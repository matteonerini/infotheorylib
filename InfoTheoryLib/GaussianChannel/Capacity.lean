/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian
public import InfoTheoryLib.GaussianChannel.Basic

/-!
# The information capacity of the Gaussian channel

The Gaussian channel adds to its input `X` an independent noise `Z ∼ N(0, N)`: `Y = X + Z`. Under
the power constraint `E X² ≤ P`, the mutual information is at most `½ log (1 + P/N)`, with
equality when `X ∼ N(0, P)`. So the information capacity is `C = ½ log (1 + P/N)`.

## Main definitions

* `gaussianInfoCapacity P N`: the information capacity `max_{E X² ≤ P} I(X; Y)`, (9.8).

## Main statements

* `integral_gaussianPDFReal_sub_mul_log_div`: the relative entropy between `N(x, N)` and
  `N(0, S)` is `½ log (S/N) - ½ + (x² + N)/(2S)`.
* `mutualInfoPDF_gaussianChannel_le`: (9.9)–(9.16), `I(X; Y) ≤ ½ log (1 + E X²/N)` for every
  input with a density and finite power.
* `gaussianPDFReal_mul_gaussianPDFReal_sub`, `marginalSnd_gaussianChannel_gaussian`: for
  `X ∼ N(0, P)` the output is `Y ∼ N(0, P + N)`.
* `mutualInfoPDF_gaussianChannel_gaussian`: (9.17), equality for `X ∼ N(0, P)`.
* `gaussianInfoCapacity_eq`: (9.17), `C = ½ log (1 + P/N)`.

## Implementation notes

The book computes `I(X; Y) = h(Y) - h(Z)` and bounds `h(Y)` by the entropy of the normal
distribution with variance `E Y² = P + N`. We compare instead the conditional density of `Y`
with the density of `N(0, E X² + N)` (`mutualInfoPDF_noiseJointPDF_le`): this gives the same bound
without assuming that `h(Y)` exists. The input has a density `f` with respect to an arbitrary
σ-finite measure `μ` on `ℝ`, so discrete inputs are included; the information capacity is the
supremum over densities with respect to the Lebesgue measure, as in (9.8). Logarithms are
natural: capacities are in nats, and the book's capacities in bits are `C / log 2`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.1
-/

open Real MeasureTheory ProbabilityTheory Filter
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Moments of the shifted normal density -/

/-- `∫ φ(y - x) h(y) dy = ∫ φ(t) h(t + x) dt`. -/
lemma integral_gaussianPDFReal_sub_mul (v : ℝ≥0) (x : ℝ) (h : ℝ → ℝ) :
    ∫ y, gaussianPDFReal 0 v (y - x) * h y = ∫ t, gaussianPDFReal 0 v t * h (t + x) := by
  have := integral_sub_right_eq_self (μ := volume)
    (fun t => gaussianPDFReal 0 v t * h (t + x)) x
  simpa using this

lemma integrable_gaussianPDFReal_sub_mul_iff (v : ℝ≥0) (x : ℝ) (h : ℝ → ℝ) :
    Integrable (fun y => gaussianPDFReal 0 v (y - x) * h y) ↔
      Integrable fun t => gaussianPDFReal 0 v t * h (t + x) := by
  constructor
  · intro hi
    simpa using hi.comp_add_right x
  · intro hi
    simpa using hi.comp_sub_right x

/-- `∫ φ_v(y - x) dy = 1`, `∫ φ_v(y - x) (y - x)² dy = v` and `∫ φ_v(y - x) y² dy = x² + v`. -/
lemma gaussianPDFReal_sub_moments {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Integrable (fun y => gaussianPDFReal 0 v (y - x)) ∧
      ∫ y, gaussianPDFReal 0 v (y - x) = 1 ∧
      Integrable (fun y => gaussianPDFReal 0 v (y - x) * (y - x) ^ 2) ∧
      ∫ y, gaussianPDFReal 0 v (y - x) * (y - x) ^ 2 = v ∧
      Integrable (fun y => gaussianPDFReal 0 v (y - x) * y ^ 2) ∧
      ∫ y, gaussianPDFReal 0 v (y - x) * y ^ 2 = x ^ 2 + v := by
  have h0 := integrable_gaussianPDFReal 0 v
  have h1 := integrable_gaussianPDFReal_mul_self hv
  have h2 := integrable_gaussianPDFReal_mul_sq_zero hv
  have e : (fun t => gaussianPDFReal 0 v t * (t + x) ^ 2) =
      fun t => gaussianPDFReal 0 v t * t ^ 2 + 2 * x * (gaussianPDFReal 0 v t * t) +
        x ^ 2 * gaussianPDFReal 0 v t := by
    funext t
    ring
  have hy2 : Integrable fun t => gaussianPDFReal 0 v t * (t + x) ^ 2 := by
    rw [e]
    exact (h2.add (h1.const_mul _)).add (h0.const_mul _)
  refine ⟨h0.comp_sub_right x, ?_, ?_, ?_, ?_, ?_⟩
  · rw [integral_sub_right_eq_self (gaussianPDFReal 0 v) x, integral_gaussianPDFReal_eq_one 0 hv]
  · exact (integrable_gaussianPDFReal_sub_mul_iff v x _).2 (by simpa using h2)
  · rw [integral_gaussianPDFReal_sub_mul]
    simpa using integral_gaussianPDFReal_mul_sq_zero hv
  · exact (integrable_gaussianPDFReal_sub_mul_iff v x _).2 hy2
  · have hA : Integrable fun t => gaussianPDFReal 0 v t * t ^ 2 +
        2 * x * (gaussianPDFReal 0 v t * t) := h2.add (h1.const_mul _)
    have hB : Integrable fun t => 2 * x * (gaussianPDFReal 0 v t * t) := h1.const_mul _
    have hC : Integrable fun t => x ^ 2 * gaussianPDFReal 0 v t := h0.const_mul _
    rw [integral_gaussianPDFReal_sub_mul, e, integral_add hA hC, integral_add h2 hB,
      integral_const_mul, integral_const_mul, integral_gaussianPDFReal_mul_sq_zero hv,
      integral_gaussianPDFReal_mul_self hv, integral_gaussianPDFReal_eq_one 0 hv]
    ring

/-- `log (φ_N(y - x)/φ_S(y)) = ½ log (S/N) - (y - x)²/(2N) + y²/(2S)`. -/
lemma log_gaussianPDFReal_sub_div {N S : ℝ≥0} (hN : N ≠ 0) (hS : S ≠ 0) (x y : ℝ) :
    log (gaussianPDFReal 0 N (y - x) / gaussianPDFReal 0 S y) =
      log (S / N) / 2 - (y - x) ^ 2 / (2 * N) + y ^ 2 / (2 * S) := by
  have hN' : (0 : ℝ) < N := by positivity
  have hS' : (0 : ℝ) < S := by positivity
  rw [log_div (gaussianPDFReal_pos _ _ _ hN).ne' (gaussianPDFReal_pos _ _ _ hS).ne',
    log_gaussianPDFReal 0 hN, log_gaussianPDFReal 0 hS, log_div hS'.ne' hN'.ne',
    log_mul (by positivity) hN'.ne', log_mul (by positivity) hS'.ne']
  ring

/-- **The relative entropy between two normal densities.** `D(N(x, N) ‖ N(0, S))`, that is
`∫ φ_N(y - x) log (φ_N(y - x)/φ_S(y)) dy`, equals `½ log (S/N) - ½ + (x² + N)/(2S)`. -/
lemma integral_gaussianPDFReal_sub_mul_log_div {N S : ℝ≥0} (hN : N ≠ 0) (hS : S ≠ 0) (x : ℝ) :
    Integrable (fun y => gaussianPDFReal 0 N (y - x) *
        log (gaussianPDFReal 0 N (y - x) / gaussianPDFReal 0 S y)) ∧
      ∫ y, gaussianPDFReal 0 N (y - x) *
          log (gaussianPDFReal 0 N (y - x) / gaussianPDFReal 0 S y) =
        log (S / N) / 2 - 1 / 2 + (x ^ 2 + N) / (2 * S) := by
  obtain ⟨i0, e0, i1, e1, i2, e2⟩ := gaussianPDFReal_sub_moments hN x
  have hN' : (0 : ℝ) < N := by positivity
  set φ := fun y => gaussianPDFReal 0 N (y - x)
  have e : (fun y => φ y * log (φ y / gaussianPDFReal 0 S y)) =
      fun y => log (S / N) / 2 * φ y - (2 * (N : ℝ))⁻¹ * (φ y * (y - x) ^ 2) +
        (2 * (S : ℝ))⁻¹ * (φ y * y ^ 2) := by
    funext y
    simp only [φ]
    rw [log_gaussianPDFReal_sub_div hN hS]
    ring
  have hA : Integrable fun y => log (S / N) / 2 * φ y - (2 * (N : ℝ))⁻¹ * (φ y * (y - x) ^ 2) :=
    (i0.const_mul _).sub (i1.const_mul _)
  have hB : Integrable fun y => (2 * (S : ℝ))⁻¹ * (φ y * y ^ 2) := i2.const_mul _
  rw [e]
  refine ⟨hA.add hB, ?_⟩
  rw [integral_add hA hB, integral_sub (i0.const_mul _) (i1.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, e0, e1, e2]
  field_simp

/-! ### The bound on the mutual information -/

section Bound

variable {μ : Measure ℝ} [SigmaFinite μ] {f : ℝ → ℝ}

/-- The integral `∫ f(x) φ_N(y - x) log (φ_N(y - x)/φ_S(y))`: the relative entropy between the
joint law of `(X, Y)` and the product of the law of `X` and `N(0, S)`. -/
lemma integral_noiseJointPDF_mul_log_div (hf : IsPDF μ f) {N S : ℝ≥0} (hN : N ≠ 0) (hS : S ≠ 0)
    (h2 : Integrable (fun x => f x * x ^ 2) μ) :
    Integrable (fun z => noiseJointPDF f (gaussianPDFReal 0 N) z *
        log (gaussianPDFReal 0 N (z.2 - z.1) / gaussianPDFReal 0 S z.2)) (μ.prod volume) ∧
      ∫ z, noiseJointPDF f (gaussianPDFReal 0 N) z *
          log (gaussianPDFReal 0 N (z.2 - z.1) / gaussianPDFReal 0 S z.2) ∂(μ.prod volume) =
        log (S / N) / 2 - 1 / 2 + ((∫ x, f x * x ^ 2 ∂μ) + N) / (2 * S) := by
  set J := noiseJointPDF f (gaussianPDFReal 0 N)
  -- The three pieces of the integrand.
  have hJ := noiseJointPDF_isPDF (μ := μ) hf (gaussianPDFReal_isPDF 0 hN)
  obtain ⟨iA, eA⟩ := integral_noiseJointPDF_mul hf (measurable_gaussianPDFReal 0 N)
    (gaussianPDFReal_nonneg 0 N) (h := fun z => (z.2 - z.1) ^ 2)
    (by fun_prop) (fun z => sq_nonneg _) (k := fun _ => (N : ℝ))
    (fun x => ⟨(gaussianPDFReal_sub_moments hN x).2.2.1,
      (gaussianPDFReal_sub_moments hN x).2.2.2.1⟩) (hf.integrable.mul_const _)
  obtain ⟨iB, eB⟩ := integral_noiseJointPDF_mul hf (measurable_gaussianPDFReal 0 N)
    (gaussianPDFReal_nonneg 0 N) (h := fun z => z.2 ^ 2)
    (by fun_prop) (fun z => sq_nonneg _) (k := fun x => x ^ 2 + N)
    (fun x => ⟨(gaussianPDFReal_sub_moments hN x).2.2.2.2.1,
      (gaussianPDFReal_sub_moments hN x).2.2.2.2.2⟩)
    ((h2.add (hf.integrable.mul_const (N : ℝ))).congr (Eventually.of_forall fun x => by
      simp only [Pi.add_apply]; ring))
  have e : (fun z => J z * log (gaussianPDFReal 0 N (z.2 - z.1) / gaussianPDFReal 0 S z.2)) =
      fun z => log (S / N) / 2 * J z - (2 * (N : ℝ))⁻¹ * (J z * (z.2 - z.1) ^ 2) +
        (2 * (S : ℝ))⁻¹ * (J z * z.2 ^ 2) := by
    funext z
    rw [log_gaussianPDFReal_sub_div hN hS]
    ring
  have hA : Integrable (fun z => log (S / N) / 2 * J z -
      (2 * (N : ℝ))⁻¹ * (J z * (z.2 - z.1) ^ 2)) (μ.prod volume) :=
    (hJ.integrable.const_mul _).sub (iA.const_mul _)
  have hB : Integrable (fun z => (2 * (S : ℝ))⁻¹ * (J z * z.2 ^ 2)) (μ.prod volume) :=
    iB.const_mul _
  have hfN : Integrable (fun x => f x * (N : ℝ)) μ := hf.integrable.mul_const _
  rw [e]
  refine ⟨hA.add hB, ?_⟩
  rw [integral_add hA hB, integral_sub (hJ.integrable.const_mul _) (iA.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, hJ.integral_eq_one, eA, eB,
    integral_mul_const, hf.integral_eq_one]
  have e2 : ∫ x, f x * (x ^ 2 + N) ∂μ = (∫ x, f x * x ^ 2 ∂μ) + N := by
    have : (fun x => f x * (x ^ 2 + N)) = fun x => f x * x ^ 2 + f x * N :=
      funext fun x => by ring
    rw [this, integral_add h2 hfN, integral_mul_const, hf.integral_eq_one, one_mul]
  rw [e2]
  have hN' : (0 : ℝ) < N := by positivity
  have hS' : (0 : ℝ) < S := by positivity
  field_simp

omit [SigmaFinite μ] in
lemma integral_mul_sq_nonneg (hf : IsPDF μ f) : 0 ≤ ∫ x, f x * x ^ 2 ∂μ :=
  integral_nonneg fun x => mul_nonneg (hf.nonneg x) (sq_nonneg x)

/-- **(9.9)–(9.16)** The mutual information between the input `X` and the output `Y = X + Z` of
the Gaussian channel with noise `Z ∼ N(0, N)` is at most `½ log (1 + E X²/N)`. -/
theorem mutualInfoPDF_gaussianChannel_le (hf : IsPDF μ f) {N : ℝ≥0} (hN : N ≠ 0)
    (h2 : Integrable (fun x => f x * x ^ 2) μ) :
    mutualInfoPDF μ volume (noiseJointPDF f (gaussianPDFReal 0 N)) ≤
      1 / 2 * log (1 + (∫ x, f x * x ^ 2 ∂μ) / N) := by
  set P := ∫ x, f x * x ^ 2 ∂μ
  have hP : 0 ≤ P := integral_mul_sq_nonneg hf
  have hN' : (0 : ℝ) < N := by positivity
  set S : ℝ≥0 := ⟨P, hP⟩ + N
  have hS' : (S : ℝ) = P + N := rfl
  have hS : S ≠ 0 := fun h => by
    have := congrArg NNReal.toReal h
    rw [hS', NNReal.coe_zero] at this
    linarith
  obtain ⟨hint, heq⟩ := integral_noiseJointPDF_mul_log_div hf hN hS h2
  refine (mutualInfoPDF_noiseJointPDF_le hf (gaussianPDFReal_isPDF 0 hN)
    (fun x => gaussianPDFReal_pos _ _ _ hN) (gaussianPDFReal_isPDF 0 hS)
    (fun y => gaussianPDFReal_pos _ _ _ hS) hint).trans_eq ?_
  rw [heq, hS', show (P + N) / N = 1 + P / N by rw [add_div, div_self hN'.ne', add_comm]]
  field_simp
  ring

/-- **(9.16)** Under the power constraint `E X² ≤ P`, `I(X; Y) ≤ ½ log (1 + P/N)`. -/
theorem mutualInfoPDF_gaussianChannel_le_of_power (hf : IsPDF μ f) {N : ℝ≥0} (hN : N ≠ 0)
    (h2 : Integrable (fun x => f x * x ^ 2) μ) {P : ℝ} (hP : ∫ x, f x * x ^ 2 ∂μ ≤ P) :
    mutualInfoPDF μ volume (noiseJointPDF f (gaussianPDFReal 0 N)) ≤ 1 / 2 * log (1 + P / N) := by
  have hN' : (0 : ℝ) < N := by positivity
  have h0 := integral_mul_sq_nonneg hf
  refine (mutualInfoPDF_gaussianChannel_le hf hN h2).trans ?_
  have h1 : 1 + (∫ x, f x * x ^ 2 ∂μ) / N ≤ 1 + P / N := by gcongr
  have h0' : 0 < 1 + (∫ x, f x * x ^ 2 ∂μ) / N := by positivity
  exact mul_le_mul_of_nonneg_left (log_le_log h0' h1) (by norm_num)

end Bound

/-! ### The normal input -/

/-- `(√a)⁻¹ e^u · (√b)⁻¹ e^v = (√(ab))⁻¹ e^{u + v}`. -/
lemma inv_sqrt_mul_exp_mul {a b : ℝ} (ha : 0 ≤ a) (u v : ℝ) :
    (√a)⁻¹ * exp u * ((√b)⁻¹ * exp v) = (√(a * b))⁻¹ * exp (u + v) := by
  rw [sqrt_mul ha, mul_inv, exp_add]
  ring

/-- Completing the square: `φ_P(x) φ_N(y - x) = φ_{P+N}(y) φ_{PN/(P+N)}(x - Py/(P+N))`. The sum of
independent `N(0, P)` and `N(0, N)` variables is `N(0, P + N)`. -/
lemma gaussianPDFReal_mul_gaussianPDFReal_sub {P N : ℝ≥0} (hP : P ≠ 0) (hN : N ≠ 0) (x y : ℝ) :
    gaussianPDFReal 0 P x * gaussianPDFReal 0 N (y - x) =
      gaussianPDFReal 0 (P + N) y *
        gaussianPDFReal ((P : ℝ) / (P + N) * y) (P * N / (P + N)) x := by
  have hP' : (0 : ℝ) < P := by positivity
  have hN' : (0 : ℝ) < N := by positivity
  simp only [gaussianPDFReal_def, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul]
  rw [inv_sqrt_mul_exp_mul (by positivity), inv_sqrt_mul_exp_mul (by positivity)]
  congr 1
  · congr 2
    field_simp
  · congr 1
    field_simp
    ring

/-- For `X ∼ N(0, P)`, the output `Y = X + Z` has density `φ_{P+N}`. -/
lemma marginalSnd_gaussianChannel_gaussian {P N : ℝ≥0} (hP : P ≠ 0) (hN : N ≠ 0) :
    marginalSnd volume (noiseJointPDF (gaussianPDFReal 0 P) (gaussianPDFReal 0 N)) =
      gaussianPDFReal 0 (P + N) := by
  have hv : P * N / (P + N) ≠ 0 := by
    have : 0 < P * N / (P + N) := by
      have hP' : 0 < P := pos_iff_ne_zero.2 hP
      have hN' : 0 < N := pos_iff_ne_zero.2 hN
      positivity
    exact this.ne'
  funext y
  simp only [marginalSnd, noiseJointPDF, gaussianPDFReal_mul_gaussianPDFReal_sub hP hN]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hv, mul_one]

/-- **(9.17)** The normal input `X ∼ N(0, P)` attains `I(X; Y) = ½ log (1 + P/N)`. -/
theorem mutualInfoPDF_gaussianChannel_gaussian {P N : ℝ≥0} (hP : P ≠ 0) (hN : N ≠ 0) :
    mutualInfoPDF volume volume (noiseJointPDF (gaussianPDFReal 0 P) (gaussianPDFReal 0 N)) =
      1 / 2 * log (1 + P / N) := by
  have hS : P + N ≠ 0 := by
    have : 0 < P + N := add_pos_of_pos_of_nonneg (pos_iff_ne_zero.2 hP) (by positivity)
    exact this.ne'
  have hN' : (0 : ℝ) < N := by positivity
  have hP' : (0 : ℝ) < P := by positivity
  rw [mutualInfoPDF_noiseJointPDF_eq (gaussianPDFReal_isPDF 0 hP) (gaussianPDFReal_isPDF 0 hN)
    (fun x => gaussianPDFReal_pos _ _ _ hN) (fun y => gaussianPDFReal_pos _ _ _ hS)
    (fun y => congrFun (marginalSnd_gaussianChannel_gaussian hP hN) y),
    (integral_noiseJointPDF_mul_log_div (gaussianPDFReal_isPDF 0 hP) hN hS
      (integrable_gaussianPDFReal_mul_sq_zero hP)).2, integral_gaussianPDFReal_mul_sq_zero hP,
    NNReal.coe_add, show ((P : ℝ) + N) / N = 1 + P / N by
      rw [add_div, div_self hN'.ne', add_comm]]
  field_simp
  ring

/-! ### The information capacity -/

/-- **Definition (9.8).** The information capacity of the Gaussian channel with power constraint
`P` and noise variance `N`: the supremum of `I(X; Y)` over the inputs with a density and
`E X² ≤ P`. -/
def gaussianInfoCapacity (P N : ℝ≥0) : ℝ :=
  sSup {I | ∃ f : ℝ → ℝ, IsPDF volume f ∧ Integrable (fun x => f x * x ^ 2) ∧
    ∫ x, f x * x ^ 2 ≤ P ∧ mutualInfoPDF volume volume (noiseJointPDF f (gaussianPDFReal 0 N)) = I}

/-- **(9.17)** The information capacity of the Gaussian channel is `C = ½ log (1 + P/N)`, and the
maximum is attained by `X ∼ N(0, P)`. -/
theorem gaussianInfoCapacity_eq (P : ℝ≥0) {N : ℝ≥0} (hN : N ≠ 0) :
    gaussianInfoCapacity P N = 1 / 2 * log (1 + P / N) := by
  set s := {I | ∃ f : ℝ → ℝ, IsPDF volume f ∧ Integrable (fun x => f x * x ^ 2) ∧
    ∫ x, f x * x ^ 2 ≤ P ∧ mutualInfoPDF volume volume (noiseJointPDF f (gaussianPDFReal 0 N)) = I}
  have hle : ∀ I ∈ s, I ≤ 1 / 2 * log (1 + P / N) := by
    rintro _ ⟨f, hf, h2, hP, rfl⟩
    exact mutualInfoPDF_gaussianChannel_le_of_power hf hN h2 hP
  rcases eq_or_ne P 0 with rfl | hP
  · have hnn : ∀ I ∈ s, 0 ≤ I := by
      rintro _ ⟨f, hf, -, -, rfl⟩
      exact mutualInfoPDF_nonneg' (noiseJointPDF_isPDF hf (gaussianPDFReal_isPDF 0 hN))
    simp only [NNReal.coe_zero, zero_div, add_zero, log_one, mul_zero] at hle ⊢
    exact le_antisymm (Real.sSup_nonpos hle) (Real.sSup_nonneg hnn)
  · refine IsGreatest.csSup_eq ⟨⟨gaussianPDFReal 0 P, gaussianPDFReal_isPDF 0 hP,
      integrable_gaussianPDFReal_mul_sq_zero hP, (integral_gaussianPDFReal_mul_sq_zero hP).le,
      mutualInfoPDF_gaussianChannel_gaussian hP hN⟩, hle⟩

end InfoTheory
