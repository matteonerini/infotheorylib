/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.RelativeEntropy

/-!
# Differential entropy of the normal distribution

The normal density `N(m, v)` has differential entropy `½ log (2πe v)`, and it maximizes the
differential entropy among all densities with the same second moment about `m`. As a consequence,
the mean squared error of any estimate of a random variable is at least `e^{2h(X)}/(2πe)`.

The real normal density is Mathlib's `ProbabilityTheory.gaussianPDFReal m v`, with mean `m` and
variance `v : ℝ≥0`.

## Main statements

* `diffEntropy_gaussianPDFReal`: Example 8.1.2, `h(N(m, v)) = ½ log (2πe v)` nats.
* `diffEntropy_le_of_integral_mul_sq`, `diffEntropy_eq_of_integral_mul_sq_iff`: Theorem 8.6.5 in
  dimension one, `h(X) ≤ ½ log (2πe E(X - m)²)` with equality iff `X` is normal.
* `exp_two_mul_diffEntropy_div_le`, `exp_two_mul_diffEntropy_div_eq_iff`: Theorem 8.6.6,
  `E(X - X̂)² ≥ e^{2h(X)}/(2πe)` for every estimate `X̂`, with equality iff `X` is normal with mean
  `X̂`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 8.1 and
  8.6
-/

open Real MeasureTheory ProbabilityTheory NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The normal distribution on the real line -/

lemma gaussianPDFReal_isPDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    IsPDF volume (gaussianPDFReal m v) :=
  ⟨measurable_gaussianPDFReal m v, gaussianPDFReal_nonneg m v, integrable_gaussianPDFReal m v,
    integral_gaussianPDFReal_eq_one m hv⟩

/-- The variance of the normal density: `∫ φ(x) (x - m)² dx = v`. -/
lemma integral_gaussianPDFReal_mul_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal m v x * (x - m) ^ 2 = v := by
  have h := variance_eq_integral (μ := gaussianReal m v) (X := fun x => x)
    measurable_id.aemeasurable
  simp only [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simpa [smul_eq_mul] using h.symm

lemma integrable_gaussianPDFReal_mul_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable fun x => gaussianPDFReal m v x * (x - m) ^ 2 :=
  Integrable.of_integral_ne_zero (by rw [integral_gaussianPDFReal_mul_sq m hv]; exact_mod_cast hv)

/-- `log φ(x) = -½ log (2πv) - (x - m)²/(2v)`. -/
lemma log_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    log (gaussianPDFReal m v x) = -(log (2 * π * v) / 2) - (x - m) ^ 2 / (2 * v) := by
  have hpos : 0 < 2 * π * (v : ℝ) := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.property (by exact_mod_cast hv.symm)
    positivity
  rw [gaussianPDFReal, log_mul (inv_ne_zero (sqrt_ne_zero'.2 hpos)) (exp_pos _).ne', log_inv,
    log_exp, log_sqrt hpos.le]
  ring

lemma negMulLog_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    negMulLog (gaussianPDFReal m v x) = log (2 * π * v) / 2 * gaussianPDFReal m v x +
      (2 * (v : ℝ))⁻¹ * (gaussianPDFReal m v x * (x - m) ^ 2) := by
  rw [negMulLog, log_gaussianPDFReal m hv]
  ring

lemma integrable_negMulLog_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable fun x => negMulLog (gaussianPDFReal m v x) := by
  simp only [negMulLog_gaussianPDFReal m hv]
  exact ((integrable_gaussianPDFReal m v).const_mul _).add
    ((integrable_gaussianPDFReal_mul_sq m hv).const_mul _)

/-- `½ log (2πv) + ½ = ½ log (2πe v)`. -/
lemma half_log_add_half {v : ℝ} (hv : 0 < v) :
    log (2 * π * v) / 2 + 1 / 2 = 1 / 2 * log (2 * π * exp 1 * v) := by
  rw [show 2 * π * exp 1 * v = 2 * π * v * exp 1 by ring, log_mul (by positivity) (exp_ne_zero 1),
    log_exp]
  ring

/-- **Example 8.1.2 (Normal distribution), (8.3)–(8.8).** The normal density `N(m, v)` has
differential entropy `h = ½ log (2πe v)` nats. -/
theorem diffEntropy_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    diffEntropy volume (gaussianPDFReal m v) = 1 / 2 * log (2 * π * exp 1 * v) := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.property (by exact_mod_cast hv.symm)
  rw [diffEntropy]
  simp only [negMulLog_gaussianPDFReal m hv]
  rw [integral_add ((integrable_gaussianPDFReal m v).const_mul _)
      ((integrable_gaussianPDFReal_mul_sq m hv).const_mul _), integral_const_mul,
    integral_const_mul, integral_gaussianPDFReal_eq_one m hv, integral_gaussianPDFReal_mul_sq m hv,
    ← half_log_add_half hv']
  field_simp

/-! ### Maximum entropy in dimension one -/

/-- `-∫ g log φ = ½ log (2πe v)` for any density `g` with `∫ g (x - m)² = v`: the cross-entropy of
`g` relative to the normal density with the same second moment about `m`. -/
lemma crossEntropy_gaussianPDFReal {g : ℝ → ℝ} (hg : IsPDF volume g) {m : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (hvar : ∫ x, g x * (x - m) ^ 2 = v) :
    Integrable (fun x => g x * log (gaussianPDFReal m v x)) ∧
      -∫ x, g x * log (gaussianPDFReal m v x) = 1 / 2 * log (2 * π * exp 1 * v) := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.property (by exact_mod_cast hv.symm)
  have hsq : Integrable fun x => g x * (x - m) ^ 2 :=
    Integrable.of_integral_ne_zero (by rw [hvar]; exact hv'.ne')
  have e : (fun x => g x * log (gaussianPDFReal m v x)) =
      fun x => -(log (2 * π * v) / 2) * g x - (2 * (v : ℝ))⁻¹ * (g x * (x - m) ^ 2) := by
    funext x
    rw [log_gaussianPDFReal m hv]
    ring
  rw [e]
  refine ⟨(hg.integrable.const_mul _).sub (hsq.const_mul _), ?_⟩
  rw [integral_sub (hg.integrable.const_mul _) (hsq.const_mul _), integral_const_mul,
    integral_const_mul, hg.integral_eq_one, hvar, ← half_log_add_half hv']
  field_simp
  ring

/-- **Theorem 8.6.5 in dimension one.** The normal distribution maximizes the differential entropy
for a given second moment: if `∫ g(x) (x - m)² dx = v`, then `h(g) ≤ ½ log (2πe v)`. -/
theorem diffEntropy_le_of_integral_mul_sq {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hint : Integrable fun x => negMulLog (g x)) {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : ∫ x, g x * (x - m) ^ 2 = v) :
    diffEntropy volume g ≤ 1 / 2 * log (2 * π * exp 1 * v) := by
  obtain ⟨h1, h2⟩ := crossEntropy_gaussianPDFReal hg hv hvar
  rw [← h2]
  exact diffEntropy_le_crossEntropy hg (gaussianPDFReal_isPDF m hv)
    (Filter.Eventually.of_forall fun x hx => absurd hx (gaussianPDFReal_pos m v x hv).ne') hint h1

/-- **Theorem 8.6.5 in dimension one (equality case).** Equality holds iff `g` is the normal
density `N(m, v)` almost everywhere. -/
theorem diffEntropy_eq_of_integral_mul_sq_iff {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hint : Integrable fun x => negMulLog (g x)) {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : ∫ x, g x * (x - m) ^ 2 = v) :
    diffEntropy volume g = 1 / 2 * log (2 * π * exp 1 * v) ↔
      g =ᵐ[volume] gaussianPDFReal m v := by
  obtain ⟨h1, h2⟩ := crossEntropy_gaussianPDFReal hg hv hvar
  rw [← h2]
  exact diffEntropy_eq_crossEntropy_iff hg (gaussianPDFReal_isPDF m hv)
    (Filter.Eventually.of_forall fun x hx => absurd hx (gaussianPDFReal_pos m v x hv).ne') hint h1

/-! ### Estimation error and differential entropy -/

/-- A density has a positive second moment about any point: `∫ g(x) (x - c)² dx > 0`. -/
lemma integral_mul_sq_pos {g : ℝ → ℝ} (hg : IsPDF volume g) (c : ℝ)
    (h2 : Integrable fun x => g x * (x - c) ^ 2) : 0 < ∫ x, g x * (x - c) ^ 2 := by
  have hnn : 0 ≤ᵐ[volume] fun x => g x * (x - c) ^ 2 :=
    Filter.Eventually.of_forall fun x => mul_nonneg (hg.nonneg x) (sq_nonneg _)
  refine lt_of_le_of_ne (integral_nonneg_of_ae hnn) fun h0 => ?_
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn h2).1 h0.symm
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [Filter.Eventually, mem_ae_iff]
    simp
  have hg0 : g =ᵐ[volume] 0 := by
    filter_upwards [hz, hne] with x hx hxc
    simpa [sub_ne_zero.2 hxc] using hx
  have := hg.integral_eq_one
  rw [integral_congr_ae hg0] at this
  simp at this

/-- **Theorem 8.6.6 (Estimation error and differential entropy).** For any random variable `X`
with density `g` and any estimate `X̂ = c`, the mean squared error is at least
`E(X - X̂)² ≥ e^{2h(X)}/(2πe)`, with `h(X)` in nats. -/
theorem exp_two_mul_diffEntropy_div_le {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hint : Integrable fun x => negMulLog (g x)) (c : ℝ)
    (h2 : Integrable fun x => g x * (x - c) ^ 2) :
    exp (2 * diffEntropy volume g) / (2 * π * exp 1) ≤ ∫ x, g x * (x - c) ^ 2 := by
  have hpos := integral_mul_sq_pos hg c h2
  set v : ℝ≥0 := ⟨_, hpos.le⟩
  have hv : v ≠ 0 := fun h => hpos.ne' (congrArg NNReal.toReal h)
  have hle := diffEntropy_le_of_integral_mul_sq hg hint hv rfl
  rw [div_le_iff₀ (by positivity)]
  calc exp (2 * diffEntropy volume g) ≤ exp (log (2 * π * exp 1 * v)) :=
        exp_le_exp.2 (by linarith)
    _ = (∫ x, g x * (x - c) ^ 2) * (2 * π * exp 1) := by
        have hv' : (v : ℝ) = ∫ x, g x * (x - c) ^ 2 := rfl
        rw [exp_log (by positivity), hv']
        ring

/-- **Theorem 8.6.6 (equality case).** Equality holds iff `X` is normal with mean `X̂ = c`. -/
theorem exp_two_mul_diffEntropy_div_eq_iff {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hint : Integrable fun x => negMulLog (g x)) (c : ℝ)
    (h2 : Integrable fun x => g x * (x - c) ^ 2) :
    exp (2 * diffEntropy volume g) / (2 * π * exp 1) = ∫ x, g x * (x - c) ^ 2 ↔
      g =ᵐ[volume] gaussianPDFReal c ⟨_, (integral_mul_sq_pos hg c h2).le⟩ := by
  have hpos := integral_mul_sq_pos hg c h2
  set v : ℝ≥0 := ⟨_, hpos.le⟩
  have hv : v ≠ 0 := fun h => hpos.ne' (congrArg NNReal.toReal h)
  rw [← diffEntropy_eq_of_integral_mul_sq_iff hg hint hv rfl]
  have hv' : (v : ℝ) = ∫ x, g x * (x - c) ^ 2 := rfl
  rw [← hv', div_eq_iff (by positivity)]
  constructor
  · intro h
    have := congrArg log h
    rw [log_exp, show (v : ℝ) * (2 * π * exp 1) = 2 * π * exp 1 * v by ring] at this
    linarith
  · intro h
    rw [h, show 2 * (1 / 2 * log (2 * π * exp 1 * v)) = log (2 * π * exp 1 * v) by ring,
      exp_log (by positivity)]
    ring

end InfoTheory
