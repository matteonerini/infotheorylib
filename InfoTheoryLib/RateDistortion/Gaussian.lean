/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Capacity

/-!
# The rate distortion function of a Gaussian source

For a `N(0, σ²)` source with squared-error distortion, the information rate distortion function
`R(D) = inf_{f(x̂|x) : E(X - X̂)² ≤ D} I(X; X̂)` (10.25) is `½ log (σ²/D)` for `0 < D ≤ σ²` and `0`
for `D ≥ σ²`. Equivalently, the distortion rate function is `D(R) = σ² e^{-2R}` (10.37).

## Main definitions

* `gaussianInfoRD S D`: the information rate distortion function (10.25) of a `N(0, S)` source
  with squared-error distortion.

## Main statements

* `integral_mul_log_div_le_mutualInfoPDF`: for every positive conditional density `g(x|y)`,
  `I(X; Y) ≥ ∫ f(x, y) log (g(x|y)/f(x))`, the difference being `D(f(x, y) ‖ f(y) g(x|y))`.
* `half_log_div_le_mutualInfoPDF`: (10.26)–(10.33), `I(X; X̂) ≥ ½ log (σ²/D)` when `X ∼ N(0, σ²)`
  and `E(X - X̂)² ≤ D`.
* `mutualInfoPDF_gaussianTest`: (10.34)–(10.35), the test channel `X = X̂ + Z` with
  `X̂ ∼ N(0, σ² - D)` and `Z ∼ N(0, D)` independent attains `½ log (σ²/D)`.
* `gaussianInfoRD_eq`: **Theorem 10.3.2**.
* `gaussianInfoRD_le_iff`: **(10.37)**, `R(D) ≤ R` iff `D ≥ σ² e^{-2R}`.

## Implementation notes

The book's rate distortion theorem is proved for finite alphabets only, and the Gaussian case
assumes its extension to continuous alphabets; we compute the information rate distortion
function. It is an infimum over the joint densities `f(x, x̂)` whose first marginal is the normal
density, with a finite second moment of `X - X̂` and an integrable mutual information integrand (as
for the Gaussian channel, `I(X; X̂)` is `0` by convention otherwise). A constant reproduction
`X̂ = 0` has no joint density, so for `D ≥ σ²` the value `0` is approached by the test channels
with `D' < σ²`.

## References

Numbers without a source refer to [cover2006].

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 10.3.2
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lectures 1 and 3
-/

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### A lower bound on the mutual information -/

section General

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SigmaFinite μ] [SigmaFinite ν]

/-- **A variational lower bound on the mutual information.** For every positive conditional
density `g(x|y)`, `I(X; Y) ≥ ∫ f(x, y) log (g(x|y)/f(x))`: the difference is the relative entropy
between `f(x, y)` and the density `f(y) g(x|y)`. -/
theorem integral_mul_log_div_le_mutualInfoPDF {f g : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hg : Measurable g) (hgpos : ∀ z, 0 < g z)
    (hg1 : ∀ y, Integrable (fun x => g (x, y)) μ ∧ ∫ x, g (x, y) ∂μ = 1)
    (hI : Integrable (fun z => f z * log (f z / (marginalFst ν f z.1 * marginalSnd μ f z.2)))
      (μ.prod ν))
    (hG : Integrable (fun z => f z * log (g z / marginalFst ν f z.1)) (μ.prod ν)) :
    ∫ z, f z * log (g z / marginalFst ν f z.1) ∂(μ.prod ν) ≤ mutualInfoPDF μ ν f := by
  set fX := marginalFst ν f
  set fY := marginalSnd μ f
  have hfY := hf.marginalSnd
  set h : α × β → ℝ := fun z => fY z.2 * g z
  -- `f(y) g(x|y)` is a density.
  have hmeas : Measurable h := (hfY.measurable.comp measurable_snd).mul hg
  have hrow : ∀ y, ∫ x, h (x, y) ∂μ = fY y := fun y => by
    simp only [h]
    rw [integral_const_mul, (hg1 y).2, mul_one]
  have hint : Integrable h (μ.prod ν) := by
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨Eventually.of_forall fun y =>
      (hg1 y).1.const_mul (fY y), hfY.integrable.congr (Eventually.of_forall fun y => ?_)⟩
    change fY y = ∫ x, ‖h (x, y)‖ ∂μ
    rw [← hrow y]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (Real.norm_of_nonneg (mul_nonneg (hfY.nonneg _) (hgpos _).le)).symm
  have hh : IsPDF (μ.prod ν) h := ⟨hmeas, fun z => mul_nonneg (hfY.nonneg _) (hgpos z).le, hint,
    by rw [integral_prod_symm _ hint]; simp_rw [hrow]; exact hfY.integral_eq_one⟩
  have habs : ∀ᵐ z ∂(μ.prod ν), h z = 0 → f z = 0 := by
    filter_upwards [ae_marginalSnd_eq_zero hf] with z hz h0
    exact hz ((mul_eq_zero.1 h0).resolve_right (hgpos z).ne')
  -- The integrand of `I(X; Y)` splits.
  have hsplit : (fun z => f z * log (f z / (fX z.1 * fY z.2))) =ᵐ[μ.prod ν]
      fun z => f z * log (g z / fX z.1) + f z * log (f z / h z) := by
    filter_upwards [ae_marginalFst_eq_zero hf, ae_marginalSnd_eq_zero hf] with z h1 h2
    rcases eq_or_ne (f z) 0 with h0 | h0
    · simp [h0]
    have hX : fX z.1 ≠ 0 := fun h => h0 (h1 h)
    have hY : fY z.2 ≠ 0 := fun h => h0 (h2 h)
    have hgz := (hgpos z).ne'
    simp only [h]
    rw [← mul_add, log_div h0 (mul_ne_zero hX hY), log_div hgz hX, log_div h0 (mul_ne_zero hY hgz),
      log_mul hX hY, log_mul hY hgz]
    ring
  have hD : Integrable (fun z => f z * log (f z / h z)) (μ.prod ν) :=
    (hI.sub hG).congr (hsplit.mono fun z hz => by simp only [Pi.sub_apply, hz]; ring)
  have hDnn := relEntropyPDF_nonneg hf hh habs hD
  rw [mutualInfoPDF, integral_congr_ae hsplit, integral_add hG hD]
  exact le_add_of_nonneg_right hDnn

end General

/-! ### The Gaussian source -/

/-- **Definition (10.25).** The information rate distortion function of a `N(0, S)` source with
squared-error distortion: the infimum of `I(X; X̂)` over the joint densities `f(x, x̂)` with
`X ∼ N(0, S)` and `E(X - X̂)² ≤ D`. -/
def gaussianInfoRD (S D : ℝ≥0) : ℝ :=
  sInf {I | ∃ f : ℝ × ℝ → ℝ, IsPDF (volume.prod volume) f ∧
    marginalFst volume f = gaussianPDFReal 0 S ∧
    Integrable (fun z => f z * (z.1 - z.2) ^ 2) (volume.prod volume) ∧
    ∫ z, f z * (z.1 - z.2) ^ 2 ∂(volume.prod volume) ≤ D ∧
    Integrable (fun z => f z * log (f z / (marginalFst volume f z.1 * marginalSnd volume f z.2)))
      (volume.prod volume) ∧
    mutualInfoPDF volume volume f = I}

/-- **(10.26)–(10.33)** If `X ∼ N(0, S)` and `E(X - X̂)² ≤ D`, then `I(X; X̂) ≥ ½ log (S/D)`. -/
theorem half_log_div_le_mutualInfoPDF {S D : ℝ≥0} (hS : S ≠ 0) (hD : D ≠ 0) {f : ℝ × ℝ → ℝ}
    (hf : IsPDF (volume.prod volume) f) (hX : marginalFst volume f = gaussianPDFReal 0 S)
    (h2 : Integrable (fun z => f z * (z.1 - z.2) ^ 2) (volume.prod volume))
    (hfD : ∫ z, f z * (z.1 - z.2) ^ 2 ∂(volume.prod volume) ≤ D)
    (hI : Integrable (fun z => f z * log (f z / (marginalFst volume f z.1 *
      marginalSnd volume f z.2))) (volume.prod volume)) :
    1 / 2 * log (S / D) ≤ mutualInfoPDF volume volume f := by
  have hS' : (0 : ℝ) < S := by positivity
  have hD' : (0 : ℝ) < D := by positivity
  set g : ℝ × ℝ → ℝ := fun z => gaussianPDFReal 0 D (z.1 - z.2)
  -- `E X² = S`.
  obtain ⟨iX, eX⟩ := integral_mul_comp_fst hf (G := fun x => x ^ 2) (by fun_prop)
    (by rw [hX]; exact integrable_gaussianPDFReal_mul_sq_zero hS)
  rw [hX, integral_gaussianPDFReal_mul_sq_zero hS] at eX
  -- The integrand of the lower bound.
  have hlog : ∀ z : ℝ × ℝ, f z * log (g z / marginalFst volume f z.1) =
      log (S / D) / 2 * f z - (2 * (D : ℝ))⁻¹ * (f z * (z.1 - z.2) ^ 2) +
        (2 * (S : ℝ))⁻¹ * (f z * z.1 ^ 2) := fun z => by
    simp only [g, hX]
    rw [log_gaussianPDFReal_sub_div hD hS]
    ring
  have hA : Integrable (fun z => log (S / D) / 2 * f z - (2 * (D : ℝ))⁻¹ *
      (f z * (z.1 - z.2) ^ 2)) (volume.prod volume) :=
    (hf.integrable.const_mul _).sub (h2.const_mul _)
  have hB : Integrable (fun z => (2 * (S : ℝ))⁻¹ * (f z * z.1 ^ 2)) (volume.prod volume) :=
    iX.const_mul _
  have hG : Integrable (fun z => f z * log (g z / marginalFst volume f z.1))
      (volume.prod volume) := by
    simp_rw [hlog]
    exact hA.add hB
  have hbound := integral_mul_log_div_le_mutualInfoPDF hf
    ((measurable_gaussianPDFReal 0 D).comp (measurable_fst.sub measurable_snd))
    (fun z => gaussianPDFReal_pos _ _ _ hD)
    (fun y => ⟨(gaussianPDFReal_sub_moments hD y).1, (gaussianPDFReal_sub_moments hD y).2.1⟩)
    hI hG
  set δ := ∫ z, f z * (z.1 - z.2) ^ 2 ∂(volume.prod volume)
  have hGval : ∫ z, f z * log (g z / marginalFst volume f z.1) ∂(volume.prod volume) =
      log (S / D) / 2 - (2 * (D : ℝ))⁻¹ * δ + (2 * (S : ℝ))⁻¹ * S := by
    rw [integral_congr_ae (Eventually.of_forall hlog), integral_add hA hB,
      integral_sub (hf.integrable.const_mul _) (h2.const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul, hf.integral_eq_one, eX, mul_one]
  have hδ : (2 * (D : ℝ))⁻¹ * δ ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have hSS : (2 * (S : ℝ))⁻¹ * S = 1 / 2 := by field_simp
  calc 1 / 2 * log (S / D) ≤ log (S / D) / 2 - (2 * (D : ℝ))⁻¹ * δ + (2 * (S : ℝ))⁻¹ * S := by
        linarith
    _ = _ := hGval.symm
    _ ≤ mutualInfoPDF volume volume f := hbound

/-- The test channel of Figure 10.5: `X = X̂ + Z` with `X̂ ∼ N(0, S - D)` and `Z ∼ N(0, D)`
independent. Its joint density at `(x, x̂)` is `φ_{S-D}(x̂) φ_D(x - x̂)`. -/
def gaussianTestPDF (S D : ℝ≥0) : ℝ × ℝ → ℝ :=
  noiseJointPDF (gaussianPDFReal 0 (S - D)) (gaussianPDFReal 0 D) ∘ Prod.swap

section Test

variable {S D : ℝ≥0}

lemma gaussianTestPDF_isPDF (hDS : D < S) (hD : D ≠ 0) :
    IsPDF (volume.prod volume) (gaussianTestPDF S D) :=
  (noiseJointPDF_isPDF (gaussianPDFReal_isPDF 0 (tsub_pos_of_lt hDS).ne')
    (gaussianPDFReal_isPDF 0 hD)).swap

/-- **(10.34)** The test channel reproduces the source: `X ∼ N(0, S)`. -/
lemma marginalFst_gaussianTestPDF (hDS : D < S) (hD : D ≠ 0) :
    marginalFst volume (gaussianTestPDF S D) = gaussianPDFReal 0 S := by
  rw [gaussianTestPDF, marginalFst_swap,
    marginalSnd_gaussianChannel_gaussian (tsub_pos_of_lt hDS).ne' hD, tsub_add_cancel_of_le hDS.le]

/-- The test channel has distortion `E(X - X̂)² = E Z² = D`. -/
lemma integral_gaussianTestPDF_mul_sq (hDS : D < S) (hD : D ≠ 0) :
    Integrable (fun z => gaussianTestPDF S D z * (z.1 - z.2) ^ 2) (volume.prod volume) ∧
      ∫ z, gaussianTestPDF S D z * (z.1 - z.2) ^ 2 ∂(volume.prod volume) = D := by
  have hP := gaussianPDFReal_isPDF 0 (tsub_pos_of_lt hDS).ne'
  obtain ⟨i, e⟩ := integral_noiseJointPDF_mul (μ := volume) (ν := volume) hP
    (measurable_gaussianPDFReal 0 D) (gaussianPDFReal_nonneg 0 D) (h := fun z => (z.2 - z.1) ^ 2)
    (by fun_prop) (fun z => sq_nonneg _) (k := fun _ => (D : ℝ))
    (fun x => ⟨(gaussianPDFReal_sub_moments hD x).2.2.1,
      (gaussianPDFReal_sub_moments hD x).2.2.2.1⟩) (hP.integrable.mul_const _)
  refine ⟨i.swap, ?_⟩
  rw [integral_mul_const, hP.integral_eq_one, one_mul] at e
  rw [← e, ← integral_prod_swap]
  rfl

/-- **(10.35)** The test channel attains `I(X; X̂) = ½ log (S/D)`, with an integrable mutual
information integrand. -/
theorem mutualInfoPDF_gaussianTest (hDS : D < S) (hD : D ≠ 0) :
    Integrable (fun z => gaussianTestPDF S D z * log (gaussianTestPDF S D z /
        (marginalFst volume (gaussianTestPDF S D) z.1 *
          marginalSnd volume (gaussianTestPDF S D) z.2))) (volume.prod volume) ∧
      mutualInfoPDF volume volume (gaussianTestPDF S D) = 1 / 2 * log (S / D) := by
  have hP : S - D ≠ 0 := (tsub_pos_of_lt hDS).ne'
  have hSD : S - D + D = S := tsub_add_cancel_of_le hDS.le
  have hS : S ≠ 0 := (lt_of_le_of_lt (by positivity : (0 : ℝ≥0) ≤ D) hDS).ne'
  set J := noiseJointPDF (gaussianPDFReal 0 (S - D)) (gaussianPDFReal 0 D)
  have hJ := noiseJointPDF_isPDF (μ := volume) (ν := volume)
    (gaussianPDFReal_isPDF 0 hP) (gaussianPDFReal_isPDF 0 hD)
  have hout := marginalSnd_gaussianChannel_gaussian hP hD
  rw [hSD] at hout
  -- The integrand of `I(X̂; X)` is `J log (φ_D(x - x̂)/φ_S(x))`, which is integrable.
  have hint : Integrable (fun z => J z * log (J z / (marginalFst volume J z.1 *
      marginalSnd volume J z.2))) (volume.prod volume) := by
    refine (integral_noiseJointPDF_mul_log_div (gaussianPDFReal_isPDF 0 hP) hD hS
      (integrable_gaussianPDFReal_mul_sq_zero hP)).1.congr ?_
    filter_upwards [ae_marginalSnd_eq_zero hJ] with z hz
    rw [marginalFst_noiseJointPDF (gaussianPDFReal_isPDF 0 hD),
      noiseJointPDF_mul_log_eq (fun x => gaussianPDFReal_pos _ _ _ hD)
        (fun y => gaussianPDFReal_pos _ _ _ hS) hz, hout,
      div_self (gaussianPDFReal_pos _ _ _ hS).ne', log_one, mul_zero, sub_zero]
  refine ⟨integrable_mutualInfoPDF_integrand_swap hint, ?_⟩
  rw [gaussianTestPDF, mutualInfoPDF_swap, mutualInfoPDF_gaussianChannel_gaussian hP hD]
  have hD' : (0 : ℝ) < D := by positivity
  congr 2
  rw [NNReal.coe_sub hDS.le]
  field_simp
  ring

end Test

/-- **Theorem 10.3.2.** The information rate distortion function of a `N(0, σ²)` source with
squared-error distortion is `R(D) = ½ log (σ²/D)` for `0 < D ≤ σ²` and `R(D) = 0` for
`D > σ²`. -/
theorem gaussianInfoRD_eq {S D : ℝ≥0} (hS : S ≠ 0) (hD : D ≠ 0) :
    gaussianInfoRD S D = if D ≤ S then 1 / 2 * log (S / D) else 0 := by
  set s := {I | ∃ f : ℝ × ℝ → ℝ, IsPDF (volume.prod volume) f ∧
    marginalFst volume f = gaussianPDFReal 0 S ∧
    Integrable (fun z => f z * (z.1 - z.2) ^ 2) (volume.prod volume) ∧
    ∫ z, f z * (z.1 - z.2) ^ 2 ∂(volume.prod volume) ≤ D ∧
    Integrable (fun z => f z * log (f z / (marginalFst volume f z.1 * marginalSnd volume f z.2)))
      (volume.prod volume) ∧
    mutualInfoPDF volume volume f = I}
  have hS' : (0 : ℝ) < S := by positivity
  -- The test channel with distortion `D' < S`, `D' ≤ D` is admissible.
  have hmem : ∀ D' : ℝ≥0, D' ≠ 0 → D' < S → D' ≤ D → 1 / 2 * log (S / D') ∈ s := by
    intro D' hD' hD'S hD'D
    obtain ⟨hi, he⟩ := mutualInfoPDF_gaussianTest hD'S hD'
    obtain ⟨h2, e2⟩ := integral_gaussianTestPDF_mul_sq hD'S hD'
    exact ⟨_, gaussianTestPDF_isPDF hD'S hD', marginalFst_gaussianTestPDF hD'S hD', h2,
      e2.trans_le (by exact_mod_cast hD'D), hi, he⟩
  have hnn : ∀ I ∈ s, 0 ≤ I := by
    rintro _ ⟨f, hf, -, -, -, -, rfl⟩
    exact mutualInfoPDF_nonneg' hf
  rcases lt_or_ge D S with hDS | hSD
  · simp only [hDS.le, ↓reduceIte]
    refine IsLeast.csInf_eq ⟨hmem D hD hDS le_rfl, ?_⟩
    rintro _ ⟨f, hf, hX, h2, hfD, hI, rfl⟩
    exact half_log_div_le_mutualInfoPDF hS hD hf hX h2 hfD hI
  · -- For `D ≥ S`, the rates `½ log (S/D')` with `D' < S` tend to `0`.
    have hval : (if D ≤ S then 1 / 2 * log (S / D) else 0) = 0 := by
      split_ifs with h
      · rw [le_antisymm h hSD, div_self (by positivity), log_one, mul_zero]
      · rfl
    rw [hval]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
      (le_csInf ⟨_, hmem (S / 2) (by positivity) (NNReal.half_lt_self hS)
        ((NNReal.half_le_self S).trans hSD)⟩ hnn)
    set D' : ℝ≥0 := S * (exp (-ε)).toNNReal
    have hD'coe : (D' : ℝ) = S * exp (-ε) := by
      simp [D', Real.coe_toNNReal _ (exp_pos _).le]
    have hD'0 : D' ≠ 0 := by
      intro h
      have := congrArg NNReal.toReal h
      rw [hD'coe, NNReal.coe_zero] at this
      exact (mul_pos hS' (exp_pos _)).ne' this
    have hD'S : D' < S := by
      rw [← NNReal.coe_lt_coe, hD'coe]
      exact mul_lt_of_lt_one_right hS' (exp_lt_one_iff.2 (neg_lt_zero.2 hε))
    calc sInf s ≤ 1 / 2 * log (S / D') :=
          csInf_le ⟨0, hnn⟩ (hmem D' hD'0 hD'S (hD'S.le.trans hSD))
      _ = ε / 2 := by
          rw [hD'coe, div_mul_cancel_left₀ hS'.ne', log_inv, log_exp]
          ring
      _ ≤ 0 + ε := by linarith

/-- **(10.37)** The distortion rate function of the Gaussian source: for `R ≥ 0`, the rate `R`
suffices for the distortion `D` iff `D ≥ σ² e^{-2R}`. -/
theorem gaussianInfoRD_le_iff {S D : ℝ≥0} (hS : S ≠ 0) (hD : D ≠ 0) {R : ℝ} (hR : 0 ≤ R) :
    gaussianInfoRD S D ≤ R ↔ S * exp (-(2 * R)) ≤ D := by
  have hS' : (0 : ℝ) < S := by positivity
  have hD' : (0 : ℝ) < D := by positivity
  rw [gaussianInfoRD_eq hS hD]
  split_ifs with hDS
  · rw [show 1 / 2 * log (S / D) ≤ R ↔ log (S / D) ≤ 2 * R by constructor <;> intro h <;>
      linarith, log_le_iff_le_exp (by positivity), div_le_iff₀ hD', exp_neg,
      ← div_eq_mul_inv, div_le_iff₀ (exp_pos _), mul_comm]
  · simp only [hR, true_iff]
    push Not at hDS
    have : S * exp (-(2 * R)) ≤ S := mul_le_of_le_one_right hS'.le
      (exp_le_one_iff.2 (by linarith))
    exact this.trans (by exact_mod_cast hDS.le)

/-- **Notation (Lecture 1 of [elgamal2010]).** The quadratic Gaussian rate function
`R(x) = ½ log x` for `x ≥ 1` and `0` otherwise, in nats. -/
def gaussianRateFun (x : ℝ) : ℝ := if 1 ≤ x then 1 / 2 * log x else 0

/-- **Theorem 6 of Lecture 3 of [elgamal2010]**, for the information rate–distortion function:
for a `N(0, P)` source with squared-error distortion, `R(D) = R(P/D)`. -/
theorem gaussianInfoRD_eq_gaussianRateFun {S D : ℝ≥0} (hS : S ≠ 0) (hD : D ≠ 0) :
    gaussianInfoRD S D = gaussianRateFun (S / D) := by
  have hD' : (0 : ℝ) < D := by positivity
  rw [gaussianInfoRD_eq hS hD, gaussianRateFun]
  by_cases h : D ≤ S
  · rw [ite_eq_left h, ite_eq_left ((one_le_div hD').2 (by exact_mod_cast h))]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (by exact_mod_cast (one_le_div hD').1 h')]

end InfoTheory
