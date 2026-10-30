/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MaxEntropy.Basic
public import InfoTheoryLib.DifferentialEntropy.Gaussian
public import InfoTheoryLib.Entropy.Bounds

/-!
# Classical maximum entropy distributions

Applications of Theorem 12.1.1: the uniform density on `[a, b]` (no constraint), the exponential
density on `[0, ∞)` (given mean), the normal density on `ℝ` (given mean and second moment), and,
for pmfs, the Gibbs distribution `p_λ(x) ∝ e^{λ g(x)}` (given the mean of `g`).

## Main definitions

* `expDensity m`: the exponential density `(1/m) e^{-x/m}` with mean `m`.
* `gibbsPMF g λ`: the pmf `e^{λ g(x)}/∑_y e^{λ g(y)}` (12.19).

## Main statements

* `diffEntropy_le_log_of_Icc`, `diffEntropy_eq_log_of_Icc_iff`: **Example 12.2.4**.
* `diffEntropy_le_of_mean`, `diffEntropy_eq_of_mean_iff`: **Example 12.2.5**, with
  `diffEntropy_expDensity`, `h = 1 + log m`.
* `diffEntropy_le_of_moments`: **Example 12.2.7**, `N(α₁, α₂ - α₁²)` maximizes the entropy.
* `entropy_le_gibbsPMF`, `entropy_eq_gibbsPMF_iff`: **Example 12.2.3**, (12.19).

## Implementation notes

Densities on a support set `S` are densities with respect to `volume.restrict S`. We take
`S = (0, ∞)` for the exponential density, which differs from `[0, ∞)` by a null set.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 12.2
-/

open Real MeasureTheory Filter Topology Finset Set
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The uniform density -/

section Uniform

variable {a b : ℝ}

lemma isPDF_const_Icc (hab : a < b) :
    IsPDF (volume.restrict (Icc a b)) fun _ : ℝ => 1 / (b - a) := by
  have hba : 0 < b - a := by linarith
  refine ⟨measurable_const, fun _ => by positivity, integrable_const _, ?_⟩
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, volume_real_Icc_of_le hab.le]
  field_simp

/-- **Example 12.2.4.** The uniform density maximizes the entropy among the densities on `[a, b]`:
`h(g) ≤ log (b - a)`. -/
theorem diffEntropy_le_log_of_Icc (hab : a < b) {g : ℝ → ℝ}
    (hg : IsPDF (volume.restrict (Icc a b)) g)
    (hent : Integrable (fun x => negMulLog (g x)) (volume.restrict (Icc a b))) :
    diffEntropy (volume.restrict (Icc a b)) g ≤ log (b - a) := by
  have hba : 0 < b - a := by linarith
  have h := diffEntropy_le_of_eq_exp (ι := Fin 0) (μ := volume.restrict (Icc a b))
    (f := fun _ => 1 / (b - a)) (fun i => i.elim0) (-log (b - a)) (fun i => i.elim0)
    (isPDF_const_Icc hab)
    (fun _ => by simp only [univ_eq_empty, sum_empty, add_zero, exp_neg, exp_log hba, one_div])
    (fun i => i.elim0) hg (fun i => i.elim0) (fun i => i.elim0) hent
  refine h.trans_eq ?_
  rw [diffEntropy, integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    volume_real_Icc_of_le hab.le, negMulLog, one_div, log_inv]
  field_simp

/-- **Example 12.2.4 (equality).** `h(g) = log (b - a)` iff `g` is the uniform density. -/
theorem diffEntropy_eq_log_of_Icc_iff (hab : a < b) {g : ℝ → ℝ}
    (hg : IsPDF (volume.restrict (Icc a b)) g)
    (hent : Integrable (fun x => negMulLog (g x)) (volume.restrict (Icc a b))) :
    diffEntropy (volume.restrict (Icc a b)) g = log (b - a) ↔
      g =ᵐ[volume.restrict (Icc a b)] fun _ => 1 / (b - a) := by
  have hba : 0 < b - a := by linarith
  have h := diffEntropy_eq_of_eq_exp_iff (ι := Fin 0) (μ := volume.restrict (Icc a b))
    (f := fun _ => 1 / (b - a)) (fun i => i.elim0) (-log (b - a)) (fun i => i.elim0)
    (isPDF_const_Icc hab)
    (fun _ => by simp only [univ_eq_empty, sum_empty, add_zero, exp_neg, exp_log hba, one_div])
    (fun i => i.elim0) hg (fun i => i.elim0) (fun i => i.elim0) hent
  have hval : diffEntropy (volume.restrict (Icc a b)) (fun _ => 1 / (b - a)) = log (b - a) := by
    rw [diffEntropy, integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
      volume_real_Icc_of_le hab.le, negMulLog, one_div, log_inv]
    field_simp
  rw [← hval]
  exact h

end Uniform

/-! ### The exponential density -/

section Exponential

variable {m : ℝ}

/-- The exponential density `(1/m) e^{-x/m}` with mean `m` (12.21). -/
def expDensity (m x : ℝ) : ℝ := exp (-x / m) / m

lemma expDensity_eq_exp (hm : 0 < m) (x : ℝ) :
    expDensity m x = exp (-log m + ∑ i : Fin 1, ![-(1 / m)] i * ![fun x : ℝ => x] i x) := by
  rw [expDensity, Fin.sum_univ_one, exp_add, exp_neg, exp_log hm]
  simp only [Matrix.cons_val_zero]
  rw [div_eq_inv_mul]
  congr 2
  ring

/-- `∫₀^∞ (1/m) e^{-x/m} dx = 1` and `∫₀^∞ x (1/m) e^{-x/m} dx = m`. -/
lemma expDensity_moments (hm : 0 < m) :
    IntegrableOn (expDensity m) (Ioi 0) ∧ ∫ x in Ioi 0, expDensity m x = 1 ∧
      IntegrableOn (fun x => expDensity m x * x) (Ioi 0) ∧
        ∫ x in Ioi 0, expDensity m x * x = m := by
  -- Antiderivatives `-e^{-x/m}` and `-(x + m) e^{-x/m}`.
  have hd0 : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => -exp (-x / m)) (expDensity m x) x := by
    intro x _
    have hf : (fun x => -exp (-x / m)) = fun x => -exp (x * (-1 / m)) := by
      funext x; ring_nf
    rw [hf]
    refine ((hasDerivAt_mul_const (-1 / m)).exp.neg).congr_deriv ?_
    rw [expDensity, show x * (-1 / m) = -x / m by ring]
    ring
  have hd1 : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => -((x + m) * exp (-x / m)))
      (expDensity m x * x) x := by
    intro x _
    have hf : (fun x => -((x + m) * exp (-x / m))) =
        fun x => -((x + m) * exp (x * (-1 / m))) := by
      funext x; ring_nf
    rw [hf]
    refine ((((hasDerivAt_id' x).add_const m).mul
      (hasDerivAt_mul_const (-1 / m)).exp).neg).congr_deriv ?_
    rw [expDensity, show x * (-1 / m) = -x / m by ring]
    field_simp
    ring
  have hlim_t : Tendsto (fun x : ℝ => x / m) atTop atTop := tendsto_id.atTop_div_const hm
  have hl0 : Tendsto (fun x : ℝ => -exp (-x / m)) atTop (𝓝 0) := by
    have := (tendsto_exp_neg_atTop_nhds_zero.comp hlim_t).neg
    simpa [neg_div] using this
  have hl1 : Tendsto (fun x : ℝ => -((x + m) * exp (-x / m))) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlim_t
    have h2 := tendsto_exp_neg_atTop_nhds_zero.comp hlim_t
    have := ((h1.add h2).const_mul m).neg
    simp only [mul_zero, add_zero, neg_zero] at this
    refine this.congr fun x => ?_
    simp only [Function.comp_apply, pow_one, neg_div]
    field_simp
  have hpos0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ expDensity m x := fun x _ => by
    unfold expDensity; positivity
  have hpos1 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ expDensity m x * x := fun x hx =>
    mul_nonneg (hpos0 x hx) (le_of_lt hx)
  have i0 := integrableOn_Ioi_deriv_of_nonneg' hd0 hpos0 hl0
  have i1 := integrableOn_Ioi_deriv_of_nonneg' hd1 hpos1 hl1
  refine ⟨i0, ?_, i1, ?_⟩
  · rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd0 i0 hl0]
    simp
  · rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd1 i1 hl1]
    simp

lemma expDensity_isPDF (hm : 0 < m) : IsPDF (volume.restrict (Ioi 0)) (expDensity m) :=
  ⟨by unfold expDensity; fun_prop, fun x => by unfold expDensity; positivity,
    (expDensity_moments hm).1, (expDensity_moments hm).2.1⟩

/-- The entropy of the exponential density with mean `m` is `1 + log m` nats. -/
theorem diffEntropy_expDensity (hm : 0 < m) :
    diffEntropy (volume.restrict (Ioi 0)) (expDensity m) = 1 + log m := by
  obtain ⟨-, h⟩ := integral_mul_log_eq_exp (μ := volume.restrict (Ioi 0)) (ι := Fin 1)
    ![fun x : ℝ => x] (-log m) ![-(1 / m)] (expDensity_eq_exp hm) (expDensity_isPDF hm)
    fun i => by fin_cases i; exact (expDensity_moments hm).2.2.1
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, (expDensity_moments hm).2.2.2] at h
  rw [diffEntropy]
  simp_rw [negMulLog, neg_mul, integral_neg, h]
  field_simp
  ring

/-- **Example 12.2.5.** The exponential density maximizes the entropy among the densities on
`[0, ∞)` with mean `m`: `h(g) ≤ 1 + log m`. -/
theorem diffEntropy_le_of_mean (hm : 0 < m) {g : ℝ → ℝ} (hg : IsPDF (volume.restrict (Ioi 0)) g)
    (hgx : Integrable (fun x => g x * x) (volume.restrict (Ioi 0)))
    (hmean : ∫ x in Ioi 0, g x * x = m)
    (hent : Integrable (fun x => negMulLog (g x)) (volume.restrict (Ioi 0))) :
    diffEntropy (volume.restrict (Ioi 0)) g ≤ 1 + log m := by
  rw [← diffEntropy_expDensity hm]
  exact diffEntropy_le_of_eq_exp (ι := Fin 1) ![fun x : ℝ => x] (-log m) ![-(1 / m)]
    (expDensity_isPDF hm) (expDensity_eq_exp hm)
    (fun i => by fin_cases i; exact (expDensity_moments hm).2.2.1) hg
    (fun i => by fin_cases i; exact hgx)
    (fun i => by fin_cases i; simp [hmean, (expDensity_moments hm).2.2.2]) hent

/-- **Example 12.2.5 (equality).** Equality holds iff `g` is the exponential density. -/
theorem diffEntropy_eq_of_mean_iff (hm : 0 < m) {g : ℝ → ℝ}
    (hg : IsPDF (volume.restrict (Ioi 0)) g)
    (hgx : Integrable (fun x => g x * x) (volume.restrict (Ioi 0)))
    (hmean : ∫ x in Ioi 0, g x * x = m)
    (hent : Integrable (fun x => negMulLog (g x)) (volume.restrict (Ioi 0))) :
    diffEntropy (volume.restrict (Ioi 0)) g = 1 + log m ↔
      g =ᵐ[volume.restrict (Ioi 0)] expDensity m := by
  rw [← diffEntropy_expDensity hm]
  exact diffEntropy_eq_of_eq_exp_iff (ι := Fin 1) ![fun x : ℝ => x] (-log m) ![-(1 / m)]
    (expDensity_isPDF hm) (expDensity_eq_exp hm)
    (fun i => by fin_cases i; exact (expDensity_moments hm).2.2.1) hg
    (fun i => by fin_cases i; exact hgx)
    (fun i => by fin_cases i; simp [hmean, (expDensity_moments hm).2.2.2]) hent

end Exponential

/-! ### The normal density -/

/-- **Example 12.2.7.** Among the densities on `ℝ` with `E X = α₁` and `E X² = α₂`, the normal
density `N(α₁, α₂ - α₁²)` has the largest entropy: `h(g) ≤ ½ log (2πe (α₂ - α₁²))`. -/
theorem diffEntropy_le_of_moments {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hent : Integrable fun x => negMulLog (g x)) (h1 : Integrable fun x => g x * x)
    (h2 : Integrable fun x => g x * x ^ 2) {α₁ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hm1 : ∫ x, g x * x = α₁) (hm2 : ∫ x, g x * x ^ 2 = α₁ ^ 2 + v) :
    diffEntropy volume g ≤ 1 / 2 * log (2 * π * exp 1 * v) := by
  refine diffEntropy_le_of_integral_mul_sq hg hent hv (m := α₁) ?_
  have e : (fun x => g x * (x - α₁) ^ 2) =
      fun x => g x * x ^ 2 - 2 * α₁ * (g x * x) + α₁ ^ 2 * g x := funext fun x => by ring
  have hA : Integrable fun x => g x * x ^ 2 - 2 * α₁ * (g x * x) := h2.sub (h1.const_mul _)
  have hB : Integrable fun x => α₁ ^ 2 * g x := hg.integrable.const_mul _
  rw [e, integral_add hA hB, integral_sub h2 (h1.const_mul _), integral_const_mul,
    integral_const_mul, hm1, hm2, hg.integral_eq_one]
  ring

/-! ### The Gibbs distribution -/

section Gibbs

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **(12.19)** The Gibbs distribution `p_λ(x) = e^{λ g(x)}/∑_y e^{λ g(y)}`. -/
def gibbsPMF (g : α → ℝ) (lam : ℝ) (x : α) : ℝ := exp (lam * g x) / ∑ y, exp (lam * g y)

lemma sum_exp_pos (g : α → ℝ) (lam : ℝ) : 0 < ∑ y, exp (lam * g y) :=
  sum_pos (fun _ _ => exp_pos _) univ_nonempty

lemma gibbsPMF_isPMF (g : α → ℝ) (lam : ℝ) : IsPMF (gibbsPMF g lam) :=
  ⟨fun x => (div_pos (exp_pos _) (sum_exp_pos g lam)).le, by
    simp only [gibbsPMF, ← sum_div]; exact div_self (sum_exp_pos g lam).ne'⟩

lemma gibbsPMF_eq_exp (g : α → ℝ) (lam : ℝ) (x : α) :
    gibbsPMF g lam x = exp (-log (∑ y, exp (lam * g y)) + ∑ i : Fin 1, ![lam] i * ![g] i x) := by
  rw [gibbsPMF, Fin.sum_univ_one, exp_add, exp_neg, exp_log (sum_exp_pos g lam)]
  simp only [Matrix.cons_val_zero]
  rw [div_eq_inv_mul]

/-- **Example 12.2.3, (12.19).** Among the pmfs with `∑ₓ p(x) g(x) = ∑ₓ p_λ(x) g(x)`, the Gibbs
distribution `p_λ ∝ e^{λ g}` has the largest entropy. For dice with `g(i) = i`, this is
Boltzmann's distribution of the faces given the mean `α`. -/
theorem entropy_le_gibbsPMF (g : α → ℝ) (lam : ℝ) {p : α → ℝ} (hp : IsPMF p)
    (hmean : ∑ x, p x * g x = ∑ x, gibbsPMF g lam x * g x) :
    entropy p ≤ entropy (gibbsPMF g lam) :=
  entropy_le_of_eq_exp (ι := Fin 1) ![g] _ ![lam] (gibbsPMF_isPMF g lam) (gibbsPMF_eq_exp g lam)
    hp fun i => by fin_cases i; exact hmean

/-- **Example 12.2.3 (uniqueness).** -/
theorem entropy_eq_gibbsPMF_iff (g : α → ℝ) (lam : ℝ) {p : α → ℝ} (hp : IsPMF p)
    (hmean : ∑ x, p x * g x = ∑ x, gibbsPMF g lam x * g x) :
    entropy p = entropy (gibbsPMF g lam) ↔ p = gibbsPMF g lam :=
  entropy_eq_of_eq_exp_iff (ι := Fin 1) ![g] _ ![lam] (gibbsPMF_isPMF g lam)
    (gibbsPMF_eq_exp g lam) hp fun i => by fin_cases i; exact hmean

end Gibbs

end InfoTheory
