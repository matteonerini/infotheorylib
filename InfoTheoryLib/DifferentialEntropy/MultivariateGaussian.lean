/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.Gaussian
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The multivariate normal distribution

The multivariate normal density `N(m, K)` on `ℝⁿ`, with mean `m` and positive definite covariance
matrix `K`, is `f(x) = ((2π)ⁿ |K|)^{-1/2} exp (-½ (x - m)ᵀ K⁻¹ (x - m))`. Its differential entropy
is `½ log ((2πe)ⁿ |K|)`, and it maximizes the differential entropy among all densities with
the same covariance. Applied to the independence bound, this gives Hadamard's inequality
`|K| ≤ ∏ᵢ Kᵢᵢ`.

## Main definitions

* `mvGaussianPDF m K`: the density of `N(m, K)`, (8.35).

## Main statements

* `mvGaussianPDF_isPDF`: `N(m, K)` is a probability density.
* `integral_mvGaussianPDF_mul`: its covariance is `K`.
* `diffEntropy_mvGaussianPDF`: Theorem 8.4.1, `h(N(m, K)) = ½ log ((2πe)ⁿ |K|)`.
* `diffEntropy_le_of_covariance`, `diffEntropy_eq_of_covariance_iff`: Theorem 8.6.5, a density
  with covariance `K` has `h ≤ ½ log ((2πe)ⁿ |K|)`, with equality iff it is `N(m, K)`.
* `det_le_prod_diag`: Hadamard's inequality (8.64), `|K| ≤ ∏ᵢ Kᵢᵢ`.
* `diffEntropy_le_of_covariance_trace`: Lecture 2 of [elgamal2010],
  `h(X) ≤ (n/2) log (2πe (1/n) ∑ᵢ Kᵢᵢ)`.

## Implementation notes

The integrals of the normal density are computed by the change of variables `x = m + U y`, where
`K = U D Uᵀ` is the orthogonal diagonalization of `K` (Mathlib's spectral theorem). In the new
variables the density is a product of one-dimensional normal densities.

## References

Numbers without a source refer to [cover2006].

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 8.4 and
  8.6
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
-/

open Real MeasureTheory ProbabilityTheory Matrix Filter

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **(8.35)** The density of the multivariate normal distribution `N(m, K)`:
`f(x) = ((2π)ⁿ |K|)^{-1/2} exp (-½ (x - m)ᵀ K⁻¹ (x - m))`. -/
def mvGaussianPDF (m : ι → ℝ) (K : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (√((2 * π) ^ Fintype.card ι * K.det))⁻¹ * exp (-(1 / 2) * ((x - m) ⬝ᵥ (K⁻¹ *ᵥ (x - m))))

/-! ### Orthogonal diagonalization -/

namespace PosDef

variable {K : Matrix ι ι ℝ} (hK : K.PosDef)

/-- The orthogonal matrix `U` of eigenvectors of `K`. -/
abbrev eigU : Matrix ι ι ℝ := (hK.1.eigenvectorUnitary : Matrix ι ι ℝ)

/-- The eigenvalues of `K`, all positive. -/
abbrev eigval : ι → ℝ := hK.1.eigenvalues

lemma eigval_pos (i : ι) : 0 < eigval hK i := hK.eigenvalues_pos i

/-- The eigenvalues of `K` as variances. -/
abbrev eigvalNN (i : ι) : NNReal := ⟨eigval hK i, (eigval_pos hK i).le⟩

lemma eigvalNN_ne_zero (i : ι) : eigvalNN hK i ≠ 0 := fun h =>
  (eigval_pos hK i).ne' (congrArg NNReal.toReal h)

lemma eigU_transpose_mul : (eigU hK)ᵀ * eigU hK = 1 := by
  have h := Unitary.coe_star_mul_self hK.1.eigenvectorUnitary
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

lemma eigU_mul_transpose : eigU hK * (eigU hK)ᵀ = 1 := by
  have h := Unitary.coe_mul_star_self hK.1.eigenvectorUnitary
  rwa [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- The spectral theorem: `K = U D Uᵀ`. -/
lemma eq_eigU : K = eigU hK * diagonal (eigval hK) * (eigU hK)ᵀ := by
  conv_lhs => rw [hK.1.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  simp

/-- `K⁻¹ = U D⁻¹ Uᵀ`. -/
lemma inv_eq_eigU : K⁻¹ = eigU hK * diagonal (eigval hK)⁻¹ * (eigU hK)ᵀ := by
  refine inv_eq_right_inv ?_
  rw [show K * (eigU hK * diagonal (eigval hK)⁻¹ * (eigU hK)ᵀ) =
    eigU hK * diagonal (eigval hK) * (eigU hK)ᵀ * (eigU hK * diagonal (eigval hK)⁻¹ * (eigU hK)ᵀ)
    from congrArg (· * _) (eq_eigU hK)]
  have hd : diagonal (eigval hK) * diagonal (eigval hK)⁻¹ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp [(eigval_pos hK i).ne']
  calc eigU hK * diagonal (eigval hK) * (eigU hK)ᵀ *
        (eigU hK * diagonal (eigval hK)⁻¹ * (eigU hK)ᵀ)
      = eigU hK * (diagonal (eigval hK) * ((eigU hK)ᵀ * eigU hK) * diagonal (eigval hK)⁻¹) *
          (eigU hK)ᵀ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [eigU_transpose_mul, Matrix.mul_one, hd, Matrix.mul_one, eigU_mul_transpose]

lemma det_eq_prod_eigval : K.det = ∏ i, eigval hK i := by
  simpa using hK.1.det_eq_prod_eigenvalues

lemma abs_det_eigU : |(eigU hK).det| = 1 := by
  have h := congrArg det (eigU_transpose_mul hK)
  rw [det_mul, det_transpose, det_one, ← sq, ← sq_abs] at h
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 h

lemma eigU_transpose_mulVec_eigU (y : ι → ℝ) : (eigU hK)ᵀ *ᵥ (eigU hK *ᵥ y) = y := by
  rw [mulVec_mulVec, eigU_transpose_mul, one_mulVec]

lemma dotProduct_eigU (y z : ι → ℝ) : (eigU hK *ᵥ y) ⬝ᵥ (eigU hK *ᵥ z) = y ⬝ᵥ z := by
  rw [dotProduct_mulVec, ← mulVec_transpose, eigU_transpose_mulVec_eigU]

/-- The quadratic form in the new variables: `(Uy)ᵀ K⁻¹ (Uy) = ∑ᵢ yᵢ²/λᵢ`. -/
lemma quadForm_eigU (y : ι → ℝ) :
    (eigU hK *ᵥ y) ⬝ᵥ (K⁻¹ *ᵥ (eigU hK *ᵥ y)) = ∑ i, y i ^ 2 / eigval hK i := by
  rw [inv_eq_eigU hK, ← mulVec_mulVec, ← mulVec_mulVec, eigU_transpose_mulVec_eigU,
    dotProduct_eigU]
  simp only [dotProduct, mulVec_diagonal, Pi.inv_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The change of variables `y ↦ m + U y`. -/
def eigEquiv (m : ι → ℝ) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  ((UnitaryGroup.toLinearEquiv hK.1.eigenvectorUnitary).toContinuousLinearEquiv.toHomeomorph.trans
    (Homeomorph.addLeft m)).toMeasurableEquiv

lemma eigEquiv_apply (m y : ι → ℝ) : eigEquiv hK m y = m + eigU hK *ᵥ y := rfl

/-- The change of variables `x = m + U y` preserves the Lebesgue measure. -/
lemma measurePreserving_eigEquiv (m : ι → ℝ) :
    MeasurePreserving (eigEquiv hK m) volume volume := by
  have hdet : LinearMap.det (toLin' (eigU hK)) ≠ 0 := by
    rw [LinearMap.det_toLin']
    intro h
    simpa [h] using abs_det_eigU hK
  have hlin : MeasurePreserving (toLin' (eigU hK)) volume volume := by
    refine ⟨(toLin' (eigU hK)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, LinearMap.det_toLin', abs_inv,
      abs_det_eigU hK, inv_one, ENNReal.ofReal_one, one_smul]
  have h := (measurePreserving_add_left (volume : Measure (ι → ℝ)) m).comp hlin
  convert h using 1
  funext y
  simp [eigEquiv_apply, toLin'_apply]

/-- `∫ G(x) dx = ∫ G(m + U y) dy`. -/
lemma integral_comp_eigEquiv (m : ι → ℝ) (G : (ι → ℝ) → ℝ) :
    ∫ y, G (m + eigU hK *ᵥ y) = ∫ x, G x := by
  simp_rw [← eigEquiv_apply hK m]
  exact (measurePreserving_eigEquiv hK m).integral_comp' G

lemma integrable_comp_eigEquiv_iff (m : ι → ℝ) (G : (ι → ℝ) → ℝ) :
    Integrable (fun y => G (m + eigU hK *ᵥ y)) ↔ Integrable G := by
  simp_rw [← eigEquiv_apply hK m]
  exact (measurePreserving_eigEquiv hK m).integrable_comp_emb (eigEquiv hK m).measurableEmbedding

end PosDef

/-! ### The normal density in the eigenbasis -/

lemma gaussianPDFReal_zero_apply (v : NNReal) (t : ℝ) :
    gaussianPDFReal 0 v t = (√(2 * π * v))⁻¹ * exp (-(1 / 2) * (t ^ 2 / v)) := by
  rw [gaussianPDFReal, sub_zero]
  congr 2
  field_simp

variable {K : Matrix ι ι ℝ}

/-- In the eigenbasis of `K`, the normal density `N(m, K)` is the product of the one-dimensional
normal densities `N(0, λᵢ)`: `f(m + U y) = ∏ᵢ φ_{λᵢ}(yᵢ)`. -/
lemma mvGaussianPDF_eigU (hK : K.PosDef) (m y : ι → ℝ) :
    mvGaussianPDF m K (m + PosDef.eigU hK *ᵥ y) =
      ∏ i, gaussianPDFReal 0 (PosDef.eigvalNN hK i) (y i) := by
  have hpos := PosDef.eigval_pos hK
  rw [mvGaussianPDF, add_sub_cancel_left, PosDef.quadForm_eigU, PosDef.det_eq_prod_eigval hK,
    Finset.mul_sum, exp_sum]
  simp only [gaussianPDFReal_zero_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  congr 2
  rw [← Real.sqrt_prod _ fun i _ => by positivity, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  rfl

/-! ### Moments of the normal density -/

lemma integral_gaussianPDFReal_mul_self {v : NNReal} (hv : v ≠ 0) :
    ∫ t, gaussianPDFReal 0 v t * t = 0 := by
  have h := integral_id_gaussianReal (μ := 0) (v := v)
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simpa [smul_eq_mul] using h

lemma integral_gaussianPDFReal_mul_sq_zero {v : NNReal} (hv : v ≠ 0) :
    ∫ t, gaussianPDFReal 0 v t * t ^ 2 = v := by
  simpa using integral_gaussianPDFReal_mul_sq 0 hv

lemma integrable_gaussianPDFReal_mul_sq_zero {v : NNReal} (hv : v ≠ 0) :
    Integrable fun t => gaussianPDFReal 0 v t * t ^ 2 := by
  simpa using integrable_gaussianPDFReal_mul_sq 0 hv

lemma integrable_gaussianPDFReal_mul_self {v : NNReal} (hv : v ≠ 0) :
    Integrable fun t => gaussianPDFReal 0 v t * t := by
  refine ((integrable_gaussianPDFReal 0 v).add (integrable_gaussianPDFReal_mul_sq_zero hv)).mono'
    (((measurable_gaussianPDFReal 0 v).mul measurable_id).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  have h0 := gaussianPDFReal_nonneg 0 v t
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left ht h0]

/-- A one-dimensional normal factor `φ(t)`, multiplied by `t` at the indices `k` and `l`. -/
def momentFactor (v : NNReal) (k l i : ι) (t : ℝ) : ℝ :=
  gaussianPDFReal 0 v t * ((if i = k then t else 1) * (if i = l then t else 1))

/-- The second moments of a product of centered normal densities:
`∫ ∏ᵢ φ_{vᵢ}(yᵢ) yₖ yₗ dy = vₖ` if `k = l` and `0` otherwise. -/
lemma integral_prod_gaussianPDFReal_mul {v : ι → NNReal} (hv : ∀ i, v i ≠ 0) (k l : ι) :
    Integrable (fun y : ι → ℝ => (∏ i, gaussianPDFReal 0 (v i) (y i)) * (y k * y l)) ∧
      ∫ y : ι → ℝ, (∏ i, gaussianPDFReal 0 (v i) (y i)) * (y k * y l) =
        if k = l then (v k : ℝ) else 0 := by
  have e : (fun y : ι → ℝ => (∏ i, gaussianPDFReal 0 (v i) (y i)) * (y k * y l)) =
      fun y => ∏ i, momentFactor (v i) k l i (y i) := by
    funext y
    simp only [momentFactor]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq']
    simp
  have hint : ∀ i, Integrable (momentFactor (v i) k l i) := by
    intro i
    by_cases hk : i = k <;> by_cases hl : i = l
    · subst hk; subst hl
      exact (integrable_gaussianPDFReal_mul_sq_zero (hv i)).congr
        (Eventually.of_forall fun t => by simp [momentFactor, sq])
    · subst hk
      exact (integrable_gaussianPDFReal_mul_self (hv i)).congr
        (Eventually.of_forall fun t => by simp [momentFactor, hl])
    · subst hl
      exact (integrable_gaussianPDFReal_mul_self (hv i)).congr
        (Eventually.of_forall fun t => by simp [momentFactor, hk])
    · exact (integrable_gaussianPDFReal 0 (v i)).congr
        (Eventually.of_forall fun t => by simp [momentFactor, hk, hl])
  rw [e]
  refine ⟨Integrable.fintype_prod hint, ?_⟩
  rw [integral_fintype_prod_volume_eq_prod]
  have hval : ∀ i, ∫ t, momentFactor (v i) k l i t =
      if i = k ∧ i = l then (v i : ℝ) else if i = k ∨ i = l then 0 else 1 := by
    intro i
    by_cases hk : i = k <;> by_cases hl : i = l
    · subst hk; subst hl
      simpa [momentFactor, sq] using integral_gaussianPDFReal_mul_sq_zero (hv i)
    · subst hk
      simpa [momentFactor, hl] using integral_gaussianPDFReal_mul_self (hv i)
    · subst hl
      simpa [momentFactor, hk] using integral_gaussianPDFReal_mul_self (hv i)
    · simpa [momentFactor, hk, hl] using integral_gaussianPDFReal_eq_one 0 (hv i)
  simp only [hval]
  split_ifs with hkl
  · subst hkl
    rw [Finset.prod_eq_single k (fun i _ hi => by simp [hi]) (by simp)]
    simp
  · exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hkl])

variable (hK : K.PosDef)
include hK

/-- The product of the one-dimensional normal densities in the eigenbasis is a density. -/
lemma integral_prod_gaussianPDFReal_eigval :
    ∫ y : ι → ℝ, ∏ i, gaussianPDFReal 0 (PosDef.eigvalNN hK i) (y i) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one 0 (PosDef.eigvalNN_ne_zero hK _)]

lemma mvGaussianPDF_pos (m x : ι → ℝ) : 0 < mvGaussianPDF m K x := by
  have hdet : 0 < K.det := hK.det_pos
  unfold mvGaussianPDF
  positivity

/-- **(8.35)** The multivariate normal density is a probability density. -/
theorem mvGaussianPDF_isPDF (m : ι → ℝ) : IsPDF volume (mvGaussianPDF m K) := by
  have hint : ∫ x, mvGaussianPDF m K x = 1 := by
    rw [← PosDef.integral_comp_eigEquiv hK m]
    simp_rw [mvGaussianPDF_eigU hK m]
    exact integral_prod_gaussianPDFReal_eigval hK
  refine ⟨?_, fun x => (mvGaussianPDF_pos hK m x).le, ?_, hint⟩
  · unfold mvGaussianPDF
    fun_prop
  · exact Integrable.of_integral_ne_zero (by rw [hint]; exact one_ne_zero)

/-- **The covariance of `N(m, K)`.** `∫ f(x) (x - m)ₐ (x - m)_b dx = K_{ab}`. -/
theorem integral_mvGaussianPDF_mul (m : ι → ℝ) (a b : ι) :
    Integrable (fun x => mvGaussianPDF m K x * ((x - m) a * (x - m) b)) ∧
      ∫ x, mvGaussianPDF m K x * ((x - m) a * (x - m) b) = K a b := by
  set U := PosDef.eigU hK
  set φ : (ι → ℝ) → ℝ := fun y => ∏ i, gaussianPDFReal 0 (PosDef.eigvalNN hK i) (y i)
  have hφ := fun k l => integral_prod_gaussianPDFReal_mul (PosDef.eigvalNN_ne_zero hK) k l
  -- In the eigenbasis the integrand is `∑ₖ ∑ₗ Uₐₖ U_bₗ φ(y) yₖ yₗ`.
  have hUy : ∀ (y : ι → ℝ) c, (U *ᵥ y) c = ∑ k, U c k * y k := fun _ _ => rfl
  have e : (fun y => mvGaussianPDF m K (m + U *ᵥ y) * ((m + U *ᵥ y - m) a * (m + U *ᵥ y - m) b)) =
      fun y => ∑ k, ∑ l, U a k * U b l * (φ y * (y k * y l)) := by
    funext y
    rw [mvGaussianPDF_eigU hK, add_sub_cancel_left, hUy y a, hUy y b, Finset.sum_mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [φ]
    ring
  have hint : Integrable fun y => ∑ k, ∑ l, U a k * U b l * (φ y * (y k * y l)) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hφ k l).1.const_mul _
  refine ⟨?_, ?_⟩
  · rw [← PosDef.integrable_comp_eigEquiv_iff hK m, e]
    exact hint
  · rw [← PosDef.integral_comp_eigEquiv hK m, e, integral_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => (hφ k l).1.const_mul _]
    simp_rw [integral_finsetSum _ fun l _ => (hφ _ l).1.const_mul _, integral_const_mul,
      fun k l => (hφ k l).2]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    conv_rhs => rw [PosDef.eq_eigU hK]
    simp only [Matrix.mul_apply, transpose_apply, diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun k _ => ?_
    change PosDef.eigU hK a k * PosDef.eigU hK b k * PosDef.eigval hK k = _
    ring

omit hK in
/-- `log f(x) = -½ log ((2π)ⁿ |K|) - ½ ∑ₐ ∑_b (x - m)ₐ (K⁻¹)ₐ_b (x - m)_b`. -/
lemma log_mvGaussianPDF (hdet : 0 < K.det) (m x : ι → ℝ) :
    log (mvGaussianPDF m K x) = -(log ((2 * π) ^ Fintype.card ι * K.det) / 2) -
      1 / 2 * ∑ a, ∑ b, K⁻¹ a b * ((x - m) a * (x - m) b) := by
  have hc : 0 < (2 * π) ^ Fintype.card ι * K.det := by positivity
  rw [mvGaussianPDF, log_mul (inv_ne_zero (sqrt_ne_zero'.2 hc)) (exp_pos _).ne', log_inv, log_exp,
    log_sqrt hc.le]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  suffices h : ∀ a b, -(1 / 2) * ((x - m) a * (K⁻¹ a b * (x - m) b)) =
      -(1 / 2 * (K⁻¹ a b * ((x - m) a * (x - m) b))) by
    simp only [h, Finset.sum_neg_distrib]
    ring
  intro a b
  ring

omit hK in
/-- The cross-entropy of a density `g` with second moments `M` relative to `N(m, K)`:
`-∫ g log f = ½ log ((2π)ⁿ |K|) + ½ ∑ₐ ∑_b (K⁻¹)ₐ_b Mₐ_b`. -/
lemma crossEntropy_mvGaussianPDF (hdet : 0 < K.det) {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g)
    (m : ι → ℝ) (M : Matrix ι ι ℝ)
    (hint : ∀ a b, Integrable fun x => g x * ((x - m) a * (x - m) b))
    (hM : ∀ a b, ∫ x, g x * ((x - m) a * (x - m) b) = M a b) :
    Integrable (fun x => g x * log (mvGaussianPDF m K x)) ∧
      -∫ x, g x * log (mvGaussianPDF m K x) =
        log ((2 * π) ^ Fintype.card ι * K.det) / 2 + 1 / 2 * ∑ a, ∑ b, K⁻¹ a b * M a b := by
  set c := log ((2 * π) ^ Fintype.card ι * K.det) / 2
  have e : (fun x => g x * log (mvGaussianPDF m K x)) =
      fun x => -c * g x - 1 / 2 * ∑ a, ∑ b, K⁻¹ a b * (g x * ((x - m) a * (x - m) b)) := by
    funext x
    rw [log_mvGaussianPDF hdet, mul_sub]
    congr 1
    · ring
    · simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  have hsum : Integrable fun x => ∑ a, ∑ b, K⁻¹ a b * (g x * ((x - m) a * (x - m) b)) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _
  rw [e]
  refine ⟨(hg.integrable.const_mul _).sub (hsum.const_mul _), ?_⟩
  have hI : ∫ x, ∑ a, ∑ b, K⁻¹ a b * (g x * ((x - m) a * (x - m) b)) =
      ∑ a, ∑ b, K⁻¹ a b * M a b := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_const_mul, hM]
      · exact fun b _ => (hint a b).const_mul _
    · exact fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _
  rw [integral_sub (hg.integrable.const_mul _) (hsum.const_mul _), integral_const_mul,
    integral_const_mul, hg.integral_eq_one, hI]
  ring

/-- `∑ₐ ∑_b (K⁻¹)ₐ_b Kₐ_b = n`, the trace of `K⁻¹ K`. -/
lemma sum_inv_mul_self : ∑ a, ∑ b, K⁻¹ a b * K a b = Fintype.card ι := by
  have hsymm : ∀ a b, K a b = K b a := fun a b => by
    simpa using (hK.1.apply a b).symm
  have h1 : K⁻¹ * K = 1 := nonsing_inv_mul K (isUnit_iff_ne_zero.2 hK.det_pos.ne')
  rw [← trace_one (n := ι) (R := ℝ), ← h1, trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun b _ => by rw [hsymm a b]

omit hK in
lemma log_two_pi_e_pow (hdet : 0 < K.det) :
    log ((2 * π) ^ Fintype.card ι * K.det) / 2 + 1 / 2 * Fintype.card ι =
      1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) := by
  have e : (2 * π * exp 1) ^ Fintype.card ι * K.det =
      (2 * π) ^ Fintype.card ι * K.det * exp 1 ^ Fintype.card ι := by ring
  have h1 : log (exp 1 ^ Fintype.card ι) = Fintype.card ι := by
    rw [← exp_nat_mul, log_exp, mul_one]
  rw [e, log_mul (x := (2 * π) ^ Fintype.card ι * K.det) (by positivity) (by positivity), h1]
  ring

/-- **Theorem 8.4.1 (Entropy of a multivariate normal distribution), (8.34)–(8.45).**
`h(N(m, K)) = ½ log ((2πe)ⁿ |K|)` nats. -/
theorem diffEntropy_mvGaussianPDF (m : ι → ℝ) :
    diffEntropy volume (mvGaussianPDF m K) =
      1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) := by
  obtain ⟨-, h⟩ := crossEntropy_mvGaussianPDF hK.det_pos (mvGaussianPDF_isPDF hK m) m K
    (fun a b => (integral_mvGaussianPDF_mul hK m a b).1)
    (fun a b => (integral_mvGaussianPDF_mul hK m a b).2)
  rw [sum_inv_mul_self hK, log_two_pi_e_pow hK.det_pos] at h
  rw [diffEntropy, ← h, ← integral_neg]
  simp [negMulLog]

lemma integrable_negMulLog_mvGaussianPDF (m : ι → ℝ) :
    Integrable fun x => negMulLog (mvGaussianPDF m K x) := by
  obtain ⟨h, -⟩ := crossEntropy_mvGaussianPDF hK.det_pos (mvGaussianPDF_isPDF hK m) m K
    (fun a b => (integral_mvGaussianPDF_mul hK m a b).1)
    (fun a b => (integral_mvGaussianPDF_mul hK m a b).2)
  exact h.neg.congr (Eventually.of_forall fun x => by simp [negMulLog])

/-- **Theorem 8.6.5.** The multivariate normal distribution maximizes the differential entropy over
all distributions with the same covariance: if `∫ g(x) (x - m)ₐ (x - m)_b dx = Kₐ_b`, then
`h(g) ≤ ½ log ((2πe)ⁿ |K|)`. The book takes `m = 0`. -/
theorem diffEntropy_le_of_covariance {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g)
    (hent : Integrable fun x => negMulLog (g x)) (m : ι → ℝ)
    (hint : ∀ a b, Integrable fun x => g x * ((x - m) a * (x - m) b))
    (hcov : ∀ a b, ∫ x, g x * ((x - m) a * (x - m) b) = K a b) :
    diffEntropy volume g ≤ 1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) := by
  obtain ⟨h1, h2⟩ := crossEntropy_mvGaussianPDF hK.det_pos hg m K hint hcov
  rw [sum_inv_mul_self hK, log_two_pi_e_pow hK.det_pos] at h2
  rw [← h2]
  exact diffEntropy_le_crossEntropy hg (mvGaussianPDF_isPDF hK m)
    (Eventually.of_forall fun x hx => absurd hx (mvGaussianPDF_pos hK m x).ne') hent h1

/-- **Theorem 8.6.5 (equality case).** Equality holds iff `g` is the normal density `N(m, K)`. -/
theorem diffEntropy_eq_of_covariance_iff {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g)
    (hent : Integrable fun x => negMulLog (g x)) (m : ι → ℝ)
    (hint : ∀ a b, Integrable fun x => g x * ((x - m) a * (x - m) b))
    (hcov : ∀ a b, ∫ x, g x * ((x - m) a * (x - m) b) = K a b) :
    diffEntropy volume g = 1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) ↔
      g =ᵐ[volume] mvGaussianPDF m K := by
  obtain ⟨h1, h2⟩ := crossEntropy_mvGaussianPDF hK.det_pos hg m K hint hcov
  rw [sum_inv_mul_self hK, log_two_pi_e_pow hK.det_pos] at h2
  rw [← h2]
  exact diffEntropy_eq_crossEntropy_iff hg (mvGaussianPDF_isPDF hK m)
    (Eventually.of_forall fun x hx => absurd hx (mvGaussianPDF_pos hK m x).ne') hent h1

/-- **Application of Corollary (8.63): Hadamard's inequality (8.64).** For a positive definite
matrix, `|K| ≤ ∏ᵢ Kᵢᵢ`. The entropy of `N(0, K)` is at most its cross-entropy relative to the
normal density with independent coordinates of variances `Kᵢᵢ`, which is `∑ᵢ ½ log (2πe Kᵢᵢ)`. -/
theorem det_le_prod_diag : K.det ≤ ∏ i, K i i := by
  set D : Matrix ι ι ℝ := diagonal fun i => K i i
  have hDpos : ∀ i, 0 < K i i := fun i => hK.diag_pos
  have hDdet : D.det = ∏ i, K i i := det_diagonal
  have hDdet_pos : 0 < D.det := by rw [hDdet]; exact Finset.prod_pos fun i _ => hDpos i
  have hDinv : D⁻¹ = diagonal fun i => (K i i)⁻¹ := by
    refine inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hDpos i).ne'
  have hD : IsPDF volume (mvGaussianPDF (0 : ι → ℝ) D) := by
    have hDposdef : D.PosDef := PosDef.diagonal (fun i => hDpos i)
    exact mvGaussianPDF_isPDF hDposdef 0
  obtain ⟨h1, h2⟩ := crossEntropy_mvGaussianPDF hDdet_pos (mvGaussianPDF_isPDF hK 0) 0 K
    (fun a b => (integral_mvGaussianPDF_mul hK 0 a b).1)
    (fun a b => (integral_mvGaussianPDF_mul hK 0 a b).2)
  have hsum : ∑ a, ∑ b, D⁻¹ a b * K a b = Fintype.card ι := by
    simp only [hDinv, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    simp [inv_mul_cancel₀ (hDpos _).ne']
  rw [hsum, log_two_pi_e_pow hDdet_pos] at h2
  have hle := diffEntropy_le_crossEntropy (mvGaussianPDF_isPDF hK 0) hD
    (Eventually.of_forall fun x hx => by
      exact absurd hx (mvGaussianPDF_pos (PosDef.diagonal fun i => hDpos i) 0 x).ne')
    (integrable_negMulLog_mvGaussianPDF hK 0) h1
  rw [h2, diffEntropy_mvGaussianPDF hK] at hle
  have hlog : log ((2 * π * exp 1) ^ Fintype.card ι * K.det) ≤
      log ((2 * π * exp 1) ^ Fintype.card ι * D.det) := by linarith
  rw [log_le_log_iff (by have := hK.det_pos; positivity) (by positivity)] at hlog
  rw [← hDdet]
  exact le_of_mul_le_mul_left hlog (by positivity)

omit [DecidableEq ι] in
/-- **Lecture 2 of [elgamal2010].** A density with covariance `K` on `ℝⁿ` has
`h(X) ≤ (n/2) log (2πe (1/n) ∑ᵢ Kᵢᵢ)`: its differential entropy is at most that of `n` i.i.d.
Gaussian coordinates whose variance is the average variance. -/
theorem diffEntropy_le_of_covariance_trace [Nonempty ι] {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g)
    (hent : Integrable fun x => negMulLog (g x)) (m : ι → ℝ)
    (hint : ∀ a b, Integrable fun x => g x * ((x - m) a * (x - m) b))
    (hcov : ∀ a b, ∫ x, g x * ((x - m) a * (x - m) b) = K a b) :
    diffEntropy volume g ≤
      Fintype.card ι / 2 * log (2 * π * exp 1 * ((∑ i, K i i) / Fintype.card ι)) := by
  classical
  have h1 := diffEntropy_le_of_covariance hK hg hent m hint hcov
  set n := Fintype.card ι
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hdiag : ∀ i, 0 < K i i := fun i => hK.diag_pos
  have hdet := hK.det_pos
  have hc : 0 < 2 * π * exp 1 := by positivity
  have havg : 0 < (∑ i, K i i) / n :=
    div_pos (Finset.sum_pos (fun i _ => hdiag i) Finset.univ_nonempty) hn
  -- `log |K| ≤ ∑ᵢ log Kᵢᵢ ≤ n log ((1/n) ∑ᵢ Kᵢᵢ)`, by Hadamard and the concavity of `log`.
  have h2 : log K.det ≤ ∑ i, log (K i i) := by
    rw [← log_prod (fun i _ => (hdiag i).ne')]
    exact log_le_log hdet (det_le_prod_diag hK)
  have h3 : ∑ i, log (K i i) ≤ n * log ((∑ i, K i i) / n) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Finset.univ)
      (w := fun _ => 1 / (n : ℝ)) (p := fun i => K i i) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp; rfl)
      (fun i _ => hdiag i)
    simp only [smul_eq_mul] at h
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      show 1 / (n : ℝ) * ∑ i, K i i = (∑ i, K i i) / n by ring] at h
    have h' := mul_le_mul_of_nonneg_left h hn.le
    rwa [← mul_assoc, mul_one_div_cancel hn.ne', one_mul] at h'
  calc diffEntropy volume g ≤ 1 / 2 * log ((2 * π * exp 1) ^ n * K.det) := h1
    _ = 1 / 2 * (n * log (2 * π * exp 1) + log K.det) := by
        rw [log_mul (by positivity) hdet.ne', log_pow]
    _ ≤ 1 / 2 * (n * log (2 * π * exp 1) + n * log ((∑ i, K i i) / n)) := by linarith
    _ = n / 2 * log (2 * π * exp 1 * ((∑ i, K i i) / n)) := by
        rw [log_mul hc.ne' havg.ne']
        ring

end InfoTheory
