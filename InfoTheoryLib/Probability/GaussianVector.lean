/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.MMSE
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Gaussian random vectors

The properties of Gaussian random vectors in Appendix B of El Gamal and Kim, on top of Mathlib's
`HasGaussianLaw`. The conditional law of `X₂` given `X₁ = x` comes from the decomposition
`X₂ = K₂₁ K₁₁⁻¹ X₁ + R`, where the residual `R` is Gaussian, independent of `X₁`, and has covariance
matrix `K₂₂ - K₂₁ K₁₁⁻¹ K₁₂`.

## Main definitions

* `crossCov μ X Y`: the cross covariance matrix of two random vectors.
* `gaussGain μ X₁ X₂`: the matrix `K₂₁ K₁₁⁻¹`.
* `gaussResidual μ X₁ X₂`: the residual `R`.
* `shiftKernel L ν`: the kernel `x ↦ law of (L x + R)` for `R ∼ ν`.

## Main statements

* `hasGaussianLaw_iff_forall_linear`: a random vector is Gaussian if and only if each linear
  combination of its coordinates is Gaussian.
* `hasGaussianLaw_mulVec`, `integral_mulVec`, `covariance_mulVec`: **Property 2**.
* `hasGaussianLaw_marginal`: **Property 3**.
* `hasGaussianLaw_residual`, `indepFun_residual`, `integral_residual`, `covariance_residual`: the
  decomposition.
* `condDistrib_gaussian`, `integral_shiftKernel`, `covariance_shiftKernel`: **Property 4**.
* `condExp_gaussian`: the MMSE estimate is linear for jointly Gaussian random variables.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Appendix B
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory Matrix

namespace InfoTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι κ : Type*}

/-! ### The definition by linear combinations -/

/-- **The definition of Appendix B.** A random vector is Gaussian if and only if every linear
combination of its coordinates is a Gaussian random variable. -/
theorem hasGaussianLaw_iff_forall_linear [Fintype ι] [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) :
    HasGaussianLaw (fun ω i => X i ω) μ ↔
      ∀ a : ι → ℝ, HasGaussianLaw (fun ω => ∑ i, a i * X i ω) μ := by
  classical
  have hV : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_iff.2 hXm
  constructor
  · intro h a
    have := h.map_fun (∑ i, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)
    simpa using this
  · intro h
    refine ⟨hV, ⟨fun L => ?_⟩⟩
    have hL : ∀ x : ι → ℝ, L x = ∑ i, L (Pi.single i 1) * x i := by
      intro x
      have h1 : x = ∑ i, x i • (Pi.single i 1 : ι → ℝ) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      nth_rw 1 [h1]
      simp [map_sum, map_smul, mul_comm]
    have hmap : HasGaussianLaw (L ∘ fun ω i => X i ω) μ := by
      have h1 := h fun i => L (Pi.single i 1)
      have h2 : (L ∘ fun ω i => X i ω) = fun ω => ∑ i, L (Pi.single i 1) * X i ω := by
        funext ω
        exact hL _
      rw [h2]
      exact h1
    have h3 := hmap.map_eq_gaussianReal
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hV, h3,
      integral_map hV L.continuous.aestronglyMeasurable,
      variance_map L.continuous.aemeasurable hV]
    rfl

/-! ### Linear transformations -/

section Linear

/-- A matrix as a continuous linear map. -/
def mulVecCLM [Fintype ι] [Fintype κ] (A : Matrix κ ι ℝ) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

lemma mulVecCLM_apply [Fintype ι] [Fintype κ] (A : Matrix κ ι ℝ) (x : ι → ℝ) : mulVecCLM A x =
  A *ᵥ x := rfl

variable {X : ι → Ω → ℝ}

/-- **Property 2 of Gaussian random vectors.** A linear transformation of a Gaussian random vector
is Gaussian. -/
theorem hasGaussianLaw_mulVec [Fintype ι] [Finite κ] (hX : HasGaussianLaw (fun ω i => X i ω) μ)
    (A : Matrix κ ι ℝ) : HasGaussianLaw (fun ω => A *ᵥ fun i => X i ω) μ := by
  have := Fintype.ofFinite κ
  exact hX.map_fun (mulVecCLM A)

lemma memLp_coord [Finite ι] (hX : HasGaussianLaw (fun ω i => X i ω) μ) (i : ι) :
    MemLp (X i) 2 μ := by
  have := Fintype.ofFinite ι
  exact (hX.eval i).memLp_two

/-- **Property 2.** The mean of `A X` is `A μ`. -/
theorem integral_mulVec [Fintype ι] (hX : HasGaussianLaw (fun ω i => X i ω) μ) (A : Matrix κ ι ℝ)
  (k : κ) :
    ∫ ω, (A *ᵥ fun i => X i ω) k ∂μ = (A *ᵥ fun i => ∫ ω, X i ω ∂μ) k := by
  have := hX.isProbabilityMeasure
  simp only [Matrix.mulVec, dotProduct]
  rw [integral_finsetSum _ fun i _ => ((memLp_coord hX i).integrable one_le_two).const_mul _]
  simp only [integral_const_mul]

/-- **Property 2.** The covariance matrix of `A X` is `A K Aᵀ`. -/
theorem covariance_mulVec [Fintype ι] (hX : HasGaussianLaw (fun ω i => X i ω) μ) (A : Matrix κ ι ℝ)
  (k l : κ) :
    cov[fun ω => (A *ᵥ fun i => X i ω) k, fun ω => (A *ᵥ fun i => X i ω) l; μ] =
      (A * covMatrix μ X * Aᵀ) k l := by
  have := hX.isProbabilityMeasure
  simp only [Matrix.mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (fun i => (memLp_coord hX i).const_mul _)
    fun i => (memLp_coord hX i).const_mul _]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, covMatrix, Matrix.of_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- **Property 3 of Gaussian random vectors.** Each subvector of a Gaussian random vector is
Gaussian. -/
theorem hasGaussianLaw_marginal [Finite ι] [Finite κ] (hX : HasGaussianLaw (fun ω i => X i ω) μ)
    (s : κ → ι) : HasGaussianLaw (fun ω k => X (s k) ω) μ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  have h := hX.map_fun (ContinuousLinearMap.pi fun k : κ =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) (s k))
  simpa using h

end Linear

/-! ### The residual -/

section Residual

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] {X₁ : ι₁ → Ω → ℝ} {X₂ : ι₂ → Ω → ℝ}

/-- The cross covariance matrix of two random vectors. -/
def crossCov (μ : Measure Ω) (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ) : Matrix ι κ ℝ :=
  Matrix.of fun i j => cov[X i, Y j; μ]

/-- The matrix `K₂₁ K₁₁⁻¹`. -/
def gaussGain (μ : Measure Ω) (X₁ : ι₁ → Ω → ℝ) (X₂ : ι₂ → Ω → ℝ) : Matrix ι₂ ι₁ ℝ :=
  crossCov μ X₂ X₁ * (covMatrix μ X₁)⁻¹

/-- The residual `X₂ - K₂₁ K₁₁⁻¹ X₁`. -/
def gaussResidual (μ : Measure Ω) (X₁ : ι₁ → Ω → ℝ) (X₂ : ι₂ → Ω → ℝ) (j : ι₂) : Ω → ℝ :=
  linErr (X₂ j) X₁ (gaussGain μ X₁ X₂ j)

variable [Finite ι₂] (hX : HasGaussianLaw (fun ω => (fun i => X₁ i ω, fun j => X₂ j ω)) μ)

include hX

omit [Fintype ι₁] [DecidableEq ι₁] in
lemma memLp₁ [Finite ι₁] (i : ι₁) : MemLp (X₁ i) 2 μ := by
  have := Fintype.ofFinite ι₂
  have := Fintype.ofFinite ι₁
  exact memLp_coord hX.fst i

omit [Fintype ι₁] [DecidableEq ι₁] in
lemma memLp₂ [Finite ι₁] (j : ι₂) : MemLp (X₂ j) 2 μ := by
  have := Fintype.ofFinite ι₂
  have := Fintype.ofFinite ι₁
  exact memLp_coord hX.snd j

/-- The joint law of `X₁` and the residual is Gaussian. -/
theorem hasGaussianLaw_residual :
    HasGaussianLaw (fun ω => (fun i => X₁ i ω, fun j => gaussResidual μ X₁ X₂ j ω)) μ := by
  have := Fintype.ofFinite ι₂
  set G := gaussGain μ X₁ X₂ with hG
  set Φ : ((ι₁ → ℝ) × (ι₂ → ℝ)) →L[ℝ] ((ι₁ → ℝ) × (ι₂ → ℝ)) :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      (ContinuousLinearMap.snd ℝ _ _ - (mulVecCLM G).comp (ContinuousLinearMap.fst ℝ _ _)) with hΦ
  have h := hX.map_fun Φ
  convert h using 2 with ω
  simp only [hΦ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
    mulVecCLM_apply]
  ext j
  · simp
  · simp [gaussResidual, linErr, hG, Matrix.mulVec, dotProduct]

/-- The residual is uncorrelated with `X₁`. -/
lemma covariance_residual_fst (hK : IsUnit (covMatrix μ X₁).det) (j : ι₂) (i : ι₁) :
    cov[gaussResidual μ X₁ X₂ j, X₁ i; μ] = 0 := by
  have := Fintype.ofFinite ι₂
  have := hX.isProbabilityMeasure
  have h := cov_linErr (μ := μ) (memLp₂ hX j) (memLp₁ hX) (gaussGain μ X₁ X₂ j) (memLp₁ hX i)
  unfold gaussResidual
  rw [h]
  have h2 : gaussGain μ X₁ X₂ * covMatrix μ X₁ = crossCov μ X₂ X₁ := by
    rw [gaussGain, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hK, Matrix.mul_one]
  have h3 := congrFun (congrFun h2 j) i
  simp only [Matrix.mul_apply, covMatrix, crossCov, Matrix.of_apply] at h3
  rw [sub_eq_zero, ← h3]

/-- **The residual is independent of `X₁`**, since the two are jointly Gaussian and uncorrelated. -/
theorem indepFun_residual (hK : IsUnit (covMatrix μ X₁).det) :
    IndepFun (fun ω i => X₁ i ω) (fun ω j => gaussResidual μ X₁ X₂ j ω) μ := by
  have := Fintype.ofFinite ι₂
  refine (hasGaussianLaw_residual hX).indepFun_of_covariance_eval fun i j => ?_
  rw [covariance_comm]
  exact covariance_residual_fst hX hK j i

/-- The residual has mean `μ₂ - K₂₁ K₁₁⁻¹ μ₁`. -/
theorem integral_residual (j : ι₂) :
    ∫ ω, gaussResidual μ X₁ X₂ j ω ∂μ =
      ∫ ω, X₂ j ω ∂μ - ∑ i, gaussGain μ X₁ X₂ j i * ∫ ω, X₁ i ω ∂μ := by
  have := Fintype.ofFinite ι₂
  have := hX.isProbabilityMeasure
  simp only [gaussResidual, linErr]
  rw [integral_sub ((memLp₂ hX j).integrable one_le_two)
    (integrable_finsetSum _ fun i _ => ((memLp₁ hX i).integrable one_le_two).const_mul _),
    integral_finsetSum _ fun i _ => ((memLp₁ hX i).integrable one_le_two).const_mul _]
  simp only [integral_const_mul]

/-- **The residual has covariance matrix `K₂₂ - K₂₁ K₁₁⁻¹ K₁₂`.** -/
theorem covariance_residual (hK : IsUnit (covMatrix μ X₁).det) (j k : ι₂) :
    cov[gaussResidual μ X₁ X₂ j, gaussResidual μ X₁ X₂ k; μ] =
      (covMatrix μ X₂ - crossCov μ X₂ X₁ * (covMatrix μ X₁)⁻¹ * crossCov μ X₁ X₂) j k := by
  have := Fintype.ofFinite ι₂
  have := hX.isProbabilityMeasure
  have hRj : MemLp (gaussResidual μ X₁ X₂ j) 2 μ := memLp_linErr (memLp₂ hX j) (memLp₁ hX) _
  have h1 : cov[gaussResidual μ X₁ X₂ j, gaussResidual μ X₁ X₂ k; μ] =
      cov[gaussResidual μ X₁ X₂ j, X₂ k; μ] := by
    rw [covariance_comm]
    have e : gaussResidual μ X₁ X₂ k = linErr (X₂ k) X₁ (gaussGain μ X₁ X₂ k) := rfl
    rw [e, cov_linErr (μ := μ) (memLp₂ hX k) (memLp₁ hX) (gaussGain μ X₁ X₂ k) hRj]
    have h2 : ∑ i, gaussGain μ X₁ X₂ k i * cov[X₁ i, gaussResidual μ X₁ X₂ j; μ] = 0 :=
      sum_eq_zero fun i _ => by
        rw [covariance_comm, covariance_residual_fst hX hK j i, mul_zero]
    rw [h2, sub_zero, covariance_comm]
  rw [h1]
  have e : gaussResidual μ X₁ X₂ j = linErr (X₂ j) X₁ (gaussGain μ X₁ X₂ j) := rfl
  rw [e, cov_linErr (μ := μ) (memLp₂ hX j) (memLp₁ hX) (gaussGain μ X₁ X₂ j) (memLp₂ hX k)]
  simp only [Matrix.sub_apply, Matrix.mul_apply, covMatrix, crossCov, Matrix.of_apply, gaussGain]

end Residual

/-! ### The conditional law -/

section Conditional

variable {ι₁ ι₂ : Type*} [Fintype ι₁] {X₁ : ι₁ → Ω → ℝ} {X₂ : ι₂ → Ω → ℝ}

/-- The cross covariance under a pushforward. -/
lemma covariance_map_of_measurable {E : Type*} [MeasurableSpace E] {T : Ω → E} (hT : Measurable T)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g) :
    cov[f, g; μ.map T] = cov[f ∘ T, g ∘ T; μ] := by
  have e1 : ∫ y, f y ∂(μ.map T) = ∫ ω, f (T ω) ∂μ :=
    integral_map hT.aemeasurable hf.aestronglyMeasurable
  have e2 : ∫ y, g y ∂(μ.map T) = ∫ ω, g (T ω) ∂μ :=
    integral_map hT.aemeasurable hg.aestronglyMeasurable
  simp only [covariance, Function.comp_apply]
  rw [e1, e2]
  exact integral_map hT.aemeasurable
    ((hf.sub_const _).mul (hg.sub_const _)).aestronglyMeasurable

/-- A matrix acts measurably. -/
lemma measurable_mulVec_add (L : Matrix ι₂ ι₁ ℝ) :
    Measurable fun z : (ι₁ → ℝ) × (ι₂ → ℝ) => L *ᵥ z.1 + z.2 := by
  refine measurable_pi_iff.2 fun j => ?_
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  exact (Finset.measurable_fun_sum _ fun i _ => (((measurable_pi_apply i).comp
    measurable_fst).const_mul _)).add ((measurable_pi_apply j).comp measurable_snd)

/-- The kernel `x ↦ law of (L x + R)`, for `R ∼ ν`. -/
def shiftKernel (L : Matrix ι₂ ι₁ ℝ) (ν : Measure (ι₂ → ℝ)) [SFinite ν] :
    ProbabilityTheory.Kernel (ι₁ → ℝ) (ι₂ → ℝ) where
  toFun x := ν.map fun r => L *ᵥ x + r
  measurable' := by
    have hT := measurable_mulVec_add L
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have h1 : (fun x => (ν.map fun r => L *ᵥ x + r) s) =
        fun x => ν (Prod.mk x ⁻¹' ((fun z : (ι₁ → ℝ) × (ι₂ → ℝ) => L *ᵥ z.1 + z.2) ⁻¹' s)) := by
      funext x
      have hx : Measurable fun r : ι₂ → ℝ => L *ᵥ x + r := measurable_const.add measurable_id
      rw [Measure.map_apply hx hs]
      rfl
    rw [h1]
    exact measurable_measure_prodMk_left (hT hs)

lemma shiftKernel_apply (L : Matrix ι₂ ι₁ ℝ) (ν : Measure (ι₂ → ℝ)) [SFinite ν] (x : ι₁ → ℝ) :
    shiftKernel L ν x = ν.map fun r => L *ᵥ x + r := rfl

instance (L : Matrix ι₂ ι₁ ℝ) (ν : Measure (ι₂ → ℝ)) [IsProbabilityMeasure ν] :
    IsMarkovKernel (shiftKernel L ν) :=
  ⟨fun _ => (Measure.isProbabilityMeasure_map_iff
    (measurable_const.add measurable_id).aemeasurable).2 inferInstance⟩

/-- The residual is measurable. -/
lemma measurable_residual [DecidableEq ι₁] (h₁ : ∀ i, Measurable (X₁ i))
  (h₂ : ∀ j, Measurable (X₂ j)) :
    Measurable fun ω j => gaussResidual μ X₁ X₂ j ω := by
  refine measurable_pi_iff.2 fun j => ?_
  exact (h₂ j).sub (Finset.measurable_fun_sum _ fun i _ => (h₁ i).const_mul _)

/-- `X₂ = K₂₁ K₁₁⁻¹ X₁ + R`. -/
lemma eq_mulVec_add_residual [DecidableEq ι₁] (ω : Ω) :
    (fun j => X₂ j ω) = gaussGain μ X₁ X₂ *ᵥ (fun i => X₁ i ω) +
      fun j => gaussResidual μ X₁ X₂ j ω := by
  funext j
  simp [gaussResidual, linErr, Matrix.mulVec, dotProduct]

variable [DecidableEq ι₁] [Finite ι₂] [IsProbabilityMeasure μ]
  (hX : HasGaussianLaw (fun ω => (fun i => X₁ i ω, fun j => X₂ j ω)) μ)
  (hK : IsUnit (covMatrix μ X₁).det) (h₁ : ∀ i, Measurable (X₁ i)) (h₂ : ∀ j, Measurable (X₂ j))

include hX hK h₁ h₂

/-- The joint law of `(X₁, X₂)`, as the law of `X₁` and the shift kernel. -/
theorem map_pair_eq_compProd :
    μ.map (fun ω => (fun i => X₁ i ω, fun j => X₂ j ω)) =
      (μ.map fun ω i => X₁ i ω) ⊗ₘ
        shiftKernel (gaussGain μ X₁ X₂) (μ.map fun ω j => gaussResidual μ X₁ X₂ j ω) := by
  set V₁ : Ω → ι₁ → ℝ := fun ω i => X₁ i ω with hV₁
  set R : Ω → ι₂ → ℝ := fun ω j => gaussResidual μ X₁ X₂ j ω with hR
  set L := gaussGain μ X₁ X₂ with hL
  have hV₁m : Measurable V₁ := measurable_pi_iff.2 h₁
  have hRm : Measurable R := measurable_residual h₁ h₂
  have hind := indepFun_residual hX hK
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hV₁m.aemeasurable hRm.aemeasurable).1 hind
  set G : (ι₁ → ℝ) × (ι₂ → ℝ) → (ι₁ → ℝ) × (ι₂ → ℝ) := fun z => (z.1, L *ᵥ z.1 + z.2) with hG
  have hGm : Measurable G := measurable_fst.prodMk (measurable_mulVec_add L)
  have hcomp : (fun ω => (V₁ ω, fun j => X₂ j ω)) = G ∘ fun ω => (V₁ ω, R ω) := by
    funext ω
    simp only [hG, Function.comp_apply, Prod.mk.injEq, true_and]
    exact eq_mulVec_add_residual ω
  ext s hs
  rw [hcomp, ← Measure.map_map hGm (hV₁m.prodMk hRm), hprod, Measure.map_apply hGm hs,
    Measure.prod_apply (hGm hs), Measure.compProd_apply hs]
  refine lintegral_congr fun x => ?_
  have hx : Measurable fun r : ι₂ → ℝ => L *ᵥ x + r := measurable_const.add measurable_id
  rw [shiftKernel_apply, Measure.map_apply hx (measurable_prodMk_left hs)]
  rfl

/-- **Property 4 of Gaussian random vectors.** Given `X₁ = x`, the vector `X₂` has the law of
`K₂₁ K₁₁⁻¹ x + R`. -/
theorem condDistrib_gaussian :
    condDistrib (fun ω j => X₂ j ω) (fun ω i => X₁ i ω) μ =ᵐ[μ.map fun ω i => X₁ i ω]
      shiftKernel (gaussGain μ X₁ X₂) (μ.map fun ω j => gaussResidual μ X₁ X₂ j ω) :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (measurable_pi_iff.2 h₁)
    (measurable_pi_iff.2 h₂) (map_pair_eq_compProd hX hK h₁ h₂)

omit hK h₁ h₂ in
/-- **Property 4.** The conditional law is Gaussian. -/
theorem isGaussian_shiftKernel (x : ι₁ → ℝ) :
    IsGaussian (shiftKernel (gaussGain μ X₁ X₂) (μ.map fun ω j => gaussResidual μ X₁ X₂ j ω) x) :=
      by
  have := Fintype.ofFinite ι₂
  have h := (hasGaussianLaw_residual hX).snd.isGaussian_map
  rw [shiftKernel_apply]
  infer_instance

omit hK in
/-- **Property 4.** The conditional mean is `K₂₁ K₁₁⁻¹ (x - μ₁) + μ₂`. -/
theorem integral_shiftKernel (x : ι₁ → ℝ) (j : ι₂) :
    ∫ y, y j ∂(shiftKernel (gaussGain μ X₁ X₂) (μ.map fun ω j => gaussResidual μ X₁ X₂ j ω) x) =
      (gaussGain μ X₁ X₂ *ᵥ fun i => x i - ∫ ω, X₁ i ω ∂μ) j + ∫ ω, X₂ j ω ∂μ := by
  have hRm : Measurable fun ω j => gaussResidual μ X₁ X₂ j ω := measurable_residual h₁ h₂
  have hx : Measurable fun r : ι₂ → ℝ => gaussGain μ X₁ X₂ *ᵥ x + r :=
    measurable_const.add measurable_id
  have hj : Measurable fun y : ι₂ → ℝ => y j := measurable_pi_apply j
  have e1 : ∫ y, y j ∂((μ.map fun ω j => gaussResidual μ X₁ X₂ j ω).map
      fun r => gaussGain μ X₁ X₂ *ᵥ x + r) =
      ∫ r, (gaussGain μ X₁ X₂ *ᵥ x + r) j ∂(μ.map fun ω j => gaussResidual μ X₁ X₂ j ω) :=
    integral_map hx.aemeasurable hj.aestronglyMeasurable
  have e2 : ∫ r, (gaussGain μ X₁ X₂ *ᵥ x + r) j ∂(μ.map fun ω j => gaussResidual μ X₁ X₂ j ω) =
      ∫ ω, (gaussGain μ X₁ X₂ *ᵥ x + fun j => gaussResidual μ X₁ X₂ j ω) j ∂μ :=
    integral_map hRm.aemeasurable (hj.comp hx).aestronglyMeasurable
  rw [shiftKernel_apply, e1, e2]
  simp only [Pi.add_apply]
  have hint : Integrable (gaussResidual μ X₁ X₂ j) μ :=
    (memLp_linErr (memLp₂ hX j) (memLp₁ hX) _).integrable one_le_two
  rw [integral_add (integrable_const _) hint]
  rw [integral_const]
  have h3 := integral_residual hX j
  simp only [probReal_univ, one_smul]
  rw [h3]
  simp only [Matrix.mulVec, dotProduct, mul_sub, sum_sub_distrib]
  ring

/-- **Property 4.** The conditional covariance matrix is `K₂₂ - K₂₁ K₁₁⁻¹ K₁₂`. -/
theorem covariance_shiftKernel (x : ι₁ → ℝ) (j k : ι₂) :
    cov[fun y => y j, fun y => y k;
      shiftKernel (gaussGain μ X₁ X₂) (μ.map fun ω j => gaussResidual μ X₁ X₂ j ω) x] =
      (covMatrix μ X₂ - crossCov μ X₂ X₁ * (covMatrix μ X₁)⁻¹ * crossCov μ X₁ X₂) j k := by
  have hRm : Measurable fun ω j => gaussResidual μ X₁ X₂ j ω := measurable_residual h₁ h₂
  set c := gaussGain μ X₁ X₂ *ᵥ x with hc
  have hx : Measurable fun r : ι₂ → ℝ => c + r := measurable_const.add measurable_id
  rw [← covariance_residual hX hK j k, shiftKernel_apply]
  have hmap : (μ.map fun ω j => gaussResidual μ X₁ X₂ j ω).map (fun r => c + r) =
      μ.map fun ω => c + fun j => gaussResidual μ X₁ X₂ j ω :=
    Measure.map_map hx hRm
  rw [hmap]
  have hm : Measurable fun ω => c + fun j => gaussResidual μ X₁ X₂ j ω :=
    measurable_const.add hRm
  have hint : ∀ l, Integrable (gaussResidual μ X₁ X₂ l) μ := fun l =>
    (memLp_linErr (memLp₂ hX l) (memLp₁ hX) _).integrable one_le_two
  have hmeas : ∀ l, Measurable fun y : ι₂ → ℝ => y l := measurable_pi_apply
  rw [covariance_map_of_measurable hm (hmeas j) (hmeas k)]
  have e1 : ∀ l, ((fun y : ι₂ → ℝ => y l) ∘ fun ω => c + fun j => gaussResidual μ X₁ X₂ j ω) =
      fun ω => c l + gaussResidual μ X₁ X₂ l ω := fun l => rfl
  rw [e1, e1, covariance_const_add_left (hint j), covariance_const_add_right (hint k)]

/-- **The remark of Appendix B.** For jointly Gaussian random variables the MMSE estimate is linear:
`E(X₂ | X₁) = K₂₁ K₁₁⁻¹ (X₁ - μ₁) + μ₂`. By `indepFun_residual`, the error is independent of the
observation. -/
theorem condExp_gaussian (j : ι₂) :
    μ[X₂ j | MeasurableSpace.comap (fun ω i => X₁ i ω) inferInstance] =ᵐ[μ] fun ω =>
      (gaussGain μ X₁ X₂ *ᵥ fun i => X₁ i ω - ∫ ω, X₁ i ω ∂μ) j + ∫ ω, X₂ j ω ∂μ := by
  set V₁ : Ω → ι₁ → ℝ := fun ω i => X₁ i ω with hV₁
  have hV₁m : Measurable V₁ := measurable_pi_iff.2 h₁
  have hle : MeasurableSpace.comap V₁ inferInstance ≤ mΩ := hV₁m.comap_le
  set R := gaussResidual μ X₁ X₂ j with hR
  have hRi : Integrable R μ := (memLp_linErr (memLp₂ hX j) (memLp₁ hX) _).integrable one_le_two
  have hRm : Measurable R := (measurable_pi_iff.1 (measurable_residual (μ := μ) h₁ h₂)) j
  set A : Ω → ℝ := fun ω => (gaussGain μ X₁ X₂ *ᵥ V₁ ω) j with hA
  have hAm : StronglyMeasurable[MeasurableSpace.comap V₁ inferInstance] A := by
    have hc : Continuous fun v : ι₁ → ℝ => (gaussGain μ X₁ X₂ *ᵥ v) j := by
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    exact (hc.measurable.comp (comap_measurable V₁)).stronglyMeasurable
  have hAi : Integrable A μ := by
    simp only [hA, Matrix.mulVec, dotProduct]
    exact integrable_finsetSum _ fun i _ => ((memLp₁ hX i).integrable one_le_two).const_mul _
  have hsplit : X₂ j = A + R := by
    funext ω
    simpa [hA, hR] using congrFun (eq_mulVec_add_residual (μ := μ) (X₁ := X₁) (X₂ := X₂) ω) j
  have hind : Indep (MeasurableSpace.comap R inferInstance)
      (MeasurableSpace.comap V₁ inferInstance) μ := by
    have h3 := (indepFun_residual hX hK).symm
    have h4 := h3.comp (measurable_pi_apply j) measurable_id
    exact (IndepFun_iff_Indep _ _ _).1 h4
  have hRc : μ[R | MeasurableSpace.comap V₁ inferInstance] =ᵐ[μ] fun _ => ∫ ω, R ω ∂μ :=
    condExp_indep_eq hRm.comap_le hle (comap_measurable R).stronglyMeasurable hind
  have hcond : μ[X₂ j | MeasurableSpace.comap V₁ inferInstance] =
      μ[A + R | MeasurableSpace.comap V₁ inferInstance] := by
    rw [← hsplit]
  rw [hcond]
  have h5 := condExp_add hAi hRi (MeasurableSpace.comap V₁ inferInstance)
  have h6 : μ[A | MeasurableSpace.comap V₁ inferInstance] = A :=
    condExp_of_stronglyMeasurable hle hAm hAi
  refine h5.trans ?_
  rw [h6]
  filter_upwards [hRc] with ω hω
  simp only [Pi.add_apply]
  rw [hω, hR, integral_residual hX j]
  simp only [hA, hV₁, Matrix.mulVec, dotProduct, mul_sub, sum_sub_distrib]
  ring

end Conditional

end InfoTheory
