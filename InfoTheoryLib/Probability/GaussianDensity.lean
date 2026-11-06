/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian
public import InfoTheoryLib.Probability.GaussianVector

/-!
# The density of a Gaussian random vector

This file connects the two descriptions of a Gaussian random vector that the library uses: the
density `mvGaussianPDF` of Cover and Thomas, and Mathlib's `HasGaussianLaw`, which says that every
linear combination of the coordinates is Gaussian. A Gaussian random vector with a positive
definite covariance matrix `K` and mean `m` has the density `mvGaussianPDF m K`, as on page B-11 of
El Gamal and Kim.

## Main definitions

* `mvGaussianLaw m K`: the measure with density `mvGaussianPDF m K`.

## Main statements

* `isGaussian_mvGaussianLaw`, `integral_mvGaussianLaw`, `covariance_mvGaussianLaw`: the measure
  `mvGaussianLaw m K` is Gaussian with mean `m` and covariance matrix `K`.
* `map_eq_of_mean_of_cov`: a Gaussian law is determined by its mean and its covariance matrix.
* `map_eq_mvGaussianLaw`: a Gaussian random vector with a positive definite covariance matrix has
  the law `mvGaussianLaw`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  B
-/

open MeasureTheory ProbabilityTheory Matrix Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℝ}

/-- The law `N(m, K)`, as the measure with density `mvGaussianPDF m K`. -/
def mvGaussianLaw (m : ι → ℝ) (K : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  volume.withDensity fun x => ENNReal.ofReal (mvGaussianPDF m K x)

omit [DecidableEq ι] in
/-- A product of one-dimensional normal measures has the product density. -/
lemma pi_gaussianReal_eq {v : ι → NNReal} (hv : ∀ i, v i ≠ 0) :
    Measure.pi (fun i => gaussianReal 0 (v i)) =
      volume.withDensity fun y : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (y i)) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox]
  have hfac : ∀ i, Integrable ((s i).indicator (gaussianPDFReal 0 (v i))) := fun i =>
    (integrable_gaussianPDFReal 0 (v i)).indicator (hs i)
  have hnn : ∀ (i : ι) t, 0 ≤ (s i).indicator (gaussianPDFReal 0 (v i)) t := fun i t =>
    Set.indicator_nonneg (fun t _ => gaussianPDFReal_nonneg 0 (v i) t) t
  have e : (Set.pi Set.univ s).indicator
      (fun y : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (y i))) =
      fun y => ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 (v i)) (y i)) := by
    funext y
    by_cases hy : y ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hy]
      congr 1
      exact prod_congr rfl fun i _ => (Set.indicator_of_mem (hy i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hy]
      obtain ⟨i, hi⟩ : ∃ i, y i ∉ s i := by simpa [Set.mem_pi] using hy
      rw [prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _), ENNReal.ofReal_zero]
  have hI : Integrable fun y : ι → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 (v i)) (y i) :=
    Integrable.fintype_prod hfac
  rw [e, ← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun y => prod_nonneg fun i _ => hnn i (y i)),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg
      fun i _ => integral_nonneg (hnn i)]
  refine prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 (hv i), integral_indicator (hs i)]

/-- `N(m, K)` is the law of `m + U Z`, for independent normal coordinates of `Z` with the
eigenvalues of `K` as variances. -/
lemma map_eigEquiv_pi (hK : K.PosDef) (m : ι → ℝ) :
    (Measure.pi fun i => gaussianReal 0 (PosDef.eigvalNN hK i)).map (PosDef.eigEquiv hK m) =
      mvGaussianLaw m K := by
  rw [pi_gaussianReal_eq (PosDef.eigvalNN_ne_zero hK)]
  ext A hA
  have h := (PosDef.measurePreserving_eigEquiv hK m).setLIntegral_comp_preimage_emb
    (PosDef.eigEquiv hK m).measurableEmbedding (fun x => ENNReal.ofReal (mvGaussianPDF m K x)) A
  rw [(PosDef.eigEquiv hK m).map_apply, withDensity_apply _ ((PosDef.eigEquiv hK m).measurable hA),
    mvGaussianLaw, withDensity_apply _ hA, ← h]
  refine lintegral_congr fun y => ?_
  simp only [PosDef.eigEquiv_apply]
  rw [mvGaussianPDF_eigU hK]

section Product

variable {v : ι → NNReal}

omit [DecidableEq ι] in
/-- The coordinates of a product of normal measures have a Gaussian law. -/
lemma hasGaussianLaw_pi :
    HasGaussianLaw (fun y : ι → ℝ => fun i => y i) (Measure.pi fun i => gaussianReal 0 (v i)) := by
  refine iIndepFun.hasGaussianLaw (X := fun i (y : ι → ℝ) => y i) (fun i => ?_) ?_
  · refine ⟨measurable_pi_apply i |>.aemeasurable, ?_⟩
    rw [(measurePreserving_eval _ i).map_eq]
    infer_instance
  · exact iIndepFun_pi (X := fun _ t => t) fun _ => aemeasurable_id

omit [DecidableEq ι] in
lemma integral_pi_coord (i : ι) :
    ∫ y : ι → ℝ, y i ∂(Measure.pi fun i => gaussianReal 0 (v i)) = 0 := by
  have h := integral_map (μ := Measure.pi fun i => gaussianReal 0 (v i))
    (measurable_pi_apply i).aemeasurable (f := fun t : ℝ => t) aestronglyMeasurable_id
  rw [(measurePreserving_eval _ i).map_eq] at h
  rw [← h]
  simp

/-- The covariance matrix of a product of normal measures is diagonal. -/
lemma covMatrix_pi :
    covMatrix (Measure.pi fun i => gaussianReal 0 (v i)) (fun i (y : ι → ℝ) => y i) =
      diagonal fun i => (v i : ℝ) := by
  ext i j
  simp only [covMatrix, of_apply, diagonal_apply]
  split_ifs with hij
  · subst hij
    rw [covariance_self (measurable_pi_apply i).aemeasurable]
    have h := variance_id_gaussianReal (μ := 0) (v := v i)
    rw [← (measurePreserving_eval (fun i => gaussianReal 0 (v i)) i).map_eq] at h
    rwa [variance_map aemeasurable_id (measurable_pi_apply i).aemeasurable] at h
  · have h := (iIndepFun_pi (μ := fun i => gaussianReal 0 (v i)) (X := fun _ t => t)
      fun _ => aemeasurable_id).indepFun hij
    exact h.covariance_eq_zero ((memLp_coord hasGaussianLaw_pi i)) (memLp_coord hasGaussianLaw_pi j)

end Product

/-- `m + U Z` has a Gaussian law. -/
lemma hasGaussianLaw_eigEquiv (hK : K.PosDef) (m : ι → ℝ) :
    HasGaussianLaw (fun y i => PosDef.eigEquiv hK m y i)
      (Measure.pi fun i => gaussianReal 0 (PosDef.eigvalNN hK i)) := by
  have h := hasGaussianLaw_mulVec (hasGaussianLaw_pi (v := PosDef.eigvalNN hK)) (PosDef.eigU hK)
  have hG := h.isGaussian_map
  refine ⟨(PosDef.eigEquiv hK m).measurable.aemeasurable, ?_⟩
  have hU : Measurable fun y : ι → ℝ => PosDef.eigU hK *ᵥ fun i => y i :=
    (mulVecCLM (PosDef.eigU hK)).continuous.measurable
  have e : (Measure.pi fun i => gaussianReal 0 (PosDef.eigvalNN hK i)).map
      (fun y i => PosDef.eigEquiv hK m y i) =
      ((Measure.pi fun i => gaussianReal 0 (PosDef.eigvalNN hK i)).map
        (fun y => PosDef.eigU hK *ᵥ fun i => y i)).map (fun x => m + x) := by
    rw [Measure.map_map (measurable_const_add m) hU]
    rfl
  rw [e]
  infer_instance

/-- **Page B-11 of [elgamal2010].** The measure with density `mvGaussianPDF m K` is Gaussian. -/
theorem isGaussian_mvGaussianLaw (hK : K.PosDef) (m : ι → ℝ) : IsGaussian (mvGaussianLaw m K) := by
  rw [← map_eigEquiv_pi hK m]
  exact (hasGaussianLaw_eigEquiv hK m).isGaussian_map

/-- The law `N(m, K)` as the law of `m + U Z`: the integral of a function. -/
lemma integral_mvGaussianLaw_comp (hK : K.PosDef) (m : ι → ℝ) (i : ι) :
    ∫ x, x i ∂mvGaussianLaw m K = m i := by
  have hL := hasGaussianLaw_pi (v := PosDef.eigvalNN hK)
  rw [← map_eigEquiv_pi hK m, integral_map (PosDef.eigEquiv hK m).measurable.aemeasurable
    (measurable_pi_apply i).aestronglyMeasurable]
  simp only [PosDef.eigEquiv_apply, Pi.add_apply]
  rw [integral_add (integrable_const _) ?_, integral_const, integral_mulVec hL]
  · simp only [integral_pi_coord, probReal_univ, smul_eq_mul, one_mul]
    change m i + (PosDef.eigU hK *ᵥ (0 : ι → ℝ)) i = m i
    simp
  · exact (memLp_coord (hasGaussianLaw_mulVec hL (PosDef.eigU hK)) i).integrable one_le_two

/-- **Page B-11 of [elgamal2010].** The mean of `N(m, K)` is `m`. -/
theorem integral_mvGaussianLaw (hK : K.PosDef) (m : ι → ℝ) (i : ι) :
    (mvGaussianLaw m K)[fun x => x i] = m i :=
  integral_mvGaussianLaw_comp hK m i

/-- **Page B-11 of [elgamal2010].** The covariance matrix of `N(m, K)` is `K`. -/
theorem covariance_mvGaussianLaw (hK : K.PosDef) (m : ι → ℝ) :
    covMatrix (mvGaussianLaw m K) (fun i x => x i) = K := by
  have hL := hasGaussianLaw_pi (v := PosDef.eigvalNN hK)
  ext i j
  change cov[fun x => x i, fun x => x j; mvGaussianLaw m K] = K i j
  rw [← map_eigEquiv_pi hK m, covariance_map_of_measurable (PosDef.eigEquiv hK m).measurable
    (measurable_pi_apply i) (measurable_pi_apply j)]
  have hU : ∀ k, Integrable (fun y : ι → ℝ => (PosDef.eigU hK *ᵥ y) k) _ := fun k =>
    (memLp_coord (hasGaussianLaw_mulVec hL (PosDef.eigU hK)) k).integrable one_le_two
  have h2 := covariance_mulVec hL (PosDef.eigU hK) i j
  rw [covMatrix_pi] at h2
  have h3 : K i j = (PosDef.eigU hK * diagonal (PosDef.eigval hK) * (PosDef.eigU hK)ᵀ) i j := by
    conv_lhs => rw [PosDef.eq_eigU hK]
  rw [h3, ← show _ = (PosDef.eigU hK * diagonal (PosDef.eigval hK) * (PosDef.eigU hK)ᵀ) i j from h2]
  change cov[fun y => m i + (PosDef.eigU hK *ᵥ y) i, fun y => m j + (PosDef.eigU hK *ᵥ y) j;
    Measure.pi fun i => gaussianReal 0 (PosDef.eigvalNN hK i)] = _
  rw [covariance_const_add_left (hU i), covariance_const_add_right (hU j)]

section Determined

/-- A linear functional on `ι → ℝ`, as a matrix with one row. -/
lemma dual_eq_mulVec (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ((Matrix.of fun (_ : Unit) i => L (Pi.single i 1)) *ᵥ x) () := by
  have h := LinearMap.pi_apply_eq_sum_univ L.toLinearMap x
  simp only [mulVec, dotProduct, of_apply]
  refine h.trans (sum_congr rfl fun i _ => ?_)
  have e : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [e, smul_eq_mul, ContinuousLinearMap.coe_coe]
  ring

variable {κ Ω Ω' : Type*} [Finite κ] {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {X : κ → Ω → ℝ} {Y : κ → Ω' → ℝ}

/-- **A Gaussian law is determined by its mean and its covariance matrix.** -/
theorem map_eq_of_mean_of_cov (hX : HasGaussianLaw (fun ω i => X i ω) μ)
    (hY : HasGaussianLaw (fun ω i => Y i ω) μ') (hm : ∀ i, μ[X i] = μ'[Y i])
    (hc : covMatrix μ X = covMatrix μ' Y) :
    μ.map (fun ω i => X i ω) = μ'.map (fun ω i => Y i ω) := by
  classical
  have := Fintype.ofFinite κ
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  have := hX.isGaussian_map
  have := hY.isGaussian_map
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [hX.charFunDual_map_eq_fun L, hY.charFunDual_map_eq_fun L]
  set A : Matrix Unit κ ℝ := Matrix.of fun (_ : Unit) i => L (Pi.single i 1) with hA
  have eX : (fun ω => L fun i => X i ω) = fun ω => (A *ᵥ fun i => X i ω) () :=
    funext fun ω => dual_eq_mulVec L _
  have eY : (fun ω => L fun i => Y i ω) = fun ω => (A *ᵥ fun i => Y i ω) () :=
    funext fun ω => dual_eq_mulVec L _
  have hmX : μ[fun ω => L fun i => X i ω] = μ'[fun ω => L fun i => Y i ω] := by
    rw [eX, eY, integral_mulVec hX A (), integral_mulVec hY A ()]
    congr 2
    exact funext hm
  have hvX : Var[fun ω => L fun i => X i ω; μ] = Var[fun ω => L fun i => Y i ω; μ'] := by
    rw [eX, eY, ← covariance_self ((hasGaussianLaw_mulVec hX A).eval ()).aemeasurable,
      ← covariance_self ((hasGaussianLaw_mulVec hY A).eval ()).aemeasurable,
      covariance_mulVec hX A, covariance_mulVec hY A, hc]
  rw [hmX, hvX]

end Determined

/-- **Page B-11 of [elgamal2010].** A Gaussian random vector with a positive definite covariance
matrix has the joint pdf `f(x) = ((2π)ⁿ |K|)^{-1/2} exp (-½ (x - m)ᵀ K⁻¹ (x - m))`. -/
theorem map_eq_mvGaussianLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω i => X i ω) μ) (hK : (covMatrix μ X).PosDef) :
    μ.map (fun ω i => X i ω) = mvGaussianLaw (fun i => μ[X i]) (covMatrix μ X) := by
  set m : ι → ℝ := fun i => μ[X i] with hm
  have hG := isGaussian_mvGaussianLaw hK m
  have hI : HasGaussianLaw (fun (x : ι → ℝ) i => x i) (mvGaussianLaw m (covMatrix μ X)) :=
    hG.hasGaussianLaw_id
  have h := map_eq_of_mean_of_cov hX hI (fun i => (integral_mvGaussianLaw hK m i).symm)
    (covariance_mvGaussianLaw hK m).symm
  rw [h]
  exact Measure.map_id

end InfoTheory
