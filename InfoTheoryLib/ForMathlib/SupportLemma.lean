/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.FenchelEggleston
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# A finite support lemma

A convex combination of vectors of a space of dimension `d` is a convex combination of at most
`d + 1` of them, by Carathéodory's theorem. This is the form of the support lemma used to bound the
cardinality of auxiliary random variables in network information theory.

## Main statements

* `exists_fin_mean_eq`: the mean of `v` under `w` is its mean under `w'` on `Fin (d + 1)`.
* `exists_fin_mixture_eq_integral`, `exists_fin_mixture_eq_sum`: **the support lemma** with
  Fenchel–Eggleston: on a connected compact set, the means of `d` continuous functions are preserved
  by a mixture of `d` points. This is the lemma of Appendix C of El Gamal and Kim.
-/

open Finset MeasureTheory

@[expose] public section

/-- **The support lemma, by Carathéodory's theorem.** The mean of `v : ι → E` under the weights `w`
is a mean of `d + 1` of its values, with `d = dim E`. -/
theorem exists_fin_mean_eq {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {w : ι → ℝ} (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) (v : ι → E) :
    ∃ (g : Fin (Module.finrank ℝ E + 1) → ι) (w' : Fin (Module.finrank ℝ E + 1) → ℝ),
      (∀ j, 0 ≤ w' j) ∧ ∑ j, w' j = 1 ∧ ∑ j, w' j • v (g j) = ∑ i, w i • v i := by
  classical
  have hmem : ∑ i, w i • v i ∈ convexHull ℝ (Set.range v) :=
    (convex_convexHull ℝ _).sum_mem (fun i _ => h0 i) h1
      fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i)
  obtain ⟨ι', _, z, w₀, hz, hind, hw0, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  have hcard : Fintype.card ι' ≤ Fintype.card (Fin (Module.finrank ℝ E + 1)) := by
    rw [Fintype.card_fin]
    refine (AffineIndependent.card_le_finrank_succ hind).trans (Nat.succ_le_succ ?_)
    exact Submodule.finrank_le _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  choose g₀ hg₀ using fun i' => hz (Set.mem_range_self i')
  have hne : Nonempty ι' := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  obtain ⟨i₀⟩ := hne
  refine ⟨Function.extend e g₀ fun _ => g₀ i₀, Function.extend e w₀ 0, fun j => ?_, ?_, ?_⟩
  · by_cases hj : ∃ i', e i' = j
    · obtain ⟨i', rfl⟩ := hj
      rw [e.injective.extend_apply]
      exact (hw0 i').le
    · rw [Function.extend_apply' _ _ _ hj]
      simp
  · rw [← hw1]
    refine (Fintype.sum_of_injective e e.injective w₀ _ (fun j hj => ?_) fun i' => ?_).symm
    · rw [Function.extend_apply' _ _ _ (by simpa using hj)]
      simp
    · rw [e.injective.extend_apply]
  · rw [← hsum]
    refine (Fintype.sum_of_injective e e.injective _ _ (fun j hj => ?_) fun i' => ?_).symm
    · rw [Function.extend_apply' _ _ _ (by simpa using hj)]
      simp
    · rw [e.injective.extend_apply, e.injective.extend_apply, hg₀]

section Connected

variable {T J : Type*} [TopologicalSpace T] [Fintype J] [Nonempty J] {S : Set T} {g : J → T → ℝ}

/-- A point of the convex hull of the values of `d` continuous functions on a connected compact set
is a mixture of `d` of the values. -/
theorem exists_fin_mixture_of_mem_convexHull (hS : IsConnected S)
    (hg : ∀ j, ContinuousOn (g j) S) {x : J → ℝ}
    (hx : x ∈ convexHull ℝ ((fun t j => g j t) '' S)) :
    ∃ (w : Fin (Fintype.card J) → ℝ) (z : Fin (Fintype.card J) → T), (∀ i, z i ∈ S) ∧
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∀ j, ∑ i, w i * g j (z i) = x j := by
  have hG : ContinuousOn (fun t j => g j t) S := continuousOn_pi.2 hg
  have hd : 0 < Module.finrank ℝ (J → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_pos
  obtain ⟨k, hk, w, y, hy, hw0, hw1, hsum⟩ :=
    exists_convex_combination_le_finrank (hS.image _ hG).isPreconnected hd hx
  rw [Module.finrank_fintype_fun_eq_card] at hk
  choose t htS ht using hy
  obtain ⟨t₀, ht₀⟩ := hS.nonempty
  set e : Fin k ↪ Fin (Fintype.card J) := Fin.castLEEmb hk with he
  refine ⟨Function.extend e w 0, Function.extend e t fun _ => t₀, fun i => ?_, fun i => ?_, ?_,
    fun j => ?_⟩
  · by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [e.injective.extend_apply]
      exact htS a
    · rwa [Function.extend_apply' _ _ _ hi]
  · by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [e.injective.extend_apply]
      exact hw0 a
    · rw [Function.extend_apply' _ _ _ hi]
      simp
  · rw [← hw1]
    refine (Fintype.sum_of_injective e e.injective w _ (fun i hi => ?_) fun a => ?_).symm
    · rw [Function.extend_apply' _ _ _ (by simpa using hi)]
      simp
    · rw [e.injective.extend_apply]
  · have h := congrFun hsum j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine (Fintype.sum_of_injective e e.injective _ _ (fun i hi => ?_) fun a => ?_).symm
    · rw [Function.extend_apply' _ _ _ (by simpa using hi)]
      simp
    · rw [e.injective.extend_apply, e.injective.extend_apply, ← ht a]

/-- **The support lemma, for a finite mixture.** The means of `d` continuous functions on a
connected set under a finite mixture are their means under a mixture of `d` points. -/
theorem exists_fin_mixture_eq_sum {ι : Type*} [Fintype ι] (hS : IsConnected S)
    (hg : ∀ j, ContinuousOn (g j) S) {a : ι → ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    {r : ι → T} (hr : ∀ i, r i ∈ S) :
    ∃ (w : Fin (Fintype.card J) → ℝ) (z : Fin (Fintype.card J) → T), (∀ i, z i ∈ S) ∧
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∀ j, ∑ i, w i * g j (z i) = ∑ i, a i * g j (r i) := by
  have hx : (fun j => ∑ i, a i * g j (r i)) ∈ convexHull ℝ ((fun t j => g j t) '' S) := by
    have h := (convex_convexHull ℝ ((fun t j => g j t) '' S)).sum_mem (t := Finset.univ) (w := a)
      (z := fun i j => g j (r i)) (fun i _ => ha0 i) ha1
      fun i _ => subset_convexHull ℝ _ ⟨r i, hr i, rfl⟩
    convert h using 1
    funext j
    simp [Finset.sum_apply]
  exact exists_fin_mixture_of_mem_convexHull hS hg hx

/-- **The support lemma of Appendix C of El Gamal and Kim.** Let `U ∼ ν` be a random variable on an
arbitrary set, with a parameter `r(U)` in a connected compact set, such as a conditional pmf
`p(x | u)`. The means of `d` continuous functions of the parameter are their means under a mixture
of `d` values of the parameter. -/
theorem exists_fin_mixture_eq_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (hc : IsCompact S) (hS : IsConnected S)
    (hg : ∀ j, ContinuousOn (g j) S) {r : Ω → T} (hr : ∀ ω, r ω ∈ S)
    (hm : ∀ j, AEStronglyMeasurable (fun ω => g j (r ω)) ν) :
    ∃ (w : Fin (Fintype.card J) → ℝ) (z : Fin (Fintype.card J) → T), (∀ i, z i ∈ S) ∧
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∀ j, ∑ i, w i * g j (z i) = ∫ ω, g j (r ω) ∂ν := by
  have hG : ContinuousOn (fun t j => g j t) S := continuousOn_pi.2 hg
  have hR : IsCompact ((fun t j => g j t) '' S) := hc.image_of_continuousOn hG
  have hI : ∀ j, Integrable (fun ω => g j (r ω)) ν := fun j => by
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hg j)
    exact Integrable.of_bound (hm j) C (Filter.Eventually.of_forall fun ω => hC _ (hr ω))
  have hmem := (convex_convexHull ℝ ((fun t j => g j t) '' S)).integral_mem
    (isCompact_convexHull_of_isCompact hR).isClosed
    (Filter.Eventually.of_forall fun ω => subset_convexHull ℝ _ ⟨r ω, hr ω, rfl⟩)
    (integrable_pi_iff.2 hI)
  obtain ⟨w, z, hz, hw0, hw1, h⟩ := exists_fin_mixture_of_mem_convexHull hS hg hmem
  refine ⟨w, z, hz, hw0, hw1, fun j => ?_⟩
  rw [h, eval_integral hI]

end Connected
