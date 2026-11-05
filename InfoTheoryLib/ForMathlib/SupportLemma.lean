/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# A finite support lemma

A convex combination of vectors of a space of dimension `d` is a convex combination of at most
`d + 1` of them, by Carathéodory's theorem. This is the form of the support lemma used to bound the
cardinality of auxiliary random variables in network information theory.

## Main statements

* `exists_fin_mean_eq`: the mean of `v` under `w` is its mean under `w'` on `Fin (d + 1)`.
-/

open Finset

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
