/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.ConvexHessian
public import InfoTheoryLib.ForMathlib.FenchelEggleston
public import InfoTheoryLib.ForMathlib.MatrixSVD
public import InfoTheoryLib.ForMathlib.SupportingHyperplane

/-!
# El Gamal & Kim, Appendix A: Convex Sets and Functions

This file indexes the formalization of Appendix A of [elgamal2010]. The notes state these results
without proof, and cite [eggleston1958] and [rockafellar1970] for some of them. We prove all of
them. Mathlib has Carathéodory's theorem with `d + 1` points, but not the Fenchel–Eggleston theorem,
and not the two lemmas on supporting hyperplanes.

## Conventions

* **Spaces.** We work in a finite-dimensional real normed space `E`, instead of `ℝ^d`. A vector `a`
  of the notes is a continuous linear functional `f`, with `f x = aᵀ x`.
* **Boundary.** The boundary of a set is its `frontier` in `E`, not relative to the convex set `ℛ`
  of the lemmas. A boundary point need not lie in the set.
* **Supporting hyperplanes.** A supporting hyperplane at `x₀` is `{y | f y = f x₀}`. We keep the
  functional, in `IsSupportingAt`, since it also records the side of the set.
* **Hessian.** The Hessian of `g` at `x` is the bilinear form `fderiv ℝ (fderiv ℝ g) x`, and
  positive semidefinite means nonnegative on the diagonal `(v, v)`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Convex sets (page A-1)
* A convex set includes the finite convex combinations of its points: Mathlib's `Convex.sum_mem`.
* The convex hull as the set of convex combinations: Mathlib's `convexHull_eq`.
* The convex hull as the smallest convex set: Mathlib's `convexHull_min`.
* The convex closure as the smallest closed convex set: here `closure_convexHull_eq_sInter`.

### The Fenchel–Eggleston–Carathéodory theorem (page A-2; `ForMathlib.FenchelEggleston`)
* `exists_finset_of_mem_convexHull`, for a connected set, here `fenchel_eggleston_caratheodory`.
* `exists_finset_of_mem_closure_convexHull`, for the closure of the convex hull of a connected
  compact set, as in the notes.
* `exists_convex_combination_le_finrank`, as a convex combination of an indexed family.
* In finite dimension, the convex hull of a compact set is compact:
  `isCompact_convexHull_of_isCompact`.

### Supporting hyperplanes (page A-2; `ForMathlib.SupportingHyperplane`)
* `IsSupportingAt`, `HasUniqueSupport`, `HasUniqueSupportingHyperplane`.
* The supporting hyperplane theorem: `exists_isSupportingAt`.
* A closed bounded convex set as an intersection of half spaces: `eq_sInter_halfSpaces`.
* **Lemma A.1:** `eq_of_forall_isSupportingAt`, here `lemma_A_1`.
* **Lemma A.2:** `eq_of_hasUniqueSupport`, with half spaces, here `lemma_A_2`, and
  `eq_of_hasUniqueSupportingHyperplane`, with hyperplanes.
* Lemma A.2 with hyperplanes fails for a point on the line: here `printed_lemma_A_2_false`.

### Convex functions (page A-3; `ForMathlib.ConvexHessian`)
* The epigraph: Mathlib's `convexOn_iff_convex_epigraph`.
* The second-order criterion: `convexOn_iff_hessian_nonneg`.
* Entropy: `concaveOn_sum_negMulLog`.
* Log determinant: `concaveOn_log_det` (`ForMathlib.MatrixSVD`).
* Maximum: `convexOn_iSup`.

## Differences from the notes

* **Fenchel–Eggleston.** The connected set need not be compact when the point is in the convex hull
  itself. Compactness is only used to show that the convex hull is closed. We assume `d ≥ 1`.
* **Lemmas A.1 and A.2.** Some hypotheses turn out not to be needed, and we drop them: the convexity
  of `ℛ` in both lemmas, the convexity of `ℛ₂` in Lemma A.1, and boundedness in Lemma A.2. We assume
  that `ℛ₁` is nonempty in Lemma A.2, and that `E` is nontrivial in both.
* **Lemma A.2.** The form with unique half spaces has no further assumption. The form with unique
  hyperplanes assumes that `ℛ₁` has nonempty interior.
* **Maximum.** The supremum of real functions has to be finite, so we assume that it is bounded
  above at each point, and that the family is nonempty.
* **Second-order criterion.** We state it on an open convex set, which covers the domains of the
  examples, and not only on the whole space.

## Not formalized

Nothing in the appendix is left out. The theorem is applied, through the support lemma, to the
cardinality bounds of Appendix C and of `RateDistortion.SideInfo` and `Network.GrayWynerConverse`.
It is not applied to all the bounds of the notes: Theorem 3 of Lecture 4 is on the "Not formalized"
list of that lecture.

## Issues in the notes

* **Page A-2, Lemma A.2.** With the definition of a supporting hyperplane on the same page, which is
  a set of points, the lemma is false for a point on the line. Take `ℛ₁ = {0}` and `ℛ₂ = [0, 1]` in
  `ℝ`: the only supporting hyperplane of `ℛ₁` at `0` is `{0}`, and `0` is on the boundary of `ℛ₂`,
  but `ℛ₁ ≠ ℛ₂`: `printed_lemma_A_2_false`. It also fails for `ℛ₁ = ∅`, with `𝒜 = ∅`. Supporting
  half spaces avoid the first problem, as `{0}` then has two supports, and only the empty set
  remains to exclude.
* **Page A-2, half spaces.** The empty set has to be excluded from "any closed bounded
  convex set", as an empty intersection of half spaces is the whole space.
* **Page A-2.** `ℛ ∈ ℝ^d` should be `ℛ ⊆ ℝ^d`; the supporting hyperplane is printed
  `{y : aᵀ(x - x₀) = 0}` and should use `y`; "interesection" is a typo. The theorem needs `d ≥ 1`.
* **Page A-3.** The epigraph is "convex for all `a`", but `a` is a coordinate of the epigraph and is
  not a parameter. Also, a function is called convex without naming its convex domain, which matters
  for the examples: the Hessian criterion needs an open convex domain, and entropy is concave on the
  nonnegative orthant only.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  A
* [H. G. Eggleston, *Convexity*][eggleston1958]
* [R. T. Rockafellar, *Convex Analysis*][rockafellar1970]
-/

open Set Module

@[expose] public noncomputable section

namespace InfoTheory

namespace ElGamalKim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Page A-1 of [elgamal2010].** The convex closure of a set, which is the closure of its convex
hull, is the smallest closed convex set containing it. -/
theorem closure_convexHull_eq_sInter (R : Set E) :
    closure (convexHull ℝ R) = ⋂₀ {C | Convex ℝ C ∧ IsClosed C ∧ R ⊆ C} := by
  refine Subset.antisymm (subset_sInter fun C ⟨h1, h2, h3⟩ => ?_) (sInter_subset_of_mem
    ⟨(convex_convexHull ℝ R).closure, isClosed_closure,
      (subset_convexHull ℝ R).trans subset_closure⟩)
  exact closure_minimal (convexHull_min h3 h1) h2

variable [FiniteDimensional ℝ E]

/-- **The Fenchel–Eggleston–Carathéodory theorem of Appendix A of [elgamal2010].** Any point in the
convex closure of a connected compact set in dimension `d ≥ 1` is a convex combination of at most
`d` points of the set. -/
theorem fenchel_eggleston_caratheodory {R : Set E} (hRc : IsCompact R) (hR : IsConnected R)
    (hd : 0 < finrank ℝ E) {x : E} (hx : x ∈ closure (convexHull ℝ R)) :
    ∃ k ≤ finrank ℝ E, ∃ (w : Fin k → ℝ) (z : Fin k → E), (∀ i, z i ∈ R) ∧ (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [(isCompact_convexHull_of_isCompact hRc).isClosed.closure_eq] at hx
  exact exists_convex_combination_le_finrank hR.isPreconnected hd hx

/-- **Lemma A.1 of Appendix A of [elgamal2010].** -/
theorem lemma_A_1 [Nontrivial E] {R R₁ R₂ : Set E} (hR₁ : Convex ℝ R₁)
    (hb₁ : Bornology.IsBounded R₁) (hb₂ : Bornology.IsBounded R₂) (hsub : R₁ ⊆ R₂) (hR₂ : R₂ ⊆ R)
    (hrel : closure R₁ ∩ R ⊆ R₁)
    (h : ∀ f x₀, IsSupportingAt R₂ f x₀ → ∃ y ∈ R₁, f y = f x₀) : R₁ = R₂ :=
  eq_of_forall_isSupportingAt hR₁ hb₁ hb₂ hsub hR₂ hrel h

/-- **Lemma A.2 of Appendix A of [elgamal2010]**, with unique supporting half spaces, for a nonempty
smaller set. -/
theorem lemma_A_2 {R R₁ R₂ A : Set E} (hR₁ : Convex ℝ R₁) (hR₂c : Convex ℝ R₂)
    (hne : R₁.Nonempty) (hsub : R₁ ⊆ R₂) (hR₂ : R₂ ⊆ R) (hrel : closure R₁ ∩ R ⊆ R₁)
    (hA : A ⊆ frontier R₁) (hcov : frontier R₁ ⊆ convexHull ℝ A)
    (huniq : ∀ x₀ ∈ A, HasUniqueSupport R₁ x₀) (hbd : ∀ x₀ ∈ A, x₀ ∈ frontier R₂) : R₁ = R₂ :=
  eq_of_hasUniqueSupport hR₁ hR₂c hne hsub hR₂ hrel hA hcov huniq hbd

/-- A nonzero functional on `ℝ` vanishes only at `0`. -/
lemma eq_zero_of_dual_real {f : StrongDual ℝ ℝ} (hf : f ≠ 0) {y : ℝ} (hy : f y = 0) : y = 0 := by
  by_contra hne
  apply hf
  ext
  have h : f y = y * f 1 := by
    have := f.map_smul y 1
    simpa using this
  rw [hy] at h
  simpa using (mul_eq_zero.1 h.symm).resolve_left hne

/-- **Lemma A.2 of Appendix A of [elgamal2010] as printed fails.** Take `R₁ = {0}` and `R₂ = [0, 1]`
in `ℝ`, with `A = {0}`. The two sets are bounded and convex, and closed in `R = [0, 1]`. The convex
hull of `A` contains the boundary of `R₁`. The point `0` has a unique supporting hyperplane of `R₁`,
the set `{0}`, and lies on the boundary of `R₂`. But `R₁ ≠ R₂`. -/
theorem printed_lemma_A_2_false :
    ∃ R R₁ R₂ A : Set ℝ, Convex ℝ R ∧ Convex ℝ R₁ ∧ Convex ℝ R₂ ∧ Bornology.IsBounded R₁ ∧
      Bornology.IsBounded R₂ ∧ R₁ ⊆ R₂ ∧ R₂ ⊆ R ∧ closure R₁ ∩ R ⊆ R₁ ∧ closure R₂ ∩ R ⊆ R₂ ∧
      A ⊆ frontier R₁ ∧ frontier R₁ ⊆ convexHull ℝ A ∧
      (∀ x₀ ∈ A, HasUniqueSupportingHyperplane R₁ x₀) ∧ (∀ x₀ ∈ A, x₀ ∈ frontier R₂) ∧ R₁ ≠ R₂ := by
  have hfr : frontier ({0} : Set ℝ) = {0} := by
    simp [frontier]
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  refine ⟨Icc 0 1, {0}, Icc 0 1, {0}, convex_Icc _ _, convex_singleton _, convex_Icc _ _,
    Bornology.isBounded_singleton, Metric.isBounded_Icc _ _, by simp, Subset.rfl, ?_, ?_, ?_, ?_,
      ?_,
    ?_, ?_⟩
  · simp
  · simp [closure_Icc]
  · rw [hfr]
  · rw [hfr]
    exact subset_convexHull ℝ _
  · rintro x₀ rfl f g hf hg
    ext y
    simp only [Set.mem_ofPred_eq, map_zero]
    constructor
    · intro h
      rw [eq_zero_of_dual_real hf.2.1 h, map_zero]
    · intro h
      rw [eq_zero_of_dual_real hg.2.1 h, map_zero]
  · rintro x₀ rfl
    rw [frontier_Icc h01]
    simp
  · intro h
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    rw [← h] at h1
    simp at h1

end ElGamalKim

end InfoTheory
