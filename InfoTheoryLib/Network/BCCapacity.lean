/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCBounds
public import InfoTheoryLib.Network.BCClasses
public import InfoTheoryLib.Network.BCDegraded
public import InfoTheoryLib.Network.BCSuperposition
public import InfoTheoryLib.Network.BinarySymmetricBC

/-!
# The capacity region of the degraded broadcast channel

This file puts together the superposition coding inner bound and the converse for degraded
channels. The capacity region of a degraded DM-BC is the closure of the region
`R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` (Theorem 2 of Lecture 5 of El Gamal and Kim), which for the
binary symmetric BC is the region `R₁ ≤ H(a ∗ p₁) - H(p₁)`, `R₂ ≤ 1 - H(a ∗ p₂)`.

## Main definitions

* `superpositionClosedRegionBits W`: the superposition coding region with non-strict inequalities.

## Main statements

* `closure_superpositionRegionBits_subset`, `superpositionClosedRegionBits_subset`: **Theorem 1 of
  [elgamal2010], Lecture 5**, as an inclusion in the capacity region.
* `closure_convexHull_union_superpositionRegionBits_subset`: the convex closure of the two
  superposition coding inner bounds, with the roles of the receivers exchanged, is an inner bound.
* `IsLessNoisy.degradedBCRegionBits_subset`: for a less noisy channel the sum-rate bound is
  inactive, so that the region `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` is achievable.
* `bcCapacityRegionBits_eq_closure_degradedBCRegionBits`: **Theorem 2 of [elgamal2010], Lecture 5**.
* `bcCapacityRegionBits_bsbc`: **the Proposition of [elgamal2010], Lecture 5**, the capacity region
  of the binary symmetric BC.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology Set

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

/-! ### The superposition coding inner bound -/

/-- **Theorem 1 of [elgamal2010], Lecture 5.** The closure of the superposition coding inner bound
is in the capacity region. -/
theorem closure_superpositionRegionBits_subset (hW : IsChannel W) :
    closure (superpositionRegionBits W) ⊆ bcCapacityRegionBits W :=
  closure_mono (superpositionRegionBits_subset hW)

/-- **Lecture 5 of [elgamal2010], page 5-18.** The closure of the superposition coding inner bound
with the roles of the receivers exchanged is in the capacity region. -/
theorem closure_superpositionRegionBits₂_subset (hW : IsChannel W) :
    closure (superpositionRegionBits₂ W) ⊆ bcCapacityRegionBits W :=
  closure_mono (superpositionRegionBits₂_subset hW)

/-- **Lecture 5 of [elgamal2010], page 5-18.** The convex closure of the union of the two
superposition coding inner bounds is an inner bound on the capacity region. -/
theorem closure_convexHull_union_superpositionRegionBits_subset [Nonempty α] (hW : IsChannel W) :
    closure (convexHull ℝ (superpositionRegionBits W ∪ superpositionRegionBits₂ W)) ⊆
      bcCapacityRegionBits W := by
  refine closure_minimal (convexHull_min (union_subset ?_ ?_) (convex_bcCapacityRegionBits hW))
    isClosed_closure
  · exact (superpositionRegionBits_subset hW).trans subset_closure
  · exact (superpositionRegionBits₂_subset hW).trans subset_closure

/-- **Theorem 1 of [elgamal2010], Lecture 5.** The superposition coding region with non-strict
inequalities: `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` and `R₁ + R₂ ≤ I(X; Y₁)` for some `p(u, x)`. It
is the form in which the notes state the capacity region of the more capable DM-BC. -/
def superpositionClosedRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧ R.1 ≤ bcInfoXY₁U q W / log 2 ∧
    R.2 ≤ bcInfoUY₂ q W / log 2 ∧ R.1 + R.2 ≤ bcInfoXY₁ q W / log 2}

/-- The superposition coding region with non-strict inequalities is in the closure of the one with
strict inequalities: its points are the limits of the points `R - (t, t)`, `t → 0⁺`. -/
theorem superpositionClosedRegionBits_subset_closure (W : α → β₁ × β₂ → ℝ) :
    superpositionClosedRegionBits W ⊆ closure (superpositionRegionBits W) := by
  rintro ⟨R₁, R₂⟩ ⟨k, q, hq, hR₁, hR₂, hR₁₂⟩
  simp only at hR₁ hR₂ hR₁₂
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => (R₁ - 1 / ((n : ℝ) + 1), R₂ - 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n : ℕ => R₁ - 1 / ((n : ℝ) + 1)) atTop (𝓝 (R₁ - 0)) :=
      tendsto_const_nhds.sub ht
    have h2 : Tendsto (fun n : ℕ => R₂ - 1 / ((n : ℝ) + 1)) atTop (𝓝 (R₂ - 0)) :=
      tendsto_const_nhds.sub ht
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  refine ⟨k, q, hq, ?_, ?_, ?_⟩
  · simp only; linarith
  · simp only; linarith
  · simp only; linarith

/-- **Theorem 1 of [elgamal2010], Lecture 5.** The superposition coding region with non-strict
inequalities is in the capacity region. -/
theorem superpositionClosedRegionBits_subset (hW : IsChannel W) :
    superpositionClosedRegionBits W ⊆ bcCapacityRegionBits W :=
  (superpositionClosedRegionBits_subset_closure W).trans
    (closure_superpositionRegionBits_subset hW)

/-- **Lecture 5 of [elgamal2010], page 5-38.** For a less noisy DM-BC the sum-rate bound of
superposition coding is inactive: `I(U; Y₂) + I(X; Y₁ | U) ≤ I(U; Y₁) + I(X; Y₁ | U) = I(X; Y₁)`.
So the region `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` is achievable. -/
theorem IsLessNoisy.degradedBCRegionBits_subset (hW : IsChannel W) (h : IsLessNoisy W) :
    degradedBCRegionBits W ⊆ bcCapacityRegionBits W := by
  refine Subset.trans ?_ (superpositionClosedRegionBits_subset hW)
  rintro R ⟨k, q, hq, hR₁, hR₂⟩
  refine ⟨k, q, hq, hR₁, hR₂, ?_⟩
  have hL := log_pos one_lt_two
  have hsum : bcInfoUY₂ q W + bcInfoXY₁U q W ≤ bcInfoXY₁ q W := by
    rw [bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U hq hW]
    linarith [h k q hq]
  have := div_le_div_of_nonneg_right hsum hL.le
  rw [add_div] at this
  linarith

/-! ### Theorem 2 -/

/-- **Theorem 2 of [elgamal2010], Lecture 5.** The private-message capacity region of a
(stochastically) degraded DM-BC is the closure of the set of rate pairs with `R₁ ≤ I(X; Y₁ | U)` and
`R₂ ≤ I(U; Y₂)` for some `p(u, x)`. -/
theorem bcCapacityRegionBits_eq_closure_degradedBCRegionBits (hW : IsChannel W)
    (hd : IsStochasticallyDegraded W) :
    bcCapacityRegionBits W = closure (degradedBCRegionBits W) := by
  refine Subset.antisymm (closure_minimal (fun R hR => ?_) isClosed_closure) ?_
  · exact IsAchievableBCBits.mem_closure_degradedBCRegionBits_of_stochasticallyDegraded hW hd hR
  · exact closure_minimal ((degradedBCRegionBits_subset_closure hW hd).trans
      (closure_superpositionRegionBits_subset hW)) isClosed_closure

/-! ### The binary symmetric broadcast channel -/

variable {p₁ p₂ : ℝ}

/-- **The Proposition of [elgamal2010], Lecture 5, page 5-27.** The capacity region of the binary
symmetric BC with crossover probabilities `p₁ ≤ p₂ ≤ 1/2` is the set of rate pairs with
`R₁ ≤ H(a ∗ p₁) - H(p₁)` and `R₂ ≤ 1 - H(a ∗ p₂)` for some `a ∈ [0, 1/2]`. -/
theorem bcCapacityRegionBits_bsbc {W : Bool → Bool × Bool → ℝ} (hW : IsChannel W)
    (h₁ : bcMarg₁ W = bsbcBSC p₁) (h₂ : bcMarg₂ W = bsbcBSC p₂) (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂)
    (hp₂ : p₂ ≤ 1 / 2) : bcCapacityRegionBits W = bsbcSuperpositionRegion p₁ p₂ := by
  rw [bcCapacityRegionBits_eq_closure_degradedBCRegionBits hW
      (isStochasticallyDegraded_of_bsbc h₁ h₂ hp₁₂ hp₂),
    degradedBCRegionBits_eq_bsbcSuperpositionRegion hW h₁ h₂ hp₁ hp₁₂ hp₂,
    (isClosed_bsbcSuperpositionRegion p₁ p₂).closure_eq]

end InfoTheory
