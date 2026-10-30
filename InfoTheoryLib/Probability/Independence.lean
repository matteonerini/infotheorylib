/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Conditional

/-!
# Independence and conditional independence

## Main definitions

* `IndepRV μ X Y`: `X` and `Y` are independent, `p(x, y) = p(x) p(y)`.
* `CondIndep μ X Y Z`: `X` and `Y` are conditionally independent given `Z`,
  `p(x, y | z) = p(x | z) p(y | z)`.
* `condProdDist μ X Y Z`: the pmf `p(z) p(x | z) p(y | z)` on `γ × α × β`.

## Main statements

* `indepRV_iff_dist_eq`: independence as an equality of pmfs.
* `condIndep_iff_dist_eq`: `CondIndep μ X Y Z` iff the law of `(Z, X, Y)` is
  `condProdDist μ X Y Z`.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Independence of two random variables: `p(x, y) = p(x) p(y)`. -/
def IndepRV (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) : Prop :=
  ∀ x y, dist μ (pair X Y) (x, y) = dist μ X x * dist μ Y y

omit [Fintype α] [Fintype β] in
lemma IndepRV.symm {μ : Ω → ℝ} {X : Ω → α} {Y : Ω → β} (h : IndepRV μ X Y) : IndepRV μ Y X :=
  fun y x => by rw [dist_pair_swap, h, mul_comm]

omit [Fintype α] [Fintype β] in
lemma indepRV_iff_dist_eq (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) :
    IndepRV μ X Y ↔ dist μ (pair X Y) = prodDist (dist μ X) (dist μ Y) := by
  constructor
  · intro h; funext z; exact h z.1 z.2
  · intro h x y; exact congrFun h (x, y)

/-- Conditional independence of `X` and `Y` given `Z` (2.118): `p(x, y|z) = p(x|z) p(y|z)`. -/
def CondIndep (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : Prop :=
  ∀ x y z, condDist μ (pair X Y) Z z (x, y) = condDist μ X Z z x * condDist μ Y Z z y

/-- The pmf `p(z) p(x|z) p(y|z)` on `γ × α × β`. -/
def condProdDist (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : γ × α × β → ℝ :=
  fun t => dist μ (pair Z X) (t.1, t.2.1) * dist μ (pair Z Y) (t.1, t.2.2) / dist μ Z t.1

lemma condProdDist_isPMF {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    IsPMF (condProdDist μ X Y Z) := by
  refine ⟨fun t => div_nonneg (mul_nonneg (dist_nonneg hμ _ _) (dist_nonneg hμ _ _))
    (dist_nonneg hμ _ _), ?_⟩
  simp only [condProdDist, Fintype.sum_prod_type]
  rw [← (hμ.dist Z).sum_eq_one]
  refine sum_congr rfl fun z _ => ?_
  simp_rw [← sum_div, ← mul_sum, ← sum_mul, sum_dist_pair_right]
  rcases eq_or_ne (dist μ Z z) 0 with h | h
  · simp [h]
  · field_simp

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma dist_triple_le_left {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (z : γ) (x : α) (y : β) :
    dist μ (pair Z (pair X Y)) (z, x, y) ≤ dist μ (pair Z X) (z, x) :=
  dist_le_dist_comp hμ (pair Z (pair X Y)) (fun t => (t.1, t.2.1)) (z, x, y)

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma dist_triple_le_right {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (z : γ) (x : α) (y : β) :
    dist μ (pair Z (pair X Y)) (z, x, y) ≤ dist μ (pair Z Y) (z, y) :=
  dist_le_dist_comp hμ (pair Z (pair X Y)) (fun t => (t.1, t.2.2)) (z, x, y)

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma absCont_condProdDist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    AbsCont (dist μ (pair Z (pair X Y))) (condProdDist μ X Y Z) := by
  rintro ⟨z, x, y⟩ h
  simp only [condProdDist, div_eq_zero_iff, mul_eq_zero] at h
  refine le_antisymm ?_ (dist_nonneg hμ _ _)
  rcases h with (h | h) | h
  · exact h ▸ dist_triple_le_left hμ X Y Z z x y
  · exact h ▸ dist_triple_le_right hμ X Y Z z x y
  · exact h ▸ (dist_pair_le_left hμ Z (pair X Y) z (x, y))

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma condIndep_iff_dist_eq {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    CondIndep μ X Y Z ↔ dist μ (pair Z (pair X Y)) = condProdDist μ X Y Z := by
  constructor
  · intro h
    funext ⟨z, x, y⟩
    have := h x y z
    simp only [condDist, condProdDist] at this ⊢
    rcases eq_or_ne (dist μ Z z) 0 with hz | hz
    · rw [hz, div_zero]
      exact dist_pair_eq_zero_of_left hμ Z (pair X Y) hz (x, y)
    · field_simp at this ⊢
      linarith
  · intro h x y z
    have := congrFun h (z, x, y)
    simp only [condDist, condProdDist] at this ⊢
    rw [this]
    rcases eq_or_ne (dist μ Z z) 0 with hz | hz
    · simp [hz]
    · field_simp

end InfoTheory
