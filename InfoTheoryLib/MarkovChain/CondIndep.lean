/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.MarkovChain.DataProcessing

/-!
# Criteria for conditional independence

## Main statements

* `condIndep_iff_mul`: `X ⊥ Z | Y` iff `p(x, y, z) p(y) = p(x, y) p(y, z)`.
* `condIndep_iff_condDist`: `X ⊥ Z | Y` iff `p(x, y, z) = p(x, y) p(z | y)` where `p(y) > 0`, and
  `p(x, y, z) = 0` elsewhere.
* `condIndep_iff_factorization`: `X ⊥ Z | Y` iff `p(x, y, z) = a(x, y) b(y, z)` where `p(y) > 0`.
* `condIndep_intersection`: the intersection axiom for strictly positive distributions.
* `condIndep_intersection_counterexample`: the intersection axiom fails without positivity.

## References

Numbers without a source refer to [yeung2008].

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 2.1
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω]

/-- Two random variables taking given values on the same outcomes have the same probability of
doing so. -/
lemma dist_congr_of_iff (μ : Ω → ℝ) {U : Ω → α} {V : Ω → β} {a : α} {b : β}
    (h : ∀ ω, U ω = a ↔ V ω = b) : dist μ U a = dist μ V b := by
  refine sum_congr rfl fun ω _ => ?_
  by_cases hU : U ω = a
  · simp [hU, (h ω).1 hU]
  · have hV : ¬V ω = b := fun hV => hU ((h ω).2 hV)
    simp [hU, hV]

/-- **(2.3)** `X ⊥ Z | Y` iff `p(x, y, z) p(y) = p(x, y) p(y, z)`. -/
theorem condIndep_iff_mul {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    CondIndep μ X Z Y ↔ ∀ x y z, dist μ (pair X (pair Y Z)) (x, y, z) * dist μ Y y =
      dist μ (pair X Y) (x, y) * dist μ (pair Y Z) (y, z) := by
  rw [← markovChain_iff_condIndep hμ, markovChain_iff_mul hμ]

open Classical in
/-- **(2.4)** `X ⊥ Z | Y` iff `p(x, y, z) = p(x, y) p(z | y)` when `p(y) > 0`, and
`p(x, y, z) = 0` otherwise. -/
theorem condIndep_iff_condDist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    CondIndep μ X Z Y ↔ ∀ x y z, dist μ (pair X (pair Y Z)) (x, y, z) =
      if 0 < dist μ Y y then dist μ (pair X Y) (x, y) * condDist μ Z Y y z else 0 := by
  rw [condIndep_iff_mul hμ]
  refine forall₃_congr fun x y z => ?_
  split_ifs with hy
  · rw [condDist, ← mul_div_assoc, eq_div_iff hy.ne']
  · have h0 : dist μ Y y = 0 := le_antisymm (not_lt.1 hy) (dist_nonneg hμ _ _)
    have h1 : dist μ (pair X (pair Y Z)) (x, y, z) = 0 :=
      le_antisymm (h0 ▸ dist_triple_le_mid hμ X Y Z x y z) (dist_nonneg hμ _ _)
    simp [h0, h1, dist_pair_eq_zero_of_right hμ X Y h0 x]

/-- **(2.5)** `X ⊥ Z | Y` iff `p(x, y, z) = a(x, y) b(y, z)` for all `x`, `y`, `z` with
`p(y) > 0`, for some functions `a` and `b`. -/
theorem condIndep_iff_factorization [Finite α] [Finite γ] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    CondIndep μ X Z Y ↔ ∃ (a : α → β → ℝ) (b : β → γ → ℝ), ∀ x y z, 0 < dist μ Y y →
      dist μ (pair X (pair Y Z)) (x, y, z) = a x y * b y z := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite γ
  rw [condIndep_iff_mul hμ]
  constructor
  · intro h
    refine ⟨fun x y => dist μ (pair X Y) (x, y), fun y z => dist μ (pair Y Z) (y, z) / dist μ Y y,
      fun x y z hy => ?_⟩
    simp only
    rw [← mul_div_assoc, eq_div_iff hy.ne', h]
  · rintro ⟨a, b, h⟩ x y z
    rcases (dist_nonneg hμ Y y).eq_or_lt with hy | hy
    · rw [← hy, dist_pair_eq_zero_of_right hμ X Y hy.symm x]
      ring
    · have h1 : ∀ x, dist μ (pair X Y) (x, y) = a x y * ∑ z, b y z := fun x => by
        rw [← sum_dist_pair_right μ (pair X Y) Z (x, y), mul_sum]
        refine sum_congr rfl fun z _ => ?_
        rw [← h x y z hy]
        exact dist_congr_of_iff μ fun ω => by simp [pair, and_assoc]
      have h2 : dist μ (pair Y Z) (y, z) = (∑ x, a x y) * b y z := by
        rw [← sum_dist_pair_left μ X (pair Y Z) (y, z), sum_mul]
        exact sum_congr rfl fun x _ => h x y z hy
      have h3 : dist μ Y y = (∑ x, a x y) * ∑ z, b y z := by
        rw [← sum_dist_pair_left μ X Y y, sum_mul]
        exact sum_congr rfl fun x _ => h1 x
      rw [h x y z hy, h1 x, h2, h3]
      ring

/-- **Proposition 2.12 (the intersection axiom).** If `p(x₁, x₂, x₃, x₄)` is strictly positive,
`X₁ ⊥ X₄ | (X₂, X₃)` and `X₁ ⊥ X₃ | (X₂, X₄)`, then `X₁ ⊥ (X₃, X₄) | X₂`. -/
theorem condIndep_intersection [Finite γ] {μ : Ω → ℝ} (hμ : IsPMF μ) {X₁ : Ω → α} {X₂ : Ω → β}
    {X₃ : Ω → γ} {X₄ : Ω → δ}
    (hpos : ∀ a b c d, 0 < dist μ (pair X₁ (pair X₂ (pair X₃ X₄))) (a, b, c, d))
    (h₁ : CondIndep μ X₁ X₄ (pair X₂ X₃)) (h₂ : CondIndep μ X₁ X₃ (pair X₂ X₄)) :
    CondIndep μ X₁ (pair X₃ X₄) X₂ := by
  have := Fintype.ofFinite γ
  rw [condIndep_iff_mul hμ] at h₁ h₂ ⊢
  intro a b t
  obtain ⟨c, d⟩ := t
  -- (2.23) and (2.24), for all values of `x₃`
  have e₁ : ∀ c, dist μ (pair X₁ (pair X₂ (pair X₃ X₄))) (a, b, c, d) * dist μ (pair X₂ X₃) (b, c) =
      dist μ (pair X₁ (pair X₂ X₃)) (a, b, c) * dist μ (pair X₂ (pair X₃ X₄)) (b, c, d) := by
    intro c
    have h := h₁ a (b, c) d
    rwa [dist_congr_of_iff (a := (a, (b, c), d)) (b := (a, b, c, d)) μ
        (V := pair X₁ (pair X₂ (pair X₃ X₄))) (fun ω => by simp [pair, and_assoc]),
      dist_congr_of_iff (a := ((b, c), d)) (b := (b, c, d)) μ
        (V := pair X₂ (pair X₃ X₄)) (fun ω => by simp [pair, and_assoc])] at h
  have e₂ : ∀ c, dist μ (pair X₁ (pair X₂ (pair X₃ X₄))) (a, b, c, d) * dist μ (pair X₂ X₄) (b, d) =
      dist μ (pair X₁ (pair X₂ X₄)) (a, b, d) * dist μ (pair X₂ (pair X₃ X₄)) (b, c, d) := by
    intro c
    have h := h₂ a (b, d) c
    rwa [dist_congr_of_iff (a := (a, (b, d), c)) (b := (a, b, c, d)) μ
        (V := pair X₁ (pair X₂ (pair X₃ X₄))) (fun ω => by simp only [pair, Prod.mk.injEq]; tauto),
      dist_congr_of_iff (a := ((b, d), c)) (b := (b, c, d)) μ
        (V := pair X₂ (pair X₃ X₄)) (fun ω => by simp only [pair, Prod.mk.injEq]; tauto),
      dist_congr_of_iff (a := (a, (b, d))) (b := (a, b, d)) μ
        (V := pair X₁ (pair X₂ X₄)) (fun ω => by simp [pair])] at h
  have hle : ∀ c, dist μ (pair X₁ (pair X₂ (pair X₃ X₄))) (a, b, c, d) ≤
      dist μ (pair X₂ (pair X₃ X₄)) (b, c, d) := fun c =>
    dist_le_dist_comp hμ (pair X₁ (pair X₂ (pair X₃ X₄))) Prod.snd (a, b, c, d)
  have hle' : dist μ (pair X₁ (pair X₂ (pair X₃ X₄))) (a, b, c, d) ≤ dist μ (pair X₂ X₄) (b, d) :=
    dist_le_dist_comp hμ (pair X₁ (pair X₂ (pair X₃ X₄))) (fun t => (t.2.1, t.2.2.2)) (a, b, c, d)
  have p₂₃₄ : ∀ c, 0 < dist μ (pair X₂ (pair X₃ X₄)) (b, c, d) := fun c =>
    (hpos a b c d).trans_le (hle c)
  have p₂₄ : 0 < dist μ (pair X₂ X₄) (b, d) := (hpos a b c d).trans_le hle'
  -- (2.25)
  have e₃ : ∀ c, dist μ (pair X₁ (pair X₂ X₃)) (a, b, c) * dist μ (pair X₂ X₄) (b, d) =
      dist μ (pair X₂ X₃) (b, c) * dist μ (pair X₁ (pair X₂ X₄)) (a, b, d) := by
    intro c
    refine mul_left_cancel₀ (p₂₃₄ c).ne' ?_
    have h₁' := e₁ c
    have h₂' := e₂ c
    calc _ = (dist μ (pair X₁ (pair X₂ X₃)) (a, b, c) * dist μ (pair X₂ (pair X₃ X₄)) (b, c, d)) *
            dist μ (pair X₂ X₄) (b, d) := by ring
      _ = dist μ (pair X₂ X₃) (b, c) * (dist μ (pair X₁ (pair X₂ (pair X₃ X₄))) (a, b, c, d) *
            dist μ (pair X₂ X₄) (b, d)) := by rw [← h₁']; ring
      _ = _ := by rw [h₂']; ring
  -- (2.26)–(2.29), summing over `x₃`
  have e₄ : dist μ (pair X₁ X₂) (a, b) * dist μ (pair X₂ X₄) (b, d) =
      dist μ X₂ b * dist μ (pair X₁ (pair X₂ X₄)) (a, b, d) := by
    have s₁ : dist μ (pair X₁ X₂) (a, b) = ∑ c, dist μ (pair X₁ (pair X₂ X₃)) (a, b, c) := by
      rw [← sum_dist_pair_right μ (pair X₁ X₂) X₃ (a, b)]
      exact sum_congr rfl fun c _ => dist_congr_of_iff μ fun ω => by simp [pair, and_assoc]
    rw [s₁, ← sum_dist_pair_right μ X₂ X₃ b, sum_mul, sum_mul]
    exact sum_congr rfl fun c _ => e₃ c
  -- (2.30)
  refine mul_left_cancel₀ p₂₄.ne' ?_
  calc _ = (dist μ (pair X₁ (pair X₂ (pair X₃ X₄))) (a, b, c, d) * dist μ (pair X₂ X₄) (b, d)) *
          dist μ X₂ b := by ring
    _ = (dist μ X₂ b * dist μ (pair X₁ (pair X₂ X₄)) (a, b, d)) *
          dist μ (pair X₂ (pair X₃ X₄)) (b, c, d) := by rw [e₂ c]; ring
    _ = _ := by rw [← e₄]; ring

/-- **Section 2.1**, after Proposition 2.12: positivity cannot be dropped from the intersection
axiom. Let `Y` and `Z` be independent, with `Y` not deterministic, and let `X₁ = Y`, `X₂ = Z` and
`X₃ = X₄ = (Y, Z)`. Then `X₁ ⊥ X₄ | (X₂, X₃)` and `X₁ ⊥ X₃ | (X₂, X₄)`, but not
`X₁ ⊥ (X₃, X₄) | X₂`. -/
theorem condIndep_intersection_counterexample [Fintype α] [Finite β] {μ : Ω → ℝ} (hμ : IsPMF μ)
    {Y : Ω → α} {Z : Ω → β} (hind : IndepRV μ Y Z) (hY : H[Y ; μ] ≠ 0) :
    CondIndep μ Y (pair Y Z) (pair Z (pair Y Z)) ∧
      ¬ CondIndep μ Y (pair (pair Y Z) (pair Y Z)) Z := by
  have := Fintype.ofFinite β
  have h₀ : ∀ {κ : Type _} [Fintype κ] (W : Ω → κ) (g : κ → α), Y = g ∘ W → H[Y | W ; μ] = 0 := by
    intro κ _ W g hg
    rw [hg]
    exact condEntropy_comp_self hμ W g
  constructor
  · rw [← condMutualInfo_eq_zero_iff hμ]
    refine le_antisymm ?_ (condMutualInfo_nonneg hμ _ _ _)
    have h₁ := h₀ (pair Z (pair Y Z)) (fun t => t.2.1) rfl
    have h₂ := condEntropy_nonneg hμ Y (pair (pair Y Z) (pair Z (pair Y Z)))
    rw [condMutualInfo, h₁]
    linarith
  · rw [← condMutualInfo_eq_zero_iff hμ, condMutualInfo,
      h₀ (pair (pair (pair Y Z) (pair Y Z)) Z) (fun t => t.1.1.1) rfl, sub_zero,
      (condEntropy_eq_entropy_iff hμ Y Z).2 hind]
    exact hY

end InfoTheory
