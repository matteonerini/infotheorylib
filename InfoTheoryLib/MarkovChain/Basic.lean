/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Independence

/-!
# Markov chains `X → Y → Z`

## Main definitions

* `MarkovChain μ X Y Z`: `X → Y → Z` is a Markov chain, `p(x, y, z) = p(x) p(y | x) p(z | y)`.

## Main statements

* `markovChain_iff_condIndep`: `X → Y → Z` iff `X` and `Z` are conditionally independent given
  `Y`.
* `MarkovChain.symm`: `X → Y → Z` implies `Z → Y → X`.
* `markovChain_comp`: `X → Y → f(Y)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.8
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Definition (2.117).** `X → Y → Z` is a Markov chain if
`p(x, y, z) = p(x) p(y|x) p(z|y)`. -/
def MarkovChain (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : Prop :=
  ∀ x y z, dist μ (pair X (pair Y Z)) (x, y, z) =
    dist μ X x * condDist μ Y X x y * condDist μ Z Y y z

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma dist_triple_le_mid {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (x : α) (y : β) (z : γ) : dist μ (pair X (pair Y Z)) (x, y, z) ≤ dist μ Y y :=
  dist_le_dist_comp hμ (pair X (pair Y Z)) (fun t => t.2.1) (x, y, z)

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- The Markov property in multiplicative form: `p(x, y, z) p(y) = p(x, y) p(y, z)`. -/
lemma markovChain_iff_mul {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    MarkovChain μ X Y Z ↔ ∀ x y z, dist μ (pair X (pair Y Z)) (x, y, z) * dist μ Y y =
      dist μ (pair X Y) (x, y) * dist μ (pair Y Z) (y, z) := by
  refine forall₃_congr fun x y z => ?_
  rw [dist_mul_condDist hμ, condDist]
  rcases eq_or_ne (dist μ Y y) 0 with h | h
  · have h1 : dist μ (pair X (pair Y Z)) (x, y, z) = 0 :=
      le_antisymm (h ▸ dist_triple_le_mid hμ X Y Z x y z) (dist_nonneg hμ _ _)
    have h2 : dist μ (pair X Y) (x, y) = 0 := dist_pair_eq_zero_of_right hμ X Y h x
    simp [h1, h2]
  · rw [mul_div_assoc']
    constructor
    · intro h'; rw [h', div_mul_cancel₀ _ h]
    · intro h'; rw [← h', mul_div_cancel_right₀ _ h]

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma dist_pair_rearrange (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) (x : α) (y : β)
    (z : γ) : dist μ (pair Y (pair X Z)) (y, x, z) = dist μ (pair X (pair Y Z)) (x, y, z) :=
  dist_eq_of_injective μ (U := pair X (pair Y Z)) (V := pair Y (pair X Z))
    (fun t : α × β × γ => (t.2.1, t.1, t.2.2))
    (fun a b h => by
      obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
      simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl) (x, y, z)

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma dist_pair_reverse (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) (x : α) (y : β)
    (z : γ) : dist μ (pair Z (pair Y X)) (z, y, x) = dist μ (pair X (pair Y Z)) (x, y, z) :=
  dist_eq_of_injective μ (U := pair X (pair Y Z)) (V := pair Z (pair Y X))
    (fun t : α × β × γ => (t.2.2, t.2.1, t.1))
    (fun a b h => by
      obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
      simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl) (x, y, z)

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- `X → Y → Z` iff `X` and `Z` are conditionally independent given `Y` (2.118). -/
theorem markovChain_iff_condIndep {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : MarkovChain μ X Y Z ↔ CondIndep μ X Z Y := by
  rw [markovChain_iff_mul hμ]
  constructor
  · intro h x z y
    simp only [condDist]
    rw [dist_pair_rearrange, dist_pair_swap μ X Y x y]
    rcases eq_or_ne (dist μ Y y) 0 with hy | hy
    · simp [hy]
    · field_simp
      linarith [h x y z]
  · intro h x y z
    have := h x z y
    simp only [condDist] at this
    rw [dist_pair_rearrange, dist_pair_swap μ X Y x y] at this
    rcases eq_or_ne (dist μ Y y) 0 with hy | hy
    · rw [hy, dist_pair_eq_zero_of_right hμ X Y hy x]; ring
    · field_simp at this
      linarith

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- `X → Y → Z` implies `Z → Y → X`. -/
theorem MarkovChain.symm {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : MarkovChain μ X Y Z) : MarkovChain μ Z Y X := by
  rw [markovChain_iff_mul hμ] at h ⊢
  intro z y x
  rw [dist_pair_reverse, h x y z, dist_pair_swap μ X Y x y, dist_pair_swap μ Y Z y z]
  ring

open Classical in
omit [Fintype α] [Fintype β] in
lemma dist_pair_comp_self (μ : Ω → ℝ) (U : Ω → α) (f : α → β) (u : α) (b : β) :
    dist μ (pair U (f ∘ U)) (u, b) = if f u = b then dist μ U u else 0 := by
  split_ifs with h
  · subst h
    exact dist_eq_of_injective μ (fun a => (a, f a)) (fun a b h => (Prod.mk.inj h).1)
      (fun _ => rfl) u
  · refine dist_eq_zero_of_forall_ne μ fun ω hω => ?_
    simp only [pair_apply, Function.comp_apply, Prod.mk.injEq] at hω
    exact h (hω.1 ▸ hω.2)

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- If `Z = f(Y)` then `X → Y → Z`. -/
theorem markovChain_comp {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (f : β → γ) :
    MarkovChain μ X Y (f ∘ Y) := by
  rw [markovChain_iff_mul hμ]
  intro x y z
  have h1 : dist μ (pair X (pair Y (f ∘ Y))) (x, y, z) =
      dist μ (pair (pair X Y) ((f ∘ Prod.snd) ∘ pair X Y)) ((x, y), z) :=
    (dist_eq_of_injective μ (U := pair (pair X Y) ((f ∘ Prod.snd) ∘ pair X Y))
      (V := pair X (pair Y (f ∘ Y))) (fun t : (α × β) × γ => (t.1.1, t.1.2, t.2))
      (fun a b h => by
        obtain ⟨⟨a1, a2⟩, a3⟩ := a; obtain ⟨⟨b1, b2⟩, b3⟩ := b
        simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl) ((x, y), z))
  rw [h1, dist_pair_comp_self, dist_pair_comp_self]
  simp only [Function.comp_apply]
  split_ifs <;> ring

end InfoTheory
