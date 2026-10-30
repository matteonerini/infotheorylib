/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Conditional

/-!
# Channels (transition kernels) between finite alphabets

A channel from `α` to `β` is a function `W : α → β → ℝ` whose rows `W x` are pmfs; `W x y` is the
transition probability `p(y | x)`.

## Main definitions

* `IsChannel W`: every row of `W` is a pmf.
* `jointOf p W`: the joint pmf `p(x) W(y | x)` on `α × β`.
* `outDist p W`: the output pmf `p(y) = ∑ₓ p(x) W(y | x)`.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- The joint pmf `p(x, y) = p(x) p(y|x)` built from an input distribution `p` and a channel
(transition kernel) `W(y|x) = W x y`. -/
def jointOf (p : α → ℝ) (W : α → β → ℝ) : α × β → ℝ := fun z => p z.1 * W z.1 z.2

/-- A channel: every row `W x` is a pmf. -/
def IsChannel (W : α → β → ℝ) : Prop := ∀ x, IsPMF (W x)

/-- The output distribution `p(y) = ∑ₓ p(x) W(y|x)`. -/
def outDist (p : α → ℝ) (W : α → β → ℝ) : β → ℝ := fun y => ∑ x, p x * W x y

lemma jointOf_isPMF {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    IsPMF (jointOf p W) :=
  ⟨fun z => mul_nonneg (hp.nonneg _) ((hW _).nonneg _), by
    simp only [jointOf, Fintype.sum_prod_type, ← mul_sum, (hW _).sum_eq_one, mul_one,
      hp.sum_eq_one]⟩

lemma dist_jointOf_fst {p : α → ℝ} {W : α → β → ℝ} (hW : IsChannel W) :
    dist (jointOf p W) Prod.fst = p := by
  funext x; rw [dist_fst]; simp [jointOf, ← mul_sum, (hW x).sum_eq_one]

lemma dist_jointOf_snd (p : α → ℝ) (W : α → β → ℝ) :
    dist (jointOf p W) Prod.snd = outDist p W := by
  funext y; rw [dist_snd]; rfl

lemma outDist_isPMF {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    IsPMF (outDist p W) := by
  rw [← dist_jointOf_snd]; exact (jointOf_isPMF hp hW).dist _

omit [Fintype α] in
lemma IsChannel.mix {W₁ W₂ : α → β → ℝ} (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) : IsChannel (s • W₁ + t • W₂) := fun x => by
  have := (h₁ x).mix (h₂ x) hs ht hst
  simpa using this

omit [Fintype α] [Fintype β] in
lemma absCont_jointOf {p q : α → ℝ} {r : α → β → ℝ} (hpq : AbsCont p q) :
    AbsCont (jointOf p r) (jointOf q r) := by
  rintro ⟨x, y⟩ h
  rcases mul_eq_zero.1 h with h | h
  · simp [jointOf, hpq x h]
  · simp [jointOf, h]

omit [Fintype α] in
lemma marg_jointOf {p : α → ℝ} {r : α → β → ℝ} (hr : IsChannel r) : marg (jointOf p r) = p := by
  funext x; simp [marg, jointOf, ← mul_sum, (hr x).sum_eq_one]

omit [Fintype β] in
lemma marg_jointOf_swap (p : α → ℝ) (r : α → β → ℝ) :
    marg (jointOf p r ∘ Prod.swap) = outDist p r := by
  funext y; rfl

end InfoTheory
