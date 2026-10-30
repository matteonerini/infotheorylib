/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.FinitePMF

/-!
# Conditional distributions

## Main definitions

* `condDist μ Y X x y`: the conditional pmf `p(y | x) = p(x, y) / p(x)` of `Y` given `X = x`.
* `marg p`, `condPMF p`: the first marginal and the conditional pmf of a pmf `p` on `α × β`.

## Main statements

* `dist_mul_condDist`: `p(x) p(y | x) = p(x, y)`.
* `condDist_isPMF`: `p(· | x)` is a pmf whenever `p(x) > 0`.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- The conditional pmf `p(y | x) = p(x, y) / p(x)` of `Y` given `X = x`. -/
def condDist (μ : Ω → ℝ) (Y : Ω → β) (X : Ω → α) (x : α) (y : β) : ℝ :=
  dist μ (pair X Y) (x, y) / dist μ X x

omit [Fintype α] [Fintype β] in
lemma condDist_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) (x : α) (y : β) :
    0 ≤ condDist μ Y X x y :=
  div_nonneg (dist_nonneg hμ _ _) (dist_nonneg hμ _ _)

omit [Fintype α] in
/-- `p(· | x)` is a pmf whenever `p(x) > 0`. -/
lemma condDist_isPMF {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) {x : α}
    (hx : dist μ X x ≠ 0) : IsPMF (condDist μ Y X x) :=
  ⟨condDist_nonneg hμ Y X x, by
    simp only [condDist]; rw [← sum_div, sum_dist_pair_right, div_self hx]⟩

omit [Fintype α] [Fintype β] in
/-- `p(x) p(y | x) = p(x, y)`. -/
lemma dist_mul_condDist {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) (x : α) (y : β) :
    dist μ X x * condDist μ Y X x y = dist μ (pair X Y) (x, y) := by
  by_cases hx : dist μ X x = 0
  · rw [hx, zero_mul, dist_pair_eq_zero_of_left hμ X Y hx]
  · rw [condDist, mul_div_cancel₀ _ hx]

omit [Fintype α] [Fintype β] in
/-- (2.20) `log p(X, Y) = log p(X) + log p(Y|X)` (almost surely). -/
lemma log_dist_pair_eq {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) {ω : Ω}
    (hω : 0 < μ ω) :
    log (dist μ (pair X Y) (X ω, Y ω)) =
      log (dist μ X (X ω)) + log (condDist μ Y X (X ω) (Y ω)) := by
  have h1 : 0 < dist μ (pair X Y) (X ω, Y ω) := dist_pos hμ (pair X Y) hω
  have h2 : 0 < dist μ X (X ω) := dist_pos hμ X hω
  rw [condDist, log_div h1.ne' h2.ne']; ring

omit [Fintype α] [Fintype β] in
/-- The log of a conditional probability, `log p(y|x) = log p(x, y) - log p(x)` (a.s.). -/
lemma log_condDist {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) {ω : Ω}
    (hω : 0 < μ ω) : log (condDist μ Y X (X ω) (Y ω)) =
      log (dist μ (pair X Y) (X ω, Y ω)) - log (dist μ X (X ω)) := by
  rw [log_dist_pair_eq hμ X Y hω]; ring

omit [Fintype α] [Fintype β] in
lemma condDist_pos {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) {ω : Ω}
    (hω : 0 < μ ω) : 0 < condDist μ Y X (X ω) (Y ω) :=
  div_pos (dist_pos hμ (pair X Y) hω) (dist_pos hμ X hω)

/-- The first marginal `p(x) = ∑ᵧ p(x, y)` of a pmf on `α × β`. -/
def marg (p : α × β → ℝ) (x : α) : ℝ := ∑ y, p (x, y)

/-- The conditional pmf `p(y|x) = p(x, y) / p(x)` of a pmf on `α × β`. -/
def condPMF (p : α × β → ℝ) (x : α) (y : β) : ℝ := p (x, y) / marg p x

lemma marg_eq_dist (p : α × β → ℝ) : marg p = dist p Prod.fst := by
  funext x; rw [dist_fst]; rfl

omit [Fintype α] in
lemma le_marg {p : α × β → ℝ} (hp : ∀ z, 0 ≤ p z) (x : α) (y : β) : p (x, y) ≤ marg p x :=
  single_le_sum (f := fun y => p (x, y)) (fun _ _ => hp _) (mem_univ y)

omit [Fintype α] in
lemma marg_mul_condPMF {p : α × β → ℝ} (hp : ∀ z, 0 ≤ p z) (x : α) (y : β) :
    marg p x * condPMF p x y = p (x, y) := by
  by_cases hx : marg p x = 0
  · rw [hx, zero_mul]
    exact (le_antisymm (hx ▸ le_marg hp x y) (hp _)).symm
  · rw [condPMF, mul_div_cancel₀ _ hx]

lemma marg_isPMF {p : α × β → ℝ} (hp : IsPMF p) : IsPMF (marg p) :=
  ⟨fun x => sum_nonneg fun y _ => hp.nonneg _, by
    rw [← hp.sum_eq_one, Fintype.sum_prod_type]; rfl⟩

omit [Fintype α] in
lemma absCont_marg {p q : α × β → ℝ} (hq : ∀ z, 0 ≤ q z) (hpq : AbsCont p q) :
    AbsCont (marg p) (marg q) := by
  intro x hx
  have : ∀ y, q (x, y) = 0 := fun y => le_antisymm (hx ▸ le_marg hq x y) (hq _)
  exact sum_eq_zero fun y _ => hpq _ (this y)

omit [Fintype α] in
lemma condPMF_isPMF {p : α × β → ℝ} (hp : ∀ z, 0 ≤ p z) {x : α} (hx : marg p x ≠ 0) :
    IsPMF (condPMF p x) :=
  ⟨fun y => div_nonneg (hp _) (sum_nonneg fun _ _ => hp _), by
    simp only [condPMF]; rw [← sum_div]; exact div_self hx⟩

omit [Fintype α] in
lemma marg_pos_of_absCont {p q : α × β → ℝ} (hq : ∀ z, 0 ≤ q z)
    (hpq : AbsCont p q) {x : α} (hx : 0 < marg p x) : 0 < marg q x :=
  (sum_nonneg fun _ _ => hq _).lt_of_ne fun h => hx.ne' (absCont_marg hq hpq x h.symm)

omit [Fintype α] in
lemma absCont_condPMF {p q : α × β → ℝ} (hq : ∀ z, 0 ≤ q z) (hpq : AbsCont p q) (x : α) :
    AbsCont (condPMF p x) (condPMF q x) := by
  intro y hy
  rcases div_eq_zero_iff.1 hy with h | h
  · simp [condPMF, hpq _ h]
  · have : ∀ y', q (x, y') = 0 := fun y' => le_antisymm (h ▸ le_marg hq x y') (hq _)
    simp [condPMF, hpq _ (this y)]

end InfoTheory
