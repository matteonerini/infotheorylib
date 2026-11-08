/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib

/-!
# Probability mass functions and random variables on finite spaces

This file sets up the elementary probability used in the library. All alphabets are finite.

* A probability mass function (pmf) on a `Fintype` `α` is a function `p : α → ℝ` satisfying
  `IsPMF p`: it is non-negative and sums to `1`.
* A discrete random variable is a function `X : Ω → α` on a finite probability space `(Ω, μ)`,
  where `μ : Ω → ℝ` is a pmf. Its law is `dist μ X`, so `dist μ X a = Pr{X = a}`.
* The pair `(X, Y)` is the random variable `pair X Y : Ω → α × β`. A joint pmf `p(x, y)` on
  `α × β` is recovered by taking `Ω = α × β`, `μ = p`, `X = Prod.fst` and `Y = Prod.snd`.

## Main definitions

* `IsPMF`: probability mass functions.
* `dist μ X`: the law of a random variable; `pair X Y`: the joint random variable.
* `expect p g`: the expectation `E_p g(X) = ∑ₓ g(x) p(x)`.
* `AbsCont p q`: absolute continuity `p ≪ q`, i.e. `q x = 0 → p x = 0`.
* `prodDist p q`: the product pmf `p(x) q(y)`.
* `uniformPMF α`: the uniform pmf on `α`.

## Main statements

* `sum_dist_mul`: change of variables `∑ₐ Pr{X = a} g(a) = ∑_ω μ(ω) g(X ω)`.
* `sum_dist_pair_right`, `sum_dist_pair_left`: marginalization.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- A probability mass function on a finite alphabet. -/
structure IsPMF (p : α → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  sum_eq_one : ∑ x, p x = 1

lemma IsPMF.le_one {p : α → ℝ} (hp : IsPMF p) (x : α) : p x ≤ 1 := by
  rw [← hp.sum_eq_one]
  exact single_le_sum (fun y _ => hp.nonneg y) (mem_univ x)

open Classical in
/-- The law (probability mass function) of a random variable `X` on `(Ω, μ)`:
`dist μ X a = Pr{X = a}`. -/
def dist (μ : Ω → ℝ) (X : Ω → α) (a : α) : ℝ := ∑ ω, if X ω = a then μ ω else 0

/-- The pair `(X, Y)` of two random variables, a random variable with values in `α × β`. -/
def pair (X : Ω → α) (Y : Ω → β) : Ω → α × β := fun ω => (X ω, Y ω)

omit [Fintype Ω] [Fintype α] [Fintype β] in
@[simp] lemma pair_apply (X : Ω → α) (Y : Ω → β) (ω : Ω) : pair X Y ω = (X ω, Y ω) := rfl

omit [Fintype α] in
lemma dist_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (a : α) : 0 ≤ dist μ X a :=
  sum_nonneg fun ω _ => by split_ifs <;> simp [hμ.nonneg ω]

/-- Change of variables ("law of the unconscious statistician"):
`∑ₐ Pr{X = a} g(a) = ∑_ω μ(ω) g(X ω)`. -/
lemma sum_dist_mul (μ : Ω → ℝ) (X : Ω → α) (g : α → ℝ) :
    ∑ a, dist μ X a * g a = ∑ ω, μ ω * g (X ω) := by
  classical
  simp only [dist, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

lemma sum_dist (μ : Ω → ℝ) (X : Ω → α) : ∑ a, dist μ X a = ∑ ω, μ ω := by
  simpa using sum_dist_mul μ X (fun _ => 1)

lemma IsPMF.dist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) : IsPMF (dist μ X) :=
  ⟨dist_nonneg hμ X, by rw [sum_dist, hμ.sum_eq_one]⟩

omit [Fintype α] in
lemma le_dist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (ω : Ω) : μ ω ≤ dist μ X (X ω) := by
  classical
  unfold dist
  calc μ ω = if X ω = X ω then μ ω else 0 := by simp
    _ ≤ _ := single_le_sum (f := fun ω' => if X ω' = X ω then μ ω' else 0)
        (fun ω' _ => by split_ifs <;> simp [hμ.nonneg ω']) (mem_univ ω)

omit [Fintype α] in
lemma dist_pos {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) {ω : Ω} (h : 0 < μ ω) :
    0 < dist μ X (X ω) :=
  h.trans_le (le_dist hμ X ω)

omit [Fintype α] in
/-- Points of probability `0` carry no mass of `μ`. -/
lemma eq_zero_of_dist_eq_zero {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) {ω : Ω}
    (h : dist μ X (X ω) = 0) : μ ω = 0 :=
  le_antisymm (h ▸ le_dist hμ X ω) (hμ.nonneg ω)

open Classical in
omit [Fintype β] in
/-- The law of `f ∘ X`. -/
lemma dist_comp (μ : Ω → ℝ) (X : Ω → α) (f : α → β) (b : β) :
    dist μ (f ∘ X) b = ∑ a, if f a = b then dist μ X a else 0 := by
  have := sum_dist_mul μ X (fun a => if f a = b then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at this
  rw [this]; simp [dist]

omit [Fintype β] in
/-- The law of `f ∘ X` is the pushforward by `f` of the law of `X`. -/
lemma dist_comp_eq (μ : Ω → ℝ) (X : Ω → α) (f : α → β) : dist μ (f ∘ X) = dist (dist μ X) f := by
  funext b; rw [dist_comp]; rfl

omit [Fintype α] [Fintype β] in
lemma dist_comp_of_injective (μ : Ω → ℝ) (X : Ω → α) {f : α → β} (hf : Function.Injective f)
    (a : α) : dist μ (f ∘ X) (f a) = dist μ X a := by
  classical
  simp [dist, hf.eq_iff]

omit [Fintype α] [Fintype β] in
/-- `Pr{W = w} ≤ Pr{g(W) = g(w)}`. -/
lemma dist_le_dist_comp {μ : Ω → ℝ} (hμ : IsPMF μ) (W : Ω → α) (g : α → β) (w : α) :
    dist μ W w ≤ dist μ (g ∘ W) (g w) := by
  refine sum_le_sum fun ω _ => ?_
  by_cases h : W ω = w
  · simp [h]
  · simp only [h, ite_false]; split_ifs <;> simp [hμ.nonneg ω]

omit [Fintype α] [Fintype β] in
/-- If `V = e(U)` with `e` injective, then `Pr{V = e(u)} = Pr{U = u}`. -/
lemma dist_eq_of_injective (μ : Ω → ℝ) {U : Ω → α} {V : Ω → β} (e : α → β)
    (he : Function.Injective e) (h : ∀ ω, V ω = e (U ω)) (u : α) :
    dist μ V (e u) = dist μ U u := by
  rw [show V = e ∘ U from funext h]; exact dist_comp_of_injective μ U he u

omit [Fintype α] in
/-- A value that is never taken has probability `0`. -/
lemma dist_eq_zero_of_forall_ne (μ : Ω → ℝ) {V : Ω → α} {b : α} (h : ∀ ω, V ω ≠ b) :
    dist μ V b = 0 :=
  sum_eq_zero fun ω _ => by simp [h ω]

omit [Fintype α] in
/-- Marginalization: `∑_y p(x, y) = p(x)`. -/
lemma sum_dist_pair_right (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (a : α) :
    ∑ b, dist μ (pair X Y) (a, b) = dist μ X a := by
  classical
  simp only [dist, pair_apply, Prod.mk.injEq]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : X ω = a <;> simp [h]

omit [Fintype β] in
/-- Marginalization: `∑_x p(x, y) = p(y)`. -/
lemma sum_dist_pair_left (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (b : β) :
    ∑ a, dist μ (pair X Y) (a, b) = dist μ Y b := by
  have h := sum_dist_pair_right μ Y X b
  rw [← h]
  refine sum_congr rfl fun a _ => ?_
  have := dist_comp_of_injective μ (pair X Y) Prod.swap_injective (a, b)
  rw [← this]; rfl

omit [Fintype α] [Fintype β] in
lemma dist_pair_le_left {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (a : α) (b : β) :
    dist μ (pair X Y) (a, b) ≤ dist μ X a :=
  dist_le_dist_comp hμ (pair X Y) Prod.fst (a, b)

omit [Fintype α] [Fintype β] in
lemma dist_pair_le_right {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (a : α) (b : β) :
    dist μ (pair X Y) (a, b) ≤ dist μ Y b :=
  dist_le_dist_comp hμ (pair X Y) Prod.snd (a, b)

omit [Fintype α] [Fintype β] in
lemma dist_pair_eq_zero_of_left {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) {a : α}
    (h : dist μ X a = 0) (b : β) : dist μ (pair X Y) (a, b) = 0 :=
  le_antisymm (h ▸ dist_pair_le_left hμ X Y a b) (dist_nonneg hμ _ _)

omit [Fintype α] [Fintype β] in
lemma dist_pair_eq_zero_of_right {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) {b : β}
    (h : dist μ Y b = 0) (a : α) : dist μ (pair X Y) (a, b) = 0 :=
  le_antisymm (h ▸ dist_pair_le_right hμ X Y a b) (dist_nonneg hμ _ _)

omit [Fintype α] in
/-- The law of a random variable depends only on the random variable (as a function). -/
lemma dist_congr (μ : Ω → ℝ) {X X' : Ω → α} (h : ∀ ω, X ω = X' ω) : dist μ X = dist μ X' := by
  rw [show X = X' from funext h]

omit [Fintype α] [Fintype β] in
lemma dist_pair_swap (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (a : α) (b : β) :
    dist μ (pair Y X) (b, a) = dist μ (pair X Y) (a, b) := by
  have := dist_comp_of_injective μ (pair X Y) Prod.swap_injective (a, b)
  rw [← this]; rfl

open Classical in
omit [Fintype α] in
/-- `dist μ X` for a constant random variable. -/
lemma dist_const {μ : Ω → ℝ} (hμ : IsPMF μ) (c a : α) :
    dist μ (fun _ => c) a = if c = a then 1 else 0 := by
  unfold dist; split_ifs with h <;> simp [hμ.sum_eq_one]

/-- The law of the identity random variable on `(Ω, μ)` is `μ` itself. -/
lemma dist_id (μ : Ω → ℝ) : dist μ id = μ := by
  classical
  funext a; simp [dist]

/-- For a pmf `μ` on a product `α × β`, the first coordinate has the marginal law. -/
lemma dist_fst (μ : α × β → ℝ) (a : α) : dist μ Prod.fst a = ∑ b, μ (a, b) := by
  classical
  simp only [dist, Fintype.sum_prod_type]
  rw [sum_comm]; simp

/-- For a pmf `μ` on a product `α × β`, the second coordinate has the marginal law. -/
lemma dist_snd (μ : α × β → ℝ) (b : β) : dist μ Prod.snd b = ∑ a, μ (a, b) := by
  classical
  simp [dist, Fintype.sum_prod_type]

omit [Fintype α] [Fintype β] in
lemma pair_fst_snd : pair (Prod.fst : α × β → α) Prod.snd = id := rfl

lemma dist_pair_fst_snd (μ : α × β → ℝ) : dist μ (pair Prod.fst Prod.snd) = μ := dist_id μ

lemma dist_pair_snd_fst (μ : α × β → ℝ) (b : β) (a : α) :
    dist μ (pair Prod.snd Prod.fst) (b, a) = μ (a, b) := by
  rw [dist_pair_swap, dist_pair_fst_snd]

/-- Expectation `E_p g(X) = ∑ₓ g(x) p(x)` (2.2). -/
def expect (p : α → ℝ) (g : α → ℝ) : ℝ := ∑ x, g x * p x

/-- Absolute continuity `p ≪ q`: `q(x) = 0 → p(x) = 0`. Exactly in this case is `D(p‖q) < ∞`. -/
def AbsCont (p q : α → ℝ) : Prop := ∀ x, q x = 0 → p x = 0

/-- The product `p(x) q(y)` of two pmfs, a pmf on `α × β`. -/
def prodDist (p : α → ℝ) (q : β → ℝ) : α × β → ℝ := fun z => p z.1 * q z.2

lemma IsPMF.prodDist {p : α → ℝ} {q : β → ℝ} (hp : IsPMF p) (hq : IsPMF q) :
    IsPMF (prodDist p q) :=
  ⟨fun z => mul_nonneg (hp.nonneg _) (hq.nonneg _), by
    change ∑ z : α × β, p z.1 * q z.2 = 1
    rw [Fintype.sum_prod_type]
    simp [← mul_sum, hp.sum_eq_one, hq.sum_eq_one]⟩

omit [Fintype γ] [Fintype δ] in
/-- The law of a pair of functions of independent parts. -/
lemma dist_prodDist_pair (μ : α → ℝ) (ρ : β → ℝ) (F : α → γ) (G : β → δ) (x : γ) (y : δ) :
    dist (prodDist μ ρ) (fun z => (F z.1, G z.2)) (x, y) = dist μ F x * dist ρ G y := by
  classical
  simp only [dist, Prod.mk.injEq]
  rw [Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun u _ => ?_
  by_cases h₁ : F u = x
  · simp only [h₁, true_and, ite_true, prodDist, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    by_cases h₂ : G v = y <;> simp [h₂]
  · simp [h₁]

omit [Fintype γ] [Fintype δ] in
/-- The law of a function of the first part. -/
lemma dist_prodDist_comp_fst (μ : α → ℝ) {ρ : β → ℝ} (hρ : IsPMF ρ) (F : α → γ) (x : γ) :
    dist (prodDist μ ρ) (fun z => F z.1) x = dist μ F x := by
  classical
  simp only [dist, Fintype.sum_prod_type, prodDist]
  refine sum_congr rfl fun u _ => ?_
  by_cases h₁ : F u = x
  · simp only [h₁, ite_true, ← mul_sum, hρ.sum_eq_one, mul_one]
  · simp [h₁]

omit [Fintype γ] [Fintype δ] in
/-- The law of a function of the second part. -/
lemma dist_prodDist_comp_snd {μ : α → ℝ} (hμ : IsPMF μ) (ρ : β → ℝ) (G : β → δ) (y : δ) :
    dist (prodDist μ ρ) (fun z => G z.2) y = dist ρ G y := by
  classical
  simp only [dist, Fintype.sum_prod_type, prodDist]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  by_cases h₁ : G v = y
  · simp only [h₁, ite_true, ← sum_mul, hμ.sum_eq_one, one_mul]
  · simp [h₁]

omit [Fintype α] [Fintype β] in
lemma absCont_dist_pair_prodDist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    AbsCont (dist μ (pair X Y)) (prodDist (dist μ X) (dist μ Y)) := by
  rintro ⟨x, y⟩ h
  rcases mul_eq_zero.1 h with h | h
  · exact dist_pair_eq_zero_of_left hμ X Y h y
  · exact dist_pair_eq_zero_of_right hμ X Y h x

/-- The uniform pmf `u(x) = 1/|𝒳|`. -/
def uniformPMF (α : Type*) [Fintype α] : α → ℝ := fun _ => 1 / Fintype.card α

/-- A type that carries a pmf is nonempty. -/
lemma IsPMF.nonempty_type {p : α → ℝ} (hp : IsPMF p) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  simpa using hp.sum_eq_one

lemma card_pos_of_isPMF {p : α → ℝ} (hp : IsPMF p) : 0 < Fintype.card α := by
  rw [Fintype.card_pos_iff]
  by_contra h
  rw [not_nonempty_iff] at h
  have := hp.sum_eq_one
  simp at this

lemma uniformPMF_isPMF [Nonempty α] : IsPMF (uniformPMF α) :=
  ⟨fun _ => by simp [uniformPMF], by
    simp [uniformPMF, card_univ, Fintype.card_ne_zero]⟩

lemma IsPMF.mix {p₁ p₂ : α → ℝ} (h₁ : IsPMF p₁) (h₂ : IsPMF p₂) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : s + t = 1) : IsPMF (s • p₁ + t • p₂) :=
  ⟨fun x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (h₁.nonneg x)) (mul_nonneg ht (h₂.nonneg x)), by
    simp [sum_add_distrib, ← mul_sum, h₁.sum_eq_one, h₂.sum_eq_one, hst]⟩

omit [Fintype α] in
lemma AbsCont.mix {p₁ q₁ p₂ q₂ : α → ℝ} (hq₁ : ∀ x, 0 ≤ q₁ x) (hq₂ : ∀ x, 0 ≤ q₂ x)
    (h₁ : AbsCont p₁ q₁) (h₂ : AbsCont p₂ q₂) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsCont (s • p₁ + t • p₂) (s • q₁ + t • q₂) := by
  intro x hx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
  have ha := mul_nonneg hs (hq₁ x)
  have hb := mul_nonneg ht (hq₂ x)
  have e1 : s * q₁ x = 0 := by linarith
  have e2 : t * q₂ x = 0 := by linarith
  rcases mul_eq_zero.1 e1 with h | h <;> rcases mul_eq_zero.1 e2 with h' | h' <;>
    simp [h, h', h₁ x, h₂ x]

end InfoTheory
