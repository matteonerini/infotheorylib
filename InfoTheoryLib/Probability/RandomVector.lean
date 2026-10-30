/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Independence

/-!
# Finite families of random variables

A sequence of random variables is `X : ℕ → Ω → α`, indexed from `0`. The random vector of its
first `n` terms is `prefixRV X n = (X₀, …, X_{n-1}) : Ω → (Fin n → α)`.

## Main definitions

* `prefixRV X n`: the random vector `(X₀, …, X_{n-1})`.
* `IndepFamily μ X n`: mutual independence of `X₀, …, X_{n-1}`.

## Main statements

* `indepFamily_iff`: `X₀, …, X_{n-1}` are independent iff each `Xᵢ` is independent of
  `(X₀, …, X_{i-1})`.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- The random vector `(X₀, …, X_{n-1})` built from a sequence of random variables. -/
def prefixRV (X : ℕ → Ω → α) (n : ℕ) : Ω → (Fin n → α) := fun ω i => X i ω

omit [Fintype α] in
lemma snoc_injective2 (n : ℕ) :
    Function.Injective (fun v : (Fin n → α) × α => (Fin.snoc v.1 v.2 : Fin (n + 1) → α)) := by
  rintro ⟨v, a⟩ ⟨w, b⟩ h
  simp only at h
  have ha : a = b := by simpa using congrFun h (Fin.last n)
  have hv : v = w := funext fun i => by simpa using congrFun h (Fin.castSucc i)
  rw [ha, hv]

omit [Fintype Ω] [Fintype α] in
lemma prefixRV_succ (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    prefixRV X (n + 1) ω = Fin.snoc (prefixRV X n ω) (X n ω) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [prefixRV]
  · simp [prefixRV]

omit [Fintype Ω] [Fintype α] in
lemma prefixRV_zero_eq (X : ℕ → Ω → α) : prefixRV X 0 = fun _ => Fin.elim0 := by
  funext ω i; exact i.elim0

/-- Mutual independence of `X₀, …, X_{n-1}`: `p(x₀, …, x_{n-1}) = ∏ᵢ p(xᵢ)`. -/
def IndepFamily (μ : Ω → ℝ) (X : ℕ → Ω → α) (n : ℕ) : Prop :=
  ∀ v : Fin n → α, dist μ (prefixRV X n) v = ∏ i : Fin n, dist μ (X i) (v i)

omit [Fintype α] in
lemma dist_prefixRV_succ (μ : Ω → ℝ) (X : ℕ → Ω → α) (n : ℕ) (v : Fin n → α) (a : α) :
    dist μ (prefixRV X (n + 1)) (Fin.snoc v a) = dist μ (pair (prefixRV X n) (X n)) (v, a) := by
  have h : prefixRV X (n + 1) =
      (fun w : (Fin n → α) × α => (Fin.snoc w.1 w.2 : Fin (n + 1) → α)) ∘
        pair (prefixRV X n) (X n) := funext fun ω => prefixRV_succ X n ω
  rw [h]
  exact dist_comp_of_injective μ _ (snoc_injective2 n) (v, a)

open Classical in
omit [Fintype α] in
lemma indepFamily_zero {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) : IndepFamily μ X 0 := by
  intro v
  rw [prefixRV_zero_eq, dist_const hμ]
  simp [Subsingleton.elim _ v]

omit [Fintype α] in
lemma indepFamily_succ_iff [Finite α] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (n : ℕ) :
    IndepFamily μ X (n + 1) ↔ IndepFamily μ X n ∧ IndepRV μ (prefixRV X n) (X n) := by
  have := Fintype.ofFinite α
  constructor
  · intro h
    have h' : ∀ w, dist μ (prefixRV X (n + 1)) w = ∏ i : Fin (n + 1), dist μ (X i) (w i) := h
    have hn : IndepFamily μ X n := by
      intro v
      rw [← sum_dist_pair_right μ (prefixRV X n) (X n) v]
      simp_rw [← dist_prefixRV_succ, h', Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      rw [← mul_sum, (hμ.dist (X n)).sum_eq_one, mul_one]
    refine ⟨hn, fun v a => ?_⟩
    rw [← dist_prefixRV_succ, h', Fin.prod_univ_castSucc, hn v]
    simp [Fin.snoc_castSucc]
  · rintro ⟨hn, hind⟩ w
    rw [← Fin.snoc_init_self w, dist_prefixRV_succ, hind (Fin.init w) (w (Fin.last n)),
      hn (Fin.init w), Fin.prod_univ_castSucc]
    simp [Fin.snoc_castSucc]

omit [Fintype α] in
lemma indepFamily_iff [Finite α] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (n : ℕ) :
    IndepFamily μ X n ↔ ∀ i ∈ range n, IndepRV μ (prefixRV X i) (X i) := by
  induction n with
  | zero => simp [indepFamily_zero hμ X]
  | succ n ih =>
    rw [indepFamily_succ_iff hμ, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 (mem_range.1 hi) with h | rfl
      · exact h1 i (mem_range.2 h)
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (mem_range.2 (Nat.lt_succ_of_lt (mem_range.1 hi))),
        h n (mem_range.2 n.lt_succ_self)⟩

end InfoTheory
