/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Inequalities.SubsetEntropy
public import InfoTheoryLib.MarkovChain.CondIndep

/-!
# Markov chains of `n` random variables

The chains in this file have random variables `X i : Ω → A i` with alphabets that depend on `i`,
since a block of variables of a chain is again a random variable of a chain, with a larger
alphabet. Only the variables with `i < n` matter for a chain of `n` variables.

## Main definitions

* `blockRV X s`: the random vector `(Xᵢ)_{i ∈ s}`.
* `blockEntropy μ X s`: its entropy.
* `IsMarkovChain μ X n`: `X₀ → X₁ → ⋯ → X_{n-1}` is a Markov chain.

## Main statements

* `isMarkovChain_three_iff`: for three variables, this is `MarkovChain`.
* `isMarkovChain_iff_condDist`: the form of a chain with conditional distributions.
* `isMarkovChain_reverse_iff`: the reverse of a chain is a chain.
* `isMarkovChain_iff_forall_markovChain`: a chain is a sequence of three-variable chains
  `(X₀, …, X_k) → X_{k+1} → X_{k+2}`.
* `isMarkovChain_iff_factorization`: a chain is a product of functions of consecutive variables.
* `IsMarkovChain.markovChain_block`: conditionally on a block containing `X_b`, the variables
  before `b` are independent of the variables from `b` on.
* `IsMarkovChain.block`: blocks of a chain form a chain.
* `IsMarkovChain.data_processing`: `I(Xᵢ; X_l) ≤ I(X_j; X_k)` for `i < j < k < l`.

## Implementation notes

The subchain property is proved with entropies of sets of indices: `blockEntropy` is monotone and
submodular, and a conditional mutual information of blocks is a linear combination of its values.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 2.1
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω : Type*} [Fintype Ω] {A : ℕ → Type*}

/-- The random vector `(Xᵢ)_{i ∈ s}`. -/
def blockRV (X : ∀ i, Ω → A i) (s : Finset ℕ) : Ω → ∀ i : s, A i := fun ω i => X i ω

omit [Fintype Ω] in
lemma blockRV_eq_iff (X : ∀ i, Ω → A i) (s : Finset ℕ) (ω : Ω) (x : ∀ i, A i) :
    blockRV X s ω = (fun i : s => x i) ↔ ∀ i ∈ s, X i ω = x i := by
  simp [blockRV, funext_iff]

/-- The probability that `Xᵢ = xᵢ` for all `i ∈ s`. -/
def blockDist (μ : Ω → ℝ) (X : ∀ i, Ω → A i) (s : Finset ℕ) (x : ∀ i, A i) : ℝ :=
  dist μ (blockRV X s) (fun i : s => x i)

/-- **Definition 2.6, (2.15).** `X₀ → X₁ → ⋯ → X_{n-1}` is a Markov chain if
`p(x₀, …, x_{n-1}) p(x₁) ⋯ p(x_{n-2}) = p(x₀, x₁) p(x₁, x₂) ⋯ p(x_{n-2}, x_{n-1})`.

The definition is meant for `n ≥ 2`, and the book's for `n ≥ 3`. For a pmf `μ` the type `Ω` is
nonempty, so all the alphabets `A i` are and the quantification over `x` is not vacuous. -/
def IsMarkovChain (μ : Ω → ℝ) (X : ∀ i, Ω → A i) (n : ℕ) : Prop :=
  ∀ x : ∀ i, A i, blockDist μ X (range n) x * ∏ i ∈ Ico 1 (n - 1), dist μ (X i) (x i) =
    ∏ i ∈ range (n - 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1))

section Dist

variable {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

lemma blockDist_nonneg (hμ : IsPMF μ) (s : Finset ℕ) (x : ∀ i, A i) :
    0 ≤ blockDist μ X s x :=
  dist_nonneg hμ _ _

lemma blockDist_le (hμ : IsPMF μ) {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) (x : ∀ i, A i) :
    blockDist μ X s x ≤ dist μ (X i) (x i) :=
  dist_le_dist_comp hμ (blockRV X s) (fun t => t ⟨i, hi⟩) (fun i : s => x i)

lemma blockDist_eq_zero (hμ : IsPMF μ) {s : Finset ℕ} {i : ℕ} (hi : i ∈ s) {x : ∀ i, A i}
    (h : dist μ (X i) (x i) = 0) : blockDist μ X s x = 0 :=
  le_antisymm (h ▸ blockDist_le hμ hi x) (blockDist_nonneg hμ s x)

lemma blockDist_congr {s : Finset ℕ} {x y : ∀ i, A i} (h : ∀ i ∈ s, x i = y i) :
    blockDist μ X s x = blockDist μ X s y :=
  dist_congr_of_iff μ fun ω => by
    rw [blockRV_eq_iff, blockRV_eq_iff]
    exact forall₂_congr fun i hi => by rw [h i hi]

lemma blockDist_succ_eq (n : ℕ) (x : ∀ i, A i) : blockDist μ X (range (n + 1)) x =
    dist μ (pair (blockRV X (range n)) (X n)) ((fun i : range n => x i), x n) :=
  dist_congr_of_iff μ fun ω => by
    simp only [pair, Prod.mk.injEq]
    rw [blockRV_eq_iff, blockRV_eq_iff, range_add_one, forall_mem_insert, and_comm]

lemma blockDist_succ_succ_eq (n : ℕ) (x : ∀ i, A i) : blockDist μ X (range (n + 2)) x =
    dist μ (pair (blockRV X (range n)) (pair (X n) (X (n + 1))))
      ((fun i : range n => x i), x n, x (n + 1)) :=
  dist_congr_of_iff μ fun ω => by
    simp only [pair, Prod.mk.injEq]
    rw [blockRV_eq_iff, blockRV_eq_iff, range_add_one, range_add_one, forall_mem_insert,
      forall_mem_insert]
    tauto

/-- Summing out the last variable. -/
lemma sum_blockDist_update (n : ℕ) [Fintype (A n)] (x : ∀ i, A i) :
    ∑ a : A n, blockDist μ X (range (n + 1)) (Function.update x n a) =
      blockDist μ X (range n) x := by
  rw [blockDist, ← sum_dist_pair_right μ (blockRV X (range n)) (X n) (fun i : range n => x i)]
  refine sum_congr rfl fun a _ => ?_
  rw [blockDist_succ_eq]
  simp only [Function.update_self]
  congr 2
  funext i
  exact Function.update_of_ne (fun h => by simpa [h] using i.2) _ _

end Dist

section Local

variable {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

/-- A point with prescribed coordinates below `k` and at `k` and `k + 1`. -/
def chainPoint (X : ∀ i, Ω → A i) (ω₀ : Ω) (k : ℕ) (u : ∀ i : range k, A i) (y : A k) :
    ∀ i, A i :=
  Function.update (fun i => if h : i ∈ range k then u ⟨i, h⟩ else X i ω₀) k y

omit [Fintype Ω] in
lemma chainPoint_restrict (ω₀ : Ω) (k : ℕ) (u : ∀ i : range k, A i) (y : A k) :
    (fun i : range k => chainPoint X ω₀ k u y i) = u := by
  funext i
  have hi : (i : ℕ) ≠ k := fun h => by simpa [h] using i.2
  simp [chainPoint, Function.update_of_ne hi, mem_range.1 i.2]

omit [Fintype Ω] in
lemma chainPoint_self (ω₀ : Ω) (k : ℕ) (u : ∀ i : range k, A i) (y : A k) :
    chainPoint X ω₀ k u y k = y := by
  simp [chainPoint]

lemma exists_of_isPMF (hμ : IsPMF μ) : Nonempty Ω :=
  Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)

/-- The three-variable chain `(X₀, …, X_{k-1}) → X_k → X_{k+1}` as an equation for all points. -/
lemma markovChain_block_iff (hμ : IsPMF μ) (X : ∀ i, Ω → A i) (k : ℕ) :
    MarkovChain μ (blockRV X (range k)) (X k) (X (k + 1)) ↔ ∀ x : ∀ i, A i,
      blockDist μ X (range (k + 2)) x * dist μ (X k) (x k) =
        blockDist μ X (range (k + 1)) x * dist μ (pair (X k) (X (k + 1))) (x k, x (k + 1)) := by
  rw [markovChain_iff_mul hμ]
  obtain ⟨ω₀⟩ := exists_of_isPMF hμ
  constructor
  · intro h x
    rw [blockDist_succ_succ_eq, blockDist_succ_eq]
    exact h _ _ _
  · intro h u y z
    have hx := h (Function.update (chainPoint X ω₀ k u y) (k + 1) z)
    have hk : Function.update (chainPoint X ω₀ k u y) (k + 1) z k = y := by
      rw [Function.update_of_ne (show k ≠ k + 1 by omega), chainPoint_self]
    have hr : (fun i : range k => Function.update (chainPoint X ω₀ k u y) (k + 1) z i) = u := by
      funext i
      have hi : (i : ℕ) ≠ k + 1 := by
        have := mem_range.1 i.2
        omega
      rw [Function.update_of_ne hi]
      exact congrFun (chainPoint_restrict ω₀ k u y) i
    rw [blockDist_succ_succ_eq, blockDist_succ_eq, hk, hr, Function.update_self] at hx
    exact hx

/-- The step of **Proposition 2.8**: a chain of `k + 3` variables is a chain of `k + 2` variables
followed by `(X₀, …, X_k) → X_{k+1} → X_{k+2}`. -/
theorem isMarkovChain_succ_iff [∀ i, Finite (A i)] (hμ : IsPMF μ) (X : ∀ i, Ω → A i) (k : ℕ) :
    IsMarkovChain μ X (k + 3) ↔ IsMarkovChain μ X (k + 2) ∧
      MarkovChain μ (blockRV X (range (k + 1))) (X (k + 1)) (X (k + 2)) := by
  have : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite (A i)
  rw [markovChain_block_iff hμ X (k + 1)]
  simp only [IsMarkovChain, Nat.add_succ_sub_one]
  have hsplit : ∀ x : ∀ i, A i, ∏ i ∈ Ico 1 (k + 2), dist μ (X i) (x i) =
      (∏ i ∈ Ico 1 (k + 1), dist μ (X i) (x i)) * dist μ (X (k + 1)) (x (k + 1)) := fun x =>
    prod_Ico_succ_top (by omega) _
  constructor
  · intro h
    have h₁ : ∀ x : ∀ i, A i, blockDist μ X (range (k + 2)) x *
        ∏ i ∈ Ico 1 (k + 1), dist μ (X i) (x i) =
          ∏ i ∈ range (k + 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) := by
      intro x
      -- sum out the last variable of the chain
      have hsum : blockDist μ X (range (k + 2)) x * ((∏ i ∈ Ico 1 (k + 1), dist μ (X i) (x i)) *
          dist μ (X (k + 1)) (x (k + 1))) =
          (∏ i ∈ range (k + 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1))) *
            dist μ (X (k + 1)) (x (k + 1)) := by
        have key : ∀ a : A (k + 2),
            blockDist μ X (range (k + 2 + 1)) (Function.update x (k + 2) a) *
            ((∏ i ∈ Ico 1 (k + 1), dist μ (X i) (x i)) * dist μ (X (k + 1)) (x (k + 1))) =
            (∏ i ∈ range (k + 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1))) *
              dist μ (pair (X (k + 1)) (X (k + 2))) (x (k + 1), a) := fun a => ?_
        · rw [← sum_blockDist_update (k + 2) x, sum_mul, sum_congr rfl fun a _ => key a, ← mul_sum,
            sum_dist_pair_right]
        have hx := h (Function.update x (k + 2) a)
        rw [hsplit, prod_range_succ] at hx
        have e₁ : ∀ i ∈ Ico 1 (k + 1), dist μ (X i) (Function.update x (k + 2) a i) =
            dist μ (X i) (x i) := fun i hi => by
          rw [Function.update_of_ne (by have := (mem_Ico.1 hi).2; omega)]
        have e₂ : ∀ i ∈ range (k + 1), dist μ (pair (X i) (X (i + 1)))
            (Function.update x (k + 2) a i, Function.update x (k + 2) a (i + 1)) =
              dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) := fun i hi => by
          have := mem_range.1 hi
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        rw [prod_congr rfl e₁, prod_congr rfl e₂, Function.update_of_ne (by omega),
          Function.update_self] at hx
        exact hx
      rcases (dist_nonneg hμ (X (k + 1)) (x (k + 1))).eq_or_lt with h0 | h0
      · rw [blockDist_eq_zero hμ (by simp) h0.symm, zero_mul, prod_range_succ,
          dist_pair_eq_zero_of_right hμ _ _ h0.symm, mul_zero]
      · exact mul_right_cancel₀ h0.ne' (by rw [← hsum]; ring)
    refine ⟨h₁, fun x => ?_⟩
    by_cases h0 : ∃ i ∈ Ico 1 (k + 1), dist μ (X i) (x i) = 0
    · obtain ⟨i, hi, h0⟩ := h0
      have hi' := (mem_Ico.1 hi).2
      rw [blockDist_eq_zero hμ (mem_range.2 (by omega)) h0,
        blockDist_eq_zero hμ (mem_range.2 (by omega)) h0, zero_mul, zero_mul]
    · have hne : ∏ i ∈ Ico 1 (k + 1), dist μ (X i) (x i) ≠ 0 :=
        prod_ne_zero_iff.2 fun i hi h' => h0 ⟨i, hi, h'⟩
      refine mul_left_cancel₀ hne ?_
      have e₁ := h x
      have e₂ := h₁ x
      rw [hsplit, prod_range_succ, ← e₂] at e₁
      linear_combination e₁
  · rintro ⟨h₁, h₂⟩ x
    rw [hsplit, prod_range_succ, ← h₁ x]
    linear_combination (∏ i ∈ Ico 1 (k + 1), dist μ (X i) (x i)) * h₂ x

/-- **Proposition 2.8.** `X₀ → X₁ → ⋯ → X_{n-1}` is a Markov chain iff
`(X₀, …, X_k) → X_{k+1} → X_{k+2}` is one for all `k` with `k + 2 < n`. -/
theorem isMarkovChain_iff_forall_markovChain [∀ i, Finite (A i)] (hμ : IsPMF μ)
    (X : ∀ i, Ω → A i) {n : ℕ} (hn : 2 ≤ n) :
    IsMarkovChain μ X n ↔
      ∀ k, k + 2 < n → MarkovChain μ (blockRV X (range (k + 1))) (X (k + 1)) (X (k + 2)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨fun _ k hk => by omega, fun _ x => ?_⟩
    simp only [Nat.add_one_sub_one, Ico_self, prod_empty, mul_one, prod_range_one]
    exact blockDist_succ_eq 1 x |>.trans (dist_congr_of_iff μ fun ω => by
      simp only [pair, Prod.mk.injEq]
      rw [blockRV_eq_iff]
      simp)
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [isMarkovChain_succ_iff hμ, ih]
    constructor
    · rintro ⟨h₁, h₂⟩ j hj
      rcases (by omega : j + 2 < k + 2 ∨ j = k) with hj | rfl
      · exact h₁ j hj
      · exact h₂
    · intro h
      exact ⟨fun j hj => h j (by omega), h k (by omega)⟩

/-- For three variables, `IsMarkovChain` is `MarkovChain`. -/
theorem isMarkovChain_three_iff (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    IsMarkovChain μ X 3 ↔ MarkovChain μ (X 0) (X 1) (X 2) := by
  rw [markovChain_iff_mul hμ]
  obtain ⟨ω₀⟩ := exists_of_isPMF hμ
  have e₁ : ∀ x : ∀ i, A i, blockDist μ X (range 3) x =
      dist μ (pair (X 0) (pair (X 1) (X 2))) (x 0, x 1, x 2) := fun x =>
    dist_congr_of_iff μ fun ω => by
      rw [blockRV_eq_iff]
      simp [pair, range_add_one, and_comm, and_assoc]
  simp only [IsMarkovChain, show 3 - 1 = 2 from rfl, e₁, prod_range_succ, prod_range_zero, one_mul]
  have e₂ : ∀ f : ℕ → ℝ, ∏ i ∈ Ico 1 2, f i = f 1 := fun f => by simp
  simp only [e₂]
  constructor
  · intro h a b c
    have hx := h (Function.update (Function.update (Function.update (fun i => X i ω₀) 0 a) 1 b) 2 c)
    simpa using hx
  · intro h x
    exact h _ _ _

open Classical in
/-- **Definition 2.6, (2.16).** `X₀ → X₁ → ⋯ → X_{n-1}` is a Markov chain iff
`p(x₀, …, x_{n-1}) = p(x₀, x₁) p(x₂ | x₁) ⋯ p(x_{n-1} | x_{n-2})` when
`p(x₁), …, p(x_{n-2}) > 0`, and `p(x₀, …, x_{n-1}) = 0` otherwise. -/
theorem isMarkovChain_iff_condDist (hμ : IsPMF μ) (X : ∀ i, Ω → A i) {n : ℕ} (hn : 2 ≤ n) :
    IsMarkovChain μ X n ↔ ∀ x : ∀ i, A i, blockDist μ X (range n) x =
      if ∀ i ∈ Ico 1 (n - 1), 0 < dist μ (X i) (x i) then
        dist μ (pair (X 0) (X 1)) (x 0, x 1) *
          ∏ i ∈ Ico 1 (n - 1), condDist μ (X (i + 1)) (X i) (x i) (x (i + 1))
      else 0 := by
  refine forall_congr' fun x => ?_
  have hQ : ∏ i ∈ range (n - 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) =
      dist μ (pair (X 0) (X 1)) (x 0, x 1) *
        ∏ i ∈ Ico 1 (n - 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) := by
    rw [range_eq_Ico, prod_eq_prod_Ico_succ_bot (by omega)]
  split_ifs with hpos
  · have hne : ∏ i ∈ Ico 1 (n - 1), dist μ (X i) (x i) ≠ 0 :=
      prod_ne_zero_iff.2 fun i hi => (hpos i hi).ne'
    simp only [condDist]
    rw [prod_div_distrib, hQ, ← mul_div_assoc, eq_div_iff hne]
  · push Not at hpos
    obtain ⟨i, hi, h0⟩ := hpos
    have h0' : dist μ (X i) (x i) = 0 := le_antisymm h0 (dist_nonneg hμ _ _)
    have hi' := mem_Ico.1 hi
    constructor
    · intro _
      exact blockDist_eq_zero hμ (mem_range.2 (by omega)) h0'
    · intro _
      rw [prod_eq_zero hi h0', mul_zero]
      exact (prod_eq_zero (mem_range.2 hi'.2) (dist_pair_eq_zero_of_left hμ _ _ h0' _)).symm

end Local

section Reverse

variable {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

omit [Fintype Ω] in
/-- A point of a reversed chain comes from a point of the chain. -/
lemma exists_reverse_point (X : ∀ i, Ω → A i) (ω₀ : Ω) (n : ℕ) (x' : ∀ i, A (n - 1 - i)) :
    ∃ x : ∀ i, A i, ∀ j, j < n → x (n - 1 - j) = x' j := by
  have hc : ∀ i, i < n → n - 1 - (n - 1 - i) = i := fun i hi => by omega
  refine ⟨fun i => if h : i < n then cast (congrArg A (hc i h)) (x' (n - 1 - i)) else X i ω₀,
    fun j hj => ?_⟩
  have hlt : n - 1 - j < n := by omega
  simp only [hlt, ↓reduceDIte]
  have key : ∀ (m : ℕ) (hm : m = j) (e : A (n - 1 - m) = A (n - 1 - j)),
      cast e (x' m) = x' j := by
    rintro m rfl e
    rfl
  exact key _ (by omega) _

/-- The equation (2.15) at a point `x` is the equation for the reversed chain at the same point. -/
lemma isMarkovChain_reverse_aux {n : ℕ} {x : ∀ i, A i} {x' : ∀ i, A (n - 1 - i)}
    (hx : ∀ j, j < n → x (n - 1 - j) = x' j) :
    (blockDist μ (fun i => X (n - 1 - i)) (range n) x' *
        ∏ i ∈ Ico 1 (n - 1), dist μ (X (n - 1 - i)) (x' i) =
      ∏ i ∈ range (n - 1), dist μ (pair (X (n - 1 - i)) (X (n - 1 - (i + 1))))
        (x' i, x' (i + 1))) ↔
    (blockDist μ X (range n) x * ∏ i ∈ Ico 1 (n - 1), dist μ (X i) (x i) =
      ∏ i ∈ range (n - 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1))) := by
  have e₀ : blockDist μ (fun i => X (n - 1 - i)) (range n) x' = blockDist μ X (range n) x := by
    refine dist_congr_of_iff μ fun ω => ?_
    rw [blockRV_eq_iff, blockRV_eq_iff]
    simp only [mem_range]
    constructor
    · intro h' i hi
      have := h' (n - 1 - i) (by omega)
      rw [← hx _ (by omega)] at this
      have hc : n - 1 - (n - 1 - i) = i := by omega
      rwa [hc] at this
    · intro h' j hj
      rw [← hx j hj]
      exact h' _ (by omega)
  have e₁ : ∏ i ∈ Ico 1 (n - 1), dist μ (X (n - 1 - i)) (x' i) =
      ∏ i ∈ Ico 1 (n - 1), dist μ (X i) (x i) := by
    refine prod_nbij' (fun i => n - 1 - i) (fun i => n - 1 - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [mem_Ico] at hi ⊢; omega
    · intro i hi; simp only [mem_Ico] at hi ⊢; omega
    · intro i hi; simp only [mem_Ico] at hi; omega
    · intro i hi; simp only [mem_Ico] at hi; omega
    · intro i hi
      simp only [mem_Ico] at hi
      rw [← hx i (by omega)]
  -- a function of two natural numbers hides the dependence of the alphabets on the indices
  let q : ℕ → ℕ → ℝ := fun a b => dist μ (pair (X a) (X b)) (x a, x b)
  have e₂ : ∏ i ∈ range (n - 1), dist μ (pair (X (n - 1 - i)) (X (n - 1 - (i + 1))))
      (x' i, x' (i + 1)) =
      ∏ i ∈ range (n - 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) := by
    change _ = ∏ i ∈ range (n - 1), q i (i + 1)
    have e : ∀ i ∈ range (n - 1), dist μ (pair (X (n - 1 - i)) (X (n - 1 - (i + 1))))
        (x' i, x' (i + 1)) = q (n - 1 - (i + 1)) (n - 1 - (i + 1) + 1) := by
      intro i hi
      have hi' := mem_range.1 hi
      have hb : n - 1 - (i + 1) + 1 = n - 1 - i := by omega
      rw [hb]
      simp only [q]
      rw [dist_pair_swap, hx i (by omega), hx (i + 1) (by omega)]
    rw [prod_congr rfl e]
    refine prod_nbij' (fun i => n - 1 - (i + 1)) (fun i => n - 1 - (i + 1)) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [mem_range] at hi ⊢; omega
    · intro i hi; simp only [mem_range] at hi ⊢; omega
    · intro i hi; simp only [mem_range] at hi; omega
    · intro i hi; simp only [mem_range] at hi; omega
    · intro i hi; rfl
  rw [e₀, e₁, e₂]


/-- **Proposition 2.7.** `X₀ → X₁ → ⋯ → X_{n-1}` is a Markov chain iff
`X_{n-1} → ⋯ → X₁ → X₀` is one. -/
theorem isMarkovChain_reverse_iff (hμ : IsPMF μ) (X : ∀ i, Ω → A i) (n : ℕ) :
    IsMarkovChain μ (fun i => X (n - 1 - i)) n ↔ IsMarkovChain μ X n := by
  obtain ⟨ω₀⟩ := exists_of_isPMF hμ
  constructor
  · intro h x
    exact (isMarkovChain_reverse_aux (x' := fun j => x (n - 1 - j)) fun _ _ => rfl).1 (h _)
  · intro h x'
    obtain ⟨x, hx⟩ := exists_reverse_point X ω₀ n x'
    exact (isMarkovChain_reverse_aux hx).2 (h x)

end Reverse

section Factorization

variable {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

/-- The easy direction of **Proposition 2.9**. -/
theorem IsMarkovChain.exists_factorization {n : ℕ} (hn : 2 ≤ n)
    (h : IsMarkovChain μ X n) :
    ∃ f : ∀ i, A i → A (i + 1) → ℝ, ∀ x : ∀ i, A i,
      (∀ i ∈ Ico 1 (n - 1), 0 < dist μ (X i) (x i)) →
        blockDist μ X (range n) x = ∏ i ∈ range (n - 1), f i (x i) (x (i + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨fun i u v => dist μ (pair (X i) (X (i + 1))) (u, v) /
    (if i < m then dist μ (X (i + 1)) v else 1), fun x hx => ?_⟩
  simp only [Nat.add_succ_sub_one] at hx ⊢
  have h₀ : blockDist μ X (range (m + 2)) x * ∏ i ∈ Ico 1 (m + 1), dist μ (X i) (x i) =
      ∏ i ∈ range (m + 1), dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) := h x
  have hne : ∏ i ∈ Ico 1 (m + 1), dist μ (X i) (x i) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi => (hx i hi).ne'
  have hne' : ∏ i ∈ range m, dist μ (X (i + 1)) (x (i + 1)) ≠ 0 := prod_ne_zero_iff.2 fun i hi =>
    (hx (i + 1) (mem_Ico.2 ⟨by omega, by have := mem_range.1 hi; omega⟩)).ne'
  have hD : ∏ i ∈ Ico 1 (m + 1), dist μ (X i) (x i) =
      ∏ i ∈ range m, dist μ (X (i + 1)) (x (i + 1)) := by
    rw [prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    exact prod_congr rfl fun i _ => by rw [add_comm 1 i]
  have hF : ∏ i ∈ range (m + 1), (dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) /
      (if i < m then dist μ (X (i + 1)) (x (i + 1)) else 1)) =
      (∏ i ∈ range m, (dist μ (pair (X i) (X (i + 1))) (x i, x (i + 1)) /
        dist μ (X (i + 1)) (x (i + 1)))) * dist μ (pair (X m) (X (m + 1))) (x m, x (m + 1)) := by
    rw [prod_range_succ]
    congr 1
    · exact prod_congr rfl fun i hi => by simp [mem_range.1 hi]
    · simp
  refine mul_right_cancel₀ hne ?_
  rw [h₀, hF, prod_div_distrib, prod_range_succ, hD]
  field_simp

/-- A factorization of a chain of `k + 3` variables gives one with `k + 2` variables. -/
lemma factorization_pred [∀ i, Finite (A i)] (hμ : IsPMF μ) {k : ℕ}
    {f : ∀ i, A i → A (i + 1) → ℝ}
    (h : ∀ x : ∀ i, A i, (∀ i ∈ Ico 1 (k + 2), 0 < dist μ (X i) (x i)) →
      blockDist μ X (range (k + 3)) x = ∏ i ∈ range (k + 2), f i (x i) (x (i + 1))) :
    ∃ f' : ∀ i, A i → A (i + 1) → ℝ, ∀ x : ∀ i, A i,
      (∀ i ∈ Ico 1 (k + 1), 0 < dist μ (X i) (x i)) →
        blockDist μ X (range (k + 2)) x = ∏ i ∈ range (k + 1), f' i (x i) (x (i + 1)) := by
  classical
  have : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite (A i)
  -- the sum over the last variable, as a function of the variable before it
  let g : ∀ j, A j → ℝ := fun j v =>
    if j = k + 1 then (if 0 < dist μ (X j) v then ∑ a, f j v a else 0) else 1
  refine ⟨fun i u v => f i u v * g (i + 1) v, fun x hx => ?_⟩
  rw [prod_range_succ]
  have e : ∀ i ∈ range k, f i (x i) (x (i + 1)) * g (i + 1) (x (i + 1)) =
      f i (x i) (x (i + 1)) := fun i hi => by
    have : i ≠ k := by have := mem_range.1 hi; omega
    simp [g, this]
  rw [prod_congr rfl e]
  beta_reduce
  rcases (dist_nonneg hμ (X (k + 1)) (x (k + 1))).eq_or_lt with h0 | h0
  · rw [blockDist_eq_zero hμ (by simp) h0.symm]
    simp [g, ← h0]
  · have hg : g (k + 1) (x (k + 1)) = ∑ a, f (k + 1) (x (k + 1)) a := by
      simp [g, h0]
    rw [hg, ← sum_blockDist_update (k + 2) x, mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have hpos : ∀ i ∈ Ico 1 (k + 2), 0 < dist μ (X i) (Function.update x (k + 2) a i) := by
      intro i hi
      have hi' := mem_Ico.1 hi
      rw [Function.update_of_ne (by omega)]
      rcases (by omega : i < k + 1 ∨ i = k + 1) with hlt | rfl
      · exact hx i (mem_Ico.2 ⟨hi'.1, hlt⟩)
      · exact h0
    rw [show range (k + 2 + 1) = range (k + 3) from rfl, h _ hpos, prod_range_succ,
      prod_range_succ, Function.update_of_ne (by omega), Function.update_self]
    have e₁ : ∀ i ∈ range k, f i (Function.update x (k + 2) a i)
        (Function.update x (k + 2) a (i + 1)) = f i (x i) (x (i + 1)) := fun i hi => by
      have := mem_range.1 hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rw [prod_congr rfl e₁, Function.update_of_ne (show k + 1 ≠ k + 2 by omega)]
    ring

/-- A factorization of a chain of `k + 3` variables gives the last three-variable chain. -/
lemma markovChain_last_of_factorization [∀ i, Finite (A i)] (hμ : IsPMF μ) {k : ℕ}
    {f : ∀ i, A i → A (i + 1) → ℝ}
    (h : ∀ x : ∀ i, A i, (∀ i ∈ Ico 1 (k + 2), 0 < dist μ (X i) (x i)) →
      blockDist μ X (range (k + 3)) x = ∏ i ∈ range (k + 2), f i (x i) (x (i + 1))) :
    MarkovChain μ (blockRV X (range (k + 1))) (X (k + 1)) (X (k + 2)) := by
  classical
  have : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite (A i)
  obtain ⟨ω₀⟩ := exists_of_isPMF hμ
  rw [markovChain_iff_condIndep hμ, condIndep_iff_factorization hμ]
  -- the factor of the first `k + 2` variables, which vanishes off the positive points
  let G : (∀ i, A i) → ℝ := fun x => if ∀ i ∈ Ico 1 (k + 1), 0 < dist μ (X i) (x i) then
    ∏ i ∈ range (k + 1), f i (x i) (x (i + 1)) else 0
  refine ⟨fun u y => G (chainPoint X ω₀ (k + 1) u y), fun y z => f (k + 1) y z,
    fun u y z hy => ?_⟩
  set x₀ := chainPoint X ω₀ (k + 1) u y with hx₀
  set x := Function.update x₀ (k + 2) z with hx
  have hlow : ∀ i, i ≠ k + 2 → x i = x₀ i := fun i hi => Function.update_of_ne hi _ _
  have hu : (fun i : range (k + 1) => x i) = u := by
    funext i
    have : (i : ℕ) ≠ k + 2 := by have := mem_range.1 i.2; omega
    rw [hlow _ this]
    exact congrFun (chainPoint_restrict ω₀ (k + 1) u y) i
  have hy' : x (k + 1) = y := by
    rw [hlow _ (by omega)]
    exact chainPoint_self ω₀ (k + 1) u y
  have hz : x (k + 2) = z := Function.update_self _ _ _
  have e : dist μ (pair (blockRV X (range (k + 1))) (pair (X (k + 1)) (X (k + 2)))) (u, y, z) =
      blockDist μ X (range (k + 3)) x := by
    rw [blockDist_succ_succ_eq (k + 1) x, hu, hy']
    rw [show x (k + 1 + 1) = z from hz]
  have hG : G x₀ = if ∀ i ∈ Ico 1 (k + 1), 0 < dist μ (X i) (x i) then
      ∏ i ∈ range (k + 1), f i (x i) (x (i + 1)) else 0 := by
    have e₁ : (∀ i ∈ Ico 1 (k + 1), 0 < dist μ (X i) (x₀ i)) ↔
        ∀ i ∈ Ico 1 (k + 1), 0 < dist μ (X i) (x i) := forall₂_congr fun i hi => by
      have := (mem_Ico.1 hi).2
      rw [hlow i (by omega)]
    have e₂ : ∀ i ∈ range (k + 1), f i (x₀ i) (x₀ (i + 1)) = f i (x i) (x (i + 1)) :=
      fun i hi => by
        have := mem_range.1 hi
        rw [hlow i (by omega), hlow (i + 1) (by omega)]
    simp only [G, e₁, prod_congr rfl e₂]
  rw [e]
  change _ = G x₀ * f (k + 1) y z
  rw [hG]
  split_ifs with hpos
  · have hpos' : ∀ i ∈ Ico 1 (k + 2), 0 < dist μ (X i) (x i) := by
      intro i hi
      have hi' := mem_Ico.1 hi
      rcases (by omega : i < k + 1 ∨ i = k + 1) with hlt | rfl
      · exact hpos i (mem_Ico.2 ⟨hi'.1, hlt⟩)
      · rw [hy']
        exact hy
    rw [h x hpos', prod_range_succ, hy']
    rw [show x (k + 1 + 1) = z from hz]
  · rw [zero_mul]
    push Not at hpos
    obtain ⟨i, hi, h0⟩ := hpos
    have hi' := (mem_Ico.1 hi).2
    exact blockDist_eq_zero hμ (mem_range.2 (by omega))
      (le_antisymm h0 (dist_nonneg hμ _ _))

/-- **Proposition 2.9.** `X₀ → X₁ → ⋯ → X_{n-1}` is a Markov chain iff
`p(x₀, …, x_{n-1}) = f₀(x₀, x₁) f₁(x₁, x₂) ⋯ f_{n-2}(x_{n-2}, x_{n-1})` for all `x` such that
`p(x₁), …, p(x_{n-2}) > 0`, for some functions `fᵢ`. -/
theorem isMarkovChain_iff_factorization [∀ i, Finite (A i)] (hμ : IsPMF μ) (X : ∀ i, Ω → A i)
    {n : ℕ} (hn : 2 ≤ n) :
    IsMarkovChain μ X n ↔ ∃ f : ∀ i, A i → A (i + 1) → ℝ, ∀ x : ∀ i, A i,
      (∀ i ∈ Ico 1 (n - 1), 0 < dist μ (X i) (x i)) →
        blockDist μ X (range n) x = ∏ i ∈ range (n - 1), f i (x i) (x (i + 1)) := by
  refine ⟨IsMarkovChain.exists_factorization hn, ?_⟩
  induction n, hn using Nat.le_induction with
  | base =>
    intro _
    exact (isMarkovChain_iff_forall_markovChain hμ X le_rfl).2 fun k hk => by omega
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rintro ⟨f, hf⟩
    rw [isMarkovChain_succ_iff hμ]
    exact ⟨ih (factorization_pred hμ hf), markovChain_last_of_factorization hμ hf⟩

end Factorization

section Entropy

variable {β γ β' γ' : Type*}

/-- Two random variables are functions of each other. -/
def RVEquiv (U : Ω → β) (V : Ω → γ) : Prop :=
  (∃ f : γ → β, ∀ ω, U ω = f (V ω)) ∧ ∃ g : β → γ, ∀ ω, V ω = g (U ω)

omit [Fintype Ω] in
lemma RVEquiv.refl (U : Ω → β) : RVEquiv U U :=
  ⟨⟨id, fun _ => rfl⟩, ⟨id, fun _ => rfl⟩⟩

omit [Fintype Ω] in
lemma RVEquiv.trans {U : Ω → β} {V : Ω → γ} {W : Ω → β'} (h₁ : RVEquiv U V) (h₂ : RVEquiv V W) :
    RVEquiv U W := by
  obtain ⟨⟨f₁, hf₁⟩, g₁, hg₁⟩ := h₁
  obtain ⟨⟨f₂, hf₂⟩, g₂, hg₂⟩ := h₂
  exact ⟨⟨f₁ ∘ f₂, fun ω => by simp [hf₁, hf₂]⟩, g₂ ∘ g₁, fun ω => by simp [← hg₁, ← hg₂]⟩

omit [Fintype Ω] in
lemma RVEquiv.pair {U : Ω → β} {V : Ω → γ} {U' : Ω → β'} {V' : Ω → γ'} (h₁ : RVEquiv U U')
    (h₂ : RVEquiv V V') : RVEquiv (pair U V) (pair U' V') := by
  obtain ⟨⟨f₁, hf₁⟩, g₁, hg₁⟩ := h₁
  obtain ⟨⟨f₂, hf₂⟩, g₂, hg₂⟩ := h₂
  exact ⟨⟨Prod.map f₁ f₂, fun ω => by simp [InfoTheory.pair, ← hf₁, ← hf₂]⟩,
    Prod.map g₁ g₂, fun ω => by simp [InfoTheory.pair, ← hg₁, ← hg₂]⟩

lemma RVEquiv.entropy_eq [Fintype β] [Fintype γ] {μ : Ω → ℝ} (hμ : IsPMF μ) {U : Ω → β}
    {V : Ω → γ} (h : RVEquiv U V) : H[U ; μ] = H[V ; μ] := by
  obtain ⟨⟨f, hf⟩, g, hg⟩ := h
  exact entropyRV_eq_of_comp hμ f g hf hg

omit [Fintype Ω] in
/-- `(X(S), X(T))` and `X(S ∪ T)` are functions of each other. -/
lemma rvEquiv_blockRV_union (X : ∀ i, Ω → A i) (S T : Finset ℕ) :
    RVEquiv (InfoTheory.pair (blockRV X S) (blockRV X T)) (blockRV X (S ∪ T)) := by
  refine ⟨⟨fun t => (fun i => t ⟨i, mem_union_left _ i.2⟩, fun i => t ⟨i, mem_union_right _ i.2⟩),
    fun ω => rfl⟩, ⟨fun p i => if h : (i : ℕ) ∈ S then p.1 ⟨i, h⟩ else
      p.2 ⟨i, (mem_union.1 i.2).resolve_left h⟩, fun ω => ?_⟩⟩
  funext i
  by_cases h : (i : ℕ) ∈ S <;> simp [blockRV, InfoTheory.pair, h]

omit [Fintype Ω] in
/-- `Xᵢ` and `X({i})` are functions of each other. -/
lemma rvEquiv_blockRV_singleton (X : ∀ i, Ω → A i) (i : ℕ) :
    RVEquiv (X i) (blockRV X {i}) := by
  refine ⟨⟨fun t => t ⟨i, mem_singleton_self i⟩, fun ω => rfl⟩,
    ⟨fun a j => (mem_singleton.1 j.2).symm ▸ a, fun ω => ?_⟩⟩
  funext j
  obtain ⟨j, hj⟩ := j
  obtain rfl := mem_singleton.1 hj
  rfl

variable [∀ i, Fintype (A i)]

/-- The entropy `H(X(s))` of the random vector `X(s) = (Xᵢ)_{i ∈ s}`. -/
def blockEntropy (μ : Ω → ℝ) (X : ∀ i, Ω → A i) (s : Finset ℕ) : ℝ := H[blockRV X s ; μ]

variable {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

/-- A conditional mutual information of blocks as a combination of entropies of index sets. -/
lemma condMutualInfo_eq_blockEntropy [Fintype β] [Fintype γ] [Fintype β'] (hμ : IsPMF μ)
    {U : Ω → β} {V : Ω → γ} {W : Ω → β'} {P F S : Finset ℕ} (hU : RVEquiv U (blockRV X P))
    (hV : RVEquiv V (blockRV X F)) (hW : RVEquiv W (blockRV X S)) :
    I[U : V | W ; μ] = blockEntropy μ X (S ∪ P) + blockEntropy μ X (S ∪ F) - blockEntropy μ X S -
      blockEntropy μ X (S ∪ (P ∪ F)) := by
  rw [condMutualInfo_eq hμ]
  have h₁ : RVEquiv (InfoTheory.pair U V) (blockRV X (P ∪ F)) :=
    (hU.pair hV).trans (rvEquiv_blockRV_union X P F)
  rw [((hW.pair hU).trans (rvEquiv_blockRV_union X S P)).entropy_eq hμ,
    ((hW.pair hV).trans (rvEquiv_blockRV_union X S F)).entropy_eq hμ, hW.entropy_eq hμ,
    ((hW.pair h₁).trans (rvEquiv_blockRV_union X S (P ∪ F))).entropy_eq hμ]
  rfl

/-- Entropies of index sets are monotone. -/
lemma blockEntropy_mono (hμ : IsPMF μ) {S T : Finset ℕ} (h : S ⊆ T) :
    blockEntropy μ X S ≤ blockEntropy μ X T :=
  entropyRV_comp_le hμ (blockRV X T) (fun t (i : S) => t ⟨i, h i.2⟩)

/-- Entropies of index sets are submodular. -/
lemma blockEntropy_submodular (hμ : IsPMF μ) (S T : Finset ℕ) :
    blockEntropy μ X (S ∪ T) + blockEntropy μ X (S ∩ T) ≤
      blockEntropy μ X S + blockEntropy μ X T := by
  have h := condMutualInfo_nonneg hμ (blockRV X (S \ T)) (blockRV X (T \ S)) (blockRV X (S ∩ T))
  rw [condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (RVEquiv.refl _) (RVEquiv.refl _)] at h
  have e₁ : S ∩ T ∪ S \ T = S := by rw [union_comm, sdiff_union_inter]
  have e₂ : S ∩ T ∪ T \ S = T := by rw [inter_comm, union_comm, sdiff_union_inter]
  have e₃ : S ∩ T ∪ (S \ T ∪ T \ S) = S ∪ T := by
    ext i
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  rw [e₁, e₂, e₃] at h
  linarith

/-- The information between two sets, without the common conditioning term, grows with the sets. -/
lemma blockEntropy_add_sub_mono (hμ : IsPMF μ) {S S' T T' : Finset ℕ} (hS : S ⊆ S') (hT : T ⊆ T') :
    blockEntropy μ X S + blockEntropy μ X T - blockEntropy μ X (S ∪ T) ≤
      blockEntropy μ X S' + blockEntropy μ X T' - blockEntropy μ X (S' ∪ T') := by
  have h₁ := blockEntropy_submodular (μ := μ) (X := X) hμ S' (S ∪ T)
  have h₂ : blockEntropy μ X S ≤ blockEntropy μ X (S' ∩ (S ∪ T)) :=
    blockEntropy_mono hμ (subset_inter hS subset_union_left)
  have e₁ : S' ∪ (S ∪ T) = S' ∪ T := by
    rw [← union_assoc, union_eq_left.2 hS]
  rw [e₁] at h₁
  have h₃ := blockEntropy_submodular (μ := μ) (X := X) hμ T' (S' ∪ T)
  have h₄ : blockEntropy μ X T ≤ blockEntropy μ X (T' ∩ (S' ∪ T)) :=
    blockEntropy_mono hμ (subset_inter hT subset_union_right)
  have e₂ : T' ∪ (S' ∪ T) = S' ∪ T' := by
    rw [union_comm S' T, ← union_assoc, union_eq_left.2 hT, union_comm]
  rw [e₂] at h₃
  linarith

/-- The three-variable chains of a Markov chain in terms of entropies of index sets. -/
lemma IsMarkovChain.blockEntropy_step (hμ : IsPMF μ) {n : ℕ} (hn : 2 ≤ n)
    (h : IsMarkovChain μ X n) {c : ℕ} (hc₁ : 2 ≤ c) (hc₂ : c < n) :
    blockEntropy μ X (range c) + blockEntropy μ X {c - 1, c} - blockEntropy μ X {c - 1} -
      blockEntropy μ X (range (c + 1)) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
  have hm := (isMarkovChain_iff_forall_markovChain hμ X hn).1 h k hc₂
  rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ,
    condMutualInfo_eq_blockEntropy hμ (P := range (k + 1)) (F := {k + 2}) (S := {k + 1})
      (RVEquiv.refl _) (rvEquiv_blockRV_singleton X _) (rvEquiv_blockRV_singleton X _)] at hm
  have e₁ : ({k + 1} : Finset ℕ) ∪ range (k + 1) = range (k + 2) := by
    ext i; simp only [mem_union, mem_singleton, mem_range]; omega
  have e₂ : ({k + 1} : Finset ℕ) ∪ {k + 2} = {k + 2 - 1, k + 2} := by
    ext i; simp only [mem_union, mem_singleton, mem_insert]; omega
  have e₃ : ({k + 1} : Finset ℕ) ∪ (range (k + 1) ∪ {k + 2}) = range (k + 2 + 1) := by
    ext i; simp only [mem_union, mem_singleton, mem_range]; omega
  rw [e₁, e₂, e₃] at hm
  simpa using hm

/-- Given `X_b`, the variables before `b` are independent of the variables from `b` to `c`. -/
lemma IsMarkovChain.blockEntropy_Ico (hμ : IsPMF μ) {n : ℕ} (hn : 2 ≤ n)
    (h : IsMarkovChain μ X n) {b c : ℕ} (hbc : b < c) (hc : c ≤ n) :
    blockEntropy μ X (range (b + 1)) + blockEntropy μ X (Ico b c) - blockEntropy μ X {b} -
      blockEntropy μ X (range c) = 0 := by
  induction c, hbc using Nat.le_induction with
  | base =>
    have : Ico b (b + 1) = {b} := by ext i; simp only [mem_Ico, mem_singleton]; omega
    rw [this]
    ring
  | succ c hbc ih =>
    have ih' := ih (by omega)
    have hsub₁ := blockEntropy_submodular (μ := μ) (X := X) hμ (range c) (Ico b (c + 1))
    have e₁ : range c ∪ Ico b (c + 1) = range (c + 1) := by
      ext i; simp only [mem_union, mem_range, mem_Ico]; omega
    have e₂ : range c ∩ Ico b (c + 1) = Ico b c := by
      ext i; simp only [mem_inter, mem_range, mem_Ico]; omega
    rw [e₁, e₂] at hsub₁
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · -- then `b = 0`, and both sets are the same
      obtain rfl : b = 0 := by omega
      have e₃ : ∀ d, Ico 0 d = range d := fun d => by
        ext i; simp only [mem_Ico, mem_range]; omega
      rw [e₃] at ih' ⊢
      rw [e₃] at hsub₁
      have hc1 : c = 1 := by omega
      subst hc1
      simp only [zero_add] at ih' ⊢
      linarith
    · have hstep := h.blockEntropy_step hμ hn hc2 (by omega)
      have hsub₂ := blockEntropy_submodular (μ := μ) (X := X) hμ (Ico b c) {c - 1, c}
      have e₃ : Ico b c ∪ {c - 1, c} = Ico b (c + 1) := by
        ext i; simp only [mem_union, mem_Ico, mem_insert, mem_singleton]; omega
      have e₄ : Ico b c ∩ {c - 1, c} = {c - 1} := by
        ext i; simp only [mem_inter, mem_Ico, mem_insert, mem_singleton]; omega
      rw [e₃, e₄] at hsub₂
      linarith

omit [∀ i, Fintype (A i)] in
/-- **Global Markov property.** Let `b ∈ S`, let the indices of `P` be less than `b`, and let
those of `S` and `F` be between `b` and `n`. Then `X(P) ⊥ X(F) | X(S)`. -/
theorem IsMarkovChain.markovChain_block [∀ i, Finite (A i)] (hμ : IsPMF μ) {n : ℕ} (hn : 2 ≤ n)
    (h : IsMarkovChain μ X n) {P S F : Finset ℕ} {b : ℕ} (hb : b ∈ S)
    (hP : ∀ i ∈ P, i < b) (hS : ∀ i ∈ S, b ≤ i ∧ i < n) (hF : ∀ i ∈ F, b ≤ i ∧ i < n) :
    MarkovChain μ (blockRV X P) (blockRV X S) (blockRV X F) := by
  have : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite (A i)
  rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ]
  refine le_antisymm ?_ (condMutualInfo_nonneg hμ _ _ _)
  rw [condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (RVEquiv.refl _) (RVEquiv.refl _)]
  have hbn : b < n := (hS b hb).2
  have hIco := h.blockEntropy_Ico hμ hn hbn le_rfl
  have hmono := blockEntropy_add_sub_mono (μ := μ) (X := X) hμ
    (S := {b} ∪ P) (S' := range (b + 1)) (T := S ∪ F) (T' := Ico b n)
    (fun i hi => by
      rcases mem_union.1 hi with hi | hi
      · rw [mem_singleton.1 hi]; exact mem_range.2 (by omega)
      · exact mem_range.2 (by have := hP i hi; omega))
    (fun i hi => by
      rcases mem_union.1 hi with hi | hi
      · exact mem_Ico.2 (hS i hi)
      · exact mem_Ico.2 (hF i hi))
  have e₁ : range (b + 1) ∪ Ico b n = range n := by
    ext i; simp only [mem_union, mem_range, mem_Ico]; omega
  rw [e₁] at hmono
  have hsub := blockEntropy_submodular (μ := μ) (X := X) hμ ({b} ∪ P) S
  have hinter : blockEntropy μ X {b} ≤ blockEntropy μ X (({b} ∪ P) ∩ S) :=
    blockEntropy_mono hμ fun i hi => by
      rw [mem_singleton.1 hi]
      exact mem_inter.2 ⟨mem_union_left _ (mem_singleton_self b), hb⟩
  have e₂ : {b} ∪ P ∪ S = S ∪ P := by
    ext i
    simp only [mem_union, mem_singleton]
    constructor
    · rintro ((rfl | h') | h')
      · exact Or.inl hb
      · exact Or.inr h'
      · exact Or.inl h'
    · rintro (h' | h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
  rw [e₂] at hsub
  have e₃ : {b} ∪ P ∪ (S ∪ F) = S ∪ (P ∪ F) := by
    ext i
    simp only [mem_union, mem_singleton]
    constructor
    · rintro ((rfl | h') | (h' | h'))
      · exact Or.inl hb
      · exact Or.inr (Or.inl h')
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rintro (h' | h' | h')
      · exact Or.inr (Or.inl h')
      · exact Or.inl (Or.inr h')
      · exact Or.inr (Or.inr h')
  rw [e₃] at hmono
  linarith

omit [∀ i, Fintype (A i)] [Fintype Ω] in
/-- A tuple of blocks and the block of their union are functions of each other. -/
lemma rvEquiv_blockRV_biUnion (X : ∀ i, Ω → A i) (α : ℕ → Finset ℕ) (t : Finset ℕ) :
    RVEquiv (blockRV (fun j => blockRV X (α j)) t) (blockRV X (t.biUnion α)) := by
  classical
  have hmem : ∀ i : t.biUnion α, ∃ j, j ∈ t ∧ (i : ℕ) ∈ α j := fun i => mem_biUnion.1 i.2
  choose J hJ₁ hJ₂ using hmem
  refine ⟨⟨fun v j i => v ⟨i, mem_biUnion.2 ⟨j, j.2, i.2⟩⟩, fun ω => rfl⟩,
    ⟨fun v i => v ⟨J i, hJ₁ i⟩ ⟨i, hJ₂ i⟩, fun ω => rfl⟩⟩

omit [∀ i, Fintype (A i)] in
/-- **Proposition 2.10 (Markov subchains).** Let `X₀ → ⋯ → X_{n-1}` be a Markov chain, and let
`α₀, …, α_{m-1}` be subsets of its indices such that the indices of `αⱼ` are less than those of
`αⱼ'` if `j < j'`. Then `X(α₀) → ⋯ → X(α_{m-1})` is a Markov chain.

The sets `αⱼ` with `0 < j < m - 1` have to be nonempty, which the book leaves implicit: conditioning
on an empty block is not conditioning at all. -/
theorem IsMarkovChain.block [∀ i, Finite (A i)] (hμ : IsPMF μ) {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : IsMarkovChain μ X n) (α : ℕ → Finset ℕ) (hα : ∀ j, j < m → ∀ i ∈ α j, i < n)
    (hne : ∀ j, 0 < j → j + 1 < m → (α j).Nonempty)
    (hord : ∀ j j', j < j' → j' < m → ∀ i ∈ α j, ∀ i' ∈ α j', i < i') :
    IsMarkovChain μ (fun j => blockRV X (α j)) m := by
  have : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite (A i)
  rw [isMarkovChain_iff_forall_markovChain hμ _ hm]
  intro k hk
  rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ]
  have hne' := hne (k + 1) (by omega) (by omega)
  set b := (α (k + 1)).min' hne' with hb
  have hbmem : b ∈ α (k + 1) := min'_mem _ _
  have hm' := h.markovChain_block hμ hn (P := (range (k + 1)).biUnion α) (S := α (k + 1))
    (F := α (k + 2)) hbmem
    (fun i hi => by
      obtain ⟨j, hj, hi⟩ := mem_biUnion.1 hi
      exact hord j (k + 1) (by have := mem_range.1 hj; omega) (by omega) i hi b hbmem)
    (fun i hi => ⟨min'_le _ _ hi, hα _ (by omega) i hi⟩)
    (fun i hi => ⟨(hord (k + 1) (k + 2) (by omega) (by omega) b hbmem i hi).le,
      hα _ (by omega) i hi⟩)
  rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ,
    condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (RVEquiv.refl _) (RVEquiv.refl _)] at hm'
  rw [condMutualInfo_eq_blockEntropy hμ (rvEquiv_blockRV_biUnion X α _) (RVEquiv.refl _)
    (RVEquiv.refl _)]
  exact hm'

/-- **Theorem 2.42 (Data Processing Theorem).** If `U → X → Y → V` is a Markov chain, then
`I(U; V) ≤ I(X; Y)`, for four variables `Xᵢ`, `Xⱼ`, `X_k`, `X_l` of a chain in this order. -/
theorem IsMarkovChain.data_processing (hμ : IsPMF μ) {n : ℕ} (hn : 2 ≤ n)
    (h : IsMarkovChain μ X n) {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hl : l < n) : I[X i : X l ; μ] ≤ I[X j : X k ; μ] := by
  -- a three-variable chain of single variables from a chain
  have key : ∀ {a b c : ℕ}, a < b → b < c → c < n → MarkovChain μ (X a) (X b) (X c) := by
    intro a b c hab hbc hc
    have hm := h.markovChain_block hμ hn (P := {a}) (S := {b}) (F := {c}) (mem_singleton_self b)
      (fun i hi => by rw [mem_singleton.1 hi]; exact hab)
      (fun i hi => by rw [mem_singleton.1 hi]; omega)
      (fun i hi => by rw [mem_singleton.1 hi]; omega)
    rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ,
      condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (RVEquiv.refl _) (RVEquiv.refl _)] at hm
    rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ,
      condMutualInfo_eq_blockEntropy hμ (rvEquiv_blockRV_singleton X a)
        (rvEquiv_blockRV_singleton X c) (rvEquiv_blockRV_singleton X b)]
    exact hm
  calc I[X i : X l ; μ] ≤ I[X i : X k ; μ] :=
        InfoTheory.data_processing hμ (key (hij.trans hjk) hkl hl)
    _ ≤ I[X j : X k ; μ] := data_processing' hμ (key hij hjk (by omega))

end Entropy

end InfoTheory
