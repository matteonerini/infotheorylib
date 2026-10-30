/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.ShannonFanoElias
public import InfoTheoryLib.AEP.Basic

/-!
# Shannon–Fano–Elias coding of sequences

The Shannon–Fano–Elias code can be applied to blocks `xⁿ = x₁ ⋯ xₙ` of source symbols, ordered
lexicographically: the code of `xⁿ` is given by the cumulative distribution function `F(xⁿ)` of
the sequence, to the appropriate accuracy. The strings below `xⁿ` are the leaves of the subtrees
of the tree of strings lying to the left of the path to `xⁿ`. For i.i.d. (or Markov) sources the
probabilities of these subtrees are products, so `p(xⁿ)` and `F(xⁿ)` can be computed sequentially,
as each symbol of the block is seen, with a cost linear in `n`.

We work with a general finite linearly ordered source alphabet `α`. Strings are `Fin n → α`, and
`Lex (Fin n → α)` carries the lexicographic order: `y < x` iff `yᵢ < xᵢ` at the first index
where they differ.

## Main definitions

* `leftSubtreeProb p x k`: the probability of the strings that agree with `x` before index `k`
  and are smaller than `x` at index `k`, the subtrees to the left of `x` hanging at depth `k`.
* `blockSfeCode p`: the Shannon–Fano–Elias code for blocks in lexicographic order.

## Main statements

* `cdfLT_lex`, `cdf_lex`: `F(xⁿ)` is a sum of subtree probabilities.
* `iidPMF_snoc`: sequential computation of `p(xⁿ⁺¹)` for i.i.d. sources (for Markov sources, see
  `InfoTheory.markovLaw_snoc`).
* `leftSubtreeProb_iid`, `cdfLT_lex_iid`: for i.i.d. sources the subtree probabilities are
  products, `p(T_{x₁ ⋯ x_{k-1} b}) = p(x₁) ⋯ p(x_{k-1}) p(b)`, so `F(xⁿ)` is computed sequentially.
* `blockSfeCode_isPrefixCode`, `expectedLength_blockSfeCode_lt`: a prefix code for blocks with
  `L < H(Xⁿ) + 2` bits.
* `expectedLength_blockSfeCode_iid_lt`: for i.i.d. sources, the expected length per symbol is
  less than `H(X) + 2/n` bits.

## Implementation notes

The code uses exact real arithmetic, whose precision grows with the block length. Arithmetic
coding, the extension with fixed-precision arithmetic that the book describes in Section 13.3, is
not formalized.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 5.9
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

/-! ### The cumulative distribution function in the tree of strings -/

/-- The probability of the subtrees to the left of the string `x` hanging at depth `k`: the
strings `y` with `y₁ ⋯ y_{k-1} = x₁ ⋯ x_{k-1}` and `y_k < x_k`. In the binary case it is the
probability `p(T_{x₁ ⋯ x_{k-1} 0})` of a single subtree when `x_k = 1`, and `0` otherwise. -/
def leftSubtreeProb (p : (Fin n → α) → ℝ) (x : Fin n → α) (k : Fin n) : ℝ :=
  ∑ y ∈ univ.filter (fun y : Fin n → α => (∀ i < k, y i = x i) ∧ y k < x k), p y

/-- The sum of the probabilities of the strings below `xⁿ` is the sum of the probabilities of the
subtrees to the left of `xⁿ`. -/
theorem cdfLT_lex (p : (Fin n → α) → ℝ) (x : Fin n → α) :
    cdfLT (p ∘ ofLex) (toLex x) = ∑ k, leftSubtreeProb p x k := by
  simp only [leftSubtreeProb]
  rw [cdfLT, ← sum_biUnion]
  · refine sum_equiv ofLex (fun a => ?_) fun _ _ => rfl
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
    exact Iff.rfl
  · intro k _ k' _ hkk'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    simp only [mem_filter, mem_univ, true_and] at hy hy'
    rcases lt_or_gt_of_ne hkk' with h | h
    · rw [hy'.1 k h] at hy
      exact lt_irrefl _ hy.2
    · rw [hy.1 k' h] at hy'
      exact lt_irrefl _ hy'.2

/-- `F(xⁿ) = ∑_{yⁿ ≤ xⁿ} p(yⁿ) = ∑_{T to the left of xⁿ} p(T) + p(xⁿ)`. -/
theorem cdf_lex (p : (Fin n → α) → ℝ) (x : Fin n → α) :
    cdf (p ∘ ofLex) (toLex x) = ∑ k, leftSubtreeProb p x k + p x := by
  rw [cdf_eq_cdfLT_add, cdfLT_lex]
  rfl

/-! ### i.i.d. sources -/

omit [Fintype α] [LinearOrder α] in
/-- For an i.i.d. source, `p(xⁿ xₙ₊₁) = p(xⁿ) p(xₙ₊₁)`: the probability of a block is computed
sequentially. -/
lemma iidPMF_snoc (q : α → ℝ) (x : Fin n → α) (a : α) :
    iidPMF q (n + 1) (Fin.snoc x a) = iidPMF q n x * q a := by
  simp [iidPMF, Fin.prod_univ_castSucc]

/-- For an i.i.d. source, the probability of the subtrees to the left of `x` at depth `k` is
`p(x₁) ⋯ p(x_{k-1}) ∑_{b < x_k} p(b)`. -/
theorem leftSubtreeProb_iid {q : α → ℝ} (hq : IsPMF q) (x : Fin n → α) (k : Fin n) :
    leftSubtreeProb (iidPMF q n) x k =
      (∏ i ∈ univ.filter (· < k), q (x i)) * ∑ b ∈ univ.filter (· < x k), q b := by
  classical
  -- The indicator of the subtrees is a product of indicators of the coordinates.
  set φ : Fin n → α → ℝ := fun i a => if (i < k → a = x i) ∧ (i = k → a < x k) then 1 else 0
  have hind : ∀ y : Fin n → α, (∏ i, φ i (y i)) =
      if (∀ i < k, y i = x i) ∧ y k < x k then 1 else 0 := by
    intro y
    rw [prod_boole]
    congr 1
    apply propext
    simp only [mem_univ, true_imp_iff]
    constructor
    · intro h
      exact ⟨fun i hi => (h i).1 hi, (h k).2 rfl⟩
    · rintro ⟨h1, h2⟩ i
      exact ⟨h1 i, fun hi => hi ▸ h2⟩
  have h1 : leftSubtreeProb (iidPMF q n) x k = ∑ y, iidPMF q n y * ∏ i, φ i (y i) := by
    simp only [leftSubtreeProb, hind, mul_ite, mul_one, mul_zero, sum_ite, sum_const_zero,
      add_zero]
  rw [h1, sum_iidPMF_mul_prod]
  -- Evaluate the factors.
  have h2 : ∀ i, ∑ a, q a * φ i a =
      if i < k then q (x i) else if i = k then ∑ b ∈ univ.filter (· < x k), q b else 1 := by
    intro i
    simp only [φ, mul_ite, mul_one, mul_zero]
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h, h.ne]
    · simp [sum_filter]
    · simp [h.ne', not_lt_of_gt h, hq.sum_eq_one]
  simp only [h2]
  rw [prod_ite, prod_ite_eq_of_mem']
  simp

/-- For an i.i.d. source, `F(xⁿ⁻) = ∑ₖ p(x₁) ⋯ p(x_{k-1}) ∑_{b < x_k} p(b)`: the cumulative
distribution function of a block is computed sequentially. -/
theorem cdfLT_lex_iid {q : α → ℝ} (hq : IsPMF q) (x : Fin n → α) :
    cdfLT (iidPMF q n ∘ ofLex) (toLex x) =
      ∑ k, (∏ i ∈ univ.filter (· < k), q (x i)) * ∑ b ∈ univ.filter (· < x k), q b := by
  rw [cdfLT_lex]
  exact sum_congr rfl fun k _ => leftSubtreeProb_iid hq x k

/-! ### The Shannon–Fano–Elias code of a block -/

omit [LinearOrder α] in
lemma isPMF_comp_ofLex {p : (Fin n → α) → ℝ} (hp : IsPMF p) : IsPMF (p ∘ ofLex) :=
  ⟨fun _ => hp.nonneg _, by rw [← hp.sum_eq_one]; exact Equiv.sum_comp ofLex p⟩

/-- **Section 5.9.** The Shannon–Fano–Elias code of the block `xⁿ`, with the strings ordered
lexicographically: the first `⌈log (1/p(xⁿ))⌉ + 1` bits of `F̄(xⁿ)`. -/
def blockSfeCode (p : (Fin n → α) → ℝ) (x : Fin n → α) : List (Fin 2) :=
  sfeCode (p ∘ ofLex) (toLex x)

/-- The Shannon–Fano–Elias code of blocks is a prefix code. -/
theorem blockSfeCode_isPrefixCode {p : (Fin n → α) → ℝ} (hp : IsPMF p) (hpos : ∀ x, 0 < p x) :
    IsPrefixCode (blockSfeCode p) := fun _ _ h =>
  toLex.injective (sfeCode_isPrefixCode (isPMF_comp_ofLex hp) (fun _ => hpos _) _ _ h)

/-- The Shannon–Fano–Elias code of blocks has expected length `L < H(Xⁿ) + 2` bits. -/
theorem expectedLength_blockSfeCode_lt {p : (Fin n → α) → ℝ} (hp : IsPMF p)
    (hpos : ∀ x, 0 < p x) : expectedLength p (blockSfeCode p) < entropyBase 2 p + 2 := by
  have h := expectedLength_sfeCode_lt (isPMF_comp_ofLex hp) (fun _ => hpos _)
  have e1 : expectedLength (p ∘ ofLex) (sfeCode (p ∘ ofLex)) =
      expectedLength p (blockSfeCode p) :=
    Equiv.sum_comp ofLex fun x => p x * (blockSfeCode p x).length
  have e2 : entropyBase 2 (p ∘ ofLex) = entropyBase 2 p :=
    congrArg Neg.neg (Equiv.sum_comp ofLex fun x => p x * logb 2 (p x))
  rwa [e1, e2] at h

/-- For an i.i.d. source, the Shannon–Fano–Elias code of blocks of length `n` has expected length
per symbol less than `H(X) + 2/n` bits: it approaches the entropy as the block length grows. -/
theorem expectedLength_blockSfeCode_iid_lt {q : α → ℝ} (hq : IsPMF q) (hpos : ∀ a, 0 < q a)
    (hn : 0 < n) :
    expectedLength (iidPMF q n) (blockSfeCode (iidPMF q n)) / n < entropyBase 2 q + 2 / n := by
  have h := expectedLength_blockSfeCode_lt (iidPMF_isPMF hq n)
    (fun x => prod_pos fun i _ => hpos (x i))
  have hH : entropyBase 2 (iidPMF q n) = n * entropyBase 2 q := by
    rw [entropyBase_eq_div, entropyBase_eq_div, entropy_iidPMF hq, mul_div_assoc]
  rw [hH] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
  linarith

end InfoTheory
