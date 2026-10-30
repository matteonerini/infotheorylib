/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.Competitive
public import InfoTheoryLib.SourceCoding.ShannonFanoElias

/-!
# Generation of discrete distributions from fair coins

How many fair coin flips does it take to generate a random variable `X` with distribution `p`?
An algorithm mapping coin flips to outputs is described by a binary tree. The leaves are labeled
by output symbols, and the path to a leaf is the sequence of flips that leads to it. A leaf at
depth `k` is reached with probability `2^{-k}`. The expected number `ET` of flips is the expected
depth of the tree. Then `H(X) ≤ ET` for every algorithm. Equality is achievable iff `p` is dyadic.
In general the binary expansions of the probabilities give an algorithm with `ET < H(X) + 2`.

Entropies are in bits.

## Main definitions

* `CoinTree X`: a generating algorithm, as a prefix-free set of binary words (the leaves of a
  possibly infinite tree) labeled by symbols of `X`, reached with total probability one.
* `CoinTree.outProb`, `CoinTree.Generates`: the distribution of the output.
* `CoinTree.expectedFlips`: the expected number `ET` of coin flips, the expected depth.
* `CoinTree.ofCode`: the tree whose leaves are the codewords of a binary prefix code.
* `binDigit t j`: the `j`-th binary digit of `t`, and `atomFlips t = ∑ⱼ j tⱼ 2^{-j}`.
* `minExpectedFlips p`: the expected number of flips of an optimal algorithm.

## Main statements

* `CoinTree.leafEntropy_eq_expectedFlips`: Lemma 5.11.1, the entropy of the distribution on the
  leaves is the expected depth.
* `CoinTree.entropyBase_le_expectedFlips`: Theorem 5.11.1, `ET ≥ H(X)`.
* `exists_generates_expectedFlips_eq_of_isDAdic`, `minExpectedFlips_eq_of_isDAdic`:
  Theorem 5.11.2, for a dyadic distribution the optimal algorithm has `ET = H(X)`.
* `hasSum_binDigit`, `atomFlips_lt`: the binary expansion `p = ∑ⱼ pⱼ 2^{-j}` and the bound
  `Tᵢ < -pᵢ log pᵢ + 2pᵢ` (5.134).
* `exists_generates_expectedFlips_lt`, `minExpectedFlips_bounds`: Theorem 5.11.3,
  `H(X) ≤ ET < H(X) + 2` for the optimal algorithm.

## Implementation notes

The proof of the lower bound avoids the entropy of the (possibly infinite) distribution on the
leaves: each leaf labeled `x` has probability at most `p(x)`, so its depth is at least
`log (1/p(x))`. The tree is complete in the sense that the algorithm stops with probability one.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 5.11
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Generating trees -/

/-- An algorithm generating a random variable with values in `X` from fair coin flips, described by
its binary tree: the leaves are a prefix-free set of binary words (the paths from the root), each
labeled by an output symbol. A leaf at depth `k` is reached with probability `2^{-k}`, and the
algorithm stops with probability one: `∑_{leaves} 2^{-k} = 1`. The tree may be infinite. -/
structure CoinTree (X : Type*) where
  /-- The leaves of the tree, as binary words. -/
  leaves : Set (List Bool)
  isPrefixFree : InformationTheory.IsPrefixFree leaves
  /-- The output symbol of each leaf. -/
  label : leaves → X
  hasSum_one : HasSum (fun w : leaves => (1 / 2 : ℝ) ^ (w : List Bool).length) 1

namespace CoinTree

variable {X : Type*} (T : CoinTree X)

open Classical in
/-- The probability that the algorithm outputs `x`: the total probability of the leaves labeled
`x`. -/
def outProb (x : X) : ℝ :=
  ∑' w : T.leaves, if T.label w = x then (1 / 2 : ℝ) ^ (w : List Bool).length else 0

/-- The algorithm generates the distribution `p`. -/
def Generates (p : X → ℝ) : Prop := ∀ x, T.outProb x = p x

/-- The expected number `ET` of fair coin flips, the expected depth of the tree. -/
def expectedFlips : ℝ :=
  ∑' w : T.leaves, ((w : List Bool).length : ℝ) * (1 / 2 : ℝ) ^ (w : List Bool).length

/-- The expected number of coin flips is finite. -/
def FiniteFlips : Prop :=
  Summable fun w : T.leaves => ((w : List Bool).length : ℝ) * (1 / 2 : ℝ) ^ (w : List Bool).length

/-- **Lemma 5.11.1, (5.99)–(5.102).** For the distribution on the leaves in which a leaf at depth
`k` has probability `2^{-k}`, the entropy is the expected depth of the tree. -/
theorem leafEntropy_eq_expectedFlips :
    ∑' w : T.leaves, -((1 / 2 : ℝ) ^ (w : List Bool).length *
      logb 2 ((1 / 2 : ℝ) ^ (w : List Bool).length)) = T.expectedFlips := by
  refine tsum_congr fun w => ?_
  rw [logb_pow, one_div, logb_inv, logb_self_eq_one one_lt_two]
  ring

open Classical in
lemma summable_ite (x : X) :
    Summable fun w : T.leaves =>
      if T.label w = x then (1 / 2 : ℝ) ^ (w : List Bool).length else 0 :=
  Summable.of_nonneg_of_le (fun w => by split_ifs <;> positivity)
    (fun w => by split_ifs; exacts [le_rfl, by positivity]) T.hasSum_one.summable

lemma outProb_nonneg (x : X) : 0 ≤ T.outProb x := by
  classical
  exact tsum_nonneg fun w => by split_ifs <;> positivity

/-- A leaf has probability at most that of its label. -/
lemma leafProb_le_outProb (w : T.leaves) :
    (1 / 2 : ℝ) ^ (w : List Bool).length ≤ T.outProb (T.label w) := by
  classical
  have := (T.summable_ite (T.label w)).le_tsum w fun j _ => by split_ifs <;> positivity
  simpa [outProb] using this

variable {T}

/-- **Theorem 5.11.1, (5.103).** Any algorithm generating `X` from fair bits uses an expected number
of bits at least the entropy: `ET ≥ H(X)`. -/
theorem entropyBase_le_expectedFlips [Fintype X] {p : X → ℝ} (hT : T.Generates p)
    (hf : T.FiniteFlips) : entropyBase 2 p ≤ T.expectedFlips := by
  classical
  have hs2 : ∀ x, Summable fun w : T.leaves =>
      if T.label w = x then ((w : List Bool).length : ℝ) * (1 / 2 : ℝ) ^ (w : List Bool).length
      else 0 := fun x =>
    Summable.of_nonneg_of_le (fun w => by split_ifs <;> positivity)
      (fun w => by split_ifs; exacts [le_rfl, by positivity]) hf
  -- Each `x` contributes `p(x) log (1/p(x)) ≤ ∑_{leaves labeled x} k 2^{-k}`.
  have hle : ∀ x, p x * logb 2 (1 / p x) ≤ ∑' w : T.leaves,
      if T.label w = x then ((w : List Bool).length : ℝ) * (1 / 2 : ℝ) ^ (w : List Bool).length
      else 0 := by
    intro x
    rcases (hT x ▸ T.outProb_nonneg x).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]
      exact tsum_nonneg fun w => by split_ifs <;> positivity
    · have h2 : ∀ w : T.leaves, T.label w = x → logb 2 (1 / p x) ≤ (w : List Bool).length := by
        intro w hw
        have h1 : (1 / 2 : ℝ) ^ (w : List Bool).length ≤ p x := by
          rw [← hT x, ← hw]
          exact T.leafProb_le_outProb w
        rw [logb_le_iff_le_rpow one_lt_two (by positivity), rpow_natCast,
          one_div_le h0 (by positivity), ← one_div_pow]
        exact h1
      generalize logb 2 (1 / p x) = L at h2 ⊢
      rw [← hT x, outProb, ← tsum_mul_right]
      refine Summable.tsum_le_tsum (fun w => ?_) ((T.summable_ite x).mul_right _) (hs2 x)
      split_ifs with hw
      · rw [mul_comm ((w : List Bool).length : ℝ)]
        exact mul_le_mul_of_nonneg_left (h2 w hw) (by positivity)
      · simp
  have hH := sum_mul_logb_inv_eq_entropyBase p 2
  push_cast at hH
  rw [← hH]
  calc ∑ x, p x * logb 2 (1 / p x)
      ≤ ∑ x, ∑' w : T.leaves, if T.label w = x then
          ((w : List Bool).length : ℝ) * (1 / 2 : ℝ) ^ (w : List Bool).length else 0 :=
        sum_le_sum fun x _ => hle x
    _ = ∑' w : T.leaves, ∑ x, if T.label w = x then
          ((w : List Bool).length : ℝ) * (1 / 2 : ℝ) ^ (w : List Bool).length else 0 :=
        (Summable.tsum_finsetSum fun x _ => hs2 x).symm
    _ = T.expectedFlips := tsum_congr fun w => by simp

/-! ### Trees from prefix codes -/

variable {ι : Type*}

/-- The tree whose leaves are the codewords of a binary prefix code `c`, the leaf `c i` labeled
`g i`. -/
def ofCode (c : ι → List Bool) (hc : IsPrefixCode c) (g : ι → X)
    (h : HasSum (fun i => (1 / 2 : ℝ) ^ (c i).length) 1) : CoinTree X where
  leaves := Set.range c
  isPrefixFree := (isPrefixCode_iff.1 hc).2
  label w := g ((Equiv.ofInjective c hc.injective).symm w)
  hasSum_one := (Equiv.ofInjective c hc.injective).hasSum_iff.1 (by
    simpa [Function.comp_def] using h)

variable (c : ι → List Bool) (hc : IsPrefixCode c) (g : ι → X)
  (h : HasSum (fun i => (1 / 2 : ℝ) ^ (c i).length) 1)

lemma tsum_ofCode (F : List Bool → X → ℝ) :
    ∑' w : (ofCode c hc g h).leaves, F w ((ofCode c hc g h).label w) = ∑' i, F (c i) (g i) := by
  change ∑' w : Set.range c, F w (g ((Equiv.ofInjective c hc.injective).symm w)) = _
  rw [← (Equiv.ofInjective c hc.injective).tsum_eq]
  simp

lemma summable_ofCode_iff (F : List Bool → X → ℝ) :
    (Summable fun w : (ofCode c hc g h).leaves => F w ((ofCode c hc g h).label w)) ↔
      Summable fun i => F (c i) (g i) := by
  change (Summable fun w : Set.range c => F w (g ((Equiv.ofInjective c hc.injective).symm w))) ↔ _
  rw [← (Equiv.ofInjective c hc.injective).summable_iff]
  simp [Function.comp_def]

open Classical in
lemma outProb_ofCode (x : X) :
    (ofCode c hc g h).outProb x = ∑' i, if g i = x then (1 / 2 : ℝ) ^ (c i).length else 0 :=
  tsum_ofCode c hc g h fun w y => if y = x then (1 / 2 : ℝ) ^ w.length else 0

lemma expectedFlips_ofCode :
    (ofCode c hc g h).expectedFlips = ∑' i, ((c i).length : ℝ) * (1 / 2 : ℝ) ^ (c i).length :=
  tsum_ofCode c hc g h fun w _ => (w.length : ℝ) * (1 / 2 : ℝ) ^ w.length

lemma finiteFlips_ofCode_iff :
    (ofCode c hc g h).FiniteFlips ↔
      Summable fun i => ((c i).length : ℝ) * (1 / 2 : ℝ) ^ (c i).length :=
  summable_ofCode_iff c hc g h fun w _ => (w.length : ℝ) * (1 / 2 : ℝ) ^ w.length

end CoinTree

open CoinTree

variable {X : Type*} [Fintype X]

/-- The expected number of fair coin flips of an optimal algorithm generating `p`. -/
def minExpectedFlips (p : X → ℝ) : ℝ :=
  sInf {e | ∃ T : CoinTree X, T.Generates p ∧ T.FiniteFlips ∧ T.expectedFlips = e}

lemma le_minExpectedFlips {p : X → ℝ} (hne : ∃ T : CoinTree X, T.Generates p ∧ T.FiniteFlips) :
    entropyBase 2 p ≤ minExpectedFlips p := by
  obtain ⟨T, hT, hf⟩ := hne
  exact le_csInf ⟨_, T, hT, hf, rfl⟩ fun _ ⟨_, hT', hf', he⟩ =>
    he ▸ entropyBase_le_expectedFlips hT' hf'

omit [Fintype X] in
lemma minExpectedFlips_le [Finite X] {p : X → ℝ} {T : CoinTree X} (hT : T.Generates p)
    (hf : T.FiniteFlips) : minExpectedFlips p ≤ T.expectedFlips := by
  have := Fintype.ofFinite X
  exact csInf_le ⟨entropyBase 2 p, fun _ ⟨_, hT', hf', he⟩ =>
    he ▸ entropyBase_le_expectedFlips hT' hf'⟩ ⟨T, hT, hf, rfl⟩

/-! ### Dyadic distributions -/

/-- **Theorem 5.11.2 (construction).** For a dyadic distribution, the tree of the Shannon (or
Huffman) code generates `X` with `ET = H(X)`: the leaf of `x` lies at depth `log (1/p(x))`. -/
theorem exists_generates_expectedFlips_eq_of_isDAdic {p : X → ℝ} (hp : IsPMF p)
    (hd : IsDAdic 2 p) :
    ∃ T : CoinTree X, T.Generates p ∧ T.FiniteFlips ∧ T.expectedFlips = entropyBase 2 p := by
  classical
  have hl := eq_one_div_two_pow_of_isDAdic hd
  have hk : ∑ x, (1 / 2 : ℝ) ^ shannonLength 2 p x = 1 :=
    (sum_congr rfl fun x _ => (hl x).symm).trans hp.sum_eq_one
  obtain ⟨c, hc, hlen⟩ := exists_prefixCode_of_kraft (α := Bool) (shannonLength 2 p) (by
    rw [Fintype.card_bool]
    push_cast
    exact hk.le)
  have hsum : HasSum (fun x => (1 / 2 : ℝ) ^ (c x).length) 1 := by
    simpa only [hlen, hk] using hasSum_fintype fun x => (1 / 2 : ℝ) ^ (c x).length
  have hlog : ∀ x, logb 2 (1 / p x) = shannonLength 2 p x := fun x => by
    rw [hl x, one_div_pow, one_div_one_div, logb_pow, logb_self_eq_one one_lt_two, mul_one]
  refine ⟨ofCode c hc id hsum, fun x => ?_, ?_, ?_⟩
  · rw [outProb_ofCode, tsum_eq_single x fun i hi => by simp [hi]]
    simp only [hlen, id_eq, eq_self, ↓reduceIte]
    exact (hl x).symm
  · rw [finiteFlips_ofCode_iff]
    exact Summable.of_finite
  · have hH := sum_mul_logb_inv_eq_entropyBase p 2
    push_cast at hH
    rw [expectedFlips_ofCode, tsum_fintype, ← hH]
    refine sum_congr rfl fun x _ => ?_
    rw [hlen, hlog, ← hl, mul_comm]

/-- **Theorem 5.11.2, (5.107).** For a dyadic distribution, the optimal algorithm generating `X`
from fair coin flips uses `ET = H(X)` flips on average. -/
theorem minExpectedFlips_eq_of_isDAdic {p : X → ℝ} (hp : IsPMF p) (hd : IsDAdic 2 p) :
    minExpectedFlips p = entropyBase 2 p := by
  obtain ⟨T, hT, hf, he⟩ := exists_generates_expectedFlips_eq_of_isDAdic hp hd
  exact le_antisymm (he ▸ minExpectedFlips_le hT hf) (le_minExpectedFlips ⟨T, hT, hf⟩)

/-! ### Binary expansions -/

/-- The `j`-th binary digit `⌊t 2^j⌋ mod 2` of `t`, for `j ≥ 0`. For `t ∈ [0, 1]`,
`t = ∑_{j ≥ 0} d_j(t) 2^{-j}`, with the terminating expansion for dyadic rationals (and
`1 = 1.000⋯`). -/
def binDigit (t : ℝ) (j : ℕ) : ℕ := ⌊t * 2 ^ j⌋₊ % 2

lemma binDigit_le_one (t : ℝ) (j : ℕ) : binDigit t j ≤ 1 :=
  Nat.lt_succ_iff.1 (Nat.mod_lt _ two_pos)

lemma binDigit_mul_eq_ite (t : ℝ) (j : ℕ) (a : ℝ) :
    (binDigit t j : ℝ) * a = if binDigit t j = 1 then a else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (binDigit_le_one t j) with h | h <;> simp [h]

@[simp] lemma binDigit_zero (j : ℕ) : binDigit 0 j = 0 := by simp [binDigit]

lemma floor_mul_two_pow_succ (t : ℝ) (j : ℕ) :
    ⌊t * 2 ^ (j + 1)⌋₊ = 2 * ⌊t * 2 ^ j⌋₊ + binDigit t (j + 1) := by
  have h : ⌊t * 2 ^ (j + 1)⌋₊ / 2 = ⌊t * 2 ^ j⌋₊ := by
    rw [← Nat.floor_div_natCast, pow_succ]
    push_cast
    congr 1
    ring
  rw [binDigit, ← h]
  exact (Nat.div_add_mod _ 2).symm

/-- The partial sums of the binary expansion are the truncations `⌊t⌋_j`. -/
lemma sum_binDigit {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 2) (j : ℕ) :
    ∑ i ∈ range (j + 1), (binDigit t i : ℝ) * (1 / 2) ^ i = truncBits j t := by
  induction j with
  | zero =>
    have : binDigit t 0 = ⌊t⌋₊ := by
      rw [binDigit, pow_zero, mul_one,
        Nat.mod_eq_of_lt ((Nat.floor_lt h0).2 (by exact_mod_cast h1))]
    simp [truncBits, this]
  | succ j ih =>
    rw [sum_range_succ, ih, truncBits, truncBits, floor_mul_two_pow_succ, one_div_pow, pow_succ]
    push_cast
    field_simp

/-- **(5.109)** The binary expansion `t = ∑_{j ≥ 0} d_j(t) 2^{-j}` of `t ∈ [0, 1]`. -/
theorem hasSum_binDigit {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    HasSum (fun j => (binDigit t j : ℝ) * (1 / 2) ^ j) t := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity), ← tendsto_add_atTop_iff_nat 1]
  simp only [sum_binDigit h0 (by linarith : t < 2)]
  have hlow : ∀ j : ℕ, t - (1 / 2 : ℝ) ^ j ≤ truncBits j t := fun j => by
    have := sub_truncBits_lt j t
    rw [one_div_pow]
    linarith
  have hlim : Tendsto (fun j : ℕ => t - (1 / 2 : ℝ) ^ j) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow
    fun j => truncBits_le j h0

/-- The expected depth `T = ∑_{j} j d_j(t) 2^{-j}` of the atoms `2^{-j}` of the binary expansion of
`t`, (5.121). -/
def atomFlips (t : ℝ) : ℝ := ∑' j : ℕ, (binDigit t j : ℝ) * ((j : ℝ) * (1 / 2) ^ j)

lemma hasSum_coe_mul_half_pow :
    HasSum (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) 2 := by
  have := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  convert this using 1
  norm_num

lemma summable_atomFlips (t : ℝ) :
    Summable fun j : ℕ => (binDigit t j : ℝ) * ((j : ℝ) * (1 / 2) ^ j) :=
  Summable.of_nonneg_of_le (fun j => by positivity) (fun j => by
      have : (binDigit t j : ℝ) ≤ 1 := by exact_mod_cast binDigit_le_one t j
      calc (binDigit t j : ℝ) * ((j : ℝ) * (1 / 2) ^ j) ≤ 1 * ((j : ℝ) * (1 / 2) ^ j) := by
            gcongr
        _ = (j : ℝ) * (1 / 2) ^ j := one_mul _)
    hasSum_coe_mul_half_pow.summable

@[simp] lemma atomFlips_zero : atomFlips 0 = 0 := by simp [atomFlips]

lemma binDigit_eq_zero_of_lt {t : ℝ} (h0 : 0 ≤ t) {n : ℕ} (hn : t * 2 ^ n < 2) {i : ℕ}
    (hi : i < n) : binDigit t i = 0 := by
  have h2 : (2 : ℝ) ^ i * 2 ≤ 2 ^ n := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ one_le_two hi
  have : t * 2 ^ i < 1 := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) i]
  rw [binDigit, Nat.floor_eq_zero.2 this]

lemma binDigit_eq_one {t : ℝ} {n : ℕ} (hn1 : (1 / 2 : ℝ) ^ n ≤ t) (hn2 : t * 2 ^ n < 2) :
    binDigit t n = 1 := by
  have h0 : 0 ≤ t := le_trans (by positivity) hn1
  have : ⌊t * 2 ^ n⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity)]
    rw [one_div_pow, div_le_iff₀ (by positivity)] at hn1
    push_cast
    constructor <;> linarith
  rw [binDigit, this]

/-- **(5.122)–(5.133)** If `2^{-n} ≤ t < 2^{-(n-1)}`, the atoms of the binary expansion of `t`
have `T ≤ (n + 1) t`: the digits before `n` vanish, the `n`-th digit is one, and the later atoms
contribute at most `2^{-n}` beyond `(n + 1)` times their probability. -/
lemma atomFlips_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) {n : ℕ} (hn1 : (1 / 2 : ℝ) ^ n ≤ t)
    (hn2 : t * 2 ^ n < 2) : atomFlips t ≤ (n + 1) * t := by
  have hd := hasSum_binDigit h0 h1
  have hs := summable_atomFlips t
  set c : ℕ → ℝ := fun j => ((j : ℝ) - (n + 1)) * ((binDigit t j : ℝ) * (1 / 2) ^ j) with hc_def
  have hc : Summable c := by
    convert hs.sub (hd.summable.mul_left ((n : ℝ) + 1)) using 1
    funext j
    simp only [c]
    ring
  have hdiff : atomFlips t - (n + 1) * t = ∑' j, c j := by
    have e1 : ((n : ℝ) + 1) * t = ∑' j, ((n : ℝ) + 1) * ((binDigit t j : ℝ) * (1 / 2) ^ j) := by
      rw [Summable.tsum_mul_left _ hd.summable, hd.tsum_eq]
    rw [e1, atomFlips, ← hs.tsum_sub (hd.summable.mul_left _)]
    congr 1
    funext j
    simp only [c]
    ring
  rw [← hc.sum_add_tsum_nat_add (n + 1)] at hdiff
  have hfirst : ∑ i ∈ range (n + 1), c i = -(1 / 2) ^ n := by
    rw [sum_range_succ, sum_eq_zero fun i hi => by
      simp [c, binDigit_eq_zero_of_lt h0 hn2 (mem_range.1 hi)]]
    simp only [c, binDigit_eq_one hn1 hn2]
    push_cast
    ring
  have hg : HasSum (fun i : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ((i : ℝ) * (1 / 2) ^ i))
      ((1 / 2) ^ (n + 1) * 2) := hasSum_coe_mul_half_pow.mul_left _
  have hsecond : ∑' i, c (i + (n + 1)) ≤ (1 / 2) ^ n := by
    calc ∑' i, c (i + (n + 1)) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (n + 1) * ((i : ℝ) * (1 / 2) ^ i) := by
          refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff (n + 1)).2 hc)
            hg.summable
          have hb : (binDigit t (i + (n + 1)) : ℝ) ≤ 1 := by exact_mod_cast binDigit_le_one _ _
          have h3 : 0 ≤ (i : ℝ) * ((1 / 2 : ℝ) ^ i * (1 / 2) ^ (n + 1)) := by positivity
          simp only [c]
          push_cast
          rw [pow_add, show (i : ℝ) + (n + 1) - (n + 1) = i by ring]
          nlinarith
      _ = (1 / 2) ^ n := by rw [hg.tsum_eq, pow_succ]; ring
  linarith

/-- **(5.134)** The atoms of the binary expansion of `t ∈ (0, 1]` have expected depth
`T < -t log t + 2t`. -/
theorem atomFlips_lt {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : atomFlips t < -(t * logb 2 t) + 2 * t := by
  set n := ⌈logb 2 (1 / t)⌉₊
  have hlog0 : 0 ≤ logb 2 (1 / t) := logb_nonneg one_lt_two (by rw [le_div_iff₀ h0]; linarith)
  have hn_ge : logb 2 (1 / t) ≤ n := Nat.le_ceil _
  have hn_lt : (n : ℝ) < logb 2 (1 / t) + 1 := Nat.ceil_lt_add_one hlog0
  have hn1 : (1 / 2 : ℝ) ^ n ≤ t := by
    rw [logb_le_iff_le_rpow one_lt_two (by positivity), rpow_natCast,
      one_div_le h0 (by positivity)] at hn_ge
    rwa [one_div_pow]
  have hn2 : t * 2 ^ n < 2 := by
    have : (n : ℝ) - 1 < logb 2 (1 / t) := by linarith
    rw [lt_logb_iff_rpow_lt one_lt_two (by positivity), rpow_sub two_pos, rpow_natCast, rpow_one,
      lt_div_iff₀ h0] at this
    linarith
  calc atomFlips t ≤ (n + 1) * t := atomFlips_le h0.le h1 hn1 hn2
    _ < (logb 2 (1 / t) + 2) * t := mul_lt_mul_of_pos_right (by linarith) h0
    _ = -(t * logb 2 t) + 2 * t := by rw [one_div, logb_inv]; ring

/-! ### Theorem 5.11.3 -/

/-- A family indexed by `X × ℕ`, with `X` finite, has sum `∑ₓ sₓ` if each row `x` has sum `sₓ`. -/
lemma hasSum_prod_nat {f : X × ℕ → ℝ} {s : X → ℝ} (h : ∀ x, HasSum (fun j => f (x, j)) (s x)) :
    HasSum f (∑ x, s x) := by
  classical
  have h1 : ∀ x, HasSum (fun z : X × ℕ => if z.1 = x then f z else 0) (s x) := by
    intro x
    have hinj : Function.Injective (fun j : ℕ => (x, j)) := fun a b hab => (Prod.ext_iff.1 hab).2
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def] using h x
    · rintro ⟨y, j⟩ hz
      simp only [ite_eq_right_iff]
      rintro rfl
      exact absurd ⟨j, rfl⟩ hz
  convert hasSum_sum fun x (_ : x ∈ univ) => h1 x using 1
  funext z
  simp

/-- The atoms of the binary expansions of the probabilities: the pairs `(x, j)` such that the
`j`-th binary digit of `p(x)` is one, each an atom of probability `2^{-j}`, (5.109). -/
def atoms (p : X → ℝ) : Set (X × ℕ) := {z | binDigit (p z.1) z.2 = 1}

lemma hasSum_atoms {p : X → ℝ} (F : X × ℕ → ℝ) (s : X → ℝ)
    (h : ∀ x, HasSum (fun j => (binDigit (p x) j : ℝ) * F (x, j)) (s x)) :
    HasSum (fun a : atoms p => F a) (∑ x, s x) := by
  classical
  refine hasSum_subtype_iff_indicator.2 (hasSum_prod_nat fun x => ?_)
  simpa [Set.indicator_apply, atoms, binDigit_mul_eq_ite] using h x

/-- **Theorem 5.11.3 (construction).** Splitting each probability into the dyadic atoms of its
binary expansion and placing an atom `2^{-j}` at depth `j` (possible by the Kraft inequality)
gives an algorithm generating `X` with `ET < H(X) + 2`. -/
theorem exists_generates_expectedFlips_lt {p : X → ℝ} (hp : IsPMF p) :
    ∃ T : CoinTree X, T.Generates p ∧ T.FiniteFlips ∧ T.expectedFlips < entropyBase 2 p + 2 := by
  classical
  let := Fintype.toEncodable X
  have hdig : ∀ x, HasSum (fun j => (binDigit (p x) j : ℝ) * (1 / 2) ^ j) (p x) := fun x =>
    hasSum_binDigit (hp.nonneg x) (hp.le_one x)
  have hkraft : HasSum (fun a : atoms p => (1 / 2 : ℝ) ^ (a : X × ℕ).2) 1 := by
    have := hasSum_atoms (p := p) (fun z => (1 / 2 : ℝ) ^ z.2) p hdig
    rwa [hp.sum_eq_one] at this
  obtain ⟨c, hc, hlen⟩ := exists_prefixCode_of_summable (α := Bool)
    (fun a : atoms p => (a : X × ℕ).2)
    (by rw [Fintype.card_bool]; push_cast; exact hkraft.summable)
    (by rw [Fintype.card_bool]; push_cast; exact hkraft.tsum_eq.le)
  have hsum1 : HasSum (fun a : atoms p => (1 / 2 : ℝ) ^ (c a).length) 1 := by
    simp only [hlen]
    exact hkraft
  have hflips : HasSum (fun a : atoms p => ((c a).length : ℝ) * (1 / 2 : ℝ) ^ (c a).length)
      (∑ x, atomFlips (p x)) := by
    simp only [hlen]
    exact hasSum_atoms (fun z => (z.2 : ℝ) * (1 / 2) ^ z.2) _ fun x =>
      (summable_atomFlips (p x)).hasSum
  refine ⟨ofCode c hc (fun a => (a : X × ℕ).1) hsum1, fun x => ?_, ?_, ?_⟩
  · rw [outProb_ofCode]
    simp only [hlen]
    have := hasSum_atoms (p := p) (fun z => if z.1 = x then (1 / 2 : ℝ) ^ z.2 else 0)
      (fun y => if y = x then p x else 0) fun y => by
        by_cases hy : y = x
        · subst hy
          simpa using hdig y
        · simp [hy]
    rw [this.tsum_eq]
    simp
  · rw [finiteFlips_ofCode_iff]
    exact hflips.summable
  · rw [expectedFlips_ofCode, hflips.tsum_eq]
    have hH : entropyBase 2 p + 2 = ∑ x, (-(p x * logb 2 (p x)) + 2 * p x) := by
      rw [sum_add_distrib, ← mul_sum, hp.sum_eq_one, entropyBase, sum_neg_distrib, mul_one]
    rw [hH]
    obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < p x := by
      by_contra hne
      push Not at hne
      have : ∑ x, p x ≤ 0 := sum_nonpos fun x _ => hne x
      linarith [hp.sum_eq_one]
    refine sum_lt_sum (fun x _ => ?_) ⟨x₀, mem_univ _, atomFlips_lt hx₀ (hp.le_one x₀)⟩
    rcases (hp.nonneg x).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · exact (atomFlips_lt h0 (hp.le_one x)).le

/-- **Theorem 5.11.3, (5.115).** The expected number of fair bits required by the optimal algorithm
to generate `X` satisfies `H(X) ≤ ET < H(X) + 2`. -/
theorem minExpectedFlips_bounds {p : X → ℝ} (hp : IsPMF p) :
    entropyBase 2 p ≤ minExpectedFlips p ∧ minExpectedFlips p < entropyBase 2 p + 2 := by
  obtain ⟨T, hT, hf, hlt⟩ := exists_generates_expectedFlips_lt hp
  exact ⟨le_minExpectedFlips ⟨T, hT, hf⟩, (minExpectedFlips_le hT hf).trans_lt hlt⟩

end InfoTheory
