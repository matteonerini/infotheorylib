/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter2
public import InfoTheoryLib.Books.CoverThomas.Chapter4
public import InfoTheoryLib.SourceCoding.Huffman
public import InfoTheoryLib.SourceCoding.ShannonFanoEliasBlock
public import InfoTheoryLib.SourceCoding.CoinFlips
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# Cover & Thomas, Chapter 5: Data Compression

This file indexes the formalization of Chapter 5 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_5_2_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Codes.** A code is a map `C : X → List α` into strings over a code alphabet `α` with
  `D = Fintype.card α` symbols. Binary codewords in the examples are written over `Fin 2` (or
  `Bool`), ternary ones over `Fin 3`. The source symbols `1, …, m` are `0, …, m - 1 : Fin m`.
* **Lengths.** Many results only involve the codeword lengths `l : X → ℕ`: by the Kraft and
  McMillan inequalities, lengths with `∑ D^{-l(x)} ≤ 1` (`kraftSum D l ≤ 1`) are exactly the
  lengths of prefix codes, and of uniquely decodable codes.
* **Logarithms.** `entropyBase D p` is the entropy `H_D(X)` in base `D`; for binary codes it is in
  bits.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 5.1 Examples of codes
* Source codes, (5.1) expected length, (5.4) non-singular codes, (5.5) extension, uniquely
  decodable and prefix codes: `expectedLength`, `IsNonsingular`, `extension`,
  `IsUniquelyDecodableCode`, `IsPrefixCode` (`SourceCoding.Code`).
* Figure 5.1, the nesting of the classes: `IsPrefixCode.isUniquelyDecodableCode'`,
  `IsUniquelyDecodableCode.isNonsingular` (`SourceCoding.Code`).
* Examples 5.1.1, 5.1.2 and 5.1.4: `example_5_1_1`, `example_5_1_1_decode`,
  `example_5_1_1_parse`, `example_5_1_2`, `example_5_1_4` (here).
* Table 5.1: `table_5_1_singular`, `table_5_1_nonsingular`, `table_5_1_ud`,
  `table_5_1_instantaneous` (here).

### 5.2 Kraft inequality
* Theorem 5.2.1: `kraft_of_isPrefixCode` and the converse `exists_prefixCode_of_kraft`
  (`SourceCoding.Kraft`).
* Theorem 5.2.2: `summable_kraft_of_isPrefixCode` and the converse `exists_prefixCode_of_summable`,
  through the intervals of (5.10)–(5.11), `exists_prefix_words` (`SourceCoding.Kraft`).

### 5.3 Optimal codes
* Theorem 5.3.1: `entropyBase_le_expectedLength`, `entropyBase_eq_expectedLength_iff`
  (`SourceCoding.OptimalLength`).
* `D`-adic distributions: `IsDAdic`, `exists_lengths_eq_entropyBase_iff`
  (`SourceCoding.OptimalLength`).

### 5.4 Bounds on the optimal codelength
* (5.29)–(5.32), the Shannon code: `shannonLength`, `shannonLength_bounds`,
  `kraftSum_shannonLength_le`, `shannon_expectedLength_bounds`, `exists_prefixCode_shannon`
  (`SourceCoding.OptimalLength`).
* Theorem 5.4.1: `minExpectedLength`, `minExpectedLength_bounds`, `minExpectedLength_le_add_one`.
* (5.35)–(5.39), Theorem 5.4.2: `minExpectedLength_iid_bounds`,
  `minExpectedLength_process_bounds`, `tendsto_minExpectedLength`.
* Theorem 5.4.3: `wrongCode_bounds`.

### 5.5 Kraft inequality for uniquely decodable codes
* Theorem 5.5.1 (McMillan): `kraft_of_isUniquelyDecodableCode`,
  `exists_uniquelyDecodableCode_of_kraft`, `exists_prefixCode_iff_exists_uniquelyDecodableCode`
  (`SourceCoding.Kraft`).
* Corollary (infinite alphabets): `summable_kraft_of_isUniquelyDecodableCode`.

### 5.6 Huffman codes
* Huffman's algorithm on codeword lengths: `huffmanMerge`, `huffmanCost`, `huffmanLengths`,
  `kraft_huffmanLengths`, `cost_huffmanLengths`, and the code `huffmanCode`
  (`SourceCoding.Huffman`).
* Example 5.6.1: `huffmanCost_5_6_1`, `example_5_6_1` (here).
* Examples 5.6.2 and 5.6.3 (ternary codes): `example_5_6_2`, `example_5_6_3` (here).

### 5.7 Some comments on Huffman codes
* Comment 2 and Example 5.7.1, weighted codewords: `huffmanCost_le` holds for any non-negative
  weights (`SourceCoding.Huffman`); `huffmanCost_5_7_1`, `example_5_7_1` (here).
* Comment 3 and Example 5.7.2, slice codes: `example_5_7_2` (here).
* Comment 4 and Example 5.7.3, Huffman and Shannon codes: `example_5_7_shannon`,
  `huffmanCost_5_7_3`, `example_5_7_3` (here).

### 5.8 Optimality of Huffman codes
* Lemma 5.8.1: `cost_comp_swap` (5.62)–(5.64), `kraft_update_of_unique_max`,
  `exists_canonical_lengths` (`SourceCoding.Huffman`).
* (5.65)–(5.71) and Theorem 5.8.1: `huffmanCost_le`, `huffmanCost_le_expectedLength`,
  `huffmanCode_optimal` (`SourceCoding.Huffman`).

### 5.9 Shannon–Fano–Elias coding
* (5.72)–(5.75): `cdf`, `cdfLT`, `midCdf`, `midCdf_injective`, `truncBits`, `sub_truncBits_lt`,
  `sfeLength`, `one_div_two_pow_sfeLength_le`, `sfeNum_div_mem_step`
  (`SourceCoding.ShannonFanoElias`).
* The code is prefix-free, and (5.76): `sfeCode`, `sfeCode_isPrefixCode`,
  `expectedLength_sfeCode_lt` (`SourceCoding.ShannonFanoElias`).
* Examples 5.9.1 and 5.9.2: `example_5_9_1`, `example_5_9_2` (here).
* Shannon–Fano–Elias coding of sequences, with the probability and the cumulative distribution
  function computed sequentially: `leftSubtreeProb`, `cdfLT_lex`, `cdf_lex`, `iidPMF_snoc`,
  `cdfLT_lex_iid`, `blockSfeCode`, `blockSfeCode_isPrefixCode`,
  `expectedLength_blockSfeCode_iid_lt` (`SourceCoding.ShannonFanoEliasBlock`), and for Markov
  sources `markovLaw_snoc` (`StochasticProcess.Markov`).

### 5.10 Competitive optimality of the Shannon code
* Theorem 5.10.1: `prob_shannonLength_ge_add_le`, `prob_shannonLength_ge_add_le_of_code`
  (`SourceCoding.Competitive`), and the `5`-bit example `example_5_10_five_bits` (here).
* (5.86)–(5.90): `sign_le_two_zpow_sub_one`, `sign_eq_two_zpow_sub_one_iff`,
  `prob_lt_sub_prob_gt_eq` (`SourceCoding.Competitive`).
* Theorem 5.10.2: `prob_gt_le_prob_lt_of_dyadic`, `prob_gt_eq_prob_lt_iff_of_dyadic`.
* Corollary (5.97): `expect_sign_sub_one_le_zero`; closing remark: `expect_le_zero_of_dyadic`,
  `intCast_le_two_zpow_sub_one`.

### 5.11 Generation of discrete distributions from fair coins
* Generating trees: `CoinTree`, `CoinTree.outProb`, `CoinTree.Generates`,
  `CoinTree.expectedFlips`, `minExpectedFlips` (`SourceCoding.CoinFlips`).
* Example 5.11.1: `example_5_11_1`, `example_5_11_1'` (here).
* Lemma 5.11.1: `CoinTree.leafEntropy_eq_expectedFlips`.
* Theorem 5.11.1: `CoinTree.entropyBase_le_expectedFlips`.
* Theorem 5.11.2: `exists_generates_expectedFlips_eq_of_isDAdic`, `minExpectedFlips_eq_of_isDAdic`.
* (5.109), binary expansions: `binDigit`, `hasSum_binDigit`; Example 5.11.2: `example_5_11_2`
  (here).
* Theorem 5.11.3, (5.116)–(5.135): `atomFlips_le`, `atomFlips_lt`,
  `exists_generates_expectedFlips_lt`, `minExpectedFlips_bounds` (`SourceCoding.CoinFlips`).

## Not formalized

* Example 5.1.3 (Morse code), the Lagrange-multiplier heuristic (5.15)–(5.20), and Figures 5.2–5.8
  (the figures of trees are represented by the definitions above).
* The equivalence with the game of 20 questions, (5.61), beyond the observation that a binary code
  is a questioning strategy: the formal statements are about codes.
* `D`-ary Huffman codes: only binary Huffman coding is formalized, so Examples 5.6.2 and 5.6.3
  check the codes' expected lengths but not their optimality.
* The Sardinas–Patterson test, Fano codes, and arithmetic coding with fixed-precision arithmetic,
  which the book defers to Section 13.3.
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 5.1: Examples of codes -/

/-- **Example 5.1.1, (5.2).** The code `C(1) = 0`, `C(2) = 10`, `C(3) = 110`, `C(4) = 111` for the
distribution `(1/2, 1/4, 1/8, 1/8)` (`pmf_2_1_2`). -/
def code_5_1_1 : Fin 4 → List (Fin 2) := ![[0], [1, 0], [1, 1, 0], [1, 1, 1]]

lemma code_5_1_1_isPrefixCode : IsPrefixCode code_5_1_1 := by
  unfold IsPrefixCode
  decide

/-- **Example 5.1.1.** The entropy is `H(X) = 1.75` bits, and the expected length of the code is
also `L(C) = 1.75` bits. -/
theorem example_5_1_1 :
    entropyBase 2 pmf_2_1_2 = 7 / 4 ∧ expectedLength pmf_2_1_2 code_5_1_1 = 7 / 4 := by
  refine ⟨by rw [entropyBase_eq_div, example_2_1_2], ?_⟩
  simp [expectedLength, code_5_1_1, pmf_2_1_2, Fin.sum_univ_four]
  norm_num

/-- **Example 5.1.1.** The bit string `0110111100110` is decoded as `134213`, and it has no other
decoding. (Symbols `1, …, 4` are `0, …, 3 : Fin 4`.) -/
theorem example_5_1_1_decode :
    extension code_5_1_1 [0, 2, 3, 1, 0, 2] = [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0] ∧
      ∀ xs, extension code_5_1_1 xs = [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0] →
        xs = [0, 2, 3, 1, 0, 2] := by
  have h : extension code_5_1_1 [0, 2, 3, 1, 0, 2] = [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0] := by
    decide
  exact ⟨h, fun xs hxs => code_5_1_1_isPrefixCode.isUniquelyDecodableCode' (hxs.trans h.symm)⟩

/-- **Section 5.1.** The string `01011111010` produced by the code of Example 5.1.1 is parsed as
`0, 10, 111, 110, 10`. -/
theorem example_5_1_1_parse :
    extension code_5_1_1 [0, 1, 3, 2, 1] = [0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0] := by
  decide

/-- **Example 5.1.2, (5.3).** The uniform distribution on three symbols. -/
def pmf_5_1_2 : Fin 3 → ℝ := fun _ => 1 / 3

/-- **Example 5.1.2, (5.3).** The code `C(1) = 0`, `C(2) = 10`, `C(3) = 11`. -/
def code_5_1_2 : Fin 3 → List (Fin 2) := ![[0], [1, 0], [1, 1]]

/-- **Example 5.1.2.** The code is uniquely decodable (indeed instantaneous), the entropy is
`log 3 ≈ 1.58` bits and the expected length `5/3 ≈ 1.66` bits: here `L(C) > H(X)`. -/
theorem example_5_1_2 :
    IsUniquelyDecodableCode code_5_1_2 ∧ entropyBase 2 pmf_5_1_2 = logb 2 3 ∧
      expectedLength pmf_5_1_2 code_5_1_2 = 5 / 3 ∧
        entropyBase 2 pmf_5_1_2 < expectedLength pmf_5_1_2 code_5_1_2 := by
  have hpre : IsPrefixCode code_5_1_2 := by
    unfold IsPrefixCode
    decide
  have hH : entropyBase 2 pmf_5_1_2 = logb 2 3 := by
    simp only [entropyBase, pmf_5_1_2, Fin.sum_univ_three, one_div, logb_inv]
    ring
  have hL : expectedLength pmf_5_1_2 code_5_1_2 = 5 / 3 := by
    simp [expectedLength, pmf_5_1_2, code_5_1_2, Fin.sum_univ_three]
    norm_num
  refine ⟨hpre.isUniquelyDecodableCode', hH, hL, ?_⟩
  rw [hH, hL, logb, div_lt_iff₀ (log_pos one_lt_two)]
  have h1 : log ((3 : ℝ) ^ 3) < log ((2 : ℝ) ^ 5) := log_lt_log (by norm_num) (by norm_num)
  rw [log_pow, log_pow] at h1
  push_cast at h1
  linarith

/-- **Example 5.1.4.** If `C(x₁) = 00` and `C(x₂) = 11`, then `C*(x₁x₂) = 0011`. -/
theorem example_5_1_4 : extension (![[0, 0], [1, 1]] : Fin 2 → List (Fin 2)) [0, 1] =
    [0, 0, 1, 1] := by
  decide

/-! ### Table 5.1: classes of codes -/

/-- **Table 5.1.** A singular code. -/
def codeSingular : Fin 4 → List (Fin 2) := fun _ => [0]

/-- **Table 5.1.** A non-singular code that is not uniquely decodable. -/
def codeNonsingular : Fin 4 → List (Fin 2) := ![[0], [0, 1, 0], [0, 1], [1, 0]]

/-- **Table 5.1.** A uniquely decodable code that is not instantaneous. -/
def codeUD : Fin 4 → List (Fin 2) := ![[1, 0], [0, 0], [1, 1], [1, 1, 0]]

lemma codeUD_zero : codeUD 0 = [1, 0] := rfl
lemma codeUD_one : codeUD 1 = [0, 0] := rfl
lemma codeUD_two : codeUD 2 = [1, 1] := rfl
lemma codeUD_three : codeUD 3 = [1, 1, 0] := rfl

/-- **Table 5.1.** An instantaneous code. -/
def codeInstantaneous : Fin 4 → List (Fin 2) := ![[0], [1, 0], [1, 1, 0], [1, 1, 1]]

theorem table_5_1_singular : ¬ IsNonsingular codeSingular := fun h =>
  absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)

/-- **Table 5.1.** The non-singular code is not uniquely decodable: the code string `010` has the
three source sequences `2`, `14` and `31`. -/
theorem table_5_1_nonsingular :
    IsNonsingular codeNonsingular ∧ ¬ IsUniquelyDecodableCode codeNonsingular ∧
      extension codeNonsingular [1] = [0, 1, 0] ∧ extension codeNonsingular [0, 3] = [0, 1, 0] ∧
        extension codeNonsingular [2, 0] = [0, 1, 0] := by
  have h1 : extension codeNonsingular [1] = [0, 1, 0] := by decide
  have h2 : extension codeNonsingular [0, 3] = [0, 1, 0] := by decide
  refine ⟨by unfold IsNonsingular Function.Injective; decide, fun h => ?_, h1, h2, by decide⟩
  exact absurd (h (h1.trans h2.symm)) (by decide)

/-- After `11`, the code `codeUD` cannot continue with a `0` followed by a valid code string: the
string of `0`s after `11` must be read as the codewords `00`, and an odd run is impossible. -/
lemma extension_codeUD_ne (n : ℕ) :
    ∀ as bs : List (Fin 4), (extension codeUD as).length = n →
      extension codeUD as ≠ 0 :: extension codeUD bs := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro as bs hn h
    match as with
    | [] => simp at h
    | a :: as' =>
      fin_cases a <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, extension_cons,
          codeUD_zero, codeUD_one, codeUD_two, codeUD_three, List.cons_append,
          List.nil_append, List.cons.injEq, Fin.reduceEq, false_and, true_and] at h hn
      have hlen := congrArg List.length h
      simp only [List.length_cons] at hlen hn
      exact ih _ (by omega) bs as' rfl h.symm

/-- **Table 5.1.** The third code is uniquely decodable but not instantaneous: `11` is a prefix of
`110`. -/
theorem table_5_1_ud : IsUniquelyDecodableCode codeUD ∧ ¬ IsPrefixCode codeUD := by
  refine ⟨fun xs => ?_, by unfold IsPrefixCode; decide⟩
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      fin_cases y <;> simp [codeUD_zero, codeUD_one, codeUD_two, codeUD_three] at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => fin_cases x <;> simp [codeUD_zero, codeUD_one, codeUD_two, codeUD_three] at h
    | cons y ys =>
      fin_cases x <;> fin_cases y <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, extension_cons,
          codeUD_zero, codeUD_one, codeUD_two, codeUD_three, List.cons_append,
          List.nil_append, List.cons.injEq, Fin.reduceEq, false_and, true_and] at h ⊢
      all_goals first
        | exact ih h
        | exact absurd h (extension_codeUD_ne _ _ _ rfl)
        | exact absurd h.symm (extension_codeUD_ne _ _ _ rfl)

/-- **Table 5.1.** The last code is instantaneous: no codeword is a prefix of another. -/
theorem table_5_1_instantaneous : IsPrefixCode codeInstantaneous := by
  unfold IsPrefixCode
  decide

/-! ## Section 5.6: Huffman codes -/

/-- **Example 5.6.1.** The distribution `(0.25, 0.25, 0.2, 0.15, 0.15)`. -/
def pmf_5_6_1 : Fin 5 → ℝ := ![1 / 4, 1 / 4, 1 / 5, 3 / 20, 3 / 20]

lemma pmf_5_6_1_isPMF : IsPMF pmf_5_6_1 :=
  ⟨fun x => by fin_cases x <;> norm_num [pmf_5_6_1],
    by simp [pmf_5_6_1, Fin.sum_univ_five]; norm_num⟩

/-- **Example 5.6.1.** The binary Huffman code `01, 10, 11, 000, 001`. -/
def code_5_6_1 : Fin 5 → List (Fin 2) := ![[0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1]]

/-- **Example 5.6.1.** Huffman's algorithm merges `0.15 + 0.15 = 0.3`, `0.2 + 0.25 = 0.45`,
`0.25 + 0.3 = 0.55` and `0.45 + 0.55 = 1`, for a total cost of `2.3`. -/
theorem huffmanCost_5_6_1 : huffmanCost 5 pmf_5_6_1 = 23 / 10 := by
  have s5 : huffmanCost 5 pmf_5_6_1 = 3 / 10 + huffmanCost 4 ![3 / 10, 1 / 5, 1 / 4, 1 / 4] :=
    huffmanCost_step _ (Equiv.swap 0 3 * Equiv.swap 1 4)
      (Fin.monotone_iff_le_succ.2 fun i => by
        fin_cases i <;> norm_num [pmf_5_6_1, Equiv.swap_apply_def])
      (by norm_num [pmf_5_6_1, Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, pmf_5_6_1, Equiv.swap_apply_def])
  have s4 : huffmanCost 4 ![3 / 10, 1 / 5, 1 / 4, 1 / 4] =
      9 / 20 + huffmanCost 3 ![9 / 20, 1 / 4, 3 / 10] :=
    huffmanCost_step _ (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, Equiv.swap_apply_def])
  have s3 : huffmanCost 3 ![9 / 20, 1 / 4, 3 / 10] = 11 / 20 + huffmanCost 2 ![11 / 20, 9 / 20] :=
    huffmanCost_step _ (Equiv.swap 0 1 * Equiv.swap 1 2)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, Equiv.swap_apply_def])
  have s2 : huffmanCost 2 ![11 / 20, 9 / 20] = 1 :=
    (huffmanCost_step (a := 1) _ (Equiv.swap 0 1)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i; norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def]) rfl).trans (by simp)
  rw [s5, s4, s3, s2]
  norm_num

/-- **Example 5.6.1.** The Huffman code is a prefix code with expected length `2.3` bits, and no
binary uniquely decodable code has a smaller expected length. -/
theorem example_5_6_1 :
    IsPrefixCode code_5_6_1 ∧ expectedLength pmf_5_6_1 code_5_6_1 = 23 / 10 ∧
      ∀ {α : Type} [Fintype α], Fintype.card α = 2 → ∀ C : Fin 5 → List α,
        IsUniquelyDecodableCode C →
          expectedLength pmf_5_6_1 code_5_6_1 ≤ expectedLength pmf_5_6_1 C := by
  have hL : expectedLength pmf_5_6_1 code_5_6_1 = 23 / 10 := by
    simp [expectedLength, pmf_5_6_1, code_5_6_1, Fin.sum_univ_five]
    norm_num
  refine ⟨by unfold IsPrefixCode; decide, hL, fun hα C hC => ?_⟩
  rw [hL, ← huffmanCost_5_6_1]
  exact huffmanCost_le_expectedLength pmf_5_6_1_isPMF.nonneg hα hC

/-- **Example 5.6.2.** The ternary Huffman code `1, 2, 00, 01, 02` for the same distribution. -/
def code_5_6_2 : Fin 5 → List (Fin 3) := ![[1], [2], [0, 0], [0, 1], [0, 2]]

/-- **Example 5.6.2.** The ternary code is a prefix code with expected length `1.5` ternary
digits. -/
theorem example_5_6_2 :
    IsPrefixCode code_5_6_2 ∧ expectedLength pmf_5_6_1 code_5_6_2 = 3 / 2 := by
  refine ⟨by unfold IsPrefixCode; decide, ?_⟩
  simp [expectedLength, pmf_5_6_1, code_5_6_2, Fin.sum_univ_five]
  norm_num

/-- **Example 5.6.3.** Six symbols with probabilities `(0.25, 0.25, 0.2, 0.1, 0.1, 0.1)` and a
dummy symbol of probability `0`, so that the number of symbols is `1 + k(D - 1) = 7`. -/
def pmf_5_6_3 : Fin 7 → ℝ := ![1 / 4, 1 / 4, 1 / 5, 1 / 10, 1 / 10, 1 / 10, 0]

/-- **Example 5.6.3.** The ternary Huffman code `1, 2, 01, 02, 000, 001, 002`. -/
def code_5_6_3 : Fin 7 → List (Fin 3) :=
  ![[1], [2], [0, 1], [0, 2], [0, 0, 0], [0, 0, 1], [0, 0, 2]]

/-- **Example 5.6.3.** The ternary code is a prefix code whose tree is complete (equality in the
Kraft inequality), with expected length `1.7` ternary digits. -/
theorem example_5_6_3 :
    IsPrefixCode code_5_6_3 ∧ kraftSum 3 (fun x => (code_5_6_3 x).length) = 1 ∧
      expectedLength pmf_5_6_3 code_5_6_3 = 17 / 10 := by
  refine ⟨by unfold IsPrefixCode; decide, ?_, ?_⟩
  · simp [kraftSum, code_5_6_3, Fin.sum_univ_succ]
    norm_num
  · simp [expectedLength, pmf_5_6_3, code_5_6_3, Fin.sum_univ_succ]
    norm_num

/-! ## Section 5.7: Some comments on Huffman codes -/

/-- **Example 5.7.1.** The weights `(5, 5, 4, 4)`. -/
def weights_5_7_1 : Fin 4 → ℝ := ![5, 5, 4, 4]

/-- **Example 5.7.1.** The code `00, 01, 10, 11` built by Huffman's algorithm for the weights. -/
def code_5_7_1 : Fin 4 → List (Fin 2) := ![[0, 0], [0, 1], [1, 0], [1, 1]]

theorem huffmanCost_5_7_1 : huffmanCost 4 weights_5_7_1 = 36 := by
  have s4 : huffmanCost 4 weights_5_7_1 = 8 + huffmanCost 3 ![8, 5, 5] :=
    huffmanCost_step _ (Equiv.swap 0 2 * Equiv.swap 1 3)
      (Fin.monotone_iff_le_succ.2 fun i => by
        fin_cases i <;> norm_num [weights_5_7_1, Equiv.swap_apply_def])
      (by norm_num [weights_5_7_1, Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, weights_5_7_1, Equiv.swap_apply_def])
  have s3 : huffmanCost 3 ![8, 5, 5] = 10 + huffmanCost 2 ![10, 8] :=
    huffmanCost_step _ (Equiv.swap 0 1 * Equiv.swap 1 2)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, Equiv.swap_apply_def])
  have s2 : huffmanCost 2 ![10, 8] = 18 :=
    (huffmanCost_step (a := 18) _ (Equiv.swap 0 1)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i; norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def]) rfl).trans (by simp)
  rw [s4, s3, s2]
  norm_num

/-- **Example 5.7.1 (Section 5.7, comment 2).** Huffman's algorithm applies to any non-negative
weights: the code `00, 01, 10, 11` minimizes the weighted sum of the codeword lengths among
binary uniquely decodable codes, and the minimum is `36`. -/
theorem example_5_7_1 :
    expectedLength weights_5_7_1 code_5_7_1 = 36 ∧
      ∀ {α : Type} [Fintype α], Fintype.card α = 2 → ∀ C : Fin 4 → List α,
        IsUniquelyDecodableCode C →
          expectedLength weights_5_7_1 code_5_7_1 ≤ expectedLength weights_5_7_1 C := by
  have hL : expectedLength weights_5_7_1 code_5_7_1 = 36 := by
    simp [expectedLength, weights_5_7_1, code_5_7_1, Fin.sum_univ_four]
    norm_num
  refine ⟨hL, fun hα C hC => ?_⟩
  rw [hL, ← huffmanCost_5_7_1]
  exact huffmanCost_le_expectedLength (fun i => by fin_cases i <;> norm_num [weights_5_7_1]) hα hC

/-- **Example 5.7.2.** The "slice" code `00, 01, 10, 110, 111` for the distribution of Example
5.6.1, with the Huffman codeword lengths `{2, 2, 2, 3, 3}` assigned in order. -/
def code_5_7_2 : Fin 5 → List (Fin 2) := ![[0, 0], [0, 1], [1, 0], [1, 1, 0], [1, 1, 1]]

/-- **Example 5.7.2 (Section 5.7, comment 3).** The slice code is an optimal prefix code (it has
the expected length `2.3` of the Huffman code), and it is alphabetic: its codewords are in
lexicographic order. The Huffman code of Example 5.6.1 is not. -/
theorem example_5_7_2 :
    IsPrefixCode code_5_7_2 ∧ expectedLength pmf_5_6_1 code_5_7_2 = 23 / 10 ∧
      StrictMono code_5_7_2 ∧ ¬ StrictMono code_5_6_1 := by
  refine ⟨by unfold IsPrefixCode; decide, ?_, by unfold StrictMono; decide,
    by unfold StrictMono; decide⟩
  simp [expectedLength, pmf_5_6_1, code_5_7_2, Fin.sum_univ_five]
  norm_num

/-- **Example 5.7.3.** The distribution `(1/3, 1/3, 1/4, 1/12)`. -/
def pmf_5_7_3 : Fin 4 → ℝ := ![1 / 3, 1 / 3, 1 / 4, 1 / 12]

theorem huffmanCost_5_7_3 : huffmanCost 4 pmf_5_7_3 = 2 := by
  have s4 : huffmanCost 4 pmf_5_7_3 = 1 / 3 + huffmanCost 3 ![1 / 3, 1 / 3, 1 / 3] :=
    huffmanCost_step _ (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 2)
      (Fin.monotone_iff_le_succ.2 fun i => by
        fin_cases i <;> norm_num [pmf_5_7_3, Equiv.swap_apply_def])
      (by norm_num [pmf_5_7_3, Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, pmf_5_7_3, Equiv.swap_apply_def])
  have s3 : huffmanCost 3 ![1 / 3, 1 / 3, 1 / 3] = 2 / 3 + huffmanCost 2 ![2 / 3, 1 / 3] :=
    huffmanCost_step _ 1
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> norm_num)
      (by norm_num)
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq])
  have s2 : huffmanCost 2 ![2 / 3, 1 / 3] = 1 :=
    (huffmanCost_step (a := 1) _ (Equiv.swap 0 1)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i; norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def]) rfl).trans (by simp)
  rw [s4, s3, s2]
  norm_num

/-- **Example 5.7.3.** Both `(2, 2, 2, 2)` and `(1, 2, 3, 3)` are optimal codeword lengths: they
satisfy the Kraft inequality (with equality) and achieve the Huffman cost `2`. So the optimal
lengths are not unique, and in the second the third symbol gets `3 > ⌈log 4⌉ = 2` bits: an
optimal code can be longer than the Shannon code on a particular symbol. -/
theorem example_5_7_3 :
    (∑ i, (1 / 2 : ℝ) ^ (![2, 2, 2, 2] : Fin 4 → ℕ) i = 1 ∧
      ∑ i, pmf_5_7_3 i * (![2, 2, 2, 2] : Fin 4 → ℕ) i = huffmanCost 4 pmf_5_7_3) ∧
    (∑ i, (1 / 2 : ℝ) ^ (![1, 2, 3, 3] : Fin 4 → ℕ) i = 1 ∧
      ∑ i, pmf_5_7_3 i * (![1, 2, 3, 3] : Fin 4 → ℕ) i = huffmanCost 4 pmf_5_7_3) ∧
    shannonLength 2 pmf_5_7_3 2 = 2 ∧
      shannonLength 2 pmf_5_7_3 2 < (![1, 2, 3, 3] : Fin 4 → ℕ) 2 := by
  have hs : shannonLength 2 pmf_5_7_3 2 = 2 :=
    shannonLength_of_eq_pow le_rfl (by norm_num [pmf_5_7_3])
  rw [huffmanCost_5_7_3, hs]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, rfl, by decide⟩ <;>
    simp [pmf_5_7_3, Fin.sum_univ_four] <;> norm_num

/-- **Section 5.7, comment 4.** The distribution `(0.9999, 0.0001)`. -/
def pmf_5_7_shannon : Fin 2 → ℝ := ![9999 / 10000, 1 / 10000]

/-- **Section 5.7, comment 4.** The Shannon code for `(0.9999, 0.0001)` uses `1` and `14` bits,
while the optimal code uses `1` bit for both symbols. -/
theorem example_5_7_shannon :
    shannonLength 2 pmf_5_7_shannon 0 = 1 ∧ shannonLength 2 pmf_5_7_shannon 1 = 14 ∧
      huffmanCost 2 pmf_5_7_shannon = 1 := by
  refine ⟨(shannonLength_eq_iff le_rfl (by norm_num [pmf_5_7_shannon]) one_ne_zero).2
      (by norm_num [pmf_5_7_shannon]),
    (shannonLength_eq_iff le_rfl (by norm_num [pmf_5_7_shannon]) (by norm_num)).2
      (by norm_num [pmf_5_7_shannon]), ?_⟩
  exact (huffmanCost_step (a := 1) _ (Equiv.swap 0 1)
    (Fin.monotone_iff_le_succ.2 fun i => by
      fin_cases i; norm_num [pmf_5_7_shannon, Equiv.swap_apply_def])
    (by norm_num [pmf_5_7_shannon, Equiv.swap_apply_def]) rfl).trans (by simp)

/-! ## Section 5.9: Shannon–Fano–Elias coding -/

/-- To compute a Shannon–Fano–Elias codeword: if `l(x) = l` and `⌊F̄(x) 2^l⌋ = N`, the codeword is
the `l`-bit binary expansion of `N`. -/
lemma sfeCode_eq_of {X : Type*} [Fintype X] [LinearOrder X] {p : X → ℝ} {x : X} {l N : ℕ}
    (hl : shannonLength 2 p x + 1 = l)
    (hN : (N : ℝ) ≤ midCdf p x * 2 ^ l ∧ midCdf p x * 2 ^ l < N + 1) :
    sfeCode p x = natToWord 2 l N := by
  have hN' : sfeNum p x = N := by
    rw [sfeNum, show sfeLength p x = l from hl]
    exact (Nat.floor_eq_iff ((Nat.cast_nonneg N).trans hN.1)).2 hN
  rw [sfeCode, show sfeLength p x = l from hl, hN']

lemma logb_two_four : logb 2 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, logb_pow, logb_self_eq_one one_lt_two]
  norm_num

lemma logb_two_eight : logb 2 8 = 3 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, logb_pow, logb_self_eq_one one_lt_two]
  norm_num

/-- **Example 5.9.1.** The dyadic distribution `(0.25, 0.5, 0.125, 0.125)`. -/
def pmf_5_9_1 : Fin 4 → ℝ := ![1 / 4, 1 / 2, 1 / 8, 1 / 8]

/-- **Example 5.9.1.** The Shannon–Fano–Elias code is `001, 10, 1101, 1111`, with average length
`2.75` bits, while the entropy is `1.75` bits. Removing the last bit of every codeword gives
`00, 1, 110, 111`, which is not a prefix code. -/
theorem example_5_9_1 :
    sfeCode pmf_5_9_1 = ![[0, 0, 1], [1, 0], [1, 1, 0, 1], [1, 1, 1, 1]] ∧
      expectedLength pmf_5_9_1 (sfeCode pmf_5_9_1) = 11 / 4 ∧ entropyBase 2 pmf_5_9_1 = 7 / 4 ∧
        ¬ IsPrefixCode (![[0, 0], [1], [1, 1, 0], [1, 1, 1]] : Fin 4 → List (Fin 2)) := by
  have hc : sfeCode pmf_5_9_1 = ![[0, 0, 1], [1, 0], [1, 1, 0, 1], [1, 1, 1, 1]] := by
    funext x
    fin_cases x
    · rw [sfeCode_eq_of (l := 3) (N := 1)
        (by rw [shannonLength_of_eq_pow (k := 2) le_rfl (by norm_num [pmf_5_9_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_four, pmf_5_9_1])]
      decide
    · rw [sfeCode_eq_of (l := 2) (N := 2)
        (by rw [shannonLength_of_eq_pow (k := 1) le_rfl (by norm_num [pmf_5_9_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_four, pmf_5_9_1])]
      decide
    · rw [sfeCode_eq_of (l := 4) (N := 13)
        (by rw [shannonLength_of_eq_pow (k := 3) le_rfl (by norm_num [pmf_5_9_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_four, pmf_5_9_1])]
      decide
    · rw [sfeCode_eq_of (l := 4) (N := 15)
        (by rw [shannonLength_of_eq_pow (k := 3) le_rfl (by norm_num [pmf_5_9_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_four, pmf_5_9_1])]
      decide
  refine ⟨hc, ?_, ?_, by unfold IsPrefixCode; decide⟩
  · rw [hc]
    simp [expectedLength, pmf_5_9_1, Fin.sum_univ_four]
    norm_num
  · simp [entropyBase, pmf_5_9_1, Fin.sum_univ_four, logb_two_four, logb_two_eight]
    norm_num

/-- **Example 5.9.2.** For the distribution `(0.25, 0.25, 0.2, 0.15, 0.15)` of Example 5.6.1, the
Shannon–Fano–Elias code is `001, 011, 1001, 1100, 1110`, with average length `3.5` bits, `1.2`
bits longer than the Huffman code. -/
theorem example_5_9_2 :
    sfeCode pmf_5_6_1 = ![[0, 0, 1], [0, 1, 1], [1, 0, 0, 1], [1, 1, 0, 0], [1, 1, 1, 0]] ∧
      expectedLength pmf_5_6_1 (sfeCode pmf_5_6_1) = 7 / 2 ∧
        expectedLength pmf_5_6_1 (sfeCode pmf_5_6_1) - huffmanCost 5 pmf_5_6_1 = 6 / 5 := by
  have hc : sfeCode pmf_5_6_1 =
      ![[0, 0, 1], [0, 1, 1], [1, 0, 0, 1], [1, 1, 0, 0], [1, 1, 1, 0]] := by
    funext x
    fin_cases x
    · rw [sfeCode_eq_of (l := 3) (N := 1)
        (by rw [shannonLength_of_eq_pow (k := 2) le_rfl (by norm_num [pmf_5_6_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_five, pmf_5_6_1])]
      decide
    · rw [sfeCode_eq_of (l := 3) (N := 3)
        (by rw [shannonLength_of_eq_pow (k := 2) le_rfl (by norm_num [pmf_5_6_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_five, pmf_5_6_1])]
      decide
    · rw [sfeCode_eq_of (l := 4) (N := 9)
        (by rw [(shannonLength_eq_iff (k := 3) le_rfl (by norm_num [pmf_5_6_1]) (by norm_num)).2
          (by norm_num [pmf_5_6_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_five, pmf_5_6_1])]
      decide
    · rw [sfeCode_eq_of (l := 4) (N := 12)
        (by rw [(shannonLength_eq_iff (k := 3) le_rfl (by norm_num [pmf_5_6_1]) (by norm_num)).2
          (by norm_num [pmf_5_6_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_five, pmf_5_6_1])]
      decide
    · rw [sfeCode_eq_of (l := 4) (N := 14)
        (by rw [(shannonLength_eq_iff (k := 3) le_rfl (by norm_num [pmf_5_6_1]) (by norm_num)).2
          (by norm_num [pmf_5_6_1])])
        (by norm_num [midCdf, cdfLT, sum_filter, Fin.sum_univ_five, pmf_5_6_1])]
      decide
  have hL : expectedLength pmf_5_6_1 (sfeCode pmf_5_6_1) = 7 / 2 := by
    rw [hc]
    simp [expectedLength, pmf_5_6_1, Fin.sum_univ_five]
    norm_num
  refine ⟨hc, hL, ?_⟩
  rw [hL, huffmanCost_5_6_1]
  norm_num

/-! ## Section 5.10: Competitive optimality of the Shannon code -/

/-- **Section 5.10.** The probability that another code is `5` or more bits shorter than the
Shannon code is at most `2^{1-5} = 1/16`. -/
theorem example_5_10_five_bits {X : Type*} [Fintype X] {p : X → ℝ} (hp : IsPMF p) (l' : X → ℕ)
    (hl' : kraftSum 2 l' ≤ 1) :
    prob p (univ.filter fun x => l' x + 5 ≤ shannonLength 2 p x) ≤ 1 / 16 := by
  have h := prob_shannonLength_ge_add_le hp l' hl' 5
  norm_num at h
  norm_num
  exact h

/-! ## Section 5.11: Generation of discrete distributions from fair coins -/

/-- **Example 5.11.1, (5.98).** The distribution `(1/2, 1/4, 1/4)` of `a, b, c`. -/
def pmf_5_11_1 : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- **Example 5.11.1.** The leaves `0 ↦ a`, `10 ↦ b`, `11 ↦ c` (Figure 5.7). -/
def leaves_5_11_1 : Fin 3 → List Bool := ![[false], [true, false], [true, true]]

lemma leaves_5_11_1_isPrefixCode : IsPrefixCode leaves_5_11_1 := by
  unfold IsPrefixCode
  decide

lemma hasSum_leaves_5_11_1 : HasSum (fun i => (1 / 2 : ℝ) ^ (leaves_5_11_1 i).length) 1 := by
  have h : ∑ i, (1 / 2 : ℝ) ^ (leaves_5_11_1 i).length = 1 := by
    simp [leaves_5_11_1, Fin.sum_univ_three]
    norm_num
  convert hasSum_fintype fun i => (1 / 2 : ℝ) ^ (leaves_5_11_1 i).length using 1
  exact h.symm

/-- **Example 5.11.1.** The algorithm of Figure 5.7. -/
def tree_5_11_1 : CoinTree (Fin 3) :=
  CoinTree.ofCode leaves_5_11_1 leaves_5_11_1_isPrefixCode id hasSum_leaves_5_11_1

/-- **Example 5.11.1.** The tree of Figure 5.7 generates `(1/2, 1/4, 1/4)` with `1.5` fair bits on
average, which is the entropy of the distribution; by Theorem 5.11.1 it is optimal. -/
theorem example_5_11_1 :
    tree_5_11_1.Generates pmf_5_11_1 ∧ tree_5_11_1.expectedFlips = 3 / 2 ∧
      entropyBase 2 pmf_5_11_1 = 3 / 2 ∧ minExpectedFlips pmf_5_11_1 = 3 / 2 := by
  have hgen : tree_5_11_1.Generates pmf_5_11_1 := fun x => by
    rw [tree_5_11_1, CoinTree.outProb_ofCode, tsum_fintype]
    fin_cases x <;> simp [leaves_5_11_1, pmf_5_11_1] <;> norm_num
  have hET : tree_5_11_1.expectedFlips = 3 / 2 := by
    rw [tree_5_11_1, CoinTree.expectedFlips_ofCode, tsum_fintype]
    simp [leaves_5_11_1, Fin.sum_univ_three]
    norm_num
  have hH : entropyBase 2 pmf_5_11_1 = 3 / 2 := by
    simp [entropyBase, pmf_5_11_1, Fin.sum_univ_three, logb_two_four]
    norm_num
  have hfin : tree_5_11_1.FiniteFlips := by
    rw [tree_5_11_1, CoinTree.finiteFlips_ofCode_iff]
    exact Summable.of_finite
  refine ⟨hgen, hET, hH, le_antisymm ?_ ?_⟩
  · rw [← hET]
    exact minExpectedFlips_le hgen hfin
  · rw [← hH]
    exact le_minExpectedFlips ⟨_, hgen, hfin⟩

/-- **Example 5.11.1.** The alternative algorithm `00 ↦ a`, `01 ↦ b`, `10 ↦ c`, `11 ↦ a` also
generates `(1/2, 1/4, 1/4)`, but uses two fair bits per sample. -/
def leaves_5_11_1' : Fin 4 → List Bool :=
  ![[false, false], [false, true], [true, false], [true, true]]

/-- The coin tree of the prefix code `leaves_5_11_1'`. -/
def tree_5_11_1' : CoinTree (Fin 3) :=
  CoinTree.ofCode leaves_5_11_1' (by unfold IsPrefixCode; decide) ![0, 1, 2, 0]
    (by
      have h : ∑ i, (1 / 2 : ℝ) ^ (leaves_5_11_1' i).length = 1 := by
        simp [leaves_5_11_1', Fin.sum_univ_four]
        norm_num
      convert hasSum_fintype fun i => (1 / 2 : ℝ) ^ (leaves_5_11_1' i).length using 1
      exact h.symm)

theorem example_5_11_1' : tree_5_11_1'.Generates pmf_5_11_1 ∧ tree_5_11_1'.expectedFlips = 2 := by
  constructor
  · intro x
    rw [tree_5_11_1', CoinTree.outProb_ofCode, tsum_fintype]
    fin_cases x <;> simp [pmf_5_11_1, leaves_5_11_1', Fin.sum_univ_four] <;> norm_num
  · rw [tree_5_11_1', CoinTree.expectedFlips_ofCode, tsum_fintype]
    simp [leaves_5_11_1', Fin.sum_univ_four]
    norm_num

/-- The binary digit of `t` at `j` from `t 2^j = N + r` with `0 ≤ r < 1`. -/
lemma binDigit_of_eq {t : ℝ} {j N : ℕ} {r : ℝ} (h : t * 2 ^ j = N + r) (h0 : 0 ≤ r)
    (h1 : r < 1) : binDigit t j = N % 2 := by
  rw [binDigit, h, (Nat.floor_eq_iff (by positivity)).2 ⟨by linarith, by linarith⟩]

lemma exists_two_thirds (k : ℕ) : ∃ A : ℕ, (2 / 3 : ℝ) * 2 ^ (2 * k) = A + 2 / 3 := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨A, hA⟩ := ih
    refine ⟨4 * A + 2, ?_⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, ← mul_assoc, hA]
    push_cast
    ring

lemma exists_one_third (k : ℕ) : ∃ B : ℕ, (1 / 3 : ℝ) * 2 ^ (2 * k) = B + 1 / 3 := by
  induction k with
  | zero => exact ⟨0, by norm_num⟩
  | succ k ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨4 * B + 1, ?_⟩
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, ← mul_assoc, hB]
    push_cast
    ring

/-- **Example 5.11.2, (5.110)–(5.114).** The binary expansions `2/3 = 0.101010⋯` and
`1/3 = 0.010101⋯`: the atoms of `2/3` are `1/2, 1/8, 1/32, …` and those of `1/3` are
`1/4, 1/16, 1/64, …`. -/
theorem example_5_11_2 (k : ℕ) :
    binDigit (2 / 3) (2 * k + 1) = 1 ∧ binDigit (2 / 3) (2 * k + 2) = 0 ∧
      binDigit (1 / 3) (2 * k + 1) = 0 ∧ binDigit (1 / 3) (2 * k + 2) = 1 := by
  obtain ⟨A, hA⟩ := exists_two_thirds k
  obtain ⟨B, hB⟩ := exists_one_third k
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [binDigit_of_eq (N := 2 * A + 1) (r := 1 / 3)
      (by rw [pow_succ, ← mul_assoc, hA]; push_cast; ring) (by norm_num) (by norm_num)]
    omega
  · rw [binDigit_of_eq (N := 4 * A + 2) (r := 2 / 3)
      (by rw [pow_add, ← mul_assoc, hA]; push_cast; ring) (by norm_num) (by norm_num)]
    omega
  · rw [binDigit_of_eq (N := 2 * B) (r := 2 / 3)
      (by rw [pow_succ, ← mul_assoc, hB]; push_cast; ring) (by norm_num) (by norm_num)]
    omega
  · rw [binDigit_of_eq (N := 4 * B + 1) (r := 1 / 3)
      (by rw [pow_add, ← mul_assoc, hB]; push_cast; ring) (by norm_num) (by norm_num)]
    omega

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 5.
-/

/-- **Theorem 5.2.1 (Kraft inequality).** -/
alias theorem_5_2_1 := kraft_of_isPrefixCode

/-- **Theorem 5.2.1 (converse).** -/
alias theorem_5_2_1_converse := exists_prefixCode_of_kraft

/-- **Theorem 5.2.2 (extended Kraft inequality).** -/
alias theorem_5_2_2 := summable_kraft_of_isPrefixCode

/-- **Theorem 5.2.2 (converse).** -/
alias theorem_5_2_2_converse := exists_prefixCode_of_summable

/-- **Theorem 5.3.1.** -/
alias theorem_5_3_1 := entropyBase_le_expectedLength

/-- **Theorem 5.4.1.** -/
alias theorem_5_4_1 := minExpectedLength_bounds

/-- **Theorem 5.4.2, (5.40).** -/
alias theorem_5_4_2 := minExpectedLength_process_bounds

/-- **Theorem 5.4.2, (5.41).** -/
alias theorem_5_4_2_tendsto := tendsto_minExpectedLength

/-- **Theorem 5.4.3.** -/
alias theorem_5_4_3 := wrongCode_bounds

/-- **Theorem 5.5.1 (McMillan).** -/
alias theorem_5_5_1 := kraft_of_isUniquelyDecodableCode

/-- **Theorem 5.5.1 (converse).** -/
alias theorem_5_5_1_converse := exists_uniquelyDecodableCode_of_kraft

/-- **Corollary of Theorem 5.5.1** (infinite alphabets). -/
alias corollary_5_5_1 := summable_kraft_of_isUniquelyDecodableCode

/-- **Lemma 5.8.1.** -/
alias lemma_5_8_1 := exists_canonical_lengths

/-- **Theorem 5.8.1.** -/
alias theorem_5_8_1 := huffmanCode_optimal

/-- **Theorem 5.10.1.** `Pr(l(X) ≥ l'(X) + c) ≤ 2^{1-c}` for the Shannon lengths `l`. -/
alias theorem_5_10_1 := prob_shannonLength_ge_add_le

/-- **Theorem 5.10.2.** The Shannon code is competitively optimal for dyadic distributions. -/
alias theorem_5_10_2 := prob_gt_le_prob_lt_of_dyadic

/-- **Theorem 5.10.2 (equality).** -/
alias theorem_5_10_2_eq_iff := prob_gt_eq_prob_lt_iff_of_dyadic

/-- **Corollary of Theorem 5.10.2, (5.97).** -/
alias corollary_5_10_2 := expect_sign_sub_one_le_zero

/-- **Lemma 5.11.1.** The expected depth of a complete tree is the entropy of its leaves. -/
alias lemma_5_11_1 := CoinTree.leafEntropy_eq_expectedFlips

/-- **Theorem 5.11.1.** Generating `X` from fair bits takes `ET ≥ H(X)` bits on average. -/
alias theorem_5_11_1 := CoinTree.entropyBase_le_expectedFlips

/-- **Theorem 5.11.2.** For a dyadic distribution the optimal algorithm has `ET = H(X)`. -/
alias theorem_5_11_2 := minExpectedFlips_eq_of_isDAdic

/-- **Theorem 5.11.3.** The optimal algorithm has `H(X) ≤ ET < H(X) + 2`. -/
alias theorem_5_11_3 := minExpectedFlips_bounds

end InfoTheory.CoverThomas
