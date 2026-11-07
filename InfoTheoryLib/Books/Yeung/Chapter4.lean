/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.CodeTree

/-!
# Yeung, Chapter 4: Zero-Error Data Compression

This file indexes the formalization of Chapter 4 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Codes.** A `D`-ary code is `C : X → List α` with `Fintype.card α = D`.
* **Code trees.** A node of the code tree is a list over the code alphabet. The internal nodes are
  the proper prefixes of the codewords, `internalNodes C`.
* **Two or more symbols.** As in the book, where `m ≥ 2`, the results on code trees assume
  `[Nontrivial X]`. With one symbol, the empty codeword is a prefix code without internal nodes.
* **Positive probabilities.** The bounds `L < H_D(X) + 1` assume `p x > 0`. The book's proof needs
  this for (4.36), and the strict bound fails otherwise: the binary distribution `(1, 0)` has
  `L = 1` and `H₂(X) = 0`.
* **`D`-adic distributions.** `IsDAdic` allows `p x = D⁻⁰ = 1`, which the book's positive `tᵢ` do
  not. Since a `D`-adic distribution has no zero probabilities, this only happens with one symbol.
* **Logarithms.** The entropy in base `D` is `entropyBase D p`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 4.1 The Entropy Bound
* Definitions 4.1 and 4.2: `C : X → List α`, `extension`, `IsUniquelyDecodableCode`
  (`SourceCoding.Code`).
* Example 4.3: `example_4_3` (here).
* Theorem 4.4: `kraft_of_isUniquelyDecodableCode` (`SourceCoding.Kraft`).
* (4.9): `expectedLength` (`SourceCoding.Code`).
* Theorem 4.5: `theorem_4_5` (here). The condition for tightness is `p x = D^{-l x}`, which is the
  book's `l x = -log_D p x` for `p x > 0`.
* Corollary 4.6: `entropy_le_log_card` (`Entropy.Bounds`), proved directly, not from Theorem 4.5.
* Definition 4.7: `codeRedundancy` (`SourceCoding.CodeTree`).

### 4.2 Prefix Codes
* Definition 4.8: `IsPrefixCode` (`SourceCoding.Code`).
* Example 4.9: `example_4_9` (here).
* A prefix code is uniquely decodable: `IsPrefixCode.isUniquelyDecodableCode'`
  (`SourceCoding.Code`).
* Theorem 4.10: `theorem_4_10` (here).
* Corollary 4.11: `exists_prefixCode_eq_entropyBase_iff` (`SourceCoding.CodeTree`), with `IsDAdic`
  (`SourceCoding.OptimalLength`).
* The Huffman procedure: `huffmanCost`, `huffmanLengths`, `huffmanCode` (`SourceCoding.Huffman`), in
  the binary case, to which the book restricts its proofs.
* Example 4.12: `example_4_12` (here).
* Example 4.13: `example_4_13` (here), and `exists_dummy_symbols` (`SourceCoding.CodeTree`) for the
  number of dummy symbols.
* Lemma 4.14: `length_le_of_isOptimal` (`SourceCoding.CodeTree`).
* Lemma 4.15: `exists_optimal_prefixCode_siblings` (`SourceCoding.CodeTree`).
* (4.31)–(4.34): `huffmanCost_succ_succ` (`SourceCoding.Huffman`).
* Theorem 4.16: `theorem_4_16` (here).
* Theorem 4.17: `expectedLength_huffmanCode_lt` (`SourceCoding.CodeTree`) for binary Huffman codes,
  `minExpectedLength_bounds` (`SourceCoding.OptimalLength`) for the optimal `D`-ary length, and
  `minExpectedLength_tightPMF`, `tendsto_entropyBase_add_one_sub_minExpectedLength`
  (`SourceCoding.CodeTree`) for the tightness, by the distributions (4.45) in `tightPMF`.
* (4.36)–(4.43), the Shannon code: `shannonLength`, `exists_prefixCode_shannon`
  (`SourceCoding.OptimalLength`).
* (4.46)–(4.48): `minExpectedLength_iid_bounds` (`SourceCoding.OptimalLength`).

### 4.3 Redundancy of Prefix Codes
* (4.51)–(4.53): `internalNodes`, `reachProb`, `branchProb`, `sum_branchProb`, `nodeEntropy`
  (`SourceCoding.CodeTree`).
* Lemmas 4.18 and 4.19: `entropyBase_eq_sum_reachProb_mul_nodeEntropy`,
  `expectedLength_eq_sum_reachProb` (`SourceCoding.CodeTree`).
* (4.65): `localRedundancy`, `localRedundancy_nonneg`, `localRedundancy_eq_zero_iff`
  (`SourceCoding.CodeTree`).
* Theorem 4.20: `codeRedundancy_eq_sum_localRedundancy` (`SourceCoding.CodeTree`).
* Corollary 4.21: `codeRedundancy_nonneg`, `codeRedundancy_eq_zero_iff`
  (`SourceCoding.CodeTree`).
* Example 4.22: `sum_localRedundancy_le_codeRedundancy`,
  `localRedundancy_siblings_le_codeRedundancy` (`SourceCoding.CodeTree`). (4.72) is stated for any
  binary prefix code in which the two symbols are siblings, which is the case in the Huffman
  procedure.

## Not formalized

* The `D`-ary Huffman procedure for `D > 2`. The book describes it and leaves its optimality as a
  straightforward extension. `minExpectedLength` is the optimal `D`-ary expected length.
* The numerical value `2.202` bits of the entropy in Example 4.12.
* Figures 4.1 and 4.2. The proof of Lemma 4.18 here is a telescoping sum over the nodes, and not the
  book's induction on the number of internal nodes.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 4
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {X α : Type*} [Fintype X] [Fintype α]

/-! ### Worked examples -/

/-- The code of **Example 4.3**, for the symbols `A, B, C, D`: `0, 1, 01, 10`. -/
def code_4_3 : Fin 4 → List (Fin 2) := ![[0], [1], [0, 1], [1, 0]]

/-- **Example 4.3.** The source sequences `AAD`, `ACA` and `AABA` all give the code sequence `0010`,
so the code is not uniquely decodable. -/
theorem example_4_3 :
    extension code_4_3 [0, 0, 3] = [0, 0, 1, 0] ∧ extension code_4_3 [0, 2, 0] = [0, 0, 1, 0] ∧
      extension code_4_3 [0, 0, 1, 0] = [0, 0, 1, 0] ∧ ¬ IsUniquelyDecodableCode code_4_3 := by
  refine ⟨by decide, by decide, by decide, fun h => ?_⟩
  have h₁ : extension code_4_3 [0, 0, 3] = extension code_4_3 [0, 2, 0] := by decide
  exact absurd (h h₁) (by decide)

/-- The prefix code `C'` of **Example 4.9**: `0, 10, 110, 1111`. -/
def code_4_9 : Fin 4 → List (Fin 2) := ![[0], [1, 0], [1, 1, 0], [1, 1, 1, 1]]

/-- **Example 4.9.** The code of Example 4.3 is not a prefix code, and `C'` is one. The source
sequence `BCDAC` gives the code sequence `1011011110110`. -/
theorem example_4_9 :
    ¬ IsPrefixCode code_4_3 ∧ IsPrefixCode code_4_9 ∧
      extension code_4_9 [1, 2, 3, 0, 2] = [1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0] := by
  refine ⟨?_, ?_, by decide⟩
  · unfold IsPrefixCode
    decide
  · unfold IsPrefixCode
    decide

/-- The distribution of **Example 4.12**, `0.35, 0.1, 0.15, 0.2, 0.2`. -/
def pmf_4_12 : Fin 5 → ℝ := ![7 / 20, 1 / 10, 3 / 20, 1 / 5, 1 / 5]

/-- The binary code of **Example 4.12**: `00, 010, 011, 10, 11`. -/
def code_4_12 : Fin 5 → List (Fin 2) := ![[0, 0], [0, 1, 0], [0, 1, 1], [1, 0], [1, 1]]

lemma pmf_4_12_isPMF : IsPMF pmf_4_12 :=
  ⟨fun x => by fin_cases x <;> norm_num [pmf_4_12],
    by simp [pmf_4_12, Fin.sum_univ_five]; norm_num⟩

/-- **Example 4.12.** The Huffman procedure merges `0.1 + 0.15 = 0.25`, `0.2 + 0.2 = 0.4`,
`0.35 + 0.25 = 0.6` and `0.6 + 0.4 = 1`, for a total cost of `2.25`. -/
theorem huffmanCost_4_12 : huffmanCost 5 pmf_4_12 = 9 / 4 := by
  have s5 : huffmanCost 5 pmf_4_12 = 1 / 4 + huffmanCost 4 ![1 / 4, 1 / 5, 1 / 5, 7 / 20] :=
    huffmanCost_step _ (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4)
      (Fin.monotone_iff_le_succ.2 fun i => by
        fin_cases i <;> norm_num [pmf_4_12, Equiv.swap_apply_def])
      (by norm_num [pmf_4_12, Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, pmf_4_12, Equiv.swap_apply_def])
  have s4 : huffmanCost 4 ![1 / 4, 1 / 5, 1 / 5, 7 / 20] =
      2 / 5 + huffmanCost 3 ![2 / 5, 1 / 4, 7 / 20] :=
    huffmanCost_step _ (Equiv.swap 0 1 * Equiv.swap 1 2)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, Equiv.swap_apply_def])
  have s3 : huffmanCost 3 ![2 / 5, 1 / 4, 7 / 20] = 3 / 5 + huffmanCost 2 ![3 / 5, 2 / 5] :=
    huffmanCost_step _ (Equiv.swap 0 1 * Equiv.swap 1 2)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def])
      (by funext i; fin_cases i <;> norm_num [huffmanMerge_eq, Equiv.swap_apply_def])
  have s2 : huffmanCost 2 ![3 / 5, 2 / 5] = 1 :=
    (huffmanCost_step (a := 1) _ (Equiv.swap 0 1)
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i; norm_num [Equiv.swap_apply_def])
      (by norm_num [Equiv.swap_apply_def]) rfl).trans (by simp)
  rw [s5, s4, s3, s2]
  norm_num

/-- **Example 4.12, (4.28).** The code is a prefix code with expected length `2.25`, the cost of the
Huffman procedure, and this is the optimal expected length over all binary uniquely decodable codes.
-/
theorem example_4_12 :
    IsPrefixCode code_4_12 ∧ expectedLength pmf_4_12 code_4_12 = 9 / 4 ∧
      ∀ C : Fin 5 → List (Fin 2), IsUniquelyDecodableCode C →
        expectedLength pmf_4_12 code_4_12 ≤ expectedLength pmf_4_12 C := by
  have hL : expectedLength pmf_4_12 code_4_12 = 9 / 4 := by
    simp [expectedLength, pmf_4_12, code_4_12, Fin.sum_univ_five]
    norm_num
  refine ⟨?_, hL, fun C hC => ?_⟩
  · unfold IsPrefixCode
    decide
  · rw [hL, ← huffmanCost_4_12]
    exact huffmanCost_le_expectedLength pmf_4_12_isPMF.nonneg (by simp) hC

/-- **Example 4.13.** For a quaternary code for the source of Example 4.12, two dummy symbols make
the number of symbols `7 = 4 + 1 · 3`, and at most `D - 2` are needed in general. -/
theorem example_4_13 : 5 + 2 = 4 + 1 * (4 - 1) ∧ 2 ≤ 4 - 2 := by
  norm_num

/-! ### Aliases -/

/-- **Theorem 4.4 (Kraft Inequality).** (4.2) -/
alias theorem_4_4 := kraft_of_isUniquelyDecodableCode

/-- **Theorem 4.5 (Entropy Bound).** (4.11) -/
theorem theorem_4_5 [Nonempty α] (hα : 2 ≤ Fintype.card α) {p : X → ℝ} (hp : IsPMF p)
    {C : X → List α} (hC : IsUniquelyDecodableCode C) :
    entropyBase (Fintype.card α) p ≤ expectedLength p C ∧
      (entropyBase (Fintype.card α) p = expectedLength p C ↔
        ∀ x, p x = (1 / (Fintype.card α : ℝ)) ^ (C x).length) :=
  ⟨entropyBase_le_expectedLength hp hα _ (kraft_of_isUniquelyDecodableCode hC),
    entropyBase_eq_expectedLength_iff hp hα _ (kraft_of_isUniquelyDecodableCode hC)⟩

/-- **Corollary 4.6.** -/
alias corollary_4_6 := entropy_le_log_card

/-- **Theorem 4.10.** (4.23) -/
theorem theorem_4_10 [Nonempty α] (l : X → ℕ) :
    (∃ C : X → List α, IsPrefixCode C ∧ ∀ x, (C x).length = l x) ↔
      ∑ x, (1 / (Fintype.card α : ℝ)) ^ l x ≤ 1 :=
  ⟨fun ⟨C, hC, hl⟩ => by simpa [hl] using kraft_of_isPrefixCode hC, exists_prefixCode_of_kraft l⟩

/-- **Corollary 4.11.** -/
alias corollary_4_11 := exists_prefixCode_eq_entropyBase_iff

/-- **Lemma 4.14.** -/
alias lemma_4_14 := length_le_of_isOptimal

/-- **Lemma 4.15.** -/
alias lemma_4_15 := exists_optimal_prefixCode_siblings

/-- **Theorem 4.16.** The Huffman procedure produces an optimal prefix code. -/
theorem theorem_4_16 [Nonempty X] {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) :
    IsPrefixCode (huffmanCode p) ∧ ∀ C' : X → List Bool, IsUniquelyDecodableCode C' →
      expectedLength p (huffmanCode p) ≤ expectedLength p C' :=
  ⟨huffmanCode_isPrefixCode p, fun _ h => huffmanCode_optimal hp h⟩

/-- **Theorem 4.17.** (4.35), for binary Huffman codes. -/
alias theorem_4_17 := expectedLength_huffmanCode_lt

/-- **Lemma 4.18.** -/
alias lemma_4_18 := entropyBase_eq_sum_reachProb_mul_nodeEntropy

/-- **Lemma 4.19.** -/
alias lemma_4_19 := expectedLength_eq_sum_reachProb

/-- **Theorem 4.20 (Local Redundancy Theorem).** (4.66) -/
alias theorem_4_20 := codeRedundancy_eq_sum_localRedundancy

/-- **Corollary 4.21 (Entropy Bound).** -/
theorem corollary_4_21 [Nontrivial X] [DecidableEq α] (hα : 2 ≤ Fintype.card α)
    {C : X → List α} (hC : IsPrefixCode C) {p : X → ℝ} (hp : IsPMF p) :
    0 ≤ codeRedundancy p C ∧ (codeRedundancy p C = 0 ↔
      ∀ k ∈ internalNodes C, ∀ j, branchProb p C k j = reachProb p C k / Fintype.card α) :=
  ⟨codeRedundancy_nonneg hα hC hp, codeRedundancy_eq_zero_iff hα hC hp⟩

/-- **Example 4.22.** (4.71) -/
alias example_4_22 := sum_localRedundancy_le_codeRedundancy

end InfoTheory.Yeung
