/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter13
public import InfoTheoryLib.Kolmogorov.Computer
public import InfoTheoryLib.Kolmogorov.Programs
public import InfoTheoryLib.Kolmogorov.BinaryStrings
public import InfoTheoryLib.Kolmogorov.Entropy
public import InfoTheoryLib.Kolmogorov.UniversalProbability
public import InfoTheoryLib.Kolmogorov.Universal
public import InfoTheoryLib.Kolmogorov.Noncomputable

/-!
# Cover & Thomas, Chapter 14: Kolmogorov Complexity

This file indexes the formalization of Chapter 14 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_14_2_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Computers.** A computer (`Computer`) is a partial recursive function, in the sense of
  Mathlib's `Partrec₂`, of a binary program `p : List Bool` and a side information `y : ℕ`, whose
  halting programs form a prefix-free set for each `y` (Section 14.1). A computer `U` is
  universal (`Computer.IsUniversal`) if for every computer `A` a fixed prefix `s_A` makes
  `U(s_A p, y) = A(p, y)`. The results hold for every universal computer, and one is
  constructed from Mathlib's universal partial recursive function (`exists_isUniversal`).
* **Complexity.** `Computer.complexity U x y` is `K(x | y)`; `K(x)` is `K(x | 0)`, and
  `K(x | l(x))` is `K(x | x.length)`. Complexities and code lengths are in bits, and entropies in
  bits are `binEntropy / log 2` (the book's `H₀`) and `entropyBase 2`.
* **Constructions.** Every program used to bound a complexity is a concrete computer whose
  computability is proved (`Kolmogorov.Programs`, `Kolmogorov.BinaryStrings`).

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 14.1–14.2 Kolmogorov complexity
* Section 14.1: `Computer`, `Computer.IsUniversal` (`Kolmogorov.Computer`); a universal
  computer: `universalComputer`, `universalComputer_isUniversal`, `exists_isUniversal`
  (`Kolmogorov.Universal`).
* (14.1)–(14.2): `Computer.complexity`, `Computer.HasProgram`, `Computer.complexity_le`,
  `Computer.exists_program_eq_complexity`.
* Theorem 14.2.1, (14.3)–(14.5): `Computer.IsUniversal.complexity_le`; (14.6):
  `Computer.IsUniversal.abs_complexity_sub_le`.
* Theorem 14.2.2, (14.7): `complexity_length_le`, with `lengthComputer`
  (`Kolmogorov.Programs`).
* Theorem 14.2.3, (14.8): `complexity_le_complexity_length_add`, with the self-delimiting code
  `eliasGamma` and its decoder `sdParse` (`sdParse_eliasGamma_append`,
  `eq_of_sdParse_eq_some`, `primrec_sdParse`) and `Computer.withLength`; every string has a
  program, `Computer.IsUniversal.hasProgram_all`, and `complexity_le_length_add`.
* Theorem 14.2.4, (14.10)–(14.12): `Computer.card_lt_two_pow_of_complexity_lt`.
* Example 14.2.1, (14.15): `complexity_zeros_le`; Example 14.2.4, (14.18):
  `complexity_alternating_le`.
* Example 14.2.7: `natComplexity_le` (`Kolmogorov.Entropy`).
* Example 14.2.8 and Theorem 14.2.5, (14.21)–(14.24): `allStrings`, `typeList`,
  `length_typeList`, `typeIndexComputer`, `complexity_le_log_choose`,
  `complexity_le_binEntropy`, `complexity_le_binEntropy_sub` (`Kolmogorov.BinaryStrings`).

### 14.3 Kolmogorov complexity and entropy
* Lemma 14.3.1, (14.26): `Computer.tsum_halting_le_one`; for the complexities,
  `Computer.sum_two_pow_neg_complexity_le_one`.
* Theorem 14.3.1, (14.27)–(14.33): `entropy_le_expected_complexity`, `expected_complexity_le`,
  `tendsto_expected_complexity_div` (`Kolmogorov.Entropy`).
* (14.36)–(14.37): `tendsto_expected_complexity_div'`.

### 14.4 Kolmogorov complexity of integers
* (14.38): `natString`, `Computer.natComplexity`.
* Theorem 14.4.1, (14.39): `natComplexity_le_of_universal`.
* Theorem 14.4.2, (14.40): `natComplexity_le`.
* Theorem 14.4.3, (14.41)–(14.43): `exists_natComplexity_gt`.

### 14.5 Algorithmically random and incompressible sequences
* Theorem 14.5.1, (14.44)–(14.48): `prob_complexity_lt_le`; `example_14_5_1` (here).
* (14.49)–(14.50): `exists_random`.
* (14.51): `IsIncompressible`.
* Theorem 14.5.2, (14.52)–(14.57): `IsIncompressible.tendsto_ones_div`, with
  `two_mul_sq_le_log_two_sub`.
* Theorem 14.5.3, (14.58)–(14.65): `tendstoInProb_complexity_div`, from
  `tendsto_prob_complexity_ge` and `tendsto_prob_complexity_le`.

### 14.6 Universal probability
* (14.66): `Computer.universalProb`, `Computer.universalProb_le_one`
  (`Kolmogorov.UniversalProbability`).
* Theorem 14.6.1, (14.67)–(14.68): `Computer.IsUniversal.universalProb_ge`.

### 14.7 The halting problem and the noncomputability of Kolmogorov complexity
* The Berry paradox: `berryComputer`, `not_computable_complexity` (`Kolmogorov.Noncomputable`).

### 14.8 Ω
* (14.70): `Computer.omega`, `Computer.omega_le_one`, `Computer.IsUniversal.omega_pos`.

### 14.9 Universal gambling
* (14.76)–(14.77): `Computer.gamblingWealth`, `Computer.summable_two_pow_neg_complexity`,
  `Computer.tsum_two_pow_neg_complexity_le_omega`.
* Theorem 14.9.1, (14.78)–(14.79): `Computer.length_le_logb_gamblingWealth_add`.

### 14.10 Occam's razor
* Laplace's rule of succession, (14.82)–(14.83): `example_14_83` (here).

### 14.11 Kolmogorov complexity and universal probability
* Theorem 14.11.1, lower half, (14.89)–(14.91): `Computer.two_pow_neg_complexity_le_universalProb`,
  `Computer.logb_inv_universalProb_le`.

### 14.12 Kolmogorov sufficient statistic
* (14.107): `Computer.indicatorString`, `Computer.structureFunction`, with
  `Computer.structureFunction_antitone`, `Computer.IsUniversal.structureFunction_le_length`,
  `Computer.IsUniversal.structureFunction_eq_zero`.
* (14.108): `Computer.minimalSufficientLength`.

## Not formalized

* Turing machines (Section 14.1): computers are partial recursive functions (Church's thesis).
* The refinement (14.9) of Theorem 14.2.3 and the bounds (14.20), (14.40) with `log* n`: we prove
  them with `2 log₂ (l + 1)` and `2 log₂ (log₂ (n + 1) + 1)`; the convention `K(x | y, y*)`.
* Examples 14.2.2, 14.2.3, 14.2.5 and 14.2.6 (`π`, weather, fractals, the Mona Lisa), and the
  bound (14.24) with `½ log n` for all strings: Theorem 14.2.5 is proved with `log₂ (n + 1)` in
  place of `½ log₂ n`, and with `½ log₂ n` and an extra term for `0 < k < n` (see
  `Kolmogorov.BinaryStrings`).
* The upper bound of Theorem 14.3.1 for alphabets with more than two letters, (14.34)–(14.35).
* The discussion of the halting problem in Section 14.7 (Mathlib proves it,
  `ComputablePred.halting_problem`), the properties of `Ω` (noncomputability, deciding
  theorems) and Theorem 14.8.1.
* The heuristic (14.84)–(14.86) of Occam's razor.
* The upper half of Theorem 14.11.1 (the code tree construction (14.92)–(14.106)).
* The examples of Section 14.12 and the minimum description length principle (Section 14.13).
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 14.5: an example -/

/-- **Section 14.5** Fewer than `1/32` of the sequences of length `n` have complexity less than
`n - 5`. -/
theorem example_14_5_1 {U : Computer} (hU : U.IsUniversal) {n : ℕ} (hn : 5 ≤ n) :
    ∑ _x ∈ univ.filter (fun x : Fin n → Bool => U.complexity (List.ofFn x) n < n - 5),
      (1 / 2 : ℝ) ^ n < 1 / 32 := by
  have h := prob_complexity_lt_le hU hn
  norm_num at h ⊢
  exact h

/-! ## Section 14.10: Laplace's rule of succession -/

/-- **(14.82)–(14.83) Laplace's rule of succession.** Under a uniform prior on the probability of
sunrise, the sun rises on day `n + 1`, having risen on days `1, …, n`, with probability
`(n + 1)/(n + 2)`. -/
theorem example_14_83 (n : ℕ) :
    laplaceMixture (n + 1) (Fin.snoc (fun _ : Fin n => true) true) =
      laplaceMixture n (fun _ => true) * ((n + 1) / (n + 2)) := by
  rw [laplaceMixture_snoc_true]
  congr 2
  simp [onesCount]

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 14.
-/

/-- **Theorem 14.2.1 (Universality of Kolmogorov complexity).** -/
alias theorem_14_2_1 := Computer.IsUniversal.complexity_le

/-- **Theorem 14.2.2 (Conditional complexity is less than the length of the sequence).** -/
alias theorem_14_2_2 := complexity_length_le

/-- **Theorem 14.2.3 (Upper bound on Kolmogorov complexity).** -/
alias theorem_14_2_3 := complexity_le_complexity_length_add

/-- **Theorem 14.2.4 (Lower bound on Kolmogorov complexity).** -/
alias theorem_14_2_4 := Computer.card_lt_two_pow_of_complexity_lt

/-- **Theorem 14.2.5**, with `log₂ (n + 1)` in place of the book's `½ log₂ n`. -/
alias theorem_14_2_5 := complexity_le_binEntropy

/-- **Lemma 14.3.1.** -/
alias lemma_14_3_1 := Computer.tsum_halting_le_one

/-- **Theorem 14.3.1 (Relationship of Kolmogorov complexity and entropy).** -/
alias theorem_14_3_1 := tendsto_expected_complexity_div

/-- **Theorem 14.4.1.** -/
alias theorem_14_4_1 := natComplexity_le_of_universal

/-- **Theorem 14.4.2.** -/
alias theorem_14_4_2 := natComplexity_le

/-- **Theorem 14.4.3.** -/
alias theorem_14_4_3 := exists_natComplexity_gt

/-- **Theorem 14.5.1.** -/
alias theorem_14_5_1 := prob_complexity_lt_le

/-- **Theorem 14.5.2 (Strong law of large numbers for incompressible sequences).** -/
alias theorem_14_5_2 := IsIncompressible.tendsto_ones_div

/-- **Theorem 14.5.3.** -/
alias theorem_14_5_3 := tendstoInProb_complexity_div

/-- **Theorem 14.6.1.** -/
alias theorem_14_6_1 := Computer.IsUniversal.universalProb_ge

/-- **Theorem 14.9.1.** -/
alias theorem_14_9_1 := Computer.length_le_logb_gamblingWealth_add

/-- **Section 14.7** Kolmogorov complexity is not computable. -/
alias noncomputability_of_complexity := not_computable_complexity

/-- **Theorem 14.11.1 (lower half).** -/
alias theorem_14_11_1_lower := Computer.two_pow_neg_complexity_le_universalProb

end InfoTheory.CoverThomas
