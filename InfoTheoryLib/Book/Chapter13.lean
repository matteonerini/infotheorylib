/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Book.Chapter12
public import InfoTheoryLib.SourceCoding.Minimax
public import InfoTheoryLib.SourceCoding.BinarySequences
public import InfoTheoryLib.SourceCoding.Arithmetic
public import InfoTheoryLib.SourceCoding.LempelZiv
public import InfoTheoryLib.SourceCoding.IntegerCode
public import InfoTheoryLib.SourceCoding.RecurrenceTime
public import InfoTheoryLib.SourceCoding.LempelZivOptimality

/-!
# Cover & Thomas, Chapter 13: Universal Source Coding

This file indexes the formalization of Chapter 13 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_13_1_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Units.** Entropies, redundancies and ideal code lengths are in nats; code lengths of actual
  binary codes are in bits and are multiplied by `log 2` when compared with entropies.
* **Redundancy.** The family `{p_θ}` is a channel `W : α → β → ℝ` (one row per `θ`), and the
  integer constraint on the code lengths is ignored, as in the book.
* **Strings.** Binary sequences are `Fin n → Bool` in Section 13.2 and `List Bool` for the
  Lempel–Ziv algorithms, which work over any alphabet with decidable equality.
* **Processes.** Processes are given by their finite-dimensional laws on the times
  `0, 1, 2, …` (`StochasticProcess`). Recurrence times are measured forward from an occurrence at
  time `0`, which by stationarity has the law of the book's backward recurrence time; ergodicity
  is replaced by the assumption that the blocks recur with probability one
  (`StochasticProcess.BlocksRecurrent`).
* **Lempel–Ziv optimality.** Theorems 13.5.2 and 13.5.3 are proved as deterministic bounds,
  uniform over all strings and all `k`-th order Markov models `Q_k`, and stated for sequences
  along which `-(1/n) log Q_k(x₁ ⋯ xₙ | s₁)` converges.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 13.1 Universal codes and channel capacity
* (13.1)–(13.6), the redundancy `R(p_θ, q) = D(p_θ ‖ q)`: `redundancy`,
  `redundancy_eq_relEntropyReal` (`SourceCoding.Minimax`).
* (13.14)–(13.20): `sum_relEntropy_eq`, with (13.15) `relEntropy_jointOf_prodDist_eq_sum`.
* (13.21)–(13.23): `mutualInfoOf_le_sum_relEntropy`, `mutualInfoOf_eq_sum_relEntropy`.
* Theorem 13.1.1, (13.11)–(13.12), (13.24)–(13.29): `isLeast_maxRedundancy`, from
  `exists_capacity_le_relEntropy` and `relEntropy_le_capacity`; the minimax distribution is unique
  (`eq_outDist_of_relEntropy_le_capacity`) and is at distance `C` from the rows charged by a
  capacity-achieving input (`relEntropy_eq_capacity`).
* Example 13.1.1, (13.30): `example_13_1_1` (here).

### 13.2 Universal coding for binary sequences
* (13.31), upper bound: `choose_le_sqrt_mul_exp_binEntropy`, from Stirling's formula
  (`SourceCoding.BinarySequences`); `choose_le_exp_binEntropy`.
* (13.32)–(13.34), the two-stage description: `twoStageLength`, `twoStageLength_le`.
* (13.35)–(13.38): `bernoulliSeqProb`, `integral_pow_mul_one_sub_pow`, `laplaceMixture`,
  `laplaceMixture_eq_integral`, `laplaceMixture_isPMF`.
* (13.39)–(13.40): `log_inv_laplaceMixture`, `log_inv_laplaceMixture_le`; the uniform bound
  `log_inv_laplaceMixture_le_uniform`.
* (13.41)–(13.44), the Laplace estimate: `laplaceMixture_snoc_true`, `laplaceMixture_snoc_false`.

### 13.3 Arithmetic coding
* Lemma 13.3.1: `map_cdf_eq_uniform` (`SourceCoding.Arithmetic`).
* (13.53)–(13.59): `cdfLT_lex`, `leftSubtreeProb` (`SourceCoding.ShannonFanoEliasBlock`), and for
  i.i.d. sources `cdfLT_lex_iid`; the arithmetic coding intervals `arithStep`, `arithInterval`,
  `arithInterval_ofFn`, `arithInterval_append_subset`, `eq_of_mem_arithInterval`.
* The code of length `log 1/p(xⁿ) + 2` bits: `blockSfeCode`, `expectedLength_blockSfeCode_lt`.
* Example 13.3.1, (13.56)–(13.58): `example_13_3_1` (here).
* Example 13.3.2: `example_13_3_2` (here).

### 13.4 Lempel–Ziv coding
* Section 13.4.1, LZ77: `LZ77Token`, `lcpLength`, `lz77Best`, `lz77Encode`, `lz77Decode`
  (`SourceCoding.LempelZiv`); the example parsing: `example_13_4_1`, `example_13_4_1_decode`
  (here).
* Section 13.4.2, LZ78: `lz78Parse`, `lz78Parse_flatten`, `lz78Parse_nodup`, `lz78Parse_last`,
  `lz78Parse_prefixClosed`, `lz78Encode`, `lz78Decode`, `lz78Decode_encode`; the example parsing:
  `example_13_4_2` (here).

### 13.5 Optimality of Lempel–Ziv algorithms
* Lemma 13.5.1, (13.61): `eliasGamma`, `eliasGamma_isPrefixCode`, `eliasDelta`,
  `eliasDelta_isPrefixCode`, `length_eliasDelta_le`, `length_eliasDelta_le'`
  (`SourceCoding.IntegerCode`).
* (13.62): `StochasticProcess.recurrenceDist`, `StochasticProcess.firstReturnProb`
  (`StochasticProcess.Recurrence`).
* Lemma 13.5.2 (Kac), (13.63), (13.65)–(13.72): `StochasticProcess.hasSum_mul_firstReturnProb`,
  with the finite identity `StochasticProcess.sum_range_mul_firstReturnProb` and Poincaré
  recurrence `StochasticProcess.hasSum_firstReturnProb`; (13.64): `example_13_64` (here).
* Corollary (13.73): `StochasticProcess.blocks`, `StochasticProcess.blocks_isStationary`,
  `StochasticProcess.blocks_law_one`.
* Theorem 13.5.1, (13.74)–(13.83): `StochasticProcess.eventually_expectedRecurrenceLength_le`,
  from `StochasticProcess.expected_log_recurrence_le`,
  `StochasticProcess.expected_log_log_recurrence_le` and
  `StochasticProcess.expectedRecurrenceLength_eliasDelta_le` (`SourceCoding.RecurrenceTime`).
* Lemma 13.5.3, (13.84)–(13.96): `mul_length_le_of_nodup`, `length_mul_le_of_nodup`,
  `exists_length_le_mul_of_nodup` (`SourceCoding.LempelZivOptimality`).
* Lemma 13.5.4, (13.97): `entropy_le_of_mean`.
* (13.98), (13.102)–(13.103): `markovProb`, `phraseState`, `phraseCount`, `sum_phraseCount`,
  `sum_phraseCount_mul`.
* Lemma 13.5.5 (Ziv's inequality), (13.104)–(13.111): `log_markovProb_le`, with
  `markovProb_flatten` and `sum_fiber_markovProb_le`.
* Theorem 13.5.2, (13.112)–(13.126): `length_mul_log_length_le`,
  `exists_length_mul_log_length_le`, `eventually_length_mul_log_length_le`.
* Theorem 13.5.3, (13.129)–(13.130): `lz78Length`, `exists_lz78Length_le`,
  `eventually_lz78Length_le`.

## Not formalized

* Figures 13.1–13.3 and the chapter summary.
* The minimax theorem of game theory (13.26), which our proof of Theorem 13.1.1 does not need.
* The lower bound in (13.31), the Dirichlet(½, ½) mixture (13.45)–(13.47) and its redundancy bound
  (13.46), stated without proof in the book, and the asymptotic redundancy (13.136).
* The finite-precision implementation of arithmetic coding, and the claim that the bits of
  `F(X)` are i.i.d. Bernoulli(½) for a distribution on infinite sequences without atoms.
* The general correctness of the LZ77 decoder (checked on the book's example), Welch's variant of
  LZ78, and the optimality of LZ77 with a finite window, which the book also does not prove.
* Ergodicity: Kac's lemma and Theorem 13.5.1 assume that blocks recur with probability one; the
  lower bound `E Lₙ ≥ H(X₀ⁿ⁻¹)` in Theorem 13.5.1, since the code depends on the infinite past.
* The ergodic theorem (13.99)–(13.101) and the limit `k → ∞` (13.127)–(13.128), which turn the
  deterministic bounds of Theorems 13.5.2 and 13.5.3 into the almost sure statements.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 13.1: Example 13.1.1 -/

/-- The two source distributions of Example 13.1.1, `p₁ = (1 - α, α, 0)` and
`p₂ = (0, α, 1 - α)`, as the rows of a channel. -/
def example1311Channel (α : ℝ) : Fin 2 → Fin 3 → ℝ := ![![1 - α, α, 0], ![0, α, 1 - α]]

/-- The midpoint `q = ((1 - α)/2, α, (1 - α)/2)` of the two distributions. -/
def example1311Mid (α : ℝ) : Fin 3 → ℝ := ![(1 - α) / 2, α, (1 - α) / 2]

lemma example1311Channel_isChannel {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    IsChannel (example1311Channel α) := by
  intro i
  refine ⟨fun y => ?_, ?_⟩
  · fin_cases i <;> fin_cases y <;> simp [example1311Channel] <;> linarith
  · fin_cases i <;> simp [example1311Channel, Fin.sum_univ_three]

lemma example1311Mid_isPMF {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : IsPMF (example1311Mid α) := by
  refine ⟨fun y => ?_, ?_⟩
  · fin_cases y <;> simp [example1311Mid] <;> linarith
  · simp only [example1311Mid, Fin.sum_univ_three]
    simp
    ring

lemma relEntropy_example1311 {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (i : Fin 2) :
    relEntropyReal (example1311Channel α i) (example1311Mid α) = (1 - α) * log 2 := by
  have h : (1 - α) / ((1 - α) / 2) = 2 := by field_simp
  fin_cases i <;>
    simp [relEntropyReal, example1311Channel, example1311Mid, Fin.sum_univ_three, h,
      div_self h0.ne']

/-- **Example 13.1.1, (13.30).** For the two distributions `p₁ = (1 - α, α, 0)` and
`p₂ = (0, α, 1 - α)`, the midpoint `q = ((1 - α)/2, α, (1 - α)/2)` has redundancy
`D(p₁ ‖ q) = D(p₂ ‖ q) = (1 - α) log 2`, which is the capacity of the channel with rows `p₁, p₂`
(an erasure channel), and `q` is the minimax coding distribution. -/
theorem example_13_1_1 {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (∀ i, relEntropyReal (example1311Channel α i) (example1311Mid α) = (1 - α) * log 2) ∧
      capacity (example1311Channel α) = (1 - α) * log 2 := by
  refine ⟨relEntropy_example1311 h0 h1, le_antisymm ?_ ?_⟩
  · -- `C ≤ max_θ D(p_θ ‖ q)`.
    refine (isLeast_maxRedundancy (example1311Channel_isChannel h0.le h1.le)).2
      ⟨example1311Mid α, example1311Mid_isPMF h0.le h1.le, fun i y hy => ?_,
        fun i => (relEntropy_example1311 h0 h1 i).le⟩
    fin_cases i <;> fin_cases y <;> simp_all [example1311Channel, example1311Mid]
  · -- The uniform input achieves `(1 - α) log 2`.
    have hW := example1311Channel_isChannel h0.le h1.le
    have hout : outDist (uniformPMF (Fin 2)) (example1311Channel α) = example1311Mid α := by
      funext y
      fin_cases y <;> simp [outDist, uniformPMF, example1311Channel, example1311Mid] <;> ring
    have hI := mutualInfoOf_eq_sum_relEntropy uniformPMF_isPMF hW
    rw [hout] at hI
    simp only [relEntropy_example1311 h0 h1, Fin.sum_univ_two, uniformPMF] at hI
    have := mutualInfoOf_le_capacity uniformPMF_isPMF hW
    rw [hI] at this
    norm_num at this
    linarith

/-! ## Section 13.3: arithmetic coding -/

/-- **Example 13.3.1, (13.56)–(13.58).** For a Bernoulli(`p`) source (`q = 1 - p`), the
sequence `110101` has `F(xⁿ⁻) = q + pq + p²q² + p³q³`. -/
theorem example_13_3_1 (p : ℝ) :
    (arithInterval ![1 - p, p] [1, 1, 0, 1, 0, 1]).1 =
      (1 - p) + p * (1 - p) + p ^ 2 * (1 - p) ^ 2 + p ^ 3 * (1 - p) ^ 3 := by
  have h0 : cdfLT (![1 - p, p] : Fin 2 → ℝ) 0 = 0 := by simp [cdfLT]
  have h1 : cdfLT (![1 - p, p] : Fin 2 → ℝ) 1 = 1 - p := by
    have : (univ.filter fun a : Fin 2 => a < 1) = {0} := by decide
    simp only [cdfLT, this, sum_singleton]
    rfl
  simp only [arithInterval, List.foldl_cons, List.foldl_nil, arithStep, h0, h1]
  simp
  ring

/-- **Example 13.3.2.** Arithmetic coding of `ACAA` with `p(A) = p(B) = 0.4`, `p(C) = 0.2`: the
intervals after each symbol are `[0, 0.4)`, `[0.32, 0.4)`, `[0.32, 0.352)` and
`[0.32, 0.3328)`, and the probability of the sequence is `0.0128`. -/
theorem example_13_3_2 :
    arithInterval ![0.4, 0.4, 0.2] [0] = (0, 0.4) ∧
      arithInterval ![0.4, 0.4, 0.2] [0, 2] = (0.32, 0.08) ∧
      arithInterval ![0.4, 0.4, 0.2] [0, 2, 0] = (0.32, 0.032) ∧
      arithInterval ![0.4, 0.4, 0.2] [0, 2, 0, 0] = (0.32, 0.0128) := by
  have h0 : cdfLT (![0.4, 0.4, 0.2] : Fin 3 → ℝ) 0 = 0 := by simp [cdfLT]
  have h2 : cdfLT (![0.4, 0.4, 0.2] : Fin 3 → ℝ) 2 = 0.8 := by
    have : (univ.filter fun a : Fin 3 => a < 2) = {0, 1} := by decide
    simp only [cdfLT, this]
    rw [sum_pair (by decide)]
    norm_num
  simp only [arithInterval, List.foldl_cons, List.foldl_nil, arithStep, h0, h2]
  norm_num

/-! ## Section 13.4: Lempel–Ziv parsings -/

/-- A two-letter alphabet for the examples of Section 13.4. -/
inductive AB
  | A
  | B
  deriving DecidableEq, Inhabited

open AB

/-- **Section 13.4.1, example.** With window `W = 4`, LZ77 parses `ABBABBABBBAABABA` as
`A, B, B, ABBABB, BA, A, BA, BA`, coded as `(0, A), (0, B), (1, 1, 1), (1, 3, 6), (1, 4, 2),
(1, 1, 1), (1, 3, 2), (1, 2, 2)`. -/
theorem example_13_4_1 :
    lz77Encode 4 [A, B, B, A, B, B, A, B, B, B, A, A, B, A, B, A] =
      [.literal A, .literal B, .pointer 1 1, .pointer 3 6, .pointer 4 2, .pointer 1 1,
        .pointer 3 2, .pointer 2 2] := by
  decide

/-- The LZ77 code of the example decodes to the string. -/
theorem example_13_4_1_decode :
    lz77Decode [.literal A, .literal B, .pointer 1 1, .pointer 3 6, .pointer 4 2, .pointer 1 1,
      .pointer 3 2, .pointer 2 2] [] = [A, B, B, A, B, B, A, B, B, B, A, A, B, A, B, A] := by
  decide

/-- **Section 13.4.2, example.** LZ78 parses `ABBABBABBBAABABAA` as
`A, B, BA, BB, AB, BBA, ABA, BAA`, coded as `(0, A), (0, B), (2, A), (2, B), (1, B), (4, A),
(5, A), (3, A)`. -/
theorem example_13_4_2 :
    (lz78Parse [A, B, B, A, B, B, A, B, B, B, A, A, B, A, B, A, A]).1 =
        [[A], [B], [B, A], [B, B], [A, B], [B, B, A], [A, B, A], [B, A, A]] ∧
      lz78Encode [A, B, B, A, B, B, A, B, B, B, A, A, B, A, B, A, A] =
        ([(0, A), (0, B), (2, A), (2, B), (1, B), (4, A), (5, A), (3, A)], 0) := by
  decide

/-! ## Section 13.5: the mean recurrence time -/

/-- **(13.64)** If every symbol recurs with probability one, the mean recurrence time
`E R₁ = ∑ᵤ p(u) · 1/p(u)` is the number of symbols of positive probability. -/
theorem example_13_64 {α : Type*} [Fintype α] [DecidableEq α] {P : StochasticProcess α}
    (hP : P.IsStationary) (hrec : ∀ u, P.law 1 (fun _ => u) ≠ 0 → P.IsRecurrent u) :
    HasSum (fun m : ℕ => ∑ u, ((m : ℝ) + 1) * P.firstReturnProb u m)
      (univ.filter fun u => P.law 1 (fun _ => u) ≠ 0).card := by
  have h : ∀ u, HasSum (fun m : ℕ => ((m : ℝ) + 1) * P.firstReturnProb u m)
      (if P.law 1 (fun _ => u) ≠ 0 then 1 else 0) := fun u => by
    split_ifs with hu
    · exact StochasticProcess.hasSum_mul_firstReturnProb u hP (hrec u hu)
    · push Not at hu
      have : ∀ m, P.firstReturnProb u m = 0 := fun m =>
        le_antisymm ((StochasticProcess.firstReturnProb_le u m).trans hu.le)
          (StochasticProcess.firstReturnProb_nonneg P u m)
      simp only [this, mul_zero]
      exact hasSum_zero
  have := hasSum_sum (s := univ) fun u _ => h u
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one] at this
  exact this

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 13.
-/

/-- **Theorem 13.1.1 (Gallager, Ryabko).** The minimax redundancy is the channel capacity. -/
alias theorem_13_1_1 := isLeast_maxRedundancy

/-- **Lemma 13.3.1 (probability integral transform).** -/
alias lemma_13_3_1 := map_cdf_eq_uniform

/-- **Lemma 13.5.1.** A prefix code for the integers of length `log k + 2 log log k + O(1)`. -/
alias lemma_13_5_1 := eliasDelta_isPrefixCode

/-- **Lemma 13.5.1 (length).** -/
alias lemma_13_5_1_length := length_eliasDelta_le'

/-- **Lemma 13.5.2 (Kac).** -/
alias lemma_13_5_2 := StochasticProcess.hasSum_mul_firstReturnProb

/-- **Theorem 13.5.1.** The recurrence time code is asymptotically optimal. -/
alias theorem_13_5_1 := StochasticProcess.eventually_expectedRecurrenceLength_le

/-- **Lemma 13.5.3 (Lempel and Ziv).** -/
alias lemma_13_5_3 := length_mul_le_of_nodup

/-- **Lemma 13.5.4.** -/
alias lemma_13_5_4 := entropy_le_of_mean

/-- **Lemma 13.5.5 (Ziv's inequality).** -/
alias lemma_13_5_5 := log_markovProb_le

/-- **Theorem 13.5.2.** -/
alias theorem_13_5_2 := eventually_length_mul_log_length_le

/-- **Theorem 13.5.3.** LZ78 is asymptotically optimal. -/
alias theorem_13_5_3 := eventually_lz78Length_le

end InfoTheory.CoverThomas
