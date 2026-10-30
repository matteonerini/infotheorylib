/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.HighProbabilitySet
public import InfoTheoryLib.SourceCoding.TypicalSetCode
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# Cover & Thomas, Chapter 3: Asymptotic Equipartition Property

This file indexes the formalization of Chapter 3 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_3_1_1`, … for them.

The end-of-chapter problems and the historical notes are not included, except for the results of
Problems 3.1 and 3.11 that the chapter relies on.

## Conventions

* **i.i.d. sequences.** `X₁, …, Xₙ` i.i.d. `∼ p` are the coordinates of the finite probability
  space `(Fin n → α, iidPMF p n)`, indexed from `0`. "In probability" and "for `n` sufficiently
  large" refer to this sequence of spaces (`TendstoInProb`, `∀ᶠ n in atTop`).
* **Logarithms.** Entropies are in nats, and the typical set is defined with `e^{-n(H ± ε)}`.
  The book's typical set, with `2^{-n(H ± ε)}` and `H`, `ε` in bits, is `typicalSet p n (ε log 2)`
  (`mem_typicalSet_iff_bits`). Codeword lengths are in bits.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Introduction
* The probability `p⁴q²` of the sequence `(1, 0, 1, 1, 0, 1)`: `example_3_intro_seq` (here).
* Not all `2ⁿ` sequences are equally likely: `example_3_intro_not_equiprobable` (here).
* (3.1): `tendsto_prob_typicalSet` (`AEP.TypicalSet`).
* The number of ones is close to `np`, and such sequences have probability about `2^{-nH(p)}`:
  `example_3_intro_numOnes`, `sampleEntropy_bernoulli` (here).
* Definition (convergence of random variables), in probability and in mean square:
  `TendstoInProb`, `TendstoInMeanSq`, and `TendstoInMeanSq.tendstoInProb`
  (`Probability.WeakLaw`).

### 3.1 Asymptotic equipartition property theorem
* Theorem 3.1.1: `aep`, with the quantitative form `aep_bound` (`AEP.Basic`).
* Definition (3.6): `typicalSet` (`AEP.TypicalSet`), `mem_typicalSet_iff_bits` (here).
* Theorem 3.1.2: `sampleEntropy_mem_Icc_of_mem_typicalSet`, `eventually_prob_typicalSet_gt`,
  `card_typicalSet_le`, `eventually_card_typicalSet_gt` (`AEP.TypicalSet`), bundled in
  `theorem_3_1_2` (here).
* The weak law of large numbers used in the proof: `weak_law` (`Probability.WeakLaw`), from
  Chebyshev's inequality `chebyshev_ineq` (`Probability.Variance`).

### 3.2 Consequences of the AEP: data compression
* The code of Figures 3.1 and 3.2: `typicalSetCode`, `typicalSetCode_injective`,
  `length_typicalSetCode_of_mem`, `length_typicalSetCode_of_notMem`
  (`SourceCoding.TypicalSetCode`).
* (3.17)–(3.22): `expect_length_typicalSetCode_le` (`SourceCoding.TypicalSetCode`).
* Theorem 3.2.1: `exists_code_expect_length_le` (`SourceCoding.TypicalSetCode`).

### 3.3 High-probability sets and the typical set
* Theorem 3.3.1: `log_card_gt_of_prob_ge` (`AEP.HighProbabilitySet`), proved for every `δ < 1`
  as outlined in Problem 3.11. Its proof uses Problem 3.11(a),
  `prob_add_prob_sub_one_le_prob_inter` (`Probability.Event`).
* Definition (3.26), `≐`: `ExpEq` (`AEP.HighProbabilitySet`).
* (3.27) and (3.30): `eventually_log_card_typicalSet`, `minHighProbCard`,
  `tendsto_log_minHighProbCard`, `minHighProbCard_expEq` (`AEP.HighProbabilitySet`).
* The Bernoulli(0.9) example: `example_3_3_most_likely`, `example_3_3_not_typical`,
  `example_3_3_minimal_set` (here).

## Not formalized

* Figures 3.1 and 3.2, whose content is the code `typicalSetCode`.
* Convergence with probability `1`, which needs a single probability space carrying the whole
  sequence. The chapter only uses convergence in probability.
* The end-of-chapter problems, apart from Problem 3.1 (Markov's and Chebyshev's inequalities,
  the weak law) and Problem 3.11, which the chapter uses.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Chapter 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

variable {α : Type*} [Fintype α]

/-! ## Introduction -/

/-- **Introduction.** For i.i.d. Bernoulli(`p`) random variables, the sequence
`(1, 0, 1, 1, 0, 1)` has probability `p^{∑ xᵢ} q^{n - ∑ xᵢ} = p⁴ q²`. -/
lemma example_3_intro_seq (θ : ℝ) :
    bernSeq 6 θ ![true, false, true, true, false, true] = θ ^ 4 * (1 - θ) ^ 2 := by
  simp [bernSeq, Fin.prod_univ_six]
  ring

/-- **Introduction.** For `p ≠ 1/2`, not all `2ⁿ` sequences of length `n ≥ 1` have the same
probability: the all-ones and the all-zeros sequences have probabilities `pⁿ ≠ qⁿ`. -/
lemma example_3_intro_not_equiprobable {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hθ : θ ≠ 1 / 2)
    {n : ℕ} (hn : 0 < n) : bernSeq n θ (fun _ => true) ≠ bernSeq n θ (fun _ => false) := by
  simp only [bernSeq, ite_true, Bool.false_eq_true, ite_false, prod_const, card_univ,
    Fintype.card_fin]
  intro h
  have := (pow_left_inj₀ h0 (by linarith) hn.ne').1 h
  exact hθ (by linarith)

/-- `(1/n) ∑ᵢ 1{xᵢ = 1}` is the fraction of ones in `x`. -/
lemma sampleMean_indicator {n : ℕ} (x : Fin n → Bool) :
    (sampleMean fun i => if x i then (1 : ℝ) else 0) = ((numOnes x : ℕ) : ℝ) / n := by
  simp [sampleMean, numOnes, sum_boole]

/-- **Introduction.** For i.i.d. Bernoulli(`p`) random variables, the fraction of ones in the
sequence converges in probability to `p`: the number of ones is close to `np` with high
probability. -/
lemma example_3_intro_numOnes {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    TendstoInProb (fun n => bernSeq n θ) (fun n x => ((numOnes x : ℕ) : ℝ) / n) θ := by
  have he : expect (bernoulliPMF θ) (fun b => if b then (1 : ℝ) else 0) = θ := by
    simp [expect, bernoulliPMF]
  intro ε hε
  have h := weak_law (bernoulliPMF_isPMF h0 h1) (fun b => if b then (1 : ℝ) else 0) ε hε
  simpa only [sampleMean_indicator, he, bernSeq_eq_iidPMF] using h

/-- **Introduction.** A sequence of `n` Bernoulli(`p`) trials with `k` ones has sample entropy
`-(1/n) log p(x) = H(p) - (k/n - p) log (p / q)`. Hence all sequences whose fraction of ones is
close to `p` have probability about `2^{-nH(p)}`. -/
lemma sampleEntropy_bernoulli {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) {n : ℕ} (hn : 0 < n)
    (x : Fin n → Bool) :
    sampleEntropy (bernoulliPMF θ) x =
      binEntropy θ - (((numOnes x : ℕ) : ℝ) / n - θ) * log (θ / (1 - θ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk : (numOnes x : ℕ) ≤ n := Nat.lt_succ_iff.1 (numOnes x).2
  have hq : 0 < 1 - θ := by linarith
  rw [sampleEntropy, ← bernSeq_eq_iidPMF, bernSeq_eq, log_mul (by positivity) (by positivity),
    log_pow, log_pow, Nat.cast_sub hk, log_div h0.ne' hq.ne', binEntropy_eq_mul_log_inv, log_inv,
    log_inv]
  field_simp
  ring

/-! ## 3.1 The AEP -/

/-- **Definition (3.6) in bits.** The typical set `typicalSet p n (ε log 2)` is the book's set of
sequences with `2^{-n(H(X)+ε)} ≤ p(x₁, …, xₙ) ≤ 2^{-n(H(X)-ε)}`, where `H(X) = entropy p / log 2`
and `ε` are in bits. -/
lemma mem_typicalSet_iff_bits {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α} :
    x ∈ typicalSet p n (ε * log 2) ↔
      (2 : ℝ) ^ (-(n * (entropy p / log 2 + ε))) ≤ iidPMF p n x ∧
        iidPMF p n x ≤ (2 : ℝ) ^ (-(n * (entropy p / log 2 - ε))) := by
  have h2 : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  have e1 : log 2 * -(n * (entropy p / log 2 + ε)) = -(n * (entropy p + ε * log 2)) := by
    field_simp
  have e2 : log 2 * -(n * (entropy p / log 2 - ε)) = -(n * (entropy p - ε * log 2)) := by
    field_simp
  rw [mem_typicalSet, rpow_def_of_pos two_pos, rpow_def_of_pos two_pos, e1, e2]

/-- **Theorem 3.1.2.** The typical set `A_ε^(n)` has the following properties:
1. If `x ∈ A_ε^(n)`, then `H(X) - ε ≤ -(1/n) log p(x) ≤ H(X) + ε`.
2. `Pr{A_ε^(n)} > 1 - ε` for `n` sufficiently large.
3. `|A_ε^(n)| ≤ e^{n(H(X)+ε)}`.
4. `|A_ε^(n)| > (1 - ε) e^{n(H(X)-ε)}` for `n` sufficiently large. -/
theorem theorem_3_1_2 {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    (∀ n : ℕ, 0 < n → ∀ x ∈ typicalSet p n ε,
      entropy p - ε ≤ sampleEntropy p x ∧ sampleEntropy p x ≤ entropy p + ε) ∧
    (∀ᶠ n in atTop, 1 - ε < prob (iidPMF p n) (typicalSet p n ε)) ∧
    (∀ n : ℕ, ((typicalSet p n ε).card : ℝ) ≤ exp (n * (entropy p + ε))) ∧
    (∀ᶠ n : ℕ in atTop, (1 - ε) * exp (n * (entropy p - ε)) < (typicalSet p n ε).card) :=
  ⟨fun _ hn _ hx => sampleEntropy_mem_Icc_of_mem_typicalSet hn hx,
    eventually_prob_typicalSet_gt hp hε, fun n => card_typicalSet_le hp n ε,
    eventually_card_typicalSet_gt hp hε⟩

/-! ## 3.3 High probability sets and the typical set -/

/-- **Section 3.3, Bernoulli(0.9) example.** The sequence of all ones is the most likely
sequence. -/
lemma example_3_3_most_likely {n : ℕ} (x : Fin n → Bool) :
    iidPMF (bernoulliPMF 0.9) n x ≤ iidPMF (bernoulliPMF 0.9) n (fun _ => true) := by
  apply Finset.prod_le_prod₀
  · intro i _; cases x i <;> norm_num [bernoulliPMF]
  · intro i _; cases x i <;> norm_num [bernoulliPMF]

/-- **Section 3.3, Bernoulli(0.9) example.** The most likely sequence, all ones, is not typical:
its sample entropy `-log 0.9` differs from `H(0.9)` by `0.1 log 9`. -/
lemma example_3_3_not_typical {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : ε < 0.1 * log 9) :
    (fun _ => true) ∉ typicalSet (bernoulliPMF 0.9) n ε := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk : ((numOnes (fun _ : Fin n => true) : ℕ) : ℝ) = n := by simp [numOnes]
  rw [mem_typicalSet_iff hn, entropy_bernoulliPMF, sampleEntropy_bernoulli (by norm_num)
    (by norm_num) hn, hk, div_self hn']
  rintro ⟨-, h⟩
  have h9 : (0.9 : ℝ) / (1 - 0.9) = 9 := by norm_num
  have hlog : 0 < log (9 : ℝ) := log_pos (by norm_num)
  rw [h9, show binEntropy 0.9 - (1 - 0.9) * log 9 - binEntropy 0.9 = -(0.1 * log 9) by ring,
    abs_neg, abs_of_pos (by positivity)] at h
  linarith

/-- **Section 3.3, Bernoulli(0.9) example.** A smallest set of probability at least `1 - δ` can be
chosen to contain the most likely sequence, all ones. -/
lemma example_3_3_minimal_set (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∃ B : Finset (Fin n → Bool), B.card = minHighProbCard (bernoulliPMF 0.9) n δ ∧
      1 - δ ≤ prob (iidPMF (bernoulliPMF 0.9) n) B ∧ (fun _ => true) ∈ B :=
  exists_minHighProbSet_mem (bernoulliPMF_isPMF (by norm_num) (by norm_num)) n hδ0 hδ1
    example_3_3_most_likely

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems of Chapter 3.
-/

/-- **Theorem 3.1.1 (AEP).** `-(1/n) log p(X₁, …, Xₙ) → H(X)` in probability. -/
alias theorem_3_1_1 := aep

/-- **Theorem 3.2.1.** One-to-one codes with `E[(1/n) l(Xⁿ)] ≤ H(X) + ε` for `n` large. -/
alias theorem_3_2_1 := exists_code_expect_length_le

/-- **Theorem 3.3.1.** High-probability sets have at least about `2^{nH}` elements. -/
alias theorem_3_3_1 := log_card_gt_of_prob_ge

end InfoTheory.CoverThomas
