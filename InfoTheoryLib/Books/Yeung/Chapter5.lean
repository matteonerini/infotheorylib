/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.SourceCodingTheorem
public import InfoTheoryLib.SourceCoding.TypicalSetCode
public import Mathlib.Probability.StrongLaw

/-!
# Yeung, Chapter 5: Weak Typicality

This file indexes the formalization of Chapter 5 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Logarithms.** Logarithms are natural, so `2^{-n(H(X) ± ε)}` becomes `e^{-n(H(X) ± ε)}` with
  `H(X)` and `ε` in nats, and `m` bits become `m log 2` nats. `mem_typicalSet_iff_bits`
  (`Books.CoverThomas.Chapter3`) converts the typical set to bits.
* **Finite alphabets.** The alphabet is finite. The book allows a countable alphabet with finite
  entropy in Sections 5.1 and 5.2.
* **Typical sequences.** A sequence with `p(x) = 0` has infinite empirical entropy in the book, so
  it is not typical. In the library, `typicalSet` has this property for `n > 0`
  (`mem_typicalSet_iff`).
* **Block codes.** A block code is given by the set `A ⊆ 𝒳ⁿ` of correctly decoded sequences, whose
  size is the number `M` of codewords, as in (5.17)–(5.18). The fair bits results instead use an
  encoder `f` and a decoder `g`, as in Section 5.3.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 5.1 The Weak AEP
* (5.1), (5.4), (5.5) and (5.8): `iidPMF` (`Probability.IID`), `sampleEntropy`, `log_iidPMF`,
  `sampleEntropy_eq_sampleMean`, `expect_neg_log` (`AEP.Basic`).
* Theorem 5.1: `theorem_5_1` (here), which is `aep` (`AEP.Basic`). The form (5.3) is
  `eventually_prob_typicalSet_gt` (`AEP.TypicalSet`).
* Definition 5.2: `typicalSet`, `mem_typicalSet`, `mem_typicalSet_iff` (`AEP.TypicalSet`).
* Theorem 5.3: `theorem_5_3` (here).
* (5.16): `tendsto_card_typicalSet_div` (`AEP.SourceCodingTheorem`).
* The remark that the most likely sequence need not be typical: `most_likely_not_typical` (here).

### 5.2 The Source Coding Theorem
* (5.19)–(5.23), the direct part: `exists_blockCode` (`AEP.SourceCodingTheorem`).
* (5.24)–(5.27), the converse part: `eventually_prob_compl_gt`, `tendsto_prob_compl_of_card_le`
  (`AEP.SourceCodingTheorem`).
* The variable-length form of the direct part, which is not in the book:
  `exists_code_expect_length_le` (`SourceCoding.TypicalSetCode`).

### 5.3 Efficient Source Coding
* Theorem 5.4: `theorem_5_4` (here), from `entropy_prefixRV_le_mul_log` and
  `entropy_prefixRV_eq_mul_log_iff` (`AEP.SourceCodingTheorem`), for any finite alphabet.
* (5.34)–(5.42): `le_entropy_of_blockCode` (`AEP.SourceCodingTheorem`) and `entropyRV_le_log_card`
  (`Entropy.Bounds`). The proof bounds `H(Y)` directly and does not pass through `H(X̂)`.
* (5.43)–(5.44), almost fair bits: `tendsto_entropy_div_of_blockCode` (`AEP.SourceCodingTheorem`).
  The book's `≈` is made precise as a limit, assuming `m log 2 / n → H(X) > 0`.

### 5.4 The Shannon-McMillan-Breiman Theorem
* Example 5.5: `example_5_5` (here), which is Mathlib's strong law of large numbers.
* Example 5.6: `example_5_6` (here).

## Not formalized

* The Shannon-McMillan-Breiman theorem (5.46) and the general definition of ergodicity (5.47), which
  the book states without proof. Mathlib has no pointwise ergodic theorem to prove it from.
* The estimates of the entropy rate of printed English at the end of Section 5.4.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {α : Type*} [Fintype α]

/-! ### Worked examples -/

/-- The source of the remark in Section 5.1: `p(0) = 0.1` and `p(1) = 0.9`. -/
def pmf_5_1 : Bool → ℝ := fun b => if b then 9 / 10 else 1 / 10

lemma pmf_5_1_isPMF : IsPMF pmf_5_1 :=
  ⟨fun b => by cases b <;> norm_num [pmf_5_1], by simp [pmf_5_1]; norm_num⟩

/-- The entropy of `pmf_5_1` exceeds the empirical entropy `-log 0.9` of `(1, 1, …, 1)` by
`(log 9) / 10`. -/
lemma entropy_pmf_5_1 : entropy pmf_5_1 = -log (9 / 10) + log 9 / 10 := by
  have h₁ : log (1 / 10 : ℝ) = log (9 / 10) - log 9 := by
    rw [show (1 / 10 : ℝ) = (9 / 10) / 9 by norm_num, log_div (by norm_num) (by norm_num)]
  rw [entropy_eq_sum_negMulLog, Fintype.sum_bool]
  simp only [pmf_5_1, Bool.false_eq_true, ↓reduceIte, negMulLog, h₁]
  ring

/-- **The remark in Section 5.1.** For `p(1) = 0.9`, the sequence `(1, 1, …, 1)` is the most likely
one, but it is not weakly `ε`-typical for small `ε`. -/
theorem most_likely_not_typical {n : ℕ} (hn : 0 < n) :
    (∀ x : Fin n → Bool, iidPMF pmf_5_1 n x ≤ iidPMF pmf_5_1 n fun _ => true) ∧
      ∀ ε < log 9 / 10, (fun _ => true) ∉ typicalSet pmf_5_1 n ε := by
  refine ⟨fun x => prod_le_prod₀ (fun i _ => pmf_5_1_isPMF.nonneg _) (fun i _ => ?_),
    fun ε hε h => ?_⟩
  · cases x i <;> norm_num [pmf_5_1]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h₁ : iidPMF pmf_5_1 n (fun _ => true) = (9 / 10) ^ n := by
    simp [iidPMF, pmf_5_1, div_pow]
  have h₂ : sampleEntropy pmf_5_1 (fun _ : Fin n => true) = -log (9 / 10) := by
    rw [sampleEntropy, h₁, log_pow]
    field_simp
  have h₃ := ((mem_typicalSet_iff hn).1 h).2
  rw [h₂, entropy_pmf_5_1,
    show -log (9 / 10) - (-log (9 / 10) + log 9 / 10) = -(log 9 / 10) by ring,
    abs_neg, abs_of_pos (by have := log_pos (show (1 : ℝ) < 9 by norm_num); positivity)] at h₃
  linarith

/-- The source of Example 5.6, on the space of `Z`: `X_k = Z` for all `k`. -/
def rv_5_6 (_ : ℕ) (z : Bool) : ℝ := if z then 1 else 0

/-- The sample means of the source of Example 5.6 converge to `Z`, and to nothing else. -/
lemma tendsto_mean_rv_5_6_iff (z : Bool) (c : ℝ) :
    Tendsto (fun n : ℕ => (∑ l ∈ range n, rv_5_6 l z) / n) atTop (𝓝 c) ↔ c = rv_5_6 0 z := by
  have h : Tendsto (fun n : ℕ => (∑ l ∈ range n, rv_5_6 l z) / n) atTop (𝓝 (rv_5_6 0 z)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [rv_5_6, sum_const, card_range, nsmul_eq_mul]
    field_simp
  exact ⟨fun h' => tendsto_nhds_unique h' h, fun h' => h' ▸ h⟩

open Classical in
/-- **Example 5.6, (5.49)–(5.51).** If `X_k = Z` for all `k`, where `Z` is a fair bit, the sample
mean converges to `0` with probability `1/2` and to `1` with probability `1/2`, and it converges to
the mean `E X_k = 1/2` with probability `0`. So the source is not mean ergodic. -/
theorem example_5_6 :
    prob (uniformPMF Bool)
        (univ.filter fun z =>
          Tendsto (fun n : ℕ => (∑ l ∈ range n, rv_5_6 l z) / n) atTop (𝓝 0)) = 1 / 2 ∧
      prob (uniformPMF Bool)
        (univ.filter fun z =>
          Tendsto (fun n : ℕ => (∑ l ∈ range n, rv_5_6 l z) / n) atTop (𝓝 1)) = 1 / 2 ∧
      expect (uniformPMF Bool) (rv_5_6 0) = 1 / 2 ∧
      prob (uniformPMF Bool)
        (univ.filter fun z =>
          Tendsto (fun n : ℕ => (∑ l ∈ range n, rv_5_6 l z) / n) atTop (𝓝 (1 / 2))) = 0 := by
  simp only [tendsto_mean_rv_5_6_iff, prob, sum_filter, Fintype.sum_bool]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [rv_5_6, uniformPMF]
  · norm_num [rv_5_6, uniformPMF]
  · norm_num [expect, uniformPMF, rv_5_6, Fintype.sum_bool]
  · norm_num [rv_5_6]

/-! ### Aliases -/

/-- **Theorem 5.1 (Weak AEP I).** (5.2) -/
alias theorem_5_1 := aep

/-- **Theorem 5.3 (Weak AEP II).** (5.9)–(5.11) -/
theorem theorem_5_3 {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    (∀ (n : ℕ) (x : Fin n → α), x ∈ typicalSet p n ε →
      exp (-(n * (entropy p + ε))) ≤ iidPMF p n x ∧
        iidPMF p n x ≤ exp (-(n * (entropy p - ε)))) ∧
    (∀ᶠ n : ℕ in atTop, 1 - ε < prob (iidPMF p n) (typicalSet p n ε)) ∧
    ∀ᶠ n : ℕ in atTop, (1 - ε) * exp (n * (entropy p - ε)) ≤ (typicalSet p n ε).card ∧
      ((typicalSet p n ε).card : ℝ) ≤ exp (n * (entropy p + ε)) := by
  refine ⟨fun n x hx => mem_typicalSet.1 hx, eventually_prob_typicalSet_gt hp hε, ?_⟩
  filter_upwards [eventually_card_typicalSet_gt hp hε] with n hn
  exact ⟨hn.le, card_typicalSet_le hp n ε⟩

/-- **Theorem 5.4.** A binary sequence `Y` of length `m` has `H(Y) ≤ m` bits, with equality iff the
`Yᵢ` are i.i.d. and uniform on `{0, 1}`. -/
theorem theorem_5_4 {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : ℕ → Ω → Bool) (m : ℕ) :
    H[prefixRV Y m ; μ] ≤ m * log 2 ∧
      (H[prefixRV Y m ; μ] = m * log 2 ↔
        IndepFamily μ Y m ∧ ∀ i ∈ range m, dist μ (Y i) = uniformPMF Bool) := by
  have h := entropy_prefixRV_le_mul_log hμ Y m
  have h' := entropy_prefixRV_eq_mul_log_iff hμ Y m
  simp only [Fintype.card_bool, Nat.cast_ofNat] at h h'
  exact ⟨h, h'⟩

/-- **Example 5.5.** An i.i.d. source is mean ergodic under suitable conditions, by the strong law
of large numbers. (5.48) -/
alias example_5_5 := ProbabilityTheory.strong_law_ae_real

end InfoTheory.Yeung
