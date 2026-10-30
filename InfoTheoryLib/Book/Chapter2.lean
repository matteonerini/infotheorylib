/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.IID
public import InfoTheoryLib.Probability.Jensen
public import InfoTheoryLib.MutualInformation.ChainRule
public import InfoTheoryLib.MutualInformation.Convexity
public import InfoTheoryLib.MarkovChain.DataProcessing
public import InfoTheoryLib.RelativeEntropy.Conditional
public import InfoTheoryLib.Statistics.Bernoulli
public import InfoTheoryLib.Entropy.Fano
public import InfoTheoryLib.Entropy.Collision

/-!
# Cover & Thomas, Chapter 2: Entropy, Relative Entropy, and Mutual Information

This file indexes the formalization of Chapter 2 of [cover2006] and contains the chapter's worked
examples, remarks and textbook-specific definitions. The general theory lives in the topic modules
of `InfoTheoryLib`. The table below lists each numbered result with the declaration that proves
it, and the last section of this file defines aliases `lemma_2_1_1`, `theorem_2_2_1`, … for them,
so the index is checked by Lean.

The end-of-chapter problems and the historical notes are not included, except for Problem 2.5,
which Section 2.10 quotes.

## Conventions

* **Logarithms.** All quantities are measured in nats. The book works in bits, but every
  statement in the chapter is homogeneous in the logarithm, so it holds verbatim in any base.
  Lemma 2.1.2 (`entropyBase_eq`) gives the change of base. Numerical examples, and the bounds
  `2^{-H}` of Section 2.10, are stated in bits by dividing by `log 2`.
* **`p log (p/0) = ∞`.** The book's `D(p‖q)` takes values in `[0, ∞]`; it is `relEntropy`. Most
  results use the finite `relEntropyReal` under `AbsCont p q`.
* **Indexing.** Families `X₁, …, Xₙ` are indexed from `0`, see `prefixRV`.
* **Parameters.** In Section 2.9 the parameter set `Θ` is finite.
* **Estimators.** In Section 2.10 an estimator `X̂` is a random variable on the same space as `X`
  and `Y`, so it may be random. Its alphabet `𝒳̂` contains `𝒳` through an injection `ι`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 2.1 Entropy
* (2.1)–(2.2) entropy and expectation: `entropy`, `entropyRV` (`Entropy.Basic`), `expect`
  (`Probability.FinitePMF`).
* Remark, (2.3) `H(X) = E log (1 / p(X))`: `entropy_eq_expect` (`Entropy.Basic`).
* Lemmas 2.1.1 and 2.1.2: `entropy_nonneg`, `entropyBase_eq` (`Entropy.Basic`).
* Examples 2.1.1 and 2.1.2: `example_2_1_1`, `example_2_1_2`, … (here).

### 2.2 Joint entropy and conditional entropy
* (2.8)–(2.13): `jointEntropy_def`, `condEntropy` (`Entropy.Conditional`).
* Theorem 2.2.1 and Corollary (2.21): `chain_rule`, `chain_rule_cond` (`Entropy.Conditional`).
* Example 2.2.1 and Remark: `example_2_2_1_HX`, …, `remark_condEntropy_not_symm` (here), and
  `entropy_sub_condEntropy_symm` (`Entropy.Conditional`).

### 2.3 Relative entropy and mutual information
* (2.26)–(2.27): `relEntropy`, `relEntropyReal` (`RelativeEntropy.Basic`).
* (2.28)–(2.30): `mutualInfo` (`MutualInformation.Basic`).
* Example 2.3.1, and the failure of symmetry and of the triangle inequality:
  `example_2_3_1_pq`, …, `example_2_3_1_not_symm`, `relEntropy_not_triangle` (here).

### 2.4 Relationship between entropy and mutual information
* (2.35)–(2.42), Theorem 2.4.1 and Example 2.4.1: `theorem_2_4_1`, `example_2_4_1` (here).

### 2.5 Chain rules for entropy, relative entropy, and mutual information
* Theorem 2.5.1: `chain_rule_entropy` (`Entropy.ChainRule`).
* (2.60)–(2.61): `condMutualInfo` (`MutualInformation.Conditional`).
* Theorem 2.5.2: `chain_rule_mutualInfo` (`MutualInformation.ChainRule`).
* (2.65)–(2.66) and Theorem 2.5.3: `condRelEntropy`, `chain_rule_relEntropy`
  (`RelativeEntropy.Conditional`).

### 2.6 Jensen's inequality and its consequences
* (2.72), examples, Theorem 2.6.1: `ConvexOver`, `convex_examples`,
  `convexOn_of_deriv2_nonneg_interval`, … (here).
* Theorem 2.6.2: `jensen`, `jensen_eq_iff` (`Probability.Jensen`).
* Theorem 2.6.3: `relEntropyReal_nonneg`, `relEntropy_eq_zero_iff`, …
  (`RelativeEntropy.InformationInequality`).
* Corollaries (2.90)–(2.92): `mutualInfo_nonneg`, `mutualInfo_eq_zero_iff`
  (`MutualInformation.Basic`), `condRelEntropy_nonneg` (`RelativeEntropy.Conditional`),
  `condMutualInfo_nonneg`, `condMutualInfo_eq_zero_iff` (`MutualInformation.Conditional`).
* Theorems 2.6.4–2.6.6 and their equality cases: `entropy_le_log_card`, `entropy_eq_log_card_iff`,
  `condEntropy_le_entropy`, `condEntropy_eq_entropy_iff`, `entropy_prefixRV_le_sum`,
  `entropy_prefixRV_eq_sum_iff` (`Entropy.Bounds`), with (2.93) `relEntropyReal_uniform`
  (`RelativeEntropy.Basic`).
* Example 2.6.1: `example_2_6_1_HX`, …, `example_2_6_1_remark` (here).

### 2.7 Log sum inequality and its applications
* Theorem 2.7.1: `log_sum_inequality` (`Analysis.LogSum`).
* (2.102)–(2.104): `relEntropyReal_nonneg'` (`RelativeEntropy.Convexity`).
* Theorem 2.7.2: `relEntropyReal_convex_pair`, `relEntropy_convex_pair`
  (`RelativeEntropy.Convexity`).
* Theorem 2.7.3 and Remark: `entropy_concaveOn`, `entropy_mix_ge` (`Entropy.Concavity`).
* Theorem 2.7.4: `mutualInfoOf_concave_input`, `mutualInfoOf_convex_channel`
  (`MutualInformation.Convexity`).

### 2.8 Data-processing inequality
* (2.117)–(2.118): `MarkovChain`, `markovChain_iff_condIndep` (`MarkovChain.Basic`).
* The other consequences of the definition: `MarkovChain.symm`, `markovChain_comp`
  (`MarkovChain.Basic`).
* Theorem 2.8.1, its equality case and its second inequality: `data_processing`,
  `data_processing_eq_iff`, `data_processing'` (`MarkovChain.DataProcessing`).
* Corollaries: `mutualInfo_comp_le`, `condMutualInfo_le_of_markov` (`MarkovChain.DataProcessing`).
* Example: `example_2_8_indep`, `example_2_8_cond` (here).

### 2.9 Sufficient statistics
* (2.123)–(2.124) and (2.128): `mutualInfo_statistic_le`, `IsSufficient`,
  `isSufficient_iff_mutualInfo`, `IsMinimalSufficient`, `IsMinimalSufficient.chain`
  (`Statistics.SufficientStatistic`).
* Example 1, (2.125): `condDist_numOnes`, `numOnes_sufficient`, `numOnes_minimal`
  (`Statistics.Bernoulli`).
* Examples 2 and 3, (2.126)–(2.127), and the remark on odd and even samples: `example_2_9_2`,
  `example_2_9_3`, `odd_even_means_sufficient`, `odd_even_means_not_function_of_mean` (here).

### 2.10 Fano's inequality
* (2.129), (2.133): `estErrProb`, `estErrRV`, and for estimators `X̂ = g(Y)`, `errProb`, `errRV`
  (`Entropy.Fano`).
* Theorem 2.10.1, (2.134)–(2.138): `condEntropy_le_estErrProb`, `fano_estimator`
  (`Entropy.Fano`).
* (2.131)–(2.132): `fano_estimator_weak`, `fano_estimator_weak_bits`,
  `fano_estimator_lower_bound`, and for `X̂ = g(Y)`, `fano_weak`, `fano_lower_bound`.
* Remark (`Pₑ = 0` implies `H(X|Y) = 0`) and Problem 2.5: `condEntropy_eq_zero_of_errProb_eq_zero`,
  `condEntropy_eq_zero_iff`.
* Corollaries (2.139) and (2.140)–(2.142): `fano_of_eq`, `fano`, `condEntropy_given_err_le`.
* Remark, (2.143)–(2.144): `fano_no_side_info`, `best_guess`, `fano_sharp`.
* (2.145), Lemma 2.10.1 and its equality case: `prob_eq_of_indepRV`, `exp_neg_entropy_le_sum_sq`,
  `sum_sq_eq_exp_neg_entropy_iff` (`Entropy.Collision`), in bits `lemma_2_10_1_bits` (here).
* Corollary (2.149)–(2.150): `exp_neg_entropy_sub_relEntropy_le` (`Entropy.Collision`).

## Not formalized

* Figures 2.1–2.3. Their mathematical content (the shape of `H(p)`, the identities of
  Theorem 2.4.1, examples of convex functions) is formalized.
* Heuristic interpretations: coding lengths, court cases, mixing gases, Markov fields.
* Examples 2 and 3 of Section 2.9 involve densities, which the book defers to Chapter 8. We
  formalize the factorization of their likelihoods through the sufficient statistic.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Chapter 2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-! ## 2.1 Entropy -/

/-- **Example 2.1.1.** For `X = 1` with probability `p` and `X = 0` with probability `1 - p`,
`H(X) = -p log p - (1 - p) log (1 - p) =: H(p)` (2.5). -/
lemma example_2_1_1 (p : ℝ) :
    entropy (fun b : Bool => if b then p else 1 - p) = -p * log p - (1 - p) * log (1 - p) := by
  rw [entropy_bernoulli, binEntropy_eq_mul_log_inv]; simp only [log_inv]; ring

/-- **Example 2.1.1.** `H(X) = 1` bit when `p = 1/2`. -/
lemma example_2_1_1_half : binEntropy (1 / 2) / log 2 = 1 := by
  rw [one_div, binEntropy_two_inv, div_self (log_pos one_lt_two).ne']

/-- **Example 2.1.1 (Figure 2.1).** `H(p)` is a concave function of the distribution. -/
lemma example_2_1_1_concave : StrictConcaveOn ℝ (Set.Icc 0 1) binEntropy :=
  strictConcave_binEntropy

/-- **Example 2.1.1 (Figure 2.1).** `H(p) = 0` exactly when `p = 0` or `p = 1`, i.e. when the
variable is not random. -/
lemma example_2_1_1_eq_zero (p : ℝ) : binEntropy p = 0 ↔ p = 0 ∨ p = 1 :=
  binEntropy_eq_zero

/-- **Example 2.1.1 (Figure 2.1).** The uncertainty is maximal (`1` bit) exactly at `p = 1/2`. -/
lemma example_2_1_1_max (p : ℝ) :
    binEntropy p ≤ binEntropy (1 / 2) ∧ (binEntropy p = binEntropy (1 / 2) ↔ p = 1 / 2) := by
  rw [one_div, binEntropy_two_inv]
  exact ⟨binEntropy_le_log_two, binEntropy_eq_log_two⟩

/-- The pmf of **Example 2.1.2**: `(1/2, 1/4, 1/8, 1/8)` on `{a, b, c, d} = Fin 4`. -/
def pmf_2_1_2 : Fin 4 → ℝ := ![1 / 2, 1 / 4, 1 / 8, 1 / 8]

lemma pmf_2_1_2_isPMF : IsPMF pmf_2_1_2 :=
  ⟨fun x => by fin_cases x <;> norm_num [pmf_2_1_2],
    by simp [pmf_2_1_2, Fin.sum_univ_four]; norm_num⟩

/-- **Example 2.1.2.** `H(X) = -½ log ½ - ¼ log ¼ - ⅛ log ⅛ - ⅛ log ⅛ = 7/4` bits (2.7). -/
lemma example_2_1_2 : entropy pmf_2_1_2 / log 2 = 7 / 4 := by
  have h2 := (log_pos one_lt_two).ne'
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_four]
  have e1 : pmf_2_1_2 0 = ((2 : ℝ) ^ 1)⁻¹ := by simp [pmf_2_1_2]
  have e2 : pmf_2_1_2 1 = ((2 : ℝ) ^ 2)⁻¹ := by simp [pmf_2_1_2]; norm_num
  have e3 : pmf_2_1_2 2 = ((2 : ℝ) ^ 3)⁻¹ := by simp [pmf_2_1_2]; norm_num
  have e4 : pmf_2_1_2 3 = ((2 : ℝ) ^ 3)⁻¹ := by simp [pmf_2_1_2]; norm_num
  rw [e1, e2, e3, e4]
  simp only [negMulLog_inv_two_pow]
  field_simp
  norm_num

/-- **Example 2.1.2 (binary questions).** Asking "Is `X = a`?", then "Is `X = b`?", then
"Is `X = c`?" determines `X` after `1, 2, 3, 3` questions respectively; the expected number of
binary questions is `1.75 = H(X)` bits. -/
lemma example_2_1_2_questions :
    expect pmf_2_1_2 (fun x => (![1, 2, 3, 3] : Fin 4 → ℝ) x) = 7 / 4 ∧
      expect pmf_2_1_2 (fun x => (![1, 2, 3, 3] : Fin 4 → ℝ) x) = entropy pmf_2_1_2 / log 2 := by
  have h : expect pmf_2_1_2 (fun x => (![1, 2, 3, 3] : Fin 4 → ℝ) x) = 7 / 4 := by
    simp [expect, pmf_2_1_2, Fin.sum_univ_four]; norm_num
  exact ⟨h, h.trans example_2_1_2.symm⟩

/-! ## 2.2 Joint entropy and conditional entropy -/

/-- The joint distribution of **Example 2.2.1**, written as in the book's table with rows
indexed by `Y` and columns by `X`. A point of `Fin 4 × Fin 4` is `(x, y)`. -/
def table_2_2_1 : Fin 4 → Fin 4 → ℝ :=
  ![![1 / 8, 1 / 16, 1 / 32, 1 / 32],
    ![1 / 16, 1 / 8, 1 / 32, 1 / 32],
    ![1 / 16, 1 / 16, 1 / 16, 1 / 16],
    ![1 / 4, 0, 0, 0]]

/-- The pmf of Example 2.2.1 on `Ω = Fin 4 × Fin 4` (`X = Prod.fst`, `Y = Prod.snd`). -/
def pmf_2_2_1 : Fin 4 × Fin 4 → ℝ := fun z => table_2_2_1 z.2 z.1

lemma pmf_2_2_1_isPMF : IsPMF pmf_2_2_1 := by
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨x, y⟩ := z
    fin_cases x <;> fin_cases y <;> norm_num [pmf_2_2_1, table_2_2_1]
  · simp [pmf_2_2_1, table_2_2_1, Fintype.sum_prod_type, Fin.sum_univ_four]; norm_num

/-- The marginal distribution of `X` in Example 2.2.1 is `(1/2, 1/4, 1/8, 1/8)`. -/
lemma example_2_2_1_dist_X : dist pmf_2_2_1 Prod.fst = pmf_2_1_2 := by
  funext a
  rw [dist_fst]
  fin_cases a <;> simp [pmf_2_2_1, table_2_2_1, pmf_2_1_2, Fin.sum_univ_four] <;> norm_num

/-- The marginal distribution of `Y` in Example 2.2.1 is `(1/4, 1/4, 1/4, 1/4)`. -/
lemma example_2_2_1_dist_Y : dist pmf_2_2_1 Prod.snd = fun _ => 1 / 4 := by
  funext b
  rw [dist_snd]
  fin_cases b <;> simp [pmf_2_2_1, table_2_2_1, Fin.sum_univ_four] <;> norm_num

/-- **Example 2.2.1.** `H(X) = 7/4` bits. -/
lemma example_2_2_1_HX : H[Prod.fst ; pmf_2_2_1] / log 2 = 7 / 4 := by
  rw [entropyRV, example_2_2_1_dist_X, example_2_1_2]

/-- **Example 2.2.1.** `H(Y) = 2` bits. -/
lemma example_2_2_1_HY : H[Prod.snd ; pmf_2_2_1] / log 2 = 2 := by
  have h2 := (log_pos one_lt_two).ne'
  rw [entropyRV, example_2_2_1_dist_Y, entropy_eq_sum_negMulLog]
  simp only [one_div, negMulLog_four_inv, sum_const, card_univ, Fintype.card_fin]
  field_simp; ring

/-- **Example 2.2.1.** `H(X, Y) = 27/8` bits. -/
lemma example_2_2_1_HXY : H[pair Prod.fst Prod.snd ; pmf_2_2_1] / log 2 = 27 / 8 := by
  have h2 := (log_pos one_lt_two).ne'
  rw [entropyRV, dist_pair_fst_snd, entropy_eq_sum_negMulLog, Fintype.sum_prod_type]
  simp only [pmf_2_2_1, table_2_2_1, Fin.sum_univ_four]
  simp [negMulLog_four_inv, negMulLog_eight_inv, negMulLog_sixteen_inv,
    negMulLog_thirtytwo_inv]
  field_simp; norm_num

/-- **Example 2.2.1.** `H(X|Y) = 11/8` bits (2.25). -/
lemma example_2_2_1_HX_given_Y : H[Prod.fst | Prod.snd ; pmf_2_2_1] / log 2 = 11 / 8 := by
  rw [condEntropy_eq_sub pmf_2_2_1_isPMF, entropyRV_pair_comm, sub_div, example_2_2_1_HXY,
    example_2_2_1_HY]; norm_num

/-- **Example 2.2.1.** `H(Y|X) = 13/8` bits. -/
lemma example_2_2_1_HY_given_X : H[Prod.snd | Prod.fst ; pmf_2_2_1] / log 2 = 13 / 8 := by
  rw [condEntropy_eq_sub pmf_2_2_1_isPMF, sub_div, example_2_2_1_HXY, example_2_2_1_HX]; norm_num

/-- **Example 2.2.1 (2.22)–(2.24).** The conditional entropies `H(X | Y = i)` are
`H(1/2, 1/4, 1/8, 1/8) = 7/4`, `H(1/4, 1/2, 1/8, 1/8) = 7/4`, `H(1/4, 1/4, 1/4, 1/4) = 2` and
`H(1, 0, 0, 0) = 0` bits. -/
lemma example_2_2_1_HX_given_Y_eq :
    condEntropyAt pmf_2_2_1 Prod.fst Prod.snd 0 / log 2 = 7 / 4 ∧
    condEntropyAt pmf_2_2_1 Prod.fst Prod.snd 1 / log 2 = 7 / 4 ∧
    condEntropyAt pmf_2_2_1 Prod.fst Prod.snd 2 / log 2 = 2 ∧
    condEntropyAt pmf_2_2_1 Prod.fst Prod.snd 3 / log 2 = 0 := by
  have h2 := (log_pos one_lt_two).ne'
  have hY : ∀ b, dist pmf_2_2_1 Prod.snd b = 1 / 4 := fun b => congrFun example_2_2_1_dist_Y b
  simp only [condEntropyAt, condDist, dist_pair_snd_fst, hY, entropy_eq_sum_negMulLog,
    Fin.sum_univ_four, pmf_2_2_1, table_2_2_1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;>
    simp only [one_div, negMulLog_two_inv, negMulLog_four_inv, negMulLog_eight_inv] <;>
    field_simp <;> ring

/-- **Remark (after Example 2.2.1).** In general `H(Y|X) ≠ H(X|Y)`. -/
lemma remark_condEntropy_not_symm :
    H[Prod.snd | Prod.fst ; pmf_2_2_1] ≠ H[Prod.fst | Prod.snd ; pmf_2_2_1] := by
  intro h
  have h1 := example_2_2_1_HY_given_X
  rw [h, example_2_2_1_HX_given_Y] at h1
  norm_num at h1

/-! ## 2.3 Relative entropy and mutual information -/

/-- The two-point distribution `(1 - r, r)` on `{0, 1}`. -/
def bernPMF (r : ℝ) : Fin 2 → ℝ := ![1 - r, r]

/-- **Example 2.3.1 (2.31).** `D(p‖q) = (1 - r) log ((1 - r)/(1 - s)) + r log (r/s)`. -/
lemma example_2_3_1_pq (r s : ℝ) :
    relEntropyReal (bernPMF r) (bernPMF s) =
      (1 - r) * log ((1 - r) / (1 - s)) + r * log (r / s) := by
  simp [relEntropyReal, bernPMF, Fin.sum_univ_two]

/-- **Example 2.3.1 (2.32).** `D(q‖p) = (1 - s) log ((1 - s)/(1 - r)) + s log (s/r)`. -/
lemma example_2_3_1_qp (r s : ℝ) :
    relEntropyReal (bernPMF s) (bernPMF r) =
      (1 - s) * log ((1 - s) / (1 - r)) + s * log (s / r) :=
  example_2_3_1_pq s r

/-- **Example 2.3.1.** If `r = s`, then `D(p‖q) = D(q‖p) = 0`. -/
lemma example_2_3_1_eq (r : ℝ) : relEntropyReal (bernPMF r) (bernPMF r) = 0 := by
  rw [example_2_3_1_pq]
  have h : ∀ x : ℝ, x * log (x / x) = 0 := fun x => by
    rcases eq_or_ne x 0 with rfl | hx <;> simp [*]
  rw [h, h, add_zero]

/-- **Example 2.3.1 (2.33).** For `r = 1/2`, `s = 1/4`: `D(p‖q) = 1 - ½ log₂ 3` bits. -/
lemma example_2_3_1_pq_val :
    relEntropyReal (bernPMF (1 / 2)) (bernPMF (1 / 4)) / log 2 = 1 - 1 / 2 * (log 3 / log 2) := by
  rw [example_2_3_1_pq]
  have h1 : log ((1 - 1 / 2 : ℝ) / (1 - 1 / 4)) = log 2 - log 3 := by
    rw [show (1 - 1 / 2 : ℝ) / (1 - 1 / 4) = 2 / 3 by norm_num, log_div (by norm_num) (by norm_num)]
  have h2 : log ((1 / 2 : ℝ) / (1 / 4)) = log 2 := by norm_num
  rw [h1, h2]
  field_simp [log_two_pos'.ne']
  ring

/-- **Example 2.3.1 (2.34).** For `r = 1/2`, `s = 1/4`: `D(q‖p) = ¾ log₂ 3 - 1` bits. -/
lemma example_2_3_1_qp_val :
    relEntropyReal (bernPMF (1 / 4)) (bernPMF (1 / 2)) / log 2 = 3 / 4 * (log 3 / log 2) - 1 := by
  rw [example_2_3_1_pq]
  have h1 : log ((1 - 1 / 4 : ℝ) / (1 - 1 / 2)) = log 3 - log 2 := by
    rw [show (1 - 1 / 4 : ℝ) / (1 - 1 / 2) = 3 / 2 by norm_num, log_div (by norm_num) (by norm_num)]
  have h2 : log ((1 / 4 : ℝ) / (1 / 2)) = -log 2 := by
    rw [show (1 / 4 : ℝ) / (1 / 2) = 2⁻¹ by norm_num, log_inv]
  rw [h1, h2]
  field_simp [log_two_pos'.ne']
  ring

/-- **Example 2.3.1 (2.33).** Numerically, `D(p‖q) = 0.2075` bits (to four decimals). -/
lemma example_2_3_1_pq_approx :
    |relEntropyReal (bernPMF (1 / 2)) (bernPMF (1 / 4)) / log 2 - 0.2075| < 0.0001 := by
  rw [example_2_3_1_pq_val]
  obtain ⟨h1, h2⟩ := log_three_div_log_two_bounds
  rw [abs_lt]; constructor <;> linarith

/-- **Example 2.3.1 (2.34).** Numerically, `D(q‖p) = 0.1887` bits (to four decimals). -/
lemma example_2_3_1_qp_approx :
    |relEntropyReal (bernPMF (1 / 4)) (bernPMF (1 / 2)) / log 2 - 0.1887| < 0.0001 := by
  rw [example_2_3_1_qp_val]
  obtain ⟨h1, h2⟩ := log_three_div_log_two_bounds
  rw [abs_lt]; constructor <;> linarith

/-- **Example 2.3.1.** `D(p‖q) ≠ D(q‖p)` in general: relative entropy is not symmetric. -/
lemma example_2_3_1_not_symm :
    relEntropyReal (bernPMF (1 / 2)) (bernPMF (1 / 4)) ≠
      relEntropyReal (bernPMF (1 / 4)) (bernPMF (1 / 2)) := by
  intro h
  have h1 := example_2_3_1_pq_approx
  have h2 := example_2_3_1_qp_approx
  rw [h] at h1
  rw [abs_lt] at h1 h2
  linarith [h1.1, h2.2]

/-- **Section 2.3.** Relative entropy does not satisfy the triangle inequality:
for `p = (1, 0)`, `q = (1/2, 1/2)` and `r = (1/4, 3/4)`, `D(p‖r) > D(p‖q) + D(q‖r)`. -/
lemma relEntropy_not_triangle :
    relEntropyReal (bernPMF 0) (bernPMF (3 / 4)) >
      relEntropyReal (bernPMF 0) (bernPMF (1 / 2)) +
        relEntropyReal (bernPMF (1 / 2)) (bernPMF (3 / 4)) := by
  simp only [example_2_3_1_pq]
  have h3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  have e1 : log ((1 - 0 : ℝ) / (1 - 3 / 4)) = 2 * log 2 := by
    rw [show (1 - 0 : ℝ) / (1 - 3 / 4) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have e2 : log ((1 - 0 : ℝ) / (1 - 1 / 2)) = log 2 := by norm_num
  have e3 : log ((1 - 1 / 2 : ℝ) / (1 - 3 / 4)) = log 2 := by norm_num
  have e4 : log ((1 / 2 : ℝ) / (3 / 4)) = log 2 - log 3 := by
    rw [show (1 / 2 : ℝ) / (3 / 4) = 2 / 3 by norm_num, log_div (by norm_num) (by norm_num)]
  rw [e1, e2, e3, e4]
  simp only [zero_mul, add_zero, sub_zero, one_mul]
  linarith

/-! ## 2.4 Relationship between entropy and mutual information -/

/-- **Theorem 2.4.1 (Mutual information and entropy).** -/
theorem theorem_2_4_1 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] ∧
    I[X : Y ; μ] = H[Y ; μ] - H[Y | X ; μ] ∧
    I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[pair X Y ; μ] ∧
    I[X : Y ; μ] = I[Y : X ; μ] ∧
    I[X : X ; μ] = H[X ; μ] :=
  ⟨mutualInfo_eq_entropy_sub_condEntropy hμ X Y, mutualInfo_eq_entropy_sub_condEntropy' hμ X Y,
    mutualInfo_eq_add_sub hμ X Y, mutualInfo_comm hμ X Y, mutualInfo_self hμ X⟩

/-- **Example 2.4.1.** For the joint distribution of Example 2.2.1, `I(X;Y) = 0.375` bits. -/
lemma example_2_4_1 : I[Prod.fst : Prod.snd ; pmf_2_2_1] / log 2 = 0.375 := by
  rw [mutualInfo_eq_entropy_sub_condEntropy pmf_2_2_1_isPMF, sub_div, example_2_2_1_HX,
    example_2_2_1_HX_given_Y]; norm_num

/-- **Example 2.4.1.** `I(X;Y) = H(X) - H(X|Y) = H(Y) - H(Y|X)` in Example 2.2.1. -/
lemma example_2_4_1' : I[Prod.fst : Prod.snd ; pmf_2_2_1] / log 2 =
    (H[Prod.snd ; pmf_2_2_1] - H[Prod.snd | Prod.fst ; pmf_2_2_1]) / log 2 := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' pmf_2_2_1_isPMF]

/-! ## 2.6 Jensen's inequality and its consequences -/

/-- **Definition (2.72).** A function `f` is convex over an interval `(a, b)` if for every
`x₁, x₂ ∈ (a, b)` and `0 ≤ λ ≤ 1`, `f(λ x₁ + (1 - λ) x₂) ≤ λ f(x₁) + (1 - λ) f(x₂)`. -/
def ConvexOver (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t * x₁ + (1 - t) * x₂) ≤ t * f x₁ + (1 - t) * f x₂

/-- **Definition.** `f` is strictly convex over `(a, b)` if equality in (2.72) holds only if
`λ = 0` or `λ = 1` (for distinct points `x₁ ≠ x₂`, which the book leaves implicit). -/
def StrictConvexOver (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x₁ ∈ Set.Ioo a b, ∀ x₂ ∈ Set.Ioo a b, x₁ ≠ x₂ → ∀ t : ℝ, 0 < t → t < 1 →
    f (t * x₁ + (1 - t) * x₂) < t * f x₁ + (1 - t) * f x₂

/-- **Definition.** A function `f` is concave if `-f` is convex. -/
def ConcaveOver (f : ℝ → ℝ) (a b : ℝ) : Prop := ConvexOver (-f) a b

/-- The book's definition of convexity agrees with Mathlib's `ConvexOn`. -/
lemma convexOver_iff (f : ℝ → ℝ) (a b : ℝ) : ConvexOver f a b ↔ ConvexOn ℝ (Set.Ioo a b) f := by
  constructor
  · intro h
    refine ⟨convex_Ioo a b, fun x hx y hy s t hs ht hst => ?_⟩
    obtain rfl : t = 1 - s := by linarith
    simpa [smul_eq_mul] using h x hx y hy s hs (by linarith)
  · intro h x₁ h₁ x₂ h₂ t ht0 ht1
    simpa [smul_eq_mul] using h.2 h₁ h₂ ht0 (by linarith : 0 ≤ 1 - t) (by ring)

/-- The book's definition of strict convexity agrees with Mathlib's `StrictConvexOn`. -/
lemma strictConvexOver_iff (f : ℝ → ℝ) (a b : ℝ) :
    StrictConvexOver f a b ↔ StrictConvexOn ℝ (Set.Ioo a b) f := by
  constructor
  · intro h
    refine ⟨convex_Ioo a b, fun x hx y hy hxy s t hs ht hst => ?_⟩
    obtain rfl : t = 1 - s := by linarith
    simpa [smul_eq_mul] using h x hx y hy hxy s hs (by linarith)
  · intro h x₁ h₁ x₂ h₂ hne t ht0 ht1
    simpa [smul_eq_mul] using h.2 h₁ h₂ hne ht0 (by linarith : 0 < 1 - t) (by ring)

/-- The book's definition of concavity agrees with Mathlib's `ConcaveOn`. -/
lemma concaveOver_iff (f : ℝ → ℝ) (a b : ℝ) : ConcaveOver f a b ↔ ConcaveOn ℝ (Set.Ioo a b) f := by
  rw [ConcaveOver, convexOver_iff, neg_convexOn_iff]

/-- "A function is convex if it always lies below any chord": the chord through `(x₁, f x₁)` and
`(x₂, f x₂)` lies above the graph of a convex function between `x₁` and `x₂`. -/
lemma ConvexOver.below_chord {f : ℝ → ℝ} {a b : ℝ} (hf : ConvexOver f a b) {x₁ x₂ : ℝ}
    (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (t * x₁ + (1 - t) * x₂) ≤ t * f x₁ + (1 - t) * f x₂ :=
  hf x₁ h₁ x₂ h₂ t ht0 ht1

/-- "A function is concave if it always lies above any chord." -/
lemma ConcaveOver.above_chord {f : ℝ → ℝ} {a b : ℝ} (hf : ConcaveOver f a b) {x₁ x₂ : ℝ}
    (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * f x₁ + (1 - t) * f x₂ ≤ f (t * x₁ + (1 - t) * x₂) := by
  have := hf x₁ h₁ x₂ h₂ t ht0 ht1
  simp only [Pi.neg_apply] at this
  linarith

/-- **Examples of convex functions:** `x²`, `|x|`, `eˣ` and `x log x` (for `x ≥ 0`). -/
lemma convex_examples :
    ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) ∧ ConvexOn ℝ Set.univ (fun x : ℝ => |x|) ∧
      ConvexOn ℝ Set.univ exp ∧ ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x * log x) := by
  refine ⟨Even.convexOn_pow (by decide), ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩,
    convexOn_exp, convexOn_mul_log⟩
  simp only [smul_eq_mul]
  calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ = a * |x| + b * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- **Examples of concave functions:** `log x` (for `x > 0`) and `√x` (for `x ≥ 0`). -/
lemma concave_examples :
    ConcaveOn ℝ (Set.Ioi 0) log ∧ ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => √x) :=
  ⟨strictConcaveOn_log_Ioi.concaveOn, strictConcaveOn_sqrt.concaveOn⟩

/-- Linear functions `ax + b` are both convex and concave. -/
lemma linear_convex_concave (a b : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => a * x + b) ∧
      ConcaveOn ℝ Set.univ (fun x : ℝ => a * x + b) := by
  have : IsLinearMap ℝ (fun x : ℝ => a * x) :=
    ⟨fun x y => by ring, fun c x => by simp [smul_eq_mul]; ring⟩
  refine ⟨⟨convex_univ, fun x _ y _ s t _ _ hst => le_of_eq ?_⟩,
    ⟨convex_univ, fun x _ y _ s t _ _ hst => le_of_eq ?_⟩⟩ <;>
  · simp only [smul_eq_mul]
    obtain rfl : t = 1 - s := by linarith
    ring

/-- **Theorem 2.6.1.** If `f'' ≥ 0` everywhere then `f` is convex. -/
theorem convexOn_of_deriv2_nonneg_univ {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (h : ∀ x, 0 ≤ deriv^[2] f x) : ConvexOn ℝ Set.univ f :=
  convexOn_univ_of_deriv2_nonneg hf hf' h

/-- **Theorem 2.6.1.** If `f'' > 0` everywhere then `f` is strictly convex. -/
theorem strictConvexOn_of_deriv2_pos_univ {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ x, 0 < deriv^[2] f x) : StrictConvexOn ℝ Set.univ f :=
  strictConvexOn_univ_of_deriv2_pos hf h

/-- **Theorem 2.6.1** on an interval (or any convex set `D`): `f'' ≥ 0` on the interior gives
convexity. -/
theorem convexOn_of_deriv2_nonneg_interval {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (h : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hf hf' hf'' h

/-- **Theorem 2.6.1** on an interval (or any convex set `D`): `f'' > 0` on the interior gives
strict convexity. -/
theorem strictConvexOn_of_deriv2_pos_interval {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (h : ∀ x ∈ interior D, 0 < deriv^[2] f x) :
    StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos hD hf h

/-- Theorem 2.6.1 gives the strict convexity of `x²`, since `(x²)'' = 2 > 0`. -/
lemma strictConvexOn_sq : StrictConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
  apply strictConvexOn_of_deriv2_pos_univ (continuous_pow 2)
  intro x; simp [Finset.prod_range_succ]

/-- Theorem 2.6.1 gives the strict convexity of `eˣ`, since `(eˣ)'' = eˣ > 0`. -/
lemma strictConvexOn_exp' : StrictConvexOn ℝ Set.univ exp := by
  apply strictConvexOn_of_deriv2_pos_univ continuous_exp
  intro x; simp [exp_pos]

/-- Theorem 2.6.1 gives the strict convexity of `x log x` for `x ≥ 0`, since
`(x log x)'' = 1/x > 0`. -/
lemma strictConvexOn_mul_log' : StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x * log x) := by
  apply strictConvexOn_of_deriv2_pos_interval (convex_Ici 0) continuous_mul_log.continuousOn
  intro x hx
  rw [interior_Ici, Set.mem_Ioi] at hx
  rw [deriv2_mul_log]; positivity

/-- Theorem 2.6.1 gives the strict concavity of `log x` (`x > 0`) and of `√x` (`x ≥ 0`). -/
lemma strictConcave_log_sqrt :
    StrictConcaveOn ℝ (Set.Ioi 0) log ∧ StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => √x) :=
  ⟨strictConcaveOn_log_Ioi, strictConcaveOn_sqrt⟩

/-- The joint distribution of **Example 2.6.1** on `Fin 2 × Fin 2` (points `(x, y)`, with the
book's values `1, 2` relabelled `0, 1`): `p(1,1) = 0`, `p(2,1) = 3/4`, `p(1,2) = 1/8`,
`p(2,2) = 1/8`. -/
def pmf_2_6_1 : Fin 2 × Fin 2 → ℝ := fun z => ![![0, 3 / 4], ![1 / 8, 1 / 8]] z.2 z.1

lemma pmf_2_6_1_isPMF : IsPMF pmf_2_6_1 := by
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨x, y⟩ := z
    fin_cases x <;> fin_cases y <;> norm_num [pmf_2_6_1]
  · simp [pmf_2_6_1, Fintype.sum_prod_type]; norm_num

lemma example_2_6_1_dist_X : dist pmf_2_6_1 Prod.fst = ![1 / 8, 7 / 8] := by
  funext a; rw [dist_fst]; fin_cases a <;> norm_num [pmf_2_6_1]

lemma example_2_6_1_dist_Y : dist pmf_2_6_1 Prod.snd = ![3 / 4, 1 / 4] := by
  funext b; rw [dist_snd]; fin_cases b <;> norm_num [pmf_2_6_1]

/-- `H(1/8, 7/8) = 3 - (7/8) log₂ 7` bits. -/
lemma example_2_6_1_HX_exact : H[Prod.fst ; pmf_2_6_1] / log 2 = 3 - 7 / 8 * (log 7 / log 2) := by
  have h2 := log_two_pos'.ne'
  rw [entropyRV, example_2_6_1_dist_X, entropy_eq_sum_negMulLog, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (1 / 8 : ℝ) = ((2 : ℝ) ^ 3)⁻¹ by norm_num, negMulLog_inv_two_pow, negMulLog,
    show (7 / 8 : ℝ) = 7 / 2 ^ 3 by norm_num, log_div (by norm_num) (by norm_num), log_pow]
  field_simp
  ring

/-- **Example 2.6.1.** `H(X) = H(1/8, 7/8) = 0.544` bits (to three decimals). -/
lemma example_2_6_1_HX : |H[Prod.fst ; pmf_2_6_1] / log 2 - 0.544| < 0.0005 := by
  rw [example_2_6_1_HX_exact]
  obtain ⟨h1, h2⟩ := log_seven_div_log_two_bounds
  rw [abs_lt]; constructor <;> linarith

/-- **Example 2.6.1.** `H(X | Y = 1) = 0` bits. -/
lemma example_2_6_1_HX_given_Y1 : condEntropyAt pmf_2_6_1 Prod.fst Prod.snd 0 = 0 := by
  simp only [condEntropyAt, condDist, dist_pair_snd_fst, example_2_6_1_dist_Y,
    entropy_eq_sum_negMulLog, Fin.sum_univ_two]
  simp [pmf_2_6_1]

/-- **Example 2.6.1.** `H(X | Y = 2) = 1` bit. -/
lemma example_2_6_1_HX_given_Y2 : condEntropyAt pmf_2_6_1 Prod.fst Prod.snd 1 / log 2 = 1 := by
  have h2 := log_two_pos'.ne'
  simp only [condEntropyAt, condDist, dist_pair_snd_fst, example_2_6_1_dist_Y,
    entropy_eq_sum_negMulLog, Fin.sum_univ_two]
  have e0 : pmf_2_6_1 (0, 1) / (![3 / 4, 1 / 4] : Fin 2 → ℝ) 1 = 2⁻¹ := by norm_num [pmf_2_6_1]
  have e1 : pmf_2_6_1 (1, 1) / (![3 / 4, 1 / 4] : Fin 2 → ℝ) 1 = 2⁻¹ := by norm_num [pmf_2_6_1]
  rw [e0, e1, negMulLog_two_inv]
  field_simp
  ring

/-- **Example 2.6.1.** `H(X|Y) = (3/4) H(X|Y = 1) + (1/4) H(X|Y = 2) = 0.25` bits. -/
lemma example_2_6_1_HX_given_Y : H[Prod.fst | Prod.snd ; pmf_2_6_1] / log 2 = 0.25 := by
  have h2 := log_two_pos'.ne'
  have e2 := example_2_6_1_HX_given_Y2
  rw [condEntropy, Fin.sum_univ_two, example_2_6_1_HX_given_Y1, example_2_6_1_dist_Y]
  rw [div_eq_iff h2] at e2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e2]
  field_simp
  ring

/-- **Remark after Theorem 2.6.5 (Example 2.6.1).** The uncertainty in `X` is increased if `Y = 2`
is observed and decreased if `Y = 1` is observed, but it decreases on average:
`H(X|Y = 1) < H(X) < H(X|Y = 2)` while `H(X|Y) < H(X)`. -/
lemma example_2_6_1_remark :
    condEntropyAt pmf_2_6_1 Prod.fst Prod.snd 0 < H[Prod.fst ; pmf_2_6_1] ∧
    H[Prod.fst ; pmf_2_6_1] < condEntropyAt pmf_2_6_1 Prod.fst Prod.snd 1 ∧
    H[Prod.fst | Prod.snd ; pmf_2_6_1] < H[Prod.fst ; pmf_2_6_1] := by
  have h2 := log_two_pos'
  have hX := example_2_6_1_HX
  have hY2 := example_2_6_1_HX_given_Y2
  have hXY := example_2_6_1_HX_given_Y
  rw [abs_lt] at hX
  rw [div_eq_iff h2.ne'] at hY2 hXY
  refine ⟨?_, ?_, ?_⟩
  · rw [example_2_6_1_HX_given_Y1]
    have : 0 < H[Prod.fst ; pmf_2_6_1] / log 2 := by linarith [hX.1]
    exact (div_pos_iff_of_pos_right h2).1 this
  · rw [hY2]
    have : H[Prod.fst ; pmf_2_6_1] / log 2 < 1 := by linarith [hX.2]
    rw [div_lt_iff₀ h2] at this; linarith
  · rw [hXY]
    have : 0.25 < H[Prod.fst ; pmf_2_6_1] / log 2 := by linarith [hX.1]
    rw [lt_div_iff₀ h2] at this; linarith

/-! ## 2.8 Data processing inequality -/

/-- Two independent fair bits: the uniform pmf on `Fin 2 × Fin 2`. -/
def pmfTwoBits : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4

lemma pmfTwoBits_isPMF : IsPMF pmfTwoBits :=
  ⟨fun _ => by norm_num [pmfTwoBits], by simp [pmfTwoBits]⟩

/-- `Z = X + Y ∈ {0, 1, 2}`. -/
def sumBits (ω : Fin 2 × Fin 2) : Fin 3 := ⟨ω.1.val + ω.2.val, by omega⟩

/-- **Example (Section 2.8).** If `X` and `Y` are independent fair bits then `I(X;Y) = 0`. -/
lemma example_2_8_indep : I[Prod.fst : Prod.snd ; pmfTwoBits] = 0 := by
  rw [mutualInfo_eq_zero_iff pmfTwoBits_isPMF]
  intro x y
  rw [dist_pair_fst_snd, dist_fst, dist_snd]
  simp [pmfTwoBits]; norm_num

/-- **Example (Section 2.8).** If `X` and `Y` are independent fair bits and `Z = X + Y`, then
`I(X;Y|Z) = 1/2` bit, so `I(X;Y|Z) > I(X;Y)` when `X, Y, Z` do not form a Markov chain. -/
lemma example_2_8_cond : I[Prod.fst : Prod.snd | sumBits ; pmfTwoBits] / log 2 = 1 / 2 := by
  have h2 := log_two_pos'.ne'
  have hμ := pmfTwoBits_isPMF
  -- `H(X | Y, Z) = 0` since `X = Z - Y`, and `(Z, X)` is an injective function of `(X, Y)`.
  have hinj1 : H[pair (pair Prod.snd sumBits) Prod.fst ; pmfTwoBits] =
      H[pair Prod.snd sumBits ; pmfTwoBits] := by
    rw [show pair (pair Prod.snd sumBits) Prod.fst =
      (fun t : Fin 2 × Fin 3 =>
        (t, (⟨(t.2.val - t.1.val) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)))
        ∘ pair Prod.snd sumBits from ?_]
    · exact entropyRV_comp_injective _ _ (fun a b h => (Prod.mk.inj h).1)
    · funext ω
      obtain ⟨x, y⟩ := ω
      simp only [pair_apply, Function.comp_apply, Prod.mk.injEq, true_and]
      ext; simp [sumBits]; omega
  have hinj2 : H[pair Prod.snd sumBits ; pmfTwoBits] = H[id ; pmfTwoBits] :=
    entropyRV_eq_of_injective _ (fun ω : Fin 2 × Fin 2 => (ω.2, sumBits ω))
      (fun a b h => by
        obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
        simp only [Prod.mk.injEq, sumBits, Fin.ext_iff] at h ⊢
        omega) (fun _ => rfl)
  have hinj3 : H[pair sumBits Prod.fst ; pmfTwoBits] = H[id ; pmfTwoBits] :=
    entropyRV_eq_of_injective _ (fun ω : Fin 2 × Fin 2 => (sumBits ω, ω.1))
      (fun a b h => by
        obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
        simp only [Prod.mk.injEq, sumBits, Fin.ext_iff] at h ⊢
        omega) (fun _ => rfl)
  have hid : H[id ; pmfTwoBits] = 2 * log 2 := by
    rw [entropyRV, dist_id, entropy_eq_sum_negMulLog]
    simp [pmfTwoBits, negMulLog_four_inv]; ring
  have hZ : H[sumBits ; pmfTwoBits] = 3 / 2 * log 2 := by
    have hd : dist pmfTwoBits sumBits = ![1 / 4, 1 / 2, 1 / 4] := by
      funext k
      simp only [dist, pmfTwoBits, Fintype.sum_prod_type, Fin.sum_univ_two]
      fin_cases k <;> norm_num [sumBits, Fin.ext_iff]
    rw [entropyRV, hd, entropy_eq_sum_negMulLog, Fin.sum_univ_three]
    simp [negMulLog_two_inv, negMulLog_four_inv]; ring
  rw [condMutualInfo, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ, hinj1, hinj3, hZ, hid]
  field_simp
  ring

/-! ## 2.9 Sufficient statistics -/

/-- **Example 2 (2.126).** For `X₁, …, Xₙ` i.i.d. `𝒩(θ, 1)`, the joint density factors as
`∏ f_θ(xᵢ) = exp(-n (x̄ - θ)²/2) h(x)`, so it depends on `θ` only through the sample mean.
By the factorization criterion this is why `X̄ₙ` is a sufficient statistic for `θ`: the
conditional law of the sample given `X̄ₙ` does not depend on `θ`. The book defers continuous
random variables to Chapter 8, so we formalize this factorization. -/
theorem example_2_9_2 {ι : Type*} [Fintype ι] (hn : 0 < Fintype.card ι) :
    ∃ h : (ι → ℝ) → ℝ, ∀ (θ : ℝ) (x : ι → ℝ),
      ∏ i, ProbabilityTheory.gaussianPDFReal θ 1 (x i) =
        exp (-(Fintype.card ι : ℝ) * (sampleMean x - θ) ^ 2 / 2) * h x := by
  refine ⟨fun x => (√(2 * π))⁻¹ ^ Fintype.card ι * exp (-(∑ i, (x i - sampleMean x) ^ 2) / 2),
    fun θ x => ?_⟩
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one]
  rw [prod_mul_distrib, prod_const, card_univ, ← exp_sum]
  have : ∑ i, -(x i - θ) ^ 2 / 2 = -(Fintype.card ι : ℝ) * (sampleMean x - θ) ^ 2 / 2 +
      -(∑ i, (x i - sampleMean x) ^ 2) / 2 := by
    rw [← sum_div, sum_neg_distrib, sum_sq_sub_eq hn x θ]; ring
  rw [this, exp_add]; ring

/-- **Example 3 (2.127).** For `X₁, …, Xₙ` i.i.d. uniform on `(θ, θ + 1)`, the joint density
`∏ 1{θ < xᵢ < θ + 1}` equals `1{θ < min xᵢ} 1{max xᵢ < θ + 1}`, so it depends on the sample
only through `T(X) = (max Xᵢ, min Xᵢ)`, a sufficient statistic for `θ`. -/
theorem example_2_9_3 {n : ℕ} (θ : ℝ) (x : Fin (n + 1) → ℝ) :
    ∏ i, Set.indicator (Set.Ioo θ (θ + 1)) (fun _ => (1 : ℝ)) (x i) =
      (if θ < univ.inf' univ_nonempty x then 1 else 0) *
        (if univ.sup' univ_nonempty x < θ + 1 then 1 else 0) := by
  simp only [Set.indicator_apply, Set.mem_Ioo]
  by_cases h : ∀ i, θ < x i ∧ x i < θ + 1
  · rw [prod_eq_one (fun i _ => by simp [h i])]
    have h1 : θ < univ.inf' univ_nonempty x := by
      simp only [lt_inf'_iff, mem_univ, true_implies]; exact fun i => (h i).1
    have h2 : univ.sup' univ_nonempty x < θ + 1 := by
      simp only [sup'_lt_iff, mem_univ, true_implies]; exact fun i => (h i).2
    simp [h1, h2]
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [prod_eq_zero (mem_univ i) (by simp only [hi]; simp)]
    rw [not_and_or, not_lt, not_lt] at hi
    rcases hi with hi | hi
    · have : univ.inf' univ_nonempty x ≤ θ := (inf'_le _ (mem_univ i)).trans hi
      simp [not_lt.2 this]
    · have : θ + 1 ≤ univ.sup' univ_nonempty x := hi.trans (le_sup' _ (mem_univ i))
      simp [not_lt.2 this]

/-- A sample of size `2m` arranged in pairs: `x (j, 0) = X_{2j+1}` (odd samples) and
`x (j, 1) = X_{2j+2}` (even samples). The mean of the odd samples. -/
def oddMean {m : ℕ} (x : Fin m × Fin 2 → ℝ) : ℝ := (∑ j, x (j, 0)) / m

/-- The mean of the even samples. -/
def evenMean {m : ℕ} (x : Fin m × Fin 2 → ℝ) : ℝ := (∑ j, x (j, 1)) / m

lemma sampleMean_eq_odd_even {m : ℕ} (hm : 0 < m) (x : Fin m × Fin 2 → ℝ) :
    sampleMean x = (oddMean x + evenMean x) / 2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [sampleMean, oddMean, evenMean, Fintype.sum_prod_type, Fin.sum_univ_two,
    sum_add_distrib, Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

/-- **Section 2.9.** For the normal family, the pair (mean of the odd samples, mean of
the even samples) is a sufficient statistic: the likelihood factors through it, because the
overall mean `X̄` is a function of the pair. -/
theorem odd_even_means_sufficient {m : ℕ} (hm : 0 < m) :
    ∃ (g : ℝ → ℝ × ℝ → ℝ) (h : (Fin m × Fin 2 → ℝ) → ℝ), ∀ (θ : ℝ) (x : Fin m × Fin 2 → ℝ),
      ∏ i, ProbabilityTheory.gaussianPDFReal θ 1 (x i) = g θ (oddMean x, evenMean x) * h x := by
  have hn : 0 < Fintype.card (Fin m × Fin 2) := by simp [hm]
  obtain ⟨h, hh⟩ := example_2_9_2 hn
  refine ⟨fun θ t => exp (-(Fintype.card (Fin m × Fin 2) : ℝ) * ((t.1 + t.2) / 2 - θ) ^ 2 / 2),
    h, fun θ x => ?_⟩
  rw [hh θ x, sampleMean_eq_odd_even hm]

/-- **Section 2.9.** The pair of odd/even means is not a minimal sufficient statistic:
it is not a function of the sufficient statistic `X̄`, since two samples can have the same `X̄`
but different odd/even means. -/
theorem odd_even_means_not_function_of_mean {m : ℕ} (hm : 0 < m) :
    ¬ ∃ g : ℝ → ℝ × ℝ, ∀ x : Fin m × Fin 2 → ℝ, (oddMean x, evenMean x) = g (sampleMean x) := by
  rintro ⟨g, hg⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let x : Fin m × Fin 2 → ℝ := fun i => if i.2 = 0 then 1 else 0
  let y : Fin m × Fin 2 → ℝ := fun i => if i.2 = 0 then 0 else 1
  have hx : oddMean x = 1 := by simp [x, oddMean, hm']
  have hy : oddMean y = 0 := by simp [y, oddMean]
  have hxy : sampleMean x = sampleMean y := by
    rw [sampleMean_eq_odd_even hm, sampleMean_eq_odd_even hm]
    simp [x, y, oddMean, evenMean, hm']
  have := congrArg Prod.fst ((hg x).trans ((congrArg g hxy).trans (hg y).symm))
  simp only at this
  rw [hx, hy] at this
  exact one_ne_zero this

/-! ## 2.10 Fano's inequality -/

/-- **Lemma 2.10.1**, in bits. If `X` and `X'` are i.i.d. with pmf `p`, then
`Pr(X = X') = ∑ₓ p(x)² ≥ 2^{-H(X)}`, where `H(X) = H(p) / log 2` is the entropy in bits. -/
theorem lemma_2_10_1_bits {p : α → ℝ} (hp : IsPMF p) :
    (2 : ℝ) ^ (-(entropy p / log 2)) ≤ ∑ x, p x ^ 2 := by
  rw [rpow_def_of_pos two_pos, mul_neg, mul_div_cancel₀ _ log_two_pos'.ne']
  exact exp_neg_entropy_le_sum_sq hp

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered lemmas and theorems of Chapter 2.
-/

/-- **Lemma 2.1.1.** `H(X) ≥ 0`. -/
alias lemma_2_1_1 := entropy_nonneg

/-- **Lemma 2.1.2.** `H_b(X) = (log_b a) H_a(X)`. -/
alias lemma_2_1_2 := entropyBase_eq

/-- **Theorem 2.2.1 (Chain rule).** `H(X, Y) = H(X) + H(Y | X)`. -/
alias theorem_2_2_1 := chain_rule

/-- **Theorem 2.5.1 (Chain rule for entropy).** -/
alias theorem_2_5_1 := chain_rule_entropy

/-- **Theorem 2.5.2 (Chain rule for information).** -/
alias theorem_2_5_2 := chain_rule_mutualInfo

/-- **Theorem 2.5.3 (Chain rule for relative entropy).** -/
alias theorem_2_5_3 := chain_rule_relEntropy

/-- **Theorem 2.6.1.** A function with non-negative second derivative is convex. -/
alias theorem_2_6_1 := convexOn_of_deriv2_nonneg_interval

/-- **Theorem 2.6.2 (Jensen's inequality).** -/
alias theorem_2_6_2 := jensen

/-- **Theorem 2.6.3 (Information inequality).** `D(p ‖ q) ≥ 0`. -/
alias theorem_2_6_3 := relEntropyReal_nonneg

/-- **Theorem 2.6.4.** `H(X) ≤ log |𝒳|`. -/
alias theorem_2_6_4 := entropy_le_log_card

/-- **Theorem 2.6.5 (Conditioning reduces entropy).** `H(X | Y) ≤ H(X)`. -/
alias theorem_2_6_5 := condEntropy_le_entropy

/-- **Theorem 2.6.6 (Independence bound on entropy).** `H(X₁, …, Xₙ) ≤ ∑ᵢ H(Xᵢ)`. -/
alias theorem_2_6_6 := entropy_prefixRV_le_sum

/-- **Theorem 2.7.1 (Log sum inequality).** -/
alias theorem_2_7_1 := log_sum_inequality

/-- **Theorem 2.7.2.** `D(p ‖ q)` is convex in the pair `(p, q)`. -/
alias theorem_2_7_2 := relEntropyReal_convex_pair

/-- **Theorem 2.7.3 (Concavity of entropy).** -/
alias theorem_2_7_3 := entropy_concaveOn

/-- **Theorem 2.7.4 (first part).** `I(X; Y)` is concave in `p(x)` for fixed `p(y | x)`. -/
alias theorem_2_7_4_concave := mutualInfoOf_concave_input

/-- **Theorem 2.7.4 (second part).** `I(X; Y)` is convex in `p(y | x)` for fixed `p(x)`. -/
alias theorem_2_7_4_convex := mutualInfoOf_convex_channel

/-- **Theorem 2.8.1 (Data processing inequality).** -/
alias theorem_2_8_1 := data_processing

/-- **Example 1 of Section 2.9 (2.125).** -/
alias example_2_9_1 := condDist_numOnes

/-- **Theorem 2.10.1 (Fano's inequality).** `H(Pₑ) + Pₑ log |𝒳| ≥ H(X | X̂) ≥ H(X | Y)`. -/
alias theorem_2_10_1 := fano_estimator

/-- **Lemma 2.10.1.** `Pr(X = X') ≥ 2^{-H(X)}` for i.i.d. `X` and `X'` (in nats, `e^{-H(X)}`). -/
alias lemma_2_10_1 := exp_neg_entropy_le_sum_sq

end InfoTheory.CoverThomas
