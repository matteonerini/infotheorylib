/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Book.Chapter2
public import InfoTheoryLib.Book.Chapter16
public import InfoTheoryLib.DifferentialEntropy.ChainRule
public import InfoTheoryLib.DifferentialEntropy.Estimation
public import InfoTheoryLib.MarkovChain.SecondLaw
public import InfoTheoryLib.Inequalities.Han
public import InfoTheoryLib.Inequalities.SubsetEntropy
public import InfoTheoryLib.Inequalities.EntropyBounds
public import InfoTheoryLib.Inequalities.Binomial
public import InfoTheoryLib.Inequalities.Schur
public import InfoTheoryLib.Inequalities.Determinant
public import InfoTheoryLib.Inequalities.Toeplitz

/-!
# Cover & Thomas, Chapter 17: Inequalities in Information Theory

This file indexes the formalization of Chapter 17 of [cover2006]. The chapter collects
inequalities proved earlier in the book (Sections 17.1–17.4 and 17.7, and Theorems 17.9.1–17.9.2)
and proves new ones: bounds on entropy and relative entropy, bounds on binomial coefficients,
Han's inequalities for subsets of random variables, and inequalities for determinants. The new
results live in the `Inequalities` topic modules of `InfoTheoryLib`. The list below gives each
numbered result with the declaration that proves it, and the last section of this file defines
aliases `theorem_17_1_11`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Logarithms** are natural, so entropies are in nats; the book's `2^{-nH(p)}` with `H` in bits
  is our `e^{-nH(p)}` with `H` in nats.
* **Entropy rates of subsets.** Han's inequalities are proved for any submodular set function `f`
  on the subsets of `Fin n` with `f(∅) = 0` (`Inequalities.Han`); the averages `h⁽ⁿ⁾ₖ`, `t⁽ⁿ⁾ₖ`,
  `g⁽ⁿ⁾ₖ`, `f⁽ⁿ⁾ₖ` of (17.51)–(17.65) are `subsetAvg`, `subsetExpAvg`, `subsetCondAvg` and
  `subsetMutAvg`. The book states them for differential entropies; we apply them to the entropies
  of discrete random variables (`subsetEntropy`, `Inequalities.SubsetEntropy`) and, for the
  Gaussian case, to `log |K(S)|` (`logMinor`, `Inequalities.Determinant`).
* **Determinants.** The principal minor `|K(S)|` is `principalMinor K S`. The determinant
  inequalities are proved with matrix algebra (Schur complements) instead of Gaussian random
  vectors; the submodularity of `log |K(S)|` (Koteljanskii's inequality) replaces the entropy
  inequalities of Section 17.6.
* **Toeplitz matrices** are infinite matrices `K : ℕ → ℕ → ℝ` with `K (i+1) (j+1) = K i j`, and
  `Kₖ = leadingSection K k`; an `n × n` Toeplitz matrix is a leading section.
* **Ratios of determinants.** In Section 17.10 the matrix is indexed by `m ⊕ p`, and the book's
  `Kₙ₋ₚ` is the leading block `K.toBlocks₁₁`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 17.1 Basic inequalities of information theory
* Theorem 17.1.1 (Jensen's inequality): `jensen` (`Probability.Jensen`); Lemma 17.1.1:
  `strictConcaveOn_log_Ioi`, `Real.convexOn_mul_log` (Mathlib).
* Theorem 17.1.2 (log sum inequality): `log_sum_inequality` (`Analysis.LogSum`).
* Theorem 17.1.3: `entropy_nonneg`, `entropy_le_log_card` (`Entropy.Basic`, `Entropy.Bounds`).
* Theorem 17.1.4: `condEntropy_le_entropy`; Theorem 17.1.5: `chain_rule_entropy`,
  `entropy_prefixRV_le_sum`; Theorem 17.1.6: `entropy_concaveOn`.
* Theorem 17.1.7: `relEntropyReal_nonneg`; Theorem 17.1.8: `relEntropyReal_convex_pair`.
* Theorem 17.1.9: `theorem_2_4_1` (`Book.Chapter2`).
* Theorem 17.1.10 (second law for Markov chains): `relEntropy_step_le`,
  `relEntropy_stationary_antitone`, `entropy_iterate_monotone`, `condEntropy_stationary_monotone`
  (`MarkovChain.SecondLaw`).
* Theorem 17.1.11, (17.16): `expect_relEntropy_typeOf_succ_le`, from
  `typeOf_eq_sum_removeNth` and `convexOn_mul_log_div` (`Inequalities.EntropyBounds`).

### 17.2 Differential entropy
* Definitions (17.17)–(17.19): `diffEntropy`, `relEntropyPDF`, `mutualInfoPDF`
  (`DifferentialEntropy.Basic`, `DifferentialEntropy.RelativeEntropy`,
  `DifferentialEntropy.Joint`).
* Table 17.1: only the uniform, exponential and normal entries, `diffEntropy_uniformPDF`,
  `diffEntropy_expDensity`, `diffEntropy_gaussianPDFReal`, `diffEntropy_mvGaussianPDF`.
* Theorem 17.2.1: `condDiffEntropy_le` (`DifferentialEntropy.Joint`); Theorem 17.2.2:
  `diffEntropy_eq_sum_condDiffEntropyLast` (`DifferentialEntropy.ChainRule`).
* Theorem 17.2.3: `diffEntropy_le_of_covariance` (`DifferentialEntropy.MultivariateGaussian`).

### 17.3 Bounds on entropy and relative entropy
* Theorem 17.3.1 (Fano's inequality): `fano_estimator`; Lemma 17.3.1:
  `exp_neg_entropy_le_sum_sq` (`Entropy.Fano`).
* Theorem 17.3.2, (17.23)–(17.24): `exp_two_mul_diffEntropy_div_le`,
  `exp_two_mul_condDiffEntropy_div_le` (`DifferentialEntropy.Estimation`).
* Theorem 17.3.3 (L₁ bound on entropy), (17.25)–(17.33): `abs_entropy_sub_le`, with (17.27)
  `abs_negMulLog_sub_le` and (17.31)–(17.33) `sum_negMulLog_le` (`Inequalities.EntropyBounds`).
* Lemma 17.3.2 (Pinsker): `pinsker` (`RelativeEntropy.Pinsker`).
* (17.35) and Lemma 17.3.3, (17.36): `chiSq`, `abs_relEntropyReal_sub_chiSq_le`,
  `tendsto_relEntropyReal_div_sq` (`Inequalities.EntropyBounds`).

### 17.4 Inequalities for types
* Theorems 17.4.1–17.4.4, (17.37)–(17.40): `card_types_le`, `iidPMF_eq_exp_type`,
  `exp_div_le_card_typeClass`, `card_typeClass_le`, `exp_div_le_prob_typeClass`,
  `prob_typeClass_le` (`Statistics.Types`).

### 17.5 Combinatorial bounds on entropy
* Lemma 17.5.1, (17.41)–(17.49): `choose_mul_exp_binEntropy_le`, `le_choose_mul_exp_binEntropy`,
  and in the form `C(n, k) pᵏ q^{n-k}`, `choose_mul_pow_le`, `le_choose_mul_pow`, from the
  identity `choose_mul_pow_mul_stirlingSeq` and the bound `stirlingSeq_mul_le`
  (`Inequalities.Binomial`).

### 17.6 Entropy rates of subsets
* (17.50): `entropy_prefixRV_le_sum` (`Entropy.ChainRule`).
* The set functions: `IsSubmodular`, `isSubmodular_subsetEntropy`, `subsetEntropy_empty`
  (`Inequalities.Han`, `Inequalities.SubsetEntropy`).
* (17.51) and Theorem 17.6.1 (Han), (17.52)–(17.54): `subsetAvg`, `subsetAvg_succ_le`, with
  (17.53) `card_sub_one_mul_le_sum_erase`; for entropies, `subsetAvg_entropy_succ_le`.
* (17.55) and Theorem 17.6.2, (17.56)–(17.58): `subsetExpAvg`, `subsetExpAvg_succ_le`,
  `subsetExpAvg_entropy_succ_le`.
* (17.59) and Theorem 17.6.3 (Han), (17.60)–(17.64): `subsetCondAvg`, `subsetCondAvg_le_succ`,
  `subsetCondAvg_entropy_le_succ`, with `condEntropy_subRV_compl` for `H(X(S) | X(Sᶜ))`.
* (17.65) and Theorem 17.6.4, (17.66): `subsetMutAvg`, `subsetMutAvg_succ_le`,
  `subsetMutAvg_entropy_succ_le`, with `mutualInfo_subRV_compl` for `I(X(S); X(Sᶜ))`.

### 17.7 Entropy and Fisher information
* Theorem 17.7.1 (Cramér–Rao inequality): `ParamFamily.cramerRao` (`Statistics.FisherInformation`).

### 17.9 Inequalities for determinants
* Theorem 17.9.1 (log-concavity of the determinant), (17.111)–(17.115):
  `det_rpow_mul_det_rpow_le` (`ForMathlib.MatrixDet`).
* Theorem 17.9.2 (Hadamard), (17.116): `det_le_prod_diag`
  (`DifferentialEntropy.MultivariateGaussian`).
* Koteljanskii's inequality, the Gaussian case of Section 17.6: `det_mul_det_le_of_block`,
  `principalMinor_union_mul_inter_le`, `isSubmodular_logMinor` (`Inequalities.Determinant`), with
  Fischer's inequality `det_le_det_mul_det` (`Inequalities.Schur`).
* Theorem 17.9.3 (Szász), (17.117)–(17.118): `minorProd`, `minorProd_rpow_succ_le`.
* Theorem 17.9.4, (17.119)–(17.120): `minorRootAvg`, `minorRootAvg_succ_le`, `minorRootAvg_one`,
  `minorRootAvg_card`.
* Theorem 17.9.5, (17.121)–(17.123): `condMinorMean`, `condMinorMean_le_succ`,
  `condMinorMean_one`, `condMinorMean_card`.
* (17.124)–(17.125) and Corollary (17.126): `condVar`, `prod_condVar_le_det`,
  `prod_condVar_le_det_le_prod_diag`.
* Theorem 17.9.6, (17.127)–(17.135): `IsToeplitz`, `leadingSection`, `det_ratio_succ_le`,
  `det_rpow_succ_le`, `tendsto_det_rpow_and_ratio`, from `det_leadingSection_mul_le_sq`
  (`Inequalities.Toeplitz`).
* Theorem 17.9.7 (Minkowski), (17.136): `det_rpow_add_det_rpow_le`, with the superadditivity of
  the geometric mean `prod_rpow_add_prod_rpow_le` (`Inequalities.Determinant`).

### 17.10 Inequalities for ratios of determinants
* Lemma 17.10.1, (17.140)–(17.143): `isLeast_det_div_det`, the minimum mean squared error of
  linear prediction; more generally `schurCompl`, `det_div_det_eq`, `quadForm_schurCompl_le`,
  `quadForm_schurCompl_eq` (`Inequalities.Schur`).
* Theorem 17.10.1 (Bergstrøm), (17.144)–(17.148): `det_div_det_rpow_mul_le`,
  `concaveOn_log_det_div_det`, from the Loewner concavity of the Schur complement
  `posSemidef_schurCompl_sub`.
* Theorem 17.10.2 (Bergstrøm), (17.149)–(17.156): `concaveOn_det_div_det`.

## Not formalized

* Lemma 17.2.1 (`h(X + Y) ≥ h(X)` for independent `X`, `Y`), and the entries of Table 17.1 other
  than the uniform, exponential and normal densities.
* The explicit form (17.42) of Stirling's approximation: the proof of Lemma 17.5.1 uses the
  monotonicity of Mathlib's Stirling sequence instead.
* Han's inequalities for differential entropies: they are proved for discrete random variables,
  and for Gaussian vectors in the form of the determinant inequalities of Section 17.9.
* Section 17.7 beyond the Cramér–Rao inequality: Fisher information of a location family, de
  Bruijn's identity (Theorem 17.7.2), the convolution inequality for Fisher information, and the
  entropy power inequality (Theorem 17.7.3).
* Section 17.8: the entropy power inequality and the Brunn–Minkowski inequality
  (Theorems 17.8.1–17.8.3), the strengthened Young's inequality (Lemma 17.8.1) and Rényi
  entropy powers.
* The proof of Minkowski's inequality from the entropy power inequality: it is proved by
  simultaneous diagonalization instead.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 17.
-/

/-- **Theorem 17.1.1 (Jensen's inequality).** -/
alias theorem_17_1_1 := jensen

/-- **Theorem 17.1.2 (Log sum inequality).** -/
alias theorem_17_1_2 := log_sum_inequality

/-- **Theorem 17.1.3 (Entropy bound).** -/
alias theorem_17_1_3 := entropy_le_log_card

/-- **Theorem 17.1.4 (Conditioning reduces entropy).** -/
alias theorem_17_1_4 := condEntropy_le_entropy

/-- **Theorem 17.1.5 (Chain rule).** -/
alias theorem_17_1_5 := chain_rule_entropy

/-- **Theorem 17.1.6** (concavity of entropy). -/
alias theorem_17_1_6 := entropy_concaveOn

/-- **Theorem 17.1.7 (Information inequality).** -/
alias theorem_17_1_7 := relEntropyReal_nonneg

/-- **Theorem 17.1.8 (Convexity of relative entropy).** -/
alias theorem_17_1_8 := relEntropyReal_convex_pair

/-- **Theorem 17.1.9.** -/
alias theorem_17_1_9 := theorem_2_4_1

/-- **Theorem 17.1.11.** -/
alias theorem_17_1_11 := expect_relEntropy_typeOf_succ_le

/-- **Theorem 17.2.1 (Conditioning reduces entropy).** -/
alias theorem_17_2_1 := condDiffEntropy_le

/-- **Theorem 17.2.2 (Chain rule).** -/
alias theorem_17_2_2 := diffEntropy_eq_sum_condDiffEntropyLast

/-- **Theorem 17.2.3.** -/
alias theorem_17_2_3 := diffEntropy_le_of_covariance

/-- **Theorem 17.3.1 (Fano's inequality).** -/
alias theorem_17_3_1 := fano_estimator

/-- **Lemma 17.3.1.** -/
alias lemma_17_3_1 := exp_neg_entropy_le_sum_sq

/-- **Theorem 17.3.2.** -/
alias theorem_17_3_2 := exp_two_mul_diffEntropy_div_le

/-- **Theorem 17.3.3 (L₁ bound on entropy).** -/
alias theorem_17_3_3 := abs_entropy_sub_le

/-- **Lemma 17.3.2 (Pinsker).** -/
alias lemma_17_3_2 := pinsker

/-- **Lemma 17.3.3.** -/
alias lemma_17_3_3 := abs_relEntropyReal_sub_chiSq_le

/-- **Lemma 17.3.3** (as a limit). -/
alias lemma_17_3_3_tendsto := tendsto_relEntropyReal_div_sq

/-- **Theorem 17.4.1.** -/
alias theorem_17_4_1 := card_types_le

/-- **Theorem 17.4.2.** -/
alias theorem_17_4_2 := iidPMF_eq_exp_type

/-- **Theorem 17.4.3** (upper bound). -/
alias theorem_17_4_3 := card_typeClass_le

/-- **Theorem 17.4.3** (lower bound). -/
alias theorem_17_4_3_lower := exp_div_le_card_typeClass

/-- **Theorem 17.4.4** (upper bound). -/
alias theorem_17_4_4 := prob_typeClass_le

/-- **Theorem 17.4.4** (lower bound). -/
alias theorem_17_4_4_lower := exp_div_le_prob_typeClass

/-- **Lemma 17.5.1** (upper bound). -/
alias lemma_17_5_1 := choose_mul_exp_binEntropy_le

/-- **Lemma 17.5.1** (lower bound). -/
alias lemma_17_5_1_lower := le_choose_mul_exp_binEntropy

/-- **Theorem 17.6.1 (Han).** -/
alias theorem_17_6_1 := subsetAvg_succ_le

/-- **Theorem 17.6.2.** -/
alias theorem_17_6_2 := subsetExpAvg_succ_le

/-- **Theorem 17.6.3 (Han).** -/
alias theorem_17_6_3 := subsetCondAvg_le_succ

/-- **Theorem 17.6.4.** -/
alias theorem_17_6_4 := subsetMutAvg_succ_le

/-- **Theorem 17.7.1 (Cramér–Rao inequality).** -/
alias theorem_17_7_1 := ParamFamily.cramerRao

/-- **Theorem 17.9.1** (log-concavity of the determinant). -/
alias theorem_17_9_1 := det_rpow_mul_det_rpow_le

/-- **Theorem 17.9.2 (Hadamard).** -/
alias theorem_17_9_2 := det_le_prod_diag

/-- **Theorem 17.9.3 (Szász).** -/
alias theorem_17_9_3 := minorProd_rpow_succ_le

/-- **Theorem 17.9.4.** -/
alias theorem_17_9_4 := minorRootAvg_succ_le

/-- **Theorem 17.9.5.** -/
alias theorem_17_9_5 := condMinorMean_le_succ

/-- **Corollary (17.126).** -/
alias corollary_17_9_5 := prod_condVar_le_det_le_prod_diag

/-- **Theorem 17.9.6** (the ratios). -/
alias theorem_17_9_6 := det_ratio_succ_le

/-- **Theorem 17.9.6, (17.127).** -/
alias theorem_17_9_6_rpow := det_rpow_succ_le

/-- **Theorem 17.9.6, (17.128).** -/
alias theorem_17_9_6_tendsto := tendsto_det_rpow_and_ratio

/-- **Theorem 17.9.7 (Minkowski).** -/
alias theorem_17_9_7 := det_rpow_add_det_rpow_le

/-- **Lemma 17.10.1.** -/
alias lemma_17_10_1 := isLeast_det_div_det

/-- **Theorem 17.10.1 (Bergstrøm).** -/
alias theorem_17_10_1 := concaveOn_log_det_div_det

/-- **Theorem 17.10.2 (Bergstrøm).** -/
alias theorem_17_10_2 := concaveOn_det_div_det

end InfoTheory.CoverThomas
