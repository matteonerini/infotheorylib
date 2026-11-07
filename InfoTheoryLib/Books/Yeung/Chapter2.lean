/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 2: Information Measures

This file maps Chapter 2 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 2.1: `IndepRV` (`Probability.Independence`).
* Definition 2.2 (Mutual Independence): `IndepFamily` (`Probability.RandomVector`).
* Definition 2.4 (Conditional Independence): `CondIndep` (`Probability.Independence`).
* Definition 2.13: `entropy`, `entropyRV` (`Entropy.Basic`).
* Definition 2.14: `jointEntropy_def` (`Entropy.Basic`).
* Definition 2.15: `condEntropy`, `condEntropy_eq_sum_joint` (`Entropy.Conditional`).
* Proposition 2.16: `chain_rule` (`Entropy.Conditional`).
* Definition 2.17: `mutualInfo`, `mutualInfo_eq_sum` (`MutualInformation.Basic`).
* Proposition 2.18: `mutualInfo_self` (`MutualInformation.Basic`).
* Proposition 2.19: `mutualInfo_eq_entropy_sub_condEntropy`,
  `mutualInfo_eq_entropy_sub_condEntropy'`, `mutualInfo_eq_add_sub` (`MutualInformation.Basic`).
* Definition 2.20: `condMutualInfo` (`MutualInformation.Conditional`).
* Definition 2.23: `l1Dist` (`RelativeEntropy.Pinsker`).
* Proposition 2.24 (Chain Rule for Entropy): `chain_rule_entropy` (`Entropy.ChainRule`).
* Proposition 2.25 (Chain Rule for Conditional Entropy): `chain_rule_cond`,
  `chain_rule_entropy_cond` (`Entropy.Conditional`, `Entropy.ChainRule`).
* Proposition 2.26 (Chain Rule for Mutual Information): `chain_rule_mutualInfo`
  (`MutualInformation.ChainRule`).
* Definition 2.28: `relEntropy`, `relEntropyReal` (`RelativeEntropy.Basic`).
* Lemma 2.29 (Fundamental Inequality): Mathlib's `Real.log_le_sub_one_of_pos`, Mathlib's
  `Real.log_lt_sub_one_of_pos`.
* Theorem 2.31 (Divergence Inequality): `relEntropy_nonneg`, `relEntropy_eq_zero_iff`,
  `relEntropyReal_nonneg`, `relEntropyReal_eq_zero_iff` (`RelativeEntropy.InformationInequality`).
* Theorem 2.32 (Log-Sum Inequality): `log_sum_inequality`, `log_sum_inequality_eq_iff`
  (`Analysis.LogSum`).
* Theorem 2.33 (Pinsker’s Inequality): `pinsker` (`RelativeEntropy.Pinsker`).
* Theorem 2.34: `condMutualInfo_nonneg`, `condMutualInfo_eq_zero_iff`
  (`MutualInformation.Conditional`).
* Proposition 2.35: `entropy_eq_zero_iff` (`Entropy.Basic`).
* Proposition 2.36: `condEntropy_eq_zero_iff` (`Entropy.Fano`).
* Proposition 2.37: `mutualInfo_eq_zero_iff` (`MutualInformation.Basic`).
* Theorem 2.38 (Conditioning Does Not Increase Entropy): `condEntropy_le_entropy`,
  `condEntropy_eq_entropy_iff` (`Entropy.Bounds`).
* Theorem 2.39 (Independence Bound for Entropy): `entropy_prefixRV_le_sum`,
  `entropy_prefixRV_eq_sum_iff` (`Entropy.Bounds`).
* Lemma 2.41: `data_processing`, `data_processing'` (`MarkovChain.DataProcessing`).
* Theorem 2.43: `entropy_le_log_card`, `entropy_eq_log_card_iff` (`Entropy.Bounds`).
* Theorem 2.47 (Fano’s Inequality): `fano`, `fano_of_eq`, `fano_estimator` (`Entropy.Fano`).
* Theorem 2.50: `entropy_le_of_eq_exp`, `entropy_eq_of_eq_exp_iff` (`MaxEntropy.Basic`).
* Corollary 2.51: `entropy_le_of_eq_exp` (`MaxEntropy.Basic`).
* Example 2.52: `entropy_le_log_card` (`Entropy.Bounds`).
* Definition 2.54: `StochasticProcess.HasEntropyRate` (`StochasticProcess.Basic`).
* Example 2.55: `iidProcess_hasEntropyRate` (`StochasticProcess.Independent`).
* Definition 2.57: `StochasticProcess.IsStationary` (`StochasticProcess.Basic`).
* Lemma 2.58: `StochasticProcess.IsStationary.hasCondEntropyRate`,
  `StochasticProcess.IsStationary.condEntropyLast_antitone` (`StochasticProcess.Basic`).
* Lemma 2.59 (Cesáro Mean): `cesaro_mean` (`StochasticProcess.Basic`).
* Theorem 2.60: `StochasticProcess.IsStationary.hasEntropyRate` (`StochasticProcess.Basic`).

## Partly in the library

* Definition 2.6 (Markov Chain): `MarkovChain`, `markovChain_iff_condIndep` (`MarkovChain.Basic`).
  Three variables.
* Proposition 2.7: `MarkovChain.symm` (`MarkovChain.Basic`). Three variables.
* Proposition 2.22: `condMutualInfo_eq'`, `condMutualInfo_eq` (`MutualInformation.Conditional`).
  (2.65), and (2.67) in joint entropies; (2.66) by symmetry.
* Proposition 2.27 (Chain Rule for Conditional Mutual Information): `chain_rule_condMutualInfo`
  (`MutualInformation.Conditional`). Two variables.
* Corollary 2.30: Mathlib's `Real.one_sub_inv_le_log_of_pos`.
* Theorem 2.40: `chain_rule_mutualInfo₂` (`MutualInformation.Conditional`). The inequality follows;
  the equality case is new.
* Corollary 2.48: `fano_weak` (`Entropy.Fano`). With ≤ in place of <.

## Other material

* Section 2.3, continuity for a fixed finite alphabet: `continuous_entropy`
  (`Probability.SupportMixture`).

## To formalize

* Definition 2.3 (Pairwise Independence): pairwise independence
* Proposition 2.5: factorization criterion
* Proposition 2.8
* Proposition 2.9
* Proposition 2.10 (Markov subchains)
* Example 2.11
* Proposition 2.12
* Proposition 2.21: conditional form of 2.18
* Theorem 2.42 (Data Processing Theorem)
* Corollary 2.44

## Planned omissions

* Example 2.45: countable.
* Example 2.46: countable.
* Example 2.49: countable.
* Example 2.53: countable.
* Example 2.56: unbounded alphabets.
* Countably infinite alphabets, including Appendix 2.A and the discontinuity examples of Section
  2.3: alphabets in this library are finite.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 2
-/
