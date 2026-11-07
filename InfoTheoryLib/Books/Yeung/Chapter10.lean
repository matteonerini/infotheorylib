/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 10: Differential Entropy

This file maps Chapter 10 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 10.1: Mathlib's `Matrix.IsSymm`.
* Definition 10.2: Mathlib's `Matrix.PosDef`, Mathlib's `Matrix.PosSemidef`.
* Proposition 10.4: Mathlib's `Matrix.PosSemidef.eigenvalues_nonneg`.
* Definition 10.10: `diffEntropy` (`DifferentialEntropy.Basic`).
* Example 10.12 (Uniform Distribution): `uniformPDF`, `diffEntropy_uniformPDF`
  (`DifferentialEntropy.Basic`).
* Example 10.13 (Gaussian Distribution): `diffEntropy_gaussianPDFReal`
  (`DifferentialEntropy.Gaussian`).
* Theorem 10.14 (Translation): `diffEntropy_comp_sub` (`DifferentialEntropy.Basic`).
* Theorem 10.15 (Scaling): `diffEntropy_scale` (`DifferentialEntropy.Basic`).
* Definition 10.17: `diffEntropy` (`DifferentialEntropy.Basic`).
* Theorem 10.18 (Translation): `diffEntropy_comp_sub` (`DifferentialEntropy.Basic`).
* Theorem 10.19 (Scaling): `diffEntropy_linearEquiv` (`DifferentialEntropy.Basic`).
* Theorem 10.20 (Multivariate Gaussian Distribution): `diffEntropy_mvGaussianPDF`
  (`DifferentialEntropy.MultivariateGaussian`).
* Proposition 10.32 (Chain Rule for Differential Entropy): `diffEntropy_eq_sum_condDiffEntropyLast`
  (`DifferentialEntropy.ChainRule`).
* Corollary 10.35 (Conditioning Does Not Increase Differential Entropy): `condDiffEntropy_le`,
  `condDiffEntropy_eq_iff` (`DifferentialEntropy.Joint`).
* Corollary 10.36 (Independence Bound for Differential Entropy): `diffEntropy_le_sum_coordMarginal`,
  `diffEntropy_eq_sum_coordMarginal_iff` (`DifferentialEntropy.ChainRule`).
* Theorem 10.37 (AEP I for Continuous Random Variables): `tendstoInMeasure_sampleDiffEntropy`
  (`DifferentialEntropy.AEP`).
* Definition 10.38: `diffTypicalSet` (`DifferentialEntropy.AEP`).
* Definition 10.39: Mathlib's `volume`.
* Theorem 10.40 (AEP II for Continuous Random Variables): `prodPDF_bounds`,
  `eventually_prob_diffTypicalSet_gt`, `volume_diffTypicalSet_le`,
  `eventually_volume_diffTypicalSet_ge` (`DifferentialEntropy.AEP`).
* Definition 10.41: `relEntropyPDF` (`DifferentialEntropy.RelativeEntropy`).
* Theorem 10.42 (Divergence Inequality): `relEntropyPDF_nonneg`, `relEntropyPDF_eq_zero_iff`
  (`DifferentialEntropy.RelativeEntropy`).
* Theorem 10.43: `diffEntropy_le_of_eq_exp`, `diffEntropy_eq_of_eq_exp_iff` (`MaxEntropy.Basic`).
* Corollary 10.44: `diffEntropy_le_of_eq_exp` (`MaxEntropy.Basic`).
* Theorem 10.48: `diffEntropy_le_of_covariance`, `diffEntropy_eq_of_covariance_iff`
  (`DifferentialEntropy.MultivariateGaussian`).

## Partly in the library

* Definition 10.28: `mutualInfoPDF` (`DifferentialEntropy.Joint`). Both variables with a joint
  density.
* Definition 10.29: `condDiffEntropy` (`DifferentialEntropy.Joint`). Both variables with a joint
  density.
* Proposition 10.31: `mutualInfoPDF_eq_sub_condDiffEntropy` (`DifferentialEntropy.Joint`). Both
  variables with a joint density.
* Theorem 10.33: `relEntropyPDF_nonneg` (`DifferentialEntropy.RelativeEntropy`). Both variables with
  a joint density.
* Corollary 10.34: `mutualInfoPDF_eq_relEntropyPDF`, `relEntropyPDF_nonneg`
  (`DifferentialEntropy.Joint`, `DifferentialEntropy.RelativeEntropy`). No conditioning variable.
* Theorem 10.46: `diffEntropy_le_of_moments` (`MaxEntropy.Distributions`). The inequality; the
  equality case is new.

## To formalize

* Proposition 10.3: covariance matrices of random vectors
* Proposition 10.5
* Proposition 10.6
* Corollary 10.7
* Proposition 10.8
* Proposition 10.9
* Example 10.11
* Example 10.16
* Definition 10.21: mixed pairs: X arbitrary, Y discrete
* Definition 10.22: mixed pairs
* Definition 10.23
* Definition 10.24
* Definition 10.25
* Proposition 10.26
* Proposition 10.27
* Definition 10.30
* Theorem 10.45
* Theorem 10.47

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 10
-/
