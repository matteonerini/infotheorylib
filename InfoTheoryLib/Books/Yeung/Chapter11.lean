/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 11: Continuous-Valued Channels

This file maps Chapter 11 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 11.19 (Gaussian Channel): `noiseJointPDF` (`GaussianChannel.Basic`).
* Definition 11.20 (Memoryless Gaussian Channel): `GaussianCode` (`GaussianChannel.Code`).
* Theorem 11.21 (Capacity of a Memoryless Gaussian Channel): `gaussianOpCapacity_eq`
  (`GaussianChannel.Achievability`).
* Proposition 11.23: `waterFill`, `sum_log_le_waterFill`, `exists_waterLevel`
  (`GaussianChannel.WaterFilling`).
* Definition 11.24: Mathlib's `VectorFourier.fourierIntegral`.

## Partly in the library

* Definition 11.6: `GaussianCode.SatisfiesPower` (`GaussianChannel.Code`). The power constraint
  only.
* Definition 11.7: `gaussianInfoCapacity` (`GaussianChannel.Capacity`). The Gaussian channel only.
* Definition 11.9: `GaussianCode` (`GaussianChannel.Code`). The Gaussian channel only.
* Definition 11.10: `GaussianCode.condErrProb` (`GaussianChannel.Code`). The Gaussian channel only.
* Definition 11.11: `GaussianCode.maxErrProb` (`GaussianChannel.Code`). The Gaussian channel only.
* Definition 11.12: `GaussianCode.avgErrProb` (`GaussianChannel.Code`). The Gaussian channel only.
* Definition 11.13: `IsAchievableGaussianRate` (`GaussianChannel.Code`). The Gaussian channel only.
* Theorem 11.14 (Channel Coding Theorem): `gaussianOpCapacity_eq` (`GaussianChannel.Achievability`).
  The Gaussian channel only.
* Lemma 11.22: `mutualInfoPDF_gaussianChannel_le` (`GaussianChannel.Capacity`). Used inside this
  bound.
* Theorem 11.29 (Sampling Theorem): `signalOfSpectrum_eq_of_samples`
  (`GaussianChannel.Bandlimited`). Uniqueness only, not the interpolation formula.

## Other material

* Section 11.5, parallel Gaussian channels: `parallelInfoCapacity_eq` (`GaussianChannel.Parallel`),
  with Proposition 11.23.
* Section 11.6, correlated Gaussian channels: `coloredInfoCapacity_eq`
  (`GaussianChannel.ColoredNoise`).
* Section 11.7, the bandlimited white Gaussian channel, as a formula: `bandlimitedCapacity_eq`,
  `tendsto_bandlimitedCapacity` (`GaussianChannel.Bandlimited`).

## To formalize

* Definition 11.1
* Definition 11.2
* Definition 11.3
* Definition 11.4
* Definition 11.5
* Theorem 11.8
* Lemma 11.15
* Definition 11.16
* Lemma 11.17
* Lemma 11.18
* Definition 11.25
* Proposition 11.26
* Proposition 11.30
* Theorem 11.32
* Lemma 11.33
* Lemma 11.34

## Planned omissions

* Definition 11.27: continuous-time random processes.
* Definition 11.28: continuous-time random processes.
* Proposition 11.31: filtered white noise, a continuous-time random process.
* The bandlimited colored Gaussian channel of Section 11.8, which rests on continuous-time random
  processes.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 11
-/
