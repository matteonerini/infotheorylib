/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 9: The Blahut–Arimoto Algorithms

This file maps Chapter 9 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Lemma 9.1: `sum_mul_log_div_le_mutualInfoOf`, `sum_mul_log_posterior_eq`
  (`RateDistortion.BlahutArimoto`).
* Lemma 9.3: `mutualInfoOf_le_relEntropy_jointOf_prodDist`, `relEntropy_jointOf_prodDist_eq`
  (`RateDistortion.BlahutArimoto`).

## Other material

* Section 9.2, the algorithm for the rate-distortion function: `baChannel`, `baIter`,
  `baObjective_baChannel_le`, `baObjective_outDist_le` (`RateDistortion.BlahutArimoto`).

## To formalize

* Theorem 9.2
* Lemma 9.4
* Theorem 9.5

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 9
-/
