/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 8: Rate-Distortion Theory

This file maps Chapter 8 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 8.1: a function `d : α → β → ℝ`.
* Definition 8.2: `seqDistortion` (`RateDistortion.Basic`).
* Example 8.4: `hammingDistortion` (`RateDistortion.Basic`).
* Definition 8.8: `RDCode`, `RDCode.distortion` (`RateDistortion.Basic`).
* Definition 8.16: `infoRD`, `exists_infoRD_eq` (`RateDistortion.Basic`).
* Theorem 8.18: `infoRD_antitoneOn`, `infoRD_convexOn` (`RateDistortion.Basic`).
* Example 8.20 (Binary Source): `infoRD_bernoulli` (`RateDistortion.Binary`).

## Partly in the library

* Definition 8.10: `IsAchievableRD` (`RateDistortion.Basic`). In expectation; the book's is in
  probability.
* Theorem 8.12: `isClosed_epigraph_infoRD` (`RateDistortion.Theorem`). For the information function.
* Definition 8.13: `rateDistortion` (`RateDistortion.Basic`). For achievability in expectation.
* Theorem 8.15: `infoRD_antitoneOn`, `infoRD_convexOn` (`RateDistortion.Basic`). For the information
  function.
* Theorem 8.17 (The Rate-Distortion Theorem): `rateDistortion_eq_infoRD` (`RateDistortion.Theorem`).
  In expectation; the book's is in probability.

## To formalize

* Example 8.3
* Definition 8.5
* Example 8.6
* Definition 8.7
* Definition 8.9
* Definition 8.11
* Definition 8.14
* Corollary 8.19

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 8
-/
