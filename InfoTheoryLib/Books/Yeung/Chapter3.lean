/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 3: The I-Measure

This file maps Chapter 3 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Lemma 3.8: `condMutualInfo_eq` (`MutualInformation.Conditional`).

## Partly in the library

* Example 3.12 (Concavity of Entropy): `entropy_concaveOn` (`Entropy.Concavity`). By another proof,
  not with an information diagram.
* Example 3.13 (Convexity of Mutual Information): `mutualInfoOf_convex_channel`
  (`MutualInformation.Convexity`). By another proof, not with an information diagram.
* Example 3.14 (Concavity of Mutual Information): `mutualInfoOf_concave_input`
  (`MutualInformation.Convexity`). By another proof, not with an information diagram.

## To formalize

* Definition 3.1
* Definition 3.2
* Example 3.3
* Definition 3.4
* Example 3.5
* Theorem 3.6
* Lemma 3.7
* Theorem 3.9
* Example 3.10
* Theorem 3.11
* Example 3.15 (Imperfect Secrecy Theorem)
* Example 3.16
* Example 3.17 (Data Processing Theorem)
* Example 3.18
* Theorem 3.19

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 3
-/
