/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 5: Weak Typicality

This file maps Chapter 5 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Theorem 5.1 (Weak AEP I): `aep` (`AEP.Basic`).
* Definition 5.2: `typicalSet`, `mem_typicalSet` (`AEP.TypicalSet`).
* Theorem 5.3 (Weak AEP II): `sampleEntropy_mem_Icc_of_mem_typicalSet`,
  `eventually_prob_typicalSet_gt`, `card_typicalSet_le`, `eventually_card_typicalSet_gt`
  (`AEP.TypicalSet`).

## Partly in the library

* Theorem 5.4: `entropy_prefixRV_le_sum`, `entropy_prefixRV_eq_sum_iff` (`Entropy.Bounds`). The
  bound and independence; not the uniform case.

## Other material

* Section 5.2, the source coding theorem: `exists_code_expect_length_le`
  (`SourceCoding.TypicalSetCode`).
* Section 5.3, efficient source coding: Theorem 5.4 is listed above; its discussion of almost i.i.d.
  bits is informal.

## Planned omissions

* Example 5.5: ergodicity.
* Example 5.6: ergodicity.
* The Shannon–McMillan–Breiman theorem of Section 5.4, which needs the ergodic theorem, as in
  `Books.CoverThomas.Chapter16`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 5
-/
