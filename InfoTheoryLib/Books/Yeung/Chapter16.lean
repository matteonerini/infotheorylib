/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 16: Entropy and Groups

This file maps Chapter 16 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 16.1: Mathlib's `Group`.
* Proposition 16.2: a one-line fact about Mathlib's groups.
* Proposition 16.3: Mathlib's `inv_unique`.
* Definition 16.4: Mathlib's `Nat.card`.
* Example 16.5 (Modulo 2 Addition): Mathlib's `ZMod 2`.
* Example 16.6 (Symmetric Group): Mathlib's `Equiv.Perm`.
* Definition 16.7: Mathlib's `Subgroup`.
* Definition 16.8: Mathlib's `leftCoset_eq_iff`.
* Proposition 16.9: Mathlib's `leftCoset_eq_iff`.
* Proposition 16.10: Mathlib's `Subgroup.leftCosetEquivSubgroup`.
* Theorem 16.11 (Lagrange’s Theorem): Mathlib's `Subgroup.card_subgroup_dvd_card`.
* Corollary 16.12: Mathlib's `Subgroup.index_eq_card`.
* Proposition 16.13: Mathlib's `Subgroup.coe_inf`.
* Corollary 16.14: Mathlib's `Subgroup.coe_iInf`.

## To formalize

* Lemma 16.15
* Theorem 16.16
* Definition 16.17
* Example 16.18
* Example 16.19
* Example 16.20
* Definition 16.21
* Theorem 16.22
* Lemma 16.23
* Corollary 16.24
* Definition 16.25
* Proposition 16.26
* Theorem 16.27
* Corollary 16.28

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 16
-/
