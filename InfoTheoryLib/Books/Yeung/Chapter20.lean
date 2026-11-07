/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 20: Single-Source Linear Network Coding: Cyclic Networks

This file maps Chapter 20 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## Partly in the library

* Lemma 20.12: `exists_aeval_ne_zero_of_degreeOf` (`ForMathlib.PolyFiniteField`). Check that the
  subset form is covered.

## To formalize

* Example 20.1
* Example 20.2
* Example 20.3
* Example 20.4
* Example 20.5
* Definition 20.6 (Convolutional Network Code)
* Example 20.7
* Example 20.8
* Theorem 20.9
* Definition 20.10 (Convolutional Multicast)
* Example 20.11
* Theorem 20.13
* Example 20.14

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 20
-/
