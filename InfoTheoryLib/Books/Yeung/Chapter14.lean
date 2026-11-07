/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 14: Shannon-Type Inequalities

This file maps Chapter 14 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## Other material

* Appendix 14.A, the polymatroidal axioms: `IsSubmodular` (`Inequalities.Han`), with `subsetEntropy`
  (`Inequalities.SubsetEntropy`) for the entropy function.

## To formalize

* Example 14.1
* Example 14.2
* Theorem 14.3
* Theorem 14.4
* Theorem 14.5
* Example 14.6
* Example 14.7
* Example 14.8 (Secret Sharing)
* Example 14.9

## Planned omissions

* The software ITIP of Section 14.4 as such. The plan is to let Lean's `linarith` combine the
  elemental inequalities.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 14
-/
