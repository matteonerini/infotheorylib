/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 17: Introduction

This file maps Chapter 17 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Example 17.1 (Butterfly Network I): `butterflyNet`, `butterflyCode`, `butterflyCode_correct`
  (`Books.ElGamalKim.Lecture16Examples`).

## Partly in the library

* Example 17.2 (Butterfly Network II): `unicastCode`, `unicastCode_correct`
  (`Books.ElGamalKim.Lecture16Examples`). The same network with two sources, as multiple unicast.

## To formalize

* Proposition 17.3
* Example 17.4 (A Wireless/Satellite System)

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 17
-/
