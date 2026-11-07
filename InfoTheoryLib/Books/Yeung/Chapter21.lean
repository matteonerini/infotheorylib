/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 21: Multi-Source Network Coding

This file maps Chapter 21 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## Partly in the library

* Definition 21.1: `NetCode` (`Network.NoiselessCode`). On acyclic networks, with other notation.
* Definition 21.2: `IsAchievable` (`Network.NoiselessCode`). Other notation.
* Definition 21.3: `capacityRegion` (`Network.NoiselessCode`). Other notation.

## To formalize

* Definition 21.4
* Theorem 21.5
* Lemma 21.6
* Lemma 21.7
* Lemma 21.8
* Lemma 21.9
* Lemma 21.10
* Lemma 21.11

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 21
-/
