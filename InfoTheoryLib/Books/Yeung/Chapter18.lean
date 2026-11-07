/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 18: The Max-Flow Bound

This file maps Chapter 18 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Theorem 18.1 (Max-Flow Min-Cut Theorem): `IsFlow`, `minCut`, `maxFlow_minCut`
  (`ForMathlib.MaxFlow`).

## Partly in the library

* Definition 18.2: `IsAchievable` (`Network.NoiselessCode`). Acyclic networks.
* Theorem 18.3 (Max-Flow Bound): `IsAchievable.le_minCut` (`Network.NoiselessCode`). Acyclic
  networks.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 18
-/
