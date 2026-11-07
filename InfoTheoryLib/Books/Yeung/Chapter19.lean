/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 19: Single-Source Linear Network Coding: Acyclic Networks

This file maps Chapter 19 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 19.6 (Local Description of a Linear Network Code): `LinCoeff`, `LinCoeff.code`
  (`Network.LinearNetworkCode`).
* Definition 19.7 (Global Description of a Linear Network Code): `globalVec`, `globalVec_eq`
  (`Network.LinearNetworkCode`).
* Lemma 19.17: `exists_aeval_ne_zero_of_degreeOf` (`ForMathlib.PolyFiniteField`).

## Partly in the library

* Proposition 19.1: `Multigraph` (`Network.LinearNetworkCode`). Nodes are ordered by definition, so
  no ordering is derived.
* Example 19.5: `butterflyCode` (`Books.ElGamalKim.Lecture16Examples`). As a code, without its
  kernels.
* Example 19.9: `kmGraph`, `kmCoeff`, `km_transfer` (`Books.ElGamalKim.Lecture16Examples`). The
  example of the notes, on another network.
* Theorem 19.10 (Max-Flow Bound for Linear Network Coding): `cuts_of_detGeneric_ne_zero`
  (`Network.LinearNetworkCode`). For a full-rank matrix at a destination.
* Corollary 19.18: `card_aeval_eq_zero_le` (`ForMathlib.PolyFiniteField`). With the total degree;
  the book's bound uses the degree in each variable.
* Theorem 19.20: `exists_coeff_of_card_gt`, `detGeneric_ne_zero_of_cuts`
  (`Network.LinearNetworkCode`). Invertible transfer matrices at the destinations; the book's
  definition is by dimensions.
* Corollary 19.24: `card_not_invertible_le` (`Network.LinearNetworkCode`). A bound on failure; the
  book's statement may differ.
* Example 19.26 (Multi-Source Multicast): `capacityRegion_multisource` (`Network.NetworkCoding`).
  The capacity region, in the form of the notes.

## To formalize

* Example 19.2
* Definition 19.3 (Local Description of a Network Code)
* Definition 19.4 (Global Description of a Network Code)
* Example 19.8
* Corollary 19.11
* Definition 19.12
* Example 19.13
* Example 19.14
* Example 19.15
* Example 19.16
* Example 19.19
* Corollary 19.21
* Corollary 19.22
* Example 19.23
* Algorithm 19.25 (Jaggi-Sanders Algorithm)
* Definition 19.27 (Generic Network Code I)
* Definition 19.28 (Generic Network Code II)
* Proposition 19.29
* Corollary 19.30
* Example 19.31
* Theorem 19.32
* Corollary 19.33
* Algorithm 19.34 (Construction of a Generic Network Code)
* Theorem 19.35
* Definition 19.36
* Definition 19.37
* Example 19.38
* Example 19.39
* Algorithm 19.40 (Construction of a Static Generic Network Code)
* Theorem 19.41
* Example 19.42

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 19
-/
