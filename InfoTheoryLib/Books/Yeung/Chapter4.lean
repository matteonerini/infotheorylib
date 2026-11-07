/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 4: Zero-Error Data Compression

This file maps Chapter 4 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 4.1: `expectedLength` (`SourceCoding.Code`).
* Definition 4.2: `IsUniquelyDecodableCode` (`SourceCoding.Code`).
* Theorem 4.4 (Kraft Inequality): `kraft_of_isUniquelyDecodableCode` (`SourceCoding.Kraft`).
* Theorem 4.5 (Entropy Bound): `entropyBase_le_expectedLength` (`SourceCoding.OptimalLength`).
* Corollary 4.6: `entropy_le_log_card` (`Entropy.Bounds`).
* Definition 4.8: `IsPrefixCode` (`SourceCoding.Code`).
* Theorem 4.10: `kraft_of_isPrefixCode`, `exists_prefixCode_of_kraft` (`SourceCoding.Kraft`).

## Partly in the library

* Corollary 4.11: `IsDAdic`, `exists_lengths_eq_entropyBase_iff` (`SourceCoding.OptimalLength`). For
  lengths; a prefix code follows from 4.10.
* Lemma 4.14: `cost_comp_swap` (`SourceCoding.Huffman`). As the exchange of two lengths.
* Lemma 4.15: `kraft_update_of_unique_max` (`SourceCoding.Huffman`). For lengths, binary.
* Theorem 4.16: `huffmanCode_optimal`, `huffmanCost_le_expectedLength` (`SourceCoding.Huffman`).
  Binary.
* Theorem 4.17: `expectedLength_huffmanCode`, `minExpectedLength_bounds` (`SourceCoding.Huffman`,
  `SourceCoding.OptimalLength`). The bound for the optimal length; binary Huffman.

## To formalize

* Example 4.3
* Definition 4.7
* Example 4.9
* Example 4.12
* Example 4.13
* Lemma 4.18
* Lemma 4.19
* Theorem 4.20 (Local Redundancy Theorem)
* Corollary 4.21 (Entropy Bound)
* Example 4.22

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 4
-/
