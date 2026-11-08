/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.Yeung.Chapter18
public import InfoTheoryLib.Network.LinearMulticast
public import InfoTheoryLib.Network.NetworkCoding

/-!
# Yeung, Chapter 19: Single-Source Linear Network Coding: Acyclic Networks

This file indexes the formalization of Chapter 19 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Acyclic networks.** By Proposition 19.1, an acyclic network can be ordered upstream to
  downstream, so a network is a `Multigraph V E` of `Network.LinearNetworkCode`: a multigraph on a
  linearly ordered set of nodes whose channels go up. Every channel has unit capacity, and parallel
  channels are allowed, as in Section 19.2.
* **Linear codes.** An `ω`-dimensional linear network code over a field `F` with source `s` is a
  `LinCoeff F E (srcDim s ω)`: its coefficients `y` are the local encoding kernels `k_{d,e}` of the
  imaginary channels `d ∈ In(s)` and the channels `e ∈ Out(s)`, and its coefficients `x` are the
  other local encoding kernels. The global encoding kernel `fₑ` is `globalVec G a e`, a vector
  indexed by the message symbols `SrcIdx s ω` instead of by `1, …, ω`. The decoding coefficients `z`
  of a `LinCoeff` play no role here.
* **Max-flows.** `maxflow(T)` and `maxflow(ξ)` are `Multigraph.maxflowNodes` and
  `Multigraph.maxflowEdges`: the capacities of the min-cuts in the graphs of Figure 18.1, written
  on the original graph. By the max-flow min-cut theorem these are the max-flows of the book.
* **Indexing.** In Example 19.2 the butterfly network is `butterflyNet'` of Chapter 18, with the
  nodes `s, 1, 2, 3, 4, t₁, t₂` numbered `0` to `6`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 19.1 Acyclic Networks
* Adjacent channels, directed paths and cycles: `PtpNetwork.Adj`, `PtpNetwork.IsAcyclic`
  (`Network.LinearMulticast`).
* Proposition 19.1: `proposition_19_1` (here), which is `PtpNetwork.exists_rank_of_isAcyclic`
  (`Network.LinearMulticast`): a ranking by the number of ancestors, instead of the length of a
  longest path. Conversely, `PtpNetwork.isAcyclic_of_rank`.
* Example 19.2: `example_19_2` (here).

### 19.2 Linear Network Codes
* Definitions 19.6 and 19.7 (Local and Global Description of a Linear Network Code): `LinCoeff`,
  `globalVec`, with (19.17) `globalVec_eq` (`Network.LinearNetworkCode`) and, off the source,
  `globalVec_eq_sum` (`Network.LinearMulticast`).

### 19.3 Desirable Properties of a Linear Network Code
* (19.31)–(19.33): `kernelSpan`, `nodeSpan` (`Network.LinearMulticast`).
* Theorem 19.10 (Max-Flow Bound for Linear Network Coding): `theorem_19_10` (here), which is
  `finrank_nodeSpan_le` (`Network.LinearMulticast`), with (19.35) in
  `nodeSpan_le_span_crossEdges`.
* Corollary 19.11: `corollary_19_11` (here), which is `finrank_kernelSpan_le`
  (`Network.LinearMulticast`).
* Definition 19.12: `IsLinearMulticast`, `IsLinearBroadcast`, `IsLinearDispersion`, and the
  implications after it, `IsLinearDispersion.isLinearBroadcast`,
  `IsLinearBroadcast.isLinearMulticast` (`Network.LinearMulticast`).
* (19.42)–(19.44), decoding at a node: `inKernels`, `injective_received_iff`
  (`Network.LinearMulticast`).
* (19.49)–(19.66), the transformation of a linear network code: `LinCoeff.transform`,
  `globalVec_transform`, and the exercise that it preserves the three properties,
  `IsLinearMulticast.transform`, `IsLinearBroadcast.transform`, `IsLinearDispersion.transform`
  (`Network.LinearMulticast`).

### 19.4 Existence and Construction
* Lemma 19.17: `lemma_19_17` (here), which is `exists_aeval_ne_zero_of_degreeOf`
  (`ForMathlib.PolyFiniteField`), for a polynomial over any subfield of `F`.
* Corollary 19.18: `card_aeval_eq_zero_le` (`ForMathlib.PolyFiniteField`), the fraction of the
  roots bounded by the total degree, `deg g / |F|`, instead of the book's `1 - (1 - m/|F|)^n`.
* Theorem 19.20: `theorem_19_20` (here), which is `exists_isLinearMulticast`
  (`Network.LinearMulticast`), over every finite field with more than `|V| ω` elements. The
  polynomials are those of `detGeneric`, which routing along edge-disjoint paths makes nonzero
  (`detGeneric_ne_zero_of_cuts`), and `exists_coeff_of_card_gt` chooses the kernels
  (`Network.LinearNetworkCode`).
* Example 19.26 (Multi-Source Multicast): `capacityRegion_multisource`
  (`Network.NetworkCoding`), the capacity region in the form of Lecture 16 of [elgamal2010].

## Not formalized

* Definitions 19.3 and 19.4, network codes that need not be linear, and the remark that the local
  encoding mappings are linear exactly when the global ones are; the codes of Chapter 18,
  `PtpNetwork.TransCode`, contain them.
* Examples 19.5, 19.8, 19.9, 19.13, 19.14, 19.15, 19.16, 19.19 and 19.23, the explicit codes on
  the butterfly network and on the networks of Figures 19.4 and 19.5.
* Corollaries 19.21 and 19.22, the existence of a linear broadcast and of a linear dispersion,
  which extend the network.
* Corollary 19.24, random network coding. `card_not_invertible_le` (`Network.LinearNetworkCode`)
  bounds the fraction of the coefficients that fail by the degree of a polynomial over `F`.
* Algorithm 19.25 (Jaggi–Sanders), the delivery of the global encoding kernels (19.68)–(19.69).
* Section 19.5, generic network codes: Definitions 19.27 and 19.28, Proposition 19.29,
  Corollary 19.30, Example 19.31, Theorem 19.32, Corollary 19.33, Algorithm 19.34 and
  Theorem 19.35.
* Section 19.6, static network codes: Definitions 19.36 and 19.37, Examples 19.38 and 19.39,
  Algorithm 19.40, Theorem 19.41 and Example 19.42.
* Section 19.7, the case study of random network coding.
* Figures 19.1 to 19.10.

## References

Numbers without a source refer to [yeung2008].

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 19
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-! ### 19.1 Acyclic Networks -/

/-- **Proposition 19.1.** The nodes of a finite acyclic network can be ordered so that every channel
goes from an earlier to a later node. -/
alias proposition_19_1 := PtpNetwork.exists_rank_of_isAcyclic

/-- The positions of the nodes `s, 1, 2, 3, 4, t₁, t₂` of the butterfly network in the sequence
`s, 2, 1, 3, 4, t₂, t₁` of (19.4). -/
def example192Pos : Fin 7 → ℕ := ![0, 2, 1, 3, 4, 6, 5]

/-- **Example 19.2.** In the sequence `s, 2, 1, 3, 4, t₂, t₁` of the nodes of the butterfly network,
if there is a directed path from node `i` to node `j`, then `i` appears before `j`. -/
theorem example_19_2 {i j : Fin 7} (h : Relation.TransGen butterflyNet'.Adj i j) :
    example192Pos i < example192Pos j :=
  butterflyNet'.lt_of_transGen (fun e => by fin_cases e <;> decide) h

/-! ### 19.3 Desirable Properties of a Linear Network Code -/

/-- **Theorem 19.10 (Max-Flow Bound for Linear Network Coding).** -/
alias theorem_19_10 := finrank_nodeSpan_le

/-- **Corollary 19.11.** -/
alias corollary_19_11 := finrank_kernelSpan_le

/-! ### 19.4 Existence and Construction -/

/-- **Lemma 19.17.** -/
alias lemma_19_17 := exists_aeval_ne_zero_of_degreeOf

/-- **Theorem 19.20.** -/
alias theorem_19_20 := exists_isLinearMulticast

end InfoTheory.Yeung
