/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture16Yeung

/-!
# El Gamal & Kim, Lecture 16: Noiseless Networks

This file indexes the formalization of Lecture 16 of [elgamal2010]. We prove the max-flow min-cut
theorem, as a statement on flows and as a coding theorem achieved by routing; the network coding
theorem by the method of Koetter and Médard, with Lemma 1; the capacity region of a multi-source
multicast network; the cutset outer bound; and all the examples of the lecture.

## Conventions

* **Networks.** A network has a linearly ordered set of nodes `V` and capacities `C j k`, positive
  only if `j < k`. A pair that is not an edge has capacity `0`. Page 16-23 assumes this order, and
  every finite acyclic graph has one. The examples have nodes `Fin N`, numbered from `0`.
* **Codes.** There is one kind of code, `NetCode`, the one of page 16-24. Relay and multicast
  networks are the case with one nonzero rate (`singleRate`) and one set of destinations
  (`multicastD`), as the notes say on page 16-23. A message that nobody decodes can have any rate.
* **Rates.** They are in bits. Messages have `2 ^ ⌈n R⌉` values and an edge carries `2 ^ ⌊n C⌋`
  indices. The decoder has no error symbol, since it would never help.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Flows and cuts (pages 16-5 and 16-7)
* `netOut`, `cutCap`, `IsFlow`, `minCut` (`ForMathlib.MaxFlow`).
* Weak duality: `IsFlow.le_cutCap`.
* Simple paths and augmentation: `SPath`, `exists_sPath`, `ResEdge`, `exists_push`,
  `IsFlow.eq_cut_or_augment`.
* **Max-flow min-cut for real capacities (the linear program of page 16-8)**: `maxFlow_minCut`.
* For integer capacities and several sources: `exists_intFlow`, `exists_supplyFlow`.
* Decomposition of an integer flow into units: `exists_unit_path`, `exists_units`
  (`ForMathlib.FlowDecomposition`).

### Codes and the cutset bound (pages 16-2 to 16-4, 16-6, 16-7, 16-24 and 16-25)
* `NoiselessNetwork`, `NetCode`, `NetCode.edge`, `NetCode.out`, `NetCode.Correct`,
  `NetCode.errProb`, `RateCode`, `IsAchievable`, `IsAchievableZE`, `capacityRegion`, `singleRate`,
  `multicastD`, `multicastCapacity` (`Network.NoiselessCode`).
* "Why?" of page 16-6: `NetCode.edge_congr`, `NetCode.out_congr`.
* **Cutset outer bound**: `cutSources`, `cutsetRegion`, `NetCode.cut_bound`, `RateCode.cut_bound`,
  `IsAchievable.mem_cutsetRegion`, `capacityRegion_subset_cutsetRegion`, and for one source
  `IsAchievable.le_minCut`. Here: `cutset_outer_bound`.
* Changing the alphabets of a code: `NetCode.exists_relabel`.

### Routing and the max-flow min-cut theorem (pages 16-5 to 16-12)
* `RoutingScheme`, `RoutingScheme.code`, `RoutingScheme.code_correct`,
  `RoutingScheme.exists_rateCode`, `IsRoutingAchievable`, `IsRoutingAchievable.isAchievableZE`
  (`Network.NoiselessRouting`).
* `exists_routes`, `cutCap_floor_ge`, `isRoutingAchievable_of_lt_minCut`.
* **Max-flow min-cut theorem (page 16-5)**: `relay_capacity`. Here: `max_flow_min_cut`.
* **Every node wants the message (page 16-12)**: `isRoutingAchievable_all_nodes`,
  `all_nodes_capacity`.

### Linear network coding (pages 16-16 to 16-22)
* `Multigraph`, `LinCoeff`, `LinCoeff.code`, `globalVec`, `transfer`, `LinVar`, `ofAssign`,
  `genericCoeff`, `detGeneric`, `aeval_detGeneric` (`Network.LinearNetworkCode`).
* Routing is linear with `A(α) = I`: `exists_coeff_of_bit`, `detGeneric_ne_zero_of_cuts`.
* A linear code with invertible matrices has no errors: `LinCoeff.code_correct`.
* `|A(x)| ≠ 0` implies the cut conditions: `cuts_of_detGeneric_ne_zero`
  (`Network.LinearNetworkCode`), and both directions in
  `detGeneric_ne_zero_iff` (`Network.NetworkCoding`).
* **Lemma 1 (page 16-21)**: `exists_aeval_galoisField_ne_zero` (`ForMathlib.PolyFiniteField`). Here:
  `lemma_16_1`.
* **Random linear codes (page 16-22)**: `card_aeval_eq_zero_le`, `card_not_invertible_le`.
* **The size of the field (page 16-22)**: `exists_aeval_ne_zero_of_degreeOf`,
  `degreeOf_globalVec_le`, `degreeOf_detGeneric_le`, `exists_coeff_of_card_gt`.
* **Zero error and finite block size for integer capacities**: `exists_linear_code`.

### The network coding theorem (page 16-15)
* `capGraph`, `capGraph_count`, `isAchievableZE_of_cuts`.
* **Network coding theorem**: `network_coding_theorem` (`Network.NetworkCoding`). Here:
  `network_coding`.
* **Multi-source multicast (page 16-25)**: `capacityRegion_multisource`.

### Examples (`Books.ElGamalKim.Lecture16Examples`, `Books.ElGamalKim.Lecture16Yeung`)
* Page 16-6: `exampleNet`, `exampleFlow`, `example_minCut`, `example_capacity`.
* Pages 16-13 and 16-14, the butterfly network: `butterflyNet`, `butterflyCode`,
  `butterflyCode_correct`, `butterfly_isAchievableZE`, `butterfly_le_two`, `butterfly_capacity`,
  and for routing `butterfly_routing_split`, `butterfly_routing_le`, `butterflyScheme`,
  `butterfly_routing_of_lt`, `butterfly_routing_rate_le`.
* Pages 16-18 and 16-20, the matrices of a linear code: `kmGraph`, `kmCoeff`, `km_transfer`,
  `km_det`.
* Pages 16-26 and 16-27, multiple unicast: `unicastNet`, `unicastD`, `unicastCode`,
  `unicastCode_correct`, `unicast_isAchievableZE`, `unicast_le_one`, `unicast_iff`,
  `unicast_routing_bound`, `unicast_routing_le`, `printed_unicast_routing`.
* Pages 16-27 and 16-28, the cutset bound is loose: `yeungNet`, `yeungD`, `yeungRate`,
  `yeung_count`, `yeung_le`, `yeungScheme`, `yeung_isRoutingAchievable`, `yeung_capacityRegion`,
  `yeung_cutsetRegion`, `yeung_cutset_loose`.

## Not formalized

* Networks with cycles (pages 16-10 and 16-25), which the notes take up in Lecture 19.
* The Ford–Fulkerson algorithm as an algorithm, its complexity and the claim that its routing has no
  cycles (page 16-10). The existence of an integer flow is proved by the same augmenting paths.
* Noninteger capacities through multigraphs of `n/k` bits, as such (page 16-19): the theorem is
  proved by another construction, see below.
* The efficient algorithm of [8] for finding `α`, and the NP-completeness of optimal routing
  (page 16-22), which are results on complexity.
* That the linear network coding inner bound is loose in general (page 16-28, cited from [14]).
* The conditions for multi-commodity flow by linear programming (page 16-26).

## Differences from the notes

* **The converse** counts correctly decoded messages instead of using Fano's inequality, so it is a
  strong converse: `(1 - P_e) 2^{n ∑ R_j} ≤ 2^{n C(S)}`.
* **Max-flow min-cut** is proved by augmenting paths instead of LP duality and Slater's condition,
  over any ordered ring. So the integer case has an integer flow, which the notes need for routing
  and linear codes (they appeal to "`R ≤ C` is achievable by routing" on page 16-21).
* **Several sources.** The notes only cite the capacity region of multi-source multicast networks.
  Here it comes from the same proof as the network coding theorem, by a flow with supplies at the
  sources and a source of all sources.
* **Lemma 1** follows from the Schwartz–Zippel lemma of Mathlib. The remark `n ≤ ⌈log(|D| R + 1)⌉`
  is proved from the bound `R` on the degree of `|A(x)|` in each indeterminate, and the
  combinatorial Nullstellensatz of Mathlib.
* **Real capacities.** For block length `n` we use the multigraph with `⌊K C⌋` edges, for a fixed
  large `K`, over the field `𝔽_{2^m}` with `m = ⌊n / K⌋`. So every large `n` has a code, without
  concatenating blocks.
* **Routing** is defined by the sets of bits that the edges carry, with any number of copies.
* **The capacity region of page 16-28** is stated in the notes without a proof. The converse here is
  a strong converse, by counting and the Cauchy–Schwarz inequality. Note that `R₁ ≤ 1` follows from
  `2 R₁ + R₂ ≤ 2` and `R₂ ≥ 0`.

## Issues in the notes

These were checked against the PDF.

* **Page 16-8.** The dual problem is printed with `νⱼ - νₖ = λⱼₖ`, and it has to be
  `νⱼ - νₖ ≤ λⱼₖ`, because the rates are nonnegative. As printed, its value on the network of page
  16-6 is at least `4`, and not the capacity `3` (`printed_dual_ge_four`). The optimal `ν*`, `λ*` of
  page 16-9 is feasible only for the inequality, since the edge `(4, 5)` goes back across the
  minimum cut.
* **Page 16-26.** The text has `D₁ = {5}`, `D₂ = {6}`, while the figure has `D₁ = {6}`, `D₂ = {5}`.
  With the text, each message has a direct edge to its destination, so routing achieves `(1, 1)`
  (`printed_unicast_routing`), against the claim of page 16-27. The cuts `{1, 3, 4, 5}` and
  `{2, 3, 4, 6}` of page 16-27 also fit the figure.
* **Page 16-13.** The bound `R₁ + R₂ ≤ 1` for routing uses that the source splits its message into
  two independent parts. If the source may send a bit on both of its edges then routing reaches
  rate `3/2` (`butterfly_routing_of_lt`), and no more (`butterfly_routing_rate_le`). The bound holds
  as stated, with the split (`butterfly_routing_split`), but `3/2` is the rate of routing in the
  sense of page 16-9.
* Page 16-9: `S ∈ N` should be `S ⊂ N`.
* Page 16-17: the second output of the source encoder is labelled `m_{e₁}`; it should be `m_{e₂}`.
* Page 16-22: "`A_j⁻¹(α)` is invertible" should be `A_j(α)`.
* Page 16-25: the condition "`Dⱼ ∩ Sᶜ ≠ ∅` for some `j`" should have `j ∈ S`, and "for all `j ∈ N`"
  in the multicast case should be for all `j ∈ [1 : k]`.
* Page 16-27: the cuts are called `J`, and `S` elsewhere.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

section Aliases

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- **Max-flow min-cut theorem, page 16-5.** -/
theorem max_flow_min_cut (N : NoiselessNetwork V) {s t : V} (hst : s ≠ t) :
    multicastCapacity N s {t} = minCut N.C s t :=
  relay_capacity N hst

/-- **Cutset outer bound, page 16-25.** -/
theorem cutset_outer_bound {N : NoiselessNetwork V} {D : V → Finset V} {R : V → ℝ}
    (h : IsAchievable N D R) (S : Finset V) : ∑ j ∈ cutSources D S, R j ≤ cutCap N.C S :=
  (IsAchievable.mem_cutsetRegion h).2 S

/-- **Network coding theorem, page 16-15.** -/
theorem network_coding (N : NoiselessNetwork V) {s : V} {T : Finset V} (hs : s ∉ T)
    (hT : T.Nonempty) : multicastCapacity N s T = T.inf' hT (minCut N.C s) :=
  network_coding_theorem N hs hT

/-- **Lemma 1 of Lecture 16, page 16-21.** -/
theorem lemma_16_1 {X : Type*} [Finite X] {P : MvPolynomial X (ZMod 2)} (hP : P ≠ 0) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ α : X → GaloisField 2 m, MvPolynomial.aeval α P ≠ 0 :=
  exists_aeval_galoisField_ne_zero hP

end Aliases

end InfoTheory.ElGamalKim
