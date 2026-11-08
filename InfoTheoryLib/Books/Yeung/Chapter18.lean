/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MaxFlowBound
public import InfoTheoryLib.Network.NoiselessRouting

/-!
# Yeung, Chapter 18: The Max-Flow Bound

This file indexes the formalization of Chapter 18 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included, except Problems 2a
and 3, which complete the proofs of the text.

## Conventions

* **Networks.** A network is a `PtpNetwork V E`: a multigraph with nodes `V`, edges `E`, maps
  `tail` and `head`, and rate constraints `cap e`. It may have cycles. Flows and cuts are on its
  matrix of capacities between nodes, `capMatrix`, which merges parallel edges, and `maxflow G s t`
  is the capacity of a min-cut, the value of a max-flow by Theorem 18.1.
* **Codes.** An `(n, (ηₑ), τ)` code of Section 18.3 is a `TransCode`: transactions `k : Fin K`
  instead of `1, …, K`, alphabets `A k` instead of index sets, and encoders and decoders as in
  (18.21)–(18.27). The block length `n` and the message set `{1, …, ⌈2^{nτ}⌉}` enter through
  Definition 18.2.
* **Bits.** In the examples a bit is an element of `ZMod 2`, the message of `ω` bits is a function
  `Fin ω → ZMod 2`, the book's `b₁, b₂, …` are `x 0, x 1, …`, and each transaction carries one bit.
* **Indexing.** In each example the nodes are numbered from `0`, starting with the source `s`, in
  the order in which the book names them, and the edges are listed in the definition of the network.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 18.1 Point-to-Point Communication Networks
* (18.1), the network: `PtpNetwork` (`Network.MaxFlowBound`).
* (18.2)–(18.6), flows and the conservation conditions: `IsFlow`, `netOut` (`ForMathlib.MaxFlow`) on
  `PtpNetwork.capMatrix` (`Network.MaxFlowBound`).
* (18.7)–(18.8), cuts and their capacity: `PtpNetwork.cutEdges`, `PtpNetwork.cutCap_capMatrix`
  (`Network.MaxFlowBound`), `cutCap`, `minCut` (`ForMathlib.MaxFlow`).
* Theorem 18.1 (Max-Flow Min-Cut Theorem): `theorem_18_1` (here), which is
  `PtpNetwork.isGreatest_maxflow` (`Network.MaxFlowBound`), from `maxFlow_minCut`
  (`ForMathlib.MaxFlow`). Problem 1, the value of a flow: `IsFlow.sum_netOut_eq`
  (`ForMathlib.MaxFlow`).

### 18.2 Examples Achieving the Max-Flow Bound
* (18.9)–(18.10): Theorem 18.3.
* Figure 18.2 and (18.11): `oneSinkNet`, `oneSinkCode` (here); `oneSinkNet_maxflow` and
  `oneSinkNet_achievable` (here): the max-flow is `3`, and the code achieves it.
* The remark that the max-flow bound is achieved by routing when there is one sink:
  `isRoutingAchievable_of_lt_minCut` (`Network.NoiselessRouting`), for acyclic networks and the
  codes of Lecture 16 of [elgamal2010].
* Figure 18.3, (18.12) and (18.13): `twoSinkNet`, `twoSinkCode`, `twoSinkCode₂` (here);
  `twoSinkNet_maxflow` and `twoSinkNet_achievable` (here): the max-flows are `5` and `6`, and
  routing achieves `5`.
* Figure 18.4 and (18.14): `butterflyNet'`, `butterflyCode'` (here); `butterflyNet'_maxflow` and
  `butterflyNet'_achievable` (here).
* Figure 18.5 and (18.15), diversity coding: `diversityNet`, `diversityCode` (here);
  `diversityNet_maxflow` and `diversityNet_achievable` (here).

### 18.3 A Class of Network Codes
* The `(n, (ηₑ), τ)` codes, (18.16)–(18.27): `PtpNetwork.TransCode`, with the induced functions
  `TransCode.val`, correctness `TransCode.Correct` and (18.19) `TransCode.eta`
  (`Network.MaxFlowBound`).

### 18.4 Proof of the Max-Flow Bound
* Definition 18.2: `PtpNetwork.IsAchievableInfoRate` (`Network.MaxFlowBound`).
* The remark after Definition 18.2: `PtpNetwork.IsAchievableInfoRate.mono`,
  `PtpNetwork.isClosed_setOf_isAchievableInfoRate` (`Network.MaxFlowBound`), which is
  Problem 2a.
* Theorem 18.3 (Max-Flow Bound): `theorem_18_3` (here), which is
  `PtpNetwork.IsAchievableInfoRate.le_maxflow` (`Network.MaxFlowBound`). The steps (18.34)–(18.40)
  are `TransCode.card_le_prod_eta`, by counting instead of entropies, and the claim of Problem 3 is
  `TransCode.val_congr` (`Network.MaxFlowBound`).
* A code for one unit of time gives an achievable rate: `PtpNetwork.isAchievableInfoRate_of_code`
  (`Network.MaxFlowBound`), with the repetition `TransCode.pow` and the relabelling
  `TransCode.mapMsg`.

## Not formalized

* The max-flow and the min-cut from the source to a collection of nodes and to a collection of
  edges, Figure 18.1, which Chapter 19 uses.
* The remark that each bit of Figure 18.3 is replicated exactly once, and the remark that coding
  is necessary in Figure 18.5.
* The disk array interpretation of Figure 18.5.
* Remark 2 after Theorem 18.3, the max-flow bound for codes with a small probability of error,
  which the book does not prove.

## References

Numbers without a source refer to [yeung2008].

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 18
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.Yeung

open PtpNetwork

/-- **Theorem 18.1 (Max-Flow Min-Cut Theorem).** -/
alias theorem_18_1 := PtpNetwork.isGreatest_maxflow

/-- **Theorem 18.3 (Max-Flow Bound).** -/
alias theorem_18_3 := PtpNetwork.IsAchievableInfoRate.le_maxflow

/-! ### Tools for the examples -/

/-- The capacity of a cut, computed in `ℕ`. -/
lemma sum_cutEdges_eq {V E : Type*} [DecidableEq V] [Fintype E] {G : PtpNetwork V E}
    {U : Finset V} {m : ℕ} (h : ∑ e ∈ G.cutEdges U, G.cap e = m) :
    ∑ e ∈ G.cutEdges U, (G.cap e : ℝ) = m := by
  rw [← Nat.cast_sum, h]

/-- In `ZMod 2`, `a + (a + b) = b`. -/
lemma zmod2_add_add (a b : ZMod 2) : a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-! ### Figure 18.2: a one-sink network -/

/-- **Figure 18.2(a).** The nodes `s, 1, 2, t₁` are `0, 1, 2, 3`, and the edges are `(s, 1)`,
`(s, 2)`, `(1, 2)`, `(1, t₁)` and `(2, t₁)`, of capacities `2, 2, 1, 1, 2`. -/
def oneSinkNet : PtpNetwork (Fin 4) (Fin 5) :=
  ⟨![0, 0, 1, 1, 2], ![1, 2, 2, 3, 3], ![2, 2, 1, 1, 2]⟩

/-- **Figure 18.2(c).** `s` sends `b₁ b₂` to `1` and `b₃` to `2`; node `1` forwards `b₁` to `2` and
`b₂` to `t₁`, and node `2` forwards `b₁ b₃` to `t₁`. -/
def oneSinkCode : oneSinkNet.TransCode 0 (Fin 3 → ZMod 2) {3} :=
  TransCode.ofFun 7 ![0, 0, 1, 2, 3, 4, 4]
    ![fun x _ => x 0, fun x _ => x 1, fun x _ => x 2, fun _ w => w 0, fun _ w => w 1,
      fun _ w => w 3, fun _ w => w 2]
    (fun k hk _ _ _ => by fin_cases k <;> first | rfl | exact (hk rfl).elim)
    fun _ _ w => ![w 5, w 4, w 6]

/-- The bit carried by each transaction of `oneSinkCode`. -/
def oneSinkBits (k : Fin 7) (x : Fin 3 → ZMod 2) : ZMod 2 := ![x 0, x 1, x 2, x 0, x 1, x 0, x 2] k

lemma oneSinkCode_correct : oneSinkCode.Correct :=
  TransCode.correct_ofFun oneSinkBits (fun k x => by fin_cases k <;> rfl) fun t ht x => by
    obtain rfl := mem_singleton.1 ht
    funext i
    fin_cases i <;> rfl

/-- **(18.11)** The max-flow from `s` to `t₁` is `3`, and Figure 18.2(c) achieves it. -/
theorem oneSinkNet_achievable : oneSinkNet.IsAchievableInfoRate 0 {3} 3 :=
  isAchievableInfoRate_of_code oneSinkCode oneSinkCode_correct (by simp) fun e => by
    rw [oneSinkCode, TransCode.eta_ofFun, ZMod.card]
    fin_cases e <;> decide

/-- **(18.11)** The max-flow from `s` to `t₁` is `3`: the min-cut is `{s, 1, 2}`. -/
theorem oneSinkNet_maxflow : oneSinkNet.maxflow 0 3 = 3 := by
  refine le_antisymm ?_ (by exact_mod_cast oneSinkNet_achievable.le_maxflow (by simp) (by decide))
  refine (oneSinkNet.maxflow_le (U := {0, 1, 2}) (by decide) (by decide)).trans_eq ?_
  rw [sum_cutEdges_eq (m := 3) (by decide)]
  norm_num

/-! ### Figure 18.3: a two-sink network without coding -/

/-- **Figure 18.3(a).** The nodes `s, 1, 2, 3, t₁, t₂` are `0, …, 5`, and the edges are `(s, 1)`,
`(s, 2)`, `(s, 3)`, `(2, 1)`, `(3, 2)`, `(1, t₁)`, `(1, t₂)`, `(3, t₁)` and `(3, t₂)`, of capacities
`2, 1, 3, 1, 1, 4, 3, 2, 3`. -/
def twoSinkNet : PtpNetwork (Fin 6) (Fin 9) :=
  ⟨![0, 0, 0, 2, 3, 1, 1, 3, 3], ![1, 2, 3, 1, 2, 4, 5, 4, 5], ![2, 1, 3, 1, 1, 4, 3, 2, 3]⟩

/-- **Figure 18.3(b).** The routing scheme that multicasts `b₁, …, b₅`: `b₁ b₂` are replicated at
node `3`, `b₃` at `s`, and `b₄ b₅` at node `1`. -/
def twoSinkCode : twoSinkNet.TransCode 0 (Fin 5 → ZMod 2) {4, 5} :=
  TransCode.ofFun 17 ![0, 0, 1, 2, 2, 2, 3, 5, 5, 5, 7, 7, 6, 6, 8, 8, 8]
    ![fun x _ => x 3, fun x _ => x 4, fun x _ => x 2, fun x _ => x 0, fun x _ => x 1,
      fun x _ => x 2, fun _ w => w 2, fun _ w => w 6, fun _ w => w 0, fun _ w => w 1,
      fun _ w => w 3, fun _ w => w 4, fun _ w => w 0, fun _ w => w 1, fun _ w => w 3,
      fun _ w => w 4, fun _ w => w 5]
    (fun k hk _ _ _ => by fin_cases k <;> first | rfl | exact (hk rfl).elim)
    fun t _ w => if t = 4 then ![w 10, w 11, w 7, w 8, w 9] else ![w 14, w 15, w 16, w 12, w 13]

/-- The bit carried by each transaction of `twoSinkCode`. -/
def twoSinkBits (k : Fin 17) (x : Fin 5 → ZMod 2) : ZMod 2 :=
  ![x 3, x 4, x 2, x 0, x 1, x 2, x 2, x 2, x 3, x 4, x 0, x 1, x 3, x 4, x 0, x 1, x 2] k

lemma twoSinkCode_correct : twoSinkCode.Correct :=
  TransCode.correct_ofFun twoSinkBits (fun k x => by fin_cases k <;> rfl) fun t ht x => by
    rcases mem_insert.1 ht with rfl | ht
    · funext i
      fin_cases i <;> rfl
    · obtain rfl := mem_singleton.1 ht
      funext i
      fin_cases i <;> rfl

/-- A routing scheme that sends `6` bits to `t₂` alone, along `s → 1 → t₂`, `s → 2 → 1 → t₂` and
`s → 3 → t₂`. -/
def twoSinkCode₂ : twoSinkNet.TransCode 0 (Fin 6 → ZMod 2) {5} :=
  TransCode.ofFun 13 ![0, 0, 1, 2, 2, 2, 3, 6, 6, 6, 8, 8, 8]
    ![fun x _ => x 0, fun x _ => x 1, fun x _ => x 2, fun x _ => x 3, fun x _ => x 4,
      fun x _ => x 5, fun _ w => w 2, fun _ w => w 0, fun _ w => w 1, fun _ w => w 6,
      fun _ w => w 3, fun _ w => w 4, fun _ w => w 5]
    (fun k hk _ _ _ => by fin_cases k <;> first | rfl | exact (hk rfl).elim)
    fun _ _ w => ![w 7, w 8, w 9, w 10, w 11, w 12]

/-- The bit carried by each transaction of `twoSinkCode₂`. -/
def twoSinkBits₂ (k : Fin 13) (x : Fin 6 → ZMod 2) : ZMod 2 :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 2, x 0, x 1, x 2, x 3, x 4, x 5] k

lemma twoSinkCode₂_correct : twoSinkCode₂.Correct :=
  TransCode.correct_ofFun twoSinkBits₂ (fun k x => by fin_cases k <;> rfl) fun t ht x => by
    obtain rfl := mem_singleton.1 ht
    funext i
    fin_cases i <;> rfl

/-- **Figure 18.3(b).** Routing multicasts `5` bits to `t₁` and `t₂`. -/
theorem twoSinkNet_achievable : twoSinkNet.IsAchievableInfoRate 0 {4, 5} 5 :=
  isAchievableInfoRate_of_code twoSinkCode twoSinkCode_correct (by simp) fun e => by
    rw [twoSinkCode, TransCode.eta_ofFun, ZMod.card]
    fin_cases e <;> decide

/-- **(18.12)–(18.13)** The max-flows from `s` to `t₁` and `t₂` are `5` and `6`. -/
theorem twoSinkNet_maxflow : twoSinkNet.maxflow 0 4 = 5 ∧ twoSinkNet.maxflow 0 5 = 6 := by
  have h₂ : twoSinkNet.IsAchievableInfoRate 0 {5} 6 :=
    isAchievableInfoRate_of_code twoSinkCode₂ twoSinkCode₂_correct (by simp) fun e => by
      rw [twoSinkCode₂, TransCode.eta_ofFun, ZMod.card]
      fin_cases e <;> decide
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · refine (twoSinkNet.maxflow_le (U := {0, 2, 3, 5}) (by decide) (by decide)).trans_eq ?_
    rw [sum_cutEdges_eq (m := 5) (by decide)]
    norm_num
  · exact_mod_cast twoSinkNet_achievable.le_maxflow (by simp) (by decide)
  · refine (twoSinkNet.maxflow_le (U := {0, 1, 2, 3, 4}) (by decide) (by decide)).trans_eq ?_
    rw [sum_cutEdges_eq (m := 6) (by decide)]
    norm_num
  · exact_mod_cast h₂.le_maxflow (by simp) (by decide)

/-! ### Figure 18.4: the butterfly network -/

/-- **Figure 18.4(a).** The nodes `s, 1, 2, 3, 4, t₁, t₂` are `0, …, 6`, and the edges are `(s, 1)`,
`(s, 2)`, `(1, 3)`, `(1, t₁)`, `(2, 3)`, `(2, t₂)`, `(3, 4)`, `(4, t₁)` and `(4, t₂)`, all of
capacity `1`. -/
def butterflyNet' : PtpNetwork (Fin 7) (Fin 9) :=
  ⟨![0, 0, 1, 1, 2, 2, 3, 4, 4], ![1, 2, 3, 5, 3, 6, 4, 5, 6], fun _ => 1⟩

/-- **Figure 18.4(b).** Node `3` sends `b₁ + b₂`. -/
def butterflyCode' : butterflyNet'.TransCode 0 (Fin 2 → ZMod 2) {5, 6} :=
  TransCode.ofFun 9 id
    ![fun x _ => x 0, fun x _ => x 1, fun _ w => w 0, fun _ w => w 0, fun _ w => w 1,
      fun _ w => w 1, fun _ w => w 2 + w 4, fun _ w => w 6, fun _ w => w 6]
    (fun k hk _ _ _ => by fin_cases k <;> first | rfl | exact (hk rfl).elim)
    fun t _ w => if t = 5 then ![w 3, w 3 + w 7] else ![w 5 + w 8, w 5]

/-- The bit carried by each transaction of `butterflyCode'`. -/
def butterflyBits' (k : Fin 9) (x : Fin 2 → ZMod 2) : ZMod 2 :=
  ![x 0, x 1, x 0, x 0, x 1, x 1, x 0 + x 1, x 0 + x 1, x 0 + x 1] k

lemma butterflyCode'_correct : butterflyCode'.Correct :=
  TransCode.correct_ofFun butterflyBits' (fun k x => by fin_cases k <;> rfl) fun t ht x => by
    rcases mem_insert.1 ht with rfl | ht
    · funext i
      fin_cases i
      · rfl
      · exact zmod2_add_add (x 0) (x 1)
    · obtain rfl := mem_singleton.1 ht
      funext i
      fin_cases i
      · change x 1 + (x 0 + x 1) = x 0
        rw [add_comm (x 0), zmod2_add_add]
      · rfl

/-- **Figure 18.4(b).** Network coding multicasts `2` bits to `t₁` and `t₂`. -/
theorem butterflyNet'_achievable : butterflyNet'.IsAchievableInfoRate 0 {5, 6} 2 :=
  isAchievableInfoRate_of_code butterflyCode' butterflyCode'_correct (by simp) fun e => by
    rw [butterflyCode', TransCode.eta_ofFun, ZMod.card]
    fin_cases e <;> decide

/-- **(18.14)** The max-flows from `s` to `t₁` and `t₂` are `2`. -/
theorem butterflyNet'_maxflow :
    butterflyNet'.maxflow 0 5 = 2 ∧ butterflyNet'.maxflow 0 6 = 2 := by
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · refine (butterflyNet'.maxflow_le (U := {0, 2, 6}) (by decide) (by decide)).trans_eq ?_
    rw [sum_cutEdges_eq (m := 2) (by decide)]
    norm_num
  · exact_mod_cast butterflyNet'_achievable.le_maxflow (by simp) (by decide)
  · refine (butterflyNet'.maxflow_le (U := {0, 1, 5}) (by decide) (by decide)).trans_eq ?_
    rw [sum_cutEdges_eq (m := 2) (by decide)]
    norm_num
  · exact_mod_cast butterflyNet'_achievable.le_maxflow (by simp) (by decide)

/-! ### Figure 18.5: a diversity coding scheme -/

/-- **Figure 18.5(a).** The nodes `s, 1, 2, 3, t₁, t₂, t₃` are `0, …, 6`, and the edges are
`(s, 1)`, `(s, 2)`, `(s, 3)`, `(1, t₁)`, `(1, t₂)`, `(2, t₁)`, `(2, t₃)`, `(3, t₂)` and
`(3, t₃)`, all of capacity `1`. -/
def diversityNet : PtpNetwork (Fin 7) (Fin 9) :=
  ⟨![0, 0, 0, 1, 1, 2, 2, 3, 3], ![1, 2, 3, 4, 5, 4, 6, 5, 6], fun _ => 1⟩

/-- **Figure 18.5(b).** The disks `1, 2, 3` store `b₁`, `b₂` and `b₁ + b₂`. -/
def diversityCode : diversityNet.TransCode 0 (Fin 2 → ZMod 2) {4, 5, 6} :=
  TransCode.ofFun 9 id
    ![fun x _ => x 0, fun x _ => x 1, fun x _ => x 0 + x 1, fun _ w => w 0, fun _ w => w 0,
      fun _ w => w 1, fun _ w => w 1, fun _ w => w 2, fun _ w => w 2]
    (fun k hk _ _ _ => by fin_cases k <;> first | rfl | exact (hk rfl).elim)
    fun t _ w => if t = 4 then ![w 3, w 5] else if t = 5 then ![w 4, w 4 + w 7]
      else ![w 6 + w 8, w 6]

/-- The bit carried by each transaction of `diversityCode`. -/
def diversityBits (k : Fin 9) (x : Fin 2 → ZMod 2) : ZMod 2 :=
  ![x 0, x 1, x 0 + x 1, x 0, x 0, x 1, x 1, x 0 + x 1, x 0 + x 1] k

lemma diversityCode_correct : diversityCode.Correct :=
  TransCode.correct_ofFun diversityBits (fun k x => by fin_cases k <;> rfl) fun t ht x => by
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i
      · rfl
      · exact zmod2_add_add (x 0) (x 1)
    · funext i
      fin_cases i
      · change x 1 + (x 0 + x 1) = x 0
        rw [add_comm (x 0), zmod2_add_add]
      · rfl

/-- **Figure 18.5(b).** Network coding multicasts `2` bits to `t₁`, `t₂` and `t₃`. -/
theorem diversityNet_achievable : diversityNet.IsAchievableInfoRate 0 {4, 5, 6} 2 :=
  isAchievableInfoRate_of_code diversityCode diversityCode_correct (by simp) fun e => by
    rw [diversityCode, TransCode.eta_ofFun, ZMod.card]
    fin_cases e <;> decide

/-- **(18.15)** The max-flows from `s` to `t₁`, `t₂` and `t₃` are `2`. -/
theorem diversityNet_maxflow :
    ∀ t ∈ ({4, 5, 6} : Finset (Fin 7)), diversityNet.maxflow 0 t = 2 := by
  intro t ht
  refine le_antisymm ?_ (by exact_mod_cast diversityNet_achievable.le_maxflow ht (by
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide))
  refine (diversityNet.maxflow_le (U := univ.erase t) (by
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide) (by simp)).trans_eq ?_
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;>
  · rw [sum_cutEdges_eq (m := 2) (by decide)]
    norm_num

end InfoTheory.Yeung
