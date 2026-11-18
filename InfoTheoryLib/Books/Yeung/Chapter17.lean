/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture16Examples
public import InfoTheoryLib.Network.Forwarding

/-!
# Yeung, Chapter 17: Introduction

This file indexes the formalization of Chapter 17 of [yeung2008], the introduction to Part II, and
contains its worked examples and aliases named after the numbers of the results, so the index is
checked by Lean. It cites the draft of 15 November 2007, which numbers definitions, theorems and
examples with one counter per chapter. The end-of-chapter problems and the historical notes are not
included, except Problem 3.

## Conventions

* **Networks and codes.** A network is a `NoiselessNetwork` on `Fin n`, an acyclic directed graph
  whose nodes are numbered so that the edges go up, and a code is a `NetCode`: each node encodes
  the symbols received from lower nodes and its own message, and each node decodes from the
  symbols it receives (`Network.NoiselessCode`). These are the networks and codes of Lecture 16 of
  [elgamal2010], which shares the butterfly examples.
* **Indexing.** The nodes of the butterfly network of Figure 17.1 are `s, 1, 2, 3, 4, t₁, t₂`,
  numbered `0` to `6`. The nodes of the network of Figure 17.2(a) are `1, 2, 3, 4, t₁, t₂`,
  numbered `0` to `5`.
* **Bits.** A bit is an element of `ZMod 2`, and a block of `n` bits is `Bitstream n`; the book's
  examples are the case `n = 1`, one bit per channel use.
* **Routing.** A routing scheme is a `RoutingScheme`: each edge carries a set of the source bits,
  at most its capacity, every bit on an edge was generated or received by its tail, and every sink
  receives the bits it wants. Replication at intermediate nodes is allowed.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 17.1 The Butterfly Network
* Example 17.1: `example_17_1` (here), from `butterflyCode_correct`
  (`Books.ElGamalKim.Lecture16Examples`): the code of Figure 17.1(c) multicasts `b₁` and `b₂`.
  `example_17_1_routing` (here): no routing scheme multicasts the two bits in one unit of time,
  by `butterfly_routing_le`. The average rate of routing is at most `1.5` bits per unit time,
  `butterfly_routing_rate_le`, and every rate below `1.5` is achieved by routing,
  `butterfly_routing_of_lt` (`Books.ElGamalKim.Lecture16Examples`), which is Problem 3.
* Example 17.2: `example_17_2` (here), with `example172Code` (here): the code of Figure 17.2(b)
  multicasts `b₁` and `b₂` to `t₁` and `t₂`. The two unicasts of Figure 17.2(c), where node `tᵢ`
  already holds `bᵢ`, are the network `unicastNet` with the demands `unicastD`; network coding
  solves them, `unicastCode_correct`, and routing must send both bits through `(3, 4)`,
  `unicast_routing_bound` (`Books.ElGamalKim.Lecture16Examples`).

### 17.2 Wireless and Satellite Communications
* Proposition 17.3: `proposition_17_3` (here), from `NetCode.forward_edge_self` and
  `NetCode.forward_out` (`Network.Forwarding`).
* Example 17.4: `example_17_4` (here). As in the book, the system is the network of
  Figure 17.2(c), with node `3` as the relay and node `4` as its dummy node. One use of the
  downlink `(3, 4)` suffices with network coding, while routing needs two.

### 17.3 Source Separation
* (17.2): `mutualInfo_eq_zero_iff` and `mutualInfo_eq_add_sub` (`MutualInformation.Basic`):
  `I(X; Y) = H(X) + H(Y) - H(X, Y)` vanishes exactly for independent `X` and `Y`.
* The suboptimality of source separation: `card_range_separate` and `card_range_add` (here). On
  the channel `(3, 4)` of Figure 17.2(c), a code that encodes `B₁` and `B₂` separately sends one
  of `4` symbols, two bits, while the network code sends one of `2`.

## Not formalized

* The introduction on routing in computer networks, and the claim that fair bits behave like a
  commodity in point-to-point communication.
* The scheme of Figure 17.1(d), which exceeds the capacity of `(3, 4)`, and the equivalence of
  Figures 17.3(a) and (b), the broadcast constraint modelled by a dummy node. Proposition 17.3 is
  the fact on which this modelling rests.
* The scheduling of Example 17.4 in time slots, with half-duplex nodes; the count of time units is
  read here as the number of uses of the downlink `(3, 4)`, as the book does.
* Figures 17.1 to 17.4.

## References

Numbers without a source refer to [yeung2008].

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 17
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory.Yeung

open InfoTheory.ElGamalKim

/-! ### 17.1 The Butterfly Network -/

/-- **Example 17.1 (Butterfly Network I).** The network code of Figure 17.1(c), in which node `3`
sends `b₁ + b₂`, multicasts both bits to `t₁` and `t₂`, for blocks of any length `n`. -/
theorem example_17_1 (n : ℕ) (m : Fin 7 → Bitstream n × Bitstream n) :
    (butterflyCode n).Correct (multicastD 0 {5, 6}) m :=
  butterflyCode_correct n m

/-- **Example 17.1 (Butterfly Network I).** With binary symbols and one bit per channel, no routing
scheme multicasts the two bits of `s` to `t₁` and `t₂`, even with replication at the nodes. -/
theorem example_17_1_routing :
    IsEmpty (RoutingScheme butterflyW (fun j => if j = 0 then 2 else 0) (multicastD 0 {5, 6})) := by
  refine ⟨fun S => ?_⟩
  have h := butterfly_routing_le (n := 1) S (fun _ _ h => h) (fun j hj => by simp [hj])
    (fun j k => by revert j k; decide)
  simp at h

/-- The destinations of Figure 17.2(b): both `t₁` and `t₂` want both bits. -/
def example172D : Fin 6 → Finset (Fin 6) := ![{4, 5}, {4, 5}, ∅, ∅, ∅, ∅]

/-- The network code of Figure 17.2(b): the encoders of `unicastCode`, and `t₁` decodes `b₁` from
node `1` and `b₂` as `b₁ + (b₁ + b₂)`, and symmetrically at `t₂`. -/
def example172Code (n : ℕ) : NetCode (Fin 6) (fun _ _ => Bitstream n) (fun _ => Bitstream n) :=
  funCode
    (fun k l u m => if unicastW k l = 0 then 0 else
      if k = 0 ∨ k = 1 then m else if k = 2 then u 0 + u 1 else u 2)
    (fun l j u => if l = 4 then (if j = 0 then u 0 else u 0 + u 3)
      else if j = 1 then u 1 else u 1 + u 3)

/-- **Example 17.2 (Butterfly Network II).** When `b₁` is generated at node `1` and `b₂` at node
`2`, the network code of Figure 17.2(b) multicasts both bits to `t₁` and `t₂`. -/
theorem example_17_2 (n : ℕ) (m : Fin 6 → Bitstream n) :
    (example172Code n).Correct example172D m := by
  have e02 : (example172Code n).edge m 0 2 = m 0 := by
    rw [example172Code, funCode_edge]
    simp [unicastW]
  have e04 : (example172Code n).edge m 0 4 = m 0 := by
    rw [example172Code, funCode_edge]
    simp [unicastW]
  have e12 : (example172Code n).edge m 1 2 = m 1 := by
    rw [example172Code, funCode_edge]
    simp [unicastW]
  have e15 : (example172Code n).edge m 1 5 = m 1 := by
    rw [example172Code, funCode_edge]
    simp [unicastW]
  have e23 : (example172Code n).edge m 2 3 = m 0 + m 1 := by
    rw [← e02, ← e12, example172Code, funCode_edge]
    simp [unicastW]
  have e34 : (example172Code n).edge m 3 4 = m 0 + m 1 := by
    rw [← e23, example172Code, funCode_edge]
    simp [unicastW]
  have e35 : (example172Code n).edge m 3 5 = m 0 + m 1 := by
    rw [← e23, example172Code, funCode_edge]
    simp [unicastW]
  intro j l hl
  have hj : (j = 0 ∨ j = 1) ∧ (l = 4 ∨ l = 5) := by
    have hall : ∀ j l : Fin 6, l ∈ example172D j → (j = 0 ∨ j = 1) ∧ (l = 4 ∨ l = 5) := by
      decide
    exact hall j l hl
  rw [example172Code, funCode_out, ← example172Code]
  obtain ⟨rfl | rfl, rfl | rfl⟩ := hj
  · simp [e04]
  · simp only [e15, e35, show ¬ (5 : Fin 6) = 4 by decide, ite_false, ite_true,
      show (1 : Fin 6) < 5 by decide, show (3 : Fin 6) < 5 by decide,
      show ¬ (0 : Fin 6) = 1 by decide]
    rw [add_comm (m 0), stream_add_add]
  · simp only [e04, e34, ite_true, show (0 : Fin 6) < 4 by decide,
      show (3 : Fin 6) < 4 by decide, show ¬ (1 : Fin 6) = 0 by decide, ite_false]
    rw [stream_add_add]
  · simp [e15]

/-! ### 17.2 Wireless and Satellite Communications -/

/-- **Proposition 17.3.** Network coding is not necessary at a node `k` without a message whose
only input channel comes from `j`, when each output channel can carry the input symbol: some code
makes `k` forward its input on every output channel and decodes exactly as the given one. -/
theorem proposition_17_3 {V : Type*} [LinearOrder V] [Finite V] {A : V → V → Type*}
    {M : V → Type*} (c : NetCode V A M) {j k : V} (hjk : j < k) [∀ i, Nonempty (A i k)]
    (hin : ∀ i, i ≠ j → Subsingleton (A i k)) [Nonempty (M k)] [Subsingleton (M k)]
    (r : ∀ l, A k l → A j k) (s : ∀ l, A j k → A k l) (hrs : ∀ l x, r l (s l x) = x) :
    ∃ c' : NetCode V A M, (∀ m l, c'.edge m k l = s l (c.edge m j k)) ∧
      ∀ m l i, c'.out m l i = c.out m l i :=
  ⟨c.forward hjk r s, c.forward_edge_self hjk r s hin hrs, c.forward_out hjk r s hin hrs⟩

/-- **Example 17.4 (A Wireless/Satellite System).** Modelled by the network of Figure 17.2(c), with
the relay as node `3` and its dummy node as node `4`: the network code exchanges `b₁` and `b₂` with
one use of the downlink `(3, 4)`, while any routing scheme that exchanges the two bits needs two
uses of it. Numbered from `0`, the downlink is the edge `(2, 3)`. -/
theorem example_17_4 :
    (∀ m, (unicastCode 1).Correct unicastD m) ∧
      ∀ (cap : Fin 6 → Fin 6 → ℕ), (∀ j k, unicastW j k = 0 → cap j k = 0) →
        RoutingScheme cap (fun j => if j = 0 ∨ j = 1 then 1 else 0) unicastD → 2 ≤ cap 2 3 := by
  refine ⟨unicastCode_correct 1, fun cap hz S => ?_⟩
  have := unicast_routing_bound S hz fun j hj => by
    have : ¬ (j = 0 ∨ j = 1) := by omega
    simp [this]
  simpa using this

/-! ### 17.3 Source Separation -/

/-- **Section 17.3.** A code on the channel `(3, 4)` of Figure 17.2(c) that encodes the bits `B₁`
and `B₂` separately, as `(f₁ B₁, f₂ B₂)`, from which `t'₂` decodes `B₁` with its own `B₂` and `t'₁`
decodes `B₂` with `B₁`, takes `4` values: it sends two bits. -/
theorem card_range_separate {A₁ A₂ : Type*} (f₁ : ZMod 2 → A₁) (f₂ : ZMod 2 → A₂)
    (d₁ : A₁ × A₂ → ZMod 2 → ZMod 2) (d₂ : A₁ × A₂ → ZMod 2 → ZMod 2)
    (h₁ : ∀ b₁ b₂, d₁ (f₁ b₁, f₂ b₂) b₂ = b₁) (h₂ : ∀ b₁ b₂, d₂ (f₁ b₁, f₂ b₂) b₁ = b₂) :
    Nat.card (Set.range fun b : ZMod 2 × ZMod 2 => (f₁ b.1, f₂ b.2)) = 4 := by
  have hinj : Function.Injective fun b : ZMod 2 × ZMod 2 => (f₁ b.1, f₂ b.2) := by
    rintro ⟨a₁, a₂⟩ ⟨c₁, c₂⟩ h
    simp only [Prod.mk.injEq] at h
    refine Prod.ext ?_ ?_
    · rw [← h₁ a₁ a₂, ← h₁ c₁ a₂, h.1]
    · rw [← h₂ a₁ a₂, ← h₂ a₁ c₂, h.2]
  rw [Nat.card_range_of_injective hinj]
  simp [Nat.card_eq_fintype_card]

/-- **Section 17.3.** The network code of Figure 17.2(c) sends `B₁ + B₂` on the channel `(3, 4)`,
which takes `2` values: one bit. -/
theorem card_range_add :
    Nat.card (Set.range fun b : ZMod 2 × ZMod 2 => b.1 + b.2) = 2 := by
  have : Set.range (fun b : ZMod 2 × ZMod 2 => b.1 + b.2) = Set.univ :=
    Set.eq_univ_of_forall fun x => ⟨(x, 0), by simp⟩
  rw [this, Nat.card_univ]
  simp [Nat.card_eq_fintype_card]

end InfoTheory.Yeung
