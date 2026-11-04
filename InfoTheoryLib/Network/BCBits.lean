/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.Broadcast

/-!
# Broadcast channels in bits, and the superposition coding regions

In their lecture notes, El Gamal and Kim measure the rates of the DM-BC `p(y₁, y₂ | x)` in bits,
with message sets `[1 : 2^{nRⱼ}] = {1, …, 2^⌈nRⱼ⌉}`, and focus on private messages. This file
gives these definitions, and the regions of the superposition coding inner bound and of the
capacity region of the degraded broadcast channel, for an auxiliary random variable `U` with
`p(u, x)`.

## Main definitions

* `IsAchievableBCBits W R₁ R₂`, `bcCapacityRegionBits W`: achievable rate pairs (private
  messages) in bits and the capacity region.
* `bcJoint q W`: the law `p(u, x) p(y₁, y₂ | x)` of `((U, X), (Y₁, Y₂))`.
* `bcInfoXY₁U`, `bcInfoUY₂`, `bcInfoXY₁`, `bcInfoUY₁`, `bcInfoXY₂U`, `bcInfoXY₂`: the mutual
  informations `I(X; Y₁ | U)`, `I(U; Y₂)`, `I(X; Y₁)`, `I(U; Y₁)`, `I(X; Y₂ | U)`, `I(X; Y₂)`,
  in nats.
* `superpositionRegionBits W`: the superposition coding inner bound `R₁ < I(X; Y₁ | U)`,
  `R₂ < I(U; Y₂)`, `R₁ + R₂ < I(X; Y₁)` (Theorem 1 of Lecture 5), in bits.
* `degradedBCRegionBits W`: `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` (Theorem 2 of Lecture 5), in
  bits.

## Implementation notes

The auxiliary random variable `U` takes values in `Fin k` for some `k`, so that the regions do not
quantify over types. The regions are not intersected with `R₁, R₂ ≥ 0`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂]

/-! ### Achievable rates in bits -/

/-- **Definition (Lecture 5 of [elgamal2010]).** A rate pair `(R₁, R₂)` of private messages, in
bits per transmission, is achievable for the DM-BC if there are `(2^{nR₁}, 2^{nR₂}, n)` codes,
with message sets `[1 : 2^{nRⱼ}] = {1, …, 2^⌈nRⱼ⌉}`, whose average probability of error tends
to `0`. -/
def IsAchievableBCBits (W : α → β₁ × β₂ → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, BCCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α β₁ β₂,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Definition (Lecture 5 of [elgamal2010]).** The private-message capacity region of the DM-BC,
in bits: the closure of the set of achievable rate pairs. -/
def bcCapacityRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableBCBits W R.1 R.2}

/-! ### The law of `(U, X, Y₁, Y₂)` -/

variable {𝒰 : Type*} [Fintype 𝒰]

/-- The law `p(u, x) p(y₁, y₂ | x)` of `((U, X), (Y₁, Y₂))`: `U → X → (Y₁, Y₂)`. -/
def bcJoint (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) : (𝒰 × α) × (β₁ × β₂) → ℝ :=
  jointOf q fun z => W z.2

lemma bcJoint_isPMF {q : 𝒰 × α → ℝ} (hq : IsPMF q) {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W) :
    IsPMF (bcJoint q W) :=
  jointOf_isPMF hq fun z => hW z.2

/-- `I(X; Y₁ | U)`. -/
def bcInfoXY₁U (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2 : fun z => z.2.1 | fun z => z.1.1 ; bcJoint q W]

/-- `I(U; Y₂)`. -/
def bcInfoUY₂ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1 : fun z => z.2.2 ; bcJoint q W]

/-- `I(X; Y₁)`. -/
def bcInfoXY₁ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2 : fun z => z.2.1 ; bcJoint q W]

/-- `I(U; Y₁)`. -/
def bcInfoUY₁ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1 : fun z => z.2.1 ; bcJoint q W]

/-- `I(X; Y₂ | U)`. -/
def bcInfoXY₂U (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2 : fun z => z.2.2 | fun z => z.1.1 ; bcJoint q W]

/-- `I(X; Y₂)`. -/
def bcInfoXY₂ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2 : fun z => z.2.2 ; bcJoint q W]

/-! ### The regions -/

/-- **Theorem 1 of [elgamal2010], Lecture 5.** The superposition coding inner bound, in bits:
the rate pairs with `R₁ < I(X; Y₁ | U)`, `R₂ < I(U; Y₂)` and `R₁ + R₂ < I(X; Y₁)` for some
`p(u, x)`, with `U` on `Fin k`. Receiver 2 decodes the cloud center `U`, receiver 1 the satellite
codeword `X`. -/
def superpositionRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧ R.1 < bcInfoXY₁U q W / log 2 ∧
    R.2 < bcInfoUY₂ q W / log 2 ∧ R.1 + R.2 < bcInfoXY₁ q W / log 2}

/-- **Lecture 5 of [elgamal2010].** The superposition coding inner bound with the roles of the
receivers exchanged: `R₁ < I(U; Y₁)`, `R₂ < I(X; Y₂ | U)`, `R₁ + R₂ < I(X; Y₂)`. -/
def superpositionRegionBits₂ (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧ R.1 < bcInfoUY₁ q W / log 2 ∧
    R.2 < bcInfoXY₂U q W / log 2 ∧ R.1 + R.2 < bcInfoXY₂ q W / log 2}

/-- **Theorem 2 of [elgamal2010], Lecture 5.** The region `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` for
some `p(u, x)`, in bits, with `U` on `Fin k`: the capacity region of the degraded DM-BC (up to
closure, as the cardinality of `U` is not bounded). -/
def degradedBCRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧ R.1 ≤ bcInfoXY₁U q W / log 2 ∧
    R.2 ≤ bcInfoUY₂ q W / log 2}

end InfoTheory
