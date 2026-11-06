/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BC3Cardinality
public import InfoTheoryLib.Network.MACCardinality
public import InfoTheoryLib.Network.MartonCardinality

/-!
# El Gamal & Kim, Appendix C: Cardinality Bounding Techniques

This file indexes the formalization of Appendix C of [elgamal2010]: the support lemma, its
application to the degraded DM-BC and to the 3-receiver degraded DM-BC, the time-sharing variable of
the DM-MAC, and the perturbation method for the sum rate of the Marton inner bound.

Two consequences go beyond the appendix: with a bounded auxiliary alphabet the regions are closed,
so the capacity regions of the degraded DM-BC and of the DM-MAC hold without a closure.

## Conventions

* **Alphabets.** A bound `|𝒰| ≤ K` is stated with `U` on `Fin K`, since a value can have probability
  zero. So `U'` takes at most `K` values.
* **Conditional pmfs.** A law `p(u, x)` is written `w(u) r(u, x)`, with `r` a channel, as
  `fun z => w z.1 * r z.1 z.2`. The conditional pmf at a value with `p(u) = 0` is arbitrary.
* **Channels.** The informations depend only on the marginals `p(yⱼ | x)` of the channel, and the
  3-receiver DM-BC is stated with one channel `T₁`, `T₂`, `T₃` for each receiver.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The support lemma (page C-1; `ForMathlib.SupportLemma`)
* **The lemma:** here `support_lemma`, from `exists_fin_mixture_eq_integral`, on any connected
  compact set of parameters.
* The form for a finite mixture: `exists_fin_mixture_eq_sum`.
* The form that also preserves the mean output of a channel, in `|A| - 1` further coordinates:
  `exists_mixture_preserving` (`Network.CardinalityBound`).

### The degraded DM-BC (pages C-2 to C-4; `Network.BCCardinality`)
* `I(X; Y₁ | U)` and `I(U; Y₂)` as means over `U`: `bcInfoXY₁U_kernel`, `bcInfoUY₂_kernel_eq`.
* `|𝒰| ≤ |𝒳| + 1`: `exists_degradedBC_card_input`.
* `|𝒰| ≤ |𝒴₂| + 1`: `exists_degradedBC_card_Y₂`.
* `|𝒰| ≤ |𝒴₁| + 1`, for a degraded channel: `exists_degradedBC_card_Y₁`.
* The three cases at once: `exists_degradedBC_card`.
* `|𝒰| ≤ min {|𝒳|, |𝒴₁|, |𝒴₂|} + 1`: `exists_degradedBC_card_min`.
* The region: `degradedBCRegionCardBits`, `degradedBCRegionBits_eq_card`,
  `isClosed_degradedBCRegionCardBits`.
* **Theorem 2 of Lecture 5 with the bound and no closure:** `bcCapacityRegionBits_eq_card`.

### The 3-receiver degraded DM-BC (pages C-5 to C-7; `Network.BC3Cardinality`)
* The law and the informations: `bc3Law`, `bc3InfoXV`, `bc3InfoVU`, `bc3InfoU`.
* The informations as means over the tree `p(u) p(v | u)`: `bc3InfoXV_tree`, `bc3InfoVU_tree`,
  `bc3InfoU_tree`.
* `|𝒰| ≤ |𝒳| + 2` and `|𝒱| ≤ (|𝒳| + 1) (|𝒳| + 2)`, with `V''' = (U', V'')`: `exists_bc3_card`.

### The time-sharing variable of the DM-MAC (page C-8; `Network.MACCardinality`)
* `|𝒬| ≤ 3`: `macRegionCard`, `macRegion_eq_card`.
* The region is closed: `isClosed_macRegionCard`.
* **The capacity region with `|𝒬| ≤ 3` and no closure:** `macCapacityRegion_eq_card`,
  `macCapacityRegionBits_eq_card`.

### The perturbation method (pages C-9 to C-11; `Network.MartonCardinality`)
* The objective in terms of entropies, page C-10: `martonSum`, `martonPhi`,
  `martonSum_eq_martonPhi`.
* A nonzero `φ` with `E(φ(U₁) | X = x) = 0` when `|𝒰₁| > |𝒳|`, page C-9: `exists_perturbation`.
* The objective along a perturbation: `mPert`, `entropy_mPert`, `entropy_mLaw₁_mPert`,
  `mLawY_mPert`, `martonPhi_le_mix`.
* A value of `U₁` can be removed: `exists_reduce₁`.
* By induction, for one and then both auxiliaries: `exists_card_le₁`, `exists_card_le`.
* **`|𝒰₁|, |𝒰₂| ≤ |𝒳|`:** `exists_marton_card`.
* **The maximum exists and is attained there:** `exists_isMax_martonSum`.

## Differences from the notes

* **Support lemma.** We state it for any connected compact set of parameters, since the DM-MAC needs
  the set of products `p(x₁ | q) p(x₂ | q)`, which is not the set of all pmfs. We assume that the
  functions `u ↦ g_j(p(· | u))` are measurable, which the notes leave implicit, and that `d ≥ 1`.
  The form for a finite mixture does not need compactness.
* **Degraded DM-BC.** The three cases are one theorem, for an output `T` that determines `Y₂`. We
  use the functions `I(X; Y₁ | U = u)` and `H(Y₂ | U = u)` in all three cases, instead of
  `H(Y₁ | U = u)` in the first. The bound `|𝒴₁| + 1` holds for a stochastically degraded channel.
* **3-receiver DM-BC.** The bound does not use degradedness. In the second step we use the functions
  `I(X; Y₁ | V' = v', U' = u')` and `H(Y₂ | V' = v', U' = u')`, so we do not need the chain of
  equalities on page C-7. We also skip the relabelling on page C-6, which the notes discard.
* **Perturbation method.** The notes take a maximizer and compute two derivatives at `ε = 0`. We
  show instead that the objective is convex along a perturbation: `H(Y₁)` and `H(Y₂)` are constant,
  `H(U₁, U₂) - H(U₁, Y₁)` is affine, and `H(U₂, Y₂)` is concave. So the objective at one of the two
  ends of the interval of `ε` is at least its value at `ε = 0`. This gives a stronger statement,
  with no maximizer: every `(p, x)` can be replaced by one on `|𝒰₁|, |𝒰₂| ≤ |𝒳|` with at least the
  same value. The existence of the maximum over all alphabets follows. The second part of the proof
  in the notes, `E(φ(U₁) | U₂, Y₂) = 0`, is not needed.
* **Capacity regions.** The statements without a closure are not in the appendix. They follow since
  a region with a bounded alphabet is closed.

## Not formalized

* The capacity region of the 3-receiver degraded DM-BC, which the notes state on page C-5: only the
  bound on the alphabets is proved.
* The cardinality bounds for the Marton inner bound with `U₀, U₁, U₂` on page C-8, which the notes
  cite; only the sum rate is treated, as in the notes.
* The bound `|𝒬| ≤ 2` of Lecture 4, which page C-8 mentions and this technique does not give.
* The other cardinality bounds of the notes, which this technique would give and which remain on the
  "Not formalized" lists of their lectures, such as `|𝒰| ≤ |𝒳| + 1` in Lecture 12.

## Issues in the notes

* **Page C-2.** `R(U, X) = R(U', X)` suggests that the law of `X` is kept. It is not in the bounds
  with `|𝒴₁| + 1` and `|𝒴₂| + 1` on page C-4, where only `p(y₁)` or `p(y₂)` is kept: the second
  argument should be `X'`.
* **Page C-3.** `∑_{u'} [p_{X|U'}(x | u')]` should have the factor `p(u')`, and `H(Y₁ | X₁)` should
  be `H(Y₁ | X)`.
* **Page C-4.** "the following `|𝒴₂|` continuous functions" should be `|𝒴₂| + 1`, as listed.
* **Page C-6.** `u' ∈ |𝒰'|` should be `u' ∈ 𝒰'`. In the list of functions of `p(x | v', u')`,
  `I(V'; Y₁ | U' = u')` is not a function of `p(x | v', u')` for one `v'`, and should be
  `H(Y₁ | V' = v', U' = u')`; also `V = v'` should be `V' = v'`.
* **Page C-9.** "Let `(U₁, U₂, X)` achieve the maximum": over all alphabets, the existence of a
  maximum is what is being proved. The argument applies to a fixed alphabet, and the conclusion then
  holds for all (`exists_isMax_martonSum`). Also, `φ` has to be nonzero on the support of `U₁`, so
  `|𝒰₁| ≥ |𝒳| + 1` has to count values of positive probability: otherwise the perturbation may leave
  `p` unchanged.
* **Page C-10.** `-∂²/∂ε² I(U₂'; Y₂')` should be `-∂²/∂ε² H(U₂', Y₂')`. The two differ, as `H(U₂')`
  changes with `ε`, and only the second is `E[E(φ(U₁) | U₂, Y₂)²]` at `ε = 0`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  C
-/

open MeasureTheory

@[expose] public noncomputable section

namespace InfoTheory

namespace ElGamalKim

/-- **The lemma on page C-1 of [elgamal2010].** Let `𝒳` be finite, let `U ∼ ν` be a random variable
on an arbitrary set, and let `p(x | u)` be conditional pmfs. For `d` continuous functions `g_j` on
the pmfs on `𝒳`, there are a pmf `w` on `d` points and pmfs `p'(x | u')` with
`∫ g_j(p(· | u)) dν(u) = ∑_{u'} g_j(p'(· | u')) w(u')` for all `j`. -/
theorem support_lemma {𝒳 Ω J : Type*} [Fintype 𝒳] [Nonempty 𝒳] [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] [Fintype J] [Nonempty J] {p : Ω → 𝒳 → ℝ} (hp : ∀ u, IsPMF (p u))
    {g : J → (𝒳 → ℝ) → ℝ} (hg : ∀ j, ContinuousOn (g j) {q | IsPMF q})
    (hm : ∀ j, AEStronglyMeasurable (fun u => g j (p u)) ν) :
    ∃ (w : Fin (Fintype.card J) → ℝ) (p' : Fin (Fintype.card J) → 𝒳 → ℝ), IsPMF w ∧
      (∀ i, IsPMF (p' i)) ∧ ∀ j, ∑ i, w i * g j (p' i) = ∫ u, g j (p u) ∂ν := by
  obtain ⟨w, z, hz, hw0, hw1, h⟩ := exists_fin_mixture_eq_integral isCompact_setOf_isPMF
    isConnected_setOf_isPMF hg hp hm
  exact ⟨w, z, ⟨hw0, hw1⟩, hz, h⟩

end ElGamalKim

end InfoTheory
