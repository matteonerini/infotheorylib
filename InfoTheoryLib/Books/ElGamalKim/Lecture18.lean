/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture18Examples
public import InfoTheoryLib.GaussianChannel.SchalkwijkKailath
public import InfoTheoryLib.Network.BCFeedbackExample
public import InfoTheoryLib.Network.DirectedInfo
public import InfoTheoryLib.Network.MACFeedbackGaussian
public import InfoTheoryLib.Network.RelayFeedback
public import InfoTheoryLib.Network.TwoWayMultiLetter

/-!
# El Gamal & Kim, Lecture 18: Interactive Communication

This file indexes the formalization of Lecture 18 of [elgamal2010]. We prove the feedback capacity
of the DMC; the Schalkwijk–Kailath scheme; the cooperative outer bound and the Cover–Leung inner
bound for the multiple access channel with feedback, with the binary erasure example, where feedback
strictly enlarges the region; the capacity region of the physically degraded broadcast channel with
feedback, and Dueck's example; the capacity of the relay channel with feedback; and, for the two-way
channel, Shannon's inner and outer bounds, the decoupled channel, the binary multiplier channel, the
dependence balance bound, directed information and the multi-letter capacity region.

## Conventions

* **Rates.** Rates are in bits with `2 ^ ⌈n R⌉` messages, and informations are in nats, so that a
  condition is written as `R * log 2 < I`.
* **Laws with feedback.** All the codes are feedback laws, `fbLaw ν W enc n`, of a message and the
  outputs.
* **Errors of a two-way code.** `TWCCode.errProb` is the sum of the errors of the two nodes, which
  tends to zero if and only if the probability that a node errs does.
* **Common output.** The two-way channel with common output `p(y | x₁, x₂)` is `commonTW`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The DMC with feedback (pages 18-3 to 18-18)
* **Theorem 1**: `fbCapacity_eq_capacity` (`ChannelCoding.Converse`). Here: `theorem_18_1`.
* **Schalkwijk–Kailath** (`GaussianChannel.SchalkwijkKailath`): the coefficients `skV`, `skG`,
  `skA`; the code `AddFBCode`, `skCode`; the power constraint `skCode_power_le`; the Chebyshev bound
  for any noise of mean zero and unit variance `skCode_err_le`, and the doubly exponential bound for
  Gaussian noise `skCode_err_gaussian_le`; all the rates below the capacity
  `isAchievableAddFB_of_lt`.

### The multiple access channel with feedback (pages 18-19 to 18-38)
* The code, the capacity region and the **cooperative outer bound**: `MACFBCode`,
  `IsAchievableMACFB`, `macfbCapacityRegion`, `macCoopRegion`,
  `IsAchievableMACFB.mem_closure_macCoopRegion` (`Network.MACFeedback`).
* **Theorem 2, Cover–Leung**: the block `CLBlock`, the random coding bound `sum_clCode_err_le`,
  `exists_clBlock_le`, `eventually_clBlock` (`Network.MACFeedbackBlock`); block Markov coding and
  backward decoding, by the reduction to the relay channel, `clFakeW`, `CLBlock.toRelay`,
  `MACFBCode.errProb_ofRC`, `CLBlock.exists_code_le`; **`isAchievableMACFB_coverLeung`**
  (`Network.MACFeedbackMarkov`). Here: `theorem_18_2`.
* **Binary erasure MAC, page 18-24**: `isAchievableMACFB_binaryErasureMAC`,
  `macCapacityRegionBits_binaryErasureMAC_sum_le`, **`feedback_enlarges_binaryErasureMAC`**
  (`Books.ElGamalKim.Lecture18Examples`).
* **The AWGN formulas, pages 18-28 to 18-34** (`Network.MACFeedbackGaussian`): the regions
  `macFBGaussRegion`, `clGaussRegion`, the inclusion `clGaussRegion_subset`, and the correlation and
  the identity `exists_rhoStar`.

### The broadcast channel with feedback (pages 18-39 to 18-42)
* **Theorem 4**: `BCFBCode`, `IsAchievableBCFB`, `bcfbCapacityRegion`,
  `IsAchievableBCFB.mem_closure_degradedBCRegionBits`, **`bcfbCapacityRegion_eq`**
  (`Network.BCFeedback`). Here: `theorem_18_4`.
* **Dueck's example** (`Network.BCFeedbackExample`): `dueckW`, `isAchievableBCFB_dueck`,
  `one_one_mem_bcfbCapacityRegion`, without feedback `dueck_mul_le`,
  `bcCapacityRegionBits_dueck_subset`, `subset_bcCapacityRegionBits_dueck`.

### The relay channel with feedback (pages 18-43 and 18-44)
* **Theorem 5**: `RCFBCode`, `IsAchievableRCFB`, `rcfbCapacity` (`Network.RelayCode`),
  `rcFBChannel`, `isAchievableRCFB_of_lt`, **`rcfbCapacity_eq`** (`Network.RelayFeedback`). Here:
  `theorem_18_5`.

### The two-way channel (pages 18-45 to 18-50)
* The code: `TWCCode`, `IsAchievableTWC`, `twcCapacityRegion` (`Network.TwoWayCode`).
* **Shannon's outer bound**: `twcOuterRegion`, `IsAchievableTWC.mem_closure_twcOuterRegion`.
* **Shannon's inner bound**: `twLaw`, `exists_twCode_le`, **`isAchievableTWC_of_lt`**
  (`Network.TwoWayInner`), and for product inputs `isAchievableTWC_of_lt_prod`
  (`Network.TwoWayExamples`).
* **Decoupled channels**: `decoupledTW`, `twcCapacityRegion_decoupled`.
* **The binary multiplier channel**: `bmcV`, the inner bound `isAchievableTWC_bmc`, the outer bound
  `mem_twcOuterRegion_bmc_iff`, and the symmetric rates `isAchievableTWC_bmc_symm`,
  `three_fifths_mem_twcCapacityRegion_bmc`.

### Dependence balance (pages 18-51 and 18-52)
* **Theorem 6**: `condMutualInfo_interaction`, `TWCCode.depBalance_step`, `TWCCode.depBalance_sum`,
  `mix_condMutualInfo`, `twcDepRegion`, **`IsAchievableTWC.mem_closure_twcDepRegion`**
  (`Network.DependenceBalance`). Here: `theorem_18_6`.

### Directed information (pages 18-53 to 18-60)
* **Directed information** (`Network.DirectedInfo`): `directedInfo`, `causalDirectedInfo`,
  **Massey's inequality** `directedInfo_le_mutualInfo`, and `condMutualInfo_markov_step`, which
  replaces the "check!" on page 18-57.
* **Theorem 7**: `Strat`, `stratW`, `twcMultiRegion`, `TWCCode.exists_strat`,
  `IsAchievableTWC.mem_closure_iUnion_twcMultiRegion` (`Network.TwoWayStrategy`);
  `blockCode`, `isAchievableTWC_of_multi`, **`twcCapacityRegion_eq_closure_iUnion`**
  (`Network.TwoWayMultiLetter`); and the rates as directed informations,
  **`cInfo_stratW_eq_causalDirectedInfo`**. Here: `theorem_18_7`.

## Differences from the notes

* **Schalkwijk–Kailath.** We define the scheme by an explicit linear recursion with explicit
  coefficients, not by MMSE estimates, and the message point lies in `[-√P, √P]`. The power is `P`
  in each use, also in the first one, so that the total power is at most `(n + 1) P` rather than
  `1 + n P`. The error bounds come from the second moment and from the moment generating function of
  the linear combination of the noises, not from mutual information.
* **Cover–Leung.** The notes use one codebook per block and induction. We use one code for all the
  blocks and bound the error by the genie run. The rates are nonnegative. We prove the theorem
  through an auxiliary relay channel, which reuses `RelayBlock.markov_errProb_le`.
* **Binary erasure MAC.** We use `Vⱼ ∼ Bern(1/4)`, for which the entropies are explicit, and prove
  the symmetric rate `25 / 32`. The notes use `Vⱼ ∼ Bern(0.2377)` and state `0.7911`.
* **Binary multiplier channel.** We prove the symmetric rate `3 / 5` from `p₁ = p₂ = 3 / 4`. The
  notes state the numbers `0.6170`, `0.6942`, `0.6463`, `0.6191` and `0.6306`, which we do not
  prove.
* **Dueck's example.** The bound without feedback is by counting, and it gives a strong converse.
* **Outer bounds.** The cooperative, Shannon and dependence balance outer bounds are stated with a
  closure: a code gives `(R₁ - εₙ, R₂ - εₙ)` in the region, and we do not prove that the region is
  closed.
* **Theorem 6.** We take `U = (Q, Y^{Q-1})` with an arbitrary finite alphabet: the bound `|U| ≤ 3`
  is not proved.
* **Theorem 7.** The regions use independent random strategies of length `k` in place of the
  causally conditional laws `p(x₁ᵏ || yᵏ⁻¹) p(x₂ᵏ || yᵏ⁻¹)` of the notes, and the theorem has a
  closure. That each such law comes from a random strategy is the functional representation of a
  causally conditional law, which we do not prove. We prove achievability by Shannon's inner bound
  on the super-channel of the strategies, not by multiplexing over the states.
  `cInfo_stratW_eq_causalDirectedInfo` identifies the rates with the directed informations.

## Not formalized

* Horstein coding (the notes give an outline) and Weldon's block feedback scheme for the BSC.
* The coding theorems for the AWGN multiple access channel with feedback (Theorem 3), including the
  extension of Schalkwijk–Kailath: we prove the formulas only.
* The variant of the dependence balance bound for the multiple access channel with feedback on page
  18-52, and the optimality of the Cover–Leung region for the class of page 18-22.
* The simple retransmission schemes for the binary erasure MAC on pages 18-23 and 18-24, whose rates
  `2/3`, `3/4` and `0.7602` are below `25 / 32`.
* The bounds on the BMC that rely on numerical optimization, and the example of pages 18-55 and
  18-56.
* The broadcast channel schemes with feedback for the AWGN channel.
* The analogues of Theorem 7 for the general two-way channel and for the MAC with feedback.

## Issues in the notes

* Page 18-11: the Chebyshev bound has `P{|θ - θ̂ₙ| > 2^{-2nR}}`; the threshold is `2^{-nR}`, as on
  page 18-9, and this is what gives the stated `2^{-2n(C(P) - R)}`.
* Page 18-18: the rate has `(H(p) + δ(ε))^{k₁} · k₂`, while the previous bullet uses the power
  `k₁ - 1`; and the last formula has `δ(δ)` for `δ(ε)`.
* Page 18-55: `𝒞 = ⋃ₖ 𝒞ₖ` needs a closure.
* Page 18-56: the reference is the unresolved `[?]`.
* Page 18-57: `Y^{i-i}` should be `Y^{i-1}`.
* Page 18-58 writes `p(x₂ⱼ | x₁^{j-1}, y^{j-1})`, and page 18-59 writes
  `S₂ⱼ = X₁^{j-1} × Y^{j-1}`, where the index of `X` should be `2`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

section Aliases

variable {X X₁ X₂ Y Y₁ Y₂ U α β : Type*} [Fintype X] [Fintype X₁] [Fintype X₂] [Fintype Y]
  [Fintype Y₁] [Fintype Y₂] [Fintype U] [Fintype α] [Fintype β]

/-- **Theorem 1, page 18-3.** Feedback does not increase the capacity of a DMC. -/
theorem theorem_18_1 [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) :
    fbCapacity W = capacity W :=
  fbCapacity_eq_capacity hW

/-- **Theorem 2, the Cover–Leung inner bound, page 18-22.** -/
theorem theorem_18_2 [Nonempty X₁] [Nonempty X₂] [Nonempty Y] {W : X₁ × X₂ → Y → ℝ} {pu : U → ℝ}
    {A : U → X₁ → ℝ} {B : U → X₂ → ℝ} (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B)
    (hW : IsChannel W) {R₁ R₂ : ℝ} (h₁0 : 0 ≤ R₁) (h₂0 : 0 ≤ R₂)
    (h₁ : R₁ * log 2 < I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ; clLaw pu A B W])
    (h₂ : R₂ * log 2 < I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ; clLaw pu A B W])
    (h₃ : (R₁ + R₂) * log 2 < I[fun z => z.1.2 : Prod.snd ; clLaw pu A B W]) :
    IsAchievableMACFB W R₁ R₂ :=
  isAchievableMACFB_coverLeung hu hA hB hW h₁0 h₂0 h₁ h₂ h₃

/-- **Theorem 4, page 18-39.** Feedback does not increase the capacity region of a physically
degraded broadcast channel. -/
theorem theorem_18_4 {α' : Type*} [Finite α'] [Nonempty α'] {W : α' → Y₁ × Y₂ → ℝ}
    (hW : IsChannel W) (hd : IsPhysicallyDegraded W) : bcfbCapacityRegion W = bcCapacityRegionBits
    W :=
  bcfbCapacityRegion_eq hW hd

/-- **Theorem 5, page 18-44.** The capacity of the relay channel with feedback. -/
theorem theorem_18_5 [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) : rcfbCapacity W = rcCutsetBound W / log 2 :=
  rcfbCapacity_eq hW

/-- **Theorem 6, the dependence balance outer bound, page 18-51.** -/
theorem theorem_18_6 {X₁' X₂' : Type*} {Y' : Type*} [Fintype X₁'] [Fintype X₂'] [Fintype Y']
    [Nonempty Y'] {V : X₁' × X₂' → Y' → ℝ} (hV : IsChannel V) {R₁ R₂ : ℝ}
    (h : IsAchievableTWC (commonTW V) R₁ R₂) : (R₁, R₂) ∈ closure (twcDepRegion V) :=
  IsAchievableTWC.mem_closure_twcDepRegion hV h

/-- **Theorem 7, the multi-letter capacity region, page 18-55.** -/
theorem theorem_18_7 [Nonempty X₁] [Nonempty X₂] [Nonempty Y] {V : X₁ × X₂ → Y → ℝ}
    (hV : IsChannel V) :
    twcCapacityRegion (commonTW V) = closure (⋃ k : ℕ, ⋃ _ : 0 < k, twcMultiRegion V k) :=
  twcCapacityRegion_eq_closure_iUnion hV

end Aliases

end InfoTheory.ElGamalKim
