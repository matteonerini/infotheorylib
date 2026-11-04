/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCMoreCapable
public import InfoTheoryLib.Network.Gaussian

/-!
# El Gamal & Kim, Lecture 5: Degraded Broadcast Channels

This file indexes the formalization of Lecture 5 of [elgamal2010], with aliases named after its
numbered results (`theorem_5_1` for Theorem 1). Cover & Thomas give the setup in Section 15.6
(`Network.Broadcast`); the coding theorems, which they state without proof, are proved in the topic
files `Network.BCSuperposition`, `Network.BCDegraded` and `Network.BCCapacity`.

## Conventions

* **Rates.** Rates are in bits, with message sets `[1 : 2^{nRⱼ}] = {1, …, 2^⌈nRⱼ⌉}`, as in
  Lecture 3. Information quantities such as `bcInfoXY₁U` are in nats, and a bound in bits is the
  quantity divided by `log 2`.
* **Regions.** Rate regions are sets of pairs `R : ℝ × ℝ`, and are not intersected with
  `R₁, R₂ ≥ 0`. The capacity region is `bcCapacityRegionBits W`, for private messages (`R₀ = 0`).
* **Auxiliary random variable.** `U` takes values in `Fin k`, for some `k`, and `q : Fin k × 𝒳 → ℝ`
  is the pmf `p(u, x)`. As `k` is not bounded, Theorem 2 is stated up to closure.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Problem setup
* The DM-BC and a `(2^{nR₁}, 2^{nR₂}, n)` code: `BCCode`, `BCCode.errProb`, `bcMarg₁`, `bcMarg₂`
  (`Network.Broadcast`).
* Achievable rate pairs and the capacity region: `IsAchievableBCBits`, `bcCapacityRegionBits`
  (`Network.BCBits`), which is Cover and Thomas's `bcCapacityRegion` scaled by `1/log 2`:
  `bcCapacityRegionBits_eq_smul` (`Network.BCTimeSharing`).
* Lemma 1, the capacity region depends only on the conditional marginals: `isAchievableBCBits_iff`,
  `isAchievableBCBits_congr`, `bcCapacityRegionBits_eq_of_marg_eq` (`Network.BCTimeSharing`).

### Simple inner and outer bounds
* The time-division inner bound and the outer bound: `bcTimeDivisionBits`,
  `bcTimeDivisionBits_subset`, `bcOuterBoundBits`, `bcCapacityRegionBits_subset_bcOuterBoundBits`
  (`Network.BCBounds`).
* The symmetric DM-BC: `bcCapacityRegionBits_eq_bcTimeDivisionBits_of_marg_eq`. The DM-BC with
  separate channels: `bcCapacityRegionBits_eq_bcOuterBoundBits_of_separate`,
  `bcCapacityRegionBits_eq_of_separate`.
* Time sharing, the capacity region is convex: `BCCode.concat`, `BCCode.errProb_concat_le`,
  `convex_bcCapacityRegionBits`; lower rates: `mem_bcCapacityRegionBits_of_le`
  (`Network.BCTimeSharing`).

### Superposition coding inner bound
* Theorem 1: `superpositionRegionBits` (`Network.BCBits`), `superpositionRegionBits_subset`
  (`Network.BCSuperposition`), `closure_superpositionRegionBits_subset`, and with non-strict
  inequalities `superpositionClosedRegionBits`, `superpositionClosedRegionBits_subset`
  (`Network.BCCapacity`).
* The proof: the codebook `superpositionColumnLaw`, the typical triples `superpositionTypicalSet`
  (`Network.BCSuperpositionLaws`); the error events `sum_superposition_cloudAtyp_eq`,
  `sum_superposition_cloudWrong_le` (`E₂₁`, `E₂₂`), `sum_superposition_atyp_le`,
  `sum_superposition_satellite_le`, `sum_superposition_wrongCloud_le` (`E₁₁`, `E₁₂`, `E₁₃`);
  `exists_bcCode_superposition` (`Network.BCSuperposition`).
* The remarks on page 5-18, the receivers exchanged and the convex closure of the two bounds:
  `superpositionRegionBits₂`, `superpositionRegionBits₂_subset`,
  `closure_convexHull_union_superpositionRegionBits_subset`.

### Degraded broadcast channels
* Physical and stochastic degradedness: `IsPhysicallyDegraded`, `IsStochasticallyDegraded`
  (`Network.Broadcast`), and the transfer `IsStochasticallyDegraded.capacityRegionBits_eq`.
* Theorem 2: `degradedBCRegionBits`, `bcCapacityRegionBits_eq_closure_degradedBCRegionBits`
  (`Network.BCCapacity`). Achievability, `I(U; Y₁) ≥ I(U; Y₂)` makes the sum-rate bound inactive:
  `IsStochasticallyDegraded.bcInfoUY₂_le_bcInfoUY₁`, `degradedBCRegionBits_subset_closure`.
  The converse: `BCCode.log_le_sum_bcInfoXY₁U`, `BCCode.log_le_sum_bcInfoUY₂`,
  `IsAchievableBCBits.mem_closure_degradedBCRegionBits`,
  `IsAchievableBCBits.mem_closure_degradedBCRegionBits_of_stochasticallyDegraded`
  (`Network.BCDegraded`), with `Uᵢ = (M₂, Y₁^{i-1}, Y₂^{i-1})`, the last alternative in the remark
  on page 5-25, and the time-sharing variable `degradedBCTimeShare` (`Network.BCDegradedLaws`).

### Binary symmetric broadcast channel
* The channel and its degradedness, with `p₁ ∗ p̃₂ = p₂`: `bsbcBSC`, `bsbcDegraded`, `bsbcNoise₂`,
  `binConv_bsbcNoise₂`, `isStochasticallyDegraded_of_bsbc` (`Network.BinarySymmetricBC`).
* The Proposition: `bcCapacityRegionBits_bsbc` (`Network.BCCapacity`), from
  `bsbcSuperpositionRegion`, `degradedBCRegionBits_bsbc`, `isClosed_bsbcSuperpositionRegion`, with
  Mrs. Gerber's lemma in `bsbc_mrsGerber_le`.
* Time division versus superposition: `bsbcTimeDivisionRegion`, `bsbcTimeDivisionRegion_subset`,
  and strictly for `p₁ = 0`, `p₂ = 1/4`: `bsbcTimeDivisionRegion_ssubset`.

### AWGN broadcast channels
* The region of Theorem 3: `gaussianBCRegion` (`Network.Gaussian`), in the notes' form with the SNRs
  `Sⱼ = P/Nⱼ`: `gaussianBCRegion_eq_snr` (here), with `C(x) = gaussCap x`.
* Superposition beats sending to the worse receiver alone: `gaussianBC_sum_ge`.

### Less noisy and more capable broadcast channels
* The classes and their inclusions: `IsLessNoisy`, `IsMoreCapable`,
  `IsPhysicallyDegraded.isLessNoisy`, `IsStochasticallyDegraded.isLessNoisy`,
  `IsLessNoisy.isMoreCapable` (`Network.BCClasses`).
* Achievability for less noisy channels: `IsLessNoisy.degradedBCRegionBits_subset`
  (`Network.BCCapacity`).
* The capacity regions: `IsLessNoisy.bcCapacityRegionBits_eq_closure_degradedBCRegionBits`,
  `bcCapacityRegionBits_eq_closure_superpositionClosedRegionBits` (`Network.BCMoreCapable`), without
  the cardinality bounds on `U`.
* The converses, with `Uᵢ = (M₂, Y₁^{i-1}, Y₂_{i+1}ⁿ)` and `Vᵢ = (M₁, Y₁^{i-1}, Y₂_{i+1}ⁿ)`: the
  Csiszár sum identity in telescoped form `condEntropy_sub_condEntropy_eq_sum_moreCapableAux`,
  `BCCode.log_add_log_le_sum_bcInfoXY₁U_add_bcInfoUY₂`, `BCCode.log_add_log_le_sum_bcInfoXY₁`
  (`Network.BCMoreCapableLaws`), `IsMoreCapable.bcInfoXY₂U_le_bcInfoXY₁U`.
* The alternative regions: `moreCapableAltRegionBits`, `lessNoisyAltRegionBits`,
  `mem_superpositionClosedRegionBits_of_mem_moreCapableAltRegionBits`,
  `IsLessNoisy.mem_degradedBCRegionBits_of_mem_lessNoisyAltRegionBits`.
* The BSC and the BEC, with the exact thresholds: `bscBecBC`, `bscBecBC_case₁`, `bscBecBC_case₂`,
  `bscBecBC_case₃`, `bscBecBC_case₄`, `isStochasticallyDegraded_bcReceiverSwap_bscBecBC_iff`,
  `isLessNoisy_bcReceiverSwap_bscBecBC_iff`, `isMoreCapable_bcReceiverSwap_bscBecBC_iff`
  (`Network.BCClasses`).

## Not formalized

* The common message: the code with `M₀`, the triples `(R₀, R₁, R₂)`, the common-message capacity
  `C₀`, the degraded message sets, and the extension on page 5-46.
* The cardinality bounds on `U` (Appendix C): the regions use an unbounded `Fin k`, so Theorem 2 is
  stated with a closure.
* Theorem 3 as a coding theorem for the AWGN-BC. Its converse needs the conditional vector entropy
  power inequality, which the library does not have.
* The explicit `U ⊕ V` scheme for the BS-BC and successive cancellation decoding; the region is
  obtained from Theorem 1 with a DSBS input.
* The BC with more than two receivers, and the remark on feedback.

## Issues in the notes

* **Page 5-18.** The remark that `R₂ < I(X; Y₁) - δ(ε)` "is already satisfied" follows from
  `R₁ + R₂ < I(X; Y₁) - δ(ε)` only for `R₁ ≥ 0`, which the notes assume implicitly. Our regions are
  not intersected with `R₁, R₂ ≥ 0`.
* **Page 5-21.** The intermediate crossover probability is printed as `p̃₂ = (p₂ − p₁)(1 − 2p₁)`.
  It should be `(p₂ − p₁)/(1 − 2p₁)`: `bsbc_not_forall_binConv_mul`, `binConv_bsbcNoise₂`.
* **Page 5-39.** Case 4 of the BSC and the BEC, "`H(p) < ε ≤ 1`: none of the three classes", fails
  at `ε = 1` and at `p = 0`, where `Y₂` is a degraded version of `Y₁`:
  `isStochasticallyDegraded_bscBecBC_of_eps_eq_one`,
  `isStochasticallyDegraded_bscBecBC_of_p_eq_zero`. It holds for `H(p) < ε < 1` and `p > 0`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Set

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## AWGN broadcast channels -/

/-- **Theorem 3 (Lecture 5)**, the region only. With the received SNRs `Sⱼ = P/Nⱼ`, the region
`R₁ ≤ C(αP/N₁)`, `R₂ ≤ C(ᾱP/(αP + N₂))` of Cover and Thomas is the notes' region
`R₁ ≤ C(αS₁)`, `R₂ ≤ C(ᾱS₂/(αS₂ + 1))`. -/
theorem gaussianBCRegion_eq_snr {P N₁ N₂ : ℝ} (hP : 0 ≤ P) (hN₂ : 0 < N₂) :
    gaussianBCRegion P N₁ N₂ = {R | ∃ a ∈ Icc (0 : ℝ) 1, R.1 ≤ gaussCap (a * (P / N₁)) ∧
      R.2 ≤ gaussCap ((1 - a) * (P / N₂) / (a * (P / N₂) + 1))} := by
  ext R
  refine exists_congr fun a => and_congr_right fun ha => ?_
  have h₁ : a * P / N₁ = a * (P / N₁) := by ring
  have hpos : 0 < a * P + N₂ := by
    have := mul_nonneg ha.1 hP
    linarith
  have h₂ : (1 - a) * P / (a * P + N₂) = (1 - a) * (P / N₂) / (a * (P / N₂) + 1) := by
    have : a * (P / N₂) + 1 = (a * P + N₂) / N₂ := by field_simp
    rw [this]
    field_simp
  rw [h₁, h₂]

/-! ## Index of numbered and named results -/

/-- **Lemma 1 (Lecture 5).** The capacity region depends only on the conditional marginals. -/
alias lemma_5_1 := bcCapacityRegionBits_eq_of_marg_eq

/-- **Theorem 1 (Lecture 5).** The superposition coding inner bound. -/
alias theorem_5_1 := superpositionRegionBits_subset

/-- **Theorem 2 (Lecture 5).** The capacity region of the degraded DM-BC. -/
alias theorem_5_2 := bcCapacityRegionBits_eq_closure_degradedBCRegionBits

/-- **The Proposition (Lecture 5).** The capacity region of the binary symmetric BC. -/
alias binary_symmetric_bc_capacity_region := bcCapacityRegionBits_bsbc

/-- **Lecture 5, page 5-38.** The capacity region of the less noisy DM-BC. -/
alias less_noisy_bc_capacity_region :=
  IsLessNoisy.bcCapacityRegionBits_eq_closure_degradedBCRegionBits

/-- **Lecture 5, page 5-39.** The capacity region of the more capable DM-BC. -/
alias more_capable_bc_capacity_region :=
  bcCapacityRegionBits_eq_closure_superpositionClosedRegionBits

end InfoTheory.ElGamalKim
