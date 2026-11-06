/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter7
public import InfoTheoryLib.GaussianChannel.AWGN
public import InfoTheoryLib.Network.Gaussian
public import InfoTheoryLib.Network.MACMultiLetter
public import InfoTheoryLib.RelativeEntropy.Pinsker
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# El Gamal & Kim, Lecture 4: Multiple Access Channels

This file indexes the formalization of Lecture 4 of [elgamal2010] and contains the lecture's worked
examples, with aliases named after its numbered results (`theorem_4_1` for Theorem 1). Much of the
theory of the two-sender DM-MAC is also in Chapter 15 of Cover & Thomas
(`Books.CoverThomas.Chapter15`), whose proofs in nats are reused here: the topic files
`Network.MACBits`, `Network.MACBounds` and `Network.MACMultiLetter` restate the results with the
notes' definitions and add the ones that Cover & Thomas do not state.

## Conventions

* **Rates.** Rates are in bits, with message sets `[1 : 2^{nRⱼ}] = {1, …, 2^⌈nRⱼ⌉}`, as in
  Lecture 3; information quantities such as `macInfo₁` are in nats, and a bound in bits is the
  quantity divided by `log 2`.
* **Regions.** Rate regions are sets of pairs `R : ℝ × ℝ`; they are not intersected with
  `R₁, R₂ ≥ 0`, as negative rates are trivially achievable (one message). The capacity region is
  `macCapacityRegionBits W`, the closure of the achievable rate pairs.
* **Inputs.** The two senders' input distributions `p(x₁) p(x₂)` are pmfs `p₁`, `p₂`, and
  `macJoint p₁ p₂ W` is the law of `((X₁, X₂), Y)`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Problem setup
* The DM-MAC `(𝒳₁ × 𝒳₂, p(y|x₁, x₂), 𝒴)`: a channel `W : 𝒳₁ × 𝒳₂ → 𝒴 → ℝ` with `IsChannel W`.
* A `(2^{nR₁}, 2^{nR₂}, n)` code and `P_e^(n)`: `MACCode`, `MACCode.avgErrProb`
  (`Network.MACCode`).
* Achievable rate pairs and the capacity region: `IsAchievableMACBits`, `macCapacityRegionBits`
  (`Network.MACBits`), which is Cover and Thomas's `macCapacityRegion` scaled by `1/log 2`:
  `macCapacityRegionBits_eq_smul`.

### Simple inner and outer bounds
* `C₁ = max_{x₂, p(x₁)} I(X₁; Y | X₂ = x₂)`, `C₂` and `C₁₂ = max_{p(x₁) p(x₂)} I(X₁, X₂; Y)`:
  `macC₁`, `macC₂`, `macC₁₂` (`Network.MACBounds`), with `macInfo₁_eq_sum`, `macInfo₂_eq_sum`.
* The time-division inner bound and the outer bound: `macTimeDivisionBits`,
  `macTimeDivisionBits_subset`, `macOuterBoundBits`,
  `macCapacityRegionBits_subset_macOuterBoundBits`.
* The binary multiplier DM-MAC, where the bounds coincide: `binaryMultiplierMAC`,
  `macCapacityRegionBits_binaryMultiplierMAC` (here).
* The binary erasure DM-MAC, where they do not: `binaryErasureMAC`,
  `pentagon_subset_macCapacityRegionBits_binaryErasureMAC`,
  `macCapacityRegionBits_binaryErasureMAC_subset`, `binaryErasureMAC_not_timeDivision` (here).
* Its capacity region, the pentagon with `R₁ + R₂ ≤ 3/2`: `macInfo₁₂_binaryErasureMAC_le`,
  `macCapacityRegionBits_binaryErasureMAC` (here).

### Multi-letter characterization
* Theorem 1: `macExt`, `macChannel₁`, `macChannel₂`, `macMultiLetterRegionBits`,
  `macCapacityRegionBits_eq_closure_iUnion` (`Network.MACMultiLetter`), with the converse
  `MACCode.log_le_mutualInfoOf₁`, `MACCode.log_le_mutualInfoOf₂`,
  `IsAchievableMAC.mem_closure_iUnion_macMultiLetterRegion`.

### Time sharing
* The time-sharing code, two codes used one after the other: `MACCode.append`,
  `MACCode.avgErrProb_append_le`, `convex_macSlackSet` (`Network.MACCode`).
* The capacity region is convex: `convex_macCapacityRegionBits` (`Network.MACBits`).
* Lowering the rates stays in the region: `mem_macCapacityRegionBits_of_le`
  (`Network.MACBounds`).

### Single-letter characterization
* The pentagon `R(X₁, X₂)` and `max {I(X₁; Y | X₂), I(X₂; Y | X₁)} ≤ I(X₁, X₂; Y) ≤
  I(X₁; Y | X₂) + I(X₂; Y | X₁)`: `macPentagonBits`, `macPentagonsBits` (`Network.MACBits`),
  `macInfo₁_le_macInfo₁₂`, `macInfo₂_le_macInfo₁₂`, `macInfo₁₂_le_add` (`Network.MACRegion`).
* Theorem 2 (Ahlswede, Liao): `macCapacityRegionBits_eq` (`Network.MACBits`).
* Achievability, with simultaneous joint typicality decoding: `isAchievableMAC_of_mem_macRateRegion`
  (`Network.MACAchievability`), Cover and Thomas's proof with weak typicality.
* The converse, with the time-sharing random variable `Q` uniform on the `n` positions:
  `IsAchievableMAC.mem_closure_macRegion` (`Network.MACConverse`), and `𝒞 = 𝒞'` for the region
  `𝒞'` of `p(q) p(x₁|q) p(x₂|q)`: `macRegion`, `macCapacityRegion_eq_closure_macRegion`
  (`Network.MACCapacity`), in nats and without a bound on `|Q|`.
* The sum capacity `max_{p(x₁) p(x₂)} I(X₁, X₂; Y)`: `sSup_sum_macCapacityRegionBits`
  (`Network.MACBounds`).

### AWGN multiple access channel
* The function `C(x) = ½ log(1 + x)` is Cover and Thomas's `gaussCap` (`Network.Gaussian`):
  `gaussCap_eq_gaussianCapacityFun` (here).
* The region of Theorem 4, `R₁ ≤ C(S₁)`, `R₂ ≤ C(S₂)`, `R₁ + R₂ ≤ C(S₁ + S₂)`: `gaussianMACRegion`,
  `mem_gaussianMACRegion_two` (`Network.Gaussian`), with noise power `1` and `Sⱼ = gⱼ² P`.
* Successive cancellation, the corner points `C(S₁) + C(S₂/(1 + S₁)) = C(S₁ + S₂)`:
  `gaussCap_add_gaussCap`.
* TDMA with power control reaches the sum capacity at `α = S₁/(S₁ + S₂)`: `tdma_eq`, and beats
  treating the other codeword as noise: `gaussCap_noise_le_tdma`.
* More than two senders with equal SNRs: `gaussianMACRegion`, `const_mem_gaussianMACRegion`; the
  sum capacity `C(kS) → ∞` and the rate per user `C(kS)/k → 0`: `tendsto_gaussCap_mul_atTop`,
  `tendsto_gaussCap_mul_div_atTop`.

## Not formalized

* Theorem 3, the cardinality bound `|Q| ≤ 2`. Appendix C gives `|Q| ≤ 3`, and then no closure is
  needed: `macCapacityRegion_eq_card` (`Network.MACCardinality`). The capacity region is also
  formalized as the closure of the region with an unbounded time-sharing variable
  (`macCapacityRegion_eq_closure_macRegion`); Cover and Thomas's planar Carathéodory theorem is
  `exists_convex_combination_le_three` (`Network.MACCapacity`).
* Successive cancellation decoding and coded time sharing as achievability proofs: the region is
  achieved by simultaneous decoding and time sharing.
* The remark on the maximal probability of error, the push-to-talk MAC, and the computational
  remark on the sum capacity.
* Theorem 4 as a coding theorem for the AWGN-MAC, the computation `I(X₁; Y | X₂) = C(S₁)` for
  Gaussian inputs, and the TDMA scheme without power control.
* Theorem 5, the `k`-sender DM-MAC, and the operational `k`-sender AWGN-MAC.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 4
-/

open Real Finset Filter Topology Set

open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Examples -/

/-- A deterministic multiple access channel `Y = f(X₁, X₂)`. -/
def detMAC {α₁ α₂ β : Type*} [DecidableEq β] (f : α₁ × α₂ → β) : α₁ × α₂ → β → ℝ :=
  fun x y => if y = f x then 1 else 0

lemma detMAC_isChannel {α₁ α₂ β : Type*} [Fintype β] [DecidableEq β] (f : α₁ × α₂ → β) :
    IsChannel (detMAC f) := fun x =>
  ⟨fun y => by unfold detMAC; split_ifs <;> norm_num, by simp [detMAC]⟩

/-- **Example (Lecture 4): binary multiplier MAC.** `X₁, X₂` and `Y = X₁ · X₂` are binary. -/
def binaryMultiplierMAC : Bool × Bool → Bool → ℝ := detMAC fun x => x.1 && x.2

/-- With one input fixed to `1`, the binary multiplier MAC is the noiseless binary channel. -/
lemma binaryMultiplierMAC_true₂ :
    (fun a => binaryMultiplierMAC (a, true)) = CoverThomas.noiselessChannel := by
  funext a y
  simp [binaryMultiplierMAC, detMAC, CoverThomas.noiselessChannel, eq_comm]

lemma binaryMultiplierMAC_true₁ :
    (fun b => binaryMultiplierMAC (true, b)) = CoverThomas.noiselessChannel := by
  funext b y
  simp [binaryMultiplierMAC, detMAC, CoverThomas.noiselessChannel, eq_comm]

/-- **Example (Lecture 4): binary multiplier MAC.** The time-division inner bound and the outer
bound coincide: the capacity region is `R₁ + R₂ ≤ 1` (with `R₁, R₂ ≤ 1`), in bits. -/
theorem macCapacityRegionBits_binaryMultiplierMAC :
    macCapacityRegionBits binaryMultiplierMAC = {R | R.1 ≤ 1 ∧ R.2 ≤ 1 ∧ R.1 + R.2 ≤ 1} := by
  have hl := log_pos one_lt_two
  have hW : IsChannel binaryMultiplierMAC := detMAC_isChannel _
  -- `C₁, C₂ ≥ 1` bit.
  have hC₁ : 1 ≤ macC₁ binaryMultiplierMAC / log 2 := by
    rw [le_div_iff₀ hl, one_mul]
    have h := le_ciSup (f := fun b => capacity fun a => binaryMultiplierMAC (a, b))
      (Set.finite_range _).bddAbove true
    simp only [binaryMultiplierMAC_true₂, CoverThomas.capacity_noiselessChannel.1] at h
    exact h
  have hC₂ : 1 ≤ macC₂ binaryMultiplierMAC / log 2 := by
    rw [le_div_iff₀ hl, one_mul]
    have h := le_ciSup (f := fun a => capacity fun b => binaryMultiplierMAC (a, b))
      (Set.finite_range _).bddAbove true
    simp only [binaryMultiplierMAC_true₁, CoverThomas.capacity_noiselessChannel.1] at h
    exact h
  refine le_antisymm ?_ ?_
  · -- The outer bound: every rate is at most `log |𝒴| = 1` bit.
    intro R hR
    rw [macCapacityRegionBits_eq_smul hW] at hR
    obtain ⟨S, hS, rfl⟩ := hR
    obtain ⟨h1, h2, h3⟩ := le_log_card_of_mem_macCapacityRegion hW hS
    simp only [Fintype.card_bool, Nat.cast_ofNat] at h1 h2 h3
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← mul_add,
      inv_mul_le_iff₀ hl, mul_one]
    exact ⟨h1, h2, h3⟩
  · -- The time-division inner bound.
    rintro R ⟨h1, h2, h3⟩
    refine macTimeDivisionBits_subset hW ?_
    rcases le_or_gt R.1 0 with h0 | h0
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using h0, by nlinarith⟩
    · exact ⟨R.1, ⟨h0.le, h1⟩, by nlinarith, by nlinarith⟩

/-- The output `X₁ + X₂ ∈ {0, 1, 2}` of the binary erasure MAC. -/
def binaryErasureMACOut (x : Bool × Bool) : Fin 3 :=
  if x.1 && x.2 then 2 else if x.1 || x.2 then 1 else 0

/-- **Example (Lecture 4): binary erasure MAC.** `X₁, X₂` are binary and `Y = X₁ + X₂` is
ternary. -/
def binaryErasureMAC : Bool × Bool → Fin 3 → ℝ := detMAC binaryErasureMACOut

lemma binaryErasureMAC_isChannel : IsChannel binaryErasureMAC := detMAC_isChannel _

/-- Given one input, the other one is sent noiselessly: `I(X₁; Y | X₂ = x₂) = 1` bit for
`X₁ ∼ Bern(1/2)`. -/
lemma mutualInfoOf_binaryErasureMAC₁ (b : Bool) :
    mutualInfoOf (uniformPMF Bool) (fun a => binaryErasureMAC (a, b)) = log 2 := by
  unfold binaryErasureMAC
  rw [mutualInfoOf_eq uniformPMF_isPMF (fun a => detMAC_isChannel binaryErasureMACOut (a, b))]
  cases b <;> simp [entropy_eq_sum_negMulLog, Fin.sum_univ_three, outDist, detMAC,
    binaryErasureMACOut, uniformPMF, negMulLog] <;> ring_nf

lemma mutualInfoOf_binaryErasureMAC₂ (a : Bool) :
    mutualInfoOf (uniformPMF Bool) (fun b => binaryErasureMAC (a, b)) = log 2 := by
  unfold binaryErasureMAC
  rw [mutualInfoOf_eq uniformPMF_isPMF (fun b => detMAC_isChannel binaryErasureMACOut (a, b))]
  cases a <;> simp [entropy_eq_sum_negMulLog, Fin.sum_univ_three, outDist, detMAC,
    binaryErasureMACOut, uniformPMF, negMulLog] <;> ring_nf

/-- **Example (Lecture 4): binary erasure MAC.** With `X₁, X₂ ∼ Bern(1/2)`,
`I(X₁, X₂; Y) = H(Y) = 3/2` bits. -/
lemma macInfo₁₂_binaryErasureMAC :
    macInfo₁₂ (uniformPMF Bool) (uniformPMF Bool) binaryErasureMAC = 3 / 2 * log 2 := by
  change mutualInfoOf (prodDist (uniformPMF Bool) (uniformPMF Bool))
    (detMAC binaryErasureMACOut) = _
  rw [mutualInfoOf_eq (uniformPMF_isPMF.prodDist uniformPMF_isPMF)
    (detMAC_isChannel binaryErasureMACOut)]
  simp [entropy_eq_sum_negMulLog, Fin.sum_univ_three, outDist, detMAC, binaryErasureMACOut,
    uniformPMF, negMulLog, prodDist, Fintype.sum_prod_type]
  ring_nf
  rw [show (1 : ℝ) / 4 = (2 ^ 2)⁻¹ by norm_num, show (1 : ℝ) / 2 = 2⁻¹ by norm_num, log_inv,
    log_inv, log_pow]
  push_cast
  ring

/-- **Example (Lecture 4): binary erasure MAC.** The pentagon `R₁ ≤ 1`, `R₂ ≤ 1`,
`R₁ + R₂ ≤ 3/2` (in bits) of the inputs `X₁, X₂ ∼ Bern(1/2)` is in the capacity region. -/
theorem pentagon_subset_macCapacityRegionBits_binaryErasureMAC :
    {R : ℝ × ℝ | R.1 ≤ 1 ∧ R.2 ≤ 1 ∧ R.1 + R.2 ≤ 3 / 2} ⊆
      macCapacityRegionBits binaryErasureMAC := by
  have hl := log_pos one_lt_two
  have hp := uniformPMF_isPMF (α := Bool)
  have h₁ : macInfo₁ (uniformPMF Bool) (uniformPMF Bool) binaryErasureMAC = log 2 := by
    rw [macInfo₁_eq_sum hp hp binaryErasureMAC_isChannel]
    simp [mutualInfoOf_binaryErasureMAC₁, uniformPMF]
  have h₂ : macInfo₂ (uniformPMF Bool) (uniformPMF Bool) binaryErasureMAC = log 2 := by
    rw [macInfo₂_eq_sum hp hp binaryErasureMAC_isChannel]
    simp [mutualInfoOf_binaryErasureMAC₂, uniformPMF]
  rintro R ⟨r₁, r₂, r₃⟩
  refine macPentagonsBits_subset binaryErasureMAC_isChannel ⟨_, _, hp, hp, ?_, ?_, ?_⟩
  · rwa [h₁, div_self hl.ne']
  · rwa [h₂, div_self hl.ne']
  · rwa [macInfo₁₂_binaryErasureMAC, mul_div_assoc, div_self hl.ne', mul_one]

/-- **Example (Lecture 4): binary erasure MAC.** `C₁ = C₂ = 1` bit. -/
lemma macC_binaryErasureMAC :
    macC₁ binaryErasureMAC ≤ log 2 ∧ macC₂ binaryErasureMAC ≤ log 2 := by
  have hW := binaryErasureMAC_isChannel
  refine ⟨ciSup_le fun b => ?_, ciSup_le fun a => ?_⟩
  · simpa [Fintype.card_bool] using
      capacity_le_log_card_input (W := fun a => binaryErasureMAC (a, b)) fun a => hW (a, b)
  · simpa [Fintype.card_bool] using
      capacity_le_log_card_input (W := fun b => binaryErasureMAC (a, b)) fun b => hW (a, b)

/-- **Example (Lecture 4): binary erasure MAC.** In the capacity region, `R₁ ≤ 1` and `R₂ ≤ 1`
bit. -/
theorem macCapacityRegionBits_binaryErasureMAC_subset :
    macCapacityRegionBits binaryErasureMAC ⊆ {R : ℝ × ℝ | R.1 ≤ 1 ∧ R.2 ≤ 1} := by
  have hl := log_pos one_lt_two
  intro R hR
  obtain ⟨h₁, h₂, -⟩ := macCapacityRegionBits_subset_macOuterBoundBits
    binaryErasureMAC_isChannel hR
  exact ⟨h₁.trans ((div_le_one hl).2 macC_binaryErasureMAC.1),
    h₂.trans ((div_le_one hl).2 macC_binaryErasureMAC.2)⟩

/-- **Example (Lecture 4): binary erasure MAC.** The inner and outer bounds do not coincide: the
rate pair `(1, 1/2)` is achievable but not by time division. -/
theorem binaryErasureMAC_not_timeDivision :
    ((1 : ℝ), (1 / 2 : ℝ)) ∈ macCapacityRegionBits binaryErasureMAC ∧
      ((1 : ℝ), (1 / 2 : ℝ)) ∉ macTimeDivisionBits binaryErasureMAC := by
  have hl := log_pos one_lt_two
  refine ⟨pentagon_subset_macCapacityRegionBits_binaryErasureMAC ⟨le_rfl, by norm_num,
    by norm_num⟩, ?_⟩
  rintro ⟨t, ⟨ht0, ht1⟩, h₁, h₂⟩
  have c₁ := (div_le_one hl).2 macC_binaryErasureMAC.1
  have c₂ := (div_le_one hl).2 macC_binaryErasureMAC.2
  dsimp only at h₁ h₂
  nlinarith [mul_le_mul_of_nonneg_left c₁ ht0,
    mul_le_mul_of_nonneg_left c₂ (by linarith : 0 ≤ 1 - t)]

/-- The tangent bound `-x log x ≤ r - x - x log r`, the elementary step of Gibbs's inequality. -/
private lemma negMulLog_le_tangent {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    negMulLog x ≤ r - x - x * log r := by
  rcases hx.eq_or_lt with rfl | hx'
  · simpa using hr.le
  · have h := log_le_sub_one_of_pos (div_pos hr hx')
    rw [log_div hr.ne' hx'.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hx
    have e : x * (r / x - 1) = r - x := by field_simp
    rw [e] at h'
    simp only [negMulLog]
    nlinarith

/-- The entropy of `Bern(s)` is at most `log 2 - (2 s - 1)² / 2`, by Pinsker's inequality. -/
private lemma binaryEntropy_le {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    negMulLog s + negMulLog (1 - s) ≤ log 2 - (2 * s - 1) ^ 2 / 2 := by
  have hP := bernoulliPMF_isPMF h0.le h1.le
  have hU := uniformPMF_isPMF (α := Bool)
  have hp := pinsker hP hU (fun x hx => by simp [uniformPMF] at hx)
  have hl1 : l1Dist (bernoulliPMF s) (uniformPMF Bool) ^ 2 = (2 * s - 1) ^ 2 := by
    have e : l1Dist (bernoulliPMF s) (uniformPMF Bool) = |s - 1 / 2| + |1 - s - 1 / 2| := by
      simp [l1Dist, bernoulliPMF, uniformPMF]
    have e₂ : |1 - s - 1 / 2| = |s - 1 / 2| := by
      rw [← abs_neg]
      congr 1
      ring
    rw [e, e₂, ← two_mul, mul_pow, sq_abs]
    ring
  have hrel : relEntropyReal (bernoulliPMF s) (uniformPMF Bool) =
      log 2 - (negMulLog s + negMulLog (1 - s)) := by
    have h1s : 0 < 1 - s := by linarith
    simp only [relEntropyReal, Fintype.sum_bool, bernoulliPMF, uniformPMF, ite_true,
      Bool.false_eq_true, ite_false, Fintype.card_bool, negMulLog]
    have e₁ : s / (1 / ((2 : ℕ) : ℝ)) = 2 * s := by norm_num; ring
    have e₂ : (1 - s) / (1 / ((2 : ℕ) : ℝ)) = 2 * (1 - s) := by norm_num; ring
    rw [e₁, e₂, log_mul two_ne_zero h0.ne', log_mul two_ne_zero h1s.ne']
    ring
  rw [hl1, hrel] at hp
  linarith

/-- **The sum rate of the binary erasure MAC, as an inequality.** With `P(Xⱼ = 1)` equal to `p` and
`q`, the entropy of `X₁ + X₂` is at most `3/2` bits. We compare with `Bin(2, s)` for
`s = (p + q) / 2`, which reduces the claim to the bound on the entropy of `Bern(s)`. -/
private lemma erasure_entropy_le {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    negMulLog ((1 - p) * (1 - q)) + negMulLog (p * (1 - q) + q * (1 - p)) + negMulLog (p * q) ≤
      3 / 2 * log 2 := by
  have hl := log_pos one_lt_two
  have hl2 : log 2 ≤ 2 := by linarith [log_two_lt_d9]
  by_cases h₀ : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h₀
    simp only [sub_zero, mul_one, zero_mul, add_zero, negMulLog_one, negMulLog_zero]
    linarith
  by_cases h₁ : p = 1 ∧ q = 1
  · obtain ⟨rfl, rfl⟩ := h₁
    simp only [sub_self, mul_zero, add_zero, mul_one, negMulLog_one, negMulLog_zero]
    linarith
  set s := (p + q) / 2 with hs
  have hs0 : 0 < s := by
    by_contra hn
    apply h₀
    constructor <;> linarith
  have hs1 : s < 1 := by
    by_contra hn
    apply h₁
    constructor <;> linarith
  have h1s : 0 < 1 - s := by linarith
  set a := (1 - p) * (1 - q) with ha
  set b := p * (1 - q) + q * (1 - p) with hb
  set c := p * q with hc
  have ha0 : 0 ≤ a := mul_nonneg (by linarith) (by linarith)
  have hb0 : 0 ≤ b := add_nonneg (mul_nonneg hp0 (by linarith)) (mul_nonneg hq0 (by linarith))
  have hc0 : 0 ≤ c := mul_nonneg hp0 hq0
  have t₀ := negMulLog_le_tangent ha0 (show 0 < (1 - s) ^ 2 by positivity)
  have t₁ := negMulLog_le_tangent hb0 (show 0 < 2 * s * (1 - s) by positivity)
  have t₂ := negMulLog_le_tangent hc0 (show 0 < s ^ 2 by positivity)
  rw [log_pow] at t₀ t₂
  rw [log_mul (by positivity) h1s.ne', log_mul two_ne_zero hs0.ne'] at t₁
  have hsum : (1 - s) ^ 2 + 2 * s * (1 - s) + s ^ 2 = a + b + c := by
    simp only [ha, hb, hc, hs]
    ring
  have e₁ : 2 * a + b = 2 * (1 - s) := by
    simp only [ha, hb, hs]
    ring
  have e₂ : b + 2 * c = 2 * s := by
    simp only [hb, hc, hs]
    ring
  have hB : 2 * s * (1 - s) ≤ b := by
    have : b - 2 * s * (1 - s) = (p - q) ^ 2 / 2 := by
      simp only [hb, hs]
      ring
    nlinarith [sq_nonneg (p - q)]
  have hH := binaryEntropy_le hs0 hs1
  -- The cross entropy with `Bin(2, s)` is `2 H(s) - b log 2`.
  have hcross : negMulLog a + negMulLog b + negMulLog c ≤
      2 * (negMulLog s + negMulLog (1 - s)) - b * log 2 := by
    have l₁ : (2 * a + b) * log (1 - s) = 2 * (1 - s) * log (1 - s) := by rw [e₁]
    have l₂ : (b + 2 * c) * log s = 2 * s * log s := by rw [e₂]
    simp only [negMulLog] at t₀ t₁ t₂ ⊢
    push_cast at t₀ t₂
    nlinarith
  have hfin : 2 * (log 2 - (2 * s - 1) ^ 2 / 2) - 2 * s * (1 - s) * log 2 ≤ 3 / 2 * log 2 := by
    have e : 2 * s * (1 - s) = (1 - (2 * s - 1) ^ 2) / 2 := by ring
    rw [e]
    nlinarith [sq_nonneg (2 * s - 1), mul_nonneg (sq_nonneg (2 * s - 1)) (sub_nonneg.2 hl2)]
  have hbl : 2 * s * (1 - s) * log 2 ≤ b * log 2 := mul_le_mul_of_nonneg_right hB hl.le
  linarith

/-- **Example (Lecture 4): binary erasure MAC.** The sum rate is at most `3/2` bits, for any product
input: `I(X₁, X₂; Y) ≤ 3/2`. -/
theorem macInfo₁₂_binaryErasureMAC_le {p₁ p₂ : Bool → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) :
    macInfo₁₂ p₁ p₂ binaryErasureMAC ≤ 3 / 2 * log 2 := by
  have hW := binaryErasureMAC_isChannel
  have hP := hp₁.prodDist hp₂
  have hf₁ : p₁ false = 1 - p₁ true := by
    have := hp₁.sum_eq_one
    rw [Fintype.sum_bool] at this
    linarith
  have hf₂ : p₂ false = 1 - p₂ true := by
    have := hp₂.sum_eq_one
    rw [Fintype.sum_bool] at this
    linarith
  have ht₁ : p₁ true ≤ 1 := by linarith [hp₁.nonneg false]
  have ht₂ : p₂ true ≤ 1 := by linarith [hp₂.nonneg false]
  have hle : macInfo₁₂ p₁ p₂ binaryErasureMAC ≤
      entropy (outDist (prodDist p₁ p₂) binaryErasureMAC) := by
    change mutualInfoOf (prodDist p₁ p₂) binaryErasureMAC ≤ _
    rw [mutualInfoOf_eq hP hW]
    have : 0 ≤ ∑ x, prodDist p₁ p₂ x * entropy (binaryErasureMAC x) :=
      sum_nonneg fun x _ => mul_nonneg (hP.nonneg x) (entropy_nonneg (hW x))
    linarith
  refine hle.trans ?_
  have h := erasure_entropy_le (hp₁.nonneg true) ht₁ (hp₂.nonneg true) ht₂
  have e₀ : outDist (prodDist p₁ p₂) binaryErasureMAC 0 = (1 - p₁ true) * (1 - p₂ true) := by
    simp [outDist, binaryErasureMAC, detMAC, binaryErasureMACOut, prodDist, Fintype.sum_prod_type,
      hf₁, hf₂]
  have e₁ : outDist (prodDist p₁ p₂) binaryErasureMAC 1 =
      p₁ true * (1 - p₂ true) + p₂ true * (1 - p₁ true) := by
    simp [outDist, binaryErasureMAC, detMAC, binaryErasureMACOut, prodDist, Fintype.sum_prod_type,
      hf₁, hf₂]
    ring
  have e₂ : outDist (prodDist p₁ p₂) binaryErasureMAC 2 = p₁ true * p₂ true := by
    simp [outDist, binaryErasureMAC, detMAC, binaryErasureMACOut, prodDist, Fintype.sum_prod_type]
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_three, e₀, e₁, e₂]
  exact h

/-- **Example (Lecture 4): binary erasure MAC.** The capacity region is the pentagon `R₁ ≤ 1`,
`R₂ ≤ 1`, `R₁ + R₂ ≤ 3/2`, in bits. -/
theorem macCapacityRegionBits_binaryErasureMAC :
    macCapacityRegionBits binaryErasureMAC =
      {R : ℝ × ℝ | R.1 ≤ 1 ∧ R.2 ≤ 1 ∧ R.1 + R.2 ≤ 3 / 2} := by
  have hl := log_pos one_lt_two
  refine Subset.antisymm (fun R hR => ?_) pentagon_subset_macCapacityRegionBits_binaryErasureMAC
  obtain ⟨h₁, h₂⟩ := macCapacityRegionBits_binaryErasureMAC_subset hR
  refine ⟨h₁, h₂, ?_⟩
  rw [macCapacityRegionBits_eq binaryErasureMAC_isChannel] at hR
  have hT : Convex ℝ {R : ℝ × ℝ | R.1 + R.2 ≤ 3 / 2} := by
    intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy ⊢
    nlinarith
  have hc : IsClosed {R : ℝ × ℝ | R.1 + R.2 ≤ 3 / 2} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hsub : macPentagonsBits binaryErasureMAC ⊆ {R : ℝ × ℝ | R.1 + R.2 ≤ 3 / 2} := by
    rintro R ⟨p₁, p₂, hp₁, hp₂, -, -, h₃⟩
    refine h₃.trans ?_
    rw [div_le_iff₀ hl]
    exact macInfo₁₂_binaryErasureMAC_le hp₁ hp₂
  exact closure_minimal (convexHull_min hsub hT) hc hR

/-! ## The AWGN multiple access channel -/

/-- Cover and Thomas's `C(x)` is the notes' `C(x) = ½ log(1 + x)`. -/
lemma gaussCap_eq_gaussianCapacityFun : gaussCap = gaussianCapacityFun := by
  funext x
  simp [gaussCap, gaussianCapacityFun]

/-! ## Index of numbered results -/

/-- **Theorem 1 (Lecture 4, van der Meulen).** `𝒞 = closure (⋃ₖ 𝒞_k)`. -/
alias theorem_4_1 := macCapacityRegionBits_eq_closure_iUnion

/-- **Theorem 2 (Lecture 4, Ahlswede, Liao).** `𝒞` is the convex closure of the pentagons. -/
alias theorem_4_2 := macCapacityRegionBits_eq

/-- **Time sharing (Lecture 4).** The capacity region is convex. -/
alias time_sharing := convex_macCapacityRegionBits

end InfoTheory.ElGamalKim
