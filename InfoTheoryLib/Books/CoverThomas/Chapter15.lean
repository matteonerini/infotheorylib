/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter14
public import InfoTheoryLib.Network.Gaussian
public import InfoTheoryLib.Network.Typicality
public import InfoTheoryLib.Network.MACCode
public import InfoTheoryLib.Network.MACRegion
public import InfoTheoryLib.Network.MACAchievability
public import InfoTheoryLib.Network.MACConverse
public import InfoTheoryLib.Network.MACCapacity
public import InfoTheoryLib.Network.SlepianWolf
public import InfoTheoryLib.Network.Broadcast

/-!
# Cover & Thomas, Chapter 15: Network Information Theory

This file indexes the formalization of Chapter 15 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_15_3_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Channels.** A multiple-access channel `p(y | x₁, x₂)` is a channel `W : 𝒳₁ × 𝒳₂ → 𝒴 → ℝ`
  with a product input, and a broadcast channel `p(y₁, y₂ | x)` a channel `W : 𝒳 → 𝒴₁ × 𝒴₂ → ℝ`
  with a product output. They are used `n` times without feedback through `channelExt`.
* **Rates.** Rates are in nats. Channel codes of rate `R` have `⌈e^{nR}⌉` messages (as in
  Chapter 7) and distributed source codes of rate `R` have `⌊e^{nR}⌋` indices (as in Chapter 10).
  Rates are real numbers: a channel code of negative rate has a single message, so the capacity
  regions of channels also contain pairs with a negative rate, which does not change their shape
  in the positive quadrant.
* **Regions.** The rate regions are written with the book's strict or nonstrict inequalities;
  the capacity regions are closures, so both give the same results.
* **Time sharing.** The time-sharing variable `Q` of Theorem 15.3.4 takes finitely many values,
  without the bound `|Q| ≤ 4`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 15.1 Gaussian multiple-user channels
* (15.5), (15.146): `gaussCap`, `gaussianInfoCapacity_eq_gaussCap` (`Network.Gaussian`).
* (15.6)–(15.10): `gaussianMACRegion`, `const_mem_gaussianMACRegion`; the remarks of
  Section 15.1.2: `tendsto_gaussCap_mul_atTop`.
* (15.11)–(15.12): `gaussianBCRegion`, `mem_gaussianBCRegion_of_single`, `gaussianBC_sum_ge`.
* (15.16)–(15.17): `gaussianRelayRate`, `gaussianRelayCapacity`, `gaussianRelayCapacity_eq`,
  `gaussCap_le_gaussianRelayCapacity`.
* Section 15.1.5: `gaussCap_lt_iff_strong_interference`.

### 15.2 Jointly typical sequences
* Theorem 15.2.1, for a pair of random variables: (15.29) `tendsto_prob_jointTypicalSet`, (15.31)
  `card_jointTypicalSet_le` (`ChannelCoding.JointTypicality`), (15.33)–(15.34)
  `jointTypicalSet_condProb_bounds` (`Network.Typicality`).
* Theorem 15.2.2, (15.40)–(15.44): `card_fiber_jointTypicalSet_le`,
  `card_fiber_jointTypicalSet_le'`.
* Theorem 15.2.3 for independent sequences: `prob_indep_jointTypicalSet_le`
  (`ChannelCoding.JointTypicality`), `sum_indep_typical_le` (`Network.MACAchievability`).
* The entropies of i.i.d. pairs: `entropy_jointIid`, `condEntropy_jointIid_fst`,
  `condEntropy_jointIid_snd`.

### 15.3 Multiple-access channel
* (15.52)–(15.55): `MACCode`, `MACCode.condErrProb`, `MACCode.avgErrProb`; achievable rate pairs
  and the capacity region: `IsAchievableMAC`, `macCapacityRegion` (`Network.MACCode`).
* (15.56)–(15.58): `macInfo₁`, `macInfo₂`, `macInfo₁₂`, `macRateRegion`, `macRateRegions`
  (`Network.MACRegion`).
* Theorem 15.3.1: `macCapacityRegion_eq` (`Network.MACCapacity`).
* Example 15.3.2 (binary multiplier channel): `binaryMultiplierMAC`, `example_15_3_2` (here), with
  `le_log_card_of_mem_macCapacityRegion` (`Network.MACCapacity`).
* Section 15.3.1 (achievability), (15.60)–(15.72): `macTypicalSet`, `macTypicalDecode`,
  `sum_codebook_macCondErrProb_le`, `exists_macCode_avgErrProb_le`,
  `isAchievableMAC_of_mem_macRateRegion`; (15.68)–(15.69): `mutualInfo_macJointA`,
  `mutualInfo_macJointB` (`Network.MACAchievability`).
* Section 15.3.2 (corner points): `isAchievableMAC_of_isAchievableRate`,
  `isAchievableMAC_of_isAchievableRate₂` (`Network.MACCapacity`).
* Theorem 15.3.2, (15.80): `MACCode.append`, `MACCode.avgErrProb_append_le`, `convex_macSlackSet`
  (`Network.MACCode`); `convex_macCapacityRegion` (`Network.MACCapacity`).
* (15.84) and `I₃ ≤ I₁ + I₂`: `macInfo₁₂_le_add`, `macInfo₁_le_macInfo₁₂`,
  `macInfo₂_le_macInfo₁₂`.
* Lemma 15.3.1, (15.85)–(15.88): `exists_pentagon_decomp`.
* Theorem 15.3.3: `sub_mem_convexHull_of_mem_macRegion`, `macRegion_subset_closure_convexHull`.
* Theorem 15.3.4, (15.89)–(15.95): `macRegion`, `macCapacityRegion_eq_closure_macRegion`.
* Theorem 15.3.5 (Carathéodory) in the plane: `exists_convex_combination_le_three`.
* Section 15.3.4 (converse), (15.96)–(15.131): `MACCode.jointLaw`, `MACCode.letterDist₁`,
  `MACCode.letterDist₂`, `MACCode.log_le_macInfo₁`, `MACCode.log_le_macInfo₂`,
  `MACCode.log_mul_le_macInfo₁₂`, `IsAchievableMAC.mem_closure_macRegion`
  (`Network.MACConverse`); (15.109)–(15.110): `condEntropy_codeLaw`.
* Section 15.3.6 (Gaussian multiple-access channel): (15.147)–(15.149)
  `mem_gaussianMACRegion_two`; onion peeling `gaussCap_add_gaussCap`,
  `corner_mem_gaussianMACRegion`; `tendsto_gaussCap_mul_div_atTop`; (15.150)–(15.151) `fdmaRate`,
  `fdmaRate_add_le`, `fdmaRate_add_eq`; time division `tdma_le`, `tdma_eq`, `naive_tdma_le`;
  (15.153) `gaussianMACRegion` (`Network.Gaussian`).

### 15.4 Encoding of correlated sources
* (15.154)–(15.157): `SWCode`, `SWCode.errProb`, `IsAchievableSW`, `swAchievableRegion`
  (`Network.SlepianWolf`).
* Theorem 15.4.1 (Slepian–Wolf), (15.158)–(15.160): `swRegion`, `swAchievableRegion_eq`.
* Example 15.4.1: `weatherPMF`, `example_15_4_1` (here). Example 15.4.2: `example_15_4_2` (here).
* Section 15.4.1 (achievability), (15.167)–(15.177): `swTypicalDecode`, `swTypicalDecode_ne_le`,
  `binLaw`, `sum_bins_errProb_le`, `isAchievableSW_of_lt`.
* Section 15.4.2 (converse), (15.178)–(15.194): `SWCode.mul_condEntropy_fst_le`,
  `SWCode.mul_condEntropy_snd_le`, `SWCode.mul_entropy_le`, `IsAchievableSW.mem_swRegion`.

### 15.6 Broadcast channel
* (15.201)–(15.204): `BCCode`, `BCCode.errProb`, `IsAchievableBC`, `bcCapacityRegion`
  (`Network.Broadcast`).
* Theorem 15.6.1: `bcCapacityRegion_eq_of_marg_eq`, with `BCCode.errProb₁_eq`,
  `BCCode.max_errProb_le`, `BCCode.errProb_le_add`, `isAchievableBC_iff`.
* Section 15.6.2, (15.209): `IsPhysicallyDegraded`, `IsStochasticallyDegraded`,
  `IsPhysicallyDegraded.isStochasticallyDegraded`, `IsStochasticallyDegraded.capacityRegion_eq`.
* Example 15.6.5, (15.229)–(15.230): `bscBroadcast`, `example_15_6_5` (here).
* Example 15.6.6, (15.240)–(15.241): `gaussianBCRegion` (`Network.Gaussian`).

## Not formalized

* The coding theorems for the Gaussian channels of Section 15.1, which the book states without
  proof, the bound (15.138)–(15.145) on the Gaussian multiple-access channel (which needs
  conditional differential entropies), the interference channel and the two-way channel.
* The typical sets of collections of random variables (15.24) and Theorem 15.2.3 for
  conditionally independent sequences.
* Examples 15.3.1 and 15.3.3, the `m`-user multiple-access channel (Theorem 15.3.6) and the bound
  `|Q| ≤ 4` (we prove Carathéodory's theorem in the plane, which gives three points of the union
  of the pentagons).
* The Slepian–Wolf theorem for many sources (Theorem 15.4.2), the interpretation of
  Section 15.4.4 and the duality of Section 15.5.
* Examples 15.6.1–15.6.4, the rates (15.231)–(15.237) of Example 15.6.5, the broadcast channel
  with common information, and Theorems 15.6.2–15.6.4 (superposition coding and the converse for
  degraded broadcast channels).
* The relay channel (Section 15.7, Theorems 15.7.1–15.7.2), source coding with side information
  (Section 15.8, Theorem 15.8.1 and Lemma 15.8.1), rate distortion with side information
  (Section 15.9, Theorem 15.9.1 and Lemma 15.9.1) and the cut-set bound for general networks
  (Section 15.10, Theorem 15.10.1).
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Example 15.3.2: the binary multiplier channel -/

/-- **Example 15.3.2** The binary multiplier channel `Y = X₁ X₂`. -/
def binaryMultiplierMAC : Bool × Bool → Bool → ℝ := fun x y => if y = (x.1 && x.2) then 1 else 0

lemma binaryMultiplierMAC_isChannel : IsChannel binaryMultiplierMAC := fun x =>
  ⟨fun y => by unfold binaryMultiplierMAC; split_ifs <;> norm_num, by
    obtain ⟨a, b⟩ := x
    cases a <;> cases b <;> simp [binaryMultiplierMAC]⟩

lemma binaryMultiplierMAC_true_right :
    (fun a => binaryMultiplierMAC (a, true)) = noiselessChannel := by
  funext a y
  cases a <;> cases y <;> simp [binaryMultiplierMAC, noiselessChannel]

lemma binaryMultiplierMAC_true_left :
    (fun b => binaryMultiplierMAC (true, b)) = noiselessChannel := by
  funext b y
  cases b <;> cases y <;> simp [binaryMultiplierMAC, noiselessChannel]

/-- **Example 15.3.2** The capacity region of the binary multiplier channel `Y = X₁ X₂` is
`R₁ + R₂ ≤ log 2` (one bit) with `R₁, R₂ ≤ log 2`: setting `X₂ = 1` gives sender 1 a noiseless
channel, and time sharing achieves the rest. -/
theorem example_15_3_2 :
    macCapacityRegion binaryMultiplierMAC =
      {R | R.1 ≤ log 2 ∧ R.2 ≤ log 2 ∧ R.1 + R.2 ≤ log 2} := by
  have hW := binaryMultiplierMAC_isChannel
  refine subset_antisymm (fun R hR => ?_) fun R hR => ?_
  · have := le_log_card_of_mem_macCapacityRegion hW hR
    simpa using this
  obtain ⟨h1, h2, h3⟩ := hR
  have hlog : 0 < log (2 : ℝ) := log_pos one_lt_two
  have hC : capacity noiselessChannel = log 2 := capacity_noiselessChannel.1
  -- The corner points `(s, 0)` and `(0, s)` for `s ≤ log 2`.
  have hc₁ : ∀ s ≤ log 2, (s, 0) ∈ macCapacityRegion binaryMultiplierMAC := fun s hs => by
    refine macSlackSet_subset_macCapacityRegion fun δ hδ => ?_
    have h := isAchievableMAC_of_isAchievableRate hW true
      (R := s - δ) (by
        rw [binaryMultiplierMAC_true_right]
        exact isAchievableRate_of_lt_capacity noiselessChannel_isChannel (by linarith))
    exact h.mono hW le_rfl (by dsimp only; linarith)
  have hc₂ : ∀ s ≤ log 2, (0, s) ∈ macCapacityRegion binaryMultiplierMAC := fun s hs => by
    refine macSlackSet_subset_macCapacityRegion fun δ hδ => ?_
    have h := isAchievableMAC_of_isAchievableRate₂ hW true
      (R := s - δ) (by
        rw [binaryMultiplierMAC_true_left]
        exact isAchievableRate_of_lt_capacity noiselessChannel_isChannel (by linarith))
    exact h.mono hW (by dsimp only; linarith) le_rfl
  -- `R` is below the point `(a, b)` with `a, b ≥ 0` and `a + b ≤ log 2`.
  set a := max R.1 0
  set b := max R.2 0
  have ha : 0 ≤ a := le_max_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have hab : a + b ≤ log 2 := by
    rcases le_total R.1 0 with r1 | r1 <;> rcases le_total R.2 0 with r2 | r2 <;>
      simp only [a, b, max_eq_right r1, max_eq_left r1, max_eq_right r2, max_eq_left r2] <;>
      linarith
  have hmem : (a, b) ∈ macCapacityRegion binaryMultiplierMAC := by
    rcases (add_nonneg ha hb).lt_or_eq with ht | ht
    · have e : (a, b) = (a / (a + b)) • ((a + b, 0) : ℝ × ℝ) + (b / (a + b)) • (0, a + b) := by
        ext <;> simp <;> field_simp
      rw [e]
      exact convex_macCapacityRegion hW (hc₁ _ hab) (hc₂ _ hab) (by positivity) (by positivity)
        (by field_simp)
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      rw [ha0, hb0]
      exact hc₁ 0 hlog.le
  exact mem_macCapacityRegion_of_le hW hmem (le_max_left _ _) (le_max_left _ _)

/-! ## Examples 15.4.1 and 15.4.2: Slepian–Wolf coding -/

/-- **Example 15.4.1** The weather in Gotham and Metropolis: each city is sunny with probability
`1/2`, and the weather is the same in both cities with probability `0.89`. -/
def weatherPMF : Bool × Bool → ℝ := fun z => if z.1 = z.2 then 89 / 200 else 11 / 200

lemma weatherPMF_isPMF : IsPMF weatherPMF :=
  ⟨fun z => by unfold weatherPMF; split_ifs <;> norm_num, by
    simp [weatherPMF, Fintype.sum_prod_type]; norm_num⟩

lemma margSnd_weatherPMF : margSnd weatherPMF = fun _ => 1 / 2 := by
  funext b
  rw [margSnd, dist_snd]
  cases b <;> simp [weatherPMF] <;> norm_num

/-- **Example 15.4.1** `H(X, Y) = log 2 + H(0.11)`: Slepian–Wolf coding of `n` days of weather
needs `n (1 + H(0.89))` bits in total instead of `2n`, and `(H(X), H(Y | X)) = (log 2, H(0.11))`
is a corner of the Slepian–Wolf region. -/
theorem example_15_4_1 :
    entropy weatherPMF = log 2 + binEntropy (11 / 100) ∧
      (log 2, binEntropy (11 / 100)) ∈ swRegion weatherPMF := by
  have h1 : log (89 / 200 : ℝ) = log (89 / 100) - log 2 := by
    rw [← log_div (by norm_num) (by norm_num)]; norm_num
  have h2 : log (11 / 200 : ℝ) = log (11 / 100) - log 2 := by
    rw [← log_div (by norm_num) (by norm_num)]; norm_num
  have hH : entropy weatherPMF = log 2 + binEntropy (11 / 100) := by
    have h3 : log (100 / 11 : ℝ) = -log (11 / 100) := by rw [← log_inv]; norm_num
    have h4 : log (100 / 89 : ℝ) = -log (89 / 100) := by rw [← log_inv]; norm_num
    simp only [entropy, Fintype.sum_prod_type, Fintype.sum_bool, weatherPMF,
      binEntropy_eq_mul_log_inv]
    norm_num
    rw [h1, h2, h3, h4]
    ring
  have hY : entropy (margSnd weatherPMF) = log 2 := by
    rw [margSnd_weatherPMF]
    simp only [entropy, Fintype.sum_bool]
    rw [one_div, log_inv]
    ring
  have hX : entropy (margFst weatherPMF) = log 2 := by
    have : margFst weatherPMF = fun _ => 1 / 2 := by
      funext a
      rw [margFst, dist_fst]
      cases a <;> simp [weatherPMF] <;> norm_num
    rw [this]
    simp only [entropy, Fintype.sum_bool]
    rw [one_div, log_inv]
    ring
  refine ⟨hH, ?_, ?_, ?_⟩
  · rw [condEntropy_fst_snd_eq weatherPMF_isPMF, hH, hY]
    linarith [binEntropy_le_log_two (p := 11 / 100)]
  · rw [condEntropy_snd_fst_eq weatherPMF_isPMF, hH, hX]
    simp
  · rw [hH]

/-- **Example 15.4.2** The joint pmf `p(0, 0) = p(0, 1) = p(1, 1) = 1/3`. -/
def example1542PMF : Bool × Bool → ℝ := fun z => if z = (true, false) then 0 else 1 / 3

/-- **Example 15.4.2** `H(U, V) = log 3`, about `1.58` bits, less than the `2` bits needed by
independent encoding. -/
theorem example_15_4_2 : entropy example1542PMF = log 3 ∧ entropy example1542PMF < 2 * log 2 := by
  have h : entropy example1542PMF = log 3 := by
    simp only [entropy, Fintype.sum_prod_type, Fintype.sum_bool, example1542PMF]
    norm_num
    simp only [one_div, log_inv]
    ring
  refine ⟨h, ?_⟩
  rw [h, ← log_rpow two_pos]
  exact log_lt_log (by norm_num) (by norm_num)

/-! ## Example 15.6.5: the binary symmetric broadcast channel -/

/-- **Example 15.6.5** Two binary symmetric channels with crossover probabilities `p₁` and `p₂`
from the same input, with independent noises. -/
def bscBroadcast (p₁ p₂ : ℝ) : Bool → Bool × Bool → ℝ := fun x y => bsc p₁ x y.1 * bsc p₂ x y.2

lemma bscBroadcast_isChannel {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁) (h₁' : p₁ ≤ 1) (h₂ : 0 ≤ p₂)
    (h₂' : p₂ ≤ 1) : IsChannel (bscBroadcast p₁ p₂) := fun x =>
  ⟨fun y => mul_nonneg ((bsc_isChannel h₁ h₁' x).nonneg _) ((bsc_isChannel h₂ h₂' x).nonneg _),
    by
      rw [Fintype.sum_prod_type]
      simp only [bscBroadcast, ← mul_sum, (bsc_isChannel h₂ h₂' x).sum_eq_one, mul_one]
      exact (bsc_isChannel h₁ h₁' x).sum_eq_one⟩

/-- **Example 15.6.5, (15.229)–(15.230).** For `p₁ < 1/2`, the binary symmetric channel with
crossover probability `p₂` is the cascade of the one with `p₁` and a binary symmetric channel with
`α = (p₂ - p₁)/(1 - 2p₁)`: `p₁(1 - α) + (1 - p₁)α = p₂`. So the binary symmetric broadcast
channel is stochastically degraded, and has the capacity region of a physically degraded
channel. -/
theorem example_15_6_5 {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁) (h₁₂ : p₁ ≤ p₂) (h₂ : p₂ < 1 / 2) :
    p₁ * (1 - (p₂ - p₁) / (1 - 2 * p₁)) + (1 - p₁) * ((p₂ - p₁) / (1 - 2 * p₁)) = p₂ ∧
      IsStochasticallyDegraded (bscBroadcast p₁ p₂) := by
  have hp : 0 < 1 - 2 * p₁ := by linarith
  set a := (p₂ - p₁) / (1 - 2 * p₁)
  have ha : p₁ * (1 - a) + (1 - p₁) * a = p₂ := by
    have hp' : 1 - 2 * p₁ ≠ 0 := hp.ne'
    have e : p₁ * (1 - a) + (1 - p₁) * a = p₁ + a * (1 - 2 * p₁) := by ring
    rw [e, div_mul_cancel₀ _ hp']
    ring
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hp.le
  have ha1 : a ≤ 1 := (div_le_one hp).2 (by linarith)
  refine ⟨ha, bsc a, bsc_isChannel ha0 ha1, fun x y₂ => ?_⟩
  have hm₁ : ∀ y₁, bcMarg₁ (bscBroadcast p₁ p₂) x y₁ = bsc p₁ x y₁ := fun y₁ => by
    simp only [bcMarg₁, bscBroadcast, ← mul_sum,
      (bsc_isChannel (h₁.trans h₁₂) (by linarith) x).sum_eq_one, mul_one]
  have hm₂ : bcMarg₂ (bscBroadcast p₁ p₂) x y₂ = bsc p₂ x y₂ := by
    simp only [bcMarg₂, bscBroadcast, ← sum_mul, (bsc_isChannel h₁ (by linarith) x).sum_eq_one,
      one_mul]
  simp only [hm₁, hm₂, Fintype.sum_bool]
  cases x <;> cases y₂ <;> simp [bsc] <;> linarith

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 15.
-/

/-- **Theorem 15.2.1 (4).** -/
alias theorem_15_2_1_4 := jointTypicalSet_condProb_bounds

/-- **Theorem 15.2.2.** -/
alias theorem_15_2_2 := card_fiber_jointTypicalSet_le

/-- **Theorem 15.3.1 (Multiple-access channel capacity).** -/
alias theorem_15_3_1 := macCapacityRegion_eq

/-- **Theorem 15.3.1 (achievability).** -/
alias theorem_15_3_1_achievability := isAchievableMAC_of_mem_macRateRegion

/-- **Theorems 15.3.1 and 15.3.4 (converse).** -/
alias theorem_15_3_1_converse := IsAchievableMAC.mem_closure_macRegion

/-- **Theorem 15.3.2 (Convexity of the capacity region).** -/
alias theorem_15_3_2 := convex_macCapacityRegion

/-- **Lemma 15.3.1.** -/
alias lemma_15_3_1 := exists_pentagon_decomp

/-- **Theorem 15.3.3.** -/
alias theorem_15_3_3 := sub_mem_convexHull_of_mem_macRegion

/-- **Theorem 15.3.4.** -/
alias theorem_15_3_4 := macCapacityRegion_eq_closure_macRegion

/-- **Theorem 15.3.5 (Carathéodory), in the plane.** -/
alias theorem_15_3_5 := exists_convex_combination_le_three

/-- **Theorem 15.4.1 (Slepian–Wolf).** -/
alias theorem_15_4_1 := swAchievableRegion_eq

/-- **Theorem 15.4.1 (achievability).** -/
alias theorem_15_4_1_achievability := isAchievableSW_of_lt

/-- **Theorem 15.4.1 (converse).** -/
alias theorem_15_4_1_converse := IsAchievableSW.mem_swRegion

/-- **Theorem 15.6.1.** -/
alias theorem_15_6_1 := bcCapacityRegion_eq_of_marg_eq

end InfoTheory.CoverThomas
