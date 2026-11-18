/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter7
public import InfoTheoryLib.Network.Gaussian
public import InfoTheoryLib.StateChannel.Compound
public import InfoTheoryLib.StateChannel.GPConverse

/-!
# El Gamal & Kim, Lecture 7: Channels with State

This file indexes the formalization of Lecture 7 of [elgamal2010] and contains the lecture's worked
examples, with aliases named after its results. We formalize the compound channel (Theorem 1), the
DMC with DM state in all the scenarios of state information, in particular Shannon's strategies
(Theorem 3) and the Gelfand–Pinsker theorem, with their examples. Writing on dirty paper and the
multiple user extensions are formulas only, or not formalized.

## Conventions

* **Rates.** Rates are in bits, with message sets `[1 : 2^{nR}] = {1, …, 2^⌈nR⌉}`, as in Lecture 3.
  The values `compoundValue`, `causalValue`, `gpValue`, `stateKnownValue` are in nats, and a
  capacity in bits is the value divided by `log 2`.
* **Scenarios.** All the scenarios use `StateCode`: the pair `(E, D)` says what the encoder knows
  (`none`, `causal` or `noncausal`) and whether the decoder knows the state (`D = true`).
* **Auxiliary variables.** `U` takes values in `Fin k` for some `k`: the cardinality bounds are not
  formalized, and a maximum over `U` is a supremum.
* **Decoders** always output a message, as in Lecture 3.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Problem setup
* The DMC with DM state and its codes: `StateCode`, `StateCode.errProb`, `EncoderStateInfo`,
  `StateCode.Allowed`, `IsAchievableStateRate`, `stateCapacity` (`StateChannel.Basic`).

### Compound channel
* Codes, achievability and capacity: `compoundErr`, `IsAchievableCompound`, `compoundCapacity`,
  `compoundInfo`, `compoundValue`, `exists_compoundInfo_eq` (`StateChannel.Compound`).
* Theorem 1: `compoundCapacity_eq`, with the converse `one_sub_compoundErr_mul_log_le` and
  achievability `isAchievableCompound_of_lt`, `exists_compound_code_le` (`StateChannel.Compound`).
  The packing lemma,
  universal in the law of the output: `prob_iidPMF_condRobustTypicalSet_le`
  (`StateChannel.Multicoding`).
* The capacity does not increase if the decoder knows the state: `IsAchievableCompoundDec`,
  `compoundDecCapacity`, `compoundDecCapacity_eq`.
* `C_CC ≤ min_s C_s`: `compoundValue_le_capacity`.
* The compound BSC, for finitely many crossover probabilities: `compoundCapacity_bsc` (here).
* The Z-channel and the inverted Z-channel: `zChannel`, `invZChannel`, `capacity_zChannel`,
  `capacity_invZChannel`, `zCompound`, `compoundValue_zCompound`, `compoundCapacity_zCompound`, and
  `C_CC < C₁`: `compoundValue_zCompound_lt` (here).

### Channels with random state: simple special cases
* No state information: `stateCapacity_none_false`, `isAchievableStateRate_none_false_iff`
  (`StateChannel.Basic`).
* The state at the decoder: `stateCapacity_none_true`, with `I(X; Y, S) = I(X; Y | S)`:
  `mutualInfoOf_strategyOutChannel`.
* The state at both ends, causally or noncausally: `stateKnownValue`,
  `stateCapacity_causal_true`, `stateCapacity_noncausal_true`,
  `exists_sum_mul_mutualInfoOf_eq_stateKnownValue`, with the converse
  `StateCode.one_sub_errProb_mul_log_le`, and by the Shannon strategy
  `capacity_strategyOutChannel_id`, `isAchievableStateRate_causal_true_of_lt`.

### Causal state information at the encoder
* Theorem 3: `causalValue`, `stateCapacity_causal_false`, `causalValue_eq_capacity`
  (`StateChannel.Causal`), with `strategyChannel`, `ChannelCode.toStateCode`,
  `ChannelCode.errProb_toStateCode` (`StateChannel.Basic`), achievability
  `isAchievableStateRate_causal_false_of_lt` and the converse
  `StateCode.one_sub_errProb_mul_log_le_strategy`, `mutualInfo_causalLaw_succ_le`.

### Noncausal state information at the encoder
* Memory with defects: `defectChannel`, `defectState`, `stateCapacity_defect_none_false`,
  `stateCapacity_defect_causal_true`, `stateCapacity_defect_noncausal_true`,
  `stateCapacity_defect_none_true`, `stateCapacity_defect_noncausal_false`, `gpRate_defect` (here).
* The Gelfand–Pinsker theorem: `gpRate`, `gpValue`, `stateCapacity_noncausal_false`
  (`StateChannel.GelfandPinsker`, `StateChannel.GPConverse`).
* Achievability, by multicoding: `sum_codebook_subcode_le`, `subcodeDecode`,
  `sum_iidPMF_ite_forall_not_mem_le`, `eventually_le_prob_iidPMF_condRobustTypicalSet`
  (`StateChannel.Multicoding`), `gpEnc`, `exists_gp_code_le`,
  `isAchievableStateRate_noncausal_false_of_lt` (`StateChannel.GelfandPinsker`).
* The converse: `gpAux`, `mutualInfo_le_sum_gp`, `StateCode.one_sub_errProb_mul_log_le_gpValue`,
  `IsAchievableStateRate.le_gpValue` (`StateChannel.GPConverse`), and the reduction to functions
  `x(u, s)`:
  `gpMix_rate_le_gpValue`, `sub_le_gpValue_of_law` (`StateChannel.GPDerandomize`).
* The comparison to the causal case: `causalValue_le_gpValue`, and to the state at both ends:
  `gpValue_le_stateKnownValue`, `gpRate_le_stateKnownValue`.

### Writing on dirty paper (formulas)
* The BSC with additive state: `additiveBSC`, `stateCapacity_additiveBSC_causal`,
  `stateCapacity_additiveBSC_noncausal` (here).
* Costa's rate for `U = X + αS`: `costaRate`, `costaRate_opt`, `costaRate_le`, and the state
  unknown: `gaussCap_noise_le` (here).
* The AWGN-MAC with state, the corner point: `costa_mac_corner`, `costa_mac_alpha` (here).

## Not formalized

* The compound channel with infinitely many states, maximum empirical mutual information decoding,
  and the capacity `inf_s C_s` when the encoder knows the state. The compound BSC with `s ∈ [0, p]`
  is formalized only for finitely many crossover probabilities.
* The arbitrarily varying channel: Theorem 2, which the notes state without proof, and its example.
* The multiplexing scheme for the state at both ends: we use the Shannon strategy, the alternative
  on page 7-26. The functional representation lemma is replaced by `prodPMF`.
* The DM-MAC and the degraded DM-BC with DM state.
* All the cardinality bounds on `U`.
* Writing on dirty paper as a coding theorem (the capacity `C(P)`, also for non-Gaussian state), the
  AWGN-MAC and AWGN-BC with state, and the inner bounds with state for the DM-MAC and DM-BC. They
  need the Gelfand–Pinsker theorem for continuous alphabets.
* Coded state information.

## Issues in the notes

* **Page 7-30.** "an `n`-bit memory with `n(1 - p)` faulty cells" should be `np` faulty cells; there
  are about `np` stuck-at faults, as the previous item says.
* **Page 7-41.** "the encoder is given by `xᵢ(sᵢ)`" should be `xᵢ(m₁, m₂, sⁱ)`.
* **Page 7-52.** "`X₂ ∼ N(0, ᾱ)P)`" should be `X₂ ∼ N(0, ᾱP)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

open CoverThomas

/-! ## Tangent lines of the entropy -/

/-- `-t log t ≤ -t log r + r - t`, from `log x ≤ x - 1`. -/
lemma negMulLog_le_tangent {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    negMulLog t ≤ -(t * log r) + r - t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [hr.le]
  · have h := log_le_sub_one_of_pos (div_pos hr ht)
    rw [log_div hr.ne' ht.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h ht.le
    have e : t * (r / t - 1) = r - t := by field_simp
    rw [e] at h2
    rw [negMulLog]
    linarith

/-- The strict form, for `t ≠ r`. -/
lemma negMulLog_lt_tangent {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (htr : t ≠ r) :
    negMulLog t < -(t * log r) + r - t := by
  have hne : r / t ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq ht.ne'] at h
    exact htr h.symm
  have h := log_lt_sub_one_of_pos (div_pos hr ht) hne
  rw [log_div hr.ne' ht.ne'] at h
  have h2 := mul_lt_mul_of_pos_left h ht
  have e : t * (r / t - 1) = r - t := by field_simp
  rw [e] at h2
  rw [negMulLog]
  linarith

/-- `H(t) ≤ -t log r - (1 - t) log (1 - r)`. -/
lemma binEntropy_le_cross {t r : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    binEntropy t ≤ -(t * log r) - (1 - t) * log (1 - r) := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have a := negMulLog_le_tangent h0 hr0
  have b := negMulLog_le_tangent (sub_nonneg.2 h1) (sub_pos.2 hr1)
  linarith

/-! ## The compound BSC -/

/-- **Example (Lecture 7), page 7-8.** The compound BSC with crossover probabilities `q(s) ≤ P`,
one of them equal to `P ≤ 1/2`, has capacity `C_CC = 1 - H(P)` bits, achieved by `Bern(1/2)`. -/
theorem compoundCapacity_bsc {σ : Type*} [Fintype σ] [Nonempty σ] {q : σ → ℝ} {P : ℝ}
    (hq : ∀ s, 0 ≤ q s) (hqP : ∀ s, q s ≤ P) (hP : P ≤ 1 / 2) {s₀ : σ} (hs₀ : q s₀ = P) :
    compoundCapacity (fun s => bsc (q s)) = (log 2 - binEntropy P) / log 2 := by
  have hW : ∀ s, IsChannel (bsc (q s)) := fun s =>
    bsc_isChannel (hq s) ((hqP s).trans (by linarith))
  rw [compoundCapacity_eq hW]
  congr 1
  refine le_antisymm ?_ ?_
  · have h := compoundValue_le_capacity hW s₀
    rwa [(capacity_bsc (hq s₀) ((hqP s₀).trans (by linarith))).1, hs₀] at h
  · refine le_trans ?_ (compoundInfo_le_compoundValue hW (uniformPMF_isPMF (α := Bool)))
    refine le_inf' _ _ fun s _ => ?_
    have h01 := capacity_bsc (hq s) ((hqP s).trans (by linarith))
    rw [h01.2, h01.1]
    have hmono := binEntropy_strictMonoOn.monotoneOn (a := q s) (b := P)
      ⟨hq s, by linarith [hqP s, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]⟩
      ⟨(hq s).trans (hqP s), by linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]⟩ (hqP s)
    linarith

/-! ## The Z-channel and the inverted Z-channel -/

/-- **Example (Lecture 7), page 7-9.** The Z-channel with parameter `1/2`: `0 ↦ 0`, and `1` is
received as `0` or `1` with probability `1/2`. -/
def zChannel : Bool → Bool → ℝ
  | false, y => if y = false then 1 else 0
  | true, _ => 1 / 2

/-- **Example (Lecture 7), page 7-9.** The inverted Z-channel with parameter `1/2`. -/
def invZChannel : Bool → Bool → ℝ
  | true, y => if y = true then 1 else 0
  | false, _ => 1 / 2

lemma zChannel_isChannel : IsChannel zChannel := fun x => by
  cases x
  · refine ⟨fun y => by cases y <;> norm_num [zChannel], by simp [zChannel]⟩
  · refine ⟨fun y => by norm_num [zChannel], by norm_num [zChannel]⟩

lemma invZChannel_isChannel : IsChannel invZChannel := fun x => by
  cases x
  · refine ⟨fun y => by norm_num [invZChannel], by norm_num [invZChannel]⟩
  · refine ⟨fun y => by cases y <;> norm_num [invZChannel], by simp [invZChannel]⟩

lemma sum_bool_mul_entropy_half : negMulLog (1 / 2) + negMulLog (1 / 2) = log 2 := by
  rw [negMulLog, one_div, log_inv]
  ring

/-- `I(X; Y) = H(a/2) - a` bits for the Z-channel, with `a = P{X = 1}`. -/
lemma mutualInfoOf_zChannel {q : Bool → ℝ} (hq : IsPMF q) :
    mutualInfoOf q zChannel = binEntropy (q true / 2) - q true * log 2 := by
  have hs : q false = 1 - q true := by
    have := hq.sum_eq_one
    rw [Fintype.sum_bool] at this
    linarith
  rw [mutualInfoOf_eq_sum hq zChannel_isChannel, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Fintype.sum_bool, entropy_eq_sum_negMulLog, zChannel]
  simp only [ite_true, ite_false, Bool.true_eq_false, mul_one, mul_zero,
    add_zero, negMulLog_one, negMulLog_zero, sum_bool_mul_entropy_half]
  have e1 : q true * (1 / 2) = q true / 2 := by ring
  have e3 : q true / 2 + q false = 1 - q true / 2 := by rw [hs]; ring
  rw [e1, e3]

/-- `I(X; Y) = H((1 - a)/2) - (1 - a)` bits for the inverted Z-channel. -/
lemma mutualInfoOf_invZChannel {q : Bool → ℝ} (hq : IsPMF q) :
    mutualInfoOf q invZChannel = binEntropy (q false / 2) - q false * log 2 := by
  have hs : q true = 1 - q false := by
    have := hq.sum_eq_one
    rw [Fintype.sum_bool] at this
    linarith
  rw [mutualInfoOf_eq_sum hq invZChannel_isChannel, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Fintype.sum_bool, entropy_eq_sum_negMulLog, invZChannel]
  simp only [ite_true, ite_false, Bool.false_eq_true, mul_one, mul_zero,
    add_zero, zero_add, negMulLog_one, negMulLog_zero, sum_bool_mul_entropy_half]
  have e1 : q false * (1 / 2) = q false / 2 := by ring
  have e3 : q true + q false / 2 = 1 - q false / 2 := by rw [hs]; ring
  rw [e1, e3]
  ring

section ZValues

/-- `log 4 = 2 log 2`. -/
lemma log_four : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num

lemma binEntropy_one_fifth : binEntropy (1 / 5) = log 5 - 8 / 5 * log 2 := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog,
    show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num, show (1 : ℝ) / 5 = 5⁻¹ by norm_num, log_inv,
    show (4 : ℝ) / 5 = 4 / 5 by norm_num, log_div (by norm_num) (by norm_num), log_four]
  ring

lemma binEntropy_one_fourth : binEntropy (1 / 4) = 2 * log 2 - 3 / 4 * log 3 := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog,
    show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show (1 : ℝ) / 4 = 4⁻¹ by norm_num, log_inv,
    log_div (by norm_num) (by norm_num), log_four]
  ring

/-- The cross-entropy bound at `r = 1/5`. -/
lemma binEntropy_le_fifth {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    binEntropy t ≤ log 5 - (1 - t) * (2 * log 2) := by
  have h := binEntropy_le_cross (r := 1 / 5) h0 h1 (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num, show (1 : ℝ) / 5 = 5⁻¹ by norm_num, log_inv,
    log_div (by norm_num) (by norm_num), log_four] at h
  linarith

/-- The cross-entropy bound at `r = 1/4`. -/
lemma binEntropy_le_fourth {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    binEntropy t ≤ t * (2 * log 2) + (1 - t) * (2 * log 2 - log 3) := by
  have h := binEntropy_le_cross (r := 1 / 4) h0 h1 (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show (1 : ℝ) / 4 = 4⁻¹ by norm_num, log_inv,
    log_div (by norm_num) (by norm_num), log_four] at h
  linarith

/-- The input with `P{X = b} = 2/5`. -/
def twoFifths (b : Bool) : Bool → ℝ := fun x => if x = b then 2 / 5 else 3 / 5

lemma twoFifths_isPMF (b : Bool) : IsPMF (twoFifths b) := by
  refine ⟨fun x => ?_, ?_⟩
  · simp only [twoFifths]
    split_ifs <;> norm_num
  · cases b <;> norm_num [twoFifths]

/-- **Example (Lecture 7), page 7-9.** The Z-channel has capacity `C₁ = H(1/5) - 2/5` bits. -/
theorem capacity_zChannel : capacity zChannel = binEntropy (1 / 5) - 2 / 5 * log 2 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hq, hqC⟩ := exists_capacity_eq zChannel_isChannel
    rw [← hqC, mutualInfoOf_zChannel hq, binEntropy_one_fifth]
    have h1 := hq.le_one true
    have h0 := hq.nonneg true
    have := binEntropy_le_fifth (t := q true / 2) (by linarith) (by linarith)
    nlinarith
  · have h := mutualInfoOf_le_capacity (twoFifths_isPMF true) zChannel_isChannel
    rw [mutualInfoOf_zChannel (twoFifths_isPMF true)] at h
    have e : twoFifths true true = 2 / 5 := by simp [twoFifths]
    rw [e, show (2 : ℝ) / 5 / 2 = 1 / 5 by norm_num] at h
    exact h

/-- **Example (Lecture 7), page 7-9.** The inverted Z-channel has capacity `C₂ = H(1/5) - 2/5`
bits. -/
theorem capacity_invZChannel : capacity invZChannel = binEntropy (1 / 5) - 2 / 5 * log 2 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hq, hqC⟩ := exists_capacity_eq invZChannel_isChannel
    rw [← hqC, mutualInfoOf_invZChannel hq, binEntropy_one_fifth]
    have h1 := hq.le_one false
    have h0 := hq.nonneg false
    have := binEntropy_le_fifth (t := q false / 2) (by linarith) (by linarith)
    nlinarith
  · have h := mutualInfoOf_le_capacity (twoFifths_isPMF false) invZChannel_isChannel
    rw [mutualInfoOf_invZChannel (twoFifths_isPMF false)] at h
    have e : twoFifths false false = 2 / 5 := by simp [twoFifths]
    rw [e, show (2 : ℝ) / 5 / 2 = 1 / 5 by norm_num] at h
    exact h

/-- **Example (Lecture 7), page 7-9.** The compound channel with the Z-channel and the inverted
Z-channel. -/
def zCompound : Bool → Bool → Bool → ℝ := fun s => if s then invZChannel else zChannel

lemma zCompound_isChannel (s : Bool) : IsChannel (zCompound s) := by
  cases s
  · exact zChannel_isChannel
  · exact invZChannel_isChannel

/-- `max_{p(x)} min_s I(X; Y_s) = H(1/4) - 1/2` bits, achieved by `X ∼ Bern(1/2)`. -/
theorem compoundValue_zCompound : compoundValue zCompound = binEntropy (1 / 4) - log 2 / 2 := by
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  have hhalf : ∀ b, uniformPMF Bool b = 1 / 2 := fun b => by simp [uniformPMF]
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨_, uniformPMF Bool, hu, rfl⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    have h₁ := compoundInfo_le zCompound q false
    have h₂ := compoundInfo_le zCompound q true
    change compoundInfo zCompound q ≤ mutualInfoOf q zChannel at h₁
    change compoundInfo zCompound q ≤ mutualInfoOf q invZChannel at h₂
    rw [mutualInfoOf_zChannel hq] at h₁
    rw [mutualInfoOf_invZChannel hq] at h₂
    have hs : q false + q true = 1 := by
      have := hq.sum_eq_one
      rwa [Fintype.sum_bool, add_comm] at this
    have a0 := hq.nonneg true
    have b0 := hq.nonneg false
    have a1 := binEntropy_le_fourth (t := q true / 2) (by linarith) (by linarith)
    have a2 := binEntropy_le_fourth (t := q false / 2) (by linarith) (by linarith)
    rw [binEntropy_one_fourth]
    have hb : q false = 1 - q true := by linarith
    rw [hb] at h₂ a2
    nlinarith
  · refine le_trans ?_ (compoundInfo_le_compoundValue zCompound_isChannel hu)
    refine le_inf' _ _ fun s _ => ?_
    cases s
    · change _ ≤ mutualInfoOf (uniformPMF Bool) zChannel
      rw [mutualInfoOf_zChannel hu, hhalf, show (1 : ℝ) / 2 / 2 = 1 / 4 by norm_num]
      linarith
    · change _ ≤ mutualInfoOf (uniformPMF Bool) invZChannel
      rw [mutualInfoOf_invZChannel hu, hhalf, show (1 : ℝ) / 2 / 2 = 1 / 4 by norm_num]
      linarith

/-- **Example (Lecture 7), page 7-9.** The capacity of the compound channel is `H(1/4) - 1/2`
bits. -/
theorem compoundCapacity_zCompound :
    compoundCapacity zCompound = (binEntropy (1 / 4) - log 2 / 2) / log 2 := by
  rw [compoundCapacity_eq zCompound_isChannel, compoundValue_zCompound]

/-- **Example (Lecture 7), page 7-9.** `C_CC < C₁ = C₂`: the inequality `C_CC ≤ min_s C_s` can be
strict. -/
theorem compoundValue_zCompound_lt : compoundValue zCompound < capacity zChannel := by
  rw [compoundValue_zCompound, capacity_zChannel, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    binEntropy_one_fifth]
  have h1 := negMulLog_lt_tangent (t := 1 / 4) (r := 1 / 5) (by norm_num) (by norm_num)
    (by norm_num)
  have h2 := negMulLog_lt_tangent (t := 1 - 1 / 4) (r := 4 / 5) (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (1 : ℝ) / 5 = 5⁻¹ by norm_num, log_inv] at h1
  rw [log_div (by norm_num) (by norm_num), log_four] at h2
  norm_num at h1 h2 ⊢
  linarith

end ZValues

/-! ## The Gelfand–Pinsker value when `Y` determines `U` -/

section GP

variable {σ α β 𝒰 : Type*} [Fintype σ] [Fintype β] [Fintype 𝒰] {p : σ → ℝ} {ρ : σ → 𝒰 → ℝ}
  {x : 𝒰 → σ → α} {W : α × σ → β → ℝ}

/-- `I(U; Y) - I(U; S) = H(U | S) - H(U | Y)`. -/
lemma gpRate_eq_sub (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s)) (hW : IsChannel W) :
    gpRate p ρ x W = ∑ s, p s * entropy (ρ s) -
      H[fun z : (σ × 𝒰) × β => z.1.2 | Prod.snd ; gpJoint p ρ x W] := by
  have hJ := gpJoint_isPMF (x := x) hp hρ hW
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hJ (fun z : (σ × 𝒰) × β => z.1.2) Prod.snd
  have h2 := mutualInfo_eq_entropy_sub_condEntropy hJ (fun z : (σ × 𝒰) × β => z.1.2)
    (fun z => z.1.1)
  have h3 : H[fun z : (σ × 𝒰) × β => z.1.2 | fun z => z.1.1 ; gpJoint p ρ x W] =
      ∑ s, p s * entropy (ρ s) := by
    rw [← condEntropy_jointOf hp hρ]
    refine condEntropy_eq_of_dist_pair_eq hJ (jointOf_isPMF hp hρ) ?_
    have e : pair (fun z : (σ × 𝒰) × β => z.1.1) (fun z => z.1.2) =
        (pair Prod.fst Prod.snd) ∘ Prod.fst := rfl
    have hm : dist (gpJoint p ρ x W) Prod.fst = gpSU p ρ := margFst_gpJoint hW
    rw [e, dist_comp_eq, hm]
    rfl
  rw [gpRate, h1, h2, h3]
  ring

/-- If `Y = U`, then `H(U | Y) = 0`, and `I(U; Y) - I(U; S) = H(U | S)`. -/
lemma gpRate_eq_of_output_eq (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s)) {W' : α × σ → 𝒰 → ℝ}
    (hW' : IsChannel W') (hsupp : ∀ s u y, ρ s u ≠ 0 → W' (x u s, s) y ≠ 0 → y = u) :
    gpRate p ρ x W' = ∑ s, p s * entropy (ρ s) := by
  classical
  have hJ := gpJoint_isPMF (x := x) hp hρ hW'
  rw [gpRate_eq_sub hp hρ hW']
  have h0 : H[fun z : (σ × 𝒰) × 𝒰 => z.1.2 | Prod.snd ; gpJoint p ρ x W'] = 0 := by
    have e : H[fun z : (σ × 𝒰) × 𝒰 => z.1.2 | Prod.snd ; gpJoint p ρ x W'] =
        H[Prod.snd | Prod.snd ; gpJoint p ρ x W'] := by
      refine condEntropy_eq_of_dist_pair_eq hJ hJ ?_
      funext a
      simp only [dist]
      refine sum_congr rfl fun ω _ => ?_
      by_cases hω : gpJoint p ρ x W' ω = 0
      · simp [hω]
      · have hρω : ρ ω.1.1 ω.1.2 ≠ 0 := fun h => hω (by simp [gpJoint, jointOf, gpSU, h])
        have hWω : W' (x ω.1.2 ω.1.1, ω.1.1) ω.2 ≠ 0 := fun h =>
          hω (by simp [gpJoint, jointOf, gpChannel, h])
        have := hsupp _ _ _ hρω hWω
        simp only [pair, this]
    rw [e]
    exact condEntropy_comp_self hJ Prod.snd id
  rw [h0, sub_zero]

end GP

/-! ## Memory with defects -/

section Defects

/-- **Example (Lecture 7), page 7-27.** The memory with stuck-at faults: the state is `none` (no
fault), `some b` (stuck at `b`). -/
def defectChannel : Bool × Option Bool → Bool → ℝ
  | (x, none), y => if x = y then 1 else 0
  | (_, some b), y => if b = y then 1 else 0

/-- The state: no fault with probability `1 - p`, stuck at `0` or at `1` with probability `p/2`. -/
def defectState (p : ℝ) : Option Bool → ℝ
  | none => 1 - p
  | some _ => p / 2

lemma defectChannel_isChannel : IsChannel defectChannel := fun z => by
  obtain ⟨x, s⟩ := z
  cases s with
  | none =>
    refine ⟨fun y => by simp only [defectChannel]; split_ifs <;> norm_num, ?_⟩
    cases x <;> simp [defectChannel]
  | some b =>
    refine ⟨fun y => by simp only [defectChannel]; split_ifs <;> norm_num, ?_⟩
    cases b <;> simp [defectChannel]

lemma defectState_isPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsPMF (defectState p) := by
  refine ⟨fun s => ?_, ?_⟩
  · cases s with
    | none => simp only [defectState]; linarith
    | some b => simp only [defectState]; linarith
  · simp [defectState, Fintype.sum_option]
    ring

lemma defect_slice_none : (fun x => defectChannel (x, none)) = noiselessChannel := by
  funext x y
  rfl

/-- A stuck cell carries no information. -/
lemma mutualInfoOf_defect_some {q : Bool → ℝ} (hq : IsPMF q) (b : Bool) :
    mutualInfoOf q (fun x => defectChannel (x, some b)) = 0 := by
  have hW : IsChannel fun x => defectChannel (x, some b) := fun x => defectChannel_isChannel _
  rw [mutualInfoOf_eq_sum hq hW]
  have e : ∀ y, ∑ x, q x * defectChannel (x, some b) y = if b = y then 1 else 0 := fun y => by
    simp only [defectChannel, ← sum_mul, hq.sum_eq_one, one_mul]
  have e2 : ∀ x, entropy (defectChannel (x, some b)) = 0 := fun x => by
    rw [entropy_eq_sum_negMulLog]
    refine sum_eq_zero fun y _ => ?_
    simp only [defectChannel]
    split_ifs <;> simp
  simp_rw [e, e2]
  simp only [mul_zero, sum_const_zero, sub_zero]
  refine sum_eq_zero fun y _ => ?_
  split_ifs <;> simp

lemma capacity_defect_some (b : Bool) : capacity (fun x => defectChannel (x, some b)) = 0 := by
  have hW : IsChannel fun x => defectChannel (x, some b) := fun x => defectChannel_isChannel _
  obtain ⟨q, hq, hqC⟩ := exists_capacity_eq hW
  rw [← hqC, mutualInfoOf_defect_some hq]

/-- With the state at both ends, the capacity is `(1 - p) log 2` nats, that is `1 - p` bits. -/
lemma stateKnownValue_defect (p : ℝ) :
    stateKnownValue defectChannel (defectState p) = (1 - p) * log 2 := by
  simp only [stateKnownValue, Fintype.sum_option, Fintype.sum_bool, defectState,
    capacity_defect_some, mul_zero, add_zero, defect_slice_none, capacity_noiselessChannel.1]

/-- **Example (Lecture 7), page 7-29.** If neither the writer nor the reader knows the fault
locations, the channel is a BSC(`p/2`), and the capacity is `1 - H(p/2)` bits/cell. -/
theorem stateCapacity_defect_none_false {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    stateCapacity defectChannel (defectState p) .none false =
      (log 2 - binEntropy (p / 2)) / log 2 := by
  rw [stateCapacity_none_false defectChannel_isChannel (defectState_isPMF h0 h1)]
  have e : strategyChannel defectChannel (defectState p) (fun x _ => x) = bsc (p / 2) := by
    funext x y
    cases x <;> cases y <;>
      simp [strategyChannel, defectState, Fintype.sum_option, defectChannel, bsc] <;> ring
  rw [e, (capacity_bsc (by linarith) (by linarith)).1]

/-- **Example (Lecture 7), page 7-29.** If both the writer and the reader know the fault locations,
the capacity is `1 - p` bits/cell, causally or noncausally. -/
theorem stateCapacity_defect_causal_true {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    stateCapacity defectChannel (defectState p) .causal true = 1 - p := by
  rw [stateCapacity_causal_true defectChannel_isChannel (defectState_isPMF h0 h1),
    stateKnownValue_defect, mul_div_assoc, div_self (log_pos one_lt_two).ne', mul_one]

theorem stateCapacity_defect_noncausal_true {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    stateCapacity defectChannel (defectState p) .noncausal true = 1 - p := by
  rw [stateCapacity_noncausal_true defectChannel_isChannel (defectState_isPMF h0 h1),
    stateKnownValue_defect, mul_div_assoc, div_self (log_pos one_lt_two).ne', mul_one]

/-- **Example (Lecture 7), page 7-29.** If the reader knows the fault locations (an erasure
channel), the capacity is also `1 - p` bits/cell. -/
theorem stateCapacity_defect_none_true {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    stateCapacity defectChannel (defectState p) .none true = 1 - p := by
  have hs := defectState_isPMF h0 h1
  have hl := log_pos one_lt_two
  have hV := strategyOutChannel_isChannel defectChannel_isChannel hs
    (fun (x : Bool) (_ : Option Bool) => x)
  rw [stateCapacity_none_true defectChannel_isChannel hs]
  have hform : ∀ {q : Bool → ℝ}, IsPMF q → mutualInfoOf q
      (strategyOutChannel defectChannel (defectState p) fun x _ => x) =
      (1 - p) * mutualInfoOf q noiselessChannel := fun {q} hq => by
    rw [mutualInfoOf_strategyOutChannel defectChannel_isChannel hs _ hq]
    have e : (dist q fun u : Bool => u) = q := dist_id q
    simp only [e, Fintype.sum_option, Fintype.sum_bool, defectState, mutualInfoOf_defect_some hq,
      mul_zero, add_zero, defect_slice_none]
  have hC : capacity (strategyOutChannel defectChannel (defectState p) fun x _ => x) =
      (1 - p) * log 2 := by
    refine le_antisymm ?_ ?_
    · obtain ⟨q, hq, hqC⟩ := exists_capacity_eq hV
      rw [← hqC, hform hq]
      have := mutualInfoOf_le_capacity hq noiselessChannel_isChannel
      rw [capacity_noiselessChannel.1] at this
      exact mul_le_mul_of_nonneg_left this (by linarith)
    · have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
      have := mutualInfoOf_le_capacity hu hV
      rwa [hform hu, capacity_noiselessChannel.2, capacity_noiselessChannel.1] at this
  rw [hC, mul_div_assoc, div_self hl.ne', mul_one]

/-- The choice of the notes: `U = X ∼ Bern(1/2)` if there is no fault, and `U = X = S` if the cell
is stuck. -/
def defectAux : Option Bool → Bool → ℝ
  | none, _ => 1 / 2
  | some b, u => if b = u then 1 else 0

lemma defectAux_isPMF (s : Option Bool) : IsPMF (defectAux s) := by
  cases s with
  | none => exact ⟨fun _ => by norm_num [defectAux], by norm_num [defectAux]⟩
  | some b =>
    refine ⟨fun u => by simp only [defectAux]; split_ifs <;> norm_num, ?_⟩
    cases b <;> simp [defectAux]

/-- **Example (Lecture 7), page 7-31.** For this choice, `I(U; Y) - I(U; S) = H(U | S) = 1 - p`
bits. -/
theorem gpRate_defect {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    gpRate (defectState p) defectAux (fun u _ => u) defectChannel = (1 - p) * log 2 := by
  rw [gpRate_eq_of_output_eq (defectState_isPMF h0 h1) defectAux_isPMF defectChannel_isChannel ?_]
  · have e1 : entropy (defectAux none) = log 2 := by
      rw [entropy_eq_sum_negMulLog]
      simp only [Fintype.sum_bool, defectAux]
      exact sum_bool_mul_entropy_half
    have e2 : ∀ b, entropy (defectAux (some b)) = 0 := fun b => by
      rw [entropy_eq_sum_negMulLog]
      refine sum_eq_zero fun u _ => ?_
      simp only [defectAux]
      split_ifs <;> simp
    simp [Fintype.sum_option, defectState, e1, e2]
  · intro s u y hρ hW
    cases s with
    | none =>
      simp only [defectChannel] at hW
      by_contra h
      exact hW (by simp [Ne.symm h])
    | some b =>
      simp only [defectAux] at hρ
      simp only [defectChannel] at hW
      have hb : b = u := by
        by_contra h
        exact hρ (by simp [h])
      by_contra h
      exact hW (by simp [hb, Ne.symm h])

/-- **Example (Lecture 7), page 7-29.** Even if only the writer knows the fault locations, we can
reliably store `1 - p` bits/cell (Kuznetsov–Tsybakov). -/
theorem stateCapacity_defect_noncausal_false {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    stateCapacity defectChannel (defectState p) .noncausal false = 1 - p := by
  have hs := defectState_isPMF h0 h1
  rw [stateCapacity_noncausal_false defectChannel_isChannel hs]
  have h : gpValue defectChannel (defectState p) = (1 - p) * log 2 := by
    refine le_antisymm ?_ ?_
    · rw [← stateKnownValue_defect]
      exact gpValue_le_stateKnownValue defectChannel_isChannel hs
    · rw [← gpRate_defect h0 h1]
      exact gpRate_le_gpValue hs defectAux_isPMF defectChannel_isChannel _
  rw [h, mul_div_assoc, div_self (log_pos one_lt_two).ne', mul_one]

end Defects

/-! ## The BSC with additive state -/

section AdditiveBSC

/-- **Example (Lecture 7), page 7-43.** The BSC with additive Bernoulli state:
`Y = X ⊕ S ⊕ Z`, with `Z ∼ Bern(P)`. -/
def additiveBSC (P : ℝ) : Bool × Bool → Bool → ℝ := fun z => bsc P (xor z.1 z.2)

variable {P : ℝ} {q : Bool → ℝ}

lemma additiveBSC_isChannel (h0 : 0 ≤ P) (h1 : P ≤ 1) : IsChannel (additiveBSC P) :=
  fun _ => bsc_isChannel h0 h1 _

/-- The state known at both ends gives at most `1 - H(P)` bits. -/
lemma stateKnownValue_additiveBSC_le (h0 : 0 ≤ P) (h1 : P ≤ 1) (hq : IsPMF q) :
    stateKnownValue (additiveBSC P) q ≤ log 2 - binEntropy P := by
  have hb := bsc_isChannel h0 h1
  have hC : ∀ s, capacity (fun x => additiveBSC P (x, s)) ≤ log 2 - binEntropy P := fun s => by
    have hV : IsChannel fun x => additiveBSC P (x, s) := fun x => hb _
    obtain ⟨r, hr, hrC⟩ := exists_capacity_eq hV
    rw [← hrC, ← (capacity_bsc h0 h1).1]
    exact mutualInfoOf_comp_le_capacity hr hb fun x => xor x s
  calc stateKnownValue (additiveBSC P) q ≤ ∑ s, q s * (log 2 - binEntropy P) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hC s) (hq.nonneg s)
    _ = log 2 - binEntropy P := by rw [← sum_mul, hq.sum_eq_one, one_mul]

/-- With `X = U ⊕ S` the channel from `U` is the BSC, so that the causal value is at least
`1 - H(P)` bits. -/
lemma le_causalValue_additiveBSC (h0 : 0 ≤ P) (h1 : P ≤ 1) (hq : IsPMF q) :
    log 2 - binEntropy P ≤ causalValue (additiveBSC P) q := by
  have hW := additiveBSC_isChannel h0 h1
  rw [causalValue_eq_capacity hW hq]
  have hV := strategyChannel_isChannel hW hq fun f : Bool → Bool => f
  have e : strategyChannel (additiveBSC P) q (fun u s => xor u s) = bsc P := by
    funext u y
    simp only [strategyChannel, additiveBSC, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    rw [← sum_mul, hq.sum_eq_one, one_mul]
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  have h := mutualInfoOf_comp_le_capacity hu hV fun u s => xor u s
  rw [← strategyChannel_eq_comp, e, (capacity_bsc h0 h1).2, (capacity_bsc h0 h1).1] at h
  exact h

/-- The values with the state causally, noncausally and at both ends all equal `1 - H(P)` bits. -/
lemma additiveBSC_values (h0 : 0 ≤ P) (h1 : P ≤ 1) (hq : IsPMF q) :
    causalValue (additiveBSC P) q = log 2 - binEntropy P ∧
      gpValue (additiveBSC P) q = log 2 - binEntropy P := by
  have hW := additiveBSC_isChannel h0 h1
  have a := le_causalValue_additiveBSC h0 h1 hq
  have b := causalValue_le_gpValue hW hq
  have c := gpValue_le_stateKnownValue hW hq
  have d := stateKnownValue_additiveBSC_le h0 h1 hq
  exact ⟨by linarith, by linarith⟩

/-- **Example (Lecture 7), page 7-43.** If the encoder knows the state causally, the capacity is
`C = 1 - H(P)` bits, as without the state. -/
theorem stateCapacity_additiveBSC_causal (h0 : 0 ≤ P) (h1 : P ≤ 1) (hq : IsPMF q) :
    stateCapacity (additiveBSC P) q .causal false = (log 2 - binEntropy P) / log 2 := by
  rw [stateCapacity_causal_false (additiveBSC_isChannel h0 h1) hq, (additiveBSC_values h0 h1 hq).1]

/-- **Example (Lecture 7), page 7-43.** If the encoder knows the state in advance, the capacity is
`C = 1 - H(P)` bits. -/
theorem stateCapacity_additiveBSC_noncausal (h0 : 0 ≤ P) (h1 : P ≤ 1) (hq : IsPMF q) :
    stateCapacity (additiveBSC P) q .noncausal false = (log 2 - binEntropy P) / log 2 := by
  rw [stateCapacity_noncausal_false (additiveBSC_isChannel h0 h1) hq,
    (additiveBSC_values h0 h1 hq).2]

end AdditiveBSC

/-! ## Writing on dirty paper -/

section Costa

/-- **Lecture 7, page 7-45.** `R(α) = I(U; Y) - I(U; S)` for `U = X + αS`, with `X ∼ N(0, P)`,
`S ∼ N(0, Q)`, `Z ∼ N(0, 1)`, as a formula. -/
def costaRate (P Q a : ℝ) : ℝ :=
  1 / 2 * log (P * (P + Q + 1) / (P * Q * (1 - a) ^ 2 + (P + a ^ 2 * Q)))

/-- **Lecture 7, page 7-46.** `α* = P/(P + 1)` gives `R(α*) = C(P)`, the best one can hope for. -/
theorem costaRate_opt {P Q : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) :
    costaRate P Q (P / (P + 1)) = gaussCap P := by
  have h1 : 0 < P + 1 := by linarith
  have hd : P * Q * (1 - P / (P + 1)) ^ 2 + (P + (P / (P + 1)) ^ 2 * Q) =
      P * (P + Q + 1) / (P + 1) := by
    field_simp
    ring
  have hne : P + Q + 1 ≠ 0 := by positivity
  rw [costaRate, hd, gaussCap]
  congr 2
  field_simp
  ring

/-- **Lecture 7, page 7-46.** `α*` maximizes `R(α)`, and `R(α) ≤ C(P)`. -/
theorem costaRate_le {P Q : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (a : ℝ) :
    costaRate P Q a ≤ gaussCap P := by
  have h1 : 0 < P + 1 := by linarith
  have hd0 : 0 < P * Q * (1 - a) ^ 2 + (P + a ^ 2 * Q) := by positivity
  have hnum : 0 < P * (P + Q + 1) := by positivity
  rw [costaRate, gaussCap]
  refine mul_le_mul_of_nonneg_left (log_le_log (div_pos hnum hd0) ?_) (by norm_num)
  rw [div_le_iff₀ hd0]
  have hkey : (P * (1 - a) - a) ^ 2 * Q ≥ 0 := by positivity
  nlinarith [hkey]

/-- **Lecture 7, page 7-44.** The state, unknown at both ends, acts as noise:
`C(P/(1 + Q)) ≤ C(P)`. -/
theorem gaussCap_noise_le {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    gaussCap (P / (1 + Q)) ≤ gaussCap P := by
  have h1 : 0 < 1 + Q := by linarith
  refine gaussCap_le_gaussCap (div_nonneg hP h1.le) ?_
  rw [div_le_iff₀ h1]
  nlinarith

/-- **Lecture 7, page 7-50.** The corner point of the region for the AWGN-MAC with state:
`C(P₁/(P₂ + 1)) + C(P₂) = C(P₁ + P₂)`. -/
theorem costa_mac_corner {P₁ P₂ : ℝ} (h₁ : 0 ≤ P₁) (h₂ : 0 ≤ P₂) :
    gaussCap (P₁ / (P₂ + 1)) + gaussCap P₂ = gaussCap (P₁ + P₂) := by
  have := gaussCap_add_gaussCap (N := 1) h₂ h₁ one_pos
  simp only [div_one] at this
  rw [add_comm, this, add_comm]

/-- **Lecture 7, page 7-50.** `α₂ = (1 - α₁) P₂/(P₂ + 1) = P₂/(P₁ + P₂ + 1)` for
`α₁ = P₁/(P₁ + P₂ + 1)`. -/
theorem costa_mac_alpha {P₁ P₂ : ℝ} (h₁ : 0 ≤ P₁) (h₂ : 0 ≤ P₂) :
    (1 - P₁ / (P₁ + P₂ + 1)) * P₂ / (P₂ + 1) = P₂ / (P₁ + P₂ + 1) := by
  have h : P₁ + P₂ + 1 ≠ 0 := by positivity
  have h' : P₂ + 1 ≠ 0 := by positivity
  field_simp
  ring

end Costa

/-! ## Index of numbered and named results -/

/-- **Theorem 1 (Lecture 7).** The capacity of the compound channel. -/
alias theorem_7_1 := compoundCapacity_eq

/-- **Theorem 3 (Lecture 7).** The capacity with the state causally at the encoder. -/
alias theorem_7_3 := stateCapacity_causal_false

/-- **The Gelfand–Pinsker theorem (Lecture 7).** The capacity with the state noncausally at the
encoder. -/
alias gelfand_pinsker_theorem := stateCapacity_noncausal_false

end InfoTheory.ElGamalKim
