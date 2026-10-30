/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Capacity
public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.ChannelCoding.Hamming
public import InfoTheoryLib.ChannelCoding.SourceChannel

/-!
# Cover & Thomas, Chapter 7: Channel Capacity

This file indexes the formalization of Chapter 7 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_7_2_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Channels.** A discrete memoryless channel is its transition matrix `W x y = p(y | x)`, with
  `IsChannel W`. Its capacity is `capacity W` and the input distribution is `p : α → ℝ`.
* **Codes.** The messages `1, …, M` are `0, …, M - 1 : Fin M`; codewords are `Fin n → α`.
* **Logarithms.** Logarithms are natural: capacities and rates are in nats per channel use. The
  book's capacities in bits are `C / log 2`, and its `(⌈2^{nR}⌉, n)` codes are our
  `(⌈e^{nR}⌉, n)` codes.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Introduction and 7.1 Examples of channel capacity
* Discrete channels and (7.1): `IsChannel`, `capacity` (`ChannelCoding.Capacity`).
* 7.1.1 Noiseless binary channel: `noiselessChannel`, `capacity_noiselessChannel` (here).
* 7.1.2 Noisy channel with nonoverlapping outputs: `nonoverlappingChannel`,
  `capacity_nonoverlappingChannel` (here).
* 7.1.3 Noisy typewriter: `typewriterChannel`, `capacity_typewriterChannel` (here).
* 7.1.4 Binary symmetric channel, (7.2)–(7.7): `bsc`, `capacity_bsc` (here).
* 7.1.5 Binary erasure channel, (7.8)–(7.16): `bec`, `mutualInfoOf_bec`, `capacity_bec` (here).

### 7.2 Symmetric channels
* (7.17), (7.23): `symmetricChannel_7_17`, `symmetricChannel_7_17_isSymmetric`,
  `capacity_symmetricChannel_7_17` (here).
* Definitions: `IsSymmetricChannel`, `IsWeaklySymmetric`, `IsSymmetricChannel.isWeaklySymmetric`
  (`ChannelCoding.Capacity`); (7.24): `weaklySymmetric_7_24`, `example_7_24` (here).
* Theorem 7.2.1, (7.19)–(7.22), (7.25): `capacity_of_isWeaklySymmetric`.

### 7.3 Properties of channel capacity
* Properties 1–3: `capacity_nonneg`, `capacity_le_log_card_input`, `capacity_le_log_card_output`.
* Properties 4–5: `continuousOn_mutualInfoOf`, `mutualInfoOf_concave_input`
  (`MutualInformation.Convexity`), and the maximum is attained: `exists_capacity_eq`.

### 7.5 Definitions
* (7.26)–(7.27): `channelExt`, `IsChannel.ext` (`ChannelCoding.Code`).
* Codes and (7.28)–(7.34): `ChannelCode`, `ChannelCode.condErrProb`, `ChannelCode.maxErrProb`,
  `ChannelCode.avgErrProb`, `ChannelCode.avgErrProb_le_maxErrProb`, `ChannelCode.errProb_jointLaw`
  (`ChannelCoding.Converse`).
* Achievable rates and the operational capacity: `IsAchievableRate`, `opCapacity`.

### 7.6 Jointly typical sequences
* (7.35)–(7.38): `jointIid`, `jointTypicalSet` (`ChannelCoding.JointTypicality`).
* Theorem 7.6.1 (joint AEP), (7.39)–(7.59): `tendsto_prob_jointTypicalSet`,
  `card_jointTypicalSet_le`, `prob_indep_jointTypicalSet_le`,
  `eventually_prob_indep_jointTypicalSet_ge`.

### 7.7 Channel coding theorem
* Random codes and joint typicality decoding, (7.60)–(7.79): `sum_iidPMF_eval`,
  `sum_iidPMF_eval₂`, `typicalDecode`, `sum_codebook_condErrProb_le`, `exists_code_avgErrProb_le`
  (`ChannelCoding.Achievability`).
* Throwing away the worst half, (7.80)–(7.81): `ChannelCode.exists_maxErrProb_le_two_mul`
  (`ChannelCoding.Code`).
* Theorem 7.7.1: `isAchievableRate_of_lt_capacity` (achievability),
  `IsAchievableRate.le_capacity` (converse), `opCapacity_eq_capacity` (`ChannelCoding.Converse`).

### 7.8 Zero-error codes
* (7.82)–(7.87): `ChannelCode.log_le_of_avgErrProb_eq_zero` (`ChannelCoding.Converse`).

### 7.9 Fano's inequality and the converse to the coding theorem
* (7.88): `ChannelCode.errProb_jointLaw` (`ChannelCoding.Converse`).
* Lemma 7.9.1: `ChannelCode.condEntropy_message_le`; Lemma 7.9.2: `mutualInfo_channelExt_le`.
* (7.98)–(7.105): `ChannelCode.one_sub_avgErrProb_mul_log_le`, `ChannelCode.avgErrProb_ge`,
  `IsAchievableRate.le_capacity`.

### 7.10 Equality in the converse to the channel coding theorem
* The noisy typewriter has a zero-error code of rate `log 13 = C`: `typewriterCode`,
  `typewriterCode_maxErrProb` (here).
* The binary symmetric channel has no zero-error code with two codewords:
  `bsc_maxErrProb_pos` (here).

### 7.11 Hamming codes
* (7.117), the table of codewords, the minimum distance and (7.118): `hammingH`, `hammingCode`,
  `card_hammingCode`, `hammingCode_eq`, `add_mem_hammingCode`, `three_le_hammingNorm`,
  `exists_hammingNorm_eq_three`, `three_le_hammingDist`, `mulVec_add_single`, `hammingDecode`,
  `hammingDecode_add_single`, `hammingDecode_of_mem`, `hammingCode_systematic`
  (`ChannelCoding.Hamming`).
* Figures 7.10–7.12, the Venn diagram: `example_7_11_venn` (here).

### 7.12 Feedback capacity
* Feedback codes and (7.119): `FeedbackCode`, `FeedbackCode.errProb`, `IsAchievableRateFB`,
  `fbCapacity` (`ChannelCoding.Converse`).
* (7.121)–(7.133): `IsAchievableRate.isAchievableRateFB`, `fbLaw`, `mutualInfo_fbLaw_succ_le`,
  `mutualInfo_fbLaw_le`, `FeedbackCode.one_sub_errProb_mul_log_le`.
* Theorem 7.12.1: `fbCapacity_eq_capacity`.

### 7.13 Source–channel separation theorem
* (7.136): `SourceChannelCode`, `SourceChannelCode.errProb` (`ChannelCoding.SourceChannel`).
* Sources satisfying the AEP: `StochasticProcess.HasTypicalSets`, `iidProcess_hasTypicalSets`.
* Theorem 7.13.1: `exists_sourceChannelCode` (achievability), `entropyRate_le_capacity`
  (converse), and for random encoders `randomErrProb`, `exists_errProb_le_randomErrProb`,
  `entropyRate_le_capacity_of_random`.

## Not formalized

* The figures other than Figures 7.10–7.12, and the informal preview of the coding theorem in
  Section 7.4.
* The algorithms for computing the capacity mentioned in Section 7.3 (Kuhn–Tucker conditions,
  Frank–Wolfe, and the Blahut–Arimoto algorithm of Section 10.8).
* The remark after Theorem 7.7.1 on the Kolmogorov complexity of the best code (Chapter 14).
* The strong converse, the conditions for equality in the converse of Section 7.10 beyond the two
  examples, the general Hamming codes with `2ˡ - 1` symbols, repetition codes, parity check
  codes, BCH, Reed–Solomon, convolutional, turbo and LDPC codes.
* The AEP for stationary ergodic sources (Section 16.8) and for irreducible Markov chains, which
  Theorem 7.13.1 takes as a hypothesis (`StochasticProcess.HasTypicalSets`); i.i.d. sources are
  covered.
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 7.1: Examples of channel capacity -/

/-- **Section 7.1.1.** The noiseless binary channel: the input is reproduced exactly. -/
def noiselessChannel : Bool → Bool → ℝ := fun x y => if x = y then 1 else 0

lemma noiselessChannel_isChannel : IsChannel noiselessChannel := fun x =>
  ⟨fun y => by unfold noiselessChannel; split_ifs <;> norm_num, by
    cases x <;> simp [noiselessChannel]⟩

/-- **Section 7.1.1.** The noiseless binary channel has capacity `log 2` nats, i.e. `1` bit,
achieved by the uniform input distribution. -/
theorem capacity_noiselessChannel :
    capacity noiselessChannel = log 2 ∧
      mutualInfoOf (uniformPMF Bool) noiselessChannel = capacity noiselessChannel := by
  have hs : IsWeaklySymmetric noiselessChannel := by
    refine ⟨fun x x' => ⟨if x = x' then 1 else Equiv.boolNot, fun y => ?_⟩, fun y y' => ?_⟩
    · cases x <;> cases x' <;> cases y <;> simp [noiselessChannel]
    · cases y <;> cases y' <;> simp [noiselessChannel]
  obtain ⟨h1, h2⟩ := capacity_of_isWeaklySymmetric noiselessChannel_isChannel hs true
  refine ⟨?_, h2⟩
  rw [h1]
  simp [entropy, noiselessChannel]

/-- **Section 7.1.2.** A noisy channel with nonoverlapping outputs: input `0` gives the outputs
`0, 1` with probabilities `1/2, 1/2`, and input `1` gives `2, 3` with probabilities
`1/3, 2/3`. -/
def nonoverlappingChannel : Fin 2 → Fin 4 → ℝ := ![![1 / 2, 1 / 2, 0, 0], ![0, 0, 1 / 3, 2 / 3]]

lemma nonoverlappingChannel_isChannel : IsChannel nonoverlappingChannel := fun x => by
  fin_cases x <;>
    exact ⟨fun y => by fin_cases y <;> norm_num [nonoverlappingChannel],
      by simp [nonoverlappingChannel, Fin.sum_univ_four]; norm_num⟩

/-- **Section 7.1.2.** The input is determined by the output, so `I(X; Y) = H(X)`. -/
theorem mutualInfoOf_nonoverlappingChannel {p : Fin 2 → ℝ} (hp : IsPMF p) :
    mutualInfoOf p nonoverlappingChannel = entropy p := by
  have hq := jointOf_isPMF hp nonoverlappingChannel_isChannel
  -- The decoder `g(y) = 0` for `y ∈ {0, 1}` and `1` for `y ∈ {2, 3}` never errs.
  set g : Fin 4 → Fin 2 := ![0, 0, 1, 1]
  have he : errProb (jointOf p nonoverlappingChannel) Prod.fst Prod.snd g = 0 := by
    classical
    simp only [errProb, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
    simp [g, jointOf, nonoverlappingChannel]
  have h0 := condEntropy_eq_zero_of_errProb_eq_zero hq Prod.fst Prod.snd g he
  rw [mutualInfoOf, mutualInfo_eq_entropy_sub_condEntropy hq, h0, sub_zero, entropyRV,
    dist_jointOf_fst nonoverlappingChannel_isChannel]

/-- **Section 7.1.2.** The noisy channel with nonoverlapping outputs has capacity `log 2` nats,
i.e. `1` bit: every transmitted bit can be recovered. -/
theorem capacity_nonoverlappingChannel : capacity nonoverlappingChannel = log 2 := by
  have hmax : mutualInfoOf (uniformPMF (Fin 2)) nonoverlappingChannel = log 2 := by
    rw [mutualInfoOf_nonoverlappingChannel uniformPMF_isPMF, entropy_uniformPMF, Fintype.card_fin]
    norm_num
  refine IsGreatest.csSup_eq ⟨⟨_, uniformPMF_isPMF, hmax⟩, fun _ ⟨p, hp, hc⟩ => ?_⟩
  rw [← hc, mutualInfoOf_nonoverlappingChannel hp]
  simpa using entropy_le_log_card hp

/-- **Section 7.1.3.** The noisy typewriter: each of the `26` letters is received unchanged or as
the next letter, each with probability `1/2`. -/
def typewriterChannel : Fin 26 → Fin 26 → ℝ := fun x y => if y = x ∨ y = x + 1 then 1 / 2 else 0

lemma card_typewriter (x : Fin 26) :
    (univ.filter fun y : Fin 26 => y = x ∨ y = x + 1).card = 2 := by
  revert x
  decide

lemma card_typewriter_col (y : Fin 26) :
    (univ.filter fun x : Fin 26 => y = x ∨ y = x + 1).card = 2 := by
  revert y
  decide

lemma typewriterChannel_isChannel : IsChannel typewriterChannel := fun x =>
  ⟨fun y => by unfold typewriterChannel; split_ifs <;> norm_num, by
    classical
    simp only [typewriterChannel, sum_ite, sum_const_zero, add_zero, sum_const, card_typewriter,
      nsmul_eq_mul]
    norm_num⟩

/-- **Section 7.1.3.** The noisy typewriter has capacity `log 26 - log 2 = log 13`: using every
alternate letter, `13` symbols are transmitted without error. -/
theorem capacity_typewriterChannel :
    capacity typewriterChannel = log 13 ∧
      mutualInfoOf (uniformPMF (Fin 26)) typewriterChannel = capacity typewriterChannel := by
  classical
  have hs : IsWeaklySymmetric typewriterChannel := by
    refine ⟨fun x x' => ⟨Equiv.addRight (x - x'), fun y => ?_⟩, fun y y' => ?_⟩
    · simp only [typewriterChannel, Equiv.coe_addRight]
      congr 1
      apply propext
      simp only [Fin.ext_iff, Fin.add_def, Fin.sub_def, Fin.val_one]
      omega
    · simp only [typewriterChannel, sum_ite, sum_const_zero, add_zero, sum_const,
        card_typewriter_col]
  obtain ⟨h1, h2⟩ := capacity_of_isWeaklySymmetric typewriterChannel_isChannel hs 0
  have hrow : entropy (typewriterChannel 0) = log 2 := by
    rw [entropy_eq_sum_negMulLog]
    have : ∀ y, negMulLog (typewriterChannel 0 y) =
        if y = 0 ∨ y = 0 + 1 then negMulLog (1 / 2) else 0 := fun y => by
      simp only [typewriterChannel]; split_ifs <;> simp
    simp only [this, sum_ite, sum_const_zero, add_zero, sum_const, card_typewriter, nsmul_eq_mul]
    simp [negMulLog, log_inv]
  refine ⟨?_, h2⟩
  rw [h1, hrow, Fintype.card_fin, ← log_div (by norm_num) (by norm_num)]
  norm_num

/-- **Section 7.1.4.** The binary symmetric channel with crossover probability `p`. -/
def bsc (p : ℝ) : Bool → Bool → ℝ := fun x y => if x = y then 1 - p else p

lemma bsc_isChannel {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsChannel (bsc p) := fun x =>
  ⟨fun y => by unfold bsc; split_ifs <;> linarith, by cases x <;> simp [bsc]⟩

/-- **Section 7.1.4, (7.2)–(7.7).** The binary symmetric channel has capacity
`log 2 - H(p)` nats, i.e. `C = 1 - H(p)` bits, achieved by the uniform input distribution. -/
theorem capacity_bsc {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    capacity (bsc p) = log 2 - binEntropy p ∧
      mutualInfoOf (uniformPMF Bool) (bsc p) = capacity (bsc p) := by
  have hs : IsWeaklySymmetric (bsc p) := by
    refine ⟨fun x x' => ⟨if x = x' then 1 else Equiv.boolNot, fun y => ?_⟩, fun y y' => ?_⟩
    · cases x <;> cases x' <;> cases y <;> simp [bsc]
    · cases y <;> cases y' <;> simp [bsc, add_comm]
  obtain ⟨hC, h2⟩ := capacity_of_isWeaklySymmetric (bsc_isChannel h0 h1) hs true
  refine ⟨?_, h2⟩
  rw [hC, entropy_eq_sum_negMulLog, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [bsc, Fintype.card_bool, add_comm]

/-- **Section 7.1.5.** The binary erasure channel: a fraction `a` of the bits is erased (output
`none`), the others are received correctly. -/
def bec (a : ℝ) : Bool → Option Bool → ℝ := fun x y =>
  match y with
  | none => a
  | some y => if x = y then 1 - a else 0

lemma bec_isChannel {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsChannel (bec a) := fun x =>
  ⟨fun y => by
    cases y with
    | none => exact h0
    | some y => simp only [bec]; split_ifs <;> linarith,
   by cases x <;> simp [bec, Fintype.sum_option]⟩

/-- **Section 7.1.5, (7.11)–(7.14).** With `π = Pr{X = 1}`, the binary erasure channel has
`H(Y) = H(a) + (1 - a) H(π)` and `I(X; Y) = (1 - a) H(π)`. -/
theorem mutualInfoOf_bec {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) {p : Bool → ℝ} (hp : IsPMF p) :
    mutualInfoOf p (bec a) = (1 - a) * binEntropy (p true) := by
  have hpf : p false = 1 - p true := by
    have := hp.sum_eq_one
    rw [Fintype.sum_bool] at this
    linarith
  rw [mutualInfoOf_eq hp (bec_isChannel h0 h1)]
  have hrow : ∀ x, entropy (bec a x) = binEntropy a := fun x => by
    rw [entropy_eq_sum_negMulLog, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    cases x <;> simp [bec, Fintype.sum_option, add_comm]
  simp only [hrow, ← sum_mul, hp.sum_eq_one, one_mul]
  rw [entropy_eq_sum_negMulLog, Fintype.sum_option, Fintype.sum_bool]
  simp only [outDist, Fintype.sum_bool, bec]
  simp only [Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, zero_add]
  have hs : p true + p false = 1 := by rw [hpf]; ring
  rw [← add_mul, hs, one_mul, negMulLog_mul, negMulLog_mul, hpf,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- **Section 7.1.5, (7.8)–(7.16).** The binary erasure channel has capacity `(1 - a) log 2`
nats, i.e. `C = 1 - a` bits, achieved by `π = 1/2`. -/
theorem capacity_bec {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    capacity (bec a) = (1 - a) * log 2 ∧
      mutualInfoOf (uniformPMF Bool) (bec a) = capacity (bec a) := by
  have hmax : mutualInfoOf (uniformPMF Bool) (bec a) = (1 - a) * log 2 := by
    rw [mutualInfoOf_bec h0 h1 uniformPMF_isPMF]
    simp [uniformPMF, binEntropy_two_inv]
  have hC : capacity (bec a) = (1 - a) * log 2 :=
    IsGreatest.csSup_eq ⟨⟨_, uniformPMF_isPMF, hmax⟩, fun _ ⟨p, hp, hc⟩ => by
      rw [← hc, mutualInfoOf_bec h0 h1 hp]
      exact mul_le_mul_of_nonneg_left binEntropy_le_log_two (by linarith)⟩
  exact ⟨hC, hmax.trans hC.symm⟩

/-! ## Section 7.2: Symmetric channels -/

/-- The first row `(0.3, 0.2, 0.5)` of the transition matrix (7.17); the matrix is circulant. -/
def row_7_17 : Fin 3 → ℝ := ![3 / 10, 1 / 5, 1 / 2]

/-- **(7.17)** The symmetric channel `p(y | x) = r(y - x)` with `r = (0.3, 0.2, 0.5)`. -/
def symmetricChannel_7_17 : Fin 3 → Fin 3 → ℝ := fun x y => row_7_17 (y - x)

/-- **(7.17)** The transition matrix of the symmetric channel. -/
lemma symmetricChannel_7_17_eq : symmetricChannel_7_17 =
    ![![3 / 10, 1 / 5, 1 / 2], ![1 / 2, 3 / 10, 1 / 5], ![1 / 5, 1 / 2, 3 / 10]] := by
  funext x y
  fin_cases x <;> fin_cases y <;> rfl

lemma symmetricChannel_7_17_isChannel : IsChannel symmetricChannel_7_17 := fun x =>
  ⟨fun y => by
      unfold symmetricChannel_7_17 row_7_17
      generalize y - x = z
      fin_cases z <;> norm_num,
    by
      unfold symmetricChannel_7_17
      rw [show (∑ y, row_7_17 (y - x)) = ∑ z, row_7_17 z from
        Equiv.sum_comp (Equiv.subRight x) row_7_17]
      simp [row_7_17, Fin.sum_univ_three]; norm_num⟩

/-- **Section 7.2.** The channel (7.17) is symmetric: its rows, and its columns, are permutations
of each other. -/
theorem symmetricChannel_7_17_isSymmetric : IsSymmetricChannel symmetricChannel_7_17 := by
  refine ⟨fun x x' => ⟨Equiv.addRight (x - x'), fun y => ?_⟩,
    fun y y' => ⟨Equiv.addRight (y - y'), fun x => ?_⟩⟩
  · simp only [symmetricChannel_7_17, Equiv.coe_addRight]
    congr 1
    simp only [Fin.ext_iff, Fin.add_def, Fin.sub_def]
    omega
  · simp only [symmetricChannel_7_17, Equiv.coe_addRight]
    congr 1
    simp only [Fin.ext_iff, Fin.add_def, Fin.sub_def]
    omega

/-- **(7.23)** The channel (7.17) has capacity `log 3 - H(0.5, 0.3, 0.2)`, achieved by the
uniform input distribution. -/
theorem capacity_symmetricChannel_7_17 :
    capacity symmetricChannel_7_17 = log 3 - entropy ![1 / 2, 3 / 10, 1 / 5] ∧
      mutualInfoOf (uniformPMF (Fin 3)) symmetricChannel_7_17 = capacity symmetricChannel_7_17 := by
  obtain ⟨h1, h2⟩ := capacity_of_isWeaklySymmetric symmetricChannel_7_17_isChannel
    symmetricChannel_7_17_isSymmetric.isWeaklySymmetric 1
  refine ⟨?_, h2⟩
  rw [h1, Fintype.card_fin]
  congr 3
  funext y
  fin_cases y <;> rfl

/-- **(7.24)** A weakly symmetric channel that is not symmetric. -/
def weaklySymmetric_7_24 : Fin 2 → Fin 3 → ℝ := ![![1 / 3, 1 / 6, 1 / 2], ![1 / 3, 1 / 2, 1 / 6]]

lemma weaklySymmetric_7_24_isChannel : IsChannel weaklySymmetric_7_24 := fun x => by
  fin_cases x <;>
    exact ⟨fun y => by fin_cases y <;> norm_num [weaklySymmetric_7_24],
      by simp [weaklySymmetric_7_24, Fin.sum_univ_three]; norm_num⟩

/-- **(7.24) and Theorem 7.2.1.** The channel (7.24) is weakly symmetric but not symmetric, and
its capacity is `log 3 - H(1/3, 1/6, 1/2)`. -/
theorem example_7_24 :
    IsWeaklySymmetric weaklySymmetric_7_24 ∧ ¬ IsSymmetricChannel weaklySymmetric_7_24 ∧
      capacity weaklySymmetric_7_24 = log 3 - entropy ![1 / 3, 1 / 6, 1 / 2] := by
  have hs : IsWeaklySymmetric weaklySymmetric_7_24 := by
    refine ⟨fun x x' => ⟨if x = x' then 1 else Equiv.swap 1 2, fun y => ?_⟩, fun y y' => ?_⟩
    · fin_cases x <;> fin_cases x' <;> fin_cases y <;>
        simp [weaklySymmetric_7_24, Equiv.swap_apply_def]
    · fin_cases y <;> fin_cases y' <;> simp [weaklySymmetric_7_24, Fin.sum_univ_two] <;> norm_num
  refine ⟨hs, fun ⟨_, hcol⟩ => ?_, ?_⟩
  · -- The column `(1/6, 1/2)` is not a permutation of the column `(1/3, 1/3)`.
    obtain ⟨τ, hτ⟩ := hcol 0 1
    have := hτ 0
    have h3 : ∀ x : Fin 2, weaklySymmetric_7_24 x 0 = 1 / 3 := fun x => by
      fin_cases x <;> rfl
    rw [h3] at this
    norm_num [weaklySymmetric_7_24] at this
  · rw [(capacity_of_isWeaklySymmetric weaklySymmetric_7_24_isChannel hs 0).1, Fintype.card_fin]
    rfl

/-! ## Section 7.10: Equality in the converse -/

/-- **Section 7.10, example 1.** For the noisy typewriter, the code using every alternate letter:
`13` codewords of block length `1`. -/
def typewriterCode : ChannelCode 13 1 (Fin 26) (Fin 26) where
  enc w _ := ⟨2 * w.val, by omega⟩
  dec y := ⟨(y 0).val / 2, by omega⟩

/-- **Section 7.10, example 1.** The alternate-letter code never errs, so the noisy typewriter
transmits `log 13 = C` nats per use with zero probability of error. -/
theorem typewriterCode_maxErrProb : typewriterCode.maxErrProb typewriterChannel = 0 := by
  classical
  have key : ∀ (w : Fin 13) (y : Fin 26), (⟨y.val / 2, by omega⟩ : Fin 13) ≠ w →
      ¬ (y = ⟨2 * w.val, by omega⟩ ∨ y = ⟨2 * w.val, by omega⟩ + 1) := by
    decide
  have h : ∀ w, typewriterCode.condErrProb typewriterChannel w = 0 := fun w => by
    refine sum_eq_zero fun y _ => ?_
    split_ifs with hne
    · have hc := key w (y 0) hne
      simp only [channelExt, Fin.prod_univ_one, typewriterChannel]
      exact ite_eq_right_iff.2 fun h => absurd h hc
    · rfl
  refine le_antisymm (ChannelCode.maxErrProb_le _ (by norm_num) fun w => (h w).le) ?_
  exact typewriterCode.maxErrProb_nonneg typewriterChannel_isChannel

/-- **Section 7.10, example 2.** Over a binary symmetric channel with `0 < p < 1`, every output
sequence has positive probability whatever the input, so no code with two or more codewords has
zero probability of error: the zero-error capacity of the BSC is zero. -/
theorem bsc_maxErrProb_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) {M n : ℕ} (hM : 2 ≤ M)
    (c : ChannelCode M n Bool Bool) : 0 < c.maxErrProb (bsc p) := by
  classical
  have hpos : ∀ x y, 0 < channelExt (bsc p) n x y := fun x y =>
    prod_pos fun i _ => by unfold bsc; split_ifs <;> linarith
  -- Pick an output `y₀` and a message `i` that `y₀` is not decoded to.
  set y₀ : Fin n → Bool := fun _ => false
  obtain ⟨i, hi⟩ : ∃ i : Fin M, c.dec y₀ ≠ i := by
    by_cases h : c.dec y₀ = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, h⟩
  have hlam : 0 < c.condErrProb (bsc p) i := by
    have := single_le_sum (f := fun y => if c.dec y ≠ i then channelExt (bsc p) n (c.enc i) y
      else 0) (fun y _ => by split_ifs <;> simp [(hpos _ _).le]) (mem_univ y₀)
    simp only [hi, ne_eq, not_false_eq_true, ↓reduceIte] at this
    exact (hpos _ _).trans_le this
  exact hlam.trans_le (c.condErrProb_le_maxErrProb i)

/-! ## Section 7.11: Hamming codes -/

open Matrix in
/-- **Figures 7.10–7.12 (the Venn diagram).** Label the three circles by the rows of `H`, and the
seven regions by the sets of circles containing them, so that position `j` of a codeword lies in
circle `r` iff `H r j = 1`. The parity checks `Hc = 0` say that every circle has even parity.
Positions `3, 5, 6, 7` are the four intersection regions, which carry the information bits, and
positions `1, 2, 4` are the regions inside a single circle, which carry the parity bits. Sending
`1101` in the intersection regions gives the codeword `0110011` (Figure 7.11). Changing the
information bit in position `3`, the intersection of the second and third circles only
(Figure 7.12), violates the parity of exactly these two circles: the syndrome is `011`, the third
column of `H`, and syndrome decoding restores the codeword. -/
theorem example_7_11_venn :
    (![0, 1, 1, 0, 0, 1, 1] : Fin 7 → ZMod 2) ∈ hammingCode ∧
      hammingH *ᵥ ((![0, 1, 1, 0, 0, 1, 1] : Fin 7 → ZMod 2) + Pi.single 2 1) = ![0, 1, 1] ∧
      hammingDecode ((![0, 1, 1, 0, 0, 1, 1] : Fin 7 → ZMod 2) + Pi.single 2 1) =
        ![0, 1, 1, 0, 0, 1, 1] := by
  have hc : (![0, 1, 1, 0, 0, 1, 1] : Fin 7 → ZMod 2) ∈ hammingCode := by decide
  refine ⟨hc, ?_, hammingDecode_add_single hc 2⟩
  rw [mulVec_add_single hc]
  decide

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 7.
-/

/-- **Theorem 7.2.1.** -/
alias theorem_7_2_1 := capacity_of_isWeaklySymmetric

/-- **Theorem 7.6.1 (Joint AEP), part 1.** -/
alias theorem_7_6_1_prob := tendsto_prob_jointTypicalSet

/-- **Theorem 7.6.1 (Joint AEP), part 2.** -/
alias theorem_7_6_1_card := card_jointTypicalSet_le

/-- **Theorem 7.6.1 (Joint AEP), part 3.** -/
alias theorem_7_6_1_indep := prob_indep_jointTypicalSet_le

/-- **Theorem 7.7.1 (The channel coding theorem), achievability.** -/
alias theorem_7_7_1 := isAchievableRate_of_lt_capacity

/-- **Theorem 7.7.1 (The channel coding theorem), converse.** -/
alias theorem_7_7_1_converse := IsAchievableRate.le_capacity

/-- **Lemma 7.9.1 (Fano's inequality).** `H(W | Ŵ) ≤ 1 + Pₑ^(n) nR` (in nats,
`log 2 + Pₑ^(n) log M`). -/
alias lemma_7_9_1 := ChannelCode.condEntropy_message_le

/-- **Lemma 7.9.2.** -/
alias lemma_7_9_2 := mutualInfo_channelExt_le

/-- **Theorem 7.12.1 (Feedback capacity).** -/
alias theorem_7_12_1 := fbCapacity_eq_capacity

/-- **Theorem 7.13.1 (Source–channel coding theorem), achievability.** -/
alias theorem_7_13_1 := exists_sourceChannelCode

/-- **Theorem 7.13.1 (Source–channel coding theorem), converse.** -/
alias theorem_7_13_1_converse := entropyRate_le_capacity

end InfoTheory.CoverThomas
