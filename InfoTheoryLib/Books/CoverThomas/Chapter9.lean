/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter7
public import InfoTheoryLib.GaussianChannel.Bandlimited
public import InfoTheoryLib.GaussianChannel.Feedback
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cover & Thomas, Chapter 9: Gaussian Channel

This file indexes the formalization of Chapter 9 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_9_1_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Channels.** The Gaussian channel is `Yᵢ = Xᵢ + Zᵢ` with `Zᵢ ∼ N(0, N)`. An input with density
  `f` (with respect to any σ-finite measure `μ`) gives the pair `(X, Y)` the joint density
  `noiseJointPDF f g` with respect to `μ × λ`, where `g` is the noise density, and
  `I(X; Y) = mutualInfoPDF μ volume (noiseJointPDF f g)`.
* **Codes.** The messages `1, …, M` are `0, …, M - 1 : Fin M`; codewords are vectors
  `Fin n → ℝ`, and the noise law is `noiseLaw N n = N(0, N)ⁿ`.
* **Logarithms.** Logarithms are natural: capacities and rates are in nats. The book's capacities
  in bits are `C / log 2`, and its `(2^{nR}, n)` codes are our `(⌈e^{nR}⌉, n)` codes.
* **Variances.** Variances and powers of normal distributions are nonnegative reals `ℝ≥0`, as in
  Mathlib's `gaussianReal`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Introduction
* (9.1)–(9.2): `noiseJointPDF` (`GaussianChannel.Basic`), `GaussianCode.SatisfiesPower`
  (`GaussianChannel.Code`).
* (9.3)–(9.7), binary signaling with `±√P`: `normalCDF`, `binarySignaling_errProb` (here); the
  resulting binary symmetric channel: `binarySignalingChannel`, `binarySignalingChannel_eq`,
  `capacity_binarySignalingChannel` (here).

### 9.1 Gaussian channel: definitions
* (9.8): `gaussianInfoCapacity` (`GaussianChannel.Capacity`).
* (9.9)–(9.16): `mutualInfoPDF_gaussianChannel_le`, `mutualInfoPDF_gaussianChannel_le_of_power`
  (`GaussianChannel.Capacity`), through the general bound `mutualInfoPDF_noiseJointPDF_le`
  (`GaussianChannel.Basic`).
* (9.17): `mutualInfoPDF_gaussianChannel_gaussian`, `marginalSnd_gaussianChannel_gaussian`,
  `gaussianInfoCapacity_eq`.
* (9.18)–(9.20), codes and achievable rates: `GaussianCode`, `GaussianCode.condErrProb`,
  `GaussianCode.maxErrProb`, `GaussianCode.avgErrProb`, `IsAchievableGaussianRate`,
  `gaussianOpCapacity` (`GaussianChannel.Code`).
* Theorem 9.1.1: `gaussianOpCapacity_eq`, `gaussianOpCapacity_eq_gaussianInfoCapacity`
  (`GaussianChannel.Achievability`).
* The sphere-packing remark (9.22): `sphere_packing_ratio` (here).
* Achievability, (9.23)–(9.34): random Gaussian codebooks `codebookLaw`, threshold decoding
  `thresholdDecode`, `thresholdCode_err_le`, `exists_gaussianCode_avgErrProb_le`,
  `isAchievableGaussianRate_of_lt`; throwing away the worse half of the codewords:
  `GaussianCode.exists_maxErrProb_le_two_mul`.

### 9.2 Converse to the coding theorem for Gaussian channels
* (9.35)–(9.53): `GaussianCode.msgLaw`, `GaussianCode.mutualInfo_msgLaw_le`,
  `GaussianCode.one_sub_avgErrProb_mul_log_le`, `IsAchievableGaussianRate.le`
  (`GaussianChannel.Converse`).

### 9.3 Bandlimited channels
* (9.54)–(9.57): `signalOfSpectrum`, `IsBandlimited` (`GaussianChannel.Bandlimited`).
* Theorem 9.3.1: `signalOfSpectrum_eq_of_samples`; (9.58): `sinc_two_pi_mul`.
* (9.60)–(9.62): `bandlimitedCapacity`, `bandlimitedCapacity_eq`; (9.63):
  `tendsto_bandlimitedCapacity`.
* Example 9.3.1: `example_9_3_1` (here).

### 9.4 Parallel Gaussian channels
* (9.64)–(9.67): `diagNoisePDF`, `parallelInfoCapacity` (`GaussianChannel.Parallel`).
* (9.68)–(9.71): `mutualInfoPDF_parallel_le`; (9.72): `mutualInfoPDF_parallel_gaussian`.
* (9.73)–(9.78), water-filling: `waterFill`, `exists_waterLevel`, `sum_log_le_waterFill`
  (`GaussianChannel.WaterFilling`), `mutualInfoPDF_parallel_le_waterFill`.
* (9.165): `parallelInfoCapacity_eq`, `exists_parallelInfoCapacity_eq`.

### 9.5 Channels with colored Gaussian noise
* (9.79)–(9.82): `coloredInfoCapacity`, `coloredInfoCapacity_eq_parallel`
  (`GaussianChannel.ColoredNoise`).
* (9.83)–(9.96): `det_add_le_prod_max`, `det_waterFill_add` (`GaussianChannel.ColoredNoise`), with
  Hadamard's inequality `det_le_prod_diag` (`DifferentialEntropy.MultivariateGaussian`).
* (9.105)–(9.106): `coloredInfoCapacity_eq`.

### 9.6 Gaussian channels with feedback
* (9.101)–(9.102): `secondMoment`, `secondMoment_mulVec_add`, `StrictlyLowerTriangular`,
  `capacityFB` (`GaussianChannel.Feedback`); (9.104)–(9.106): `capacityNoFB`, `capacityNoFB_eq`,
  `isGreatest_capacityNoFB` (`GaussianChannel.ColoredNoise`).
* Lemma 9.6.1: `secondMoment_add_add_sub`, and for `X = BZ + V`,
  `feedback_covariance_identity`.
* Lemma 9.6.2: `det_le_det_of_posSemidef_sub` (`ForMathlib.MatrixDet`).
* Lemma 9.6.3: `det_add_one_le_two_pow_mul`.
* Lemma 9.6.4: `det_rpow_mul_det_rpow_le` (`ForMathlib.MatrixDet`).
* Lemma 9.6.5, (9.143): `det_le_det_sub_one`.
* Theorem 9.6.2: `capacityFB_le_add`; Theorem 9.6.3: `capacityFB_le_two_mul`.

## Not formalized

* Figures 9.1–9.6, the chapter summary, the discussion of practical modems, DSL and turbo codes,
  and the prolate spheroidal functions (about `2TW` dimensions of almost time-limited, almost
  bandlimited signals) that justify the model of Section 9.3.
* The explicit interpolation formula (9.59) of the sampling theorem; its uniqueness statement,
  Theorem 9.3.1, is formalized.
* The capacity (9.97) of channels with stationary noise, water-filling in the spectral domain.
* Theorem 9.6.1 (the converse for Gaussian channels with feedback) and the characterizations
  (9.100) of `C_{n,FB}` and (9.104) of `C_n` as capacities: we take (9.102) and (9.104) as
  definitions, and prove Theorems 9.6.2 and 9.6.3 for them. The entropy inequality (9.142) of
  Lemma 9.6.5 is replaced by the determinant inequality (9.143) for `X = BZ + V`.

Deviations from the book's proofs are explained in the module docstrings: achievability uses
threshold decoding on the information density instead of joint typicality; the bounds on mutual
information compare the output with a normal density instead of using `h(Y)`; the colored-noise
channel is rotated into parallel channels; and Lemmas 9.6.2 and 9.6.4 are proved with the spectral
theorem.
-/

open Real MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Introduction: binary signaling -/

/-- **(9.7)** The cumulative normal function `Φ(x) = ∫_{-∞}^x φ(t) dt`. -/
def normalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Iic x)

/-- `N(0, N)` is `√N Z₀` for `Z₀ ∼ N(0, 1)`. -/
lemma gaussianReal_eq_map_sqrt {N : ℝ≥0} :
    gaussianReal 0 N = (gaussianReal 0 1).map (√(N : ℝ) * ·) := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp

/-- `Pr{Z > a} = 1 - Φ(a/√N)` for `Z ∼ N(0, N)`. -/
lemma gaussianReal_real_Ioi {N : ℝ≥0} (hN : N ≠ 0) (a : ℝ) :
    (gaussianReal 0 N).real (Ioi a) = 1 - normalCDF (a / √(N : ℝ)) := by
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [gaussianReal_eq_map_sqrt, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  have e : (√(N : ℝ) * ·) ⁻¹' Ioi a = (Iic (a / √(N : ℝ)))ᶜ := by
    ext z
    simp only [mem_preimage, mem_Ioi, mem_compl_iff, mem_Iic, not_le]
    rw [div_lt_iff₀ hs, mul_comm]
  rw [e, measureReal_compl measurableSet_Iic, probReal_univ, normalCDF]

/-- `N(0, N)` is symmetric: `Pr{Z ∈ S} = Pr{-Z ∈ S}`. -/
lemma gaussianReal_real_neg {N : ℝ≥0} {S : Set ℝ} (hS : MeasurableSet S) :
    (gaussianReal 0 N).real S = (gaussianReal 0 N).real ((fun z => -z) ⁻¹' S) := by
  conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg]
  rw [map_measureReal_apply (by fun_prop) hS]

/-- `N(0, N)` has no atoms. -/
lemma gaussianReal_singleton {N : ℝ≥0} (hN : N ≠ 0) (a : ℝ) : gaussianReal 0 N {a} = 0 :=
  gaussianReal_absolutelyContinuous 0 hN (measure_singleton a)

/-- **(9.3)–(9.6)** Sending one of the two levels `±√P`, equally likely, and deciding by the sign
of the output, the probability of error is
`Pₑ = ½ Pr{Y < 0 | X = √P} + ½ Pr{Y > 0 | X = -√P} = Pr{Z > √P} = 1 - Φ(√(P/N))`. -/
theorem binarySignaling_errProb {N : ℝ≥0} (hN : N ≠ 0) (P : ℝ≥0) :
    1 / 2 * (gaussianReal 0 N).real {z | √(P : ℝ) + z < 0} +
        1 / 2 * (gaussianReal 0 N).real {z | 0 < -√(P : ℝ) + z} =
      1 - normalCDF (√((P : ℝ) / N)) := by
  have h1 : (gaussianReal 0 N).real {z | √(P : ℝ) + z < 0} =
      (gaussianReal 0 N).real (Ioi √(P : ℝ)) := by
    rw [gaussianReal_real_neg (measurableSet_lt (by fun_prop) measurable_const)]
    congr 1
    ext z
    simp only [mem_preimage, mem_ofPred_eq, mem_Ioi]
    constructor <;> intro h <;> linarith
  have h2 : {z : ℝ | 0 < -√(P : ℝ) + z} = Ioi √(P : ℝ) := by
    ext z
    simp only [mem_ofPred_eq, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [h1, h2, gaussianReal_real_Ioi hN, ← Real.sqrt_div' _ (NNReal.coe_nonneg N)]
  ring

/-- The binary symmetric channel obtained from the Gaussian channel by sending `±√P` for the
two input bits and deciding by the sign of the output. -/
def binarySignalingChannel (P N : ℝ≥0) (b b' : Bool) : ℝ :=
  (gaussianReal 0 N).real {z | decide (0 < (if b then √(P : ℝ) else -√(P : ℝ)) + z) = b'}

/-- **Section 9 (introduction).** Binary signaling converts the Gaussian channel into a binary
symmetric channel with crossover probability `Pₑ = 1 - Φ(√(P/N))`. -/
theorem binarySignalingChannel_eq {N : ℝ≥0} (hN : N ≠ 0) (P : ℝ≥0) :
    binarySignalingChannel P N = bsc (1 - normalCDF (√((P : ℝ) / N))) := by
  set a := √(P : ℝ)
  have hPe : (gaussianReal 0 N).real (Ioi a) = 1 - normalCDF (√((P : ℝ) / N)) := by
    rw [gaussianReal_real_Ioi hN, ← Real.sqrt_div' _ (NNReal.coe_nonneg N)]
  -- `Pr{Z ≤ -a} = Pr{Z ≥ a} = Pr{Z > a}`.
  have hle : (gaussianReal 0 N).real (Iic (-a)) = (gaussianReal 0 N).real (Ioi a) := by
    rw [gaussianReal_real_neg measurableSet_Iic]
    have e : (fun z : ℝ => -z) ⁻¹' Iic (-a) = Ioi a ∪ {a} := by
      ext z
      simp only [mem_preimage, mem_Iic, neg_le_neg_iff, mem_union, mem_Ioi, mem_singleton_iff]
      constructor
      · intro h
        rcases h.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
      · rintro (h | rfl)
        · exact h.le
        · exact le_rfl
    have h0 : (gaussianReal 0 N).real {a} = 0 := by
      rw [measureReal_def, gaussianReal_singleton hN, ENNReal.toReal_zero]
    rw [e, measureReal_union (by simp) (measurableSet_singleton a), h0, add_zero]
  have hcompl : ∀ S : Set ℝ, MeasurableSet S →
      (gaussianReal 0 N).real Sᶜ = 1 - (gaussianReal 0 N).real S := fun S hS => by
    rw [measureReal_compl hS, probReal_univ]
  funext b b'
  cases b <;> cases b'
  · -- `-a + Z ≤ 0`, that is `Z ≤ a`.
    have e : {z : ℝ | decide (0 < -a + z) = false} = (Ioi a)ᶜ := by
      ext z
      simp only [mem_ofPred_eq, decide_eq_false_iff_not, mem_compl_iff, mem_Ioi]
      constructor <;> intro h <;> linarith
    simp only [binarySignalingChannel, Bool.false_eq_true, ↓reduceIte, bsc]
    rw [e, hcompl _ measurableSet_Ioi, hPe]
  · have e : {z : ℝ | decide (0 < -a + z) = true} = Ioi a := by
      ext z
      simp only [mem_ofPred_eq, decide_eq_true_eq, mem_Ioi]
      constructor <;> intro h <;> linarith
    simp only [binarySignalingChannel, Bool.false_eq_true, ↓reduceIte, bsc]
    rw [e, hPe]
  · have e : {z : ℝ | decide (0 < a + z) = false} = Iic (-a) := by
      ext z
      simp only [mem_ofPred_eq, decide_eq_false_iff_not, mem_Iic, not_lt]
      constructor <;> intro h <;> linarith
    simp only [binarySignalingChannel, ↓reduceIte, bsc]
    rw [e, hle, hPe]
    simp
  · have e : {z : ℝ | decide (0 < a + z) = true} = (Iic (-a))ᶜ := by
      ext z
      simp only [mem_ofPred_eq, decide_eq_true_eq, mem_compl_iff, mem_Iic, not_le]
      constructor <;> intro h <;> linarith
    simp only [binarySignalingChannel, ↓reduceIte, bsc]
    rw [e, hcompl _ measurableSet_Iic, hle, hPe]

/-- The capacity of the binary symmetric channel obtained by binary signaling is
`log 2 - H(Pₑ)` nats, `1 - H(Pₑ)` bits. -/
theorem capacity_binarySignalingChannel {N : ℝ≥0} (hN : N ≠ 0) (P : ℝ≥0) :
    capacity (binarySignalingChannel P N) =
      log 2 - binEntropy (1 - normalCDF (√((P : ℝ) / N))) := by
  have hPe : 1 - normalCDF (√((P : ℝ) / N)) = (gaussianReal 0 N).real (Ioi √(P : ℝ)) := by
    rw [gaussianReal_real_Ioi hN, ← Real.sqrt_div' _ (NNReal.coe_nonneg N)]
  have h0 : 0 ≤ 1 - normalCDF (√((P : ℝ) / N)) := by rw [hPe]; exact measureReal_nonneg
  have h1 : 1 - normalCDF (√((P : ℝ) / N)) ≤ 1 := by rw [hPe]; exact measureReal_le_one
  rw [binarySignalingChannel_eq hN]
  exact (capacity_bsc h0 h1).1

/-! ## Section 9.1: the sphere-packing argument -/

/-- **(9.22) Sphere packing.** The received vectors lie in a ball of radius `√(n(P + N))`, and a
decoding ball has radius `√(nN)`. The ratio of their volumes is
`(n(P + N))^{n/2}/(nN)^{n/2} = e^{n · ½ log (1 + P/N)} = e^{nC}`, so at most about `e^{nC}`
nonintersecting decoding balls fit. -/
theorem sphere_packing_ratio {n : ℕ} (hn : 0 < n) {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) √(n * (P + N)))).toReal /
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) √(n * N))).toReal =
      exp (n * (1 / 2 * log (1 + P / N))) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hV0 : V.toReal ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨(Metric.measure_ball_pos _ _ one_pos).ne', measure_ball_lt_top.ne⟩
  rw [Measure.addHaar_ball _ _ (sqrt_nonneg _), Measure.addHaar_ball _ _ (sqrt_nonneg _),
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    mul_div_mul_right _ _ hV0, ← div_pow, ← Real.sqrt_div' _ (by positivity),
    show (n : ℝ) * (P + N) / (n * N) = 1 + P / N by field_simp; ring]
  have hx : 0 < 1 + P / N := by positivity
  rw [← exp_log (pow_pos (sqrt_pos.2 hx) n), log_pow, log_sqrt hx.le]
  ring_nf

/-! ## Section 9.3: Example 9.3.1 -/

/-- **Example 9.3.1 (Telephone line).** With bandwidth `W = 3300` Hz and signal-to-noise ratio
`P/(N₀W) = 2000` (about `33` dB), the capacity (9.62) of the telephone channel is
`3300 log₂ 2001 ≈ 36,000` bits per second. -/
theorem example_9_3_1 :
    bandlimitedCapacity 3300 (2000 * 3300) 1 = 3300 * log 2001 ∧
      36000 < 3300 * logb 2 2001 ∧ 3300 * logb 2 2001 < 36300 ∧
      33 < 10 * logb 10 2000 ∧ 10 * logb 10 2000 < 33.1 := by
  have h2 : (1 : ℝ) < 2 := one_lt_two
  have h10 : (1 : ℝ) < 10 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [bandlimitedCapacity]
    norm_num
  · have : (120 / 11 : ℝ) < logb 2 2001 := by
      rw [lt_logb_iff_rpow_lt h2 (by norm_num),
        ← pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (11 : ℕ) ≠ 0),
        ← rpow_natCast, ← rpow_mul (by norm_num),
        show (120 / 11 : ℝ) * ((11 : ℕ) : ℝ) = ((120 : ℕ) : ℝ) by norm_num, rpow_natCast]
      norm_num
    linarith
  · have : logb 2 2001 < 11 := by
      rw [logb_lt_iff_lt_rpow h2 (by norm_num), show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num,
        rpow_natCast]
      norm_num
    linarith
  · have : (33 / 10 : ℝ) < logb 10 2000 := by
      rw [lt_logb_iff_rpow_lt h10 (by norm_num),
        ← pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (10 : ℕ) ≠ 0),
        ← rpow_natCast, ← rpow_mul (by norm_num),
        show (33 / 10 : ℝ) * ((10 : ℕ) : ℝ) = ((33 : ℕ) : ℝ) by norm_num, rpow_natCast]
      norm_num
    linarith
  · -- `log₁₀ 2000 = 3 + log₁₀ 2` and `log₁₀ 2 < 0.31`.
    have h3 : logb 10 2000 = 3 + logb 10 2 := by
      rw [show (2000 : ℝ) = 10 ^ (3 : ℕ) * 2 by norm_num, logb_mul (by positivity) (by norm_num),
        logb_pow, logb_self_eq_one h10]
      norm_num
    have : logb 10 2 < 31 / 100 := by
      rw [logb_lt_iff_lt_rpow h10 (by norm_num),
        ← pow_lt_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (100 : ℕ) ≠ 0),
        ← rpow_natCast (10 ^ _), ← rpow_mul (by norm_num),
        show (31 / 100 : ℝ) * ((100 : ℕ) : ℝ) = ((31 : ℕ) : ℝ) by norm_num, rpow_natCast]
      norm_num
    rw [h3]
    linarith

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 9.
-/

/-- **Theorem 9.1.1.** The capacity of the Gaussian channel is `½ log (1 + P/N)`. -/
alias theorem_9_1_1 := gaussianOpCapacity_eq

/-- **Theorem 9.1.1 (achievability), Section 9.1.** -/
alias theorem_9_1_1_achievability := isAchievableGaussianRate_of_lt

/-- **Theorem 9.1.1 (converse), Section 9.2.** -/
alias theorem_9_1_1_converse := IsAchievableGaussianRate.le

/-- **Theorem 9.3.1 (Nyquist–Shannon sampling theorem).** -/
alias theorem_9_3_1 := signalOfSpectrum_eq_of_samples

/-- **Lemma 9.6.1.** -/
alias lemma_9_6_1 := secondMoment_add_add_sub

/-- **Lemma 9.6.2.** -/
alias lemma_9_6_2 := det_le_det_of_posSemidef_sub

/-- **Lemma 9.6.3.** -/
alias lemma_9_6_3 := det_add_one_le_two_pow_mul

/-- **Lemma 9.6.4.** -/
alias lemma_9_6_4 := det_rpow_mul_det_rpow_le

/-- **Lemma 9.6.5, (9.143).** -/
alias lemma_9_6_5 := det_le_det_sub_one

/-- **Theorem 9.6.2.** `C_{n,FB} ≤ C_n + ½` bit. -/
alias theorem_9_6_2 := capacityFB_le_add

/-- **Theorem 9.6.3.** `C_{n,FB} ≤ 2 C_n`. -/
alias theorem_9_6_3 := capacityFB_le_two_mul

end InfoTheory.CoverThomas
