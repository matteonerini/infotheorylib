/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter9
public import InfoTheoryLib.RateDistortion.Binary
public import InfoTheoryLib.RateDistortion.ParallelGaussian
public import InfoTheoryLib.RateDistortion.SourceChannel
public import InfoTheoryLib.RateDistortion.BlahutArimoto
public import InfoTheoryLib.AEP.StrongTypicality

/-!
# Cover & Thomas, Chapter 10: Rate Distortion Theory

This file indexes the formalization of Chapter 10 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_10_2_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Sources and distortions.** A source is a pmf `p : α → ℝ` on a finite alphabet, the
  reproduction alphabet is a finite type `β`, and a distortion measure is any
  `d : α → β → ℝ`, assumed nonnegative (`∀ x y, 0 ≤ d x y`) where needed. Finite alphabets make
  every distortion measure bounded (10.3).
* **Test channels.** A conditional distribution `p(x̂|x)` is a channel `q : α → β → ℝ`
  (`IsChannel q`), with `I(X; X̂) = mutualInfoOf p q`.
* **Codes and rates.** The indices `1, …, 2^{nR}` are `0, …, M - 1 : Fin M`. Rates are in nats: a
  code of rate `R` has `⌊e^{nR}⌋` codewords, the book's `(2^{nR}, n)` codes with `R` in bits. A
  pair `(R, D)` is achievable if a sequence of such codes has `limsup E d(Xⁿ, X̂ⁿ) ≤ D`.
* **Continuous sources.** For Gaussian sources we compute the information rate distortion
  function, an infimum of `I(X; X̂)` over joint densities, as the book does.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 10.1 Quantization
* (10.1), the one-bit quantizer of a `N(0, σ²)` variable and its distortion `(π - 2)/π σ²`
  (Problem 10.1): `oneBitQuantizer`, `integral_abs_mul_gaussianPDFReal`, `oneBit_distortion`,
  `oneBit_distortion_optimal` (here).
* The first property of optimal quantizers, mapping each source sequence to the closest
  reproduction: `nearestEncode`, `distortion_nearestCode_le` (here).

### 10.2 Definitions
* (10.2)–(10.6): distortion measures `d : α → β → ℝ`, `maxDistortion`, `hammingDistortion`,
  `seqDistortion` (`RateDistortion.Basic`); the Hamming distortion is the probability of error:
  `sum_mul_hammingDistortion` (here); the squared-error distortion (10.5) appears in
  `RateDistortion.Gaussian`.
* (10.7)–(10.10): `RDCode`, `RDCode.distortion`.
* Achievable pairs, the rate distortion region, the rate distortion and distortion rate
  functions: `IsAchievableRD`, `rdRegion`, `rateDistortion`, `distortionRate`.
* (10.11): `infoRD`, `expDistortion`, `minDistortion`; the minimum is attained:
  `exists_infoRD_eq`.
* Theorem 10.2.1: `rateDistortion_eq_infoRD`, with the rate distortion region `rdRegion_eq` and
  `distortionRate_eq` (`RateDistortion.Theorem`).

### 10.3 Calculation of the rate distortion function
* Theorem 10.3.1: `infoRD_bernoulli` (`RateDistortion.Binary`); (10.15)–(10.19):
  `binEntropy_sub_le_mutualInfoOf`; (10.20)–(10.22): `infoRD_bernoulli_le`; Figure 10.4, the
  Bernoulli(1/2) source: `infoRD_bernoulli_half` (here).
* (10.25): `gaussianInfoRD` (`RateDistortion.Gaussian`); (10.26)–(10.33):
  `half_log_div_le_mutualInfoPDF`, through the bound `integral_mul_log_div_le_mutualInfoPDF`;
  (10.34)–(10.35): `gaussianTestPDF`, `mutualInfoPDF_gaussianTest`,
  `integral_gaussianTestPDF_mul_sq`.
* Theorem 10.3.2: `gaussianInfoRD_eq`; (10.37): `gaussianInfoRD_le_iff`; one bit of description
  gives the distortion `σ²/4`, less than the `(π - 2)/π σ²` of one-bit quantization:
  `gaussianInfoRD_quarter`, `quarter_lt_oneBit_distortion` (here).
* (10.38): `parallelInfoRD` (`RateDistortion.ParallelGaussian`); (10.39)–(10.44):
  `sum_le_mutualInfoPDF_parallel`, `sum_half_log_le_mutualInfoPDF_parallel`, with the test
  channels `parallelTestPDF`, `mutualInfoPDF_parallelTest`; (10.45)–(10.50):
  `half_log_revWaterFill_add_le`, `sum_half_log_revWaterFill_le`; (10.52): `revWaterFill`,
  `exists_revWaterLevel`.
* Theorem 10.3.3: `parallelInfoRD_eq`.

### 10.4 Converse to the rate distortion theorem
* Lemma 10.4.1: `infoRD_antitoneOn`, `infoRD_convexOn` (`RateDistortion.Basic`).
* (10.58)–(10.71): `RDCode.mul_infoRD_le_log`, through `mul_infoRD_le_mutualInfo`,
  `sum_mutualInfo_le_of_indepFamily` (`RateDistortion.Converse`) and `infoRD_le_mutualInfo`
  (`RateDistortion.Basic`);
  the converse `IsAchievableRD.infoRD_le`, using the closedness of the epigraph,
  `infoRD_le_of_tendsto`.
* Theorem 10.4.1: `LossySourceChannelCode`, `IsAchievableSCDistortion`,
  `IsAchievableSCDistortion.infoRD_le_capacity`, `isAchievableSCDistortion_of_infoRD_lt`, with
  the concatenated code `concatCode` (`RateDistortion.SourceChannel`).

### 10.5 Achievability of the rate distortion function
* (10.72)–(10.75): `distortionTypicalSet` (`RateDistortion.Achievability`).
* Lemma 10.5.1: `tendsto_prob_distortionTypicalSet`; Lemma 10.5.2:
  `channelExt_mul_exp_le_iidPMF`; Lemma 10.5.3: `one_sub_mul_pow_le`.
* Encoding and decoding: `typicalEncode`, `typicalRDCode`; (10.89)–(10.101):
  `sum_codebook_distortion_le`; achievability: `isAchievableRD_of_infoRD_lt`.
* (10.103)–(10.104): `sphere_packing_ratio` (`Books.CoverThomas.Chapter9`); (10.105):
  `sphere_covering_ratio` (here).

### 10.6 Strongly typical sequences and rate distortion
* (10.106)–(10.107): `symbolCount`, `strongTypicalSet`, `jointStrongTypicalSet`,
  `mem_strongTypicalSet_of_mem_joint` (`AEP.StrongTypicality`).
* Lemma 10.6.1: `tendsto_prob_strongTypicalSet`, `tendsto_prob_jointStrongTypicalSet`.

### 10.7 Characterization of the rate distortion function
* (10.116)–(10.124), the optimal test channel for a fixed output distribution, by the Gibbs
  variational principle: `neg_log_sum_le_relEntropyReal_add`, `relEntropyReal_gibbs_add`
  (`RelativeEntropy.Gibbs`), `baChannel`, `baObjective_baChannel_le`
  (`RateDistortion.BlahutArimoto`).

### 10.8 Computation of channel capacity and the rate distortion function
* Lemma 10.8.1: `mutualInfoOf_le_relEntropy_jointOf_prodDist`, with (10.134)–(10.138)
  `relEntropy_jointOf_prodDist_eq`; (10.132)–(10.133): `posterior`,
  `sum_mul_log_div_le_mutualInfoOf`, `sum_mul_log_posterior_eq`.
* (10.140)–(10.141): `infoRD_eq_sInf_relEntropy`; (10.142)–(10.143): `baObjective`,
  `baObjective_baChannel_le`, `baObjective_outDist_le`; the Blahut–Arimoto iteration `baIter`
  decreases the Lagrangian: `baObjective_iter_antitone`.
* (10.144)–(10.147), the capacity: (10.145) follows from `sum_mul_log_div_le_mutualInfoOf` and
  `sum_mul_log_posterior_eq`, and (10.147) is `sum_mul_sub_log_le_log_sum_exp`
  (`RelativeEntropy.Gibbs`).

## Not formalized

* Figures 10.1–10.9 and the chapter summary; the Lloyd algorithm beyond its first step, and the
  second property of optimal quantizers (centroid reproduction points); the Itakura–Saito
  distance.
* The rate distortion theorem for continuous alphabets, assumed by the book in Section 10.3.2:
  we compute the information rate distortion functions of Gaussian sources. Likewise, reverse
  water-filling on the eigenvalues for a general multivariate normal source, and on the spectrum
  for a Gaussian process, are only mentioned by the book.
* Lemma 10.6.2 with the book's strongly typical sets (proved in the book only as Problem 10.16) and
  the achievability proof of Section 10.6 based on it, which shows that most source sequences have
  small distortion; the achievability of Section 10.5 is formalized. The form of the lemma with
  robust typicality is the joint typicality lemma (`Typicality.JointTypicalityLemma`).
* The Kuhn–Tucker conditions (10.125)–(10.129), and the convergence of the Blahut–Arimoto
  algorithm to `R(D)` (due to Csiszár) and of the analogous algorithm for the capacity.
-/

open Real MeasureTheory ProbabilityTheory Set Filter Finset Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 10.1: quantization -/

/-- `∫_0^∞ x e^{-bx²} dx = 1/(2b)`. -/
lemma integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi 0, x * exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => -(2 * b)⁻¹ * exp (-b * x ^ 2))
      (x * exp (-b * x ^ 2)) x := fun x _ => by
    convert ((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹) using 1
    field_simp
    ring
  have hlim : Tendsto (fun x => -(2 * b)⁻¹ * exp (-b * x ^ 2)) atTop (𝓝 (-(2 * b)⁻¹ * 0)) :=
    (tendsto_exp_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (neg_lt_zero.2 hb))).const_mul _
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_mul_exp_neg_mul_sq hb).integrableOn hlim]
  simp

/-- **(10.1)** For `X ∼ N(0, σ²)`, `E|X| = σ √(2/π)`. -/
lemma integral_abs_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => |x| * gaussianPDFReal 0 v x) ∧
      ∫ x, |x| * gaussianPDFReal 0 v x = √(2 * v / π) := by
  have hv' : (0 : ℝ) < v := by positivity
  set c := (√(2 * π * v))⁻¹
  set b := (2 * (v : ℝ))⁻¹
  have hb : 0 < b := by positivity
  have hφ : ∀ x, gaussianPDFReal 0 v x = c * exp (-b * x ^ 2) := fun x => by
    rw [gaussianPDFReal_def]
    simp only [c, b, sub_zero]
    ring_nf
  have hf : (fun x => |x| * gaussianPDFReal 0 v x) = fun x => |x| * (c * exp (-b * |x| ^ 2)) :=
    funext fun x => by rw [hφ, sq_abs]
  refine ⟨?_, ?_⟩
  · refine ((integrable_mul_exp_neg_mul_sq hb).norm.const_mul c).congr
      (Eventually.of_forall fun x => ?_)
    change c * ‖x * exp (-b * x ^ 2)‖ = |x| * gaussianPDFReal 0 v x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (exp_pos _).le, hφ]
    ring
  · rw [hf, integral_comp_abs (f := fun t => t * (c * exp (-b * t ^ 2)))]
    simp_rw [mul_left_comm _ c]
    rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hb]
    simp only [c, b]
    rw [show (2 * π * v : ℝ) = (2 * v) * π by ring, sqrt_mul (by positivity),
      show (2 * v / π : ℝ) = (2 * v) / π by ring, sqrt_div' _ (by positivity)]
    have h1 : 0 < √(2 * (v : ℝ)) := sqrt_pos.2 (by positivity)
    have h2 : 0 < √π := sqrt_pos.2 pi_pos
    have h3 : √(2 * (v : ℝ)) ^ 2 = 2 * v := sq_sqrt (by positivity)
    field_simp
    nlinarith [h3]

/-- **(10.1)** The one-bit quantizer with reproduction points `±a`: `x̂(x) = a` if `x ≥ 0` and
`-a` if `x < 0`. -/
def oneBitQuantizer (a x : ℝ) : ℝ := if 0 ≤ x then a else -a

lemma sub_oneBitQuantizer_sq (a x : ℝ) :
    (x - oneBitQuantizer a x) ^ 2 = x ^ 2 - 2 * a * |x| + a ^ 2 := by
  unfold oneBitQuantizer
  split_ifs with h
  · rw [abs_of_nonneg h]; ring
  · rw [abs_of_neg (not_le.1 h)]; ring

/-- **Problem 10.1.** The distortion of the one-bit quantizer with points `±a` for `X ∼ N(0, σ²)`
is `E(X - x̂(X))² = σ² - 2a σ √(2/π) + a²`. -/
theorem oneBit_distortion {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    ∫ x, gaussianPDFReal 0 v x * (x - oneBitQuantizer a x) ^ 2 =
      v - 2 * a * √(2 * v / π) + a ^ 2 := by
  obtain ⟨i1, e1⟩ := integral_abs_mul_gaussianPDFReal hv
  have i2 := integrable_gaussianPDFReal_mul_sq_zero hv
  have i0 := integrable_gaussianPDFReal 0 v
  have e : (fun x => gaussianPDFReal 0 v x * (x - oneBitQuantizer a x) ^ 2) =
      fun x => gaussianPDFReal 0 v x * x ^ 2 - 2 * a * (|x| * gaussianPDFReal 0 v x) +
        a ^ 2 * gaussianPDFReal 0 v x := funext fun x => by
    rw [sub_oneBitQuantizer_sq]; ring
  have hA : Integrable fun x => gaussianPDFReal 0 v x * x ^ 2 - 2 * a *
      (|x| * gaussianPDFReal 0 v x) := i2.sub (i1.const_mul _)
  rw [e, integral_add hA (i0.const_mul _), integral_sub i2 (i1.const_mul _), integral_const_mul,
    integral_const_mul, integral_gaussianPDFReal_mul_sq_zero hv, e1,
    integral_gaussianPDFReal_eq_one 0 hv, mul_one]

/-- **(10.1), Problem 10.1.** The best reproduction points of the one-bit quantizer are
`±σ √(2/π)`, the conditional means of the half-lines, and the distortion is `(π - 2)/π σ²`. -/
theorem oneBit_distortion_optimal {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal 0 v x * (x - oneBitQuantizer √(2 * v / π) x) ^ 2 = (π - 2) / π * v ∧
      ∀ a, (π - 2) / π * v ≤ ∫ x, gaussianPDFReal 0 v x * (x - oneBitQuantizer a x) ^ 2 := by
  have hsq : √(2 * v / π) ^ 2 = 2 * v / π := sq_sqrt (by positivity)
  have hval : (v : ℝ) - √(2 * v / π) ^ 2 = (π - 2) / π * v := by
    rw [hsq]; field_simp
  refine ⟨?_, fun a => ?_⟩
  · rw [oneBit_distortion hv, ← hval]
    ring
  · rw [oneBit_distortion hv, ← hval]
    nlinarith [sq_nonneg (a - √(2 * v / π))]

/-- **Section 10.1, the nearest-neighbor condition.** Mapping each source sequence to the index of
a closest reproduction sequence. -/
def nearestEncode {α β : Type*} {M n : ℕ} [NeZero M]
    (d : α → β → ℝ) (dec : Fin M → Fin n → β) (x : Fin n → α) : Fin M :=
  (Finite.exists_min fun w => seqDistortion d x (dec w)).choose

/-- **Section 10.1.** Given the reproduction points, the distortion is minimized by mapping each
source sequence to the closest reproduction point. -/
theorem distortion_nearestCode_le {α β : Type*} [Fintype α] {M n : ℕ} [NeZero M]
    {p : α → ℝ} (hp : IsPMF p) (d : α → β → ℝ) (c : RDCode M n α β) :
    (⟨nearestEncode d c.dec, c.dec⟩ : RDCode M n α β).distortion p d ≤ c.distortion p d :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    ((Finite.exists_min fun w => seqDistortion d x (c.dec w)).choose_spec (c.enc x))
    (iidPMF_nonneg hp.nonneg x)

/-! ## Section 10.2: the Hamming distortion -/

open Classical in
/-- **(10.4)** With the Hamming distortion, `E d(X, X̂) = Pr{X ≠ X̂}`. -/
theorem sum_mul_hammingDistortion {Ω α : Type*} [Fintype Ω] (μ : Ω → ℝ) (X Y : Ω → α) :
    ∑ ω, μ ω * hammingDistortion (X ω) (Y ω) = prob μ (univ.filter fun ω => X ω ≠ Y ω) := by
  rw [prob, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : X ω = Y ω <;> simp [hammingDistortion, h]

/-! ## Section 10.3: examples -/

/-- **Figure 10.4.** For a Bernoulli(1/2) source, `R(D) = log 2 - H(D)` for `0 ≤ D ≤ 1/2` (one
bit minus `H(D)` bits), and `0` for `D > 1/2`. -/
theorem infoRD_bernoulli_half {D : ℝ} (hD0 : 0 ≤ D) :
    infoRD (bernoulliPMF (1 / 2)) hammingDistortion D =
      if D ≤ 1 / 2 then log 2 - binEntropy D else 0 := by
  rw [infoRD_bernoulli (by norm_num) (by norm_num) hD0,
    show min (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 by norm_num, one_div, binEntropy_two_inv]

/-- **Section 10.3.2.** One bit of description (`R = log 2` nats) of a `N(0, σ²)` source achieves
the distortion `σ²/4`: `R(σ²/4) = log 2`. -/
theorem gaussianInfoRD_quarter {S : ℝ≥0} (hS : S ≠ 0) : gaussianInfoRD S (S / 4) = log 2 := by
  have hS' : (0 : ℝ) < S := by positivity
  have hle : S / 4 ≤ S := by
    rw [← NNReal.coe_le_coe, NNReal.coe_div]
    push_cast
    linarith
  rw [gaussianInfoRD_eq hS (by positivity)]
  simp only [hle, ↓reduceIte]
  rw [NNReal.coe_div, show ((4 : ℝ≥0) : ℝ) = 4 by norm_num, div_div_cancel₀ hS'.ne',
    show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  ring

/-- **Section 10.3.2.** The distortion `σ²/4` of the best description with one bit per symbol is
less than the distortion `(π - 2)/π σ² ≈ 0.3633 σ²` of one-bit quantization of each symbol. -/
theorem quarter_lt_oneBit_distortion {v : ℝ} (hv : 0 < v) : v / 4 < (π - 2) / π * v := by
  have h := pi_gt_three
  rw [div_mul_eq_mul_div, lt_div_iff₀ pi_pos]
  nlinarith

/-! ## Section 10.5: sphere covering -/

/-- **(10.105) Sphere covering.** A source sequence lies in a ball of radius `√(nσ²)`, and is
represented within distortion `D` by the codewords whose balls of radius `√(nD)` cover it. The
ratio of the volumes is `(nσ²)^{n/2}/(nD)^{n/2} = e^{n · ½ log (σ²/D)} = e^{nR(D)}`, so at least
about `e^{nR(D)}` codewords are needed. -/
theorem sphere_covering_ratio {n : ℕ} (hn : 0 < n) {S D : ℝ} (hS : 0 < S) (hD : 0 < D) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) √(n * S))).toReal /
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) √(n * D))).toReal =
      exp (n * (1 / 2 * log (S / D))) := by
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
    show (n : ℝ) * S / (n * D) = S / D by field_simp]
  have hx : 0 < S / D := by positivity
  rw [← exp_log (pow_pos (sqrt_pos.2 hx) n), log_pow, log_sqrt hx.le]
  ring_nf

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 10.
-/

/-- **Theorem 10.2.1 (The rate distortion theorem).** `R(D) = R^(I)(D)`. -/
alias theorem_10_2_1 := rateDistortion_eq_infoRD

/-- **Theorem 10.2.1 (achievability).** Every `(R, D)` with `R > R(D)` is achievable. -/
alias theorem_10_2_1_achievability := isAchievableRD_of_infoRD_lt

/-- **Theorem 10.2.1 (converse).** Every achievable `(R, D)` has `R ≥ R(D)`. -/
alias theorem_10_2_1_converse := IsAchievableRD.infoRD_le

/-- **Theorem 10.3.1.** The rate distortion function of a Bernoulli source. -/
alias theorem_10_3_1 := infoRD_bernoulli

/-- **Theorem 10.3.2.** The rate distortion function of a Gaussian source. -/
alias theorem_10_3_2 := gaussianInfoRD_eq

/-- **Theorem 10.3.3.** Reverse water-filling for independent Gaussian sources. -/
alias theorem_10_3_3 := parallelInfoRD_eq

/-- **Lemma 10.4.1 (convexity of `R(D)`).** `R(D)` is convex. -/
alias lemma_10_4_1 := infoRD_convexOn

/-- **Lemma 10.4.1.** `R(D)` is nonincreasing. -/
alias lemma_10_4_1_antitone := infoRD_antitoneOn

/-- **Theorem 10.4.1 (Source–channel separation with distortion).** If `R(D) < C`, the
distortion `D` is achievable. -/
alias theorem_10_4_1 := isAchievableSCDistortion_of_infoRD_lt

/-- **Theorem 10.4.1 (converse).** If the distortion `D` is achievable, `R(D) ≤ C`. -/
alias theorem_10_4_1_converse := IsAchievableSCDistortion.infoRD_le_capacity

/-- **Lemma 10.5.1.** `Pr{A_{d,ε}^(n)} → 1`. -/
alias lemma_10_5_1 := tendsto_prob_distortionTypicalSet

/-- **Lemma 10.5.2.** `p(x̂ⁿ) ≥ p(x̂ⁿ | xⁿ) e^{-n(I(X; X̂)+3ε)}` on the distortion typical set. -/
alias lemma_10_5_2 := channelExt_mul_exp_le_iidPMF

/-- **Lemma 10.5.3.** `(1 - xy)ⁿ ≤ 1 - x + e^{-yn}`. -/
alias lemma_10_5_3 := one_sub_mul_pow_le

/-- **Lemma 10.6.1.** `Pr{A_ε^{*(n)}} → 1`. -/
alias lemma_10_6_1 := tendsto_prob_jointStrongTypicalSet

/-- **Lemma 10.8.1.** The output distribution minimizes `D(p(x) p(y|x) ‖ p(x) r(y))`. -/
alias lemma_10_8_1 := mutualInfoOf_le_relEntropy_jointOf_prodDist

/-- **Lemma 10.8.1, (10.132).** The posterior maximizes `∑ p(x) p(y|x) log (r(x|y)/p(x))`. -/
alias lemma_10_8_1_posterior := sum_mul_log_div_le_mutualInfoOf

end InfoTheory.CoverThomas
