/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter10
public import InfoTheoryLib.Books.CoverThomas.Chapter7
public import InfoTheoryLib.ChannelCoding.Cost
public import InfoTheoryLib.ChannelCoding.Product
public import InfoTheoryLib.GaussianChannel.AWGN
public import InfoTheoryLib.GaussianChannel.Bandlimited
public import InfoTheoryLib.GaussianChannel.Parallel
public import InfoTheoryLib.RateDistortion.Binary
public import InfoTheoryLib.RateDistortion.BitRate
public import InfoTheoryLib.RateDistortion.Gaussian
public import InfoTheoryLib.RateDistortion.SourceChannel
public import InfoTheoryLib.SourceCoding.LosslessRate
public import InfoTheoryLib.Typicality.Covering
public import InfoTheoryLib.Typicality.Packing

/-!
# El Gamal & Kim, Lecture 3: Point-to-Point Information Theory

This file indexes the formalization of Lecture 3 of [elgamal2010] and contains the lecture's
worked examples, with aliases named after its results. The lecture proves Shannon's
point-to-point theorems with the robust typicality of Lecture 2, and isolates the packing and
covering lemmas that later lectures use repeatedly.

## Conventions

* **Logarithms and rates.** The notes measure rates in bits; the library's logarithms are
  natural, so a capacity or rate–distortion function in bits is the quantity in nats divided by
  `log 2`. Information quantities such as `capacity W` and `infoRD p d D` are in nats.
* **Codes.** A `(2^{nR}, n)` channel code has message set `[1 : 2^{nR}] = {1, …, 2^⌈nR⌉}`: a
  `ChannelCode (2 ^ ⌈n R⌉₊) n 𝒳 𝒴`. A `(2^{nR}, n)` source code has index set
  `[1 : 2^{nR}) = {1, …, 2^⌊nR⌋}`: an `RDCode (2 ^ ⌊n R⌋₊) n 𝒳 𝒳̂`. Messages and indices are
  `0, …, M - 1`. The decoder of a `ChannelCode` always outputs a message: the notes' error symbol
  `e` can be replaced by any message without increasing the probability of error.
* **Typicality.** As in `Books.ElGamalKim.Lecture2`; the triple `(U, X, Y)` is a pair of pairs.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Channel coding
* The DMC `(𝒳, p(y|x), 𝒴)`: `IsChannel` (`Probability.Channel`); the memoryless property
  without feedback, `p(yⁿ|xⁿ, m) = ∏ᵢ p(yᵢ|xᵢ)`: `channelExt` (`ChannelCoding.Code`), and with
  feedback `fbLaw` (`ChannelCoding.Converse`).
* A `(2^{nR}, n)` code, `λ_m(𝒞)` and `P_e^(n)(𝒞)`: `ChannelCode`, `ChannelCode.condErrProb`,
  `ChannelCode.avgErrProb` (`ChannelCoding.Code`); the uniform message:
  `ChannelCode.jointLaw`, `ChannelCode.errProb_jointLaw` (`ChannelCoding.Converse`).
* Achievable rates and the capacity: `IsAchievableRateAvg`, `opCapacityAvg`
  (`ChannelCoding.AverageError`).
* Shannon's channel coding theorem `C = max_{p(x)} I(X; Y)`: `opCapacityAvg_eq`, with
  `capacity` and `exists_capacity_eq` (`ChannelCoding.Capacity`).
* The BSC, `C = 1 - H(p)`: `example_bsc` (here); the BEC, `C = 1 - p`: `example_bec` (here).
* The product DMC, `C = C₁ + C₂`: `prodChannel`, `capacity_prodChannel`
  (`ChannelCoding.Product`).
* Achievability: `isAchievableRateAvg_of_lt`, derived from Cover and Thomas's random coding
  proof `isAchievableRate_of_lt_capacity` (`ChannelCoding.Achievability`).
* Remarks: the maximal and the average probability of error give the same capacity,
  `ChannelCode.exists_maxErrProb_le_two_mul` (`ChannelCoding.Code`), `opCapacity_eq_capacity`
  (`ChannelCoding.Converse`).
* The weak converse: `IsAchievableRateAvg.le_capacity_div`, through Fano's inequality
  `ChannelCode.condEntropy_message_le` and the steps `I(M; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`,
  `mutualInfo_fbLaw_succ_le_mutualInfoOf` (`ChannelCoding.Converse`), which also hold with
  feedback.

### Packing lemma
* The packing lemma: `prob_exists_mem_robustTypicalSet_le`, and for `|𝒜| ≤ 2^{nR}`
  `prob_exists_mem_robustTypicalSet_le_exp` (`Typicality.Packing`).

### Channel coding with cost
* The cost constraint and the capacity: `ChannelCode.SatisfiesCost`, `IsAchievableRateCost`,
  `opCapacityCost` (`ChannelCoding.Cost`).
* Theorem 2, `C(B) = max_{p(x) : E b(X) ≤ B} I(X; Y)`: `capacityCost`,
  `exists_capacityCost_eq`, `opCapacityCost_eq`, with achievability
  `isAchievableRateCost_of_lt` and converse `IsAchievableRateCost.le`,
  `ChannelCode.one_sub_avgErrProb_mul_log_le_capacityCost`.
* `C(B)` is nondecreasing, concave and continuous: `monotoneOn_capacityCost`,
  `concaveOn_capacityCost`, `continuousOn_capacityCost` (for `B > 0`).

### Additive white Gaussian noise channel
* The AWGN channel `Y = gX + Z` with power constraint `P` and received SNR `S = g²P`:
  `GaussianCode`, `GaussianCode.SatisfiesPower` (`GaussianChannel.Code`), `GaussianCode.scale`,
  `IsAchievableAWGNRate`, `opCapacityAWGN`, `receivedPower` (`GaussianChannel.AWGN`).
* Theorem 3, `C = C(S)`: `opCapacityAWGN_eq`, with `gaussianCapacityFun`; achievability
  `isAchievableAWGNRate_of_lt` and converse `IsAchievableAWGNRate.le`, derived from Cover and
  Thomas's `gaussianOpCapacity_eq` (`GaussianChannel.Achievability`).
* `I(X; Y) = C(S)` for `X ∼ N(0, P)`: `mutualInfoPDF_gaussianChannel_gaussian`
  (`GaussianChannel.Capacity`).
* The bandlimited channel, `C = W C(S)` and its wideband limit: `bandlimitedCapacity`,
  `bandlimitedCapacity_eq`, `tendsto_bandlimitedCapacity` (`GaussianChannel.Bandlimited`), in
  Cover and Thomas's normalization.

### Gaussian product channel
* The parallel Gaussian channel and water-filling: `parallelInfoCapacity`,
  `parallelInfoCapacity_eq`, `exists_parallelInfoCapacity_eq`,
  `mutualInfoPDF_parallel_le_waterFill` (`GaussianChannel.Parallel`), with noise powers `1/g_j²`.

### Lossless source coding
* A `(2^{nR}, n)` source code, `P_e^(n)`, achievable rates and `R*`: `RDCode`
  (`RateDistortion.Basic`), `RDCode.blockErrProb`, `IsAchievableLosslessRate`,
  `optLosslessRate` (`SourceCoding.LosslessRate`).
* Shannon's lossless source coding theorem `R* = H(X)`: `optLosslessRate_eq`, with achievability
  `isAchievableLosslessRate_of_lt` and converse `IsAchievableLosslessRate.le`,
  `RDCode.mul_entropy_le`.
* The `Bern(p)` source: `optLosslessRate_bernoulli` (here).
* Error-free compression with variable-length codes: Cover and Thomas's Theorems 5.3.1,
  5.4.1 and 5.4.2, `entropyBase_le_expectedLength`, `minExpectedLength_bounds` and
  `tendsto_minExpectedLength` (`SourceCoding.OptimalLength`).

### Lossy source coding
* Distortion measures, `d(xⁿ, x̂ⁿ)`, codes and their distortion: `hammingDistortion`,
  `seqDistortion`, `RDCode`, `RDCode.distortion` (`RateDistortion.Basic`).
* Achievable pairs and `R(D)`: `IsAchievableRDBits`, `rateDistortionBits`
  (`RateDistortion.BitRate`).
* Shannon's lossy source coding theorem `R(D) = min I(X; X̂)` for `D ≥ D_min`:
  `rateDistortionBits_eq`, with `infoRD`, `minDistortion` (`RateDistortion.Basic`);
  achievability `isAchievableRDBits_of_lt` and converse `IsAchievableRDBits.infoRD_div_le`.
* `R(D)` is nonincreasing and convex: `infoRD_antitoneOn`, `infoRD_convexOn`
  (`RateDistortion.Basic`).
* The `Bern(p)` source with Hamming distortion, `R(D) = H(p) - H(D)` for `D < p`:
  `rateDistortionBits_bernoulli` (here), from `infoRD_bernoulli` (`RateDistortion.Binary`).
* Lossless source coding revisited, `R* = R(0)`: `optLosslessRate_eq_rateDistortionBits_zero`
  (here), from `minDistortion_hammingDistortion` and `infoRD_hammingDistortion_zero`
  (`RateDistortion.BitRate`).

### Covering lemma
* The covering lemma: `prob_forall_not_mem_robustTypicalSet_le`, and asymptotically
  `eventually_prob_forall_not_mem_robustTypicalSet_le` (`Typicality.Covering`).

### Quadratic Gaussian source coding
* Theorem 6, `R(D) = R(P/D)`, in its informational form: `gaussianInfoRD`,
  `gaussianInfoRD_eq_gaussianRateFun` (`RateDistortion.Gaussian`), with `gaussianRateFun`.

### Joint source–channel coding
* Joint source–channel codes and achievable distortions: `LossySourceChannelCode`,
  `LossySourceChannelCode.distortion`, `IsAchievableSCDistortion`
  (`RateDistortion.SourceChannel`), for `r = 1`.
* Shannon's source–channel separation theorem for `r = 1`:
  `isAchievableSCDistortion_of_infoRD_lt` and `IsAchievableSCDistortion.infoRD_le_capacity`.
* Uncoded transmission of a `Bern(1/2)` source over a `BSC(p)`: the distortion `p`,
  `uncodedCode`, `distortion_uncodedCode`, `isAchievableSCDistortion_uncoded`, and its
  optimality `R(p) = C`: `rateDistortionBits_bernoulli_half_eq_opCapacityAvg_bsc` (here).

## Not formalized

* The achievability proof of the channel coding theorem with robust typicality: the theorem is
  derived from Cover and Thomas's proof, which decodes with weak typicality and bounds the
  maximal probability of error. The proof of Theorem 2 uses the same decoder, restricted to
  robustly typical codewords (`ChannelCoding.Cost`).
* The product DMC with `d > 2` components, as a separate statement; it follows by iterating the
  case of two channels.
* Achievability with linear codes for the BSC; error exponents.
* The continuity of `C(B)` at the smallest cost `B = 0`.
* Lemma 2 and its Appendix (the quantization argument `I([X]ⱼ; [Yⱼ]ₖ) → I(X; Y)`): Theorem 3
  is derived from Cover and Thomas's direct proof for Gaussian codebooks.
* The Gaussian product channel with gains `g_j` as an operational theorem: only its information
  capacity is formalized, with noise powers `1/g_j²`.
* The remarks on stationary ergodic sources.
* The operational form of Theorem 6 (the rate–distortion theorem for the `WGN(P)` source with
  quadratic distortion): only the informational rate–distortion function is formalized.
* Joint source–channel coding at rates `r = k/n ≠ 1`, and the conditions for the optimality of
  uncoded transmission in general.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Channel coding -/

/-- **Example (Lecture 3): binary symmetric channel.** The capacity of the `BSC(p)` is
`C = 1 - H(p)` bits, attained by `X ∼ Bern(1/2)`. -/
theorem example_bsc {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    opCapacityAvg (CoverThomas.bsc p) = 1 - binEntropy p / log 2 := by
  rw [opCapacityAvg_eq (CoverThomas.bsc_isChannel h0 h1), (CoverThomas.capacity_bsc h0 h1).1,
    sub_div, div_self (log_pos one_lt_two).ne']

/-- **Example (Lecture 3): binary erasure channel.** The capacity of the `BEC(p)` is `C = 1 - p`
bits, attained by `X ∼ Bern(1/2)`. -/
theorem example_bec {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    opCapacityAvg (CoverThomas.bec p) = 1 - p := by
  rw [opCapacityAvg_eq (CoverThomas.bec_isChannel h0 h1), (CoverThomas.capacity_bec h0 h1).1,
    mul_div_cancel_right₀ _ (log_pos one_lt_two).ne']

/-! ## Lossless source coding -/

/-- **Example (Lecture 3).** For a `Bern(p)` source, the optimal lossless compression rate is
`H(p)` bits. -/
theorem optLosslessRate_bernoulli {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    optLosslessRate (bernoulliPMF p) = binEntropy p / log 2 := by
  rw [optLosslessRate_eq (bernoulliPMF_isPMF h0 h1), entropy_bernoulliPMF]

/-! ## Lossy source coding -/

/-- **Example (Lecture 3): Bernoulli source with Hamming distortion.** For `p ≤ 1/2`, the
rate–distortion function of a `Bern(p)` source is `H(p) - H(D)` bits for `0 ≤ D < p` and `0`
for `D ≥ p`. -/
theorem rateDistortionBits_bernoulli {p D : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1 / 2) (hD : 0 ≤ D) :
    rateDistortionBits (bernoulliPMF p) hammingDistortion D =
      (if D < p then binEntropy p - binEntropy D else 0) / log 2 := by
  have hp := bernoulliPMF_isPMF h0 (by linarith : p ≤ 1)
  rw [rateDistortionBits_eq hp (fun x y => by unfold hammingDistortion; split_ifs <;> norm_num)
    (by rw [minDistortion_hammingDistortion]; exact hD),
    infoRD_bernoulli h0 (by linarith) hD, min_eq_left (by linarith)]
  congr 1
  by_cases hDp : D < p
  · rw [ite_eq_left hDp.le, ite_eq_left hDp]
  · by_cases hDp' : D ≤ p
    · rw [le_antisymm hDp' (not_lt.1 hDp), ite_eq_left le_rfl, ite_eq_right (lt_irrefl p),
        sub_self]
    · rw [ite_eq_right hDp', ite_eq_right hDp]

/-- **Lossless source coding revisited (Lecture 3).** Lossless source coding is the case `D = 0`
of lossy source coding with the Hamming distortion: `R* = R(0)`. -/
theorem optLosslessRate_eq_rateDistortionBits_zero {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsPMF p) : optLosslessRate p = rateDistortionBits p hammingDistortion 0 := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  rw [optLosslessRate_eq hp, rateDistortionBits_eq hp
    (fun x y => by unfold hammingDistortion; split_ifs <;> norm_num)
    (minDistortion_hammingDistortion p).le, infoRD_hammingDistortion_zero hp]

/-! ## Uncoded transmission -/

/-- The output of a memoryless channel at time `i` depends only on the input at time `i`:
`∑_{yⁿ} p(yⁿ|xⁿ) g(yᵢ) = ∑_y p(y|xᵢ) g(y)`. -/
lemma sum_channelExt_mul_apply {α β : Type*} [Fintype β] {W : α → β → ℝ} (hW : IsChannel W)
    {n : ℕ} (x : Fin n → α) (i : Fin n) (g : β → ℝ) :
    ∑ y, channelExt W n x y * g (y i) = ∑ b, W (x i) b * g b := by
  classical
  have h := Fintype.prod_sum fun (j : Fin n) (b : β) => W (x j) b * if j = i then g b else 1
  rw [prod_eq_single i (fun j _ hj => by simp [hj, (hW _).sum_eq_one]) (by simp)] at h
  simp only [ite_true] at h
  rw [h]
  refine sum_congr rfl fun y _ => ?_
  rw [prod_mul_distrib, prod_ite_eq' univ i, ite_eq_left (mem_univ i), channelExt]

/-- **Uncoded transmission (Lecture 3).** Send the source sequence over the channel and use the
channel output as the reconstruction. -/
def uncodedCode (n : ℕ) : LossySourceChannelCode n Bool Bool Bool Bool := ⟨id, id⟩

/-- **Uncoded transmission (Lecture 3).** Sent uncoded over a `BSC(p)`, a binary source is
reconstructed with expected Hamming distortion `p`. -/
theorem distortion_uncodedCode {p θ : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    (uncodedCode n).distortion (bernoulliPMF θ) (CoverThomas.bsc p) hammingDistortion = p := by
  have hW := CoverThomas.bsc_isChannel h0 h1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ∀ v : Fin n → Bool, ∑ y, channelExt (CoverThomas.bsc p) n v y *
      seqDistortion hammingDistortion v y = p := fun v => by
    simp only [seqDistortion, mul_div_assoc', ← sum_div, mul_sum]
    rw [sum_comm, div_eq_iff hn']
    have : ∀ i, ∑ y, hammingDistortion (v i) (y i) * channelExt (CoverThomas.bsc p) n v y = p :=
      fun i => by
        simp_rw [mul_comm (hammingDistortion (v i) _)]
        rw [sum_channelExt_mul_apply hW v i (hammingDistortion (v i))]
        cases v i <;> simp [CoverThomas.bsc, hammingDistortion]
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  simp only [LossySourceChannelCode.distortion, uncodedCode, id, mul_assoc, ← mul_sum, key,
    ← sum_mul, (iidPMF_isPMF (bernoulliPMF_isPMF hθ0 hθ1) n).sum_eq_one, one_mul]

/-- **Uncoded transmission (Lecture 3).** Uncoded transmission achieves the distortion `p` for a
binary source over a `BSC(p)`. -/
theorem isAchievableSCDistortion_uncoded {p θ : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    IsAchievableSCDistortion (bernoulliPMF θ) (CoverThomas.bsc p) hammingDistortion p := by
  refine ⟨uncodedCode, fun ε hε => ?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [distortion_uncodedCode h0 h1 hθ0 hθ1 hn]
  linarith

/-- **Uncoded transmission (Lecture 3).** For a `Bern(1/2)` source over a `BSC(p)`, `p ≤ 1/2`,
the distortion `p` of uncoded transmission is optimal: `R(p) = 1 - H(p) = C` bits, so by the
separation theorem no code achieves a smaller distortion. -/
theorem rateDistortionBits_bernoulli_half_eq_opCapacityAvg_bsc {p : ℝ} (h0 : 0 ≤ p)
    (h1 : p ≤ 1 / 2) :
    rateDistortionBits (bernoulliPMF (1 / 2)) hammingDistortion p =
      opCapacityAvg (CoverThomas.bsc p) := by
  have hp := bernoulliPMF_isPMF (θ := 1 / 2) (by norm_num) (by norm_num)
  rw [rateDistortionBits_eq hp (fun x y => by unfold hammingDistortion; split_ifs <;> norm_num)
    (by rw [minDistortion_hammingDistortion]; exact h0), CoverThomas.infoRD_bernoulli_half h0,
    ite_eq_left h1, example_bsc h0 (by linarith), sub_div, div_self (log_pos one_lt_two).ne']

/-! ## Index of numbered and named results -/

/-- **Shannon's channel coding theorem (Lecture 3).** `C = max_{p(x)} I(X; Y)`. -/
alias channel_coding_theorem := opCapacityAvg_eq

/-- **Example (Lecture 3): product DMC.** `C = C₁ + C₂`. -/
alias example_product_dmc := capacity_prodChannel

/-- **Packing lemma (Lecture 3).** -/
alias packing_lemma := prob_exists_mem_robustTypicalSet_le_exp

/-- **Theorem 2 (Lecture 3).** The capacity with cost constraint `B` is `C(B)`. -/
alias theorem_3_2 := opCapacityCost_eq

/-- **Theorem 3 (Lecture 3).** The capacity of the AWGN channel is `C(S)`. -/
alias theorem_3_3 := opCapacityAWGN_eq

/-- **Shannon's lossless source coding theorem (Lecture 3).** `R* = H(X)`. -/
alias lossless_source_coding_theorem := optLosslessRate_eq

/-- **Shannon's lossy source coding theorem (Lecture 3).** `R(D) = min I(X; X̂)`. -/
alias lossy_source_coding_theorem := rateDistortionBits_eq

/-- **Covering lemma (Lecture 3).** -/
alias covering_lemma := eventually_prob_forall_not_mem_robustTypicalSet_le

/-- **Theorem 6 (Lecture 3).** `R(D) = R(P/D)` for the `WGN(P)` source, informational form. -/
alias theorem_3_6 := gaussianInfoRD_eq_gaussianRateFun

/-- **Shannon's source–channel separation theorem (Lecture 3)**, achievability for `r = 1`. -/
alias separation_theorem_achievability := isAchievableSCDistortion_of_infoRD_lt

/-- **Shannon's source–channel separation theorem (Lecture 3)**, converse for `r = 1`. -/
alias separation_theorem_converse := IsAchievableSCDistortion.infoRD_le_capacity

end InfoTheory.ElGamalKim
