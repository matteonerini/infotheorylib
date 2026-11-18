/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter7
public import InfoTheoryLib.ChannelCoding.AsymptoticRate
public import InfoTheoryLib.ChannelCoding.DiscreteChannel
public import InfoTheoryLib.Typicality.L1Conditional

/-!
# Yeung, Chapter 7: Discrete Memoryless Channels

This file indexes the formalization of Chapter 7 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Logarithms and rates.** Logarithms are natural, so rates and capacities are in nats per use:
  the BSC has capacity `log 2 - H(ε)` nats, which is `1 - h_b(ε)` bits.
* **Channels.** A channel `p(y|x)` is `W : α → β → ℝ` with `IsChannel W`. The alphabets are finite,
  as the book assumes from Definition 7.6 on.
* **Messages.** The message set `{1, …, M}` is `Fin M = {0, …, M - 1}`.
* **Feedback codes.** The `i`-th encoding function `fᵢ(W, Yⁱ⁻¹)` of Definition 7.18 is
  `enc (i - 1)`, indexed from `0`. The joint law of the message and the outputs is `fbLaw`, built
  time by time as in (7.209).
* **Achievable rates.** The book's achievable rates (Definitions 7.14 and 7.19) are
  `IsAsymptoticallyAchievable` and `IsAsymptoticallyAchievableFB`. The library's `IsAchievableRate`
  (Cover & Thomas) asks for `⌈e^{nR}⌉` messages instead; both give the same capacity.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The introduction: the binary repetition code
* (7.12)–(7.22), the repetition code makes `Pₑ → 0` at rate `1/n → 0`: `repetitionCode`,
  `tendsto_maxErrProb_repetitionCode`, `tendsto_codeRate_two` (here). The book uses the weak law of
  large numbers; the proof here uses the Chernoff bound `prob_symbolCount_ge_le` (`Typicality.L1`).

### 7.1 Definition and Capacity
* Definition 7.1 and (7.23)–(7.24): `IsChannel`, `jointOf` (`Probability.Channel`).
* Definition 7.2: `noiseChannel` (`ChannelCoding.DiscreteChannel`).
* Definition 7.3: `IsEquivalentChannel` (`ChannelCoding.DiscreteChannel`).
* (7.25)–(7.32), every channel has a noise form: `isEquivalentChannel_coord`
  (`ChannelCoding.DiscreteChannel`).
* Definition 7.4 and (7.35): `IsMemorylessUse` (`ChannelCoding.DiscreteChannel`), and
  `channelExt` (`ChannelCoding.Code`) for a use without feedback.
* (7.38): `IsMemorylessUse.markovChain` (`ChannelCoding.DiscreteChannel`).
* Definition 7.5 and (7.40)–(7.51): `isMemorylessUse_noise` (`ChannelCoding.DiscreteChannel`).
* Definition 7.6: `capacity`, `exists_capacity_eq` (`ChannelCoding.Capacity`).
* (7.53)–(7.57): `capacity_nonneg`, `capacity_le_log_card_input`, `capacity_le_log_card_output`
  (`ChannelCoding.Capacity`).
* Example 7.7: `example_7_7` (here), from `capacity_bsc` (`Books.CoverThomas.Chapter7`), with the
  noise form (7.58)–(7.59).
* Example 7.8: `example_7_8` (here), which is `capacity_bec` (`Books.CoverThomas.Chapter7`).

### 7.2 The Channel Coding Theorem
* Definition 7.9: `ChannelCode` (`ChannelCoding.Code`). (7.80): `ChannelCode.entropy_fst_jointLaw`
  (`ChannelCoding.Converse`).
* Definitions 7.10–7.12: `ChannelCode.condErrProb`, `ChannelCode.maxErrProb`,
  `ChannelCode.avgErrProb` (`ChannelCoding.Code`). (7.88)–(7.92):
  `ChannelCode.errProb_jointLaw` (`ChannelCoding.Converse`), `ChannelCode.avgErrProb_le_maxErrProb`
  (`ChannelCoding.Code`).
* Definition 7.13: `codeRate` (`ChannelCoding.AsymptoticRate`).
* Definition 7.14: `IsAsymptoticallyAchievable` (`ChannelCoding.AsymptoticRate`).
* Theorem 7.15: `theorem_7_15` (here), which is `isAsymptoticallyAchievable_iff`
  (`ChannelCoding.AsymptoticRate`).

### 7.3 The Converse
* (7.97) and (7.101): `codeLaw` (`Network.MACConverse`), `ChannelCode.jointLaw_apply`
  (`ChannelCoding.Converse`).
* Lemma 7.16: `lemma_7_16` (here), which is `mutualInfo_codeLaw_le_sum`
  (`ChannelCoding.DiscreteChannel`). (7.116): `condEntropy_codeLaw` (`Network.MACConverse`).
* (7.122)–(7.133): `ChannelCode.one_sub_avgErrProb_mul_log_le` (`ChannelCoding.Converse`) and
  `le_of_eventually_code_bound` (`ChannelCoding.AsymptoticRate`). The proof bounds `I(W; Y)` through
  the joint law with feedback (`mutualInfo_fbLaw_le`), so it does not state the Markov chain (7.98).
* (7.134): `ChannelCode.avgErrProb_ge` (`ChannelCoding.Converse`). That `Pₑ > 0` for every block
  length when the rate exceeds `C`: `ChannelCode.log_le_of_avgErrProb_eq_zero`.

### 7.4 Achievability
* Lemma 7.17: `lemma_7_17` (here), which is `prob_indep_jointL1TypicalSet_le`
  (`Typicality.L1Conditional`).
* (7.146)–(7.189): `isAchievableRate_of_lt_capacity`, `exists_code_avgErrProb_le`
  (`ChannelCoding.Achievability`), `ChannelCode.exists_maxErrProb_le_two_mul`
  (`ChannelCoding.Code`). The library decodes with weak joint typicality, as in Cover & Thomas,
  rather than the book's strong typicality; the theorem is the same.

### 7.6 Feedback Capacity
* Definition 7.18: `FeedbackCode` (`ChannelCoding.Converse`), and
  `FeedbackCode.condErrProb`, `FeedbackCode.maxErrProb` (`ChannelCoding.AsymptoticRate`).
* Definition 7.19: `IsAsymptoticallyAchievableFB` (`ChannelCoding.AsymptoticRate`).
* Definition 7.20: `fbCapacityMax` (`ChannelCoding.AsymptoticRate`).
* Proposition 7.21: `proposition_7_21` (here), which is
  `isAsymptoticallyAchievableFB_fbCapacityMax` (`ChannelCoding.AsymptoticRate`). It is proved from
  `C_FB = C`, not by the book's limit argument.
* (7.208): `IsAsymptoticallyAchievable.fb` (`ChannelCoding.AsymptoticRate`).
* (7.209): `fbLaw` (`ChannelCoding.Converse`), `fbLaw_isMemorylessUse`
  (`ChannelCoding.DiscreteChannel`).
* Lemma 7.22: `lemma_7_22` (here), which is `markovChain_fbLaw` (`ChannelCoding.DiscreteChannel`).
* (7.219)–(7.229), `C_FB = C`: `FeedbackCode.one_sub_errProb_mul_log_le`,
  `mutualInfo_fbLaw_le` (`ChannelCoding.Converse`), `isAsymptoticallyAchievableFB_iff`,
  `fbCapacityMax_eq_capacity` (`ChannelCoding.AsymptoticRate`).
* Example 7.23: `example_7_23` (here), the computation only.

### 7.7 Separation of Source and Channel Coding
* (7.235)–(7.243): `exists_sourceChannelCode` (`ChannelCoding.SourceChannel`). The book uses the
  Shannon-McMillan-Breiman theorem for an ergodic stationary source; the library assumes instead
  that the source has typical sets (`StochasticProcess.HasTypicalSets`), which i.i.d. sources have.
* (7.244)–(7.254), the converse with complete feedback: `entropyRate_le_capacity_of_fbLaw`
  (`ChannelCoding.AsymptoticRate`).

## Not formalized

* The single use of a BSC, (7.1)–(7.11).
* The strong converse, which the book states without proof.
* (7.190)–(7.196), that most random codebooks are good, and the rest of the discussion in Section
  7.5, including the heuristic (7.197).
* Figures 7.1 to 7.17, and the dependency graphs of Sections 7.3 and 7.6, which the formalization
  replaces by the joint laws `codeLaw` and `fbLaw`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.Yeung

open CoverThomas

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Worked examples -/

/-- The binary repetition code of block length `n`: message `0` is sent as `n` zeros and message `1`
as `n` ones, and the decoder takes a majority vote, with ties decoded to `0`. -/
def repetitionCode (n : ℕ) : ChannelCode 2 n Bool Bool where
  enc i _ := decide (i = 1)
  dec y := if n < 2 * symbolCount y true then 1 else 0

lemma symbolCount_true_add_false {n : ℕ} (y : Fin n → Bool) :
    symbolCount y true + symbolCount y false = n := by
  have h := sum_symbolCount y
  rw [Fintype.sum_bool] at h
  exact_mod_cast h

lemma ite_le_ite_of_imp {p q : Prop} [Decidable p] [Decidable q] {a : ℝ} (ha : 0 ≤ a)
    (h : p → q) : (if p then a else 0) ≤ if q then a else 0 := by
  split_ifs with hp hq <;> first | exact le_rfl | exact ha | exact absurd (h hp) hq

/-- Each message of the repetition code is decoded wrongly with probability at most
`e^{-n ρ(1/2 - ε)}`. -/
lemma condErrProb_repetitionCode_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) (n : ℕ) (i : Fin 2) :
    (repetitionCode n).condErrProb (bsc ε) i ≤ exp (-(n * chernoffRate (1 / 2 - ε))) := by
  classical
  have hδ : 0 < 1 / 2 - ε := by linarith
  have hext : ∀ b y, channelExt (bsc ε) n (fun _ => b) y = iidPMF (bsc ε b) n y :=
    fun _ _ => rfl
  fin_cases i
  · have hp : IsPMF (bsc ε false) := bsc_isChannel h0 (by linarith) false
    refine le_trans ?_ (prob_symbolCount_ge_le hp n true hδ)
    rw [ChannelCode.condErrProb, prob, sum_filter]
    refine sum_le_sum fun y _ => ?_
    refine ite_le_ite_of_imp (iidPMF_nonneg hp.nonneg _) fun h => ?_
    have hd : n < 2 * symbolCount y true := by
      by_contra hd
      exact h (by simp [repetitionCode, hd])
    have : (n : ℝ) < 2 * symbolCount y true := by exact_mod_cast hd
    have hb : bsc ε false true = ε := by simp [bsc]
    rw [hb]
    linarith
  · have hp : IsPMF (bsc ε true) := bsc_isChannel h0 (by linarith) true
    refine le_trans ?_ (prob_symbolCount_ge_le hp n false hδ)
    rw [ChannelCode.condErrProb, prob, sum_filter]
    refine sum_le_sum fun y _ => ?_
    refine ite_le_ite_of_imp (iidPMF_nonneg hp.nonneg _) fun h => ?_
    have hd : ¬n < 2 * symbolCount y true := fun hd => h (by simp [repetitionCode, hd])
    have h₁ := symbolCount_true_add_false y
    have h₃ : (n : ℝ) ≤ 2 * symbolCount y false := by
      have : n ≤ 2 * symbolCount y false := by omega
      exact_mod_cast this
    have hb : bsc ε true false = ε := by simp [bsc]
    rw [hb]
    linarith

/-- **(7.16)–(7.22)** For a BSC with crossover probability `ε < 1/2`, the maximal probability of
error of the repetition code tends to `0`. -/
theorem tendsto_maxErrProb_repetitionCode {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) :
    Tendsto (fun n => (repetitionCode n).maxErrProb (bsc ε)) atTop (𝓝 0) := by
  have hW : IsChannel (bsc ε) := bsc_isChannel h0 (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_exp_neg_mul_nat (chernoffRate_pos (show 0 < 1 / 2 - ε by linarith)))
    (fun n => (repetitionCode n).maxErrProb_nonneg hW) fun n => ?_
  exact ChannelCode.maxErrProb_le _ (by norm_num) fun i =>
    condErrProb_repetitionCode_le h0 h1 n i

/-- The rate `(1/n) log 2` of the repetition code tends to `0`. -/
theorem tendsto_codeRate_two : Tendsto (fun n => codeRate 2 n) atTop (𝓝 0) := by
  simpa [codeRate] using tendsto_const_div_atTop_nhds_zero_nat (log 2)

/-- **Example 7.23.** With feedback, a bit is sent over the BEC until it is not erased. The number
of uses is geometric, with mean `1/(1 - γ)`, so the rate `1 - γ` bits per use, the capacity, is
achieved with zero probability of error. We formalize the computation: the geometric law, its mean
and the capacity of the BEC; the feedback scheme itself is not modelled. -/
theorem example_7_23 {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    HasSum (fun k : ℕ => γ ^ k * (1 - γ)) 1 ∧
      HasSum (fun k : ℕ => ((k : ℝ) + 1) * (γ ^ k * (1 - γ))) (1 - γ)⁻¹ ∧
      capacity (bec γ) = (1 - γ) * log 2 := by
  have hγ : 1 - γ ≠ 0 := by linarith
  have h₁ := hasSum_geometric_of_lt_one h0 h1
  have h₂ := hasSum_coe_mul_geometric_of_norm_lt_one (r := γ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  refine ⟨?_, ?_, (capacity_bec h0 h1.le).1⟩
  · have := h₁.mul_right (1 - γ)
    rwa [inv_mul_cancel₀ hγ] at this
  · have := (h₂.add h₁).mul_right (1 - γ)
    convert this using 1
    · funext k
      ring
    · field_simp
      ring

/-! ### Aliases -/

/-- **Example 7.7 (Binary Symmetric Channel).** The BSC has the noise form `Y = X + Z mod 2`,
(7.58)–(7.59), and capacity `1 - h_b(ε)` bits, (7.65). -/
theorem example_7_7 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsEquivalentChannel (bsc ε) (fun x z => xor x z) (bsc ε false) ∧
      capacity (bsc ε) = log 2 - binEntropy ε := by
  refine ⟨fun x y => ?_, (capacity_bsc h0 h1).1⟩
  cases x <;> cases y <;> simp [dist, bsc]

/-- **Example 7.8 (Binary Erasure Channel).** (7.77) -/
alias example_7_8 := capacity_bec

/-- **Theorem 7.15 (Channel Coding Theorem).** -/
alias theorem_7_15 := isAsymptoticallyAchievable_iff

/-- **Lemma 7.16.** (7.113) -/
alias lemma_7_16 := mutualInfo_codeLaw_le_sum

/-- **Lemma 7.17.** (7.136) -/
alias lemma_7_17 := prob_indep_jointL1TypicalSet_le

/-- **Proposition 7.21.** -/
alias proposition_7_21 := isAsymptoticallyAchievableFB_fbCapacityMax

/-- **Lemma 7.22.** (7.210) -/
alias lemma_7_22 := markovChain_fbLaw

end InfoTheory.Yeung
