/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter7
public import InfoTheoryLib.SourceCoding.FixedLength
public import InfoTheoryLib.SourceCoding.Kraft
public import InfoTheoryLib.SourceCoding.OptimalLength

/-!
# Cover & Thomas, Chapter 1: Introduction and Preview

This file indexes the formalization of Chapter 1 of [cover2006] and contains the chapter's worked
examples. Chapter 1 is an informal preview: it states the definitions of entropy, mutual
information, channel capacity and relative entropy, which the book repeats in Chapter 2, and
announces results proved in later chapters. The list below points each of them to the declaration
that formalizes it. The chapter has no numbered theorems, so there are no aliases.

## Conventions

* **Logarithms.** The book uses logarithms to base `2` in this chapter. The library's logarithms
  are natural; `entropyBits p = entropy p / log 2` is the entropy in bits, and capacities in bits
  are `C / log 2`.
* **Codes.** A binary code is a map `C : X → List (Fin 2)` or `C : X → List Bool`, with expected
  length `expectedLength p C = ∑ₓ p(x) |C(x)|`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Introduction
* The data transmission limit of Figure 1.2, `max I(X; Y)`: `capacity` (`ChannelCoding.Capacity`),
  achieved by codes of every rate below it: `isAchievableRate_of_lt_capacity`,
  `opCapacity_eq_capacity` (`ChannelCoding.Achievability`, `ChannelCoding.Converse`).
* The second law of thermodynamics (Section 4.4): `relEntropy_step_le`,
  `entropy_iterate_monotone` (`MarkovChain.SecondLaw`).

### 1.1 Preview of the book
* (1.1): `entropy`, `entropyBits`, `entropyBits_eq` (`Entropy.Basic`).
* Example 1.1.1, (1.2): `binaryLabel`, `binaryLabel_isPrefixCode`, `example_1_1_1` (here).
* Example 1.1.2, (1.3): `pmf_1_1_2`, `code_1_1_2`, `example_1_1_2`, and the entropy bound for every
  uniquely decodable code, `example_1_1_2_le` (here).
* The entropy is a lower bound on the expected length of a code, and there are codes within one
  bit of it (Chapter 5): `entropyBase_le_expectedLength`, `kraft_of_isUniquelyDecodableCode`,
  `exists_prefixCode_shannon`, `minExpectedLength_bounds` (`SourceCoding.OptimalLength`,
  `SourceCoding.Kraft`).
* The AEP and typical sequences (Chapter 3): `aep`, `eventually_prob_typicalSet_gt`,
  `card_typicalSet_le`, `eventually_card_typicalSet_gt` (`AEP.Basic`, `AEP.TypicalSet`).
* Generating a random variable from fair coin flips (Section 5.11):
  `CoinTree.entropyBase_le_expectedFlips`, `minExpectedFlips_bounds` (`SourceCoding.CoinFlips`).
* (1.4): `mutualInfo`, `mutualInfo_eq_entropy_sub_condEntropy`, `mutualInfo_eq_sum`; it is
  symmetric, non-negative, and zero iff `X` and `Y` are independent: `mutualInfo_comm`,
  `mutualInfo_nonneg`, `mutualInfo_eq_zero_iff` (`MutualInformation.Basic`).
* (1.5): `IsChannel`, `mutualInfoOf`, `capacity` (`ChannelCoding.Capacity`).
* Example 1.1.3: `noiselessChannel` (`Books.CoverThomas.Chapter7`), `noiselessCode`,
  `example_1_1_3` (here).
* Example 1.1.4: `fourSymbolChannel`, `fourSymbolCode`, `example_1_1_4` (here).
* Example 1.1.5: `bsc` (`Books.CoverThomas.Chapter7`), `example_1_1_5` (here).
* (1.6): `relEntropy`, `relEntropyReal` (`RelativeEntropy.Basic`); it is non-negative and zero iff
  `p = q`: `relEntropy_nonneg`, `relEntropy_eq_zero_iff`, `relEntropyReal_nonneg`,
  `relEntropyReal_eq_zero_iff` (`RelativeEntropy.InformationInequality`).
* Gambling (Chapter 6): for a horse race with uniform odds, `W + H` is constant,
  `optDoublingRate_add_entropy` (`Gambling.HorseRace`); side information increases the doubling
  rate by `I`, `optCondDoublingRate_sub` (`Gambling.SideInformation`).

## Not formalized

* Figures 1.1 and 1.2, and the discussion of the relations of information theory to other fields.
* The von Neumann entropy, which the book mentions but does not treat. The other quantities and
  topics of later chapters announced in this chapter are indexed in the corresponding chapter
  files: the stock market doubling rate (1.7) (Chapter 16), Kolmogorov complexity (Chapter 14),
  rate distortion theory and the data compression limit `min I(X; X̂)` (Chapter 10), network
  information theory (Chapter 15), hypothesis testing and large deviations (Chapter 11), and
  maximum entropy inference (Chapter 12).
* The equivalence of codes with strategies for the game of "20 questions" (see Chapter 5).
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 1.1: Preview of the book -/

/-- The fixed-length binary labels of `N` outcomes: outcome `x` is labelled by the `k` binary
digits of its index. For `N ≤ 2ᵏ` the labels are distinct. -/
def binaryLabel (k : ℕ) {N : ℕ} (x : Fin N) : List Bool := binaryDigits k x

lemma length_binaryLabel (k : ℕ) {N : ℕ} (x : Fin N) : (binaryLabel k x).length = k :=
  length_binaryDigits k x

/-- Fixed-length labels form a prefix code. -/
lemma binaryLabel_isPrefixCode {k N : ℕ} (hN : N ≤ 2 ^ k) :
    IsPrefixCode (binaryLabel k (N := N)) := by
  intro x y h
  have := h.eq_of_length (by rw [length_binaryLabel, length_binaryLabel])
  exact Fin.ext (binaryDigits_inj (x.2.trans_le hN) (y.2.trans_le hN) this)

lemma expectedLength_binaryLabel {k N : ℕ} {p : Fin N → ℝ} (hp : IsPMF p) :
    expectedLength p (binaryLabel k) = k := by
  simp only [expectedLength, length_binaryLabel]
  rw [← sum_mul, hp.sum_eq_one, one_mul]

/-- **Example 1.1.1, (1.2).** A random variable uniform over `32` outcomes has entropy
`H(X) = log 32 = 5` bits, which agrees with the `5`-bit labels needed to identify the outcomes. -/
theorem example_1_1_1 :
    entropyBits (uniformPMF (Fin 32)) = 5 ∧ IsPrefixCode (binaryLabel 5 (N := 32)) ∧
      expectedLength (uniformPMF (Fin 32)) (binaryLabel 5) = 5 := by
  refine ⟨?_, binaryLabel_isPrefixCode (by norm_num), ?_⟩
  · rw [entropyBits_eq, entropy_uniformPMF, Fintype.card_fin, Nat.cast_ofNat,
      show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow, mul_div_cancel_right₀ _ (log_pos one_lt_two).ne']
    norm_num
  · rw [expectedLength_binaryLabel uniformPMF_isPMF]
    norm_num

/-- **Example 1.1.2.** The win probabilities `(1/2, 1/4, 1/8, 1/16, 1/64, 1/64, 1/64, 1/64)` of
eight horses. -/
def pmf_1_1_2 : Fin 8 → ℝ := ![1 / 2, 1 / 4, 1 / 8, 1 / 16, 1 / 64, 1 / 64, 1 / 64, 1 / 64]

lemma pmf_1_1_2_isPMF : IsPMF pmf_1_1_2 :=
  ⟨fun x => by fin_cases x <;> norm_num [pmf_1_1_2],
    by simp [pmf_1_1_2, Fin.sum_univ_eight]; norm_num⟩

/-- **Example 1.1.2.** The description `0, 10, 110, 1110, 111100, 111101, 111110, 111111` of the
winning horse. -/
def code_1_1_2 : Fin 8 → List (Fin 2) :=
  ![[0], [1, 0], [1, 1, 0], [1, 1, 1, 0], [1, 1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 1],
    [1, 1, 1, 1, 1, 0], [1, 1, 1, 1, 1, 1]]

/-- **Example 1.1.2, (1.3).** The horse race has entropy `H(X) = 2` bits. Sending the index of the
winning horse takes `3` bits, but the prefix code `code_1_1_2`, with shorter descriptions for the
more probable horses, has expected length `2` bits, equal to the entropy. -/
theorem example_1_1_2 :
    entropyBits pmf_1_1_2 = 2 ∧ IsPrefixCode code_1_1_2 ∧
      expectedLength pmf_1_1_2 code_1_1_2 = 2 ∧ expectedLength pmf_1_1_2 (binaryLabel 3) = 3 := by
  refine ⟨?_, by unfold IsPrefixCode; decide, ?_, ?_⟩
  · have h2 := (log_pos one_lt_two).ne'
    rw [entropyBits_eq, entropy_eq_sum_negMulLog, Fin.sum_univ_eight]
    have e : ∀ i, pmf_1_1_2 i = ((2 : ℝ) ^ (![1, 2, 3, 4, 6, 6, 6, 6] : Fin 8 → ℕ) i)⁻¹ := by
      intro i
      fin_cases i <;> norm_num [pmf_1_1_2]
    simp only [e, negMulLog_inv_two_pow]
    simp
    field_simp
    norm_num
  · simp [expectedLength, code_1_1_2, pmf_1_1_2, Fin.sum_univ_eight]
    norm_num
  · rw [expectedLength_binaryLabel pmf_1_1_2_isPMF]
    norm_num

/-- **Example 1.1.2.** The entropy is a lower bound on the average number of bits needed to
describe the winning horse: every uniquely decodable binary code has expected length at least
`H(X) = 2` bits, so `code_1_1_2` is optimal. -/
theorem example_1_1_2_le {C : Fin 8 → List (Fin 2)} (hC : IsUniquelyDecodableCode C) :
    2 ≤ expectedLength pmf_1_1_2 C := by
  have hk := kraft_of_isUniquelyDecodableCode hC
  have h := entropyBase_le_expectedLength pmf_1_1_2_isPMF (D := 2) le_rfl (fun x => (C x).length)
    (by simpa [kraftSum] using hk)
  rw [← example_1_1_2.1]
  simpa [expectedLength] using h

/-- **Example 1.1.3.** Over the noiseless binary channel, a bit is sent as itself: two messages
with block length `1`. -/
def noiselessCode : ChannelCode 2 1 Bool Bool where
  enc w _ := decide (w = 1)
  dec y := if y 0 then 1 else 0

/-- **Example 1.1.3 (Noiseless binary channel).** Every transmitted bit is received without error,
so one bit is sent reliably per transmission, and the capacity is `C = max I(X; Y) = 1` bit. -/
theorem example_1_1_3 :
    capacity noiselessChannel / log 2 = 1 ∧ noiselessCode.maxErrProb noiselessChannel = 0 := by
  refine ⟨by rw [capacity_noiselessChannel.1, div_self (log_pos one_lt_two).ne'], ?_⟩
  classical
  have key : ∀ (w : Fin 2) (b : Bool), (if b then 1 else 0 : Fin 2) ≠ w → decide (w = 1) ≠ b := by
    decide
  have h : ∀ w, noiselessCode.condErrProb noiselessChannel w = 0 := fun w => by
    refine sum_eq_zero fun y _ => ?_
    split_ifs with hne
    · have hc := key w (y 0) hne
      simp only [channelExt, Fin.prod_univ_one, noiselessChannel]
      exact ite_eq_right_iff.2 fun h => absurd h hc
    · rfl
  refine le_antisymm (ChannelCode.maxErrProb_le _ (by norm_num) fun w => (h w).le) ?_
  exact noiselessCode.maxErrProb_nonneg noiselessChannel_isChannel

/-- **Example 1.1.4 (Figure 1.4).** The noisy four-symbol channel: each input letter is received
as the same letter or as the next letter (cyclically), each with probability `1/2`. Letters
`1, …, 4` are `0, …, 3 : Fin 4`. -/
def fourSymbolChannel : Fin 4 → Fin 4 → ℝ := fun x y => if y = x ∨ y = x + 1 then 1 / 2 else 0

lemma card_fourSymbol (x : Fin 4) :
    (univ.filter fun y : Fin 4 => y = x ∨ y = x + 1).card = 2 := by
  revert x
  decide

lemma card_fourSymbol_col (y : Fin 4) :
    (univ.filter fun x : Fin 4 => y = x ∨ y = x + 1).card = 2 := by
  revert y
  decide

lemma fourSymbolChannel_isChannel : IsChannel fourSymbolChannel := fun x =>
  ⟨fun y => by unfold fourSymbolChannel; split_ifs <;> norm_num, by
    classical
    simp only [fourSymbolChannel, sum_ite, sum_const_zero, add_zero, sum_const, card_fourSymbol,
      nsmul_eq_mul]
    norm_num⟩

lemma capacity_fourSymbolChannel : capacity fourSymbolChannel = log 2 := by
  classical
  have hs : IsWeaklySymmetric fourSymbolChannel := by
    refine ⟨fun x x' => ⟨Equiv.addRight (x - x'), fun y => ?_⟩, fun y y' => ?_⟩
    · simp only [fourSymbolChannel, Equiv.coe_addRight]
      congr 1
      apply propext
      simp only [Fin.ext_iff, Fin.add_def, Fin.sub_def, Fin.val_one]
      omega
    · simp only [fourSymbolChannel, sum_ite, sum_const_zero, add_zero, sum_const,
        card_fourSymbol_col]
  obtain ⟨h1, -⟩ := capacity_of_isWeaklySymmetric fourSymbolChannel_isChannel hs 0
  have hrow : entropy (fourSymbolChannel 0) = log 2 := by
    rw [entropy_eq_sum_negMulLog]
    have : ∀ y, negMulLog (fourSymbolChannel 0 y) =
        if y = 0 ∨ y = 0 + 1 then negMulLog (1 / 2) else 0 := fun y => by
      simp only [fourSymbolChannel]; split_ifs <;> simp
    simp only [this, sum_ite, sum_const_zero, add_zero, sum_const, card_fourSymbol, nsmul_eq_mul]
    simp [negMulLog, log_inv]
  rw [h1, hrow, Fintype.card_fin, ← log_div (by norm_num) (by norm_num)]
  norm_num

/-- **Example 1.1.4.** The code using only the inputs `1` and `3`: two messages with block
length `1`, decoded from the output without error. -/
def fourSymbolCode : ChannelCode 2 1 (Fin 4) (Fin 4) where
  enc w _ := ⟨2 * w.val, by omega⟩
  dec y := ⟨(y 0).val / 2, by omega⟩

/-- **Example 1.1.4 (Noisy four-symbol channel).** Using only the inputs `1` and `3`, the channel
acts like the noiseless binary channel: one bit per transmission is sent with no errors, and the
capacity is `C = max I(X; Y) = 1` bit. -/
theorem example_1_1_4 :
    capacity fourSymbolChannel / log 2 = 1 ∧ fourSymbolCode.maxErrProb fourSymbolChannel = 0 := by
  refine ⟨by rw [capacity_fourSymbolChannel, div_self (log_pos one_lt_two).ne'], ?_⟩
  classical
  have key : ∀ (w : Fin 2) (y : Fin 4), (⟨y.val / 2, by omega⟩ : Fin 2) ≠ w →
      ¬ (y = ⟨2 * w.val, by omega⟩ ∨ y = ⟨2 * w.val, by omega⟩ + 1) := by
    decide
  have h : ∀ w, fourSymbolCode.condErrProb fourSymbolChannel w = 0 := fun w => by
    refine sum_eq_zero fun y _ => ?_
    split_ifs with hne
    · have hc := key w (y 0) hne
      simp only [channelExt, Fin.prod_univ_one, fourSymbolChannel]
      exact ite_eq_right_iff.2 fun h => absurd h hc
    · rfl
  refine le_antisymm (ChannelCode.maxErrProb_le _ (by norm_num) fun w => (h w).le) ?_
  exact fourSymbolCode.maxErrProb_nonneg fourSymbolChannel_isChannel

/-- **Example 1.1.5 (Binary symmetric channel).** The capacity of the binary symmetric channel
with crossover probability `p` is `C = 1 + p log p + (1 - p) log (1 - p)` bits per transmission,
and information can be sent at any rate below `C` with an arbitrarily low probability of error. -/
theorem example_1_1_5 {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    capacity (bsc p) / log 2 = 1 + p * logb 2 p + (1 - p) * logb 2 (1 - p) ∧
      ∀ R < capacity (bsc p), IsAchievableRate (bsc p) R := by
  refine ⟨?_, fun R hR => isAchievableRate_of_lt_capacity (bsc_isChannel h0 h1) hR⟩
  have h2 := (log_pos one_lt_two).ne'
  rw [(capacity_bsc h0 h1).1, binEntropy_eq_mul_log_inv, log_inv, log_inv, logb, logb]
  field_simp
  ring

end InfoTheory.CoverThomas
