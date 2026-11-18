/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Gambling.SideInformation
public import InfoTheoryLib.Gambling.DependentRaces
public import InfoTheoryLib.Gambling.DataCompression
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# Cover & Thomas, Chapter 6: Gambling and Data Compression

This file indexes the formalization of Chapter 6 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_6_1_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Horse races.** Horse `x` wins with probability `p(x)` and pays `o(x)`-for-`1`; the gambler bets
  the fraction `b(x)` of their wealth on it. Horses `1, …, m` are `0, …, m - 1 : Fin m`.
* **Logarithms.** Logarithms are natural, so doubling rates are in nats per race. The book's
  doubling rate is in bits, `W / log 2`, and its `2^{nW}` is `exp (n W)`.
* **Infinite doubling rates.** If a gambler bets nothing on a horse that can win, the book's
  doubling rate is `-∞`. Such schemes are excluded by the hypothesis `AbsCont p b` (`p ≪ b`).

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 6.1 The horse race
* (6.1)–(6.2), wealth and doubling rate: `wealth`, `doublingRate` (`Gambling.HorseRace`).
* Theorem 6.1.1: `log_wealth_div_tendstoInProb`.
* (6.6), Theorem 6.1.2 and (6.11)–(6.14): `optDoublingRate`, `doublingRate_eq`,
  `doublingRate_le`, `doublingRate_eq_iff`, `doublingRate_self`, `optDoublingRate_eq`.
* Example 6.1.1, (6.15): `example_6_1_1`, `example_6_1_1_growth` (here).
* (6.16)–(6.19), fair odds: `doublingRate_eq_relEntropy_sub`, `optDoublingRate_uniform`.
* Theorem 6.1.3: `optDoublingRate_add_entropy`.
* (6.21) and the three subcases, keeping cash: `cashDoublingRate`, `cashDoublingRate_le` (fair and
  superfair odds), `dutchBook_wealthRelative`; `example_6_1_dutchBook` and `example_6_1_subfair`
  (here).

### 6.2 Gambling and side information
* (6.22)–(6.24): `condDoublingRate`, `IsCondBet`, `optCondDoublingRate`
  (`Gambling.SideInformation`).
* (6.26)–(6.29): `condDoublingRate_le`, `condDoublingRate_condDist`, `optCondDoublingRate_eq`,
  `optDoublingRate_dist`.
* Theorem 6.2.1, (6.30): `optCondDoublingRate_sub`.

### 6.3 Dependent horse races and entropy rate
* Sequential betting, (6.32): `seqBetProb`, `seqWealth`, `seqWealth_const`, `seqBetProb_isPMF`
  (`Gambling.DependentRaces`).
* (6.31), (6.33)–(6.35): `propBet`, `seqBetProb_propBet`, `expectedLogWealth`,
  `expectedLogWealth_le`, `expectedLogWealth_propBet`, `expectedLogWealth_propBet_succ_sub`.
* (6.36): `tendsto_expectedLogWealth_propBet`.
* Example 6.3.1 (Red and Black), (6.39): `deckPMF`, `example_6_3_1`, `example_6_3_1_optimal`
  (here).

### 6.4 The entropy of English
* The zeroth-order model and the size of the third-order table: `example_6_4_zeroOrder`,
  `example_6_4_table` (here).

### 6.5 Data compression and gambling
* (6.41)–(6.43): `seqWealth_const`, `seqBetProb_isPMF` (`Gambling.DependentRaces`).
* The twin compressor: `gamblerCode`, `gamblerCode_injective`, `length_gamblerCode_lt`,
  `expectedLength_gamblerCode_lt` (`Gambling.DataCompression`).

### 6.6 Gambling estimate of the entropy of English
* (6.44)–(6.50): `seqWealth_const`, `expectedLogWealth_eq`, `expectedLogWealth_div_le`
  (`Gambling.DependentRaces`), with `StochasticProcess.mul_entropyRate_le_jointEntropy`
  (`StochasticProcess.Basic`).

## Not formalized

* The growth of wealth with probability one for ergodic races (6.37), which the book proves in
  Chapter 16.
* In Example 6.3.1, the equivalence of betting on the whole deck with sequential proportional
  betting card by card (only the direction from sequential betting to betting on sequences,
  `seqWealth_const`, is formalized).
* The Markov approximations of English, the cryptographic remarks, the Shannon guessing game and
  the experimental estimates of the entropy of English.
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 6.1: The horse race -/

/-- **Example 6.1.1.** Two horses at even odds (`2`-for-`1` on each): the optimal doubling rate is
`W*(p) = log 2 - H(p)` nats, that is `1 - H(p)` bits. -/
theorem example_6_1_1 {p : Fin 2 → ℝ} (hp : IsPMF p) :
    optDoublingRate (fun _ => 2) p = log 2 - entropy p ∧
      optDoublingRate (fun _ => 2) p / log 2 = 1 - entropy p / log 2 := by
  have h : optDoublingRate (fun _ => 2) p = log 2 - entropy p := by
    rw [optDoublingRate_eq hp fun _ => two_pos, ← sum_mul, hp.sum_eq_one, one_mul]
  refine ⟨h, ?_⟩
  rw [h, sub_div, div_self (log_pos one_lt_two).ne']

/-- **Example 6.1.1, (6.15).** With proportional betting on two horses at even odds, the wealth
grows like `Sₙ ≐ exp (n (log 2 - H(p)))`: `(1/n) log Sₙ → log 2 - H(p)` in probability. -/
theorem example_6_1_1_growth {p : Fin 2 → ℝ} (hp : IsPMF p) (hpos : ∀ x, 0 < p x) :
    TendstoInProb (fun n => iidPMF p n) (fun n x => log (wealth p (fun _ => 2) x) / n)
      (log 2 - entropy p) := by
  have h := log_wealth_div_tendstoInProb (o := fun _ => 2) hp fun x => mul_pos (hpos x) two_pos
  rwa [doublingRate_self hp fun _ => two_pos, ← sum_mul, hp.sum_eq_one, one_mul] at h

/-- **Section 6.1, subcase 2.** With superfair odds of `3`-for-`1` on two equally likely horses, a
Dutch book that keeps cash (bet `1/3` on each horse, keep `1/3`) returns `4/3` whichever horse
wins. It is risk-free but does not optimize the doubling rate: proportional betting has the larger
doubling rate `log (3/2) > log (4/3)`. (The book's Dutch book `b(x) = c/o(x)` of
`dutchBook_wealthRelative` is here `b = (1/2, 1/2)`, which is proportional betting.) -/
theorem example_6_1_dutchBook :
    (∀ _ : Fin 2, (1 : ℝ) / 3 + 1 / 3 * 3 = 4 / 3) ∧
      cashDoublingRate (1 / 3) (fun _ => 1 / 3) (fun _ => 3) (fun _ : Fin 2 => 1 / 2) =
        log (4 / 3) ∧
      doublingRate (fun _ => 1 / 2) (fun _ => 3) (fun _ : Fin 2 => 1 / 2) = log (3 / 2) ∧
      log (4 / 3) < log (3 / 2) := by
  refine ⟨fun _ => by norm_num, ?_, ?_, log_lt_log (by norm_num) (by norm_num)⟩
  · simp only [cashDoublingRate, Fin.sum_univ_two]
    norm_num
    ring
  · simp only [doublingRate, Fin.sum_univ_two]
    norm_num
    ring

/-- **Section 6.1, subcase 3.** With subfair odds proportional gambling is no longer log-optimal:
for two equally likely horses at `1`-for-`1`, proportional betting has doubling rate
`-log 2 < 0`, while keeping all the wealth as cash has doubling rate `0`. -/
theorem example_6_1_subfair :
    doublingRate (fun _ => 1 / 2) (fun _ => 1) (fun _ : Fin 2 => 1 / 2) = -log 2 ∧
      cashDoublingRate 1 (fun _ => 0) (fun _ => 1) (fun _ : Fin 2 => 1 / 2) = 0 ∧
      -log 2 < 0 := by
  refine ⟨?_, ?_, neg_neg_of_pos (log_pos one_lt_two)⟩
  · simp only [doublingRate, Fin.sum_univ_two, mul_one, one_div, log_inv]
    ring
  · simp [cashDoublingRate]

/-! ## Section 6.3: Dependent horse races and entropy rate -/

/-- **Example 6.3.1 (Red and Black).** The order of the cards in a deck of `26` red (`true`) and
`26` black cards: all `C(52, 26)` orders are equally likely. -/
def deckPMF : (Fin 52 → Bool) → ℝ := fun x => if numOnes x = 26 then 1 / (Nat.choose 52 26) else 0

lemma choose_52_26 : Nat.choose 52 26 = 495918532948104 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

lemma card_deck : #(univ.filter fun x : Fin 52 → Bool => numOnes x = 26) = Nat.choose 52 26 := by
  simpa using card_numOnes_eq 52 26

lemma deckPMF_isPMF : IsPMF deckPMF := by
  have hC : (0 : ℝ) < Nat.choose 52 26 := by exact_mod_cast Nat.choose_pos (by norm_num)
  refine ⟨fun x => by unfold deckPMF; split_ifs <;> positivity, ?_⟩
  simp only [deckPMF, sum_ite, sum_const_zero, add_zero, sum_const, card_deck, nsmul_eq_mul]
  field_simp

/-- **Example 6.3.1, (6.39).** Betting `1/C(52, 26)` of the wealth on each possible order of the
deck, at `2`-for-`1` odds on each card, multiplies the wealth by `2⁵²/C(52, 26) ≈ 9.08` whatever
the order: the return does not depend on the sequence. -/
theorem example_6_3_1 :
    (∀ x, numOnes x = 26 → (2 : ℝ) ^ 52 * deckPMF x = 2 ^ 52 / Nat.choose 52 26) ∧
      9.08 < (2 : ℝ) ^ 52 / Nat.choose 52 26 ∧ (2 : ℝ) ^ 52 / Nat.choose 52 26 < 9.09 := by
  refine ⟨fun x hx => by simp [deckPMF, hx, div_eq_mul_inv], ?_, ?_⟩ <;>
    rw [choose_52_26] <;> norm_num

/-- **Example 6.3.1.** Betting `b = p` on the whole deck is proportional gambling in the horse race
whose horses are the `2⁵²` orders, at `2⁵²`-for-`1` odds: it is log-optimal, with optimal doubling
rate `log 2⁵² - H(p)`. -/
theorem example_6_3_1_optimal :
    optDoublingRate (fun _ => (2 : ℝ) ^ 52) deckPMF = 52 * log 2 - entropy deckPMF ∧
      doublingRate deckPMF (fun _ => (2 : ℝ) ^ 52) deckPMF = 52 * log 2 - entropy deckPMF := by
  have ho : ∀ x : Fin 52 → Bool, (0 : ℝ) < 2 ^ 52 := fun _ => by positivity
  have hsum : ∑ x, deckPMF x * log ((2 : ℝ) ^ 52) = 52 * log 2 := by
    rw [← sum_mul, deckPMF_isPMF.sum_eq_one, one_mul, log_pow]
    norm_num
  rw [optDoublingRate_eq deckPMF_isPMF ho, doublingRate_self deckPMF_isPMF ho, hsum]
  exact ⟨rfl, rfl⟩

/-! ## Section 6.4: The entropy of English -/

/-- **Section 6.4.** The zeroth-order model of English, with `27` equiprobable symbols, has entropy
`log₂ 27 ≈ 4.75` bits per letter (the book rounds it to `4.76`). -/
theorem example_6_4_zeroOrder :
    entropy (uniformPMF (Fin 27)) / log 2 = logb 2 27 ∧ 4.75 < logb 2 27 ∧ logb 2 27 < 4.76 := by
  have hu : entropy (uniformPMF (Fin 27)) = log 27 := by
    have h := relEntropyReal_uniform (uniformPMF_isPMF (α := Fin 27))
    rw [relEntropyReal_self, Fintype.card_fin] at h
    push_cast at h
    linarith
  have hl : 0 < log 2 := log_pos one_lt_two
  -- `2¹⁹ < 27⁴` and `27²⁵ < 2¹¹⁹`.
  have h1 : log ((2 : ℝ) ^ 19) < log ((27 : ℝ) ^ 4) := log_lt_log (by positivity) (by norm_num)
  have h2 : log ((27 : ℝ) ^ 25) < log ((2 : ℝ) ^ 119) := log_lt_log (by positivity) (by norm_num)
  rw [log_pow, log_pow] at h1 h2
  push_cast at h1 h2
  refine ⟨by rw [hu, logb], ?_, ?_⟩ <;> rw [logb]
  · rw [lt_div_iff₀ hl]
    linarith
  · rw [div_lt_iff₀ hl]
    linarith

/-- **Section 6.4.** A third-order Markov model of English needs the `27⁴ = 531441` probabilities
`p(xᵢ | xᵢ₋₁, xᵢ₋₂, xᵢ₋₃)`. -/
theorem example_6_4_table : Fintype.card (Fin 4 → Fin 27) = 531441 := by
  simp

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems of Chapter 6.
-/

/-- **Theorem 6.1.1.** -/
alias theorem_6_1_1 := log_wealth_div_tendstoInProb

/-- **Theorem 6.1.2 (Proportional gambling is log-optimal).** -/
alias theorem_6_1_2 := optDoublingRate_eq

/-- **Theorem 6.1.3 (Conservation theorem).** -/
alias theorem_6_1_3 := optDoublingRate_add_entropy

/-- **Theorem 6.2.1.** -/
alias theorem_6_2_1 := optCondDoublingRate_sub

end InfoTheory.CoverThomas
