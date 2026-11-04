/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter15
public import InfoTheoryLib.Investment.Basic
public import InfoTheoryLib.Investment.KuhnTucker
public import InfoTheoryLib.Investment.SideInformation
public import InfoTheoryLib.Investment.Causal
public import InfoTheoryLib.Investment.AlmostSure
public import InfoTheoryLib.Investment.Competitive
public import InfoTheoryLib.Investment.Universal

/-!
# Cover & Thomas, Chapter 16: Information Theory and Portfolio Theory

This file indexes the formalization of Chapter 16 of [cover2006]. The general theory lives in the
topic modules of `InfoTheoryLib`, together with the chapter's only worked example
(`minimaxRatio_two_one`, Section 16.7.1). The list below gives each numbered result with the
declaration that proves it, and the last section of this file defines aliases `theorem_16_2_1`,
… for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Markets.** A stock market with `m` stocks has finitely many outcomes `k : ι`, with
  probabilities `F k` and price relatives `x k : Fin m → ℝ`; all price relatives are positive
  (`IsPosMarket`), so that every portfolio has a positive wealth relative. Growth rates are
  defined for nonnegative weights `F`, not necessarily summing to `1`; this handles conditional
  laws without division.
* **Logarithms** are natural, so growth rates are in nats per day; the book's `2^{nW}` is our
  `exp (n W)`.
* **Market processes** are `StochasticProcess ι` (Chapter 4), and causal strategies choose the
  portfolio of each day from the past outcomes (`CausalStrategy`).
* **Almost sure results** are stated on a probability space `(Ω, P)` with independent outcomes
  `Y₀, Y₁, …` of law `F`, using Mathlib's strong law and the Borel–Cantelli lemma.
* **Universal portfolios** are deterministic: the market vectors are arbitrary nonnegative
  vectors, and ratios `Ŝₙ/Sₙ* ≥ V` are stated as `V Sₙ(b) ≤ Ŝₙ` for every constant rebalanced
  portfolio `b`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 16.1 The stock market: some definitions
* (16.1)–(16.2): `wealthRel`, `growthRate`, `optGrowthRate`, `IsLogOptimal`, `IsPosMarket`;
  existence of a log-optimal portfolio: `exists_isLogOptimal` (`Investment.Basic`).
* Theorem 16.1.1, (16.3)–(16.6): `tendsto_log_stratWealth_const_ae`,
  `IsLogOptimal.tendsto_log_stratWealth_ae` (`Investment.AlmostSure`).
* Lemma 16.1.1, (16.7)–(16.10): `concaveOn_growthRate`, `growthRate_add`, `growthRate_smul`,
  `convexOn_optGrowthRate`; with `optGrowthRate_add_le` and `optGrowthRate_smul`.
* Lemma 16.1.2, (16.11): `convex_isLogOptimal`.

### 16.2 Kuhn–Tucker characterization of the log-optimal portfolio
* Theorem 16.2.1, (16.12)–(16.18): `isLogOptimal_iff_kuhnTucker`, with `IsLogOptimal.sum_le`
  (`Investment.KuhnTucker`).
* Theorem 16.2.2, (16.19)–(16.23): `isLogOptimal_iff_expected_ratio_le`,
  `IsLogOptimal.sum_ratio_le`.
* (16.24): `IsLogOptimal.expected_proportion`.

### 16.3 Asymptotic optimality of the log-optimal portfolio
* (16.25) and the definition of causal strategies: `CausalStrategy`, `stratWealth`
  (`Investment.Causal`).
* Lemma 16.3.1, (16.27)–(16.31): `sum_iid_log_stratWealth_le`,
  `IsLogOptimal.sum_iid_log_stratWealth`.
* Theorem 16.3.1, (16.32)–(16.38): `ae_limsup_log_ratio_le_zero` (`Investment.AlmostSure`), with
  `E(Sₙ/Sₙ*) ≤ 1` (`IsCondLogOptimal.sum_law_ratio_le_one`) and the Borel–Cantelli lemma
  `ae_eventually_log_le_two_log`.

### 16.4 Side information and the growth rate
* Theorem 16.4.1, (16.39)–(16.47): `growthRate_sub_le_relEntropy`, from
  `growthRate_sub_le_of_absCont` (`Investment.SideInformation`).
* Theorem 16.4.2, (16.48)–(16.53): `sideInfo_gain_le`.

### 16.5 Investment in stationary markets
* (16.54)–(16.60): `condLaw`, `IsCondLogOptimal`, `condOptGrowth`, `marketOptGrowth`,
  `sum_law_log_stratWealth`, `sum_law_log_stratWealth_le`,
  `IsCondLogOptimal.sum_law_log_stratWealth`, `isGreatest_marketOptGrowth` (`Investment.Causal`).
* Theorem 16.5.1, (16.61)–(16.64): `condOptGrowth_mono`, `tendsto_marketOptGrowth`.
* Theorem 16.5.2, (16.68)–(16.70): the supermartingale property
  `IsCondLogOptimal.sum_condLaw_ratio_le`.

### 16.6 Competitive optimality of the log-optimal portfolio
* (16.76)–(16.77): `IsCondLogOptimal.sum_law_ratio_le_one`, `IsCondLogOptimal.prob_ratio_ge_le`.
* Theorem 16.6.1, (16.79)–(16.90): `competitive_optimality`, with `measure_le_of_isUniform`
  (`Investment.Competitive`).

### 16.7 Universal portfolios
* (16.91)–(16.93): `crpWealth`, `CausalStrategy`, `stratWealth` (`Investment.Universal`).
* Lemma 16.7.1, (16.96)–(16.98): `ratio_sum_ge`.
* The example `n = 1`, `m = 2`: `minimaxRatio_two_one`.
* (16.105)–(16.107): `seqReturn`, `crpWealth_eq_sum`.
* (16.110)–(16.114): `occ`, `bestWeight`, `prod_le_bestWeight`, `empiricalPortfolio`,
  `minimaxRatio`.
* Theorem 16.7.1, (16.94)–(16.95), (16.116)–(16.131): `exists_universal`, `extremalSeq`,
  `sum_stratWealth_extremal`, `exists_extremal_le`, `minimax_universal`.
* (16.132)–(16.134): `weightStrategy`, `stratWealth_weightStrategy`.
* (16.141)–(16.146): `stratWealth_mixture`, for finite mixtures of constant rebalanced portfolios.
* Lemma 16.7.2, (16.147)–(16.155): `le_stratWealth_of_weights`.

### 16.8 Shannon–McMillan–Breiman theorem
* Lemma 16.8.3, (16.197)–(16.211): `sum_mul_ratio_le_one`, `ae_eventually_log_le_two_log`,
  `ae_limsup_log_div_le_zero` (`Investment.AlmostSure`).

## Not formalized

* The Sharpe–Markowitz mean–variance theory of Section 16.1.
* Markets in which a stock can become worthless, such as the horse race of (16.73)–(16.75) (see
  `optDoublingRate_uniform` in Chapter 6), and the example (16.78).
* The convergence `Sₙ/Sₙ* → V` and the maximal inequality (16.67) of Theorem 16.5.2, and
  Theorem 16.5.3 (the AEP for the stock market), whose proof the book omits.
* The multinomial form of (16.95), the asymptotics (16.135)–(16.138) of `Vₙ`, and the
  horizon-free universal portfolio with the Dirichlet(1/2) prior, Theorem 16.7.2 and
  (16.156)–(16.171); Lemma 16.7.2 is proved for investments with finitely many weights.
* The Shannon–McMillan–Breiman theorem (Theorem 16.8.1) and Lemmas 16.8.1–16.8.2, which need the
  ergodic theorem and Lévy's martingale convergence theorem.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 16.
-/

/-- **Theorem 16.1.1.** -/
alias theorem_16_1_1 := IsLogOptimal.tendsto_log_stratWealth_ae

/-- **Lemma 16.1.1** (concavity in `b`). -/
alias lemma_16_1_1 := concaveOn_growthRate

/-- **Lemma 16.1.1** (convexity of `W*` in `F`). -/
alias lemma_16_1_1_convex := convexOn_optGrowthRate

/-- **Lemma 16.1.2.** -/
alias lemma_16_1_2 := convex_isLogOptimal

/-- **Theorem 16.2.1 (Kuhn–Tucker conditions).** -/
alias theorem_16_2_1 := isLogOptimal_iff_kuhnTucker

/-- **Theorem 16.2.2.** -/
alias theorem_16_2_2 := isLogOptimal_iff_expected_ratio_le

/-- **Lemma 16.3.1.** -/
alias lemma_16_3_1 := sum_iid_log_stratWealth_le

/-- **Theorem 16.3.1 (Asymptotic optimality of the log-optimal portfolio).** -/
alias theorem_16_3_1 := ae_limsup_log_ratio_le_zero

/-- **Theorem 16.4.1.** -/
alias theorem_16_4_1 := growthRate_sub_le_relEntropy

/-- **Theorem 16.4.2.** -/
alias theorem_16_4_2 := sideInfo_gain_le

/-- **Theorem 16.5.1.** -/
alias theorem_16_5_1 := tendsto_marketOptGrowth

/-- **Theorem 16.5.2** (the supermartingale property). -/
alias theorem_16_5_2 := IsCondLogOptimal.sum_condLaw_ratio_le

/-- **Theorem 16.6.1 (Competitive optimality).** -/
alias theorem_16_6_1 := competitive_optimality

/-- **Lemma 16.7.1.** -/
alias lemma_16_7_1 := ratio_sum_ge

/-- **Theorem 16.7.1.** -/
alias theorem_16_7_1 := minimax_universal

/-- **Lemma 16.7.2.** -/
alias lemma_16_7_2 := le_stratWealth_of_weights

/-- **Lemma 16.8.3 (Sandwich).** -/
alias lemma_16_8_3 := ae_limsup_log_div_le_zero

end InfoTheory.CoverThomas
