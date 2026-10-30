/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Investment.KuhnTucker
public import InfoTheoryLib.StochasticProcess.Independent

/-!
# Causal portfolios in a market process

The market outcomes `X₁, X₂, …` form a stochastic process with values in a finite set `ι`, given by
its finite-dimensional laws, and outcome `k` has price relatives `x(k)`. A causal (nonanticipating)
portfolio strategy chooses the portfolio `bᵢ(X₁, …, Xᵢ₋₁)` of day `i` from the past outcomes
(Section 16.3). The conditionally log-optimal strategy uses on each day the log-optimal portfolio
of the conditional law of the next outcome given the past (Section 16.5).

The conditional law of `Xₙ₊₁` given `(X₁, …, Xₙ) = s` is used unnormalized, as the weights
`k ↦ p(s, k)`; since growth rates are linear in the weights, this gives the conditional growth
rates multiplied by `p(s)` without dividing by `p(s)`.

## Main definitions

* `CausalStrategy m ι`: a nonanticipating portfolio strategy; `CausalStrategy.IsValid`: all its
  portfolios are pmfs; `CausalStrategy.const b`: the constant rebalanced portfolio `b`.
* `stratWealth β x n s`: **(16.25), (16.54)** the wealth `Sₙ = ∏ᵢ bᵢᵗxᵢ` after the outcomes `s`.
* `condLaw P n s`: the weights `k ↦ p(s, k)` of the conditional law of `Xₙ₊₁` given the past `s`.
* `IsCondLogOptimal P x β`: `β` is conditionally log-optimal.
* `condOptGrowth P x n`: **(16.57)–(16.58)** `W*(Xₙ₊₁ | X₁, …, Xₙ)`.
* `marketOptGrowth P x n`: **(16.59)** `W*(X₁, …, Xₙ) = max E log Sₙ`.

## Main statements

* `IsCondLogOptimal.sum_condLaw_ratio_le`: **(16.68)–(16.70)** `Sₙ/Sₙ*` is a supermartingale.
* `IsCondLogOptimal.sum_law_ratio_le_one`: **(16.33), (16.76)** `E(Sₙ/Sₙ*) ≤ 1`.
* `IsCondLogOptimal.prob_ratio_ge_le`: **(16.34), (16.77)** `Pr(Sₙ ≥ t Sₙ*) ≤ 1/t`.
* `sum_law_log_stratWealth`: the chain rule (16.55) for `E log Sₙ`.
* `sum_law_log_stratWealth_le`, `isGreatest_marketOptGrowth`: **(16.55)–(16.60)** the conditionally
  log-optimal strategy maximizes `E log Sₙ`, and `W*(X₁, …, Xₙ) = ∑ᵢ W*(Xᵢ | X₁, …, Xᵢ₋₁)`.
* `sum_iid_log_stratWealth_le`: **Lemma 16.3.1** for an i.i.d. market, `E log Sₙ ≤ n W*` with
  equality for the constant log-optimal portfolio.
* `condOptGrowth_mono`, `tendsto_marketOptGrowth`: **Theorem 16.5.1**, for a stationary market
  `W*(Xₙ | X₁, …, Xₙ₋₁)` is nondecreasing and `W*∞ = lim W*(X₁, …, Xₙ)/n` exists.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 16.3 and
  16.5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- **Definition (Section 16.3).** A nonanticipating (causal) portfolio strategy: the portfolio
`bᵢ(x₁, …, xᵢ₋₁)` used on day `i` after the outcomes `x₁, …, xᵢ₋₁`. -/
def CausalStrategy (m : ℕ) (ι : Type*) : Type _ := ∀ i : ℕ, (Fin i → ι) → Fin m → ℝ

namespace CausalStrategy

/-- All the portfolios of the strategy are pmfs. -/
def IsValid (β : CausalStrategy m ι) : Prop := ∀ i s, IsPMF (β i s)

/-- The constant rebalanced portfolio `b`. -/
def const (b : Fin m → ℝ) : CausalStrategy m ι := fun _ _ => b

omit [Fintype ι] in
lemma isValid_const {b : Fin m → ℝ} (hb : IsPMF b) : (const b : CausalStrategy m ι).IsValid :=
  fun _ _ => hb

end CausalStrategy

/-- **(16.25), (16.54)** The wealth `Sₙ = ∏ᵢ bᵢ(x₁, …, xᵢ₋₁)ᵗ x(sᵢ)` of the strategy `β` after the
outcomes `s₁, …, sₙ`, starting from one unit. -/
def stratWealth (β : CausalStrategy m ι) (x : ι → Fin m → ℝ) : (n : ℕ) → (Fin n → ι) → ℝ
  | 0, _ => 1
  | n + 1, s => stratWealth β x n (Fin.init s) * wealthRel (β n (Fin.init s)) (x (s (Fin.last n)))

variable {β β' : CausalStrategy m ι} {x : ι → Fin m → ℝ}

omit [Fintype ι] in
@[simp] lemma stratWealth_zero (s : Fin 0 → ι) : stratWealth β x 0 s = 1 := rfl

omit [Fintype ι] in
lemma stratWealth_snoc (n : ℕ) (s : Fin n → ι) (k : ι) :
    stratWealth β x (n + 1) (Fin.snoc s k) = stratWealth β x n s * wealthRel (β n s) (x k) := by
  simp [stratWealth, Fin.init_snoc, Fin.snoc_last]

omit [Fintype ι] in
lemma stratWealth_pos (hβ : β.IsValid) (hx : IsPosMarket x) (n : ℕ) (s : Fin n → ι) :
    0 < stratWealth β x n s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [stratWealth]
    exact mul_pos (ih _) (wealthRel_pos (hβ _ _) (hx _))

omit [Fintype ι] in
/-- The wealth of a constant rebalanced portfolio `b` is `∏ᵢ bᵗx(sᵢ)`. -/
lemma stratWealth_const (b : Fin m → ℝ) (n : ℕ) (s : Fin n → ι) :
    stratWealth (CausalStrategy.const b) x n s = ∏ i, wealthRel b (x (s i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [stratWealth, ih, Fin.prod_univ_castSucc]
    rfl

omit [Fintype ι] in
lemma log_stratWealth_const {b : Fin m → ℝ} (hb : IsPMF b) (hx : IsPosMarket x) (n : ℕ)
    (s : Fin n → ι) :
    log (stratWealth (CausalStrategy.const b) x n s) = ∑ i, log (wealthRel b (x (s i))) := by
  rw [stratWealth_const, log_prod fun i _ => (wealthRel_pos hb (hx _)).ne']

/-! ### Market processes -/

variable (P : StochasticProcess ι)

/-- The weights `k ↦ p(s, k)` of the conditional law of `Xₙ₊₁` given `(X₁, …, Xₙ) = s`, not
normalized by `p(s)`. -/
def condLaw (n : ℕ) (s : Fin n → ι) (k : ι) : ℝ := P.law (n + 1) (Fin.snoc s k)

variable {P}

lemma condLaw_nonneg (n : ℕ) (s : Fin n → ι) (k : ι) : 0 ≤ condLaw P n s k :=
  (P.isPMF _).nonneg _

lemma sum_condLaw (n : ℕ) (s : Fin n → ι) : ∑ k, condLaw P n s k = P.law n s :=
  P.consistent n s

/-- **Section 16.5** A conditionally log-optimal strategy: on each day, the log-optimal portfolio
for the conditional law of the next outcome given the past. -/
def IsCondLogOptimal (P : StochasticProcess ι) (x : ι → Fin m → ℝ) (β : CausalStrategy m ι) :
    Prop :=
  ∀ n s, IsLogOptimal (condLaw P n s) x (β n s)

lemma IsCondLogOptimal.isValid (h : IsCondLogOptimal P x β) : β.IsValid :=
  fun n s => (h n s).1

/-- A conditionally log-optimal strategy exists. -/
theorem exists_isCondLogOptimal (hm : 0 < m) (hx : IsPosMarket x) :
    ∃ β : CausalStrategy m ι, IsCondLogOptimal P x β := by
  choose β hβ using fun n (s : Fin n → ι) => exists_isLogOptimal hm hx (condLaw P n s)
  exact ⟨β, hβ⟩

/-- **(16.68)–(16.70)** `Sₙ/Sₙ*` is a supermartingale: given the past `s`, the expected next ratio
is at most the current one, `E[Sₙ₊₁/S*ₙ₊₁ | s] ≤ Sₙ(s)/S*ₙ(s)`, with the conditional expectation
multiplied by `p(s)`. -/
theorem IsCondLogOptimal.sum_condLaw_ratio_le {β₀ : CausalStrategy m ι}
    (h : IsCondLogOptimal P x β₀) (hβ : β.IsValid) (hx : IsPosMarket x) (n : ℕ)
    (s : Fin n → ι) :
    ∑ k, condLaw P n s k * (stratWealth β x (n + 1) (Fin.snoc s k) /
        stratWealth β₀ x (n + 1) (Fin.snoc s k)) ≤
      P.law n s * (stratWealth β x n s / stratWealth β₀ x n s) := by
  have hR : 0 ≤ stratWealth β x n s / stratWealth β₀ x n s :=
    (div_pos (stratWealth_pos hβ hx n s) (stratWealth_pos h.isValid hx n s)).le
  have e : ∀ k, stratWealth β x (n + 1) (Fin.snoc s k) / stratWealth β₀ x (n + 1) (Fin.snoc s k) =
      stratWealth β x n s / stratWealth β₀ x n s *
        (wealthRel (β n s) (x k) / wealthRel (β₀ n s) (x k)) := fun k => by
    rw [stratWealth_snoc, stratWealth_snoc]
    field_simp
  simp only [e]
  have hKT := (h n s).sum_ratio_le (condLaw_nonneg n s) hx (hβ n s)
  rw [sum_condLaw] at hKT
  calc ∑ k, condLaw P n s k * (stratWealth β x n s / stratWealth β₀ x n s *
        (wealthRel (β n s) (x k) / wealthRel (β₀ n s) (x k)))
      = stratWealth β x n s / stratWealth β₀ x n s *
          ∑ k, condLaw P n s k * (wealthRel (β n s) (x k) / wealthRel (β₀ n s) (x k)) := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by ring
    _ ≤ stratWealth β x n s / stratWealth β₀ x n s * P.law n s :=
        mul_le_mul_of_nonneg_left hKT hR
    _ = _ := mul_comm _ _

/-- **(16.33), (16.76)** For the conditionally log-optimal wealth `Sₙ*` and the wealth `Sₙ` of any
causal strategy, `E(Sₙ/Sₙ*) ≤ 1`. -/
theorem IsCondLogOptimal.sum_law_ratio_le_one {β₀ : CausalStrategy m ι}
    (h : IsCondLogOptimal P x β₀) (hβ : β.IsValid) (hx : IsPosMarket x) (n : ℕ) :
    ∑ s, P.law n s * (stratWealth β x n s / stratWealth β₀ x n s) ≤ 1 := by
  induction n with
  | zero =>
    simp only [stratWealth_zero, div_one, mul_one]
    exact (P.isPMF 0).sum_eq_one.le
  | succ n ih =>
    rw [sum_snoc]
    exact (sum_le_sum fun s _ => h.sum_condLaw_ratio_le hβ hx n s).trans ih

/-- **(16.34), (16.77)** `Pr(Sₙ ≥ t Sₙ*) ≤ 1/t` for `t > 0`. -/
theorem IsCondLogOptimal.prob_ratio_ge_le {β₀ : CausalStrategy m ι}
    (h : IsCondLogOptimal P x β₀) (hβ : β.IsValid) (hx : IsPosMarket x) (n : ℕ) {t : ℝ}
    (ht : 0 < t) :
    ∑ s ∈ univ.filter (fun s => t * stratWealth β₀ x n s ≤ stratWealth β x n s), P.law n s ≤
      1 / t := by
  rw [le_div_iff₀ ht]
  calc (∑ s ∈ univ.filter (fun s => t * stratWealth β₀ x n s ≤ stratWealth β x n s),
        P.law n s) * t
      ≤ ∑ s ∈ univ.filter (fun s => t * stratWealth β₀ x n s ≤ stratWealth β x n s),
          P.law n s * (stratWealth β x n s / stratWealth β₀ x n s) := by
        rw [sum_mul]
        refine sum_le_sum fun s hs => mul_le_mul_of_nonneg_left ?_ ((P.isPMF n).nonneg s)
        have hs := (mem_filter.1 hs).2
        rw [le_div_iff₀ (stratWealth_pos h.isValid hx n s)]
        linarith
    _ ≤ ∑ s, P.law n s * (stratWealth β x n s / stratWealth β₀ x n s) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun s _ _ =>
          mul_nonneg ((P.isPMF n).nonneg s)
            (div_pos (stratWealth_pos hβ hx n s) (stratWealth_pos h.isValid hx n s)).le
    _ ≤ 1 := h.sum_law_ratio_le_one hβ hx n

/-! ### The chain rule for the optimal growth rate -/

/-- **(16.57)–(16.58)** The conditional optimal growth rate `W*(Xₙ₊₁ | X₁, …, Xₙ) =
E max_b E[log bᵗXₙ₊₁ | X₁, …, Xₙ]`. -/
def condOptGrowth (P : StochasticProcess ι) (x : ι → Fin m → ℝ) (n : ℕ) : ℝ :=
  ∑ s : Fin n → ι, optGrowthRate (condLaw P n s) x

/-- **(16.59)** `W*(X₁, …, Xₙ) = ∑ᵢ W*(Xᵢ | X₁, …, Xᵢ₋₁)`, the maximum of `E log Sₙ` over the
causal strategies (`isGreatest_marketOptGrowth`). -/
def marketOptGrowth (P : StochasticProcess ι) (x : ι → Fin m → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, condOptGrowth P x i

/-- **(16.55)** `E log Sₙ = ∑ᵢ E log bᵢᵗXᵢ`, the expected log return of each day, with the
conditional laws of the outcomes. -/
theorem sum_law_log_stratWealth (hβ : β.IsValid) (hx : IsPosMarket x) (n : ℕ) :
    ∑ s, P.law n s * log (stratWealth β x n s) =
      ∑ i ∈ range n, ∑ s : Fin i → ι, growthRate (β i s) (condLaw P i s) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih, sum_snoc]
    simp only [stratWealth_snoc, growthRate]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    simp only [log_mul (stratWealth_pos hβ hx n s).ne' (wealthRel_pos (hβ n s) (hx _)).ne',
      mul_add, sum_add_distrib, ← sum_mul]
    rw [show ∑ k, P.law (n + 1) (Fin.snoc s k) = P.law n s from P.consistent n s]
    rfl

/-- **(16.55)–(16.56)** Every causal strategy has `E log Sₙ ≤ W*(X₁, …, Xₙ)`. -/
theorem sum_law_log_stratWealth_le (hm : 0 < m) (hβ : β.IsValid) (hx : IsPosMarket x) (n : ℕ) :
    ∑ s, P.law n s * log (stratWealth β x n s) ≤ marketOptGrowth P x n := by
  rw [sum_law_log_stratWealth hβ hx]
  exact sum_le_sum fun i _ => sum_le_sum fun s _ =>
    growthRate_le_optGrowthRate hm hx (hβ i s)

/-- **(16.56)** The conditionally log-optimal strategy has `E log Sₙ* = W*(X₁, …, Xₙ)`. -/
theorem IsCondLogOptimal.sum_law_log_stratWealth (h : IsCondLogOptimal P x β)
    (hx : IsPosMarket x) (n : ℕ) :
    ∑ s, P.law n s * log (stratWealth β x n s) = marketOptGrowth P x n := by
  rw [InfoTheory.sum_law_log_stratWealth h.isValid hx]
  exact sum_congr rfl fun i _ => sum_congr rfl fun s _ => (h i s).optGrowthRate_eq.symm

/-- **(16.59)–(16.60)** `W*(X₁, …, Xₙ)` is the maximum of `E log Sₙ` over the causal strategies,
and it satisfies the chain rule `W*(X₁, …, Xₙ) = ∑ᵢ W*(Xᵢ | X₁, …, Xᵢ₋₁)`. -/
theorem isGreatest_marketOptGrowth (hm : 0 < m) (hx : IsPosMarket x) (n : ℕ) :
    IsGreatest {w | ∃ β : CausalStrategy m ι, β.IsValid ∧
      w = ∑ s, P.law n s * log (stratWealth β x n s)} (marketOptGrowth P x n) := by
  obtain ⟨β₀, h₀⟩ := exists_isCondLogOptimal (P := P) hm hx
  refine ⟨⟨β₀, h₀.isValid, (h₀.sum_law_log_stratWealth hx n).symm⟩, ?_⟩
  rintro _ ⟨β, hβ, rfl⟩
  exact sum_law_log_stratWealth_le hm hβ hx n

/-! ### Independent markets -/

lemma IsLogOptimal.smul {F : ι → ℝ} {b : Fin m → ℝ} (h : IsLogOptimal F x b) {c : ℝ}
    (hc : 0 ≤ c) : IsLogOptimal (c • F) x b :=
  ⟨h.1, fun b' hb' => by
    rw [growthRate_smul, growthRate_smul]
    exact mul_le_mul_of_nonneg_left (h.2 b' hb') hc⟩

lemma condLaw_iidProcess {F : ι → ℝ} (hF : IsPMF F) (n : ℕ) (s : Fin n → ι) :
    condLaw (iidProcess F hF) n s = (iidPMF F n s) • F := by
  funext k
  simp only [condLaw, iidProcess_law, iidPMF, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, Pi.smul_apply, smul_eq_mul]

/-- For an i.i.d. market, the constant log-optimal portfolio is conditionally log-optimal. -/
theorem IsLogOptimal.isCondLogOptimal_iid {F : ι → ℝ} (hF : IsPMF F) {b : Fin m → ℝ}
    (h : IsLogOptimal F x b) :
    IsCondLogOptimal (iidProcess F hF) x (CausalStrategy.const b) := fun n s => by
  rw [condLaw_iidProcess]
  exact h.smul (iidPMF_nonneg hF.nonneg s)

/-- **Lemma 16.3.1, (16.27)–(16.31).** In an i.i.d. market with law `F`, every causal strategy has
`E log Sₙ ≤ n W*(F)`, with equality for the constant log-optimal portfolio. -/
theorem sum_iid_log_stratWealth_le (hm : 0 < m) {F : ι → ℝ} (hF : IsPMF F) (hβ : β.IsValid)
    (hx : IsPosMarket x) (n : ℕ) :
    ∑ s, iidPMF F n s * log (stratWealth β x n s) ≤ n * optGrowthRate F x := by
  have h := sum_law_log_stratWealth_le (P := iidProcess F hF) hm hβ hx n
  have e : marketOptGrowth (iidProcess F hF) x n = n * optGrowthRate F x := by
    simp only [marketOptGrowth, condOptGrowth, condLaw_iidProcess,
      optGrowthRate_smul hm hx (iidPMF_nonneg hF.nonneg _), ← sum_mul,
      (iidPMF_isPMF hF _).sum_eq_one, one_mul, sum_const, card_range, nsmul_eq_mul]
  rw [e] at h
  exact h

/-- **Lemma 16.3.1** The constant log-optimal portfolio achieves `E log Sₙ* = n W*(F)`. -/
theorem IsLogOptimal.sum_iid_log_stratWealth {F : ι → ℝ} (hF : IsPMF F) {b : Fin m → ℝ}
    (h : IsLogOptimal F x b) (hx : IsPosMarket x) (n : ℕ) :
    ∑ s, iidPMF F n s * log (stratWealth (CausalStrategy.const b) x n s) =
      n * optGrowthRate F x := by
  simp only [log_stratWealth_const h.1 hx, mul_sum]
  rw [sum_comm]
  have : ∀ i : Fin n, ∑ s, iidPMF F n s * log (wealthRel b (x (s i))) = growthRate b F x :=
    fun i => by
      rw [show (∑ s, iidPMF F n s * log (wealthRel b (x (s i)))) =
        expect (iidPMF F n) (fun s => log (wealthRel b (x (s i)))) by
          simp only [expect, mul_comm]]
      rw [expect_iidPMF_apply hF (fun k => log (wealthRel b (x k))) i]
      simp only [expect, growthRate, mul_comm]
  simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, h.optGrowthRate_eq]

/-! ### Stationary markets -/

/-- `W*(∑ₐ rₐ) ≤ ∑ₐ W*(rₐ)`. -/
lemma optGrowthRate_sum_le {α : Type*} [Fintype α] (hm : 0 < m) (hx : IsPosMarket x)
    (r : α → ι → ℝ) : optGrowthRate (∑ a, r a) x ≤ ∑ a, optGrowthRate (r a) x := by
  obtain ⟨b, hb⟩ := exists_isLogOptimal hm hx (∑ a, r a)
  rw [hb.optGrowthRate_eq]
  have e : growthRate b (∑ a, r a) x = ∑ a, growthRate b (r a) x := by
    simp only [growthRate, Finset.sum_apply, sum_mul]
    exact sum_comm
  rw [e]
  exact sum_le_sum fun a _ => growthRate_le_optGrowthRate hm hx hb.1

/-- **Theorem 16.5.1 (monotonicity).** For a stationary market, `W*(Xₙ | X₁, …, Xₙ₋₁)` is
nondecreasing in `n`: knowing more of the past cannot decrease the optimal growth rate. -/
theorem condOptGrowth_mono (hm : 0 < m) (hx : IsPosMarket x) (hP : P.IsStationary) (n : ℕ) :
    condOptGrowth P x n ≤ condOptGrowth P x (n + 1) := by
  unfold condOptGrowth
  rw [sum_cons, sum_comm]
  refine sum_le_sum fun s _ => ?_
  have e : condLaw P n s = ∑ a, fun k => P.law (n + 1 + 1) (Fin.cons a (Fin.snoc s k)) := by
    funext k
    rw [Finset.sum_apply]
    exact (hP (n + 1) (Fin.snoc s k)).symm
  rw [e]
  refine (optGrowthRate_sum_le hm hx _).trans (le_of_eq (sum_congr rfl fun a _ => ?_))
  congr 1
  funext k
  simp only [condLaw]
  rw [Fin.cons_snoc_eq_snoc_cons]

/-- `W*(Xₙ₊₁ | X₁, …, Xₙ) ≤ log c` if all price relatives are at most `c`. -/
lemma condOptGrowth_le (hm : 0 < m) (hx : IsPosMarket x) {c : ℝ} (hc : ∀ k i, x k i ≤ c)
    (n : ℕ) : condOptGrowth P x n ≤ log c := by
  unfold condOptGrowth
  calc ∑ s : Fin n → ι, optGrowthRate (condLaw P n s) x
      ≤ ∑ s : Fin n → ι, (∑ k, condLaw P n s k) * log c := sum_le_sum fun s _ => by
        obtain ⟨b, hb⟩ := exists_isLogOptimal hm hx (condLaw P n s)
        rw [hb.optGrowthRate_eq]
        exact growthRate_le (condLaw_nonneg n s) hx hb.1 hc
    _ = log c := by simp only [sum_condLaw, ← sum_mul, (P.isPMF n).sum_eq_one, one_mul]

/-- **Theorem 16.5.1, (16.61)–(16.64).** For a stationary market, the growth rate
`W*∞ = lim W*(X₁, …, Xₙ)/n` exists and equals `lim W*(Xₙ | X₁, …, Xₙ₋₁)`. -/
theorem tendsto_marketOptGrowth (hm : 0 < m) (hx : IsPosMarket x) (hP : P.IsStationary) :
    ∃ W, Tendsto (condOptGrowth P x) atTop (𝓝 W) ∧
      Tendsto (fun n => marketOptGrowth P x n / n) atTop (𝓝 W) := by
  set c := ∑ k, ∑ i, x k i
  have hc : ∀ k i, x k i ≤ c := fun k i =>
    (single_le_sum (f := fun i => x k i) (fun i _ => (hx k i).le) (mem_univ i)).trans
      (single_le_sum (f := fun k => ∑ i, x k i)
        (fun k _ => sum_nonneg fun i _ => (hx k i).le) (mem_univ k))
  have hmono : Monotone (condOptGrowth P x) := monotone_nat_of_le_succ (condOptGrowth_mono hm hx hP)
  have hbdd : BddAbove (Set.range (condOptGrowth P x)) :=
    ⟨log c, by rintro _ ⟨n, rfl⟩; exact condOptGrowth_le hm hx hc n⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  exact ⟨_, hlim, cesaro_mean hlim⟩

end InfoTheory
