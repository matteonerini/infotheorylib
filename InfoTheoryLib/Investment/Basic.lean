/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Gambling.HorseRace

/-!
# The stock market, growth rates and log-optimal portfolios

A stock market with `m` stocks is a random vector `X = (X₁, …, Xₘ)` of price relatives, the ratio
of the price at the end of the day to the price at the beginning. A portfolio `b` is a pmf on the
stocks: `bᵢ` is the fraction of the wealth invested in stock `i`, and the wealth is multiplied by
the wealth relative `S = bᵗX = ∑ᵢ bᵢ Xᵢ`. With daily reinvestment the wealth grows exponentially at
the growth rate `W(b, F) = E log bᵗX`, maximized by the log-optimal portfolio (Section 16.1).

We describe a market by finitely many outcomes `k : ι`, with probabilities `F k` and price
relatives `x k : Fin m → ℝ`. The growth rate is also defined for an unnormalized nonnegative
weight `F` (a measure on the outcomes); it is linear in `F`, which is how conditional growth rates
are handled later without dividing by probabilities.

## Main definitions

* `wealthRel b v`: the wealth relative `bᵗv = ∑ᵢ bᵢ vᵢ`.
* `growthRate b F x`: **(16.1)** the growth rate `W(b, F) = ∑ₖ F(k) log bᵗx(k)`.
* `optGrowthRate F x`: **(16.2)** the optimal growth rate `W*(F) = max_b W(b, F)`.
* `IsLogOptimal F x b`: `b` is a log-optimal (growth optimal) portfolio.
* `IsPosMarket x`: all price relatives are positive.

## Main statements

* `exists_isLogOptimal`: a log-optimal portfolio exists.
* `concaveOn_growthRate`, `growthRate_add`, `growthRate_smul`, `convexOn_optGrowthRate`:
  **Lemma 16.1.1**, `W(b, F)` is concave in `b` and linear in `F`, and `W*(F)` is convex in `F`.
* `optGrowthRate_add_le`, `optGrowthRate_smul`: `W*` is subadditive and positively homogeneous.
* `convex_isLogOptimal`: **Lemma 16.1.2**, the log-optimal portfolios form a convex set.

## Implementation notes

Logarithms are natural, so growth rates are in nats; the book's doubling rate in bits is
`W / log 2`. We assume that all price relatives are positive (`IsPosMarket`), so that every
portfolio has a positive wealth relative and its logarithm is finite. A market with stocks that
can become worthless, like a horse race, is the limit of positive markets; the horse race itself is
treated in Chapter 6.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 16.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- The wealth relative `S = bᵗv = ∑ᵢ bᵢ vᵢ` of the portfolio `b` when the price relatives are
`v`. -/
def wealthRel (b v : Fin m → ℝ) : ℝ := ∑ i, b i * v i

/-- **Definition (16.1).** The growth rate `W(b, F) = E log bᵗX = ∑ₖ F(k) log bᵗx(k)` of the
portfolio `b` in the market with outcomes `k`, of weights `F(k)` and price relatives `x(k)`. -/
def growthRate (b : Fin m → ℝ) (F : ι → ℝ) (x : ι → Fin m → ℝ) : ℝ :=
  ∑ k, F k * log (wealthRel b (x k))

/-- **Definition (16.2).** The optimal growth rate `W*(F) = max_b W(b, F)`, the maximum over the
portfolios. -/
def optGrowthRate (F : ι → ℝ) (x : ι → Fin m → ℝ) : ℝ :=
  sSup ((fun b => growthRate b F x) '' {b | IsPMF b})

/-- **Definition (Section 16.1).** A log-optimal or growth optimal portfolio: a portfolio
maximizing the growth rate. -/
def IsLogOptimal (F : ι → ℝ) (x : ι → Fin m → ℝ) (b : Fin m → ℝ) : Prop :=
  IsPMF b ∧ ∀ b', IsPMF b' → growthRate b' F x ≤ growthRate b F x

/-- A market in which all price relatives are positive. -/
def IsPosMarket (x : ι → Fin m → ℝ) : Prop := ∀ k i, 0 < x k i

/-! ### Wealth relatives -/

lemma wealthRel_pos {b v : Fin m → ℝ} (hb : IsPMF b) (hv : ∀ i, 0 < v i) : 0 < wealthRel b v := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < b i := by
    by_contra h
    push Not at h
    have : ∑ i, b i ≤ 0 := sum_nonpos fun i _ => h i
    linarith [hb.sum_eq_one]
  calc 0 < b i * v i := mul_pos hi (hv i)
    _ ≤ wealthRel b v := single_le_sum (f := fun i => b i * v i)
        (fun j _ => mul_nonneg (hb.nonneg j) (hv j).le) (mem_univ i)

lemma wealthRel_add_smul (b b' v : Fin m → ℝ) (s t : ℝ) :
    wealthRel (s • b + t • b') v = s * wealthRel b v + t * wealthRel b' v := by
  simp only [wealthRel, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
    mul_sum, mul_assoc]

/-- The wealth relative of the portfolio investing everything in stock `i` is `vᵢ`. -/
lemma wealthRel_single (i : Fin m) (v : Fin m → ℝ) :
    wealthRel (Pi.single i 1) v = v i := by
  simp [wealthRel, Pi.single_apply]

lemma isPMF_single (i : Fin m) : IsPMF (Pi.single i (1 : ℝ) : Fin m → ℝ) :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

/-! ### The set of portfolios -/

/-- The portfolios form a convex set. -/
lemma convex_portfolios : Convex ℝ {b : Fin m → ℝ | IsPMF b} := by
  intro b hb b' hb' s t hs ht hst
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (hb.nonneg i)) (mul_nonneg ht (hb'.nonneg i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      hb.sum_eq_one, hb'.sum_eq_one]
    linarith

/-- The portfolios form a compact set. -/
lemma isCompact_portfolios : IsCompact {b : Fin m → ℝ | IsPMF b} := by
  have hset : {b : Fin m → ℝ | IsPMF b} =
      (⋂ i, {b : Fin m → ℝ | 0 ≤ b i}) ∩ {b | ∑ i, b i = 1} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h.nonneg, h.sum_eq_one⟩, fun h => ⟨h.1, h.2⟩⟩
  have hclosed : IsClosed {b : Fin m → ℝ | IsPMF b} := by
    rw [hset]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  refine (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := 1)).of_isClosed_subset hclosed ?_
  intro b hb
  exact ⟨fun i => hb.nonneg i, fun i => hb.le_one i⟩

lemma portfolios_nonempty (hm : 0 < m) : {b : Fin m → ℝ | IsPMF b}.Nonempty :=
  ⟨_, isPMF_single ⟨0, hm⟩⟩

/-! ### Growth rates -/

variable {F G : ι → ℝ} {x : ι → Fin m → ℝ}

lemma continuousOn_growthRate (hx : IsPosMarket x) :
    ContinuousOn (fun b => growthRate b F x) {b : Fin m → ℝ | IsPMF b} := by
  refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
  refine ContinuousOn.log ?_ fun b hb => (wealthRel_pos hb (hx k)).ne'
  exact (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul continuous_const).continuousOn

/-- **Section 16.1** A log-optimal portfolio exists. -/
theorem exists_isLogOptimal (hm : 0 < m) (hx : IsPosMarket x) (F : ι → ℝ) :
    ∃ b, IsLogOptimal F x b := by
  obtain ⟨b, hb, hmax⟩ := isCompact_portfolios.exists_isMaxOn (portfolios_nonempty hm)
    (continuousOn_growthRate (F := F) hx)
  exact ⟨b, hb, fun b' hb' => hmax hb'⟩

lemma IsLogOptimal.optGrowthRate_eq {b : Fin m → ℝ} (h : IsLogOptimal F x b) :
    optGrowthRate F x = growthRate b F x := by
  refine IsGreatest.csSup_eq ⟨⟨b, h.1, rfl⟩, ?_⟩
  rintro _ ⟨b', hb', rfl⟩
  exact h.2 b' hb'

lemma growthRate_le_optGrowthRate (hm : 0 < m) (hx : IsPosMarket x) {b : Fin m → ℝ}
    (hb : IsPMF b) : growthRate b F x ≤ optGrowthRate F x := by
  obtain ⟨b₀, hb₀⟩ := exists_isLogOptimal hm hx F
  rw [hb₀.optGrowthRate_eq]
  exact hb₀.2 b hb

lemma isLogOptimal_iff (hm : 0 < m) (hx : IsPosMarket x) {b : Fin m → ℝ} :
    IsLogOptimal F x b ↔ IsPMF b ∧ growthRate b F x = optGrowthRate F x := by
  refine ⟨fun h => ⟨h.1, h.optGrowthRate_eq.symm⟩, fun ⟨hb, h⟩ => ⟨hb, fun b' hb' => ?_⟩⟩
  rw [h]
  exact growthRate_le_optGrowthRate hm hx hb'

/-- **Lemma 16.1.1** `W(b, F)` is linear in `F`: additivity. -/
lemma growthRate_add (b : Fin m → ℝ) (F G : ι → ℝ) (x : ι → Fin m → ℝ) :
    growthRate b (F + G) x = growthRate b F x + growthRate b G x := by
  simp only [growthRate, Pi.add_apply, add_mul, sum_add_distrib]

/-- **Lemma 16.1.1** `W(b, F)` is linear in `F`: homogeneity. -/
lemma growthRate_smul (b : Fin m → ℝ) (c : ℝ) (F : ι → ℝ) (x : ι → Fin m → ℝ) :
    growthRate b (c • F) x = c * growthRate b F x := by
  simp only [growthRate, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]

/-- **Lemma 16.1.1** `W(b, F)` is concave in `b`, (16.8). -/
theorem concaveOn_growthRate (hF : ∀ k, 0 ≤ F k) (hx : IsPosMarket x) :
    ConcaveOn ℝ {b : Fin m → ℝ | IsPMF b} (fun b => growthRate b F x) := by
  refine ⟨convex_portfolios, fun b hb b' hb' s t hs ht hst => ?_⟩
  simp only [growthRate, smul_eq_mul, mul_sum]
  rw [← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  rw [wealthRel_add_smul]
  have h := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 (wealthRel_pos hb (hx k)))
    (Set.mem_Ioi.2 (wealthRel_pos hb' (hx k))) hs ht hst
  simp only [smul_eq_mul] at h
  nlinarith [mul_le_mul_of_nonneg_left h (hF k)]

/-- `W*` is subadditive. -/
theorem optGrowthRate_add_le (hm : 0 < m) (hx : IsPosMarket x) (F G : ι → ℝ) :
    optGrowthRate (F + G) x ≤ optGrowthRate F x + optGrowthRate G x := by
  obtain ⟨b, hb⟩ := exists_isLogOptimal hm hx (F + G)
  rw [hb.optGrowthRate_eq, growthRate_add]
  exact add_le_add (growthRate_le_optGrowthRate hm hx hb.1)
    (growthRate_le_optGrowthRate hm hx hb.1)

/-- `W*` is positively homogeneous. -/
theorem optGrowthRate_smul (hm : 0 < m) (hx : IsPosMarket x) {c : ℝ} (hc : 0 ≤ c)
    (F : ι → ℝ) : optGrowthRate (c • F) x = c * optGrowthRate F x := by
  obtain ⟨b, hb⟩ := exists_isLogOptimal hm hx F
  rw [hb.optGrowthRate_eq]
  refine (isLogOptimal_iff hm hx).1 ⟨hb.1, fun b' hb' => ?_⟩ |>.2.symm.trans ?_
  · rw [growthRate_smul, growthRate_smul]
    exact mul_le_mul_of_nonneg_left (hb.2 b' hb') hc
  · exact growthRate_smul b c F x

/-- **Lemma 16.1.1** `W*(F)` is convex in `F`, (16.9)–(16.10). -/
theorem convexOn_optGrowthRate (hm : 0 < m) (hx : IsPosMarket x) :
    ConvexOn ℝ Set.univ (fun F : ι → ℝ => optGrowthRate F x) := by
  refine ⟨convex_univ, fun F _ G _ s t hs ht _ => ?_⟩
  obtain ⟨b, hb⟩ := exists_isLogOptimal hm hx (s • F + t • G)
  simp only [smul_eq_mul]
  rw [hb.optGrowthRate_eq, growthRate_add, growthRate_smul, growthRate_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (growthRate_le_optGrowthRate hm hx hb.1) hs)
    (mul_le_mul_of_nonneg_left (growthRate_le_optGrowthRate hm hx hb.1) ht)

/-- **Lemma 16.1.2** The log-optimal portfolios form a convex set, (16.11). -/
theorem convex_isLogOptimal (hF : ∀ k, 0 ≤ F k) (hx : IsPosMarket x) :
    Convex ℝ {b : Fin m → ℝ | IsLogOptimal F x b} := by
  intro b hb b' hb' s t hs ht hst
  have hmem := convex_portfolios hb.1 hb'.1 hs ht hst
  refine ⟨hmem, fun b'' hb'' => ?_⟩
  have h := (concaveOn_growthRate hF hx).2 hb.1 hb'.1 hs ht hst
  simp only [smul_eq_mul] at h
  calc growthRate b'' F x = s * growthRate b'' F x + t * growthRate b'' F x := by
        rw [← add_mul, hst, one_mul]
    _ ≤ s * growthRate b F x + t * growthRate b' F x :=
        add_le_add (mul_le_mul_of_nonneg_left (hb.2 b'' hb'') hs)
          (mul_le_mul_of_nonneg_left (hb'.2 b'' hb'') ht)
    _ ≤ _ := h

/-- An upper bound on the growth rate: `W(b, F) ≤ (∑ₖ F(k)) log maxᵢₖ xₖᵢ`. -/
lemma growthRate_le (hF : ∀ k, 0 ≤ F k) (hx : IsPosMarket x) {b : Fin m → ℝ} (hb : IsPMF b)
    {c : ℝ} (hc : ∀ k i, x k i ≤ c) : growthRate b F x ≤ (∑ k, F k) * log c := by
  rw [sum_mul]
  refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hF k)
  have hpos := wealthRel_pos hb (hx k)
  refine log_le_log hpos ?_
  calc wealthRel b (x k) ≤ ∑ i, b i * c :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc k i) (hb.nonneg i)
    _ = c := by rw [← sum_mul, hb.sum_eq_one, one_mul]

end InfoTheory
