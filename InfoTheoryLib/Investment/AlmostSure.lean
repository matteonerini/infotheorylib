/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Investment.Causal
public import Mathlib.Probability.StrongLaw

/-!
# Almost sure growth of wealth

For i.i.d. market outcomes, the wealth of the constant rebalanced portfolio `b` grows as
`e^{nW(b, F)}` with probability `1`, by the strong law of large numbers (Theorem 16.1.1). No causal
strategy beats the log-optimal portfolio to first order in the exponent, with probability `1`
(Theorem 16.3.1): `E(Sₙ/Sₙ*) ≤ 1` and Markov's inequality give `Pr(Sₙ/Sₙ* ≥ n²) ≤ 1/n²`, and the
Borel–Cantelli lemma concludes. The same argument, for any nonnegative random variables with
`E Zₙ ≤ 1`, is the sandwich lemma of the general AEP (Lemma 16.8.3).

The outcomes are random variables `Y₀, Y₁, …` on a probability space `(Ω, P)` with values in the
finite set `ι`, independent and with law `F`.

## Main statements

* `measureReal_seq_eq_iidPMF`, `integral_comp_seq`: the first `n` outcomes have the law
  `∏ᵢ F(sᵢ)`, and expectations of functions of them are finite sums.
* `tendsto_log_stratWealth_const_ae`: **Theorem 16.1.1, (16.4)–(16.6)**
  `(1/n) log Sₙ → W(b, F)` with probability `1`; for the log-optimal portfolio the limit is `W*`.
* `ae_eventually_log_le_two_log`, `ae_limsup_log_div_le_zero`: **(16.34)–(16.38),
  (16.207)–(16.211)** if `Zₙ ≥ 0` and `E Zₙ ≤ 1`, then `(1/n) log Zₙ ≤ ε` eventually, for every
  `ε > 0`, with probability `1`.
* `sum_mul_ratio_le_one`: **Lemma 16.8.3, (16.199)–(16.202)** `E_p (q/p) ≤ 1`.
* `ae_limsup_log_ratio_le_zero`: **Theorem 16.3.1 (asymptotic optimality of the log-optimal
  portfolio)**, `limsup (1/n) log (Sₙ/Sₙ*) ≤ 0` with probability `1`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 16.1, 16.3
  and 16.8
-/

open Real Finset Filter Topology MeasureTheory ProbabilityTheory

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-! ### Finite-valued random variables -/

omit [Fintype ι] in
lemma measurableSet_of_finite' [Finite ι] (s : Set ι) : MeasurableSet s :=
  (Set.toFinite s).measurableSet

/-- The expectation of a function of a random variable with finitely many values is a finite
sum. -/
lemma integral_comp_of_finite {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {V : Ω → T} (hV : Measurable V) (g : T → ℝ) :
    ∫ ω, g (V ω) ∂P = ∑ t, P.real (V ⁻¹' {t}) * g t := by
  classical
  have hpt : ∀ ω, g (V ω) = ∑ t, (V ⁻¹' {t}).indicator (fun _ => g t) ω := fun ω => by
    rw [sum_eq_single (V ω) (fun t _ ht => by simp [Set.indicator, Ne.symm ht]) (by simp)]
    simp [Set.indicator]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine sum_congr rfl fun t _ => ?_
    rw [integral_indicator_const _ (hV (measurableSet_singleton t)), smul_eq_mul]
  · exact fun t _ => (integrable_const (g t)).indicator (hV (measurableSet_singleton t))

lemma integrable_comp_of_finite {T : Type*} [Finite T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {V : Ω → T} (hV : Measurable V) (g : T → ℝ) :
    Integrable (fun ω => g (V ω)) P := by
  have := Fintype.ofFinite T
  refine (integrable_const (∑ t, |g t|)).mono'
    ((measurable_of_countable g).comp hV).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact single_le_sum (f := fun t => |g t|) (fun t _ => abs_nonneg _) (mem_univ (V ω))

variable {F : ι → ℝ} {Y : ℕ → Ω → ι}

omit [Fintype ι] [IsProbabilityMeasure P] in
/-- **(16.3)** For independent outcomes with law `F`, the first `n` outcomes take the values `s`
with probability `∏ᵢ F(sᵢ)`. -/
theorem measureReal_seq_eq_iidPMF [Finite ι] (hind : iIndepFun Y P)
    (hlaw : ∀ i k, P.real (Y i ⁻¹' {k}) = F k) (n : ℕ) (s : Fin n → ι) :
    P.real ((fun ω (j : Fin n) => Y j ω) ⁻¹' {s}) = iidPMF F n s := by
  set sets : ℕ → Set ι := fun i => {y | ∀ h : i < n, y = s ⟨i, h⟩}
  have hset : (fun ω (j : Fin n) => Y j ω) ⁻¹' {s} = ⋂ i ∈ range n, Y i ⁻¹' sets i := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, mem_range]
    constructor
    · intro h i _ hi
      exact (congrFun h ⟨i, hi⟩).symm ▸ rfl
    · intro h
      funext j
      exact h j j.isLt j.isLt
  have hsets : ∀ j : Fin n, Y j ⁻¹' sets j = Y j ⁻¹' {s j} := fun j => by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, sets, Set.mem_ofPred_eq]
    exact ⟨fun h => h j.isLt, fun h _ => h⟩
  rw [hset, measureReal_def, hind.measure_inter_preimage_eq_mul (range n)
    (fun i _ => measurableSet_of_finite' _), ENNReal.toReal_prod,
    ← Fin.prod_univ_eq_prod_range (fun i => (P (Y i ⁻¹' sets i)).toReal) n]
  refine prod_congr rfl fun j _ => ?_
  rw [hsets j, ← measureReal_def, hlaw]

/-- The expectation of a function of the first `n` outcomes is `∑ₛ ∏ᵢ F(sᵢ) g(s)`. -/
theorem integral_comp_seq (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i k, P.real (Y i ⁻¹' {k}) = F k) (n : ℕ) (g : (Fin n → ι) → ℝ) :
    ∫ ω, g (fun j => Y j ω) ∂P = ∑ s, iidPMF F n s * g s := by
  rw [integral_comp_of_finite (Measurable.of_eval (f := fun ω (j : Fin n) => Y j ω)
    fun j => hY j) g]
  exact sum_congr rfl fun s _ => by rw [measureReal_seq_eq_iidPMF hind hlaw]

/-! ### Theorem 16.1.1 -/

omit [IsProbabilityMeasure P] [Fintype ι] in
lemma identDistrib_of_law [Countable ι] {Y : ℕ → Ω → ι} (hY : ∀ i, Measurable (Y i))
    [IsFiniteMeasure P] (hlaw : ∀ i k, P.real (Y i ⁻¹' {k}) = F k) (i : ℕ) :
    IdentDistrib (Y i) (Y 0) P P := by
  refine ⟨(hY i).aemeasurable, (hY 0).aemeasurable, ?_⟩
  rw [Measure.ext_iff_singleton]
  intro k
  rw [Measure.map_apply (hY i) (measurableSet_singleton k),
    Measure.map_apply (hY 0) (measurableSet_singleton k), ← ofReal_measureReal,
    ← ofReal_measureReal, hlaw, hlaw]

/-- **Theorem 16.1.1, (16.4)–(16.6).** For i.i.d. outcomes with law `F`, the wealth `Sₙ` of the
constant rebalanced portfolio `b` satisfies `(1/n) log Sₙ → W(b, F)` with probability `1`. -/
theorem tendsto_log_stratWealth_const_ae {m : ℕ} {x : ι → Fin m → ℝ} (hx : IsPosMarket x)
    {b : Fin m → ℝ} (hb : IsPMF b) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i k, P.real (Y i ⁻¹' {k}) = F k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      log (stratWealth (CausalStrategy.const b) x n fun j => Y j ω) / n) atTop
        (𝓝 (growthRate b F x)) := by
  set f : ι → ℝ := fun k => log (wealthRel b (x k))
  have hf : Measurable f := measurable_of_countable f
  set Z : ℕ → Ω → ℝ := fun i ω => f (Y i ω)
  have hint : Integrable (Z 0) P := integrable_comp_of_finite (hY 0) f
  have hindep : Pairwise fun i j => IndepFun (Z i) (Z j) P := fun i j hij =>
    (hind.indepFun hij).comp hf hf
  have hident : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    (identDistrib_of_law hY hlaw i).comp hf
  have hmean : ∫ ω, Z 0 ω ∂P = growthRate b F x := by
    rw [integral_comp_of_finite (hY 0) f]
    simp only [hlaw, growthRate, f]
  have hslln := strong_law_ae Z hint hindep hident
  filter_upwards [hslln] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  rw [log_stratWealth_const hb hx, smul_eq_mul, ← Fin.sum_univ_eq_sum_range (fun i => Z i ω) n,
    inv_mul_eq_div]

/-- **Theorem 16.1.1** For the log-optimal portfolio `b*`, `(1/n) log Sₙ* → W*` with
probability `1`. -/
theorem IsLogOptimal.tendsto_log_stratWealth_ae {m : ℕ} {x : ι → Fin m → ℝ}
    (hx : IsPosMarket x) {b : Fin m → ℝ} (h : IsLogOptimal F x b) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y P) (hlaw : ∀ i k, P.real (Y i ⁻¹' {k}) = F k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      log (stratWealth (CausalStrategy.const b) x n fun j => Y j ω) / n) atTop
        (𝓝 (optGrowthRate F x)) := by
  rw [h.optGrowthRate_eq]
  exact tendsto_log_stratWealth_const_ae hx h.1 hY hind hlaw

/-! ### The Borel–Cantelli argument -/

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- **(16.34)–(16.37), (16.207)–(16.210)** If `Zₙ ≥ 0` and `E Zₙ ≤ 1`, then with probability `1`,
`log Zₙ ≤ 2 log (n + 1)` for all large `n`: Markov's inequality gives
`Pr(Zₙ ≥ (n + 1)²) ≤ 1/(n + 1)²`, and the Borel–Cantelli lemma applies. -/
theorem ae_eventually_log_le_two_log {Z : ℕ → Ω → ℝ}
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hZi : ∀ n, Integrable (Z n) P) (hZ1 : ∀ n, ∫ ω, Z n ω ∂P ≤ 1) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, log (Z n ω) ≤ 2 * log ((n : ℝ) + 1) := by
  set s : ℕ → Set Ω := fun n => {ω | ((n : ℝ) + 1) ^ 2 ≤ Z n ω}
  have hs : ∀ n, P (s n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := fun n => by
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (hZ0 n)) (hZi n)
      (((n : ℝ) + 1) ^ 2)
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact h.trans (hZ1 n)
  have hsum : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  have hfin : ∑' n, P (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hs)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with n hn
  simp only [s, Set.mem_ofPred_eq, not_le] at hn
  rcases (hZ0 n ω).lt_or_eq with hz | hz
  · rw [show (2 : ℝ) * log ((n : ℝ) + 1) = log (((n : ℝ) + 1) ^ 2) by rw [log_pow]; norm_num]
    exact (log_lt_log hz hn).le
  · rw [← hz, log_zero]
    exact mul_nonneg zero_le_two (log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))

lemma tendsto_two_log_div : Tendsto (fun n : ℕ => 2 * log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 := (h.comp hx).const_mul 2
  rw [mul_zero] at h2
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  simp only [Function.comp, pow_one, one_mul]
  rw [show (n : ℝ) + 1 + -1 = n by ring, mul_div_assoc]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- If `Zₙ ≥ 0` and `E Zₙ ≤ 1`, then `limsup (1/n) log Zₙ ≤ 0` with probability `1`: for every
`ε > 0`, eventually `(1/n) log Zₙ ≤ ε`. -/
theorem ae_limsup_log_div_le_zero {Z : ℕ → Ω → ℝ}
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hZi : ∀ n, Integrable (Z n) P) (hZ1 : ∀ n, ∫ ω, Z n ω ∂P ≤ 1) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, log (Z n ω) / n ≤ ε := by
  filter_upwards [ae_eventually_log_le_two_log hZ0 hZi hZ1] with ω hω ε hε
  filter_upwards [hω, tendsto_two_log_div.eventually (gt_mem_nhds hε),
    eventually_gt_atTop 0] with n h1 h2 h3
  have hn : (0 : ℝ) < n := by exact_mod_cast h3
  exact (div_le_div_of_nonneg_right h1 hn.le).trans h2.le

/-- **Lemma 16.8.3, (16.199)–(16.202).** For pmfs `p` and `q` on a finite set,
`E_p (q(X)/p(X)) = q(supp p) ≤ 1`, so the sandwich argument applies to `Zₙ = q(Xⁿ)/p(Xⁿ)`. -/
lemma sum_mul_ratio_le_one {α : Type*} [Fintype α] {p q : α → ℝ} (hp : IsPMF p)
    (hq : IsPMF q) : ∑ a, p a * (q a / p a) ≤ 1 := by
  calc ∑ a, p a * (q a / p a) ≤ ∑ a, q a := sum_le_sum fun a _ => by
        rcases (hp.nonneg a).lt_or_eq with h | h
        · rw [mul_div_cancel₀ _ h.ne']
        · rw [← h, zero_mul]
          exact hq.nonneg a
    _ = 1 := hq.sum_eq_one

/-! ### Theorem 16.3.1 -/

/-- **Theorem 16.3.1 (Asymptotic optimality of the log-optimal portfolio), (16.32)–(16.38).** For
i.i.d. outcomes with law `F`, the wealth `Sₙ` of any causal strategy and the wealth `Sₙ*` of the
log-optimal portfolio satisfy `limsup (1/n) log (Sₙ/Sₙ*) ≤ 0` with probability `1`. -/
theorem ae_limsup_log_ratio_le_zero {m : ℕ} {x : ι → Fin m → ℝ} (hx : IsPosMarket x)
    (hF : IsPMF F) {b : Fin m → ℝ} (h : IsLogOptimal F x b) {β : CausalStrategy m ι}
    (hβ : β.IsValid) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i k, P.real (Y i ⁻¹' {k}) = F k) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      log (stratWealth β x n (fun j => Y j ω) /
        stratWealth (CausalStrategy.const b) x n (fun j => Y j ω)) / n ≤ ε := by
  set g : ∀ n, (Fin n → ι) → ℝ := fun n s =>
    stratWealth β x n s / stratWealth (CausalStrategy.const b) x n s
  have hYn : ∀ n, Measurable fun ω (j : Fin n) => Y j ω := fun n =>
    Measurable.of_eval (f := fun ω (j : Fin n) => Y j ω) fun j => hY j
  refine ae_limsup_log_div_le_zero (Z := fun n ω => g n fun j => Y j ω) (fun n ω => ?_)
    (fun n => integrable_comp_of_finite (hYn n) (g n)) (fun n => ?_)
  · exact (div_pos (stratWealth_pos hβ hx n _)
      (stratWealth_pos (CausalStrategy.isValid_const h.1) hx n _)).le
  · rw [integral_comp_seq hY hind hlaw n (g n)]
    have := (h.isCondLogOptimal_iid hF).sum_law_ratio_le_one hβ hx n
    simpa only [iidProcess_law] using this

end InfoTheory
