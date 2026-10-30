/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Investment.Basic

/-!
# The Kuhn–Tucker characterization of the log-optimal portfolio

A portfolio `b*` is log-optimal iff `E(Xᵢ / b*ᵗX) ≤ 1` for every stock `i`, with equality for the
stocks in which it invests (Theorem 16.2.1). Sufficiency follows from `log t ≤ t - 1`: for every
portfolio `b`, `W(b) - W(b*) = E log (bᵗX / b*ᵗX) ≤ E (bᵗX / b*ᵗX) - 1 = ∑ᵢ bᵢ E(Xᵢ / b*ᵗX) - 1`.
Necessity follows from the one-sided derivative of `W` at `b*` towards the portfolio investing
everything in stock `i`, bounded below with `log t ≥ 1 - 1/t`. Consequently the log-optimal
portfolio also maximizes `E(S/S*)` in the sense that `E(S/S*) ≤ 1` (Theorem 16.2.2).

The weights `F` need not sum to `1`: for nonnegative weights the conditions read
`∑ₖ F(k) xₖᵢ / b*ᵗxₖ ≤ ∑ₖ F(k)`.

## Main statements

* `sum_ratio_eq`: `∑ₖ F(k) bᵗxₖ / b*ᵗxₖ = ∑ᵢ bᵢ ∑ₖ F(k) xₖᵢ / b*ᵗxₖ`.
* `isLogOptimal_iff_kuhnTucker`: **Theorem 16.2.1 (Kuhn–Tucker conditions)**, (16.12).
* `IsLogOptimal.sum_ratio_le`: **(16.22)** `E(S/S*) ≤ 1`.
* `isLogOptimal_iff_expected_ratio_le`: **Theorem 16.2.2**, (16.19).
* `IsLogOptimal.expected_proportion`: **(16.24)** the expected proportion of wealth in each stock
  is unchanged by a day of trading.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 16.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {m : ℕ} {ι : Type*} [Fintype ι] {F : ι → ℝ} {x : ι → Fin m → ℝ}

/-- `∑ₖ F(k) bᵗxₖ / b*ᵗxₖ = ∑ᵢ bᵢ ∑ₖ F(k) xₖᵢ / b*ᵗxₖ`: the expected wealth ratio is linear in
`b`. -/
lemma sum_ratio_eq (F : ι → ℝ) (x : ι → Fin m → ℝ) (b b' : Fin m → ℝ) :
    ∑ k, F k * (wealthRel b' (x k) / wealthRel b (x k)) =
      ∑ i, b' i * ∑ k, F k * (x k i / wealthRel b (x k)) := by
  simp only [wealthRel, sum_div, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
  ring

/-- `∑ₖ F(k) b*ᵗxₖ / b*ᵗxₖ = ∑ₖ F(k)`. -/
lemma sum_ratio_self (hx : IsPosMarket x) {b : Fin m → ℝ} (hb : IsPMF b) :
    ∑ i, b i * ∑ k, F k * (x k i / wealthRel b (x k)) = ∑ k, F k := by
  rw [← sum_ratio_eq]
  exact sum_congr rfl fun k _ => by rw [div_self (wealthRel_pos hb (hx k)).ne', mul_one]

/-- `W(b) - W(b*) = ∑ₖ F(k) log (bᵗxₖ / b*ᵗxₖ)`. -/
lemma growthRate_sub_eq (hx : IsPosMarket x) {b b' : Fin m → ℝ} (hb : IsPMF b) (hb' : IsPMF b') :
    growthRate b' F x - growthRate b F x =
      ∑ k, F k * log (wealthRel b' (x k) / wealthRel b (x k)) := by
  simp only [growthRate, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [log_div (wealthRel_pos hb' (hx k)).ne' (wealthRel_pos hb (hx k)).ne']
  ring

/-- `W(b) - W(b*) ≤ E(bᵗX / b*ᵗX) - 1`, from `log t ≤ t - 1`. -/
lemma growthRate_sub_le (hF : ∀ k, 0 ≤ F k) (hx : IsPosMarket x) {b b' : Fin m → ℝ}
    (hb : IsPMF b) (hb' : IsPMF b') :
    growthRate b' F x - growthRate b F x ≤
      ∑ k, F k * (wealthRel b' (x k) / wealthRel b (x k)) - ∑ k, F k := by
  rw [growthRate_sub_eq hx hb hb', ← sum_sub_distrib]
  refine sum_le_sum fun k _ => ?_
  have h := log_le_sub_one_of_pos (div_pos (wealthRel_pos hb' (hx k)) (wealthRel_pos hb (hx k)))
  nlinarith [mul_le_mul_of_nonneg_left h (hF k)]

/-- **(16.13)–(16.17)** If `b*` is log-optimal, `∑ₖ F(k) xₖⱼ / b*ᵗxₖ ≤ ∑ₖ F(k)` for every stock
`j`: the derivative of the growth rate towards stock `j` is nonpositive. -/
theorem IsLogOptimal.sum_le (hF : ∀ k, 0 ≤ F k) (hx : IsPosMarket x) {b : Fin m → ℝ}
    (h : IsLogOptimal F x b) (j : Fin m) :
    ∑ k, F k * (x k j / wealthRel b (x k)) ≤ ∑ k, F k := by
  set S : ι → ℝ := fun k => wealthRel b (x k)
  have hS : ∀ k, 0 < S k := fun k => wealthRel_pos h.1 (hx k)
  set Y : ι → ℝ := fun k => x k j / S k
  have hY : ∀ k, 0 < Y k := fun k => div_pos (hx k j) (hS k)
  set g : ℝ → ℝ := fun t => ∑ k, F k * ((Y k - 1) / (1 + t * (Y k - 1)))
  -- For `0 < t < 1`, `g t ≤ 0`.
  have hg : ∀ t, 0 < t → t < 1 → g t ≤ 0 := by
    intro t ht0 ht1
    set b' : Fin m → ℝ := (1 - t) • b + t • Pi.single j 1
    have hb' : IsPMF b' := convex_portfolios h.1 (isPMF_single j) (by linarith) ht0.le
      (by ring)
    have hz : ∀ k, 0 < 1 + t * (Y k - 1) := fun k => by nlinarith [hY k]
    have hwr : ∀ k, wealthRel b' (x k) / wealthRel b (x k) = 1 + t * (Y k - 1) := fun k => by
      have hk := (wealthRel_pos h.1 (hx k)).ne'
      simp only [b', wealthRel_add_smul, wealthRel_single, Y, S]
      field_simp
      ring
    have h1 := growthRate_sub_eq hx h.1 hb' (F := F)
    have h2 := h.2 b' hb'
    simp only [hwr] at h1
    have h3 : ∑ k, F k * (t * ((Y k - 1) / (1 + t * (Y k - 1)))) ≤ 0 := by
      refine le_trans (sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hF k)) (by linarith)
      have := one_sub_inv_le_log_of_pos (hz k)
      have e : t * ((Y k - 1) / (1 + t * (Y k - 1))) = 1 - (1 + t * (Y k - 1))⁻¹ := by
        field_simp [(hz k).ne']
        ring
      rw [e]
      exact this
    have e : ∑ k, F k * (t * ((Y k - 1) / (1 + t * (Y k - 1)))) = t * g t := by
      simp only [g, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    rw [e] at h3
    nlinarith
  -- Let `t → 0⁺`.
  have hcont : ContinuousAt g 0 := by
    unfold ContinuousAt
    refine tendsto_finsetSum _ fun k _ => (continuousAt_const.mul ?_).tendsto
    exact continuousAt_const.div (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
      (by simp)
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    exact hg t ht.1 ht.2
  have h0 : g 0 ≤ 0 := le_of_tendsto hlim hev
  have e0 : g 0 = ∑ k, F k * Y k - ∑ k, F k := by
    simp only [g, zero_mul, add_zero, div_one]
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  linarith

/-- **Theorem 16.2.1 (Kuhn–Tucker conditions), (16.12).** A portfolio `b*` is log-optimal iff
`E(Xᵢ / b*ᵗX) ≤ 1` for every stock `i`, with equality if `b*ᵢ > 0`. With nonnegative weights `F`,
the right-hand side `1` is `∑ₖ F(k)`. -/
theorem isLogOptimal_iff_kuhnTucker (hF : ∀ k, 0 ≤ F k) (hx : IsPosMarket x) {b : Fin m → ℝ} :
    IsLogOptimal F x b ↔ IsPMF b ∧ ∀ i, ∑ k, F k * (x k i / wealthRel b (x k)) ≤ ∑ k, F k ∧
      (0 < b i → ∑ k, F k * (x k i / wealthRel b (x k)) = ∑ k, F k) := by
  constructor
  · intro h
    have hle := h.sum_le hF hx
    refine ⟨h.1, fun i => ⟨hle i, fun hi => ?_⟩⟩
    -- `∑ᵢ bᵢ (∑ₖ F(k) - Aᵢ) = 0` with nonnegative terms.
    have hzero : ∑ i, b i * (∑ k, F k - ∑ k, F k * (x k i / wealthRel b (x k))) = 0 := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, h.1.sum_eq_one, one_mul,
        sum_ratio_self hx h.1, sub_self]
    have := (sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (h.1.nonneg i) (sub_nonneg.2 (hle i))).1 hzero i (mem_univ i)
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hi.ne'
    · linarith
  · rintro ⟨hb, hkt⟩
    refine ⟨hb, fun b' hb' => ?_⟩
    have h1 := growthRate_sub_le hF hx hb hb'
    rw [sum_ratio_eq] at h1
    have h2 : ∑ i, b' i * ∑ k, F k * (x k i / wealthRel b (x k)) ≤ ∑ i, b' i * ∑ k, F k :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hkt i).1 (hb'.nonneg i)
    rw [← sum_mul, hb'.sum_eq_one, one_mul] at h2
    linarith

/-- **(16.20)–(16.22)** For a log-optimal portfolio `b*` and any portfolio `b`, `E(S/S*) ≤ 1`:
`∑ₖ F(k) bᵗxₖ / b*ᵗxₖ ≤ ∑ₖ F(k)`. -/
theorem IsLogOptimal.sum_ratio_le (hF : ∀ k, 0 ≤ F k) (hx : IsPosMarket x) {b : Fin m → ℝ}
    (h : IsLogOptimal F x b) {b' : Fin m → ℝ} (hb' : IsPMF b') :
    ∑ k, F k * (wealthRel b' (x k) / wealthRel b (x k)) ≤ ∑ k, F k := by
  rw [sum_ratio_eq]
  calc ∑ i, b' i * ∑ k, F k * (x k i / wealthRel b (x k)) ≤ ∑ i, b' i * ∑ k, F k :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h.sum_le hF hx i) (hb'.nonneg i)
    _ = ∑ k, F k := by rw [← sum_mul, hb'.sum_eq_one, one_mul]

/-- **Theorem 16.2.2, (16.19)–(16.23).** For a pmf `F`, `E ln (S/S*) ≤ 0` for all portfolios iff
`E (S/S*) ≤ 1` for all portfolios; both say that `b*` is log-optimal. -/
theorem isLogOptimal_iff_expected_ratio_le (hF : IsPMF F) (hx : IsPosMarket x) {b : Fin m → ℝ}
    (hb : IsPMF b) :
    (∀ b', IsPMF b' → ∑ k, F k * log (wealthRel b' (x k) / wealthRel b (x k)) ≤ 0) ↔
      ∀ b', IsPMF b' → ∑ k, F k * (wealthRel b' (x k) / wealthRel b (x k)) ≤ 1 := by
  constructor
  · intro h b' hb'
    have hopt : IsLogOptimal F x b := ⟨hb, fun b'' hb'' => by
      have := h b'' hb''
      rw [← growthRate_sub_eq hx hb hb''] at this
      linarith⟩
    have := hopt.sum_ratio_le hF.nonneg hx hb'
    rwa [hF.sum_eq_one] at this
  · intro h b' hb'
    have h1 := growthRate_sub_le hF.nonneg hx hb hb'
    rw [growthRate_sub_eq hx hb hb', hF.sum_eq_one] at h1
    linarith [h b' hb']

/-- **(16.24)** Under the log-optimal portfolio, the expected proportion `E(b*ᵢXᵢ / b*ᵗX)` of the
wealth in stock `i` at the end of the day is the proportion `b*ᵢ` invested in it. -/
theorem IsLogOptimal.expected_proportion (hF : IsPMF F) (hx : IsPosMarket x) {b : Fin m → ℝ}
    (h : IsLogOptimal F x b) (i : Fin m) :
    ∑ k, F k * (b i * x k i / wealthRel b (x k)) = b i := by
  have hkt := ((isLogOptimal_iff_kuhnTucker hF.nonneg hx).1 h).2 i
  have e : ∑ k, F k * (b i * x k i / wealthRel b (x k)) =
      b i * ∑ k, F k * (x k i / wealthRel b (x k)) := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [e]
  rcases (h.1.nonneg i).lt_or_eq with hi | hi
  · rw [hkt.2 hi, hF.sum_eq_one, mul_one]
  · rw [← hi, zero_mul]

end InfoTheory
