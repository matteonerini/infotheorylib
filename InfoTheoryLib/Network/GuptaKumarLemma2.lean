/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.GuptaKumar

/-!
# The Gupta–Kumar random network: the upper bound

Lemma 2 of Lecture 20 of El Gamal and Kim, on the sum `D(N)` of the logarithms of the diagonal
entries of the gain matrix, and the upper bound on the capacity that follows from it.

A node is at a distance `U` from the cut and `W = 2 |U|` is uniform on `[0, N^{1/2}]`. In this file
the law of `W` is `gkUnif`.

## Main definitions

* `gkLog c ν u`: the function `log (1 + c u ^ (-ν))`.
* `gkUnif k`: the uniform law on `(0, k]`.
* `gkD ν P N w`: the sum `D(N)`.

## Main statements

* `pi_sum_ge_le`: Chebyshev's inequality for a sum of i.i.d. random variables.
* `integral_gkLog_le`, `integral_gkLog_ge`, `integral_gkLog_sq_le`: the bounds on `k E(X)` and
  `k E(X²)` of pages 20-39 to 20-41.
* `gkD_whp`: **Lemma 2**.
* `gk_upper_whp`, `gk_capacity_upper_whp`: **the upper bound on the capacity**, with probability
  tending to one, for a positive semidefinite gain matrix.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 20
-/

open Real Finset MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped Interval NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Chebyshev's inequality for a sum -/

section Chebyshev

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Chebyshev's inequality for a sum of i.i.d. random variables.** The probability that the sum
of `n` copies of `f` is at least twice its mean is at most `E(f²) / (n E(f)²)`. -/
theorem pi_sum_ge_le {f : Ω → ℝ} (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n)
    (hm : 0 < ∫ x, f x ∂μ) :
    (Measure.pi fun _ : Fin n => μ) {ω | 2 * ((n : ℝ) * ∫ x, f x ∂μ) ≤ ∑ j, f (ω j)} ≤
      ENNReal.ofReal ((∫ x, f x ^ 2 ∂μ) / ((n : ℝ) * (∫ x, f x ∂μ) ^ 2)) := by
  set Q := Measure.pi fun _ : Fin n => μ with hQ
  set m := ∫ x, f x ∂μ with hmd
  set s := ∫ x, f x ^ 2 ∂μ with hsd
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let X : Fin n → (Fin n → Ω) → ℝ := fun j ω => f (ω j)
  have hX : ∀ j, MemLp (X j) 2 Q := fun j =>
    hf.comp_measurePreserving (measurePreserving_eval _ j)
  have hD : MemLp (∑ j, X j) 2 Q := memLp_finsetSum' _ fun j _ => hX j
  have hint : ∀ j, ∫ ω, X j ω ∂Q = m := fun j =>
    integral_comp_eval (μ := fun _ => μ) hf.aestronglyMeasurable
  have hE : ∫ ω, (∑ j, X j) ω ∂Q = n * m := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun j _ => (hX j).integrable (by norm_num)]
    simp [hint]
  have hind : iIndepFun X Q := iIndepFun_pi (μ := fun _ => μ) (X := fun _ => f)
    fun _ => hf.aestronglyMeasurable.aemeasurable
  have hvar : ProbabilityTheory.variance (∑ j, X j) Q = ∑ j, ProbabilityTheory.variance (X j) Q :=
    IndepFun.variance_sum (s := univ) (X := X) (fun j _ => hX j) fun i _ j _ hij =>
      hind.indepFun hij
  have hvj : ∀ j, ProbabilityTheory.variance (X j) Q ≤ s := fun j => by
    refine (variance_le_expectation_sq (hX j).aestronglyMeasurable).trans (le_of_eq ?_)
    exact integral_comp_eval (μ := fun _ : Fin n => μ) (i := j) (f := fun x => f x ^ 2)
      (hf.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  have hvs : ProbabilityTheory.variance (∑ j, X j) Q ≤ n * s := by
    rw [hvar]
    calc _ ≤ ∑ _j : Fin n, s := sum_le_sum fun j _ => hvj j
      _ = n * s := by simp
  have hc : 0 < (n : ℝ) * m := by positivity
  have hsub : {ω : Fin n → Ω | 2 * ((n : ℝ) * m) ≤ ∑ j, f (ω j)} ⊆
      {ω | (n : ℝ) * m ≤ |(∑ j, X j) ω - ∫ ω, (∑ j, X j) ω ∂Q|} := by
    intro ω hω
    have hω' : 2 * ((n : ℝ) * m) ≤ (∑ j, X j) ω := by
      rw [Finset.sum_apply]
      exact hω
    change (n : ℝ) * m ≤ |(∑ j, X j) ω - ∫ ω, (∑ j, X j) ω ∂Q|
    rw [hE, abs_of_nonneg (by linarith)]
    linarith
  have hch := meas_ge_le_variance_div_sq hD hc
  refine (measure_mono ?_).trans (hch.trans (ENNReal.ofReal_le_ofReal ?_))
  · exact hsub
  · have hle : ProbabilityTheory.variance (∑ j, X j) Q / ((n : ℝ) * m) ^ 2 ≤ (n * s) / ((n : ℝ) * m)
    ^ 2 :=
      div_le_div_of_nonneg_right hvs (by positivity)
    refine hle.trans (le_of_eq ?_)
    field_simp

end Chebyshev

/-! ### The function and its integrals -/

section Calculus

/-- The function `log (1 + c u ^ (-ν))`. -/
def gkLog (c ν u : ℝ) : ℝ := log (1 + c * u ^ (-ν))

lemma measurable_gkLog (c ν : ℝ) : Measurable (gkLog c ν) := by
  unfold gkLog
  fun_prop

variable {c ν u : ℝ}

lemma gkLog_nonneg (hc : 0 ≤ c) (hu : 0 ≤ u) : 0 ≤ gkLog c ν u :=
  log_nonneg (by have := rpow_nonneg hu (-ν); nlinarith [mul_nonneg hc this])

/-- The first bound of page 20-40, for all `u > 0`. -/
lemma gkLog_le_left (hc : 0 ≤ c) (hν : 0 < ν) (hu : 0 < u) :
    gkLog c ν u ≤ log (1 + c) + 4 * ν * u ^ (-(1 / 4) : ℝ) := by
  have hpow : 0 < u ^ (-(1 / 4) : ℝ) := rpow_pos_of_pos hu _
  rcases le_total u 1 with h | h
  · have h₁ : 1 ≤ u ^ (-ν) := one_le_rpow_of_pos_of_le_one_of_nonpos hu h (by linarith)
    have h₂ : 1 + c * u ^ (-ν) ≤ (1 + c) * u ^ (-ν) := by nlinarith
    have h₃ : log ((1 + c) * u ^ (-ν)) = log (1 + c) + -ν * log u := by
      rw [log_mul (by positivity) (by positivity), log_rpow hu]
    have h₄ : log (1 / u) ≤ (1 / u) ^ (1 / 4 : ℝ) / (1 / 4) :=
      log_le_rpow_div (by positivity) (by norm_num)
    have h₅ : (1 / u) ^ (1 / 4 : ℝ) = u ^ (-(1 / 4) : ℝ) := by
      rw [one_div, inv_rpow hu.le, rpow_neg hu.le]
    have h₆ : log (1 / u) = -log u := by rw [one_div, log_inv]
    rw [h₅, h₆] at h₄
    have h₇ : gkLog c ν u ≤ log (1 + c) + -ν * log u := by
      rw [← h₃]
      exact log_le_log (by have := rpow_pos_of_pos hu (-ν); positivity) h₂
    have h₈ : ν * -log u ≤ ν * (u ^ (-(1 / 4) : ℝ) / (1 / 4)) :=
      mul_le_mul_of_nonneg_left h₄ hν.le
    linarith
  · have h₁ : u ^ (-ν) ≤ 1 := rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have h₀ : 0 < u ^ (-ν) := rpow_pos_of_pos hu _
    have h₂ : gkLog c ν u ≤ log (1 + c) :=
      log_le_log (by positivity) (by nlinarith)
    have h₃ : 0 ≤ 4 * ν * u ^ (-(1 / 4) : ℝ) := by positivity
    linarith

/-- The point where `c u ^ (-ν) = 1`: `u₀ = c ^ (1 / ν)`. -/
def gkU (c ν : ℝ) : ℝ := c ^ (1 / ν)

lemma gkU_pow (hc : 0 < c) (hν : 0 < ν) : gkU c ν ^ ν = c := by
  rw [gkU, ← rpow_mul hc.le, one_div, inv_mul_cancel₀ hν.ne', rpow_one]

/-- Beyond `u₀` the argument is at most one, so that the function and its square are bounded by the
power. -/
lemma gkLog_le_right (hc : 0 < c) (hν : 0 < ν) (hu : gkU c ν ≤ u) :
    gkLog c ν u ≤ c * u ^ (-ν) ∧ gkLog c ν u ^ 2 ≤ c * u ^ (-ν) := by
  have hu0 : 0 < gkU c ν := rpow_pos_of_pos hc _
  have hu' : 0 < u := by linarith
  have hpos : 0 < c * u ^ (-ν) := mul_pos hc (rpow_pos_of_pos hu' _)
  have hone : c * u ^ (-ν) ≤ 1 := by
    rw [rpow_neg hu'.le, ← div_eq_mul_inv, div_le_one (rpow_pos_of_pos hu' _)]
    calc c = gkU c ν ^ ν := (gkU_pow hc hν).symm
      _ ≤ u ^ ν := rpow_le_rpow hu0.le hu hν.le
  have h₁ : gkLog c ν u ≤ c * u ^ (-ν) := by
    have := log_le_sub_one_of_pos (show 0 < 1 + c * u ^ (-ν) by linarith)
    unfold gkLog
    linarith
  have h₀ : 0 ≤ gkLog c ν u := gkLog_nonneg hc.le hu'.le
  exact ⟨h₁, by nlinarith⟩

/-- **Page 20-40 of [elgamal2010]**, corrected: below `u₀`, the function is at least `log 2`. -/
lemma gkLog_ge_log_two (hc : 0 < c) (hν : 0 < ν) (hu : 0 < u) (hu' : u ≤ gkU c ν) :
    log 2 ≤ gkLog c ν u := by
  have hone : 1 ≤ c * u ^ (-ν) := by
    rw [rpow_neg hu.le, ← div_eq_mul_inv, one_le_div (rpow_pos_of_pos hu _)]
    calc u ^ ν ≤ gkU c ν ^ ν := rpow_le_rpow hu.le hu' hν.le
      _ = c := gkU_pow hc hν
  exact log_le_log (by norm_num) (by linarith)

variable {k : ℝ}

/-- The second bound of page 20-41: the square of the function, below `u₀`. -/
lemma gkLog_sq_le_left (hc : 0 ≤ c) (hν : 0 < ν) (hu : 0 < u) :
    gkLog c ν u ^ 2 ≤ 2 * log (1 + c) ^ 2 + 32 * ν ^ 2 * u ^ (-(1 / 2) : ℝ) := by
  have h₁ := gkLog_le_left hc hν hu
  have h₀ := gkLog_nonneg (ν := ν) hc hu.le
  have h₂ : (u ^ (-(1 / 4) : ℝ)) ^ 2 = u ^ (-(1 / 2) : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hu.le]
    norm_num
  set A := log (1 + c)
  set B := u ^ (-(1 / 4) : ℝ)
  rw [← h₂]
  have h₃ : gkLog c ν u ^ 2 ≤ (A + 4 * ν * B) ^ 2 := pow_le_pow_left₀ h₀ h₁ 2
  nlinarith [sq_nonneg (A - 4 * ν * B)]

lemma intervalIntegrable_rpow_right {r a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ r) volume a b := by
  refine intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
  rw [uIcc_of_le hab]
  exact fun h => absurd h.1 (not_le.2 ha)

/-- A nonnegative measurable function below an integrable function is integrable. -/
lemma intervalIntegrable_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hf : Measurable f)
    (h : ∀ x ∈ Ioc a b, 0 ≤ f x ∧ f x ≤ g x) : IntervalIntegrable f volume a b := by
  refine hg.mono_fun hf.aestronglyMeasurable ?_
  rw [uIoc_of_le hab]
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
  obtain ⟨h₁, h₂⟩ := h x hx
  simp only [Real.norm_of_nonneg h₁, Real.norm_of_nonneg (h₁.trans h₂)]
  exact h₂

lemma intervalIntegrable_tail (hk : gkU c ν ≤ k) (h1 : 1 ≤ gkU c ν) :
    IntervalIntegrable (fun u => c * u ^ (-ν)) volume (gkU c ν) k :=
  (intervalIntegrable_rpow_right (by linarith) hk).const_mul c

lemma intervalIntegrable_head₁ (b : ℝ) :
    IntervalIntegrable (fun u : ℝ => log (1 + c) + 4 * ν * u ^ (-(1 / 4) : ℝ)) volume 0 b :=
  intervalIntegrable_const.add
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)

lemma intervalIntegrable_head₂ (b : ℝ) :
    IntervalIntegrable (fun u : ℝ => 2 * log (1 + c) ^ 2 + 32 * ν ^ 2 * u ^ (-(1 / 2) : ℝ)) volume 0
      b :=
  intervalIntegrable_const.add
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)

variable (hc : 0 < c) (hν : 1 < ν) (h1 : 1 ≤ gkU c ν) (hk : gkU c ν ≤ k)
include hc hν h1 hk

/-- The tail of the integrals of pages 20-39 to 20-41. -/
lemma integral_tail_le :
    ∫ u in gkU c ν..k, c * u ^ (-ν) ≤ gkU c ν / (ν - 1) := by
  have hν0 : 0 < ν := by linarith
  set u₀ := gkU c ν with hu₀
  have hu0 : 0 < u₀ := by linarith
  have hk0 : 0 < k := by linarith
  have hnot : (0 : ℝ) ∉ [[u₀, k]] := by
    rw [uIcc_of_le hk]
    exact fun h => absurd h.1 (not_le.2 hu0)
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by intro h; linarith, hnot⟩)]
  have e₁ : -ν + 1 = -(ν - 1) := by ring
  have hpos : 0 < ν - 1 := by linarith
  have hu : c * u₀ ^ (-ν + 1) = u₀ := by
    rw [rpow_add hu0, rpow_one, rpow_neg hu0.le, gkU_pow hc hν0]
    field_simp
  have hkp : 0 ≤ c * k ^ (-ν + 1) := by positivity
  have e₂ : c * ((k ^ (-ν + 1) - u₀ ^ (-ν + 1)) / (-ν + 1)) =
      (c * u₀ ^ (-ν + 1) - c * k ^ (-ν + 1)) / (ν - 1) := by
    rw [e₁]
    have : -(ν - 1) ≠ 0 := by linarith
    field_simp
    ring
  rw [e₂, hu]
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

lemma intervalIntegrable_gkLog_tail :
    IntervalIntegrable (gkLog c ν) volume (gkU c ν) k := by
  have hν0 : 0 < ν := by linarith
  refine intervalIntegrable_of_le hk (intervalIntegrable_tail hk h1) (measurable_gkLog c ν)
    fun x hx => ⟨gkLog_nonneg hc.le (by linarith [hx.1]), (gkLog_le_right hc hν0 hx.1.le).1⟩

lemma intervalIntegrable_gkLog_sq_tail :
    IntervalIntegrable (fun u => gkLog c ν u ^ 2) volume (gkU c ν) k := by
  have hν0 : 0 < ν := by linarith
  refine intervalIntegrable_of_le hk (intervalIntegrable_tail hk h1)
    ((measurable_gkLog c ν).pow_const 2)
    fun x hx => ⟨sq_nonneg _, (gkLog_le_right hc hν0 hx.1.le).2⟩

omit hk in
lemma intervalIntegrable_gkLog_head :
    IntervalIntegrable (gkLog c ν) volume 0 (gkU c ν) := by
  have hν0 : 0 < ν := by linarith
  refine intervalIntegrable_of_le (by linarith) (intervalIntegrable_head₁ _)
    (measurable_gkLog c ν)
    fun x hx => ⟨gkLog_nonneg hc.le hx.1.le, gkLog_le_left hc.le hν0 hx.1⟩

omit hk in
lemma intervalIntegrable_gkLog_sq_head :
    IntervalIntegrable (fun u => gkLog c ν u ^ 2) volume 0 (gkU c ν) := by
  have hν0 : 0 < ν := by linarith
  refine intervalIntegrable_of_le (by linarith) (intervalIntegrable_head₂ _)
    ((measurable_gkLog c ν).pow_const 2)
    fun x hx => ⟨sq_nonneg _, gkLog_sq_le_left hc.le hν0 hx.1⟩

/-- **Pages 20-39 and 20-40 of [elgamal2010]: the upper bound on `k E(X)`.** -/
theorem integral_gkLog_le :
    ∫ u in 0..k, gkLog c ν u ≤ gkU c ν * (log (1 + c) + (16 / 3 * ν + 1 / (ν - 1))) := by
  have hν0 : 0 < ν := by linarith
  set u₀ := gkU c ν with hu₀
  have hu0 : 0 ≤ u₀ := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_gkLog_head hc hν h1) (intervalIntegrable_gkLog_tail hc hν h1 hk)]
  have h₁ : ∫ u in 0..u₀, gkLog c ν u ≤ ∫ u in 0..u₀, (log (1 + c) + 4 * ν * u ^ (-(1 / 4) : ℝ)) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hu0 (intervalIntegrable_gkLog_head hc hν h1)
      (intervalIntegrable_head₁ _) fun x hx => gkLog_le_left hc.le hν0 hx.1
  have h₂ : ∫ u in u₀..k, gkLog c ν u ≤ ∫ u in u₀..k, c * u ^ (-ν) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hk (intervalIntegrable_gkLog_tail hc hν h1 hk)
      (intervalIntegrable_tail hk h1) fun x hx => (gkLog_le_right hc hν0 hx.1.le).1
  have h₃ : ∫ u in 0..u₀, (log (1 + c) + 4 * ν * u ^ (-(1 / 4) : ℝ)) =
      u₀ * log (1 + c) + 4 * ν * (u₀ ^ (3 / 4 : ℝ) / (3 / 4)) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num))]
    norm_num [smul_eq_mul]
  have h₄ : u₀ ^ (3 / 4 : ℝ) ≤ u₀ := by
    calc u₀ ^ (3 / 4 : ℝ) ≤ u₀ ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = u₀ := rpow_one u₀
  have h₅ := integral_tail_le hc hν h1 hk
  have hν1 : 0 < ν - 1 := by linarith
  have e : u₀ * (log (1 + c) + (16 / 3 * ν + 1 / (ν - 1))) =
      u₀ * log (1 + c) + 4 * ν * (u₀ / (3 / 4)) + u₀ / (ν - 1) := by
    field_simp
    ring
  rw [e]
  have h₆ : 4 * ν * (u₀ ^ (3 / 4 : ℝ) / (3 / 4)) ≤ 4 * ν * (u₀ / (3 / 4)) := by
    gcongr
  linarith

/-- **Page 20-40 of [elgamal2010]: the lower bound on `k E(X)`.** -/
theorem integral_gkLog_ge : gkU c ν * log 2 ≤ ∫ u in 0..k, gkLog c ν u := by
  have hν0 : 0 < ν := by linarith
  set u₀ := gkU c ν with hu₀
  have hu0 : 0 ≤ u₀ := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_gkLog_head hc hν h1) (intervalIntegrable_gkLog_tail hc hν h1 hk)]
  have h₁ : ∫ _u in 0..u₀, log 2 ≤ ∫ u in 0..u₀, gkLog c ν u :=
    intervalIntegral.integral_mono_on_of_le_Ioo hu0 intervalIntegrable_const
      (intervalIntegrable_gkLog_head hc hν h1)
      fun x hx => gkLog_ge_log_two hc hν0 hx.1 hx.2.le
  have h₂ : 0 ≤ ∫ u in u₀..k, gkLog c ν u :=
    intervalIntegral.integral_nonneg hk fun x hx => gkLog_nonneg hc.le (by linarith [hx.1])
  rw [intervalIntegral.integral_const] at h₁
  simp only [sub_zero, smul_eq_mul] at h₁
  linarith

/-- **Page 20-41 of [elgamal2010]: the upper bound on `k E(X²)`.** -/
theorem integral_gkLog_sq_le :
    ∫ u in 0..k, gkLog c ν u ^ 2 ≤ gkU c ν *
      (2 * log (1 + c) ^ 2 + (64 * ν ^ 2 + 1 / (ν - 1))) := by
  have hν0 : 0 < ν := by linarith
  set u₀ := gkU c ν with hu₀
  have hu0 : 0 ≤ u₀ := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_gkLog_sq_head hc hν h1) (intervalIntegrable_gkLog_sq_tail hc hν h1 hk)]
  have h₁ : ∫ u in 0..u₀, gkLog c ν u ^ 2 ≤
      ∫ u in 0..u₀, (2 * log (1 + c) ^ 2 + 32 * ν ^ 2 * u ^ (-(1 / 2) : ℝ)) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hu0 (intervalIntegrable_gkLog_sq_head hc hν h1)
      (intervalIntegrable_head₂ _) fun x hx => gkLog_sq_le_left hc.le hν0 hx.1
  have h₂ : ∫ u in u₀..k, gkLog c ν u ^ 2 ≤ ∫ u in u₀..k, c * u ^ (-ν) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hk (intervalIntegrable_gkLog_sq_tail hc hν h1 hk)
      (intervalIntegrable_tail hk h1) fun x hx => (gkLog_le_right hc hν0 hx.1.le).2
  have h₃ : ∫ u in 0..u₀, (2 * log (1 + c) ^ 2 + 32 * ν ^ 2 * u ^ (-(1 / 2) : ℝ)) =
      u₀ * (2 * log (1 + c) ^ 2) + 32 * ν ^ 2 * (u₀ ^ (1 / 2 : ℝ) / (1 / 2)) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num))]
    norm_num [smul_eq_mul]
  have h₄ : u₀ ^ (1 / 2 : ℝ) ≤ u₀ := by
    calc u₀ ^ (1 / 2 : ℝ) ≤ u₀ ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = u₀ := rpow_one u₀
  have h₅ := integral_tail_le hc hν h1 hk
  have hν1 : 0 < ν - 1 := by linarith
  have e : u₀ * (2 * log (1 + c) ^ 2 + (64 * ν ^ 2 + 1 / (ν - 1))) =
      u₀ * (2 * log (1 + c) ^ 2) + 32 * ν ^ 2 * (u₀ / (1 / 2)) + u₀ / (ν - 1) := by
    field_simp
    ring
  rw [e]
  have h₆ : 32 * ν ^ 2 * (u₀ ^ (1 / 2 : ℝ) / (1 / 2)) ≤ 32 * ν ^ 2 * (u₀ / (1 / 2)) := by
    gcongr
  linarith

end Calculus

/-! ### The uniform law -/

section Uniform

/-- The uniform law on `(0, k]`. -/
def gkUnif (k : ℝ) : Measure ℝ := ENNReal.ofReal k⁻¹ • volume.restrict (Ioc 0 k)

lemma isProbabilityMeasure_gkUnif {k : ℝ} (hk : 0 < k) : IsProbabilityMeasure (gkUnif k) := by
  refine ⟨?_⟩
  simp only [gkUnif, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one]

lemma integral_gkUnif {k : ℝ} (hk : 0 < k) (g : ℝ → ℝ) :
    ∫ x, g x ∂gkUnif k = k⁻¹ * ∫ u in 0..k, g u := by
  rw [gkUnif, integral_smul_measure, intervalIntegral.integral_of_le hk.le,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

lemma integrable_gkUnif {k : ℝ} (hk : 0 < k) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 k) : Integrable g (gkUnif k) :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le hk.le).1 hg).smul_measure ENNReal.ofReal_ne_top

end Uniform

/-! ### Lemma 2 -/

section Lemma2

variable {c ν k : ℝ}

/-- The sum `D(N)`, for `2N` nodes at (twice the) distances `w j` from the cut. -/
def gkD (ν P : ℝ) (N : ℕ) (w : Fin (2 * N) → ℝ) : ℝ :=
  ∑ j, gkLog √(2 * N * P) (ν / 2) (w j)

/-- The law of the distances: independent and uniform on `(0, N^{1/2}]`. -/
def gkLaw (N : ℕ) : Measure (Fin (2 * N) → ℝ) := Measure.pi fun _ => gkUnif √(N : ℝ)

/-- The bound of page 20-42 for a fixed `k`. -/
theorem pi_gkLog_ge_le (hc : 0 < c) (hν : 1 < ν) (h1 : 1 ≤ gkU c ν) (hk : gkU c ν ≤ k) {n : ℕ}
    (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => gkUnif k)
        {w | 2 * ((n : ℝ) * (k⁻¹ * (gkU c ν * (log (1 + c) + (16 / 3 * ν + 1 / (ν - 1)))))) ≤
          ∑ j, gkLog c ν (w j)} ≤
      ENNReal.ofReal (k * (2 * log (1 + c) ^ 2 + (64 * ν ^ 2 + 1 / (ν - 1))) /
        ((n : ℝ) * gkU c ν * log 2 ^ 2)) := by
  have hν0 : 0 < ν := by linarith
  have hu0 : 0 < gkU c ν := by linarith
  have hk0 : 0 < k := by linarith
  have := isProbabilityMeasure_gkUnif hk0
  have hint : IntervalIntegrable (gkLog c ν) volume 0 k :=
    (intervalIntegrable_gkLog_head hc hν h1).trans
      (intervalIntegrable_gkLog_tail hc hν h1 hk)
  have hint₂ : IntervalIntegrable (fun u => gkLog c ν u ^ 2) volume 0 k :=
    (intervalIntegrable_gkLog_sq_head hc hν h1).trans
      (intervalIntegrable_gkLog_sq_tail hc hν h1 hk)
  have hmem : MemLp (gkLog c ν) 2 (gkUnif k) :=
    (memLp_two_iff_integrable_sq (measurable_gkLog c ν).aestronglyMeasurable).2
      (integrable_gkUnif hk0 hint₂)
  have hupper := integral_gkLog_le hc hν h1 hk
  have hlower := integral_gkLog_ge hc hν h1 hk
  have hsq := integral_gkLog_sq_le hc hν h1 hk
  have hm : ∫ x, gkLog c ν x ∂gkUnif k = k⁻¹ * ∫ u in 0..k, gkLog c ν u := integral_gkUnif hk0 _
  have hs : ∫ x, gkLog c ν x ^ 2 ∂gkUnif k = k⁻¹ * ∫ u in 0..k, gkLog c ν u ^ 2 :=
    integral_gkUnif hk0 _
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hk' : 0 < k⁻¹ := inv_pos.2 hk0
  set m := ∫ x, gkLog c ν x ∂gkUnif k with hmd
  set s := ∫ x, gkLog c ν x ^ 2 ∂gkUnif k with hsd
  set u₀ := gkU c ν with hu₀
  set A := log (1 + c) + (16 / 3 * ν + 1 / (ν - 1)) with hA
  set B := 2 * log (1 + c) ^ 2 + (64 * ν ^ 2 + 1 / (ν - 1)) with hB
  have hmlow : k⁻¹ * (u₀ * log 2) ≤ m := by
    rw [hm]
    exact mul_le_mul_of_nonneg_left hlower hk'.le
  have hmup : m ≤ k⁻¹ * (u₀ * A) := by
    rw [hm]
    exact mul_le_mul_of_nonneg_left hupper hk'.le
  have hsup : s ≤ k⁻¹ * (u₀ * B) := by
    rw [hs]
    exact mul_le_mul_of_nonneg_left hsq hk'.le
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hmlow
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (measure_mono ?_).trans ((pi_sum_ge_le (gkUnif k) hmem hn hm0).trans
    (ENNReal.ofReal_le_ofReal ?_))
  · intro w hw
    refine le_trans ?_ (show _ ≤ ∑ j, gkLog c ν (w j) from hw)
    gcongr
  · have hB0 : 0 ≤ B := by
      have : 0 ≤ 1 / (ν - 1) := by
        have : 0 < ν - 1 := by linarith
        positivity
      positivity
    have h₁ : (k⁻¹ * (u₀ * log 2)) ^ 2 ≤ m ^ 2 :=
      pow_le_pow_left₀ (by positivity) hmlow 2
    calc s / ((n : ℝ) * m ^ 2)
        ≤ (k⁻¹ * (u₀ * B)) / ((n : ℝ) * (k⁻¹ * (u₀ * log 2)) ^ 2) := by
          gcongr
      _ = _ := by
          field_simp

private lemma tendsto_gkBound (B : ℝ) :
    Tendsto (fun x : ℝ => (8 * log x ^ 2 + B) / (x * log 2 ^ 2)) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun x : ℝ => log x ^ 2 / x) atTop (𝓝 0) :=
    (isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have h₂ : Tendsto (fun x : ℝ => B / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h₃ := ((h₁.const_mul 8).add h₂).div_const (log 2 ^ 2)
  simp only [mul_zero, add_zero, zero_div] at h₃
  refine h₃.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have : log 2 ≠ 0 := (log_pos (by norm_num)).ne'
  field_simp

/-- **Lemma 2 of Lecture 20 of [elgamal2010].** There is a constant `b` such that
`D(N) < b N^{1/2 + 1/ν} log N` with probability tending to one. -/
theorem gkD_whp {ν P : ℝ} (hν : 2 < ν) (hP : 0 < P) :
    ∃ b > 0, Tendsto (fun N : ℕ =>
      gkLaw N {w | b * ((N : ℝ) ^ (1 / 2 + 1 / ν) * log N) ≤ gkD ν P N w}) atTop (𝓝 0) := by
  have hν0 : 0 < ν := by linarith
  have hν' : 1 < ν / 2 := by linarith
  have hν₁ : 0 < ν / 2 - 1 := by linarith
  set a := √(2 * P) with ha
  have ha0 : 0 < a := sqrt_pos.2 (by positivity)
  set C₁ := 16 / 3 * (ν / 2) + 1 / (ν / 2 - 1) with hC₁
  set C₂ := 64 * (ν / 2) ^ 2 + 1 / (ν / 2 - 1) with hC₂
  have hC₁0 : 0 < C₁ := by positivity
  have hC₂0 : 0 < C₂ := by positivity
  refine ⟨4 * a ^ (2 / ν) * (1 + C₁), by positivity, ?_⟩
  have hsqrt : Tendsto (fun N : ℕ => √(N : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ => ENNReal.ofReal
      ((8 * log √(N : ℝ) ^ 2 + C₂) / (√(N : ℝ) * log 2 ^ 2))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal ((tendsto_gkBound C₂).comp hsqrt)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => zero_le) ?_
  have hpowk : Tendsto (fun k : ℝ => k ^ (ν / 2 - 1)) atTop atTop := tendsto_rpow_atTop hν₁
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_ge_atTop (a + 1), hsqrt.eventually_ge_atTop (1 / a + 1),
    hsqrt.eventually_ge_atTop 1, hsqrt.eventually (hpowk.eventually_ge_atTop a),
    hlogN.eventually_ge_atTop 1, eventually_ge_atTop 1] with N h₁ h₂ h₃ h₄ h₅ h₆
  set k := √(N : ℝ) with hk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast h₆
  have hk0 : 0 < k := by linarith
  have hkk : k * k = N := mul_self_sqrt hN0.le
  set c := a * k with hcd
  have hc0 : 0 < c := by positivity
  have hcc : √(2 * (N : ℝ) * P) = c := by
    rw [hcd, ha, hk, ← sqrt_mul (by positivity)]
    congr 1
    ring
  have hc1 : 1 ≤ c := by
    have : 1 / a < k := by linarith
    rw [div_lt_iff₀ ha0] at this
    rw [hcd]
    linarith
  have hu1 : 1 ≤ gkU c (ν / 2) :=
    one_le_rpow hc1 (by positivity)
  have huk : gkU c (ν / 2) ≤ k := by
    have h₇ : c ≤ k ^ (ν / 2) := by
      have : k ^ (ν / 2) = k ^ (ν / 2 - 1) * k := by
        rw [← rpow_add_one hk0.ne']
        congr 1
        ring
      rw [this, hcd]
      exact mul_le_mul_of_nonneg_right h₄ hk0.le
    calc gkU c (ν / 2) ≤ (k ^ (ν / 2)) ^ (1 / (ν / 2)) :=
          rpow_le_rpow hc0.le h₇ (by positivity)
      _ = k := by
          rw [← rpow_mul hk0.le, mul_one_div, div_self (by positivity), rpow_one]
  have hkey := pi_gkLog_ge_le hc0 hν' hu1 huk (n := 2 * N) (by omega)
  set u₀ := gkU c (ν / 2) with hu₀
  have hu0 : 0 < u₀ := by linarith
  -- the logarithm
  have hLN : log (1 + c) ≤ log N := by
    refine log_le_log (by positivity) ?_
    have : (a + 1) * k ≤ k * k := mul_le_mul_of_nonneg_right h₁ hk0.le
    rw [hcd, ← hkk]
    nlinarith
  have hL0 : 0 ≤ log (1 + c) := log_nonneg (by linarith)
  have hlogk : log N = 2 * log k := by
    rw [← hkk, log_mul hk0.ne' hk0.ne']
    ring
  have hn2 : ((2 * N : ℕ) : ℝ) = 2 * (k * k) := by
    rw [hkk]
    push_cast
    ring
  refine (measure_mono ?_).trans (hkey.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro w hw
    have hw' : 4 * a ^ (2 / ν) * (1 + C₁) * ((N : ℝ) ^ (1 / 2 + 1 / ν) * log N) ≤ gkD ν P N w := hw
    have hD : gkD ν P N w = ∑ j, gkLog c (ν / 2) (w j) := by rw [gkD, hcc]
    rw [hD] at hw'
    refine le_trans ?_ hw'
    have hpow : k * u₀ = a ^ (2 / ν) * (N : ℝ) ^ (1 / 2 + 1 / ν) := by
      have e₁ : (1 : ℝ) / (ν / 2) = 2 / ν := by field_simp
      rw [hu₀, gkU, e₁, hcd, mul_rpow ha0.le hk0.le, rpow_add hN0]
      have e₂ : (N : ℝ) ^ (1 / 2 : ℝ) = k := by rw [hk, sqrt_eq_rpow]
      have e₃ : (N : ℝ) ^ (1 / ν) = k ^ (2 / ν) := by
        rw [hk, sqrt_eq_rpow, ← rpow_mul hN0.le]
        congr 1
        field_simp
      rw [e₂, e₃]
      ring
    have e : 2 * (((2 * N : ℕ) : ℝ) * (k⁻¹ * (u₀ * (log (1 + c) + C₁)))) =
        4 * (k * u₀) * (log (1 + c) + C₁) := by
      rw [hn2]
      field_simp
      ring
    rw [e, hpow]
    have h₇ : log (1 + c) + C₁ ≤ (1 + C₁) * log N := by nlinarith
    have h₈ : 0 ≤ 4 * (a ^ (2 / ν) * (N : ℝ) ^ (1 / 2 + 1 / ν)) := by positivity
    calc 4 * (a ^ (2 / ν) * (N : ℝ) ^ (1 / 2 + 1 / ν)) * (log (1 + c) + C₁)
        ≤ 4 * (a ^ (2 / ν) * (N : ℝ) ^ (1 / 2 + 1 / ν)) * ((1 + C₁) * log N) :=
          mul_le_mul_of_nonneg_left h₇ h₈
      _ = _ := by ring
  · have hsqL : log (1 + c) ^ 2 ≤ (2 * log k) ^ 2 := by
      rw [← hlogk]
      exact pow_le_pow_left₀ hL0 hLN 2
    have hlog2 : 0 < log 2 ^ 2 := pow_pos (log_pos (by norm_num)) 2
    have hX : 2 * log (1 + c) ^ 2 + C₂ ≤ 8 * log k ^ 2 + C₂ := by nlinarith
    have hX0 : 0 ≤ 8 * log k ^ 2 + C₂ := by positivity
    rw [hn2]
    calc k * (2 * log (1 + c) ^ 2 + C₂) / (2 * (k * k) * u₀ * log 2 ^ 2)
        ≤ k * (8 * log k ^ 2 + C₂) / (2 * (k * k) * u₀ * log 2 ^ 2) := by
          gcongr
      _ = (8 * log k ^ 2 + C₂) / (2 * k * u₀ * log 2 ^ 2) := by
          field_simp
      _ ≤ (8 * log k ^ 2 + C₂) / (k * log 2 ^ 2) := by
          refine div_le_div_of_nonneg_left hX0 (by positivity) ?_
          have h₇ : 1 ≤ 2 * u₀ := by linarith
          have h₈ : k * log 2 ^ 2 * 1 ≤ k * log 2 ^ 2 * (2 * u₀) :=
            mul_le_mul_of_nonneg_left h₇ (by positivity)
          linarith

/-- Almost surely, all the distances are positive. -/
lemma ae_pos_gkLaw (N : ℕ) : ∀ᵐ w ∂gkLaw N, ∀ j, 0 < w j := by
  have hfin : IsFiniteMeasure (gkUnif √(N : ℝ)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  rw [ae_all_iff]
  intro j
  have h : ∀ᵐ x ∂gkUnif √(N : ℝ), 0 < x :=
    Measure.ae_smul_measure (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hx.1) _
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin (2 * N) => gkUnif √(N : ℝ)) j).ae h

/-- **The upper bound on the capacity, page 20-34 of [elgamal2010].** Let `G N w` be a positive
semidefinite gain matrix for `2N` nodes, with `G_{jj} = w_j ^ {-ν / 2}`. Then, with probability
tending to one, `½ log |I + G K Gᵀ| < b N^{1/2 + 1/ν} log N` for all covariances with trace at most
`2 N P`. The positive semidefiniteness, shown by Lévêque and Telatar, is a hypothesis here, for
positive distances. -/
theorem gk_upper_whp {ν P : ℝ} (hν : 2 < ν) (hP : 0 < P)
    (G : ∀ N : ℕ, (Fin (2 * N) → ℝ) → Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ)
    (hG : ∀ N w, (∀ j, 0 < w j) → (G N w).PosSemidef)
    (hdiag : ∀ N w, (∀ j, 0 < w j) → ∀ j, G N w j j = w j ^ (-(ν / 2))) :
    ∃ b > 0, Tendsto (fun N : ℕ => gkLaw N {w | ∃ K : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ,
      K.PosSemidef ∧ K.trace ≤ 2 * N * P ∧
        b * ((N : ℝ) ^ (1 / 2 + 1 / ν) * log N) ≤ gvRate (G N w) K}) atTop (𝓝 0) := by
  obtain ⟨b, hb, h⟩ := gkD_whp hν hP
  refine ⟨b, hb, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) fun N => measure_mono_ae ?_⟩
  filter_upwards [ae_pos_gkLaw N] with w hw hmem
  obtain ⟨K, hK, htr, hle⟩ := hmem
  refine hle.trans ((gvRate_le_sum_log (hG N w hw) hK htr (by positivity)).trans (le_of_eq ?_))
  refine sum_congr rfl fun j _ => ?_
  rw [hdiag N w hw, gkLog]

/-- **The upper bound of Theorem 1 of page 20-21 of [elgamal2010]**, for codes without relaying
(`GNCode`). Let `G N w` be a positive semidefinite gain matrix for the `2N` nodes of the augmented
network. Then, with probability tending to one, any rate tuple achievable by a part of the network
has a sum rate, in nats, below `b N^{1/2 + 1/ν} log N`. -/
theorem gk_capacity_upper_whp {ν : ℝ} {P : ℝ≥0} (hν : 2 < ν) (hP : 0 < (P : ℝ))
    (G : ∀ N : ℕ, (Fin (2 * N) → ℝ) → Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ)
    (hG : ∀ N w, (∀ j, 0 < w j) → (G N w).PosSemidef)
    (hdiag : ∀ N w, (∀ j, 0 < w j) → ∀ j, G N w j j = w j ^ (-(ν / 2))) :
    ∃ b > 0, Tendsto (fun N : ℕ => gkLaw N {w | ∃ (n : ℕ) (d s : Fin n → Fin (2 * N))
      (D : Fin n → Finset (Fin n)) (R : Fin n → ℝ), Function.Injective d ∧ Function.Injective s ∧
        (∀ j, (D j).Nonempty) ∧ IsAchievableGN ((G N w).submatrix d s) D P R ∧
        b * ((N : ℝ) ^ (1 / 2 + 1 / ν) * log N) ≤ (∑ j, R j) * log 2}) atTop (𝓝 0) := by
  obtain ⟨b, hb, h⟩ := gk_upper_whp hν hP G hG hdiag
  refine ⟨b, hb, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) fun N => measure_mono ?_⟩
  rintro w ⟨n, d, s, D, R, hd, hs, hD, hach, hle⟩
  refine ⟨(P : ℝ) • 1, PosSemidef.one.smul P.2, ?_, hle.trans (hach.sum_le_gain hd hs hD)⟩
  simp [trace_smul]
  linarith

end Lemma2

end InfoTheory
