/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.Statistics.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.Moments.Variance

/-!
# Probability bounds and limits

The Chebyshev lemma, the Chernoff bound and the weak law of large numbers, as stated in Appendix B
of El Gamal and Kim. The first and the third are for random variables on a general probability
space.

The Chebyshev lemma as printed fails if `E X < 0`, and the Chernoff bound as printed fails for large
`δ`. We prove the first for `E X > 0` and the second for `0 < δ ≤ 2`.

## Main definitions

* `bernCount a`: the number of successes of a binary sequence.

## Main statements

* `chebyshev_lemma`, `chebyshev_lemma_lower`, `chebyshev_lemma_upper`: the Chebyshev lemma.
* `printed_chebyshev_false`: it fails for a negative mean.
* `le_log_one_add_of_nonneg`: `2 x / (2 + x) ≤ log (1 + x)`.
* `chernoff_bound`: the Chernoff bound.
* `printed_chernoff_false`: it fails for large `δ`.
* `weak_law_real`: the weak law of large numbers.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Appendix B
-/

@[expose] public noncomputable section

open Finset Filter Topology Real MeasureTheory ProbabilityTheory

namespace InfoTheory

/-! ### The Chebyshev lemma -/

section Chebyshev

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
  {δ : ℝ}

/-- **The Chebyshev lemma of Appendix B.** For a random variable with positive mean,
`P{|X - E X| ≥ δ E X} ≤ Var X / (δ E X)²`. -/
theorem chebyshev_lemma (hX : MemLp X 2 μ) (hm : 0 < μ[X]) (hδ : 0 < δ) :
    μ.real {ω | δ * μ[X] ≤ |X ω - μ[X]|} ≤ Var[X; μ] / (δ * μ[X]) ^ 2 := by
  have h := meas_ge_le_variance_div_sq hX (mul_pos hδ hm)
  exact ENNReal.toReal_le_of_le_ofReal
    (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (sq_nonneg _)) h

/-- The lower tail in the Chebyshev lemma. -/
theorem chebyshev_lemma_lower (hX : MemLp X 2 μ) (hm : 0 < μ[X]) (hδ : 0 < δ) :
    μ.real {ω | X ω ≤ (1 - δ) * μ[X]} ≤ Var[X; μ] / (δ * μ[X]) ^ 2 := by
  refine le_trans (measureReal_mono fun ω hω => ?_) (chebyshev_lemma hX hm hδ)
  have h : X ω ≤ (1 - δ) * μ[X] := hω
  have h2 : δ * μ[X] ≤ -(X ω - μ[X]) := by linarith
  exact h2.trans (neg_le_abs _)

/-- The upper tail in the Chebyshev lemma. -/
theorem chebyshev_lemma_upper (hX : MemLp X 2 μ) (hm : 0 < μ[X]) (hδ : 0 < δ) :
    μ.real {ω | (1 + δ) * μ[X] ≤ X ω} ≤ Var[X; μ] / (δ * μ[X]) ^ 2 := by
  refine le_trans (measureReal_mono fun ω hω => ?_) (chebyshev_lemma hX hm hδ)
  have h : (1 + δ) * μ[X] ≤ X ω := hω
  have h2 : δ * μ[X] ≤ X ω - μ[X] := by linarith
  exact h2.trans (le_abs_self _)

end Chebyshev

/-- **The Chebyshev lemma of Appendix B as printed fails for a negative mean.** If `X = -1` then
`|X - E X| = 0 ≥ δ E X = -δ` always, while the variance is `0`. -/
theorem printed_chebyshev_false :
    ¬ ((Measure.dirac ()).real {_ω : Unit | (1 : ℝ) * (Measure.dirac ())[fun _ : Unit => (-1 : ℝ)] ≤
        |(-1 : ℝ) - (Measure.dirac ())[fun _ : Unit => (-1 : ℝ)]|} ≤
      Var[fun _ : Unit => (-1 : ℝ); Measure.dirac ()] /
        ((1 : ℝ) * (Measure.dirac ())[fun _ : Unit => (-1 : ℝ)]) ^ 2) := by
  have h1 : (Measure.dirac ())[fun _ : Unit => (-1 : ℝ)] = -1 := by simp
  have h2 : Var[fun _ : Unit => (-1 : ℝ); Measure.dirac ()] = 0 := by simp
  rw [h1, h2]
  have h3 : {ω : Unit | (1 : ℝ) * (-1) ≤ |(-1 : ℝ) - (-1)|} = Set.univ := by
    ext
    simp
  rw [h3]
  simp

/-! ### The Chernoff bound -/

/-- **A lower bound for the logarithm:** `2 x / (2 + x) ≤ log (1 + x)` for `x ≥ 0`, from the first
term of the series `log (1 + 1 / a) = ∑ 2 / (2 k + 1) (1 / (2 a + 1))^(2 k + 1)`. -/
lemma le_log_one_add_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ log (1 + x) := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have h := hasSum_log_one_add_inv (inv_pos.2 hx0)
  rw [inv_inv] at h
  have h1 := le_hasSum h 0 fun k _ => by positivity
  refine le_trans (le_of_eq ?_) h1
  have h2 : 2 * x⁻¹ + 1 = (2 + x) / x := by
    field_simp
  rw [h2]
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one, one_div, inv_div]
  ring

/-- The number of successes of a binary sequence. -/
def bernCount {n : ℕ} (a : Fin n → Bool) : ℕ := (univ.filter fun i => a i = true).card

section Chernoff

variable {p δ : ℝ} {n : ℕ}

/-- The inequality behind the Chernoff bound, for `0 ≤ δ ≤ 2`. -/
lemma chernoff_arith (h0 : 0 ≤ δ) (h2 : δ ≤ 2) : δ + δ ^ 2 / 4 ≤ (1 + δ) * log (1 + δ) := by
  have h1 := le_log_one_add_of_nonneg h0
  have hd : (0 : ℝ) < 2 + δ := by linarith
  have h3 : (1 + δ) * (2 * δ / (2 + δ)) ≤ (1 + δ) * log (1 + δ) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  refine le_trans ?_ h3
  rw [mul_div_assoc', le_div_iff₀ hd]
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h2), mul_nonneg h0 h0]

/-- The moment generating function of the number of successes. -/
lemma sum_iidPMF_mul_pow_bernCount (c : ℝ) :
    ∑ a : Fin n → Bool, iidPMF (bernoulliPMF p) n a * c ^ bernCount a = (1 - p + p * c) ^ n := by
  classical
  have h1 : ∀ a : Fin n → Bool, iidPMF (bernoulliPMF p) n a * c ^ bernCount a =
      ∏ i, (bernoulliPMF p (a i) * if a i = true then c else 1) := by
    intro a
    rw [prod_mul_distrib, prod_ite, prod_const_one, mul_one, prod_const]
    rfl
  simp only [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) =>
    bernoulliPMF p b * if b = true then c else 1)]
  simp [bernoulliPMF]
  ring_nf

/-- **The Chernoff bound of Appendix B**, for `0 < δ ≤ 2`: `P{Y_n ≥ n (1 + δ) p} ≤ e^{-n p δ² / 4}`
for a sum `Y_n` of `n` i.i.d. `Bern(p)` random variables. -/
theorem chernoff_bound (h0 : 0 ≤ p) (h1 : p ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2) (n : ℕ) :
    ∑ a : Fin n → Bool, iidPMF (bernoulliPMF p) n a *
      (if (n : ℝ) * (1 + δ) * p ≤ bernCount a then 1 else 0) ≤ exp (-(n * p * δ ^ 2 / 4)) := by
  have hq := bernoulliPMF_isPMF h0 h1
  have hc : (0 : ℝ) < 1 + δ := by linarith
  set l := log (1 + δ) with hl
  have hl0 : 0 ≤ l := log_nonneg (by linarith)
  set t := (n : ℝ) * (1 + δ) * p with ht
  have hpt : ∀ a : Fin n → Bool, (if t ≤ bernCount a then (1 : ℝ) else 0) ≤
      exp (-(l * t)) * (1 + δ) ^ bernCount a := by
    intro a
    have hpow : (1 + δ) ^ bernCount a = exp (bernCount a * l) := by
      rw [hl, ← rpow_natCast, rpow_def_of_pos hc, mul_comm]
    rw [hpow, ← exp_add]
    split_ifs with h
    · refine one_le_exp ?_
      nlinarith
    · exact (exp_pos _).le
  calc _ ≤ ∑ a : Fin n → Bool, iidPMF (bernoulliPMF p) n a *
        (exp (-(l * t)) * (1 + δ) ^ bernCount a) :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) ((iidPMF_isPMF hq n).nonneg a)
    _ = exp (-(l * t)) * (1 - p + p * (1 + δ)) ^ n := by
        rw [← sum_iidPMF_mul_pow_bernCount, mul_sum]
        exact sum_congr rfl fun a _ => by ring
    _ ≤ exp (-(l * t)) * exp (n * (p * δ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
        rw [exp_natCast_mul]
        refine pow_le_pow_left₀ (by nlinarith) ?_ _
        have := add_one_le_exp (p * δ)
        linarith
    _ = exp (-(l * t) + n * (p * δ)) := (exp_add _ _).symm
    _ ≤ _ := by
        refine exp_le_exp.2 ?_
        have h3 := chernoff_arith hδ.le hδ2
        have hnp : 0 ≤ (n : ℝ) * p := by positivity
        have h4 := mul_le_mul_of_nonneg_left h3 hnp
        rw [ht]
        nlinarith

/-- **The Chernoff bound of Appendix B as printed fails for large `δ`**, although it is stated for
all `δ > 0`. For `n = 1`, `p = 1/20` and `δ = 19`, the event is `X₁ = 1`, of probability `1/20`, and
the bound is `e^{-361/80} < 1/20`. -/
theorem printed_chernoff_false :
    exp (-((1 : ℕ) * (1 / 20 : ℝ) * 19 ^ 2 / 4)) <
      ∑ a : Fin 1 → Bool, iidPMF (bernoulliPMF (1 / 20)) 1 a *
        (if ((1 : ℕ) : ℝ) * (1 + 19) * (1 / 20) ≤ bernCount a then 1 else 0) := by
  have hsum : ∑ a : Fin 1 → Bool, iidPMF (bernoulliPMF (1 / 20)) 1 a *
      (if ((1 : ℕ) : ℝ) * (1 + 19) * (1 / 20) ≤ bernCount a then (1 : ℝ) else 0) = 1 / 20 := by
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
    have h1 : bernCount ((Equiv.funUnique (Fin 1) Bool).symm true) = 1 := by
      simp [bernCount, Finset.filter_true_of_mem]
    have h2 : bernCount ((Equiv.funUnique (Fin 1) Bool).symm false) = 0 := by
      simp [bernCount]
    rw [h1, h2]
    norm_num [iidPMF, bernoulliPMF]
  rw [hsum]
  -- `e^4 > 20`.
  have he : (2.7 : ℝ) < exp 1 := by
    have := exp_one_gt_d9
    linarith
  have h4 : (20 : ℝ) < exp 4 := by
    have h5 : exp 4 = exp 1 ^ 4 := by
      rw [← exp_natCast_mul]
      norm_num
    rw [h5]
    calc (20 : ℝ) < 2.7 ^ 4 := by norm_num
      _ ≤ exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he.le 4
  have h6 : exp (-((1 : ℕ) * (1 / 20 : ℝ) * 19 ^ 2 / 4)) ≤ exp (-4) :=
    exp_le_exp.2 (by norm_num)
  have h7 : exp (-4) < 1 / 20 := by
    rw [exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) h4
  linarith

end Chernoff

/-! ### The weak law of large numbers -/

section WeakLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}

/-- **The weak law of large numbers of Appendix B**, for pairwise independent identically
distributed random variables with finite mean and variance on a general probability space. -/
theorem weak_law_real (hL : ∀ i, MemLp (X i) 2 μ) (hind : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - μ[X 0]|}) atTop (𝓝 0) := by
  set V := Var[X 0; μ] with hV
  have hV0 : 0 ≤ V := ProbabilityTheory.variance_nonneg _ _
  have hbound : ∀ n : ℕ, 0 < n →
      μ.real {ω | ε ≤ |(∑ i ∈ range n, X i ω) / n - μ[X 0]|} ≤ V / ε ^ 2 / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set S : Ω → ℝ := fun ω => ∑ i ∈ range n, X i ω with hS
    have hSeq : S = ∑ i ∈ range n, X i := by
      funext ω
      simp [hS, Finset.sum_apply]
    have hSL : MemLp S 2 μ := by
      exact memLp_finsetSum _ fun i _ => hL i
    set A : Ω → ℝ := fun ω => S ω / n with hA
    have hAe : A = (n : ℝ)⁻¹ • S := by
      funext ω
      simp [hA, div_eq_inv_mul]
    have hAL : MemLp A 2 μ := by
      rw [hAe]
      exact hSL.const_smul _
    -- The mean.
    have hmeanS : μ[S] = (n : ℝ) * μ[X 0] := by
      have h0 : μ[S] = ∫ ω, ∑ i ∈ range n, X i ω ∂μ := rfl
      rw [h0, integral_finsetSum _ fun i _ => (hL i).integrable one_le_two]
      simp [(hid _).integral_eq]
    have hmeanA : μ[A] = μ[X 0] := by
      simp only [hA]
      rw [integral_div, hmeanS]
      field_simp
    -- The variance.
    have hvarS : Var[S; μ] = n * V := by
      rw [hSeq, IndepFun.variance_sum (fun i _ => hL i) fun i _ j _ hij => hind hij]
      simp [(hid _).variance_eq, hV]
    have hvarA : Var[A; μ] = V / n := by
      rw [hAe, ProbabilityTheory.variance_smul, hvarS]
      field_simp
    have hch := meas_ge_le_variance_div_sq hAL hε
    rw [hmeanA, hvarA] at hch
    have h2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hch
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_))
    · rfl
    · field_simp
  have hlim : Tendsto (fun n : ℕ => V / ε ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => measureReal_nonneg) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn using hbound n hn

end WeakLaw

end InfoTheory
