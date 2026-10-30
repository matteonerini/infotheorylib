/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StochasticProcess.Recurrence
public import InfoTheoryLib.SourceCoding.IntegerCode
public import InfoTheoryLib.Entropy.Bounds

/-!
# Recurrence time coding

A simple idealized version of the sliding window Lempel–Ziv algorithm describes the block
`X₀ⁿ⁻¹` by its recurrence time `Rₙ`, the distance back to its last occurrence, coded with the
integer code of Lemma 13.5.1 in `log Rₙ + 2 log log Rₙ + O(1)` bits. By Kac's lemma the mean of
`Rₙ` given `X₀ⁿ⁻¹ = xⁿ` is `1/p(xⁿ)`, and Jensen's inequality gives `E log Rₙ ≤ H(X₀ⁿ⁻¹)`: the
expected description length per symbol is asymptotically at most the entropy rate
(Theorem 13.5.1).

## Main definitions

* `StochasticProcess.recurrenceProb P n x m`: `Pr{X₀ⁿ⁻¹ = xⁿ, Rₙ = m + 1}`.
* `StochasticProcess.BlocksRecurrent P`: every block of positive probability recurs with
  probability one.
* `StochasticProcess.expectedRecurrenceLength P n ℓ`: `E ℓ(Rₙ)`.

## Main statements

* `StochasticProcess.expected_log_recurrence_le`: **(13.76)–(13.79)**, `E log Rₙ ≤ H(X₀ⁿ⁻¹)`.
* `StochasticProcess.expected_log_log_recurrence_le`: **(13.82)–(13.83)**.
* `StochasticProcess.expectedRecurrenceLength_eliasDelta_le`: the expected length of the
  recurrence time code of blocks of length `n` is at most
  `H(X₀ⁿ⁻¹) + 2 log₂ (H(X₀ⁿ⁻¹) + 1) + 1` bits.
* `StochasticProcess.eventually_expectedRecurrenceLength_le`: **Theorem 13.5.1**, upper bound,
  `lim sup (1/n) E Lₙ ≤ H(𝒳)`.

## Implementation notes

As in `StochasticProcess.Recurrence`, we look forward from time `0` to the next occurrence of the
block, which by stationarity has the law of the backward recurrence time, and we assume that the
blocks recur with probability one, which holds for ergodic processes. Jensen's inequality is
replaced by the tangent line bound `log t ≤ log a + t/a - 1`. The lower bound `E Lₙ ≥ H(X₀ⁿ⁻¹)`,
which the book quotes from Chapter 5, is not formalized: the code depends on the infinite past,
which is not part of this model of processes.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 13.5.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

namespace StochasticProcess

variable {α : Type*} [Fintype α] [DecidableEq α] (P : StochasticProcess α)

/-- `Pr{X₀ⁿ⁻¹ = xⁿ, Rₙ = m + 1}`: the block at time `0` is `xⁿ` and occurs next at time `m + 1`. -/
def recurrenceProb (n : ℕ) (x : Fin n → α) (m : ℕ) : ℝ := (P.blocks n).firstReturnProb x m

/-- Every block of positive probability recurs with probability one (true for an ergodic
process). -/
def BlocksRecurrent : Prop := ∀ n (x : Fin n → α), P.law n x ≠ 0 → (P.blocks n).IsRecurrent x

/-- The expected value `E ℓ(Rₙ)` of a function of the recurrence time of the first block. -/
def expectedRecurrenceLength (n : ℕ) (ℓ : ℕ → ℝ) : ℝ :=
  ∑ x : Fin n → α, ∑' m, recurrenceProb P n x m * ℓ (m + 1)

lemma recurrenceProb_nonneg (n : ℕ) (x : Fin n → α) (m : ℕ) : 0 ≤ recurrenceProb P n x m :=
  firstReturnProb_nonneg _ _ _

lemma recurrenceProb_le (n : ℕ) (x : Fin n → α) (m : ℕ) : recurrenceProb P n x m ≤ P.law n x := by
  rw [← blocks_law_one P n x]
  exact firstReturnProb_le _ m

variable {P}

/-- The recurrence time is finite with probability one: `∑ₘ Pr{xⁿ, Rₙ = m + 1} = p(xⁿ)`. -/
lemma hasSum_recurrenceProb (hP : P.IsStationary) (n : ℕ) (x : Fin n → α) :
    HasSum (recurrenceProb P n x) (P.law n x) := by
  rw [← blocks_law_one P n x]
  exact hasSum_firstReturnProb x (blocks_isStationary P hP n)

lemma summable_mul_recurrenceProb (hP : P.IsStationary) (n : ℕ) (x : Fin n → α) :
    Summable fun m : ℕ => ((m : ℝ) + 1) * recurrenceProb P n x m :=
  summable_of_sum_range_le (c := 1) (fun m => mul_nonneg (by positivity)
    (recurrenceProb_nonneg P n x m))
    (sum_range_mul_firstReturnProb_le x (blocks_isStationary P hP n))

/-- Functions of the recurrence time growing at most linearly are integrable. -/
lemma summable_recurrenceProb_mul (hP : P.IsStationary) (n : ℕ) (x : Fin n → α) {g : ℕ → ℝ}
    {C : ℝ} (hg0 : ∀ m, 0 ≤ g m) (hg : ∀ m, g m ≤ C * ((m : ℝ) + 1)) :
    Summable fun m => recurrenceProb P n x m * g m :=
  Summable.of_nonneg_of_le (fun m => mul_nonneg (recurrenceProb_nonneg P n x m) (hg0 m))
    (fun m => by
      have := mul_le_mul_of_nonneg_left (hg m) (recurrenceProb_nonneg P n x m)
      calc recurrenceProb P n x m * g m ≤ recurrenceProb P n x m * (C * ((m : ℝ) + 1)) := this
        _ = C * (((m : ℝ) + 1) * recurrenceProb P n x m) := by ring)
    ((summable_mul_recurrenceProb hP n x).mul_left C)

lemma log_le_succ (m : ℕ) : log ((m : ℝ) + 1) ≤ 1 * ((m : ℝ) + 1) := by
  rw [one_mul]
  exact (log_le_sub_one_of_pos (by positivity)).trans (by linarith)

lemma log_succ_nonneg (m : ℕ) : 0 ≤ log ((m : ℝ) + 1) :=
  log_nonneg (by linarith [m.cast_nonneg (α := ℝ)])

/-- **(13.76)–(13.78)** `E[log Rₙ | xⁿ] ≤ log 1/p(xⁿ)`, in the form
`∑ₘ Pr{xⁿ, Rₙ = m + 1} log (m + 1) ≤ -p(xⁿ) log p(xⁿ)`. -/
theorem tsum_recurrenceProb_mul_log_le (hP : P.IsStationary) (hrec : P.BlocksRecurrent) (n : ℕ)
    (x : Fin n → α) :
    ∑' m, recurrenceProb P n x m * log ((m : ℝ) + 1) ≤ negMulLog (P.law n x) := by
  set p := P.law n x
  rcases eq_or_ne p 0 with hp | hp
  · have : ∀ m, recurrenceProb P n x m = 0 := fun m =>
      le_antisymm ((recurrenceProb_le P n x m).trans hp.le) (recurrenceProb_nonneg P n x m)
    simp [this, hp]
  have hp0 : 0 < p := lt_of_le_of_ne ((P.isPMF n).nonneg x) (Ne.symm hp)
  have hKac : HasSum (fun m : ℕ => ((m : ℝ) + 1) * recurrenceProb P n x m) 1 := by
    have := hasSum_mul_firstReturnProb x (blocks_isStationary P hP n) (hrec n x hp)
    exact this
  have hr := hasSum_recurrenceProb hP n x
  -- The tangent line `log (m + 1) ≤ -log p + p (m + 1) - 1`.
  have hbound : ∀ m : ℕ, recurrenceProb P n x m * log ((m : ℝ) + 1) ≤
      recurrenceProb P n x m * (-log p) + p * (((m : ℝ) + 1) * recurrenceProb P n x m) -
        recurrenceProb P n x m := fun m => by
    have h := log_le_sub_one_of_pos (show 0 < p * ((m : ℝ) + 1) by positivity)
    rw [log_mul hp (by positivity)] at h
    have := mul_le_mul_of_nonneg_left (show log ((m : ℝ) + 1) ≤ -log p + p * ((m : ℝ) + 1) - 1 by
      linarith) (recurrenceProb_nonneg P n x m)
    linarith
  have hsum : HasSum (fun m : ℕ => recurrenceProb P n x m * (-log p) +
      p * (((m : ℝ) + 1) * recurrenceProb P n x m) - recurrenceProb P n x m)
      (p * (-log p) + p * 1 - p) :=
    ((hr.mul_right _).add (hKac.mul_left p)).sub hr
  have hs := summable_recurrenceProb_mul hP n x (fun m => log_succ_nonneg m) log_le_succ
  refine (hasSum_le hbound hs.hasSum hsum).trans_eq ?_
  rw [negMulLog]
  ring

/-- **(13.76)–(13.79)** The expected logarithm of the recurrence time of a block of length `n` is
at most its entropy: `E log Rₙ ≤ H(X₀ⁿ⁻¹)`. -/
theorem expected_log_recurrence_le (hP : P.IsStationary) (hrec : P.BlocksRecurrent) (n : ℕ) :
    expectedRecurrenceLength P n (fun i => log i) ≤ P.jointEntropy n := by
  rw [jointEntropy, entropy_eq_sum_negMulLog, expectedRecurrenceLength]
  refine sum_le_sum fun x _ => ?_
  push_cast
  exact tsum_recurrenceProb_mul_log_le hP hrec n x

/-- The tangent line bound for the concave function `log₂ (t + 1)` at `b`. -/
lemma logb_add_one_le (b : ℝ) (hb : 0 ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    logb 2 (t + 1) ≤ logb 2 (b + 1) + (t - b) / ((b + 1) * log 2) := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  have h := log_le_sub_one_of_pos (show 0 < (t + 1) / (b + 1) by positivity)
  rw [log_div (by positivity) (by positivity)] at h
  have h' : log (t + 1) ≤ log (b + 1) + (t - b) / (b + 1) := by
    have : (t + 1) / (b + 1) - 1 = (t - b) / (b + 1) := by field_simp; ring
    linarith
  rw [logb, logb, show (t - b) / ((b + 1) * log 2) = ((t - b) / (b + 1)) / log 2 by
    rw [div_div], ← add_div]
  exact div_le_div_of_nonneg_right h' hl.le

/-- `log₂ (z + 1) ≤ z / log 2`. -/
lemma logb_add_one_le_div {z : ℝ} (hz : 0 ≤ z) : logb 2 (z + 1) ≤ 1 / log 2 * z := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  have := log_le_sub_one_of_pos (show 0 < z + 1 by linarith)
  rw [logb, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (by linarith) hl.le

/-- The total mass: `∑ₓ ∑ₘ Pr{xⁿ, Rₙ = m + 1} = 1`. -/
lemma sum_tsum_recurrenceProb (hP : P.IsStationary) (n : ℕ) :
    ∑ x : Fin n → α, ∑' m, recurrenceProb P n x m = 1 := by
  simp only [(hasSum_recurrenceProb hP n _).tsum_eq]
  exact (P.isPMF n).sum_eq_one

/-- **(13.82)–(13.83)** `E log₂ (log₂ Rₙ + 1) ≤ log₂ (E log₂ Rₙ + 1)`. -/
theorem expected_log_log_recurrence_le (hP : P.IsStationary) (n : ℕ) :
    expectedRecurrenceLength P n (fun i => logb 2 (logb 2 i + 1)) ≤
      logb 2 (expectedRecurrenceLength P n (fun i => logb 2 i) + 1) := by
  set b := expectedRecurrenceLength P n (fun i => logb 2 i)
  have hl : 0 < log 2 := log_pos (by norm_num)
  have ht : ∀ m : ℕ, 0 ≤ logb 2 ((m : ℝ) + 1) := fun m =>
    logb_nonneg (by norm_num) (by linarith [m.cast_nonneg (α := ℝ)])
  have htle : ∀ m : ℕ, logb 2 ((m : ℝ) + 1) ≤ (1 / log 2) * ((m : ℝ) + 1) := fun m => by
    rw [logb, div_eq_mul_inv, one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left (by simpa using log_le_succ m) (by positivity)
  have hb : 0 ≤ b := sum_nonneg fun x _ => tsum_nonneg fun m => by
    push_cast
    exact mul_nonneg (recurrenceProb_nonneg P n x m) (ht m)
  set c₁ := 1 / ((b + 1) * log 2)
  set c₀ := logb 2 (b + 1) - b * c₁
  have hpt : ∀ x : Fin n → α, ∀ m : ℕ, recurrenceProb P n x m * logb 2 (logb 2 ((m : ℝ) + 1) + 1) ≤
      c₀ * recurrenceProb P n x m + c₁ * (recurrenceProb P n x m * logb 2 ((m : ℝ) + 1)) :=
    fun x m => by
      have := logb_add_one_le b hb (ht m)
      have h2 := mul_le_mul_of_nonneg_left this (recurrenceProb_nonneg P n x m)
      simp only [c₀, c₁]
      rw [show (logb 2 ((m : ℝ) + 1) - b) / ((b + 1) * log 2) =
        1 / ((b + 1) * log 2) * logb 2 ((m : ℝ) + 1) - b * (1 / ((b + 1) * log 2)) by ring] at h2
      linarith
  have hs1 : ∀ x, Summable fun m => recurrenceProb P n x m * logb 2 ((m : ℝ) + 1) := fun x =>
    summable_recurrenceProb_mul hP n x ht htle
  have hs0 : ∀ x, Summable (recurrenceProb P n x) := fun x =>
    (hasSum_recurrenceProb hP n x).summable
  have hs2 : ∀ x, Summable fun m => recurrenceProb P n x m * logb 2 (logb 2 ((m : ℝ) + 1) + 1) :=
    fun x => summable_recurrenceProb_mul hP n x (C := 1 / log 2 * (1 / log 2))
      (fun m => logb_nonneg (by norm_num) (by linarith [ht m]))
      (fun m => by
        have := logb_add_one_le_div (ht m)
        have h1 := mul_le_mul_of_nonneg_left (htle m) (show 0 ≤ 1 / log 2 by positivity)
        linarith)
  calc expectedRecurrenceLength P n (fun i => logb 2 (logb 2 i + 1))
      = ∑ x : Fin n → α, ∑' m, recurrenceProb P n x m * logb 2 (logb 2 ((m : ℝ) + 1) + 1) := by
        simp [expectedRecurrenceLength]
    _ ≤ ∑ x : Fin n → α, ∑' m, (c₀ * recurrenceProb P n x m +
        c₁ * (recurrenceProb P n x m * logb 2 ((m : ℝ) + 1))) :=
        sum_le_sum fun x _ => Summable.tsum_le_tsum (hpt x) (hs2 x)
          (((hs0 x).mul_left c₀).add ((hs1 x).mul_left c₁))
    _ = c₀ * ∑ x : Fin n → α, ∑' m, recurrenceProb P n x m + c₁ * b := by
        simp only [b, expectedRecurrenceLength, mul_sum]
        rw [← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [Summable.tsum_add ((hs0 x).mul_left c₀) ((hs1 x).mul_left c₁), tsum_mul_left,
          tsum_mul_left]
        push_cast
        rfl
    _ = logb 2 (b + 1) := by
        rw [sum_tsum_recurrenceProb hP]
        ring

/-- The expected length of the recurrence time code of blocks of length `n`, in bits, is at most
`H(X₀ⁿ⁻¹)/log 2 + 2 log₂ (H(X₀ⁿ⁻¹)/log 2 + 1) + 1`, the entropy being in nats. -/
theorem expectedRecurrenceLength_eliasDelta_le (hP : P.IsStationary) (hrec : P.BlocksRecurrent)
    (n : ℕ) :
    expectedRecurrenceLength P n (fun i => (eliasDelta i).length) ≤
      P.jointEntropy n / log 2 + 2 * logb 2 (P.jointEntropy n / log 2 + 1) + 1 := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  have ht : ∀ m : ℕ, 0 ≤ logb 2 ((m : ℝ) + 1) := fun m =>
    logb_nonneg (by norm_num) (by linarith [m.cast_nonneg (α := ℝ)])
  -- `E log₂ Rₙ ≤ H/log 2`.
  have hb : expectedRecurrenceLength P n (fun i => logb 2 i) ≤ P.jointEntropy n / log 2 := by
    have h := expected_log_recurrence_le hP hrec n
    rw [le_div_iff₀ hl]
    refine le_trans (le_of_eq ?_) h
    simp only [expectedRecurrenceLength, sum_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [logb, mul_assoc, div_mul_cancel₀ _ hl.ne']
  have hb0 : 0 ≤ expectedRecurrenceLength P n (fun i => logb 2 i) :=
    sum_nonneg fun x _ => tsum_nonneg fun m => by
      push_cast
      exact mul_nonneg (recurrenceProb_nonneg P n x m) (ht m)
  have hll := expected_log_log_recurrence_le hP n
  have hmono : logb 2 (expectedRecurrenceLength P n (fun i => logb 2 i) + 1) ≤
      logb 2 (P.jointEntropy n / log 2 + 1) :=
    logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  -- The code length is at most `log₂ i + 2 log₂ (log₂ i + 1) + 1`.
  have hs0 : ∀ x, Summable (recurrenceProb P n x) := fun x =>
    (hasSum_recurrenceProb hP n x).summable
  have hsl : ∀ x, Summable fun m => recurrenceProb P n x m * logb 2 ((m : ℝ) + 1) := fun x =>
    summable_recurrenceProb_mul hP n x ht (C := 1 / log 2) fun m => by
      rw [logb, div_eq_mul_inv, one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left (by simpa using log_le_succ m) (by positivity)
  have hsll : ∀ x, Summable fun m => recurrenceProb P n x m * logb 2 (logb 2 ((m : ℝ) + 1) + 1) :=
    fun x => Summable.of_nonneg_of_le
      (fun m => mul_nonneg (recurrenceProb_nonneg P n x m)
        (logb_nonneg (by norm_num) (by linarith [ht m])))
      (fun m => by
        have := mul_le_mul_of_nonneg_left (logb_add_one_le_div (ht m))
          (recurrenceProb_nonneg P n x m)
        calc recurrenceProb P n x m * logb 2 (logb 2 ((m : ℝ) + 1) + 1)
            ≤ recurrenceProb P n x m * (1 / log 2 * logb 2 ((m : ℝ) + 1)) := this
          _ = 1 / log 2 * (recurrenceProb P n x m * logb 2 ((m : ℝ) + 1)) := by ring)
      ((hsl x).mul_left (1 / log 2))
  have hpt : ∀ x : Fin n → α, ∀ m : ℕ, recurrenceProb P n x m * ((eliasDelta (m + 1)).length : ℝ) ≤
      recurrenceProb P n x m * logb 2 ((m : ℝ) + 1) +
        2 * (recurrenceProb P n x m * logb 2 (logb 2 ((m : ℝ) + 1) + 1)) +
        recurrenceProb P n x m := fun x m => by
    have h := length_eliasDelta_le (m + 1)
    push_cast at h
    have := mul_le_mul_of_nonneg_left h (recurrenceProb_nonneg P n x m)
    linarith
  have hsd : ∀ x, Summable fun m => recurrenceProb P n x m * ((eliasDelta (m + 1)).length : ℝ) :=
    fun x => Summable.of_nonneg_of_le
      (fun m => mul_nonneg (recurrenceProb_nonneg P n x m) (by positivity)) (hpt x)
      (((hsl x).add ((hsll x).mul_left 2)).add (hs0 x))
  calc expectedRecurrenceLength P n (fun i => (eliasDelta i).length)
      = ∑ x : Fin n → α, ∑' m, recurrenceProb P n x m * ((eliasDelta (m + 1)).length : ℝ) := rfl
    _ ≤ ∑ x : Fin n → α, ∑' m, (recurrenceProb P n x m * logb 2 ((m : ℝ) + 1) +
        2 * (recurrenceProb P n x m * logb 2 (logb 2 ((m : ℝ) + 1) + 1)) +
        recurrenceProb P n x m) :=
        sum_le_sum fun x _ => Summable.tsum_le_tsum (hpt x) (hsd x)
          (((hsl x).add ((hsll x).mul_left 2)).add (hs0 x))
    _ = expectedRecurrenceLength P n (fun i => logb 2 i) +
        2 * expectedRecurrenceLength P n (fun i => logb 2 (logb 2 i + 1)) +
        ∑ x : Fin n → α, ∑' m, recurrenceProb P n x m := by
        simp only [expectedRecurrenceLength, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [Summable.tsum_add ((hsl x).add ((hsll x).mul_left 2)) (hs0 x),
          Summable.tsum_add (hsl x) ((hsll x).mul_left 2), tsum_mul_left]
        push_cast
        rfl
    _ ≤ P.jointEntropy n / log 2 + 2 * logb 2 (P.jointEntropy n / log 2 + 1) + 1 := by
        rw [sum_tsum_recurrenceProb hP]
        linarith

/-- `log₂ (c n + 1) / n → 0`. -/
lemma tendsto_logb_mul_add_one_div (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => logb 2 (c * n + 1) / n) atTop (𝓝 0) := by
  set d := c + 1
  have hd : 0 < d := by positivity
  have h := (tendsto_pow_log_div_mul_add_atTop (1 / d) (-(1 / d)) 1 (by positivity)).comp
    (tendsto_atTop_add_const_right _ (1 : ℝ)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hd))
  have h' : Tendsto (fun n : ℕ => log (d * n + 1) / n) atTop (𝓝 0) := by
    refine h.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
    simp only [Function.comp, pow_one]
    congr 1
    field_simp
    ring
  have hl : 0 < log 2 := log_pos (by norm_num)
  have h'' := h'.div_const (log 2)
  rw [zero_div] at h''
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h''
    ((eventually_gt_atTop 0).mono fun n hn => ?_) ((eventually_gt_atTop 0).mono fun n hn => ?_)
  · exact div_nonneg (logb_nonneg (by norm_num) (by nlinarith [n.cast_nonneg (α := ℝ)]))
      n.cast_nonneg
  · rw [logb, div_div, div_div, mul_comm (n : ℝ)]
    refine div_le_div_of_nonneg_right (log_le_log (by nlinarith [n.cast_nonneg (α := ℝ)]) ?_)
      (by positivity)
    nlinarith [n.cast_nonneg (α := ℝ)]

/-- **Theorem 13.5.1 (upper bound), (13.74)–(13.81).** For a stationary process whose blocks
recur with probability one, the recurrence time code has asymptotic expected length per symbol at
most the entropy rate: `lim sup (1/n) E Lₙ ≤ H(𝒳)` bits. -/
theorem eventually_expectedRecurrenceLength_le (hP : P.IsStationary) (hrec : P.BlocksRecurrent)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, expectedRecurrenceLength P n (fun i => (eliasDelta i).length) / n ≤
      P.entropyRate / log 2 + ε := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  set c := log (Fintype.card α) / log 2
  have hc : 0 ≤ c := by
    by_cases h : Fintype.card α = 0
    · simp [c, h]
    · exact div_nonneg (log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 h)) hl.le
  -- `H(X₀ⁿ⁻¹) ≤ n log |α|`.
  have hH : ∀ n, P.jointEntropy n / log 2 ≤ c * n := fun n => by
    rw [div_le_iff₀ hl]
    have := entropy_le_log_card (P.isPMF n)
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, log_pow] at this
    calc P.jointEntropy n ≤ n * log (Fintype.card α) := this
      _ = c * n * log 2 := by simp only [c]; field_simp
  have hrate := (hP.hasEntropyRate.div_const (log 2))
  have hlog := (tendsto_logb_mul_add_one_div c hc).const_mul 2
  have hinv := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hsum := (hrate.add hlog).add hinv
  rw [mul_zero, add_zero, add_zero] at hsum
  filter_upwards [(tendsto_order.1 hsum).2 _ (lt_add_of_pos_right _ hε),
    eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hbound := expectedRecurrenceLength_eliasDelta_le hP hrec n
  have hmono : logb 2 (P.jointEntropy n / log 2 + 1) ≤ logb 2 (c * n + 1) :=
    logb_le_logb_of_le (by norm_num)
      (by have := P.jointEntropy_nonneg n; positivity) (by linarith [hH n])
  refine le_trans ?_ hn.le
  rw [div_le_iff₀ hn']
  have e : (P.jointEntropy n / n / log 2 + 2 * (logb 2 (c * n + 1) / n) + 1 / n) * n =
      P.jointEntropy n / log 2 + 2 * logb 2 (c * n + 1) + 1 := by field_simp
  rw [e]
  linarith

end StochasticProcess

end InfoTheory
