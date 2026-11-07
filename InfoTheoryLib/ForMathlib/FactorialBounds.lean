/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Elementary bounds on `log n!`

## Main statements

* `mul_log_sub_lt_log_factorial`, `log_factorial_lt`:
  `n log n - n < log n! < (n + 1) log (n + 1) - n` for `n > 0`.

## Implementation notes

The book proves the bounds by comparing `log n!` with integrals of `log`. We prove them by induction
from `log x ≤ x - 1`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Lemma 6.11
-/

open Real

public section

namespace InfoTheory

/-- `n log n - n < log n!` for `n > 0`. -/
theorem mul_log_sub_lt_log_factorial {n : ℕ} (hn : 0 < n) :
    n * log n - n < log n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h₁ : log (((n : ℝ) + 1) / n) ≤ ((n : ℝ) + 1) / n - 1 :=
      log_le_sub_one_of_pos (by positivity)
    rw [log_div hn₁.ne' hn'.ne'] at h₁
    have h₂ : n * (log ((n : ℝ) + 1) - log n) ≤ 1 := by
      calc n * (log ((n : ℝ) + 1) - log n) ≤ n * (((n : ℝ) + 1) / n - 1) :=
            mul_le_mul_of_nonneg_left h₁ hn'.le
        _ = 1 := by field_simp; ring
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [Nat.factorial_succ]
    push_cast
    rw [log_mul hn₁.ne' hf.ne']
    linarith

/-- `log n! < (n + 1) log (n + 1) - n` for `n > 0`. -/
theorem log_factorial_lt {n : ℕ} (hn : 0 < n) :
    log n.factorial < (n + 1) * log (n + 1) - n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have := log_two_gt_d9
    norm_num
    linarith
  | succ n hn ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn₂ : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h₁ : log (((n : ℝ) + 1) / (n + 2)) ≤ ((n : ℝ) + 1) / (n + 2) - 1 :=
      log_le_sub_one_of_pos (by positivity)
    rw [log_div hn₁.ne' hn₂.ne'] at h₁
    have h₂ : 1 ≤ ((n : ℝ) + 2) * (log ((n : ℝ) + 2) - log ((n : ℝ) + 1)) := by
      have h₃ : ((n : ℝ) + 2) * (1 - ((n : ℝ) + 1) / (n + 2)) = 1 := by field_simp; ring
      calc 1 = ((n : ℝ) + 2) * (1 - ((n : ℝ) + 1) / (n + 2)) := h₃.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hn₂.le
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [Nat.factorial_succ]
    push_cast
    rw [log_mul hn₁.ne' hf.ne', show (n : ℝ) + 1 + 1 = n + 2 by ring]
    nlinarith

end InfoTheory
