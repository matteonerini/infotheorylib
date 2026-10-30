/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib

/-!
# Auxiliary facts about the logarithm

Elementary real-analysis facts about `Real.log` and `Real.negMulLog` used throughout the library.
They do not mention any information-theoretic notion and are candidates for upstreaming to
Mathlib.

## Main statements

* `sub_le_mul_log_div`: `a - b ≤ a log (a / b)`, the pointwise form of Gibbs' inequality, and its
  equality case `mul_log_div_eq_sub_iff`.
* `negMulLog_inv_two_pow`: `-2⁻ᵏ log 2⁻ᵏ = k 2⁻ᵏ log 2`, used to evaluate entropies of dyadic
  distributions.
* `log_three_div_log_two_bounds`, `log_seven_div_log_two_bounds`: certified decimal bounds on
  `log₂ 3` and `log₂ 7`.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- `-x log x` at `x = 2⁻ᵏ`. -/
lemma negMulLog_inv_two_pow (k : ℕ) :
    negMulLog ((2 : ℝ) ^ k)⁻¹ = k / 2 ^ k * log 2 := by
  rw [negMulLog, log_inv, log_pow]; ring

lemma negMulLog_two_inv : negMulLog (2⁻¹ : ℝ) = 1 / 2 * log 2 := by
  simpa using negMulLog_inv_two_pow 1

lemma negMulLog_four_inv : negMulLog (4⁻¹ : ℝ) = 2 / 4 * log 2 := by
  have := negMulLog_inv_two_pow 2; norm_num at this ⊢; linarith

lemma negMulLog_eight_inv : negMulLog (8⁻¹ : ℝ) = 3 / 8 * log 2 := by
  have := negMulLog_inv_two_pow 3; norm_num at this ⊢; linarith

lemma negMulLog_sixteen_inv : negMulLog (16⁻¹ : ℝ) = 4 / 16 * log 2 := by
  have := negMulLog_inv_two_pow 4; norm_num at this ⊢; linarith

lemma negMulLog_thirtytwo_inv : negMulLog (32⁻¹ : ℝ) = 5 / 32 * log 2 := by
  have := negMulLog_inv_two_pow 5; norm_num at this ⊢; linarith

lemma log_two_pos' : 0 < log (2 : ℝ) := log_pos one_lt_two

/-- `1.5849 < log₂ 3 < 1.585`. -/
lemma log_three_div_log_two_bounds : 1.5849 < log 3 / log 2 ∧ log 3 / log 2 < 1.585 := by
  have h2 := log_two_pos'
  constructor
  · rw [lt_div_iff₀ h2]
    have h : (2 : ℝ) ^ 15849 < 3 ^ 10000 := by
      have : (2 : ℕ) ^ 15849 < 3 ^ 10000 := by
        set_option exponentiation.threshold 30000 in norm_num
      exact_mod_cast this
    have := log_lt_log (by positivity) h
    rw [log_pow, log_pow] at this
    push_cast at this
    linarith
  · rw [div_lt_iff₀ h2]
    have h : (3 : ℝ) ^ 200 < 2 ^ 317 := by
      have : (3 : ℕ) ^ 200 < 2 ^ 317 := by
        set_option exponentiation.threshold 30000 in norm_num
      exact_mod_cast this
    have := log_lt_log (by positivity) h
    rw [log_pow, log_pow] at this
    push_cast at this
    linarith

/-- `2.8063 < log₂ 7 < 2.8074`. -/
lemma log_seven_div_log_two_bounds : 2.8063 < log 7 / log 2 ∧ log 7 / log 2 < 2.8074 := by
  have h2 := log_two_pos'
  constructor
  · rw [lt_div_iff₀ h2]
    have h : (2 : ℝ) ^ 28063 < 7 ^ 10000 := by
      have : (2 : ℕ) ^ 28063 < 7 ^ 10000 := by
        set_option exponentiation.threshold 30000 in norm_num
      exact_mod_cast this
    have := log_lt_log (by positivity) h
    rw [log_pow, log_pow] at this
    push_cast at this
    linarith
  · rw [div_lt_iff₀ h2]
    have h : (7 : ℝ) ^ 10000 < 2 ^ 28074 := by
      have : (7 : ℕ) ^ 10000 < 2 ^ 28074 := by
        set_option exponentiation.threshold 30000 in norm_num
      exact_mod_cast this
    have := log_lt_log (by positivity) h
    rw [log_pow, log_pow] at this
    push_cast at this
    linarith

/-- The elementary inequality `a log (a/b) ≥ a - b` behind the information inequality. -/
lemma sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a - b ≤ a * log (a / b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hb
  · have hb : 0 < b := hb.lt_of_ne fun h => ha.ne' (hab h.symm)
    have h := log_le_sub_one_of_pos (div_pos hb ha)
    have e : log (a / b) = -log (b / a) := by rw [← log_inv, inv_div]
    rw [e]
    have : a * log (b / a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h ha.le
    have e2 : a * (b / a - 1) = b - a := by field_simp
    linarith

lemma mul_log_div_eq_sub_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a * log (a / b) = a - b ↔ a = b := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, zero_sub, zero_eq_neg]; exact eq_comm
  · have hb : 0 < b := hb.lt_of_ne fun h => ha.ne' (hab h.symm)
    constructor
    · intro h
      by_contra hne
      have hne' : b / a ≠ 1 := fun h' => hne ((div_eq_one_iff_eq ha.ne').1 h').symm
      have h' := log_lt_sub_one_of_pos (div_pos hb ha) hne'
      have e : log (a / b) = -log (b / a) := by rw [← log_inv, inv_div]
      rw [e] at h
      have : a * log (b / a) < a * (b / a - 1) := mul_lt_mul_of_pos_left h' ha
      have e2 : a * (b / a - 1) = b - a := by field_simp
      linarith
    · rintro rfl; simp [div_self ha.ne']

lemma mul_log_div_self (x : ℝ) : x * log (x / x) = 0 := by
  rcases eq_or_ne x 0 with rfl | hx <;> simp [*]

lemma mul_log_scale {t a b : ℝ} : (t * a) * log ((t * a) / (t * b)) = t * (a * log (a / b)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [mul_div_mul_left _ _ ht]; ring

/-- Injectivity of the log-odds `log θ - log (1 - θ)` on `(0, 1)`. -/
lemma log_odds_injective {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (h : log a - log (1 - a) = log b - log (1 - b)) : a = b := by
  rw [← log_div ha0.ne' (by linarith), ← log_div hb0.ne' (by linarith)] at h
  have := log_injOn_pos (Set.mem_Ioi.2 (div_pos ha0 (by linarith)))
    (Set.mem_Ioi.2 (div_pos hb0 (by linarith))) h
  rw [div_eq_div_iff (by linarith) (by linarith)] at this
  linarith

lemma log_card_sub_one_le_log_card [Nonempty α] :
    log ((Fintype.card α : ℝ) - 1) ≤ log (Fintype.card α) := by
  rcases (sub_nonneg.2 (by exact_mod_cast Fintype.card_pos : (1 : ℝ) ≤ Fintype.card α)).eq_or_lt
    with h | h
  · rw [← h, log_zero]
    exact log_nonneg (by exact_mod_cast Fintype.card_pos)
  · exact log_le_log h (by linarith)

end InfoTheory
