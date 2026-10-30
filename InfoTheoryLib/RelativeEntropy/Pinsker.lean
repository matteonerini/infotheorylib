/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RelativeEntropy.InformationInequality
public import InfoTheoryLib.Analysis.LogSum

/-!
# The `L₁` distance and Pinsker's inequality

The `L₁` distance between two pmfs is `‖P₁ - P₂‖₁ = ∑ₓ |P₁(x) - P₂(x)|`; half of it is the
variational distance `max_B (P₁(B) - P₂(B))`. Convergence in relative entropy implies convergence
in `L₁`: `D(P₁‖P₂) ≥ ½ ‖P₁ - P₂‖₁²` (Pinsker's inequality, in nats).

## Main definitions

* `l1Dist P₁ P₂`: the `L₁` distance (11.131).

## Main statements

* `l1Dist_eq_two_mul`: (11.132)–(11.136), `‖P₁ - P₂‖₁ = 2 (P₁(A) - P₂(A))` for
  `A = {x : P₁(x) > P₂(x)}`.
* `sum_sub_sum_le_l1Dist_div_two`: (11.137), `P₁(B) - P₂(B) ≤ ‖P₁ - P₂‖₁/2`, with equality for
  `B = A`.
* `two_mul_sq_le_binary`: (11.139)–(11.143), the binary case.
* `pinsker`: **Lemma 11.6.1**, `D(P₁‖P₂) ≥ ½ ‖P₁ - P₂‖₁²`.

## Implementation notes

Logarithms are natural, so the book's `1/(2 ln 2)` with `D` in bits is our `1/2`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 11.6
-/

open Real Finset Set

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### The `L₁` distance -/

/-- **Definition (11.131).** The `L₁` distance `‖P₁ - P₂‖₁ = ∑ₓ |P₁(x) - P₂(x)|`. -/
def l1Dist (P₁ P₂ : α → ℝ) : ℝ := ∑ x, |P₁ x - P₂ x|

open Classical in
/-- **(11.132)–(11.136)** `‖P₁ - P₂‖₁ = 2 (P₁(A) - P₂(A))` for `A = {x : P₁(x) > P₂(x)}`. -/
theorem l1Dist_eq_two_mul {P₁ P₂ : α → ℝ} (h₁ : IsPMF P₁) (h₂ : IsPMF P₂) :
    l1Dist P₁ P₂ = 2 * (∑ x ∈ univ.filter (fun x => P₂ x < P₁ x), P₁ x -
      ∑ x ∈ univ.filter (fun x => P₂ x < P₁ x), P₂ x) := by
  set A := univ.filter fun x => P₂ x < P₁ x
  have hs₁ := sum_filter_add_sum_filter_not univ (fun x => P₂ x < P₁ x) P₁
  have hs₂ := sum_filter_add_sum_filter_not univ (fun x => P₂ x < P₁ x) P₂
  have habs := sum_filter_add_sum_filter_not univ (fun x => P₂ x < P₁ x) fun x => |P₁ x - P₂ x|
  rw [h₁.sum_eq_one] at hs₁
  rw [h₂.sum_eq_one] at hs₂
  have e1 : ∑ x ∈ A, |P₁ x - P₂ x| = ∑ x ∈ A, P₁ x - ∑ x ∈ A, P₂ x := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun x hx => abs_of_pos (sub_pos.2 (mem_filter.1 hx).2)
  have e2 : ∑ x ∈ univ.filter (fun x => ¬P₂ x < P₁ x), |P₁ x - P₂ x| =
      ∑ x ∈ univ.filter (fun x => ¬P₂ x < P₁ x), P₂ x -
        ∑ x ∈ univ.filter (fun x => ¬P₂ x < P₁ x), P₁ x := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun x hx => ?_
    rw [abs_of_nonpos (sub_nonpos.2 (not_lt.1 (mem_filter.1 hx).2))]
    ring
  rw [l1Dist, ← habs, e1, e2]
  linarith

open Classical in
/-- **(11.137)** `P₁(B) - P₂(B) ≤ ‖P₁ - P₂‖₁/2` for every set `B`: the variational distance is half
the `L₁` distance, attained at `A = {x : P₁(x) > P₂(x)}`. -/
theorem sum_sub_sum_le_l1Dist_div_two {P₁ P₂ : α → ℝ} (h₁ : IsPMF P₁) (h₂ : IsPMF P₂)
    (B : Finset α) : ∑ x ∈ B, P₁ x - ∑ x ∈ B, P₂ x ≤ l1Dist P₁ P₂ / 2 := by
  rw [l1Dist_eq_two_mul h₁ h₂, mul_div_cancel_left₀ _ two_ne_zero, ← sum_sub_distrib,
    ← sum_sub_distrib]
  calc ∑ x ∈ B, (P₁ x - P₂ x) ≤ ∑ x ∈ B, max (P₁ x - P₂ x) 0 :=
        sum_le_sum fun x _ => le_max_left _ _
    _ ≤ ∑ x, max (P₁ x - P₂ x) 0 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => le_max_right _ _
    _ = ∑ x ∈ univ.filter (fun x => P₂ x < P₁ x), (P₁ x - P₂ x) := by
        rw [sum_filter]
        refine sum_congr rfl fun x _ => ?_
        split_ifs with h
        · exact max_eq_left (sub_pos.2 h).le
        · exact max_eq_right (sub_nonpos.2 (not_lt.1 h))

/-! ### Pinsker's inequality -/

lemma continuousOn_mul_log {c : ℝ} {S : Set ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f S)
    (h : ∀ x ∈ S, f x ≠ 0 ∨ c = 0) : ContinuousOn (fun x => c * log (f x)) S := by
  by_cases hc : c = 0
  · simp only [hc, zero_mul]
    exact continuousOn_const
  · exact continuousOn_const.mul (hf.log fun x hx => (h x hx).resolve_right hc)

lemma mul_log_div_eq_sub {a b : ℝ} (hb : b ≠ 0) : a * log (a / b) = a * log a - a * log b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hb]
    ring

/-- **(11.139)–(11.143) Pinsker's inequality for binary distributions.** For `0 ≤ p ≤ 1` and
`0 < q < 1`, `p log (p/q) + (1 - p) log ((1 - p)/(1 - q)) ≥ 2 (p - q)²`. -/
theorem two_mul_sq_le_binary {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  -- `ψ(q) = -p log q - (1 - p) log (1 - q) - 2 (p - q)²` is minimal at `q = p`.
  set ψ : ℝ → ℝ := fun t => -p * log t - (1 - p) * log (1 - t) - 2 * (p - t) ^ 2
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt ψ (-p / t + (1 - p) / (1 - t) + 4 * (p - t)) t := by
    intro t ht
    have h1t : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    have h1 := (hasDerivAt_log ht.1.ne').const_mul (-p)
    have h2 := (((hasDerivAt_id' t).const_sub 1).log h1t).const_mul (1 - p)
    have h3 := (((hasDerivAt_id' t).const_sub p).pow 2).const_mul 2
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    field_simp
    ring
  have hcont : ∀ a b : ℝ, (∀ t ∈ Icc a b, t ≠ 0 ∨ -p = 0) → (∀ t ∈ Icc a b, 1 - t ≠ 0 ∨ 1 - p = 0) →
      ContinuousOn ψ (Icc a b) := fun a b h₁ h₂ =>
    ((continuousOn_mul_log continuousOn_id h₁).sub (continuousOn_mul_log
      (continuousOn_const.sub continuousOn_id) h₂)).sub (by fun_prop)
  have hdiff : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → DifferentiableOn ℝ ψ (interior (Icc a b)) := by
    intro a b ha hb t ht
    rw [interior_Icc] at ht
    exact (hderiv t ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩).differentiableAt.differentiableWithinAt
  have hpsi : ψ p ≤ ψ q := by
    rcases le_total p q with hpq | hqp
    · refine monotoneOn_of_deriv_nonneg (convex_Icc p q) (hcont p q (fun t ht => ?_)
        fun t ht => Or.inl (by linarith [ht.2])) (hdiff p q hp0 hq1.le) (fun t ht => ?_)
        (left_mem_Icc.2 hpq) (right_mem_Icc.2 hpq) hpq
      · by_cases ht0 : t = 0
        · right
          have : p = 0 := le_antisymm (ht0 ▸ ht.1) hp0
          simp [this]
        · exact Or.inl ht0
      · rw [interior_Icc] at ht
        have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨hp0.trans_lt ht.1, ht.2.trans hq1⟩
        rw [(hderiv t ht').deriv]
        have hpt : p < t := ht.1
        have h4 : 0 < t * (1 - t) := mul_pos ht'.1 (by linarith [ht'.2])
        have : -p / t + (1 - p) / (1 - t) + 4 * (p - t) =
            (t - p) * (1 - 4 * (t * (1 - t))) / (t * (1 - t)) := by
          field_simp [ht'.1.ne', (by linarith [ht'.2] : (1 : ℝ) - t ≠ 0)]
          ring
        rw [this]
        refine div_nonneg (mul_nonneg (by linarith) ?_) h4.le
        nlinarith [sq_nonneg (2 * t - 1)]
    · refine antitoneOn_of_deriv_nonpos (convex_Icc q p) (hcont q p
        (fun t ht => Or.inl (by linarith [ht.1])) fun t ht => ?_) (hdiff q p hq0.le hp1)
        (fun t ht => ?_) (left_mem_Icc.2 hqp) (right_mem_Icc.2 hqp) hqp
      · by_cases ht1 : 1 - t = 0
        · right
          have : p = 1 := le_antisymm hp1 (by linarith [ht.2])
          simp [this]
        · exact Or.inl ht1
      · rw [interior_Icc] at ht
        have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨hq0.trans ht.1, ht.2.trans_le hp1⟩
        rw [(hderiv t ht').deriv]
        have h4 : 0 < t * (1 - t) := mul_pos ht'.1 (by linarith [ht'.2])
        have : -p / t + (1 - p) / (1 - t) + 4 * (p - t) =
            (t - p) * (1 - 4 * (t * (1 - t))) / (t * (1 - t)) := by
          field_simp [ht'.1.ne', (by linarith [ht'.2] : (1 : ℝ) - t ≠ 0)]
          ring
        rw [this]
        refine div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
          (by linarith [ht.2]) ?_) h4.le
        nlinarith [sq_nonneg (2 * t - 1)]
  have hq1' : (1 : ℝ) - q ≠ 0 := by linarith
  rw [mul_log_div_eq_sub hq0.ne', mul_log_div_eq_sub hq1']
  simp only [ψ, sub_self] at hpsi
  nlinarith [hpsi]

open Classical in
/-- **Lemma 11.6.1 (Pinsker's inequality).** `D(P₁‖P₂) ≥ ½ ‖P₁ - P₂‖₁²` (in nats): by the
data-processing inequality for the indicator of `A = {x : P₁(x) > P₂(x)}` and the binary case. -/
theorem pinsker {P₁ P₂ : α → ℝ} (h₁ : IsPMF P₁) (h₂ : IsPMF P₂) (h : AbsCont P₁ P₂) :
    l1Dist P₁ P₂ ^ 2 / 2 ≤ relEntropyReal P₁ P₂ := by
  set A := univ.filter fun x => P₂ x < P₁ x
  set a := ∑ x ∈ A, P₁ x
  set b := ∑ x ∈ A, P₂ x
  have hl1 := l1Dist_eq_two_mul h₁ h₂
  have hD0 := relEntropyReal_nonneg h₁ h₂ h
  have hs₁ := sum_filter_add_sum_filter_not univ (fun x => P₂ x < P₁ x) P₁
  have hs₂ := sum_filter_add_sum_filter_not univ (fun x => P₂ x < P₁ x) P₂
  rw [h₁.sum_eq_one] at hs₁
  rw [h₂.sum_eq_one] at hs₂
  set A' := univ.filter fun x => ¬P₂ x < P₁ x
  -- The data-processing inequality, by the log sum inequality on `A` and its complement.
  have hdp : a * log (a / b) + (1 - a) * log ((1 - a) / (1 - b)) ≤ relEntropyReal P₁ P₂ := by
    have h1 := log_sum_inequality A (fun x _ => h₁.nonneg x) (fun x _ => h₂.nonneg x)
      fun x _ => h x
    have h2 := log_sum_inequality A' (fun x _ => h₁.nonneg x) (fun x _ => h₂.nonneg x)
      fun x _ => h x
    have hsplit := sum_filter_add_sum_filter_not univ (fun x => P₂ x < P₁ x)
      fun x => P₁ x * log (P₁ x / P₂ x)
    rw [show (1 : ℝ) - a = ∑ x ∈ A', P₁ x by linarith,
      show (1 : ℝ) - b = ∑ x ∈ A', P₂ x by linarith, relEntropyReal, ← hsplit]
    exact add_le_add h1 h2
  have hb0 : 0 ≤ b := sum_nonneg fun x _ => h₂.nonneg x
  have hb1 : b ≤ 1 := by linarith [sum_nonneg fun x (_ : x ∈ A') => h₂.nonneg x]
  have ha0 : 0 ≤ a := sum_nonneg fun x _ => h₁.nonneg x
  have ha1 : a ≤ 1 := by linarith [sum_nonneg fun x (_ : x ∈ A') => h₁.nonneg x]
  rcases hb0.eq_or_lt with hb | hb
  · -- `P₂(A) = 0` forces `P₁(A) = 0`.
    have : a = 0 := sum_eq_zero fun x hx =>
      h x ((sum_eq_zero_iff_of_nonneg fun x _ => h₂.nonneg x).1 hb.symm x hx)
    rw [hl1]
    change (2 * (a - b)) ^ 2 / 2 ≤ _
    rw [this, ← hb]
    simpa using hD0
  rcases hb1.eq_or_lt with hb' | hb'
  · have hc : ∑ x ∈ A', P₂ x = 0 := by linarith
    have : ∑ x ∈ A', P₁ x = 0 := sum_eq_zero fun x hx =>
      h x ((sum_eq_zero_iff_of_nonneg fun x _ => h₂.nonneg x).1 hc x hx)
    have ha : a = 1 := by linarith
    rw [hl1]
    change (2 * (a - b)) ^ 2 / 2 ≤ _
    rw [ha, hb']
    simpa using hD0
  have hbin := two_mul_sq_le_binary ha0 ha1 hb hb'
  rw [hl1]
  change (2 * (a - b)) ^ 2 / 2 ≤ _
  nlinarith

end InfoTheory
