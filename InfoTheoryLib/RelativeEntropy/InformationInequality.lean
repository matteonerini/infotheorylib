/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.Log
public import InfoTheoryLib.RelativeEntropy.Basic

/-!
# The information inequality

## Main statements

* `relEntropyReal_nonneg`, `relEntropy_nonneg`: `D(p ‖ q) ≥ 0`.
* `relEntropyReal_eq_zero_iff`, `relEntropy_eq_zero_iff`: `D(p ‖ q) = 0` iff `p = q`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.6.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Theorem 2.6.3 (Information inequality).** `D(p‖q) ≥ 0` (for `p ≪ q`, i.e. whenever the
relative entropy is finite). -/
theorem relEntropyReal_nonneg {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q) (hpq : AbsCont p q) :
    0 ≤ relEntropyReal p q := by
  have : ∑ x, (p x - q x) ≤ relEntropyReal p q :=
    sum_le_sum fun x _ => sub_le_mul_log_div (hp.nonneg x) (hq.nonneg x) (hpq x)
  rwa [sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one, sub_self] at this

/-- **Theorem 2.6.3 (Information inequality, equality case).** `D(p‖q) = 0` iff `p(x) = q(x)`
for all `x`. -/
theorem relEntropyReal_eq_zero_iff {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q)
    (hpq : AbsCont p q) : relEntropyReal p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hsum : ∑ x, (p x * log (p x / q x) - (p x - q x)) = 0 := by
      rw [sum_sub_distrib, ← relEntropyReal, h, sum_sub_distrib, hp.sum_eq_one, hq.sum_eq_one]
      ring
    have hnn : ∀ x ∈ univ, 0 ≤ p x * log (p x / q x) - (p x - q x) := fun x _ =>
      sub_nonneg.2 (sub_le_mul_log_div (hp.nonneg x) (hq.nonneg x) (hpq x))
    have h0 := (sum_eq_zero_iff_of_nonneg hnn).1 hsum
    funext x
    exact (mul_log_div_eq_sub_iff (hp.nonneg x) (hq.nonneg x) (hpq x)).1
      (by linarith [h0 x (mem_univ x)])
  · rintro rfl; exact relEntropyReal_self p

/-- **Theorem 2.6.3 (Information inequality)** for the extended relative entropy
`D(p‖q) ∈ [0, ∞]`: `D(p‖q) ≥ 0`. -/
theorem relEntropy_nonneg {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q) : 0 ≤ relEntropy p q := by
  unfold relEntropy
  split_ifs with h
  · exact EReal.coe_nonneg.2 (relEntropyReal_nonneg hp hq h)
  · exact le_top

/-- **Theorem 2.6.3 (Information inequality)** for the extended relative entropy:
`D(p‖q) = 0` iff `p = q`. -/
theorem relEntropy_eq_zero_iff {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q) :
    relEntropy p q = 0 ↔ p = q := by
  unfold relEntropy
  split_ifs with h
  · rw [EReal.coe_eq_zero]; exact relEntropyReal_eq_zero_iff hp hq h
  · simp only [EReal.top_ne_zero, false_iff]
    rintro rfl; exact h fun x hx => hx

lemma relEntropy_ne_bot {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q) : relEntropy p q ≠ ⊥ :=
  ne_bot_of_le_ne_bot EReal.zero_ne_bot (relEntropy_nonneg hp hq)

end InfoTheory
