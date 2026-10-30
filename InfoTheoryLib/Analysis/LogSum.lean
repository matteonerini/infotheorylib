/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.Log

/-!
# The log sum inequality

## Main statements

* `log_sum_inequality`: for non-negative `a₁, …, aₙ` and `b₁, …, bₙ`,
  `(∑ aᵢ) log ((∑ aᵢ)/(∑ bᵢ)) ≤ ∑ aᵢ log (aᵢ/bᵢ)`.
* `log_sum_inequality_eq_iff`: equality holds iff `aᵢ = c bᵢ` for a constant `c`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.7.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Termwise form of the log sum inequality: `a log (a/b) - a log c ≥ a - c b`, with equality
iff `a = c b`. -/
lemma log_sum_term {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) (hc : 0 < c) :
    a - c * b ≤ a * log (a / b) - a * log c ∧
      (a * log (a / b) - a * log c = a - c * b ↔ a = c * b) := by
  have hcb : c * b = 0 → a = 0 := fun h => hab ((mul_eq_zero.1 h).resolve_left hc.ne')
  have e : a * log (a / b) - a * log c = a * log (a / (c * b)) := by
    rcases ha.eq_or_lt with rfl | ha'
    · simp
    · have hb' : 0 < b := hb.lt_of_ne fun h => ha'.ne' (hab h.symm)
      rw [← mul_sub, ← log_div (by positivity) hc.ne', div_div, mul_comm b c]
  rw [e]
  exact ⟨sub_le_mul_log_div ha (by positivity) hcb,
    mul_log_div_eq_sub_iff ha (by positivity) hcb⟩

/-- **Theorem 2.7.1 (Log sum inequality).** For non-negative `a₁, …, aₙ` and `b₁, …, bₙ`,
`∑ aᵢ log (aᵢ/bᵢ) ≥ (∑ aᵢ) log ((∑ aᵢ)/(∑ bᵢ))`.
We use the conventions `0 log 0 = 0` and `0 log (0/0) = 0` (automatic), and assume
`bᵢ = 0 → aᵢ = 0`. Otherwise some term is `aᵢ log (aᵢ/0) = ∞`, and the inequality is trivial. -/
theorem log_sum_inequality {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * log (a i / b i) := by
  set A := ∑ i ∈ s, a i
  set B := ∑ i ∈ s, b i
  have hA : 0 ≤ A := sum_nonneg ha
  rcases hA.eq_or_lt with hA0 | hA0
  · rw [← hA0, zero_mul]
    have : ∀ i ∈ s, a i = 0 := (sum_eq_zero_iff_of_nonneg ha).1 hA0.symm
    rw [sum_eq_zero fun i hi => by rw [this i hi, zero_mul]]
  · have hB0 : 0 < B := by
      obtain ⟨i, hi, hai⟩ : ∃ i ∈ s, 0 < a i := by
        by_contra! h
        exact hA0.ne' (sum_eq_zero fun i hi => le_antisymm (h i hi) (ha i hi))
      exact lt_of_lt_of_le ((hb i hi).lt_of_ne fun h => hai.ne' (hab i hi h.symm))
        (single_le_sum hb hi)
    have hc : 0 < A / B := div_pos hA0 hB0
    have key := sum_le_sum fun i hi => (log_sum_term (ha i hi) (hb i hi) (hab i hi) hc).1
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, div_mul_cancel₀ _ hB0.ne',
      sub_self] at key
    linarith

/-- **Theorem 2.7.1 (Log sum inequality, equality case).** Equality holds iff `aᵢ/bᵢ` is
constant, i.e. `aᵢ = c bᵢ` for some constant `c`. -/
theorem log_sum_inequality_eq_iff {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) = ∑ i ∈ s, a i * log (a i / b i) ↔
      ∃ c : ℝ, ∀ i ∈ s, a i = c * b i := by
  set A := ∑ i ∈ s, a i
  set B := ∑ i ∈ s, b i
  have hA : 0 ≤ A := sum_nonneg ha
  rcases hA.eq_or_lt with hA0 | hA0
  · have h0 : ∀ i ∈ s, a i = 0 := (sum_eq_zero_iff_of_nonneg ha).1 hA0.symm
    rw [← hA0, zero_mul, sum_eq_zero fun i hi => by rw [h0 i hi, zero_mul]]
    exact ⟨fun _ => ⟨0, fun i hi => by rw [h0 i hi, zero_mul]⟩, fun _ => rfl⟩
  · have hB0 : 0 < B := by
      obtain ⟨i, hi, hai⟩ : ∃ i ∈ s, 0 < a i := by
        by_contra! h
        exact hA0.ne' (sum_eq_zero fun i hi => le_antisymm (h i hi) (ha i hi))
      exact lt_of_lt_of_le ((hb i hi).lt_of_ne fun h => hai.ne' (hab i hi h.symm))
        (single_le_sum hb hi)
    have hc : 0 < A / B := div_pos hA0 hB0
    have hterm := fun i hi => log_sum_term (ha i hi) (hb i hi) (hab i hi) hc
    have hsum : ∑ i ∈ s, (a i * log (a i / b i) - a i * log (A / B) - (a i - A / B * b i)) =
        ∑ i ∈ s, a i * log (a i / b i) - A * log (A / B) := by
      rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul,
        div_mul_cancel₀ _ hB0.ne']
      ring
    have hnn : ∀ i ∈ s, 0 ≤ a i * log (a i / b i) - a i * log (A / B) - (a i - A / B * b i) :=
      fun i hi => sub_nonneg.2 (hterm i hi).1
    constructor
    · intro h
      refine ⟨A / B, fun i hi => (hterm i hi).2.1 ?_⟩
      have h0 := (sum_eq_zero_iff_of_nonneg hnn).1 (by rw [hsum, h, sub_self])
      linarith [h0 i hi]
    · rintro ⟨c, hc'⟩
      have hcAB : c = A / B := by
        have : A = c * B := by rw [mul_sum]; exact sum_congr rfl hc'
        field_simp; linarith
      subst hcAB
      have h0 : ∑ i ∈ s, (a i * log (a i / b i) - a i * log (A / B) - (a i - A / B * b i)) = 0 :=
        sum_eq_zero fun i hi => by rw [(hterm i hi).2.2 (hc' i hi)]; ring
      rw [hsum] at h0
      linarith

/-- Pointwise two-term log sum inequality used for the convexity of `D`. -/
lemma log_sum_two {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (h₁ : b₁ = 0 → a₁ = 0) (h₂ : b₂ = 0 → a₂ = 0) :
    (a₁ + a₂) * log ((a₁ + a₂) / (b₁ + b₂)) ≤ a₁ * log (a₁ / b₁) + a₂ * log (a₂ / b₂) := by
  have := log_sum_inequality (univ : Finset (Fin 2)) (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (fun i _ => by fin_cases i <;> simpa) (fun i _ => by fin_cases i <;> simpa)
    (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using this

end InfoTheory
