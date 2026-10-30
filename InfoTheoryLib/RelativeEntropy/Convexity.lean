/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Analysis.LogSum
public import InfoTheoryLib.RelativeEntropy.InformationInequality

/-!
# Convexity of relative entropy

## Main statements

* `relEntropyReal_convex_pair`, `relEntropy_convex_pair`: `D(p ‖ q)` is convex in the pair
  `(p, q)`.
* `relEntropyReal_convexOn`: the same statement as a `ConvexOn`.
* `relEntropyReal_nonneg'`: a second proof of the information inequality, from the log sum
  inequality.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.7.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Theorem 2.6.3, reproved with the log sum inequality (2.102)–(2.104).** -/
theorem relEntropyReal_nonneg' {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q)
    (hpq : AbsCont p q) : 0 ≤ relEntropyReal p q := by
  have := log_sum_inequality univ (fun x _ => hp.nonneg x) (fun x _ => hq.nonneg x)
    (fun x _ => hpq x)
  rwa [hp.sum_eq_one, hq.sum_eq_one, div_one, log_one, mul_zero] at this

/-- **Theorem 2.7.2.** `D(p‖q)` is convex in the pair `(p, q)`:
`D(λp₁ + (1-λ)p₂ ‖ λq₁ + (1-λ)q₂) ≤ λ D(p₁‖q₁) + (1-λ) D(p₂‖q₂)` for `0 ≤ λ ≤ 1` (2.105). -/
theorem relEntropyReal_convex_pair {p₁ q₁ p₂ q₂ : α → ℝ} (hp₁ : ∀ x, 0 ≤ p₁ x)
    (hq₁ : ∀ x, 0 ≤ q₁ x) (hp₂ : ∀ x, 0 ≤ p₂ x) (hq₂ : ∀ x, 0 ≤ q₂ x) (h₁ : AbsCont p₁ q₁)
    (h₂ : AbsCont p₂ q₂) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    relEntropyReal (fun x => t * p₁ x + (1 - t) * p₂ x) (fun x => t * q₁ x + (1 - t) * q₂ x) ≤
      t * relEntropyReal p₁ q₁ + (1 - t) * relEntropyReal p₂ q₂ := by
  have ht1' : 0 ≤ 1 - t := by linarith
  rw [relEntropyReal, relEntropyReal, relEntropyReal, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  have := log_sum_two (mul_nonneg ht0 (hp₁ x)) (mul_nonneg ht1' (hp₂ x))
    (mul_nonneg ht0 (hq₁ x)) (mul_nonneg ht1' (hq₂ x))
    (fun h => by
      rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul]
      · rw [h₁ x h, mul_zero])
    (fun h => by
      rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul]
      · rw [h₂ x h, mul_zero])
  rwa [mul_log_scale, mul_log_scale] at this

/-- **Theorem 2.7.2** as convexity (`ConvexOn`) of `(p, q) ↦ D(p‖q)` on pairs of pmfs with
`p ≪ q`. -/
theorem relEntropyReal_convexOn :
    ConvexOn ℝ {pq : (α → ℝ) × (α → ℝ) | IsPMF pq.1 ∧ IsPMF pq.2 ∧ AbsCont pq.1 pq.2}
      (fun pq => relEntropyReal pq.1 pq.2) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p₁, q₁⟩ ⟨hp₁, hq₁, h₁⟩ ⟨p₂, q₂⟩ ⟨hp₂, hq₂, h₂⟩ s t hs ht hst
    exact ⟨hp₁.mix hp₂ hs ht hst, hq₁.mix hq₂ hs ht hst,
      AbsCont.mix hq₁.nonneg hq₂.nonneg h₁ h₂ hs ht⟩
  · rintro ⟨p₁, q₁⟩ ⟨hp₁, hq₁, h₁⟩ ⟨p₂, q₂⟩ ⟨hp₂, hq₂, h₂⟩ s t hs ht hst
    obtain rfl : t = 1 - s := by linarith
    have := relEntropyReal_convex_pair hp₁.nonneg hq₁.nonneg hp₂.nonneg hq₂.nonneg h₁ h₂ hs
      (by linarith)
    have e : ∀ a b : α → ℝ, s • a + (1 - s) • b = fun x => s * a x + (1 - s) * b x :=
      fun a b => by funext x; simp [smul_eq_mul]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [e p₁ p₂, e q₁ q₂]
    exact this

/-- **Theorem 2.7.2** for the extended relative entropy `D(p‖q) ∈ [0, ∞]` (with the convention
`p log (p/0) = ∞`): `D(λp₁ + (1-λ)p₂ ‖ λq₁ + (1-λ)q₂) ≤ λ D(p₁‖q₁) + (1-λ) D(p₂‖q₂)`. -/
theorem relEntropy_convex_pair {p₁ q₁ p₂ q₂ : α → ℝ} (hp₁ : IsPMF p₁) (hq₁ : IsPMF q₁)
    (hp₂ : IsPMF p₂) (hq₂ : IsPMF q₂) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    relEntropy (fun x => t * p₁ x + (1 - t) * p₂ x) (fun x => t * q₁ x + (1 - t) * q₂ x) ≤
      (t : EReal) * relEntropy p₁ q₁ + ((1 - t : ℝ) : EReal) * relEntropy p₂ q₂ := by
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp
  have ht1'' : 0 < 1 - t := by linarith
  have hmixp := hp₁.mix hp₂ ht0 ht1''.le (by ring)
  have hmixq := hq₁.mix hq₂ ht0 ht1''.le (by ring)
  have hn₁ : ((1 - t : ℝ) : EReal) * relEntropy p₂ q₂ ≠ ⊥ := by
    have := EReal.mul_nonneg (EReal.coe_nonneg.2 ht1''.le) (relEntropy_nonneg hp₂ hq₂)
    exact ne_bot_of_le_ne_bot EReal.zero_ne_bot this
  have hn₂ : (t : EReal) * relEntropy p₁ q₁ ≠ ⊥ := by
    have := EReal.mul_nonneg (EReal.coe_nonneg.2 ht0) (relEntropy_nonneg hp₁ hq₁)
    exact ne_bot_of_le_ne_bot EReal.zero_ne_bot this
  by_cases h₁ : AbsCont p₁ q₁
  · by_cases h₂ : AbsCont p₂ q₂
    · have hmix : AbsCont (fun x => t * p₁ x + (1 - t) * p₂ x)
          (fun x => t * q₁ x + (1 - t) * q₂ x) := by
        have := AbsCont.mix hq₁.nonneg hq₂.nonneg h₁ h₂ ht0 ht1''.le
        intro x hx
        exact this x (by simpa [smul_eq_mul] using hx) |>.symm ▸ by simp [smul_eq_mul]
      rw [relEntropy_of_absCont hmix, relEntropy_of_absCont h₁, relEntropy_of_absCont h₂,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      exact relEntropyReal_convex_pair hp₁.nonneg hq₁.nonneg hp₂.nonneg hq₂.nonneg h₁ h₂
        ht0 ht1
    · rw [relEntropy_eq_top_iff.2 h₂, EReal.coe_mul_top_of_pos ht1'', EReal.add_top_of_ne_bot hn₂]
      exact le_top
  · rw [relEntropy_eq_top_iff.2 h₁, EReal.coe_mul_top_of_pos ht0', EReal.top_add_of_ne_bot hn₁]
    exact le_top

end InfoTheory
