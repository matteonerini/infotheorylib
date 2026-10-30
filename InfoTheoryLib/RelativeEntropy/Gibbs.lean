/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RelativeEntropy.InformationInequality

/-!
# The Gibbs variational principle

For a pmf `s ≪ r` and any function `f`, `D(s ‖ r) + ∑ s f ≥ -log ∑ r e^{-f}`, with equality for
the Gibbs (tilted) distribution `g ∝ r e^{-f}`. It describes the minimizers of relative entropy
under linear constraints: the optimal test channels of rate distortion theory (Section 10.7),
the input distributions of the Blahut–Arimoto algorithm (10.147), and the closest distributions
in Sanov's theorem (11.110).

## Main statements

* `neg_log_sum_le_relEntropyReal_add`: the Gibbs inequality.
* `relEntropyReal_gibbs_add`: equality for the Gibbs distribution.
* `sum_mul_sub_log_le_log_sum_exp`: `∑ s (c - log s) ≤ log ∑ e^{c}`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 10.7,
  10.8 and 11.5
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {γ : Type*} [Fintype γ]

/-- **The Gibbs variational principle.** For a pmf `s ≪ r` with `r ≥ 0` and any `f`,
`∑ s log (s/r) + ∑ s f ≥ -log ∑ r e^{-f}`. The difference is `D(s ‖ g)` for the Gibbs
distribution `g ∝ r e^{-f}`. -/
theorem neg_log_sum_le_relEntropyReal_add {s r : γ → ℝ} (hs : IsPMF s) (hr : ∀ a, 0 ≤ r a)
    (hsr : AbsCont s r) (f : γ → ℝ) :
    -log (∑ a, r a * exp (-f a)) ≤ relEntropyReal s r + ∑ a, s a * f a := by
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < s a := by
    by_contra h
    push Not at h
    have : ∑ a, s a ≤ 0 := sum_nonpos fun a _ => h a
    linarith [hs.sum_eq_one]
  set Z := ∑ a, r a * exp (-f a)
  have hra₀ : 0 < r a₀ := lt_of_le_of_ne (hr a₀) fun h => ha₀.ne' (hsr a₀ h.symm)
  have hZ : 0 < Z := lt_of_lt_of_le (mul_pos hra₀ (exp_pos _))
    (single_le_sum (f := fun a => r a * exp (-f a)) (fun a _ => mul_nonneg (hr a) (exp_pos _).le)
      (mem_univ a₀))
  set g := fun a => r a * exp (-f a) / Z
  have hg : IsPMF g := ⟨fun a => div_nonneg (mul_nonneg (hr a) (exp_pos _).le) hZ.le, by
    simp only [g, ← sum_div]; exact div_self hZ.ne'⟩
  have hsg : AbsCont s g := fun a h => by
    rcases mul_eq_zero.1 (div_eq_zero_iff.1 h |>.resolve_right hZ.ne') with h | h
    · exact hsr a h
    · exact absurd h (exp_pos _).ne'
  have hD := relEntropyReal_nonneg hs hg hsg
  have hterm : ∀ a, s a * log (s a / g a) =
      s a * log (s a / r a) + s a * f a + s a * log Z := fun a => by
    rcases eq_or_ne (s a) 0 with h0 | h0
    · simp [h0]
    have hra : r a ≠ 0 := fun h => h0 (hsr a h)
    simp only [g]
    rw [← mul_add, ← mul_add, log_div h0 (div_ne_zero (mul_ne_zero hra (exp_pos _).ne') hZ.ne'),
      log_div (mul_ne_zero hra (exp_pos _).ne') hZ.ne', log_mul hra (exp_pos _).ne', log_exp,
      log_div h0 hra]
    ring
  have : relEntropyReal s g = relEntropyReal s r + ∑ a, s a * f a + log Z := by
    rw [relEntropyReal, sum_congr rfl fun a _ => hterm a, sum_add_distrib, sum_add_distrib,
      ← sum_mul, hs.sum_eq_one, one_mul]
    rfl
  linarith

/-- **The Gibbs distribution attains the bound.** For `g = r e^{-f}/Z` with `Z = ∑ r e^{-f} > 0`,
`∑ g log (g/r) + ∑ g f = -log Z`. -/
theorem relEntropyReal_gibbs_add {r : γ → ℝ} (f : γ → ℝ)
    (hZ : 0 < ∑ a, r a * exp (-f a)) :
    relEntropyReal (fun a => r a * exp (-f a) / ∑ b, r b * exp (-f b)) r +
        ∑ a, r a * exp (-f a) / (∑ b, r b * exp (-f b)) * f a =
      -log (∑ a, r a * exp (-f a)) := by
  set Z := ∑ a, r a * exp (-f a)
  have hterm : ∀ a, r a * exp (-f a) / Z * log (r a * exp (-f a) / Z / r a) +
      r a * exp (-f a) / Z * f a = r a * exp (-f a) / Z * -log Z := fun a => by
    rcases eq_or_ne (r a) 0 with h0 | h0
    · simp [h0]
    rw [← mul_add]
    congr 1
    have : r a * exp (-f a) / Z / r a = exp (-f a) / Z := by field_simp
    rw [this, log_div (exp_pos _).ne' hZ.ne', log_exp]
    ring
  rw [relEntropyReal, ← sum_add_distrib, sum_congr rfl fun a _ => hterm a, ← sum_mul, ← sum_div,
    div_self hZ.ne', one_mul]

/-- **(10.147)** For any weights `c`, `∑ₓ s(x) (c(x) - log s(x)) ≤ log ∑ₓ e^{c(x)}` for every pmf
`s`, with equality for `s ∝ e^{c}`. With `c(x) = ∑_y p(y|x) log q(x|y)`, this is the best input
distribution `r(x) ∝ ∏_y q(x|y)^{p(y|x)}` for a fixed backward channel `q(x|y)`. -/
theorem sum_mul_sub_log_le_log_sum_exp {s : γ → ℝ} (hs : IsPMF s) (c : γ → ℝ) :
    ∑ a, s a * (c a - log (s a)) ≤ log (∑ a, exp (c a)) := by
  have h := neg_log_sum_le_relEntropyReal_add hs (r := fun _ => 1) (fun _ => zero_le_one)
    (fun _ h => absurd h one_ne_zero) (fun a => -c a)
  simp only [neg_neg, one_mul, div_one, relEntropyReal] at h
  have : ∑ a, s a * (c a - log (s a)) = -(∑ a, s a * log (s a) + ∑ a, s a * -c a) := by
    rw [← sum_add_distrib, ← sum_neg_distrib]
    exact sum_congr rfl fun a _ => by ring
  linarith

end InfoTheory
