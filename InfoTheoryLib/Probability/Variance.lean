/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Event

/-!
# Expectation, variance, and the inequalities of Markov and Chebyshev

## Main definitions

* `variance p f`: the variance `Var f(X) = E (f(X) - E f(X))²` of `f(X)` for `X ∼ p`.

## Main statements

* `expect_add`, `expect_const_mul`, `expect_sum`: linearity of expectation.
* `variance_eq`: `Var f(X) = E f(X)² - (E f(X))²`.
* `markov_ineq`: Markov's inequality `Pr{f(X) ≥ t} ≤ E f(X) / t` for `f ≥ 0` and `t > 0`.
* `chebyshev_ineq`: Chebyshev's inequality `Pr{|f(X) - E f(X)| ≥ ε} ≤ Var f(X) / ε²`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Problem 3.1
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### Linearity of expectation -/

lemma expect_add (p f g : α → ℝ) :
    expect p (fun x => f x + g x) = expect p f + expect p g := by
  simp [expect, add_mul, sum_add_distrib]

lemma expect_sub (p f g : α → ℝ) :
    expect p (fun x => f x - g x) = expect p f - expect p g := by
  simp [expect, sub_mul, sum_sub_distrib]

lemma expect_const_mul (p f : α → ℝ) (c : ℝ) :
    expect p (fun x => c * f x) = c * expect p f := by
  simp [expect, mul_sum, mul_assoc]

lemma expect_neg (p f : α → ℝ) : expect p (fun x => -f x) = -expect p f := by
  simp [expect, sum_neg_distrib]

lemma expect_const {p : α → ℝ} (hp : IsPMF p) (c : ℝ) : expect p (fun _ => c) = c := by
  simp [expect, ← mul_sum, hp.sum_eq_one]

lemma expect_sum {ι : Type*} (p : α → ℝ) (s : Finset ι) (F : ι → α → ℝ) :
    expect p (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, expect p (F i) := by
  simp only [expect, sum_mul]
  exact sum_comm

lemma expect_nonneg {p f : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ expect p f :=
  sum_nonneg fun x _ => mul_nonneg (hf x) (hp x)

lemma expect_mono {p f g : α → ℝ} (hp : ∀ x, 0 ≤ p x) (h : ∀ x, f x ≤ g x) :
    expect p f ≤ expect p g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (h x) (hp x)

/-! ### Variance -/

/-- The variance `Var f(X) = E (f(X) - E f(X))²` of `f(X)` for `X ∼ p`. -/
def variance (p f : α → ℝ) : ℝ := expect p (fun x => (f x - expect p f) ^ 2)

lemma variance_nonneg {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (f : α → ℝ) : 0 ≤ variance p f :=
  expect_nonneg hp fun _ => sq_nonneg _

/-- `Var f(X) = E f(X)² - (E f(X))²`. -/
lemma variance_eq {p : α → ℝ} (hp : IsPMF p) (f : α → ℝ) :
    variance p f = expect p (fun x => f x ^ 2) - expect p f ^ 2 := by
  have h : ∀ x, (f x - expect p f) ^ 2 =
      f x ^ 2 + (-(2 * expect p f) * f x + expect p f ^ 2) := fun x => by ring
  rw [variance, funext h, expect_add, expect_add, expect_const_mul, expect_const hp]
  ring

/-! ### The inequalities of Markov and Chebyshev -/

/-- **Markov's inequality** (Problem 3.1(a)). If `f ≥ 0` and `t > 0`, then
`Pr{f(X) ≥ t} ≤ E f(X) / t`. -/
theorem markov_ineq {p f : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hf : ∀ x, 0 ≤ f x) {t : ℝ}
    (ht : 0 < t) : prob p (univ.filter fun x => t ≤ f x) ≤ expect p f / t := by
  rw [le_div_iff₀ ht, mul_comm, prob, mul_sum]
  calc ∑ x ∈ univ.filter (fun x => t ≤ f x), t * p x
      ≤ ∑ x ∈ univ.filter (fun x => t ≤ f x), f x * p x :=
        sum_le_sum fun x hx => mul_le_mul_of_nonneg_right (mem_filter.1 hx).2 (hp x)
    _ ≤ expect p f := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        fun x _ _ => mul_nonneg (hf x) (hp x)

/-- **Chebyshev's inequality** (Problem 3.1(b)). For `ε > 0`,
`Pr{|f(X) - E f(X)| ≥ ε} ≤ Var f(X) / ε²`. -/
theorem chebyshev_ineq {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    prob p (univ.filter fun x => ε ≤ |f x - expect p f|) ≤ variance p f / ε ^ 2 := by
  refine (prob_mono hp ?_).trans (markov_ineq hp (fun x => sq_nonneg (f x - expect p f))
    (pow_pos hε 2))
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  calc ε ^ 2 ≤ |f x - expect p f| ^ 2 := pow_le_pow_left₀ hε.le hx 2
    _ = (f x - expect p f) ^ 2 := sq_abs _

end InfoTheory
