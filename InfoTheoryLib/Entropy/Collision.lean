/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RelativeEntropy.Basic
public import InfoTheoryLib.Probability.Jensen
public import InfoTheoryLib.Probability.Independence
public import InfoTheoryLib.Probability.Event

/-!
# The probability that two independent random variables agree

For independent random variables `X ∼ p` and `X' ∼ r` with the same alphabet,
`Pr(X = X') = ∑ₓ p(x) r(x)`. By Jensen's inequality for the convex function `eᵗ`, this
probability is at least `e^{-H(p) - D(p‖r)}`. For i.i.d. `X` and `X'` it is at least `e^{-H(X)}`,
with equality iff `X` is uniform on its support. The book states these bounds in bits, with
`2^{-H}`; in nats they read `e^{-H}`.

## Main statements

* `prob_eq_of_indepRV`: (2.145), `Pr(X = X') = ∑ₓ p(x) r(x)` for independent `X` and `X'`.
* `exp_neg_entropy_sub_relEntropy_le`: Corollary (2.149)–(2.150) of Lemma 2.10.1,
  `∑ₓ p(x) r(x) ≥ e^{-H(p) - D(p‖r)}`.
* `exp_neg_entropy_le_sum_sq`, `sum_sq_eq_exp_neg_entropy_iff`: Lemma 2.10.1,
  `∑ₓ p(x)² ≥ e^{-H(p)}`, with equality iff `p` is constant on its support.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.10
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α : Type*} [Fintype Ω] [Fintype α]

open Classical in
/-- **(2.145)** If `X` and `X'` are independent, `Pr(X = X') = ∑ₓ p(x) r(x)`, where `p` and `r`
are the laws of `X` and `X'`. -/
theorem prob_eq_of_indepRV {μ : Ω → ℝ} {X X' : Ω → α} (h : IndepRV μ X X') :
    prob μ (univ.filter fun ω => X ω = X' ω) = ∑ x, dist μ X x * dist μ X' x := by
  rw [sum_congr rfl fun x _ => (h x x).symm]
  simp only [dist, prob, sum_filter, pair_apply, Prod.ext_iff]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hω : X ω = X' ω
  · simp [hω]
  · simp only [hω, ↓reduceIte]
    refine (sum_eq_zero fun x _ => ?_).symm
    split
    · next hx => exact absurd (hx.1.trans hx.2.symm) hω
    · rfl

/-- `-H(p) - D(p‖r) = ∑ₓ p(x) log r(x)` when `p ≪ r`. -/
lemma neg_entropy_sub_relEntropyReal {p r : α → ℝ} (hpr : AbsCont p r) :
    -entropy p - relEntropyReal p r = ∑ x, p x * log (r x) := by
  rw [entropy, relEntropyReal, neg_neg, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (p x) 0 with h | h
  · simp [h]
  · rw [log_div h fun hr => h (hpr x hr)]
    ring

/-- **Corollary (2.149)–(2.150) of Lemma 2.10.1.** If `X ∼ p` and `X' ∼ r` are independent, then
`Pr(X = X') = ∑ₓ p(x) r(x) ≥ e^{-H(p) - D(p‖r)}` (the book's `2^{-H(p) - D(p‖r)}` in bits).
Exchanging `p` and `r` gives `Pr(X = X') ≥ e^{-H(r) - D(r‖p)}`. -/
theorem exp_neg_entropy_sub_relEntropy_le {p r : α → ℝ} (hp : IsPMF p) (hr : ∀ x, 0 ≤ r x)
    (hpr : AbsCont p r) : exp (-entropy p - relEntropyReal p r) ≤ ∑ x, p x * r x := by
  -- Jensen's inequality for `eᵗ` and the random variable `log r(X)`, `X ∼ p`.
  have h := jensen hp (s := Set.univ) convexOn_exp (X := fun x => log (r x)) fun _ => trivial
  have hE : expect p (fun x => log (r x)) = -entropy p - relEntropyReal p r := by
    rw [neg_entropy_sub_relEntropyReal hpr, expect]
    exact sum_congr rfl fun x _ => mul_comm _ _
  have hEf : expect p (exp ∘ fun x => log (r x)) = ∑ x, p x * r x := by
    rw [expect]
    refine sum_congr rfl fun x _ => ?_
    rcases eq_or_ne (p x) 0 with h0 | h0
    · simp [h0]
    · have : 0 < r x := lt_of_le_of_ne (hr x) fun h' => h0 (hpr x h'.symm)
      simp [exp_log this, mul_comm]
  rwa [hE, hEf] at h

/-- **Lemma 2.10.1.** If `X` and `X'` are i.i.d. with pmf `p`, then
`Pr(X = X') = ∑ₓ p(x)² ≥ e^{-H(X)}` (the book's `2^{-H(X)}` in bits). -/
theorem exp_neg_entropy_le_sum_sq {p : α → ℝ} (hp : IsPMF p) :
    exp (-entropy p) ≤ ∑ x, p x ^ 2 := by
  have h := exp_neg_entropy_sub_relEntropy_le hp hp.nonneg fun _ h => h
  rw [relEntropyReal_self, sub_zero] at h
  simpa [sq] using h

/-- **Lemma 2.10.1 (equality case).** `∑ₓ p(x)² = e^{-H(X)}` iff `X` is uniformly distributed on
its support, that is, `p` takes the same value at all the points where it is positive. -/
theorem sum_sq_eq_exp_neg_entropy_iff {p : α → ℝ} (hp : IsPMF p) :
    ∑ x, p x ^ 2 = exp (-entropy p) ↔ ∀ x y, p x ≠ 0 → p y ≠ 0 → p x = p y := by
  set X : α → ℝ := fun x => log (p x)
  have key := jensen_eq_iff hp (s := Set.univ) strictConvexOn_exp (X := X) fun _ => trivial
  have hE : expect p X = -entropy p := by
    rw [← sub_zero (-entropy p), ← relEntropyReal_self p,
      neg_entropy_sub_relEntropyReal fun _ h => h, expect]
    exact sum_congr rfl fun x _ => mul_comm _ _
  have hEf : expect p (exp ∘ X) = ∑ x, p x ^ 2 := by
    rw [expect]
    refine sum_congr rfl fun x _ => ?_
    rcases eq_or_ne (p x) 0 with h0 | h0
    · simp [X, h0]
    · simp [X, exp_log (lt_of_le_of_ne (hp.nonneg x) (Ne.symm h0)), sq]
  rw [hEf, hE] at key
  rw [key]
  have hpos : ∀ x, p x ≠ 0 → 0 < p x := fun x h => lt_of_le_of_ne (hp.nonneg x) (Ne.symm h)
  constructor
  · intro h x y hx hy
    have e1 := h x hx
    have e2 := h y hy
    exact log_injOn_pos (hpos x hx) (hpos y hy) (e1.trans e2.symm)
  · intro h x hx
    -- `p` is constant, equal to `p x`, on its support, so `-H(p) = ∑ p log p = log p(x)`.
    have hsum : -entropy p = ∑ y, p y * log (p x) := by
      rw [entropy, neg_neg]
      refine sum_congr rfl fun y _ => ?_
      rcases eq_or_ne (p y) 0 with h0 | h0
      · simp [h0]
      · rw [h y x h0 hx]
    rw [hsum, ← sum_mul, hp.sum_eq_one, one_mul]

end InfoTheory
