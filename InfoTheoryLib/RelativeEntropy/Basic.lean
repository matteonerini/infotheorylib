/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Basic

/-!
# Relative entropy (Kullback–Leibler divergence)

## Main definitions

* `relEntropyReal p q`: the real number `∑ₓ p(x) log (p(x) / q(x))`.
* `relEntropy p q`: the relative entropy `D(p ‖ q) ∈ [0, ∞]`, as an `EReal`. It is `⊤` unless
  `p ≪ q`, in which case it equals `relEntropyReal p q`.

## Main statements

* `relEntropy_eq_top_iff`: `D(p ‖ q) = ∞` iff `p` is not absolutely continuous w.r.t. `q`.
* `relEntropyReal_uniform`: `D(p ‖ u) = log |𝒳| - H(p)` for the uniform distribution `u`.

## Implementation notes

The conventions `0 log (0 / q) = 0` and `p log (p / 0) = ∞` are built into `relEntropy`. Most
results are stated for `relEntropyReal` under the hypothesis `AbsCont p q`, which is exactly the
case in which `D(p ‖ q)` is finite.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- The sum `∑ₓ p(x) log (p(x) / q(x))`, computed with real logarithms. It agrees with the
relative entropy `D(p‖q)` whenever `p ≪ q`. -/
def relEntropyReal (p q : α → ℝ) : ℝ := ∑ x, p x * log (p x / q x)

open Classical in
/-- **Definition (2.26).** The relative entropy (Kullback–Leibler distance)
`D(p‖q) = ∑ₓ p(x) log (p(x) / q(x))`, with the conventions `0 log (0/q) = 0` and
`p log (p/0) = ∞`. It takes values in `[0, ∞]`; we use `EReal`. -/
def relEntropy (p q : α → ℝ) : EReal := if AbsCont p q then (relEntropyReal p q : EReal) else ⊤

lemma relEntropy_of_absCont {p q : α → ℝ} (h : AbsCont p q) :
    relEntropy p q = (relEntropyReal p q : EReal) := by
  simp [relEntropy, h]

/-- The convention `p log (p/0) = ∞`: a single point with `p(x) > 0 = q(x)` makes `D(p‖q) = ∞`. -/
lemma relEntropy_eq_top {p q : α → ℝ} {x : α} (hp : p x ≠ 0) (hq : q x = 0) :
    relEntropy p q = ⊤ := by
  unfold relEntropy
  split_ifs with h
  · exact absurd (h x hq) hp
  · rfl

lemma relEntropy_eq_top_iff {p q : α → ℝ} : relEntropy p q = ⊤ ↔ ¬ AbsCont p q := by
  unfold relEntropy; split_ifs with h <;> simp [h]

/-- The convention `0 log (0/q) = 0`: points with `p(x) = 0` do not contribute. -/
lemma relEntropyReal_eq_sum_support (p q : α → ℝ) :
    relEntropyReal p q = ∑ x with p x ≠ 0, p x * log (p x / q x) := by
  rw [relEntropyReal, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not.1 h, zero_mul]

/-- (2.27) `D(p‖q) = E_p log (p(X) / q(X))`. -/
lemma relEntropyReal_eq_expect (p q : α → ℝ) :
    relEntropyReal p q = expect p (fun x => log (p x / q x)) := by
  simp [relEntropyReal, expect, mul_comm]

lemma relEntropyReal_self (p : α → ℝ) : relEntropyReal p p = 0 := by
  simp [relEntropyReal]

lemma relEntropyReal_comp_equiv (e : β ≃ α) (p q : α → ℝ) :
    relEntropyReal (p ∘ e) (q ∘ e) = relEntropyReal p q := by
  simp only [relEntropyReal, Function.comp_apply]
  exact e.sum_comp (fun a => p a * log (p a / q a))

/-- (2.93) and Summary property 4: `D(p‖u) = log |𝒳| - H(p)`. -/
theorem relEntropyReal_uniform {p : α → ℝ} (hp : IsPMF p) :
    relEntropyReal p (uniformPMF α) = log (Fintype.card α) - entropy p := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hp
  have key : ∀ x, p x * log (p x / uniformPMF α x) =
      p x * log (Fintype.card α) + p x * log (p x) := by
    intro x
    rcases (hp.nonneg x).eq_or_lt with h | h
    · simp [← h]
    · rw [uniformPMF, div_div_eq_mul_div, div_one, log_mul h.ne' hc.ne']; ring
  rw [relEntropyReal, entropy]
  simp only [key, sum_add_distrib, ← sum_mul, hp.sum_eq_one]
  ring

end InfoTheory
