/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Conditional
public import InfoTheoryLib.RelativeEntropy.InformationInequality

/-!
# Conditional relative entropy

## Main definitions

* `condRelEntropy p q`: the conditional relative entropy
  `D(p(y | x) ‖ q(y | x)) = ∑ₓ p(x) ∑ᵧ p(y | x) log (p(y | x) / q(y | x))`.

## Main statements

* `chain_rule_relEntropy`: `D(p(x, y) ‖ q(x, y)) = D(p(x) ‖ q(x)) + D(p(y | x) ‖ q(y | x))`.
* `condRelEntropy_nonneg`: `D(p(y | x) ‖ q(y | x)) ≥ 0`, with equality iff the conditional
  distributions agree wherever `p(x) > 0` (`condRelEntropy_eq_zero_iff`).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006],
  Theorem 2.5.3 and Section 2.6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Definition (2.65).** The conditional relative entropy
`D(p(y|x) ‖ q(y|x)) = ∑ₓ p(x) ∑ᵧ p(y|x) log (p(y|x) / q(y|x))`. -/
def condRelEntropy (p q : α × β → ℝ) : ℝ :=
  ∑ x, marg p x * ∑ y, condPMF p x y * log (condPMF p x y / condPMF q x y)

/-- (2.66) `D(p(y|x) ‖ q(y|x)) = ∑ₓ ∑ᵧ p(x, y) log (p(y|x) / q(y|x))`. -/
lemma condRelEntropy_eq_sum {p : α × β → ℝ} (hp : ∀ z, 0 ≤ p z) (q : α × β → ℝ) :
    condRelEntropy p q = ∑ x, ∑ y, p (x, y) * log (condPMF p x y / condPMF q x y) := by
  unfold condRelEntropy
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [← mul_assoc, marg_mul_condPMF hp]

/-- **Theorem 2.5.3 (Chain rule for relative entropy).**
`D(p(x, y) ‖ q(x, y)) = D(p(x) ‖ q(x)) + D(p(y|x) ‖ q(y|x))`. -/
theorem chain_rule_relEntropy {p q : α × β → ℝ} (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (hpq : AbsCont p q) :
    relEntropyReal p q = relEntropyReal (marg p) (marg q) + condRelEntropy p q := by
  rw [condRelEntropy_eq_sum hp, relEntropyReal, relEntropyReal, Fintype.sum_prod_type]
  simp only [marg]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rcases (hp (x, y)).eq_or_lt with h | h
  · simp [← h]
  · have hq' : 0 < q (x, y) := (hq _).lt_of_ne fun h' => h.ne' (hpq _ h'.symm)
    have hpx : 0 < marg p x := h.trans_le (le_marg hp x y)
    have hqx : 0 < marg q x := hq'.trans_le (le_marg hq x y)
    simp only [condPMF, marg] at hpx hqx ⊢
    rw [← mul_add, ← log_mul (by positivity) (by positivity)]
    congr 2
    field_simp

/-- `D(p(y|x) ‖ q(y|x)) = ∑ₓ p(x) D(p(·|x) ‖ q(·|x))`. -/
lemma condRelEntropy_eq_sum_relEntropy (p q : α × β → ℝ) :
    condRelEntropy p q = ∑ x, marg p x * relEntropyReal (condPMF p x) (condPMF q x) := rfl

/-- **Corollary (2.91).** `D(p(y|x) ‖ q(y|x)) ≥ 0`. -/
theorem condRelEntropy_nonneg {p q : α × β → ℝ} (hp : IsPMF p) (hq : IsPMF q)
    (hpq : AbsCont p q) : 0 ≤ condRelEntropy p q := by
  rw [condRelEntropy_eq_sum_relEntropy]
  refine sum_nonneg fun x _ => ?_
  rcases ((marg_isPMF hp).nonneg x).eq_or_lt with h | h
  · rw [← h, zero_mul]
  · exact mul_nonneg h.le (relEntropyReal_nonneg (condPMF_isPMF hp.nonneg h.ne')
      (condPMF_isPMF hq.nonneg (marg_pos_of_absCont hq.nonneg hpq h).ne')
      (absCont_condPMF hq.nonneg hpq x))

/-- **Corollary (2.91), equality case.** `D(p(y|x) ‖ q(y|x)) = 0` iff `p(y|x) = q(y|x)` for all
`y` and all `x` with `p(x) > 0`. -/
theorem condRelEntropy_eq_zero_iff {p q : α × β → ℝ} (hp : IsPMF p) (hq : IsPMF q)
    (hpq : AbsCont p q) :
    condRelEntropy p q = 0 ↔ ∀ x, 0 < marg p x → ∀ y, condPMF p x y = condPMF q x y := by
  have hterm : ∀ x, 0 < marg p x →
      (0 ≤ relEntropyReal (condPMF p x) (condPMF q x) ∧
        (relEntropyReal (condPMF p x) (condPMF q x) = 0 ↔ condPMF p x = condPMF q x)) := by
    intro x h
    have h1 := condPMF_isPMF hp.nonneg h.ne'
    have h2 := condPMF_isPMF hq.nonneg (marg_pos_of_absCont hq.nonneg hpq h).ne'
    exact ⟨relEntropyReal_nonneg h1 h2 (absCont_condPMF hq.nonneg hpq x),
      relEntropyReal_eq_zero_iff h1 h2 (absCont_condPMF hq.nonneg hpq x)⟩
  have hnn : ∀ x ∈ univ, 0 ≤ marg p x * relEntropyReal (condPMF p x) (condPMF q x) := by
    intro x _
    rcases ((marg_isPMF hp).nonneg x).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · exact mul_nonneg h.le (hterm x h).1
  rw [condRelEntropy_eq_sum_relEntropy, sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h x hx y
    have := h x (mem_univ x)
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hx.ne'
    · exact congrFun ((hterm x hx).2.1 h') y
  · intro h x _
    rcases ((marg_isPMF hp).nonneg x).eq_or_lt with h' | h'
    · rw [← h', zero_mul]
    · rw [(hterm x h').2.2 (funext (h x h')), mul_zero]

end InfoTheory
