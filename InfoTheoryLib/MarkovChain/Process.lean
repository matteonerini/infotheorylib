/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Channel

/-!
# Time-homogeneous Markov processes on a finite state space

A Markov process on the states `α` is described by a transition matrix `r : α → α → ℝ`, with
`r x x'` the probability of moving from `x` to `x'`.

## Main definitions

* `IsStochastic r`: every row of `r` is a pmf.
* `step r μ`: one step of the process, `μₙ₊₁(x') = ∑ₓ μₙ(x) r(x' | x)`.
* `transPow r n`: the `n`-step transition probabilities.
* `IsStationaryDist r π`: `π` is a stationary distribution.
* `IsDoublyStochastic P`: the rows and the columns of `P` sum to `1`.

## Main statements

* `uniform_stationary_iff`: the uniform distribution is stationary iff the transition matrix is
  doubly stochastic.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 4.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- A probability transition function `r(x'|x) = r x x'` of a Markov chain on the states `α`. -/
abbrev IsStochastic (r : α → α → ℝ) : Prop := IsChannel r

/-- One step of the Markov chain: `μₙ₊₁(x') = ∑ₓ μₙ(x) r(x'|x)`. -/
def step (r : α → α → ℝ) (μ : α → ℝ) : α → ℝ := outDist μ r

lemma step_isPMF {r : α → α → ℝ} (hr : IsStochastic r) {μ : α → ℝ} (hμ : IsPMF μ) :
    IsPMF (step r μ) :=
  outDist_isPMF hμ hr

lemma absCont_step {r : α → α → ℝ} (hr : IsStochastic r) {p q : α → ℝ} (hq : IsPMF q)
    (hpq : AbsCont p q) : AbsCont (step r p) (step r q) := by
  intro y hy
  have h0 := (sum_eq_zero_iff_of_nonneg fun x _ =>
    mul_nonneg (hq.nonneg x) ((hr x).nonneg y)).1 hy
  refine sum_eq_zero fun x hx => ?_
  rcases mul_eq_zero.1 (h0 x hx) with h | h
  · rw [hpq x h, zero_mul]
  · rw [h, mul_zero]

lemma iterate_step_isPMF {r : α → α → ℝ} (hr : IsStochastic r) {μ : α → ℝ} (hμ : IsPMF μ)
    (n : ℕ) : IsPMF ((step r)^[n] μ) := by
  induction n with
  | zero => exact hμ
  | succ n ih => rw [Function.iterate_succ_apply']; exact step_isPMF hr ih

lemma iterate_absCont {r : α → α → ℝ} (hr : IsStochastic r) {p q : α → ℝ} (hq : IsPMF q)
    (hpq : AbsCont p q) (n : ℕ) :
    AbsCont ((step r)^[n] p) ((step r)^[n] q) := by
  induction n with
  | zero => exact hpq
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact absCont_step hr (iterate_step_isPMF hr hq n) ih

/-- A stationary distribution `ν` of the chain: `ν r = ν`, that is `νⱼ = ∑ᵢ νᵢ rᵢⱼ` (4.26). -/
def IsStationaryDist (r : α → α → ℝ) (ν : α → ℝ) : Prop := step r ν = ν

lemma IsStationaryDist.iterate {r : α → α → ℝ} {ν : α → ℝ} (h : IsStationaryDist r ν) (n : ℕ) :
    (step r)^[n] ν = ν :=
  Function.iterate_fixed h n

/-- **Definition (4.48)–(4.49).** A probability transition matrix `[Pᵢⱼ]` is doubly stochastic
if `∑ᵢ Pᵢⱼ = 1` for all `j` and `∑ⱼ Pᵢⱼ = 1` for all `i`. -/
def IsDoublyStochastic (P : α → α → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ j, ∑ i, P i j = 1) ∧ (∀ i, ∑ j, P i j = 1)

/-- **Remark.** The uniform distribution is a stationary distribution of `P` iff the probability
transition matrix is doubly stochastic. -/
theorem uniform_stationary_iff [Nonempty α] {r : α → α → ℝ} (hr : IsStochastic r) :
    IsStationaryDist r (uniformPMF α) ↔ IsDoublyStochastic r := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hrow : ∀ i, ∑ j, r i j = 1 := fun i => (hr i).sum_eq_one
  have hnn : ∀ i j, 0 ≤ r i j := fun i j => (hr i).nonneg j
  constructor
  · intro h
    refine ⟨hnn, fun j => ?_, hrow⟩
    have := congrFun h j
    simp only [step, outDist, uniformPMF, ← mul_sum] at this
    field_simp at this
    linarith
  · rintro ⟨-, hcol, -⟩
    funext j
    simp [step, outDist, uniformPMF, ← mul_sum, hcol j]

open Classical in
/-- The `n`-step transition probabilities `rⁿ(x'|x)`. -/
def transPow (r : α → α → ℝ) : ℕ → α → α → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | n + 1 => fun x z => ∑ y, r x y * transPow r n y z

lemma transPow_isStochastic {r : α → α → ℝ} (hr : IsStochastic r) (n : ℕ) :
    IsStochastic (transPow r n) := by
  classical
  induction n with
  | zero => intro x; exact ⟨fun y => by simp [transPow]; split_ifs <;> norm_num, by simp [transPow]⟩
  | succ n ih =>
    intro x
    refine ⟨fun z => sum_nonneg fun y _ => mul_nonneg ((hr x).nonneg y) ((ih y).nonneg z), ?_⟩
    simp only [transPow]
    rw [sum_comm]
    simp [← mul_sum, (ih _).sum_eq_one, (hr x).sum_eq_one]

/-- The last step of an `(n + 1)`-step transition: `rⁿ⁺¹(z|x) = ∑_y rⁿ(y|x) r(z|y)`. -/
lemma transPow_succ' (r : α → α → ℝ) (n : ℕ) (x z : α) :
    transPow r (n + 1) x z = ∑ y, transPow r n x y * r y z := by
  classical
  induction n generalizing x with
  | zero => simp [transPow]
  | succ n ih =>
    calc transPow r (n + 2) x z = ∑ y, r x y * transPow r (n + 1) y z := rfl
      _ = ∑ y, r x y * ∑ w, transPow r n y w * r w z := by simp_rw [ih]
      _ = ∑ w, (∑ y, r x y * transPow r n y w) * r w z := by
        simp_rw [mul_sum, sum_mul, mul_assoc]
        exact sum_comm
      _ = ∑ w, transPow r (n + 1) x w * r w z := rfl

end InfoTheory
