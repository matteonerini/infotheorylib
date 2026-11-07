/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.Probability.SupportMixture

/-!
# The values taken by the entropy

## Main statements

* `exists_isPMF_entropy_eq`: on a fixed alphabet, the entropy takes all values between `0` and
  `log |𝒳|`.
* `exists_entropy_eq`: the entropy of a random variable may take any nonnegative real value.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Corollary 2.44
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- On a fixed alphabet, the entropy takes all values between `0` and `log |𝒳|`. -/
theorem exists_isPMF_entropy_eq [Nonempty α] {a : ℝ} (h₀ : 0 ≤ a)
    (h₁ : a ≤ log (Fintype.card α)) : ∃ p : α → ℝ, IsPMF p ∧ entropy p = a := by
  classical
  obtain ⟨c⟩ := ‹Nonempty α›
  let e : α → ℝ := fun x => if x = c then 1 else 0
  have he : IsPMF e := ⟨fun x => by simp only [e]; split_ifs <;> norm_num, by simp [e]⟩
  have hu : IsPMF (uniformPMF α) := uniformPMF_isPMF
  let p : ℝ → α → ℝ := fun t x => (1 - t) * e x + t * uniformPMF α x
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsPMF (p t) := fun t ht =>
    ⟨fun x => add_nonneg (mul_nonneg (by linarith [ht.2]) (he.nonneg x))
      (mul_nonneg ht.1 (hu.nonneg x)), by
      simp only [p, sum_add_distrib, ← mul_sum, he.sum_eq_one, hu.sum_eq_one]
      ring⟩
  have hc : Continuous fun t => entropy (p t) :=
    continuous_entropy.comp (continuous_pi fun x => by fun_prop)
  have h0 : entropy (p 0) = 0 := by
    have : p 0 = e := by funext x; simp [p]
    rw [this, entropy_eq_zero_iff he]
    exact ⟨c, fun _ => rfl⟩
  have h1 : entropy (p 1) = log (Fintype.card α) := by
    have : p 1 = uniformPMF α := by funext x; simp [p]
    rw [this, entropy_eq_log_card_iff hu]
  obtain ⟨t, ht, hta⟩ := intermediate_value_Icc zero_le_one hc.continuousOn
    (show a ∈ Set.Icc (entropy (p 0)) (entropy (p 1)) by rw [h0, h1]; exact ⟨h₀, h₁⟩)
  exact ⟨p t, hp t ht, hta⟩

/-- **Corollary 2.44 of [yeung2008].** The entropy of a random variable may take any nonnegative
real value. -/
theorem exists_entropy_eq {a : ℝ} (h₀ : 0 ≤ a) :
    ∃ (n : ℕ) (p : Fin n → ℝ), IsPMF p ∧ entropy p = a := by
  have hpos : 0 < ⌈exp a⌉₊ := Nat.ceil_pos.2 (exp_pos a)
  have : Nonempty (Fin ⌈exp a⌉₊) := Fin.pos_iff_nonempty.1 hpos
  refine ⟨⌈exp a⌉₊, exists_isPMF_entropy_eq h₀ ?_⟩
  rw [Fintype.card_fin]
  calc a = log (exp a) := (log_exp a).symm
    _ ≤ _ := log_le_log (exp_pos a) (Nat.le_ceil _)

end InfoTheory
