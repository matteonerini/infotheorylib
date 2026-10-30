/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RelativeEntropy.Convexity

/-!
# Concavity of entropy

## Main statements

* `entropy_concaveOn`: `H(p)` is a concave function of the pmf `p`.
* `entropy_mix_ge`: mixing two distributions of equal entropy does not decrease the entropy.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.7.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- (2.107) `H(p) = log |𝒳| - D(p‖u)`. -/
lemma entropy_eq_log_card_sub {p : α → ℝ} (hp : IsPMF p) :
    entropy p = log (Fintype.card α) - relEntropyReal p (uniformPMF α) := by
  rw [relEntropyReal_uniform hp]; ring

/-- **Theorem 2.7.3 (Concavity of entropy).** `H(p)` is a concave function of `p`. -/
theorem entropy_concaveOn : ConcaveOn ℝ {p : α → ℝ | IsPMF p} entropy := by
  refine ⟨fun p₁ h₁ p₂ h₂ s t hs ht hst => h₁.mix h₂ hs ht hst, ?_⟩
  intro p₁ h₁ p₂ h₂ s t hs ht hst
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF h₁)
  have hu : AbsCont p₁ (uniformPMF α) ∧ AbsCont p₂ (uniformPMF α) :=
    ⟨fun x hx => absurd hx (by simp [uniformPMF, Fintype.card_ne_zero]),
      fun x hx => absurd hx (by simp [uniformPMF, Fintype.card_ne_zero])⟩
  have hD := relEntropyReal_convexOn.2 (x := (p₁, uniformPMF α)) ⟨h₁, uniformPMF_isPMF, hu.1⟩
    (y := (p₂, uniformPMF α)) ⟨h₂, uniformPMF_isPMF, hu.2⟩ hs ht hst
  have hmix : s • uniformPMF α + t • uniformPMF α = uniformPMF α := by
    rw [← add_smul, hst, one_smul]
  simp only [Prod.smul_mk, Prod.mk_add_mk, hmix, smul_eq_mul] at hD
  rw [entropy_eq_log_card_sub h₁, entropy_eq_log_card_sub h₂,
    entropy_eq_log_card_sub (h₁.mix h₂ hs ht hst)]
  simp only [smul_eq_mul]
  have : s * log (Fintype.card α) + t * log (Fintype.card α) = log (Fintype.card α) := by
    rw [← add_mul, hst, one_mul]
  nlinarith

/-- **Remark after Theorem 2.7.3.** "Mixing two gases of equal entropy results in a gas with
higher entropy." -/
lemma entropy_mix_ge {p₁ p₂ : α → ℝ} (h₁ : IsPMF p₁) (h₂ : IsPMF p₂) (heq : entropy p₁ = entropy p₂)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : entropy p₁ ≤ entropy (s • p₁ + (1 - s) • p₂) := by
  have := entropy_concaveOn.2 h₁ h₂ hs0 (by linarith : 0 ≤ 1 - s) (by ring)
  simp only [smul_eq_mul, ← heq] at this
  nlinarith

end InfoTheory
