/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.ChainRule
public import InfoTheoryLib.MutualInformation.Conditional

/-!
# The chain rule for mutual information

## Main statements

* `chain_rule_mutualInfo`: `I(X₁, …, Xₙ; Y) = ∑ᵢ I(Xᵢ; Y | X_{i-1}, …, X₁)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.5.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Theorem 2.5.2 (Chain rule for information).**
`I(X₁, X₂, …, Xₙ; Y) = ∑ᵢ I(Xᵢ; Y | X_{i-1}, …, X₁)`. -/
theorem chain_rule_mutualInfo {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (Y : Ω → β) (n : ℕ) :
    I[prefixRV X n : Y ; μ] = ∑ i ∈ range n, I[X i : Y | prefixRV X i ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, chain_rule_entropy hμ,
    chain_rule_entropy_cond hμ, ← sum_sub_distrib]
  rfl

end InfoTheory
