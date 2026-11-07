/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MutualInformation.Conditional
public import InfoTheoryLib.Probability.SupportMixture

/-!
# Continuity of the conditional mutual information

For finite alphabets, the conditional mutual information is a continuous function of the joint
distribution. The topology of `Ω → ℝ` is that of pointwise convergence, which for a finite `Ω` is
the same as that of convergence in variational distance. Entropy, conditional entropy and mutual
information are special cases, with a repeated or a constant random variable.

## Main statements

* `continuousOn_condMutualInfo`: `μ ↦ I(X; Y | Z)` is continuous on the set of pmfs.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 2.3
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

/-- **(2.78)–(2.84) of [yeung2008].** `I(X; Y | Z)` is a continuous function of the distribution,
for fixed finite alphabets. -/
theorem continuousOn_condMutualInfo (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    ContinuousOn (fun μ : Ω → ℝ => I[X : Y | Z ; μ]) {μ | IsPMF μ} := by
  refine ContinuousOn.congr (f := fun μ => H[pair Z X ; μ] + H[pair Z Y ; μ] - H[Z ; μ] -
    H[pair Z (pair X Y) ; μ]) (Continuous.continuousOn ?_) fun μ hμ => condMutualInfo_eq hμ X Y Z
  exact (((continuous_entropy_dist _).add (continuous_entropy_dist _)).sub
    (continuous_entropy_dist _)).sub (continuous_entropy_dist _)

end InfoTheory
