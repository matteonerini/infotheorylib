/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MarkovChain.Basic
public import InfoTheoryLib.MutualInformation.Conditional

/-!
# The data processing inequality

## Main statements

* `data_processing`: if `X → Y → Z` then `I(X; Z) ≤ I(X; Y)`, with equality iff `X → Z → Y`
  (`data_processing_eq_iff`).
* `mutualInfo_comp_le`: `I(X; g(Y)) ≤ I(X; Y)`.
* `condMutualInfo_le_of_markov`: if `X → Y → Z` then `I(X; Y | Z) ≤ I(X; Y)`.
* `condMutualInfo_le_of_markovChain_left`: if `Z → X → Y` then `I(X; Y | Z) ≤ I(X; Y)`.
* `mutualInfo_le_condMutualInfo_of_indep`: if `X` and `Z` are independent then
  `I(X; Y | Z) ≥ I(X; Y)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.8
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- (2.119)–(2.120) Under `X → Y → Z`: `I(X;Y) = I(X;Z) + I(X;Y|Z)`. -/
lemma mutualInfo_eq_of_markov {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : MarkovChain μ X Y Z) : I[X : Y ; μ] = I[X : Z ; μ] + I[X : Y | Z ; μ] := by
  have h1 := chain_rule_mutualInfo₂ hμ X Y Z
  have h2 := chain_rule_mutualInfo₂ hμ X Z Y
  have h3 : I[X : pair Z Y ; μ] = I[X : pair Y Z ; μ] :=
    mutualInfo_congr_right hμ X Prod.swap Prod.swap_injective (fun _ => rfl)
  have h4 : I[X : Z | Y ; μ] = 0 :=
    (condMutualInfo_eq_zero_iff hμ X Z Y).2 ((markovChain_iff_condIndep hμ X Y Z).1 h)
  linarith

/-- **Theorem 2.8.1 (Data processing inequality).** If `X → Y → Z`, then `I(X;Y) ≥ I(X;Z)`. -/
theorem data_processing {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : MarkovChain μ X Y Z) : I[X : Z ; μ] ≤ I[X : Y ; μ] := by
  have h1 := chain_rule_mutualInfo₂ hμ X Y Z
  have h2 := chain_rule_mutualInfo₂ hμ X Z Y
  have h3 : I[X : pair Z Y ; μ] = I[X : pair Y Z ; μ] :=
    mutualInfo_congr_right hμ X Prod.swap Prod.swap_injective (fun _ => rfl)
  have h4 : I[X : Z | Y ; μ] = 0 :=
    (condMutualInfo_eq_zero_iff hμ X Z Y).2 ((markovChain_iff_condIndep hμ X Y Z).1 h)
  have h5 := condMutualInfo_nonneg hμ X Y Z
  linarith

/-- **Theorem 2.8.1 (equality case).** Equality `I(X;Y) = I(X;Z)` holds iff `I(X;Y|Z) = 0`, i.e.
iff `X → Z → Y` is a Markov chain. -/
theorem data_processing_eq_iff {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : MarkovChain μ X Y Z) :
    (I[X : Y ; μ] = I[X : Z ; μ] ↔ I[X : Y | Z ; μ] = 0) ∧
      (I[X : Y | Z ; μ] = 0 ↔ MarkovChain μ X Z Y) := by
  refine ⟨?_, ?_⟩
  · rw [mutualInfo_eq_of_markov hμ h]; constructor <;> intro h' <;> linarith
  · rw [condMutualInfo_eq_zero_iff hμ, markovChain_iff_condIndep hμ]

/-- **Theorem 2.8.1 (second inequality).** If `X → Y → Z`, then `I(Y;Z) ≥ I(X;Z)`. -/
theorem data_processing' {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : MarkovChain μ X Y Z) : I[X : Z ; μ] ≤ I[Y : Z ; μ] := by
  have := data_processing hμ (h.symm hμ)
  rwa [mutualInfo_comm hμ Z X, mutualInfo_comm hμ Z Y] at this

/-- **Corollary.** `I(X;Y) ≥ I(X; g(Y))`: functions of the data `Y` cannot increase the
information about `X`. -/
theorem mutualInfo_comp_le {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → γ) :
    I[X : g ∘ Y ; μ] ≤ I[X : Y ; μ] :=
  data_processing hμ (markovChain_comp hμ X Y g)

/-- **Corollary (2.122).** If `X → Y → Z`, then `I(X;Y|Z) ≤ I(X;Y)`: the dependence of `X` and
`Y` is decreased by the observation of a "downstream" random variable `Z`. -/
theorem condMutualInfo_le_of_markov {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β}
    {Z : Ω → γ} (h : MarkovChain μ X Y Z) : I[X : Y | Z ; μ] ≤ I[X : Y ; μ] := by
  rw [mutualInfo_eq_of_markov hμ h]
  linarith [mutualInfo_nonneg hμ X Z]

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] in
/-- If `X → Y → Z` then `X → Y → h(Z)`. -/
lemma MarkovChain.comp_right [Finite α] [Finite β] [Finite γ] [Finite δ] {μ : Ω → ℝ}
    (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ} (h : MarkovChain μ X Y Z) (g : γ → δ) :
    MarkovChain μ X Y (g ∘ Z) := by
  have := Fintype.ofFinite α; have := Fintype.ofFinite β
  have := Fintype.ofFinite γ; have := Fintype.ofFinite δ
  rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ] at h ⊢
  exact le_antisymm (h ▸ condMutualInfo_comp_le hμ X Z Y g) (condMutualInfo_nonneg hμ _ _ _)

/-- **Conditioning on an independent variable** (Lecture 2 of [elgamal2010]). If `X` and `Z` are
independent, then `I(X;Y|Z) ≥ I(X;Y)`. -/
theorem mutualInfo_le_condMutualInfo_of_indep {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α}
    {Y : Ω → β} {Z : Ω → γ} (h : IndepRV μ X Z) : I[X : Y ; μ] ≤ I[X : Y | Z ; μ] := by
  have h1 := chain_rule_mutualInfo₂ hμ X Y Z
  have h2 := (mutualInfo_eq_zero_iff hμ X Z).2 h
  have h3 := mutualInfo_comp_le hμ X (pair Y Z) Prod.fst
  have h4 : Prod.fst ∘ pair Y Z = Y := rfl
  rw [h4] at h3
  linarith

/-- **Conditioning on an upstream variable** (Lecture 2 of [elgamal2010]). If `Z → X → Y`
form a Markov chain, then `I(X;Y|Z) ≤ I(X;Y)`. -/
theorem condMutualInfo_le_of_markovChain_left {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α}
    {Y : Ω → β} {Z : Ω → γ} (h : MarkovChain μ Z X Y) : I[X : Y | Z ; μ] ≤ I[X : Y ; μ] := by
  rw [condMutualInfo_comm hμ, mutualInfo_comm hμ]
  exact condMutualInfo_le_of_markov hμ (h.symm hμ)

end InfoTheory
