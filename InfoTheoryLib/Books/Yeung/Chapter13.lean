/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.HalfSpaceEquivalence
public import InfoTheoryLib.InfoInequalities.EntropySpace

/-!
# Yeung, Chapter 13: Information Inequalities

This file indexes the formalization of Chapter 13 of [yeung2008], and contains its worked example
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **The entropy space.** `ℋₙ` is `EntropySpace ι`, the functions on the nonempty subsets of the
  index type `ι`; the coordinates are labelled by subsets, not listed in an order. The convention
  `h_∅ = 0` is `EntropySpace.extend`.
* **Random variables.** "Any collection of `n` random variables" ranges over finite sample spaces
  and finite alphabets in the universe of `ι`, as in Theorem 3.11.
* **Canonical form.** An information expression in canonical form `b⊤h` is `infoExpr b h`, with a
  coefficient vector `b : EntropySpace ι`.
* **Section 13.4.** The results on equivalent inequalities are linear algebra and are stated for any
  matrix `Q : Matrix q k ℝ`, with `h : k → ℝ`. The row space of `Q` is `rowSpace Q`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Introduction
* (13.9)–(13.15), the imperfect secrecy theorem of Example 3.15: `example_3_15`
  (`Books.Yeung.Chapter3`).

### 13.1 The Region `Γ*ₙ`
* (13.22)–(13.23): `blockRV`, `blockEntropy` (`MutualInformation.Block`), and the entropy function
  `entropyVector` (`InfoInequalities.EntropySpace`).
* The entropy space `ℋₙ`: `EntropySpace` (`InfoInequalities.EntropySpace`).
* (13.24): `entropicRegion` (`InfoInequalities.EntropySpace`).
* Properties 1 and 3 of `Γ*ₙ`: `zero_mem_entropicRegion`, `nonneg_of_mem_entropicRegion`
  (`InfoInequalities.EntropySpace`). Property 2, which the book proves in Chapter 15:
  `convex_closure_entropicRegion` (`InfoInequalities.EntropicRegion`).

### 13.2 Information Expressions in Canonical Form
* (13.26)–(13.28): `condEntropy_eq_sub` (`Entropy.Conditional`), `mutualInfo_eq_add_sub`
  (`MutualInformation.Basic`), `condMutualInfo_eq` (`MutualInformation.Conditional`), and for
  blocks `condMutualInfo_eq_blockEntropy` (`MutualInformation.Block`).
* (13.29): `infoExpr` (`InfoInequalities.EntropySpace`).
* (13.35): `atomsToEntropy`, with every `h` of the form `Cₙ u` in `exists_atomsToEntropy_eq`
  (`InfoInequalities.EntropySpace`).
* (13.36): `entropicAtomRegion` (`InfoInequalities.EntropySpace`).
* Lemma 13.1: `lemma_13_1` (here), which is `atomsToEntropy_mem_entropicRegion`
  (`InfoInequalities.EntropySpace`).
* Theorem 13.2: `theorem_13_2` (here), which is `infoExpr_eq_zero_iff`
  (`InfoInequalities.EntropySpace`). The proof shows that every vector of `ℋₙ` is a difference of
  two entropic vectors, `exists_sub_eq`, instead of using the Lebesgue measure of `Γ*ₙ`.
* Corollary 13.3: `corollary_13_3` (here), which is `infoExpr_eq_iff`
  (`InfoInequalities.EntropySpace`).

### 13.3 A Geometrical Framework
* Sections 13.3.1–13.3.2: `IneqAlwaysHolds`, `ineqAlwaysHolds_iff`
  (`InfoInequalities.EntropySpace`), with the constraint `Φ` any set, such as `{h : Qh = 0}` of
  (13.48).
* The examples of constraints after (13.46): `theorem_2_39` (`Books.Yeung.Chapter2`) for mutual
  independence, `mutualInfo_eq_zero_iff` (`MutualInformation.Basic`) for pairwise independence,
  and `condEntropy_eq_zero_iff` (`Entropy.Fano`) for a function.
* (13.49)–(13.50): `IneqAlwaysHolds.mono` (`InfoInequalities.EntropySpace`).
* Section 13.3.3: `forall_infoExpr_eq_zero_iff` (`InfoInequalities.EntropySpace`).

### 13.4 Equivalence of Constrained Inequalities
* (13.52)–(13.58): `IneqEquivOn`, `rowSpace`, `mem_span_rows_iff`
  (`ForMathlib.HalfSpaceEquivalence`).
* (13.59): `ineqEquivOn_of_eq`, `ineqEquivOn_iff_exists` (`ForMathlib.HalfSpaceEquivalence`).
* Theorem 13.4: `theorem_13_4` (here), which is `ineqEquivOn_iff_of_mem_span`
  (`ForMathlib.HalfSpaceEquivalence`). The book leaves the proof as an exercise.
* Theorem 13.5: `theorem_13_5` (here), which is `ineqEquivOn_iff_existsUnique`
  (`ForMathlib.HalfSpaceEquivalence`), with `Q'` any matrix with linearly independent rows spanning
  the row space of `Q`.
* Example 13.6: `example_13_6` (here).

### 13.5 The Implication Problem of Conditional Independence
* (13.74)–(13.77): `condIndep_blockRV_iff` (`InfoInequalities.EntropySpace`), from Theorem 2.34.
* (13.78): `ciHyperplane` (`InfoInequalities.EntropySpace`).
* The implication problem as a property of `Γ*ₙ`: `ciImplies_iff`
  (`InfoInequalities.EntropySpace`).

## Not formalized

* The fourth example of a constraint after (13.46), the characterization of `X₁ → X₂ → X₃ → X₄`
  by `I(X₁; X₃ | X₂) = 0` and `I(X₁, X₂; X₄ | X₃) = 0`; the library characterizes Markov chains by
  Proposition 2.8 instead.
* The remark after Example 13.6 on the equivalence of identities, which is left as Problem 5.
* Figures 13.1 to 13.5.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 13
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-- **Lemma 13.1.** -/
alias lemma_13_1 := atomsToEntropy_mem_entropicRegion

/-- **Theorem 13.2.** -/
alias theorem_13_2 := infoExpr_eq_zero_iff

/-- **Corollary 13.3.** -/
alias corollary_13_3 := infoExpr_eq_iff

/-- **Theorem 13.4.** -/
alias theorem_13_4 := ineqEquivOn_iff_of_mem_span

/-- **Theorem 13.5.** (13.61) -/
alias theorem_13_5 := ineqEquivOn_iff_existsUnique

/-! ### Example 13.6

The coordinates of `ℋ₃` are ordered as in (13.66): `h₁, h₂, h₃, h₁₂, h₂₃, h₁₃, h₁₂₃`. -/

/-- The Markov constraint `I(X₁; X₃ | X₂) = 0` as `Q h = 0`, (13.65). -/
def example136Q : Matrix (Fin 1) (Fin 7) ℝ := !![0, -1, 0, 1, 1, 0, -1]

/-- `H(X₁ | X₃) - H(X₁ | X₂)`, (13.69). -/
def example136b : Fin 7 → ℝ := ![0, 1, -1, -1, 0, 1, 0]

/-- `I(X₁; X₂ | X₃)`, (13.70). -/
def example136c : Fin 7 → ℝ := ![0, 0, -1, 0, 1, 1, -1]

/-- **Example 13.6.** Under the Markov constraint `I(X₁; X₃ | X₂) = 0`, the inequalities
`H(X₁ | X₃) - H(X₁ | X₂) ≥ 0` and `I(X₁; X₂ | X₃) ≥ 0` are equivalent: (13.71) has the unique
solution `e = 1`, `a = 1`. -/
theorem example_13_6 :
    IneqEquivOn example136Q example136b example136c ∧
      ∃! p : (Fin 1 → ℝ) × ℝ, 0 < p.2 ∧
        example136c = example136Qᵀ *ᵥ p.1 + p.2 • example136b := by
  have hsol : example136c = (1 : ℝ) • example136b + example136Qᵀ *ᵥ ![1] := by
    ext i
    fin_cases i <;> simp [example136Q, example136b, example136c]
  have heq := ineqEquivOn_of_eq one_pos ![1] hsol
  have hb : example136b ∉ rowSpace example136Q := by
    rw [mem_span_rows_iff_exists]
    rintro ⟨e, he⟩
    have := congrFun he 2
    simp [example136Q, example136b, mulVec, dotProduct] at this
  have hc : example136c ∉ rowSpace example136Q := by
    rw [mem_span_rows_iff_exists]
    rintro ⟨e, he⟩
    have := congrFun he 2
    simp [example136Q, example136c, mulVec, dotProduct] at this
  have hind : LinearIndependent ℝ fun i => example136Q i := by
    rw [linearIndependent_unique_iff]
    intro h
    have := congrFun h 1
    simp [example136Q] at this
  exact ⟨heq, (ineqEquivOn_iff_existsUnique rfl hind hb hc).1 heq⟩

end InfoTheory.Yeung
