/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.InfoInequalities.NonShannon

/-!
# Yeung, Chapter 15: Beyond Shannon-Type Inequalities

This file indexes the formalization of Chapter 15 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included, except Problem 4.

## Conventions

* **Entropy space.** As in Chapters 13 and 14, `h : EntropySpace ι` has coordinates on the
  nonempty subsets, and `h.extend` adds `h_∅ = 0`. `Γ*ₙ` is `entropicRegion (Fin n)`, `Γₙ` is
  `shannonRegion (Fin n)`, and `Γ̄*ₙ` is `closure (entropicRegion (Fin n))`.
* **Indexing.** The variables are `X i` for `i : Fin n`, starting at `0`: the book's `X₁` is
  `X 0`, and its `X₃, X₄` are `X 2, X 3`.
* **The copy.** The auxiliary random variables `X̃₁, X̃₂` of (15.63) live on the sample space
  `Ω × Ω` with the measure `copyMeasure μ X`. Their entropy function `copyEntropy μ X` has the six
  indices `0, …, 5` for `X₁, X₂, X₃, X₄, X̃₁, X̃₂`. Lemmas 15.9 and 15.10 are stated for any
  polymatroid on these six indices with the two properties used in their proofs.
* **Information measures as constraints.** `I(X_S; X_T | X_K) = 0` is
  `condInfo h.extend S T K = 0`, and `H(Xᵢ | X_K)` is `I(Xᵢ; Xᵢ | X_K)`. The 14 measures of
  (15.94) are `zyMeasures`, in the order of the book.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 15.1 Characterizations of `Γ*₂`, `Γ*₃` and `Γ̄*ₙ`
* Theorem 15.1: `theorem_15_1` (here), which is `entropicRegion_fin_two`
  (`InfoInequalities.EntropicRegion`), through the I-Measure: an element of `Γ₂` has
  nonnegative atoms (`atom_nonneg_of_mem_shannonRegion`), and Lemma 13.1 realizes it.
* Theorem 15.2: `theorem_15_2` (here), which is `entropicRegion_fin_three_ne`
  (`InfoInequalities.EntropicRegion`). The vector `a • (1, 1, 1, 2, 2, 2, 2)` is
  `a • rankVector (Fin 3) 2`; it is in `Γ₃` for `a ≥ 0` (`smul_rankVector_mem_shannonRegion`), and
  in `Γ*₃` only if `a = log M` for a positive integer `M` (`exists_eq_log_of_smul_rankTwo_mem`).
  The proof takes `a = log (3 / 2)`.
* Lemma 15.3: `lemma_15_3` (here), which is `add_mem_entropicRegion`
  (`InfoInequalities.EntropicRegion`).
* Corollary 15.4: `corollary_15_4` (here), which is `nsmul_mem_entropicRegion`
  (`InfoInequalities.EntropicRegion`), for every natural number `k`.
* Theorem 15.5: `theorem_15_5` (here), from `convex_closure_entropicRegion` and
  `smul_mem_closure_entropicRegion` (`InfoInequalities.EntropicRegion`). The mixture of a
  collection with a constant one by an independent coin of bias `δ` is
  `exists_mem_entropicRegion_eq_binEntropy_add`.
* (15.34)–(15.36): `ineqAlwaysHolds_iff_closure_subset` (`InfoInequalities.EntropicRegion`).
* Theorem 15.6: `theorem_15_6` (here), which is `closure_entropicRegion_fin_three`
  (`InfoInequalities.EntropicRegion`). The vector `log 2 • rankVector (Fin 3) 2` of three
  pairwise independent bits with a zero sum is `smul_rankVector_mem_entropicRegion`.

### 15.2 A Non-Shannon-Type Unconstrained Inequality
* Theorem 15.7: `theorem_15_7` (here), which is `zhangYeung` (`InfoInequalities.ZhangYeung`).
* (15.63): `copyMeasure`, `isPMF_copyMeasure`, `copyFamily`, `copyEntropy`
  (`InfoInequalities.ZhangYeung`).
* Lemma 15.8: `lemma_15_8` (here), from `copy_markov` and `copy_snd`
  (`InfoInequalities.ZhangYeung`); the equality of the distributions is
  `dist_copyMeasure_copyVec`, and `copy_fst` says that `X₁, …, X₄` keep their entropy function.
* Lemma 15.9: `lemma_15_9` (here), which is `condInfo_sub_sub_le_of_markov`
  (`InfoInequalities.ZhangYeung`).
* Lemma 15.10: `lemma_15_10` (here), which is `condInfo_sub_two_mul_le_of_markov`
  (`InfoInequalities.ZhangYeung`).
* (15.77)–(15.84), the end of the proof of Theorem 15.7: `zhangYeung_of_copy`
  (`InfoInequalities.ZhangYeung`).
* (15.85): `zyNat`, `zyPoint`, `zyPoint_mem_shannonRegion` (`InfoInequalities.NonShannon`).
* Theorem 15.11: `theorem_15_11` (here), from `not_isShannonType_zyCoeff` and
  `entropicRegion_fin_four_ne` (`InfoInequalities.NonShannon`); (15.86)–(15.90), for the closure,
  is `closure_entropicRegion_fin_four_ne`.
* Theorem 15.12: `theorem_15_12` (here), which is `not_isShannonType_zyCoeff_constrained`
  (`InfoInequalities.NonShannon`), for every subset of the 14 measures `zyMeasures` of (15.94),
  with `condInfo_zyPoint_zyMeasures`.

### 15.3 A Non-Shannon-Type Constrained Inequality
* Lemma 15.13: `lemma_15_13` (here), which is `dist_copyTilde` (`InfoInequalities.NonShannon`).
* Theorem 15.14: `theorem_15_14` (here), which is `zhangYeung_constrained`
  (`InfoInequalities.NonShannon`); in the entropy space, `ineqAlwaysHolds_zyConstrainedCoeff`.
  The sub-probability `p̂` of (15.124) is `pHat`, and (15.126)–(15.143) is `sum_pHat_le_one`.
* Theorem 15.15: `theorem_15_15` (here), which is
  `not_isShannonType_zyConstrainedCoeff_zyConstraint` (`InfoInequalities.NonShannon`).
* Theorem 15.16: `theorem_15_16` (here), which is `not_isShannonType_zyConstrainedCoeff`
  (`InfoInequalities.NonShannon`), for every subset of the 14 measures; the book's constraints are
  the subsets that contain the first two.

### 15.4 Applications
* Example 15.17: `example_15_17` (here), the implication (15.152), and `example_15_17_not_shannon`
  (here): `h̃(1) ∈ Γ₄` meets the four constraints but not `I(X₃; X₄) = 0`, so the implication does
  not follow from the basic inequalities (Problem 4).
* Example 15.18: `example_15_18` (here), the implication (15.155) from (15.62). The book says that
  this implication cannot be deduced from the basic inequalities, but it can:
  `example_15_18_shannon` (here) proves `I(X₃; X₄) = 0` on `Γ₄` from `I(X₁; X₃, X₄) = 0` and
  `I(X₃; X₄ | X₁) = 0` alone, since `I(X₃; X₄) ≤ I(X₁; X₃) + I(X₁; X₄)` under these two
  constraints.
* Example 15.19: `example_15_19` (here): (15.62) is non-Shannon-type under the constraints
  (15.156), the last four measures of (15.94).
* Example 15.20: `example_15_20` (here), the inequality (15.161), which holds for all four random
  variables, and `example_15_20_markov` (here): (15.62) is non-Shannon-type under the Markov
  condition (15.158).

## Not formalized

* The outer bound `Γ̃₄` of (15.91)–(15.93), the twelve versions `⟨15.62⟩` of (15.62), and the
  claim that `Γ̃₄ ∩ Φ` is a tighter outer bound than `Γ₄ ∩ Φ` in Example 15.19, which is not
  proved in the book.
* The remark after Theorem 15.12 that `h̃(a)` defines an extreme direction of `Γ₄`, which the
  proofs here do not need.
* The claim after Theorem 15.15 that the constrained inequality is not implied by `⟨15.62⟩` and
  the basic inequalities, which the book attributes to a computation.
* The inequality (15.159) of Example 15.20 and its optimality, which the book attributes to ITIP.
* Figures 15.1 to 15.4.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 15
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-! ### 15.1 Characterizations of `Γ*₂`, `Γ*₃` and `Γ̄*ₙ` -/

/-- **Theorem 15.1.** `Γ*₂ = Γ₂`. -/
alias theorem_15_1 := entropicRegion_fin_two

/-- **Theorem 15.2.** `Γ*₃ ≠ Γ₃`. -/
alias theorem_15_2 := entropicRegion_fin_three_ne

/-- **Lemma 15.3.** If `h` and `h'` are in `Γ*ₙ`, then `h + h'` is in `Γ*ₙ`. -/
alias lemma_15_3 := add_mem_entropicRegion

/-- **Corollary 15.4.** If `h ∈ Γ*ₙ`, then `k h ∈ Γ*ₙ` for any natural number `k`. -/
alias corollary_15_4 := nsmul_mem_entropicRegion

/-- **Theorem 15.5.** `Γ̄*ₙ` is a convex cone. -/
theorem theorem_15_5 {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Convex ℝ (closure (entropicRegion ι)) ∧
      ∀ h ∈ closure (entropicRegion ι), ∀ t : ℝ, 0 ≤ t → t • h ∈ closure (entropicRegion ι) :=
  ⟨convex_closure_entropicRegion, fun _ hh _ ht => smul_mem_closure_entropicRegion hh ht⟩

/-- **Theorem 15.6.** `Γ̄*₃ = Γ₃`. -/
alias theorem_15_6 := closure_entropicRegion_fin_three

/-! ### 15.2 A Non-Shannon-Type Unconstrained Inequality -/

/-- **Theorem 15.7.** For any four random variables,
`2 I(X₃; X₄) ≤ I(X₁; X₂) + I(X₁; X₃, X₄) + 3 I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂)` (15.62). -/
alias theorem_15_7 := zhangYeung

section Copy

variable {Ω : Type*} [Fintype Ω] {A : Fin 4 → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}

/-- **Lemma 15.8.** `(X₁, X₂) → (X₃, X₄) → (X̃₁, X̃₂)` is a Markov chain (15.64), and
`(X̃₁, X̃₂, X₃, X₄)` has the entropy function of `(X₁, X₂, X₃, X₄)`. -/
theorem lemma_15_8 (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    condInfo (copyEntropy μ X) {0, 1} {4, 5} {2, 3} = 0 ∧
      ∀ S, copyEntropy μ X (S.map copyEmb₂) = blockEntropy μ X S :=
  ⟨copy_markov hμ, copy_snd hμ⟩

end Copy

/-- **Lemma 15.9**, for a polymatroid on `X₁, X₂, X₃, X₄, X̃₁, X̃₂`:
`I(X₃; X₄) - I(X₃; X₄ | X₁) - I(X₃; X₄ | X₂) ≤ I(X₁; X̃₂)` (15.65). -/
alias lemma_15_9 := condInfo_sub_sub_le_of_markov

/-- **Lemma 15.10**, for a polymatroid on `X₁, X₂, X₃, X₄, X̃₁, X̃₂`:
`I(X₃; X₄) - 2 I(X₃; X₄ | X₁) ≤ I(X₁; X̃₁)` (15.76). -/
alias lemma_15_10 := condInfo_sub_two_mul_le_of_markov

/-- **Theorem 15.11.** The inequality (15.62) is a non-Shannon-type inequality, and `Γ*₄ ≠ Γ₄`. -/
theorem theorem_15_11 :
    ¬IsShannonType zyCoeff Set.univ ∧ entropicRegion (Fin 4) ≠ shannonRegion (Fin 4) :=
  ⟨not_isShannonType_zyCoeff, entropicRegion_fin_four_ne⟩

/-- **Theorem 15.12.** The inequality (15.62) is a non-Shannon-type inequality under the
constraint that any subset of the 14 Shannon's information measures (15.94) vanishes. -/
alias theorem_15_12 := not_isShannonType_zyCoeff_constrained

/-! ### 15.3 A Non-Shannon-Type Constrained Inequality -/

/-- **Lemma 15.13.** `p̃` of (15.98) is the distribution of `(X₁, X̃₂, X₃, X₄)`, and it has the
marginals (15.99)–(15.100). -/
alias lemma_15_13 := dist_copyTilde

/-- **Theorem 15.14.** If `I(X₁; X₂) = I(X₁; X₂ | X₃) = 0`, then
`I(X₃; X₄) ≤ I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂)`. -/
alias theorem_15_14 := zhangYeung_constrained

/-- **Theorem 15.15.** The constrained inequality of Theorem 15.14 is non-Shannon-type. -/
alias theorem_15_15 := not_isShannonType_zyConstrainedCoeff_zyConstraint

/-- **Theorem 15.16.** The inequality (15.144) is non-Shannon-type under the constraint that any
subset of the 14 measures (15.94) vanishes, in particular `I(X₁; X₂)`, `I(X₁; X₂ | X₃)` and any
subset of the 12 measures (15.145). -/
alias theorem_15_16 := not_isShannonType_zyConstrainedCoeff

/-! ### 15.4 Applications -/

section Applications

variable {Ω : Type*} [Fintype Ω] {A : Fin 4 → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}

omit [∀ i, Fintype (A i)] in
/-- **Example 15.17**, (15.152): `X₁ ⊥ X₂`, `X₁ ⊥ X₂ | X₃`, `X₃ ⊥ X₄ | X₁` and `X₃ ⊥ X₄ | X₂`
imply `X₃ ⊥ X₄`. -/
theorem example_15_17 [∀ i, Finite (A i)] (hμ : IsPMF μ) {X : ∀ i, Ω → A i}
    (h₁ : IndepRV μ (X 0) (X 1))
    (h₂ : CondIndep μ (X 0) (X 1) (X 2)) (h₃ : CondIndep μ (X 2) (X 3) (X 0))
    (h₄ : CondIndep μ (X 2) (X 3) (X 1)) : IndepRV μ (X 2) (X 3) := by
  have _ : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite (A i)
  have := zhangYeung_constrained hμ ((mutualInfo_eq_zero_iff hμ _ _).2 h₁)
    ((condMutualInfo_eq_zero_iff hμ _ _ _).2 h₂)
  rw [(condMutualInfo_eq_zero_iff hμ _ _ _).2 h₃, (condMutualInfo_eq_zero_iff hμ _ _ _).2 h₄]
    at this
  exact (mutualInfo_eq_zero_iff hμ _ _).1
    (le_antisymm (by linarith) (mutualInfo_nonneg hμ _ _))

lemma condInfo_zyPoint_two_three : condInfo (zyPoint 1).extend {2} {3} ∅ = 1 := by
  rw [condInfo_zyPoint, one_mul]
  have : ((((zyNat (∅ ∪ {2}) + zyNat (∅ ∪ {3}) : ℕ) : ℤ) - zyNat (∅ ∪ {2} ∪ {3}) -
      zyNat ∅ : ℤ) : ℝ) = 1 := by norm_cast
  exact this

/-- **Example 15.17**: the implication (15.152) does not follow from the basic inequalities, as
`h̃(1) ∈ Γ₄` meets its four constraints but not `I(X₃; X₄) = 0`. -/
theorem example_15_17_not_shannon : ∃ h ∈ shannonRegion (Fin 4),
    condInfo h.extend {0} {1} ∅ = 0 ∧ condInfo h.extend {0} {1} {2} = 0 ∧
      condInfo h.extend {2} {3} {0} = 0 ∧ condInfo h.extend {2} {3} {1} = 0 ∧
        condInfo h.extend {2} {3} ∅ ≠ 0 :=
  ⟨zyPoint 1, zyPoint_mem_shannonRegion zero_le_one, condInfo_zyPoint_zyMeasures 1 0,
    condInfo_zyPoint_zyMeasures 1 1, condInfo_zyPoint_zyMeasures 1 7,
    condInfo_zyPoint_zyMeasures 1 8, by rw [condInfo_zyPoint_two_three]; exact one_ne_zero⟩

omit [∀ i, Fintype (A i)] in
/-- **Example 15.18**, (15.155): `X₁ ⊥ X₂`, `X₁ ⊥ (X₃, X₄)`, `X₃ ⊥ X₄ | X₁` and `X₃ ⊥ X₄ | X₂`
imply `X₃ ⊥ X₄`, by (15.62). -/
theorem example_15_18 [∀ i, Finite (A i)] (hμ : IsPMF μ) {X : ∀ i, Ω → A i}
    (h₁ : IndepRV μ (X 0) (X 1))
    (h₂ : IndepRV μ (X 0) (pair (X 2) (X 3))) (h₃ : CondIndep μ (X 2) (X 3) (X 0))
    (h₄ : CondIndep μ (X 2) (X 3) (X 1)) : IndepRV μ (X 2) (X 3) := by
  have _ : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite (A i)
  have := zhangYeung hμ X
  rw [(mutualInfo_eq_zero_iff hμ _ _).2 h₁, (mutualInfo_eq_zero_iff hμ _ _).2 h₂,
    (condMutualInfo_eq_zero_iff hμ _ _ _).2 h₃, (condMutualInfo_eq_zero_iff hμ _ _ _).2 h₄]
    at this
  exact (mutualInfo_eq_zero_iff hμ _ _).1
    (le_antisymm (by linarith) (mutualInfo_nonneg hμ _ _))

/-- **Example 15.18**, corrected: on `Γ₄`, `I(X₁; X₃, X₄) = 0` and `I(X₃; X₄ | X₁) = 0` already
give `I(X₃; X₄) = 0`, so the implication (15.155) follows from the basic inequalities, contrary to
the book. -/
theorem example_15_18_shannon {h : EntropySpace (Fin 4)} (hh : h ∈ shannonRegion (Fin 4))
    (h₁ : condInfo h.extend {0} {2, 3} ∅ = 0) (h₂ : condInfo h.extend {2} {3} {0} = 0) :
    condInfo h.extend {2} {3} ∅ = 0 := by
  rw [mem_shannonRegion_iff] at hh
  set f := h.extend
  rw [condInfo_eq_of f (U₁ := {0}) (U₂ := {2, 3}) (U₃ := {0, 2, 3}) (by decide) (by decide)
    (by decide)] at h₁
  rw [condInfo_eq_of f (U₁ := {0, 2}) (U₂ := {0, 3}) (U₃ := {0, 2, 3}) (by decide) (by decide)
    (by decide)] at h₂
  have n := hh.condInfo_nonneg {2} {3} ∅
  rw [condInfo_eq_of f (U₁ := {2}) (U₂ := {3}) (U₃ := {2, 3}) (by decide) (by decide)
    (by decide)] at n ⊢
  have s₁ := hh.submod {0, 2} {2, 3}
  have s₂ := hh.submod {0, 3} {2, 3}
  rw [show ({0, 2} ∪ {2, 3} : Finset (Fin 4)) = {0, 2, 3} by decide,
    show ({0, 2} ∩ {2, 3} : Finset (Fin 4)) = {2} by decide] at s₁
  rw [show ({0, 3} ∪ {2, 3} : Finset (Fin 4)) = {0, 2, 3} by decide,
    show ({0, 3} ∩ {2, 3} : Finset (Fin 4)) = {3} by decide] at s₂
  have e := hh.empty
  exact le_antisymm (by linarith) n

/-- **Example 15.19.** For a fault-tolerant data storage system, `H(Xᵢ | Xⱼ, j ≠ i) = 0` (15.156),
(15.62) is a non-Shannon-type inequality. -/
theorem example_15_19 : ¬IsShannonType zyCoeff {h | ∀ k ∈ ({10, 11, 12, 13} : Finset (Fin 14)),
    condInfo h.extend (zyMeasures k).1 (zyMeasures k).2.1 (zyMeasures k).2.2 = 0} :=
  not_isShannonType_zyCoeff_constrained _

/-- **Example 15.20**, (15.161): adding (15.62) and its version (15.160) with `X₁` and `X₂`
exchanged gives
`I(X₃; X₄) ≤ I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂) + I(X₁; X₂) / 2 + I(X₁; X₃, X₄) / 4 +
I(X₂; X₃, X₄) / 4`. -/
theorem example_15_20 (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    I[X 2 : X 3 ; μ] ≤ I[X 2 : X 3 | X 0 ; μ] + I[X 2 : X 3 | X 1 ; μ] + I[X 0 : X 1 ; μ] / 2 +
      I[X 0 : pair (X 2) (X 3) ; μ] / 4 + I[X 1 : pair (X 2) (X 3) ; μ] / 4 := by
  have h₁ := zhangYeung hμ X
  have h₂ : 2 * I[X 2 : X 3 ; μ] ≤ I[X 1 : X 0 ; μ] + I[X 1 : pair (X 2) (X 3) ; μ] +
      3 * I[X 2 : X 3 | X 1 ; μ] + I[X 2 : X 3 | X 0 ; μ] :=
    zhangYeung hμ (A := fun i => A (![1, 0, 2, 3] i)) fun i => X (![1, 0, 2, 3] i)
  rw [mutualInfo_comm hμ (X 1) (X 0)] at h₂
  linarith

/-- **Example 15.20.** (15.62) is a non-Shannon-type inequality under the Markov condition
`X₃ → (X₁, X₂) → X₄` (15.158). -/
theorem example_15_20_markov : ¬IsShannonType zyCoeff {h | ∀ k ∈ ({9} : Finset (Fin 14)),
    condInfo h.extend (zyMeasures k).1 (zyMeasures k).2.1 (zyMeasures k).2.2 = 0} :=
  not_isShannonType_zyCoeff_constrained _

end Applications

end InfoTheory.Yeung
