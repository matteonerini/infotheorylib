/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.IMeasure.MarkovField

/-!
# Yeung, Chapter 12: Markov Structures

This file indexes the formalization of Chapter 12 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Indexing.** The variables are `X i` with `i : ι`, for a finite type `ι` such as `Fin n`, whose
  elements start at `0`: the book's `X₁` is `X 0`.
* **Atoms.** A nonempty atom `A` of `Fₙ` is `a : NAtom ι`, the set `a.1` of indices that are not
  complemented in `A` (Chapter 3). The book's `U_A` of (12.73) is `a.1ᶜ`, and the weight `w(A)` is
  `#a.1`.
* **Blocks.** A collection `X_Q = (Xₗ, l ∈ Q)` is `blockRV X Q`, and the joint entropies are
  `blockEntropy μ X Q`.
* **Conditional mutual independencies.** `K = (T, Qᵢ, 1 ≤ i ≤ k)` is `FCMI.mk T 𝒬` with
  `𝒬 = {Q₁, …, Q_k}` a set of index sets, and `K` holds if `CondMutIndep` holds for the blocks
  `X_{Qᵢ}` given `X_T`. A conditional mutual independency is a family `Zⱼ`, `j ∈ κ`, conditioning
  on `Y`, and `κ` may contain indices with constant `Zⱼ`, which do not change the independence.
* **Graphs.** A graph is a `SimpleGraph ι`, which has no loops. `G \ U` is not built as a graph:
  `ReachableOutside G U l l'` says that some walk of `G` from `l` to `l'` avoids `U`. The chain of
  Figure 12.6 is Mathlib's `SimpleGraph.pathGraph n`.
* **Markov chains.** A Markov chain is either a Markov random field on `pathGraph n`, as in
  Section 12.4, or `IsMarkovChain μ Z n` of Definition 2.6. Theorem 12.30 is proved for both.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 12.1 Conditional Mutual Independence
* (12.1): `iMeasure_atoms_markov_four` (`IMeasure.Markov`).
* Example 12.1: `example_12_1` (here).
* Mutual independence conditioning on `Y`: `CondMutIndep` (`MutualInformation.CondMutIndep`).
* Theorem 12.2: `theorem_12_2` (here), which is `condMutIndep_iff_condEntropy_eq_sum`
  (`MutualInformation.CondMutIndep`). For blocks of variables: `condMutIndep_blocks_iff_sum`
  (`IMeasure.CondMutIndep`).
* Theorem 12.3: `theorem_12_3` (here), which is `condMutIndep_iff_condMutualInfo_eq_zero`, with the
  conditional independencies `condMutIndep_iff_condIndep` (`MutualInformation.CondMutIndep`). For
  blocks: `condMutIndep_blocks_iff_condInfo` (`IMeasure.CondMutIndep`).
* Theorem 12.4: `theorem_12_4` (here), which is `condMutIndep_iff_condEntropy_eq_sum_condEntropy`
  (`MutualInformation.CondMutIndep`).
* (12.18) and (12.22), the chain rule: `condEntropy_blockRV_insert`
  (`MutualInformation.CondMutIndep`).
* Theorem 12.5: `theorem_12_5` (here), which is `condMutIndep_blocks_sdiff`
  (`IMeasure.CondMutIndep`), stated for all the `Wᵢ`. The inequalities of the proof are
  `IsPolymatroid.sub_le_sub` and `IsPolymatroid.sub_le_sum` (`InfoInequalities.Polymatroid`).
* Example 12.6: `example_12_6` (here).
* Lemma 12.7: `lemma_12_7` (here), which is `iMeasure_inf_sdiff_eq_zero_of_condMutIndep`, with
  the case `r = 2` in `iMeasure_inf_sdiff_eq_zero_of_condInfo` (`IMeasure.CondMutIndep`).
* Lemma 12.8: `lemma_12_8` (here), which is `IsSignedMeasure.inf_inter_inf_sdiff_eq_sum`
  (`IMeasure.CondMutIndep`), for nonempty `S` and `T`, which (12.44) needs.
* Theorem 12.9: `theorem_12_9` (here), which is `condMutIndep_blocks_iff_iMeasure`
  (`IMeasure.CondMutIndep`).
* Example 12.10: `example_12_10` (here).

### 12.2 Full Conditional Mutual Independence
* Definition 12.11: `FCMI`, `FCMI.IsFull`, `FCMI.Holds` (`IMeasure.CondMutIndep`).
* Example 12.12: `example_12_12` (here).
* Definition 12.13: `FCMI.image`, `FCMI.mem_image` (`IMeasure.CondMutIndep`).
* Proposition 12.14: `proposition_12_14` (here), which is `FCMI.mem_image_iff_of_parts_eq_pair`
  (`IMeasure.CondMutIndep`).
* Proposition 12.15: `proposition_12_15` (here), which is `FCMI.mem_image_iff`
  (`IMeasure.CondMutIndep`).
* Example 12.16: `example_12_16` (here).
* Theorem 12.17: `theorem_12_17` (here), which is `FCMI.holds_iff` (`IMeasure.CondMutIndep`), with
  (12.72) in `FCMI.inf_tilde_sdiff_eq_singleton`.
* Definition 12.18: `fcmiImage` (`IMeasure.CondMutIndep`).
* Theorem 12.19: `theorem_12_19` (here), which is `FCMI.holds_set_iff` (`IMeasure.CondMutIndep`).
* Theorem 12.20: `theorem_12_20` (here), which is `FCMI.implies_iff`, with the implication
  `FCMI.Implies` (`IMeasure.CondMutIndep`).
* Corollary 12.21: `corollary_12_21` (here), which is `FCMI.equiv_iff` (`IMeasure.CondMutIndep`).
* Example 12.22: `example_12_22` (here).

### 12.3 Markov Random Field
* `G \ U`, its components and `s(U)`: `ReachableOutside`, `componentsOutside`,
  `one_lt_card_componentsOutside` (`IMeasure.MarkovField`).
* Definition 12.23 and (12.88)–(12.89): `IsMarkovField`, `cutFCMI`, `isFull_cutFCMI`
  (`IMeasure.MarkovField`).
* Definition 12.24: `IsTypeTwoAtom` (`IMeasure.MarkovField`).
* Theorem 12.25: `theorem_12_25` (here), which is `isMarkovField_iff`, with (12.91) in
  `fcmiImage_cutFCMI` (`IMeasure.MarkovField`).
* Proposition 12.26: `proposition_12_26` (here), which is `not_reachableOutside_union_sdiff`
  (`IMeasure.MarkovField`).

### 12.4 Markov Chain
* Lemma 12.29: `lemma_12_29` (here), from `not_isTypeTwoAtom_pathGraph_iff` and
  `isTypeTwoAtom_pathGraph_iff` (`IMeasure.MarkovField`).
* (12.103)–(12.110): `iMeasure_Icc_eq_condMutualInfo`, and for a Markov chain
  `IsMarkovChain.iMeasure_Icc` (`IMeasure.MarkovField`).
* Theorem 12.30: `theorem_12_30` (here), which is `IsMarkovChain.iMeasure_nonneg`, with the Type II
  atoms in `IsMarkovChain.iMeasure_eq_zero`; for a Markov random field on a path,
  `IsMarkovField.iMeasure_nonneg_pathGraph` (`IMeasure.MarkovField`). For a Markov chain the
  vanishing on the Type II atoms is proved directly, by splitting the chain at a missing index.

## Not formalized

* Examples 12.27 and 12.28, which read the connectivity of the graphs of Figures 12.4 and 12.5.
  Deciding the connectivity of a concrete graph is not automated here.
* The remark after Theorem 12.17 that an FCMI is determined by its image, (12.75)–(12.76).
* The second half of Example 12.10, which says what Theorem 12.9 does not imply.
* The information diagrams and Figures 12.1 to 12.7, in particular the two-dimensional diagram of a
  Markov chain.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 12
-/

open Real Finset Function

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ}

/-- **Theorem 12.2.** (12.15) -/
alias theorem_12_2 := condMutIndep_iff_condEntropy_eq_sum

/-- **Theorem 12.3.** (12.16) -/
alias theorem_12_3 := condMutIndep_iff_condMutualInfo_eq_zero

/-- **Theorem 12.4.** (12.20) -/
alias theorem_12_4 := condMutIndep_iff_condEntropy_eq_sum_condEntropy

/-- **Theorem 12.5.** -/
alias theorem_12_5 := condMutIndep_blocks_sdiff

/-- **Lemma 12.7.** (12.40) -/
alias lemma_12_7 := iMeasure_inf_sdiff_eq_zero_of_condMutIndep

/-- **Lemma 12.8.** (12.41) -/
alias lemma_12_8 := IsSignedMeasure.inf_inter_inf_sdiff_eq_sum

/-- **Theorem 12.9.** (12.52) -/
alias theorem_12_9 := condMutIndep_blocks_iff_iMeasure

/-- **Proposition 12.14.** (12.68) -/
alias proposition_12_14 := FCMI.mem_image_iff_of_parts_eq_pair

/-- **Proposition 12.15.** (12.69) -/
alias proposition_12_15 := FCMI.mem_image_iff

/-- **Theorem 12.17.** -/
alias theorem_12_17 := FCMI.holds_iff

/-- **Theorem 12.19.** -/
alias theorem_12_19 := FCMI.holds_set_iff

/-- **Theorem 12.20.** -/
alias theorem_12_20 := FCMI.implies_iff

/-- **Corollary 12.21.** -/
alias corollary_12_21 := FCMI.equiv_iff

/-- **Theorem 12.25.** -/
alias theorem_12_25 := isMarkovField_iff

/-- **Proposition 12.26.** -/
alias proposition_12_26 := not_reachableOutside_union_sdiff

/-- **Lemma 12.29.** (12.102) -/
theorem lemma_12_29 {n : ℕ} (a : NAtom (Fin n)) :
    ¬IsTypeTwoAtom (SimpleGraph.pathGraph n) a ↔ ∃ l u, l ≤ u ∧ a.1 = Icc l u :=
  not_isTypeTwoAtom_pathGraph_iff a

/-- **Theorem 12.30.** -/
alias theorem_12_30 := IsMarkovChain.iMeasure_nonneg

/-! ### Examples -/

section Examples

variable {A : Fin 3 → Type*} [∀ i, Fintype (A i)]

/-- The FCMI "`X₁`, `X₂` and `X₃` are mutually independent". -/
def indepThree : FCMI (Fin 3) := ⟨∅, {{0}, {1}, {2}}⟩

lemma isFull_indepThree : indepThree.IsFull := by
  rw [FCMI.isFull_iff]
  decide

/-- **Example 12.1.** `X₁`, `X₂` and `X₃` are mutually independent if and only if `μ*` vanishes on
the atoms in the intersection of two of the `X̃ᵢ`, (12.12)–(12.13). -/
theorem example_12_1 (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    indepThree.Holds μ X ↔ ∀ a : NAtom (Fin 3), 2 ≤ #a.1 → iMeasure μ X {a} = 0 := by
  have key : ∀ a : NAtom (Fin 3), a ∈ indepThree.image ↔ 2 ≤ #a.1 := by
    intro a
    rw [FCMI.mem_image_iff isFull_indepThree]
    simp only [mem_sdiff, mem_inter, mem_tilde]
    revert a
    decide
  rw [FCMI.holds_iff hμ isFull_indepThree]
  exact forall_congr' fun a => by rw [key]

variable {A : Fin 7 → Type*} [∀ i, Fintype (A i)]

omit [∀ i, Fintype (A i)] in
/-- **Example 12.6.** If `X₁`, `(X₂, X₃, X₄)` and `(X₅, X₆)` are mutually independent
conditioning on `X₇`, then `X₁`, `X₂` and `(X₅, X₆)` are mutually independent conditioning on
`(X₃, X₄, X₇)`. -/
theorem example_12_6 [∀ i, Finite (A i)] (hμ : IsPMF μ) (X : ∀ i, Ω → A i)
    (h : CondMutIndep μ (fun j : Fin 3 => blockRV X (![{0}, {1, 2, 3}, {4, 5}] j))
      (blockRV X {6})) :
    CondMutIndep μ (fun j : Fin 3 => blockRV X (![{0}, {1}, {4, 5}] j)) (blockRV X {2, 3, 6}) := by
  have h' := condMutIndep_blocks_sdiff hμ (W := ![{0}, {1}, {4, 5}]) (by decide) h
  have e : ({6} ∪ univ.biUnion fun j : Fin 3 =>
      (![{0}, {1, 2, 3}, {4, 5}] j : Finset (Fin 7)) \ ![{0}, {1}, {4, 5}] j) = {2, 3, 6} := by
    decide
  rwa [e] at h'

/-- **Example 12.10.** Under the same mutual independence as in Example 12.6,
`μ*(X̃₁ ∩ X̃₂ ∩ X̃₅ ∩ X̃₆ - (X̃₃ ∪ X̃₄ ∪ X̃₇)) = 0` (12.53). -/
theorem example_12_10 (hμ : IsPMF μ) (X : ∀ i, Ω → A i)
    (h : CondMutIndep μ (fun j : Fin 3 => blockRV X (![{0}, {1, 2, 3}, {4, 5}] j))
      (blockRV X {6})) :
    iMeasure μ X (({0, 1, 4, 5} : Finset (Fin 7)).inf (fun l => tilde {l}) \ tilde {2, 3, 6}) =
      0 := by
  have hQ : Pairwise
      (Disjoint on fun j : Fin 3 => (![{0}, {1, 2, 3}, {4, 5}] j : Finset (Fin 7))) := by
    unfold Pairwise onFun
    decide
  have h' := (condMutIndep_blocks_iff_iMeasure hμ hQ).1 h ![{0}, {1}, {4, 5}] (by decide)
    ⟨0, 1, by decide, by decide, by decide⟩
  have e₁ : (univ.biUnion fun j : Fin 3 => (![{0}, {1}, {4, 5}] j : Finset (Fin 7))) =
      {0, 1, 4, 5} := by decide
  have e₂ : ({6} ∪ univ.biUnion fun j : Fin 3 =>
      (![{0}, {1, 2, 3}, {4, 5}] j : Finset (Fin 7)) \ ![{0}, {1}, {4, 5}] j) = {2, 3, 6} := by
    decide
  rwa [e₁, e₂] at h'

/-- **Example 12.12.** For `n = 5`, "`X₁`, `X₂`, `X₄` and `X₅` are mutually independent
conditioning on `X₃`" is an FCMI, while "`X₁`, `X₂` and `X₅` are mutually independent conditioning
on `X₃`" is not. -/
theorem example_12_12 :
    (FCMI.mk ({2} : Finset (Fin 5)) {{0}, {1}, {3}, {4}}).IsFull ∧
      ¬(FCMI.mk ({2} : Finset (Fin 5)) {{0}, {1}, {4}}).IsFull := by
  refine ⟨by rw [FCMI.isFull_iff]; decide, fun h => ?_⟩
  have h₃ := (FCMI.isFull_iff.1 h).2.2
  revert h₃
  decide

/-- **Example 12.16.** For `n = 4`, `Im(K₁)` and `Im(K₂)` for `K₁ = ({3}, {1}, {2, 4})` and
`K₂ = (∅, {1}, {2, 3}, {4})`, (12.70)–(12.71). -/
theorem example_12_16 (a : NAtom (Fin 4)) :
    (a ∈ (FCMI.mk {2} {{0}, {1, 3}}).image ↔ a ∈ (tilde {0} ∩ tilde {1, 3}) \ tilde {2}) ∧
      (a ∈ (FCMI.mk ∅ {{0}, {1, 2}, {3}}).image ↔
        a ∈ (tilde {0} ∩ tilde {1, 2}) ∪ (tilde {1, 2} ∩ tilde {3}) ∪ (tilde {0} ∩ tilde {3})) := by
  have h₁ : (FCMI.mk ({2} : Finset (Fin 4)) {{0}, {1, 3}}).IsFull := by
    rw [FCMI.isFull_iff]
    decide
  have h₂ : (FCMI.mk (∅ : Finset (Fin 4)) {{0}, {1, 2}, {3}}).IsFull := by
    rw [FCMI.isFull_iff]
    decide
  refine ⟨FCMI.mem_image_iff_of_parts_eq_pair h₁ (by decide) rfl, ?_⟩
  rw [FCMI.mem_image_iff h₂]
  simp only [mem_sdiff, mem_inter, mem_union, mem_tilde]
  revert a
  decide

/-- The FCMIs `K₁ = (∅, {1, 2, 3}, {4})`, `K₂ = (∅, {1, 2, 4}, {3})`, `K₃ = (∅, {1, 2}, {3, 4})`
and `K₄ = (∅, {1, 3}, {2, 4})` of Example 12.22, (12.80)–(12.81). -/
def example1222K : Fin 4 → FCMI (Fin 4) :=
  ![⟨∅, {{0, 1, 2}, {3}}⟩, ⟨∅, {{0, 1, 3}, {2}}⟩, ⟨∅, {{0, 1}, {2, 3}}⟩, ⟨∅, {{0, 2}, {1, 3}}⟩]

lemma isFull_example1222K (i : Fin 4) : (example1222K i).IsFull := by
  rw [FCMI.isFull_iff]
  revert i
  decide

/-- The images in Example 12.22, (12.84)–(12.87). -/
lemma mem_image_example1222K (a : NAtom (Fin 4)) :
    (a ∈ (example1222K 0).image ↔ a ∈ tilde {0, 1, 2} ∩ tilde {3}) ∧
      (a ∈ (example1222K 1).image ↔ a ∈ tilde {0, 1, 3} ∩ tilde {2}) ∧
        (a ∈ (example1222K 2).image ↔ a ∈ tilde {0, 1} ∩ tilde {2, 3}) ∧
          (a ∈ (example1222K 3).image ↔ a ∈ tilde {0, 2} ∩ tilde {1, 3}) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [FCMI.mem_image_iff_of_parts_eq_pair (isFull_example1222K _) (by decide) rfl]
    simp [example1222K, tilde_empty]

/-- **Example 12.22.** `Π₂ = {K₃, K₄}` implies `Π₁ = {K₁, K₂}`, because `Im(Π₁) ⊆ Im(Π₂)`. -/
theorem example_12_22 :
    FCMI.Implies {example1222K 2, example1222K 3} {example1222K 0, example1222K 1} := by
  have hfull : ∀ P : Set (FCMI (Fin 4)), P ⊆ Set.range example1222K → ∀ K ∈ P, K.IsFull :=
    fun P hP K hK => by
      obtain ⟨i, rfl⟩ := hP hK
      exact isFull_example1222K i
  have hr : ∀ i j, ({example1222K i, example1222K j} : Set (FCMI (Fin 4))) ⊆
      Set.range example1222K := fun i j => by
    rintro K (rfl | rfl) <;> exact ⟨_, rfl⟩
  rw [FCMI.implies_iff (hfull _ (hr 2 3)) (hfull _ (hr 0 1))]
  intro a ha
  simp only [fcmiImage, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, mem_coe,
    exists_prop, exists_eq_or_imp, exists_eq_left] at ha ⊢
  obtain ⟨h₀, h₁, h₂, h₃⟩ := mem_image_example1222K a
  rw [h₀, h₁] at ha
  rw [h₂, h₃]
  clear h₀ h₁ h₂ h₃
  simp only [mem_inter, mem_tilde] at ha ⊢
  revert a
  decide

end Examples

end InfoTheory.Yeung
