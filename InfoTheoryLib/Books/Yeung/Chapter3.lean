/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Concavity
public import InfoTheoryLib.IMeasure.Markov
public import InfoTheoryLib.IMeasure.Realization
public import InfoTheoryLib.MutualInformation.Convexity

/-!
# Yeung, Chapter 3: The I-Measure

This file indexes the formalization of Chapter 3 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **The field.** `Fₙ` is modelled by its atoms: a set of the field is a `Finset` of atoms, and a
  signed measure is a function on these. In Section 3.1 an atom is any subset of the indices; from
  Section 3.3 on, the empty atom is removed, leaving `NAtom ι`. The book's assumption that the sets
  intersect generically is built into this model.
* **Indexing.** The variables are `X i` with `i : ι`, for a finite type `ι`, such as `Fin n`, whose
  elements start at `0`: the book's `X₁` is `X 0`.
* **Three or more sets.** The book's `I(X₁; X₂; X₃)` has no separate name here. It is
  `iMeasure μ X (tilde {0} ∩ tilde {1} ∩ tilde {2})`.
* **Logarithms.** All quantities are in nats. The value `-1` of Example 3.10, in bits, is `-log 2`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 3.1 Preliminaries
* Definition 3.1: `baseSet`, `closure_range_baseSet` (`IMeasure.SignedMeasure`).
* Definition 3.2: `singleton_eq_inf_baseSet` (`IMeasure.SignedMeasure`).
* Example 3.3: `example_3_3` (here).
* Definition 3.4 and (3.3): `IsSignedMeasure`, `IsSignedMeasure.map_empty`
  (`IMeasure.SignedMeasure`).
* Specification by the atoms: `IsSignedMeasure.eq_sum_singleton` (`IMeasure.SignedMeasure`).
* Example 3.5: `IsSignedMeasure.eq_inter_add_sdiff` (`IMeasure.SignedMeasure`).

### 3.2 The I-Measure for Two Random Variables
* (3.10)–(3.15), the case of two variables: `iMeasure_sdiff`, `iMeasure_inter`, `iMeasure_tilde`
  (`IMeasure.Basic`).
* (3.20): `IsSignedMeasure.inter_sdiff_eq_union` (`IMeasure.SignedMeasure`) with `C = ∅`.
* (3.21): `mutualInfo_eq_add_sub` (`MutualInformation.Basic`).

### 3.3 Construction of the I-Measure
* (3.22)–(3.26): `NAtom`, `card_nAtom`, `tilde`, `tilde_univ` (`IMeasure.SignedMeasure`).
* Theorem 3.6: `existsUnique_isSignedMeasure_tilde` (`IMeasure.SignedMeasure`).
* (3.28) and (3.29): `IsSignedMeasure.inter_sdiff_eq`, `IsSignedMeasure.sdiff_eq`
  (`IMeasure.SignedMeasure`).
* Lemma 3.7: `IsSignedMeasure.inter_sdiff_eq_union` (`IMeasure.SignedMeasure`).
* Lemma 3.8: `lemma_3_8` (here).
* (3.40): `iMeasure`, `iMeasure_tilde` (`IMeasure.Basic`).
* (3.41)–(3.44): `iMeasure_consistent`, `iMeasure_inter`, `iMeasure_sdiff`, `iMeasure_tilde`
  (`IMeasure.Basic`).
* Theorem 3.9: `theorem_3_9` (here).

### 3.4 `μ*` Can be Negative
* (3.51)–(3.52): `iMeasure_atom_singleton`, `iMeasure_atom_pair`, `iMeasure_atom_nonneg`
  (`IMeasure.Basic`), for any number of variables.
* Nonnegativity for `n = 2`: `iMeasure_nonneg_of_card_two` (`IMeasure.Basic`).
* Example 3.10: `example_3_10` (here).
* (3.64) and (3.70): `IsSignedMeasure.inter_inter_sdiff_eq` (`IMeasure.SignedMeasure`),
  `iMeasure_inter_inter_sdiff` (`IMeasure.Basic`).

### 3.5 Information Diagrams
* Theorem 3.11: `exists_iMeasure_eq` (`IMeasure.Realization`).
* (3.73), for independent variables: `entropy_prodLaw_blockRV` (`IMeasure.Realization`).
* (3.77)–(3.81), Markov chains of three variables: `iMeasure_atom_markov_three`,
  `iMeasure_inter_markov_three`, `iMeasure_nonneg_markov_three` (`IMeasure.Markov`).
* (3.91)–(3.96), the five atoms for four variables: `iMeasure_atoms_markov_four`
  (`IMeasure.Markov`).
* (3.97)–(3.98), the values of `μ*` on the other ten atoms for a Markov chain, and its
  nonnegativity: `IsMarkovChain.iMeasure_Icc`, `iMeasure_atom_singleton` and
  `IsMarkovChain.iMeasure_nonneg` (`IMeasure.MarkovField`, `IMeasure.Basic`), for chains of any
  length. The book defers the proof to Theorem 12.30.

### 3.6 Examples of Applications
* Example 3.12: `entropy_concaveOn` (`Entropy.Concavity`), by another proof.
* Example 3.13: `mutualInfoOf_convex_channel` (`MutualInformation.Convexity`), by another proof.
* Example 3.14: `mutualInfoOf_concave_input` (`MutualInformation.Convexity`), by another proof.
* Examples 3.15, 3.16 and 3.18: `example_3_15`, `example_3_16`, `example_3_18` (here).
* Example 3.17: `IsMarkovChain.data_processing` (`MarkovChain.Sequence`).

### Appendix 3.A
* Theorem 3.19: `IsSignedMeasure.inf_sdiff_eq_sum` (`IMeasure.SignedMeasure`).
* (3.148)–(3.149): `singleton_eq_inf_tilde`, `IsSignedMeasure.singleton_eq_atomValue`
  (`IMeasure.SignedMeasure`).

## Not formalized

* Information diagrams as pictures, and Figures 3.1 to 3.21. The proofs here use the identities that
  the diagrams display.
* The substitution of symbols (3.19), which is a remark about notation.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 3
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

/-! ### Worked examples -/

/-- **Example 3.3.** Two sets generate a field with four atoms and sixteen sets. -/
theorem example_3_3 :
    Fintype.card (Finset (Fin 2)) = 4 ∧ Fintype.card (Finset (Finset (Fin 2))) = 16 := by
  simp [Fintype.card_finset]

section Example310

/-- The uniform distribution on two independent fair bits, of **Example 3.10**. -/
def example_3_10_μ : Bool × Bool → ℝ := fun _ => 1 / 4

/-- The variables of **Example 3.10**: two independent fair bits, and their sum modulo `2`, (3.54).
-/
def example_3_10_X : Fin 3 → Bool × Bool → Bool :=
  ![Prod.fst, Prod.snd, fun ω => xor ω.1 ω.2]

lemma example_3_10_isPMF : IsPMF example_3_10_μ :=
  ⟨fun _ => by norm_num [example_3_10_μ], by simp [example_3_10_μ]⟩

lemma example_3_10_dist₀ (a : Bool) : dist example_3_10_μ (example_3_10_X 0) a = 1 / 2 := by
  cases a <;> simp [dist, example_3_10_μ, example_3_10_X, Fintype.sum_prod_type] <;> norm_num

lemma example_3_10_indep₀₁ : IndepRV example_3_10_μ (example_3_10_X 0) (example_3_10_X 1) := by
  intro a b
  cases a <;> cases b <;>
    simp [dist, pair, example_3_10_μ, example_3_10_X, Fintype.sum_prod_type] <;> norm_num

lemma example_3_10_indep₀₂ : IndepRV example_3_10_μ (example_3_10_X 0) (example_3_10_X 2) := by
  intro a b
  cases a <;> cases b <;>
    simp [dist, pair, example_3_10_μ, example_3_10_X, Fintype.sum_prod_type] <;> norm_num

lemma example_3_10_entropy₀ : H[example_3_10_X 0 ; example_3_10_μ] = log 2 := by
  have e : dist example_3_10_μ (example_3_10_X 0) = uniformPMF Bool := by
    funext a
    rw [example_3_10_dist₀]
    simp [uniformPMF]
  rw [entropyRV, e, (entropy_eq_log_card_iff uniformPMF_isPMF).2 rfl]
  simp

/-- (3.71)'s ingredient (3.63): `I(X₁; X₂ | X₃) = log 2`, one bit. -/
lemma example_3_10_condMutualInfo :
    I[example_3_10_X 0 : example_3_10_X 1 | example_3_10_X 2 ; example_3_10_μ] = log 2 := by
  have hμ := example_3_10_isPMF
  have h₀ :
      H[example_3_10_X 0 | pair (example_3_10_X 1) (example_3_10_X 2) ; example_3_10_μ] = 0 := by
    have e : example_3_10_X 0 =
        (fun t : Bool × Bool => xor t.1 t.2) ∘ pair (example_3_10_X 1) (example_3_10_X 2) := by
      funext ω
      obtain ⟨a, b⟩ := ω
      cases a <;> cases b <;> rfl
    rw [e]
    exact condEntropy_comp_self hμ _ _
  have h₁ : H[example_3_10_X 0 | example_3_10_X 2 ; example_3_10_μ] = log 2 := by
    rw [(condEntropy_eq_entropy_iff hμ _ _).2 example_3_10_indep₀₂, example_3_10_entropy₀]
  rw [condMutualInfo, h₀, h₁, sub_zero]

/-- **Example 3.10.** For two independent fair bits `X₁`, `X₂` and `X₃ = X₁ + X₂ mod 2`,
`μ*(X̃₁ ∩ X̃₂ ∩ X̃₃) = -log 2`, which is `-1` in bits: the I-Measure can be negative, and (3.71)
conditioning can increase the mutual information. -/
theorem example_3_10 :
    iMeasure example_3_10_μ example_3_10_X (tilde {0} ∩ tilde {1} ∩ tilde {2}) = -log 2 ∧
      I[example_3_10_X 0 : example_3_10_X 1 ; example_3_10_μ] <
        I[example_3_10_X 0 : example_3_10_X 1 | example_3_10_X 2 ; example_3_10_μ] := by
  have hμ := example_3_10_isPMF
  have hI : I[example_3_10_X 0 : example_3_10_X 1 ; example_3_10_μ] = 0 :=
    (mutualInfo_eq_zero_iff hμ _ _).2 example_3_10_indep₀₁
  have hlog : 0 < log 2 := log_pos one_lt_two
  refine ⟨?_, by rw [hI, example_3_10_condMutualInfo]; exact hlog⟩
  have hm := isSignedMeasure_iMeasure example_3_10_μ example_3_10_X
  have h₀ := hm.inter_inter_sdiff_eq (tilde {0}) (tilde {1}) ∅ (tilde {2})
  rw [sdiff_empty, sdiff_empty, empty_union] at h₀
  rw [h₀, iMeasure_inter hμ (rvEquiv_blockRV_singleton _ 0) (rvEquiv_blockRV_singleton _ 1), hI,
    iMeasure_inter_sdiff hμ (rvEquiv_blockRV_singleton _ 0) (rvEquiv_blockRV_singleton _ 1)
      (rvEquiv_blockRV_singleton _ 2), example_3_10_condMutualInfo, zero_sub]

end Example310

/-- **Example 3.15 (Imperfect Secrecy Theorem).** If the plain text `X` can be recovered from the
cipher text `Y` and the key `Z`, then `I(X; Y) ≥ H(X) - H(Z)`, (3.122)–(3.123). -/
theorem example_3_15 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (h : H[X | pair Y Z ; μ] = 0) : H[X ; μ] - H[Z ; μ] ≤ I[X : Y ; μ] := by
  have h₁ := condMutualInfo_eq' hμ X Z Y
  have h₂ := condMutualInfo_eq_sub_right hμ X Z Y
  rw [h, sub_zero] at h₁
  have h₃ := condEntropy_nonneg hμ Z (pair X Y)
  have h₄ := condEntropy_le_entropy hμ Z Y
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ]
  linarith

/-- **Example 3.16.** For a Markov chain `X → Y → Z`: (3.134) `I(X; Y) = I(X; Y, Z)`,
(3.135) `H(X | Y) = H(X | Y, Z)`, (3.136) `I(X; Z) ≤ I(X; Y)` and (3.137) `H(X | Y) ≤ H(X | Z)`. -/
theorem example_3_16 {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : MarkovChain μ X Y Z) :
    I[X : Y ; μ] = I[X : pair Y Z ; μ] ∧ H[X | Y ; μ] = H[X | pair Y Z ; μ] ∧
      I[X : Z ; μ] ≤ I[X : Y ; μ] ∧ H[X | Y ; μ] ≤ H[X | Z ; μ] := by
  have h₁ := (mutualInfo_pair_eq_iff hμ X Y Z).2 h
  have h₂ := data_processing hμ h
  have e₁ := mutualInfo_eq_entropy_sub_condEntropy hμ X Y
  have e₂ := mutualInfo_eq_entropy_sub_condEntropy hμ X (pair Y Z)
  have e₃ := mutualInfo_eq_entropy_sub_condEntropy hμ X Z
  exact ⟨h₁.symm, by linarith, h₂, by linarith⟩

/-- **Example 3.18.** If `X → Y → Z → T → U` is a Markov chain, then
`H(Y) + H(T) = I(Z; X, Y, T, U) + I(X, Y; T, U) + H(Y | Z) + H(T | Z)`, (3.139). -/
theorem example_3_18 {A : ℕ → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ} (hμ : IsPMF μ)
    {X : ∀ i, Ω → A i} (h : IsMarkovChain μ X 5) :
    H[X 1 ; μ] + H[X 3 ; μ] =
      I[X 2 : pair (pair (X 0) (X 1)) (pair (X 3) (X 4)) ; μ] +
        I[pair (X 0) (X 1) : pair (X 3) (X 4) ; μ] + H[X 1 | X 2 ; μ] + H[X 3 | X 2 ; μ] := by
  set E := blockEntropy μ X with hE
  -- blocks as pairs of variables
  have sing := rvEquiv_blockRV_singleton X
  have pr : ∀ {i j : ℕ} {s : Finset ℕ}, {i} ∪ {j} = s →
      RVEquiv (pair (X i) (X j)) (blockRV X s) := by
    intro i j s hs
    rw [← hs]
    exact ((sing i).pair (sing j)).trans (rvEquiv_blockRV_union X {i} {j})
  have p₀₁ := pr (i := 0) (j := 1) (s := {0, 1}) (by decide)
  have p₃₄ := pr (i := 3) (j := 4) (s := {3, 4}) (by decide)
  have p₁₂ : RVEquiv (pair (X 2) (X 1)) (blockRV X {1, 2}) := pr (by decide)
  have p₂₃ : RVEquiv (pair (X 2) (X 3)) (blockRV X {2, 3}) := pr (by decide)
  have q : RVEquiv (pair (pair (X 0) (X 1)) (pair (X 3) (X 4))) (blockRV X {0, 1, 3, 4}) := by
    have := (p₀₁.pair p₃₄).trans (rvEquiv_blockRV_union X {0, 1} {3, 4})
    rwa [show ({0, 1} : Finset ℕ) ∪ {3, 4} = {0, 1, 3, 4} by decide] at this
  have r : RVEquiv (pair (X 2) (pair (pair (X 0) (X 1)) (pair (X 3) (X 4))))
      (blockRV X {0, 1, 2, 3, 4}) := by
    have := ((sing 2).pair q).trans (rvEquiv_blockRV_union X {2} {0, 1, 3, 4})
    rwa [show ({2} : Finset ℕ) ∪ {0, 1, 3, 4} = {0, 1, 2, 3, 4} by decide] at this
  -- the three Markov chains that are used
  have key : ∀ {P S F U₁ U₂ U₃ : Finset ℕ} {b : ℕ}, b ∈ S → (∀ i ∈ P, i < b) →
      (∀ i ∈ S, b ≤ i ∧ i < 5) → (∀ i ∈ F, b ≤ i ∧ i < 5) → S ∪ P = U₁ → S ∪ F = U₂ →
        S ∪ (P ∪ F) = U₃ → E U₁ + E U₂ - E S - E U₃ = 0 := by
    intro P S F U₁ U₂ U₃ b hb hP hS hF e₁ e₂ e₃
    have hm := h.markovChain_block hμ (by norm_num) hb hP hS hF
    rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ,
      condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (RVEquiv.refl _) (RVEquiv.refl _),
      e₁, e₂, e₃] at hm
    exact hm
  have E₁ : E {0, 1} + E {1, 2} - E {1} - E {0, 1, 2} = 0 :=
    key (P := {0}) (S := {1}) (F := {2}) (b := 1) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by decide)
  have E₂ : E {2, 3} + E {3, 4} - E {3} - E {2, 3, 4} = 0 :=
    key (P := {2}) (S := {3}) (F := {4}) (b := 3) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by decide)
  have E₃ : E {0, 1, 2} + E {2, 3, 4} - E {2} - E {0, 1, 2, 3, 4} = 0 :=
    key (P := {0, 1}) (S := {2}) (F := {3, 4}) (b := 2) (by simp) (by simp) (by simp) (by simp)
      (by decide) (by decide) (by decide)
  rw [mutualInfo_eq_add_sub hμ, mutualInfo_eq_add_sub hμ, condEntropy_eq_sub hμ,
    condEntropy_eq_sub hμ, q.entropy_eq hμ, r.entropy_eq hμ, p₀₁.entropy_eq hμ, p₃₄.entropy_eq hμ,
    p₁₂.entropy_eq hμ, p₂₃.entropy_eq hμ, (sing 1).entropy_eq hμ, (sing 2).entropy_eq hμ,
    (sing 3).entropy_eq hμ]
  simp only [hE, blockEntropy] at E₁ E₂ E₃ ⊢
  linarith

/-! ### Aliases -/

/-- **Theorem 3.6.** -/
alias theorem_3_6 := existsUnique_isSignedMeasure_tilde

/-- **Lemma 3.7.** (3.32) -/
alias lemma_3_7 := IsSignedMeasure.inter_sdiff_eq_union

/-- **Lemma 3.8.** `I(X; Y | Z) = H(X, Z) + H(Y, Z) - H(X, Y, Z) - H(Z)`, (3.36). -/
theorem lemma_3_8 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    I[X : Y | Z ; μ] =
      H[pair X Z ; μ] + H[pair Y Z ; μ] - H[pair (pair X Y) Z ; μ] - H[Z ; μ] := by
  rw [condMutualInfo_eq hμ, entropyRV_pair_comm μ X Z, entropyRV_pair_comm μ Y Z,
    entropyRV_pair_comm μ (pair X Y) Z]
  ring

/-- **Theorem 3.9.** `μ*` is the unique signed measure consistent with all Shannon's information
measures. -/
theorem theorem_3_9 {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    (∀ G G' G'' : Finset ι, iMeasure μ X ((tilde G ∩ tilde G') \ tilde G'') =
        I[blockRV X G : blockRV X G' | blockRV X G'' ; μ]) ∧
      ∀ m : Finset (NAtom ι) → ℝ, IsSignedMeasure m →
        (∀ G G' G'' : Finset ι, G.Nonempty → G'.Nonempty →
          m ((tilde G ∩ tilde G') \ tilde G'') =
            I[blockRV X G : blockRV X G' | blockRV X G'' ; μ]) → m = iMeasure μ X :=
  ⟨iMeasure_consistent hμ, fun _ hm h => eq_iMeasure_of_consistent hμ hm h⟩

/-- **Theorem 3.11.** -/
alias theorem_3_11 := exists_iMeasure_eq

/-- **Example 3.12 (Concavity of Entropy).** -/
alias example_3_12 := entropy_concaveOn

/-- **Example 3.13 (Convexity of Mutual Information).** -/
alias example_3_13 := mutualInfoOf_convex_channel

/-- **Example 3.14 (Concavity of Mutual Information).** -/
alias example_3_14 := mutualInfoOf_concave_input

/-- **Example 3.17 (Data Processing Theorem).** (3.138) -/
alias example_3_17 := IsMarkovChain.data_processing

/-- **Theorem 3.19.** (3.142) -/
alias theorem_3_19 := IsSignedMeasure.inf_sdiff_eq_sum

end InfoTheory.Yeung
