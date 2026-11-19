/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.IMeasure.Basic
public import InfoTheoryLib.MarkovChain.Sequence

/-!
# The I-Measure of a Markov chain

Numbers without a source refer to [yeung2008].

## Main statements

* `iMeasure_atom_markov_three`, `iMeasure_inter_markov_three`, `iMeasure_nonneg_markov_three`:
  for a Markov chain of three variables, `μ*` vanishes on `X̃₁ ∩ X̃₂ᶜ ∩ X̃₃`, has the value
  `I(X₁; X₃)` on `X̃₁ ∩ X̃₂ ∩ X̃₃`, and is nonnegative.
* `iMeasure_atoms_markov_four`: for a Markov chain of four variables, `μ*` vanishes on five atoms.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 3.5
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω : Type*} [Fintype Ω]

section Three

variable {A : Fin 3 → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

/-- **(3.77)** If `X₁ → X₂ → X₃`, then `μ*(X̃₁ ∩ X̃₂ᶜ ∩ X̃₃) = I(X₁; X₃ | X₂) = 0`. -/
theorem iMeasure_atom_markov_three (hμ : IsPMF μ) (h : MarkovChain μ (X 0) (X 1) (X 2)) :
    iMeasure μ X {⟨{0, 2}, insert_nonempty 0 _⟩} = 0 := by
  have hc : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
  rw [singleton_atom_pair, hc, iMeasure_inter_sdiff hμ (rvEquiv_blockRV_singleton X 0)
    (rvEquiv_blockRV_singleton X 2) (rvEquiv_blockRV_singleton X 1),
    condMutualInfo_eq_zero_iff hμ, ← markovChain_iff_condIndep hμ]
  exact h

/-- **(3.78)–(3.81)** If `X₁ → X₂ → X₃`, then `I(X₁; X₂; X₃) = I(X₁; X₃) ≥ 0`. -/
theorem iMeasure_inter_markov_three (hμ : IsPMF μ) (h : MarkovChain μ (X 0) (X 1) (X 2)) :
    iMeasure μ X (tilde {0} ∩ tilde {1} ∩ tilde {2}) = I[X 0 : X 2 ; μ] := by
  have hm := isSignedMeasure_iMeasure μ X
  have h₀ := hm.inter_inter_sdiff_eq (tilde {0}) (tilde {2}) ∅ (tilde {1})
  rw [sdiff_empty, sdiff_empty, empty_union, inter_right_comm] at h₀
  rw [h₀, iMeasure_inter hμ (rvEquiv_blockRV_singleton X 0) (rvEquiv_blockRV_singleton X 2)]
  have h₁ : iMeasure μ X ((tilde {0} ∩ tilde {2}) \ tilde {1}) = 0 := by
    rw [iMeasure_inter_sdiff hμ (rvEquiv_blockRV_singleton X 0) (rvEquiv_blockRV_singleton X 2)
      (rvEquiv_blockRV_singleton X 1), condMutualInfo_eq_zero_iff hμ,
      ← markovChain_iff_condIndep hμ]
    exact h
  rw [h₁, sub_zero]

/-- **Section 3.5.** If `X₁ → X₂ → X₃`, then `μ*` is nonnegative. -/
theorem iMeasure_nonneg_markov_three (hμ : IsPMF μ) (h : MarkovChain μ (X 0) (X 1) (X 2))
    (F : Finset (NAtom (Fin 3))) : 0 ≤ iMeasure μ X F := by
  rw [(isSignedMeasure_iMeasure μ X).eq_sum_singleton F]
  refine sum_nonneg fun a _ => ?_
  by_cases ha : #a.val ≤ 2
  · exact iMeasure_atom_nonneg hμ a ha
  · have hle : #a.val ≤ 3 := by simpa using card_le_univ a.val
    have hu : a.val = univ := (card_eq_iff_eq_univ _).1 (by simp; omega)
    have ha' : a = ⟨{0, 1, 2}, insert_nonempty 0 _⟩ := Subtype.ext (hu.trans (by decide))
    have hc : ({0, 1, 2} : Finset (Fin 3))ᶜ = ∅ := by decide
    rw [ha', singleton_atom_triple, hc, tilde_empty, sdiff_empty,
      iMeasure_inter_markov_three hμ h]
    exact mutualInfo_nonneg hμ _ _

end Three

section Bridge

variable {A : ℕ → Type*} {n : ℕ}

omit [Fintype Ω] in
/-- A block of the variables of a chain, indexed by `Fin n` or by `ℕ`. -/
lemma rvEquiv_blockRV_map (Z : ∀ i, Ω → A i) (G : Finset (Fin n)) :
    RVEquiv (blockRV Z (G.map Fin.valEmbedding)) (blockRV (fun i : Fin n => Z i) G) := by
  have hlt : ∀ j : G.map Fin.valEmbedding, (j : ℕ) < n := fun j => by
    obtain ⟨i, _, hi⟩ := mem_map.1 j.property
    rw [← hi]
    exact i.isLt
  have hmem : ∀ j : G.map Fin.valEmbedding, (⟨j, hlt j⟩ : Fin n) ∈ G := fun j => by
    obtain ⟨i, hi, hij⟩ := mem_map.1 j.property
    have : (⟨j, hlt j⟩ : Fin n) = i := Fin.ext hij.symm
    rwa [this]
  exact ⟨⟨fun t j => t ⟨⟨j, hlt j⟩, hmem j⟩, fun _ => rfl⟩,
    ⟨fun t i => t ⟨i, mem_map.2 ⟨i, i.property, rfl⟩⟩, fun _ => rfl⟩⟩

variable [∀ i, Fintype (A i)] {μ : Ω → ℝ} {Z : ∀ i, Ω → A i}

/-- The global Markov property, for the entropies of the index sets of `Fin n`. -/
theorem IsMarkovChain.blockEntropy_fin (hμ : IsPMF μ) (hn : 2 ≤ n) (h : IsMarkovChain μ Z n)
    {P S F : Finset (Fin n)} {b : Fin n} (hb : b ∈ S) (hP : ∀ i ∈ P, i < b)
    (hS : ∀ i ∈ S, b ≤ i) (hF : ∀ i ∈ F, b ≤ i) :
    blockEntropy μ (fun i : Fin n => Z i) (S ∪ P) + blockEntropy μ (fun i : Fin n => Z i) (S ∪ F) -
      blockEntropy μ (fun i : Fin n => Z i) S -
        blockEntropy μ (fun i : Fin n => Z i) (S ∪ (P ∪ F)) = 0 := by
  have hm := h.markovChain_block hμ hn (P := P.map Fin.valEmbedding) (S := S.map Fin.valEmbedding)
    (F := F.map Fin.valEmbedding) (b := b)
    (mem_map.2 ⟨b, hb, rfl⟩)
    (fun i hi => by
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hi
      exact hP j hj)
    (fun i hi => by
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hi
      exact ⟨hS j hj, j.isLt⟩)
    (fun i hi => by
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hi
      exact ⟨hF j hj, j.isLt⟩)
  rw [markovChain_iff_condIndep hμ, ← condMutualInfo_eq_zero_iff hμ,
    condMutualInfo_eq_blockEntropy hμ (rvEquiv_blockRV_map Z P) (rvEquiv_blockRV_map Z F)
      (rvEquiv_blockRV_map Z S)] at hm
  exact hm

end Bridge

section Four

variable {A : ℕ → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ} {Z : ∀ i, Ω → A i}

/-- **(3.91)–(3.96)** If `X₁ → X₂ → X₃ → X₄`, then `μ*` vanishes on the five atoms
`X̃₁ ∩ X̃₂ᶜ ∩ X̃₃ ∩ X̃₄ᶜ`, `X̃₁ ∩ X̃₂ᶜ ∩ X̃₃ ∩ X̃₄`, `X̃₁ ∩ X̃₂ᶜ ∩ X̃₃ᶜ ∩ X̃₄`,
`X̃₁ ∩ X̃₂ ∩ X̃₃ᶜ ∩ X̃₄` and `X̃₁ᶜ ∩ X̃₂ ∩ X̃₃ᶜ ∩ X̃₄`. -/
theorem iMeasure_atoms_markov_four (hμ : IsPMF μ) (h : IsMarkovChain μ Z 4) :
    iMeasure μ (fun i : Fin 4 => Z i) {⟨{0, 2}, insert_nonempty 0 _⟩} = 0 ∧
      iMeasure μ (fun i : Fin 4 => Z i) {⟨{0, 2, 3}, insert_nonempty 0 _⟩} = 0 ∧
        iMeasure μ (fun i : Fin 4 => Z i) {⟨{0, 3}, insert_nonempty 0 _⟩} = 0 ∧
          iMeasure μ (fun i : Fin 4 => Z i) {⟨{0, 1, 3}, insert_nonempty 0 _⟩} = 0 ∧
            iMeasure μ (fun i : Fin 4 => Z i) {⟨{1, 3}, insert_nonempty 1 _⟩} = 0 := by
  set X : ∀ i : Fin 4, Ω → A i := fun i => Z i with hX
  set H := blockEntropy μ X with hH
  have hm := isSignedMeasure_iMeasure μ X
  have key : ∀ {P S F U₁ U₂ U₃ : Finset (Fin 4)} {b : Fin 4}, b ∈ S → (∀ i ∈ P, i < b) →
      (∀ i ∈ S, b ≤ i) → (∀ i ∈ F, b ≤ i) → S ∪ P = U₁ → S ∪ F = U₂ → S ∪ (P ∪ F) = U₃ →
        H U₁ + H U₂ - H S - H U₃ = 0 := by
    intro P S F U₁ U₂ U₃ b hb hP hS hF e₁ e₂ e₃
    rw [← e₁, ← e₂, ← e₃]
    exact h.blockEntropy_fin hμ (by norm_num) hb hP hS hF
  -- the Markov chains of (3.82)–(3.87)
  have E₁ : H {0, 1} + H {1, 2} - H {1} - H {0, 1, 2} = 0 :=
    key (P := {0}) (S := {1}) (F := {2}) (b := 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have E₂ : H {0, 1} + H {1, 3} - H {1} - H {0, 1, 3} = 0 :=
    key (P := {0}) (S := {1}) (F := {3}) (b := 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have E₃ : H {0, 2} + H {2, 3} - H {2} - H {0, 2, 3} = 0 :=
    key (P := {0}) (S := {2}) (F := {3}) (b := 2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have E₄ : H {1, 2} + H {2, 3} - H {2} - H {1, 2, 3} = 0 :=
    key (P := {1}) (S := {2}) (F := {3}) (b := 2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have E₅ : H {0, 1, 2} + H {2, 3} - H {2} - H {0, 1, 2, 3} = 0 :=
    key (P := {0, 1}) (S := {2}) (F := {3}) (b := 2) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  -- the values on the atoms, by Lemma 3.7
  have J₀₂₁₃ : iMeasure μ X ((tilde {0} ∩ tilde {2}) \ tilde {1, 3}) =
      H {0, 1, 3} + H {1, 2, 3} - H {0, 1, 2, 3} - H {1, 3} :=
    iMeasure_inter_sdiff_eq_blockEntropy hμ (by decide) (by decide) (by decide)
  have J₀₂₁ : iMeasure μ X ((tilde {0} ∩ tilde {2}) \ tilde {1}) =
      H {0, 1} + H {1, 2} - H {0, 1, 2} - H {1} :=
    iMeasure_inter_sdiff_eq_blockEntropy hμ (by decide) (by decide) (by decide)
  have J₀₃₁₂ : iMeasure μ X ((tilde {0} ∩ tilde {3}) \ tilde {1, 2}) =
      H {0, 1, 2} + H {1, 2, 3} - H {0, 1, 2, 3} - H {1, 2} :=
    iMeasure_inter_sdiff_eq_blockEntropy hμ (by decide) (by decide) (by decide)
  have J₀₃₂ : iMeasure μ X ((tilde {0} ∩ tilde {3}) \ tilde {2}) =
      H {0, 2} + H {2, 3} - H {0, 2, 3} - H {2} :=
    iMeasure_inter_sdiff_eq_blockEntropy hμ (by decide) (by decide) (by decide)
  have J₁₃₀₂ : iMeasure μ X ((tilde {1} ∩ tilde {3}) \ tilde {0, 2}) =
      H {0, 1, 2} + H {0, 2, 3} - H {0, 1, 2, 3} - H {0, 2} :=
    iMeasure_inter_sdiff_eq_blockEntropy hμ (by decide) (by decide) (by decide)
  have Z₀₂₁₃ : iMeasure μ X ((tilde {0} ∩ tilde {2}) \ tilde {1, 3}) = 0 := by
    rw [J₀₂₁₃]
    linarith
  have Z₀₃₁₂ : iMeasure μ X ((tilde {0} ∩ tilde {3}) \ tilde {1, 2}) = 0 := by
    rw [J₀₃₁₂]
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hc : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
    rw [singleton_atom_pair, hc]
    exact Z₀₂₁₃
  · have hc : ({0, 2, 3} : Finset (Fin 4))ᶜ = {1} := by decide
    have hu : ({1} : Finset (Fin 4)) ∪ {3} = {1, 3} := by decide
    rw [singleton_atom_triple, hc, hm.inter_inter_sdiff_eq, ← tilde_union, hu, Z₀₂₁₃, J₀₂₁]
    linarith
  · have hc : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide
    rw [singleton_atom_pair, hc]
    exact Z₀₃₁₂
  · have hc : ({0, 1, 3} : Finset (Fin 4))ᶜ = {2} := by decide
    have hu : ({2} : Finset (Fin 4)) ∪ {1} = {1, 2} := by decide
    rw [singleton_atom_triple, hc, inter_right_comm, hm.inter_inter_sdiff_eq, ← tilde_union, hu,
      Z₀₃₁₂, J₀₃₂]
    linarith
  · have hc : ({1, 3} : Finset (Fin 4))ᶜ = {0, 2} := by decide
    rw [singleton_atom_pair, hc, J₁₃₀₂]
    linarith

end Four

end InfoTheory
