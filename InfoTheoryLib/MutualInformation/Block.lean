/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Inequalities.SubsetEntropy

/-!
# Blocks of random variables

The random vector `X(s) = (Xᵢ)_{i ∈ s}` of a family of random variables `X i : Ω → A i`, whose
alphabets may depend on `i`, and the entropies `H(X(s))`. The conditional mutual information of
blocks is a linear combination of these entropies. `subsetEntropy` of `Inequalities.SubsetEntropy`
is the same notion for families on one alphabet.

## Main definitions

* `blockRV X s`: the random vector `(Xᵢ)_{i ∈ s}`.
* `blockEntropy μ X s`: its entropy.
* `RVEquiv U V`: `U` and `V` are functions of each other.

## Main statements

* `condMutualInfo_eq_blockEntropy`: `I(U; V | W)` in terms of entropies of index sets.
* `blockEntropy_mono`, `blockEntropy_submodular`: `blockEntropy` is monotone and submodular.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 2.1 and 3.3
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [DecidableEq ι] {A : ι → Type*} {β γ β' γ' : Type*}

/-- The random vector `(Xᵢ)_{i ∈ s}`. -/
def blockRV (X : ∀ i, Ω → A i) (s : Finset ι) : Ω → ∀ i : s, A i := fun ω i => X i ω

omit [Fintype Ω] [DecidableEq ι] in
lemma blockRV_eq_iff (X : ∀ i, Ω → A i) (s : Finset ι) (ω : Ω) (x : ∀ i, A i) :
    blockRV X s ω = (fun i : s => x i) ↔ ∀ i ∈ s, X i ω = x i := by
  simp [blockRV, funext_iff]

/-- Two random variables are functions of each other. -/
def RVEquiv (U : Ω → β) (V : Ω → γ) : Prop :=
  (∃ f : γ → β, ∀ ω, U ω = f (V ω)) ∧ ∃ g : β → γ, ∀ ω, V ω = g (U ω)

omit [Fintype Ω] in
lemma RVEquiv.refl (U : Ω → β) : RVEquiv U U :=
  ⟨⟨id, fun _ => rfl⟩, ⟨id, fun _ => rfl⟩⟩

omit [Fintype Ω] in
lemma RVEquiv.trans {U : Ω → β} {V : Ω → γ} {W : Ω → β'} (h₁ : RVEquiv U V) (h₂ : RVEquiv V W) :
    RVEquiv U W := by
  obtain ⟨⟨f₁, hf₁⟩, g₁, hg₁⟩ := h₁
  obtain ⟨⟨f₂, hf₂⟩, g₂, hg₂⟩ := h₂
  exact ⟨⟨f₁ ∘ f₂, fun ω => by simp [hf₁, hf₂]⟩, g₂ ∘ g₁, fun ω => by simp [← hg₁, ← hg₂]⟩

omit [Fintype Ω] in
lemma RVEquiv.pair {U : Ω → β} {V : Ω → γ} {U' : Ω → β'} {V' : Ω → γ'} (h₁ : RVEquiv U U')
    (h₂ : RVEquiv V V') : RVEquiv (pair U V) (pair U' V') := by
  obtain ⟨⟨f₁, hf₁⟩, g₁, hg₁⟩ := h₁
  obtain ⟨⟨f₂, hf₂⟩, g₂, hg₂⟩ := h₂
  exact ⟨⟨Prod.map f₁ f₂, fun ω => by simp [InfoTheory.pair, ← hf₁, ← hf₂]⟩,
    Prod.map g₁ g₂, fun ω => by simp [InfoTheory.pair, ← hg₁, ← hg₂]⟩

lemma RVEquiv.entropy_eq [Fintype β] [Fintype γ] {μ : Ω → ℝ} (hμ : IsPMF μ) {U : Ω → β}
    {V : Ω → γ} (h : RVEquiv U V) : H[U ; μ] = H[V ; μ] := by
  obtain ⟨⟨f, hf⟩, g, hg⟩ := h
  exact entropyRV_eq_of_comp hμ f g hf hg

omit [Fintype Ω] in
/-- `(X(S), X(T))` and `X(S ∪ T)` are functions of each other. -/
lemma rvEquiv_blockRV_union (X : ∀ i, Ω → A i) (S T : Finset ι) :
    RVEquiv (InfoTheory.pair (blockRV X S) (blockRV X T)) (blockRV X (S ∪ T)) := by
  refine ⟨⟨fun t => (fun i => t ⟨i, mem_union_left _ i.2⟩, fun i => t ⟨i, mem_union_right _ i.2⟩),
    fun ω => rfl⟩, ⟨fun p i => if h : (i : ι) ∈ S then p.1 ⟨i, h⟩ else
      p.2 ⟨i, (mem_union.1 i.2).resolve_left h⟩, fun ω => ?_⟩⟩
  funext i
  by_cases h : (i : ι) ∈ S <;> simp [blockRV, InfoTheory.pair, h]

omit [Fintype Ω] [DecidableEq ι] in
/-- `Xᵢ` and `X({i})` are functions of each other. -/
lemma rvEquiv_blockRV_singleton (X : ∀ i, Ω → A i) (i : ι) :
    RVEquiv (X i) (blockRV X {i}) := by
  refine ⟨⟨fun t => t ⟨i, mem_singleton_self i⟩, fun ω => rfl⟩,
    ⟨fun a j => (mem_singleton.1 j.2).symm ▸ a, fun ω => ?_⟩⟩
  funext j
  obtain ⟨j, hj⟩ := j
  obtain rfl := mem_singleton.1 hj
  rfl

variable [∀ i, Fintype (A i)]

/-- The entropy `H(X(s))` of the random vector `X(s) = (Xᵢ)_{i ∈ s}`. -/
def blockEntropy (μ : Ω → ℝ) (X : ∀ i, Ω → A i) (s : Finset ι) : ℝ := H[blockRV X s ; μ]

variable {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

/-- A conditional mutual information of blocks as a combination of entropies of index sets. -/
lemma condMutualInfo_eq_blockEntropy [Fintype β] [Fintype γ] [Fintype β'] (hμ : IsPMF μ)
    {U : Ω → β} {V : Ω → γ} {W : Ω → β'} {P F S : Finset ι} (hU : RVEquiv U (blockRV X P))
    (hV : RVEquiv V (blockRV X F)) (hW : RVEquiv W (blockRV X S)) :
    I[U : V | W ; μ] = blockEntropy μ X (S ∪ P) + blockEntropy μ X (S ∪ F) - blockEntropy μ X S -
      blockEntropy μ X (S ∪ (P ∪ F)) := by
  rw [condMutualInfo_eq hμ]
  have h₁ : RVEquiv (InfoTheory.pair U V) (blockRV X (P ∪ F)) :=
    (hU.pair hV).trans (rvEquiv_blockRV_union X P F)
  rw [((hW.pair hU).trans (rvEquiv_blockRV_union X S P)).entropy_eq hμ,
    ((hW.pair hV).trans (rvEquiv_blockRV_union X S F)).entropy_eq hμ, hW.entropy_eq hμ,
    ((hW.pair h₁).trans (rvEquiv_blockRV_union X S (P ∪ F))).entropy_eq hμ]
  rfl

/-- Entropies of index sets are monotone. -/
lemma blockEntropy_mono (hμ : IsPMF μ) {S T : Finset ι} (h : S ⊆ T) :
    blockEntropy μ X S ≤ blockEntropy μ X T :=
  entropyRV_comp_le hμ (blockRV X T) (fun t (i : S) => t ⟨i, h i.2⟩)

/-- Entropies of index sets are submodular. -/
lemma blockEntropy_submodular (hμ : IsPMF μ) (S T : Finset ι) :
    blockEntropy μ X (S ∪ T) + blockEntropy μ X (S ∩ T) ≤
      blockEntropy μ X S + blockEntropy μ X T := by
  have h := condMutualInfo_nonneg hμ (blockRV X (S \ T)) (blockRV X (T \ S)) (blockRV X (S ∩ T))
  rw [condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (RVEquiv.refl _) (RVEquiv.refl _)] at h
  have e₁ : S ∩ T ∪ S \ T = S := by rw [union_comm, sdiff_union_inter]
  have e₂ : S ∩ T ∪ T \ S = T := by rw [inter_comm, union_comm, sdiff_union_inter]
  have e₃ : S ∩ T ∪ (S \ T ∪ T \ S) = S ∪ T := by
    ext i
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  rw [e₁, e₂, e₃] at h
  linarith

/-- The information between two sets, without the common conditioning term, grows with the sets. -/
lemma blockEntropy_add_sub_mono (hμ : IsPMF μ) {S S' T T' : Finset ι} (hS : S ⊆ S') (hT : T ⊆ T') :
    blockEntropy μ X S + blockEntropy μ X T - blockEntropy μ X (S ∪ T) ≤
      blockEntropy μ X S' + blockEntropy μ X T' - blockEntropy μ X (S' ∪ T') := by
  have h₁ := blockEntropy_submodular (μ := μ) (X := X) hμ S' (S ∪ T)
  have h₂ : blockEntropy μ X S ≤ blockEntropy μ X (S' ∩ (S ∪ T)) :=
    blockEntropy_mono hμ (subset_inter hS subset_union_left)
  have e₁ : S' ∪ (S ∪ T) = S' ∪ T := by
    rw [← union_assoc, union_eq_left.2 hS]
  rw [e₁] at h₁
  have h₃ := blockEntropy_submodular (μ := μ) (X := X) hμ T' (S' ∪ T)
  have h₄ : blockEntropy μ X T ≤ blockEntropy μ X (T' ∩ (S' ∪ T)) :=
    blockEntropy_mono hμ (subset_inter hT subset_union_right)
  have e₂ : T' ∪ (S' ∪ T) = S' ∪ T' := by
    rw [union_comm S' T, ← union_assoc, union_eq_left.2 hT, union_comm]
  rw [e₂] at h₃
  linarith

/-- The entropy of the empty block vanishes. -/
lemma blockEntropy_empty (hμ : IsPMF μ) : blockEntropy μ X ∅ = 0 := by
  have : blockRV X ∅ = fun _ i => isEmptyElim i := by
    funext ω i
    exact isEmptyElim i
  rw [blockEntropy, this]
  exact entropyRV_const hμ _

omit [∀ i, Fintype (A i)] [Fintype Ω] [DecidableEq ι] in
/-- The empty block is constant. -/
lemma blockRV_empty (X : ∀ i, Ω → A i) :
    blockRV X ∅ = fun _ => (fun i => isEmptyElim i : ∀ i : (∅ : Finset ι), A i) := by
  funext ω i
  exact isEmptyElim i

omit [∀ i, Fintype (A i)] [Fintype Ω] in
/-- A tuple of blocks and the block of their union are functions of each other. -/
lemma rvEquiv_blockRV_biUnion (X : ∀ i, Ω → A i) {κ : Type*} (α : κ → Finset ι) (t : Finset κ) :
    RVEquiv (blockRV (fun j => blockRV X (α j)) t) (blockRV X (t.biUnion α)) := by
  classical
  have hmem : ∀ i : t.biUnion α, ∃ j, j ∈ t ∧ (i : ι) ∈ α j := fun i => mem_biUnion.1 i.2
  choose J hJ₁ hJ₂ using hmem
  refine ⟨⟨fun v j i => v ⟨i, mem_biUnion.2 ⟨j, j.2, i.2⟩⟩, fun ω => rfl⟩,
    ⟨fun v i => v ⟨J i, hJ₁ i⟩ ⟨i, hJ₂ i⟩, fun ω => rfl⟩⟩

end InfoTheory
