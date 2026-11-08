/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MutualInformation.Block

/-!
# Polymatroids

A set function `f` on the finite subsets of an index type is a *polymatroid* if `f ∅ = 0`, `f` is
monotone and `f` is submodular. The entropy function `s ↦ H(X_s)` of random variables is a
polymatroid; the polymatroidal axioms are equivalent to the basic inequalities.

For a set function `f`, `condInfo f S T K = f (K ∪ S) + f (K ∪ T) - f (K ∪ S ∪ T) - f K` is the
counterpart of the conditional mutual information `I(X_S; X_T | X_K)`. This file collects the
inequalities between these quantities that follow from the polymatroidal axioms alone.

## Main definitions

* `IsPolymatroid f`: the polymatroidal axioms P1–P3.
* `condInfo f S T K`: the counterpart of `I(X_S; X_T | X_K)`.

## Main statements

* `IsPolymatroid.sub_le_sub`: diminishing returns, `f (B ∪ D) - f B ≤ f (A ∪ D) - f A` for
  `A ⊆ B`.
* `IsPolymatroid.condInfo_nonneg`, `IsPolymatroid.condInfo_mono`: `condInfo f S T K` is
  nonnegative and grows with `S` and `T`.
* `IsPolymatroid.sub_le_sum`: `f (K ∪ ⋃ⱼ Qⱼ) - f K ≤ ∑ⱼ (f (K ∪ Qⱼ) - f K)`.
* `isPolymatroid_blockEntropy`: the entropy function of random variables is a polymatroid.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Appendix 14.A
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [DecidableEq ι]

/-- **The polymatroidal axioms**, P1–P3 of Appendix 14.A: `f ∅ = 0`, `f` is monotone, and `f` is
submodular. -/
structure IsPolymatroid (f : Finset ι → ℝ) : Prop where
  /-- P1: `f ∅ = 0`. -/
  empty : f ∅ = 0
  /-- P2: `f α ≤ f β` if `α ⊆ β`. -/
  mono : ∀ ⦃s t : Finset ι⦄, s ⊆ t → f s ≤ f t
  /-- P3: `f (α ∪ β) + f (α ∩ β) ≤ f α + f β`. -/
  submod : ∀ s t : Finset ι, f (s ∪ t) + f (s ∩ t) ≤ f s + f t

/-- The counterpart `f (K ∪ S) + f (K ∪ T) - f (K ∪ S ∪ T) - f K` of `I(X_S; X_T | X_K)` for a set
function `f`. -/
def condInfo (f : Finset ι → ℝ) (S T K : Finset ι) : ℝ :=
  f (K ∪ S) + f (K ∪ T) - f (K ∪ S ∪ T) - f K

lemma condInfo_comm (f : Finset ι → ℝ) (S T K : Finset ι) :
    condInfo f S T K = condInfo f T S K := by
  simp only [condInfo, union_right_comm K S T]
  ring

namespace IsPolymatroid

variable {f : Finset ι → ℝ}

lemma nonneg (hf : IsPolymatroid f) (s : Finset ι) : 0 ≤ f s :=
  hf.empty ▸ hf.mono (empty_subset s)

/-- **Diminishing returns.** If `A ⊆ B`, then `f (B ∪ D) - f B ≤ f (A ∪ D) - f A`. -/
theorem sub_le_sub (hf : IsPolymatroid f) {A B : Finset ι} (hAB : A ⊆ B) (D : Finset ι) :
    f (B ∪ D) - f B ≤ f (A ∪ D) - f A := by
  have h₁ := hf.submod (A ∪ D) B
  have e : A ∪ D ∪ B = B ∪ D := by
    rw [union_right_comm, union_eq_right.2 hAB, union_comm]
  have h₂ : f A ≤ f ((A ∪ D) ∩ B) :=
    hf.mono (subset_inter subset_union_left hAB)
  rw [e] at h₁
  linarith

/-- The basic inequality `I(X_S; X_T | X_K) ≥ 0` for a polymatroid. -/
theorem condInfo_nonneg (hf : IsPolymatroid f) (S T K : Finset ι) : 0 ≤ condInfo f S T K := by
  have h := hf.sub_le_sub (subset_union_left (s₁ := K) (s₂ := T)) S
  rw [union_right_comm] at h
  simp only [condInfo]
  linarith

/-- `condInfo f S T K` grows with `S`. -/
theorem condInfo_mono_left (hf : IsPolymatroid f) {S S' : Finset ι} (hS : S ⊆ S') (T K : Finset ι) :
    condInfo f S T K ≤ condInfo f S' T K := by
  have h := hf.sub_le_sub (subset_union_left (s₁ := K ∪ S) (s₂ := T)) S'
  have e₁ : K ∪ S ∪ T ∪ S' = K ∪ S' ∪ T := by
    rw [union_right_comm, union_assoc K S S', union_eq_right.2 hS]
  have e₂ : K ∪ S ∪ S' = K ∪ S' := by rw [union_assoc, union_eq_right.2 hS]
  rw [e₁, e₂] at h
  simp only [condInfo]
  linarith

/-- `condInfo f S T K` grows with `S` and `T`. -/
theorem condInfo_mono (hf : IsPolymatroid f) {S S' T T' : Finset ι} (hS : S ⊆ S') (hT : T ⊆ T')
    (K : Finset ι) : condInfo f S T K ≤ condInfo f S' T' K := by
  have h₁ := hf.condInfo_mono_left hS T K
  have h₂ := hf.condInfo_mono_left hT S' K
  rw [condInfo_comm f T, condInfo_comm f T'] at h₂
  linarith

/-- Moving the parts `D` and `E` of the condition to the two sides does not decrease the
information: `I(X_S; X_T | X_{C ∪ D ∪ E}) ≤ I(X_{S ∪ D}; X_{T ∪ E} | X_C)`. -/
theorem condInfo_le_condInfo_union (hf : IsPolymatroid f) (S T C D E : Finset ι) :
    condInfo f S T (C ∪ D ∪ E) ≤ condInfo f (S ∪ D) (T ∪ E) C := by
  have h₁ := hf.condInfo_nonneg D (T ∪ E) C
  have h₂ := hf.condInfo_nonneg S E (C ∪ D)
  simp only [condInfo] at h₁ h₂ ⊢
  simp only [union_comm, union_left_comm] at h₁ h₂ ⊢
  linarith

/-- **Subadditivity** of the conditional counterpart: `f (K ∪ ⋃ⱼ Qⱼ) - f K ≤ ∑ⱼ (f (K ∪ Qⱼ) - f K)`.
-/
theorem sub_le_sum (hf : IsPolymatroid f) {κ : Type*} (K : Finset ι) (Q : κ → Finset ι)
    (s : Finset κ) : f (K ∪ s.biUnion Q) - f K ≤ ∑ j ∈ s, (f (K ∪ Q j) - f K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, biUnion_insert]
    have h := hf.sub_le_sub (subset_union_left (s₁ := K) (s₂ := s.biUnion Q)) (Q a)
    have e : K ∪ (Q a ∪ s.biUnion Q) = K ∪ s.biUnion Q ∪ Q a := by
      rw [union_left_comm, union_comm, union_assoc, union_comm (s.biUnion Q)]
    rw [e]
    linarith

end IsPolymatroid

section Entropy

variable {Ω : Type*} [Fintype Ω] [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}
  {X : ∀ i, Ω → A i}

omit [Fintype ι] in
/-- **Appendix 14.A.** The entropy function `s ↦ H(X_s)` of random variables is a polymatroid. -/
theorem isPolymatroid_blockEntropy (hμ : IsPMF μ) : IsPolymatroid (blockEntropy μ X) :=
  ⟨blockEntropy_empty hμ, fun _ _ h => blockEntropy_mono hμ h, blockEntropy_submodular hμ⟩

omit [Fintype ι] in
/-- `condInfo` of the entropy function is a conditional mutual information. -/
lemma condInfo_blockEntropy (hμ : IsPMF μ) (S T K : Finset ι) :
    condInfo (blockEntropy μ X) S T K = I[blockRV X S : blockRV X T | blockRV X K ; μ] := by
  rw [condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (RVEquiv.refl _) (RVEquiv.refl _),
    condInfo, union_assoc]
  ring

end Entropy

end InfoTheory
