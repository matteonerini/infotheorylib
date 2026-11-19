/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Range
public import InfoTheoryLib.IMeasure.Basic
public import InfoTheoryLib.Network.DetNoInterference

/-!
# Every set of nonnegative values is taken by an I-Measure

## Main statements

* `exists_iMeasure_eq`: without constraints on the random variables, `μ*` can take any set of
  nonnegative values on the nonempty atoms.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Theorem 3.11
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

universe u

section Marginal

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {B : κ → Type*} [∀ k, Fintype (B k)]

/-- The coordinates of a tuple, as a family of random variables. -/
def piCoordRV (k : κ) : (∀ k, B k) → B k := fun ω => ω k

/-- The law of a block of coordinates of an independent family is the product of the marginals. -/
theorem dist_prodLaw_blockRV {ν : ∀ k, B k → ℝ} (hν : ∀ k, IsPMF (ν k)) (C : Finset κ)
    (y : ∀ k : C, B k) :
    dist (prodLaw ν) (blockRV (piCoordRV (B := B)) C) y = prodLaw (fun k : C => ν k) y := by
  classical
  let g : ∀ k, B k → ℝ := fun k c =>
    if h : k ∈ C then (if c = y ⟨k, h⟩ then ν k c else 0) else ν k c
  have h₁ : dist (prodLaw ν) (blockRV (piCoordRV (B := B)) C) y =
      ∑ ω : ∀ k, B k, ∏ k, g k (ω k) := by
    refine sum_congr rfl fun ω _ => ?_
    by_cases hω : blockRV (piCoordRV (B := B)) C ω = y
    · simp only [hω, ↓reduceIte, prodLaw]
      refine prod_congr rfl fun k _ => ?_
      by_cases hk : k ∈ C
      · have : ω k = y ⟨k, hk⟩ := congrFun hω ⟨k, hk⟩
        simp [g, hk, this]
      · simp [g, hk]
    · simp only [hω, ↓reduceIte]
      have : ∃ k : C, ω k ≠ y k := by
        by_contra hne
        push Not at hne
        exact hω (funext hne)
      obtain ⟨⟨k, hk⟩, hne⟩ := this
      refine (prod_eq_zero (mem_univ k) ?_).symm
      simp [g, hk, hne]
  have h₂ : ∀ k, ∑ c, g k c = if h : k ∈ C then ν k (y ⟨k, h⟩) else 1 := by
    intro k
    by_cases hk : k ∈ C
    · simp [g, hk]
    · simp [g, hk, (hν k).sum_eq_one]
  rw [h₁, sum_prod_pi]
  simp_rw [h₂]
  have h₃ : ∏ k, (if h : k ∈ C then ν k (y ⟨k, h⟩) else 1) =
      ∏ k ∈ C, (if h : k ∈ C then ν k (y ⟨k, h⟩) else 1) :=
    (prod_subset (subset_univ C) fun k _ hk => by simp [hk]).symm
  rw [h₃, ← prod_coe_sort C, prodLaw]
  exact prod_congr rfl fun k _ => by simp [k.property]

/-- The entropy of a block of coordinates of an independent family. -/
theorem entropy_prodLaw_blockRV {ν : ∀ k, B k → ℝ} (hν : ∀ k, IsPMF (ν k)) (C : Finset κ) :
    H[blockRV (piCoordRV (B := B)) C ; prodLaw ν] = ∑ k ∈ C, entropy (ν k) := by
  have e : dist (prodLaw ν) (blockRV (piCoordRV (B := B)) C) = prodLaw (fun k : C => ν k) :=
    funext (dist_prodLaw_blockRV hν C)
  rw [entropyRV, e, entropy_prodLaw fun k : C => hν k, ← sum_coe_sort C]

end Marginal

/-- **Theorem 3.11.** If there is no constraint on the random variables, then `μ*` can take any set
of nonnegative values on the nonempty atoms. -/
theorem exists_iMeasure_eq {ι : Type u} [Fintype ι] [DecidableEq ι] (v : NAtom ι → ℝ)
    (hv : ∀ a, 0 ≤ v a) :
    ∃ (Ω : Type u) (_ : Fintype Ω) (A : ι → Type u) (_ : ∀ i, Fintype (A i)) (μ : Ω → ℝ)
      (X : ∀ i, Ω → A i), IsPMF μ ∧ ∀ a, iMeasure μ X {a} = v a := by
  classical
  -- (3.72): independent `Y_a` with `H(Y_a) = v a`, and `Xᵢ = (Y_a : i ∈ a)`
  choose n p hp hH using fun a => exists_entropy_eq (hv a)
  let X : ∀ i, (∀ a, Fin (n a)) → ∀ a : {a : NAtom ι // i ∈ a.val}, Fin (n a) :=
    fun i ω a => ω a
  have hμ : IsPMF (prodLaw p) := prodLaw_isPMF hp
  -- (3.73)
  have hG : ∀ G : Finset ι, blockEntropy (prodLaw p) X G = ∑ a ∈ tilde G, v a := by
    intro G
    have hmem : ∀ a : tilde G, ∃ i, ∃ _ : i ∈ G, i ∈ a.val.val := fun a => by
      obtain ⟨i, h₁, h₂⟩ := mem_tilde.1 a.property
      exact ⟨i, h₁, h₂⟩
    choose I hI₁ hI₂ using hmem
    have heq : RVEquiv (blockRV X G) (blockRV (piCoordRV (B := fun a => Fin (n a))) (tilde G)) :=
      ⟨⟨fun t i a => t ⟨a.val, mem_tilde.2 ⟨i, i.property, a.property⟩⟩, fun _ => rfl⟩,
        ⟨fun t a => t ⟨I a, hI₁ a⟩ ⟨a.val, hI₂ a⟩, fun _ => rfl⟩⟩
    rw [blockEntropy, heq.entropy_eq hμ, entropy_prodLaw_blockRV hp]
    exact sum_congr rfl fun a _ => hH a
  refine ⟨_, inferInstance, fun i => ∀ a : {a : NAtom ι // i ∈ a.val}, Fin (n a), inferInstance,
    prodLaw p, X, hμ, fun a => ?_⟩
  -- (3.74)–(3.76), by the uniqueness of `μ*`
  have hm : (fun F : Finset (NAtom ι) => ∑ a ∈ F, v a) = iMeasure (prodLaw p) X :=
    (isSignedMeasure_sum v).eq_signedMeasureOf (blockEntropy_empty hμ)
      fun G _ => (hG G).symm
  rw [← hm]
  simp

end InfoTheory
