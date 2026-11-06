/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.Log

/-!
# Random binary matrices

The product `A v` of a uniformly random binary matrix `A` with a fixed nonzero vector `v` is
uniform. This is the counting argument behind random linear codes.

## Main statements

* `card_dotProduct_eq`: `2ⁿ⁻¹` vectors have a given product with a nonzero vector.
* `card_mulVec_eq`: `2^{k n} / 2^k` matrices `A` have `A v = w`, for `v ≠ 0`.
-/

open Finset

@[expose] public section

variable {k n : ℕ}

/-- A vector with a nonzero coordinate has half of the vectors on each side of a linear equation. -/
theorem card_dotProduct_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → ZMod 2} (hv : v ≠ 0)
    (c : ZMod 2) :
    2 * (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c).card = 2 ^ Fintype.card ι := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hi' : v i = 1 := by
    have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact this _ hi
  set f : (ι → ZMod 2) → ι → ZMod 2 := fun a => a + Pi.single i 1 with hf
  have hff : ∀ a, f (f a) = a := fun a => by
    funext j
    have : ∀ x : ZMod 2, x + x = 0 := by decide
    simp only [hf, Pi.add_apply, add_assoc, this, add_zero]
  have hdot : ∀ a, f a ⬝ᵥ v = a ⬝ᵥ v + 1 := fun a => by
    simp only [hf, add_dotProduct, single_dotProduct, one_mul, hi']
  have hswap : ∀ c : ZMod 2, (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c + 1).card =
      (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c).card := fun c => by
    refine card_nbij' f f ?_ ?_ (fun a _ => hff a) fun a _ => hff a
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      have : ∀ x : ZMod 2, x + 1 + 1 = x := by decide
      rw [hdot, ha, this]
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      rw [hdot, ha]
  have htot : (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c).card +
      (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c + 1).card = 2 ^ Fintype.card ι := by
    have hd : Disjoint (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c)
        (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c + 1) := by
      refine disjoint_filter.2 fun a _ h₁ h₂ => ?_
      have : ∀ x : ZMod 2, x ≠ x + 1 := by decide
      exact this c (h₁.symm.trans h₂)
    rw [← card_union_of_disjoint hd]
    have hu : (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c) ∪
        (univ.filter fun a : ι → ZMod 2 => a ⬝ᵥ v = c + 1) = univ := by
      ext a
      simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
      have : ∀ x y : ZMod 2, x = y ∨ x = y + 1 := by decide
      exact this _ _
    rw [hu, card_univ, Fintype.card_fun, ZMod.card]
  rw [hswap c] at htot
  omega

/-- The number of binary matrices `A` with `A v = w`, for `v ≠ 0`, as a fraction `2^{-k}` of all the
matrices. -/
theorem card_mulVec_eq {v : Fin n → ZMod 2} (hv : v ≠ 0) (w : Fin k → ZMod 2) :
    ((univ.filter fun A : Fin k → Fin n → ZMod 2 => ∀ j, A j ⬝ᵥ v = w j).card : ℝ) =
      (2 : ℝ) ^ (n * k) / 2 ^ k := by
  have hset : (univ.filter fun A : Fin k → Fin n → ZMod 2 => ∀ j, A j ⬝ᵥ v = w j) =
      Fintype.piFinset fun j => univ.filter fun a : Fin n → ZMod 2 => a ⬝ᵥ v = w j := by
    ext A
    simp [Fintype.mem_piFinset]
  have hprod : (2 : ℝ) ^ k * ∏ j : Fin k,
      ((univ.filter fun a : Fin n → ZMod 2 => a ⬝ᵥ v = w j).card : ℝ) = (2 : ℝ) ^ (n * k) := by
    have h := fun j => card_dotProduct_eq hv (w j)
    simp only [Fintype.card_fin] at h
    have e : (2 : ℝ) ^ k = ∏ _j : Fin k, (2 : ℝ) := by simp
    rw [e, ← prod_mul_distrib]
    calc _ = ∏ _j : Fin k, (2 : ℝ) ^ n := prod_congr rfl fun j _ => by exact_mod_cast h j
      _ = _ := by simp [pow_mul]
  rw [hset, Fintype.card_piFinset, eq_div_iff (by positivity), Nat.cast_prod, mul_comm]
  exact hprod
