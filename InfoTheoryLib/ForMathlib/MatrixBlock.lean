/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Block diagonal positive definite matrices

## Main statements

* `posDef_fromBlocks_zero`: `diag(A, D)` is positive definite if `A` and `D` are.
-/

@[expose] public section

open Matrix

namespace InfoTheory

variable {m n : Type*} [Finite m] [Finite n]

/-- The block diagonal matrix `diag(A, D)` is positive definite if `A` and `D` are. -/
theorem posDef_fromBlocks_zero {A : Matrix m m ℝ} {D : Matrix n n ℝ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  refine PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hD.1) fun x hx => ?_
  have e : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [e]
  have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := fun hr => hx <| funext fun i => by
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    have := hD.dotProduct_mulVec_pos hr
    linarith
  · have := hA.dotProduct_mulVec_pos hl
    linarith

end InfoTheory
