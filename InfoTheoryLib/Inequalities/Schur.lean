/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.MatrixDet
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Inequalities for ratios of determinants

Write a positive definite matrix on `m ⊕ p` in blocks, `K = [[A, B], [Bᵀ, D]]`, with `A = K₁₁` the
leading block. The Schur complement `K/A = D - Bᵀ A⁻¹ B` has `|K| = |A| |K/A|`, and it is the
"conditional covariance" of the last `p` coordinates given the first ones: for every `y`,
`yᵀ (K/A) y = min_x (x, y)ᵀ K (x, y)`. With `p = 1` this is Lemma 17.10.1: `|Kₙ|/|Kₙ₋₁|` is the
minimum mean squared error `σₙ²` of the linear prediction of `Xₙ` from `X₁, …, Xₙ₋₁`.

The minimum characterization makes `K ↦ K/A` concave in the Loewner order, which gives
Bergstrøm's theorems: `log (|Kₙ|/|Kₙ₋ₚ|)` is concave (Theorem 17.10.1), and `|Kₙ|/|Kₙ₋₁|` is
concave (Theorem 17.10.2).

## Main definitions

* `schurCompl K`: the Schur complement `K₂₂ - K₂₁ K₁₁⁻¹ K₁₂` of the leading block.

## Main statements

* `det_eq_mul_det_schurCompl`, `schurCompl_posDef`: `|K| = |K₁₁| |K/K₁₁|`, and `K/K₁₁ ≻ 0`.
* `det_le_det_mul_det`: **Fischer's inequality** `|K| ≤ |K₁₁| |K₂₂|`.
* `quadForm_schurCompl_le`, `quadForm_schurCompl_eq`: `yᵀ (K/K₁₁) y = min_x (x, y)ᵀ K (x, y)`.
* `isLeast_det_div_det`: **Lemma 17.10.1**, `|Kₙ|/|Kₙ₋₁| = min_x (x, 1)ᵀ K (x, 1)`.
* `posSemidef_schurCompl_sub`: the Schur complement is concave in the Loewner order.
* `det_div_det_rpow_mul_le`, `concaveOn_log_det_div_det`: **Theorem 17.10.1 (Bergstrøm)**.
* `concaveOn_det_div_det`: **Theorem 17.10.2 (Bergstrøm)**.

## Implementation notes

The book's `Kₙ` and `Kₙ₋ₚ` are the matrix and its leading `(n - p) × (n - p)` block; we index the
matrix by `m ⊕ p`, with `Kₙ₋ₚ = K.toBlocks₁₁`. The book proves these results with Gaussian
random vectors and the conditioning inequality for differential entropy; the minimum
characterization of the Schur complement is the matrix form of the same argument.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 17.10
-/

open Matrix Real

@[expose] public noncomputable section

namespace InfoTheory

variable {m p : Type*} [Fintype m] [DecidableEq m]

/-- The Schur complement `K/K₁₁ = K₂₂ - K₂₁ K₁₁⁻¹ K₁₂` of the leading block of `K`. -/
def schurCompl (K : Matrix (m ⊕ p) (m ⊕ p) ℝ) : Matrix p p ℝ :=
  K.toBlocks₂₂ - K.toBlocks₂₁ * K.toBlocks₁₁⁻¹ * K.toBlocks₁₂

variable {K : Matrix (m ⊕ p) (m ⊕ p) ℝ}

omit [Fintype m] [DecidableEq m] in
lemma toBlocks₁₁_posDef (hK : K.PosDef) : K.toBlocks₁₁.PosDef :=
  hK.submatrix Sum.inl_injective

omit [Fintype m] [DecidableEq m] in
lemma toBlocks₂₂_posDef (hK : K.PosDef) : K.toBlocks₂₂.PosDef :=
  hK.submatrix Sum.inr_injective

omit [Fintype m] [DecidableEq m] in
lemma toBlocks₂₁_eq (hK : K.IsHermitian) : K.toBlocks₂₁ = K.toBlocks₁₂ᴴ := by
  ext i j
  simpa [toBlocks₂₁, toBlocks₁₂] using (hK.apply (Sum.inr i) (Sum.inl j)).symm

omit [Fintype m] [DecidableEq m] in
lemma eq_fromBlocks (hK : K.IsHermitian) :
    K = fromBlocks K.toBlocks₁₁ K.toBlocks₁₂ K.toBlocks₁₂ᴴ K.toBlocks₂₂ := by
  rw [← toBlocks₂₁_eq hK, fromBlocks_toBlocks]

lemma schurCompl_eq (hK : K.IsHermitian) :
    schurCompl K = K.toBlocks₂₂ - K.toBlocks₁₂ᴴ * K.toBlocks₁₁⁻¹ * K.toBlocks₁₂ := by
  rw [schurCompl, toBlocks₂₁_eq hK]

/-- `|K| = |K₁₁| |K/K₁₁|`. -/
theorem det_eq_mul_det_schurCompl [Fintype p] [DecidableEq p] (hK : K.PosDef) :
    K.det = K.toBlocks₁₁.det * (schurCompl K).det := by
  let := (toBlocks₁₁_posDef hK).isUnit.invertible
  conv_lhs => rw [← fromBlocks_toBlocks K]
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, schurCompl]

/-- The Schur complement of a positive definite matrix is positive definite. -/
theorem schurCompl_posDef [Finite p] (hK : K.PosDef) : (schurCompl K).PosDef := by
  have := Fintype.ofFinite p
  classical
  have hA := toBlocks₁₁_posDef hK
  let := hA.isUnit.invertible
  have hpsd : (schurCompl K).PosSemidef := by
    have h := hK.posSemidef
    rw [eq_fromBlocks hK.1, PosDef.fromBlocks₁₁ _ _ hA] at h
    rwa [schurCompl_eq hK.1]
  refine hpsd.posDef_iff_det_ne_zero.2 fun h0 => ?_
  have := hK.det_pos
  rw [det_eq_mul_det_schurCompl hK, h0, mul_zero] at this
  exact lt_irrefl _ this

/-- `|K| / |K₁₁| = |K/K₁₁|`. -/
theorem det_div_det_eq [Fintype p] [DecidableEq p] (hK : K.PosDef) :
    K.det / K.toBlocks₁₁.det = (schurCompl K).det := by
  rw [det_eq_mul_det_schurCompl hK, mul_div_cancel_left₀ _ (toBlocks₁₁_posDef hK).det_pos.ne']

/-- **Fischer's inequality.** `|K| ≤ |K₁₁| |K₂₂|` for a positive definite `K`. -/
theorem det_le_det_mul_det [Fintype p] [DecidableEq p] (hK : K.PosDef) :
    K.det ≤ K.toBlocks₁₁.det * K.toBlocks₂₂.det := by
  have hA := toBlocks₁₁_posDef hK
  rw [det_eq_mul_det_schurCompl hK]
  refine mul_le_mul_of_nonneg_left ?_ hA.det_pos.le
  refine det_le_det_of_posSemidef_sub (schurCompl_posDef hK).posSemidef ?_
  rw [schurCompl_eq hK.1, sub_sub_cancel]
  exact hA.inv.posSemidef.conjTranspose_mul_mul_same _

/-- The quadratic form of `K` in terms of the Schur complement:
`(x, y)ᵀ K (x, y) = (x + A⁻¹By)ᵀ A (x + A⁻¹By) + yᵀ (K/A) y`. -/
lemma quadForm_eq [Fintype p] (hK : K.PosDef) (x : m → ℝ) (y : p → ℝ) :
    (x ⊕ᵥ y) ⬝ᵥ K *ᵥ (x ⊕ᵥ y) =
      (x + (K.toBlocks₁₁⁻¹ * K.toBlocks₁₂) *ᵥ y) ⬝ᵥ
          K.toBlocks₁₁ *ᵥ (x + (K.toBlocks₁₁⁻¹ * K.toBlocks₁₂) *ᵥ y) +
        y ⬝ᵥ schurCompl K *ᵥ y := by
  let := (toBlocks₁₁_posDef hK).isUnit.invertible
  have h := schur_complement_eq₁₁ K.toBlocks₁₂ K.toBlocks₂₂ x y (toBlocks₁₁_posDef hK).1
  simp only [star_trivial, ← dotProduct_mulVec] at h
  rw [schurCompl_eq hK.1, ← h, ← eq_fromBlocks hK.1]

/-- `yᵀ (K/K₁₁) y ≤ (x, y)ᵀ K (x, y)` for every `x`. -/
theorem quadForm_schurCompl_le [Fintype p] (hK : K.PosDef) (x : m → ℝ) (y : p → ℝ) :
    y ⬝ᵥ schurCompl K *ᵥ y ≤ (x ⊕ᵥ y) ⬝ᵥ K *ᵥ (x ⊕ᵥ y) := by
  rw [quadForm_eq hK]
  have := (toBlocks₁₁_posDef hK).posSemidef.dotProduct_mulVec_nonneg
    (x + (K.toBlocks₁₁⁻¹ * K.toBlocks₁₂) *ᵥ y)
  rw [star_trivial] at this
  linarith

/-- The minimum is attained at `x = -K₁₁⁻¹ K₁₂ y`: the coefficients of the best linear
prediction. -/
theorem quadForm_schurCompl_eq [Fintype p] (hK : K.PosDef) (y : p → ℝ) :
    (-((K.toBlocks₁₁⁻¹ * K.toBlocks₁₂) *ᵥ y) ⊕ᵥ y) ⬝ᵥ K *ᵥ
        (-((K.toBlocks₁₁⁻¹ * K.toBlocks₁₂) *ᵥ y) ⊕ᵥ y) = y ⬝ᵥ schurCompl K *ᵥ y := by
  rw [quadForm_eq hK, neg_add_cancel, zero_dotProduct, zero_add]

/-- The Schur complement of a `1 × 1` block is `|K|/|K₁₁|`. -/
lemma schurCompl_unit {K : Matrix (m ⊕ Unit) (m ⊕ Unit) ℝ} (hK : K.PosDef) :
    (fun _ => 1 : Unit → ℝ) ⬝ᵥ schurCompl K *ᵥ (fun _ => 1) = K.det / K.toBlocks₁₁.det := by
  rw [det_div_det_eq hK, det_unique]
  simp [dotProduct, mulVec]

/-- **Lemma 17.10.1, (17.140)–(17.143).** `|Kₙ|/|Kₙ₋₁|` is the minimum over `x` of
`(x, 1)ᵀ Kₙ (x, 1)`. For a random vector with covariance `Kₙ`, `(-a, 1)ᵀ Kₙ (-a, 1)` is the mean
squared error `E(Xₙ - aᵀ(X₁, …, Xₙ₋₁))²` of a linear predictor, so `|Kₙ|/|Kₙ₋₁| = σₙ²` is the
minimum mean squared error of the linear prediction of `Xₙ` from the other coordinates. -/
theorem isLeast_det_div_det {K : Matrix (m ⊕ Unit) (m ⊕ Unit) ℝ} (hK : K.PosDef) :
    IsLeast (Set.range fun x : m → ℝ => (x ⊕ᵥ fun _ => 1) ⬝ᵥ K *ᵥ (x ⊕ᵥ fun _ => 1))
      (K.det / K.toBlocks₁₁.det) := by
  rw [← schurCompl_unit hK]
  refine ⟨⟨_, quadForm_schurCompl_eq hK _⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact quadForm_schurCompl_le hK x _

omit [Fintype m] [DecidableEq m] in
lemma posDef_convex_comb {S T : Matrix (m ⊕ p) (m ⊕ p) ℝ} (hS : S.PosDef) (hT : T.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • S + b • T).PosDef := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    simpa [hab] using hT
  exact (hS.smul ha').add_posSemidef (hT.posSemidef.smul hb)

/-- The Schur complement is concave in the Loewner order:
`K/K₁₁ - (a (S/S₁₁) + b (T/T₁₁))` is positive semidefinite for `K = a S + b T`. -/
theorem posSemidef_schurCompl_sub [Finite p] {S T : Matrix (m ⊕ p) (m ⊕ p) ℝ} (hS : S.PosDef)
    (hT : T.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (schurCompl (a • S + b • T) - (a • schurCompl S + b • schurCompl T)).PosSemidef := by
  have := Fintype.ofFinite p
  have hK := posDef_convex_comb hS hT ha hb hab
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun y => ?_⟩
  · exact (schurCompl_posDef hK).1.sub
      (((schurCompl_posDef hS).1.smul (IsSelfAdjoint.all a)).add
        ((schurCompl_posDef hT).1.smul (IsSelfAdjoint.all b)))
  rw [star_trivial, sub_mulVec, dotProduct_sub, add_mulVec, dotProduct_add, smul_mulVec,
    smul_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, sub_nonneg]
  set x := -(((a • S + b • T).toBlocks₁₁⁻¹ * (a • S + b • T).toBlocks₁₂) *ᵥ y)
  rw [← quadForm_schurCompl_eq hK y, add_mulVec, dotProduct_add, smul_mulVec,
    smul_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := quadForm_schurCompl_le hS x y
  have h2 := quadForm_schurCompl_le hT x y
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **Theorem 17.10.1 (Bergstrøm), (17.144)–(17.148).** `|Kₙ|/|Kₙ₋ₚ|` is log-concave: for
`K = a S + (1 - a) T`, `(|S|/|S₁₁|)^a (|T|/|T₁₁|)^{1-a} ≤ |K|/|K₁₁|`. -/
theorem det_div_det_rpow_mul_le [Fintype p] [DecidableEq p] {S T : Matrix (m ⊕ p) (m ⊕ p) ℝ}
    (hS : S.PosDef) (hT : T.PosDef) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (S.det / S.toBlocks₁₁.det) ^ a * (T.det / T.toBlocks₁₁.det) ^ (1 - a) ≤
      (a • S + (1 - a) • T).det / (a • S + (1 - a) • T).toBlocks₁₁.det := by
  have hb : 0 ≤ 1 - a := by linarith
  have hK := posDef_convex_comb hS hT ha0 hb (by ring)
  rw [det_div_det_eq hS, det_div_det_eq hT, det_div_det_eq hK]
  have hS' := (schurCompl_posDef hS).posSemidef
  have hT' := (schurCompl_posDef hT).posSemidef
  refine (det_rpow_mul_det_rpow_le hS' hT' ha0 ha1).trans
    (det_le_det_of_posSemidef_sub ((hS'.smul ha0).add (hT'.smul hb)) ?_)
  exact posSemidef_schurCompl_sub hS hT ha0 hb (by ring)

omit [Fintype m] [DecidableEq m] in
lemma convex_posDef :
    Convex ℝ {K : Matrix (m ⊕ p) (m ⊕ p) ℝ | K.PosDef} :=
  fun _ hS _ hT _ _ ha hb hab => posDef_convex_comb hS hT ha hb hab

/-- **Theorem 17.10.1 (Bergstrøm).** `log (|Kₙ|/|Kₙ₋ₚ|)` is concave on positive definite
matrices. -/
theorem concaveOn_log_det_div_det [Fintype p] [DecidableEq p] :
    ConcaveOn ℝ {K : Matrix (m ⊕ p) (m ⊕ p) ℝ | K.PosDef}
      fun K => log (K.det / K.toBlocks₁₁.det) := by
  refine ⟨convex_posDef, fun S hS T hT a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have hpos : ∀ {K : Matrix (m ⊕ p) (m ⊕ p) ℝ}, K.PosDef → 0 < K.det / K.toBlocks₁₁.det :=
    fun hK => div_pos hK.det_pos (toBlocks₁₁_posDef hK).det_pos
  have h := det_div_det_rpow_mul_le hS hT ha (by linarith)
  have h' := log_le_log (by have := hpos hS; have := hpos hT; positivity) h
  rw [log_mul (rpow_pos_of_pos (hpos hS) _).ne' (rpow_pos_of_pos (hpos hT) _).ne',
    log_rpow (hpos hS), log_rpow (hpos hT)] at h'
  simpa only [smul_eq_mul] using h'

/-- **Theorem 17.10.2 (Bergstrøm), (17.149)–(17.156).** `|Kₙ|/|Kₙ₋₁|` is concave on positive
definite matrices. -/
theorem concaveOn_det_div_det :
    ConcaveOn ℝ {K : Matrix (m ⊕ Unit) (m ⊕ Unit) ℝ | K.PosDef}
      fun K => K.det / K.toBlocks₁₁.det := by
  refine ⟨convex_posDef, fun S hS T hT a b ha hb hab => ?_⟩
  have hK := posDef_convex_comb hS hT ha hb hab
  have h := (posSemidef_schurCompl_sub hS hT ha hb hab).dotProduct_mulVec_nonneg
    (fun _ => 1)
  rw [star_trivial, sub_mulVec, dotProduct_sub, add_mulVec, dotProduct_add, smul_mulVec,
    smul_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    schurCompl_unit hS, schurCompl_unit hT, schurCompl_unit hK] at h
  simp only [smul_eq_mul]
  linarith

end InfoTheory
