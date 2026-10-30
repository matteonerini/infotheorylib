/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities

/-!
# Determinants of positive semidefinite matrices

Inequalities between the determinants of real positive semidefinite matrices, proved with the
spectral theorem.

## Main statements

* `det_smul_one_add_smul`: `det (a • 1 + b • A) = ∏ᵢ (a + b λᵢ)` for a symmetric `A` with
  eigenvalues `λᵢ`.
* `exists_mul_mul_transpose_eq_one`: a positive definite `B` can be whitened, `S B Sᵀ = 1`.
* `det_le_det_of_posSemidef_sub`: if `B` and `A - B` are positive semidefinite, `|B| ≤ |A|`.
* `det_rpow_mul_det_rpow_le`: the determinant is log-concave,
  `|A|^t |B|^{1-t} ≤ |t A + (1 - t) B|`.
-/

@[expose] public section

open Matrix Real Finset

namespace InfoTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The orthogonal matrix of eigenvectors of a symmetric real matrix. -/
noncomputable abbrev eigvecs {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  (hA.eigenvectorUnitary : Matrix n n ℝ)

lemma eigvecs_transpose_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (eigvecs hA)ᵀ * eigvecs hA = 1 := by
  have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

lemma eigvecs_mul_transpose {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    eigvecs hA * (eigvecs hA)ᵀ = 1 := by
  have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  rwa [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- The spectral theorem for real symmetric matrices: `A = U D Uᵀ`. -/
lemma eq_eigvecs {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = eigvecs hA * diagonal hA.eigenvalues * (eigvecs hA)ᵀ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  simp

/-- `det (S X Sᵀ) = (det S)² det X`. -/
lemma det_mul_mul_transpose (S X : Matrix n n ℝ) : (S * X * Sᵀ).det = S.det ^ 2 * X.det := by
  rw [det_mul, det_mul, det_transpose]
  ring

/-- `det (a • 1 + b • A) = ∏ᵢ (a + b λᵢ)` for a symmetric `A` with eigenvalues `λᵢ`. -/
lemma det_smul_one_add_smul {A : Matrix n n ℝ} (hA : A.IsHermitian) (a b : ℝ) :
    (a • (1 : Matrix n n ℝ) + b • A).det = ∏ i, (a + b * hA.eigenvalues i) := by
  set U := eigvecs hA
  have hD : a • (1 : Matrix n n ℝ) + b • diagonal hA.eigenvalues =
      diagonal fun i => a + b * hA.eigenvalues i := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h, Matrix.one_apply_ne h]
  have h : a • (1 : Matrix n n ℝ) + b • A =
      U * diagonal (fun i => a + b * hA.eigenvalues i) * Uᵀ := by
    rw [← hD]
    calc a • (1 : Matrix n n ℝ) + b • A =
          a • (U * Uᵀ) + b • (U * diagonal hA.eigenvalues * Uᵀ) := by
          rw [eigvecs_mul_transpose, ← eq_eigvecs]
      _ = _ := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one]
  rw [h, det_mul_mul_transpose, det_diagonal]
  have hU : U.det ^ 2 = 1 := by
    have := congrArg det (eigvecs_mul_transpose hA)
    rwa [det_mul, det_transpose, det_one, ← sq] at this
  rw [hU, one_mul]

/-- **Whitening.** A positive definite `B` has `S B Sᵀ = 1` with `S = D^{-1/2} Uᵀ`. -/
lemma exists_mul_mul_transpose_eq_one {B : Matrix n n ℝ} (hB : B.PosDef) :
    ∃ S : Matrix n n ℝ, S * B * Sᵀ = 1 := by
  set U := eigvecs hB.1
  set d : n → ℝ := fun i => (√(hB.1.eigenvalues i))⁻¹
  refine ⟨diagonal d * Uᵀ, ?_⟩
  have hpos := hB.eigenvalues_pos
  rw [transpose_mul, transpose_transpose, diagonal_transpose]
  conv_lhs => rw [eq_eigvecs hB.1]
  calc diagonal d * Uᵀ * (U * diagonal hB.1.eigenvalues * Uᵀ) * (U * diagonal d)
      = diagonal d * (Uᵀ * U) * diagonal hB.1.eigenvalues * (Uᵀ * U) * diagonal d := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [eigvecs_transpose_mul, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal,
          diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        have h := hpos i
        simp only [d]
        have hs : √(hB.1.eigenvalues i) * √(hB.1.eigenvalues i) = hB.1.eigenvalues i :=
          mul_self_sqrt h.le
        have hs0 : √(hB.1.eigenvalues i) ≠ 0 := (sqrt_pos.2 h).ne'
        field_simp
        linarith

/-- `det (1 + M) ≥ 1` for a positive semidefinite `M`. -/
lemma one_le_det_one_add {M : Matrix n n ℝ} (hM : M.PosSemidef) : 1 ≤ (1 + M).det := by
  have h := det_smul_one_add_smul hM.1 1 1
  simp only [one_smul, one_mul] at h
  rw [h]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, (1 + hM.1.eigenvalues i) := prod_le_prod₀ (fun _ _ => zero_le_one)
        fun i _ => by linarith [hM.eigenvalues_nonneg i]

/-- **Lemma 9.6.2.** If `B` and `A - B` are positive semidefinite, then `|B| ≤ |A|`. -/
theorem det_le_det_of_posSemidef_sub {A B : Matrix n n ℝ} (hB : B.PosSemidef)
    (hAB : (A - B).PosSemidef) : B.det ≤ A.det := by
  have hA : A.PosSemidef := by simpa using hB.add hAB
  rcases hB.det_nonneg.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact hA.det_nonneg
  have hBpd : B.PosDef := hB.posDef_iff_det_ne_zero.2 hpos.ne'
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hBpd
  have hM : (S * (A - B) * Sᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hAB.mul_mul_conjTranspose_same S
  have hSA : S * A * Sᵀ = 1 + S * (A - B) * Sᵀ := by
    rw [← hS, ← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel]
  have h1 := one_le_det_one_add hM
  rw [← hSA, det_mul_mul_transpose] at h1
  have h2 := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at h2
  have hs : 0 < S.det ^ 2 := by
    rcases (sq_nonneg S.det).eq_or_lt with h | h
    · rw [← h, zero_mul] at h2; exact absurd h2 zero_ne_one
    · exact h
  have : S.det ^ 2 * B.det ≤ S.det ^ 2 * A.det := by linarith
  exact le_of_mul_le_mul_left this hs

/-- **Lemma 9.6.4.** The determinant is log-concave on positive semidefinite matrices: for
`0 ≤ t ≤ 1`, `|A|^t |B|^{1-t} ≤ |t A + (1 - t) B|`. -/
theorem det_rpow_mul_det_rpow_le {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    A.det ^ t * B.det ^ (1 - t) ≤ (t • A + (1 - t) • B).det := by
  have hC : (t • A + (1 - t) • B).PosSemidef := (hA.smul ht0).add (hB.smul (by linarith))
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp
  rcases hA.det_nonneg.eq_or_lt with hA0 | hApos
  · rw [← hA0, zero_rpow ht0'.ne', zero_mul]
    exact hC.det_nonneg
  rcases hB.det_nonneg.eq_or_lt with hB0 | hBpos
  · rw [← hB0, zero_rpow (by linarith), mul_zero]
    exact hC.det_nonneg
  have hApd : A.PosDef := hA.posDef_iff_det_ne_zero.2 hApos.ne'
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hApd
  have hM : (S * B * Sᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hB.mul_mul_conjTranspose_same S
  have hSC : S * (t • A + (1 - t) • B) * Sᵀ =
      t • (1 : Matrix n n ℝ) + (1 - t) • (S * B * Sᵀ) := by
    rw [← hS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  -- `det (t • 1 + (1 - t) • M) ≥ det M ^ (1 - t)` by the weighted AM-GM inequality.
  have hamgm : (S * B * Sᵀ).det ^ (1 - t) ≤
      (t • (1 : Matrix n n ℝ) + (1 - t) • (S * B * Sᵀ)).det := by
    rw [det_smul_one_add_smul hM.1, hM.1.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [← finsetProd_rpow _ _ fun i _ => hM.eigenvalues_nonneg i]
    refine prod_le_prod₀ (fun i _ => rpow_nonneg (hM.eigenvalues_nonneg i) _) fun i _ => ?_
    have h := geom_mean_le_arith_mean2_weighted ht0'.le (by linarith : 0 ≤ 1 - t) zero_le_one
      (hM.eigenvalues_nonneg i) (by ring)
    rwa [one_rpow, one_mul, mul_one] at h
  rw [← hSC, det_mul_mul_transpose, det_mul_mul_transpose] at hamgm
  have h2 := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at h2
  set s := S.det ^ 2
  have hs : 0 < s := by
    rcases (sq_nonneg S.det).eq_or_lt with h | h
    · have h0 : s = 0 := h.symm
      rw [h0, zero_mul] at h2
      exact absurd h2 zero_ne_one
    · exact h
  -- `det A^t det B^{1-t} = s^{-t} det B^{1-t} ≤ s^{-t} s^t det C = det C`.
  rw [mul_rpow hs.le hBpos.le] at hamgm
  have hsA : A.det = s⁻¹ := eq_inv_of_mul_eq_one_right h2
  have hB' : B.det ^ (1 - t) ≤ s ^ t * (t • A + (1 - t) • B).det := by
    have h3 : s ^ (1 - t) * B.det ^ (1 - t) ≤
        s ^ (1 - t) * (s ^ t * (t • A + (1 - t) • B).det) := by
      calc s ^ (1 - t) * B.det ^ (1 - t) ≤ s * (t • A + (1 - t) • B).det := hamgm
        _ = _ := by rw [← mul_assoc, ← rpow_add hs, sub_add_cancel, rpow_one]
    exact le_of_mul_le_mul_left h3 (rpow_pos_of_pos hs _)
  calc A.det ^ t * B.det ^ (1 - t) = s ^ (-t) * B.det ^ (1 - t) := by
        rw [hsA, inv_rpow hs.le, ← rpow_neg hs.le]
    _ ≤ s ^ (-t) * (s ^ t * (t • A + (1 - t) • B).det) :=
        mul_le_mul_of_nonneg_left hB' (rpow_nonneg hs.le _)
    _ = (t • A + (1 - t) • B).det := by
        rw [← mul_assoc, ← rpow_add hs, neg_add_cancel, rpow_zero, one_mul]

end InfoTheory
