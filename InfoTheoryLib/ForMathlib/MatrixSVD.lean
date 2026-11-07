/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.MatrixDet
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The singular value decomposition and the log-determinant

A singular value decomposition of a real rectangular matrix, and bounds on `log |A|` for positive
definite `A`.

## Main statements

* `exists_svd`: `G = U D Ψᵀ` with `U` orthogonal, `D = diag(γ)` with `γ ≥ 0`, and `Ψ` with
  orthonormal columns where `γ ≠ 0` and zero columns where `γ = 0`.
* `trace_transpose_mul_mul_le`: `tr(Ψᵀ K Ψ) ≤ tr K` for such a `Ψ` and a positive semidefinite `K`.
* `log_det_le_trace_sub_card`: `log |B| - log |A| ≤ tr(A⁻¹ B) - dim` for positive definite `A`, `B`.
* `concaveOn_log_det`: `log |A|` is concave on positive definite matrices.

## Implementation notes

The usual reduced decomposition `G = Φ Γ Ψᵀ` has `Γ` of size `d = rank G`. We keep the index set of
the outputs and allow `γ = 0`, because then `U` is a square orthogonal matrix, which is what is
needed to rotate noise vectors.

The decomposition comes from the spectral theorem for `G Gᵀ = U Λ Uᵀ`, with `γ = √Λ` and
`Ψ = Gᵀ U Λ^{-1/2}`, where `0⁻¹ = 0`.
-/

@[expose] public section

open Matrix Real Finset

namespace InfoTheory

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]

/-! ### Positive semidefinite products -/

omit [Fintype r] [DecidableEq r] [DecidableEq t] in
lemma posSemidef_mul_mul_transpose [Finite r] {K : Matrix t t ℝ} (hK : K.PosSemidef)
    (G : Matrix r t ℝ) : (G * K * Gᵀ).PosSemidef := by
  have := Fintype.ofFinite r
  simpa [conjTranspose_eq_transpose_of_trivial] using hK.mul_mul_conjTranspose_same G

omit [Fintype t] [DecidableEq r] [DecidableEq t] in
lemma posSemidef_transpose_mul_mul [Finite t] {K : Matrix r r ℝ} (hK : K.PosSemidef)
    (G : Matrix r t ℝ) : (Gᵀ * K * G).PosSemidef := by
  have := Fintype.ofFinite t
  simpa [conjTranspose_eq_transpose_of_trivial] using hK.conjTranspose_mul_mul_same G

omit [Fintype r] [DecidableEq r] [DecidableEq t] in
lemma posSemidef_self_mul_transpose [Finite r] (G : Matrix r t ℝ) : (G * Gᵀ).PosSemidef := by
  have := Fintype.ofFinite r
  simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose G

omit [Fintype r] in
lemma posDef_add_one {K : Matrix r r ℝ} (hK : K.PosSemidef) : (K + 1).PosDef :=
  Matrix.PosDef.posSemidef_add hK PosDef.one

omit [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t] in
/-- For real matrices, `Aᵀ A = 0` implies `A = 0`. -/
lemma eq_zero_of_transpose_mul_eq_zero [Fintype t] {A : Matrix t r ℝ} (h : Aᵀ * A = 0) : A = 0 := by
  refine conjTranspose_mul_self_eq_zero.1 ?_
  rw [conjTranspose_eq_transpose_of_trivial]
  exact h

omit [Fintype t] [DecidableEq r] [DecidableEq t] in
/-- For real matrices, `A Aᵀ = 0` implies `A = 0`. -/
lemma eq_zero_of_mul_transpose_eq_zero {A : Matrix t r ℝ} (h : A * Aᵀ = 0) : A = 0 := by
  refine self_mul_conjTranspose_eq_zero.1 ?_
  rw [conjTranspose_eq_transpose_of_trivial]
  exact h

omit [DecidableEq t] in
/-- A positive semidefinite matrix is `Cᵀ C`. -/
lemma exists_eq_transpose_mul_self {A : Matrix t t ℝ} (hA : A.PosSemidef) :
    ∃ C : Matrix t t ℝ, A = Cᵀ * C := by
  classical
  refine ⟨diagonal (fun i => √(hA.1.eigenvalues i)) * (eigvecs hA.1)ᵀ, ?_⟩
  simp only [transpose_mul, transpose_transpose, diagonal_transpose]
  conv_lhs => rw [eq_eigvecs hA.1]
  have e : diagonal hA.1.eigenvalues = diagonal (fun i => √(hA.1.eigenvalues i)) *
      diagonal (fun i => √(hA.1.eigenvalues i)) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact (mul_self_sqrt (hA.eigenvalues_nonneg i)).symm
  rw [e]
  simp only [Matrix.mul_assoc]

omit [DecidableEq t] in
/-- The trace of the product of positive semidefinite matrices is nonnegative. -/
lemma trace_mul_nonneg_of_posSemidef {A B : Matrix t t ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, rfl⟩ := exists_eq_transpose_mul_self hA
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc C]
  exact (posSemidef_mul_mul_transpose hB C).trace_nonneg

/-! ### The singular value decomposition -/

omit [DecidableEq t] in
/-- **The singular value decomposition.** Every real matrix is `G = U D Ψᵀ` with `U` orthogonal,
`D = diag(γ)`, `γ ≥ 0`, and `Ψᵀ Ψ = diag(s)` where `s = 1` if `γ ≠ 0` and `s = 0` otherwise. -/
theorem exists_svd (G : Matrix r t ℝ) :
    ∃ (U : Matrix r r ℝ) (Ψ : Matrix t r ℝ) (γ : r → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ (∀ k, 0 ≤ γ k) ∧
      G = U * diagonal γ * Ψᵀ ∧ Ψᵀ * Ψ = diagonal fun k => if γ k = 0 then 0 else 1 := by
  have hA := posSemidef_self_mul_transpose G
  set U := eigvecs hA.1
  set lam := hA.1.eigenvalues
  have hlam : ∀ k, 0 ≤ lam k := hA.eigenvalues_nonneg
  have hUU : Uᵀ * U = 1 := eigvecs_transpose_mul hA.1
  have hUU' : U * Uᵀ = 1 := eigvecs_mul_transpose hA.1
  have hspec : G * Gᵀ = U * diagonal lam * Uᵀ := eq_eigvecs hA.1
  have hUGG : Uᵀ * (G * Gᵀ) * U = diagonal lam := by
    rw [hspec]
    calc Uᵀ * (U * diagonal lam * Uᵀ) * U = (Uᵀ * U) * diagonal lam * (Uᵀ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal lam := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  set γ : r → ℝ := fun k => √(lam k)
  set d : r → ℝ := fun k => if γ k = 0 then 0 else (γ k)⁻¹
  set s : r → ℝ := fun k => if γ k = 0 then 0 else 1
  have hγ2 : ∀ k, γ k * γ k = lam k := fun k => mul_self_sqrt (hlam k)
  have hdγ : ∀ k, d k * γ k = s k := fun k => by
    simp only [d, s]
    split_ifs with h
    · simp
    · exact inv_mul_cancel₀ h
  have hd2 : ∀ k, d k * lam k * d k = s k := fun k => by
    rw [← hγ2]
    simp only [d, s]
    split_ifs with h
    · simp
    · field_simp
  refine ⟨U, Gᵀ * U * diagonal d, γ, hUU, hUU', fun k => sqrt_nonneg _, ?_, ?_⟩
  · -- `U (1 - s) Uᵀ G = 0`, because its product with its transpose vanishes.
    set W : Matrix r t ℝ := U * diagonal (fun k => 1 - s k) * Uᵀ * G with hW
    have hW0 : W = 0 := by
      refine eq_zero_of_mul_transpose_eq_zero ?_
      have ht : Wᵀ = Gᵀ * U * diagonal (fun k => 1 - s k) * Uᵀ := by
        simp only [hW, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
      have hzero : diagonal (fun k => 1 - s k) * diagonal lam * diagonal (fun k => 1 - s k) =
          (0 : Matrix r r ℝ) := by
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_zero]
        congr 1
        funext k
        by_cases h : γ k = 0
        · have hl : lam k = 0 := by rw [← hγ2, h, mul_zero]
          simp [hl]
        · simp [s, h]
      calc W * Wᵀ = U * diagonal (fun k => 1 - s k) * (Uᵀ * (G * Gᵀ) * U) *
            diagonal (fun k => 1 - s k) * Uᵀ := by
            rw [ht, hW]
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [hUGG]
            calc U * diagonal (fun k => 1 - s k) * diagonal lam * diagonal (fun k => 1 - s k) * Uᵀ
                = U * (diagonal (fun k => 1 - s k) * diagonal lam *
                    diagonal (fun k => 1 - s k)) * Uᵀ := by
                  simp only [Matrix.mul_assoc]
              _ = 0 := by rw [hzero]; simp
    have hD : diagonal γ * (Gᵀ * U * diagonal d)ᵀ = diagonal s * Uᵀ * G := by
      simp only [transpose_mul, transpose_transpose, diagonal_transpose]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, diagonal_mul_diagonal]
      congr 3
      funext k
      rw [mul_comm, hdγ]
    have hsum : diagonal s + diagonal (fun k => 1 - s k) = (1 : Matrix r r ℝ) := by
      rw [diagonal_add, ← diagonal_one]
      congr 1
      funext k
      ring
    have h1 : G = (U * (diagonal s + diagonal (fun k => 1 - s k)) * Uᵀ) * G := by
      rw [hsum, Matrix.mul_one, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc U, hD]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul] at h1
    rw [← hW, hW0, add_zero] at h1
    calc G = U * diagonal s * Uᵀ * G := h1
      _ = U * (diagonal s * Uᵀ * G) := by simp only [Matrix.mul_assoc]
  · have e : (Gᵀ * U * diagonal d)ᵀ * (Gᵀ * U * diagonal d) =
        diagonal d * (Uᵀ * (G * Gᵀ) * U) * diagonal d := by
      simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    rw [e, hUGG, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    exact hd2 k

section SemiOrthogonal

variable {Ψ : Matrix t r ℝ} {s : r → ℝ}

omit [DecidableEq t] in
/-- `Ψ` has orthonormal columns or zero columns, according to `s`, so that `Ψ s = Ψ`. -/
private lemma mul_diagonal_of_transpose_mul (hΨ : Ψᵀ * Ψ = diagonal s)
    (hs : ∀ k, s k = 0 ∨ s k = 1) : Ψ * diagonal s = Ψ := by
  have h0 : (Ψ * diagonal fun k => 1 - s k) = 0 := by
    refine eq_zero_of_transpose_mul_eq_zero ?_
    simp only [transpose_mul, diagonal_transpose]
    calc diagonal (fun k => 1 - s k) * Ψᵀ * (Ψ * diagonal fun k => 1 - s k)
        = diagonal (fun k => 1 - s k) * (Ψᵀ * Ψ) * diagonal (fun k => 1 - s k) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [hΨ, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_zero]
          congr 1
          funext k
          rcases hs k with h | h <;> simp [h]
  have hsum : diagonal s + diagonal (fun k => 1 - s k) = (1 : Matrix r r ℝ) := by
    rw [diagonal_add, ← diagonal_one]
    congr 1
    funext k
    ring
  calc Ψ * diagonal s = Ψ * diagonal s + Ψ * diagonal (fun k => 1 - s k) := by rw [h0, add_zero]
    _ = Ψ := by rw [← Matrix.mul_add, hsum, Matrix.mul_one]

/-- `Ψ Ψᵀ ≼ 1`: the matrix `Ψ Ψᵀ` is a projection. -/
lemma one_sub_mul_transpose_posSemidef (hΨ : Ψᵀ * Ψ = diagonal s) (hs : ∀ k, s k = 0 ∨ s k = 1) :
    (1 - Ψ * Ψᵀ).PosSemidef := by
  have hp : (Ψ * Ψᵀ) * (Ψ * Ψᵀ) = Ψ * Ψᵀ := by
    calc (Ψ * Ψᵀ) * (Ψ * Ψᵀ) = Ψ * (Ψᵀ * Ψ) * Ψᵀ := by simp only [Matrix.mul_assoc]
      _ = Ψ * Ψᵀ := by rw [hΨ, mul_diagonal_of_transpose_mul hΨ hs]
  have ht : (1 - Ψ * Ψᵀ)ᵀ = 1 - Ψ * Ψᵀ := by
    simp [transpose_sub, transpose_mul]
  have e : (1 - Ψ * Ψᵀ) = (1 - Ψ * Ψᵀ) * (1 - Ψ * Ψᵀ)ᵀ := by
    rw [ht, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hp, sub_self, sub_zero]
  rw [e]
  exact posSemidef_self_mul_transpose _

omit [DecidableEq t] in
/-- `tr(Ψᵀ K Ψ) ≤ tr K` for a positive semidefinite `K`. -/
theorem trace_transpose_mul_mul_le (hΨ : Ψᵀ * Ψ = diagonal s) (hs : ∀ k, s k = 0 ∨ s k = 1)
    {K : Matrix t t ℝ} (hK : K.PosSemidef) : (Ψᵀ * K * Ψ).trace ≤ K.trace := by
  classical
  have hQ := one_sub_mul_transpose_posSemidef hΨ hs
  -- Writing `1 - Ψ Ψᵀ = Q Qᵀ` with `Q = 1 - Ψ Ψᵀ` (a projection).
  have hp : (1 - Ψ * Ψᵀ) * (1 - Ψ * Ψᵀ)ᵀ = 1 - Ψ * Ψᵀ := by
    have ht : (1 - Ψ * Ψᵀ)ᵀ = 1 - Ψ * Ψᵀ := by simp [transpose_sub, transpose_mul]
    have hpp : (Ψ * Ψᵀ) * (Ψ * Ψᵀ) = Ψ * Ψᵀ := by
      calc (Ψ * Ψᵀ) * (Ψ * Ψᵀ) = Ψ * (Ψᵀ * Ψ) * Ψᵀ := by simp only [Matrix.mul_assoc]
        _ = Ψ * Ψᵀ := by rw [hΨ, mul_diagonal_of_transpose_mul hΨ hs]
    rw [ht, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hpp, sub_self,
      sub_zero]
  have h0 : 0 ≤ ((1 - Ψ * Ψᵀ)ᵀ * K * (1 - Ψ * Ψᵀ)).trace :=
    (posSemidef_transpose_mul_mul hK _).trace_nonneg
  have e1 : ((1 - Ψ * Ψᵀ)ᵀ * K * (1 - Ψ * Ψᵀ)).trace = K.trace - (Ψᵀ * K * Ψ).trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hp, Matrix.sub_mul, Matrix.one_mul, trace_sub,
      Matrix.mul_assoc Ψ, trace_mul_comm Ψ]
  linarith

end SemiOrthogonal

/-! ### The log-determinant -/

section LogDet

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private lemma log_sum_le {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    ∑ i, log (x i) ≤ ∑ i, x i - Fintype.card ι := by
  have h : ∑ i, log (x i) ≤ ∑ i, (x i - 1) := sum_le_sum fun i _ => log_le_sub_one_of_pos (hx i)
  simpa [sum_sub_distrib] using h

/-- `log |M| ≤ tr M - dim` for a positive definite `M`. -/
lemma log_det_le_trace_sub_card' {M : Matrix n n ℝ} (hM : M.PosDef) :
    log M.det ≤ M.trace - Fintype.card n := by
  rw [hM.1.det_eq_prod_eigenvalues, hM.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [log_prod fun i _ => (hM.eigenvalues_pos i).ne']
  exact log_sum_le hM.eigenvalues_pos

/-- **Whitening.** For positive definite `A` and `B`, the matrix `M = S B Sᵀ` with `S A Sᵀ = I` is
positive definite, with `log |M| = log |B| - log |A|` and `tr M = tr(A⁻¹ B)`, and `M = I` only if
`B = A`. -/
lemma exists_whitened {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    ∃ M : Matrix n n ℝ, M.PosDef ∧ log B.det - log A.det = log M.det ∧ (A⁻¹ * B).trace = M.trace ∧
      (M = 1 → B = A) := by
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hA
  have hdet := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at hdet
  have hSdet : S.det ≠ 0 := fun h => by simp [h] at hdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hSdet
  have hM : (S * B * Sᵀ).PosDef := by
    refine (posSemidef_mul_mul_transpose hB.posSemidef S).posDef_iff_det_ne_zero.2 ?_
    rw [det_mul_mul_transpose]
    exact mul_ne_zero (pow_ne_zero 2 hSdet) hB.det_pos.ne'
  have hSS : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
  have hAinv : A⁻¹ = Sᵀ * S := by
    have h1 : A * (Sᵀ * S) = 1 := by
      have h2 : S⁻¹ * (S * A * Sᵀ) * S = S⁻¹ * 1 * S := by rw [hS]
      calc A * (Sᵀ * S) = (S⁻¹ * S) * A * Sᵀ * S := by rw [hSS]; simp only [Matrix.mul_assoc,
            Matrix.one_mul]
        _ = S⁻¹ * (S * A * Sᵀ) * S := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hSS]
    exact inv_eq_right_inv h1
  have hlog : log (S.det ^ 2) = - log A.det := by
    have : S.det ^ 2 = (A.det)⁻¹ := eq_inv_of_mul_eq_one_left hdet
    rw [this, log_inv]
  refine ⟨S * B * Sᵀ, hM, ?_, ?_, fun h1 => ?_⟩
  · rw [det_mul_mul_transpose, log_mul (pow_ne_zero 2 hSdet) hB.det_pos.ne', hlog]
    ring
  · rw [hAinv, Matrix.mul_assoc, trace_mul_comm]
  · have hSt : IsUnit Sᵀ.det := by rwa [det_transpose]
    have hc : S * B * Sᵀ = S * A * Sᵀ := by rw [h1, hS]
    have hc₂ : S * B = S * A := by
      have := congrArg (· * (Sᵀ)⁻¹) hc
      simpa [Matrix.mul_assoc, mul_nonsing_inv _ hSt] using this
    have := congrArg (S⁻¹ * ·) hc₂
    simpa [← Matrix.mul_assoc, hSS] using this

/-- **The tangent bound for `log |A|`:** for positive definite `A` and `B`,
`log |B| - log |A| ≤ tr(A⁻¹ B) - dim`. -/
theorem log_det_le_trace_sub_card {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    log B.det - log A.det ≤ (A⁻¹ * B).trace - Fintype.card n := by
  obtain ⟨M, hM, h₁, h₂, -⟩ := exists_whitened hA hB
  rw [h₁, h₂]
  exact log_det_le_trace_sub_card' hM

/-- **Concavity of `log |A|`** on positive definite matrices. -/
theorem concaveOn_log_det : ConcaveOn ℝ {A : Matrix n n ℝ | A.PosDef} fun A => log A.det := by
  refine ⟨fun A hA B hB a b ha hb hab => ?_, fun A hA B hB a b ha hb hab => ?_⟩
  · rcases ha.eq_or_lt with rfl | ha'
    · have hb1 : b = 1 := by linarith
      simpa [hb1] using hB
    rcases hb.eq_or_lt with rfl | hb'
    · have ha1 : a = 1 := by linarith
      simpa [ha1] using hA
    exact Matrix.PosDef.add (hA.smul ha') (hB.smul hb')
  · have hb' : b = 1 - a := by linarith
    subst hb'
    have h := det_rpow_mul_det_rpow_le (t := a) hA.posSemidef hB.posSemidef ha (by linarith)
    have hC : 0 < (a • A + (1 - a) • B).det := by
      refine lt_of_lt_of_le (mul_pos (rpow_pos_of_pos hA.det_pos _)
        (rpow_pos_of_pos hB.det_pos _)) h
    have := log_le_log (mul_pos (rpow_pos_of_pos hA.det_pos _) (rpow_pos_of_pos hB.det_pos _)) h
    rw [log_mul (rpow_pos_of_pos hA.det_pos _).ne' (rpow_pos_of_pos hB.det_pos _).ne',
      log_rpow hA.det_pos, log_rpow hB.det_pos] at this
    simpa [smul_eq_mul] using this

end LogDet

end InfoTheory
