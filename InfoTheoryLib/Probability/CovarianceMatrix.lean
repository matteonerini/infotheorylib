/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.MMSE
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Integration

/-!
# Covariance and correlation matrices of random vectors

For a random vector `X = (X₁, …, Xₙ)` with square-integrable components, the covariance matrix is
`K_X = [cov(Xᵢ, Xⱼ)]` and the correlation matrix is `K̃_X = [E Xᵢ Xⱼ]`. Both are symmetric and
positive semidefinite, and a linear map `Y = AX` transforms them to `A K Aᵀ`.

## Main definitions

* `covMatrix μ X`: the covariance matrix `K_X`, (10.6).
* `corrMatrix μ X`: the correlation matrix `K̃_X`, (10.7).

## Main statements

* `corrMatrix_eq_covMatrix_add`: (10.12), `K̃_X = K_X + (EX)(EX)ᵀ`.
* `posSemidef_covMatrix`, `posSemidef_corrMatrix`: Proposition 10.3.
* `covMatrix_mulVec`, `corrMatrix_mulVec`: Proposition 10.5, `K_{AX} = A K_X Aᵀ`.
* `covMatrix_transpose_mulVec`: Proposition 10.6, an orthogonal diagonalization decorrelates.
* `covMatrix_add_of_indepFun`: Proposition 10.8, `K_{X+Z} = K_X + K_Z` for independent `X`, `Z`.
* `sum_sq_mulVec_of_orthogonal`, `integral_sum_sq_mulVec_of_orthogonal`: Proposition 10.9, an
  orthogonal transformation preserves the energy.
* `corrMatrix_add_of_indepFun`: Lemma 11.33, `K̃_{X+Z} = K̃_X + K̃_Z` for a zero-mean `X`
  independent of `Z`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 10.1 and 11.9
-/

open MeasureTheory ProbabilityTheory Matrix Finset Filter

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι] [Fintype κ]

/-- **(10.7)** The correlation matrix `K̃_X = [E Xᵢ Xⱼ]` of a random vector, the counterpart of
the covariance matrix `covMatrix μ X` (`Probability.MMSE`) of (10.6). -/
def corrMatrix (μ : Measure Ω) (X : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ ω, X i ω * X j ω ∂μ

omit [Fintype ι] in
/-- **(10.8)–(10.12)** `K̃_X = K_X + (EX)(EX)ᵀ`. -/
theorem corrMatrix_eq_covMatrix_add [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) :
    corrMatrix μ X = covMatrix μ X + Matrix.vecMulVec (fun i => ∫ ω, X i ω ∂μ)
      (fun i => ∫ ω, X i ω ∂μ) := by
  ext i j
  simp only [corrMatrix, covMatrix, Matrix.of_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    covariance_eq_sub (hX i) (hX j)]
  simp

/-! ### Proposition 10.3 -/

omit [Fintype ι] in
/-- The integral of a double finite sum. -/
lemma integral_sum_sum {ι' : Type*} [Fintype ι] [Fintype ι'] {F : ι → ι' → Ω → ℝ}
    (h : ∀ k l, Integrable (F k l) μ) :
    ∫ ω, ∑ k, ∑ l, F k l ω ∂μ = ∑ k, ∑ l, ∫ ω, F k l ω ∂μ := by
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => h k l]
  exact sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => h k l

/-- The quadratic form of the covariance matrix is a variance:
`vᵀ K_X v = cov(∑ᵢ vᵢ Xᵢ, ∑ᵢ vᵢ Xᵢ)`. -/
lemma dotProduct_covMatrix_mulVec [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (v : ι → ℝ) :
    v ⬝ᵥ (covMatrix μ X *ᵥ v) =
      cov[fun ω => ∑ i, v i * X i ω, fun ω => ∑ i, v i * X i ω; μ] := by
  have hY : ∀ i, MemLp (fun ω => v i * X i ω) 2 μ := fun i => (hX i).const_mul (v i)
  rw [covariance_fun_sum_fun_sum hY hY]
  simp only [dotProduct, mulVec, covMatrix, Matrix.of_apply, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

omit [Fintype ι] in
/-- **Proposition 10.3.** A covariance matrix is symmetric and positive semidefinite. -/
theorem posSemidef_covMatrix [Finite ι] [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) : (covMatrix μ X).PosSemidef := by
  have := Fintype.ofFinite ι
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, covMatrix, Matrix.of_apply]
    exact covariance_comm _ _
  · rw [star_trivial, dotProduct_covMatrix_mulVec hX]
    exact integral_nonneg fun ω => mul_self_nonneg _

omit [Fintype ι] in
/-- **Proposition 10.3.** A correlation matrix is symmetric and positive semidefinite. -/
theorem posSemidef_corrMatrix [Finite ι] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) : (corrMatrix μ X).PosSemidef := by
  have := Fintype.ofFinite ι
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, corrMatrix, Matrix.of_apply]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  · rw [star_trivial]
    have h : v ⬝ᵥ (corrMatrix μ X *ᵥ v) =
        ∫ ω, (∑ i, v i * X i ω) * (∑ i, v i * X i ω) ∂μ := by
      have hint : ∀ i j, Integrable (fun ω => v i * X i ω * (v j * X j ω)) μ :=
        fun i j => ((hX i).const_mul (v i)).integrable_mul ((hX j).const_mul (v j))
      simp_rw [sum_mul_sum]
      rw [integral_sum_sum hint]
      simp only [dotProduct, mulVec, corrMatrix, Matrix.of_apply, mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [show (fun ω => v i * X i ω * (v j * X j ω)) = fun ω => (v i * v j) * (X i ω * X j ω)
        from funext fun ω => by ring, integral_const_mul]
      ring
    rw [h]
    exact integral_nonneg fun ω => mul_self_nonneg _

/-! ### Linear transformations -/

omit [Fintype κ] in
/-- **Proposition 10.5, (10.28).** `K_{AX} = A K_X Aᵀ`. -/
theorem covMatrix_mulVec [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (A : Matrix κ ι ℝ) :
    covMatrix μ (fun k ω => (A *ᵥ fun i => X i ω) k) = A * covMatrix μ X * Aᵀ := by
  ext i j
  have hY : ∀ (i : κ) (k : ι), MemLp (fun ω => A i k * X k ω) 2 μ :=
    fun i k => (hX k).const_mul (A i k)
  simp only [covMatrix, Matrix.of_apply, mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum (hY i) (hY j)]
  simp only [Matrix.mul_apply, transpose_apply, Matrix.of_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

omit [Fintype κ] in
/-- **Proposition 10.5, (10.29).** `K̃_{AX} = A K̃_X Aᵀ`. -/
theorem corrMatrix_mulVec {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (A : Matrix κ ι ℝ) :
    corrMatrix μ (fun k ω => (A *ᵥ fun i => X i ω) k) = A * corrMatrix μ X * Aᵀ := by
  ext i j
  have hint : ∀ k l, Integrable (fun ω => A i k * X k ω * (A j l * X l ω)) μ :=
    fun k l => ((hX k).const_mul (A i k)).integrable_mul ((hX l).const_mul (A j l))
  simp only [corrMatrix, Matrix.of_apply, mulVec, dotProduct]
  simp_rw [sum_mul_sum]
  rw [integral_sum_sum hint]
  simp only [Matrix.mul_apply, transpose_apply, Matrix.of_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  rw [← integral_const_mul, ← integral_mul_const]
  exact integral_congr_ae (Eventually.of_forall fun ω => by ring)

/-- **Proposition 10.6.** If `K_X = Q Λ Qᵀ` with `Q` orthogonal, the random vector `Y = Qᵀ X` has
covariance matrix `Λ`: a diagonal `Λ` makes the `Yᵢ` uncorrelated, with variances `λᵢ`. -/
theorem covMatrix_transpose_mulVec [DecidableEq ι] [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) {Q Λ : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1)
    (hK : covMatrix μ X = Q * Λ * Qᵀ) : covMatrix μ (fun k ω => (Qᵀ *ᵥ fun i => X i ω) k) = Λ := by
  rw [covMatrix_mulVec hX, hK, transpose_transpose]
  calc Qᵀ * (Q * Λ * Qᵀ) * Q = (Qᵀ * Q) * Λ * (Qᵀ * Q) := by simp only [Matrix.mul_assoc]
    _ = Λ := by rw [hQ, Matrix.one_mul, Matrix.mul_one]

omit [Fintype ι] in
/-- **Corollary 10.7.** With `Q` orthogonal, `X = Q Y` for `Y = Qᵀ X`. -/
theorem eq_mulVec_transpose_mulVec [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Q * Qᵀ = 1)
    (x : ι → ℝ) : x = Q *ᵥ (Qᵀ *ᵥ x) := by
  rw [mulVec_mulVec, hQ, one_mulVec]

/-! ### Independent sums and energy -/

omit [Fintype ι] in
/-- **Proposition 10.8.** If `X` and `Z` are independent, `K_{X+Z} = K_X + K_Z`. -/
theorem covMatrix_add_of_indepFun [IsFiniteMeasure μ] {X Z : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hXZ : (fun ω i => X i ω) ⟂ᵢ[μ] (fun ω i => Z i ω)) :
    covMatrix μ (X + Z) = covMatrix μ X + covMatrix μ Z := by
  ext i j
  have hind : ∀ a b, X a ⟂ᵢ[μ] Z b := fun a b =>
    hXZ.comp (measurable_pi_apply a) (measurable_pi_apply b)
  have e : (X + Z) i = X i + Z i := rfl
  have e' : (X + Z) j = X j + Z j := rfl
  simp only [covMatrix, Matrix.of_apply, Matrix.add_apply]
  rw [e, e', covariance_add_left (hX i) (hZ i) ((hX j).add (hZ j)),
    covariance_add_right (hX i) (hX j) (hZ j), covariance_add_right (hZ i) (hX j) (hZ j),
    (hind i j).covariance_eq_zero (hX i) (hZ j),
    (hind j i).symm.covariance_eq_zero (hZ i) (hX j)]
  ring

omit [Fintype ι] in
/-- **(10.43)–(10.47)** An orthogonal transformation preserves `∑ᵢ xᵢ²`. -/
lemma sum_sq_mulVec_of_orthogonal [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Qᵀ * Q = 1) (x : ι → ℝ) : ∑ i, (Q *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
  have h : (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hQ, vecMul_one]
  simpa [dotProduct, sq] using h

/-- **Proposition 10.9.** An orthogonal transformation preserves the total energy:
`E ∑ᵢ Yᵢ² = E ∑ᵢ Xᵢ²` for `Y = QX`. -/
theorem integral_sum_sq_mulVec_of_orthogonal [DecidableEq ι] {X : ι → Ω → ℝ} {Q : Matrix ι ι ℝ}
    (hQ : Qᵀ * Q = 1) : ∫ ω, ∑ i, (Q *ᵥ fun j => X j ω) i ^ 2 ∂μ = ∫ ω, ∑ i, X i ω ^ 2 ∂μ :=
  integral_congr_ae (Eventually.of_forall fun ω => sum_sq_mulVec_of_orthogonal hQ (fun j => X j ω))

omit [Fintype ι] in
/-- **Lemma 11.33, (11.271)–(11.277).** If `X` has zero mean and is independent of `Z`, the
correlation matrices add: `K̃_{X+Z} = K̃_X + K̃_Z`. -/
theorem corrMatrix_add_of_indepFun {X Z : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hXZ : (fun ω i => X i ω) ⟂ᵢ[μ] (fun ω i => Z i ω)) (h0 : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    corrMatrix μ (X + Z) = corrMatrix μ X + corrMatrix μ Z := by
  ext i j
  have hind : ∀ a b, X a ⟂ᵢ[μ] Z b := fun a b =>
    hXZ.comp (measurable_pi_apply a) (measurable_pi_apply b)
  have hcross : ∀ a b, ∫ ω, X a ω * Z b ω ∂μ = 0 := fun a b => by
    have := ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral (hind a b)
      (hX a).aestronglyMeasurable (hZ b).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, h0, zero_mul]
  have hcross' : ∀ a b, ∫ ω, Z a ω * X b ω ∂μ = 0 := fun a b => by
    rw [← hcross b a]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have e : ∀ ω, (X + Z) i ω * (X + Z) j ω =
      (X i ω * X j ω + X i ω * Z j ω) + (Z i ω * X j ω + Z i ω * Z j ω) := fun ω => by
    simp only [Pi.add_apply]; ring
  have i₁ : Integrable (fun ω => X i ω * X j ω) μ := (hX i).integrable_mul (hX j)
  have i₂ : Integrable (fun ω => X i ω * Z j ω) μ := (hX i).integrable_mul (hZ j)
  have i₃ : Integrable (fun ω => Z i ω * X j ω) μ := (hZ i).integrable_mul (hX j)
  have i₄ : Integrable (fun ω => Z i ω * Z j ω) μ := (hZ i).integrable_mul (hZ j)
  simp only [corrMatrix, Matrix.of_apply, Matrix.add_apply, e]
  have h₁ := integral_add (i₁.add i₂) (i₃.add i₄)
  have h₂ := integral_add i₁ i₂
  have h₃ := integral_add i₃ i₄
  simp only [Pi.add_apply] at h₁ h₂ h₃
  rw [h₁, h₂, h₃, hcross, hcross']
  ring

end InfoTheory
