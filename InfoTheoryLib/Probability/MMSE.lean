/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Moments.Covariance

/-!
# Mean squared error estimation

The minimum mean squared error (MMSE) estimate and the linear MMSE estimate, as in Appendix B of
El Gamal and Kim. The random variables live on a general probability space and have finite second
moments.

## Main definitions

* `linMSE μ X Y a b`: the mean squared error of the linear estimate `aᵀ Y + b` of `X`.
* `covMatrix μ Y`: the covariance matrix `K_Y`.
* `covVec μ X Y`: the cross covariance `K_{X Y}`.

## Main statements

* `integral_sq_sub_eq`: `E (X - X̂)² = E (X - E(X | Y))² + E (E(X | Y) - X̂)²`.
* `integral_sq_condExp_le`: the conditional expectation is the MMSE estimate.
* `integral_sq_sub_condExp_eq`, `integral_condVar_eq`: its mean squared error.
* `integral_condVar_add_variance_condExp'`: `Var X = E Var(X | Y) + Var E(X | Y)`.
* `linMSE_eq`: the mean squared error of a linear estimate.
* `linMSE_le_of_orthogonal`, `orthogonal_of_isMin`: **the orthogonality principle**.
* `linMSE_inv`: the linear MMSE estimate for a nonsingular `K_Y`.
* `integral_condVar_le_linMSE`: the MMSE is at most the linear MMSE.
* `matrix_inversion_lemma`: the matrix inversion lemma.
* `covMatrix_noise_inv`, `linMSE_noise`: the additive noise example.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Appendix B
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory Matrix

namespace InfoTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The MMSE estimate -/

section MMSE

variable {m : MeasurableSpace Ω} {X g : Ω → ℝ}

/-- `E ((X - X̂)²) = E ((X - E(X | Y))²) + E ((E(X | Y) - X̂)²)` for an estimate `X̂` measurable
with respect to the observation. -/
theorem integral_sq_sub_eq (hm : m ≤ m₀) (hX : MemLp X 2 μ) (hg : MemLp g 2 μ)
    (hgm : StronglyMeasurable[m] g) :
    ∫ ω, (X ω - g ω) ^ 2 ∂μ =
      ∫ ω, (X ω - (μ[X | m]) ω) ^ 2 ∂μ + ∫ ω, ((μ[X | m]) ω - g ω) ^ 2 ∂μ := by
  set E := μ[X | m] with hE
  have hEL : MemLp E 2 μ := hX.condExp one_le_two
  set h : Ω → ℝ := E - g with hh
  have hhL : MemLp h 2 μ := hEL.sub hg
  have hhm : StronglyMeasurable[m] h := stronglyMeasurable_condExp.sub hgm
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hhX : Integrable (h * X) μ := hhL.integrable_mul hX
  have hhE : Integrable (h * E) μ := hhL.integrable_mul hEL
  -- The error is orthogonal to functions of the observation.
  have hpull : ∫ ω, (h * X) ω ∂μ = ∫ ω, (h * E) ω ∂μ := by
    rw [← integral_condExp hm (f := h * X)]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hhm hhX hXi)
  have horth : ∫ ω, (X ω - E ω) * h ω ∂μ = 0 := by
    have h1 : ∀ ω, (X ω - E ω) * h ω = (h * X) ω - (h * E) ω := fun ω => by
      simp only [Pi.mul_apply]
      ring
    simp only [h1]
    rw [integral_sub hhX hhE, hpull, sub_self]
  have hsq : ∀ {f : Ω → ℝ}, MemLp f 2 μ → Integrable (fun ω => f ω ^ 2) μ := fun hf =>
    hf.integrable_sq
  have hXE : MemLp (X - E) 2 μ := hX.sub hEL
  have h1 : ∀ ω, (X ω - g ω) ^ 2 =
      (X ω - E ω) ^ 2 + (E ω - g ω) ^ 2 + 2 * ((X ω - E ω) * h ω) := fun ω => by
    simp only [hh, Pi.sub_apply]
    ring
  simp only [h1]
  have i1 : Integrable (fun ω => (X ω - E ω) ^ 2) μ := hsq hXE
  have i2 : Integrable (fun ω => (E ω - g ω) ^ 2) μ := hsq hhL
  have i3 : Integrable (fun ω => (X ω - E ω) * h ω) μ := hXE.integrable_mul hhL
  have i12 : Integrable (fun ω => (X ω - E ω) ^ 2 + (E ω - g ω) ^ 2) μ := i1.add i2
  rw [integral_add i12 (i3.const_mul 2), integral_add i1 i2, integral_const_mul, horth]
  ring

/-- **The conditional expectation is the MMSE estimate.** -/
theorem integral_sq_condExp_le (hm : m ≤ m₀) (hX : MemLp X 2 μ) (hg : MemLp g 2 μ)
    (hgm : StronglyMeasurable[m] g) :
    ∫ ω, (X ω - (μ[X | m]) ω) ^ 2 ∂μ ≤ ∫ ω, (X ω - g ω) ^ 2 ∂μ := by
  rw [integral_sq_sub_eq hm hX hg hgm]
  have : 0 ≤ ∫ ω, ((μ[X | m]) ω - g ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  linarith

/-- **The mean squared error of the MMSE estimate**: `E (X - E(X | Y))² = E X² - E (E(X | Y))²`. -/
theorem integral_sq_sub_condExp_eq (hm : m ≤ m₀) (hX : MemLp X 2 μ) :
    ∫ ω, (X ω - (μ[X | m]) ω) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ - ∫ ω, (μ[X | m]) ω ^ 2 ∂μ := by
  have h := integral_sq_sub_eq (g := 0) hm hX (MemLp.zero) stronglyMeasurable_zero
  simp only [Pi.zero_apply, sub_zero] at h
  linarith

/-- **The mean squared error of the MMSE estimate** is `E Var(X | Y)`. -/
theorem integral_condVar_eq (hm : m ≤ m₀) :
    ∫ ω, (Var[X; μ | m]) ω ∂μ = ∫ ω, (X ω - (μ[X | m]) ω) ^ 2 ∂μ := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  unfold condVar
  rw [integral_condExp hm]
  rfl

/-- **The law of total variance** of Appendix B: `Var X = E Var(X | Y) + Var E(X | Y)`. -/
theorem integral_condVar_add_variance_condExp' (hm : m ≤ m₀) (hX : MemLp X 2 μ) :
    Var[X; μ] = ∫ ω, (Var[X; μ | m]) ω ∂μ + Var[μ[X | m]; μ] :=
  (integral_condVar_add_variance_condExp hm hX).symm

end MMSE

/-! ### The linear MMSE estimate -/

section Linear

variable {ι : Type*} [Fintype ι] {X : Ω → ℝ} {Y : ι → Ω → ℝ}

/-- The mean squared error of the linear estimate `aᵀ Y + b` of `X`. -/
def linMSE (μ : Measure Ω) (X : Ω → ℝ) (Y : ι → Ω → ℝ) (a : ι → ℝ) (b : ℝ) : ℝ :=
  ∫ ω, (X ω - (∑ i, a i * Y i ω + b)) ^ 2 ∂μ

/-- The covariance matrix `K_Y`. -/
def covMatrix (μ : Measure Ω) (Y : ι → Ω → ℝ) : Matrix ι ι ℝ := Matrix.of fun i j =>
  cov[Y i, Y j; μ]

/-- The cross covariance `K_{X Y}`. -/
def covVec (μ : Measure Ω) (X : Ω → ℝ) (Y : ι → Ω → ℝ) : ι → ℝ := fun i => cov[X, Y i; μ]

/-- The estimation error of the linear part of an estimate. -/
def linErr (X : Ω → ℝ) (Y : ι → Ω → ℝ) (a : ι → ℝ) : Ω → ℝ := fun ω => X ω - ∑ i, a i * Y i ω

omit [IsProbabilityMeasure μ] in
lemma memLp_linErr (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (a : ι → ℝ) :
    MemLp (linErr X Y a) 2 μ :=
  hX.sub (memLp_finsetSum _ fun i _ => (hY i).const_mul (a i))

/-- The covariance of the error with an observation. -/
lemma cov_linErr (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (a : ι → ℝ) {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) :
    cov[linErr X Y a, Z; μ] = cov[X, Z; μ] - ∑ i, a i * cov[Y i, Z; μ] := by
  have h1 : MemLp (fun ω => ∑ i, a i * Y i ω) 2 μ :=
    memLp_finsetSum _ fun i _ => (hY i).const_mul (a i)
  unfold linErr
  rw [covariance_fun_sub_left hX h1 hZ, covariance_fun_sum_left
    (X := fun i ω => a i * Y i ω) (fun i => (hY i).const_mul (a i)) hZ]
  simp_rw [covariance_const_mul_left]

/-- The variance of the error, as a quadratic form in the coefficients. -/
lemma variance_linErr (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (a : ι → ℝ) :
    Var[linErr X Y a; μ] = Var[X; μ] - 2 * ∑ i, a i * covVec μ X Y i +
      ∑ i, ∑ j, a i * a j * covMatrix μ Y i j := by
  have hE := memLp_linErr hX hY a
  have hEi : AEMeasurable (linErr X Y a) μ := hE.aestronglyMeasurable.aemeasurable
  rw [← covariance_self hEi, cov_linErr hX hY a hE]
  have h1 : cov[X, linErr X Y a; μ] = Var[X; μ] - ∑ i, a i * covVec μ X Y i := by
    rw [covariance_comm, cov_linErr hX hY a hX, covariance_self
      hX.aestronglyMeasurable.aemeasurable]
    simp only [covVec]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [covariance_comm]
  have h2 : ∀ i, cov[Y i, linErr X Y a; μ] = covVec μ X Y i - ∑ j, a j * covMatrix μ Y i j := by
    intro i
    rw [covariance_comm, cov_linErr hX hY a (hY i)]
    simp only [covVec, covMatrix, Matrix.of_apply]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [covariance_comm]
  rw [h1]
  have h3 : ∑ i, a i * cov[Y i, linErr X Y a; μ] =
      ∑ i, a i * covVec μ X Y i - ∑ i, ∑ j, a i * a j * covMatrix μ Y i j := by
    simp only [h2, mul_sub, sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [h3]
  ring

/-- **The mean squared error of a linear estimate**, in terms of the means and the covariances. -/
theorem linMSE_eq (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (a : ι → ℝ) (b : ℝ) :
    linMSE μ X Y a b = Var[X; μ] - 2 * ∑ i, a i * covVec μ X Y i +
      ∑ i, ∑ j, a i * a j * covMatrix μ Y i j + (μ[X] - ∑ i, a i * μ[Y i] - b) ^ 2 := by
  set Z := linErr X Y a with hZ
  have hZL : MemLp Z 2 μ := memLp_linErr hX hY a
  have hmean : μ[Z] = μ[X] - ∑ i, a i * μ[Y i] := by
    simp only [hZ, linErr]
    rw [integral_sub (hX.integrable one_le_two)
      (integrable_finsetSum _ fun i _ => ((hY i).integrable one_le_two).const_mul _),
      integral_finsetSum _ fun i _ => ((hY i).integrable one_le_two).const_mul _]
    simp only [integral_const_mul]
  have h1 : ∀ ω, (X ω - (∑ i, a i * Y i ω + b)) ^ 2 = Z ω ^ 2 - 2 * b * Z ω + b ^ 2 := fun ω => by
    simp only [hZ, linErr]
    ring
  have i1 : Integrable (fun ω => Z ω ^ 2) μ := hZL.integrable_sq
  have i2 : Integrable Z μ := hZL.integrable one_le_two
  have i3 : Integrable (fun ω => Z ω ^ 2 - 2 * b * Z ω) μ := i1.sub (i2.const_mul _)
  unfold linMSE
  simp only [h1]
  rw [integral_add i3 (integrable_const _), integral_sub i1 (i2.const_mul _), integral_const_mul]
  have h2 := variance_eq_sub hZL
  rw [← variance_linErr hX hY a, ← hZ, h2, ← hmean]
  simp only [integral_const, Pi.pow_apply, smul_eq_mul]
  simp
  ring

/-- `K_Y` is positive semidefinite. -/
lemma sum_covMatrix_nonneg (hY : ∀ i, MemLp (Y i) 2 μ) (d : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, d i * d j * covMatrix μ Y i j := by
  have h := variance_linErr (μ := μ) (X := 0) MemLp.zero hY d
  have h2 : 0 ≤ Var[linErr 0 Y d; μ] := ProbabilityTheory.variance_nonneg _ _
  have h3 : Var[(0 : Ω → ℝ); μ] = 0 := by simp
  have h4 : ∀ i, covVec μ (0 : Ω → ℝ) Y i = 0 := fun i => by
    simp [covVec]
  rw [h3] at h
  simp only [h4, mul_zero, sum_const_zero, sub_self, zero_add] at h
  rw [← h]
  exact h2

/-- The normal equations: the error is orthogonal to the observations if and only if
`aᵀ K_Y = K_{X Y}`. -/
lemma cov_linErr_eq_zero_iff (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (a : ι → ℝ) :
    (∀ i, cov[linErr X Y a, Y i; μ] = 0) ↔ ∀ i, ∑ j, a j * covMatrix μ Y j i = covVec μ X Y i := by
  refine forall_congr' fun i => ?_
  rw [cov_linErr hX hY a (hY i)]
  simp only [covVec, covMatrix, Matrix.of_apply]
  exact sub_eq_zero.trans eq_comm

omit [IsProbabilityMeasure μ] [Fintype ι] in
/-- `K_Y` is symmetric. -/
lemma covMatrix_symm (Y : ι → Ω → ℝ) (i j : ι) : covMatrix μ Y i j = covMatrix μ Y j i := by
  simp only [covMatrix, Matrix.of_apply]
  exact covariance_comm _ _

/-- The excess mean squared error of another linear estimate. -/
lemma linMSE_sub (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (a d : ι → ℝ) :
    Var[linErr X Y (a + d); μ] = Var[linErr X Y a; μ] +
      2 * ∑ i, d i * (∑ j, a j * covMatrix μ Y j i - covVec μ X Y i) +
      ∑ i, ∑ j, d i * d j * covMatrix μ Y i j := by
  rw [variance_linErr hX hY, variance_linErr hX hY]
  have e1 : ∑ i, d i * (∑ j, a j * covMatrix μ Y j i - covVec μ X Y i) =
      ∑ i, ∑ j, d i * a j * covMatrix μ Y i j - ∑ i, d i * covVec μ X Y i := by
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by rw [covMatrix_symm Y j i]; ring
  have e2 : ∑ i, (a + d) i * covVec μ X Y i =
      ∑ i, a i * covVec μ X Y i + ∑ i, d i * covVec μ X Y i := by
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
  have e3 : ∑ i, ∑ j, a i * d j * covMatrix μ Y i j = ∑ i, ∑ j, d i * a j * covMatrix μ Y i j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [covMatrix_symm Y j i]; ring
  have e4 : ∑ i, ∑ j, (a + d) i * (a + d) j * covMatrix μ Y i j =
      ∑ i, ∑ j, a i * a j * covMatrix μ Y i j + ∑ i, ∑ j, a i * d j * covMatrix μ Y i j +
        ∑ i, ∑ j, d i * a j * covMatrix μ Y i j + ∑ i, ∑ j, d i * d j * covMatrix μ Y i j := by
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
  rw [e1, e2, e4, e3]
  ring

/-- **The orthogonality principle, sufficiency.** If the error of `aᵀ Y + b` is orthogonal to the
observations and has mean zero, the estimate is the linear MMSE estimate. -/
theorem linMSE_le_of_orthogonal (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) {a : ι → ℝ} {b : ℝ}
    (h : ∀ i, cov[linErr X Y a, Y i; μ] = 0) (hb : b = μ[X] - ∑ i, a i * μ[Y i]) (a' : ι → ℝ)
    (b' : ℝ) : linMSE μ X Y a b ≤ linMSE μ X Y a' b' := by
  have hne := (cov_linErr_eq_zero_iff hX hY a).1 h
  have hsub := linMSE_sub hX hY a (a' - a)
  have hadd : a + (a' - a) = a' := by
    funext i
    simp
  rw [hadd, variance_linErr hX hY a', variance_linErr hX hY a] at hsub
  have hz : ∑ i, (a' - a) i * (∑ j, a j * covMatrix μ Y j i - covVec μ X Y i) = 0 :=
    sum_eq_zero fun i _ => by rw [hne i, sub_self, mul_zero]
  rw [hz] at hsub
  have hd := sum_covMatrix_nonneg (μ := μ) hY (a' - a)
  rw [linMSE_eq hX hY, linMSE_eq hX hY, hb]
  have : 0 ≤ (μ[X] - ∑ i, a' i * μ[Y i] - b') ^ 2 := sq_nonneg _
  have h0 : (μ[X] - ∑ i, a i * μ[Y i] - (μ[X] - ∑ i, a i * μ[Y i])) ^ 2 = 0 := by
    ring
  rw [h0]
  linarith

/-- **The orthogonality principle, necessity.** The error of a linear MMSE estimate is orthogonal
to the observations and has mean zero. -/
theorem orthogonal_of_isMin (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    {a : ι → ℝ} {b : ℝ} (h : ∀ a' b', linMSE μ X Y a b ≤ linMSE μ X Y a' b') :
    (∀ i, cov[linErr X Y a, Y i; μ] = 0) ∧ b = μ[X] - ∑ i, a i * μ[Y i] := by
  classical
  have hb : b = μ[X] - ∑ i, a i * μ[Y i] := by
    have h1 := h a (μ[X] - ∑ i, a i * μ[Y i])
    rw [linMSE_eq hX hY, linMSE_eq hX hY] at h1
    have h2 : (μ[X] - ∑ i, a i * μ[Y i] - b) ^ 2 ≤ 0 := by
      have h3 : (μ[X] - ∑ i, a i * μ[Y i] - (μ[X] - ∑ i, a i * μ[Y i])) ^ 2 = 0 := by ring
      linarith
    have h4 := pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h2 (sq_nonneg _))
    linarith
  refine ⟨(cov_linErr_eq_zero_iff hX hY a).2 fun i => ?_, hb⟩
  -- Perturb one coefficient.
  set N := ∑ j, a j * covMatrix μ Y j i - covVec μ X Y i with hN
  set K := covMatrix μ Y i i with hK
  have hpert : ∀ t : ℝ, 0 ≤ 2 * t * N + t ^ 2 * K := by
    intro t
    have h1 := h (a + Pi.single i t) (μ[X] - ∑ j, (a + Pi.single i t : ι → ℝ) j * μ[Y j])
    have h2 := linMSE_sub hX hY a (Pi.single i t)
    rw [linMSE_eq hX hY, linMSE_eq hX hY, hb] at h1
    rw [variance_linErr hX hY, variance_linErr hX hY] at h2
    have e1 : ∑ k, (Pi.single i t : ι → ℝ) k * (∑ j, a j * covMatrix μ Y j k - covVec μ X Y k) =
        t * N := by
      rw [sum_eq_single i]
      · simp [hN]
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
      · simp
    have e2 : ∑ k, ∑ j, (Pi.single i t : ι → ℝ) k * (Pi.single i t : ι → ℝ) j *
        covMatrix μ Y k j = t ^ 2 * K := by
      rw [sum_eq_single i, sum_eq_single i]
      · simp [hK, sq]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
      · simp
    rw [e1, e2] at h2
    have e3 : (μ[X] - ∑ j, a j * μ[Y j] - (μ[X] - ∑ j, a j * μ[Y j])) ^ 2 = 0 := by ring
    have e4 : (μ[X] - ∑ j, (a + Pi.single i t : ι → ℝ) j * μ[Y j] -
        (μ[X] - ∑ j, (a + Pi.single i t : ι → ℝ) j * μ[Y j])) ^ 2 = 0 := by ring
    rw [e3, e4] at h1
    linarith
  have hK0 : 0 ≤ K := by
    simpa [hK, covMatrix] using
      (covariance_self (X := Y i) (μ := μ) (hY i).aestronglyMeasurable.aemeasurable).symm ▸
        ProbabilityTheory.variance_nonneg (Y i) μ
  -- A nonnegative quadratic without constant term has no linear term.
  have hN0 : N = 0 := by
    by_contra hne
    have h3 := hpert (-N / (|K| + 1))
    have hD : 0 < |K| + 1 := by positivity
    have hNsq : 0 < N ^ 2 := by positivity
    have e : 2 * (-N / (|K| + 1)) * N + (-N / (|K| + 1)) ^ 2 * K =
        -(N ^ 2) * (2 * (|K| + 1) - K) / (|K| + 1) ^ 2 := by
      field_simp
      ring
    rw [e] at h3
    have h4 : 0 < 2 * (|K| + 1) - K := by
      have := le_abs_self K
      linarith [abs_nonneg K]
    have h5 : -(N ^ 2) * (2 * (|K| + 1) - K) / (|K| + 1) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) (by positivity)
    linarith
  linarith

variable [DecidableEq ι]

/-- **The linear MMSE estimate for a nonsingular `K_Y`:** `X̂ = K_{X Y} K_Y⁻¹ (Y - E Y) + E X`, with
mean squared error `K_X - K_{X Y} K_Y⁻¹ K_{Y X}`. -/
theorem linMSE_inv (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (hK : IsUnit (covMatrix μ Y).det) :
    (∀ i, cov[linErr X Y ((covMatrix μ Y)⁻¹ *ᵥ covVec μ X Y), Y i; μ] = 0) ∧
    linMSE μ X Y ((covMatrix μ Y)⁻¹ *ᵥ covVec μ X Y)
      (μ[X] - ∑ i, ((covMatrix μ Y)⁻¹ *ᵥ covVec μ X Y) i * μ[Y i]) =
      Var[X; μ] - covVec μ X Y ⬝ᵥ ((covMatrix μ Y)⁻¹ *ᵥ covVec μ X Y) := by
  set a := (covMatrix μ Y)⁻¹ *ᵥ covVec μ X Y with ha
  have hne : ∀ i, ∑ j, a j * covMatrix μ Y j i = covVec μ X Y i := by
    intro i
    have h1 : covMatrix μ Y *ᵥ a = covVec μ X Y := by
      rw [ha, mulVec_mulVec, Matrix.mul_nonsing_inv _ hK, one_mulVec]
    have h2 := congrFun h1 i
    simp only [mulVec, dotProduct] at h2
    rw [← h2]
    exact sum_congr rfl fun j _ => by rw [covMatrix_symm Y j i, mul_comm]
  refine ⟨(cov_linErr_eq_zero_iff hX hY a).2 hne, ?_⟩
  rw [linMSE_eq hX hY]
  have h3 : ∑ i, ∑ j, a i * a j * covMatrix μ Y i j = ∑ i, a i * covVec μ X Y i := by
    refine sum_congr rfl fun i _ => ?_
    rw [← hne i, mul_sum]
    exact sum_congr rfl fun j _ => by rw [covMatrix_symm Y i j]; ring
  have h4 : covVec μ X Y ⬝ᵥ a = ∑ i, a i * covVec μ X Y i := by
    simp only [dotProduct]
    exact sum_congr rfl fun i _ => mul_comm _ _
  rw [h3, h4]
  ring

/-- **Since the linear MMSE estimate is in general not optimal,**
`E Var(X | Y) ≤ K_X - K_{X Y} K_Y⁻¹ K_{Y X}`. -/
theorem integral_condVar_le_linMSE (hX : MemLp X 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (hYm : ∀ i, Measurable (Y i)) (hK : IsUnit (covMatrix μ Y).det) :
    ∫ ω, (Var[X; μ | MeasurableSpace.comap (fun ω i => Y i ω) inferInstance]) ω ∂μ ≤
      Var[X; μ] - covVec μ X Y ⬝ᵥ ((covMatrix μ Y)⁻¹ *ᵥ covVec μ X Y) := by
  set V : Ω → ι → ℝ := fun ω i => Y i ω with hV
  have hVm : Measurable V := measurable_pi_iff.2 hYm
  have hm : MeasurableSpace.comap V inferInstance ≤ m₀ := hVm.comap_le
  set a := (covMatrix μ Y)⁻¹ *ᵥ covVec μ X Y with ha
  set b := μ[X] - ∑ i, a i * μ[Y i] with hb
  rw [integral_condVar_eq hm, ← (linMSE_inv hX hY hK).2]
  set g : Ω → ℝ := fun ω => ∑ i, a i * Y i ω + b with hg
  have hgL : MemLp g 2 μ :=
    (memLp_finsetSum _ fun i _ => (hY i).const_mul (a i)).add (memLp_const b)
  have hgm : StronglyMeasurable[MeasurableSpace.comap V inferInstance] g := by
    have hc : Continuous fun v : ι → ℝ => ∑ i, a i * v i + b := by fun_prop
    exact (hc.measurable.comp (comap_measurable V)).stronglyMeasurable
  exact integral_sq_condExp_le hm hX hgL hgm

end Linear

/-! ### The matrix inversion lemma -/

section Inversion

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The matrix inversion lemma of Appendix B.** The invertibility of the matrices involved is
implicit in the notes. -/
theorem matrix_inversion_lemma {K₁₁ : Matrix m m ℝ} {K₁₂ : Matrix m n ℝ} {K₂₁ : Matrix n m ℝ}
    {K₂₂ : Matrix n n ℝ} (h₁ : IsUnit K₁₁) (h₂ : IsUnit K₂₂)
    (hS : IsUnit (K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂)) :
    (K₁₁ - K₁₂ * K₂₂⁻¹ * K₂₁)⁻¹ =
      K₁₁⁻¹ + K₁₁⁻¹ * K₁₂ * (K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂)⁻¹ * K₂₁ * K₁₁⁻¹ := by
  have hd₂ := (Matrix.isUnit_iff_isUnit_det _).1 h₂
  have hC : IsUnit (-K₂₂⁻¹) := (Matrix.isUnit_nonsing_inv_iff.2 h₂).neg
  have hCinv : (-K₂₂⁻¹)⁻¹ = -K₂₂ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hd₂]
  have hSne : IsUnit ((-K₂₂⁻¹)⁻¹ + K₂₁ * K₁₁⁻¹ * K₁₂) := by
    rw [hCinv]
    have : -K₂₂ + K₂₁ * K₁₁⁻¹ * K₁₂ = -(K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂) := by
      abel
    rw [this]
    exact hS.neg
  have h := Matrix.add_mul_mul_inv_eq_sub K₁₁ K₁₂ (-K₂₂⁻¹) K₂₁ h₁ hC hSne
  have e1 : K₁₁ + K₁₂ * -K₂₂⁻¹ * K₂₁ = K₁₁ - K₁₂ * K₂₂⁻¹ * K₂₁ := by
    rw [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]
  rw [e1, hCinv] at h
  rw [h]
  have e2 : -K₂₂ + K₂₁ * K₁₁⁻¹ * K₁₂ = -(K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂) := by
    abel
  have hdS := (Matrix.isUnit_iff_isUnit_det _).1 hS
  have e3 : (-(K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂))⁻¹ = -(K₂₂ - K₂₁ * K₁₁⁻¹ * K₁₂)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hdS]
  rw [e2, e3]
  simp only [Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]

end Inversion

/-! ### The additive noise example -/

section Noise

variable {n : ℕ}

/-- **The example of Appendix B:** `(N I + P 1 1ᵀ)⁻¹ = (1 / N) I - P / (N (n P + N)) 1 1ᵀ`. -/
theorem covMatrix_noise_inv {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    (Matrix.of fun i j : Fin n => (if i = j then N else 0) + P)⁻¹ =
      Matrix.of fun i j : Fin n => (if i = j then 1 / N else 0) - P / (N * (n * P + N)) := by
  have hD : (n : ℝ) * P + N ≠ 0 := by positivity
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  set c := P / (N * (n * P + N)) with hc
  have hrow : ∀ k, ((if i = k then N else 0) + P) * ((if k = j then 1 / N else 0) - c) =
      (if i = k then (if k = j then (1 : ℝ) else 0) else 0) - (if i = k then c * N else 0) +
        (if k = j then P / N else 0) - P * c := by
    intro k
    by_cases h2 : k = j
    · subst h2
      by_cases h1 : i = k
      · simp only [h1, ite_true]
        field_simp
        ring
      · simp only [h1, ite_true, ite_false]
        ring
    · by_cases h1 : i = k
      · simp only [h1, h2, ite_true, ite_false]
        ring
      · simp only [h1, h2, ite_false]
        ring
  simp only [hrow, sum_sub_distrib, sum_add_distrib, sum_ite_eq, sum_ite_eq', mem_univ, ite_true,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hzero : c * N - P / N + n * (P * c) = 0 := by
    rw [hc]
    field_simp
    ring
  linarith

variable {X : Ω → ℝ} {Z : Fin n → Ω → ℝ}

/-- **The example of Appendix B.** For a signal `X` with mean `m` and variance `P`, observed as
`Yᵢ = X + Zᵢ` with zero mean noise of variance `N` uncorrelated with each other and with `X`, the
linear MMSE estimate has coefficients `P / (n P + N)` and offset `N m / (n P + N)`, and its mean
squared error is `P N / (n P + N)`. -/
theorem linMSE_noise {P N m : ℝ} (hP : 0 ≤ P) (hN : 0 < N) (hX : MemLp X 2 μ)
    (hZ : ∀ i, MemLp (Z i) 2 μ) (hmX : μ[X] = m) (hvX : Var[X; μ] = P) (hmZ : ∀ i, μ[Z i] = 0)
    (hvZ : ∀ i, Var[Z i; μ] = N) (hXZ : ∀ i, cov[X, Z i; μ] = 0)
    (hZZ : ∀ i j, i ≠ j → cov[Z i, Z j; μ] = 0) :
    (∀ a' b', linMSE μ X (fun i ω => X ω + Z i ω) (fun _ => P / (n * P + N)) (N * m / (n * P + N)) ≤
      linMSE μ X (fun i ω => X ω + Z i ω) a' b') ∧
    linMSE μ X (fun i ω => X ω + Z i ω) (fun _ => P / (n * P + N)) (N * m / (n * P + N)) =
      P * N / (n * P + N) := by
  have hD : (n : ℝ) * P + N ≠ 0 := by positivity
  set Y : Fin n → Ω → ℝ := fun i ω => X ω + Z i ω with hY
  have hYL : ∀ i, MemLp (Y i) 2 μ := fun i => hX.add (hZ i)
  have hmY : ∀ i, μ[Y i] = m := fun i => by
    simp only [hY]
    rw [integral_add (hX.integrable one_le_two) ((hZ i).integrable one_le_two), hmX, hmZ, add_zero]
  have hcXX : cov[X, X; μ] = P := by
    rw [covariance_self hX.aestronglyMeasurable.aemeasurable, hvX]
  have hcZX : ∀ i, cov[Z i, X; μ] = 0 := fun i => by rw [covariance_comm, hXZ]
  have hcovX : ∀ i, covVec μ X Y i = P := fun i => by
    simp only [covVec, hY]
    have := covariance_add_right hX (Y := X) (Z := Z i) hX (hZ i)
    simp only [Pi.add_def] at this
    rw [this, hcXX, hXZ, add_zero]
  have hcovY : ∀ i j, covMatrix μ Y i j = (if i = j then N else 0) + P := fun i j => by
    simp only [covMatrix, Matrix.of_apply, hY]
    have h1 := covariance_add_left (μ := μ) hX (hZ i) ((hX.add (hZ j)))
    have h2 := covariance_add_right (μ := μ) hX hX (hZ j)
    have h3 := covariance_add_right (μ := μ) (hZ i) hX (hZ j)
    simp only [Pi.add_def] at h1 h2 h3
    rw [h1, h2, h3, hcXX, hXZ, hcZX]
    by_cases h : i = j
    · subst h
      rw [covariance_self (hZ i).aestronglyMeasurable.aemeasurable, hvZ]
      simp
      ring
    · rw [hZZ i j h]
      simp [h]
  have hne : ∀ i, ∑ j, (fun _ => P / (n * P + N)) j * covMatrix μ Y j i = covVec μ X Y i := by
    intro i
    simp only [hcovY, hcovX]
    rw [← mul_sum, sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ i)]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hb : N * m / (n * P + N) = μ[X] - ∑ i, (fun _ => P / (n * P + N)) i * μ[Y i] := by
    simp only [hmY, hmX, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  refine ⟨linMSE_le_of_orthogonal hX hYL ((cov_linErr_eq_zero_iff hX hYL _).2 hne) hb, ?_⟩
  rw [linMSE_eq hX hYL, ← hb, hvX, sub_self]
  simp only [hcovX, hcovY, mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq, mem_univ,
    ite_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end Noise

end InfoTheory
