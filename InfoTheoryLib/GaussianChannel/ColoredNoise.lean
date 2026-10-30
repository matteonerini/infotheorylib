/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.MatrixDet
public import InfoTheoryLib.GaussianChannel.Parallel

/-!
# Gaussian channels with colored noise

The channel `Yⁿ = Xⁿ + Zⁿ` with dependent normal noise `Zⁿ ∼ N(0, K_Z)` and power constraint
`∑ᵢ E Xᵢ² ≤ nP`. Diagonalizing `K_Z = Q Λ Qᵀ` turns it into parallel channels with noise variances
the eigenvalues `λᵢ` of `K_Z`, so the capacity is given by water-filling on the eigenvalues. In
matrix form, the capacity is `C_n = max_{tr K_X ≤ nP} (1/2n) log (|K_X + K_Z|/|K_Z|)`, and the
maximization is solved by Hadamard's inequality and water-filling.

## Main definitions

* `coloredInfoCapacity K P`: the information capacity of the channel with noise `N(0, K)`.
* `capacityNoFB K P`: the capacity `C_n` of (9.104), a maximum over input covariance matrices.

## Main statements

* `coloredInfoCapacity_eq_parallel`: rotating by the eigenvectors of `K_Z`, the channel is
  equivalent to parallel channels with noise variances `λᵢ`.
* `coloredInfoCapacity_eq`: water-filling on the eigenvalues of `K_Z`, (9.105).
* `det_add_le_prod_max`: (9.83)–(9.96), `|K_X + K_Z| ≤ ∏ᵢ max(ν, λᵢ)` if `tr K_X ≤ ∑ᵢ (ν - λᵢ)⁺`.
* `det_waterFill_add`: equality for `K_X = Q diag((ν - λᵢ)⁺) Qᵀ`.
* `isGreatest_capacityNoFB`, `capacityNoFB_eq`: (9.104)–(9.106), the maximum defining `C_n` is
  attained by water-filling, `C_n = (1/2n) ∑ᵢ log (1 + (ν - λᵢ)⁺/λᵢ)`.

## Implementation notes

The book computes `I(Xⁿ; Yⁿ) = h(Yⁿ) - h(Zⁿ)` and maximizes `|K_X + K_Z|`, (9.81)–(9.96). For the
information capacity we rotate instead: `x ↦ Q x` preserves the Lebesgue measure, the mutual
information (`mutualInfoPDF_comp_prodMap`) and the total power, and turns `N(0, K_Z)` into
independent `N(0, λᵢ)` noises, so the results of Section 9.4 apply. The matrix argument
(9.83)–(9.96) is formalized for `C_n`. The power constraint is `∑ᵢ E Xᵢ² ≤ P` for the
information capacity, `P` being the total power, and `tr K_X ≤ nP` for `C_n`, as in (9.80).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.5
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The information capacity -/

lemma IsPDF.comp_measurePreserving {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : IsPDF μ f) (e : α ≃ᵐ α) (he : MeasurePreserving e μ μ) :
    IsPDF μ (f ∘ e) :=
  ⟨hf.measurable.comp e.measurable, fun _ => hf.nonneg _,
    he.integrable_comp_of_integrable hf.integrable,
    by rw [← hf.integral_eq_one]; exact he.integral_comp' f⟩

omit [DecidableEq ι] in
/-- A measure-preserving change of variables preserving `∑ᵢ xᵢ²` preserves the total power. -/
lemma power_comp_measurePreserving (T : (ι → ℝ) ≃ᵐ (ι → ℝ))
    (hT : MeasurePreserving T volume volume) (hnorm : ∀ x, ∑ i, (T x) i ^ 2 = ∑ i, x i ^ 2)
    {f : (ι → ℝ) → ℝ} (hf : IsPDF volume f) (h2 : ∀ i, Integrable fun x => f x * x i ^ 2) :
    (∀ i, Integrable fun x => f (T x) * x i ^ 2) ∧
      ∑ i, ∫ x, f (T x) * x i ^ 2 = ∑ i, ∫ x, f x * x i ^ 2 := by
  set F : (ι → ℝ) → ℝ := fun x => f x * ∑ j, x j ^ 2
  have hF : Integrable F := by
    simp only [F, mul_sum]
    exact integrable_finsetSum _ fun j _ => h2 j
  have hFT : Integrable fun x => F (T x) := hT.integrable_comp_of_integrable hF
  have e : ∀ x, F (T x) = f (T x) * ∑ j, x j ^ 2 := fun x => by simp only [F, hnorm]
  have hint : ∀ i, Integrable fun x => f (T x) * x i ^ 2 := by
    intro i
    refine hFT.mono' ((hf.measurable.comp T.measurable).mul
      ((measurable_pi_apply i).pow_const 2)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hf.nonneg _) (sq_nonneg _)), e]
    exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => sq_nonneg (x j)) (mem_univ i))
      (hf.nonneg _)
  refine ⟨hint, ?_⟩
  rw [← integral_finsetSum _ fun i _ => hint i, ← integral_finsetSum _ fun i _ => h2 i]
  simp_rw [← mul_sum]
  have h := hT.integral_comp' F
  simp only [e] at h
  exact h

/-- **Definition (Section 9.5).** The information capacity of the Gaussian channel with colored
noise `Zⁿ ∼ N(0, K)` and total power constraint `∑ᵢ E Xᵢ² ≤ P`. -/
def coloredInfoCapacity (K : Matrix ι ι ℝ) (P : ℝ) : ℝ :=
  sSup {I | ∃ f : (ι → ℝ) → ℝ, IsPDF volume f ∧ (∀ i, Integrable fun x => f x * x i ^ 2) ∧
    ∑ i, ∫ x, f x * x i ^ 2 ≤ P ∧
      mutualInfoPDF volume volume (noiseJointPDF f (mvGaussianPDF 0 K)) = I}

variable {K : Matrix ι ι ℝ}

/-- In the eigenbasis of `K`, the noise `N(0, K)` has independent coordinates `N(0, λᵢ)`. -/
lemma noiseJointPDF_eigEquiv (hK : K.PosDef) (f : (ι → ℝ) → ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    noiseJointPDF f (mvGaussianPDF 0 K) (PosDef.eigEquiv hK 0 z.1, PosDef.eigEquiv hK 0 z.2) =
      noiseJointPDF (f ∘ PosDef.eigEquiv hK 0) (diagNoisePDF (PosDef.eigvalNN hK)) z := by
  simp only [noiseJointPDF, Function.comp_apply]
  congr 1
  rw [PosDef.eigEquiv_apply, PosDef.eigEquiv_apply, zero_add, zero_add, ← mulVec_sub,
    ← zero_add (PosDef.eigU hK *ᵥ (z.2 - z.1)), mvGaussianPDF_eigU hK 0 (z.2 - z.1)]
  rfl

lemma sum_sq_eigEquiv (hK : K.PosDef) (x : ι → ℝ) :
    ∑ i, (PosDef.eigEquiv hK 0 x) i ^ 2 = ∑ i, x i ^ 2 := by
  have h := PosDef.dotProduct_eigU hK x x
  simp only [dotProduct] at h
  rw [PosDef.eigEquiv_apply, zero_add]
  simpa [sq] using h

/-- **Section 9.5.** Rotating by the eigenvectors of `K_Z`, the channel with colored noise
`N(0, K_Z)` is equivalent to parallel channels with independent noises `N(0, λᵢ)`: the two
information capacities agree. -/
theorem coloredInfoCapacity_eq_parallel (hK : K.PosDef) (P : ℝ) :
    coloredInfoCapacity K P = parallelInfoCapacity (PosDef.eigvalNN hK) P := by
  set T := PosDef.eigEquiv hK 0
  have hT : MeasurePreserving T volume volume := PosDef.measurePreserving_eigEquiv hK 0
  have hTs : MeasurePreserving T.symm volume volume := MeasurePreserving.symm T hT
  have hnorm : ∀ x, ∑ i, (T x) i ^ 2 = ∑ i, x i ^ 2 := sum_sq_eigEquiv hK
  have hnorm' : ∀ x, ∑ i, (T.symm x) i ^ 2 = ∑ i, x i ^ 2 := fun x => by
    rw [← hnorm (T.symm x), MeasurableEquiv.apply_symm_apply]
  have hI : ∀ f : (ι → ℝ) → ℝ,
      mutualInfoPDF volume volume (noiseJointPDF f (mvGaussianPDF 0 K)) =
        mutualInfoPDF volume volume
          (noiseJointPDF (f ∘ T) (diagNoisePDF (PosDef.eigvalNN hK))) := fun f => by
    rw [← mutualInfoPDF_comp_prodMap T T hT hT]
    exact congrArg _ (funext fun z => noiseJointPDF_eigEquiv hK f z)
  rw [coloredInfoCapacity, parallelInfoCapacity]
  congr 1
  ext I
  constructor
  · rintro ⟨f, hf, h2, hP, rfl⟩
    obtain ⟨h2', hsum⟩ := power_comp_measurePreserving T hT hnorm hf h2
    exact ⟨f ∘ T, hf.comp_measurePreserving T hT, h2', hsum.trans_le hP, (hI f).symm⟩
  · rintro ⟨f', hf', h2', hP', rfl⟩
    set f := f' ∘ T.symm
    have hfT : f ∘ T = f' := funext fun x => by simp [f]
    obtain ⟨h2, hsum⟩ := power_comp_measurePreserving T.symm hTs hnorm' hf' h2'
    refine ⟨f, hf'.comp_measurePreserving T.symm hTs, h2, hsum.trans_le hP', ?_⟩
    rw [hI f, hfT]

/-- **(9.105)** The information capacity of the Gaussian channel with colored noise `N(0, K_Z)` is
given by water-filling on the eigenvalues `λᵢ` of `K_Z`: `C = ∑ᵢ ½ log (1 + (ν - λᵢ)⁺/λᵢ)`, where
`∑ᵢ (ν - λᵢ)⁺ = P`. -/
theorem coloredInfoCapacity_eq (hK : K.PosDef) {P ν : ℝ} (hν : 0 < ν)
    (hνP : ∑ i, waterFill (PosDef.eigval hK) ν i = P) :
    coloredInfoCapacity K P =
      ∑ i, 1 / 2 * log (1 + waterFill (PosDef.eigval hK) ν i / PosDef.eigval hK i) := by
  rw [coloredInfoCapacity_eq_parallel hK]
  exact parallelInfoCapacity_eq (fun i => PosDef.eigvalNN_ne_zero hK i) hν hνP

/-! ### Maximizing `|K_X + K_Z|` -/

lemma det_transpose_mul_mul_eigU (hK : K.PosDef) (M : Matrix ι ι ℝ) :
    ((PosDef.eigU hK)ᵀ * M * PosDef.eigU hK).det = M.det := by
  have hU : (PosDef.eigU hK).det ^ 2 = 1 := by
    have := congrArg det (PosDef.eigU_mul_transpose hK)
    rwa [det_mul, det_transpose, det_one, ← sq] at this
  rw [det_mul, det_mul, det_transpose]
  linear_combination M.det * hU

lemma transpose_mul_mul_eigU_self (hK : K.PosDef) :
    (PosDef.eigU hK)ᵀ * K * PosDef.eigU hK = diagonal (PosDef.eigval hK) := by
  have h : (PosDef.eigU hK)ᵀ * K * PosDef.eigU hK = (PosDef.eigU hK)ᵀ *
      (PosDef.eigU hK * diagonal (PosDef.eigval hK) * (PosDef.eigU hK)ᵀ) * PosDef.eigU hK :=
    congrArg (fun M => (PosDef.eigU hK)ᵀ * M * PosDef.eigU hK) (PosDef.eq_eigU hK)
  rw [h]
  simp only [Matrix.mul_assoc, PosDef.eigU_transpose_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, PosDef.eigU_transpose_mul, Matrix.one_mul]

omit [DecidableEq ι] in
/-- `∏ᵢ (aᵢ + λᵢ) ≤ ∏ᵢ max(ν, λᵢ)` for `aᵢ ≥ 0` with `∑ᵢ aᵢ ≤ ∑ᵢ (ν - λᵢ)⁺`: water-filling. -/
lemma prod_add_le_prod_max {lam a : ι → ℝ} (hlam : ∀ i, 0 < lam i) (ha : ∀ i, 0 ≤ a i) {ν : ℝ}
    (hν : 0 < ν) (hsum : ∑ i, a i ≤ ∑ i, waterFill lam ν i) :
    ∏ i, (a i + lam i) ≤ ∏ i, max ν (lam i) := by
  have hpos1 : ∀ i, 0 < a i + lam i := fun i => by linarith [ha i, hlam i]
  have hpos2 : ∀ i, 0 < max ν (lam i) := fun i => lt_max_of_lt_left hν
  rw [← log_le_log_iff (prod_pos fun i _ => hpos1 i) (prod_pos fun i _ => hpos2 i),
    log_prod fun i _ => (hpos1 i).ne', log_prod fun i _ => (hpos2 i).ne']
  have e1 : ∀ i, log (a i + lam i) = log (lam i) + log (1 + a i / lam i) := fun i => by
    have hl := (hlam i).ne'
    rw [← log_mul hl (by linarith [div_nonneg (ha i) (hlam i).le])]
    congr 1
    field_simp
    ring
  have e2 : ∀ i, log (max ν (lam i)) = log (lam i) + log (1 + waterFill lam ν i / lam i) :=
    fun i => by
      have hl := (hlam i).ne'
      rw [← add_waterFill lam ν i, ← log_mul hl
        (by linarith [div_nonneg (waterFill_nonneg lam ν i) (hlam i).le])]
      congr 1
      field_simp
  simp only [e1, e2, sum_add_distrib]
  linarith [sum_log_le_waterFill hlam hν ha hsum]

/-- **(9.83)–(9.96)** For `K_Z` positive definite with eigenvalues `λᵢ` and `K_X` positive
semidefinite with `tr K_X ≤ ∑ᵢ (ν - λᵢ)⁺`, `|K_X + K_Z| ≤ ∏ᵢ max(ν, λᵢ)`. Writing
`K_Z = Q Λ Qᵀ` and `A = Qᵀ K_X Q`, `|K_X + K_Z| = |A + Λ| ≤ ∏ᵢ (Aᵢᵢ + λᵢ)` by Hadamard's
inequality, with `∑ᵢ Aᵢᵢ = tr K_X`, and water-filling maximizes the product. -/
theorem det_add_le_prod_max {KX : Matrix ι ι ℝ} (hX : KX.PosSemidef) (hK : K.PosDef) {ν : ℝ}
    (hν : 0 < ν) (htr : KX.trace ≤ ∑ i, waterFill (PosDef.eigval hK) ν i) :
    (KX + K).det ≤ ∏ i, max ν (PosDef.eigval hK i) := by
  set U := PosDef.eigU hK
  set A := Uᵀ * KX * U
  have hA : A.PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hX.conjTranspose_mul_mul_same U
  have hC : Uᵀ * (KX + K) * U = A + diagonal (PosDef.eigval hK) := by
    rw [Matrix.mul_add, Matrix.add_mul, transpose_mul_mul_eigU_self hK]
  have hCpd : (A + diagonal (PosDef.eigval hK)).PosDef :=
    Matrix.PosDef.posSemidef_add hA (PosDef.diagonal fun i => PosDef.eigval_pos hK i)
  have htrA : A.trace = KX.trace := by
    simp only [A]
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, PosDef.eigU_mul_transpose hK,
      Matrix.mul_one]
  rw [← det_transpose_mul_mul_eigU hK, hC]
  refine (det_le_prod_diag hCpd).trans ?_
  have hdiag : ∀ i, (A + diagonal (PosDef.eigval hK)) i i = A i i + PosDef.eigval hK i := by
    intro i
    simp
  simp only [hdiag]
  refine prod_add_le_prod_max (PosDef.eigval_pos hK) (fun i => hA.diag_nonneg) hν ?_
  rw [← htrA] at htr
  exact htr

/-- **(9.96)** The bound is attained by `K_X = Q diag((ν - λᵢ)⁺) Qᵀ`. -/
theorem det_waterFill_add (hK : K.PosDef) (ν : ℝ) :
    (PosDef.eigU hK * diagonal (waterFill (PosDef.eigval hK) ν) * (PosDef.eigU hK)ᵀ).PosSemidef ∧
      (PosDef.eigU hK * diagonal (waterFill (PosDef.eigval hK) ν) * (PosDef.eigU hK)ᵀ).trace =
        ∑ i, waterFill (PosDef.eigval hK) ν i ∧
      (PosDef.eigU hK * diagonal (waterFill (PosDef.eigval hK) ν) * (PosDef.eigU hK)ᵀ + K).det =
        ∏ i, max ν (PosDef.eigval hK i) := by
  set U := PosDef.eigU hK
  set w := waterFill (PosDef.eigval hK) ν
  refine ⟨?_, ?_, ?_⟩
  · simpa [conjTranspose_eq_transpose_of_trivial] using
      (PosSemidef.diagonal fun i => waterFill_nonneg (PosDef.eigval hK) ν i
        ).mul_mul_conjTranspose_same U
  · rw [trace_mul_comm, ← Matrix.mul_assoc, PosDef.eigU_transpose_mul hK, Matrix.one_mul,
      trace_diagonal]
  · have h : U * diagonal w * Uᵀ + K =
        U * diagonal (fun i => w i + PosDef.eigval hK i) * Uᵀ := by
      have h0 : U * diagonal w * Uᵀ + K =
          U * diagonal w * Uᵀ + U * diagonal (PosDef.eigval hK) * Uᵀ :=
        congrArg (fun M => U * diagonal w * Uᵀ + M) (PosDef.eq_eigU hK)
      rw [h0, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    rw [h, ← det_transpose_mul_mul_eigU hK]
    have e : Uᵀ * (U * diagonal (fun i => w i + PosDef.eigval hK i) * Uᵀ) * U =
        diagonal (fun i => w i + PosDef.eigval hK i) := by
      simp only [Matrix.mul_assoc]
      rw [PosDef.eigU_transpose_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        PosDef.eigU_transpose_mul, Matrix.one_mul]
    rw [e, det_diagonal]
    refine prod_congr rfl fun i _ => ?_
    rw [add_comm]
    exact add_waterFill _ ν i

/-! ### The capacity `C_n` -/

/-- **(9.104)** The capacity without feedback of `n` uses of the Gaussian channel with colored noise
`N(0, K_Z)` and power constraint `P`: `C_n = max_{tr K_X ≤ nP} (1/2n) log (|K_X + K_Z|/|K_Z|)`,
in nats per transmission. -/
def capacityNoFB {n : ℕ} (KZ : Matrix (Fin n) (Fin n) ℝ) (P : ℝ) : ℝ :=
  sSup ((fun KX => 1 / (2 * n) * log ((KX + KZ).det / KZ.det)) ''
    {KX | KX.PosSemidef ∧ KX.trace ≤ n * P})

/-- **(9.83)–(9.96), (9.105)** The maximum defining `C_n` is attained by water-filling on the
eigenvalues of `K_Z`, where `∑ᵢ (ν - λᵢ)⁺ = nP`. -/
theorem isGreatest_capacityNoFB {n : ℕ} {KZ : Matrix (Fin n) (Fin n) ℝ} (hK : KZ.PosDef)
    {P ν : ℝ} (hν : 0 < ν) (hνP : ∑ i, waterFill (PosDef.eigval hK) ν i = n * P) :
    IsGreatest ((fun KX => 1 / (2 * n) * log ((KX + KZ).det / KZ.det)) ''
        {KX | KX.PosSemidef ∧ KX.trace ≤ n * P})
      (1 / (2 * n) * ∑ i, log (1 + waterFill (PosDef.eigval hK) ν i / PosDef.eigval hK i)) := by
  set lam := PosDef.eigval hK
  set w := waterFill lam ν
  have hlam : ∀ i, 0 < lam i := PosDef.eigval_pos hK
  have hdetK : KZ.det = ∏ i, lam i := PosDef.det_eq_prod_eigval hK
  have hdetpos : 0 < KZ.det := hK.det_pos
  have hval : log ((∏ i, max ν (lam i)) / KZ.det) = ∑ i, log (1 + w i / lam i) := by
    rw [hdetK, ← prod_div_distrib, log_prod fun i _ =>
      (div_pos (lt_max_of_lt_left hν) (hlam i)).ne']
    refine sum_congr rfl fun i _ => ?_
    rw [← add_waterFill lam ν i]
    congr 1
    have hl := (hlam i).ne'
    field_simp
    rfl
  obtain ⟨hXpsd, htr, hdet⟩ := det_waterFill_add hK ν
  refine ⟨⟨_, ⟨hXpsd, htr.trans_le hνP.le⟩, ?_⟩, ?_⟩
  · simp only
    rw [hdet, hval]
  · rintro _ ⟨KX, ⟨hX, hXtr⟩, rfl⟩
    have hle := det_add_le_prod_max hX hK hν (hXtr.trans hνP.ge)
    have hpos : 0 < (KX + KZ).det := (Matrix.PosDef.posSemidef_add hX hK).det_pos
    simp only
    rw [← hval]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact log_le_log (div_pos hpos hdetpos) (div_le_div_of_nonneg_right hle hdetpos.le)

/-- **(9.105)–(9.106)** `C_n = (1/2n) ∑ᵢ log (1 + (ν - λᵢ)⁺/λᵢ)` with `∑ᵢ (ν - λᵢ)⁺ = nP`:
water-filling on the eigenvalues of `K_Z`. -/
theorem capacityNoFB_eq {n : ℕ} {KZ : Matrix (Fin n) (Fin n) ℝ} (hK : KZ.PosDef) {P ν : ℝ}
    (hν : 0 < ν) (hνP : ∑ i, waterFill (PosDef.eigval hK) ν i = n * P) :
    capacityNoFB KZ P =
      1 / (2 * n) * ∑ i, log (1 + waterFill (PosDef.eigval hK) ν i / PosDef.eigval hK i) :=
  (isGreatest_capacityNoFB hK hν hνP).csSup_eq

/-- Every input covariance matrix satisfying the power constraint gives at most `C_n`. -/
theorem le_capacityNoFB {n : ℕ} (hn : 0 < n) {KZ : Matrix (Fin n) (Fin n) ℝ} (hK : KZ.PosDef)
    {P : ℝ} (hP : 0 ≤ P) {KX : Matrix (Fin n) (Fin n) ℝ} (hX : KX.PosSemidef)
    (htr : KX.trace ≤ n * P) :
    1 / (2 * n) * log ((KX + KZ).det / KZ.det) ≤ capacityNoFB KZ P := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ν, -, ⟨i, hi⟩, hνP⟩ := exists_waterLevel (PosDef.eigval hK)
    (by positivity : (0 : ℝ) ≤ n * P)
  have hν : 0 < ν := (PosDef.eigval_pos hK i).trans_le hi
  exact le_csSup (isGreatest_capacityNoFB hK hν hνP).bddAbove ⟨KX, ⟨hX, htr⟩, rfl⟩

end InfoTheory
