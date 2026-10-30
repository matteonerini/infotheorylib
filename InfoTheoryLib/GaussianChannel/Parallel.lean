/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Converse
public import InfoTheoryLib.GaussianChannel.WaterFilling

/-!
# Parallel Gaussian channels

`k` independent Gaussian channels `Yⱼ = Xⱼ + Zⱼ`, `Zⱼ ∼ N(0, Nⱼ)`, used with a common power
constraint `∑ⱼ E Xⱼ² ≤ P`. The mutual information is at most `∑ⱼ ½ log (1 + Pⱼ/Nⱼ)` with
`Pⱼ = E Xⱼ²`, with equality for independent normal inputs `Xⱼ ∼ N(0, Pⱼ)`; the best allocation of
the power is water-filling. The information capacity is
`C = ∑ⱼ ½ log (1 + (ν - Nⱼ)⁺/Nⱼ)` with `∑ⱼ (ν - Nⱼ)⁺ = P`.

## Main definitions

* `diagNoisePDF N`: the density `∏ⱼ φ_{Nⱼ}(zⱼ)` of independent noises `Zⱼ ∼ N(0, Nⱼ)`.
* `parallelInfoCapacity N P`: the information capacity (9.67).

## Main statements

* `mutualInfoPDF_parallel_le`: (9.68)–(9.71), `I(Xᵏ; Yᵏ) ≤ ∑ⱼ ½ log (1 + E Xⱼ²/Nⱼ)`.
* `mutualInfoPDF_parallel_le_waterFill`: with the power constraint, the water-filling bound.
* `mutualInfoPDF_parallel_gaussian`: (9.72), equality for `X ∼ N(0, diag(P₁, …, P_k))`.
* `parallelInfoCapacity_eq`: (9.165), the information capacity is given by water-filling.

## Implementation notes

As for a single channel, `I(Xᵏ; Yᵏ)` is bounded by comparing the conditional density of the
output with the normal density `∏ⱼ φ_{E Xⱼ² + Nⱼ}`. The water-filling allocation may leave some
channels unused, and a normal input with a zero variance has no density; the information capacity
is then approached by normal inputs with positive variances.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.4
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι]

/-- The density `∏ⱼ φ_{Nⱼ}(zⱼ)` of independent noises `Zⱼ ∼ N(0, Nⱼ)`, (9.65). -/
def diagNoisePDF (N : ι → ℝ≥0) (z : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 (N i) (z i)

variable {N : ι → ℝ≥0}

lemma diagNoisePDF_isPDF (hN : ∀ i, N i ≠ 0) : IsPDF volume (diagNoisePDF N) :=
  isPDF_prod_apply fun i => gaussianPDFReal_isPDF 0 (hN i)

lemma diagNoisePDF_pos (hN : ∀ i, N i ≠ 0) (z : ι → ℝ) : 0 < diagNoisePDF N z :=
  prod_pos fun i _ => gaussianPDFReal_pos _ _ _ (hN i)

lemma log_diagNoisePDF_sub_div {S : ι → ℝ≥0} (hN : ∀ i, N i ≠ 0) (hS : ∀ i, S i ≠ 0)
    (x y : ι → ℝ) :
    log (diagNoisePDF N (y - x) / diagNoisePDF S y) =
      ∑ i, (log (S i / N i) / 2 - (y i - x i) ^ 2 / (2 * N i) + y i ^ 2 / (2 * S i)) := by
  simp only [diagNoisePDF, Pi.sub_apply, ← prod_div_distrib]
  rw [log_prod fun i _ => (div_pos (gaussianPDFReal_pos _ _ _ (hN i))
    (gaussianPDFReal_pos _ _ _ (hS i))).ne']
  exact sum_congr rfl fun i _ => log_gaussianPDFReal_sub_div (hN i) (hS i) (x i) (y i)

/-- The second moments of the output given the input `xᵏ`:
`∫ g(y - x) (yᵢ - xᵢ)² dy = Nᵢ` and `∫ g(y - x) yᵢ² dy = xᵢ² + Nᵢ`. -/
lemma diagNoisePDF_sub_moments (hN : ∀ i, N i ≠ 0) (x : ι → ℝ) (i : ι) :
    Integrable (fun y => diagNoisePDF N (y - x) * (y i - x i) ^ 2) ∧
      ∫ y, diagNoisePDF N (y - x) * (y i - x i) ^ 2 = N i ∧
      Integrable (fun y => diagNoisePDF N (y - x) * y i ^ 2) ∧
      ∫ y, diagNoisePDF N (y - x) * y i ^ 2 = x i ^ 2 + N i := by
  have hg := fun j => (gaussianPDFReal_sub_moments (hN j) (x j)).1
  have hg1 := fun j => (gaussianPDFReal_sub_moments (hN j) (x j)).2.1
  obtain ⟨-, -, i1, e1, i2, e2⟩ := gaussianPDFReal_sub_moments (hN i) (x i)
  obtain ⟨j1, f1⟩ := integral_prod_mul_apply (g := fun j t => gaussianPDFReal 0 (N j) (t - x j))
    hg hg1 i (ℓ := fun t => (t - x i) ^ 2) i1
  obtain ⟨j2, f2⟩ := integral_prod_mul_apply (g := fun j t => gaussianPDFReal 0 (N j) (t - x j))
    hg hg1 i (ℓ := fun t => t ^ 2) i2
  exact ⟨j1, f1.trans e1, j2, f2.trans e2⟩

/-- The second moments of independent normal coordinates: `∫ ∏ⱼ φ_{Pⱼ}(xⱼ) xᵢ² dx = Pᵢ`. -/
lemma diagNoisePDF_moments {P : ι → ℝ≥0} (hP : ∀ i, P i ≠ 0) (i : ι) :
    Integrable (fun x => diagNoisePDF P x * x i ^ 2) ∧ ∫ x, diagNoisePDF P x * x i ^ 2 = P i := by
  obtain ⟨h1, h2⟩ := integral_prod_mul_apply (g := fun j t => gaussianPDFReal 0 (P j) t)
    (fun j => integrable_gaussianPDFReal 0 (P j))
    (fun j => integral_gaussianPDFReal_eq_one 0 (hP j)) i (ℓ := fun t => t ^ 2)
    (integrable_gaussianPDFReal_mul_sq_zero (hP i))
  exact ⟨h1, h2.trans (integral_gaussianPDFReal_mul_sq_zero (hP i))⟩

section Bound

variable {μ : Measure (ι → ℝ)} [SigmaFinite μ] {f : (ι → ℝ) → ℝ}

/-- The integral `∫ f(x) g(y - x) log (g(y - x)/q(y))` for independent normal noises `g` and the
independent normal output density `q = ∏ⱼ φ_{Sⱼ}`. -/
lemma integral_noiseJointPDF_diag_mul_log_div (hf : IsPDF μ f) {S : ι → ℝ≥0}
    (hN : ∀ i, N i ≠ 0) (hS : ∀ i, S i ≠ 0) (h2 : ∀ i, Integrable (fun x => f x * x i ^ 2) μ) :
    Integrable (fun z => noiseJointPDF f (diagNoisePDF N) z *
        log (diagNoisePDF N (z.2 - z.1) / diagNoisePDF S z.2)) (μ.prod volume) ∧
      ∫ z, noiseJointPDF f (diagNoisePDF N) z *
          log (diagNoisePDF N (z.2 - z.1) / diagNoisePDF S z.2) ∂(μ.prod volume) =
        ∑ i, (log (S i / N i) / 2 - 1 / 2 + ((∫ x, f x * x i ^ 2 ∂μ) + N i) / (2 * S i)) := by
  set J := noiseJointPDF f (diagNoisePDF N)
  have hg := diagNoisePDF_isPDF hN
  have hJ := noiseJointPDF_isPDF (μ := μ) hf hg
  have hA : ∀ i, Integrable (fun z => J z * (z.2 i - z.1 i) ^ 2) (μ.prod volume) ∧
      ∫ z, J z * (z.2 i - z.1 i) ^ 2 ∂(μ.prod volume) = ∫ x, f x * (N i : ℝ) ∂μ := fun i =>
    integral_noiseJointPDF_mul hf hg.measurable hg.nonneg (h := fun z => (z.2 i - z.1 i) ^ 2)
      (by fun_prop) (fun z => sq_nonneg _) (k := fun _ => (N i : ℝ))
      (fun x => ⟨(diagNoisePDF_sub_moments hN x i).1, (diagNoisePDF_sub_moments hN x i).2.1⟩)
      (hf.integrable.mul_const _)
  have hfN : ∀ i, Integrable (fun x => f x * (N i : ℝ)) μ := fun i => hf.integrable.mul_const _
  have hB : ∀ i, Integrable (fun z => J z * z.2 i ^ 2) (μ.prod volume) ∧
      ∫ z, J z * z.2 i ^ 2 ∂(μ.prod volume) = ∫ x, f x * (x i ^ 2 + N i) ∂μ := fun i =>
    integral_noiseJointPDF_mul hf hg.measurable hg.nonneg (h := fun z => z.2 i ^ 2)
      (by fun_prop) (fun z => sq_nonneg _) (k := fun x => x i ^ 2 + N i)
      (fun x => ⟨(diagNoisePDF_sub_moments hN x i).2.2.1,
        (diagNoisePDF_sub_moments hN x i).2.2.2⟩)
      (((h2 i).add (hfN i)).congr (Eventually.of_forall fun x => by
        simp only [Pi.add_apply]; ring))
  set T : ι → (ι → ℝ) × (ι → ℝ) → ℝ := fun i z => log (S i / N i) / 2 * J z -
    (2 * (N i : ℝ))⁻¹ * (J z * (z.2 i - z.1 i) ^ 2) + (2 * (S i : ℝ))⁻¹ * (J z * z.2 i ^ 2)
  have hT : ∀ i, Integrable (T i) (μ.prod volume) := fun i =>
    ((hJ.integrable.const_mul _).sub ((hA i).1.const_mul _)).add ((hB i).1.const_mul _)
  have e : (fun z => J z * log (diagNoisePDF N (z.2 - z.1) / diagNoisePDF S z.2)) =
      fun z => ∑ i, T i z := by
    funext z
    rw [log_diagNoisePDF_sub_div hN hS, mul_sum]
    exact sum_congr rfl fun i _ => by simp only [T]; ring
  have hTi : ∀ i, ∫ z, T i z ∂(μ.prod volume) =
      log (S i / N i) / 2 - 1 / 2 + ((∫ x, f x * x i ^ 2 ∂μ) + N i) / (2 * S i) := by
    intro i
    have hN' : (0 : ℝ) < N i := by have := hN i; positivity
    have hS' : (0 : ℝ) < S i := by have := hS i; positivity
    have hA' : Integrable (fun z => log (S i / N i) / 2 * J z -
        (2 * (N i : ℝ))⁻¹ * (J z * (z.2 i - z.1 i) ^ 2)) (μ.prod volume) :=
      (hJ.integrable.const_mul _).sub ((hA i).1.const_mul _)
    have hB' : Integrable (fun z => (2 * (S i : ℝ))⁻¹ * (J z * z.2 i ^ 2)) (μ.prod volume) :=
      (hB i).1.const_mul _
    have e2 : ∫ x, f x * (x i ^ 2 + N i) ∂μ = (∫ x, f x * x i ^ 2 ∂μ) + N i := by
      have : (fun x => f x * (x i ^ 2 + N i)) = fun x => f x * x i ^ 2 + f x * N i :=
        funext fun x => by ring
      rw [this, integral_add (h2 i) (hfN i), integral_mul_const, hf.integral_eq_one, one_mul]
    simp only [T]
    rw [integral_add hA' hB', integral_sub (hJ.integrable.const_mul _) ((hA i).1.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, hJ.integral_eq_one, (hA i).2,
      (hB i).2, integral_mul_const, hf.integral_eq_one, e2]
    field_simp
  rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => hT i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hT i]
  exact sum_congr rfl fun i _ => hTi i

omit [Fintype ι] [SigmaFinite μ] in
lemma integral_mul_sq_apply_nonneg (hf : IsPDF μ f) (i : ι) : 0 ≤ ∫ x, f x * x i ^ 2 ∂μ :=
  integral_nonneg fun x => mul_nonneg (hf.nonneg x) (sq_nonneg _)

/-- **(9.68)–(9.71)** For parallel Gaussian channels with independent noises `Zⱼ ∼ N(0, Nⱼ)`,
`I(Xᵏ; Yᵏ) ≤ ∑ⱼ ½ log (1 + E Xⱼ²/Nⱼ)`. -/
theorem mutualInfoPDF_parallel_le (hf : IsPDF μ f) (hN : ∀ i, N i ≠ 0)
    (h2 : ∀ i, Integrable (fun x => f x * x i ^ 2) μ) :
    mutualInfoPDF μ volume (noiseJointPDF f (diagNoisePDF N)) ≤
      ∑ i, 1 / 2 * log (1 + (∫ x, f x * x i ^ 2 ∂μ) / N i) := by
  set Pv : ι → ℝ := fun i => ∫ x, f x * x i ^ 2 ∂μ
  have hPv : ∀ i, 0 ≤ Pv i := integral_mul_sq_apply_nonneg hf
  set S : ι → ℝ≥0 := fun i => ⟨Pv i, hPv i⟩ + N i
  have hS' : ∀ i, (S i : ℝ) = Pv i + N i := fun i => rfl
  have hN' : ∀ i, (0 : ℝ) < N i := fun i => by have := hN i; positivity
  have hS : ∀ i, S i ≠ 0 := fun i h => by
    have := congrArg NNReal.toReal h
    rw [hS', NNReal.coe_zero] at this
    linarith [hPv i, hN' i]
  obtain ⟨hint, heq⟩ := integral_noiseJointPDF_diag_mul_log_div hf hN hS h2
  refine (mutualInfoPDF_noiseJointPDF_le hf (diagNoisePDF_isPDF hN) (diagNoisePDF_pos hN)
    (diagNoisePDF_isPDF hS) (diagNoisePDF_pos hS) hint).trans_eq ?_
  rw [heq]
  refine sum_congr rfl fun i _ => ?_
  have hPvi : (∫ x, f x * x i ^ 2 ∂μ) = Pv i := rfl
  have hpos : Pv i + N i ≠ 0 := by linarith [hPv i, hN' i]
  rw [hPvi, hS', show (Pv i + N i) / N i = 1 + Pv i / N i by
    rw [add_div, div_self (hN' i).ne', add_comm]]
  field_simp
  ring

/-- **(9.71) and water-filling.** If `∑ⱼ E Xⱼ² ≤ ∑ⱼ (ν - Nⱼ)⁺`, then
`I(Xᵏ; Yᵏ) ≤ ∑ⱼ ½ log (1 + (ν - Nⱼ)⁺/Nⱼ)`. -/
theorem mutualInfoPDF_parallel_le_waterFill (hf : IsPDF μ f) (hN : ∀ i, N i ≠ 0)
    (h2 : ∀ i, Integrable (fun x => f x * x i ^ 2) μ) {ν : ℝ} (hν : 0 < ν)
    (hP : ∑ i, ∫ x, f x * x i ^ 2 ∂μ ≤ ∑ i, waterFill (fun i => (N i : ℝ)) ν i) :
    mutualInfoPDF μ volume (noiseJointPDF f (diagNoisePDF N)) ≤
      ∑ i, 1 / 2 * log (1 + waterFill (fun i => (N i : ℝ)) ν i / N i) := by
  have hN' : ∀ i, (0 : ℝ) < N i := fun i => by have := hN i; positivity
  refine (mutualInfoPDF_parallel_le hf hN h2).trans ?_
  rw [← mul_sum, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_log_le_waterFill hN' hν
    (integral_mul_sq_apply_nonneg hf) hP) (by norm_num)

end Bound

/-! ### Normal inputs -/

/-- For independent normal inputs `Xⱼ ∼ N(0, Pⱼ)`, the output has density `∏ⱼ φ_{Pⱼ + Nⱼ}`. -/
lemma marginalSnd_parallel_gaussian {P : ι → ℝ≥0} (hP : ∀ i, P i ≠ 0) (hN : ∀ i, N i ≠ 0) :
    marginalSnd volume (noiseJointPDF (diagNoisePDF P) (diagNoisePDF N)) =
      diagNoisePDF (P + N) := by
  funext y
  simp only [marginalSnd, noiseJointPDF, diagNoisePDF, Pi.sub_apply, ← prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun i t =>
    gaussianPDFReal 0 (P i) t * gaussianPDFReal 0 (N i) (y i - t))]
  exact prod_congr rfl fun i _ =>
    congrFun (marginalSnd_gaussianChannel_gaussian (hP i) (hN i)) (y i)

/-- **(9.72)** Independent normal inputs `Xⱼ ∼ N(0, Pⱼ)` attain
`I(Xᵏ; Yᵏ) = ∑ⱼ ½ log (1 + Pⱼ/Nⱼ)`. -/
theorem mutualInfoPDF_parallel_gaussian {P : ι → ℝ≥0} (hP : ∀ i, P i ≠ 0)
    (hN : ∀ i, N i ≠ 0) :
    mutualInfoPDF volume volume (noiseJointPDF (diagNoisePDF P) (diagNoisePDF N)) =
      ∑ i, 1 / 2 * log (1 + P i / N i) := by
  have hS : ∀ i, (P + N) i ≠ 0 := fun i => by
    have : 0 < P i + N i := add_pos_of_pos_of_nonneg (pos_iff_ne_zero.2 (hP i)) zero_le
    exact this.ne'
  have hN' : ∀ i, (0 : ℝ) < N i := fun i => by have := hN i; positivity
  rw [mutualInfoPDF_noiseJointPDF_eq (diagNoisePDF_isPDF hP) (diagNoisePDF_isPDF hN)
    (diagNoisePDF_pos hN) (diagNoisePDF_pos hS)
    (fun y => congrFun (marginalSnd_parallel_gaussian hP hN) y),
    (integral_noiseJointPDF_diag_mul_log_div (diagNoisePDF_isPDF hP) hN hS
      fun i => (diagNoisePDF_moments hP i).1).2]
  refine sum_congr rfl fun i _ => ?_
  have hpos : (P i : ℝ) + N i ≠ 0 := by have := hN' i; positivity
  rw [(diagNoisePDF_moments hP i).2, Pi.add_apply, NNReal.coe_add,
    show ((P i : ℝ) + N i) / N i = 1 + P i / N i by rw [add_div, div_self (hN' i).ne', add_comm]]
  field_simp
  ring

/-! ### The information capacity -/

/-- **Definition (9.67).** The information capacity of parallel Gaussian channels with noise
variances `Nⱼ` and total power constraint `P`: the supremum of `I(Xᵏ; Yᵏ)` over the inputs with a
density and `∑ⱼ E Xⱼ² ≤ P`. -/
def parallelInfoCapacity (N : ι → ℝ≥0) (P : ℝ) : ℝ :=
  sSup {I | ∃ f : (ι → ℝ) → ℝ, IsPDF volume f ∧ (∀ i, Integrable fun x => f x * x i ^ 2) ∧
    ∑ i, ∫ x, f x * x i ^ 2 ≤ P ∧
      mutualInfoPDF volume volume (noiseJointPDF f (diagNoisePDF N)) = I}

/-- **(9.165) Water-filling.** The information capacity of parallel Gaussian channels is
`C = ∑ⱼ ½ log (1 + (ν - Nⱼ)⁺/Nⱼ)`, where the water level `ν` satisfies `∑ⱼ (ν - Nⱼ)⁺ = P`. -/
theorem parallelInfoCapacity_eq (hN : ∀ i, N i ≠ 0) {P ν : ℝ} (hν : 0 < ν)
    (hνP : ∑ i, waterFill (fun i => (N i : ℝ)) ν i = P) :
    parallelInfoCapacity N P =
      ∑ i, 1 / 2 * log (1 + waterFill (fun i => (N i : ℝ)) ν i / N i) := by
  set w := waterFill (fun i => (N i : ℝ)) ν
  set C := ∑ i, 1 / 2 * log (1 + w i / N i)
  set s := {I | ∃ f : (ι → ℝ) → ℝ, IsPDF volume f ∧ (∀ i, Integrable fun x => f x * x i ^ 2) ∧
    ∑ i, ∫ x, f x * x i ^ 2 ≤ P ∧
      mutualInfoPDF volume volume (noiseJointPDF f (diagNoisePDF N)) = I}
  have hN' : ∀ i, (0 : ℝ) < N i := fun i => by have := hN i; positivity
  have hw : ∀ i, 0 ≤ w i := waterFill_nonneg _ ν
  have hP : 0 ≤ P := hνP ▸ sum_nonneg fun i _ => hw i
  have hle : ∀ I ∈ s, I ≤ C := by
    rintro _ ⟨f, hf, h2, hpow, rfl⟩
    exact mutualInfoPDF_parallel_le_waterFill hf hN h2 hν (hpow.trans hνP.ge)
  have hnn : ∀ I ∈ s, 0 ≤ I := by
    rintro _ ⟨f, hf, -, -, rfl⟩
    exact mutualInfoPDF_nonneg' (noiseJointPDF_isPDF hf (diagNoisePDF_isPDF hN))
  have hC0 : 0 ≤ C := sum_nonneg fun i _ => mul_nonneg (by norm_num)
    (log_nonneg (by linarith [div_nonneg (hw i) (hN' i).le]))
  refine le_antisymm (Real.sSup_le hle hC0) ?_
  change C ≤ sSup s
  rcases hP.eq_or_lt with hP0 | hPpos
  · -- Without power, `C = 0`.
    have hw0 : ∀ i, w i = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg fun i _ => hw i).1 (hνP.trans hP0.symm) i (mem_univ i)
    have hC : C = 0 := by simp [C, hw0]
    rw [hC]
    exact Real.sSup_nonneg hnn
  -- Normal inputs with the positive variances `(1 - t) wᵢ + t P/k` approach `C`.
  have hbdd : BddAbove s := ⟨C, hle⟩
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Finset.univ_eq_empty] at hνP
    linarith
  set k : ℝ := (Fintype.card ι : ℝ)
  have hk : 0 < k := by simp only [k]; exact_mod_cast Fintype.card_pos
  set Pt : ℝ → ι → ℝ := fun t i => (1 - t) * w i + t * (P / k)
  set F : ℝ → ℝ := fun t => ∑ i, 1 / 2 * log (1 + Pt t i / N i)
  have hmem : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F t ∈ s := by
    intro t ht
    have hpos : ∀ i, 0 < Pt t i := fun i => by
      have h1 : 0 ≤ (1 - t) * w i := mul_nonneg (by linarith [ht.2]) (hw i)
      have h2 : 0 < t * (P / k) := mul_pos ht.1 (div_pos hPpos hk)
      simp only [Pt]
      linarith
    set Pv : ι → ℝ≥0 := fun i => ⟨Pt t i, (hpos i).le⟩
    have hPv : ∀ i, Pv i ≠ 0 := fun i h => (hpos i).ne' (congrArg NNReal.toReal h)
    refine ⟨diagNoisePDF Pv, diagNoisePDF_isPDF hPv, fun i => (diagNoisePDF_moments hPv i).1,
      ?_, mutualInfoPDF_parallel_gaussian hPv hN⟩
    have hsum : ∑ i, Pt t i = P := by
      simp only [Pt, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
      rw [hνP]
      field_simp
      ring
    simp only [fun i => (diagNoisePDF_moments hPv i).2]
    exact hsum.le
  have hcont : Tendsto F (𝓝 0) (𝓝 C) := by
    have hF0 : F 0 = C := by simp [F, Pt, C]
    rw [← hF0]
    refine tendsto_finsetSum _ fun i _ => Tendsto.const_mul _ (Tendsto.log ?_ ?_)
    · have hc : Continuous fun t => 1 + Pt t i / N i := by simp only [Pt]; fun_prop
      exact hc.tendsto 0
    · have h0 : Pt 0 i = w i := by simp [Pt]
      have : 0 ≤ Pt 0 i / N i := by rw [h0]; exact div_nonneg (hw i) (hN' i).le
      linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hev : ∀ᶠ t in 𝓝[>] 0, C - ε < F t ∧ t ∈ Set.Ioo (0 : ℝ) 1 :=
    ((hcont.eventually (lt_mem_nhds (by linarith : C - ε < C))).filter_mono
      nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT one_pos)
  obtain ⟨t, ht1, ht2⟩ := hev.exists
  have := le_csSup hbdd (hmem t ht2)
  linarith

/-- **(9.165)** The information capacity of parallel Gaussian channels with power `P ≥ 0`, with
the water level given by `exists_waterLevel`. -/
theorem exists_parallelInfoCapacity_eq [Nonempty ι] (hN : ∀ i, N i ≠ 0) {P : ℝ} (hP : 0 ≤ P) :
    ∃ ν, 0 < ν ∧ ∑ i, waterFill (fun i => (N i : ℝ)) ν i = P ∧
      parallelInfoCapacity N P =
        ∑ i, 1 / 2 * log (1 + waterFill (fun i => (N i : ℝ)) ν i / N i) := by
  obtain ⟨ν, -, ⟨i, hi⟩, hνP⟩ := exists_waterLevel (fun i => (N i : ℝ)) hP
  have hν : 0 < ν := lt_of_lt_of_le (by have := hN i; positivity) hi
  exact ⟨ν, hν, hνP, parallelInfoCapacity_eq hN hν hνP⟩

end InfoTheory
