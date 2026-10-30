/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Gaussian
public import InfoTheoryLib.GaussianChannel.Parallel

/-!
# Independent Gaussian sources: reverse water-filling

Independent sources `Xᵢ ∼ N(0, σᵢ²)`, `i = 1, …, m`, are described together with the distortion
`d(xᵐ, x̂ᵐ) = ∑ᵢ (xᵢ - x̂ᵢ)²`. The information rate distortion function (10.38) is

  `R(D) = ∑ᵢ ½ log (σᵢ²/Dᵢ)`, `Dᵢ = min {λ, σᵢ²}`, `∑ᵢ Dᵢ = D`:

the components with variance below the level `λ` are not described at all (reverse
water-filling).

## Main definitions

* `revWaterFill σ λ i = min {λ, σᵢ}`: the distortion allocation (10.52).
* `parallelInfoRD σ D`: the information rate distortion function (10.38).

## Main statements

* `exists_revWaterLevel`: for `0 ≤ D ≤ ∑ᵢ σᵢ` there is a level `λ` with `∑ᵢ min {λ, σᵢ} = D`.
* `sum_half_log_revWaterFill_le`: (10.45)–(10.50), reverse water-filling minimizes
  `∑ᵢ (½ log (σᵢ/δᵢ))⁺` subject to `∑ᵢ δᵢ ≤ D`.
* `sum_half_log_le_mutualInfoPDF_parallel`: (10.39)–(10.44),
  `I(Xᵐ; X̂ᵐ) ≥ ∑ᵢ (½ log (σᵢ/E(Xᵢ - X̂ᵢ)²))⁺`.
* `parallelInfoRD_eq`: **Theorem 10.3.3**.

## Implementation notes

As for one source, `I(Xᵐ; X̂ᵐ)` is bounded below by comparing the conditional density of the source
given the reproduction with a normal density, here a product over the components of
`φ_{δᵢ}(xᵢ - x̂ᵢ)` for the described components and `φ_{σᵢ}(xᵢ)` for the others. The book derives
the allocation with the Kuhn–Tucker conditions; we verify it with a tangent line bound. The
components with `σᵢ ≤ λ` would be reproduced by `X̂ᵢ = 0`, which has no density, so the minimum is
approached by test channels describing them with a small rate.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 10.3.3
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*}

/-! ### Reverse water-filling -/

/-- **(10.52)** The reverse water-filling allocation `Dᵢ = min {λ, σᵢ}`. -/
def revWaterFill (σ : ι → ℝ) (lam : ℝ) (i : ι) : ℝ := min lam (σ i)

variable [Fintype ι]

lemma continuous_sum_revWaterFill (σ : ι → ℝ) : Continuous fun lam => ∑ i, revWaterFill σ lam i :=
  continuous_finsetSum _ fun _ _ => continuous_id.min continuous_const

/-- For every `0 ≤ D ≤ ∑ᵢ σᵢ` there is a level `λ ≥ 0` with `∑ᵢ min {λ, σᵢ} = D`. -/
theorem exists_revWaterLevel [Nonempty ι] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : D ≤ ∑ i, σ i) : ∃ lam, 0 ≤ lam ∧ ∑ i, revWaterFill σ lam i = D := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image univ σ univ_nonempty
  have hf0 : ∑ i, revWaterFill σ 0 i = 0 := sum_eq_zero fun i _ => min_eq_left (hσ i)
  have hf1 : ∑ i, revWaterFill σ (σ i₀) i = ∑ i, σ i :=
    sum_congr rfl fun i _ => min_eq_right (hi₀ i (mem_univ i))
  obtain ⟨lam, hlam, hD'⟩ := intermediate_value_Icc (hσ i₀)
    (continuous_sum_revWaterFill σ).continuousOn ⟨hf0 ▸ hD0, hf1 ▸ hD⟩
  exact ⟨lam, hlam.1, hD'⟩

omit [Fintype ι] in
/-- The tangent line bound behind (10.45)–(10.50): for `λ, σ, δ > 0`,
`½ log (σ/min {λ, σ}) + (min {λ, σ} - δ)/(2λ) ≤ (½ log (σ/δ))⁺`. -/
lemma half_log_revWaterFill_add_le {lam s δ : ℝ} (hlam : 0 < lam) (hs : 0 < s) (hδ : 0 < δ) :
    1 / 2 * log (s / min lam s) + (min lam s - δ) / (2 * lam) ≤ max (1 / 2 * log (s / δ)) 0 := by
  rcases le_total lam s with h | h
  · rw [min_eq_left h]
    refine le_max_of_le_left ?_
    have hlog := one_sub_inv_le_log_of_pos (div_pos hlam hδ)
    rw [inv_div, log_div hlam.ne' hδ.ne'] at hlog
    rw [log_div hs.ne' hlam.ne', log_div hs.ne' hδ.ne']
    have : (lam - δ) / (2 * lam) = 1 / 2 * (1 - δ / lam) := by field_simp
    rw [this]
    linarith
  · rw [min_eq_right h, div_self hs.ne', log_one, mul_zero, zero_add]
    rcases le_total s δ with hsδ | hsδ
    · exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)).trans (le_max_right _ _)
    · refine le_max_of_le_left ?_
      have hlog := one_sub_inv_le_log_of_pos (div_pos hs hδ)
      rw [inv_div] at hlog
      calc (s - δ) / (2 * lam) ≤ (s - δ) / (2 * s) :=
            div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
        _ = 1 / 2 * (1 - δ / s) := by field_simp
        _ ≤ 1 / 2 * log (s / δ) := by linarith

/-- **(10.45)–(10.50) Reverse water-filling.** For `λ > 0` and distortions `δᵢ > 0` with
`∑ᵢ δᵢ ≤ ∑ᵢ min {λ, σᵢ}`, `∑ᵢ ½ log (σᵢ/min {λ, σᵢ}) ≤ ∑ᵢ (½ log (σᵢ/δᵢ))⁺`. -/
theorem sum_half_log_revWaterFill_le {σ δ : ι → ℝ} (hσ : ∀ i, 0 < σ i) {lam : ℝ} (hlam : 0 < lam)
    (hδ : ∀ i, 0 < δ i) (hsum : ∑ i, δ i ≤ ∑ i, revWaterFill σ lam i) :
    ∑ i, 1 / 2 * log (σ i / revWaterFill σ lam i) ≤ ∑ i, max (1 / 2 * log (σ i / δ i)) 0 := by
  have h := sum_le_sum fun i (_ : i ∈ univ) => half_log_revWaterFill_add_le hlam (hσ i) (hδ i)
  rw [sum_add_distrib, ← sum_div, sum_sub_distrib] at h
  have : 0 ≤ (∑ i, min lam (σ i) - ∑ i, δ i) / (2 * lam) :=
    div_nonneg (by simpa [revWaterFill] using hsum) (by positivity)
  simp only [revWaterFill] at h ⊢
  linarith

/-! ### The lower bound -/

open Classical in
/-- The conditional reference density of the source component `xᵢ` given `x̂ᵢ`:
`φ_{tᵢ}(xᵢ - x̂ᵢ)` for a described component `i ∈ s`, and `φ_{σᵢ}(xᵢ)` otherwise. -/
def refKernel (σ t : ι → ℝ≥0) (s : Finset ι) (i : ι) (a b : ℝ) : ℝ :=
  if i ∈ s then gaussianPDFReal 0 (t i) (a - b) else gaussianPDFReal 0 (σ i) a

omit [Fintype ι] in
lemma refKernel_pos {σ t : ι → ℝ≥0} (hσ : ∀ i, σ i ≠ 0) (ht : ∀ i, t i ≠ 0) (s : Finset ι)
    (i : ι) (a b : ℝ) : 0 < refKernel σ t s i a b := by
  unfold refKernel
  split_ifs
  · exact gaussianPDFReal_pos _ _ _ (ht i)
  · exact gaussianPDFReal_pos _ _ _ (hσ i)

omit [Fintype ι] in
lemma refKernel_isPDF {σ t : ι → ℝ≥0} (hσ : ∀ i, σ i ≠ 0) (ht : ∀ i, t i ≠ 0) (s : Finset ι)
    (i : ι) (b : ℝ) : IsPDF volume fun a => refKernel σ t s i a b := by
  unfold refKernel
  split_ifs
  · simp_rw [gaussianPDFReal_sub]
    exact gaussianPDFReal_isPDF _ (ht i)
  · exact gaussianPDFReal_isPDF _ (hσ i)

open Classical in
omit [Fintype ι] in
/-- `log (refKernel/φ_{σᵢ}(xᵢ))` vanishes off `s`, and on `s` it is
`log (σᵢ/tᵢ)/2 - (xᵢ - x̂ᵢ)²/(2tᵢ) + xᵢ²/(2σᵢ)`. -/
lemma log_refKernel_div {σ t : ι → ℝ≥0} (hσ : ∀ i, σ i ≠ 0) (ht : ∀ i, t i ≠ 0) (s : Finset ι)
    (i : ι) (a b : ℝ) :
    log (refKernel σ t s i a b / gaussianPDFReal 0 (σ i) a) = if i ∈ s then
      log (σ i / t i) / 2 - (a - b) ^ 2 / (2 * t i) + a ^ 2 / (2 * σ i) else 0 := by
  unfold refKernel
  split_ifs
  · exact log_gaussianPDFReal_sub_div (ht i) (hσ i) b a
  · rw [div_self (gaussianPDFReal_pos _ _ _ (hσ i)).ne', log_one]

/-- **(10.39)–(10.44), the key bound.** If `X ∼ N(0, diag σ)`, then for every set `s` of described
components and variances `tᵢ > 0`,
`I(Xᵐ; X̂ᵐ) ≥ ∑_{i ∈ s} (½ log (σᵢ/tᵢ) - E(Xᵢ - X̂ᵢ)²/(2tᵢ) + ½)`. -/
theorem sum_le_mutualInfoPDF_parallel {σ t : ι → ℝ≥0} (hσ : ∀ i, σ i ≠ 0) (ht : ∀ i, t i ≠ 0)
    (s : Finset ι) {f : (ι → ℝ) × (ι → ℝ) → ℝ} (hf : IsPDF (volume.prod volume) f)
    (hX : marginalFst volume f = diagNoisePDF σ)
    (h2 : ∀ i, Integrable (fun z => f z * (z.1 i - z.2 i) ^ 2) (volume.prod volume))
    (hI : Integrable (fun z => f z * log (f z / (marginalFst volume f z.1 *
      marginalSnd volume f z.2))) (volume.prod volume)) :
    ∑ i ∈ s, (log (σ i / t i) / 2 - (∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume)) /
      (2 * t i) + 1 / 2) ≤ mutualInfoPDF volume volume f := by
  classical
  set g : (ι → ℝ) × (ι → ℝ) → ℝ := fun z => ∏ i, refKernel σ t s i (z.1 i) (z.2 i)
  have hgm : Measurable g := Finset.measurable_prod _ fun i _ => by
    unfold refKernel
    split_ifs
    · exact (measurable_gaussianPDFReal 0 _).comp
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp measurable_snd))
    · exact (measurable_gaussianPDFReal 0 _).comp ((measurable_pi_apply i).comp measurable_fst)
  have hgpos : ∀ z, 0 < g z := fun z => prod_pos fun i _ => refKernel_pos hσ ht s i _ _
  have hg1 : ∀ y, Integrable (fun x => g (x, y)) ∧ ∫ x, g (x, y) = 1 := fun y =>
    let h := isPDF_prod_apply fun i => refKernel_isPDF hσ ht s i (y i)
    ⟨h.integrable, h.integral_eq_one⟩
  -- The moments `E Xᵢ² = σᵢ`.
  have hmom : ∀ i, Integrable (fun z => f z * z.1 i ^ 2) (volume.prod volume) ∧
      ∫ z, f z * z.1 i ^ 2 ∂(volume.prod volume) = σ i := fun i => by
    obtain ⟨i1, e1⟩ := integral_mul_comp_fst hf (G := fun x => x i ^ 2) (by fun_prop)
      (by rw [hX]; exact (diagNoisePDF_moments hσ i).1)
    rw [hX, (diagNoisePDF_moments hσ i).2] at e1
    exact ⟨i1, e1⟩
  -- The integrand of the lower bound, component by component.
  set T : ι → (ι → ℝ) × (ι → ℝ) → ℝ := fun i z => if i ∈ s then
    log (σ i / t i) / 2 * f z - (2 * (t i : ℝ))⁻¹ * (f z * (z.1 i - z.2 i) ^ 2) +
      (2 * (σ i : ℝ))⁻¹ * (f z * z.1 i ^ 2) else 0
  have hlog : ∀ z, f z * log (g z / marginalFst volume f z.1) = ∑ i, T i z := fun z => by
    rw [hX, diagNoisePDF, ← prod_div_distrib, log_prod fun i _ =>
      (div_pos (refKernel_pos hσ ht s i _ _) (gaussianPDFReal_pos _ _ _ (hσ i))).ne', mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [log_refKernel_div hσ ht s i]
    simp only [T]
    split_ifs
    · ring
    · ring
  have hT : ∀ i, Integrable (T i) (volume.prod volume) := fun i => by
    simp only [T]
    split_ifs
    · exact ((hf.integrable.const_mul _).sub ((h2 i).const_mul _)).add ((hmom i).1.const_mul _)
    · exact integrable_zero _ _ _
  have hTi : ∀ i, ∫ z, T i z ∂(volume.prod volume) = if i ∈ s then
      log (σ i / t i) / 2 - (∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume)) / (2 * t i) +
        1 / 2 else 0 := fun i => by
    have hσi : (0 : ℝ) < σ i := by have := hσ i; positivity
    simp only [T]
    split_ifs
    · have hA : Integrable (fun z => log (σ i / t i) / 2 * f z - (2 * (t i : ℝ))⁻¹ *
          (f z * (z.1 i - z.2 i) ^ 2)) (volume.prod volume) :=
        (hf.integrable.const_mul _).sub ((h2 i).const_mul _)
      have hB : Integrable (fun z => (2 * (σ i : ℝ))⁻¹ * (f z * z.1 i ^ 2))
          (volume.prod volume) := (hmom i).1.const_mul _
      rw [integral_add hA hB, integral_sub (hf.integrable.const_mul _) ((h2 i).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, hf.integral_eq_one,
        (hmom i).2]
      field_simp
    · exact integral_zero _ _
  have hG : Integrable (fun z => f z * log (g z / marginalFst volume f z.1))
      (volume.prod volume) := by
    simp_rw [hlog]
    exact integrable_finsetSum _ fun i _ => hT i
  have hbound := integral_mul_log_div_le_mutualInfoPDF hf hgm hgpos hg1 hI hG
  have hval : ∫ z, f z * log (g z / marginalFst volume f z.1) ∂(volume.prod volume) =
      ∑ i ∈ s, (log (σ i / t i) / 2 -
        (∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume)) / (2 * t i) + 1 / 2) := by
    rw [integral_congr_ae (Eventually.of_forall hlog), integral_finsetSum _ fun i _ => hT i]
    simp_rw [hTi]
    rw [sum_ite_mem, univ_inter]
  exact hval ▸ hbound

lemma integral_mul_sq_sub_nonneg {f : (ι → ℝ) × (ι → ℝ) → ℝ}
    (hf : IsPDF (volume.prod volume) f) (i : ι) :
    0 ≤ ∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume) :=
  integral_nonneg fun z => mul_nonneg (hf.nonneg z) (sq_nonneg _)

/-- **(10.39)–(10.44)** If `X ∼ N(0, diag σ)`, every component has a positive distortion
`δᵢ = E(Xᵢ - X̂ᵢ)² > 0`, and `I(Xᵐ; X̂ᵐ) ≥ ∑ᵢ (½ log (σᵢ/δᵢ))⁺`. -/
theorem sum_half_log_le_mutualInfoPDF_parallel {σ : ι → ℝ≥0} (hσ : ∀ i, σ i ≠ 0)
    {f : (ι → ℝ) × (ι → ℝ) → ℝ} (hf : IsPDF (volume.prod volume) f)
    (hX : marginalFst volume f = diagNoisePDF σ)
    (h2 : ∀ i, Integrable (fun z => f z * (z.1 i - z.2 i) ^ 2) (volume.prod volume))
    (hI : Integrable (fun z => f z * log (f z / (marginalFst volume f z.1 *
      marginalSnd volume f z.2))) (volume.prod volume)) :
    (∀ i, 0 < ∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume)) ∧
      ∑ i, max (1 / 2 * log (σ i / ∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume))) 0 ≤
        mutualInfoPDF volume volume f := by
  classical
  set δ : ι → ℝ := fun i => ∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume)
  have hσ' : ∀ i, (0 : ℝ) < σ i := fun i => by have := hσ i; positivity
  set I := mutualInfoPDF volume volume f
  -- A component with `δᵢ = 0` would give `I ≥ ½ log (σᵢ/t) + ½` for every `t > 0`.
  have hpos : ∀ i, 0 < δ i := by
    intro i
    refine lt_of_le_of_ne (integral_mul_sq_sub_nonneg hf i) fun h0 => ?_
    set t : ℝ≥0 := (σ i * exp (-(2 * (I + 1)))).toNNReal
    have ht' : (t : ℝ) = σ i * exp (-(2 * (I + 1))) :=
      Real.coe_toNNReal _ (mul_pos (hσ' i) (exp_pos _)).le
    have ht0 : t ≠ 0 := by
      intro h
      have := congrArg NNReal.toReal h
      rw [ht', NNReal.coe_zero] at this
      exact (mul_pos (hσ' i) (exp_pos _)).ne' this
    have h := sum_le_mutualInfoPDF_parallel hσ (t := fun _ => t) (fun _ => ht0) {i} hf hX h2 hI
    rw [sum_singleton, show (∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume)) = 0 from h0.symm,
      zero_div, sub_zero, ht', div_mul_cancel_left₀ (hσ' i).ne', log_inv, log_exp] at h
    linarith
  refine ⟨hpos, ?_⟩
  -- Describe the components with `δᵢ < σᵢ`, with `tᵢ = δᵢ`.
  set s := univ.filter fun i => δ i < σ i
  set t : ι → ℝ≥0 := fun i => (δ i).toNNReal
  have ht' : ∀ i, (t i : ℝ) = δ i := fun i => Real.coe_toNNReal _ (hpos i).le
  have ht0 : ∀ i, t i ≠ 0 := fun i h => by
    have := congrArg NNReal.toReal h
    rw [ht', NNReal.coe_zero] at this
    exact (hpos i).ne' this
  have h := sum_le_mutualInfoPDF_parallel hσ ht0 s hf hX h2 hI
  refine le_trans (le_of_eq ?_) h
  rw [← sum_filter_add_sum_filter_not univ fun i => δ i < σ i]
  have h0 : ∑ i ∈ univ.filter (fun i => ¬δ i < σ i),
      max (1 / 2 * log (σ i / δ i)) 0 = 0 := sum_eq_zero fun i hi => by
    simp only [mem_filter, mem_univ, true_and, not_lt] at hi
    exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (log_nonpos (div_nonneg (hσ' i).le (hpos i).le) ((div_le_one (hpos i)).2 hi)))
  rw [h0, add_zero]
  refine sum_congr rfl fun i hi => ?_
  simp only [s, mem_filter, mem_univ, true_and] at hi
  have hδσ : 1 < σ i / δ i := (one_lt_div (hpos i)).2 hi
  rw [ht', max_eq_left (mul_nonneg (by norm_num) (log_nonneg hδσ.le))]
  change _ = log (σ i / δ i) / 2 - δ i / (2 * δ i) + 1 / 2
  have hd : δ i / (2 * δ i) = 1 / 2 := by
    have := (hpos i).ne'
    field_simp
  rw [hd]
  ring

/-! ### The test channel -/

/-- The test channel `X = X̂ + Z` with `X̂ᵢ ∼ N(0, σᵢ - Nᵢ)` and `Zᵢ ∼ N(0, Nᵢ)` independent; its
joint density at `(x, x̂)` is `∏ᵢ φ_{σᵢ-Nᵢ}(x̂ᵢ) φ_{Nᵢ}(xᵢ - x̂ᵢ)`. -/
def parallelTestPDF (σ N : ι → ℝ≥0) : (ι → ℝ) × (ι → ℝ) → ℝ :=
  noiseJointPDF (diagNoisePDF (σ - N)) (diagNoisePDF N) ∘ Prod.swap

section Test

variable {σ N : ι → ℝ≥0} (hN : ∀ i, N i ≠ 0) (hNσ : ∀ i, N i < σ i)
include hN hNσ

lemma parallelTestPDF_isPDF : IsPDF (volume.prod volume) (parallelTestPDF σ N) :=
  (noiseJointPDF_isPDF (diagNoisePDF_isPDF fun i => (tsub_pos_of_lt (hNσ i)).ne')
    (diagNoisePDF_isPDF hN)).swap

lemma marginalFst_parallelTestPDF :
    marginalFst volume (parallelTestPDF σ N) = diagNoisePDF σ := by
  rw [parallelTestPDF, marginalFst_swap,
    marginalSnd_parallel_gaussian (P := σ - N) (fun i => (tsub_pos_of_lt (hNσ i)).ne') hN]
  congr 1
  funext i
  exact tsub_add_cancel_of_le (hNσ i).le

lemma integral_parallelTestPDF_mul_sq (i : ι) :
    Integrable (fun z => parallelTestPDF σ N z * (z.1 i - z.2 i) ^ 2) (volume.prod volume) ∧
      ∫ z, parallelTestPDF σ N z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume) = N i := by
  have hP := diagNoisePDF_isPDF fun i => (tsub_pos_of_lt (hNσ i)).ne'
  have hg := diagNoisePDF_isPDF hN
  obtain ⟨j, e⟩ := integral_noiseJointPDF_mul (μ := volume) (ν := volume) hP hg.measurable
    hg.nonneg (h := fun z => (z.2 i - z.1 i) ^ 2) (by fun_prop) (fun z => sq_nonneg _)
    (k := fun _ => (N i : ℝ))
    (fun x => ⟨(diagNoisePDF_sub_moments hN x i).1, (diagNoisePDF_sub_moments hN x i).2.1⟩)
    (hP.integrable.mul_const _)
  refine ⟨j.swap, ?_⟩
  rw [integral_mul_const, hP.integral_eq_one, one_mul] at e
  rw [← e, ← integral_prod_swap]
  rfl

/-- **(10.41)–(10.44), equality.** The test channel attains `I(Xᵐ; X̂ᵐ) = ∑ᵢ ½ log (σᵢ/Nᵢ)`, with
an integrable mutual information integrand. -/
theorem mutualInfoPDF_parallelTest :
    Integrable (fun z => parallelTestPDF σ N z * log (parallelTestPDF σ N z /
        (marginalFst volume (parallelTestPDF σ N) z.1 *
          marginalSnd volume (parallelTestPDF σ N) z.2))) (volume.prod volume) ∧
      mutualInfoPDF volume volume (parallelTestPDF σ N) = ∑ i, 1 / 2 * log (σ i / N i) := by
  have hP : ∀ i, (σ - N) i ≠ 0 := fun i => (tsub_pos_of_lt (hNσ i)).ne'
  have hPN : σ - N + N = σ := funext fun i => tsub_add_cancel_of_le (hNσ i).le
  have hσ : ∀ i, σ i ≠ 0 := fun i => (lt_of_le_of_lt (by positivity : (0 : ℝ≥0) ≤ N i)
    (hNσ i)).ne'
  set J := noiseJointPDF (diagNoisePDF (σ - N)) (diagNoisePDF N)
  have hJ := noiseJointPDF_isPDF (μ := volume) (ν := volume) (diagNoisePDF_isPDF hP)
    (diagNoisePDF_isPDF hN)
  have hout := marginalSnd_parallel_gaussian hP hN
  rw [hPN] at hout
  have hint : Integrable (fun z => J z * log (J z / (marginalFst volume J z.1 *
      marginalSnd volume J z.2))) (volume.prod volume) := by
    refine (integral_noiseJointPDF_diag_mul_log_div (diagNoisePDF_isPDF hP) hN hσ
      fun i => (diagNoisePDF_moments hP i).1).1.congr ?_
    filter_upwards [ae_marginalSnd_eq_zero hJ] with z hz
    rw [marginalFst_noiseJointPDF (diagNoisePDF_isPDF hN),
      noiseJointPDF_mul_log_eq (diagNoisePDF_pos hN) (diagNoisePDF_pos hσ) hz, hout,
      div_self (diagNoisePDF_pos hσ _).ne', log_one, mul_zero, sub_zero]
  refine ⟨integrable_mutualInfoPDF_integrand_swap hint, ?_⟩
  rw [parallelTestPDF, mutualInfoPDF_swap, mutualInfoPDF_parallel_gaussian hP hN]
  refine sum_congr rfl fun i _ => ?_
  have hN' : (0 : ℝ) < N i := by have := hN i; positivity
  congr 2
  rw [Pi.sub_apply, NNReal.coe_sub (hNσ i).le]
  field_simp
  ring

end Test

/-! ### Theorem 10.3.3 -/

/-- **Definition (10.38).** The information rate distortion function of independent sources
`Xᵢ ∼ N(0, σᵢ)` with the distortion `∑ᵢ (xᵢ - x̂ᵢ)²`: the infimum of `I(Xᵐ; X̂ᵐ)` over the joint
densities with `Xᵐ ∼ N(0, diag σ)` and `∑ᵢ E(Xᵢ - X̂ᵢ)² ≤ D`. -/
def parallelInfoRD (σ : ι → ℝ≥0) (D : ℝ) : ℝ :=
  sInf {I | ∃ f : (ι → ℝ) × (ι → ℝ) → ℝ, IsPDF (volume.prod volume) f ∧
    marginalFst volume f = diagNoisePDF σ ∧
    (∀ i, Integrable (fun z => f z * (z.1 i - z.2 i) ^ 2) (volume.prod volume)) ∧
    ∑ i, ∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume) ≤ D ∧
    Integrable (fun z => f z * log (f z / (marginalFst volume f z.1 * marginalSnd volume f z.2)))
      (volume.prod volume) ∧
    mutualInfoPDF volume volume f = I}

/-- **Theorem 10.3.3 (Rate distortion for a parallel Gaussian source).** For independent
`Xᵢ ∼ N(0, σᵢ)` and the distortion `∑ᵢ (xᵢ - x̂ᵢ)²`, `R(D) = ∑ᵢ ½ log (σᵢ/Dᵢ)` with
`Dᵢ = min {λ, σᵢ}` (10.52), where `λ > 0` is chosen so that `∑ᵢ Dᵢ = D`. -/
theorem parallelInfoRD_eq {σ : ι → ℝ≥0} (hσ : ∀ i, σ i ≠ 0) {lam : ℝ} (hlam : 0 < lam) {D : ℝ}
    (hD : ∑ i, revWaterFill (fun i => (σ i : ℝ)) lam i = D) :
    parallelInfoRD σ D = ∑ i, 1 / 2 * log (σ i / revWaterFill (fun i => (σ i : ℝ)) lam i) := by
  set s := {I | ∃ f : (ι → ℝ) × (ι → ℝ) → ℝ, IsPDF (volume.prod volume) f ∧
    marginalFst volume f = diagNoisePDF σ ∧
    (∀ i, Integrable (fun z => f z * (z.1 i - z.2 i) ^ 2) (volume.prod volume)) ∧
    ∑ i, ∫ z, f z * (z.1 i - z.2 i) ^ 2 ∂(volume.prod volume) ≤ D ∧
    Integrable (fun z => f z * log (f z / (marginalFst volume f z.1 * marginalSnd volume f z.2)))
      (volume.prod volume) ∧
    mutualInfoPDF volume volume f = I}
  set R := ∑ i, 1 / 2 * log (σ i / revWaterFill (fun i => (σ i : ℝ)) lam i)
  have hσ' : ∀ i, (0 : ℝ) < σ i := fun i => by have := hσ i; positivity
  -- The lower bound.
  have hle : ∀ I ∈ s, R ≤ I := by
    rintro _ ⟨f, hf, hX, h2, hfD, hI, rfl⟩
    obtain ⟨hpos, hbound⟩ := sum_half_log_le_mutualInfoPDF_parallel hσ hf hX h2 hI
    exact (sum_half_log_revWaterFill_le hσ' hlam hpos (hfD.trans hD.ge)).trans hbound
  -- The test channels with `Nᵢ = min {λ, σᵢ - η}` for small `η > 0`.
  set Dη : ℝ → ι → ℝ := fun η i => min lam (σ i - η)
  set F : ℝ → ℝ := fun η => ∑ i, 1 / 2 * log (σ i / Dη η i)
  have hmem : ∀ η : ℝ, 0 < η → (∀ i, η < (σ i : ℝ)) → F η ∈ s := by
    intro η hη hησ
    have hpos : ∀ i, 0 < Dη η i := fun i => lt_min hlam (by linarith [hησ i])
    set N : ι → ℝ≥0 := fun i => (Dη η i).toNNReal
    have hN' : ∀ i, (N i : ℝ) = Dη η i := fun i => Real.coe_toNNReal _ (hpos i).le
    have hN : ∀ i, N i ≠ 0 := fun i h => by
      have := congrArg NNReal.toReal h
      rw [hN', NNReal.coe_zero] at this
      exact (hpos i).ne' this
    have hNσ : ∀ i, N i < σ i := fun i => by
      rw [← NNReal.coe_lt_coe, hN']
      exact (min_le_right _ _).trans_lt (by linarith)
    obtain ⟨hi, he⟩ := mutualInfoPDF_parallelTest hN hNσ
    refine ⟨_, parallelTestPDF_isPDF hN hNσ, marginalFst_parallelTestPDF hN hNσ,
      fun i => (integral_parallelTestPDF_mul_sq hN hNσ i).1, ?_, hi, ?_⟩
    · simp only [fun i => (integral_parallelTestPDF_mul_sq hN hNσ i).2, hN']
      rw [← hD]
      exact sum_le_sum fun i _ => min_le_min_left _ (by linarith)
    · rw [he]
      exact sum_congr rfl fun i _ => by rw [hN']
  have hcont : Tendsto F (𝓝[>] 0) (𝓝 R) := by
    have hF0 : F 0 = R := by simp [F, Dη, R, revWaterFill]
    rw [← hF0]
    refine tendsto_nhdsWithin_of_tendsto_nhds (tendsto_finsetSum _ fun i _ =>
      Tendsto.const_mul _ (Tendsto.log (tendsto_const_nhds.div ?_ ?_) ?_))
    · exact ((continuous_const.min (continuous_const.sub continuous_id)).tendsto 0)
    · simp only [Dη, sub_zero]
      exact (lt_min hlam (hσ' i)).ne'
    · simp only [Dη, sub_zero]
      exact (div_pos (hσ' i) (lt_min hlam (hσ' i))).ne'
  refine le_antisymm ?_ (le_csInf ?_ hle)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev : ∀ᶠ η in 𝓝[>] 0, F η < R + ε ∧ 0 < η ∧ ∀ i, η < (σ i : ℝ) :=
      (hcont.eventually (gt_mem_nhds (by linarith))).and (eventually_mem_nhdsWithin.and
        (eventually_all.2 fun i => eventually_of_mem (Ioo_mem_nhdsGT (hσ' i)) fun η h => h.2))
    obtain ⟨η, hη1, hη2, hη3⟩ := hev.exists
    exact (csInf_le ⟨R, hle⟩ (hmem η hη2 hη3)).trans hη1.le
  · obtain ⟨η, hη2, hη3⟩ := ((eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).and
      (eventually_all.2 fun i => eventually_of_mem (Ioo_mem_nhdsGT (hσ' i)) fun η h => h.2)).exists
    exact ⟨_, hmem η hη2 hη3⟩

end InfoTheory
