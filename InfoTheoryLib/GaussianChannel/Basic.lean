/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.Joint

/-!
# Additive noise channels

An additive noise channel adds to its input `X` an independent noise `Z` with density `g`: the
output is `Y = X + Z`. If `X` has density `f` with respect to `μ`, the pair `(X, Y)` has density
`f(x) g(y - x)` with respect to `μ × ν`, where `ν` is a translation invariant measure (the
Lebesgue measure). Comparing the conditional density `g(y - x)` of the output with any other
density `q` bounds the mutual information:
`I(X; Y) ≤ ∫ f(x) g(y - x) log (g(y - x)/q(y))`, with equality when `q` is the density of `Y`.
This is how the capacity of the Gaussian channel is computed: with `q` normal, the right side is
explicit.

## Main definitions

* `noiseJointPDF f g`: the joint density `f(x) g(y - x)` of `(X, X + Z)`.

## Main statements

* `noiseJointPDF_isPDF`, `marginalFst_noiseJointPDF`: it is a density, with first marginal `f`.
* `integral_noiseJointPDF_mul`: integrals against the joint density, integrating over `y` first.
* `mutualInfoPDF_nonneg'`: `I(X; Y) ≥ 0` for every joint density.
* `mutualInfoPDF_noiseJointPDF_le`: `I(X; Y) ≤ ∫ f(x) g(y - x) log (g(y - x)/q(y))` for every
  positive density `q`.
* `mutualInfoPDF_noiseJointPDF_eq`: equality when `q` is the density of the output.

## Implementation notes

The bound needs no integrability hypothesis on the mutual information, only on its right side:
if the integrand of `I(X; Y)` is not integrable the mutual information is `0` by convention, and
the right side is a relative entropy, hence non-negative.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.1
-/

open Real MeasureTheory Filter

@[expose] public noncomputable section

namespace InfoTheory

section General

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Theorem 8.6.1** without integrability hypothesis: `D(f‖g) ≥ 0` for densities `f ≪ g`, where
`D(f‖g)` is `0` by convention when its integrand is not integrable. -/
theorem relEntropyPDF_nonneg' {f g : α → ℝ} (hf : IsPDF μ f) (hg : IsPDF μ g)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) : 0 ≤ relEntropyPDF μ f g := by
  by_cases hint : Integrable (fun x => f x * log (f x / g x)) μ
  · exact relEntropyPDF_nonneg hf hg hfg hint
  · rw [relEntropyPDF, integral_undef hint]

variable {β : Type*} [MeasurableSpace β] {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]

/-- The product `f(x) q(y)` of two densities is a density. -/
lemma IsPDF.mul_prod {f : α → ℝ} {q : β → ℝ} (hf : IsPDF μ f) (hq : IsPDF ν q) :
    IsPDF (μ.prod ν) fun z => f z.1 * q z.2 :=
  ⟨(hf.measurable.comp measurable_fst).mul (hq.measurable.comp measurable_snd),
    fun z => mul_nonneg (hf.nonneg _) (hq.nonneg _), hf.integrable.mul_prod hq.integrable,
    by rw [integral_prod_mul, hf.integral_eq_one, hq.integral_eq_one, one_mul]⟩

/-- `I(X; Y) ≥ 0` for every joint density, with the convention that `I(X; Y) = 0` when its
integrand is not integrable. -/
theorem mutualInfoPDF_nonneg' {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    0 ≤ mutualInfoPDF μ ν f :=
  relEntropyPDF_nonneg' hf hf.prod_marginals (ae_marginals_eq_zero hf)

end General

/-! ### The joint density of an additive noise channel -/

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] [MeasurableSub₂ G]
  {μ ν : Measure G} [SigmaFinite μ] [SigmaFinite ν] [ν.IsAddRightInvariant]

/-- The joint density `f(x) g(y - x)` of the input `X` and the output `Y = X + Z` of an additive
noise channel, where `X` has density `f` and the noise `Z` is independent of `X` with density
`g`. -/
def noiseJointPDF (f g : G → ℝ) (z : G × G) : ℝ := f z.1 * g (z.2 - z.1)

omit [MeasurableAdd G] [SigmaFinite μ] [SigmaFinite ν] [ν.IsAddRightInvariant] in
lemma measurable_noiseJointPDF {f g : G → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (noiseJointPDF f g) :=
  (hf.comp measurable_fst).mul (hg.comp (measurable_snd.sub measurable_fst))

omit [MeasurableSub₂ G] [SigmaFinite μ] [SigmaFinite ν] in
lemma integral_noiseJointPDF_right {f g : G → ℝ} (hg : IsPDF ν g) (x : G) :
    ∫ y, noiseJointPDF f g (x, y) ∂ν = f x := by
  simp only [noiseJointPDF]
  rw [integral_const_mul, integral_sub_right_eq_self g x, hg.integral_eq_one, mul_one]

/-- The joint density of `(X, X + Z)` is a density. -/
lemma noiseJointPDF_isPDF {f g : G → ℝ} (hf : IsPDF μ f) (hg : IsPDF ν g) :
    IsPDF (μ.prod ν) (noiseJointPDF f g) := by
  have hm := measurable_noiseJointPDF hf.measurable hg.measurable
  have hint : Integrable (noiseJointPDF f g) (μ.prod ν) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact (hg.integrable.comp_sub_right x).const_mul (f x)
    · refine hf.integrable.congr (Eventually.of_forall fun x => ?_)
      have : ∀ y, ‖noiseJointPDF f g (x, y)‖ = noiseJointPDF f g (x, y) := fun y =>
        Real.norm_of_nonneg (mul_nonneg (hf.nonneg _) (hg.nonneg _))
      simp only [this, integral_noiseJointPDF_right hg]
  refine ⟨hm, fun z => mul_nonneg (hf.nonneg _) (hg.nonneg _), hint, ?_⟩
  rw [integral_prod _ hint]
  simp only [integral_noiseJointPDF_right hg, hf.integral_eq_one]

omit [MeasurableSub₂ G] [SigmaFinite μ] [SigmaFinite ν] in
/-- The input has density `f`. -/
lemma marginalFst_noiseJointPDF {f g : G → ℝ} (hg : IsPDF ν g) :
    marginalFst ν (noiseJointPDF f g) = f :=
  funext fun x => integral_noiseJointPDF_right hg x

omit [MeasurableAdd G] [ν.IsAddRightInvariant] in
/-- The integrals of `f(x) g(y - x) h(x, y)` over `μ × ν`, for `h ≥ 0`, computed by integrating
over `y` first. -/
lemma integral_noiseJointPDF_mul {f g : G → ℝ} (hf : IsPDF μ f) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {h : G × G → ℝ} (hh : Measurable h) (hnn : ∀ z, 0 ≤ h z) {k : G → ℝ}
    (hk : ∀ x, Integrable (fun y => g (y - x) * h (x, y)) ν ∧
      ∫ y, g (y - x) * h (x, y) ∂ν = k x)
    (hfk : Integrable (fun x => f x * k x) μ) :
    Integrable (fun z => noiseJointPDF f g z * h z) (μ.prod ν) ∧
      ∫ z, noiseJointPDF f g z * h z ∂(μ.prod ν) = ∫ x, f x * k x ∂μ := by
  have hm : Measurable fun z => noiseJointPDF f g z * h z :=
    (measurable_noiseJointPDF hf.measurable hg).mul hh
  have hrow : ∀ x, ∫ y, noiseJointPDF f g (x, y) * h (x, y) ∂ν = f x * k x := by
    intro x
    simp only [noiseJointPDF]
    rw [← (hk x).2, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have hint : Integrable (fun z => noiseJointPDF f g z * h z) (μ.prod ν) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact ((hk x).1.const_mul (f x)).congr (Eventually.of_forall fun y => by
        simp only [noiseJointPDF]; ring)
    · refine hfk.congr (Eventually.of_forall fun x => ?_)
      have : ∀ y, ‖noiseJointPDF f g (x, y) * h (x, y)‖ = noiseJointPDF f g (x, y) * h (x, y) :=
        fun y => Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hf.nonneg _) (hg0 _)) (hnn _))
      simp only [this, hrow]
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  exact integral_congr_ae (Eventually.of_forall fun x => hrow x)

/-! ### Bounding the mutual information -/

omit [MeasurableAdd G] [MeasurableSub₂ G] [SigmaFinite μ] [SigmaFinite ν]
  [ν.IsAddRightInvariant] in
/-- Pointwise decomposition of the integrand of `I(X; Y)`: where the output density `f_Y` is
positive, `log (f(x, y)/(f(x) f_Y(y))) = log (g(y - x)/q(y)) - log (f_Y(y)/q(y))`. -/
lemma noiseJointPDF_mul_log_eq {f g q : G → ℝ} (hgpos : ∀ x, 0 < g x) (hqpos : ∀ y, 0 < q y)
    {x y : G} (hY : marginalSnd μ (noiseJointPDF f g) y = 0 → noiseJointPDF f g (x, y) = 0) :
    noiseJointPDF f g (x, y) *
        log (noiseJointPDF f g (x, y) / (f x * marginalSnd μ (noiseJointPDF f g) y)) =
      noiseJointPDF f g (x, y) * log (g (y - x) / q y) -
        noiseJointPDF f g (x, y) * log (marginalSnd μ (noiseJointPDF f g) y / q y) := by
  set J := noiseJointPDF f g (x, y)
  set fY := marginalSnd μ (noiseJointPDF f g) y
  rcases eq_or_ne J 0 with hJ | hJ
  · simp [hJ]
  have hfx : f x ≠ 0 := fun h => hJ (by simp [J, noiseJointPDF, h])
  have hfY : fY ≠ 0 := fun h => hJ (hY h)
  have hg := (hgpos (y - x)).ne'
  have hq := (hqpos y).ne'
  have e : J / (f x * fY) = g (y - x) / fY := by
    simp only [J, noiseJointPDF]
    field_simp
  rw [e, ← mul_sub, log_div hg hfY, log_div hg hq, log_div hfY hq]
  ring

/-- **Bounding the mutual information of an additive noise channel.** For every positive
density `q` of the output space,
`I(X; Y) ≤ ∫ f(x) g(y - x) log (g(y - x)/q(y)) = D(f(x) g(y - x) ‖ f(x) q(y))`. The difference is
`D(f_Y ‖ q) ≥ 0`, where `f_Y` is the density of the output. -/
theorem mutualInfoPDF_noiseJointPDF_le {f g q : G → ℝ} (hf : IsPDF μ f) (hg : IsPDF ν g)
    (hgpos : ∀ x, 0 < g x) (hq : IsPDF ν q) (hqpos : ∀ y, 0 < q y)
    (hint : Integrable (fun z => noiseJointPDF f g z * log (g (z.2 - z.1) / q z.2)) (μ.prod ν)) :
    mutualInfoPDF μ ν (noiseJointPDF f g) ≤
      ∫ z, noiseJointPDF f g z * log (g (z.2 - z.1) / q z.2) ∂(μ.prod ν) := by
  have hJ := noiseJointPDF_isPDF hf hg
  set J := noiseJointPDF f g
  set fY := marginalSnd μ J
  have hfY : IsPDF ν fY := hJ.marginalSnd
  -- The right side is the relative entropy `D(J ‖ f ⊗ q) ≥ 0`.
  have hG : ∫ z, J z * log (g (z.2 - z.1) / q z.2) ∂(μ.prod ν) =
      relEntropyPDF (μ.prod ν) J fun z => f z.1 * q z.2 := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    rcases eq_or_ne (f z.1) 0 with h0 | h0
    · simp [J, noiseJointPDF, h0]
    · simp only [J, noiseJointPDF]
      congr 2
      field_simp
  have hGnn : 0 ≤ ∫ z, J z * log (g (z.2 - z.1) / q z.2) ∂(μ.prod ν) := by
    rw [hG]
    refine relEntropyPDF_nonneg' hJ (hf.mul_prod hq) (Eventually.of_forall fun z hz => ?_)
    rcases mul_eq_zero.1 hz with h | h
    · simp [J, noiseJointPDF, h]
    · exact absurd h (hqpos _).ne'
  -- The integrand of `I(X; Y)` is `G - H`, with `H(x, y) = J(x, y) log (f_Y(y)/q(y))`.
  have hdec : (fun z => J z * log (J z / (marginalFst ν J z.1 * fY z.2))) =ᵐ[μ.prod ν]
      fun z => J z * log (g (z.2 - z.1) / q z.2) - J z * log (fY z.2 / q z.2) := by
    filter_upwards [ae_marginalSnd_eq_zero hJ] with z hz
    rw [marginalFst_noiseJointPDF hg]
    exact noiseJointPDF_mul_log_eq hgpos hqpos hz
  by_cases hF : Integrable (fun z => J z * log (J z / (marginalFst ν J z.1 * fY z.2))) (μ.prod ν)
  · -- `H = G - F` is integrable, and `∫ H = D(f_Y ‖ q) ≥ 0`.
    have hH : Integrable (fun z => J z * log (fY z.2 / q z.2)) (μ.prod ν) :=
      (hint.sub hF).congr (hdec.mono fun z hz => by
        simp only [Pi.sub_apply] at hz ⊢
        rw [hz]
        ring)
    have hHint : ∫ z, J z * log (fY z.2 / q z.2) ∂(μ.prod ν) =
        ∫ y, fY y * log (fY y / q y) ∂ν := by
      rw [integral_prod_symm _ hH]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      change ∫ x, J (x, y) * log (fY y / q y) ∂μ = fY y * log (fY y / q y)
      exact integral_mul_const _ _
    have hHnn : 0 ≤ ∫ z, J z * log (fY z.2 / q z.2) ∂(μ.prod ν) := by
      rw [hHint]
      refine relEntropyPDF_nonneg hfY hq (Eventually.of_forall fun y hy => absurd hy
        (hqpos y).ne') ?_
      refine hH.integral_prod_right.congr (Eventually.of_forall fun y => ?_)
      change ∫ x, J (x, y) * log (fY y / q y) ∂μ = fY y * log (fY y / q y)
      exact integral_mul_const _ _
    rw [mutualInfoPDF, integral_congr_ae hdec, integral_sub hint hH]
    linarith
  · rw [mutualInfoPDF, integral_undef hF]
    exact hGnn

/-- **Equality in the bound.** If `q` is the density of the output, then
`I(X; Y) = ∫ f(x) g(y - x) log (g(y - x)/q(y))`. -/
theorem mutualInfoPDF_noiseJointPDF_eq {f g q : G → ℝ} (hf : IsPDF μ f) (hg : IsPDF ν g)
    (hgpos : ∀ x, 0 < g x) (hqpos : ∀ y, 0 < q y)
    (hout : ∀ y, marginalSnd μ (noiseJointPDF f g) y = q y) :
    mutualInfoPDF μ ν (noiseJointPDF f g) =
      ∫ z, noiseJointPDF f g z * log (g (z.2 - z.1) / q z.2) ∂(μ.prod ν) := by
  have hJ := noiseJointPDF_isPDF hf hg
  refine integral_congr_ae ?_
  filter_upwards [ae_marginalSnd_eq_zero hJ] with z hz
  rw [marginalFst_noiseJointPDF hg, noiseJointPDF_mul_log_eq hgpos hqpos hz, hout,
    div_self (hqpos _).ne', log_one, mul_zero, sub_zero]

end InfoTheory
