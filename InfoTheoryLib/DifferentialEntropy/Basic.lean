/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.Integral

/-!
# Differential entropy

A continuous random variable `X` with values in a measure space `(α, μ)` (for instance `ℝ` or
`ℝⁿ` with Lebesgue measure) has a probability density `f` if its law is `f dμ`. Its differential
entropy is `h(X) = h(f) = -∫ f log f dμ`. Unlike the entropy of a discrete random variable it can
be negative, and it depends on the reference measure `μ`.

## Main definitions

* `IsPDF μ f`: `f` is a probability density function with respect to `μ`.
* `pdfMeasure μ f`: the law `f dμ` of a random variable with density `f`.
* `diffEntropy μ f`: the differential entropy `h(f) = -∫ f log f dμ`, (8.1).
* `uniformPDF a b`: the uniform density on `[a, b]`.

## Main statements

* `diffEntropy_eq_setIntegral_support`: (8.1), the integral over the support set of `f`.
* `diffEntropy_uniformPDF`: the uniform density on `[a, b]` has `h = log (b - a)` (Example 8.1.1).
* `diffEntropy_comp_sub`, `pdfMeasure_map_add`: Theorem 8.6.3, `h(X + c) = h(X)`.
* `diffEntropy_scale`, `pdfMeasure_map_mul`: Theorem 8.6.4, `h(aX) = h(X) + log |a|`.
* `diffEntropy_linearEquiv`: Corollary (8.71), `h(AX) = h(X) + log |det A|`.

## Implementation notes

Densities are real-valued, measurable and pointwise non-negative. The differential entropy is a
Bochner integral, which is `0` when `f log f` is not integrable, so results about it carry the
hypothesis that `f log f` is integrable: the book's "if it exists". Logarithms are natural, so
differential entropies are in nats.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 8.1 and
  8.6
-/

open Real MeasureTheory Set

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Definition (Section 8.1).** `f` is a probability density function with respect to `μ`: it is
measurable, non-negative and integrable with `∫ f dμ = 1`. -/
structure IsPDF (μ : Measure α) (f : α → ℝ) : Prop where
  measurable : Measurable f
  nonneg : ∀ x, 0 ≤ f x
  integrable : Integrable f μ
  integral_eq_one : ∫ x, f x ∂μ = 1

/-- The law `f dμ` of a random variable with density `f` with respect to `μ`. -/
def pdfMeasure (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity fun x => ENNReal.ofReal (f x)

lemma IsPDF.isProbabilityMeasure {μ : Measure α} {f : α → ℝ} (hf : IsPDF μ f) :
    IsProbabilityMeasure (pdfMeasure μ f) := by
  constructor
  rw [pdfMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrable (Filter.Eventually.of_forall hf.nonneg),
    hf.integral_eq_one, ENNReal.ofReal_one]

/-- The probability `Pr{X ∈ s} = ∫_s f dμ` of a measurable set under the density `f`. -/
lemma pdfMeasure_apply {μ : Measure α} {f : α → ℝ} (hf : IsPDF μ f) {s : Set α}
    (hs : MeasurableSet s) : (pdfMeasure μ f s).toReal = ∫ x in s, f x ∂μ := by
  rw [pdfMeasure, withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal
    hf.integrable.integrableOn (Filter.Eventually.of_forall hf.nonneg),
    ENNReal.toReal_ofReal (setIntegral_nonneg hs fun x _ => hf.nonneg x)]

/-- The integral of `g` against the law with density `f` is `∫ f g dμ`. -/
lemma integral_pdfMeasure {μ : Measure α} {f : α → ℝ} (hf : IsPDF μ f) (g : α → ℝ) :
    ∫ x, g x ∂pdfMeasure μ f = ∫ x, f x * g x ∂μ := by
  rw [pdfMeasure, integral_withDensity_eq_integral_toReal_smul
    (hf.measurable.ennreal_ofReal) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [ENNReal.toReal_ofReal (hf.nonneg _)]

/-- **Definition (8.1).** The differential entropy `h(f) = -∫ f log f dμ` of a density `f`. -/
def diffEntropy (μ : Measure α) (f : α → ℝ) : ℝ := ∫ x, negMulLog (f x) ∂μ

/-- **(8.1)** The differential entropy is the integral over the support set `S = {f > 0}`:
`h(f) = -∫_S f log f dμ`. -/
lemma diffEntropy_eq_setIntegral_support {μ : Measure α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    diffEntropy μ f = -∫ x in {x | 0 < f x}, f x * log (f x) ∂μ := by
  rw [← integral_neg, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
  · simp [diffEntropy, negMulLog]
  · simp only [mem_ofPred_eq, not_lt] at hx
    simp [le_antisymm hx (hf x)]

lemma diffEntropy_congr_ae {μ : Measure α} {f g : α → ℝ} (h : f =ᵐ[μ] g) :
    diffEntropy μ f = diffEntropy μ g :=
  integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-! ### The uniform distribution -/

/-- The uniform density `1/(b - a)` on the interval `[a, b]`. -/
def uniformPDF (a b : ℝ) : ℝ → ℝ := indicator (Icc a b) fun _ => 1 / (b - a)

lemma uniformPDF_isPDF {a b : ℝ} (hab : a < b) : IsPDF volume (uniformPDF a b) := by
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨measurable_const.indicator measurableSet_Icc, fun x => ?_, ?_, ?_⟩
  · exact indicator_nonneg (fun _ _ => (one_div_pos.2 hba).le) x
  · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  · rw [uniformPDF, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le hab.le, smul_eq_mul]
    field_simp

/-- **Example 8.1.1 (Uniform distribution), (8.2).** The uniform density on `[a, b]` has
differential entropy `h = log (b - a)`. In particular for `b - a < 1` it is negative, but
`e^{h} = b - a` is the volume of the support set. -/
theorem diffEntropy_uniformPDF {a b : ℝ} (hab : a < b) :
    diffEntropy volume (uniformPDF a b) = log (b - a) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h : (fun x => negMulLog (uniformPDF a b x)) =
      indicator (Icc a b) fun _ => negMulLog (1 / (b - a)) := by
    funext x
    simp only [uniformPDF, indicator]
    split_ifs <;> simp
  rw [diffEntropy, h, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le hab.le, smul_eq_mul, negMulLog, one_div, log_inv]
  field_simp

/-! ### Change of variables -/

/-- The law of `e(X)` for a measurable equivalence `e`: `(f dμ) ∘ e⁻¹ = (f ∘ e⁻¹) d(μ ∘ e⁻¹)`. -/
lemma map_withDensity_measurableEquiv {β : Type*} [MeasurableSpace β] (μ : Measure α)
    (e : α ≃ᵐ β) (g : α → ENNReal) :
    (μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map, lintegral_map_equiv]
  simp

variable {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]

/-- **Theorem 8.6.3**, the density: if `X` has density `f`, then `X + c` has density
`f(x - c)`. -/
theorem pdfMeasure_map_add (μ : Measure G) [μ.IsAddRightInvariant] (f : G → ℝ) (c : G) :
    (pdfMeasure μ f).map (· + c) = pdfMeasure μ fun x => f (x - c) := by
  have h := map_withDensity_measurableEquiv μ (MeasurableEquiv.addRight c)
    fun x => ENNReal.ofReal (f x)
  have hm : μ.map (MeasurableEquiv.addRight c) = μ := map_add_right_eq_self μ c
  rw [hm] at h
  change (pdfMeasure μ f).map (MeasurableEquiv.addRight c) = _
  rw [pdfMeasure, h, pdfMeasure]
  congr 1
  funext x
  simp [sub_eq_add_neg]

/-- **Theorem 8.6.3, (8.65).** Translation does not change the differential entropy:
`h(X + c) = h(X)`, where `X + c` has density `f(x - c)`. -/
theorem diffEntropy_comp_sub (μ : Measure G) [μ.IsAddRightInvariant] (f : G → ℝ) (c : G) :
    diffEntropy μ (fun x => f (x - c)) = diffEntropy μ f :=
  integral_sub_right_eq_self (fun x => negMulLog (f x)) c

/-- **Theorem 8.6.4**, the density, (8.67): if `X` has density `f` and `a ≠ 0`, then `aX` has
density `f(y/a)/|a|`. -/
theorem pdfMeasure_map_mul (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) :
    (pdfMeasure volume f).map (a * ·) = pdfMeasure volume fun y => |a|⁻¹ * f (y / a) := by
  have h := map_withDensity_measurableEquiv volume (MeasurableEquiv.mulLeft₀ a ha)
    fun x => ENNReal.ofReal (f x)
  have hm : (volume : Measure ℝ).map (MeasurableEquiv.mulLeft₀ a ha) =
      ENNReal.ofReal |a⁻¹| • volume := Real.map_volume_mul_left ha
  rw [hm, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top] at h
  change (pdfMeasure volume f).map (MeasurableEquiv.mulLeft₀ a ha) = _
  rw [pdfMeasure, h, pdfMeasure]
  congr 1
  funext y
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, div_eq_inv_mul]
  rfl

/-- `negMulLog (c t) = t · c log (1/c) + c · negMulLog t`, rearranged for `c = 1/s`. -/
lemma negMulLog_inv_mul (s t : ℝ) :
    negMulLog (s⁻¹ * t) = s⁻¹ * (t * log s + negMulLog t) := by
  rw [negMulLog_mul, negMulLog, log_inv]
  ring

/-- **Theorem 8.6.4, (8.66)–(8.70).** Scaling by `a ≠ 0` adds `log |a|` to the differential
entropy: `h(aX) = h(X) + log |a|`, where `aX` has density `f(y/a)/|a|`. -/
theorem diffEntropy_scale {f : ℝ → ℝ} (hf : IsPDF volume f)
    (hint : Integrable (fun x => negMulLog (f x))) {a : ℝ} (ha : a ≠ 0) :
    diffEntropy volume (fun y => |a|⁻¹ * f (y / a)) = diffEntropy volume f + log |a| := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have h := Measure.integral_comp_inv_mul_left (fun t => negMulLog (|a|⁻¹ * f t)) a
  simp only [smul_eq_mul] at h
  rw [diffEntropy, show (fun y => negMulLog (|a|⁻¹ * f (y / a))) =
    fun y => negMulLog (|a|⁻¹ * f (a⁻¹ * y)) from funext fun y => by rw [div_eq_inv_mul], h]
  simp only [negMulLog_inv_mul]
  rw [integral_const_mul, integral_add (hf.integrable.mul_const _) hint, integral_mul_const,
    hf.integral_eq_one, diffEntropy]
  field_simp
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- **Corollary (8.71).** For a linear equivalence `A` of a finite-dimensional space with an
additive Haar measure, `h(AX) = h(X) + log |det A|`, where `AX` has density
`f(A⁻¹ y)/|det A|`. -/
theorem diffEntropy_linearEquiv (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : IsPDF μ f) (hint : Integrable (fun x => negMulLog (f x)) μ) (A : E ≃ₗ[ℝ] E) :
    diffEntropy μ (fun y => |LinearMap.det (A : E →ₗ[ℝ] E)|⁻¹ * f (A.symm y)) =
      diffEntropy μ f + log |LinearMap.det (A : E →ₗ[ℝ] E)| := by
  set d := LinearMap.det (A : E →ₗ[ℝ] E)
  have hd : 0 < |d| := abs_pos.2 A.isUnit_det'.ne_zero
  have hdet : LinearMap.det (A.symm : E →ₗ[ℝ] E) = d⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← LinearMap.det_comp]
    simp
  have h := integral_comp_linearEquiv μ A.symm fun t => negMulLog (|d|⁻¹ * f t)
  rw [hdet, abs_inv, inv_inv] at h
  rw [diffEntropy, h]
  simp only [negMulLog_inv_mul]
  rw [integral_const_mul, integral_add (hf.integrable.mul_const _) hint, integral_mul_const,
    hf.integral_eq_one, diffEntropy]
  field_simp
  ring

end InfoTheory
