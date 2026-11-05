/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.RelativeEntropy

/-!
# Joint and conditional differential entropy, mutual information

A pair `(X, Y)` with values in `α × β` has a joint density `f(x, y)` with respect to `μ × ν`, with
marginal densities `f(x) = ∫ f(x, y) dν(y)` and `f(y) = ∫ f(x, y) dμ(x)`. The joint differential
entropy is `h(X, Y) = h(f)`, the conditional differential entropy is
`h(X|Y) = -∫ f(x, y) log f(x|y)`, with `f(x|y) = f(x, y)/f(y)`, and the mutual information is
`I(X; Y) = ∫ f(x, y) log (f(x, y)/(f(x) f(y)))`.

## Main definitions

* `marginalFst ν f`, `marginalSnd μ f`: the marginal densities `f(x)` and `f(y)`.
* `condDiffEntropy μ ν f`: the conditional differential entropy `h(X|Y)`, (8.32).
* `mutualInfoPDF μ ν f`: the mutual information `I(X; Y)`, (8.47).

## Main statements

* `ae_marginalSnd_eq_zero`, `ae_marginalFst_eq_zero`: almost everywhere, `f(x, y) = 0` where a
  marginal vanishes.
* `condDiffEntropy_eq`: (8.33), `h(X|Y) = h(X, Y) - h(Y)`.
* `mutualInfoPDF_eq_relEntropyPDF`: (8.49), `I(X; Y) = D(f(x, y) ‖ f(x) f(y))`.
* `mutualInfoPDF_eq_add_sub`, `mutualInfoPDF_eq_sub_condDiffEntropy`,
  `mutualInfoPDF_eq_sub_condDiffEntropy'`: (8.48).
* `mutualInfoPDF_nonneg`, `mutualInfoPDF_eq_zero_iff`: Corollary of Theorem 8.6.1, `I(X; Y) ≥ 0`
  with equality iff `X` and `Y` are independent.
* `condDiffEntropy_le`, `condDiffEntropy_eq_iff`: Corollary of Theorem 8.6.1, `h(X|Y) ≤ h(X)`
  with equality iff `X` and `Y` are independent.
* `mutualInfoPDF_comp_prodMap`: `I(X; Y)` is invariant under measure-preserving changes of
  variables of `X` and `Y`.
* `mutualInfoPDF_swap`: `I(Y; X) = I(X; Y)`.

## Implementation notes

The book notes that (8.33) needs care when the differential entropies are infinite. The results
assume that `f log f` and the corresponding expressions for the marginals are integrable.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 8.4–8.6
-/

open Real MeasureTheory Filter Set

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SigmaFinite μ] [SigmaFinite ν]

/-- The marginal density `f(x) = ∫ f(x, y) dν(y)` of the first coordinate. -/
def marginalFst (ν : Measure β) (f : α × β → ℝ) (x : α) : ℝ := ∫ y, f (x, y) ∂ν

/-- The marginal density `f(y) = ∫ f(x, y) dμ(x)` of the second coordinate. -/
def marginalSnd (μ : Measure α) (f : α × β → ℝ) (y : β) : ℝ := ∫ x, f (x, y) ∂μ

lemma IsPDF.marginalFst {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    IsPDF μ (marginalFst ν f) :=
  ⟨(hf.measurable.stronglyMeasurable.integral_prod_right').measurable,
    fun _ => integral_nonneg fun _ => hf.nonneg _, hf.integrable.integral_prod_left, by
      change ∫ x, ∫ y, f (x, y) ∂ν ∂μ = 1
      rw [← integral_prod f hf.integrable, hf.integral_eq_one]⟩

lemma IsPDF.marginalSnd {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    IsPDF ν (marginalSnd μ f) :=
  ⟨(hf.measurable.stronglyMeasurable.integral_prod_left').measurable,
    fun _ => integral_nonneg fun _ => hf.nonneg _, hf.integrable.integral_prod_right, by
      change ∫ y, ∫ x, f (x, y) ∂μ ∂ν = 1
      rw [← integral_prod_symm f hf.integrable, hf.integral_eq_one]⟩

/-- The density `f(y, x)` of the pair `(Y, X)`. -/
lemma IsPDF.swap {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) : IsPDF (ν.prod μ) (f ∘ Prod.swap) :=
  ⟨hf.measurable.comp measurable_swap, fun _ => hf.nonneg _, hf.integrable.swap,
    by rw [← hf.integral_eq_one]; exact integral_prod_swap f⟩

omit [MeasurableSpace α] [SigmaFinite μ] [SigmaFinite ν] in
lemma marginalSnd_swap (f : α × β → ℝ) : marginalSnd ν (f ∘ Prod.swap) = marginalFst ν f := rfl

omit [MeasurableSpace β] [SigmaFinite μ] [SigmaFinite ν] in
lemma marginalFst_swap (f : α × β → ℝ) : marginalFst μ (f ∘ Prod.swap) = marginalSnd μ f := rfl

lemma diffEntropy_swap (f : α × β → ℝ) :
    diffEntropy (ν.prod μ) (f ∘ Prod.swap) = diffEntropy (μ.prod ν) f :=
  integral_prod_swap fun z => negMulLog (f z)

/-- Almost everywhere, `f(x, y) = 0` wherever the marginal `f(y)` vanishes. -/
lemma ae_marginalSnd_eq_zero {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    ∀ᵐ z ∂(μ.prod ν), marginalSnd μ f z.2 = 0 → f z = 0 := by
  set Z := {y | marginalSnd μ f y = 0}
  have hZ : MeasurableSet Z := hf.marginalSnd.measurable (measurableSet_singleton 0)
  have hS : MeasurableSet (Prod.snd ⁻¹' Z : Set (α × β)) := measurable_snd hZ
  set g := (Prod.snd ⁻¹' Z).indicator f
  have hg : Integrable g (μ.prod ν) := hf.integrable.indicator hS
  have hg0 : 0 ≤ᵐ[μ.prod ν] g :=
    Eventually.of_forall fun z => indicator_nonneg (fun z _ => hf.nonneg z) z
  have hint : ∫ z, g z ∂(μ.prod ν) = 0 := by
    rw [integral_prod_symm g hg]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Z
    · have e : ∀ x, g (x, y) = f (x, y) := fun x =>
        indicator_of_mem (show (x, y) ∈ (Prod.snd ⁻¹' Z : Set (α × β)) from hy) f
      simp_rw [e]
      exact hy
    · have e : ∀ x, g (x, y) = 0 := fun x =>
        indicator_of_notMem (show (x, y) ∉ (Prod.snd ⁻¹' Z : Set (α × β)) from hy) f
      simp_rw [e]
      simp
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hg0 hg).1 hint] with z hz hz2
  have hmem : z ∈ (Prod.snd ⁻¹' Z : Set (α × β)) := hz2
  simpa [g, indicator, hmem] using hz

/-- Almost everywhere, `f(x, y) = 0` wherever the marginal `f(x)` vanishes. -/
lemma ae_marginalFst_eq_zero {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    ∀ᵐ z ∂(μ.prod ν), marginalFst ν f z.1 = 0 → f z = 0 := by
  have h := ae_marginalSnd_eq_zero hf.swap
  rw [marginalSnd_swap] at h
  have h' := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).quasiMeasurePreserving.ae h
  simpa using h'

/-- `∫ f(x, y) G(y) d(x, y) = ∫ f(y) G(y) dy` when `f(y) G(y)` is integrable. -/
lemma integral_mul_comp_snd {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) {G : β → ℝ}
    (hG : Measurable G) (hint : Integrable (fun y => marginalSnd μ f y * G y) ν) :
    Integrable (fun z => f z * G z.2) (μ.prod ν) ∧
      ∫ z, f z * G z.2 ∂(μ.prod ν) = ∫ y, marginalSnd μ f y * G y ∂ν := by
  have hmeas : AEStronglyMeasurable (fun z : α × β => f z * G z.2) (μ.prod ν) :=
    (hf.measurable.mul (hG.comp measurable_snd)).aestronglyMeasurable
  have hInt : Integrable (fun z => f z * G z.2) (μ.prod ν) := by
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [hf.integrable.prod_left_ae] with y hy
      exact hy.mul_const (G y)
    · refine hint.norm.congr (Eventually.of_forall fun y => ?_)
      change ‖marginalSnd μ f y * G y‖ = ∫ x, ‖f (x, y) * G y‖ ∂μ
      calc ‖marginalSnd μ f y * G y‖ = (∫ x, f (x, y) ∂μ) * |G y| := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, marginalSnd,
              abs_of_nonneg (integral_nonneg fun x => hf.nonneg _)]
        _ = ∫ x, f (x, y) * |G y| ∂μ := (integral_mul_const _ _).symm
        _ = ∫ x, ‖f (x, y) * G y‖ ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            simp [norm_mul, abs_of_nonneg (hf.nonneg (x, y))]
  refine ⟨hInt, ?_⟩
  rw [integral_prod_symm _ hInt]
  exact integral_congr_ae (Eventually.of_forall fun y =>
    (integral_mul_const (G y) fun x => f (x, y) : _))

/-- `∫ f(x, y) G(x) d(x, y) = ∫ f(x) G(x) dx` when `f(x) G(x)` is integrable. -/
lemma integral_mul_comp_fst {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) {G : α → ℝ}
    (hG : Measurable G) (hint : Integrable (fun x => marginalFst ν f x * G x) μ) :
    Integrable (fun z => f z * G z.1) (μ.prod ν) ∧
      ∫ z, f z * G z.1 ∂(μ.prod ν) = ∫ x, marginalFst ν f x * G x ∂μ := by
  have h := integral_mul_comp_snd hf.swap hG (by rwa [marginalSnd_swap])
  rw [marginalSnd_swap] at h
  refine ⟨?_, ?_⟩
  · have := h.1.swap
    exact this
  · rw [← h.2]
    exact (integral_prod_swap fun z => f z * G z.1).symm

/-- `∫ f(x, y) log f(y) = -h(Y)`. -/
lemma integral_mul_log_marginalSnd {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    Integrable (fun z => f z * log (marginalSnd μ f z.2)) (μ.prod ν) ∧
      ∫ z, f z * log (marginalSnd μ f z.2) ∂(μ.prod ν) = -diffEntropy ν (marginalSnd μ f) := by
  have hint : Integrable (fun y => marginalSnd μ f y * log (marginalSnd μ f y)) ν :=
    hY.neg.congr (Eventually.of_forall fun y => by simp [negMulLog])
  obtain ⟨h1, h2⟩ := integral_mul_comp_snd hf (G := fun y => log (marginalSnd μ f y))
    (measurable_log.comp hf.marginalSnd.measurable) hint
  refine ⟨h1, ?_⟩
  rw [h2, diffEntropy, ← integral_neg]
  simp [negMulLog]

/-- `∫ f(x, y) log f(x) = -h(X)`. -/
lemma integral_mul_log_marginalFst {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ) :
    Integrable (fun z => f z * log (marginalFst ν f z.1)) (μ.prod ν) ∧
      ∫ z, f z * log (marginalFst ν f z.1) ∂(μ.prod ν) = -diffEntropy μ (marginalFst ν f) := by
  have hint : Integrable (fun x => marginalFst ν f x * log (marginalFst ν f x)) μ :=
    hX.neg.congr (Eventually.of_forall fun x => by simp [negMulLog])
  obtain ⟨h1, h2⟩ := integral_mul_comp_fst hf (G := fun x => log (marginalFst ν f x))
    (measurable_log.comp hf.marginalFst.measurable) hint
  refine ⟨h1, ?_⟩
  rw [h2, diffEntropy, ← integral_neg]
  simp [negMulLog]

/-! ### Conditional differential entropy -/

/-- **Definition (8.32).** The conditional differential entropy
`h(X|Y) = -∫ f(x, y) log f(x|y)`, with the conditional density `f(x|y) = f(x, y)/f(y)`. -/
def condDiffEntropy (μ : Measure α) (ν : Measure β) (f : α × β → ℝ) : ℝ :=
  -∫ z, f z * log (f z / marginalSnd μ f z.2) ∂(μ.prod ν)

/-- **(8.33)** `h(X|Y) = h(X, Y) - h(Y)`, when the differential entropies are finite. -/
theorem condDiffEntropy_eq {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    condDiffEntropy μ ν f = diffEntropy (μ.prod ν) f - diffEntropy ν (marginalSnd μ f) := by
  obtain ⟨h1, h2⟩ := integral_mul_log_marginalSnd hf hY
  have hneg : Integrable (fun z => -negMulLog (f z)) (μ.prod ν) := hXY.neg
  rw [condDiffEntropy, integral_congr_ae ((ae_marginalSnd_eq_zero hf).mono fun z hz =>
    mul_log_div_eq hz), integral_sub hneg h1, integral_neg, h2]
  unfold diffEntropy
  ring

/-! ### Mutual information -/

/-- **Definition (8.47).** The mutual information `I(X; Y) = ∫ f(x, y) log (f(x, y)/(f(x) f(y)))`
between two random variables with joint density `f`. -/
def mutualInfoPDF (μ : Measure α) (ν : Measure β) (f : α × β → ℝ) : ℝ :=
  ∫ z, f z * log (f z / (marginalFst ν f z.1 * marginalSnd μ f z.2)) ∂(μ.prod ν)

omit [SigmaFinite μ] [SigmaFinite ν] in
/-- **(8.49)** `I(X; Y) = D(f(x, y) ‖ f(x) f(y))`. -/
lemma mutualInfoPDF_eq_relEntropyPDF (f : α × β → ℝ) :
    mutualInfoPDF μ ν f =
      relEntropyPDF (μ.prod ν) f fun z => marginalFst ν f z.1 * marginalSnd μ f z.2 := rfl

/-- The product of the marginal densities, the density of independent `X` and `Y`. -/
lemma IsPDF.prod_marginals {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    IsPDF (μ.prod ν) fun z => InfoTheory.marginalFst ν f z.1 * InfoTheory.marginalSnd μ f z.2 :=
  ⟨(hf.marginalFst.measurable.comp measurable_fst).mul
      (hf.marginalSnd.measurable.comp measurable_snd),
    fun z => mul_nonneg (hf.marginalFst.nonneg _) (hf.marginalSnd.nonneg _),
    hf.marginalFst.integrable.mul_prod hf.marginalSnd.integrable,
    by rw [integral_prod_mul, hf.marginalFst.integral_eq_one, hf.marginalSnd.integral_eq_one,
      one_mul]⟩

lemma ae_marginals_eq_zero {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    ∀ᵐ z ∂(μ.prod ν), marginalFst ν f z.1 * marginalSnd μ f z.2 = 0 → f z = 0 := by
  filter_upwards [ae_marginalFst_eq_zero hf, ae_marginalSnd_eq_zero hf] with z h1 h2 h
  rcases mul_eq_zero.1 h with h | h
  · exact h1 h
  · exact h2 h

/-- Pointwise decomposition of the integrand of `I(X; Y)`. -/
lemma mul_log_div_mul_eq {a b c : ℝ} (hb : b = 0 → a = 0) (hc : c = 0 → a = 0) :
    a * log (a / (b * c)) = -negMulLog a - a * log b - a * log c := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hb' : b ≠ 0 := fun h => ha (hb h)
    have hc' : c ≠ 0 := fun h => ha (hc h)
    rw [log_div ha (mul_ne_zero hb' hc'), log_mul hb' hc', negMulLog]
    ring

lemma mutualInfoPDF_integrand_ae {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f) :
    (fun z => f z * log (f z / (marginalFst ν f z.1 * marginalSnd μ f z.2))) =ᵐ[μ.prod ν]
      fun z => -negMulLog (f z) - f z * log (marginalFst ν f z.1) -
        f z * log (marginalSnd μ f z.2) := by
  filter_upwards [ae_marginalFst_eq_zero hf, ae_marginalSnd_eq_zero hf] with z h1 h2
  exact mul_log_div_mul_eq h1 h2

/-- **(8.48)** `I(X; Y) = h(X) + h(Y) - h(X, Y)`. -/
theorem mutualInfoPDF_eq_add_sub {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    mutualInfoPDF μ ν f =
      diffEntropy μ (marginalFst ν f) + diffEntropy ν (marginalSnd μ f) -
        diffEntropy (μ.prod ν) f := by
  obtain ⟨h1, h2⟩ := integral_mul_log_marginalFst hf hX
  obtain ⟨h3, h4⟩ := integral_mul_log_marginalSnd hf hY
  have hneg : Integrable (fun z => -negMulLog (f z)) (μ.prod ν) := hXY.neg
  have h13 : Integrable (fun z => -negMulLog (f z) - f z * log (marginalFst ν f z.1))
      (μ.prod ν) := hneg.sub h1
  rw [mutualInfoPDF, integral_congr_ae (mutualInfoPDF_integrand_ae hf),
    integral_sub h13 h3, integral_sub hneg h1, integral_neg, h2, h4]
  unfold diffEntropy
  ring

lemma integrable_mutualInfoPDF_integrand {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    Integrable (fun z => f z * log (f z / (marginalFst ν f z.1 * marginalSnd μ f z.2)))
      (μ.prod ν) :=
  ((hXY.neg.sub (integral_mul_log_marginalFst hf hX).1).sub
    (integral_mul_log_marginalSnd hf hY).1).congr (mutualInfoPDF_integrand_ae hf).symm

/-- **(8.48)** `I(X; Y) = h(X) - h(X|Y)`. -/
theorem mutualInfoPDF_eq_sub_condDiffEntropy {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    mutualInfoPDF μ ν f = diffEntropy μ (marginalFst ν f) - condDiffEntropy μ ν f := by
  rw [mutualInfoPDF_eq_add_sub hf hXY hX hY, condDiffEntropy_eq hf hXY hY]
  ring

/-- **(8.48)** `I(X; Y) = h(Y) - h(Y|X)`, where `h(Y|X)` is the conditional differential entropy
of the pair `(Y, X)` with density `f(y, x)`. -/
theorem mutualInfoPDF_eq_sub_condDiffEntropy' {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    mutualInfoPDF μ ν f =
      diffEntropy ν (marginalSnd μ f) - condDiffEntropy ν μ (f ∘ Prod.swap) := by
  have hXY' : Integrable (fun z => negMulLog ((f ∘ Prod.swap) z)) (ν.prod μ) := hXY.swap
  rw [mutualInfoPDF_eq_add_sub hf hXY hX hY, condDiffEntropy_eq hf.swap hXY' (by
    rwa [marginalSnd_swap]), marginalSnd_swap, diffEntropy_swap]
  ring

/-- **Corollary of Theorem 8.6.1.** `I(X; Y) ≥ 0`. -/
theorem mutualInfoPDF_nonneg {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    0 ≤ mutualInfoPDF μ ν f :=
  relEntropyPDF_nonneg hf hf.prod_marginals (ae_marginals_eq_zero hf)
    (integrable_mutualInfoPDF_integrand hf hXY hX hY)

/-- **Corollary of Theorem 8.6.1 (equality case).** `I(X; Y) = 0` iff `X` and `Y` are
independent: `f(x, y) = f(x) f(y)` almost everywhere. -/
theorem mutualInfoPDF_eq_zero_iff {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    mutualInfoPDF μ ν f = 0 ↔ f =ᵐ[μ.prod ν] fun z => marginalFst ν f z.1 * marginalSnd μ f z.2 :=
  relEntropyPDF_eq_zero_iff hf hf.prod_marginals (ae_marginals_eq_zero hf)
    (integrable_mutualInfoPDF_integrand hf hXY hX hY)

/-- **Corollary of Theorem 8.6.1.** Conditioning reduces differential entropy: `h(X|Y) ≤ h(X)`. -/
theorem condDiffEntropy_le {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    condDiffEntropy μ ν f ≤ diffEntropy μ (marginalFst ν f) := by
  have h := mutualInfoPDF_nonneg hf hXY hX hY
  rw [mutualInfoPDF_eq_sub_condDiffEntropy hf hXY hX hY] at h
  linarith

/-- **Corollary of Theorem 8.6.1 (equality case).** `h(X|Y) = h(X)` iff `X` and `Y` are
independent. -/
theorem condDiffEntropy_eq_iff {f : α × β → ℝ} (hf : IsPDF (μ.prod ν) f)
    (hXY : Integrable (fun z => negMulLog (f z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (marginalFst ν f x)) μ)
    (hY : Integrable (fun y => negMulLog (marginalSnd μ f y)) ν) :
    condDiffEntropy μ ν f = diffEntropy μ (marginalFst ν f) ↔
      f =ᵐ[μ.prod ν] fun z => marginalFst ν f z.1 * marginalSnd μ f z.2 := by
  rw [← mutualInfoPDF_eq_zero_iff hf hXY hX hY, mutualInfoPDF_eq_sub_condDiffEntropy hf hXY hX hY]
  constructor <;> intro h <;> linarith

/-! ### Changes of variables -/

/-- `I(Y; X) = I(X; Y)`: the pair `(Y, X)` has joint density `f(x, y)` at `(y, x)`. -/
theorem mutualInfoPDF_swap (f : α × β → ℝ) :
    mutualInfoPDF ν μ (f ∘ Prod.swap) = mutualInfoPDF μ ν f := by
  rw [mutualInfoPDF, mutualInfoPDF, marginalFst_swap, marginalSnd_swap,
    ← integral_prod_swap (μ := μ) (ν := ν)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [mul_comm]

/-- The integrand of `I(Y; X)` is integrable iff that of `I(X; Y)` is. -/
lemma integrable_mutualInfoPDF_integrand_swap {f : α × β → ℝ}
    (h : Integrable (fun z => f z * log (f z / (marginalFst ν f z.1 * marginalSnd μ f z.2)))
      (μ.prod ν)) :
    Integrable (fun z => (f ∘ Prod.swap) z * log ((f ∘ Prod.swap) z /
      (marginalFst μ (f ∘ Prod.swap) z.1 * marginalSnd ν (f ∘ Prod.swap) z.2))) (ν.prod μ) := by
  rw [marginalFst_swap, marginalSnd_swap]
  refine h.swap.congr (Eventually.of_forall fun z => ?_)
  simp [mul_comm]

/-- `I(X; Y)` is invariant under measure-preserving changes of variables `e₁` of `X` and `e₂` of
`Y`: the pair `(e₁⁻¹ X, e₂⁻¹ Y)` has joint density `f(e₁ x, e₂ y)`. -/
theorem mutualInfoPDF_comp_prodMap (e₁ : α ≃ᵐ α) (e₂ : β ≃ᵐ β) (h₁ : MeasurePreserving e₁ μ μ)
    (h₂ : MeasurePreserving e₂ ν ν) (f : α × β → ℝ) :
    mutualInfoPDF μ ν (fun z => f (e₁ z.1, e₂ z.2)) = mutualInfoPDF μ ν f := by
  have hX : ∀ x, marginalFst ν (fun z => f (e₁ z.1, e₂ z.2)) x = marginalFst ν f (e₁ x) :=
    fun x => h₂.integral_comp' (fun y => f (e₁ x, y))
  have hY : ∀ y, marginalSnd μ (fun z => f (e₁ z.1, e₂ z.2)) y = marginalSnd μ f (e₂ y) :=
    fun y => h₁.integral_comp' (fun x => f (x, e₂ y))
  have h := (h₁.prod h₂).integral_comp' (f := e₁.prodCongr e₂)
    (fun z => f z * log (f z / (marginalFst ν f z.1 * marginalSnd μ f z.2)))
  rw [mutualInfoPDF, mutualInfoPDF, ← h]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hX, hY]
  rfl

end InfoTheory
