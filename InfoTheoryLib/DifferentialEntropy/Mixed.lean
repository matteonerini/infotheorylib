/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.RelativeEntropy
public import InfoTheoryLib.Entropy.Basic

/-!
# Mixed pairs: a continuous variable related to an arbitrary one

Let `X` have an arbitrary law `μ` on any measurable space, and let `Y` be related to `X` through a
conditional density `f(y|x)` with respect to a reference measure `ν`, defined for all `x`. The joint
law of `(X, Y)` is `μ(dx) f(y|x) ν(dy)`. If `f(y|x)` is bounded, `Y` has the bounded density
`f(y) = ∫ f(y|x) μ(dx)`, whatever the law of `X`. This defines the conditional differential entropy
`h(Y|X)` and the mutual information `I(X; Y)` with no density for `X`, and `h(Y) = h(Y|X) + I(X; Y)`
with `I(X; Y) ≥ 0`.

## Main definitions

* `IsCondPDF ν k`: `k x` is a density with respect to `ν` for every `x`, measurably in `(x, y)`.
* `IsBoundedPDF f`, `IsBoundedCondPDF k`: Definitions 10.24 and 10.25.
* `jointLawOfCondPDF μ ν k`: the joint law of `(X, Y)`, (10.96).
* `outPDF μ k`: the density `f(y) = ∫ f(y|x) dF(x)` of `Y`, (10.100).
* `condDiffEntropyOfCondPDF μ ν k`: `h(Y|X)`, Definition 10.23.
* `mutualInfoOfCondPDF μ ν k`: `I(X; Y)`, Definition 10.28.
* `condMutualInfoOfCondPDF`: `I(X; Y|T)`, Definition 10.29.
* `condEntropyOfCondPDF`: `H(Y|X)` for a discrete `Y`, Definition 10.30.

## Main statements

* `map_fst_jointLawOfCondPDF`: `X` has law `μ`.
* `map_snd_jointLawOfCondPDF`, `isPDF_outPDF`, `isBoundedPDF_outPDF`: Propositions 10.26 and 10.27.
* `ae_ae_outPDF_eq_zero`: `f(y|x) = 0` almost everywhere where `f(y) = 0`.
* `diffEntropy_outPDF_eq_add`: Proposition 10.31, `h(Y) = h(Y|X) + I(X; Y)`.
* `mutualInfoOfCondPDF_nonneg`, `mutualInfoOfCondPDF_eq_zero_iff`: Theorem 10.33.
* `condMutualInfoOfCondPDF_nonneg`, `condMutualInfoOfCondPDF_eq_zero_iff`: Corollary 10.34.

## Implementation notes

The book's real random variables are replaced by any measurable spaces, with `ν` the Lebesgue
measure for a real `Y`; Proposition 10.27 for random vectors is then the same statement as
Proposition 10.26. Independence of `X` and `Y` is `f(y|x) = f(y)` for almost every `x` and `y`,
(10.147). Integrability conditions stand for the book's "assumed to be defined".

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 10.3
-/

open MeasureTheory Real Filter Set Function
open scoped ENNReal

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒳 𝒴 𝒯 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒯]
  {μ : Measure 𝒳} {ν : Measure 𝒴} {k : 𝒳 → 𝒴 → ℝ}

/-- **Definition 10.22.** `k` is a conditional density `f(y|x)` with respect to `ν`, defined for
all `x`. -/
structure IsCondPDF (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) : Prop where
  measurable : Measurable (uncurry k)
  isPDF : ∀ x, IsPDF ν (k x)

/-- **Definition 10.24.** A bounded density. -/
def IsBoundedPDF (f : 𝒴 → ℝ) : Prop := ∃ M, ∀ y, f y < M

/-- **Definition 10.25.** A bounded conditional density. -/
def IsBoundedCondPDF (k : 𝒳 → 𝒴 → ℝ) : Prop := ∃ M, ∀ x y, k x y < M

/-- **(10.96)** The joint law `μ(dx) f(y|x) ν(dy)` of `(X, Y)`. -/
def jointLawOfCondPDF (μ : Measure 𝒳) (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) : Measure (𝒳 × 𝒴) :=
  (μ.prod ν).withDensity fun z => ENNReal.ofReal (k z.1 z.2)

/-- **(10.100)** The density `f(y) = ∫ f(y|x) dF(x)` of `Y`. -/
def outPDF (μ : Measure 𝒳) (k : 𝒳 → 𝒴 → ℝ) (y : 𝒴) : ℝ := ∫ x, k x y ∂μ

lemma IsCondPDF.measurable_ofReal (hk : IsCondPDF ν k) :
    Measurable fun z : 𝒳 × 𝒴 => ENNReal.ofReal (k z.1 z.2) :=
  ENNReal.measurable_ofReal.comp hk.measurable

lemma IsCondPDF.lintegral_ofReal (hk : IsCondPDF ν k) (x : 𝒳) :
    ∫⁻ y, ENNReal.ofReal (k x y) ∂ν = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hk.isPDF x).integrable
    (ae_of_all _ (hk.isPDF x).nonneg), (hk.isPDF x).integral_eq_one, ENNReal.ofReal_one]

lemma jointLawOfCondPDF_prod [SFinite μ] [SFinite ν] (hk : IsCondPDF ν k) {A : Set 𝒳}
    {B : Set 𝒴} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    jointLawOfCondPDF μ ν k (A ×ˢ B) = ∫⁻ x in A, ∫⁻ y in B, ENNReal.ofReal (k x y) ∂ν ∂μ := by
  rw [jointLawOfCondPDF, withDensity_apply _ (hA.prod hB),
    setLIntegral_prod _ hk.measurable_ofReal.aemeasurable]

/-- The first marginal of the joint law is the law `μ` of `X`. -/
theorem map_fst_jointLawOfCondPDF [SFinite μ] [SFinite ν] (hk : IsCondPDF ν k) :
    (jointLawOfCondPDF μ ν k).map Prod.fst = μ := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, ← Set.prod_univ,
    jointLawOfCondPDF_prod hk hA MeasurableSet.univ]
  simp [Measure.restrict_univ, hk.lintegral_ofReal]

section Bounded

variable [IsProbabilityMeasure μ] [SFinite ν] (hk : IsCondPDF ν k) (hb : IsBoundedCondPDF k)
include hk hb

omit [SFinite ν] in
lemma integrable_section (y : 𝒴) : Integrable (fun x => k x y) μ := by
  obtain ⟨M, hM⟩ := hb
  refine Integrable.of_bound (hk.measurable.comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable M (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg ((hk.isPDF x).nonneg y)]
  exact (hM x y).le

/-- **Proposition 10.26, (10.101)–(10.119).** If `f(y|x)` is bounded, `Y` has the density
`f(y) = ∫ f(y|x) dF(x)`. -/
theorem map_snd_jointLawOfCondPDF :
    (jointLawOfCondPDF μ ν k).map Prod.snd = pdfMeasure ν (outPDF μ k) := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB, ← Set.univ_prod,
    jointLawOfCondPDF_prod hk MeasurableSet.univ hB, Measure.restrict_univ, pdfMeasure,
    withDensity_apply _ hB, lintegral_lintegral_swap (μ := μ) (ν := ν.restrict B)
      (f := fun x y => ENNReal.ofReal (k x y)) hk.measurable_ofReal.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [outPDF, ofReal_integral_eq_lintegral_ofReal (integrable_section hk hb y)
    (ae_of_all _ fun x => (hk.isPDF x).nonneg y)]

omit [SFinite ν] hb in
lemma measurable_outPDF : Measurable (outPDF μ k) :=
  (hk.measurable.stronglyMeasurable.integral_prod_left (f := k)).measurable

/-- **Proposition 10.26.** The density of `Y` is a density. -/
theorem isPDF_outPDF : IsPDF ν (outPDF μ k) := by
  have hnn : ∀ y, 0 ≤ outPDF μ k y := fun y => integral_nonneg fun x => (hk.isPDF x).nonneg y
  have hm := measurable_outPDF (μ := μ) hk
  have hone : ∫⁻ y, ENNReal.ofReal (outPDF μ k y) ∂ν = 1 := by
    have h := congrArg (fun m : Measure 𝒴 => m univ) (map_snd_jointLawOfCondPDF (μ := μ) hk hb)
    simp only [pdfMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    rw [← h, Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ]
    calc jointLawOfCondPDF μ ν k univ = (jointLawOfCondPDF μ ν k).map Prod.fst univ := by
          rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
      _ = 1 := by rw [map_fst_jointLawOfCondPDF hk, measure_univ]
  refine ⟨hm, hnn, ⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hone]
    exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hm.aestronglyMeasurable, hone,
      ENNReal.toReal_one]

omit [SFinite ν] in
/-- **Proposition 10.26.** The density of `Y` is bounded by the bound of `f(y|x)`. -/
theorem isBoundedPDF_outPDF : IsBoundedPDF (outPDF μ k) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M + 1, fun y => ?_⟩
  have : outPDF μ k y ≤ M := by
    calc outPDF μ k y ≤ ∫ _x, M ∂μ :=
          integral_mono (integrable_section hk ⟨M, hM⟩ y) (integrable_const M)
            fun x => (hM x y).le
      _ = M := by simp
  linarith

/-- Almost surely, `f(y|x) = 0` for almost every `y` with `f(y) = 0`: `f(·|x) ≪ f`. -/
theorem ae_ae_outPDF_eq_zero : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, outPDF μ k y = 0 → k x y = 0 := by
  set Z := {y | outPDF μ k y = 0}
  have hZ : MeasurableSet Z := measurable_outPDF (μ := μ) hk (measurableSet_singleton 0)
  set g : 𝒳 → 𝒴 → ℝ≥0∞ := fun x y => Z.indicator (fun y => ENNReal.ofReal (k x y)) y
  have hg : Measurable (uncurry g) :=
    Measurable.indicator hk.measurable_ofReal (measurable_snd hZ)
  have h₀ : ∫⁻ x, ∫⁻ y, g x y ∂ν ∂μ = 0 := by
    rw [lintegral_lintegral_swap hg.aemeasurable]
    have : ∀ y, ∫⁻ x, g x y ∂μ = 0 := by
      intro y
      by_cases hy : y ∈ Z
      · simp only [g, indicator_of_mem hy]
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_section hk hb y)
          (ae_of_all _ fun x => (hk.isPDF x).nonneg y)]
        rw [show ∫ x, k x y ∂μ = 0 from hy, ENNReal.ofReal_zero]
      · simp [g, indicator_of_notMem hy]
    simp [this]
  have h₁ := (lintegral_eq_zero_iff (Measurable.lintegral_prod_right' hg)).1 h₀
  filter_upwards [h₁] with x hx
  have h₂ := (lintegral_eq_zero_iff (hg.comp measurable_prodMk_left)).1 hx
  filter_upwards [h₂] with y hy hyZ
  have h₃ : ENNReal.ofReal (k x y) = 0 := by
    simpa [g, uncurry, indicator_of_mem (show y ∈ Z from hyZ)] using hy
  exact le_antisymm (ENNReal.ofReal_eq_zero.1 h₃) ((hk.isPDF x).nonneg y)

end Bounded

/-! ### Information measures -/

/-- **Definition 10.23, (10.99).** The conditional differential entropy
`h(Y|X) = ∫ h(Y|X = x) dF(x)`. -/
def condDiffEntropyOfCondPDF (μ : Measure 𝒳) (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) : ℝ :=
  ∫ x, diffEntropy ν (k x) ∂μ

/-- **Definition 10.28, (10.122).** The mutual information
`I(X; Y) = ∫∫ f(y|x) log (f(y|x)/f(y)) dy dF(x)`, the average of `D(f(·|x) ‖ f)`. -/
def mutualInfoOfCondPDF (μ : Measure 𝒳) (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) : ℝ :=
  ∫ x, relEntropyPDF ν (k x) (outPDF μ k) ∂μ

section Bounded

variable [IsProbabilityMeasure μ] [SFinite ν] (hk : IsCondPDF ν k) (hb : IsBoundedCondPDF k)
include hk hb

/-- **Theorem 10.33, (10.140)–(10.145).** `I(X; Y) ≥ 0`. -/
theorem mutualInfoOfCondPDF_nonneg
    (hint : ∀ᵐ x ∂μ, Integrable (fun y => k x y * log (k x y / outPDF μ k y)) ν) :
    0 ≤ mutualInfoOfCondPDF μ ν k := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_ae_outPDF_eq_zero hk hb, hint] with x hac hx
  exact relEntropyPDF_nonneg (hk.isPDF x) (isPDF_outPDF hk hb) hac hx

/-- **Theorem 10.33, (10.147).** `I(X; Y) = 0` iff `X` and `Y` are independent: `f(y|x) = f(y)` for
almost every `x` and `y`. -/
theorem mutualInfoOfCondPDF_eq_zero_iff
    (hint : ∀ᵐ x ∂μ, Integrable (fun y => k x y * log (k x y / outPDF μ k y)) ν)
    (hI : Integrable (fun x => relEntropyPDF ν (k x) (outPDF μ k)) μ) :
    mutualInfoOfCondPDF μ ν k = 0 ↔ ∀ᵐ x ∂μ, k x =ᵐ[ν] outPDF μ k := by
  have hnn : 0 ≤ᵐ[μ] fun x => relEntropyPDF ν (k x) (outPDF μ k) := by
    filter_upwards [ae_ae_outPDF_eq_zero hk hb, hint] with x hac hx
    exact relEntropyPDF_nonneg (hk.isPDF x) (isPDF_outPDF hk hb) hac hx
  rw [mutualInfoOfCondPDF, integral_eq_zero_iff_of_nonneg_ae hnn hI]
  refine eventually_congr ?_
  filter_upwards [ae_ae_outPDF_eq_zero hk hb, hint] with x hac hx
  exact relEntropyPDF_eq_zero_iff (hk.isPDF x) (isPDF_outPDF hk hb) hac hx

/-- **Proposition 10.31, (10.137).** `h(Y) = h(Y|X) + I(X; Y)`. -/
theorem diffEntropy_outPDF_eq_add
    (hent : ∀ᵐ x ∂μ, Integrable (fun y => negMulLog (k x y)) ν)
    (hlog : Integrable (uncurry fun x y => k x y * log (outPDF μ k y)) (μ.prod ν))
    (hh : Integrable (fun x => diffEntropy ν (k x)) μ) :
    diffEntropy ν (outPDF μ k) = condDiffEntropyOfCondPDF μ ν k + mutualInfoOfCondPDF μ ν k := by
  have hD : ∀ᵐ x ∂μ, relEntropyPDF ν (k x) (outPDF μ k) =
      -diffEntropy ν (k x) - ∫ y, k x y * log (outPDF μ k y) ∂ν := by
    filter_upwards [ae_ae_outPDF_eq_zero hk hb, hent, hlog.prod_right_ae] with x hac h₁ h₂
    exact relEntropyPDF_eq hac h₁ h₂
  have hI : mutualInfoOfCondPDF μ ν k =
      -condDiffEntropyOfCondPDF μ ν k - ∫ x, ∫ y, k x y * log (outPDF μ k y) ∂ν ∂μ := by
    have h₁ : Integrable (fun x => -diffEntropy ν (k x)) μ := hh.neg
    have h₂ : Integrable (fun x => ∫ y, k x y * log (outPDF μ k y) ∂ν) μ :=
      hlog.integral_prod_left
    rw [mutualInfoOfCondPDF, integral_congr_ae hD, integral_sub h₁ h₂, integral_neg,
      condDiffEntropyOfCondPDF]
  have hswap : ∫ x, ∫ y, k x y * log (outPDF μ k y) ∂ν ∂μ =
      ∫ y, outPDF μ k y * log (outPDF μ k y) ∂ν := by
    rw [integral_integral_swap hlog]
    exact integral_congr_ae (ae_of_all _ fun y => integral_mul_const _ _)
  have hh' : diffEntropy ν (outPDF μ k) = -∫ y, outPDF μ k y * log (outPDF μ k y) ∂ν := by
    rw [diffEntropy, ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun y => by simp [negMulLog])
  rw [hI, hswap, hh']
  ring

end Bounded

/-- **Definition 10.29, (10.125)–(10.126).** The conditional mutual information
`I(X; Y|T) = ∫ I(X; Y|T = t) dF(t)`, where given `T = t`, `X` has law `μ t` and `Y` has conditional
density `f(y|x, t) = k t x y`. -/
def condMutualInfoOfCondPDF (ρ : Measure 𝒯) (μ : 𝒯 → Measure 𝒳) (ν : Measure 𝒴)
    (k : 𝒯 → 𝒳 → 𝒴 → ℝ) : ℝ :=
  ∫ t, mutualInfoOfCondPDF (μ t) ν (k t) ∂ρ

section Conditional

variable {ρ : Measure 𝒯} {μ : 𝒯 → Measure 𝒳} [∀ t, IsProbabilityMeasure (μ t)] [SFinite ν]
  {k : 𝒯 → 𝒳 → 𝒴 → ℝ} (hk : ∀ t, IsCondPDF ν (k t)) (hb : ∀ t, IsBoundedCondPDF (k t))
  (hint : ∀ t, ∀ᵐ x ∂μ t, Integrable (fun y => k t x y * log (k t x y / outPDF (μ t) (k t) y)) ν)
include hk hb hint

/-- **Corollary 10.34, (10.149).** `I(X; Y|T) ≥ 0`. -/
theorem condMutualInfoOfCondPDF_nonneg : 0 ≤ condMutualInfoOfCondPDF ρ μ ν k :=
  integral_nonneg fun t => mutualInfoOfCondPDF_nonneg (hk t) (hb t) (hint t)

/-- **Corollary 10.34.** `I(X; Y|T) = 0` iff `X` and `Y` are independent given `T`. -/
theorem condMutualInfoOfCondPDF_eq_zero_iff
    (hI : ∀ t, Integrable (fun x => relEntropyPDF ν (k t x) (outPDF (μ t) (k t))) (μ t))
    (hIT : Integrable (fun t => mutualInfoOfCondPDF (μ t) ν (k t)) ρ) :
    condMutualInfoOfCondPDF ρ μ ν k = 0 ↔
      ∀ᵐ t ∂ρ, ∀ᵐ x ∂μ t, k t x =ᵐ[ν] outPDF (μ t) (k t) := by
  rw [condMutualInfoOfCondPDF, integral_eq_zero_iff_of_nonneg
    (fun t => mutualInfoOfCondPDF_nonneg (hk t) (hb t) (hint t)) hIT]
  exact eventually_congr (ae_of_all _ fun t =>
    mutualInfoOfCondPDF_eq_zero_iff (hk t) (hb t) (hint t) (hI t))

end Conditional

/-- **Definition 10.30, (10.136).** For a discrete `Y` with pmf `p` and a continuous `X` related to
`Y` through the conditional density `f(x|y) = k y x`, `H(Y|X) = H(Y) - I(X; Y)`. The law of `Y` is
the measure `∑_y p(y) δ_y`. -/
def condEntropyOfCondPDF {β : Type*} [Fintype β] [MeasurableSpace β] (p : β → ℝ)
    (ν : Measure 𝒳) (k : β → 𝒳 → ℝ) : ℝ :=
  entropy p - mutualInfoOfCondPDF (∑ y, ENNReal.ofReal (p y) • Measure.dirac y) ν k

/-- **Proposition 10.31, (10.138).** `H(Y) = H(Y|X) + I(X; Y)` for a discrete `Y` and a continuous
`X`. -/
theorem entropy_eq_condEntropyOfCondPDF_add {β : Type*} [Fintype β] [MeasurableSpace β]
    (p : β → ℝ) (ν : Measure 𝒳) (k : β → 𝒳 → ℝ) :
    entropy p = condEntropyOfCondPDF p ν k +
      mutualInfoOfCondPDF (∑ y, ENNReal.ofReal (p y) • Measure.dirac y) ν k := by
  rw [condEntropyOfCondPDF]
  ring

end InfoTheory
