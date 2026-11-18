/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.AsymptoticRate
public import InfoTheoryLib.DifferentialEntropy.Gaussian
public import InfoTheoryLib.DifferentialEntropy.Mixed

/-!
# Continuous channels

A discrete-time continuous channel relates its output to its input through a bounded conditional
density `f(y|x)`, defined for every input `x`, whose conditional differential entropy is uniformly
bounded. A channel `Y = α(X, Z)` with noise `Z` independent of the input is equivalent to it if
`(X, Y)` has the same law for every input distribution; the additive channel `Y = X + Z` with noise
density `g` has `f(y|x) = g(y - x)`. The capacity with an input constraint `E κ(X) ≤ P` is
nondecreasing, concave and left-continuous in `P`.

## Main definitions

* `IsContinuousChannel ν k`: Definition 11.1.
* `contNoiseLaw μ ρ α`: the law of `(X, α(X, Z))`, Definition 11.2.
* `IsEquivalentContChannel ν k ρ α`: Definition 11.3.
* `meanCost κ x`, `ContChannelCode`: the input constraint (11.6) and codes (Definition 11.9).
* `ContChannelCode.condErrProb`, `ContChannelCode.maxErrProb`: Definitions 11.10 and 11.11.
* `IsAchievableContRate`: Definition 11.13.
* `contCapacity ν k κ P`: the capacity `C(P)`, Definition 11.7.

## Main statements

* `isEquivalentContChannel_add`: the additive channel `Y = X + Z` has `f(y|x) = g(y - x)`.
* `monotoneOn_contCapacity`, `concaveOn_contCapacity`, `tendsto_contCapacity_left`: Theorem 11.8.
* `prod_pdfMeasure_le_exp_neg`: the bound (11.82)–(11.88) of Lemma 11.18.
* `condDiffEntropyOfCondPDF_sub`: Lemma 11.22.

## Implementation notes

The concavity of `I(X; Y)` in the input distribution, (11.12), which the book leaves as an exercise,
is a hypothesis of the concavity and continuity parts of Theorem 11.8. The capacity is a supremum of
real numbers, so these results also assume that the mutual informations are bounded.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 11.1 to 11.4
-/

open MeasureTheory ProbabilityTheory Real Filter Set Function Topology
open scoped ENNReal

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒵]

/-! ### Definitions 11.1 to 11.3 -/

/-- **Definition 11.1.** A discrete-time continuous channel: a bounded conditional density `f(y|x)`
whose conditional differential entropy `h(Y|X = x)` is finite and uniformly bounded, (11.1). -/
structure IsContinuousChannel (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) : Prop where
  isCondPDF : IsCondPDF ν k
  bounded : IsBoundedCondPDF k
  integrable : ∀ x, Integrable (fun y => negMulLog (k x y)) ν
  bounded_diffEntropy : ∃ B, ∀ x, |diffEntropy ν (k x)| ≤ B

/-- **Definition 11.2, (11.2).** The law of `(X, α(X, Z))` for an input with law `μ` and a noise
`Z ∼ ρ` independent of the input. -/
def contNoiseLaw (μ : Measure 𝒳) (ρ : Measure 𝒵) (α : 𝒳 → 𝒵 → 𝒴) : Measure (𝒳 × 𝒴) :=
  (μ.prod ρ).map fun p => (p.1, α p.1 p.2)

/-- **Definition 11.3, (11.3).** The channels `f(y|x)` and `(α, Z)` are equivalent if `(X, Y)` has
the same law for every input distribution. -/
def IsEquivalentContChannel (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) (ρ : Measure 𝒵)
    (α : 𝒳 → 𝒵 → 𝒴) : Prop :=
  ∀ μ : Measure 𝒳, IsProbabilityMeasure μ → contNoiseLaw μ ρ α = jointLawOfCondPDF μ ν k

/-- The additive channel `Y = X + Z` with noise density `g` has the conditional density
`f(y|x) = g(y - x)`. -/
lemma isCondPDF_add {g : ℝ → ℝ} (hg : IsPDF volume g) :
    IsCondPDF volume fun x y : ℝ => g (y - x) := by
  refine ⟨hg.measurable.comp (measurable_snd.sub measurable_fst), fun x => ?_⟩
  refine ⟨hg.measurable.comp (measurable_id.sub_const x), fun y => hg.nonneg _,
    hg.integrable.comp_sub_right x, ?_⟩
  rw [integral_sub_right_eq_self (fun y => g y) x, hg.integral_eq_one]

/-- **Definitions 11.2–11.3.** The additive channel `Y = X + Z`, with noise `Z` of density `g`
independent of `X`, is equivalent to the channel `f(y|x) = g(y - x)`. -/
theorem isEquivalentContChannel_add {g : ℝ → ℝ} (hg : IsPDF volume g) :
    IsEquivalentContChannel volume (fun x y : ℝ => g (y - x)) (pdfMeasure volume g)
      (fun x z => x + z) := by
  intro μ hμ
  have hρ := hg.isProbabilityMeasure
  have hk := isCondPDF_add hg
  have hmap : Measurable fun p : ℝ × ℝ => (p.1, p.1 + p.2) :=
    measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hfin : IsFiniteMeasure (contNoiseLaw μ (pdfMeasure volume g) fun x z => x + z) := by
    rw [contNoiseLaw]; infer_instance
  -- Both measures agree on rectangles `A × B`.
  have hrect : ∀ A B : Set ℝ, MeasurableSet A → MeasurableSet B →
      contNoiseLaw μ (pdfMeasure volume g) (fun x z => x + z) (A ×ˢ B) =
        jointLawOfCondPDF μ volume (fun x y => g (y - x)) (A ×ˢ B) := by
    intro A B hA hB
    rw [contNoiseLaw, Measure.map_apply hmap (hA.prod hB), jointLawOfCondPDF_prod hk hA hB,
      Measure.prod_apply (hmap (hA.prod hB))]
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, pdfMeasure, withDensity_apply _ (by
        exact measurable_prodMk_left (hmap (hA.prod hB)))]
      rw [← lintegral_indicator (measurable_prodMk_left (hmap (hA.prod hB))),
        ← lintegral_indicator hB]
      rw [← lintegral_sub_right_eq_self (fun z => indicator
        (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => (p.1, p.1 + p.2)) ⁻¹' A ×ˢ B))
        (fun z => ENNReal.ofReal (g z)) z) x]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ B
      · rw [indicator_of_mem hy, indicator_of_mem]
        simp [hx, hy]
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        simp [hy]
    · rw [indicator_of_notMem hx]
      refine measure_mono_null (fun z hz => ?_) (measure_empty (μ := pdfMeasure volume g))
      simp only [mem_preimage, Set.mem_prod] at hz
      exact absurd hz.1 hx
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hrect A B hA hB
  · rw [← Set.univ_prod_univ]
    exact hrect _ _ MeasurableSet.univ MeasurableSet.univ

/-- **Definition 11.19.** The Gaussian channel with noise energy `N`: `f(y|x) = N(x, N)(y)` and
`Y = X + Z` with `Z ∼ N(0, N)` are equivalent. -/
theorem isEquivalentContChannel_gaussian {N : NNReal} (hN : N ≠ 0) :
    IsEquivalentContChannel volume (fun x y : ℝ => gaussianPDFReal 0 N (y - x))
      (pdfMeasure volume (gaussianPDFReal 0 N)) (fun x z => x + z) :=
  isEquivalentContChannel_add (gaussianPDFReal_isPDF 0 hN)

/-! ### Codes and input constraints -/

/-- **(11.6)** The average cost `(1/n) ∑ᵢ κ(xᵢ)` of a codeword. -/
def meanCost (κ : 𝒳 → ℝ) {n : ℕ} (x : Fin n → 𝒳) : ℝ := (∑ i, κ (x i)) / n

/-- **Definition 11.9.** An `(n, M)` code for a continuous memoryless channel with input constraint
`(κ, P)`: every codeword satisfies `(1/n) ∑ᵢ κ(xᵢ(w)) ≤ P`, (11.23). -/
structure ContChannelCode (M n : ℕ) (𝒳 𝒴 : Type*) (κ : 𝒳 → ℝ) (P : ℝ) where
  /-- The encoding function `e : {1, …, M} → 𝒳ⁿ`. -/
  enc : Fin M → Fin n → 𝒳
  /-- The decoding function `g : 𝒴ⁿ → {1, …, M}`. -/
  dec : (Fin n → 𝒴) → Fin M
  /-- The input constraint. -/
  cost_le : ∀ w, meanCost κ (enc w) ≤ P

namespace ContChannelCode

variable {M n : ℕ} {κ : 𝒳 → ℝ} {P : ℝ}

open Classical in
/-- **Definition 11.10, (11.29).** The conditional probability of error `λ_w`, for a memoryless use
of the channel `f(y|x)`, with `f(y|x) = ∏ᵢ f(yᵢ|xᵢ)`. -/
def condErrProb (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) (c : ContChannelCode M n 𝒳 𝒴 κ P)
    (w : Fin M) : ℝ :=
  ∫ y, (if c.dec y ≠ w then ∏ i, k (c.enc w i) (y i) else 0) ∂Measure.pi fun _ => ν

/-- **Definition 11.11, (11.30).** The maximal probability of error. -/
def maxErrProb (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) (c : ContChannelCode M n 𝒳 𝒴 κ P) : ℝ :=
  ⨆ w, c.condErrProb ν k w

/-- **Definition 11.12, (11.31).** The average probability of error, for a uniform message. -/
def avgErrProb (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) (c : ContChannelCode M n 𝒳 𝒴 κ P) : ℝ :=
  (∑ w, c.condErrProb ν k w) / M

end ContChannelCode

/-- **Definition 11.13.** A rate `R` is achievable for the continuous memoryless channel `f(y|x)`
with input constraint `(κ, P)`. -/
def IsAchievableContRate (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) (κ : 𝒳 → ℝ) (P R : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 0 < M ∧ ∃ c : ContChannelCode M n 𝒳 𝒴 κ P,
    R - ε < codeRate M n ∧ c.maxErrProb ν k < ε

/-! ### The capacity -/

/-- The input distributions satisfying the input constraint `E κ(X) ≤ P`. -/
def AdmissibleInput (κ : 𝒳 → ℝ) (P : ℝ) (μ : Measure 𝒳) : Prop :=
  IsProbabilityMeasure μ ∧ Integrable κ μ ∧ ∫ x, κ x ∂μ ≤ P

/-- **Definition 11.7, (11.7).** The capacity `C(P) = sup_{F : E κ(X) ≤ P} I(X; Y)`. -/
def contCapacity (ν : Measure 𝒴) (k : 𝒳 → 𝒴 → ℝ) (κ : 𝒳 → ℝ) (P : ℝ) : ℝ :=
  sSup {I | ∃ μ, AdmissibleInput κ P μ ∧ mutualInfoOfCondPDF μ ν k = I}

section Capacity

variable {ν : Measure 𝒴} {k : 𝒳 → 𝒴 → ℝ} {κ : 𝒳 → ℝ}

/-- The constraint values `P` with an admissible input distribution. -/
def feasibleCosts (κ : 𝒳 → ℝ) : Set ℝ := {P | ∃ μ, AdmissibleInput κ P μ}

lemma admissible_mono {P P' : ℝ} (h : P ≤ P') {μ : Measure 𝒳} (hμ : AdmissibleInput κ P μ) :
    AdmissibleInput κ P' μ :=
  ⟨hμ.1, hμ.2.1, hμ.2.2.trans h⟩

/-- **Theorem 11.8 (nondecreasing).** -/
theorem monotoneOn_contCapacity
    (hbdd : ∀ P, BddAbove {I | ∃ μ, AdmissibleInput κ P μ ∧ mutualInfoOfCondPDF μ ν k = I}) :
    MonotoneOn (contCapacity ν k κ) (feasibleCosts κ) := by
  rintro P ⟨μ, hμ⟩ P' - h
  refine csSup_le_csSup (hbdd P') ⟨_, μ, hμ, rfl⟩ ?_
  rintro _ ⟨μ', hμ', rfl⟩
  exact ⟨μ', admissible_mono h hμ', rfl⟩

lemma feasibleCosts_upward {P P' : ℝ} (h : P ≤ P') (hP : P ∈ feasibleCosts κ) :
    P' ∈ feasibleCosts κ := by
  obtain ⟨μ, hμ⟩ := hP
  exact ⟨μ, admissible_mono h hμ⟩

lemma convex_feasibleCosts : Convex ℝ (feasibleCosts κ) := by
  intro P₁ h₁ P₂ h₂ a b ha hb hab
  obtain rfl : a = 1 - b := by linarith
  rcases le_total P₁ P₂ with h | h
  · exact feasibleCosts_upward
      (by simp only [smul_eq_mul]; nlinarith [mul_nonneg hb (sub_nonneg.2 h)]) h₁
  · exact feasibleCosts_upward
      (by simp only [smul_eq_mul]; nlinarith [mul_nonneg ha (sub_nonneg.2 h)]) h₂

/-- The mixture `a μ₁ + b μ₂` of two admissible inputs is admissible for `a P₁ + b P₂`, (11.11). -/
lemma admissible_mix {P₁ P₂ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {μ₁ μ₂ : Measure 𝒳} (h₁ : AdmissibleInput κ P₁ μ₁) (h₂ : AdmissibleInput κ P₂ μ₂) :
    AdmissibleInput κ (a * P₁ + b * P₂) (ENNReal.ofReal a • μ₁ + ENNReal.ofReal b • μ₂) := by
  have := h₁.1
  have := h₂.1
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simp only [add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  · exact (h₁.2.1.smul_measure ENNReal.ofReal_ne_top).add_measure
      (h₂.2.1.smul_measure ENNReal.ofReal_ne_top)
  · rw [integral_add_measure (h₁.2.1.smul_measure ENNReal.ofReal_ne_top)
      (h₂.2.1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]
    nlinarith [h₁.2.2, h₂.2.2]

/-- **Theorem 11.8 (concave), (11.8)–(11.16).** If `I(X; Y)` is concave in the input distribution,
(11.12), the capacity is concave. -/
theorem concaveOn_contCapacity
    (hbdd : ∀ P, BddAbove {I | ∃ μ, AdmissibleInput κ P μ ∧ mutualInfoOfCondPDF μ ν k = I})
    (hconc : ∀ μ₁ μ₂ : Measure 𝒳, IsProbabilityMeasure μ₁ → IsProbabilityMeasure μ₂ →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a * mutualInfoOfCondPDF μ₁ ν k + b * mutualInfoOfCondPDF μ₂ ν k ≤
          mutualInfoOfCondPDF (ENNReal.ofReal a • μ₁ + ENNReal.ofReal b • μ₂) ν k) :
    ConcaveOn ℝ (feasibleCosts κ) (contCapacity ν k κ) := by
  refine ⟨convex_feasibleCosts, fun P₁ h₁ P₂ h₂ a b ha hb hab => ?_⟩
  obtain ⟨μ₀₁, hμ₀₁⟩ := h₁
  obtain ⟨μ₀₂, hμ₀₂⟩ := h₂
  simp only [smul_eq_mul]
  set S : ℝ → Set ℝ := fun P => {I | ∃ μ, AdmissibleInput κ P μ ∧ mutualInfoOfCondPDF μ ν k = I}
  have hC : ∀ P, contCapacity ν k κ P = sSup (S P) := fun P => rfl
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Inputs within `ε` of `C(P₁)` and `C(P₂)`, (11.8)–(11.9).
  have hne₁ : (S P₁).Nonempty := ⟨_, μ₀₁, hμ₀₁, rfl⟩
  have hne₂ : (S P₂).Nonempty := ⟨_, μ₀₂, hμ₀₂, rfl⟩
  obtain ⟨_, ⟨μ₁, hμ₁, rfl⟩, hI₁⟩ := exists_lt_of_lt_csSup hne₁
    (show sSup (S P₁) - ε < sSup (S P₁) by linarith)
  obtain ⟨_, ⟨μ₂, hμ₂, rfl⟩, hI₂⟩ := exists_lt_of_lt_csSup hne₂
    (show sSup (S P₂) - ε < sSup (S P₂) by linarith)
  have hmix := admissible_mix ha hb hab hμ₁ hμ₂
  have hle : mutualInfoOfCondPDF (ENNReal.ofReal a • μ₁ + ENNReal.ofReal b • μ₂) ν k ≤
      sSup (S (a * P₁ + b * P₂)) := le_csSup (hbdd (a * P₁ + b * P₂)) ⟨_, hmix, rfl⟩
  have hc := hconc μ₁ μ₂ hμ₁.1 hμ₂.1 a b ha hb hab
  have h₁ := mul_le_mul_of_nonneg_left hI₁.le ha
  have h₂ := mul_le_mul_of_nonneg_left hI₂.le hb
  rw [mul_sub] at h₁ h₂
  have hε' : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  rw [hC, hC, hC]
  linarith

/-- **Theorem 11.8 (left-continuous), (11.17)–(11.20).** Under the hypotheses of concavity, `C(P)`
is left-continuous at every `P₂` above a feasible `P₁`. -/
theorem tendsto_contCapacity_left
    (hbdd : ∀ P, BddAbove {I | ∃ μ, AdmissibleInput κ P μ ∧ mutualInfoOfCondPDF μ ν k = I})
    (hconc : ∀ μ₁ μ₂ : Measure 𝒳, IsProbabilityMeasure μ₁ → IsProbabilityMeasure μ₂ →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a * mutualInfoOfCondPDF μ₁ ν k + b * mutualInfoOfCondPDF μ₂ ν k ≤
          mutualInfoOfCondPDF (ENNReal.ofReal a • μ₁ + ENNReal.ofReal b • μ₂) ν k)
    {P₁ P₂ : ℝ} (h₁ : P₁ ∈ feasibleCosts κ) (h₁₂ : P₁ < P₂) :
    Tendsto (contCapacity ν k κ) (𝓝[<] P₂) (𝓝 (contCapacity ν k κ P₂)) := by
  have hconcave := concaveOn_contCapacity hbdd hconc
  have hmono := monotoneOn_contCapacity hbdd (ν := ν) (k := k)
  have h₂ : P₂ ∈ feasibleCosts κ := feasibleCosts_upward h₁₂.le h₁
  set C := contCapacity ν k κ
  set L : ℝ → ℝ := fun P => (P₂ - P) / (P₂ - P₁) * C P₁ + (P - P₁) / (P₂ - P₁) * C P₂
  have hd : 0 < P₂ - P₁ := by linarith
  have hL : Tendsto L (𝓝[<] P₂) (𝓝 (C P₂)) := by
    have hc : Continuous L := by fun_prop
    have := (hc.tendsto P₂).mono_left (nhdsWithin_le_nhds (s := Iio P₂))
    have hL₂ : L P₂ = C P₂ := by
      simp only [L, sub_self, zero_div, zero_mul, zero_add]
      rw [div_self hd.ne', one_mul]
    rwa [hL₂] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT h₁₂] with P hP
    have ha : 0 ≤ (P₂ - P) / (P₂ - P₁) := div_nonneg (by linarith [hP.2]) hd.le
    have hb : 0 ≤ (P - P₁) / (P₂ - P₁) := div_nonneg (by linarith [hP.1]) hd.le
    have hab : (P₂ - P) / (P₂ - P₁) + (P - P₁) / (P₂ - P₁) = 1 := by
      field_simp; ring
    have hcomb : (P₂ - P) / (P₂ - P₁) * P₁ + (P - P₁) / (P₂ - P₁) * P₂ = P := by
      field_simp; ring
    have := hconcave.2 h₁ h₂ ha hb hab
    simp only [smul_eq_mul] at this
    rwa [hcomb] at this
  · filter_upwards [Ioo_mem_nhdsLT h₁₂] with P hP
    exact hmono (feasibleCosts_upward hP.1.le h₁) h₂ hP.2.le

end Capacity

/-! ### Mutual typicality and additive noise -/

/-- **Lemma 11.18, (11.82)–(11.88).** Let `(X', Y')` have independent components with laws `μ` and
`g dν`. If `f(y|x) ≥ e^c g(y)` on a set `U`, then `Pr{(X', Y') ∈ U} ≤ e^{-c}`. For `n` uses of the
channel, `U` is the mutually typical set of Definition 11.16 and `c = n(I(X; Y) - δ)`. -/
theorem prod_pdfMeasure_le_exp_neg {μ : Measure 𝒳} [IsProbabilityMeasure μ] {ν : Measure 𝒴}
    [SFinite ν] {k : 𝒳 → 𝒴 → ℝ} (hk : IsCondPDF ν k) {g : 𝒴 → ℝ} {U : Set (𝒳 × 𝒴)}
    (hU : MeasurableSet U) {c : ℝ} (h : ∀ z ∈ U, exp c * g z.2 ≤ k z.1 z.2) :
    (μ.prod (pdfMeasure ν g)) U ≤ ENNReal.ofReal (exp (-c)) := by
  have : SFinite (pdfMeasure ν g) := by unfold pdfMeasure; infer_instance
  rw [Measure.prod_apply hU]
  calc ∫⁻ x, pdfMeasure ν g (Prod.mk x ⁻¹' U) ∂μ ≤ ∫⁻ _x, ENNReal.ofReal (exp (-c)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [pdfMeasure, withDensity_apply _ (measurable_prodMk_left hU)]
        calc ∫⁻ y in Prod.mk x ⁻¹' U, ENNReal.ofReal (g y) ∂ν
            ≤ ∫⁻ y in Prod.mk x ⁻¹' U, ENNReal.ofReal (exp (-c)) * ENNReal.ofReal (k x y) ∂ν := by
              refine setLIntegral_mono' (measurable_prodMk_left hU) fun y hy => ?_
              rw [← ENNReal.ofReal_mul (exp_pos _).le]
              refine ENNReal.ofReal_le_ofReal ?_
              have hxy := h (x, y) hy
              have e : exp (-c) * (exp c * g y) = g y := by
                rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
              calc g y = exp (-c) * (exp c * g y) := e.symm
                _ ≤ exp (-c) * k x y := mul_le_mul_of_nonneg_left hxy (exp_pos _).le
          _ ≤ ∫⁻ y, ENNReal.ofReal (exp (-c)) * ENNReal.ofReal (k x y) ∂ν :=
              setLIntegral_le_lintegral _ _
          _ = ENNReal.ofReal (exp (-c)) := by
              rw [lintegral_const_mul _ (hk.isPDF x).measurable.ennreal_ofReal,
                hk.lintegral_ofReal, mul_one]
    _ = ENNReal.ofReal (exp (-c)) := by simp

/-- **Lemma 11.22, (11.119)–(11.124).** For `Y = X + Z` with `f_{Z|X}(z|x) = g x z`,
`h(Y|X) = h(Z|X)`. -/
theorem condDiffEntropyOfCondPDF_sub (μ : Measure ℝ) (g : ℝ → ℝ → ℝ) :
    condDiffEntropyOfCondPDF μ volume (fun x y => g x (y - x)) =
      condDiffEntropyOfCondPDF μ volume g := by
  simp only [condDiffEntropyOfCondPDF]
  exact integral_congr_ae (ae_of_all _ fun x => diffEntropy_comp_sub volume (g x) x)

end InfoTheory
