/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.Joint

/-!
# The chain rule for differential entropy and the independence bound

A random vector `(X₁, …, Xₙ)` with values in `αⁿ` has a density `f` with respect to the product
measure `μⁿ`. Splitting off one coordinate identifies `αⁿ⁺¹` with `α × αⁿ`, so the results on
pairs apply: the chain rule `h(X₁, …, Xₙ) = ∑ h(Xᵢ | X₁, …, Xᵢ₋₁)`, and the independence bound
`h(X₁, …, Xₙ) ≤ ∑ h(Xᵢ)`.

## Main definitions

* `splitPDF i f`: the density `(t, y) ↦ f(x)` of `(Xᵢ, (Xⱼ)_{j ≠ i})`, where `x` has coordinate `t`
  at `i` and the coordinates of `y` elsewhere.
* `coordMarginal μ i f`: the marginal density of the coordinate `Xᵢ`.
* `condDiffEntropyLast μ f`: `h(Xₙ₊₁ | X₁, …, Xₙ)` for a density `f` on `αⁿ⁺¹`.

## Main statements

* `diffEntropy_eq_sum_condDiffEntropyLast`: Theorem 8.6.2, the chain rule, for the densities of
  `(X₁, …, Xₖ)`, `k ≤ n`.
* `diffEntropy_le_sum_coordMarginal`, `diffEntropy_eq_sum_coordMarginal_iff`: Corollary (8.63),
  `h(X₁, …, Xₙ) ≤ ∑ h(Xᵢ)` with equality iff the `Xᵢ` are independent.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 8.6
-/

open Real MeasureTheory Filter Set

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

/-- The identification of `αⁿ⁺¹` with `α × αⁿ` splitting off the coordinate `i`. -/
abbrev splitEquiv (α : Type*) [MeasurableSpace α] (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => α) i

lemma measurePreserving_splitEquiv (μ : Measure α) [SigmaFinite μ] (i : Fin (n + 1)) :
    MeasurePreserving (splitEquiv α n i) (Measure.pi fun _ => μ)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
  measurePreserving_piFinSuccAbove (fun _ => μ) i

/-- The density `(t, y) ↦ f(x)` of `(Xᵢ, (Xⱼ)_{j ≠ i})`, where `x` has coordinate `t` at `i` and
the coordinates of `y` elsewhere. -/
def splitPDF (i : Fin (n + 1)) (f : (Fin (n + 1) → α) → ℝ) : α × (Fin n → α) → ℝ :=
  f ∘ (splitEquiv α n i).symm

lemma integral_splitPDF (μ : Measure α) [SigmaFinite μ] (i : Fin (n + 1))
    (F : (Fin (n + 1) → α) → ℝ) :
    ∫ z, splitPDF i F z ∂(μ.prod (Measure.pi fun _ => μ)) = ∫ x, F x ∂(Measure.pi fun _ => μ) := by
  rw [← (measurePreserving_splitEquiv μ i).integral_comp']
  simp only [splitPDF, Function.comp_apply, MeasurableEquiv.symm_apply_apply]

lemma integrable_splitPDF_iff (μ : Measure α) [SigmaFinite μ] (i : Fin (n + 1))
    (F : (Fin (n + 1) → α) → ℝ) :
    Integrable (splitPDF i F) (μ.prod (Measure.pi fun _ => μ)) ↔
      Integrable F (Measure.pi fun _ => μ) := by
  rw [← (measurePreserving_splitEquiv μ i).integrable_comp_emb
    (splitEquiv α n i).measurableEmbedding]
  simp only [splitPDF, Function.comp_def, MeasurableEquiv.symm_apply_apply]

lemma ae_splitPDF_iff (μ : Measure α) [SigmaFinite μ] (i : Fin (n + 1))
    {p : (Fin (n + 1) → α) → Prop} :
    (∀ᵐ z ∂(μ.prod (Measure.pi fun _ => μ)), p ((splitEquiv α n i).symm z)) ↔
      ∀ᵐ x ∂(Measure.pi fun _ => μ), p x := by
  rw [← (measurePreserving_splitEquiv μ i).map_eq,
    (splitEquiv α n i).measurableEmbedding.ae_map_iff]
  simp only [MeasurableEquiv.symm_apply_apply]

lemma IsPDF.splitPDF {f : (Fin (n + 1) → α) → ℝ} (hf : IsPDF (Measure.pi fun _ => μ) f)
    (i : Fin (n + 1)) : IsPDF (μ.prod (Measure.pi fun _ => μ)) (InfoTheory.splitPDF i f) :=
  ⟨hf.measurable.comp (splitEquiv α n i).symm.measurable, fun _ => hf.nonneg _,
    (integrable_splitPDF_iff μ i f).2 hf.integrable,
    by rw [integral_splitPDF, hf.integral_eq_one]⟩

lemma diffEntropy_splitPDF (μ : Measure α) [SigmaFinite μ] (i : Fin (n + 1))
    (f : (Fin (n + 1) → α) → ℝ) :
    diffEntropy (μ.prod (Measure.pi fun _ => μ)) (splitPDF i f) =
      diffEntropy (Measure.pi fun _ => μ) f :=
  integral_splitPDF μ i fun x => negMulLog (f x)

/-! ### The chain rule -/

/-- `h(Xₙ₊₁ | X₁, …, Xₙ)` for a density `f` of `(X₁, …, Xₙ₊₁)`, (8.32). -/
def condDiffEntropyLast (μ : Measure α) (f : (Fin (n + 1) → α) → ℝ) : ℝ :=
  condDiffEntropy μ (Measure.pi fun _ => μ) (splitPDF (Fin.last n) f)

/-- The marginal density of `(X₁, …, Xₙ)` obtained from the density of `(X₁, …, Xₙ₊₁)` by
integrating out the last coordinate. -/
def initMarginal (μ : Measure α) (f : (Fin (n + 1) → α) → ℝ) : (Fin n → α) → ℝ :=
  marginalSnd μ (splitPDF (Fin.last n) f)

omit [SigmaFinite μ] in
lemma initMarginal_apply (f : (Fin (n + 1) → α) → ℝ) (y : Fin n → α) :
    initMarginal μ f y = ∫ t, f (Fin.snoc y t) ∂μ := by
  simp only [initMarginal, marginalSnd, splitPDF, Function.comp_apply]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  congr 1
  funext j
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

/-- The chain rule in one step: `h(X₁, …, Xₙ₊₁) = h(X₁, …, Xₙ) + h(Xₙ₊₁ | X₁, …, Xₙ)`. -/
theorem diffEntropy_eq_initMarginal_add {f : (Fin (n + 1) → α) → ℝ}
    (hf : IsPDF (Measure.pi fun _ => μ) f)
    (hint : Integrable (fun x => negMulLog (f x)) (Measure.pi fun _ => μ))
    (hint' : Integrable (fun y => negMulLog (initMarginal μ f y)) (Measure.pi fun _ => μ)) :
    diffEntropy (Measure.pi fun _ => μ) f =
      diffEntropy (Measure.pi fun _ => μ) (initMarginal μ f) + condDiffEntropyLast μ f := by
  have h := condDiffEntropy_eq (hf.splitPDF (Fin.last n))
    ((integrable_splitPDF_iff μ (Fin.last n) fun x => negMulLog (f x)).2 hint) hint'
  rw [condDiffEntropyLast, h, diffEntropy_splitPDF, initMarginal]
  ring

omit [SigmaFinite μ] in
/-- `h(f) = 0` for a density on the one-point space `α⁰`. -/
lemma diffEntropy_fin_zero {f : (Fin 0 → α) → ℝ} (hf : IsPDF (Measure.pi fun _ => μ) f) :
    diffEntropy (Measure.pi fun _ => μ) f = 0 := by
  have h1 := hf.integral_eq_one
  rw [Measure.pi_of_empty, integral_dirac] at h1
  rw [diffEntropy, Measure.pi_of_empty, integral_dirac, h1, negMulLog_one]

/-- **Theorem 8.6.2 (Chain rule for differential entropy), (8.62).** If `f k` is the density of
`(X₁, …, Xₖ)` for `k ≤ n`, each the marginal of the next, then
`h(X₁, …, Xₙ) = ∑ᵢ h(Xᵢ | X₁, …, Xᵢ₋₁)`. -/
theorem diffEntropy_eq_sum_condDiffEntropyLast (f : ∀ k, (Fin k → α) → ℝ)
    (hpdf : ∀ k ≤ n, IsPDF (Measure.pi fun _ => μ) (f k))
    (hint : ∀ k ≤ n, Integrable (fun x => negMulLog (f k x)) (Measure.pi fun _ => μ))
    (hcons : ∀ k < n, initMarginal μ (f (k + 1)) = f k) :
    diffEntropy (Measure.pi fun _ => μ) (f n) =
      ∑ k ∈ Finset.range n, condDiffEntropyLast μ (f (k + 1)) := by
  induction n with
  | zero => simp [diffEntropy_fin_zero (hpdf 0 le_rfl)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih (fun k hk => hpdf k (by omega)) (fun k hk => hint k (by omega))
      (fun k hk => hcons k (by omega))]
    have h := diffEntropy_eq_initMarginal_add (hpdf (n + 1) le_rfl) (hint (n + 1) le_rfl)
      (by rw [hcons n (by omega)]; exact hint n (by omega))
    rw [h, hcons n (by omega)]

/-! ### The independence bound -/

/-- The marginal density `f(xᵢ)` of the coordinate `Xᵢ`. -/
def coordMarginal (μ : Measure α) (i : Fin (n + 1)) (f : (Fin (n + 1) → α) → ℝ) : α → ℝ :=
  marginalFst (Measure.pi fun _ => μ) (splitPDF i f)

lemma IsPDF.coordMarginal {f : (Fin (n + 1) → α) → ℝ} (hf : IsPDF (Measure.pi fun _ => μ) f)
    (i : Fin (n + 1)) : IsPDF μ (InfoTheory.coordMarginal μ i f) :=
  (hf.splitPDF i).marginalFst

lemma splitEquiv_apply_fst (i : Fin (n + 1)) (x : Fin (n + 1) → α) :
    (splitEquiv α n i x).1 = x i := rfl

/-- `f(x) = 0` almost everywhere where `f(xᵢ) = 0`. -/
lemma ae_coordMarginal_eq_zero {f : (Fin (n + 1) → α) → ℝ} (hf : IsPDF (Measure.pi fun _ => μ) f)
    (i : Fin (n + 1)) :
    ∀ᵐ x ∂(Measure.pi fun _ => μ), coordMarginal μ i f (x i) = 0 → f x = 0 := by
  have h := ae_marginalFst_eq_zero (hf.splitPDF i)
  rw [← ae_splitPDF_iff μ i]
  filter_upwards [h] with z hz
  simpa [splitPDF, coordMarginal] using hz

/-- `∫ f(x) log f(xᵢ) dx = -h(Xᵢ)`. -/
lemma integral_mul_log_coordMarginal {f : (Fin (n + 1) → α) → ℝ}
    (hf : IsPDF (Measure.pi fun _ => μ) f) (i : Fin (n + 1))
    (hi : Integrable (fun t => negMulLog (coordMarginal μ i f t)) μ) :
    Integrable (fun x => f x * log (coordMarginal μ i f (x i))) (Measure.pi fun _ => μ) ∧
      ∫ x, f x * log (coordMarginal μ i f (x i)) ∂(Measure.pi fun _ => μ) =
        -diffEntropy μ (coordMarginal μ i f) := by
  obtain ⟨h1, h2⟩ := integral_mul_log_marginalFst (hf.splitPDF i) hi
  set G : α × (Fin n → α) → ℝ := fun z =>
    splitPDF i f z * log (marginalFst (Measure.pi fun _ => μ) (splitPDF i f) z.1)
  have e : (fun x => f x * log (coordMarginal μ i f (x i))) = fun x => G (splitEquiv α n i x) := by
    funext x
    simp only [G, splitPDF, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact ((measurePreserving_splitEquiv μ i).integrable_comp_emb
      (splitEquiv α n i).measurableEmbedding).2 h1
  · rw [e, (measurePreserving_splitEquiv μ i).integral_comp' G]
    exact h2

/-- The product `∏ᵢ f(xᵢ)` of the marginal densities, the density of independent coordinates. -/
lemma IsPDF.prod_coordMarginal {f : (Fin (n + 1) → α) → ℝ}
    (hf : IsPDF (Measure.pi fun _ => μ) f) :
    IsPDF (Measure.pi fun _ => μ) fun x => ∏ i, InfoTheory.coordMarginal μ i f (x i) :=
  ⟨Finset.measurable_prod _ fun i _ => (hf.coordMarginal i).measurable.comp (measurable_pi_apply i),
    fun x => Finset.prod_nonneg fun i _ => (hf.coordMarginal i).nonneg _,
    Integrable.fintype_prod fun i => (hf.coordMarginal i).integrable,
    by rw [integral_fintype_prod_eq_prod]; simp [(hf.coordMarginal _).integral_eq_one]⟩

lemma crossEntropy_prod_coordMarginal {f : (Fin (n + 1) → α) → ℝ}
    (hf : IsPDF (Measure.pi fun _ => μ) f)
    (hi : ∀ i, Integrable (fun t => negMulLog (coordMarginal μ i f t)) μ) :
    Integrable (fun x => f x * log (∏ i, coordMarginal μ i f (x i))) (Measure.pi fun _ => μ) ∧
      -∫ x, f x * log (∏ i, coordMarginal μ i f (x i)) ∂(Measure.pi fun _ => μ) =
        ∑ i, diffEntropy μ (coordMarginal μ i f) := by
  have hae : (fun x => f x * log (∏ i, coordMarginal μ i f (x i))) =ᵐ[Measure.pi fun _ => μ]
      fun x => ∑ i, f x * log (coordMarginal μ i f (x i)) := by
    filter_upwards [eventually_all.2 fun i => ae_coordMarginal_eq_zero hf i] with x hx
    rcases eq_or_ne (f x) 0 with h0 | h0
    · simp [h0]
    · rw [log_prod fun i _ => fun h => h0 (hx i h), Finset.mul_sum]
  have hint : ∀ i, Integrable (fun x => f x * log (coordMarginal μ i f (x i)))
      (Measure.pi fun _ => μ) := fun i => (integral_mul_log_coordMarginal hf i (hi i)).1
  refine ⟨(integrable_finsetSum _ fun i _ => hint i).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_finsetSum _ fun i _ => hint i, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [(integral_mul_log_coordMarginal hf i (hi i)).2, neg_neg]

lemma ae_prod_coordMarginal_eq_zero {f : (Fin (n + 1) → α) → ℝ}
    (hf : IsPDF (Measure.pi fun _ => μ) f) :
    ∀ᵐ x ∂(Measure.pi fun _ => μ), ∏ i, coordMarginal μ i f (x i) = 0 → f x = 0 := by
  filter_upwards [eventually_all.2 fun i => ae_coordMarginal_eq_zero hf i] with x hx h
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 h
  exact hx i hi

/-- **Corollary (8.63) of Theorem 8.6.2.** `h(X₁, …, Xₙ) ≤ ∑ᵢ h(Xᵢ)`. -/
theorem diffEntropy_le_sum_coordMarginal {f : (Fin (n + 1) → α) → ℝ}
    (hf : IsPDF (Measure.pi fun _ => μ) f)
    (hint : Integrable (fun x => negMulLog (f x)) (Measure.pi fun _ => μ))
    (hi : ∀ i, Integrable (fun t => negMulLog (coordMarginal μ i f t)) μ) :
    diffEntropy (Measure.pi fun _ => μ) f ≤ ∑ i, diffEntropy μ (coordMarginal μ i f) := by
  obtain ⟨h1, h2⟩ := crossEntropy_prod_coordMarginal hf hi
  rw [← h2]
  exact diffEntropy_le_crossEntropy hf hf.prod_coordMarginal (ae_prod_coordMarginal_eq_zero hf)
    hint h1

/-- **Corollary (8.63) (equality case).** Equality holds iff `X₁, …, Xₙ` are independent:
`f(x) = ∏ᵢ f(xᵢ)` almost everywhere. -/
theorem diffEntropy_eq_sum_coordMarginal_iff {f : (Fin (n + 1) → α) → ℝ}
    (hf : IsPDF (Measure.pi fun _ => μ) f)
    (hint : Integrable (fun x => negMulLog (f x)) (Measure.pi fun _ => μ))
    (hi : ∀ i, Integrable (fun t => negMulLog (coordMarginal μ i f t)) μ) :
    diffEntropy (Measure.pi fun _ => μ) f = ∑ i, diffEntropy μ (coordMarginal μ i f) ↔
      f =ᵐ[Measure.pi fun _ => μ] fun x => ∏ i, coordMarginal μ i f (x i) := by
  obtain ⟨h1, h2⟩ := crossEntropy_prod_coordMarginal hf hi
  rw [← h2]
  exact diffEntropy_eq_crossEntropy_iff hf hf.prod_coordMarginal
    (ae_prod_coordMarginal_eq_zero hf) hint h1

end InfoTheory
