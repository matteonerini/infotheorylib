/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.Basic

/-!
# Relative entropy between probability densities

The relative entropy (Kullback–Leibler distance) between two densities `f` and `g` with respect to
the same measure `μ` is `D(f‖g) = ∫ f log (f/g) dμ`. It is finite only if the support of `f` is
contained in the support of `g` (`f ≪ g`), and it is non-negative, with equality iff `f = g`
almost everywhere.

## Main definitions

* `relEntropyPDF μ f g`: the relative entropy `D(f‖g)`, (8.46).

## Main statements

* `relEntropyPDF_nonneg`, `relEntropyPDF_eq_zero_iff`: Theorem 8.6.1, `D(f‖g) ≥ 0` with
  equality iff `f = g` a.e.
* `relEntropyPDF_eq`: `D(f‖g) = -h(f) - ∫ f log g`.
* `diffEntropy_le_crossEntropy`, `diffEntropy_eq_crossEntropy_iff`: `h(f) ≤ -∫ f log g`, with
  equality iff `f = g` a.e., the form of Theorem 8.6.1 used for maximum entropy.
* `sum_mul_log_div_le_relEntropyPDF`: quantizing into finitely many cells decreases the relative
  entropy, `∑ᵢ P(Aᵢ) log (P(Aᵢ)/Q(Aᵢ)) ≤ D(p‖q)`.

## Implementation notes

The book's convention `p log (p/0) = ∞` is replaced by the hypothesis `f ≪ g`, that is
`g = 0 → f = 0` almost everywhere, and by the integrability of `f log (f/g)`, which says that
`D(f‖g)` is finite.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 8.5 and
  8.6
-/

open Real MeasureTheory Filter

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Definition (8.46).** The relative entropy `D(f‖g) = ∫ f log (f/g) dμ` between the densities
`f` and `g`. -/
def relEntropyPDF (μ : Measure α) (f g : α → ℝ) : ℝ := ∫ x, f x * log (f x / g x) ∂μ

/-- **Theorem 8.6.1, (8.57).** `D(f‖g) ≥ 0` for densities `f ≪ g` with `D(f‖g)` finite. -/
theorem relEntropyPDF_nonneg {f g : α → ℝ} (hf : IsPDF μ f) (hg : IsPDF μ g)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) (hint : Integrable (fun x => f x * log (f x / g x)) μ) :
    0 ≤ relEntropyPDF μ f g := by
  have h : ∫ x, (f x - g x) ∂μ ≤ relEntropyPDF μ f g :=
    integral_mono_ae (hf.integrable.sub hg.integrable) hint
      (hfg.mono fun x hx => sub_le_mul_log_div (hf.nonneg x) (hg.nonneg x) hx)
  rwa [integral_sub hf.integrable hg.integrable, hf.integral_eq_one, hg.integral_eq_one,
    sub_self] at h

/-- **Theorem 8.6.1 (equality case).** `D(f‖g) = 0` iff `f = g` almost everywhere. -/
theorem relEntropyPDF_eq_zero_iff {f g : α → ℝ} (hf : IsPDF μ f) (hg : IsPDF μ g)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) (hint : Integrable (fun x => f x * log (f x / g x)) μ) :
    relEntropyPDF μ f g = 0 ↔ f =ᵐ[μ] g := by
  set k : α → ℝ := fun x => f x * log (f x / g x) - (f x - g x)
  have hk : Integrable k μ := hint.sub (hf.integrable.sub hg.integrable)
  have hk0 : 0 ≤ᵐ[μ] k := hfg.mono fun x hx => by
    simp only [Pi.zero_apply, k, sub_nonneg]
    exact sub_le_mul_log_div (hf.nonneg x) (hg.nonneg x) hx
  have hfg' : Integrable (fun x => f x - g x) μ := hf.integrable.sub hg.integrable
  have hint_k : ∫ x, k x ∂μ = relEntropyPDF μ f g := by
    rw [integral_sub hint hfg', integral_sub hf.integrable hg.integrable, hf.integral_eq_one,
      hg.integral_eq_one, sub_self, sub_zero]
    rfl
  rw [← hint_k, integral_eq_zero_iff_of_nonneg_ae hk0 hk]
  constructor
  · intro h
    filter_upwards [h, hfg] with x hx hxg
    simp only [Pi.zero_apply, k, sub_eq_zero] at hx
    exact (mul_log_div_eq_sub_iff (hf.nonneg x) (hg.nonneg x) hxg).1 hx
  · intro h
    filter_upwards [h, hfg] with x hx hxg
    simp only [Pi.zero_apply, k, sub_eq_zero]
    exact (mul_log_div_eq_sub_iff (hf.nonneg x) (hg.nonneg x) hxg).2 hx

/-- Pointwise, `f log (f/g) = -(-f log f) - f log g` where `g = 0 → f = 0`. -/
lemma mul_log_div_eq {a b : ℝ} (hab : b = 0 → a = 0) :
    a * log (a / b) = -negMulLog a - a * log b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hb : b ≠ 0 := fun h => ha (hab h)
    rw [log_div ha hb, negMulLog]
    ring

/-- `D(f‖g) = -h(f) - ∫ f log g`. -/
theorem relEntropyPDF_eq {f g : α → ℝ} (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (h1 : Integrable (fun x => negMulLog (f x)) μ) (h2 : Integrable (fun x => f x * log (g x)) μ) :
    relEntropyPDF μ f g = -diffEntropy μ f - ∫ x, f x * log (g x) ∂μ := by
  have h1' : Integrable (fun x => -negMulLog (f x)) μ := h1.neg
  rw [relEntropyPDF, integral_congr_ae (hfg.mono fun _ hx => mul_log_div_eq hx),
    integral_sub h1' h2, integral_neg, diffEntropy]

lemma integrable_mul_log_div {f g : α → ℝ} (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (h1 : Integrable (fun x => negMulLog (f x)) μ) (h2 : Integrable (fun x => f x * log (g x)) μ) :
    Integrable (fun x => f x * log (f x / g x)) μ :=
  (h1.neg.sub h2).congr (hfg.mono fun _ hx => (mul_log_div_eq hx).symm)

/-- **Theorem 8.6.1**, as a bound on the differential entropy: for densities `f ≪ g`,
`h(f) ≤ -∫ f log g`. -/
theorem diffEntropy_le_crossEntropy {f g : α → ℝ} (hf : IsPDF μ f) (hg : IsPDF μ g)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) (h1 : Integrable (fun x => negMulLog (f x)) μ)
    (h2 : Integrable (fun x => f x * log (g x)) μ) :
    diffEntropy μ f ≤ -∫ x, f x * log (g x) ∂μ := by
  have h := relEntropyPDF_nonneg hf hg hfg (integrable_mul_log_div hfg h1 h2)
  rw [relEntropyPDF_eq hfg h1 h2] at h
  linarith

/-- **Theorem 8.6.1 (equality case)**: `h(f) = -∫ f log g` iff `f = g` almost everywhere. -/
theorem diffEntropy_eq_crossEntropy_iff {f g : α → ℝ} (hf : IsPDF μ f) (hg : IsPDF μ g)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) (h1 : Integrable (fun x => negMulLog (f x)) μ)
    (h2 : Integrable (fun x => f x * log (g x)) μ) :
    diffEntropy μ f = -∫ x, f x * log (g x) ∂μ ↔ f =ᵐ[μ] g := by
  rw [← relEntropyPDF_eq_zero_iff hf hg hfg (integrable_mul_log_div hfg h1 h2),
    relEntropyPDF_eq hfg h1 h2]
  constructor <;> intro h <;> linarith

/-! ### Quantization decreases the relative entropy -/

/-- `t log c + t - s c ≤ t log (t/s)` for `t ≥ 0` and `s, c > 0`. -/
lemma mul_log_add_sub_le_mul_log_div {t s c : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (hc : 0 < c) :
    t * log c + t - s * c ≤ t * log (t / s) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [zero_mul, zero_add, zero_sub, Left.neg_nonpos_iff]
    positivity
  have h := sub_le_mul_log_div ht.le (mul_pos hs hc).le fun h => absurd h (mul_pos hs hc).ne'
  rw [show t / (s * c) = t / s / c by ring, log_div (div_pos ht hs).ne' hc.ne'] at h
  linarith

/-- The integral is the sum of the integrals over the cells `g⁻¹{i}` of a finite partition. -/
lemma sum_setIntegral_preimage_singleton {F : α → ℝ} (hF : Integrable F μ) {ι : Type*}
    [Fintype ι] {g : α → ι} (hg : ∀ i, MeasurableSet (g ⁻¹' {i})) :
    ∑ i, ∫ x in g ⁻¹' {i}, F x ∂μ = ∫ x, F x ∂μ := by
  classical
  have e : ∀ x, F x = ∑ i, (g ⁻¹' {i}).indicator F x := by
    intro x
    rw [Finset.sum_eq_single (g x) (fun i _ hi => Set.indicator_of_notMem
      (fun h => hi (by simpa using h.symm)) _) (by simp)]
    exact (Set.indicator_of_mem (by simp) _).symm
  calc ∑ i, ∫ x in g ⁻¹' {i}, F x ∂μ = ∑ i, ∫ x, (g ⁻¹' {i}).indicator F x ∂μ :=
        Finset.sum_congr rfl fun i _ => (integral_indicator (hg i)).symm
    _ = ∫ x, ∑ i, (g ⁻¹' {i}).indicator F x ∂μ :=
        (integral_finsetSum _ fun i _ => hF.indicator (hg i)).symm
    _ = ∫ x, F x ∂μ := integral_congr_ae (Eventually.of_forall fun x => (e x).symm)

/-- The probability `P(A) log (P(A)/Q(A))` of one cell is at most `∫_A p log (p/q)`. -/
lemma setIntegral_mul_log_div_ge {p q : α → ℝ} (hp : IsPDF μ p) (hq : IsPDF μ q)
    (hqpos : ∀ x, 0 < q x) (hint : Integrable (fun x => p x * log (p x / q x)) μ) {A : Set α}
    (hA : MeasurableSet A) :
    (∫ x in A, p x ∂μ) * log ((∫ x in A, p x ∂μ) / ∫ x in A, q x ∂μ) ≤
      ∫ x in A, p x * log (p x / q x) ∂μ := by
  set a := ∫ x in A, p x ∂μ
  set b := ∫ x in A, q x ∂μ
  have ha : 0 ≤ a := setIntegral_nonneg hA fun x _ => hp.nonneg x
  rcases ha.eq_or_lt with ha0 | ha
  · -- `p = 0` almost everywhere on `A`.
    have h0 : p =ᵐ[μ.restrict A] 0 := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall hp.nonneg) hp.integrable.integrableOn).1 ha0.symm
    rw [← ha0, zero_mul]
    refine le_of_eq (integral_eq_zero_of_ae ?_).symm
    filter_upwards [h0] with x hx
    simp [hx]
  have hb : 0 < b := by
    rcases (setIntegral_nonneg hA fun x _ => (hq.nonneg x)).eq_or_lt with hb | hb
    · exfalso
      have h0 : q =ᵐ[μ.restrict A] 0 := (setIntegral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall hq.nonneg) hq.integrable.integrableOn).1 hb.symm
      have hall : ∀ᵐ x ∂μ.restrict A, False := h0.mono fun x hx => (hqpos x).ne' hx
      have hμA : μ.restrict A = 0 := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hall)
      have : a = 0 := by simp only [a, hμA, integral_zero_measure]
      exact ha.ne' this
    · exact hb
  set c := a / b
  have hc : 0 < c := div_pos ha hb
  have i3 : IntegrableOn (fun x => p x * log c) A μ := (hp.integrable.mul_const _).integrableOn
  have i4 : IntegrableOn p A μ := hp.integrable.integrableOn
  have i1 : IntegrableOn (fun x => p x * log c + p x) A μ := i3.add i4
  have i2 : IntegrableOn (fun x => q x * c) A μ := (hq.integrable.mul_const _).integrableOn
  have i5 : IntegrableOn (fun x => p x * log c + p x - q x * c) A μ := i1.sub i2
  have hmono := setIntegral_mono_on i5 hint.integrableOn hA fun x _ =>
    mul_log_add_sub_le_mul_log_div (hp.nonneg x) (hqpos x) hc
  rw [integral_sub i1 i2, integral_add i3 i4, integral_mul_const, integral_mul_const] at hmono
  have hcb : b * c = a := by simp only [c]; field_simp
  calc a * log (a / b) = a * log c + a - b * c := by rw [hcb]; ring
    _ ≤ _ := hmono

/-- **Quantization decreases the relative entropy.** If the measurable map `g` partitions the space
into finitely many cells `Aᵢ = g⁻¹{i}`, then `∑ᵢ P(Aᵢ) log (P(Aᵢ)/Q(Aᵢ)) ≤ D(p‖q)`, where
`P(A) = ∫_A p` and `Q(A) = ∫_A q`. -/
theorem sum_mul_log_div_le_relEntropyPDF {p q : α → ℝ} (hp : IsPDF μ p) (hq : IsPDF μ q)
    (hqpos : ∀ x, 0 < q x) (hint : Integrable (fun x => p x * log (p x / q x)) μ)
    {ι : Type*} [Fintype ι] {g : α → ι} (hg : ∀ i, MeasurableSet (g ⁻¹' {i})) :
    ∑ i, (∫ x in g ⁻¹' {i}, p x ∂μ) *
        log ((∫ x in g ⁻¹' {i}, p x ∂μ) / ∫ x in g ⁻¹' {i}, q x ∂μ) ≤
      relEntropyPDF μ p q := by
  have hsplit : relEntropyPDF μ p q = ∑ i, ∫ x in g ⁻¹' {i}, p x * log (p x / q x) ∂μ :=
    (sum_setIntegral_preimage_singleton hint hg).symm
  rw [hsplit]
  exact Finset.sum_le_sum fun i _ => setIntegral_mul_log_div_ge hp hq hqpos hint (hg i)

end InfoTheory
