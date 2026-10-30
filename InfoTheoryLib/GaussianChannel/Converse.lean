/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.DifferentialEntropy.AEP
public import InfoTheoryLib.DifferentialEntropy.RelativeEntropy
public import InfoTheoryLib.GaussianChannel.Code

/-!
# The converse to the coding theorem for Gaussian channels

Every `(M, n)` code for the Gaussian channel with power constraint `P` and noise variance `N`
satisfies `(1 - Pₑ^(n)) log M ≤ log 2 + n · ½ log (1 + P/N)`, so achievable rates are at most
`C = ½ log (1 + P/N)`.

## Main definitions

* `shiftedNoisePDF N x`: the density `∏ᵢ φ_N(yᵢ - xᵢ)` of the output `xⁿ + Zⁿ`.
* `GaussianCode.transProb`, `GaussianCode.msgLaw`: the joint law of a uniformly distributed
  message `W` and the decoded message `Ŵ`.

## Main statements

* `noiseLaw_real_eq`: `Pr{xⁿ + Zⁿ ∈ A} = ∫_A ∏ᵢ φ_N(yᵢ - xᵢ) dy`.
* `relEntropyPDF_shiftedNoisePDF`: the relative entropy between `N(xⁿ, N I)` and `N(0, S I)` is
  `∑ᵢ (½ log (S/N) - ½ + (xᵢ² + N)/(2S))`.
* `GaussianCode.mutualInfo_msgLaw_le`: (9.40)–(9.53), `I(W; Ŵ) ≤ n · ½ log (1 + P/N)`.
* `GaussianCode.one_sub_avgErrProb_mul_log_le`: (9.37)–(9.53),
  `(1 - Pₑ^(n)) log M ≤ log 2 + n · ½ log (1 + P/N)`.
* `IsAchievableGaussianRate.le`: the converse to Theorem 9.1.1, `R ≤ ½ log (1 + P/N)`.

## Implementation notes

The book bounds `I(W; Ŵ) ≤ I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)` and then each `I(Xᵢ; Yᵢ)` by the entropy of
the normal distribution with the same variance. We bound `I(W; Ŵ)` directly: comparing the law
of `Ŵ` with the law `Q` of `g(Ỹⁿ)` for `Ỹⁿ ∼ N(0, (P + N) I)` gives
`I(W; Ŵ) ≤ (1/M) ∑_w D(p(ŵ | w) ‖ Q)` (`mutualInfo_le_sum_log_div`), and quantizing by the decoder
decreases the relative entropy (`sum_mul_log_div_le_relEntropyPDF`), so
`I(W; Ŵ) ≤ (1/M) ∑_w D(N(xⁿ(w), N I) ‖ N(0, (P + N) I))`. The average power of the codewords
enters as in (9.46)–(9.51). Only finite (discrete) entropies appear besides these relative
entropies.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.2
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Product densities on `ℝⁿ` -/

/-- `∫ ∏ⱼ gⱼ(yⱼ) · ℓ(yₖ) dy = ∫ gₖ ℓ` when each `gⱼ` integrates to `1`. -/
lemma integral_prod_mul_apply {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ}
    (hg : ∀ j, Integrable (g j)) (hg1 : ∀ j, ∫ t, g j t = 1) (k : ι) {ℓ : ℝ → ℝ}
    (hℓ : Integrable fun t => g k t * ℓ t) :
    Integrable (fun y : ι → ℝ => (∏ j, g j (y j)) * ℓ (y k)) ∧
      ∫ y : ι → ℝ, (∏ j, g j (y j)) * ℓ (y k) = ∫ t, g k t * ℓ t := by
  classical
  set h : ι → ℝ → ℝ := Function.update g k fun t => g k t * ℓ t
  have hk : h k = fun t => g k t * ℓ t := Function.update_self _ _ _
  have hj : ∀ j ∈ univ.erase k, h j = g j := fun j hj =>
    Function.update_of_ne (ne_of_mem_erase hj) _ _
  have e : (fun y : ι → ℝ => (∏ j, g j (y j)) * ℓ (y k)) = fun y => ∏ j, h j (y j) := by
    funext y
    have hp : ∏ j ∈ univ.erase k, h j (y j) = ∏ j ∈ univ.erase k, g j (y j) :=
      prod_congr rfl fun j hj' => by rw [hj j hj']
    rw [← mul_prod_erase univ (fun j => h j (y j)) (mem_univ k),
      ← mul_prod_erase univ (fun j => g j (y j)) (mem_univ k), hp]
    simp only [hk]
    ring
  have hint : ∀ j, Integrable (h j) := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      rw [hk]
      exact hℓ
    · rw [hj j (mem_erase.2 ⟨hjk, mem_univ j⟩)]
      exact hg j
  rw [e]
  refine ⟨Integrable.fintype_prod hint, ?_⟩
  rw [integral_fintype_prod_volume_eq_prod, ← mul_prod_erase univ _ (mem_univ k), hk,
    prod_eq_one fun j hj' => by rw [hj j hj', hg1], mul_one]

/-- A product of densities is a density on `ℝⁿ`. -/
lemma isPDF_prod_apply {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ} (hg : ∀ j, IsPDF volume (g j)) :
    IsPDF volume fun y : ι → ℝ => ∏ j, g j (y j) :=
  ⟨Finset.measurable_prod _ fun j _ => (hg j).measurable.comp (measurable_pi_apply j),
    fun y => prod_nonneg fun j _ => (hg j).nonneg _,
    Integrable.fintype_prod fun j => (hg j).integrable,
    by rw [integral_fintype_prod_volume_eq_prod]; simp [fun j => (hg j).integral_eq_one]⟩

/-- The density `∏ᵢ φ_N(yᵢ - xᵢ)` of the output `xⁿ + Zⁿ` of the Gaussian channel. -/
def shiftedNoisePDF (N : ℝ≥0) {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 N (y i - x i)

lemma shiftedNoisePDF_isPDF {N : ℝ≥0} (hN : N ≠ 0) {n : ℕ} (x : Fin n → ℝ) :
    IsPDF volume (shiftedNoisePDF N x) :=
  isPDF_prod_apply fun i => ⟨(measurable_gaussianPDFReal 0 N).comp (measurable_id.sub_const _),
    fun _ => gaussianPDFReal_nonneg _ _ _, (gaussianPDFReal_sub_moments hN (x i)).1,
    (gaussianPDFReal_sub_moments hN (x i)).2.1⟩

lemma shiftedNoisePDF_pos {N : ℝ≥0} (hN : N ≠ 0) {n : ℕ} (x y : Fin n → ℝ) :
    0 < shiftedNoisePDF N x y :=
  prod_pos fun _ _ => gaussianPDFReal_pos _ _ _ hN

/-- The noise law `N(0, N)ⁿ` has density `∏ᵢ φ_N(zᵢ)`. -/
lemma noiseLaw_eq_pdfMeasure {N : ℝ≥0} (hN : N ≠ 0) (n : ℕ) :
    noiseLaw N n = pdfMeasure volume (prodPDF (gaussianPDFReal 0 N) n) := by
  have h : gaussianReal 0 N = pdfMeasure volume (gaussianPDFReal 0 N) := by
    rw [gaussianReal_of_var_ne_zero 0 hN]
    rfl
  rw [noiseLaw, h, pi_pdfMeasure (gaussianPDFReal_isPDF 0 hN) n]
  rfl

/-- `Pr{xⁿ + Zⁿ ∈ A} = ∫_A ∏ᵢ φ_N(yᵢ - xᵢ) dy`. -/
lemma noiseLaw_real_eq {N : ℝ≥0} (hN : N ≠ 0) {n : ℕ} (x : Fin n → ℝ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    (noiseLaw N n).real {z | x + z ∈ A} = ∫ y in A, shiftedNoisePDF N x y := by
  have hS : MeasurableSet {z : Fin n → ℝ | x + z ∈ A} := (measurable_const_add x) hA
  have hpdf : IsPDF volume (prodPDF (gaussianPDFReal 0 N) n) :=
    (gaussianPDFReal_isPDF 0 hN).prodPDF n
  rw [measureReal_def, noiseLaw_eq_pdfMeasure hN, pdfMeasure_apply_eq_ofReal hpdf hS,
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun z _ => hpdf.nonneg z)]
  set F := A.indicator (shiftedNoisePDF N x)
  have e : ∀ z, {z : Fin n → ℝ | x + z ∈ A}.indicator (prodPDF (gaussianPDFReal 0 N) n) z =
      F (x + z) := by
    intro z
    simp only [F]
    by_cases hz : x + z ∈ A
    · rw [Set.indicator_of_mem (show z ∈ {z | x + z ∈ A} from hz), Set.indicator_of_mem hz]
      simp [prodPDF, shiftedNoisePDF]
    · rw [Set.indicator_of_notMem (show z ∉ {z | x + z ∈ A} from hz), Set.indicator_of_notMem hz]
  rw [← integral_indicator hS, ← integral_indicator hA]
  change ∫ z, {z : Fin n → ℝ | x + z ∈ A}.indicator (prodPDF (gaussianPDFReal 0 N) n) z = ∫ y, F y
  simp_rw [e]
  exact integral_add_left_eq_self F x

/-- The relative entropy between the normal densities `N(xⁿ, N I)` and `N(0, S I)` on `ℝⁿ`:
`∑ᵢ (½ log (S/N) - ½ + (xᵢ² + N)/(2S))`. -/
lemma relEntropyPDF_shiftedNoisePDF {N S : ℝ≥0} (hN : N ≠ 0) (hS : S ≠ 0) {n : ℕ}
    (x : Fin n → ℝ) :
    Integrable (fun y => shiftedNoisePDF N x y *
        log (shiftedNoisePDF N x y / shiftedNoisePDF S 0 y)) ∧
      relEntropyPDF volume (shiftedNoisePDF N x) (shiftedNoisePDF S 0) =
        ∑ i, (log (S / N) / 2 - 1 / 2 + (x i ^ 2 + N) / (2 * S)) := by
  set g : Fin n → ℝ → ℝ := fun j t => gaussianPDFReal 0 N (t - x j)
  set ℓ : Fin n → ℝ → ℝ := fun j t => log (gaussianPDFReal 0 N (t - x j) / gaussianPDFReal 0 S t)
  have hlog : ∀ y : Fin n → ℝ,
      log (shiftedNoisePDF N x y / shiftedNoisePDF S 0 y) = ∑ j, ℓ j (y j) := by
    intro y
    simp only [shiftedNoisePDF, Pi.zero_apply, sub_zero, ← prod_div_distrib]
    exact log_prod fun j _ => (div_pos (gaussianPDFReal_pos _ _ _ hN)
      (gaussianPDFReal_pos _ _ _ hS)).ne'
  have hterm : ∀ k, Integrable (fun y : Fin n → ℝ => (∏ j, g j (y j)) * ℓ k (y k)) ∧
      ∫ y : Fin n → ℝ, (∏ j, g j (y j)) * ℓ k (y k) =
        log (S / N) / 2 - 1 / 2 + (x k ^ 2 + N) / (2 * S) := by
    intro k
    obtain ⟨h1, h2⟩ := integral_prod_mul_apply (g := g)
      (fun j => (gaussianPDFReal_sub_moments hN (x j)).1)
      (fun j => (gaussianPDFReal_sub_moments hN (x j)).2.1) k
      (integral_gaussianPDFReal_sub_mul_log_div hN hS (x k)).1
    exact ⟨h1, h2.trans (integral_gaussianPDFReal_sub_mul_log_div hN hS (x k)).2⟩
  have e : ∀ y, shiftedNoisePDF N x y * log (shiftedNoisePDF N x y / shiftedNoisePDF S 0 y) =
      ∑ k, (∏ j, g j (y j)) * ℓ k (y k) := by
    intro y
    rw [hlog, mul_sum]
    rfl
  have hint : Integrable fun y : Fin n → ℝ => ∑ k, (∏ j, g j (y j)) * ℓ k (y k) :=
    integrable_finsetSum _ fun k _ => (hterm k).1
  refine ⟨hint.congr (Eventually.of_forall fun y => (e y).symm), ?_⟩
  rw [relEntropyPDF, integral_congr_ae (Eventually.of_forall e),
    integral_finsetSum _ fun k _ => (hterm k).1]
  exact sum_congr rfl fun k _ => (hterm k).2

/-! ### The converse -/

namespace GaussianCode

variable {M n : ℕ} (N : ℝ≥0) (c : GaussianCode M n)

/-- The transition probabilities `p(ŵ | w) = Pr{g(xⁿ(w) + Zⁿ) = ŵ}` from the sent message to the
decoded message. -/
def transProb (w ŵ : Fin M) : ℝ := (noiseLaw N n).real {z | c.dec (c.enc w + z) = ŵ}

/-- The joint law `p(w, ŵ) = (1/M) p(ŵ | w)` of a uniformly distributed message `W` and the decoded
message `Ŵ = g(Yⁿ)`. -/
def msgLaw (p : Fin M × Fin M) : ℝ := (M : ℝ)⁻¹ * c.transProb N p.1 p.2

lemma measurableSet_cell (ŵ : Fin M) : MeasurableSet (c.dec ⁻¹' {ŵ}) :=
  c.measurable_dec (measurableSet_singleton ŵ)

lemma measurable_dec_add (w : Fin M) : Measurable fun z => c.dec (c.enc w + z) :=
  c.measurable_dec.comp (measurable_const_add _)

lemma sum_transProb (w : Fin M) : ∑ ŵ, c.transProb N w ŵ = 1 := by
  have h := sum_measureReal_preimage_singleton (μ := noiseLaw N n) univ
    (f := fun z => c.dec (c.enc w + z)) fun ŵ _ =>
      (c.measurable_dec_add w) (measurableSet_singleton ŵ)
  simp only [coe_univ, Set.preimage_univ, probReal_univ] at h
  exact h

lemma sum_transProb_erase (w : Fin M) :
    ∑ ŵ ∈ univ.erase w, c.transProb N w ŵ = c.condErrProb N w := by
  have h := sum_measureReal_preimage_singleton (μ := noiseLaw N n) (univ.erase w)
    (f := fun z => c.dec (c.enc w + z)) fun ŵ _ =>
      (c.measurable_dec_add w) (measurableSet_singleton ŵ)
  refine h.trans ?_
  rw [condErrProb]
  congr 1
  ext z
  simp

lemma msgLaw_isPMF (hM : 0 < M) : IsPMF (c.msgLaw N) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨fun p => mul_nonneg (by positivity) measureReal_nonneg, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [msgLaw, ← mul_sum, sum_transProb, mul_one, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

lemma dist_fst_msgLaw (w : Fin M) : dist (c.msgLaw N) Prod.fst w = (M : ℝ)⁻¹ := by
  rw [dist_fst]
  simp only [msgLaw, ← mul_sum, sum_transProb, mul_one]

/-- With a uniformly distributed message, `Pr{Ŵ ≠ W} = Pₑ^(n)`. -/
lemma errProb_msgLaw : errProb (c.msgLaw N) Prod.fst Prod.snd id = c.avgErrProb N := by
  classical
  simp only [errProb, Fintype.sum_prod_type, id, msgLaw, avgErrProb]
  rw [sum_div]
  refine sum_congr rfl fun w _ => ?_
  rw [← sum_transProb_erase, ← sum_filter, filter_ne', sum_div]
  exact sum_congr rfl fun ŵ _ => by ring

lemma entropy_fst_msgLaw (hM : 0 < M) : H[Prod.fst ; c.msgLaw N] = log M := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hd : dist (c.msgLaw N) Prod.fst = uniformPMF (Fin M) := by
    funext w
    rw [dist_fst_msgLaw, uniformPMF, Fintype.card_fin, one_div]
  rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_fin]

/-- **(9.40)–(9.53)** For a code satisfying the power constraint `P`, the message and its estimate
have `I(W; Ŵ) ≤ n · ½ log (1 + P/N)`. -/
theorem mutualInfo_msgLaw_le (hN : N ≠ 0) {P : ℝ≥0} (hc : c.SatisfiesPower P) (hM : 0 < M) :
    I[Prod.fst : Prod.snd ; c.msgLaw N] ≤ n * (1 / 2 * log (1 + P / N)) := by
  have hμ := c.msgLaw_isPMF N hM
  have hN' : (0 : ℝ) < N := by positivity
  set S : ℝ≥0 := P + N
  have hS' : (S : ℝ) = P + N := NNReal.coe_add _ _
  have hSpos : (0 : ℝ) < S := by rw [hS']; positivity
  have hS : S ≠ 0 := fun h => by rw [h, NNReal.coe_zero] at hSpos; exact lt_irrefl 0 hSpos
  set q : (Fin n → ℝ) → ℝ := shiftedNoisePDF S 0
  have hq := shiftedNoisePDF_isPDF hS (0 : Fin n → ℝ)
  have hqpos := shiftedNoisePDF_pos hS (0 : Fin n → ℝ)
  -- The law `Q` of the decoded message when the output is `N(0, S I)`.
  set Q : Fin M → ℝ := fun ŵ => ∫ y in c.dec ⁻¹' {ŵ}, q y
  have hQ : IsPMF Q := ⟨fun ŵ => setIntegral_nonneg (c.measurableSet_cell ŵ) fun y _ =>
    hq.nonneg y, by rw [sum_setIntegral_preimage_singleton hq.integrable c.measurableSet_cell,
      hq.integral_eq_one]⟩
  have hT : ∀ w ŵ, c.transProb N w ŵ = ∫ y in c.dec ⁻¹' {ŵ}, shiftedNoisePDF N (c.enc w) y :=
    fun w ŵ => noiseLaw_real_eq hN (c.enc w) (c.measurableSet_cell ŵ)
  have hQμ : ∀ w ŵ, Q ŵ = 0 → c.msgLaw N (w, ŵ) = 0 := by
    intro w ŵ h
    have h0 : q =ᵐ[volume.restrict (c.dec ⁻¹' {ŵ})] 0 := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall hq.nonneg) hq.integrable.integrableOn).1 h
    have hall : ∀ᵐ y ∂volume.restrict (c.dec ⁻¹' {ŵ}), False :=
      h0.mono fun y hy => (hqpos y).ne' hy
    have hr : volume.restrict (c.dec ⁻¹' {ŵ}) = 0 :=
      ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hall)
    simp [msgLaw, hT, hr]
  have hgold := mutualInfo_le_sum_log_div hμ hQ hQμ
  have hM' : (M : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hM.ne')
  -- `I(W; Ŵ) ≤ (1/M) ∑_w ∑_ŵ p(ŵ | w) log (p(ŵ | w)/Q(ŵ))`.
  have hrhs : ∑ w, ∑ ŵ, c.msgLaw N (w, ŵ) *
      log (c.msgLaw N (w, ŵ) / (dist (c.msgLaw N) Prod.fst w * Q ŵ)) =
      (M : ℝ)⁻¹ * ∑ w, ∑ ŵ, c.transProb N w ŵ * log (c.transProb N w ŵ / Q ŵ) := by
    rw [mul_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ŵ _ => ?_
    simp only [msgLaw, dist_fst_msgLaw]
    rw [mul_div_mul_left _ _ hM', mul_assoc]
  -- Quantization by the decoder: `∑_ŵ p(ŵ | w) log (p(ŵ | w)/Q(ŵ)) ≤ D(N(xⁿ(w), N I) ‖ N(0, S I))`.
  have hdp : ∀ w, ∑ ŵ, c.transProb N w ŵ * log (c.transProb N w ŵ / Q ŵ) ≤
      ∑ i, (log (S / N) / 2 - 1 / 2 + (c.enc w i ^ 2 + N) / (2 * S)) := by
    intro w
    obtain ⟨hint, heq⟩ := relEntropyPDF_shiftedNoisePDF hN hS (c.enc w)
    rw [← heq]
    simp only [hT]
    exact sum_mul_log_div_le_relEntropyPDF (shiftedNoisePDF_isPDF hN _) hq hqpos hint
      c.measurableSet_cell
  -- The power constraint: each codeword contributes at most `n · ½ log (S/N)`.
  have hpow : ∀ w, ∑ i, (log (S / N) / 2 - 1 / 2 + (c.enc w i ^ 2 + N) / (2 * S)) ≤
      n * (1 / 2 * log (1 + P / N)) := by
    intro w
    have hcw := hc w
    have e1 : ∑ i, (log (S / N) / 2 - 1 / 2 + (c.enc w i ^ 2 + N) / (2 * S)) =
        n * (log (S / N) / 2 - 1 / 2 + N / (2 * S)) + (∑ i, c.enc w i ^ 2) / (2 * S) := by
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_div]
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have e2 : log (S / N) = log (1 + P / N) := by
      rw [hS', add_div, div_self hN'.ne', add_comm]
    rw [e1, e2]
    have h3 : (∑ i, c.enc w i ^ 2) / (2 * S) ≤ n * P / (2 * S) :=
      div_le_div_of_nonneg_right hcw (by positivity)
    have h4 : (n : ℝ) * (log (1 + P / N) / 2 - 1 / 2 + N / (2 * S)) + n * P / (2 * S) =
        n * (1 / 2 * log (1 + P / N)) := by
      rw [hS']
      field_simp
      ring
    linarith
  calc I[Prod.fst : Prod.snd ; c.msgLaw N]
      ≤ (M : ℝ)⁻¹ * ∑ w, ∑ ŵ, c.transProb N w ŵ * log (c.transProb N w ŵ / Q ŵ) :=
        hgold.trans_eq hrhs
    _ ≤ (M : ℝ)⁻¹ * ∑ _w : Fin M, n * (1 / 2 * log (1 + P / N)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun w _ => (hdp w).trans (hpow w))
          (by positivity)
    _ = n * (1 / 2 * log (1 + P / N)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (by exact_mod_cast hM.ne'), one_mul]

/-- **(9.37)–(9.53)** Every `(M, n)` code satisfying the power constraint `P` has
`(1 - Pₑ^(n)) log M ≤ log 2 + n · ½ log (1 + P/N)`. -/
theorem one_sub_avgErrProb_mul_log_le (hN : N ≠ 0) {P : ℝ≥0} (hc : c.SatisfiesPower P)
    (hM : 0 < M) : (1 - c.avgErrProb N) * log M ≤ log 2 + n * (1 / 2 * log (1 + P / N)) := by
  have hμ := c.msgLaw_isPMF N hM
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ (Prod.fst : Fin M × Fin M → Fin M)
    Prod.snd
  have h2 := fano_weak hμ (Prod.fst : Fin M × Fin M → Fin M) Prod.snd id
  rw [c.errProb_msgLaw N, Fintype.card_fin] at h2
  have h3 := c.mutualInfo_msgLaw_le N hN hc hM
  rw [c.entropy_fst_msgLaw N hM] at h1
  linarith

end GaussianCode

/-- **Theorem 9.1.1 (converse), Section 9.2.** A rate achievable for the Gaussian channel with
power constraint `P` and noise variance `N` is at most `C = ½ log (1 + P/N)`. -/
theorem IsAchievableGaussianRate.le {P N : ℝ≥0} (hN : N ≠ 0) {R : ℝ}
    (h : IsAchievableGaussianRate P N R) : R ≤ 1 / 2 * log (1 + P / N) := by
  obtain ⟨c, hpow, hc⟩ := h
  have hPe : Tendsto (fun n => (c n).avgErrProb N) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n => (c n).avgErrProb_nonneg N) fun n => (c n).avgErrProb_le_maxErrProb N
  exact le_of_converse_bound hPe
    (fun n => ((c n).avgErrProb_le_maxErrProb N).trans ((c n).maxErrProb_le_one N))
    fun n _ => (c n).one_sub_avgErrProb_mul_log_le N hN (hpow n) (one_le_ceil_exp _)

end InfoTheory
