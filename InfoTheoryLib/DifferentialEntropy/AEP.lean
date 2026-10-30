/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.Basic
public import InfoTheoryLib.ForMathlib.WeakLaw

/-!
# The AEP for continuous random variables

If `X₁, X₂, …` are i.i.d. with density `f`, then `-(1/n) log f(X₁, …, Xₙ) → h(f)`, where
`f(x₁, …, xₙ) = ∏ᵢ f(xᵢ)`. This follows from the strong law of large numbers applied to
`-log f(Xᵢ)`, whose mean is `h(f)`. The typical set `A_ε^(n)` of sequences with sample entropy
within `ε` of `h(f)` has probability close to `1` and volume about `e^{nh(f)}`, and no set of
smaller volume to first order in the exponent has probability close to `1`.

## Main definitions

* `sampleDiffEntropy f n x`: the sample entropy `-(1/n) log f(x₁, …, xₙ)`.
* `diffTypicalSet μ f n ε`: the typical set `A_ε^(n)`, (8.11).

## Main statements

* `pi_pdfMeasure`: the law of `n` i.i.d. draws has density `∏ᵢ f(xᵢ)` with respect to `μⁿ`.
* `tendsto_sampleDiffEntropy_ae`, `tendstoInMeasure_sampleDiffEntropy`: Theorem 8.2.1, the
  sample entropy converges to `h(f)` with probability `1`, hence in probability.
* `eventually_prob_diffTypicalSet_gt`, `volume_diffTypicalSet_le`,
  `eventually_volume_diffTypicalSet_ge`: Theorem 8.2.2.
* `eventually_volume_gt_of_prob_ge`: Theorem 8.2.3, a set of probability at least `1 - δ` has
  volume at least `e^{n(h - δ')}` for `n` large.

## Implementation notes

Logarithms are natural, so the book's `2^{n(h ± ε)}` with `h` in bits is `e^{n(h ± ε)}` with `h`
in nats. The volume of a set `A ⊆ αⁿ` is its measure under the product measure `μⁿ`, which for
`α = ℝ` and `μ` the Lebesgue measure is the volume (8.12). Theorem 8.2.1 is stated for i.i.d.
random variables on any probability space; Theorems 8.2.2 and 8.2.3 use the product law
`(f dμ)ⁿ` of `n` draws.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 8.2
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Set

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

/-- The probability of a measurable set under the density `f` is `∫_s f dμ`. -/
lemma pdfMeasure_apply_eq_ofReal (hf : IsPDF μ f) {s : Set α} (hs : MeasurableSet s) :
    pdfMeasure μ f s = ENNReal.ofReal (∫ x in s, f x ∂μ) := by
  rw [pdfMeasure, withDensity_apply _ hs, ofReal_integral_eq_lintegral_ofReal
    hf.integrable.integrableOn (Eventually.of_forall hf.nonneg)]

/-- The product density `∏ᵢ f(xᵢ)` of `n` i.i.d. draws. -/
def prodPDF (f : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := ∏ i, f (x i)

variable [SigmaFinite μ]

lemma IsPDF.prodPDF (hf : IsPDF μ f) (n : ℕ) :
    IsPDF (Measure.pi fun _ : Fin n => μ) (InfoTheory.prodPDF f n) :=
  ⟨Finset.measurable_prod _ fun i _ => hf.measurable.comp (measurable_pi_apply i),
    fun x => Finset.prod_nonneg fun i _ => hf.nonneg _,
    Integrable.fintype_prod fun _ => hf.integrable,
    by simp [InfoTheory.prodPDF, integral_fintype_prod_eq_prod, hf.integral_eq_one]⟩

/-- The law of `n` i.i.d. draws with density `f` has density `f(x₁, …, xₙ) = ∏ᵢ f(xᵢ)` with
respect to `μⁿ`. -/
theorem pi_pdfMeasure (hf : IsPDF μ f) (n : ℕ) :
    Measure.pi (fun _ : Fin n => pdfMeasure μ f) =
      pdfMeasure (Measure.pi fun _ => μ) (prodPDF f n) := by
  have := hf.isProbabilityMeasure
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : (Set.univ.pi s).indicator (prodPDF f n) =
      fun x => ∏ i, (s i).indicator f (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) f).symm
    · rw [indicator_of_notMem hx]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi f)).symm
  rw [pdfMeasure_apply_eq_ofReal (hf.prodPDF n) hbox, ← integral_indicator hbox, hind,
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      fun i _ => integral_nonneg fun x => indicator_nonneg (fun y _ => hf.nonneg y) x]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pdfMeasure_apply_eq_ofReal hf (hs i), integral_indicator (hs i)]

/-! ### The AEP -/

omit [MeasurableSpace α] in
/-- The sample entropy `-(1/n) log f(x₁, …, xₙ)` of a sequence. -/
def sampleDiffEntropy (f : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := -log (prodPDF f n x) / n

omit [MeasurableSpace α] in
lemma sampleDiffEntropy_eq_sum {n : ℕ} {x : Fin n → α} (hx : ∀ i, f (x i) ≠ 0) :
    sampleDiffEntropy f n x = (n : ℝ)⁻¹ * ∑ i, -log (f (x i)) := by
  rw [sampleDiffEntropy, prodPDF, log_prod fun i _ => hx i, Finset.sum_neg_distrib]
  ring

omit [SigmaFinite μ] in
/-- `-log f(X)` is integrable for `X ∼ f` when the differential entropy exists, with mean
`E[-log f(X)] = h(f)`. -/
lemma integrable_neg_log_pdfMeasure (hf : IsPDF μ f)
    (hint : Integrable (fun x => negMulLog (f x)) μ) :
    Integrable (fun x => -log (f x)) (pdfMeasure μ f) ∧
      ∫ x, -log (f x) ∂pdfMeasure μ f = diffEntropy μ f := by
  refine ⟨?_, ?_⟩
  · rw [pdfMeasure, integrable_withDensity_iff_integrable_smul' hf.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hint.congr (Eventually.of_forall fun x => ?_)
    simp [negMulLog, ENNReal.toReal_ofReal (hf.nonneg x)]
  · rw [integral_pdfMeasure hf, diffEntropy]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [negMulLog])

omit [SigmaFinite μ] in
/-- A sample from the density `f` lands where `f > 0` with probability `1`. -/
lemma pdfMeasure_ae_ne_zero (hf : IsPDF μ f) : ∀ᵐ x ∂pdfMeasure μ f, f x ≠ 0 := by
  rw [ae_iff]
  have hm : MeasurableSet {x | ¬ f x ≠ 0} := by
    have e : {x | ¬ f x ≠ 0} = f ⁻¹' {0} := by ext; simp
    rw [e]
    exact hf.measurable (measurableSet_singleton 0)
  rw [pdfMeasure_apply_eq_ofReal hf hm, ENNReal.ofReal_eq_zero]
  refine le_of_eq (setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_)
  simpa using hx

omit [SigmaFinite μ] in
/-- **Theorem 8.2.1 (AEP for continuous random variables), with probability `1`.** If
`X₁, X₂, …` are i.i.d. with density `f` and `h(f)` exists, then
`-(1/n) log f(X₁, …, Xₙ) → h(f)` almost surely. -/
theorem tendsto_sampleDiffEntropy_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hf : IsPDF μ f) (hint : Integrable (fun x => negMulLog (f x)) μ)
    {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = pdfMeasure μ f) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sampleDiffEntropy f n fun i => X i ω) atTop
      (𝓝 (diffEntropy μ f)) := by
  set g : α → ℝ := fun x => -log (f x)
  have hg : Measurable g := (measurable_log.comp hf.measurable).neg
  set Y : ℕ → Ω → ℝ := fun i => g ∘ X i
  obtain ⟨hgint, hgmean⟩ := integrable_neg_log_pdfMeasure hf hint
  have hYint : Integrable (Y 0) P := by
    have := (integrable_map_measure hg.aestronglyMeasurable (hX 0).aemeasurable).1
      (by rw [hlaw 0]; exact hgint)
    exact this
  have hYmean : ∫ ω, Y 0 ω ∂P = diffEntropy μ f := by
    rw [← hgmean, ← hlaw 0, integral_map (hX 0).aemeasurable hg.aestronglyMeasurable]
    rfl
  have hindep' : Pairwise fun i j => IndepFun (Y i) (Y j) P := fun i j hij =>
    (hindep.indepFun hij).comp hg hg
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    (⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩ :
      IdentDistrib (X i) (X 0) P P).comp hg
  have hslln := strong_law_ae Y hYint hindep' hident
  have hpos : ∀ᵐ ω ∂P, ∀ i, f (X i ω) ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have h := pdfMeasure_ae_ne_zero hf
    rw [← hlaw i] at h
    exact ae_of_ae_map (hX i).aemeasurable h
  filter_upwards [hslln, hpos] with ω hω hωpos
  rw [hYmean] at hω
  refine hω.congr fun n => ?_
  rw [sampleDiffEntropy_eq_sum fun i => hωpos i, smul_eq_mul,
    ← Fin.sum_univ_eq_sum_range (fun i => Y i ω) n]
  rfl

omit [SigmaFinite μ] in
/-- **Theorem 8.2.1 (AEP for continuous random variables), (8.10).**
`-(1/n) log f(X₁, …, Xₙ) → h(f)` in probability. -/
theorem tendstoInMeasure_sampleDiffEntropy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hf : IsPDF μ f) (hint : Integrable (fun x => negMulLog (f x)) μ)
    {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = pdfMeasure μ f) :
    TendstoInMeasure P (fun n ω => sampleDiffEntropy f n fun i => X i ω) atTop
      fun _ => diffEntropy μ f := by
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_)
    (tendsto_sampleDiffEntropy_ae hf hint hX hindep hlaw)
  have hm : Measurable fun ω => ∏ i : Fin n, f (X i ω) :=
    Finset.measurable_prod Finset.univ fun i _ => hf.measurable.comp (hX i)
  exact ((measurable_log.comp hm).neg.div_const (n : ℝ)).aestronglyMeasurable

/-! ### The typical set -/

/-- **Definition (8.11).** The typical set `A_ε^(n)` with respect to the density `f`: the sequences
in the support with sample entropy within `ε` of `h(f)`,
`|-(1/n) log f(x₁, …, xₙ) - h(f)| ≤ ε`. -/
def diffTypicalSet (μ : Measure α) (f : α → ℝ) (n : ℕ) (ε : ℝ) : Set (Fin n → α) :=
  {x | (∀ i, 0 < f (x i)) ∧ |sampleDiffEntropy f n x - diffEntropy μ f| ≤ ε}

omit [SigmaFinite μ] in
lemma measurableSet_diffTypicalSet (hf : Measurable f) (n : ℕ) (ε : ℝ) :
    MeasurableSet (diffTypicalSet μ f n ε) := by
  have h1 : MeasurableSet {x : Fin n → α | ∀ i, 0 < f (x i)} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (hf.comp (measurable_pi_apply i))
  have hS : Measurable (sampleDiffEntropy f n) :=
    (measurable_log.comp (Finset.measurable_prod Finset.univ fun i _ =>
      hf.comp (measurable_pi_apply i))).neg.div_const _
  exact h1.inter (measurableSet_le ((hS.sub_const _).abs) measurable_const)

omit [MeasurableSpace α] [SigmaFinite μ] in
/-- **Theorem 8.2.2, property of typical sequences.** On the typical set,
`e^{-n(h + ε)} ≤ f(x₁, …, xₙ) ≤ e^{-n(h - ε)}`. -/
lemma prodPDF_bounds {n : ℕ} {ε : ℝ} {x : Fin n → α} {h : ℝ} (hpos : ∀ i, 0 < f (x i))
    (hx : |sampleDiffEntropy f n x - h| ≤ ε) :
    exp (-(n * (h + ε))) ≤ prodPDF f n x ∧ prodPDF f n x ≤ exp (-(n * (h - ε))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [prodPDF]
  have hP : 0 < prodPDF f n x := Finset.prod_pos fun i _ => hpos i
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : log (prodPDF f n x) = -(n * sampleDiffEntropy f n x) := by
    rw [sampleDiffEntropy]
    field_simp
  rw [abs_le] at hx
  rw [← exp_log hP, hlog]
  constructor
  · exact exp_le_exp.2 (by nlinarith)
  · exact exp_le_exp.2 (by nlinarith)

/-- `Pr{A} ≤ c · Vol(A)` when the density `f(x₁, …, xₙ)` is at most `c` on `A`. -/
lemma prob_le_mul_volume (hf : IsPDF μ f) {n : ℕ} {A : Set (Fin n → α)} (hA : MeasurableSet A)
    {c : ℝ} (hc : ∀ x ∈ A, prodPDF f n x ≤ c) :
    Measure.pi (fun _ : Fin n => pdfMeasure μ f) A ≤
      ENNReal.ofReal c * Measure.pi (fun _ : Fin n => μ) A := by
  rw [pi_pdfMeasure hf, pdfMeasure, withDensity_apply _ hA, ← setLIntegral_const]
  exact setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal (hc x hx)

/-- `c · Vol(A) ≤ Pr{A}` when the density `f(x₁, …, xₙ)` is at least `c` on `A`. -/
lemma mul_volume_le_prob (hf : IsPDF μ f) {n : ℕ} {A : Set (Fin n → α)} (hA : MeasurableSet A)
    {c : ℝ} (hc : ∀ x ∈ A, c ≤ prodPDF f n x) :
    ENNReal.ofReal c * Measure.pi (fun _ : Fin n => μ) A ≤
      Measure.pi (fun _ : Fin n => pdfMeasure μ f) A := by
  rw [pi_pdfMeasure hf, pdfMeasure, withDensity_apply _ hA, ← setLIntegral_const]
  exact setLIntegral_mono (hf.prodPDF n).measurable.ennreal_ofReal
    fun x hx => ENNReal.ofReal_le_ofReal (hc x hx)

omit [SigmaFinite μ] in
/-- **Theorem 8.2.2 (1).** `Pr{A_ε^(n)} > 1 - ε` for `n` sufficiently large. -/
theorem eventually_prob_diffTypicalSet_gt (hf : IsPDF μ f)
    (hint : Integrable (fun x => negMulLog (f x)) μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      1 - ε < (Measure.pi (fun _ : Fin n => pdfMeasure μ f) (diffTypicalSet μ f n ε)).toReal := by
  have := hf.isProbabilityMeasure
  set ν := pdfMeasure μ f
  set P := Measure.infinitePi fun _ : ℕ => ν
  have hX : ∀ i, Measurable fun ω : ℕ → α => ω i := fun i => measurable_pi_apply i
  have hind : iIndepFun (fun i (ω : ℕ → α) => ω i) P :=
    iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  have hlaw : ∀ i, P.map (fun ω => ω i) = ν := fun i => Measure.infinitePi_map_eval _ i
  have hconv := tendstoInMeasure_sampleDiffEntropy hf hint hX hind hlaw (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε)
  have hpos : ∀ᵐ ω ∂P, ∀ i, f (ω i) ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have h : ∀ᵐ x ∂ν, f x ≠ 0 := pdfMeasure_ae_ne_zero hf
    rw [← hlaw i] at h
    exact ae_of_ae_map (hX i).aemeasurable h
  filter_upwards [(tendsto_order.1 hconv).2 _ (ENNReal.ofReal_pos.2 hε)] with n hn
  have hA := measurableSet_diffTypicalSet (μ := μ) hf.measurable n ε
  have hproj : Measurable fun (ω : ℕ → α) (i : Fin n) => ω i :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  rw [← map_infinitePi_fin ν n, Measure.map_apply hproj hA]
  set G := (fun (ω : ℕ → α) (i : Fin n) => ω i) ⁻¹' diffTypicalSet μ f n ε
  have hG : MeasurableSet G := hproj hA
  set bad := {ω : ℕ → α | ENNReal.ofReal ε ≤
    edist (sampleDiffEntropy f n fun i => ω i) (diffEntropy μ f)}
  have hZ : P {ω | ¬ ∀ i, f (ω i) ≠ 0} = 0 := ae_iff.1 hpos
  have hsub : Gᶜ ⊆ bad ∪ {ω | ¬ ∀ i, f (ω i) ≠ 0} := by
    intro ω hω
    by_cases h0 : ∀ i, f (ω i) ≠ 0
    · left
      simp only [G, mem_compl_iff, mem_preimage, diffTypicalSet, mem_ofPred_eq, not_and_or,
        not_forall, not_le] at hω
      rcases hω with ⟨i, hi⟩ | hω
      · exact absurd (lt_of_le_of_ne (hf.nonneg _) (h0 i).symm) hi
      · simp only [bad, mem_ofPred_eq, edist_dist, Real.dist_eq]
        exact ENNReal.ofReal_le_ofReal hω.le
    · right
      exact h0
  have hbad : P Gᶜ < ENNReal.ofReal ε :=
    lt_of_le_of_lt ((measure_mono hsub).trans ((measure_union_le _ _).trans (by
      rw [hZ, add_zero]))) hn
  have hreal := measureReal_add_measureReal_compl (μ := P) hG
  rw [probReal_univ] at hreal
  have hlt : P.real Gᶜ < ε := ENNReal.toReal_lt_of_lt_ofReal hbad
  change 1 - ε < P.real G
  linarith

/-- **Theorem 8.2.2 (2), (8.13)–(8.17).** `Vol(A_ε^(n)) ≤ e^{n(h(f) + ε)}` for all `n`. -/
theorem volume_diffTypicalSet_le (hf : IsPDF μ f) (n : ℕ) (ε : ℝ) :
    Measure.pi (fun _ : Fin n => μ) (diffTypicalSet μ f n ε) ≤
      ENNReal.ofReal (exp (n * (diffEntropy μ f + ε))) := by
  have := hf.isProbabilityMeasure
  have hA := measurableSet_diffTypicalSet (μ := μ) hf.measurable n ε
  have h := mul_volume_le_prob hf hA (c := exp (-(n * (diffEntropy μ f + ε))))
    fun x hx => (prodPDF_bounds hx.1 hx.2).1
  have h1 := h.trans prob_le_one
  calc Measure.pi (fun _ : Fin n => μ) (diffTypicalSet μ f n ε)
      = ENNReal.ofReal (exp (n * (diffEntropy μ f + ε))) *
          (ENNReal.ofReal (exp (-(n * (diffEntropy μ f + ε)))) *
            Measure.pi (fun _ : Fin n => μ) (diffTypicalSet μ f n ε)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, add_neg_cancel, exp_zero,
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (exp (n * (diffEntropy μ f + ε))) * 1 := by gcongr
    _ = _ := mul_one _

/-- **Theorem 8.2.2 (3), (8.18)–(8.21).** `Vol(A_ε^(n)) ≥ (1 - ε) e^{n(h(f) - ε)}` for `n`
sufficiently large. -/
theorem eventually_volume_diffTypicalSet_ge (hf : IsPDF μ f)
    (hint : Integrable (fun x => negMulLog (f x)) μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((1 - ε) * exp (n * (diffEntropy μ f - ε))) ≤
      Measure.pi (fun _ : Fin n => μ) (diffTypicalSet μ f n ε) := by
  have := hf.isProbabilityMeasure
  filter_upwards [eventually_prob_diffTypicalSet_gt hf hint hε] with n hn
  have hA := measurableSet_diffTypicalSet (μ := μ) hf.measurable n ε
  have h := prob_le_mul_volume hf hA (c := exp (-(n * (diffEntropy μ f - ε))))
    fun x hx => (prodPDF_bounds hx.1 hx.2).2
  have h1 : ENNReal.ofReal (1 - ε) ≤
      ENNReal.ofReal (exp (-(n * (diffEntropy μ f - ε)))) *
        Measure.pi (fun _ : Fin n => μ) (diffTypicalSet μ f n ε) :=
    (ENNReal.ofReal_le_of_le_toReal hn.le).trans h
  calc ENNReal.ofReal ((1 - ε) * exp (n * (diffEntropy μ f - ε)))
      = ENNReal.ofReal (exp (n * (diffEntropy μ f - ε))) * ENNReal.ofReal (1 - ε) := by
        rw [ENNReal.ofReal_mul' (exp_pos _).le, mul_comm]
    _ ≤ ENNReal.ofReal (exp (n * (diffEntropy μ f - ε))) *
          (ENNReal.ofReal (exp (-(n * (diffEntropy μ f - ε)))) *
            Measure.pi (fun _ : Fin n => μ) (diffTypicalSet μ f n ε)) := by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, add_neg_cancel, exp_zero,
          ENNReal.ofReal_one, one_mul]

/-- **Theorem 8.2.3.** The typical set is the smallest set of probability close to `1`, to first
order in the exponent: if `Pr{Bₙ} ≥ 1 - δ` with `δ < 1`, then for any `δ' > 0`,
`Vol(Bₙ) > e^{n(h(f) - δ')}` for `n` sufficiently large. -/
theorem eventually_volume_gt_of_prob_ge (hf : IsPDF μ f)
    (hint : Integrable (fun x => negMulLog (f x)) μ) {δ : ℝ} (hδ : δ < 1) {δ' : ℝ}
    (hδ' : 0 < δ') (B : ∀ n, Set (Fin n → α)) (hB : ∀ n, MeasurableSet (B n))
    (hprob : ∀ n, 1 - δ ≤ (Measure.pi (fun _ : Fin n => pdfMeasure μ f) (B n)).toReal) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (exp (n * (diffEntropy μ f - δ'))) <
      Measure.pi (fun _ : Fin n => μ) (B n) := by
  have := hf.isProbabilityMeasure
  set h := diffEntropy μ f
  set ε := min (δ' / 2) ((1 - δ) / 2)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ' : ε ≤ δ' / 2 := min_le_left _ _
  have hεδ : ε ≤ (1 - δ) / 2 := min_le_right _ _
  -- `e^{-n(δ' - ε)} → 0`.
  have hdecay : ∀ᶠ n : ℕ in atTop, exp (-(n * (δ' - ε))) < (1 - δ) / 2 := by
    have ht : Tendsto (fun n : ℕ => exp (-(n * (δ' - ε)))) atTop (𝓝 0) := by
      refine tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
      exact Tendsto.atTop_mul_const (by linarith) tendsto_natCast_atTop_atTop
    exact (tendsto_order.1 ht).2 _ (by linarith)
  filter_upwards [eventually_prob_diffTypicalSet_gt hf hint hε, hdecay] with n hn hd
  set ν := Measure.pi fun _ : Fin n => pdfMeasure μ f
  set V := Measure.pi fun _ : Fin n => μ
  set A := diffTypicalSet μ f n ε
  have hA := measurableSet_diffTypicalSet (μ := μ) hf.measurable n ε
  -- `Pr{A ∩ B} > (1 - δ)/2`.
  have hAB : (1 - δ) / 2 < ν.real (A ∩ B n) := by
    have h1 : ν.real (B n) ≤ ν.real (A ∩ B n) + ν.real Aᶜ := by
      refine (measureReal_mono (fun x hx => ?_)).trans (measureReal_union_le _ _)
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, hx⟩
      · exact Or.inr hxA
    have h2 := measureReal_add_measureReal_compl (μ := ν) hA
    rw [probReal_univ] at h2
    have h3 : 1 - δ ≤ ν.real (B n) := hprob n
    have h4 : 1 - ε < ν.real A := hn
    linarith
  -- `Pr{A ∩ B} ≤ e^{-n(h - ε)} Vol(A ∩ B) ≤ e^{-n(h - ε)} Vol(B)`.
  have hle : ν (A ∩ B n) ≤ ENNReal.ofReal (exp (-(n * (h - ε)))) * V (B n) :=
    (prob_le_mul_volume hf (hA.inter (hB n)) fun x hx => (prodPDF_bounds hx.1.1 hx.1.2).2).trans
      (by gcongr; exact inter_subset_right)
  rcases eq_or_ne (V (B n)) ⊤ with htop | htop
  · rw [htop]
    exact ENNReal.ofReal_lt_top
  have hVreal : (1 - δ) / 2 < exp (-(n * (h - ε))) * (V (B n)).toReal := by
    have := ENNReal.toReal_mono (by finiteness) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le] at this
    exact hAB.trans_le this
  rw [← ENNReal.ofReal_toReal htop]
  refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (exp_pos _).le |>.2 ?_
  have e1 : exp (n * (h - δ')) = exp (-(n * (δ' - ε))) * exp (n * (h - ε)) := by
    rw [← exp_add]
    ring_nf
  have e2 : exp (-(n * (h - ε))) * exp (n * (h - ε)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  rw [e1]
  calc exp (-(n * (δ' - ε))) * exp (n * (h - ε)) < (1 - δ) / 2 * exp (n * (h - ε)) := by
        gcongr
    _ < exp (-(n * (h - ε))) * (V (B n)).toReal * exp (n * (h - ε)) := by gcongr
    _ = (V (B n)).toReal := by
        rw [mul_comm (exp (-(n * (h - ε)))), mul_assoc, e2, mul_one]

end InfoTheory
