/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.WeakLaw
public import InfoTheoryLib.GaussianChannel.Converse

/-!
# Achievability for the Gaussian channel

Every rate `R < C = ½ log (1 + P/N)` is achievable for the Gaussian channel with power constraint
`P` and noise variance `N`. As in the book, the codewords are drawn i.i.d. from `N(0, P')` with
`P' < P` close to `P`, and codewords violating the power constraint count as errors. Together with
the converse this proves Theorem 9.1.1: the capacity of the Gaussian channel is
`C = ½ log (1 + P/N)`.

## Main definitions

* `infoDensity N S x y`: the information density `∑ᵢ log (φ_N(yᵢ - xᵢ)/φ_S(yᵢ))`.
* `thresholdDecode`: the decoder choosing the first codeword whose information density with the
  output exceeds a threshold.

## Main statements

* `thresholdDecode_ne`: if the decoder errs, then either the sent codeword is below the
  threshold or another codeword is above it.
* `noiseLaw_infoDensity_gt_le`: an independent codeword passes the threshold `γ` with
  probability at most `e^{-γ}`.
* `tendsto_prob_infoDensity_sent_le`, `tendsto_prob_power_gt`: by the law of large numbers, the
  sent codeword passes the threshold and satisfies the power constraint with probability
  tending to `1`.
* `exists_gaussianCode_avgErrProb_le`: the random coding bound.
* `isAchievableGaussianRate_of_lt`: Theorem 9.1.1 (achievability).
* `gaussianOpCapacity_eq`, `gaussianOpCapacity_eq_gaussianInfoCapacity`: Theorem 9.1.1, the
  capacity is `½ log (1 + P/N)`, the information capacity.

## Implementation notes

The book decodes by joint typicality. We decode with a threshold on the information density
`i(xⁿ; yⁿ) = log (f(yⁿ | xⁿ)/f(yⁿ))` instead (Feinstein's decoder), which needs one law of large
numbers instead of three: an error occurs only if `i(Xⁿ(w); Yⁿ) ≤ γ` for the sent codeword, which
has probability tending to `0` when `γ/n < I(X; Y)`, or if `i(Xⁿ(w'); Yⁿ) > γ` for another
codeword, which has probability at most `e^{-γ}` since `Xⁿ(w')` is independent of `Yⁿ`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.1
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InfoTheory

/-- The information density `i(xⁿ; yⁿ) = ∑ᵢ log (φ_N(yᵢ - xᵢ)/φ_S(yᵢ))` of the Gaussian channel
with noise variance `N`, relative to the output law `N(0, S)ⁿ`. -/
def infoDensity (N S : ℝ≥0) {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, log (gaussianPDFReal 0 N (y i - x i) / gaussianPDFReal 0 S (y i))

lemma measurable_infoDensity (N S : ℝ≥0) (n : ℕ) :
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => infoDensity N S p.1 p.2 := by
  unfold infoDensity
  refine Finset.measurable_sum _ fun i _ => measurable_log.comp ?_
  exact ((measurable_gaussianPDFReal 0 N).comp (((measurable_pi_apply i).comp measurable_snd).sub
    ((measurable_pi_apply i).comp measurable_fst))).div
    ((measurable_gaussianPDFReal 0 S).comp ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_infoDensity_right (N S : ℝ≥0) {n : ℕ} (x : Fin n → ℝ) :
    Measurable (infoDensity N S x) := by
  unfold infoDensity
  refine Finset.measurable_sum _ fun i _ => measurable_log.comp ?_
  exact ((measurable_gaussianPDFReal 0 N).comp ((measurable_pi_apply i).sub_const _)).div
    ((measurable_gaussianPDFReal 0 S).comp (measurable_pi_apply i))

lemma measurable_infoDensity_sent (N S : ℝ≥0) (n : ℕ) :
    Measurable fun q : (Fin n → ℝ) × (Fin n → ℝ) => infoDensity N S q.1 (q.1 + q.2) := by
  unfold infoDensity
  refine Finset.measurable_sum _ fun i _ => measurable_log.comp ?_
  have h1 : Measurable fun q : (Fin n → ℝ) × (Fin n → ℝ) => (q.1 + q.2) i :=
    (measurable_pi_apply i).comp (measurable_fst.add measurable_snd)
  have h2 : Measurable fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 i :=
    (measurable_pi_apply i).comp measurable_fst
  exact ((measurable_gaussianPDFReal 0 N).comp (h1.sub h2)).div
    ((measurable_gaussianPDFReal 0 S).comp h1)

/-! ### Threshold decoding -/

section Decoder

variable {M n : ℕ} (θ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (C : Fin M → Fin n → ℝ) (γ : ℝ)

open Classical in
/-- The index of the first codeword `w` with `θ(xⁿ(w), yⁿ) > γ`, or `M` if there is none. -/
def thresholdIndex (y : Fin n → ℝ) : ℕ :=
  Nat.find (⟨M, Or.inl le_rfl⟩ : ∃ k, M ≤ k ∨ ∃ h : k < M, γ < θ (C ⟨k, h⟩) y)

/-- Threshold decoding: the first codeword `w` with `θ(xⁿ(w), yⁿ) > γ`, or `w₀` if there is
none. -/
def thresholdDecode (w₀ : Fin M) (y : Fin n → ℝ) : Fin M :=
  if h : thresholdIndex θ C γ y < M then ⟨_, h⟩ else w₀

lemma measurable_thresholdDecode (hθ : ∀ x, Measurable (θ x)) (w₀ : Fin M) :
    Measurable (thresholdDecode θ C γ w₀) := by
  classical
  have hm : ∀ k, MeasurableSet {y : Fin n → ℝ | M ≤ k ∨ ∃ h : k < M, γ < θ (C ⟨k, h⟩) y} := by
    intro k
    by_cases hk : M ≤ k
    · simp [hk]
    · have e : {y : Fin n → ℝ | M ≤ k ∨ ∃ h : k < M, γ < θ (C ⟨k, h⟩) y} =
          {y | γ < θ (C ⟨k, not_le.1 hk⟩) y} := by
        ext y
        simp [hk, not_le.1 hk]
      rw [e]
      exact measurableSet_lt measurable_const (hθ _)
  have hidx : Measurable (thresholdIndex θ C γ) :=
    measurable_find (p := fun y k => M ≤ k ∨ ∃ h : k < M, γ < θ (C ⟨k, h⟩) y)
      (fun _ => ⟨M, Or.inl le_rfl⟩) hm
  set g : ℕ → Fin M := fun k => if h : k < M then ⟨k, h⟩ else w₀
  have e : thresholdDecode θ C γ w₀ = g ∘ thresholdIndex θ C γ := rfl
  rw [e]
  exact (Measurable.of_discrete (f := g)).comp hidx

/-- If threshold decoding errs, either the sent codeword is below the threshold or another
codeword is above it. -/
lemma thresholdDecode_ne {w₀ w : Fin M} {y : Fin n → ℝ} (h : thresholdDecode θ C γ w₀ y ≠ w) :
    θ (C w) y ≤ γ ∨ ∃ w' ≠ w, γ < θ (C w') y := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨hw, hothers⟩ := hc
  have hex : ∃ k, M ≤ k ∨ ∃ h : k < M, γ < θ (C ⟨k, h⟩) y := ⟨M, Or.inl le_rfl⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex (Or.inr ⟨w.2, hw⟩)
  have hlt : Nat.find hex < M := lt_of_le_of_lt hle w.2
  have hspec := Nat.find_spec hex
  rcases hspec with hM | ⟨hk, hk'⟩
  · omega
  · have hidx : thresholdIndex θ C γ y = Nat.find hex := rfl
    have hdec : thresholdDecode θ C γ w₀ y = ⟨Nat.find hex, hk⟩ := by
      simp only [thresholdDecode, hidx, hk, ↓reduceDIte]
    rw [hdec] at h
    exact absurd (hothers _ h) (not_le.2 hk')

end Decoder

/-! ### The code of a codebook -/

section RandomCode

variable {M n : ℕ} (N S : ℝ≥0) (P γ : ℝ) (w₀ : Fin M)

/-- The code built from a codebook `C`: codewords violating the power constraint `P` are replaced
by `0`, and the decoder is threshold decoding with the information density. -/
def thresholdCode (C : Fin M → Fin n → ℝ) : GaussianCode M n where
  enc w := if ∑ i, C w i ^ 2 ≤ n * P then C w else 0
  dec := thresholdDecode (infoDensity N S) C γ w₀
  measurable_dec := measurable_thresholdDecode _ C γ (measurable_infoDensity_right N S) w₀

lemma thresholdCode_satisfiesPower (hP : 0 ≤ P) (C : Fin M → Fin n → ℝ) :
    (thresholdCode N S P γ w₀ C).SatisfiesPower P := by
  intro w
  simp only [thresholdCode]
  split_ifs with h
  · exact h
  · simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sum_const_zero]
    positivity

/-- The error event for the message `w` is contained in the union of three events: the codeword
violates the power constraint, it falls below the threshold, or another codeword passes it. -/
lemma thresholdCode_err_le (C : Fin M → Fin n → ℝ) (w : Fin M) :
    noiseLaw N n {z | (thresholdCode N S P γ w₀ C).dec
        ((thresholdCode N S P γ w₀ C).enc w + z) ≠ w} ≤
      (if n * P < ∑ i, C w i ^ 2 then 1 else 0) +
        noiseLaw N n {z | infoDensity N S (C w) (C w + z) ≤ γ} +
        ∑ w' ∈ univ.erase w, noiseLaw N n {z | γ < infoDensity N S (C w') (C w + z)} := by
  by_cases hv : n * P < ∑ i, C w i ^ 2
  · simp only [hv, ↓reduceIte, add_assoc]
    exact le_trans MeasureTheory.prob_le_one le_self_add
  · simp only [hv, ↓reduceIte, zero_add]
    have henc : (thresholdCode N S P γ w₀ C).enc w = C w := by
      simp [thresholdCode, not_lt.1 hv]
    rw [henc]
    calc noiseLaw N n {z | (thresholdCode N S P γ w₀ C).dec (C w + z) ≠ w}
        ≤ noiseLaw N n ({z | infoDensity N S (C w) (C w + z) ≤ γ} ∪
            ⋃ w' ∈ univ.erase w, {z | γ < infoDensity N S (C w') (C w + z)}) := by
          refine measure_mono fun z hz => ?_
          rcases thresholdDecode_ne (infoDensity N S) C γ hz with h | ⟨w', hw', h⟩
          · exact Or.inl h
          · exact Or.inr (Set.mem_biUnion (mem_erase.2 ⟨hw', mem_univ _⟩) h)
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))

end RandomCode

/-! ### The laws of the codewords and the output -/

/-- The law of a random codebook with `M` codewords of length `n` and i.i.d. `N(0, P)` letters. -/
abbrev codebookLaw (P : ℝ≥0) (M n : ℕ) : Measure (Fin M → Fin n → ℝ) :=
  Measure.pi fun _ => noiseLaw P n

/-- Two distinct coordinates of an i.i.d. family are independent. -/
lemma measurePreserving_eval_pair {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x : ι → α => (x i, x j)) (Measure.pi fun _ => μ) (μ.prod μ) := by
  have hind := iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => id) fun _ => aemeasurable_id
  have h2 := hind.indepFun hij
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 h2, (measurePreserving_eval _ i).map_eq,
    (measurePreserving_eval _ j).map_eq]

/-- The sum of independent `N(0, P)ⁿ` and `N(0, N)ⁿ` vectors is `N(0, P + N)ⁿ`. -/
lemma map_add_noiseLaw (P N : ℝ≥0) (n : ℕ) :
    ((noiseLaw P n).prod (noiseLaw N n)).map (fun p => p.1 + p.2) = noiseLaw (P + N) n := by
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => gaussianReal 0 P)
    (fun _ => gaussianReal 0 N)
  rw [noiseLaw, noiseLaw, ← he.map_eq, Measure.map_map (by fun_prop) he.measurable]
  have e : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2) ∘
      MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) = fun q k => (q k).1 + (q k).2 := by
    funext q
    rfl
  rw [e, show (fun (q : Fin n → ℝ × ℝ) k => (q k).1 + (q k).2) =
    fun q k => (fun p : ℝ × ℝ => p.1 + p.2) (q k) from rfl,
    Measure.pi_map_pi (f := fun _ (p : ℝ × ℝ) => p.1 + p.2)
      fun k => (measurable_fst.add measurable_snd).aemeasurable]
  congr 1
  funext k
  have h := gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := P) (v₂ := N)
  rw [add_zero] at h
  exact h

section Laws

variable (P N : ℝ≥0) {M n : ℕ}

/-- The sent codeword and the noise: `(Xⁿ(w), Zⁿ) ∼ N(0, P)ⁿ × N(0, N)ⁿ`. -/
lemma map_codebook_eval (w : Fin M) :
    ((codebookLaw P M n).prod (noiseLaw N n)).map (fun p => (p.1 w, p.2)) =
      (noiseLaw P n).prod (noiseLaw N n) :=
  ((measurePreserving_eval (fun _ : Fin M => noiseLaw P n) w).prod
    (MeasurePreserving.id (noiseLaw N n))).map_eq

/-- Another codeword and the output: `(Xⁿ(w'), Xⁿ(w) + Zⁿ) ∼ N(0, P)ⁿ × N(0, P + N)ⁿ`. -/
lemma map_codebook_other {w w' : Fin M} (hww : w' ≠ w) :
    ((codebookLaw P M n).prod (noiseLaw N n)).map (fun p => (p.1 w', p.1 w + p.2)) =
      (noiseLaw P n).prod (noiseLaw (P + N) n) := by
  have h1 := (measurePreserving_eval_pair (noiseLaw P n) hww).prod
    (MeasurePreserving.id (noiseLaw N n))
  have h2 : MeasurePreserving MeasurableEquiv.prodAssoc
      (((noiseLaw P n).prod (noiseLaw P n)).prod (noiseLaw N n))
      ((noiseLaw P n).prod ((noiseLaw P n).prod (noiseLaw N n))) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have h3 : (noiseLaw P n).prod (noiseLaw (P + N) n) =
      ((noiseLaw P n).prod ((noiseLaw P n).prod (noiseLaw N n))).map
        (Prod.map id fun q => q.1 + q.2) := by
    rw [← map_add_noiseLaw, ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
      Measure.map_id]
  rw [h3, ← h2.map_eq, ← h1.map_eq,
    Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (by fun_prop) h1.measurable]
  rfl

variable {P N}

/-- **The probability that an independent codeword passes the threshold.** If `xⁿ` is fixed and
`Yⁿ ∼ N(0, S)ⁿ`, then `Pr{i(xⁿ; Yⁿ) > γ} ≤ e^{-γ}`: on this event the density of `N(0, S)ⁿ` is at
most `e^{-γ}` times the density of `N(xⁿ, N)ⁿ`. -/
lemma noiseLaw_infoDensity_gt_le {S : ℝ≥0} (hN : N ≠ 0) (hS : S ≠ 0) (x : Fin n → ℝ) (γ : ℝ) :
    noiseLaw S n {y | γ < infoDensity N S x y} ≤ ENNReal.ofReal (exp (-γ)) := by
  have hE : MeasurableSet {y : Fin n → ℝ | γ < infoDensity N S x y} :=
    measurableSet_lt (f := fun _ => γ) (g := infoDensity N S x) measurable_const
      (measurable_infoDensity_right N S x)
  have hp := shiftedNoisePDF_isPDF hN x
  rw [noiseLaw_eq_pdfMeasure hS, pdfMeasure, withDensity_apply _ hE]
  have hbound : ∀ y ∈ {y : Fin n → ℝ | γ < infoDensity N S x y},
      ENNReal.ofReal (prodPDF (gaussianPDFReal 0 S) n y) ≤
        ENNReal.ofReal (exp (-γ)) * ENNReal.ofReal (shiftedNoisePDF N x y) := by
    intro y hy
    rw [← ENNReal.ofReal_mul (exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hpos1 : 0 < prodPDF (gaussianPDFReal 0 S) n y :=
      prod_pos fun i _ => gaussianPDFReal_pos _ _ _ hS
    have hpos2 : 0 < shiftedNoisePDF N x y := shiftedNoisePDF_pos hN x y
    have hlog : infoDensity N S x y =
        log (shiftedNoisePDF N x y / prodPDF (gaussianPDFReal 0 S) n y) := by
      rw [infoDensity, shiftedNoisePDF, prodPDF, ← prod_div_distrib,
        log_prod fun i _ => (div_pos (gaussianPDFReal_pos _ _ _ hN)
          (gaussianPDFReal_pos _ _ _ hS)).ne']
    have h : γ < infoDensity N S x y := hy
    rw [hlog, lt_log_iff_exp_lt (div_pos hpos2 hpos1), lt_div_iff₀ hpos1] at h
    calc prodPDF (gaussianPDFReal 0 S) n y
        = exp (-γ) * (exp γ * prodPDF (gaussianPDFReal 0 S) n y) := by
          rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
      _ ≤ exp (-γ) * shiftedNoisePDF N x y := by gcongr
  calc ∫⁻ y in {y | γ < infoDensity N S x y}, ENNReal.ofReal (prodPDF (gaussianPDFReal 0 S) n y)
      ≤ ∫⁻ y in {y | γ < infoDensity N S x y},
          ENNReal.ofReal (exp (-γ)) * ENNReal.ofReal (shiftedNoisePDF N x y) :=
        setLIntegral_mono (measurable_const.mul hp.measurable.ennreal_ofReal) hbound
    _ ≤ ∫⁻ y, ENNReal.ofReal (exp (-γ)) * ENNReal.ofReal (shiftedNoisePDF N x y) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (exp (-γ)) * ∫⁻ y, ENNReal.ofReal (shiftedNoisePDF N x y) :=
        lintegral_const_mul _ hp.measurable.ennreal_ofReal
    _ = ENNReal.ofReal (exp (-γ)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hp.integrable
          (Eventually.of_forall hp.nonneg), hp.integral_eq_one, ENNReal.ofReal_one, mul_one]

/-- An independent codeword passes the threshold with probability at most `e^{-γ}`. -/
lemma prob_infoDensity_other_gt_le (hN : N ≠ 0) {w w' : Fin M} (hww : w' ≠ w) (γ : ℝ) :
    ((codebookLaw P M n).prod (noiseLaw N n))
        {p | γ < infoDensity N (P + N) (p.1 w') (p.1 w + p.2)} ≤ ENNReal.ofReal (exp (-γ)) := by
  have hS : P + N ≠ 0 := by
    have : 0 < P + N := add_pos_of_nonneg_of_pos zero_le (pos_iff_ne_zero.2 hN)
    exact this.ne'
  have hE : MeasurableSet {q : (Fin n → ℝ) × (Fin n → ℝ) | γ < infoDensity N (P + N) q.1 q.2} :=
    measurableSet_lt (f := fun _ => γ) (g := fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      infoDensity N (P + N) q.1 q.2) measurable_const (measurable_infoDensity N (P + N) n)
  have hΦ : Measurable fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) => (p.1 w', p.1 w + p.2) := by
    fun_prop
  have e : {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) |
      γ < infoDensity N (P + N) (p.1 w') (p.1 w + p.2)} =
      (fun p => (p.1 w', p.1 w + p.2)) ⁻¹' {q | γ < infoDensity N (P + N) q.1 q.2} := rfl
  rw [e, ← Measure.map_apply hΦ hE, map_codebook_other P N hww, Measure.prod_apply hE]
  calc ∫⁻ x, noiseLaw (P + N) n (Prod.mk x ⁻¹'
        {q : (Fin n → ℝ) × (Fin n → ℝ) | γ < infoDensity N (P + N) q.1 q.2}) ∂noiseLaw P n
      ≤ ∫⁻ _x, ENNReal.ofReal (exp (-γ)) ∂noiseLaw P n :=
        lintegral_mono fun x => noiseLaw_infoDensity_gt_le hN hS x γ
    _ = ENNReal.ofReal (exp (-γ)) := by rw [lintegral_const, measure_univ, mul_one]

end Laws

/-! ### The law of large numbers -/

/-- The first two moments of `N(0, v)`. -/
lemma gaussianReal_moments (v : ℝ≥0) :
    Integrable (fun x : ℝ => x) (gaussianReal 0 v) ∧ ∫ x, x ∂gaussianReal 0 v = 0 ∧
      Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) ∧ ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by norm_num)).integrable le_rfl
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)).integrable_sq
  refine ⟨h1, integral_id_gaussianReal, h2, ?_⟩
  have h := variance_eq_integral (μ := gaussianReal 0 v) (X := fun x => x)
    measurable_id.aemeasurable
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simpa using h.symm

/-- The information density of one letter, as a function of the input `a` and the noise `b`:
`log (φ_N((a + b) - a)/φ_S(a + b))`. -/
def letterInfo (N S : ℝ≥0) (q : ℝ × ℝ) : ℝ :=
  log (gaussianPDFReal 0 N (q.1 + q.2 - q.1) / gaussianPDFReal 0 S (q.1 + q.2))

lemma measurable_letterInfo (N S : ℝ≥0) : Measurable (letterInfo N S) := by
  unfold letterInfo
  exact measurable_log.comp (((measurable_gaussianPDFReal 0 N).comp
    ((measurable_fst.add measurable_snd).sub measurable_fst)).div
    ((measurable_gaussianPDFReal 0 S).comp (measurable_fst.add measurable_snd)))

/-- For `X ∼ N(0, P)` and `Z ∼ N(0, N)` independent, the information density of one letter has
mean `I(X; X + Z) = ½ log (1 + P/N)`. -/
lemma letterInfo_moments {N : ℝ≥0} (hN : N ≠ 0) (P : ℝ≥0) :
    Integrable (letterInfo N (P + N)) ((gaussianReal 0 P).prod (gaussianReal 0 N)) ∧
      ∫ q, letterInfo N (P + N) q ∂((gaussianReal 0 P).prod (gaussianReal 0 N)) =
        1 / 2 * log (1 + P / N) := by
  have hN' : (0 : ℝ) < N := by positivity
  have hS' : ((P + N : ℝ≥0) : ℝ) = P + N := NNReal.coe_add _ _
  have hSpos : (0 : ℝ) < ((P + N : ℝ≥0) : ℝ) := by rw [hS']; positivity
  have hS : P + N ≠ 0 := fun h => by rw [h, NNReal.coe_zero] at hSpos; exact lt_irrefl 0 hSpos
  obtain ⟨a1, ea1, a2, ea2⟩ := gaussianReal_moments P
  obtain ⟨b1, eb1, b2, eb2⟩ := gaussianReal_moments N
  set ρ := (gaussianReal 0 P).prod (gaussianReal 0 N)
  set c := log (((P + N : ℝ≥0) : ℝ) / N) / 2
  set α := -(2 * (N : ℝ))⁻¹ + (2 * ((P + N : ℝ≥0) : ℝ))⁻¹
  set β := (2 * ((P + N : ℝ≥0) : ℝ))⁻¹
  have iB : Integrable (fun q : ℝ × ℝ => q.2 ^ 2) ρ :=
    ((integrable_const (1 : ℝ)).mul_prod b2).congr (Eventually.of_forall fun q => by simp)
  have iA : Integrable (fun q : ℝ × ℝ => q.1 ^ 2) ρ :=
    (a2.mul_prod (integrable_const (1 : ℝ))).congr (Eventually.of_forall fun q => by simp)
  have iAB : Integrable (fun q : ℝ × ℝ => q.1 * q.2) ρ := a1.mul_prod b1
  have eB : ∫ q, q.2 ^ 2 ∂ρ = N := by
    have h := integral_prod_mul (μ := gaussianReal 0 P) (ν := gaussianReal 0 N)
      (fun _ : ℝ => (1 : ℝ)) (fun b => b ^ 2)
    simp only [one_mul, integral_const, probReal_univ, one_smul] at h
    rw [h, eb2]
  have eA : ∫ q, q.1 ^ 2 ∂ρ = P := by
    have h := integral_prod_mul (μ := gaussianReal 0 P) (ν := gaussianReal 0 N)
      (fun a => a ^ 2) (fun _ : ℝ => (1 : ℝ))
    simp only [mul_one, integral_const, probReal_univ, one_smul] at h
    rw [h, ea2]
  have eAB : ∫ q, q.1 * q.2 ∂ρ = 0 := by
    rw [integral_prod_mul (fun a => a) (fun b => b), ea1, zero_mul]
  have e : letterInfo N (P + N) = fun q => c + α * q.2 ^ 2 + β * q.1 ^ 2 +
      2 * β * (q.1 * q.2) := by
    funext q
    rw [letterInfo, log_gaussianPDFReal_sub_div hN hS, add_sub_cancel_left]
    simp only [c, α, β]
    ring
  have i1 : Integrable (fun q : ℝ × ℝ => c + α * q.2 ^ 2) ρ :=
    (integrable_const c).add (iB.const_mul α)
  have i2 : Integrable (fun q : ℝ × ℝ => c + α * q.2 ^ 2 + β * q.1 ^ 2) ρ :=
    i1.add (iA.const_mul β)
  have i3 : Integrable (fun q : ℝ × ℝ => 2 * β * (q.1 * q.2)) ρ := iAB.const_mul _
  rw [e]
  refine ⟨i2.add i3, ?_⟩
  rw [integral_add i2 i3, integral_add i1 (iA.const_mul β), integral_add (integrable_const c)
    (iB.const_mul α), integral_const_mul, integral_const_mul, integral_const_mul, eA, eB, eAB,
    integral_const]
  simp only [probReal_univ, one_smul, mul_zero, add_zero]
  have hc : c = 1 / 2 * log (1 + P / N) := by
    simp only [c]
    rw [hS', add_div, div_self hN'.ne', add_comm]
    ring
  rw [hc]
  simp only [α, β, hS']
  field_simp
  ring

/-- **The sent codeword passes the threshold.** With `Xⁿ ∼ N(0, P)ⁿ` and `Zⁿ ∼ N(0, N)ⁿ`,
`Pr{i(Xⁿ; Xⁿ + Zⁿ) ≤ n(C - δ)} → 0`, where `C = ½ log (1 + P/N)`. -/
lemma tendsto_prob_infoDensity_sent_le {N : ℝ≥0} (hN : N ≠ 0) (P : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ((noiseLaw P n).prod (noiseLaw N n))
      {q | infoDensity N (P + N) q.1 (q.1 + q.2) ≤ n * (1 / 2 * log (1 + P / N) - δ)})
      atTop (𝓝 0) := by
  obtain ⟨hint, hmean⟩ := letterInfo_moments hN P
  have hlln := tendsto_pi_measure_abs_mean_sub_ge ((gaussianReal 0 P).prod (gaussianReal 0 N))
    (measurable_letterInfo N (P + N)) hint hδ
  rw [hmean] at hlln
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlln
    (Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => gaussianReal 0 P)
    (fun _ => gaussianReal 0 N)
  have hE : MeasurableSet {q : (Fin n → ℝ) × (Fin n → ℝ) |
      infoDensity N (P + N) q.1 (q.1 + q.2) ≤ n * (1 / 2 * log (1 + P / N) - δ)} :=
    measurableSet_le (measurable_infoDensity_sent N (P + N) n) measurable_const
  rw [← he.measure_preimage hE.nullMeasurableSet]
  refine measure_mono fun q hq => ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hkey : infoDensity N (P + N) (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) q).1
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) q).1 +
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) q).2) =
      ∑ i, letterInfo N (P + N) (q i) := by
    unfold infoDensity letterInfo
    rfl
  have hsum : ∑ i, letterInfo N (P + N) (q i) ≤ n * (1 / 2 * log (1 + P / N) - δ) := by
    rw [← hkey]
    exact hq
  have hmean' : (n : ℝ)⁻¹ * ∑ i, letterInfo N (P + N) (q i) ≤ 1 / 2 * log (1 + P / N) - δ := by
    rw [inv_mul_le_iff₀ hn']
    exact hsum
  change δ ≤ |(n : ℝ)⁻¹ * ∑ i, letterInfo N (P + N) (q i) - 1 / 2 * log (1 + P / N)|
  rw [abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

/-! ### The random coding bound -/

/-- **The random coding bound.** For codewords drawn i.i.d. from `N(0, P')`, threshold decoding
with threshold `γ` and the information density relative to `N(0, P' + N)`, and codewords
violating the power constraint `P` replaced by `0`, some code with `M` codewords has
`Pₑ^(n) ≤ Pr{∑ᵢ Xᵢ² > nP} + Pr{i(Xⁿ; Xⁿ + Zⁿ) ≤ γ} + (M - 1) e^{-γ}`. -/
theorem exists_gaussianCode_avgErrProb_le {P : ℝ} (hP : 0 ≤ P) (P' : ℝ≥0) {N : ℝ≥0}
    (hN : N ≠ 0) {M n : ℕ} (hM : 0 < M) (γ : ℝ) :
    ∃ c : GaussianCode M n, c.SatisfiesPower P ∧ c.avgErrProb N ≤
      (noiseLaw P' n {x | n * P < ∑ i, x i ^ 2}).toReal +
        (((noiseLaw P' n).prod (noiseLaw N n))
          {q | infoDensity N (P' + N) q.1 (q.1 + q.2) ≤ γ}).toReal + (M - 1) * exp (-γ) := by
  classical
  set S := P' + N
  set w₀ : Fin M := ⟨0, hM⟩
  set ρ := codebookLaw P' M n
  set ν := noiseLaw N n
  set Vset : Set (Fin n → ℝ) := {x | n * P < ∑ i, x i ^ 2}
  set Aset : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | infoDensity N S q.1 (q.1 + q.2) ≤ γ}
  set Bset : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | γ < infoDensity N S q.1 q.2}
  have hVset : MeasurableSet Vset := measurableSet_lt measurable_const
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)
  have hAset : MeasurableSet Aset :=
    measurableSet_le (measurable_infoDensity_sent N S n) measurable_const
  have hBset : MeasurableSet Bset := measurableSet_lt (f := fun _ => γ)
    (g := fun q : (Fin n → ℝ) × (Fin n → ℝ) => infoDensity N S q.1 q.2) measurable_const
    (measurable_infoDensity N S n)
  set V : Fin M → Set (Fin M → Fin n → ℝ) := fun w => (fun C => C w) ⁻¹' Vset
  set A : Fin M → Set ((Fin M → Fin n → ℝ) × (Fin n → ℝ)) :=
    fun w => (fun p => (p.1 w, p.2)) ⁻¹' Aset
  set B : Fin M → Fin M → Set ((Fin M → Fin n → ℝ) × (Fin n → ℝ)) :=
    fun w w' => (fun p => (p.1 w', p.1 w + p.2)) ⁻¹' Bset
  have hV : ∀ w, MeasurableSet (V w) := fun w => (measurable_pi_apply w) hVset
  have hA : ∀ w, MeasurableSet (A w) := fun w =>
    ((measurable_pi_apply w).comp measurable_fst |>.prodMk measurable_snd) hAset
  have hB : ∀ w w', MeasurableSet (B w w') := fun w w' =>
    (((measurable_pi_apply w').comp measurable_fst).prodMk
      (((measurable_pi_apply w).comp measurable_fst).add measurable_snd)) hBset
  -- The bound `T_w(C)` on the error of the message `w` for the codebook `C`.
  set T : Fin M → (Fin M → Fin n → ℝ) → ℝ≥0∞ := fun w C =>
    (V w).indicator 1 C + ν (Prod.mk C ⁻¹' A w) + ∑ w' ∈ univ.erase w, ν (Prod.mk C ⁻¹' B w w')
  have hTm : ∀ w, Measurable (T w) := fun w =>
    ((measurable_one.indicator (hV w)).add (measurable_measure_prodMk_left (hA w))).add
      (Finset.measurable_sum _ fun w' _ => measurable_measure_prodMk_left (hB w w'))
  set e := ENNReal.ofReal (exp (-γ))
  set K := noiseLaw P' n Vset + ((noiseLaw P' n).prod ν) Aset + (M - 1 : ℕ) * e
  -- The expected bound.
  have hTint : ∀ w, ∫⁻ C, T w C ∂ρ ≤ K := by
    intro w
    have h1 : ∫⁻ C, (V w).indicator 1 C ∂ρ = noiseLaw P' n Vset := by
      rw [lintegral_indicator_one (hV w)]
      exact (measurePreserving_eval (fun _ : Fin M => noiseLaw P' n) w).measure_preimage
        hVset.nullMeasurableSet
    have h2 : ∫⁻ C, ν (Prod.mk C ⁻¹' A w) ∂ρ = ((noiseLaw P' n).prod ν) Aset := by
      rw [← Measure.prod_apply (hA w), ← map_codebook_eval P' N w,
        Measure.map_apply (by fun_prop) hAset]
    have h3 : ∀ w' ∈ univ.erase w, ∫⁻ C, ν (Prod.mk C ⁻¹' B w w') ∂ρ ≤ e := by
      intro w' hw'
      rw [← Measure.prod_apply (hB w w')]
      exact prob_infoDensity_other_gt_le hN (ne_of_mem_erase hw') γ
    have m1 : Measurable fun C => (V w).indicator (1 : (Fin M → Fin n → ℝ) → ℝ≥0∞) C :=
      measurable_one.indicator (hV w)
    have m2 : Measurable fun C => (V w).indicator (1 : (Fin M → Fin n → ℝ) → ℝ≥0∞) C +
        ν (Prod.mk C ⁻¹' A w) :=
      m1.add (measurable_measure_prodMk_left (hA w))
    change ∫⁻ C, (V w).indicator 1 C + ν (Prod.mk C ⁻¹' A w) +
      ∑ w' ∈ univ.erase w, ν (Prod.mk C ⁻¹' B w w') ∂ρ ≤ K
    rw [lintegral_add_left m2, lintegral_add_left m1, h1, h2,
      lintegral_finsetSum _ fun w' _ => measurable_measure_prodMk_left (hB w w')]
    change _ ≤ noiseLaw P' n Vset + ((noiseLaw P' n).prod ν) Aset + (M - 1 : ℕ) * e
    refine add_le_add le_rfl ?_
    calc ∑ w' ∈ univ.erase w, ∫⁻ C, ν (Prod.mk C ⁻¹' B w w') ∂ρ ≤ ∑ _w' ∈ univ.erase w, e :=
          sum_le_sum h3
      _ = (M - 1 : ℕ) * e := by
          rw [sum_const, card_erase_of_mem (mem_univ w), card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hU : ∫⁻ C, ∑ w, T w C ∂ρ ≤ M * K := by
    rw [lintegral_finsetSum _ fun w _ => hTm w]
    calc ∑ w, ∫⁻ C, T w C ∂ρ ≤ ∑ _w : Fin M, K := sum_le_sum fun w _ => hTint w
      _ = M * K := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨C, hC⟩ := exists_le_lintegral (μ := ρ)
    (Finset.measurable_sum _ fun w _ => hTm w).aemeasurable
  -- The code of the codebook `C`.
  set c := thresholdCode N S P γ w₀ C
  have hTfin : ∀ w, T w C ≠ ∞ := by
    intro w
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, measure_ne_top _ _⟩,
      ENNReal.sum_ne_top.2 fun w' _ => measure_ne_top _ _⟩
    by_cases h : C ∈ V w <;> simp [Set.indicator, h]
  have hKfin : K ≠ ∞ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      measure_ne_top _ _⟩, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top⟩
  have herr : ∀ w, c.condErrProb N w ≤ (T w C).toReal := by
    intro w
    refine ENNReal.toReal_mono (hTfin w) ((thresholdCode_err_le N S P γ w₀ C w).trans ?_)
    have hind : (if n * P < ∑ i, C w i ^ 2 then (1 : ℝ≥0∞) else 0) = (V w).indicator 1 C := by
      by_cases h : n * P < ∑ i, C w i ^ 2
      · simp only [h, ↓reduceIte, Set.indicator_of_mem (show C ∈ V w from h), Pi.one_apply]
      · simp only [h, ↓reduceIte, Set.indicator_of_notMem (show C ∉ V w from h)]
    rw [hind]
    exact le_rfl
  refine ⟨c, thresholdCode_satisfiesPower N S P γ w₀ hP C, ?_⟩
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : ∑ w, c.condErrProb N w ≤ M * K.toReal := by
    calc ∑ w, c.condErrProb N w ≤ ∑ w, (T w C).toReal := sum_le_sum fun w _ => herr w
      _ = (∑ w, T w C).toReal := (ENNReal.toReal_sum fun w _ => hTfin w).symm
      _ ≤ ((M : ℝ≥0∞) * K).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hKfin) (hC.trans hU)
      _ = M * K.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hK : K.toReal = (noiseLaw P' n Vset).toReal + (((noiseLaw P' n).prod ν) Aset).toReal +
      (M - 1) * exp (-γ) := by
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal (exp_pos _).le, Nat.cast_sub hM]
    push_cast
    ring
  rw [GaussianCode.avgErrProb, div_le_iff₀ hM', ← hK, mul_comm]
  exact hsum

/-- **The power constraint is rarely violated.** With `Xⁿ ∼ N(0, P')ⁿ` and `P' < P`,
`Pr{∑ᵢ Xᵢ² > nP} → 0`. -/
lemma tendsto_prob_power_gt {P P' : ℝ≥0} (hP : (P' : ℝ) < P) :
    Tendsto (fun n : ℕ => noiseLaw P' n {x | n * (P : ℝ) < ∑ i, x i ^ 2}) atTop (𝓝 0) := by
  obtain ⟨-, -, hint, hmean⟩ := gaussianReal_moments P'
  have hlln := tendsto_pi_measure_abs_mean_sub_ge (gaussianReal 0 P') (V := fun x => x ^ 2)
    (by fun_prop) hint (sub_pos.2 hP)
  rw [hmean] at hlln
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlln
    (Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine measure_mono fun x hx => ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' : (P : ℝ) < (n : ℝ)⁻¹ * ∑ i, x i ^ 2 := by
    rw [lt_inv_mul_iff₀ hn']
    exact hx
  change (P : ℝ) - P' ≤ |(n : ℝ)⁻¹ * ∑ i, x i ^ 2 - P'|
  exact le_trans (by linarith) (le_abs_self _)

/-! ### Theorem 9.1.1 -/

/-- A code with a single message never errs. -/
lemma exists_gaussianCode_maxErrProb_eq_zero {M : ℕ} (hM : M = 1) (n : ℕ) (N : ℝ≥0) {P : ℝ}
    (hP : 0 ≤ P) : ∃ c : GaussianCode M n, c.SatisfiesPower P ∧ c.maxErrProb N = 0 := by
  subst hM
  refine ⟨⟨fun _ _ => 0, fun _ => 0, measurable_const⟩, fun w => ?_, ?_⟩
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
    positivity
  · have h : ∀ w : Fin 1,
        (⟨fun _ _ => 0, fun _ => 0, measurable_const⟩ : GaussianCode 1 n).condErrProb N w = 0 :=
      fun w => by simp [GaussianCode.condErrProb, Subsingleton.elim w 0]
    simp [GaussianCode.maxErrProb, h]

/-- **Theorem 9.1.1 (achievability), Section 9.1.** Every rate `R < C = ½ log (1 + P/N)` is
achievable for the Gaussian channel with power constraint `P` and noise variance `N`. -/
theorem isAchievableGaussianRate_of_lt {P N : ℝ≥0} (hN : N ≠ 0) {R : ℝ}
    (hR : R < 1 / 2 * log (1 + P / N)) : IsAchievableGaussianRate P N R := by
  rcases le_or_gt R 0 with hR0 | hR0
  · -- With `R ≤ 0` there is a single message.
    have h1 : ∀ n : ℕ, ⌈exp (n * R)⌉₊ = 1 := fun n => by
      rw [Nat.ceil_eq_iff one_ne_zero]
      refine ⟨by simp [exp_pos], ?_⟩
      have : (n : ℝ) * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0
      simpa using exp_le_one_iff.2 this
    choose c hc using fun n : ℕ => exists_gaussianCode_maxErrProb_eq_zero (h1 n) n N P.2
    exact ⟨c, fun n => (hc n).1, by simp [fun n => (hc n).2]⟩
  have hN' : (0 : ℝ) < N := by positivity
  -- Choose `P' < P` with `R < ½ log (1 + P'/N)`: the midpoint of `N (e^{2R} - 1)` and `P`.
  have hexp : exp (2 * R) < 1 + P / N := by
    have h := exp_lt_exp.2 (show 2 * R < log (1 + P / N) by linarith)
    rwa [exp_log (by positivity)] at h
  have hexp1 : 1 < exp (2 * R) := one_lt_exp_iff.2 (by linarith)
  have hlow : N * (exp (2 * R) - 1) < P := by
    have h : exp (2 * R) - 1 < P / N := by linarith
    rwa [lt_div_iff₀ hN', mul_comm] at h
  set t : ℝ := (N * (exp (2 * R) - 1) + P) / 2 with ht
  have hlow0 : 0 < N * (exp (2 * R) - 1) := mul_pos hN' (by linarith)
  have ht0 : 0 < t := by rw [ht]; positivity
  set P' : ℝ≥0 := ⟨t, ht0.le⟩
  have hP'P : (P' : ℝ) < P := by change t < P; rw [ht]; linarith
  have hC' : R < 1 / 2 * log (1 + P' / N) := by
    have h1 : exp (2 * R) < 1 + t / N := by
      rw [← sub_lt_iff_lt_add', lt_div_iff₀ hN', mul_comm]
      rw [ht]
      linarith
    have h2 := log_lt_log (exp_pos _) h1
    rw [log_exp] at h2
    change R < 1 / 2 * log (1 + t / N)
    linarith
  set C' := 1 / 2 * log (1 + P' / N)
  set δ := (C' - R) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hγ : C' - δ = R + δ := by rw [hδ_def]; ring
  -- For each `n`, a random code with `2⌈e^{nR}⌉` codewords and its better half.
  set U : ℕ → ℝ := fun n => (noiseLaw P' n {x | n * (P : ℝ) < ∑ i, x i ^ 2}).toReal +
    (((noiseLaw P' n).prod (noiseLaw N n))
      {q | infoDensity N (P' + N) q.1 (q.1 + q.2) ≤ n * (C' - δ)}).toReal +
    (2 * ⌈exp (n * R)⌉₊ - 1) * exp (-(n * (C' - δ)))
  have hcode : ∀ n : ℕ, ∃ c : GaussianCode ⌈exp (n * R)⌉₊ n, c.SatisfiesPower P ∧
      c.maxErrProb N ≤ 2 * U n := by
    intro n
    have hM := one_le_ceil_exp (n * R)
    obtain ⟨c₀, hpow₀, hc₀⟩ := exists_gaussianCode_avgErrProb_le (M := 2 * ⌈exp (n * R)⌉₊)
      P.2 P' hN (by omega) (n * (C' - δ))
    obtain ⟨c, hpow, hc⟩ := GaussianCode.exists_maxErrProb_le_two_mul N (by omega) c₀ hpow₀
    refine ⟨c, hpow, hc.trans ?_⟩
    push_cast at hc₀
    exact mul_le_mul_of_nonneg_left hc₀ (by norm_num)
  choose c hpow hc using hcode
  refine ⟨c, hpow, ?_⟩
  -- `U n → 0`.
  have hv : Tendsto (fun n : ℕ => (noiseLaw P' n {x | n * (P : ℝ) < ∑ i, x i ^ 2}).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_prob_power_gt hP'P)
    rw [ENNReal.toReal_zero] at h
    exact h
  have ha : Tendsto (fun n : ℕ => (((noiseLaw P' n).prod (noiseLaw N n))
      {q | infoDensity N (P' + N) q.1 (q.1 + q.2) ≤ n * (C' - δ)}).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_prob_infoDensity_sent_le hN P' hδ)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hbound : ∀ n : ℕ, (2 * (⌈exp (n * R)⌉₊ : ℝ) - 1) * exp (-(n * (C' - δ))) ≤
      2 * exp (-(n * δ)) + exp (-(n * (R + δ))) := by
    intro n
    have hceil : (⌈exp (n * R)⌉₊ : ℝ) ≤ exp (n * R) + 1 :=
      (Nat.ceil_lt_add_one (exp_pos _).le).le
    have hpos : 0 ≤ exp (-(n * (R + δ))) := (exp_pos _).le
    have hexp' : exp (n * R) * exp (-(n * (R + δ))) = exp (-(n * δ)) := by
      rw [← exp_add]; ring_nf
    rw [hγ]
    calc (2 * (⌈exp (n * R)⌉₊ : ℝ) - 1) * exp (-(n * (R + δ)))
        ≤ (2 * (exp (n * R) + 1) - 1) * exp (-(n * (R + δ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
      _ = _ := by rw [← hexp']; ring
  have hlim : Tendsto (fun n : ℕ => 2 * ((noiseLaw P' n {x | n * (P : ℝ) < ∑ i, x i ^ 2}).toReal +
      (((noiseLaw P' n).prod (noiseLaw N n))
        {q | infoDensity N (P' + N) q.1 (q.1 + q.2) ≤ n * (C' - δ)}).toReal +
      (2 * exp (-(n * δ)) + exp (-(n * (R + δ)))))) atTop (𝓝 0) := by
    have h2 := ((tendsto_exp_neg_mul_nat hδ).const_mul 2).add
      (tendsto_exp_neg_mul_nat (by linarith : 0 < R + δ))
    simpa using ((hv.add ha).add h2).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (c n).maxErrProb_nonneg N) fun n => (hc n).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  simp only [U]
  linarith [hbound n]

/-- **Theorem 9.1.1.** The capacity of the Gaussian channel with power constraint `P` and noise
variance `N`, the supremum of the achievable rates, is `C = ½ log (1 + P/N)` nats per
transmission. -/
theorem gaussianOpCapacity_eq (P : ℝ≥0) {N : ℝ≥0} (hN : N ≠ 0) :
    gaussianOpCapacity P N = 1 / 2 * log (1 + P / N) := by
  have hN' : (0 : ℝ) < N := by positivity
  have hC : 0 ≤ 1 / 2 * log (1 + P / N) :=
    mul_nonneg (by norm_num) (log_nonneg (by linarith [show (0 : ℝ) ≤ P / N by positivity]))
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨-1, isAchievableGaussianRate_of_lt hN (by linarith)⟩ (fun R hR => hR.le hN) fun w hw => ?_
  exact ⟨(w + 1 / 2 * log (1 + P / N)) / 2, isAchievableGaussianRate_of_lt hN (by linarith),
    by linarith⟩

/-- **Theorem 9.1.1.** The capacity of the Gaussian channel equals its information capacity
`max_{E X² ≤ P} I(X; Y)`. -/
theorem gaussianOpCapacity_eq_gaussianInfoCapacity (P : ℝ≥0) {N : ℝ≥0} (hN : N ≠ 0) :
    gaussianOpCapacity P N = gaussianInfoCapacity P N := by
  rw [gaussianOpCapacity_eq P hN, gaussianInfoCapacity_eq P hN]

end InfoTheory
