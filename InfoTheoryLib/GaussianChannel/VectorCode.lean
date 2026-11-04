/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.AWGN
public import InfoTheoryLib.GaussianChannel.Parallel
public import InfoTheoryLib.GaussianChannel.Vector
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The Gaussian vector channel: the coding theorem

This file proves Theorem 1 of Lecture 10 of El Gamal and Kim's notes for the channel
`Y(i) = G X(i) + Z(i)` with `Z(i) ∼ N(0, I)`: the capacity is
`C = max_{K ≽ 0, tr K ≤ P} ½ log |G K Gᵀ + I|`.

For the converse, let `K̄` be the average covariance of the codewords and rotate the outputs by the
eigenvectors of `G K̄ Gᵀ + I`. This gives parallel Gaussian channels whose average powers are the
eigenvalues of `G K̄ Gᵀ`, and the comparison of the output with independent normal coordinates
bounds
the mutual information by `n · ½ log |G K̄ Gᵀ + I|`.

For achievability, write `G = U D Ψᵀ`. A code for the AWGN channel for each `γₖ ≠ 0`, with the power
`pₖ` that it is allotted by Hadamard's inequality, gives the code with the transmitted vectors
`X = Ψ X̃`. The decoder rotates by `Uᵀ` and decodes each coordinate separately.

## Main definitions

* `stdNoise ι`: the law `N(0, 1)^ι`.
* `GVCode M n r t`: codes, with the noise indexed by the pairs `(i, k)`.
* `GVCode.SatisfiesPower`, `GVCode.condErrProb`, `GVCode.avgErrProb`.
* `IsAchievableGV G P R`, `opCapacityGV G P`: achievable rates in bits and the capacity.

## Main statements

* `map_stdNoise_of_orthogonal`: an orthogonal matrix preserves the noise.
* `GaussianCode.one_sub_avgErrProb_mul_log_le_sum`: the bound for parallel channels.
* `IsAchievableGV.le`: the converse.
* `isAchievableGV_of_lt`: achievability.
* `opCapacityGV_eq`: **Theorem 1 of Lecture 10**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 10
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The noise -/

section Noise

variable {ι : Type*} [Fintype ι]

/-- The law `N(0, 1)^ι` of independent standard normal coordinates. -/
abbrev stdNoise (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 (1 : ℝ≥0)

/-- An orthogonal matrix preserves the law `N(0, 1)^ι`. -/
theorem map_stdNoise_of_orthogonal [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) :
    (stdNoise ι).map (fun z => Q *ᵥ z) = stdNoise ι := by
  set E := EuclideanSpace ℝ ι
  -- The columns of `Q` are an orthonormal basis.
  set v : ι → E := fun i => WithLp.toLp 2 fun k => Q k i
  have hv : Orthonormal ℝ (Set.univ.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, -⟩ ⟨j, -⟩
    have h := congrArg (fun A : Matrix ι ι ℝ => A i j) hQ
    simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply] at h
    change inner ℝ (v i) (v j) = _
    rw [PiLp.inner_apply]
    simp only [Subtype.mk.injEq, v, RCLike.inner_apply, conj_trivial]
    rw [← h]
    exact sum_congr rfl fun k _ => mul_comm _ _
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp [E])
  have hb' : ∀ i, b i = v i := fun i => hb i (Set.mem_univ i)
  have h1 := stdGaussian_eq_map_pi_orthonormalBasis b
  have h2 : (stdNoise ι).map (WithLp.toLp 2) = stdGaussian E := map_pi_eq_stdGaussian
  have hfun : (fun x : ι → ℝ => ∑ i, x i • b i) = (WithLp.toLp 2) ∘ fun z => Q *ᵥ z := by
    funext x
    ext k
    simp only [hb', v, Function.comp_apply, mulVec, dotProduct]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    exact sum_congr rfl fun i _ => mul_comm _ _
  have hmeas : Measurable fun z : ι → ℝ => Q *ᵥ z :=
    (Matrix.mulVecLin Q).continuous_of_finiteDimensional.measurable
  have htoLp : Measurable (WithLp.toLp 2 : (ι → ℝ) → E) :=
    (PiLp.continuous_toLp 2 fun _ : ι => ℝ).measurable
  have hofLp : Measurable (WithLp.ofLp : E → ι → ℝ) :=
    (PiLp.continuous_ofLp 2 fun _ : ι => ℝ).measurable
  have h3 : ((stdNoise ι).map fun z => Q *ᵥ z).map (WithLp.toLp 2) =
      (stdNoise ι).map (WithLp.toLp 2) := by
    rw [Measure.map_map htoLp hmeas, ← hfun, ← h1, h2]
  have h4 := congrArg (Measure.map WithLp.ofLp) h3
  rw [Measure.map_map hofLp htoLp, Measure.map_map hofLp htoLp] at h4
  have hid : (WithLp.ofLp ∘ WithLp.toLp 2 : (ι → ℝ) → ι → ℝ) = id := rfl
  rwa [hid, Measure.map_id, Measure.map_id] at h4

/-- Reindexing preserves the law `N(0, 1)^ι`. -/
theorem map_stdNoise_reindex {ι' : Type*} [Fintype ι'] (e : ι ≃ ι') :
    (stdNoise ι').map (fun z i => z (e i)) = stdNoise ι := by
  classical
  refine (Measure.pi_eq fun S hS => ?_).symm
  have hm : Measurable fun (z : ι' → ℝ) (i : ι) => z (e i) := by fun_prop
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have hset : (fun (z : ι' → ℝ) (i : ι) => z (e i)) ⁻¹' Set.univ.pi S =
      Set.univ.pi fun j => S (e.symm j) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact ⟨fun h j => by simpa using h (e.symm j), fun h i => by simpa using h (e i)⟩
  rw [hset, Measure.pi_pi]
  exact e.symm.prod_comp fun i => gaussianReal 0 (1 : ℝ≥0) (S i)

/-- The coordinates with a fixed second index are i.i.d. standard normal. -/
theorem map_stdNoise_fiber {n : ℕ} {r : Type*} [Fintype r] (k : r) :
    (stdNoise (Fin n × r)).map (fun z i => z (i, k)) = noiseLaw 1 n := by
  classical
  refine (Measure.pi_eq fun S hS => ?_).symm
  have hm : Measurable fun (z : Fin n × r → ℝ) (i : Fin n) => z (i, k) := by fun_prop
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have hset : (fun (z : Fin n × r → ℝ) (i : Fin n) => z (i, k)) ⁻¹' Set.univ.pi S =
      Set.univ.pi fun p : Fin n × r => if p.2 = k then S p.1 else Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h p
      split_ifs with hp
      · have := h p.1
        have e : (p.1, k) = p := Prod.ext rfl hp.symm
        rwa [e] at this
      · exact Set.mem_univ _
    · intro h i
      simpa using h (i, k)
  rw [hset, Measure.pi_pi, Fintype.prod_prod_type]
  refine prod_congr rfl fun i _ => ?_
  have e : ∀ l : r, gaussianReal 0 (1 : ℝ≥0) (if l = k then S i else Set.univ) =
      if l = k then gaussianReal 0 (1 : ℝ≥0) (S i) else 1 := fun l => by
    split_ifs <;> simp
  simp only [e]
  rw [prod_ite_eq' univ k]
  simp

end Noise

/-! ### Parallel channels with coordinate-dependent powers -/

namespace GaussianCode

variable {M n : ℕ} (c : GaussianCode M n)

/-- The average power `(1/M) ∑_w xⱼ(w)²` of a coordinate. -/
def avgPower (j : Fin n) : ℝ := (M : ℝ)⁻¹ * ∑ w, c.enc w j ^ 2

lemma avgPower_nonneg (j : Fin n) : 0 ≤ c.avgPower j :=
  mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)

/-- The relative entropy between `N(xⁿ, I)` and the independent `N(0, Sⱼ)`:
`∑ⱼ (½ log Sⱼ - ½ + (xⱼ² + 1)/(2Sⱼ))`. -/
private lemma relEntropyPDF_shifted_diag {S : Fin n → ℝ≥0} (hS : ∀ j, S j ≠ 0) (x : Fin n → ℝ) :
    Integrable (fun y => shiftedNoisePDF 1 x y * log (shiftedNoisePDF 1 x y / diagNoisePDF S y)) ∧
      relEntropyPDF volume (shiftedNoisePDF 1 x) (diagNoisePDF S) =
        ∑ j, (log (S j / (1 : ℝ≥0)) / 2 - 1 / 2 + (x j ^ 2 + (1 : ℝ≥0)) / (2 * S j)) := by
  set g : Fin n → ℝ → ℝ := fun j t => gaussianPDFReal 0 1 (t - x j)
  set ℓ : Fin n → ℝ → ℝ := fun j t =>
    log (gaussianPDFReal 0 1 (t - x j) / gaussianPDFReal 0 (S j) t)
  have hlog : ∀ y : Fin n → ℝ,
      log (shiftedNoisePDF 1 x y / diagNoisePDF S y) = ∑ j, ℓ j (y j) := by
    intro y
    simp only [shiftedNoisePDF, diagNoisePDF, ← prod_div_distrib]
    exact log_prod fun j _ => (div_pos (gaussianPDFReal_pos _ _ _ one_ne_zero)
      (gaussianPDFReal_pos _ _ _ (hS j))).ne'
  have hterm : ∀ k, Integrable (fun y : Fin n → ℝ => (∏ j, g j (y j)) * ℓ k (y k)) ∧
      ∫ y : Fin n → ℝ, (∏ j, g j (y j)) * ℓ k (y k) =
        log (S k / (1 : ℝ≥0)) / 2 - 1 / 2 + (x k ^ 2 + (1 : ℝ≥0)) / (2 * S k) := by
    intro k
    obtain ⟨h1, h2⟩ := integral_prod_mul_apply (g := g)
      (fun j => (gaussianPDFReal_sub_moments one_ne_zero (x j)).1)
      (fun j => (gaussianPDFReal_sub_moments one_ne_zero (x j)).2.1) k
      (integral_gaussianPDFReal_sub_mul_log_div one_ne_zero (hS k) (x k)).1
    exact ⟨h1, h2.trans (integral_gaussianPDFReal_sub_mul_log_div one_ne_zero (hS k) (x k)).2⟩
  have e : ∀ y, shiftedNoisePDF 1 x y * log (shiftedNoisePDF 1 x y / diagNoisePDF S y) =
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

/-- For a code over parallel channels with unit noise,
`I(W; Ŵ) ≤ ∑ⱼ ½ log (1 + (1/M) ∑_w xⱼ(w)²)`. -/
theorem mutualInfo_msgLaw_le_sum (hM : 0 < M) :
    I[Prod.fst : Prod.snd ; c.msgLaw 1] ≤ ∑ j, 1 / 2 * log (1 + c.avgPower j) := by
  have hμ := c.msgLaw_isPMF 1 hM
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  set S : Fin n → ℝ≥0 := fun j => ⟨1 + c.avgPower j, by linarith [c.avgPower_nonneg j]⟩
  have hS' : ∀ j, (S j : ℝ) = 1 + c.avgPower j := fun j => rfl
  have hSpos : ∀ j, (0 : ℝ) < S j := fun j => by rw [hS']; linarith [c.avgPower_nonneg j]
  have hS : ∀ j, S j ≠ 0 := fun j h => by
    have := hSpos j
    rw [h, NNReal.coe_zero] at this
    exact lt_irrefl 0 this
  set q : (Fin n → ℝ) → ℝ := diagNoisePDF S
  have hq : IsPDF volume q := diagNoisePDF_isPDF hS
  have hqpos : ∀ y, 0 < q y := diagNoisePDF_pos hS
  set Q : Fin M → ℝ := fun ŵ => ∫ y in c.dec ⁻¹' {ŵ}, q y
  have hQ : IsPMF Q := ⟨fun ŵ => setIntegral_nonneg (c.measurableSet_cell ŵ) fun y _ =>
    hq.nonneg y, by rw [sum_setIntegral_preimage_singleton hq.integrable c.measurableSet_cell,
      hq.integral_eq_one]⟩
  have hT : ∀ w ŵ, c.transProb 1 w ŵ = ∫ y in c.dec ⁻¹' {ŵ}, shiftedNoisePDF 1 (c.enc w) y :=
    fun w ŵ => noiseLaw_real_eq one_ne_zero (c.enc w) (c.measurableSet_cell ŵ)
  have hQμ : ∀ w ŵ, Q ŵ = 0 → c.msgLaw 1 (w, ŵ) = 0 := by
    intro w ŵ h
    have h0 : q =ᵐ[volume.restrict (c.dec ⁻¹' {ŵ})] 0 := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall hq.nonneg) hq.integrable.integrableOn).1 h
    have hall : ∀ᵐ y ∂volume.restrict (c.dec ⁻¹' {ŵ}), False :=
      h0.mono fun y hy => (hqpos y).ne' hy
    have hr : volume.restrict (c.dec ⁻¹' {ŵ}) = 0 :=
      ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hall)
    simp [msgLaw, hT, hr]
  have hgold := mutualInfo_le_sum_log_div hμ hQ hQμ
  have hM' : (M : ℝ)⁻¹ ≠ 0 := inv_ne_zero hM0
  have hrhs : ∑ w, ∑ ŵ, c.msgLaw 1 (w, ŵ) *
      log (c.msgLaw 1 (w, ŵ) / (dist (c.msgLaw 1) Prod.fst w * Q ŵ)) =
      (M : ℝ)⁻¹ * ∑ w, ∑ ŵ, c.transProb 1 w ŵ * log (c.transProb 1 w ŵ / Q ŵ) := by
    rw [mul_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ŵ _ => ?_
    simp only [msgLaw, dist_fst_msgLaw]
    rw [mul_div_mul_left _ _ hM', mul_assoc]
  have hdp : ∀ w, ∑ ŵ, c.transProb 1 w ŵ * log (c.transProb 1 w ŵ / Q ŵ) ≤
      ∑ j, (log (S j / (1 : ℝ≥0)) / 2 - 1 / 2 + (c.enc w j ^ 2 + (1 : ℝ≥0)) / (2 * S j)) := by
    intro w
    obtain ⟨hint, heq⟩ := relEntropyPDF_shifted_diag hS (c.enc w)
    rw [← heq]
    simp only [hT]
    exact sum_mul_log_div_le_relEntropyPDF (shiftedNoisePDF_isPDF one_ne_zero _) hq hqpos hint
      c.measurableSet_cell
  have havg : (M : ℝ)⁻¹ * ∑ w : Fin M, ∑ j, (log (S j / (1 : ℝ≥0)) / 2 - 1 / 2 +
      (c.enc w j ^ 2 + (1 : ℝ≥0)) / (2 * S j)) = ∑ j, 1 / 2 * log (1 + c.avgPower j) := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have hsj := (hSpos j).ne'
    have e1 : ∑ w : Fin M, (log (S j / (1 : ℝ≥0)) / 2 - 1 / 2 +
        (c.enc w j ^ 2 + (1 : ℝ≥0)) / (2 * S j)) =
        M * (log (S j) / 2 - 1 / 2 + 1 / (2 * S j)) + (∑ w, c.enc w j ^ 2) / (2 * S j) := by
      simp only [NNReal.coe_one, div_one]
      have e0 : ∀ w : Fin M, log (S j) / 2 - 1 / 2 + (c.enc w j ^ 2 + 1) / (2 * S j) =
          (log (S j) / 2 - 1 / 2 + 1 / (2 * S j)) + c.enc w j ^ 2 / (2 * S j) := fun w => by
        ring
      simp only [e0]
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_div]
    rw [e1, mul_add, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    have e2 : (M : ℝ)⁻¹ * ((∑ w, c.enc w j ^ 2) / (2 * S j)) = c.avgPower j / (2 * S j) := by
      rw [avgPower]
      ring
    rw [e2, hS']
    have h1 : 1 + c.avgPower j ≠ 0 := by rw [← hS']; exact hsj
    field_simp
    ring
  calc I[Prod.fst : Prod.snd ; c.msgLaw 1]
      ≤ (M : ℝ)⁻¹ * ∑ w, ∑ ŵ, c.transProb 1 w ŵ * log (c.transProb 1 w ŵ / Q ŵ) :=
        hgold.trans_eq hrhs
    _ ≤ (M : ℝ)⁻¹ * ∑ w : Fin M, ∑ j, (log (S j / (1 : ℝ≥0)) / 2 - 1 / 2 +
          (c.enc w j ^ 2 + (1 : ℝ≥0)) / (2 * S j)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun w _ => hdp w) (by positivity)
    _ = _ := havg

/-- **The bound for parallel channels.** Every code has
`(1 - Pₑ) log M ≤ log 2 + ∑ⱼ ½ log (1 + (1/M) ∑_w xⱼ(w)²)`. -/
theorem one_sub_avgErrProb_mul_log_le_sum (hM : 0 < M) :
    (1 - c.avgErrProb 1) * log M ≤ log 2 + ∑ j, 1 / 2 * log (1 + c.avgPower j) := by
  have hμ := c.msgLaw_isPMF 1 hM
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ (Prod.fst : Fin M × Fin M → Fin M)
    Prod.snd
  have h2 := fano_weak hμ (Prod.fst : Fin M × Fin M → Fin M) Prod.snd id
  rw [c.errProb_msgLaw 1, Fintype.card_fin] at h2
  have h3 := c.mutualInfo_msgLaw_le_sum hM
  rw [c.entropy_fst_msgLaw 1 hM] at h1
  linarith

end GaussianCode

section ParallelIndex

variable {ι : Type*} [Fintype ι] {M : ℕ}

/-- The bound for parallel channels, for an arbitrary finite index set. -/
theorem one_sub_err_mul_log_le_of_parallel (hM : 0 < M) (x : Fin M → ι → ℝ)
    (dec : (ι → ℝ) → Fin M) (hd : Measurable dec) :
    (1 - (∑ w, (stdNoise ι).real {z | dec (x w + z) ≠ w}) / M) * log M ≤
      log 2 + ∑ j, 1 / 2 * log (1 + (M : ℝ)⁻¹ * ∑ w, x w j ^ 2) := by
  classical
  set e := Fintype.equivFin ι
  let c : GaussianCode M (Fintype.card ι) :=
    ⟨fun w j => x w (e.symm j), fun y => dec fun i => y (e i), hd.comp (by fun_prop)⟩
  have h := c.one_sub_avgErrProb_mul_log_le_sum hM
  have hsum : ∑ j, 1 / 2 * log (1 + c.avgPower j) =
      ∑ j, 1 / 2 * log (1 + (M : ℝ)⁻¹ * ∑ w, x w j ^ 2) :=
    e.symm.sum_comp fun j => 1 / 2 * log (1 + (M : ℝ)⁻¹ * ∑ w, x w j ^ 2)
  have herr : ∀ w, c.condErrProb 1 w = (stdNoise ι).real {z | dec (x w + z) ≠ w} := fun w => by
    have hmeas : MeasurableSet {z : ι → ℝ | dec (x w + z) ≠ w} :=
      (hd.comp (measurable_const_add (x w))) (measurableSet_singleton w).compl
    have hm : Measurable fun (z : Fin (Fintype.card ι) → ℝ) (i : ι) => z (e i) := by fun_prop
    rw [← map_stdNoise_reindex e, map_measureReal_apply hm hmeas]
    change (noiseLaw 1 _).real _ = (noiseLaw 1 _).real _
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, c]
    have ez : (fun i => ((fun j => x w (e.symm j)) + z) (e i)) = x w + fun i => z (e i) := by
      funext i
      simp
    rw [ez]
  have hA : c.avgErrProb 1 = (∑ w, (stdNoise ι).real {z | dec (x w + z) ≠ w}) / M := by
    simp only [GaussianCode.avgErrProb, herr]
  rwa [hA, hsum] at h

end ParallelIndex

/-! ### Codes for the vector channel -/

/-- **Lecture 10 of [elgamal2010], pages 10-2 and 10-3.** A code for the Gaussian vector channel
with
`t` inputs and `r` outputs: an encoder and a measurable decoder of the output `y(i, k)`, the output
`k` at the time `i`. -/
structure GVCode (M n : ℕ) (r t : Type*) where
  /-- The encoder `w ↦ (x(w, 1), …, x(w, n))`. -/
  enc : Fin M → Fin n → t → ℝ
  /-- The decoder. -/
  dec : (Fin n × r → ℝ) → Fin M
  measurable_dec : Measurable dec

namespace GVCode

variable {M n : ℕ} {r t : Type*} [Fintype r] [Fintype t] (c : GVCode M n r t)

/-- **Lecture 10, page 10-3.** The power constraint `∑ᵢ x(w, i)ᵀ x(w, i) ≤ n P`. -/
def SatisfiesPower (P : ℝ) : Prop := ∀ w, ∑ i, ∑ k, c.enc w i k ^ 2 ≤ n * P

variable (G : Matrix r t ℝ)

/-- The noiseless output `G x(w, i)`. -/
def out (w : Fin M) : Fin n × r → ℝ := fun p => (G *ᵥ c.enc w p.1) p.2

/-- The probability of error for the message `w`. -/
def condErrProb (w : Fin M) : ℝ := (stdNoise (Fin n × r)).real {z | c.dec (c.out G w + z) ≠ w}

/-- The average probability of error. -/
def avgErrProb : ℝ := (∑ w, c.condErrProb G w) / M

lemma avgErrProb_nonneg : 0 ≤ c.avgErrProb G :=
  div_nonneg (sum_nonneg fun _ _ => measureReal_nonneg) (Nat.cast_nonneg _)

lemma avgErrProb_le_one : c.avgErrProb G ≤ 1 := by
  rw [avgErrProb]
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  calc ∑ w, c.condErrProb G w ≤ ∑ _w : Fin M, (1 : ℝ) := sum_le_sum fun _ _ => measureReal_le_one
    _ = M := by simp

end GVCode

/-- **Lecture 10 of [elgamal2010].** A rate `R`, in bits per transmission, is achievable for the
Gaussian vector channel `Y = G X + Z`, `Z ∼ N(0, I)`, with power constraint `P`, if there are
`(2^{nR}, n)` codes satisfying the power constraint whose average probability of error tends to
`0`. -/
def IsAchievableGV {r t : Type*} [Fintype r] [Fintype t] (G : Matrix r t ℝ) (P : ℝ≥0) (R : ℝ) :
    Prop :=
  ∃ c : ∀ n : ℕ, GVCode (2 ^ ⌈n * R⌉₊) n r t, (∀ n, (c n).SatisfiesPower P) ∧
    Tendsto (fun n => (c n).avgErrProb G) atTop (𝓝 0)

/-- **Lecture 10 of [elgamal2010].** The capacity of the Gaussian vector channel, in bits per
transmission. -/
def opCapacityGV {r t : Type*} [Fintype r] [Fintype t] (G : Matrix r t ℝ) (P : ℝ≥0) : ℝ :=
  sSup {R | IsAchievableGV G P R}

/-! ### Rotating the outputs -/

section Rotation

variable {n : ℕ} {r : Type*} [Fintype r] [DecidableEq r]

/-- The rotation of the outputs at each time by `U`. -/
def blockRot (n : ℕ) (U : Matrix r r ℝ) : Matrix (Fin n × r) (Fin n × r) ℝ :=
  Matrix.of fun p q => if p.1 = q.1 then U p.2 q.2 else 0

omit [DecidableEq r] in
lemma blockRot_mulVec (U : Matrix r r ℝ) (z : Fin n × r → ℝ) (p : Fin n × r) :
    (blockRot n U *ᵥ z) p = (U *ᵥ fun l => z (p.1, l)) p.2 := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, blockRot, Matrix.of_apply, ite_mul,
    zero_mul, sum_ite_irrel, sum_const_zero]
  rw [sum_ite_eq univ p.1]
  simp

lemma blockRot_orth {U : Matrix r r ℝ} (hU : Uᵀ * U = 1) :
    (blockRot n U)ᵀ * blockRot n U = 1 := by
  ext p q
  have h := congrArg (fun A : Matrix r r ℝ => A p.2 q.2) hU
  simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply] at h
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [transpose_apply, blockRot, Matrix.of_apply]
  rw [sum_eq_single p.1 (fun i _ hi => sum_eq_zero fun l _ => by simp [hi]) (by simp)]
  by_cases hpq : p.1 = q.1
  · simp only [hpq, ite_true]
    rw [h]
    by_cases h2 : p.2 = q.2
    · simp [Prod.ext hpq h2]
    · have : p ≠ q := fun e => h2 (congrArg Prod.snd e)
      simp [this, h2]
  · have : p ≠ q := fun e => hpq (congrArg Prod.fst e)
    simp [this, hpq]

end Rotation

/-! ### The converse -/

section Converse

variable {M n : ℕ} {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]

namespace GVCode

variable (c : GVCode M n r t) (G : Matrix r t ℝ)

/-- The matrix of all the transmitted vectors. -/
def codeMatrix : Matrix (Fin M × Fin n) t ℝ := Matrix.of fun p k => c.enc p.1 p.2 k

/-- The average covariance `K̄ = (1/(M n)) ∑_w ∑ᵢ x(w, i) x(w, i)ᵀ` of the codewords. -/
def avgCov : Matrix t t ℝ := ((M : ℝ) * n)⁻¹ • (c.codeMatrixᵀ * c.codeMatrix)

omit [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t] in
lemma avgCov_posSemidef [Finite t] : c.avgCov.PosSemidef := by
  have := Fintype.ofFinite t
  refine PosSemidef.smul ?_ (by positivity)
  simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self c.codeMatrix

omit [Fintype r] [DecidableEq r] [DecidableEq t] in
/-- `(A K̄ Aᵀ)ₖₖ = (1/(M n)) ∑_w ∑ᵢ ((A x(w, i))ₖ)²`. -/
lemma diag_mul_avgCov {r' : Type*} (A : Matrix r' t ℝ) (k : r') :
    (A * c.avgCov * Aᵀ) k k = ((M : ℝ) * n)⁻¹ * ∑ w, ∑ i, ((A *ᵥ c.enc w i) k) ^ 2 := by
  have e : A * c.avgCov * Aᵀ =
      ((M : ℝ) * n)⁻¹ • ((c.codeMatrix * Aᵀ)ᵀ * (c.codeMatrix * Aᵀ)) := by
    rw [avgCov, Matrix.mul_smul, Matrix.smul_mul]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fintype.sum_prod_type]
  congr 1
  refine sum_congr rfl fun w _ => sum_congr rfl fun i _ => ?_
  rw [transpose_apply, sq]
  have h : (c.codeMatrix * Aᵀ) (w, i) k = (A *ᵥ c.enc w i) k := by
    simp only [Matrix.mul_apply, codeMatrix, Matrix.of_apply, transpose_apply, mulVec, dotProduct]
    exact sum_congr rfl fun l _ => mul_comm _ _
  rw [h]

omit [Fintype r] [DecidableEq r] [DecidableEq t] in
lemma trace_avgCov_le (hM : 0 < M) (hn : 0 < n) {P : ℝ} (hc : c.SatisfiesPower P) :
    c.avgCov.trace ≤ P := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : c.avgCov.trace = ((M : ℝ) * n)⁻¹ * ∑ w, ∑ i, ∑ k, c.enc w i k ^ 2 := by
    rw [avgCov, trace_smul, smul_eq_mul, trace_mul_comm, trace]
    congr 1
    simp only [diag_apply, Matrix.mul_apply, transpose_apply, codeMatrix, Matrix.of_apply,
      Fintype.sum_prod_type, sq]
  rw [e, inv_mul_le_iff₀ (by positivity)]
  calc ∑ w, ∑ i, ∑ k, c.enc w i k ^ 2 ≤ ∑ _w : Fin M, (n * P) := sum_le_sum fun w _ => hc w
    _ = M * n * P := by simp [mul_assoc]

omit [DecidableEq t] in
/-- **Lecture 10, page 10-3 (converse).** Every code has
`(1 - Pₑ) log M ≤ log 2 + n · ½ log |G K̄ Gᵀ + I|`, with `K̄` the average covariance of the
codewords. -/
theorem one_sub_avgErrProb_mul_log_le (hM : 0 < M) (hn : 0 < n) :
    (1 - c.avgErrProb G) * log M ≤ log 2 + n * gvRate G c.avgCov := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hK := c.avgCov_posSemidef
  have hS := posDef_add_one (posSemidef_mul_mul_transpose hK G)
  set S := G * c.avgCov * Gᵀ + 1 with hSd
  set U := eigvecs hS.1
  set lam := hS.1.eigenvalues
  have hUU : Uᵀ * U = 1 := eigvecs_transpose_mul hS.1
  have hUU' : U * Uᵀ = 1 := eigvecs_mul_transpose hS.1
  have hlam : ∀ k, 0 < lam k := hS.eigenvalues_pos
  have hspec : Uᵀ * S * U = diagonal lam := by
    have h : S = U * diagonal lam * Uᵀ := eq_eigvecs hS.1
    calc Uᵀ * S * U = (Uᵀ * U) * diagonal lam * (Uᵀ * U) := by
          rw [h]
          simp only [Matrix.mul_assoc]
      _ = diagonal lam := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  set A := Uᵀ * G with hA
  have hAdiag : ∀ k, (A * c.avgCov * Aᵀ) k k = lam k - 1 := fun k => by
    have e : A * c.avgCov * Aᵀ = Uᵀ * S * U - 1 := by
      rw [hSd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, add_sub_cancel_right, hA]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e, hspec, Matrix.sub_apply, diagonal_apply_eq, Matrix.one_apply_eq]
  -- The parallel channels.
  set x : Fin M → Fin n × r → ℝ := fun w p => (A *ᵥ c.enc w p.1) p.2 with hx
  set Q := blockRot n U with hQ
  have hQo : Qᵀ * Q = 1 := blockRot_orth hUU
  have hQm : Measurable fun z : Fin n × r → ℝ => Q *ᵥ z :=
    (Matrix.mulVecLin Q).continuous_of_finiteDimensional.measurable
  have hQx : ∀ w, Q *ᵥ x w = c.out G w := fun w => by
    funext p
    rw [hQ, blockRot_mulVec]
    have e : (fun l => x w (p.1, l)) = Uᵀ *ᵥ (G *ᵥ c.enc w p.1) := by
      funext l
      simp only [hx, hA, ← Matrix.mulVec_mulVec]
    rw [e, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
    rfl
  have hdec : Measurable fun y => c.dec (Q *ᵥ y) := c.measurable_dec.comp hQm
  have hb := one_sub_err_mul_log_le_of_parallel hM x (fun y => c.dec (Q *ᵥ y)) hdec
  have herr : ∀ w, (stdNoise (Fin n × r)).real {z | c.dec (Q *ᵥ (x w + z)) ≠ w} =
      c.condErrProb G w := fun w => by
    have hmeas : MeasurableSet {z : Fin n × r → ℝ | c.dec (c.out G w + z) ≠ w} :=
      (c.measurable_dec.comp (measurable_const_add _)) (measurableSet_singleton w).compl
    rw [condErrProb, ← map_stdNoise_of_orthogonal hQo, map_measureReal_apply hQm hmeas,
      map_stdNoise_of_orthogonal hQo]
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Matrix.mulVec_add, hQx]
  have hA2 : (∑ w, (stdNoise (Fin n × r)).real {z | c.dec (Q *ᵥ (x w + z)) ≠ w}) / M =
      c.avgErrProb G := by
    simp only [herr, avgErrProb]
  rw [hA2] at hb
  refine hb.trans (add_le_add le_rfl ?_)
  -- Averaging over the time and using the eigenvalues.
  rw [Fintype.sum_prod_type, sum_comm]
  have hk : ∀ k, ∑ i, 1 / 2 * log (1 + (M : ℝ)⁻¹ * ∑ w, x w (i, k) ^ 2) ≤
      n * (1 / 2 * log (lam k)) := fun k => by
    set a : Fin n → ℝ := fun i => (M : ℝ)⁻¹ * ∑ w, x w (i, k) ^ 2 with ha
    have ha0 : ∀ i, 0 ≤ a i := fun i =>
      mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)
    have hb' : ∑ i, a i = n * (lam k - 1) := by
      rw [← hAdiag, c.diag_mul_avgCov A k]
      have e : ∑ i, a i = (M : ℝ)⁻¹ * ∑ w, ∑ i, ((A *ᵥ c.enc w i) k) ^ 2 := by
        simp only [ha, hx]
        rw [← mul_sum, sum_comm]
      rw [e]
      field_simp
    have hb0 : 0 ≤ lam k - 1 := by
      have : 0 ≤ ∑ i, a i := sum_nonneg fun i _ => ha0 i
      rw [hb'] at this
      exact nonneg_of_mul_nonneg_right this hn'
    have hterm : ∀ i, log (1 + a i) ≤ log (lam k) + (a i - (lam k - 1)) / lam k := fun i => by
      have h := log_one_add_div_le one_pos (ha0 i) hb0
      simp only [div_one] at h
      have e1 : 1 + (lam k - 1) = lam k := by ring
      rwa [e1] at h
    have hsum : ∑ i, log (1 + a i) ≤ n * log (lam k) := by
      calc ∑ i, log (1 + a i) ≤ ∑ i, (log (lam k) + (a i - (lam k - 1)) / lam k) :=
            sum_le_sum fun i _ => hterm i
        _ = n * log (lam k) := by
            rw [sum_add_distrib, ← sum_div, sum_sub_distrib, hb', sum_const, sum_const, card_univ,
              Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, sub_self, zero_div, add_zero]
    rw [← mul_sum]
    nlinarith
  calc ∑ k, ∑ i, 1 / 2 * log (1 + (M : ℝ)⁻¹ * ∑ w, x w (i, k) ^ 2)
      ≤ ∑ k, n * (1 / 2 * log (lam k)) := sum_le_sum fun k _ => hk k
    _ = n * gvRate G c.avgCov := by
        rw [gvRate, ← hSd, hS.1.det_eq_prod_eigenvalues]
        simp only [RCLike.ofReal_real_eq_id, id]
        rw [log_prod fun k _ => (hlam k).ne', ← mul_sum, ← mul_sum]

end GVCode

omit [DecidableEq t] in
/-- **Theorem 1 of Lecture 10 (converse).** Every achievable rate is at most the capacity formula,
in
bits. -/
theorem IsAchievableGV.le {G : Matrix r t ℝ} {P : ℝ≥0} {R : ℝ} (h : IsAchievableGV G P R) :
    R ≤ gvCapacity G P / log 2 := by
  obtain ⟨c, hpow, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  have h1 : ∀ n, (c n).avgErrProb G ≤ 1 := fun n => (c n).avgErrProb_le_one G
  have key := le_of_converse_bound (R := R * log 2) (C := gvCapacity G P) hc h1
    fun n hn => by
      have hb := (c n).one_sub_avgErrProb_mul_log_le G (hpos n) hn
      have hr : gvRate G (c n).avgCov ≤ gvCapacity G P :=
        gvRate_le_gvCapacity G (c n).avgCov_posSemidef
          ((c n).trace_avgCov_le (hpos n) hn (hpow n))
      have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (by linarith [h1 n]))
        (hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr hn')))
      exact log_le_log (Nat.cast_pos.2 (Nat.ceil_pos.2 (exp_pos _)))
        (by exact_mod_cast ceil_exp_le_two_pow n R)
  rwa [le_div_iff₀ (log_pos one_lt_two)]

end Converse

/-! ### Achievability -/

section Achievability

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
  {G : Matrix r t ℝ} {U : Matrix r r ℝ} {Ψ : Matrix t r ℝ} {γ : r → ℝ}

omit [DecidableEq t] in
/-- `‖Ψ v‖² = ∑ₖ sₖ vₖ²`. -/
private lemma sum_sq_mulVec_svd (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ)) (v : r → ℝ) :
    ∑ l, (Ψ *ᵥ v) l ^ 2 = ∑ k, svdSupport γ k * v k ^ 2 := by
  have h : (Ψ *ᵥ v) ⬝ᵥ (Ψ *ᵥ v) = v ⬝ᵥ ((Ψᵀ * Ψ) *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Ψᵀ, Matrix.vecMul_transpose]
  rw [hΨ] at h
  simp only [dotProduct, mulVec_diagonal] at h
  simp only [sq]
  rw [h]
  exact sum_congr rfl fun k _ => by ring

omit [DecidableEq t] in
/-- `(Uᵀ G Ψ v)ₖ = γₖ vₖ`. -/
private lemma mulVec_svd (hU : Uᵀ * U = 1) (hG : G = U * diagonal γ * Ψᵀ)
    (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ)) (v : r → ℝ) (k : r) :
    (Uᵀ *ᵥ (G *ᵥ (Ψ *ᵥ v))) k = γ k * v k := by
  have e : Uᵀ * G * Ψ = diagonal γ := by
    rw [hG]
    calc Uᵀ * (U * diagonal γ * Ψᵀ) * Ψ = (Uᵀ * U) * diagonal γ * (Ψᵀ * Ψ) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal γ := by
          rw [hU, Matrix.one_mul, hΨ, diagonal_mul_diagonal]
          congr 1
          funext l
          exact mul_svdSupport γ l
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, mulVec_diagonal]

omit [DecidableEq t] in
/-- **Lecture 10, page 10-7.** A code from codes for the subchannels: the transmitted vector is
`Ψ X̃` and the decoder decodes each coordinate of `Uᵀ Y`. -/
private lemma exists_gvCode_of_product (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hG : G = U * diagonal γ * Ψᵀ) (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ))
    {n M : ℕ} (hM : 0 < M) {m : {k // γ k ≠ 0} → ℕ} (φ : Fin M ↪ ∀ k, Fin (m k))
    (cs : ∀ k, GaussianCode (m k) n) {p : {k // γ k ≠ 0} → ℝ}
    (hcs : ∀ k, (cs k).SatisfiesPower (γ k ^ 2 * p k)) {P : ℝ} (hP : ∑ k, p k ≤ P) :
    ∃ c : GVCode M n r t, c.SatisfiesPower P ∧ c.avgErrProb G ≤ ∑ k, (cs k).maxErrProb 1 := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hγ : ∀ k : {k // γ k ≠ 0}, γ k ^ 2 ≠ 0 := fun k => pow_ne_zero 2 k.2
  set v : Fin M → Fin n → r → ℝ := fun w i k =>
    if h : γ k ≠ 0 then (γ k)⁻¹ * (cs ⟨k, h⟩).enc (φ w ⟨k, h⟩) i else 0 with hv
  have hvs : ∀ w i (k : {k // γ k ≠ 0}), v w i k = (γ k)⁻¹ * (cs k).enc (φ w k) i := fun w i k => by
    simp [hv, k.2]
  set B := blockRot n Uᵀ with hB
  have hBo : Bᵀ * B = 1 := blockRot_orth (by rw [transpose_transpose]; exact hU')
  have hBm : Measurable fun z : Fin n × r → ℝ => B *ᵥ z :=
    (Matrix.mulVecLin B).continuous_of_finiteDimensional.measurable
  set D : (Fin n × r → ℝ) → ∀ k, Fin (m k) :=
    fun y k => (cs k).dec fun i => (B *ᵥ y) (i, k.1) with hD
  have hDm : Measurable D := by
    refine measurable_pi_iff.2 fun k => (cs k).measurable_dec.comp ?_
    exact measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp hBm
  have hinv : Measurable (Function.invFun φ) := Measurable.of_discrete
  let c : GVCode M n r t := ⟨fun w i => Ψ *ᵥ v w i, fun y => Function.invFun φ (D y),
    hinv.comp hDm⟩
  refine ⟨c, fun w => ?_, ?_⟩
  · -- The power constraint.
    have e1 : ∀ i, ∑ l, c.enc w i l ^ 2 = ∑ k : {k // γ k ≠ 0}, v w i k ^ 2 := fun i => by
      change ∑ l, (Ψ *ᵥ v w i) l ^ 2 = _
      rw [sum_sq_mulVec_svd hΨ]
      rw [sum_subtype_of_zero γ fun k hk => by simp [svdSupport, hk]]
      exact sum_congr rfl fun k _ => by simp [svdSupport, k.2]
    simp only [e1]
    rw [sum_comm]
    have e2 : ∀ k : {k // γ k ≠ 0}, ∑ i, v w i k ^ 2 ≤ n * p k := fun k => by
      have h := hcs k (φ w k)
      have e3 : ∑ i, v w i k ^ 2 = (γ k ^ 2)⁻¹ * ∑ i, (cs k).enc (φ w k) i ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [hvs, mul_pow, inv_pow]
      rw [e3, inv_mul_le_iff₀ (lt_of_le_of_ne (sq_nonneg _) (hγ k).symm)]
      linarith
    calc ∑ k : {k // γ k ≠ 0}, ∑ i, v w i k ^ 2 ≤ ∑ k : {k // γ k ≠ 0}, n * p k :=
          sum_le_sum fun k _ => e2 k
      _ = n * ∑ k, p k := by rw [mul_sum]
      _ ≤ n * P := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg n)
  · -- The probability of error.
    have hBout : ∀ w (i : Fin n) (k : {k // γ k ≠ 0}), (B *ᵥ c.out G w) (i, k.1) =
        (cs k).enc (φ w k) i := fun w i k => by
      rw [hB, blockRot_mulVec]
      change (Uᵀ *ᵥ (G *ᵥ (Ψ *ᵥ v w i))) k.1 = _
      rw [mulVec_svd hU hG hΨ, hvs, ← mul_assoc, mul_inv_cancel₀ k.2, one_mul]
    have hfib : ∀ k : {k // γ k ≠ 0},
        (stdNoise (Fin n × r)).map (fun z (i : Fin n) => (B *ᵥ z) (i, k.1)) = noiseLaw 1 n :=
      fun k => by
      have hf : Measurable fun (z : Fin n × r → ℝ) (i : Fin n) => z (i, k.1) := by fun_prop
      have h := Measure.map_map (μ := stdNoise (Fin n × r)) hf hBm
      rw [map_stdNoise_of_orthogonal hBo, map_stdNoise_fiber] at h
      exact h.symm
    have hkerr : ∀ w (k : {k // γ k ≠ 0}), (stdNoise (Fin n × r)).real
        {z | D (c.out G w + z) k ≠ φ w k} ≤ (cs k).maxErrProb 1 := fun w k => by
      refine le_trans (le_of_eq ?_) ((cs k).condErrProb_le_maxErrProb 1 (φ w k))
      have hmeas : MeasurableSet {y : Fin n → ℝ | (cs k).dec ((cs k).enc (φ w k) + y) ≠ φ w k} :=
        ((cs k).measurable_dec.comp (measurable_const_add _))
          (measurableSet_singleton _).compl
      have hTm : Measurable fun (z : Fin n × r → ℝ) (i : Fin n) => (B *ᵥ z) (i, k.1) :=
        measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp hBm
      rw [GaussianCode.condErrProb, ← hfib k, map_measureReal_apply hTm hmeas]
      congr 1
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hD, Matrix.mulVec_add]
      have ez : (fun i => (B *ᵥ c.out G w + B *ᵥ z) (i, k.1)) =
          (cs k).enc (φ w k) + fun i => (B *ᵥ z) (i, k.1) := by
        funext i
        simp only [Pi.add_apply, hBout]
      rw [ez]
    have hw : ∀ w, c.condErrProb G w ≤ ∑ k, (cs k).maxErrProb 1 := fun w => by
      have hsub : {z | c.dec (c.out G w + z) ≠ w} ⊆
          ⋃ k, {z | D (c.out G w + z) k ≠ φ w k} := by
        intro z hz
        by_contra hnot
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot
        apply hz
        change Function.invFun φ (D (c.out G w + z)) = w
        rw [funext hnot]
        exact Function.leftInverse_invFun φ.injective w
      refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans ?_)
      exact sum_le_sum fun k _ => hkerr w k
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    rw [GVCode.avgErrProb, div_le_iff₀ hM']
    calc ∑ w, c.condErrProb G w ≤ ∑ _w : Fin M, ∑ k, (cs k).maxErrProb 1 :=
          sum_le_sum fun w _ => hw w
      _ = (∑ k, (cs k).maxErrProb 1) * M := by simp [mul_comm]

omit [DecidableEq t] in
/-- **Theorem 1 of Lecture 10 (achievability).** A rate below the rate of an allowed covariance
matrix is achievable. -/
theorem isAchievableGV_of_lt_gvRate {G : Matrix r t ℝ} {P : ℝ≥0} {K : Matrix t t ℝ}
    (hK : K.PosSemidef) (htr : K.trace ≤ P) {R : ℝ} (hR : R * log 2 < gvRate G K) :
    IsAchievableGV G P R := by
  classical
  obtain ⟨U, Ψ, γ, hU, hU', -, hG, hΨ⟩ := exists_svd G
  have hΨ' : Ψᵀ * Ψ = diagonal (svdSupport γ) := hΨ
  have hl := log_pos one_lt_two
  have hM0 := posSemidef_transpose_mul_mul hK Ψ
  set q : {k // γ k ≠ 0} → ℝ := fun k => (Ψᵀ * K * Ψ : Matrix r r ℝ) k k with hq
  have hq0 : ∀ k, 0 ≤ q k := fun k => hM0.diag_nonneg
  have hqP : ∑ k, q k ≤ P := by
    refine le_trans ?_ ((trace_transpose_mul_mul_le hΨ' (svdSupport_cases γ) hK).trans htr)
    rw [trace]
    have := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset (fun k => γ k ≠ 0) univ)
      (f := fun k => (Ψᵀ * K * Ψ : Matrix r r ℝ) k k) fun k _ _ => hM0.diag_nonneg
    refine le_trans (le_of_eq ?_) this
    exact (Finset.sum_subtype (univ.filter fun k => γ k ≠ 0) (p := fun k => γ k ≠ 0) (by simp)
      fun k => (Ψᵀ * K * Ψ : Matrix r r ℝ) k k).symm
  set C : {k // γ k ≠ 0} → ℝ := fun k => 1 / 2 * log (1 + γ k ^ 2 * q k) with hC
  have hrate : gvRate G K ≤ ∑ k, C k := by
    refine (gvRate_le_sum hU hU' hG hK).trans (le_of_eq ?_)
    exact sum_subtype_of_zero γ fun k hk => by simp [hk]
  set card := Fintype.card {k // γ k ≠ 0}
  have hcard : (0 : ℝ) < card + 1 := by positivity
  set ε := (gvRate G K - R * log 2) / (card + 1) with hε
  have hεpos : 0 < ε := div_pos (by linarith) hcard
  set Rk : {k // γ k ≠ 0} → ℝ := fun k => C k - ε with hRk
  have hsumR : R * log 2 + ε ≤ ∑ k, Rk k := by
    have h1 : ∑ k, Rk k = ∑ k, C k - card * ε := by
      simp only [hRk, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
      rfl
    have h2 : (card + 1) * ε = gvRate G K - R * log 2 := mul_div_cancel₀ _ hcard.ne'
    rw [h1]
    nlinarith
  -- The codes for the subchannels.
  set pk : {k // γ k ≠ 0} → ℝ≥0 := fun k => ⟨γ k ^ 2 * q k, mul_nonneg (sq_nonneg _) (hq0 k)⟩
  have hach : ∀ k, IsAchievableGaussianRate (pk k) 1 (Rk k) := fun k =>
    isAchievableGaussianRate_of_lt one_ne_zero (by
      change C k - ε < 1 / 2 * log (1 + γ k ^ 2 * q k / ((1 : ℝ≥0) : ℝ))
      rw [NNReal.coe_one, div_one]
      simp only [hC]
      linarith)
  choose cs hpow htend using hach
  -- The number of messages.
  have hev : ∀ᶠ n : ℕ in atTop, 2 ^ ⌈n * R⌉₊ ≤ ∏ k, ⌈exp (n * Rk k)⌉₊ := by
    filter_upwards [eventually_ge_atTop ⌈log 2 / ε⌉₊] with n hn
    have hn' : log 2 ≤ n * ε := (div_le_iff₀ hεpos).1 (Nat.ceil_le.1 hn)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hprod : exp (n * ∑ k, Rk k) ≤ ((∏ k, ⌈exp (n * Rk k)⌉₊ : ℕ) : ℝ) := by
      push_cast
      rw [mul_sum, exp_sum]
      exact prod_le_prod₀ (fun _ _ => (exp_pos _).le) fun _ _ => Nat.le_ceil _
    have hone : (1 : ℝ) ≤ ((∏ k, ⌈exp (n * Rk k)⌉₊ : ℕ) : ℝ) := by
      have : 1 ≤ ∏ k, ⌈exp (n * Rk k)⌉₊ := Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2
        fun k _ => (Nat.ceil_pos.2 (exp_pos _)).ne')
      exact_mod_cast this
    have hreal : ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ ((∏ k, ⌈exp (n * Rk k)⌉₊ : ℕ) : ℝ) := by
      rcases le_or_gt R 0 with hR0 | hR0
      · rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos hn0 hR0)]
        simpa using hone
      · refine le_trans ?_ hprod
        push_cast
        calc (2 : ℝ) ^ ⌈n * R⌉₊ = 2 ^ (⌈n * R⌉₊ : ℝ) := (rpow_natCast 2 _).symm
          _ ≤ 2 ^ (n * R + 1) := rpow_le_rpow_of_exponent_le one_le_two
              (Nat.ceil_lt_add_one (mul_nonneg hn0 hR0.le)).le
          _ = exp (n * R * log 2 + log 2) := by
              rw [rpow_def_of_pos two_pos]
              congr 1
              ring
          _ ≤ exp (n * ∑ k, Rk k) := exp_le_exp.2 (by nlinarith)
    exact_mod_cast hreal
  have hsub : ∀ n : ℕ, ∃ c : GVCode (2 ^ ⌈n * R⌉₊) n r t, c.SatisfiesPower P ∧
      (2 ^ ⌈n * R⌉₊ ≤ ∏ k, ⌈exp (n * Rk k)⌉₊ →
        c.avgErrProb G ≤ ∑ k, (cs k n).maxErrProb 1) := fun n => by
    have hMpos : 0 < 2 ^ ⌈n * R⌉₊ := by positivity
    by_cases h : 2 ^ ⌈n * R⌉₊ ≤ ∏ k, ⌈exp (n * Rk k)⌉₊
    · have hcardle : Fintype.card (Fin (2 ^ ⌈n * R⌉₊)) ≤
          Fintype.card (∀ k : {k // γ k ≠ 0}, Fin ⌈exp (n * Rk k)⌉₊) := by
        simpa [Fintype.card_pi] using h
      obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hcardle
      obtain ⟨c, h1, h2⟩ := exists_gvCode_of_product hU hU' hG hΨ' hMpos φ (fun k => cs k n)
        (p := q) (fun k => hpow k n) hqP
      exact ⟨c, h1, fun _ => h2⟩
    · exact ⟨⟨fun _ _ _ => 0, fun _ => ⟨0, hMpos⟩, measurable_const⟩,
        fun w => by simpa using mul_nonneg (Nat.cast_nonneg n) P.2, fun h' => absurd h' h⟩
  choose c hcp hce using hsub
  refine ⟨c, hcp, ?_⟩
  have hlim : Tendsto (fun n => ∑ k, (cs k n).maxErrProb 1) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (univ : Finset {k // γ k ≠ 0}) fun k _ => htend k
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => (c n).avgErrProb_nonneg G) ?_
  filter_upwards [hev] with n hn
  exact hce n hn

omit [DecidableEq t] in
/-- **Theorem 1 of Lecture 10 of [elgamal2010], page 10-3.** The capacity of the Gaussian vector
channel `Y = G X + Z`, `Z ∼ N(0, I)`, with average power constraint `P`, is
`C = max_{K ≽ 0, tr K ≤ P} ½ log |G K Gᵀ + I|`, in bits per transmission. -/
theorem opCapacityGV_eq (G : Matrix r t ℝ) (P : ℝ≥0) :
    opCapacityGV G P = gvCapacity G P / log 2 := by
  have hl := log_pos one_lt_two
  have hzero : gvRate G (0 : Matrix t t ℝ) = 0 := by simp [gvRate]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨-1, isAchievableGV_of_lt_gvRate (K := 0) PosSemidef.zero (by simp) (by
      rw [hzero]
      linarith)⟩ (fun R hR => IsAchievableGV.le hR) fun w hw => ?_
  obtain ⟨R, hR1, hR2⟩ := exists_between hw
  have hR3 : R * log 2 < gvCapacity G P := (lt_div_iff₀ hl).1 hR2
  have hne : {v | ∃ K : Matrix t t ℝ, K.PosSemidef ∧ K.trace ≤ P ∧ gvRate G K = v}.Nonempty :=
    ⟨_, 0, PosSemidef.zero, by simp, rfl⟩
  rw [gvCapacity] at hR3
  obtain ⟨_, ⟨K, hK, htr, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hR3
  exact ⟨R, isAchievableGV_of_lt_gvRate hK htr hlt, hR1⟩

end Achievability

end InfoTheory
