/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.VectorCode
public import InfoTheoryLib.GaussianChannel.VectorFading
public import InfoTheoryLib.Network.GaussianVectorBC

/-!
# El Gamal & Kim, Lecture 10: Gaussian Vector Channels

This file indexes the formalization of Lecture 10 of [elgamal2010] and contains two examples. We
prove the capacity of the Gaussian vector channel as a coding theorem. The other results are about
the formulas: the coding theorems for the MAC and the BC are for continuous alphabets, and the
converse for the Gaussian vector BC needs the vector entropy power inequality, which the library
does not have.

## Conventions

* **Rates.** The coding theorem is in bits, as in Lecture 3. The formulas are in nats.
* **The noise.** It is `N(0, I)`; a general `K_Z ≻ 0` is whitened by `exists_mul_gvRate_eq`. In a
  code the output is indexed by the pairs `(i, k)` of a time and an antenna.
* **The singular value decomposition.** `exists_svd` keeps the index set of the outputs and allows
  `γₖ = 0`, so that `U` is square: `G = U D Ψᵀ` with `Ψᵀ Ψ = diag(1[γₖ ≠ 0])`.
* **Regions.** They are for nonnegative rates and with non-strict inequalities. With these, the
  convex hull of the two dirty paper coding regions is the dual MAC region without taking a closure.
* **Fading.** There are finitely many states, as in Lecture 8. Isotropy is the invariance of the law
  under sign flips and transpositions of the transmit antennas, which every orthogonally invariant
  law has, as a finitely supported law cannot be invariant under all orthogonal matrices unless
  `G = 0`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The Gaussian vector channel
* The codes: `GVCode`, `GVCode.SatisfiesPower`, `GVCode.avgErrProb`, `IsAchievableGV`,
  `opCapacityGV` (`GaussianChannel.VectorCode`).
* **Theorem 1**: `gvRate`, `gvCapacity` (`GaussianChannel.Vector`), `opCapacityGV_eq`, with the
  converse `IsAchievableGV.le` and achievability `isAchievableGV_of_lt_gvRate`.
* The tools: `map_stdNoise_of_orthogonal`, `blockRot`,
  `GaussianCode.one_sub_avgErrProb_mul_log_le_sum`,
  `GVCode.avgCov`, `GVCode.one_sub_avgErrProb_mul_log_le`.
* Whitening the noise: `exists_mul_gvRate_eq`.
* The singular values and water-filling: `exists_svd` (`ForMathlib.MatrixSVD`), `gvRate_le_sum`,
  `gvRate_diagonal`, `gvRate_le_waterFill`, `exists_gvRate_waterFill`, `gvCapacity_eq_waterFill`.
* The product channel: `gvRate_diagonal_gain`; one receive antenna: `gvCapacity_rowGain` (here).
* The **reciprocity lemma**: `exists_reciprocal`, `gvCapacity_transpose`.
* The alternative characterization by the KKT conditions, sufficiency: `log_det_le_of_kkt`, from
  `log_det_le_trace_sub_card` and `log_det_add_sub_le`.

### Gaussian vector fading channels (formulas)
* The rate and the formula: `gvFadingRate`, `gvFadingCapacity` (`GaussianChannel.VectorFading`).
* **Theorem 2**: `IsIsotropicFading`, `exists_sum_isoKernel_eq`, `gvFadingRate_le_isotropic`,
  `gvFadingCapacity_eq`, and the form with the eigenvalues `gvRate_isotropic_eq_sum`.
* Low and high SNR: `tendsto_gvRate_div`, `tendsto_gvFadingRate_div`, `tendsto_gvRate_sub_log`,
  `tendsto_gvFadingRate_sub_log`.

### Gaussian vector MAC (formulas)
* **The region of Theorem 3**: `gvMACRates`, `gvMACRegion` (`Network.GaussianVector`).
* The regions are closed: `isCompact_posSemidef_trace_le`, `isClosed_gvMACRegion`,
  `isClosed_gvSumMACRegion` (`Network.GaussianVectorClosed`).
* The corner points: `corner₁_mem_gvMACRates`, `corner₂_mem_gvMACRates`, by `det_add_one_add_le`.
* The fixed points of iterative water-filling: `log_det_mac_le_of_kkt`.

### The spectral Gaussian BC (formulas)
* **The region of the first Theorem 4**: `spectralBCRegion`; the rates to one receiver:
  `single_mem_spectralBCRegion` (`Network.GaussianVectorBC`).

### Vector writing on dirty paper (formulas)
* The MMSE gain: `mmseGain`, `mmseGain_orthogonal`; the rate: `det_mmseError_mul`
  (`GaussianChannel.Vector`).

### The Gaussian vector BC (formulas)
* The dirty paper coding regions: `dpcRate`, `dpcRegion₁`, `dpcRegion₂`.
* The dual MAC: `gvSumMACRegion`, `convex_gvSumMACRegion`.
* The **MAC–BC duality lemma**: `convexHull_dpcRegion_eq`, with the transformations
  `exists_dual_of_bc`, `exists_bc_of_dual`, and `dpcRegion₁_subset`, `dpcRegion₂_subset`,
  `gvSumMACRegion_subset_convexHull`.
* The enhanced degraded channel (`Network.GaussianVectorBC`): `enhSigma₁`, `enhSigma₂`, `enhK₁`,
  `enhK₂`, with `enhK₁_add_sigma₁`, `enhK₁_add_sigma₂`, `enhK_add_sigma₂`, `enhSigma₂_sub`,
  `enhK₁_posSemidef`, `enhK₂_posSemidef`, `enhSigma₂_sub_posSemidef`, `enhSigma₁_posDef`,
  `det_enhK₁_add_div`, `det_enhK_add_div`, `trace_enhK_add`, `log_det_add_sigma₂_le`,
  `det_smul_rpow_add`, `one_sub_mul_sigma_posSemidef`.
* Matrix inverses: `one_sub_inv_posSemidef`, `posSemidef_inv_sub_inv`.

## Not formalized

* The coding theorem for Theorem 3, the GV-MAC with more than two senders, and the convergence of
  iterative water-filling. The operational meaning of the rates of the fading channel.
* Necessity of the KKT conditions (we prove that they are sufficient, which is what is used here),
  and the equivalence with the product channel as a transformation of codes on pages 10-6 and 10-7.
* The coding theorem of the first Theorem 4, the product of reversely degraded DM-BCs with its
  proposition on page 10-26, and the private-message capacity region `C = C₁ ∩ C₂`.
* Vector writing on dirty paper as a coding theorem: the Gelfand–Pinsker theorem of Lecture 7 is for
  finite alphabets.
* The capacity region of the Gaussian vector BC (the second Theorem 4): the coding theorem of the
  dirty paper region, Lemma 3 as a statement about codes, and Lemma 4, which needs the vector
  entropy power inequality. We have the matrix facts that these proofs use.
* The boundary points of the dual MAC region as solutions of the optimization
  problem, the uniqueness of the supporting hyperplane, and more than two receivers.
* The figures on pages 10-40, 10-43 and 10-45.

## Issues in the notes

* **Numbering.** There are two results called Theorem 4, on pages 10-24 and 10-46, and the Lemmas 3
  and 4 have no Lemmas 1 and 2.
* **Pages 10-2 and 10-13.** The gain `Gⱼₖ` is described with `j` a transmit antenna and
  `j ∈ [1 : t]`, `k ∈ [1 : r]`, while `G` is an `r × t` matrix.
* **Page 10-5.** The water-filling condition has `Pⱼ` on the left and `γᵢ` on the right.
* **Page 10-12.** The stationarity condition has `λ* I_r` twice; it should be `λ* I_t`, as
  `Gᵀ (…)⁻¹ G` is `t × t` (`log_det_le_of_kkt`).
* **Page 10-29.** In the capacity region of the product of `d` reversely degraded DM-BCs, the first
  sum in each of the four bounds should run over `k ∈ [1 : r]`, not `[1 : d]`, as in the first
  Theorem 4 on page 10-24, and the pmf should be `∏ₖ p(uₖ, xₖ)`.
* **Page 10-37.** "the converse is does not follow".
* **Page 10-39.** The numerator of the bound on `R₂` in the second region has `I_t`; it should be
  `I_r`.
* **Page 10-46.** `Cⱼ` has `Gⱼᵀ Kⱼ Gⱼ + I_r`; it should be `I_t`.
* **Page 10-49.** The Lagrangian has `tr(Υ₁ K₂)`; it should be `tr(Υ₂ K₂)`.
* **Page 10-57.** `K₁** + K₂** + Σ₂ = (ᾱ/λ*) I_t` should be `(ᾱ/(2λ*)) I_t`, as in the definition on
  page 10-50 (`enhK_add_sigma₂`).
* **Page 10-65.** The second codeword is written with `M₁`; it should be `M₂`.
* **Page 10-67.** `P^{-1/2}` should be `Σ₁^{-1/2}`.
* **Page 10-70.** The derivative at `ε = 0` is set to `0`, but the perturbation
  `((1 - ε) K₁*, ε K₁* + K₂*)` is feasible only for `ε ≥ 0` unless the range of `K₁*` is in that of
  `K₂*`, so that optimality only gives that the derivative is at most `0`. The step that concludes
  from the two equalities needs a further argument. We do not formalize this appendix.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 10
-/

open Real Finset Matrix
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Aliases -/

section Aliases

variable {σ r t : Type*} [Fintype σ] [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]

omit [DecidableEq t] in
/-- **Theorem 1 of Lecture 10, page 10-3.** The capacity of the Gaussian vector channel. -/
theorem theorem_10_1 (G : Matrix r t ℝ) (P : ℝ≥0) :
    opCapacityGV G P = gvCapacity G P / log 2 :=
  opCapacityGV_eq G P

/-- **Theorem 2 of Lecture 10, page 10-14.** The formula for an isotropic gain matrix. -/
theorem theorem_10_2 {q : σ → ℝ} (hq : ∀ s, 0 ≤ q s) {G : σ → Matrix r t ℝ}
    (hiso : IsIsotropicFading q G) {P : ℝ} (hP : 0 ≤ P) (ht : 0 < Fintype.card t) :
    gvFadingCapacity q G P = gvFadingRate q G ((P / Fintype.card t) • 1) :=
  gvFadingCapacity_eq hq hiso hP ht

/-- **The reciprocity lemma of Lecture 10, page 10-9.** -/
theorem reciprocity_lemma (G : Matrix r t ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) :
    ∃ K' : Matrix r r ℝ, K'.PosSemidef ∧ K'.trace ≤ K.trace ∧
      (Gᵀ * K' * G + 1).det = (G * K * Gᵀ + 1).det :=
  exists_reciprocal G hK

/-- **The MAC–BC duality lemma of Lecture 10, page 10-41.** -/
theorem mac_bc_duality_lemma {r₁ r₂ : Type*} [Fintype r₁] [Fintype r₂] [DecidableEq r₁]
    [DecidableEq r₂] (G₁ : Matrix r₁ t ℝ) (G₂ : Matrix r₂ t ℝ) (P : ℝ) :
    convexHull ℝ (dpcRegion₁ G₁ G₂ P ∪ dpcRegion₂ G₁ G₂ P) = gvSumMACRegion G₁ᵀ G₂ᵀ P :=
  convexHull_dpcRegion_eq G₁ G₂ P

end Aliases

/-! ## Examples -/

section Examples

variable {t : Type*} [Fintype t] [DecidableEq t]

/-- **Lecture 10, page 10-3.** The vector channel with `G = diag(g)` is the Gaussian product
channel: the rate of `K = diag(p)` is `∑ⱼ ½ log (1 + gⱼ² pⱼ)`. -/
theorem gvRate_diagonal_gain {g p : t → ℝ} (hp : ∀ j, 0 ≤ p j) :
    gvRate (diagonal g) (diagonal p) = ∑ j, 1 / 2 * log (1 + g j ^ 2 * p j) := by
  have e : diagonal g * diagonal p * (diagonal g)ᵀ + 1 =
      (diagonal fun j => 1 + g j ^ 2 * p j : Matrix t t ℝ) := by
    rw [diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one,
      diagonal_add]
    congr 1
    funext j
    ring
  have hpos : ∀ j, 0 < 1 + g j ^ 2 * p j := fun j => by
    have := mul_nonneg (sq_nonneg (g j)) (hp j)
    linarith
  rw [gvRate, e, det_diagonal, log_prod fun j _ => (hpos j).ne', mul_sum]

/-- The channel to one receive antenna, with the gains `g`. -/
def rowGain (g : t → ℝ) : Matrix Unit t ℝ := Matrix.of fun _ k => g k

private lemma det_unit_add_one (M : Matrix Unit Unit ℝ) : (M + 1).det = M () () + 1 := by
  simp [det_unique]

omit [DecidableEq t] in
/-- `g K gᵀ ≤ ‖g‖² tr K`, by the Cauchy–Schwarz inequality. -/
private lemma mul_rowGain_le (g : t → ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) :
    (rowGain g * K * (rowGain g)ᵀ) () () ≤ (∑ j, g j ^ 2) * K.trace := by
  obtain ⟨C, rfl⟩ := exists_eq_transpose_mul_self hK
  have e : rowGain g * (Cᵀ * C) * (rowGain g)ᵀ = (C * (rowGain g)ᵀ)ᵀ * (C * (rowGain g)ᵀ) := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e, Matrix.mul_apply, trace_mul_comm, trace]
  simp only [transpose_apply, diag_apply, Matrix.mul_apply, rowGain, Matrix.of_apply]
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => C i j) g
  simp only [sq] at h ⊢
  calc (∑ j, C i j * g j) * (∑ j, C i j * g j) ≤ _ := by simpa [sq] using h
    _ = _ := by ring

omit [DecidableEq t] in
/-- **Example (Lecture 10), page 10-5.** With one receive antenna the capacity formula is
`½ log (1 + ‖g‖² P)`, attained by beamforming along `g`: the only singular value is `‖g‖`. -/
theorem gvCapacity_rowGain (g : t → ℝ) {P : ℝ} (hP : 0 ≤ P) (hg : 0 < ∑ j, g j ^ 2) :
    gvCapacity (rowGain g) P = 1 / 2 * log (1 + (∑ j, g j ^ 2) * P) := by
  set S := ∑ j, g j ^ 2 with hS
  have hG : (rowGain g * (rowGain g)ᵀ) () () = S := by
    simp [Matrix.mul_apply, rowGain, hS, sq]
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · refine ⟨(P / S) • ((rowGain g)ᵀ * rowGain g), ?_, ?_, ?_⟩
    · refine PosSemidef.smul ?_ (div_nonneg hP hg.le)
      simpa [conjTranspose_eq_transpose_of_trivial] using
        posSemidef_conjTranspose_mul_self (rowGain g)
    · rw [trace_smul, trace_mul_comm, trace]
      simp only [diag_apply, Fintype.sum_unique, smul_eq_mul]
      have h1 : (rowGain g * (rowGain g)ᵀ) default default = S := hG
      rw [h1, div_mul_cancel₀ _ hg.ne']
    · have e : rowGain g * ((P / S) • ((rowGain g)ᵀ * rowGain g)) * (rowGain g)ᵀ =
          (P / S) • ((rowGain g * (rowGain g)ᵀ) * (rowGain g * (rowGain g)ᵀ)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
      rw [gvRate, e, det_unit_add_one, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
      simp only [Fintype.sum_unique]
      have h1 : (rowGain g * (rowGain g)ᵀ) () default = S := hG
      rw [h1]
      congr 2
      field_simp
      ring
  · rintro _ ⟨K, hK, htr, rfl⟩
    have h0 : 0 ≤ (rowGain g * K * (rowGain g)ᵀ) () () :=
      (posSemidef_mul_mul_transpose hK (rowGain g)).diag_nonneg
    rw [gvRate, det_unit_add_one]
    refine mul_le_mul_of_nonneg_left (log_le_log (by linarith) ?_) (by norm_num)
    have := (mul_rowGain_le g hK).trans (mul_le_mul_of_nonneg_left htr hg.le)
    linarith

end Examples

end InfoTheory.ElGamalKim
