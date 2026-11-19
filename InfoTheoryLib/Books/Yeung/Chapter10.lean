/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.AEP
public import InfoTheoryLib.DifferentialEntropy.ChainRule
public import InfoTheoryLib.DifferentialEntropy.Gaussian
public import InfoTheoryLib.DifferentialEntropy.Mixed
public import InfoTheoryLib.DifferentialEntropy.Quantization
public import InfoTheoryLib.MaxEntropy.Basic
public import InfoTheoryLib.MaxEntropy.Covariance
public import InfoTheoryLib.Probability.CovarianceMatrix
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Yeung, Chapter 10: Differential Entropy

This file indexes the formalization of Chapter 10 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Densities.** A random variable or vector with a density is described by `f` with
  `IsPDF volume f`. Differential entropies are Bochner integrals, so results assume the
  integrability of the relevant `f log f` terms, the book's "assumed to be defined".
* **Logarithms.** Logarithms are natural, so differential entropies are in nats.
* **Random vectors.** Covariance and correlation matrices are those of a random vector
  `X : ι → Ω → ℝ` on a measure space, with square-integrable components `X i` (`MemLp _ 2`).
* **Mixed pairs.** In Definitions 10.21–10.30, `X` has any law `μ` on any measurable space and `Y`
  has the conditional density `f(y|x) = k x y` with respect to `ν`.
* **The support.** Integrals over the support `S` are integrals over the whole space of the
  density, which vanishes outside `S`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The introduction
* (10.4)–(10.5): Mathlib's `ProbabilityTheory.variance` and `ProbabilityTheory.covariance`.
* (10.6)–(10.7): `covMatrix` (`Probability.MMSE`), `corrMatrix` (`Probability.CovarianceMatrix`),
  for a random vector `X : ι → Ω → ℝ`.
* (10.8)–(10.14): `corrMatrix_eq_covMatrix_add` (`Probability.CovarianceMatrix`).
* (10.15)–(10.16): `gaussianPDFReal` (Mathlib), `mvGaussianPDF`
  (`DifferentialEntropy.MultivariateGaussian`).

### 10.1 Preliminaries
* Definitions 10.1 and 10.2: Mathlib's `Matrix.IsSymm`, `Matrix.PosDef`, `Matrix.PosSemidef`.
* Proposition 10.3: `proposition_10_3` (here), from `posSemidef_covMatrix` and
  `posSemidef_corrMatrix` (`Probability.CovarianceMatrix`). The book omits the proof.
* (10.19)–(10.25): Mathlib's spectral theorem `Matrix.IsHermitian.spectral_theorem`.
* Proposition 10.4: `proposition_10_4` (here), which is Mathlib's
  `Matrix.PosSemidef.eigenvalues_nonneg`.
* Proposition 10.5: `proposition_10_5` (here), from `covMatrix_mulVec` and `corrMatrix_mulVec`
  (`Probability.CovarianceMatrix`).
* Proposition 10.6: `proposition_10_6` (here), which is `covMatrix_transpose_mulVec`
  (`Probability.CovarianceMatrix`).
* Corollary 10.7: `corollary_10_7` (here), which is `eq_mulVec_transpose_mulVec`
  (`Probability.CovarianceMatrix`).
* Proposition 10.8: `proposition_10_8` (here), which is `covMatrix_add_of_indepFun`
  (`Probability.CovarianceMatrix`). The book omits the proof.
* Proposition 10.9: `proposition_10_9` (here), which is `integral_sum_sq_mulVec_of_orthogonal`
  (`Probability.CovarianceMatrix`).

### 10.2 Definition
* Definition 10.10: `diffEntropy` (`DifferentialEntropy.Basic`).
* Example 10.11: `example_10_11` (here). The dyadic expansion is replaced by quantization into
  `2ⁿ` cells: the entropy of the quantized variable tends to `∞`, through
  `tendsto_entropy_quantPMF_two_pow_sub` (`DifferentialEntropy.Quantization`).
* Example 10.12: `uniformPDF`, `diffEntropy_uniformPDF` (`DifferentialEntropy.Basic`), on `[0, a]`.
* Example 10.13: `diffEntropy_gaussianPDFReal` (`DifferentialEntropy.Gaussian`).
* Theorem 10.14: `theorem_10_14` (here), which is `diffEntropy_comp_sub`
  (`DifferentialEntropy.Basic`).
* Theorem 10.15: `theorem_10_15` (here), which is `diffEntropy_scale` (`DifferentialEntropy.Basic`).
* Example 10.16: `example_10_16` (here).

### 10.3 Joint Differential Entropy, Conditional (Differential) Entropy, and Mutual Information
* Definition 10.17: `diffEntropy` on `ι → ℝ` (`DifferentialEntropy.Basic`).
* (10.82): `diffEntropy_eq_sum_coordMarginal_iff` (`DifferentialEntropy.ChainRule`).
* Theorem 10.18: `diffEntropy_comp_sub` (`DifferentialEntropy.Basic`), for any normed space.
* Theorem 10.19: `theorem_10_19` (here), which is `diffEntropy_linearEquiv`
  (`DifferentialEntropy.Basic`).
* Theorem 10.20: `theorem_10_20` (here), which is `diffEntropy_mvGaussianPDF`
  (`DifferentialEntropy.MultivariateGaussian`). The proof changes variables to independent
  coordinates, as the book does.
* Definitions 10.21 and 10.22: `IsCondPDF`, `jointLawOfCondPDF`, `map_fst_jointLawOfCondPDF`
  (`DifferentialEntropy.Mixed`). A discrete `Y` (Definition 10.21) is the case of the counting
  measure `ν`.
* Definition 10.23: `condDiffEntropyOfCondPDF` (`DifferentialEntropy.Mixed`), and
  `condDiffEntropy` (`DifferentialEntropy.Joint`) for a joint density.
* Definitions 10.24 and 10.25: `IsBoundedPDF`, `IsBoundedCondPDF` (`DifferentialEntropy.Mixed`).
* Proposition 10.26: `proposition_10_26` (here), from `map_snd_jointLawOfCondPDF`, `isPDF_outPDF`
  and `isBoundedPDF_outPDF` (`DifferentialEntropy.Mixed`). The proof uses Tonelli's theorem rather
  than differentiating the conditional distribution function.
* Proposition 10.27: the same statement, which holds for any measurable space `𝒴`.
* Definition 10.28: `mutualInfoOfCondPDF` (`DifferentialEntropy.Mixed`), and `mutualInfoPDF`
  (`DifferentialEntropy.Joint`) for a joint density, (10.124).
* Definition 10.29: `condMutualInfoOfCondPDF` (`DifferentialEntropy.Mixed`).
* (10.127)–(10.135), the quantization interpretation of `I(X; Y)`:
  `sum_mul_log_div_le_relEntropyPDF` (`DifferentialEntropy.RelativeEntropy`) gives
  `I(X̂_Δ; Ŷ_Δ) ≤ I(X; Y)`.
* Definition 10.30: `condEntropyOfCondPDF` (`DifferentialEntropy.Mixed`).
* Proposition 10.31: `proposition_10_31` (here), which is `diffEntropy_outPDF_eq_add`
  (`DifferentialEntropy.Mixed`); (10.138) is `entropy_eq_condEntropyOfCondPDF_add`
  (`DifferentialEntropy.Mixed`); for joint densities, `mutualInfoPDF_eq_sub_condDiffEntropy`
  (`DifferentialEntropy.Joint`).
* Proposition 10.32: `proposition_10_32` (here), which is `diffEntropy_eq_sum_condDiffEntropyLast`
  (`DifferentialEntropy.ChainRule`), for a joint density.
* Theorem 10.33: the inequality `theorem_10_33` (here), which is `mutualInfoOfCondPDF_nonneg`,
  and the equality case `mutualInfoOfCondPDF_eq_zero_iff` (`DifferentialEntropy.Mixed`).
* Corollary 10.34: the inequality `corollary_10_34` (here), which is
  `condMutualInfoOfCondPDF_nonneg`, and the equality case `condMutualInfoOfCondPDF_eq_zero_iff`
  (`DifferentialEntropy.Mixed`).
* Corollary 10.35: `condDiffEntropy_le`, `condDiffEntropy_eq_iff` (`DifferentialEntropy.Joint`), for
  a joint density.
* Corollary 10.36: `diffEntropy_le_sum_coordMarginal`, `diffEntropy_eq_sum_coordMarginal_iff`
  (`DifferentialEntropy.ChainRule`).

### 10.4 The AEP for Continuous Random Variables
* Theorem 10.37: `theorem_10_37` (here), which is `tendstoInMeasure_sampleDiffEntropy`
  (`DifferentialEntropy.AEP`).
* Definition 10.38: `diffTypicalSet` (`DifferentialEntropy.AEP`), with `≤ ε` as in Definition 5.2,
  where Definition 10.38 has `< ε`, and with `f(xᵢ) > 0`; so the bounds of Theorem 10.40 are
  non-strict.
* Definition 10.39: Mathlib's `MeasureTheory.volume`.
* Theorem 10.40: `prodPDF_bounds`, `eventually_prob_diffTypicalSet_gt`, `volume_diffTypicalSet_le`,
  `eventually_volume_diffTypicalSet_ge` (`DifferentialEntropy.AEP`).

### 10.5 Informational Divergence
* Definition 10.41: `relEntropyPDF` (`DifferentialEntropy.RelativeEntropy`), with `f ≪ g` and the
  integrability of `f log (f/g)` in place of the convention `c log (c/0) = ∞`.
* Theorem 10.42: the inequality `theorem_10_42` (here), which is `relEntropyPDF_nonneg`, and the
  equality case `relEntropyPDF_eq_zero_iff` (`DifferentialEntropy.RelativeEntropy`).

### 10.6 Maximum Differential Entropy Distributions
* Theorem 10.43 and Corollary 10.44: `diffEntropy_le_of_eq_exp`, `diffEntropy_eq_of_eq_exp_iff`
  (`MaxEntropy.Basic`).
* Theorem 10.45: `theorem_10_45` (here), from `diffEntropy_le_of_integral_mul_sq` and
  `diffEntropy_eq_of_integral_mul_sq_iff` (`DifferentialEntropy.Gaussian`) with mean `0`.
* Theorem 10.46: `theorem_10_46` (here), from the same.
* Theorem 10.47: `theorem_10_47` (here), from `diffEntropy_le_of_partialCovariance` and
  `diffEntropy_eq_of_partialCovariance_iff` (`MaxEntropy.Covariance`), with all the second moments
  constrained.
* Theorem 10.48: `diffEntropy_le_of_covariance`, `diffEntropy_eq_of_covariance_iff`
  (`DifferentialEntropy.MultivariateGaussian`).

## Not formalized

* The general mutual information of footnote 6, with a Radon–Nikodym derivative.
* The remark that strong typicality does not apply to continuous random variables.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 10
-/

open Real Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-! ### Worked examples -/

/-- **Example 10.11, (10.49)–(10.53).** For `X` uniform on `[0, 1]`, the entropy of `X` quantized
into `2ⁿ` cells tends to `∞`: a continuous random variable contains an infinite amount of
information. -/
theorem example_10_11 :
    Tendsto (fun n : ℕ => entropy (quantPMF (uniformPDF 0 1) 0 (0 + 1) (2 ^ n))) atTop atTop := by
  have hf := uniformPDF_isPDF (show (0 : ℝ) < 1 by norm_num)
  have hcont : ContinuousOn (uniformPDF 0 1) (Set.Icc 0 (0 + 1)) := by
    rw [zero_add]
    exact continuousOn_const.congr fun x hx => Set.indicator_of_mem hx _
  have hzero : ∀ x ∉ Set.Icc (0 : ℝ) (0 + 1), uniformPDF 0 1 x = 0 := fun x hx => by
    rw [zero_add] at hx
    exact Set.indicator_of_notMem hx _
  have h := tendsto_entropy_quantPMF_two_pow_sub hf hcont hzero
  have hlog : Tendsto (fun n : ℕ => (n : ℝ) * log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (log_pos one_lt_two)
  exact (h.add_atTop hlog).congr fun n => by ring

/-- **Example 10.16, (10.79)–(10.80).** For `X ∼ N(m, v)` and `Y = aX ∼ N(am, a² v)`,
`h(Y) = h(X) + log |a|`, as Theorem 10.15 predicts. -/
theorem example_10_16 (m : ℝ) {v w : ℝ≥0} (hv : v ≠ 0) {a : ℝ} (ha : a ≠ 0)
    (hw : (w : ℝ) = a ^ 2 * v) :
    diffEntropy volume (gaussianPDFReal (a * m) w) =
      diffEntropy volume (gaussianPDFReal m v) + log |a| := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hw
    have : (0 : ℝ) < a ^ 2 * v := mul_pos (by positivity) (lt_of_le_of_ne v.property (by
      exact_mod_cast (Ne.symm hv)))
    linarith
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.property (by exact_mod_cast (Ne.symm hv))
  rw [diffEntropy_gaussianPDFReal _ hw0, diffEntropy_gaussianPDFReal _ hv, hw]
  have h₁ : (0 : ℝ) < 2 * π * exp 1 := by positivity
  rw [show 2 * π * exp 1 * (a ^ 2 * v) = a ^ 2 * (2 * π * exp 1 * v) by ring,
    log_mul (by positivity) (by positivity), ← sq_abs, log_pow]
  push_cast
  ring

/-! ### Aliases -/

/-- **Proposition 10.3.** Covariance and correlation matrices are positive semidefinite. -/
theorem proposition_10_3 {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) :
    (covMatrix μ X).PosSemidef ∧ (corrMatrix μ X).PosSemidef :=
  ⟨posSemidef_covMatrix hX, posSemidef_corrMatrix hX⟩

/-- **Proposition 10.4.** -/
alias proposition_10_4 := Matrix.PosSemidef.eigenvalues_nonneg

/-- **Proposition 10.5.** (10.28)–(10.29) -/
theorem proposition_10_5 {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (A : Matrix κ ι ℝ) :
    covMatrix μ (fun k ω => (A.mulVec fun i => X i ω) k) = A * covMatrix μ X * A.transpose ∧
      corrMatrix μ (fun k ω => (A.mulVec fun i => X i ω) k) = A * corrMatrix μ X * A.transpose :=
  ⟨covMatrix_mulVec hX A, corrMatrix_mulVec hX A⟩

/-- **Proposition 10.6.** -/
alias proposition_10_6 := covMatrix_transpose_mulVec

/-- **Corollary 10.7.** (10.40) -/
alias corollary_10_7 := eq_mulVec_transpose_mulVec

/-- **Proposition 10.8.** (10.41) -/
alias proposition_10_8 := covMatrix_add_of_indepFun

/-- **Proposition 10.9.** (10.42) -/
alias proposition_10_9 := integral_sum_sq_mulVec_of_orthogonal

/-- **Theorem 10.14 (Translation).** (10.65) -/
alias theorem_10_14 := diffEntropy_comp_sub

/-- **Theorem 10.15 (Scaling).** (10.71) -/
alias theorem_10_15 := diffEntropy_scale

/-- **Theorem 10.19 (Scaling).** (10.84) -/
alias theorem_10_19 := diffEntropy_linearEquiv

/-- **Theorem 10.20 (Multivariate Gaussian Distribution).** (10.85) -/
alias theorem_10_20 := diffEntropy_mvGaussianPDF

/-- **Proposition 10.26.** If `f(y|x)` is bounded, `Y` has a bounded density
`f(y) = ∫ f(y|x) dF(x)`, (10.100). -/
theorem proposition_10_26 {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] {μ : Measure 𝒳}
    {ν : Measure 𝒴} [IsProbabilityMeasure μ] [SFinite ν] {k : 𝒳 → 𝒴 → ℝ} (hk : IsCondPDF ν k)
    (hb : IsBoundedCondPDF k) :
    (jointLawOfCondPDF μ ν k).map Prod.snd = pdfMeasure ν (outPDF μ k) ∧
      IsPDF ν (outPDF μ k) ∧ IsBoundedPDF (outPDF μ k) :=
  ⟨map_snd_jointLawOfCondPDF hk hb, isPDF_outPDF hk hb, isBoundedPDF_outPDF hk hb⟩

/-- **Proposition 10.31.** (10.137) -/
alias proposition_10_31 := diffEntropy_outPDF_eq_add

/-- **Proposition 10.32 (Chain Rule for Differential Entropy).** (10.139) -/
alias proposition_10_32 := diffEntropy_eq_sum_condDiffEntropyLast

/-- **Theorem 10.33**, the inequality (10.140); the equality case is
`mutualInfoOfCondPDF_eq_zero_iff`. -/
alias theorem_10_33 := mutualInfoOfCondPDF_nonneg

/-- **Corollary 10.34**, the inequality (10.149); the equality case is
`condMutualInfoOfCondPDF_eq_zero_iff`. -/
alias corollary_10_34 := condMutualInfoOfCondPDF_nonneg

/-- **Theorem 10.37 (AEP I for Continuous Random Variables).** (10.152) -/
alias theorem_10_37 := tendstoInMeasure_sampleDiffEntropy

/-- **Theorem 10.42 (Divergence Inequality)**, the inequality (10.174); the equality case is
`relEntropyPDF_eq_zero_iff`. -/
alias theorem_10_42 := relEntropyPDF_nonneg

/-- **Theorem 10.45.** If `EX² = κ`, then `h(X) ≤ ½ log (2πeκ)`, with equality iff `X ∼ N(0, κ)`. -/
theorem theorem_10_45 {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hint : Integrable fun x => negMulLog (g x)) {κ : ℝ≥0} (hκ : κ ≠ 0)
    (h2 : ∫ x, g x * x ^ 2 = κ) :
    diffEntropy volume g ≤ 1 / 2 * log (2 * π * exp 1 * κ) ∧
      (diffEntropy volume g = 1 / 2 * log (2 * π * exp 1 * κ) ↔
        g =ᵐ[volume] gaussianPDFReal 0 κ) := by
  have h2' : ∫ x, g x * (x - 0) ^ 2 = (κ : ℝ) := by simpa using h2
  exact ⟨diffEntropy_le_of_integral_mul_sq hg hint hκ h2',
    diffEntropy_eq_of_integral_mul_sq_iff hg hint hκ h2'⟩

/-- **Theorem 10.46.** If `X` has mean `m` and variance `v`, then `h(X) ≤ ½ log (2πev)`, with
equality iff `X ∼ N(m, v)`. -/
theorem theorem_10_46 {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hint : Integrable fun x => negMulLog (g x)) {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : ∫ x, g x * (x - m) ^ 2 = v) :
    diffEntropy volume g ≤ 1 / 2 * log (2 * π * exp 1 * v) ∧
      (diffEntropy volume g = 1 / 2 * log (2 * π * exp 1 * v) ↔
        g =ᵐ[volume] gaussianPDFReal m v) :=
  ⟨diffEntropy_le_of_integral_mul_sq hg hint hv hvar,
    diffEntropy_eq_of_integral_mul_sq_iff hg hint hv hvar⟩

/-- **Theorem 10.47.** If `X` has correlation matrix `K̃`, then `h(X) ≤ ½ log ((2πe)ⁿ |K̃|)`, with
equality iff `X ∼ N(0, K̃)`. -/
theorem theorem_10_47 {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : K.PosDef)
    {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g) (hent : Integrable fun x => negMulLog (g x))
    (hint : ∀ a b, Integrable fun x => g x * (x a * x b))
    (hcorr : ∀ a b, ∫ x, g x * (x a * x b) = K a b) :
    diffEntropy volume g ≤ 1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) ∧
      (diffEntropy volume g = 1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) ↔
        g =ᵐ[volume] mvGaussianPDF 0 K) :=
  ⟨diffEntropy_le_of_partialCovariance hK (fun _ _ => True) (fun _ _ h => absurd trivial h) hg
      hent hint fun a b _ => hcorr a b,
    diffEntropy_eq_of_partialCovariance_iff hK (fun _ _ => True) (fun _ _ h => absurd trivial h)
      hg hent hint fun a b _ => hcorr a b⟩

/-- **Theorem 10.48**, the inequality (10.201); the equality case is
`diffEntropy_eq_of_covariance_iff`. -/
alias theorem_10_48 := diffEntropy_le_of_covariance

end InfoTheory.Yeung
