/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter11
public import InfoTheoryLib.MaxEntropy.Basic
public import InfoTheoryLib.MaxEntropy.Distributions
public import InfoTheoryLib.MaxEntropy.Covariance
public import InfoTheoryLib.MaxEntropy.Burg

/-!
# Cover & Thomas, Chapter 12: Maximum Entropy

This file indexes the formalization of Chapter 12 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_12_1_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Support sets.** A density on the support set `S` is a density with respect to the reference
  measure `μ = volume.restrict S`; for pmfs, `S` is the finite type `α`. The constraints
  `∫_S f rᵢ = αᵢ` are integrals with respect to `μ`, and `∫ g rᵢ`, `∫ g log g` are assumed
  integrable.
* **Logarithms.** Logarithms are natural, so entropies are in nats.
* **Second moments.** The constraints of Examples 12.2.8–12.2.9 and Theorem 12.6.1 are on
  `E Xᵢ Xⱼ`, as in the book, so the densities need not have mean zero.
* **Autoregressive processes.** The book's `a₁, …, a_p` are `a 0, …, a (p - 1)`. A segment of
  length `n = p + m` is indexed by `Fin (p + m)`, the first `p` samples carrying the stationary
  initial covariance `K_{p-1} = toeplitzCov R p`, and lags are `Nat.dist i j = |i - j|`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 12.1 Maximum entropy distributions
* Theorem 12.1.1, (12.5)–(12.12): `diffEntropy_le_of_eq_exp`, uniqueness
  `diffEntropy_eq_of_eq_exp_iff`, with (12.9) `integral_mul_log_eq_exp` (`MaxEntropy.Basic`).
* Theorem 12.1.1 for discrete entropy: `entropy_le_of_eq_exp`, `entropy_eq_of_eq_exp_iff`.

### 12.2 Examples
* Example 12.2.1, (12.13)–(12.14): `example_12_2_1` (here), through Theorem 12.1.1.
* Example 12.2.2: `example_12_2_2` (here), from `entropy_le_log_card`, `entropy_eq_log_card_iff`
  (`Entropy.Bounds`).
* Example 12.2.3, (12.19): `gibbsPMF`, `entropy_le_gibbsPMF`, `entropy_eq_gibbsPMF_iff`
  (`MaxEntropy.Distributions`); dice: `example_12_2_3` (here). The counting argument
  (12.16)–(12.18) is Theorem 11.1.3 (`card_typeClass_le`, `exp_div_le_card_typeClass`).
* Example 12.2.4: `diffEntropy_le_log_of_Icc`, `diffEntropy_eq_log_of_Icc_iff`.
* Example 12.2.5, (12.21): `expDensity`, `diffEntropy_le_of_mean`, `diffEntropy_eq_of_mean_iff`,
  `diffEntropy_expDensity`.
* Example 12.2.6: `example_12_2_6` (here).
* Example 12.2.7: `diffEntropy_le_of_moments`.
* Example 12.2.8, (12.22)–(12.24): `diffEntropy_le_of_covariance`,
  `diffEntropy_eq_of_covariance_iff`, `diffEntropy_mvGaussianPDF`
  (`DifferentialEntropy.MultivariateGaussian`).
* Example 12.2.9: `diffEntropy_le_of_partialCovariance`, `diffEntropy_eq_of_partialCovariance_iff`
  (`MaxEntropy.Covariance`).

### 12.3 Anomalous maximum entropy problem
* The upper bound in (12.32): `diffEntropy_le_of_moments`, which ignores the third moment.

### 12.4 Spectrum estimation
* (12.35): `sampleAutocorr` (`MaxEntropy.Burg`).

### 12.5 Entropy rates of a Gaussian process
* (12.39): `diffEntropy_mvGaussianPDF` with the Toeplitz covariance `toeplitzCov R n`.

### 12.6 Burg's maximum entropy theorem
* (12.43): the whitening filter `arFilter` and the covariance `arCov` of the AR(p) process, the
  Toeplitz matrix of the Yule–Walker extension `ywExt` (`MaxEntropy.Burg`).
* (12.52)–(12.53), the Yule–Walker equations: `ywExt_zero_add_sum`, `ywExt_add_sum_eq_zero`; in
  matrix form `arFilter_mul_arCov_mul_transpose`.
* `arCov_posDef`, `det_arCov`, and the banded inverse `inv_arCov_eq_zero`.
* Theorem 12.6.1, (12.44)–(12.49): `diffEntropy_le_burg`, `diffEntropy_eq_burg_iff`, attained by
  `diffEntropy_arCov`, `integral_mvGaussianPDF_arCov_mul`.
* (12.50)–(12.51), the entropy rate `½ log 2πeσ²`: `tendsto_diffEntropy_arCov`.
* (12.55): `arSpectrum`.
* (12.56)–(12.58): `det_toeplitzCov_succ`, `σ² = |K_p| / |K_{p-1}|`.

## Not formalized

* Approach 1 (the calculus of variations, (12.2)–(12.4)), which only suggests the form of the
  maximizer.
* Stirling's approximation (12.16)–(12.18), replaced by the bounds of Theorem 11.1.3, and the
  concentration (12.20) of the dice frequencies, a conditional limit theorem along the hyperplane
  `∑ i nᵢ = nα` (Theorem 11.6.2 treats conditioning on a closed convex set of types).
* The ε-achievability in (12.32): we prove the upper bound, not that the supremum is attained in
  the limit.
* The power spectral density (12.34) and the periodogram discussion; the existence of the entropy
  rate of a stationary process (12.37)–(12.38) and Kolmogorov's formula (12.40)–(12.41).
* The existence of a solution of the Yule–Walker equations (Levinson–Durbin), assumed in
  Theorem 12.6.1, and the identity (12.54) = (12.55) between the Fourier series of the extended
  autocorrelation and the AR spectrum.
* Theorem 12.6.1 for infinite processes: we prove the bound for every finite segment, which gives
  the bound on the entropy rate whenever that rate exists, and the rate (12.51) of the AR(p)
  process. The chain-rule proof (12.44)–(12.49) is replaced by Example 12.2.9.
-/

open Real MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 12.2: examples -/

/-- **Example 12.2.1 (One-dimensional gas with a temperature constraint), (12.13)–(12.14).** The
normal density `N(0, σ²)` has the form `e^{λ₀ + λ₁ x + λ₂ x²}` (with `λ₁ = 0`,
`λ₂ = -1/(2σ²)`), so by Theorem 12.1.1 it maximizes the entropy among the densities with
`E X = 0` and `E X² = σ²`. -/
theorem example_12_2_1 {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ} (hg : IsPDF volume g)
    (hent : Integrable fun x => negMulLog (g x)) (h1 : Integrable fun x => g x * x)
    (h2 : Integrable fun x => g x * x ^ 2) (hm1 : ∫ x, g x * x = 0)
    (hm2 : ∫ x, g x * x ^ 2 = v) :
    diffEntropy volume g ≤ diffEntropy volume (gaussianPDFReal 0 v) := by
  have hform : ∀ x, gaussianPDFReal 0 v x = exp (-(log (2 * π * v) / 2) +
      ∑ i, ![0, -1 / (2 * (v : ℝ))] i * ![fun x : ℝ => x, fun x => x ^ 2] i x) := fun x => by
    rw [← exp_log (gaussianPDFReal_pos 0 v x hv), log_gaussianPDFReal 0 hv, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    ring_nf
  refine diffEntropy_le_of_eq_exp _ _ _ (gaussianPDFReal_isPDF 0 hv) hform (fun i => ?_) hg
    (fun i => ?_) (fun i => ?_) hent
  · fin_cases i
    · exact integrable_gaussianPDFReal_mul_self hv
    · exact integrable_gaussianPDFReal_mul_sq_zero hv
  · fin_cases i
    · exact h1
    · exact h2
  · fin_cases i
    · simpa [hm1] using (integral_gaussianPDFReal_mul_self hv).symm
    · simpa [hm2] using (integral_gaussianPDFReal_mul_sq_zero hv).symm

/-- **Example 12.2.2 (Dice, no constraints).** On `S = {1, …, 6}` the uniform distribution
maximizes the entropy, and only it: `H(p) ≤ log 6`, with equality iff `p` is uniform. -/
theorem example_12_2_2 {p : Fin 6 → ℝ} (hp : IsPMF p) :
    entropy p ≤ log 6 ∧ (entropy p = log 6 ↔ p = uniformPMF (Fin 6)) := by
  have h := entropy_le_log_card hp
  have h' := entropy_eq_log_card_iff hp
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h h'
  exact ⟨h, h'⟩

/-- **Example 12.2.3 (Dice, with `E X = ∑ i pᵢ = α`), (12.19).** Among the distributions of a die
with the mean of the Boltzmann distribution `p*ᵢ = e^{λi} / ∑ⱼ e^{λj}`, the latter has the largest
entropy. -/
theorem example_12_2_3 (lam : ℝ) {p : Fin 6 → ℝ} (hp : IsPMF p)
    (hmean : ∑ i, p i * (i + 1 : ℕ) = ∑ i, gibbsPMF (fun i : Fin 6 => ((i + 1 : ℕ) : ℝ)) lam i *
      (i + 1 : ℕ)) :
    entropy p ≤ entropy (gibbsPMF (fun i : Fin 6 => ((i + 1 : ℕ) : ℝ)) lam) :=
  entropy_le_gibbsPMF _ lam hp hmean

/-- The normal density `N(μ, v)` has mean `μ`. -/
lemma integral_gaussianPDFReal_mul_id (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal μ v x * x = μ := by
  have h := integral_id_gaussianReal (μ := μ) (v := v)
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simpa [smul_eq_mul] using h

/-- **Example 12.2.6.** On `S = ℝ` with the constraint `E X = μ` alone, the entropy is unbounded,
so there is no maximum entropy distribution: the normal densities `N(μ, v)` have mean `μ` and
entropy `½ log 2πev → ∞`. -/
theorem example_12_2_6 (μ M : ℝ) :
    ∃ v : ℝ≥0, v ≠ 0 ∧ ∫ x, gaussianPDFReal μ v x * x = μ ∧
      M < diffEntropy volume (gaussianPDFReal μ v) := by
  set v : ℝ≥0 := ⟨exp (2 * M), (exp_pos _).le⟩
  have hv : v ≠ 0 := fun h => (exp_pos (2 * M)).ne' (congrArg NNReal.toReal h)
  refine ⟨v, hv, integral_gaussianPDFReal_mul_id μ hv, ?_⟩
  rw [diffEntropy_gaussianPDFReal μ hv]
  have h2πe : 1 < 2 * π * exp 1 := by
    have := pi_gt_three
    have := add_one_le_exp (1 : ℝ)
    nlinarith
  have hv' : (v : ℝ) = exp (2 * M) := rfl
  rw [hv', log_mul (by positivity) (exp_pos _).ne', log_exp]
  have := log_pos h2πe
  linarith

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems of Chapter 12.
-/

/-- **Theorem 12.1.1 (Maximum entropy distribution).** -/
alias theorem_12_1_1 := diffEntropy_le_of_eq_exp

/-- **Theorem 12.1.1 (uniqueness).** -/
alias theorem_12_1_1_unique := diffEntropy_eq_of_eq_exp_iff

/-- **Theorem 12.1.1 for pmfs.** -/
alias theorem_12_1_1_discrete := entropy_le_of_eq_exp

/-- **Theorem 12.6.1 (Burg's maximum entropy theorem).** -/
alias theorem_12_6_1 := diffEntropy_le_burg

/-- **Theorem 12.6.1 (uniqueness).** -/
alias theorem_12_6_1_unique := diffEntropy_eq_burg_iff

/-- **Theorem 12.6.1, (12.50)–(12.51): the maximum entropy rate `½ log 2πeσ²`.** -/
alias theorem_12_6_1_rate := tendsto_diffEntropy_arCov

end InfoTheory.CoverThomas
