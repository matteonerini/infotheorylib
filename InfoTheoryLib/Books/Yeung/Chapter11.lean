/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.ContinuousChannel
public import InfoTheoryLib.ForMathlib.CrossCorrelation
public import InfoTheoryLib.GaussianChannel.Achievability
public import InfoTheoryLib.GaussianChannel.Bandlimited
public import InfoTheoryLib.GaussianChannel.ColoredNoise
public import InfoTheoryLib.GaussianChannel.Parallel
public import InfoTheoryLib.MaxEntropy.Covariance
public import InfoTheoryLib.Probability.CovarianceMatrix

/-!
# Yeung, Chapter 11: Continuous-Valued Channels

This file indexes the formalization of Chapter 11 of [yeung2008], and contains aliases named after
the numbers of the results, so the index is checked by Lean. It cites the draft of 15 November
2007, which numbers definitions, theorems and examples with one counter per chapter. The
end-of-chapter problems and the historical notes are not included.

## Conventions

* **Logarithms.** Logarithms are natural, so capacities are in nats.
* **Channels.** A continuous channel is a conditional density `f(y|x) = k x y` with respect to a
  reference measure `ν` (Lebesgue measure for real outputs), as in Section 10.3. Inputs may have any
  distribution `μ`.
* **The Gaussian channel.** Sections 11.4–11.6 use the library's Gaussian channel of Cover &
  Thomas, whose information capacity is a supremum over inputs with a density, rather than over all
  input distributions as in Definition 11.7.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 11.1 Discrete-Time Channels
* Definition 11.1: `IsContinuousChannel` (`ChannelCoding.ContinuousChannel`).
* Definition 11.2: `contNoiseLaw` (`ChannelCoding.ContinuousChannel`).
* Definition 11.3: `IsEquivalentContChannel` (`ChannelCoding.ContinuousChannel`). The additive
  channel `Y = X + Z` with a noise density `g` is equivalent to `f(y|x) = g(y - x)`:
  `isEquivalentContChannel_add`.
* Definitions 11.4 and 11.5: a memoryless use without feedback is the product density
  `∏ᵢ f(yᵢ|xᵢ)` of `ContChannelCode.condErrProb` (`ChannelCoding.ContinuousChannel`); the general
  definition with the past `Tᵢ₋` is not formalized for continuous outputs.
* Definition 11.6: `meanCost` (`ChannelCoding.ContinuousChannel`).
* Definition 11.7: `contCapacity`, `AdmissibleInput` (`ChannelCoding.ContinuousChannel`).
* Theorem 11.8: `monotoneOn_contCapacity`, `concaveOn_contCapacity`, `tendsto_contCapacity_left`
  (`ChannelCoding.ContinuousChannel`). The concavity of `I(X; Y)` in the input distribution,
  (11.12), which the book leaves as an exercise, is a hypothesis of the last two, and the mutual
  informations are assumed bounded so that `C(P)` is a supremum of real numbers.

### 11.2 The Channel Coding Theorem
* Definition 11.9: `ContChannelCode` (`ChannelCoding.ContinuousChannel`).
* Definitions 11.10–11.12: `ContChannelCode.condErrProb`, `ContChannelCode.maxErrProb`,
  `ContChannelCode.avgErrProb` (`ChannelCoding.ContinuousChannel`).
* Definition 11.13: `IsAchievableContRate` (`ChannelCoding.ContinuousChannel`).
* Theorem 11.14: only for the Gaussian channel, `gaussianOpCapacity_eq`
  (`GaussianChannel.Achievability`).

### 11.3 Proof of the Channel Coding Theorem
* Lemma 11.18: `prod_pdfMeasure_le_exp_neg` (`ChannelCoding.ContinuousChannel`), the bound
  (11.82)–(11.88) for any set on which `f(y|x) ≥ e^c f(y)`, which the mutually typical set of
  Definition 11.16 is for `n` uses of the channel.

### 11.4 Memoryless Gaussian Channels
* Definition 11.19: `isEquivalentContChannel_gaussian`, the equivalence of the two specifications
  (`ChannelCoding.ContinuousChannel`), and `noiseJointPDF` (`GaussianChannel.Basic`).
* Definition 11.20: `GaussianCode` (`GaussianChannel.Code`).
* Theorem 11.21: `gaussianInfoCapacity_eq` (`GaussianChannel.Capacity`),
  `gaussianOpCapacity_eq` (`GaussianChannel.Achievability`).
* Lemma 11.22: `lemma_11_22` (here), which is `condDiffEntropyOfCondPDF_sub`
  (`ChannelCoding.ContinuousChannel`). The library's bound for the Gaussian channel is
  `mutualInfoPDF_gaussianChannel_le` (`GaussianChannel.Capacity`).

### 11.5 Parallel Gaussian Channels
* (11.142)–(11.179): `parallelInfoCapacity_eq` (`GaussianChannel.Parallel`).
* Proposition 11.23: `waterFill`, `sum_log_le_waterFill`, `exists_waterLevel`
  (`GaussianChannel.WaterFilling`).

### 11.6 Correlated Gaussian Channels
* (11.180)–(11.192): `coloredInfoCapacity_eq`, `coloredInfoCapacity_eq_parallel`
  (`GaussianChannel.ColoredNoise`).

### 11.7 The Bandlimited White Gaussian Channel
* Definition 11.24: Mathlib's `FourierTransform.fourier`, with notation `𝓕`.
* Definition 11.25: `crossCorrelation` (`ForMathlib.CrossCorrelation`).
* Proposition 11.26: `proposition_11_26` (here), which is `fourier_crossCorrelation`
  (`ForMathlib.CrossCorrelation`), for integrable signals rather than signals of finite energy.
* Theorem 11.29: `signalOfSpectrum_eq_of_samples` (`GaussianChannel.Bandlimited`), the uniqueness
  part only, not the interpolation formula.
* (11.258), the capacity `W log (1 + P/(N₀ W))`: `bandlimitedCapacity_eq`,
  `tendsto_bandlimitedCapacity` (`GaussianChannel.Bandlimited`), as a formula.

### 11.9 Zero-Mean Gaussian Noise is the Worst Additive Noise
* Lemma 11.33: `lemma_11_33` (here), which is `corrMatrix_add_of_indepFun`
  (`Probability.CovarianceMatrix`).
* Lemma 11.34: `lemma_11_34` (here), from `crossEntropy_mvGaussianPDF_of_partial`
  (`MaxEntropy.Covariance`) and `diffEntropy_mvGaussianPDF`
  (`DifferentialEntropy.MultivariateGaussian`).

## Not formalized

* Theorem 11.14 for a general continuous memoryless channel, with Lemma 11.15, the mutually typical
  set of Definition 11.16, Lemma 11.17, and the `n`-letter form of Lemma 11.18. Only the Gaussian
  channel is formalized.
* The concavity (11.12) of `I(X; Y)` in a general input distribution (Problem 2).
* Proposition 11.30, the orthonormal basis of sinc functions, and the interpolation formula of
  Theorem 11.29.
* Definitions 11.27 and 11.28, Proposition 11.31 and Section 11.8, on continuous-time random
  processes.
* Theorem 11.32 and (11.306), that zero-mean Gaussian noise is the worst additive noise. The proof
  needs the density of a sum of independent Gaussian vectors, which the library does not have.
* Figures 11.1 to 11.5.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 11
-/

open Real Filter Topology MeasureTheory ProbabilityTheory FourierTransform ComplexConjugate
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-! ### Aliases -/


/-- **Lemma 11.22.** (11.119)–(11.124) -/
alias lemma_11_22 := condDiffEntropyOfCondPDF_sub

/-- **Proposition 11.26.** (11.198) -/
alias proposition_11_26 := fourier_crossCorrelation

/-- **Lemma 11.33.** (11.271) -/
alias lemma_11_33 := corrMatrix_add_of_indepFun

/-- **Lemma 11.34.** If `Y` has the correlation matrix `K` of `Y* ∼ N(0, K)`, then
`∫ f_{Y*} log f_{Y*} = ∫ f_Y log f_{Y*}`, (11.278). -/
theorem lemma_11_34 {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℝ} (hK : K.PosDef)
    {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g) (hint : ∀ a b, Integrable fun x => g x * (x a * x b))
    (hcorr : ∀ a b, ∫ x, g x * (x a * x b) = K a b) :
    ∫ x, mvGaussianPDF 0 K x * log (mvGaussianPDF 0 K x) =
      ∫ x, g x * log (mvGaussianPDF 0 K x) := by
  obtain ⟨-, h₁⟩ := crossEntropy_mvGaussianPDF_of_partial hK (fun _ _ => True)
    (fun _ _ h => absurd trivial h) hg hint fun a b _ => hcorr a b
  have h₂ := diffEntropy_mvGaussianPDF hK 0
  have h₃ : diffEntropy volume (mvGaussianPDF 0 K) =
      -∫ x, mvGaussianPDF 0 K x * log (mvGaussianPDF 0 K x) := by
    rw [diffEntropy, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [negMulLog])
  linarith

end InfoTheory.Yeung
