/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.Fourier.Convolution

/-!
# Cross-correlation of energy signals

The cross-correlation `R₁₂(τ) = ∫ g₁(t) g₂(t - τ) dt` of two signals is the convolution of `g₁` with
the reflection of `g₂`. For real signals, its Fourier transform is `G₁(f) G₂*(f)`.

## Main definitions

* `crossCorrelation g₁ g₂`: Definition 11.25.

## Main statements

* `fourier_crossCorrelation`: Proposition 11.26, `R₁₂ ⇌ G₁ G₂*`.

## Implementation notes

Signals are complex-valued and integrable; a real signal is one with `conj (g t) = g t`. Mathlib's
Fourier transform `𝓕 g (f) = ∫ e^{-2πi f t} g(t) dt` is the book's (11.193).

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 11.7
-/

open MeasureTheory Complex FourierTransform ComplexConjugate
open scoped Convolution

@[expose] public noncomputable section

namespace InfoTheory

/-- **Definition 11.25, (11.197).** The cross-correlation `R₁₂(τ) = ∫ g₁(t) g₂(t - τ) dt`. -/
def crossCorrelation (g₁ g₂ : ℝ → ℂ) (τ : ℝ) : ℂ := ∫ t, g₁ t * g₂ (t - τ)

/-- The cross-correlation is the convolution of `g₁` with the reflection of `g₂`. -/
lemma crossCorrelation_eq_convolution (g₁ g₂ : ℝ → ℂ) :
    crossCorrelation g₁ g₂ = g₁ ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun s => g₂ (-s)) := by
  funext τ
  rw [crossCorrelation, convolution_def]
  simp [neg_sub]

/-- The Fourier transform of a real signal at `-f` is the conjugate of its value at `f`. -/
lemma fourier_neg_of_real {g : ℝ → ℂ} (hg : ∀ t, conj (g t) = g t) (ξ : ℝ) :
    𝓕 g (-ξ) = conj (𝓕 g ξ) := by
  simp only [Real.fourier_real_eq]
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul, map_mul, hg, mul_neg, neg_neg,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- **Proposition 11.26, (11.198).** For integrable signals `g₁` and `g₂`, with `g₂` real, the
Fourier transform of `R₁₂` is `G₁(f) G₂*(f)`. -/
theorem fourier_crossCorrelation {g₁ g₂ : ℝ → ℂ} (h₁ : Integrable g₁) (h₂ : Integrable g₂)
    (hg₂ : ∀ t, conj (g₂ t) = g₂ t) (ξ : ℝ) :
    𝓕 (crossCorrelation g₁ g₂) ξ = 𝓕 g₁ ξ * conj (𝓕 g₂ ξ) := by
  rw [crossCorrelation_eq_convolution, Real.fourier_mul_convolution_eq h₁ h₂.comp_neg,
    ← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg, fourier_neg_of_real hg₂]

end InfoTheory
