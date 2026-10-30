/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import InfoTheoryLib.GaussianChannel.Achievability

/-!
# Bandlimited channels

A signal bandlimited to `W` hertz is determined by its samples taken `1/(2W)` seconds apart
(the Nyquist–Shannon sampling theorem). Over a time `T`, a bandlimited channel with white
Gaussian noise of power spectral density `N₀/2` is thus `2WT` uses of a Gaussian channel with
noise variance `N₀/2` and power `P/(2W)` per sample, and its capacity is
`C = W log (1 + P/(N₀W))` per second. As `W → ∞`, `C → P/N₀`.

## Main definitions

* `signalOfSpectrum G`: the signal `f(t) = ∫ G(ξ) e^{2πiξt} dξ` with spectrum `G`, (9.55).
* `IsBandlimited W G`: the spectrum vanishes outside `[-W, W]`.
* `bandlimitedCapacity W P N₀`: `W log (1 + P/(N₀W))`, (9.62).

## Main statements

* `signalOfSpectrum_eq_of_samples`: Theorem 9.3.1, a bandlimited signal is determined by its
  samples `f(k/(2W))`.
* `sinc_two_pi_mul`: (9.58), `sinc(2πWt)` is `1` at `t = 0` and `0` at `t = n/(2W)`, `n ≠ 0`.
* `bandlimitedCapacity_eq`: (9.60)–(9.62).
* `tendsto_bandlimitedCapacity`: (9.63), `W log (1 + P/(N₀W)) → P/N₀` as `W → ∞`.

## Implementation notes

Frequencies `ξ` are in hertz; the book writes `ω = 2πξ`, so its `F(ω)` is our `G(ω/2π)` up to the
factor `1/(2π)` of (9.55). Theorem 9.3.1 is proved, as in the book, by noting that the samples
`f(k/(2W))` are the Fourier coefficients of the spectrum on `[-W, W]`; Parseval's identity shows
that the spectrum, assumed square-integrable, is determined by them. Capacities are in nats.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.3
-/

open Real MeasureTheory Filter Topology Set
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The sampling theorem -/

/-- **(9.55)** The signal `f(t) = ∫ G(ξ) e^{2πiξt} dξ` with spectrum `G`. -/
def signalOfSpectrum (G : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ξ : ℝ, Complex.exp (2 * π * Complex.I * ξ * t) * G ξ

/-- The spectrum `G` is bandlimited to `W`: `G(ξ) = 0` for `|ξ| > W`. -/
def IsBandlimited (W : ℝ) (G : ℝ → ℂ) : Prop := ∀ ξ, ξ ∉ Icc (-W) W → G ξ = 0

lemma norm_exp_two_pi_I_mul (ξ t : ℝ) : ‖Complex.exp (2 * π * Complex.I * ξ * t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma integrable_exp_mul {G : ℝ → ℂ} (hG : Integrable G) (t : ℝ) :
    Integrable fun ξ : ℝ => Complex.exp (2 * π * Complex.I * ξ * t) * G ξ := by
  refine hG.norm.mono' (by fun_prop) (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_exp_two_pi_I_mul, one_mul]

lemma signalOfSpectrum_sub {G₁ G₂ : ℝ → ℂ} (h₁ : Integrable G₁) (h₂ : Integrable G₂) (t : ℝ) :
    signalOfSpectrum (G₁ - G₂) t = signalOfSpectrum G₁ t - signalOfSpectrum G₂ t := by
  rw [signalOfSpectrum, signalOfSpectrum, signalOfSpectrum, ← integral_sub
    (integrable_exp_mul h₁ t) (integrable_exp_mul h₂ t)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.sub_apply, mul_sub]

/-- A bandlimited spectrum whose signal vanishes at all the sampling times `k/(2W)` vanishes
almost everywhere: its Fourier coefficients on `[-W, W]` are the samples. -/
theorem ae_eq_zero_of_samples {W : ℝ} (hW : 0 < W) {H : ℝ → ℂ} (hH : IsBandlimited W H)
    (hL2 : MemLp H 2) (hs : ∀ k : ℤ, signalOfSpectrum H (k / (2 * W)) = 0) : H =ᵐ[volume] 0 := by
  have hab : -W < W := by linarith
  have hT : W - -W = 2 * W := by ring
  -- The Fourier coefficients of `H` on `[-W, W]` are the samples.
  have hcoeff : ∀ n : ℤ, fourierCoeffOn hab H n = 0 := by
    intro n
    rw [fourierCoeffOn_eq_integral H n hab]
    have h1 : ∫ x in -W..W, fourier (-n) (x : AddCircle (W - -W)) • H x =
        signalOfSpectrum H ((-n : ℤ) / (2 * W)) := by
      calc ∫ x in -W..W, fourier (-n) (x : AddCircle (W - -W)) • H x
          = ∫ x in Icc (-W) W, fourier (-n) (x : AddCircle (W - -W)) • H x := by
            rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]
        _ = ∫ x in Icc (-W) W,
              Complex.exp (2 * π * Complex.I * x * ((-n : ℤ) / (2 * W) : ℝ)) * H x := by
            refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
            rw [fourier_coe_apply, smul_eq_mul, hT]
            congr 2
            push_cast
            field_simp
        _ = signalOfSpectrum H ((-n : ℤ) / (2 * W)) :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
              rw [hH x hx, mul_zero]
    rw [h1, hs (-n), smul_zero]
  -- Parseval: `∫_{-W}^{W} ‖H‖² = 2W ∑ₙ ‖cₙ‖² = 0`.
  have hL2' : MemLp H 2 (volume.restrict (Ioc (-W) W)) := hL2.restrict _
  have hsum := tsum_sq_fourierCoeffOn hab hL2'
  simp only [hcoeff, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    tsum_zero] at hsum
  have hint0 : ∫ x in Ioc (-W) W, ‖H x‖ ^ 2 = 0 := by
    rw [← intervalIntegral.integral_of_le hab.le]
    have hne : (W - -W)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
    exact (smul_eq_zero.1 hsum.symm).resolve_left hne
  have hint : Integrable (fun x => ‖H x‖ ^ 2) (volume.restrict (Ioc (-W) W)) := by
    have h := hL2'.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using h
  have hae : ∀ᵐ x ∂volume.restrict (Ioc (-W) W), ‖H x‖ ^ 2 = 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
      hint).1 hint0
  -- Hence `H = 0` almost everywhere on `ℝ`.
  rw [Filter.EventuallyEq, ae_iff]
  have hsub : {x | ¬ H x = (0 : ℝ → ℂ) x} ⊆
      ({x | ¬ ‖H x‖ ^ 2 = 0} ∩ Ioc (-W) W) ∪ {-W} := by
    intro x hx
    have hx0 : H x ≠ 0 := hx
    by_cases hxI : x ∈ Icc (-W) W
    · by_cases hxW : x = -W
      · exact Or.inr hxW
      · exact Or.inl ⟨by simpa using hx0, lt_of_le_of_ne hxI.1 (Ne.symm hxW), hxI.2⟩
    · exact absurd (hH x hxI) hx0
  refine measure_mono_null hsub (measure_union_null ?_ (measure_singleton _))
  rw [ae_iff, Measure.restrict_apply' measurableSet_Ioc] at hae
  exact hae

/-- **Theorem 9.3.1 (Nyquist–Shannon sampling theorem).** A signal bandlimited to `W` is
completely determined by its samples spaced `1/(2W)` seconds apart: if two square-integrable
spectra vanishing outside `[-W, W]` give signals with the same samples `f(k/(2W))`, `k ∈ ℤ`, then
the signals are equal. -/
theorem signalOfSpectrum_eq_of_samples {W : ℝ} (hW : 0 < W) {G₁ G₂ : ℝ → ℂ}
    (h₁ : IsBandlimited W G₁) (h₂ : IsBandlimited W G₂) (hi₁ : Integrable G₁)
    (hi₂ : Integrable G₂) (hL₁ : MemLp G₁ 2) (hL₂ : MemLp G₂ 2)
    (hs : ∀ k : ℤ, signalOfSpectrum G₁ (k / (2 * W)) = signalOfSpectrum G₂ (k / (2 * W))) :
    signalOfSpectrum G₁ = signalOfSpectrum G₂ := by
  have hH : IsBandlimited W (G₁ - G₂) := fun ξ hξ => by simp [h₁ ξ hξ, h₂ ξ hξ]
  have h0 := ae_eq_zero_of_samples hW hH (hL₁.sub hL₂) fun k => by
    rw [signalOfSpectrum_sub hi₁ hi₂, hs k, sub_self]
  funext t
  rw [← sub_eq_zero, ← signalOfSpectrum_sub hi₁ hi₂, signalOfSpectrum,
    integral_congr_ae (h0.mono fun ξ (hξ : (G₁ - G₂) ξ = 0) => by
      change Complex.exp (2 * π * Complex.I * ξ * t) * (G₁ - G₂) ξ = 0
      rw [hξ, mul_zero])]
  simp

/-- **(9.58)** The function `sinc(2πWt) = sin(2πWt)/(2πWt)` is `1` at `t = 0` and `0` at the other
sampling times `t = n/(2W)`. -/
theorem sinc_two_pi_mul {W : ℝ} (hW : 0 < W) (n : ℤ) :
    sinc (2 * π * W * (n / (2 * W))) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · simp [hn]
  · have e : 2 * π * W * (n / (2 * W)) = n * π := by field_simp
    have hne : (n : ℝ) * π ≠ 0 := mul_ne_zero (by exact_mod_cast hn) pi_ne_zero
    rw [e, sinc_of_ne_zero hne, sin_int_mul_pi, zero_div]

/-! ### The capacity of a bandlimited channel -/

/-- **(9.62)** The capacity `C = W log (1 + P/(N₀W))`, in nats per second, of the channel with
bandwidth `W`, white Gaussian noise of power spectral density `N₀/2` and power `P`. -/
def bandlimitedCapacity (W P N₀ : ℝ) : ℝ := W * log (1 + P / (N₀ * W))

/-- **(9.60)–(9.62)** The bandlimited channel is used `2W` times per second as a Gaussian channel
with power `P/(2W)` and noise variance `N₀/2` per sample, whose capacity is
`½ log (1 + P/(N₀W))` per sample (9.61), by Theorem 9.1.1. -/
theorem bandlimitedCapacity_eq {W P N₀ : ℝ} (hW : 0 < W) (hP : 0 ≤ P) (hN₀ : 0 < N₀) :
    2 * W * gaussianOpCapacity (P / (2 * W)).toNNReal (N₀ / 2).toNNReal =
      bandlimitedCapacity W P N₀ := by
  have hN : (N₀ / 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    positivity
  rw [gaussianOpCapacity_eq _ hN, bandlimitedCapacity, Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by positivity), show P / (2 * W) / (N₀ / 2) = P / (N₀ * W) by field_simp]
  ring

/-- **(9.63)** As the bandwidth grows, `W log (1 + P/(N₀W)) → P/N₀` nats per second, i.e.
`(P/N₀) log₂ e` bits per second: the capacity grows linearly with the power. -/
theorem tendsto_bandlimitedCapacity (P N₀ : ℝ) :
    Tendsto (fun W => bandlimitedCapacity W P N₀) atTop (𝓝 (P / N₀)) := by
  refine (tendsto_mul_log_one_add_div_atTop (P / N₀)).congr fun W => ?_
  rw [bandlimitedCapacity, div_div]

end InfoTheory
