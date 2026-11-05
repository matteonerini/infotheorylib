/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.QuadraticGaussian

/-!
# Quadratic Gaussian multiple descriptions: the formulas

This file proves the algebra behind Ozarow's theorem, Theorem 2 of Lecture 14 of El Gamal and Kim:
the test channels, the increase `Δ` of the sum rate, and its derivation from the bound of the
converse. The coding theorem needs the conditional entropy power inequality, which the library does
not have.

The formula of the notes for `Δ` only holds if `1/D₀ + 1/P ≥ 1/D₁ + 1/D₂`. Otherwise the noise
variance `N` of the converse is negative, and the printed sum rate is larger than what the scheme of
the notes achieves with independent noises.

## Main definitions

* `mdNoise P D`: the noise variance `N = P D / (P - D)`.
* `ozarowRatio`, `ozarowDelta`: the increase `Δ(P, D₀, D₁, D₂)` of the sum rate, in nats.
* `ozarowRegion`: the region of Theorem 2 of the notes.
* `ozarowN`: the optimal noise variance of the converse.

## Main statements

* `mdNoise_var`, `mdNoise_mse`, `mdNoise_info`: the test channel `X̂ = (1 - D/P) (X + Z)`.
* `exists_rho_of_high_distortion`: high distortion, page 14-17.
* `ozarow_corr_sq`: `I(X̂₁; X̂₂) = Δ` for `ρ = -1`, page 14-18.
* `ozarow_sq_identity`, `ozarow_ratio_le`, `ozarow_ratio_ozarowN`: the maximization over `N` in the
  converse, page 14-20.
* `ozarowN_pos_iff`: `N > 0` if and only if `1/D₁ + 1/D₂ < 1/D₀ + 1/P`.
* `ozarow_counterexample`: the printed sum rate is too large at
  `(P, D₀, D₁, D₂) = (1, 0.3, 0.31, 0.31)`.
* `mdNoise_indep_inv`: the distortion of independent noises, which gives the correct region there.
* `qgR_refinement`: successive refinability of the Gaussian source, page 14-25.

## Implementation notes

All the rates are in nats, as in `InfoTheoryLib.Network.QuadraticGaussian`: `R(x) = (1/2) log x` is
`qgR x`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 14
-/

open Real

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The test channels -/

section Noise

variable {P D D₀ D₁ D₂ : ℝ}

/-- **Lecture 14, page 14-16.** The noise variance `N = P D / (P - D)`. -/
def mdNoise (P D : ℝ) : ℝ := P * D / (P - D)

/-- `Var(X̂) = (1 - D/P)² (P + N) = P - D`, for `X̂ = (1 - D/P) (X + Z)`. -/
lemma mdNoise_var (hP : 0 < P) (hD : D < P) : (1 - D / P) ^ 2 * (P + mdNoise P D) = P - D := by
  have h : P - D ≠ 0 := by linarith
  simp only [mdNoise]
  field_simp
  ring

/-- `E (X - X̂)² = P - 2 Cov(X, X̂) + Var(X̂) = D`, with `Cov(X, X̂) = (1 - D/P) P`. -/
lemma mdNoise_mse (hP : 0 < P) (hD : D < P) :
    P - 2 * ((1 - D / P) * P) + (1 - D / P) ^ 2 * (P + mdNoise P D) = D := by
  rw [mdNoise_var hP hD]
  field_simp
  ring

/-- `I(X; X̂) = R(P / D)`: `1 / (1 - Cov(X, X̂)² / (P Var(X̂))) = P / D`. -/
lemma mdNoise_info (hP : 0 < P) (hD : D < P) :
    1 / (1 - ((1 - D / P) * P) ^ 2 / (P * ((1 - D / P) ^ 2 * (P + mdNoise P D)))) = P / D := by
  rw [mdNoise_var hP hD]
  have h : P - D ≠ 0 := by linarith
  have e1 : (1 - D / P) * P = P - D := by
    field_simp
  have e2 : (P - D) ^ 2 / (P * (P - D)) = (P - D) / P := by
    field_simp
  have e3 : 1 - (P - D) / P = D / P := by
    field_simp
    ring
  rw [e1, e2, e3, one_div_div]

/-- `N - N₀ = P² (D - D₀) / ((P - D) (P - D₀))`. -/
lemma mdNoise_sub (hD : D < P) (hD₀ : D₀ < P) :
    mdNoise P D - mdNoise P D₀ = P ^ 2 * (D - D₀) / ((P - D) * (P - D₀)) := by
  have h : P - D ≠ 0 := by linarith
  have h' : P - D₀ ≠ 0 := by linarith
  simp only [mdNoise]
  field_simp
  ring

/-- `P + N₀ = P² / (P - D₀)`. -/
lemma add_mdNoise (hD₀ : D₀ < P) : P + mdNoise P D₀ = P ^ 2 / (P - D₀) := by
  have h' : P - D₀ ≠ 0 := by linarith
  simp only [mdNoise]
  field_simp
  ring

/-- **Lecture 14, page 14-17.** Under high distortion, `(N₁ - N₀) (N₂ - N₀) ≥ (P + N₀)²`. -/
lemma mdNoise_high_distortion (hP : 0 < P) (h₁ : D₀ ≤ D₁) (hD₁ : D₁ < P)
    (hD₂ : D₂ < P) (h : P + D₀ ≤ D₁ + D₂) :
    (P + mdNoise P D₀) ^ 2 ≤ (mdNoise P D₁ - mdNoise P D₀) * (mdNoise P D₂ - mdNoise P D₀) := by
  have hδ : 0 < P - D₀ := by linarith
  have hb₁ : 0 < P - D₁ := by linarith
  have hb₂ : 0 < P - D₂ := by linarith
  rw [add_mdNoise (by linarith), mdNoise_sub hD₁ (by linarith), mdNoise_sub hD₂ (by linarith)]
  have e : (P ^ 2 * (D₁ - D₀) / ((P - D₁) * (P - D₀))) * (P ^ 2 * (D₂ - D₀) / ((P - D₂) * (P - D₀)))
    =
      (P ^ 2 / (P - D₀)) ^ 2 * ((D₁ - D₀) * (D₂ - D₀) / ((P - D₁) * (P - D₂))) := by
    field_simp
  rw [e]
  refine le_mul_of_one_le_right (by positivity) ?_
  rw [one_le_div (by positivity)]
  nlinarith

/-- **Lecture 14, page 14-17.** Under high distortion there is `ρ ∈ [-1, 1]` with
`N₀ + ρ √((N₁ - N₀) (N₂ - N₀)) = -P`: then `X̂₁` and `X̂₂` are independent. -/
theorem exists_rho_of_high_distortion (hP : 0 < P) (h₁ : D₀ ≤ D₁) (hD₁ : D₁ < P)
    (hD₂ : D₂ < P) (h : P + D₀ ≤ D₁ + D₂) :
    ∃ ρ : ℝ, |ρ| ≤ 1 ∧
      mdNoise P D₀ + ρ * √((mdNoise P D₁ - mdNoise P D₀) * (mdNoise P D₂ - mdNoise P D₀)) = -P := by
  have hle := mdNoise_high_distortion hP h₁ hD₁ hD₂ h
  have hδ : 0 < P - D₀ := by linarith
  have hpos : 0 < P + mdNoise P D₀ := by
    rw [add_mdNoise (by linarith)]
    positivity
  have hs : P + mdNoise P D₀ ≤ √((mdNoise P D₁ - mdNoise P D₀) * (mdNoise P D₂ - mdNoise P D₀)) :=
    Real.le_sqrt_of_sq_le hle
  have hspos := hpos.trans_le hs
  refine ⟨-(P + mdNoise P D₀) / √((mdNoise P D₁ - mdNoise P D₀) * (mdNoise P D₂ - mdNoise P D₀)),
    ?_, ?_⟩
  · rw [abs_div, abs_neg, abs_of_pos hpos, abs_of_pos hspos]
    exact (div_le_one hspos).2 hs
  · field_simp
    ring

/-- **Lecture 14, page 14-25.** Successive refinability of the Gaussian source:
`R(P/D₁) + R(D₁/D₀) = R(P/D₀)`. -/
theorem qgR_refinement (hP : 0 < P) (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) :
    qgR (P / D₁) + qgR (D₁ / D₀) = qgR (P / D₀) := by
  simp only [qgR]
  rw [log_div hP.ne' hD₁.ne', log_div hD₁.ne' hD₀.ne', log_div hP.ne' hD₀.ne']
  ring

/-- **Lecture 14, page 14-25.** The backward test channels of the successive refinement of the
Gaussian source have the right variances: `Var(X̂₀) = Var(X̂₁) + Var(Z₁)`, and
`P = Var(X̂₀) + Var(Z₀)`. -/
theorem gaussian_refinement_vars : (P - D₁) + (D₁ - D₀) = P - D₀ ∧ (P - D₀) + D₀ = P :=
  ⟨by ring, by ring⟩

end Noise

/-! ### Ozarow's theorem -/

section Ozarow

variable {P D₀ D₁ D₂ : ℝ}

/-- `a = √((D₁ - D₀) (D₂ - D₀))`. -/
abbrev ozarowA (D₀ D₁ D₂ : ℝ) : ℝ := √((D₁ - D₀) * (D₂ - D₀))

/-- `b = √((P - D₁) (P - D₂))`. -/
abbrev ozarowB (P D₁ D₂ : ℝ) : ℝ := √((P - D₁) * (P - D₂))

/-- The argument of `R` in `Δ` on page 14-15. -/
def ozarowRatio (P D₀ D₁ D₂ : ℝ) : ℝ :=
  (P - D₀) ^ 2 / ((P - D₀) ^ 2 - (ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂) ^ 2)

open Classical in
/-- **Theorem 2 of Lecture 14 of [elgamal2010], page 14-15.** The increase `Δ(P, D₀, D₁, D₂)` of the
sum rate, as printed, in nats. -/
def ozarowDelta (P D₀ D₁ D₂ : ℝ) : ℝ :=
  if D₁ + D₂ < P + D₀ then qgR (ozarowRatio P D₀ D₁ D₂) else 0

/-- **Theorem 2 of Lecture 14 of [elgamal2010], page 14-15.** The region as printed, in nats. -/
def ozarowRegion (P D₀ D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | qgR (P / D₁) ≤ R.1 ∧ qgR (P / D₂) ≤ R.2 ∧
    qgR (P / D₀) + ozarowDelta P D₀ D₁ D₂ ≤ R.1 + R.2}

/-- **Lecture 14, page 14-20.** The optimal noise variance of the converse. -/
def ozarowN (P D₀ D₁ D₂ : ℝ) : ℝ :=
  (D₁ * D₂ - D₀ * P + √((D₁ - D₀) * (D₂ - D₀) * (P - D₁) * (P - D₂))) / (P + D₀ - D₁ - D₂)

/-- The square
  `δ² (D₁ + N) (D₂ + N) - (δ² - (b - a)²) (P + N) (D₀ + N) = ((b - a) (D₀ + N) - a δ)²`,
with `δ = P - D₀`, for `a² = (D₁ - D₀) (D₂ - D₀)` and `b² = (P - D₁) (P - D₂)`: this is why the
bound of the converse has a maximum, at the double root of the right side. -/
lemma ozarow_sq_identity {a b : ℝ} (ha : a ^ 2 = (D₁ - D₀) * (D₂ - D₀))
    (hb : b ^ 2 = (P - D₁) * (P - D₂)) (N : ℝ) :
    (P - D₀) ^ 2 * ((D₁ + N) * (D₂ + N)) -
        ((P - D₀) ^ 2 - (b - a) ^ 2) * ((P + N) * (D₀ + N)) =
      ((b - a) * (D₀ + N) - a * (P - D₀)) ^ 2 := by
  linear_combination (-((P - D₀) ^ 2 + (P - D₀) * (D₀ + N))) * ha + ((P - D₀) * (D₀ + N)) * hb

/-- `a < b` under low distortion: `b² - a² = (P - D₀) (P + D₀ - D₁ - D₂)`. -/
lemma ozarowA_lt_ozarowB (h₁ : D₀ < D₁) (h₂ : D₀ ≤ D₂) (hD₁ : D₁ < P) (hlow : D₁ + D₂ < P + D₀) :
    ozarowA D₀ D₁ D₂ < ozarowB P D₁ D₂ := by
  refine Real.sqrt_lt_sqrt (mul_nonneg (by linarith) (by linarith)) ?_
  nlinarith [mul_pos (show 0 < P - D₀ by linarith) (show 0 < P + D₀ - D₁ - D₂ by linarith)]

/-- The denominator of the ratio is positive. -/
lemma ozarow_denom_pos (h₁ : D₀ < D₁) (h₂ : D₀ ≤ D₂) (hD₁ : D₁ < P) (hD₂ : D₂ < P)
    (hlow : D₁ + D₂ < P + D₀) :
    0 < (P - D₀) ^ 2 - (ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂) ^ 2 := by
  have hab := ozarowA_lt_ozarowB (P := P) h₁ h₂ hD₁ hlow
  have ha0 : 0 ≤ ozarowA D₀ D₁ D₂ := Real.sqrt_nonneg _
  have hbδ : ozarowB P D₁ D₂ < P - D₀ := by
    rw [ozarowB, Real.sqrt_lt' (by linarith)]
    nlinarith [mul_pos (show 0 < D₁ - D₀ by linarith) (show 0 < P - D₂ by linarith),
      mul_nonneg (show 0 ≤ D₂ - D₀ by linarith) (show 0 ≤ P - D₀ by linarith)]
  nlinarith

/-- **Lecture 14, page 14-20.** The bound of the converse is at most `Δ`: for every `N` with
`D₁ + N > 0` and `D₂ + N > 0`, `(P + N) (D₀ + N) / ((D₁ + N) (D₂ + N))` is at most the ratio. -/
theorem ozarow_ratio_le (h₁ : D₀ < D₁) (h₂ : D₀ ≤ D₂) (hD₁ : D₁ < P) (hD₂ : D₂ < P)
    (hlow : D₁ + D₂ < P + D₀) {N : ℝ} (hN₁ : 0 < D₁ + N) (hN₂ : 0 < D₂ + N) :
    (P + N) * (D₀ + N) / ((D₁ + N) * (D₂ + N)) ≤ ozarowRatio P D₀ D₁ D₂ := by
  have hG := ozarow_denom_pos (P := P) h₁ h₂ hD₁ hD₂ hlow
  have ha : ozarowA D₀ D₁ D₂ ^ 2 = (D₁ - D₀) * (D₂ - D₀) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hb : ozarowB P D₁ D₂ ^ 2 = (P - D₁) * (P - D₂) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hsq := ozarow_sq_identity ha hb N
  rw [ozarowRatio, div_le_div_iff₀ (mul_pos hN₁ hN₂) hG]
  nlinarith [sq_nonneg ((ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂) * (D₀ + N) -
    ozarowA D₀ D₁ D₂ * (P - D₀))]

/-- `√((D₁ - D₀) (D₂ - D₀) (P - D₁) (P - D₂)) = a b`. -/
lemma ozarow_sqrt_eq (h₁ : D₀ ≤ D₁) (h₂ : D₀ ≤ D₂) :
    √((D₁ - D₀) * (D₂ - D₀) * (P - D₁) * (P - D₂)) = ozarowA D₀ D₁ D₂ * ozarowB P D₁ D₂ := by
  rw [ozarowA, ozarowB, ← Real.sqrt_mul (mul_nonneg (by linarith) (by linarith))]
  congr 1
  ring

/-- `(b - a) (D₀ + N) = a (P - D₀)` at the optimal `N`. -/
lemma ozarow_opt (h₁ : D₀ < D₁) (h₂ : D₀ ≤ D₂) (hD₁ : D₁ < P) (hD₂ : D₂ < P)
    (hlow : D₁ + D₂ < P + D₀) :
    (ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂) * (D₀ + ozarowN P D₀ D₁ D₂) =
      ozarowA D₀ D₁ D₂ * (P - D₀) := by
  have ha : ozarowA D₀ D₁ D₂ ^ 2 = (D₁ - D₀) * (D₂ - D₀) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hb : ozarowB P D₁ D₂ ^ 2 = (P - D₁) * (P - D₂) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hT : P + D₀ - D₁ - D₂ ≠ 0 := by linarith
  have hN : (P + D₀ - D₁ - D₂) * ozarowN P D₀ D₁ D₂ =
      D₁ * D₂ - D₀ * P + ozarowA D₀ D₁ D₂ * ozarowB P D₁ D₂ := by
    rw [ozarowN, ozarow_sqrt_eq h₁.le h₂]
    field_simp
  set a := ozarowA D₀ D₁ D₂
  set b := ozarowB P D₁ D₂
  set N := ozarowN P D₀ D₁ D₂
  have hN' : (P + D₀ - D₁ - D₂) * (D₀ + N) = a * (a + b) := by
    linear_combination hN - ha
  have hba : (P - D₀) * (P + D₀ - D₁ - D₂) = b ^ 2 - a ^ 2 := by
    linear_combination ha - hb
  refine mul_left_cancel₀ hT ?_
  linear_combination (b - a) * hN' - a * hba

/-- **Lecture 14, page 14-20.** At the optimal `N`, the bound of the converse is `Δ`, for
`D₀ < D₁` and `D₀ < D₂`. -/
theorem ozarow_ratio_ozarowN (h₁ : D₀ < D₁) (h₂ : D₀ < D₂) (hD₁ : D₁ < P) (hD₂ : D₂ < P)
    (hlow : D₁ + D₂ < P + D₀) :
    (P + ozarowN P D₀ D₁ D₂) * (D₀ + ozarowN P D₀ D₁ D₂) /
        ((D₁ + ozarowN P D₀ D₁ D₂) * (D₂ + ozarowN P D₀ D₁ D₂)) = ozarowRatio P D₀ D₁ D₂ := by
  have hG := ozarow_denom_pos (P := P) h₁ h₂.le hD₁ hD₂ hlow
  have hab := ozarowA_lt_ozarowB (P := P) h₁ h₂.le hD₁ hlow
  have ha0 : 0 ≤ ozarowA D₀ D₁ D₂ := Real.sqrt_nonneg _
  have ha : ozarowA D₀ D₁ D₂ ^ 2 = (D₁ - D₀) * (D₂ - D₀) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hb : ozarowB P D₁ D₂ ^ 2 = (P - D₁) * (P - D₂) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hopt := ozarow_opt (P := P) h₁ h₂.le hD₁ hD₂ hlow
  have hsq := ozarow_sq_identity ha hb (ozarowN P D₀ D₁ D₂)
  rw [hopt, sub_self] at hsq
  have hD : 0 ≤ D₀ + ozarowN P D₀ D₁ D₂ := by
    have hpos : 0 < ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂ := by linarith
    have hr : 0 ≤ ozarowA D₀ D₁ D₂ * (P - D₀) := mul_nonneg ha0 (by linarith)
    rw [← hopt] at hr
    exact nonneg_of_mul_nonneg_right hr hpos
  have h31 : 0 < D₁ + ozarowN P D₀ D₁ D₂ := by linarith
  have h32 : 0 < D₂ + ozarowN P D₀ D₁ D₂ := by linarith
  rw [ozarowRatio, div_eq_div_iff (mul_pos h31 h32).ne' hG.ne']
  linear_combination -hsq

/-- `a² b² - (D₁ D₂ - D₀ P)² = (P + D₀ - D₁ - D₂) ((P + D₀) D₁ D₂ - (D₁ + D₂) P D₀)`. -/
lemma ozarow_disc_identity :
    (D₁ - D₀) * (D₂ - D₀) * (P - D₁) * (P - D₂) - (D₁ * D₂ - D₀ * P) ^ 2 =
      (P + D₀ - D₁ - D₂) * ((P + D₀) * (D₁ * D₂) - (D₁ + D₂) * (P * D₀)) := by
  ring

/-- **The condition for the converse.** The optimal noise variance of the converse is positive if
and only if `1/D₁ + 1/D₂ < 1/D₀ + 1/P`, which the notes do not assume: the variance of the noise
`Zᵢ` must be positive. -/
theorem ozarowN_pos_iff (h₀ : 0 < D₀) (h₁ : D₀ < D₁) (h₂ : D₀ ≤ D₂) (hD₁ : D₁ < P) (hD₂ : D₂ < P)
    (hlow : D₁ + D₂ < P + D₀) :
    0 < ozarowN P D₀ D₁ D₂ ↔ 1 / D₁ + 1 / D₂ < 1 / D₀ + 1 / P := by
  have hT : 0 < P + D₀ - D₁ - D₂ := by linarith
  have hP : 0 < P := by linarith
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hcond : 1 / D₁ + 1 / D₂ < 1 / D₀ + 1 / P ↔
      (D₁ + D₂) * (P * D₀) < (P + D₀) * (D₁ * D₂) := by
    rw [div_add_div _ _ hD₁0.ne' hD₂0.ne', div_add_div _ _ h₀.ne' hP.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [hcond, ozarowN, div_pos_iff_of_pos_right hT]
  have hd := ozarow_disc_identity (P := P) (D₀ := D₀) (D₁ := D₁) (D₂ := D₂)
  have hnn : 0 ≤ (D₁ - D₀) * (D₂ - D₀) * (P - D₁) * (P - D₂) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  set s := √((D₁ - D₀) * (D₂ - D₀) * (P - D₁) * (P - D₂)) with hs
  have hs2 : s ^ 2 = (D₁ - D₀) * (D₂ - D₀) * (P - D₁) * (P - D₂) := Real.sq_sqrt hnn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  constructor
  · intro h
    by_contra hc
    push Not at hc
    -- Then `s² ≤ (D₁ D₂ - D₀ P)²` and `D₁ D₂ ≤ D₀ P`.
    have hle : (P + D₀) * (D₁ * D₂) - (D₁ + D₂) * (P * D₀) ≤ 0 := by linarith
    have hprod := mul_nonpos_of_nonneg_of_nonpos hT.le hle
    have hM : D₁ * D₂ ≤ D₀ * P := by
      have h3 : (P + D₀) * (D₁ * D₂) ≤ (P + D₀) * (P * D₀) := by
        refine hc.trans ?_
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hpos : 0 < P + D₀ := by linarith
      have h4 := le_of_mul_le_mul_left h3 hpos
      linarith
    have hsq : s ^ 2 ≤ (D₁ * D₂ - D₀ * P) ^ 2 := by
      rw [hs2]
      linarith
    nlinarith
  · intro h
    have hprod : 0 < (P + D₀ - D₁ - D₂) * ((P + D₀) * (D₁ * D₂) - (D₁ + D₂) * (P * D₀)) :=
      mul_pos hT (by linarith)
    have hsq : (D₁ * D₂ - D₀ * P) ^ 2 < s ^ 2 := by
      rw [hs2]
      linarith
    have h5 := abs_lt_of_sq_lt_sq hsq hs0
    linarith [(abs_lt.1 h5).1]

/-- **The correlation of the reproductions for `ρ = -1`, page 14-18.** If `a² = (D₁ - D₀)(D₂ - D₀)`
and `b² = (P - D₁)(P - D₂)`, then the covariance `(1 - D₁/P) (1 - D₂/P) (P + K₁₂)` of `X̂₁`, `X̂₂`
  with
`K₁₂ = N₀ - √((N₁ - N₀)(N₂ - N₀))` is `b (b - a) / (P - D₀)`, so the correlation coefficient of
  `X̂₁`,
`X̂₂` is `(b - a) / (P - D₀)` and `1 / (1 - corr²)` is the ratio. Hence `I(X̂₁; X̂₂) = Δ`. -/
theorem ozarow_corr_sq (hP : 0 < P) (h₁ : D₀ ≤ D₁) (hD₁ : D₁ < P) (hD₂ : D₂ < P)
    (hG : 0 < (P - D₀) ^ 2 - (ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂) ^ 2) :
    (1 - D₁ / P) * (1 - D₂ / P) * (P + (mdNoise P D₀ -
        √((mdNoise P D₁ - mdNoise P D₀) * (mdNoise P D₂ - mdNoise P D₀)))) =
      ozarowB P D₁ D₂ * (ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂) / (P - D₀) ∧
    1 / (1 - ((ozarowB P D₁ D₂ - ozarowA D₀ D₁ D₂) / (P - D₀)) ^ 2) =
      ozarowRatio P D₀ D₁ D₂ := by
  have hδ : 0 < P - D₀ := by linarith
  have hb₁ : 0 < P - D₁ := by linarith
  have hb₂ : 0 < P - D₂ := by linarith
  have hb : 0 < ozarowB P D₁ D₂ := Real.sqrt_pos.2 (mul_pos hb₁ hb₂)
  have hbs : ozarowB P D₁ D₂ ^ 2 = (P - D₁) * (P - D₂) := Real.sq_sqrt (mul_pos hb₁ hb₂).le
  constructor
  · rw [mdNoise_sub hD₁ (by linarith), mdNoise_sub hD₂ (by linarith)]
    have hs : √((P ^ 2 * (D₁ - D₀) / ((P - D₁) * (P - D₀))) *
        (P ^ 2 * (D₂ - D₀) / ((P - D₂) * (P - D₀)))) =
        P ^ 2 * ozarowA D₀ D₁ D₂ / (ozarowB P D₁ D₂ * (P - D₀)) := by
      have e : (P ^ 2 * (D₁ - D₀) / ((P - D₁) * (P - D₀))) *
          (P ^ 2 * (D₂ - D₀) / ((P - D₂) * (P - D₀))) =
          (P ^ 2 / (ozarowB P D₁ D₂ * (P - D₀))) ^ 2 * ((D₁ - D₀) * (D₂ - D₀)) := by
        rw [div_pow, mul_pow, hbs]
        field_simp
      rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      ring
    rw [hs]
    have hadd : P + (mdNoise P D₀ - P ^ 2 * ozarowA D₀ D₁ D₂ / (ozarowB P D₁ D₂ * (P - D₀))) =
        P ^ 2 / (P - D₀) * (1 - ozarowA D₀ D₁ D₂ / ozarowB P D₁ D₂) := by
      have := add_mdNoise (P := P) (D₀ := D₀) (by linarith)
      rw [← add_sub_assoc, this]
      field_simp
    rw [hadd]
    have e2 : (1 - D₁ / P) * (1 - D₂ / P) = ozarowB P D₁ D₂ ^ 2 / P ^ 2 := by
      rw [hbs]
      field_simp
    rw [e2]
    field_simp
  · rw [ozarowRatio, div_pow]
    field_simp

/-- **The distortion of independent noises.** If `X̂₁` and `X̂₂` have independent noises `Z₁`, `Z₂`,
then the minimum mean squared error of `X` given both is the inverse of
`1/P + 1/N₁ + 1/N₂ = 1/D₁ + 1/D₂ - 1/P`, and the sum rate is `R(P/D₁) + R(P/D₂)`. So the distortion
`D₀` is achieved at this sum rate if `1/D₁ + 1/D₂ - 1/P ≥ 1/D₀`. -/
theorem mdNoise_indep_inv (hP : 0 < P) (hD₁0 : 0 < D₁) (hD₂0 : 0 < D₂) (hD₁ : D₁ < P)
    (hD₂ : D₂ < P) :
    1 / P + 1 / mdNoise P D₁ + 1 / mdNoise P D₂ = 1 / D₁ + 1 / D₂ - 1 / P := by
  have h1 : P - D₁ ≠ 0 := by linarith
  have h2 : P - D₂ ≠ 0 := by linarith
  simp only [mdNoise]
  field_simp
  ring

/-- **A counterexample to Theorem 2 of Lecture 14 as printed (page 14-15).** At
`(P, D₀, D₁, D₂) = (1, 3/10, 31/100, 31/100)`, which has low distortion: the optimal noise variance
of the converse is negative, `1/D₀ + 1/P < 1/D₁ + 1/D₂`, and the printed sum rate
`R(P/D₀) + Δ` is strictly larger than `R(P/D₁) + R(P/D₂)`. But the rate pair
`(R(P/D₁), R(P/D₂))` has the distortions `(D₁, D₂)` and, with independent noises, the combined
distortion `(1/D₁ + 1/D₂ - 1/P)⁻¹ < D₀`, by `mdNoise_indep_inv`. It is also strictly larger than the
sum `2 R(P/D₀)` of the simple scheme that sends the same description twice. -/
theorem ozarow_counterexample :
    (31 / 100 + 31 / 100 : ℝ) < 1 + 3 / 10 ∧ ozarowN 1 (3 / 10) (31 / 100) (31 / 100) < 0 ∧
    (1 / (3 / 10) + 1 / 1 : ℝ) < 1 / (31 / 100) + 1 / (31 / 100) ∧
    qgR (1 / (31 / 100)) + qgR (1 / (31 / 100)) <
      qgR (1 / (3 / 10)) + ozarowDelta 1 (3 / 10) (31 / 100) (31 / 100) ∧
    qgR (1 / (3 / 10)) + qgR (1 / (3 / 10)) <
      qgR (1 / (3 / 10)) + ozarowDelta 1 (3 / 10) (31 / 100) (31 / 100) := by
  have hA : ozarowA (3 / 10) (31 / 100) (31 / 100) = 1 / 100 := by
    rw [ozarowA, show ((31 / 100 - 3 / 10) * (31 / 100 - 3 / 10) : ℝ) = (1 / 100) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hB : ozarowB 1 (31 / 100) (31 / 100) = 69 / 100 := by
    rw [ozarowB, show ((1 - 31 / 100) * (1 - 31 / 100) : ℝ) = (69 / 100) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hR : ozarowRatio 1 (3 / 10) (31 / 100) (31 / 100) = 1225 / 69 := by
    rw [ozarowRatio, hA, hB]
    norm_num
  have hΔ : ozarowDelta 1 (3 / 10) (31 / 100) (31 / 100) = qgR (1225 / 69) := by
    rw [ozarowDelta, hR]
    norm_num
  have hS : √((31 / 100 - 3 / 10) * (31 / 100 - 3 / 10) * (1 - 31 / 100) * (1 - 31 / 100) : ℝ) =
      69 / 10000 := by
    rw [show ((31 / 100 - 3 / 10) * (31 / 100 - 3 / 10) * (1 - 31 / 100) * (1 - 31 / 100) : ℝ) =
      (69 / 10000) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hq : ∀ {x y z : ℝ}, 0 < x → 0 < y → 0 < z → x * y < z * z →
      qgR x + qgR y < qgR z + qgR z := fun {x y z} hx hy hz h => by
    simp only [qgR]
    have := Real.log_lt_log (mul_pos hx hy) h
    rw [Real.log_mul hx.ne' hy.ne', Real.log_mul hz.ne' hz.ne'] at this
    linarith
  have hq' : ∀ {x y z : ℝ}, 0 < x → 0 < y → 0 < z → x * x < y * z →
      qgR x + qgR x < qgR y + qgR z := fun {x y z} hx hy hz h => by
    simp only [qgR]
    have := Real.log_lt_log (mul_pos hx hx) h
    rw [Real.log_mul hx.ne' hx.ne', Real.log_mul hy.ne' hz.ne'] at this
    linarith
  refine ⟨by norm_num, ?_, by norm_num, ?_, ?_⟩
  · rw [ozarowN, hS]
    norm_num
  · rw [hΔ]
    exact hq' (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [hΔ]
    exact hq' (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Ozarow

end InfoTheory
