/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Quadratic Gaussian distributed source coding: the formulas

Lecture 13 determines the rate–distortion region of the quadratic Gaussian distributed source coding
problem and of the Gaussian CEO problem. The coding theorems concern continuous sources and need the
conditional entropy power inequality, which are not in this library. This file proves the formulas
and
the algebra of the proofs, with the rates in nats.

## Main definitions

* `qgR x`: `R(x) = (1 / 2) log x`.
* `qgG ρ R D`: `g(R, D) = R((1 - ρ² + ρ² e^{-2R}) / D)`.
* `qgPhi ρ D₁ D₂`: `φ(D₁, D₂)`.
* `qgRegion ρ D₁ D₂`: the region of Theorem 3 of Lecture 13.
* `qgD₁`, `qgD₂`: the distortions of a distributed Gaussian test channel.
* `qgTheta`, `qgR1`, `qgR2`: `θ*`, and the two lower bounds on the sum rate.
* `ceoRegion`: the rate–distortion region of the Gaussian CEO problem.

## Main statements

* `qg_lemma4`: Lemma 4, the error covariance of a distributed Gaussian test channel.
* `qgG_corner`, `qgR_corner_sum`: the left corner point of the rate region of a test channel.
* `qg_lemma3`: Lemma 3, the sum rate and the second bound are not active in case 1.
* `qgTheta_quadratic`, `qgR1_theta`, `qgR2_theta`: the point `θ*` of the converse.
* `qg_le_max`: `min_θ max {R₁(θ), R₂(θ)}` is the sum rate of Theorem 3.
* `qg_markov`, `qg_lemma5_step3`, `qg_alpha`: the Markov chain and the matrix bound of Lemma 5.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The region of Theorem 3 -/

/-- `R(x) = (1 / 2) log x`, in nats. -/
def qgR (x : ℝ) : ℝ := 1 / 2 * log x

/-- **Theorem 3 of Lecture 13.** `g(R, D) = R((1 - ρ² + ρ² e^{-2R}) / D)`. -/
def qgG (ρ R D : ℝ) : ℝ := qgR ((1 - ρ ^ 2 + ρ ^ 2 * exp (-(2 * R))) / D)

/-- **Theorem 3 of Lecture 13.** `φ(D₁, D₂) = 1 + √(1 + 4 ρ² D₁ D₂ / (1 - ρ²)²)`. -/
def qgPhi (ρ D₁ D₂ : ℝ) : ℝ := 1 + √(1 + 4 * ρ ^ 2 * D₁ * D₂ / (1 - ρ ^ 2) ^ 2)

/-- **Theorem 3 of Lecture 13 of [elgamal2010], page 13-16.** The rate–distortion region of the
quadratic
Gaussian problem, in nats: the intersection of `R₁(D₁)`, `R₂(D₂)` and `R₁₂(D₁, D₂)`. -/
def qgRegion (ρ D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | qgG ρ R.2 D₁ ≤ R.1 ∧ qgG ρ R.1 D₂ ≤ R.2 ∧
    qgR ((1 - ρ ^ 2) * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂)) ≤ R.1 + R.2}

/-! ### Distributed Gaussian test channels -/

section Test

variable {ρ N₁ N₂ : ℝ}

/-- The determinant `(1 + N₁)(1 + N₂) - ρ²`. -/
def qgDelta (ρ N₁ N₂ : ℝ) : ℝ := (1 + N₁) * (1 + N₂) - ρ ^ 2

/-- **Lecture 13, page 13-18.** `D₁ = N₁ (1 + N₂ - ρ²) / ((1 + N₁)(1 + N₂) - ρ²)`. -/
def qgD₁ (ρ N₁ N₂ : ℝ) : ℝ := N₁ * (1 + N₂ - ρ ^ 2) / qgDelta ρ N₁ N₂

/-- **Lecture 13, page 13-18.** `D₂ = N₂ (1 + N₁ - ρ²) / ((1 + N₁)(1 + N₂) - ρ²)`. -/
def qgD₂ (ρ N₁ N₂ : ℝ) : ℝ := N₂ * (1 + N₁ - ρ ^ 2) / qgDelta ρ N₁ N₂

lemma qgDelta_pos (hρ : ρ ^ 2 < 1) (h₁ : 0 < N₁) (h₂ : 0 < N₂) : 0 < qgDelta ρ N₁ N₂ := by
  unfold qgDelta
  nlinarith [mul_pos h₁ h₂]

/-- **Lemma 4 of Lecture 13, page 13-22.** The error covariance of the MMSE estimate of `X` given
`Uⱼ = Xⱼ + Vⱼ` has the inverse `K_X⁻¹ + K_V⁻¹`: the matrix with the diagonal `(D₁, D₂)` and the
off-diagonal
term `ρ N₁ N₂ / Δ` is the inverse of `K_X⁻¹ + diag(1 / N₁, 1 / N₂)`. -/
theorem qg_lemma4 (hρ : ρ ^ 2 < 1) (h₁ : 0 < N₁) (h₂ : 0 < N₂) :
    !![qgD₁ ρ N₁ N₂, ρ * N₁ * N₂ / qgDelta ρ N₁ N₂; ρ * N₁ * N₂ / qgDelta ρ N₁ N₂, qgD₂ ρ N₁ N₂] *
      !![1 / (1 - ρ ^ 2) + 1 / N₁, -ρ / (1 - ρ ^ 2); -ρ / (1 - ρ ^ 2), 1 / (1 - ρ ^ 2) + 1 / N₂] =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hΔ := (qgDelta_pos hρ h₁ h₂).ne'
  have ha : 1 - ρ ^ 2 ≠ 0 := by linarith
  have hd : qgDelta ρ N₁ N₂ = (1 + N₁) * (1 + N₂) - ρ ^ 2 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, qgD₁, qgD₂] <;> field_simp <;> rw [hd] <;> ring

/-- **Lecture 13, page 13-19.** The left corner point: `R((1 + N₁)(1 + N₂) - ρ²) / (N₁ (1 + N₂))) =
g₁(R((1 + N₂) / N₂), D₁)`. -/
theorem qgG_corner (hρ : ρ ^ 2 < 1) (h₁ : 0 < N₁) (h₂ : 0 < N₂) :
    qgG ρ (qgR ((1 + N₂) / N₂)) (qgD₁ ρ N₁ N₂) = qgR (qgDelta ρ N₁ N₂ / (N₁ * (1 + N₂))) := by
  have hpos : 0 < (1 + N₂) / N₂ := by positivity
  have hexp : exp (-(2 * qgR ((1 + N₂) / N₂))) = N₂ / (1 + N₂) := by
    rw [qgR, show -(2 * (1 / 2 * log ((1 + N₂) / N₂))) = -log ((1 + N₂) / N₂) by ring, exp_neg,
      exp_log hpos, inv_div]
  have hΔ := (qgDelta_pos hρ h₁ h₂).ne'
  have ha : 1 + N₂ - ρ ^ 2 ≠ 0 := by nlinarith
  have hd : qgDelta ρ N₁ N₂ = (1 + N₁) * (1 + N₂) - ρ ^ 2 := rfl
  rw [qgG, hexp, qgD₁]
  congr 1
  rw [hd] at hΔ ⊢
  field_simp
  ring

/-- **Lecture 13, page 13-19.** The sum of the rates of the left corner point. -/
theorem qgR_corner_sum (hρ : ρ ^ 2 < 1) (h₁ : 0 < N₁) (h₂ : 0 < N₂) :
    qgR (qgDelta ρ N₁ N₂ / (N₁ * (1 + N₂))) + qgR ((1 + N₂) / N₂) =
      qgR (qgDelta ρ N₁ N₂ / (N₁ * N₂)) := by
  have hΔ := qgDelta_pos hρ h₁ h₂
  simp only [qgR]
  rw [← mul_add, ← log_mul (by positivity) (by positivity)]
  congr 2
  field_simp

/-- **Lecture 13, page 13-21.** The ratio of the distortions:
`D₂ / D₁ = (1 / N₁ + 1 / (1 - ρ²)) / (1 / N₂ + 1 / (1 - ρ²))`. -/
theorem qgD_ratio (hρ : ρ ^ 2 < 1) (h₁ : 0 < N₁) (h₂ : 0 < N₂) :
    qgD₂ ρ N₁ N₂ / qgD₁ ρ N₁ N₂ =
      (1 / N₁ + 1 / (1 - ρ ^ 2)) / (1 / N₂ + 1 / (1 - ρ ^ 2)) := by
  have hΔ := (qgDelta_pos hρ h₁ h₂).ne'
  have ha : 1 - ρ ^ 2 ≠ 0 := by linarith
  have h3 : 1 + N₂ - ρ ^ 2 ≠ 0 := by nlinarith
  have h4 : 1 + N₁ - ρ ^ 2 ≠ 0 := by nlinarith
  have h5 : 1 / N₂ + 1 / (1 - ρ ^ 2) ≠ 0 := by
    have : 0 < 1 - ρ ^ 2 := by linarith
    positivity
  simp only [qgD₁, qgD₂]
  field_simp
  ring

/-- **Lecture 13, page 13-20.** In case 1, the test channel with `N₁ = D₁ / (1 - D₁)` and `U₂`
constant has
the distortions `1 - 1 / (1 + N₁) = D₁` and `1 - ρ² / (1 + N₁) = 1 - ρ² + ρ² D₁`. -/
theorem qg_case1 {D₁ : ℝ} (hD₁ : D₁ < 1) :
    1 - 1 / (1 + D₁ / (1 - D₁)) = D₁ ∧ 1 - ρ ^ 2 / (1 + D₁ / (1 - D₁)) = 1 - ρ ^ 2 + ρ ^ 2 * D₁ :=
      by
  have h : 1 - D₁ ≠ 0 := by linarith
  have e : 1 + D₁ / (1 - D₁) = 1 / (1 - D₁) := by
    field_simp
    ring
  rw [e]
  constructor <;> field_simp <;> ring

end Test

/-! ### Lemma 3 -/

section Lemma3

variable {ρ D₁ D₂ : ℝ}

/-- **Lecture 13, page 13-51.** The sum rate of Theorem 3 at `D₂ = 1 - ρ² + ρ² D₁`:
`(1 - ρ²) φ / (2 D₁ D₂) = 1 / D₁`. -/
theorem qgPhi_corner (hρ : ρ ^ 2 < 1) (hD₁ : 0 < D₁) :
    (1 - ρ ^ 2) * qgPhi ρ D₁ (1 - ρ ^ 2 + ρ ^ 2 * D₁) /
      (2 * D₁ * (1 - ρ ^ 2 + ρ ^ 2 * D₁)) = 1 / D₁ := by
  have ha : 0 < 1 - ρ ^ 2 := by linarith
  have hb : 0 ≤ ρ ^ 2 * D₁ := by positivity
  have hsq : 1 + 4 * ρ ^ 2 * D₁ * (1 - ρ ^ 2 + ρ ^ 2 * D₁) / (1 - ρ ^ 2) ^ 2 =
      ((1 - ρ ^ 2 + 2 * (ρ ^ 2 * D₁)) / (1 - ρ ^ 2)) ^ 2 := by
    field_simp
    ring
  have hphi : qgPhi ρ D₁ (1 - ρ ^ 2 + ρ ^ 2 * D₁) =
      2 * (1 - ρ ^ 2 + ρ ^ 2 * D₁) / (1 - ρ ^ 2) := by
    rw [qgPhi, hsq, sqrt_sq (by positivity)]
    field_simp
    ring
  rw [hphi]
  have hne : 1 - ρ ^ 2 + ρ ^ 2 * D₁ ≠ 0 := by positivity
  field_simp

/-- The quantity `(a + √(a² + 4 k D)) / D` is nonincreasing in `D`. -/
private lemma phi_div_anti {a k D D' : ℝ} (ha : 0 < a) (hk : 0 ≤ k) (hD : 0 < D) (hDD : D ≤ D') :
    (a + √(a ^ 2 + 4 * k * D')) / D' ≤ (a + √(a ^ 2 + 4 * k * D)) / D := by
  have hD' : 0 < D' := hD.trans_le hDD
  rw [div_le_div_iff₀ hD' hD]
  have hs : 0 ≤ √(a ^ 2 + 4 * k * D) := sqrt_nonneg _
  have hs' : 0 ≤ √(a ^ 2 + 4 * k * D') := sqrt_nonneg _
  have h1 : √(a ^ 2 + 4 * k * D') * D ≤ √(a ^ 2 + 4 * k * D) * D' := by
    have e1 : √(a ^ 2 + 4 * k * D') * D = √((a ^ 2 + 4 * k * D') * D ^ 2) := by
      rw [sqrt_mul (by positivity), sqrt_sq hD.le]
    have e2 : √(a ^ 2 + 4 * k * D) * D' = √((a ^ 2 + 4 * k * D) * D' ^ 2) := by
      rw [sqrt_mul (by positivity), sqrt_sq hD'.le]
    rw [e1, e2]
    refine sqrt_le_sqrt ?_
    nlinarith [mul_nonneg (mul_nonneg hD.le hD'.le) (mul_nonneg hk (sub_nonneg.2 hDD)),
      mul_nonneg (sq_nonneg a) (mul_nonneg (sub_nonneg.2 hDD) (add_nonneg hD.le hD'.le))]
  nlinarith [mul_le_mul_of_nonneg_left hDD ha.le]

/-- **Lemma 3 of Lecture 13, page 13-20.** If `1 - D₂ ≤ ρ² (1 - D₁)`, the rate pairs of `R₁(D₁)` are
in
`R₁₂(D₁, D₂)` and, with nonnegative rates, in `R₂(D₂)`. -/
theorem qg_lemma3 (hρ : ρ ^ 2 < 1) (hD₁ : 0 < D₁) (hc : 1 - D₂ ≤ ρ ^ 2 * (1 - D₁)) {R₁ R₂ : ℝ}
    (hR₂0 : 0 ≤ R₂) (hR : qgG ρ R₂ D₁ ≤ R₁) :
    qgR ((1 - ρ ^ 2) * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂)) ≤ R₁ + R₂ ∧ qgG ρ R₁ D₂ ≤ R₂ := by
  set a := 1 - ρ ^ 2 with ha'
  have ha : 0 < a := by rw [ha']; linarith
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hD₂l : a + ρ ^ 2 * D₁ ≤ D₂ := by rw [ha']; linarith
  have hD₂ : 0 < D₂ := by
    have : 0 ≤ ρ ^ 2 * D₁ := by positivity
    linarith
  set x := exp (-(2 * R₁)) with hx
  set y := exp (-(2 * R₂)) with hy
  have hx0 : 0 < x := exp_pos _
  have hy0 : 0 < y := exp_pos _
  have hy1 : y ≤ 1 := exp_le_one_iff.2 (by linarith)
  have hxinv : exp (2 * R₁) = 1 / x := by
    rw [hx, exp_neg, one_div, inv_inv]
  have hyinv : exp (2 * R₂) = 1 / y := by
    rw [hy, exp_neg, one_div, inv_inv]
  -- The hypothesis.
  have hpos1 : 0 < (a + ρ ^ 2 * y) / D₁ := by positivity
  have h1 : (a + ρ ^ 2 * y) / D₁ ≤ 1 / x := by
    rw [← hxinv, ← exp_log hpos1]
    refine exp_le_exp.2 ?_
    have : 1 / 2 * log ((a + ρ ^ 2 * y) / D₁) ≤ R₁ := hR
    linarith
  have h2 : x * (a + ρ ^ 2 * y) ≤ D₁ := by
    rw [div_le_div_iff₀ hD₁ hx0] at h1
    linarith
  refine ⟨?_, ?_⟩
  · -- The sum rate.
    have hk : 0 ≤ ρ ^ 2 * D₁ := by positivity
    have hQ : a * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂) ≤ 1 / D₁ := by
      have hphi : ∀ D : ℝ, 0 ≤ D → a * qgPhi ρ D₁ D = a + √(a ^ 2 + 4 * (ρ ^ 2 * D₁) * D) :=
        fun D hD => by
          have e : a ^ 2 + 4 * (ρ ^ 2 * D₁) * D =
              (1 + 4 * ρ ^ 2 * D₁ * D / a ^ 2) * a ^ 2 := by
            field_simp
          rw [qgPhi, mul_add, mul_one, e, sqrt_mul (by positivity), sqrt_sq ha.le, mul_comm a]
      have hanti := phi_div_anti ha hk (D := a + ρ ^ 2 * D₁) (D' := D₂) (by positivity) hD₂l
      have hcorner := qgPhi_corner hρ hD₁
      rw [← ha', hphi _ (by positivity)] at hcorner
      rw [hphi _ hD₂.le]
      calc (a + √(a ^ 2 + 4 * (ρ ^ 2 * D₁) * D₂)) / (2 * D₁ * D₂)
          = (a + √(a ^ 2 + 4 * (ρ ^ 2 * D₁) * D₂)) / D₂ / (2 * D₁) := by
            rw [div_div]
            congr 1
            ring
        _ ≤ (a + √(a ^ 2 + 4 * (ρ ^ 2 * D₁) * (a + ρ ^ 2 * D₁))) / (a + ρ ^ 2 * D₁) / (2 * D₁) :=
            div_le_div_of_nonneg_right hanti (by positivity)
        _ = (a + √(a ^ 2 + 4 * (ρ ^ 2 * D₁) * (a + ρ ^ 2 * D₁))) /
              (2 * D₁ * (a + ρ ^ 2 * D₁)) := by
            rw [div_div]
            congr 1
            ring
        _ = 1 / D₁ := hcorner
    have hpos2 : 0 < a * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂) := by
      have : 0 < qgPhi ρ D₁ D₂ := by
        have := sqrt_nonneg (1 + 4 * ρ ^ 2 * D₁ * D₂ / (1 - ρ ^ 2) ^ 2)
        unfold qgPhi
        linarith
      positivity
    have hlog1 : log (a * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂)) ≤ log (1 / D₁) :=
      log_le_log hpos2 hQ
    -- `R(1 / D₁) ≤ R₁ + R₂`.
    have hR' : 1 / 2 * log ((a + ρ ^ 2 * y) / D₁) ≤ R₁ := hR
    have hlogy : log y = -(2 * R₂) := by rw [hy, log_exp]
    have hlog2 : log (1 / D₁) ≤ log ((a + ρ ^ 2 * y) / D₁) - log y := by
      rw [← log_div hpos1.ne' hy0.ne']
      refine log_le_log (by positivity) ?_
      rw [div_div, div_le_div_iff₀ hD₁ (by positivity)]
      have h3 : y * D₁ ≤ (a + ρ ^ 2 * y) * D₁ := by
        refine mul_le_mul_of_nonneg_right ?_ hD₁.le
        have : a + ρ ^ 2 = 1 := by rw [ha']; ring
        nlinarith [mul_nonneg ha.le (sub_nonneg.2 hy1)]
      linarith
    change 1 / 2 * log (a * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂)) ≤ R₁ + R₂
    rw [hlogy] at hlog2
    linarith
  · -- The second bound.
    have hkey : y * (a + ρ ^ 2 * x) ≤ D₂ := by
      have h3 : a + ρ ^ 2 * (x * (a + ρ ^ 2 * y)) ≤ D₂ :=
        le_trans (by nlinarith [mul_le_mul_of_nonneg_left h2 hρ2]) hD₂l
      have hρ1 : a + ρ ^ 2 = 1 := by rw [ha']; ring
      have h4 : 0 ≤ a * (1 - y) * (1 + ρ ^ 2 * x) :=
        mul_nonneg (mul_nonneg ha.le (sub_nonneg.2 hy1)) (by positivity)
      have h5 : a + ρ ^ 2 * (x * (a + ρ ^ 2 * y)) - y * (a + ρ ^ 2 * x) =
          a * (1 - y) * (1 + ρ ^ 2 * x) := by
        have hρe : ρ ^ 2 = 1 - a := by linarith
        rw [hρe]
        ring
      linarith
    have hpos3 : 0 < (a + ρ ^ 2 * x) / D₂ := by positivity
    have h6 : (a + ρ ^ 2 * x) / D₂ ≤ 1 / y := by
      rw [div_le_div_iff₀ hD₂ hy0]
      linarith
    have h7 : log ((a + ρ ^ 2 * x) / D₂) ≤ 2 * R₂ := by
      rw [← hyinv] at h6
      calc _ ≤ log (exp (2 * R₂)) := log_le_log hpos3 h6
        _ = 2 * R₂ := log_exp _
    change 1 / 2 * log ((a + ρ ^ 2 * x) / D₂) ≤ R₂
    linarith

end Lemma3

/-! ### The converse: `θ*` -/

section Theta

variable {ρ D₁ D₂ θ : ℝ}

/-- **Lecture 13, page 13-22.** `θ* = (√((1 - ρ²)² + 4 ρ² D₁ D₂) - (1 - ρ²)) / (2 ρ √(D₁ D₂))`. -/
def qgTheta (ρ D₁ D₂ : ℝ) : ℝ :=
  (√((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) - (1 - ρ ^ 2)) / (2 * ρ * √(D₁ * D₂))

/-- **Lecture 13, page 13-30.** `N = (1 - ρ²) / (ρ √(D₁ D₂))`. -/
def qgN (ρ D₁ D₂ : ℝ) : ℝ := (1 - ρ ^ 2) / (ρ * √(D₁ * D₂))

/-- **The cooperative lower bound (Lecture 13, page 13-29).** `R₁(θ) = R(|K_X| / |K(θ)|)`. -/
def qgR1 (ρ D₁ D₂ θ : ℝ) : ℝ := qgR ((1 - ρ ^ 2) / (D₁ * D₂ * (1 - θ ^ 2)))

/-- **The `μ`-sum lower bound (Lecture 13, page 13-30).**
`R₂(θ) = R(|K_X| (2 (1 + θ) + N) / (N D₁ D₂ (1 + θ)²))`. -/
def qgR2 (ρ D₁ D₂ θ : ℝ) : ℝ :=
  qgR ((1 - ρ ^ 2) * (2 * (1 + θ) + qgN ρ D₁ D₂) / (qgN ρ D₁ D₂ * (D₁ * D₂) * (1 + θ) ^ 2))

variable (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)

include hρ0 hD₁ hD₂ in
/-- **Lecture 13, page 13-22.** `θ*` is the root of `ρ s θ² + (1 - ρ²) θ - ρ s = 0`, with
`s = √(D₁ D₂)`:
this says that `K(θ)⁻¹ - K_X⁻¹` is diagonal. -/
theorem qgTheta_quadratic :
    (1 - ρ ^ 2) * qgTheta ρ D₁ D₂ = ρ * √(D₁ * D₂) * (1 - qgTheta ρ D₁ D₂ ^ 2) := by
  have hs : 0 < √(D₁ * D₂) := sqrt_pos.2 (mul_pos hD₁ hD₂)
  have hs2 : √(D₁ * D₂) ^ 2 = D₁ * D₂ := sq_sqrt (mul_pos hD₁ hD₂).le
  have hq2 : √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) ^ 2 =
      (1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂) := sq_sqrt (by positivity)
  have hd : 2 * ρ * √(D₁ * D₂) ≠ 0 := by positivity
  have e : qgTheta ρ D₁ D₂ * (2 * ρ * √(D₁ * D₂)) =
      √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) - (1 - ρ ^ 2) := div_mul_cancel₀ _ hd
  set t := qgTheta ρ D₁ D₂
  set s := √(D₁ * D₂)
  set q := √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂))
  have hq : q = 2 * ρ * s * t + (1 - ρ ^ 2) := by linear_combination -e
  rw [← hs2, hq] at hq2
  have h0 : 4 * ρ * s * ((1 - ρ ^ 2) * t - ρ * s * (1 - t ^ 2)) = 0 := by
    linear_combination hq2
  have hne : 4 * ρ * s ≠ 0 := by positivity
  have := (mul_eq_zero.1 h0).resolve_left hne
  linarith

include hρ0 hρ1 hD₁ hD₂ in
/-- `0 ≤ θ* < 1`. -/
theorem qgTheta_mem : 0 ≤ qgTheta ρ D₁ D₂ ∧ qgTheta ρ D₁ D₂ < 1 := by
  have hs : 0 < √(D₁ * D₂) := sqrt_pos.2 (mul_pos hD₁ hD₂)
  have ha : 0 < 1 - ρ ^ 2 := by nlinarith
  have hq2 : √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) ^ 2 =
      (1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂) := sq_sqrt (by positivity)
  have hs2 : √(D₁ * D₂) ^ 2 = D₁ * D₂ := sq_sqrt (mul_pos hD₁ hD₂).le
  have hq0 : 0 ≤ √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) := sqrt_nonneg _
  have hqa : 1 - ρ ^ 2 < √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) := by
    refine lt_sqrt_of_sq_lt ?_
    have : 0 < 4 * ρ ^ 2 * (D₁ * D₂) := by positivity
    linarith
  have hd : 0 < 2 * ρ * √(D₁ * D₂) := by positivity
  refine ⟨div_nonneg (by linarith) hd.le, ?_⟩
  rw [qgTheta, div_lt_one hd]
  set s := √(D₁ * D₂)
  set q := √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂))
  have : q < 2 * ρ * s + (1 - ρ ^ 2) := by
    refine abs_lt_of_sq_lt_sq' ?_ (by positivity) |>.2
    rw [hq2, ← hs2]
    nlinarith [mul_pos (mul_pos hρ0 hs) ha]
  linarith

include hρ0 hρ1 hD₁ hD₂ in
/-- **Lecture 13, page 13-31.** At `θ*`, `R₁(θ*) = R((1 - ρ²) φ(D₁, D₂) / (2 D₁ D₂))`. -/
theorem qgR1_theta :
    qgR1 ρ D₁ D₂ (qgTheta ρ D₁ D₂) = qgR ((1 - ρ ^ 2) * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂)) := by
  have ha : 0 < 1 - ρ ^ 2 := by nlinarith
  have hs : 0 < √(D₁ * D₂) := sqrt_pos.2 (mul_pos hD₁ hD₂)
  have hs2 : √(D₁ * D₂) ^ 2 = D₁ * D₂ := sq_sqrt (mul_pos hD₁ hD₂).le
  have hq0 : 0 ≤ √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) := sqrt_nonneg _
  have hq2 : √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) ^ 2 =
      (1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂) := sq_sqrt (by positivity)
  -- `(1 - ρ²) φ = (1 - ρ²) + q`.
  have hphi : (1 - ρ ^ 2) * qgPhi ρ D₁ D₂ =
      (1 - ρ ^ 2) + √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) := by
    have e : (1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂) =
        (1 + 4 * ρ ^ 2 * D₁ * D₂ / (1 - ρ ^ 2) ^ 2) * (1 - ρ ^ 2) ^ 2 := by
      field_simp
    rw [qgPhi, mul_add, mul_one, e, sqrt_mul (by positivity), sqrt_sq ha.le, mul_comm (1 - ρ ^ 2)]
  have h := qgTheta_quadratic hρ0 hD₁ hD₂
  obtain ⟨h0, h1⟩ := qgTheta_mem hρ0 hρ1 hD₁ hD₂
  have hu : 0 < 1 - qgTheta ρ D₁ D₂ ^ 2 := by nlinarith
  have hd : 2 * ρ * √(D₁ * D₂) ≠ 0 := by positivity
  have e : qgTheta ρ D₁ D₂ * (2 * ρ * √(D₁ * D₂)) =
      √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂)) - (1 - ρ ^ 2) := div_mul_cancel₀ _ hd
  rw [qgR1, hphi]
  congr 1
  -- `1 - θ² = 2 a / (a + q)`.
  set t := qgTheta ρ D₁ D₂ with ht
  set q := √((1 - ρ ^ 2) ^ 2 + 4 * ρ ^ 2 * (D₁ * D₂))
  set s := √(D₁ * D₂)
  have hq : q = 2 * ρ * s * t + (1 - ρ ^ 2) := by linear_combination -e
  have hkey : (1 - t ^ 2) * ((1 - ρ ^ 2) + q) = 2 * (1 - ρ ^ 2) := by
    rw [hq]
    linear_combination (-2 * t) * h
  have hDD : 0 < D₁ * D₂ := mul_pos hD₁ hD₂
  rw [show 2 * D₁ * D₂ = 2 * (D₁ * D₂) by ring, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(D₁ * D₂)) * hkey

include hρ0 hρ1 hD₁ hD₂ in
/-- **Lecture 13, page 13-31.** At `θ*`, the two lower bounds coincide. The formula of the notes for
`R₂(θ)` has the square of `2 (1 + θ) + N`, which does not coincide with `R₁(θ*)`. -/
theorem qgR2_theta : qgR2 ρ D₁ D₂ (qgTheta ρ D₁ D₂) = qgR1 ρ D₁ D₂ (qgTheta ρ D₁ D₂) := by
  have hs : 0 < √(D₁ * D₂) := sqrt_pos.2 (mul_pos hD₁ hD₂)
  have ha : 0 < 1 - ρ ^ 2 := by nlinarith
  have hN : 0 < qgN ρ D₁ D₂ := div_pos ha (mul_pos hρ0 hs)
  have h := qgTheta_quadratic hρ0 hD₁ hD₂
  obtain ⟨h0, h1⟩ := qgTheta_mem hρ0 hρ1 hD₁ hD₂
  have hu : 0 < 1 - qgTheta ρ D₁ D₂ ^ 2 := by nlinarith
  -- `1 - θ² = N θ`.
  have hNθ : 1 - qgTheta ρ D₁ D₂ ^ 2 = qgN ρ D₁ D₂ * qgTheta ρ D₁ D₂ := by
    rw [qgN, div_mul_eq_mul_div, eq_div_iff (by positivity), h]
    ring
  rw [qgR2, qgR1]
  congr 1
  set t := qgTheta ρ D₁ D₂
  set N := qgN ρ D₁ D₂
  have h1t : 0 < 1 + t := by linarith
  have hDD : 0 < D₁ * D₂ := mul_pos hD₁ hD₂
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hk : (2 * (1 + t) + N) * (1 - t ^ 2) = N * (1 + t) ^ 2 := by
    linear_combination (2 * (1 + t)) * hNθ
  linear_combination ((1 - ρ ^ 2) * (D₁ * D₂)) * hk

include hρ0 hρ1 hD₁ hD₂ in
/-- **Lecture 13, pages 13-31 and 13-32.** `min_θ max {R₁(θ), R₂(θ)} = R((1 - ρ²) φ / (2 D₁ D₂))`:
for
every `θ ∈ (-1, 1)`, one of the two lower bounds is at least the sum rate of Theorem 3. -/
theorem qg_le_max (hθ0 : -1 < θ) (hθ1 : θ < 1) :
    qgR ((1 - ρ ^ 2) * qgPhi ρ D₁ D₂ / (2 * D₁ * D₂)) ≤ max (qgR1 ρ D₁ D₂ θ) (qgR2 ρ D₁ D₂ θ) := by
  have ha : 0 < 1 - ρ ^ 2 := by nlinarith
  have hs : 0 < √(D₁ * D₂) := sqrt_pos.2 (mul_pos hD₁ hD₂)
  have hN : 0 < qgN ρ D₁ D₂ := div_pos ha (mul_pos hρ0 hs)
  have hDD : 0 < D₁ * D₂ := mul_pos hD₁ hD₂
  obtain ⟨h0, h1⟩ := qgTheta_mem hρ0 hρ1 hD₁ hD₂
  have hmono : ∀ {x y : ℝ}, 0 < x → x ≤ y → qgR x ≤ qgR y := fun hx hxy => by
    simp only [qgR]
    have := log_le_log hx hxy
    linarith
  set t := qgTheta ρ D₁ D₂ with ht
  rcases le_total t θ with h | h
  · refine le_max_of_le_left ?_
    rw [← qgR1_theta hρ0 hρ1 hD₁ hD₂]
    have hθ2 : t ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ h0 h 2
    have hu : 0 < 1 - θ ^ 2 := by nlinarith
    refine hmono (by
      have : 0 < 1 - t ^ 2 := by linarith
      positivity) ?_
    refine div_le_div_of_nonneg_left ha.le (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hDD.le
  · refine le_max_of_le_right ?_
    rw [← qgR1_theta hρ0 hρ1 hD₁ hD₂, ← qgR2_theta hρ0 hρ1 hD₁ hD₂]
    have hv : 0 < 1 + θ := by linarith
    have hv' : 0 < 1 + t := by linarith
    refine hmono (by positivity) ?_
    set N := qgN ρ D₁ D₂
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : (2 * (1 + t) + N) * (1 + θ) ^ 2 ≤ (2 * (1 + θ) + N) * (1 + t) ^ 2 := by
      have hd : 0 ≤ t - θ := sub_nonneg.2 h
      nlinarith [mul_nonneg (mul_nonneg hv.le hv'.le) hd, mul_nonneg hN.le (mul_nonneg hd
        (add_pos hv hv').le)]
    have hc : 0 ≤ (1 - ρ ^ 2) * (N * (D₁ * D₂)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hk hc]

end Theta

/-! ### The test channel of case 2 and Lemma 5 -/

section Case

variable {ρ D₁ D₂ θ : ℝ}

/-- **Lecture 13, pages 13-22 and 13-23.** With `1 / Nⱼ = 1 / (Dⱼ (1 - θ²)) - 1 / (1 - ρ²)`, for the
root `θ`
of the quadratic equation, the sum rate of the left corner point is `R(|K_X| / |K(θ)|)`:
`((1 + N₁)(1 + N₂) - ρ²) / (N₁ N₂) = (1 - ρ²) / (D₁ D₂ (1 - θ²))`. -/
theorem qg_case2_sum {s A₁ A₂ : ℝ} (ha : 1 - ρ ^ 2 ≠ 0) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hs : s ^ 2 = D₁ * D₂) (hu : 1 - θ ^ 2 ≠ 0)
    (hθ : (1 - ρ ^ 2) * θ = ρ * s * (1 - θ ^ 2))
    (h₁ : A₁ = 1 / (D₁ * (1 - θ ^ 2)) - 1 / (1 - ρ ^ 2))
    (h₂ : A₂ = 1 / (D₂ * (1 - θ ^ 2)) - 1 / (1 - ρ ^ 2)) :
    (1 + A₁) * (1 + A₂) - ρ ^ 2 * (A₁ * A₂) = (1 - ρ ^ 2) / (D₁ * D₂ * (1 - θ ^ 2)) := by
  subst h₁ h₂
  have hDD : D₁ * D₂ ≠ 0 := mul_ne_zero hD₁ hD₂
  have h2 : (1 - ρ ^ 2) ^ 2 * θ ^ 2 = ρ ^ 2 * (D₁ * D₂) * (1 - θ ^ 2) ^ 2 := by
    rw [← hs]
    linear_combination ((1 - ρ ^ 2) * θ + ρ * s * (1 - θ ^ 2)) * hθ
  set u := 1 - θ ^ 2 with hu'
  set a := 1 - ρ ^ 2 with ha'
  have hρ : ρ ^ 2 = 1 - a := by rw [ha']; ring
  set x := 1 / (D₁ * u) with hx
  set y := 1 / (D₂ * u) with hy
  set b := 1 / a with hb
  have hxe : x * (D₁ * u) = 1 := by rw [hx]; field_simp
  have hye : y * (D₂ * u) = 1 := by rw [hy]; field_simp
  have hbe : b * a = 1 := by rw [hb]; field_simp
  have hz : a / (D₁ * D₂ * u) = a * (x * y * u) := by
    rw [hx, hy]
    field_simp
  rw [hz]
  -- `(1 + x - b)(1 + y - b) - ρ² (x - b)(y - b) = a x y - ρ² b`.
  have h3 : (1 + (x - b)) * (1 + (y - b)) - ρ ^ 2 * ((x - b) * (y - b)) =
      a * (x * y) - ρ ^ 2 * b := by
    rw [hρ]
    linear_combination (-(x + y + 1 - b)) * hbe
  -- `a x y θ² = ρ² b`.
  have h4 : a * (x * y) * θ ^ 2 = ρ ^ 2 * b := by
    have h5 : a * (x * y) * θ ^ 2 * (b * a) =
        ρ ^ 2 * (D₁ * D₂) * u ^ 2 * (x * y) * b := by
      rw [← h2]
      ring
    rw [hbe, mul_one] at h5
    rw [h5]
    have h6 : (D₁ * D₂) * u ^ 2 * (x * y) = 1 := by
      calc (D₁ * D₂) * u ^ 2 * (x * y) = (x * (D₁ * u)) * (y * (D₂ * u)) := by ring
        _ = 1 := by rw [hxe, hye, one_mul]
    calc ρ ^ 2 * (D₁ * D₂) * u ^ 2 * (x * y) * b = ρ ^ 2 * b * ((D₁ * D₂) * u ^ 2 * (x * y)) := by
          ring
      _ = ρ ^ 2 * b := by rw [h6, mul_one]
  rw [h3, ← h4, hu']
  ring

/-- **Lecture 13, page 13-30.** The Markov chain `X₁ → Y → X₂`: the conditional covariance of `X₁`
and `X₂`
given `Y = μ₁ X₁ + μ₂ X₂ + Z` vanishes for `N = (1 - ρ²) μ₁ μ₂ / ρ`. -/
theorem qg_markov {μ₁ μ₂ N : ℝ} (hρ : ρ ≠ 0) (hN : N = (1 - ρ ^ 2) * (μ₁ * μ₂) / ρ) :
    ρ * (μ₁ ^ 2 + 2 * ρ * (μ₁ * μ₂) + μ₂ ^ 2 + N) = (μ₁ + ρ * μ₂) * (ρ * μ₁ + μ₂) := by
  subst hN
  field_simp
  ring

/-- **Lecture 13, page 13-52.** `1 + θ - 2 α = N (1 + θ) / (2 (1 + θ) + N)`, for
`α = (1 + θ)² / (2 (1 + θ) + N)`. -/
theorem qg_alpha {N : ℝ} (h : 2 * (1 + θ) + N ≠ 0) :
    1 + θ - 2 * ((1 + θ) ^ 2 / (2 * (1 + θ) + N)) = N * (1 + θ) / (2 * (1 + θ) + N) := by
  have e : (1 + θ) ^ 2 / (2 * (1 + θ) + N) * (2 * (1 + θ) + N) = (1 + θ) ^ 2 :=
    div_mul_cancel₀ _ h
  rw [eq_div_iff h]
  linear_combination (-2 : ℝ) * e

/-- **Lecture 13, page 13-54, step 3 of Lemma 5.** If `b₁, b₂ ≥ 0` and `diag(b₁, b₂) ≼ [a c; c a]`,
then
`b₁ b₂ ≤ (a - c)²`. -/
theorem qg_lemma5_step3 {b₁ b₂ a c : ℝ} (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ b₂)
    (h : ∀ x y : ℝ, b₁ * x ^ 2 + b₂ * y ^ 2 ≤ a * x ^ 2 + 2 * c * (x * y) + a * y ^ 2) :
    b₁ * b₂ ≤ (a - c) ^ 2 := by
  have h3 := h 1 (-1)
  have h4 : b₁ + b₂ ≤ 2 * (a - c) := by nlinarith
  have h5 : 0 ≤ a - c := by linarith
  have h6 : (b₁ + b₂) ^ 2 ≤ (2 * (a - c)) ^ 2 := pow_le_pow_left₀ (by linarith) h4 2
  nlinarith [sq_nonneg (b₁ - b₂)]

end Case

/-! ### The Gaussian CEO problem -/

section CEO

variable {P D N₁ N₂ : ℝ}

/-- **The rate–distortion region of the Gaussian CEO problem (Lecture 13 of [elgamal2010], page
13-35)**, in
nats. -/
def ceoRegion (P N₁ N₂ D : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ r₁ r₂ : ℝ, 0 ≤ r₁ ∧ 0 ≤ r₂ ∧
    r₁ + 1 / 2 * log (1 / D) - 1 / 2 * log (1 / P + (1 - exp (-(2 * r₂))) / N₂) ≤ R.1 ∧
    r₂ + 1 / 2 * log (1 / D) - 1 / 2 * log (1 / P + (1 - exp (-(2 * r₁))) / N₁) ≤ R.2 ∧
    r₁ + r₂ + 1 / 2 * log (P / D) ≤ R.1 + R.2 ∧
    1 / D ≤ 1 / P + (1 - exp (-(2 * r₁))) / N₁ + (1 - exp (-(2 * r₂))) / N₂}

/-- **Lecture 13, page 13-38.** The bound of the converse in the two forms of the notes. -/
theorem ceo_bound_eq {x : ℝ} (hP : 0 < P) (hD : 0 < D) (hx : 0 ≤ x) :
    1 / 2 * log (P / D) - 1 / 2 * log (1 + P * x) = 1 / 2 * log (1 / D) - 1 / 2 * log (1 / P + x) :=
      by
  have h1 : 0 < 1 + P * x := by positivity
  have h2 : 0 < 1 / P + x := by positivity
  have e : 1 + P * x = P * (1 / P + x) := by
    field_simp
  rw [e, log_mul hP.ne' h2.ne', log_div hP.ne' hD.ne', log_div one_ne_zero hD.ne', log_one]
  ring

/-- **Lecture 13, page 13-35.** The Gaussian test channel of the achievability: `Uⱼ = Yⱼ + Vⱼ` with
noise
power `Q = N / (e^{2r} - 1)` has `I(Yⱼ; Uⱼ | X) = r` and the precision
`1 / (N + Q) = (1 - e^{-2r}) / N`. -/
theorem ceo_test_channel {N r : ℝ} (hN : 0 < N) (hr : 0 < r) :
    1 / (N + N / (exp (2 * r) - 1)) = (1 - exp (-(2 * r))) / N ∧
      1 / 2 * log (1 + N / (N / (exp (2 * r) - 1))) = r := by
  have h1 : 1 < exp (2 * r) := one_lt_exp_iff.2 (by positivity)
  have h2 : exp (2 * r) - 1 ≠ 0 := by linarith
  have h3 : exp (2 * r) ≠ 0 := (exp_pos _).ne'
  constructor
  · rw [exp_neg]
    field_simp
    ring
  · have e : 1 + N / (N / (exp (2 * r) - 1)) = exp (2 * r) := by
      field_simp
      ring
    rw [e, log_exp]
    ring

end CEO

end InfoTheory
