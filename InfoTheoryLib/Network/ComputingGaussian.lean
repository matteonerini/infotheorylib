/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.QuadraticGaussian
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Gaussian computing: the formulas

This file proves the formulas of the Gaussian examples of Lecture 22 of [elgamal2010]: the reduction
of the `μ`-sum problem to the CEO problem, the sum rates of forwarding and local computing over a
cascade, and the bounds for distributed lossy averaging. As in Lecture 13, these are statements
about formulas: the library has no coding theorems for continuous sources.

## Main definitions

* `muS₁`, `muS₂`, `muDelta`, `muA₁`, `muA₂`, `muSumRegion`: the quantities of Theorem 3.
* `forwardingSum`, `localSum`: the sum rates of the two schemes on a cascade.

## Main statements

* `muSum_a_sq`, `muSum_mse`, `muSum_normalization`: the algebra of the reduction.
* `muSumRegion_eq_ceoRegion`: **Theorem 3** as the CEO region with distortion `D + δ`.
* `forwardingSum_ge`, `localSum_ge`, `localOpt_lt_forwardOpt`: local computing beats forwarding.
* `averaging_sum_ge`: the Jensen step of **Theorem 6**.
* `averaging_avg_distortion`: the distortion of the scheme of **Theorem 7**.
* `printed_averaging_counterexample`: the second inequality of Theorem 7 is false.
* `averaging_upper_le_add`: its correct form, with an additive gap.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The `μ`-sum problem -/

section MuSum

variable {ρ μ₁ μ₂ : ℝ}

/-- **Lecture 22 of [elgamal2010], page 22-15.** `s₁ = ρ (ρ + μ₁ / μ₂) / (1 - ρ²)`. -/
def muS₁ (ρ μ₁ μ₂ : ℝ) : ℝ := ρ * (ρ + μ₁ / μ₂) / (1 - ρ ^ 2)

/-- **Lecture 22 of [elgamal2010], page 22-15.** `s₂ = ρ (ρ + μ₂ / μ₁) / (1 - ρ²)`. -/
def muS₂ (ρ μ₁ μ₂ : ℝ) : ℝ := ρ * (ρ + μ₂ / μ₁) / (1 - ρ ^ 2)

/-- **Lecture 22 of [elgamal2010], page 22-15.** `δ = 1 / (1 + s₁ + s₂)`. -/
def muDelta (ρ μ₁ μ₂ : ℝ) : ℝ := 1 / (1 + muS₁ ρ μ₁ μ₂ + muS₂ ρ μ₁ μ₂)

/-- **Lecture 22 of [elgamal2010], page 22-17.** The solution `a₁ = μ₁ + ρ μ₂`. -/
def muA₁ (ρ μ₁ μ₂ : ℝ) : ℝ := μ₁ + ρ * μ₂

/-- **Lecture 22 of [elgamal2010], page 22-17.** The solution `a₂ = μ₂ + ρ μ₁`. -/
def muA₂ (ρ μ₁ μ₂ : ℝ) : ℝ := μ₂ + ρ * μ₁

/-- **Lecture 22, page 22-17.** `a₁` and `a₂` solve `X̃ = μᵀ Y`. -/
theorem muSum_a_solves (h1 : ρ ^ 2 ≠ 1) :
    (muA₁ ρ μ₁ μ₂ - ρ * muA₂ ρ μ₁ μ₂) / (1 - ρ ^ 2) = μ₁ ∧
      (muA₂ ρ μ₁ μ₂ - ρ * muA₁ ρ μ₁ μ₂) / (1 - ρ ^ 2) = μ₂ := by
  have h : 1 - ρ ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  simp only [muA₁, muA₂]
  constructor <;> field_simp <;> ring

section Normalized

variable (hρ : 0 < ρ) (hρ1 : ρ < 1) (h₁ : 0 < μ₁) (h₂ : 0 < μ₂)
  (hn : muA₁ ρ μ₁ μ₂ * muA₂ ρ μ₁ μ₂ = ρ)

include hρ hρ1 h₂ in
omit hρ hρ1 h₂ in
lemma muS₁_eq (hc : 1 - ρ ^ 2 ≠ 0) (h₂ : μ₂ ≠ 0) :
    muS₁ ρ μ₁ μ₂ = ρ * muA₁ ρ μ₁ μ₂ / (μ₂ * (1 - ρ ^ 2)) := by
  simp only [muS₁, muA₁]
  field_simp
  ring

omit hρ hρ1 h₂ in
lemma muS₂_eq (hc : 1 - ρ ^ 2 ≠ 0) (h₁ : μ₁ ≠ 0) :
    muS₂ ρ μ₁ μ₂ = ρ * muA₂ ρ μ₁ μ₂ / (μ₁ * (1 - ρ ^ 2)) := by
  simp only [muS₂, muA₂]
  field_simp
  ring

include hρ hρ1 h₁ h₂ hn in
/-- **Lecture 22, page 22-17.** `δ = μ₁ μ₂ (1 - ρ²) / ρ`. -/
theorem muDelta_eq : muDelta ρ μ₁ μ₂ = μ₁ * μ₂ * (1 - ρ ^ 2) / ρ := by
  have hc : 1 - ρ ^ 2 ≠ 0 := by nlinarith
  have hsum : 1 + muS₁ ρ μ₁ μ₂ + muS₂ ρ μ₁ μ₂ = ρ / (μ₁ * μ₂ * (1 - ρ ^ 2)) := by
    rw [muS₁_eq hc h₂.ne', muS₂_eq hc h₁.ne']
    have e : 1 + ρ * muA₁ ρ μ₁ μ₂ / (μ₂ * (1 - ρ ^ 2)) + ρ * muA₂ ρ μ₁ μ₂ / (μ₁ * (1 - ρ ^ 2)) =
        muA₁ ρ μ₁ μ₂ * muA₂ ρ μ₁ μ₂ / (μ₁ * μ₂ * (1 - ρ ^ 2)) := by
      simp only [muA₁, muA₂]
      field_simp
      ring
    rw [e, hn]
  rw [muDelta, hsum, one_div, inv_div]

include hρ hρ1 h₁ h₂ hn in
/-- **Lecture 22, page 22-17.** `a₁² = s₁ / (1 + s₁)` and `a₂² = s₂ / (1 + s₂)`. -/
theorem muSum_a_sq :
    muA₁ ρ μ₁ μ₂ ^ 2 = muS₁ ρ μ₁ μ₂ / (1 + muS₁ ρ μ₁ μ₂) ∧
      muA₂ ρ μ₁ μ₂ ^ 2 = muS₂ ρ μ₁ μ₂ / (1 + muS₂ ρ μ₁ μ₂) := by
  have hc : 1 - ρ ^ 2 ≠ 0 := by nlinarith
  have hc' : 0 < 1 - ρ ^ 2 := by nlinarith
  have ha₁ : 0 < muA₁ ρ μ₁ μ₂ := by simp only [muA₁]; positivity
  have ha₂ : 0 < muA₂ ρ μ₁ μ₂ := by simp only [muA₂]; positivity
  have e₁ : 1 + muS₁ ρ μ₁ μ₂ = muA₂ ρ μ₁ μ₂ / (μ₂ * (1 - ρ ^ 2)) := by
    rw [muS₁_eq hc h₂.ne']
    simp only [muA₁, muA₂]
    field_simp
    ring
  have e₂ : 1 + muS₂ ρ μ₁ μ₂ = muA₁ ρ μ₁ μ₂ / (μ₁ * (1 - ρ ^ 2)) := by
    rw [muS₂_eq hc h₁.ne']
    simp only [muA₁, muA₂]
    field_simp
    ring
  constructor
  · rw [e₁, muS₁_eq hc h₂.ne', div_div_div_cancel_right₀ (by positivity), eq_div_iff ha₂.ne']
    calc _ = muA₁ ρ μ₁ μ₂ * (muA₁ ρ μ₁ μ₂ * muA₂ ρ μ₁ μ₂) := by ring
      _ = _ := by rw [hn]; ring
  · rw [e₂, muS₂_eq hc h₁.ne', div_div_div_cancel_right₀ (by positivity), eq_div_iff ha₁.ne']
    calc _ = muA₂ ρ μ₁ μ₂ * (muA₁ ρ μ₁ μ₂ * muA₂ ρ μ₁ μ₂) := by ring
      _ = _ := by rw [hn]; ring

include hρ hρ1 h₁ h₂ hn in
/-- **Lecture 22, page 22-17.** The mean squared error of the MMSE estimate is `δ`. -/
theorem muSum_mse :
    1 - (muA₁ ρ μ₁ μ₂ ^ 2 + muA₂ ρ μ₁ μ₂ ^ 2 - 2 * ρ ^ 2) / (1 - ρ ^ 2) = muDelta ρ μ₁ μ₂ := by
  have hc : 1 - ρ ^ 2 ≠ 0 := by nlinarith
  rw [muDelta_eq hρ hρ1 h₁ h₂ hn]
  simp only [muA₁, muA₂] at hn ⊢
  field_simp
  linear_combination (-(1 + ρ ^ 2)) * hn

include hρ hρ1 h₁ h₂ hn in
/-- **Lecture 22, pages 22-15 and 22-17.** The normalization: `ρ = a₁ a₂` is equivalent to
`μ₁ μ₂ = ρ / ((ρ + μ₁ / μ₂) (ρ + μ₂ / μ₁))`, and this is also `μ₁ μ₂ = δ² s₁ s₂ / ρ`. -/
theorem muSum_normalization :
    μ₁ * μ₂ = ρ / ((ρ + μ₁ / μ₂) * (ρ + μ₂ / μ₁)) ∧
      μ₁ * μ₂ = muDelta ρ μ₁ μ₂ ^ 2 * muS₁ ρ μ₁ μ₂ * muS₂ ρ μ₁ μ₂ / ρ := by
  have hc : 1 - ρ ^ 2 ≠ 0 := by nlinarith
  constructor
  · have hpos : 0 < (ρ + μ₁ / μ₂) * (ρ + μ₂ / μ₁) := by positivity
    rw [eq_div_iff hpos.ne']
    simp only [muA₁, muA₂] at hn
    field_simp
    linear_combination hn
  · rw [muDelta_eq hρ hρ1 h₁ h₂ hn, muS₁_eq hc h₂.ne', muS₂_eq hc h₁.ne']
    field_simp
    linear_combination (-1 : ℝ) * hn

end Normalized

/-- **Theorem 3 of Lecture 22 of [elgamal2010], page 22-15.** The `μ`-sum rate–distortion region of
the theorem, in nats. -/
def muSumRegion (s₁ s₂ δ D : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ r₁ r₂ : ℝ, 0 ≤ r₁ ∧ 0 ≤ r₂ ∧
    r₁ + 1 / 2 * log (1 / (D + δ)) - 1 / 2 * log (1 + s₂ * (1 - exp (-(2 * r₂)))) ≤ R.1 ∧
    r₂ + 1 / 2 * log (1 / (D + δ)) - 1 / 2 * log (1 + s₁ * (1 - exp (-(2 * r₁)))) ≤ R.2 ∧
    r₁ + r₂ + 1 / 2 * log (1 / (D + δ)) ≤ R.1 + R.2 ∧
    1 / (D + δ) ≤ 1 + s₁ * (1 - exp (-(2 * r₁))) + s₂ * (1 - exp (-(2 * r₂)))}

/-- **Lecture 22, page 22-18.** The region of Theorem 3 is that of the CEO problem with the
observations `Yⱼ / aⱼ = X + Z̃ⱼ`, `Z̃ⱼ ∼ N(0, 1 / sⱼ)`, and with distortion `D + δ`. -/
theorem muSumRegion_eq_ceoRegion (s₁ s₂ δ D : ℝ) :
    muSumRegion s₁ s₂ δ D = ceoRegion 1 (1 / s₁) (1 / s₂) (D + δ) := by
  have e : ∀ s x : ℝ, x / (1 / s) = s * x := fun s x => by
    rw [div_div_eq_mul_div, div_one, mul_comm]
  ext R
  simp only [muSumRegion, ceoRegion, Set.mem_ofPred_eq, e, div_one]

end MuSum

/-! ### Cascade: forwarding and local computing -/

section Cascade

variable {D D₁ D₂ : ℝ}

/-- **Lecture 22 of [elgamal2010], page 22-27.** The sum rate `2 R(1 / D₁) + R(1 / D₂)` of
forwarding for two independent `WGN(1)` sources and the sum `X₁ + X₂`. -/
def forwardingSum (D₁ D₂ : ℝ) : ℝ := 2 * qgR (1 / D₁) + qgR (1 / D₂)

/-- **Lecture 22 of [elgamal2010], page 22-28.** The sum rate `R(1 / D₁) + R((2 - D₁) / D₂)` of
local computing. -/
def localSum (D₁ D₂ : ℝ) : ℝ := qgR (1 / D₁) + qgR ((2 - D₁) / D₂)

/-- **Lecture 22 of [elgamal2010], page 22-28.** The minimum `D₁* = 2 (1 - √(1 - D / 2))` of local
computing. -/
def localOptD (D : ℝ) : ℝ := 2 * (1 - √(1 - D / 2))

lemma forwardingSum_eq (h₁ : 0 < D₁) (h₂ : 0 < D₂) :
    forwardingSum D₁ D₂ = qgR (1 / (D₁ ^ 2 * D₂)) := by
  simp only [forwardingSum, qgR]
  rw [log_div one_ne_zero h₁.ne', log_div one_ne_zero h₂.ne', log_div one_ne_zero (by positivity),
    log_one, log_mul (by positivity) h₂.ne', log_pow]
  push_cast
  ring

lemma localSum_eq (h₁ : 0 < D₁) (h₁' : D₁ < 2) (h₂ : 0 < D₂) :
    localSum D₁ D₂ = qgR ((2 - D₁) / (D₁ * D₂)) := by
  have h : 0 < 2 - D₁ := by linarith
  simp only [localSum, qgR]
  rw [log_div one_ne_zero h₁.ne', log_div h.ne' h₂.ne', log_div h.ne' (by positivity),
    log_mul h₁.ne' h₂.ne', log_one]
  ring

/-- `qgR` is monotone. -/
lemma qgR_le_qgR {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : qgR x ≤ qgR y := by
  simp only [qgR]
  have := log_le_log hx h
  linarith

/-- **Lecture 22, page 22-27.** The sum rate of forwarding with `D₁ + D₂ ≤ D` is at least
`R(27 / (4 D³))`, with equality at `D₁ = 2 D₂ = 2 D / 3`. -/
theorem forwardingSum_ge (h₁ : 0 < D₁) (h₂ : 0 < D₂) (h : D₁ + D₂ ≤ D) :
    qgR (27 / (4 * D ^ 3)) ≤ forwardingSum D₁ D₂ := by
  have hD : 0 < D := by linarith
  rw [forwardingSum_eq h₁ h₂]
  refine qgR_le_qgR (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hk : D₁ ^ 2 * D₂ ≤ D₁ ^ 2 * (D - D₁) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith [mul_nonneg (sq_nonneg (3 * D₁ - 2 * D)) (by positivity : 0 ≤ 3 * D₁ + D)]

theorem forwardingSum_opt (hD : 0 < D) :
    forwardingSum (2 * D / 3) (D / 3) = qgR (27 / (4 * D ^ 3)) := by
  rw [forwardingSum_eq (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- The equation of `D₁*`. -/
lemma localOptD_eq (hD : D ≤ 2) : localOptD D ^ 2 - 4 * localOptD D + 2 * D = 0 := by
  have h : 0 ≤ 1 - D / 2 := by linarith
  have hs := sq_sqrt h
  simp only [localOptD]
  nlinarith

/-- **Lecture 22, page 22-28.** The sum rate of local computing with `D₁ + D₂ ≤ D` is at least
`R(1 / (2 (1 - √(1 - D / 2))²))`, with equality at `D₁ = D₁*`, `D₂ = D - D₁*`. -/
theorem localSum_ge (hD : D ≤ 2) (h₁ : 0 < D₁) (h₁' : D₁ < 2) (h₂ : 0 < D₂) (h : D₁ + D₂ ≤ D) :
    qgR (1 / (localOptD D ^ 2 / 2)) ≤ localSum D₁ D₂ := by
  have hD0 : 0 < D := by linarith
  have ht : 0 < localOptD D := by
    simp only [localOptD]
    have : √(1 - D / 2) < 1 := by
      rw [sqrt_lt' one_pos]
      linarith
    linarith
  have heq := localOptD_eq hD
  obtain ⟨T, hT⟩ : ∃ T, T = localOptD D := ⟨_, rfl⟩
  rw [← hT] at heq ht ⊢
  rw [localSum_eq h₁ h₁' h₂]
  have h2 : 0 < 2 - D₁ := by linarith
  refine qgR_le_qgR (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hk : D₁ * D₂ ≤ D₁ * (D - D₁) := mul_le_mul_of_nonneg_left (by linarith) h₁.le
  have hD' : D = (4 * T - T ^ 2) / 2 := by linarith
  have hkey : D₁ * (D - D₁) ≤ T ^ 2 / 2 * (2 - D₁) := by
    rw [hD']
    nlinarith [sq_nonneg (D₁ - T)]
  linarith

theorem localSum_opt (hD : 0 < D) (hD2 : D < 2) :
    localSum (localOptD D) (D - localOptD D) = qgR (1 / (localOptD D ^ 2 / 2)) := by
  have heq := localOptD_eq hD2.le
  have hs : 0 < √(1 - D / 2) := sqrt_pos.2 (by linarith)
  have hs1 : √(1 - D / 2) < 1 := by
    rw [sqrt_lt' one_pos]
    linarith
  have ht : 0 < localOptD D := by simp only [localOptD]; linarith
  have ht2 : localOptD D < 2 := by simp only [localOptD]; linarith
  obtain ⟨T, hT⟩ : ∃ T, T = localOptD D := ⟨_, rfl⟩
  rw [← hT] at heq ht ht2 ⊢
  have hD' : D - T = T * (2 - T) / 2 := by nlinarith
  have hpos : 0 < D - T := by
    rw [hD']
    have : 0 < 2 - T := by linarith
    positivity
  rw [localSum_eq ht ht2 hpos, hD']
  congr 1
  have : 2 - T ≠ 0 := by linarith
  field_simp

/-- **Lecture 22, page 22-28.** `R*_l < R*_f` for `D ∈ (0, 1]`: local computing outperforms
forwarding. -/
theorem localOpt_lt_forwardOpt (hD : 0 < D) (hD1 : D ≤ 1) :
    qgR (1 / (localOptD D ^ 2 / 2)) < qgR (27 / (4 * D ^ 3)) := by
  have heq := localOptD_eq (by linarith : D ≤ 2)
  have hs1 : √(1 - D / 2) < 1 := by
    rw [sqrt_lt' one_pos]
    linarith
  have hs2 : 1 / 2 < √(1 - D / 2) := by
    rw [lt_sqrt (by norm_num)]
    linarith
  have ht : 0 < localOptD D := by simp only [localOptD]; linarith
  have ht1 : localOptD D < 1 := by simp only [localOptD]; linarith
  obtain ⟨T, hT⟩ : ∃ T, T = localOptD D := ⟨_, rfl⟩
  rw [← hT] at heq ht ht1 ⊢
  have hD' : D = T * (4 - T) / 2 := by nlinarith
  simp only [qgR]
  refine mul_lt_mul_of_pos_left (log_lt_log (by positivity) ?_) (by norm_num)
  rw [div_lt_div_iff₀ (by positivity) (by positivity), hD']
  -- with `T = 2 t`, this is `27 > 16 t (2 - t)³`
  have hk : 0 < (T - 1) ^ 2 * (T ^ 2 - 10 * T + 27) := by
    have h1 : 0 < (T - 1) ^ 2 := by
      have : T - 1 ≠ 0 := by linarith
      positivity
    have h2 : 0 < T ^ 2 - 10 * T + 27 := by nlinarith
    positivity
  have hT2 : 0 < T ^ 2 := by positivity
  nlinarith [mul_pos hT2 hk]

end Cascade

/-! ### Distributed lossy averaging -/

section Averaging

/-- **Theorem 6 of Lecture 22, page 22-43: the Jensen step.** For `(1 / N) ∑ Dⱼ ≤ D`,
`∑ⱼ R(c / Dⱼ) ≥ N R(c / D)`. -/
theorem averaging_sum_ge {N : ℕ} (hN : 0 < N) {c D : ℝ} (hc : 0 < c) {Dj : Fin N → ℝ}
    (hDj : ∀ j, 0 < Dj j) (hD : (∑ j, Dj j) / N ≤ D) :
    N * qgR (c / D) ≤ ∑ j, qgR (c / Dj j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hmean : 0 < (∑ j, Dj j) / N := div_pos (sum_pos (fun j _ => hDj j) univ_nonempty) hN'
  have hD0 : 0 < D := hmean.trans_le hD
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := (univ : Finset (Fin N)))
    (w := fun _ => (N : ℝ)⁻¹) (p := Dj) (fun _ _ => by positivity)
    (by simp [hN'.ne']) (fun j _ => hDj j)
  simp only [smul_eq_mul, ← mul_sum] at hj
  have hm : (N : ℝ)⁻¹ * ∑ j, Dj j = (∑ j, Dj j) / N := by ring
  rw [hm] at hj
  have hlog := log_le_log hmean hD
  have e : ∑ j, qgR (c / Dj j) = 1 / 2 * (N * log c - ∑ j, log (Dj j)) := by
    simp only [qgR]
    rw [← mul_sum, sum_congr rfl fun j _ => log_div hc.ne' (hDj j).ne', sum_sub_distrib]
    simp
  rw [e, qgR, log_div hc.ne' hD0.ne']
  have hmul := mul_le_mul_of_nonneg_left (hj.trans hlog) hN'.le
  rw [← mul_assoc, mul_inv_cancel₀ hN'.ne', one_mul] at hmul
  nlinarith

/-- **Lecture 22, page 22-45.** The distortion of the scheme of Theorem 7: with distortions `D'` on
the links, `D₁ = (N - 1) D' / N²` and `Dⱼ ≤ (2 N - 3) D' / N²`, the average is at most
`2 (N - 1)² D' / N³`. -/
theorem averaging_avg_distortion {N D' : ℝ} (hN : N ≠ 0) :
    (1 / N) * ((N - 1) / N ^ 2 * D' + (N - 1) * ((2 * N - 3) / N ^ 2 * D')) =
      2 * (N - 1) ^ 2 / N ^ 3 * D' := by
  field_simp
  ring

/-- **Lecture 22, page 22-31.** The estimate `X_j / N` has the distortion `(N - 1) / N²`, as
`Z - X_j / N` is the sum of `N - 1` independent variables of variance `1 / N²`. -/
theorem averaging_zero_rate {N : ℝ} (hN : N ≠ 0) : (N - 1) * (1 / N) ^ 2 = (N - 1) / N ^ 2 := by
  field_simp

/-- **The second inequality of Theorem 7 (page 22-32) is false.** The notes claim
`2 (N - 1) R(2 (N - 1)² / (N³ D)) ≤ 2 N R((N - 1) / (N² D))` for `D < (N - 1) / N²`, so that the
cutset bound is achievable within a factor of 2. For `N = 3` and `D = 1 / 5 < 2 / 9`, this is
`2 log (40 / 27) ≤ 3 log (10 / 9)`, which fails. -/
theorem printed_averaging_counterexample :
    (1 / 5 : ℝ) < (3 - 1) / 3 ^ 2 ∧
      ¬ (2 * (3 - 1) * qgR (2 * (3 - 1) ^ 2 / (3 ^ 3 * (1 / 5))) ≤
        2 * 3 * qgR ((3 - 1) / (3 ^ 2 * (1 / 5))) : Prop) := by
  refine ⟨by norm_num, fun h => ?_⟩
  simp only [qgR] at h
  have e₁ : (2 : ℝ) * (3 - 1) ^ 2 / (3 ^ 3 * (1 / 5)) = 40 / 27 := by norm_num
  have e₂ : ((3 : ℝ) - 1) / (3 ^ 2 * (1 / 5)) = 10 / 9 := by norm_num
  rw [e₁, e₂] at h
  have h₁ : 2 * log (40 / 27 : ℝ) ≤ 3 * log (10 / 9 : ℝ) := by linarith
  have h₂ : log ((40 / 27 : ℝ) ^ 2) ≤ log ((10 / 9 : ℝ) ^ 3) := by
    rw [log_pow, log_pow]
    push_cast
    exact h₁
  have := (log_le_log_iff (by positivity) (by positivity)).1 h₂
  norm_num at this

/-- **The correct form of the second inequality of Theorem 7.** The upper bound of the scheme is
within a factor of 2 of the cutset bound up to an additive gap of `(N - 1) log 2`:
`2 (N - 1) R(2 (N - 1)² / (N³ D)) ≤ 2 N R((N - 1) / (N² D)) + (N - 1) log 2`, for `N ≥ 1` and
`0 < D ≤ (N - 1) / N²`. -/
theorem averaging_upper_le_add {N D : ℝ} (hN : 1 < N) (hD : 0 < D) (hDt : D ≤ (N - 1) / N ^ 2) :
    2 * (N - 1) * qgR (2 * (N - 1) ^ 2 / (N ^ 3 * D)) ≤
      2 * N * qgR ((N - 1) / (N ^ 2 * D)) + (N - 1) * log 2 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  obtain ⟨c, hc⟩ : ∃ c, c = (N - 1) / (N ^ 2 * D) := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    rw [hc, one_le_div (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hDt
    linarith
  have hc0 : 0 < c := by linarith
  have ha : 0 < 2 * (N - 1) / N := by positivity
  have ha2 : 2 * (N - 1) / N ≤ 2 := by
    rw [div_le_iff₀ hN0]
    linarith
  have e : 2 * (N - 1) ^ 2 / (N ^ 3 * D) = 2 * (N - 1) / N * c := by
    rw [hc]
    field_simp
  rw [e, ← hc]
  simp only [qgR]
  rw [log_mul ha.ne' hc0.ne']
  have h₁ : log (2 * (N - 1) / N) ≤ log 2 := log_le_log ha ha2
  have h₂ : 0 ≤ log c := log_nonneg hc1
  nlinarith [mul_le_mul_of_nonneg_left h₁ hN1.le, mul_nonneg hN1.le h₂]

end Averaging

end InfoTheory
