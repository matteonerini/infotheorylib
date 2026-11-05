/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.Gaussian

/-!
# The bounds on the capacity of the AWGN relay channel

Pages 17-31, 17-32, 17-48, 17-53 and 17-54 of the notes evaluate the cutset bound and the
decode–forward and compress–forward lower bounds for Gaussian input laws. The coding theorems for
Gaussian channels are not formalized; this file proves the closed forms of the expressions, which
are optimization problems over the correlation coefficient `ρ` and over the noise `N` of the
description.

## Main definitions

* `awgnMaxMin S S₂ c ρ`: the value `min {C(S + S₂ + 2 ρ √(S S₂)), C(c (1 - ρ²))}`.
* `awgnClosed S S₂ c`: the optimum of the problem, for `c ≥ S + S₂`.

## Main statements

* `isGreatest_awgnMaxMin_of_le`, `isGreatest_awgnMaxMin_of_ge`: the optimum over `ρ`.
* `awgn_cutset`, `awgn_decodeForward`: the closed forms of the cutset bound and of decode–forward.
* `awgn_cutset_notes_ne`: the formula of the cutset bound printed in the notes is a typo.
* `isGreatest_awgnCF`: the compress–forward bound, optimized over `N`.
* `isGreatest_rfdCF`: the compress–forward bound for the RFD channel.
* `rfd_cutset_eq`, `rfd_df_eq`, `rfd_df_eq_cutset`: the bounds for the RFD channel.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Set

@[expose] public noncomputable section

namespace InfoTheory

/-- The value of the expression of the cutset bound and of decode–forward, at the correlation
coefficient `ρ`. -/
def awgnMaxMin (S S₂ c ρ : ℝ) : ℝ :=
  min (gaussCap (S + S₂ + 2 * ρ * √(S * S₂))) (gaussCap (c * (1 - ρ ^ 2)))

/-- The optimum over `ρ`, for `c ≥ S + S₂`. -/
def awgnClosed (S S₂ c : ℝ) : ℝ := (√(S * (c - S₂)) + √(S₂ * (c - S))) ^ 2 / c

variable {S S₂ c : ℝ}

/-- **The optimum of the expression, for `c ≤ S + S₂`.** -/
theorem isGreatest_awgnMaxMin_of_ge (hc : 0 ≤ c) (h : c ≤ S + S₂) :
    IsGreatest (awgnMaxMin S S₂ c '' Icc 0 1) (gaussCap c) := by
  refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
  · simp only [awgnMaxMin]
    have h₀ : S + S₂ + 2 * 0 * √(S * S₂) = S + S₂ := by ring
    have h₁ : c * (1 - (0 : ℝ) ^ 2) = c := by ring
    rw [h₀, h₁]
    exact min_eq_right (gaussCap_le_gaussCap hc h)
  · rintro _ ⟨ρ, hρ, rfl⟩
    refine (min_le_right _ _).trans ?_
    have h₁ : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
    refine gaussCap_le_gaussCap (mul_nonneg hc h₁) ?_
    nlinarith [sq_nonneg ρ]

/-- **The optimum of the expression, for `c ≥ S + S₂`.** -/
theorem isGreatest_awgnMaxMin_of_le (hS : 0 ≤ S) (hS₂ : 0 ≤ S₂) (hc : 0 < c) (h : S + S₂ ≤ c) :
    IsGreatest (awgnMaxMin S S₂ c '' Icc 0 1) (gaussCap (awgnClosed S S₂ c)) := by
  have hcS : 0 ≤ c - S := by linarith
  have hcS₂ : 0 ≤ c - S₂ := by linarith
  set r := √(S * S₂) with hr
  set d := √((c - S) * (c - S₂)) with hd
  have hr0 : 0 ≤ r := sqrt_nonneg _
  have hd0 : 0 ≤ d := sqrt_nonneg _
  have hr2 : r ^ 2 = S * S₂ := sq_sqrt (mul_nonneg hS hS₂)
  have hd2 : d ^ 2 = (c - S) * (c - S₂) := sq_sqrt (mul_nonneg hcS hcS₂)
  have hrd : r ≤ d := by
    refine abs_le_of_sq_le_sq' ?_ hd0 |>.2
    rw [hr2, hd2]
    nlinarith
  have hdc : d ≤ c := by
    refine abs_le_of_sq_le_sq' ?_ hc.le |>.2
    rw [hd2]
    nlinarith
  set ρ₀ := (d - r) / c with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := div_nonneg (by linarith) hc.le
  have hρ₀1 : ρ₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
  have hcρ : c * ρ₀ = d - r := by
    rw [hρ₀]
    field_simp
  -- the two terms are equal at the optimum
  have hval : awgnClosed S S₂ c = S + S₂ + 2 * ρ₀ * r := by
    have hsq : √(S * (c - S₂)) * √(S₂ * (c - S)) = r * d := by
      rw [hr, hd, ← sqrt_mul (mul_nonneg hS hcS₂), ← sqrt_mul (mul_nonneg hS hS₂)]
      congr 1
      ring
    have h₁ : √(S * (c - S₂)) ^ 2 = S * (c - S₂) := sq_sqrt (mul_nonneg hS hcS₂)
    have h₂ : √(S₂ * (c - S)) ^ 2 = S₂ * (c - S) := sq_sqrt (mul_nonneg hS₂ hcS)
    rw [awgnClosed, div_eq_iff hc.ne']
    have : (S + S₂ + 2 * ρ₀ * r) * c = (S + S₂) * c + 2 * (c * ρ₀) * r := by ring
    rw [this, hcρ]
    nlinarith
  have hval₂ : c * (1 - ρ₀ ^ 2) = S + S₂ + 2 * ρ₀ * r := by
    have h₁ : c * ρ₀ ^ 2 = ρ₀ * (d - r) := by
      rw [← hcρ]
      ring
    have h₂ : (d - r) * (d + r) = c * (c - S - S₂) := by nlinarith
    have h₃ : ρ₀ * (d - r) + 2 * ρ₀ * r = ρ₀ * (d + r) := by ring
    have h₄ : c * (ρ₀ * (d + r)) = c * (c - S - S₂) := by
      rw [← mul_assoc, hcρ, h₂]
    have h₅ : ρ₀ * (d + r) = c - S - S₂ := mul_left_cancel₀ hc.ne' h₄
    nlinarith
  refine ⟨⟨ρ₀, ⟨hρ₀0, hρ₀1⟩, ?_⟩, ?_⟩
  · simp only [awgnMaxMin]
    rw [← hr, hval₂, hval, min_self]
  · rintro _ ⟨ρ, hρ, rfl⟩
    have hv0 : 0 ≤ awgnClosed S S₂ c := by
      rw [hval]
      have := mul_nonneg hρ₀0 hr0
      nlinarith
    rcases le_total ρ ρ₀ with hle | hle
    · refine (min_le_left _ _).trans (gaussCap_le_gaussCap ?_ ?_)
      · have := mul_nonneg hρ.1 hr0
        nlinarith
      · rw [hval]
        have := mul_le_mul_of_nonneg_right hle hr0
        linarith
    · refine (min_le_right _ _).trans (gaussCap_le_gaussCap ?_ ?_)
      · have h₁ : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
        exact mul_nonneg hc.le h₁
      · rw [hval, ← hval₂]
        refine mul_le_mul_of_nonneg_left ?_ hc.le
        nlinarith

variable {S₁ : ℝ}

/-- **Page 17-31 of [elgamal2010]: the cutset bound for the AWGN relay channel**, in the corrected
form: the term `√(S + S₁ - S₂)` of the notes should be `√(S (S + S₁ - S₂))`. -/
theorem awgn_cutset (hS : 0 ≤ S) (hS₂ : 0 ≤ S₂) (hpos : 0 < S + S₁) :
    IsGreatest (awgnMaxMin S S₂ (S + S₁) '' Icc 0 1)
      (if S₂ ≤ S₁ then gaussCap ((√(S₁ * S₂) + √(S * (S + S₁ - S₂))) ^ 2 / (S + S₁))
        else gaussCap (S + S₁)) := by
  by_cases h : S₂ ≤ S₁
  · rw [ite_eq_left h]
    have h₀ := isGreatest_awgnMaxMin_of_le hS hS₂ hpos (by linarith)
    have e : awgnClosed S S₂ (S + S₁) = (√(S₁ * S₂) + √(S * (S + S₁ - S₂))) ^ 2 / (S + S₁) := by
      simp only [awgnClosed]
      have e₁ : S₂ * (S + S₁ - S) = S₁ * S₂ := by ring
      rw [e₁, add_comm]
    rw [← e]
    exact h₀
  · rw [ite_eq_right h]
    push Not at h
    exact isGreatest_awgnMaxMin_of_ge hpos.le (by linarith)

/-- **Page 17-31 of [elgamal2010]: a typo in the cutset bound.** The closed form printed in the
  notes,
with `√(S + S₁ - S₂)` for `√(S (S + S₁ - S₂))`, is wrong: for `S = 4`, `S₁ = S₂ = 1` it gives
  `C(9/5)`,
while the optimum is `C(5)`. -/
theorem awgn_cutset_notes_ne :
    ¬ IsGreatest (awgnMaxMin 4 1 (4 + 1) '' Icc 0 1)
      (gaussCap ((√(1 * 1) + √(4 + 1 - 1)) ^ 2 / (4 + 1))) := by
  intro h
  have h₀ := awgn_cutset (S := 4) (S₁ := 1) (S₂ := 1) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left le_rfl] at h₀
  have huniq := h.unique h₀
  have e₁ : √((4 : ℝ) + 1 - 1) = 2 := by
    rw [show (4 : ℝ) + 1 - 1 = 2 ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  have e₂ : √((4 : ℝ) * (4 + 1 - 1)) = 4 := by
    rw [show (4 : ℝ) * (4 + 1 - 1) = 4 ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  have e₃ : √((1 : ℝ) * 1) = 1 := by simp
  rw [e₁, e₂, e₃] at huniq
  have hlt : gaussCap (((1 : ℝ) + 2) ^ 2 / (4 + 1)) < gaussCap (((1 : ℝ) + 4) ^ 2 / (4 + 1)) :=
    gaussCap_lt_gaussCap (by norm_num) (by norm_num)
  exact absurd huniq hlt.ne

/-- **Page 17-32 of [elgamal2010]: decode–forward for the AWGN relay channel.** -/
theorem awgn_decodeForward (hS : 0 ≤ S) (hS₂ : 0 ≤ S₂) (hS₁ : 0 < S₁) :
    IsGreatest (awgnMaxMin S S₂ S₁ '' Icc 0 1)
      (if S + S₂ ≤ S₁ then gaussCap (awgnClosed S S₂ S₁) else gaussCap S₁) := by
  by_cases h : S + S₂ ≤ S₁
  · rw [ite_eq_left h]
    exact isGreatest_awgnMaxMin_of_le hS hS₂ hS₁ h
  · rw [ite_eq_right h]
    push Not at h
    exact isGreatest_awgnMaxMin_of_ge hS₁.le h.le

/-- **Page 17-32 of [elgamal2010].** For `S₁ < S`, the decode–forward rate is lower than the
  capacity
`C(S)` of the direct channel. -/
theorem awgn_decodeForward_lt_direct (hS₂ : 0 ≤ S₂) (hS₁ : 0 ≤ S₁) (h : S₁ < S) :
    IsGreatest (awgnMaxMin S S₂ S₁ '' Icc 0 1) (gaussCap S₁) ∧ gaussCap S₁ < gaussCap S :=
  ⟨isGreatest_awgnMaxMin_of_ge hS₁ (by linarith), gaussCap_lt_gaussCap hS₁ h⟩

/-- **Pages 17-31 and 17-32 of [elgamal2010].** Multi-hop is at most non-coherent decode–forward,
  and
non-coherent decode–forward is decode–forward with `ρ = 0`. -/
theorem awgn_multihop_le_noncoherent (hS : 0 ≤ S) (hS₂ : 0 ≤ S₂) :
    min (gaussCap S₁) (gaussCap (S₂ / (S + 1))) ≤ min (gaussCap S₁) (gaussCap (S + S₂)) := by
  refine min_le_min le_rfl (gaussCap_le_gaussCap (by positivity) ?_)
  have h₁ : S₂ / (S + 1) ≤ S₂ := div_le_self hS₂ (by linarith)
  linarith

lemma awgn_noncoherent_eq (S S₂ S₁ : ℝ) :
    awgnMaxMin S S₂ S₁ 0 = min (gaussCap (S + S₂)) (gaussCap S₁) := by
  simp [awgnMaxMin]

/-! ### Compress–forward -/

/-- The expression of compress–forward, in terms of the noise `N` of the description. The constant
`T` is such that `C(T)` is the first term without the description. -/
def awgnCFExpr (T S S₁ N : ℝ) : ℝ := min (gaussCap T - gaussCap (1 / N)) (gaussCap (S + S₁ / (1 +
  N)))

variable {T : ℝ}

/-- **The optimization over the noise of the description.** -/
theorem isGreatest_awgnCFExpr (hS : 0 ≤ S) (hS₁ : 0 ≤ S₁) (hT : S < T) :
    IsGreatest (awgnCFExpr T S S₁ '' Ioi 0) (gaussCap (S + S₁ * (T - S) / (T + 1 + S₁))) := by
  have hT0 : 0 < T - S := by linarith
  have hd : 0 < T + 1 + S₁ := by linarith
  set N₀ := (1 + S + S₁) / (T - S) with hN₀
  have hN₀0 : 0 < N₀ := div_pos (by linarith) hT0
  have h₂ : S₁ / (1 + N₀) = S₁ * (T - S) / (T + 1 + S₁) := by
    rw [hN₀]
    field_simp
    ring
  have hv : 0 ≤ S + S₁ * (T - S) / (T + 1 + S₁) := by positivity
  have h₁ : gaussCap T - gaussCap (1 / N₀) = gaussCap (S + S₁ * (T - S) / (T + 1 + S₁)) := by
    simp only [gaussCap]
    rw [← mul_sub, ← log_div (by linarith) (by positivity)]
    congr 2
    rw [hN₀]
    field_simp
    ring
  refine ⟨⟨N₀, hN₀0, ?_⟩, ?_⟩
  · simp only [awgnCFExpr]
    rw [h₁, h₂, min_self]
  · rintro _ ⟨N, hN, rfl⟩
    have hN' : 0 < N := hN
    simp only [awgnCFExpr]
    rcases le_total N N₀ with hle | hle
    · refine (min_le_left _ _).trans ?_
      rw [← h₁]
      have : gaussCap (1 / N₀) ≤ gaussCap (1 / N) :=
        gaussCap_le_gaussCap (by positivity) (one_div_le_one_div_of_le hN' hle)
      linarith
    · refine (min_le_right _ _).trans ?_
      rw [← h₂]
      refine gaussCap_le_gaussCap (by positivity) ?_
      have : S₁ / (1 + N) ≤ S₁ / (1 + N₀) :=
        div_le_div_of_nonneg_left hS₁ (by positivity) (by linarith)
      linarith

/-- **Page 17-48 of [elgamal2010]: compress–forward for the AWGN relay channel.** With Gaussian
signals and `Ŷ₁ = Y₁ + Z'`, for `Z' ∼ N(0, N)`, the optimum over `N` is
`C(S + S₁ S₂ / (S + S₁ + S₂ + 1))`. -/
theorem isGreatest_awgnCF (hS : 0 ≤ S) (hS₁ : 0 ≤ S₁) (hS₂ : 0 < S₂) :
    IsGreatest (awgnCFExpr (S + S₂) S S₁ '' Ioi 0) (gaussCap (S + S₁ * S₂ / (S + S₁ + S₂ + 1))) :=
      by
  have h := isGreatest_awgnCFExpr (T := S + S₂) hS hS₁ (by linarith)
  have e₁ : S + S₂ - S = S₂ := by ring
  have e₂ : S + S₂ + 1 + S₁ = S + S₁ + S₂ + 1 := by ring
  rwa [e₁, e₂] at h

/-! ### The RFD relay channel -/

/-- `C(S) + C(S₂) = C(S + S₂ (S + 1))`. -/
lemma gaussCap_add_rfd (hS : 0 ≤ S) (hS₂ : 0 ≤ S₂) :
    gaussCap S + gaussCap S₂ = gaussCap (S + S₂ * (S + 1)) := by
  simp only [gaussCap]
  rw [← mul_add, ← log_mul (by linarith) (by linarith)]
  congr 2
  ring

/-- **Page 17-54 of [elgamal2010]: compress–forward for the RFD relay channel.** -/
theorem isGreatest_rfdCF (hS : 0 ≤ S) (hS₁ : 0 ≤ S₁) (hS₂ : 0 < S₂) :
    IsGreatest (awgnCFExpr (S + S₂ * (S + 1)) S S₁ '' Ioi 0)
      (gaussCap (S + S₁ * S₂ * (S + 1) / (S₁ + (S + 1) * (S₂ + 1)))) := by
  have hpos : 0 < S₂ * (S + 1) := by positivity
  have h := isGreatest_awgnCFExpr (T := S + S₂ * (S + 1)) hS hS₁ (by linarith)
  have e₁ : S₁ * (S + S₂ * (S + 1) - S) / (S + S₂ * (S + 1) + 1 + S₁) =
      S₁ * S₂ * (S + 1) / (S₁ + (S + 1) * (S₂ + 1)) := by
    congr 1 <;> ring
  rwa [e₁] at h

/-- **Page 17-53 of [elgamal2010]: the cutset bound for the RFD relay channel.** -/
theorem rfd_cutset_eq (hS : 0 ≤ S) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) :
    min (gaussCap S + gaussCap S₂) (gaussCap (S + S₁)) =
      if S₂ * (1 + S) ≤ S₁ then gaussCap (S + S₂ * (S + 1)) else gaussCap (S + S₁) := by
  rw [gaussCap_add_rfd hS hS₂]
  by_cases h : S₂ * (1 + S) ≤ S₁
  · rw [ite_eq_left h]
    exact min_eq_left (gaussCap_le_gaussCap (by positivity) (by linarith))
  · rw [ite_eq_right h]
    push Not at h
    exact min_eq_right (gaussCap_le_gaussCap (by positivity) (by linarith))

/-- **Page 17-54 of [elgamal2010]: decode–forward for the RFD relay channel.** -/
theorem rfd_df_eq (hS : 0 ≤ S) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) :
    min (gaussCap S + gaussCap S₂) (gaussCap S₁) =
      if S + S₂ * (S + 1) ≤ S₁ then gaussCap (S + S₂ * (S + 1)) else gaussCap S₁ := by
  rw [gaussCap_add_rfd hS hS₂]
  by_cases h : S + S₂ * (S + 1) ≤ S₁
  · rw [ite_eq_left h]
    exact min_eq_left (gaussCap_le_gaussCap (by positivity) h)
  · rw [ite_eq_right h]
    push Not at h
    exact min_eq_right (gaussCap_le_gaussCap hS₁ h.le)

/-- **Page 17-54 of [elgamal2010].** The bounds coincide if `S₁ ≥ S + S₂ (S + 1)`, and the value is
`C(S) + C(S₂)`. -/
theorem rfd_df_eq_cutset (hS : 0 ≤ S) (hS₂ : 0 ≤ S₂) (h : S + S₂ * (S + 1) ≤ S₁) :
    min (gaussCap S + gaussCap S₂) (gaussCap S₁) = gaussCap S + gaussCap S₂ ∧
      min (gaussCap S + gaussCap S₂) (gaussCap (S + S₁)) = gaussCap S + gaussCap S₂ := by
  rw [gaussCap_add_rfd hS hS₂]
  exact ⟨min_eq_left (gaussCap_le_gaussCap (by positivity) h),
    min_eq_left (gaussCap_le_gaussCap (by positivity) (by nlinarith))⟩

end InfoTheory
