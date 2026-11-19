/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Combinatorial bounds on entropy

Tight bounds on binomial coefficients (Lemma 17.5.1, after Wozencraft and Reiffen): for `0 < k < n`
and `p = k/n`, `1/√(8npq) ≤ C(n, k) e^{-n H(p)} ≤ 1/√(πnpq)`, where `q = 1 - p` and `H` is the
binary entropy in nats.

Write `sₙ = n!/(√(2n) (n/e)ⁿ)` for Mathlib's Stirling sequence. Then
`C(n, k) pᵏ q^{n-k} = sₙ/(sₖ s_{n-k}) · 1/√(2npq)`, and the bounds follow from
`√π ≤ sₙ ≤ s₁ = e/√2` and the values `s₂ = e²/4`, `s₃ = √6 e³/27`.

## Main statements

* `choose_mul_pow_mul_stirlingSeq`: `C(k + m, k) pᵏ qᵐ sₖ sₘ · 2√k√m = s_{k+m} √2 √(k+m)`.
* `stirlingSeq_mul_le`: `sₖ sₘ ≤ 2 s_{k+m}` for `k, m ≥ 1`.
* `choose_mul_pow_le`, `le_choose_mul_pow`: **Lemma 17.5.1, (17.41)**, for
  `C(n, k) pᵏ q^{n-k}`.
* `choose_mul_exp_binEntropy_le`, `le_choose_mul_exp_binEntropy`: **Lemma 17.5.1** with
  `e^{-n H(p)} = pᵏ q^{n-k}`.

## Implementation notes

The book states the lemma with `2^{-nH(p)}` and `H` in bits, which is the same as `e^{-nH(p)}`
with `H` in nats. The proof uses the monotonicity of the Stirling sequence instead of the
book's explicit form (17.42) of Stirling's approximation.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 17.5
-/

open Real Nat Stirling

@[expose] public noncomputable section

namespace InfoTheory

/-- `sₙ ≤ s₁ = e/√2` for `n ≥ 1`. -/
lemma stirlingSeq_le_exp_one_div_sqrt_two {n : ℕ} (hn : 1 ≤ n) : stirlingSeq n ≤ exp 1 / √2 := by
  obtain ⟨n, rfl⟩ := exists_add_of_le hn
  rw [← stirlingSeq_one, add_comm]
  exact stirlingSeq'_antitone (Nat.zero_le n)

/-- `sₙ ≤ sₘ` for `1 ≤ m ≤ n`. -/
lemma stirlingSeq_le_of_le {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : stirlingSeq n ≤ stirlingSeq m := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hm
  obtain ⟨n, rfl⟩ := exists_add_of_le (hm.trans h)
  rw [add_comm 1 m, add_comm 1 n]
  exact stirlingSeq'_antitone (by omega : m ≤ n)

lemma stirlingSeq_two : stirlingSeq 2 = exp 1 ^ 2 / 4 := by
  rw [stirlingSeq, show √(2 * ((2 : ℕ) : ℝ)) = 2 by
    rw [show 2 * ((2 : ℕ) : ℝ) = 2 ^ 2 by norm_num]; exact sqrt_sq zero_le_two]
  have := exp_pos 1
  simp only [factorial, Nat.cast_ofNat]
  field_simp
  norm_num

lemma stirlingSeq_three : stirlingSeq 3 = √6 * exp 1 ^ 3 / 27 := by
  rw [stirlingSeq, show 2 * ((3 : ℕ) : ℝ) = 6 by norm_num]
  have := exp_pos 1
  have h6 : √6 * √6 = 6 := mul_self_sqrt (by norm_num)
  have h6' : 0 < √6 := sqrt_pos.2 (by norm_num)
  simp only [factorial, Nat.cast_ofNat]
  field_simp
  norm_num

lemma sqrt_pi_gt : 1.772 < √π := by
  rw [lt_sqrt (by norm_num)]
  linarith [pi_gt_d2]

/-- `C(k + m, k) pᵏ qᵐ sₖ sₘ · 2√k√m = s_{k+m} √2 √(k+m)`, with `p = k/(k+m)` and
`q = m/(k+m)`. -/
theorem choose_mul_pow_mul_stirlingSeq {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    ((k + m).choose k * ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m) *
        stirlingSeq k * stirlingSeq m * (2 * √k * √m) =
      stirlingSeq (k + m) * √2 * √((k : ℝ) + m) := by
  have he := exp_pos 1
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (0 : ℝ) < k + m := by positivity
  -- `j! = sⱼ √2 √j (j/e)ʲ`.
  have hfac : ∀ j : ℕ, 0 < j →
      (j ! : ℝ) = stirlingSeq j * (√2 * √j) * ((j : ℝ) / exp 1) ^ j := by
    intro j hj
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    have : 0 < √(2 * (j : ℝ)) := sqrt_pos.2 (by positivity)
    rw [stirlingSeq, ← sqrt_mul zero_le_two]
    field_simp
  have hC : ((k + m) ! : ℝ) = (k + m).choose k * k ! * m ! := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k m)
    rw [Nat.add_sub_cancel_left] at this
    exact_mod_cast this.symm
  rw [hfac k hk, hfac m hm, hfac (k + m) (by omega)] at hC
  push_cast at hC
  have hpow : ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m *
      (((k : ℝ) + m) / exp 1) ^ (k + m) = ((k : ℝ) / exp 1) ^ k * ((m : ℝ) / exp 1) ^ m := by
    rw [pow_add, show (k : ℝ) / exp 1 = k / (k + m) * ((k + m) / exp 1) by field_simp,
      show (m : ℝ) / exp 1 = m / (k + m) * ((k + m) / exp 1) by field_simp, mul_pow, mul_pow]
    ring
  have h2 : √2 * √2 = 2 := mul_self_sqrt zero_le_two
  have hX : (((k : ℝ) + m) / exp 1) ^ (k + m) ≠ 0 := by positivity
  refine mul_right_cancel₀ hX ?_
  linear_combination ((k + m).choose k * stirlingSeq k * stirlingSeq m * 2 * √k * √m) * hpow -
    ((k + m).choose k * stirlingSeq k * stirlingSeq m * √k * √m * ((k : ℝ) / exp 1) ^ k *
      ((m : ℝ) / exp 1) ^ m) * h2 - hC

/-- `sₖ sₘ ≤ 2 s_{k+m}` for `k, m ≥ 1`. -/
theorem stirlingSeq_mul_le {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    stirlingSeq k * stirlingSeq m ≤ 2 * stirlingSeq (k + m) := by
  wlog hkm : k ≤ m generalizing k m
  · rw [mul_comm, add_comm]
    exact this hm hk (by omega)
  have hs : ∀ j, 1 ≤ j → 0 ≤ stirlingSeq j := fun j hj =>
    (sqrt_nonneg π).trans (sqrt_pi_le_stirlingSeq (by omega))
  have he1 := exp_one_lt_d9
  have he2 := exp_one_gt_d9
  have hpi := sqrt_pi_gt
  have hr2 : 1.41421 < √2 := by rw [lt_sqrt (by norm_num)]; norm_num
  have hr6 : 2.4494 < √6 := by rw [lt_sqrt (by norm_num)]; norm_num
  have hr6' : √6 < 2.44949 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs1 : stirlingSeq 1 < 1.9222 := by
    rw [stirlingSeq_one, div_lt_iff₀ (by positivity)]; nlinarith
  have hN := sqrt_pi_le_stirlingSeq (n := k + m) (by omega)
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | hm3
    · -- `s₁² = e²/2 = 2 s₂`.
      rw [stirlingSeq_one, show 1 + 1 = 2 from rfl, stirlingSeq_two,
        show exp 1 / √2 * (exp 1 / √2) = exp 1 ^ 2 / (√2 * √2) by ring,
        mul_self_sqrt zero_le_two]
      linarith
    · -- `s₁ s₂ ≤ 2 s₃`.
      rw [show 1 + 2 = 3 from rfl, stirlingSeq_three, stirlingSeq_two]
      have hs1' : 0 ≤ stirlingSeq 1 := hs 1 le_rfl
      have he2l : 7.389056 < exp 1 ^ 2 := by nlinarith
      have he3 : 20.0855 < exp 1 ^ 3 := by rw [pow_succ]; nlinarith
      have he2' : exp 1 ^ 2 < 7.38906 := by nlinarith
      nlinarith
    · -- `s₁ sₘ ≤ s₁ s₃ < 2√π`.
      have h3 := stirlingSeq_le_of_le (by norm_num) hm3
      rw [stirlingSeq_three] at h3
      have he2u : exp 1 ^ 2 < 7.38906 := by nlinarith
      have he3 : exp 1 ^ 3 < 20.0856 := by rw [pow_succ]; nlinarith
      have hs1' : 0 ≤ stirlingSeq 1 := hs 1 le_rfl
      have hsm : 0 ≤ stirlingSeq m := hs m (by omega)
      have : stirlingSeq m < 1.8223 := by nlinarith
      nlinarith
  · -- `sₖ sₘ ≤ s₂² = e⁴/16 < 2√π`.
    have h2k := stirlingSeq_le_of_le (by norm_num) hk2
    have h2m := stirlingSeq_le_of_le (by norm_num) (hk2.trans hkm)
    rw [stirlingSeq_two] at h2k h2m
    have he4 : exp 1 ^ 2 < 7.38906 := by nlinarith
    have hsk := hs k (by omega)
    have hsm := hs m (by omega)
    have : stirlingSeq k < 1.8473 := by linarith
    have : stirlingSeq m < 1.8473 := by linarith
    nlinarith

/-- The algebraic part of Lemma 17.5.1: `√(c npq) = √c √k √m / √n` for `p = k/n`, `q = m/n` and
`n = k + m`. -/
lemma sqrt_mul_npq {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {c : ℝ} (hc : 0 ≤ c) :
    √(c * ((k : ℝ) + m) * (k / (k + m)) * (m / (k + m))) = √c * √k * √m / √((k : ℝ) + m) := by
  have hN : (0 : ℝ) < k + m := by positivity
  rw [show c * ((k : ℝ) + m) * (k / (k + m)) * (m / (k + m)) = c * k * m / (k + m) by
    field_simp, sqrt_div' _ hN.le, sqrt_mul (by positivity), sqrt_mul hc]

/-- **Lemma 17.5.1, (17.41), upper bound.** For `p = k/n`, `q = m/n` and `n = k + m` with
`k, m > 0`, `C(n, k) pᵏ qᵐ ≤ 1/√(π npq)`. -/
theorem choose_mul_pow_le' {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    (k + m).choose k * ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m ≤
      1 / √(π * ((k : ℝ) + m) * (k / (k + m)) * (m / (k + m))) := by
  set A := (k + m).choose k * ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m
  have hid := choose_mul_pow_mul_stirlingSeq hk hm
  rw [sqrt_mul_npq hk hm pi_pos.le, one_div_div,
    le_div_iff₀ (by have := sqrt_pos.2 pi_pos; positivity)]
  have hsk := sqrt_pi_le_stirlingSeq (n := k) (by omega)
  have hsm := sqrt_pi_le_stirlingSeq (n := m) (by omega)
  have hpi : √π * √π = π := mul_self_sqrt pi_pos.le
  have hσ : π ≤ stirlingSeq k * stirlingSeq m := by
    rw [← hpi]; exact mul_le_mul hsk hsm (sqrt_nonneg _) ((sqrt_nonneg _).trans hsk)
  have hN : stirlingSeq (k + m) * √2 ≤ exp 1 := by
    have := stirlingSeq_le_exp_one_div_sqrt_two (n := k + m) (by omega)
    rwa [le_div_iff₀ (sqrt_pos.2 two_pos)] at this
  have he : exp 1 * √π ≤ 2 * π := by
    have := sqrt_pi_gt
    have := exp_one_lt_d9
    nlinarith
  have hc : 0 ≤ √((k : ℝ) + m) := sqrt_nonneg _
  have hab : 0 < √(k : ℝ) * √(m : ℝ) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hσ0 : 0 < stirlingSeq k * stirlingSeq m := (pi_pos.trans_le hσ)
  -- `A √π √k √m · 2σ = s_{k+m} √2 √π √(k+m) ≤ e √π √(k+m) ≤ 2π √(k+m) ≤ 2σ √(k+m)`.
  have key : A * (√π * √k * √m) * (2 * (stirlingSeq k * stirlingSeq m)) =
      stirlingSeq (k + m) * √2 * √π * √((k : ℝ) + m) := by
    linear_combination √π * hid
  have : A * (√π * √k * √m) * (2 * (stirlingSeq k * stirlingSeq m)) ≤
      √((k : ℝ) + m) * (2 * (stirlingSeq k * stirlingSeq m)) := by
    rw [key]
    calc stirlingSeq (k + m) * √2 * √π * √((k : ℝ) + m)
        ≤ exp 1 * √π * √((k : ℝ) + m) := by gcongr
      _ ≤ 2 * π * √((k : ℝ) + m) := by gcongr
      _ ≤ _ := by nlinarith
  exact le_of_mul_le_mul_right this (by positivity)

/-- **Lemma 17.5.1, (17.41), lower bound.** For `p = k/n`, `q = m/n` and `n = k + m` with
`k, m > 0`, `1/√(8npq) ≤ C(n, k) pᵏ qᵐ`. -/
theorem le_choose_mul_pow' {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    1 / √(8 * ((k : ℝ) + m) * (k / (k + m)) * (m / (k + m))) ≤
      (k + m).choose k * ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m := by
  set A := (k + m).choose k * ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m
  have hid := choose_mul_pow_mul_stirlingSeq hk hm
  have h8 : √8 = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, sqrt_mul (by norm_num), sqrt_sq zero_le_two]
  have hab : 0 < √(k : ℝ) * √(m : ℝ) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hr2 : 0 < √2 := sqrt_pos.2 two_pos
  rw [sqrt_mul_npq hk hm (by norm_num), one_div_div, h8, div_le_iff₀ (by positivity)]
  have h2 : √2 * √2 = 2 := mul_self_sqrt zero_le_two
  have hsk := sqrt_pi_le_stirlingSeq (n := k) (by omega)
  have hsm := sqrt_pi_le_stirlingSeq (n := m) (by omega)
  have hσ0 : 0 < stirlingSeq k * stirlingSeq m :=
    mul_pos ((sqrt_pos.2 pi_pos).trans_le hsk) ((sqrt_pos.2 pi_pos).trans_le hsm)
  have hσ := stirlingSeq_mul_le (k := k) (m := m) (by omega) (by omega)
  -- `A · 2√2 √k √m · σ = 2 s_{k+m} √(k+m) ≥ σ √(k+m)`.
  have key : A * (2 * √2 * √k * √m) * (stirlingSeq k * stirlingSeq m) =
      2 * stirlingSeq (k + m) * √((k : ℝ) + m) := by
    linear_combination √2 * hid + stirlingSeq (k + m) * √((k : ℝ) + m) * h2
  refine le_of_mul_le_mul_right ?_ hσ0
  rw [key]
  have hc : 0 ≤ √((k : ℝ) + m) := sqrt_nonneg _
  nlinarith

/-- `e^{-n H(p)} = pᵏ qᵐ` for `p = k/n`, `q = m/n` and `n = k + m`, with `H` the binary
entropy in nats. -/
lemma exp_neg_binEntropy {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    exp (-(((k : ℝ) + m) * binEntropy (k / (k + m)))) =
      ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (0 : ℝ) < k + m := by positivity
  have hq : 1 - (k : ℝ) / (k + m) = m / (k + m) := by field_simp; ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, hq, negMulLog, negMulLog]
  rw [show -(((k : ℝ) + m) * (-(k / (k + m)) * Real.log (k / (k + m)) +
      -(m / (k + m)) * Real.log (m / (k + m)))) =
      k * Real.log (k / (k + m)) + m * Real.log (m / (k + m)) by field_simp; ring,
    exp_add, exp_natCast_mul, exp_natCast_mul, exp_log (by positivity), exp_log (by positivity)]

/-- **Lemma 17.5.1, (17.41), upper bound.** For `0 < k < n` and `p = k/n`, `q = 1 - p`,
`C(n, k) pᵏ q^{n-k} ≤ 1/√(π npq)`. -/
theorem choose_mul_pow_le {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    n.choose k * ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) ≤
      1 / √(π * n * (k / n) * (1 - k / n)) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hkn.le
  have hm : 0 < m := by omega
  have hq : 1 - (k : ℝ) / (k + m) = m / (k + m) := by field_simp; ring
  push_cast
  rw [Nat.add_sub_cancel_left, hq]
  exact choose_mul_pow_le' hk hm

/-- **Lemma 17.5.1, (17.41), lower bound.** For `0 < k < n` and `p = k/n`, `q = 1 - p`,
`1/√(8npq) ≤ C(n, k) pᵏ q^{n-k}`. -/
theorem le_choose_mul_pow {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    1 / √(8 * n * (k / n) * (1 - k / n)) ≤
      n.choose k * ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hkn.le
  have hm : 0 < m := by omega
  have hq : 1 - (k : ℝ) / (k + m) = m / (k + m) := by field_simp; ring
  push_cast
  rw [Nat.add_sub_cancel_left, hq]
  exact le_choose_mul_pow' hk hm

/-- **Lemma 17.5.1, (17.41)**, with the binary entropy: for `0 < k < n` and `p = k/n`,
`C(n, k) e^{-n H(p)} ≤ 1/√(π npq)`. -/
theorem choose_mul_exp_binEntropy_le {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    n.choose k * exp (-(n * binEntropy (k / n))) ≤ 1 / √(π * n * (k / n) * (1 - k / n)) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hkn.le
  have hm : 0 < m := by omega
  have hq : 1 - (k : ℝ) / (k + m) = m / (k + m) := by field_simp; ring
  push_cast
  rw [exp_neg_binEntropy hk hm, hq, ← mul_assoc]
  exact choose_mul_pow_le' hk hm

/-- **Lemma 17.5.1, (17.41)**, with the binary entropy: for `0 < k < n` and `p = k/n`,
`1/√(8npq) ≤ C(n, k) e^{-n H(p)}`. -/
theorem le_choose_mul_exp_binEntropy {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    1 / √(8 * n * (k / n) * (1 - k / n)) ≤ n.choose k * exp (-(n * binEntropy (k / n))) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hkn.le
  have hm : 0 < m := by omega
  have hq : 1 - (k : ℝ) / (k + m) = m / (k + m) := by field_simp; ring
  push_cast
  rw [exp_neg_binEntropy hk hm, hq, ← mul_assoc]
  exact le_choose_mul_pow' hk hm

end InfoTheory
