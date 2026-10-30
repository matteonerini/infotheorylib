/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import InfoTheoryLib.Probability.FinitePMF

/-!
# Universal coding of binary sequences

A binary sequence `xⁿ` with `k` ones can be described without any model of its source in about
`n H(k/n) + ½ log n` nats: either by a two-stage description (the count `k`, then the index of
`xⁿ` among the `C(n, k)` sequences with `k` ones), or on the fly, by coding with the uniform
mixture of all Bernoulli distributions,
`q(xⁿ) = ∫₀¹ θᵏ (1 - θ)ⁿ⁻ᵏ dθ = 1 / ((n + 1) C(n, k))`. The conditional probabilities of this
mixture are the Laplace estimates `q(1 | xⁱ) = (kᵢ + 1)/(i + 2)`, which can drive an arithmetic
coder.

## Main definitions

* `twoStageLength n k`: `⌈log₂ (n + 1)⌉ + ⌈log₂ C(n, k)⌉` bits (13.32).
* `bernoulliSeqProb θ x`: the probability `θᵏ (1 - θ)ⁿ⁻ᵏ` of `x` under Bernoulli(`θ`).
* `laplaceMixture n x`: the uniform mixture `1 / ((n + 1) C(n, k))` of Bernoulli distributions
  (13.38).

## Main statements

* `choose_le_sqrt_mul_exp_binEntropy`: **(13.31)**, upper bound,
  `C(n, k) ≤ √(n / (π k (n - k))) e^{n H(k/n)}`, from Stirling's formula.
* `choose_le_exp_binEntropy`: `C(n, k) ≤ e^{n H(k/n)}` for all `k`.
* `twoStageLength_le`: **(13.32)–(13.34)**.
* `integral_pow_mul_one_sub_pow`, `laplaceMixture_eq_integral`: **(13.35)–(13.38)**.
* `laplaceMixture_isPMF`: the mixture is a distribution on `{0, 1}ⁿ`.
* `log_inv_laplaceMixture`, `log_inv_laplaceMixture_le`, `log_inv_laplaceMixture_le_uniform`:
  **(13.39)–(13.40)**, and the uniform redundancy bound `log (n + 1)`.
* `laplaceMixture_snoc_true`, `laplaceMixture_snoc_false`: **(13.41)–(13.44)**, the Laplace
  estimate of the next symbol.

## Implementation notes

Entropies and code lengths are in nats; the two-stage length is in bits, and
`twoStageLength_le` multiplies it by `log 2`. We compute the Beta integral
`∫₀¹ θᵃ (1 - θ)ᵇ dθ = a! b! / (a + b + 1)!` by induction on `b`, from
`θᵃ (1 - θ)ᵇ⁺¹ = θᵃ (1 - θ)ᵇ - θᵃ⁺¹ (1 - θ)ᵇ`, instead of integrating by parts.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 13.2
-/

open Real Finset
open scoped Nat

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Bounds on binomial coefficients -/

/-- `e^{n H(k/n)} = nⁿ / (kᵏ (n - k)ⁿ⁻ᵏ)` for `0 < k < n`. -/
lemma exp_mul_binEntropy {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    exp (n * binEntropy (k / n)) =
      (n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hkn
  have hcast : ((n - k : ℕ) : ℝ) = n - k := by rw [Nat.cast_sub hkn.le]
  have h1 : 1 - (k : ℝ) / n = ((n - k : ℕ) : ℝ) / n := by
    rw [hcast]
    field_simp
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, h1, negMulLog, negMulLog,
    log_div hk'.ne' hn.ne', log_div hm.ne' hn.ne']
  rw [← exp_log (show (0 : ℝ) < (n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) by
    positivity), log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_pow, log_pow]
  congr 1
  have hnk : (n : ℝ) = k + ((n - k : ℕ) : ℝ) := by rw [hcast]; ring
  rw [Nat.cast_sub hkn.le]
  field_simp
  rw [hnk]
  ring

/-- `n! ≤ e √n (n/e)ⁿ`, since the Stirling sequence decreases from `e / √2`. -/
lemma factorial_le_exp_one_mul_sqrt {n : ℕ} (hn : n ≠ 0) :
    (n ! : ℝ) ≤ exp 1 * √n * (n / exp 1) ^ n := by
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.2 hn), Stirling.stirlingSeq_one] at h
  have hpos : 0 < √(2 * n : ℝ) * (n / exp 1) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  rw [Stirling.stirlingSeq, div_le_iff₀ hpos] at h
  calc (n ! : ℝ) ≤ exp 1 / √2 * (√(2 * n : ℝ) * (n / exp 1) ^ n) := h
    _ = exp 1 * √n * (n / exp 1) ^ n := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp

/-- **(13.31), upper bound.** For `0 < k < n`, `C(n, k) ≤ √(n / (π k (n - k))) e^{n H(k/n)}`. -/
theorem choose_le_sqrt_mul_exp_binEntropy {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    (n.choose k : ℝ) ≤ √(n / (π * k * (n - k))) * exp (n * binEntropy (k / n)) := by
  set m := n - k with hm_def
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.sub_pos_of_lt hkn
  have hcast : (m : ℝ) = n - k := by rw [hm_def, Nat.cast_sub hkn.le]
  rw [exp_mul_binEntropy hk hkn, ← hm_def, ← hcast, Nat.cast_choose ℝ hkn.le, ← hm_def]
  have hkf : √(2 * π * k) * (k / exp 1) ^ k ≤ k ! := Stirling.le_factorial_stirling k
  have hmf : √(2 * π * m) * (m / exp 1) ^ m ≤ m ! := Stirling.le_factorial_stirling m
  have hnf := factorial_le_exp_one_mul_sqrt (n := n) (by omega)
  have hkm : (k : ℝ) + m = n := by rw [hcast]; ring
  have hfpos : (0 : ℝ) < k ! * m ! := by positivity
  rw [div_le_iff₀ hfpos]
  -- `e ≤ 2 √π`.
  have he : exp 1 ≤ 2 * √π := by
    have h1 : exp 1 < 2.7182818286 := exp_one_lt_d9
    have h2 : (1.7 : ℝ) ≤ √π := by
      rw [show (1.7 : ℝ) = √(1.7 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [pi_gt_three])
    linarith
  set X := √(n / (π * k * m)) * ((n : ℝ) ^ n / ((k : ℝ) ^ k * (m : ℝ) ^ m))
  have hX : 0 ≤ X := by positivity
  calc (n ! : ℝ) ≤ exp 1 * √n * (n / exp 1) ^ n := hnf
    _ ≤ 2 * √π * √n * (n / exp 1) ^ n := by gcongr
    _ = X * ((√(2 * π * k) * (k / exp 1) ^ k) * (√(2 * π * m) * (m / exp 1) ^ m)) := by
      simp only [X]
      have hsq : √(n / (π * k * m)) * (√(2 * π * k) * √(2 * π * m)) = 2 * √π * √n := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        rw [show n / (π * k * m) * (2 * π * k * (2 * π * m)) = (2 * √π * √n) ^ 2 by
          rw [mul_pow, mul_pow, Real.sq_sqrt pi_pos.le, Real.sq_sqrt hn.le]
          field_simp]
        exact Real.sqrt_sq (by positivity)
      have hexp : (n / exp 1) ^ n = (n : ℝ) ^ n / ((k : ℝ) ^ k * (m : ℝ) ^ m) *
          ((k / exp 1) ^ k * (m / exp 1) ^ m) := by
        rw [div_pow, div_pow, div_pow]
        have : exp 1 ^ n = exp 1 ^ k * exp 1 ^ m := by
          rw [← pow_add]
          congr 1
          exact_mod_cast hkm.symm
        rw [this]
        field_simp
      rw [hexp, ← hsq]
      ring
    _ ≤ X * (k ! * m !) := by gcongr

/-- `C(n, k) ≤ e^{n H(k/n)}` for every `k ≤ n`: the term `C(n, k) pᵏ (1 - p)ⁿ⁻ᵏ` of the binomial
expansion of `(p + (1 - p))ⁿ` is at most `1`, for `p = k/n`. -/
theorem choose_le_exp_binEntropy {n k : ℕ} (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ exp (n * binEntropy (k / n)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases hkn.eq_or_lt with rfl | hkn'
  · have : (k : ℝ) / k = 1 := div_self (by exact_mod_cast hk.ne')
    simp [this]
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = k / n := ⟨_, rfl⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn'
  have hsum := add_pow p (1 - p) n
  rw [add_sub_cancel, one_pow] at hsum
  have hterm : p ^ k * (1 - p) ^ (n - k) * n.choose k ≤ 1 := by
    have hp1 : 0 ≤ 1 - p := by
      rw [hp, sub_nonneg, div_le_one hn]
      exact_mod_cast hkn
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    calc p ^ k * (1 - p) ^ (n - k) * n.choose k
        ≤ ∑ j ∈ range (n + 1), p ^ j * (1 - p) ^ (n - j) * n.choose j :=
          single_le_sum (f := fun j => p ^ j * (1 - p) ^ (n - j) * n.choose j)
            (fun j _ => by positivity) (mem_range.2 (Nat.lt_succ_of_le hkn))
      _ = 1 := hsum.symm
  have hm : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hkn'
  have hpow : p ^ k * (1 - p) ^ (n - k) = (exp (n * binEntropy (k / n)))⁻¹ := by
    rw [exp_mul_binEntropy hk hkn', inv_div]
    have h1 : 1 - p = ((n - k : ℕ) : ℝ) / n := by
      rw [Nat.cast_sub hkn'.le, hp]
      field_simp
    rw [h1, hp, div_pow, div_pow, div_mul_div_comm, ← pow_add, Nat.add_sub_cancel' hkn'.le]
  rw [hpow] at hterm
  rwa [inv_mul_le_iff₀ (exp_pos _), mul_one] at hterm

/-! ### The two-stage description -/

/-- **(13.32)** The two-stage description of a binary sequence with `k` ones: `⌈log₂ (n + 1)⌉`
bits for `k`, then `⌈log₂ C(n, k)⌉` bits for the index of the sequence among those with `k`
ones. -/
def twoStageLength (n k : ℕ) : ℕ := ⌈logb 2 (n + 1)⌉₊ + ⌈logb 2 (n.choose k)⌉₊

/-- **(13.33)–(13.34)** The two-stage description costs about `½ log n` more than `n H(k/n)`:
`l(xⁿ) ≤ n H(k/n) + ½ log n - ½ log (π (k/n) ((n - k)/n)) + 3` bits, for `0 < k < n`. -/
theorem twoStageLength_le {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    (twoStageLength n k : ℝ) * log 2 ≤ n * binEntropy (k / n) + 1 / 2 * log n -
      1 / 2 * log (π * (k / n) * ((n - k) / n)) + 3 * log 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < n - k := by
    have : (k : ℝ) < n := by exact_mod_cast hkn
    linarith
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn.le
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  -- The ceilings cost at most two bits.
  have h1 : (⌈logb 2 (n + 1)⌉₊ : ℝ) < logb 2 (n + 1) + 1 :=
    Nat.ceil_lt_add_one (logb_nonneg (by norm_num) (by linarith))
  have h2 : (⌈logb 2 (n.choose k)⌉₊ : ℝ) < logb 2 (n.choose k) + 1 :=
    Nat.ceil_lt_add_one (logb_nonneg (by norm_num) (by exact_mod_cast Nat.choose_pos hkn.le))
  have hlen : (twoStageLength n k : ℝ) * log 2 ≤ log (n + 1) + log (n.choose k) + 2 * log 2 := by
    have : (twoStageLength n k : ℝ) ≤ logb 2 (n + 1) + logb 2 (n.choose k) + 2 := by
      simp only [twoStageLength, Nat.cast_add]
      linarith
    calc (twoStageLength n k : ℝ) * log 2 ≤ (logb 2 (n + 1) + logb 2 (n.choose k) + 2) * log 2 :=
          mul_le_mul_of_nonneg_right this hlog2.le
      _ = _ := by
        rw [add_mul, add_mul, logb, logb, div_mul_cancel₀ _ hlog2.ne',
          div_mul_cancel₀ _ hlog2.ne']
  -- `log (n + 1) ≤ log n + log 2`.
  have hn1 : log (n + 1) ≤ log n + log 2 := by
    rw [← log_mul hn.ne' (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hk.trans hkn
    exact log_le_log (by positivity) (by linarith)
  -- `log C(n, k) ≤ n H(k/n) - ½ log n - ½ log (π (k/n) ((n - k)/n))`.
  have hCb := choose_le_sqrt_mul_exp_binEntropy hk hkn
  have hlogC : log (n.choose k) ≤ n * binEntropy (k / n) - 1 / 2 * log n -
      1 / 2 * log (π * (k / n) * ((n - k) / n)) := by
    have := log_le_log hC hCb
    rw [log_mul (by positivity) (exp_pos _).ne', log_exp, Real.log_sqrt (by positivity)] at this
    have e : (n : ℝ) / (π * k * (n - k)) = (n * (π * (k / n) * ((n - k) / n)))⁻¹ := by
      field_simp
    rw [e, log_inv, log_mul hn.ne' (by positivity)] at this
    linarith
  linarith

/-! ### The Bernoulli mixture -/

variable {n : ℕ}

/-- The number of ones `k` in a binary sequence. -/
def onesCount (x : Fin n → Bool) : ℕ := ∑ i, if x i then 1 else 0

lemma onesCount_eq_card (x : Fin n → Bool) :
    onesCount x = (univ.filter fun i => x i = true).card := by
  rw [onesCount, card_filter]

lemma onesCount_le (x : Fin n → Bool) : onesCount x ≤ n := by
  rw [onesCount_eq_card]
  exact (card_filter_le _ _).trans (card_fin n).le

lemma onesCount_snoc (x : Fin n → Bool) (b : Bool) :
    onesCount (Fin.snoc x b : Fin (n + 1) → Bool) = onesCount x + if b then 1 else 0 := by
  simp only [onesCount, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The probability `θᵏ (1 - θ)ⁿ⁻ᵏ` of a binary sequence under the Bernoulli(`θ`) distribution. -/
def bernoulliSeqProb (θ : ℝ) (x : Fin n → Bool) : ℝ := ∏ i, if x i then θ else 1 - θ

lemma bernoulliSeqProb_eq (θ : ℝ) (x : Fin n → Bool) :
    bernoulliSeqProb θ x = θ ^ onesCount x * (1 - θ) ^ (n - onesCount x) := by
  rw [bernoulliSeqProb, prod_ite, prod_const, prod_const, ← onesCount_eq_card]
  congr 2
  have h := card_filter_add_card_filter_not (s := univ) (fun i : Fin n => x i = true)
  rw [card_univ, Fintype.card_fin, ← onesCount_eq_card] at h
  omega

/-- **The Beta integral** `∫₀¹ θᵃ (1 - θ)ᵇ dθ = a! b! / (a + b + 1)!`. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ θ in (0 : ℝ)..1, θ ^ a * (1 - θ) ^ b = a ! * b ! / (a + b + 1)! := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, one_pow, ne_eq, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero, Nat.factorial_zero,
      Nat.cast_one, add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
    field_simp
  | succ b ih =>
    have e : (fun θ : ℝ => θ ^ a * (1 - θ) ^ (b + 1)) =
        fun θ => θ ^ a * (1 - θ) ^ b - θ ^ (a + 1) * (1 - θ) ^ b := by
      funext θ
      ring
    rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), ih, ih]
    rw [show a + 1 + b + 1 = (a + b + 1) + 1 by ring,
      show a + (b + 1) + 1 = (a + b + 1) + 1 by ring,
      Nat.factorial_succ (a + b + 1), Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    field_simp
    ring

/-- **(13.38)** The uniform mixture of the Bernoulli distributions,
`q(xⁿ) = 1 / ((n + 1) C(n, k))` for a sequence with `k` ones. -/
def laplaceMixture (n : ℕ) (x : Fin n → Bool) : ℝ := ((n + 1 : ℝ) * n.choose (onesCount x))⁻¹

/-- **(13.35)–(13.38)** `q(xⁿ) = ∫₀¹ θᵏ (1 - θ)ⁿ⁻ᵏ dθ`: the mixture of the Bernoulli(`θ`)
distributions with `θ` uniform on `[0, 1]`. -/
theorem laplaceMixture_eq_integral (x : Fin n → Bool) :
    laplaceMixture n x = ∫ θ in (0 : ℝ)..1, bernoulliSeqProb θ x := by
  simp only [bernoulliSeqProb_eq]
  have hk := onesCount_le x
  rw [integral_pow_mul_one_sub_pow, Nat.add_sub_cancel' hk, laplaceMixture,
    Nat.cast_choose ℝ hk, Nat.factorial_succ]
  have : (0 : ℝ) < n ! := by positivity
  have : (0 : ℝ) < (onesCount x)! := by positivity
  have : (0 : ℝ) < (n - onesCount x)! := by positivity
  push_cast
  field_simp

lemma laplaceMixture_pos (x : Fin n → Bool) : 0 < laplaceMixture n x := by
  have : (0 : ℝ) < n.choose (onesCount x) := by exact_mod_cast Nat.choose_pos (onesCount_le x)
  unfold laplaceMixture
  positivity

/-- The mixture is a probability distribution on `{0, 1}ⁿ`. -/
theorem laplaceMixture_isPMF : IsPMF (laplaceMixture n) := by
  refine ⟨fun x => (laplaceMixture_pos x).le, ?_⟩
  simp only [laplaceMixture_eq_integral]
  rw [← intervalIntegral.integral_finsetSum fun x _ => by
    apply Continuous.intervalIntegrable
    refine continuous_finsetProd _ fun i _ => ?_
    cases x i
    · simp only [Bool.false_eq_true, ite_false]
      fun_prop
    · simp only [ite_true]
      fun_prop]
  have : ∀ θ : ℝ, ∑ x : Fin n → Bool, bernoulliSeqProb θ x = 1 := fun θ => by
    have h := prod_univ_sum (fun _ : Fin n => (univ : Finset Bool))
      (fun _ b => if b then θ else 1 - θ)
    rw [Fintype.piFinset_univ] at h
    simp only [bernoulliSeqProb, ← h, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
      add_sub_cancel, prod_const_one]
  simp [this]

/-- **(13.39)** The ideal code length of the mixture: `log 1/q(xⁿ) = log (n + 1) + log C(n, k)`. -/
theorem log_inv_laplaceMixture (x : Fin n → Bool) :
    log (laplaceMixture n x)⁻¹ = log (n + 1) + log (n.choose (onesCount x)) := by
  have : (0 : ℝ) < n.choose (onesCount x) := by exact_mod_cast Nat.choose_pos (onesCount_le x)
  rw [laplaceMixture, inv_inv, log_mul (by positivity) this.ne']

/-- **(13.40)** For `0 < k < n`, the mixture code is within about `½ log n` of `n H(k/n)`:
`log 1/q(xⁿ) ≤ n H(k/n) + ½ log n - ½ log (π (k/n) ((n - k)/n)) + log 2`. -/
theorem log_inv_laplaceMixture_le (x : Fin n → Bool) (hk : 0 < onesCount x)
    (hkn : onesCount x < n) :
    log (laplaceMixture n x)⁻¹ ≤ n * binEntropy (onesCount x / n) + 1 / 2 * log n -
      1 / 2 * log (π * (onesCount x / n) * ((n - onesCount x) / n)) + log 2 := by
  set k := onesCount x
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : (0 : ℝ) < n - k := by
    have : (k : ℝ) < n := by exact_mod_cast hkn
    linarith
  rw [log_inv_laplaceMixture]
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn.le
  have hn1 : log (n + 1) ≤ log n + log 2 := by
    rw [← log_mul hn.ne' (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hk.trans hkn
    exact log_le_log (by positivity) (by linarith)
  have hCb := choose_le_sqrt_mul_exp_binEntropy hk hkn
  have := log_le_log hC hCb
  rw [log_mul (by positivity) (exp_pos _).ne', log_exp, Real.log_sqrt (by positivity)] at this
  have e : (n : ℝ) / (π * k * (n - k)) = (n * (π * (k / n) * ((n - k) / n)))⁻¹ := by
    field_simp
  rw [e, log_inv, log_mul hn.ne' (by positivity)] at this
  linarith

/-- The uniform redundancy bound: for every `xⁿ`, including `k = 0` and `k = n`,
`log 1/q(xⁿ) ≤ n H(k/n) + log (n + 1)`. -/
theorem log_inv_laplaceMixture_le_uniform (x : Fin n → Bool) :
    log (laplaceMixture n x)⁻¹ ≤ n * binEntropy (onesCount x / n) + log (n + 1) := by
  rw [log_inv_laplaceMixture]
  have hC : (0 : ℝ) < n.choose (onesCount x) := by exact_mod_cast Nat.choose_pos (onesCount_le x)
  have := log_le_log hC (choose_le_exp_binEntropy (onesCount_le x))
  rw [log_exp] at this
  linarith

/-- **(13.41)–(13.44) The Laplace estimate.** The mixture assigns the next symbol `1`, after a
sequence `xⁱ` with `kᵢ` ones, the conditional probability `q(1 | xⁱ) = (kᵢ + 1)/(i + 2)`. -/
theorem laplaceMixture_snoc_true (x : Fin n → Bool) :
    laplaceMixture (n + 1) (Fin.snoc x true) =
      laplaceMixture n x * ((onesCount x + 1) / (n + 2)) := by
  rw [laplaceMixture, laplaceMixture, onesCount_snoc, ite_eq_left rfl]
  have h := Nat.add_one_mul_choose_eq n (onesCount x)
  have hC : (0 : ℝ) < n.choose (onesCount x) := by exact_mod_cast Nat.choose_pos (onesCount_le x)
  have h' : ((n + 1).choose (onesCount x + 1) : ℝ) = (n + 1) * n.choose (onesCount x) /
      (onesCount x + 1) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  rw [h']
  push_cast
  field_simp
  ring

/-- **(13.44)** The conditional probability of `0` is `(i - kᵢ + 1)/(i + 2)`. -/
theorem laplaceMixture_snoc_false (x : Fin n → Bool) :
    laplaceMixture (n + 1) (Fin.snoc x false) =
      laplaceMixture n x * ((n - onesCount x + 1) / (n + 2)) := by
  rw [laplaceMixture, laplaceMixture, onesCount_snoc, ite_eq_right Bool.false_ne_true, add_zero]
  have hk := onesCount_le x
  have h := Nat.choose_mul_succ_eq n (onesCount x)
  have hC : (0 : ℝ) < n.choose (onesCount x) := by exact_mod_cast Nat.choose_pos hk
  have hpos : (0 : ℝ) < n + 1 - onesCount x := by
    have : (onesCount x : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  have h' : ((n + 1).choose (onesCount x) : ℝ) = n.choose (onesCount x) * (n + 1) /
      (n + 1 - onesCount x) := by
    rw [eq_div_iff hpos.ne']
    have := congrArg (fun t : ℕ => (t : ℝ)) h
    simp only [Nat.cast_mul,
      Nat.cast_sub (hk.trans (Nat.le_succ n)), Nat.cast_succ] at this
    linarith
  rw [h']
  have : (n : ℝ) - onesCount x + 1 = n + 1 - onesCount x := by ring
  rw [this]
  push_cast
  field_simp
  ring

end InfoTheory
