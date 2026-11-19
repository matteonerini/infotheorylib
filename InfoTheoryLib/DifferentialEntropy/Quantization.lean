/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.Basic
public import InfoTheoryLib.Entropy.Basic

/-!
# Differential entropy and the entropy of quantized random variables

Divide the range of a continuous random variable `X` with density `f` into bins of length `Δ`,
and let `X^Δ` be the bin containing `X`, a discrete random variable with
`Pr{X^Δ = k} = pₖ = ∫_{bin k} f`. Then `H(X^Δ) + log Δ → h(X)` as `Δ → 0`: an `n`-bit
quantization of `X` has entropy about `h(X) + n` bits.

## Main definitions

* `binEdge a b N k`: the edge `a + kΔ` of the `k`-th bin of `[a, b]`, with `Δ = (b - a)/N`.
* `quantPMF f a b N`: the pmf `pₖ = ∫_{bin k} f` of the quantized random variable, (8.25).

## Main statements

* `quantPMF_isPMF`: the quantized probabilities form a pmf.
* `entropy_quantPMF_add_log`: (8.26)–(8.29), `H(X^Δ) + log Δ = ∑ₖ Δ · (-(pₖ/Δ) log (pₖ/Δ))`.
* `tendsto_entropy_quantPMF_add_log`: Theorem 8.3.1, `H(X^Δ) + log Δ → h(X)`.
* `tendsto_entropy_quantPMF_two_pow_sub`: (8.84), `H(X^Δ) - n log 2 → h(X)` for `Δ = 2⁻ⁿ`.

## Implementation notes

The book asks for `f log f` to be Riemann integrable. We prove Theorem 8.3.1 for a density
that is continuous on an interval `[a, b]` and vanishes outside it, quantized with `N` bins of
length `Δ = (b - a)/N` and `N → ∞`. The value of `pₖ / Δ` is the average of `f` over the bin
rather than a value `f(xᵢ)` given by the mean value theorem (8.23); for a continuous `f` these
coincide.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 8.3
-/

open Real MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- The edge `a + kΔ` of the bins of `[a, b]`, with `N` bins of length `Δ = (b - a)/N`. -/
def binEdge (a b : ℝ) (N k : ℕ) : ℝ := a + k * ((b - a) / N)

/-- **(8.24)–(8.25)** The pmf `pₖ = ∫_{a + kΔ}^{a + (k+1)Δ} f` of the quantized random variable
`X^Δ`. -/
def quantPMF (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  ∫ x in binEdge a b N k..binEdge a b N (k + 1), f x

variable {f : ℝ → ℝ} {a b : ℝ} {N : ℕ}

lemma binEdge_zero : binEdge a b N 0 = a := by simp [binEdge]

lemma binEdge_self (hN : N ≠ 0) : binEdge a b N N = b := by
  rw [binEdge]
  field_simp
  ring

lemma binEdge_succ_sub (k : ℕ) : binEdge a b N (k + 1) - binEdge a b N k = (b - a) / N := by
  simp only [binEdge, Nat.cast_add, Nat.cast_one]
  ring

lemma binEdge_le_succ (hab : a ≤ b) (k : ℕ) : binEdge a b N k ≤ binEdge a b N (k + 1) := by
  have := binEdge_succ_sub (a := a) (b := b) (N := N) k
  have : 0 ≤ (b - a) / N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  linarith

/-- The bins lie in `[a, b]`. -/
lemma Icc_binEdge_subset (hab : a ≤ b) {k : ℕ} (hk : k < N) :
    Icc (binEdge a b N k) (binEdge a b N (k + 1)) ⊆ Icc a b := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hk' : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
  intro x ⟨h1, h2⟩
  refine ⟨le_trans ?_ h1, le_trans h2 ?_⟩
  · simp only [binEdge]
    have : 0 ≤ (k : ℝ) * ((b - a) / N) := by positivity
    linarith
  · simp only [binEdge]
    have : ((k + 1 : ℕ) : ℝ) * ((b - a) / N) ≤ N * ((b - a) / N) :=
      mul_le_mul_of_nonneg_right hk' (div_nonneg (by linarith) hN.le)
    rw [mul_div_cancel₀ _ hN.ne'] at this
    linarith

lemma intervalIntegrable_bin {g : ℝ → ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) {k : ℕ}
    (hk : k < N) : IntervalIntegrable g volume (binEdge a b N k) (binEdge a b N (k + 1)) := by
  refine (hg.mono ?_).intervalIntegrable
  rw [uIcc_of_le (binEdge_le_succ hab k)]
  exact Icc_binEdge_subset hab hk

/-- The integral over `[a, b]` is the sum of the integrals over the bins. -/
lemma sum_integral_bins {g : ℝ → ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) (hN : N ≠ 0) :
    ∑ k : Fin N, ∫ x in binEdge a b N k..binEdge a b N (k + 1), g x = ∫ x in a..b, g x := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ x in binEdge a b N k..binEdge a b N (k + 1), g x),
    intervalIntegral.sum_integral_adjacent_intervals (a := binEdge a b N)
      fun k hk => intervalIntegrable_bin hab hg hk,
    binEdge_zero, binEdge_self hN]

/-- For a function vanishing outside `[a, b]`, the integral over `ℝ` is the integral over
`[a, b]`. -/
lemma integral_eq_intervalIntegral {g : ℝ → ℝ} (hab : a ≤ b) (hg : ∀ x ∉ Icc a b, g x = 0) :
    ∫ x, g x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero hg]

lemma quantPMF_nonneg (hf : ∀ x, 0 ≤ f x) (hab : a ≤ b) (k : Fin N) : 0 ≤ quantPMF f a b N k :=
  intervalIntegral.integral_nonneg (binEdge_le_succ hab k) fun x _ => hf x

/-- The quantized probabilities form a pmf. -/
theorem quantPMF_isPMF (hf : IsPDF volume f) (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hzero : ∀ x ∉ Icc a b, f x = 0) (hN : N ≠ 0) : IsPMF (quantPMF f a b N) :=
  ⟨quantPMF_nonneg hf.nonneg hab, by
    change ∑ k : Fin N, ∫ x in binEdge a b N k..binEdge a b N (k + 1), f x = 1
    rw [sum_integral_bins hab hcont hN, ← integral_eq_intervalIntegral hab hzero,
      hf.integral_eq_one]⟩

/-- `-p log p + p log Δ = Δ · (-(p/Δ) log (p/Δ))`. -/
lemma negMulLog_add_mul_log {p Δ : ℝ} (hp : 0 ≤ p) (hΔ : 0 < Δ) :
    negMulLog p + p * log Δ = Δ * negMulLog (p / Δ) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  · rw [negMulLog, negMulLog, log_div hp.ne' hΔ.ne']
    field_simp
    ring

/-- **(8.26)–(8.29)** `H(X^Δ) + log Δ = ∑ₖ ∫_{bin k} -(pₖ/Δ) log (pₖ/Δ)`. -/
theorem entropy_quantPMF_add_log (hf : IsPDF volume f) (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hzero : ∀ x ∉ Icc a b, f x = 0) (hN : N ≠ 0) :
    entropy (quantPMF f a b N) + log ((b - a) / N) =
      ∑ k : Fin N, ∫ _ in binEdge a b N k..binEdge a b N (k + 1),
        negMulLog (quantPMF f a b N k / ((b - a) / N)) := by
  have hΔ : 0 < (b - a) / N := div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hp := quantPMF_isPMF hf hab.le hcont hzero hN
  rw [entropy_eq_sum_negMulLog, ← one_mul (log _), ← hp.sum_eq_one, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [negMulLog_add_mul_log (hp.nonneg k) hΔ, intervalIntegral.integral_const, binEdge_succ_sub,
    smul_eq_mul]

/-- `h(f) = ∑ₖ ∫_{bin k} -f log f`. -/
lemma diffEntropy_eq_sum_bins (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hzero : ∀ x ∉ Icc a b, f x = 0) (hN : N ≠ 0) :
    diffEntropy volume f =
      ∑ k : Fin N, ∫ x in binEdge a b N k..binEdge a b N (k + 1), negMulLog (f x) := by
  rw [sum_integral_bins (g := fun x => negMulLog (f x)) hab
    (continuous_negMulLog.comp_continuousOn hcont) hN, diffEntropy,
    integral_eq_intervalIntegral hab fun x hx => by simp [hzero x hx]]

/-- **Theorem 8.3.1.** If the density `f` of `X` is continuous on `[a, b]` and vanishes outside
it, then `H(X^Δ) + log Δ → h(f)` as `Δ = (b - a)/N → 0`, where `X^Δ` is the quantization of `X`
into `N` bins of length `Δ`. -/
theorem tendsto_entropy_quantPMF_add_log (hf : IsPDF volume f) (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hzero : ∀ x ∉ Icc a b, f x = 0) :
    Tendsto (fun N : ℕ => entropy (quantPMF f a b N) + log ((b - a) / N)) atTop
      (𝓝 (diffEntropy volume f)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hba : 0 < b - a := by linarith
  -- `f` is bounded by `C` on `[a, b]`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  -- `negMulLog` is uniformly continuous on `[0, C + 1]`.
  set η' := η / (2 * (b - a))
  have hη' : 0 < η' := by positivity
  obtain ⟨δ₁, hδ₁, hneg⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := 0) (b := C + 1)).uniformContinuousOn_of_continuous
      continuous_negMulLog.continuousOn) η' hη'
  set δ₁' := min δ₁ 1
  have hδ₁' : 0 < δ₁' := lt_min hδ₁ one_pos
  -- `f` is uniformly continuous on `[a, b]`.
  obtain ⟨δ₂, hδ₂, hfu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) (δ₁' / 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / δ₂)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  set Δ := (b - a) / N
  have hΔ : 0 < Δ := div_pos hba hNpos
  have hΔδ : Δ < δ₂ := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hδ₂] at hN₀
    have : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    nlinarith
  have hp := quantPMF_isPMF hf hab.le hcont hzero hN0
  rw [entropy_quantPMF_add_log hf hab hcont hzero hN0, diffEntropy_eq_sum_bins hab.le hcont hzero
    hN0, dist_eq_norm, ← Finset.sum_sub_distrib]
  -- Each bin contributes at most `η' Δ`.
  have hbin : ∀ k : Fin N, ‖(∫ _ in binEdge a b N k..binEdge a b N (k + 1),
      negMulLog (quantPMF f a b N k / Δ)) -
        ∫ x in binEdge a b N k..binEdge a b N (k + 1), negMulLog (f x)‖ ≤ η' * Δ := by
    intro k
    have hk : (k : ℕ) < N := k.isLt
    have hsub := Icc_binEdge_subset hab.le hk
    have hle := binEdge_le_succ (a := a) (b := b) (N := N) hab.le k
    have hwidth := binEdge_succ_sub (a := a) (b := b) (N := N) k
    rw [← intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_bin (g := fun x => negMulLog (f x)) hab.le
        (continuous_negMulLog.comp_continuousOn hcont) hk)]
    have hbound : ∀ x ∈ uIoc (binEdge a b N k) (binEdge a b N (k + 1)),
        ‖negMulLog (quantPMF f a b N k / Δ) - negMulLog (f x)‖ ≤ η' := by
      intro x hx
      rw [uIoc_of_le hle] at hx
      have hxI : x ∈ Icc a b := hsub (Ioc_subset_Icc_self hx)
      -- `pₖ/Δ` is within `δ₁'/2` of `f(x)`.
      have havg : |quantPMF f a b N k / Δ - f x| ≤ δ₁' / 2 := by
        have h1 : quantPMF f a b N k - Δ * f x =
            ∫ y in binEdge a b N k..binEdge a b N (k + 1), (f y - f x) := by
          rw [intervalIntegral.integral_sub (intervalIntegrable_bin hab.le hcont hk)
            intervalIntegrable_const, intervalIntegral.integral_const, hwidth, smul_eq_mul]
          rfl
        have h2 : ‖∫ y in binEdge a b N k..binEdge a b N (k + 1), (f y - f x)‖ ≤
            δ₁' / 2 * |binEdge a b N (k + 1) - binEdge a b N k| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
          rw [uIoc_of_le hle] at hy
          have hyI : y ∈ Icc a b := hsub (Ioc_subset_Icc_self hy)
          have hxy : Dist.dist y x < δ₂ := by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
          exact (le_of_lt (hfu y hyI x hxI hxy))
        rw [← h1, hwidth, abs_of_pos hΔ, Real.norm_eq_abs] at h2
        rw [show quantPMF f a b N k / Δ - f x = (quantPMF f a b N k - Δ * f x) / Δ by
          field_simp, abs_div, abs_of_pos hΔ, div_le_iff₀ hΔ]
        exact h2
      have hfx : f x ∈ Icc 0 (C + 1) := by
        have := hC x hxI
        rw [Real.norm_eq_abs, abs_le] at this
        exact ⟨hf.nonneg x, by linarith⟩
      have hpk : quantPMF f a b N k / Δ ∈ Icc 0 (C + 1) := by
        refine ⟨div_nonneg (hp.nonneg k) hΔ.le, ?_⟩
        rw [abs_le] at havg
        have : δ₁' ≤ 1 := min_le_right _ _
        linarith [hfx.2, hC x hxI, (abs_le.1 (Real.norm_eq_abs (f x) ▸ hC x hxI)).2]
      have hd : Dist.dist (quantPMF f a b N k / Δ) (f x) < δ₁ := by
        rw [Real.dist_eq]
        have : δ₁' ≤ δ₁ := min_le_left _ _
        linarith
      exact (le_of_lt (hneg _ hpk _ hfx hd))
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rwa [hwidth, abs_of_pos hΔ] at this
  calc ‖∑ k : Fin N, ((∫ _ in binEdge a b N k..binEdge a b N (k + 1),
        negMulLog (quantPMF f a b N k / Δ)) -
          ∫ x in binEdge a b N k..binEdge a b N (k + 1), negMulLog (f x))‖
      ≤ ∑ k : Fin N, η' * Δ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hbin k)
    _ = η / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, η', Δ]
        field_simp
    _ < η := by linarith

/-- **(8.84)** An `n`-bit quantization of `X` has entropy about `h(X) + n` bits: for a density on
an interval of length one, quantized with `2ⁿ` bins of length `Δ = 2⁻ⁿ`,
`H(X^Δ) - n log 2 → h(X)`. -/
theorem tendsto_entropy_quantPMF_two_pow_sub (hf : IsPDF volume f)
    (hcont : ContinuousOn f (Icc a (a + 1))) (hzero : ∀ x ∉ Icc a (a + 1), f x = 0) :
    Tendsto (fun n : ℕ => entropy (quantPMF f a (a + 1) (2 ^ n)) - n * log 2) atTop
      (𝓝 (diffEntropy volume f)) := by
  refine ((tendsto_entropy_quantPMF_add_log hf (by linarith) hcont hzero).comp
    (tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) one_lt_two)).congr fun n => ?_
  simp only [Function.comp_apply, add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat, one_div,
    log_inv, log_pow]
  ring

end InfoTheory
