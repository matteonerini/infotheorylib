/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Statistics.LargeDeviations
public import InfoTheoryLib.Probability.Variance

/-!
# Chernoff information

With prior probabilities `π₁, π₂ > 0` on the hypotheses `Q = P₁` and `Q = P₂`, the smallest
Bayesian probability of error `Pₑ^(n) = min_A (π₁ P₁ⁿ(Aᶜ) + π₂ P₂ⁿ(A))` decays like `e^{-nC}`,
where `C(P₁, P₂) = -min_{0 ≤ λ ≤ 1} log ∑ₓ P₁(x)^λ P₂(x)^{1-λ}` is the Chernoff information. It
equals `D(P_{λ*}‖P₁) = D(P_{λ*}‖P₂)` for the geometric mixture
`P_λ ∝ P₁^λ P₂^{1-λ}` with `D(P_{λ*}‖P₁) = D(P_{λ*}‖P₂)`.

## Main definitions

* `chernoffZ P₁ P₂ λ = ∑ₓ P₁(x)^λ P₂(x)^{1-λ}`.
* `geomMix P₁ P₂ λ`: the geometric mixture `P_λ` (11.232).
* `chernoffInfo P₁ P₂`: the Chernoff information (11.239).
* `bayesErr π₁ π₂ P₁ P₂ n = ∑ₓ min {π₁ P₁ⁿ(x), π₂ P₂ⁿ(x)}`, the smallest Bayesian probability of
  error (11.240)–(11.243).

## Main statements

* `bayesErr_le`, `bayesErr_eq_map`: (11.240)–(11.243), the maximum a posteriori rule is optimal.
* `min_le_exp_mul_add`: (11.244), `min {a, b} ≤ a^λ b^{1-λ}`.
* `bayesErr_le_chernoffZ_pow`: (11.245)–(11.252), `Pₑ^(n) ≤ (∑ₓ P₁^λ P₂^{1-λ})ⁿ`.
* `exists_relEntropyReal_geomMix_eq`: (11.231)–(11.233) and their equivalence with (11.239).
* `tendsto_neg_log_bayesErr`: **Theorem 11.9.1 (Chernoff)**.
* `prob_ge_le_exp_mul_expect`: **Lemma 11.9.1 (Chernoff bound)**.

## Implementation notes

We assume `P₁, P₂ > 0` so that every relative entropy is finite and continuous.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 11.9
-/

open Real Finset Filter Topology
open Set (Icc)

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### The Chernoff bound -/

/-- **Lemma 11.9.1 (Chernoff bound).** For `s ≥ 0`, `Pr(Y ≥ a) ≤ e^{-sa} E e^{sY}`, by Markov's
inequality applied to `e^{sY}`. -/
theorem prob_ge_le_exp_mul_expect {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (Y : Ω → ℝ) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    prob μ (univ.filter fun ω => a ≤ Y ω) ≤ exp (-(s * a)) * expect μ (fun ω => exp (s * Y ω)) := by
  have h := markov_ineq hμ (fun ω => (exp_pos (s * Y ω)).le) (exp_pos (s * a))
  calc prob μ (univ.filter fun ω => a ≤ Y ω)
      ≤ prob μ (univ.filter fun ω => exp (s * a) ≤ exp (s * Y ω)) :=
        prob_mono hμ fun ω hω => by
          simp only [mem_filter, mem_univ, true_and] at hω ⊢
          exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hs)
    _ ≤ expect μ (fun ω => exp (s * Y ω)) / exp (s * a) := h
    _ = _ := by rw [exp_neg, div_eq_inv_mul]

/-! ### The Bayesian probability of error -/

/-- **(11.243)** The smallest Bayesian probability of error `∑ₓ min {π₁ P₁ⁿ(x), π₂ P₂ⁿ(x)}`. -/
def bayesErr (π₁ π₂ : ℝ) (P₁ P₂ : α → ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → α, min (π₁ * iidPMF P₁ n x) (π₂ * iidPMF P₂ n x)

/-- **(11.241)–(11.243)** Every test `A` has `π₁ P₁ⁿ(Aᶜ) + π₂ P₂ⁿ(A) ≥ Pₑ^(n)`. -/
theorem bayesErr_le [DecidableEq α] (π₁ π₂ : ℝ) (P₁ P₂ : α → ℝ) {n : ℕ}
    (A : Finset (Fin n → α)) :
    bayesErr π₁ π₂ P₁ P₂ n ≤ π₁ * prob (iidPMF P₁ n) Aᶜ + π₂ * prob (iidPMF P₂ n) A := by
  rw [bayesErr, prob, prob, mul_sum, mul_sum, ← sum_add_sum_compl A, add_comm]
  exact add_le_add (sum_le_sum fun x _ => min_le_left _ _) (sum_le_sum fun x _ => min_le_right _ _)

open Classical in
/-- **(11.240)–(11.243)** The maximum a posteriori rule `A = {x : π₁ P₁ⁿ(x) > π₂ P₂ⁿ(x)}` attains
`Pₑ^(n)`. -/
theorem bayesErr_eq_map (π₁ π₂ : ℝ) (P₁ P₂ : α → ℝ) (n : ℕ) :
    bayesErr π₁ π₂ P₁ P₂ n = π₁ * prob (iidPMF P₁ n)
      (univ.filter fun x => π₂ * iidPMF P₂ n x < π₁ * iidPMF P₁ n x)ᶜ +
      π₂ * prob (iidPMF P₂ n) (univ.filter fun x => π₂ * iidPMF P₂ n x < π₁ * iidPMF P₁ n x) := by
  set A := univ.filter fun x : Fin n → α => π₂ * iidPMF P₂ n x < π₁ * iidPMF P₁ n x
  rw [bayesErr, prob, prob, mul_sum, mul_sum, ← sum_add_sum_compl A, add_comm]
  congr 1
  · refine sum_congr rfl fun x hx => min_eq_left ?_
    simp only [A, mem_compl, mem_filter, mem_univ, true_and, not_lt] at hx
    exact hx
  · refine sum_congr rfl fun x hx => min_eq_right ?_
    simp only [A, mem_filter, mem_univ, true_and] at hx
    exact hx.le

/-- **(11.244)** For `a, b > 0` and `0 ≤ λ ≤ 1`, `min {a, b} ≤ a^λ b^{1-λ}`. -/
lemma min_le_exp_mul_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {lam : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) : min a b ≤ exp (lam * log a + (1 - lam) * log b) := by
  rw [← exp_log (lt_min ha hb), exp_le_exp]
  have h1' : 0 ≤ 1 - lam := by linarith
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    have := log_le_log ha h
    nlinarith
  · rw [min_eq_right h]
    have := log_le_log hb h
    nlinarith

/-! ### The geometric mixtures -/

variable {P₁ P₂ : α → ℝ}

/-- **(11.239)** `Z(λ) = ∑ₓ P₁(x)^λ P₂(x)^{1-λ}`. -/
def chernoffZ (P₁ P₂ : α → ℝ) (lam : ℝ) : ℝ := ∑ x, P₁ x ^ lam * P₂ x ^ (1 - lam)

/-- **(11.232)** The geometric mixture `P_λ(x) = P₁(x)^λ P₂(x)^{1-λ}/Z(λ)`. -/
def geomMix (P₁ P₂ : α → ℝ) (lam : ℝ) (x : α) : ℝ :=
  P₁ x ^ lam * P₂ x ^ (1 - lam) / chernoffZ P₁ P₂ lam

/-- **(11.239)** The Chernoff information `C(P₁, P₂) = -min_{0 ≤ λ ≤ 1} log Z(λ)`. -/
def chernoffInfo (P₁ P₂ : α → ℝ) : ℝ :=
  -sInf ((fun lam => log (chernoffZ P₁ P₂ lam)) '' Icc 0 1)

/-- The exponent `log P₁(x)^λ P₂(x)^{1-λ} = λ log P₁(x) + (1 - λ) log P₂(x)`. -/
private def expo (P₁ P₂ : α → ℝ) (lam : ℝ) (x : α) : ℝ := lam * log (P₁ x) + (1 - lam) * log (P₂ x)

omit [Fintype α] in
private lemma rpow_mul_rpow_eq (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) (lam : ℝ) (x : α) :
    P₁ x ^ lam * P₂ x ^ (1 - lam) = exp (expo P₁ P₂ lam x) := by
  rw [rpow_def_of_pos (h₁ x), rpow_def_of_pos (h₂ x), ← exp_add, expo]
  ring_nf

private lemma chernoffZ_eq (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) (lam : ℝ) :
    chernoffZ P₁ P₂ lam = ∑ x, exp (expo P₁ P₂ lam x) :=
  sum_congr rfl fun x _ => rpow_mul_rpow_eq h₁ h₂ lam x

private lemma chernoffZ_pos [Nonempty α] (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) (lam : ℝ) :
    0 < chernoffZ P₁ P₂ lam := by
  rw [chernoffZ_eq h₁ h₂]
  exact sum_pos (fun x _ => exp_pos _) univ_nonempty

lemma geomMix_pos [Nonempty α] (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) (lam : ℝ) (x : α) :
    0 < geomMix P₁ P₂ lam x := by
  rw [geomMix, rpow_mul_rpow_eq h₁ h₂]
  exact div_pos (exp_pos _) (chernoffZ_pos h₁ h₂ lam)

lemma geomMix_isPMF [Nonempty α] (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) (lam : ℝ) :
    IsPMF (geomMix P₁ P₂ lam) :=
  ⟨fun x => (geomMix_pos h₁ h₂ lam x).le, by
    simp only [geomMix, ← sum_div]; exact div_self (chernoffZ_pos h₁ h₂ lam).ne'⟩

/-- The log-likelihood ratio `L(x) = log (P₁(x)/P₂(x))`. -/
private def llr (P₁ P₂ : α → ℝ) (x : α) : ℝ := log (P₁ x) - log (P₂ x)

/-- The mean `m(λ) = ∑ₓ P_λ(x) L(x)` of the log-likelihood ratio under `P_λ`. -/
private def meanLLR (P₁ P₂ : α → ℝ) (lam : ℝ) : ℝ := ∑ x, geomMix P₁ P₂ lam x * llr P₁ P₂ x

private lemma log_geomMix [Nonempty α] (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) (lam : ℝ)
    (x : α) : log (geomMix P₁ P₂ lam x) = expo P₁ P₂ lam x - log (chernoffZ P₁ P₂ lam) := by
  rw [geomMix, rpow_mul_rpow_eq h₁ h₂, log_div (exp_pos _).ne' (chernoffZ_pos h₁ h₂ lam).ne',
    log_exp]

/-- `D(P_λ‖P₁) = -(1 - λ) m(λ) - log Z(λ)` and `D(P_λ‖P₂) = λ m(λ) - log Z(λ)`. -/
private lemma relEntropyReal_geomMix [Nonempty α] (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    relEntropyReal (geomMix P₁ P₂ lam) P₁ =
        -(1 - lam) * meanLLR P₁ P₂ lam - log (chernoffZ P₁ P₂ lam) ∧
      relEntropyReal (geomMix P₁ P₂ lam) P₂ =
        lam * meanLLR P₁ P₂ lam - log (chernoffZ P₁ P₂ lam) := by
  have hG := geomMix_isPMF h₁ h₂ lam
  constructor
  · rw [relEntropyReal, meanLLR, mul_sum]
    have : ∀ x, geomMix P₁ P₂ lam x * log (geomMix P₁ P₂ lam x / P₁ x) =
        -(1 - lam) * (geomMix P₁ P₂ lam x * llr P₁ P₂ x) -
          geomMix P₁ P₂ lam x * log (chernoffZ P₁ P₂ lam) := fun x => by
      rw [log_div (geomMix_pos h₁ h₂ lam x).ne' (h₁ x).ne', log_geomMix h₁ h₂, expo, llr]
      ring
    rw [sum_congr rfl fun x _ => this x, sum_sub_distrib, ← sum_mul, hG.sum_eq_one, one_mul]
  · rw [relEntropyReal, meanLLR, mul_sum]
    have : ∀ x, geomMix P₁ P₂ lam x * log (geomMix P₁ P₂ lam x / P₂ x) =
        lam * (geomMix P₁ P₂ lam x * llr P₁ P₂ x) -
          geomMix P₁ P₂ lam x * log (chernoffZ P₁ P₂ lam) := fun x => by
      rw [log_div (geomMix_pos h₁ h₂ lam x).ne' (h₂ x).ne', log_geomMix h₁ h₂, expo, llr]
      ring
    rw [sum_congr rfl fun x _ => this x, sum_sub_distrib, ← sum_mul, hG.sum_eq_one, one_mul]

/-- If `m(λ*) = 0`, then `log Z(λ) ≥ log Z(λ*)` for every `λ`: `Z(λ)/Z(λ*) = E_{P_{λ*}} e^{(λ-λ*)L}
≥ e^{(λ-λ*) m(λ*)} = 1`. -/
private lemma log_chernoffZ_le [Nonempty α] (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a)
    {ls : ℝ} (hm : meanLLR P₁ P₂ ls = 0) (lam : ℝ) :
    log (chernoffZ P₁ P₂ ls) ≤ log (chernoffZ P₁ P₂ lam) := by
  have hG := geomMix_isPMF h₁ h₂ ls
  have hgibbs := neg_log_sum_le_relEntropyReal_add hG hG.nonneg (fun _ h => h)
    fun x => -((lam - ls) * llr P₁ P₂ x)
  have hD : relEntropyReal (geomMix P₁ P₂ ls) (geomMix P₁ P₂ ls) = 0 :=
    sum_eq_zero fun x _ => by rw [div_self (geomMix_pos h₁ h₂ ls x).ne', log_one, mul_zero]
  have hm' : ∑ x, geomMix P₁ P₂ ls x * -((lam - ls) * llr P₁ P₂ x) = 0 := by
    have : ∑ x, geomMix P₁ P₂ ls x * -((lam - ls) * llr P₁ P₂ x) =
        -((lam - ls) * meanLLR P₁ P₂ ls) := by
      rw [meanLLR, mul_sum, ← sum_neg_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [this, hm, mul_zero, neg_zero]
  have hratio : ∑ x, geomMix P₁ P₂ ls x * exp (-(-((lam - ls) * llr P₁ P₂ x))) =
      chernoffZ P₁ P₂ lam / chernoffZ P₁ P₂ ls := by
    rw [chernoffZ_eq h₁ h₂ lam, sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [geomMix, rpow_mul_rpow_eq h₁ h₂, neg_neg, div_mul_eq_mul_div, ← exp_add]
    congr 2
    simp only [expo, llr]
    ring
  rw [hD, hm', add_zero, hratio, neg_nonpos,
    log_div (chernoffZ_pos h₁ h₂ lam).ne' (chernoffZ_pos h₁ h₂ ls).ne'] at hgibbs
  linarith

/-- **(11.231)–(11.233), (11.239)** There is `λ* ∈ [0, 1]` with
`D(P_{λ*}‖P₁) = D(P_{λ*}‖P₂) = C(P₁, P₂)`, and `C(P₁, P₂) = -log Z(λ*)`. -/
theorem exists_relEntropyReal_geomMix_eq (hp₁ : IsPMF P₁) (hp₂ : IsPMF P₂)
    (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) :
    ∃ ls ∈ Icc (0 : ℝ) 1, relEntropyReal (geomMix P₁ P₂ ls) P₁ = chernoffInfo P₁ P₂ ∧
      relEntropyReal (geomMix P₁ P₂ ls) P₂ = chernoffInfo P₁ P₂ ∧
      chernoffInfo P₁ P₂ = -log (chernoffZ P₁ P₂ ls) := by
  have : Nonempty α := by
    obtain ⟨a, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hp₁)
    exact ⟨a⟩
  -- `m` is continuous, `m(0) = -D(P₂‖P₁) ≤ 0` and `m(1) = D(P₁‖P₂) ≥ 0`.
  have hZ : ∀ lam, chernoffZ P₁ P₂ lam = ∑ x, exp (expo P₁ P₂ lam x) := chernoffZ_eq h₁ h₂
  have hcont : Continuous (meanLLR P₁ P₂) := by
    have hm : meanLLR P₁ P₂ = fun lam => ∑ x, exp (expo P₁ P₂ lam x) /
        (∑ y, exp (expo P₁ P₂ lam y)) * llr P₁ P₂ x := by
      funext lam
      simp only [meanLLR, geomMix, rpow_mul_rpow_eq h₁ h₂, hZ]
    rw [hm]
    refine continuous_finsetSum _ fun x _ => Continuous.mul ?_ continuous_const
    refine Continuous.div (by unfold expo; fun_prop)
      (continuous_finsetSum _ fun y _ => by unfold expo; fun_prop) fun lam => ?_
    exact (sum_pos (fun y _ => exp_pos _) univ_nonempty).ne'
  have hZ01 : ∀ lam ∈ ({0, 1} : Set ℝ), chernoffZ P₁ P₂ lam = 1 := by
    intro lam hlam
    rcases hlam with rfl | rfl
    · simp [chernoffZ, hp₂.sum_eq_one]
    · simp [chernoffZ, hp₁.sum_eq_one]
  have hm0 : meanLLR P₁ P₂ 0 ≤ 0 := by
    have hD := relEntropyReal_nonneg hp₂ hp₁ fun a h => absurd h (h₁ a).ne'
    have : meanLLR P₁ P₂ 0 = -relEntropyReal P₂ P₁ := by
      rw [meanLLR, relEntropyReal, ← sum_neg_distrib]
      refine sum_congr rfl fun x _ => ?_
      simp only [geomMix, hZ01 0 (by simp), div_one, rpow_zero, one_mul, sub_zero, rpow_one, llr]
      rw [log_div (h₂ x).ne' (h₁ x).ne']
      ring
    linarith
  have hm1 : 0 ≤ meanLLR P₁ P₂ 1 := by
    have hD := relEntropyReal_nonneg hp₁ hp₂ fun a h => absurd h (h₂ a).ne'
    have : meanLLR P₁ P₂ 1 = relEntropyReal P₁ P₂ := by
      rw [meanLLR, relEntropyReal]
      refine sum_congr rfl fun x _ => ?_
      simp only [geomMix, hZ01 1 (by simp), div_one, rpow_one, sub_self, rpow_zero, mul_one, llr]
      rw [log_div (h₁ x).ne' (h₂ x).ne']
    linarith
  obtain ⟨ls, hls, hmls⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn ⟨hm0, hm1⟩
  have hC : chernoffInfo P₁ P₂ = -log (chernoffZ P₁ P₂ ls) := by
    have hinf : sInf ((fun lam => log (chernoffZ P₁ P₂ lam)) '' Icc 0 1) =
        log (chernoffZ P₁ P₂ ls) := by
      refine IsLeast.csInf_eq ⟨⟨ls, hls, rfl⟩, ?_⟩
      rintro _ ⟨lam, -, rfl⟩
      exact log_chernoffZ_le h₁ h₂ hmls lam
    rw [chernoffInfo, hinf]
  obtain ⟨hD1, hD2⟩ := relEntropyReal_geomMix h₁ h₂ ls
  refine ⟨ls, hls, ?_, ?_, hC⟩
  · rw [hD1, hmls, hC]; ring
  · rw [hD2, hmls, hC]; ring

/-! ### Theorem 11.9.1 -/

/-- **(11.245)–(11.252)** For priors `π₁, π₂ ≤ 1` and `0 ≤ λ ≤ 1`,
`Pₑ^(n) ≤ (∑ₓ P₁(x)^λ P₂(x)^{1-λ})ⁿ`. -/
theorem bayesErr_le_chernoffZ_pow (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) {π₁ π₂ : ℝ}
    (hπ₁ : π₁ ≤ 1) (hπ₂ : π₂ ≤ 1) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (n : ℕ) :
    bayesErr π₁ π₂ P₁ P₂ n ≤ chernoffZ P₁ P₂ lam ^ n := by
  have key : chernoffZ P₁ P₂ lam ^ n = ∑ x : Fin n → α, ∏ i, exp (expo P₁ P₂ lam (x i)) := by
    rw [chernoffZ_eq h₁ h₂, ← Fintype.prod_sum (fun (_ : Fin n) a => exp (expo P₁ P₂ lam a)),
      prod_const, card_univ, Fintype.card_fin]
  rw [key, bayesErr]
  refine sum_le_sum fun x _ => ?_
  have hp1 : 0 < iidPMF P₁ n x := prod_pos fun i _ => h₁ _
  have hp2 : 0 < iidPMF P₂ n x := prod_pos fun i _ => h₂ _
  calc min (π₁ * iidPMF P₁ n x) (π₂ * iidPMF P₂ n x) ≤ min (iidPMF P₁ n x) (iidPMF P₂ n x) :=
        min_le_min (mul_le_of_le_one_left hp1.le hπ₁) (mul_le_of_le_one_left hp2.le hπ₂)
    _ ≤ exp (lam * log (iidPMF P₁ n x) + (1 - lam) * log (iidPMF P₂ n x)) :=
        min_le_exp_mul_add hp1 hp2 h0 h1
    _ = ∏ i, exp (expo P₁ P₂ lam (x i)) := by
        rw [← exp_sum, iidPMF, iidPMF, log_prod fun i _ => (h₁ _).ne',
          log_prod fun i _ => (h₂ _).ne', mul_sum, mul_sum, ← sum_add_distrib]
        rfl

/-- The Bayesian probability of error is at least `min {π₁, π₂} e^{-n max_i D(Pₓ‖Pᵢ)}/(n + 1)^|𝒳|`
for every type `Pₓ`. -/
theorem le_bayesErr (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) {π₁ π₂ : ℝ} (hπ₁ : 0 < π₁)
    (hπ₂ : 0 < π₂) {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    min π₁ π₂ * exp (-(n * max (relEntropyReal (typeOf x) P₁) (relEntropyReal (typeOf x) P₂))) /
      (n + 1) ^ Fintype.card α ≤ bayesErr π₁ π₂ P₁ P₂ n := by
  set M := max (relEntropyReal (typeOf x) P₁) (relEntropyReal (typeOf x) P₂)
  set H := entropy (typeOf x)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmin : ∀ y ∈ typeClass (typeOf x) n, min π₁ π₂ * exp (-(n * (H + M))) ≤
      min (π₁ * iidPMF P₁ n y) (π₂ * iidPMF P₂ n y) := by
    intro y hy
    rw [mem_typeClass] at hy
    have e : ∀ P : α → ℝ, (∀ a, 0 < P a) → iidPMF P n y =
        exp (-(n * (H + relEntropyReal (typeOf x) P))) := fun P hP => by
      rw [iidPMF_eq_exp_type (fun a => (hP a).le) y (fun a h => absurd h (hP a).ne'), hy]
    rw [e P₁ h₁, e P₂ h₂]
    have hm1 : relEntropyReal (typeOf x) P₁ ≤ M := le_max_left _ _
    have hm2 : relEntropyReal (typeOf x) P₂ ≤ M := le_max_right _ _
    have k1 : exp (-(n * (H + M))) ≤ exp (-(n * (H + relEntropyReal (typeOf x) P₁))) :=
      exp_le_exp.2 (by nlinarith)
    have k2 : exp (-(n * (H + M))) ≤ exp (-(n * (H + relEntropyReal (typeOf x) P₂))) :=
      exp_le_exp.2 (by nlinarith)
    refine le_min ?_ ?_
    · exact mul_le_mul (min_le_left _ _) k1 (exp_pos _).le hπ₁.le
    · exact mul_le_mul (min_le_right _ _) k2 (exp_pos _).le hπ₂.le
  have hT := exp_div_le_card_typeClass hn x
  calc min π₁ π₂ * exp (-(n * M)) / (n + 1) ^ Fintype.card α
      = exp (n * H) / (n + 1) ^ Fintype.card α * (min π₁ π₂ * exp (-(n * (H + M)))) := by
        have e : exp (n * H) * exp (-(n * (H + M))) = exp (-(n * M)) := by
          rw [← exp_add]; ring_nf
        rw [div_mul_eq_mul_div, mul_left_comm, e]
    _ ≤ (typeClass (typeOf x) n).card * (min π₁ π₂ * exp (-(n * (H + M)))) :=
        mul_le_mul_of_nonneg_right hT (mul_pos (lt_min hπ₁ hπ₂) (exp_pos _)).le
    _ = ∑ _y ∈ typeClass (typeOf x) n, min π₁ π₂ * exp (-(n * (H + M))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ typeClass (typeOf x) n, min (π₁ * iidPMF P₁ n y) (π₂ * iidPMF P₂ n y) :=
        sum_le_sum hmin
    _ ≤ bayesErr π₁ π₂ P₁ P₂ n :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ =>
          le_min (mul_nonneg hπ₁.le (prod_nonneg fun i _ => (h₁ _).le))
            (mul_nonneg hπ₂.le (prod_nonneg fun i _ => (h₂ _).le))

/-- **Theorem 11.9.1 (Chernoff).** For priors `0 < π₁, π₂ ≤ 1`, the best achievable exponent of
the Bayesian probability of error is the Chernoff information:
`-(1/n) log Pₑ^(n) → C(P₁, P₂) = D(P_{λ*}‖P₁) = D(P_{λ*}‖P₂)`. -/
theorem tendsto_neg_log_bayesErr (hp₁ : IsPMF P₁) (hp₂ : IsPMF P₂) (h₁ : ∀ a, 0 < P₁ a)
    (h₂ : ∀ a, 0 < P₂ a) {π₁ π₂ : ℝ} (hπ₁ : 0 < π₁) (hπ₂ : 0 < π₂) (hπ₁' : π₁ ≤ 1)
    (hπ₂' : π₂ ≤ 1) :
    Tendsto (fun n : ℕ => -log (bayesErr π₁ π₂ P₁ P₂ n) / n) atTop (𝓝 (chernoffInfo P₁ P₂)) := by
  obtain ⟨ls, hls, hD1, hD2, hC⟩ := exists_relEntropyReal_geomMix_eq hp₁ hp₂ h₁ h₂
  have : Nonempty α := by
    obtain ⟨a, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hp₁)
    exact ⟨a⟩
  set C := chernoffInfo P₁ P₂
  set G := geomMix P₁ P₂ ls
  have hG := geomMix_isPMF h₁ h₂ ls
  set k := Fintype.card α
  -- The probability of error is positive and at least `min π e^{-n(C+ε)}/(n + 1)^k`.
  have hlow : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 0 < n ∧
      min π₁ π₂ * exp (-(n * (C + ε))) / (n + 1) ^ k ≤ bayesErr π₁ π₂ P₁ P₂ n := by
    intro ε hε
    obtain ⟨η₁, hη₁, hc₁⟩ := exists_relEntropyReal_lt h₁ G hε
    obtain ⟨η₂, hη₂, hc₂⟩ := exists_relEntropyReal_lt h₂ G hε
    have hk : Tendsto (fun n : ℕ => (k : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hk.eventually (gt_mem_nhds (lt_min hη₁ hη₂)), eventually_gt_atTop 0]
      with n hkn hn
    obtain ⟨x, hx, -⟩ := exists_typeOf_near hG hn
    have hclose : ∀ a, |typeOf x a - G a| < min η₁ η₂ := fun a => (hx a).trans_lt hkn
    have hM : max (relEntropyReal (typeOf x) P₁) (relEntropyReal (typeOf x) P₂) ≤ C + ε :=
      max_le (by linarith [hc₁ _ fun a => (hclose a).trans_le (min_le_left _ _)])
        (by linarith [hc₂ _ fun a => (hclose a).trans_le (min_le_right _ _)])
    refine ⟨hn, le_trans ?_ (le_bayesErr h₁ h₂ hπ₁ hπ₂ hn x)⟩
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    gcongr
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- `Pₑ^(n) ≤ Z(λ*)ⁿ = e^{-nC}`.
    filter_upwards [hlow 1 one_pos] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hpos : 0 < bayesErr π₁ π₂ P₁ P₂ n :=
      (div_pos (mul_pos (lt_min hπ₁ hπ₂) (exp_pos _)) (by positivity)).trans_le hn.2
    have hup := bayesErr_le_chernoffZ_pow h₁ h₂ hπ₁' hπ₂' hls.1 hls.2 n
    have h1 := log_le_log hpos hup
    rw [log_pow, show log (chernoffZ P₁ P₂ ls) = -C by rw [hC]; ring] at h1
    rw [lt_div_iff₀ hn']
    nlinarith
  · set ε := (a - C) / 3
    have hε : 0 < ε := by simp only [ε]; linarith
    have hlog := (tendsto_log_add_one_div.const_mul (k : ℝ)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (log (min π₁ π₂)))
    rw [mul_zero, sub_zero] at hlog
    filter_upwards [hlow ε hε, hlog.eventually (gt_mem_nhds hε)] with n hn hlogn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hpos : 0 < min π₁ π₂ * exp (-(n * (C + ε))) / (n + 1) ^ k :=
      div_pos (mul_pos (lt_min hπ₁ hπ₂) (exp_pos _)) (by positivity)
    have h1 := log_le_log hpos hn.2
    rw [log_div (mul_pos (lt_min hπ₁ hπ₂) (exp_pos _)).ne' (by positivity),
      log_mul (lt_min hπ₁ hπ₂).ne' (exp_pos _).ne', log_exp, log_pow] at h1
    rw [div_lt_iff₀ hn']
    rw [mul_div_assoc', div_sub_div_same, div_lt_iff₀ hn'] at hlogn
    have : ε * 3 = a - C := by simp only [ε]; ring
    nlinarith

end InfoTheory
