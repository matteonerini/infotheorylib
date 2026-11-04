/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.WeakLaw

/-!
# Fisher information and the Cramér–Rao inequality

A parametric family `{p(·; θ)}` of distributions on a finite space, differentiable in `θ`, has
the score `V = ∂/∂θ log p(X; θ)` and the Fisher information `J(θ) = E_θ V²`. Every estimator
`T` has `E_θ (T - θ)² ≥ (1 + b'(θ))²/J(θ) + b(θ)²`, where `b` is its bias; in particular an
unbiased estimator has `var T ≥ 1/J(θ)` (the Cramér–Rao inequality). For `n` i.i.d. samples the
Fisher information is `n J(θ)`.

## Main definitions

* `ParamFamily Ω`: a family of positive pmfs `p(·; θ)` on `Ω`, differentiable in `θ`.
* `ParamFamily.score`, `ParamFamily.fisherInfo`: the score (11.264) and the Fisher information
  (11.270).
* `ParamFamily.bias`, `IsUnbiased`, `mse`, `Dominates`, `IsEfficient`, `IsConsistent`: the bias,
  unbiased estimators, the mean-squared error, domination (11.263), efficient and consistent
  estimators.
* `ParamFamily.iid F n`: the family of `n` i.i.d. samples (11.271).

## Main statements

* `ParamFamily.sum_mul_score`: (11.265)–(11.269), `E_θ V = 0`.
* `ParamFamily.cramerRao_bias`: (11.290), `E_θ (T - θ)² ≥ (1 + b'(θ))²/J(θ) + b(θ)²`.
* `ParamFamily.cramerRao`: **Theorem 11.10.1 (Cramér–Rao inequality)**.
* `ParamFamily.fisherInfo_iid`: (11.272)–(11.279), `Jₙ(θ) = n J(θ)`.

## Implementation notes

The book works with densities and justifies the interchange of differentiation and integration
for "well behaved" families. We work with families on a finite space, where the interchange is
the derivative of a finite sum; the Gaussian family of Example 11.10.2 is treated in
`Books.CoverThomas.Chapter11`. The multiparameter Fisher information matrix (11.291)–(11.292) is not
formalized.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 11.10
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- A parametric family `{p(·; θ)}` of positive pmfs on a finite space, differentiable in `θ`. -/
structure ParamFamily (Ω : Type*) [Fintype Ω] where
  /-- The pmf `p(·; θ)`. -/
  pmf : ℝ → Ω → ℝ
  /-- The derivative `∂/∂θ p(ω; θ)`. -/
  deriv : ℝ → Ω → ℝ
  isPMF : ∀ θ, IsPMF (pmf θ)
  pos : ∀ θ ω, 0 < pmf θ ω
  hasDerivAt : ∀ θ ω, HasDerivAt (fun t => pmf t ω) (deriv θ ω) θ

namespace ParamFamily

variable {Ω : Type*} [Fintype Ω] (F : ParamFamily Ω)

/-- **Definition (11.264).** The score `V = ∂/∂θ ln p(X; θ) = (∂/∂θ p(X; θ))/p(X; θ)`. -/
def score (θ : ℝ) (ω : Ω) : ℝ := F.deriv θ ω / F.pmf θ ω

/-- The score is the derivative of the log-likelihood. -/
lemma hasDerivAt_log_pmf (θ : ℝ) (ω : Ω) :
    HasDerivAt (fun t => log (F.pmf t ω)) (F.score θ ω) θ :=
  (F.hasDerivAt θ ω).log (F.pos θ ω).ne'

/-- **Definition (11.270).** The Fisher information `J(θ) = E_θ V²`. -/
def fisherInfo (θ : ℝ) : ℝ := ∑ ω, F.pmf θ ω * F.score θ ω ^ 2

lemma fisherInfo_nonneg (θ : ℝ) : 0 ≤ F.fisherInfo θ :=
  sum_nonneg fun ω _ => mul_nonneg (F.pos θ ω).le (sq_nonneg _)

/-- The derivative of an expectation: `∂/∂θ E_θ T = ∑ ∂/∂θ p(ω; θ) T(ω)`. -/
lemma hasDerivAt_sum_mul (T : Ω → ℝ) (θ : ℝ) :
    HasDerivAt (fun t => ∑ ω, F.pmf t ω * T ω) (∑ ω, F.deriv θ ω * T ω) θ :=
  HasDerivAt.fun_sum fun ω _ => (F.hasDerivAt θ ω).mul_const (T ω)

lemma pmf_mul_score (θ : ℝ) (ω : Ω) : F.pmf θ ω * F.score θ ω = F.deriv θ ω := by
  rw [score, mul_div_cancel₀ _ (F.pos θ ω).ne']

/-- **(11.265)–(11.269)** The score has mean zero: `E_θ V = ∑ ∂/∂θ p = ∂/∂θ 1 = 0`. -/
theorem sum_mul_score (θ : ℝ) : ∑ ω, F.pmf θ ω * F.score θ ω = 0 := by
  have h := F.hasDerivAt_sum_mul (fun _ => 1) θ
  simp only [mul_one, (F.isPMF _).sum_eq_one] at h
  rw [sum_congr rfl fun ω _ => F.pmf_mul_score θ ω]
  exact h.unique (hasDerivAt_const θ 1)

/-! ### Estimators -/

/-- **Definition (Section 11.10).** The bias `b(θ) = E_θ T - θ` of an estimator `T`. -/
def bias (T : Ω → ℝ) (θ : ℝ) : ℝ := ∑ ω, F.pmf θ ω * T ω - θ

/-- **Definition (Section 11.10).** `T` is unbiased if `E_θ T = θ` for every `θ`. -/
def IsUnbiased (T : Ω → ℝ) : Prop := ∀ θ, ∑ ω, F.pmf θ ω * T ω = θ

/-- The mean-squared error `E_θ (T - θ)²`. -/
def mse (T : Ω → ℝ) (θ : ℝ) : ℝ := ∑ ω, F.pmf θ ω * (T ω - θ) ^ 2

/-- **Definition (11.263).** `T₁` dominates `T₂` if `E_θ (T₁ - θ)² ≤ E_θ (T₂ - θ)²` for all `θ`. -/
def Dominates (T₁ T₂ : Ω → ℝ) : Prop := ∀ θ, F.mse T₁ θ ≤ F.mse T₂ θ

/-- **Definition (Section 11.10).** An unbiased estimator is efficient if it meets the Cramér–Rao
bound: `var T = 1/J(θ)`. -/
def IsEfficient (T : Ω → ℝ) : Prop := F.IsUnbiased T ∧ ∀ θ, F.mse T θ = 1 / F.fisherInfo θ

/-- **(11.290)** The Cramér–Rao inequality with a bias term: for `J(θ) > 0`,
`E_θ (T - θ)² ≥ (1 + b'(θ))²/J(θ) + b(θ)²`, where `1 + b'(θ) = ∂/∂θ E_θ T = ∑ ∂/∂θ p(ω; θ) T(ω)`. -/
theorem cramerRao_bias (T : Ω → ℝ) {θ : ℝ} (hJ : 0 < F.fisherInfo θ) :
    (∑ ω, F.deriv θ ω * T ω) ^ 2 / F.fisherInfo θ + F.bias T θ ^ 2 ≤ F.mse T θ := by
  set p := F.pmf θ
  set V := F.score θ
  set m := ∑ ω, p ω * T ω
  have hp := F.isPMF θ
  -- `E V T = E V (T - E T)` since `E V = 0`.
  have hVT : ∑ ω, F.deriv θ ω * T ω = ∑ ω, p ω * V ω * (T ω - m) := by
    have h0 := F.sum_mul_score θ
    have : ∑ ω, p ω * V ω * (T ω - m) = ∑ ω, p ω * V ω * T ω - m * ∑ ω, p ω * V ω := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun ω _ => by ring
    rw [this, h0, mul_zero, sub_zero]
    exact sum_congr rfl fun ω _ => by rw [F.pmf_mul_score]
  -- Cauchy–Schwarz: `(E V (T - E T))² ≤ E V² var T`.
  have hCS : (∑ ω, p ω * V ω * (T ω - m)) ^ 2 ≤
      F.fisherInfo θ * ∑ ω, p ω * (T ω - m) ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq univ (fun ω => √(p ω) * V ω) fun ω => √(p ω) * (T ω - m)
    have hs : ∀ ω, √(p ω) ^ 2 = p ω := fun ω => sq_sqrt (F.pos θ ω).le
    convert h using 2
    · exact sum_congr rfl fun ω _ => by rw [mul_mul_mul_comm, ← sq, hs]; ring
    · exact sum_congr rfl fun ω _ => by rw [mul_pow, hs]
    · exact sum_congr rfl fun ω _ => by rw [mul_pow, hs]
  -- `E (T - θ)² = var T + b²`.
  have hmse : F.mse T θ = ∑ ω, p ω * (T ω - m) ^ 2 + F.bias T θ ^ 2 := by
    have hc : ∑ ω, p ω * (T ω - m) = 0 := by
      rw [show ∑ ω, p ω * (T ω - m) = ∑ ω, p ω * T ω - m * ∑ ω, p ω by
        rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun _ _ => by ring, hp.sum_eq_one]
      ring
    have e : ∀ ω, p ω * (T ω - θ) ^ 2 = p ω * (T ω - m) ^ 2 +
        2 * (m - θ) * (p ω * (T ω - m)) + (m - θ) ^ 2 * p ω := fun ω => by ring
    rw [mse, sum_congr rfl fun ω _ => e ω, sum_add_distrib, sum_add_distrib, ← mul_sum,
      ← mul_sum, hc, hp.sum_eq_one, bias]
    ring
  have hd : (∑ ω, p ω * V ω * (T ω - m)) ^ 2 / F.fisherInfo θ ≤ ∑ ω, p ω * (T ω - m) ^ 2 := by
    rw [div_le_iff₀ hJ]
    linarith
  rw [hmse, hVT]
  linarith

/-- **Theorem 11.10.1 (Cramér–Rao inequality).** The mean-squared error of an unbiased estimator
is at least the reciprocal of the Fisher information: `var T ≥ 1/J(θ)`. -/
theorem cramerRao {T : Ω → ℝ} (hT : F.IsUnbiased T) {θ : ℝ} (hJ : 0 < F.fisherInfo θ) :
    1 / F.fisherInfo θ ≤ F.mse T θ := by
  have h := F.cramerRao_bias T hJ
  -- `∂/∂θ E_θ T = ∂/∂θ θ = 1` (11.283)–(11.288), and the bias vanishes.
  have h1 : ∑ ω, F.deriv θ ω * T ω = 1 := by
    have := F.hasDerivAt_sum_mul T θ
    have hfun : (fun t => ∑ ω, F.pmf t ω * T ω) = id := funext hT
    rw [hfun] at this
    exact this.unique (hasDerivAt_id θ)
  have h0 : F.bias T θ = 0 := by rw [bias, hT, sub_self]
  rw [h1, h0] at h
  simpa using h

/-- **Definition (Section 11.10).** A sequence of estimators `Tₙ` is consistent (in probability)
if `Tₙ(X₁, …, Xₙ) → θ` in probability for every `θ`. -/
def IsConsistent (T : ∀ n : ℕ, (Fin n → Ω) → ℝ) : Prop :=
  ∀ θ, TendstoInProb (fun n => iidPMF (F.pmf θ) n) T θ

/-! ### Independent samples -/

/-- **(11.271)** The family `p(x₁, …, xₙ; θ) = ∏ᵢ p(xᵢ; θ)` of `n` i.i.d. samples; its derivative
is `p(xⁿ; θ) ∑ᵢ V(xᵢ)` (11.272)–(11.274). -/
def iid (n : ℕ) : ParamFamily (Fin n → Ω) where
  pmf θ := iidPMF (F.pmf θ) n
  deriv θ x := iidPMF (F.pmf θ) n x * ∑ i, F.score θ (x i)
  isPMF θ := iidPMF_isPMF (F.isPMF θ) n
  pos θ x := prod_pos fun i _ => F.pos θ (x i)
  hasDerivAt θ x := by
    classical
    have h := HasDerivAt.fun_finsetProd (u := univ) (f := fun i t => F.pmf t (x i))
      fun i _ => F.hasDerivAt θ (x i)
    refine h.congr_deriv ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, iidPMF, ← mul_prod_erase univ (fun j => F.pmf θ (x j)) (mem_univ i), score]
    field_simp [(F.pos θ (x i)).ne']

/-- **(11.274)** The score of `n` i.i.d. samples is the sum of the individual scores. -/
lemma score_iid (n : ℕ) (θ : ℝ) (x : Fin n → Ω) :
    (F.iid n).score θ x = ∑ i, F.score θ (x i) := by
  simp only [score, iid]
  rw [mul_div_cancel_left₀ _ (show iidPMF (F.pmf θ) n x ≠ 0 from
    (prod_pos fun i _ => F.pos θ (x i)).ne')]

/-- **(11.275)–(11.279)** The Fisher information of `n` i.i.d. samples is `n J(θ)`. -/
theorem fisherInfo_iid (n : ℕ) (θ : ℝ) : (F.iid n).fisherInfo θ = n * F.fisherInfo θ := by
  classical
  have hp := F.isPMF θ
  have hE : expect (F.pmf θ) (F.score θ) = 0 := by
    rw [expect, ← F.sum_mul_score θ]
    exact sum_congr rfl fun ω _ => mul_comm _ _
  have hJ : expect (F.pmf θ) (fun a => F.score θ a * F.score θ a) = F.fisherInfo θ := by
    rw [expect, fisherInfo]
    exact sum_congr rfl fun ω _ => by ring
  -- `E (∑ᵢ Vᵢ)² = ∑ᵢ E Vᵢ² + ∑_{i ≠ j} (E V)² = n J`.
  have h : (F.iid n).fisherInfo θ =
      ∑ i : Fin n, ∑ j : Fin n, expect (iidPMF (F.pmf θ) n)
        (fun x => F.score θ (x i) * F.score θ (x j)) := by
    simp only [fisherInfo, score_iid, expect]
    calc ∑ x, (F.iid n).pmf θ x * (∑ i, F.score θ (x i)) ^ 2
        = ∑ x, ∑ i, ∑ j, F.score θ (x i) * F.score θ (x j) * iidPMF (F.pmf θ) n x := by
          refine sum_congr rfl fun x _ => ?_
          rw [sq, sum_mul_sum, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by simp only [iid]; ring
      _ = _ := by
          rw [sum_comm]
          exact sum_congr rfl fun i _ => sum_comm
  rw [h]
  have hterm : ∀ i j : Fin n, expect (iidPMF (F.pmf θ) n)
      (fun x => F.score θ (x i) * F.score θ (x j)) = if i = j then F.fisherInfo θ else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      rw [← hJ]
      exact expect_iidPMF_apply hp (fun a => F.score θ a * F.score θ a) i
    · rw [expect_iidPMF_mul_apply hp _ _ hij, hE, mul_zero]
  simp only [hterm, sum_ite_eq, mem_univ, ↓reduceIte, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end ParamFamily

end InfoTheory
