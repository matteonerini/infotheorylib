/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StochasticProcess.Basic
public import InfoTheoryLib.MarkovChain.Process

/-!
# Markov chains as stochastic processes

A time-invariant Markov chain with initial distribution `μ` and probability transition matrix
`r` (with `r a b = Pr{Xₙ₊₁ = b | Xₙ = a}`) has the laws
`p(x₁, …, xₙ) = μ(x₁) r(x₁, x₂) ⋯ r(xₙ₋₁, xₙ)`, (4.3).

## Main definitions

* `pathProb r n x`: the probability `r(x₀, x₁) ⋯ r(xₙ₋₁, xₙ)` of a path of `n` transitions.
* `markovLaw μ r n`: the law (4.3) of `(X₁, …, Xₙ)`.
* `markovProcess μ r`: the Markov chain as a `StochasticProcess`.
* `IsIrreducible r`: every state can be reached from every other state.
* `IsAperiodic r`: the lengths of the paths from each state to itself have no common factor
  other than `1`.

## Main statements

* `markovLaw_snoc`: the Markov property (4.2), `p(x₁, …, xₙ, b) = p(x₁, …, xₙ) r(xₙ, b)`.
* `dist_markovLaw_last`: the law of `Xₙ` evolves by `μₙ₊₁ = μₙ r`, (4.5).
* `markovProcess_isStationary`: a chain started from a stationary distribution is a stationary
  process.
* `markovProcess_condEntropyLast`: `H(Xₙ₊₁ | Xₙ, …, X₁) = H(Xₙ₊₁ | Xₙ) = ∑ₐ μₙ(a) H(r(a, ·))`,
  (4.25).
* `markovProcess_hasEntropyRate`: Theorem 4.2.4, the entropy rate of a stationary Markov chain is
  `-∑ᵢⱼ μᵢ Pᵢⱼ log Pᵢⱼ`.
* `markovProcess_hasEntropyRate_of_tendsto`: if the law of `Xₙ` converges to `ν`, the entropy
  rate is `-∑ᵢⱼ νᵢ Pᵢⱼ log Pᵢⱼ` whatever the initial distribution.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 4.1 and
  4.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- The probability `r(x₀, x₁) r(x₁, x₂) ⋯ r(xₙ₋₁, xₙ)` of the transitions along a path. -/
def pathProb (r : α → α → ℝ) (n : ℕ) (x : Fin (n + 1) → α) : ℝ :=
  ∏ i : Fin n, r (x i.castSucc) (x i.succ)

/-- **(4.3)** The law `p(x₁, …, xₙ) = μ(x₁) r(x₁, x₂) ⋯ r(xₙ₋₁, xₙ)` of a time-invariant Markov
chain. -/
def markovLaw (μ : α → ℝ) (r : α → α → ℝ) : (n : ℕ) → (Fin n → α) → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun x => μ (x 0) * pathProb r n x

omit [Fintype α] in
lemma markovLaw_succ (μ : α → ℝ) (r : α → α → ℝ) (n : ℕ) (x : Fin (n + 1) → α) :
    markovLaw μ r (n + 1) x = μ (x 0) * pathProb r n x := rfl

omit [Fintype α] in
lemma pathProb_snoc (r : α → α → ℝ) (n : ℕ) (x : Fin (n + 1) → α) (b : α) :
    pathProb r (n + 1) (Fin.snoc x b) = pathProb r n x * r (x (Fin.last n)) b := by
  rw [pathProb, Fin.prod_univ_castSucc]
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc]
  · rw [Fin.succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

omit [Fintype α] in
lemma pathProb_cons (r : α → α → ℝ) (n : ℕ) (a : α) (x : Fin (n + 1) → α) :
    pathProb r (n + 1) (Fin.cons a x) = r a (x 0) * pathProb r n x := by
  rw [pathProb, Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one]
  congr 1

omit [Fintype α] in
/-- **The Markov property (4.2).** `p(x₁, …, xₙ, b) = p(x₁, …, xₙ) r(xₙ, b)`: given the past,
the next state depends only on the present state. -/
lemma markovLaw_snoc (μ : α → ℝ) (r : α → α → ℝ) (n : ℕ) (x : Fin (n + 1) → α) (b : α) :
    markovLaw μ r (n + 2) (Fin.snoc x b) = markovLaw μ r (n + 1) x * r (x (Fin.last n)) b := by
  rw [markovLaw_succ, markovLaw_succ, pathProb_snoc, ← mul_assoc]
  congr 3

lemma markovLaw_consistent {μ : α → ℝ} (hμ : IsPMF μ) {r : α → α → ℝ} (hr : IsStochastic r)
    (n : ℕ) (x : Fin n → α) : ∑ a, markovLaw μ r (n + 1) (Fin.snoc x a) = markovLaw μ r n x := by
  cases n with
  | zero =>
    have h0 : ∀ a, (Fin.snoc x a : Fin 1 → α) 0 = a := fun a =>
      Fin.snoc_last (α := fun _ => α) a x
    simp [pathProb, h0, hμ.sum_eq_one, markovLaw]
  | succ n => simp only [markovLaw_snoc, ← mul_sum, (hr _).sum_eq_one, mul_one]

lemma markovLaw_nonneg {μ : α → ℝ} (hμ : IsPMF μ) {r : α → α → ℝ} (hr : IsStochastic r)
    (n : ℕ) (x : Fin n → α) : 0 ≤ markovLaw μ r n x := by
  cases n with
  | zero => simp [markovLaw]
  | succ n => exact mul_nonneg (hμ.nonneg _) (prod_nonneg fun i _ => (hr _).nonneg _)

lemma sum_markovLaw {μ : α → ℝ} (hμ : IsPMF μ) {r : α → α → ℝ} (hr : IsStochastic r) (n : ℕ) :
    ∑ x, markovLaw μ r n x = 1 := by
  induction n with
  | zero => simp [markovLaw]
  | succ n ih => rw [sum_snoc]; simp only [markovLaw_consistent hμ hr, ih]

lemma markovLaw_isPMF {μ : α → ℝ} (hμ : IsPMF μ) {r : α → α → ℝ} (hr : IsStochastic r) (n : ℕ) :
    IsPMF (markovLaw μ r n) :=
  ⟨markovLaw_nonneg hμ hr n, sum_markovLaw hμ hr n⟩

/-- The time-invariant Markov chain with initial distribution `μ` and transition matrix `r`. -/
def markovProcess (μ : α → ℝ) (r : α → α → ℝ) (hμ : IsPMF μ) (hr : IsStochastic r) :
    StochasticProcess α where
  law := markovLaw μ r
  isPMF := markovLaw_isPMF hμ hr
  consistent := markovLaw_consistent hμ hr

/-- **Definition.** A Markov chain is irreducible if it is possible to go with positive
probability from any state to any other state in a finite number of steps. -/
def IsIrreducible (r : α → α → ℝ) : Prop := ∀ i j, ∃ n, 0 < transPow r n i j

/-- **Definition.** A Markov chain is aperiodic if, for every state, the largest common factor of
the lengths of the paths from the state to itself is `1`: the only `d` dividing every `n` with
`rⁿ(i|i) > 0` is `d = 1`. -/
def IsAperiodic (r : α → α → ℝ) : Prop :=
  ∀ i (d : ℕ), (∀ n, 0 < transPow r n i i → d ∣ n) → d = 1

/-- A chain that can stay in every state for one step is aperiodic. -/
lemma isAperiodic_of_pos {r : α → α → ℝ} (h : ∀ i, 0 < r i i) : IsAperiodic r := by
  classical
  intro i d hd
  have h1 : transPow r 1 i i = r i i := by simp [transPow]
  exact Nat.dvd_one.1 (hd 1 (h1 ▸ h i))

variable {μ : α → ℝ} {r : α → α → ℝ}

/-- **(4.5)** The law of the state `Xₙ₊₁` is `μ rⁿ`: `μₙ₊₁(x') = ∑ₓ μₙ(x) r(x, x')`. -/
theorem dist_markovLaw_last (n : ℕ) :
    dist (markovLaw μ r (n + 1)) (fun x => x (Fin.last n)) = (step r)^[n] μ := by
  classical
  induction n with
  | zero =>
    funext b
    simp only [Function.iterate_zero, id, dist, markovLaw_succ, pathProb, univ_eq_empty,
      prod_empty, mul_one]
    rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
    simp [Fin.last]
  | succ n ih =>
    funext b
    rw [Function.iterate_succ_apply', ← ih, dist, sum_snoc]
    simp only [Fin.snoc_last, markovLaw_snoc]
    simp only [sum_ite_eq', mem_univ, ite_true]
    rw [step, outDist, sum_dist_mul (markovLaw μ r (n + 1)) (fun x => x (Fin.last n))
      (fun a => r a b)]

/-- A Markov chain whose initial distribution is stationary is a stationary process. -/
theorem markovProcess_isStationary (hμ : IsPMF μ) (hr : IsStochastic r)
    (hstat : IsStationaryDist r μ) : (markovProcess μ r hμ hr).IsStationary := by
  intro n x
  change ∑ a, markovLaw μ r (n + 1) (Fin.cons a x) = markovLaw μ r n x
  cases n with
  | zero => simp [pathProb, hμ.sum_eq_one, markovLaw]
  | succ n =>
    simp only [markovLaw_succ, pathProb_cons, Fin.cons_zero]
    have h := congrFun hstat (x 0)
    simp only [step, outDist] at h
    rw [← h, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    ring

/-! ### Entropy rate of a Markov chain -/

/-- `H(X₁) = H(μ)`. -/
lemma markovProcess_condEntropyLast_zero (hμ : IsPMF μ) (hr : IsStochastic r) :
    (markovProcess μ r hμ hr).condEntropyLast 0 = entropy μ := by
  rw [StochasticProcess.condEntropyLast_eq, StochasticProcess.jointEntropy_zero, sub_zero,
    StochasticProcess.jointEntropy]
  change entropy (markovLaw μ r 1) = entropy μ
  rw [← entropy_comp_equiv (Equiv.funUnique (Fin 1) α).symm]
  congr 1
  funext a
  simp [markovLaw_succ, pathProb]

/-- **(4.25)** For a Markov chain, `H(Xₙ₊₁ | Xₙ, …, X₁) = H(Xₙ₊₁ | Xₙ) = ∑ₐ μₙ(a) H(r(a, ·))`,
where `μₙ` is the law of `Xₙ`. -/
theorem markovProcess_condEntropyLast (hμ : IsPMF μ) (hr : IsStochastic r) (n : ℕ) :
    (markovProcess μ r hμ hr).condEntropyLast (n + 1) =
      ∑ a, (step r)^[n] μ a * entropy (r a) := by
  rw [StochasticProcess.condEntropyLast_eq]
  simp only [StochasticProcess.jointEntropy]
  change entropy (markovLaw μ r (n + 2)) - entropy (markovLaw μ r (n + 1)) = _
  rw [entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog, sum_snoc]
  simp only [markovLaw_snoc, negMulLog_mul, sum_add_distrib, ← sum_mul, ← mul_sum,
    (hr _).sum_eq_one, one_mul]
  rw [← dist_markovLaw_last n, add_sub_cancel_left, sum_dist_mul]
  simp [entropy_eq_sum_negMulLog]

/-- **Theorem 4.2.4.** The entropy rate of a stationary Markov chain with stationary distribution
`μ` and transition matrix `P` is `H(𝒳) = ∑ᵢ μᵢ H(Pᵢ) = -∑ᵢⱼ μᵢ Pᵢⱼ log Pᵢⱼ`, (4.27). -/
theorem markovProcess_hasEntropyRate (hμ : IsPMF μ) (hr : IsStochastic r)
    (hstat : IsStationaryDist r μ) :
    (markovProcess μ r hμ hr).HasEntropyRate (∑ i, μ i * entropy (r i)) := by
  have h : ∀ n, (markovProcess μ r hμ hr).condEntropyLast (n + 1) = ∑ i, μ i * entropy (r i) :=
    fun n => by rw [markovProcess_condEntropyLast, hstat.iterate]
  have hc : (markovProcess μ r hμ hr).HasCondEntropyRate (∑ i, μ i * entropy (r i)) := by
    rw [StochasticProcess.HasCondEntropyRate, ← tendsto_add_atTop_iff_nat 1]
    simp only [h]
    exact tendsto_const_nhds
  exact (cesaro_mean hc).congr fun n => by rw [StochasticProcess.jointEntropy_eq_sum]

/-- **(4.27)** `∑ᵢ μᵢ H(Pᵢ) = -∑ᵢⱼ μᵢ Pᵢⱼ log Pᵢⱼ`. -/
lemma sum_mul_entropy_eq (μ : α → ℝ) (r : α → α → ℝ) :
    ∑ i, μ i * entropy (r i) = -∑ i, ∑ j, μ i * r i j * log (r i j) := by
  simp [entropy, mul_sum, mul_assoc, sum_neg_distrib]

/-- **Remark after Example 4.2.1.** If the law of `Xₙ` converges to `ν` (for instance for an
irreducible and aperiodic chain), then the entropy rate is `∑ᵢ νᵢ H(Pᵢ)` whatever the initial
distribution. -/
theorem markovProcess_hasEntropyRate_of_tendsto (hμ : IsPMF μ) (hr : IsStochastic r)
    {ν : α → ℝ} (hlim : Tendsto (fun n => (step r)^[n] μ) atTop (𝓝 ν)) :
    (markovProcess μ r hμ hr).HasEntropyRate (∑ i, ν i * entropy (r i)) := by
  have hc : (markovProcess μ r hμ hr).HasCondEntropyRate (∑ i, ν i * entropy (r i)) := by
    rw [StochasticProcess.HasCondEntropyRate, ← tendsto_add_atTop_iff_nat 1]
    simp only [markovProcess_condEntropyLast]
    refine tendsto_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).tendsto ν |>.comp hlim).mul_const _
  exact (cesaro_mean hc).congr fun n => by rw [StochasticProcess.jointEntropy_eq_sum]

end InfoTheory
