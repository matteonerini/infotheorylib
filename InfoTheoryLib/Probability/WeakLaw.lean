/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.IID

/-!
# Convergence in probability and the weak law of large numbers

For each `n`, let `Yₙ` be a random variable on a finite probability space `(Ωₙ, μₙ)`. The
sequence `Yₙ` converges in probability to `c` if `Pr{|Yₙ - c| ≥ ε} → 0` for every `ε > 0`, and in
mean square if `E(Yₙ - c)² → 0`. Only the law of each `Yₙ` matters, so the spaces `Ωₙ` may depend
on `n`; for i.i.d. sequences we take `Ωₙ = Fin n → α` with the product law `iidPMF p n`.

## Main definitions

* `TendstoInProb μ Y c`: `Yₙ → c` in probability.
* `TendstoInMeanSq μ Y c`: `Yₙ → c` in mean square.

## Main statements

* `TendstoInMeanSq.tendstoInProb`: convergence in mean square implies convergence in probability.
* `weak_law_bound`: `Pr{|(1/n) ∑ᵢ f(Xᵢ) - E f(X)| ≥ ε} ≤ Var f(X) / (n ε²)`.
* `weak_law`: the weak law of large numbers, `(1/n) ∑ᵢ f(Xᵢ) → E f(X)` in probability.

## Implementation notes

The book defines the modes of convergence of a sequence `X₁, X₂, …` of random variables on one
probability space to a random variable `X`. Here every `Yₙ` lives on its own finite space and
the limit is a constant, which is the case of the AEP and of the weak law. Convergence with
probability `1` needs a single space carrying the whole sequence, and is not defined here.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Chapter 3 and
  Problem 3.1(c)
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- **Definition (convergence in probability).** `Yₙ → c` in probability:
`Pr{|Yₙ - c| ≥ ε} → 0` for every `ε > 0`, where `Yₙ` is a random variable on the finite
probability space `(Ωₙ, μₙ)`. (The book's condition `Pr{|Yₙ - c| > ε} → 0` for every `ε > 0` is
equivalent.) -/
def TendstoInProb {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] (μ : ∀ n, Ω n → ℝ)
    (Y : ∀ n, Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => prob (μ n) (univ.filter fun ω => ε ≤ |Y n ω - c|)) atTop (𝓝 0)

/-- **Definition (convergence in mean square).** `Yₙ → c` in mean square: `E(Yₙ - c)² → 0`. -/
def TendstoInMeanSq {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] (μ : ∀ n, Ω n → ℝ)
    (Y : ∀ n, Ω n → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun n => expect (μ n) fun ω => (Y n ω - c) ^ 2) atTop (𝓝 0)

/-- Convergence in mean square implies convergence in probability, by Markov's inequality
`Pr{|Yₙ - c| ≥ ε} ≤ E(Yₙ - c)² / ε²`. -/
theorem TendstoInMeanSq.tendstoInProb {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    {μ : ∀ n, Ω n → ℝ} (hμ : ∀ n, IsPMF (μ n)) {Y : ∀ n, Ω n → ℝ} {c : ℝ}
    (h : TendstoInMeanSq μ Y c) : TendstoInProb μ Y c := by
  intro ε hε
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  have hlim : Tendsto (fun n => expect (μ n) (fun ω => (Y n ω - c) ^ 2) / ε ^ 2) atTop (𝓝 0) := by
    simpa using h.div_const (ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => prob_nonneg (hμ n).nonneg _) fun n => ?_
  refine (prob_mono (hμ n).nonneg ?_).trans
    (markov_ineq (hμ n).nonneg (fun ω => sq_nonneg (Y n ω - c)) hε2)
  intro ω hω
  simp only [mem_filter, mem_univ, true_and] at hω ⊢
  calc ε ^ 2 ≤ |Y n ω - c| ^ 2 := pow_le_pow_left₀ hε.le hω 2
    _ = (Y n ω - c) ^ 2 := sq_abs _

variable {α : Type*} [Fintype α]

/-- The quantitative weak law of large numbers (Problem 3.1(c), (3.33)): for i.i.d. `Xᵢ ∼ p`,
`Pr{|(1/n) ∑ᵢ f(Xᵢ) - E f(X)| ≥ ε} ≤ Var f(X) / (n ε²)`. -/
theorem weak_law_bound {p : α → ℝ} (hp : IsPMF p) (f : α → ℝ) {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : 0 < ε) :
    prob (iidPMF p n) (univ.filter fun x => ε ≤ |(sampleMean fun i => f (x i)) - expect p f|)
      ≤ variance p f / (n * ε ^ 2) := by
  have h := chebyshev_ineq (iidPMF_isPMF hp n).nonneg (fun x => sampleMean fun i => f (x i)) hε
  rw [expect_sampleMean hp f hn, variance_sampleMean hp f hn, div_div] at h
  exact h

/-- **The weak law of large numbers.** For i.i.d. `Xᵢ ∼ p`, the sample mean `(1/n) ∑ᵢ f(Xᵢ)`
converges in probability to `E f(X)`. -/
theorem weak_law {p : α → ℝ} (hp : IsPMF p) (f : α → ℝ) :
    TendstoInProb (fun n => iidPMF p n) (fun _ x => sampleMean fun i => f (x i)) (expect p f) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => variance p f / ε ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => prob_nonneg (iidPMF_isPMF hp n).nonneg _) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  calc _ ≤ variance p f / (n * ε ^ 2) := weak_law_bound hp f hn hε
    _ = variance p f / ε ^ 2 / n := by rw [div_div, mul_comm]

end InfoTheory
