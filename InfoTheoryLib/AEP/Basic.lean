/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Basic
public import InfoTheoryLib.Probability.WeakLaw

/-!
# The asymptotic equipartition property

Let `X₁, X₂, …` be i.i.d. with law `p`. The AEP states that the sample entropy
`-(1/n) log p(X₁, …, Xₙ)` converges in probability to the entropy `H(X)`: "almost all events are
almost equally surprising". It is a consequence of the weak law of large numbers applied to the
i.i.d. random variables `-log p(Xᵢ)`.

## Main definitions

* `sampleEntropy p x`: the sample entropy `-(1/n) log p(x₁, …, xₙ)` of a sequence.
* `varentropy p`: the variance `Var(-log p(X))` of the surprisal.

## Main statements

* `aep`: the AEP, `-(1/n) log p(X₁, …, Xₙ) → H(X)` in probability.
* `aep_bound`: the quantitative form
  `Pr{|-(1/n) log p(X₁, …, Xₙ) - H(X)| ≥ ε} ≤ Var(-log p(X)) / (n ε²)`.
* `entropy_iidPMF`: `H(X₁, …, Xₙ) = n H(X)` for i.i.d. random variables.

## Implementation notes

Logarithms are natural, so `H(X)` is in nats. The statement is the same in any base.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 3.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- The sample entropy `-(1/n) log p(x₁, …, xₙ)` of a sequence `x` of length `n`, for the
i.i.d. law `p(x₁, …, xₙ) = ∏ᵢ p(xᵢ)`. -/
def sampleEntropy (p : α → ℝ) {n : ℕ} (x : Fin n → α) : ℝ := -log (iidPMF p n x) / n

/-- The varentropy `Var(-log p(X))`, the variance of the surprisal of `X ∼ p`. -/
def varentropy (p : α → ℝ) : ℝ := variance p fun a => -log (p a)

/-- The entropy is the expected surprisal: `H(X) = E[-log p(X)]`. -/
lemma expect_neg_log (p : α → ℝ) : expect p (fun a => -log (p a)) = entropy p := by
  simp [expect, entropy, sum_neg_distrib, mul_comm]

omit [Fintype α] in
/-- `log p(x₁, …, xₙ) = ∑ᵢ log p(xᵢ)` for a sequence of positive probability. -/
lemma log_iidPMF {p : α → ℝ} {n : ℕ} {x : Fin n → α} (h : iidPMF p n x ≠ 0) :
    log (iidPMF p n x) = ∑ i, log (p (x i)) :=
  log_prod fun i _ => (prod_ne_zero_iff.1 h) i (mem_univ i)

omit [Fintype α] in
/-- For a sequence of positive probability, the sample entropy is the sample mean of the
surprisals `-log p(xᵢ)`. -/
lemma sampleEntropy_eq_sampleMean {p : α → ℝ} {n : ℕ} {x : Fin n → α} (h : iidPMF p n x ≠ 0) :
    sampleEntropy p x = sampleMean fun i => -log (p (x i)) := by
  rw [sampleEntropy, log_iidPMF h, sampleMean, Fintype.card_fin, sum_neg_distrib, neg_div]

/-- **The AEP, quantitative form.** For `n > 0` and `ε > 0`,
`Pr{|-(1/n) log p(X₁, …, Xₙ) - H(X)| ≥ ε} ≤ Var(-log p(X)) / (n ε²)`. -/
theorem aep_bound {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    prob (iidPMF p n) (univ.filter fun x => ε ≤ |sampleEntropy p x - entropy p|)
      ≤ varentropy p / (n * ε ^ 2) := by
  refine (prob_le_prob_of_ae (iidPMF_isPMF hp n).nonneg fun x hx h0 => ?_).trans
    (weak_law_bound hp (fun a => -log (p a)) hn hε)
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  rwa [expect_neg_log, ← sampleEntropy_eq_sampleMean h0]

/-- **Theorem 3.1.1 (AEP).** If `X₁, X₂, …` are i.i.d. `∼ p(x)`, then
`-(1/n) log p(X₁, X₂, …, Xₙ) → H(X)` in probability (3.2). -/
theorem aep {p : α → ℝ} (hp : IsPMF p) :
    TendstoInProb (fun n => iidPMF p n) (fun _ x => sampleEntropy p x) (entropy p) := by
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => varentropy p / ε ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => prob_nonneg (iidPMF_isPMF hp n).nonneg _) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  calc _ ≤ varentropy p / (n * ε ^ 2) := aep_bound hp hn hε
    _ = varentropy p / ε ^ 2 / n := by rw [div_div, mul_comm]

/-- The entropy of `n` i.i.d. random variables is `n` times the entropy of one of them:
`H(X₁, …, Xₙ) = n H(X)`. -/
theorem entropy_iidPMF {p : α → ℝ} (hp : IsPMF p) (n : ℕ) :
    entropy (iidPMF p n) = n * entropy p := by
  have h : ∀ x : Fin n → α, -log (iidPMF p n x) * iidPMF p n x =
      (∑ i, -log (p (x i))) * iidPMF p n x := by
    intro x
    by_cases h0 : iidPMF p n x = 0
    · simp [h0]
    · rw [log_iidPMF h0, sum_neg_distrib]
  calc entropy (iidPMF p n) = expect (iidPMF p n) (fun x => -log (iidPMF p n x)) :=
        (expect_neg_log _).symm
    _ = expect (iidPMF p n) (fun x => ∑ i, -log (p (x i))) := sum_congr rfl fun x _ => h x
    _ = n * entropy p := by
        rw [expect_sum, sum_congr rfl fun i _ => expect_iidPMF_apply hp (fun a => -log (p a)) i]
        simp [expect_neg_log]

end InfoTheory
