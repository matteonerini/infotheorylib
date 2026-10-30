/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.Basic

/-!
# The typical set

The typical set `A_ε^(n)` with respect to `p` is the set of sequences `x ∈ 𝒳ⁿ` with
`e^{-n(H(X)+ε)} ≤ p(x₁, …, xₙ) ≤ e^{-n(H(X)-ε)}`. By the AEP it has probability nearly `1`, its
elements are nearly equiprobable, and it has about `e^{nH(X)}` elements.

## Main definitions

* `typicalSet p n ε`: the typical set `A_ε^(n)`.

## Main statements

* `mem_typicalSet_iff`: `x ∈ A_ε^(n)` iff `p(x) > 0` and `|-(1/n) log p(x) - H(X)| ≤ ε`.
* `tendsto_prob_typicalSet`: `Pr{A_ε^(n)} → 1`.
* `card_typicalSet_le`: `|A_ε^(n)| ≤ e^{n(H(X)+ε)}`.
* `eventually_card_typicalSet_gt`: `|A_ε^(n)| > (1 - ε) e^{n(H(X)-ε)}` for `n` large.

## Implementation notes

Logarithms are natural, so the bounds read `e^{±n(H ± ε)}` with `H` in nats. The book's typical
set uses `2^{-n(H ± ε)}` with `H` and `ε` in bits; it is `typicalSet p n (ε log 2)` (see
`InfoTheory.CoverThomas.mem_typicalSet_iff_bits`).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 3.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- **Definition (3.6).** The typical set `A_ε^(n)` with respect to `p` is the set of sequences
`(x₁, …, xₙ)` with `e^{-n(H(X)+ε)} ≤ p(x₁, …, xₙ) ≤ e^{-n(H(X)-ε)}`. -/
def typicalSet (p : α → ℝ) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) :=
  univ.filter fun x =>
    exp (-(n * (entropy p + ε))) ≤ iidPMF p n x ∧ iidPMF p n x ≤ exp (-(n * (entropy p - ε)))

lemma mem_typicalSet {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α} :
    x ∈ typicalSet p n ε ↔
      exp (-(n * (entropy p + ε))) ≤ iidPMF p n x ∧
        iidPMF p n x ≤ exp (-(n * (entropy p - ε))) := by
  simp [typicalSet]

/-- A sequence is typical iff it has positive probability and its sample entropy is within `ε`
of the entropy. -/
lemma mem_typicalSet_iff {p : α → ℝ} {n : ℕ} (hn : 0 < n) {ε : ℝ} {x : Fin n → α} :
    x ∈ typicalSet p n ε ↔
      0 < iidPMF p n x ∧ |sampleEntropy p x - entropy p| ≤ ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mem_typicalSet]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < iidPMF p n x := (exp_pos _).trans_le h1
    have l1 := (le_log_iff_exp_le hpos).2 h1
    have l2 := (log_le_iff_le_exp hpos).2 h2
    refine ⟨hpos, abs_sub_le_iff.2 ⟨?_, ?_⟩⟩
    · rw [sampleEntropy, sub_le_iff_le_add, div_le_iff₀ hn']; linarith
    · rw [sampleEntropy, sub_le_comm, le_div_iff₀ hn']; linarith
  · rintro ⟨hpos, h⟩
    obtain ⟨h1, h2⟩ := abs_sub_le_iff.1 h
    rw [sampleEntropy, sub_le_iff_le_add, div_le_iff₀ hn'] at h1
    rw [sampleEntropy, sub_le_comm, le_div_iff₀ hn'] at h2
    exact ⟨(le_log_iff_exp_le hpos).1 (by linarith), (log_le_iff_le_exp hpos).1 (by linarith)⟩

/-- **Theorem 3.1.2 (1).** If `x ∈ A_ε^(n)`, then
`H(X) - ε ≤ -(1/n) log p(x₁, …, xₙ) ≤ H(X) + ε`. -/
theorem sampleEntropy_mem_Icc_of_mem_typicalSet {p : α → ℝ} {n : ℕ} (hn : 0 < n) {ε : ℝ}
    {x : Fin n → α} (hx : x ∈ typicalSet p n ε) :
    entropy p - ε ≤ sampleEntropy p x ∧ sampleEntropy p x ≤ entropy p + ε := by
  have h := ((mem_typicalSet_iff hn).1 hx).2
  constructor <;> linarith [abs_sub_le_iff.1 h]

/-- The probability of the complement of the typical set is at most the probability that the
sample entropy deviates from the entropy by at least `ε`. -/
lemma prob_typicalSet_compl_le [DecidableEq α] {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (hn : 0 < n)
    (ε : ℝ) :
    prob (iidPMF p n) (typicalSet p n ε)ᶜ ≤
      prob (iidPMF p n) (univ.filter fun x => ε ≤ |sampleEntropy p x - entropy p|) := by
  refine prob_le_prob_of_ae (iidPMF_isPMF hp n).nonneg fun x hx h0 => ?_
  have hpos : 0 < iidPMF p n x := lt_of_le_of_ne (iidPMF_nonneg hp.nonneg x) (Ne.symm h0)
  rw [mem_compl, mem_typicalSet_iff hn] at hx
  simp only [mem_filter, mem_univ, true_and]
  by_contra! h
  exact hx ⟨hpos, h.le⟩

/-- **(3.1)** The typical set has probability tending to `1`:
`Pr{(X₁, …, Xₙ) : p(X₁, …, Xₙ) = e^{-n(H ± ε)}} → 1`. -/
theorem tendsto_prob_typicalSet {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF p n) (typicalSet p n ε)) atTop (𝓝 1) := by
  classical
  have hc : Tendsto (fun n => prob (iidPMF p n) (typicalSet p n ε)ᶜ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (aep hp ε hε)
      (Eventually.of_forall fun n => prob_nonneg (iidPMF_isPMF hp n).nonneg _) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact prob_typicalSet_compl_le hp hn ε
  have h : ∀ n, prob (iidPMF p n) (typicalSet p n ε) = 1 - prob (iidPMF p n) (typicalSet p n ε)ᶜ :=
    fun n => by linarith [prob_add_prob_compl (iidPMF_isPMF hp n) (typicalSet p n ε)]
  simp only [h]
  simpa using hc.const_sub 1

/-- **Theorem 3.1.2 (2).** `Pr{A_ε^(n)} > 1 - ε` for `n` sufficiently large. -/
theorem eventually_prob_typicalSet_gt {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 - ε < prob (iidPMF p n) (typicalSet p n ε) :=
  (tendsto_prob_typicalSet hp hε).eventually (lt_mem_nhds (by linarith))

/-- **Theorem 3.1.2 (3).** `|A_ε^(n)| ≤ e^{n(H(X)+ε)}`. -/
theorem card_typicalSet_le {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (ε : ℝ) :
    ((typicalSet p n ε).card : ℝ) ≤ exp (n * (entropy p + ε)) := by
  have h1 : ((typicalSet p n ε).card : ℝ) * exp (-(n * (entropy p + ε))) ≤
      prob (iidPMF p n) (typicalSet p n ε) :=
    card_mul_le_prob fun x hx => (mem_typicalSet.1 hx).1
  have h2 := prob_le_one (iidPMF_isPMF hp n) (typicalSet p n ε)
  have h3 : exp (-(n * (entropy p + ε))) * exp (n * (entropy p + ε)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  calc ((typicalSet p n ε).card : ℝ)
      = (typicalSet p n ε).card * exp (-(n * (entropy p + ε))) * exp (n * (entropy p + ε)) := by
        rw [mul_assoc, h3, mul_one]
    _ ≤ 1 * exp (n * (entropy p + ε)) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (exp_pos _).le
    _ = exp (n * (entropy p + ε)) := one_mul _

/-- **Theorem 3.1.2 (4).** `|A_ε^(n)| > (1 - ε) e^{n(H(X)-ε)}` for `n` sufficiently large. -/
theorem eventually_card_typicalSet_gt {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 - ε) * exp (n * (entropy p - ε)) < (typicalSet p n ε).card := by
  filter_upwards [eventually_prob_typicalSet_gt hp hε] with n hn
  have h1 : prob (iidPMF p n) (typicalSet p n ε) ≤
      (typicalSet p n ε).card * exp (-(n * (entropy p - ε))) :=
    prob_le_card_mul fun x hx => (mem_typicalSet.1 hx).2
  have h3 : exp (-(n * (entropy p - ε))) * exp (n * (entropy p - ε)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  calc (1 - ε) * exp (n * (entropy p - ε))
      < (typicalSet p n ε).card * exp (-(n * (entropy p - ε))) * exp (n * (entropy p - ε)) :=
        mul_lt_mul_of_pos_right (hn.trans_le h1) (exp_pos _)
    _ = (typicalSet p n ε).card := by rw [mul_assoc, h3, mul_one]

end InfoTheory
