/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Statistics.Types
public import InfoTheoryLib.Statistics.LargeDeviations

/-!
# Hypothesis testing and the Chernoff–Stein lemma

To decide between two hypotheses `H₁ : Q = P₁` and `H₂ : Q = P₂` from i.i.d. observations, a
test accepts `H₁` on a set `A ⊆ 𝒳ⁿ`, with error probabilities `α = P₁ⁿ(Aᶜ)` and `β = P₂ⁿ(A)`.
Likelihood ratio tests are optimal (Neyman–Pearson). If `α` is only required to stay below
`ε`, the best `β` decays like `e^{-nD(P₁‖P₂)}` (Chernoff–Stein).

## Main definitions

* `lrRegion P₁ P₂ T`: the likelihood ratio region `{x : P₁(x)/P₂(x) > T}` (11.176).
* `relEntTypicalSet P₁ P₂ n ε`: the relative entropy typical set `A_ε^(n)(P₁‖P₂)` (11.206).
* `steinBeta P₁ P₂ ε n`: the smallest `βₙ` with `αₙ < ε` (11.225).

## Main statements

* `neyman_pearson`: **Theorem 11.7.1 (Neyman–Pearson lemma)**.
* `log_iidPMF_div_eq`: (11.187)–(11.192), the log-likelihood ratio is
  `n D(P_{xⁿ}‖P₂) - n D(P_{xⁿ}‖P₁)`.
* `tendstoInProb_log_likelihood`: **Theorem 11.8.1 (AEP for relative entropy)**.
* `relEntTypicalSet_bounds`, `tendsto_prob_relEntTypicalSet`, `prob_relEntTypicalSet_le`,
  `le_prob_relEntTypicalSet`: **Theorem 11.8.2**.
* `le_prob_of_relEntTypicalSet`: **Lemma 11.8.1**.
* `tendsto_log_steinBeta`: **Theorem 11.8.3 (Chernoff–Stein lemma)**.

## Implementation notes

Logarithms are natural. The relative entropy typical set also requires `P₁ⁿ(x), P₂ⁿ(x) > 0`, so
that the bounds of property 1 hold; this changes nothing under `P₁` when `P₁ ≪ P₂`. In the
Neyman–Pearson lemma we assume `T > 0` (for `T = 0` the conclusion can fail).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 11.7
  and 11.8
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The Neyman–Pearson lemma -/

section NeymanPearson

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

open Classical in
/-- **(11.176)** The likelihood ratio region `{x : P₁(x) > T P₂(x)}`. -/
def lrRegion (P₁ P₂ : Ω → ℝ) (T : ℝ) : Finset Ω := univ.filter fun x => T * P₂ x < P₁ x

/-- **(11.178)–(11.182)** For every acceptance region `B`,
`T (β_B - β*) ≥ α* - α_B`, where `α*`, `β*` are the error probabilities of the likelihood ratio
test. -/
theorem lrRegion_err_ineq {P₁ P₂ : Ω → ℝ} (h₁ : IsPMF P₁) (T : ℝ)
    (B : Finset Ω) :
    prob P₁ (lrRegion P₁ P₂ T)ᶜ - prob P₁ Bᶜ ≤
      T * (prob P₂ B - prob P₂ (lrRegion P₁ P₂ T)) := by
  classical
  set A := lrRegion P₁ P₂ T
  -- `(φ_A(x) - φ_B(x))(P₁(x) - T P₂(x)) ≥ 0` for every `x`.
  have hpt : ∀ x, 0 ≤ ((if x ∈ A then 1 else 0) - (if x ∈ B then 1 else 0)) *
      (P₁ x - T * P₂ x) := by
    intro x
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
      simp only [hA, hB, ↓reduceIte, sub_self, zero_mul, le_refl]
    · simp only [A, lrRegion, mem_filter, mem_univ, true_and] at hA
      nlinarith
    · simp only [A, lrRegion, mem_filter, mem_univ, true_and, not_lt] at hA
      nlinarith
  have hsum := sum_nonneg fun x (_ : x ∈ univ) => hpt x
  have e : ∀ S : Finset Ω, ∑ x, (if x ∈ S then (1 : ℝ) else 0) * (P₁ x - T * P₂ x) =
      prob P₁ S - T * prob P₂ S := fun S => by
    simp only [ite_mul, one_mul, zero_mul, prob, mul_sum, ← sum_sub_distrib]
    rw [← sum_filter]
    congr 1
    ext x
    simp
  simp only [sub_mul, sum_sub_distrib, e] at hsum
  rw [prob_compl h₁, prob_compl h₁]
  linarith

/-- **Theorem 11.7.1 (Neyman–Pearson lemma).** Let `T > 0` and let `α*`, `β*` be the error
probabilities of the likelihood ratio region `{x : P₁(x)/P₂(x) > T}`. Every acceptance region `B`
with `α ≤ α*` has `β ≥ β*`. -/
theorem neyman_pearson {P₁ P₂ : Ω → ℝ} (h₁ : IsPMF P₁) {T : ℝ} (hT : 0 < T)
    {B : Finset Ω} (hα : prob P₁ Bᶜ ≤ prob P₁ (lrRegion P₁ P₂ T)ᶜ) :
    prob P₂ (lrRegion P₁ P₂ T) ≤ prob P₂ B := by
  have h := lrRegion_err_ineq (P₂ := P₂) h₁ T B
  by_contra hlt
  push Not at hlt
  nlinarith

end NeymanPearson

variable {α : Type*} [Fintype α]

/-! ### The log-likelihood ratio -/

/-- **(11.187)–(11.192)** The log-likelihood ratio of i.i.d. observations depends only on their
type: `log (P₁ⁿ(x)/P₂ⁿ(x)) = n D(Pₓ‖P₂) - n D(Pₓ‖P₁)`, for `P₁, P₂ > 0`. -/
theorem log_iidPMF_div_eq {P₁ P₂ : α → ℝ} (h₁ : ∀ a, 0 < P₁ a) (h₂ : ∀ a, 0 < P₂ a) {n : ℕ}
    (x : Fin n → α) :
    log (iidPMF P₁ n x / iidPMF P₂ n x) =
      n * relEntropyReal (typeOf x) P₂ - n * relEntropyReal (typeOf x) P₁ := by
  rw [iidPMF_eq_exp_type (fun a => (h₁ a).le) x (fun a h => absurd h (h₁ a).ne'),
    iidPMF_eq_exp_type (fun a => (h₂ a).le) x (fun a h => absurd h (h₂ a).ne'), ← exp_sub,
    log_exp]
  ring

/-! ### The AEP for relative entropy -/

variable {P₁ P₂ : α → ℝ}

omit [Fintype α] in
/-- On a sequence of positive probability, the log-likelihood ratio is a sum over the letters. -/
lemma log_iidPMF_div_eq_sum (h : AbsCont P₁ P₂) {n : ℕ} {x : Fin n → α}
    (hx : iidPMF P₁ n x ≠ 0) :
    log (iidPMF P₁ n x / iidPMF P₂ n x) = ∑ i, log (P₁ (x i) / P₂ (x i)) := by
  have h1 : ∀ i, P₁ (x i) ≠ 0 := fun i h0 => hx (prod_eq_zero (mem_univ i) h0)
  have h2 : ∀ i, P₂ (x i) ≠ 0 := fun i h0 => h1 i (h _ h0)
  rw [iidPMF, iidPMF, ← prod_div_distrib, log_prod fun i _ => div_ne_zero (h1 i) (h2 i)]

/-- **Theorem 11.8.1 (AEP for relative entropy).** For `X₁, X₂, …` i.i.d. `∼ P₁` and `P₁ ≪ P₂`,
`(1/n) log (P₁ⁿ(Xⁿ)/P₂ⁿ(Xⁿ)) → D(P₁‖P₂)` in probability. -/
theorem tendstoInProb_log_likelihood (h₁ : IsPMF P₁) (h : AbsCont P₁ P₂) :
    TendstoInProb (fun n => iidPMF P₁ n)
      (fun n x => log (iidPMF P₁ n x / iidPMF P₂ n x) / n) (relEntropyReal P₁ P₂) := by
  intro ε hε
  have hw := weak_law h₁ (fun a => log (P₁ a / P₂ a)) ε hε
  have hexp : expect P₁ (fun a => log (P₁ a / P₂ a)) = relEntropyReal P₁ P₂ := by
    rw [expect, relEntropyReal]
    exact sum_congr rfl fun a _ => mul_comm _ _
  rw [hexp] at hw
  refine hw.congr fun n => prob_congr_ae (iidPMF_nonneg h₁.nonneg) fun x hx => ?_
  simp only [mem_filter, mem_univ, true_and]
  rw [log_iidPMF_div_eq_sum h hx, sampleMean, Fintype.card_fin]

/-! ### The relative entropy typical set -/

open Classical in
/-- **Definition (11.206).** The relative entropy typical set `A_ε^(n)(P₁‖P₂)`: the sequences of
positive probability with `D(P₁‖P₂) - ε ≤ (1/n) log (P₁ⁿ(x)/P₂ⁿ(x)) ≤ D(P₁‖P₂) + ε`. -/
def relEntTypicalSet (P₁ P₂ : α → ℝ) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) :=
  univ.filter fun x => 0 < iidPMF P₁ n x ∧ 0 < iidPMF P₂ n x ∧
    |log (iidPMF P₁ n x / iidPMF P₂ n x) / n - relEntropyReal P₁ P₂| ≤ ε

lemma mem_relEntTypicalSet {n : ℕ} {ε : ℝ} {x : Fin n → α} :
    x ∈ relEntTypicalSet P₁ P₂ n ε ↔ 0 < iidPMF P₁ n x ∧ 0 < iidPMF P₂ n x ∧
      |log (iidPMF P₁ n x / iidPMF P₂ n x) / n - relEntropyReal P₁ P₂| ≤ ε := by
  classical
  simp [relEntTypicalSet]

/-- **Theorem 11.8.2 (1), (11.207).** On the typical set,
`P₁ⁿ(x) e^{-n(D+ε)} ≤ P₂ⁿ(x) ≤ P₁ⁿ(x) e^{-n(D-ε)}`. -/
theorem relEntTypicalSet_bounds {n : ℕ} (hn : 0 < n) {ε : ℝ} {x : Fin n → α}
    (hx : x ∈ relEntTypicalSet P₁ P₂ n ε) :
    iidPMF P₁ n x * exp (-(n * (relEntropyReal P₁ P₂ + ε))) ≤ iidPMF P₂ n x ∧
      iidPMF P₂ n x ≤ iidPMF P₁ n x * exp (-(n * (relEntropyReal P₁ P₂ - ε))) := by
  obtain ⟨hp1, hp2, hb⟩ := mem_relEntTypicalSet.1 hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set L := log (iidPMF P₁ n x / iidPMF P₂ n x)
  have hL : iidPMF P₂ n x = iidPMF P₁ n x * exp (-L) := by
    rw [exp_neg, exp_log (div_pos hp1 hp2), inv_div, mul_div_cancel₀ _ hp1.ne']
  have h1 : L / n ≤ relEntropyReal P₁ P₂ + ε := by linarith [(abs_le.1 hb).2]
  have h2 : relEntropyReal P₁ P₂ - ε ≤ L / n := by linarith [(abs_le.1 hb).1]
  rw [div_le_iff₀ hn'] at h1
  rw [le_div_iff₀ hn'] at h2
  constructor
  · rw [hL]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) hp1.le
  · rw [hL]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) hp1.le

/-- **Theorem 11.8.2 (2).** For `P₁ ≪ P₂`, `P₁ⁿ(A_ε^(n)(P₁‖P₂)) → 1`, by the AEP for relative
entropy. -/
theorem tendsto_prob_relEntTypicalSet (h₁ : IsPMF P₁) (h₂ : IsPMF P₂) (h : AbsCont P₁ P₂)
    {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF P₁ n) (relEntTypicalSet P₁ P₂ n ε)) atTop (𝓝 1) := by
  classical
  have hbad := tendstoInProb_log_likelihood h₁ h ε hε
  have hle : ∀ n, 1 - prob (iidPMF P₁ n) (univ.filter fun x : Fin n → α =>
      ε ≤ |log (iidPMF P₁ n x / iidPMF P₂ n x) / n - relEntropyReal P₁ P₂|) ≤
      prob (iidPMF P₁ n) (relEntTypicalSet P₁ P₂ n ε) := by
    intro n
    have hc := prob_compl (iidPMF_isPMF h₁ n) (relEntTypicalSet P₁ P₂ n ε)
    have : prob (iidPMF P₁ n) (relEntTypicalSet P₁ P₂ n ε)ᶜ ≤ prob (iidPMF P₁ n)
        (univ.filter fun x : Fin n → α =>
          ε ≤ |log (iidPMF P₁ n x / iidPMF P₂ n x) / n - relEntropyReal P₁ P₂|) := by
      refine prob_le_prob_of_ae (iidPMF_nonneg h₁.nonneg) fun x hx hx0 => ?_
      rw [mem_compl, mem_relEntTypicalSet] at hx
      have hp1 : 0 < iidPMF P₁ n x := lt_of_le_of_ne (iidPMF_nonneg h₁.nonneg x) (Ne.symm hx0)
      have hp2 : 0 < iidPMF P₂ n x := prod_pos fun i _ => lt_of_le_of_ne (h₂.nonneg _)
        (Ne.symm fun h0 => hx0 (prod_eq_zero (mem_univ i) (h _ h0)))
      simp only [mem_filter, mem_univ, true_and]
      by_contra hlt
      push Not at hlt
      exact hx ⟨hp1, hp2, hlt.le⟩
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hbad.const_sub 1)
    tendsto_const_nhds hle fun n => prob_le_one (iidPMF_isPMF h₁ n) _

/-- **Theorem 11.8.2 (3), (11.208)–(11.212).** `P₂ⁿ(A_ε^(n)(P₁‖P₂)) ≤ e^{-n(D(P₁‖P₂)-ε)}`. -/
theorem prob_relEntTypicalSet_le (h₁ : IsPMF P₁) {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    prob (iidPMF P₂ n) (relEntTypicalSet P₁ P₂ n ε) ≤ exp (-(n * (relEntropyReal P₁ P₂ - ε))) := by
  calc prob (iidPMF P₂ n) (relEntTypicalSet P₁ P₂ n ε)
      ≤ ∑ x ∈ relEntTypicalSet P₁ P₂ n ε, iidPMF P₁ n x * exp (-(n * (relEntropyReal P₁ P₂ - ε))) :=
        sum_le_sum fun x hx => (relEntTypicalSet_bounds hn hx).2
    _ = prob (iidPMF P₁ n) (relEntTypicalSet P₁ P₂ n ε) *
          exp (-(n * (relEntropyReal P₁ P₂ - ε))) := by rw [prob, sum_mul]
    _ ≤ _ := mul_le_of_le_one_left (exp_pos _).le (prob_le_one (iidPMF_isPMF h₁ n) _)

/-- **Theorem 11.8.2 (4), (11.213)–(11.217).**
`P₂ⁿ(A_ε^(n)(P₁‖P₂)) ≥ P₁ⁿ(A_ε^(n)(P₁‖P₂)) e^{-n(D(P₁‖P₂)+ε)}`, which is at least
`(1 - ε) e^{-n(D+ε)}` for `n` large. -/
theorem le_prob_relEntTypicalSet {n : ℕ} (hn : 0 < n) (ε : ℝ) :
    prob (iidPMF P₁ n) (relEntTypicalSet P₁ P₂ n ε) * exp (-(n * (relEntropyReal P₁ P₂ + ε))) ≤
      prob (iidPMF P₂ n) (relEntTypicalSet P₁ P₂ n ε) := by
  rw [prob, sum_mul]
  exact sum_le_sum fun x hx => (relEntTypicalSet_bounds hn hx).1

/-- **Lemma 11.8.1.** If `P₁ⁿ(B) ≥ 1 - ε` and the typical set `A_δ^(n)` has
`P₁ⁿ(A_δ^(n)) ≥ 1 - δ`, then `P₂ⁿ(B) ≥ (1 - ε - δ) e^{-n(D(P₁‖P₂)+δ)}`. (The book takes
`δ = ε`.) -/
theorem le_prob_of_relEntTypicalSet (h₁ : IsPMF P₁) (h₂ : IsPMF P₂) {n : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hA : 1 - δ ≤ prob (iidPMF P₁ n) (relEntTypicalSet P₁ P₂ n δ))
    {B : Finset (Fin n → α)} (hB : 1 - ε ≤ prob (iidPMF P₁ n) B) :
    (1 - ε - δ) * exp (-(n * (relEntropyReal P₁ P₂ + δ))) ≤ prob (iidPMF P₂ n) B := by
  classical
  set A := relEntTypicalSet P₁ P₂ n δ
  have hinter := prob_add_prob_sub_one_le_prob_inter (iidPMF_isPMF h₁ n) A B
  calc (1 - ε - δ) * exp (-(n * (relEntropyReal P₁ P₂ + δ)))
      ≤ prob (iidPMF P₁ n) (A ∩ B) * exp (-(n * (relEntropyReal P₁ P₂ + δ))) :=
        mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
    _ = ∑ x ∈ A ∩ B, iidPMF P₁ n x * exp (-(n * (relEntropyReal P₁ P₂ + δ))) := by
        rw [prob, sum_mul]
    _ ≤ ∑ x ∈ A ∩ B, iidPMF P₂ n x :=
        sum_le_sum fun x hx => (relEntTypicalSet_bounds hn (mem_inter.1 hx).1).1
    _ ≤ prob (iidPMF P₂ n) B :=
        sum_le_sum_of_subset_of_nonneg inter_subset_right fun x _ _ =>
          iidPMF_nonneg h₂.nonneg x

/-! ### The Chernoff–Stein lemma -/

/-- **(11.225)** The smallest probability of error of the second kind `βₙ = P₂ⁿ(Aₙ)` over the
acceptance regions with `αₙ = P₁ⁿ(Aₙᶜ) < ε`. -/
def steinBeta [DecidableEq α] (P₁ P₂ : α → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  sInf {b | ∃ A : Finset (Fin n → α), prob (iidPMF P₁ n) Aᶜ < ε ∧ prob (iidPMF P₂ n) A = b}

/-- **Theorem 11.8.3 (Chernoff–Stein lemma).** For `P₁ ≪ P₂` and `0 < ε < 1`,
`(1/n) log βₙ^ε → -D(P₁‖P₂)`: the best exponent of the error of the second kind, when the error
of the first kind is kept below `ε`, is the relative entropy. -/
theorem tendsto_log_steinBeta [DecidableEq α] (h₁ : IsPMF P₁) (h₂ : IsPMF P₂)
    (h : AbsCont P₁ P₂) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n => log (steinBeta P₁ P₂ ε n) / n) atTop (𝓝 (-relEntropyReal P₁ P₂)) := by
  set D := relEntropyReal P₁ P₂
  have hne : ∀ n, {b | ∃ A : Finset (Fin n → α), prob (iidPMF P₁ n) Aᶜ < ε ∧
      prob (iidPMF P₂ n) A = b}.Nonempty := fun n => ⟨_, univ, by simpa using hε0, rfl⟩
  have hbdd : ∀ n, BddBelow {b | ∃ A : Finset (Fin n → α), prob (iidPMF P₁ n) Aᶜ < ε ∧
      prob (iidPMF P₂ n) A = b} := fun n =>
    ⟨0, fun _ ⟨A, _, hb⟩ => hb ▸ prob_nonneg (iidPMF_nonneg h₂.nonneg) A⟩
  -- Lower bound: for `0 < δ < 1 - ε`, eventually `βₙ ≥ (1 - ε - δ) e^{-n(D+δ)}`.
  have hlow : ∀ δ, 0 < δ → δ < 1 - ε → ∀ᶠ n : ℕ in atTop, 0 < n ∧
      (1 - ε - δ) * exp (-(n * (D + δ))) ≤ steinBeta P₁ P₂ ε n := by
    intro δ hδ hδε
    have hA := tendsto_prob_relEntTypicalSet h₁ h₂ h hδ
    filter_upwards [hA.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith)),
      eventually_gt_atTop 0] with n hn hn0
    refine ⟨hn0, le_csInf (hne n) fun _ ⟨B, hB, hb⟩ => hb ▸ ?_⟩
    refine le_prob_of_relEntTypicalSet h₁ h₂ hn0 hn.le ?_
    have := prob_compl (iidPMF_isPMF h₁ n) B
    linarith
  -- Upper bound: for `δ > 0`, eventually `βₙ ≤ e^{-n(D-δ)}`.
  have hup : ∀ δ, 0 < δ → ∀ᶠ n : ℕ in atTop, steinBeta P₁ P₂ ε n ≤ exp (-(n * (D - δ))) := by
    intro δ hδ
    have hA := tendsto_prob_relEntTypicalSet h₁ h₂ h hδ
    filter_upwards [hA.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith)),
      eventually_gt_atTop 0] with n hn hn0
    refine (csInf_le (hbdd n) ⟨_, ?_, rfl⟩).trans (prob_relEntTypicalSet_le h₁ hn0 δ)
    rw [prob_compl (iidPMF_isPMF h₁ n)]
    linarith
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · set δ := min ((-D - a) / 3) ((1 - ε) / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ1 : δ ≤ (-D - a) / 3 := min_le_left _ _
    have hδ2 : δ ≤ (1 - ε) / 2 := min_le_right _ _
    have hc : 0 < 1 - ε - δ := by linarith
    have hlog : Tendsto (fun n : ℕ => log (1 - ε - δ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hlow δ hδ (by linarith), hlog.eventually (lt_mem_nhds (neg_lt_zero.2 hδ))]
      with n hn hlogn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hpos : 0 < (1 - ε - δ) * exp (-(n * (D + δ))) := mul_pos hc (exp_pos _)
    have h1 := log_le_log hpos hn.2
    rw [log_mul hc.ne' (exp_pos _).ne', log_exp] at h1
    rw [lt_div_iff₀ hn']
    rw [lt_div_iff₀ hn'] at hlogn
    nlinarith
  · set δ := (a + D) / 2
    have hδ : 0 < δ := by simp only [δ]; linarith
    obtain ⟨δ', hδ'0, hδ'1⟩ : ∃ δ', 0 < δ' ∧ δ' < 1 - ε := ⟨(1 - ε) / 2, by linarith, by linarith⟩
    filter_upwards [hup δ hδ, hlow δ' hδ'0 hδ'1] with n hn hn2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn2.1
    have hpos : 0 < steinBeta P₁ P₂ ε n :=
      (mul_pos (by linarith) (exp_pos _)).trans_le hn2.2
    have h1 := log_le_log hpos hn
    rw [log_exp] at h1
    rw [div_lt_iff₀ hn']
    simp only [δ] at h1
    nlinarith

end InfoTheory
