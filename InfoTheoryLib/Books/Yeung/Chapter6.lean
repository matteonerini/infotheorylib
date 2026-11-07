/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.FactorialBounds
public import InfoTheoryLib.Typicality.L1Conditional

/-!
# Yeung, Chapter 6: Strong Typicality

This file indexes the formalization of Chapter 6 of [yeung2008], and contains its worked example
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Logarithms.** Logarithms are natural, so `2^{-n(H ± η)}` becomes `e^{-n(H ± η)}` with `H` and
  `η` in nats, and the moment generating function `E[2^{sY}]` of Lemma 6.4 becomes `E[e^{sY}]`.
* **Typical sets.** `T_{[X]δ}ⁿ` is `l1TypicalSet p n δ`, and `N(x; x)/n` is `typeOf x a`. The sums
  run over the whole alphabet. The book sums over the support, which gives the same value, since a
  typical sequence has `N(x; x) = 0` outside it.
* **The constant `η`.** `η = δ (-log minₓ p(x))` is `δ * maxNegLog p`, and `λ` is the same for the
  joint pmf. The book says `η > 0` in Theorem 6.2 and (6.15); this fails for a point mass, where
  `η = 0`, without affecting the statements.
* **Limits in `δ` and `n`.** "`ν → 0` as `n → ∞` and `δ → 0`" in Theorem 6.10 is stated as: for
  every `ν > 0` there is `δ₀ > 0` such that the bounds hold for `0 < δ ≤ δ₀` and `n` sufficiently
  large.
* **Joint and marginal laws.** A joint pmf is `q : α × β → ℝ`, with marginals `margFst q` and
  `margSnd q`, and `H(Y|X)` is `H[Prod.snd | Prod.fst ; q]`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 6.1 Strong AEP
* Definition 6.1: `l1TypicalSet`, `mem_l1TypicalSet` (`Typicality.L1`).
* Theorem 6.2: `theorem_6_2` (here).
* The remark after Theorem 6.2, existence of typical sequences: `eventually_l1TypicalSet_nonempty`
  (`Typicality.L1`).
* Theorem 6.3: `theorem_6_3` (here), which is `exists_eventually_prob_l1TypicalSet_compl_lt`
  (`Typicality.L1`).
* Lemma 6.4: `lemma_6_4` (here), from `prob_ge_le_exp_mul_expect` (`Statistics.ChernoffInformation`)
  and `prob_le_le_exp_mul_expect` (`Typicality.L1`). In Lean `log 0 = 0`, so the logarithmic form
  assumes a positive probability; the two lemmas it comes from do not.

### 6.2 Strong Typicality Versus Weak Typicality
* Proposition 6.5: `proposition_6_5` (here), which is `l1TypicalSet_subset_typicalSet`
  (`Typicality.L1`).
* (6.86)–(6.88), a weakly typical sequence that is not strongly typical: `weak_not_strong` (here).

### 6.3 Joint Typicality
* Definition 6.6: `jointL1TypicalSet`, `mem_jointL1TypicalSet` (`Typicality.L1`).
* Theorem 6.7: `theorem_6_7` (here).
* Theorem 6.8: `theorem_6_8` (here), which is `comp_mem_l1TypicalSet` (`Typicality.L1`).
* Theorem 6.9: `theorem_6_9` (here).
* (6.110): `condL1TypicalSet`, `mem_condL1TypicalSet` (`Typicality.L1Conditional`).
* Theorem 6.10: `theorem_6_10` (here), which is `exists_card_condL1TypicalSet_bounds`
  (`Typicality.L1Conditional`). The upper bound `card_condL1TypicalSet_le` holds for every `n`. The
  lower bound is proved from `card_typeClass_zip_le` and `exp_div_le_card_completions`, not from
  Lemma 6.11.
* Lemma 6.11: `lemma_6_11` (here), from `mul_log_sub_lt_log_factorial` and `log_factorial_lt`
  (`ForMathlib.FactorialBounds`), by induction and not by integrals.
* Corollary 6.12: `corollary_6_12` (here), which is `eventually_card_l1TypicalProjection_ge`
  (`Typicality.L1Conditional`), with `S_{[X]δ}ⁿ` as `l1TypicalProjection`. Its `ψ` does not depend
  on `n`.
* Proposition 6.13: `proposition_6_13` (here), which is `eventually_prob_l1TypicalProjection_gt`
  (`Typicality.L1Conditional`). The book leaves the proof as an exercise.

### 6.4 An Interpretation of the Basic Inequalities
* (6.153)–(6.154): `card_condL1TypicalSet_pair_le` (`Typicality.L1Conditional`).
* (6.155)–(6.156): `condEntropy_le_add_of_typicality` (`Typicality.L1Conditional`). The conditional
  entropies on the right are computed from the laws of `(Z, X)` and `(Z, Y)`.

## Differences from the book

* (6.123)–(6.125) write `H(X)` where the proof needs `H(X, Y)` and the conclusion `H(Y|X)`:
  `2^{-n(H(X,Y) + ν/2)}` in (6.123)–(6.124), and `2^{n(H(Y|X) + ν)}` in (6.125). The Lean statement
  has the corrected form.
* (6.98) and (6.104) write `< δ` where Definition 6.1 has `≤ δ`. The Lean statement of Theorem 6.8
  uses `≤ δ`.
* The book's lower bound in Theorem 6.10 omits the details of the case `p(x, y) = 1` (its footnote
  3). The proof here has no such case.

## Not formalized

* Figures 6.1 to 6.3, and the informal description of the asymptotic quasi-uniform structure of the
  strong joint typicality arrays.
* The heuristic count (6.109).
* The remark that all unconstrained information inequalities can be obtained from this structure,
  which the book attributes to Chan.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Worked example -/

/-- The source of Section 6.2: `p(0) = 0.5`, `p(1) = 0.25` and `p(2) = 0.25`. -/
def pmf_6_2 : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

lemma pmf_6_2_isPMF : IsPMF pmf_6_2 := by
  refine ⟨fun a => ?_, ?_⟩
  · fin_cases a <;> norm_num [pmf_6_2]
  · norm_num [pmf_6_2, Fin.sum_univ_three]

/-- The sequence of Section 6.2, with relative frequencies `q(0) = q(1) = 0.5` and `q(2) = 0`. -/
def seq_6_2 (k : ℕ) : Fin (k + k) → Fin 3 := Fin.append (fun _ => 0) (fun _ => 1)

lemma log_four : log (4 : ℝ) = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num

lemma entropy_pmf_6_2 : entropy pmf_6_2 = 3 / 2 * log 2 := by
  have h₁ : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
  have h₂ : log (1 / 4 : ℝ) = -(2 * log 2) := by rw [one_div, log_inv, log_four]
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_three]
  simp only [pmf_6_2, negMulLog, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    h₁, h₂]
  ring

lemma symbolCount_seq_6_2 (k : ℕ) (a : Fin 3) :
    (symbolCount (seq_6_2 k) a : ℝ) = (if a = 0 then k else 0) + if a = 1 then k else 0 := by
  classical
  rw [symbolCount_eq_sum, Fin.sum_univ_add]
  simp only [seq_6_2, Fin.append_left, Fin.append_right]
  fin_cases a <;> simp

lemma iidPMF_seq_6_2 (k : ℕ) :
    iidPMF pmf_6_2 (k + k) (seq_6_2 k) = exp (-(((k + k : ℕ) : ℝ) * entropy pmf_6_2)) := by
  have h₁ : (1 / 2 : ℝ) = exp (-log 2) := by
    rw [exp_neg, exp_log (by norm_num)]; norm_num
  have h₂ : (1 / 4 : ℝ) = exp (-(2 * log 2)) := by
    rw [exp_neg, ← log_four, exp_log (by norm_num)]; norm_num
  have h₃ : iidPMF pmf_6_2 (k + k) (seq_6_2 k) = (1 / 2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k := by
    have h₄ : ∀ i : Fin k, pmf_6_2 (seq_6_2 k (Fin.castAdd k i)) = 1 / 2 := fun i => by
      rw [seq_6_2, Fin.append_left]; norm_num [pmf_6_2]
    have h₅ : ∀ i : Fin k, pmf_6_2 (seq_6_2 k (Fin.natAdd k i)) = 1 / 4 := fun i => by
      rw [seq_6_2, Fin.append_right]; norm_num [pmf_6_2]
    rw [iidPMF, Fin.prod_univ_add]
    simp only [h₄, h₅, prod_const, card_univ, Fintype.card_fin]
  rw [h₃, h₁, h₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, entropy_pmf_6_2]
  congr 1
  push_cast
  ring

/-- **(6.86)–(6.88)** For `p = (0.5, 0.25, 0.25)`, a sequence of length `2k` with relative
frequencies `(0.5, 0.5, 0)` is weakly `ε`-typical for every `ε ≥ 0`, but it is not strongly
`δ`-typical for `δ < 1/2`. So weak typicality does not imply strong typicality. -/
theorem weak_not_strong {k : ℕ} (hk : 0 < k) :
    (∀ ε ≥ 0, seq_6_2 k ∈ typicalSet pmf_6_2 (k + k) ε) ∧
      ∀ δ < 1 / 2, seq_6_2 k ∉ l1TypicalSet pmf_6_2 (k + k) δ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun ε hε => mem_typicalSet.2 ?_, fun δ hδ h => ?_⟩
  · rw [iidPMF_seq_6_2]
    have hn : (0 : ℝ) ≤ ((k + k : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor <;> refine exp_le_exp.2 ?_ <;> nlinarith [mul_nonneg hn hε]
  · have h₁ := (mem_l1TypicalSet.1 h).2
    have ht : ∀ a, typeOf (seq_6_2 k) a =
        (if a = 0 then 1 / 2 else 0) + if a = 1 then 1 / 2 else 0 := by
      intro a
      rw [typeOf, symbolCount_seq_6_2]
      push_cast
      fin_cases a <;> simp <;> field_simp <;> norm_num
    rw [Fin.sum_univ_three] at h₁
    simp only [ht, pmf_6_2] at h₁
    norm_num at h₁
    linarith

/-! ### Aliases -/

/-- **Theorem 6.2 (Strong AEP).** (6.2)–(6.4), with `η = δ (-log minₓ p(x))`. -/
theorem theorem_6_2 {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ : 0 < δ) :
    (∀ (n : ℕ) (x : Fin n → α), x ∈ l1TypicalSet p n δ →
      exp (-(n * (entropy p + δ * maxNegLog p))) ≤ iidPMF p n x ∧
        iidPMF p n x ≤ exp (-(n * (entropy p - δ * maxNegLog p)))) ∧
    (∀ᶠ n in atTop, 1 - δ < prob (iidPMF p n) (l1TypicalSet p n δ)) ∧
    ∀ᶠ n : ℕ in atTop, (1 - δ) * exp (n * (entropy p - δ * maxNegLog p)) ≤
        (l1TypicalSet p n δ).card ∧
      ((l1TypicalSet p n δ).card : ℝ) ≤ exp (n * (entropy p + δ * maxNegLog p)) := by
  refine ⟨fun n x hx => exp_le_iidPMF_of_mem_l1TypicalSet hp hx,
    eventually_prob_l1TypicalSet_gt hp hδ, ?_⟩
  filter_upwards [eventually_card_l1TypicalSet_ge hp hδ] with n hn
  exact ⟨hn, card_l1TypicalSet_le hp n δ⟩

/-- **Theorem 6.3.** (6.36) -/
alias theorem_6_3 := exists_eventually_prob_l1TypicalSet_compl_lt

/-- **Lemma 6.4 (Chernoff Bound).** (6.37)–(6.38), for an event of positive probability. -/
theorem lemma_6_4 {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (Y : Ω → ℝ) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    (0 < prob μ (univ.filter fun ω => a ≤ Y ω) →
      log (prob μ (univ.filter fun ω => a ≤ Y ω)) ≤
        -(s * a) + log (expect μ fun ω => exp (s * Y ω))) ∧
    (0 < prob μ (univ.filter fun ω => Y ω ≤ a) →
      log (prob μ (univ.filter fun ω => Y ω ≤ a)) ≤
        s * a + log (expect μ fun ω => exp (-s * Y ω))) := by
  have key : ∀ {P E c : ℝ}, 0 < P → P ≤ exp c * E → log P ≤ c + log E := by
    intro P E c hP h
    have hE : 0 < E := by
      by_contra hE
      have := mul_nonpos_of_nonneg_of_nonpos (exp_pos c).le (not_lt.1 hE)
      linarith
    have h₁ := log_le_log hP h
    rwa [log_mul (exp_pos c).ne' hE.ne', log_exp] at h₁
  exact ⟨fun hP => key hP (prob_ge_le_exp_mul_expect hμ Y a hs),
    fun hP => key hP (prob_le_le_exp_mul_expect hμ Y a hs)⟩

/-- **Proposition 6.5.** With `η = δ (-log minₓ p(x))`, which tends to `0` as `δ → 0`. -/
alias proposition_6_5 := l1TypicalSet_subset_typicalSet

/-- **Theorem 6.7 (Consistency).** -/
theorem theorem_6_7 {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {δ : ℝ} {x : Fin n → α} {y : Fin n → β}
    (h : (x, y) ∈ jointL1TypicalSet q n δ) :
    x ∈ l1TypicalSet (margFst q) n δ ∧ y ∈ l1TypicalSet (margSnd q) n δ :=
  ⟨fst_mem_l1TypicalSet hq h, snd_mem_l1TypicalSet hq h⟩

/-- **Theorem 6.8 (Preservation).** (6.96)–(6.97) -/
alias theorem_6_8 := comp_mem_l1TypicalSet

/-- **Theorem 6.9 (Strong JAEP).** (6.106)–(6.108), with `λ = δ (-log min p(x, y))`. -/
theorem theorem_6_9 {q : α × β → ℝ} (hq : IsPMF q) {δ : ℝ} (hδ : 0 < δ) :
    (∀ (n : ℕ) (z : (Fin n → α) × (Fin n → β)), z ∈ jointL1TypicalSet q n δ →
      exp (-(n * (entropy q + δ * maxNegLog q))) ≤ jointIid q n z ∧
        jointIid q n z ≤ exp (-(n * (entropy q - δ * maxNegLog q)))) ∧
    (∀ᶠ n in atTop, 1 - δ < prob (jointIid q n) (jointL1TypicalSet q n δ)) ∧
    ∀ᶠ n : ℕ in atTop, (1 - δ) * exp (n * (entropy q - δ * maxNegLog q)) ≤
        (jointL1TypicalSet q n δ).card ∧
      ((jointL1TypicalSet q n δ).card : ℝ) ≤ exp (n * (entropy q + δ * maxNegLog q)) := by
  refine ⟨fun n z hz => exp_le_jointIid_of_mem_jointL1TypicalSet hq hz,
    eventually_prob_jointL1TypicalSet_gt hq hδ, ?_⟩
  filter_upwards [eventually_card_jointL1TypicalSet_ge hq hδ] with n hn
  exact ⟨hn, card_jointL1TypicalSet_le hq n δ⟩

/-- **Theorem 6.10.** (6.111) -/
alias theorem_6_10 := exists_card_condL1TypicalSet_bounds

/-- **Lemma 6.11.** (6.112) -/
theorem lemma_6_11 {n : ℕ} (hn : 0 < n) :
    n * log n - n < log n.factorial ∧ log n.factorial < (n + 1) * log (n + 1) - n :=
  ⟨mul_log_sub_lt_log_factorial hn, log_factorial_lt hn⟩

/-- **Corollary 6.12.** (6.148) -/
alias corollary_6_12 := eventually_card_l1TypicalProjection_ge

/-- **Proposition 6.13.** (6.152) -/
alias proposition_6_13 := eventually_prob_l1TypicalProjection_gt

end InfoTheory.Yeung
