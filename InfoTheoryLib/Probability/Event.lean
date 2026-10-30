/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.FinitePMF

/-!
# Events and their probabilities

An event in a finite probability space `(Ω, μ)` is a `Finset Ω`, and its probability is
`prob μ S = ∑_{ω ∈ S} μ(ω)`. Events defined by a predicate are written `univ.filter P`.

## Main definitions

* `prob μ S`: the probability `Pr{S}` of an event.

## Main statements

* `prob_compl`: `Pr{Sᶜ} = 1 - Pr{S}`.
* `prob_add_prob_sub_one_le_prob_inter`: `Pr{S ∩ T} ≥ Pr{S} + Pr{T} - 1`.
* `prob_biUnion_le`: the union bound `Pr{⋃ᵢ Sᵢ} ≤ ∑ᵢ Pr{Sᵢ}`.
* `card_mul_le_prob`, `prob_le_card_mul`: if every outcome of `S` has probability at least
  (at most) `c`, then `Pr{S}` is at least (at most) `|S| c`. These are the counting arguments
  behind the bounds on the size of the typical set.
* `prob_le_prob_of_ae`: an inclusion of events that holds outside a set of probability zero
  gives an inequality of probabilities.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Chapter 3
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω : Type*} [Fintype Ω]

/-- The probability `Pr{S} = ∑_{ω ∈ S} μ(ω)` of an event `S`. -/
def prob (μ : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ ω ∈ S, μ ω

omit [Fintype Ω] in
lemma prob_nonneg {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (S : Finset Ω) : 0 ≤ prob μ S :=
  sum_nonneg fun ω _ => hμ ω

lemma prob_univ {μ : Ω → ℝ} (hμ : IsPMF μ) : prob μ univ = 1 := hμ.sum_eq_one

omit [Fintype Ω] in
@[simp] lemma prob_empty (μ : Ω → ℝ) : prob μ ∅ = 0 := sum_empty

omit [Fintype Ω] in
lemma prob_mono {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {S T : Finset Ω} (h : S ⊆ T) :
    prob μ S ≤ prob μ T :=
  sum_le_sum_of_subset_of_nonneg h fun ω _ _ => hμ ω

lemma prob_le_one {μ : Ω → ℝ} (hμ : IsPMF μ) (S : Finset Ω) : prob μ S ≤ 1 :=
  (prob_mono hμ.nonneg (subset_univ S)).trans_eq (prob_univ hμ)

lemma prob_add_prob_compl [DecidableEq Ω] {μ : Ω → ℝ} (hμ : IsPMF μ) (S : Finset Ω) :
    prob μ S + prob μ Sᶜ = 1 := by
  rw [prob, prob, sum_add_sum_compl, hμ.sum_eq_one]

lemma prob_compl [DecidableEq Ω] {μ : Ω → ℝ} (hμ : IsPMF μ) (S : Finset Ω) :
    prob μ Sᶜ = 1 - prob μ S := by
  linarith [prob_add_prob_compl hμ S]

omit [Fintype Ω] in
lemma prob_union_le [DecidableEq Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (S T : Finset Ω) :
    prob μ (S ∪ T) ≤ prob μ S + prob μ T := by
  rw [prob, prob, prob, ← sum_union_inter]
  linarith [sum_nonneg fun ω (_ : ω ∈ S ∩ T) => hμ ω]

omit [Fintype Ω] in
/-- The union bound `Pr{⋃ᵢ Sᵢ} ≤ ∑ᵢ Pr{Sᵢ}`. -/
lemma prob_biUnion_le [DecidableEq Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {ι : Type*}
    (s : Finset ι) (S : ι → Finset Ω) : prob μ (s.biUnion S) ≤ ∑ i ∈ s, prob μ (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    exact (prob_union_le hμ _ _).trans (by linarith)

/-- If `Pr{S} ≥ 1 - ε₁` and `Pr{T} ≥ 1 - ε₂`, then `Pr{S ∩ T} ≥ 1 - ε₁ - ε₂` (Problem 3.11(a) of
[cover2006]), in the form `Pr{S} + Pr{T} - 1 ≤ Pr{S ∩ T}`. -/
lemma prob_add_prob_sub_one_le_prob_inter [DecidableEq Ω] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (S T : Finset Ω) : prob μ S + prob μ T - 1 ≤ prob μ (S ∩ T) := by
  have h := sum_union_inter (s₁ := S) (s₂ := T) (f := μ)
  have hu := prob_le_one hμ (S ∪ T)
  rw [prob] at hu ⊢
  rw [prob, prob]
  linarith

omit [Fintype Ω] in
/-- If every outcome of `S` has probability at least `c`, then `|S| c ≤ Pr{S}`. -/
lemma card_mul_le_prob {μ : Ω → ℝ} {S : Finset Ω} {c : ℝ} (h : ∀ ω ∈ S, c ≤ μ ω) :
    S.card * c ≤ prob μ S := by
  rw [prob, ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum h

omit [Fintype Ω] in
/-- If every outcome of `S` has probability at most `c`, then `Pr{S} ≤ |S| c`. -/
lemma prob_le_card_mul {μ : Ω → ℝ} {S : Finset Ω} {c : ℝ} (h : ∀ ω ∈ S, μ ω ≤ c) :
    prob μ S ≤ S.card * c := by
  rw [prob, ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum h

omit [Fintype Ω] in
/-- If `S ⊆ T` up to outcomes of probability zero, then `Pr{S} ≤ Pr{T}`. -/
lemma prob_le_prob_of_ae {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {S T : Finset Ω}
    (h : ∀ ω ∈ S, μ ω ≠ 0 → ω ∈ T) : prob μ S ≤ prob μ T := by
  classical
  calc prob μ S = ∑ ω ∈ S.filter (fun ω => μ ω ≠ 0), μ ω := by
        rw [prob, sum_filter_ne_zero]
    _ ≤ prob μ T := sum_le_sum_of_subset_of_nonneg
        (fun ω hω => h ω (mem_filter.1 hω).1 (mem_filter.1 hω).2) fun ω _ _ => hμ ω

omit [Fintype Ω] in
/-- Events that agree outside a set of probability zero have the same probability. -/
lemma prob_congr_ae {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {S T : Finset Ω}
    (h : ∀ ω, μ ω ≠ 0 → (ω ∈ S ↔ ω ∈ T)) : prob μ S = prob μ T :=
  le_antisymm (prob_le_prob_of_ae hμ fun ω hω h0 => (h ω h0).1 hω)
    (prob_le_prob_of_ae hμ fun ω hω h0 => (h ω h0).2 hω)

/-- The law of a random variable is the probability of the corresponding event:
`Pr{X = a} = Pr{ω | X ω = a}`. -/
lemma dist_eq_prob {α : Type*} [DecidableEq α] (μ : Ω → ℝ) (X : Ω → α) (a : α) :
    dist μ X a = prob μ (univ.filter fun ω => X ω = a) := by
  rw [prob, sum_filter, dist]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : X ω = a <;> simp [h]

/-- The probability of an event is the expectation of its indicator. -/
lemma prob_eq_expect [DecidableEq Ω] (μ : Ω → ℝ) (S : Finset Ω) :
    prob μ S = expect μ (fun ω => if ω ∈ S then 1 else 0) := by
  simp [prob, expect, ite_mul, sum_ite_mem]

end InfoTheory
