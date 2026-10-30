/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.TypicalSet

/-!
# High-probability sets and the typical set

Any set `B ⊆ 𝒳ⁿ` of probability at least `1 - δ` has at least about `e^{nH}` elements, so the
typical set is, to first order in the exponent, as small as the smallest high-probability set.

## Main definitions

* `ExpEq a b`, with notation `a ≐ b`: `aₙ` and `bₙ` are equal to first order in the exponent,
  `(1/n) log (aₙ / bₙ) → 0`.
* `minHighProbCard p n δ`: the size `|B_δ^(n)|` of a smallest set of sequences of probability at
  least `1 - δ`.

## Main statements

* `log_card_gt_of_prob_ge`: Theorem 3.3.1, if `Pr{B} ≥ 1 - δ` with `δ < 1`, then
  `(1/n) log |B| > H - δ'` for `n` large, uniformly in `B`.
* `tendsto_log_minHighProbCard`, `minHighProbCard_expEq`: `|B_δ^(n)| ≐ e^{nH}` (3.30).
* `eventually_log_card_typicalSet`: `(1/n) log |A_ε^(n)|` lies eventually in `(H - ε - η, H + ε]`.
* `exists_minHighProbSet_mem`: some smallest high-probability set contains any given most
  probable sequence.

## Implementation notes

The book states Theorem 3.3.1 for `δ < 1/2` and `Pr{B} > 1 - δ`; we prove it for every `δ < 1`
and `Pr{B} ≥ 1 - δ`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 3.3 and
  Problem 3.11
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- **Theorem 3.3.1.** Let `X₁, …, Xₙ` be i.i.d. `∼ p`. For `δ < 1` and any `δ' > 0`, for `n`
sufficiently large every set `B ⊆ 𝒳ⁿ` with `Pr{B} ≥ 1 - δ` satisfies `(1/n) log |B| > H - δ'`
(3.25). -/
theorem log_card_gt_of_prob_ge {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ : δ < 1) {δ' : ℝ}
    (hδ' : 0 < δ') :
    ∀ᶠ n : ℕ in atTop, ∀ B : Finset (Fin n → α), 1 - δ ≤ prob (iidPMF p n) B →
      entropy p - δ' < log B.card / n := by
  classical
  set ε := min (δ' / 2) ((1 - δ) / 2) with hε_def
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  set c := (1 - δ) / 2 with hc_def
  have hc : 0 < c := by linarith
  have hlim : Tendsto (fun n : ℕ => log c / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [eventually_prob_typicalSet_gt hp hε, eventually_gt_atTop 0,
    hlim.eventually (lt_mem_nhds (show -(δ' / 2) < 0 by linarith))] with n hA hn hlog B hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A := typicalSet p n ε
  -- `Pr{A ∩ B} > 1 - ε - δ ≥ c`, by Problem 3.11(a).
  have hAB := prob_add_prob_sub_one_le_prob_inter (iidPMF_isPMF hp n) A B
  have hεc : ε ≤ c := min_le_right _ _
  have h1 : c < prob (iidPMF p n) (A ∩ B) := by linarith
  -- `Pr{A ∩ B} ≤ |A ∩ B| e^{-n(H-ε)} ≤ |B| e^{-n(H-ε)}`.
  have h2 : prob (iidPMF p n) (A ∩ B) ≤ (A ∩ B).card * exp (-(n * (entropy p - ε))) :=
    prob_le_card_mul fun x hx => (mem_typicalSet.1 (mem_inter.1 hx).1).2
  have h3 : ((A ∩ B).card : ℝ) ≤ B.card := by exact_mod_cast card_le_card inter_subset_right
  have h4 : c < B.card * exp (-(n * (entropy p - ε))) :=
    h1.trans_le (h2.trans (mul_le_mul_of_nonneg_right h3 (exp_pos _).le))
  have hB0 : (0 : ℝ) < B.card := by
    by_contra! h
    have : (B.card : ℝ) * exp (-(n * (entropy p - ε))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (exp_pos _).le
    linarith
  -- Take logarithms.
  have h5 : log c < log B.card - n * (entropy p - ε) := by
    have := log_lt_log hc h4
    rwa [log_mul hB0.ne' (exp_pos _).ne', log_exp, ← sub_eq_add_neg] at this
  rw [lt_div_iff₀ hn']
  have hεδ : ε ≤ δ' / 2 := min_le_left _ _
  have h6 : log c > -(δ' / 2) * n := by
    rw [lt_div_iff₀ hn'] at hlog
    linarith
  nlinarith

/-! ### Equality to first order in the exponent -/

/-- **Definition (3.26).** `aₙ ≐ bₙ` means that `aₙ` and `bₙ` are equal to first order in the
exponent: `(1/n) log (aₙ / bₙ) → 0`. -/
def ExpEq (a b : ℕ → ℝ) : Prop := Tendsto (fun n => log (a n / b n) / n) atTop (𝓝 0)

/-- `a ≐ b`: `aₙ` and `bₙ` are equal to first order in the exponent. -/
scoped infix:50 " ≐ " => ExpEq

/-- `aₙ ≐ e^{nc}` iff `(1/n) log aₙ → c`, for `aₙ` eventually positive. -/
lemma expEq_exp_iff {a : ℕ → ℝ} (ha : ∀ᶠ n in atTop, 0 < a n) (c : ℝ) :
    a ≐ (fun n => exp (n * c)) ↔ Tendsto (fun n => log (a n) / n) atTop (𝓝 c) := by
  have h : (fun n : ℕ => log (a n / exp (n * c)) / n) =ᶠ[atTop]
      fun n => log (a n) / n - c := by
    filter_upwards [ha, eventually_gt_atTop 0] with n han hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [log_div han.ne' (exp_pos _).ne', log_exp]
    field_simp
  rw [ExpEq, tendsto_congr' h]
  constructor
  · intro h'; simpa using h'.add_const c
  · intro h'; simpa using h'.sub_const c

/-! ### The smallest high-probability set -/

/-- The size `|B_δ^(n)|` of a smallest set `B ⊆ 𝒳ⁿ` with `Pr{B} ≥ 1 - δ`. -/
def minHighProbCard (p : α → ℝ) (n : ℕ) (δ : ℝ) : ℕ :=
  sInf {k | ∃ B : Finset (Fin n → α), B.card = k ∧ 1 - δ ≤ prob (iidPMF p n) B}

omit [Fintype α] in
lemma minHighProbCard_le {p : α → ℝ} {n : ℕ} {δ : ℝ} {B : Finset (Fin n → α)}
    (hB : 1 - δ ≤ prob (iidPMF p n) B) : minHighProbCard p n δ ≤ B.card :=
  Nat.sInf_le ⟨B, rfl, hB⟩

/-- A smallest set of probability at least `1 - δ` exists. -/
lemma exists_minHighProbSet {p : α → ℝ} (hp : IsPMF p) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ B : Finset (Fin n → α), B.card = minHighProbCard p n δ ∧ 1 - δ ≤ prob (iidPMF p n) B :=
  Nat.sInf_mem (s := {k | ∃ B : Finset (Fin n → α), B.card = k ∧ 1 - δ ≤ prob (iidPMF p n) B})
    ⟨_, univ, rfl, by rw [prob_univ (iidPMF_isPMF hp n)]; linarith⟩

lemma minHighProbCard_pos {p : α → ℝ} (hp : IsPMF p) (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) : 0 < minHighProbCard p n δ := by
  obtain ⟨B, hB, hpB⟩ := exists_minHighProbSet hp n hδ0
  rw [← hB, card_pos]
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  rw [h, prob_empty] at hpB
  linarith

/-- **(3.30)** The smallest set of probability at least `1 - δ` has `(1/n) log |B_δ^(n)| → H`. -/
theorem tendsto_log_minHighProbCard {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    Tendsto (fun n => log (minHighProbCard p n δ) / n) atTop (𝓝 (entropy p)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- Lower bound, from Theorem 3.3.1.
    filter_upwards [log_card_gt_of_prob_ge hp hδ1 (sub_pos.2 ha)] with n hn
    obtain ⟨B, hB, hpB⟩ := exists_minHighProbSet hp n hδ0.le
    have := hn B hpB
    rw [hB] at this
    linarith
  · -- Upper bound, from the typical set.
    set ε := min δ ((a - entropy p) / 2)
    have hε : 0 < ε := lt_min hδ0 (by linarith)
    filter_upwards [eventually_prob_typicalSet_gt hp hε, eventually_gt_atTop 0] with n hA hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : minHighProbCard p n δ ≤ (typicalSet p n ε).card :=
      minHighProbCard_le (by linarith [min_le_left δ ((a - entropy p) / 2)])
    have hpos : (0 : ℝ) < minHighProbCard p n δ := by
      exact_mod_cast minHighProbCard_pos hp n hδ0.le hδ1
    have h1 : log (minHighProbCard p n δ) ≤ n * (entropy p + ε) := by
      rw [log_le_iff_le_exp hpos]
      exact (Nat.cast_le.2 hle).trans (card_typicalSet_le hp n ε)
    rw [div_lt_iff₀ hn']
    have : ε ≤ (a - entropy p) / 2 := min_le_right _ _
    nlinarith

/-- **(3.30)** For `0 < δ < 1`, `|B_δ^(n)| ≐ e^{nH}`; in bits, `|B_δ^(n)| ≐ 2^{nH}`. -/
theorem minHighProbCard_expEq {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (fun n => (minHighProbCard p n δ : ℝ)) ≐ (fun n => exp (n * entropy p)) :=
  (expEq_exp_iff (Eventually.of_forall fun n => by
    exact_mod_cast minHighProbCard_pos hp n hδ0.le hδ1) _).2
    (tendsto_log_minHighProbCard hp hδ0 hδ1)

/-- **(3.27)** The typical set has `e^{nH}` elements to first order in the exponent: for
`0 < ε < 1` and `η > 0`, eventually `H - ε - η < (1/n) log |A_ε^(n)| ≤ H + ε`. -/
theorem eventually_log_card_typicalSet {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, entropy p - ε - η < log (typicalSet p n ε).card / n ∧
      log (typicalSet p n ε).card / n ≤ entropy p + ε := by
  have hlim : Tendsto (fun n : ℕ => log (1 - ε) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [eventually_card_typicalSet_gt hp hε0, eventually_gt_atTop 0,
    hlim.eventually (lt_mem_nhds (show -η < 0 by linarith))] with n hcard hn hlog
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1ε : 0 < 1 - ε := by linarith
  have hpos : (0 : ℝ) < (typicalSet p n ε).card :=
    (mul_pos h1ε (exp_pos _)).trans hcard
  constructor
  · have := log_lt_log (mul_pos h1ε (exp_pos _)) hcard
    rw [log_mul h1ε.ne' (exp_pos _).ne', log_exp] at this
    rw [lt_div_iff₀ hn']
    rw [lt_div_iff₀ hn'] at hlog
    nlinarith
  · rw [div_le_iff₀ hn', mul_comm, log_le_iff_le_exp hpos]
    exact card_typicalSet_le hp n ε

/-! ### Most probable sequences -/

/-- Exchanging an element of `B` for a most probable outcome `a` does not decrease the
probability: there is `B'` with `|B'| ≤ |B|`, `a ∈ B'` and `Pr{B'} ≥ Pr{B}`. -/
lemma exists_card_le_mem_prob_ge {Ω : Type*} {μ : Ω → ℝ} {a : Ω}
    (ha : ∀ ω, μ ω ≤ μ a) {B : Finset Ω} (hB : B.Nonempty) :
    ∃ B' : Finset Ω, B'.card ≤ B.card ∧ a ∈ B' ∧ prob μ B ≤ prob μ B' := by
  classical
  by_cases haB : a ∈ B
  · exact ⟨B, le_rfl, haB, le_rfl⟩
  · obtain ⟨b, hb⟩ := hB
    refine ⟨insert a (B.erase b), ?_, mem_insert_self a _, ?_⟩
    · rw [card_insert_of_notMem (fun h => haB (mem_of_mem_erase h)), card_erase_of_mem hb]
      have := card_pos.2 ⟨b, hb⟩
      omega
    · rw [prob, prob, sum_insert (fun h => haB (mem_of_mem_erase h)), ← add_sum_erase B μ hb]
      linarith [ha b]

/-- Some smallest set of probability at least `1 - δ` contains a given most probable sequence. -/
theorem exists_minHighProbSet_mem {p : α → ℝ} (hp : IsPMF p) (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) {a : Fin n → α} (ha : ∀ x, iidPMF p n x ≤ iidPMF p n a) :
    ∃ B : Finset (Fin n → α), B.card = minHighProbCard p n δ ∧
      1 - δ ≤ prob (iidPMF p n) B ∧ a ∈ B := by
  classical
  obtain ⟨B, hB, hpB⟩ := exists_minHighProbSet hp n hδ0
  have hne : B.Nonempty := by
    rw [← card_pos, hB]; exact minHighProbCard_pos hp n hδ0 hδ1
  obtain ⟨B', hcard, haB', hprob⟩ := exists_card_le_mem_prob_ge ha hne
  have hpB' : 1 - δ ≤ prob (iidPMF p n) B' := hpB.trans hprob
  exact ⟨B', le_antisymm (hcard.trans hB.le) (minHighProbCard_le hpB'), hpB', haB'⟩

end InfoTheory
