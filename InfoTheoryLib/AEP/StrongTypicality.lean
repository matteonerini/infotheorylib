/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.JointTypicality
public import InfoTheoryLib.Probability.WeakLaw

/-!
# Strongly typical sequences

A sequence `xⁿ` is `ε`-strongly typical for `p` if the relative frequency `N(a|xⁿ)/n` of every
symbol `a` with `p(a) > 0` is within `ε/|𝒳|` of `p(a)`, and the symbols with `p(a) = 0` do not
occur. A pair of sequences is jointly strongly typical if the sequence of pairs is strongly
typical for the joint pmf. By the weak law of large numbers, i.i.d. sequences are strongly typical
with probability tending to `1`.

## Main definitions

* `symbolCount x a`: the number `N(a|xⁿ)` of occurrences of `a` in `xⁿ`.
* `strongTypicalSet p n ε`: the strongly typical set `A_ε^{*(n)}`, (10.106).
* `jointStrongTypicalSet q n ε`: the jointly strongly typical set, (10.107).

## Main statements

* `tendsto_prob_strongTypicalSet`, `tendsto_prob_jointStrongTypicalSet`: **Lemma 10.6.1**.
* `mem_strongTypicalSet_of_mem_joint`: a jointly strongly typical pair has a strongly typical
  first sequence.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 10.6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

open Classical in
/-- The number `N(a|xⁿ)` of occurrences of the symbol `a` in the sequence `xⁿ`. -/
def symbolCount {n : ℕ} (x : Fin n → α) (a : α) : ℕ := #(univ.filter fun i => x i = a)

open Classical in
omit [Fintype α] in
lemma symbolCount_eq_sum {n : ℕ} (x : Fin n → α) (a : α) :
    (symbolCount x a : ℝ) = ∑ i, if x i = a then 1 else 0 := by
  rw [symbolCount, natCast_card_filter]

open Classical in
/-- **Definition (10.106).** The strongly typical set `A_ε^{*(n)}`: the sequences in which every
symbol `a` with `p(a) > 0` has relative frequency `|N(a|xⁿ)/n - p(a)| < ε/|𝒳|`, and no symbol with
`p(a) = 0` occurs. -/
def strongTypicalSet (p : α → ℝ) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) :=
  univ.filter fun x => ∀ a, (0 < p a → |(symbolCount x a : ℝ) / n - p a| < ε / Fintype.card α) ∧
    (p a = 0 → symbolCount x a = 0)

lemma mem_strongTypicalSet {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α} :
    x ∈ strongTypicalSet p n ε ↔ ∀ a,
      (0 < p a → |(symbolCount x a : ℝ) / n - p a| < ε / Fintype.card α) ∧
        (p a = 0 → symbolCount x a = 0) := by
  classical
  simp [strongTypicalSet]

/-- **Definition (10.107).** The jointly strongly typical set: the pairs `(xⁿ, yⁿ)` whose sequence
of pairs is strongly typical for the joint pmf `q`, that is
`|N(a, b|xⁿ, yⁿ)/n - q(a, b)| < ε/(|𝒳||𝒴|)` for `q(a, b) > 0` and `N(a, b|xⁿ, yⁿ) = 0` for
`q(a, b) = 0`. -/
def jointStrongTypicalSet (q : α × β → ℝ) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → α) × (Fin n → β)) :=
  open Classical in univ.filter fun z => zipSeq z.1 z.2 ∈ strongTypicalSet q n ε

lemma mem_jointStrongTypicalSet {q : α × β → ℝ} {n : ℕ} {ε : ℝ}
    {z : (Fin n → α) × (Fin n → β)} :
    z ∈ jointStrongTypicalSet q n ε ↔ zipSeq z.1 z.2 ∈ strongTypicalSet q n ε := by
  classical
  simp [jointStrongTypicalSet]

/-- **Section 10.6.** If `(xⁿ, yⁿ)` is jointly strongly typical, then `xⁿ` is strongly typical for
the first marginal. -/
theorem mem_strongTypicalSet_of_mem_joint {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) {x : Fin n → α} {y : Fin n → β}
    (h : (x, y) ∈ jointStrongTypicalSet q n ε) : x ∈ strongTypicalSet (margFst q) n ε := by
  classical
  rw [mem_jointStrongTypicalSet, mem_strongTypicalSet] at h
  rw [mem_strongTypicalSet]
  -- `N(a|xⁿ) = ∑_b N(a, b|xⁿ, yⁿ)`.
  have hcount : ∀ a, (symbolCount x a : ℝ) = ∑ b, (symbolCount (zipSeq x y) (a, b) : ℝ) := by
    intro a
    simp only [symbolCount_eq_sum, zipSeq, Prod.mk.injEq]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    by_cases hx : x i = a
    · simp [hx]
    · simp [hx]
  have hmarg : ∀ a, margFst q a = ∑ b, q (a, b) := fun a => dist_fst q a
  have hcard : (Fintype.card (α × β) : ℝ) = Fintype.card α * Fintype.card β := by
    simp [Fintype.card_prod]
  intro a
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨b₀, hb₀⟩ : ∃ b, 0 < q (a, b) := by
      by_contra hne
      push Not at hne
      have : margFst q a ≤ 0 := (hmarg a).trans_le (sum_nonpos fun b _ => hne b)
      linarith
    have hβ : 0 < Fintype.card β := Fintype.card_pos_iff.2 ⟨b₀⟩
    have hα : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
    set c := ε / Fintype.card (α × β)
    have hc : 0 < c := div_pos hε (by rw [hcard]; positivity)
    have hterm : ∀ b, |(symbolCount (zipSeq x y) (a, b) : ℝ) / n - q (a, b)| < c := by
      intro b
      rcases (hq.nonneg (a, b)).eq_or_lt with h0 | h0
      · rw [← h0, (h (a, b)).2 h0.symm]
        simpa using hc
      · exact (h (a, b)).1 h0
    calc |(symbolCount x a : ℝ) / n - margFst q a|
        = |∑ b, ((symbolCount (zipSeq x y) (a, b) : ℝ) / n - q (a, b))| := by
          rw [hcount, hmarg, sum_sub_distrib, sum_div]
      _ ≤ ∑ b, |(symbolCount (zipSeq x y) (a, b) : ℝ) / n - q (a, b)| := abs_sum_le_sum_abs _ _
      _ < ∑ _b : β, c := sum_lt_sum_of_nonempty ⟨b₀, mem_univ _⟩ fun b _ => hterm b
      _ = ε / Fintype.card α := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          simp only [c]
          rw [hcard]
          field_simp
  · have h0 : ∀ b, q (a, b) = 0 := fun b =>
      (sum_eq_zero_iff_of_nonneg fun b _ => hq.nonneg (a, b)).1 ((hmarg a).symm.trans ha) b
        (mem_univ b)
    have : (symbolCount x a : ℝ) = 0 := by
      rw [hcount]
      exact sum_eq_zero fun b _ => by rw [(h (a, b)).2 (h0 b), Nat.cast_zero]
    exact_mod_cast this

/-- **Lemma 10.6.1.** For `Xᵢ` i.i.d. `∼ p`, `Pr{A_ε^{*(n)}} → 1`: by the weak law of large numbers
the relative frequency of each symbol tends to its probability, and the symbols of probability
`0` occur with probability `0`. -/
theorem tendsto_prob_strongTypicalSet {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF p n) (strongTypicalSet p n ε)) atTop (𝓝 1) := by
  classical
  have hα : 0 < Fintype.card α := card_pos_of_isPMF hp
  set c := ε / Fintype.card α
  have hc : 0 < c := div_pos hε (by exact_mod_cast hα)
  set f : α → α → ℝ := fun a b => if b = a then 1 else 0
  set B : α → ∀ n : ℕ, Finset (Fin n → α) := fun a n =>
    univ.filter fun x => c ≤ |(sampleMean fun i => f a (x i)) - expect p (f a)|
  have hB : ∀ a, Tendsto (fun n => prob (iidPMF p n) (B a n)) atTop (𝓝 0) := fun a =>
    weak_law hp (f a) c hc
  have hexp : ∀ a, expect p (f a) = p a := fun a => by simp [expect, f]
  have hmean : ∀ {n : ℕ} (x : Fin n → α) (a : α),
      (sampleMean fun i => f a (x i)) = (symbolCount x a : ℝ) / n := fun x a => by
    simp [sampleMean, f, symbolCount_eq_sum]
  -- Outside a set of probability `0`, an atypical sequence is in some `B a`.
  have hcompl : ∀ n, prob (iidPMF p n) (strongTypicalSet p n ε)ᶜ ≤
      ∑ a, prob (iidPMF p n) (B a n) := by
    intro n
    refine (prob_le_prob_of_ae (iidPMF_nonneg hp.nonneg) (T := univ.biUnion fun a => B a n)
      fun x hx hx0 => ?_).trans (prob_biUnion_le (iidPMF_nonneg hp.nonneg) _ _)
    rw [mem_compl, mem_strongTypicalSet, not_forall] at hx
    obtain ⟨a, ha⟩ := hx
    rw [mem_biUnion]
    refine ⟨a, mem_univ a, ?_⟩
    by_cases hpa : 0 < p a
    · have hge : c ≤ |(symbolCount x a : ℝ) / n - p a| := by
        by_contra hlt
        exact ha ⟨fun _ => not_le.1 hlt, fun h0 => absurd h0 hpa.ne'⟩
      simp only [B, mem_filter, mem_univ, true_and, hmean, hexp]
      exact hge
    · have hpa0 : p a = 0 := le_antisymm (not_lt.1 hpa) (hp.nonneg a)
      exfalso
      have hN : symbolCount x a ≠ 0 := fun hN =>
        ha ⟨fun h => absurd h hpa, fun _ => hN⟩
      obtain ⟨i, hi⟩ : ∃ i, x i = a := by
        by_contra hne
        push Not at hne
        exact hN (card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ => hne i))
      exact hx0 (prod_eq_zero (mem_univ i) (by rw [hi, hpa0]))
  have hlow : ∀ n, 1 - ∑ a, prob (iidPMF p n) (B a n) ≤
      prob (iidPMF p n) (strongTypicalSet p n ε) := fun n => by
    have := prob_compl (iidPMF_isPMF hp n) (strongTypicalSet p n ε)
    linarith [hcompl n]
  have hsum : Tendsto (fun n => 1 - ∑ a, prob (iidPMF p n) (B a n)) atTop (𝓝 1) := by
    simpa using (tendsto_finsetSum univ fun a _ => hB a).const_sub 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hsum tendsto_const_nhds hlow
    fun n => prob_le_one (iidPMF_isPMF hp n) _

/-- **Lemma 10.6.1 (pairs).** For `(Xᵢ, Yᵢ)` i.i.d. `∼ q`, `Pr{A_ε^{*(n)}(X, Y)} → 1`. -/
theorem tendsto_prob_jointStrongTypicalSet {q : α × β → ℝ} (hq : IsPMF q) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (jointIid q n) (jointStrongTypicalSet q n ε)) atTop (𝓝 1) := by
  classical
  refine (tendsto_prob_strongTypicalSet hq hε).congr fun n => ?_
  have h := sum_jointIid q n fun w => if w ∈ strongTypicalSet q n ε then 1 else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  have e1 : ∑ ω ∈ strongTypicalSet q n ε, iidPMF q n ω =
      ∑ x, if x ∈ strongTypicalSet q n ε then iidPMF q n x else 0 := by
    rw [sum_ite_mem, univ_inter]
  have e2 : ∑ ω ∈ jointStrongTypicalSet q n ε, jointIid q n ω =
      ∑ x, if zipSeq x.1 x.2 ∈ strongTypicalSet q n ε then jointIid q n x else 0 := by
    rw [jointStrongTypicalSet, sum_filter]
  rw [prob, prob, e1, e2, h]

end InfoTheory
