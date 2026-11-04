/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.StrongTypicality
public import InfoTheoryLib.AEP.TypicalSet
public import InfoTheoryLib.Statistics.Types

/-!
# Robust typicality

A sequence `xⁿ ∈ 𝒳ⁿ` is `ε`-typical for a pmf `p` if its empirical pmf (its type) `π(x|xⁿ)` is
within a relative error `ε` of `p`: `|π(x|xⁿ) - p(x)| ≤ ε p(x)` for every `x`. This notion, the
robust typicality of Orlitsky and Roche, is the one used by El Gamal and Kim in their lecture
notes. Symbols of probability zero do not occur in a typical sequence, and the average of a
nonnegative function along a typical sequence is within a factor `1 ± ε` of its expectation (the
typical average lemma). Consequently a typical sequence has probability `≐ e^{-nH(X)}`, there are
`≐ e^{nH(X)}` typical sequences, and an i.i.d. sequence is typical with probability tending to
`1`.

Typicality is preserved by functions: if `xⁿ` is typical for `p`, then `f(xⁿ)` is typical for the
law of `f(X)`. Applied to the projections of a sequence of tuples, this gives the typicality of
subtuples, in particular of the components of a jointly typical pair.

## Main definitions

* `robustTypicalSet p n ε`: the typical set `T_ε^(n)(X)`.

## Main statements

* `card_mul_le_sum_of_mem_robustTypicalSet`, `sum_le_card_mul_of_mem_robustTypicalSet`: the
  typical average lemma.
* `le_iidPMF_of_mem_robustTypicalSet`, `iidPMF_le_of_mem_robustTypicalSet`: property 1,
  `e^{-n(H(X) + δ(ε))} ≤ p(xⁿ) ≤ e^{-n(H(X) - δ(ε))}` with `δ(ε) = εH(X)`.
* `card_robustTypicalSet_le`: property 2, `|T_ε^(n)(X)| ≤ e^{n(H(X) + δ(ε))}`.
* `tendsto_prob_robustTypicalSet`: property 3, `P{Xⁿ ∈ T_ε^(n)(X)} → 1`.
* `eventually_card_robustTypicalSet_ge`: property 4,
  `|T_ε^(n)(X)| ≥ (1 - ε) e^{n(H(X) - δ(ε))}` for `n` large.
* `comp_mem_robustTypicalSet`: typicality is preserved by functions.
* `robustTypicalSet_subset_typicalSet`: robust typicality implies weak typicality.

## Implementation notes

Logarithms are natural, so the notes' `2^{-n(H(X) ± δ(ε))}` are `e^{-n(H(X) ± δ(ε))}` with `H`
in nats. The type of the empty sequence is `0`, so for `n = 0` the typical set is empty unless
`ε ≥ 1`; the statements hold for every `n`. The typical average lemma is stated after
multiplying by `n`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
* [A. Orlitsky and J. R. Roche, *Coding for computing*][orlitsky2001]
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Counting symbols -/

omit [Fintype α] in
/-- `N(a|xⁿ) = 0` for the empty sequence. -/
lemma symbolCount_fin_zero (x : Fin 0 → α) (a : α) : symbolCount x a = 0 := by
  simp [symbolCount]

omit [Fintype α] in
/-- A symbol that occurs in `xⁿ` is counted. -/
lemma one_le_symbolCount {n : ℕ} (x : Fin n → α) (i : Fin n) : 1 ≤ symbolCount x (x i) := by
  classical
  unfold symbolCount
  exact card_pos.2 ⟨i, by simp⟩

/-- `∑ᵢ g(xᵢ) = ∑ₓ N(x|xⁿ) g(x)`: a sum along a sequence only depends on its type. -/
lemma sum_comp_eq_sum_symbolCount {n : ℕ} (x : Fin n → α) (g : α → ℝ) :
    ∑ i, g (x i) = ∑ a, (symbolCount x a : ℝ) * g a := by
  simp_rw [symbolCount_eq_sum, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single (x i) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-! ### The typical set -/

open Classical in
/-- **Definition (Lecture 2).** The typical set `T_ε^(n)(X)` of the pmf `p`: the sequences `xⁿ`
whose empirical pmf satisfies `|π(x|xⁿ) - p(x)| ≤ ε p(x)` for every `x`. -/
def robustTypicalSet (p : α → ℝ) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) :=
  univ.filter fun x => ∀ a, |typeOf x a - p a| ≤ ε * p a

lemma mem_robustTypicalSet {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α} :
    x ∈ robustTypicalSet p n ε ↔ ∀ a, |typeOf x a - p a| ≤ ε * p a := by
  classical
  simp [robustTypicalSet]

variable {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α}

/-- In a typical sequence, `N(a|xⁿ) ≤ n (p(a) + ε p(a))`. -/
lemma symbolCount_le_of_mem_robustTypicalSet (hx : x ∈ robustTypicalSet p n ε) (a : α) :
    (symbolCount x a : ℝ) ≤ n * (p a + ε * p a) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [symbolCount_fin_zero]
  · have h := (abs_le.1 (mem_robustTypicalSet.1 hx a)).2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← mul_typeOf hn x a]
    nlinarith

/-- In a typical sequence, `N(a|xⁿ) ≥ n (p(a) - ε p(a))`. -/
lemma le_symbolCount_of_mem_robustTypicalSet (hx : x ∈ robustTypicalSet p n ε) (a : α) :
    n * (p a - ε * p a) ≤ symbolCount x a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [symbolCount_fin_zero]
  · have h := (abs_le.1 (mem_robustTypicalSet.1 hx a)).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← mul_typeOf hn x a]
    nlinarith

/-- A symbol of probability zero does not occur in a typical sequence. -/
lemma symbolCount_eq_zero_of_mem_robustTypicalSet (hx : x ∈ robustTypicalSet p n ε) {a : α}
    (ha : p a = 0) : symbolCount x a = 0 := by
  have h := symbolCount_le_of_mem_robustTypicalSet hx a
  rw [ha, mul_zero, add_zero, mul_zero] at h
  exact Nat.cast_eq_zero.1 (le_antisymm h (Nat.cast_nonneg _))

/-- Every symbol of a typical sequence has positive probability. -/
lemma pos_of_mem_robustTypicalSet (hp : ∀ a, 0 ≤ p a) (hx : x ∈ robustTypicalSet p n ε)
    (i : Fin n) : 0 < p (x i) := by
  refine (hp (x i)).lt_of_ne fun h => ?_
  have h1 := symbolCount_eq_zero_of_mem_robustTypicalSet hx h.symm
  have h2 := one_le_symbolCount x i
  omega

/-- **Typical average lemma** (upper bound). For `xⁿ ∈ T_ε^(n)(X)` and a nonnegative function
`g`, `(1/n) ∑ᵢ g(xᵢ) ≤ (1 + ε) E g(X)`. -/
theorem sum_le_card_mul_of_mem_robustTypicalSet (hx : x ∈ robustTypicalSet p n ε) {g : α → ℝ}
    (hg : ∀ a, 0 ≤ g a) : ∑ i, g (x i) ≤ n * ((1 + ε) * expect p g) := by
  rw [sum_comp_eq_sum_symbolCount, expect, mul_sum, mul_sum]
  refine sum_le_sum fun a _ => ?_
  calc (symbolCount x a : ℝ) * g a ≤ n * (p a + ε * p a) * g a :=
        mul_le_mul_of_nonneg_right (symbolCount_le_of_mem_robustTypicalSet hx a) (hg a)
    _ = n * ((1 + ε) * (g a * p a)) := by ring

/-- **Typical average lemma** (lower bound). For `xⁿ ∈ T_ε^(n)(X)` and a nonnegative function
`g`, `(1 - ε) E g(X) ≤ (1/n) ∑ᵢ g(xᵢ)`. -/
theorem card_mul_le_sum_of_mem_robustTypicalSet (hx : x ∈ robustTypicalSet p n ε) {g : α → ℝ}
    (hg : ∀ a, 0 ≤ g a) : n * ((1 - ε) * expect p g) ≤ ∑ i, g (x i) := by
  rw [sum_comp_eq_sum_symbolCount, expect, mul_sum, mul_sum]
  refine sum_le_sum fun a _ => ?_
  calc n * ((1 - ε) * (g a * p a)) = n * (p a - ε * p a) * g a := by ring
    _ ≤ (symbolCount x a : ℝ) * g a :=
        mul_le_mul_of_nonneg_right (le_symbolCount_of_mem_robustTypicalSet hx a) (hg a)

/-! ### Properties of typical sequences -/

/-- The probability of a sequence of symbols of positive probability, as `e^{∑ᵢ log p(xᵢ)}`. -/
lemma iidPMF_eq_exp_sum_log (hp : ∀ a, 0 ≤ p a) (hx : x ∈ robustTypicalSet p n ε) :
    iidPMF p n x = exp (-∑ i, -log (p (x i))) := by
  rw [iidPMF, show -∑ i, -log (p (x i)) = ∑ i, log (p (x i)) by simp, exp_sum]
  exact prod_congr rfl fun i _ => (exp_log (pos_of_mem_robustTypicalSet hp hx i)).symm

/-- **Property 1 (Lecture 2)**, lower bound. For `xⁿ ∈ T_ε^(n)(X)`,
`p(xⁿ) ≥ e^{-n(H(X) + δ(ε))}` with `δ(ε) = εH(X)`. -/
theorem le_iidPMF_of_mem_robustTypicalSet (hp : IsPMF p) (hx : x ∈ robustTypicalSet p n ε) :
    exp (-(n * (entropy p + ε * entropy p))) ≤ iidPMF p n x := by
  rw [iidPMF_eq_exp_sum_log hp.nonneg hx]
  have h := sum_le_card_mul_of_mem_robustTypicalSet hx (g := fun a => -log (p a))
    fun a => neg_nonneg.2 (log_nonpos (hp.nonneg a) (hp.le_one a))
  rw [expect_neg_log] at h
  exact exp_le_exp.2 (by linarith)

/-- **Property 1 (Lecture 2)**, upper bound. For `xⁿ ∈ T_ε^(n)(X)`,
`p(xⁿ) ≤ e^{-n(H(X) - δ(ε))}` with `δ(ε) = εH(X)`. -/
theorem iidPMF_le_of_mem_robustTypicalSet (hp : IsPMF p) (hx : x ∈ robustTypicalSet p n ε) :
    iidPMF p n x ≤ exp (-(n * (entropy p - ε * entropy p))) := by
  rw [iidPMF_eq_exp_sum_log hp.nonneg hx]
  have h := card_mul_le_sum_of_mem_robustTypicalSet hx (g := fun a => -log (p a))
    fun a => neg_nonneg.2 (log_nonpos (hp.nonneg a) (hp.le_one a))
  rw [expect_neg_log] at h
  exact exp_le_exp.2 (by linarith)

/-- Robustly typical sequences are weakly typical: `T_ε^(n)(X) ⊆ A_δ^(n)(X)` for `δ = εH(X)`
(Lecture 2, appendix on weak typicality). -/
theorem robustTypicalSet_subset_typicalSet (hp : IsPMF p) (n : ℕ) (ε : ℝ) :
    robustTypicalSet p n ε ⊆ typicalSet p n (ε * entropy p) := fun _ hx =>
  mem_typicalSet.2 ⟨le_iidPMF_of_mem_robustTypicalSet hp hx,
    iidPMF_le_of_mem_robustTypicalSet hp hx⟩

/-- **Property 2 (Lecture 2).** `|T_ε^(n)(X)| ≤ e^{n(H(X) + δ(ε))}`. -/
theorem card_robustTypicalSet_le (hp : IsPMF p) (n : ℕ) (ε : ℝ) :
    ((robustTypicalSet p n ε).card : ℝ) ≤ exp (n * (entropy p + ε * entropy p)) := by
  have h := (card_mul_le_prob fun x hx => le_iidPMF_of_mem_robustTypicalSet hp hx).trans
    (prob_le_one (iidPMF_isPMF hp n) (robustTypicalSet p n ε))
  rw [← le_div_iff₀ (exp_pos _), one_div, ← exp_neg, neg_neg] at h
  exact h

/-- A strongly typical set is contained in a robustly typical set. -/
lemma exists_strongTypicalSet_subset (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' > 0, ∀ n, strongTypicalSet p n ε' ⊆ robustTypicalSet p n ε := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hp
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < p a := by
    by_contra h
    push Not at h
    have := hp.sum_eq_one
    have : ∑ a, p a ≤ 0 := sum_nonpos fun a _ => h a
    linarith
  classical
  set S := univ.filter fun a => 0 < p a
  have hS : S.Nonempty := ⟨a₀, by simp [S, ha₀]⟩
  set m := S.inf' hS p
  have hm : 0 < m := (lt_inf'_iff hS).2 fun a ha => (mem_filter.1 ha).2
  have hle : ∀ a, 0 < p a → m ≤ p a := fun a ha => inf'_le _ (by simp [S, ha])
  refine ⟨ε * m * Fintype.card α, by positivity, fun n x hx => mem_robustTypicalSet.2 fun a => ?_⟩
  have h := mem_strongTypicalSet.1 hx a
  rcases (hp.nonneg a).lt_or_eq with ha | ha
  · have h1 := h.1 ha
    rw [mul_div_cancel_right₀ _ hα.ne'] at h1
    exact (h1.le.trans (mul_le_mul_of_nonneg_left (hle a ha) hε.le))
  · rw [← ha, typeOf, h.2 ha.symm]
    simp

/-- **Property 3 (Lecture 2).** If `X₁, X₂, …` are i.i.d. with law `p`, then
`P{Xⁿ ∈ T_ε^(n)(X)} → 1`, by the law of large numbers. -/
theorem tendsto_prob_robustTypicalSet (hp : IsPMF p) (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF p n) (robustTypicalSet p n ε)) atTop (𝓝 1) := by
  obtain ⟨ε', hε', hsub⟩ := exists_strongTypicalSet_subset hp hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_prob_strongTypicalSet hp hε')
    tendsto_const_nhds (fun n => prob_mono (iidPMF_nonneg hp.nonneg) (hsub n))
    fun n => prob_le_one (iidPMF_isPMF hp n) _

/-- **Property 4 (Lecture 2).** For `n` sufficiently large,
`|T_ε^(n)(X)| ≥ (1 - ε) e^{n(H(X) - δ(ε))}`. -/
theorem eventually_card_robustTypicalSet_ge (hp : IsPMF p) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 - ε) * exp (n * (entropy p - ε * entropy p)) ≤ (robustTypicalSet p n ε).card := by
  filter_upwards [(tendsto_order.1 (tendsto_prob_robustTypicalSet hp hε)).1 (1 - ε)
    (by linarith)] with n hn
  have h := prob_le_card_mul (μ := iidPMF p n) (S := robustTypicalSet p n ε)
    fun x hx => iidPMF_le_of_mem_robustTypicalSet hp hx
  have h' : 1 - ε ≤ (robustTypicalSet p n ε).card * exp (-(n * (entropy p - ε * entropy p))) :=
    hn.le.trans h
  rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)] at h'
  exact h'

/-! ### Functions of typical sequences -/

omit [Fintype β] in
/-- The type of `f(xⁿ)` is the law of `f` under the type of `xⁿ`. -/
lemma typeOf_comp (x : Fin n → α) (f : α → β) (b : β) :
    typeOf (f ∘ x) b = dist (typeOf x) f b := by
  classical
  have h : (symbolCount (f ∘ x) b : ℝ) =
      ∑ a, (symbolCount x a : ℝ) * if f a = b then 1 else 0 := by
    rw [symbolCount_eq_sum, ← sum_comp_eq_sum_symbolCount]
    exact sum_congr rfl fun i _ => by simp
  rw [typeOf, h, sum_div, dist]
  refine sum_congr rfl fun a _ => ?_
  split_ifs <;> simp [typeOf]

/-- **Typicality of functions (Lecture 2).** If `xⁿ` is typical for `p`, then `f(xⁿ)` is typical
for the law of `f(X)`. In particular a subtuple of a typical sequence of tuples is typical, and
the components of a jointly typical pair are typical. -/
theorem comp_mem_robustTypicalSet (hx : x ∈ robustTypicalSet p n ε) (f : α → β) :
    f ∘ x ∈ robustTypicalSet (dist p f) n ε := by
  classical
  refine mem_robustTypicalSet.2 fun b => ?_
  rw [typeOf_comp, dist, dist, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
  split_ifs
  · exact mem_robustTypicalSet.1 hx a
  · simp

end InfoTheory
