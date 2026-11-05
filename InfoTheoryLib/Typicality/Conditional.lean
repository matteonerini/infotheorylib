/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Code
public import InfoTheoryLib.ChannelCoding.JointTypicality
public import InfoTheoryLib.Typicality.Basic

/-!
# Jointly and conditionally typical sequences

Let `(X, Y) ∼ q(x, y)`. A pair of sequences `(xⁿ, yⁿ)` is jointly typical if the sequence of pairs
`((x₁, y₁), …, (xₙ, yₙ))` is typical for `q`, so jointly typical sequences are typical sequences
for the "large" random variable `(X, Y)`. For a fixed `xⁿ`, the conditionally typical set
`T_ε^(n)(Y|xⁿ)` is the set of `yⁿ` that are jointly typical with `xⁿ`. It has at most
`e^{n(H(Y|X) + δ(ε))}` elements, and, by the conditional typicality lemma, a sequence `Yⁿ` drawn
from `∏ᵢ p(yᵢ|xᵢ)` is jointly typical with a typical `xⁿ` with high probability.

We prove the conditional typicality lemma in a uniform and quantitative form: for
`xⁿ ∈ T_{ε'}^(n)(X)` with `ε' < ε`, `P{(xⁿ, Yⁿ) ∈ T_ε^(n)(X, Y)} ≥ 1 - K/n` for a constant `K`
that only depends on `q`, `ε'` and `ε`. The proof applies Chebyshev's inequality to the joint
counts `N(a, b|xⁿ, Yⁿ)`, which are sums of independent but not identically distributed random
variables.

## Main definitions

* `condRobustTypicalSet q ε xⁿ`: the conditionally typical set `T_ε^(n)(Y|xⁿ)`.
* `condTypicalityConst q ε' ε`: the constant `K` of the conditional typicality lemma.

## Main statements

* `fst_mem_robustTypicalSet`, `snd_mem_robustTypicalSet`: property 1(a) of jointly typical
  sequences, the components of a jointly typical pair are typical.
* `le_channelExt_condPMF_of_mem`, `channelExt_condPMF_le_of_mem`: property 1(c),
  `p(yⁿ|xⁿ) ≐ e^{-nH(Y|X)}`.
* `card_condRobustTypicalSet_le`: property 3, `|T_ε^(n)(Y|xⁿ)| ≤ e^{n(H(Y|X) + δ(ε))}`.
* `mem_condRobustTypicalSet_comp_iff`: property 4, for `Y = g(X)`.
* `one_sub_div_le_prob_condRobustTypicalSet`, `eventually_prob_condRobustTypicalSet_ge`,
  `tendsto_prob_condRobustTypicalSet`: the conditional typicality lemma.
* `eventually_card_condRobustTypicalSet_ge`: property 5,
  `|T_ε^(n)(Y|xⁿ)| ≥ (1 - ε) e^{n(H(Y|X) - δ(ε))}` for `xⁿ ∈ T_{ε'}^(n)(X)`.

## Implementation notes

The joint pmf is `q : α × β → ℝ` and the conditional pmf `p(y|x)` is `condPMF q x y`, so that
`p(yⁿ|xⁿ) = ∏ᵢ p(yᵢ|xᵢ)` is `channelExt (condPMF q) n xⁿ yⁿ`. The conditional entropy `H(Y|X)` is
`H[Prod.snd | Prod.fst ; q]`. Results for `p(xⁿ|yⁿ)` follow by applying those for `p(yⁿ|xⁿ)` to the
pmf of `(Y, X)`, see `zipSeq_swap_mem_robustTypicalSet`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Sums of independent random variables -/

section Independent

variable {n : ℕ}

/-- `∑_{yⁿ} ∏ᵢ Pᵢ(yᵢ) ∏ᵢ φᵢ(yᵢ) = ∏ᵢ ∑_b Pᵢ(b) φᵢ(b)`: expectations of products of functions of
independent random variables factor. -/
lemma sum_prod_mul_prod (P φ : Fin n → β → ℝ) :
    ∑ y : Fin n → β, (∏ i, P i (y i)) * ∏ i, φ i (y i) = ∏ i, ∑ b, P i b * φ i b := by
  rw [Fintype.prod_sum]
  simp only [prod_mul_distrib]

/-- `E[g(Yᵢ) h(Yⱼ)]` for independent `Y₁, …, Yₙ`. -/
lemma sum_prod_mul_apply_mul_apply {P : Fin n → β → ℝ} (hP : ∀ i, IsPMF (P i)) (i j : Fin n)
    (g h : β → ℝ) :
    ∑ y : Fin n → β, (∏ k, P k (y k)) * (g (y i) * h (y j)) =
      if i = j then ∑ b, P i b * (g b * h b)
      else (∑ b, P i b * g b) * ∑ b, P j b * h b := by
  classical
  set φ : Fin n → β → ℝ := fun k b => (if k = i then g b else 1) * (if k = j then h b else 1)
  have hφ : ∀ y : Fin n → β, ∏ k, φ k (y k) = g (y i) * h (y j) := fun y => by
    simp only [φ, prod_mul_distrib, prod_ite_eq', mem_univ, ite_true]
  simp_rw [← hφ]
  rw [sum_prod_mul_prod]
  split_ifs with hij
  · subst hij
    rw [prod_eq_single i (fun k _ hk => by simp [φ, hk, (hP k).sum_eq_one]) (by simp)]
    simp [φ]
  · rw [Fintype.prod_eq_mul_prod_compl i, prod_eq_single j
      (fun k hk hkj => by
        have hki : k ≠ i := by simpa using hk
        simp [φ, hki, hkj, (hP k).sum_eq_one])
      (by simp [Ne.symm hij])]
    simp [φ, hij, Ne.symm hij]

/-- The second moment of a sum of independent, centered random variables bounded by `1` is at
most `n`: `E (∑ᵢ fᵢ(Yᵢ))² ≤ n` if `E fᵢ(Yᵢ) = 0` and `fᵢ² ≤ 1`. -/
theorem sum_prod_mul_sq_sum_le {P : Fin n → β → ℝ} (hP : ∀ i, IsPMF (P i))
    {f : Fin n → β → ℝ} (hf0 : ∀ i, ∑ b, P i b * f i b = 0) (hf1 : ∀ i b, f i b ^ 2 ≤ 1) :
    ∑ y : Fin n → β, (∏ i, P i (y i)) * (∑ i, f i (y i)) ^ 2 ≤ n := by
  have h : ∀ y : Fin n → β, (∏ i, P i (y i)) * (∑ i, f i (y i)) ^ 2 =
      ∑ i, ∑ j, (∏ k, P k (y k)) * (f i (y i) * f j (y j)) := fun y => by
    rw [sq, sum_mul_sum, mul_sum]
    simp_rw [mul_sum]
  have h2 : ∑ y : Fin n → β, (∏ i, P i (y i)) * (∑ i, f i (y i)) ^ 2 =
      ∑ i, ∑ j, (if i = j then ∑ b, P i b * (f i b * f j b)
        else (∑ b, P i b * f i b) * ∑ b, P j b * f j b) := by
    simp_rw [h]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_prod_mul_apply_mul_apply hP i j _ _
  rw [h2]
  calc ∑ i, ∑ j, (if i = j then ∑ b, P i b * (f i b * f j b)
          else (∑ b, P i b * f i b) * ∑ b, P j b * f j b)
      = ∑ i, ∑ b, P i b * (f i b * f i b) := by
        refine sum_congr rfl fun i _ => ?_
        rw [sum_eq_single i (fun j _ hj => by simp [Ne.symm hj, hf0]) (by simp), ite_eq_left rfl]
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := sum_le_sum fun i _ => by
        calc ∑ b, P i b * (f i b * f i b) ≤ ∑ b, P i b * 1 :=
              sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (by nlinarith [hf1 i b])
                ((hP i).nonneg b)
          _ = 1 := by simp [(hP i).sum_eq_one]
    _ = n := by simp

end Independent

/-! ### Conditional pmfs -/

omit [Fintype α] in
lemma condPMF_nonneg {q : α × β → ℝ} (hq : ∀ z, 0 ≤ q z) (a : α) (b : β) :
    0 ≤ condPMF q a b :=
  div_nonneg (hq _) (sum_nonneg fun _ _ => hq _)

omit [Fintype α] in
lemma condPMF_le_one {q : α × β → ℝ} (hq : ∀ z, 0 ≤ q z) (a : α) (b : β) : condPMF q a b ≤ 1 :=
  div_le_one_of_le₀ (le_marg hq a b) (sum_nonneg fun _ _ => hq _)

omit [Fintype α] in
lemma sum_condPMF_le_one {q : α × β → ℝ} (hq : ∀ z, 0 ≤ q z) (a : α) :
    ∑ b, condPMF q a b ≤ 1 := by
  rcases (sum_nonneg fun b _ => hq (a, b) : 0 ≤ marg q a).lt_or_eq with h | h
  · rw [(condPMF_isPMF hq h.ne').sum_eq_one]
  · have h0 : marg q a = 0 := h.symm
    simp [condPMF, h0]

/-- The conditional pmf of `Y = Prod.snd` given `X = Prod.fst` is `condPMF q`. -/
lemma condDist_snd_fst (q : α × β → ℝ) : condDist q Prod.snd Prod.fst = condPMF q := by
  funext a b
  rw [condDist, pair_fst_snd, dist_id, condPMF, marg_eq_dist]

/-- `H(Y|X) = E[-log p(Y|X)]`. -/
lemma expect_neg_log_condPMF {q : α × β → ℝ} (hq : IsPMF q) :
    expect q (fun z => -log (condPMF q z.1 z.2)) = H[Prod.snd | Prod.fst ; q] := by
  rw [condEntropy_eq_expect hq, condDist_snd_fst, expect]
  simp only [neg_mul, sum_neg_distrib]
  congr 1
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-! ### Jointly typical sequences -/

variable {q : α × β → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α} {y : Fin n → β}

/-- **Property 1(a) of jointly typical sequences (Lecture 2).** If `(xⁿ, yⁿ)` is jointly typical,
then `xⁿ` is typical. -/
lemma fst_mem_robustTypicalSet (h : zipSeq x y ∈ robustTypicalSet q n ε) :
    x ∈ robustTypicalSet (margFst q) n ε :=
  comp_mem_robustTypicalSet h Prod.fst

/-- **Property 1(a) of jointly typical sequences (Lecture 2).** If `(xⁿ, yⁿ)` is jointly typical,
then `yⁿ` is typical. -/
lemma snd_mem_robustTypicalSet (h : zipSeq x y ∈ robustTypicalSet q n ε) :
    y ∈ robustTypicalSet (margSnd q) n ε :=
  comp_mem_robustTypicalSet h Prod.snd

/-- Joint typicality is symmetric: `(yⁿ, xⁿ)` is jointly typical for the pmf of `(Y, X)`. -/
lemma zipSeq_swap_mem_robustTypicalSet (h : zipSeq x y ∈ robustTypicalSet q n ε) :
    zipSeq y x ∈ robustTypicalSet (dist q Prod.swap) n ε :=
  comp_mem_robustTypicalSet h Prod.swap

/-- `p(yⁿ|xⁿ)` for a jointly typical pair, as an exponential. -/
lemma channelExt_condPMF_eq_exp (hq : IsPMF q) (h : zipSeq x y ∈ robustTypicalSet q n ε) :
    channelExt (condPMF q) n x y = exp (-∑ i, -log (condPMF q (x i) (y i))) := by
  rw [channelExt, show -∑ i, -log (condPMF q (x i) (y i)) = ∑ i, log (condPMF q (x i) (y i)) by
    simp, exp_sum]
  refine prod_congr rfl fun i _ => (exp_log ?_).symm
  have hpos : 0 < q (x i, y i) := pos_of_mem_robustTypicalSet hq.nonneg h i
  exact div_pos hpos (hpos.trans_le (le_marg hq.nonneg _ _))

/-- **Property 1(c) of jointly typical sequences (Lecture 2)**, lower bound. For a jointly
typical pair, `p(yⁿ|xⁿ) ≥ e^{-n(H(Y|X) + δ(ε))}` with `δ(ε) = εH(Y|X)`. -/
theorem le_channelExt_condPMF_of_mem (hq : IsPMF q) (h : zipSeq x y ∈ robustTypicalSet q n ε) :
    exp (-(n * (H[Prod.snd | Prod.fst ; q] + ε * H[Prod.snd | Prod.fst ; q]))) ≤
      channelExt (condPMF q) n x y := by
  rw [channelExt_condPMF_eq_exp hq h]
  have hb := sum_le_card_mul_of_mem_robustTypicalSet h
    (g := fun z => -log (condPMF q z.1 z.2))
    fun z => neg_nonneg.2 (log_nonpos (condPMF_nonneg hq.nonneg _ _) (condPMF_le_one hq.nonneg _ _))
  rw [expect_neg_log_condPMF hq] at hb
  exact exp_le_exp.2 (by simp only [zipSeq] at hb; linarith)

/-- **Property 1(c) of jointly typical sequences (Lecture 2)**, upper bound. For a jointly
typical pair, `p(yⁿ|xⁿ) ≤ e^{-n(H(Y|X) - δ(ε))}` with `δ(ε) = εH(Y|X)`. -/
theorem channelExt_condPMF_le_of_mem (hq : IsPMF q) (h : zipSeq x y ∈ robustTypicalSet q n ε) :
    channelExt (condPMF q) n x y ≤
      exp (-(n * (H[Prod.snd | Prod.fst ; q] - ε * H[Prod.snd | Prod.fst ; q]))) := by
  rw [channelExt_condPMF_eq_exp hq h]
  have hb := card_mul_le_sum_of_mem_robustTypicalSet h
    (g := fun z => -log (condPMF q z.1 z.2))
    fun z => neg_nonneg.2 (log_nonpos (condPMF_nonneg hq.nonneg _ _) (condPMF_le_one hq.nonneg _ _))
  rw [expect_neg_log_condPMF hq] at hb
  exact exp_le_exp.2 (by simp only [zipSeq] at hb; linarith)

/-! ### Conditionally typical sequences -/

open Classical in
/-- **Definition (Lecture 2).** The conditionally typical set
`T_ε^(n)(Y|xⁿ) = {yⁿ : (xⁿ, yⁿ) ∈ T_ε^(n)(X, Y)}`. -/
def condRobustTypicalSet (q : α × β → ℝ) (ε : ℝ) {n : ℕ} (x : Fin n → α) :
    Finset (Fin n → β) :=
  univ.filter fun y => zipSeq x y ∈ robustTypicalSet q n ε

lemma mem_condRobustTypicalSet :
    y ∈ condRobustTypicalSet q ε x ↔ zipSeq x y ∈ robustTypicalSet q n ε := by
  classical
  simp [condRobustTypicalSet]

omit [Fintype α] in
/-- The total mass `∑_{yⁿ} p(yⁿ|xⁿ)` is at most `1`, with equality unless some `xᵢ` has
probability zero. -/
lemma sum_channelExt_condPMF_le_one (hq : ∀ z, 0 ≤ q z) (x : Fin n → α) :
    ∑ y, channelExt (condPMF q) n x y ≤ 1 := by
  rw [show ∑ y, channelExt (condPMF q) n x y = ∏ i, ∑ b, condPMF q (x i) b from
    (Fintype.prod_sum _).symm]
  exact prod_le_one₀ (fun i _ => sum_nonneg fun b _ => condPMF_nonneg hq _ _)
    fun i _ => sum_condPMF_le_one hq _

/-- **Property 3 of jointly typical sequences (Lecture 2).** For every `xⁿ`,
`|T_ε^(n)(Y|xⁿ)| ≤ e^{n(H(Y|X) + δ(ε))}` with `δ(ε) = εH(Y|X)`. -/
theorem card_condRobustTypicalSet_le (hq : IsPMF q) (ε : ℝ) (x : Fin n → α) :
    ((condRobustTypicalSet q ε x).card : ℝ) ≤
      exp (n * (H[Prod.snd | Prod.fst ; q] + ε * H[Prod.snd | Prod.fst ; q])) := by
  have h1 := card_mul_le_prob (μ := channelExt (condPMF q) n x)
    (S := condRobustTypicalSet q ε x) fun y hy =>
      le_channelExt_condPMF_of_mem hq (mem_condRobustTypicalSet.1 hy)
  have h2 : prob (channelExt (condPMF q) n x) (condRobustTypicalSet q ε x) ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ =>
      prod_nonneg fun i _ => condPMF_nonneg hq.nonneg _ _).trans
      (sum_channelExt_condPMF_le_one hq.nonneg x)
  have h := h1.trans h2
  rw [← le_div_iff₀ (exp_pos _), one_div, ← exp_neg, neg_neg] at h
  exact h

/-- **Property 4 of jointly typical sequences (Lecture 2).** If `Y = g(X)` and `xⁿ` is typical,
then `yⁿ ∈ T_ε^(n)(Y|xⁿ)` iff `yᵢ = g(xᵢ)` for every `i`. -/
theorem mem_condRobustTypicalSet_comp_iff {p : α → ℝ} (hp : IsPMF p) (g : α → β)
    (hx : x ∈ robustTypicalSet p n ε) :
    y ∈ condRobustTypicalSet (dist p fun a => (a, g a)) ε x ↔ ∀ i, y i = g (x i) := by
  classical
  rw [mem_condRobustTypicalSet]
  constructor
  · intro h i
    have hpos := pos_of_mem_robustTypicalSet (hp.dist _).nonneg h i
    by_contra hne
    refine hpos.ne' (sum_eq_zero fun a _ => ?_)
    split_ifs with ha
    · simp only [zipSeq, Prod.mk.injEq] at ha
      exact absurd (ha.2 ▸ ha.1 ▸ rfl) hne
    · rfl
  · intro h
    have : zipSeq x y = (fun a => (a, g a)) ∘ x := funext fun i => by simp [zipSeq, h i]
    rw [this]
    exact comp_mem_robustTypicalSet hx _

/-! ### The conditional typicality lemma -/

open Classical in
omit [Fintype α] [Fintype β] in
/-- `∑ᵢ 1{xᵢ = a} (1{yᵢ = b} - w) = N(a, b|xⁿ, yⁿ) - N(a|xⁿ) w`. -/
lemma sum_count_deviation (x : Fin n → α) (y : Fin n → β) (a : α) (b : β) (w : ℝ) :
    ∑ i, (if x i = a then (if y i = b then 1 else 0) - w else 0) =
      (symbolCount (zipSeq x y) (a, b) : ℝ) - symbolCount x a * w := by
  classical
  rw [symbolCount_eq_sum, symbolCount_eq_sum, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  by_cases h1 : x i = a <;> by_cases h2 : y i = b <;> simp [zipSeq, h1, h2]

omit [Fintype α] in
lemma exists_eq_of_symbolCount_ne_zero {x : Fin n → α} {a : α} (h : symbolCount x a ≠ 0) :
    ∃ i, x i = a := by
  classical
  by_contra hne
  push Not at hne
  exact h (card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ => hne i))

open Classical in
/-- The constant `K = ∑_{q(a, b) > 0} ((ε - ε') q(a, b))⁻²` of the conditional typicality lemma. -/
def condTypicalityConst (q : α × β → ℝ) (ε' ε : ℝ) : ℝ :=
  ∑ z ∈ univ.filter (fun z => 0 < q z), 1 / ((ε - ε') * q z) ^ 2

/-- **Conditional typicality lemma (Lecture 2)**, quantitative form. Let `ε' < ε` and
`xⁿ ∈ T_{ε'}^(n)(X)`. If `Yⁿ ∼ ∏ᵢ p(yᵢ|xᵢ)`, then `P{(xⁿ, Yⁿ) ∈ T_ε^(n)(X, Y)} ≥ 1 - K/n` with
`K = condTypicalityConst q ε' ε`. -/
theorem one_sub_div_le_prob_condRobustTypicalSet (hq : IsPMF q) {ε' : ℝ} (hεε : ε' < ε)
    (hn : 0 < n) (hx : x ∈ robustTypicalSet (margFst q) n ε') :
    1 - condTypicalityConst q ε' ε / n ≤
      prob (channelExt (condPMF q) n x) (condRobustTypicalSet q ε x) := by
  classical
  set W := condPMF q
  set μ := channelExt W n x
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmarg : ∀ i, 0 < marg q (x i) := fun i => by
    have := pos_of_mem_robustTypicalSet (hq.dist Prod.fst).nonneg hx i
    rw [marg_eq_dist]
    exact this
  have hrow : ∀ i, IsPMF (W (x i)) := fun i => condPMF_isPMF hq.nonneg (hmarg i).ne'
  have hμ : IsPMF μ := ⟨fun y => prod_nonneg fun i _ => (hrow i).nonneg _, by
    rw [show ∑ y, μ y = ∏ i, ∑ b, W (x i) b from (Fintype.prod_sum _).symm]
    simp [(hrow _).sum_eq_one]⟩
  -- The centered count `Sₐ_b(yⁿ) = N(a, b|xⁿ, yⁿ) - N(a|xⁿ) p(b|a)`.
  set f : α × β → Fin n → β → ℝ := fun z i c =>
    if x i = z.1 then (if c = z.2 then 1 else 0) - W z.1 z.2 else 0
  set S : α × β → (Fin n → β) → ℝ := fun z y => ∑ i, f z i (y i)
  have hf0 : ∀ z i, ∑ c, W (x i) c * f z i c = 0 := fun z i => by
    simp only [f]
    split_ifs with hi
    · rw [← hi]
      simp [mul_sub, sum_sub_distrib, ← sum_mul, (hrow i).sum_eq_one]
    · simp
  have hf1 : ∀ z i c, f z i c ^ 2 ≤ 1 := fun z i c => by
    have h0 := condPMF_nonneg hq.nonneg z.1 z.2
    have h1 := condPMF_le_one hq.nonneg z.1 z.2
    simp only [f]
    split_ifs <;> nlinarith
  -- Chebyshev's inequality for each `Sₐ_b`.
  set c : α × β → ℝ := fun z => (ε - ε') * q z
  set B : α × β → Finset (Fin n → β) := fun z => univ.filter fun y => c z * n ≤ |S z y|
  have hB : ∀ z, 0 < q z → prob μ (B z) ≤ 1 / (c z) ^ 2 / n := fun z hz => by
    have hc : 0 < c z := mul_pos (by linarith) hz
    have hm := markov_ineq hμ.nonneg (f := fun y => S z y ^ 2) (fun y => sq_nonneg _)
      (pow_pos (mul_pos hc hn') 2)
    have hE : expect μ (fun y => S z y ^ 2) ≤ n := by
      rw [expect]
      simp_rw [mul_comm _ (μ _)]
      exact sum_prod_mul_sq_sum_le hrow (hf0 z) (hf1 z)
    refine (prob_mono hμ.nonneg ?_).trans (hm.trans ?_)
    · intro y hy
      simp only [B, mem_filter, mem_univ, true_and] at hy ⊢
      calc (c z * n) ^ 2 ≤ |S z y| ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
        _ = S z y ^ 2 := sq_abs _
    · rw [div_le_div_iff₀ (by positivity) hn']
      calc expect μ (fun y => S z y ^ 2) * n ≤ n * n := mul_le_mul_of_nonneg_right hE hn'.le
        _ = 1 / c z ^ 2 / n * ((c z * n) ^ 2) * n := by field_simp
        _ = 1 / c z ^ 2 * ((c z * n) ^ 2) := by field_simp
  -- An atypical `yⁿ` of positive probability is in some `Bₐ_b`.
  set P := univ.filter fun z : α × β => 0 < q z
  have hcover : prob μ (condRobustTypicalSet q ε x)ᶜ ≤ prob μ (P.biUnion B) := by
    refine prob_le_prob_of_ae hμ.nonneg fun y hy hy0 => ?_
    rw [mem_compl, mem_condRobustTypicalSet, mem_robustTypicalSet, not_forall] at hy
    obtain ⟨⟨a, b⟩, hab⟩ := hy
    rw [not_le] at hab
    rcases (hq.nonneg (a, b)).lt_or_eq with hpos | hzero
    · refine mem_biUnion.2 ⟨(a, b), by simp [P, hpos], ?_⟩
      simp only [B, mem_filter, mem_univ, true_and, S, f, c]
      rw [sum_count_deviation, ← mul_typeOf hn, ← mul_typeOf hn, mul_assoc (n : ℝ) (typeOf x a),
        ← mul_sub, abs_mul,
        abs_of_pos hn', mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ hn'.le
      have hqW : q (a, b) = marg q a * W a b := (marg_mul_condPMF hq.nonneg a b).symm
      have hxa : |typeOf x a - marg q a| ≤ ε' * marg q a := by
        rw [marg_eq_dist]
        exact mem_robustTypicalSet.1 hx a
      have hW := condPMF_nonneg hq.nonneg a b
      have h2 : |typeOf x a * W a b - q (a, b)| ≤ ε' * q (a, b) := by
        rw [hqW, ← sub_mul, abs_mul, abs_of_nonneg hW, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hxa hW
      have h3 := abs_sub_le (typeOf (zipSeq x y) (a, b)) (typeOf x a * W a b) (q (a, b))
      linarith
    · exfalso
      rw [← hzero, sub_zero, mul_zero, abs_pos] at hab
      have hcount : symbolCount (zipSeq x y) (a, b) ≠ 0 := fun h0 => hab (by simp [typeOf, h0])
      obtain ⟨i, hi⟩ := exists_eq_of_symbolCount_ne_zero hcount
      simp only [zipSeq, Prod.mk.injEq] at hi
      refine hy0 (prod_eq_zero (mem_univ i) ?_)
      rw [hi.1, hi.2]
      simp [W, condPMF, ← hzero]
  have hunion : prob μ (P.biUnion B) ≤ condTypicalityConst q ε' ε / n := by
    refine (prob_biUnion_le hμ.nonneg _ _).trans ?_
    rw [condTypicalityConst, sum_div]
    exact sum_le_sum fun z hz => hB z (mem_filter.1 hz).2
  have hc := prob_compl hμ (condRobustTypicalSet q ε x)
  linarith

/-- **Conditional typicality lemma (Lecture 2)**, uniform form. Let `ε' < ε`. For every `η > 0`,
for `n` sufficiently large and every `xⁿ ∈ T_{ε'}^(n)(X)`,
`P{(xⁿ, Yⁿ) ∈ T_ε^(n)(X, Y)} ≥ 1 - η` when `Yⁿ ∼ ∏ᵢ p(yᵢ|xᵢ)`. -/
theorem eventually_prob_condRobustTypicalSet_ge (hq : IsPMF q) {ε' : ℝ} (hεε : ε' < ε) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ robustTypicalSet (margFst q) n ε',
      1 - η ≤ prob (channelExt (condPMF q) n x) (condRobustTypicalSet q ε x) := by
  have hlim : Tendsto (fun n : ℕ => condTypicalityConst q ε' ε / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [(tendsto_order.1 hlim).2 η hη, eventually_gt_atTop 0] with n hK hn x hx
  linarith [one_sub_div_le_prob_condRobustTypicalSet hq hεε hn hx]

/-- **Conditional typicality lemma (Lecture 2).** Let `ε' < ε`, let `xⁿ ∈ T_{ε'}^(n)(X)` for
every `n`, and `Yⁿ ∼ ∏ᵢ p(yᵢ|xᵢ)`. Then `P{(xⁿ, Yⁿ) ∈ T_ε^(n)(X, Y)} → 1`. -/
theorem tendsto_prob_condRobustTypicalSet (hq : IsPMF q) {ε' : ℝ} (hεε : ε' < ε)
    {xs : ∀ n, Fin n → α} (hxs : ∀ n, xs n ∈ robustTypicalSet (margFst q) n ε') :
    Tendsto (fun n => prob (channelExt (condPMF q) n (xs n)) (condRobustTypicalSet q ε (xs n)))
      atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ => 1 - condTypicalityConst q ε' ε / n) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (condTypicalityConst q ε' ε)).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_
    (Eventually.of_forall fun n => ?_)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact one_sub_div_le_prob_condRobustTypicalSet hq hεε hn (hxs n)
  · exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ =>
      prod_nonneg fun i _ => condPMF_nonneg hq.nonneg _ _).trans
      (sum_channelExt_condPMF_le_one hq.nonneg _)

/-- **Property 5 of jointly typical sequences (Lecture 2).** Let `ε' < ε`. For `n` sufficiently
large and every `xⁿ ∈ T_{ε'}^(n)(X)`, `|T_ε^(n)(Y|xⁿ)| ≥ (1 - ε) e^{n(H(Y|X) - δ(ε))}` with
`δ(ε) = εH(Y|X)`. -/
theorem eventually_card_condRobustTypicalSet_ge (hq : IsPMF q) {ε' : ℝ} (hεε : ε' < ε)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ robustTypicalSet (margFst q) n ε',
      (1 - ε) * exp (n * (H[Prod.snd | Prod.fst ; q] - ε * H[Prod.snd | Prod.fst ; q])) ≤
        (condRobustTypicalSet q ε x).card := by
  filter_upwards [eventually_prob_condRobustTypicalSet_ge hq hεε hε] with n hn x hx
  have h := prob_le_card_mul (μ := channelExt (condPMF q) n x) (S := condRobustTypicalSet q ε x)
    fun y hy => channelExt_condPMF_le_of_mem hq (mem_condRobustTypicalSet.1 hy)
  have h' := (hn x hx).trans h
  rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)] at h'
  exact h'

end InfoTheory
