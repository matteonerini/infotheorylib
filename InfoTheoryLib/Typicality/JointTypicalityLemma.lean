/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MarkovChain.Basic
public import InfoTheoryLib.MutualInformation.Conditional
public import InfoTheoryLib.Typicality.Conditional

/-!
# The joint typicality lemma

Let `(X, Y, Z) ∼ p(x, y, z)`. If `Z̃ⁿ` is drawn from `∏ᵢ p(zᵢ|xᵢ)`, so that it depends on `xⁿ` but
not on `yⁿ`, then `(xⁿ, yⁿ, Z̃ⁿ)` is jointly typical with probability `≐ e^{-nI(Y;Z|X)}`: at most
`e^{-n(I(Y;Z|X) - δ(ε))}` for arbitrary `(xⁿ, yⁿ)`, and at least `e^{-n(I(Y;Z|X) + δ(ε))}` for
typical `(xⁿ, yⁿ)` and `n` large. This lemma is used in most achievability proofs of the lecture
notes: for `X = ∅` it bounds the probability that an independently generated codeword is
jointly typical with the received sequence (packing), or with the source sequence (covering).

We first bound the conditional probability `p(zⁿ|xⁿ) = ∏ᵢ p(zᵢ|xᵢ)` along a typical sequence,
for arbitrary random variables `X` and `Z` that are functions of the typical "large" random
variable.

## Main statements

* `le_prod_condDist_of_mem`, `prod_condDist_le_of_mem`: for a typical sequence `ωⁿ` and functions
  `X`, `Z` of `ω`, `p(zⁿ|xⁿ) ≐ e^{-nH(Z|X)}`.
* `prob_condRobustTypicalSet_condDist_le`: **joint typicality lemma**, part 1(a).
* `eventually_prob_condRobustTypicalSet_condDist_ge`,
  `eventually_exp_le_prob_condRobustTypicalSet_condDist`: **joint typicality lemma**, part 1(b).
* `sum_mul_prob_condRobustTypicalSet_condDist_le`: **joint typicality lemma**, part 2, for
  random `(X̃ⁿ, Ỹⁿ)` with an arbitrary pmf.
* `eventually_prob_condRobustTypicalSet_of_markovChain`: if `X → Y → Z` and `Zⁿ ∼ ∏ᵢ p(zᵢ|yᵢ)`,
  then `(xⁿ, yⁿ, Zⁿ)` is jointly typical with high probability.

## Implementation notes

The triple `(X, Y, Z)` takes values in `(α × β) × γ`, with pmf `q`. Thus `X = Prod.fst ∘ Prod.fst`,
`Y = Prod.snd ∘ Prod.fst`, `Z = Prod.snd`, the pair `(X, Y)` is `Prod.fst`, and
`T_ε^(n)(X, Y, Z)` is `robustTypicalSet q n ε`. The set of `zⁿ` with `(xⁿ, yⁿ, zⁿ)` jointly typical
is the conditionally typical set `condRobustTypicalSet q ε (zipSeq xⁿ yⁿ)`. The conditional pmf
`p(z|x)` is `condDist q Prod.snd (Prod.fst ∘ Prod.fst)`.

The `δ(ε)` of the lecture notes are explicit: `δ(ε) = ε (H(Z|X, Y) + H(Z|X))` in part 1(a). In
part 1(b) the factor `1 - ε` of the cardinality bound is kept, and it is absorbed into
`δ(ε) = ε (H(Z|X, Y) + H(Z|X) + 1)` in `eventually_exp_le_prob_condRobustTypicalSet_condDist`.
Part 1(b) assumes `(xⁿ, yⁿ) ∈ T_{ε'}^(n)` with `ε' < ε`: for `(xⁿ, yⁿ)` on the boundary of
`T_ε^(n)`, the set `T_ε^(n)(Z|xⁿ, yⁿ)` can be empty.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

/-! ### Conditional probabilities along typical sequences -/

section CondDist

variable {μ : Ω → ℝ} {n : ℕ} {ε : ℝ} {w : Fin n → Ω}

omit [Fintype α] [Fintype γ] in
lemma condDist_le_one (hμ : IsPMF μ) (Z : Ω → γ) (X : Ω → α) (a : α) (c : γ) :
    condDist μ Z X a c ≤ 1 :=
  div_le_one_of_le₀ (dist_pair_le_left hμ X Z a c) (dist_nonneg hμ X a)

omit [Fintype α] [Fintype γ] in
/-- `p(zⁿ|xⁿ)` along a typical sequence, as an exponential. -/
lemma prod_condDist_eq_exp (hμ : IsPMF μ) (X : Ω → α) (Z : Ω → γ)
    (hw : w ∈ robustTypicalSet μ n ε) :
    ∏ i, condDist μ Z X (X (w i)) (Z (w i)) =
      exp (-∑ i, -log (condDist μ Z X (X (w i)) (Z (w i)))) := by
  rw [show -∑ i, -log (condDist μ Z X (X (w i)) (Z (w i))) =
    ∑ i, log (condDist μ Z X (X (w i)) (Z (w i))) by simp, exp_sum]
  exact prod_congr rfl fun i _ =>
    (exp_log (condDist_pos hμ Z X (pos_of_mem_robustTypicalSet hμ.nonneg hw i))).symm

/-- `H(Z|X) = E[-log p(Z|X)]`. -/
lemma expect_neg_log_condDist (hμ : IsPMF μ) (X : Ω → α) (Z : Ω → γ) :
    expect μ (fun ω => -log (condDist μ Z X (X ω) (Z ω))) = H[Z | X ; μ] := by
  rw [condEntropy_eq_expect hμ, expect]
  simp only [neg_mul, sum_neg_distrib]
  congr 1
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- For a typical sequence `ωⁿ` and functions `X`, `Z` of `ω`,
`p(zⁿ|xⁿ) ≥ e^{-n(H(Z|X) + εH(Z|X))}`. -/
theorem le_prod_condDist_of_mem (hμ : IsPMF μ) (X : Ω → α) (Z : Ω → γ)
    (hw : w ∈ robustTypicalSet μ n ε) :
    exp (-(n * (H[Z | X ; μ] + ε * H[Z | X ; μ]))) ≤ ∏ i, condDist μ Z X (X (w i)) (Z (w i)) := by
  rw [prod_condDist_eq_exp hμ X Z hw]
  have hb := sum_le_card_mul_of_mem_robustTypicalSet hw
    (g := fun ω => -log (condDist μ Z X (X ω) (Z ω)))
    fun ω => neg_nonneg.2 (log_nonpos (condDist_nonneg hμ _ _ _ _) (condDist_le_one hμ _ _ _ _))
  rw [expect_neg_log_condDist hμ] at hb
  exact exp_le_exp.2 (by linarith)

/-- For a typical sequence `ωⁿ` and functions `X`, `Z` of `ω`,
`p(zⁿ|xⁿ) ≤ e^{-n(H(Z|X) - εH(Z|X))}`. -/
theorem prod_condDist_le_of_mem (hμ : IsPMF μ) (X : Ω → α) (Z : Ω → γ)
    (hw : w ∈ robustTypicalSet μ n ε) :
    ∏ i, condDist μ Z X (X (w i)) (Z (w i)) ≤ exp (-(n * (H[Z | X ; μ] - ε * H[Z | X ; μ]))) := by
  rw [prod_condDist_eq_exp hμ X Z hw]
  have hb := card_mul_le_sum_of_mem_robustTypicalSet hw
    (g := fun ω => -log (condDist μ Z X (X ω) (Z ω)))
    fun ω => neg_nonneg.2 (log_nonpos (condDist_nonneg hμ _ _ _ _) (condDist_le_one hμ _ _ _ _))
  rw [expect_neg_log_condDist hμ] at hb
  exact exp_le_exp.2 (by linarith)

end CondDist

/-! ### The joint typicality lemma -/

variable {q : (α × β) × γ → ℝ} {n : ℕ} {ε : ℝ}

/-- `I(Y;Z|X) = H(Z|X) - H(Z|X, Y)`. -/
lemma condMutualInfo_triple_eq (hq : IsPMF q) :
    I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] =
      H[Prod.snd | Prod.fst ∘ Prod.fst ; q] - H[Prod.snd | Prod.fst ; q] := by
  rw [condMutualInfo_comm hq, condMutualInfo]
  congr 1
  exact condEntropy_congr_right hq _ Prod.swap Prod.swap_injective fun _ => rfl

/-- **Joint typicality lemma (Lecture 2)**, part 1(a). For arbitrary sequences `(xⁿ, yⁿ)` and
`Z̃ⁿ ∼ ∏ᵢ p(zᵢ|xᵢ)`, `P{(xⁿ, yⁿ, Z̃ⁿ) ∈ T_ε^(n)(X, Y, Z)} ≤ e^{-n(I(Y;Z|X) - δ(ε))}` with
`δ(ε) = ε (H(Z|X, Y) + H(Z|X))`. -/
theorem prob_condRobustTypicalSet_condDist_le (hq : IsPMF q) (n : ℕ) (ε : ℝ) (x : Fin n → α)
    (y : Fin n → β) :
    prob (channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n x)
        (condRobustTypicalSet q ε (zipSeq x y)) ≤
      exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] -
        ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q])))) := by
  have h1 := prob_le_card_mul
    (μ := channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n x)
    (S := condRobustTypicalSet q ε (zipSeq x y)) fun z hz =>
      prod_condDist_le_of_mem hq (Prod.fst ∘ Prod.fst) Prod.snd (mem_condRobustTypicalSet.1 hz)
  have h2 := card_condRobustTypicalSet_le hq ε (zipSeq x y)
  refine h1.trans ((mul_le_mul_of_nonneg_right h2 (exp_pos _).le).trans_eq ?_)
  rw [← exp_add, condMutualInfo_triple_eq hq]
  ring_nf

/-- **Joint typicality lemma (Lecture 2)**, part 1(b). Let `ε' < ε`. For `n` sufficiently large,
every `(xⁿ, yⁿ) ∈ T_{ε'}^(n)(X, Y)`, and `Z̃ⁿ ∼ ∏ᵢ p(zᵢ|xᵢ)`,
`P{(xⁿ, yⁿ, Z̃ⁿ) ∈ T_ε^(n)(X, Y, Z)} ≥ (1 - ε) e^{-n(I(Y;Z|X) + ε (H(Z|X, Y) + H(Z|X)))}`. -/
theorem eventually_prob_condRobustTypicalSet_condDist_ge (hq : IsPMF q) {ε' : ℝ}
    (hεε : ε' < ε) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (x : Fin n → α) (y : Fin n → β),
      zipSeq x y ∈ robustTypicalSet (margFst q) n ε' →
        (1 - ε) * exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] +
          ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q])))) ≤
        prob (channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n x)
          (condRobustTypicalSet q ε (zipSeq x y)) := by
  filter_upwards [eventually_card_condRobustTypicalSet_ge hq hεε hε] with n hn x y hxy
  have h1 := card_mul_le_prob
    (μ := channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n x)
    (S := condRobustTypicalSet q ε (zipSeq x y)) fun z hz =>
      le_prod_condDist_of_mem hq (Prod.fst ∘ Prod.fst) Prod.snd (mem_condRobustTypicalSet.1 hz)
  refine le_trans ?_ ((mul_le_mul_of_nonneg_right (hn _ hxy) (exp_pos _).le).trans h1)
  rw [mul_assoc, ← exp_add, condMutualInfo_triple_eq hq]
  ring_nf
  rfl

/-- **Joint typicality lemma (Lecture 2)**, part 1(b), in the form of the notes. Let
`ε' < ε < 1`. For `n` sufficiently large and every `(xⁿ, yⁿ) ∈ T_{ε'}^(n)(X, Y)`,
`P{(xⁿ, yⁿ, Z̃ⁿ) ∈ T_ε^(n)(X, Y, Z)} ≥ e^{-n(I(Y;Z|X) + δ(ε))}` with
`δ(ε) = ε (H(Z|X, Y) + H(Z|X) + 1)`. -/
theorem eventually_exp_le_prob_condRobustTypicalSet_condDist (hq : IsPMF q) {ε' : ℝ}
    (hεε : ε' < ε) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (x : Fin n → α) (y : Fin n → β),
      zipSeq x y ∈ robustTypicalSet (margFst q) n ε' →
        exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] +
          ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q] + 1)))) ≤
        prob (channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n x)
          (condRobustTypicalSet q ε (zipSeq x y)) := by
  have hlim : Tendsto (fun n : ℕ => exp (-(n * ε))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hε))
  filter_upwards [eventually_prob_condRobustTypicalSet_condDist_ge hq hεε hε,
    (tendsto_order.1 hlim).2 (1 - ε) (by linarith)] with n hn hexp x y hxy
  refine le_trans ?_ (hn x y hxy)
  calc exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] +
          ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q] + 1))))
      = exp (-(n * ε)) * exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] +
          ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q])))) := by
        rw [← exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp.le (exp_pos _).le

/-! ### Random sequences -/

/-- **Joint typicality lemma (Lecture 2)**, part 2. If `(X̃ⁿ, Ỹⁿ)` has an arbitrary pmf `P` and
`Z̃ⁿ ∼ ∏ᵢ p(z̃ᵢ|x̃ᵢ)` is conditionally independent of `Ỹⁿ` given `X̃ⁿ`, then
`P{(X̃ⁿ, Ỹⁿ, Z̃ⁿ) ∈ T_ε^(n)} ≤ e^{-n(I(Y;Z|X) - δ(ε))}`. Sequences of pairs `(x̃ᵢ, ỹᵢ)` are elements
`w` of `Fin n → α × β`, and `x̃ⁿ = Prod.fst ∘ w`. -/
theorem sum_mul_prob_condRobustTypicalSet_condDist_le (hq : IsPMF q) (n : ℕ) (ε : ℝ)
    {P : (Fin n → α × β) → ℝ} (hP : IsPMF P) :
    ∑ w : Fin n → α × β, P w *
        prob (channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w))
          (condRobustTypicalSet q ε w) ≤
      exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] -
        ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q])))) := by
  calc _ ≤ ∑ w : Fin n → α × β, P w *
        exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] -
          ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q])))) :=
        sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
          (prob_condRobustTypicalSet_condDist_le hq n ε (Prod.fst ∘ w) (Prod.snd ∘ w))
          (hP.nonneg w)
    _ = _ := by rw [← sum_mul, hP.sum_eq_one, one_mul]

/-! ### Markov chains -/

/-- If `X → Y → Z`, then `p(z|x, y) = p(z|y)` whenever `p(x, y) > 0`. -/
lemma condPMF_eq_condDist_of_markovChain (hq : IsPMF q)
    (h : MarkovChain q (Prod.fst ∘ Prod.fst) (Prod.snd ∘ Prod.fst) Prod.snd) {a : α} {b : β}
    (hab : 0 < marg q (a, b)) (c : γ) :
    condPMF q (a, b) c = condDist q Prod.snd (Prod.snd ∘ Prod.fst) b c := by
  have hm := (markovChain_iff_mul hq _ _ _).1 h a b c
  have e1 : dist q (pair (Prod.fst ∘ Prod.fst) (pair (Prod.snd ∘ Prod.fst) Prod.snd)) (a, b, c) =
      q ((a, b), c) := by
    have := dist_comp_of_injective q id (f := fun t : (α × β) × γ => (t.1.1, (t.1.2, t.2)))
      (Function.LeftInverse.injective (g := fun s => ((s.1, s.2.1), s.2.2)) fun _ => rfl)
      ((a, b), c)
    rw [dist_id] at this
    exact this
  have e2 : dist q (pair (Prod.fst ∘ Prod.fst) (Prod.snd ∘ Prod.fst)) (a, b) = marg q (a, b) := by
    rw [marg_eq_dist]
    rfl
  rw [e1, e2] at hm
  have hy : 0 < dist q (Prod.snd ∘ Prod.fst) b :=
    hab.trans_le (e2 ▸ dist_pair_le_right hq _ _ a b)
  rw [condPMF, condDist, div_eq_div_iff hab.ne' hy.ne']
  linarith

/-- **Joint typicality for Markov chains (Lecture 2).** Let `X → Y → Z` form a Markov chain and
`ε' < ε`. For every `η > 0`, for `n` sufficiently large and every `(xⁿ, yⁿ) ∈ T_{ε'}^(n)(X, Y)`, if
`Zⁿ ∼ ∏ᵢ p(zᵢ|yᵢ)`, then `P{(xⁿ, yⁿ, Zⁿ) ∈ T_ε^(n)(X, Y, Z)} ≥ 1 - η`. -/
theorem eventually_prob_condRobustTypicalSet_of_markovChain (hq : IsPMF q)
    (h : MarkovChain q (Prod.fst ∘ Prod.fst) (Prod.snd ∘ Prod.fst) Prod.snd) {ε' : ℝ}
    (hεε : ε' < ε) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ (x : Fin n → α) (y : Fin n → β),
      zipSeq x y ∈ robustTypicalSet (margFst q) n ε' →
        1 - η ≤ prob (channelExt (condDist q Prod.snd (Prod.snd ∘ Prod.fst)) n y)
          (condRobustTypicalSet q ε (zipSeq x y)) := by
  filter_upwards [eventually_prob_condRobustTypicalSet_ge hq hεε hη] with n hn x y hxy
  have heq : channelExt (condDist q Prod.snd (Prod.snd ∘ Prod.fst)) n y =
      channelExt (condPMF q) n (zipSeq x y) := by
    funext z
    refine prod_congr rfl fun i _ => ?_
    have hpos : 0 < marg q (x i, y i) := by
      have := pos_of_mem_robustTypicalSet (hq.dist _).nonneg hxy i
      rw [marg_eq_dist]
      exact this
    exact (condPMF_eq_condDist_of_markovChain hq h hpos _).symm
  rw [heq]
  exact hn _ hxy

end InfoTheory
