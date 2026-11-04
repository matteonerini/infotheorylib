/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Typicality.JointTypicalityLemma

/-!
# The packing lemma

Let `(U, X, Y) ∼ p(u, x, y)`, let `(Ũⁿ, Ỹⁿ)` be arbitrarily distributed, and let `Xⁿ(m)`,
`m ∈ 𝒜`, be random sequences, each distributed according to `∏ᵢ p(xᵢ|ũᵢ)` and conditionally
independent of `Ỹⁿ` given `Ũⁿ` (but arbitrarily dependent on each other). Then the probability
that some `Xⁿ(m)` is jointly typical with `(Ũⁿ, Ỹⁿ)` is at most
`|𝒜| e^{-n(I(X;Y|U) - δ(ε))}`, which tends to `0` if `|𝒜| ≤ e^{nR}` with `R < I(X;Y|U) - δ(ε)`.
In channel coding, the `Xⁿ(m)` are the codewords other than the transmitted one, and `Ỹⁿ` is the
received sequence: the lemma bounds the probability that a wrong codeword is decoded. The proof is
the union bound together with the joint typicality lemma.

## Main statements

* `prob_exists_mem_robustTypicalSet_le`: **the packing lemma**, with an explicit bound.
* `prob_exists_mem_robustTypicalSet_le_exp`: the packing lemma for `|𝒜| ≤ e^{nR}`.

## Implementation notes

The random objects live on a finite probability space `(Ω, μ)`. The pair `(Ũⁿ, Ỹⁿ)` is a single
random sequence `W : Ω → Fin n → υ × β` of pairs, and the codewords are `Xc : ι → Ω → Fin n → α`.
The triple is ordered as `((U, Y), X)`, as in the joint typicality lemma, so its pmf is
`q : (υ × β) × α → ℝ`, `I(X;Y|U)` is `I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q]`
and `p(x|u)` is `condDist q Prod.snd (Prod.fst ∘ Prod.fst)`. The hypothesis on the law of each
`(W, Xc m)` says both that `Xⁿ(m) ∼ ∏ᵢ p(xᵢ|ũᵢ)` and that it is conditionally independent of
`Ỹⁿ` given `Ũⁿ`. Rates are in nats.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω ι υ α β : Type*} [Fintype Ω] [Fintype ι] [Fintype υ] [Fintype α] [Fintype β]
  {q : (υ × β) × α → ℝ} {n : ℕ}

open Classical in
/-- The probability that one random sequence `Xⁿ(m) ∼ ∏ᵢ p(xᵢ|ũᵢ)` is jointly typical with an
arbitrarily distributed `(Ũⁿ, Ỹⁿ)`. -/
lemma prob_mem_robustTypicalSet_eq {μ : Ω → ℝ} (W : Ω → Fin n → υ × β) (X : Ω → Fin n → α)
    (hX : ∀ w x, dist μ (pair W X) (w, x) =
      dist μ W w * channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w) x)
    (ε : ℝ) :
    prob μ (univ.filter fun ω => zipSeq (W ω) (X ω) ∈ robustTypicalSet q n ε) =
      ∑ w, dist μ W w *
        prob (channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w))
          (condRobustTypicalSet q ε w) := by
  classical
  have h := sum_dist_mul μ (pair W X)
    fun z => if zipSeq z.1 z.2 ∈ robustTypicalSet q n ε then (1 : ℝ) else 0
  have e : (∑ ω, if zipSeq (W ω) (X ω) ∈ robustTypicalSet q n ε then μ ω else 0) =
      ∑ z, dist μ (pair W X) z * if zipSeq z.1 z.2 ∈ robustTypicalSet q n ε then 1 else 0 := by
    rw [h]
    refine sum_congr rfl fun ω _ => ?_
    by_cases hc : zipSeq (W ω) (X ω) ∈ robustTypicalSet q n ε <;> simp [pair, hc]
  rw [prob, sum_filter, e, Fintype.sum_prod_type]
  refine sum_congr rfl fun w _ => ?_
  calc ∑ y, dist μ (pair W X) (w, y) *
        (if zipSeq (w, y).1 (w, y).2 ∈ robustTypicalSet q n ε then 1 else 0)
      = ∑ y, if y ∈ condRobustTypicalSet q ε w then dist μ W w *
          channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w) y else 0 := by
        refine sum_congr rfl fun y _ => ?_
        have hiff : zipSeq w y ∈ robustTypicalSet q n ε ↔ y ∈ condRobustTypicalSet q ε w :=
          mem_condRobustTypicalSet.symm
        by_cases hc : y ∈ condRobustTypicalSet q ε w <;> simp [hc, hiff, hX]
    _ = _ := by rw [sum_ite_mem, univ_inter, prob, mul_sum]

open Classical in
/-- **Packing lemma (Lecture 3).** Let `(Ũⁿ, Ỹⁿ)` be arbitrarily distributed and let `Xⁿ(m)`,
`m ∈ 𝒜`, each be distributed according to `∏ᵢ p(xᵢ|ũᵢ)` and conditionally independent of `Ỹⁿ`
given `Ũⁿ`. Then
`P{(Ũⁿ, Xⁿ(m), Ỹⁿ) ∈ T_ε^(n) for some m ∈ 𝒜} ≤ |𝒜| e^{-n(I(X;Y|U) - δ(ε))}` with
`δ(ε) = ε (H(X|U, Y) + H(X|U))`. -/
theorem prob_exists_mem_robustTypicalSet_le (hq : IsPMF q) {μ : Ω → ℝ} (hμ : IsPMF μ)
    (W : Ω → Fin n → υ × β) (Xc : ι → Ω → Fin n → α)
    (hX : ∀ m w x, dist μ (pair W (Xc m)) (w, x) =
      dist μ W w * channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w) x)
    (ε : ℝ) :
    prob μ (univ.filter fun ω => ∃ m, zipSeq (W ω) (Xc m ω) ∈ robustTypicalSet q n ε) ≤
      Fintype.card ι *
        exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] -
          ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q])))) := by
  classical
  have hsub : (univ.filter fun ω => ∃ m, zipSeq (W ω) (Xc m ω) ∈ robustTypicalSet q n ε) ⊆
      univ.biUnion fun m => univ.filter fun ω => zipSeq (W ω) (Xc m ω) ∈ robustTypicalSet q n ε :=
    fun ω hω => by
      obtain ⟨m, hm⟩ := (mem_filter.1 hω).2
      exact mem_biUnion.2 ⟨m, mem_univ m, mem_filter.2 ⟨mem_univ ω, hm⟩⟩
  refine (prob_mono hμ.nonneg hsub).trans ((prob_biUnion_le hμ.nonneg _ _).trans ?_)
  rw [← card_univ, ← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun m _ => ?_
  rw [prob_mem_robustTypicalSet_eq W (Xc m) (hX m)]
  exact sum_mul_prob_condRobustTypicalSet_condDist_le hq n ε (hμ.dist W)

open Classical in
/-- **Packing lemma (Lecture 3)**, for `|𝒜| ≤ e^{nR}`: the probability that some `Xⁿ(m)` is jointly
typical with `(Ũⁿ, Ỹⁿ)` is at most `e^{-n(I(X;Y|U) - δ(ε) - R)}`, which tends to `0` as `n → ∞`
if `R < I(X;Y|U) - δ(ε)`. -/
theorem prob_exists_mem_robustTypicalSet_le_exp (hq : IsPMF q) {μ : Ω → ℝ} (hμ : IsPMF μ)
    (W : Ω → Fin n → υ × β) (Xc : ι → Ω → Fin n → α)
    (hX : ∀ m w x, dist μ (pair W (Xc m)) (w, x) =
      dist μ W w * channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w) x)
    (ε : ℝ) {R : ℝ} (hA : (Fintype.card ι : ℝ) ≤ exp (n * R)) :
    prob μ (univ.filter fun ω => ∃ m, zipSeq (W ω) (Xc m ω) ∈ robustTypicalSet q n ε) ≤
      exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] -
        ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q]) - R))) := by
  refine (prob_exists_mem_robustTypicalSet_le hq hμ W Xc hX ε).trans ?_
  refine (mul_le_mul_of_nonneg_right hA (exp_pos _).le).trans_eq ?_
  rw [← exp_add]
  ring_nf

end InfoTheory
