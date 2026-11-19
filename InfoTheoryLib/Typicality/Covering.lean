/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Typicality.JointTypicalityLemma

/-!
# The covering lemma

Let `(U, X, X̂) ∼ p(u, x, x̂)`, let `(Uⁿ, Xⁿ)` be arbitrarily distributed with
`P{(Uⁿ, Xⁿ) ∈ T_{ε'}^(n)} → 1`, and let `X̂ⁿ(m)`, `m ∈ 𝒜`, be random sequences, conditionally
independent of each other and of `Xⁿ` given `Uⁿ`, each distributed according to `∏ᵢ p(x̂ᵢ|uᵢ)`.
Then the probability that no `X̂ⁿ(m)` is jointly typical with `(Uⁿ, Xⁿ)` tends to `0` if
`|𝒜| ≥ e^{nR}` with `R > I(X; X̂|U) + δ(ε)`. In lossy source coding, the `X̂ⁿ(m)` are the
reproduction sequences and `Xⁿ` is the source sequence: the lemma says that some reproduction
sequence covers the source. It is dual to the packing lemma.

Given `(Uⁿ, Xⁿ) = (uⁿ, xⁿ)` typical, each `X̂ⁿ(m)` is jointly typical with probability at least
`a ≐ e^{-nI(X;X̂|U)}` by the joint typicality lemma, so by independence none is with probability at
most `(1 - a)^{|𝒜|} ≤ e^{-|𝒜| a}`.

## Main statements

* `prob_forall_not_mem_robustTypicalSet_le`: the bound
  `P{no X̂ⁿ(m) is typical} ≤ P{(Uⁿ, Xⁿ) ∉ 𝒮} + e^{-|𝒜| a}` when each `X̂ⁿ(m)` is typical with
  probability at least `a` given `(Uⁿ, Xⁿ) ∈ 𝒮`.
* `eventually_prob_forall_not_mem_robustTypicalSet_le`: **the covering lemma**.

## Implementation notes

The random objects live on a finite probability space `(Ω, μ)`. The pair `(Uⁿ, Xⁿ)` is a single
random sequence `W : Ω → Fin n → υ × α` and the reproduction sequences are
`Xh : Ω → ι → Fin n → β`. The triple is ordered as `((U, X), X̂)`, as in the joint typicality
lemma: its pmf is `q : (υ × α) × β → ℝ`, `I(X; X̂|U)` is
`I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q]` and `p(x̂|u)` is
`condDist q Prod.snd (Prod.fst ∘ Prod.fst)`. The hypothesis on the joint law of `W` and the family
`Xh` expresses both the conditional independence and the conditional law of the `X̂ⁿ(m)`.

As in the joint typicality lemma, `(Uⁿ, Xⁿ)` is assumed typical for some `ε' < ε` (the lecture
notes take `ε' = ε`): for sequences on the boundary of `T_ε^(n)` no `x̂ⁿ` may be jointly typical.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u v

variable {υ α β : Type*} [Fintype υ] [Fintype α] [Fintype β] {q : (υ × α) × β → ℝ}

omit [Fintype υ] [Fintype α] [Fintype β] in
lemma channelExt_condDist_nonneg {Ω γ δ : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (Z : Ω → δ) (X : Ω → γ) {n : ℕ} (x : Fin n → γ) (z : Fin n → δ) :
    0 ≤ channelExt (condDist μ Z X) n x z :=
  prod_nonneg fun _ _ => condDist_nonneg hμ _ _ _ _

omit [Fintype υ] [Fintype α] [Fintype β] in
/-- The total mass `∑_{zⁿ} p(zⁿ|xⁿ)` of a product of conditional pmfs is at most `1`. -/
lemma sum_channelExt_condDist_le_one {Ω γ δ : Type*} [Fintype Ω] [Fintype δ] {μ : Ω → ℝ}
    (hμ : IsPMF μ) (Z : Ω → δ) (X : Ω → γ) {n : ℕ} (x : Fin n → γ) :
    ∑ z, channelExt (condDist μ Z X) n x z ≤ 1 := by
  classical
  rw [show ∑ z, channelExt (condDist μ Z X) n x z = ∏ i, ∑ b, condDist μ Z X (x i) b from
    (Fintype.prod_sum _).symm]
  refine prod_le_one₀ (fun i _ => sum_nonneg fun b _ => condDist_nonneg hμ _ _ _ _)
    fun i _ => ?_
  by_cases h : dist μ X (x i) = 0
  · simp [condDist, h]
  · rw [(condDist_isPMF hμ Z X h).sum_eq_one]

open Classical in
/-- If, given `(Uⁿ, Xⁿ) = w ∈ 𝒮`, each `X̂ⁿ(m)` is jointly typical with `w` with probability at
least `a`, then the probability that no `X̂ⁿ(m)` is jointly typical with `(Uⁿ, Xⁿ)` is at most
`P{(Uⁿ, Xⁿ) ∉ 𝒮} + e^{-|𝒜| a}`. -/
theorem prob_forall_not_mem_robustTypicalSet_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (hq : IsPMF q) {n : ℕ} {μ : Ω → ℝ} (hμ : IsPMF μ) (W : Ω → Fin n → υ × α)
    (Xh : Ω → ι → Fin n → β)
    (hX : ∀ w xs, dist μ (pair W Xh) (w, xs) = dist μ W w *
      ∏ m, channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w) (xs m))
    (ε : ℝ) (S : Finset (Fin n → υ × α)) {a : ℝ}
    (ha : ∀ w ∈ S, a ≤ prob (channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n
      (Prod.fst ∘ w)) (condRobustTypicalSet q ε w)) :
    prob μ (univ.filter fun ω => ∀ m, zipSeq (W ω) (Xh ω m) ∉ robustTypicalSet q n ε) ≤
      prob μ (univ.filter fun ω => W ω ∉ S) + exp (-(Fintype.card ι * a)) := by
  set V := condDist q Prod.snd (Prod.fst ∘ Prod.fst)
  set C : (Fin n → υ × α) → Finset (Fin n → β) := fun w => condRobustTypicalSet q ε w
  -- The probability that `X̂ⁿ(m) ∉ C w`, for each `m`.
  set s : (Fin n → υ × α) → ℝ :=
    fun w => ∑ x, if x ∈ C w then 0 else channelExt V n (Prod.fst ∘ w) x
  have hV0 : ∀ (w : Fin n → υ × α) (x : Fin n → β), 0 ≤ channelExt V n (Prod.fst ∘ w) x :=
    fun w x => channelExt_condDist_nonneg hq Prod.snd (Prod.fst ∘ Prod.fst) _ x
  have hs0 : ∀ w, 0 ≤ s w := fun w =>
    sum_nonneg fun x _ => by
      split_ifs
      · exact le_rfl
      · exact hV0 w x
  have hs1 : ∀ w, s w ≤ 1 - prob (channelExt V n (Prod.fst ∘ w)) (C w) := fun w => by
    have htot := sum_channelExt_condDist_le_one hq Prod.snd (Prod.fst ∘ Prod.fst) (Prod.fst ∘ w)
    have e2 : prob (channelExt V n (Prod.fst ∘ w)) (C w) =
        ∑ x, if x ∈ C w then channelExt V n (Prod.fst ∘ w) x else 0 := by
      rw [sum_ite_mem, univ_inter]
      rfl
    have : s w + prob (channelExt V n (Prod.fst ∘ w)) (C w) =
        ∑ x, channelExt V n (Prod.fst ∘ w) x := by
      rw [e2, ← sum_add_distrib]
      exact sum_congr rfl fun x _ => by split_ifs <;> ring
    linarith
  -- The event as a sum over `(w, x̂ⁿ(·))`.
  have hevent : prob μ (univ.filter fun ω => ∀ m, zipSeq (W ω) (Xh ω m) ∉ robustTypicalSet q n ε) =
      ∑ w, dist μ W w * s w ^ Fintype.card ι := by
    have h := sum_dist_mul μ (pair W Xh)
      fun z => if ∀ m, zipSeq z.1 (z.2 m) ∉ robustTypicalSet q n ε then (1 : ℝ) else 0
    rw [prob, sum_filter]
    have e : (∑ ω, if ∀ m, zipSeq (W ω) (Xh ω m) ∉ robustTypicalSet q n ε then μ ω else 0) =
        ∑ z, dist μ (pair W Xh) z *
          if ∀ m, zipSeq z.1 (z.2 m) ∉ robustTypicalSet q n ε then 1 else 0 := by
      rw [h]
      refine sum_congr rfl fun ω _ => ?_
      by_cases hc : ∀ m, zipSeq (W ω) (Xh ω m) ∉ robustTypicalSet q n ε <;> simp [pair, hc]
    rw [e, Fintype.sum_prod_type]
    refine sum_congr rfl fun w _ => ?_
    simp_rw [hX, mul_assoc, ← mul_sum]
    congr 1
    have hpow : s w ^ Fintype.card ι = ∏ _m : ι,
        ∑ x, (if x ∈ C w then 0 else channelExt V n (Prod.fst ∘ w) x) := by
      rw [prod_const, card_univ]
    rw [hpow, Fintype.prod_sum]
    refine sum_congr rfl fun xs _ => ?_
    by_cases hc : ∀ m, zipSeq w (xs m) ∉ robustTypicalSet q n ε
    · rw [ite_eq_left hc, mul_one]
      refine prod_congr rfl fun m _ => ?_
      have : xs m ∉ C w := fun h' => hc m (mem_condRobustTypicalSet.1 h')
      simp [this]
    · rw [ite_eq_right hc, mul_zero]
      push Not at hc
      obtain ⟨m, hm⟩ := hc
      refine (prod_eq_zero (mem_univ m) ?_).symm
      have : xs m ∈ C w := mem_condRobustTypicalSet.2 hm
      simp [this]
  rw [hevent]
  -- Split according to `w ∈ S`.
  have hbound : ∀ w, dist μ W w * s w ^ Fintype.card ι ≤
      (if w ∈ S then 0 else dist μ W w) + dist μ W w * exp (-(Fintype.card ι * a)) := fun w => by
    have hd := dist_nonneg hμ W w
    by_cases hw : w ∈ S
    · rw [ite_eq_left hw, zero_add]
      refine mul_le_mul_of_nonneg_left ?_ hd
      have h1 : s w ≤ exp (-a) := (hs1 w).trans
        ((sub_le_sub_left (ha w hw) 1).trans (by linarith [add_one_le_exp (-a)]))
      calc s w ^ Fintype.card ι ≤ exp (-a) ^ Fintype.card ι := pow_le_pow_left₀ (hs0 w) h1 _
        _ = exp (-(Fintype.card ι * a)) := by rw [← exp_natCast_mul]; ring_nf
    · rw [ite_eq_right hw]
      have hp0 := prob_nonneg (hV0 w) (C w)
      have : s w ^ Fintype.card ι ≤ 1 := pow_le_one₀ (hs0 w) ((hs1 w).trans (by linarith))
      nlinarith [exp_pos (-(Fintype.card ι * a))]
  refine (sum_le_sum fun w _ => hbound w).trans_eq ?_
  rw [sum_add_distrib, ← sum_mul, (hμ.dist W).sum_eq_one, one_mul]
  congr 1
  have h := sum_dist_mul μ W fun w => if w ∈ S then (0 : ℝ) else 1
  simp only [mul_ite, mul_zero, mul_one] at h
  rw [h, prob, sum_filter]
  exact sum_congr rfl fun ω _ => by by_cases hc : W ω ∈ S <;> simp [hc]

open Classical in
/-- **Covering lemma (Lecture 3).** Let `ε' < ε` and `0 < ε`. For `n` sufficiently large, let
`(Uⁿ, Xⁿ)` be arbitrarily distributed and let `X̂ⁿ(m)`, `m ∈ 𝒜`, be conditionally independent of
each other and of `Xⁿ` given `Uⁿ`, each distributed according to `∏ᵢ p(x̂ᵢ|uᵢ)`. Then
`P{(Uⁿ, Xⁿ, X̂ⁿ(m)) ∉ T_ε^(n) for all m ∈ 𝒜} ≤ P{(Uⁿ, Xⁿ) ∉ T_{ε'}^(n)} + e^{-|𝒜| a}` with
`a = (1 - ε) e^{-n(I(X; X̂|U) + δ(ε))}` and `δ(ε) = ε (H(X̂|U, X) + H(X̂|U))`. If
`P{(Uⁿ, Xⁿ) ∈ T_{ε'}^(n)} → 1` and `|𝒜| ≥ e^{nR}` with `R > I(X; X̂|U) + δ(ε)`, both terms tend to
`0`. -/
theorem eventually_prob_forall_not_mem_robustTypicalSet_le (hq : IsPMF q) {ε' ε : ℝ}
    (hεε : ε' < ε) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι] {μ : Ω → ℝ},
      IsPMF μ → ∀ (W : Ω → Fin n → υ × α) (Xh : Ω → ι → Fin n → β),
      (∀ w xs, dist μ (pair W Xh) (w, xs) = dist μ W w *
        ∏ m, channelExt (condDist q Prod.snd (Prod.fst ∘ Prod.fst)) n (Prod.fst ∘ w) (xs m)) →
      prob μ (univ.filter fun ω => ∀ m, zipSeq (W ω) (Xh ω m) ∉ robustTypicalSet q n ε) ≤
        prob μ (univ.filter fun ω => W ω ∉ robustTypicalSet (margFst q) n ε') +
          exp (-(Fintype.card ι * ((1 - ε) *
            exp (-(n * (I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; q] +
              ε * (H[Prod.snd | Prod.fst ; q] + H[Prod.snd | Prod.fst ∘ Prod.fst ; q]))))))) := by
  filter_upwards [eventually_prob_condRobustTypicalSet_condDist_ge hq hεε hε] with n hn
  intro Ω ι _ _ μ hμ W Xh hX
  exact prob_forall_not_mem_robustTypicalSet_le hq hμ W Xh hX ε _
    fun w hw => hn (Prod.fst ∘ w) (Prod.snd ∘ w) hw

end InfoTheory
