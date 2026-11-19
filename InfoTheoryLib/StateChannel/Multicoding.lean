/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StateChannel.Basic
public import InfoTheoryLib.Typicality.Conditional

/-!
# Random coding with subcodebooks

For each message `m`, generate a subcodebook `C(m)` of `L` sequences, all independent and
identically distributed. The decoder looks for a message whose subcodebook has a sequence that is
related to the output by `A`, typically joint typicality. This file bounds the probability of error
averaged over the codebooks, and gives the two typicality bounds that the proofs need: the
probability that an independent sequence is typical with a given one is at most `2^{-n(I - δ)}` and
at least `2^{-n(I + δ)}`.

Everything is uniform in the output, so that nothing is assumed about the law of `Yⁿ`, which need
not be i.i.d.: this is what the notes call the universality of the packing lemma.

## Main definitions

* `subcodeDecode A C m₀ y`: the decoder.

## Main statements

* `sum_codebook_subcode_le`: the bound on the average over the codebooks.
* `sum_iidPMF_ite_forall_not_mem_le`: `L` independent sequences all miss a set of probability `P`
  with probability at most `e^{-LP}`.
* `prob_iidPMF_condRobustTypicalSet_le`, `eventually_le_prob_iidPMF_condRobustTypicalSet`: the
  bounds on the probability that an independent sequence is typical with a given one.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section Decoder

variable {X Y : Type*}

open Classical in
/-- The decoder: a message whose subcodebook has a sequence related to the output by `A`. -/
def subcodeDecode {M L : ℕ} (A : X → Y → Prop) (C : Fin M → Fin L → X) (m₀ : Fin M) (y : Y) :
    Fin M :=
  if h : ∃ m l, A (C m l) y then h.choose else m₀

/-- An error occurs only if no sequence of the right subcodebook is related to the output, or some
sequence of a wrong subcodebook is. -/
lemma subcodeDecode_ne_imp {M L : ℕ} {A : X → Y → Prop} {C : Fin M → Fin L → X} {m₀ m : Fin M}
    {y : Y} (h : subcodeDecode A C m₀ y ≠ m) :
    (∀ l, ¬ A (C m l) y) ∨ ∃ m', m' ≠ m ∧ ∃ l, A (C m' l) y := by
  classical
  by_cases hy : ∃ m l, A (C m l) y
  · by_cases hm : ∃ l, A (C m l) y
    · refine Or.inr ⟨hy.choose, ?_, hy.choose_spec⟩
      simpa only [subcodeDecode, hy, dite_true] using h
    · exact Or.inl fun l hl => hm ⟨l, hl⟩
  · exact Or.inl fun l hl => hy ⟨m, l, hl⟩

variable [Fintype X] [Fintype Y]

open Classical in
/-- **Random coding with subcodebooks.** Let `Q(D, y)` be the law of the output when the subcodebook
of the message sent is `D`, and let every sequence be related to any given output with probability
at most `η`. Then the probability of error when `m` is sent, averaged over the codebooks, is at most
the probability that no sequence of the right subcodebook is related to the output, plus `M L η`. -/
theorem sum_codebook_subcode_le {μ : X → ℝ} (hμ : IsPMF μ) {M L : ℕ} (m₀ : Fin M)
    (A : X → Y → Prop) (Q : (Fin L → X) → Y → ℝ) (hQ : ∀ D y, 0 ≤ Q D y)
    (hQ1 : ∀ D, ∑ y, Q D y ≤ 1) {η : ℝ} (hη₀ : 0 ≤ η)
    (hη : ∀ y, ∑ x, μ x * (if A x y then 1 else 0) ≤ η) (m : Fin M) :
    ∑ C : Fin M → Fin L → X, iidPMF (iidPMF μ L) M C *
        ∑ y, (if subcodeDecode A C m₀ y ≠ m then Q (C m) y else 0) ≤
      ∑ D : Fin L → X, iidPMF μ L D * ∑ y, (if ∀ l, ¬ A (D l) y then Q D y else 0) +
        M * (L * η) := by
  have hν : IsPMF (iidPMF μ L) := iidPMF_isPMF hμ L
  have hνM := iidPMF_isPMF hν M
  set f : (Fin L → X) → ℝ := fun D => ∑ y, if ∀ l, ¬ A (D l) y then Q D y else 0
  set g : (Fin L → X) → (Fin L → X) → ℝ := fun D D' => ∑ y, ∑ l, if A (D' l) y then Q D y else 0
  have hpt : ∀ C : Fin M → Fin L → X, ∑ y, (if subcodeDecode A C m₀ y ≠ m then Q (C m) y else 0) ≤
      f (C m) + ∑ m' ∈ univ.erase m, g (C m) (C m') := fun C => by
    simp only [f, g]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_le_sum fun y _ => ?_
    have h1 : 0 ≤ if ∀ l, ¬ A (C m l) y then Q (C m) y else 0 := by
      split_ifs
      · exact hQ _ _
      · exact le_rfl
    have h2 : ∀ m' ∈ univ.erase m, 0 ≤ ∑ l, if A (C m' l) y then Q (C m) y else 0 := fun m' _ =>
      sum_nonneg fun l _ => by
        split_ifs
        · exact hQ _ _
        · exact le_rfl
    by_cases hd : subcodeDecode A C m₀ y ≠ m
    · simp only [hd, ne_eq, not_false_eq_true, ite_true]
      rcases subcodeDecode_ne_imp hd with h | ⟨m', hm', l, hl⟩
      · have e : (if ∀ l, ¬ A (C m l) y then Q (C m) y else 0) = Q (C m) y := by
          split_ifs
          rfl
        rw [e]
        exact le_add_of_nonneg_right (sum_nonneg h2)
      · refine le_add_of_nonneg_of_le h1 ?_
        refine le_trans ?_ (single_le_sum h2 (mem_erase.2 ⟨hm', mem_univ _⟩))
        refine le_trans ?_ (single_le_sum (f := fun l => if A (C m' l) y then Q (C m) y else 0)
          (fun l _ => by
            split_ifs
            · exact hQ _ _
            · exact le_rfl) (mem_univ l))
        simp [hl]
    · simp only [hd, ite_false]
      exact add_nonneg h1 (sum_nonneg h2)
  -- The sequence in a wrong subcodebook is independent of the output.
  have hg : ∀ D, ∑ D', iidPMF μ L D' * g D D' ≤ L * η := fun D => by
    have hstep : ∀ y l, ∑ D' : Fin L → X, iidPMF μ L D' * (if A (D' l) y then Q D y else 0) ≤
        Q D y * η := fun y l => by
      have h := sum_iidPMF_eval hμ l fun x => if A x y then Q D y else 0
      rw [h]
      have : ∀ x, μ x * (if A x y then Q D y else 0) = Q D y * (μ x * if A x y then 1 else 0) :=
        fun x => by split_ifs <;> ring
      simp_rw [this, ← mul_sum]
      exact mul_le_mul_of_nonneg_left (hη y) (hQ D y)
    simp only [g]
    simp_rw [mul_sum]
    rw [sum_comm]
    calc ∑ y, ∑ D', ∑ l, iidPMF μ L D' * (if A (D' l) y then Q D y else 0)
        = ∑ y, ∑ l, ∑ D', iidPMF μ L D' * (if A (D' l) y then Q D y else 0) :=
          sum_congr rfl fun y _ => sum_comm
      _ ≤ ∑ y, ∑ _l : Fin L, Q D y * η := sum_le_sum fun y _ => sum_le_sum fun l _ => hstep y l
      _ = (∑ y, Q D y) * (L * η) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [sum_mul]
          exact sum_congr rfl fun y _ => by ring
      _ ≤ L * η := by
          have := mul_nonneg (Nat.cast_nonneg (α := ℝ) L) hη₀
          nlinarith [hQ1 D]
  calc ∑ C : Fin M → Fin L → X, iidPMF (iidPMF μ L) M C *
        ∑ y, (if subcodeDecode A C m₀ y ≠ m then Q (C m) y else 0)
      ≤ ∑ C : Fin M → Fin L → X, iidPMF (iidPMF μ L) M C *
          (f (C m) + ∑ m' ∈ univ.erase m, g (C m) (C m')) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hpt C) (hνM.nonneg C)
    _ = ∑ C : Fin M → Fin L → X, iidPMF (iidPMF μ L) M C * f (C m) +
          ∑ m' ∈ univ.erase m, ∑ C : Fin M → Fin L → X,
            iidPMF (iidPMF μ L) M C * g (C m) (C m') := by
        simp_rw [mul_add, mul_sum]
        rw [sum_add_distrib, sum_comm (s := univ) (t := univ.erase m)]
    _ ≤ ∑ D, iidPMF μ L D * f D + ∑ _m' ∈ univ.erase m, (L * η : ℝ) := by
        rw [sum_iidPMF_eval hν m f]
        refine add_le_add le_rfl (sum_le_sum fun m' hm' => ?_)
        rw [sum_iidPMF_eval₂ hν (Ne.symm (mem_erase.1 hm').1) g]
        calc ∑ D, ∑ D', iidPMF μ L D * iidPMF μ L D' * g D D'
            = ∑ D, iidPMF μ L D * ∑ D', iidPMF μ L D' * g D D' :=
              sum_congr rfl fun D _ => by
                rw [mul_sum]
                exact sum_congr rfl fun D' _ => by ring
          _ ≤ ∑ D, iidPMF μ L D * (L * η) :=
              sum_le_sum fun D _ => mul_le_mul_of_nonneg_left (hg D) (hν.nonneg D)
          _ = L * η := by rw [← sum_mul, hν.sum_eq_one, one_mul]
    _ ≤ ∑ D, iidPMF μ L D * f D + M * (L * η) := by
        refine add_le_add le_rfl ?_
        rw [sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Nat.cast_nonneg L) hη₀)
        have := card_le_card (erase_subset m (univ : Finset (Fin M)))
        simp only [card_univ, Fintype.card_fin] at this
        exact_mod_cast this

end Decoder

/-! ### Missing a set -/

section Missing

variable {X : Type*} [Fintype X]

open Classical in
/-- `L` independent sequences all miss a set of probability `P` with probability
`(1 - P)^L ≤ e^{-LP}`. -/
theorem sum_iidPMF_ite_forall_not_mem_le {μ : X → ℝ} (hμ : IsPMF μ) (L : ℕ) (S : Finset X) :
    ∑ D : Fin L → X, iidPMF μ L D * (if ∀ l, D l ∉ S then 1 else 0) ≤
      exp (-(L * prob μ S)) := by
  have h := sum_iidPMF_mul_prod μ (n := L) fun _ x => if x ∉ S then (1 : ℝ) else 0
  have e₁ : ∀ D : Fin L → X, (∏ i, if D i ∉ S then (1 : ℝ) else 0) =
      if ∀ l, D l ∉ S then 1 else 0 := fun D => by
    by_cases hD : ∀ l, D l ∉ S
    · simp [hD]
    · have ⟨l, hl⟩ := not_forall.1 hD
      have e : (if ∀ l, D l ∉ S then (1 : ℝ) else 0) = 0 := by
        split_ifs
        rfl
      rw [e]
      exact prod_eq_zero (mem_univ l) (by simp [hl])
  simp_rw [e₁] at h
  rw [h, prod_const, card_univ, Fintype.card_fin]
  have e₂ : ∑ a, μ a * (if a ∉ S then (1 : ℝ) else 0) = 1 - prob μ S := by
    rw [← prob_compl hμ S, prob]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    congr 1
    ext a
    simp
  rw [e₂]
  have hP := prob_le_one hμ S
  calc (1 - prob μ S) ^ L ≤ exp (-prob μ S) ^ L :=
        pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-prob μ S)]) L
    _ = exp (-(L * prob μ S)) := by
        rw [← exp_natCast_mul]
        ring_nf

end Missing

/-! ### Typicality with a given sequence -/

section Typical

variable {β 𝒰 : Type*} [Fintype β] [Fintype 𝒰] {q : β × 𝒰 → ℝ} {n : ℕ} {ε : ℝ}

/-- **Packing (Lecture 3 of [elgamal2010]).** An independent `Uⁿ ∼ ∏ᵢ p(uᵢ)` is typical with a
given sequence `yⁿ`, whatever it is, with probability at most `e^{-n(I(U; Y) - δ(ε))}`. -/
theorem prob_iidPMF_condRobustTypicalSet_le (hq : IsPMF q) (ε : ℝ) (y : Fin n → β) :
    prob (iidPMF (margSnd q) n) (condRobustTypicalSet q ε y) ≤
      exp (-(n * (I[Prod.snd : Prod.fst ; q] -
        ε * (H[Prod.snd ; q] + H[Prod.snd | Prod.fst ; q])))) := by
  have hI := mutualInfo_eq_entropy_sub_condEntropy hq (Prod.snd : β × 𝒰 → 𝒰) Prod.fst
  have h := prob_le_card_mul (μ := iidPMF (margSnd q) n) (S := condRobustTypicalSet q ε y)
    (c := exp (-(n * (entropy (margSnd q) - ε * entropy (margSnd q))))) fun u hu =>
      iidPMF_le_of_mem_robustTypicalSet (hq.dist _)
        (snd_mem_robustTypicalSet (mem_condRobustTypicalSet.1 hu))
  refine h.trans ((mul_le_mul_of_nonneg_right (card_condRobustTypicalSet_le hq ε y)
    (exp_pos _).le).trans ?_)
  rw [← exp_add, hI]
  have e : H[Prod.snd ; q] = entropy (margSnd q) := rfl
  rw [e]
  exact exp_le_exp.2 (by nlinarith)

/-- **Covering (Lecture 3 of [elgamal2010]).** An independent `Uⁿ ∼ ∏ᵢ p(uᵢ)` is typical with a
typical sequence `yⁿ` with probability at least `(1 - ε) e^{-n(I(U; Y) + δ(ε))}`. -/
theorem eventually_le_prob_iidPMF_condRobustTypicalSet (hq : IsPMF q) {ε' : ℝ} (hεε : ε' < ε)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y ∈ robustTypicalSet (margFst q) n ε',
      (1 - ε) * exp (-(n * (I[Prod.snd : Prod.fst ; q] +
          ε * (H[Prod.snd ; q] + H[Prod.snd | Prod.fst ; q])))) ≤
        prob (iidPMF (margSnd q) n) (condRobustTypicalSet q ε y) := by
  filter_upwards [eventually_card_condRobustTypicalSet_ge hq hεε hε] with n hn y hy
  have hI := mutualInfo_eq_entropy_sub_condEntropy hq (Prod.snd : β × 𝒰 → 𝒰) Prod.fst
  have h := card_mul_le_prob (μ := iidPMF (margSnd q) n) (S := condRobustTypicalSet q ε y)
    (c := exp (-(n * (entropy (margSnd q) + ε * entropy (margSnd q))))) fun u hu =>
      le_iidPMF_of_mem_robustTypicalSet (hq.dist _)
        (snd_mem_robustTypicalSet (mem_condRobustTypicalSet.1 hu))
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (hn y hy) (exp_pos _).le)
  rw [hI, mul_assoc, ← exp_add]
  have e : H[Prod.snd ; q] = entropy (margSnd q) := rfl
  rw [e]
  congr 2
  ring

/-- The pmf `p(u) p(y | u)` of `(Y, U)`. -/
def revJoint (p : 𝒰 → ℝ) (V : 𝒰 → β → ℝ) : β × 𝒰 → ℝ := fun z => p z.2 * V z.2 z.1

lemma revJoint_isPMF {p : 𝒰 → ℝ} (hp : IsPMF p) {V : 𝒰 → β → ℝ} (hV : IsChannel V) :
    IsPMF (revJoint p V) := by
  refine ⟨fun z => mul_nonneg (hp.nonneg _) ((hV _).nonneg _), ?_⟩
  simp only [revJoint]
  rw [Fintype.sum_prod_type_right]
  simp only [← mul_sum, (hV _).sum_eq_one, mul_one, hp.sum_eq_one]

lemma margSnd_revJoint {p : 𝒰 → ℝ} {V : 𝒰 → β → ℝ} (hV : IsChannel V) :
    margSnd (revJoint p V) = p := by
  classical
  funext u
  simp only [margSnd, dist, revJoint]
  rw [Fintype.sum_prod_type_right]
  simp [← mul_sum, (hV _).sum_eq_one]

lemma mutualInfo_revJoint (p : 𝒰 → ℝ) (V : 𝒰 → β → ℝ) :
    I[Prod.snd : Prod.fst ; revJoint p V] = mutualInfoOf p V := by
  classical
  refine mutualInfo_eq_of_dist_pair_eq ?_
  funext ⟨u, y⟩
  simp only [dist, pair, revJoint, jointOf, Prod.mk.injEq, Fintype.sum_prod_type, ite_and]
  simp

omit [Fintype β] [Fintype 𝒰] in
lemma iidPMF_revJoint (p : 𝒰 → ℝ) (V : 𝒰 → β → ℝ) (u : Fin n → 𝒰) (y : Fin n → β) :
    iidPMF (revJoint p V) n (zipSeq y u) = iidPMF p n u * channelExt V n u y := by
  simp only [iidPMF, revJoint, channelExt, zipSeq, prod_mul_distrib]

open Classical in
/-- `P{(Uⁿ, Yⁿ) ∉ T_ε^(n)(Y, U)} = 1 - P{(Yⁿ, Uⁿ) ∈ T_ε^(n)}` for `(U, Y) ∼ p(u) p(y | u)`. -/
lemma sum_iidPMF_mul_sum_ite_not_mem {p : 𝒰 → ℝ} (hp : IsPMF p) {V : 𝒰 → β → ℝ}
    (hV : IsChannel V) (ε : ℝ) :
    ∑ u, iidPMF p n u * ∑ y, (if zipSeq y u ∉ robustTypicalSet (revJoint p V) n ε then
        channelExt V n u y else 0) =
      1 - prob (iidPMF (revJoint p V) n) (robustTypicalSet (revJoint p V) n ε) := by
  have hq := iidPMF_isPMF (revJoint_isPMF hp hV) n
  rw [← prob_compl hq, prob]
  have hequiv := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => β)
    (fun _ => 𝒰)).symm.sum_comp fun z : Fin n → β × 𝒰 =>
    if z ∉ robustTypicalSet (revJoint p V) n ε then iidPMF (revJoint p V) n z else 0
  have e : ∑ z ∈ (robustTypicalSet (revJoint p V) n ε)ᶜ, iidPMF (revJoint p V) n z =
      ∑ z, if z ∉ robustTypicalSet (revJoint p V) n ε then iidPMF (revJoint p V) n z else 0 := by
    rw [← sum_filter]
    congr 1
    ext z
    simp
  rw [e, ← hequiv, Fintype.sum_prod_type_right]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  have hz : (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => β) (fun _ => 𝒰)).symm (y, u) =
      zipSeq y u := rfl
  rw [hz, iidPMF_revJoint]
  split_ifs <;> simp

end Typical

end InfoTheory
