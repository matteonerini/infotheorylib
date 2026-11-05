/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTung

/-!
# Distributed lossy source coding: binning

The encoders of Berger–Tung coding send the bin indices of their codewords, and the decoder finds
the
unique jointly typical pair of the two bins. This file bounds the probability of the corresponding
error event, by the mutual packing lemma. As in Lecture 12, we bin at random, independently of the
codebooks, which avoids the analogue of Lemma 1 of Lecture 12 used on page 13-12.

## Main definitions

* `btYU P κ₁ κ₂`: the law of `(U₁, U₂)`.
* `btPackExp`: the exponent `I(U₁; U₂) - δ(ε)` of the mutual packing lemma.
* `btIndex`: the decoder.

## Main statements

* `sum_iidPMF_snd_typical_le`, `sum_iidPMF_fst_typical_le`: the bound for a fixed sequence.
* `prob_mutual_packing_le`: **the mutual packing lemma**.
* `btIndex_not_mem_le`: the error event `E₄`.
* `exists_bt_code_le`: the bound on the probability of error of a code.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ υ₁ υ₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂]
  {P : α₁ × α₂ → ℝ} {κ₁ : α₁ → υ₁ → ℝ} {κ₂ : α₂ → υ₂ → ℝ}

/-! ### The mutual packing lemma -/

section Packing

/-- The law of `(U₁, U₂)`. -/
def btUU (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) : υ₁ × υ₂ → ℝ :=
  dist (btLaw P κ₁ κ₂) fun z => (z.1.1.2, z.2)

lemma btUU_isPMF (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    IsPMF (btUU P κ₁ κ₂) :=
  (btLaw_isPMF hP h₁ h₂).dist _

/-- The exponent of the mutual packing lemma: `I(U₁; U₂) - ε (H(U₁) + H(U₂) + H(U₁|U₂) + H(U₂|U₁))`.
-/
def btPackExp {a b : Type*} [Fintype a] [Fintype b] (J : a × b → ℝ) (ε : ℝ) : ℝ :=
  I[Prod.fst : Prod.snd ; J] - ε * (H[Prod.fst ; J] + H[Prod.snd ; J] +
    H[Prod.fst | Prod.snd ; J] + H[Prod.snd | Prod.fst ; J])

variable {a b : Type*} [Fintype a] [Fintype b] {J : a × b → ℝ} {n : ℕ} {ε : ℝ}

/-- **The mutual packing lemma, for one sequence (Lecture 13, page 13-12).** An independent `Uⁿ` is
typical
with a given sequence with probability at most `e^{-n (I(U₁; U₂) - δ(ε))}`. -/
theorem sum_iidPMF_snd_typical_le (hJ : IsPMF J) (hε : 0 ≤ ε) (u : Fin n → a) :
    ∑ v, iidPMF (margSnd J) n v *
        (open Classical in if zipSeq u v ∈ robustTypicalSet J n ε then (1 : ℝ) else 0) ≤
      exp (-(n * btPackExp J ε)) := by
  classical
  have h := prob_iidPMF_condRobustTypicalSet_le hJ ε u
  have e : ∑ v, iidPMF (margSnd J) n v *
      (if zipSeq u v ∈ robustTypicalSet J n ε then (1 : ℝ) else 0) =
      prob (iidPMF (margSnd J) n) (condRobustTypicalSet J ε u) := by
    have e1 : prob (iidPMF (margSnd J) n) (condRobustTypicalSet J ε u) =
        ∑ v, if v ∈ condRobustTypicalSet J ε u then iidPMF (margSnd J) n v else 0 := by
      rw [prob, sum_ite_mem, univ_inter]
    rw [e1]
    refine sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ condRobustTypicalSet J ε u
    · have := mem_condRobustTypicalSet.1 hv
      simp [hv, this]
    · have : zipSeq u v ∉ robustTypicalSet J n ε := fun h' => hv (mem_condRobustTypicalSet.2 h')
      simp [hv, this]
  rw [e]
  refine h.trans (exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))))
  have hI : I[Prod.snd : Prod.fst ; J] = I[Prod.fst : Prod.snd ; J] := mutualInfo_comm hJ _ _
  rw [hI, btPackExp]
  have h1 : 0 ≤ H[Prod.fst ; J] := entropy_nonneg (hJ.dist _)
  have h2 : 0 ≤ H[Prod.fst | Prod.snd ; J] := condEntropy_nonneg hJ _ _
  nlinarith [mul_nonneg hε (add_nonneg h1 h2)]

/-- **The mutual packing lemma, for the other sequence.** -/
theorem sum_iidPMF_fst_typical_le (hJ : IsPMF J) (hε : 0 ≤ ε) (v : Fin n → b) :
    ∑ u, iidPMF (margFst J) n u *
        (open Classical in if zipSeq u v ∈ robustTypicalSet J n ε then (1 : ℝ) else 0) ≤
      exp (-(n * btPackExp J ε)) := by
  classical
  have hJ' : IsPMF (dist J Prod.swap) := hJ.dist _
  have hsw := sum_iidPMF_snd_typical_le (J := dist J Prod.swap) hJ' hε v
  have hm : margSnd (dist J Prod.swap) = margFst J := by
    rw [show margSnd (dist J Prod.swap) = dist (dist J Prod.swap) Prod.snd from rfl,
      ← dist_comp_eq]
    rfl
  have hf : dist (dist J Prod.swap) Prod.fst = dist J Prod.snd := by
    rw [← dist_comp_eq]
    rfl
  have hexp : btPackExp (dist J Prod.swap) ε = btPackExp J ε := by
    have hp : dist (dist J Prod.swap) (pair Prod.fst Prod.snd) = dist J (pair Prod.snd Prod.fst) :=
      by
      rw [dist_pair_fst_snd]
      rfl
    have hIeq : I[Prod.fst : Prod.snd ; dist J Prod.swap] = I[Prod.fst : Prod.snd ; J] := by
      rw [mutualInfo_eq_of_dist_pair_eq hp, mutualInfo_comm hJ]
    have h1 : H[Prod.fst ; dist J Prod.swap] = H[Prod.snd ; J] := congrArg entropy hf
    have h2 : H[Prod.snd ; dist J Prod.swap] = H[Prod.fst ; J] := congrArg entropy hm
    have h3 : H[Prod.fst | Prod.snd ; dist J Prod.swap] = H[Prod.snd | Prod.fst ; J] := by
      refine condEntropy_eq_of_dist_pair_eq hJ' hJ ?_
      rw [← dist_comp_eq]
      rfl
    have h4 : H[Prod.snd | Prod.fst ; dist J Prod.swap] = H[Prod.fst | Prod.snd ; J] := by
      refine condEntropy_eq_of_dist_pair_eq hJ' hJ ?_
      rw [show pair Prod.fst Prod.snd = (id : b × a → b × a) from rfl, dist_id]
      rfl
    rw [btPackExp, btPackExp, hIeq, h1, h2, h3, h4]
    ring
  rw [hm, hexp] at hsw
  refine le_trans (le_of_eq (sum_congr rfl fun u _ => ?_)) hsw
  congr 1
  by_cases h : zipSeq u v ∈ robustTypicalSet J n ε
  · have h2 : zipSeq v u ∈ robustTypicalSet (dist J Prod.swap) n ε :=
      zipSeq_swap_mem_robustTypicalSet h
    simp [h, h2]
  · have h2 : zipSeq v u ∉ robustTypicalSet (dist J Prod.swap) n ε := fun h3 => h (by
      have h4 := zipSeq_swap_mem_robustTypicalSet h3
      have e : dist (dist J Prod.swap) Prod.swap = J := by
        rw [← dist_comp_eq]
        have : (Prod.swap ∘ Prod.swap : a × b → a × b) = id := by
          funext z
          simp
        rw [this, dist_id]
      rwa [e] at h4)
    simp [h, h2]

open Classical in
/-- **The mutual packing lemma (Lecture 13, page 13-12).** Let `U₁ⁿ(l₁)` and `U₂ⁿ(l₂)` be two
independent
families of random sequences, with arbitrary dependence inside each family and with each sequence of
the second family distributed according to `∏ᵢ p(uᵢ)`. Then some pair of sequences is jointly
typical
with probability at most `L₁ L₂ e^{-n (I(U₁; U₂) - δ(ε))}`. The notes also assume the law of the
first
family, which the proof does not use. -/
theorem prob_mutual_packing_le (hJ : IsPMF J) (hε : 0 ≤ ε) {L₁ L₂ : ℕ}
    {ρ₁ : (Fin L₁ → Fin n → a) → ℝ} {ρ₂ : (Fin L₂ → Fin n → b) → ℝ} (hρ₁ : IsPMF ρ₁)
    (hρ₂ : IsPMF ρ₂)
    (h₂ : ∀ (l : Fin L₂) (F : (Fin n → b) → ℝ), ∑ C, ρ₂ C * F (C l) =
      ∑ v, iidPMF (margSnd J) n v * F v) :
    ∑ C₁, ρ₁ C₁ * ∑ C₂, ρ₂ C₂ *
        (if ∃ l₁ l₂, zipSeq (C₁ l₁) (C₂ l₂) ∈ robustTypicalSet J n ε then (1 : ℝ) else 0) ≤
      L₁ * L₂ * exp (-(n * btPackExp J ε)) := by
  set R := robustTypicalSet J n ε
  set e := exp (-(n * btPackExp J ε)) with he
  have he0 : 0 ≤ e := (exp_pos _).le
  have hnn : ∀ p : Prop, ∀ [Decidable p], (0 : ℝ) ≤ if p then 1 else 0 := fun p _ => by
    split_ifs <;> norm_num
  -- The union bound.
  have hunion : ∀ (C₁ : Fin L₁ → Fin n → a) (C₂ : Fin L₂ → Fin n → b),
      (if ∃ l₁ l₂, zipSeq (C₁ l₁) (C₂ l₂) ∈ R then (1 : ℝ) else 0) ≤
      ∑ l₁, ∑ l₂, if zipSeq (C₁ l₁) (C₂ l₂) ∈ R then 1 else 0 := fun C₁ C₂ => by
    split_ifs with h
    · obtain ⟨l₁, l₂, hm⟩ := h
      have h3 := single_le_sum (f := fun l₂ => if zipSeq (C₁ l₁) (C₂ l₂) ∈ R then (1 : ℝ) else 0)
        (fun _ _ => hnn _) (mem_univ l₂)
      have h4 := single_le_sum (f := fun l₁ => ∑ l₂,
        if zipSeq (C₁ l₁) (C₂ l₂) ∈ R then (1 : ℝ) else 0)
        (fun _ _ => sum_nonneg fun _ _ => hnn _) (mem_univ l₁)
      simp only [hm, ite_true] at h3
      exact h3.trans h4
    · exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => hnn _
  have hin : ∀ C₁ : Fin L₁ → Fin n → a, ∑ C₂, ρ₂ C₂ *
      (∑ l₁, ∑ l₂, if zipSeq (C₁ l₁) (C₂ l₂) ∈ R then (1 : ℝ) else 0) ≤ L₁ * L₂ * e := fun C₁ => by
    have e1 : ∑ C₂, ρ₂ C₂ * (∑ l₁, ∑ l₂, if zipSeq (C₁ l₁) (C₂ l₂) ∈ R then (1 : ℝ) else 0) =
        ∑ l₁, ∑ l₂, ∑ C₂, ρ₂ C₂ * (if zipSeq (C₁ l₁) (C₂ l₂) ∈ R then (1 : ℝ) else 0) := by
      simp only [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun l₁ _ => ?_
      rw [sum_comm]
    rw [e1]
    calc _ ≤ ∑ _l₁ : Fin L₁, ∑ _l₂ : Fin L₂, e := by
          refine sum_le_sum fun l₁ _ => sum_le_sum fun l₂ _ => ?_
          rw [h₂ l₂ fun v => if zipSeq (C₁ l₁) v ∈ R then (1 : ℝ) else 0]
          exact le_trans (le_of_eq (sum_congr rfl fun v _ => by congr))
            (sum_iidPMF_snd_typical_le hJ hε (C₁ l₁))
      _ = _ := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc _ ≤ ∑ C₁, ρ₁ C₁ * (L₁ * L₂ * e) := sum_le_sum fun C₁ _ =>
        mul_le_mul_of_nonneg_left ((sum_le_sum fun C₂ _ => mul_le_mul_of_nonneg_left
          (hunion C₁ C₂) (hρ₂.nonneg C₂)).trans (hin C₁)) (hρ₁.nonneg C₁)
    _ = _ := by rw [← sum_mul, hρ₁.sum_eq_one, one_mul]

end Packing

/-! ### The marginals of the law -/

section Marginals

omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] in
/-- The law of `(g(A), C)` for `A ∼ Q` and `C` from the channel `κ` with input `g(A)`. -/
lemma dist_jointOf_map {A B C : Type*} [Fintype A] [Fintype C] {Q : A → ℝ} (g : A → B)
    (κ : B → C → ℝ) :
    dist (jointOf Q fun a => κ (g a)) (fun z => (g z.1, z.2)) = jointOf (dist Q g) κ := by
  classical
  funext ⟨b, u⟩
  simp only [dist, jointOf, Prod.mk.injEq]
  rw [Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single u]
  · by_cases h : g a = b <;> simp [h]
  · intro c _ hc
    simp [hc]
  · simp

/-- The law of `X₂` under the law of `((X₁, U₁), X₂)`. -/
lemma dist_btQ₃_snd (h₁ : IsChannel κ₁) : dist (btQ₃ P κ₁) Prod.snd = margSnd P := by
  funext x₂
  rw [dist_snd, show margSnd P x₂ = ∑ x₁, P (x₁, x₂) from dist_snd P x₂, Fintype.sum_prod_type]
  refine sum_congr rfl fun x₁ _ => ?_
  simp only [btQ₃]
  rw [← mul_sum, (h₁ x₁).sum_eq_one, mul_one]

/-- The law of `(X₂, U₂)` is `p(x₂) p(u₂ | x₂)`. -/
lemma dist_btLaw_X₂U₂ (h₁ : IsChannel κ₁) :
    dist (btLaw P κ₁ κ₂) (fun z => (z.1.2, z.2)) = btJ₂ P κ₂ := by
  have h := dist_jointOf_map (Q := btQ₃ P κ₁) (Prod.snd : (α₁ × υ₁) × α₂ → α₂) κ₂
  rw [dist_btQ₃_snd h₁] at h
  exact h

/-- The law of `(X₁, U₁)`. -/
lemma dist_btLaw_X₁U₁ (h₂ : IsChannel κ₂) :
    dist (btLaw P κ₁ κ₂) (fun z => z.1.1) = btJ₁ P κ₁ := by
  have h := dist_comp_eq (btLaw P κ₁ κ₂) Prod.fst (Prod.fst : (α₁ × υ₁) × α₂ → α₁ × υ₁)
  have e : dist (btLaw P κ₁ κ₂) Prod.fst = btQ₃ P κ₁ := margFst_btLaw h₂
  rw [e] at h
  exact h.trans margFst_btQ₃

lemma margFst_btUU (h₂ : IsChannel κ₂) : margFst (btUU P κ₁ κ₂) = margSnd (btJ₁ P κ₁) := by
  have h := dist_comp_eq (btLaw P κ₁ κ₂) (fun z => z.1.1) (Prod.snd : α₁ × υ₁ → υ₁)
  rw [dist_btLaw_X₁U₁ h₂] at h
  rw [show margSnd (btJ₁ P κ₁) = dist (btJ₁ P κ₁) Prod.snd from rfl, ← h]
  exact (dist_comp_eq (btLaw P κ₁ κ₂) (fun z => (z.1.1.2, z.2)) Prod.fst).symm

lemma margSnd_btUU (h₁ : IsChannel κ₁) : margSnd (btUU P κ₁ κ₂) = margSnd (btJ₂ P κ₂) := by
  have h := dist_comp_eq (btLaw P κ₁ κ₂) (fun z => (z.1.2, z.2)) (Prod.snd : α₂ × υ₂ → υ₂)
  rw [dist_btLaw_X₂U₂ h₁] at h
  rw [show margSnd (btJ₂ P κ₂) = dist (btJ₂ P κ₂) Prod.snd from rfl, ← h]
  exact (dist_comp_eq (btLaw P κ₁ κ₂) (fun z => (z.1.1.2, z.2)) Prod.snd).symm

end Marginals

/-! ### The decoder -/

section Decoder

variable {n L₁ L₂ M₁ M₂ : ℕ}

open Classical in
/-- **Lecture 13 of [elgamal2010], page 13-10.** The decoder: an index pair of the two bins whose
codewords are jointly typical, and `l₀` if there is none. -/
def btIndex (B₁ : Fin L₁ → Fin M₁) (B₂ : Fin L₂ → Fin M₂) (R : Finset (Fin n → υ₁ × υ₂))
    (C₁ : Fin L₁ → Fin n → υ₁) (C₂ : Fin L₂ → Fin n → υ₂) (l₀ : Fin L₁ × Fin L₂)
    (m : Fin M₁ × Fin M₂) : Fin L₁ × Fin L₂ :=
  if h : ∃ l : Fin L₁ × Fin L₂, B₁ l.1 = m.1 ∧ B₂ l.2 = m.2 ∧ zipSeq (C₁ l.1) (C₂ l.2) ∈ R then
    h.choose else l₀

open Classical in
omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] in
/-- **Lecture 13, page 13-10.** The decoder recovers the indices `(l₁, l₂)` unless their codewords
are
not typical with the sources, or another pair of the bins is jointly typical (the event `E₄`). -/
theorem btIndex_not_mem_le {B₁ : Fin L₁ → Fin M₁} {B₂ : Fin L₂ → Fin M₂}
    {R : Finset (Fin n → υ₁ × υ₂)} {C₁ : Fin L₁ → Fin n → υ₁} {C₂ : Fin L₂ → Fin n → υ₂}
    (l₀ : Fin L₁ × Fin L₂) (l₁ : Fin L₁) (l₂ : Fin L₂)
    {T : Finset (Fin n → ((α₁ × υ₁) × α₂) × υ₂)}
    (hT : ∀ (ω : Fin n → α₁ × α₂) (u₁ : Fin n → υ₁) (u₂ : Fin n → υ₂), btSeq ω u₁ u₂ ∈ T →
      zipSeq u₁ u₂ ∈ R) (ω : Fin n → α₁ × α₂) :
    (if btSeq ω (C₁ (btIndex B₁ B₂ R C₁ C₂ l₀ (B₁ l₁, B₂ l₂)).1)
        (C₂ (btIndex B₁ B₂ R C₁ C₂ l₀ (B₁ l₁, B₂ l₂)).2) ∈ T then (0 : ℝ) else 1) ≤
      (if btSeq ω (C₁ l₁) (C₂ l₂) ∈ T then 0 else 1) +
      ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) *
        (if zipSeq (C₁ a) (C₂ l₂) ∈ R then 1 else 0) +
      ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) *
        (if zipSeq (C₁ l₁) (C₂ b) ∈ R then 1 else 0) +
      ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) *
        ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) *
          (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0) := by
  set X₁ : ℝ := ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) *
    (if zipSeq (C₁ a) (C₂ l₂) ∈ R then 1 else 0) with hX₁
  set X₂ : ℝ := ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) *
    (if zipSeq (C₁ l₁) (C₂ b) ∈ R then 1 else 0) with hX₂
  set X₃ : ℝ := ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) *
    ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) *
      (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0) with hX₃
  have hnn : ∀ p : Prop, ∀ [Decidable p], (0 : ℝ) ≤ if p then 1 else 0 := fun p _ => by
    split_ifs <;> norm_num
  have hX₁0 : 0 ≤ X₁ := sum_nonneg fun a _ => mul_nonneg (hnn _) (hnn _)
  have hX₂0 : 0 ≤ X₂ := sum_nonneg fun a _ => mul_nonneg (hnn _) (hnn _)
  have hX₃0 : 0 ≤ X₃ := sum_nonneg fun a _ => mul_nonneg (hnn _)
    (sum_nonneg fun b _ => mul_nonneg (hnn _) (hnn _))
  have hle1 : (if btSeq ω (C₁ (btIndex B₁ B₂ R C₁ C₂ l₀ (B₁ l₁, B₂ l₂)).1)
      (C₂ (btIndex B₁ B₂ R C₁ C₂ l₀ (B₁ l₁, B₂ l₂)).2) ∈ T then (0 : ℝ) else 1) ≤ 1 := by
    split_ifs <;> norm_num
  have hle0 : (0 : ℝ) ≤ if btSeq ω (C₁ l₁) (C₂ l₂) ∈ T then 0 else 1 := by
    split_ifs <;> norm_num
  by_cases hL : btSeq ω (C₁ l₁) (C₂ l₂) ∈ T
  · have hin := hT _ _ _ hL
    by_cases hu : ∀ l : Fin L₁ × Fin L₂, B₁ l.1 = B₁ l₁ → B₂ l.2 = B₂ l₂ →
        zipSeq (C₁ l.1) (C₂ l.2) ∈ R → l = (l₁, l₂)
    · have hex : ∃ l : Fin L₁ × Fin L₂, B₁ l.1 = B₁ l₁ ∧ B₂ l.2 = B₂ l₂ ∧
          zipSeq (C₁ l.1) (C₂ l.2) ∈ R := ⟨(l₁, l₂), rfl, rfl, hin⟩
      have hd : btIndex B₁ B₂ R C₁ C₂ l₀ (B₁ l₁, B₂ l₂) = (l₁, l₂) := by
        simp only [btIndex, hex, ↓reduceDIte]
        exact hu _ hex.choose_spec.1 hex.choose_spec.2.1 hex.choose_spec.2.2
      rw [hd]
      simp only [hL, ite_true, zero_add]
      linarith
    · push Not at hu
      obtain ⟨⟨a, b⟩, h₁', h₂', hR, hne⟩ := hu
      simp only at h₁' h₂' hR
      have hle : (1 : ℝ) ≤ X₁ + X₂ + X₃ := by
        by_cases ha : a = l₁
        · subst ha
          have hb : b ≠ l₂ := fun h => hne (by rw [h])
          have := single_le_sum (s := univ.erase l₂) (f := fun b =>
            (if B₂ b = B₂ l₂ then (1 : ℝ) else 0) *
              (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0))
            (fun _ _ => mul_nonneg (hnn _) (hnn _)) (mem_erase.2 ⟨hb, mem_univ b⟩)
          simp only [h₂', hR, ite_true, mul_one] at this
          linarith
        · by_cases hb : b = l₂
          · subst hb
            have := single_le_sum (s := univ.erase l₁) (f := fun a =>
              (if B₁ a = B₁ l₁ then (1 : ℝ) else 0) *
                (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0))
              (fun _ _ => mul_nonneg (hnn _) (hnn _)) (mem_erase.2 ⟨ha, mem_univ a⟩)
            simp only [h₁', hR, ite_true, mul_one] at this
            linarith
          · have hin2 := single_le_sum (s := univ.erase l₂) (f := fun b =>
              (if B₂ b = B₂ l₂ then (1 : ℝ) else 0) *
                (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0))
              (fun _ _ => mul_nonneg (hnn _) (hnn _)) (mem_erase.2 ⟨hb, mem_univ b⟩)
            simp only [h₂', hR, ite_true, mul_one] at hin2
            have := single_le_sum (s := univ.erase l₁) (f := fun a =>
              (if B₁ a = B₁ l₁ then (1 : ℝ) else 0) *
                ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) *
                  (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0))
              (fun a _ => mul_nonneg (hnn _) (sum_nonneg fun b _ => mul_nonneg (hnn _) (hnn _)))
              (mem_erase.2 ⟨ha, mem_univ a⟩)
            simp only [h₁', ite_true, one_mul] at this
            linarith
      linarith
  · simp only [hL, ite_false]
    linarith

/-- **Lecture 13, page 13-12.** Over random bins, the event `E₄` has a probability of at most
`N₁ / M₁ + N₂ / M₂ + N₃ / (M₁ M₂)`, with the numbers of jointly typical pairs. -/
theorem sum_bins_bt_le (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (l₁ : Fin L₁) (l₂ : Fin L₂)
    {Z₁ : Fin L₁ → ℝ} {Z₂ : Fin L₂ → ℝ} {Z₃ : Fin L₁ → Fin L₂ → ℝ} (h₁ : ∀ a, 0 ≤ Z₁ a)
    (h₂ : ∀ b, 0 ≤ Z₂ b) (h₃ : ∀ a b, 0 ≤ Z₃ a b) :
    ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ *
      ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ *
        (∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * Z₁ a +
          ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) * Z₂ b +
          ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) *
            ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) * Z₃ a b) ≤
      (∑ a, Z₁ a) / M₁ + (∑ b, Z₂ b) / M₂ + (∑ a, ∑ b, Z₃ a b) / (M₁ * M₂) := by
  have hne₁ : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have hne₂ : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  have hl₁ := iidPMF_isPMF (uniformPMF_isPMF (α := Fin M₁)) L₁
  have hl₂ := iidPMF_isPMF (uniformPMF_isPMF (α := Fin M₂)) L₂
  have hM₂' : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hM₁' : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  set law₁ := iidPMF (uniformPMF (Fin M₁)) L₁
  set law₂ := iidPMF (uniformPMF (Fin M₂)) L₂
  -- For a fixed first binning.
  have hin : ∀ B₁ : Fin L₁ → Fin M₁, ∑ B₂ : Fin L₂ → Fin M₂, law₂ B₂ *
      (∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * Z₁ a +
        ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) * Z₂ b +
        ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) *
          ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) * Z₃ a b) ≤
      ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * Z₁ a + (∑ b, Z₂ b) / M₂ +
        ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * ((∑ b, Z₃ a b) / M₂) := fun B₁ => by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hl₂.sum_eq_one, one_mul]
    refine add_le_add (add_le_add le_rfl (sum_bins_erase_le hM₂ l₂ h₂)) ?_
    have e : ∑ B₂ : Fin L₂ → Fin M₂, law₂ B₂ * ∑ a ∈ univ.erase l₁,
        (if B₁ a = B₁ l₁ then 1 else 0) *
          ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) * Z₃ a b =
        ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) *
          ∑ B₂ : Fin L₂ → Fin M₂, law₂ B₂ *
            ∑ b ∈ univ.erase l₂, (if B₂ b = B₂ l₂ then 1 else 0) * Z₃ a b := by
      simp only [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun a _ => sum_congr rfl fun B₂ _ => sum_congr rfl fun b _ => ?_
      ring
    rw [e]
    refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
      (sum_bins_erase_le hM₂ l₂ (h₃ a)) (by split_ifs <;> norm_num)
  calc _ ≤ ∑ B₁ : Fin L₁ → Fin M₁, law₁ B₁ *
        (∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * Z₁ a + (∑ b, Z₂ b) / M₂ +
          ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * ((∑ b, Z₃ a b) / M₂)) :=
        sum_le_sum fun B₁ _ => mul_le_mul_of_nonneg_left (hin B₁) (hl₁.nonneg B₁)
    _ = ∑ B₁ : Fin L₁ → Fin M₁, law₁ B₁ *
          ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * Z₁ a + (∑ b, Z₂ b) / M₂ +
        ∑ B₁ : Fin L₁ → Fin M₁, law₁ B₁ *
          ∑ a ∈ univ.erase l₁, (if B₁ a = B₁ l₁ then 1 else 0) * ((∑ b, Z₃ a b) / M₂) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hl₁.sum_eq_one, one_mul]
    _ ≤ _ := by
        have h4 := sum_bins_erase_le hM₁ l₁ h₁
        have h5 := sum_bins_erase_le hM₁ l₁ (Z := fun a => (∑ b, Z₃ a b) / M₂)
          fun a => div_nonneg (sum_nonneg fun b _ => h₃ a b) hM₂'.le
        have e : (∑ a, (∑ b, Z₃ a b) / M₂) / M₁ = (∑ a, ∑ b, Z₃ a b) / (M₁ * M₂) := by
          rw [← sum_div, div_div, mul_comm]
        rw [e] at h5
        linarith

omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] in
/-- Two averages commute. -/
lemma sum_mul_sum_swap {A B : Type*} [Fintype A] [Fintype B] (f : A → ℝ) (g : B → ℝ)
    (X : A → B → ℝ) : ∑ a, f a * ∑ b, g b * X a b = ∑ b, g b * ∑ a, f a * X a b := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring

omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] in
/-- `E ∑ₐ Φ(C a) = L E Φ(U)` for a random codebook. -/
lemma sum_codebook_count_le {X : Type*} [Fintype X] {r : X → ℝ} (hr : IsPMF r) (L : ℕ)
    {Φ : X → ℝ} {b : ℝ} (h : ∑ z, r z * Φ z ≤ b) :
    ∑ C : Fin L → X, iidPMF r L C * ∑ a, Φ (C a) ≤ L * b := by
  have e : ∑ C : Fin L → X, iidPMF r L C * ∑ a, Φ (C a) = ∑ _a : Fin L, ∑ z, r z * Φ z := by
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_iidPMF_eval hr a Φ
  rw [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg L)

open Classical in
/-- **Lecture 13, pages 13-10 to 13-13.** The bound on the probability of error of Berger–Tung
coding:
for any numbers of codewords and bins, there are a code and a typicality decoder with
`(X₁ⁿ, U₁ⁿ, X₂ⁿ, U₂ⁿ)` typical except with probability at most
`btCoverBound + (L₁ / M₁ + L₂ / M₂ + L₁ L₂ / (M₁ M₂)) e^{-n (I(U₁; U₂) - δ(ε))}`. -/
theorem exists_bt_code_le {ε ε₁ ε₂ ε₃ : ℝ} (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hε₁₂ : ε₂ < ε₁) (hε : ε₁ < ε) (hε0 : 0 ≤ ε) (hε1 : ε - ε₁ ≤ 1) (hε₂ : ε₂ ≤ 1 / 2) (hn : 0 < n)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hlow₁ : ∀ x ∈ robustTypicalSet (margFst P) n ε₃,
      (1 - ε₂) * exp (-(n * coverExp (btJ₁ P κ₁) ε₂)) ≤
        prob (iidPMF (margSnd (btJ₁ P κ₁)) n) (condRobustTypicalSet (btJ₁ P κ₁) ε₂ x))
    (hlow₂ : ∀ x ∈ robustTypicalSet (margSnd P) n ε₃,
      (1 - ε₂) * exp (-(n * coverExp (btJ₂ P κ₂) ε₂)) ≤
        prob (iidPMF (margSnd (btJ₂ P κ₂)) n) (condRobustTypicalSet (btJ₂ P κ₂) ε₂ x)) :
    ∃ (enc₁ : (Fin n → α₁) → Fin M₁) (enc₂ : (Fin n → α₂) → Fin M₂)
      (dec : Fin M₁ × Fin M₂ → (Fin n → υ₁) × (Fin n → υ₂)),
      ∑ ω, iidPMF P n ω * (if btSeq ω (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).1
          (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).2 ∈ robustTypicalSet (btLaw P κ₁ κ₂) n ε
          then 0 else 1) ≤
      btCoverBound P κ₁ κ₂ ε ε₁ ε₂ ε₃ n L₁ L₂ +
        ((L₁ : ℝ) / M₁ + L₂ / M₂ + L₁ * L₂ / (M₁ * M₂)) *
          exp (-(n * btPackExp (btUU P κ₁ κ₂) ε)) := by
  have hJ₁ := btJ₁_isPMF (P := P) hP h₁
  have hJ₂ := btJ₂_isPMF (P := P) hP h₂
  have hU := btUU_isPMF hP h₁ h₂
  have hr₁ := iidPMF_isPMF (hJ₁.dist Prod.snd) n
  have hr₂ := iidPMF_isPMF (hJ₂.dist Prod.snd) n
  have hlaw₁ := iidPMF_isPMF hr₁ L₁
  have hlaw₂ := iidPMF_isPMF hr₂ L₂
  have hμ := iidPMF_isPMF hP n
  have hne₁ : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have hne₂ : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  have hb₁ := iidPMF_isPMF (uniformPMF_isPMF (α := Fin M₁)) L₁
  have hb₂ := iidPMF_isPMF (uniformPMF_isPMF (α := Fin M₂)) L₂
  have hM₁' : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂' : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  set r₁ := iidPMF (margSnd (btJ₁ P κ₁)) n with hr₁d
  set r₂ := iidPMF (margSnd (btJ₂ P κ₂)) n with hr₂d
  set T := robustTypicalSet (btLaw P κ₁ κ₂) n ε
  set R := robustTypicalSet (btUU P κ₁ κ₂) n ε
  set l₁ : Fin L₁ := ⟨0, hL₁⟩
  set l₂ : Fin L₂ := ⟨0, hL₂⟩
  set f₁ := fun (C : Fin L₁ → Fin n → υ₁) (x : Fin n → α₁) =>
    firstIn (condRobustTypicalSet (btJ₁ P κ₁) ε₂ x) C l₁ with hf₁
  set f₂ := fun (C : Fin L₂ → Fin n → υ₂) (x : Fin n → α₂) =>
    firstIn (condRobustTypicalSet (btJ₂ P κ₂) ε₂ x) C l₂ with hf₂
  set e₀ := exp (-(n * btPackExp (btUU P κ₁ κ₂) ε)) with he₀
  have hT : ∀ (ω : Fin n → α₁ × α₂) (u₁ : Fin n → υ₁) (u₂ : Fin n → υ₂), btSeq ω u₁ u₂ ∈ T →
      zipSeq u₁ u₂ ∈ R := fun ω u₁ u₂ h =>
    comp_mem_robustTypicalSet h fun z => (z.1.1.2, z.2)
  set base := fun (C₁ : Fin L₁ → Fin n → υ₁) (C₂ : Fin L₂ → Fin n → υ₂) (ω : Fin n → α₁ × α₂) =>
    (if btSeq ω (C₁ (f₁ C₁ (fstSeq ω))) (C₂ (f₂ C₂ (sndSeq ω))) ∈ T then (0 : ℝ) else 1) with hbase
  have hnn : ∀ p : Prop, ∀ [Decidable p], (0 : ℝ) ≤ if p then 1 else 0 := fun p _ => by
    split_ifs <;> norm_num
  -- For fixed codebooks, over the bins.
  have hbins : ∀ (C₁ : Fin L₁ → Fin n → υ₁) (C₂ : Fin L₂ → Fin n → υ₂),
      ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ *
        ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ *
          ∑ ω, iidPMF P n ω * (if btSeq ω
            (C₁ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).1)
            (C₂ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).2) ∈
              T
            then 0 else 1) ≤
      ∑ ω, iidPMF P n ω * (base C₁ C₂ ω +
        (∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then 1 else 0) / M₁ +
        (∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then 1 else 0) / M₂ +
        (∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0) / (M₁ * M₂)) := fun C₁ C₂ => by
    have hswap : ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ *
        ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ *
          ∑ ω, iidPMF P n ω * (if btSeq ω
            (C₁ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).1)
            (C₂ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).2) ∈
              T
            then (0 : ℝ) else 1) =
        ∑ ω, iidPMF P n ω * ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ *
          ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * (if btSeq ω
            (C₁ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).1)
            (C₂ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).2) ∈
              T
            then (0 : ℝ) else 1) := by
      have e1 : ∀ B₁ : Fin L₁ → Fin M₁, ∑ B₂ : Fin L₂ → Fin M₂,
          iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * ∑ ω, iidPMF P n ω * (if btSeq ω
            (C₁ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).1)
            (C₂ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).2) ∈
              T
            then (0 : ℝ) else 1) =
          ∑ ω, iidPMF P n ω * ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * (if btSeq
            ω
            (C₁ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).1)
            (C₂ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) (B₁ (f₁ C₁ (fstSeq ω)), B₂ (f₂ C₂ (sndSeq ω)))).2) ∈
              T
            then (0 : ℝ) else 1) := fun B₁ => by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun ω _ => sum_congr rfl fun B₂ _ => by ring
      simp only [e1]
      exact sum_mul_sum_swap _ _ _
    rw [hswap]
    refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hμ.nonneg ω)
    set a₁ := f₁ C₁ (fstSeq ω)
    set a₂ := f₂ C₂ (sndSeq ω)
    have hpt := fun (B₁ : Fin L₁ → Fin M₁) (B₂ : Fin L₂ → Fin M₂) =>
      btIndex_not_mem_le (B₁ := B₁) (B₂ := B₂) (R := R) (C₁ := C₁) (C₂ := C₂) (l₁, l₂) a₁ a₂ hT ω
    have hZ := sum_bins_bt_le (L₁ := L₁) (L₂ := L₂) hM₁ hM₂ a₁ a₂
      (Z₁ := fun a => if zipSeq (C₁ a) (C₂ a₂) ∈ R then 1 else 0)
      (Z₂ := fun b => if zipSeq (C₁ a₁) (C₂ b) ∈ R then 1 else 0)
      (Z₃ := fun a b => if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0)
      (fun _ => hnn _) (fun _ => hnn _) (fun _ _ => hnn _)
    calc _ ≤ ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ *
          ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * (base C₁ C₂ ω +
            (∑ a ∈ univ.erase a₁, (if B₁ a = B₁ a₁ then 1 else 0) *
                (if zipSeq (C₁ a) (C₂ a₂) ∈ R then 1 else 0) +
              ∑ b ∈ univ.erase a₂, (if B₂ b = B₂ a₂ then 1 else 0) *
                (if zipSeq (C₁ a₁) (C₂ b) ∈ R then 1 else 0) +
              ∑ a ∈ univ.erase a₁, (if B₁ a = B₁ a₁ then 1 else 0) *
                ∑ b ∈ univ.erase a₂, (if B₂ b = B₂ a₂ then 1 else 0) *
                  (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0))) := by
          refine sum_le_sum fun B₁ _ => mul_le_mul_of_nonneg_left
            (sum_le_sum fun B₂ _ => mul_le_mul_of_nonneg_left ?_ (hb₂.nonneg B₂)) (hb₁.nonneg B₁)
          have := hpt B₁ B₂
          simp only [hbase]
          linarith
      _ = base C₁ C₂ ω + ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ *
          ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ *
            (∑ a ∈ univ.erase a₁, (if B₁ a = B₁ a₁ then 1 else 0) *
                (if zipSeq (C₁ a) (C₂ a₂) ∈ R then 1 else 0) +
              ∑ b ∈ univ.erase a₂, (if B₂ b = B₂ a₂ then 1 else 0) *
                (if zipSeq (C₁ a₁) (C₂ b) ∈ R then 1 else 0) +
              ∑ a ∈ univ.erase a₁, (if B₁ a = B₁ a₁ then 1 else 0) *
                ∑ b ∈ univ.erase a₂, (if B₂ b = B₂ a₂ then 1 else 0) *
                  (if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0)) := by
          have e2 : ∀ (B₁ : Fin L₁ → Fin M₁) (X : (Fin L₂ → Fin M₂) → ℝ),
              ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * (base C₁ C₂ ω + X B₂) =
              base C₁ C₂ ω + ∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * X B₂ :=
            fun _ X => by
              rw [show (∑ B₂ : Fin L₂ → Fin M₂, iidPMF (uniformPMF (Fin M₂)) L₂ B₂ *
                  (base C₁ C₂ ω + X B₂)) =
                  ∑ B₂ : Fin L₂ → Fin M₂, (iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * base C₁ C₂ ω +
                    iidPMF (uniformPMF (Fin M₂)) L₂ B₂ * X B₂) from
                  sum_congr rfl fun B₂ _ => mul_add _ _ _, sum_add_distrib, ← sum_mul,
                hb₂.sum_eq_one, one_mul]
          have e3 : ∀ X : (Fin L₁ → Fin M₁) → ℝ,
              ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ * (base C₁ C₂ ω + X B₁) =
              base C₁ C₂ ω + ∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ * X B₁ :=
            fun X => by
              rw [show (∑ B₁ : Fin L₁ → Fin M₁, iidPMF (uniformPMF (Fin M₁)) L₁ B₁ *
                  (base C₁ C₂ ω + X B₁)) =
                  ∑ B₁ : Fin L₁ → Fin M₁, (iidPMF (uniformPMF (Fin M₁)) L₁ B₁ * base C₁ C₂ ω +
                    iidPMF (uniformPMF (Fin M₁)) L₁ B₁ * X B₁) from
                  sum_congr rfl fun B₁ _ => mul_add _ _ _, sum_add_distrib, ← sum_mul,
                hb₁.sum_eq_one, one_mul]
          refine (sum_congr rfl fun B₁ _ => ?_).trans (e3 _)
          exact congrArg (fun t => iidPMF (uniformPMF (Fin M₁)) L₁ B₁ * t) (e2 B₁ _)
      _ ≤ _ := by
          simp only [add_assoc] at hZ ⊢
          linarith
  -- Over the codebooks.
  have hcover := sum_two_codebooks_le (ε := ε) (ε₁ := ε₁) (ε₃ := ε₃) hP h₁ h₂ hε₁₂ hε hε1 hε₂ hn
    l₁ l₂ hlow₁ hlow₂
  have hpack₁ : ∀ u₂, ∑ u₁, r₁ u₁ * (if zipSeq u₁ u₂ ∈ R then (1 : ℝ) else 0) ≤ e₀ := fun u₂ => by
    have h := sum_iidPMF_fst_typical_le hU (ε := ε) hε0 u₂
    rw [margFst_btUU h₂] at h
    refine le_trans (le_of_eq (sum_congr rfl fun u _ => by congr)) h
  have hpack₂ : ∀ u₁, ∑ u₂, r₂ u₂ * (if zipSeq u₁ u₂ ∈ R then (1 : ℝ) else 0) ≤ e₀ := fun u₁ => by
    have h := sum_iidPMF_snd_typical_le hU (ε := ε) hε0 u₁
    rw [margSnd_btUU h₁] at h
    refine le_trans (le_of_eq (sum_congr rfl fun u _ => by congr)) h
  have hN₁ : ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
      ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω *
        ((∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then (1 : ℝ) else 0) / M₁) ≤
      L₁ / M₁ * e₀ := by
    rw [sum_mul_sum_swap]
    calc _ = ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω *
          (∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
            ((∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then (1 : ℝ) else 0) / M₁)) := by
          refine sum_congr rfl fun C₂ _ => ?_
          rw [mul_eq_mul_left_iff]
          left
          exact sum_mul_sum_swap _ _ _
      _ ≤ ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω * (L₁ / M₁ * e₀) := by
          refine sum_le_sum fun C₂ _ => mul_le_mul_of_nonneg_left (sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left ?_ (hμ.nonneg ω)) (hlaw₂.nonneg C₂)
          have h := sum_codebook_count_le hr₁ L₁ (hpack₁ (C₂ (f₂ C₂ (sndSeq ω))))
          have e : ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
              ((∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then (1 : ℝ) else 0) / M₁) =
              (∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
                ∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then (1 : ℝ) else 0) / M₁ := by
            rw [sum_div]
            exact sum_congr rfl fun C₁ _ => by ring
          rw [e, div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right h hM₁'.le
      _ = _ := by
          simp only [← sum_mul, hμ.sum_eq_one, hlaw₂.sum_eq_one, one_mul]
  have hN₂ : ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
      ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω *
        ((∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then (1 : ℝ) else 0) / M₂) ≤
      L₂ / M₂ * e₀ := by
    calc _ = ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ * ∑ ω, iidPMF P n ω *
          (∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ *
            ((∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then (1 : ℝ) else 0) / M₂)) := by
          refine sum_congr rfl fun C₁ _ => ?_
          rw [mul_eq_mul_left_iff]
          left
          exact sum_mul_sum_swap _ _ _
      _ ≤ ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ * ∑ ω, iidPMF P n ω * (L₂ / M₂ * e₀) := by
          refine sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left (sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left ?_ (hμ.nonneg ω)) (hlaw₁.nonneg C₁)
          have h := sum_codebook_count_le hr₂ L₂ (hpack₂ (C₁ (f₁ C₁ (fstSeq ω))))
          have e : ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ *
              ((∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then (1 : ℝ) else 0) / M₂) =
              (∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ *
                ∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then (1 : ℝ) else 0) / M₂ := by
            rw [sum_div]
            exact sum_congr rfl fun C₂ _ => by ring
          rw [e, div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right h hM₂'.le
      _ = _ := by
          simp only [← sum_mul, hμ.sum_eq_one, hlaw₁.sum_eq_one, one_mul]
  have hN₃ : ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
      ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω *
        ((∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂)) ≤
      L₁ * L₂ / (M₁ * M₂) * e₀ := by
    have hin : ∀ C₁ : Fin L₁ → Fin n → υ₁, ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ *
        ∑ ω, iidPMF P n ω *
          ((∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂)) ≤
        L₁ * L₂ / (M₁ * M₂) * e₀ := fun C₁ => by
      have e : ∀ C₂ : Fin L₂ → Fin n → υ₂, ∑ ω, iidPMF P n ω *
          ((∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂)) =
          (∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂) := fun C₂ => by
        rw [← sum_mul, hμ.sum_eq_one, one_mul]
      simp only [e]
      have e2 : ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ *
          ((∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂)) =
          (∑ a, ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ *
            ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂) := by
        calc _ = (∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ *
              ∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂) := by
              rw [sum_div]
              exact sum_congr rfl fun C₂ _ => by ring
          _ = _ := by
              congr 1
              simp only [mul_sum]
              rw [sum_comm]
      rw [e2, div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc _ ≤ ∑ _a : Fin L₁, (L₂ * e₀ : ℝ) := sum_le_sum fun a _ =>
            sum_codebook_count_le hr₂ L₂ (hpack₂ (C₁ a))
        _ = _ := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc _ ≤ ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ * (L₁ * L₂ / (M₁ * M₂) * e₀) :=
          sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left (hin C₁) (hlaw₁.nonneg C₁)
      _ = _ := by rw [← sum_mul, hlaw₁.sum_eq_one, one_mul]
  -- The average of the total.
  have htotal : ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
      ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω * (base C₁ C₂ ω +
        (∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then 1 else 0) / M₁ +
        (∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then 1 else 0) / M₂ +
        (∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0) / (M₁ * M₂)) ≤
      btCoverBound P κ₁ κ₂ ε ε₁ ε₂ ε₃ n L₁ L₂ +
        ((L₁ : ℝ) / M₁ + L₂ / M₂ + L₁ * L₂ / (M₁ * M₂)) * e₀ := by
    have e : ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
        ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω * (base C₁ C₂ ω +
          (∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then 1 else 0) / M₁ +
          (∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then 1 else 0) / M₂ +
          (∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then 1 else 0) / (M₁ * M₂)) =
        ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
          ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω * base C₁ C₂ ω +
        ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
          ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω *
            ((∑ a, if zipSeq (C₁ a) (C₂ (f₂ C₂ (sndSeq ω))) ∈ R then (1 : ℝ) else 0) / M₁) +
        ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
          ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω *
            ((∑ b, if zipSeq (C₁ (f₁ C₁ (fstSeq ω))) (C₂ b) ∈ R then (1 : ℝ) else 0) / M₂) +
        ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
          ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω *
            ((∑ a, ∑ b, if zipSeq (C₁ a) (C₂ b) ∈ R then (1 : ℝ) else 0) / (M₁ * M₂)) := by
      simp only [mul_add, sum_add_distrib]
    rw [e]
    have hc : ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF r₁ L₁ C₁ *
        ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF r₂ L₂ C₂ * ∑ ω, iidPMF P n ω * base C₁ C₂ ω ≤
        btCoverBound P κ₁ κ₂ ε ε₁ ε₂ ε₃ n L₁ L₂ := hcover
    have hd : ((L₁ : ℝ) / M₁ + L₂ / M₂ + L₁ * L₂ / (M₁ * M₂)) * e₀ =
        L₁ / M₁ * e₀ + L₂ / M₂ * e₀ + L₁ * L₂ / (M₁ * M₂) * e₀ := by ring
    rw [hd]
    linarith
  obtain ⟨C₁, hC₁⟩ := exists_le_of_sum_mul_le hlaw₁ htotal
  obtain ⟨C₂, hC₂⟩ := exists_le_of_sum_mul_le hlaw₂ hC₁
  obtain ⟨B₁, hB₁⟩ := exists_le_of_sum_mul_le hb₁ ((hbins C₁ C₂).trans hC₂)
  obtain ⟨B₂, hB₂⟩ := exists_le_of_sum_mul_le hb₂ hB₁
  exact ⟨fun x => B₁ (f₁ C₁ x), fun x => B₂ (f₂ C₂ x), fun m =>
    (C₁ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) m).1, C₂ (btIndex B₁ B₂ R C₁ C₂ (l₁, l₂) m).2), hB₂⟩

end Decoder

end InfoTheory
