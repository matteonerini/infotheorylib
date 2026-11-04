/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Cost
public import InfoTheoryLib.ChannelCoding.Product
public import InfoTheoryLib.Network.ICBounds

/-!
# The interference channel with strong interference: the converse

A DM-IC has strong interference if `I(X₁; Y₁ | X₂) ≤ I(X₁; Y₂ | X₂)` and
`I(X₂; Y₂ | X₁) ≤ I(X₂; Y₁ | X₁)` for all `p(x₁) p(x₂)`. Lemma 1 of Lecture 6 of El Gamal and Kim
extends the condition to `n` uses of the channel. Given `X₂ⁿ = x₂ⁿ`, this is the statement that a
product of more capable channels is more capable. We prove it by replacing the outputs one at a
time: with `U` the other outputs, `U → Xₖ → (Y₁ₖ, Y₂ₖ)`, so that the single-letter condition
gives `I(Xₖ; Y₁ₖ | U) ≤ I(Xₖ; Y₂ₖ | U)`.

## Main definitions

* `sideOut T U`: the channel with the two conditionally independent outputs of `T` and `U`.
* `indexedExt V`: the memoryless channel `∏ₖ Vₖ(yₖ | xₖ)` with channels depending on the time.
* `IsStrongIC W`, `IsVeryStrongIC W`: strong and very strong interference.
* `icStrongRegionBits W`: the region of Theorem 1 of Lecture 6.

## Main statements

* `mutualInfoOf_sideOut`: the information from a side output and a channel output, as an average
  over the side output.
* `mutualInfoOf_indexedExt_le`: a product of more capable channels is more capable.
* `IsStrongIC.macInfo₁_macExt_le`, `IsStrongIC.macInfo₂_macExt_le`: **Lemma 1 of [elgamal2010],
  Lecture 6**.
* `IsVeryStrongIC.isStrongIC`: very strong interference implies strong interference.
* `IsAchievableICBits.mem_closure_icStrongRegionBits`: **Theorem 1 of [elgamal2010], Lecture 6
  (converse)**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 6
-/

open Real Finset Filter Topology Set

@[expose] public noncomputable section

namespace InfoTheory

universe uΞ uα v₁ v₂

/-! ### A side output -/

section Side

variable {Ξ α γ β : Type*} [Fintype Ξ] [Fintype α] [Fintype γ] [Fintype β]

/-- The channel with two conditionally independent outputs, of `T` and of `U`. -/
def sideOut (T : Ξ → γ → ℝ) (U : Ξ → β → ℝ) : Ξ → γ × β → ℝ := fun ξ z => T ξ z.1 * U ξ z.2

omit [Fintype Ξ] in
lemma sideOut_isChannel {T : Ξ → γ → ℝ} {U : Ξ → β → ℝ} (hT : IsChannel T) (hU : IsChannel U) :
    IsChannel (sideOut T U) := fun ξ => (hT ξ).prodDist (hU ξ)

/-- `H(G, Y) = H(G) + H(Y | G)` for the law `a(g) b(y | g)`. -/
lemma entropy_jointOf {a : γ → ℝ} {b : γ → β → ℝ} (ha : IsPMF a) (hb : IsChannel b) :
    entropy (jointOf a b) = entropy a + ∑ g, a g * entropy (b g) := by
  have hμ := jointOf_isPMF ha hb
  have h := chain_rule hμ (Prod.fst : γ × β → γ) Prod.snd
  rw [condEntropy_jointOf ha hb, entropyRV, dist_pair_fst_snd, entropyRV, dist_jointOf_fst hb] at h
  exact h

omit [Fintype β] in
open Classical in
/-- The law of `x(Ξ)` given the side output `G = g`. If `g` has probability `0`, it is the law of
`x(Ξ)`, so that it is a pmf for every `g`. -/
def sideCond (P : Ξ → ℝ) (T : Ξ → γ → ℝ) (x : Ξ → α) (g : γ) (a : α) : ℝ :=
  if outDist P T g = 0 then dist P x a else
    (∑ ξ, if x ξ = a then P ξ * T ξ g else 0) / outDist P T g

variable {P : Ξ → ℝ} {T : Ξ → γ → ℝ} {x : Ξ → α}

omit [Fintype α] [Fintype β] in
open Classical in
/-- `p(g) p(a | g) = ∑_{ξ : x(ξ) = a} p(ξ) p(g | ξ)`. -/
lemma mul_sideCond (hP : IsPMF P) (hT : IsChannel T) (g : γ) (a : α) :
    outDist P T g * sideCond P T x g a = ∑ ξ, if x ξ = a then P ξ * T ξ g else 0 := by
  by_cases h : outDist P T g = 0
  · have h0 : ∀ ξ, P ξ * T ξ g = 0 := fun ξ =>
      (sum_eq_zero_iff_of_nonneg fun ξ _ => mul_nonneg (hP.nonneg ξ) ((hT ξ).nonneg g)).1 h ξ
        (mem_univ ξ)
    simp [h, h0]
  · simp only [sideCond, h, ite_false]
    field_simp

omit [Fintype β] in
lemma sideCond_isPMF (hP : IsPMF P) (hT : IsChannel T) (g : γ) : IsPMF (sideCond P T x g) := by
  classical
  by_cases h : outDist P T g = 0
  · have : sideCond P T x g = dist P x := by
      funext a
      simp [sideCond, h]
    rw [this]
    exact hP.dist x
  · have hpos : 0 < outDist P T g := lt_of_le_of_ne
      (sum_nonneg fun ξ _ => mul_nonneg (hP.nonneg ξ) ((hT ξ).nonneg g)) (Ne.symm h)
    refine ⟨fun a => ?_, ?_⟩
    · simp only [sideCond, h, ite_false]
      refine div_nonneg (sum_nonneg fun ξ _ => ?_) hpos.le
      split_ifs
      · exact mul_nonneg (hP.nonneg ξ) ((hT ξ).nonneg g)
      · exact le_rfl
    · simp only [sideCond, h, ite_false, ← sum_div]
      rw [div_eq_one_iff_eq h, sum_comm]
      refine sum_congr rfl fun ξ _ => ?_
      rw [sum_ite_eq]
      simp

/-- **Lecture 6 of [elgamal2010], page 6-14.** With a side output `G` and a channel `V` from
`x(Ξ)`, `I(Ξ; G, Y) = I(Ξ; G) + ∑_g p(g) I(X; Y | G = g)`, with `U → X → Y` given `G = g`: the
conditional law of `Y` given `X = a` and `G = g` is `V a`. -/
theorem mutualInfoOf_sideOut (hP : IsPMF P) (hT : IsChannel T) {V : α → β → ℝ}
    (hV : IsChannel V) :
    mutualInfoOf P (sideOut T fun ξ => V (x ξ)) =
      (entropy (outDist P T) - ∑ ξ, P ξ * entropy (T ξ)) +
        ∑ g, outDist P T g * mutualInfoOf (sideCond P T x g) V := by
  classical
  have hW : IsChannel (sideOut T fun ξ => V (x ξ)) := sideOut_isChannel hT fun ξ => hV (x ξ)
  have hpG : IsPMF (outDist P T) := outDist_isPMF hP hT
  have hout : IsChannel fun g => outDist (sideCond P T x g) V := fun g =>
    outDist_isPMF (sideCond_isPMF hP hT g) hV
  -- The law of the outputs.
  have e₁ : outDist P (sideOut T fun ξ => V (x ξ)) =
      jointOf (outDist P T) fun g => outDist (sideCond P T x g) V := by
    funext ⟨g, y⟩
    simp only [jointOf, outDist, sideOut, mul_sum, ← mul_assoc]
    have : ∀ a, (∑ ξ, P ξ * T ξ g) * sideCond P T x g a * V a y =
        ∑ ξ, if x ξ = a then P ξ * T ξ g * V a y else 0 := fun a => by
      have h := mul_sideCond (x := x) hP hT g a
      simp only [outDist] at h
      rw [h, sum_mul]
      refine sum_congr rfl fun ξ _ => ?_
      split_ifs <;> simp
    simp only [this]
    rw [sum_comm]
    refine sum_congr rfl fun ξ _ => ?_
    rw [sum_ite_eq]
    simp
  -- The noise terms.
  have e₂ : ∑ g, outDist P T g * ∑ a, sideCond P T x g a * entropy (V a) =
      ∑ ξ, P ξ * entropy (V (x ξ)) := by
    calc ∑ g, outDist P T g * ∑ a, sideCond P T x g a * entropy (V a)
        = ∑ g, ∑ a, (∑ ξ, if x ξ = a then P ξ * T ξ g else 0) * entropy (V a) := by
          refine sum_congr rfl fun g _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun a _ => by rw [← mul_assoc, mul_sideCond hP hT]
      _ = ∑ g, ∑ ξ, P ξ * T ξ g * entropy (V (x ξ)) := by
          refine sum_congr rfl fun g _ => ?_
          simp only [sum_mul, ite_mul, zero_mul]
          rw [sum_comm]
          refine sum_congr rfl fun ξ _ => ?_
          rw [sum_ite_eq]
          simp
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun ξ _ => ?_
          rw [← sum_mul, ← mul_sum, (hT ξ).sum_eq_one, mul_one]
  rw [mutualInfoOf_eq hP hW, e₁, entropy_jointOf hpG hout]
  have e₃ : ∀ ξ, entropy (sideOut T (fun ξ => V (x ξ)) ξ) = entropy (T ξ) + entropy (V (x ξ)) :=
    fun ξ => entropy_prodDist (hT ξ) (hV (x ξ))
  simp only [e₃, mul_add, sum_add_distrib]
  simp only [mutualInfoOf_eq (sideCond_isPMF hP hT _) hV, mul_sub, sum_sub_distrib]
  rw [e₂]
  ring

/-- **Lecture 6 of [elgamal2010], page 6-14.** If `V₂` is more capable than `V₁`, then replacing
the output of `V₁` by the output of `V₂` does not decrease the information, in the presence of a
conditionally independent side output. -/
theorem mutualInfoOf_sideOut_le {β' : Type*} [Fintype β'] (hP : IsPMF P) (hT : IsChannel T)
    {V₁ : α → β → ℝ} {V₂ : α → β' → ℝ} (hV₁ : IsChannel V₁) (hV₂ : IsChannel V₂)
    (h : ∀ p : α → ℝ, IsPMF p → mutualInfoOf p V₁ ≤ mutualInfoOf p V₂) :
    mutualInfoOf P (sideOut T fun ξ => V₁ (x ξ)) ≤
      mutualInfoOf P (sideOut T fun ξ => V₂ (x ξ)) := by
  rw [mutualInfoOf_sideOut hP hT hV₁, mutualInfoOf_sideOut hP hT hV₂]
  refine add_le_add_right (sum_le_sum fun g _ => ?_) _
  exact mul_le_mul_of_nonneg_left (h _ (sideCond_isPMF hP hT g))
    ((outDist_isPMF hP hT).nonneg g)

/-- The information does not depend on the names of the outputs. -/
lemma mutualInfoOf_congr_output {β' : Type*} [Fintype β'] {W : Ξ → β → ℝ} {W' : Ξ → β' → ℝ}
    (hP : IsPMF P) (hW : IsChannel W) (hW' : IsChannel W') (e : β ≃ β')
    (h : ∀ ξ z, W' ξ (e z) = W ξ z) : mutualInfoOf P W' = mutualInfoOf P W := by
  have hH : ∀ {f : β → ℝ} {f' : β' → ℝ}, (∀ z, f' (e z) = f z) → entropy f' = entropy f :=
    fun {f f'} hf => by
      simp only [entropy_eq_sum_negMulLog, ← Equiv.sum_comp e fun y => negMulLog (f' y), hf]
  rw [mutualInfoOf_eq hP hW, mutualInfoOf_eq hP hW']
  congr 1
  · exact hH fun z => by simp only [outDist, h]
  · exact sum_congr rfl fun ξ _ => by rw [hH (h ξ)]

end Side

/-! ### Products of more capable channels -/

section Product

variable {α : Type*} [Fintype α]

/-- The memoryless channel `∏ₖ Vₖ(yₖ | xₖ)`, with channels depending on the time. -/
def indexedExt {β : Type*} {n : ℕ} (V : Fin n → α → β → ℝ) (x : Fin n → α) (y : Fin n → β) : ℝ :=
  ∏ k, V k (x k) (y k)

omit [Fintype α] in
lemma indexedExt_isChannel {β : Type*} [Fintype β] {n : ℕ} {V : Fin n → α → β → ℝ}
    (hV : ∀ k, IsChannel (V k)) : IsChannel (indexedExt V) := by
  classical
  intro x
  refine ⟨fun y => prod_nonneg fun k _ => (hV k _).nonneg _, ?_⟩
  have h := Fintype.prod_sum fun (k : Fin n) (b : β) => V k (x k) b
  simp only [(hV _ _).sum_eq_one, prod_const_one] at h
  exact h.symm

omit [Fintype α] in
lemma indexedExt_consEquiv {β : Type*} {n : ℕ} (V : Fin (n + 1) → α → β → ℝ)
    (x : Fin (n + 1) → α) (b : β) (y : Fin n → β) :
    indexedExt V x (Fin.consEquiv (fun _ => β) (b, y)) =
      V 0 (x 0) b * indexedExt (fun k => V k.succ) (fun k => x k.succ) y := by
  simp [indexedExt, Fin.prod_univ_succ, Fin.consEquiv]

omit [Fintype α] in
/-- With no channel uses, only the side output remains. -/
lemma mutualInfoOf_sideOut_indexedExt_zero {Ξ γ β : Type*} [Fintype Ξ] [Fintype γ] [Fintype β]
    {P : Ξ → ℝ} (hP : IsPMF P) {T : Ξ → γ → ℝ} (hT : IsChannel T) (f : Ξ → Fin 0 → α)
    (V : Fin 0 → α → β → ℝ) :
    mutualInfoOf P (sideOut T fun ξ => indexedExt V (f ξ)) = mutualInfoOf P T :=
  mutualInfoOf_congr_output hP hT
    (sideOut_isChannel hT fun ξ => indexedExt_isChannel (fun k => k.elim0) (f ξ))
    (Equiv.prodUnique γ (Fin 0 → β)).symm fun ξ z => by simp [sideOut, indexedExt]

/-- A trivial side output does not change the information. -/
lemma mutualInfoOf_sideOut_punit {Ξ γ β : Type*} [Fintype Ξ] [Fintype β] [Unique γ] [Fintype γ]
    {P : Ξ → ℝ} (hP : IsPMF P) {U : Ξ → β → ℝ} (hU : IsChannel U) :
    mutualInfoOf P (sideOut (fun _ (_ : γ) => (1 : ℝ)) U) = mutualInfoOf P U :=
  mutualInfoOf_congr_output hP hU
    (sideOut_isChannel (fun _ => ⟨fun _ => zero_le_one, by simp⟩) hU)
    (Equiv.uniqueProd β γ).symm fun ξ z => by simp [sideOut]

variable {β₁ : Type v₁} {β₂ : Type v₂} [Fintype β₁] [Fintype β₂] {Ξ : Type uΞ} [Fintype Ξ]
  {P : Ξ → ℝ}

/-- **Lecture 6 of [elgamal2010], page 6-14.** Replacing the outputs of a memoryless channel one at
a time, in the presence of a side output `T`. The side output is generalized in the induction, as
it accumulates the outputs already replaced. -/
theorem mutualInfoOf_side_indexedExt_le (hP : IsPMF P) (n : ℕ) :
    ∀ (γ : Type (max v₁ v₂)) [Fintype γ] (T : Ξ → γ → ℝ) (_ : IsChannel T) (f : Ξ → Fin n → α)
      (V₁ : Fin n → α → β₁ → ℝ) (V₂ : Fin n → α → β₂ → ℝ) (_ : ∀ k, IsChannel (V₁ k))
      (_ : ∀ k, IsChannel (V₂ k))
      (_ : ∀ k, ∀ p : α → ℝ, IsPMF p → mutualInfoOf p (V₁ k) ≤ mutualInfoOf p (V₂ k)),
      mutualInfoOf P (sideOut T fun ξ => indexedExt V₁ (f ξ)) ≤
        mutualInfoOf P (sideOut T fun ξ => indexedExt V₂ (f ξ)) := by
  induction n with
  | zero =>
    intro γ _ T hT f V₁ V₂ _ _ _
    rw [mutualInfoOf_sideOut_indexedExt_zero hP hT f V₁,
      mutualInfoOf_sideOut_indexedExt_zero hP hT f V₂]
  | succ n ih =>
    intro γ _ T hT f V₁ V₂ hV₁ hV₂ h
    set V₁' : Fin n → α → β₁ → ℝ := fun k => V₁ k.succ
    set V₂' : Fin n → α → β₂ → ℝ := fun k => V₂ k.succ
    set f' : Ξ → Fin n → α := fun ξ k => f ξ k.succ
    have hV₁' : ∀ k, IsChannel (V₁' k) := fun k => hV₁ k.succ
    have hV₂' : ∀ k, IsChannel (V₂' k) := fun k => hV₂ k.succ
    have hI₁ : IsChannel fun ξ => indexedExt V₁' (f' ξ) := fun ξ => indexedExt_isChannel hV₁' (f' ξ)
    have hI₂ : IsChannel fun ξ => indexedExt V₂' (f' ξ) := fun ξ => indexedExt_isChannel hV₂' (f' ξ)
    have hx₁ : IsChannel fun ξ => V₁ 0 (f ξ 0) := fun ξ => hV₁ 0 _
    have hx₂ : IsChannel fun ξ => V₂ 0 (f ξ 0) := fun ξ => hV₂ 0 _
    -- The last output of the first channel, moved next to the side output.
    have s₁ : mutualInfoOf P (sideOut T fun ξ => indexedExt V₁ (f ξ)) =
        mutualInfoOf P (sideOut (sideOut T fun ξ => indexedExt V₁' (f' ξ))
          fun ξ => V₁ 0 (f ξ 0)) :=
      mutualInfoOf_congr_output hP (sideOut_isChannel (sideOut_isChannel hT hI₁) hx₁)
        (sideOut_isChannel hT fun ξ => indexedExt_isChannel hV₁ (f ξ))
        { toFun := fun z => (z.1.1, Fin.consEquiv (fun _ => β₁) (z.2, z.1.2))
          invFun := fun z => ((z.1, ((Fin.consEquiv (fun _ => β₁)).symm z.2).2),
            ((Fin.consEquiv (fun _ => β₁)).symm z.2).1)
          left_inv := fun z => by simp
          right_inv := fun z => by simp }
        fun ξ z => by
          simp only [sideOut, Equiv.coe_fn_mk, indexedExt_consEquiv, V₁', f']
          ring
    -- Replace it.
    have s₂ := mutualInfoOf_sideOut_le (x := fun ξ => f ξ 0) hP (sideOut_isChannel hT hI₁)
      (hV₁ 0) (hV₂ 0) (h 0)
    -- Swap the replaced output into the side output.
    have s₃ : mutualInfoOf P (sideOut (sideOut T fun ξ => indexedExt V₁' (f' ξ))
          fun ξ => V₂ 0 (f ξ 0)) =
        mutualInfoOf P (sideOut (sideOut T fun ξ => V₂ 0 (f ξ 0))
          fun ξ => indexedExt V₁' (f' ξ)) :=
      mutualInfoOf_congr_output hP (sideOut_isChannel (sideOut_isChannel hT hx₂) hI₁)
        (sideOut_isChannel (sideOut_isChannel hT hI₁) hx₂)
        { toFun := fun z => ((z.1.1, z.2), z.1.2)
          invFun := fun z => ((z.1.1, z.2), z.1.2)
          left_inv := fun z => rfl
          right_inv := fun z => rfl }
        fun ξ z => by
          simp only [sideOut, Equiv.coe_fn_mk]
          ring
    -- The induction hypothesis.
    have s₄ := ih (γ × β₂) (sideOut T fun ξ => V₂ 0 (f ξ 0)) (sideOut_isChannel hT hx₂) f' V₁' V₂'
      hV₁' hV₂' fun k => h k.succ
    -- Back to the second channel.
    have s₅ : mutualInfoOf P (sideOut T fun ξ => indexedExt V₂ (f ξ)) =
        mutualInfoOf P (sideOut (sideOut T fun ξ => V₂ 0 (f ξ 0))
          fun ξ => indexedExt V₂' (f' ξ)) :=
      mutualInfoOf_congr_output hP (sideOut_isChannel (sideOut_isChannel hT hx₂) hI₂)
        (sideOut_isChannel hT fun ξ => indexedExt_isChannel hV₂ (f ξ))
        { toFun := fun z => (z.1.1, Fin.consEquiv (fun _ => β₂) (z.1.2, z.2))
          invFun := fun z => ((z.1, ((Fin.consEquiv (fun _ => β₂)).symm z.2).1),
            ((Fin.consEquiv (fun _ => β₂)).symm z.2).2)
          left_inv := fun z => by simp
          right_inv := fun z => by simp }
        fun ξ z => by
          simp only [sideOut, Equiv.coe_fn_mk, indexedExt_consEquiv, V₂', f']
          ring
    rw [s₁, s₅]
    exact s₂.trans (s₃.le.trans s₄)

/-- **Lecture 6 of [elgamal2010], page 6-14.** A product of more capable channels is more capable:
if `I(X; Y₁ₖ) ≤ I(X; Y₂ₖ)` for all `p(x)` and every `k`, then `I(Xⁿ; Y₁ⁿ) ≤ I(Xⁿ; Y₂ⁿ)` for all
`p(xⁿ)`. -/
theorem mutualInfoOf_indexedExt_le {n : ℕ} {P : (Fin n → α) → ℝ} (hP : IsPMF P)
    {V₁ : Fin n → α → β₁ → ℝ} {V₂ : Fin n → α → β₂ → ℝ} (hV₁ : ∀ k, IsChannel (V₁ k))
    (hV₂ : ∀ k, IsChannel (V₂ k))
    (h : ∀ k, ∀ p : α → ℝ, IsPMF p → mutualInfoOf p (V₁ k) ≤ mutualInfoOf p (V₂ k)) :
    mutualInfoOf P (indexedExt V₁) ≤ mutualInfoOf P (indexedExt V₂) := by
  have hT : IsChannel fun (_ : Fin n → α) (_ : PUnit.{max v₁ v₂ + 1}) => (1 : ℝ) := fun _ =>
    ⟨fun _ => zero_le_one, by simp⟩
  have := mutualInfoOf_side_indexedExt_le hP n PUnit (fun _ _ => (1 : ℝ)) hT id V₁ V₂ hV₁ hV₂ h
  simp only [id] at this
  rwa [mutualInfoOf_sideOut_punit hP (indexedExt_isChannel hV₁),
    mutualInfoOf_sideOut_punit hP (indexedExt_isChannel hV₂)] at this

end Product

/-! ### Strong interference -/

section Strong

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
  {W : α₁ × α₂ → β₁ × β₂ → ℝ}

/-- **Lecture 6 of [elgamal2010].** A DM-IC has strong interference if
`I(X₁; Y₁ | X₂) ≤ I(X₁; Y₂ | X₂)` and `I(X₂; Y₂ | X₁) ≤ I(X₂; Y₁ | X₁)` for all `p(x₁) p(x₂)`. -/
def IsStrongIC (W : α₁ × α₂ → β₁ × β₂ → ℝ) : Prop :=
  ∀ (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ), IsPMF p₁ → IsPMF p₂ →
    macInfo₁ p₁ p₂ (bcMarg₁ W) ≤ macInfo₁ p₁ p₂ (bcMarg₂ W) ∧
      macInfo₂ p₁ p₂ (bcMarg₂ W) ≤ macInfo₂ p₁ p₂ (bcMarg₁ W)

/-- **Lecture 6 of [elgamal2010].** A DM-IC has very strong interference if
`I(X₁; Y₁ | X₂) ≤ I(X₁; Y₂)` and `I(X₂; Y₂ | X₁) ≤ I(X₂; Y₁)` for all `p(x₁) p(x₂)`. -/
def IsVeryStrongIC (W : α₁ × α₂ → β₁ × β₂ → ℝ) : Prop :=
  ∀ (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ), IsPMF p₁ → IsPMF p₂ →
    macInfo₁ p₁ p₂ (bcMarg₁ W) ≤ mutualInfoOf p₁ (macChannel₁ (bcMarg₂ W) p₂) ∧
      macInfo₂ p₁ p₂ (bcMarg₂ W) ≤ mutualInfoOf p₂ (macChannel₂ (bcMarg₁ W) p₁)

/-- **Lecture 6 of [elgamal2010], page 6-12.** Very strong interference implies strong
interference. -/
theorem IsVeryStrongIC.isStrongIC (hW : IsChannel W) (h : IsVeryStrongIC W) : IsStrongIC W :=
  fun p₁ p₂ hp₁ hp₂ =>
    ⟨(h p₁ p₂ hp₁ hp₂).1.trans (mutualInfoOf_macChannel₁_le hp₁ hp₂ hW.bcMarg₂),
      (h p₁ p₂ hp₁ hp₂).2.trans (mutualInfoOf_macChannel₂_le hp₁ hp₂ hW.bcMarg₁)⟩

/-- Strong interference, with the other input fixed: given `X₂ = b`, the channel to `Y₂` is more
capable than the channel to `Y₁`. -/
lemma IsStrongIC.mutualInfoOf_slice₁ (hW : IsChannel W) (h : IsStrongIC W) (b : α₂) {p : α₁ → ℝ}
    (hp : IsPMF p) :
    mutualInfoOf p (fun a => bcMarg₁ W (a, b)) ≤ mutualInfoOf p (fun a => bcMarg₂ W (a, b)) := by
  classical
  have hs := isPMF_pi_single (α := α₂) b
  have := (h p _ hp hs).1
  rw [macInfo₁_eq_sum hp hs hW.bcMarg₁, macInfo₁_eq_sum hp hs hW.bcMarg₂] at this
  simpa [Pi.single_apply] using this

/-- Strong interference, with the other input fixed: given `X₁ = a`, the channel to `Y₁` is more
capable than the channel to `Y₂`. -/
lemma IsStrongIC.mutualInfoOf_slice₂ (hW : IsChannel W) (h : IsStrongIC W) (a : α₁) {p : α₂ → ℝ}
    (hp : IsPMF p) :
    mutualInfoOf p (fun b => bcMarg₂ W (a, b)) ≤ mutualInfoOf p (fun b => bcMarg₁ W (a, b)) := by
  classical
  have hs := isPMF_pi_single (α := α₁) a
  have := (h _ p hs hp).2
  rw [macInfo₂_eq_sum hs hp hW.bcMarg₂, macInfo₂_eq_sum hs hp hW.bcMarg₁] at this
  simpa [Pi.single_apply] using this

variable {n : ℕ} {P₁ : (Fin n → α₁) → ℝ} {P₂ : (Fin n → α₂) → ℝ}

/-- **Lemma 1 of [elgamal2010], Lecture 6.** With strong interference,
`I(X₁ⁿ; Y₁ⁿ | X₂ⁿ) ≤ I(X₁ⁿ; Y₂ⁿ | X₂ⁿ)` for all `p(x₁ⁿ) p(x₂ⁿ)`. -/
theorem IsStrongIC.macInfo₁_macExt_le (hW : IsChannel W) (h : IsStrongIC W) (hP₁ : IsPMF P₁)
    (hP₂ : IsPMF P₂) :
    macInfo₁ P₁ P₂ (macExt (bcMarg₁ W) n) ≤ macInfo₁ P₁ P₂ (macExt (bcMarg₂ W) n) := by
  rw [macInfo₁_eq_sum hP₁ hP₂ (macExt_isChannel hW.bcMarg₁ n),
    macInfo₁_eq_sum hP₁ hP₂ (macExt_isChannel hW.bcMarg₂ n)]
  refine sum_le_sum fun x₂ _ => mul_le_mul_of_nonneg_left ?_ (hP₂.nonneg x₂)
  exact mutualInfoOf_indexedExt_le hP₁ (V₁ := fun k a => bcMarg₁ W (a, x₂ k))
    (V₂ := fun k a => bcMarg₂ W (a, x₂ k)) (fun k a => hW.bcMarg₁ (a, x₂ k))
    (fun k a => hW.bcMarg₂ (a, x₂ k)) fun k _ hp => h.mutualInfoOf_slice₁ hW (x₂ k) hp

/-- **Lemma 1 of [elgamal2010], Lecture 6.** With strong interference,
`I(X₂ⁿ; Y₂ⁿ | X₁ⁿ) ≤ I(X₂ⁿ; Y₁ⁿ | X₁ⁿ)` for all `p(x₁ⁿ) p(x₂ⁿ)`. -/
theorem IsStrongIC.macInfo₂_macExt_le (hW : IsChannel W) (h : IsStrongIC W) (hP₁ : IsPMF P₁)
    (hP₂ : IsPMF P₂) :
    macInfo₂ P₁ P₂ (macExt (bcMarg₂ W) n) ≤ macInfo₂ P₁ P₂ (macExt (bcMarg₁ W) n) := by
  rw [macInfo₂_eq_sum hP₁ hP₂ (macExt_isChannel hW.bcMarg₂ n),
    macInfo₂_eq_sum hP₁ hP₂ (macExt_isChannel hW.bcMarg₁ n)]
  refine sum_le_sum fun x₁ _ => mul_le_mul_of_nonneg_left ?_ (hP₁.nonneg x₁)
  exact mutualInfoOf_indexedExt_le hP₂ (V₁ := fun k b => bcMarg₂ W (x₁ k, b))
    (V₂ := fun k b => bcMarg₁ W (x₁ k, b)) (fun k b => hW.bcMarg₂ (x₁ k, b))
    (fun k b => hW.bcMarg₁ (x₁ k, b)) fun k _ hp => h.mutualInfoOf_slice₂ hW (x₁ k) hp

/-- **Theorem 1 of [elgamal2010], Lecture 6.** The region `R₁ ≤ I(X₁; Y₁ | X₂, Q)`,
`R₂ ≤ I(X₂; Y₂ | X₁, Q)`, `R₁ + R₂ ≤ min {I(X₁, X₂; Y₁ | Q), I(X₁, X₂; Y₂ | Q)}` for some
`p(q) p(x₁ | q) p(x₂ | q)`, in bits. -/
def icStrongRegionBits (W : α₁ × α₂ → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k → ℝ) (p₁ : Fin k → α₁ → ℝ) (p₂ : Fin k → α₂ → ℝ),
    IsPMF q ∧ (∀ i, IsPMF (p₁ i)) ∧ (∀ i, IsPMF (p₂ i)) ∧
    R.1 ≤ icAvg₁ q p₁ p₂ (bcMarg₁ W) / log 2 ∧ R.2 ≤ icAvg₂ q p₁ p₂ (bcMarg₂ W) / log 2 ∧
    R.1 + R.2 ≤ icAvg₁₂ q p₁ p₂ (bcMarg₁ W) / log 2 ∧
    R.1 + R.2 ≤ icAvg₁₂ q p₁ p₂ (bcMarg₂ W) / log 2}

namespace ICCode

variable {M₁ M₂ : ℕ} (c : ICCode M₁ M₂ n α₁ α₂ β₁ β₂)

/-- **Theorem 1 of [elgamal2010], Lecture 6 (converse), for one code.**
`n (R₁ + R₂) ≤ I(X₁ⁿ; Y₁ⁿ) + I(X₂ⁿ; Y₂ⁿ) + nεₙ ≤ I(X₁ⁿ; Y₂ⁿ | X₂ⁿ) + I(X₂ⁿ; Y₂ⁿ) + nεₙ
= I(X₁ⁿ, X₂ⁿ; Y₂ⁿ) + nεₙ ≤ ∑ᵢ I(X₁ᵢ, X₂ᵢ; Y₂ᵢ) + nεₙ`. -/
theorem log_add_log_le_sum_macInfo₁₂_marg₂ (hW : IsChannel W) (h : IsStrongIC W) (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) :
    log M₁ + log M₂ ≤ ∑ i, macInfo₁₂ (c.letter₁ i) (c.letter₂ i) (bcMarg₂ W) + 2 * log 2 +
      c.errProb₁ W * log M₁ + c.errProb₂ W * log M₂ := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hP₁ : IsPMF c.codeword₁ := uniformPMF_isPMF.dist _
  have hP₂ : IsPMF c.codeword₂ := uniformPMF_isPMF.dist _
  have hV₁ := macExt_isChannel hW.bcMarg₁ n
  have hV₂ := macExt_isChannel hW.bcMarg₂ n
  have b₁ := c.log_le_mutualInfoOf_codeword₁ hW h₁ h₂
  have b₂ := c.log_le_mutualInfoOf_codeword₂ hW h₁ h₂
  have s₁ := mutualInfoOf_macChannel₁_le hP₁ hP₂ hV₁
  have s₂ := h.macInfo₁_macExt_le hW hP₁ hP₂
  have s₃ := macInfo₁₂_eq_add₁ hP₁ hP₂ hV₂
  have s₄ := mutualInfoOf_macChannel₂ (p₂ := c.codeword₂) hP₁ hV₂
  rw [mutualInfo_comm (macJoint_isPMF hP₁ hP₂ hV₂)] at s₄
  have s₅ := (macInfo_macExt_le hP₁ hP₂ hW.bcMarg₂).2.2
  simp only [letter₁, letter₂]
  linarith

/-- **Theorem 1 of [elgamal2010], Lecture 6 (converse), for one code.** The other sum-rate bound:
`n (R₁ + R₂) ≤ ∑ᵢ I(X₁ᵢ, X₂ᵢ; Y₁ᵢ) + nεₙ`. -/
theorem log_add_log_le_sum_macInfo₁₂_marg₁ (hW : IsChannel W) (h : IsStrongIC W) (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) :
    log M₁ + log M₂ ≤ ∑ i, macInfo₁₂ (c.letter₁ i) (c.letter₂ i) (bcMarg₁ W) + 2 * log 2 +
      c.errProb₁ W * log M₁ + c.errProb₂ W * log M₂ := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hP₁ : IsPMF c.codeword₁ := uniformPMF_isPMF.dist _
  have hP₂ : IsPMF c.codeword₂ := uniformPMF_isPMF.dist _
  have hV₁ := macExt_isChannel hW.bcMarg₁ n
  have hV₂ := macExt_isChannel hW.bcMarg₂ n
  have b₁ := c.log_le_mutualInfoOf_codeword₁ hW h₁ h₂
  have b₂ := c.log_le_mutualInfoOf_codeword₂ hW h₁ h₂
  have s₁ := mutualInfoOf_macChannel₂_le hP₁ hP₂ hV₂
  have s₂ := h.macInfo₂_macExt_le hW hP₁ hP₂
  have s₃ := macInfo₁₂_eq_add₂ hP₁ hP₂ hV₁
  have s₄ := mutualInfoOf_macChannel₁ (p₁ := c.codeword₁) hP₂ hV₁
  rw [mutualInfo_comm (macJoint_isPMF hP₁ hP₂ hV₁)] at s₄
  have s₅ := (macInfo_macExt_le hP₁ hP₂ hW.bcMarg₁).2.2
  simp only [letter₁, letter₂]
  linarith

end ICCode

/-- **Theorem 1 of [elgamal2010], Lecture 6 (converse).** With strong interference, every achievable
rate pair is in the closure of the region of Theorem 1, with the time-sharing variable uniform on
the `n` positions. -/
theorem IsAchievableICBits.mem_closure_icStrongRegionBits (hW : IsChannel W) (hs : IsStrongIC W)
    {R₁ R₂ : ℝ} (h : IsAchievableICBits W R₁ R₂) : (R₁, R₂) ∈ closure (icStrongRegionBits W) := by
  obtain ⟨c, hc⟩ := h
  have hl := log_pos one_lt_two
  set P : ℕ → ℝ := fun n => 2 * (c n).errProb W
  have hP : ∀ n, 0 ≤ P n := fun n => mul_nonneg (by norm_num) ((c n).errProb_nonneg hW)
  have hP0 : Tendsto P atTop (𝓝 0) := by simpa using hc.const_mul 2
  refine mem_closure_of_sub_icEps (tendsto_icEps (R₁ := R₁) (R₂ := R₂) hP hP0) fun n hn => ?_
  have hM₁ := two_pow_ceil_pos n R₁
  have hM₂ := two_pow_ceil_pos n R₂
  have : Nonempty (Fin (2 ^ ⌈n * R₁⌉₊)) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin (2 ^ ⌈n * R₂⌉₊)) := ⟨⟨0, hM₂⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A := log ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ)
  set B := log ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ)
  have hA : 0 ≤ A := log_natCast_nonneg _
  have hB : 0 ≤ B := log_natCast_nonneg _
  have l₁ : n * R₁ * log 2 ≤ A := (log_two_pow_ceil_bounds n R₁).1
  have l₂ : n * R₂ * log 2 ≤ B := (log_two_pow_ceil_bounds n R₂).1
  have b₁ := (c n).log_le_sum_macInfo₁ hW hM₁ hM₂
  have b₂ := (c n).log_le_sum_macInfo₂ hW hM₁ hM₂
  have b₃ := (c n).log_add_log_le_sum_macInfo₁₂_marg₁ hW hs hM₁ hM₂
  have b₄ := (c n).log_add_log_le_sum_macInfo₁₂_marg₂ hW hs hM₁ hM₂
  have m₁ := mul_le_mul_of_nonneg_right ((c n).errProb₁_le hW) hA
  have m₂ := mul_le_mul_of_nonneg_right ((c n).errProb₂_le hW) hB
  have mA : (c n).errProb W * A ≥ 0 := mul_nonneg ((c n).errProb_nonneg hW) hA
  have mB : (c n).errProb W * B ≥ 0 := mul_nonneg ((c n).errProb_nonneg hW) hB
  have hPe : P n * (A + B) = 2 * ((c n).errProb W * A) + 2 * ((c n).errProb W * B) := by
    simp only [P]
    ring
  have hE := icEps_nonneg (R₁ := R₁) (R₂ := R₂) hP n
  have hs₁ : (R₁ + R₂) - icEps R₁ R₂ P n ≤
      (1 / n * ∑ i, macInfo₁₂ ((c n).letter₁ i) ((c n).letter₂ i) (bcMarg₁ W)) / log 2 :=
    sub_icEps_le hn (by nlinarith)
  have hs₂ : (R₁ + R₂) - icEps R₁ R₂ P n ≤
      (1 / n * ∑ i, macInfo₁₂ ((c n).letter₁ i) ((c n).letter₂ i) (bcMarg₂ W)) / log 2 :=
    sub_icEps_le hn (by nlinarith)
  refine ⟨n, fun _ => 1 / n, fun i => (c n).letter₁ i, fun i => (c n).letter₂ i,
    ⟨fun _ => by positivity, by simp [hn'.ne']⟩, fun i => (uniformPMF_isPMF.dist _).dist _,
    fun i => (uniformPMF_isPMF.dist _).dist _, ?_, ?_, ?_, ?_⟩
  · simp only [icAvg₁, ← mul_sum]
    exact sub_icEps_le hn (by nlinarith)
  · simp only [icAvg₂, ← mul_sum]
    exact sub_icEps_le hn (by nlinarith)
  · simp only [icAvg₁₂, ← mul_sum]
    linarith
  · simp only [icAvg₁₂, ← mul_sum]
    linarith

end Strong

end InfoTheory
