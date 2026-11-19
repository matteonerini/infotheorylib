/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCCapacity
public import InfoTheoryLib.Network.FeedbackLaw

/-!
# The broadcast channel with feedback

Theorem 4 of Lecture 18: the capacity region of a physically degraded DM-BC does not increase with
feedback.

## Main definitions

* `BCFBCode`: a code for the broadcast channel with feedback from both receivers.
* `IsAchievableBCFB`, `bcfbCapacityRegion`: achievable rates and the capacity region.

## Main statements

* `BCFBCode.log_le_sum₁`, `BCFBCode.log_le_sum₂`: the bounds for a single code.
* `IsAchievableBCFB.mem_closure_degradedBCRegionBits`: the converse.
* `bcfbCapacityRegion_eq`: **Theorem 4**.

## Implementation notes

The remark of page 18-39 says that the converse without feedback needs to be modified. The converse
of Lecture 5 here already uses `Uᵢ = (M₂, Y₁^{i-1}, Y₂^{i-1})`, which is what the modification
needs: the input `Xᵢ` is now a function of `(M₁, M₂, Y₁^{i-1}, Y₂^{i-1})`, and the chain rule
replaces the factorization of the law over the times.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {M₁ M₂ n : ℕ}
  {W : α → β₁ × β₂ → ℝ}

/-- **Page 18-39 of [elgamal2010].** A code for the broadcast channel with feedback from both
receivers. -/
structure BCFBCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*) where
  /-- The encoder. -/
  enc : ∀ k, Fin M₁ × Fin M₂ → (Fin k → β₁ × β₂) → α
  /-- The decoder of receiver 1. -/
  dec₁ : (Fin n → β₁) → Fin M₁
  /-- The decoder of receiver 2. -/
  dec₂ : (Fin n → β₂) → Fin M₂

namespace BCFBCode

variable (c : BCFBCode M₁ M₂ n α β₁ β₂)

/-- The joint law of the uniform messages and of the outputs. -/
def law (W : α → β₁ × β₂ → ℝ) : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → ℝ :=
  fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W c.enc n

/-- The probability of error. -/
def errProb (W : α → β₁ × β₂ → ℝ) : ℝ :=
  InfoTheory.errProb (c.law W) Prod.fst (fun z => z.2)
    fun y => (c.dec₁ fun i => (y i).1, c.dec₂ fun i => (y i).2)

/-- The probability of error at receiver 1. -/
def errProb₁ (W : α → β₁ × β₂ → ℝ) : ℝ :=
  InfoTheory.errProb (c.law W) (fun z => z.1.1) (fun z i => (z.2 i).1) c.dec₁

/-- The probability of error at receiver 2. -/
def errProb₂ (W : α → β₁ × β₂ → ℝ) : ℝ :=
  InfoTheory.errProb (c.law W) (fun z => z.1.2) (fun z i => (z.2 i).2) c.dec₂

/-- The law of `(Uᵢ, Xᵢ)`, with `Uᵢ = (Y₁^{i-1}, Y₂^{i-1}, M₂)`. -/
def letter (W : α → β₁ × β₂ → ℝ) (i : Fin n) : ((Fin n → Option (β₁ × β₂)) × Fin M₂) × α → ℝ :=
  dist (c.law W) fun z => ((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc i z.1 (fbPre i z.2))

omit [Fintype α] in
lemma law_isPMF (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) : IsPMF (c.law W) :=
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  fbLaw_isPMF uniformPMF_isPMF hW n

/-- The past outputs as a vector of fixed length, from the prefix. -/
def mask (i : Fin n) {γ : Type*} (u : Fin i → γ) : Fin n → Option γ :=
  fun j => if h : (j : ℕ) < i then some (u ⟨j, h⟩) else none

omit [Fintype α] [Fintype β₁] [Fintype β₂] in
lemma mask_fbPre (i : Fin n) {γ : Type*} (z : Fin n → γ) :
    mask i (fbPre i z) = degradedBCPast (i : ℕ) z := by
  funext j
  by_cases h : (j : ℕ) < i <;> simp [mask, degradedBCPast, fbPre, h]

omit [Fintype α] [Fintype β₁] [Fintype β₂] in
lemma mask_injective (i : Fin n) {γ : Type*} : Function.Injective (mask (i := i) (γ := γ)) := by
  intro u v h
  funext t
  have ht := congrFun h ⟨t, t.isLt.trans i.isLt⟩
  simpa [mask, t.isLt] using ht

omit [Fintype α] in
/-- The law of `((Uᵢ, Xᵢ), (Y₁ᵢ, Y₂ᵢ))`. -/
lemma dist_letter [Finite α] (hW : IsChannel W) (i : Fin n) :
    dist (c.law W) (fun z => (((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc i z.1 (fbPre i z.2)),
      z.2 i)) = bcJoint (c.letter W i) W := by
  have : Fintype α := Fintype.ofFinite α
  funext ⟨t, b⟩
  have h := dist_fbLaw_letter (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := W) (enc := c.enc) hW i
    (fun z : (Fin M₁ × Fin M₂) × (Fin i → β₁ × β₂) => ((mask i z.2, z.1.2), c.enc i z.1 z.2))
    Prod.snd (fun _ _ => rfl) t b
  simp only [mask_fbPre] at h
  exact h

/-- `H(Yᵢ | past, M) = H(Yᵢ | Xᵢ)`, the entropy of the channel. -/
lemma condEntropy_past (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (i : Fin n) :
    H[fun z => z.2 i | pair (fun z => degradedBCPast (i : ℕ) z.2) Prod.fst ; c.law W] =
      ∑ a, dist (c.law W) (fun z => c.enc i z.1 (fbPre i z.2)) a * entropy (W a) := by
  have hμ := c.law_isPMF (W := W) hW h₁ h₂
  have hc : H[fun z => z.2 i | pair (fun z => degradedBCPast (i : ℕ) z.2) Prod.fst ; c.law W] =
      H[fun z => z.2 i | pair (fun z => fbPre i z.2) Prod.fst ; c.law W] :=
    condEntropy_congr_right hμ _ (fun t : (Fin i → β₁ × β₂) × (Fin M₁ × Fin M₂) => (mask i t.1,
      t.2))
      (fun a b h => Prod.ext (mask_injective i (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2)
      fun z => by
        simp only [pair, mask_fbPre]
  rw [hc]
  refine condEntropy_of_channel (fun t : (Fin i → β₁ × β₂) × (Fin M₁ × Fin M₂) => c.enc i t.2 t.1)
    fun t b => ?_
  exact dist_fbLaw_letter (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := W) (enc := c.enc) hW i
    (fun z : (Fin M₁ × Fin M₂) × (Fin i → β₁ × β₂) => (z.2, z.1))
    (fun t => c.enc i t.2 t.1) (fun _ _ => rfl) t b

/-- `H(Yᵢ | Uᵢ) - H(Yᵢ | Xᵢ) = I(Xᵢ; Y₁ᵢ | Uᵢ)`, for a physically degraded channel. -/
lemma term₁ (hW : IsChannel W) (hd : IsPhysicallyDegraded W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (i : Fin n) : H[fun z => z.2 i | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ; c.law W] - ∑
    a, dist (c.law W) (fun z => c.enc i z.1 (fbPre i z.2)) a * entropy (W a) = bcInfoXY₁U
    (c.letter W i) W := by
  have hμ := c.law_isPMF (W := W) hW h₁ h₂
  have hq : IsPMF (c.letter W i) := hμ.dist _
  have hB : H[fun z => z.2 i | pair (fun z => c.enc i z.1 (fbPre i z.2))
      (fun z => (degradedBCPast (i : ℕ) z.2, z.1.2)) ; c.law W] =
      ∑ a, dist (c.law W) (fun z => c.enc i z.1 (fbPre i z.2)) a * entropy (W a) := by
    refine condEntropy_of_channel Prod.fst fun t b => ?_
    have h := dist_fbLaw_letter (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := W) (enc := c.enc) hW i
      (fun z : (Fin M₁ × Fin M₂) × (Fin i → β₁ × β₂) => (c.enc i z.1 z.2, (mask i z.2, z.1.2)))
      Prod.fst (fun _ _ => rfl) t b
    simp only [mask_fbPre] at h
    exact h
  have e := condMutualInfo_comp hμ
    (fun z => (((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc i z.1 (fbPre i z.2)), z.2 i))
    (fun t => t.1.2) Prod.snd (fun t => t.1.1)
  rw [c.dist_letter hW i, degradedBC_condMutualInfo_out_eq hq hW hd,
    condMutualInfo_comm hμ, condMutualInfo] at e
  rw [← e, ← hB]
  rfl

/-- `H(Y₂ᵢ) - H(Y₂ᵢ | Uᵢ) = I(Uᵢ; Y₂ᵢ)`. -/
lemma term₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (i : Fin n) :
    H[fun z => (z.2 i).2 ; c.law W] -
      H[fun z => (z.2 i).2 | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ; c.law W] =
      bcInfoUY₂ (c.letter W i) W := by
  have hμ := c.law_isPMF (W := W) hW h₁ h₂
  have e := mutualInfo_comp (μ := c.law W)
    (fun z => (((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc i z.1 (fbPre i z.2)), z.2 i))
    (fun t => t.1.1) (fun t => t.2.2)
  rw [c.dist_letter hW i, mutualInfo_eq_entropy_sub_condEntropy' hμ] at e
  exact e

omit [Fintype α] in
lemma entropy_law (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    H[Prod.fst ; c.law W] = log (M₁ * M₂) := by
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  have hd : dist (c.law W) Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hW n
  rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rfl

omit [Fintype α] in
lemma entropy_law₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2 ; c.law W] = log M₂ := by
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hd : dist (c.law W) Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hW n
  have hu : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.2) = uniformPMF (Fin M₂) := by
    have := MACCode.dist_uniformPMF_prod_snd (M₂ := M₂) h₁ id
    rw [dist_id] at this
    exact this
  have e : (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2) =
      (fun w : Fin M₁ × Fin M₂ => w.2) ∘ Prod.fst := rfl
  rw [entropyRV, e, dist_comp_eq, hd, hu, entropy_uniformPMF, Fintype.card_fin]

/-- **The bound on `R₁`, for one code.** -/
theorem log_le_sum₁ (hW : IsChannel W) (hd : IsPhysicallyDegraded W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₁ ≤ ∑ i, bcInfoXY₁U (c.letter W i) W + log 2 + c.errProb₁ W * log M₁ := by
  have hμ := c.law_isPMF (W := W) hW h₁ h₂
  set μ := c.law W with hμdef
  set Mv : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₁ × Fin M₂ := Prod.fst
  set A : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₁ := fun z => z.1.1
  set B : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₂ := fun z => z.1.2
  set Y : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin n → β₁ × β₂ := Prod.snd
  have hH : H[A | B ; μ] = log M₁ := by
    rw [condEntropy_eq_sub hμ]
    have e : H[pair B A ; μ] = H[Mv ; μ] :=
      entropyRV_eq_of_injective μ Prod.swap Prod.swap_injective fun _ => rfl
    have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
    have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
    rw [e, c.entropy_law hW h₁ h₂, c.entropy_law₂ hW h₁ h₂, log_mul hM₁ hM₂]
    ring
  have hF : H[A | pair Y B ; μ] ≤ log 2 + c.errProb₁ W * log M₁ := by
    have h0 := condEntropy_le_condEntropy_comp hμ A (pair Y B)
      (fun p (j : Fin n) => (p.1 j).1)
    have h3 := fano_weak hμ A (fun z j => (z.2 j).1) c.dec₁
    have e : InfoTheory.errProb μ A (fun z j => (z.2 j).1) c.dec₁ = c.errProb₁ W := rfl
    rw [e, Fintype.card_fin] at h3
    exact h0.trans h3
  have hI : I[A : Y | B ; μ] = H[Y | B ; μ] - H[Y | Mv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
    rfl
  have hchain := condEntropy_eq_sum_past hμ Y B
  have hchain₂ := condEntropy_eq_sum_past hμ Y Mv
  have hsum : ∑ i, bcInfoXY₁U (c.letter W i) W =
      ∑ i, H[fun ω => Y ω i | pair (fun ω => degradedBCPast (i : ℕ) (Y ω)) B ; μ] -
        ∑ i, H[fun ω => Y ω i | pair (fun ω => degradedBCPast (i : ℕ) (Y ω)) Mv ; μ] := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    have h₃ := c.condEntropy_past hW h₁ h₂ i
    have h₄ := c.term₁ hW hd h₁ h₂ i
    rw [← h₄, ← h₃]
    rfl
  have hfano : H[A | B ; μ] = I[A : Y | B ; μ] + H[A | pair Y B ; μ] := by
    rw [condMutualInfo]
    ring
  linarith

/-- **The bound on `R₂`, for one code.** -/
theorem log_le_sum₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₂ ≤ ∑ i, bcInfoUY₂ (c.letter W i) W + log 2 + c.errProb₂ W * log M₂ := by
  have hμ := c.law_isPMF (W := W) hW h₁ h₂
  set μ := c.law W with hμdef
  set B : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₂ := fun z => z.1.2
  set Y₂ : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin n → β₂ := fun z j => (z.2 j).2
  have hH : H[B ; μ] = log M₂ := c.entropy_law₂ hW h₁ h₂
  have hF : H[B | Y₂ ; μ] ≤ log 2 + c.errProb₂ W * log M₂ := by
    have h3 := fano_weak hμ B Y₂ c.dec₂
    have e : InfoTheory.errProb μ B Y₂ c.dec₂ = c.errProb₂ W := rfl
    rwa [e, Fintype.card_fin] at h3
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ B Y₂
  have hI' := mutualInfo_eq_entropy_sub_condEntropy' hμ B Y₂
  have hY : H[Y₂ ; μ] ≤ ∑ i, H[fun z => (z.2 i).2 ; μ] := by
    have := condEntropy_pi_le_sum hμ Y₂ (fun _ => ())
    simp only [condEntropy_const hμ] at this
    exact this
  have hchain := condEntropy_eq_sum_past hμ Y₂ B
  have hle : ∀ i : Fin n, H[fun z => (z.2 i).2 | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ; μ] ≤
      H[fun ω => Y₂ ω i | pair (fun ω => degradedBCPast (i : ℕ) (Y₂ ω)) B ; μ] := by
    intro i
    have h := condEntropy_le_condEntropy_comp hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) =>
      (z.2 i).2) (fun z => (degradedBCPast (i : ℕ) z.2, z.1.2))
      (fun p => ((fun j => (p.1 j).map Prod.snd), p.2))
    have e : ((fun p : (Fin n → Option (β₁ × β₂)) × Fin M₂ =>
        ((fun j => (p.1 j).map Prod.snd), p.2)) ∘
        fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => (degradedBCPast (i : ℕ) z.2, z.1.2)) =
        pair (fun ω => degradedBCPast (i : ℕ) (Y₂ ω)) B := by
      funext z
      refine Prod.ext ?_ rfl
      funext j
      by_cases hj : j < i <;> simp [degradedBCPast, Y₂, pair_apply, hj]
    rw [e] at h
    exact h
  have hsum : ∑ i, bcInfoUY₂ (c.letter W i) W =
      ∑ i, H[fun z => (z.2 i).2 ; μ] -
        ∑ i : Fin n, H[fun z => (z.2 i).2 | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ; μ] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => (c.term₂ hW h₁ h₂ i).symm
  have hle' := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin n))) => hle i
  linarith

omit [Fintype α] in
/-- The probability of error at a receiver is at most the probability of error. -/
lemma errProb₁_le (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    c.errProb₁ W ≤ c.errProb W := by
  classical
  have hμ := c.law_isPMF (W := W) hW h₁ h₂
  refine sum_le_sum fun z _ => ?_
  by_cases h : c.dec₁ (fun j => (z.2 j).1) = z.1.1
  · rw [ite_eq_right (not_not.mpr h)]
    split_ifs
    · exact hμ.nonneg z
    · exact le_rfl
  · rw [ite_eq_left h, ite_eq_left]
    exact fun he => h (congrArg Prod.fst he)

omit [Fintype α] in
lemma errProb₂_le (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    c.errProb₂ W ≤ c.errProb W := by
  classical
  have hμ := c.law_isPMF (W := W) hW h₁ h₂
  refine sum_le_sum fun z _ => ?_
  by_cases h : c.dec₂ (fun j => (z.2 j).2) = z.1.2
  · rw [ite_eq_right (not_not.mpr h)]
    split_ifs
    · exact hμ.nonneg z
    · exact le_rfl
  · rw [ite_eq_left h, ite_eq_left]
    exact fun he => h (congrArg Prod.snd he)

end BCFBCode

/-- A code without feedback is a code with feedback that ignores it. -/
def BCCode.toFB [Nonempty α] (c : BCCode M₁ M₂ n α β₁ β₂) : BCFBCode M₁ M₂ n α β₁ β₂ where
  enc := nfEnc c.enc
  dec₁ := c.dec₁
  dec₂ := c.dec₂

omit [Fintype α] in
/-- The code has the same probability of error. -/
lemma BCCode.errProb_toFB [Nonempty α] (c : BCCode M₁ M₂ n α β₁ β₂) :
    c.toFB.errProb W = c.errProb W := by
  classical
  simp only [BCFBCode.errProb, InfoTheory.errProb, BCCode.errProb, BCFBCode.law, BCCode.toFB]
  rw [Fintype.sum_prod_type, sum_div]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun y _ => ?_
  rw [fbLaw_nfEnc]
  simp only [uniformPMF, Fintype.card_prod, Fintype.card_fin]
  push_cast
  by_cases h : c.dec₁ (fun i => (y i).1) ≠ w.1 ∨ c.dec₂ (fun i => (y i).2) ≠ w.2
  · rw [ite_eq_left h, ite_eq_left]
    · ring
    · intro he
      rcases h with h | h
      · exact h (congrArg Prod.fst he)
      · exact h (congrArg Prod.snd he)
  · rw [ite_eq_right h, ite_eq_right]
    · simp
    · push Not at h
      exact fun hc => hc (Prod.ext h.1 h.2)

/-- **Page 18-39 of [elgamal2010].** A rate pair, in bits, is achievable with feedback. -/
def IsAchievableBCFB (W : α → β₁ × β₂ → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, BCFBCode (2 ^ ⌈(n : ℝ) * R₁⌉₊) (2 ^ ⌈(n : ℝ) * R₂⌉₊) n α β₁ β₂,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Page 18-39 of [elgamal2010].** The capacity region with feedback, in bits. -/
def bcfbCapacityRegion (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableBCFB W R.1 R.2}

/-- **The converse of Theorem 4.** -/
theorem IsAchievableBCFB.mem_closure_degradedBCRegionBits (hW : IsChannel W)
    (hd : IsPhysicallyDegraded W) {R₁ R₂ : ℝ} (h : IsAchievableBCFB W R₁ R₂) :
    (R₁, R₂) ∈ closure (degradedBCRegionBits W) := by
  obtain ⟨c, hc⟩ := h
  set a₁ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₁⌉₊ with ha₁
  set a₂ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₂⌉₊ with ha₂
  set P : ℕ → ℝ := fun n => (c n).errProb W with hPdef
  set ε : ℕ → ℝ := fun n => (1 + P n * ((a₁ n : ℝ) + a₂ n)) / n with hεdef
  have hpos₁ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := fun n => by positivity
  have hpos₂ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := fun n => by positivity
  have hP₁ : ∀ n, (c n).errProb₁ W ≤ P n := fun n => (c n).errProb₁_le hW (hpos₁ n) (hpos₂ n)
  have hP₂ : ∀ n, (c n).errProb₂ W ≤ P n := fun n => (c n).errProb₂_le hW (hpos₁ n) (hpos₂ n)
  have hP0 : ∀ n, 0 ≤ P n := fun n => errProb_nonneg ((c n).law_isPMF hW (hpos₁ n) (hpos₂ n)) _ _ _
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg zero_le_one
    (mul_nonneg (hP0 n) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Nat.cast_nonneg n)
  have hL := log_two_pos'
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ degradedBCRegionBits W := by
    intro n hn
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hM₁ := hpos₁ n
    have hM₂ := hpos₂ n
    have hμ := (c n).law_isPMF (W := W) hW hM₁ hM₂
    have hq : ∀ i, IsPMF ((c n).letter W i) := fun i => hμ.dist _
    have hw : IsPMF (uniformPMF (Fin n)) := uniformPMF_isPMF
    have hbar := degradedBCTimeShare_isPMF hw hq
    have b₁ := (c n).log_le_sum₁ hW hd hM₁ hM₂
    have b₂ := (c n).log_le_sum₂ hW hM₁ hM₂
    refine ⟨_, degradedBCRelabelLaw (Fintype.equivFin _)
      (degradedBCTimeShare (uniformPMF (Fin n)) ((c n).letter W)),
      degradedBCRelabelLaw_isPMF _ hbar, ?_, ?_⟩
    · rw [degradedBC_bcInfoXY₁U_relabel _ hbar hW, bcInfoXY₁U_degradedBCTimeShare hw hq hW,
        degradedBC_sum_uniform]
      exact degradedBC_rate_le (b := a₂ n) hn (hP0 n) (hP₁ n) (by exact_mod_cast b₁)
    · rw [degradedBC_bcInfoUY₂_relabel _ hbar hW]
      have h1 := sum_mul_bcInfoUY₂_le_degradedBCTimeShare (W := W) hw hq hW
      rw [degradedBC_sum_uniform] at h1
      have h2 := degradedBC_rate_le (b := a₁ n) hn (hP0 n) (hP₂ n) (by exact_mod_cast b₂)
      have h3 : ε n = (1 + P n * ((a₂ n : ℝ) + a₁ n)) / n := by
        simp only [hεdef, add_comm]
      rw [h3]
      exact h2.trans (div_le_div_of_nonneg_right h1 hL.le)
  have hε : Tendsto ε atTop (𝓝 0) := by
    set K := |R₁| + |R₂| + 2
    have hP0' : Tendsto P atTop (𝓝 0) := hc
    have hup : Tendsto (fun n : ℕ => 1 / (n : ℝ) + P n * K) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add (hP0'.mul_const K)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall hε0) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hceil : ∀ x : ℝ, (⌈x⌉₊ : ℝ) ≤ |x| + 1 := fun x => by
      have h1 : (⌈x⌉₊ : ℝ) ≤ ⌈|x|⌉₊ := by exact_mod_cast Nat.ceil_mono (le_abs_self x)
      linarith [Nat.ceil_lt_add_one (abs_nonneg x)]
    have h1 := hceil ((n : ℝ) * R₁)
    have h2 := hceil ((n : ℝ) * R₂)
    rw [abs_mul, Nat.abs_cast] at h1 h2
    have hab : (a₁ n : ℝ) + a₂ n ≤ n * K := by
      simp only [ha₁, ha₂, K]
      nlinarith
    simp only [hεdef]
    rw [add_div, mul_div_assoc]
    gcongr
    · exact hP0 n
    · rw [div_le_iff₀ hn']
      linarith
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

omit [Fintype α] in
/-- **Theorem 4 of Lecture 18 of [elgamal2010], page 18-39.** The capacity region of a physically
degraded DM-BC does not increase with feedback. -/
theorem bcfbCapacityRegion_eq [Finite α] [Nonempty α] (hW : IsChannel W)
    (hd : IsPhysicallyDegraded W) : bcfbCapacityRegion W = bcCapacityRegionBits W := by
  have : Fintype α := Fintype.ofFinite α
  refine Set.Subset.antisymm ?_ ?_
  · rw [bcCapacityRegionBits_eq_closure_degradedBCRegionBits hW hd.isStochasticallyDegraded]
    exact closure_minimal (fun R hR => hR.mem_closure_degradedBCRegionBits hW hd) isClosed_closure
  · refine closure_mono fun R hR => ?_
    obtain ⟨c, hc⟩ := hR
    refine ⟨fun n => (c n).toFB, ?_⟩
    simp_rw [BCCode.errProb_toFB]
    exact hc

end InfoTheory
