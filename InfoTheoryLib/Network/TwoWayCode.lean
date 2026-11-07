/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCFeedback

/-!
# Codes for two senders that see the past outputs

Lecture 18 studies channels with two senders whose encoders see the past outputs: the two-way
channel, and the multiple-access channel with feedback. This file gives the common definition and
the converse.

## Main definitions

* `TWCCode`: a code for two nodes: each node has a message, sees a function of the output of the
  channel, and decodes the message of the other node.
* `TWCCode.law`, `TWCCode.err₁`, `TWCCode.err₂`: its law and its probabilities of error.
* `IsAchievableTWC`, `twcCapacityRegion`: achievable rates of the two-way channel.

## Main statements

* `condInfo_le_sum`: the bound `I(A; Oⁿ | B) ≤ ∑ᵢ (H(Oᵢ | φ(Xᵢ)) - H(Oᵢ | Xᵢ))`.
* `TWCCode.exists_input_law`: **the outer bound for one code**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The single-letter bound -/

section Bound

variable {𝒲 A B α β γ ξ : Type*} [Fintype 𝒲] [Fintype A] [Fintype B] [Fintype α] [Fintype β]
  [Fintype γ] [Fintype ξ] {ν : 𝒲 → ℝ} {W : α → β → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β) → α} {n : ℕ}

/-- **The single-letter bound.** Let `A, B` be functions of the message `w` that determine it. Let
`O` be a function of the output, and suppose that a function `φ` of the input is determined by `B`
and by the past of `O`. Then `I(A; Oⁿ | B) ≤ ∑ᵢ (H(Oᵢ | φ(Xᵢ)) - H(Oᵢ | Xᵢ))`. -/
theorem condInfo_le_sum (hν : IsPMF ν) (hW : IsChannel W) (ma : 𝒲 → A) (mb : 𝒲 → B)
    (hab : Function.Injective fun w => (ma w, mb w)) (v : β → γ) (φ : α → ξ)
    (e : ∀ k, B → (Fin k → γ) → ξ)
    (he : ∀ k w (z : Fin k → β), φ (enc k w z) = e k (mb w) fun i => v (z i)) :
    I[fun z => ma z.1 : fun z i => v (z.2 i) | fun z => mb z.1 ; fbLaw ν W enc n] ≤
      ∑ i : Fin n, (H[fun z => v (z.2 i) | fun z => φ (enc i z.1 (fbPre i z.2)) ; fbLaw ν W enc n] -
        H[fun z => v (z.2 i) | fun z => enc i z.1 (fbPre i z.2) ; fbLaw ν W enc n]) := by
  classical
  have hμ : IsPMF (fbLaw ν W enc n) := fbLaw_isPMF hν hW n
  set μ := fbLaw ν W enc n with hμd
  let Ma : 𝒲 × (Fin n → β) → A := fun z => ma z.1
  let Mb : 𝒲 × (Fin n → β) → B := fun z => mb z.1
  let O : 𝒲 × (Fin n → β) → Fin n → γ := fun z i => v (z.2 i)
  have hI : I[Ma : O | Mb ; μ] = H[O | Mb ; μ] - H[O | Prod.fst ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    congr 1
    exact condEntropy_congr_right hμ O (fun w : 𝒲 => (mb w, ma w))
      (fun a b h => hab (Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1)) fun _ => rfl
  have hc₁ := condEntropy_eq_sum_past hμ O Mb
  have hc₂ := condEntropy_eq_sum_past hμ O Prod.fst
  rw [hI, hc₁, hc₂, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  -- the first term
  have h₁ : H[fun ω => O ω i | pair (fun ω => degradedBCPast (i : ℕ) (O ω)) Mb ; μ] ≤
      H[fun z => v (z.2 i) | fun z => φ (enc i z.1 (fbPre i z.2)) ; μ] := by
    have hinj : H[fun ω => O ω i | pair (fun ω => degradedBCPast (i : ℕ) (O ω)) Mb ; μ] =
        H[fun ω => O ω i | pair (fun ω => fbPre i (O ω)) Mb ; μ] :=
      condEntropy_congr_right hμ _
        (fun t : (Fin i → γ) × B => (BCFBCode.mask i t.1, t.2))
        (fun a b h => Prod.ext (BCFBCode.mask_injective i (Prod.ext_iff.mp h).1)
          (Prod.ext_iff.mp h).2)
        fun z => by simp only [pair, BCFBCode.mask_fbPre]
    rw [hinj]
    have h := condEntropy_le_condEntropy_comp hμ (fun ω => O ω i)
      (pair (fun ω => fbPre i (O ω)) Mb) (fun t : (Fin i → γ) × B => e i t.2 t.1)
    have e' : (fun t : (Fin i → γ) × B => e i t.2 t.1) ∘ pair (fun ω => fbPre i (O ω)) Mb =
        fun z => φ (enc i z.1 (fbPre i z.2)) :=
      funext fun z => (he i z.1 (fbPre i z.2)).symm
    rw [e'] at h
    exact h
  -- the second term
  have h₂ : H[fun z => v (z.2 i) | fun z => enc i z.1 (fbPre i z.2) ; μ] ≤
      H[fun ω => O ω i | pair (fun ω => degradedBCPast (i : ℕ) (O ω)) Prod.fst ; μ] := by
    have hX : H[fun z => v (z.2 i) | fun z => enc i z.1 (fbPre i z.2) ; μ] =
        ∑ a, dist μ (fun z => enc i z.1 (fbPre i z.2)) a * entropy (dist (W a) v) :=
      condEntropy_of_channel (W := fun a => dist (W a) v) id fun t b =>
        dist_fbLaw_letter_view hW i (fun t : 𝒲 × (Fin i → β) => enc i t.1 t.2) id (fun _ _ => rfl)
          v t b
    have hP : H[fun z => v (z.2 i) | pair (fun z => fbPre i z.2) Prod.fst ; μ] =
        ∑ a, dist μ (fun z => enc i z.1 (fbPre i z.2)) a * entropy (dist (W a) v) :=
      condEntropy_of_channel (W := fun a => dist (W a) v)
        (fun t : (Fin i → β) × 𝒲 => enc i t.2 t.1) fun t b =>
        dist_fbLaw_letter_view hW i (fun t : 𝒲 × (Fin i → β) => (t.2, t.1))
          (fun t => enc i t.2 t.1) (fun _ _ => rfl) v t b
    rw [hX, ← hP]
    have h := condEntropy_le_condEntropy_comp hμ (fun z : 𝒲 × (Fin n → β) => v (z.2 i))
      (pair (fun z => fbPre i z.2) Prod.fst)
      (fun t : (Fin i → β) × 𝒲 => (BCFBCode.mask i fun j => v (t.1 j), t.2))
    refine le_trans h (le_of_eq ?_)
    have e' : ((fun t : (Fin i → β) × 𝒲 => (BCFBCode.mask i fun j => v (t.1 j), t.2)) ∘
        pair (fun z => fbPre i z.2) Prod.fst) =
        pair (fun ω => degradedBCPast (i : ℕ) (O ω)) Prod.fst := by
      funext z
      refine Prod.ext ?_ rfl
      exact BCFBCode.mask_fbPre i (O z)
    rw [e']
  linarith

/-- **The single-letter bound, with the informations of the letters**, for an input `(a, b)` of
which `b` is determined by `B` and the past of `O`. -/
theorem condInfo_le_sum_cInfo {a' b' : Type*} [Fintype a'] [Fintype b']
    {W : a' × b' → β → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β) → a' × b'} (hν : IsPMF ν) (hW : IsChannel W)
    (ma : 𝒲 → A) (mb : 𝒲 → B) (hab : Function.Injective fun w => (ma w, mb w)) (v : β → γ)
    (e : ∀ k, B → (Fin k → γ) → b')
    (he : ∀ k w (z : Fin k → β), (enc k w z).2 = e k (mb w) fun i => v (z i)) :
    I[fun z => ma z.1 : fun z i => v (z.2 i) | fun z => mb z.1 ; fbLaw ν W enc n] ≤
      ∑ i : Fin n, cInfo (dist (fbLaw ν W enc n) fun z => enc i z.1 (fbPre i z.2))
        fun t => dist (W t) v := by
  classical
  have hμ : IsPMF (fbLaw ν W enc n) := fbLaw_isPMF hν hW n
  refine (condInfo_le_sum hν hW ma mb hab v Prod.snd e he).trans (le_of_eq ?_)
  refine sum_congr rfl fun i _ => ?_
  set μ := fbLaw ν W enc n
  set X : 𝒲 × (Fin n → β) → a' × b' := fun z => enc i z.1 (fbPre i z.2) with hX
  have hK : IsChannel fun t : a' × b' => dist (W t) v := fun t => (hW t).dist _
  have hq : IsPMF (dist μ X) := hμ.dist _
  have hd : dist μ (pair X fun z => v (z.2 i)) = jointOf (dist μ X) fun t => dist (W t) v := by
    funext ⟨t, d⟩
    exact dist_fbLaw_letter_view hW i (fun t : 𝒲 × (Fin i → β) => enc i t.1 t.2) id
      (fun _ _ => rfl) v t d
  rw [cInfo_eq hq hK]
  congr 1
  · refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hq hK) ?_
    have e₁ : (pair (fun z : 𝒲 × (Fin n → β) => (X z).2) fun z => v (z.2 i)) =
        (pair (fun t : (a' × b') × γ => t.1.2) Prod.snd) ∘ pair X fun z => v (z.2 i) := rfl
    rw [e₁, dist_comp_eq, hd]
  · exact condEntropy_of_channel (W := fun t => dist (W t) v) id fun t d =>
      dist_fbLaw_letter_view hW i (fun t : 𝒲 × (Fin i → β) => enc i t.1 t.2) id (fun _ _ => rfl)
        v t d

end Bound

/-! ### Codes -/

/-- **Page 18-46 of [elgamal2010].** A code for two nodes. Each encoder sees the past of what its
node receives, and each decoder knows the message of its node. -/
structure TWCCode (M₁ M₂ n : ℕ) (α₁ α₂ γ₁ γ₂ : Type*) where
  /-- The encoder of node 1. -/
  enc₁ : ∀ k, Fin M₁ → (Fin k → γ₁) → α₁
  /-- The encoder of node 2. -/
  enc₂ : ∀ k, Fin M₂ → (Fin k → γ₂) → α₂
  /-- The decoder of node 1, of the message of node 2. -/
  dec₁ : Fin M₁ → (Fin n → γ₁) → Fin M₂
  /-- The decoder of node 2, of the message of node 1. -/
  dec₂ : Fin M₂ → (Fin n → γ₂) → Fin M₁

namespace TWCCode

variable {M₁ M₂ n : ℕ} {α₁ α₂ β γ₁ γ₂ : Type*}
  (c : TWCCode M₁ M₂ n α₁ α₂ γ₁ γ₂)

/-- The two encoders, as an encoder with feedback, when the nodes receive `v₁` and `v₂` of the
output. -/
def fbEnc (v₁ : β → γ₁) (v₂ : β → γ₂) : ∀ k, Fin M₁ × Fin M₂ → (Fin k → β) → α₁ × α₂ :=
  fun k w z => (c.enc₁ k w.1 fun i => v₁ (z i), c.enc₂ k w.2 fun i => v₂ (z i))

variable [Fintype β]

/-- The joint law of the uniform messages and of the outputs. -/
def law (W : α₁ × α₂ → β → ℝ) (v₁ : β → γ₁) (v₂ : β → γ₂) :
    (Fin M₁ × Fin M₂) × (Fin n → β) → ℝ :=
  fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W (c.fbEnc v₁ v₂) n

/-- The probability of error of the decoder of node 1. -/
def err₁ (W : α₁ × α₂ → β → ℝ) (v₁ : β → γ₁) (v₂ : β → γ₂) : ℝ :=
  InfoTheory.errProb (c.law W v₁ v₂) (fun z => z.1.2) (fun z => (z.1.1, fun i => v₁ (z.2 i)))
    fun t => c.dec₁ t.1 t.2

/-- The probability of error of the decoder of node 2. -/
def err₂ (W : α₁ × α₂ → β → ℝ) (v₁ : β → γ₁) (v₂ : β → γ₂) : ℝ :=
  InfoTheory.errProb (c.law W v₁ v₂) (fun z => z.1.1) (fun z => (z.1.2, fun i => v₂ (z.2 i)))
    fun t => c.dec₂ t.1 t.2

/-- The law of the inputs at time `i`. -/
def letter (W : α₁ × α₂ → β → ℝ) (v₁ : β → γ₁) (v₂ : β → γ₂) (i : Fin n) :
    α₁ × α₂ → ℝ :=
  dist (c.law W v₁ v₂) fun z => c.fbEnc v₁ v₂ i z.1 (fbPre i z.2)

variable [Fintype α₁] [Fintype α₂] [Fintype γ₁] [Fintype γ₂] {W : α₁ × α₂ → β → ℝ} {v₁ : β → γ₁}
  {v₂ : β → γ₂}

omit [Fintype α₁] [Fintype α₂] [Fintype γ₁] [Fintype γ₂] in
lemma law_isPMF (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) : IsPMF (c.law W v₁ v₂) :=
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  fbLaw_isPMF uniformPMF_isPMF hW n

/-- The two encoders with the inputs exchanged. -/
def fbEncSwap (v₁ : β → γ₁) (v₂ : β → γ₂) : ∀ k, Fin M₁ × Fin M₂ → (Fin k → β) → α₂ × α₁ :=
  fun k w z => (c.fbEnc v₁ v₂ k w z).swap

omit [Fintype β] [Fintype α₁] [Fintype α₂] [Fintype γ₁] [Fintype γ₂] in
/-- The law does not depend on the order of the inputs. -/
lemma fbLaw_swap (k : ℕ) (t : (Fin M₁ × Fin M₂) × (Fin k → β)) :
    fbLaw (uniformPMF (Fin M₁ × Fin M₂)) (fun a : α₂ × α₁ => W a.swap) (c.fbEncSwap v₁ v₂) k t =
      fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W (c.fbEnc v₁ v₂) k t := by
  obtain ⟨w, z⟩ := t
  rw [fbLaw_eq_prod, fbLaw_eq_prod]
  simp [fbEncSwap]

omit [Fintype α₁] [Fintype α₂] [Fintype γ₁] [Fintype γ₂] in
/-- **Fano's inequality for node 2.** -/
lemma log_le_of_fano₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) [Fintype γ₂] :
    log M₁ ≤ I[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 : fun z i => v₂ (z.2 i) |
      fun z => z.1.2 ; c.law W v₁ v₂] + log 2 + c.err₂ W v₁ v₂ * log M₁ := by
  classical
  have hμ := c.law_isPMF (W := W) (v₁ := v₁) (v₂ := v₂) hW h₁ h₂
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hd : dist (c.law W v₁ v₂) Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hW n
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hH : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 | fun z => z.1.2 ; c.law W v₁ v₂] =
      log M₁ := by
    rw [condEntropy_eq_sub hμ]
    have e : H[pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2) (fun z => z.1.1) ;
        c.law W v₁ v₂] = H[Prod.fst ; c.law W v₁ v₂] :=
      entropyRV_eq_of_injective _ Prod.swap Prod.swap_injective fun _ => rfl
    have hu : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.2) = uniformPMF (Fin M₂) := by
      have := MACCode.dist_uniformPMF_prod_snd (M₂ := M₂) h₁ id
      rw [dist_id] at this
      exact this
    have e₂ : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 ; c.law W v₁ v₂] = log M₂ := by
      have ee : (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2) =
          (fun w : Fin M₁ × Fin M₂ => w.2) ∘ Prod.fst := rfl
      rw [entropyRV, ee, dist_comp_eq, hd, hu, entropy_uniformPMF, Fintype.card_fin]
    rw [e, e₂, entropyRV, hd, entropy_uniformPMF, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    push_cast
    rw [log_mul hM₁ hM₂]
    ring
  have hF := fano_weak hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1)
    (fun z => (z.1.2, fun i => v₂ (z.2 i))) fun t => c.dec₂ t.1 t.2
  rw [Fintype.card_fin] at hF
  have hc : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 |
      pair (fun z i => v₂ (z.2 i)) (fun z => z.1.2) ; c.law W v₁ v₂] =
      H[fun z => z.1.1 | fun z => (z.1.2, fun i => v₂ (z.2 i)) ; c.law W v₁ v₂] :=
    condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have hI : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 : fun z i => v₂ (z.2 i) |
      fun z => z.1.2 ; c.law W v₁ v₂] = H[fun z => z.1.1 | fun z => z.1.2 ; c.law W v₁ v₂] -
      H[fun z => z.1.1 | pair (fun z i => v₂ (z.2 i)) (fun z => z.1.2) ; c.law W v₁ v₂] := rfl
  have he : InfoTheory.errProb (c.law W v₁ v₂) (fun z => z.1.1)
      (fun z => (z.1.2, fun i => v₂ (z.2 i))) (fun t => c.dec₂ t.1 t.2) = c.err₂ W v₁ v₂ := rfl
  rw [he] at hF
  rw [hI, hH, hc]
  linarith

omit [Fintype α₁] [Fintype α₂] [Fintype γ₁] [Fintype γ₂] in
/-- **Fano's inequality for node 1.** -/
lemma log_le_of_fano₁ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) [Fintype γ₁] :
    log M₂ ≤ I[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 : fun z i => v₁ (z.2 i) |
      fun z => z.1.1 ; c.law W v₁ v₂] + log 2 + c.err₁ W v₁ v₂ * log M₂ := by
  classical
  have hμ := c.law_isPMF (W := W) (v₁ := v₁) (v₂ := v₂) hW h₁ h₂
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hd : dist (c.law W v₁ v₂) Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hW n
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hH : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 | fun z => z.1.1 ; c.law W v₁ v₂] =
      log M₂ := by
    rw [condEntropy_eq_sub hμ]
    have e : H[pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1) (fun z => z.1.2) ;
        c.law W v₁ v₂] = H[Prod.fst ; c.law W v₁ v₂] := rfl
    have hu : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.1) = uniformPMF (Fin M₁) := by
      have := MACCode.dist_uniformPMF_prod_fst (M₁ := M₁) h₂ id
      rw [dist_id] at this
      exact this
    have e₂ : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 ; c.law W v₁ v₂] = log M₁ := by
      have ee : (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1) =
          (fun w : Fin M₁ × Fin M₂ => w.1) ∘ Prod.fst := rfl
      rw [entropyRV, ee, dist_comp_eq, hd, hu, entropy_uniformPMF, Fintype.card_fin]
    rw [e, e₂, entropyRV, hd, entropy_uniformPMF, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    push_cast
    rw [log_mul hM₁ hM₂]
    ring
  have hF := fano_weak hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2)
    (fun z => (z.1.1, fun i => v₁ (z.2 i))) fun t => c.dec₁ t.1 t.2
  rw [Fintype.card_fin] at hF
  have hc : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 |
      pair (fun z i => v₁ (z.2 i)) (fun z => z.1.1) ; c.law W v₁ v₂] =
      H[fun z => z.1.2 | fun z => (z.1.1, fun i => v₁ (z.2 i)) ; c.law W v₁ v₂] :=
    condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have hI : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 : fun z i => v₁ (z.2 i) |
      fun z => z.1.1 ; c.law W v₁ v₂] = H[fun z => z.1.2 | fun z => z.1.1 ; c.law W v₁ v₂] -
      H[fun z => z.1.2 | pair (fun z i => v₁ (z.2 i)) (fun z => z.1.1) ; c.law W v₁ v₂] := rfl
  have he : InfoTheory.errProb (c.law W v₁ v₂) (fun z => z.1.2)
      (fun z => (z.1.1, fun i => v₁ (z.2 i))) (fun t => c.dec₁ t.1 t.2) = c.err₁ W v₁ v₂ := rfl
  rw [he] at hF
  rw [hI, hH, hc]
  linarith

omit [Fintype γ₁] in
/-- **The bound of node 2, for one code**: `log M₁ ≤ ∑ᵢ I(X₁ᵢ; O₂ᵢ | X₂ᵢ) + log 2 + P₂ log M₁`. -/
theorem log_le_sum₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₁ ≤ ∑ i : Fin n, cInfo (c.letter W v₁ v₂ i) (fun t => dist (W t) v₂) + log 2 +
      c.err₂ W v₁ v₂ * log M₁ := by
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  have hb := condInfo_le_sum_cInfo (ν := uniformPMF (Fin M₁ × Fin M₂)) (n := n)
    (enc := c.fbEnc v₁ v₂) uniformPMF_isPMF hW (fun w => w.1) (fun w => w.2)
    Function.injective_id v₂ (fun k b z => c.enc₂ k b z) (fun _ _ _ => rfl)
  have hf := c.log_le_of_fano₂ (W := W) (v₁ := v₁) (v₂ := v₂) hW h₁ h₂
  have hb' : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 : fun z i => v₂ (z.2 i) |
      fun z => z.1.2 ; c.law W v₁ v₂] ≤
      ∑ i : Fin n, cInfo (c.letter W v₁ v₂ i) fun t => dist (W t) v₂ := hb
  linarith

/-- The law of the inputs at time `i`, with the inputs exchanged. -/
def letterSwap (W : α₁ × α₂ → β → ℝ) (v₁ : β → γ₁) (v₂ : β → γ₂) (i : Fin n) : α₂ × α₁ → ℝ :=
  fun a => c.letter W v₁ v₂ i a.swap

omit [Fintype γ₂] in
/-- **The bound of node 1, for one code**: `log M₂ ≤ ∑ᵢ I(X₂ᵢ; O₁ᵢ | X₁ᵢ) + log 2 + P₁ log M₂`. -/
theorem log_le_sum₁ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₂ ≤ ∑ i : Fin n, cInfo (c.letterSwap W v₁ v₂ i) (fun t => dist (W t.swap) v₁) + log 2 +
      c.err₁ W v₁ v₂ * log M₂ := by
  classical
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  have hW' : IsChannel fun a : α₂ × α₁ => W a.swap := fun a => hW _
  have hlaw : fbLaw (uniformPMF (Fin M₁ × Fin M₂)) (fun a : α₂ × α₁ => W a.swap)
      (c.fbEncSwap v₁ v₂) n = c.law W v₁ v₂ := funext fun t => c.fbLaw_swap n t
  have hb := condInfo_le_sum_cInfo (ν := uniformPMF (Fin M₁ × Fin M₂)) (n := n)
    (W := fun a : α₂ × α₁ => W a.swap) (enc := c.fbEncSwap v₁ v₂) uniformPMF_isPMF hW'
    (fun w => w.2) (fun w => w.1) (fun a b h => Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp
      h).1)
    v₁ (fun k b z => c.enc₁ k b z) (fun _ _ _ => rfl)
  rw [hlaw] at hb
  have hf := c.log_le_of_fano₁ (W := W) (v₁ := v₁) (v₂ := v₂) hW h₁ h₂
  have hl : ∀ i : Fin n, dist (c.law W v₁ v₂) (fun z => c.fbEncSwap v₁ v₂ i z.1 (fbPre i z.2)) =
      c.letterSwap W v₁ v₂ i := by
    intro i
    funext a
    have := dist_comp_of_injective (c.law W v₁ v₂)
      (fun z => c.fbEnc v₁ v₂ i z.1 (fbPre i z.2)) Prod.swap_injective a.swap
    simpa [letterSwap, letter, fbEncSwap, Function.comp_def] using this
  simp_rw [hl] at hb
  linarith

/-- **The outer bound for one code.** The input law is the average of the laws of the letters. -/
theorem exists_input_law (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (hn : 0 < n) :
    ∃ p : α₁ × α₂ → ℝ, IsPMF p ∧
      log M₁ ≤ n * cInfo p (fun t => dist (W t) v₂) + log 2 + c.err₂ W v₁ v₂ * log M₁ ∧
      log M₂ ≤ n * cInfo (fun a : α₂ × α₁ => p a.swap) (fun t => dist (W t.swap) v₁) + log 2 +
        c.err₁ W v₁ v₂ * log M₂ := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hμ := c.law_isPMF (W := W) (v₁ := v₁) (v₂ := v₂) hW h₁ h₂
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : IsPMF (uniformPMF (Fin n)) := uniformPMF_isPMF
  have hwv : ∀ i : Fin n, uniformPMF (Fin n) i = 1 / n := fun i => by simp [uniformPMF]
  have hq : ∀ i : Fin n, IsPMF (c.letter W v₁ v₂ i) := fun i => hμ.dist _
  have hq' : ∀ i : Fin n, IsPMF (c.letterSwap W v₁ v₂ i) := fun i =>
    ⟨fun a => (hq i).nonneg _, by
      rw [← (hq i).sum_eq_one]
      exact Equiv.sum_comp (Equiv.prodComm α₂ α₁) (c.letter W v₁ v₂ i)⟩
  let p : α₁ × α₂ → ℝ := fun a => ∑ i, uniformPMF (Fin n) i * c.letter W v₁ v₂ i a
  have hp : IsPMF p := by
    refine ⟨fun a => sum_nonneg fun i _ => mul_nonneg (hw.nonneg i) ((hq i).nonneg a), ?_⟩
    simp only [p]
    rw [sum_comm]
    simp_rw [← mul_sum, (hq _).sum_eq_one, mul_one, hw.sum_eq_one]
  have hK₂ : IsChannel fun t : α₁ × α₂ => dist (W t) v₂ := fun t => (hW t).dist _
  have hK₁ : IsChannel fun t : α₂ × α₁ => dist (W t.swap) v₁ := fun t => (hW _).dist _
  have hsum : ∀ g : Fin n → ℝ, ∑ i, g i = n * ∑ i, uniformPMF (Fin n) i * g i := by
    intro g
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hwv]
    field_simp
  refine ⟨p, hp, ?_, ?_⟩
  · have hb := c.log_le_sum₂ (W := W) (v₁ := v₁) (v₂ := v₂) hW h₁ h₂
    have hc := sum_cInfo_le hw hq hK₂
    rw [hsum] at hb
    have := mul_le_mul_of_nonneg_left hc hn'.le
    linarith
  · have hb := c.log_le_sum₁ (W := W) (v₁ := v₁) (v₂ := v₂) hW h₁ h₂
    have hc := sum_cInfo_le hw hq' hK₁
    rw [hsum] at hb
    have := mul_le_mul_of_nonneg_left hc hn'.le
    have e : (fun a : α₂ × α₁ => ∑ i, uniformPMF (Fin n) i * c.letterSwap W v₁ v₂ i a) =
        fun a => p a.swap := rfl
    rw [e] at this
    linarith

end TWCCode

/-! ### The two-way channel -/

section TWC

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
  {W : α₁ × α₂ → β₁ × β₂ → ℝ}

/-- **Page 18-46 of [elgamal2010].** The probability of error for the two-way channel. -/
def TWCCode.errProb {M₁ M₂ n : ℕ} (c : TWCCode M₁ M₂ n α₁ α₂ β₁ β₂) (W : α₁ × α₂ → β₁ × β₂ → ℝ) :
    ℝ :=
  c.err₁ W Prod.fst Prod.snd + c.err₂ W Prod.fst Prod.snd

/-- **Page 18-46 of [elgamal2010].** A rate pair, in bits, is achievable for the two-way channel. We
use the sum of the two probabilities of error, which tends to zero if and only if the probability
that a node makes an error does. -/
def IsAchievableTWC (W : α₁ × α₂ → β₁ × β₂ → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, TWCCode (2 ^ ⌈(n : ℝ) * R₁⌉₊) (2 ^ ⌈(n : ℝ) * R₂⌉₊) n α₁ α₂ β₁ β₂,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Page 18-46 of [elgamal2010].** The capacity region of the two-way channel. -/
def twcCapacityRegion (W : α₁ × α₂ → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableTWC W R.1 R.2}

/-- `I(X₁; Y₂ | X₂)`. -/
def twcInfo₁ (p : α₁ × α₂ → ℝ) (W : α₁ × α₂ → β₁ × β₂ → ℝ) : ℝ := cInfo p (bcMarg₂ W)

/-- `I(X₂; Y₁ | X₁)`. -/
def twcInfo₂ (p : α₁ × α₂ → ℝ) (W : α₁ × α₂ → β₁ × β₂ → ℝ) : ℝ :=
  cInfo (fun a : α₂ × α₁ => p a.swap) fun t => bcMarg₁ W t.swap

/-- The correction to the rates of a sequence of codes tends to zero. -/
lemma tendsto_rate_eps {R₁ R₂ : ℝ} {P : ℕ → ℝ} (hP : Tendsto P atTop (𝓝 0)) (hP0 : ∀ n, 0 ≤ P n) :
    Tendsto (fun n : ℕ => (1 + P n * ((⌈(n : ℝ) * R₁⌉₊ : ℝ) + ⌈(n : ℝ) * R₂⌉₊)) / n) atTop
      (𝓝 0) := by
  set K := |R₁| + |R₂| + 2
  have hup : Tendsto (fun n : ℕ => 1 / (n : ℝ) + P n * K) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add (hP.mul_const K)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => div_nonneg (add_nonneg zero_le_one
      (mul_nonneg (hP0 n) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Nat.cast_nonneg
        n))
    ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hceil : ∀ x : ℝ, (⌈x⌉₊ : ℝ) ≤ |x| + 1 := fun x => by
    have h1 : (⌈x⌉₊ : ℝ) ≤ ⌈|x|⌉₊ := by exact_mod_cast Nat.ceil_mono (le_abs_self x)
    linarith [Nat.ceil_lt_add_one (abs_nonneg x)]
  have h1 := hceil ((n : ℝ) * R₁)
  have h2 := hceil ((n : ℝ) * R₂)
  rw [abs_mul, Nat.abs_cast] at h1 h2
  have hab : (⌈(n : ℝ) * R₁⌉₊ : ℝ) + ⌈(n : ℝ) * R₂⌉₊ ≤ n * K := by
    simp only [K]
    nlinarith
  rw [add_div, mul_div_assoc]
  gcongr
  · exact hP0 n
  · rw [div_le_iff₀ hn']
    linarith

/-- **Shannon's outer bound, page 18-48 of [elgamal2010]**, in bits. -/
def twcOuterRegion (W : α₁ × α₂ → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ p : α₁ × α₂ → ℝ, IsPMF p ∧ R.1 ≤ twcInfo₁ p W / log 2 ∧ R.2 ≤ twcInfo₂ p W / log 2}

omit [Fintype α₁] [Fintype α₂] in
/-- The marginals as laws of functions of the output. -/
lemma dist_snd_eq_bcMarg₂ (a : α₁ × α₂) : dist (W a) Prod.snd = bcMarg₂ W a := by
  funext y
  rw [dist_snd]
  rfl

omit [Fintype α₁] [Fintype α₂] in
lemma dist_fst_eq_bcMarg₁ (a : α₁ × α₂) : dist (W a) Prod.fst = bcMarg₁ W a := by
  funext y
  rw [dist_fst]
  rfl

/-- **Shannon's outer bound, page 18-48 of [elgamal2010].** Every achievable rate pair is in the
closure of the region. -/
theorem IsAchievableTWC.mem_closure_twcOuterRegion (hW : IsChannel W)
    {R₁ R₂ : ℝ} (h : IsAchievableTWC W R₁ R₂) : (R₁, R₂) ∈ closure (twcOuterRegion W) := by
  obtain ⟨c, hc⟩ := h
  set a₁ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₁⌉₊ with ha₁
  set a₂ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₂⌉₊ with ha₂
  set P : ℕ → ℝ := fun n => (c n).errProb W with hPdef
  set ε : ℕ → ℝ := fun n => (1 + P n * ((a₁ n : ℝ) + a₂ n)) / n with hεdef
  have hpos₁ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := fun n => by positivity
  have hpos₂ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := fun n => by positivity
  have he₁ : ∀ n, 0 ≤ (c n).err₁ W Prod.fst Prod.snd := fun n =>
    errProb_nonneg ((c n).law_isPMF hW (hpos₁ n) (hpos₂ n)) _ _ _
  have he₂ : ∀ n, 0 ≤ (c n).err₂ W Prod.fst Prod.snd := fun n =>
    errProb_nonneg ((c n).law_isPMF hW (hpos₁ n) (hpos₂ n)) _ _ _
  have hP₁ : ∀ n, (c n).err₁ W Prod.fst Prod.snd ≤ P n := fun n => by
    simp only [hPdef, TWCCode.errProb]
    linarith [he₂ n]
  have hP₂ : ∀ n, (c n).err₂ W Prod.fst Prod.snd ≤ P n := fun n => by
    simp only [hPdef, TWCCode.errProb]
    linarith [he₁ n]
  have hP0 : ∀ n, 0 ≤ P n := fun n => (he₁ n).trans (hP₁ n)
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg zero_le_one
    (mul_nonneg (hP0 n) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Nat.cast_nonneg n)
  have hL := log_two_pos'
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ twcOuterRegion W := by
    intro n hn
    obtain ⟨p, hp, b₁, b₂⟩ := (c n).exists_input_law (W := W) (v₁ := Prod.fst) (v₂ := Prod.snd) hW
      (hpos₁ n) (hpos₂ n) hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨p, hp, ?_, ?_⟩
    · have hm : (fun t => dist (W t) Prod.snd) = bcMarg₂ W := funext dist_snd_eq_bcMarg₂
      rw [hm] at b₁
      have h₃ := degradedBC_rate_le (b := a₂ n) (S := n * twcInfo₁ p W) (R := R₁) hn (hP0 n) (hP₂ n)
        (by exact_mod_cast b₁)
      refine h₃.trans (le_of_eq ?_)
      field_simp
    · have hm : (fun t : α₂ × α₁ => dist (W t.swap) Prod.fst) = fun t => bcMarg₁ W t.swap :=
        funext fun t => dist_fst_eq_bcMarg₁ t.swap
      rw [hm] at b₂
      have h₃ := degradedBC_rate_le (b := a₁ n) (S := n * twcInfo₂ p W) (R := R₂) hn (hP0 n) (hP₁ n)
        (by exact_mod_cast b₂)
      have e : ε n = (1 + P n * ((a₂ n : ℝ) + a₁ n)) / n := by
        simp only [hεdef, add_comm]
      rw [e]
      refine h₃.trans (le_of_eq ?_)
      field_simp
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_rate_eps hc hP0
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

end TWC

end InfoTheory
