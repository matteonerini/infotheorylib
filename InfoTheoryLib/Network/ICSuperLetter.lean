/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.ICStrong

/-!
# Compound coding and super-letters for the interference channel

The simultaneous decoding inner bound of Lecture 6 of El Gamal and Kim has each receiver decode both
messages, so a single codebook must be good for the multiple access channels `p(y₁ | x₁, x₂)` and
`p(y₂ | x₁, x₂)` at the same time, and a time-sharing variable `Q` enters through the minimum of two
averages. The notes use coded time sharing. We get the same effect from the random coding bound for
a product input distribution, used on super-letters of `m` channel uses: the letters of a
super-letter follow a fixed pattern of values of `Q`, in the right proportions.

## Main definitions

* `indexedPMF r`: the product `∏ⱼ rⱼ(xⱼ)` of pmfs.
* `ICCode.err₁`, `ICCode.err₂`: the probabilities of error at each receiver, for a channel to that
  receiver.
* `icRandomBound p₁ p₂ V M₁ M₂ n ε`: the random coding bound for the channel `V`.

## Main statements

* `exists_icCode_err_le`: **compound random coding**, a codebook good for both receivers.
* `mutualInfoOf_indexedExt_eq`: `I(Xⁿ; Yⁿ) = ∑ⱼ I(Xⱼ; Yⱼ)` for independent inputs.
* `macInfo₁_macExt_indexedPMF`, `macInfo₂_macExt_indexedPMF`, `macInfo₁₂_macExt_indexedPMF`: the
  informations of a super-letter with independent letters.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]

/-! ### The error at each receiver -/

namespace ICCode

variable {M₁ M₂ n : ℕ} (c : ICCode M₁ M₂ n α₁ α₂ β₁ β₂)

open Classical in
/-- The probability of error `P{M̂₁ ≠ M₁}` at receiver 1, for the channel `V` to that receiver. -/
def err₁ (V : α₁ × α₂ → β₁ → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ y, if c.dec₁ y ≠ i then
    channelExt V n (zipSeq (c.enc₁ i) (c.enc₂ j)) y else 0) / (M₁ * M₂)

open Classical in
/-- The probability of error `P{M̂₂ ≠ M₂}` at receiver 2, for the channel `V` to that receiver. -/
def err₂ (V : α₁ × α₂ → β₂ → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ y, if c.dec₂ y ≠ j then
    channelExt V n (zipSeq (c.enc₁ i) (c.enc₂ j)) y else 0) / (M₁ * M₂)

omit [Fintype α₁] [Fintype α₂] in
lemma errProb₁_eq_err₁ (W : α₁ × α₂ → β₁ × β₂ → ℝ) : c.errProb₁ W = c.err₁ (bcMarg₁ W) :=
  c.errProb₁_eq

omit [Fintype α₁] [Fintype α₂] in
lemma errProb₂_eq_err₂ (W : α₁ × α₂ → β₁ × β₂ → ℝ) : c.errProb₂ W = c.err₂ (bcMarg₂ W) :=
  c.errProb₂_eq

end ICCode

/-! ### Compound random coding -/

section Compound

variable {β : Type*} [Fintype β] {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ}

/-- The random coding bound of the multiple access channel `V` with inputs `p₁`, `p₂`. -/
def icRandomBound (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (V : α₁ × α₂ → β → ℝ) (M₁ M₂ n : ℕ) (ε : ℝ) : ℝ :=
  macAtypProb p₁ p₂ V n ε + (M₁ - 1) * exp (-(n * (macInfo₁ p₁ p₂ V - 3 * ε))) +
    (M₂ - 1) * exp (-(n * (macInfo₂ p₁ p₂ V - 3 * ε))) +
    (M₁ - 1) * (M₂ - 1) * exp (-(n * (macInfo₁₂ p₁ p₂ V - 3 * ε)))

omit [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂] [Fintype β] in
/-- An error on the first message is an error on the pair. -/
lemma ite_fst_ne_le {A B : Type*} (d : A × B) (i : A) (j : B) {c : ℝ} (hc : 0 ≤ c)
    [Decidable (d.1 ≠ i)] [Decidable (d ≠ (i, j))] :
    (if d.1 ≠ i then c else 0) ≤ if d ≠ (i, j) then c else 0 := by
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact absurd (by rw [not_not.1 h₂]) h₁
  · exact hc
  · exact le_rfl

omit [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂] [Fintype β] in
/-- An error on the second message is an error on the pair. -/
lemma ite_snd_ne_le {A B : Type*} (d : A × B) (i : A) (j : B) {c : ℝ} (hc : 0 ≤ c)
    [Decidable (d.2 ≠ j)] [Decidable (d ≠ (i, j))] :
    (if d.2 ≠ j then c else 0) ≤ if d ≠ (i, j) then c else 0 := by
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact absurd (by rw [not_not.1 h₂]) h₁
  · exact hc
  · exact le_rfl

/-- Averaged over the random codebooks, the average probability of error of joint typicality
decoding is at most the random coding bound. -/
lemma sum_codebook_avgErrProb_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) {V : α₁ × α₂ → β → ℝ}
    (hV : IsChannel V) {M₁ M₂ : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (n : ℕ) (ε : ℝ)
    (d : Fin M₁ × Fin M₂) :
    ∑ C : (Fin M₁ → Fin n → α₁) × (Fin M₂ → Fin n → α₂),
      prodDist (iidPMF (iidPMF p₁ n) M₁) (iidPMF (iidPMF p₂ n) M₂) C *
        (macTypicalCode (macTypicalSet p₁ p₂ V n ε) C.1 C.2 d).avgErrProb V ≤
      icRandomBound p₁ p₂ V M₁ M₂ n ε := by
  set μ := prodDist (iidPMF (iidPMF p₁ n) M₁) (iidPMF (iidPMF p₂ n) M₂)
  set code : (Fin M₁ → Fin n → α₁) × (Fin M₂ → Fin n → α₂) → MACCode M₁ M₂ n α₁ α₂ β :=
    fun C => macTypicalCode (macTypicalSet p₁ p₂ V n ε) C.1 C.2 d
  set U := icRandomBound p₁ p₂ V M₁ M₂ n ε
  have hM : (0 : ℝ) < M₁ * M₂ := by positivity
  have hb : ∀ i j, ∑ C, μ C * (code C).condErrProb V i j ≤ U := fun i j => by
    rw [Fintype.sum_prod_type]
    exact sum_codebook_macCondErrProb_le hp₁ hp₂ hV ε d i j
  have e : ∑ C, μ C * (code C).avgErrProb V =
      (∑ i, ∑ j, ∑ C, μ C * (code C).condErrProb V i j) / (M₁ * M₂) := by
    simp only [MACCode.avgErrProb, mul_div_assoc', ← sum_div, mul_sum]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_comm
  rw [e, div_le_iff₀ hM]
  calc ∑ i, ∑ j, ∑ C, μ C * (code C).condErrProb V i j ≤ ∑ _i : Fin M₁, ∑ _j : Fin M₂, U :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hb i j
    _ = U * (M₁ * M₂) := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Lecture 6 of [elgamal2010], page 6-7.** Compound random coding: for two multiple access
channels with the same inputs, some codebook has a total probability of error at the two receivers
at most the sum of the two random coding bounds. Each receiver decodes both messages by joint
typicality, for its own channel, and keeps its own message. -/
theorem exists_icCode_err_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) {V₁ : α₁ × α₂ → β₁ → ℝ}
    {V₂ : α₁ × α₂ → β₂ → ℝ} (hV₁ : IsChannel V₁) (hV₂ : IsChannel V₂) {M₁ M₂ : ℕ} (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) (n : ℕ) (ε : ℝ) :
    ∃ c : ICCode M₁ M₂ n α₁ α₂ β₁ β₂, c.err₁ V₁ + c.err₂ V₂ ≤
      icRandomBound p₁ p₂ V₁ M₁ M₂ n ε + icRandomBound p₁ p₂ V₂ M₁ M₂ n ε := by
  classical
  set μ := prodDist (iidPMF (iidPMF p₁ n) M₁) (iidPMF (iidPMF p₂ n) M₂)
  have hμ : IsPMF μ := (iidPMF_isPMF (iidPMF_isPMF hp₁ n) M₁).prodDist
    (iidPMF_isPMF (iidPMF_isPMF hp₂ n) M₂)
  set d : Fin M₁ × Fin M₂ := (⟨0, h₁⟩, ⟨0, h₂⟩)
  set c₁ := fun C : (Fin M₁ → Fin n → α₁) × (Fin M₂ → Fin n → α₂) =>
    macTypicalCode (macTypicalSet p₁ p₂ V₁ n ε) C.1 C.2 d
  set c₂ := fun C : (Fin M₁ → Fin n → α₁) × (Fin M₂ → Fin n → α₂) =>
    macTypicalCode (macTypicalSet p₁ p₂ V₂ n ε) C.1 C.2 d
  have h : ∑ C, μ C * ((c₁ C).avgErrProb V₁ + (c₂ C).avgErrProb V₂) ≤
      icRandomBound p₁ p₂ V₁ M₁ M₂ n ε + icRandomBound p₁ p₂ V₂ M₁ M₂ n ε := by
    simp only [mul_add, sum_add_distrib]
    exact add_le_add (sum_codebook_avgErrProb_le hp₁ hp₂ hV₁ h₁ h₂ n ε d)
      (sum_codebook_avgErrProb_le hp₁ hp₂ hV₂ h₁ h₂ n ε d)
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hμ h
  refine ⟨⟨C.1, C.2, fun y => ((c₁ C).dec y).1, fun y => ((c₂ C).dec y).2⟩, le_trans ?_ hC⟩
  refine add_le_add ?_ ?_
  · refine div_le_div_of_nonneg_right
      (sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun y _ => ?_) (by positivity)
    exact ite_fst_ne_le _ i j (channelExt_nonneg hV₁ (zipSeq (C.1 i) (C.2 j)) y)
  · refine div_le_div_of_nonneg_right
      (sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun y _ => ?_) (by positivity)
    exact ite_snd_ne_le _ i j (channelExt_nonneg hV₂ (zipSeq (C.1 i) (C.2 j)) y)

end Compound

/-! ### Independent letters -/

section Additive

variable {α β : Type*} [Fintype α] [Fintype β] {m : ℕ}

/-- The product `∏ⱼ rⱼ(xⱼ)` of pmfs, the law of independent letters. -/
def indexedPMF (r : Fin m → α → ℝ) (x : Fin m → α) : ℝ := ∏ j, r j (x j)

lemma indexedPMF_isPMF {r : Fin m → α → ℝ} (hr : ∀ j, IsPMF (r j)) : IsPMF (indexedPMF r) := by
  classical
  refine ⟨fun x => prod_nonneg fun j _ => (hr j).nonneg _, ?_⟩
  have h := Fintype.prod_sum fun (j : Fin m) (a : α) => r j a
  simp only [(hr _).sum_eq_one, prod_const_one] at h
  exact h.symm

/-- `∑_{xⁿ} ∏ⱼ rⱼ(xⱼ) ∑ⱼ fⱼ(xⱼ) = ∑ⱼ E fⱼ(Xⱼ)`. -/
lemma sum_indexedPMF_mul_sum {r : Fin m → α → ℝ} (hr : ∀ j, IsPMF (r j)) (f : Fin m → α → ℝ) :
    ∑ x, indexedPMF r x * ∑ j, f j (x j) = ∑ j, ∑ a, r j a * f j a := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_prod_mul_apply (fun k => (hr k).sum_eq_one) j (f j)

/-- **Lecture 6 of [elgamal2010], page 6-9.** For independent letters and a memoryless channel,
`I(Xⁿ; Yⁿ) = ∑ⱼ I(Xⱼ; Yⱼ)`. -/
theorem mutualInfoOf_indexedExt_eq {r : Fin m → α → ℝ} (hr : ∀ j, IsPMF (r j))
    {V : Fin m → α → β → ℝ} (hV : ∀ j, IsChannel (V j)) :
    mutualInfoOf (indexedPMF r) (indexedExt V) = ∑ j, mutualInfoOf (r j) (V j) := by
  classical
  have hout : outDist (indexedPMF r) (indexedExt V) = fun y => ∏ j, outDist (r j) (V j) (y j) := by
    funext y
    simp only [outDist, indexedPMF, indexedExt, ← prod_mul_distrib]
    exact (Fintype.prod_sum fun j a => r j a * V j a (y j)).symm
  have hent : ∀ x, entropy (indexedExt V x) = ∑ j, entropy (V j (x j)) := fun x =>
    entropy_prod_pmf (p := fun j => V j (x j)) fun j => hV j (x j)
  rw [mutualInfoOf_eq (indexedPMF_isPMF hr) (indexedExt_isChannel hV), hout,
    entropy_prod_pmf fun j => outDist_isPMF (hr j) (hV j)]
  simp only [hent, sum_indexedPMF_mul_sum hr fun j a => entropy (V j a),
    mutualInfoOf_eq (hr _) (hV _), sum_sub_distrib]

variable {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂] {r₁ : Fin m → α₁ → ℝ} {r₂ : Fin m → α₂ → ℝ}
  {V : α₁ × α₂ → β → ℝ}

/-- **Lecture 6 of [elgamal2010].** For a super-letter with independent letters,
`I(X₁ᵐ; Yᵐ | X₂ᵐ) = ∑ⱼ I(X₁ⱼ; Yⱼ | X₂ⱼ)`. -/
theorem macInfo₁_macExt_indexedPMF (hr₁ : ∀ j, IsPMF (r₁ j)) (hr₂ : ∀ j, IsPMF (r₂ j))
    (hV : IsChannel V) :
    macInfo₁ (indexedPMF r₁) (indexedPMF r₂) (macExt V m) =
      ∑ j, macInfo₁ (r₁ j) (r₂ j) V := by
  rw [macInfo₁_eq_sum (indexedPMF_isPMF hr₁) (indexedPMF_isPMF hr₂) (macExt_isChannel hV m)]
  have key : ∀ x₂ : Fin m → α₂, mutualInfoOf (indexedPMF r₁) (fun a => macExt V m (a, x₂)) =
      ∑ j, mutualInfoOf (r₁ j) (fun a => V (a, x₂ j)) := fun x₂ =>
    mutualInfoOf_indexedExt_eq hr₁ (V := fun j a => V (a, x₂ j)) fun j a => hV (a, x₂ j)
  simp only [key]
  rw [sum_indexedPMF_mul_sum hr₂ fun j b => mutualInfoOf (r₁ j) (fun a => V (a, b))]
  exact sum_congr rfl fun j _ => (macInfo₁_eq_sum (hr₁ j) (hr₂ j) hV).symm

/-- **Lecture 6 of [elgamal2010].** For a super-letter with independent letters,
`I(X₂ᵐ; Yᵐ | X₁ᵐ) = ∑ⱼ I(X₂ⱼ; Yⱼ | X₁ⱼ)`. -/
theorem macInfo₂_macExt_indexedPMF (hr₁ : ∀ j, IsPMF (r₁ j)) (hr₂ : ∀ j, IsPMF (r₂ j))
    (hV : IsChannel V) :
    macInfo₂ (indexedPMF r₁) (indexedPMF r₂) (macExt V m) =
      ∑ j, macInfo₂ (r₁ j) (r₂ j) V := by
  rw [macInfo₂_eq_sum (indexedPMF_isPMF hr₁) (indexedPMF_isPMF hr₂) (macExt_isChannel hV m)]
  have key : ∀ x₁ : Fin m → α₁, mutualInfoOf (indexedPMF r₂) (fun b => macExt V m (x₁, b)) =
      ∑ j, mutualInfoOf (r₂ j) (fun b => V (x₁ j, b)) := fun x₁ =>
    mutualInfoOf_indexedExt_eq hr₂ (V := fun j b => V (x₁ j, b)) fun j b => hV (x₁ j, b)
  simp only [key]
  rw [sum_indexedPMF_mul_sum hr₁ fun j a => mutualInfoOf (r₂ j) (fun b => V (a, b))]
  exact sum_congr rfl fun j _ => (macInfo₂_eq_sum (hr₁ j) (hr₂ j) hV).symm

omit [Fintype β] [Fintype α₁] in
/-- The channel from `X₁ᵐ` through a super-letter is memoryless, for independent letters of
`X₂ᵐ`. -/
lemma macChannel₁_macExt_indexedPMF :
    macChannel₁ (macExt V m) (indexedPMF r₂) = indexedExt fun j => macChannel₁ V (r₂ j) := by
  classical
  funext a y
  simp only [macChannel₁, outDist, indexedPMF, macExt, channelExt, indexedExt, zipSeq,
    ← prod_mul_distrib]
  exact (Fintype.prod_sum fun j b => r₂ j b * V (a j, b) (y j)).symm

/-- `I(X₁, X₂; Y) = I(X₁; Y) + I(X₂; Y | X₁)` for independent inputs. -/
lemma macInfo₁₂_eq_mutualInfoOf_add {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hV : IsChannel V) :
    macInfo₁₂ p₁ p₂ V = mutualInfoOf p₁ (macChannel₁ V p₂) + macInfo₂ p₁ p₂ V := by
  rw [macInfo₁₂_eq_add₂ hp₁ hp₂ hV, mutualInfoOf_macChannel₁ hp₂ hV,
    mutualInfo_comm (macJoint_isPMF hp₁ hp₂ hV)]

/-- **Lecture 6 of [elgamal2010].** For a super-letter with independent letters,
`I(X₁ᵐ, X₂ᵐ; Yᵐ) = ∑ⱼ I(X₁ⱼ, X₂ⱼ; Yⱼ)`. -/
theorem macInfo₁₂_macExt_indexedPMF (hr₁ : ∀ j, IsPMF (r₁ j)) (hr₂ : ∀ j, IsPMF (r₂ j))
    (hV : IsChannel V) :
    macInfo₁₂ (indexedPMF r₁) (indexedPMF r₂) (macExt V m) =
      ∑ j, macInfo₁₂ (r₁ j) (r₂ j) V := by
  rw [macInfo₁₂_eq_mutualInfoOf_add (indexedPMF_isPMF hr₁) (indexedPMF_isPMF hr₂)
      (macExt_isChannel hV m), macChannel₁_macExt_indexedPMF,
    mutualInfoOf_indexedExt_eq hr₁ fun j => macChannel₁_isChannel (hr₂ j) hV,
    macInfo₂_macExt_indexedPMF hr₁ hr₂ hV, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => (macInfo₁₂_eq_mutualInfoOf_add (hr₁ j) (hr₂ j) hV).symm

end Additive

end InfoTheory
