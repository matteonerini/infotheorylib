/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACBits
public import InfoTheoryLib.Network.Broadcast

/-!
# Interference channels

A 2-user pair discrete memoryless interference channel (DM-IC) is a channel
`p(y₁, y₂ | x₁, x₂)`, which we write `W : 𝒳₁ × 𝒳₂ → 𝒴₁ × 𝒴₂ → ℝ`. Each sender `j` wishes to send an
independent message `Mⱼ` to its receiver `Yⱼ`. An interference code is a broadcast code for the
input `(X₁, X₂)` whose encoder is a pair of separate encoders, so that the probabilities of error
and their properties come from `Network.Broadcast`.

## Main definitions

* `ICCode M₁ M₂ n α₁ α₂ β₁ β₂`: a `(M₁, M₂, n)` code for the interference channel.
* `ICCode.toBC`: the code as a broadcast code.
* `ICCode.errProb`, `ICCode.errProb₁`, `ICCode.errProb₂`: the probabilities of error.
* `ICCode.toMACOf`: the code seen from one receiver that decodes both messages.
* `IsAchievableICBits W R₁ R₂`, `icCapacityRegionBits W`: achievable rate pairs in bits and the
  capacity region.

## Main statements

* `isAchievableICBits_congr`, `icCapacityRegionBits_eq_of_marg_eq`: the capacity region of the DM-IC
  depends on `p(y₁, y₂ | x₁, x₂)` only through the conditional marginals.
* `icCapacityRegionBits_eq_of_same_marg`: if `p(y₁ | x₁, x₂) = p(y₂ | x₁, x₂)`, the capacity region
  of the DM-IC is the capacity region of the DM-MAC with output `Y₁`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]

/-- **Definition (Lecture 6 of [elgamal2010]).** A `(M₁, M₂, n)` code for the interference channel:
an encoder and a decoder for each user pair. -/
structure ICCode (M₁ M₂ n : ℕ) (α₁ α₂ β₁ β₂ : Type*) where
  /-- The encoder `m₁ ↦ x₁ⁿ(m₁)` of sender 1. -/
  enc₁ : Fin M₁ → Fin n → α₁
  /-- The encoder `m₂ ↦ x₂ⁿ(m₂)` of sender 2. -/
  enc₂ : Fin M₂ → Fin n → α₂
  /-- The decoder `y₁ⁿ ↦ m̂₁` of receiver 1. -/
  dec₁ : (Fin n → β₁) → Fin M₁
  /-- The decoder `y₂ⁿ ↦ m̂₂` of receiver 2. -/
  dec₂ : (Fin n → β₂) → Fin M₂

namespace ICCode

variable {M₁ M₂ n : ℕ} (c : ICCode M₁ M₂ n α₁ α₂ β₁ β₂) (W : α₁ × α₂ → β₁ × β₂ → ℝ)

/-- An interference code as a broadcast code with input `(X₁, X₂)`. -/
def toBC : BCCode M₁ M₂ n (α₁ × α₂) β₁ β₂ :=
  ⟨fun w => zipSeq (c.enc₁ w.1) (c.enc₂ w.2), c.dec₁, c.dec₂⟩

/-- **Definition (Lecture 6 of [elgamal2010]).** The average probability of error
`P{(M̂₁, M̂₂) ≠ (M₁, M₂)}`. -/
def errProb : ℝ := c.toBC.errProb W

/-- The probability of error `P{M̂₁ ≠ M₁}` at receiver 1. -/
def errProb₁ : ℝ := c.toBC.errProb₁ W

/-- The probability of error `P{M̂₂ ≠ M₂}` at receiver 2. -/
def errProb₂ : ℝ := c.toBC.errProb₂ W

/-- The code seen from a receiver with output alphabet `γ`, whose decoder `d` guesses both
messages. -/
def toMACOf {γ : Type*} (d : (Fin n → γ) → Fin M₁ × Fin M₂) : MACCode M₁ M₂ n α₁ α₂ γ :=
  ⟨c.enc₁, c.enc₂, d⟩

end ICCode

/-- **Definition (Lecture 6 of [elgamal2010]).** A rate pair `(R₁, R₂)`, in bits per transmission,
is achievable for the DM-IC if there are `(2^{nR₁}, 2^{nR₂}, n)` codes whose average probability of
error tends to `0`. -/
def IsAchievableICBits (W : α₁ × α₂ → β₁ × β₂ → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, ICCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α₁ α₂ β₁ β₂,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Definition (Lecture 6 of [elgamal2010]).** The capacity region of the DM-IC, in bits: the
closure of the set of achievable rate pairs. -/
def icCapacityRegionBits (W : α₁ × α₂ → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableICBits W R.1 R.2}

variable [Fintype α₁] [Fintype α₂] {W W' : α₁ × α₂ → β₁ × β₂ → ℝ}

namespace ICCode

variable {M₁ M₂ n : ℕ} (c : ICCode M₁ M₂ n α₁ α₂ β₁ β₂)

omit [Fintype α₁] [Fintype α₂] in
lemma errProb₁_nonneg (hW : IsChannel W) : 0 ≤ c.errProb₁ W := c.toBC.errProb₁_nonneg hW

omit [Fintype α₁] [Fintype α₂] in
lemma errProb₂_nonneg (hW : IsChannel W) : 0 ≤ c.errProb₂ W := c.toBC.errProb₂_nonneg hW

omit [Fintype α₁] [Fintype α₂] in
lemma errProb₁_le (hW : IsChannel W) : c.errProb₁ W ≤ c.errProb W :=
  (le_max_left _ _).trans (c.toBC.max_errProb_le hW)

omit [Fintype α₁] [Fintype α₂] in
lemma errProb₂_le (hW : IsChannel W) : c.errProb₂ W ≤ c.errProb W :=
  (le_max_right _ _).trans (c.toBC.max_errProb_le hW)

omit [Fintype α₁] [Fintype α₂] in
lemma errProb_le_add (hW : IsChannel W) : c.errProb W ≤ c.errProb₁ W + c.errProb₂ W :=
  c.toBC.errProb_le_add hW

omit [Fintype α₁] [Fintype α₂] in
lemma errProb_nonneg (hW : IsChannel W) : 0 ≤ c.errProb W :=
  (c.errProb₁_nonneg hW).trans (c.errProb₁_le hW)

omit [Fintype α₁] [Fintype α₂] in
/-- `P₁` depends only on `p(y₁ | x₁, x₂)`. -/
lemma errProb₁_congr (h : bcMarg₁ W = bcMarg₁ W') : c.errProb₁ W = c.errProb₁ W' :=
  c.toBC.errProb₁_congr h

omit [Fintype α₁] [Fintype α₂] in
/-- `P₂` depends only on `p(y₂ | x₁, x₂)`. -/
lemma errProb₂_congr (h : bcMarg₂ W = bcMarg₂ W') : c.errProb₂ W = c.errProb₂ W' :=
  c.toBC.errProb₂_congr h

end ICCode

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 6 of [elgamal2010].** Whether a rate pair is achievable depends on
`p(y₁, y₂ | x₁, x₂)` only through the conditional marginals. -/
theorem isAchievableICBits_congr (hW : IsChannel W) (hW' : IsChannel W')
    (h₁ : bcMarg₁ W = bcMarg₁ W') (h₂ : bcMarg₂ W = bcMarg₂ W') {R₁ R₂ : ℝ} :
    IsAchievableICBits W R₁ R₂ ↔ IsAchievableICBits W' R₁ R₂ := by
  have key : ∀ {W W' : α₁ × α₂ → β₁ × β₂ → ℝ}, IsChannel W → IsChannel W' →
      bcMarg₁ W = bcMarg₁ W' → bcMarg₂ W = bcMarg₂ W' →
      IsAchievableICBits W R₁ R₂ → IsAchievableICBits W' R₁ R₂ := by
    rintro W W' hW hW' h₁ h₂ ⟨c, hc⟩
    refine ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hc.const_mul 2) (fun n => (c n).errProb_nonneg hW') fun n => ?_⟩
    have h3 := (c n).errProb_le_add hW'
    rw [← (c n).errProb₁_congr h₁, ← (c n).errProb₂_congr h₂] at h3
    have h4 := (c n).errProb₁_le hW
    have h5 := (c n).errProb₂_le hW
    linarith
  exact ⟨key hW hW' h₁ h₂, key hW' hW h₁.symm h₂.symm⟩

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 6 of [elgamal2010].** The capacity region of the DM-IC depends on
`p(y₁, y₂ | x₁, x₂)` only through the conditional marginals. -/
theorem icCapacityRegionBits_eq_of_marg_eq (hW : IsChannel W) (hW' : IsChannel W')
    (h₁ : bcMarg₁ W = bcMarg₁ W') (h₂ : bcMarg₂ W = bcMarg₂ W') :
    icCapacityRegionBits W = icCapacityRegionBits W' := by
  simp only [icCapacityRegionBits, isAchievableICBits_congr hW hW' h₁ h₂]

/-! ### The same conditional marginals -/

section SameMarg

variable {β : Type*} [Fintype β] {V : α₁ × α₂ → β → ℝ}

omit [Fintype α₁] [Fintype α₂] in
open Classical in
/-- The probability of error `P₁`, written with the conditional marginal. -/
lemma ICCode.errProb₁_eq {M₁ M₂ n : ℕ} {W : α₁ × α₂ → β × β₂ → ℝ}
    (c : ICCode M₁ M₂ n α₁ α₂ β β₂) :
    c.errProb₁ W = (∑ i, ∑ j, ∑ y, if c.dec₁ y ≠ i then
      channelExt (bcMarg₁ W) n (zipSeq (c.enc₁ i) (c.enc₂ j)) y else 0) / (M₁ * M₂) := by
  simp only [ICCode.errProb₁, BCCode.errProb₁, ICCode.toBC, Fintype.sum_prod_type]
  congr!

omit [Fintype α₁] [Fintype α₂] in
open Classical in
/-- The probability of error `P₂`, written with the conditional marginal. -/
lemma ICCode.errProb₂_eq {M₁ M₂ n : ℕ} {W : α₁ × α₂ → β₁ × β → ℝ}
    (c : ICCode M₁ M₂ n α₁ α₂ β₁ β) :
    c.errProb₂ W = (∑ i, ∑ j, ∑ y, if c.dec₂ y ≠ j then
      channelExt (bcMarg₂ W) n (zipSeq (c.enc₁ i) (c.enc₂ j)) y else 0) / (M₁ * M₂) := by
  simp only [ICCode.errProb₂, BCCode.errProb₂, ICCode.toBC, Fintype.sum_prod_type]
  congr!

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 6 of [elgamal2010], page 6-7.** With the same conditional marginals, a code for the
DM-IC gives a code for the DM-MAC in which the receiver runs both decoders. -/
lemma ICCode.avgErrProb_toMACOf_le {W : α₁ × α₂ → β × β → ℝ} (h₁ : bcMarg₁ W = V)
    (h₂ : bcMarg₂ W = V) (hV : IsChannel V) {M₁ M₂ n : ℕ} (c : ICCode M₁ M₂ n α₁ α₂ β β) :
    (c.toMACOf fun y => (c.dec₁ y, c.dec₂ y)).avgErrProb V ≤ c.errProb₁ W + c.errProb₂ W := by
  classical
  rw [ICCode.errProb₁_eq, ICCode.errProb₂_eq, h₁, h₂, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  simp only [← sum_add_distrib]
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  simp only [MACCode.condErrProb, MACCode.input, ICCode.toMACOf]
  refine sum_le_sum fun y _ => ?_
  have hnn := channelExt_nonneg hV (zipSeq (c.enc₁ i) (c.enc₂ j)) y
  by_cases h₁ : c.dec₁ y = i <;> by_cases h₂ : c.dec₂ y = j <;> simp [h₁, h₂, hnn]

omit [Fintype α₁] [Fintype α₂] in
/-- With the same conditional marginals, a code for the DM-MAC gives a code for the DM-IC in which
each receiver runs the decoder of the DM-MAC. -/
lemma ICCode.errProb_ofMAC_le {W : α₁ × α₂ → β × β → ℝ} (h₁ : bcMarg₁ W = V)
    (h₂ : bcMarg₂ W = V) (hW : IsChannel W) (hV : IsChannel V) {M₁ M₂ n : ℕ}
    (c : MACCode M₁ M₂ n α₁ α₂ β) :
    (⟨c.enc₁, c.enc₂, fun y => (c.dec y).1, fun y => (c.dec y).2⟩ :
      ICCode M₁ M₂ n α₁ α₂ β β).errProb W ≤ 2 * c.avgErrProb V := by
  classical
  set d : ICCode M₁ M₂ n α₁ α₂ β β := ⟨c.enc₁, c.enc₂, fun y => (c.dec y).1, fun y => (c.dec y).2⟩
  have hd₁ : d.errProb₁ W ≤ c.avgErrProb V := by
    rw [ICCode.errProb₁_eq, h₁]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun y _ => ?_
    have hnn := channelExt_nonneg hV (zipSeq (c.enc₁ i) (c.enc₂ j)) y
    by_cases h : (c.dec y).1 = i
    · simp only [d, h, ne_eq, not_true_eq_false, ite_false]
      by_cases h' : c.dec y = (i, j) <;> simp [h', MACCode.input, hnn]
    · have h' : c.dec y ≠ (i, j) := fun e => h (by rw [e])
      simp [d, h, h', MACCode.input]
  have hd₂ : d.errProb₂ W ≤ c.avgErrProb V := by
    rw [ICCode.errProb₂_eq, h₂]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun y _ => ?_
    have hnn := channelExt_nonneg hV (zipSeq (c.enc₁ i) (c.enc₂ j)) y
    by_cases h : (c.dec y).2 = j
    · simp only [d, h, ne_eq, not_true_eq_false, ite_false]
      by_cases h' : c.dec y = (i, j) <;> simp [h', MACCode.input, hnn]
    · have h' : c.dec y ≠ (i, j) := fun e => h (by rw [e])
      simp [d, h, h', MACCode.input]
  linarith [d.errProb_le_add hW]

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 6 of [elgamal2010], page 6-7.** If `p(y₁ | x₁, x₂) = p(y₂ | x₁, x₂)`, a rate pair is
achievable for the DM-IC iff it is achievable for the DM-MAC with output `Y₁`: each receiver can
decode whatever the other one decodes. -/
theorem isAchievableICBits_iff_of_same_marg {W : α₁ × α₂ → β × β → ℝ} (hW : IsChannel W)
    (h₁ : bcMarg₁ W = V) (h₂ : bcMarg₂ W = V) {R₁ R₂ : ℝ} :
    IsAchievableICBits W R₁ R₂ ↔ IsAchievableMACBits V R₁ R₂ := by
  have hV : IsChannel V := h₁ ▸ hW.bcMarg₁
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun n => (c n).toMACOf fun y => ((c n).dec₁ y, (c n).dec₂ y),
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hc.const_mul 2) (fun n => MACCode.avgErrProb_nonneg _ hV) fun n => ?_⟩
    have h4 := (c n).errProb₁_le hW
    have h5 := (c n).errProb₂_le hW
    have h6 := (c n).avgErrProb_toMACOf_le h₁ h₂ hV
    linarith
  · rintro ⟨c, hc⟩
    refine ⟨fun n => ⟨(c n).enc₁, (c n).enc₂, fun y => ((c n).dec y).1, fun y => ((c n).dec y).2⟩,
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hc.const_mul 2) (fun n => ICCode.errProb_nonneg _ hW)
        fun n => ICCode.errProb_ofMAC_le h₁ h₂ hW hV (c n)⟩

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 6 of [elgamal2010], page 6-7.** If `p(y₁ | x₁, x₂) = p(y₂ | x₁, x₂)`, the capacity
region of the DM-IC is the capacity region of the DM-MAC with inputs `X₁`, `X₂` and output `Y₁`. -/
theorem icCapacityRegionBits_eq_of_same_marg {W : α₁ × α₂ → β × β → ℝ} (hW : IsChannel W)
    (h₁ : bcMarg₁ W = V) (h₂ : bcMarg₂ W = V) :
    icCapacityRegionBits W = macCapacityRegionBits V := by
  simp only [icCapacityRegionBits, macCapacityRegionBits,
    isAchievableICBits_iff_of_same_marg hW h₁ h₂]

end SameMarg

end InfoTheory
