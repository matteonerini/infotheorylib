/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACFeedbackBlock
public import InfoTheoryLib.Network.RelayRates

/-!
# The Cover–Leung inner bound

Theorem 2 on page 18-22 of the notes: block Markov coding and backward decoding for the multiple
access channel with feedback.

## Main definitions

* `clFakeW`: the auxiliary relay channel.
* `CLBlock.toRelay`: a code for one block as a code for one block of the auxiliary relay channel.
* `MACFBCode.ofRC`: a code for the auxiliary relay channel as a code with feedback.
* `MACFBCode.pad`: a code for a longer block.

## Main statements

* `CLBlock.exists_code_le`: the code of all the blocks.
* `MACFBCode.exists_sub`: a code still works with fewer messages.
* `isAchievableMACFB_coverLeung`: **Theorem 2, the Cover–Leung inner bound**.

## Implementation notes

The block Markov structure of the Cover–Leung scheme is the one of decode–forward for the relay
channel: sender 2 plays the sender, sender 1 plays the relay, which decodes the index of sender 2
and which forwards it. The only difference is that sender 1 also has a message of its own, which the
relay of the notes does not have. So we pass to an auxiliary relay channel: the input of the relay
is a table of symbols, one for each value of the message of sender 1, the input of the sender
carries that value, the channel selects the entry of the table, and it tells the value to the relay.
A theorem about the relay channel, `RelayBlock.markov_errProb_le`, then gives the error of the code
of all the blocks, and a code of this auxiliary channel is a code with feedback.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X₁ X₂ Y : Type*} [Fintype Y] {W : X₁ × X₂ → Y → ℝ}

/-! ### The auxiliary relay channel -/

section Fake

variable {Mm : ℕ}

/-- **The auxiliary relay channel.** The sender sends `(m, x₂)`, the relay sends a table `F` of
symbols, the output is drawn with the input `(F m, x₂)`, and the relay also learns `m`. -/
def clFakeW (W : X₁ × X₂ → Y → ℝ) (t : (Fin Mm × X₂) × (Fin Mm → X₁)) (z : Y × (Fin Mm × Y)) : ℝ :=
  W (t.2 t.1.1, t.1.2) z.1 * ind (z.2 = (t.1.1, z.1))

lemma clFakeW_isChannel (hW : IsChannel W) : IsChannel (clFakeW (Mm := Mm) W) := fun t => by
  classical
  refine ⟨fun z => mul_nonneg ((hW _).nonneg _) (ind_nonneg _), ?_⟩
  rw [Fintype.sum_prod_type]
  have h : ∀ y, ∑ s, clFakeW (Mm := Mm) W t (y, s) = W (t.2 t.1.1, t.1.2) y := fun y => by
    simp only [clFakeW]
    rw [sum_eq_single (t.1.1, y) (fun s _ hs => by rw [ind_of_neg hs, mul_zero]) (by simp),
      ind_of_pos rfl, mul_one]
  simp only [h]
  exact (hW _).sum_eq_one

variable {Mb n : ℕ} [NeZero n]

/-- A code for one block as a code for one block of the auxiliary relay channel. -/
def CLBlock.toRelay (C : CLBlock Mb Mm (Fin n → X₁) (Fin n → X₂) (Fin n → Y)) :
    RelayBlock Mb Mm (Fin n → Fin Mm → X₁) (Fin n → Fin Mm × X₂) (Fin n → Y)
      (Fin n → Fin Mm × Y) where
  s l i m := C.x₁ l m i
  x l a m i := (m, C.x₂ l a i)
  rDec l ys := C.d₁ l (ys ⟨0, NeZero.pos n⟩).1 fun i => (ys i).2
  dDec a y := C.d a y

/-- The error of a block of the auxiliary channel is the error of the block. -/
lemma CLBlock.err_toRelay (C : CLBlock Mb Mm (Fin n → X₁) (Fin n → X₂) (Fin n → Y)) (l c : Fin Mb)
    (m : Fin Mm) :
    C.toRelay.err (relaySeq (clFakeW W) n) l c m = C.err (macSeq W n) l c m := by
  classical
  simp only [RelayBlock.err, CLBlock.err]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_eq_single (fun i => (m, y i))]
  · have hp : relaySeq (clFakeW W) n (C.toRelay.x l c m, C.toRelay.s l) (y, fun i => (m, y i)) =
        macSeq W n (C.x₁ l m, C.x₂ l c) y := by
      simp only [relaySeq, macSeq, clFakeW, CLBlock.toRelay]
      refine prod_congr rfl fun i _ => ?_
      rw [ind_of_pos trivial, mul_one]
    rw [hp]
    rfl
  · intro s _ hs
    have hz : relaySeq (clFakeW W) n (C.toRelay.x l c m, C.toRelay.s l) (y, s) = 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
      refine prod_eq_zero (mem_univ i) ?_
      simp only [clFakeW, CLBlock.toRelay]
      rw [ind_of_neg hi, mul_zero]
    rw [hz, zero_mul]
  · simp

/-- The average error of a block of the auxiliary channel is the one of the block. -/
lemma CLBlock.avgErr_toRelay [NeZero Mb] [NeZero Mm]
    (C : CLBlock Mb Mm (Fin n → X₁) (Fin n → X₂) (Fin n → Y)) :
    C.toRelay.avgErr (relaySeq (clFakeW W) n) = C.avgErr (macSeq W n) := by
  simp only [RelayBlock.avgErr, CLBlock.avgErr, CLBlock.err_toRelay]

end Fake

/-! ### From the auxiliary channel to feedback -/

section OfRC

variable {M M₁ M₂ Mm N : ℕ}

/-- A code for the auxiliary relay channel, whose encoder has the form `(tag w₁, x₂ w₂)`, as a code
with feedback. -/
def MACFBCode.ofRC (c : RCCode M N (Fin Mm × X₂) (Fin Mm → X₁) Y (Fin Mm × Y))
    (e : Fin M₁ × Fin M₂ ≃ Fin M) (tag : ℕ → Fin M₁ → Fin Mm) (x₂ : ℕ → Fin M₂ → X₂) :
    MACFBCode M₁ M₂ N X₁ X₂ Y where
  enc₁ k w₁ ys := c.relay k (fun t => (tag t w₁, ys t)) (tag k w₁)
  enc₂ k w₂ _ := x₂ k w₂
  dec y := e.symm (c.dec y)

/-- The probability of error as an expectation. -/
lemma MACFBCode.errProb_eq (c : MACFBCode M₁ M₂ N X₁ X₂ Y) :
    c.errProb W = ∑ ω, c.law W ω * ind (c.dec ω.2 ≠ ω.1) := by
  classical
  simp only [MACFBCode.errProb, InfoTheory.errProb]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : c.dec ω.2 = ω.1
  · have hne : ¬ c.dec ω.2 ≠ ω.1 := not_not.mpr h
    rw [ind_of_neg hne, mul_zero]
    exact ite_eq_right hne
  · rw [ind_of_pos h, mul_one]
    exact ite_eq_left h

/-- The probability of error of a code for the auxiliary channel is the one of the code with
feedback. -/
theorem MACFBCode.errProb_ofRC (c : RCCode M N (Fin Mm × X₂) (Fin Mm → X₁) Y (Fin Mm × Y))
    (e : Fin M₁ × Fin M₂ ≃ Fin M) (tag : ℕ → Fin M₁ → Fin Mm) (x₂ : ℕ → Fin M₂ → X₂)
    (hc : ∀ k w, c.enc k (e w) = (tag k w.1, x₂ k w.2)) :
    (MACFBCode.ofRC (X₁ := X₁) c e tag x₂).errProb W = c.errProb (clFakeW W) := by
  classical
  have hcard : M₁ * M₂ = M := by
    have h := Fintype.card_congr e
    simpa using h
  set c' := MACFBCode.ofRC (X₁ := X₁) c e tag x₂ with hc'
  rw [MACFBCode.errProb_eq, RCCode.errProb_eq]
  have e₁ : ∑ ω, c'.law W ω * ind (c'.dec ω.2 ≠ ω.1) =
      ∑ w, ∑ y, c'.law W (w, y) * ind (c'.dec y ≠ w) := Fintype.sum_prod_type _
  have e₂ : ∑ ω, c.law (clFakeW W) N ω * ind (c.dec (rcY ω) ≠ ω.1) =
      ∑ w, ∑ z, c.law (clFakeW W) N (w, z) * ind (c.dec (rcY (w, z)) ≠ w) :=
    Fintype.sum_prod_type _
  rw [e₁, e₂, ← Equiv.sum_comp e]
  refine sum_congr rfl fun w _ => ?_
  -- the row of a message
  have hu₁ : uniformPMF (Fin M₁ × Fin M₂) w = uniformPMF (Fin M) (e w) := by
    simp only [uniformPMF, Fintype.card_prod, Fintype.card_fin, hcard]
  let lift : (Fin N → Y) → Fin N → Y × (Fin Mm × Y) := fun y k => (y k, (tag k w.1, y k))
  refine (Finset.sum_of_injOn lift ?_ (fun _ _ => mem_univ _) ?_ ?_)
  · intro y _ y' _ h
    funext k
    exact congrArg Prod.fst (congrFun h k)
  · intro z _ hz
    have hne : ∃ k, (z k).2 ≠ (tag k w.1, (z k).1) := by
      by_contra hall
      push Not at hall
      refine hz ?_
      refine ⟨fun k => (z k).1, by simp, ?_⟩
      funext k
      exact Prod.ext rfl (hall k).symm
    obtain ⟨k, hk⟩ := hne
    have hl : c.law (clFakeW W) N (e w, z) = 0 := by
      rw [RCCode.law, fbLaw_eq_prod]
      refine mul_eq_zero_of_right _ (prod_eq_zero (mem_univ k) ?_)
      simp only [RCCode.fbEnc, hc, clFakeW]
      rw [ind_of_neg hk, mul_zero]
    rw [hl, zero_mul]
  · intro y _
    have hl : c'.law W (w, y) = c.law (clFakeW W) N (e w, lift y) := by
      rw [MACFBCode.law, RCCode.law, fbLaw_eq_prod, fbLaw_eq_prod, hu₁]
      congr 1
      refine prod_congr rfl fun k _ => ?_
      simp only [RCCode.fbEnc, hc, clFakeW, MACFBCode.fbEnc, hc', MACFBCode.ofRC, lift]
      rw [ind_of_pos trivial, mul_one]
    rw [hl]
    congr 1
    have hd : c'.dec y = e.symm (c.dec y) := rfl
    have hY : rcY (e w, lift y) = y := rfl
    rw [hd, hY]
    by_cases h : c.dec y = e w
    · rw [h, Equiv.symm_apply_apply, ind_of_neg (not_not.mpr rfl), ind_of_neg (not_not.mpr rfl)]
    · have h' : e.symm (c.dec y) ≠ w := fun h'' => h (by rw [← h'', Equiv.apply_symm_apply])
      rw [ind_of_pos h, ind_of_pos h']

end OfRC

/-! ### The code of all the blocks -/

section Code

variable {Mb Mm n B : ℕ} [NeZero Mb] [NeZero Mm] [NeZero n]

omit [NeZero Mb] [NeZero n] in
lemma msgC_snd (f f' : Fin B → Fin Mb) (g : Fin B → Fin Mm) (j : ℕ) :
    msgC (f, g) j = msgC (f', g) j := rfl

omit [NeZero Mm] [NeZero n] in
lemma msgA_fst (f : Fin B → Fin Mb) (g g' : Fin B → Fin Mm) (j : ℕ) :
    msgA (f, g) j = msgA (f, g') j := rfl

omit [NeZero Mm] [NeZero n] in
lemma msgL_fst (f : Fin B → Fin Mb) (g g' : Fin B → Fin Mm) (j : ℕ) :
    msgL (f, g) j = msgL (f, g') j := by
  cases j <;> rfl

/-- **The code of all the blocks.** -/
theorem CLBlock.exists_code_le [Nonempty Y] (C : CLBlock Mb Mm (Fin n → X₁) (Fin n → X₂) (Fin n →
  Y))
    (hB : 0 < B) (hW : IsChannel W) :
    ∃ c : MACFBCode (Mm ^ B) (Mb ^ B) ((B + 1) * n) X₁ X₂ Y,
      c.errProb W ≤ ((B : ℝ) + 1) * C.avgErr (macSeq W n) := by
  classical
  let e₁ : Fin (Mm ^ B) ≃ (Fin B → Fin Mm) := (Fintype.equivFinOfCardEq (by simp)).symm
  let e₂ : Fin (Mb ^ B) ≃ (Fin B → Fin Mb) := (Fintype.equivFinOfCardEq (by simp)).symm
  let e' : Fin (Mm ^ B) × Fin (Mb ^ B) ≃ Fin (Mm ^ B * Mb ^ B) := finProdFinEquiv
  let e : Fin (Mm ^ B * Mb ^ B) ≃ MarkovMsg Mb Mm B :=
    e'.symm.trans ((e₁.prodCongr e₂).trans (Equiv.prodComm _ _))
  let f₀ : Fin B → Fin Mb := fun _ => 0
  let g₀ : Fin B → Fin Mm := fun _ => 0
  let d₁ : Fin Mm × Y := (0, Classical.arbitrary Y)
  let c₀ := C.toRelay.markov (X := Fin Mm × X₂) (X₁ := Fin Mm → X₁) e d₁ (Classical.arbitrary Y)
  let tag : ℕ → Fin (Mm ^ B) → Fin Mm := fun k w₁ => msgC (f₀, e₁ w₁) (k / n)
  let x₂ : ℕ → Fin (Mb ^ B) → X₂ := fun k w₂ =>
    C.x₂ (msgL (e₂ w₂, g₀) (k / n)) (msgA (e₂ w₂, g₀) (k / n)) ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩
  have hc : ∀ k w, c₀.enc k (e' w) = (tag k w.1, x₂ k w.2) := by
    intro k w
    have hew : e (e' w) = (e₂ w.2, e₁ w.1) := by
      simp [e]
      rfl
    simp only [c₀, RelayBlock.markov, hew, CLBlock.toRelay, tag, x₂]
    rw [msgL_fst (e₂ w.2) (e₁ w.1) g₀, msgA_fst (e₂ w.2) (e₁ w.1) g₀, msgC_snd (e₂ w.2) f₀ (e₁ w.1)]
  refine ⟨MACFBCode.ofRC (X₁ := X₁) c₀ e' tag x₂, ?_⟩
  rw [MACFBCode.errProb_ofRC c₀ e' tag x₂ hc]
  have h := C.toRelay.markov_errProb_le (W := clFakeW W) hB (clFakeW_isChannel hW) e d₁
    (Classical.arbitrary Y)
  rwa [CLBlock.avgErr_toRelay] at h

end Code

/-! ### Longer blocks and fewer messages -/

section Lift

variable {M₁ M₂ N : ℕ}

/-- A code for a longer block: the decoder ignores the last symbols. -/
def MACFBCode.pad (c : MACFBCode M₁ M₂ N X₁ X₂ Y) (m : ℕ) : MACFBCode M₁ M₂ (N + m) X₁ X₂ Y where
  enc₁ := c.enc₁
  enc₂ := c.enc₂
  dec y := c.dec fun i => y (Fin.castAdd m i)

/-- Padding does not change the probability of error. -/
theorem MACFBCode.errProb_pad (c : MACFBCode M₁ M₂ N X₁ X₂ Y) (hW : IsChannel W) (m : ℕ) :
    (c.pad m).errProb W = c.errProb W := by
  classical
  have key : ∀ m : ℕ, ∑ ω : (Fin M₁ × Fin M₂) × (Fin (N + m) → Y),
      fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W c.fbEnc (N + m) ω *
        ind (c.dec (fun i => ω.2 (Fin.castAdd m i)) ≠ ω.1) =
      ∑ ω, c.law W ω * ind (c.dec ω.2 ≠ ω.1) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have hm := sum_dist_mul (fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W c.fbEnc (N + m + 1))
        (fun z => (z.1, Fin.init z.2))
        (fun ω : (Fin M₁ × Fin M₂) × (Fin (N + m) → Y) =>
          ind (c.dec (fun i => ω.2 (Fin.castAdd m i)) ≠ ω.1))
      have hd : dist (fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W c.fbEnc (N + m + 1))
          (fun z => (z.1, Fin.init z.2)) = fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W c.fbEnc (N + m) :=
        dist_fbLaw_init hW (N + m)
      rw [hd] at hm
      exact hm.symm.trans ih
  rw [MACFBCode.errProb_eq, MACFBCode.errProb_eq]
  exact key m

/-- **Fewer messages.** A code still works with fewer messages: the best rectangle of messages has
  at
most the average error. -/
theorem MACFBCode.exists_sub [NeZero M₁] [NeZero M₂] (c : MACFBCode M₁ M₂ N X₁ X₂ Y) {M₁' M₂' : ℕ}
    (h₁' : 0 < M₁') (h₂' : 0 < M₂') (h₁ : M₁' ≤ M₁) (h₂ : M₂' ≤ M₂) (hW : IsChannel W) :
    ∃ c' : MACFBCode M₁' M₂' N X₁ X₂ Y, c'.errProb W ≤ c.errProb W := by
  classical
  have hM₁ : (0 : ℝ) < M₁ := by exact_mod_cast NeZero.pos M₁
  have hM₂ : (0 : ℝ) < M₂ := by exact_mod_cast NeZero.pos M₂
  have hM₁' : (0 : ℝ) < M₁' := by exact_mod_cast h₁'
  have hM₂' : (0 : ℝ) < M₂' := by exact_mod_cast h₂'
  have : Nonempty (Fin M₁') := ⟨⟨0, h₁'⟩⟩
  have : Nonempty (Fin M₂') := ⟨⟨0, h₂'⟩⟩
  -- the error of a pair of messages
  let P : Fin M₁ × Fin M₂ → (Fin N → Y) → ℝ := fun w y =>
    ∏ i : Fin N, W (c.fbEnc i w fun t : Fin i => y ⟨t, t.2.trans i.2⟩) (y i)
  have hP0 : ∀ w y, 0 ≤ P w y := fun w y => prod_nonneg fun i _ => (hW _).nonneg _
  let f : Fin M₁ × Fin M₂ → ℝ := fun w => ∑ y, P w y * ind (c.dec y ≠ w)
  have hf0 : ∀ w, 0 ≤ f w := fun w => sum_nonneg fun y _ => mul_nonneg (hP0 w y) (ind_nonneg _)
  have herr : ∀ {A₁ A₂ : ℕ} (d : MACFBCode A₁ A₂ N X₁ X₂ Y), d.errProb W =
      (∑ w, ∑ y, (∏ i : Fin N, W (d.fbEnc i w fun t : Fin i => y ⟨t, t.2.trans i.2⟩) (y i)) *
        ind (d.dec y ≠ w)) / ((A₁ : ℝ) * A₂) := by
    intro A₁ A₂ d
    rw [MACFBCode.errProb_eq, Fintype.sum_prod_type, sum_div]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    rw [MACFBCode.law, fbLaw_eq_prod]
    simp only [uniformPMF, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hc : c.errProb W = (∑ w, f w) / ((M₁ : ℝ) * M₂) := herr c
  -- the windows
  obtain ⟨s₁, hs₁⟩ := exists_window h₁ fun w₁ => ∑ w₂, f (w₁, w₂)
  let ι₁ : Fin M₁' → Fin M₁ := fun t => s₁ + Fin.castLE h₁ t
  obtain ⟨s₂, hs₂⟩ := exists_window h₂ fun w₂ => ∑ t₁, f (ι₁ t₁, w₂)
  let ι₂ : Fin M₂' → Fin M₂ := fun t => s₂ + Fin.castLE h₂ t
  have hι₁ : Function.Injective ι₁ := fun a b hab => Fin.castLE_injective h₁ (add_left_cancel hab)
  have hι₂ : Function.Injective ι₂ := fun a b hab => Fin.castLE_injective h₂ (add_left_cancel hab)
  let c' : MACFBCode M₁' M₂' N X₁ X₂ Y :=
    ⟨fun k t => c.enc₁ k (ι₁ t), fun k t => c.enc₂ k (ι₂ t),
      fun y => (Function.invFun ι₁ (c.dec y).1, Function.invFun ι₂ (c.dec y).2)⟩
  refine ⟨c', ?_⟩
  have hrow : ∀ t : Fin M₁' × Fin M₂', (∑ y, (∏ i : Fin N, W (c'.fbEnc i t fun u : Fin i =>
      y ⟨u, u.2.trans i.2⟩) (y i)) * ind (c'.dec y ≠ t)) ≤ f (ι₁ t.1, ι₂ t.2) := by
    intro t
    refine sum_le_sum fun y _ => ?_
    refine mul_le_mul_of_nonneg_left (ind_mono ?_) (hP0 (ι₁ t.1, ι₂ t.2) y)
    intro hne heq
    refine hne ?_
    have hd : c'.dec y = (Function.invFun ι₁ (c.dec y).1, Function.invFun ι₂ (c.dec y).2) := rfl
    rw [hd, heq]
    exact Prod.ext (Function.leftInverse_invFun hι₁ t.1) (Function.leftInverse_invFun hι₂ t.2)
  rw [herr c', hc, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsum : (∑ t : Fin M₁' × Fin M₂', f (ι₁ t.1, ι₂ t.2)) * ((M₁ : ℝ) * M₂) ≤
      (∑ w, f w) * ((M₁' : ℝ) * M₂') := by
    have e₁ : ∑ t : Fin M₁' × Fin M₂', f (ι₁ t.1, ι₂ t.2) = ∑ t₂, ∑ t₁, f (ι₁ t₁, ι₂ t₂) := by
      rw [Fintype.sum_prod_type_right]
    have e₂ : ∑ w₂, ∑ t₁, f (ι₁ t₁, w₂) = ∑ t₁, ∑ w₂, f (ι₁ t₁, w₂) := sum_comm
    have e₃ : ∑ w, f w = ∑ w₁, ∑ w₂, f (w₁, w₂) := Fintype.sum_prod_type _
    rw [e₁, e₃]
    calc _ = ((∑ t₂, ∑ t₁, f (ι₁ t₁, s₂ + Fin.castLE h₂ t₂)) * M₂) * M₁ := by ring
      _ ≤ ((∑ w₂, ∑ t₁, f (ι₁ t₁, w₂)) * M₂') * M₁ :=
          mul_le_mul_of_nonneg_right hs₂ hM₁.le
      _ = ((∑ t₁, ∑ w₂, f (s₁ + Fin.castLE h₁ t₁, w₂)) * M₁) * M₂' := by
          rw [e₂]
          ring
      _ ≤ ((∑ w₁, ∑ w₂, f (w₁, w₂)) * M₁') * M₂' :=
          mul_le_mul_of_nonneg_right hs₁ hM₂'.le
      _ = _ := by ring
  calc _ ≤ (∑ t : Fin M₁' × Fin M₂', f (ι₁ t.1, ι₂ t.2)) * ((M₁ : ℝ) * M₂) :=
        mul_le_mul_of_nonneg_right (sum_le_sum fun t _ => hrow t) (by positivity)
    _ ≤ _ := hsum

end Lift

/-! ### The rates -/

section Rates

/-- The number of messages of the code of all the blocks is at least the target. -/
lemma two_pow_ceil_le_of_exp {ρ R η : ℝ} {B₁ n N M₀ : ℕ} (hρ0 : 0 ≤ ρ) (hM₀ : 0 < M₀)
    (hexp : exp ((B₁ : ℝ) * ((n : ℝ) * ρ)) ≤ (M₀ : ℝ))
    (hNreal : (N : ℝ) / ((B₁ : ℝ) + 1) < (n : ℝ) + 1)
    (hη : η ≤ (B₁ : ℝ) / (B₁ + 1) * ρ - R * log 2) (hN : (B₁ : ℝ) * ρ + log 2 ≤ (N : ℝ) * η) :
    2 ^ ⌈(N : ℝ) * R⌉₊ ≤ M₀ := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hB₁pos : (0 : ℝ) < (B₁ : ℝ) + 1 := by positivity
  by_cases hR0 : (N : ℝ) * R ≤ 0
  · rw [Nat.ceil_eq_zero.mpr hR0, pow_zero]
    exact hM₀
  · push Not at hR0
    have hceil : ((⌈(N : ℝ) * R⌉₊ : ℕ) : ℝ) < (N : ℝ) * R + 1 := Nat.ceil_lt_add_one hR0.le
    have h₂ : ((2 ^ ⌈(N : ℝ) * R⌉₊ : ℕ) : ℝ) ≤ (M₀ : ℝ) := by
      refine le_trans ?_ hexp
      push_cast
      rw [← exp_log (by norm_num : (0 : ℝ) < 2), ← exp_nat_mul]
      refine exp_le_exp.mpr ?_
      have h₃ : (B₁ : ℝ) * ((N : ℝ) / ((B₁ : ℝ) + 1) * ρ) = (N : ℝ) * ((B₁ : ℝ) / (B₁ + 1) * ρ) :=
        by
        field_simp
      have h₄ : (N : ℝ) / ((B₁ : ℝ) + 1) * ρ ≤ ((n : ℝ) + 1) * ρ :=
        mul_le_mul_of_nonneg_right hNreal.le hρ0
      have h₅ : (B₁ : ℝ) * ((N : ℝ) / ((B₁ : ℝ) + 1) * ρ) ≤ (B₁ : ℝ) * (((n : ℝ) + 1) * ρ) :=
        mul_le_mul_of_nonneg_left h₄ (Nat.cast_nonneg _)
      have h₆ : ((⌈(N : ℝ) * R⌉₊ : ℕ) : ℝ) * log 2 ≤ ((N : ℝ) * R + 1) * log 2 :=
        mul_le_mul_of_nonneg_right hceil.le hlog2.le
      have h₇ : (N : ℝ) * η ≤ (N : ℝ) * ((B₁ : ℝ) / (B₁ + 1) * ρ) - (N : ℝ) * R * log 2 := by
        have := mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg N)
        linarith
      nlinarith
    exact_mod_cast h₂

variable {U : Type*} [Fintype U] [Fintype X₁] [Fintype X₂] [Nonempty X₁] [Nonempty X₂] [Nonempty Y]
  {pu : U → ℝ} {A : U → X₁ → ℝ} {B : U → X₂ → ℝ}

omit [Fintype X₁] [Fintype X₂] in
instance (M₁ M₂ n : ℕ) [NeZero M₁] [NeZero M₂] : Nonempty (MACFBCode M₁ M₂ n X₁ X₂ Y) :=
  ⟨⟨fun _ _ _ => Classical.arbitrary X₁, fun _ _ _ => Classical.arbitrary X₂, fun _ => (0, 0)⟩⟩

/-- **Theorem 2 (Cover–Leung inner bound), page 18-22 of [elgamal2010].** For
`p(u) p(x₁ | u) p(x₂ | u)`, every pair of nonnegative rates, in bits, with `R₁ < I(X₁; Y | X₂, U)`,
`R₂ < I(X₂; Y | X₁, U)` and `R₁ + R₂ < I(X₁, X₂; Y)` is achievable for the multiple access channel
with feedback. -/
theorem isAchievableMACFB_coverLeung (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B)
    (hW : IsChannel W) {R₁ R₂ : ℝ} (h₁0 : 0 ≤ R₁) (h₂0 : 0 ≤ R₂)
    (h₁ : R₁ * log 2 < I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ; clLaw pu A B W])
    (h₂ : R₂ * log 2 < I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ; clLaw pu A B W])
    (h₃ : (R₁ + R₂) * log 2 < I[fun z => z.1.2 : Prod.snd ; clLaw pu A B W]) :
    IsAchievableMACFB W R₁ R₂ := by
  classical
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  set μ := clLaw pu A B W with hμ
  set I₁ := I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ; μ] with hI₁
  set I₂ := I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ; μ] with hI₂
  set I₃ := I[fun z => z.1.2 : Prod.snd ; μ] with hI₃
  -- the rates of the blocks
  set g := min (min (I₁ - R₁ * log 2) (I₂ - R₂ * log 2)) (I₃ - (R₁ + R₂) * log 2) with hg
  have hg0 : 0 < g := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hg₁ : g ≤ I₁ - R₁ * log 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hg₂ : g ≤ I₂ - R₂ * log 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hg₃ : g ≤ I₃ - (R₁ + R₂) * log 2 := min_le_right _ _
  set r₁ := R₁ * log 2 + g / 3 with hr₁
  set r₂ := R₂ * log 2 + g / 3 with hr₂
  have hr₁0 : 0 ≤ r₁ := by positivity
  have hr₂0 : 0 ≤ r₂ := by positivity
  have hr₁I : r₁ < I₁ := by rw [hr₁]; linarith
  have hr₂I : r₂ < I₂ := by rw [hr₂]; linarith
  have hr₃I : r₁ + r₂ < I₃ := by
    rw [hr₁, hr₂]
    nlinarith
  -- the number of blocks
  set η := g / 6 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (r₁ + r₂) / η < b := exists_nat_gt _
  set B₁ := b + 1 with hB₁
  have hB₁pos : (0 : ℝ) < (B₁ : ℝ) + 1 := by positivity
  have hsmall : ∀ r : ℝ, 0 ≤ r → r ≤ r₁ + r₂ → r / ((B₁ : ℝ) + 1) ≤ η := by
    intro r hr hrs
    rw [div_le_iff₀ hB₁pos]
    rw [div_lt_iff₀ hη0] at hb
    have : (b : ℝ) ≤ (B₁ : ℝ) + 1 := by
      simp only [hB₁]
      push_cast
      linarith
    nlinarith
  have hfrac : ∀ r : ℝ, (B₁ : ℝ) / (B₁ + 1) * r = r - r / ((B₁ : ℝ) + 1) := by
    intro r
    field_simp
    ring
  have hη₁ : η ≤ (B₁ : ℝ) / (B₁ + 1) * r₁ - R₁ * log 2 := by
    rw [hfrac, hr₁] at *
    have := hsmall _ hr₁0 (by linarith)
    rw [hr₁] at this
    rw [hη] at *
    linarith
  have hη₂ : η ≤ (B₁ : ℝ) / (B₁ + 1) * r₂ - R₂ * log 2 := by
    rw [hfrac]
    have := hsmall _ hr₂0 (by linarith)
    rw [hη] at *
    rw [hr₂] at *
    linarith
  have hB₁0 : 0 < B₁ := by simp [hB₁]
  have key : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ∃ c : MACFBCode (2 ^ ⌈(N : ℝ) * R₁⌉₊) (2 ^ ⌈(N : ℝ) * R₂⌉₊) N X₁ X₂ Y, c.errProb W ≤ ε := by
    intro ε hε
    have hδ : 0 < ε / ((B₁ : ℝ) + 1) := by positivity
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (eventually_clBlock hu hA hB hW hr₁0 hr₁I hr₂I hr₃I hδ)
    have hdiv : Tendsto (fun N : ℕ => N / (B₁ + 1)) atTop atTop :=
      Nat.tendsto_div_const_atTop (Nat.succ_ne_zero B₁)
    have hev₁ : ∀ᶠ N : ℕ in atTop, (B₁ : ℝ) * r₁ + log 2 ≤ (N : ℝ) * η :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hη0 |>.eventually_ge_atTop _
    have hev₂ : ∀ᶠ N : ℕ in atTop, (B₁ : ℝ) * r₂ + log 2 ≤ (N : ℝ) * η :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hη0 |>.eventually_ge_atTop _
    filter_upwards [hdiv.eventually_ge_atTop (n₀ + 1), hev₁, hev₂] with N hN₁ hN₂ hN₃
    obtain ⟨n, hn⟩ : ∃ n, n = N / (B₁ + 1) := ⟨_, rfl⟩
    rw [← hn] at hN₁
    have hnpos : NeZero n := ⟨by omega⟩
    obtain ⟨C, hC⟩ := hn₀ n (by omega)
    obtain ⟨m, hm⟩ : ∃ m, N = (B₁ + 1) * n + m :=
      Nat.exists_eq_add_of_le (by rw [hn]; exact Nat.mul_div_le N (B₁ + 1))
    have hNreal : (N : ℝ) / ((B₁ : ℝ) + 1) < (n : ℝ) + 1 := by
      have h₀ : N < (B₁ + 1) * (n + 1) := by
        rw [hn]
        exact Nat.lt_mul_div_succ N (Nat.succ_pos B₁)
      have h₀' : (N : ℝ) < ((B₁ : ℝ) + 1) * ((n : ℝ) + 1) := by exact_mod_cast h₀
      rw [div_lt_iff₀ hB₁pos]
      linarith
    have hexpM : ∀ r : ℝ, exp ((B₁ : ℝ) * ((n : ℝ) * r)) ≤ ((⌈exp (n * r)⌉₊ ^ B₁ : ℕ) : ℝ) := by
      intro r
      have h₁ : exp (n * r) ≤ ((⌈exp (n * r)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      rw [exp_nat_mul]
      push_cast
      exact pow_le_pow_left₀ (exp_pos _).le h₁ _
    have hpos₁ : 0 < ⌈exp (n * r₁)⌉₊ ^ B₁ := pow_pos (NeZero.pos _) _
    have hpos₂ : 0 < ⌈exp (n * r₂)⌉₊ ^ B₁ := pow_pos (NeZero.pos _) _
    have hrate₁ := two_pow_ceil_le_of_exp hr₁0 hpos₁ (hexpM r₁) hNreal hη₁ hN₂
    have hrate₂ := two_pow_ceil_le_of_exp hr₂0 hpos₂ (hexpM r₂) hNreal hη₂ hN₃
    obtain ⟨c₀, hc₀⟩ := C.exists_code_le (B := B₁) hB₁0 hW
    have hbound : c₀.errProb W ≤ ε := by
      calc _ ≤ ((B₁ : ℝ) + 1) * C.avgErr (macSeq W n) := hc₀
        _ ≤ ((B₁ : ℝ) + 1) * (ε / ((B₁ : ℝ) + 1)) := mul_le_mul_of_nonneg_left hC hB₁pos.le
        _ = ε := by field_simp
    have hne₁ : NeZero (⌈exp (n * r₁)⌉₊ ^ B₁) := ⟨hpos₁.ne'⟩
    have hne₂ : NeZero (⌈exp (n * r₂)⌉₊ ^ B₁) := ⟨hpos₂.ne'⟩
    subst hm
    obtain ⟨c', hc'⟩ := (c₀.pad m).exists_sub (by positivity) (by positivity) hrate₁ hrate₂ hW
    exact ⟨c', hc'.trans ((c₀.errProb_pad hW m).trans_le hbound)⟩
  exact exists_seq_tendsto
    (C := fun N : ℕ => MACFBCode (2 ^ ⌈(N : ℝ) * R₁⌉₊) (2 ^ ⌈(N : ℝ) * R₂⌉₊) N X₁ X₂ Y)
    (fun N c => c.errProb W)
    (fun N c => errProb_nonneg (c.law_isPMF hW (by positivity) (by positivity)) _ _ _) key

end Rates

end InfoTheory
