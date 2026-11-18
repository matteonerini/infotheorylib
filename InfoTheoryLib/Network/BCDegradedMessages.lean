/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCCapacity
public import InfoTheoryLib.Network.BCCutSet
public import InfoTheoryLib.Network.BCMoreCapable

/-!
# The DM-BC with degraded message sets

A common message `M₀` is sent to both receivers and a private message `M₁` to receiver 1. This file
proves Theorem 1 of Lecture 9: the capacity region is the set of `(R₀, R₁)` with `R₀ ≤ I(U; Y₂)`,
`R₁ ≤ I(X; Y₁ | U)`, `R₀ + R₁ ≤ I(X; Y₁)` for some `p(u, x)`.

## Main definitions

* `DMSCode M₀ M₁ n α β₁ β₂`: the codes, where receiver 1 decodes both messages.
* `IsAchievableDMSBits W R₀ R₁`, `dmsCapacityRegionBits W`: achievable rates and the capacity
  region.
* `dmsRegionBits W`: the region of Theorem 1.

## Main statements

* `dmsDecode`, `sum_codebook_dmsDecode_le`: decoding both messages at receiver 1.
* `isAchievableDMSBits_of_lt`: achievability, by superposition coding.
* `IsAchievableDMSBits.mem_closure_dmsRegionBits`: the converse.
* `dmsCapacityRegionBits_eq`: **Theorem 1 of Lecture 9**.
* `IsAchievableBCBits.mem_closure_bcOuterRegionBits`: the form of the Nair–El Gamal outer bound on
  page 9-40 of Lecture 9.

## Implementation notes

The capacity region is for nonnegative rates. Unlike for private messages, a negative rate `R₁`
would not be harmless in the region, as `R₀ + R₁ ≤ I(X; Y₁)` is what makes receiver 1 able to
decode `M₀`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Decoding both messages at receiver 1 -/

section Decoder

variable {𝒰 α β : Type*} [Fintype 𝒰] [Fintype α] [Fintype β] {q : 𝒰 × α → ℝ} {V : α → β → ℝ}

open Classical in
/-- The decoder of both messages: the unique pair `(k, l)` with `(uⁿ(k), xⁿ(k, l), yⁿ) ∈ T`, and `d`
otherwise. -/
def dmsDecode {n K L : ℕ} (T : Finset ((Fin n → 𝒰) × (Fin n → α) × (Fin n → β)))
    (C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)) (d : Fin K × Fin L) (y : Fin n → β) :
    Fin K × Fin L :=
  if h : ∃ p : Fin K × Fin L, ((C p.1).1, (C p.1).2 p.2, y) ∈ T ∧
      ∀ p' : Fin K × Fin L, ((C p'.1).1, (C p'.1).2 p'.2, y) ∈ T → p' = p then h.choose else d

omit [Fintype 𝒰] [Fintype α] [Fintype β] in
lemma dmsDecode_eq {n K L : ℕ} {T : Finset ((Fin n → 𝒰) × (Fin n → α) × (Fin n → β))}
    {C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)} (d : Fin K × Fin L) {y : Fin n → β}
    {p : Fin K × Fin L} (hp : ((C p.1).1, (C p.1).2 p.2, y) ∈ T)
    (huniq : ∀ p' : Fin K × Fin L, ((C p'.1).1, (C p'.1).2 p'.2, y) ∈ T → p' = p) :
    dmsDecode T C d y = p := by
  have h : ∃ p : Fin K × Fin L, ((C p.1).1, (C p.1).2 p.2, y) ∈ T ∧
      ∀ p' : Fin K × Fin L, ((C p'.1).1, (C p'.1).2 p'.2, y) ∈ T → p' = p := ⟨p, hp, huniq⟩
  rw [dmsDecode]
  split
  · next h' => exact (h'.choose_spec.2 p hp).symm
  · next h' => exact absurd h h'

omit [Fintype 𝒰] [Fintype α] [Fintype β] in
open Classical in
/-- A decoding error for `(k, l)` occurs only if the triple sent is not typical, a wrong satellite
codeword of the right cloud center is typical, or a codeword of a wrong cloud center is typical. -/
lemma dmsDecode_ne_le {n K L : ℕ} (T : Finset ((Fin n → 𝒰) × (Fin n → α) × (Fin n → β)))
    (C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)) (d : Fin K × Fin L) (y : Fin n → β)
    (k : Fin K) (l : Fin L) :
    (if dmsDecode T C d y ≠ (k, l) then (1 : ℝ) else 0) ≤
      (if ((C k).1, (C k).2 l, y) ∈ T then 0 else 1) +
        ∑ l' ∈ univ.erase l, (if ((C k).1, (C k).2 l', y) ∈ T then 1 else 0) +
        ∑ k' ∈ univ.erase k, ∑ l', (if ((C k').1, (C k').2 l', y) ∈ T then 1 else 0) := by
  have hind : ∀ t : (Fin n → 𝒰) × (Fin n → α) × (Fin n → β),
      0 ≤ (if t ∈ T then (1 : ℝ) else 0) := fun t => by split_ifs <;> norm_num
  have hS₁ := sum_nonneg fun l' (_ : l' ∈ univ.erase l) => hind ((C k).1, (C k).2 l', y)
  have hS₂ := sum_nonneg fun k' (_ : k' ∈ univ.erase k) =>
    sum_nonneg fun l' (_ : l' ∈ univ) => hind ((C k').1, (C k').2 l', y)
  have h0 : 0 ≤ (if ((C k).1, (C k).2 l, y) ∈ T then (0 : ℝ) else 1) := by split_ifs <;> norm_num
  by_cases hd : dmsDecode T C d y = (k, l)
  · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte]
    linarith
  simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases hw : ((C k).1, (C k).2 l, y) ∈ T
  swap
  · simp only [hw, ↓reduceIte]
    linarith
  obtain ⟨⟨k', l'⟩, hk', hne⟩ : ∃ p' : Fin K × Fin L, ((C p'.1).1, (C p'.1).2 p'.2, y) ∈ T ∧
      p' ≠ (k, l) := by
    by_contra hne
    push Not at hne
    exact hd (dmsDecode_eq d hw hne)
  simp only at hk'
  by_cases hk : k' = k
  · subst hk
    have hl : l' ∈ univ.erase l := mem_erase.2 ⟨fun h => hne (by rw [h]), mem_univ l'⟩
    have := single_le_sum (f := fun l' => if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0)
      (fun l' _ => hind _) hl
    simp only [hw, hk', ↓reduceIte] at this ⊢
    linarith
  have h1 := single_le_sum (f := fun l' => if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0)
    (fun l' _ => hind _) (mem_univ l')
  have h2 := single_le_sum
    (f := fun k' => ∑ l', if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0)
    (fun k' _ => sum_nonneg fun l' _ => hind _) (mem_erase.2 ⟨hk, mem_univ k'⟩)
  simp only [hw, hk', ↓reduceIte] at h1 h2 ⊢
  linarith

open Classical in
/-- Averaged over the random superposition codebooks, the probability that `(k, l)` is decoded
wrongly by receiver 1 is at most
`P(E₁₁) + (L - 1) e^{-n(I(X; Y | U) - 4ε)} + (K - 1) L e^{-n(I(U, X; Y) - 3ε)}`. -/
theorem sum_codebook_dmsDecode_le (hq : IsPMF q) (hV : IsChannel V) {n K L : ℕ}
    (ε : ℝ) (d : Fin K × Fin L) (k : Fin K) (l : Fin L) :
    ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF (superpositionColumnLaw q n L) K C *
        ∑ y, (if dmsDecode (superpositionTypicalSet q V n ε) C d y ≠ (k, l) then
          channelExt V n ((C k).2 l) y else 0) ≤
      superpositionAtypProb q V n ε + (L - 1) * exp (-(n * (superpositionInfoCond q V - 4 * ε))) +
        (K - 1) * L *
          exp (-(n * (I[Prod.fst : Prod.snd ; superpositionTriple q V] - 3 * ε))) := by
  set T := superpositionTypicalSet q V n ε
  set ν := superpositionColumnLaw q n L
  have hν := superpositionColumnLaw_isPMF hq n L
  set f₁ : (Fin n → 𝒰) → (Fin n → α) → ℝ :=
    fun u x => ∑ y, channelExt V n x y * (if (u, x, y) ∈ T then 0 else 1)
  set f₂ : (Fin n → 𝒰) → (Fin n → α) → (Fin n → α) → ℝ :=
    fun u x x' => ∑ y, channelExt V n x y * (if (u, x', y) ∈ T then 1 else 0)
  set f₃ : (Fin n → α) → (Fin n → 𝒰) → (Fin n → α) → ℝ :=
    fun x u' x' => ∑ y, channelExt V n x y * (if (u', x', y) ∈ T then 1 else 0)
  set I₁ := superpositionInfoCond q V
  set I₃ := I[Prod.fst : Prod.snd ; superpositionTriple q V]
  have hlam : ∀ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
      ∑ y, (if dmsDecode T C d y ≠ (k, l) then channelExt V n ((C k).2 l) y else 0) ≤
        f₁ (C k).1 ((C k).2 l) + ∑ l' ∈ univ.erase l, f₂ (C k).1 ((C k).2 l) ((C k).2 l') +
          ∑ k' ∈ univ.erase k, ∑ l', f₃ ((C k).2 l) (C k').1 ((C k').2 l') := by
    intro C
    have h2 : ∑ l' ∈ univ.erase l, f₂ (C k).1 ((C k).2 l) ((C k).2 l') =
        ∑ y, channelExt V n ((C k).2 l) y *
          ∑ l' ∈ univ.erase l, (if ((C k).1, (C k).2 l', y) ∈ T then 1 else 0) := by
      simp only [f₂, mul_sum]
      exact sum_comm
    have h3 : ∑ k' ∈ univ.erase k, ∑ l', f₃ ((C k).2 l) (C k').1 ((C k').2 l') =
        ∑ y, channelExt V n ((C k).2 l) y * ∑ k' ∈ univ.erase k, ∑ l',
          (if ((C k').1, (C k').2 l', y) ∈ T then 1 else 0) := by
      simp only [f₃, mul_sum]
      calc _ = ∑ k' ∈ univ.erase k, ∑ y, ∑ l', channelExt V n ((C k).2 l) y *
            (if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0) :=
            sum_congr rfl fun k' _ => sum_comm
        _ = _ := sum_comm
    rw [h2, h3]
    simp only [f₁, ← sum_add_distrib, ← mul_add]
    refine sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (dmsDecode_ne_le T C d y k l)
      (channelExt_nonneg hV ((C k).2 l) y)
    rw [mul_ite, mul_one, mul_zero] at this
    exact this
  have hA₁ : ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF ν K C *
      f₁ (C k).1 ((C k).2 l) ≤ superpositionAtypProb q V n ε := by
    have e := sum_iidPMF_eval hν k (fun c => f₁ c.1 (c.2 l))
    beta_reduce at e
    rw [e, sum_superpositionColumnLaw_eval hq l f₁]
    exact sum_superposition_atyp_le hq hV n ε
  have hA₂ : ∀ l' ∈ univ.erase l, ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
      iidPMF ν K C * f₂ (C k).1 ((C k).2 l) ((C k).2 l') ≤ exp (-(n * (I₁ - 4 * ε))) := by
    intro l' hl'
    have e := sum_iidPMF_eval hν k (fun c => f₂ c.1 (c.2 l) (c.2 l'))
    beta_reduce at e
    rw [e, sum_superpositionColumnLaw_eval₂ hq (Ne.symm (ne_of_mem_erase hl')) f₂]
    exact sum_superposition_satellite_le hq hV n ε
  have hA₃ : ∀ k' ∈ univ.erase k, ∀ l' : Fin L,
      ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
        iidPMF ν K C * f₃ ((C k).2 l) (C k').1 ((C k').2 l') ≤ exp (-(n * (I₃ - 3 * ε))) := by
    intro k' hk' l'
    have e := sum_iidPMF_eval₂ hν (Ne.symm (ne_of_mem_erase hk'))
      (fun c c' => f₃ (c.2 l) c'.1 (c'.2 l'))
    beta_reduce at e
    rw [e]
    have e' : ∀ c, ∑ c', superpositionColumnLaw q n L c * superpositionColumnLaw q n L c' *
        f₃ (c.2 l) c'.1 (c'.2 l') = superpositionColumnLaw q n L c *
          ∑ u', ∑ x', jointIid q n (u', x') * f₃ (c.2 l) u' x' := by
      intro c
      rw [← sum_superpositionColumnLaw_eval hq l' (f₃ (c.2 l)), mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    simp only [e']
    rw [sum_superpositionColumnLaw_eval hq l
      (fun _ x => ∑ u', ∑ x', jointIid q n (u', x') * f₃ x u' x')]
    refine le_trans (le_of_eq ?_) (sum_superposition_wrongCloud_le hq hV n ε)
    refine sum_congr rfl fun u _ => sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u' _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun x' _ => by ring
  have hw : ∀ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), 0 ≤ iidPMF ν K C :=
    fun C => iidPMF_nonneg hν.nonneg C
  have hcardL : (#((univ : Finset (Fin L)).erase l) : ℝ) = L - 1 := by
    rw [card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos l).ne'), Nat.cast_one]
  have hcardK : (#((univ : Finset (Fin K)).erase k) : ℝ) = K - 1 := by
    rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos k).ne'), Nat.cast_one]
  have hpull : ∀ {ι : Type} (s : Finset ι)
      (f : (Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)) → ι → ℝ),
      ∑ C, iidPMF ν K C * ∑ i ∈ s, f C i = ∑ i ∈ s, ∑ C, iidPMF ν K C * f C i := by
    intro ι s f
    simp only [mul_sum]
    exact sum_comm
  calc _ ≤ ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF ν K C *
        (f₁ (C k).1 ((C k).2 l) + ∑ l' ∈ univ.erase l, f₂ (C k).1 ((C k).2 l) ((C k).2 l') +
          ∑ k' ∈ univ.erase k, ∑ l', f₃ ((C k).2 l) (C k').1 ((C k').2 l')) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hlam C) (hw C)
    _ = ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF ν K C *
          f₁ (C k).1 ((C k).2 l) +
        ∑ l' ∈ univ.erase l, ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
          iidPMF ν K C * f₂ (C k).1 ((C k).2 l) ((C k).2 l') +
        ∑ k' ∈ univ.erase k, ∑ l',
          ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
            iidPMF ν K C * f₃ ((C k).2 l) (C k').1 ((C k').2 l') := by
        simp only [mul_add, sum_add_distrib]
        rw [hpull, hpull]
        congr 1
        exact sum_congr rfl fun k' _ => hpull _ _
    _ ≤ superpositionAtypProb q V n ε + ∑ _l' ∈ univ.erase l, exp (-(n * (I₁ - 4 * ε))) +
          ∑ _k' ∈ univ.erase k, ∑ _l' : Fin L, exp (-(n * (I₃ - 3 * ε))) :=
        add_le_add (add_le_add hA₁ (sum_le_sum hA₂)) (sum_le_sum fun k' hk' =>
          sum_le_sum fun l' _ => hA₃ k' hk' l')
    _ = _ := by
        simp only [sum_const, nsmul_eq_mul, hcardL, hcardK, card_univ, Fintype.card_fin]
        ring

end Decoder

/-! ### Codes -/

variable {α β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

/-- **Lecture 9 of [elgamal2010].** A code for the DM-BC with degraded message sets: an encoder of
`(m₀, m₁)`, a decoder of both messages at receiver 1 and a decoder of `m₀` at receiver 2. -/
structure DMSCode (M₀ M₁ n : ℕ) (α β₁ β₂ : Type*) where
  /-- The encoder `xⁿ(m₀, m₁)`. -/
  enc : Fin M₀ × Fin M₁ → Fin n → α
  /-- The decoder of receiver 1. -/
  dec₁ : (Fin n → β₁) → Fin M₀ × Fin M₁
  /-- The decoder of receiver 2. -/
  dec₂ : (Fin n → β₂) → Fin M₀

namespace DMSCode

variable {M₀ M₁ n : ℕ} (W) (c : DMSCode M₀ M₁ n α β₁ β₂)

open Classical in
/-- The probability of error `P{(M̂₀₁, M̂₁) ≠ (M₀, M₁) or M̂₀₂ ≠ M₀}`. -/
def errProb : ℝ :=
  (∑ w, ∑ y : Fin n → β₁ × β₂, if c.dec₁ (fun i => (y i).1) ≠ w ∨ c.dec₂ (fun i => (y i).2) ≠ w.1
    then channelExt W n (c.enc w) y else 0) / (M₀ * M₁)

open Classical in
/-- The probability of error at receiver 1. -/
def errProb₁ : ℝ :=
  (∑ w, ∑ y₁, if c.dec₁ y₁ ≠ w then channelExt (bcMarg₁ W) n (c.enc w) y₁ else 0) / (M₀ * M₁)

open Classical in
/-- The probability of error at receiver 2. -/
def errProb₂ : ℝ :=
  (∑ w, ∑ y₂, if c.dec₂ y₂ ≠ w.1 then channelExt (bcMarg₂ W) n (c.enc w) y₂ else 0) / (M₀ * M₁)

variable {W}

open Classical in
lemma errProb₁_eq : c.errProb₁ W = (∑ w, ∑ y : Fin n → β₁ × β₂,
    if c.dec₁ (fun i => (y i).1) ≠ w then channelExt W n (c.enc w) y else 0) / (M₀ * M₁) := by
  unfold errProb₁
  congr 1
  refine sum_congr rfl fun w _ => ?_
  have h := sum_channelExt_fst W (c.enc w) fun y₁ => if c.dec₁ y₁ ≠ w then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  exact h.symm

open Classical in
lemma errProb₂_eq : c.errProb₂ W = (∑ w, ∑ y : Fin n → β₁ × β₂,
    if c.dec₂ (fun i => (y i).2) ≠ w.1 then channelExt W n (c.enc w) y else 0) / (M₀ * M₁) := by
  unfold errProb₂
  congr 1
  refine sum_congr rfl fun w _ => ?_
  have h := sum_channelExt_snd W (c.enc w) fun y₂ => if c.dec₂ y₂ ≠ w.1 then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  exact h.symm

lemma errProb_le_add (hW : IsChannel W) : c.errProb W ≤ c.errProb₁ W + c.errProb₂ W := by
  classical
  rw [errProb₁_eq, errProb₂_eq, errProb, ← add_div, ← sum_add_distrib]
  refine div_le_div_of_nonneg_right (sum_le_sum fun w _ => ?_) (by positivity)
  rw [← sum_add_distrib]
  refine sum_le_sum fun y _ => ?_
  have hE := channelExt_nonneg hW (c.enc w) y
  split_ifs <;> simp_all

lemma errProb₁_le (hW : IsChannel W) : c.errProb₁ W ≤ c.errProb W := by
  classical
  rw [errProb₁_eq, errProb]
  refine div_le_div_of_nonneg_right (sum_le_sum fun w _ => sum_le_sum fun y _ => ?_) (by positivity)
  have hE := channelExt_nonneg hW (c.enc w) y
  split_ifs <;> simp_all

lemma errProb₂_le (hW : IsChannel W) : c.errProb₂ W ≤ c.errProb W := by
  classical
  rw [errProb₂_eq, errProb]
  refine div_le_div_of_nonneg_right (sum_le_sum fun w _ => sum_le_sum fun y _ => ?_) (by positivity)
  have hE := channelExt_nonneg hW (c.enc w) y
  split_ifs <;> simp_all

lemma errProb_nonneg (hW : IsChannel W) : 0 ≤ c.errProb W := by
  unfold errProb
  refine div_nonneg (sum_nonneg fun w _ => sum_nonneg fun y _ => ?_) (by positivity)
  split_ifs
  · exact channelExt_nonneg hW _ _
  · exact le_rfl

end DMSCode

/-- **Lecture 9 of [elgamal2010].** A rate pair `(R₀, R₁)`, in bits, is achievable for the DM-BC
with degraded message sets if there are `(2^{nR₀}, 2^{nR₁}, n)` codes whose probability of error
tends to `0`. -/
def IsAchievableDMSBits (W : α → β₁ × β₂ → ℝ) (R₀ R₁ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, DMSCode (2 ^ ⌈n * R₀⌉₊) (2 ^ ⌈n * R₁⌉₊) n α β₁ β₂,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Lecture 9 of [elgamal2010].** The capacity region with degraded message sets, in bits: the
closure of the achievable pairs of nonnegative rates. -/
def dmsCapacityRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  closure {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ IsAchievableDMSBits W R.1 R.2}

variable [Fintype α]

/-- **Theorem 1 of [elgamal2010], Lecture 9.** The region `R₀ ≤ I(U; Y₂)`, `R₁ ≤ I(X; Y₁ | U)`,
`R₀ + R₁ ≤ I(X; Y₁)` for some `p(u, x)`, with `R₀, R₁ ≥ 0` and `U` on `Fin k`. -/
def dmsRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧
    R.1 ≤ bcInfoUY₂ q W / log 2 ∧ R.2 ≤ bcInfoXY₁U q W / log 2 ∧
      R.1 + R.2 ≤ bcInfoXY₁ q W / log 2}

/-! ### Achievability -/

section Achievability

variable {𝒰 : Type*} [Fintype 𝒰] {q : 𝒰 × α → ℝ}

open Classical in
/-- Superposition coding with receiver 1 decoding both messages. -/
theorem exists_dms_code (hq : IsPMF q) (hW : IsChannel W) {M₀ M₁ n : ℕ} (h₀ : 0 < M₀) (h₁ : 0 < M₁)
    (ε : ℝ) :
    ∃ c : DMSCode M₀ M₁ n α β₁ β₂, c.errProb W ≤
      (superpositionAtypProb q (bcMarg₁ W) n ε +
          (M₁ - 1) * exp (-(n * (superpositionInfoCond q (bcMarg₁ W) - 4 * ε))) +
          (M₀ - 1) * M₁ *
            exp (-(n * (I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₁ W)] - 3 * ε)))) +
        ((1 - prob (jointIid (superpositionOut q (bcMarg₂ W)) n)
            (jointTypicalSet (superpositionOut q (bcMarg₂ W)) n ε)) +
          (M₀ - 1) *
            exp (-(n * (I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₂ W)] - 3 * ε)))) := by
  have hP := iidPMF_isPMF (superpositionColumnLaw_isPMF hq n M₁) M₀
  let code : (Fin M₀ → (Fin n → 𝒰) × (Fin M₁ → Fin n → α)) → DMSCode M₀ M₁ n α β₁ β₂ := fun C =>
    ⟨fun w => (C w.1).2 w.2,
      dmsDecode (superpositionTypicalSet q (bcMarg₁ W) n ε) C (⟨0, h₀⟩, ⟨0, h₁⟩),
      typicalDecode (jointTypicalSet (superpositionOut q (bcMarg₂ W)) n ε) (fun k => (C k).1)
        ⟨0, h₀⟩⟩
  have hM : (0 : ℝ) < M₀ * M₁ := by positivity
  have key : ∀ (e : (Fin M₀ → (Fin n → 𝒰) × (Fin M₁ → Fin n → α)) → Fin M₀ × Fin M₁ → ℝ) {b : ℝ},
      (∀ w, ∑ θ, iidPMF (superpositionColumnLaw q n M₁) M₀ θ * e θ w ≤ b) →
      ∑ θ, iidPMF (superpositionColumnLaw q n M₁) M₀ θ * ((∑ w, e θ w) / (M₀ * M₁)) ≤ b := by
    intro e b he
    have e1 : ∑ θ, iidPMF (superpositionColumnLaw q n M₁) M₀ θ * ((∑ w, e θ w) / (M₀ * M₁)) =
        (∑ w, ∑ θ, iidPMF (superpositionColumnLaw q n M₁) M₀ θ * e θ w) / (M₀ * M₁) := by
      simp only [mul_div_assoc', ← sum_div, mul_sum]
      congr 1
      exact sum_comm
    rw [e1, div_le_iff₀ hM]
    calc _ ≤ ∑ _w : Fin M₀ × Fin M₁, b := sum_le_sum fun w _ => he w
      _ = b * (M₀ * M₁) := by simp [sum_const, card_univ, mul_comm]
  have h := add_le_add (key (fun θ w => ∑ y₁, if (code θ).dec₁ y₁ ≠ w then
      channelExt (bcMarg₁ W) n ((code θ).enc w) y₁ else 0)
      fun w => sum_codebook_dmsDecode_le hq hW.bcMarg₁ ε _ w.1 w.2)
    (key (fun θ w => ∑ y₂, if (code θ).dec₂ y₂ ≠ w.1 then
      channelExt (bcMarg₂ W) n ((code θ).enc w) y₂ else 0)
      fun w => sum_codebook_superpositionCloudDecode_le hq hW.bcMarg₂ ε _ w.1 w.2)
  rw [← sum_add_distrib] at h
  simp_rw [← mul_add] at h
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hP h
  exact ⟨code C, ((code C).errProb_le_add hW).trans hC⟩

/-- **Achievability of Theorem 1 of Lecture 9.** A pair of nonnegative rates `(R₀, R₁)` is
achievable if `R₁ = 0` or `R₁ < I(X; Y₁ | U)`, and `R₀ = 0` or both `R₀ < I(U; Y₂)` and
`R₀ + R₁ < I(X; Y₁)`. -/
theorem isAchievableDMSBits_of_lt (hq : IsPMF q) (hW : IsChannel W) {R₀ R₁ : ℝ} (h₀ : 0 ≤ R₀)
    (h₁ : 0 ≤ R₁) (hs : R₁ = 0 ∨ R₁ * log 2 < superpositionInfoCond q (bcMarg₁ W))
    (hc : R₀ = 0 ∨ (R₀ * log 2 < I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₂ W)] ∧
      (R₀ + R₁) * log 2 < I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₁ W)])) :
    IsAchievableDMSBits W R₀ R₁ := by
  set I₁ := superpositionInfoCond q (bcMarg₁ W)
  set I₂ := I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₂ W)]
  set I₃ := I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₁ W)]
  obtain ⟨ε, hε, e₁, e₂⟩ : ∃ ε : ℝ, 0 < ε ∧ (R₁ = 0 ∨ R₁ * log 2 + 5 * ε ≤ I₁) ∧
      (R₀ = 0 ∨ (R₀ * log 2 + 5 * ε ≤ I₂ ∧ (R₀ + R₁) * log 2 + 5 * ε ≤ I₃)) := by
    obtain ⟨a, ha, hs'⟩ : ∃ a : ℝ, 0 < a ∧ (R₁ = 0 ∨ a ≤ I₁ - R₁ * log 2) := by
      rcases hs with h | h
      · exact ⟨1, one_pos, Or.inl h⟩
      · exact ⟨I₁ - R₁ * log 2, by linarith, Or.inr le_rfl⟩
    obtain ⟨b, hb, c, hc0, hc'⟩ : ∃ b : ℝ, 0 < b ∧ ∃ c : ℝ, 0 < c ∧
        (R₀ = 0 ∨ (b ≤ I₂ - R₀ * log 2 ∧ c ≤ I₃ - (R₀ + R₁) * log 2)) := by
      rcases hc with h | ⟨h, h'⟩
      · exact ⟨1, one_pos, 1, one_pos, Or.inl h⟩
      · exact ⟨I₂ - R₀ * log 2, by linarith, I₃ - (R₀ + R₁) * log 2, by linarith,
          Or.inr ⟨le_rfl, le_rfl⟩⟩
    obtain ⟨ε, hε, a₁, a₂, a₃⟩ := superposition_exists_slack ha hb hc0
    refine ⟨ε, hε, hs'.imp id fun h => by linarith, hc'.imp id fun h => ⟨by linarith [h.1],
      by linarith [h.2]⟩⟩
  have hP := tendsto_superposition_errBound hq hW.bcMarg₁ hW.bcMarg₂ hε
  have hcode : ∀ n : ℕ, ∃ c : DMSCode (2 ^ ⌈n * R₀⌉₊) (2 ^ ⌈n * R₁⌉₊) n α β₁ β₂,
      c.errProb W ≤ superpositionAtypProb q (bcMarg₁ W) n ε +
        (1 - prob (jointIid (superpositionOut q (bcMarg₂ W)) n)
          (jointTypicalSet (superpositionOut q (bcMarg₂ W)) n ε)) + 8 * exp (-(n * ε)) := by
    intro n
    obtain ⟨c, hc⟩ := exists_dms_code (n := n) hq hW (M₀ := 2 ^ ⌈n * R₀⌉₊)
      (M₁ := 2 ^ ⌈n * R₁⌉₊) (by positivity) (by positivity) ε
    refine ⟨c, hc.trans ?_⟩
    have hexp := (exp_pos (-(n * ε))).le
    have hM₁ := superposition_two_pow_ceil_sub_one_le n R₁
    have hM₀ := superposition_two_pow_ceil_sub_one_le n R₀
    have hM₁' := two_pow_ceil_le n h₁
    -- The first term.
    have t₁ : (((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (I₁ - 4 * ε))) ≤ 2 * exp (-(n * ε)) := by
      rcases e₁ with h | h
      · subst h
        simp only [mul_zero, Nat.ceil_zero, pow_zero, Nat.cast_one, sub_self, zero_mul]
        positivity
      · exact superposition_mul_exp_le (t := 4) hM₁ (by norm_num) (by linarith)
    have tt : (((2 ^ ⌈n * R₀⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (I₂ - 3 * ε))) +
        (((2 ^ ⌈n * R₀⌉₊ : ℕ) : ℝ) - 1) * ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) *
          exp (-(n * (I₃ - 3 * ε))) ≤ 6 * exp (-(n * ε)) := by
      rcases e₂ with h | ⟨h, h'⟩
      · subst h
        simp only [mul_zero, Nat.ceil_zero, pow_zero, Nat.cast_one, sub_self, zero_mul, add_zero]
        positivity
      · have a₁ := superposition_mul_exp_le (t := 3) (I := I₂) (ε := ε) hM₀ (by norm_num)
          (by linarith)
        have hprod : (((2 ^ ⌈n * R₀⌉₊ : ℕ) : ℝ) - 1) * ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) ≤
            4 * exp (n * ((R₀ + R₁) * log 2)) := by
          calc _ ≤ (2 * exp (n * (R₀ * log 2))) * (2 * exp (n * (R₁ * log 2))) :=
                mul_le_mul hM₀ hM₁' (Nat.cast_nonneg _) (by positivity)
            _ = _ := by
                rw [show (n : ℝ) * ((R₀ + R₁) * log 2) = n * (R₀ * log 2) + n * (R₁ * log 2) by
                  ring, exp_add]
                ring
        have a₂ := superposition_mul_exp_le (t := 3) (I := I₃) (ε := ε) hprod (by norm_num)
          (by linarith)
        linarith
    have hcast : ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) = ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) := rfl
    linarith
  choose c hc using hcode
  exact ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP
    (fun n => (c n).errProb_nonneg hW) hc⟩

end Achievability

/-! ### The converse -/

section Converse

variable {M₀ M₁ n : ℕ}

/-- The code as a broadcast code with the private message `M₁` for receiver 1 and the message `M₀`
for receiver 2. -/
def DMSCode.toBC (c : DMSCode M₀ M₁ n α β₁ β₂) : BCCode M₁ M₀ n α β₁ β₂ :=
  ⟨fun w => c.enc (w.2, w.1), fun y => (c.dec₁ y).2, c.dec₂⟩

omit [Fintype α] in
lemma DMSCode.errProb₁_toBC_le (hW : IsChannel W) (c : DMSCode M₀ M₁ n α β₁ β₂) :
    c.toBC.errProb₁ W ≤ c.errProb W := by
  classical
  refine le_trans ?_ (c.errProb₁_le hW)
  have e := (Equiv.prodComm (Fin M₁) (Fin M₀)).sum_comp fun w : Fin M₀ × Fin M₁ =>
    ∑ y₁, if c.dec₁ y₁ ≠ w then channelExt (bcMarg₁ W) n (c.enc w) y₁ else 0
  simp only [BCCode.errProb₁, DMSCode.errProb₁]
  rw [← e, mul_comm (M₁ : ℝ)]
  refine div_le_div_of_nonneg_right (sum_le_sum fun w _ => sum_le_sum fun y _ => ?_) (by positivity)
  have hE := channelExt_nonneg hW.bcMarg₁ (c.enc (w.2, w.1)) y
  have hne : (c.dec₁ y).2 ≠ w.1 → c.dec₁ y ≠ (w.2, w.1) := fun h h' => h (by rw [h'])
  change (if (c.dec₁ y).2 ≠ w.1 then channelExt (bcMarg₁ W) n (c.enc (w.2, w.1)) y else 0) ≤
    if c.dec₁ y ≠ (w.2, w.1) then channelExt (bcMarg₁ W) n (c.enc (w.2, w.1)) y else 0
  split_ifs with h h' h'
  · exact le_rfl
  · exact absurd (hne h) h'
  · exact hE
  · exact le_rfl

omit [Fintype α] in
lemma DMSCode.errProb₂_toBC_le (hW : IsChannel W) (c : DMSCode M₀ M₁ n α β₁ β₂) :
    c.toBC.errProb₂ W ≤ c.errProb W := by
  classical
  refine le_trans (le_of_eq ?_) (c.errProb₂_le hW)
  have e := (Equiv.prodComm (Fin M₁) (Fin M₀)).sum_comp fun w : Fin M₀ × Fin M₁ =>
    ∑ y₂, if c.dec₂ y₂ ≠ w.1 then channelExt (bcMarg₂ W) n (c.enc w) y₂ else 0
  simp only [BCCode.errProb₂, DMSCode.errProb₂]
  rw [← e, mul_comm (M₁ : ℝ)]
  rfl

/-- Fano's inequality for the two messages at receiver 1:
`log M₁ + log M₀ ≤ ∑ᵢ I(Xᵢ; Y₁ᵢ) + 2 log 2 + P (log M₁ + log M₀)`. -/
theorem DMSCode.log_add_log_le (hW : IsChannel W) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (c : DMSCode M₀ M₁ n α β₁ β₂) [Nonempty α] :
    log (M₁ : ℝ) + log (M₀ : ℝ) ≤
      ∑ i, bcInfoXY₁ (c.toBC.moreCapableLetterLaw W (fun w => w.2) i) W + 2 * log 2 +
        c.errProb W * (log (M₁ : ℝ) + log (M₀ : ℝ)) := by
  classical
  have : Nonempty (Fin M₀) := ⟨⟨0, hM₀⟩⟩
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have hl := log_pos one_lt_two
  have hA : 0 ≤ log (M₁ : ℝ) + log (M₀ : ℝ) :=
    add_nonneg (log_natCast_nonneg _) (log_natCast_nonneg _)
  set e' : ℝ := (∑ w : Fin M₁ × Fin M₀, ∑ y, if ((c.dec₁ y).2, (c.dec₁ y).1) ≠ id w then
    channelExt (bcMarg₁ W) n (c.toBC.enc w) y else 0) /
      (Fintype.card (Fin M₁ × Fin M₀) : ℝ) with he'
  have b := log_le_sum_mutualInfoOf_of_dec c.toBC.enc hW.bcMarg₁
    (id : Fin M₁ × Fin M₀ → Fin M₁ × Fin M₀) (dist_id _) (fun y => ((c.dec₁ y).2, (c.dec₁ y).1))
    (e := e') (by rw [he']; congr!)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul,
    log_mul (by exact_mod_cast hM₁.ne') (by exact_mod_cast hM₀.ne')] at b
  have hle : e' ≤ c.errProb W := by
    refine le_trans ?_ (c.errProb₁_le hW)
    have e := (Equiv.prodComm (Fin M₁) (Fin M₀)).sum_comp fun w : Fin M₀ × Fin M₁ =>
      ∑ y₁, if c.dec₁ y₁ ≠ w then channelExt (bcMarg₁ W) n (c.enc w) y₁ else 0
    rw [he', DMSCode.errProb₁, ← e, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.cast_mul, mul_comm (M₁ : ℝ)]
    refine le_of_eq (congrArg₂ _ (sum_congr rfl fun w _ => sum_congr rfl fun y _ => ?_) rfl)
    change (if ((c.dec₁ y).2, (c.dec₁ y).1) ≠ w then
      channelExt (bcMarg₁ W) n (c.enc (w.2, w.1)) y else 0) =
      if c.dec₁ y ≠ (w.2, w.1) then channelExt (bcMarg₁ W) n (c.enc (w.2, w.1)) y else 0
    refine if_congr ?_ rfl rfl
    constructor
    · exact fun h h' => h (by rw [h'])
    · exact fun h h' => h (by rw [← h'])
  have hI : ∀ i, mutualInfoOf (dist (uniformPMF (Fin M₁ × Fin M₀)) fun w => c.toBC.enc w i)
      (bcMarg₁ W) = bcInfoXY₁ (c.toBC.moreCapableLetterLaw W (fun w => w.2) i) W := fun i => by
    rw [bcInfoXY₁_eq]
    congr 1
    funext a
    have h1 := sum_dist_pair_left (c.toBC.degradedJointLaw W)
      (moreCapableV (fun w : Fin M₁ × Fin M₀ => w.2) (i : ℕ)) (fun z => c.toBC.enc z.1 i) a
    have h2 : dist (c.toBC.degradedJointLaw W) (fun z => c.toBC.enc z.1 i) =
        dist (uniformPMF (Fin M₁ × Fin M₀)) fun w => c.toBC.enc w i :=
      dist_codeLaw_comp_fst hW fun w => c.toBC.enc w i
    rw [← h2, ← h1]
    rfl
  simp_rw [hI] at b
  have h3 := mul_le_mul_of_nonneg_right hle hA
  linarith

/-- If `εₙ → 0`, the points `(max (a - εₙ) 0, max (b - εₙ) 0)` tend to `(a, b)` for `a, b ≥ 0`. -/
lemma tendsto_max_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => (max (a - ε n) 0, max (b - ε n) 0)) atTop (𝓝 (a, b)) := by
  have h1 : Tendsto (fun n => max (a - ε n) 0) atTop (𝓝 (max (a - 0) 0)) :=
    (tendsto_const_nhds.sub hε).max tendsto_const_nhds
  have h2 : Tendsto (fun n => max (b - ε n) 0) atTop (𝓝 (max (b - 0) 0)) :=
    (tendsto_const_nhds.sub hε).max tendsto_const_nhds
  rw [sub_zero, max_eq_left ha] at h1
  rw [sub_zero, max_eq_left hb] at h2
  exact h1.prodMk_nhds h2

/-- **Converse of Theorem 1 of Lecture 9.** With `Uᵢ = (M₀, Y₁^{i-1}, Y₂_{i+1}ⁿ)`, as in the
converse for the more capable DM-BC. -/
theorem IsAchievableDMSBits.mem_closure_dmsRegionBits [Nonempty α] (hW : IsChannel W) {R₀ R₁ : ℝ}
    (h₀ : 0 ≤ R₀) (h₁ : 0 ≤ R₁) (h : IsAchievableDMSBits W R₀ R₁) :
    (R₀, R₁) ∈ closure (dmsRegionBits W) := by
  obtain ⟨c, hc⟩ := h
  have hl := log_pos one_lt_two
  obtain ⟨ε, hε, hε0, hmem⟩ := exists_eps_mem_superpositionClosedRegionBits hW
    (fun n => (c n).toBC) hc (fun n => (c n).errProb₁_toBC_le hW)
    (fun n => (c n).errProb₂_toBC_le hW) (fun n => (c n).errProb_nonneg hW)
    fun n => (c n).log_add_log_le hW (by positivity) (by positivity)
  have h2ε : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by simpa using hε.const_mul 2
  refine mem_closure_of_tendsto (tendsto_max_sub h₀ h₁ h2ε)
    ((eventually_gt_atTop 0).mono fun n hn => ?_)
  obtain ⟨k, q, hq, e₁, e₂, e₃⟩ := hmem n hn
  simp only at e₁ e₂ e₃
  have hJ := bcJoint_isPMF hq hW
  have n₁ : 0 ≤ bcInfoXY₁U q W / log 2 := div_nonneg (condMutualInfo_nonneg hJ _ _ _) hl.le
  have n₂ : 0 ≤ bcInfoUY₂ q W / log 2 := div_nonneg (mutualInfo_nonneg hJ _ _) hl.le
  have n₃ : 0 ≤ bcInfoXY₁ q W / log 2 := div_nonneg (mutualInfo_nonneg hJ _ _) hl.le
  have hε' := hε0 n
  refine ⟨le_max_right _ _, le_max_right _ _, k, q, hq, max_le (by linarith) n₂,
    max_le (by linarith) n₁, ?_⟩
  rcases le_total (R₀ - 2 * ε n) 0 with a | a <;> rcases le_total (R₁ - 2 * ε n) 0 with b | b
  · rw [max_eq_right a, max_eq_right b]
    linarith
  · rw [max_eq_right a, max_eq_left b]
    linarith
  · rw [max_eq_left a, max_eq_right b]
    linarith
  · rw [max_eq_left a, max_eq_left b]
    linarith

/-- **Theorem 1 of [elgamal2010], Lecture 9.** The capacity region of the DM-BC with degraded
message sets is the set of `(R₀, R₁)` with `R₀ ≤ I(U; Y₂)`, `R₁ ≤ I(X; Y₁ | U)`,
`R₀ + R₁ ≤ I(X; Y₁)` for some `p(u, x)`, up to closure, as the cardinality of `U` is not bounded. -/
theorem dmsCapacityRegionBits_eq [Nonempty α] (hW : IsChannel W) :
    dmsCapacityRegionBits W = closure (dmsRegionBits W) := by
  have hl := log_pos one_lt_two
  refine Set.Subset.antisymm (closure_minimal ?_ isClosed_closure)
    (closure_minimal ?_ isClosed_closure)
  · rintro ⟨R₀, R₁⟩ ⟨h₀, h₁, h⟩
    exact h.mem_closure_dmsRegionBits hW h₀ h₁
  · rintro ⟨R₀, R₁⟩ ⟨h₀, h₁, k, q, hq, e₂, e₁, e₃⟩
    dsimp only at h₀ h₁ e₁ e₂ e₃
    rw [superposition_bcInfoUY₂_eq, le_div_iff₀ hl] at e₂
    rw [superposition_bcInfoXY₁U_eq hq hW, le_div_iff₀ hl] at e₁
    rw [superposition_bcInfoXY₁_eq hq hW, le_div_iff₀ hl] at e₃
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine mem_closure_of_tendsto (tendsto_max_sub h₀ h₁ ht) (Eventually.of_forall fun n => ?_)
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    set t := 1 / ((n : ℝ) + 1)
    have htl : 0 < t * log 2 := mul_pos hpos hl
    refine ⟨le_max_right _ _, le_max_right _ _, isAchievableDMSBits_of_lt hq hW (le_max_right _ _)
      (le_max_right _ _) ?_ ?_⟩
    · rcases le_or_gt (R₁ - t) 0 with b | b
      · exact Or.inl (max_eq_right b)
      · refine Or.inr ?_
        rw [max_eq_left b.le]
        nlinarith
    · rcases le_or_gt (R₀ - t) 0 with a | a
      · exact Or.inl (max_eq_right a)
      · refine Or.inr ?_
        rw [max_eq_left a.le]
        refine ⟨by nlinarith, ?_⟩
        rcases le_total (R₁ - t) 0 with b | b
        · rw [max_eq_right b]
          nlinarith
        · rw [max_eq_left b]
          nlinarith

/-! ### A form of the Nair–El Gamal outer bound -/

/-- The average over a uniform time-sharing variable. -/
private lemma sum_uniformPMF_mul {n : ℕ} (I : Fin n → ℝ) :
    ∑ i, uniformPMF (Fin n) i * I i = (∑ i, I i) / n := by
  simp only [uniformPMF, Fintype.card_fin]
  rw [← mul_sum, one_div_mul_eq_div]

/-- **Lecture 9 of [elgamal2010], page 9-40.** The form of the Nair–El Gamal outer bound for private
messages with `U₂ = U`, in bits: `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ I(U; Y₂) + I(X; Y₁ | U)`,
`R₁ ≤ I(X; Y₁)` for some `p(u, x)`. -/
def bcOuterRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧ R.2 ≤ bcInfoUY₂ q W / log 2 ∧
    R.1 + R.2 ≤ (bcInfoXY₁U q W + bcInfoUY₂ q W) / log 2 ∧ R.1 ≤ bcInfoXY₁ q W / log 2}

/-- **Lecture 9 of [elgamal2010], page 9-40.** Every achievable rate pair is in the outer bound, up
to closure, with `U = (Q, M₂, Y₁^{Q-1}, Y₂_{Q+1}ⁿ)`. -/
theorem IsAchievableBCBits.mem_closure_bcOuterRegionBits [Nonempty α] (hW : IsChannel W)
    {R₁ R₂ : ℝ} (h : IsAchievableBCBits W R₁ R₂) : (R₁, R₂) ∈ closure (bcOuterRegionBits W) := by
  classical
  obtain ⟨c, hc⟩ := h
  have hl := log_pos one_lt_two
  set P : ℕ → ℝ := fun n => (c n).errProb W with hPd
  have hP₁ : ∀ n, (c n).errProb₁ W ≤ P n := fun n =>
    (le_max_left _ _).trans ((c n).max_errProb_le hW)
  have hP₂ : ∀ n, (c n).errProb₂ W ≤ P n := fun n =>
    (le_max_right _ _).trans ((c n).max_errProb_le hW)
  have hP0 : ∀ n, 0 ≤ P n := fun n => ((c n).errProb₁_nonneg hW).trans (hP₁ n)
  refine mem_closure_of_sub_icEps (tendsto_icEps (R₁ := R₁) (R₂ := R₂) hP0 hc) fun n hn => ?_
  have hM₁ : 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := by positivity
  have hM₂ : 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := by positivity
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin (2 ^ ⌈(n : ℝ) * R₁⌉₊)) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin (2 ^ ⌈(n : ℝ) * R₂⌉₊)) := ⟨⟨0, hM₂⟩⟩
  set q := fun i => (c n).moreCapableLetterLaw W (fun w => w.2) i
  have hq : ∀ i, IsPMF (q i) := fun i => (c n).moreCapableLetterLaw_isPMF _ hW hM₁ hM₂ i
  have hw : IsPMF (uniformPMF (Fin n)) := uniformPMF_isPMF
  have hbar := degradedBCTimeShare_isPMF hw hq
  set qbar := degradedBCRelabelLaw (Fintype.equivFin _)
    (degradedBCTimeShare (uniformPMF (Fin n)) q)
  have hqbar : IsPMF qbar := degradedBCRelabelLaw_isPMF _ hbar
  have hXU : bcInfoXY₁U qbar W = (∑ i, bcInfoXY₁U (q i) W) / n := by
    rw [degradedBC_bcInfoXY₁U_relabel _ hbar hW, bcInfoXY₁U_degradedBCTimeShare hw hq hW,
      sum_uniformPMF_mul]
  have hUY : (∑ i, bcInfoUY₂ (q i) W) / n ≤ bcInfoUY₂ qbar W := by
    rw [degradedBC_bcInfoUY₂_relabel _ hbar hW]
    have h1 := sum_mul_bcInfoUY₂_le_degradedBCTimeShare (W := W) hw hq hW
    rwa [sum_uniformPMF_mul] at h1
  have hX : (∑ i, bcInfoXY₁ (q i) W) / n ≤ bcInfoXY₁ qbar W := by
    rw [moreCapable_bcInfoXY₁_relabel]
    have h1 := sum_mul_bcInfoXY₁_le_degradedBCTimeShare (W := W) hw hq hW
    rwa [sum_uniformPMF_mul] at h1
  set A := log (((2 : ℕ) ^ ⌈(n : ℝ) * R₁⌉₊ : ℕ) : ℝ)
  set B := log (((2 : ℕ) ^ ⌈(n : ℝ) * R₂⌉₊ : ℕ) : ℝ)
  have hA : 0 ≤ A := log_natCast_nonneg _
  have hB : 0 ≤ B := log_natCast_nonneg _
  have hAb := (log_two_pow_ceil_bounds n R₁).1
  have hBb := (log_two_pow_ceil_bounds n R₂).1
  have b₂ := (c n).log_le_sum_bcInfoUY₂_moreCapable hW hM₁ hM₂
  have b₁₂ := (c n).log_add_log_le_sum_bcInfoXY₁U_add_bcInfoUY₂ hW hM₁ hM₂
  -- Fano's inequality for the message of receiver 1.
  have hcard : ((Fintype.card (Fin (2 ^ ⌈(n : ℝ) * R₁⌉₊) × Fin (2 ^ ⌈(n : ℝ) * R₂⌉₊)) : ℕ) : ℝ) =
      ((2 ^ ⌈(n : ℝ) * R₁⌉₊ : ℕ) : ℝ) * ((2 ^ ⌈(n : ℝ) * R₂⌉₊ : ℕ) : ℝ) := by simp
  have b₁ := log_le_sum_mutualInfoOf_of_dec (c n).enc hW.bcMarg₁ Prod.fst
    dist_uniformPMF_prod_fst (c n).dec₁ (e := (c n).errProb₁ W) (by
      rw [hcard]
      simp only [BCCode.errProb₁]
      congr!)
  rw [Fintype.card_fin] at b₁
  have hI : ∀ i, mutualInfoOf (dist (uniformPMF _) fun w => (c n).enc w i) (bcMarg₁ W) =
      bcInfoXY₁ (q i) W := fun i => by
    rw [bcInfoXY₁_eq]
    congr 1
    funext a
    have h1 := sum_dist_pair_left ((c n).degradedJointLaw W)
      (moreCapableV (fun w : Fin (2 ^ ⌈(n : ℝ) * R₁⌉₊) × Fin (2 ^ ⌈(n : ℝ) * R₂⌉₊) => w.2) (i : ℕ))
      (fun z => (c n).enc z.1 i) a
    have h2 : dist ((c n).degradedJointLaw W) (fun z => (c n).enc z.1 i) =
        dist (uniformPMF _) fun w => (c n).enc w i :=
      dist_codeLaw_comp_fst hW fun w => (c n).enc w i
    rw [← h2, ← h1]
    rfl
  simp_rw [hI] at b₁
  have hPA := mul_le_mul_of_nonneg_right (hP₁ n) hA
  have hPB := mul_le_mul_of_nonneg_right (hP₂ n) hB
  have hP0A := mul_nonneg (hP0 n) hA
  have hP0B := mul_nonneg (hP0 n) hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hε := icEps_nonneg (R₁ := R₁) (R₂ := R₂) hP0 n
  have hdiv : ∀ {S I : ℝ}, S / n ≤ I → (1 / (n : ℝ) * S) / log 2 ≤ I / log 2 := fun {S I} h => by
    refine div_le_div_of_nonneg_right ?_ hl.le
    rwa [div_mul_eq_mul_div, one_mul]
  refine ⟨_, qbar, hqbar, ?_, ?_, ?_⟩
  · refine (sub_icEps_le hn (S := ∑ i, bcInfoUY₂ (q i) W) ?_).trans (hdiv hUY)
    nlinarith
  · have hs := sub_icEps_le (a := R₁ + R₂) (S := ∑ i, (bcInfoXY₁U (q i) W + bcInfoUY₂ (q i) W))
      (R₁ := R₁) (R₂ := R₂) (P := P) hn (by nlinarith)
    refine le_trans ?_ (hs.trans (hdiv ?_))
    · simp only
      linarith
    · rw [sum_add_distrib, add_div, ← hXU]
      linarith
  · refine (sub_icEps_le hn (S := ∑ i, bcInfoXY₁ (q i) W) ?_).trans (hdiv hX)
    nlinarith

end Converse

end InfoTheory
