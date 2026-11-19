/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayClasses
public import InfoTheoryLib.StateChannel.Compound

/-!
# The relay channel with lookahead

The relay without delay and the relay with unlimited lookahead of Lecture 17 of El Gamal and Kim.
The channel is `p(y₁ | x) p(y | x, x₁, y₁)`.

## Main definitions

* `rwdChannel W₁ W₂`: the relay channel whose relay alphabet is the set of maps `Y₁ → X₁`.
* `IsAchievableRWD`, `rwdCapacity`: rates of the relay without delay.
* `LookCode`, `LookCode.err`, `IsAchievableLook`, `lookCapacity`: codes for unlimited lookahead.
* `lookY W₁ W₂`: the channel from `(X, X₁)` to `Y` for a relay that ignores `Y₁`.

## Main statements

* `IsAchievableRWD.le_rcCutsetBound`: **Theorem 7**, the relay-without-delay cutset bound.
* `isAchievableRWD_instantaneous`: the instantaneous relaying lower bound, page 17-74.
* `isAchievableLook_noncausal`: the noncausal decode–forward lower bound, page 17-70.
* `IsAchievableLook.le_capacity`: an upper bound for unlimited lookahead.

## Implementation notes

A relay without delay sends at time `k` a function of `y₁,₀, …, y₁,ₖ₋₁` and of the current `y₁ₖ`.
This is a function of the past with values in the maps `Y₁ → X₁`, as the notes remark on page 17-73.
So its codes are the codes of the relay channel `rwdChannel W₁ W₂`, and all the results on relay
channels apply. Noncausal decode–forward is reduced to the compound channel theorem: a code for the
two channels from `(X, X₁)` to `Y₁` and to `Y` with one encoder gives the code of the relay.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X X₁ Y Y₁ : Type*}

/-! ### The relay without delay -/

section RWD

variable [Fintype Y] [Fintype Y₁]

/-- **Page 17-73 of [elgamal2010].** The relay channel with relay alphabet the maps `Y₁ → X₁`. -/
def rwdChannel (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) : X × (Y₁ → X₁) → Y × Y₁ → ℝ :=
  fun a o => W₁ a.1 o.2 * W₂ (a.1, a.2 o.2, o.2) o.1

variable {W₁ : X → Y₁ → ℝ} {W₂ : X × X₁ × Y₁ → Y → ℝ}

lemma rwdChannel_isChannel (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) :
    IsChannel (rwdChannel W₁ W₂) := by
  intro a
  refine ⟨fun o => mul_nonneg ((h₁ _).nonneg _) ((h₂ _).nonneg _), ?_⟩
  simp only [rwdChannel]
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [← mul_sum, (h₂ _).sum_eq_one, mul_one]
  exact (h₁ _).sum_eq_one

/-- **Page 17-73 of [elgamal2010].** A rate is achievable for the relay without delay. -/
def IsAchievableRWD (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) (R : ℝ) : Prop :=
  IsAchievableRC (rwdChannel W₁ W₂) R

/-- **Page 17-73 of [elgamal2010].** The capacity of the relay without delay, in bits. -/
def rwdCapacity (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) : ℝ :=
  rcCapacity (rwdChannel W₁ W₂)

variable [Fintype X] [Fintype X₁] [DecidableEq Y₁] [Nonempty X] [Nonempty X₁]

omit [Nonempty X] [Nonempty X₁] in
/-- **Theorem 7 of Lecture 17 of [elgamal2010], page 17-73: the relay-without-delay cutset bound**,
in the form `max_{p(x, x₁')} min {I(X; Y, Y₁ | X₁'), I(X, X₁'; Y)}` of the remark there, with `X₁'`
the maps `Y₁ → X₁`. -/
theorem IsAchievableRWD.le_rcCutsetBound (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) {R : ℝ}
    (h : IsAchievableRWD W₁ W₂ R) : R * log 2 ≤ rcCutsetBound (rwdChannel W₁ W₂) :=
  IsAchievableRC.le_rcCutsetBound (rwdChannel_isChannel h₁ h₂) h

omit [Fintype X₁] [DecidableEq Y₁] in
/-- **The instantaneous relaying lower bound, page 17-74 of [elgamal2010].** For `p(x)` and a map
`x₁(y₁)`, every rate below `I(X; Y)` is achievable by the relay without delay. -/
theorem isAchievableRWD_instantaneous [Finite X₁] [Nonempty Y] [Nonempty Y₁] (h₁ : IsChannel W₁)
    (h₂ : IsChannel W₂) {q : X → ℝ} (hq : IsPMF q) (φ : Y₁ → X₁) {R : ℝ}
    (h : R * log 2 < mutualInfoOf q fun x => bcMarg₁ (rwdChannel W₁ W₂) (x, φ)) :
    IsAchievableRWD W₁ W₂ R :=
  isAchievableRC_direct hq φ (rwdChannel_isChannel h₁ h₂) h

end RWD

/-! ### Unlimited lookahead -/

/-- **Page 17-68 of [elgamal2010].** A code for the relay with unlimited lookahead: at each time the
relay may use all of `y₁ⁿ`. -/
structure LookCode (M n : ℕ) (X X₁ Y Y₁ : Type*) where
  /-- The encoder. -/
  enc : Fin M → Fin n → X
  /-- The relay encoder. -/
  relay : Fin n → (Fin n → Y₁) → X₁
  /-- The decoder. -/
  dec : (Fin n → Y) → Fin M

section Look

variable [Fintype Y] [Fintype Y₁] {M n : ℕ} {W₁ : X → Y₁ → ℝ} {W₂ : X × X₁ × Y₁ → Y → ℝ}

/-- The probability of error for the message `m`. -/
def LookCode.rowErr (c : LookCode M n X X₁ Y Y₁) (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ)
    (m : Fin M) : ℝ :=
  ∑ y₁ : Fin n → Y₁, (∏ i, W₁ (c.enc m i) (y₁ i)) *
    ∑ y : Fin n → Y, (∏ i, W₂ (c.enc m i, c.relay i y₁, y₁ i) (y i)) * ind (c.dec y ≠ m)

/-- **Page 17-68 of [elgamal2010].** The average probability of error. -/
def LookCode.err (c : LookCode M n X X₁ Y Y₁) (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) : ℝ :=
  (∑ m, c.rowErr W₁ W₂ m) / M

/-- **Page 17-69 of [elgamal2010].** A rate is achievable for the relay with unlimited lookahead. -/
def IsAchievableLook (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, LookCode (2 ^ ⌈(n : ℝ) * R⌉₊) n X X₁ Y Y₁,
    Tendsto (fun n => (c n).err W₁ W₂) atTop (𝓝 0)

/-- **Page 17-69 of [elgamal2010].** The capacity of the relay with unlimited lookahead, in bits. -/
def lookCapacity (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) : ℝ :=
  sSup {R | IsAchievableLook W₁ W₂ R}

/-- The channel from `(X, X₁)` to `Y`, when `X₁` does not depend on `Y₁`. -/
def lookY (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) : X × X₁ → Y → ℝ :=
  fun a y => ∑ y₁, W₁ a.1 y₁ * W₂ (a.1, a.2, y₁) y

lemma lookY_isChannel (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) : IsChannel (lookY W₁ W₂) := by
  intro a
  refine ⟨fun y => sum_nonneg fun y₁ _ => mul_nonneg ((h₁ _).nonneg _) ((h₂ _).nonneg _), ?_⟩
  simp only [lookY]
  rw [sum_comm]
  simp_rw [← mul_sum, (h₂ _).sum_eq_one, mul_one]
  exact (h₁ _).sum_eq_one

/-- For a relay that decodes correctly, the channel to the receiver is memoryless. -/
lemma sum_prod_lookY (c : Fin n → X) (d : Fin n → X₁) (G : (Fin n → Y) → ℝ) :
    ∑ y₁ : Fin n → Y₁, (∏ i, W₁ (c i) (y₁ i)) *
      ∑ y : Fin n → Y, (∏ i, W₂ (c i, d i, y₁ i) (y i)) * G y =
      ∑ y : Fin n → Y, (∏ i, lookY W₁ W₂ (c i, d i) (y i)) * G y := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  have h : (∏ i, lookY W₁ W₂ (c i, d i) (y i)) =
      ∑ y₁ : Fin n → Y₁, ∏ i, W₁ (c i) (y₁ i) * W₂ (c i, d i, y₁ i) (y i) := by
    simp only [lookY]
    rw [prod_univ_sum, Fintype.piFinset_univ]
  rw [h, sum_mul]
  refine sum_congr rfl fun y₁ _ => ?_
  rw [prod_mul_distrib]
  ring

/-- The two channels of the compound channel, with outputs in `Y ⊕ Y₁`. -/
def lookCompound (W₁ : X → Y₁ → ℝ) (W₂ : X × X₁ × Y₁ → Y → ℝ) (s : Bool) (a : X × X₁) :
    Y ⊕ Y₁ → ℝ :=
  fun o => match s, o with
    | true, Sum.inl y => lookY W₁ W₂ a y
    | false, Sum.inr y₁ => W₁ a.1 y₁
    | _, _ => 0

lemma lookCompound_isChannel (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) (s : Bool) :
    IsChannel (lookCompound W₁ W₂ s) := by
  intro a
  cases s
  · refine ⟨?_, ?_⟩
    · rintro (y | y₁)
      · exact le_rfl
      · exact (h₁ _).nonneg _
    · simp [lookCompound, Fintype.sum_sum_type, (h₁ _).sum_eq_one]
  · refine ⟨?_, ?_⟩
    · rintro (y | y₁)
      · exact (lookY_isChannel h₁ h₂ a).nonneg _
      · exact le_rfl
    · simp [lookCompound, Fintype.sum_sum_type, (lookY_isChannel h₁ h₂ a).sum_eq_one]

omit [Fintype Y] [Fintype Y₁] in
/-- A sum over sequences in `A ⊕ B`, when only one summand has positive probability. -/
lemma sum_seq_sum_left {A B : Type*} [Fintype A] [Fintype B] {κ : Fin n → A ⊕ B → ℝ}
    (hκ : ∀ i b, κ i (Sum.inr b) = 0) (G : (Fin n → A ⊕ B) → ℝ) :
    ∑ o, (∏ i, κ i (o i)) * G o = ∑ y : Fin n → A,
      (∏ i, κ i (Sum.inl (y i))) * G fun i => Sum.inl (y i) := by
  classical
  refine (Finset.sum_of_injOn (fun y : Fin n → A => fun i => (Sum.inl (y i) : A ⊕ B))
    (fun a _ b _ h => funext fun i => Sum.inl_injective (congrFun h i))
    (fun _ _ => Finset.mem_coe.mpr (mem_univ _)) (fun o _ ho => ?_) fun _ _ => rfl).symm
  have hex : ∃ i, ∃ b, o i = Sum.inr b := by
    by_contra hcon
    push Not at hcon
    refine ho ?_
    have hl : ∀ i, ∃ a, o i = Sum.inl a := fun i => by
      cases hi : o i with
      | inl a => exact ⟨a, rfl⟩
      | inr b => exact absurd hi (hcon i b)
    choose y hy using hl
    exact ⟨y, mem_coe.mpr (mem_univ _), funext fun i => (hy i).symm⟩
  obtain ⟨i, b, hb⟩ := hex
  rw [prod_eq_zero (mem_univ i) (by rw [hb, hκ]), zero_mul]

omit [Fintype Y] [Fintype Y₁] in
/-- The same when the other summand has positive probability. -/
lemma sum_seq_sum_right {A B : Type*} [Fintype A] [Fintype B] {κ : Fin n → A ⊕ B → ℝ}
    (hκ : ∀ i a, κ i (Sum.inl a) = 0) (G : (Fin n → A ⊕ B) → ℝ) :
    ∑ o, (∏ i, κ i (o i)) * G o = ∑ y : Fin n → B,
      (∏ i, κ i (Sum.inr (y i))) * G fun i => Sum.inr (y i) := by
  classical
  refine (Finset.sum_of_injOn (fun y : Fin n → B => fun i => (Sum.inr (y i) : A ⊕ B))
    (fun a _ b _ h => funext fun i => Sum.inr_injective (congrFun h i))
    (fun _ _ => Finset.mem_coe.mpr (mem_univ _)) (fun o _ ho => ?_) fun _ _ => rfl).symm
  have hex : ∃ i, ∃ a, o i = Sum.inl a := by
    by_contra hcon
    push Not at hcon
    refine ho ?_
    have hl : ∀ i, ∃ b, o i = Sum.inr b := fun i => by
      cases hi : o i with
      | inl a => exact absurd hi (hcon i a)
      | inr b => exact ⟨b, rfl⟩
    choose y hy using hl
    exact ⟨y, mem_coe.mpr (mem_univ _), funext fun i => (hy i).symm⟩
  obtain ⟨i, a, ha⟩ := hex
  rw [prod_eq_zero (mem_univ i) (by rw [ha, hκ]), zero_mul]

/-- The code for the relay with unlimited lookahead from a code for the compound channel. -/
def lookOfCompound (c : ChannelCode M n (X × X₁) (Y ⊕ Y₁)) : LookCode M n X X₁ Y Y₁ where
  enc m i := (c.enc m i).1
  relay i y₁ := (c.enc (c.dec fun j => Sum.inr (y₁ j)) i).2
  dec y := c.dec fun j => Sum.inl (y j)

/-- The error of a message: the relay fails, or the receiver fails. -/
lemma lookOfCompound_rowErr_le (h₁ : IsChannel W₁) (h₂ : IsChannel W₂)
    (c : ChannelCode M n (X × X₁) (Y ⊕ Y₁)) (m : Fin M) :
    (lookOfCompound c).rowErr W₁ W₂ m ≤
      c.condErrProb (lookCompound W₁ W₂ false) m + c.condErrProb (lookCompound W₁ W₂ true) m := by
  classical
  have hcond : ∀ s, c.condErrProb (lookCompound W₁ W₂ s) m =
      ∑ o, (∏ i, lookCompound W₁ W₂ s (c.enc m i) (o i)) * ind (c.dec o ≠ m) := by
    intro s
    simp only [ChannelCode.condErrProb]
    refine sum_congr rfl fun o _ => ?_
    by_cases ho : c.dec o = m
    · rw [ind_of_neg (not_not.mpr ho), mul_zero]
      exact ite_eq_right (not_not.mpr ho)
    · rw [ind_of_pos ho, mul_one]
      exact ite_eq_left ho
  have hfalse : c.condErrProb (lookCompound W₁ W₂ false) m =
      ∑ y₁ : Fin n → Y₁, (∏ i, W₁ (c.enc m i).1 (y₁ i)) *
        ind (c.dec (fun j => Sum.inr (y₁ j)) ≠ m) := by
    rw [hcond, sum_seq_sum_right (κ := fun i => lookCompound W₁ W₂ false (c.enc m i))
      (fun i a => rfl)]
    rfl
  have htrue : c.condErrProb (lookCompound W₁ W₂ true) m =
      ∑ y : Fin n → Y, (∏ i, lookY W₁ W₂ (c.enc m i) (y i)) *
        ind (c.dec (fun j => Sum.inl (y j)) ≠ m) := by
    rw [hcond, sum_seq_sum_left (κ := fun i => lookCompound W₁ W₂ true (c.enc m i))
      (fun i a => rfl)]
    rfl
  rw [hfalse, htrue, ← sum_prod_lookY (W₁ := W₁) (W₂ := W₂) (fun i => (c.enc m i).1)
    (fun i => (c.enc m i).2), ← sum_add_distrib]
  refine sum_le_sum fun y₁ _ => ?_
  rw [← mul_add]
  have hW₁ : 0 ≤ ∏ i, W₁ (c.enc m i).1 (y₁ i) := prod_nonneg fun i _ => (h₁ _).nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hW₁
  have hprod : ∀ d : Fin n → X₁, 0 ≤ ∑ y : Fin n → Y,
      (∏ i, W₂ ((c.enc m i).1, d i, y₁ i) (y i)) * ind (c.dec (fun j => Sum.inl (y j)) ≠ m) :=
    fun d => sum_nonneg fun y _ =>
      mul_nonneg (prod_nonneg fun i _ => (h₂ _).nonneg _) (ind_nonneg _)
  by_cases hdec : c.dec (fun j => Sum.inr (y₁ j)) = m
  · rw [ind_of_neg (not_not.mpr hdec), zero_add]
    simp only [lookOfCompound, hdec]
    exact le_rfl
  · rw [ind_of_pos hdec]
    have hle : ∑ y : Fin n → Y,
      (∏ i, W₂ ((c.enc m i).1, (lookOfCompound c).relay i y₁, y₁ i) (y i)) *
        ind ((lookOfCompound c).dec y ≠ m) ≤ 1 := by
      have hch := seqChan_isChannel h₂ n
        (fun i => ((c.enc m i).1, (lookOfCompound c).relay i y₁, y₁ i))
      calc _ ≤ ∑ y : Fin n → Y, (∏ i, W₂ ((c.enc m i).1, (lookOfCompound c).relay i y₁, y₁ i)
            (y i)) * 1 := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ind_le_one _)
              (prod_nonneg fun i _ => (h₂ _).nonneg _)
        _ = 1 := by
            simp only [mul_one]
            exact hch.sum_eq_one
    have := hprod fun i => (c.enc m i).2
    exact hle.trans (by linarith)

variable [Fintype X] [Fintype X₁] [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]

omit [Nonempty Y] [Nonempty Y₁] in
/-- **The noncausal decode–forward lower bound, page 17-70 of [elgamal2010].** For any input law,
every rate `R`, in bits, with `R log 2 < I(X; Y₁)` and `R log 2 < I(X, X₁; Y)` is achievable. -/
theorem isAchievableLook_noncausal (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) {p : X × X₁ → ℝ}
    (hp : IsPMF p) {R : ℝ} (hR₁ : R * log 2 < mutualInfoOf (dist p Prod.fst) W₁)
    (hR₂ : R * log 2 < mutualInfoOf p (lookY W₁ W₂)) : IsAchievableLook W₁ W₂ R := by
  classical
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hC := lookCompound_isChannel h₁ h₂
  have hYc := lookY_isChannel h₁ h₂
  -- the informations of the two channels
  have hI₁ : mutualInfoOf p (lookCompound W₁ W₂ false) = mutualInfoOf (dist p Prod.fst) W₁ := by
    rw [← mutualInfoOf_comp hp h₁ Prod.fst]
    have hJ := jointOf_isPMF hp fun a : X × X₁ => h₁ a.1
    rw [mutualInfoOf, mutualInfoOf]
    have e₁ := mutualInfo_congr_right hJ (Prod.fst : (X × X₁) × Y₁ → X × X₁)
      (Y := Prod.snd) (Y' := fun z => (Sum.inr z.2 : Y ⊕ Y₁)) (fun t => Sum.inr t)
      Sum.inr_injective fun _ => rfl
    rw [Function.comp_def]
    refine Eq.trans ?_ e₁
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    funext ⟨a, o⟩
    have hinj : Function.Injective (pair (Prod.fst : (X × X₁) × Y₁ → X × X₁)
        fun z => (Sum.inr z.2 : Y ⊕ Y₁)) := fun u v he => by
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext h₁ (Sum.inr_injective h₂)
    cases o with
    | inr y₁ =>
      have := dist_comp_of_injective (jointOf p fun a : X × X₁ => W₁ a.1) id hinj (a, y₁)
      rw [dist_id] at this
      exact this.symm
    | inl y =>
      simp only [jointOf, lookCompound, mul_zero]
      refine (sum_eq_zero fun z _ => ite_eq_right fun he => ?_).symm
      exact absurd (congrArg Prod.snd he) (by simp [pair])
  have hI₂ : mutualInfoOf p (lookCompound W₁ W₂ true) = mutualInfoOf p (lookY W₁ W₂) := by
    have hJ := jointOf_isPMF hp hYc
    rw [mutualInfoOf, mutualInfoOf]
    have e₁ := mutualInfo_congr_right hJ (Prod.fst : (X × X₁) × Y → X × X₁)
      (Y := Prod.snd) (Y' := fun z => (Sum.inl z.2 : Y ⊕ Y₁)) (fun t => Sum.inl t)
      Sum.inl_injective fun _ => rfl
    refine Eq.trans ?_ e₁
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    funext ⟨a, o⟩
    have hinj : Function.Injective (pair (Prod.fst : (X × X₁) × Y → X × X₁)
        fun z => (Sum.inl z.2 : Y ⊕ Y₁)) := fun u v he => by
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext h₁ (Sum.inl_injective h₂)
    cases o with
    | inl y =>
      have := dist_comp_of_injective (jointOf p (lookY W₁ W₂)) id hinj (a, y)
      rw [dist_id] at this
      exact this.symm
    | inr y₁ =>
      simp only [jointOf, lookCompound, mul_zero]
      refine (sum_eq_zero fun z _ => ite_eq_right fun he => ?_).symm
      exact absurd (congrArg Prod.snd he) (by simp [pair])
  -- the compound channel
  have hval : R * log 2 < compoundValue (lookCompound W₁ W₂) := by
    have hbdd : BddAbove {v | ∃ q, IsPMF q ∧ compoundInfo (lookCompound W₁ W₂) q = v} :=
      bddAbove_compoundValue hC
    refine lt_of_lt_of_le ?_ (le_csSup hbdd ⟨p, hp, rfl⟩)
    refine (lt_inf'_iff _).mpr fun s _ => ?_
    cases s
    · rwa [hI₁]
    · rwa [hI₂]
  obtain ⟨c, hc⟩ := isAchievableCompound_of_lt hC ((lt_div_iff₀ hlog2).mpr hval)
  refine ⟨fun n => lookOfCompound (c n), ?_⟩
  have hsqueeze : ∀ n : ℕ, (lookOfCompound (c n)).err W₁ W₂ ≤
      2 * compoundErr (lookCompound W₁ W₂) (c n) := by
    intro n
    have hM : (0 : ℝ) < ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by positivity
    have h₀ := compoundErr_ge (lookCompound W₁ W₂) (c n) false
    have h₁' := compoundErr_ge (lookCompound W₁ W₂) (c n) true
    simp only [LookCode.err]
    rw [div_le_iff₀ hM]
    have hsum : ∑ m, (lookOfCompound (c n)).rowErr W₁ W₂ m ≤
        (c n).avgErrProb (lookCompound W₁ W₂ false) * ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) +
        (c n).avgErrProb (lookCompound W₁ W₂ true) * ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by
      simp only [ChannelCode.avgErrProb]
      rw [div_mul_cancel₀ _ hM.ne', div_mul_cancel₀ _ hM.ne', ← sum_add_distrib]
      exact sum_le_sum fun m _ => lookOfCompound_rowErr_le h₁ h₂ _ m
    nlinarith
  have hnonneg : ∀ n : ℕ, 0 ≤ (lookOfCompound (c n)).err W₁ W₂ := fun n =>
    div_nonneg (sum_nonneg fun m _ => sum_nonneg fun y₁ _ => mul_nonneg
      (prod_nonneg fun i _ => (h₁ _).nonneg _) (sum_nonneg fun y _ => mul_nonneg
        (prod_nonneg fun i _ => (h₂ _).nonneg _) (ind_nonneg _))) (Nat.cast_nonneg _)
  have hlim : Tendsto (fun n => 2 * compoundErr (lookCompound W₁ W₂) (c n)) atTop (𝓝 0) := by
    simpa using hc.const_mul 2
  exact squeeze_zero hnonneg hsqueeze hlim

omit [Nonempty Y] in
/-- **An upper bound for unlimited lookahead.** Given the message and `y₁ⁿ`, the receiver sees the
output of the memoryless channel `p(y | x, x₁, y₁)`. So its rate is at most the capacity of this
channel. -/
theorem IsAchievableLook.le_capacity (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) {R : ℝ}
    (h : IsAchievableLook W₁ W₂ R) : R * log 2 ≤ capacity W₂ := by
  classical
  obtain ⟨c, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R⌉₊ := fun n => by positivity
  -- for one code
  have key : ∀ n : ℕ, (1 - (c n).err W₁ W₂) * log ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) ≤
      log 2 + n * capacity W₂ ∧ (c n).err W₁ W₂ ≤ 1 := by
    intro n
    set M := 2 ^ ⌈(n : ℝ) * R⌉₊ with hM
    have hne : Nonempty (Fin M) := ⟨⟨0, hpos n⟩⟩
    let ν : Fin M × (Fin n → Y₁) → ℝ := fun w =>
      uniformPMF (Fin M) w.1 * ∏ i, W₁ ((c n).enc w.1 i) (w.2 i)
    have hν : IsPMF ν := by
      refine ⟨fun w => mul_nonneg (uniformPMF_isPMF.nonneg _)
        (prod_nonneg fun i _ => (h₁ _).nonneg _), ?_⟩
      rw [Fintype.sum_prod_type]
      simp_rw [ν, ← mul_sum]
      have hs : ∀ m : Fin M, ∑ y₁ : Fin n → Y₁, ∏ i, W₁ ((c n).enc m i) (y₁ i) = 1 := fun m =>
        (seqChan_isChannel h₁ n ((c n).enc m)).sum_eq_one
      simp_rw [hs, mul_one]
      exact uniformPMF_isPMF.sum_eq_one
    let d : X × X₁ × Y₁ := (Classical.arbitrary X, Classical.arbitrary X₁, Classical.arbitrary Y₁)
    let enc : ∀ k, Fin M × (Fin n → Y₁) → (Fin k → Y) → X × X₁ × Y₁ := fun k w _ =>
      if hk : k < n then ((c n).enc w.1 ⟨k, hk⟩, (c n).relay ⟨k, hk⟩ w.2, w.2 ⟨k, hk⟩) else d
    let μ := fbLaw ν W₂ enc n
    have hμ : IsPMF μ := fbLaw_isPMF hν h₂ n
    have hlaw : ∀ w y, μ (w, y) = ν w * ∏ i : Fin n,
        W₂ ((c n).enc w.1 i, (c n).relay i w.2, w.2 i) (y i) := by
      intro w y
      simp only [μ]
      rw [fbLaw_eq_prod]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      simp only [enc, dite_eq_left i.isLt]
    let Mv : (Fin M × (Fin n → Y₁)) × (Fin n → Y) → Fin M := fun z => z.1.1
    -- Fano's inequality
    have hF := fano_weak hμ Mv Prod.snd (c n).dec
    have hE : InfoTheory.errProb μ Mv Prod.snd (c n).dec = (c n).err W₁ W₂ := by
      simp only [InfoTheory.errProb, LookCode.err, LookCode.rowErr, Fintype.sum_prod_type]
      rw [sum_div]
      refine sum_congr rfl fun m _ => ?_
      rw [sum_div]
      refine sum_congr rfl fun y₁ _ => ?_
      rw [mul_sum, sum_div]
      refine sum_congr rfl fun y _ => ?_
      have hu : uniformPMF (Fin M) m = 1 / (M : ℝ) := by simp [uniformPMF]
      rw [hlaw]
      simp only [ν, hu, Mv]
      by_cases hd : (c n).dec y = m
      · rw [ind_of_neg (not_not.mpr hd), mul_zero, mul_zero, zero_div]
        exact ite_eq_right (not_not.mpr hd)
      · rw [ind_of_pos hd, mul_one, ite_eq_left hd]
        ring
    have hH : H[Mv ; μ] = log M := by
      have hd₁ : dist μ Mv = uniformPMF (Fin M) := by
        have e : Mv = Prod.fst ∘ Prod.fst := rfl
        rw [e, dist_comp_eq, dist_fst_fbLaw h₂ n]
        funext m
        simp only [dist, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single m]
        · have hs : ∑ y₁ : Fin n → Y₁, ∏ i, W₁ ((c n).enc m i) (y₁ i) = 1 :=
            (seqChan_isChannel h₁ n ((c n).enc m)).sum_eq_one
          simp only [ite_true, ν, ← mul_sum]
          rw [hs, mul_one]
        · intro m' _ hm'
          exact sum_eq_zero fun y₁ _ => ite_eq_right hm'
        · simp
      rw [entropyRV, hd₁, entropy_uniformPMF, Fintype.card_fin]
    have hI := mutualInfo_eq_entropy_sub_condEntropy hμ Mv Prod.snd
    have hI₂ : I[Mv : Prod.snd ; μ] ≤ n * capacity W₂ := by
      have h₁' := mutualInfo_comp_le hμ (Prod.snd : (Fin M × (Fin n → Y₁)) × (Fin n → Y) → _)
        Prod.fst (Prod.fst : Fin M × (Fin n → Y₁) → Fin M)
      rw [mutualInfo_comm hμ Mv]
      refine h₁'.trans ?_
      rw [mutualInfo_comm hμ]
      exact mutualInfo_fbLaw_le hν h₂ n
    have hcard : (Fintype.card (Fin M) : ℝ) = M := by simp
    rw [hE, hcard] at hF
    have hE1 : (c n).err W₁ W₂ ≤ 1 := by
      rw [← hE]
      exact errProb_le_one hμ _ _ _
    exact ⟨by linarith, hE1⟩
  refine le_of_converse_bound hc (fun n => (key n).2) fun n _ => ?_
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hceil : (⌈exp (n * (R * log 2))⌉₊ : ℝ) ≤ ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by
    have hle₂ : exp (n * (R * log 2)) ≤ ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by
      push_cast
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine exp_le_exp.mpr ?_
      have := Nat.le_ceil ((n : ℝ) * R)
      have hl : 0 < log 2 := log_pos (by norm_num)
      nlinarith
    exact_mod_cast Nat.ceil_le.mpr hle₂
  have hexp : (0 : ℝ) < ⌈exp (n * (R * log 2))⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr (exp_pos _)
  have hlog := log_le_log hexp hceil
  have h1 : 0 ≤ 1 - (c n).err W₁ W₂ := sub_nonneg.mpr (key n).2
  exact (mul_le_mul_of_nonneg_left hlog h1).trans (key n).1

end Look

end InfoTheory
