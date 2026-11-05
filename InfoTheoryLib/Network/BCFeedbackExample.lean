/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCFeedback

/-!
# Dueck's example: feedback enlarges the capacity region of a broadcast channel

Pages 18-40 and 18-41 of the notes: `Y₁ = (X₀, X₁ ⊕ Z)` and `Y₂ = (X₀, X₂ ⊕ Z)`, for
`Z ∼ Bern(1/2)`. Without feedback, the capacity region is `R₁ + R₂ ≤ 1`. With feedback, the sender
learns the noise and broadcasts it on `X₀`, and `(1, 1)` is achievable.

## Main definitions

* `dueckW`: the channel.
* `dueckCode`: the code with feedback.

## Main statements

* `isAchievableBCFB_dueck`, `one_one_mem_bcfbCapacityRegion`: `(1, 1)` is achievable with feedback.
* `dueck_mul_le`: for one code without feedback, `(1 - 2 Pₑ) M₁ M₂ ≤ 2ⁿ`.
* `bcCapacityRegionBits_dueck_subset`, `subset_bcCapacityRegionBits_dueck`: the region without
  feedback, for nonnegative rates.

## Implementation notes

The bound without feedback is by counting, and so it is a strong converse: since `X₁ ⊕ Z` is uniform
and independent of the input, some fixed value of it gives a decoder from `X₀ⁿ` alone.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- The input alphabet. -/
abbrev DueckX : Type := Bool × Bool × Bool

/-- The output alphabet of a receiver. -/
abbrev DueckY : Type := Bool × Bool

open Classical in
/-- **Page 18-40 of [elgamal2010].** The channel: `Y₁ = (X₀, X₁ ⊕ Z)`, `Y₂ = (X₀, X₂ ⊕ Z)`. -/
def dueckW (x : DueckX) (o : DueckY × DueckY) : ℝ :=
  ∑ b : Bool, 2⁻¹ * if o = ((x.1, xor x.2.1 b), (x.1, xor x.2.2 b)) then 1 else 0

lemma dueckW_isChannel : IsChannel dueckW := fun x => by
  classical
  refine ⟨fun o => sum_nonneg fun b _ => mul_nonneg (by norm_num) (by split_ifs <;> norm_num), ?_⟩
  simp only [dueckW]
  rw [sum_comm]
  simp_rw [← mul_sum]
  simp

/-- A positive probability means that the output has the form of the channel. -/
lemma dueckW_ne_zero {x : DueckX} {o : DueckY × DueckY} (h : dueckW x o ≠ 0) :
    ∃ b : Bool, o = ((x.1, xor x.2.1 b), (x.1, xor x.2.2 b)) := by
  classical
  by_contra hc
  push Not at hc
  exact h (sum_eq_zero fun b _ => by rw [ite_eq_right (hc b), mul_zero])

/-! ### The code with feedback -/

section Feedback

variable {a₁ a₂ n : ℕ}

/-- A bit of a message, at a time. -/
def dueckBit {a : ℕ} (t : Fin a → Bool) (k : ℕ) : Bool := if h : k < a then t ⟨k, h⟩ else false

/-- The equivalence of messages and bit sequences. -/
def dueckEq (a : ℕ) : Fin (2 ^ a) ≃ (Fin a → Bool) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

/-- **Page 18-41 of [elgamal2010].** The code with feedback: at time `k + 1`, the sender sends the
noise of time `k` on `X₀`. -/
def dueckCode (a₁ a₂ n : ℕ) : BCFBCode (2 ^ a₁) (2 ^ a₂) n DueckX DueckY DueckY where
  enc k w z := (match k, z with
      | 0, _ => false
      | j + 1, z => xor (z (Fin.last j)).1.2 (dueckBit (dueckEq a₁ w.1) j),
    dueckBit (dueckEq a₁ w.1) k, dueckBit (dueckEq a₂ w.2) k)
  dec₁ y := (dueckEq a₁).symm fun i =>
    if h : (i : ℕ) + 1 < n then xor (y ⟨i, by omega⟩).2 (y ⟨i + 1, h⟩).1 else false
  dec₂ y := (dueckEq a₂).symm fun i =>
    if h : (i : ℕ) + 1 < n then xor (y ⟨i, by omega⟩).2 (y ⟨i + 1, h⟩).1 else false

/-- On a run of positive probability the receivers decode correctly. -/
lemma dueckCode_good (h₁ : a₁ + 1 ≤ n) (h₂ : a₂ + 1 ≤ n) (w : Fin (2 ^ a₁) × Fin (2 ^ a₂))
    (z : Fin n → DueckY × DueckY) (hz : (dueckCode a₁ a₂ n).law dueckW (w, z) ≠ 0) :
    (dueckCode a₁ a₂ n).dec₁ (fun i => (z i).1) = w.1 ∧
      (dueckCode a₁ a₂ n).dec₂ (fun i => (z i).2) = w.2 := by
  classical
  simp only [BCFBCode.law] at hz
  rw [fbLaw_eq_prod] at hz
  have hprod := right_ne_zero_of_mul hz
  have hi : ∀ i : Fin n, ∃ b : Bool, z i =
      ((((dueckCode a₁ a₂ n).enc i w (fbPre i z)).1,
          xor ((dueckCode a₁ a₂ n).enc i w (fbPre i z)).2.1 b),
        (((dueckCode a₁ a₂ n).enc i w (fbPre i z)).1,
          xor ((dueckCode a₁ a₂ n).enc i w (fbPre i z)).2.2 b)) := fun i =>
    dueckW_ne_zero (prod_ne_zero_iff.mp hprod i (mem_univ i))
  have hstep : ∀ (j : ℕ) (hj : j + 1 < n), ∃ b : Bool,
      (z ⟨j, by omega⟩).1.2 = xor (dueckBit (dueckEq a₁ w.1) j) b ∧
      (z ⟨j, by omega⟩).2.2 = xor (dueckBit (dueckEq a₂ w.2) j) b ∧
      (z ⟨j + 1, hj⟩).1.1 = b ∧ (z ⟨j + 1, hj⟩).2.1 = b := by
    intro j hj
    obtain ⟨b, hb⟩ := hi ⟨j, by omega⟩
    obtain ⟨b', hb'⟩ := hi ⟨j + 1, hj⟩
    have hb₁ : (z ⟨j, by omega⟩).1.2 = xor (dueckBit (dueckEq a₁ w.1) j) b := by
      rw [hb]
      rfl
    have hb₂ : (z ⟨j, by omega⟩).2.2 = xor (dueckBit (dueckEq a₂ w.2) j) b := by
      rw [hb]
      rfl
    have hx : ((dueckCode a₁ a₂ n).enc (j + 1) w (fbPre ⟨j + 1, hj⟩ z)).1 = b := by
      change xor (z ⟨j, by omega⟩).1.2 (dueckBit (dueckEq a₁ w.1) j) = b
      rw [hb₁]
      cases dueckBit (dueckEq a₁ w.1) j <;> cases b <;> rfl
    refine ⟨b, hb₁, hb₂, ?_, ?_⟩
    · rw [hb']
      exact hx
    · rw [hb']
      exact hx
  have hbit : ∀ {a : ℕ} (t : Fin a → Bool) (i : Fin a), dueckBit t i = t i := by
    intro a t i
    simp [dueckBit]
  constructor
  · simp only [dueckCode]
    rw [Equiv.symm_apply_eq]
    funext i
    have hin : (i : ℕ) + 1 < n := by have := i.2; omega
    rw [dite_eq_left hin]
    obtain ⟨b, h₃, -, h₅, -⟩ := hstep i hin
    rw [h₃, h₅, hbit]
    cases dueckEq a₁ w.1 i <;> cases b <;> rfl
  · simp only [dueckCode]
    rw [Equiv.symm_apply_eq]
    funext i
    have hin : (i : ℕ) + 1 < n := by have := i.2; omega
    rw [dite_eq_left hin]
    obtain ⟨b, -, h₄, -, h₆⟩ := hstep i hin
    rw [h₄, h₆, hbit]
    cases dueckEq a₂ w.2 i <;> cases b <;> rfl

/-- The code has no errors, if the messages are shorter than the block. -/
lemma dueckCode_errProb (h₁ : a₁ + 1 ≤ n) (h₂ : a₂ + 1 ≤ n) :
    (dueckCode a₁ a₂ n).errProb dueckW = 0 := by
  classical
  simp only [BCFBCode.errProb, InfoTheory.errProb]
  refine sum_eq_zero fun t _ => ?_
  by_cases ht : (dueckCode a₁ a₂ n).law dueckW t = 0
  · rw [ht]
    simp
  · obtain ⟨w, z⟩ := t
    obtain ⟨h₃, h₄⟩ := dueckCode_good h₁ h₂ w z ht
    refine ite_eq_right fun hc => ?_
    exact absurd (Prod.ext h₃ h₄) hc

/-- **Page 18-41 of [elgamal2010].** Every rate pair `R₁, R₂ < 1` is achievable with feedback. -/
theorem isAchievableBCFB_dueck {R₁ R₂ : ℝ} (hR₁ : R₁ < 1) (hR₂ : R₂ < 1) :
    IsAchievableBCFB dueckW R₁ R₂ := by
  refine ⟨fun n => dueckCode ⌈(n : ℝ) * R₁⌉₊ ⌈(n : ℝ) * R₂⌉₊ n, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ R : ℝ, R < 1 → ∀ᶠ n : ℕ in atTop, ⌈(n : ℝ) * R⌉₊ + 1 ≤ n := by
    intro R hR
    have hg : 0 < 1 - max R 0 := sub_pos.mpr (max_lt hR one_pos)
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) * (1 - max R 0)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hg
    filter_upwards [hlim.eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h₀ : (0 : ℝ) ≤ (n : ℝ) * max R 0 := mul_nonneg hn0 (le_max_right _ _)
    have h₁ : (n : ℝ) * R ≤ (n : ℝ) * max R 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hn0
    have h₂ : (⌈(n : ℝ) * R⌉₊ : ℝ) ≤ ⌈(n : ℝ) * max R 0⌉₊ := by exact_mod_cast Nat.ceil_mono h₁
    have h₃ := Nat.ceil_lt_add_one h₀
    have h₄ : ((⌈(n : ℝ) * R⌉₊ : ℝ)) + 1 ≤ n := by nlinarith
    exact_mod_cast h₄
  filter_upwards [hev R₁ hR₁, hev R₂ hR₂] with n h₁ h₂
  exact (dueckCode_errProb h₁ h₂).symm

/-- **Page 18-41 of [elgamal2010].** `(1, 1)` is in the capacity region with feedback. -/
theorem one_one_mem_bcfbCapacityRegion : ((1, 1) : ℝ × ℝ) ∈ bcfbCapacityRegion dueckW := by
  have ht : Tendsto (fun k : ℕ => (1 : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at ht
  refine mem_closure_of_tendsto (ht.prodMk_nhds ht) (Eventually.of_forall fun k => ?_)
  have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  exact isAchievableBCFB_dueck (by linarith) (by linarith)

end Feedback

/-! ### Without feedback -/

section NoFeedback

variable {M₁ M₂ n : ℕ}

/-- The marginal at receiver 1. -/
lemma bcMarg₁_dueckW (x : DueckX) (o : DueckY) :
    bcMarg₁ dueckW x o = 2⁻¹ * if o.1 = x.1 then 1 else 0 := by
  classical
  obtain ⟨a, c, d⟩ := x
  obtain ⟨o₀, u⟩ := o
  cases a <;> cases c <;> cases d <;> cases o₀ <;> cases u <;>
    simp [bcMarg₁, dueckW]

/-- The marginal at receiver 2. -/
lemma bcMarg₂_dueckW (x : DueckX) (o : DueckY) :
    bcMarg₂ dueckW x o = 2⁻¹ * if o.1 = x.1 then 1 else 0 := by
  classical
  obtain ⟨a, c, d⟩ := x
  obtain ⟨o₀, u⟩ := o
  cases a <;> cases c <;> cases d <;> cases o₀ <;> cases u <;>
    simp [bcMarg₂, dueckW]

open Classical in
/-- The error of a decoder, for a channel that shows `X₀` and adds uniform noise. -/
lemma dueck_row {T : DueckX → DueckY → ℝ} (hT : ∀ x o, T x o = 2⁻¹ * if o.1 = x.1 then 1 else 0)
    {ι : Type*} (g : (Fin n → DueckY) → ι) (m : ι) (x : Fin n → DueckX) :
    (∑ y, if g y ≠ m then channelExt T n x y else 0) =
      ∑ u : Fin n → Bool, (2⁻¹ : ℝ) ^ n *
        if g (fun i => ((x i).1, u i)) ≠ m then 1 else 0 := by
  have hval : ∀ (y₀ u : Fin n → Bool), channelExt T n x (zipSeq y₀ u) =
      if y₀ = fun i => (x i).1 then (2⁻¹ : ℝ) ^ n else 0 := by
    intro y₀ u
    simp only [channelExt, zipSeq, hT]
    by_cases h : y₀ = fun i => (x i).1
    · subst h
      simp
    · rw [ite_eq_right h]
      have : ∃ i, y₀ i ≠ (x i).1 := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      obtain ⟨i, hi⟩ := this
      exact prod_eq_zero (mem_univ i) (by simp [hi])
  rw [← sum_zipSeq, sum_eq_single (fun i => (x i).1)]
  · refine sum_congr rfl fun u _ => ?_
    have e : zipSeq (fun i => (x i).1) u = fun i => ((x i).1, u i) := rfl
    rw [hval, ite_eq_left rfl, e]
    by_cases h : g (fun i => ((x i).1, u i)) ≠ m
    · rw [ite_eq_left h, ite_eq_left h, mul_one]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  · intro y₀ _ hy
    refine sum_eq_zero fun u _ => ?_
    rw [hval, ite_eq_right hy]
    simp
  · simp

/-- **The counting bound of the example of page 18-40.** Without feedback,
`(1 - P₁ - P₂) M₁ M₂ ≤ 2ⁿ`. -/
theorem dueck_mul_le (c : BCCode M₁ M₂ n DueckX DueckY DueckY) :
    (1 - c.errProb₁ dueckW - c.errProb₂ dueckW) * ((M₁ : ℝ) * M₂) ≤ 2 ^ n := by
  classical
  rcases Nat.eq_zero_or_pos M₁ with rfl | hM₁
  · simp
  rcases Nat.eq_zero_or_pos M₂ with rfl | hM₂
  · simp
  have hM : (0 : ℝ) < (M₁ : ℝ) * M₂ := by positivity
  let x₀ : Fin M₁ × Fin M₂ → Fin n → Bool := fun w i => (c.enc w i).1
  -- the error with a fixed noise
  have hexists : ∀ {ι : Type} {T : DueckX → DueckY → ℝ}
      (_ : ∀ x o, T x o = 2⁻¹ * if o.1 = x.1 then 1 else 0)
      (g : (Fin n → DueckY) → ι) (pr : Fin M₁ × Fin M₂ → ι),
      ∃ u : Fin n → Bool, (∑ w, if g (fun i => (x₀ w i, u i)) ≠ pr w then (1 : ℝ) else 0) ≤
        (∑ w, ∑ y, if g y ≠ pr w then channelExt T n (c.enc w) y else 0) := by
    intro ι T hT g pr
    have h₀ : (∑ w, ∑ y, if g y ≠ pr w then channelExt T n (c.enc w) y else 0) =
        (2⁻¹ : ℝ) ^ n * ∑ u : Fin n → Bool,
          (∑ w, if g (fun i => (x₀ w i, u i)) ≠ pr w then (1 : ℝ) else 0) := by
      simp_rw [dueck_row hT g]
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun u _ => ?_
      rw [mul_sum]
    have hs : ∑ u : Fin n → Bool, (∑ w, if g (fun i => (x₀ w i, u i)) ≠ pr w then (1 : ℝ) else 0) =
        ∑ _u : Fin n → Bool, (∑ w, ∑ y, if g y ≠ pr w then channelExt T n (c.enc w) y else 0) := by
      rw [h₀]
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      rw [← mul_assoc, ← mul_pow]
      norm_num
    obtain ⟨u, -, hu⟩ := exists_le_of_sum_le (s := univ) ⟨fun _ => false, mem_univ _⟩ hs.le
    exact ⟨u, hu⟩
  obtain ⟨u₁, hu₁⟩ := hexists bcMarg₁_dueckW c.dec₁ Prod.fst
  obtain ⟨u₂, hu₂⟩ := hexists bcMarg₂_dueckW c.dec₂ Prod.snd
  have hu₁' : (∑ w, if c.dec₁ (fun i => (x₀ w i, u₁ i)) ≠ w.1 then (1 : ℝ) else 0) ≤
      ∑ w, ∑ y, if c.dec₁ y ≠ w.1 then channelExt (bcMarg₁ dueckW) n (c.enc w) y else 0 := by
    convert hu₁
  have hu₂' : (∑ w, if c.dec₂ (fun i => (x₀ w i, u₂ i)) ≠ w.2 then (1 : ℝ) else 0) ≤
      ∑ w, ∑ y, if c.dec₂ y ≠ w.2 then channelExt (bcMarg₂ dueckW) n (c.enc w) y else 0 := by
    convert hu₂
  have he₁ : c.errProb₁ dueckW * ((M₁ : ℝ) * M₂) =
      ∑ w, ∑ y, if c.dec₁ y ≠ w.1 then channelExt (bcMarg₁ dueckW) n (c.enc w) y else 0 := by
    rw [BCCode.errProb₁, div_mul_cancel₀ _ hM.ne']
  have he₂ : c.errProb₂ dueckW * ((M₁ : ℝ) * M₂) =
      ∑ w, ∑ y, if c.dec₂ y ≠ w.2 then channelExt (bcMarg₂ dueckW) n (c.enc w) y else 0 := by
    rw [BCCode.errProb₂, div_mul_cancel₀ _ hM.ne']
  -- the messages that are decoded correctly
  let G : Finset (Fin M₁ × Fin M₂) := univ.filter fun w =>
    c.dec₁ (fun i => (x₀ w i, u₁ i)) = w.1 ∧ c.dec₂ (fun i => (x₀ w i, u₂ i)) = w.2
  have hcard : (G.card : ℝ) ≤ 2 ^ n := by
    have h : G.card ≤ (univ : Finset (Fin n → Bool)).card := by
      refine card_le_card_of_injOn x₀ (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
      intro a ha b hb hab
      have ha' := (mem_filter.mp (mem_coe.mp ha)).2
      have hb' := (mem_filter.mp (mem_coe.mp hb)).2
      refine Prod.ext ?_ ?_
      · rw [← ha'.1, ← hb'.1, hab]
      · rw [← ha'.2, ← hb'.2, hab]
    have h' : (G.card : ℝ) ≤ ((univ : Finset (Fin n → Bool)).card : ℝ) := by exact_mod_cast h
    simpa [Fintype.card_fun] using h'
  have hcount : (M₁ : ℝ) * M₂ ≤ G.card +
      (∑ w, if c.dec₁ (fun i => (x₀ w i, u₁ i)) ≠ w.1 then (1 : ℝ) else 0) +
      (∑ w, if c.dec₂ (fun i => (x₀ w i, u₂ i)) ≠ w.2 then (1 : ℝ) else 0) := by
    have hG : (G.card : ℝ) = ∑ w, if w ∈ G then (1 : ℝ) else 0 := by
      rw [sum_ite_mem, univ_inter]
      simp
    have hone : (M₁ : ℝ) * M₂ = ∑ _w : Fin M₁ × Fin M₂, (1 : ℝ) := by
      simp
    rw [hG, hone, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_le_sum fun w _ => ?_
    by_cases h₁ : c.dec₁ (fun i => (x₀ w i, u₁ i)) = w.1
    · by_cases h₂ : c.dec₂ (fun i => (x₀ w i, u₂ i)) = w.2
      · have hw : w ∈ G := mem_filter.mpr ⟨mem_univ _, h₁, h₂⟩
        rw [ite_eq_left hw]
        split_ifs <;> norm_num
      · rw [ite_eq_left h₂]
        split_ifs <;> norm_num
    · rw [ite_eq_left h₁]
      split_ifs <;> norm_num
  have hmul : (1 - c.errProb₁ dueckW - c.errProb₂ dueckW) * ((M₁ : ℝ) * M₂) =
      (M₁ : ℝ) * M₂ - c.errProb₁ dueckW * ((M₁ : ℝ) * M₂) -
        c.errProb₂ dueckW * ((M₁ : ℝ) * M₂) := by ring
  rw [hmul, he₁, he₂]
  linarith

/-- **The capacity region without feedback, the outer bound.** -/
theorem bcCapacityRegionBits_dueck_subset :
    bcCapacityRegionBits dueckW ⊆ {R : ℝ × ℝ | R.1 + R.2 ≤ 1} := by
  have hcl : IsClosed {R : ℝ × ℝ | R.1 + R.2 ≤ 1} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  refine closure_minimal ?_ hcl
  rintro ⟨R₁, R₂⟩ ⟨c, hc⟩
  change R₁ + R₂ ≤ 1
  by_contra hgt
  push Not at hgt
  have hδ : 0 < R₁ + R₂ - 1 := by linarith
  have hsmall : ∀ᶠ n : ℕ in atTop, (c n).errProb dueckW < 1 / 4 :=
    (tendsto_order.mp hc).2 _ (by norm_num)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) * (R₁ + R₂ - 1) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hδ).eventually_ge_atTop 2
  obtain ⟨n, hn₁, hn₂⟩ := (hsmall.and hlarge).exists
  have hb := dueck_mul_le (c n)
  have hm := (c n).max_errProb_le dueckW_isChannel
  have hP₁ : (c n).errProb₁ dueckW ≤ (c n).errProb dueckW := (le_max_left _ _).trans hm
  have hP₂ : (c n).errProb₂ dueckW ≤ (c n).errProb dueckW := (le_max_right _ _).trans hm
  set a := ⌈(n : ℝ) * R₁⌉₊ with ha
  set b := ⌈(n : ℝ) * R₂⌉₊ with hb'
  have hMM : (0 : ℝ) < ((2 ^ a : ℕ) : ℝ) * ((2 ^ b : ℕ) : ℝ) := by positivity
  have h₃ : (1 / 2 : ℝ) * (((2 ^ a : ℕ) : ℝ) * ((2 ^ b : ℕ) : ℝ)) ≤ 2 ^ n := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hMM.le) hb
    linarith
  have h₄ : ((2 : ℝ) ^ (a + b)) ≤ 2 ^ (n + 1) := by
    rw [pow_add, pow_succ]
    push_cast at h₃
    linarith
  have h₅ : a + b ≤ n + 1 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h₄
  have h₆ : (n : ℝ) * R₁ ≤ a := Nat.le_ceil _
  have h₇ : (n : ℝ) * R₂ ≤ b := Nat.le_ceil _
  have h₈ : (a : ℝ) + b ≤ n + 1 := by exact_mod_cast h₅
  nlinarith

/-- The code without feedback: the bits of the two messages are sent on `X₀`. -/
def dueckNF (a₁ a₂ n : ℕ) : BCCode (2 ^ a₁) (2 ^ a₂) n DueckX DueckY DueckY where
  enc w i := (if (i : ℕ) < a₁ then dueckBit (dueckEq a₁ w.1) i
    else dueckBit (dueckEq a₂ w.2) (i - a₁), false, false)
  dec₁ y := (dueckEq a₁).symm fun i => if h : (i : ℕ) < n then (y ⟨i, h⟩).1 else false
  dec₂ y := (dueckEq a₂).symm fun i =>
    if h : a₁ + (i : ℕ) < n then (y ⟨a₁ + i, h⟩).1 else false

lemma dueckNF_errProb {a₁ a₂ : ℕ} (h : a₁ + a₂ ≤ n) :
    (dueckNF a₁ a₂ n).errProb dueckW = 0 := by
  classical
  simp only [BCCode.errProb]
  rw [div_eq_zero_iff]
  left
  refine sum_eq_zero fun w _ => sum_eq_zero fun y _ => ?_
  by_cases hy : channelExt dueckW n ((dueckNF a₁ a₂ n).enc w) y = 0
  · rw [hy]
    simp
  have hi : ∀ i : Fin n, (y i).1.1 = ((dueckNF a₁ a₂ n).enc w i).1 ∧
      (y i).2.1 = ((dueckNF a₁ a₂ n).enc w i).1 := by
    intro i
    have hne : dueckW ((dueckNF a₁ a₂ n).enc w i) (y i) ≠ 0 := by
      intro h0
      exact hy (prod_eq_zero (mem_univ i) h0)
    obtain ⟨b, hb⟩ := dueckW_ne_zero hne
    rw [hb]
    exact ⟨rfl, rfl⟩
  have hbit : ∀ {a : ℕ} (t : Fin a → Bool) (i : Fin a), dueckBit t i = t i := by
    intro a t i
    simp [dueckBit]
  have h₁ : (dueckNF a₁ a₂ n).dec₁ (fun i => (y i).1) = w.1 := by
    simp only [dueckNF]
    rw [Equiv.symm_apply_eq]
    funext i
    have hin : (i : ℕ) < n := by have := i.2; omega
    rw [dite_eq_left hin, (hi ⟨i, hin⟩).1]
    change (if (i : ℕ) < a₁ then _ else _) = _
    rw [ite_eq_left i.2, hbit]
  have h₂ : (dueckNF a₁ a₂ n).dec₂ (fun i => (y i).2) = w.2 := by
    simp only [dueckNF]
    rw [Equiv.symm_apply_eq]
    funext i
    have hin : a₁ + (i : ℕ) < n := by have := i.2; omega
    rw [dite_eq_left hin, (hi ⟨a₁ + i, hin⟩).2]
    change (if a₁ + (i : ℕ) < a₁ then _ else _) = _
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, hbit]
  rw [ite_eq_right]
  rintro (h | h)
  · exact h h₁
  · exact h h₂

/-- **The capacity region without feedback, the inner bound.** -/
theorem subset_bcCapacityRegionBits_dueck :
    {R : ℝ × ℝ | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ R.1 + R.2 ≤ 1} ⊆ bcCapacityRegionBits dueckW := by
  rintro ⟨R₁, R₂⟩ ⟨h₁, h₂, h₃⟩
  simp only at h₁ h₂ h₃
  -- rates with a strictly smaller sum
  have hach : ∀ S₁ S₂ : ℝ, 0 ≤ S₁ → 0 ≤ S₂ → S₁ + S₂ < 1 → IsAchievableBCBits dueckW S₁ S₂ := by
    intro S₁ S₂ hS₁ hS₂ hS
    refine ⟨fun n => dueckNF ⌈(n : ℝ) * S₁⌉₊ ⌈(n : ℝ) * S₂⌉₊ n, tendsto_const_nhds.congr' ?_⟩
    have hg : 0 < 1 - (S₁ + S₂) := by linarith
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) * (1 - (S₁ + S₂))) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hg
    filter_upwards [hlim.eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h₄ := Nat.ceil_lt_add_one (mul_nonneg hn0 hS₁)
    have h₅ := Nat.ceil_lt_add_one (mul_nonneg hn0 hS₂)
    have h₆ : ((⌈(n : ℝ) * S₁⌉₊ : ℝ)) + ⌈(n : ℝ) * S₂⌉₊ ≤ n := by nlinarith
    exact (dueckNF_errProb (by exact_mod_cast h₆)).symm
  have ht : Tendsto (fun k : ℕ => (1 : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at ht
  have hlim : Tendsto (fun k : ℕ => (((1 : ℝ) - 1 / ((k : ℝ) + 1)) * R₁,
      ((1 : ℝ) - 1 / ((k : ℝ) + 1)) * R₂)) atTop (𝓝 (R₁, R₂)) := by
    have e₁ := ht.mul_const R₁
    have e₂ := ht.mul_const R₂
    rw [one_mul] at e₁ e₂
    exact e₁.prodMk_nhds e₂
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hp₁ : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  refine hach _ _ (mul_nonneg (by linarith) h₁) (mul_nonneg (by linarith) h₂) ?_
  have : (1 - 1 / ((k : ℝ) + 1)) * R₁ + (1 - 1 / ((k : ℝ) + 1)) * R₂ =
      (1 - 1 / ((k : ℝ) + 1)) * (R₁ + R₂) := by ring
  rw [this]
  nlinarith

end NoFeedback

end InfoTheory
