/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACBounds
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# The random access channel

The random access channel of Lecture 24 of El Gamal and Kim: `Y = S₁ X₁ ⊕ S₂ X₂`, where sender `j`
is active when `S_j = 1`, and the states are i.i.d. `Bern(p)`. The receiver knows both states and
each sender at most its own.

The notes state the adaptive and broadcast regions without proof, so this file studies them as
formulas in the mutual informations of the channel, except for the compound region, which is proved
as a coding theorem from the outer bound for the DM-MAC.

## Main definitions

* `racW s₁ s₂`: the channel in the states `s₁, s₂`.
* `IsAchievableRACCompound R₁ R₂`: a single pair of encoders is reliable for all states.
* `racAdaptiveRegion`, `racAvgSum`: the adaptive region and its average sum rate.
* `racBCRegion`, `racBCSum`: the region of the broadcast approach and its average sum rate.

## Main statements

* `isAchievableRACCompound_iff`: the compound capacity region is `R₁ = R₂ = 0`.
* `mem_racAdaptiveRegion_iff`: the reduction of the adaptive region.
* `isGreatest_racAvgSum`: the average adaptive sum capacity is `p`.
* `isGreatest_racBCSum`: `C_sp = max {2 p (1 - p), p}`.
* `isGreatest_racErgodic`: the ergodic sum capacity is `1 - (1 - p)²`.
* `racSum_comparison`: `0 ≤ p ≤ C_sp ≤ 1 - (1 - p)²`, and `racBC_gt_iff`: the broadcast approach
  beats adaptive coding exactly if `p < 1/2`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset Filter Topology Real

namespace InfoTheory

/-- **The random access channel.** The output `Y = s₁ X₁ ⊕ s₂ X₂` in the states `s₁, s₂`. -/
def racOutput (s₁ s₂ : Bool) (x : Bool × Bool) : Bool := xor (s₁ && x.1) (s₂ && x.2)

/-- The random access channel in the states `s₁, s₂`, as a channel. -/
def racW (s₁ s₂ : Bool) : Bool × Bool → Bool → ℝ :=
  fun x y => if y = racOutput s₁ s₂ x then 1 else 0

lemma racW_isChannel (s₁ s₂ : Bool) : IsChannel (racW s₁ s₂) := fun x =>
  ⟨fun y => by unfold racW; split_ifs <;> norm_num, by simp [racW]⟩

/-! ### Channels with constant or noiseless rows -/

section Rows

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A channel whose rows are all equal carries no information. -/
lemma mutualInfoOf_of_const_rows {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W)
    {r : β → ℝ} (hr : ∀ x, W x = r) : mutualInfoOf p W = 0 := by
  rw [mutualInfoOf_eq_sum hp hW]
  simp only [hr, ← sum_mul, hp.sum_eq_one, one_mul, entropy_eq_sum_negMulLog, sub_self]

lemma capacity_of_const_rows [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) {r : β → ℝ}
    (hr : ∀ x, W x = r) : capacity W = 0 := by
  refine le_antisymm (csSup_le ?_ ?_) (capacity_nonneg hW)
  · obtain ⟨c, hc⟩ := exists_capacity_eq hW
    exact ⟨_, c, hc.1, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (mutualInfoOf_of_const_rows hp hW hr).le

end Rows

/-- The noiseless binary channel, up to a flip of the output, gives `1` bit for a uniform input. -/
lemma mutualInfoOf_xor (c : Bool) :
    mutualInfoOf (uniformPMF Bool) (fun a y => if y = xor a c then (1 : ℝ) else 0) = log 2 := by
  have hW : IsChannel (fun (a y : Bool) => if y = xor a c then (1 : ℝ) else 0) := fun a =>
    ⟨fun y => by dsimp only; split_ifs <;> norm_num, by simp⟩
  rw [mutualInfoOf_eq_sum (uniformPMF_isPMF) hW]
  have h0 : ∀ a : Bool, entropy (fun y => if y = xor a c then (1 : ℝ) else 0) = 0 := by
    intro a
    rw [entropy_eq_sum_negMulLog]
    refine sum_eq_zero fun y _ => ?_
    split_ifs <;> simp
  simp only [h0, mul_zero, sum_const_zero, sub_zero]
  cases c
  · simp [uniformPMF, negMulLog]
  · simp [uniformPMF, negMulLog]
    ring

variable {p₁ p₂ : Bool → ℝ}

lemma macInfo₁_rac_false (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (s₂ : Bool) :
    macInfo₁ p₁ p₂ (racW false s₂) = 0 := by
  have hW := racW_isChannel false s₂
  rw [macInfo₁_eq_sum hp₁ hp₂ hW]
  refine sum_eq_zero fun b _ => ?_
  rw [mutualInfoOf_of_const_rows (r := racW false s₂ (true, b)) hp₁ (fun a => hW (a, b))
    fun a => by funext y; simp [racW, racOutput], mul_zero]

lemma macInfo₂_rac_false (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (s₁ : Bool) :
    macInfo₂ p₁ p₂ (racW s₁ false) = 0 := by
  have hW := racW_isChannel s₁ false
  rw [macInfo₂_eq_sum hp₁ hp₂ hW]
  refine sum_eq_zero fun a _ => ?_
  rw [mutualInfoOf_of_const_rows (r := racW s₁ false (a, true)) hp₂ (fun b => hW (a, b))
    fun b => by funext y; simp [racW, racOutput], mul_zero]

lemma macInfo₁₂_rac_false (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) :
    macInfo₁₂ p₁ p₂ (racW false false) = 0 := by
  have hW := racW_isChannel false false
  have h := mutualInfoOf_of_const_rows (r := racW false false (true, true)) (hp₁.prodDist hp₂) hW
    fun a => by funext y; simp [racW, racOutput]
  exact h

lemma macInfo₁_rac_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (s₁ s₂ : Bool) :
    macInfo₁ p₁ p₂ (racW s₁ s₂) ≤ log 2 := by
  have hW := racW_isChannel s₁ s₂
  rw [macInfo₁_eq_sum hp₁ hp₂ hW]
  calc ∑ b, p₂ b * mutualInfoOf p₁ (fun a => racW s₁ s₂ (a, b)) ≤ ∑ b, p₂ b * log 2 := by
        refine sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hp₂.nonneg b)
        simpa using mutualInfoOf_le_log_card_output hp₁ fun a => hW (a, b)
    _ = log 2 := by rw [← sum_mul, hp₂.sum_eq_one, one_mul]

lemma macInfo₂_rac_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (s₁ s₂ : Bool) :
    macInfo₂ p₁ p₂ (racW s₁ s₂) ≤ log 2 := by
  have hW := racW_isChannel s₁ s₂
  rw [macInfo₂_eq_sum hp₁ hp₂ hW]
  calc ∑ a, p₁ a * mutualInfoOf p₂ (fun b => racW s₁ s₂ (a, b)) ≤ ∑ a, p₁ a * log 2 := by
        refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hp₁.nonneg a)
        simpa using mutualInfoOf_le_log_card_output hp₂ fun b => hW (a, b)
    _ = log 2 := by rw [← sum_mul, hp₁.sum_eq_one, one_mul]

lemma macInfo₁₂_rac_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (s₁ s₂ : Bool) :
    macInfo₁₂ p₁ p₂ (racW s₁ s₂) ≤ log 2 := by
  simpa using macInfo₁₂_le_log_card hp₁ hp₂ (racW_isChannel s₁ s₂)

lemma macInfo₁_rac_uniform (s₂ : Bool) :
    macInfo₁ (uniformPMF Bool) (uniformPMF Bool) (racW true s₂) = log 2 := by
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  rw [macInfo₁_eq_sum hu hu (racW_isChannel _ _)]
  have : ∀ b : Bool, mutualInfoOf (uniformPMF Bool) (fun a => racW true s₂ (a, b)) = log 2 := by
    intro b
    rw [← mutualInfoOf_xor (s₂ && b)]
    congr 1
  simp only [this]
  rw [← sum_mul, hu.sum_eq_one, one_mul]

lemma macInfo₂_rac_uniform (s₁ : Bool) :
    macInfo₂ (uniformPMF Bool) (uniformPMF Bool) (racW s₁ true) = log 2 := by
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  rw [macInfo₂_eq_sum hu hu (racW_isChannel _ _)]
  have : ∀ a : Bool, mutualInfoOf (uniformPMF Bool) (fun b => racW s₁ true (a, b)) = log 2 := by
    intro a
    rw [← mutualInfoOf_xor (s₁ && a)]
    congr 1
    funext b y
    simp [racW, racOutput, Bool.xor_comm]
  simp only [this]
  rw [← sum_mul, hu.sum_eq_one, one_mul]

lemma macInfo₁₂_rac_uniform {s₁ s₂ : Bool} (h : s₁ = true ∨ s₂ = true) :
    macInfo₁₂ (uniformPMF Bool) (uniformPMF Bool) (racW s₁ s₂) = log 2 := by
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  refine le_antisymm (macInfo₁₂_rac_le hu hu _ _) ?_
  rcases h with h | h
  · subst h
    rw [← macInfo₁_rac_uniform s₂]
    exact macInfo₁_le_macInfo₁₂ hu hu (racW_isChannel _ _)
  · subst h
    rw [← macInfo₂_rac_uniform s₁]
    exact macInfo₂_le_macInfo₁₂ hu hu (racW_isChannel _ _)

/-! ### The compound channel -/

/-- **The compound channel of Lecture 24.** A rate pair (in bits) is achievable for the compound
channel if one pair of encoders, with decoders knowing the states, is reliable in all states. -/
def IsAchievableRACCompound (R₁ R₂ : ℝ) : Prop :=
  ∃ (enc₁ : ∀ n : ℕ, Fin (2 ^ ⌈n * R₁⌉₊) → Fin n → Bool)
    (enc₂ : ∀ n : ℕ, Fin (2 ^ ⌈n * R₂⌉₊) → Fin n → Bool)
    (dec : ∀ (_ _ : Bool) (n : ℕ),
      (Fin n → Bool) → Fin (2 ^ ⌈n * R₁⌉₊) × Fin (2 ^ ⌈n * R₂⌉₊)),
    ∀ s₁ s₂, Tendsto (fun n => (MACCode.mk (enc₁ n) (enc₂ n) (dec s₁ s₂ n)).avgErrProb (racW s₁ s₂))
      atTop (𝓝 0)

/-- **Lecture 24.** The compound channel capacity region is `R₁ = R₂ = 0`: for nonpositive rates
there is a single message, and otherwise the channel in the states `s₁ = s₂ = 0` carries nothing. -/
theorem isAchievableRACCompound_iff {R₁ R₂ : ℝ} :
    IsAchievableRACCompound R₁ R₂ ↔ R₁ ≤ 0 ∧ R₂ ≤ 0 := by
  have hl := log_pos one_lt_two
  constructor
  · rintro ⟨enc₁, enc₂, dec, h⟩
    have hW := racW_isChannel false false
    have hach : IsAchievableMACBits (racW false false) R₁ R₂ :=
      ⟨fun n => MACCode.mk (enc₁ n) (enc₂ n) (dec false false n), h false false⟩
    have hmem : (R₁, R₂) ∈ macCapacityRegionBits (racW false false) := subset_closure hach
    obtain ⟨h1, h2, -⟩ := macCapacityRegionBits_subset_macOuterBoundBits hW hmem
    have hC₁ : macC₁ (racW false false) = 0 := by
      unfold macC₁
      have : ∀ b : Bool, capacity (fun a => racW false false (a, b)) = 0 := fun b =>
        capacity_of_const_rows (r := racW false false (true, b)) (fun a => hW (a, b))
          fun a => by funext y; simp [racW, racOutput]
      simp [this]
    have hC₂ : macC₂ (racW false false) = 0 := by
      unfold macC₂
      have : ∀ a : Bool, capacity (fun b => racW false false (a, b)) = 0 := fun a =>
        capacity_of_const_rows (r := racW false false (a, true)) (fun b => hW (a, b))
          fun b => by funext y; simp [racW, racOutput]
      simp [this]
    rw [hC₁] at h1
    rw [hC₂] at h2
    simpa using And.intro h1 h2
  · rintro ⟨h1, h2⟩
    have hc₁ : ∀ n : ℕ, ⌈(n : ℝ) * R₁⌉₊ = 0 := fun n =>
      Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) h1)
    have hc₂ : ∀ n : ℕ, ⌈(n : ℝ) * R₂⌉₊ = 0 := fun n =>
      Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) h2)
    have hne₁ : ∀ n : ℕ, Unique (Fin (2 ^ ⌈(n : ℝ) * R₁⌉₊)) := fun n => by
      rw [hc₁ n]
      exact inferInstanceAs (Unique (Fin 1))
    have hne₂ : ∀ n : ℕ, Unique (Fin (2 ^ ⌈(n : ℝ) * R₂⌉₊)) := fun n => by
      rw [hc₂ n]
      exact inferInstanceAs (Unique (Fin 1))
    refine ⟨fun _ _ _ => true, fun _ _ _ => true,
      fun _ _ n _ => ((hne₁ n).default, (hne₂ n).default), fun s₁ s₂ => ?_⟩
    have hz : ∀ n : ℕ, (MACCode.mk (fun _ _ => true) (fun _ _ => true)
        (fun _ => ((hne₁ n).default, (hne₂ n).default)) :
        MACCode _ _ n Bool Bool Bool).avgErrProb (racW s₁ s₂) = 0 := by
      intro n
      unfold MACCode.avgErrProb MACCode.condErrProb
      simp
    simp only [hz]
    exact tendsto_const_nhds

/-! ### The adaptive capacity region -/

/-- **The adaptive region of Lecture 24.** The rates `R₁ s₁` and `R₂ s₂` of the two senders depend
on their own states, and every pair of states must allow decoding. Rates are in bits. -/
def racAdaptiveRegion : Set ((Bool → ℝ) × (Bool → ℝ)) :=
  {R | (∀ s, 0 ≤ R.1 s) ∧ (∀ s, 0 ≤ R.2 s) ∧ ∃ p₁ p₂ : Bool → ℝ, IsPMF p₁ ∧ IsPMF p₂ ∧
    ∀ s₁ s₂, R.1 s₁ * log 2 ≤ macInfo₁ p₁ p₂ (racW s₁ s₂) ∧
      R.2 s₂ * log 2 ≤ macInfo₂ p₁ p₂ (racW s₁ s₂) ∧
      (R.1 s₁ + R.2 s₂) * log 2 ≤ macInfo₁₂ p₁ p₂ (racW s₁ s₂)}

/-- **Lecture 24.** The adaptive region reduces to `R₁₀ = R₂₀ = 0`, `R₁₁, R₂₁ ≤ 1` and
`R₁₁ + R₂₁ ≤ 1`, and uniform inputs attain all of it. -/
theorem mem_racAdaptiveRegion_iff {R : (Bool → ℝ) × (Bool → ℝ)} :
    R ∈ racAdaptiveRegion ↔ R.1 false = 0 ∧ R.2 false = 0 ∧ 0 ≤ R.1 true ∧ 0 ≤ R.2 true ∧
      R.1 true + R.2 true ≤ 1 := by
  have hl := log_pos one_lt_two
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  constructor
  · rintro ⟨h1, h2, p₁, p₂, hp₁, hp₂, h⟩
    refine ⟨?_, ?_, h1 _, h2 _, ?_⟩
    · have := (h false false).1
      rw [macInfo₁_rac_false hp₁ hp₂] at this
      exact le_antisymm (by nlinarith) (h1 _)
    · have := (h false false).2.1
      rw [macInfo₂_rac_false hp₁ hp₂] at this
      exact le_antisymm (by nlinarith) (h2 _)
    · have h3 := (h true true).2.2.trans (macInfo₁₂_rac_le hp₁ hp₂ _ _)
      nlinarith
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun s => by cases s <;> simp [*], fun s => by cases s <;> simp [*],
      uniformPMF Bool, uniformPMF Bool, hu, hu, fun s₁ s₂ => ?_⟩
    have hR1 : R.1 true ≤ 1 := by linarith
    have hR2 : R.2 true ≤ 1 := by linarith
    cases s₁ <;> cases s₂
    · exact ⟨by rw [h1, macInfo₁_rac_false hu hu]; simp, by rw [h2, macInfo₂_rac_false hu hu]; simp,
        by rw [h1, h2, macInfo₁₂_rac_false hu hu]; simp⟩
    · exact ⟨by rw [h1, macInfo₁_rac_false hu hu]; simp, by rw [macInfo₂_rac_uniform]; nlinarith,
        by rw [h1, macInfo₁₂_rac_uniform (Or.inr rfl)]; nlinarith⟩
    · exact ⟨by rw [macInfo₁_rac_uniform]; nlinarith, by rw [h2, macInfo₂_rac_false hu hu]; simp,
        by rw [h2, macInfo₁₂_rac_uniform (Or.inl rfl)]; nlinarith⟩
    · rw [macInfo₁_rac_uniform, macInfo₂_rac_uniform, macInfo₁₂_rac_uniform (Or.inl rfl)]
      exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The average sum rate of a pair of adaptive rates, over the i.i.d. states. -/
def racAvgSum (p : ℝ) (R : (Bool → ℝ) × (Bool → ℝ)) : ℝ :=
  ∑ s₁, ∑ s₂, bernoulliPMF p s₁ * bernoulliPMF p s₂ * (R.1 s₁ + R.2 s₂)

/-- **Lecture 24.** The average adaptive sum capacity is `p`. -/
theorem isGreatest_racAvgSum {p : ℝ} (h0 : 0 ≤ p) :
    IsGreatest (racAvgSum p '' racAdaptiveRegion) p := by
  have hval : ∀ R : (Bool → ℝ) × (Bool → ℝ), R.1 false = 0 → R.2 false = 0 →
      racAvgSum p R = p * (R.1 true + R.2 true) := by
    intro R h1 h2
    simp [racAvgSum, bernoulliPMF, h1, h2]
    ring
  constructor
  · refine ⟨(fun s => if s then 1 else 0, fun _ => 0), ?_, ?_⟩
    · rw [mem_racAdaptiveRegion_iff]
      simp
    · rw [hval _ (by simp) (by simp)]
      simp
  · rintro _ ⟨R, hR, rfl⟩
    obtain ⟨h1, h2, -, -, h5⟩ := mem_racAdaptiveRegion_iff.1 hR
    rw [hval R h1 h2]
    nlinarith

/-! ### The broadcast approach -/

/-- **The broadcast approach of Lecture 24.** The rate quadruples `(R̃₁₀, R̃₁₁, R̃₂₀, R̃₂₁)` of the
2-sender 3-receiver channel. The notes state this region without proof. -/
def racBCRegion : Set (ℝ × ℝ × ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2.1 ∧ 0 ≤ R.2.2.2 ∧ R.1 + R.2.1 ≤ 1 ∧ R.2.2.1 + R.2.2.2 ≤ 1 ∧
    R.1 + R.2.1 + R.2.2.2 ≤ 1 ∧ R.2.2.1 + R.2.1 + R.2.2.2 ≤ 1}

/-- The average sum rate of the broadcast approach. -/
def racBCSum (p : ℝ) (R : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  p * (1 - p) * (R.1 + R.2.1) + p * (1 - p) * (R.2.2.1 + R.2.2.2) + p ^ 2 * (R.2.1 + R.2.2.2)

/-- **Lecture 24.** The average sum capacity of the broadcast approach is
`C_sp = max {2 p (1 - p), p}`. -/
theorem isGreatest_racBCSum {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsGreatest (racBCSum p '' racBCRegion) (max (2 * p * (1 - p)) p) := by
  have h1p : 0 ≤ 1 - p := by linarith
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg h0 h1p
  constructor
  · rcases le_total (2 * p * (1 - p)) p with h | h
    · rw [max_eq_right h]
      refine ⟨(0, 1, 0, 0), ?_, ?_⟩
      · simp [racBCRegion]
      · simp [racBCSum]
        ring
    · rw [max_eq_left h]
      refine ⟨(1, 0, 1, 0), ?_, ?_⟩
      · simp [racBCRegion]
      · simp [racBCSum]
        ring
  · rintro _ ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd, -, -, h3, h4⟩, rfl⟩
    simp only at ha hb hc hd h3 h4
    simp only [racBCSum]
    -- The objective is linear in `b + d`, so one of the two ends is the maximum.
    set t := b + d with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by linarith
    have hobj : p * (1 - p) * (a + b) + p * (1 - p) * (c + d) + p ^ 2 * t =
        p * (1 - p) * (a + c) + p * t := by
      rw [ht]
      ring
    rw [hobj]
    have hac : a + c ≤ 2 * (1 - t) := by linarith
    have h5 : p * (1 - p) * (a + c) ≤ p * (1 - p) * (2 * (1 - t)) :=
      mul_le_mul_of_nonneg_left hac hpp
    have h6 : p * (1 - p) * (2 * (1 - t)) + p * t =
        (1 - t) * (2 * p * (1 - p)) + t * p := by
      ring
    have h7 : (1 - t) * (2 * p * (1 - p)) ≤ (1 - t) * max (2 * p * (1 - p)) p :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    have h8 : t * p ≤ t * max (2 * p * (1 - p)) p :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
    nlinarith

/-! ### The ergodic sum capacity and the comparison -/

/-- **Lecture 24.** The ergodic sum capacity, in bits, is `1 - (1 - p)²`: this is the maximum of the
average of `I(X₁, X₂; Y | s₁, s₂)` over inputs depending on both states, and uniform inputs, which
do not depend on the states, attain it. So it does not matter what the encoders know of the
states. -/
theorem isGreatest_racErgodic {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsGreatest {c | ∃ q₁ q₂ : Bool → Bool → Bool → ℝ, (∀ s₁ s₂, IsPMF (q₁ s₁ s₂)) ∧
      (∀ s₁ s₂, IsPMF (q₂ s₁ s₂)) ∧
      c = ∑ s₁, ∑ s₂, bernoulliPMF p s₁ * bernoulliPMF p s₂ *
        (macInfo₁₂ (q₁ s₁ s₂) (q₂ s₁ s₂) (racW s₁ s₂) / log 2)} (1 - (1 - p) ^ 2) := by
  have hl := log_pos one_lt_two
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  have h1p : 0 ≤ 1 - p := by linarith
  constructor
  · refine ⟨fun _ _ => uniformPMF Bool, fun _ _ => uniformPMF Bool, fun _ _ => hu, fun _ _ =>
    hu, ?_⟩
    simp only [Fintype.sum_bool, bernoulliPMF]
    rw [macInfo₁₂_rac_false hu hu, macInfo₁₂_rac_uniform (Or.inl rfl),
      macInfo₁₂_rac_uniform (Or.inl rfl), macInfo₁₂_rac_uniform (Or.inr rfl), div_self hl.ne']
    simp
    ring
  · rintro _ ⟨q₁, q₂, h₁, h₂, rfl⟩
    simp only [Fintype.sum_bool, bernoulliPMF]
    rw [macInfo₁₂_rac_false (h₁ false false) (h₂ false false)]
    have hb : ∀ s₁ s₂, macInfo₁₂ (q₁ s₁ s₂) (q₂ s₁ s₂) (racW s₁ s₂) / log 2 ≤ 1 := fun s₁ s₂ =>
      (div_le_one hl).2 (macInfo₁₂_rac_le (h₁ _ _) (h₂ _ _) _ _)
    have e1 := mul_le_mul_of_nonneg_left (hb true true) (mul_nonneg h0 h0)
    have e2 := mul_le_mul_of_nonneg_left (hb true false) (mul_nonneg h0 h1p)
    have e3 := mul_le_mul_of_nonneg_left (hb false true) (mul_nonneg h1p h0)
    simp only [ite_true, Bool.false_eq_true, ite_false, zero_div, mul_zero] at e1 e2 e3 ⊢
    nlinarith

/-- **The figure on p. 24-28.** The sum capacities are ordered as
`C_C = 0 ≤ C_A = p ≤ C_BC = max {2 p (1 - p), p} ≤ C = 1 - (1 - p)²`. -/
theorem racSum_comparison {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ p ∧ p ≤ max (2 * p * (1 - p)) p ∧ max (2 * p * (1 - p)) p ≤ 1 - (1 - p) ^ 2 := by
  refine ⟨h0, le_max_right _ _, max_le ?_ ?_⟩
  · nlinarith
  · nlinarith

/-- **Lecture 24.** The broadcast approach is better than adaptive coding exactly when the senders
are active less often than half of the time. -/
theorem racBC_gt_iff {p : ℝ} (h0 : 0 < p) : p < max (2 * p * (1 - p)) p ↔ p < 1 / 2 := by
  rw [lt_max_iff]
  constructor
  · rintro (h | h)
    · nlinarith
    · exact absurd h (lt_irrefl _)
  · intro h
    left
    nlinarith

end InfoTheory
