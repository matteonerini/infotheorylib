/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCTimeSharing

/-!
# Simple inner and outer bounds on the capacity region of the broadcast channel

The first part of Lecture 5 of El Gamal and Kim: the capacity region of the DM-BC lies between the
time-division inner bound and the outer bound `R₁ ≤ C₁`, `R₂ ≤ C₂` given by the capacities
`Cⱼ = max_{p(x)} I(X; Yⱼ)` of the channels `p(yⱼ | x)`. The time-division inner bound is tight for
the symmetric DM-BC, and the outer bound for the DM-BC with separate channels.

## Main definitions

* `bcOuterBoundBits W`: the outer bound `R₁ ≤ C₁`, `R₂ ≤ C₂`, in bits.
* `bcTimeDivisionBits W`: the time-division inner bound, in bits.

## Main statements

* `bcCapacityRegionBits_subset_bcOuterBoundBits`: the outer bound.
* `bcTimeDivisionBits_subset`: the time-division inner bound.
* `bcCapacityRegionBits_eq_bcTimeDivisionBits_of_marg_eq`: for the symmetric DM-BC,
  `p(y₁ | x) = p(y₂ | x)`, the capacity region is the time-division region.
* `bcCapacityRegionBits_eq_of_separate`: for the DM-BC with separate channels,
  `p(y₁, y₂ | x₁, x₂) = p(y₁ | x₁) p(y₂ | x₂)`, the capacity region is the rectangle
  `R₁ ≤ C(p(y₁ | x₁))`, `R₂ ≤ C(p(y₂ | x₂))`.

## Implementation notes

The outer bound is proved by Fano's inequality at each receiver: fixing the message of
receiver 2 in a broadcast code gives a single-user code for `p(y₁ | x)` whose probability of
error, for a well chosen message, is at most `P₁⁽ⁿ⁾`, and the converse to the channel coding
theorem applies. For the symmetric DM-BC, decoding both messages from the output `Y₁` gives a
single-user code with `2^{n(R₁ + R₂)}` messages, with probability of error at most
`P₁⁽ⁿ⁾ + P₂⁽ⁿ⁾`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology Set

open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂]

variable {W : α → β₁ × β₂ → ℝ}

/-! ### The outer bound -/

/-- **Lecture 5 of [elgamal2010].** Receiver 1 alone sees a single-user channel: an achievable
rate pair has `R₁ ≤ C₁ = max_{p(x)} I(X; Y₁)` (in nats). -/
theorem IsAchievableBC.le_capacity₁ [Nonempty α] (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h : IsAchievableBC W R₁ R₂) : R₁ ≤ capacity (bcMarg₁ W) := by
  obtain ⟨c, h₁, -⟩ := (isAchievableBC_iff hW).1 h
  refine le_of_converse_bound h₁ (fun n => (c n).errProb₁_le_one hW (one_le_ceil_exp _)
    (one_le_ceil_exp _)) fun n _ => ?_
  obtain ⟨j, hj⟩ := (c n).exists_userCode₁_le (W := W) (one_le_ceil_exp _)
  have := ((c n).userCode₁ j).one_sub_avgErrProb_mul_log_le hW.bcMarg₁ (one_le_ceil_exp _)
  have hlog : 0 ≤ log (⌈exp (n * R₁)⌉₊ : ℝ) :=
    log_nonneg (by exact_mod_cast one_le_ceil_exp (n * R₁))
  have := mul_le_mul_of_nonneg_right (sub_le_sub_left hj 1) hlog
  linarith

/-- **Lecture 5 of [elgamal2010].** An achievable rate pair has `R₂ ≤ C₂ = max_{p(x)} I(X; Y₂)`
(in nats). -/
theorem IsAchievableBC.le_capacity₂ [Nonempty α] (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h : IsAchievableBC W R₁ R₂) : R₂ ≤ capacity (bcMarg₂ W) := by
  obtain ⟨c, -, h₂⟩ := (isAchievableBC_iff hW).1 h
  refine le_of_converse_bound h₂ (fun n => (c n).errProb₂_le_one hW (one_le_ceil_exp _)
    (one_le_ceil_exp _)) fun n _ => ?_
  obtain ⟨i, hi⟩ := (c n).exists_userCode₂_le (W := W) (one_le_ceil_exp _)
  have := ((c n).userCode₂ i).one_sub_avgErrProb_mul_log_le hW.bcMarg₂ (one_le_ceil_exp _)
  have hlog : 0 ≤ log (⌈exp (n * R₂)⌉₊ : ℝ) :=
    log_nonneg (by exact_mod_cast one_le_ceil_exp (n * R₂))
  have := mul_le_mul_of_nonneg_right (sub_le_sub_left hi 1) hlog
  linarith

/-- **Lecture 5 of [elgamal2010].** The outer bound `R₁ ≤ C₁`, `R₂ ≤ C₂`, in bits, with
`Cⱼ = max_{p(x)} I(X; Yⱼ)` the capacity of the channel `p(yⱼ | x)`. -/
def bcOuterBoundBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | R.1 ≤ capacity (bcMarg₁ W) / log 2 ∧ R.2 ≤ capacity (bcMarg₂ W) / log 2}

/-- **Lecture 5 of [elgamal2010].** The outer bound: every rate pair in the capacity region has
`R₁ ≤ C₁` and `R₂ ≤ C₂`. -/
theorem bcCapacityRegionBits_subset_bcOuterBoundBits [Nonempty α] (hW : IsChannel W) :
    bcCapacityRegionBits W ⊆ bcOuterBoundBits W := by
  have hl := log_pos one_lt_two
  have hc : IsClosed {R : ℝ × ℝ | R.1 ≤ capacity (bcMarg₁ W) ∧ R.2 ≤ capacity (bcMarg₂ W)} :=
    (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le continuous_snd continuous_const)
  rw [bcCapacityRegionBits_eq_smul hW]
  rintro _ ⟨R, hR, rfl⟩
  have hsub : {R : ℝ × ℝ | IsAchievableBC W R.1 R.2} ⊆
      {R : ℝ × ℝ | R.1 ≤ capacity (bcMarg₁ W) ∧ R.2 ≤ capacity (bcMarg₂ W)} := fun R hR =>
    ⟨IsAchievableBC.le_capacity₁ hW hR, IsAchievableBC.le_capacity₂ hW hR⟩
  have h := closure_minimal hsub hc hR
  simp only [bcOuterBoundBits, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    inv_mul_eq_div]
  exact ⟨div_le_div_of_nonneg_right h.1 hl.le, div_le_div_of_nonneg_right h.2 hl.le⟩

/-! ### The time-division inner bound -/

omit [Fintype α] in
/-- A rate achievable over the channel `p(y₁ | x)` is achievable for receiver 1 when receiver 2
has a single message. -/
theorem isAchievableBC_of_isAchievableRate₁ (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRate (bcMarg₁ W) R) : IsAchievableBC W R 0 := by
  obtain ⟨c, hc⟩ := h
  have h1 : ∀ n : ℕ, ⌈exp (n * (0 : ℝ))⌉₊ = 1 := fun n => by simp
  refine (isAchievableBC_iff hW).2 ⟨fun n => BCCode.ofReceiver₁Code (c n) (h1 n), ?_, ?_⟩
  · have e : ∀ n, (BCCode.ofReceiver₁Code (β₂ := β₂) (c n) (h1 n)).errProb₁ W =
        (c n).avgErrProb (bcMarg₁ W) := fun n =>
      BCCode.errProb₁_eq_avgErrProb _ _ (one_le_ceil_exp _) (by rw [h1]; exact one_pos) rfl
        fun _ => rfl
    simp only [e]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n => (c n).avgErrProb_nonneg hW.bcMarg₁) fun n => (c n).avgErrProb_le_maxErrProb
  · simp only [fun n => BCCode.errProb₂_eq_zero (W := W)
      (BCCode.ofReceiver₁Code (β₂ := β₂) (c n) (h1 n)) (h1 n)]
    exact tendsto_const_nhds

omit [Fintype α] in
/-- A rate achievable over the channel `p(y₂ | x)` is achievable for receiver 2 when receiver 1
has a single message. -/
theorem isAchievableBC_of_isAchievableRate₂ (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRate (bcMarg₂ W) R) : IsAchievableBC W 0 R := by
  obtain ⟨c, hc⟩ := h
  have h1 : ∀ n : ℕ, ⌈exp (n * (0 : ℝ))⌉₊ = 1 := fun n => by simp
  refine (isAchievableBC_iff hW).2 ⟨fun n => BCCode.ofReceiver₂Code (c n) (h1 n), ?_, ?_⟩
  · simp only [fun n => BCCode.errProb₁_eq_zero (W := W)
      (BCCode.ofReceiver₂Code (β₁ := β₁) (c n) (h1 n)) (h1 n)]
    exact tendsto_const_nhds
  · have e : ∀ n, (BCCode.ofReceiver₂Code (β₁ := β₁) (c n) (h1 n)).errProb₂ W =
        (c n).avgErrProb (bcMarg₂ W) := fun n =>
      BCCode.errProb₂_eq_avgErrProb _ _ (by rw [h1]; exact one_pos) (one_le_ceil_exp _) rfl
        fun _ => rfl
    simp only [e]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n => (c n).avgErrProb_nonneg hW.bcMarg₂) fun n => (c n).avgErrProb_le_maxErrProb

/-- `(C₁, 0)` is in the capacity region: receiver 2 has a single message and the sender codes for
the channel `p(y₁ | x)`. -/
lemma capacity₁_mem_bcCapacityRegionBits [Nonempty α] (hW : IsChannel W) :
    (capacity (bcMarg₁ W) / log 2, 0) ∈ bcCapacityRegionBits W := by
  have hmem : (capacity (bcMarg₁ W), 0) ∈ bcCapacityRegion W := by
    have hlim : Tendsto (fun k : ℕ => (capacity (bcMarg₁ W) - 1 / ((k : ℝ) + 1), (0 : ℝ)))
        atTop (𝓝 (capacity (bcMarg₁ W), 0)) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub
        (capacity (bcMarg₁ W))
      rw [sub_zero] at h
      exact h.prodMk_nhds tendsto_const_nhds
    exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k =>
      isAchievableBC_of_isAchievableRate₁ hW
        (isAchievableRate_of_lt_capacity hW.bcMarg₁ (sub_lt_self _ (by positivity))))
  rw [bcCapacityRegionBits_eq_smul hW]
  exact ⟨_, hmem, by ext <;> simp [div_eq_inv_mul]⟩

/-- `(0, C₂)` is in the capacity region. -/
lemma capacity₂_mem_bcCapacityRegionBits [Nonempty α] (hW : IsChannel W) :
    (0, capacity (bcMarg₂ W) / log 2) ∈ bcCapacityRegionBits W := by
  have hmem : (0, capacity (bcMarg₂ W)) ∈ bcCapacityRegion W := by
    have hlim : Tendsto (fun k : ℕ => ((0 : ℝ), capacity (bcMarg₂ W) - 1 / ((k : ℝ) + 1)))
        atTop (𝓝 (0, capacity (bcMarg₂ W))) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub
        (capacity (bcMarg₂ W))
      rw [sub_zero] at h
      exact tendsto_const_nhds.prodMk_nhds h
    exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k =>
      isAchievableBC_of_isAchievableRate₂ hW
        (isAchievableRate_of_lt_capacity hW.bcMarg₂ (sub_lt_self _ (by positivity))))
  rw [bcCapacityRegionBits_eq_smul hW]
  exact ⟨_, hmem, by ext <;> simp [div_eq_inv_mul]⟩

/-- **Lecture 5 of [elgamal2010].** The time-division inner bound: the rate pairs below
`(t C₁, (1 - t) C₂)` for some `t ∈ [0, 1]`, in bits. -/
def bcTimeDivisionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ t ∈ Icc (0 : ℝ) 1, R.1 ≤ t * (capacity (bcMarg₁ W) / log 2) ∧
    R.2 ≤ (1 - t) * (capacity (bcMarg₂ W) / log 2)}

/-- **Lecture 5 of [elgamal2010].** The time-division inner bound is in the capacity region. -/
theorem bcTimeDivisionBits_subset [Nonempty α] (hW : IsChannel W) :
    bcTimeDivisionBits W ⊆ bcCapacityRegionBits W := by
  rintro R ⟨t, ⟨ht0, ht1⟩, h₁, h₂⟩
  have hmix := convex_bcCapacityRegionBits hW (capacity₁_mem_bcCapacityRegionBits hW)
    (capacity₂_mem_bcCapacityRegionBits hW) ht0 (by linarith : 0 ≤ 1 - t) (by ring)
  refine mem_bcCapacityRegionBits_of_le hW hmix ?_ ?_ <;> simpa using by assumption

/-! ### Example: the symmetric DM-BC -/

section Symmetric

variable {β : Type*} [Fintype β]

/-- For a DM-BC with `𝒴₁ = 𝒴₂`, the single-user code sending both messages over the channel
`p(y₁ | x)`, and decoding them with the two decoders. The messages are numbered by
`finProdFinEquiv`. -/
def BCCode.bothMsgsCode {M₁ M₂ n : ℕ} (c : BCCode M₁ M₂ n α β β) :
    ChannelCode (M₁ * M₂) n α β :=
  ⟨fun k => c.enc (finProdFinEquiv.symm k), fun y => finProdFinEquiv (c.dec₁ y, c.dec₂ y)⟩

omit [Fintype α] in
/-- If `p(y₁ | x) = p(y₂ | x)`, the single-user code sending both messages over `p(y₁ | x)` has
probability of error at most `P₁⁽ⁿ⁾ + P₂⁽ⁿ⁾`. -/
lemma BCCode.avgErrProb_bothMsgsCode_le {M₁ M₂ n : ℕ} {W : α → β × β → ℝ}
    (c : BCCode M₁ M₂ n α β β) (hW : IsChannel W) (h : bcMarg₁ W = bcMarg₂ W) :
    c.bothMsgsCode.avgErrProb (bcMarg₁ W) ≤ c.errProb₁ W + c.errProb₂ W := by
  classical
  unfold ChannelCode.avgErrProb ChannelCode.condErrProb BCCode.errProb₁ BCCode.errProb₂
  rw [← h, ← add_div, ← sum_add_distrib, Nat.cast_mul]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← Equiv.sum_comp finProdFinEquiv]
  refine sum_le_sum fun w _ => ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun y _ => ?_
  have hnn := channelExt_nonneg hW.bcMarg₁ (c.enc w) y
  have henc : c.bothMsgsCode.enc (finProdFinEquiv w) = c.enc w := by
    change c.enc (finProdFinEquiv.symm (finProdFinEquiv w)) = c.enc w
    rw [Equiv.symm_apply_apply]
  have hdec : c.bothMsgsCode.dec y = finProdFinEquiv (c.dec₁ y, c.dec₂ y) := rfl
  simp only [henc, hdec, ne_eq, Equiv.apply_eq_iff_eq]
  by_cases h1 : c.dec₁ y = w.1 <;> by_cases h2 : c.dec₂ y = w.2 <;>
    simp [h1, h2, Prod.ext_iff, hnn]

/-- **Lecture 5 of [elgamal2010] (symmetric DM-BC).** If `p(y₁ | x) = p(y₂ | x)`, an achievable
rate pair has `R₁ + R₂ ≤ C₁` (in nats): as the capacity region only depends on the conditional
marginals, both receivers can be taken to see the same output, which carries both messages. -/
theorem IsAchievableBC.add_le_capacity_of_marg_eq [Nonempty α] {W : α → β × β → ℝ}
    (hW : IsChannel W) (h : bcMarg₁ W = bcMarg₂ W) {R₁ R₂ : ℝ} (hR : IsAchievableBC W R₁ R₂) :
    R₁ + R₂ ≤ capacity (bcMarg₁ W) := by
  obtain ⟨c, h₁, h₂⟩ := (isAchievableBC_iff hW).1 hR
  have hpos : ∀ n : ℕ, 0 < ⌈exp (n * R₁)⌉₊ * ⌈exp (n * R₂)⌉₊ := fun n =>
    Nat.mul_pos (one_le_ceil_exp _) (one_le_ceil_exp _)
  have hP : Tendsto (fun n => (c n).bothMsgsCode.avgErrProb (bcMarg₁ W)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using h₁.add h₂)
      (fun n => (c n).bothMsgsCode.avgErrProb_nonneg hW.bcMarg₁)
      fun n => (c n).avgErrProb_bothMsgsCode_le hW h
  refine le_of_converse_bound hP
    (fun n => BCCode.channelCode_avgErrProb_le_one hW.bcMarg₁ (hpos n) _)
    fun n _ => ?_
  have hc := (c n).bothMsgsCode.one_sub_avgErrProb_mul_log_le hW.bcMarg₁ (hpos n)
  have hM : ⌈exp (n * (R₁ + R₂))⌉₊ ≤ ⌈exp (n * R₁)⌉₊ * ⌈exp (n * R₂)⌉₊ :=
    ceil_exp_le_mul (mul_add _ _ _).le
  have hlog : log (⌈exp (n * (R₁ + R₂))⌉₊ : ℝ) ≤
      log ((⌈exp (n * R₁)⌉₊ * ⌈exp (n * R₂)⌉₊ : ℕ) : ℝ) :=
    log_le_log (by exact_mod_cast one_le_ceil_exp _) (by exact_mod_cast hM)
  have h1 := BCCode.channelCode_avgErrProb_le_one hW.bcMarg₁ (hpos n) (c n).bothMsgsCode
  have := mul_le_mul_of_nonneg_left hlog (sub_nonneg.2 h1)
  linarith

/-- **Lecture 5 of [elgamal2010] (symmetric DM-BC).** If `p(y₁ | x) = p(y₂ | x)`, every rate pair
in the capacity region has `R₁ + R₂ ≤ C₁`. -/
theorem add_le_of_mem_bcCapacityRegionBits_of_marg_eq [Nonempty α] {W : α → β × β → ℝ}
    (hW : IsChannel W) (h : bcMarg₁ W = bcMarg₂ W) {R : ℝ × ℝ}
    (hR : R ∈ bcCapacityRegionBits W) : R.1 + R.2 ≤ capacity (bcMarg₁ W) / log 2 := by
  have hl := log_pos one_lt_two
  have hc : IsClosed {R : ℝ × ℝ | R.1 + R.2 ≤ capacity (bcMarg₁ W)} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hsub : {R : ℝ × ℝ | IsAchievableBC W R.1 R.2} ⊆
      {R : ℝ × ℝ | R.1 + R.2 ≤ capacity (bcMarg₁ W)} := fun R hR =>
    IsAchievableBC.add_le_capacity_of_marg_eq hW h hR
  rw [bcCapacityRegionBits_eq_smul hW] at hR
  obtain ⟨S, hS, rfl⟩ := hR
  have h' : S.1 + S.2 ≤ capacity (bcMarg₁ W) := closure_minimal hsub hc hS
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [← mul_add, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right h' hl.le

/-- **Lecture 5 of [elgamal2010] (symmetric DM-BC).** If `p(y₁ | x) = p(y₂ | x)`, the
time-division inner bound is tight: the capacity region is the set of rate pairs below
`(t C₁, (1 - t) C₁)` for some `t ∈ [0, 1]`. -/
theorem bcCapacityRegionBits_eq_bcTimeDivisionBits_of_marg_eq [Nonempty α]
    {W : α → β × β → ℝ} (hW : IsChannel W) (h : bcMarg₁ W = bcMarg₂ W) :
    bcCapacityRegionBits W = bcTimeDivisionBits W := by
  refine le_antisymm (fun R hR => ?_) (bcTimeDivisionBits_subset hW)
  have hl := log_pos one_lt_two
  obtain ⟨ho₁, ho₂⟩ := bcCapacityRegionBits_subset_bcOuterBoundBits hW hR
  have hs := add_le_of_mem_bcCapacityRegionBits_of_marg_eq hW h hR
  rw [← h] at ho₂
  have hD : 0 ≤ capacity (bcMarg₁ W) / log 2 := div_nonneg (capacity_nonneg hW.bcMarg₁) hl.le
  simp only [bcTimeDivisionBits, Set.mem_ofPred_eq, ← h]
  set D := capacity (bcMarg₁ W) / log 2
  rcases le_or_gt R.1 0 with h0 | h0
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using h0, by simpa using ho₂⟩
  · have hDpos : 0 < D := h0.trans_le ho₁
    refine ⟨R.1 / D, ⟨div_nonneg h0.le hD, (div_le_one hDpos).2 ho₁⟩, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ hDpos.ne']
    · rw [sub_mul, div_mul_cancel₀ _ hDpos.ne', one_mul]
      linarith

end Symmetric

/-! ### Example: the DM-BC with separate channels -/

section Separate

variable {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂]

/-- The capacity of the channel `p(y | x₁, x₂) = p(y | x₁)`, which ignores its second input, is
the capacity of `p(y | x₁)`. -/
theorem capacity_comp_fst_input [Nonempty α₁] [Nonempty α₂] {V : α₁ → β₁ → ℝ}
    (hV : IsChannel V) : capacity (fun x : α₁ × α₂ => V x.1) = capacity V := by
  have hV' : IsChannel fun x : α₁ × α₂ => V x.1 := fun x => hV x.1
  rw [← opCapacity_eq_capacity hV, ← opCapacity_eq_capacity hV']
  unfold opCapacity
  congr 1
  ext R
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun n => ⟨fun i k => ((c n).enc i k).1, (c n).dec⟩, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun n => ⟨fun i k => ((c n).enc i k, Classical.arbitrary α₂), (c n).dec⟩, hc⟩

/-- The capacity of the channel `p(y | x₁, x₂) = p(y | x₂)`, which ignores its first input, is
the capacity of `p(y | x₂)`. -/
theorem capacity_comp_snd_input [Nonempty α₁] [Nonempty α₂] {V : α₂ → β₂ → ℝ}
    (hV : IsChannel V) : capacity (fun x : α₁ × α₂ => V x.2) = capacity V := by
  have hV' : IsChannel fun x : α₁ × α₂ => V x.2 := fun x => hV x.2
  rw [← opCapacity_eq_capacity hV, ← opCapacity_eq_capacity hV']
  unfold opCapacity
  congr 1
  ext R
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun n => ⟨fun i k => ((c n).enc i k).2, (c n).dec⟩, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun n => ⟨fun i k => (Classical.arbitrary α₁, (c n).enc i k), (c n).dec⟩, hc⟩

variable {W : α₁ × α₂ → β₁ × β₂ → ℝ} {W₁ : α₁ → β₁ → ℝ} {W₂ : α₂ → β₂ → ℝ}

omit [Fintype α₁] [Fintype α₂] [Fintype β₁] in
/-- With separate channels, `p(y₁ | x₁, x₂) = p(y₁ | x₁)`. -/
lemma bcMarg₁_eq_of_separate (hW₂ : IsChannel W₂)
    (hsep : ∀ x y, W x y = W₁ x.1 y.1 * W₂ x.2 y.2) : bcMarg₁ W = fun x => W₁ x.1 := by
  funext x y₁
  simp only [bcMarg₁, hsep, ← mul_sum, (hW₂ _).sum_eq_one, mul_one]

omit [Fintype α₁] [Fintype α₂] [Fintype β₂] in
/-- With separate channels, `p(y₂ | x₁, x₂) = p(y₂ | x₂)`. -/
lemma bcMarg₂_eq_of_separate (hW₁ : IsChannel W₁)
    (hsep : ∀ x y, W x y = W₁ x.1 y.1 * W₂ x.2 y.2) : bcMarg₂ W = fun x => W₂ x.2 := by
  funext x y₂
  simp only [bcMarg₂, hsep, ← sum_mul, (hW₁ _).sum_eq_one, one_mul]

/-- For a DM-BC with separate channels, the broadcast code made of a code for each receiver: the
first components of the codewords of `c₁` go to the first channel and the second components of
the codewords of `c₂` to the second. -/
def BCCode.ofSeparateCodes {M₁ M₂ n : ℕ} (c₁ : ChannelCode M₁ n (α₁ × α₂) β₁)
    (c₂ : ChannelCode M₂ n (α₁ × α₂) β₂) : BCCode M₁ M₂ n (α₁ × α₂) β₁ β₂ :=
  ⟨fun w i => ((c₁.enc w.1 i).1, (c₂.enc w.2 i).2), c₁.dec, c₂.dec⟩

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 5 of [elgamal2010] (DM-BC with separate channels).** For
`p(y₁, y₂ | x₁, x₂) = p(y₁ | x₁) p(y₂ | x₂)`, every pair of rates below the individual capacities
is achievable: each receiver gets its own channel. -/
theorem isAchievableBC_of_separate (hW : IsChannel W) (hW₁ : IsChannel W₁)
    (hW₂ : IsChannel W₂) (hsep : ∀ x y, W x y = W₁ x.1 y.1 * W₂ x.2 y.2) {R₁ R₂ : ℝ}
    (h₁ : IsAchievableRate (bcMarg₁ W) R₁) (h₂ : IsAchievableRate (bcMarg₂ W) R₂) :
    IsAchievableBC W R₁ R₂ := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  have hm₁ := bcMarg₁_eq_of_separate hW₂ hsep
  have hm₂ := bcMarg₂_eq_of_separate hW₁ hsep
  refine (isAchievableBC_iff hW).2 ⟨fun n => BCCode.ofSeparateCodes (c₁ n) (c₂ n), ?_, ?_⟩
  · have e : ∀ n, (BCCode.ofSeparateCodes (c₁ n) (c₂ n)).errProb₁ W =
        (c₁ n).avgErrProb (bcMarg₁ W) := fun n =>
      BCCode.errProb₁_eq_avgErrProb _ _ (one_le_ceil_exp _) (one_le_ceil_exp _) rfl fun w => by
        rw [hm₁]
        rfl
    simp only [e]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc₁
      (fun n => (c₁ n).avgErrProb_nonneg hW.bcMarg₁) fun n => (c₁ n).avgErrProb_le_maxErrProb
  · have e : ∀ n, (BCCode.ofSeparateCodes (c₁ n) (c₂ n)).errProb₂ W =
        (c₂ n).avgErrProb (bcMarg₂ W) := fun n =>
      BCCode.errProb₂_eq_avgErrProb _ _ (one_le_ceil_exp _) (one_le_ceil_exp _) rfl fun w => by
        rw [hm₂]
        rfl
    simp only [e]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc₂
      (fun n => (c₂ n).avgErrProb_nonneg hW.bcMarg₂) fun n => (c₂ n).avgErrProb_le_maxErrProb

/-- **Lecture 5 of [elgamal2010] (DM-BC with separate channels).** For
`p(y₁, y₂ | x₁, x₂) = p(y₁ | x₁) p(y₂ | x₂)`, the outer bound is tight: the capacity region is
`R₁ ≤ C₁`, `R₂ ≤ C₂`. -/
theorem bcCapacityRegionBits_eq_bcOuterBoundBits_of_separate [Nonempty α₁] [Nonempty α₂]
    (hW : IsChannel W) (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂)
    (hsep : ∀ x y, W x y = W₁ x.1 y.1 * W₂ x.2 y.2) :
    bcCapacityRegionBits W = bcOuterBoundBits W := by
  have hl := log_pos one_lt_two
  refine le_antisymm (bcCapacityRegionBits_subset_bcOuterBoundBits hW) fun R ⟨h₁, h₂⟩ => ?_
  have hS : log 2 • R ∈ bcSlackSet W := fun δ hδ => by
    refine isAchievableBC_of_separate hW hW₁ hW₂ hsep
      (isAchievableRate_of_lt_capacity hW.bcMarg₁ ?_)
      (isAchievableRate_of_lt_capacity hW.bcMarg₂ ?_)
    · have := (le_div_iff₀ hl).1 h₁
      simp only [Prod.smul_fst, smul_eq_mul]
      linarith
    · have := (le_div_iff₀ hl).1 h₂
      simp only [Prod.smul_snd, smul_eq_mul]
      linarith
  rw [bcCapacityRegionBits_eq_smul hW]
  exact ⟨_, bcSlackSet_subset_bcCapacityRegion hS, by
    change (log 2)⁻¹ • log 2 • R = R
    rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]⟩

/-- **Lecture 5 of [elgamal2010] (DM-BC with separate channels).** For
`p(y₁, y₂ | x₁, x₂) = p(y₁ | x₁) p(y₂ | x₂)`, the capacity region is the rectangle
`R₁ ≤ C(p(y₁ | x₁))`, `R₂ ≤ C(p(y₂ | x₂))`. -/
theorem bcCapacityRegionBits_eq_of_separate [Nonempty α₁] [Nonempty α₂]
    (hW : IsChannel W) (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂)
    (hsep : ∀ x y, W x y = W₁ x.1 y.1 * W₂ x.2 y.2) :
    bcCapacityRegionBits W =
      {R | R.1 ≤ capacity W₁ / log 2 ∧ R.2 ≤ capacity W₂ / log 2} := by
  rw [bcCapacityRegionBits_eq_bcOuterBoundBits_of_separate hW hW₁ hW₂ hsep, bcOuterBoundBits,
    bcMarg₁_eq_of_separate hW₂ hsep, bcMarg₂_eq_of_separate hW₁ hsep,
    capacity_comp_fst_input hW₁, capacity_comp_snd_input hW₂]

end Separate

end InfoTheory
