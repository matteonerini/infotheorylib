/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCBits
public import InfoTheoryLib.Network.MACBits
public import InfoTheoryLib.ChannelCoding.Converse

/-!
# Broadcast codes in bits: Lemma 1 and time sharing

In their lecture notes, El Gamal and Kim measure the rates of the DM-BC `p(y₁, y₂ | x)` in bits,
with `(2^{nR₁}, 2^{nR₂}, n)` codes. We show that the capacity region in bits is the capacity region
in nats (Section 15.6 of Cover and Thomas) scaled by `1 / log 2`, that it only depends on the
conditional marginals (Lemma 1 of Lecture 5), and that it is convex (time sharing).

## Main definitions

* `BCCode.pairErrProb`: the probability of error for a message pair.
* `BCCode.shrink`: a code restricted to fewer messages.
* `BCCode.concat`: two codes used one after the other.
* `bcSlackSet W`: the rate pairs `R` (in nats) with `R - (δ, δ)` achievable for every `δ > 0`.
* `BCCode.userCode₁`, `BCCode.userCode₂`: the single-user codes obtained by fixing the message of
  the other receiver.

## Main statements

* `BCCode.exists_errProb_le_of_le`: a code can be restricted to fewer messages without
  increasing its probability of error.
* `bcCapacityRegionBits_eq_smul`: the capacity region in bits is the one in nats scaled by
  `1 / log 2`.
* `isAchievableBCBits_iff`, `isAchievableBCBits_congr`, `bcCapacityRegionBits_eq_of_marg_eq`:
  **Lemma 1 of [elgamal2010], Lecture 5**, the capacity region only depends on the conditional
  marginals.
* `IsStochasticallyDegraded.capacityRegionBits_eq`: a stochastically degraded DM-BC has the
  capacity region of the corresponding physically degraded DM-BC.
* `convex_bcCapacityRegionBits`: time sharing, the capacity region is convex.
* `mem_bcCapacityRegionBits_of_le`: lowering the rates stays in the capacity region.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology Set

open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂]

/-! ### The probability of error for a message pair -/

namespace BCCode

variable {M₁ M₂ n : ℕ} {W : α → β₁ × β₂ → ℝ} (c : BCCode M₁ M₂ n α β₁ β₂)

/-- The pair `(g₁(y₁ⁿ), g₂(y₂ⁿ))` of the guesses of the two decoders. -/
def pairDec (y : Fin n → β₁ × β₂) : Fin M₁ × Fin M₂ :=
  (c.dec₁ fun i => (y i).1, c.dec₂ fun i => (y i).2)

open Classical in
/-- The probability `P(g₁(Y₁ⁿ) ≠ w₁ or g₂(Y₂ⁿ) ≠ w₂ | (w₁, w₂) sent)` that some receiver errs
when the message pair `w = (w₁, w₂)` is sent. -/
def pairErrProb (W : α → β₁ × β₂ → ℝ) (w : Fin M₁ × Fin M₂) : ℝ :=
  ∑ y, if c.pairDec y ≠ w then channelExt W n (c.enc w) y else 0

omit [Fintype α] in
/-- The probability of error is the average of the probabilities of error of the message
pairs. -/
lemma errProb_eq_sum_pairErrProb : c.errProb W = (∑ w, c.pairErrProb W w) / (M₁ * M₂) := by
  classical
  unfold errProb pairErrProb
  congr 1
  refine sum_congr rfl fun w _ => sum_congr rfl fun y _ => ?_
  have : (c.dec₁ (fun i => (y i).1) ≠ w.1 ∨ c.dec₂ (fun i => (y i).2) ≠ w.2) ↔
      c.pairDec y ≠ w := by
    simp only [pairDec, ne_eq, Prod.ext_iff, not_and_or]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.1 h1) h2
  · exact absurd (this.2 h2) h1
  · rfl

omit [Fintype α] in
lemma pairErrProb_nonneg (hW : IsChannel W) (w : Fin M₁ × Fin M₂) : 0 ≤ c.pairErrProb W w := by
  classical
  exact sum_nonneg fun y _ => by split_ifs <;> simp [channelExt_nonneg hW]

/-! ### Fewer messages -/

/-- Re-index the messages along injections `e₁`, `e₂`: send `xⁿ(e₁ k, e₂ l)` for the pair
`(k, l)`, and decode as the old code, mapping back to the new messages. -/
def shrink {M₁' M₂' : ℕ} [NeZero M₁'] [NeZero M₂'] (e₁ : Fin M₁' ↪ Fin M₁)
    (e₂ : Fin M₂' ↪ Fin M₂) : BCCode M₁' M₂' n α β₁ β₂ where
  enc k := c.enc (e₁ k.1, e₂ k.2)
  dec₁ y := Function.invFun e₁ (c.dec₁ y)
  dec₂ y := Function.invFun e₂ (c.dec₂ y)

omit [Fintype α] in
lemma pairErrProb_shrink_le {M₁' M₂' : ℕ} [NeZero M₁'] [NeZero M₂'] (hW : IsChannel W)
    (e₁ : Fin M₁' ↪ Fin M₁) (e₂ : Fin M₂' ↪ Fin M₂) (k : Fin M₁' × Fin M₂') :
    (c.shrink e₁ e₂).pairErrProb W k ≤ c.pairErrProb W (e₁ k.1, e₂ k.2) := by
  classical
  refine sum_le_sum fun y _ => ?_
  have hin : (c.shrink e₁ e₂).enc k = c.enc (e₁ k.1, e₂ k.2) := rfl
  rw [hin]
  by_cases h : c.pairDec y = (e₁ k.1, e₂ k.2)
  · have : (c.shrink e₁ e₂).pairDec y = k := by
      simp only [pairDec, Prod.mk.injEq] at h
      simp only [pairDec, shrink, h.1, h.2, Function.leftInverse_invFun e₁.injective k.1,
        Function.leftInverse_invFun e₂.injective k.2]
    simp [this, h]
  · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte]
    split_ifs <;> simp [channelExt_nonneg hW]

end BCCode

/-- Among the `M₁ × M₂` entries of an array, a sub-array of `M₁' × M₂'` entries has an average at
most the average of the array. -/
private lemma exists_embedding_sum_div_le {M₁ M₂ M₁' M₂' : ℕ} (L : Fin M₁ → Fin M₂ → ℝ)
    (h₁ : 0 < M₁') (h₂ : 0 < M₂') (hM₁ : M₁' ≤ M₁) (hM₂ : M₂' ≤ M₂) :
    ∃ (e₁ : Fin M₁' ↪ Fin M₁) (e₂ : Fin M₂' ↪ Fin M₂),
      (∑ k, ∑ l, L (e₁ k) (e₂ l)) / (M₁' * M₂') ≤ (∑ i, ∑ j, L i j) / (M₁ * M₂) := by
  classical
  obtain ⟨t₁, -, ht₁, hs₁⟩ := MACCode.exists_subset_sum_mul_le (fun i => ∑ j, L i j) univ
    (k := M₁') (by simpa using hM₁)
  obtain ⟨t₂, -, ht₂, hs₂⟩ := MACCode.exists_subset_sum_mul_le (fun j => ∑ i ∈ t₁, L i j) univ
    (k := M₂') (by simpa using hM₂)
  set e₁ := (t₁.orderEmbOfFin ht₁).toEmbedding
  set e₂ := (t₂.orderEmbOfFin ht₂).toEmbedding
  refine ⟨e₁, e₂, ?_⟩
  simp only [card_univ, Fintype.card_fin] at hs₁ hs₂
  have hle : ∑ k, ∑ l, L (e₁ k) (e₂ l) = ∑ i ∈ t₁, ∑ j ∈ t₂, L i j := by
    rw [← MACCode.sum_orderEmbOfFin t₁ ht₁ (fun i => ∑ j ∈ t₂, L i j)]
    refine sum_congr rfl fun k _ => ?_
    exact MACCode.sum_orderEmbOfFin t₂ ht₂ (fun j => L (e₁ k) j)
  have hswap : ∑ i ∈ t₁, ∑ j ∈ t₂, L i j = ∑ j ∈ t₂, ∑ i ∈ t₁, L i j := sum_comm
  have hswap' : ∑ j, ∑ i ∈ t₁, L i j = ∑ i ∈ t₁, ∑ j, L i j := sum_comm
  rw [hswap'] at hs₂
  have hM₁' : (0 : ℝ) < M₁' := by exact_mod_cast h₁
  have hM₂' : (0 : ℝ) < M₂' := by exact_mod_cast h₂
  have hM₁r : (M₁' : ℝ) ≤ M₁ := by exact_mod_cast hM₁
  have hM₂r : (M₂' : ℝ) ≤ M₂ := by exact_mod_cast hM₂
  have hM₁0 : (0 : ℝ) < M₁ := hM₁'.trans_le hM₁r
  have hM₂0 : (0 : ℝ) < M₂ := hM₂'.trans_le hM₂r
  rw [div_le_div_iff₀ (by positivity) (by positivity), hle, hswap]
  set X := ∑ j ∈ t₂, ∑ i ∈ t₁, L i j
  set Y := ∑ i ∈ t₁, ∑ j, L i j
  set Z := ∑ i, ∑ j, L i j
  calc X * (M₁ * M₂) = (X * M₂) * M₁ := by ring
    _ ≤ (Y * M₂') * M₁ := mul_le_mul_of_nonneg_right hs₂ (by positivity)
    _ = (Y * M₁) * M₂' := by ring
    _ ≤ (Z * M₁') * M₂' := mul_le_mul_of_nonneg_right hs₁ hM₂'.le
    _ = Z * (M₁' * M₂') := by ring

namespace BCCode

variable {M₁ M₂ n : ℕ} {W : α → β₁ × β₂ → ℝ} (c : BCCode M₁ M₂ n α β₁ β₂)

omit [Fintype α] in
/-- A code can be restricted to `M₁' ≤ M₁` and `M₂' ≤ M₂` messages without increasing its
probability of error. -/
theorem exists_errProb_le_of_le (hW : IsChannel W) {M₁' M₂' : ℕ} (h₁ : 0 < M₁') (h₂ : 0 < M₂')
    (hM₁ : M₁' ≤ M₁) (hM₂ : M₂' ≤ M₂) :
    ∃ c' : BCCode M₁' M₂' n α β₁ β₂, c'.errProb W ≤ c.errProb W := by
  have : NeZero M₁' := ⟨h₁.ne'⟩
  have : NeZero M₂' := ⟨h₂.ne'⟩
  obtain ⟨e₁, e₂, he⟩ := exists_embedding_sum_div_le (fun i j => c.pairErrProb W (i, j)) h₁ h₂
    hM₁ hM₂
  refine ⟨c.shrink e₁ e₂, ?_⟩
  rw [errProb_eq_sum_pairErrProb, errProb_eq_sum_pairErrProb, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  exact le_trans (div_le_div_of_nonneg_right (sum_le_sum fun k _ => sum_le_sum fun l _ =>
    c.pairErrProb_shrink_le hW e₁ e₂ (k, l)) (by positivity)) he

end BCCode

namespace BCCode

variable {M₁ M₂ n : ℕ} {W : α → β₁ × β₂ → ℝ} (c : BCCode M₁ M₂ n α β₁ β₂)

omit [Fintype α] in
private lemma errProb_nonneg' (hW : IsChannel W) : 0 ≤ c.errProb W :=
  (c.errProb₁_nonneg hW).trans ((le_max_left _ _).trans (c.max_errProb_le hW))

/-- A code with `M₁', M₂' ≥ 1` messages sending a fixed codeword of `c` and making a fixed
guess. -/
private def trivialOf (h₁ : 0 < M₁) (h₂ : 0 < M₂) (M₁' M₂' : ℕ) [NeZero M₁'] [NeZero M₂'] :
    BCCode M₁' M₂' n α β₁ β₂ :=
  ⟨fun _ => c.enc (⟨0, h₁⟩, ⟨0, h₂⟩), fun _ => 0, fun _ => 0⟩

end BCCode

/-! ### Rates in bits and in nats -/

variable {W W' : α → β₁ × β₂ → ℝ}

omit [Fintype α] in
/-- A rate pair achievable in bits is achievable in nats, after multiplying by `log 2`: a
`(2^{nR₁}, 2^{nR₂}, n)` code has at least `⌈e^{nR₁ log 2}⌉` and `⌈e^{nR₂ log 2}⌉` messages. -/
theorem IsAchievableBCBits.isAchievableBC (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h : IsAchievableBCBits W R₁ R₂) : IsAchievableBC W (R₁ * log 2) (R₂ * log 2) := by
  obtain ⟨c, hc⟩ := h
  have hsub : ∀ n : ℕ, ∃ c' : BCCode ⌈exp (n * (R₁ * log 2))⌉₊ ⌈exp (n * (R₂ * log 2))⌉₊ n
      α β₁ β₂, c'.errProb W ≤ (c n).errProb W := fun n =>
    (c n).exists_errProb_le_of_le hW (one_le_ceil_exp _) (one_le_ceil_exp _)
      (ceil_exp_le_two_pow n R₁) (ceil_exp_le_two_pow n R₂)
  choose c' hc' using hsub
  exact ⟨c', tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => (c' n).errProb_nonneg' hW) hc'⟩

omit [Fintype α] in
/-- A rate pair achievable in nats is achievable in bits, after dividing by `log 2`, up to an
arbitrarily small loss. -/
theorem IsAchievableBC.isAchievableBCBits (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h : IsAchievableBC W R₁ R₂) {δ : ℝ} (hδ : 0 < δ) :
    IsAchievableBCBits W (R₁ / log 2 - δ) (R₂ / log 2 - δ) := by
  obtain ⟨c, hc⟩ := h
  have hsub : ∀ n : ℕ, ∃ c' : BCCode (2 ^ ⌈n * (R₁ / log 2 - δ)⌉₊)
      (2 ^ ⌈n * (R₂ / log 2 - δ)⌉₊) n α β₁ β₂,
      1 ≤ n * δ → c'.errProb W ≤ (c n).errProb W := fun n => by
    by_cases hn : 1 ≤ n * δ
    · obtain ⟨c', hc'⟩ := (c n).exists_errProb_le_of_le hW (by positivity) (by positivity)
        (two_pow_ceil_le_ceil_exp hn) (two_pow_ceil_le_ceil_exp hn)
      exact ⟨c', fun _ => hc'⟩
    · have : NeZero (2 ^ ⌈n * (R₁ / log 2 - δ)⌉₊) := ⟨by positivity⟩
      have : NeZero (2 ^ ⌈n * (R₂ / log 2 - δ)⌉₊) := ⟨by positivity⟩
      exact ⟨(c n).trivialOf (one_le_ceil_exp _) (one_le_ceil_exp _) _ _,
        fun h' => absurd h' hn⟩
  choose c' hc' using hsub
  refine ⟨c', tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Eventually.of_forall fun n => (c' n).errProb_nonneg' hW) ?_⟩
  filter_upwards [eventually_ge_atTop ⌈1 / δ⌉₊] with n hn
  refine hc' n ?_
  have := (div_le_iff₀ hδ).1 (Nat.ceil_le.1 hn)
  linarith

omit [Fintype α] in
/-- **Lecture 5 of [elgamal2010].** The capacity region in bits is the capacity region in nats
scaled by `1 / log 2`. -/
theorem bcCapacityRegionBits_eq_smul (hW : IsChannel W) :
    bcCapacityRegionBits W = (log 2)⁻¹ • bcCapacityRegion W := by
  have hl := log_pos one_lt_two
  set A := {R : ℝ × ℝ | IsAchievableBCBits W R.1 R.2}
  set B := {R : ℝ × ℝ | IsAchievableBC W R.1 R.2}
  have h1 : A ⊆ (log 2)⁻¹ • B := fun R hR =>
    ⟨R * (log 2, log 2), hR.isAchievableBC hW, by
      ext <;> simp [field]⟩
  have h2 : (log 2)⁻¹ • B ⊆ closure A := by
    rintro _ ⟨R, hR, rfl⟩
    have hlim : Tendsto (fun k : ℕ => (R.1 / log 2 - 1 / ((k : ℝ) + 1),
        R.2 / log 2 - 1 / ((k : ℝ) + 1))) atTop (𝓝 ((log 2)⁻¹ • R)) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h1 : Tendsto (fun k : ℕ => R.1 / log 2 - 1 / ((k : ℝ) + 1)) atTop
          (𝓝 (R.1 / log 2 - 0)) := tendsto_const_nhds.sub h
      have h2 : Tendsto (fun k : ℕ => R.2 / log 2 - 1 / ((k : ℝ) + 1)) atTop
          (𝓝 (R.2 / log 2 - 0)) := tendsto_const_nhds.sub h
      rw [sub_zero] at h1 h2
      convert h1.prodMk_nhds h2 using 2
      ext <;> simp [div_eq_inv_mul]
    exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k =>
      IsAchievableBC.isAchievableBCBits hW hR (by positivity))
  refine le_antisymm ?_ ?_
  · calc bcCapacityRegionBits W ⊆ closure ((log 2)⁻¹ • B) := closure_mono h1
      _ = (log 2)⁻¹ • bcCapacityRegion W := closure_smul₀ _ _
  · calc (log 2)⁻¹ • bcCapacityRegion W = closure ((log 2)⁻¹ • B) := (closure_smul₀ _ _).symm
      _ ⊆ closure (closure A) := closure_mono h2
      _ = bcCapacityRegionBits W := closure_closure

/-! ### Lemma 1: the capacity region only depends on the conditional marginals -/

omit [Fintype α] in
/-- **Lemma 1 of [elgamal2010], Lecture 5 (proof).** A rate pair is achievable iff there are codes
whose probabilities of error `P₁⁽ⁿ⁾`, `P₂⁽ⁿ⁾` at both receivers tend to `0`. -/
theorem isAchievableBCBits_iff (hW : IsChannel W) {R₁ R₂ : ℝ} :
    IsAchievableBCBits W R₁ R₂ ↔ ∃ c : ∀ n : ℕ, BCCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α β₁ β₂,
      Tendsto (fun n => (c n).errProb₁ W) atTop (𝓝 0) ∧
        Tendsto (fun n => (c n).errProb₂ W) atTop (𝓝 0) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun n => (c n).errProb₁_nonneg hW)
        fun n => (le_max_left _ _).trans ((c n).max_errProb_le hW)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun n => (c n).errProb₂_nonneg hW)
        fun n => (le_max_right _ _).trans ((c n).max_errProb_le hW)
  · rintro ⟨c, h₁, h₂⟩
    refine ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using h₁.add h₂) (fun n => (c n).errProb_nonneg' hW)
      fun n => (c n).errProb_le_add hW⟩

omit [Fintype α] in
/-- **Lemma 1 of [elgamal2010], Lecture 5.** Whether a rate pair is achievable only depends on the
conditional marginals `p(y₁ | x)` and `p(y₂ | x)`. -/
theorem isAchievableBCBits_congr (hW : IsChannel W) (hW' : IsChannel W')
    (h₁ : bcMarg₁ W = bcMarg₁ W') (h₂ : bcMarg₂ W = bcMarg₂ W') {R₁ R₂ : ℝ} :
    IsAchievableBCBits W R₁ R₂ ↔ IsAchievableBCBits W' R₁ R₂ := by
  rw [isAchievableBCBits_iff hW, isAchievableBCBits_iff hW']
  refine exists_congr fun c => ?_
  simp only [fun n => (c n).errProb₁_congr h₁, fun n => (c n).errProb₂_congr h₂]

omit [Fintype α] in
/-- **Lemma 1 of [elgamal2010], Lecture 5.** The capacity region of the DM-BC depends on
`p(y₁, y₂ | x)` only through the conditional marginals `p(y₁ | x)` and `p(y₂ | x)`. -/
theorem bcCapacityRegionBits_eq_of_marg_eq (hW : IsChannel W) (hW' : IsChannel W')
    (h₁ : bcMarg₁ W = bcMarg₁ W') (h₂ : bcMarg₂ W = bcMarg₂ W') :
    bcCapacityRegionBits W = bcCapacityRegionBits W' := by
  unfold bcCapacityRegionBits
  congr 1
  ext R
  exact isAchievableBCBits_congr hW hW' h₁ h₂

omit [Fintype α] in
/-- **Lecture 5 of [elgamal2010].** The capacity region of a stochastically degraded DM-BC, with
`p(y₂ | x) = ∑_{y₁} p(y₁ | x) p'(y₂ | y₁)`, is that of the physically degraded DM-BC
`p(y₁ | x) p'(y₂ | y₁)`. -/
theorem IsStochasticallyDegraded.capacityRegionBits_eq (hW : IsChannel W) {V : β₁ → β₂ → ℝ}
    (hV : IsChannel V) (h : ∀ x y₂, bcMarg₂ W x y₂ = ∑ y₁, bcMarg₁ W x y₁ * V y₁ y₂) :
    bcCapacityRegionBits W = bcCapacityRegionBits fun x y => bcMarg₁ W x y.1 * V y.1 y.2 := by
  have hW' : IsChannel fun x (y : β₁ × β₂) => bcMarg₁ W x y.1 * V y.1 y.2 := fun x =>
    ⟨fun y => mul_nonneg ((hW.bcMarg₁ x).nonneg _) ((hV _).nonneg _), by
      rw [Fintype.sum_prod_type]
      simp only [← mul_sum, (hV _).sum_eq_one, mul_one]
      exact (hW.bcMarg₁ x).sum_eq_one⟩
  rw [bcCapacityRegionBits_eq_smul hW, bcCapacityRegionBits_eq_smul hW',
    IsStochasticallyDegraded.capacityRegion_eq hW hV h]

/-! ### Lower rates -/

omit [Fintype α] in
/-- Lower rates are achievable. -/
theorem IsAchievableBC.mono (hW : IsChannel W) {R₁ R₂ R₁' R₂' : ℝ}
    (h : IsAchievableBC W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) :
    IsAchievableBC W R₁' R₂' := by
  obtain ⟨c, hc⟩ := h
  have hle : ∀ (n : ℕ) {a b : ℝ}, a ≤ b → ⌈exp (n * a)⌉₊ ≤ ⌈exp (n * b)⌉₊ := fun n _ _ hab =>
    Nat.ceil_mono (exp_le_exp.2 (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)))
  choose c' hc' using fun n => (c n).exists_errProb_le_of_le hW (one_le_ceil_exp _)
    (one_le_ceil_exp _) (hle n h₁) (hle n h₂)
  exact ⟨c', tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => (c' n).errProb_nonneg' hW) hc'⟩

omit [Fintype α] in
/-- Lower rates are achievable, in bits. -/
theorem IsAchievableBCBits.mono (hW : IsChannel W) {R₁ R₂ R₁' R₂' : ℝ}
    (h : IsAchievableBCBits W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) :
    IsAchievableBCBits W R₁' R₂' := by
  obtain ⟨c, hc⟩ := h
  have hle : ∀ (n : ℕ) {a b : ℝ}, a ≤ b → 2 ^ ⌈n * a⌉₊ ≤ 2 ^ ⌈n * b⌉₊ := fun n _ _ hab =>
    Nat.pow_le_pow_right two_pos
      (Nat.ceil_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)))
  choose c' hc' using fun n => (c n).exists_errProb_le_of_le hW (by positivity)
    (by positivity) (hle n h₁) (hle n h₂)
  exact ⟨c', tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => (c' n).errProb_nonneg' hW) hc'⟩

omit [Fintype α] in
/-- **Lecture 5 of [elgamal2010].** Lowering the rates of a pair in the capacity region stays in
the capacity region. -/
theorem mem_bcCapacityRegionBits_of_le (hW : IsChannel W) {R R' : ℝ × ℝ}
    (hR : R ∈ bcCapacityRegionBits W) (h₁ : R'.1 ≤ R.1) (h₂ : R'.2 ≤ R.2) :
    R' ∈ bcCapacityRegionBits W := by
  set φ : ℝ × ℝ → ℝ × ℝ := fun x => x - (R - R')
  have hφ : Continuous φ := continuous_id.sub continuous_const
  have himage : φ '' {R | IsAchievableBCBits W R.1 R.2} ⊆ {R | IsAchievableBCBits W R.1 R.2} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.mono hW (by simp only [φ, Prod.fst_sub]; linarith)
      (by simp only [φ, Prod.snd_sub]; linarith)
  have := image_closure_subset_closure_image hφ ⟨R, hR, rfl⟩
  simp only [φ, sub_sub_cancel] at this
  exact closure_mono himage this

/-! ### Time sharing -/

namespace BCCode

variable {M₁ M₂ n : ℕ} {W : α → β₁ × β₂ → ℝ} (c : BCCode M₁ M₂ n α β₁ β₂)

/-- The code sending the first components of the messages with `c` during the first `n` symbols
and the second components with `c'` during the last `n'` symbols. The messages of the new code
are pairs, numbered by `finProdFinEquiv`. -/
def concat {M₁' M₂' n' : ℕ} (c' : BCCode M₁' M₂' n' α β₁ β₂) :
    BCCode (M₁ * M₁') (M₂ * M₂') (n + n') α β₁ β₂ where
  enc w := Fin.append (c.enc ((finProdFinEquiv.symm w.1).1, (finProdFinEquiv.symm w.2).1))
    (c'.enc ((finProdFinEquiv.symm w.1).2, (finProdFinEquiv.symm w.2).2))
  dec₁ y := finProdFinEquiv (c.dec₁ fun k => y (Fin.castAdd n' k),
    c'.dec₁ fun k => y (Fin.natAdd n k))
  dec₂ y := finProdFinEquiv (c.dec₂ fun k => y (Fin.castAdd n' k),
    c'.dec₂ fun k => y (Fin.natAdd n k))

omit [Fintype α] [Fintype β₁] [Fintype β₂] in
private lemma channelExt_fin_append {γ : Type*} (V : α → γ → ℝ) {n' : ℕ} (x : Fin n → α)
    (x' : Fin n' → α) (u : Fin n → γ) (v : Fin n' → γ) :
    channelExt V (n + n') (Fin.append x x') (Fin.append u v) =
      channelExt V n x u * channelExt V n' x' v := by
  simp only [channelExt, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

omit [Fintype α] [Fintype β₁] [Fintype β₂] in
lemma pairDec_concat {M₁' M₂' n' : ℕ} (c' : BCCode M₁' M₂' n' α β₁ β₂) (u : Fin n → β₁ × β₂)
    (v : Fin n' → β₁ × β₂) :
    (c.concat c').pairDec (Fin.append u v) =
      (finProdFinEquiv ((c.pairDec u).1, (c'.pairDec v).1),
        finProdFinEquiv ((c.pairDec u).2, (c'.pairDec v).2)) := by
  simp only [pairDec, concat, Fin.append_left, Fin.append_right]

omit [Fintype α] in
/-- The probability of error of two codes used one after the other is at most the sum of their
probabilities of error. -/
lemma pairErrProb_concat_le (hW : IsChannel W) {M₁' M₂' n' : ℕ}
    (c' : BCCode M₁' M₂' n' α β₁ β₂) (w : Fin (M₁ * M₁') × Fin (M₂ * M₂')) :
    (c.concat c').pairErrProb W w ≤
      c.pairErrProb W ((finProdFinEquiv.symm w.1).1, (finProdFinEquiv.symm w.2).1) +
        c'.pairErrProb W ((finProdFinEquiv.symm w.1).2, (finProdFinEquiv.symm w.2).2) := by
  classical
  set w₁ := ((finProdFinEquiv.symm w.1).1, (finProdFinEquiv.symm w.2).1)
  set w₂ := ((finProdFinEquiv.symm w.1).2, (finProdFinEquiv.symm w.2).2)
  set P := channelExt W n (c.enc w₁)
  set P' := channelExt W n' (c'.enc w₂)
  have hP := (hW.ext n) (c.enc w₁)
  have hP' := (hW.ext n') (c'.enc w₂)
  have key : ∀ u v, (if (c.concat c').pairDec (Fin.append u v) ≠ w then
      channelExt W (n + n') ((c.concat c').enc w) (Fin.append u v) else 0) ≤
      P' v * (if c.pairDec u ≠ w₁ then P u else 0) +
        P u * (if c'.pairDec v ≠ w₂ then P' v else 0) := by
    intro u v
    have henc : (c.concat c').enc w = Fin.append (c.enc w₁) (c'.enc w₂) := rfl
    rw [henc, channelExt_fin_append]
    have h0 : 0 ≤ P u * P' v := mul_nonneg (hP.nonneg u) (hP'.nonneg v)
    by_cases h1 : c.pairDec u = w₁
    · by_cases h2 : c'.pairDec v = w₂
      · have : (c.concat c').pairDec (Fin.append u v) = w := by
          rw [pairDec_concat, h1, h2]
          simp only [w₁, w₂, Prod.mk.eta, Equiv.apply_symm_apply]
        simp only [this, h1, h2, ne_eq, not_true_eq_false, ↓reduceIte, mul_zero, add_zero,
          le_refl]
      · simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, mul_zero,
          zero_add]
        split_ifs <;> linarith
    · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte]
      have : 0 ≤ P u * (if c'.pairDec v = w₂ then 0 else P' v) := by
        split_ifs
        · simp
        · exact h0
      split_ifs <;> nlinarith
  calc (c.concat c').pairErrProb W w
      = ∑ uv : (Fin n → β₁ × β₂) × (Fin n' → β₁ × β₂), (if (c.concat c').pairDec
          (Fin.appendEquiv n n' uv) ≠ w then channelExt W (n + n') ((c.concat c').enc w)
          (Fin.appendEquiv n n' uv) else 0) := (Equiv.sum_comp (Fin.appendEquiv n n') _).symm
    _ ≤ ∑ uv : (Fin n → β₁ × β₂) × (Fin n' → β₁ × β₂), (P' uv.2 * (if c.pairDec uv.1 ≠ w₁
          then P uv.1 else 0) + P uv.1 * (if c'.pairDec uv.2 ≠ w₂ then P' uv.2 else 0)) :=
        sum_le_sum fun uv _ => key uv.1 uv.2
    _ = c.pairErrProb W w₁ + c'.pairErrProb W w₂ := by
        rw [Fintype.sum_prod_type]
        simp only [sum_add_distrib]
        have e1 : ∀ u, ∑ v, P' v * (if c.pairDec u ≠ w₁ then P u else 0) =
            if c.pairDec u ≠ w₁ then P u else 0 := fun u => by
          rw [← sum_mul, hP'.sum_eq_one, one_mul]
        have e2 : ∑ u, ∑ v, P u * (if c'.pairDec v ≠ w₂ then P' v else 0) =
            ∑ v, if c'.pairDec v ≠ w₂ then P' v else 0 := by
          simp_rw [← mul_sum]
          rw [← sum_mul, hP.sum_eq_one, one_mul]
        rw [e2]
        simp only [e1]
        rfl

omit [Fintype α] in
/-- The probability of error of two codes used one after the other is at most the sum of their
probabilities of error. -/
theorem errProb_concat_le (hW : IsChannel W) {M₁' M₂' n' : ℕ}
    (c' : BCCode M₁' M₂' n' α β₁ β₂) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₁' : 0 < M₁')
    (h₂' : 0 < M₂') : (c.concat c').errProb W ≤ c.errProb W + c'.errProb W := by
  set L := fun a b => c.pairErrProb W (a, b)
  set L' := fun a b => c'.pairErrProb W (a, b)
  have hsum : ∑ w, (c.concat c').pairErrProb W w ≤
      M₁' * M₂' * ∑ i, ∑ j, L i j + M₁ * M₂ * ∑ i, ∑ j, L' i j := by
    calc ∑ w, (c.concat c').pairErrProb W w
        ≤ ∑ w : Fin (M₁ * M₁') × Fin (M₂ * M₂'),
            (L (finProdFinEquiv.symm w.1).1 (finProdFinEquiv.symm w.2).1 +
              L' (finProdFinEquiv.symm w.1).2 (finProdFinEquiv.symm w.2).2) :=
          sum_le_sum fun w _ => c.pairErrProb_concat_le hW c' w
      _ = ∑ p : Fin M₁ × Fin M₁', ∑ q : Fin M₂ × Fin M₂', (L p.1 q.1 + L' p.2 q.2) := by
          rw [Fintype.sum_prod_type, ← Equiv.sum_comp finProdFinEquiv]
          refine sum_congr rfl fun p _ => ?_
          rw [← Equiv.sum_comp finProdFinEquiv]
          simp
      _ = M₁' * M₂' * ∑ i, ∑ j, L i j + M₁ * M₂ * ∑ i, ∑ j, L' i j := by
          simp only [sum_add_distrib]
          have h' : ∑ p : Fin M₁ × Fin M₁', ∑ q : Fin M₂ × Fin M₂', L' p.2 q.2 =
              ∑ p : Fin M₁' × Fin M₁, ∑ q : Fin M₂' × Fin M₂, L' p.1 q.1 := by
            rw [← Equiv.sum_comp (Equiv.prodComm _ _)]
            refine sum_congr rfl fun p _ => ?_
            rw [← Equiv.sum_comp (Equiv.prodComm _ _)]
            rfl
          rw [h', MACCode.sum_prod_sum_prod_fst, MACCode.sum_prod_sum_prod_fst]
          simp
  have e : ∑ w, c.pairErrProb W w = ∑ i, ∑ j, L i j := Fintype.sum_prod_type _
  have e' : ∑ w, c'.pairErrProb W w = ∑ i, ∑ j, L' i j := Fintype.sum_prod_type _
  have hM₁ : (0 : ℝ) < M₁ := by exact_mod_cast h₁
  have hM₂ : (0 : ℝ) < M₂ := by exact_mod_cast h₂
  have hM₁' : (0 : ℝ) < M₁' := by exact_mod_cast h₁'
  have hM₂' : (0 : ℝ) < M₂' := by exact_mod_cast h₂'
  rw [errProb_eq_sum_pairErrProb, errProb_eq_sum_pairErrProb, errProb_eq_sum_pairErrProb, e, e',
    div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by push_cast; positivity)
    (by positivity)]
  push_cast
  calc (∑ w, (c.concat c').pairErrProb W w) * (M₁ * M₂ * (M₁' * M₂'))
      ≤ (M₁' * M₂' * ∑ i, ∑ j, L i j + M₁ * M₂ * ∑ i, ∑ j, L' i j) * (M₁ * M₂ * (M₁' * M₂')) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = ((∑ i, ∑ j, L i j) * (M₁' * M₂') + M₁ * M₂ * ∑ i, ∑ j, L' i j) *
          (M₁ * M₁' * (M₂ * M₂')) := by ring

/-- Transport a code along an equality of block lengths. -/
private def castLen {n' : ℕ} (h : n = n') : BCCode M₁ M₂ n' α β₁ β₂ := h ▸ c

omit [Fintype α] in
private lemma errProb_castLen {n' : ℕ} (h : n = n') :
    (c.castLen h).errProb W = c.errProb W := by
  subst h
  rfl

end BCCode

/-- The rate pairs `R` (in nats) such that `R - (δ, δ)` is achievable for every `δ > 0`. -/
def bcSlackSet (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∀ δ > 0, IsAchievableBC W (R.1 - δ) (R.2 - δ)}

omit [Fintype α] in
/-- To prove that a rate pair is achievable, it suffices to find codes for all large `n`, with
error probabilities bounded by a sequence tending to `0`. -/
private lemma isAchievableBC_of_forall_ge' [Nonempty α] (hW : IsChannel W)
    {R₁ R₂ : ℝ} {P : ℕ → ℝ} (hP : Tendsto P atTop (𝓝 0)) (N : ℕ)
    (h : ∀ n ≥ N, ∃ c : BCCode ⌈exp (n * R₁)⌉₊ ⌈exp (n * R₂)⌉₊ n α β₁ β₂,
      c.errProb W ≤ P n) : IsAchievableBC W R₁ R₂ := by
  have hz : ∀ n : ℕ, NeZero ⌈exp (n * R₁)⌉₊ ∧ NeZero ⌈exp (n * R₂)⌉₊ := fun n =>
    ⟨⟨Nat.one_le_iff_ne_zero.1 (one_le_ceil_exp _)⟩, ⟨Nat.one_le_iff_ne_zero.1 (one_le_ceil_exp _)⟩⟩
  let c : ∀ n : ℕ, BCCode ⌈exp (n * R₁)⌉₊ ⌈exp (n * R₂)⌉₊ n α β₁ β₂ := fun n =>
    if hn : N ≤ n then (h n hn).choose else
      have := (hz n).1
      have := (hz n).2
      ⟨fun _ _ => Classical.arbitrary α, fun _ => 0, fun _ => 0⟩
  refine ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hP
    (Eventually.of_forall fun n => (c n).errProb_nonneg' hW) ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [c, hn, ↓reduceDIte]
  exact (h n hn).choose_spec

omit [Fintype α] in
/-- **Time sharing (Lecture 5 of [elgamal2010]).** If `R` and `R'` are achievable up to an
arbitrarily small loss, so is every convex combination `λR + (1 - λ)R'`: use a code of rate `R`
for the first `⌊λn⌋` transmissions and a code of rate `R'` for the others. -/
theorem convex_bcSlackSet [Nonempty α] (hW : IsChannel W) : Convex ℝ (bcSlackSet W) := by
  rw [convex_iff_forall_pos]
  intro R hR R' hR' a b ha hb hab δ hδ
  obtain ⟨ca, hca⟩ := hR (δ / 2) (by positivity)
  obtain ⟨cb, hcb⟩ := hR' (δ / 2) (by positivity)
  have hb' : b = 1 - a := by linarith
  subst hb'
  set n₁ : ℕ → ℕ := fun n => ⌊a * n⌋₊
  have hn₁ : ∀ n : ℕ, (n₁ n : ℝ) ≤ a * n := fun n => Nat.floor_le (by positivity)
  have hn₁' : ∀ n : ℕ, a * n < n₁ n + 1 := fun n => Nat.lt_floor_add_one _
  have hn₁n : ∀ n : ℕ, n₁ n ≤ n := fun n => by
    have : (n₁ n : ℝ) ≤ n := (hn₁ n).trans (mul_le_of_le_one_left (Nat.cast_nonneg n) (by linarith))
    exact_mod_cast this
  set P : ℕ → ℝ := fun n => (ca (n₁ n)).errProb W + (cb (n - n₁ n)).errProb W
  have hP : Tendsto P atTop (𝓝 0) := by
    have h1 : Tendsto n₁ atTop atTop :=
      tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
    have h2 : Tendsto (fun n => n - n₁ n) atTop atTop := by
      rw [← tendsto_natCast_atTop_iff (R := ℝ)]
      refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop.const_mul_atTop hb)
      rw [Nat.cast_sub (hn₁n n)]
      linarith [hn₁ n]
    simpa using (hca.comp h1).add (hcb.comp h2)
  set N := ⌈2 * (|R.1 - R'.1| + |R.2 - R'.2|) / δ⌉₊
  refine isAchievableBC_of_forall_ge' hW hP N fun n hn => ?_
  have hnδ : 2 * (|R.1 - R'.1| + |R.2 - R'.2|) ≤ n * δ := by
    have : 2 * (|R.1 - R'.1| + |R.2 - R'.2|) / δ ≤ n := (Nat.ceil_le.1 hn)
    rwa [div_le_iff₀ hδ] at this
  have habs₁ := abs_nonneg (R.1 - R'.1)
  have habs₂ := abs_nonneg (R.2 - R'.2)
  have hcast : ((n - n₁ n : ℕ) : ℝ) = n - n₁ n := Nat.cast_sub (hn₁n n)
  have hmsg : ∀ r r' : ℝ, 2 * |r - r'| ≤ n * δ →
      ⌈exp (n * (a * r + (1 - a) * r' - δ))⌉₊ ≤
        ⌈exp (n₁ n * (r - δ / 2))⌉₊ * ⌈exp ((n - n₁ n : ℕ) * (r' - δ / 2))⌉₊ := by
    intro r r' hrr
    refine ceil_exp_le_mul ?_
    rw [hcast]
    exact time_sharing_bound (hn₁ n) (hn₁' n) hrr
  let c₀ := ((ca (n₁ n)).concat (cb (n - n₁ n))).castLen (Nat.add_sub_cancel' (hn₁n n))
  have hm₁ := hmsg R.1 R'.1 (by linarith)
  have hm₂ := hmsg R.2 R'.2 (by linarith)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  obtain ⟨c', hc'⟩ := c₀.exists_errProb_le_of_le hW (one_le_ceil_exp _) (one_le_ceil_exp _)
    hm₁ hm₂
  refine ⟨c', hc'.trans ?_⟩
  rw [BCCode.errProb_castLen]
  exact (ca (n₁ n)).errProb_concat_le hW _ (one_le_ceil_exp _) (one_le_ceil_exp _)
    (one_le_ceil_exp _) (one_le_ceil_exp _)

omit [Fintype α] in
lemma IsAchievableBC.mem_bcSlackSet (hW : IsChannel W) {R : ℝ × ℝ}
    (h : IsAchievableBC W R.1 R.2) : R ∈ bcSlackSet W :=
  fun _ _ => h.mono hW (by linarith) (by linarith)

omit [Fintype α] in
lemma bcSlackSet_subset_bcCapacityRegion : bcSlackSet W ⊆ bcCapacityRegion W := by
  intro R hR
  have hlim : Tendsto (fun k : ℕ => (R.1 - 1 / ((k : ℝ) + 1), R.2 - 1 / ((k : ℝ) + 1))) atTop
      (𝓝 R) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Tendsto (fun k : ℕ => R.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.1 - 0)) :=
      tendsto_const_nhds.sub h
    have h2 : Tendsto (fun k : ℕ => R.2 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.2 - 0)) :=
      tendsto_const_nhds.sub h
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k => hR _ (by positivity))

omit [Fintype α] in
/-- The capacity region is the closure of the rate pairs achievable up to an arbitrarily small
loss. -/
theorem bcCapacityRegion_eq_closure_bcSlackSet (hW : IsChannel W) :
    bcCapacityRegion W = closure (bcSlackSet W) :=
  le_antisymm (closure_mono fun _ hR => IsAchievableBC.mem_bcSlackSet hW hR)
    (closure_minimal bcSlackSet_subset_bcCapacityRegion isClosed_closure)

omit [Fintype α] in
/-- **Time sharing (Lecture 5 of [elgamal2010]).** The capacity region of the DM-BC, in nats, is
convex. -/
theorem convex_bcCapacityRegion [Nonempty α] (hW : IsChannel W) :
    Convex ℝ (bcCapacityRegion W) := by
  rw [bcCapacityRegion_eq_closure_bcSlackSet hW]
  exact (convex_bcSlackSet hW).closure

omit [Fintype α] in
/-- **Time sharing (Lecture 5 of [elgamal2010]).** The capacity region of the DM-BC is convex. -/
theorem convex_bcCapacityRegionBits [Nonempty α] (hW : IsChannel W) :
    Convex ℝ (bcCapacityRegionBits W) := by
  rw [bcCapacityRegionBits_eq_smul hW]
  exact (convex_bcCapacityRegion hW).smul _

/-! ### Single-user codes and broadcast codes -/

namespace BCCode

variable {M₁ M₂ n : ℕ} {W : α → β₁ × β₂ → ℝ} (c : BCCode M₁ M₂ n α β₁ β₂)

/-- The single-user code for `p(y₁ | x)` obtained by fixing the message `j` of receiver 2. -/
def userCode₁ (j : Fin M₂) : ChannelCode M₁ n α β₁ := ⟨fun i => c.enc (i, j), c.dec₁⟩

/-- The single-user code for `p(y₂ | x)` obtained by fixing the message `i` of receiver 1. -/
def userCode₂ (i : Fin M₁) : ChannelCode M₂ n α β₂ := ⟨fun j => c.enc (i, j), c.dec₂⟩

omit [Fintype α] in
/-- `P₁⁽ⁿ⁾` is the average over the messages `j` of receiver 2 of the probabilities of error of
the single-user codes `c.userCode₁ j`. -/
lemma errProb₁_eq_sum_avgErrProb :
    c.errProb₁ W = (∑ j, (c.userCode₁ j).avgErrProb (bcMarg₁ W)) / M₂ := by
  classical
  unfold errProb₁ ChannelCode.avgErrProb ChannelCode.condErrProb
  rw [Fintype.sum_prod_type, sum_comm, ← sum_div, div_div, mul_comm]
  rfl

omit [Fintype α] in
/-- `P₂⁽ⁿ⁾` is the average over the messages `i` of receiver 1 of the probabilities of error of
the single-user codes `c.userCode₂ i`. -/
lemma errProb₂_eq_sum_avgErrProb :
    c.errProb₂ W = (∑ i, (c.userCode₂ i).avgErrProb (bcMarg₂ W)) / M₁ := by
  classical
  unfold errProb₂ ChannelCode.avgErrProb ChannelCode.condErrProb
  rw [Fintype.sum_prod_type, ← sum_div, div_div, mul_comm (M₂ : ℝ)]
  rfl

omit [Fintype α] [Fintype β₁] [Fintype β₂] in
lemma channelCode_avgErrProb_le_one {γ : Type*} [Fintype γ] {V : α → γ → ℝ} (hV : IsChannel V)
    {M : ℕ} (hM : 0 < M) (c : ChannelCode M n α γ) : c.avgErrProb V ≤ 1 :=
  c.avgErrProb_le_maxErrProb.trans
    (ChannelCode.maxErrProb_le _ hM fun i => c.condErrProb_le_one hV i)

omit [Fintype α] in
lemma errProb₁_le_one (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) : c.errProb₁ W ≤ 1 := by
  rw [errProb₁_eq_sum_avgErrProb, div_le_one (by exact_mod_cast h₂)]
  calc ∑ j, (c.userCode₁ j).avgErrProb (bcMarg₁ W) ≤ ∑ _j : Fin M₂, (1 : ℝ) :=
        sum_le_sum fun j _ => channelCode_avgErrProb_le_one hW.bcMarg₁ h₁ _
    _ = M₂ := by simp

omit [Fintype α] in
lemma errProb₂_le_one (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) : c.errProb₂ W ≤ 1 := by
  rw [errProb₂_eq_sum_avgErrProb, div_le_one (by exact_mod_cast h₁)]
  calc ∑ i, (c.userCode₂ i).avgErrProb (bcMarg₂ W) ≤ ∑ _i : Fin M₁, (1 : ℝ) :=
        sum_le_sum fun i _ => channelCode_avgErrProb_le_one hW.bcMarg₂ h₂ _
    _ = M₁ := by simp

omit [Fintype α] in
/-- Some message of receiver 2 gives a single-user code for receiver 1 with probability of error
at most `P₁⁽ⁿ⁾`. -/
lemma exists_userCode₁_le (h₂ : 0 < M₂) :
    ∃ j, (c.userCode₁ j).avgErrProb (bcMarg₁ W) ≤ c.errProb₁ W := by
  obtain ⟨j, -, hj⟩ := exists_min_image univ (fun j => (c.userCode₁ j).avgErrProb (bcMarg₁ W))
    ⟨⟨0, h₂⟩, mem_univ _⟩
  refine ⟨j, ?_⟩
  rw [errProb₁_eq_sum_avgErrProb, le_div_iff₀ (by exact_mod_cast h₂)]
  calc (c.userCode₁ j).avgErrProb (bcMarg₁ W) * M₂
      = ∑ _j' : Fin M₂, (c.userCode₁ j).avgErrProb (bcMarg₁ W) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun j' _ => hj j' (mem_univ _)

omit [Fintype α] in
/-- Some message of receiver 1 gives a single-user code for receiver 2 with probability of error
at most `P₂⁽ⁿ⁾`. -/
lemma exists_userCode₂_le (h₁ : 0 < M₁) :
    ∃ i, (c.userCode₂ i).avgErrProb (bcMarg₂ W) ≤ c.errProb₂ W := by
  obtain ⟨i, -, hi⟩ := exists_min_image univ (fun i => (c.userCode₂ i).avgErrProb (bcMarg₂ W))
    ⟨⟨0, h₁⟩, mem_univ _⟩
  refine ⟨i, ?_⟩
  rw [errProb₂_eq_sum_avgErrProb, le_div_iff₀ (by exact_mod_cast h₁)]
  calc (c.userCode₂ i).avgErrProb (bcMarg₂ W) * M₁
      = ∑ _i' : Fin M₁, (c.userCode₂ i).avgErrProb (bcMarg₂ W) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun i' _ => hi i' (mem_univ _)

omit [Fintype α] in
/-- If the codeword of `(w₁, w₂)` is seen by receiver 1 as the codeword `xⁿ(w₁)` of a single-user
code `c₁` with the same decoder, then `P₁⁽ⁿ⁾` is the probability of error of `c₁`. -/
lemma errProb₁_eq_avgErrProb (c₁ : ChannelCode M₁ n α β₁) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (hdec : c.dec₁ = c₁.dec)
    (henc : ∀ w, channelExt (bcMarg₁ W) n (c.enc w) = channelExt (bcMarg₁ W) n (c₁.enc w.1)) :
    c.errProb₁ W = c₁.avgErrProb (bcMarg₁ W) := by
  classical
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  unfold errProb₁ ChannelCode.avgErrProb ChannelCode.condErrProb
  simp only [henc, hdec]
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
  field_simp

omit [Fintype α] in
/-- If the codeword of `(w₁, w₂)` is seen by receiver 2 as the codeword `xⁿ(w₂)` of a single-user
code `c₂` with the same decoder, then `P₂⁽ⁿ⁾` is the probability of error of `c₂`. -/
lemma errProb₂_eq_avgErrProb (c₂ : ChannelCode M₂ n α β₂) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (hdec : c.dec₂ = c₂.dec)
    (henc : ∀ w, channelExt (bcMarg₂ W) n (c.enc w) = channelExt (bcMarg₂ W) n (c₂.enc w.2)) :
    c.errProb₂ W = c₂.avgErrProb (bcMarg₂ W) := by
  classical
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  unfold errProb₂ ChannelCode.avgErrProb ChannelCode.condErrProb
  simp only [henc, hdec]
  rw [Fintype.sum_prod_type, sum_comm]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
  field_simp

omit [Fintype α] in
/-- With a single message for receiver 2, receiver 2 never errs. -/
lemma errProb₂_eq_zero (hM₂ : M₂ = 1) : c.errProb₂ W = 0 := by
  subst hM₂
  simp [errProb₂, Fin.fin_one_eq_zero]

omit [Fintype α] in
/-- With a single message for receiver 1, receiver 1 never errs. -/
lemma errProb₁_eq_zero (hM₁ : M₁ = 1) : c.errProb₁ W = 0 := by
  subst hM₁
  simp [errProb₁, Fin.fin_one_eq_zero]

/-- A code for the channel `p(y₁ | x)` as a broadcast code with a single message for
receiver 2. -/
def ofReceiver₁Code {M : ℕ} (c₁ : ChannelCode M n α β₁) (hM₂ : M₂ = 1) :
    BCCode M M₂ n α β₁ β₂ :=
  ⟨fun w => c₁.enc w.1, c₁.dec, fun _ => ⟨0, by omega⟩⟩

/-- A code for the channel `p(y₂ | x)` as a broadcast code with a single message for
receiver 1. -/
def ofReceiver₂Code {M : ℕ} (c₂ : ChannelCode M n α β₂) (hM₁ : M₁ = 1) :
    BCCode M₁ M n α β₁ β₂ :=
  ⟨fun w => c₂.enc w.2, fun _ => ⟨0, by omega⟩, c₂.dec⟩

end BCCode

end InfoTheory
