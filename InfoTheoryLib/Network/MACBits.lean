/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.AverageError
public import InfoTheoryLib.Network.MACCapacity

/-!
# The capacity region of the multiple access channel in bits

In their lecture notes, El Gamal and Kim measure rates in bits, with `(2^{nR₁}, 2^{nR₂}, n)` codes
whose message sets are `[1 : 2^{nRⱼ}] = {1, …, 2^⌈nRⱼ⌉}`, and define the capacity region of the
DM-MAC as the closure of the set of achievable rate pairs, with the average probability of error.
Cover and Thomas use rates in nats and `⌈e^{nRⱼ}⌉` messages. We show that the two capacity regions
agree up to the factor `log 2`, and restate Theorem 2 of Lecture 4 with the notes' closed
pentagons `R(X₁, X₂)`.

## Main definitions

* `IsAchievableMACBits W R₁ R₂`, `macCapacityRegionBits W`: achievable rate pairs in bits and the
  capacity region.
* `macPentagonBits W p₁ p₂`: the pentagon `R(X₁, X₂)` of the notes, in bits.
* `macPentagonsBits W`: the union of the pentagons over all product input distributions.

## Main statements

* `macCapacityRegionBits_eq_smul`: the capacity region in bits is the one in nats scaled by
  `1 / log 2`.
* `macCapacityRegionBits_eq`: **Theorem 2 of [elgamal2010], Lecture 4 (Ahlswede, Liao)**, the
  capacity region is the convex closure of the union of the pentagons `R(X₁, X₂)`.
* `convex_macCapacityRegionBits`: the capacity region is convex (time sharing).

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 4
-/

open Real Finset Filter Topology Set

open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}

/-! ### Achievable rates in bits -/

/-- **Definition (Lecture 4 of [elgamal2010]).** A rate pair `(R₁, R₂)`, in bits per
transmission, is achievable if there are `(2^{nR₁}, 2^{nR₂}, n)` codes, with message sets
`[1 : 2^{nRⱼ}] = {1, …, 2^⌈nRⱼ⌉}`, whose average probability of error tends to `0`. -/
def IsAchievableMACBits (W : α₁ × α₂ → β → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, MACCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α₁ α₂ β,
    Tendsto (fun n => (c n).avgErrProb W) atTop (𝓝 0)

/-- **Definition (Lecture 4 of [elgamal2010]).** The capacity region of the DM-MAC, in bits: the
closure of the set of achievable rate pairs. -/
def macCapacityRegionBits (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableMACBits W R.1 R.2}

omit [Fintype α₁] [Fintype α₂] in
/-- A rate pair achievable in bits is achievable in nats, after multiplying by `log 2`: a
`(2^{nR₁}, 2^{nR₂}, n)` code has at least `⌈e^{nR₁ log 2}⌉` and `⌈e^{nR₂ log 2}⌉` messages. -/
theorem IsAchievableMACBits.isAchievableMAC (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h : IsAchievableMACBits W R₁ R₂) : IsAchievableMAC W (R₁ * log 2) (R₂ * log 2) := by
  obtain ⟨c, hc⟩ := h
  have hsub : ∀ n : ℕ, ∃ c' : MACCode ⌈exp (n * (R₁ * log 2))⌉₊ ⌈exp (n * (R₂ * log 2))⌉₊ n
      α₁ α₂ β, c'.avgErrProb W ≤ (c n).avgErrProb W := fun n =>
    (c n).exists_avgErrProb_le_of_le hW (one_le_ceil_exp _) (one_le_ceil_exp _)
      (ceil_exp_le_two_pow n R₁) (ceil_exp_le_two_pow n R₂)
  choose c' hc' using hsub
  exact ⟨c', tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => (c' n).avgErrProb_nonneg hW) hc'⟩

/-- `2^⌈nx⌉ ≤ e^{nR}` for `x = R / log 2 - δ` and `nδ ≥ 1`. -/
lemma two_pow_ceil_le_ceil_exp {R δ : ℝ} {n : ℕ} (hn : 1 ≤ n * δ) :
    2 ^ ⌈n * (R / log 2 - δ)⌉₊ ≤ ⌈exp (n * R)⌉₊ := by
  have hl := log_pos one_lt_two
  rcases le_or_gt (n * (R / log 2 - δ)) 0 with h0 | h0
  · rw [Nat.ceil_eq_zero.2 h0, pow_zero]
    exact one_le_ceil_exp _
  · have hreal : ((2 ^ ⌈n * (R / log 2 - δ)⌉₊ : ℕ) : ℝ) ≤ exp (n * R) := by
      push_cast
      calc (2 : ℝ) ^ ⌈n * (R / log 2 - δ)⌉₊ = 2 ^ (⌈n * (R / log 2 - δ)⌉₊ : ℝ) :=
            (rpow_natCast 2 _).symm
        _ ≤ 2 ^ (n * (R / log 2 - δ) + 1) :=
            rpow_le_rpow_of_exponent_le one_le_two (Nat.ceil_lt_add_one h0.le).le
        _ = exp (n * R - (n * δ - 1) * log 2) := by
            rw [rpow_def_of_pos two_pos]
            congr 1
            field_simp
            ring
        _ ≤ exp (n * R) := exp_le_exp.2 (by nlinarith)
    exact_mod_cast hreal.trans (Nat.le_ceil _)

omit [Fintype α₁] [Fintype α₂] in
/-- A rate pair achievable in nats is achievable in bits, after dividing by `log 2`, up to an
arbitrarily small loss. -/
theorem IsAchievableMAC.isAchievableMACBits [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W)
    {R₁ R₂ : ℝ} (h : IsAchievableMAC W R₁ R₂) {δ : ℝ} (hδ : 0 < δ) :
    IsAchievableMACBits W (R₁ / log 2 - δ) (R₂ / log 2 - δ) := by
  obtain ⟨c, hc⟩ := h
  have hz : ∀ n : ℕ, NeZero (2 ^ ⌈n * (R₁ / log 2 - δ)⌉₊) ∧
      NeZero (2 ^ ⌈n * (R₂ / log 2 - δ)⌉₊) := fun n => ⟨⟨by positivity⟩, ⟨by positivity⟩⟩
  have hsub : ∀ n : ℕ, ∃ c' : MACCode (2 ^ ⌈n * (R₁ / log 2 - δ)⌉₊)
      (2 ^ ⌈n * (R₂ / log 2 - δ)⌉₊) n α₁ α₂ β,
      1 ≤ n * δ → c'.avgErrProb W ≤ (c n).avgErrProb W := fun n => by
    by_cases hn : 1 ≤ n * δ
    · obtain ⟨c', hc'⟩ := (c n).exists_avgErrProb_le_of_le hW (by positivity) (by positivity)
        (two_pow_ceil_le_ceil_exp hn) (two_pow_ceil_le_ceil_exp hn)
      exact ⟨c', fun _ => hc'⟩
    · have := (hz n).1
      have := (hz n).2
      exact ⟨MACCode.const _ _ n, fun h' => absurd h' hn⟩
  choose c' hc' using hsub
  refine ⟨c', tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Eventually.of_forall fun n => (c' n).avgErrProb_nonneg hW) ?_⟩
  filter_upwards [eventually_ge_atTop ⌈1 / δ⌉₊] with n hn
  refine hc' n ?_
  have := (div_le_iff₀ hδ).1 (Nat.ceil_le.1 hn)
  linarith

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 4 of [elgamal2010].** The capacity region in bits is the capacity region in nats
scaled by `1 / log 2`. -/
theorem macCapacityRegionBits_eq_smul [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macCapacityRegionBits W = (log 2)⁻¹ • macCapacityRegion W := by
  have hl := log_pos one_lt_two
  set A := {R : ℝ × ℝ | IsAchievableMACBits W R.1 R.2}
  set B := {R : ℝ × ℝ | IsAchievableMAC W R.1 R.2}
  have h1 : A ⊆ (log 2)⁻¹ • B := fun R hR =>
    ⟨R * (log 2, log 2), hR.isAchievableMAC hW, by
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
      IsAchievableMAC.isAchievableMACBits hW hR (by positivity))
  refine le_antisymm ?_ ?_
  · calc macCapacityRegionBits W ⊆ closure ((log 2)⁻¹ • B) := closure_mono h1
      _ = (log 2)⁻¹ • macCapacityRegion W := closure_smul₀ _ _
  · calc (log 2)⁻¹ • macCapacityRegion W = closure ((log 2)⁻¹ • B) := (closure_smul₀ _ _).symm
      _ ⊆ closure (closure A) := closure_mono h2
      _ = macCapacityRegionBits W := closure_closure

/-! ### Theorem 2 -/

/-- **Lecture 4 of [elgamal2010].** The pentagon `R(X₁, X₂)`, in bits: the rate pairs with
`R₁ ≤ I(X₁; Y | X₂)`, `R₂ ≤ I(X₂; Y | X₁)` and `R₁ + R₂ ≤ I(X₁, X₂; Y)` for the product input
distribution `p₁(x₁) p₂(x₂)`. -/
def macPentagonBits (W : α₁ × α₂ → β → ℝ) (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | R.1 ≤ macInfo₁ p₁ p₂ W / log 2 ∧ R.2 ≤ macInfo₂ p₁ p₂ W / log 2 ∧
    R.1 + R.2 ≤ macInfo₁₂ p₁ p₂ W / log 2}

/-- The union of the pentagons `R(X₁, X₂)` over all product input distributions. -/
def macPentagonsBits (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ R ∈ macPentagonBits W p₁ p₂}

omit [Fintype β] in
/-- If `S ⊆ T ⊆ closure S`, then `S` and `T` have the same convex closure. -/
lemma closure_convexHull_eq_of_subset {S T : Set (ℝ × ℝ)} (h₁ : S ⊆ T) (h₂ : T ⊆ closure S) :
    closure (convexHull ℝ S) = closure (convexHull ℝ T) := by
  refine le_antisymm (closure_mono (convexHull_mono h₁)) ?_
  refine closure_minimal (convexHull_min (h₂.trans (closure_mono (subset_convexHull ℝ S)))
    (convex_convexHull ℝ S).closure) isClosed_closure

/-- **Theorem 2 of [elgamal2010], Lecture 4 (Ahlswede, Liao).** The capacity region of the DM-MAC
is the convex closure of the union of the pentagons `R(X₁, X₂)` over all product input
distributions `p(x₁) p(x₂)`. -/
theorem macCapacityRegionBits_eq [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macCapacityRegionBits W = closure (convexHull ℝ (macPentagonsBits W)) := by
  have hl := log_pos one_lt_two
  rw [macCapacityRegionBits_eq_smul hW, macCapacityRegion_eq hW, ← closure_smul₀,
    ← convexHull_smul]
  refine closure_convexHull_eq_of_subset ?_ ?_
  · rintro _ ⟨R, ⟨p₁, p₂, hp₁, hp₂, h1, h2, h3⟩, rfl⟩
    refine ⟨p₁, p₂, hp₁, hp₂, ?_, ?_, ?_⟩ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← div_eq_inv_mul] <;>
      [exact div_le_div_of_nonneg_right h1.le hl.le;
       exact div_le_div_of_nonneg_right h2.le hl.le;
       (rw [← add_div]; exact div_le_div_of_nonneg_right h3.le hl.le)]
  · rintro R ⟨p₁, p₂, hp₁, hp₂, h1, h2, h3⟩
    -- `R - (t, t)` is in the open pentagon for every `t > 0`.
    have hlim : Tendsto (fun k : ℕ => (log 2)⁻¹ • ((R.1 - 1 / ((k : ℝ) + 1)) * log 2,
        (R.2 - 1 / ((k : ℝ) + 1)) * log 2)) atTop (𝓝 R) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h1 : Tendsto (fun k : ℕ => R.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.1 - 0)) :=
        tendsto_const_nhds.sub h
      have h2 : Tendsto (fun k : ℕ => R.2 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.2 - 0)) :=
        tendsto_const_nhds.sub h
      rw [sub_zero] at h1 h2
      convert h1.prodMk_nhds h2 using 2
      ext <;> simp [field]
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    have ht : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine ⟨_, ⟨p₁, p₂, hp₁, hp₂, ?_, ?_, ?_⟩, rfl⟩ <;> dsimp only
    · have := (le_div_iff₀ hl).1 h1
      nlinarith
    · have := (le_div_iff₀ hl).1 h2
      nlinarith
    · have := (le_div_iff₀ hl).1 h3
      nlinarith

omit [Fintype α₁] [Fintype α₂] in
/-- **Time sharing (Lecture 4 of [elgamal2010]).** The capacity region of the DM-MAC is
convex. -/
theorem convex_macCapacityRegionBits [Finite α₁] [Finite α₂] [Nonempty α₁] [Nonempty α₂]
    (hW : IsChannel W) : Convex ℝ (macCapacityRegionBits W) := by
  have := Fintype.ofFinite α₁
  have := Fintype.ofFinite α₂
  rw [macCapacityRegionBits_eq_smul hW]
  exact (convex_macCapacityRegion hW).smul _

end InfoTheory
