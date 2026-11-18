/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.MutualInformation.Convexity
public import InfoTheoryLib.Network.MACBits

/-!
# Simple inner and outer bounds on the capacity region of the multiple access channel

The individual capacities `C₁ = max_{x₂, p(x₁)} I(X₁; Y | X₂ = x₂)` and
`C₂ = max_{x₁, p(x₂)} I(X₂; Y | X₁ = x₁)`, and the sum-rate bound
`C₁₂ = max_{p(x₁) p(x₂)} I(X₁, X₂; Y)`, give a time-division inner bound and an outer bound on the
capacity region of any DM-MAC. The sum-rate bound is the sum capacity.

## Main definitions

* `macC₁ W`, `macC₂ W`, `macC₁₂ W`: `C₁`, `C₂` and `C₁₂`, in nats.
* `macTimeDivisionBits W`, `macOuterBoundBits W`: the time-division inner bound and the outer
  bound, in bits.

## Main statements

* `macInfo₁_eq_sum`, `macInfo₂_eq_sum`: `I(X₁; Y | X₂) = ∑_{x₂} p(x₂) I(X₁; Y | X₂ = x₂)`.
* `macTimeDivisionBits_subset`: the time-division inner bound.
* `macCapacityRegionBits_subset_macOuterBoundBits`: the outer bound.
* `sSup_sum_macCapacityRegionBits`: the sum capacity `max {R₁ + R₂ : (R₁, R₂) ∈ 𝒞}` is `C₁₂`.
* `mem_macCapacityRegionBits_of_le`: lowering the rates stays in the capacity region.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 4
-/

open Real Finset Filter Topology Set

open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}
  {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ}

/-! ### Conditional mutual information as an average -/

/-- The law of `(X₂, Y)`: given `X₂ = b`, the output is `outDist p₁ (W (·, b))`. -/
lemma dist_macJoint_snd_out (hp₁ : IsPMF p₁) (hW : IsChannel W) (b : α₂) (y : β) :
    dist (macJoint p₁ p₂ W) (pair (fun z : (α₁ × α₂) × β => z.1.2) Prod.snd) (b, y) =
      dist (macJoint p₁ p₂ W) (fun z => z.1.2) b * outDist p₁ (fun a => W (a, b)) y := by
  classical
  rw [dist_macJoint_snd hp₁ hW]
  simp only [dist, pair, macJoint, jointOf, prodDist, outDist, Prod.mk.injEq,
    Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single b (fun b' _ hb' => by simp [hb']) (by simp)]
  rw [sum_eq_single y (fun y' _ hy' => by simp [hy']) (by simp)]
  simp only [and_self, ite_true]
  ring

/-- The law of `(X₁, Y)`: given `X₁ = a`, the output is `outDist p₂ (W (a, ·))`. -/
lemma dist_macJoint_fst_out (hp₂ : IsPMF p₂) (hW : IsChannel W) (a : α₁) (y : β) :
    dist (macJoint p₁ p₂ W) (pair (fun z : (α₁ × α₂) × β => z.1.1) Prod.snd) (a, y) =
      dist (macJoint p₁ p₂ W) (fun z => z.1.1) a * outDist p₂ (fun b => W (a, b)) y := by
  classical
  rw [dist_macJoint_fst hp₂ hW]
  simp only [dist, pair, macJoint, jointOf, prodDist, outDist, Prod.mk.injEq,
    Fintype.sum_prod_type, mul_sum]
  rw [sum_eq_single a (fun a' _ ha' => by simp [ha']) (by simp)]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_eq_single y (fun y' _ hy' => by simp [hy']) (by simp)]
  simp only [and_self, ite_true]
  ring

/-- `H(Y | X₁, X₂) = ∑_{x₁, x₂} p(x₁) p(x₂) H(Y | X₁ = x₁, X₂ = x₂)`. -/
lemma condEntropy_macJoint_inputs (hW : IsChannel W) :
    H[Prod.snd | Prod.fst ; macJoint p₁ p₂ W] = ∑ a, ∑ b, p₁ a * p₂ b * entropy (W (a, b)) := by
  have h : ∀ x y, dist (macJoint p₁ p₂ W) (pair Prod.fst Prod.snd) (x, y) =
      dist (macJoint p₁ p₂ W) Prod.fst x * W x y := fun x y => by
    rw [dist_pair_fst_snd, dist_macJoint_inputs hW]
    rfl
  rw [condEntropy_of_channel id h, Function.id_comp, dist_macJoint_inputs hW,
    Fintype.sum_prod_type]
  rfl

/-- `I(X₁; Y | X₂) = ∑_{x₂} p(x₂) I(X₁; Y | X₂ = x₂)`: given `X₂ = x₂`, the input `X₁ ∼ p₁` is
sent over the channel `p(y | x₁, x₂)`. -/
theorem macInfo₁_eq_sum (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁ p₁ p₂ W = ∑ b, p₂ b * mutualInfoOf p₁ (fun a => W (a, b)) := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  have hY₂ := condEntropy_of_channel (W := fun b => outDist p₁ (fun a => W (a, b))) id
    (dist_macJoint_snd_out (p₂ := p₂) hp₁ hW)
  rw [macInfo₁, condMutualInfo_comm hμ, condMutualInfo]
  change H[Prod.snd | fun z : (α₁ × α₂) × β => z.1.2 ; macJoint p₁ p₂ W] -
    H[Prod.snd | Prod.fst ; macJoint p₁ p₂ W] = _
  rw [hY₂, condEntropy_macJoint_inputs hW, Function.id_comp, dist_macJoint_snd hp₁ hW, sum_comm,
    ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [mutualInfoOf_eq hp₁ fun a => hW (a, b), mul_sub, mul_sum]
  congr 1
  exact sum_congr rfl fun a _ => by ring

/-- `I(X₂; Y | X₁) = ∑_{x₁} p(x₁) I(X₂; Y | X₁ = x₁)`. -/
theorem macInfo₂_eq_sum (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₂ p₁ p₂ W = ∑ a, p₁ a * mutualInfoOf p₂ (fun b => W (a, b)) := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  have hY₁ := condEntropy_of_channel (W := fun a => outDist p₂ (fun b => W (a, b))) id
    (dist_macJoint_fst_out (p₁ := p₁) hp₂ hW)
  have e : H[Prod.snd | pair (fun z : (α₁ × α₂) × β => z.1.2) (fun z => z.1.1) ;
      macJoint p₁ p₂ W] = H[Prod.snd | Prod.fst ; macJoint p₁ p₂ W] :=
    condEntropy_congr_right hμ Prod.snd Prod.swap Prod.swap_injective fun _ => rfl
  rw [macInfo₂, condMutualInfo_comm hμ, condMutualInfo, e, hY₁, condEntropy_macJoint_inputs hW,
    Function.id_comp, dist_macJoint_fst hp₂ hW, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [mutualInfoOf_eq hp₂ fun b => hW (a, b), mul_sub, mul_sum]
  congr 1
  exact sum_congr rfl fun b _ => by ring

/-! ### The individual capacities and the sum-rate bound -/

/-- **Lecture 4 of [elgamal2010].** `C₁ = max_{x₂, p(x₁)} I(X₁; Y | X₂ = x₂)`, the largest
capacity of the channels `p(y | x₁, x₂)` from `X₁` with `x₂` fixed. -/
def macC₁ (W : α₁ × α₂ → β → ℝ) : ℝ := ⨆ b, capacity fun a => W (a, b)

/-- **Lecture 4 of [elgamal2010].** `C₂ = max_{x₁, p(x₂)} I(X₂; Y | X₁ = x₁)`. -/
def macC₂ (W : α₁ × α₂ → β → ℝ) : ℝ := ⨆ a, capacity fun b => W (a, b)

/-- **Lecture 4 of [elgamal2010].** `C₁₂ = max_{p(x₁) p(x₂)} I(X₁, X₂; Y)`. -/
def macC₁₂ (W : α₁ × α₂ → β → ℝ) : ℝ :=
  sSup {c | ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ macInfo₁₂ p₁ p₂ W = c}

lemma bddAbove_macC₁₂ (hW : IsChannel W) :
    BddAbove {c | ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ macInfo₁₂ p₁ p₂ W = c} :=
  ⟨log (Fintype.card β), fun _ ⟨_, _, hp₁, hp₂, hc⟩ => hc ▸ macInfo₁₂_le_log_card hp₁ hp₂ hW⟩

/-- `I(X₁; Y | X₂) ≤ C₁`. -/
lemma macInfo₁_le_macC₁ (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁ p₁ p₂ W ≤ macC₁ W := by
  rw [macInfo₁_eq_sum hp₁ hp₂ hW]
  calc ∑ b, p₂ b * mutualInfoOf p₁ (fun a => W (a, b)) ≤ ∑ b, p₂ b * macC₁ W :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
          ((mutualInfoOf_le_capacity hp₁ fun a => hW (a, b)).trans
            (le_ciSup (f := fun b => capacity fun a => W (a, b)) (Set.finite_range _).bddAbove
              b)) (hp₂.nonneg b)
    _ = macC₁ W := by rw [← sum_mul, hp₂.sum_eq_one, one_mul]

/-- `I(X₂; Y | X₁) ≤ C₂`. -/
lemma macInfo₂_le_macC₂ (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₂ p₁ p₂ W ≤ macC₂ W := by
  rw [macInfo₂_eq_sum hp₁ hp₂ hW]
  calc ∑ a, p₁ a * mutualInfoOf p₂ (fun b => W (a, b)) ≤ ∑ a, p₁ a * macC₂ W :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          ((mutualInfoOf_le_capacity hp₂ fun b => hW (a, b)).trans
            (le_ciSup (f := fun a => capacity fun b => W (a, b)) (Set.finite_range _).bddAbove
              a)) (hp₁.nonneg a)
    _ = macC₂ W := by rw [← sum_mul, hp₁.sum_eq_one, one_mul]

/-- `I(X₁, X₂; Y) ≤ C₁₂`. -/
lemma macInfo₁₂_le_macC₁₂ (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁₂ p₁ p₂ W ≤ macC₁₂ W :=
  le_csSup (bddAbove_macC₁₂ hW) ⟨p₁, p₂, hp₁, hp₂, rfl⟩

/-! ### The bounds -/

/-- The pentagons are in the capacity region. -/
lemma macPentagonsBits_subset [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macPentagonsBits W ⊆ macCapacityRegionBits W := by
  rw [macCapacityRegionBits_eq hW]
  exact (subset_convexHull ℝ _).trans subset_closure

omit [Fintype α₁] [Fintype α₂] in
/-- **Lecture 4 of [elgamal2010].** Lowering the rates of a pair in the capacity region stays in
the capacity region. -/
theorem mem_macCapacityRegionBits_of_le [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W)
    {R R' : ℝ × ℝ} (hR : R ∈ macCapacityRegionBits W) (h₁ : R'.1 ≤ R.1) (h₂ : R'.2 ≤ R.2) :
    R' ∈ macCapacityRegionBits W := by
  have hl := log_pos one_lt_two
  rw [macCapacityRegionBits_eq_smul hW] at hR ⊢
  obtain ⟨S, hS, rfl⟩ := hR
  refine ⟨log 2 • R', mem_macCapacityRegion_of_le hW hS ?_ ?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul] at h₁ ⊢
    rw [inv_mul_eq_div, le_div_iff₀ hl] at h₁
    linarith
  · simp only [smul_eq_mul, Prod.smul_snd] at h₂ ⊢
    rw [inv_mul_eq_div, le_div_iff₀ hl] at h₂
    linarith
  · change (log 2)⁻¹ • log 2 • R' = R'
    rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]

/-- **Lecture 4 of [elgamal2010].** The time-division inner bound: the rate pairs below
`(t C₁, (1 - t) C₂)` for some `t ∈ [0, 1]`, in bits. -/
def macTimeDivisionBits (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ t ∈ Icc (0 : ℝ) 1, R.1 ≤ t * (macC₁ W / log 2) ∧ R.2 ≤ (1 - t) * (macC₂ W / log 2)}

/-- **Lecture 4 of [elgamal2010].** The outer bound `R₁ ≤ C₁`, `R₂ ≤ C₂`, `R₁ + R₂ ≤ C₁₂`, in
bits. -/
def macOuterBoundBits (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | R.1 ≤ macC₁ W / log 2 ∧ R.2 ≤ macC₂ W / log 2 ∧ R.1 + R.2 ≤ macC₁₂ W / log 2}

omit [Fintype α₂] in
/-- `(C₁, 0)` is in the capacity region: sender 2 sends a fixed symbol and sender 1 codes for the
resulting single-user channel. -/
lemma macC₁_mem_macCapacityRegionBits [Finite α₂] [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    (macC₁ W / log 2, 0) ∈ macCapacityRegionBits W := by
  have := Fintype.ofFinite α₂
  have hl := log_pos one_lt_two
  obtain ⟨b, hb⟩ := exists_eq_ciSup_of_finite (f := fun b => capacity fun a => W (a, b))
  have hmem : (macC₁ W, 0) ∈ macCapacityRegion W := by
    have hlim : Tendsto (fun k : ℕ => (macC₁ W - 1 / ((k : ℝ) + 1), (0 : ℝ))) atTop
        (𝓝 (macC₁ W, 0)) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub (macC₁ W)
      rw [sub_zero] at h
      exact h.prodMk_nhds tendsto_const_nhds
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    refine isAchievableMAC_of_isAchievableRate hW b
      (isAchievableRate_of_lt_capacity (fun a => hW (a, b)) ?_)
    rw [hb]
    exact sub_lt_self _ (by positivity)
  rw [macCapacityRegionBits_eq_smul hW]
  exact ⟨_, hmem, by ext <;> simp [div_eq_inv_mul]⟩

omit [Fintype α₁] in
/-- `(0, C₂)` is in the capacity region. -/
lemma macC₂_mem_macCapacityRegionBits [Finite α₁] [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    (0, macC₂ W / log 2) ∈ macCapacityRegionBits W := by
  have := Fintype.ofFinite α₁
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := fun a => capacity fun b => W (a, b))
  have hmem : (0, macC₂ W) ∈ macCapacityRegion W := by
    have hlim : Tendsto (fun k : ℕ => ((0 : ℝ), macC₂ W - 1 / ((k : ℝ) + 1))) atTop
        (𝓝 (0, macC₂ W)) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub (macC₂ W)
      rw [sub_zero] at h
      exact tendsto_const_nhds.prodMk_nhds h
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    refine isAchievableMAC_of_isAchievableRate₂ hW a
      (isAchievableRate_of_lt_capacity (fun b => hW (a, b)) ?_)
    rw [ha]
    exact sub_lt_self _ (by positivity)
  rw [macCapacityRegionBits_eq_smul hW]
  exact ⟨_, hmem, by ext <;> simp [div_eq_inv_mul]⟩

/-- **Lecture 4 of [elgamal2010].** The time-division inner bound is in the capacity region. -/
theorem macTimeDivisionBits_subset [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macTimeDivisionBits W ⊆ macCapacityRegionBits W := by
  rintro R ⟨t, ⟨ht0, ht1⟩, h₁, h₂⟩
  have hmix := convex_macCapacityRegionBits hW (macC₁_mem_macCapacityRegionBits hW)
    (macC₂_mem_macCapacityRegionBits hW) ht0 (by linarith : 0 ≤ 1 - t) (by ring)
  refine mem_macCapacityRegionBits_of_le hW hmix ?_ ?_ <;> simpa using by assumption

/-- **Lecture 4 of [elgamal2010].** The outer bound: every rate pair in the capacity region has
`R₁ ≤ C₁`, `R₂ ≤ C₂` and `R₁ + R₂ ≤ C₁₂`. -/
theorem macCapacityRegionBits_subset_macOuterBoundBits [Nonempty α₁] [Nonempty α₂]
    (hW : IsChannel W) : macCapacityRegionBits W ⊆ macOuterBoundBits W := by
  have hl := log_pos one_lt_two
  rw [macCapacityRegionBits_eq hW]
  have hc : IsClosed (macOuterBoundBits W) :=
    (isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_snd continuous_const).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hconv : Convex ℝ (macOuterBoundBits W) := by
    rintro x ⟨hx₁, hx₂, hx₃⟩ y ⟨hy₁, hy₂, hy₃⟩ a b ha hb hab
    simp only [macOuterBoundBits, Set.mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
      Prod.snd_add, Prod.smul_snd]
    have key : ∀ {u v c : ℝ}, u ≤ c → v ≤ c → a * u + b * v ≤ c := fun {u v c} hu hv => by
      have e : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
      have h1 := mul_le_mul_of_nonneg_left hu ha
      have h2 := mul_le_mul_of_nonneg_left hv hb
      linarith
    refine ⟨key hx₁ hy₁, key hx₂ hy₂, ?_⟩
    have := key hx₃ hy₃
    linarith
  refine closure_minimal (convexHull_min ?_ hconv) hc
  rintro R ⟨p₁, p₂, hp₁, hp₂, h₁, h₂, h₃⟩
  exact ⟨h₁.trans (div_le_div_of_nonneg_right (macInfo₁_le_macC₁ hp₁ hp₂ hW) hl.le),
    h₂.trans (div_le_div_of_nonneg_right (macInfo₂_le_macC₂ hp₁ hp₂ hW) hl.le),
    h₃.trans (div_le_div_of_nonneg_right (macInfo₁₂_le_macC₁₂ hp₁ hp₂ hW) hl.le)⟩

/-- **Lecture 4 of [elgamal2010].** The sum capacity: the largest sum rate `R₁ + R₂` over the
capacity region is `C₁₂ = max_{p(x₁) p(x₂)} I(X₁, X₂; Y)`, attained at the corner point
`(I(X₁; Y | X₂), I(X₂; Y))` of the pentagons. -/
theorem sSup_sum_macCapacityRegionBits [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    sSup ((fun R : ℝ × ℝ => R.1 + R.2) '' macCapacityRegionBits W) = macC₁₂ W / log 2 := by
  have hl := log_pos one_lt_two
  have hne : {c | ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ macInfo₁₂ p₁ p₂ W = c}.Nonempty :=
    ⟨_, uniformPMF α₁, uniformPMF α₂, uniformPMF_isPMF, uniformPMF_isPMF, rfl⟩
  -- The corner point of a pentagon has sum rate `I(X₁, X₂; Y)`.
  have hcorner : ∀ p₁ p₂, IsPMF p₁ → IsPMF p₂ →
      macInfo₁₂ p₁ p₂ W / log 2 ∈ (fun R : ℝ × ℝ => R.1 + R.2) '' macCapacityRegionBits W := by
    intro p₁ p₂ hp₁ hp₂
    refine ⟨(macInfo₁ p₁ p₂ W / log 2, (macInfo₁₂ p₁ p₂ W - macInfo₁ p₁ p₂ W) / log 2),
      macPentagonsBits_subset hW ⟨p₁, p₂, hp₁, hp₂, le_rfl, ?_, ?_⟩, ?_⟩
    · exact div_le_div_of_nonneg_right (by linarith [macInfo₁₂_le_add hp₁ hp₂ hW]) hl.le
    · dsimp only
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hl.le
    · dsimp only
      rw [← add_div]
      ring_nf
  obtain ⟨_, ⟨p₁, p₂, hp₁, hp₂, rfl⟩⟩ := hne
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨_, hcorner p₁ p₂ hp₁ hp₂⟩ ?_ ?_
  · rintro _ ⟨R, hR, rfl⟩
    exact (macCapacityRegionBits_subset_macOuterBoundBits hW hR).2.2
  · intro w hw
    have hne' : {c | ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ macInfo₁₂ p₁ p₂ W = c}.Nonempty :=
      ⟨_, p₁, p₂, hp₁, hp₂, rfl⟩
    obtain ⟨_, ⟨q₁, q₂, hq₁, hq₂, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne'
      ((lt_div_iff₀ hl).1 hw : w * log 2 < macC₁₂ W)
    exact ⟨_, hcorner q₁ q₂ hq₁ hq₂, (lt_div_iff₀ hl).2 hlt⟩

end InfoTheory
