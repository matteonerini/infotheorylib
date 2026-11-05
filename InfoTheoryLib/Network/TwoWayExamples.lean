/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayModSum
public import InfoTheoryLib.Network.TwoWayInner

/-!
# Examples of two-way channels

## Main definitions

* `decoupledTW`: the two-way channel `p(y₁ | x₂) p(y₂ | x₁)`.
* `commonTW`: the two-way channel with a common output.
* `bmcV`: the binary multiplier channel `Y = X₁ · X₂`.

## Main statements

* `isAchievableTWC_of_lt_prod`: Shannon's inner bound for product inputs, without time sharing.
* `twcCapacityRegion_decoupled`: **Shannon's inner bound is tight for a decoupled channel**.
* `isAchievableTWC_bmc`: the inner bound for the binary multiplier channel.
* `mem_twcOuterRegion_bmc_iff`: the outer bound for the binary multiplier channel.
* `isAchievableTWC_bmc_symm`, `three_fifths_mem_twcCapacityRegion_bmc`: symmetric rates up to
  `3 / 5`
  are achievable.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Product inputs -/

section Prod

variable {A B Z : Type*} [Fintype A] [Fintype B] [Fintype Z]

/-- The conditional mutual information does not change under a relabelling of the conditioning. -/
lemma condMutualInfo_cond_congr {Ω a b c c' : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]
    [Fintype c'] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → a) (Y : Ω → b) {C : Ω → c} {C' : Ω → c'}
    (f : c → c') (hf : Function.Injective f) (h : ∀ ω, C' ω = f (C ω)) :
    I[X : Y | C' ; μ] = I[X : Y | C ; μ] := by
  have e₁ := condEntropy_congr_right hμ X f hf h
  have e₂ := condEntropy_congr_right hμ X (X := pair Y C) (X' := pair Y C')
    (fun t : b × c => (t.1, f t.2))
    (fun s t hst => by
      have h' := Prod.ext_iff.mp hst
      exact Prod.ext h'.1 (hf h'.2))
    fun ω => by simp [pair, h]
  simp only [condMutualInfo]
  rw [e₁, e₂]

/-- **`I(A; Z | B)` for independent `A` and `B`.** -/
lemma cInfo_prodDist {p₁ : A → ℝ} {p₂ : B → ℝ} {T : A × B → Z → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hT : IsChannel T) :
    cInfo (prodDist p₁ p₂) T = ∑ b, p₂ b * mutualInfoOf p₁ fun a => T (a, b) := by
  classical
  have hP := hp₁.prodDist hp₂
  have hμ := jointOf_isPMF hP hT
  have hrow : ∀ b, IsChannel fun a => T (a, b) := fun b a => hT _
  have hK : IsChannel fun b => outDist p₁ fun a => T (a, b) := fun b => outDist_isPMF hp₁ (hrow b)
  have hd : dist (jointOf (prodDist p₁ p₂) T) (pair (fun z : (A × B) × Z => z.1.2) Prod.snd) =
      jointOf p₂ fun b => outDist p₁ fun a => T (a, b) := by
    funext ⟨b, z⟩
    simp only [dist, pair, jointOf, Fintype.sum_prod_type, prodDist, Prod.mk.injEq, outDist]
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_eq_single b (fun b' _ hb' => sum_eq_zero fun z' _ => by simp [hb']) (by simp),
      sum_eq_single z (fun z' _ hz' => by simp [hz']) (by simp)]
    simp only [and_self, ite_true]
    ring
  have hH : H[Prod.snd | fun z : (A × B) × Z => z.1.2 ; jointOf (prodDist p₁ p₂) T] =
      ∑ b, p₂ b * entropy (outDist p₁ fun a => T (a, b)) := by
    rw [← condEntropy_jointOf hp₂ hK]
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hp₂ hK) (hd.trans ?_)
    rw [show pair (Prod.fst : B × Z → B) Prod.snd = id from rfl, dist_id]
  rw [cInfo_eq hP hT, hH, Fintype.sum_prod_type (f := fun a => prodDist p₁ p₂ a * entropy (T a)),
    sum_comm, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [mutualInfoOf_eq hp₁ (hrow b), mul_sub, mul_sum]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  simp only [prodDist]
  ring

end Prod

section Bridge

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
  {W : X₁ × X₂ → Y₁ × Y₂ → ℝ}

lemma dist_jointOf_bc₂ (p : X₁ × X₂ → ℝ) :
    dist (jointOf p W) (fun z => (z.1, z.2.2)) = jointOf p (bcMarg₂ W) := by
  classical
  funext ⟨a, y⟩
  simp only [dist, jointOf, Fintype.sum_prod_type (f := fun z : (X₁ × X₂) × (Y₁ × Y₂) => _),
    Prod.mk.injEq, bcMarg₂]
  rw [sum_eq_single a (fun b _ hb => sum_eq_zero fun o _ => by simp [hb]) (by simp), mul_sum,
    Fintype.sum_prod_type]
  rw [sum_comm, sum_eq_single y (fun y' _ hy' => sum_eq_zero fun o _ => by simp [hy']) (by simp)]
  simp

lemma dist_jointOf_bc₁ (p : X₁ × X₂ → ℝ) :
    dist (jointOf p W) (fun z => (z.1.swap, z.2.1)) =
      jointOf (fun a => p a.swap) fun t => bcMarg₁ W t.swap := by
  classical
  funext ⟨a, y⟩
  simp only [dist, jointOf, Fintype.sum_prod_type (f := fun z : (X₁ × X₂) × (Y₁ × Y₂) => _),
    Prod.mk.injEq, bcMarg₁]
  rw [sum_eq_single a.swap (fun b _ hb => sum_eq_zero fun o _ => by
    have : b.swap ≠ a := fun h => hb (by rw [← h, Prod.swap_swap])
    simp [this]) (by simp), mul_sum, Fintype.sum_prod_type]
  rw [sum_eq_single y (fun y' _ hy' => sum_eq_zero fun o _ => by simp [hy']) (by simp)]
  simp

/-- The first information of the outer bound in the notation of the joint law. -/
lemma twcInfo₁_eq {p : X₁ × X₂ → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    twcInfo₁ p W = I[fun z => z.1.1 : fun z => z.2.2 | fun z => z.1.2 ; jointOf p W] := by
  rw [twcInfo₁, cInfo, ← dist_jointOf_bc₂ p, condMutualInfo_dist (jointOf_isPMF hp hW)]
  rfl

/-- The second information of the outer bound in the notation of the joint law. -/
lemma twcInfo₂_eq {p : X₁ × X₂ → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    twcInfo₂ p W = I[fun z => z.1.2 : fun z => z.2.1 | fun z => z.1.1 ; jointOf p W] := by
  rw [twcInfo₂, cInfo, ← dist_jointOf_bc₁ p, condMutualInfo_dist (jointOf_isPMF hp hW)]
  rfl

/-- The law of the random code without time sharing. -/
lemma dist_twLaw_unit {p₁ : X₁ → ℝ} {p₂ : X₂ → ℝ} :
    dist (twLaw (fun _ : Unit => 1) (fun _ => p₁) (fun _ => p₂) W) (fun z => (z.1.2, z.2)) =
      jointOf (prodDist p₁ p₂) W := by
  classical
  set L := twLaw (fun _ : Unit => 1) (fun _ => p₁) (fun _ => p₂) W with hL
  set G : (Unit × (X₁ × X₂)) × (Y₁ × Y₂) → (X₁ × X₂) × (Y₁ × Y₂) := fun z => (z.1.2, z.2) with hG
  have hGi : Function.Injective G := fun a b h => by
    have h' := Prod.ext_iff.mp h
    exact Prod.ext (Prod.ext rfl h'.1) h'.2
  funext ⟨s, o⟩
  have h := dist_comp_of_injective L id hGi (((), s), o)
  rw [dist_id] at h
  refine h.trans ?_
  simp [hL, twLaw, twIn, jointOf, prodDist]

/-- The first information of the inner bound without time sharing. -/
lemma twLaw_unit_info₁ {p₁ : X₁ → ℝ} {p₂ : X₂ → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hW : IsChannel W) :
    I[fun z => z.1.2.1 : fun z => z.2.2 | fun z => (z.1.1, z.1.2.2) ;
      twLaw (fun _ : Unit => 1) (fun _ => p₁) (fun _ => p₂) W] = twcInfo₁ (prodDist p₁ p₂) W := by
  have hq : IsPMF fun _ : Unit => (1 : ℝ) := ⟨fun _ => zero_le_one, by simp⟩
  have hL := twLaw_isPMF hq (fun _ => hp₁) (fun _ => hp₂) hW
  have hP := hp₁.prodDist hp₂
  rw [condMutualInfo_cond_congr hL _ _ (C := fun z => z.1.2.2) (fun x => ((), x))
    (fun a b h => (Prod.ext_iff.mp h).2) fun _ => rfl]
  rw [twcInfo₁_eq hP hW, ← dist_twLaw_unit, condMutualInfo_dist hL]
  rfl

/-- The second information of the inner bound without time sharing. -/
lemma twLaw_unit_info₂ {p₁ : X₁ → ℝ} {p₂ : X₂ → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hW : IsChannel W) :
    I[fun z => z.1.2.2 : fun z => z.2.1 | fun z => (z.1.1, z.1.2.1) ;
      twLaw (fun _ : Unit => 1) (fun _ => p₁) (fun _ => p₂) W] = twcInfo₂ (prodDist p₁ p₂) W := by
  have hq : IsPMF fun _ : Unit => (1 : ℝ) := ⟨fun _ => zero_le_one, by simp⟩
  have hL := twLaw_isPMF hq (fun _ => hp₁) (fun _ => hp₂) hW
  have hP := hp₁.prodDist hp₂
  rw [condMutualInfo_cond_congr hL _ _ (C := fun z => z.1.2.1) (fun x => ((), x))
    (fun a b h => (Prod.ext_iff.mp h).2) fun _ => rfl]
  rw [twcInfo₂_eq hP hW, ← dist_twLaw_unit, condMutualInfo_dist hL]
  rfl

/-- **Shannon's inner bound for product inputs, without time sharing.** -/
theorem isAchievableTWC_of_lt_prod [Nonempty X₁] [Nonempty X₂] {p₁ : X₁ → ℝ} {p₂ : X₂ → ℝ}
    (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h₁ : R₁ * log 2 < twcInfo₁ (prodDist p₁ p₂) W)
    (h₂ : R₂ * log 2 < twcInfo₂ (prodDist p₁ p₂) W) : IsAchievableTWC W R₁ R₂ := by
  have hq : IsPMF fun _ : Unit => (1 : ℝ) := ⟨fun _ => zero_le_one, by simp⟩
  refine isAchievableTWC_of_lt hq (fun _ => hp₁) (fun _ => hp₂) hW ?_ ?_
  · rwa [twLaw_unit_info₁ hp₁ hp₂ hW]
  · rwa [twLaw_unit_info₂ hp₁ hp₂ hW]

/-- The first information of the outer bound for a product input. -/
lemma twcInfo₁_prodDist {p₁ : X₁ → ℝ} {p₂ : X₂ → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hW : IsChannel W) :
    twcInfo₁ (prodDist p₁ p₂) W = ∑ b, p₂ b * mutualInfoOf p₁ fun a => bcMarg₂ W (a, b) :=
  cInfo_prodDist hp₁ hp₂ hW.bcMarg₂

/-- The second information of the outer bound for a product input. -/
lemma twcInfo₂_prodDist {p₁ : X₁ → ℝ} {p₂ : X₂ → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hW : IsChannel W) :
    twcInfo₂ (prodDist p₁ p₂) W = ∑ a, p₁ a * mutualInfoOf p₂ fun b => bcMarg₁ W (a, b) := by
  have e : (fun a : X₂ × X₁ => prodDist p₁ p₂ a.swap) = prodDist p₂ p₁ := by
    funext a
    simp [prodDist, mul_comm]
  rw [twcInfo₂, e]
  exact cInfo_prodDist hp₂ hp₁ fun t => hW.bcMarg₁ t.swap

end Bridge

/-! ### Decoupled channels -/

section Decoupled

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
  {T₂ : X₁ → Y₂ → ℝ} {T₁ : X₂ → Y₁ → ℝ}

/-- The decoupled two-way channel `p(y₁, y₂ | x₁, x₂) = p(y₁ | x₂) p(y₂ | x₁)`. -/
def decoupledTW (T₂ : X₁ → Y₂ → ℝ) (T₁ : X₂ → Y₁ → ℝ) : X₁ × X₂ → Y₁ × Y₂ → ℝ :=
  fun x y => T₁ x.2 y.1 * T₂ x.1 y.2

omit [Fintype X₁] [Fintype X₂] in
lemma decoupledTW_isChannel (hT₂ : IsChannel T₂) (hT₁ : IsChannel T₁) :
    IsChannel (decoupledTW T₂ T₁) := fun x =>
  (hT₁ x.2).prodDist (hT₂ x.1)

omit [Fintype X₁] [Fintype X₂] [Fintype Y₂] in
lemma bcMarg₂_decoupledTW (hT₁ : IsChannel T₁) (x : X₁ × X₂) :
    bcMarg₂ (decoupledTW T₂ T₁) x = T₂ x.1 := by
  funext y
  simp only [bcMarg₂, decoupledTW]
  rw [← sum_mul, (hT₁ x.2).sum_eq_one, one_mul]

omit [Fintype X₁] [Fintype X₂] [Fintype Y₁] in
lemma bcMarg₁_decoupledTW (hT₂ : IsChannel T₂) (x : X₁ × X₂) :
    bcMarg₁ (decoupledTW T₂ T₁) x = T₁ x.2 := by
  funext y
  simp only [bcMarg₁, decoupledTW]
  rw [← mul_sum, (hT₂ x.1).sum_eq_one, mul_one]

/-- `I(A; Z | B) ≤ I(A; Z)` when `Z` depends only on `A`. -/
lemma cInfo_comp_fst_le {A B Z : Type*} [Fintype A] [Fintype B] [Fintype Z] {p : A × B → ℝ}
    {T : A → Z → ℝ} (hp : IsPMF p) (hT : IsChannel T) :
    cInfo p (fun t => T t.1) ≤ mutualInfoOf (dist p Prod.fst) T := by
  classical
  have hT' : IsChannel fun t : A × B => T t.1 := fun t => hT _
  have hμ := jointOf_isPMF hp hT'
  have hp₁ := hp.dist (Prod.fst : A × B → A)
  have h₁ := condEntropy_le_entropy hμ (Prod.snd : (A × B) × Z → Z) fun z => z.1.2
  have h₂ : H[Prod.snd ; jointOf p fun t : A × B => T t.1] = entropy (outDist (dist p Prod.fst) T)
    := by
    rw [entropyRV, dist_jointOf_snd]
    congr 1
    funext y
    simp only [outDist, dist_fst, sum_mul, Fintype.sum_prod_type]
  have h₃ : ∑ a : A × B, p a * entropy (T a.1) = ∑ a, dist p Prod.fst a * entropy (T a) := by
    simp only [dist_fst, sum_mul, Fintype.sum_prod_type]
  rw [cInfo_eq hp hT', mutualInfoOf_eq hp₁ hT, h₃]
  linarith

/-- **Page 18-48 of [elgamal2010]: Shannon's inner bound is tight for a decoupled channel.** The
capacity region is the product of the capacities of the two channels, in bits. -/
theorem twcCapacityRegion_decoupled [Nonempty X₁] [Nonempty X₂] (hT₂ : IsChannel T₂)
    (hT₁ : IsChannel T₁) :
    twcCapacityRegion (decoupledTW T₂ T₁) =
      Set.Iic (capacity T₂ / log 2) ×ˢ Set.Iic (capacity T₁ / log 2) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hW := decoupledTW_isChannel hT₂ hT₁
  apply Set.Subset.antisymm
  · refine closure_minimal (fun R hR => ?_) (isClosed_Iic.prod isClosed_Iic)
    refine closure_minimal (fun R hR => ?_) (isClosed_Iic.prod isClosed_Iic)
      (IsAchievableTWC.mem_closure_twcOuterRegion hW hR)
    obtain ⟨p, hp, h₁, h₂⟩ := hR
    refine ⟨h₁.trans (div_le_div_of_nonneg_right ?_ hlog2.le),
      h₂.trans (div_le_div_of_nonneg_right ?_ hlog2.le)⟩
    · have e : bcMarg₂ (decoupledTW T₂ T₁) = fun t => T₂ t.1 := funext (bcMarg₂_decoupledTW hT₁)
      rw [twcInfo₁, e]
      exact (cInfo_comp_fst_le hp hT₂).trans (mutualInfoOf_le_capacity (hp.dist _) hT₂)
    · have e : (fun t : X₂ × X₁ => bcMarg₁ (decoupledTW T₂ T₁) t.swap) = fun t => T₁ t.1 :=
        funext fun t => bcMarg₁_decoupledTW hT₂ t.swap
      have hs : IsPMF fun a : X₂ × X₁ => p a.swap :=
        ⟨fun a => hp.nonneg _, (Equiv.sum_comp (Equiv.prodComm X₂ X₁) p).trans hp.sum_eq_one⟩
      rw [twcInfo₂, e]
      exact (cInfo_comp_fst_le hs hT₁).trans (mutualInfoOf_le_capacity (hs.dist _) hT₁)
  · obtain ⟨p₁, hp₁, hC₁⟩ := exists_capacity_eq hT₂
    obtain ⟨p₂, hp₂, hC₂⟩ := exists_capacity_eq hT₁
    have hsub : Set.Iio (capacity T₂ / log 2) ×ˢ Set.Iio (capacity T₁ / log 2) ⊆
        {R : ℝ × ℝ | IsAchievableTWC (decoupledTW T₂ T₁) R.1 R.2} := by
      rintro ⟨R₁, R₂⟩ ⟨h₁, h₂⟩
      simp only [Set.mem_Iio, lt_div_iff₀ hlog2] at h₁ h₂
      refine isAchievableTWC_of_lt_prod hp₁ hp₂ hW ?_ ?_
      · rw [twcInfo₁_prodDist hp₁ hp₂ hW]
        simp only [bcMarg₂_decoupledTW hT₁]
        rw [← sum_mul, hp₂.sum_eq_one, one_mul, hC₁] at *
        exact h₁
      · rw [twcInfo₂_prodDist hp₁ hp₂ hW]
        simp only [bcMarg₁_decoupledTW hT₂]
        rw [← sum_mul, hp₁.sum_eq_one, one_mul, hC₂]
        exact h₂
    have := closure_mono hsub
    rwa [closure_prod_eq, closure_Iio, closure_Iio] at this

end Decoupled

/-! ### Common output -/

section Common

variable {X₁ X₂ Y : Type*} [Fintype Y] {V : X₁ × X₂ → Y → ℝ}

/-- The two-way channel with a common output `Y₁ = Y₂ = Y`. -/
def commonTW (V : X₁ × X₂ → Y → ℝ) : X₁ × X₂ → Y × Y → ℝ :=
  fun x y => V x y.1 * ind (y.2 = y.1)

omit [Fintype Y] in
lemma bcMarg₁_commonTW [Fintype Y] (x : X₁ × X₂) : bcMarg₁ (commonTW V) x = V x := by
  classical
  funext y
  simp only [bcMarg₁, commonTW]
  rw [sum_eq_single y (fun y' _ hy' => by rw [ind_of_neg hy', mul_zero]) (by simp),
    ind_of_pos rfl, mul_one]

omit [Fintype Y] in
lemma bcMarg₂_commonTW [Fintype Y] (x : X₁ × X₂) : bcMarg₂ (commonTW V) x = V x := by
  classical
  funext y
  simp only [bcMarg₂, commonTW]
  rw [sum_eq_single y (fun y' _ hy' => by rw [ind_of_neg hy'.symm, mul_zero]) (by simp),
    ind_of_pos rfl, mul_one]

lemma commonTW_isChannel (hV : IsChannel V) : IsChannel (commonTW V) := fun x => by
  classical
  refine ⟨fun y => mul_nonneg ((hV x).nonneg _) (ind_nonneg _), ?_⟩
  rw [Fintype.sum_prod_type]
  have h : ∀ y₁, ∑ y₂, commonTW V x (y₁, y₂) = V x y₁ := fun y₁ => by
    simp only [commonTW]
    rw [sum_eq_single y₁ (fun y' _ hy' => by rw [ind_of_neg hy', mul_zero]) (by simp),
      ind_of_pos rfl, mul_one]
  simp only [h]
  exact (hV x).sum_eq_one

end Common

/-! ### The binary multiplier channel -/

section BMC

/-- **Page 18-49 of [elgamal2010].** The binary multiplier channel `Y = X₁ · X₂`. -/
def bmcV (x : Bool × Bool) (y : Bool) : ℝ := if y = (x.1 && x.2) then 1 else 0

lemma bmcV_isChannel : IsChannel bmcV := fun x => by
  obtain ⟨a, b⟩ := x
  refine ⟨fun y => ?_, ?_⟩
  · simp only [bmcV]
    split_ifs <;> norm_num
  · cases a <;> cases b <;> simp [bmcV]

lemma bmcV_swap (x : Bool × Bool) : bmcV x.swap = bmcV x := by
  funext y
  simp [bmcV, Bool.and_comm]

/-- `I(X₁; Y | X₂ = 1) = H(X₁)`. -/
lemma mutualInfoOf_bmcV_true {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    mutualInfoOf (msBern p) (fun a => bmcV (a, true)) = binEntropy p := by
  have hc : IsChannel fun a => bmcV (a, true) := fun a => bmcV_isChannel _
  have he : ∀ a, entropy (bmcV (a, true)) = 0 := fun a => by
    rw [entropy_bool (bmcV_isChannel _)]
    cases a <;> simp [bmcV]
  have ho : outDist (msBern p) (fun a => bmcV (a, true)) = msBern p := by
    funext y
    cases y <;> simp [outDist, msBern, bmcV]
  rw [mutualInfoOf_eq (msBern_isPMF h0 h1) hc, ho, entropy_msBern h0 h1]
  simp [he]

/-- `I(X₁; Y | X₂ = 0) = 0`. -/
lemma mutualInfoOf_bmcV_false {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    mutualInfoOf (msBern p) (fun a => bmcV (a, false)) = 0 := by
  have hc : IsChannel fun a => bmcV (a, false) := fun a => bmcV_isChannel _
  have he : ∀ a, entropy (bmcV (a, false)) = 0 := fun a => by
    rw [entropy_bool (bmcV_isChannel _)]
    simp [bmcV]
  have ho : outDist (msBern p) (fun a => bmcV (a, false)) = bmcV (false, false) := by
    funext y
    cases y <;> simp [outDist, msBern, bmcV]
  rw [mutualInfoOf_eq (msBern_isPMF h0 h1) hc, ho, he]
  simp [he]

/-- **The inner bound for the binary multiplier channel, page 18-49.** With `P(X₁ = 1) = p₁` and
`P(X₂ = 1) = p₂`, every pair with `R₁ < p₂ H(p₁)` and `R₂ < p₁ H(p₂)`, in bits, is achievable. -/
theorem isAchievableTWC_bmc {p₁ p₂ R₁ R₂ : ℝ} (h₁0 : 0 ≤ p₁) (h₁1 : p₁ ≤ 1) (h₂0 : 0 ≤ p₂)
    (h₂1 : p₂ ≤ 1) (h₁ : R₁ * log 2 < p₂ * binEntropy p₁) (h₂ : R₂ * log 2 < p₁ * binEntropy p₂) :
    IsAchievableTWC (commonTW bmcV) R₁ R₂ := by
  have hW := commonTW_isChannel bmcV_isChannel
  have hp₁ := msBern_isPMF h₁0 h₁1
  have hp₂ := msBern_isPMF h₂0 h₂1
  refine isAchievableTWC_of_lt_prod hp₁ hp₂ hW ?_ ?_
  · rw [twcInfo₁_prodDist hp₁ hp₂ hW]
    simp only [bcMarg₂_commonTW, Fintype.sum_bool]
    rw [mutualInfoOf_bmcV_true h₁0 h₁1, mutualInfoOf_bmcV_false h₁0 h₁1]
    simpa [msBern] using h₁
  · rw [twcInfo₂_prodDist hp₁ hp₂ hW]
    simp only [bcMarg₁_commonTW, Fintype.sum_bool]
    have e : ∀ a : Bool, (fun b => bmcV (a, b)) = fun b => bmcV (b, a) := fun a => by
      funext b
      exact bmcV_swap (b, a)
    rw [e, e, mutualInfoOf_bmcV_true h₂0 h₂1, mutualInfoOf_bmcV_false h₂0 h₂1]
    simpa [msBern] using h₂

/-- The value `3 / 5` for `p₁ = p₂ = 3 / 4`. -/
lemma three_fifths_le_binEntropy : 3 / 5 * log 2 ≤ 3 / 4 * binEntropy (3 / 4) := by
  have h3 : 5 * log 3 ≤ 8 * log 2 := by
    have h : ((3 : ℝ) ^ 5) ≤ 2 ^ 8 := by norm_num
    have := log_le_log (by norm_num) h
    rw [log_pow, log_pow] at this
    exact_mod_cast this
  have e₁ : log (4 / 3 : ℝ) = 2 * log 2 - log 3 := by
    rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have e₂ : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have e : binEntropy (3 / 4) = 3 / 4 * (2 * log 2 - log 3) + 1 / 4 * (2 * log 2) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [negMulLog]
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num, log_div (by norm_num) (by norm_num),
      log_div (by norm_num) (by norm_num), e₂]
    rw [log_one, show (3 : ℝ) = 3 from rfl]
    ring
  rw [e]
  linarith

/-- **Symmetric rates up to `3 / 5` are achievable** for the binary multiplier channel. The notes
state the larger value `0.6170`. -/
theorem isAchievableTWC_bmc_symm {R : ℝ} (hR : R < 3 / 5) : IsAchievableTWC (commonTW bmcV) R R :=
  by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have h : R * log 2 < 3 / 4 * binEntropy (3 / 4) :=
    (mul_lt_mul_of_pos_right hR hlog2).trans_le three_fifths_le_binEntropy
  exact isAchievableTWC_bmc (by norm_num) (by norm_num) (by norm_num) (by norm_num) h h

/-- The pair `(3 / 5, 3 / 5)` lies in the capacity region of the binary multiplier channel. -/
theorem three_fifths_mem_twcCapacityRegion_bmc :
    ((3 / 5 : ℝ), (3 / 5 : ℝ)) ∈ twcCapacityRegion (commonTW bmcV) := by
  have hsub : Set.Iio (3 / 5 : ℝ) ×ˢ Set.Iio (3 / 5 : ℝ) ⊆
      {R : ℝ × ℝ | IsAchievableTWC (commonTW bmcV) R.1 R.2} := by
    rintro ⟨R₁, R₂⟩ ⟨h₁, h₂⟩
    have h₁' : R₁ < 3 / 5 := h₁
    have h₂' : R₂ < 3 / 5 := h₂
    have hlog2 : 0 < log 2 := log_pos (by norm_num)
    exact isAchievableTWC_bmc (p₁ := 3 / 4) (p₂ := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ((mul_lt_mul_of_pos_right h₁' hlog2).trans_le three_fifths_le_binEntropy)
      ((mul_lt_mul_of_pos_right h₂' hlog2).trans_le three_fifths_le_binEntropy)
  have := closure_mono hsub
  rw [closure_prod_eq, closure_Iio] at this
  exact this ⟨Set.mem_Iic.mpr le_rfl, Set.mem_Iic.mpr le_rfl⟩

/-- `H(Y | X₂)` for the binary multiplier channel: `(a + c) H(c / (a + c))`. -/
def bmcPhi (a c : ℝ) : ℝ := negMulLog a + negMulLog c - negMulLog (a + c)

lemma bmcPhi_eq {t c : ℝ} (h0 : 0 ≤ c) (hc : c ≤ t) :
    bmcPhi (t - c) c = t * binEntropy (c / t) := by
  rcases hc.eq_or_lt with rfl | hlt
  · rcases h0.eq_or_lt with rfl | hc0
    · simp [bmcPhi, negMulLog]
    · have : c / c = 1 := div_self hc0.ne'
      simp [bmcPhi, this, negMulLog]
  have ht : 0 < t := h0.trans_lt hlt
  have hd : 0 < t - c := sub_pos.mpr hlt
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have e : 1 - c / t = (t - c) / t := by
    field_simp
  rw [e]
  simp only [bmcPhi, negMulLog]
  rcases h0.eq_or_lt with rfl | hc0
  · simp [ht.ne', div_self]
  rw [log_div hc0.ne' ht.ne', log_div hd.ne' ht.ne', sub_add_cancel]
  field_simp
  ring

/-- **The concavity of `negMulLog`, in the form of increments.** -/
lemma negMulLog_incr {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hc : 0 ≤ c) :
    negMulLog (y + c) + negMulLog x ≤ negMulLog y + negMulLog (x + c) := by
  have hL : 0 ≤ y + c - x := by linarith
  rcases hL.eq_or_lt with h | hLpos
  · have e₁ : y = x := by linarith
    have e₂ : c = 0 := by linarith
    rw [e₁, e₂]
    simp
  have hconc := Real.concaveOn_negMulLog
  set L := y + c - x with hLd
  have hL0 : L ≠ 0 := hLpos.ne'
  have hy : (c / L) * x + ((y - x) / L) * (y + c) = y := by
    field_simp
    rw [hLd]
    ring
  have hxc : ((y - x) / L) * x + (c / L) * (y + c) = x + c := by
    field_simp
    rw [hLd]
    ring
  have ha : 0 ≤ c / L := by positivity
  have hb : 0 ≤ (y - x) / L := div_nonneg (by linarith) hLpos.le
  have hab : c / L + (y - x) / L = 1 := by
    rw [← add_div, div_eq_one_iff_eq hL0, hLd]
    ring
  have hab' : (y - x) / L + c / L = 1 := by linarith
  have hx' : x ∈ Set.Ici (0 : ℝ) := hx
  have hz' : y + c ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith)
  have h₁ := hconc.2 hx' hz' ha hb hab
  have h₂ := hconc.2 hx' hz' hb ha hab'
  simp only [smul_eq_mul] at h₁ h₂
  rw [hy] at h₁
  rw [hxc] at h₂
  have hs : c / L * negMulLog x + (y - x) / L * negMulLog (y + c) +
      ((y - x) / L * negMulLog x + c / L * negMulLog (y + c)) =
      (c / L + (y - x) / L) * (negMulLog x + negMulLog (y + c)) := by ring
  rw [hab, one_mul] at hs
  linarith

/-- `I(X₁; Y | X₂)` for an arbitrary input law of the binary multiplier channel. -/
lemma cInfo_bmcV {p : Bool × Bool → ℝ} (hp : IsPMF p) :
    cInfo p bmcV = bmcPhi (p (true, true)) (p (false, true)) := by
  classical
  have hμ := jointOf_isPMF hp bmcV_isChannel
  have he : ∀ a, entropy (bmcV a) = 0 := fun a => by
    rw [entropy_bool (bmcV_isChannel _)]
    obtain ⟨a, b⟩ := a
    cases a <;> cases b <;> simp [bmcV]
  rw [cInfo_eq hp bmcV_isChannel, condEntropy_eq_sub hμ]
  simp only [he, mul_zero, sum_const_zero, sub_zero, entropyRV]
  rw [entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, dist, pair, jointOf, Fintype.sum_prod_type, bmcV]
  simp only [bmcPhi]
  simp

/-- The bound does not decrease when the mass of `(0, 0)` moves to `(1, 1)`. -/
lemma bmcPhi_mono {a d c : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hc : 0 ≤ c) :
    bmcPhi a c ≤ bmcPhi (a + d) c := by
  have := negMulLog_incr ha (le_add_of_nonneg_right hd) hc
  simp only [bmcPhi]
  linarith

/-- **The outer bound for the binary multiplier channel, pages 18-49 and 18-50.** -/
theorem mem_twcOuterRegion_bmc_iff {R : ℝ × ℝ} :
    R ∈ twcOuterRegion (commonTW bmcV) ↔ ∃ p₁ p₂ : ℝ, 0 ≤ p₁ ∧ 0 ≤ p₂ ∧ p₁ + p₂ ≤ 1 ∧
      R.1 ≤ (1 - p₁) * binEntropy (p₂ / (1 - p₁)) / log 2 ∧
      R.2 ≤ (1 - p₂) * binEntropy (p₁ / (1 - p₂)) / log 2 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hi₁ : ∀ p : Bool × Bool → ℝ, IsPMF p →
      twcInfo₁ p (commonTW bmcV) = bmcPhi (p (true, true)) (p (false, true)) := fun p hp => by
    rw [twcInfo₁, show bcMarg₂ (commonTW bmcV) = bmcV from funext bcMarg₂_commonTW]
    exact cInfo_bmcV hp
  have hi₂ : ∀ p : Bool × Bool → ℝ, IsPMF p →
      twcInfo₂ p (commonTW bmcV) = bmcPhi (p (true, true)) (p (true, false)) := fun p hp => by
    have hs : IsPMF fun a : Bool × Bool => p a.swap :=
      ⟨fun a => hp.nonneg _, (Equiv.sum_comp (Equiv.prodComm Bool Bool) p).trans hp.sum_eq_one⟩
    have e : (fun t : Bool × Bool => bcMarg₁ (commonTW bmcV) t.swap) = bmcV := by
      funext t
      rw [bcMarg₁_commonTW, bmcV_swap]
    rw [twcInfo₂, e, cInfo_bmcV hs]
    rfl
  constructor
  · rintro ⟨p, hp, h₁, h₂⟩
    rw [hi₁ p hp] at h₁
    rw [hi₂ p hp] at h₂
    have hs := hp.sum_eq_one
    rw [Fintype.sum_prod_type] at hs
    simp only [Fintype.sum_bool] at hs
    have ha := hp.nonneg (true, true)
    have hb := hp.nonneg (true, false)
    have hc := hp.nonneg (false, true)
    have hd := hp.nonneg (false, false)
    refine ⟨p (true, false), p (false, true), hb, hc, by linarith, ?_, ?_⟩
    · refine h₁.trans (div_le_div_of_nonneg_right ?_ hlog2.le)
      rw [← bmcPhi_eq hc (by linarith)]
      have e : 1 - p (true, false) - p (false, true) = p (true, true) + p (false, false) := by
        linarith
      rw [e]
      exact bmcPhi_mono ha hd hc
    · refine h₂.trans (div_le_div_of_nonneg_right ?_ hlog2.le)
      rw [← bmcPhi_eq hb (by linarith)]
      have e : 1 - p (false, true) - p (true, false) = p (true, true) + p (false, false) := by
        linarith
      rw [e]
      exact bmcPhi_mono ha hd hb
  · rintro ⟨p₁, p₂, h₁0, h₂0, hs, h₁, h₂⟩
    let p : Bool × Bool → ℝ := fun x =>
      if x.1 then (if x.2 then 1 - p₁ - p₂ else p₁) else (if x.2 then p₂ else 0)
    have hp : IsPMF p := by
      refine ⟨fun x => ?_, ?_⟩
      · obtain ⟨a, b⟩ := x
        cases a <;> cases b <;> simp only [p, Bool.false_eq_true, ite_true, ite_false] <;> linarith
      · rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, p, Bool.false_eq_true, ite_true, ite_false]
        ring
    refine ⟨p, hp, ?_, ?_⟩
    · rw [hi₁ p hp]
      have e : bmcPhi (p (true, true)) (p (false, true)) = (1 - p₁) * binEntropy (p₂ / (1 - p₁)) :=
        by
        rw [← bmcPhi_eq h₂0 (by linarith)]
        simp [p]
      rwa [e]
    · rw [hi₂ p hp]
      have e : bmcPhi (p (true, true)) (p (true, false)) = (1 - p₂) * binEntropy (p₁ / (1 - p₂)) :=
        by
        rw [← bmcPhi_eq h₁0 (by linarith)]
        simp only [p, ite_true, Bool.false_eq_true, ite_false]
        congr 1
        ring
      rwa [e]

end BMC

end InfoTheory
