/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCCutSet
public import InfoTheoryLib.Network.BCDegradedMessages
public import InfoTheoryLib.StateChannel.GPDerandomize

/-!
# Semi-deterministic broadcast channels

Marton's inner bound holds also for a random mapping `p(x | u₁, u₂)`: with `X = V(U₁, U₂)` for a
random function `V` independent of `(U₁, U₂)`, the pair `U₂' = (U₂, V)` satisfies
`I(U₁; U₂') = I(U₁; U₂)` and `I(U₂'; Y₂) ≥ I(U₂; Y₂)`, and `X` is a function of `(U₁, U₂')`.

For the semi-deterministic DM-BC, with `Y₁ = y₁(X)`, taking `U₁ = Y₁` gives the capacity region:
`R₁ ≤ H(Y₁)`, `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ H(Y₁ | U) + I(U; Y₂)` for some `p(u, x)`. As
`I(X; Y₁) = H(Y₁)` and `I(X; Y₁ | U) = H(Y₁ | U)`, this is the outer bound `bcOuterRegionBits`.

## Main definitions

* `martonMix₁`, `martonMix₂`: the channels `p(yⱼ | u₁, u₂)` of a random mapping `p(x | u₁, u₂)`.
* `martonMixInfo₁`, `martonMixInfo₂`: `I(U₁; Y₁)`, `I(U₂; Y₂)` for a random mapping.
* `IsSemiDeterministicBC W`: `Y₁ = y₁(X)`.

## Main statements

* `isAchievableBCBits_of_marton_mix`: Marton's inner bound for a random mapping.
* `bcInfoXY₁_eq_entropy`, `bcInfoXY₁U_eq_condEntropy`: `I(X; Y₁) = H(Y₁)` and
  `I(X; Y₁ | U) = H(Y₁ | U)`.
* `bcCapacityRegionBits_eq_of_isSemiDeterministicBC`: **the capacity region of the
  semi-deterministic DM-BC (Lecture 9)**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒰₁ 𝒰₂ α β₁ β₂ : Type*} [Fintype 𝒰₁] [Fintype 𝒰₂] [Fintype α] [Fintype β₁] [Fintype β₂]
  {q : 𝒰₁ × 𝒰₂ → ℝ} {W : α → β₁ × β₂ → ℝ}

/-! ### A random mapping -/

/-- The channel `p(y₁ | u₁, u₂) = ∑ₓ p(x | u₁, u₂) p(y₁ | x)`. -/
def martonMix₁ (κ : 𝒰₁ × 𝒰₂ → α → ℝ) (W : α → β₁ × β₂ → ℝ) : 𝒰₁ × 𝒰₂ → β₁ → ℝ :=
  fun z y => ∑ a, κ z a * bcMarg₁ W a y

/-- The channel `p(y₂ | u₁, u₂) = ∑ₓ p(x | u₁, u₂) p(y₂ | x)`. -/
def martonMix₂ (κ : 𝒰₁ × 𝒰₂ → α → ℝ) (W : α → β₁ × β₂ → ℝ) : 𝒰₁ × 𝒰₂ → β₂ → ℝ :=
  fun z y => ∑ a, κ z a * bcMarg₂ W a y

/-- `I(U₁; Y₁)` for a random mapping. -/
def martonMixInfo₁ (q : 𝒰₁ × 𝒰₂ → ℝ) (κ : 𝒰₁ × 𝒰₂ → α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun w : (𝒰₁ × 𝒰₂) × β₁ => w.1.1 : Prod.snd ; jointOf q (martonMix₁ κ W)]

/-- `I(U₂; Y₂)` for a random mapping. -/
def martonMixInfo₂ (q : 𝒰₁ × 𝒰₂ → ℝ) (κ : 𝒰₁ × 𝒰₂ → α → ℝ) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun w : (𝒰₁ × 𝒰₂) × β₂ => w.1.2 : Prod.snd ; jointOf q (martonMix₂ κ W)]

section RandomMapping

variable {κ : 𝒰₁ × 𝒰₂ → α → ℝ}

omit [Fintype 𝒰₁] [Fintype 𝒰₂] in
private lemma mix_isChannel {β : Type*} [Fintype β] {V : α → β → ℝ} (hκ : ∀ z, IsPMF (κ z))
    (hV : IsChannel V) : IsChannel (fun z y => ∑ a, κ z a * V a y) := fun z => by
  refine ⟨fun y => sum_nonneg fun a _ => mul_nonneg ((hκ z).nonneg a) ((hV a).nonneg y), ?_⟩
  rw [sum_comm]
  simp only [← mul_sum, (hV _).sum_eq_one, mul_one, (hκ z).sum_eq_one]

omit [Fintype 𝒰₁] [Fintype 𝒰₂] in
lemma martonMix₁_isChannel (hκ : ∀ z, IsPMF (κ z)) (hW : IsChannel W) :
    IsChannel (martonMix₁ κ W) :=
  mix_isChannel hκ hW.bcMarg₁

omit [Fintype 𝒰₁] [Fintype 𝒰₂] in
lemma martonMix₂_isChannel (hκ : ∀ z, IsPMF (κ z)) (hW : IsChannel W) :
    IsChannel (martonMix₂ κ W) :=
  mix_isChannel hκ hW.bcMarg₂

/-- The law of `(U₁, U₂)` and the output, forgetting the random function. -/
private lemma dist_mix_proj [DecidableEq 𝒰₁] [DecidableEq 𝒰₂] {β : Type*} [Fintype β]
    {V : α → β → ℝ} (hκ : ∀ z, IsPMF (κ z)) (q : 𝒰₁ × 𝒰₂ → ℝ) :
    dist (jointOf (fun z : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) => q (z.1, z.2.1) * prodPMF κ z.2.2)
        (fun z y => V (z.2.2 (z.1, z.2.1)) y))
      (fun w : (𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α)) × β => ((w.1.1, w.1.2.1), w.2)) =
      jointOf q (fun z y => ∑ a, κ z a * V a y) := by
  classical
  funext ⟨⟨u₁, u₂⟩, y⟩
  simp only [dist, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  rw [sum_eq_single u₁ (fun s _ h => by simp [h]) (by simp)]
  simp only [ite_true]
  rw [sum_eq_single u₂ (fun s _ h => by simp [h]) (by simp)]
  simp only [ite_true]
  have e : ∀ v : 𝒰₁ × 𝒰₂ → α, (∑ y', if y' = y then
      jointOf (fun z : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) => q (z.1, z.2.1) * prodPMF κ z.2.2)
        (fun z y => V (z.2.2 (z.1, z.2.1)) y) ((u₁, u₂, v), y') else 0) =
      q (u₁, u₂) * (prodPMF κ v * V (v (u₁, u₂)) y) := fun v => by
    rw [sum_ite_eq' univ y]
    simp only [mem_univ, ite_true, jointOf]
    ring
  simp_rw [e, ← mul_sum]
  rw [sum_prodPMF_mul_eval hκ (u₁, u₂) fun a => V a y]
  rfl

/-- `I(U₁; U₂') = I(U₁; U₂)` for `U₂' = (U₂, V)` with `V` independent of `(U₁, U₂)`. -/
private lemma martonInfo₁₂_prod [DecidableEq 𝒰₁] [DecidableEq 𝒰₂] (hq : IsPMF q)
    (hκ : ∀ z, IsPMF (κ z)) :
    martonInfo₁₂ (fun z : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) => q (z.1, z.2.1) * prodPMF κ z.2.2) =
      martonInfo₁₂ q := by
  have hP := prodPMF_isPMF hκ
  set μ : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) → ℝ := fun z => q (z.1, z.2.1) * prodPMF κ z.2.2 with hμd
  have hμ : IsPMF μ := by
    refine ⟨fun z => mul_nonneg (hq.nonneg _) (hP.nonneg _), ?_⟩
    have := hq.sum_eq_one
    rw [Fintype.sum_prod_type] at this
    simp only [hμd, Fintype.sum_prod_type, ← mul_sum, hP.sum_eq_one, mul_one, this]
  set U₁v : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) → 𝒰₁ := fun z => z.1
  set U₂v : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) → 𝒰₂ := fun z => z.2.1
  set Vv : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) → (𝒰₁ × 𝒰₂ → α) := fun z => z.2.2
  have hjoint : ∀ v u₁ u₂,
      dist μ (pair Vv (pair U₁v U₂v)) (v, (u₁, u₂)) = prodPMF κ v * q (u₁, u₂) :=
    fun v u₁ u₂ => by
      have hinj : Function.Injective
          (fun a : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) => (a.2.2, (a.1, a.2.1))) := fun a b hab => by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext hab.2.1 (Prod.ext hab.2.2 hab.1)
      have := dist_comp_of_injective μ id hinj (u₁, u₂, v)
      rw [dist_id] at this
      refine this.trans ?_
      simp only [hμd]
      ring
  have hV : ∀ v, dist μ Vv v = prodPMF κ v := fun v => by
    rw [← sum_dist_pair_right μ Vv (pair U₁v U₂v) v, Fintype.sum_prod_type]
    simp_rw [hjoint, ← mul_sum]
    have := hq.sum_eq_one
    rw [Fintype.sum_prod_type] at this
    rw [this, mul_one]
  have hSU : ∀ u₁ u₂, dist μ (pair U₁v U₂v) (u₁, u₂) = q (u₁, u₂) := fun u₁ u₂ => by
    rw [← sum_dist_pair_left μ Vv (pair U₁v U₂v) (u₁, u₂)]
    simp_rw [hjoint, ← sum_mul, hP.sum_eq_one, one_mul]
  have hind : IndepRV μ Vv (pair U₁v U₂v) := fun v ⟨u₁, u₂⟩ => by
    rw [hjoint, hV, hSU]
  have hI0 : I[Vv : pair U₁v U₂v ; μ] = 0 := (mutualInfo_eq_zero_iff hμ _ _).2 hind
  have hcond : I[Vv : U₁v | U₂v ; μ] = 0 := by
    have h1 := chain_rule_mutualInfo₂ hμ Vv U₁v U₂v
    have h2 := mutualInfo_nonneg hμ Vv U₂v
    have h3 := condMutualInfo_nonneg hμ Vv U₁v U₂v
    linarith
  have h1 : I[U₁v : Prod.snd ; μ] = I[U₁v : pair Vv U₂v ; μ] :=
    mutualInfo_congr_right hμ U₁v (fun a : (𝒰₁ × 𝒰₂ → α) × 𝒰₂ => (a.2, a.1))
      (fun a b hab => by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext hab.2 hab.1) (fun _ => rfl)
  have h2 := chain_rule_mutualInfo₂ hμ U₁v Vv U₂v
  have h3 : I[U₁v : Vv | U₂v ; μ] = 0 := by rw [condMutualInfo_comm hμ, hcond]
  have h4 : I[U₁v : U₂v ; μ] = I[Prod.fst : Prod.snd ; q] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    funext ⟨u₁, u₂⟩
    exact hSU u₁ u₂
  change I[U₁v : Prod.snd ; μ] = I[Prod.fst : Prod.snd ; q]
  rw [h1, h2, h3, add_zero, h4]

/-- **Lecture 9 of [elgamal2010], page 9-20.** Marton's inner bound for a random mapping
`p(x | u₁, u₂)`, for nonnegative rates: the region does not increase with these mappings. -/
theorem isAchievableBCBits_of_marton_mix (hq : IsPMF q) (hκ : ∀ z, IsPMF (κ z)) (hW : IsChannel W)
    {R₁ R₂ : ℝ} (h₁ : 0 ≤ R₁) (h₂ : 0 ≤ R₂) (h1 : R₁ * log 2 < martonMixInfo₁ q κ W)
    (h2 : R₂ * log 2 < martonMixInfo₂ q κ W)
    (h12 : (R₁ + R₂) * log 2 < martonMixInfo₁ q κ W + martonMixInfo₂ q κ W - martonInfo₁₂ q) :
    IsAchievableBCBits W R₁ R₂ := by
  classical
  have hP := prodPMF_isPMF hκ
  set q' : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) → ℝ := fun z => q (z.1, z.2.1) * prodPMF κ z.2.2 with hq'd
  set x' : 𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α) → α := fun z => z.2.2 (z.1, z.2.1) with hx'
  have hq' : IsPMF q' := by
    refine ⟨fun z => mul_nonneg (hq.nonneg _) (hP.nonneg _), ?_⟩
    have := hq.sum_eq_one
    rw [Fintype.sum_prod_type] at this
    simp only [hq'd, Fintype.sum_prod_type, ← mul_sum, hP.sum_eq_one, mul_one, this]
  have hI₁ : martonInfo₁ q' x' W = martonMixInfo₁ q κ W := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    have hproj := dist_mix_proj (V := bcMarg₁ W) hκ q
    change dist (jointOf q' (martonK₁ x' W)) _ = dist (jointOf q (martonMix₁ κ W)) _
    have e : jointOf q (martonMix₁ κ W) = dist (jointOf q' (martonK₁ x' W))
        (fun w : (𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α)) × β₁ => ((w.1.1, w.1.2.1), w.2)) := hproj.symm
    rw [e, ← dist_comp_eq]
    rfl
  have hI₂ : martonMixInfo₂ q κ W ≤ martonInfo₂ q' x' W := by
    have hJ := jointOf_isPMF hq' (martonK₂_isChannel hW x')
    have hproj := dist_mix_proj (V := bcMarg₂ W) hκ q
    have e : jointOf q (martonMix₂ κ W) = dist (jointOf q' (martonK₂ x' W))
        (fun w : (𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α)) × β₂ => ((w.1.1, w.1.2.1), w.2)) := hproj.symm
    have h3 : martonMixInfo₂ q κ W =
        I[fun w : (𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α)) × β₂ => w.1.2.1 : Prod.snd ;
          jointOf q' (martonK₂ x' W)] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      change dist (jointOf q (martonMix₂ κ W)) _ = _
      rw [e, ← dist_comp_eq]
      rfl
    rw [h3]
    have h4 := mutualInfo_comp_le hJ Prod.snd
      (fun w : (𝒰₁ × 𝒰₂ × (𝒰₁ × 𝒰₂ → α)) × β₂ => w.1.2) Prod.fst
    rw [mutualInfo_comm hJ, martonInfo₂, mutualInfo_comm hJ (fun w => w.1.2)]
    exact h4
  have hI₁₂ : martonInfo₁₂ q' = martonInfo₁₂ q := martonInfo₁₂_prod hq hκ
  refine isAchievableBCBits_of_marton hq' hW x' h₁ h₂ ?_ ?_ ?_
  · rwa [hI₁]
  · exact h2.trans_le hI₂
  · rw [hI₁, hI₁₂]
    linarith

end RandomMapping

/-! ### Semi-deterministic channels -/

/-- **Lecture 9 of [elgamal2010], page 9-21.** The semi-deterministic DM-BC: `Y₁ = y₁(X)`. -/
def IsSemiDeterministicBC (W : α → β₁ × β₂ → ℝ) : Prop :=
  ∃ f₁ : α → β₁, bcMarg₁ W = detChannel f₁

section SemiDeterministic

variable {𝒰 : Type*} [Fintype 𝒰] {r : 𝒰 × α → ℝ}

private lemma semiMarg_isPMF (hr : IsPMF r) : IsPMF fun x => ∑ u, r (u, x) := by
  refine ⟨fun x => sum_nonneg fun u _ => hr.nonneg _, ?_⟩
  rw [sum_comm, ← Fintype.sum_prod_type', hr.sum_eq_one]

private lemma bcInfoXY₁_eq_entropy_marg (hr : IsPMF r) {f₁ : α → β₁}
    (hf : bcMarg₁ W = detChannel f₁) :
    bcInfoXY₁ r W = entropy (dist (fun x => ∑ u, r (u, x)) f₁) := by
  rw [bcInfoXY₁_eq, hf, mutualInfoOf_detChannel (semiMarg_isPMF hr)]

/-- For `Y₁ = y₁(X)`, `I(X; Y₁) = H(Y₁)`. -/
theorem bcInfoXY₁_eq_entropy (hr : IsPMF r) {f₁ : α → β₁} (hf : bcMarg₁ W = detChannel f₁) :
    bcInfoXY₁ r W = H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1 ; bcJoint r W] := by
  classical
  rw [bcInfoXY₁_eq_entropy_marg hr hf, entropyRV]
  congr 1
  funext y
  rw [← sum_dist_pair_left (bcJoint r W) (fun z => z.1.2) (fun z => z.2.1) y]
  have e : ∀ a, dist (bcJoint r W) (pair (fun z => z.1.2) (fun z => z.2.1)) (a, y) =
      (∑ u, r (u, a)) * detChannel f₁ a y := fun a => by
    rw [dist_bcJoint_XY₁, hf]
  simp_rw [e]
  simp only [dist, detChannel, mul_ite, mul_one, mul_zero]

/-- For `Y₁ = y₁(X)`, `I(X; Y₁ | U) = H(Y₁ | U)`. -/
theorem bcInfoXY₁U_eq_condEntropy (hr : IsPMF r) (hW : IsChannel W) {f₁ : α → β₁}
    (hf : bcMarg₁ W = detChannel f₁) :
    bcInfoXY₁U r W = H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1 | fun z => z.1.1 ; bcJoint r W] := by
  have hJ := bcJoint_isPMF hr hW
  have h1 := bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U hr hW
  rw [bcInfoXY₁_eq_entropy hr hf] at h1
  have h2 : bcInfoUY₁ r W = H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1 ; bcJoint r W] -
      H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1 | fun z => z.1.1 ; bcJoint r W] := by
    rw [bcInfoUY₁, mutualInfo_comm hJ, mutualInfo_eq_entropy_sub_condEntropy hJ]
  linarith

/-- The law of `((Y₁, U), X)`. -/
private def semiLaw (r : 𝒰 × α → ℝ) (f₁ : α → β₁) : (β₁ × 𝒰) × α → ℝ :=
  open Classical in fun z => if f₁ z.2 = z.1.1 then r (z.1.2, z.2) else 0

private lemma semiLaw_isPMF (hr : IsPMF r) (f₁ : α → β₁) : IsPMF (semiLaw r f₁) := by
  classical
  refine ⟨fun z => ?_, ?_⟩
  · simp only [semiLaw]
    split_ifs
    · exact hr.nonneg _
    · exact le_rfl
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [semiLaw, sum_comm (s := (univ : Finset β₁)), sum_ite_eq, mem_univ, ite_true]
    rw [← Fintype.sum_prod_type', hr.sum_eq_one]

private lemma semiLaw_dist_fst (f₁ : α → β₁) (y : β₁) (u : 𝒰) :
    dist (semiLaw r f₁) Prod.fst (y, u) = ∑ x, r (u, x) * detChannel f₁ x y := by
  classical
  rw [dist_fst]
  simp only [semiLaw, detChannel, mul_ite, mul_one, mul_zero]

omit [Fintype α] [Fintype β₁] [Fintype β₂] [Fintype 𝒰] in
/-- The law of `(B, C)` under a law of `((A, B), C)`. -/
private lemma dist_snd_snd {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : (A × B) × C → ℝ) (b : B) (c : C) :
    dist μ (pair (fun w : (A × B) × C => w.1.2) Prod.snd) (b, c) = ∑ a, μ ((a, b), c) := by
  classical
  simp only [dist, pair_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single b (fun s _ h => by simp [h]) (by simp)]
  simp

/-- With `U₁ = Y₁`, `U₂ = U`, Marton's three informations are `I(X; Y₁)`, `I(U; Y₂)`, `I(U; Y₁)`. -/
private lemma semi_infos (hr : IsPMF r) (hW : IsChannel W) {f₁ : α → β₁}
    (hf : bcMarg₁ W = detChannel f₁) {κ : β₁ × 𝒰 → α → ℝ} (hκ : ∀ z, IsPMF (κ z))
    (hker : ∀ z a, semiLaw r f₁ (z, a) = dist (semiLaw r f₁) Prod.fst z * κ z a) :
    martonMixInfo₁ (dist (semiLaw r f₁) Prod.fst) κ W = bcInfoXY₁ r W ∧
      martonMixInfo₂ (dist (semiLaw r f₁) Prod.fst) κ W = bcInfoUY₂ r W ∧
      martonInfo₁₂ (dist (semiLaw r f₁) Prod.fst) = bcInfoUY₁ r W := by
  classical
  have hs := semiLaw_isPMF hr f₁
  have hq₀ := hs.dist (Prod.fst : (β₁ × 𝒰) × α → β₁ × 𝒰)
  obtain ⟨q₀, hq₀d⟩ : ∃ q₀, q₀ = dist (semiLaw r f₁) Prod.fst := ⟨_, rfl⟩
  rw [← hq₀d] at hq₀ hker ⊢
  have hval : ∀ y u, q₀ (y, u) = ∑ x, r (u, x) * detChannel f₁ x y := fun y u => by
    rw [hq₀d, semiLaw_dist_fst]
  refine ⟨?_, ?_, ?_⟩
  · have hsupp : ∀ (z : β₁ × 𝒰) (y : β₁), q₀ z ≠ 0 → martonMix₁ κ W z y ≠ 0 → y = z.1 := by
      intro z y hz hy
      by_contra hne
      refine hy (sum_eq_zero fun a _ => ?_)
      rw [hf]
      by_cases hay : f₁ a = y
      · have h0 : semiLaw r f₁ (z, a) = 0 := by
          simp only [semiLaw]
          split_ifs with h
          · exact absurd (hay.symm.trans h) hne
          · rfl
        rw [hker] at h0
        rw [(mul_eq_zero.1 h0).resolve_left hz, zero_mul]
      · simp [detChannel, hay]
    have h1 := mutualInfo_comp_jointOf_of_output_eq hq₀ (martonMix₁_isChannel hκ hW) Prod.fst hsupp
    refine h1.trans ?_
    rw [bcInfoXY₁_eq_entropy_marg hr hf]
    congr 1
    funext y
    rw [dist_fst]
    simp_rw [hval]
    simp only [dist, detChannel, mul_ite, mul_one, mul_zero]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  · rw [bcInfoUY₂_eq]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    funext ⟨u, y₂⟩
    have e := dist_snd_snd (jointOf q₀ (martonMix₂ κ W)) u y₂
    refine e.trans ?_
    simp only [jointOf, martonMix₂, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    have e' : ∀ y₁, q₀ (y₁, u) * (κ (y₁, u) x * bcMarg₂ W x y₂) =
        semiLaw r f₁ ((y₁, u), x) * bcMarg₂ W x y₂ := fun y₁ => by
      rw [hker]
      ring
    simp_rw [e']
    simp only [semiLaw, ite_mul, zero_mul]
    rw [sum_ite_eq univ (f₁ x)]
    simp
  · rw [martonInfo₁₂, mutualInfo_comm hq₀, bcInfoUY₁_eq]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    funext ⟨u, y⟩
    rw [dist_pair_snd_fst, hval, hf]

/-- `I(U; Y₂) ≤ C₂`. -/
private lemma bcInfoUY₂_le_capacity (hr : IsPMF r) (hW : IsChannel W) :
    bcInfoUY₂ r W ≤ capacity (bcMarg₂ W) := by
  have hW' : IsChannel (bcReceiverSwap W) := hW.bcReceiverSwap
  have h1 := bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U hr hW'
  have h2 := condMutualInfo_nonneg (bcJoint_isPMF hr hW') (fun z => z.1.2) (fun z => z.2.1)
    (fun z => z.1.1)
  rw [bcInfoUY₁_bcReceiverSwap, bcInfoXY₁_eq, bcMarg₁_bcReceiverSwap] at h1
  have h3 := mutualInfoOf_le_capacity (semiMarg_isPMF hr) hW.bcMarg₂
  have h4 : 0 ≤ bcInfoXY₁U r (bcReceiverSwap W) := h2
  linarith

/-- **Lecture 9 of [elgamal2010], page 9-21.** The capacity region of the semi-deterministic DM-BC
is the set of `(R₁, R₂)` with `R₁ ≤ H(Y₁)`, `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ H(Y₁ | U) + I(U; Y₂)` for
some `p(u, x)`, up to closure: by `bcInfoXY₁_eq_entropy` and `bcInfoXY₁U_eq_condEntropy`, this is
`bcOuterRegionBits`. -/
theorem bcCapacityRegionBits_eq_of_isSemiDeterministicBC [Nonempty α] (hW : IsChannel W)
    (h : IsSemiDeterministicBC W) : bcCapacityRegionBits W = closure (bcOuterRegionBits W) := by
  classical
  obtain ⟨f₁, hf⟩ := h
  have hl := log_pos one_lt_two
  refine Set.Subset.antisymm (closure_minimal (fun R hR => ?_) isClosed_closure)
    (closure_minimal ?_ isClosed_closure)
  · exact IsAchievableBCBits.mem_closure_bcOuterRegionBits hW hR
  · rintro ⟨R₁, R₂⟩ ⟨k, r, hr, h₂, h₁₂, h₁⟩
    dsimp only at h₁ h₂ h₁₂
    rw [le_div_iff₀ hl] at h₁ h₂ h₁₂
    obtain ⟨κ, hκ, hker⟩ := exists_kernel (semiLaw_isPMF hr f₁)
    obtain ⟨i₁, i₂, i₁₂⟩ := semi_infos hr hW hf hκ hker
    have hsum := bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U hr hW
    have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine mem_closure_of_sub_icEps hε fun n _ => ?_
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    set t := 1 / ((n : ℝ) + 1)
    have htl : 0 < t * log 2 := mul_pos hpos hl
    have a₁ : (R₁ - t) * log 2 < bcInfoXY₁ r W := by nlinarith
    have a₂ : (R₂ - t) * log 2 < bcInfoUY₂ r W := by nlinarith
    have a₁₂ : (R₁ - t + (R₂ - t)) * log 2 < bcInfoXY₁U r W + bcInfoUY₂ r W := by nlinarith
    rcases le_or_gt (R₁ - t) 0 with hR₁ | hR₁
    · refine isAchievableBCBits_of_lt_capacity₂ hW hR₁ ?_
      rw [lt_div_iff₀ hl]
      exact a₂.trans_le (bcInfoUY₂_le_capacity hr hW)
    rcases le_or_gt (R₂ - t) 0 with hR₂ | hR₂
    · refine isAchievableBCBits_of_lt_capacity₁ hW hR₂ ?_
      rw [lt_div_iff₀ hl]
      refine a₁.trans_le ?_
      rw [bcInfoXY₁_eq]
      exact mutualInfoOf_le_capacity (semiMarg_isPMF hr) hW.bcMarg₁
    refine isAchievableBCBits_of_marton_mix ((semiLaw_isPMF hr f₁).dist Prod.fst) hκ hW hR₁.le
      hR₂.le ?_ ?_ ?_
    · rwa [i₁]
    · rwa [i₂]
    · rw [i₁, i₂, i₁₂]
      linarith

end SemiDeterministic

end InfoTheory
