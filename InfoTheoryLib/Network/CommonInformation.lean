/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.GrayWynerConverse

/-!
# The common part and the notions of common information

This file defines the common part of two random variables, the Gács–Körner–Witsenhausen common
information `K(U₁; U₂)` and Wyner's common information `J(U₁; U₂)`, and relates them to the corner
points of the Gray–Wyner region, as on pages 15-14, 15-15 and 15-23 to 15-25 of Lecture 15 of
El Gamal and Kim.

## Main definitions

* `CommonIdx P`, `commonG₁ P`, `commonG₂ P`: the common part, as the connected components of the
  bipartite graph of the pairs with positive probability.
* `gkCommon P`: the Gács–Körner–Witsenhausen common information, in nats.
* `gwResidual P κ`: `I(U₁; U₂|V)`.
* `wynerSet P`, `wynerJ P`: Wyner's common information, in nats.

## Main statements

* `commonG_eq`, `exists_common_lift`: the common part is a common function, and every common
  function is a function of it. This is the maximality of `k` on page 15-15.
* `gwRegion_le`: the four bounds of page 15-24.
* `mem_gwRegion_det` and the extreme points of page 15-23.
* `gkCommon_le_mutualInfo`, `mutualInfo_le_wynerJ`, `wynerJ_le_entropy`:
  `K(U₁; U₂) ≤ I(U₁; U₂) ≤ J(U₁; U₂) ≤ H(U₁, U₂)`.
* `gkCommon_mem_gwRegion`, `le_gkCommon_of_mem_gwRegion`: `K(U₁; U₂)` is the largest `R₀` with
  `R₀ + R₁ = H(U₁)` and `R₀ + R₂ = H(U₂)`.
* `exists_wyner_min`, `wynerJ_mem_gwRegion`, `wynerJ_le_of_mem_gwRegion`: `J(U₁; U₂)` is the
  smallest `R₀` with `R₀ + R₁ + R₂ = H(U₁, U₂)`.
* `mutualInfo_of_outer`: `I(U₁; U₂)` is the largest `R₀` with
  `2 R₀ + R₁ + R₂ = H(U₁) + H(U₂)` allowed by the bounds.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ : Type*}

/-! ### The common part -/

section Common

/-- The relation between the symbols of a pair with positive probability. -/
def commonRel (P : α₁ × α₂ → ℝ) (x y : α₁ ⊕ α₂) : Prop :=
  ∃ a b, x = Sum.inl a ∧ y = Sum.inr b ∧ P (a, b) ≠ 0

/-- **Lecture 15 of [elgamal2010], page 15-14.** The indices of the blocks of `p(u₁, u₂)`: the
connected components of the bipartite graph of the pairs with positive probability. -/
def CommonIdx (P : α₁ × α₂ → ℝ) : Type _ := Quot (Relation.EqvGen (commonRel P))

/-- The block of a symbol of `U₁`. -/
def commonG₁ (P : α₁ × α₂ → ℝ) (a : α₁) : CommonIdx P := Quot.mk _ (Sum.inl a)

/-- The block of a symbol of `U₂`. -/
def commonG₂ (P : α₁ × α₂ → ℝ) (b : α₂) : CommonIdx P := Quot.mk _ (Sum.inr b)

instance [Finite α₁] [Finite α₂] (P : α₁ × α₂ → ℝ) : Finite (CommonIdx P) :=
  Quot.finite _

instance [Finite α₁] [Finite α₂] (P : α₁ × α₂ → ℝ) : Fintype (CommonIdx P) :=
  Fintype.ofFinite _

variable {P : α₁ × α₂ → ℝ}

/-- **Lecture 15, page 15-15.** The common part is a common function:
`P{g₁(U₁) = g₂(U₂)} = 1`. -/
lemma commonG_eq {a : α₁} {b : α₂} (h : P (a, b) ≠ 0) : commonG₁ P a = commonG₂ P b :=
  Quot.sound (Relation.EqvGen.rel _ _ ⟨a, b, rfl, rfl, h⟩)

/-- **Lecture 15, page 15-15: the maximality of the common part.** If `h₁(U₁) = h₂(U₂)` almost
surely, then `h₁` and `h₂` are functions of the common part. -/
theorem exists_common_lift {T : Type*} (h₁ : α₁ → T) (h₂ : α₂ → T)
    (hh : ∀ a b, P (a, b) ≠ 0 → h₁ a = h₂ b) :
    ∃ f : CommonIdx P → T, (∀ a, h₁ a = f (commonG₁ P a)) ∧ ∀ b, h₂ b = f (commonG₂ P b) := by
  have hrel : ∀ x y, Relation.EqvGen (commonRel P) x y → Sum.elim h₁ h₂ x = Sum.elim h₁ h₂ y := by
    intro x y hxy
    induction hxy with
    | rel x y h =>
        obtain ⟨a, b, rfl, rfl, hab⟩ := h
        exact hh a b hab
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact ⟨Quot.lift (Sum.elim h₁ h₂) fun x y h => hrel x y h,
    fun _ => rfl, fun _ => rfl⟩

end Common

/-! ### The law of the auxiliary random variable -/

section Basic

variable [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ} {υ : Type*} [Fintype υ]
  {κ : α₁ × α₂ → υ → ℝ}

lemma dist_congr_of_ae {Ω γ : Type*} [Fintype Ω] {μ : Ω → ℝ} {X Y : Ω → γ}
    (h : ∀ ω, μ ω ≠ 0 → X ω = Y ω) : dist μ X = dist μ Y := by
  classical
  funext c
  simp only [dist]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hω : μ ω = 0
  · simp [hω]
  · rw [h ω hω]

/-- The entropy of `U₁` under the joint law. -/
lemma entropy_gw_fst (hκ : IsChannel κ) :
    H[fun z : (α₁ × α₂) × υ => z.1.1 ; jointOf P κ] = H[(Prod.fst : α₁ × α₂ → α₁) ; P] := by
  have e : (fun z : (α₁ × α₂) × υ => z.1.1) =
      (Prod.fst : α₁ × α₂ → α₁) ∘ (Prod.fst : (α₁ × α₂) × υ → α₁ × α₂) := rfl
  rw [e, entropyRV, dist_comp_eq, dist_jointOf_fst hκ]
  rfl

/-- The entropy of `U₂` under the joint law. -/
lemma entropy_gw_snd (hκ : IsChannel κ) :
    H[fun z : (α₁ × α₂) × υ => z.1.2 ; jointOf P κ] = H[(Prod.snd : α₁ × α₂ → α₂) ; P] := by
  have e : (fun z : (α₁ × α₂) × υ => z.1.2) =
      (Prod.snd : α₁ × α₂ → α₂) ∘ (Prod.fst : (α₁ × α₂) × υ → α₁ × α₂) := rfl
  rw [e, entropyRV, dist_comp_eq, dist_jointOf_fst hκ]
  rfl

/-- `I(U₁, U₂; V) = I(U₂; V | U₁) + I(U₁; V)`, and `I(U₁; V) + H(U₁|V) = H(U₁)`. -/
lemma gwInfo_add_cond₁ (hP : IsPMF P) (hκ : IsChannel κ) :
    gwInfo P κ + gwCond₁ P κ = H[Prod.fst ; P] +
      I[Prod.snd : (fun z : (α₁ × α₂) × υ => z.1.2) | (fun z => z.1.1) ; jointOf P κ] := by
  have hμ := jointOf_isPMF hP hκ
  have h1 := chain_rule_mutualInfo₂ hμ Prod.snd (fun z : (α₁ × α₂) × υ => z.1.2) (fun z => z.1.1)
  have h2 : I[Prod.snd : pair (fun z : (α₁ × α₂) × υ => z.1.2) (fun z => z.1.1) ; jointOf P κ] =
      gwInfo P κ := by
    have e := mutualInfo_congr_right hμ (Prod.snd : (α₁ × α₂) × υ → υ)
      (Y := (Prod.fst : (α₁ × α₂) × υ → α₁ × α₂)) (Prod.swap : α₁ × α₂ → α₂ × α₁)
      Prod.swap_injective fun _ => rfl
    exact e.trans (mutualInfo_comm hμ _ _)
  have h3 : I[Prod.snd : (fun z : (α₁ × α₂) × υ => z.1.1) ; jointOf P κ] =
      H[Prod.fst ; P] - gwCond₁ P κ := by
    rw [mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ, entropy_gw_fst hκ]
    rfl
  linarith

/-- `I(U₁, U₂; V) + H(U₂|V) = H(U₂) + I(U₁; V | U₂)`. -/
lemma gwInfo_add_cond₂ (hP : IsPMF P) (hκ : IsChannel κ) :
    gwInfo P κ + gwCond₂ P κ = H[Prod.snd ; P] +
      I[Prod.snd : (fun z : (α₁ × α₂) × υ => z.1.1) | (fun z => z.1.2) ; jointOf P κ] := by
  have hμ := jointOf_isPMF hP hκ
  have h1 := chain_rule_mutualInfo₂ hμ Prod.snd (fun z : (α₁ × α₂) × υ => z.1.1) (fun z => z.1.2)
  have h2 : I[Prod.snd : pair (fun z : (α₁ × α₂) × υ => z.1.1) (fun z => z.1.2) ; jointOf P κ] =
      gwInfo P κ := by
    rw [gwInfo, mutualInfo_comm hμ]
    rfl
  have h3 : I[Prod.snd : (fun z : (α₁ × α₂) × υ => z.1.2) ; jointOf P κ] =
      H[Prod.snd ; P] - gwCond₂ P κ := by
    rw [mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ, entropy_gw_snd hκ]
    rfl
  linarith

/-- `I(U₁; U₂|V)` in terms of the quantities of the Gray–Wyner theorem. -/
def gwResidual (P : α₁ × α₂ → ℝ) (κ : α₁ × α₂ → υ → ℝ) : ℝ :=
  gwCond₁ P κ + gwCond₂ P κ - (entropy P - gwInfo P κ)

/-- `I(U₁; U₂|V)` is `H(U₁|V) + H(U₂|V) - H(U₁, U₂|V)`. -/
lemma condMutualInfo_eq_gwResidual (hP : IsPMF P) (hκ : IsChannel κ) :
    I[(fun z : (α₁ × α₂) × υ => z.1.1) : (fun z => z.1.2) | Prod.snd ; jointOf P κ] =
      gwResidual P κ := by
  have hμ := jointOf_isPMF hP hκ
  have h1 := chain_rule_cond hμ (fun z : (α₁ × α₂) × υ => z.1.2) (fun z => z.1.1) Prod.snd
  have h2 : H[pair (fun z : (α₁ × α₂) × υ => z.1.2) (fun z => z.1.1) | Prod.snd ; jointOf P κ] =
      H[Prod.fst | Prod.snd ; jointOf P κ] :=
    condEntropy_congr_left hμ Prod.snd Prod.swap Prod.swap_injective fun _ => rfl
  have h3 : H[Prod.fst | Prod.snd ; jointOf P κ] = entropy P - gwInfo P κ := by
    rw [gwInfo, mutualInfo_eq_entropy_sub_condEntropy hμ, entropyRV, dist_jointOf_fst hκ]
    ring
  rw [condMutualInfo, gwResidual]
  have h4 : gwCond₁ P κ = H[fun z : (α₁ × α₂) × υ => z.1.1 | Prod.snd ; jointOf P κ] := rfl
  have h5 : gwCond₂ P κ = H[fun z : (α₁ × α₂) × υ => z.1.2 | Prod.snd ; jointOf P κ] := rfl
  linarith

lemma gwResidual_nonneg (hP : IsPMF P) (hκ : IsChannel κ) : 0 ≤ gwResidual P κ := by
  rw [← condMutualInfo_eq_gwResidual hP hκ]
  exact condMutualInfo_nonneg (jointOf_isPMF hP hκ) _ _ _

end Basic

/-! ### The bounds on the region -/

section Region

variable [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ}

/-- **Lecture 15, page 15-24.** A rate triple of the region satisfies `R₀ + R₁ ≥ H(U₁)`,
`R₀ + R₂ ≥ H(U₂)`, `R₀ + R₁ + R₂ ≥ H(U₁, U₂)` and `2 R₀ + R₁ + R₂ ≥ H(U₁) + H(U₂)`, with the rates
in bits. -/
theorem gwRegion_le (hP : IsPMF P) {R₀ R₁ R₂ : ℝ} (h : (R₀, R₁, R₂) ∈ gwRegion P) :
    H[Prod.fst ; P] ≤ (R₀ + R₁) * log 2 ∧ H[Prod.snd ; P] ≤ (R₀ + R₂) * log 2 ∧
      entropy P ≤ (R₀ + R₁ + R₂) * log 2 ∧
      H[Prod.fst ; P] + H[Prod.snd ; P] ≤ (2 * R₀ + R₁ + R₂) * log 2 := by
  obtain ⟨κ, hκ, a0, a1, a2⟩ := gwRegion_subset_gwSet hP h
  have a0' : gwInfo P κ ≤ R₀ * log 2 := a0
  have a1' : gwCond₁ P κ ≤ R₁ * log 2 := a1
  have a2' : gwCond₂ P κ ≤ R₂ * log 2 := a2
  have hμ := jointOf_isPMF hP hκ
  have e1 := gwInfo_add_cond₁ hP hκ
  have e2 := gwInfo_add_cond₂ hP hκ
  have n1 := condMutualInfo_nonneg hμ Prod.snd (fun z : (α₁ × α₂) × Fin _ => z.1.2) (fun z => z.1.1)
  have n2 := condMutualInfo_nonneg hμ Prod.snd (fun z : (α₁ × α₂) × Fin _ => z.1.1) (fun z => z.1.2)
  have n3 := gwResidual_nonneg hP hκ
  rw [gwResidual] at n3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [add_mul]
    linarith
  · rw [add_mul]
    linarith
  · simp only [add_mul]
    linarith
  · simp only [add_mul, two_mul]
    linarith

variable {τ : Type*} [Fintype τ]

omit [Fintype τ] in
/-- The joint law for a function `V = f(U₁, U₂)`. -/
lemma jointOf_detChannel (f : α₁ × α₂ → τ) :
    jointOf P (detChannel f) = dist P fun z => (z, f z) := by
  classical
  funext ⟨z, t⟩
  simp only [jointOf, detChannel, dist]
  rw [sum_eq_single z]
  · by_cases h : f z = t <;> simp [h]
  · intro z' _ hz'
    simp [hz']
  · simp

lemma gwInfo_det (f : α₁ × α₂ → τ) (hP : IsPMF P) : gwInfo P (detChannel f) = H[f ; P] := by
  rw [gwInfo, jointOf_detChannel, ← mutualInfo_comp (fun z => (z, f z)) Prod.fst Prod.snd]
  rw [mutualInfo_comm hP, mutualInfo_eq_entropy_sub_condEntropy hP]
  have : H[f | (Prod.fst ∘ fun z : α₁ × α₂ => (z, f z)) ; P] = 0 :=
    condEntropy_comp_self hP id f
  rw [show (Prod.snd ∘ fun z : α₁ × α₂ => (z, f z)) = f from rfl, this, sub_zero]

lemma gwCond₁_det (f : α₁ × α₂ → τ) (hP : IsPMF P) :
    gwCond₁ P (detChannel f) = H[Prod.fst | f ; P] := by
  rw [gwCond₁, jointOf_detChannel]
  exact (condEntropy_comp_comp hP (fun z => (z, f z)) (fun z => z.1.1) Prod.snd).symm

lemma gwCond₂_det (f : α₁ × α₂ → τ) (hP : IsPMF P) :
    gwCond₂ P (detChannel f) = H[Prod.snd | f ; P] := by
  rw [gwCond₂, jointOf_detChannel]
  exact (condEntropy_comp_comp hP (fun z => (z, f z)) (fun z => z.1.2) Prod.snd).symm

/-- The rates of a description `V = f(U₁, U₂)`. -/
theorem mem_gwRegion_det (f : α₁ × α₂ → τ) (hP : IsPMF P) :
    (H[f ; P] / log 2, H[Prod.fst | f ; P] / log 2, H[Prod.snd | f ; P] / log 2) ∈ gwRegion P := by
  have hl := log_pos one_lt_two
  refine mem_gwRegion_of_channel hP (detChannel_isChannel f) ?_ ?_ ?_
  · rw [gwInfo_det f hP, div_mul_cancel₀ _ hl.ne']
  · rw [gwCond₁_det f hP, div_mul_cancel₀ _ hl.ne']
  · rw [gwCond₂_det f hP, div_mul_cancel₀ _ hl.ne']

/-- **Lecture 15, page 15-23.** The extreme point `R₀ = 0`. -/
theorem gw_extreme_zero (hP : IsPMF P) :
    ((0 : ℝ), H[Prod.fst ; P] / log 2, H[Prod.snd ; P] / log 2) ∈ gwRegion P := by
  have h := mem_gwRegion_det (P := P) (fun _ => ()) hP
  rwa [entropyRV_const hP, zero_div, condEntropy_const hP, condEntropy_const hP] at h

/-- **Lecture 15, page 15-23.** The extreme point `R₁ = 0`, with `V = U₁`. -/
theorem gw_extreme_one (hP : IsPMF P) :
    (H[Prod.fst ; P] / log 2, (0 : ℝ), H[Prod.snd | Prod.fst ; P] / log 2) ∈ gwRegion P := by
  have h := mem_gwRegion_det (P := P) Prod.fst hP
  rwa [condEntropy_self hP, zero_div] at h

/-- **Lecture 15, page 15-23.** The extreme point `R₂ = 0`, with `V = U₂`. -/
theorem gw_extreme_two (hP : IsPMF P) :
    (H[Prod.snd ; P] / log 2, H[Prod.fst | Prod.snd ; P] / log 2, (0 : ℝ)) ∈ gwRegion P := by
  have h := mem_gwRegion_det (P := P) Prod.snd hP
  rwa [condEntropy_self hP, zero_div] at h

/-- **Lecture 15, page 15-23.** The extreme point `R₁ = R₂ = 0`, with `V = (U₁, U₂)`. -/
theorem gw_extreme_both (hP : IsPMF P) :
    (entropy P / log 2, (0 : ℝ), (0 : ℝ)) ∈ gwRegion P := by
  have h := mem_gwRegion_det (P := P) id hP
  have e₁ : H[Prod.fst | id ; P] = 0 := condEntropy_comp_self hP id Prod.fst
  have e₂ : H[Prod.snd | id ; P] = 0 := condEntropy_comp_self hP id Prod.snd
  rw [e₁, e₂, zero_div] at h
  have e₃ : H[id ; P] = entropy P := by rw [entropyRV, dist_id]
  rwa [e₃] at h

end Region

/-! ### The Gács–Körner–Witsenhausen common information -/

section GK

variable [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ}

/-- **Lecture 15 of [elgamal2010], page 15-24.** The Gács–Körner–Witsenhausen common information
`K(U₁; U₂) = H(U₀)`, in nats. -/
def gkCommon (P : α₁ × α₂ → ℝ) : ℝ := H[fun z => commonG₁ P z.1 ; P]

lemma dist_commonG (P : α₁ × α₂ → ℝ) :
    dist P (fun z => commonG₁ P z.1) = dist P fun z => commonG₂ P z.2 :=
  dist_congr_of_ae fun _ h => commonG_eq h

lemma gkCommon_nonneg (hP : IsPMF P) : 0 ≤ gkCommon P := entropyRV_nonneg hP _

/-- **Lecture 15, page 15-25.** `K(U₁; U₂) ≤ I(U₁; U₂)`. -/
theorem gkCommon_le_mutualInfo (hP : IsPMF P) : gkCommon P ≤ I[Prod.fst : Prod.snd ; P] := by
  have h1 := mutualInfo_comp_le hP (Prod.snd : α₁ × α₂ → α₂) (Prod.fst : α₁ × α₂ → α₁)
    (commonG₁ P)
  rw [mutualInfo_comm hP, mutualInfo_eq_entropy_sub_condEntropy hP] at h1
  have h2 : H[commonG₁ P ∘ Prod.fst | Prod.snd ; P] = H[commonG₂ P ∘ Prod.snd | Prod.snd ; P] := by
    refine condEntropy_eq_of_dist_pair_eq hP hP (dist_congr_of_ae fun z hz => ?_)
    obtain ⟨a, b⟩ := z
    have := commonG_eq hz
    simp only [pair, Function.comp, this]
  rw [h2, condEntropy_comp_self hP, sub_zero] at h1
  rw [mutualInfo_comm hP] at h1
  exact h1

/-- A description `V` with both double Markov chains is a function of the common part in law:
`I(U₁, U₂; V) ≤ H(U₀)`. -/
theorem gwInfo_le_gkCommon_of_markov {υ : Type*} [Fintype υ] {κ : α₁ × α₂ → υ → ℝ} (hP : IsPMF P)
    (hκ : IsChannel κ)
    (h₁ : I[Prod.snd : (fun z : (α₁ × α₂) × υ => z.1.2) | (fun z => z.1.1) ; jointOf P κ] = 0)
    (h₂ : I[Prod.snd : (fun z : (α₁ × α₂) × υ => z.1.1) | (fun z => z.1.2) ; jointOf P κ] = 0) :
    gwInfo P κ ≤ gkCommon P := by
  classical
  have hμ := jointOf_isPMF hP hκ
  set μ := jointOf P κ with hμd
  set V : (α₁ × α₂) × υ → υ := Prod.snd
  set U₁ : (α₁ × α₂) × υ → α₁ := fun z => z.1.1
  set U₂ : (α₁ × α₂) × υ → α₂ := fun z => z.1.2
  -- `κ(v | a, b) = p(v | a)` on the support.
  have hval : ∀ a b v, dist μ (pair U₂ (pair U₁ V)) (b, a, v) = P (a, b) * κ (a, b) v :=
    fun a b v => by
    have hinj : Function.Injective (fun w : (α₁ × α₂) × υ => (w.1.2, w.1.1, w.2)) := by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      tauto
    have := dist_comp_of_injective μ id hinj ((a, b), v)
    rw [dist_id] at this
    exact this
  have hval' : ∀ a b v, dist μ (pair U₁ (pair U₂ V)) (a, b, v) = P (a, b) * κ (a, b) v :=
    fun a b v => by
    have hinj : Function.Injective (fun w : (α₁ × α₂) × υ => (w.1.1, w.1.2, w.2)) := by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      tauto
    have := dist_comp_of_injective μ id hinj ((a, b), v)
    rw [dist_id] at this
    exact this
  have hP₁ : ∀ a b, dist μ (pair U₂ U₁) (b, a) = P (a, b) := fun a b => by
    have e : pair U₂ U₁ = (fun z : α₁ × α₂ => (z.2, z.1)) ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, dist_jointOf_fst hκ]
    have hinj : Function.Injective (fun z : α₁ × α₂ => (z.2, z.1)) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      tauto
    have := dist_comp_of_injective P id hinj (a, b)
    rw [dist_id] at this
    exact this
  have hP₂ : ∀ a b, dist μ (pair U₁ U₂) (a, b) = P (a, b) := fun a b => by
    have e : pair U₁ U₂ = Prod.fst := rfl
    rw [e, dist_jointOf_fst hκ]
  have hM₁ := (markovChain_iff_mul hμ U₂ U₁ V).1 ((markovChain_iff_condIndep hμ _ _ _).2
    ((condMutualInfo_eq_zero_iff hμ _ _ _).1 (by
      rw [condMutualInfo_comm hμ]
      exact h₁)))
  have hM₂ := (markovChain_iff_mul hμ U₁ U₂ V).1 ((markovChain_iff_condIndep hμ _ _ _).2
    ((condMutualInfo_eq_zero_iff hμ _ _ _).1 (by
      rw [condMutualInfo_comm hμ]
      exact h₂)))
  have hk₁ : ∀ a b v, P (a, b) ≠ 0 → κ (a, b) v = condDist μ V U₁ a v := fun a b v hab => by
    have h := hM₁ b a v
    rw [hval, hP₁] at h
    have hpa : dist μ U₁ a ≠ 0 := by
      have h3 := dist_pair_le_right hμ U₂ U₁ b a
      rw [hP₁] at h3
      have h4 : 0 < P (a, b) := lt_of_le_of_ne (hP.nonneg _) (Ne.symm hab)
      exact (h4.trans_le h3).ne'
    rw [condDist, eq_div_iff hpa]
    have h5 : κ (a, b) v * dist μ U₁ a = dist μ (pair U₁ V) (a, v) := by
      refine mul_left_cancel₀ hab ?_
      rw [← mul_assoc]
      exact h
    exact h5
  have hk₂ : ∀ a b v, P (a, b) ≠ 0 → κ (a, b) v = condDist μ V U₂ b v := fun a b v hab => by
    have h := hM₂ a b v
    rw [hval', hP₂] at h
    have hpb : dist μ U₂ b ≠ 0 := by
      have h3 := dist_pair_le_right hμ U₁ U₂ a b
      rw [hP₂] at h3
      have h4 : 0 < P (a, b) := lt_of_le_of_ne (hP.nonneg _) (Ne.symm hab)
      exact (h4.trans_le h3).ne'
    rw [condDist, eq_div_iff hpb]
    have h5 : κ (a, b) v * dist μ U₂ b = dist μ (pair U₂ V) (b, v) := by
      refine mul_left_cancel₀ hab ?_
      rw [← mul_assoc]
      exact h
    exact h5
  -- The lift to the common part.
  have hlift : ∀ v, ∃ f : CommonIdx P → ℝ, (∀ a, condDist μ V U₁ a v = f (commonG₁ P a)) ∧
      ∀ b, condDist μ V U₂ b v = f (commonG₂ P b) := fun v =>
    exists_common_lift _ _ fun a b hab => (hk₁ a b v hab).symm.trans (hk₂ a b v hab)
  choose f hf₁ _ using hlift
  have hκf : ∀ z v, P z ≠ 0 → κ z v = f v (commonG₁ P z.1) := fun ⟨a, b⟩ v hz => by
    rw [hk₁ a b v hz, hf₁]
  -- The Markov chain `V → U₀ → (U₁, U₂)`.
  set U₀ : (α₁ × α₂) × υ → CommonIdx P := fun z => commonG₁ P z.1.1 with hU₀
  have hjoint : ∀ v u, dist μ (pair V U₀) (v, u) = f v u * dist P (fun z => commonG₁ P z.1) u := by
    intro v u
    have e1 : dist μ (pair V U₀) (v, u) =
        ∑ z : α₁ × α₂, (if commonG₁ P z.1 = u then P z * κ z v else 0) := by
      simp only [dist, pair, hU₀]
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun z _ => ?_
      rw [sum_eq_single v]
      · by_cases h : commonG₁ P z.1 = u
        · simp [V, h, hμd, jointOf]
        · simp [V, h]
      · intro v' _ hv'
        simp [V, hv']
      · simp
    have e2 : dist P (fun z => commonG₁ P z.1) u =
        ∑ z : α₁ × α₂, (if commonG₁ P z.1 = u then P z else 0) := rfl
    rw [e1, e2, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    by_cases h : commonG₁ P z.1 = u
    · simp only [h, ite_true]
      by_cases hz : P z = 0
      · simp [hz]
      · rw [hκf z v hz, h]
        ring
    · simp [h]
  have hu₀ : dist μ U₀ = dist P fun z => commonG₁ P z.1 := by
    have e : U₀ = (fun z : α₁ × α₂ => commonG₁ P z.1) ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, dist_jointOf_fst hκ]
  have hMk : MarkovChain μ V U₀ Prod.fst := by
    refine (markovChain_iff_mul hμ _ _ _).2 fun v u z => ?_
    have hinj : Function.Injective (fun w : (α₁ × α₂) × υ => (w.2, commonG₁ P w.1.1, w.1)) := by
      rintro ⟨z, c⟩ ⟨z', c'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      tauto
    have e3 : dist μ (pair U₀ Prod.fst) (u, z) = if commonG₁ P z.1 = u then P z else 0 := by
      have e : pair U₀ Prod.fst = (fun t : α₁ × α₂ => (commonG₁ P t.1, t)) ∘ Prod.fst := rfl
      rw [e, dist_comp_eq, dist_jointOf_fst hκ]
      by_cases h : commonG₁ P z.1 = u
      · have hi : Function.Injective (fun t : α₁ × α₂ => (commonG₁ P t.1, t)) :=
          fun _ _ hab => (Prod.mk.inj hab).2
        have := dist_comp_of_injective P id hi z
        rw [dist_id] at this
        rw [ite_eq_left h, ← h]
        exact this
      · rw [ite_eq_right h]
        simp only [dist]
        refine sum_eq_zero fun t _ => ?_
        rw [ite_eq_right]
        intro ht
        apply h
        have h1 := (Prod.mk.inj ht).1
        have h2 := (Prod.mk.inj ht).2
        rw [← h2]
        exact h1
    have e4 : dist μ (pair V (pair U₀ Prod.fst)) (v, u, z) =
        if commonG₁ P z.1 = u then P z * κ z v else 0 := by
      by_cases h : commonG₁ P z.1 = u
      · have := dist_comp_of_injective μ id hinj (z, v)
        rw [dist_id] at this
        rw [ite_eq_left h, ← h]
        exact this
      · rw [ite_eq_right h]
        simp only [dist]
        refine sum_eq_zero fun t _ => ?_
        rw [ite_eq_right]
        intro ht
        apply h
        simp only [pair, Prod.mk.injEq, hU₀] at ht
        rw [← ht.2.2]
        exact ht.2.1
    rw [e3, e4, hjoint, hu₀]
    by_cases h : commonG₁ P z.1 = u
    · simp only [h, ite_true]
      by_cases hz : P z = 0
      · simp [hz]
      · rw [hκf z v hz, h]
        ring
    · simp [h]
  have hd := data_processing hμ hMk
  have hIU : I[V : U₀ ; μ] ≤ H[U₀ ; μ] := by
    rw [mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
    linarith [condEntropy_nonneg hμ U₀ V]
  have hHU : H[U₀ ; μ] = gkCommon P := by
    rw [entropyRV, hu₀]
    rfl
  rw [gwInfo, mutualInfo_comm hμ]
  linarith

/-- **Lecture 15, page 15-24.** `K(U₁; U₂)` is the largest common rate with `R₀ + R₁ = H(U₁)` and
`R₀ + R₂ = H(U₂)`: every such rate triple of the region has `R₀ ≤ K(U₁; U₂)`, with the rates in
bits. -/
theorem le_gkCommon_of_mem_gwRegion (hP : IsPMF P) {R₀ R₁ R₂ : ℝ} (h : (R₀, R₁, R₂) ∈ gwRegion P)
    (h₁ : (R₀ + R₁) * log 2 = H[Prod.fst ; P]) (h₂ : (R₀ + R₂) * log 2 = H[Prod.snd ; P]) :
    R₀ * log 2 ≤ gkCommon P := by
  obtain ⟨κ, hκ, a0, a1, a2⟩ := gwRegion_subset_gwSet hP h
  have a0' : gwInfo P κ ≤ R₀ * log 2 := a0
  have a1' : gwCond₁ P κ ≤ R₁ * log 2 := a1
  have a2' : gwCond₂ P κ ≤ R₂ * log 2 := a2
  have hμ := jointOf_isPMF hP hκ
  have e1 := gwInfo_add_cond₁ hP hκ
  have e2 := gwInfo_add_cond₂ hP hκ
  have n1 := condMutualInfo_nonneg hμ Prod.snd (fun z : (α₁ × α₂) × Fin _ => z.1.2) (fun z => z.1.1)
  have n2 := condMutualInfo_nonneg hμ Prod.snd (fun z : (α₁ × α₂) × Fin _ => z.1.1) (fun z => z.1.2)
  rw [add_mul] at h₁ h₂
  have hle := gwInfo_le_gkCommon_of_markov hP hκ (le_antisymm (by linarith) n1)
    (le_antisymm (by linarith) n2)
  linarith

/-- **Lecture 15, page 15-24.** The rate triple `(K, H(U₁) - K, H(U₂) - K)` is in the region. -/
theorem gkCommon_mem_gwRegion (hP : IsPMF P) :
    (gkCommon P / log 2, (H[Prod.fst ; P] - gkCommon P) / log 2,
      (H[Prod.snd ; P] - gkCommon P) / log 2) ∈ gwRegion P := by
  have h := mem_gwRegion_det (P := P) (fun z => commonG₁ P z.1) hP
  have e₁ : H[Prod.fst | (fun z : α₁ × α₂ => commonG₁ P z.1) ; P] =
      H[Prod.fst ; P] - gkCommon P := by
    have h1 := chain_rule hP (fun z : α₁ × α₂ => commonG₁ P z.1) Prod.fst
    have h2 : H[pair (fun z : α₁ × α₂ => commonG₁ P z.1) Prod.fst ; P] = H[Prod.fst ; P] :=
      entropyRV_eq_of_injective P (fun a : α₁ => (commonG₁ P a, a))
        (fun _ _ hab => (Prod.mk.inj hab).2) fun _ => rfl
    rw [gkCommon]
    linarith
  have e₂ : H[Prod.snd | (fun z : α₁ × α₂ => commonG₁ P z.1) ; P] =
      H[Prod.snd ; P] - gkCommon P := by
    have h1 := chain_rule hP (fun z : α₁ × α₂ => commonG₁ P z.1) Prod.snd
    have h2 : H[pair (fun z : α₁ × α₂ => commonG₁ P z.1) Prod.snd ; P] =
        H[pair (fun z : α₁ × α₂ => commonG₂ P z.2) Prod.snd ; P] := by
      rw [entropyRV, entropyRV]
      congr 1
      exact dist_congr_of_ae fun z hz => by
        obtain ⟨a, b⟩ := z
        simp only [pair, commonG_eq hz]
    have h3 : H[pair (fun z : α₁ × α₂ => commonG₂ P z.2) Prod.snd ; P] = H[Prod.snd ; P] :=
      entropyRV_eq_of_injective P (fun b : α₂ => (commonG₂ P b, b))
        (fun _ _ hab => (Prod.mk.inj hab).2) fun _ => rfl
    rw [gkCommon]
    linarith
  rwa [e₁, e₂] at h

end GK

/-! ### Wyner's common information -/

section Wyner

variable [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ}

/-- The values of `I(U₁, U₂; V)` over the `p(v|u₁, u₂)` with `I(U₁; U₂|V) = 0`. -/
def wynerSet (P : α₁ × α₂ → ℝ) : Set ℝ :=
  {I | ∃ (k : ℕ) (κ : α₁ × α₂ → Fin k → ℝ), IsChannel κ ∧ gwResidual P κ = 0 ∧ gwInfo P κ = I}

/-- **Lecture 15 of [elgamal2010], page 15-25.** Wyner's common information
`J(U₁; U₂) = min I(U₁, U₂; V)` over the `p(v|u₁, u₂)` with `I(U₁; U₂|V) = 0`, in nats. -/
def wynerJ (P : α₁ × α₂ → ℝ) : ℝ := sInf (wynerSet P)

/-- A value of `I(U₁, U₂; V)` for `V` on `Fin N`, with `N = |𝒰₁| |𝒰₂| + 2`, for any feasible `V`. -/
lemma exists_wyner_reduce {υ : Type*} [Fintype υ] {κ : α₁ × α₂ → υ → ℝ} (hP : IsPMF P)
    (hκ : IsChannel κ) (h : gwResidual P κ = 0) :
    ∃ κ' : α₁ × α₂ → Fin (Fintype.card (α₁ × α₂) + 2) → ℝ, IsChannel κ' ∧ gwResidual P κ' = 0 ∧
      gwInfo P κ' = gwInfo P κ := by
  obtain ⟨κ', hκ', e0, e1, e2⟩ := exists_gw_reduce hP hκ rfl
  refine ⟨κ', hκ', ?_, e0⟩
  rw [← h, gwResidual, gwResidual, e0, e1, e2]

lemma wynerSet_bddBelow (hP : IsPMF P) : BddBelow (wynerSet P) :=
  ⟨0, by
    rintro _ ⟨k, κ, hκ, -, rfl⟩
    exact mutualInfo_nonneg (jointOf_isPMF hP hκ) _ _⟩

/-- `J(U₁; U₂) ≤ I(U₁, U₂; V)` for every feasible `V` on any finite set. -/
theorem wynerJ_le {υ : Type*} [Fintype υ] {κ : α₁ × α₂ → υ → ℝ} (hP : IsPMF P) (hκ : IsChannel κ)
    (h : gwResidual P κ = 0) : wynerJ P ≤ gwInfo P κ := by
  obtain ⟨κ', hκ', h', e⟩ := exists_wyner_reduce hP hκ h
  exact csInf_le (wynerSet_bddBelow hP) ⟨_, κ', hκ', h', e⟩

/-- `V = (U₁, U₂)` is feasible. -/
lemma gwResidual_id (hP : IsPMF P) : gwResidual P (detChannel (id : α₁ × α₂ → α₁ × α₂)) = 0 := by
  have e₁ : H[Prod.fst | id ; P] = 0 := condEntropy_comp_self hP id Prod.fst
  have e₂ : H[Prod.snd | id ; P] = 0 := condEntropy_comp_self hP id Prod.snd
  have e₃ : H[id ; P] = entropy P := by rw [entropyRV, dist_id]
  rw [gwResidual, gwCond₁_det _ hP, gwCond₂_det _ hP, gwInfo_det _ hP, e₁, e₂, e₃]
  ring

/-- **Lecture 15, page 15-25.** `J(U₁; U₂) ≤ H(U₁, U₂)`. -/
theorem wynerJ_le_entropy (hP : IsPMF P) : wynerJ P ≤ entropy P := by
  have h := wynerJ_le hP (detChannel_isChannel (id : α₁ × α₂ → α₁ × α₂)) (gwResidual_id hP)
  rw [gwInfo_det _ hP] at h
  have e₃ : H[id ; P] = entropy P := by rw [entropyRV, dist_id]
  rwa [e₃] at h

lemma wynerSet_nonempty (hP : IsPMF P) : (wynerSet P).Nonempty := by
  obtain ⟨κ', hκ', h', e⟩ := exists_wyner_reduce hP
    (detChannel_isChannel (id : α₁ × α₂ → α₁ × α₂)) (gwResidual_id hP)
  exact ⟨_, _, κ', hκ', h', rfl⟩

/-- **Lecture 15, page 15-25.** The minimum is attained: `J(U₁; U₂)` is a minimum over a compact
set of test channels. -/
theorem exists_wyner_min (hP : IsPMF P) :
    ∃ κ : α₁ × α₂ → Fin (Fintype.card (α₁ × α₂) + 2) → ℝ, IsChannel κ ∧ gwResidual P κ = 0 ∧
      gwInfo P κ = wynerJ P := by
  set N := Fintype.card (α₁ × α₂) + 2
  have hc : ContinuousOn (fun κ : α₁ × α₂ → Fin N → ℝ => gwInfo P κ) {κ | IsChannel κ} := by
    have h : Continuous fun κ : α₁ × α₂ → Fin N → ℝ =>
        H[Prod.fst ; jointOf P κ] + H[Prod.snd ; jointOf P κ] -
          H[pair Prod.fst Prod.snd ; jointOf P κ] :=
      ((continuous_entropyRV_jointOf P _).add (continuous_entropyRV_jointOf P _)).sub
        (continuous_entropyRV_jointOf P _)
    refine h.continuousOn.congr fun κ hκ => ?_
    exact mutualInfo_eq_add_sub (jointOf_isPMF hP hκ) _ _
  have hc' : ContinuousOn (fun κ : α₁ × α₂ → Fin N → ℝ => gwResidual P κ) {κ | IsChannel κ} := by
    have h₁ : Continuous fun κ : α₁ × α₂ → Fin N → ℝ =>
        H[pair Prod.snd (fun z : (α₁ × α₂) × Fin N => z.1.1) ; jointOf P κ] -
          H[Prod.snd ; jointOf P κ] :=
      (continuous_entropyRV_jointOf P _).sub (continuous_entropyRV_jointOf P _)
    have h₂ : Continuous fun κ : α₁ × α₂ → Fin N → ℝ =>
        H[pair Prod.snd (fun z : (α₁ × α₂) × Fin N => z.1.2) ; jointOf P κ] -
          H[Prod.snd ; jointOf P κ] :=
      (continuous_entropyRV_jointOf P _).sub (continuous_entropyRV_jointOf P _)
    have h₃ := ((h₁.continuousOn (s := {κ | IsChannel κ})).add h₂.continuousOn).sub
      (continuousOn_const (c := entropy P) |>.sub hc)
    refine h₃.congr fun κ hκ => ?_
    have hμ := jointOf_isPMF hP (show IsChannel κ from hκ)
    simp only [gwResidual, gwCond₁, gwCond₂]
    rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
    simp only [Pi.sub_apply, Pi.add_apply]
  have hK : IsCompact {κ : α₁ × α₂ → Fin N → ℝ | IsChannel κ ∧ gwResidual P κ = 0} := by
    have hcl : IsClosed ({κ : α₁ × α₂ → Fin N → ℝ | IsChannel κ} ∩
        (fun κ => gwResidual P κ) ⁻¹' {0}) :=
      hc'.preimage_isClosed_of_isClosed isCompact_setOf_isChannel.isClosed isClosed_singleton
    exact isCompact_setOf_isChannel.of_isClosed_subset hcl fun κ hκ => hκ.1
  obtain ⟨κ₀, h₀, e₀⟩ := exists_wyner_reduce hP
    (detChannel_isChannel (id : α₁ × α₂ → α₁ × α₂)) (gwResidual_id hP)
  obtain ⟨κ, ⟨hκ, hr⟩, hmin⟩ := hK.exists_isMinOn ⟨κ₀, h₀, e₀.1⟩ (hc.mono fun κ hκ => hκ.1)
  refine ⟨κ, hκ, hr, le_antisymm ?_ (wynerJ_le hP hκ hr)⟩
  refine le_csInf (wynerSet_nonempty hP) ?_
  rintro _ ⟨k, κ', hκ', h', rfl⟩
  obtain ⟨κ'', hκ'', h'', e⟩ := exists_wyner_reduce hP hκ' h'
  rw [← e]
  exact hmin ⟨hκ'', h''⟩

/-- **Lecture 15, page 15-25.** `I(U₁; U₂) ≤ I(U₁, U₂; V)` if `I(U₁; U₂|V) = 0`. -/
theorem mutualInfo_le_gwInfo {υ : Type*} [Fintype υ] {κ : α₁ × α₂ → υ → ℝ} (hP : IsPMF P)
    (hκ : IsChannel κ) (h : gwResidual P κ = 0) :
    I[Prod.fst : Prod.snd ; P] ≤ gwInfo P κ := by
  have hμ := jointOf_isPMF hP hκ
  have e1 := gwInfo_add_cond₁ hP hκ
  have e2 := gwInfo_add_cond₂ hP hκ
  have n1 := condMutualInfo_nonneg hμ Prod.snd (fun z : (α₁ × α₂) × υ => z.1.2) (fun z => z.1.1)
  have n2 := condMutualInfo_nonneg hμ Prod.snd (fun z : (α₁ × α₂) × υ => z.1.1) (fun z => z.1.2)
  rw [mutualInfo_eq_add_sub hP]
  have e3 : H[pair Prod.fst Prod.snd ; P] = entropy P := by
    have : pair (Prod.fst : α₁ × α₂ → α₁) Prod.snd = id := rfl
    rw [this, entropyRV, dist_id]
  rw [e3]
  rw [gwResidual] at h
  linarith

/-- **Lecture 15, page 15-25.** `I(U₁; U₂) ≤ J(U₁; U₂)`. -/
theorem mutualInfo_le_wynerJ (hP : IsPMF P) : I[Prod.fst : Prod.snd ; P] ≤ wynerJ P := by
  obtain ⟨κ, hκ, hr, e⟩ := exists_wyner_min hP
  rw [← e]
  exact mutualInfo_le_gwInfo hP hκ hr

/-- **Lecture 15, page 15-25.** `0 ≤ K(U₁; U₂) ≤ I(U₁; U₂) ≤ J(U₁; U₂) ≤ H(U₁, U₂)`. -/
theorem common_information_chain (hP : IsPMF P) :
    0 ≤ gkCommon P ∧ gkCommon P ≤ I[Prod.fst : Prod.snd ; P] ∧
      I[Prod.fst : Prod.snd ; P] ≤ wynerJ P ∧ wynerJ P ≤ entropy P :=
  ⟨gkCommon_nonneg hP, gkCommon_le_mutualInfo hP, mutualInfo_le_wynerJ hP, wynerJ_le_entropy hP⟩

/-- **Lecture 15, page 15-25.** `J(U₁; U₂)` is the smallest common rate with
`R₀ + R₁ + R₂ = H(U₁, U₂)`: every such rate triple of the region has `R₀ ≥ J(U₁; U₂)`, with the
rates in bits. -/
theorem wynerJ_le_of_mem_gwRegion (hP : IsPMF P) {R₀ R₁ R₂ : ℝ} (h : (R₀, R₁, R₂) ∈ gwRegion P)
    (hs : (R₀ + R₁ + R₂) * log 2 = entropy P) : wynerJ P ≤ R₀ * log 2 := by
  obtain ⟨κ, hκ, a0, a1, a2⟩ := gwRegion_subset_gwSet hP h
  have a0' : gwInfo P κ ≤ R₀ * log 2 := a0
  have a1' : gwCond₁ P κ ≤ R₁ * log 2 := a1
  have a2' : gwCond₂ P κ ≤ R₂ * log 2 := a2
  have hn := gwResidual_nonneg hP hκ
  have hr : gwResidual P κ = 0 := by
    refine le_antisymm ?_ hn
    rw [gwResidual]
    simp only [add_mul] at hs
    linarith
  exact (wynerJ_le hP hκ hr).trans a0'

/-- **Lecture 15, page 15-25.** The minimum is achieved: some rate triple of the region has
`R₀ = J(U₁; U₂)` and `R₀ + R₁ + R₂ = H(U₁, U₂)`, with the rates in bits. -/
theorem wynerJ_mem_gwRegion (hP : IsPMF P) :
    ∃ R₁ R₂ : ℝ, (wynerJ P / log 2, R₁, R₂) ∈ gwRegion P ∧
      (wynerJ P / log 2 + R₁ + R₂) * log 2 = entropy P := by
  have hl := log_pos one_lt_two
  obtain ⟨κ, hκ, hr, e⟩ := exists_wyner_min hP
  refine ⟨gwCond₁ P κ / log 2, gwCond₂ P κ / log 2, ?_, ?_⟩
  · refine mem_gwRegion_of_channel hP hκ ?_ ?_ ?_
    · rw [div_mul_cancel₀ _ hl.ne', e]
    · rw [div_mul_cancel₀ _ hl.ne']
    · rw [div_mul_cancel₀ _ hl.ne']
  · rw [gwResidual] at hr
    simp only [add_mul, div_mul_cancel₀ _ hl.ne']
    rw [← e]
    linarith

/-- **Lecture 15, page 15-24.** `I(U₁; U₂)` is the largest common rate with
`2 R₀ + R₁ + R₂ = H(U₁) + H(U₂)` allowed by the bounds of `gwRegion_le`. -/
theorem mutualInfo_of_outer (hP : IsPMF P) {R₀ R₁ R₂ : ℝ}
    (h₂ : entropy P ≤ (R₀ + R₁ + R₂) * log 2)
    (hs : (2 * R₀ + R₁ + R₂) * log 2 = H[Prod.fst ; P] + H[Prod.snd ; P]) :
    R₀ * log 2 ≤ I[Prod.fst : Prod.snd ; P] := by
  rw [mutualInfo_eq_add_sub hP]
  have e3 : H[pair Prod.fst Prod.snd ; P] = entropy P := by
    have : pair (Prod.fst : α₁ × α₂ → α₁) Prod.snd = id := rfl
    rw [this, entropyRV, dist_id]
  rw [e3]
  simp only [add_mul, two_mul] at hs h₂
  linarith

end Wyner

end InfoTheory
