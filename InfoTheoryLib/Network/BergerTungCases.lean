/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungSharing
public import InfoTheoryLib.RateDistortion.SideInfoConverse

/-!
# The Berger–Tung inner bound: special cases

With `U₂ = X₂`, the inner bound of Lecture 13 reduces to the rates `R₁ > I(X₁; U₁ | X₂)`,
`R₂ > H(X₂ | U₁)` and `R₁ + R₂ > I(X₁; U₁) + H(X₂ | U₁)`, for the Hamming distortion of the second
source at `D₂ = 0`. This contains the Wyner–Ziv rates, and the Slepian–Wolf rates with `U₁ = X₁`.

## Main statements

* `isAchievableDL_of_side`: **the inner bound for `D₂ = 0`**.
* `isAchievableDL_of_wyner_ziv`: the Wyner–Ziv rates, with no limit on the rate of `X₂`.
* `isAchievableDL_slepian_wolf`: the Slepian–Wolf rates, at the Hamming distortion `0`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ υ₁ : Type*} [Fintype α₁] [Fintype α₂] [Fintype υ₁]
  {P : α₁ × α₂ → ℝ} {κ₁ : α₁ → υ₁ → ℝ} {d₁ : α₁ → β₁ → ℝ}

/-- The map from the law of `((X₁, X₂), U₁)` to the law of `(((X₁, U₁), X₂), U₂)` with `U₂ = X₂`. -/
def caseMap (w : (α₁ × α₂) × υ₁) : ((α₁ × υ₁) × α₂) × α₂ := (((w.1.1, w.2), w.1.2), w.1.2)

omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] in
lemma caseMap_injective : Function.Injective (caseMap (α₁ := α₁) (α₂ := α₂) (υ₁ := υ₁)) := by
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
  simp only [caseMap, Prod.mk.injEq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, -⟩ := h
  rfl

/-- With `U₂ = X₂`, the law is the image of `p(x₁, x₂) p(u₁ | x₁)`. -/
lemma btLaw_identity [DecidableEq α₂] (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) :
    btLaw P κ₁ identityKernel = dist (siLaw P κ₁) caseMap := by
  classical
  funext ⟨⟨⟨x₁, u₁⟩, x₂⟩, u₂⟩
  by_cases h : u₂ = x₂
  · subst h
    have h' := dist_comp_of_injective (siLaw P κ₁) id
      (caseMap_injective (α₁ := α₁) (α₂ := α₂) (υ₁ := υ₁)) ((x₁, u₂), u₁)
    rw [dist_id] at h'
    refine Eq.trans ?_ h'.symm
    simp [btLaw, btQ₃, jointOf, siLaw, identityKernel]
  · have h0 : dist (siLaw P κ₁) caseMap (((x₁, u₁), x₂), u₂) = 0 :=
      dist_eq_zero_of_forall_ne _ fun w hw => h (by
        have := Prod.mk.inj hw
        have h2 := (Prod.mk.inj this.1).2
        rw [← this.2, ← h2])
    rw [h0]
    simp [btLaw, jointOf, identityKernel, h]

variable (h₁ : IsChannel κ₁) (hP : IsPMF P)

include hP h₁ in
/-- `I(X₁; U₁ | U₂) = I(X₁; U₁ | X₂)` for `U₂ = X₂`. -/
lemma btRate₁_identity [DecidableEq α₂] :
    btRate₁ P κ₁ identityKernel = sideRate 1 P κ₁ := by
  have hμ := siLaw_isPMF hP h₁
  rw [btRate₁_eq hP h₁ identityKernel_isChannel, sideRate, one_mul]
  have e1 : I[fun z : ((α₁ × υ₁) × α₂) × α₂ => z.1.1.2 : fun z => z.1.1.1 ;
      btLaw P κ₁ identityKernel] = I[fun w : (α₁ × α₂) × υ₁ => w.1.1 : Prod.snd ; siLaw P κ₁] := by
    rw [mutualInfo_comm hμ]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [btLaw_identity, ← dist_comp_eq]
    rfl
  have e2 : I[fun z : ((α₁ × υ₁) × α₂) × α₂ => z.1.1.2 : Prod.snd ;
      btLaw P κ₁ identityKernel] = I[fun w : (α₁ × α₂) × υ₁ => w.1.2 : Prod.snd ; siLaw P κ₁] := by
    rw [mutualInfo_comm hμ]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [btLaw_identity, ← dist_comp_eq]
    rfl
  rw [e1, e2]

include hP h₁ in
/-- `I(X₂; U₂ | U₁) = H(X₂ | U₁)` for `U₂ = X₂`. -/
lemma btRate₂_identity [DecidableEq α₂] :
    btRate₂ P κ₁ identityKernel = H[fun w : (α₁ × α₂) × υ₁ => w.1.2 | Prod.snd ; siLaw P κ₁] := by
  classical
  have hμ := siLaw_isPMF hP h₁
  rw [btRate₂_eq hP h₁ identityKernel_isChannel]
  have e1 : I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × α₂ => z.1.2 ; btLaw P κ₁ identityKernel] =
      H[fun w : (α₁ × α₂) × υ₁ => w.1.2 ; siLaw P κ₁] := by
    have e : I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × α₂ => z.1.2 ; btLaw P κ₁ identityKernel] =
        I[fun w : (α₁ × α₂) × υ₁ => w.1.2 : fun w => w.1.2 ; siLaw P κ₁] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [btLaw_identity, ← dist_comp_eq]
      rfl
    rw [e, mutualInfo_eq_entropy_sub_condEntropy hμ, condEntropy_self hμ, sub_zero]
  have e2 : I[fun z : ((α₁ × υ₁) × α₂) × α₂ => z.1.1.2 : Prod.snd ;
      btLaw P κ₁ identityKernel] = I[fun w : (α₁ × α₂) × υ₁ => w.1.2 : Prod.snd ; siLaw P κ₁] := by
    rw [mutualInfo_comm hμ]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [btLaw_identity, ← dist_comp_eq]
    rfl
  rw [e1, e2, mutualInfo_eq_entropy_sub_condEntropy hμ]
  ring

include hP h₁ in
/-- `I(X₁, X₂; U₁, U₂) = I(X₁; U₁) + H(X₂ | U₁)` for `U₂ = X₂`. -/
lemma btRate₁₂_identity [DecidableEq α₂] :
    btRate₁₂ P κ₁ identityKernel =
      sideRate 0 P κ₁ + H[fun w : (α₁ × α₂) × υ₁ => w.1.2 | Prod.snd ; siLaw P κ₁] := by
  have hid : IsChannel (identityKernel (α := α₂)) := identityKernel_isChannel
  have h1 := btRate₁_identity h₁ hP
  have h2 := btRate₂_identity h₁ hP
  rw [btRate₁_eq hP h₁ hid] at h1
  rw [btRate₂_eq hP h₁ hid] at h2
  rw [btRate₁₂_eq hP h₁ hid, ← h2]
  have h3 : sideRate 0 P κ₁ =
      I[fun z : ((α₁ × υ₁) × α₂) × α₂ => z.1.1.2 : fun z => z.1.1.1 ;
        btLaw P κ₁ identityKernel] := by
    have hμ := siLaw_isPMF hP h₁
    rw [sideRate, zero_mul, sub_zero, mutualInfo_comm hμ]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [btLaw_identity, ← dist_comp_eq]
    rfl
  rw [h3]
  ring

/-- **Lecture 13, page 13-5.** When `d₂` is the Hamming distortion and `D₂ = 0`, the inner bound
gives the rates `R₁ > I(X₁; U₁ | X₂)`, `R₂ > H(X₂ | U₁)` and `R₁ + R₂ > I(X₁; U₁) + H(X₂ | U₁)`, in
bits, for `p(u₁ | x₁)` and `x̂₁(u₁, x₂)` with `E d₁(X₁, X̂₁) ≤ D₁`. -/
theorem isAchievableDL_of_side [Finite β₁] (hP : IsPMF P) (hd₁ : ∀ x y, 0 ≤ d₁ x y)
    (h₁ : IsChannel κ₁) (f : υ₁ → α₂ → β₁) {R₁ R₂ D₁ : ℝ}
    (hc : sideCost P κ₁ (fun u x y => d₁ x (f u y)) ≤ D₁) (hR₁ : sideRate 1 P κ₁ / log 2 < R₁)
    (hR₂ : H[fun w : (α₁ × α₂) × υ₁ => w.1.2 | Prod.snd ; siLaw P κ₁] / log 2 < R₂)
    (hR₁₂ : (sideRate 0 P κ₁ + H[fun w : (α₁ × α₂) × υ₁ => w.1.2 | Prod.snd ; siLaw P κ₁]) / log 2 <
      R₁ + R₂) :
    IsAchievableDL P d₁ (hammingDistortion (α := α₂)) R₁ R₂ D₁ 0 := by
  classical
  have hid : IsChannel (identityKernel (α := α₂)) := identityKernel_isChannel
  have hcost₁ : btCost₁ P κ₁ identityKernel d₁ f = sideCost P κ₁ fun u x y => d₁ x (f u y) := by
    rw [btCost₁, btLaw_identity]
    exact sum_dist_mul (siLaw P κ₁) caseMap fun z => d₁ z.1.1.1 (f z.1.1.2 z.2)
  have hcost₂ : btCost₂ P κ₁ identityKernel hammingDistortion (fun (_ : υ₁) (u₂ : α₂) => u₂) =
    0 := by
    rw [btCost₂, btLaw_identity]
    refine (sum_dist_mul (siLaw P κ₁) caseMap fun z => hammingDistortion z.1.2 z.2).trans ?_
    refine sum_eq_zero fun w _ => ?_
    simp [caseMap, hammingDistortion]
  refine isAchievableDL_of_lt hP hd₁ hammingDistortion_nonneg h₁ hid f (fun _ u₂ => u₂)
    (hcost₁.le.trans hc) hcost₂.le ?_ ?_ ?_
  · rwa [btRate₁_identity h₁ hP]
  · rwa [btRate₂_identity h₁ hP]
  · rwa [btRate₁₂_identity h₁ hP]

/-- **Lecture 13, page 13-5.** When there is no rate limit for `X₂`, the inner bound gives the
Wyner–Ziv rate: `R₁ > R_SI-D(D₁)` and `R₂ > H(X₂)`, in bits. -/
theorem isAchievableDL_of_wyner_ziv [Finite β₁] [Nonempty β₁] (hP : IsPMF P)
    (hd₁ : ∀ x y, 0 ≤ d₁ x y) {R₁ R₂ D₁ : ℝ} (hD : minDistortion (margFst P) d₁ ≤ D₁)
    (hR₁ : wzRD P d₁ D₁ / log 2 < R₁) (hR₂ : H[Prod.snd ; P] / log 2 < R₂) :
    IsAchievableDL P d₁ (hammingDistortion (α := α₂)) R₁ R₂ D₁ 0 := by
  have hl := log_pos one_lt_two
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 1) hP hD
  have hμ := siLaw_isPMF hP hq
  have hY : H[fun w : (α₁ × α₂) × Fin (Fintype.card α₁ + 1) => w.1.2 ; siLaw P q] =
      H[Prod.snd ; P] := by
    rw [entropyRV, entropyRV, dist_siLaw_Y hq]
  have hle : H[fun w : (α₁ × α₂) × Fin (Fintype.card α₁ + 1) => w.1.2 | Prod.snd ; siLaw P q] ≤
      H[Prod.snd ; P] := by
    rw [← hY]
    exact condEntropy_le_entropy hμ _ _
  have hsum : sideRate 0 P q +
      H[fun w : (α₁ × α₂) × Fin (Fintype.card α₁ + 1) => w.1.2 | Prod.snd ; siLaw P q] =
      sideRate 1 P q + H[Prod.snd ; P] := by
    rw [← hY]
    simp only [sideRate]
    rw [mutualInfo_eq_entropy_sub_condEntropy hμ (fun w : (α₁ × α₂) × _ => w.1.2)]
    ring
  rw [div_lt_iff₀ hl] at hR₁ hR₂
  have hw : sideRate 1 P q < R₁ * log 2 := by
    rw [he]
    exact hR₁
  refine isAchievableDL_of_side hP hd₁ hq f hc ?_ ?_ ?_
  · rwa [div_lt_iff₀ hl]
  · rw [div_lt_iff₀ hl]
    linarith
  · rw [div_lt_iff₀ hl, hsum, add_mul]
    linarith

/-- **Lecture 13, page 13-5.** With `U₁ = X₁` and `U₂ = X₂`, the inner bound gives the Slepian–Wolf
rates, at the Hamming distortion `0`. -/
theorem isAchievableDL_slepian_wolf (hP : IsPMF P) {R₁ R₂ : ℝ}
    (hR₁ : H[Prod.fst | Prod.snd ; P] / log 2 < R₁) (hR₂ : H[Prod.snd | Prod.fst ; P] / log 2 < R₂)
    (hR₁₂ : entropy P / log 2 < R₁ + R₂) :
    IsAchievableDL P (hammingDistortion (α := α₁)) (hammingDistortion (α := α₂)) R₁ R₂ 0 0 := by
  classical
  have hid : IsChannel (identityKernel (α := α₁)) := identityKernel_isChannel
  have hμ := siLaw_isPMF hP hid
  have hf : ∀ z : (α₁ × α₂) × α₁, siLaw P identityKernel z ≠ 0 →
      (fun (u : α₁) (_ : α₂) => u) z.2 z.1.2 = z.1.1 := fun z hz => by
    by_contra hne
    apply hz
    simp [siLaw, jointOf, identityKernel, hne]
  -- The informations.
  have hsup : H[fun z : (α₁ × α₂) × α₁ => z.1.1 | pair Prod.snd (fun z => z.1.2) ;
      siLaw P identityKernel] = 0 := (condEntropy_XUY_eq_zero_iff hP hid).2 ⟨fun u _ => u, hf⟩
  have e₁ : sideRate 1 P (identityKernel (α := α₁)) = H[Prod.fst | Prod.snd ; P] :=
    sideRate_one_eq_of_support hP hid hsup
  have hmap : siLaw P (identityKernel (α := α₁)) = dist P fun z => (z, z.1) := by
    funext ⟨z, u⟩
    by_cases h : u = z.1
    · subst h
      have h' := dist_comp_of_injective P id (f := fun z : α₁ × α₂ => (z, z.1))
        (fun a b h => (Prod.mk.inj h).1) z
      rw [dist_id] at h'
      refine Eq.trans ?_ h'.symm
      simp [siLaw, jointOf, identityKernel]
    · have h0 : dist P (fun z : α₁ × α₂ => (z, z.1)) (z, u) = 0 :=
        dist_eq_zero_of_forall_ne _ fun w hw => h (by
          have := Prod.mk.inj hw
          rw [← this.2, ← this.1])
      rw [h0]
      simp [siLaw, jointOf, identityKernel, h]
  have e₂ : H[fun w : (α₁ × α₂) × α₁ => w.1.2 | Prod.snd ; siLaw P identityKernel] =
      H[Prod.snd | Prod.fst ; P] := by
    refine condEntropy_eq_of_dist_pair_eq hμ hP ?_
    rw [hmap, ← dist_comp_eq]
    rfl
  have e₃ : sideRate 0 P (identityKernel (α := α₁)) = H[Prod.fst ; P] := by
    have h1 : H[fun w : (α₁ × α₂) × α₁ => w.1.1 | Prod.snd ; siLaw P identityKernel] = 0 :=
      (condEntropy_eq_zero_iff hμ _ _).2 ⟨id, fun z hz => (hf z hz).symm⟩
    rw [sideRate, zero_mul, sub_zero, mutualInfo_eq_entropy_sub_condEntropy hμ, h1, sub_zero]
    rw [entropyRV, entropyRV, dist_siLaw_X hid]
  have hchain : H[Prod.fst ; P] + H[Prod.snd | Prod.fst ; P] = entropy P := by
    rw [← chain_rule hP]
    rw [entropyRV, dist_pair_fst_snd]
  refine isAchievableDL_of_side hP (fun x y => hammingDistortion_nonneg x y) hid (fun u _ => u)
    ((sideCost_hamming_le_zero_iff hP hid fun u _ => u).2 hf) ?_ ?_ ?_
  · rwa [e₁]
  · rwa [e₂]
  · rwa [e₃, e₂, hchain]

end InfoTheory
