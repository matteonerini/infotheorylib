/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayCF
public import InfoTheoryLib.Network.RelayClasses

/-!
# The relay channel with orthogonal receiver components

Page 17-50 of the notes: `Y = (Y', Y'')` and `p(y, y₁ | x, x₁) = p(y', y₁ | x) p(y'' | x₁)`.

## Main definitions

* `rcRO P κ`: the relay channel with orthogonal receiver components.

## Main statements

* `isAchievableRC_ro`: the compress–forward lower bound for these channels.
* `rcMacInfo_ro_le`, `rcBcInfo_ro_le`: the cutset bound for these channels.
* `rcCapacity_ro_semiDet`: **the capacity when `Y₁` is a function of `(X, Y')`**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X U Y' Y'' S V : Type*} [Fintype X] [Fintype U] [Fintype Y'] [Fintype Y''] [Fintype S]
  [Fintype V]

/-- **Page 17-50 of [elgamal2010].** The relay channel with orthogonal receiver components. -/
def rcRO (P : X → Y' × S → ℝ) (κ : U → Y'' → ℝ) : X × U → (Y' × Y'') × S → ℝ :=
  fun a o => P a.1 (o.1.1, o.2) * κ a.2 o.1.2

variable {P : X → Y' × S → ℝ} {κ : U → Y'' → ℝ}

omit [Fintype X] [Fintype U] in
lemma rcRO_isChannel (hP : IsChannel P) (hκ : IsChannel κ) : IsChannel (rcRO P κ) := fun a => by
  refine ⟨fun o => mul_nonneg ((hP _).nonneg _) ((hκ _).nonneg _), ?_⟩
  simp only [rcRO, Fintype.sum_prod_type]
  have h₁ := (hP a.1).sum_eq_one
  have h₂ := (hκ a.2).sum_eq_one
  rw [Fintype.sum_prod_type] at h₁
  calc _ = ∑ y', ∑ s, P a.1 (y', s) * ∑ y'', κ a.2 y'' := by
        refine sum_congr rfl fun y' _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun s _ => (mul_sum _ _ _).symm
    _ = 1 := by
        simp_rw [h₂, mul_one]
        exact h₁

/-! ### The cuts for independent inputs -/

section Cuts

variable {p : X → ℝ} {p₁ : U → ℝ}

/-- The map from the two parts to the variables of the channel. -/
def roMap₀ (w : (X × (Y' × S)) × (U × Y'')) : (X × U) × ((Y' × Y'') × S) :=
  ((w.1.1, w.2.1), ((w.1.2.1, w.2.2), w.1.2.2))

/-- The inverse of `roMap₀`. -/
def roInv₀ (z : (X × U) × ((Y' × Y'') × S)) : (X × (Y' × S)) × (U × Y'') :=
  ((z.1.1, (z.2.1.1, z.2.2)), (z.1.2, z.2.1.2))

omit [Fintype X] [Fintype U] [Fintype Y'] [Fintype Y''] [Fintype S] [Fintype V] in
lemma dist_roMap₀ [Fintype X] [Fintype U] [Fintype Y'] [Fintype Y''] [Fintype S] :
    dist (prodDist (jointOf p P) (jointOf p₁ κ)) roMap₀ = jointOf (prodDist p p₁) (rcRO P κ) := by
  classical
  funext z
  simp only [dist]
  rw [sum_eq_single (roInv₀ z)]
  · have : roMap₀ (roInv₀ z) = z := rfl
    simp only [this, ite_true]
    simp only [prodDist, jointOf, roInv₀, rcRO]
    ring
  · intro w _ hw
    have : roMap₀ w ≠ z := fun h => hw (by rw [← h]; rfl)
    exact ite_eq_right this
  · simp

omit [Fintype V] in
/-- An entropy under the law of the channel, as the sum of the entropies of the two parts. -/
lemma entropy_ro₀ {C D E : Type*} [Fintype C] [Fintype D] [Fintype E] (hν₁ : IsPMF (jointOf p P))
    (hν₂ : IsPMF (jointOf p₁ κ)) (g : X × (Y' × S) → C) (h : U × Y'' → D)
    (f : (X × U) × ((Y' × Y'') × S) → E) (j : C × D → E) (hj : Function.Injective j)
    (hf : ∀ w, f (roMap₀ w) = j (g w.1, h w.2)) :
    H[f ; jointOf (prodDist p p₁) (rcRO P κ)] = H[g ; jointOf p P] + H[h ; jointOf p₁ κ] := by
  rw [← dist_roMap₀, ← entropy_prod_parts hν₁ hν₂ g h]
  have e : H[f ; dist (prodDist (jointOf p P) (jointOf p₁ κ)) roMap₀] =
      H[f ∘ roMap₀ ; prodDist (jointOf p P) (jointOf p₁ κ)] := entropyRV_dist _ _ _
  rw [e]
  exact entropyRV_eq_of_injective _ j hj hf

omit [Fintype V] in
/-- The broadcast cut for independent inputs: `I(X; Y, Y₁ | X₁) = I(X; Y', Y₁)`. -/
theorem rcBcInfo_ro_prod (hp : IsPMF p) (hp₁ : IsPMF p₁) (hP : IsChannel P) (hκ : IsChannel κ) :
    rcBcInfo (prodDist p p₁) (rcRO P κ) = mutualInfoOf p P := by
  have hν₁ : IsPMF (jointOf p P) := jointOf_isPMF hp hP
  have hν₂ : IsPMF (jointOf p₁ κ) := jointOf_isPMF hp₁ hκ
  have hμ : IsPMF (jointOf (prodDist p p₁) (rcRO P κ)) :=
    jointOf_isPMF (hp.prodDist hp₁) (rcRO_isChannel hP hκ)
  rw [rcBcInfo, condMutualInfo_eq_entropies hμ, mutualInfoOf, mutualInfo_eq_add_sub hν₁]
  have h₁ := entropy_ro₀ (p := p) (p₁ := p₁) (P := P) (κ := κ) hν₁ hν₂ Prod.fst Prod.fst
    (pair (fun z => z.1.2) fun z => z.1.1) (fun t => (t.2, t.1))
    (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl
  have h₂ := entropy_ro₀ (p := p) (p₁ := p₁) (P := P) (κ := κ) hν₁ hν₂ (fun _ => ()) Prod.fst
    (fun z => z.1.2) Prod.snd (fun a b h => Prod.ext rfl h) fun _ => rfl
  have h₃ := entropy_ro₀ (p := p) (p₁ := p₁) (P := P) (κ := κ) hν₁ hν₂
    (pair Prod.fst Prod.snd) (fun w => w)
    (pair (pair (fun z => z.1.2) Prod.snd) fun z => z.1.1)
    (fun t => ((t.2.1, ((t.1.2.1, t.2.2), t.1.2.2)), t.1.1))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₄ := entropy_ro₀ (p := p) (p₁ := p₁) (P := P) (κ := κ) hν₁ hν₂
    Prod.snd (fun w => w) (pair (fun z => z.1.2) Prod.snd)
    (fun t => (t.2.1, ((t.1.1, t.2.2), t.1.2)))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₀ : H[fun _ : X × (Y' × S) => () ; jointOf p P] = 0 := entropyRV_const hν₁ ()
  rw [h₁, h₂, h₃, h₄, h₀]
  ring

omit [Fintype V] in
/-- The multiple access cut for independent inputs: `I(X, X₁; Y) = I(X; Y') + I(X₁; Y'')`. -/
theorem rcMacInfo_ro_prod (hp : IsPMF p)
    (hp₁ : IsPMF p₁) (hP : IsChannel P) (hκ : IsChannel κ) :
    rcMacInfo (prodDist p p₁) (rcRO P κ) =
      I[Prod.fst : fun z : X × (Y' × S) => z.2.1 ; jointOf p P] + mutualInfoOf p₁ κ := by
  have hν₁ : IsPMF (jointOf p P) := jointOf_isPMF hp hP
  have hν₂ : IsPMF (jointOf p₁ κ) := jointOf_isPMF hp₁ hκ
  have hμ : IsPMF (jointOf (prodDist p p₁) (rcRO P κ)) :=
    jointOf_isPMF (hp.prodDist hp₁) (rcRO_isChannel hP hκ)
  rw [rcMacInfo_eq, mutualInfo_eq_add_sub hμ, mutualInfoOf, mutualInfo_eq_add_sub hν₁,
    mutualInfo_eq_add_sub hν₂]
  have h₁ := entropy_ro₀ (p := p) (p₁ := p₁) (P := P) (κ := κ) hν₁ hν₂ Prod.fst Prod.fst
    Prod.fst id Function.injective_id fun _ => rfl
  have h₂ := entropy_ro₀ (p := p) (p₁ := p₁) (P := P) (κ := κ) hν₁ hν₂ (fun z => z.2.1) Prod.snd
    (fun z => z.2.1) id Function.injective_id fun _ => rfl
  have h₃ := entropy_ro₀ (p := p) (p₁ := p₁) (P := P) (κ := κ) hν₁ hν₂
    (pair Prod.fst fun z => z.2.1) (pair Prod.fst Prod.snd)
    (pair Prod.fst fun z => z.2.1) (fun t => ((t.1.1, t.2.1), (t.1.2, t.2.2)))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  rw [h₁, h₂, h₃]
  ring

end Cuts

/-! ### The laws of the two parts -/

section Parts

variable {p : X → ℝ} {p₁ : U → ℝ} {τ' : S → V → ℝ}

/-- The law of the part `(X, (Y', Y₁), Ŷ₁)`. -/
def roν₁ (p : X → ℝ) (P : X → Y' × S → ℝ) (τ' : S → V → ℝ) : (X × (Y' × S)) × V → ℝ :=
  jointOf (jointOf p P) fun t => τ' t.2.2

lemma roν₁_isPMF (hp : IsPMF p) (hP : IsChannel P) (hτ' : IsChannel τ') : IsPMF (roν₁ p P τ') :=
  jointOf_isPMF (jointOf_isPMF hp hP) fun _ => hτ' _

/-- The map from the two parts to the variables of compress–forward. -/
def roMap (w : ((X × (Y' × S)) × V) × (U × Y'')) : ((X × U) × ((Y' × Y'') × S)) × V :=
  (((w.1.1.1, w.2.1), ((w.1.1.2.1, w.2.2), w.1.1.2.2)), w.1.2)

/-- The inverse of `roMap`. -/
def roInv (z : ((X × U) × ((Y' × Y'') × S)) × V) : ((X × (Y' × S)) × V) × (U × Y'') :=
  (((z.1.1.1, (z.1.2.1.1, z.1.2.2)), z.2), (z.1.1.2, z.1.2.1.2))

/-- The law of compress–forward is the law of the two independent parts. -/
lemma dist_roMap :
    dist (prodDist (roν₁ p P τ') (jointOf p₁ κ)) roMap =
      cfLaw p p₁ (rcRO P κ) (fun t => τ' t.2) := by
  classical
  funext z
  simp only [dist]
  rw [sum_eq_single (roInv z)]
  · have : roMap (roInv z) = z := rfl
    simp only [this, ite_true]
    simp only [prodDist, roν₁, jointOf, roInv, cfLaw, rcRO]
    ring
  · intro w _ hw
    have : roMap w ≠ z := fun h => hw (by rw [← h]; rfl)
    exact ite_eq_right this
  · simp

/-- An entropy under the law of compress–forward, as the sum of the entropies of the two parts. -/
lemma entropy_ro {C D E : Type*} [Fintype C] [Fintype D] [Fintype E]
    (hν₁ : IsPMF (roν₁ p P τ')) (hν₂ : IsPMF (jointOf p₁ κ))
    (g : (X × (Y' × S)) × V → C) (h : U × Y'' → D) (f : ((X × U) × ((Y' × Y'') × S)) × V → E)
    (j : C × D → E) (hj : Function.Injective j) (hf : ∀ w, f (roMap w) = j (g w.1, h w.2)) :
    H[f ; cfLaw p p₁ (rcRO P κ) (fun t => τ' t.2)] = H[g ; roν₁ p P τ'] + H[h ; jointOf p₁ κ] := by
  rw [← dist_roMap, ← entropy_prod_parts hν₁ hν₂ g h]
  have e : H[f ; dist (prodDist (roν₁ p P τ') (jointOf p₁ κ)) roMap] =
      H[f ∘ roMap ; prodDist (roν₁ p P τ') (jointOf p₁ κ)] := entropyRV_dist _ _ _
  rw [e]
  exact entropyRV_eq_of_injective _ j hj hf

/-- The second term of the compress–forward lower bound: `I(X; Y, Ŷ₁ | X₁) = I(X; Y', Ŷ₁)`. -/
theorem ro_term₂ (hp : IsPMF p) (hp₁ : IsPMF p₁) (hP : IsChannel P) (hκ : IsChannel κ)
    (hτ' : IsChannel τ') :
    I[fun z => z.1.1.1 : fun z => (z.1.2.1, z.2) | fun z => z.1.1.2 ;
        cfLaw p p₁ (rcRO P κ) (fun t => τ' t.2)] =
      I[fun z => z.1.1 : fun z => (z.1.2.1, z.2) ; roν₁ p P τ'] := by
  have hν₁ := roν₁_isPMF hp hP hτ'
  have hν₂ : IsPMF (jointOf p₁ κ) := jointOf_isPMF hp₁ hκ
  have hμ := cfLaw_isPMF hp hp₁ (rcRO_isChannel hP hκ) (τ := fun t => τ' t.2) fun _ => hτ' _
  rw [condMutualInfo_eq_entropies hμ, mutualInfo_eq_add_sub hν₁]
  have h₁ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (fun w => w.1.1) (fun w => w.1)
    (pair (fun z => z.1.1.2) fun z => z.1.1.1) (fun t => (t.2, t.1))
    (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl
  have h₂ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (fun _ => ()) (fun w => w.1) (fun z => z.1.1.2) (fun t => t.2)
    (fun a b h => Prod.ext rfl h) fun _ => rfl
  have h₃ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (fun w => ((w.1.2.1, w.2), w.1.1)) (fun w => w)
    (pair (pair (fun z => z.1.1.2) fun z => (z.1.2.1, z.2)) fun z => z.1.1.1)
    (fun t => ((t.2.1, ((t.1.1.1, t.2.2), t.1.1.2)), t.1.2))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₄ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (fun w => (w.1.2.1, w.2)) (fun w => w)
    (pair (fun z => z.1.1.2) fun z => (z.1.2.1, z.2))
    (fun t => (t.2.1, ((t.1.1, t.2.2), t.1.2)))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₅ : H[fun _ : (X × (Y' × S)) × V => () ; roν₁ p P τ'] = 0 := entropyRV_const hν₁ ()
  have e : H[pair (fun z : (X × (Y' × S)) × V => z.1.1) fun z => (z.1.2.1, z.2) ; roν₁ p P τ'] =
      H[fun w => ((w.1.2.1, w.2), w.1.1) ; roν₁ p P τ'] :=
    entropyRV_eq_of_injective _ (fun t : (Y' × V) × X => (t.2, t.1))
      (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl
  rw [h₁, h₂, h₃, h₄, e]
  linarith

/-- The first term of the compress–forward lower bound:
`I(X, X₁; Y) - I(Y₁; Ŷ₁ | X, X₁, Y) = I(X; Y') + I(X₁; Y'') - I(Y₁; Ŷ₁ | X, Y')`. -/
theorem ro_term₁ (hp : IsPMF p) (hp₁ : IsPMF p₁) (hP : IsChannel P) (hκ : IsChannel κ)
    (hτ' : IsChannel τ') :
    I[fun z => z.1.1 : fun z => z.1.2.1 ; cfLaw p p₁ (rcRO P κ) (fun t => τ' t.2)] -
        I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ;
          cfLaw p p₁ (rcRO P κ) (fun t => τ' t.2)] =
      I[fun z => z.1.1 : fun z => z.1.2.1 ; roν₁ p P τ'] + mutualInfoOf p₁ κ -
        I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ; roν₁ p P τ'] := by
  have hν₁ := roν₁_isPMF hp hP hτ'
  have hν₂ : IsPMF (jointOf p₁ κ) := jointOf_isPMF hp₁ hκ
  have hμ := cfLaw_isPMF hp hp₁ (rcRO_isChannel hP hκ) (τ := fun t => τ' t.2) fun _ => hτ' _
  rw [mutualInfo_eq_add_sub hμ, condMutualInfo_eq_entropies hμ, mutualInfoOf,
    mutualInfo_eq_add_sub hν₂, mutualInfo_eq_add_sub hν₁, condMutualInfo_eq_entropies hν₁]
  have h₁ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (fun w => w.1.1) (fun w => w.1) (fun z => z.1.1) id Function.injective_id fun _ => rfl
  have h₂ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (fun w => w.1.2.1) (fun w => w.2) (fun z => z.1.2.1) id Function.injective_id fun _ => rfl
  have h₃ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (pair (fun z => z.1.1) fun z => z.1.2.1) (pair Prod.fst Prod.snd)
    (pair (fun z => z.1.1) fun z => z.1.2.1) (fun t => ((t.1.1, t.2.1), (t.1.2, t.2.2)))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₄ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (pair (pair (fun z => z.1.1) fun z => z.1.2.1) fun z => z.1.2.2) (pair Prod.fst Prod.snd)
    (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.1.2.2)
    (fun t => (((t.1.1.1, t.2.1), (t.1.1.2, t.2.2)), t.1.2))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₅ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2) (pair Prod.fst Prod.snd)
    (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2)
    (fun t => (((t.1.1.1, t.2.1), (t.1.1.2, t.2.2)), t.1.2))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₆ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (pair (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2) fun z => z.1.2.2) (pair Prod.fst Prod.snd)
    (pair (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2) fun z => z.1.2.2)
    (fun t => ((((t.1.1.1.1, t.2.1), (t.1.1.1.2, t.2.2)), t.1.1.2), t.1.2))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have h₇ := entropy_ro (p := p) (p₁ := p₁) (P := P) (κ := κ) (τ' := τ') hν₁ hν₂
    (fun z => (z.1.1, z.1.2.1)) (pair Prod.fst Prod.snd)
    (fun z => (z.1.1, z.1.2.1)) (fun t => ((t.1.1, t.2.1), (t.1.2, t.2.2)))
    (fun a b h => by
      simp only [Prod.ext_iff] at h ⊢
      tauto) fun _ => rfl
  have e₁ : H[pair (fun z : (X × (Y' × S)) × V => z.1.1) fun z => z.1.2.1 ; roν₁ p P τ'] =
      H[fun z => (z.1.1, z.1.2.1) ; roν₁ p P τ'] := rfl
  have e₂ : H[pair (pair (fun z : (X × (Y' × S)) × V => z.1.1) fun z => z.1.2.1)
      (fun z => z.1.2.2) ; roν₁ p P τ'] =
      H[pair (fun z => (z.1.1, z.1.2.1)) fun z => z.1.2.2 ; roν₁ p P τ'] := rfl
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, e₁, e₂]
  have e₃ : H[Prod.fst ; jointOf p₁ κ] + H[Prod.snd ; jointOf p₁ κ] -
      H[pair Prod.fst Prod.snd ; jointOf p₁ κ] = 0 + (H[Prod.fst ; jointOf p₁ κ] +
        H[Prod.snd ; jointOf p₁ κ] - H[pair Prod.fst Prod.snd ; jointOf p₁ κ]) := by ring
  linarith

/-- **The compress–forward lower bound for orthogonal receiver components.** -/
theorem isAchievableRC_ro [Nonempty X] [Nonempty U] [Nonempty Y'] [Nonempty Y''] [Nonempty S]
    [Nonempty V] (hp : IsPMF p) (hp₁ : IsPMF p₁) (hP : IsChannel P) (hκ : IsChannel κ)
    (hτ' : IsChannel τ') {R : ℝ}
    (h₁ : R * log 2 < I[fun z => z.1.1 : fun z => z.1.2.1 ; roν₁ p P τ'] + mutualInfoOf p₁ κ -
      I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ; roν₁ p P τ'])
    (h₂ : R * log 2 < I[fun z => z.1.1 : fun z => (z.1.2.1, z.2) ; roν₁ p P τ']) :
    IsAchievableRC (rcRO P κ) R :=
  isAchievableRC_compressForward (τ := fun t => τ' t.2) hp hp₁ (rcRO_isChannel hP hκ)
    (fun _ => hτ' _) (by rw [ro_term₁ hp hp₁ hP hκ hτ']; exact h₁)
    (by rw [ro_term₂ hp hp₁ hP hκ hτ']; exact h₂)

end Parts

/-! ### The cuts for all inputs -/

section Bound

variable {q : X × U → ℝ}

omit [Fintype X] [Fintype Y'] [Fintype Y''] [Fintype S] [Fintype V] in
/-- An output law of a function of the input. -/
lemma outDist_dist_comp {α β : Type*} [Fintype α] [Fintype X] (q : α → ℝ) (f : α → X)
    (T : X → β → ℝ) (y : β) : outDist (dist q f) T y = ∑ a, q a * T (f a) y :=
  sum_dist_mul q f fun x => T x y

omit [Fintype V] in
/-- **The multiple access cut**: `I(X, X₁; Y) ≤ I(X; Y') + I(X₁; Y'')`. -/
theorem rcMacInfo_ro_le (hq : IsPMF q) (hP : IsChannel P) (hκ : IsChannel κ) :
    rcMacInfo q (rcRO P κ) ≤ mutualInfoOf (dist q Prod.fst) (bcMarg₁ P) +
      mutualInfoOf (dist q Prod.snd) κ := by
  classical
  have hP₁ : IsChannel (bcMarg₁ P) := hP.bcMarg₁
  have hc : ∀ a, bcMarg₁ (rcRO P κ) a = prodDist (bcMarg₁ P a.1) (κ a.2) := by
    intro a
    funext o
    simp only [bcMarg₁, rcRO, prodDist, ← sum_mul]
  have hW₁ : IsChannel (bcMarg₁ (rcRO P κ)) := (rcRO_isChannel hP hκ).bcMarg₁
  rw [rcMacInfo, mutualInfoOf_eq hq hW₁, mutualInfoOf_eq (hq.dist _) hP₁,
    mutualInfoOf_eq (hq.dist _) hκ]
  set out := outDist q (bcMarg₁ (rcRO P κ)) with hout
  have hoP : IsPMF out := outDist_isPMF hq hW₁
  have hsub : entropy out ≤ entropy (dist out Prod.fst) + entropy (dist out Prod.snd) := by
    have h := mutualInfo_nonneg hoP (Prod.fst : Y' × Y'' → Y') Prod.snd
    rw [mutualInfo_eq_add_sub hoP] at h
    have e : H[pair (Prod.fst : Y' × Y'' → Y') Prod.snd ; out] = entropy out := by
      have : (pair (Prod.fst : Y' × Y'' → Y') Prod.snd) = id := rfl
      simp only [entropyRV, this, dist_id]
    rw [e] at h
    have e₁ : H[(Prod.fst : Y' × Y'' → Y') ; out] = entropy (dist out Prod.fst) := rfl
    have e₂ : H[(Prod.snd : Y' × Y'' → Y'') ; out] = entropy (dist out Prod.snd) := rfl
    rw [e₁, e₂] at h
    linarith
  have hm₁ : dist out Prod.fst = outDist (dist q Prod.fst) (bcMarg₁ P) := by
    funext y
    rw [dist_fst, outDist_dist_comp]
    simp only [hout, outDist, hc, prodDist]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    simp only [← mul_sum, (hκ _).sum_eq_one, mul_one]
  have hm₂ : dist out Prod.snd = outDist (dist q Prod.snd) κ := by
    funext y
    rw [dist_snd, outDist_dist_comp]
    simp only [hout, outDist, hc, prodDist]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    have : ∀ y' : Y', q a * (bcMarg₁ P a.1 y' * κ a.2 y) =
        q a * κ a.2 y * bcMarg₁ P a.1 y' := fun _ => by ring
    simp_rw [this, ← mul_sum, (hP₁ _).sum_eq_one, mul_one]
  have hE : ∑ a, q a * entropy (bcMarg₁ (rcRO P κ) a) =
      ∑ x, dist q Prod.fst x * entropy (bcMarg₁ P x) + ∑ u, dist q Prod.snd u * entropy (κ u) := by
    rw [sum_dist_mul, sum_dist_mul, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [hc, entropy_prodDist (hP₁ _) (hκ _)]
    ring
  rw [hE, ← hm₁, ← hm₂]
  linarith

/-- The law of a function of a pair, row by row. -/
lemma dist_jointOf_row {α β γ : Type*} [Fintype α] [Fintype β] (q : α → ℝ) (T : α → β → ℝ)
    (R : α × β → γ) (t : γ) :
    dist (jointOf q T) R t = ∑ a, q a * dist (T a) (fun o => R (a, o)) t := by
  classical
  simp only [dist]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun o _ => ?_
  by_cases h : R (a, o) = t <;> simp [h, jointOf]

omit [Fintype X] [Fintype U] [Fintype V] in
/-- A row of the channel is the law of two independent parts. -/
lemma rcRO_row (a : X × U) :
    rcRO P κ a = dist (prodDist (P a.1) (κ a.2)) fun w => ((w.1.1, w.2), w.1.2) := by
  classical
  funext o
  simp only [dist]
  rw [sum_eq_single ((o.1.1, o.2), o.1.2)]
  · simp [rcRO, prodDist]
  · intro w _ hw
    refine ite_eq_right fun h => hw ?_
    rw [← h]
  · simp

omit [Fintype V] in
/-- **The broadcast cut**: `I(X; Y, Y₁ | X₁) ≤ I(X; Y', Y₁)`. -/
theorem rcBcInfo_ro_le (hq : IsPMF q) (hP : IsChannel P) (hκ : IsChannel κ) :
    rcBcInfo q (rcRO P κ) ≤ mutualInfoOf (dist q Prod.fst) P := by
  classical
  have hW := rcRO_isChannel hP hκ
  have hJ := jointOf_isPMF hq hW
  rw [rcBcInfo_eq hq hW, mutualInfoOf_eq (hq.dist _) hP]
  set J := jointOf q (rcRO P κ) with hJd
  let Uu : (X × U) × ((Y' × Y'') × S) → U := fun z => z.1.2
  let Aa : (X × U) × ((Y' × Y'') × S) → Y' × S := fun z => (z.2.1.1, z.2.2)
  let Bb : (X × U) × ((Y' × Y'') × S) → Y'' := fun z => z.2.1.2
  -- the chain rule
  have h₁ : H[Prod.snd | Uu ; J] = H[pair Aa Bb | Uu ; J] := by
    rw [condEntropy_eq_sub hJ, condEntropy_eq_sub hJ]
    congr 1
    exact entropyRV_eq_of_injective _
      (fun t : U × ((Y' × S) × Y'') => (t.1, ((t.2.1.1, t.2.2), t.2.1.2)))
      (fun a b h => by
        simp only [Prod.ext_iff] at h ⊢
        tauto) fun _ => rfl
  have h₂ := chain_rule_cond hJ Aa Bb Uu
  have h₃ := condEntropy_le_condEntropy hJ Bb Aa Uu
  have h₄ := condEntropy_le_entropy hJ Aa Uu
  -- the law of `(Y', Y₁)`
  have hrow : ∀ a : X × U, dist (rcRO P κ a) (fun o => (o.1.1, o.2)) = P a.1 := by
    intro a
    rw [rcRO_row, ← dist_comp_eq]
    exact dist_prodDist_fst (hκ _) _
  have hrow₂ : ∀ a : X × U, dist (rcRO P κ a) (fun o => o.1.2) = κ a.2 := by
    intro a
    rw [rcRO_row, ← dist_comp_eq]
    exact dist_prodDist_snd (hP _) _
  have hA : dist J Aa = outDist (dist q Prod.fst) P := by
    funext t
    rw [outDist_dist_comp, hJd, dist_jointOf_row]
    refine sum_congr rfl fun a _ => ?_
    rw [show (fun o => Aa (a, o)) = fun o => (o.1.1, o.2) from rfl, hrow]
  -- the entropy of `Y''` given `X₁`
  have hB : H[Bb | Uu ; J] = ∑ u, dist q Prod.snd u * entropy (κ u) := by
    have hd : dist J (pair Uu Bb) =
      dist (jointOf (dist q Prod.snd) κ) (pair Prod.fst Prod.snd) := by
      funext ⟨u, y⟩
      rw [dist_pair_fst_snd, hJd, dist_jointOf_row]
      have hin : ∀ a : X × U, dist (rcRO P κ a) (fun o => pair Uu Bb (a, o)) (u, y) =
          (if a.2 = u then 1 else 0) * κ u y := by
        intro a
        by_cases ha : a.2 = u
        · subst ha
          have e : (fun o : (Y' × Y'') × S => pair Uu Bb (a, o)) =
              (fun b : Y'' => (a.2, b)) ∘ fun o => o.1.2 := rfl
          rw [e, dist_comp_of_injective _ _ (fun b b' h => (Prod.ext_iff.mp h).2), hrow₂]
          simp
        · rw [ite_eq_right ha, zero_mul]
          simp only [dist]
          refine sum_eq_zero fun o _ => ite_eq_right fun h => absurd (Prod.ext_iff.mp h).1 ha
      simp_rw [hin]
      simp only [jointOf, dist, mul_ite, ite_mul, mul_zero, zero_mul]
      rw [sum_mul]
      refine sum_congr rfl fun a _ => ?_
      by_cases ha : a.2 = u <;> simp [ha]
    rw [condEntropy_eq_of_dist_pair_eq hJ (jointOf_isPMF (hq.dist _) hκ) hd,
      condEntropy_jointOf (hq.dist _) hκ]
  -- the entropy of a row
  have hE : ∀ a : X × U, entropy (rcRO P κ a) = entropy (P a.1) + entropy (κ a.2) := by
    intro a
    have h := entropyRV_comp_injective (prodDist (P a.1) (κ a.2)) id
      (f := fun w : (Y' × S) × Y'' => ((w.1.1, w.2), w.1.2)) (fun x y h => by
        simp only [Prod.ext_iff] at h ⊢
        tauto)
    rw [rcRO_row, ← entropy_prodDist (hP _) (hκ _)]
    have e₁ : H[id ; prodDist (P a.1) (κ a.2)] = entropy (prodDist (P a.1) (κ a.2)) := by
      simp only [entropyRV, dist_id]
    rw [← e₁, ← h]
    rfl
  have hsum : ∑ a, q a * entropy (rcRO P κ a) =
      ∑ x, dist q Prod.fst x * entropy (P x) + ∑ u, dist q Prod.snd u * entropy (κ u) := by
    rw [sum_dist_mul, sum_dist_mul, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [hE]
    ring
  have hAe : H[Aa ; J] = entropy (outDist (dist q Prod.fst) P) := by
    rw [entropyRV, hA]
  rw [hsum, h₁, h₂, ← hAe, ← hB]
  linarith

end Bound

/-! ### The bound of the notes, and the semi-deterministic case -/

section Semi

/-- **Page 17-50 of [elgamal2010].** The cutset bound for orthogonal receiver components:
`max_{p(x)} min {I(X; Y') + C₀, I(X; Y', Y₁)}`, in nats. -/
def rcROBound (P : X → Y' × S → ℝ) (κ : U → Y'' → ℝ) : ℝ :=
  sSup {v | ∃ p : X → ℝ, IsPMF p ∧ v = min (mutualInfoOf p (bcMarg₁ P) + capacity κ)
    (mutualInfoOf p P)}

omit [Fintype V] in
lemma bddAbove_rcRO (hP : IsChannel P) :
    BddAbove {v | ∃ p : X → ℝ, IsPMF p ∧ v = min (mutualInfoOf p (bcMarg₁ P) + capacity κ)
      (mutualInfoOf p P)} := by
  refine ⟨capacity P, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (min_le_right _ _).trans (mutualInfoOf_le_capacity hp hP)

omit [Fintype V] in
/-- **Page 17-50 of [elgamal2010].** The cutset bound for orthogonal receiver components. -/
theorem rcCutsetBound_ro_le [Nonempty X] [Nonempty U] (hP : IsChannel P) (hκ : IsChannel κ) :
    rcCutsetBound (rcRO P κ) ≤ rcROBound P κ := by
  refine csSup_le ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩ ?_
  rintro _ ⟨q, hq, rfl⟩
  refine le_trans ?_ (le_csSup (bddAbove_rcRO hP) ⟨dist q Prod.fst, hq.dist _, rfl⟩)
  refine min_le_min ((rcMacInfo_ro_le hq hP hκ).trans ?_) (rcBcInfo_ro_le hq hP hκ)
  exact add_le_add le_rfl (mutualInfoOf_le_capacity (hq.dist _) hκ)

/-- `Y₁` is a function of `(X, Y')`. -/
def IsSemiDetRO (P : X → Y' × S → ℝ) (f : X × Y' → S) : Prop :=
  ∀ x y' s, P x (y', s) ≠ 0 → s = f (x, y')

/-- The channel with `Ŷ₁ = Y₁`. -/
def roIdC (S : Type*) [DecidableEq S] (s v : S) : ℝ := if v = s then 1 else 0

lemma roIdC_isChannel [DecidableEq S] : IsChannel (roIdC S) := fun s => by
  refine ⟨fun v => ?_, ?_⟩
  · simp only [roIdC]
    split_ifs <;> norm_num
  · simp [roIdC]

/-- **Page 17-51 of [elgamal2010]: the receiver-orthogonal semi-deterministic relay channel.** If
`Y₁` is a function of `(X, Y')`, then compress–forward with `Ŷ₁ = Y₁` achieves the cutset bound. -/
theorem rcCapacity_ro_semiDet [Nonempty X] [Nonempty U] [Nonempty Y'] [Nonempty Y''] [Nonempty S]
    {f : X × Y' → S} (hf : IsSemiDetRO P f) (hP : IsChannel P) (hκ : IsChannel κ) :
    rcCapacity (rcRO P κ) = rcROBound P κ / log 2 := by
  classical
  have hW := rcRO_isChannel hP hκ
  refine rcCapacity_eq (fun R hR => ?_) fun R hR =>
    (hR.le_rcCutsetBound hW).trans (rcCutsetBound_ro_le hP hκ)
  have hR₀ : R * log 2 < sSup {v | ∃ p : X → ℝ, IsPMF p ∧ v =
      min (mutualInfoOf p (bcMarg₁ P) + capacity κ) (mutualInfoOf p P)} := hR
  have hne : Set.Nonempty {v | ∃ p : X → ℝ, IsPMF p ∧ v =
      min (mutualInfoOf p (bcMarg₁ P) + capacity κ) (mutualInfoOf p P)} :=
    ⟨_, ⟨uniformPMF X, uniformPMF_isPMF, rfl⟩⟩
  obtain ⟨_, ⟨p, hp, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hR₀
  obtain ⟨p₁, hp₁, hcap⟩ := exists_capacity_eq hκ
  have hν := roν₁_isPMF hp hP (roIdC_isChannel (S := S))
  set ν := roν₁ p P (roIdC S) with hνd
  have hsupp : ∀ z, ν z ≠ 0 → z.1.2.2 = f (z.1.1, z.1.2.1) ∧ z.2 = z.1.2.2 := by
    rintro ⟨⟨x, y', s⟩, v⟩ hz
    simp only [hνd, roν₁, jointOf, roIdC] at hz
    refine ⟨hf x y' s ?_, ?_⟩
    · intro h0
      simp [h0] at hz
    · by_contra hc
      simp [hc] at hz
  have hfst : dist ν Prod.fst = jointOf p P := dist_jointOf_fst fun _ => roIdC_isChannel _
  -- the first information
  have h₁ : I[fun z => z.1.1 : fun z => z.1.2.1 ; ν] = mutualInfoOf p (bcMarg₁ P) := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    funext ⟨x, y⟩
    rw [dist_pair_fst_snd]
    have e : (pair (fun z : (X × (Y' × S)) × S => z.1.1) fun z => z.1.2.1) =
        (pair (Prod.fst : X × (Y' × S) → X) fun z => (Prod.snd z).1) ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, hfst, dist_pair_marg_fst]
    simp_rw [dist_pair_fst_snd]
    simp only [jointOf, bcMarg₁, mul_sum]
  -- the third information
  have h₃ : I[fun z => z.1.1 : fun z => (z.1.2.1, z.2) ; ν] = mutualInfoOf p P := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    have hae : dist ν (pair (fun z => z.1.1) fun z => (z.1.2.1, z.2)) =
        dist ν (pair (fun z => z.1.1) fun z => z.1.2) :=
      dist_congr_of_ae fun z hz => by
        simp only [pair]
        rw [(hsupp z hz).2]
    rw [hae]
    have e : (pair (fun z : (X × (Y' × S)) × S => z.1.1) fun z => z.1.2) =
        (pair Prod.fst Prod.snd) ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, hfst]
  -- the second information
  have h₂ : I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ; ν] = 0 := by
    rw [condMutualInfo_eq_entropies hν]
    have hH : ∀ {T : Type _} [Fintype T] (g : (X × (Y' × S)) × S → T) (j : X × Y' → T),
        Function.Injective j → (∀ z, ν z ≠ 0 → g z = j (z.1.1, z.1.2.1)) →
        H[g ; ν] = H[fun z => (z.1.1, z.1.2.1) ; ν] := by
      intro T _ g j hj h
      rw [entropyRV, dist_congr_of_ae h]
      exact entropyRV_eq_of_injective _ j hj fun _ => rfl
    have hinj : Function.Injective fun c : X × Y' => (c, f c) :=
      fun a b h => (Prod.ext_iff.mp h).1
    have hinj₂ : Function.Injective fun c : X × Y' => ((c, f c), f c) :=
      fun a b h => (Prod.ext_iff.mp (Prod.ext_iff.mp h).1).1
    have e₁ := hH (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.1.2.2) (fun c => (c, f c)) hinj
      fun z hz => by
        simp only [pair]
        rw [(hsupp z hz).1]
    have e₂ := hH (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2) (fun c => (c, f c)) hinj
      fun z hz => by
        simp only [pair]
        rw [(hsupp z hz).2, (hsupp z hz).1]
    have e₃ := hH (pair (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2) fun z => z.1.2.2)
      (fun c => ((c, f c), f c)) hinj₂ fun z hz => by
        simp only [pair]
        rw [(hsupp z hz).2, (hsupp z hz).1]
    rw [e₁, e₂, e₃]
    ring
  have hR' := lt_min_iff.mp hlt
  refine isAchievableRC_ro (V := S) (τ' := roIdC S) hp hp₁ hP hκ roIdC_isChannel ?_ ?_
  · rw [h₁, h₂, hcap, sub_zero]
    exact hR'.1
  · rw [h₃]
    exact hR'.2

end Semi

end InfoTheory
