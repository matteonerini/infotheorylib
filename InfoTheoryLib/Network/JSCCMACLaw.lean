/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Product
public import InfoTheoryLib.Network.JSCCRandomCode

/-!
# Joint source–channel coding over a MAC: the law and the entropies

This file defines the law `p(u₁, u₂) p(w) p(x₁|u₁, w) p(x₂|u₂, w) p(y|x₁, x₂)` of the coding scheme
of Theorem 2 of Lecture 15 of El Gamal and Kim, and computes the entropies that appear in the
exponents of the error events.

## Main definitions

* `JZ`: the alphabet of all the random variables, and `jU₁`, `jU₂`, `jW`, `jX₁`, `jX₂`, `jY`.
* `jsLaw P τ κ₁ κ₂ W`: the law.

## Main statements

* `entropy_jsLaw`: `H(all) = H(U₁, U₂) + H(W) + H(X₁|U₁, W) + H(X₂|U₂, W) + H(Y|X₁, X₂)`.
* `jsGap_a`, `jsGap_b`, `jsGap_c`, `jsGap_d`: the exponents of the four error events.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- The alphabet of `(((((U₁, U₂), W), X₁), X₂), Y)`. -/
abbrev JZ (α₁ α₂ ω ξ₁ ξ₂ β : Type*) : Type _ := ((((α₁ × α₂) × ω) × ξ₁) × ξ₂) × β

variable {α₁ α₂ ω ξ₁ ξ₂ β : Type*}

/-- The source `U₁`. -/
abbrev jU₁ (z : JZ α₁ α₂ ω ξ₁ ξ₂ β) : α₁ := z.1.1.1.1.1
/-- The source `U₂`. -/
abbrev jU₂ (z : JZ α₁ α₂ ω ξ₁ ξ₂ β) : α₂ := z.1.1.1.1.2
/-- The auxiliary random variable `W`. -/
abbrev jW (z : JZ α₁ α₂ ω ξ₁ ξ₂ β) : ω := z.1.1.1.2
/-- The input `X₁`. -/
abbrev jX₁ (z : JZ α₁ α₂ ω ξ₁ ξ₂ β) : ξ₁ := z.1.1.2
/-- The input `X₂`. -/
abbrev jX₂ (z : JZ α₁ α₂ ω ξ₁ ξ₂ β) : ξ₂ := z.1.2
/-- The output `Y`. -/
abbrev jY (z : JZ α₁ α₂ ω ξ₁ ξ₂ β) : β := z.2

variable [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂] [Fintype β]

/-- The law of `((((U₁, U₂), W), X₁)`. -/
def jsL₁ (P : α₁ × α₂ → ℝ) (τ : ω → ℝ) (κ₁ : α₁ × ω → ξ₁ → ℝ) : ((α₁ × α₂) × ω) × ξ₁ → ℝ :=
  jointOf (prodDist P τ) fun v => κ₁ (v.1.1, v.2)

/-- The law of `(((((U₁, U₂), W), X₁), X₂)`. -/
def jsL₂ (P : α₁ × α₂ → ℝ) (τ : ω → ℝ) (κ₁ : α₁ × ω → ξ₁ → ℝ) (κ₂ : α₂ × ω → ξ₂ → ℝ) :
    (((α₁ × α₂) × ω) × ξ₁) × ξ₂ → ℝ :=
  jointOf (jsL₁ P τ κ₁) fun v => κ₂ (v.1.1.2, v.1.2)

/-- **Lecture 15 of [elgamal2010], page 15-16.** The law
`p(u₁, u₂) p(w) p(x₁|u₁, w) p(x₂|u₂, w) p(y|x₁, x₂)`. -/
def jsLaw (P : α₁ × α₂ → ℝ) (τ : ω → ℝ) (κ₁ : α₁ × ω → ξ₁ → ℝ) (κ₂ : α₂ × ω → ξ₂ → ℝ)
    (W : ξ₁ × ξ₂ → β → ℝ) : JZ α₁ α₂ ω ξ₁ ξ₂ β → ℝ :=
  jointOf (jsL₂ P τ κ₁ κ₂) fun v => W (v.1.2, v.2)

variable {P : α₁ × α₂ → ℝ} {τ : ω → ℝ} {κ₁ : α₁ × ω → ξ₁ → ℝ} {κ₂ : α₂ × ω → ξ₂ → ℝ}
  {W : ξ₁ × ξ₂ → β → ℝ}

section Law

variable (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (hW : IsChannel W)

include hP hτ h₁ in
lemma jsL₁_isPMF : IsPMF (jsL₁ P τ κ₁) := jointOf_isPMF (hP.prodDist hτ) fun _ => h₁ _

include hP hτ h₁ h₂ in
lemma jsL₂_isPMF : IsPMF (jsL₂ P τ κ₁ κ₂) := jointOf_isPMF (jsL₁_isPMF hP hτ h₁) fun _ => h₂ _

include hP hτ h₁ h₂ hW in
lemma jsLaw_isPMF : IsPMF (jsLaw P τ κ₁ κ₂ W) := jointOf_isPMF (jsL₂_isPMF hP hτ h₁ h₂) fun _ => hW
  _

include hW in
omit [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂] in
lemma dist_fst_jsLaw [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂] :
    dist (jsLaw P τ κ₁ κ₂ W) Prod.fst = jsL₂ P τ κ₁ κ₂ := dist_jointOf_fst fun _ => hW _

include h₂ in
lemma dist_fst_jsL₂ : dist (jsL₂ P τ κ₁ κ₂) Prod.fst = jsL₁ P τ κ₁ := dist_jointOf_fst fun _ => h₂ _

include h₁ in
lemma dist_fst_jsL₁ : dist (jsL₁ P τ κ₁) Prod.fst = prodDist P τ := dist_jointOf_fst fun _ => h₁ _

include hW h₂ h₁ in
/-- A function of `((U₁, U₂), W)` under the law. -/
lemma dist_jsLaw_comp₀ {T : Type*} (f : (α₁ × α₂) × ω → T) :
    dist (jsLaw P τ κ₁ κ₂ W) (fun z => f z.1.1.1) = dist (prodDist P τ) f := by
  have e : (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => f z.1.1.1) =
      f ∘ Prod.fst ∘ Prod.fst ∘ Prod.fst := rfl
  rw [e, dist_comp_eq, dist_comp_eq, dist_comp_eq, dist_fst_jsLaw hW, dist_fst_jsL₂ h₂,
    dist_fst_jsL₁ h₁]

omit [Fintype ξ₁] [Fintype ξ₂] [Fintype β] in
/-- The law of a function of `(U₁, U₂)` and `W`: they are independent. -/
lemma dist_prodDist_map_fst {T : Type*} (f : α₁ × α₂ → T) :
    dist (prodDist P τ) (fun v => (f v.1, v.2)) = prodDist (dist P f) τ := by
  classical
  funext ⟨t, w⟩
  simp only [dist, prodDist, Prod.mk.injEq, Fintype.sum_prod_type (f := fun v : (α₁ × α₂) × ω => _)]
  have : ∀ z : α₁ × α₂, ∑ y, (if f z = t ∧ y = w then P z * τ y else 0) =
      (if f z = t then P z else 0) * τ w := fun z => by
    rw [sum_eq_single w]
    · by_cases h : f z = t <;> simp [h]
    · intro y _ hy
      simp [hy]
    · simp
  simp only [this, sum_mul]

end Law

/-! ### The conditional laws -/

section Cond

variable (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (hW : IsChannel W)

include h₂ hW in
/-- The law of `((U₁, W), X₁)`. -/
lemma dist_jsLaw_κ₁ :
    dist (jsLaw P τ κ₁ κ₂ W) (pair (pair jU₁ jW) jX₁) =
      jointOf (dist (prodDist P τ) fun v => (v.1.1, v.2)) κ₁ := by
  have e : pair (pair jU₁ jW) jX₁ = (fun z : ((α₁ × α₂) × ω) × ξ₁ => ((z.1.1.1, z.1.2), z.2)) ∘
      Prod.fst ∘ (Prod.fst : JZ α₁ α₂ ω ξ₁ ξ₂ β → _) := rfl
  rw [e, dist_comp_eq, dist_comp_eq, dist_fst_jsLaw hW, dist_fst_jsL₂ h₂]
  exact dist_jointOf_map (Q := prodDist P τ) (fun v => (v.1.1, v.2)) κ₁

include hW in
/-- The law of `((U₂, W), X₂)`. -/
lemma dist_jsLaw_κ₂ :
    dist (jsLaw P τ κ₁ κ₂ W) (pair (pair jU₂ jW) jX₂) =
      jointOf (dist (jsL₁ P τ κ₁) fun v => (v.1.1.2, v.1.2)) κ₂ := by
  have e : pair (pair jU₂ jW) jX₂ =
      (fun z : (((α₁ × α₂) × ω) × ξ₁) × ξ₂ => ((z.1.1.1.2, z.1.1.2), z.2)) ∘
      (Prod.fst : JZ α₁ α₂ ω ξ₁ ξ₂ β → _) := rfl
  rw [e, dist_comp_eq, dist_fst_jsLaw hW]
  exact dist_jointOf_map (Q := jsL₁ P τ κ₁) (fun v => (v.1.1.2, v.1.2)) κ₂

/-- The conditional pmf of a channel, where the condition has positive probability. -/
lemma condDist_eq_of_dist_pair {Ω A' B' : Type*} [Fintype Ω] {μ : Ω → ℝ}
    {X : Ω → A'} {Y : Ω → B'} {Q : A' → ℝ} {κ : A' → B' → ℝ}
    (h : dist μ (pair X Y) = jointOf Q κ) (hQ : Q = dist μ X) {a : A'} (ha : dist μ X a ≠ 0)
    (b : B') : condDist μ Y X a b = κ a b := by
  rw [condDist, h]
  simp only [jointOf, ← hQ]
  rw [hQ]
  field_simp

omit hW in
/-- The law of `((X₁, X₂), Y)`. -/
lemma dist_jsLaw_W :
    dist (jsLaw P τ κ₁ κ₂ W) (pair (pair jX₁ jX₂) jY) =
      jointOf (dist (jsL₂ P τ κ₁ κ₂) fun v => (v.1.2, v.2)) W :=
  dist_jointOf_map (Q := jsL₂ P τ κ₁ κ₂) (fun v => (v.1.2, v.2)) W

end Cond

/-! ### The entropies -/

section Entropy

variable (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (hW : IsChannel W)

/-- `H(X₁|U₁, W)`. -/
abbrev jsH₁ (P : α₁ × α₂ → ℝ) (τ : ω → ℝ) (κ₁ : α₁ × ω → ξ₁ → ℝ) (κ₂ : α₂ × ω → ξ₂ → ℝ)
    (W : ξ₁ × ξ₂ → β → ℝ) : ℝ :=
  H[jX₁ | pair jU₁ jW ; jsLaw P τ κ₁ κ₂ W]

/-- `H(X₂|U₂, W)`. -/
abbrev jsH₂ (P : α₁ × α₂ → ℝ) (τ : ω → ℝ) (κ₁ : α₁ × ω → ξ₁ → ℝ) (κ₂ : α₂ × ω → ξ₂ → ℝ)
    (W : ξ₁ × ξ₂ → β → ℝ) : ℝ :=
  H[jX₂ | pair jU₂ jW ; jsLaw P τ κ₁ κ₂ W]

/-- `H(Y|X₁, X₂)`. -/
abbrev jsHY (P : α₁ × α₂ → ℝ) (τ : ω → ℝ) (κ₁ : α₁ × ω → ξ₁ → ℝ) (κ₂ : α₂ × ω → ξ₂ → ℝ)
    (W : ξ₁ × ξ₂ → β → ℝ) : ℝ :=
  H[jY | pair jX₁ jX₂ ; jsLaw P τ κ₁ κ₂ W]

/-- The conditional entropy of the second component of `jointOf Q (κ ∘ g)` given the first one only
depends on `g`. -/
lemma condEntropy_jointOf_comp {A B C' : Type*} [Fintype A] [Fintype B] [Fintype C'] {Q : A → ℝ}
    (hQ : IsPMF Q) {κ : B → C' → ℝ} (hκ : IsChannel κ) (g : A → B) :
    H[Prod.snd | Prod.fst ; jointOf Q fun a => κ (g a)] =
      H[Prod.snd | g ∘ Prod.fst ; jointOf Q fun a => κ (g a)] := by
  have hc : IsChannel fun a => κ (g a) := fun a => hκ (g a)
  refine condEntropy_eq_comp_of_channel (jointOf_isPMF hQ hc) Prod.fst Prod.snd g hκ ?_
  rw [dist_pair_fst_snd, dist_jointOf_fst hc]

/-- The entropy of a joint law, by the chain rule. -/
lemma entropy_jointOf_eq {A B : Type*} [Fintype A] [Fintype B] {Q : A → ℝ} (hQ : IsPMF Q)
    {κ : A → B → ℝ} (hκ : IsChannel κ) :
    entropy (jointOf Q κ) = entropy Q + H[Prod.snd | Prod.fst ; jointOf Q κ] := by
  have hμ := jointOf_isPMF hQ hκ
  have h := chain_rule hμ (Prod.fst : A × B → A) (Prod.snd : A × B → B)
  have e : pair (Prod.fst : A × B → A) Prod.snd = id := rfl
  rw [e, entropyRV, dist_id, entropyRV, dist_jointOf_fst hκ] at h
  exact h

include hP hτ h₁ h₂ hW

lemma condEntropy_snd_jsL₁ :
    H[Prod.snd | Prod.fst ; jsL₁ P τ κ₁] = jsH₁ P τ κ₁ κ₂ W := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have h := condEntropy_jointOf_comp (hP.prodDist hτ) h₁ (fun v : (α₁ × α₂) × ω => (v.1.1, v.2))
  refine h.trans ?_
  have e := condEntropy_comp_comp hL
    (Prod.fst ∘ (Prod.fst : JZ α₁ α₂ ω ξ₁ ξ₂ β → _)) (Prod.snd : ((α₁ × α₂) × ω) × ξ₁ → ξ₁)
    ((fun v : (α₁ × α₂) × ω => (v.1.1, v.2)) ∘ Prod.fst)
  rw [dist_comp_eq, dist_fst_jsLaw hW, dist_fst_jsL₂ h₂] at e
  exact e.symm

lemma condEntropy_snd_jsL₂ :
    H[Prod.snd | Prod.fst ; jsL₂ P τ κ₁ κ₂] = jsH₂ P τ κ₁ κ₂ W := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have h := condEntropy_jointOf_comp (jsL₁_isPMF hP hτ h₁) h₂
    (fun v : ((α₁ × α₂) × ω) × ξ₁ => (v.1.1.2, v.1.2))
  refine h.trans ?_
  have e := condEntropy_comp_comp hL
    (Prod.fst : JZ α₁ α₂ ω ξ₁ ξ₂ β → _) (Prod.snd : (((α₁ × α₂) × ω) × ξ₁) × ξ₂ → ξ₂)
    ((fun v : ((α₁ × α₂) × ω) × ξ₁ => (v.1.1.2, v.1.2)) ∘ Prod.fst)
  rw [dist_fst_jsLaw hW] at e
  exact e.symm

lemma condEntropy_snd_jsLaw :
    H[jY | Prod.fst ; jsLaw P τ κ₁ κ₂ W] = jsHY P τ κ₁ κ₂ W :=
  condEntropy_jointOf_comp (jsL₂_isPMF hP hτ h₁ h₂) hW
    (fun v : (((α₁ × α₂) × ω) × ξ₁) × ξ₂ => (v.1.2, v.2))

/-- `H(Y|A) = H(Y|X₁, X₂)` for any `A` that determines `(X₁, X₂)` and is determined by
`(U₁, U₂, W, X₁, X₂)`. -/
lemma condEntropy_jY_eq {T : Type*} [Fintype T] (A : JZ α₁ α₂ ω ξ₁ ξ₂ β → T) (f : T → ξ₁ × ξ₂)
    (hf : ∀ z, f (A z) = (jX₁ z, jX₂ z)) (g : (((α₁ × α₂) × ω) × ξ₁) × ξ₂ → T)
    (hg : ∀ z, A z = g z.1) : H[jY | A ; jsLaw P τ κ₁ κ₂ W] = jsHY P τ κ₁ κ₂ W := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have h0 := condEntropy_snd_jsLaw hP hτ h₁ h₂ hW
  have e₁ : (pair jX₁ jX₂ : JZ α₁ α₂ ω ξ₁ ξ₂ β → _) = f ∘ A := funext fun z => (hf z).symm
  have e₂ : A = g ∘ Prod.fst := funext hg
  have l1 := condEntropy_le_condEntropy_comp hL jY A f
  have l2 := condEntropy_le_condEntropy_comp hL jY Prod.fst g
  rw [← e₁] at l1
  rw [← e₂, h0] at l2
  exact le_antisymm l1 l2

/-- **The entropy of all the random variables**. -/
theorem entropy_jsLaw :
    entropy (jsLaw P τ κ₁ κ₂ W) = entropy P + entropy τ + jsH₁ P τ κ₁ κ₂ W + jsH₂ P τ κ₁ κ₂ W +
      jsHY P τ κ₁ κ₂ W := by
  have a3 := entropy_jointOf_eq (jsL₂_isPMF hP hτ h₁ h₂) (κ := fun v => W (v.1.2, v.2))
    fun _ => hW _
  have a2 := entropy_jointOf_eq (jsL₁_isPMF hP hτ h₁) (κ := fun v => κ₂ (v.1.1.2, v.1.2))
    fun _ => h₂ _
  have a1 := entropy_jointOf_eq (hP.prodDist hτ) (κ := fun v => κ₁ (v.1.1, v.2)) fun _ => h₁ _
  have a0 := entropy_prodDist hP hτ
  have b1 := condEntropy_snd_jsL₁ hP hτ h₁ h₂ hW
  have b2 := condEntropy_snd_jsL₂ hP hτ h₁ h₂ hW
  have b3 := condEntropy_snd_jsLaw hP hτ h₁ h₂ hW
  have e1 : entropy (jsL₁ P τ κ₁) = entropy (prodDist P τ) + jsH₁ P τ κ₁ κ₂ W := by
    rw [← b1]
    exact a1
  have e2 : entropy (jsL₂ P τ κ₁ κ₂) = entropy (jsL₁ P τ κ₁) + jsH₂ P τ κ₁ κ₂ W := by
    rw [← b2]
    exact a2
  have e3 : entropy (jsLaw P τ κ₁ κ₂ W) = entropy (jsL₂ P τ κ₁ κ₂) + jsHY P τ κ₁ κ₂ W := by
    rw [← b3]
    exact a3
  linarith

/-- The entropy of a function of `(U₁, U₂)` together with `W`. -/
lemma entropy_pair_jW {T : Type*} [Fintype T] (f : α₁ × α₂ → T) :
    H[pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => f z.1.1.1.1) jW ; jsLaw P τ κ₁ κ₂ W] =
      H[f ; P] + entropy τ := by
  have e := dist_jsLaw_comp₀ (κ₁ := κ₁) (κ₂ := κ₂) (W := W) (P := P) (τ := τ) h₁ h₂ hW
    (fun v : (α₁ × α₂) × ω => (f v.1, v.2))
  have e' := dist_prodDist_map_fst (P := P) (τ := τ) f
  rw [entropyRV]
  have e'' : dist (jsLaw P τ κ₁ κ₂ W) (pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => f z.1.1.1.1) jW) =
      prodDist (dist P f) τ := e.trans e'
  rw [e'', entropy_prodDist (hP.dist f) hτ]
  rfl

omit hP in
/-- The entropy of a function of `(U₁, U₂)`. -/
lemma entropy_jsLaw_comp {T : Type*} [Fintype T] (f : α₁ × α₂ → T) :
    H[fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => f z.1.1.1.1 ; jsLaw P τ κ₁ κ₂ W] = H[f ; P] := by
  have e := dist_jsLaw_comp₀ (κ₁ := κ₁) (κ₂ := κ₂) (W := W) (P := P) (τ := τ) h₁ h₂ hW
    (fun v : (α₁ × α₂) × ω => f v.1)
  have e' : dist (prodDist P τ) (fun v : (α₁ × α₂) × ω => f v.1) = dist P f := by
    have e₁ : (fun v : (α₁ × α₂) × ω => f v.1) = f ∘ Prod.fst := rfl
    rw [e₁, dist_comp_eq, show dist (prodDist P τ) Prod.fst = P from ?_]
    funext a
    rw [dist_fst]
    simp [prodDist, ← mul_sum, hτ.sum_eq_one]
  rw [entropyRV, entropyRV, e, e']

/-- **The exponent of a wrong first source sequence.** -/
theorem jsGap_a :
    entropy (jsLaw P τ κ₁ κ₂ W) - H[pair (pair (pair jU₂ jW) jX₂) jY ; jsLaw P τ κ₁ κ₂ W] -
        jsH₁ P τ κ₁ κ₂ W =
      H[jU₁ | jU₂ ; jsLaw P τ κ₁ κ₂ W] -
        I[jX₁ : jY | pair jX₂ (pair jU₂ jW) ; jsLaw P τ κ₁ κ₂ W] := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have hE := entropy_jsLaw hP hτ h₁ h₂ hW
  -- The entropy of the visible variables.
  have c1 := chain_rule hL (pair (pair jU₂ jW) jX₂) jY
  have c2 := chain_rule hL (pair jU₂ jW) jX₂
  have c3 := entropy_pair_jW hP hτ h₁ h₂ hW (Prod.snd : α₁ × α₂ → α₂)
  have c4 : H[pair jU₂ jW ; jsLaw P τ κ₁ κ₂ W] = H[Prod.snd ; P] + entropy τ := c3
  -- The conditional entropy of the sources.
  have d1 := condEntropy_eq_sub hL jU₁ jU₂
  have d2 : H[pair jU₂ jU₁ ; jsLaw P τ κ₁ κ₂ W] = entropy P := by
    have e := entropy_jsLaw_comp (P := P) hτ h₁ h₂ hW (fun z : α₁ × α₂ => (z.2, z.1))
    have e' : H[fun z : α₁ × α₂ => (z.2, z.1) ; P] = entropy P := by
      rw [show entropy P = H[id ; P] by rw [entropyRV, dist_id]]
      exact entropyRV_eq_of_injective P (fun z : α₁ × α₂ => (z.2, z.1))
        (fun a b h => by
          obtain ⟨a1, a2⟩ := a
          obtain ⟨b1, b2⟩ := b
          simp only [Prod.mk.injEq] at h ⊢
          tauto) (fun _ => rfl)
    exact e.trans e'
  have d3 := entropy_jsLaw_comp (P := P) hτ h₁ h₂ hW (Prod.snd : α₁ × α₂ → α₂)
  have d4 : H[jU₂ ; jsLaw P τ κ₁ κ₂ W] = H[Prod.snd ; P] := d3
  -- The mutual information.
  have i1 : I[jX₁ : jY | pair jX₂ (pair jU₂ jW) ; jsLaw P τ κ₁ κ₂ W] =
      H[jY | pair (pair jU₂ jW) jX₂ ; jsLaw P τ κ₁ κ₂ W] - jsHY P τ κ₁ κ₂ W := by
    rw [condMutualInfo_comm hL, condMutualInfo]
    have e1 : H[jY | pair jX₂ (pair jU₂ jW) ; jsLaw P τ κ₁ κ₂ W] =
        H[jY | pair (pair jU₂ jW) jX₂ ; jsLaw P τ κ₁ κ₂ W] :=
      condEntropy_congr_right hL jY Prod.swap Prod.swap_injective fun _ => rfl
    have e2 := condEntropy_jY_eq hP hτ h₁ h₂ hW
      (pair jX₁ (pair jX₂ (pair jU₂ jW))) (fun t => (t.1, t.2.1)) (fun _ => rfl)
      (fun v => (v.1.2, v.2, v.1.1.1.2, v.1.1.2)) fun _ => rfl
    rw [e1, e2]
  rw [i1, hE, c1, c2, c4, d1, d2, d4]
  ring

/-- **The exponent of a wrong second source sequence.** -/
theorem jsGap_b :
    entropy (jsLaw P τ κ₁ κ₂ W) - H[pair (pair (pair jU₁ jW) jX₁) jY ; jsLaw P τ κ₁ κ₂ W] -
        jsH₂ P τ κ₁ κ₂ W =
      H[jU₂ | jU₁ ; jsLaw P τ κ₁ κ₂ W] -
        I[jX₂ : jY | pair jX₁ (pair jU₁ jW) ; jsLaw P τ κ₁ κ₂ W] := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have hE := entropy_jsLaw hP hτ h₁ h₂ hW
  have c1 := chain_rule hL (pair (pair jU₁ jW) jX₁) jY
  have c2 := chain_rule hL (pair jU₁ jW) jX₁
  have c3 := entropy_pair_jW hP hτ h₁ h₂ hW (Prod.fst : α₁ × α₂ → α₁)
  have c4 : H[pair jU₁ jW ; jsLaw P τ κ₁ κ₂ W] = H[Prod.fst ; P] + entropy τ := c3
  have d1 := condEntropy_eq_sub hL jU₂ jU₁
  have d2 : H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] = entropy P := by
    have e := entropy_jsLaw_comp (P := P) hτ h₁ h₂ hW (id : α₁ × α₂ → α₁ × α₂)
    rw [show entropy P = H[id ; P] by rw [entropyRV, dist_id]]
    exact e
  have d3 := entropy_jsLaw_comp (P := P) hτ h₁ h₂ hW (Prod.fst : α₁ × α₂ → α₁)
  have d4 : H[jU₁ ; jsLaw P τ κ₁ κ₂ W] = H[Prod.fst ; P] := d3
  have i1 : I[jX₂ : jY | pair jX₁ (pair jU₁ jW) ; jsLaw P τ κ₁ κ₂ W] =
      H[jY | pair (pair jU₁ jW) jX₁ ; jsLaw P τ κ₁ κ₂ W] - jsHY P τ κ₁ κ₂ W := by
    rw [condMutualInfo_comm hL, condMutualInfo]
    have e1 : H[jY | pair jX₁ (pair jU₁ jW) ; jsLaw P τ κ₁ κ₂ W] =
        H[jY | pair (pair jU₁ jW) jX₁ ; jsLaw P τ κ₁ κ₂ W] :=
      condEntropy_congr_right hL jY Prod.swap Prod.swap_injective fun _ => rfl
    have e2 := condEntropy_jY_eq hP hτ h₁ h₂ hW
      (pair jX₂ (pair jX₁ (pair jU₁ jW))) (fun t => (t.2.1, t.1)) (fun _ => rfl)
      (fun v => (v.2, v.1.2, v.1.1.1.1, v.1.1.2)) fun _ => rfl
    rw [e1, e2]
  rw [i1, hE, c1, c2, c4, d1, d2, d4]
  ring

/-- **The exponent of two wrong source sequences with the true common part `U₀ = g(U₁, U₂)`.** -/
theorem jsGap_c {T : Type*} [Fintype T] (g : α₁ × α₂ → T) :
    entropy (jsLaw P τ κ₁ κ₂ W) -
        H[pair (pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) jW) jY ; jsLaw P τ κ₁ κ₂ W] -
        jsH₁ P τ κ₁ κ₂ W - jsH₂ P τ κ₁ κ₂ W =
      H[pair jU₁ jU₂ | (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) ; jsLaw P τ κ₁ κ₂ W] -
        I[pair jX₁ jX₂ : jY | pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) jW ;
          jsLaw P τ κ₁ κ₂ W] := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have hE := entropy_jsLaw hP hτ h₁ h₂ hW
  have c1 := chain_rule hL (pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) jW) jY
  have c3 := entropy_pair_jW hP hτ h₁ h₂ hW g
  have d1 := condEntropy_eq_sub hL (pair jU₁ jU₂) (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1)
  have d2 : H[pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) (pair jU₁ jU₂) ;
      jsLaw P τ κ₁ κ₂ W] = entropy P := by
    have e := entropy_jsLaw_comp (P := P) hτ h₁ h₂ hW (fun z : α₁ × α₂ => (g z, z))
    have e' : H[fun z : α₁ × α₂ => (g z, z) ; P] = entropy P := by
      rw [show entropy P = H[id ; P] by rw [entropyRV, dist_id]]
      exact entropyRV_eq_of_injective P (fun z : α₁ × α₂ => (g z, z))
        (fun _ _ h => (Prod.mk.inj h).2) (fun _ => rfl)
    exact e.trans e'
  have d3 := entropy_jsLaw_comp (P := P) hτ h₁ h₂ hW g
  have i1 : I[pair jX₁ jX₂ : jY | pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) jW ;
      jsLaw P τ κ₁ κ₂ W] =
      H[jY | pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) jW ; jsLaw P τ κ₁ κ₂ W] -
        jsHY P τ κ₁ κ₂ W := by
    rw [condMutualInfo_comm hL, condMutualInfo]
    have e2 := condEntropy_jY_eq hP hτ h₁ h₂ hW
      (pair (pair jX₁ jX₂) (pair (fun z : JZ α₁ α₂ ω ξ₁ ξ₂ β => g z.1.1.1.1) jW)) (fun t => t.1)
      (fun _ => rfl) (fun v => ((v.1.2, v.2), g v.1.1.1, v.1.1.2)) fun _ => rfl
    rw [e2]
  rw [i1, hE, c1, c3, d1, d2, d3]
  ring

/-- **The exponent of two wrong source sequences with a wrong common part.** -/
theorem jsGap_d :
    entropy (jsLaw P τ κ₁ κ₂ W) - H[jY ; jsLaw P τ κ₁ κ₂ W] - entropy τ -
        jsH₁ P τ κ₁ κ₂ W - jsH₂ P τ κ₁ κ₂ W =
      H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] - I[pair jX₁ jX₂ : jY ; jsLaw P τ κ₁ κ₂ W] := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have hE := entropy_jsLaw hP hτ h₁ h₂ hW
  have d2 : H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] = entropy P := by
    have e := entropy_jsLaw_comp (P := P) hτ h₁ h₂ hW (id : α₁ × α₂ → α₁ × α₂)
    rw [show entropy P = H[id ; P] by rw [entropyRV, dist_id]]
    exact e
  have i1 : I[pair jX₁ jX₂ : jY ; jsLaw P τ κ₁ κ₂ W] =
      H[jY ; jsLaw P τ κ₁ κ₂ W] - jsHY P τ κ₁ κ₂ W := by
    rw [mutualInfo_comm hL, mutualInfo_eq_entropy_sub_condEntropy hL]
  rw [i1, hE, d2]
  ring

end Entropy

end InfoTheory
