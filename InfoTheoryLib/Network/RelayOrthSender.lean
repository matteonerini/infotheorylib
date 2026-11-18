/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayOrth

/-!
# The relay channel with orthogonal sender components

Page 17-36 of the notes: `X = (X', X'')` and `p(y, y₁ | x, x₁) = p(y | x', x₁) p(y₁ | x'', x₁)`. The
capacity is
`max_{p(x₁) p(x' | x₁) p(x'' | x₁)} min {I(X', X₁; Y), I(X''; Y₁ | X₁) + I(X'; Y | X₁)}`.

## Main definitions

* `rcOS W₁ W₂`: the relay channel with orthogonal sender components.
* `rcOSBound W₁ W₂`: the expression of the capacity.

## Main statements

* `rcCapacity_os`: **the capacity**: partial decode–forward with `U = X''` achieves the cutset
  bound.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X' X'' U Y S : Type*} [Fintype X'] [Fintype X''] [Fintype U] [Fintype Y] [Fintype S]
  {W₁ : X' × U → Y → ℝ} {W₂ : X'' × U → S → ℝ}

/-- **Page 17-36 of [elgamal2010].** The relay channel with orthogonal sender components. -/
def rcOS (W₁ : X' × U → Y → ℝ) (W₂ : X'' × U → S → ℝ) : (X' × X'') × U → Y × S → ℝ :=
  fun a => prodDist (W₁ (a.1.1, a.2)) (W₂ (a.1.2, a.2))

omit [Fintype X'] [Fintype X''] [Fintype U] in
lemma rcOS_isChannel (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂) : IsChannel (rcOS W₁ W₂) :=
  fun _ => (hW₁ _).prodDist (hW₂ _)

/-- `I(X; Y | X₁)` for a law `p(x, x₁)` and a channel `p(y | x, x₁)`. -/
def osCI {A : Type*} (r : A × U → ℝ) (T : A × U → Y → ℝ) [Fintype A] : ℝ :=
  I[fun z : (A × U) × Y => z.1.1 : Prod.snd | fun z => z.1.2 ; jointOf r T]

lemma osCI_eq {A : Type*} [Fintype A] {r : A × U → ℝ} {T : A × U → Y → ℝ} (hr : IsPMF r)
    (hT : IsChannel T) :
    osCI r T = H[Prod.snd | fun z : (A × U) × Y => z.1.2 ; jointOf r T] -
      ∑ a, r a * entropy (T a) := by
  have hμ := jointOf_isPMF hr hT
  rw [osCI, condMutualInfo_comm hμ, condMutualInfo_eq' hμ, ← condEntropy_jointOf hr hT]
  congr 1
  refine condEntropy_congr_right hμ Prod.snd (X := (Prod.fst : (A × U) × Y → A × U))
    (fun t => (t.2, t.1)) (fun a b hab => ?_) fun z => rfl
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext hab.2 hab.1

/-- The law `p(x₁) p(a | x₁)`. -/
def osPair {A : Type*} (p₁ : U → ℝ) (K : U → A → ℝ) : A × U → ℝ := fun t => p₁ t.2 * K t.2 t.1

lemma osPair_isPMF {A : Type*} [Fintype A] {p₁ : U → ℝ} {K : U → A → ℝ} (hp₁ : IsPMF p₁)
    (hK : IsChannel K) : IsPMF (osPair p₁ K) := by
  refine ⟨fun t => mul_nonneg (hp₁.nonneg _) ((hK _).nonneg _), ?_⟩
  simp only [osPair, Fintype.sum_prod_type]
  rw [sum_comm]
  simp_rw [← mul_sum, (hK _).sum_eq_one, mul_one]
  exact hp₁.sum_eq_one

/-- **Page 17-36 of [elgamal2010].** The expression of the capacity, in nats. -/
def rcOSBound (W₁ : X' × U → Y → ℝ) (W₂ : X'' × U → S → ℝ) : ℝ :=
  sSup {v | ∃ (p₁ : U → ℝ) (A : U → X' → ℝ) (B : U → X'' → ℝ), IsPMF p₁ ∧ IsChannel A ∧
    IsChannel B ∧
    v = min (mutualInfoOf (osPair p₁ A) W₁) (osCI (osPair p₁ B) W₂ + osCI (osPair p₁ A) W₁)}

/-! ### The variables -/

section Vars

variable {q : (X' × X'') × U → ℝ}

/-- `(X', X₁)`. -/
def osG₁ (a : (X' × X'') × U) : X' × U := (a.1.1, a.2)

/-- `(X'', X₁)`. -/
def osG₂ (a : (X' × X'') × U) : X'' × U := (a.1.2, a.2)

/-- The law of `(X', X₁, Y)` under the law of the channel. -/
lemma os_dist₁ (hW₂ : IsChannel W₂) :
    dist (jointOf q (rcOS W₁ W₂)) (fun z => (osG₁ z.1, z.2.1)) = jointOf (dist q osG₁) W₁ := by
  classical
  funext ⟨t, y⟩
  rw [dist_jointOf_row]
  have hin : ∀ a : (X' × X'') ×
    U, dist (rcOS W₁ W₂ a) (fun o => (osG₁ (a, o).1, (a, o).2.1)) (t, y) =
      (if osG₁ a = t then 1 else 0) * W₁ t y := by
    intro a
    by_cases ha : osG₁ a = t
    · subst ha
      have e : (fun o : Y × S => (osG₁ (a, o).1, (a, o).2.1)) = (fun b => (osG₁ a, b)) ∘ Prod.fst :=
        rfl
      rw [e, dist_comp_of_injective _ _ (fun b b' h => (Prod.ext_iff.mp h).2)]
      rw [rcOS, dist_prodDist_fst (hW₂ _)]
      simp [osG₁]
    · rw [ite_eq_right ha, zero_mul]
      simp only [dist]
      exact sum_eq_zero fun o _ => ite_eq_right fun h => absurd (Prod.ext_iff.mp h).1 ha
  simp_rw [hin]
  simp only [jointOf, dist, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [sum_mul]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : osG₁ a = t <;> simp [ha]

/-- The law of `(X'', X₁, Y₁)` under the law of the channel. -/
lemma os_dist₂ (hW₁ : IsChannel W₁) :
    dist (jointOf q (rcOS W₁ W₂)) (fun z => (osG₂ z.1, z.2.2)) = jointOf (dist q osG₂) W₂ := by
  classical
  funext ⟨t, y⟩
  rw [dist_jointOf_row]
  have hin : ∀ a : (X' × X'') ×
    U, dist (rcOS W₁ W₂ a) (fun o => (osG₂ (a, o).1, (a, o).2.2)) (t, y) =
      (if osG₂ a = t then 1 else 0) * W₂ t y := by
    intro a
    by_cases ha : osG₂ a = t
    · subst ha
      have e : (fun o : Y × S => (osG₂ (a, o).1, (a, o).2.2)) = (fun b => (osG₂ a, b)) ∘ Prod.snd :=
        rfl
      rw [e, dist_comp_of_injective _ _ (fun b b' h => (Prod.ext_iff.mp h).2)]
      rw [rcOS, dist_prodDist_snd (hW₁ _)]
      simp [osG₂]
    · rw [ite_eq_right ha, zero_mul]
      simp only [dist]
      exact sum_eq_zero fun o _ => ite_eq_right fun h => absurd (Prod.ext_iff.mp h).1 ha
  simp_rw [hin]
  simp only [jointOf, dist, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [sum_mul]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : osG₂ a = t <;> simp [ha]

/-- The multiple access cut: `I(X, X₁; Y) = I(X', X₁; Y)`. -/
lemma rcMacInfo_os (hq : IsPMF q) (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂) :
    rcMacInfo q (rcOS W₁ W₂) = mutualInfoOf (dist q osG₁) W₁ := by
  have hb : bcMarg₁ (rcOS W₁ W₂) = W₁ ∘ osG₁ := by
    funext a y
    simp only [bcMarg₁, rcOS, prodDist, ← mul_sum, (hW₂ _).sum_eq_one, mul_one]
    rfl
  rw [rcMacInfo, hb, mutualInfoOf_comp hq hW₁]

/-- The conditional entropies of the outputs, from the marginal laws. -/
lemma os_cond₁ (hq : IsPMF q) (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂) :
    H[fun z : ((X' × X'') × U) × (Y × S) => z.2.1 | fun z => z.1.2 ; jointOf q (rcOS W₁ W₂)] =
      H[Prod.snd | fun z : (X' × U) × Y => z.1.2 ; jointOf (dist q osG₁) W₁] := by
  refine condEntropy_eq_of_dist_pair_eq (jointOf_isPMF hq (rcOS_isChannel hW₁ hW₂))
    (jointOf_isPMF (hq.dist _) hW₁) ?_
  rw [← os_dist₁ hW₂, ← dist_comp_eq]
  rfl

lemma os_cond₂ (hq : IsPMF q) (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂) :
    H[fun z : ((X' × X'') × U) × (Y × S) => z.2.2 | fun z => z.1.2 ; jointOf q (rcOS W₁ W₂)] =
      H[Prod.snd | fun z : (X'' × U) × S => z.1.2 ; jointOf (dist q osG₂) W₂] := by
  refine condEntropy_eq_of_dist_pair_eq (jointOf_isPMF hq (rcOS_isChannel hW₁ hW₂))
    (jointOf_isPMF (hq.dist _) hW₂) ?_
  rw [← os_dist₂ hW₁, ← dist_comp_eq]
  rfl

/-- **The broadcast cut**: `I(X; Y, Y₁ | X₁) ≤ I(X'; Y | X₁) + I(X''; Y₁ | X₁)`. -/
theorem rcBcInfo_os_le (hq : IsPMF q) (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂) :
    rcBcInfo q (rcOS W₁ W₂) ≤ osCI (dist q osG₂) W₂ + osCI (dist q osG₁) W₁ := by
  have hW := rcOS_isChannel hW₁ hW₂
  have hJ := jointOf_isPMF hq hW
  rw [rcBcInfo_eq hq hW, osCI_eq (hq.dist _) hW₁, osCI_eq (hq.dist _) hW₂, ← os_cond₁ hq hW₁ hW₂,
    ← os_cond₂ hq hW₁ hW₂, sum_dist_mul, sum_dist_mul]
  have hE : ∑ a, q a * entropy (rcOS W₁ W₂ a) =
      ∑ a, q a * entropy (W₁ (osG₁ a)) + ∑ a, q a * entropy (W₂ (osG₂ a)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [rcOS, entropy_prodDist (hW₁ _) (hW₂ _)]
    simp only [osG₁, osG₂]
    ring
  have h₁ := chain_rule_cond hJ (fun z : ((X' × X'') × U) × (Y × S) => z.2.1) (fun z => z.2.2)
    (fun z => z.1.2)
  have h₂ := condEntropy_le_condEntropy hJ (fun z : ((X' × X'') × U) × (Y × S) => z.2.2)
    (fun z => z.2.1) (fun z => z.1.2)
  have h₃ : H[Prod.snd | fun z : ((X' × X'') × U) × (Y × S) => z.1.2 ; jointOf q (rcOS W₁ W₂)] =
      H[pair (fun z => z.2.1) (fun z => z.2.2) | fun z => z.1.2 ; jointOf q (rcOS W₁ W₂)] := rfl
  rw [hE, h₃, h₁]
  linarith

end Vars

/-! ### Conditionally independent inputs -/

section Input

variable {p₁ : U → ℝ} {A : U → X' → ℝ} {B : U → X'' → ℝ}

/-- The input law `p(x₁) p(x' | x₁) p(x'' | x₁)`. -/
def osInput (p₁ : U → ℝ) (A : U → X' → ℝ) (B : U → X'' → ℝ) : (X' × X'') × U → ℝ :=
  fun a => p₁ a.2 * (A a.2 a.1.1 * B a.2 a.1.2)

omit [Fintype X'] [Fintype X''] [Fintype U] [Fintype Y] [Fintype S] in
lemma osInput_isPMF [Fintype X'] [Fintype X''] [Fintype U] (hp₁ : IsPMF p₁) (hA : IsChannel A)
    (hB : IsChannel B) : IsPMF (osInput p₁ A B) := by
  refine ⟨fun a => mul_nonneg (hp₁.nonneg _) (mul_nonneg ((hA _).nonneg _) ((hB _).nonneg _)), ?_⟩
  simp only [osInput, Fintype.sum_prod_type]
  have : ∀ x' : X', ∑ x'' : X'', ∑ u, p₁ u * (A u x' * B u x'') = ∑ u, p₁ u * A u x' := by
    intro x'
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [← mul_sum, ← mul_sum, (hB _).sum_eq_one, mul_one]
  simp_rw [this]
  rw [sum_comm]
  simp_rw [← mul_sum, (hA _).sum_eq_one, mul_one]
  exact hp₁.sum_eq_one

omit [Fintype Y] [Fintype S] in
/-- A sum over the inputs with given `(X', X₁)`. -/
lemma os_dist_G₁ (F : (X' × X'') × U → ℝ) (t : X' × U) :
    dist F osG₁ t = ∑ x'', F ((t.1, x''), t.2) := by
  classical
  obtain ⟨x', u⟩ := t
  simp only [dist, Fintype.sum_prod_type]
  rw [sum_eq_single x']
  · refine sum_congr rfl fun x'' _ => ?_
    rw [sum_eq_single u]
    · simp [osG₁]
    · intro u' _ hu
      refine ite_eq_right fun h => hu (Prod.ext_iff.mp h).2
    · simp
  · intro x₀ _ hx
    exact sum_eq_zero fun _ _ => sum_eq_zero fun _ _ =>
      ite_eq_right fun h => hx (Prod.ext_iff.mp h).1
  · simp

omit [Fintype Y] [Fintype S] in
/-- A sum over the inputs with given `(X'', X₁)`. -/
lemma os_dist_G₂ (F : (X' × X'') × U → ℝ) (t : X'' × U) :
    dist F osG₂ t = ∑ x', F ((x', t.1), t.2) := by
  classical
  obtain ⟨x'', u⟩ := t
  simp only [dist, Fintype.sum_prod_type]
  refine sum_congr rfl fun x' _ => ?_
  rw [sum_eq_single x'']
  · rw [sum_eq_single u]
    · simp [osG₂]
    · intro u' _ hu
      refine ite_eq_right fun h => hu (Prod.ext_iff.mp h).2
    · simp
  · intro x₀ _ hx
    exact sum_eq_zero fun _ _ => ite_eq_right fun h => hx (Prod.ext_iff.mp h).1
  · simp

omit [Fintype Y] [Fintype S] in
lemma dist_osG₁ (hB : IsChannel B) : dist (osInput p₁ A B) osG₁ = osPair p₁ A := by
  funext t
  rw [os_dist_G₁]
  simp only [osInput, osPair]
  rw [← mul_sum, ← mul_sum, (hB _).sum_eq_one, mul_one]

omit [Fintype Y] [Fintype S] in
lemma dist_osG₂ (hA : IsChannel A) : dist (osInput p₁ A B) osG₂ = osPair p₁ B := by
  funext t
  rw [os_dist_G₂]
  simp only [osInput, osPair]
  have e : ∀ x', p₁ t.2 * (A t.2 x' * B t.2 t.1) = p₁ t.2 * B t.2 t.1 * A t.2 x' := fun _ => by ring
  simp_rw [e]
  rw [← mul_sum, (hA _).sum_eq_one, mul_one]

/-- `Y` and `X''` are conditionally independent given `X₁`. -/
lemma os_markov (hp₁ : IsPMF p₁) (hA : IsChannel A) (hB : IsChannel B) (hW₁ : IsChannel W₁)
    (hW₂ : IsChannel W₂) :
    H[fun z : ((X' × X'') × U) × (Y × S) => z.2.1 | fun z => (z.1.2, z.1.1.2) ;
        jointOf (osInput p₁ A B) (rcOS W₁ W₂)] =
      H[fun z : ((X' × X'') × U) × (Y × S) => z.2.1 | fun z => z.1.2 ;
        jointOf (osInput p₁ A B) (rcOS W₁ W₂)] := by
  classical
  have hq := osInput_isPMF hp₁ hA hB
  have hK := jointOf_isPMF hq (rcOS_isChannel hW₁ hW₂)
  let κ : U → Y → ℝ := fun u y => ∑ x', A u x' * W₁ (x', u) y
  have hκ : IsChannel κ := fun u => by
    refine ⟨fun y => sum_nonneg fun x' _ => mul_nonneg ((hA _).nonneg _) ((hW₁ _).nonneg _), ?_⟩
    simp only [κ]
    rw [sum_comm]
    simp_rw [← mul_sum, (hW₁ _).sum_eq_one, mul_one]
    exact (hA _).sum_eq_one
  refine condEntropy_eq_comp_of_channel hK (fun z => (z.1.2, z.1.1.2)) (fun z => z.2.1)
    (Prod.fst : U × X'' → U) hκ ?_
  funext ⟨⟨u, x''⟩, y⟩
  have hinjS : Function.Injective fun t : X'' × U => (t.2, t.1) :=
    fun a b h => Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
  have hGd : ∀ F : (X' × X'') × U → ℝ, dist F (fun a => (a.2, a.1.2)) (u, x'') =
      ∑ x', F ((x', x''), u) := by
    intro F
    have e : (fun a : (X' × X'') × U => (a.2, a.1.2)) = (fun t : X'' × U => (t.2, t.1)) ∘ osG₂ :=
      rfl
    have h := dist_comp_of_injective F osG₂ hinjS (x'', u)
    rw [e]
    exact h.trans (os_dist_G₂ F (x'', u))
  have hG : dist (jointOf (osInput p₁ A B) (rcOS W₁ W₂)) (fun z => (z.1.2, z.1.1.2)) (u, x'') =
      p₁ u * B u x'' := by
    have hf : dist (jointOf (osInput p₁ A B) (rcOS W₁ W₂)) Prod.fst = osInput p₁ A B :=
      dist_jointOf_fst (rcOS_isChannel hW₁ hW₂)
    have e : (fun z : ((X' × X'') × U) × (Y × S) => (z.1.2, z.1.1.2)) =
        (fun a : (X' × X'') × U => (a.2, a.1.2)) ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, hf, hGd]
    simp only [osInput]
    have e' : ∀ x', p₁ u * (A u x' * B u x'') = p₁ u * B u x'' * A u x' := fun _ => by ring
    simp_rw [e']
    rw [← mul_sum, (hA _).sum_eq_one, mul_one]
  have hin : ∀ a : (X' × X'') × U,
      dist (rcOS W₁ W₂ a) (fun o => ((a.2, a.1.2), o.1)) ((u, x''), y) =
      (if (a.2, a.1.2) = (u, x'') then 1 else 0) * W₁ (osG₁ a) y := by
    intro a
    by_cases ha : (a.2, a.1.2) = (u, x'')
    · rw [ite_eq_left ha, one_mul, ← ha]
      have e : (fun o : Y × S => ((a.2, a.1.2), o.1)) = (fun b => ((a.2, a.1.2), b)) ∘ Prod.fst :=
        rfl
      rw [e, dist_comp_of_injective _ _ (fun b b' h => (Prod.ext_iff.mp h).2)]
      rw [rcOS, dist_prodDist_fst (hW₂ _)]
      rfl
    · rw [ite_eq_right ha, zero_mul]
      simp only [dist]
      exact sum_eq_zero fun o _ => ite_eq_right fun h => absurd (Prod.ext_iff.mp h).1 ha
  rw [show (pair (fun z : ((X' × X'') × U) × (Y × S) => (z.1.2, z.1.1.2)) fun z => z.2.1) =
    fun z => ((z.1.2, z.1.1.2), z.2.1) from rfl, dist_jointOf_row]
  simp_rw [hin]
  have hsum : ∑ a : (X' × X'') × U, osInput p₁ A B a *
      ((if (a.2, a.1.2) = (u, x'') then 1 else 0) * W₁ (osG₁ a) y) =
      dist (fun a => osInput p₁ A B a * W₁ (osG₁ a) y) (fun a => (a.2, a.1.2)) (u, x'') := by
    simp only [dist]
    refine sum_congr rfl fun a _ => ?_
    by_cases ha : (a.2, a.1.2) = (u, x'')
    · rw [ite_eq_left ha, ite_eq_left ha, one_mul]
    · rw [ite_eq_right ha, ite_eq_right ha, zero_mul, mul_zero]
  rw [hsum, hGd]
  simp only [jointOf, hG, κ, mul_sum, osInput, osG₁]
  refine sum_congr rfl fun x' _ => ?_
  ring

end Input

/-! ### The capacity -/

section Capacity

variable [Nonempty X'] [Nonempty X''] [Nonempty U] [Nonempty Y] [Nonempty S]

omit [Nonempty X'] [Nonempty X''] [Nonempty U] [Nonempty Y] [Nonempty S] in
lemma bddAbove_rcOS (hW₁ : IsChannel W₁) :
    BddAbove {v | ∃ (p₁ : U → ℝ) (A : U → X' → ℝ) (B : U → X'' → ℝ), IsPMF p₁ ∧ IsChannel A ∧
      IsChannel B ∧ v = min (mutualInfoOf (osPair p₁ A) W₁)
        (osCI (osPair p₁ B) W₂ + osCI (osPair p₁ A) W₁)} := by
  refine ⟨capacity W₁, ?_⟩
  rintro _ ⟨p₁, A, B, hp₁, hA, hB, rfl⟩
  exact (min_le_left _ _).trans (mutualInfoOf_le_capacity (osPair_isPMF hp₁ hA) hW₁)

/-- **Page 17-36 of [elgamal2010]: the capacity of the relay channel with orthogonal sender
components.** Partial decode–forward with `U = X''` achieves the cutset bound. -/
theorem rcCapacity_os (hW₁ : IsChannel W₁) (hW₂ : IsChannel W₂) :
    rcCapacity (rcOS W₁ W₂) = rcOSBound W₁ W₂ / log 2 := by
  classical
  have hW := rcOS_isChannel hW₁ hW₂
  refine rcCapacity_eq (fun R hR => ?_) fun R hR => (hR.le_rcCutsetBound hW).trans ?_
  · have hne : Set.Nonempty {v | ∃ (p₁ : U → ℝ) (A : U → X' → ℝ) (B : U → X'' → ℝ), IsPMF p₁ ∧
        IsChannel A ∧ IsChannel B ∧ v = min (mutualInfoOf (osPair p₁ A) W₁)
          (osCI (osPair p₁ B) W₂ + osCI (osPair p₁ A) W₁)} :=
      ⟨_, ⟨uniformPMF U, fun _ => uniformPMF X', fun _ => uniformPMF X'', uniformPMF_isPMF,
        fun _ => uniformPMF_isPMF, fun _ => uniformPMF_isPMF, rfl⟩⟩
    obtain ⟨_, ⟨p₁, A, B, hp₁, hA, hB, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hR
    obtain ⟨h₁, h₂⟩ := lt_min_iff.mp hlt
    have hq := osInput_isPMF hp₁ hA hB
    have hK := jointOf_isPMF hq hW
    refine isAchievableRC_of_fun (U := X'') hq hW (fun a => a.1.2) ?_ ?_
    · rw [rcMacInfo_os hq hW₁ hW₂, dist_osG₁ hB]
      exact h₁
    · refine lt_of_lt_of_eq h₂ ?_
      simp only [rcFunInfo]
      congr 1
      · -- `I(X''; Y₁ | X₁)`
        rw [← dist_osG₂ (p₁ := p₁) (A := A) (B := B) hA, osCI, ← os_dist₂ hW₁,
          condMutualInfo_dist hK]
        rfl
      · -- `I(X; Y | X₁, X'') = I(X'; Y | X₁)`
        rw [condMutualInfo_comm hK, condMutualInfo_eq' hK, os_markov hp₁ hA hB hW₁ hW₂,
          osCI_eq (osPair_isPMF hp₁ hA) hW₁, ← dist_osG₁ (p₁ := p₁) (A := A) (B := B) hB,
          ← os_cond₁ hq hW₁ hW₂, sum_dist_mul]
        congr 1
        have hT : IsChannel (W₁ ∘ osG₁ : (X' × X'') × U → Y → ℝ) := fun a => hW₁ _
        have e₁ : H[fun z : ((X' × X'') × U) × (Y × S) => z.2.1 | pair (fun z => (z.1.2, z.1.1.2))
            (fun z => z.1.1) ; jointOf (osInput p₁ A B) (rcOS W₁ W₂)] =
            H[fun z => z.2.1 | Prod.fst ; jointOf (osInput p₁ A B) (rcOS W₁ W₂)] :=
          condEntropy_congr_right hK _ (fun a : (X' × X'') × U => ((a.2, a.1.2), a.1))
            (fun a b h => Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp (Prod.ext_iff.mp h).1).1)
            fun _ => rfl
        have e₂ : H[fun z : ((X' × X'') × U) × (Y × S) => z.2.1 | Prod.fst ;
            jointOf (osInput p₁ A B) (rcOS W₁ W₂)] =
            H[Prod.snd | Prod.fst ; jointOf (osInput p₁ A B) (W₁ ∘ osG₁)] := by
          refine condEntropy_eq_of_dist_pair_eq hK (jointOf_isPMF hq hT) ?_
          funext ⟨a, y⟩
          rw [show (pair Prod.fst fun z : ((X' × X'') × U) × (Y × S) => z.2.1) =
            pair Prod.fst fun z => (Prod.snd z).1 from rfl, dist_pair_marg_fst]
          simp_rw [dist_pair_fst_snd]
          simp only [jointOf, rcOS, prodDist, ← mul_sum, (hW₂ _).sum_eq_one, mul_one]
          rfl
        rw [e₁, e₂, condEntropy_jointOf hq hT]
        rfl
  · refine csSup_le ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    -- the laws of the two components
    have hswap₁ : Function.Injective fun t : X' × U => (t.2, t.1) :=
      fun a b h => Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
    have hswap₂ : Function.Injective fun t : X'' × U => (t.2, t.1) :=
      fun a b h => Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1
    obtain ⟨A, hA, hfA⟩ := exists_kernel (hq.dist fun a : (X' × X'') × U => (a.2, a.1.1))
    obtain ⟨B, hB, hfB⟩ := exists_kernel (hq.dist fun a : (X' × X'') × U => (a.2, a.1.2))
    have hm₁ : dist (dist q fun a : (X' × X'') × U => (a.2, a.1.1)) Prod.fst = dist q Prod.snd :=
      (dist_comp_eq _ _ _).symm
    have hm₂ : dist (dist q fun a : (X' × X'') × U => (a.2, a.1.2)) Prod.fst = dist q Prod.snd :=
      (dist_comp_eq _ _ _).symm
    have hr₁ : dist q osG₁ = osPair (dist q Prod.snd) A := by
      funext ⟨x', u⟩
      have h := dist_comp_of_injective q osG₁ hswap₁ (x', u)
      rw [← h]
      have := hfA u x'
      rw [hm₁] at this
      exact this
    have hr₂ : dist q osG₂ = osPair (dist q Prod.snd) B := by
      funext ⟨x'', u⟩
      have h := dist_comp_of_injective q osG₂ hswap₂ (x'', u)
      rw [← h]
      have := hfB u x''
      rw [hm₂] at this
      exact this
    refine le_trans ?_ (le_csSup (bddAbove_rcOS hW₁) ⟨dist q Prod.snd, A, B, hq.dist _, hA, hB,
      rfl⟩)
    rw [← hr₁, ← hr₂]
    exact min_le_min (le_of_eq (rcMacInfo_os hq hW₁ hW₂)) (rcBcInfo_os_le hq hW₁ hW₂)

end Capacity

end InfoTheory
