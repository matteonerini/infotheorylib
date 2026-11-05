/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungBinning
public import InfoTheoryLib.RateDistortion.SideInfoAchievability

/-!
# The Berger–Tung inner bound for a constant `Q`

This file proves the inner bound of Theorem 1 of Lecture 13 without time sharing: the rates
`R₁ > I(X₁; U₁ | U₂)`, `R₂ > I(X₂; U₂ | U₁)` and `R₁ + R₂ > I(X₁, X₂; U₁, U₂)`, for
`p(u₁ | x₁) p(u₂ | x₂)`, are achievable.

## Main definitions

* `btRate₁`, `btRate₂`, `btRate₁₂`: the three informations, in nats.
* `btCost₁`, `btCost₂`: the expected distortions.

## Main statements

* `btRate₁_eq`, `btRate₂_eq`, `btRate₁₂_eq`: the informations in terms of `I(Xⱼ; Uⱼ)` and
  `I(U₁; U₂)`.
* `eventually_bt_code`: the codes for typical quadruples.
* `isAchievableDL_of_lt`: **the Berger–Tung inner bound, without time sharing**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ υ₁ υ₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂]
  {P : α₁ × α₂ → ℝ} {κ₁ : α₁ → υ₁ → ℝ} {κ₂ : α₂ → υ₂ → ℝ}

/-! ### The informations -/

section Rates

/-- **Theorem 1 of Lecture 13.** `I(X₁; U₁ | U₂)`, in nats. -/
def btRate₁ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) : ℝ :=
  I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.1 : fun z => z.1.1.2 | Prod.snd ; btLaw P κ₁ κ₂]

/-- **Theorem 1 of Lecture 13.** `I(X₂; U₂ | U₁)`, in nats. -/
def btRate₂ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) : ℝ :=
  I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 : Prod.snd | fun z => z.1.1.2 ; btLaw P κ₁ κ₂]

/-- **Theorem 1 of Lecture 13.** `I(X₁, X₂; U₁, U₂)`, in nats. -/
def btRate₁₂ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) : ℝ :=
  I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => (z.1.1.1, z.1.2) : fun z => (z.1.1.2, z.2) ; btLaw P κ₁ κ₂]

/-- If the law of `(V, U)` is `p(v) κ(u | g(v))`, then `H(U | V) = H(U | g(V))`. -/
lemma condEntropy_eq_comp_of_channel {Ω V X U : Type*} [Fintype Ω] [Fintype V] [Fintype X]
    [Fintype U] {μ : Ω → ℝ} (hμ : IsPMF μ) (A : Ω → V) (B : Ω → U) (g : V → X) {κ : X → U → ℝ}
    (hκ : IsChannel κ) (h : dist μ (pair A B) = jointOf (dist μ A) fun v => κ (g v)) :
    H[B | A ; μ] = H[B | g ∘ A ; μ] := by
  classical
  have hw : IsPMF (dist μ A) := hμ.dist A
  have hw' : IsPMF (dist μ (g ∘ A)) := hμ.dist _
  have h1 : H[B | A ; μ] = ∑ v, dist μ A v * entropy (κ (g v)) := by
    rw [← condEntropy_jointOf hw fun v => hκ (g v)]
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hw fun v => hκ (g v)) ?_
    rw [h, dist_pair_fst_snd]
  have h2 : H[B | g ∘ A ; μ] = ∑ x, dist μ (g ∘ A) x * entropy (κ x) := by
    rw [← condEntropy_jointOf hw' hκ]
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hw' hκ) ?_
    rw [dist_pair_fst_snd, dist_comp_eq, ← dist_jointOf_map, ← h, ← dist_comp_eq]
    rfl
  rw [h1, h2, dist_comp_eq]
  exact (sum_dist_mul (dist μ A) g fun x => entropy (κ x)).symm ▸ rfl

/-- The conditioning sequence of `U₁`: `H(U₁ | X₁, X₂, U₂) = H(U₁ | X₁)`. -/
lemma condEntropy_U₁ (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    H[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 | fun z => (z.1.1.1, z.1.2, z.2) ;
      btLaw P κ₁ κ₂] =
    H[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 | fun z => z.1.1.1 ; btLaw P κ₁ κ₂] := by
  classical
  have hμ := btLaw_isPMF hP h₁ h₂
  refine condEntropy_eq_comp_of_channel hμ _ _ (fun v : α₁ × α₂ × υ₂ => v.1) h₁ ?_
  have hinj : Function.Injective fun z : ((α₁ × υ₁) × α₂) × υ₂ =>
      (((z.1.1.1, z.1.2, z.2), z.1.1.2) : (α₁ × α₂ × υ₂) × υ₁) := by
    rintro ⟨⟨⟨a, b⟩, c⟩, d⟩ ⟨⟨⟨a', b'⟩, c'⟩, d'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    rfl
  have hA : ∀ (x₁ : α₁) (x₂ : α₂) (u₂ : υ₂),
      dist (btLaw P κ₁ κ₂) (fun z : ((α₁ × υ₁) × α₂) × υ₂ => (z.1.1.1, z.1.2, z.2)) (x₁, x₂, u₂) =
        P (x₁, x₂) * κ₂ x₂ u₂ := fun x₁ x₂ u₂ => by
    have e : ∀ u₁, dist (btLaw P κ₁ κ₂) (fun z : ((α₁ × υ₁) × α₂) × υ₂ =>
        (((z.1.1.1, z.1.2, z.2), z.1.1.2) : (α₁ × α₂ × υ₂) × υ₁)) ((x₁, x₂, u₂), u₁) =
        P (x₁, x₂) * κ₁ x₁ u₁ * κ₂ x₂ u₂ := fun u₁ => by
      have h := dist_comp_of_injective (btLaw P κ₁ κ₂) id hinj (((x₁, u₁), x₂), u₂)
      rw [dist_id] at h
      exact h
    have hs := sum_dist_pair_right (btLaw P κ₁ κ₂)
      (fun z : ((α₁ × υ₁) × α₂) × υ₂ => (z.1.1.1, z.1.2, z.2)) (fun z => z.1.1.2) (x₁, x₂, u₂)
    rw [← hs]
    calc _ = ∑ u₁, P (x₁, x₂) * κ₁ x₁ u₁ * κ₂ x₂ u₂ := sum_congr rfl fun u₁ _ => e u₁
      _ = _ := by
          simp only [← sum_mul, ← mul_sum, (h₁ x₁).sum_eq_one, mul_one]
  funext ⟨⟨x₁, x₂, u₂⟩, u₁⟩
  have h := dist_comp_of_injective (btLaw P κ₁ κ₂) id hinj (((x₁, u₁), x₂), u₂)
  rw [dist_id] at h
  simp only [jointOf, hA]
  refine Eq.trans h ?_
  simp only [btLaw, jointOf, btQ₃]
  ring

/-- The conditioning sequence of `U₂`: `H(U₂ | X₁, U₁, X₂) = H(U₂ | X₂)`. -/
lemma condEntropy_U₂ (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    H[Prod.snd | Prod.fst ; btLaw P κ₁ κ₂] =
    H[Prod.snd | fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 ; btLaw P κ₁ κ₂] := by
  have hμ := btLaw_isPMF hP h₁ h₂
  refine condEntropy_eq_comp_of_channel hμ _ _ (Prod.snd : (α₁ × υ₁) × α₂ → α₂) h₂ ?_
  have hm : dist (btLaw P κ₁ κ₂) Prod.fst = btQ₃ P κ₁ := margFst_btLaw h₂
  rw [dist_pair_fst_snd, hm]
  rfl

/-- `I(X₁; U₁ | U₂) = I(X₁; U₁) - I(U₁; U₂)`. -/
theorem btRate₁_eq (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    btRate₁ P κ₁ κ₂ =
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : fun z => z.1.1.1 ; btLaw P κ₁ κ₂] -
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ₂] := by
  classical
  have hμ := btLaw_isPMF hP h₁ h₂
  set U₁ : ((α₁ × υ₁) × α₂) × υ₂ → υ₁ := fun z => z.1.1.2
  set X₁ : ((α₁ × υ₁) × α₂) × υ₂ → α₁ := fun z => z.1.1.1
  set U₂ : ((α₁ × υ₁) × α₂) × υ₂ → υ₂ := Prod.snd
  have hkey := condEntropy_U₁ hP h₁ h₂
  have hle1 : H[U₁ | pair X₁ U₂ ; btLaw P κ₁ κ₂] ≤ H[U₁ | X₁ ; btLaw P κ₁ κ₂] :=
    condEntropy_le_condEntropy_comp hμ U₁ (pair X₁ U₂) Prod.fst
  have hle2 : H[U₁ | fun z : ((α₁ × υ₁) × α₂) × υ₂ => (z.1.1.1, z.1.2, z.2) ; btLaw P κ₁ κ₂] ≤
      H[U₁ | pair X₁ U₂ ; btLaw P κ₁ κ₂] :=
    condEntropy_le_condEntropy_comp hμ U₁ _ fun v : α₁ × α₂ × υ₂ => (v.1, v.2.2)
  have heq : H[U₁ | pair X₁ U₂ ; btLaw P κ₁ κ₂] = H[U₁ | X₁ ; btLaw P κ₁ κ₂] :=
    le_antisymm hle1 (by rw [← hkey]; exact hle2)
  rw [btRate₁, condMutualInfo_comm hμ, condMutualInfo, mutualInfo_eq_entropy_sub_condEntropy hμ,
    mutualInfo_eq_entropy_sub_condEntropy hμ]
  have hsw : H[U₁ | pair X₁ U₂ ; btLaw P κ₁ κ₂] = H[U₁ | pair X₁ U₂ ; btLaw P κ₁ κ₂] := rfl
  rw [hsw, heq]
  ring

/-- `I(X₂; U₂ | U₁) = I(X₂; U₂) - I(U₁; U₂)`. -/
theorem btRate₂_eq (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    btRate₂ P κ₁ κ₂ =
      I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 ; btLaw P κ₁ κ₂] -
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ₂] := by
  classical
  have hμ := btLaw_isPMF hP h₁ h₂
  set U₁ : ((α₁ × υ₁) × α₂) × υ₂ → υ₁ := fun z => z.1.1.2
  set X₂ : ((α₁ × υ₁) × α₂) × υ₂ → α₂ := fun z => z.1.2
  set U₂ : ((α₁ × υ₁) × α₂) × υ₂ → υ₂ := Prod.snd
  have hkey := condEntropy_U₂ hP h₁ h₂
  have hle1 : H[U₂ | pair X₂ U₁ ; btLaw P κ₁ κ₂] ≤ H[U₂ | X₂ ; btLaw P κ₁ κ₂] :=
    condEntropy_le_condEntropy_comp hμ U₂ (pair X₂ U₁) Prod.fst
  have hle2 : H[U₂ | Prod.fst ; btLaw P κ₁ κ₂] ≤ H[U₂ | pair X₂ U₁ ; btLaw P κ₁ κ₂] :=
    condEntropy_le_condEntropy_comp hμ U₂ Prod.fst fun v : (α₁ × υ₁) × α₂ => (v.2, v.1.2)
  have heq : H[U₂ | pair X₂ U₁ ; btLaw P κ₁ κ₂] = H[U₂ | X₂ ; btLaw P κ₁ κ₂] :=
    le_antisymm hle1 (by rw [← hkey]; exact hle2)
  rw [btRate₂, condMutualInfo_comm hμ, condMutualInfo, mutualInfo_eq_entropy_sub_condEntropy hμ,
    mutualInfo_comm hμ U₁ U₂, mutualInfo_eq_entropy_sub_condEntropy hμ]
  rw [heq]
  ring

/-- `I(X₁, X₂; U₁, U₂) = I(X₁; U₁) + I(X₂; U₂) - I(U₁; U₂)`. -/
theorem btRate₁₂_eq (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    btRate₁₂ P κ₁ κ₂ =
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : fun z => z.1.1.1 ; btLaw P κ₁ κ₂] +
      I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 ; btLaw P κ₁ κ₂] -
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ₂] := by
  classical
  have hμ := btLaw_isPMF hP h₁ h₂
  set U₁ : ((α₁ × υ₁) × α₂) × υ₂ → υ₁ := fun z => z.1.1.2
  set X₁ : ((α₁ × υ₁) × α₂) × υ₂ → α₁ := fun z => z.1.1.1
  set X₂ : ((α₁ × υ₁) × α₂) × υ₂ → α₂ := fun z => z.1.2
  set U₂ : ((α₁ × υ₁) × α₂) × υ₂ → υ₂ := Prod.snd
  set XX : ((α₁ × υ₁) × α₂) × υ₂ → α₁ × α₂ := fun z => (z.1.1.1, z.1.2)
  -- `H(U₁ | X₁, X₂) = H(U₁ | X₁)`.
  have h1 : H[U₁ | XX ; btLaw P κ₁ κ₂] = H[U₁ | X₁ ; btLaw P κ₁ κ₂] := by
    have hle1 : H[U₁ | XX ; btLaw P κ₁ κ₂] ≤ H[U₁ | X₁ ; btLaw P κ₁ κ₂] :=
      condEntropy_le_condEntropy_comp hμ U₁ XX Prod.fst
    have hle2 : H[U₁ | fun z : ((α₁ × υ₁) × α₂) × υ₂ => (z.1.1.1, z.1.2, z.2) ; btLaw P κ₁ κ₂] ≤
        H[U₁ | XX ; btLaw P κ₁ κ₂] :=
      condEntropy_le_condEntropy_comp hμ U₁ _ fun v : α₁ × α₂ × υ₂ => (v.1, v.2.1)
    exact le_antisymm hle1 (by rw [← condEntropy_U₁ hP h₁ h₂]; exact hle2)
  -- `H(U₂ | U₁, X₁, X₂) = H(U₂ | X₂)`.
  have h2 : H[U₂ | pair U₁ XX ; btLaw P κ₁ κ₂] = H[U₂ | X₂ ; btLaw P κ₁ κ₂] := by
    have hle1 : H[U₂ | pair U₁ XX ; btLaw P κ₁ κ₂] ≤ H[U₂ | X₂ ; btLaw P κ₁ κ₂] :=
      condEntropy_le_condEntropy_comp hμ U₂ (pair U₁ XX) fun v : υ₁ × α₁ × α₂ => v.2.2
    have hle2 : H[U₂ | Prod.fst ; btLaw P κ₁ κ₂] ≤ H[U₂ | pair U₁ XX ; btLaw P κ₁ κ₂] :=
      condEntropy_le_condEntropy_comp hμ U₂ Prod.fst
        fun v : (α₁ × υ₁) × α₂ => (v.1.2, v.1.1, v.2)
    exact le_antisymm hle1 (by rw [← condEntropy_U₂ hP h₁ h₂]; exact hle2)
  -- The chain rule.
  have hc := chain_rule_cond hμ U₁ U₂ XX
  have hc2 := chain_rule hμ U₁ U₂
  have e0 : btRate₁₂ P κ₁ κ₂ = H[pair U₁ U₂ ; btLaw P κ₁ κ₂] -
    H[pair U₁ U₂ | XX ; btLaw P κ₁ κ₂] := by
    rw [btRate₁₂, mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
    rfl
  rw [e0, hc, hc2, h1, h2, mutualInfo_eq_entropy_sub_condEntropy hμ,
    mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_comm hμ U₁ U₂,
    mutualInfo_eq_entropy_sub_condEntropy hμ]
  ring

end Rates

/-! ### The rates -/

section Limit

variable {R₁ R₂ ε : ℝ}

/-- `I(X₁; U₁)` under the law of `(X₁, U₁)`. -/
lemma mutualInfo_btJ₁ (h₂ : IsChannel κ₂) :
    I[Prod.snd : Prod.fst ; btJ₁ P κ₁] =
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : fun z => z.1.1.1 ; btLaw P κ₁ κ₂] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [← dist_btLaw_X₁U₁ h₂, ← dist_comp_eq]
  rfl

/-- `I(X₂; U₂)` under the law of `(X₂, U₂)`. -/
lemma mutualInfo_btJ₂ (h₁ : IsChannel κ₁) :
    I[Prod.snd : Prod.fst ; btJ₂ P κ₂] =
      I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 ; btLaw P κ₁ κ₂] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [← dist_btLaw_X₂U₂ h₁, ← dist_comp_eq]
  rfl

/-- `I(U₁; U₂)` under the law of `(U₁, U₂)`. -/
lemma mutualInfo_btUU :
    I[Prod.fst : Prod.snd ; btUU P κ₁ κ₂] =
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ₂] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [dist_pair_fst_snd]
  rfl

/-- If `a < b` and `L n ≥ e^{nb}`, then `exp(-L n c e^{-na}) → 0`, for `c > 0`. -/
lemma tendsto_exp_neg_cover' {a b c : ℝ} (hab : a < b) (hc : 0 < c) {L : ℕ → ℕ}
    (hL : ∀ n : ℕ, exp (n * b) ≤ L n) :
    Tendsto (fun n : ℕ => exp (-(L n * (c * exp (-(n * a)))))) atTop (𝓝 0) := by
  refine tendsto_exp_neg_atTop_nhds_zero.comp ?_
  have hlow : ∀ n : ℕ, c * exp (n * (b - a)) ≤ L n * (c * exp (-(n * a))) := fun n => by
    have e : exp (n * (b - a)) = exp (n * b) * exp (-(n * a)) := by
      rw [← exp_add]
      ring_nf
    rw [e]
    have := mul_le_mul_of_nonneg_right (hL n) (mul_pos hc (exp_pos (-(n * a)))).le
    nlinarith
  refine tendsto_atTop_mono hlow (Tendsto.const_mul_atTop hc ?_)
  exact tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hab))

/-- The terms of the binning, with `Lⱼ = ⌈e^{n bⱼ}⌉` codewords and `Mⱼ = 2^⌊n Rⱼ⌋` bins. -/
lemma bin_terms_le (n : ℕ) {R₁ R₂ b₁ b₂ E : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    (((⌈exp (n * b₁)⌉₊ : ℕ) : ℝ) / ((2 ^ ⌊n * R₁⌋₊ : ℕ) : ℝ) +
      ((⌈exp (n * b₂)⌉₊ : ℕ) : ℝ) / ((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ) +
      ((⌈exp (n * b₁)⌉₊ : ℕ) : ℝ) * ((⌈exp (n * b₂)⌉₊ : ℕ) : ℝ) / (((2 ^ ⌊n * R₁⌋₊ : ℕ) : ℝ) *
        ((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ))) * exp (-(n * E)) ≤
      4 * exp (-(n * (R₁ * log 2 + E - b₁))) + 4 * exp (-(n * (R₂ * log 2 + E - b₂))) +
        16 * exp (-(n * ((R₁ + R₂) * log 2 + E - b₁ - b₂))) := by
  have hLub : ∀ (b : ℝ), 0 ≤ b → ((⌈exp (n * b)⌉₊ : ℕ) : ℝ) ≤ 2 * exp (n * b) := fun b hb => by
    have h1 : 1 ≤ exp (n * b) := one_le_exp (by positivity)
    have := (Nat.ceil_lt_add_one (exp_pos (n * b)).le).le
    linarith
  have hMl₁ := exp_le_two_pow_floor n R₁
  have hMl₂ := exp_le_two_pow_floor n R₂
  set a₁ := ((⌈exp (n * b₁)⌉₊ : ℕ) : ℝ) / ((2 ^ ⌊n * R₁⌋₊ : ℕ) : ℝ) with ha₁
  set a₂ := ((⌈exp (n * b₂)⌉₊ : ℕ) : ℝ) / ((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ) with ha₂
  have hdiv₁ : a₁ ≤ 2 * exp (n * b₁) / exp (n * (R₁ * log 2) - log 2) :=
    div_le_div₀ (by positivity) (hLub b₁ hb₁) (exp_pos _) hMl₁
  have hdiv₂ : a₂ ≤ 2 * exp (n * b₂) / exp (n * (R₂ * log 2) - log 2) :=
    div_le_div₀ (by positivity) (hLub b₂ hb₂) (exp_pos _) hMl₂
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have hcast : ((⌈exp (n * b₁)⌉₊ : ℕ) : ℝ) * ((⌈exp (n * b₂)⌉₊ : ℕ) : ℝ) /
      (((2 ^ ⌊n * R₁⌋₊ : ℕ) : ℝ) * ((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ)) = a₁ * a₂ := mul_div_mul_comm _ _ _ _
  rw [hcast]
  have e4 : (4 : ℝ) = 2 * exp (log 2) := by rw [exp_log two_pos]; norm_num
  have hexp : ∀ a b : ℝ, exp a / exp b = exp (a - b) := fun a b => (exp_sub a b).symm
  have he₁ : 2 * exp (n * b₁) / exp (n * (R₁ * log 2) - log 2) * exp (-(n * E)) =
      4 * exp (-(n * (R₁ * log 2 + E - b₁))) := by
    rw [e4, mul_assoc, mul_div_assoc, hexp, mul_assoc, ← exp_add, ← exp_add]
    congr 2
    ring
  have he₂ : 2 * exp (n * b₂) / exp (n * (R₂ * log 2) - log 2) * exp (-(n * E)) =
      4 * exp (-(n * (R₂ * log 2 + E - b₂))) := by
    rw [e4, mul_assoc, mul_div_assoc, hexp, mul_assoc, ← exp_add, ← exp_add]
    congr 2
    ring
  have he₃ : 2 * exp (n * b₁) / exp (n * (R₁ * log 2) - log 2) *
      (2 * exp (n * b₂) / exp (n * (R₂ * log 2) - log 2)) * exp (-(n * E)) =
      16 * exp (-(n * ((R₁ + R₂) * log 2 + E - b₁ - b₂))) := by
    have e16 : (16 : ℝ) = 4 * (exp (log 2) * exp (log 2)) := by
      rw [exp_log two_pos]
      norm_num
    rw [e16, show 2 * exp (n * b₁) / exp (n * (R₁ * log 2) - log 2) *
      (2 * exp (n * b₂) / exp (n * (R₂ * log 2) - log 2)) * exp (-(n * E)) =
      4 * ((exp (n * b₁) / exp (n * (R₁ * log 2) - log 2)) *
        (exp (n * b₂) / exp (n * (R₂ * log 2) - log 2)) * exp (-(n * E))) by ring,
      hexp, hexp, ← exp_add, ← exp_add, ← exp_add, mul_assoc (4 : ℝ), ← exp_add]
    congr 2
    ring
  have he0 : 0 ≤ exp (-(n * E)) := (exp_pos _).le
  rw [add_mul, add_mul, ← he₁, ← he₂, ← he₃]
  refine add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdiv₁ he0)
    (mul_le_mul_of_nonneg_right hdiv₂ he0)) (mul_le_mul_of_nonneg_right ?_ he0)
  exact mul_le_mul hdiv₁ hdiv₂ ha₂0 (ha₁0.trans hdiv₁)

open Classical in
/-- **Lecture 13, page 13-13.** If `R₁ > I(X₁; U₁) - I(U₁; U₂)`, `R₂ > I(X₂; U₂) - I(U₁; U₂)` and
`R₁ + R₂ > I(X₁; U₁) + I(X₂; U₂) - I(U₁; U₂)`, with a loss `δ(ε)` in `I(U₁; U₂)`, then there are
codes with `2^⌊nRⱼ⌋` indices and with `(X₁ⁿ, U₁ⁿ, X₂ⁿ, U₂ⁿ)` typical except with probability at most
`δ`. -/
theorem eventually_bt_code (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1)
    (hR₁ : I[Prod.snd : Prod.fst ; btJ₁ P κ₁] - btPackExp (btUU P κ₁ κ₂) ε < R₁ * log 2)
    (hR₂ : I[Prod.snd : Prod.fst ; btJ₂ P κ₂] - btPackExp (btUU P κ₁ κ₂) ε < R₂ * log 2)
    (hR₁₂ : I[Prod.snd : Prod.fst ; btJ₁ P κ₁] + I[Prod.snd : Prod.fst ; btJ₂ P κ₂] -
      btPackExp (btUU P κ₁ κ₂) ε < (R₁ + R₂) * log 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ (enc₁ : (Fin n → α₁) → Fin (2 ^ ⌊n * R₁⌋₊))
      (enc₂ : (Fin n → α₂) → Fin (2 ^ ⌊n * R₂⌋₊))
      (dec : Fin (2 ^ ⌊n * R₁⌋₊) × Fin (2 ^ ⌊n * R₂⌋₊) → (Fin n → υ₁) × (Fin n → υ₂)),
      ∑ ω, iidPMF P n ω * (if btSeq ω (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).1
          (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).2 ∈ robustTypicalSet (btLaw P κ₁ κ₂) n ε
          then 0 else 1) ≤ δ := by
  have hJ₁ := btJ₁_isPMF (P := P) hP h₁
  have hJ₂ := btJ₂_isPMF (P := P) hP h₂
  set I₁ := I[Prod.snd : Prod.fst ; btJ₁ P κ₁]
  set I₂ := I[Prod.snd : Prod.fst ; btJ₂ P κ₂]
  set E := btPackExp (btUU P κ₁ κ₂) ε
  set D₁ := H[Prod.snd ; btJ₁ P κ₁] + H[Prod.snd | Prod.fst ; btJ₁ P κ₁]
  set D₂ := H[Prod.snd ; btJ₂ P κ₂] + H[Prod.snd | Prod.fst ; btJ₂ P κ₂]
  have hD₁ : 0 ≤ D₁ := add_nonneg (entropy_nonneg (hJ₁.dist _)) (condEntropy_nonneg hJ₁ _ _)
  have hD₂ : 0 ≤ D₂ := add_nonneg (entropy_nonneg (hJ₂.dist _)) (condEntropy_nonneg hJ₂ _ _)
  have hI₁ : 0 ≤ I₁ := mutualInfo_nonneg hJ₁ _ _
  have hI₂ : 0 ≤ I₂ := mutualInfo_nonneg hJ₂ _ _
  -- The slack.
  set S := min (R₁ * log 2 - (I₁ - E)) (min (R₂ * log 2 - (I₂ - E))
    ((R₁ + R₂) * log 2 - (I₁ + I₂ - E))) with hS
  have hS0 : 0 < S := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hS₁ : S ≤ R₁ * log 2 - (I₁ - E) := min_le_left _ _
  have hS₂ : S ≤ R₂ * log 2 - (I₂ - E) := (min_le_right _ _).trans (min_le_left _ _)
  have hS₃ : S ≤ (R₁ + R₂) * log 2 - (I₁ + I₂ - E) := (min_le_right _ _).trans (min_le_right _ _)
  set ε₁ := ε / 2 with hε₁
  obtain ⟨c, hc, hlim⟩ := exists_mul_condExpBound_tendsto (btLaw P κ₁ κ₂)
    (show ε₁ < ε by rw [hε₁]; linarith)
  -- The parameters.
  set ε₂ := min (ε / 4) (min (1 / 2) (min (S / (8 * (D₁ + D₂ + 1))) (c / (4 * (D₂ + 1))))) with hε₂d
  have hpos1 : 0 < S / (8 * (D₁ + D₂ + 1)) := by positivity
  have hpos2 : 0 < c / (4 * (D₂ + 1)) := by positivity
  have hε₂0 : 0 < ε₂ := lt_min (by linarith) (lt_min (by norm_num) (lt_min hpos1 hpos2))
  have hε₂1 : ε₂ ≤ ε / 4 := min_le_left _ _
  have hε₂2 : ε₂ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₂3 : ε₂ ≤ S / (8 * (D₁ + D₂ + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₂4 : ε₂ ≤ c / (4 * (D₂ + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbD : ε₂ * (D₁ + D₂ + 1) ≤ S / 8 := by
    rw [le_div_iff₀ (by positivity)] at hε₂3
    linarith
  have hbD₁ : ε₂ * D₁ ≤ S / 8 := by nlinarith
  have hbD₂ : ε₂ * D₂ ≤ S / 8 := by nlinarith
  have hG : 2 * (ε₂ * D₂) < c := by
    rw [le_div_iff₀ (by positivity)] at hε₂4
    nlinarith
  set ε₃ := ε₂ / 2 with hε₃
  set η := S / 8 with hη
  set b₁ := coverExp (btJ₁ P κ₁) ε₂ + η with hb₁
  set b₂ := coverExp (btJ₂ P κ₂) ε₂ + η with hb₂
  have hb₁' : b₁ = I₁ + ε₂ * D₁ + η := rfl
  have hb₂' : b₂ = I₂ + ε₂ * D₂ + η := rfl
  set L₁ : ℕ → ℕ := fun n => ⌈exp (n * b₁)⌉₊ with hL₁
  set L₂ : ℕ → ℕ := fun n => ⌈exp (n * b₂)⌉₊ with hL₂
  have hb₁0 : 0 ≤ b₁ := by rw [hb₁']; positivity
  have hb₂0 : 0 ≤ b₂ := by rw [hb₂']; positivity
  -- The limits.
  have t₁ : Tendsto (fun n : ℕ => exp (-(L₂ n * ((1 - ε₂) *
      exp (-(n * coverExp (btJ₂ P κ₂) ε₂)))))) atTop (𝓝 0) :=
    tendsto_exp_neg_cover' (by rw [hb₂]; linarith) (by linarith) fun n => Nat.le_ceil _
  have t₂ : Tendsto (fun n : ℕ => 2 * (exp (n * (2 * (ε₂ * D₂))) *
      condExpBound (btLaw P κ₁ κ₂) ε₁ ε n)) atTop (𝓝 0) := by
    simpa using (hlim _ hG).const_mul 2
  have t₃ : Tendsto (fun n => 1 - prob (iidPMF (margSnd P) n)
      (robustTypicalSet (margSnd P) n ε₃)) atTop (𝓝 0) := by
    simpa using (tendsto_prob_robustTypicalSet (hP.dist _) (by positivity)).const_sub 1
  have t₄ : Tendsto (fun n => 1 - prob (iidPMF (margFst P) n)
      (robustTypicalSet (margFst P) n ε₃)) atTop (𝓝 0) := by
    simpa using (tendsto_prob_robustTypicalSet (hP.dist _) (by positivity)).const_sub 1
  have t₅ : Tendsto (fun n : ℕ => exp (-(L₁ n * ((1 - ε₂) *
      exp (-(n * coverExp (btJ₁ P κ₁) ε₂)))))) atTop (𝓝 0) :=
    tendsto_exp_neg_cover' (by rw [hb₁]; linarith) (by linarith) fun n => Nat.le_ceil _
  have t₆ : Tendsto (fun n : ℕ => condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hexpo : ∀ {g : ℝ}, 0 < g → Tendsto (fun n : ℕ => exp (-(n * g))) atTop (𝓝 0) := fun hg =>
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hg)
  set g₁ := R₁ * log 2 + E - b₁ with hg₁
  set g₂ := R₂ * log 2 + E - b₂ with hg₂
  set g₃ := (R₁ + R₂) * log 2 + E - b₁ - b₂ with hg₃
  have hg₁0 : 0 < g₁ := by rw [hg₁, hb₁']; linarith
  have hg₂0 : 0 < g₂ := by rw [hg₂, hb₂']; linarith
  have hg₃0 : 0 < g₃ := by rw [hg₃, hb₁', hb₂']; linarith
  have t₇ : Tendsto (fun n : ℕ => 4 * exp (-(n * g₁)) + 4 * exp (-(n * g₂)) +
      16 * exp (-(n * g₃))) atTop (𝓝 0) := by
    simpa using (((hexpo hg₁0).const_mul 4).add ((hexpo hg₂0).const_mul 4)).add
      ((hexpo hg₃0).const_mul 16)
  have hsum := (((((((t₁.add t₂).add t₃).add t₄).add t₅).add t₆)).add t₇)
  simp only [add_zero] at hsum
  have hmF₁ : margFst (btJ₁ P κ₁) = margFst P := dist_jointOf_fst h₁
  have hmF₂ : margFst (btJ₂ P κ₂) = margSnd P := dist_jointOf_fst h₂
  have hc₁ := eventually_le_prob_iidPMF_condRobustTypicalSet hJ₁ (ε' := ε₃) (ε := ε₂)
    (by rw [hε₃]; linarith) hε₂0
  have hc₂ := eventually_le_prob_iidPMF_condRobustTypicalSet hJ₂ (ε' := ε₃) (ε := ε₂)
    (by rw [hε₃]; linarith) hε₂0
  rw [hmF₁] at hc₁
  rw [hmF₂] at hc₂
  filter_upwards [hsum.eventually (gt_mem_nhds hδ), hc₁, hc₂, eventually_gt_atTop 0]
    with n hn hl₁ hl₂ hn0
  have hL₁0 : 0 < L₁ n := Nat.ceil_pos.2 (exp_pos _)
  have hL₂0 : 0 < L₂ n := Nat.ceil_pos.2 (exp_pos _)
  have hM₁ : 0 < 2 ^ ⌊n * R₁⌋₊ := by positivity
  have hM₂ : 0 < 2 ^ ⌊n * R₂⌋₊ := by positivity
  obtain ⟨enc₁, enc₂, dec, hbd⟩ := exists_bt_code_le (L₁ := L₁ n) (L₂ := L₂ n) (ε := ε)
    (ε₁ := ε₁) (ε₂ := ε₂) (ε₃ := ε₃) hP h₁ h₂ (by rw [hε₁]; linarith) (by rw [hε₁]; linarith)
    hε0.le (by rw [hε₁]; linarith) hε₂2 hn0 hL₁0 hL₂0 hM₁ hM₂ hl₁ hl₂
  refine ⟨enc₁, enc₂, dec, hbd.trans ?_⟩
  have hbin := bin_terms_le n (R₁ := R₁) (R₂ := R₂) (E := E) hb₁0 hb₂0
  have hcover : btCoverBound P κ₁ κ₂ ε ε₁ ε₂ ε₃ n (L₁ n) (L₂ n) +
      (((L₁ n : ℕ) : ℝ) / ((2 ^ ⌊n * R₁⌋₊ : ℕ) : ℝ) +
      ((L₂ n : ℕ) : ℝ) / ((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ) +
      ((L₁ n : ℕ) : ℝ) * ((L₂ n : ℕ) : ℝ) / (((2 ^ ⌊n * R₁⌋₊ : ℕ) : ℝ) *
        ((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ))) * exp (-(n * E)) ≤
      btCoverBound P κ₁ κ₂ ε ε₁ ε₂ ε₃ n (L₁ n) (L₂ n) +
        (4 * exp (-(n * g₁)) + 4 * exp (-(n * g₂)) + 16 * exp (-(n * g₃))) :=
    add_le_add le_rfl hbin
  refine hcover.trans (le_of_lt ?_)
  simp only [btCoverBound]
  linarith

end Limit

/-! ### The inner bound -/

section Inner

variable {β₁ β₂ : Type*} {d₁ : α₁ → β₁ → ℝ} {d₂ : α₂ → β₂ → ℝ}

/-- `E d₁(X₁, x̂₁(U₁, U₂))`. -/
def btCost₁ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) (d₁ : α₁ → β₁ → ℝ)
    (f₁ : υ₁ → υ₂ → β₁) : ℝ :=
  ∑ z, btLaw P κ₁ κ₂ z * d₁ z.1.1.1 (f₁ z.1.1.2 z.2)

/-- `E d₂(X₂, x̂₂(U₁, U₂))`. -/
def btCost₂ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) (d₂ : α₂ → β₂ → ℝ)
    (f₂ : υ₁ → υ₂ → β₂) : ℝ :=
  ∑ z, btLaw P κ₁ κ₂ z * d₂ z.1.2 (f₂ z.1.1.2 z.2)

omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] in
instance DistLossyCode.finite [Finite α₁] [Finite α₂] [Finite β₁] [Finite β₂] {M₁ M₂ n : ℕ} :
    Finite (DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂) :=
  Finite.of_injective (fun c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂ => (c.enc₁, c.enc₂, c.dec))
    fun c c' h => by
      cases c
      cases c'
      simpa using h

omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] in
lemma DistLossyCode.nonempty [Nonempty β₁] [Nonempty β₂] {M₁ M₂ n : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    Nonempty (DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂) :=
  ⟨⟨fun _ => ⟨0, h₁⟩, fun _ => ⟨0, h₂⟩,
    fun _ => (fun _ => Classical.arbitrary β₁, fun _ => Classical.arbitrary β₂)⟩⟩

/-- To show that a rate pair is achievable it is enough to find, for every `ε > 0` and all large
`n`, a code with distortions at most `Dⱼ + ε`. -/
theorem isAchievableDL_of_eventually [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂]
    {R₁ R₂ D₁ D₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ c : DistLossyCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂ β₁
      β₂,
      c.distortion₁ P d₁ ≤ D₁ + ε ∧ c.distortion₂ P d₂ ≤ D₂ + ε) :
    IsAchievableDL P d₁ d₂ R₁ R₂ D₁ D₂ := by
  have hne := fun n : ℕ => DistLossyCode.nonempty (α₁ := α₁) (α₂ := α₂) (β₁ := β₁) (β₂ := β₂)
    (n := n) (M₁ := 2 ^ ⌊n * R₁⌋₊) (M₂ := 2 ^ ⌊n * R₂⌋₊) (by positivity) (by positivity)
  obtain ⟨c, hc⟩ := exists_seq_of_eventually
    (C := fun n : ℕ => DistLossyCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂ β₁ β₂)
    (fun n c => max (c.distortion₁ P d₁ - D₁) (c.distortion₂ P d₂ - D₂)) (a := 0) fun ε hε => by
      filter_upwards [h ε hε] with n ⟨c, h1, h2⟩
      exact ⟨c, by
        rw [zero_add]
        exact max_le (by linarith) (by linarith)⟩
  refine ⟨hR₁, hR₂, c, fun ε hε => ?_⟩
  filter_upwards [hc ε hε] with n hn
  rw [zero_add] at hn
  have h1 := (le_max_left _ _).trans hn
  have h2 := (le_max_right _ _).trans hn
  exact ⟨by linarith, by linarith⟩

open Classical in
omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] in
/-- The expected average cost is at most `(1 + ε) E g + m P{not typical}`, by the typical average
lemma. -/
lemma sum_mul_cost_le {Ω Z : Type*} [Fintype Ω] [Fintype Z] {μ : Ω → ℝ} (hμ : IsPMF μ) {q : Z → ℝ}
    (hq : IsPMF q) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) (t : Ω → Fin n → Z) {g : Z → ℝ}
    (hg : ∀ z, 0 ≤ g z) {F : Ω → ℝ} (hF : ∀ ω, F ω = (∑ i, g (t ω i)) / n) {m : ℝ}
    (hFm : ∀ ω, F ω ≤ m) :
    ∑ ω, μ ω * F ω ≤ (1 + ε) * expect q g + m *
      ∑ ω, μ ω * (if t ω ∈ robustTypicalSet q n ε then (0 : ℝ) else 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : 0 ≤ expect q g := sum_nonneg fun z _ => mul_nonneg (hg z) (hq.nonneg z)
  have hpt : ∀ ω, F ω ≤ (1 + ε) * expect q g +
      m * (if t ω ∈ robustTypicalSet q n ε then (0 : ℝ) else 1) := fun ω => by
    by_cases ht : t ω ∈ robustTypicalSet q n ε
    · have h3 := sum_le_card_mul_of_mem_robustTypicalSet ht hg
      simp only [ht, ite_true, mul_zero, add_zero]
      rw [hF, div_le_iff₀ hn', mul_comm _ (n : ℝ)]
      exact h3
    · simp only [ht, ite_false, mul_one]
      have : 0 ≤ (1 + ε) * expect q g := by positivity
      linarith [hFm ω]
  calc ∑ ω, μ ω * F ω ≤ ∑ ω, μ ω * ((1 + ε) * expect q g +
        m * (if t ω ∈ robustTypicalSet q n ε then (0 : ℝ) else 1)) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hμ.nonneg ω)
    _ = _ := by
        have e : ∀ ω, μ ω * ((1 + ε) * expect q g +
            m * (if t ω ∈ robustTypicalSet q n ε then (0 : ℝ) else 1)) =
            μ ω * ((1 + ε) * expect q g) +
              m * (μ ω * (if t ω ∈ robustTypicalSet q n ε then (0 : ℝ) else 1)) := fun ω => by ring
        simp only [e]
        rw [sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul, mul_sum]

/-- The code with the reconstructions `x̂ⱼ(u₁, u₂)` from a code for the auxiliary sequences. -/
def btCode {M₁ M₂ n : ℕ} (enc₁ : (Fin n → α₁) → Fin M₁) (enc₂ : (Fin n → α₂) → Fin M₂)
    (dec : Fin M₁ × Fin M₂ → (Fin n → υ₁) × (Fin n → υ₂)) (f₁ : υ₁ → υ₂ → β₁)
    (f₂ : υ₁ → υ₂ → β₂) : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂ :=
  ⟨enc₁, enc₂, fun m => (fun i => f₁ ((dec m).1 i) ((dec m).2 i),
    fun i => f₂ ((dec m).1 i) ((dec m).2 i))⟩

open Classical in
/-- The first distortion of the code. -/
lemma distortion₁_btCode_le [Finite β₁] (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hd₁ : ∀ x y, 0 ≤ d₁ x y) {M₁ M₂ n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε)
    (enc₁ : (Fin n → α₁) → Fin M₁) (enc₂ : (Fin n → α₂) → Fin M₂)
    (dec : Fin M₁ × Fin M₂ → (Fin n → υ₁) × (Fin n → υ₂)) (f₁ : υ₁ → υ₂ → β₁)
    (f₂ : υ₁ → υ₂ → β₂) :
    (btCode enc₁ enc₂ dec f₁ f₂).distortion₁ P d₁ ≤ (1 + ε) * btCost₁ P κ₁ κ₂ d₁ f₁ +
      maxDistortion d₁ * ∑ ω, iidPMF P n ω * (if btSeq ω (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).1
        (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).2 ∈ robustTypicalSet (btLaw P κ₁ κ₂) n ε
        then 0 else 1) := by
  have h3 := sum_mul_cost_le (iidPMF_isPMF hP n) (btLaw_isPMF hP h₁ h₂) hn hε
    (fun ω => btSeq ω (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).1
      (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).2)
    (g := fun z => d₁ z.1.1.1 (f₁ z.1.1.2 z.2)) (fun z => hd₁ _ _)
    (F := fun ω => seqDistortion d₁ (fstSeq ω) ((btCode enc₁ enc₂ dec f₁ f₂).output ω).1)
    (fun ω => rfl) (m := maxDistortion d₁) fun ω => seqDistortion_le_maxDistortion d₁ hn _ _
  have e : expect (btLaw P κ₁ κ₂) (fun z => d₁ z.1.1.1 (f₁ z.1.1.2 z.2)) =
      btCost₁ P κ₁ κ₂ d₁ f₁ := by
    simp only [expect, btCost₁, mul_comm]
  rw [e] at h3
  refine h3.trans (le_of_eq ?_)
  congr!

open Classical in
/-- The second distortion of the code. -/
lemma distortion₂_btCode_le [Finite β₂] (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hd₂ : ∀ x y, 0 ≤ d₂ x y) {M₁ M₂ n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε)
    (enc₁ : (Fin n → α₁) → Fin M₁) (enc₂ : (Fin n → α₂) → Fin M₂)
    (dec : Fin M₁ × Fin M₂ → (Fin n → υ₁) × (Fin n → υ₂)) (f₁ : υ₁ → υ₂ → β₁)
    (f₂ : υ₁ → υ₂ → β₂) :
    (btCode enc₁ enc₂ dec f₁ f₂).distortion₂ P d₂ ≤ (1 + ε) * btCost₂ P κ₁ κ₂ d₂ f₂ +
      maxDistortion d₂ * ∑ ω, iidPMF P n ω * (if btSeq ω (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).1
        (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).2 ∈ robustTypicalSet (btLaw P κ₁ κ₂) n ε
        then 0 else 1) := by
  have h3 := sum_mul_cost_le (iidPMF_isPMF hP n) (btLaw_isPMF hP h₁ h₂) hn hε
    (fun ω => btSeq ω (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).1
      (dec (enc₁ (fstSeq ω), enc₂ (sndSeq ω))).2)
    (g := fun z => d₂ z.1.2 (f₂ z.1.1.2 z.2)) (fun z => hd₂ _ _)
    (F := fun ω => seqDistortion d₂ (sndSeq ω) ((btCode enc₁ enc₂ dec f₁ f₂).output ω).2)
    (fun ω => rfl) (m := maxDistortion d₂) fun ω => seqDistortion_le_maxDistortion d₂ hn _ _
  have e : expect (btLaw P κ₁ κ₂) (fun z => d₂ z.1.2 (f₂ z.1.1.2 z.2)) =
      btCost₂ P κ₁ κ₂ d₂ f₂ := by
    simp only [expect, btCost₂, mul_comm]
  rw [e] at h3
  refine h3.trans (le_of_eq ?_)
  congr!

open Classical in
/-- **Theorem 1 of Lecture 13, for a constant `Q` (pages 13-9 to 13-13).** For
`p(u₁ | x₁) p(u₂ | x₂)` and `x̂ⱼ(u₁, u₂)` with `E dⱼ(Xⱼ, X̂ⱼ) ≤ Dⱼ`, every rate pair with
`R₁ > I(X₁; U₁ | U₂)`, `R₂ > I(X₂; U₂ | U₁)` and `R₁ + R₂ > I(X₁, X₂; U₁, U₂)` bits is
achievable. -/
theorem isAchievableDL_of_lt [Finite β₁] [Finite β₂] (hP : IsPMF P) (hd₁ : ∀ x y, 0 ≤ d₁ x y)
    (hd₂ : ∀ x y, 0 ≤ d₂ x y) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (f₁ : υ₁ → υ₂ → β₁)
    (f₂ : υ₁ → υ₂ → β₂) {R₁ R₂ D₁ D₂ : ℝ} (hc₁ : btCost₁ P κ₁ κ₂ d₁ f₁ ≤ D₁)
    (hc₂ : btCost₂ P κ₁ κ₂ d₂ f₂ ≤ D₂) (hR₁ : btRate₁ P κ₁ κ₂ / log 2 < R₁)
    (hR₂ : btRate₂ P κ₁ κ₂ / log 2 < R₂) (hR₁₂ : btRate₁₂ P κ₁ κ₂ / log 2 < R₁ + R₂) :
    IsAchievableDL P d₁ d₂ R₁ R₂ D₁ D₂ := by
  have hl := log_pos one_lt_two
  have hμ := btLaw_isPMF hP h₁ h₂
  have hU := btUU_isPMF hP h₁ h₂
  have hJ₁ := btJ₁_isPMF (P := P) hP h₁
  have hJ₂ := btJ₂_isPMF (P := P) hP h₂
  -- The rates are nonnegative, and the alphabets are not empty.
  have h0₁ : 0 ≤ btRate₁ P κ₁ κ₂ := condMutualInfo_nonneg hμ _ _ _
  have h0₂ : 0 ≤ btRate₂ P κ₁ κ₂ := condMutualInfo_nonneg hμ _ _ _
  have hR₁0 : 0 ≤ R₁ := (div_nonneg h0₁ hl.le).trans hR₁.le
  have hR₂0 : 0 ≤ R₂ := (div_nonneg h0₂ hl.le).trans hR₂.le
  obtain ⟨⟨x₁, x₂⟩⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  obtain ⟨u₁, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF (h₁ x₁))
  obtain ⟨u₂, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF (h₂ x₂))
  have hβ₁ : Nonempty β₁ := ⟨f₁ u₁ u₂⟩
  have hβ₂ : Nonempty β₂ := ⟨f₂ u₁ u₂⟩
  have hα₁ : Nonempty α₁ := ⟨x₁⟩
  have hα₂ : Nonempty α₂ := ⟨x₂⟩
  have hm₁ := maxDistortion_nonneg (d := d₁) hd₁
  have hm₂ := maxDistortion_nonneg (d := d₂) hd₂
  -- The exponents.
  set I₁ := I[Prod.snd : Prod.fst ; btJ₁ P κ₁] with hI₁
  set I₂ := I[Prod.snd : Prod.fst ; btJ₂ P κ₂] with hI₂
  set I₁₂ := I[Prod.fst : Prod.snd ; btUU P κ₁ κ₂] with hI₁₂
  have er₁ : btRate₁ P κ₁ κ₂ = I₁ - I₁₂ := by
    rw [btRate₁_eq hP h₁ h₂, hI₁, hI₁₂, mutualInfo_btJ₁ h₂, mutualInfo_btUU]
  have er₂ : btRate₂ P κ₁ κ₂ = I₂ - I₁₂ := by
    rw [btRate₂_eq hP h₁ h₂, hI₂, hI₁₂, mutualInfo_btJ₂ h₁, mutualInfo_btUU]
  have er₁₂ : btRate₁₂ P κ₁ κ₂ = I₁ + I₂ - I₁₂ := by
    rw [btRate₁₂_eq hP h₁ h₂, hI₁, hI₂, hI₁₂, mutualInfo_btJ₁ h₂, mutualInfo_btJ₂ h₁,
      mutualInfo_btUU]
  rw [div_lt_iff₀ hl] at hR₁ hR₂ hR₁₂
  rw [er₁] at hR₁
  rw [er₂] at hR₂
  rw [er₁₂] at hR₁₂
  set D₀ := H[Prod.fst ; btUU P κ₁ κ₂] + H[Prod.snd ; btUU P κ₁ κ₂] +
    H[Prod.fst | Prod.snd ; btUU P κ₁ κ₂] + H[Prod.snd | Prod.fst ; btUU P κ₁ κ₂] with hD₀
  have hD₀0 : 0 ≤ D₀ := by
    have a1 := entropy_nonneg (hU.dist (Prod.fst : υ₁ × υ₂ → υ₁))
    have a2 := entropy_nonneg (hU.dist (Prod.snd : υ₁ × υ₂ → υ₂))
    have a3 := condEntropy_nonneg hU (Prod.fst : υ₁ × υ₂ → υ₁) Prod.snd
    have a4 := condEntropy_nonneg hU (Prod.snd : υ₁ × υ₂ → υ₂) Prod.fst
    exact add_nonneg (add_nonneg (add_nonneg a1 a2) a3) a4
  set C₁ := btCost₁ P κ₁ κ₂ d₁ f₁ with hC₁
  set C₂ := btCost₂ P κ₁ κ₂ d₂ f₂ with hC₂
  refine isAchievableDL_of_eventually hR₁0 hR₂0 fun η hη => ?_
  -- The choice of `ε`.
  set S := min (R₁ * log 2 - (I₁ - I₁₂)) (min (R₂ * log 2 - (I₂ - I₁₂))
    ((R₁ + R₂) * log 2 - (I₁ + I₂ - I₁₂))) with hS
  have hS0 : 0 < S := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  set ε := min 1 (min (S / (2 * (D₀ + 1))) (min (η / (2 * (C₁ + 1))) (η / (2 * (C₂ + 1))))) with hε
  have hC₁0 : 0 ≤ C₁ := sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (hd₁ _ _)
  have hC₂0 : 0 ≤ C₂ := sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (hd₂ _ _)
  have hε0 : 0 < ε := lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by
    positivity)))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ S / (2 * (D₀ + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ η / (2 * (C₁ + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε4 : ε ≤ η / (2 * (C₂ + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεD : ε * D₀ ≤ S / 2 := by
    rw [le_div_iff₀ (by positivity)] at hε2
    linarith
  have hεC₁ : ε * C₁ ≤ η / 2 := by
    rw [le_div_iff₀ (by positivity)] at hε3
    linarith
  have hεC₂ : ε * C₂ ≤ η / 2 := by
    rw [le_div_iff₀ (by positivity)] at hε4
    linarith
  have hE : btPackExp (btUU P κ₁ κ₂) ε = I₁₂ - ε * D₀ := rfl
  have hS₁ : S ≤ R₁ * log 2 - (I₁ - I₁₂) := min_le_left _ _
  have hS₂ : S ≤ R₂ * log 2 - (I₂ - I₁₂) := (min_le_right _ _).trans (min_le_left _ _)
  have hS₃ : S ≤ (R₁ + R₂) * log 2 - (I₁ + I₂ - I₁₂) := (min_le_right _ _).trans (min_le_right _ _)
  -- The codes.
  set δ := η / 2 / (maxDistortion d₁ + maxDistortion d₂ + 1) with hδd
  have hδ : 0 < δ := by positivity
  have hmδ₁ : maxDistortion d₁ * δ ≤ η / 2 := by
    rw [hδd, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith [mul_nonneg hη.le (add_nonneg hm₂ zero_le_one)]
  have hmδ₂ : maxDistortion d₂ * δ ≤ η / 2 := by
    rw [hδd, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith [mul_nonneg hη.le (add_nonneg hm₁ zero_le_one)]
  filter_upwards [eventually_bt_code hP h₁ h₂ hε0 hε1 (R₁ := R₁) (R₂ := R₂)
    (by rw [hE]; linarith) (by rw [hE]; linarith) (by rw [hE]; linarith) hδ,
    eventually_gt_atTop 0] with n ⟨enc₁, enc₂, dec, hbd⟩ hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hμn := iidPMF_isPMF hP n
  refine ⟨btCode enc₁ enc₂ dec f₁ f₂, ?_, ?_⟩
  · refine (distortion₁_btCode_le hP h₁ h₂ hd₁ hn hε0.le enc₁ enc₂ dec f₁ f₂).trans ?_
    have := mul_le_mul_of_nonneg_left hbd hm₁
    linarith
  · refine (distortion₂_btCode_le hP h₁ h₂ hd₂ hn hε0.le enc₁ enc₂ dec f₁ f₂).trans ?_
    have := mul_le_mul_of_nonneg_left hbd hm₂
    linarith

end Inner

end InfoTheory
