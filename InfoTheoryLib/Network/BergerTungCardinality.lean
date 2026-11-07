/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungSharing
public import InfoTheoryLib.RateDistortion.SideInfo

/-!
# The cardinality bound of the Berger–Tung inner bound

In the Berger–Tung inner bound, Theorem 1 of Lecture 13 of El Gamal and Kim, it suffices to take
`|𝒰₁| ≤ |𝒳₁| + 3` and `|𝒰₂| ≤ |𝒳₂| + 3`, which improves on the bound `|𝒳ⱼ| + 4` of the notes.

The three rates are functions of `I(U₁; X₁)`, `I(U₂; X₂)` and `I(U₁; U₂)` (`btRate₁_eq`,
`btRate₂_eq`, `btRate₁₂_eq`), so when `U₁` is reduced for a fixed `p(u₂ | x₂)`, two functions of
`p(x₁ | u₁)` preserve the rates, while the notes use three. With `|𝒳₁| - 1` functions for `p(x₁)`
and one for each distortion, this gives `|𝒳₁| + 3`. Each distortion is replaced by its best decoder,
as in `RateDistortion.SideInfo`, so that the distortions may decrease.

The Markov chain `U₁ → X₁ → U₂` makes `(X₁, U₂, U₁)` a law `siLaw`, and we use the tools of
`RateDistortion.SideInfo`. The outer bound of Theorem 2 of Lecture 13 is different: there `U₁` and
`U₂` have a joint law, so reducing `U₁` has to preserve the law of `(X₁, X₂, U₂)`, whose size
depends on `|𝒰₂|`.

## Main definitions

* `btGenCost P κ₁ κ₂ c`: `E c(X₁, X₂, U₁, U₂)`.

## Main statements

* `exists_bt_reduce₁`: the reduction of `U₁` for a fixed `p(u₂ | x₂)`.
* `exists_bt_reduce`: **the bound**, for a law without time sharing.
* `exists_bt_sharing_card`: **the bound**, with time sharing, as in Theorem 1 of Lecture 13.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13 and Appendix C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ υ₁ υ₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂]
  {P : α₁ × α₂ → ℝ} {κ₁ : α₁ → υ₁ → ℝ} {κ₂ : α₂ → υ₂ → ℝ}

/-- `E c(X₁, X₂, U₁, U₂)` under the law `p(x₁, x₂) p(u₁ | x₁) p(u₂ | x₂)`. -/
def btGenCost (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ)
    (c : α₁ × α₂ → υ₁ → υ₂ → ℝ) : ℝ :=
  ∑ z, btLaw P κ₁ κ₂ z * c (z.1.1.1, z.1.2) z.1.1.2 z.2

/-- The law of `(X₁, U₂)`. -/
def btSide₁ (P : α₁ × α₂ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) : α₁ × υ₂ → ℝ :=
  fun z => ∑ x₂, P (z.1, x₂) * κ₂ x₂ z.2

/-- The law of `(X₁, (X₂, U₂))`. -/
def btSide₂ (P : α₁ × α₂ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) : α₁ × α₂ × υ₂ → ℝ :=
  fun z => P (z.1, z.2.1) * κ₂ z.2.1 z.2.2

lemma margFst_btSide₁ (h₂ : IsChannel κ₂) : margFst (btSide₁ P κ₂) = margFst P := by
  funext x
  rw [margFst_apply, margFst_apply]
  simp only [btSide₁]
  rw [sum_comm]
  simp only [← mul_sum, (h₂ _).sum_eq_one, mul_one]

lemma margFst_btSide₂ (h₂ : IsChannel κ₂) : margFst (btSide₂ P κ₂) = margFst P := by
  funext x
  rw [margFst_apply, margFst_apply, Fintype.sum_prod_type]
  simp only [btSide₂, ← mul_sum, (h₂ _).sum_eq_one, mul_one]

lemma btSide₁_isPMF (hP : IsPMF P) (h₂ : IsChannel κ₂) : IsPMF (btSide₁ P κ₂) := by
  refine ⟨fun z => sum_nonneg fun x _ => mul_nonneg (hP.nonneg _) ((h₂ _).nonneg _), ?_⟩
  have h : ∑ x, margFst (btSide₁ P κ₂) x = 1 := by
    rw [margFst_btSide₁ h₂]
    exact (hP.dist _).sum_eq_one
  simpa only [margFst_apply, Fintype.sum_prod_type] using h

lemma btSide₂_isPMF (hP : IsPMF P) (h₂ : IsChannel κ₂) : IsPMF (btSide₂ P κ₂) := by
  refine ⟨fun z => mul_nonneg (hP.nonneg _) ((h₂ _).nonneg _), ?_⟩
  have h : ∑ x, margFst (btSide₂ P κ₂) x = 1 := by
    rw [margFst_btSide₂ h₂]
    exact (hP.dist _).sum_eq_one
  simpa only [margFst_apply, Fintype.sum_prod_type] using h

/-- The law of `((X₁, U₂), U₁)` is a law `siLaw`, by the Markov chain `U₁ → X₁ → U₂`. -/
lemma dist_btLaw_side₁ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) :
    dist (btLaw P κ₁ κ₂) (fun z => ((z.1.1.1, z.2), z.1.1.2)) = siLaw (btSide₁ P κ₂) κ₁ := by
  classical
  funext ⟨⟨x, u₂⟩, u₁⟩
  simp only [dist, Fintype.sum_prod_type, Prod.mk.injEq, siLaw, jointOf, btSide₁, btLaw, btQ₃,
    sum_mul]
  rw [sum_eq_single x (fun x' _ hx => by simp [hx]) (by simp),
    sum_eq_single u₁ (fun u' _ hu => by simp [hu]) (by simp)]
  refine sum_congr rfl fun x₂ _ => ?_
  rw [sum_eq_single u₂ (fun u' _ hu => by simp [hu]) (by simp)]
  simp only [and_self, ite_true]
  ring

/-- `I(U₁; X₁)`, as a rate of `siLaw`. -/
lemma mutualInfo_U₁X₁ (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : fun z => z.1.1.1 ; btLaw P κ₁ κ₂] =
      sideRate 0 (btSide₁ P κ₂) κ₁ := by
  have hμ := btLaw_isPMF hP h₁ h₂
  have e := mutualInfo_comp (μ := btLaw P κ₁ κ₂) (fun z : ((α₁ × υ₁) × α₂) × υ₂ =>
    ((z.1.1.1, z.2), z.1.1.2)) (fun t : (α₁ × υ₂) × υ₁ => t.1.1) Prod.snd
  rw [dist_btLaw_side₁] at e
  rw [mutualInfo_comm hμ, sideRate, zero_mul, sub_zero, ← e]
  rfl

/-- `I(U₁; U₂)`, as a difference of rates of `siLaw`. -/
lemma mutualInfo_U₁U₂ (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ₂] =
      sideRate 0 (btSide₁ P κ₂) κ₁ - sideRate 1 (btSide₁ P κ₂) κ₁ := by
  have hμ := btLaw_isPMF hP h₁ h₂
  have e := mutualInfo_comp (μ := btLaw P κ₁ κ₂) (fun z : ((α₁ × υ₁) × α₂) × υ₂ =>
    ((z.1.1.1, z.2), z.1.1.2)) (fun t : (α₁ × υ₂) × υ₁ => t.1.2) Prod.snd
  rw [dist_btLaw_side₁] at e
  simp only [sideRate, zero_mul, sub_zero, one_mul]
  rw [sub_sub_cancel, ← e, mutualInfo_comm hμ]
  rfl

/-- `E c(X₁, X₂, U₁, U₂)`, as a cost of `siLaw`. -/
lemma btGenCost_eq_sideCost (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ)
    (c : α₁ × α₂ → υ₁ → υ₂ → ℝ) :
    btGenCost P κ₁ κ₂ c = sideCost (btSide₂ P κ₂) κ₁ fun u x y => c (x, y.1) u y.2 := by
  let e : ((α₁ × υ₁) × α₂) × υ₂ ≃ (α₁ × α₂ × υ₂) × υ₁ :=
    { toFun := fun z => ((z.1.1.1, z.1.2, z.2), z.1.1.2)
      invFun := fun t => (((t.1.1, t.2), t.1.2.1), t.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ fun z => ?_
  simp only [e, Equiv.coe_fn_mk, siLaw, jointOf, btSide₂, btLaw, btQ₃]
  ring

/-- **The reduction of `U₁`, for a fixed `p(u₂ | x₂)`.** There is `p(u₁' | x₁)` with
`|𝒰₁'| = |𝒳₁| + 3`, the same `I(U₁; X₁)` and `I(U₁; U₂)`, and with decoders that have no larger
values of the two costs. -/
theorem exists_bt_reduce₁ (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (c₁ c₂ : α₁ × α₂ → υ₁ → υ₂ → ℝ) {N : ℕ} (hN : N = Fintype.card α₁ + 3) :
    ∃ (κ' : α₁ → Fin N → ℝ) (g₁ g₂ : Fin N → υ₁), IsChannel κ' ∧
      I[fun z : ((α₁ × Fin N) × α₂) × υ₂ => z.1.1.2 : fun z => z.1.1.1 ; btLaw P κ' κ₂] =
        I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : fun z => z.1.1.1 ; btLaw P κ₁ κ₂] ∧
      I[fun z : ((α₁ × Fin N) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ' κ₂] =
        I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ₂] ∧
      btGenCost P κ' κ₂ (fun x j u => c₁ x (g₁ j) u) ≤ btGenCost P κ₁ κ₂ c₁ ∧
      btGenCost P κ' κ₂ (fun x j u => c₂ x (g₂ j) u) ≤ btGenCost P κ₁ κ₂ c₂ := by
  classical
  have hP₁ := btSide₁_isPMF hP h₂
  have hP₂ := btSide₂_isPMF hP h₂
  obtain ⟨W, hW, hPW⟩ := exists_side_channel hP₁
  obtain ⟨V, -, hPV⟩ := exists_side_channel hP₂
  obtain ⟨w, r, hw, hr, hrep⟩ := exists_side_rep hP₁ h₁
  have hwP := isPMF_of_rep hP₁ h₁ hw hr hrep
  have hm : margFst (btSide₂ P κ₂) = margFst (btSide₁ P κ₂) := by
    rw [margFst_btSide₁ h₂, margFst_btSide₂ h₂]
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hα : Nonempty α₁ := ⟨z₀.1⟩
  have hαpos : 0 < Fintype.card α₁ := Fintype.card_pos
  have hυ : Nonempty υ₁ := Fintype.card_pos_iff.1 (card_pos_of_isPMF hwP)
  -- The best costs, as functions of the posterior law.
  set G : (α₁ × α₂ → υ₁ → υ₂ → ℝ) → υ₁ → (α₁ → ℝ) → ℝ := fun c u t =>
    sideG V (fun x y => c (x, y.1) u y.2) t with hG
  set best : (α₁ × α₂ → υ₁ → υ₂ → ℝ) → (α₁ → ℝ) → ℝ := fun c t =>
    univ.inf' univ_nonempty fun u => G c u t with hbest
  have hbc : ∀ c, Continuous (best c) := fun c =>
    Continuous.finset_inf'_apply univ_nonempty fun u _ => by
      have h : Continuous fun t : α₁ → ℝ => ∑ x, t x * ∑ y, V x y * c (x, y.1) u y.2 := by fun_prop
      exact h
  have hc : ∀ θ, Continuous (sideF θ W) := fun θ => by
    unfold sideF
    exact continuous_entropy.sub (continuous_const.mul (continuous_entropy_outDist W))
  set F : Fin 4 → (α₁ → ℝ) → ℝ := ![sideF 0 W, sideF 1 W, best c₁, best c₂] with hF
  have hFc : ∀ k, ContinuousOn (F k) {p | IsPMF p} := by
    intro k
    fin_cases k
    · exact (hc 0).continuousOn
    · exact (hc 1).continuousOn
    · exact (hbc c₁).continuousOn
    · exact (hbc c₂).continuousOn
  obtain ⟨w', z, hw', hz, hmean, hmix⟩ := exists_mixture_preserving_mean (κ := Fin 4) hFc hwP
    (fun u => hr u) (n := N) (by rw [Fintype.card_fin, hN]; omega)
  have m₀ := hmix 0
  have m₁ := hmix 1
  have m₂ := hmix 2
  have m₃ := hmix 3
  simp only [hF, Matrix.cons_val] at m₀ m₁ m₂ m₃
  have h1 : ∀ x, ∑ j, w' j * z j x = margFst (btSide₁ P κ₂) x := fun x => by
    rw [hmean, ← mul_one (margFst (btSide₁ P κ₂) x), ← (h₁ x).sum_eq_one, mul_sum]
    exact (sum_congr rfl fun u _ => hrep x u).symm
  obtain ⟨κ', hκ', hrep'⟩ := exists_kernel_of_mean hP₁ hw' hz h1
  have hrate := fun θ => sideRate_eq_of_rep hP₁ hκ' hW hPW hw'.nonneg (fun j => hz j) hrep' θ
  have hrate₀ := fun θ => sideRate_eq_of_rep hP₁ h₁ hW hPW hw hr hrep θ
  have e₀ : sideRate 0 (btSide₁ P κ₂) κ' = sideRate 0 (btSide₁ P κ₂) κ₁ := by
    rw [hrate, hrate₀, m₀]
  have e₁ : sideRate 1 (btSide₁ P κ₂) κ' = sideRate 1 (btSide₁ P κ₂) κ₁ := by
    rw [hrate, hrate₀, m₁]
  -- The decoders.
  have hmin : ∀ (c : α₁ × α₂ → υ₁ → υ₂ → ℝ) (j : Fin N), ∃ u, best c (z j) = G c u (z j) :=
      fun c j => by
    obtain ⟨u, -, hu⟩ := exists_mem_eq_inf' (s := (univ : Finset υ₁)) univ_nonempty
      fun u => G c u (z j)
    exact ⟨u, hu⟩
  choose g hg using hmin
  have hcost : ∀ (c : α₁ × α₂ → υ₁ → υ₂ → ℝ),
      ∑ j, w' j * best c (z j) = ∑ u, w u * best c (r u) →
      btGenCost P κ' κ₂ (fun x j u => c x (g c j) u) ≤ btGenCost P κ₁ κ₂ c := fun c hc' => by
    rw [btGenCost_eq_sideCost, btGenCost_eq_sideCost,
      sideCost_eq_of_rep (P := btSide₂ P κ₂) hPV (by rw [hm]; exact hrep'),
      sideCost_eq_of_rep (P := btSide₂ P κ₂) hPV (by rw [hm]; exact hrep)]
    have e : ∀ j, sideG V (fun x y => c (x, y.1) (g c j) y.2) (z j) = best c (z j) :=
      fun j => (hg c j).symm
    simp only [e]
    rw [hc']
    refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hw u)
    simp only [hbest]
    exact inf'_le (fun u₀ => G c u₀ (r u)) (mem_univ u)
  refine ⟨κ', g c₁, g c₂, hκ', ?_, ?_, hcost c₁ m₂, hcost c₂ m₃⟩
  · rw [mutualInfo_U₁X₁ hP hκ' h₂, mutualInfo_U₁X₁ hP h₁ h₂, e₀]
  · rw [mutualInfo_U₁U₂ hP hκ' h₂, mutualInfo_U₁U₂ hP h₁ h₂, e₀, e₁]

/-! ### Exchanging the two sources -/

/-- The law `p(x₂, x₁)` with the two sources exchanged. -/
def btSwap (P : α₁ × α₂ → ℝ) : α₂ × α₁ → ℝ := fun z => P z.swap

lemma btSwap_isPMF (hP : IsPMF P) : IsPMF (btSwap P) :=
  ⟨fun _ => hP.nonneg _, by
    rw [← hP.sum_eq_one]
    exact (Equiv.prodComm α₂ α₁).sum_comp P⟩

/-- Exchanging the two sources and the two auxiliaries. -/
private def btSwapEquiv (α₁ α₂ υ₁ υ₂ : Type*) :
    ((α₂ × υ₂) × α₁) × υ₁ ≃ ((α₁ × υ₁) × α₂) × υ₂ where
  toFun z := (((z.1.2, z.2), z.1.1.1), z.1.1.2)
  invFun t := (((t.1.2, t.2), t.1.1.1), t.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private lemma dist_btLaw_swap (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) :
    dist (btLaw (btSwap P) κ₂ κ₁) (btSwapEquiv α₁ α₂ υ₁ υ₂) = btLaw P κ₁ κ₂ := by
  have h := dist_comp_equiv (btLaw P κ₁ κ₂) (btSwapEquiv α₁ α₂ υ₁ υ₂)
  rw [← h]
  congr 1
  funext z
  simp only [btLaw, jointOf, btQ₃, btSwap, btSwapEquiv, Equiv.coe_fn_mk, Prod.swap]
  ring

private lemma mutualInfo_swap_X (κ₁ : α₁ → υ₁ → ℝ) (κ : α₂ → υ₂ → ℝ) :
    I[fun z : ((α₂ × υ₂) × α₁) × υ₁ => z.1.1.2 : fun z => z.1.1.1 ; btLaw (btSwap P) κ κ₁] =
      I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 ; btLaw P κ₁ κ] := by
  have e := mutualInfo_comp (μ := btLaw (btSwap P) κ κ₁) (btSwapEquiv α₁ α₂ υ₁ υ₂)
    (Prod.snd : ((α₁ × υ₁) × α₂) × υ₂ → υ₂) (fun z => z.1.2)
  rw [dist_btLaw_swap] at e
  exact e

private lemma mutualInfo_swap_U (hP : IsPMF P) (h₁ : IsChannel κ₁) {κ : α₂ → υ₂ → ℝ}
    (hκ : IsChannel κ) :
    I[fun z : ((α₂ × υ₂) × α₁) × υ₁ => z.1.1.2 : Prod.snd ; btLaw (btSwap P) κ κ₁] =
      I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ] := by
  have e := mutualInfo_comp (μ := btLaw (btSwap P) κ κ₁) (btSwapEquiv α₁ α₂ υ₁ υ₂)
    (Prod.snd : ((α₁ × υ₁) × α₂) × υ₂ → υ₂) (fun z => z.1.1.2)
  rw [dist_btLaw_swap] at e
  rw [mutualInfo_comm (btLaw_isPMF hP h₁ hκ)]
  exact e

private lemma btGenCost_swap (κ₁ : α₁ → υ₁ → ℝ) (κ : α₂ → υ₂ → ℝ) (c : α₁ × α₂ → υ₁ → υ₂ → ℝ) :
    btGenCost (btSwap P) κ κ₁ (fun x u₂ u₁ => c x.swap u₁ u₂) = btGenCost P κ₁ κ c := by
  refine Fintype.sum_equiv (btSwapEquiv α₁ α₂ υ₁ υ₂) _ _ fun z => ?_
  simp only [btLaw, jointOf, btQ₃, btSwap, btSwapEquiv, Equiv.coe_fn_mk, Prod.swap]
  ring

/-- **The reduction of `U₂`, for a fixed `p(u₁ | x₁)`.** -/
theorem exists_bt_reduce₂ (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (c₁ c₂ : α₁ × α₂ → υ₁ → υ₂ → ℝ) {N : ℕ} (hN : N = Fintype.card α₂ + 3) :
    ∃ (κ' : α₂ → Fin N → ℝ) (g₁ g₂ : Fin N → υ₂), IsChannel κ' ∧
      I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × Fin N => z.1.2 ; btLaw P κ₁ κ'] =
        I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 ; btLaw P κ₁ κ₂] ∧
      I[fun z : ((α₁ × υ₁) × α₂) × Fin N => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ'] =
        I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ; btLaw P κ₁ κ₂] ∧
      btGenCost P κ₁ κ' (fun x u j => c₁ x u (g₁ j)) ≤ btGenCost P κ₁ κ₂ c₁ ∧
      btGenCost P κ₁ κ' (fun x u j => c₂ x u (g₂ j)) ≤ btGenCost P κ₁ κ₂ c₂ := by
  have hP' := btSwap_isPMF hP
  obtain ⟨κ', g₁, g₂, hκ', hA, hC, h₃, h₄⟩ := exists_bt_reduce₁ hP' h₂ h₁
    (fun x u₂ u₁ => c₁ x.swap u₁ u₂) (fun x u₂ u₁ => c₂ x.swap u₁ u₂) hN
  refine ⟨κ', g₁, g₂, hκ', ?_, ?_, ?_, ?_⟩
  · rw [← mutualInfo_swap_X κ₁ κ', ← mutualInfo_swap_X κ₁ κ₂]
    exact hA
  · rw [← mutualInfo_swap_U hP h₁ hκ', ← mutualInfo_swap_U hP h₁ h₂]
    exact hC
  · rw [← btGenCost_swap κ₁ κ₂ c₁, ← btGenCost_swap κ₁ κ' fun x u j => c₁ x u (g₁ j)]
    exact h₃
  · rw [← btGenCost_swap κ₁ κ₂ c₂, ← btGenCost_swap κ₁ κ' fun x u j => c₂ x u (g₂ j)]
    exact h₄

/-! ### The bound -/

variable {β₁ β₂ : Type*}

/-- **The cardinality bound of Theorem 1 of Lecture 13 of [elgamal2010], for a law without time
sharing.** For every `p(u₁ | x₁)`, `p(u₂ | x₂)`, `x̂₁(u₁, u₂)` and `x̂₂(u₁, u₂)` there are such laws
and functions with `|𝒰₁'| = |𝒳₁| + 3` and `|𝒰₂'| = |𝒳₂| + 3`, the same three rates, and no larger
distortions. -/
theorem exists_bt_reduce (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (d₁ : α₁ → β₁ → ℝ)
    (d₂ : α₂ → β₂ → ℝ) (f₁ : υ₁ → υ₂ → β₁) (f₂ : υ₁ → υ₂ → β₂) :
    ∃ (κ₁' : α₁ → Fin (Fintype.card α₁ + 3) → ℝ) (κ₂' : α₂ → Fin (Fintype.card α₂ + 3) → ℝ)
      (f₁' : Fin (Fintype.card α₁ + 3) → Fin (Fintype.card α₂ + 3) → β₁)
      (f₂' : Fin (Fintype.card α₁ + 3) → Fin (Fintype.card α₂ + 3) → β₂),
      IsChannel κ₁' ∧ IsChannel κ₂' ∧ btRate₁ P κ₁' κ₂' = btRate₁ P κ₁ κ₂ ∧
      btRate₂ P κ₁' κ₂' = btRate₂ P κ₁ κ₂ ∧ btRate₁₂ P κ₁' κ₂' = btRate₁₂ P κ₁ κ₂ ∧
      btCost₁ P κ₁' κ₂' d₁ f₁' ≤ btCost₁ P κ₁ κ₂ d₁ f₁ ∧
      btCost₂ P κ₁' κ₂' d₂ f₂' ≤ btCost₂ P κ₁ κ₂ d₂ f₂ := by
  -- Reduce `U₁`.
  obtain ⟨κ₁', g₁, g₂, hκ₁', eA, eC, c₁, c₂⟩ := exists_bt_reduce₁ hP h₁ h₂
    (fun x u v => d₁ x.1 (f₁ u v)) (fun x u v => d₂ x.2 (f₂ u v)) rfl
  have eB : I[Prod.snd : fun z : ((α₁ × Fin (Fintype.card α₁ + 3)) × α₂) × υ₂ => z.1.2 ;
      btLaw P κ₁' κ₂] = I[Prod.snd : fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.2 ; btLaw P κ₁ κ₂] := by
    rw [← mutualInfo_btJ₂ hκ₁', ← mutualInfo_btJ₂ h₁]
  -- Reduce `U₂`.
  obtain ⟨κ₂', g₃, g₄, hκ₂', eB', eC', c₃, c₄⟩ := exists_bt_reduce₂ hP hκ₁' h₂
    (fun x j v => d₁ x.1 (f₁ (g₁ j) v)) (fun x j v => d₂ x.2 (f₂ (g₂ j) v)) rfl
  have eA' : I[fun z : ((α₁ × Fin (Fintype.card α₁ + 3)) × α₂) × Fin (Fintype.card α₂ + 3) =>
      z.1.1.2 : fun z => z.1.1.1 ; btLaw P κ₁' κ₂'] =
      I[fun z : ((α₁ × Fin (Fintype.card α₁ + 3)) × α₂) × υ₂ => z.1.1.2 : fun z => z.1.1.1 ;
        btLaw P κ₁' κ₂] := by
    rw [← mutualInfo_btJ₁ hκ₂', ← mutualInfo_btJ₁ h₂]
  refine ⟨κ₁', κ₂', fun j l => f₁ (g₁ j) (g₃ l), fun j l => f₂ (g₂ j) (g₄ l), hκ₁', hκ₂', ?_, ?_,
    ?_, c₃.trans c₁, c₄.trans c₂⟩
  · rw [btRate₁_eq hP hκ₁' hκ₂', btRate₁_eq hP h₁ h₂, eA', eA, eC', eC]
  · rw [btRate₂_eq hP hκ₁' hκ₂', btRate₂_eq hP h₁ h₂, eB', eB, eC', eC]
  · rw [btRate₁₂_eq hP hκ₁' hκ₂', btRate₁₂_eq hP h₁ h₂, eA', eA, eB', eB, eC', eC]

/-- **The cardinality bound of Theorem 1 of Lecture 13 of [elgamal2010], page 13-4.** For every
`p(u₁ | x₁, q)`, `p(u₂ | x₂, q)`, `x̂₁(u₁, u₂, q)` and `x̂₂(u₁, u₂, q)` there are such laws and
functions with `|𝒰₁'| = |𝒳₁| + 3` and `|𝒰₂'| = |𝒳₂| + 3`, the same three rates for each `q`, and
no larger distortions for each `q`. So the inner bound holds over these smaller alphabets, by
`isAchievableDL_of_lt_sharing`. The notes have `|𝒳ⱼ| + 4`. -/
theorem exists_bt_sharing_card {Q : Type*} (hP : IsPMF P) {κ₁ : Q → α₁ → υ₁ → ℝ}
    {κ₂ : Q → α₂ → υ₂ → ℝ} (h₁ : ∀ q, IsChannel (κ₁ q)) (h₂ : ∀ q, IsChannel (κ₂ q))
    (d₁ : α₁ → β₁ → ℝ) (d₂ : α₂ → β₂ → ℝ) (f₁ : Q → υ₁ → υ₂ → β₁) (f₂ : Q → υ₁ → υ₂ → β₂) :
    ∃ (κ₁' : Q → α₁ → Fin (Fintype.card α₁ + 3) → ℝ)
      (κ₂' : Q → α₂ → Fin (Fintype.card α₂ + 3) → ℝ)
      (f₁' : Q → Fin (Fintype.card α₁ + 3) → Fin (Fintype.card α₂ + 3) → β₁)
      (f₂' : Q → Fin (Fintype.card α₁ + 3) → Fin (Fintype.card α₂ + 3) → β₂),
      (∀ q, IsChannel (κ₁' q)) ∧ (∀ q, IsChannel (κ₂' q)) ∧
      (∀ q, btRate₁ P (κ₁' q) (κ₂' q) = btRate₁ P (κ₁ q) (κ₂ q)) ∧
      (∀ q, btRate₂ P (κ₁' q) (κ₂' q) = btRate₂ P (κ₁ q) (κ₂ q)) ∧
      (∀ q, btRate₁₂ P (κ₁' q) (κ₂' q) = btRate₁₂ P (κ₁ q) (κ₂ q)) ∧
      (∀ q, btCost₁ P (κ₁' q) (κ₂' q) d₁ (f₁' q) ≤ btCost₁ P (κ₁ q) (κ₂ q) d₁ (f₁ q)) ∧
      (∀ q, btCost₂ P (κ₁' q) (κ₂' q) d₂ (f₂' q) ≤ btCost₂ P (κ₁ q) (κ₂ q) d₂ (f₂ q)) := by
  choose κ₁' κ₂' f₁' f₂' a₁ a₂ a₃ a₄ a₅ a₆ a₇ using fun q =>
    exists_bt_reduce hP (h₁ q) (h₂ q) d₁ d₂ (f₁ q) (f₂ q)
  exact ⟨κ₁', κ₂', f₁', f₂', a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩

end InfoTheory
