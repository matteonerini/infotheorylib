/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DFDegraded

/-!
# Deterministic networks

In a deterministic network the outputs are functions of the inputs. The information across a cut is
`H(Y(Sᶜ) | X(Sᶜ))`, and noisy network coding with `Ŷ_k = Y_k` achieves it for independent inputs.

## Main definitions

* `detW f`: the channel of the network with outputs `f xᴺ`.

## Main statements

* `cutInfo_detW`: the information across a cut is `H(Y(Sᶜ) | X(Sᶜ))`.
* `nncInfo_detW`: the noisy network coding bound with `Ŷ_k = Y_k` is the information across the cut.
* `isAchievableMN_det`, `isAchievableDMN_det`: **the lower bounds of pages 19-19 and 19-41**.
* `mnCapacity_det_eq`: the capacity, when one product law maximizes the information across all the
  cuts.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section General

variable {Ω Ω' a c : Type*} [Fintype Ω] [Fintype Ω'] [Fintype a] [Fintype c]

/-- A conditional entropy under the law of a function. -/
lemma condEntropy_dist_comp {μ : Ω → ℝ} (hμ : IsPMF μ) (g : Ω → Ω') (A : Ω' → a) (C : Ω' → c) :
    H[A | C ; dist μ g] = H[A ∘ g | C ∘ g ; μ] := by
  refine condEntropy_eq_of_dist_pair_eq (hμ.dist g) hμ ?_
  rw [← dist_comp_eq]
  rfl

end General

section Det

variable {N : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]

/-- **Page 19-19 of [elgamal2010].** The channel of a deterministic network. -/
def detW (f : (∀ k, X k) → ∀ k, Y k) (x : ∀ k, X k) (y : ∀ k, Y k) : ℝ := ind (y = f x)

variable {f : (∀ k, X k) → ∀ k, Y k}

omit [∀ k, Fintype (X k)] in
lemma detW_isChannel : IsChannel (detW (X := X) (Y := Y) f) := by
  classical
  intro x
  refine ⟨fun y => ind_nonneg _, ?_⟩
  simp only [detW]
  rw [Finset.sum_eq_single (f x)]
  · exact ind_of_pos rfl
  · exact fun y _ hy => ind_of_neg hy
  · simp

omit [∀ k, Fintype (Y k)] in
/-- The joint law of a deterministic network is the law of a function of the input. -/
lemma jointOf_detW (p : (∀ k, X k) → ℝ) :
    jointOf p (detW f) = dist p fun x => (x, f x) := by
  classical
  funext ⟨x, y⟩
  simp only [jointOf, detW, dist, Prod.mk.injEq]
  rw [Finset.sum_eq_single x]
  · by_cases h : y = f x
    · simp [ind, h]
    · simp [ind, h, Ne.symm h]
  · intro x' _ hx'
    exact ite_eq_right fun h => absurd h.1 hx'
  · simp

/-- **Page 19-19 of [elgamal2010].** The information across a cut of a deterministic network is
`H(Y(Sᶜ) | X(Sᶜ))`. -/
theorem cutInfo_detW {p : (∀ k, X k) → ℝ} (hp : IsPMF p) (S : Finset (Fin N)) :
    cutInfo p (detW f) S = H[fun x => restr Sᶜ (f x) | restr Sᶜ ; p] := by
  classical
  have hL : IsPMF (jointOf p (detW f)) := jointOf_isPMF hp detW_isChannel
  rw [cutInfo, condMutualInfo_comm hL, condMutualInfo_eq' hL, jointOf_detW,
    condEntropy_dist_comp hp, condEntropy_dist_comp hp]
  have h₁ : H[(fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.2) ∘ fun x => (x, f x) |
      (pair (fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.1) fun z => restr S z.1) ∘
        fun x => (x, f x) ; p] = 0 := by
    have e : H[(fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.2) ∘ fun x => (x, f x) |
        (pair (fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.1) fun z => restr S z.1) ∘
          fun x => (x, f x) ; p] =
        H[(fun x => restr Sᶜ (f x)) ∘ id | id ; p] :=
      condEntropy_congr_right hp _ (fun x : ∀ k, X k => (restr Sᶜ x, restr S x))
        (restr_compl_restr_injective S) fun _ => rfl
    rw [e]
    exact condEntropy_comp_self hp id fun x => restr Sᶜ (f x)
  rw [h₁, sub_zero]
  rfl

variable (X Y) in
/-- The compression `Ŷ_k = Y_k`. -/
def detTau (k : Fin N) (t : X k × Y k) (v : Y k) : ℝ := ind (v = t.2)

omit [∀ k, Fintype (X k)] in
lemma detTau_isChannel (k : Fin N) : IsChannel (detTau X Y k) := by
  classical
  intro t
  refine ⟨fun v => ind_nonneg _, ?_⟩
  simp only [detTau]
  rw [Finset.sum_eq_single t.2]
  · exact ind_of_pos rfl
  · exact fun v _ hv => ind_of_neg hv
  · simp

omit [∀ k, Fintype (Y k)] in
/-- The law of noisy network coding with `Ŷ_k = Y_k` is the law of a function of the input. -/
lemma nncLaw_detW (px : ∀ k, X k → ℝ) :
    nncLaw (V := Y) px (detW f) (detTau X Y) = dist (prodLaw px) fun x => (x, f x, f x) := by
  classical
  funext ⟨x, y, v⟩
  simp only [nncLaw, detW, detTau, dist, Prod.mk.injEq]
  rw [Finset.sum_eq_single x]
  · have hprod : ∏ k, ind (v k = y k) = ind (v = y) := by
      by_cases h : v = y
      · rw [ind_of_pos h]
        exact prod_eq_one fun k _ => ind_of_pos (congrFun h k)
      · rw [ind_of_neg h]
        obtain ⟨k, hk⟩ := Function.ne_iff.mp h
        exact prod_eq_zero (mem_univ k) (ind_of_neg hk)
    simp only [hprod]
    by_cases h : y = f x ∧ v = f x
    · rw [ind_of_pos h.1, ind_of_pos (h.2.trans h.1.symm), mul_one, mul_one,
        ite_eq_left ⟨trivial, h.1.symm, h.2.symm⟩]
      rfl
    · rw [ite_eq_right fun h' => h ⟨h'.2.1.symm, h'.2.2.symm⟩]
      by_cases h₁ : y = f x
      · have h₂ : ¬ v = y := fun e => h ⟨h₁, e.trans h₁⟩
        rw [ind_of_neg h₂, mul_zero]
      · rw [ind_of_neg h₁, mul_zero, zero_mul]
  · intro x' _ hx'
    exact ite_eq_right fun h => absurd h.1 hx'
  · simp

/-- **Page 19-19 of [elgamal2010].** With `Ŷ_k = Y_k`, the noisy network coding bound is the
information across the cut. -/
theorem nncInfo_detW {px : ∀ k, X k → ℝ} (hpx : ∀ k, IsPMF (px k)) (S : Finset (Fin N)) {d : Fin N}
    (hd : d ∉ S) :
    nncInfo (nncLaw (V := Y) px (detW f) (detTau X Y)) S d = cutInfo (prodLaw px) (detW f) S := by
  classical
  have hp := prodLaw_isPMF hpx
  have hdc : d ∈ Sᶜ := mem_compl.mpr hd
  set g : (∀ k, X k) → NNCΩ X Y Y := fun x => (x, f x, f x) with hg
  have hjoint := jointOf_detW (f := f) (prodLaw px)
  rw [nncInfo, nncLaw_detW, cutInfo, hjoint]
  simp only [condMutualInfo]
  rw [condEntropy_dist_comp hp, condEntropy_dist_comp hp, condEntropy_dist_comp hp,
    condEntropy_dist_comp hp, condEntropy_dist_comp hp, condEntropy_dist_comp hp]
  -- the second information is zero
  have h₁ : H[(fun ω : NNCΩ X Y Y => restr S ω.2.1) ∘ g |
      (fun ω : NNCΩ X Y Y => ((ω.1, restr Sᶜ ω.2.2), ω.2.1 d)) ∘ g ; prodLaw px] = 0 := by
    have e : (fun ω : NNCΩ X Y Y => restr S ω.2.1) ∘ g =
        (fun t : ((∀ k, X k) × ∀ k : (Sᶜ : Finset (Fin N)), Y k) × Y d => restr S (f t.1.1)) ∘
          ((fun ω : NNCΩ X Y Y => ((ω.1, restr Sᶜ ω.2.2), ω.2.1 d)) ∘ g) := rfl
    rw [e]
    exact condEntropy_comp_self hp _ _
  have h₂ : H[(fun ω : NNCΩ X Y Y => restr S ω.2.1) ∘ g |
      (pair (fun ω : NNCΩ X Y Y => restr S ω.2.2)
        fun ω => ((ω.1, restr Sᶜ ω.2.2), ω.2.1 d)) ∘ g ; prodLaw px] = 0 := by
    have e : (fun ω : NNCΩ X Y Y => restr S ω.2.1) ∘ g =
        (fun t : (∀ k : S, Y k) × ((∀ k, X k) × ∀ k : (Sᶜ : Finset (Fin N)), Y k) × Y d =>
          restr S (f t.2.1.1)) ∘
          ((pair (fun ω : NNCΩ X Y Y => restr S ω.2.2)
            fun ω => ((ω.1, restr Sᶜ ω.2.2), ω.2.1 d)) ∘ g) := rfl
    rw [e]
    exact condEntropy_comp_self hp _ _
  rw [h₁, h₂, sub_zero, sub_zero]
  -- the first information
  congr 1
  refine condEntropy_congr_right hp _
    (fun t : (∀ k : (Sᶜ : Finset (Fin N)), Y k) × ∀ k : (Sᶜ : Finset (Fin N)), X k =>
      ((t.1, t.1 ⟨d, hdc⟩), t.2)) (fun a b h => ?_) fun x => rfl
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1.1 h.2

/-- **Page 19-19 of [elgamal2010].** The lower bound for a deterministic multicast network: for
independent inputs, the rate `R` is achievable if `R < H(Y(Sᶜ) | X(Sᶜ))` for all the cuts. -/
theorem isAchievableMN_det {px : ∀ k, X k → ℝ} (hpx : ∀ k, IsPMF (px k)) {s : Fin N}
    {D : Finset (Fin N)} {R : ℝ} (hR : 0 ≤ R)
    (hrate : ∀ d ∈ D, ∀ S : Finset (Fin N), s ∈ S → d ∉ S →
      R * log 2 < cutInfo (prodLaw px) (detW f) S) :
    IsAchievableMN (detW f) s D R := by
  refine isAchievableMN_nnc (V := Y) (τ := detTau X Y) hpx detW_isChannel detTau_isChannel hR
    fun d hd S hs hdS => ?_
  rw [nncInfo_detW hpx S hdS]
  exact hrate d hd S hs hdS

/-- **Page 19-41 of [elgamal2010].** The inner bound for a deterministic network with many sources:
for independent inputs, the rates are achievable if `∑_{k ∈ S} R_k < H(Y(Sᶜ) | X(Sᶜ))` for all the
cuts with a destination in `Sᶜ`. -/
theorem isAchievableDMN_det {px : ∀ k, X k → ℝ} (hpx : ∀ k, IsPMF (px k))
    {D : Fin N → Finset (Fin N)} {R : Fin N → ℝ} (hR0 : ∀ k, 0 ≤ R k)
    (hrate : ∀ d ∈ univ.biUnion D, ∀ S : Finset (Fin N), d ∉ S → (∃ k ∈ S, 0 < R k) →
      (∑ k ∈ S, R k) * log 2 < cutInfo (prodLaw px) (detW f) S) :
    IsAchievableDMN (detW f) D R := by
  refine isAchievableDMN_nnc (V := Y) (τ := detTau X Y) hpx detW_isChannel detTau_isChannel hR0
    fun d hd S hdS hS => ?_
  rw [nncInfo_detW hpx S hdS]
  exact hrate d hd S hdS hS

/-- **Page 19-19 of [elgamal2010].** If one product law maximizes the information across all the
cuts, the cutset bound is tight: the capacity is the smallest information across a cut. -/
theorem mnCapacity_det_eq [∀ k, Nonempty (X k)] {px : ∀ k, X k → ℝ} (hpx : ∀ k, IsPMF (px k))
    {s : Fin N} {D : Finset (Fin N)} (hD : ∀ k ∈ D, s ≠ k)
    (hmax : ∀ p : (∀ k, X k) → ℝ, IsPMF p → ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S → k ∉ S →
      cutInfo p (detW f) S ≤ cutInfo (prodLaw px) (detW f) S)
    {c : ℝ} (hc : ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S → k ∉ S →
      c ≤ cutInfo (prodLaw px) (detW f) S)
    {k₀ : Fin N} {S₀ : Finset (Fin N)} (hk₀ : k₀ ∈ D) (hS₀ : s ∈ S₀) (hkS₀ : k₀ ∉ S₀)
    (hc₀ : cutInfo (prodLaw px) (detW f) S₀ = c) :
    mnCapacity (detW f) s D * log 2 = c := by
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hW := detW_isChannel (X := X) (Y := Y) (f := f)
  have hbdd := bddAbove_isAchievableMN hW hk₀ (hD k₀ hk₀)
  have hC0 : 0 ≤ mnCapacity (detW f) s D := le_csSup hbdd (isAchievableMN_zero s D)
  have hc0 : 0 ≤ c := hc₀ ▸ cutInfo_nonneg (prodLaw_isPMF hpx) hW S₀
  refine le_antisymm ?_ ?_
  · rw [← le_div_iff₀ hlog]
    refine Real.sSup_le (fun R hR => ?_) (div_nonneg hc0 hlog.le)
    rw [le_div_iff₀ hlog]
    obtain ⟨p, hp, hle⟩ := IsAchievableMN.exists_cutset hW hR
    exact (hle k₀ hk₀ S₀ hS₀ hkS₀).trans ((hmax p hp k₀ hk₀ S₀ hS₀ hkS₀).trans_eq hc₀)
  · rw [← div_le_iff₀ hlog]
    refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
    by_cases hR0 : 0 ≤ R
    · refine le_csSup hbdd (isAchievableMN_det hpx hR0 fun d hd S hs hdS => ?_)
      exact ((lt_div_iff₀ hlog).mp hR).trans_le (hc d hd S hs hdS)
    · exact (not_le.mp hR0).le.trans hC0

end Det

end InfoTheory
