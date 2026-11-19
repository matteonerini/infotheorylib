/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.InfoInequalities.Groups

/-!
# Yeung, Chapter 16: Entropy and Groups

This file indexes the formalization of Chapter 16 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Groups.** Groups are Mathlib's multiplicative groups, and `|G|` is `Nat.card G`. The group of
  modulo 2 addition is `Multiplicative (ZMod 2)`, and a left coset `aS` is `a • (S : Set G)`.
* **Indexing.** The subgroups `G₁, …, Gₙ` are `H i` for `i : Fin n`, starting at `0`: the book's
  `G₁` is `H 0`. The intersection `G_α` is `subgroupInter H α`.
* **Universes.** The region `Υₙ` takes groups in the universe of the index type, as `Γ*ₙ` takes
  sample spaces. Theorem 16.22, Corollary 16.24 and the correspondence between information and
  group inequalities are stated for index types and groups in `Type`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Introduction
* (16.3)–(16.4): `card_mul_card_le_card_mul_card_inf` (`InfoInequalities.Groups`).
* (16.5): `card_inf_pow_mul_le_of_zhangYeung` (`InfoInequalities.Groups`).

### 16.1 Group Preliminaries
* Definition 16.1: Mathlib's `Group`.
* Proposition 16.2: `proposition_16_2` (here).
* Proposition 16.3: `proposition_16_3` (here), from Mathlib's `inv_eq_of_mul_eq_one_right`.
* Definition 16.4: Mathlib's `Nat.card`.
* Example 16.5: `example_16_5` (here).
* Example 16.6: `example_16_6` and `example_16_6_card` (here). The book's (16.27) gives
  `σ₂ ∘ σ₁ = (4, 1, 2, 3)`, but `σ₂ ∘ σ₁ = (4, 1, 3, 2)`; the two products still differ.
* Definition 16.7: Mathlib's `Subgroup`.
* Definition 16.8: the left coset `a • (S : Set G)`, with Mathlib's `mem_leftCoset_iff`.
* Proposition 16.9: `proposition_16_9` (here).
* Proposition 16.10: `proposition_16_10` (here), from Mathlib's `Set.ncard_smul_set`.
* Theorem 16.11 (Lagrange's Theorem): `theorem_16_11` (here), which is Mathlib's
  `Subgroup.card_subgroup_dvd_card`.
* Corollary 16.12: `corollary_16_12` (here).

### 16.2 Group-Characterizable Entropy Functions
* Proposition 16.13: `proposition_16_13` (here), which is Mathlib's `Subgroup.coe_inf`.
* Corollary 16.14: `subgroupInter`, `coe_subgroupInter` (`InfoInequalities.Groups`).
* Lemma 16.15: `lemma_16_15` (here), which is `ncard_iInter_smul_subgroup`
  (`InfoInequalities.Groups`).
* Theorem 16.16: `theorem_16_16` (here), which is `groupEntropy_mem_entropicRegion`
  (`InfoInequalities.Groups`). The entropy of a uniform `Λ` seen through its coset is
  `entropyRV_uniformPMF_of_card_fiber`.
* Definition 16.17: `groupEntropy` (`InfoInequalities.Groups`): `(G, G₁, …, Gₙ)` is a group
  characterization of `h` when `h = groupEntropy H`.
* Examples 16.18 and 16.19: `example_16_18`, `example_16_19` (here).
* Example 16.20: `example_16_20` (here), with `example1620Subgroup` (here); in nats
  `h_α = log 2 · min(|α|, 2)`, which is `log 2 • rankVector (Fin 3) 2`.

### 16.3 A Group Characterization of `Γ̄*ₙ`
* Definition 16.21: `groupCharRegion`, with `groupCharRegion_subset_entropicRegion` and
  `zero_mem_groupCharRegion` (`InfoInequalities.Groups`).
* Theorem 16.22: `theorem_16_22` (here), which is `exists_tendsto_smul_groupEntropy`
  (`InfoInequalities.Groups`). The proof does not approximate by rational distributions: for every
  `r` it takes a sequence of length `r` whose type is close to the distribution
  (`exists_typeOf_near`, `Statistics.Types`), and `|G| / |G_α|` is the size of the type class of
  its `α`-coordinates (`groupEntropy_permStab`, `card_typeClass_mul_card_permStab`,
  `InfoInequalities.Groups`). So the omitted details at the end of the book's proof are not
  needed.
* Lemma 16.23: `lemma_16_23` (here), which is `tendsto_log_multinomial`
  (`InfoInequalities.Groups`), through the bounds `log_card_typeClass_le` and
  `sub_le_log_card_typeClass`.
* Corollary 16.24: `corollary_16_24` (here), which is `closure_convexHull_groupCharRegion`
  (`InfoInequalities.Groups`).

### 16.4 Information Inequalities and Group Inequalities
* (16.84)–(16.89): `ineqAlwaysHolds_iff_groupEntropy` (`InfoInequalities.Groups`).
* Definition 16.25: Mathlib's pointwise product `(G₁ : Set G) * G₂`.
* Proposition 16.26: `proposition_16_26` (here), which is `card_mul_mul_card_inf`
  (`InfoInequalities.Groups`).
* Theorem 16.27: `theorem_16_27` (here), which is `card_inf_mul_card_inf_le`
  (`InfoInequalities.Groups`).
* Corollary 16.28: `corollary_16_28` (here), proved through the groups by (16.84)–(16.89) and
  Theorem 16.27.
* (16.114)–(16.116): `zyCoeff` (`InfoInequalities.NonShannon`) and
  `card_inf_pow_mul_le_of_zhangYeung` (`InfoInequalities.Groups`).

## Not formalized

* The four group axioms of Definition 16.1 and the check of them for Examples 16.5 and 16.6,
  which Mathlib's `Group` instances carry.
* The membership table and the strong typicality array of Figures 16.1 and 16.2, and the remark
  on quasi-uniform structures.
* The remark after Corollary 16.12 and the claim after Definition 16.25 that `G₁ ∘ G₂` is a
  subgroup when `G` is Abelian (Problem 1).
* The construction, before Definition 16.21, of an entropy function without a group
  characterization.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 16
-/

open Real Finset
open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-! ### 16.1 Group Preliminaries -/

section Preliminaries

variable {G : Type*} [Group G]

/-- **Proposition 16.2.** The identity element of a group is unique. -/
theorem proposition_16_2 {e : G} (h : ∀ a, a * e = a ∧ e * a = a) : e = 1 := by
  simpa using (h 1).2

/-- **Proposition 16.3.** The inverse of an element of a group is unique. -/
theorem proposition_16_3 {a b b' : G} (h : a * b = 1 ∧ b * a = 1) (h' : a * b' = 1 ∧ b' * a = 1) :
    b = b' := by
  rw [← inv_eq_of_mul_eq_one_right h.1, ← inv_eq_of_mul_eq_one_right h'.1]

/-- **Example 16.5 (Modulo 2 Addition).** The group of modulo 2 addition has order 2, and
`1 + 1 = 0`. -/
theorem example_16_5 : Nat.card (ZMod 2) = 2 ∧ (1 : ZMod 2) + 1 = 0 :=
  ⟨by simp, by decide⟩

/-- The permutation `σ₁ = (2, 1, 4, 3)` of (16.23), counting from `0`. -/
def example166σ₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The permutation `σ₂ = (1, 4, 2, 3)` of (16.24), counting from `0`. -/
def example166σ₂ : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 1 3

/-- **Example 16.6 (Symmetric Group).** `σ₁ ∘ σ₂ = (2, 3, 1, 4)` (16.26) and
`σ₂ ∘ σ₁ = (4, 1, 3, 2)`, so the symmetric group is not commutative. -/
theorem example_16_6 :
    ⇑(example166σ₁ * example166σ₂) = ![1, 2, 0, 3] ∧
      ⇑(example166σ₂ * example166σ₁) = ![3, 0, 2, 1] ∧
        example166σ₁ * example166σ₂ ≠ example166σ₂ * example166σ₁ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Example 16.6.** The symmetric group on `r` letters has order `r!`. -/
theorem example_16_6_card (r : ℕ) : Nat.card (Equiv.Perm (Fin r)) = r.factorial := by
  rw [Nat.card_perm, Nat.card_fin]

/-- **Proposition 16.9.** Two left cosets `a₁S` and `a₂S` are identical or disjoint, and they are
identical if and only if `a₁` and `a₂` belong to the same left coset. -/
theorem proposition_16_9 (S : Subgroup G) (a₁ a₂ : G) :
    (a₁ • (S : Set G) = a₂ • (S : Set G) ∨ Disjoint (a₁ • (S : Set G)) (a₂ • (S : Set G))) ∧
      (a₁ • (S : Set G) = a₂ • (S : Set G) ↔
        ∃ b : G, a₁ ∈ b • (S : Set G) ∧ a₂ ∈ b • (S : Set G)) := by
  refine ⟨?_, ⟨fun h => ⟨a₁, ?_, ?_⟩, fun ⟨b, h₁, h₂⟩ => ?_⟩⟩
  · by_cases h : a₁⁻¹ * a₂ ∈ S
    · exact Or.inl (leftCoset_eq_iff S |>.2 h)
    · refine Or.inr (Set.disjoint_left.2 fun x hx₁ hx₂ => h ?_)
      rw [mem_leftCoset_iff] at hx₁ hx₂
      rw [show a₁⁻¹ * a₂ = a₁⁻¹ * x * (a₂⁻¹ * x)⁻¹ by group]
      exact S.mul_mem hx₁ (S.inv_mem hx₂)
  · rw [mem_leftCoset_iff, inv_mul_cancel]
    exact S.one_mem
  · rw [h, mem_leftCoset_iff, inv_mul_cancel]
    exact S.one_mem
  · rw [mem_leftCoset_iff] at h₁ h₂
    refine leftCoset_eq_iff S |>.2 ?_
    rw [show a₁⁻¹ * a₂ = (b⁻¹ * a₁)⁻¹ * (b⁻¹ * a₂) by group]
    exact S.mul_mem (S.inv_mem h₁) h₂

/-- **Proposition 16.10.** `|aS| = |S|`. -/
theorem proposition_16_10 (S : Subgroup G) (a : G) : (a • (S : Set G)).ncard = Nat.card S := by
  rw [Set.ncard_smul_set]
  exact (Nat.card_coe_set_eq _).symm

/-- **Theorem 16.11 (Lagrange's Theorem).** The order of a subgroup divides the order of the
group. -/
alias theorem_16_11 := Subgroup.card_subgroup_dvd_card

/-- **Corollary 16.12.** The number of distinct left cosets of `S` is `|G| / |S|`. -/
theorem corollary_16_12 [Finite G] (S : Subgroup G) :
    Nat.card (G ⧸ S) = Nat.card G / Nat.card S := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup S, Nat.mul_div_cancel _ Nat.card_pos]

end Preliminaries

/-! ### 16.2 Group-Characterizable Entropy Functions -/

/-- **Proposition 16.13.** The intersection of two subgroups is a subgroup. -/
alias proposition_16_13 := Subgroup.coe_inf

/-- **Lemma 16.15.** `|⋂_{i ∈ α} aᵢGᵢ|` is `|G_α|` or `0`, (16.40). -/
alias lemma_16_15 := ncard_iInter_smul_subgroup

/-- **Theorem 16.16.** `h_α = log (|G| / |G_α|)` is entropic. -/
alias theorem_16_16 := groupEntropy_mem_entropicRegion

/-- **Example 16.19.** For `β ⊆ Nₙ`, the vector `h_α = log 2` if `α ∩ β ≠ ∅` and `0` otherwise has
the group characterization `Gᵢ = {0}` for `i ∈ β` and `Gᵢ = G` otherwise, in the group of
modulo 2 addition, (16.57)–(16.58). -/
theorem example_16_19 {ι : Type*} [DecidableEq ι] (β : Finset ι) :
    groupEntropy (fun i => if i ∈ β then (⊥ : Subgroup (Multiplicative (ZMod 2))) else ⊤) =
      fun α => if (α.val ∩ β).Nonempty then log 2 else 0 := by
  funext α
  have hG : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp [Nat.card_eq_fintype_card]
  rw [groupEntropy, hG]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [mem_inter] at hi
    have : subgroupInter (fun i => if i ∈ β then (⊥ : Subgroup (Multiplicative (ZMod 2)))
        else ⊤) α.val = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      have := mem_subgroupInter.1 hx i hi.1
      simpa [hi.2] using this
    rw [this, Subgroup.card_bot]
    norm_num
  · have : subgroupInter (fun i => if i ∈ β then (⊥ : Subgroup (Multiplicative (ZMod 2)))
        else ⊤) α.val = ⊤ := by
      refine eq_top_iff.2 fun x _ => mem_subgroupInter.2 fun i hi => ?_
      have : i ∉ β := fun hb => h ⟨i, mem_inter.2 ⟨hi, hb⟩⟩
      simp [this]
    rw [this, Subgroup.card_top, hG]
    norm_num

/-- **Example 16.18.** The case `n = 3` of Example 16.19, (16.50)–(16.56). -/
theorem example_16_18 (β : Finset (Fin 3)) :
    groupEntropy (fun i => if i ∈ β then (⊥ : Subgroup (Multiplicative (ZMod 2))) else ⊤) =
      fun α => if (α.val ∩ β).Nonempty then log 2 else 0 :=
  example_16_19 β

/-- The subgroups `G₁ = {(0, 0), (1, 0)}`, `G₂ = {(0, 0), (0, 1)}` and `G₃ = {(0, 0), (1, 1)}` of
`F × F` in Example 16.20, as the kernels of the second coordinate, the first coordinate and the
sum. -/
def example1620Subgroup : Fin 3 → Subgroup (Multiplicative (ZMod 2 × ZMod 2)) :=
  ![(AddMonoidHom.snd (ZMod 2) (ZMod 2)).toMultiplicative.ker,
    (AddMonoidHom.fst (ZMod 2) (ZMod 2)).toMultiplicative.ker,
    (AddMonoidHom.fst (ZMod 2) (ZMod 2) + AddMonoidHom.snd (ZMod 2) (ZMod 2)).toMultiplicative.ker]

/-- **Example 16.20.** `(F × F, G₁, G₂, G₃)` is a group characterization of
`h_α = min(|α|, 2)` bits, (16.59)–(16.62). -/
theorem example_16_20 : groupEntropy example1620Subgroup = log 2 • rankVector (Fin 3) 2 := by
  classical
  -- the membership conditions of the three subgroups
  set c : Fin 3 → ZMod 2 × ZMod 2 → ZMod 2 := ![fun v => v.2, fun v => v.1, fun v => v.1 + v.2]
  have hmem : ∀ i x, x ∈ example1620Subgroup i ↔ c i (Multiplicative.toAdd x) = 0 := by
    intro i x
    fin_cases i <;> simp [example1620Subgroup, c, MonoidHom.mem_ker, AddSubgroup.mem_prod,
      ← ofAdd_add]
  have hcount : ∀ s : Finset (Fin 3), s.Nonempty →
      #(univ.filter fun x : Multiplicative (ZMod 2 × ZMod 2) =>
        ∀ i ∈ s, c i (Multiplicative.toAdd x) = 0) = if #s = 1 then 2 else 1 := by
    decide
  have hcard : ∀ s : Finset (Fin 3), s.Nonempty →
      Nat.card (subgroupInter example1620Subgroup s) = if #s = 1 then 2 else 1 := by
    intro s hs
    rw [← hcount s hs, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [mem_subgroupInter]
      exact forall₂_congr fun i _ => hmem i x)
  have hG : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by simp [Nat.card_eq_fintype_card]
  funext α
  rw [groupEntropy, hcard α.val α.property, hG, Pi.smul_apply, rankVector, smul_eq_mul]
  have hle : #α.val ≤ 3 := by simpa using card_le_univ α.val
  have hpos : 0 < #α.val := card_pos.2 α.property
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  interval_cases h : #α.val <;> norm_num [h4] <;> ring

/-! ### 16.3 A Group Characterization of `Γ̄*ₙ` -/

/-- **Theorem 16.22.** For any `h ∈ Γ*ₙ` there is a sequence `f(r) ∈ Υₙ` with `f(r) / r → h`. -/
alias theorem_16_22 := exists_tendsto_smul_groupEntropy

/-- **Lemma 16.23.** `(1 / r) log (r! / ∏ₓ (r p(x))!) → H(X)` for a rational distribution with
denominator `q`, as `r = q, 2q, 3q, …`. -/
alias lemma_16_23 := tendsto_log_multinomial

/-- **Corollary 16.24.** `con(Υₙ) = Γ̄*ₙ`. -/
alias corollary_16_24 := closure_convexHull_groupCharRegion

/-! ### 16.4 Information Inequalities and Group Inequalities -/

/-- **Proposition 16.26.** `|G₁ ∘ G₂| = |G₁| |G₂| / |G₁ ∩ G₂|`, (16.91). -/
alias proposition_16_26 := card_mul_mul_card_inf

/-- **Theorem 16.27.** `|G₃| |G₁₂₃| ≥ |G₁₃| |G₂₃|`, (16.104). -/
alias theorem_16_27 := card_inf_mul_card_inf_le

/-- **Corollary 16.28.** `I(X₁; X₂ | X₃) ≥ 0` always holds, proved through the group inequality of
Theorem 16.27 by (16.84)–(16.89), (16.109)–(16.113). -/
theorem corollary_16_28 :
    IneqAlwaysHolds (canonicalForm (condInfoFunctional ({0} : Finset (Fin 3)) {1} {2}))
      Set.univ := by
  rw [ineqAlwaysHolds_iff_groupEntropy]
  intro G _ _ H
  rw [infoExpr_canonicalForm, condInfoFunctional_apply, condInfo_eq_of _ (S := {0}) (T := {1})
    (K := {2}) (U₁ := {0, 2}) (U₂ := {1, 2}) (U₃ := {0, 1, 2}) (by decide) (by decide)
    (by decide)]
  simp only [extend_groupEntropy, subgroupInter_insert, subgroupInter_singleton, ← inf_assoc]
  have hp : ∀ K : Subgroup G, (0 : ℝ) < Nat.card K := fun K => by exact_mod_cast Nat.card_pos
  have h : ((Nat.card (H 0 ⊓ H 2 : Subgroup G) * Nat.card (H 1 ⊓ H 2 : Subgroup G) : ℕ) : ℝ) ≤
      ((Nat.card (H 2) * Nat.card (H 0 ⊓ H 1 ⊓ H 2 : Subgroup G) : ℕ) : ℝ) := by
    exact_mod_cast card_inf_mul_card_inf_le (H 0) (H 1) (H 2)
  push_cast at h
  have hl := log_le_log (mul_pos (hp _) (hp _)) h
  rw [log_mul (hp _).ne' (hp _).ne', log_mul (hp _).ne' (hp _).ne'] at hl
  linarith

end InfoTheory.Yeung
