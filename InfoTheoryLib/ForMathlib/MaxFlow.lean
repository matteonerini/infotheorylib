/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib

/-!
# The max-flow min-cut theorem

Flows on a finite set of nodes, with values in an ordered ring, cuts, and the max-flow min-cut
theorem of Ford and Fulkerson, for real and for integer capacities.

## Main definitions

* `netOut f k`: the flow out of node `k` minus the flow into it.
* `cutCap c S`: the capacity of the cut `S`.
* `IsFlow c s t f v`: `f` is a flow from `s` to `t` of value `v`.
* `minCut c s t`: the capacity of a minimum cut, for real capacities.

## Main statements

* `IsFlow.le_cutCap`: the value of a flow is at most the capacity of any cut.
* `maxFlow_minCut`: for real capacities, the largest value of a flow is the minimum cut.
* `exists_intFlow`: for integer capacities, every integer up to the minimum cut is the value of an
  integer flow.
* `exists_supplyFlow`: the same with several sources, by adding a source of all sources.

## Implementation notes

The proof is by augmenting paths. A simple path is the inductive predicate `SPath`, whose index is
the set of nodes it has to avoid, so no lists are needed. No acyclicity is assumed here.
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {V R : Type*} [Fintype V] [DecidableEq V]

/-! ### Net flow and cuts -/

section Ring

variable [CommRing R]

/-- The flow out of node `k` minus the flow into it. -/
def netOut (f : V → V → R) (k : V) : R := ∑ l, f k l - ∑ j, f j k

/-- **Lecture 16 of [elgamal2010], page 16-5.** The capacity `C(S) = ∑_{j ∈ S, k ∈ Sᶜ} C_jk` of the
cut `S`. A pair that is not an edge has capacity `0`. -/
def cutCap (c : V → V → R) (S : Finset V) : R := ∑ j ∈ S, ∑ k ∈ Sᶜ, c j k

/-- The net flow out of a set of nodes is the flow across the cut minus the flow back. -/
lemma sum_netOut (f : V → V → R) (S : Finset V) :
    ∑ k ∈ S, netOut f k = cutCap f S - ∑ j ∈ S, ∑ k ∈ Sᶜ, f k j := by
  have h₁ : ∀ k, ∑ l, f k l = ∑ l ∈ S, f k l + ∑ l ∈ Sᶜ, f k l :=
    fun k => (Finset.sum_add_sum_compl S _).symm
  have h₂ : ∀ k, ∑ j, f j k = ∑ j ∈ S, f j k + ∑ j ∈ Sᶜ, f j k :=
    fun k => (Finset.sum_add_sum_compl S _).symm
  simp only [netOut, cutCap, h₁, h₂, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := S) (t := S) (f := fun k j => f j k)]
  ring

/-- Adding `δ` on the pair `(a, b)` changes the net flow at `a` and `b` only. -/
lemma netOut_add_single (f : V → V → R) (a b : V) (δ : R) (k : V) :
    netOut (fun j l => f j l + if j = a ∧ l = b then δ else 0) k =
      netOut f k + (if k = a then δ else 0) - (if k = b then δ else 0) := by
  have h₁ : ∑ l, (if k = a ∧ l = b then δ else 0) = if k = a then δ else 0 := by
    by_cases hk : k = a <;> simp [hk]
  have h₂ : ∑ j, (if j = a ∧ k = b then δ else 0) = if k = b then δ else 0 := by
    by_cases hk : k = b <;> simp [hk]
  simp only [netOut, Finset.sum_add_distrib, h₁, h₂]
  ring

end Ring

/-! ### Flows and weak duality -/

section Order

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A flow from `s` to `t` of value `v`: the rate allocation of page 16-7 of [elgamal2010]. -/
structure IsFlow (c : V → V → R) (s t : V) (f : V → V → R) (v : R) : Prop where
  /-- Rates are nonnegative. -/
  nonneg : ∀ j k, 0 ≤ f j k
  /-- Rates are at most the capacities. -/
  le_cap : ∀ j k, f j k ≤ c j k
  /-- What comes into a relay node goes out of it. -/
  cons : ∀ k, k ≠ s → k ≠ t → netOut f k = 0
  /-- The value of the flow. -/
  value : netOut f s = v

omit [DecidableEq V] [IsStrictOrderedRing R] in
lemma IsFlow.sum_netOut_eq {c : V → V → R} {s t : V} {f : V → V → R} {v : R}
    (hf : IsFlow c s t f v) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    ∑ k ∈ S, netOut f k = v := by
  rw [Finset.sum_eq_single_of_mem s hs fun k hk hks =>
    hf.cons k hks (fun h => ht (h ▸ hk)), hf.value]

/-- **Weak duality.** The value of a flow is at most the capacity of any cut. -/
theorem IsFlow.le_cutCap {c : V → V → R} {s t : V} {f : V → V → R} {v : R}
    (hf : IsFlow c s t f v) {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) : v ≤ cutCap c S := by
  rw [← hf.sum_netOut_eq hs ht, sum_netOut]
  have h₁ : cutCap f S ≤ cutCap c S :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hf.le_cap j k
  have h₂ : 0 ≤ ∑ j ∈ S, ∑ k ∈ Sᶜ, f k j :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hf.nonneg k j
  linarith

/-! ### Simple paths -/

/-- `SPath r t A u`: there is a simple path for the relation `r` from `u` to `t` that avoids the
nodes of `A`. -/
inductive SPath (r : V → V → Prop) (t : V) : Finset V → V → Prop
  | nil {A : Finset V} : t ∉ A → SPath r t A t
  | cons {A : Finset V} {u w : V} : u ∉ A → r u w → SPath r t (insert u A) w → SPath r t A u

omit [Fintype V] in
lemma SPath.not_mem {r : V → V → Prop} {t : V} {A : Finset V} {u : V} (h : SPath r t A u) :
    u ∉ A := by
  cases h with
  | nil h => exact h
  | cons h _ _ => exact h

omit [Fintype V] in
lemma SPath.mono {r : V → V → Prop} {t : V} {A : Finset V} {u : V} (h : SPath r t A u) :
    ∀ {B : Finset V}, B ⊆ A → SPath r t B u := by
  induction h with
  | nil h => exact fun hB => SPath.nil fun ht => h (hB ht)
  | cons h₁ h₂ _ ih =>
    exact fun hB => SPath.cons (fun hu => h₁ (hB hu)) h₂ (ih (Finset.insert_subset_insert _ hB))

omit [Fintype V] in
/-- A simple path from `w` either avoids `u` or has a suffix starting at `u`. -/
lemma SPath.avoid_or {r : V → V → Prop} {t : V} {A : Finset V} {w : V} (h : SPath r t A w)
    {u : V} : u ∉ A → SPath r t (insert u A) w ∨ SPath r t A u := by
  induction h with
  | @nil A h =>
    intro hu
    by_cases hut : u = t
    · exact Or.inr (by rw [hut]; exact SPath.nil h)
    · refine Or.inl (SPath.nil ?_)
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h' => hut h'.symm, h⟩
  | @cons A w w' h₁ h₂ h₃ ih =>
    intro hu
    by_cases huw : u = w
    · exact Or.inr (by rw [huw]; exact SPath.cons h₁ h₂ h₃)
    · have hu' : u ∉ insert w A := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨huw, hu⟩
      rcases ih hu' with h | h
      · refine Or.inl (SPath.cons ?_ h₂ ?_)
        · simp only [Finset.mem_insert, not_or]
          exact ⟨fun h' => huw h'.symm, h₁⟩
        · rwa [Finset.insert_comm]
      · exact Or.inr (h.mono (Finset.subset_insert _ _))

omit [Fintype V] in
/-- If `t` is reachable from `u` then there is a simple path. -/
lemma exists_sPath {r : V → V → Prop} {u t : V} (h : Relation.ReflTransGen r u t) :
    SPath r t ∅ u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact SPath.nil (by simp)
  | @head a c hac _ ih =>
    rcases ih.avoid_or (u := a) (by simp) with h | h
    · exact SPath.cons (by simp) hac h
    · exact h

/-! ### Augmenting paths -/

/-- The pair `(j, k)` can take `δ` more units: forward if `f j k + δ ≤ c j k`, and by cancelling
flow if `δ ≤ f k j`. -/
def ResEdge (c f : V → V → R) (δ : R) (j k : V) : Prop := f j k + δ ≤ c j k ∨ δ ≤ f k j

/-- Pushing `δ` along a simple residual path changes the net flow at its two ends only. -/
lemma exists_push {c f : V → V → R} {δ : R} (hδ : 0 < δ) (h0 : ∀ j k, 0 ≤ f j k)
    (hc : ∀ j k, f j k ≤ c j k) {t : V} {A : Finset V} {u : V}
    (h : SPath (ResEdge c f δ) t A u) :
    ∃ f' : V → V → R, (∀ j k, 0 ≤ f' j k) ∧ (∀ j k, f' j k ≤ c j k) ∧
      (∀ k, netOut f' k = netOut f k + (if k = u then δ else 0) - (if k = t then δ else 0)) ∧
      ∀ a ∈ A, ∀ b, f' a b = f a b ∧ f' b a = f b a := by
  induction h with
  | nil _ =>
    exact ⟨f, h0, hc, fun k => by ring, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | @cons A u w hu hr hp ih =>
    obtain ⟨f', h0', hc', hn', ha'⟩ := ih
    have huw : u ≠ w := fun h => hp.not_mem (h ▸ Finset.mem_insert_self _ _)
    have hwA : w ∉ A := fun h => hp.not_mem (Finset.mem_insert_of_mem h)
    have hne : ∀ a ∈ A, a ≠ u ∧ a ≠ w :=
      fun a ha => ⟨fun h => hu (h ▸ ha), fun h => hwA (h ▸ ha)⟩
    obtain ⟨huw₁, huw₂⟩ := ha' u (Finset.mem_insert_self _ _) w
    rcases hr with hr | hr
    · refine ⟨fun j l => f' j l + if j = u ∧ l = w then δ else 0, ?_, ?_, ?_, ?_⟩
      · intro j k
        have := h0' j k
        dsimp only
        split_ifs <;> linarith
      · intro j k
        dsimp only
        split_ifs with hjk
        · obtain ⟨rfl, rfl⟩ := hjk
          rw [huw₁]
          exact hr
        · simpa using hc' j k
      · intro k
        rw [netOut_add_single, hn' k]
        ring
      · intro a ha b
        obtain ⟨h₁, h₂⟩ := ha' a (Finset.mem_insert_of_mem ha) b
        obtain ⟨h₃, h₄⟩ := hne a ha
        simp [h₁, h₂, h₃, h₄]
    · refine ⟨fun j l => f' j l + if j = w ∧ l = u then -δ else 0, ?_, ?_, ?_, ?_⟩
      · intro j k
        dsimp only
        split_ifs with hjk
        · obtain ⟨rfl, rfl⟩ := hjk
          rw [huw₂]
          linarith
        · simpa using h0' j k
      · intro j k
        have := hc' j k
        dsimp only
        split_ifs <;> linarith
      · intro k
        rw [netOut_add_single, hn' k]
        split_ifs <;> ring
      · intro a ha b
        obtain ⟨h₁, h₂⟩ := ha' a (Finset.mem_insert_of_mem ha) b
        obtain ⟨h₃, h₄⟩ := hne a ha
        simp [h₁, h₂, h₃, h₄]

/-- Either a flow saturates a cut or it can be augmented by `δ`, if `δ` is at most every positive
residual capacity. -/
theorem IsFlow.eq_cut_or_augment {c : V → V → R} {s t : V} {f : V → V → R} {v δ : R}
    (hf : IsFlow c s t f v) (hst : s ≠ t) (hδ : 0 < δ)
    (h₁ : ∀ j k, f j k < c j k → f j k + δ ≤ c j k) (h₂ : ∀ j k, 0 < f j k → δ ≤ f j k) :
    (∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ v = cutCap c S) ∨ ∃ f', IsFlow c s t f' (v + δ) := by
  classical
  by_cases hr : Relation.ReflTransGen (ResEdge c f δ) s t
  · refine Or.inr ?_
    obtain ⟨f', h0', hc', hn', -⟩ := exists_push hδ hf.nonneg hf.le_cap (exists_sPath hr)
    refine ⟨f', h0', hc', fun k hks hkt => ?_, ?_⟩
    · rw [hn' k, hf.cons k hks hkt]
      simp [hks, hkt]
    · rw [hn' s, hf.value]
      simp [hst]
  · refine Or.inl ⟨Finset.univ.filter (Relation.ReflTransGen (ResEdge c f δ) s), by
      simpa using Relation.ReflTransGen.refl, by simpa using hr, ?_⟩
    set S := Finset.univ.filter (Relation.ReflTransGen (ResEdge c f δ) s) with hS
    have hnot : ∀ j ∈ S, ∀ k ∈ Sᶜ, ¬ ResEdge c f δ j k := by
      intro j hj k hk hjk
      simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
      exact hk (hj.tail hjk)
    have hsS : s ∈ S := by simpa [hS] using Relation.ReflTransGen.refl
    have htS : t ∉ S := by simpa [hS] using hr
    rw [← hf.sum_netOut_eq hsS htS, sum_netOut]
    have hsat : cutCap f S = cutCap c S := by
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
      have hn := hnot j hj k hk
      simp only [ResEdge, not_or, not_le] at hn
      refine le_antisymm (hf.le_cap j k) (not_lt.mp fun h => ?_)
      have := h₁ j k h
      linarith [hn.1]
    have hback : ∑ j ∈ S, ∑ k ∈ Sᶜ, f k j = 0 := by
      refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk => ?_
      have hn := hnot j hj k hk
      simp only [ResEdge, not_or, not_le] at hn
      refine le_antisymm (not_lt.mp fun h => ?_) (hf.nonneg k j)
      have := h₂ k j h
      linarith [hn.2]
    rw [hsat, hback, sub_zero]

end Order

/-! ### Integer capacities -/

/-- **Max-flow min-cut for integer capacities.** Every natural number up to the capacity of every
cut is the value of an integer flow. -/
theorem exists_intFlow {c : V → V → ℤ} (hc : ∀ j k, 0 ≤ c j k) {s t : V} (hst : s ≠ t) (v : ℕ)
    (h : ∀ S : Finset V, s ∈ S → t ∉ S → (v : ℤ) ≤ cutCap c S) :
    ∃ f, IsFlow c s t f v := by
  induction v with
  | zero =>
    refine ⟨fun _ _ => 0, fun _ _ => le_rfl, hc, fun _ _ _ => by simp [netOut], by simp [netOut]⟩
  | succ v ih =>
    obtain ⟨f, hf⟩ := ih fun S hs ht => by
      have := h S hs ht
      push_cast at this
      linarith
    rcases hf.eq_cut_or_augment hst one_pos (fun _ _ h => h) (fun _ _ h => h) with
      ⟨S, hs, ht, hv⟩ | ⟨f', hf'⟩
    · have := h S hs ht
      push_cast at this
      linarith
    · exact ⟨f', by simpa using hf'⟩

/-! ### Real capacities -/

/-- The capacity of a minimum cut separating `s` from `t`. -/
def minCut (c : V → V → ℝ) (s t : V) : ℝ :=
  sInf (cutCap c '' {S : Finset V | s ∈ S ∧ t ∉ S})

lemma finite_cuts (c : V → V → ℝ) (s t : V) :
    (cutCap c '' {S : Finset V | s ∈ S ∧ t ∉ S}).Finite :=
  (Set.toFinite _).image _

lemma minCut_le (c : V → V → ℝ) {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    minCut c s t ≤ cutCap c S :=
  csInf_le (finite_cuts c s t).bddBelow ⟨S, ⟨hs, ht⟩, rfl⟩

/-- A minimum cut exists. -/
lemma exists_cut_eq_minCut (c : V → V → ℝ) {s t : V} (hst : s ≠ t) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ cutCap c S = minCut c s t := by
  have hne : (cutCap c '' {S : Finset V | s ∈ S ∧ t ∉ S}).Nonempty :=
    ⟨_, {s}, ⟨by simp, by simpa using hst.symm⟩, rfl⟩
  obtain ⟨S, ⟨hs, ht⟩, hS⟩ := hne.csInf_mem (finite_cuts c s t)
  exact ⟨S, hs, ht, hS⟩

lemma le_minCut (c : V → V → ℝ) {s t : V} (hst : s ≠ t) {a : ℝ}
    (h : ∀ S : Finset V, s ∈ S → t ∉ S → a ≤ cutCap c S) : a ≤ minCut c s t := by
  obtain ⟨S, hs, ht, hS⟩ := exists_cut_eq_minCut c hst
  exact hS ▸ h S hs ht

lemma minCut_nonneg {c : V → V → ℝ} (hc : ∀ j k, 0 ≤ c j k) {s t : V} (hst : s ≠ t) :
    0 ≤ minCut c s t :=
  le_minCut c hst fun _ _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hc _ _

/-- Finitely many positive reals have a positive lower bound. -/
private lemma exists_pos_le (T : Finset ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ T, 0 < x → δ ≤ x := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a T _ ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    by_cases ha : 0 < a
    · refine ⟨min a δ, lt_min ha hδ, fun x hx hx0 => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (h x hx hx0)
    · refine ⟨δ, hδ, fun x hx hx0 => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact absurd hx0 ha
      · exact h x hx hx0

omit [DecidableEq V] in
/-- A flow of largest value exists, by compactness. -/
private lemma exists_max_flow {c : V → V → ℝ} (hc : ∀ j k, 0 ≤ c j k) (s t : V) :
    ∃ f, IsFlow c s t f (netOut f s) ∧ ∀ g v, IsFlow c s t g v → v ≤ netOut f s := by
  have hcont : ∀ k, Continuous fun f : V → V → ℝ => netOut f k := by
    intro k
    unfold netOut
    fun_prop
  let F : Set (V → V → ℝ) := (Set.univ.pi fun j => Set.univ.pi fun k => Set.Icc 0 (c j k)) ∩
    ⋂ k ∈ {k : V | k ≠ s ∧ k ≠ t}, {f | netOut f k = 0}
  have hF : IsCompact F := by
    refine IsCompact.inter_right
      (isCompact_univ_pi fun j => isCompact_univ_pi fun k => isCompact_Icc) ?_
    exact isClosed_biInter fun k _ => isClosed_eq (hcont k) continuous_const
  have hne : F.Nonempty := by
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · exact fun j _ k _ => ⟨le_rfl, hc j k⟩
    · simp [netOut]
  obtain ⟨f, hfF, hmax⟩ := hF.exists_isMaxOn hne (hcont s).continuousOn
  have hmem : ∀ {g : V → V → ℝ} {v : ℝ}, IsFlow c s t g v → g ∈ F := by
    intro g v hg
    refine ⟨fun j _ k _ => ⟨hg.nonneg j k, hg.le_cap j k⟩, ?_⟩
    simp only [Set.mem_iInter]
    exact fun k hk => hg.cons k hk.1 hk.2
  refine ⟨f, ⟨fun j k => (hfF.1 j trivial k trivial).1, fun j k => (hfF.1 j trivial k trivial).2,
    fun k hs ht => ?_, rfl⟩, fun g v hg => ?_⟩
  · have := hfF.2
    simp only [Set.mem_iInter] at this
    exact this k ⟨hs, ht⟩
  · have := hmax (hmem hg)
    change netOut g s ≤ netOut f s at this
    rw [← hg.value]
    exact this

/-- **Max-flow min-cut theorem, page 16-5 of [elgamal2010], in the form of the linear program of
page 16-8.** For real capacities, the largest value of a flow is the capacity of a minimum cut. The
proof takes a flow of largest value, and its residual graph gives a saturated cut, in place of LP
duality and Slater's condition. -/
theorem maxFlow_minCut {c : V → V → ℝ} (hc : ∀ j k, 0 ≤ c j k) {s t : V} (hst : s ≠ t) :
    IsGreatest {v | ∃ f, IsFlow c s t f v} (minCut c s t) := by
  obtain ⟨f, hf, hmax⟩ := exists_max_flow hc s t
  classical
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le
    ((Finset.univ.image fun p : V × V => c p.1 p.2 - f p.1 p.2) ∪
      Finset.univ.image fun p : V × V => f p.1 p.2)
  have h₁ : ∀ j k, f j k < c j k → f j k + δ ≤ c j k := by
    intro j k h
    have := hle (c j k - f j k) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩)) (sub_pos.mpr h)
    linarith
  have h₂ : ∀ j k, 0 < f j k → δ ≤ f j k := fun j k h =>
    hle (f j k) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩)) h
  rcases hf.eq_cut_or_augment hst hδ h₁ h₂ with ⟨S, hs, ht, hv⟩ | ⟨f', hf'⟩
  · have hle' : ∀ v, (∃ g, IsFlow c s t g v) → v ≤ minCut c s t := by
      rintro v ⟨g, hg⟩
      obtain ⟨S', hs', ht', hS'⟩ := exists_cut_eq_minCut c hst
      exact hS' ▸ hg.le_cutCap hs' ht'
    have heq : netOut f s = minCut c s t :=
      le_antisymm (hle' _ ⟨f, hf⟩) (hv ▸ minCut_le c hs ht)
    exact ⟨⟨f, heq ▸ hf⟩, fun v hv' => hle' v hv'⟩
  · have := hmax f' _ hf'
    linarith

/-! ### Several sources -/

/-- **Flows with several sources.** Suppose each node `k ≠ t` has a supply `ρ k`, and the supplies
inside any set not containing `t` are at most the capacity of its cut. Then there is an integer
flow whose net flow out of each `k ≠ t` is `ρ k`. The proof adds a source of all sources. -/
theorem exists_supplyFlow {c : V → V → ℤ} (hc : ∀ j k, 0 ≤ c j k) (t : V) {ρ : V → ℕ}
    (h : ∀ S : Finset V, t ∉ S → ∑ j ∈ S, (ρ j : ℤ) ≤ cutCap c S) :
    ∃ f : V → V → ℤ, (∀ j k, 0 ≤ f j k) ∧ (∀ j k, f j k ≤ c j k) ∧
      ∀ k, k ≠ t → netOut f k = ρ k := by
  classical
  -- the extended capacities; the supply of `t` is not used
  let ρ' : V → ℤ := fun k => if k = t then 0 else ρ k
  have hρ' : ∀ k, 0 ≤ ρ' k := fun k => by
    simp only [ρ']
    split_ifs <;> simp
  let c' : Option V → Option V → ℤ := fun a b =>
    match a, b with
    | none, some k => ρ' k
    | some j, some k => c j k
    | _, none => 0
  have hc' : ∀ a b, 0 ≤ c' a b := by
    rintro (_ | j) (_ | k)
    · exact le_rfl
    · exact hρ' k
    · exact le_rfl
    · exact hc j k
  let v : ℕ := ∑ k ∈ Finset.univ.erase t, ρ k
  have hcut : ∀ S' : Finset (Option V), none ∈ S' → some t ∉ S' → (v : ℤ) ≤ cutCap c' S' := by
    intro S' hn ht
    let S : Finset V := Finset.univ.filter fun j => some j ∈ S'
    have htS : t ∉ S := by simpa [S] using ht
    have hval : cutCap c' S' = ∑ k ∈ Sᶜ, ρ' k + cutCap c S := by
      have hind : cutCap c' S' = ∑ a, ∑ b, (if a ∈ S' ∧ b ∉ S' then c' a b else 0) := by
        unfold cutCap
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S')]
        have h0 : ∑ a ∈ Finset.univ.filter (· ∉ S'),
            ∑ b, (if a ∈ S' ∧ b ∉ S' then c' a b else 0) = 0 :=
          Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b _ => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
            simp [ha]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter, h0, add_zero]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∉ S')]
        have h1 : ∑ b ∈ Finset.univ.filter (fun b => ¬ b ∉ S'),
            (if a ∈ S' ∧ b ∉ S' then c' a b else 0) = 0 :=
          Finset.sum_eq_zero fun b hb => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
            simp only [hb, and_false, ite_false]
        rw [h1, add_zero]
        have : Finset.univ.filter (· ∉ S') = S'ᶜ := by
          ext b
          simp
        rw [this]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [ite_eq_left ⟨ha, Finset.mem_compl.mp hb⟩]
      rw [hind, Fintype.sum_option]
      simp only [Fintype.sum_option, hn, not_true_eq_false, and_false, ite_false, zero_add,
        true_and]
      have h1 : ∑ k, (if some k ∉ S' then c' none (some k) else 0) = ∑ k ∈ Sᶜ, ρ' k := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext k
        simp [S]
      have h2 : ∑ j, ∑ k, (if some j ∈ S' ∧ some k ∉ S' then c' (some j) (some k) else 0) =
          cutCap c S := by
        unfold cutCap
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => some j ∈ S')]
        rw [add_comm, Finset.sum_eq_zero (s := Finset.univ.filter (fun j => ¬ some j ∈ S')),
          zero_add]
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : some j ∈ S' := by simpa [S] using hj
          simp only [hj', true_and]
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext k
          simp [S]
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp [hj]
      rw [h1, h2]
    rw [hval]
    have hsum : (v : ℤ) = ∑ k ∈ S, ρ' k + ∑ k ∈ Sᶜ, ρ' k := by
      rw [Finset.sum_add_sum_compl]
      simp only [v, ρ']
      rw [Nat.cast_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ t)]
      simp only [ite_true, zero_add]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ite_eq_right (Finset.ne_of_mem_erase hk)]
    have hS : ∑ k ∈ S, ρ' k ≤ cutCap c S := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) (h S htS)
      have : k ≠ t := fun hkt => htS (hkt ▸ hk)
      simp [ρ', this]
    rw [hsum]
    linarith
  obtain ⟨f', hf'⟩ := exists_intFlow hc' (s := none) (t := some t) (by simp) v hcut
  have hto : ∀ a, f' a none = 0 := fun a =>
    le_antisymm (by simpa [c'] using (hf'.le_cap a none).trans (by cases a <;> simp [c']))
      (hf'.nonneg a none)
  have hin : ∀ k, f' none (some k) = ρ' k := by
    have hle : ∀ k ∈ Finset.univ, f' none (some k) ≤ ρ' k := fun k _ => hf'.le_cap none (some k)
    have hval : ∑ k, f' none (some k) = ∑ k, ρ' k := by
      have h0 := hf'.value
      simp only [netOut, Fintype.sum_option, hto, zero_add, Finset.sum_const_zero, sub_zero] at h0
      rw [h0]
      simp only [v, ρ']
      rw [Nat.cast_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ t)]
      simp only [ite_true, zero_add]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ite_eq_right (Finset.ne_of_mem_erase hk)]
    intro k
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hval k (Finset.mem_univ k)
  refine ⟨fun j k => f' (some j) (some k), fun j k => hf'.nonneg _ _,
    fun j k => hf'.le_cap (some j) (some k), fun k hk => ?_⟩
  have h0 := hf'.cons (some k) (by simp) (by simpa using hk)
  simp only [netOut, Fintype.sum_option, hto, zero_add, hin] at h0
  have : ρ' k = ρ k := by simp [ρ', hk]
  simp only [netOut]
  linarith

end InfoTheory
