/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.MaxFlow

/-!
# Decomposition of an integer flow

An integer flow on an acyclic network, whose nodes are linearly ordered so that the flow goes up,
carries individual units: each unit starting at a node reaches the sink along edges of the network,
and an edge with flow `f` carries at most `f` units.

## Main statements

* `exists_unit_path`: a unit path to the sink inside a flow.
* `exists_units`: the decomposition of a flow into units.
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {V β : Type*} [Fintype V] [LinearOrder V]

/-- A unit of flow from `j₀` reaches `t`: if the net flow out of every node other than `t` is
nonnegative, and it is positive at `j₀`, then a path from `j₀` to `t` is contained in `f`. The
path is a function `p` with values in `{0, 1}` and net flow `1` at `j₀` and `-1` at `t`. -/
theorem exists_unit_path {f : V → V → ℤ} (h0 : ∀ j k, 0 ≤ f j k) (hord : ∀ j k, 0 < f j k → j < k)
    {t j₀ : V} (hnet : ∀ k, k ≠ t → 0 ≤ netOut f k) (hpos : 0 < netOut f j₀) :
    ∃ p : V → V → ℤ, (∀ a b, p a b = 0 ∨ p a b = 1) ∧ (∀ a b, p a b ≤ f a b) ∧
      ∀ k, netOut p k = (if k = j₀ then 1 else 0) - (if k = t then 1 else 0) := by
  classical
  -- `Reach u`: a path from `j₀` to `u`, using only edges with head at most `u`
  let Reach : V → Prop := fun u => ∃ p : V → V → ℤ, (∀ a b, p a b = 0 ∨ p a b = 1) ∧
    (∀ a b, p a b ≤ f a b) ∧ (∀ a b, p a b ≠ 0 → b ≤ u) ∧
    ∀ k, netOut p k = (if k = j₀ then 1 else 0) - (if k = u then 1 else 0)
  have hbase : Reach j₀ := by
    refine ⟨fun _ _ => 0, fun _ _ => Or.inl rfl, h0, fun _ _ h => absurd rfl h, fun k => ?_⟩
    simp [netOut]
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image (Finset.univ.filter Reach) id ⟨j₀, by
    simpa using hbase⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hu hmax
  by_cases hut : u = t
  · obtain ⟨p, hp₁, hp₂, -, hp₄⟩ := hu
    exact ⟨p, hp₁, hp₂, hut ▸ hp₄⟩
  exfalso
  obtain ⟨p, hp₁, hp₂, hp₃, hp₄⟩ := hu
  -- an edge out of `u` carries flow
  have hout : 0 < ∑ l, f u l := by
    by_cases huj : u = j₀
    · have h₁ : 0 ≤ ∑ j, f j u := Finset.sum_nonneg fun _ _ => h0 _ _
      have := huj ▸ hpos
      simp only [netOut] at this
      linarith
    · have hn := hp₄ u
      simp only [huj, ite_false, ite_true, netOut] at hn
      have h₁ : 0 ≤ ∑ l, p u l := Finset.sum_nonneg fun l _ => by
        rcases hp₁ u l with h | h <;> simp [h]
      have h₂ : ∑ j, p j u ≤ ∑ j, f j u := Finset.sum_le_sum fun j _ => hp₂ j u
      have h₃ := hnet u hut
      simp only [netOut] at h₃
      linarith
  obtain ⟨w, -, hw⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℤ))
    (g := fun l => f u l) (by simpa using hout)
  have huw : u < w := hord u w hw
  have hpuw : p u w = 0 := by
    by_contra h
    exact absurd (hp₃ u w h) (not_le.mpr huw)
  refine absurd (hmax w ?_) (not_le.mpr huw)
  refine ⟨fun a b => p a b + if a = u ∧ b = w then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro a b
    by_cases hab : a = u ∧ b = w
    · obtain ⟨rfl, rfl⟩ := hab
      simp [hpuw]
    · simpa [hab] using hp₁ a b
  · intro a b
    by_cases hab : a = u ∧ b = w
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [hpuw, and_self, ite_true, zero_add]
      exact hw
    · simpa [hab] using hp₂ a b
  · intro a b hne
    by_cases hab : a = u ∧ b = w
    · exact hab.2.le
    · have hne' : p a b ≠ 0 := by simpa [hab] using hne
      exact (hp₃ a b hne').trans huw.le
  · intro k
    rw [netOut_add_single, hp₄ k]
    ring

omit [LinearOrder V] in
/-- A flow into a node, given a flow out of a node with a smaller net flow. -/
private lemma exists_in_of_out {p : V → V → ℤ} (hp : ∀ a b, p a b = 0 ∨ p a b = 1) {k l : V}
    (hkl : p k l = 1) (hnet : netOut p k ≤ 0) : ∃ j, p j k = 1 := by
  have h₁ : 1 ≤ ∑ l, p k l := by
    rw [← hkl]
    exact Finset.single_le_sum (f := fun l => p k l)
      (fun l _ => by rcases hp k l with h | h <;> simp [h]) (Finset.mem_univ l)
  simp only [netOut] at hnet
  have h₂ : 0 < ∑ j, p j k := by linarith
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℤ))
    (g := fun j => p j k) (by simpa using h₂)
  rcases hp j k with h | h
  · simp [h] at hj
  · exact ⟨j, h⟩

/-- **Decomposition of a flow.** Let `own k` be the units starting at `k`, and let the net flow out
of every `k ≠ t` be the number of them. Then each edge can carry a set of at most `f j k` units such
that a unit on an edge out of `k` either starts at `k` or came in on an edge into `k`, and every
unit reaches `t`. -/
theorem exists_units {f : V → V → ℤ} (h0 : ∀ j k, 0 ≤ f j k) (hord : ∀ j k, 0 < f j k → j < k)
    (t : V) (own : V → Finset β) (hnet : ∀ k, k ≠ t → netOut f k = #(own k)) :
    ∃ B : V → V → Finset β, (∀ j k, (#(B j k) : ℤ) ≤ f j k) ∧
      (∀ k l, ∀ r ∈ B k l, r ∈ own k ∨ ∃ j, j < k ∧ r ∈ B j k) ∧
      ∀ k, k ≠ t → ∀ r ∈ own k, ∃ i, i < t ∧ r ∈ B i t := by
  classical
  induction hn : ∑ k ∈ Finset.univ.erase t, #(own k) using Nat.strong_induction_on
    generalizing f own with
  | _ n ih =>
  by_cases hex : ∃ j₀, j₀ ≠ t ∧ (own j₀).Nonempty
  · obtain ⟨j₀, hj₀, r₀, hr₀⟩ := hex
    have hcard : 0 < #(own j₀) := Finset.card_pos.mpr ⟨r₀, hr₀⟩
    obtain ⟨p, hp₁, hp₂, hp₄⟩ := exists_unit_path h0 hord
      (fun k hk => by rw [hnet k hk]; positivity)
      (by rw [hnet j₀ hj₀]; exact_mod_cast hcard)
    -- remove the path and the unit
    let f' : V → V → ℤ := fun a b => f a b - p a b
    let own' : V → Finset β := fun k => if k = j₀ then (own j₀).erase r₀ else own k
    have hp0 : ∀ a b, 0 ≤ p a b := fun a b => by rcases hp₁ a b with h | h <;> simp [h]
    have hf'0 : ∀ a b, 0 ≤ f' a b := fun a b => sub_nonneg.mpr (hp₂ a b)
    have hf'ord : ∀ a b, 0 < f' a b → a < b := fun a b h =>
      hord a b (lt_of_lt_of_le h (sub_le_self _ (hp0 a b)))
    have hnet' : ∀ k, k ≠ t → netOut f' k = #(own' k) := by
      intro k hk
      have hsub : netOut f' k = netOut f k - netOut p k := by
        simp only [netOut, f', Finset.sum_sub_distrib]
        ring
      rw [hsub, hp₄ k, hnet k hk]
      by_cases hkj : k = j₀
      · subst hkj
        simp only [own', hk, ite_false, ite_true]
        rw [Finset.card_erase_of_mem hr₀, Nat.cast_sub hcard]
        simp
      · simp [own', hkj, hk]
    have hlt : ∑ k ∈ Finset.univ.erase t, #(own' k) < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨j₀, by simpa using hj₀, ?_⟩
      · by_cases hkj : k = j₀
        · subst hkj
          simpa [own'] using Finset.card_le_card (Finset.erase_subset _ _)
        · simp [own', hkj]
      · simpa [own'] using Finset.card_erase_lt_of_mem hr₀
    obtain ⟨B', hB₁, hB₂, hB₃⟩ := ih _ hlt hf'0 hf'ord own' hnet' rfl
    have hown' : ∀ k r, r ∈ own' k → r ∈ own k := by
      intro k r hr
      by_cases hkj : k = j₀
      · subst hkj
        simp only [own', ite_true] at hr
        exact Finset.mem_of_mem_erase hr
      · simpa [own', hkj] using hr
    refine ⟨fun a b => if p a b = 1 then insert r₀ (B' a b) else B' a b, ?_, ?_, ?_⟩
    · intro a b
      have hle := hB₁ a b
      simp only [f'] at hle
      by_cases hab : p a b = 1
      · simp only [hab, ite_true]
        have : (#(insert r₀ (B' a b)) : ℤ) ≤ #(B' a b) + 1 := by
          exact_mod_cast Finset.card_insert_le _ _
        linarith
      · have hab0 : p a b = 0 := (hp₁ a b).resolve_right hab
        simp only [hab, ite_false]
        linarith
    · intro k l r hr
      have hin : ∀ j, r ∈ B' j k → r ∈ (if p j k = 1 then insert r₀ (B' j k) else B' j k) := by
        intro j hj
        split_ifs
        · exact Finset.mem_insert_of_mem hj
        · exact hj
      have hcase : r ∈ B' k l ∨ (r = r₀ ∧ p k l = 1) := by
        dsimp only at hr
        split_ifs at hr with hkl
        · rcases Finset.mem_insert.mp hr with h | h
          · exact Or.inr ⟨h, hkl⟩
          · exact Or.inl h
        · exact Or.inl hr
      rcases hcase with hr' | ⟨rfl, hkl⟩
      · rcases hB₂ k l r hr' with h | ⟨j, hj, hjr⟩
        · exact Or.inl (hown' k r h)
        · exact Or.inr ⟨j, hj, hin j hjr⟩
      · by_cases hkj : k = j₀
        · subst hkj
          exact Or.inl hr₀
        · have hn' : netOut p k ≤ 0 := by
            rw [hp₄ k]
            simp only [hkj, ite_false, zero_sub]
            split_ifs <;> simp
          obtain ⟨j, hj⟩ := exists_in_of_out hp₁ hkl hn'
          refine Or.inr ⟨j, hord j k (lt_of_lt_of_le (by simp [hj]) (hp₂ j k)), ?_⟩
          simp [hj]
    · intro k hk r hr
      have hin : ∀ i, r ∈ B' i t → r ∈ (if p i t = 1 then insert r₀ (B' i t) else B' i t) := by
        intro i hi
        split_ifs
        · exact Finset.mem_insert_of_mem hi
        · exact hi
      by_cases hrk : r ∈ own' k
      · obtain ⟨i, hi, hir⟩ := hB₃ k hk r hrk
        exact ⟨i, hi, hin i hir⟩
      · have hkj : k = j₀ := by
          by_contra hkj
          exact hrk (by simpa [own', hkj] using hr)
        subst hkj
        have hrr : r = r₀ := by
          by_contra hrr
          exact hrk (by simpa [own', hrr] using hr)
        subst hrr
        have hsum : 0 < ∑ i, p i t := by
          have hn' := hp₄ t
          simp only [hk.symm, ite_false, ite_true, netOut] at hn'
          have : 0 ≤ ∑ l, p t l := Finset.sum_nonneg fun l _ => hp0 t l
          linarith
        obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
          (f := fun _ => (0 : ℤ)) (g := fun i => p i t) (by simpa using hsum)
        have hi1 : p i t = 1 := (hp₁ i t).resolve_left (by intro h; simp [h] at hi)
        refine ⟨i, hord i t (lt_of_lt_of_le (by simp [hi1]) (hp₂ i t)), ?_⟩
        simp [hi1]
  · push Not at hex
    refine ⟨fun _ _ => ∅, fun j k => by simpa using h0 j k, by simp, fun k hk r hr => ?_⟩
    simp [hex k hk] at hr

end InfoTheory
