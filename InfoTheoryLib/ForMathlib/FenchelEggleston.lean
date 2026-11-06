/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Fenchel–Eggleston strengthening of Carathéodory's theorem

In a real vector space of dimension `d ≥ 1`, Carathéodory's theorem writes a point of the convex
hull of a set as a convex combination of at most `d + 1` points of the set. If the set is connected,
then `d` points suffice.

The idea of the proof is as follows. Suppose that `x` is a convex combination `∑ wᵢ zᵢ` of `d + 1`
affinely independent points with positive weights. Each vector is a combination
`∑ μᵢ wᵢ (zᵢ - x)`, and `μ` is unique up to adding a constant. Say that a point `p` has type `i` if
the coordinate `μᵢ` of `x - p` is strictly the smallest. Then `zᵢ` has type `i`, and the sets of
points of a given type are open and disjoint, so a connected set cannot be covered by them. A point
`p` of no type has two smallest coordinates. Subtracting the smallest one writes `x` as a convex
combination of `p` and `d - 1` of the `zᵢ`.

## Main statements

* `isCompact_convexHull_of_isCompact`: in finite dimension the convex hull of a compact set is
  compact.
* `exists_finset_of_mem_convexHull`: **the Fenchel–Eggleston theorem**, for a connected set.
* `exists_finset_of_mem_closure_convexHull`: the same for the closure of the convex hull of a
  connected compact set.
* `exists_convex_combination_le_finrank`: the same as a convex combination of an indexed family.

## References

* [H. G. Eggleston, *Convexity*][eggleston1958]
-/

@[expose] public section

open Finset Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimension, **the convex hull of a compact set is compact**, as the continuous image of
a simplex times a power of the set, by Carathéodory's theorem. -/
theorem isCompact_convexHull_of_isCompact {R : Set E} (hR : IsCompact R) :
    IsCompact (convexHull ℝ R) := by
  classical
  set d := finrank ℝ E with hd
  set W : Set (Fin (d + 1) → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} with hW
  have hWc : IsCompact W := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ))
      (b := 1)) ?_ fun w hw i _ => ⟨hw.1 i, ?_⟩
    · have h1 : IsClosed {w : Fin (d + 1) → ℝ | ∀ i, 0 ≤ w i} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
      have h2 : IsClosed {w : Fin (d + 1) → ℝ | ∑ i, w i = 1} :=
        isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
      exact h1.inter h2
    · rw [← hw.2]
      exact single_le_sum (f := w) (fun j _ => hw.1 j) (mem_univ i)
  set C : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → E)) :=
    W ×ˢ Set.pi Set.univ fun _ => R with hC
  have hCc : IsCompact C := hWc.prod (isCompact_univ_pi fun _ => hR)
  have hcont : Continuous fun q : (Fin (d + 1) → ℝ) × (Fin (d + 1) → E) => ∑ i, q.1 i • q.2 i := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp continuous_fst).smul
      ((continuous_apply i).comp continuous_snd)
  have himg := hCc.image hcont
  convert himg using 1
  ext x
  constructor
  · intro hx
    obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι ≤ d + 1 := by
      have h1 := hai.card_le_finrank_succ
      have h2 : finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ d := Submodule.finrank_le _
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin (d + 1))
      (by simpa using hcard)
    have hne : Nonempty ι := by
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      simp at hw1
    obtain ⟨i₀⟩ := hne
    set w' : Fin (d + 1) → ℝ := Function.extend e w 0 with hw'
    set z' : Fin (d + 1) → E := Function.extend e z fun _ => z i₀ with hz'
    have hw'0 : ∀ j, j ∉ Set.range e → w' j = 0 := fun j hj => by
      simp [hw', Function.extend_apply' _ _ _ (by simpa using hj)]
    have he₁ : ∀ i, w' (e i) = w i := fun i => e.injective.extend_apply _ _ _
    have he₂ : ∀ i, z' (e i) = z i := fun i => e.injective.extend_apply _ _ _
    refine ⟨(w', z'), ⟨⟨fun j => ?_, ?_⟩, fun j _ => ?_⟩, ?_⟩
    · change 0 ≤ w' j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [he₁]
        exact (hw i).le
      · rw [hw'0 j hj]
    · rw [← hw1]
      exact (Fintype.sum_of_injective e e.injective w w' (fun j hj => hw'0 j hj)
        fun i => (he₁ i).symm).symm
    · change z' j ∈ R
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [he₂]
        exact hz ⟨i, rfl⟩
      · have : z' j = z i₀ := by
          simp only [hz']
          rw [Function.extend_apply' _ _ _ (by simpa using hj)]
        rw [this]
        exact hz ⟨i₀, rfl⟩
    · change ∑ i, w' i • z' i = x
      rw [← hwz]
      refine (Fintype.sum_of_injective e e.injective (fun i => w i • z i)
        (fun j => w' j • z' j) (fun j hj => ?_) (fun i => ?_)).symm
      · simp [hw'0 j hj]
      · simp [he₁, he₂]
  · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
    exact (convex_convexHull ℝ R).sum_mem (fun i _ => hw.1 i) hw.2
      fun i _ => subset_convexHull ℝ R (hz i (Set.mem_univ i))

/-- **The Fenchel–Eggleston theorem.** In a real vector space of dimension `d ≥ 1`, each point of
the convex hull of a connected set is in the convex hull of at most `d` points of the set. -/
theorem exists_finset_of_mem_convexHull {R : Set E} (hR : IsPreconnected R)
    (hd : 0 < finrank ℝ E) {x : E} (hx : x ∈ convexHull ℝ R) :
    ∃ t : Finset E, (t : Set E) ⊆ R ∧ t.card ≤ finrank ℝ E ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  set d := finrank ℝ E with hdd
  have hcard : Fintype.card ι ≤ d + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ d := Submodule.finrank_le _
    omega
  by_cases hsmall : Fintype.card ι ≤ d
  · -- With at most `d` points there is nothing to do.
    refine ⟨univ.image z, ?_, card_image_le.trans (by simpa using hsmall), ?_⟩
    · intro y hy
      obtain ⟨i, -, rfl⟩ := mem_image.1 (by exact_mod_cast hy)
      exact hz ⟨i, rfl⟩
    · rw [← hwz]
      exact (convex_convexHull ℝ _).sum_mem (fun i _ => (hw i).le) hw1 fun i _ =>
        subset_convexHull ℝ _ (by simp)
  have hcard' : Fintype.card ι = d + 1 := by omega
  -- The combinations of the vectors `wᵢ (zᵢ - x)`.
  set T : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ fun i => w i • (z i - x) with hT
  have hTapp : ∀ μ, T μ = ∑ i, μ i • w i • (z i - x) := fun μ => by
    simp [hT, Fintype.linearCombination_apply]
  have hsum0 : ∑ i, w i • (z i - x) = 0 := by
    simp only [smul_sub, sum_sub_distrib, hwz, ← sum_smul, hw1, one_smul, sub_self]
  have hTc : ∀ c : ℝ, T (fun _ => c) = 0 := fun c => by
    rw [hTapp]
    simp only [← smul_sum, hsum0, smul_zero]
  -- The kernel consists of the constants.
  have hker : ∀ μ, T μ = 0 → ∀ i, μ i = ∑ j, μ j * w j := by
    intro μ hμ i
    set m := ∑ j, μ j * w j with hm
    have h1 : ∑ j, (μ j * w j - m * w j) = 0 := by
      rw [sum_sub_distrib, ← mul_sum, hw1, mul_one, sub_self]
    have h2 : ∑ j, (μ j * w j - m * w j) • z j = 0 := by
      have h3 := hμ
      rw [hTapp] at h3
      have h4 : ∑ j, μ j • w j • (z j - x) = ∑ j, (μ j * w j) • z j - m • x := by
        simp only [smul_smul, smul_sub, sum_sub_distrib, ← sum_smul, ← hm]
      rw [h4, sub_eq_zero] at h3
      simp only [sub_smul, sum_sub_distrib, h3]
      simp only [mul_smul, ← smul_sum, hwz, sub_self]
    have h3 := (affineIndependent_iff.1 hai) univ _ h1 h2 i (mem_univ i)
    have h4 := (hw i).ne'
    have h5 : (μ i - m) * w i = 0 := by linarith
    have h6 := (mul_eq_zero.1 h5).resolve_right h4
    linarith
  -- `T` is surjective.
  have hsurj : LinearMap.range T = ⊤ := by
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    have hdom : finrank ℝ (ι → ℝ) = d + 1 := by simp [hcard']
    have hk : finrank ℝ (LinearMap.ker T) ≤ 1 := by
      have hle : LinearMap.ker T ≤ Submodule.span ℝ {fun _ : ι => (1 : ℝ)} := by
        intro μ hμ
        refine Submodule.mem_span_singleton.2 ⟨∑ j, μ j * w j, ?_⟩
        funext i
        simpa using (hker μ hμ i).symm
      refine (Submodule.finrank_mono hle).trans ?_
      simpa using finrank_span_le_card (R := ℝ) ({fun _ => 1} : Set (ι → ℝ))
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    omega
  obtain ⟨L, hL⟩ := T.exists_rightInverse_of_surjective hsurj
  have hTL : ∀ y, T (L y) = y := fun y => LinearMap.congr_fun hL y
  -- The coordinates of `x - p`.
  set f : ι → E → ℝ := fun i p => L (x - p) i with hf
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    have h1 : Continuous fun y : E => L y := L.continuous_of_finiteDimensional
    exact (continuous_apply i).comp (h1.comp (continuous_const.sub continuous_id))
  set U : ι → Set E := fun i => {p | ∀ j, j ≠ i → f i p < f j p} with hU
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    have : U i = ⋂ j, ⋂ (_ : j ≠ i), {p | f i p < f j p} := by
      ext p
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      isOpen_lt (hfc i) (hfc j)
  -- The point `zₖ` has type `k`.
  have hzU : ∀ k, z k ∈ U k := by
    intro k j hjk
    set μ : ι → ℝ := fun j => if j = k then 0 else (w k)⁻¹ with hμ
    have hTμ : T μ = x - z k := by
      rw [hTapp]
      have h1 : ∀ j, μ j • w j • (z j - x) =
          (w k)⁻¹ • (w j • (z j - x)) - (if j = k then (w k)⁻¹ • (w j • (z j - x)) else 0) := by
        intro j
        by_cases h : j = k <;> simp [hμ, h]
      simp only [h1, sum_sub_distrib, ← smul_sum, hsum0, smul_zero, sum_ite_eq', mem_univ, ite_true,
        zero_sub]
      rw [smul_smul, inv_mul_cancel₀ (hw k).ne', one_smul]
      abel
    have h2 : T (L (x - z k) - μ) = 0 := by
      rw [map_sub, hTL, hTμ, sub_self]
    have h3 := hker _ h2
    set m := ∑ j, (L (x - z k) - μ) j * w j with hm
    have hval : ∀ i, f i (z k) = μ i + m := by
      intro i
      have h4 := h3 i
      simp only [Pi.sub_apply] at h4
      simp only [hf]
      linarith
    change f k (z k) < f j (z k)
    rw [hval k, hval j]
    have h6 : 0 < (w k)⁻¹ := inv_pos.2 (hw k)
    simp only [hμ, ite_true, hjk, ite_false]
    linarith
  -- Some point of the set has no type.
  have hne2 : 1 < Fintype.card ι := by omega
  obtain ⟨k₀, k₁, hk⟩ := Fintype.one_lt_card_iff.1 hne2
  have hnotype : ∃ p ∈ R, ∀ i, p ∉ U i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, hp1, hp2⟩ := hR (U k₀) (⋃ i, ⋃ (_ : i ≠ k₀), U i) (hUo k₀)
      (isOpen_iUnion fun i => isOpen_iUnion fun _ => hUo i)
      (fun p hp => by
        obtain ⟨i, hi⟩ := hcon p hp
        by_cases h : i = k₀
        · exact Or.inl (h ▸ hi)
        · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, h, hi⟩))
      ⟨z k₀, hz ⟨k₀, rfl⟩, hzU k₀⟩
      ⟨z k₁, hz ⟨k₁, rfl⟩, Set.mem_iUnion₂.2 ⟨k₁, hk.symm, hzU k₁⟩⟩
    obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.1 hp2
    have h1 := hp1 i hi
    have h2 := hpi k₀ (Ne.symm hi)
    linarith
  obtain ⟨p, hpR, hp⟩ := hnotype
  -- The two smallest coordinates.
  obtain ⟨i₀, -, hi₀⟩ := exists_min_image (univ : Finset ι) (fun i => f i p)
    ⟨k₀, mem_univ _⟩
  have hnot := hp i₀
  simp only [hU, Set.mem_ofPred_eq] at hnot
  push Not at hnot
  obtain ⟨j₀, hj₀, hle⟩ := hnot
  have hmin : ∀ i, f i₀ p ≤ f i p := fun i => hi₀ i (mem_univ i)
  have heq : f j₀ p = f i₀ p := le_antisymm hle (hmin j₀)
  set c : ι → ℝ := fun j => (f j p - f i₀ p) * w j with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j =>
    mul_nonneg (sub_nonneg.2 (hmin j)) (hw j).le
  have hci : c i₀ = 0 := by simp [hc]
  have hcj : c j₀ = 0 := by simp [hc, heq]
  -- The combination.
  have hrep : x - p = ∑ j, c j • (z j - x) := by
    have h1 : T (fun j => f j p - f i₀ p) = x - p := by
      have h2 : (fun j => f j p - f i₀ p) = L (x - p) - fun _ => f i₀ p := rfl
      rw [h2, map_sub, hTL, hTc, sub_zero]
    rw [← h1, hTapp]
    refine sum_congr rfl fun j _ => ?_
    rw [smul_smul]
  set C := ∑ j, c j with hC
  have hC0 : 0 ≤ C := sum_nonneg fun j _ => hc0 j
  have hW : 0 < 1 + C := by linarith
  have hcomb : (1 + C) • x = p + ∑ j, c j • z j := by
    have h1 : ∑ j, c j • (z j - x) = ∑ j, c j • z j - C • x := by
      simp only [smul_sub, sum_sub_distrib, ← sum_smul, hC]
    rw [h1] at hrep
    rw [add_smul, one_smul]
    have h2 : x + C • x - (p + ∑ j, c j • z j) = (x - p) - (∑ j, c j • z j - C • x) := by
      abel
    exact sub_eq_zero.1 (by rw [h2, hrep, sub_self])
  set A := (univ.erase i₀).erase j₀ with hA
  have hAmem : ∀ j, j ∉ A → c j = 0 := by
    intro j hj
    by_cases h1 : j = j₀
    · rw [h1, hcj]
    · by_cases h2 : j = i₀
      · rw [h2, hci]
      · exact absurd (mem_erase.2 ⟨h1, mem_erase.2 ⟨h2, mem_univ j⟩⟩) hj
  have hsumA : ∑ j, c j • z j = ∑ j ∈ A, c j • z j :=
    (sum_subset (subset_univ A) fun j _ hj => by rw [hAmem j hj, zero_smul]).symm
  have hsumC : C = ∑ j ∈ A, c j :=
    (sum_subset (subset_univ A) fun j _ hj => hAmem j hj).symm
  have hcardA : A.card + 1 = d := by
    have h1 : j₀ ∈ univ.erase i₀ := mem_erase.2 ⟨hj₀, mem_univ _⟩
    have h2 : (univ.erase i₀ : Finset ι).card = d := by
      rw [card_erase_of_mem (mem_univ _), card_univ, hcard']
      rfl
    rw [hA, card_erase_of_mem h1, h2]
    omega
  refine ⟨insert p (A.image z), ?_, ?_, ?_⟩
  · intro y hy
    rcases mem_insert.1 (by exact_mod_cast hy) with rfl | hy'
    · exact hpR
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hy'
      exact hz ⟨i, rfl⟩
  · calc (insert p (A.image z)).card ≤ (A.image z).card + 1 := card_insert_le _ _
      _ ≤ A.card + 1 := by
          have := card_image_le (s := A) (f := z)
          omega
      _ = d := hcardA
  · -- The point `x` as a convex combination.
    have hxeq : x = (1 + C)⁻¹ • p + ∑ j ∈ A, ((1 + C)⁻¹ * c j) • z j := by
      have h1 : x = (1 + C)⁻¹ • ((1 + C) • x) := by
        rw [smul_smul, inv_mul_cancel₀ hW.ne', one_smul]
      rw [hcomb, hsumA, smul_add, smul_sum] at h1
      simpa only [smul_smul] using h1
    set G := convexHull ℝ ((insert p (A.image z) : Finset E) : Set E) with hG
    have hGc : Convex ℝ G := convex_convexHull ℝ _
    have hpG : p ∈ G := subset_convexHull ℝ _ (by simp)
    have hzG : ∀ j ∈ A, z j ∈ G := fun j hj => subset_convexHull ℝ _ (by
      have : z j ∈ insert p (A.image z) := mem_insert_of_mem (mem_image_of_mem z hj)
      exact_mod_cast this)
    rw [hxeq]
    have hsumw : (1 + C)⁻¹ + ∑ j ∈ A, (1 + C)⁻¹ * c j = 1 := by
      rw [← mul_sum, ← hsumC, ← mul_one_add, inv_mul_cancel₀ hW.ne']
    have hmain := hGc.sum_mem (t := insertNone A)
      (w := fun o => o.elim (1 + C)⁻¹ fun j => (1 + C)⁻¹ * c j)
      (z := fun o => o.elim p z)
      (fun o _ => by
        cases o with
        | none => exact (inv_pos.2 hW).le
        | some j => exact mul_nonneg (inv_pos.2 hW).le (hc0 j))
      (by simpa using hsumw)
      (fun o ho => by
        cases o with
        | none => exact hpG
        | some j => exact hzG j (by simpa using ho))
    simpa using hmain

/-- **The Fenchel–Eggleston theorem**, in the form of Appendix A of El Gamal and Kim: each point of
the closure of the convex hull of a connected compact set is in the convex hull of at most `d`
points of the set. -/
theorem exists_finset_of_mem_closure_convexHull {R : Set E} (hRc : IsCompact R)
    (hR : IsPreconnected R) (hd : 0 < finrank ℝ E) {x : E} (hx : x ∈ closure (convexHull ℝ R)) :
    ∃ t : Finset E, (t : Set E) ⊆ R ∧ t.card ≤ finrank ℝ E ∧ x ∈ convexHull ℝ (t : Set E) := by
  rw [(isCompact_convexHull_of_isCompact hRc).isClosed.closure_eq] at hx
  exact exists_finset_of_mem_convexHull hR hd hx

/-- **The Fenchel–Eggleston theorem** as a convex combination of an indexed family: at most `d`
points of a connected set suffice. -/
theorem exists_convex_combination_le_finrank {R : Set E} (hR : IsPreconnected R)
    (hd : 0 < finrank ℝ E) {x : E} (hx : x ∈ convexHull ℝ R) :
    ∃ k ≤ finrank ℝ E, ∃ (w : Fin k → ℝ) (z : Fin k → E), (∀ i, z i ∈ R) ∧ (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  classical
  obtain ⟨t, htR, htc, hxt⟩ := exists_finset_of_mem_convexHull hR hd hx
  obtain ⟨a, ha0, ha1, hax⟩ := Finset.mem_convexHull'.1 hxt
  set e := t.equivFin
  refine ⟨t.card, htc, fun i => a (e.symm i), fun i => (e.symm i : E), fun i => htR (e.symm i).2,
    fun i => ha0 _ (e.symm i).2, ?_, ?_⟩
  · rw [e.symm.sum_comp (fun y : t => a y), ← ha1]
    exact sum_coe_sort t a
  · rw [e.symm.sum_comp (fun y : t => a y • (y : E)), ← hax]
    exact sum_coe_sort t fun y => a y • y
