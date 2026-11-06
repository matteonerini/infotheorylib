/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.CardinalityBound
public import InfoTheoryLib.Network.GaussianVector

/-!
# The dual MAC regions are closed

The union of the pentagons of the Gaussian vector MAC over the covariance matrices is a closed set,
for each of the two power constraints, since the set of covariance matrices is compact and the rates
are continuous on it. The notes use this in Lecture 10 of El Gamal and Kim, for the boundary of the
dual MAC region.

## Main statements

* `isCompact_posSemidef_trace_le`: `{K ≽ 0 : tr K ≤ P}` is compact.
* `isClosed_gvMACRegion`: the region for the individual power constraints is closed.
* `isClosed_gvSumMACRegion`: the region for the sum power constraint is closed.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 10
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

section Compact

/-- The positive semidefinite matrices form a closed set. -/
lemma isClosed_posSemidef {t : Type*} [Finite t] : IsClosed {K : Matrix t t ℝ | K.PosSemidef} := by
  have := Fintype.ofFinite t
  have e : {K : Matrix t t ℝ | K.PosSemidef} =
      (⋂ i, ⋂ j, {K | K j i = K i j}) ∩ ⋂ x : t → ℝ, {K | 0 ≤ x ⬝ᵥ (K *ᵥ x)} := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      posSemidef_iff_dotProduct_mulVec]
    refine and_congr ⟨fun h i j => ?_, fun h => ?_⟩ ⟨fun h x => by simpa using h x,
      fun h x => by simpa using h x⟩
    · have := congrFun (congrFun h i) j
      simpa using this
    · ext i j
      simpa using h i j
  rw [e]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq
    (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)).inter
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem i j).mul continuous_const)

variable {t : Type*} [Fintype t]

/-- An entry of a positive semidefinite matrix is at most the trace in absolute value. -/
lemma abs_apply_le_trace {K : Matrix t t ℝ} (hK : K.PosSemidef) (i j : t) : |K i j| ≤ K.trace := by
  classical
  obtain ⟨C, rfl⟩ := exists_eq_transpose_mul_self hK
  have hd : ∀ l, (Cᵀ * C) l l = ∑ k, C k l ^ 2 := fun l => by
    simp [Matrix.mul_apply, sq]
  have hnn : ∀ l, 0 ≤ (Cᵀ * C) l l := fun l => by
    rw [hd]
    exact sum_nonneg fun k _ => sq_nonneg _
  have htr : (Cᵀ * C).trace = ∑ l, (Cᵀ * C) l l := rfl
  have hle : ∀ l, (Cᵀ * C) l l ≤ (Cᵀ * C).trace := fun l => by
    rw [htr]
    exact single_le_sum (fun l _ => hnn l) (mem_univ l)
  have hij : ∀ s : ℝ, s ^ 2 = 1 → s * (Cᵀ * C) i j ≤ ((Cᵀ * C) i i + (Cᵀ * C) j j) / 2 :=
      fun s hs => by
    simp only [hd, Matrix.mul_apply, transpose_apply, mul_sum, ← sum_add_distrib, sum_div]
    refine sum_le_sum fun k _ => ?_
    nlinarith [sq_nonneg (s * C k i - C k j)]
  have hsum : (Cᵀ * C) i i + (Cᵀ * C) j j ≤ 2 * (Cᵀ * C).trace :=
    by linarith [hle i, hle j]
  rw [abs_le]
  have h₁ := hij 1 (by norm_num)
  have h₂ := hij (-1) (by norm_num)
  constructor <;> linarith

/-- **The covariance matrices with a trace constraint form a compact set.** -/
theorem isCompact_posSemidef_trace_le (P : ℝ) :
    IsCompact {K : Matrix t t ℝ | K.PosSemidef ∧ K.trace ≤ P} := by
  have hcl : IsClosed {K : Matrix t t ℝ | K.PosSemidef ∧ K.trace ≤ P} := by
    have e : {K : Matrix t t ℝ | K.PosSemidef ∧ K.trace ≤ P} =
        {K | K.PosSemidef} ∩ {K | K.trace ≤ P} := rfl
    rw [e]
    exact isClosed_posSemidef.inter (isClosed_le (continuous_id.matrix_trace) continuous_const)
  have hbox : IsCompact (Set.pi Set.univ fun _ : t => Set.pi Set.univ fun _ : t =>
      Set.Icc (-P) P : Set (t → t → ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine IsCompact.of_isClosed_subset hbox hcl fun K hK i _ j _ => ?_
  have h := (abs_apply_le_trace hK.1 i j).trans hK.2
  exact abs_le.1 h

end Compact

section Regions

variable {r t₁ t₂ : Type*} [Fintype r] [Fintype t₁] [Fintype t₂] [DecidableEq r]
  (G₁ : Matrix r t₁ ℝ) (G₂ : Matrix r t₂ ℝ)

/-- The covariance matrices of the two senders. -/
private abbrev gvPairs (t₁ t₂ : Type*) : Set (Matrix t₁ t₁ ℝ × Matrix t₂ t₂ ℝ) :=
  {K | K.1.PosSemidef ∧ K.2.PosSemidef}

/-- The sum rate is continuous on the covariance matrices. -/
private lemma continuousOn_sumRate :
    ContinuousOn (fun K : Matrix t₁ t₁ ℝ × Matrix t₂ t₂ ℝ =>
      1 / 2 * log (G₁ * K.1 * G₁ᵀ + G₂ * K.2 * G₂ᵀ + 1).det) (gvPairs t₁ t₂) := by
  refine continuousOn_const.mul (ContinuousOn.log (Continuous.continuousOn ?_) fun K hK => ?_)
  · refine Continuous.matrix_det ?_
    exact (((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).add
      ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const)).add
      continuous_const
  · have h := Matrix.PosDef.posSemidef_add ((posSemidef_mul_mul_transpose hK.1 G₁).add
      (posSemidef_mul_mul_transpose hK.2 G₂)) (Matrix.PosDef.one (n := r))
    exact h.det_pos.ne'

/-- The rate of one sender is continuous on its covariance matrices. -/
private lemma continuousOn_gvRate {t : Type*} [Fintype t] (G : Matrix r t ℝ) :
    ContinuousOn (fun K : Matrix t t ℝ => gvRate G K) {K | K.PosSemidef} := by
  refine continuousOn_const.mul (ContinuousOn.log (Continuous.continuousOn ?_) fun K hK => ?_)
  · exact Continuous.matrix_det (((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).add continuous_const)
  · exact (Matrix.PosDef.posSemidef_add (posSemidef_mul_mul_transpose hK G)
      (Matrix.PosDef.one (n := r))).det_pos.ne'

/-- The five bounds that define a pentagon, on a compact set of covariance matrices. -/
private lemma isClosed_pentagons {S : Set (Matrix t₁ t₁ ℝ × Matrix t₂ t₂ ℝ)} (hS : IsCompact S)
    (hsub : S ⊆ gvPairs t₁ t₂) :
    IsClosed {R : ℝ × ℝ | ∃ K ∈ S, R ∈ gvMACRates G₁ G₂ K.1 K.2} := by
  have h := isClosed_exists_forall_le (J := Fin 5) (E := ℝ × ℝ) hS
    (L := ![fun R => -R.1, fun R => -R.2, fun R => R.1, fun R => R.2, fun R => R.1 + R.2])
    (F := ![fun _ => 0, fun _ => 0, fun K => gvRate G₁ K.1, fun K => gvRate G₂ K.2,
      fun K => 1 / 2 * log (G₁ * K.1 * G₁ᵀ + G₂ * K.2 * G₂ᵀ + 1).det])
    (by
      intro j
      fin_cases j
      · exact continuous_fst.neg
      · exact continuous_snd.neg
      · exact continuous_fst
      · exact continuous_snd
      · exact continuous_fst.add continuous_snd)
    (by
      intro j
      fin_cases j
      · exact continuousOn_const
      · exact continuousOn_const
      · exact ((continuousOn_gvRate G₁).comp continuous_fst.continuousOn
          fun K hK => (hsub hK).1)
      · exact ((continuousOn_gvRate G₂).comp continuous_snd.continuousOn
          fun K hK => (hsub hK).2)
      · exact (continuousOn_sumRate G₁ G₂).mono hsub)
  convert h using 1
  ext R
  constructor
  · rintro ⟨K, hK, h₀, h₁, h₂, h₃, h₄⟩
    refine ⟨K, hK, fun j => ?_⟩
    fin_cases j
    · simpa using h₀
    · simpa using h₁
    · exact h₂
    · exact h₃
    · exact h₄
  · rintro ⟨K, hK, h⟩
    have h₀ := h 0
    have h₁ := h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_nonpos] at h₀ h₁
    exact ⟨K, hK, h₀, h₁, h 2, h 3, h 4⟩

/-- **Lecture 10 of [elgamal2010], page 10-42.** The union of the pentagons for the individual power
constraints is closed. -/
theorem isClosed_gvMACRegion (P : ℝ) : IsClosed (gvMACRegion G₁ G₂ P) := by
  have hS : IsCompact ({K : Matrix t₁ t₁ ℝ | K.PosSemidef ∧ K.trace ≤ P} ×ˢ
      {K : Matrix t₂ t₂ ℝ | K.PosSemidef ∧ K.trace ≤ P}) :=
    (isCompact_posSemidef_trace_le P).prod (isCompact_posSemidef_trace_le P)
  convert isClosed_pentagons G₁ G₂ hS fun K hK => ⟨hK.1.1, hK.2.1⟩ using 1
  ext R
  constructor
  · rintro ⟨K₁, K₂, h₁, h₂, t₁', t₂', hR⟩
    exact ⟨(K₁, K₂), ⟨⟨h₁, t₁'⟩, h₂, t₂'⟩, hR⟩
  · rintro ⟨⟨K₁, K₂⟩, ⟨⟨h₁, t₁'⟩, h₂, t₂'⟩, hR⟩
    exact ⟨K₁, K₂, h₁, h₂, t₁', t₂', hR⟩

/-- **Lecture 10 of [elgamal2010], page 10-42.** The union of the pentagons for the sum power
constraint is closed. -/
theorem isClosed_gvSumMACRegion (P : ℝ) : IsClosed (gvSumMACRegion G₁ G₂ P) := by
  have hS : IsCompact (({K : Matrix t₁ t₁ ℝ | K.PosSemidef ∧ K.trace ≤ P} ×ˢ
      {K : Matrix t₂ t₂ ℝ | K.PosSemidef ∧ K.trace ≤ P}) ∩ {K | K.1.trace + K.2.trace ≤ P}) :=
    ((isCompact_posSemidef_trace_le P).prod (isCompact_posSemidef_trace_le P)).inter_right
      (isClosed_le ((continuous_fst.matrix_trace).add (continuous_snd.matrix_trace))
        continuous_const)
  convert isClosed_pentagons G₁ G₂ hS fun K hK => ⟨hK.1.1.1, hK.1.2.1⟩ using 1
  ext R
  constructor
  · rintro ⟨K₁, K₂, h₁, h₂, hs, hR⟩
    have n₁ := h₁.trace_nonneg
    have n₂ := h₂.trace_nonneg
    exact ⟨(K₁, K₂), ⟨⟨⟨h₁, by linarith⟩, h₂, by linarith⟩, hs⟩, hR⟩
  · rintro ⟨⟨K₁, K₂⟩, ⟨⟨⟨h₁, -⟩, h₂, -⟩, hs⟩, hR⟩
    exact ⟨K₁, K₂, h₁, h₂, hs, hR⟩

end Regions

end InfoTheory
