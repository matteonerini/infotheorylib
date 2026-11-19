/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MarkovChain.DataProcessing

/-!
# Mutual information of general random variables

A finite measurable partition `P = {P₁, …, Pₖ}` of the range of `X` is given by the measurable map
`q : α → Fin k` sending a point to the index of its cell, and the quantization `[X]_P = q(X)` is
a discrete random variable. The mutual information of arbitrary random variables `X` and `Y`
is the supremum of `I([X]_P; [Y]_Q)` over all finite partitions `P` and `Q`. Refining the
partitions increases the quantized mutual information, and for discrete random variables the
supremum is the mutual information (2.28).

## Main definitions

* `pmfOfMeasure ν`: the pmf `x ↦ ν{x}` of a measure on a finite type.
* `quantJointPMF P q r`: the joint pmf `Pr([X]_P = i, [Y]_Q = j)` of the quantizations, (8.53).
* `quantMutualInfo P q r`: `I([X]_P; [Y]_Q)`.
* `mutualInfoSup P`: the mutual information `I(X; Y) = sup_{P, Q} I([X]_P; [Y]_Q)`, (8.54), with
  values in `[0, ∞]`.

## Main statements

* `quantMutualInfo_le_of_refine`: refining the partitions increases `I([X]_P; [Y]_Q)`.
* `mutualInfoSup_eq_of_finite`: for discrete random variables, (8.54) agrees with (2.28).

## Implementation notes

`P` is the joint law of `(X, Y)`, a probability measure on `α × β`. A partition of the range of
`X` into `k` cells is a measurable map `α → Fin k`; empty cells are allowed, which does not change
the supremum.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 8.5
-/

open Real MeasureTheory Finset

@[expose] public noncomputable section

namespace InfoTheory

section Pmf

variable {γ δ : Type*} [Fintype γ]

/-- The pmf `x ↦ ν{x}` of a measure on a finite type. -/
def pmfOfMeasure [MeasurableSpace γ] (ν : Measure γ) (x : γ) : ℝ := (ν {x}).toReal

lemma pmfOfMeasure_isPMF [MeasurableSpace γ] [MeasurableSingletonClass γ] (ν : Measure γ)
    [IsProbabilityMeasure ν] : IsPMF (pmfOfMeasure ν) := by
  refine ⟨fun x => ENNReal.toReal_nonneg, ?_⟩
  rw [show ∑ x, pmfOfMeasure ν x = ∑ x, (ν {x}).toReal from rfl,
    ← ENNReal.toReal_sum fun x _ => measure_ne_top ν {x}, sum_measure_singleton,
    coe_univ, measure_univ, ENNReal.toReal_one]

/-- The pmf of the image measure is the image of the pmf. -/
lemma pmfOfMeasure_map [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace δ]
    [MeasurableSingletonClass δ] (ν : Measure γ) [IsFiniteMeasure ν] (g : γ → δ) :
    pmfOfMeasure (ν.map g) = dist (pmfOfMeasure ν) g := by
  classical
  funext z
  have hpre : g ⁻¹' {z} = ↑(univ.filter fun w => g w = z) := by ext; simp
  rw [pmfOfMeasure, Measure.map_apply Measurable.of_discrete (measurableSet_singleton z), hpre,
    ← sum_measure_singleton, ENNReal.toReal_sum fun x _ => measure_ne_top ν {x}, dist,
    sum_filter]
  rfl

/-- Merging the values of the pair through maps `r` and `s` decreases the mutual information:
`I(r(X); s(Y)) ≤ I(X; Y)`. -/
lemma mutualInfo_dist_prodMap_le [Fintype δ] {γ' δ' : Type*} [Fintype γ'] [Fintype δ']
    {μ : γ × δ → ℝ}
    (hμ : IsPMF μ) (r : γ → γ') (s : δ → δ') :
    I[Prod.fst : Prod.snd ; dist μ (Prod.map r s)] ≤ I[Prod.fst : Prod.snd ; μ] := by
  have e : I[Prod.fst : Prod.snd ; dist μ (Prod.map r s)] =
      I[r ∘ Prod.fst : s ∘ Prod.snd ; μ] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    rfl
  rw [e]
  calc I[r ∘ Prod.fst : s ∘ Prod.snd ; μ] ≤ I[r ∘ Prod.fst : Prod.snd ; μ] :=
        mutualInfo_comp_le hμ _ _ s
    _ = I[Prod.snd : r ∘ Prod.fst ; μ] := mutualInfo_comm hμ _ _
    _ ≤ I[Prod.snd : Prod.fst ; μ] := mutualInfo_comp_le hμ _ _ r
    _ = I[Prod.fst : Prod.snd ; μ] := mutualInfo_comm hμ _ _

end Pmf

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **(8.53)** The joint pmf `Pr([X]_P = i, [Y]_Q = j)` of the quantizations of `(X, Y) ∼ P` by
the partitions with cells `q⁻¹{i}` and `r⁻¹{j}`. -/
def quantJointPMF (P : Measure (α × β)) {k l : ℕ} (q : α → Fin k) (r : β → Fin l) :
    Fin k × Fin l → ℝ :=
  pmfOfMeasure (P.map (Prod.map q r))

lemma quantJointPMF_apply (P : Measure (α × β)) {k l : ℕ} {q : α → Fin k} {r : β → Fin l}
    (hq : Measurable q) (hr : Measurable r) (z : Fin k × Fin l) :
    quantJointPMF P q r z = (P ((q ⁻¹' {z.1}) ×ˢ (r ⁻¹' {z.2}))).toReal := by
  rw [quantJointPMF, pmfOfMeasure, Measure.map_apply (hq.prodMap hr) (measurableSet_singleton z)]
  congr 2
  ext w
  simp [Prod.ext_iff]

lemma quantJointPMF_isPMF (P : Measure (α × β)) [IsProbabilityMeasure P] {k l : ℕ}
    (q : α → Fin k) (r : β → Fin l) : IsPMF (quantJointPMF P q r) :=
  pmfOfMeasure_isPMF _

/-- The mutual information `I([X]_P; [Y]_Q)` of the quantizations. -/
def quantMutualInfo (P : Measure (α × β)) {k l : ℕ} (q : α → Fin k) (r : β → Fin l) : ℝ :=
  I[Prod.fst : Prod.snd ; quantJointPMF P q r]

lemma quantMutualInfo_nonneg (P : Measure (α × β)) [IsProbabilityMeasure P] {k l : ℕ}
    (q : α → Fin k) (r : β → Fin l) :
    0 ≤ quantMutualInfo P q r :=
  mutualInfo_nonneg (quantJointPMF_isPMF P q r) _ _

/-- **Definition (8.54).** The mutual information of two random variables with joint law `P`:
`I(X; Y) = sup_{P, Q} I([X]_P; [Y]_Q)`, the supremum over all finite measurable partitions. -/
def mutualInfoSup (P : Measure (α × β)) : ENNReal :=
  ⨆ (k : ℕ) (l : ℕ) (q : {q : α → Fin k // Measurable q}) (r : {r : β → Fin l // Measurable r}),
    ENNReal.ofReal (quantMutualInfo P q.val r.val)

lemma quantMutualInfo_le_mutualInfoSup (P : Measure (α × β)) {k l : ℕ} {q : α → Fin k}
    {r : β → Fin l} (hq : Measurable q) (hr : Measurable r) :
    ENNReal.ofReal (quantMutualInfo P q r) ≤ mutualInfoSup P :=
  le_iSup_of_le k <| le_iSup_of_le l <| le_iSup_of_le ⟨q, hq⟩ <| le_iSup_of_le ⟨r, hr⟩ le_rfl

/-- **Section 8.5.** Refining the partitions increases the mutual information of the
quantizations: if every cell of `P` is a union of cells of `P'` and every cell of `Q` is a union
of cells of `Q'`, then `I([X]_P; [Y]_Q) ≤ I([X]_{P'}; [Y]_{Q'})`. -/
theorem quantMutualInfo_le_of_refine (P : Measure (α × β)) [IsProbabilityMeasure P]
    {k l k' l' : ℕ} {q : α → Fin k'} {r : β → Fin l'} (hq : Measurable q) (hr : Measurable r)
    (s : Fin k' → Fin k) (t : Fin l' → Fin l) :
    quantMutualInfo P (s ∘ q) (t ∘ r) ≤ quantMutualInfo P q r := by
  have h : quantJointPMF P (s ∘ q) (t ∘ r) = dist (quantJointPMF P q r) (Prod.map s t) := by
    rw [quantJointPMF, show Prod.map (s ∘ q) (t ∘ r) = Prod.map s t ∘ Prod.map q r from rfl,
      ← Measure.map_map Measurable.of_discrete (hq.prodMap hr), pmfOfMeasure_map]
    rfl
  rw [quantMutualInfo, h]
  exact mutualInfo_dist_prodMap_le (quantJointPMF_isPMF P q r) s t

/-- **Section 8.5.** For discrete random variables, the master definition (8.54) agrees with the
definition (2.28) of mutual information: the supremum is attained by the partitions into
points. -/
theorem mutualInfoSup_eq_of_finite [Fintype α] [MeasurableSingletonClass α] [Fintype β]
    [MeasurableSingletonClass β] (P : Measure (α × β)) [IsProbabilityMeasure P] :
    mutualInfoSup P = ENNReal.ofReal I[Prod.fst : Prod.snd ; pmfOfMeasure P] := by
  have hP := pmfOfMeasure_isPMF P
  have hquant : ∀ {k l : ℕ} (q : α → Fin k) (r : β → Fin l),
      quantJointPMF P q r = dist (pmfOfMeasure P) (Prod.map q r) := fun q r =>
    pmfOfMeasure_map P (Prod.map q r)
  refine le_antisymm (iSup_le fun k => iSup_le fun l => iSup_le fun q => iSup_le fun r => ?_) ?_
  · rw [quantMutualInfo, hquant]
    exact ENNReal.ofReal_le_ofReal (mutualInfo_dist_prodMap_le hP q.val r.val)
  · set e := Fintype.equivFin α
    set e' := Fintype.equivFin β
    refine le_trans (le_of_eq ?_) (quantMutualInfo_le_mutualInfoSup P (q := e) (r := e')
      Measurable.of_discrete Measurable.of_discrete)
    congr 1
    rw [quantMutualInfo, hquant]
    have h1 : I[Prod.fst : Prod.snd ; dist (pmfOfMeasure P) (Prod.map e e')] =
        I[e ∘ Prod.fst : e' ∘ Prod.snd ; pmfOfMeasure P] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [dist_pair_fst_snd]
      rfl
    rw [h1, mutualInfo_congr_right hP (e ∘ Prod.fst) (Y := Prod.snd) (Y' := e' ∘ Prod.snd) e'
      e'.injective fun _ => rfl, mutualInfo_comm hP (e ∘ Prod.fst),
      mutualInfo_congr_right hP Prod.snd (Y := Prod.fst) (Y' := e ∘ Prod.fst) e e.injective
      fun _ => rfl, mutualInfo_comm hP]

end InfoTheory
