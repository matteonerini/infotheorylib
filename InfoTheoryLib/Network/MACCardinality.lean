/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.CardinalityBound
public import InfoTheoryLib.Network.MACBits
public import InfoTheoryLib.Networking.AsyncMAC

/-!
# The cardinality of the time-sharing variable of the multiple-access channel

The capacity region of the DM-MAC is described with a time-sharing variable `Q` with `|𝒬| ≤ 3`, by
the remark in Appendix C of El Gamal and Kim. With a bounded alphabet the region is closed, so the
capacity region needs no closure.

## Main definitions

* `macRegionCard W K`: the region with `Q` on `Fin K`.

## Main statements

* `macRegion_eq_card`: the time-sharing variable can be taken with `|𝒬| = 3`.
* `isClosed_macRegionCard`: the region with a bounded time-sharing variable is closed.
* `macCapacityRegion_eq_card`, `macCapacityRegionBits_eq_card`: the capacity region with `|𝒬| = 3`
  and no closure.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  C
-/

open Real Finset

open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}

/-- The rate pairs with `R₁ ≤ I(X₁; Y | X₂, Q)`, `R₂ ≤ I(X₂; Y | X₁, Q)` and
`R₁ + R₂ ≤ I(X₁, X₂; Y | Q)` for some `p(q) p(x₁ | q) p(x₂ | q)` with `Q` on `Fin K`. -/
def macRegionCard (W : α₁ × α₂ → β → ℝ) (K : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ (q : Fin K → ℝ) (p₁ : Fin K → α₁ → ℝ) (p₂ : Fin K → α₂ → ℝ),
    IsPMF q ∧ (∀ i, IsPMF (p₁ i)) ∧ (∀ i, IsPMF (p₂ i)) ∧
    R.1 ≤ ∑ i, q i * macInfo₁ (p₁ i) (p₂ i) W ∧ R.2 ≤ ∑ i, q i * macInfo₂ (p₁ i) (p₂ i) W ∧
    R.1 + R.2 ≤ ∑ i, q i * macInfo₁₂ (p₁ i) (p₂ i) W}

/-- **The remark on page C-8 of [elgamal2010].** The time-sharing variable of the DM-MAC can be
taken with `|𝒬| = 3`. -/
theorem macRegion_eq_card (hW : IsChannel W) : macRegion W = macRegionCard W 3 := by
  refine Set.Subset.antisymm ?_ fun R ⟨q, p₁, p₂, h⟩ => ⟨3, q, p₁, p₂, h⟩
  rintro R ⟨k, q, p₁, p₂, hq, hp₁, hp₂, h₁, h₂, h₁₂⟩
  obtain ⟨i₀⟩ : Nonempty (Fin k) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  have : Nonempty α₁ := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hp₁ i₀))
  have : Nonempty α₂ := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hp₂ i₀))
  have hS : IsConnected ({p : α₁ → ℝ | IsPMF p} ×ˢ {p : α₂ → ℝ | IsPMF p}) :=
    isConnected_setOf_isPMF.prod isConnected_setOf_isPMF
  set g : Fin 3 → (α₁ → ℝ) × (α₂ → ℝ) → ℝ := ![fun p => macInfo₁ p.1 p.2 W,
    fun p => macInfo₂ p.1 p.2 W, fun p => macInfo₁₂ p.1 p.2 W] with hg
  have hgc : ∀ j, ContinuousOn (g j) ({p : α₁ → ℝ | IsPMF p} ×ˢ {p : α₂ → ℝ | IsPMF p}) := by
    intro j
    fin_cases j
    · exact continuousOn_macInfo₁ hW
    · exact continuousOn_macInfo₂ hW
    · exact continuousOn_macInfo₁₂ hW
  have h := exists_fin_mixture_eq_sum (J := Fin 3) (g := g) hS hgc hq.nonneg hq.sum_eq_one
    (r := fun i => (p₁ i, p₂ i)) fun i => ⟨hp₁ i, hp₂ i⟩
  rw [Fintype.card_fin] at h
  obtain ⟨w, z, hz, hw0, hw1, hmix⟩ := h
  refine ⟨w, fun i => (z i).1, fun i => (z i).2, ⟨hw0, hw1⟩, fun i => (hz i).1, fun i => (hz i).2,
    ?_, ?_, ?_⟩
  · have e := hmix 0
    simp only [hg, Matrix.cons_val_zero] at e
    rwa [e]
  · have e := hmix 1
    simp only [hg, Matrix.cons_val_one, Matrix.cons_val_zero] at e
    rwa [e]
  · have e := hmix 2
    simp only [hg, Matrix.cons_val] at e
    rwa [e]

/-- The laws of `(Q, X₁, X₂)` with `Q` on `Fin K` and the inputs independent given `Q`. -/
def timeShareLaws (K : ℕ) (α₁ α₂ : Type*) [Fintype α₁] [Fintype α₂] :
    Set ((Fin K → ℝ) × (Fin K → α₁ → ℝ) × (Fin K → α₂ → ℝ)) :=
  {P | IsPMF P.1 ∧ (∀ i, IsPMF (P.2.1 i)) ∧ ∀ i, IsPMF (P.2.2 i)}

/-- The set of these laws is compact. -/
lemma isCompact_timeShareLaws (K : ℕ) : IsCompact (timeShareLaws K α₁ α₂) := by
  have e : timeShareLaws K α₁ α₂ = {q : Fin K → ℝ | IsPMF q} ×ˢ
      (Set.pi Set.univ (fun _ => {p : α₁ → ℝ | IsPMF p}) ×ˢ
        Set.pi Set.univ fun _ => {p : α₂ → ℝ | IsPMF p}) := by
    ext P
    simp [timeShareLaws, Set.mem_prod, Set.mem_pi]
  rw [e]
  exact isCompact_setOf_isPMF.prod
    ((isCompact_univ_pi fun _ => isCompact_setOf_isPMF).prod
      (isCompact_univ_pi fun _ => isCompact_setOf_isPMF))

/-- A mean over `Q` of a continuous function of the inputs is continuous in the law. -/
lemma continuousOn_timeShare {K : ℕ} {f : (α₁ → ℝ) × (α₂ → ℝ) → ℝ}
    (hf : ContinuousOn f {p | IsPMF p.1 ∧ IsPMF p.2}) :
    ContinuousOn (fun P : (Fin K → ℝ) × (Fin K → α₁ → ℝ) × (Fin K → α₂ → ℝ) =>
      ∑ i, P.1 i * f (P.2.1 i, P.2.2 i)) (timeShareLaws K α₁ α₂) := by
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine (Continuous.continuousOn (by fun_prop)).mul (hf.comp (Continuous.continuousOn ?_) ?_)
  · fun_prop
  · exact fun P hP => ⟨hP.2.1 i, hP.2.2 i⟩

/-- With a bounded time-sharing variable the region is closed. -/
theorem isClosed_macRegionCard (hW : IsChannel W) (K : ℕ) : IsClosed (macRegionCard W K) := by
  have h := isClosed_exists_forall_le (J := Fin 3) (E := ℝ × ℝ) (isCompact_timeShareLaws K)
    (L := ![fun R => R.1, fun R => R.2, fun R => R.1 + R.2])
    (F := ![fun P => ∑ i, P.1 i * macInfo₁ (P.2.1 i) (P.2.2 i) W,
      fun P => ∑ i, P.1 i * macInfo₂ (P.2.1 i) (P.2.2 i) W,
      fun P => ∑ i, P.1 i * macInfo₁₂ (P.2.1 i) (P.2.2 i) W])
    (by
      intro j
      fin_cases j
      · exact continuous_fst
      · exact continuous_snd
      · exact continuous_fst.add continuous_snd)
    (by
      intro j
      fin_cases j
      · exact continuousOn_timeShare (continuousOn_macInfo₁ hW)
      · exact continuousOn_timeShare (continuousOn_macInfo₂ hW)
      · exact continuousOn_timeShare (continuousOn_macInfo₁₂ hW))
  convert h using 1
  ext R
  constructor
  · rintro ⟨q, p₁, p₂, hq, hp₁, hp₂, h₁, h₂, h₁₂⟩
    refine ⟨(q, p₁, p₂), ⟨hq, hp₁, hp₂⟩, fun j => ?_⟩
    fin_cases j
    exacts [h₁, h₂, h₁₂]
  · rintro ⟨⟨q, p₁, p₂⟩, ⟨hq, hp₁, hp₂⟩, h⟩
    exact ⟨q, p₁, p₂, hq, hp₁, hp₂, h 0, h 1, h 2⟩

/-- **The capacity region of the DM-MAC in nats with `|𝒬| = 3`**, with no closure. -/
theorem macCapacityRegion_eq_card [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macCapacityRegion W = macRegionCard W 3 := by
  rw [macCapacityRegion_eq_closure_macRegion hW, macRegion_eq_card hW,
    (isClosed_macRegionCard hW 3).closure_eq]

/-- **The capacity region of the DM-MAC in bits with `|𝒬| = 3`**, with no closure. -/
theorem macCapacityRegionBits_eq_card [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macCapacityRegionBits W = (log 2)⁻¹ • macRegionCard W 3 := by
  rw [macCapacityRegionBits_eq_smul hW, macCapacityRegion_eq_card hW]

end InfoTheory
