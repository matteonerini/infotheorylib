/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.ICAchievability
public import InfoTheoryLib.Network.MACCardinality

/-!
# The cardinality of the time-sharing variable of the interference channel

The capacity region of the DM-IC with strong interference, Theorem 1 of Lecture 6 of El Gamal and
Kim, is described with a time-sharing variable `Q` with `|𝒬| ≤ 4`, by the technique of Appendix C of
the notes. With a bounded alphabet the region is closed, so the capacity region needs no closure.

## Main definitions

* `icStrongRegionCardBits W K`: the region with `Q` on `Fin K`.

## Main statements

* `icStrongRegionBits_eq_card`: the time-sharing variable can be taken with `|𝒬| = 4`.
* `isClosed_icStrongRegionCardBits`: the region with a bounded time-sharing variable is closed.
* `icCapacityRegionBits_eq_card`: **Theorem 1 of Lecture 6**, with `|𝒬| = 4` and no closure.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 6 and Appendix C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
  {W : α₁ × α₂ → β₁ × β₂ → ℝ}

/-- **Theorem 1 of Lecture 6 of [elgamal2010] with the cardinality bound.** The region
`R₁ ≤ I(X₁; Y₁ | X₂, Q)`, `R₂ ≤ I(X₂; Y₂ | X₁, Q)`,
`R₁ + R₂ ≤ min {I(X₁, X₂; Y₁ | Q), I(X₁, X₂; Y₂ | Q)}` for some `p(q) p(x₁ | q) p(x₂ | q)` with `Q`
on `Fin K`, in bits. -/
def icStrongRegionCardBits (W : α₁ × α₂ → β₁ × β₂ → ℝ) (K : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ (q : Fin K → ℝ) (p₁ : Fin K → α₁ → ℝ) (p₂ : Fin K → α₂ → ℝ),
    IsPMF q ∧ (∀ i, IsPMF (p₁ i)) ∧ (∀ i, IsPMF (p₂ i)) ∧
    R.1 ≤ icAvg₁ q p₁ p₂ (bcMarg₁ W) / log 2 ∧ R.2 ≤ icAvg₂ q p₁ p₂ (bcMarg₂ W) / log 2 ∧
    R.1 + R.2 ≤ icAvg₁₂ q p₁ p₂ (bcMarg₁ W) / log 2 ∧
    R.1 + R.2 ≤ icAvg₁₂ q p₁ p₂ (bcMarg₂ W) / log 2}

/-- **Theorem 1 of Lecture 6 of [elgamal2010].** The time-sharing variable can be taken with
`|𝒬| = 4`. -/
theorem icStrongRegionBits_eq_card (hW : IsChannel W) :
    icStrongRegionBits W = icStrongRegionCardBits W 4 := by
  refine Set.Subset.antisymm ?_ fun R ⟨q, p₁, p₂, h⟩ => ⟨4, q, p₁, p₂, h⟩
  rintro R ⟨k, q, p₁, p₂, hq, hp₁, hp₂, h₁, h₂, h₃, h₄⟩
  obtain ⟨i₀⟩ : Nonempty (Fin k) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  have : Nonempty α₁ := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hp₁ i₀))
  have : Nonempty α₂ := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hp₂ i₀))
  have hS : IsConnected ({p : α₁ → ℝ | IsPMF p} ×ˢ {p : α₂ → ℝ | IsPMF p}) :=
    isConnected_setOf_isPMF.prod isConnected_setOf_isPMF
  set g : Fin 4 → (α₁ → ℝ) × (α₂ → ℝ) → ℝ := ![fun p => macInfo₁ p.1 p.2 (bcMarg₁ W),
    fun p => macInfo₂ p.1 p.2 (bcMarg₂ W), fun p => macInfo₁₂ p.1 p.2 (bcMarg₁ W),
    fun p => macInfo₁₂ p.1 p.2 (bcMarg₂ W)] with hg
  have hgc : ∀ j, ContinuousOn (g j) ({p : α₁ → ℝ | IsPMF p} ×ˢ {p : α₂ → ℝ | IsPMF p}) := by
    intro j
    fin_cases j
    · exact continuousOn_macInfo₁ hW.bcMarg₁
    · exact continuousOn_macInfo₂ hW.bcMarg₂
    · exact continuousOn_macInfo₁₂ hW.bcMarg₁
    · exact continuousOn_macInfo₁₂ hW.bcMarg₂
  have h := exists_fin_mixture_eq_sum (J := Fin 4) (g := g) hS hgc hq.nonneg hq.sum_eq_one
    (r := fun i => (p₁ i, p₂ i)) fun i => ⟨hp₁ i, hp₂ i⟩
  rw [Fintype.card_fin] at h
  obtain ⟨w, z, hz, hw0, hw1, hmix⟩ := h
  have e₁ : icAvg₁ w (fun i => (z i).1) (fun i => (z i).2) (bcMarg₁ W) =
      icAvg₁ q p₁ p₂ (bcMarg₁ W) := hmix 0
  have e₂ : icAvg₂ w (fun i => (z i).1) (fun i => (z i).2) (bcMarg₂ W) =
      icAvg₂ q p₁ p₂ (bcMarg₂ W) := hmix 1
  have e₃ : icAvg₁₂ w (fun i => (z i).1) (fun i => (z i).2) (bcMarg₁ W) =
      icAvg₁₂ q p₁ p₂ (bcMarg₁ W) := hmix 2
  have e₄ : icAvg₁₂ w (fun i => (z i).1) (fun i => (z i).2) (bcMarg₂ W) =
      icAvg₁₂ q p₁ p₂ (bcMarg₂ W) := hmix 3
  exact ⟨w, fun i => (z i).1, fun i => (z i).2, ⟨hw0, hw1⟩, fun i => (hz i).1, fun i => (hz i).2,
    by rwa [e₁], by rwa [e₂], by rwa [e₃], by rwa [e₄]⟩

/-- With a bounded time-sharing variable the region is closed. -/
theorem isClosed_icStrongRegionCardBits (hW : IsChannel W) (K : ℕ) :
    IsClosed (icStrongRegionCardBits W K) := by
  have h := isClosed_exists_forall_le (J := Fin 4) (E := ℝ × ℝ) (isCompact_timeShareLaws K)
    (L := ![fun R => R.1, fun R => R.2, fun R => R.1 + R.2, fun R => R.1 + R.2])
    (F := ![fun P => icAvg₁ P.1 P.2.1 P.2.2 (bcMarg₁ W) / log 2,
      fun P => icAvg₂ P.1 P.2.1 P.2.2 (bcMarg₂ W) / log 2,
      fun P => icAvg₁₂ P.1 P.2.1 P.2.2 (bcMarg₁ W) / log 2,
      fun P => icAvg₁₂ P.1 P.2.1 P.2.2 (bcMarg₂ W) / log 2])
    (by
      intro j
      fin_cases j
      · exact continuous_fst
      · exact continuous_snd
      · exact continuous_fst.add continuous_snd
      · exact continuous_fst.add continuous_snd)
    (by
      intro j
      fin_cases j
      · exact (continuousOn_timeShare (continuousOn_macInfo₁ hW.bcMarg₁)).div_const _
      · exact (continuousOn_timeShare (continuousOn_macInfo₂ hW.bcMarg₂)).div_const _
      · exact (continuousOn_timeShare (continuousOn_macInfo₁₂ hW.bcMarg₁)).div_const _
      · exact (continuousOn_timeShare (continuousOn_macInfo₁₂ hW.bcMarg₂)).div_const _)
  convert h using 1
  ext R
  constructor
  · rintro ⟨q, p₁, p₂, hq, hp₁, hp₂, h₁, h₂, h₃, h₄⟩
    refine ⟨(q, p₁, p₂), ⟨hq, hp₁, hp₂⟩, fun j => ?_⟩
    fin_cases j
    exacts [h₁, h₂, h₃, h₄]
  · rintro ⟨⟨q, p₁, p₂⟩, ⟨hq, hp₁, hp₂⟩, h⟩
    exact ⟨q, p₁, p₂, hq, hp₁, hp₂, h 0, h 1, h 2, h 3⟩

/-- **Theorem 1 of Lecture 6 of [elgamal2010].** The capacity region of a DM-IC with strong
interference, with `|𝒬| = 4` and no closure. -/
theorem icCapacityRegionBits_eq_card (hW : IsChannel W) (hs : IsStrongIC W) :
    icCapacityRegionBits W = icStrongRegionCardBits W 4 := by
  rw [icCapacityRegionBits_eq_closure_icStrongRegionBits hW hs, icStrongRegionBits_eq_card hW,
    (isClosed_icStrongRegionCardBits hW 4).closure_eq]

end InfoTheory
