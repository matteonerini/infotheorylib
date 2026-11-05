/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MultiWay

/-!
# Communication for omniscience: two and three nodes

The examples of page 21-17 of El Gamal and Kim.

## Main statements

* `mwRegion_two`, `rCFO_two`: two nodes; this is the two-way lossless coding of page 21-14.
* `mwRegion_three`, `rCFO_three`: three nodes and `A = {1, 2}`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Two nodes -/

section Two

variable {α : Fin 2 → Type*} [∀ j, Fintype (α j)] {p : (∀ j, α j) → ℝ}

/-- **Page 21-17 of [elgamal2010]: two nodes.** `R₁ ≥ H(X₁ | X₂)` and `R₂ ≥ H(X₂ | X₁)`. -/
theorem mwRegion_two (hp : IsPMF p) (R : Fin 2 → ℝ) :
    R ∈ mwRegion p univ ↔
      swCondH p {0} / log 2 ≤ R 0 ∧ swCondH p {1} / log 2 ≤ R 1 := by
  have hl := log_pos one_lt_two
  have hH : ∀ S, 0 ≤ swCondH p S / log 2 := fun S => div_nonneg (condEntropy_nonneg hp _ _) hl.le
  constructor
  · intro h
    have h₀ := h.2 1 (mem_univ _) {0} (by decide)
    have h₁ := h.2 0 (mem_univ _) {1} (by decide)
    simpa using And.intro h₀ h₁
  · rintro ⟨h₀, h₁⟩
    refine ⟨fun j => ?_, fun k _ S hk => ?_⟩
    · fin_cases j
      · exact (hH _).trans h₀
      · exact (hH _).trans h₁
    · have hS : k = 0 ∧ (S = ∅ ∨ S = {1}) ∨ k = 1 ∧ (S = ∅ ∨ S = {0}) := by
        revert k S
        decide
      rcases hS with ⟨-, rfl | rfl⟩ | ⟨-, rfl | rfl⟩
      · simp [swCondH_empty hp]
      · simpa using h₁
      · simp [swCondH_empty hp]
      · simpa using h₀

/-- **Page 21-17 of [elgamal2010].** `R_CFO({1, 2}) = H(X₁ | X₂) + H(X₂ | X₁)`. -/
theorem rCFO_two (hp : IsPMF p) :
    rCFO p univ = swCondH p {0} / log 2 + swCondH p {1} / log 2 := by
  refine IsLeast.csInf_eq ⟨⟨![swCondH p {0} / log 2, swCondH p {1} / log 2], ?_, ?_⟩, ?_⟩
  · exact (mwRegion_two hp _).2 ⟨le_rfl, le_rfl⟩
  · simp [Fin.sum_univ_two]
  · rintro _ ⟨R, hR, rfl⟩
    obtain ⟨h₀, h₁⟩ := (mwRegion_two hp R).1 hR
    simp only [Fin.sum_univ_two]
    linarith

end Two

/-! ### Three nodes -/

section Three

variable {α : Fin 3 → Type*} [∀ j, Fintype (α j)] {p : (∀ j, α j) → ℝ}

/-- `H(X₁, X₃ | X₂) = H(X₃ | X₂) + H(X₁ | X₂, X₃)`, in the labels of the notes. -/
lemma swCondH_zero_two (hp : IsPMF p) :
    swCondH p {0, 2} = H[fun x : ∀ j, α j => x 2 | fun x => x 1 ; p] + swCondH p {0} := by
  have h₁ : swCondH p {0, 2} = H[pair (fun x : ∀ j, α j => x 2) (fun x => x 0) |
      fun x => x 1 ; p] := by
    have e₁ : H[pair (fun x : ∀ j, α j => x 2) (fun x => x 0) | fun x => x 1 ; p] =
        H[swPart ({0, 2} : Finset (Fin 3)) | fun x : ∀ j, α j => x 1 ; p] := by
      refine condEntropy_congr_left hp _
        (fun v => (v ⟨2, by decide⟩, v ⟨0, by decide⟩)) ?_ fun _ => rfl
      intro v w h
      funext ⟨j, hj⟩
      have hj' : j = 0 ∨ j = 2 := by simpa using hj
      rcases hj' with rfl | rfl
      · exact (Prod.mk.inj h).2
      · exact (Prod.mk.inj h).1
    rw [e₁, swCondH]
    refine (condEntropy_congr_right hp _ (X := swRest ({0, 2} : Finset (Fin 3)))
      (X' := fun x => x 1) (fun v => v ⟨1, by decide⟩) ?_ fun _ => rfl).symm
    intro v w h
    funext ⟨j, hj⟩
    have hj' : j = 1 := by
      revert j
      decide
    subst hj'
    exact h
  have h₂ : swCondH p {0} = H[fun x : ∀ j, α j => x 0 |
      pair (fun x : ∀ j, α j => x 2) (fun x => x 1) ; p] := by
    have e₁ : H[fun x : ∀ j, α j => x 0 | pair (fun x : ∀ j, α j => x 2) (fun x => x 1) ; p] =
        H[swPart ({0} : Finset (Fin 3)) | pair (fun x : ∀ j, α j => x 2) (fun x => x 1) ; p] := by
      refine condEntropy_congr_left hp _ (fun v => v ⟨0, by decide⟩) ?_ fun _ => rfl
      intro v w h
      funext ⟨j, hj⟩
      have hj' : j = 0 := by simpa using hj
      subst hj'
      exact h
    rw [e₁, swCondH]
    refine (condEntropy_congr_right hp _ (X := swRest ({0} : Finset (Fin 3)))
      (X' := pair (fun x : ∀ j, α j => x 2) (fun x => x 1)) (fun v => (v ⟨2, by decide⟩, v ⟨1, by
        decide⟩))
      ?_ fun _ => rfl).symm
    intro v w h
    funext ⟨j, hj⟩
    have hj' : j = 1 ∨ j = 2 := by
      revert j
      decide
    rcases hj' with rfl | rfl
    · exact (Prod.mk.inj h).2
    · exact (Prod.mk.inj h).1
  rw [h₁, h₂, chain_rule_cond hp]

/-- `H(X₂, X₃ | X₁) = H(X₃ | X₁) + H(X₂ | X₁, X₃)`, in the labels of the notes. -/
lemma swCondH_one_two (hp : IsPMF p) :
    swCondH p {1, 2} = H[fun x : ∀ j, α j => x 2 | fun x => x 0 ; p] + swCondH p {1} := by
  have h₁ : swCondH p {1, 2} = H[pair (fun x : ∀ j, α j => x 2) (fun x => x 1) |
      fun x => x 0 ; p] := by
    have e₁ : H[pair (fun x : ∀ j, α j => x 2) (fun x => x 1) | fun x => x 0 ; p] =
        H[swPart ({1, 2} : Finset (Fin 3)) | fun x : ∀ j, α j => x 0 ; p] := by
      refine condEntropy_congr_left hp _
        (fun v => (v ⟨2, by decide⟩, v ⟨1, by decide⟩)) ?_ fun _ => rfl
      intro v w h
      funext ⟨j, hj⟩
      have hj' : j = 1 ∨ j = 2 := by simpa using hj
      rcases hj' with rfl | rfl
      · exact (Prod.mk.inj h).2
      · exact (Prod.mk.inj h).1
    rw [e₁, swCondH]
    refine (condEntropy_congr_right hp _ (X := swRest ({1, 2} : Finset (Fin 3)))
      (X' := fun x => x 0) (fun v => v ⟨0, by decide⟩) ?_ fun _ => rfl).symm
    intro v w h
    funext ⟨j, hj⟩
    have hj' : j = 0 := by
      revert j
      decide
    subst hj'
    exact h
  have h₂ : swCondH p {1} = H[fun x : ∀ j, α j => x 1 |
      pair (fun x : ∀ j, α j => x 2) (fun x => x 0) ; p] := by
    have e₁ : H[fun x : ∀ j, α j => x 1 | pair (fun x : ∀ j, α j => x 2) (fun x => x 0) ; p] =
        H[swPart ({1} : Finset (Fin 3)) | pair (fun x : ∀ j, α j => x 2) (fun x => x 0) ; p] := by
      refine condEntropy_congr_left hp _ (fun v => v ⟨1, by decide⟩) ?_ fun _ => rfl
      intro v w h
      funext ⟨j, hj⟩
      have hj' : j = 1 := by simpa using hj
      subst hj'
      exact h
    rw [e₁, swCondH]
    refine (condEntropy_congr_right hp _ (X := swRest ({1} : Finset (Fin 3)))
      (X' := pair (fun x : ∀ j, α j => x 2) (fun x => x 0)) (fun v => (v ⟨2, by decide⟩, v ⟨0, by
        decide⟩))
      ?_ fun _ => rfl).symm
    intro v w h
    funext ⟨j, hj⟩
    have hj' : j = 0 ∨ j = 2 := by
      revert j
      decide
    rcases hj' with rfl | rfl
    · exact (Prod.mk.inj h).2
    · exact (Prod.mk.inj h).1
  rw [h₁, h₂, chain_rule_cond hp]

/-- `H(X₃ | X₁, X₂) ≤ H(X₃ | X₂)`, in the labels of the notes. -/
lemma swCondH_two_le (hp : IsPMF p) :
    swCondH p {2} ≤ H[fun x : ∀ j, α j => x 2 | fun x => x 1 ; p] := by
  have e₁ : H[fun x : ∀ j, α j => x 2 | swRest ({2} : Finset (Fin 3)) ; p] =
      H[swPart ({2} : Finset (Fin 3)) | swRest ({2} : Finset (Fin 3)) ; p] := by
    refine condEntropy_congr_left hp _ (fun v => v ⟨2, by decide⟩) ?_ fun _ => rfl
    intro v w h
    funext ⟨j, hj⟩
    have hj' : j = 2 := by simpa using hj
    subst hj'
    exact h
  rw [swCondH, ← e₁]
  have h := condEntropy_le_condEntropy_comp hp (fun x : ∀ j, α j => x 2)
    (swRest ({2} : Finset (Fin 3))) (fun v => v ⟨1, by decide⟩)
  exact h

/-- **Page 21-17 of [elgamal2010]: three nodes and `A = {1, 2}`.** The region. -/
theorem mwRegion_three (hp : IsPMF p) (R : Fin 3 → ℝ) :
    R ∈ mwRegion p {0, 1} ↔ swCondH p {0} / log 2 ≤ R 0 ∧ swCondH p {1} / log 2 ≤ R 1 ∧
      swCondH p {2} / log 2 ≤ R 2 ∧ swCondH p {0, 2} / log 2 ≤ R 0 + R 2 ∧
      swCondH p {1, 2} / log 2 ≤ R 1 + R 2 := by
  have hl := log_pos one_lt_two
  have hH : ∀ S, 0 ≤ swCondH p S / log 2 := fun S => div_nonneg (condEntropy_nonneg hp _ _) hl.le
  constructor
  · intro h
    have h₀ := h.2 1 (by decide) {0} (by decide)
    have h₁ := h.2 0 (by decide) {1} (by decide)
    have h₂ := h.2 0 (by decide) {2} (by decide)
    have h₃ := h.2 1 (by decide) {0, 2} (by decide)
    have h₄ := h.2 0 (by decide) {1, 2} (by decide)
    rw [sum_singleton] at h₀ h₁ h₂
    rw [sum_pair (by decide)] at h₃ h₄
    exact ⟨h₀, h₁, h₂, h₃, h₄⟩
  · rintro ⟨h₀, h₁, h₂, h₃, h₄⟩
    refine ⟨fun j => ?_, fun k hk S hkS => ?_⟩
    · fin_cases j
      · exact (hH _).trans h₀
      · exact (hH _).trans h₁
      · exact (hH _).trans h₂
    · have hS : (S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 2} ∨ S = {1, 2}) := by
        revert k S
        decide
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [swCondH_empty hp]
      · simpa using h₀
      · simpa using h₁
      · simpa using h₂
      · rw [sum_pair (by decide)]
        exact h₃
      · rw [sum_pair (by decide)]
        exact h₄

/-- **Page 21-17 of [elgamal2010], corrected: the minimum sum rate for three nodes and
`A = {1, 2}`.** `R_CFO({1, 2}) = H(X₁ | X₂, X₃) + H(X₂ | X₁, X₃) + max {H(X₃ | X₁), H(X₃ | X₂)}`, in
the labels of the notes. The notes have `H(X₁ | X₂) + H(X₂ | X₁)` instead of the first two terms. -/
theorem rCFO_three (hp : IsPMF p) :
    rCFO p {0, 1} = (swCondH p {0} + swCondH p {1} +
      max (H[fun x : ∀ j, α j => x 2 | fun x => x 0 ; p])
        (H[fun x : ∀ j, α j => x 2 | fun x => x 1 ; p])) / log 2 := by
  have hl := log_pos one_lt_two
  set a := swCondH p {0}
  set c := swCondH p {1}
  set m₁ := H[fun x : ∀ j, α j => x 2 | fun x => x 0 ; p]
  set m₂ := H[fun x : ∀ j, α j => x 2 | fun x => x 1 ; p]
  have e₀₂ : swCondH p {0, 2} = m₂ + a := swCondH_zero_two hp
  have e₁₂ : swCondH p {1, 2} = m₁ + c := swCondH_one_two hp
  have hb : swCondH p {2} ≤ m₂ := swCondH_two_le hp
  refine IsLeast.csInf_eq ⟨⟨![a / log 2, c / log 2, max m₁ m₂ / log 2], ?_, ?_⟩, ?_⟩
  · refine (mwRegion_three hp _).2 ⟨le_rfl, le_rfl, ?_, ?_, ?_⟩
    · simp only [Matrix.cons_val]
      exact div_le_div_of_nonneg_right (hb.trans (le_max_right _ _)) hl.le
    · simp only [Matrix.cons_val]
      rw [e₀₂, ← add_div]
      refine div_le_div_of_nonneg_right ?_ hl.le
      linarith [le_max_right m₁ m₂]
    · simp only [Matrix.cons_val]
      rw [e₁₂, ← add_div]
      refine div_le_div_of_nonneg_right ?_ hl.le
      linarith [le_max_left m₁ m₂]
  · simp only [Fin.sum_univ_three, Matrix.cons_val]
    ring
  · rintro _ ⟨R, hR, rfl⟩
    obtain ⟨h₀, h₁, -, h₃, h₄⟩ := (mwRegion_three hp R).1 hR
    simp only [Fin.sum_univ_three]
    rw [e₀₂, add_div] at h₃
    rw [e₁₂, add_div] at h₄
    rw [add_div, add_div]
    rcases le_total m₁ m₂ with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      linarith

end Three

end InfoTheory
