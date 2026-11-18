/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.FourierMotzkin
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# El Gamal & Kim, Appendix D: Fourier–Motzkin Elimination

This file indexes the formalization of Appendix D of [elgamal2010]: the elimination of a variable
from a finite system of linear inequalities, and the elimination of the two rates `R₀₁` and `R₀₂`
in the Han–Kobayashi inner bound. Mathlib has no such theorem: `linarith` has a Fourier–Motzkin
oracle, with no statement about polyhedra.

## Conventions

* **Polyhedra.** A polyhedron is `{r | A *ᵥ r ≤ b}` for a matrix `A : Matrix J ι ℝ` with finite `J`
  and `ι`, and `≤` is pointwise.
* **New systems.** The new inequalities are combinations of the old ones: the matrix is `C * A` and
  the right side is `C *ᵥ b`, for the matrix `C = fmCoef c` with nonnegative entries, where `c` is
  the column of the eliminated variable. So `C` depends only on `A`, which covers the symbolic
  inequalities on page D-4: the theorems hold for every `b`.
* **Symbolic constants.** In the Han–Kobayashi example, `I₁, …, I₈` are arbitrary real numbers.

## Index

Module names are relative to `InfoTheoryLib`. The general results are in `ForMathlib.FourierMotzkin`
and in namespace `FourierMotzkin`; "here" means this file.

### The elimination (pages D-1 and D-3)
* The criterion, that each lower bound is at most each upper bound: `exists_forall_mul_le_iff`,
  `exists_forall_mul_le_iff_fmCoef`.
* The three categories of inequalities and the new system: `fmIndex`, `fmCoef`,
  `fmCoef_mulVec_inl`, `fmCoef_mulVec_inr`, `fmCoef_nonneg`.
* **The projection of `R` on the hyperplane `{r₁ = 0}`:** `fmTail`, `fm_eliminate_cons`, with both
  properties 1 and 2 of page D-1 in one equivalence.
* The elimination of any coordinate: `fm_eliminate`, `fmCoef_mul_apply_self`.

### The example (pages D-2 and D-3)
* `max {1, r₂, 2 - r₂} ≤ min {(r₂ + 3) / 2, 15 - 4 r₂}`: here `example_criterion`.
* `R' = {r₂ : 1/2 ≤ r₂ ≤ 3}`: here `example_projection`.

### The remarks (page D-4)
* At most `k² / 4` generated inequalities, and the bound is attained: `card_fmIndex`,
  `four_mul_card_pos_mul_card_neg_le`, `card_fmIndex_worst_case`, and `four_mul_card_fmIndex_le`
  with the copied inequalities.
* The projection along any direction, which replaces the affine change of variables:
  `fm_projection`, `fmCoef_mul_mulVec`.
* **The elimination of several variables, with symbolic constants:** `exists_elimination`.
* With all the variables eliminated, feasibility is a condition on `b`:
  `exists_feasibility_certificate`, and Farkas's lemma `exists_nonneg_comb_of_infeasible`, which
  Mathlib has for cones. These are not in the notes.

### The Han–Kobayashi inner bound (pages D-5 to D-7; here)
* The system: `hkSystem`.
* **Step 1, the elimination of `R₀₁`:** `hkStep1`, `hk_step1`.
* That none of the 8 inequalities is redundant: `hkStep1Row`, `hkStep1_iff_rows`,
  `hkStep1_irredundant`.
* **Step 2, the elimination of `R₀₂`:** `hkStep2`, `hk_step2`.
* The last inequality is redundant, which leaves 7: `hkRegion`, `hkStep2_iff_hkRegion`.
* **The elimination of both:** `hk_elimination`.
* That none of the 7 inequalities is redundant, which the notes do not claim: `hkRegionRow`,
  `hkRegion_iff_rows`, `hkRegion_irredundant`.

## Differences from the notes

* **Projection.** We keep the coordinate system for several variables: the new system is on the same
  coordinates, with zero columns at the eliminated variables, and the values at these coordinates do
  not matter. For the first variable, `fm_eliminate_cons` is on `ℝ^{d-1}`, as in the notes.
* **Affine transformations.** The remark on page D-4 is replaced by the projection along a
  direction, `fm_projection`.
* **Number of inequalities.** The bound `k² / 4` holds for all `k` for the generated inequalities.
  With the copied ones it needs `k ≥ 4`: 3 inequalities without `r₁` are copied into 3.
* **Example.** The two examples are proved directly, by comparing bounds as in the notes, and not by
  writing out a matrix for `fm_eliminate_cons`.

## Not formalized

* The remark on software on page D-4 (PORTA). `fmCoef` is a definition over the reals, with no
  algorithm that removes redundant inequalities.
* The use of relations among the constants `b₁, …, b_k` to remove inequalities on page D-4 and the
  cited example.
* The Han–Kobayashi inner bound itself, Theorem 4 of Lecture 6. Page 6-27 eliminates under the
  further constraints `R_j0 = R_j - R_jj` and `0 ≤ R_jj ≤ R_j`, which the example of this appendix
  does not include, so `hk_elimination` is the system of the example and not a statement about the
  region of that theorem.

## Issues in the notes

* **Page D-6.** "None of these 8 inequalities is redundant" holds for symbolic `I₁, …, I₈`
  (`hkStep1_irredundant`), but not for all values: `R₁ + R₂ ≤ I₁ + I₈` and `R₁ + R₂ ≤ I₃ + I₇` have
  the same left side, so one of the two is implied by the other as soon as the constants are known.
* **Page D-3.** "redudant" is a typo, and an upper or lower bound is an affine function, not "an
  affine equation".
* **Page D-7.** "`R20`" should be `R02`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  D
* [G. M. Ziegler, *Lectures on Polytopes*][ziegler1995]
-/

open Set

@[expose] public noncomputable section

namespace InfoTheory

namespace ElGamalKim

/-! ### The example of pages D-2 and D-3 -/

/-- **Page D-2 of [elgamal2010].** `r₂ ∈ R'` if and only if `-2 r₂ ≤ -1`, and every lower bound on
`r₁` is at most every upper bound on `r₁`. -/
theorem example_criterion (r₂ : ℝ) :
    (∃ r₁ : ℝ, -r₁ ≤ -1 ∧ -2 * r₂ ≤ -1 ∧ -r₁ + r₂ ≤ 0 ∧ -r₁ - r₂ ≤ -2 ∧ r₁ + 4 * r₂ ≤ 15 ∧
      2 * r₁ - r₂ ≤ 3) ↔
      -2 * r₂ ≤ -1 ∧ max 1 (max r₂ (2 - r₂)) ≤ min ((r₂ + 3) / 2) (15 - 4 * r₂) := by
  constructor
  · rintro ⟨r₁, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨h₂, le_min (max_le ?_ (max_le ?_ ?_)) (max_le ?_ (max_le ?_ ?_))⟩ <;> linarith
  · rintro ⟨h₂, h⟩
    have hl := le_min_iff.1 h
    obtain ⟨hu₁, hu₂⟩ := hl
    refine ⟨max 1 (max r₂ (2 - r₂)), ?_, h₂, ?_, ?_, ?_, ?_⟩
    · have := le_max_left 1 (max r₂ (2 - r₂))
      linarith
    · have := (le_max_left r₂ (2 - r₂)).trans (le_max_right 1 _)
      linarith
    · have := (le_max_right r₂ (2 - r₂)).trans (le_max_right 1 _)
      linarith
    · linarith
    · linarith

/-- **Page D-3 of [elgamal2010].** `R' = {r₂ : 1/2 ≤ r₂ ≤ 3}`. -/
theorem example_projection :
    {r₂ : ℝ | ∃ r₁ : ℝ, -r₁ ≤ -1 ∧ -2 * r₂ ≤ -1 ∧ -r₁ + r₂ ≤ 0 ∧ -r₁ - r₂ ≤ -2 ∧
      r₁ + 4 * r₂ ≤ 15 ∧ 2 * r₁ - r₂ ≤ 3} = Icc (1 / 2) 3 := by
  ext r₂
  rw [mem_ofPred_eq, example_criterion, mem_Icc]
  constructor
  · rintro ⟨h₂, h⟩
    obtain ⟨hu₁, hu₂⟩ := le_min_iff.1 h
    have := (le_max_left r₂ (2 - r₂)).trans (le_max_right 1 _)
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    refine ⟨by linarith, le_min (max_le ?_ (max_le ?_ ?_)) (max_le ?_ (max_le ?_ ?_))⟩ <;> linarith

/-! ### The Han–Kobayashi inner bound -/

section HanKobayashi

variable (I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ : ℝ)

/-- **Page D-5 of [elgamal2010].** The system in `(R₀₁, R₀₂, R₁, R₂)`. -/
def hkSystem (R₀₁ R₀₂ R₁ R₂ : ℝ) : Prop :=
  R₁ - R₀₁ ≤ I₁ ∧ R₁ ≤ I₂ ∧ R₁ - R₀₁ + R₀₂ ≤ I₃ ∧ R₁ + R₀₂ ≤ I₄ ∧
    R₂ - R₀₂ ≤ I₅ ∧ R₂ ≤ I₆ ∧ R₂ - R₀₂ + R₀₁ ≤ I₇ ∧ R₂ + R₀₁ ≤ I₈

/-- **Page D-6 of [elgamal2010].** The system in `(R₀₂, R₁, R₂)` after step 1. -/
def hkStep1 (R₀₂ R₁ R₂ : ℝ) : Prop :=
  R₁ ≤ I₂ ∧ R₁ + R₀₂ ≤ I₄ ∧ R₂ - R₀₂ ≤ I₅ ∧ R₂ ≤ I₆ ∧ R₁ + R₂ - R₀₂ ≤ I₁ + I₇ ∧
    R₁ + R₂ ≤ I₁ + I₈ ∧ R₁ + R₂ ≤ I₃ + I₇ ∧ R₁ + R₂ + R₀₂ ≤ I₃ + I₈

/-- **Page D-7 of [elgamal2010].** The system in `(R₁, R₂)` after step 2. -/
def hkStep2 (R₁ R₂ : ℝ) : Prop :=
  R₁ ≤ I₂ ∧ R₂ ≤ I₆ ∧ R₁ + R₂ ≤ I₁ + I₈ ∧ R₁ + R₂ ≤ I₃ + I₇ ∧ R₁ + R₂ ≤ I₄ + I₅ ∧
    2 * R₁ + R₂ ≤ I₁ + I₄ + I₇ ∧ R₁ + 2 * R₂ ≤ I₃ + I₅ + I₈ ∧ 2 * R₁ + 2 * R₂ ≤ I₁ + I₃ + I₇ + I₈

/-- **Page D-7 of [elgamal2010].** The 7 inequalities on `(R₁, R₂)`. -/
def hkRegion (R₁ R₂ : ℝ) : Prop :=
  R₁ ≤ I₂ ∧ R₂ ≤ I₆ ∧ R₁ + R₂ ≤ I₁ + I₈ ∧ R₁ + R₂ ≤ I₃ + I₇ ∧ R₁ + R₂ ≤ I₄ + I₅ ∧
    2 * R₁ + R₂ ≤ I₁ + I₄ + I₇ ∧ R₁ + 2 * R₂ ≤ I₃ + I₅ + I₈

variable {I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈}

/-- **Step 1 on pages D-5 and D-6 of [elgamal2010]:** the elimination of `R₀₁`. -/
theorem hk_step1 (R₀₂ R₁ R₂ : ℝ) :
    (∃ R₀₁, hkSystem I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₁ R₀₂ R₁ R₂) ↔
      hkStep1 I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₂ R₁ R₂ := by
  constructor
  · rintro ⟨R₀₁, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    refine ⟨h₂, h₄, h₅, h₆, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h₂, h₄, h₅, h₆, h₁₇, h₁₈, h₃₇, h₃₈⟩
    have hu₁ := min_le_left (I₇ - R₂ + R₀₂) (I₈ - R₂)
    have hu₂ := min_le_right (I₇ - R₂ + R₀₂) (I₈ - R₂)
    have hl₁ : R₁ - I₁ ≤ min (I₇ - R₂ + R₀₂) (I₈ - R₂) := le_min (by linarith) (by linarith)
    have hl₂ : R₁ + R₀₂ - I₃ ≤ min (I₇ - R₂ + R₀₂) (I₈ - R₂) := le_min (by linarith) (by linarith)
    exact ⟨min (I₇ - R₂ + R₀₂) (I₈ - R₂), by linarith, h₂, by linarith, h₄, h₅, h₆, by linarith,
      by linarith⟩

/-- **Step 2 on page D-7 of [elgamal2010]:** the elimination of `R₀₂`. -/
theorem hk_step2 (R₁ R₂ : ℝ) :
    (∃ R₀₂, hkStep1 I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₂ R₁ R₂) ↔ hkStep2 I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ := by
  constructor
  · rintro ⟨R₀₂, h₂, h₄, h₅, h₆, h₁₇, h₁₈, h₃₇, h₃₈⟩
    refine ⟨h₂, h₆, h₁₈, h₃₇, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h₂, h₆, h₁₈, h₃₇, h₄₅, h₁₄₇, h₃₅₈, h₁₃₇₈⟩
    have hu₁ := min_le_left (I₄ - R₁) (I₃ + I₈ - R₁ - R₂)
    have hu₂ := min_le_right (I₄ - R₁) (I₃ + I₈ - R₁ - R₂)
    have hl₁ : R₂ - I₅ ≤ min (I₄ - R₁) (I₃ + I₈ - R₁ - R₂) := le_min (by linarith) (by linarith)
    have hl₂ : R₁ + R₂ - I₁ - I₇ ≤ min (I₄ - R₁) (I₃ + I₈ - R₁ - R₂) :=
      le_min (by linarith) (by linarith)
    exact ⟨min (I₄ - R₁) (I₃ + I₈ - R₁ - R₂), h₂, by linarith, by linarith, h₆, by linarith, h₁₈,
      h₃₇, by linarith⟩

/-- **Page D-7 of [elgamal2010].** The last inequality is implied by the third and the fourth. -/
theorem hkStep2_iff_hkRegion (R₁ R₂ : ℝ) :
    hkStep2 I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ ↔ hkRegion I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, -⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, by linarith⟩

/-- **The example on pages D-5 to D-7 of [elgamal2010].** Eliminating `R₀₁` and `R₀₂` leaves the 7
inequalities on `(R₁, R₂)`. -/
theorem hk_elimination (R₁ R₂ : ℝ) :
    (∃ R₀₁ R₀₂, hkSystem I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₁ R₀₂ R₁ R₂) ↔
      hkRegion I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ := by
  rw [← hkStep2_iff_hkRegion, ← hk_step2]
  constructor
  · rintro ⟨R₀₁, R₀₂, h⟩
    exact ⟨R₀₂, (hk_step1 R₀₂ R₁ R₂).1 ⟨R₀₁, h⟩⟩
  · rintro ⟨R₀₂, h⟩
    obtain ⟨R₀₁, h'⟩ := (hk_step1 R₀₂ R₁ R₂).2 h
    exact ⟨R₀₁, R₀₂, h'⟩

variable (I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈)

/-- The 8 inequalities after step 1, as a family. -/
def hkStep1Row (R₀₂ R₁ R₂ : ℝ) : Fin 8 → Prop :=
  ![R₁ ≤ I₂, R₁ + R₀₂ ≤ I₄, R₂ - R₀₂ ≤ I₅, R₂ ≤ I₆, R₁ + R₂ - R₀₂ ≤ I₁ + I₇, R₁ + R₂ ≤ I₁ + I₈,
    R₁ + R₂ ≤ I₃ + I₇, R₁ + R₂ + R₀₂ ≤ I₃ + I₈]

/-- The 7 inequalities on `(R₁, R₂)`, as a family. -/
def hkRegionRow (R₁ R₂ : ℝ) : Fin 7 → Prop :=
  ![R₁ ≤ I₂, R₂ ≤ I₆, R₁ + R₂ ≤ I₁ + I₈, R₁ + R₂ ≤ I₃ + I₇, R₁ + R₂ ≤ I₄ + I₅,
    2 * R₁ + R₂ ≤ I₁ + I₄ + I₇, R₁ + 2 * R₂ ≤ I₃ + I₅ + I₈]

variable {I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈}

lemma hkStep1_iff_rows (R₀₂ R₁ R₂ : ℝ) :
    hkStep1 I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₂ R₁ R₂ ↔
      ∀ k, hkStep1Row I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₂ R₁ R₂ k := by
  simp [hkStep1, hkStep1Row, Fin.forall_fin_succ]

lemma hkRegion_iff_rows (R₁ R₂ : ℝ) :
    hkRegion I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ ↔
      ∀ k, hkRegionRow I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ k := by
  simp [hkRegion, hkRegionRow, Fin.forall_fin_succ]

/-- **Page D-6 of [elgamal2010].** None of the 8 inequalities is redundant, for symbolic constants:
for each of them there are constants and a point that violate this inequality and no other. -/
theorem hkStep1_irredundant (k : Fin 8) :
    ∃ I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₂ R₁ R₂ : ℝ, ¬ hkStep1Row I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₂ R₁ R₂ k ∧
      ∀ l, l ≠ k → hkStep1Row I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₀₂ R₁ R₂ l := by
  fin_cases k
  · refine ⟨1, -1, 1, 1, 1, 1, 1, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]
  · refine ⟨1, 1, 1, -1, 1, 1, 1, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]
  · refine ⟨1, 1, 1, 1, -1, 1, 1, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]
  · refine ⟨1, 1, 1, 1, 1, -1, 1, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]
  · refine ⟨-1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]
  · refine ⟨-1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]
  · refine ⟨1, 1, -1, 1, 1, 1, 0, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]
  · refine ⟨1, 1, -1, 1, 1, 1, 1, 0, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkStep1Row, Fin.forall_fin_succ]

/-- None of the 7 inequalities on `(R₁, R₂)` is redundant, for symbolic constants. -/
theorem hkRegion_irredundant (k : Fin 7) :
    ∃ I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ : ℝ, ¬ hkRegionRow I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ k ∧
      ∀ l, l ≠ k → hkRegionRow I₁ I₂ I₃ I₄ I₅ I₆ I₇ I₈ R₁ R₂ l := by
  fin_cases k
  · refine ⟨1, -1, 1, 1, 1, 1, 1, 1, 0, 0, ?_, ?_⟩ <;> norm_num [hkRegionRow, Fin.forall_fin_succ]
  · refine ⟨1, 1, 1, 1, 1, -1, 1, 1, 0, 0, ?_, ?_⟩ <;> norm_num [hkRegionRow, Fin.forall_fin_succ]
  · refine ⟨-1, 1, 1, 1, 1, 1, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkRegionRow, Fin.forall_fin_succ]
  · refine ⟨1, 1, -1, 1, 1, 1, 0, 1, 0, 0, ?_, ?_⟩ <;> norm_num [hkRegionRow, Fin.forall_fin_succ]
  · refine ⟨1, 1, 1, -1, 0, 1, 1, 1, 0, 0, ?_, ?_⟩ <;> norm_num [hkRegionRow, Fin.forall_fin_succ]
  · refine ⟨0, 1, 1, -1, 1, 1, 0, 1, 0, 0, ?_, ?_⟩ <;> norm_num [hkRegionRow, Fin.forall_fin_succ]
  · refine ⟨1, 1, 0, 1, -1, 1, 1, 0, 0, 0, ?_, ?_⟩ <;> norm_num [hkRegionRow, Fin.forall_fin_succ]

end HanKobayashi

end ElGamalKim

end InfoTheory
