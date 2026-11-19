/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Linarith

/-!
# Fourier–Motzkin elimination

The set of solutions of a finite system of linear inequalities `A r ≤ b` is a polyhedron. Fourier–
Motzkin elimination computes a system for its projection along a direction `w`. An inequality that
does not involve the eliminated variable is copied, and each upper bound on the variable is compared
with each lower bound. Each new inequality is a nonnegative combination of the old ones, with
coefficients that depend only on `A`, so the elimination also holds for symbolic `b`.

## Main definitions

* `fmIndex c`: the index set of the new system, for the coefficients `c` of the eliminated variable.
* `fmCoef c`: the coefficients of the new inequalities as combinations of the old ones.

## Main statements

* `exists_forall_mul_le_iff`: a variable satisfies the inequalities if and only if each lower bound
  is at most each upper bound.
* `fm_projection`: **the elimination** along a direction.
* `fm_eliminate`, `fm_eliminate_cons`: the elimination of one coordinate.
* `card_fmIndex`, `four_mul_card_pos_mul_card_neg_le`, `four_mul_card_fmIndex_le`,
  `card_fmIndex_worst_case`: the number of inequalities.
* `exists_elimination`: **the elimination of several variables**: a projection of a polyhedron on
  coordinates is a polyhedron.
* `exists_nonneg_comb_of_infeasible`: an infeasible system has a nonnegative combination that gives
  `0 ≤ -1`, a form of Farkas's lemma.

## References

* [G. M. Ziegler, *Lectures on Polytopes*][ziegler1995]
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Appendix D
-/

open Finset Matrix

@[expose] public section

namespace FourierMotzkin

variable {J ι : Type*}

/-- **The elimination criterion.** There is a `t` with `c j * t ≤ u j` for all `j` if and only if
`0 ≤ u j` when `c j = 0`, and each lower bound `u n / c n` (for `c n < 0`) is at most each upper
bound `u p / c p` (for `c p > 0`), which we write without division. -/
theorem exists_forall_mul_le_iff [Finite J] {c u : J → ℝ} :
    (∃ t : ℝ, ∀ j, c j * t ≤ u j) ↔ (∀ j, c j = 0 → 0 ≤ u j) ∧
      ∀ p n, 0 < c p → c n < 0 → 0 ≤ -c n * u p + c p * u n := by
  classical
  have := Fintype.ofFinite J
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun j hj => by simpa [hj] using ht j, fun p n hp hn => ?_⟩
    have h1 := mul_le_mul_of_nonneg_left (ht p) (neg_pos.2 hn).le
    have h2 := mul_le_mul_of_nonneg_left (ht n) hp.le
    nlinarith
  · rintro ⟨h0, h⟩
    set P := univ.filter fun j => 0 < c j with hP
    set N := univ.filter fun j => c j < 0 with hN
    have hup : ∀ {t : ℝ}, (∀ p ∈ P, t ≤ u p / c p) → (∀ n ∈ N, u n / c n ≤ t) →
        ∀ j, c j * t ≤ u j :=
      fun {t} h₁ h₂ j => by
        rcases lt_trichotomy (c j) 0 with hj | hj | hj
        · have := h₂ j (by simp [hN, hj])
          rw [div_le_iff_of_neg hj] at this
          linarith
        · simpa [hj] using h0 j hj
        · have := h₁ j (by simp [hP, hj])
          rw [le_div_iff₀ hj] at this
          linarith
    have hcmp : ∀ p ∈ P, ∀ n ∈ N, u n / c n ≤ u p / c p := fun p hp n hn => by
      have hp' : 0 < c p := by simpa [hP] using hp
      have hn' : c n < 0 := by simpa [hN] using hn
      rw [div_le_iff_of_neg hn', div_mul_eq_mul_div, div_le_iff₀ hp']
      nlinarith [h p n hp' hn']
    by_cases hNe : N.Nonempty
    · obtain ⟨m, hm, hmax⟩ := exists_max_image N (fun n => u n / c n) hNe
      exact ⟨u m / c m, hup (fun p hp => hcmp p hp m hm) hmax⟩
    · rw [not_nonempty_iff_eq_empty] at hNe
      by_cases hPe : P.Nonempty
      · obtain ⟨m, hm, hmin⟩ := exists_min_image P (fun p => u p / c p) hPe
        exact ⟨u m / c m, hup hmin (by simp [hNe])⟩
      · rw [not_nonempty_iff_eq_empty] at hPe
        exact ⟨0, hup (by simp [hPe]) (by simp [hNe])⟩

/-- The new inequalities: those with `c j = 0`, and the pairs of an upper and a lower bound. -/
abbrev fmIndex (c : J → ℝ) : Type _ := {j // c j = 0} ⊕ ({j // 0 < c j} × {j // c j < 0})

open Classical in
/-- The new inequalities as nonnegative combinations of the old ones: an inequality with `c j = 0`
is copied, and an upper bound `p` and a lower bound `n` are combined with weights `-c n` and
`c p`, which cancels the eliminated variable. -/
noncomputable def fmCoef (c : J → ℝ) : Matrix (fmIndex c) J ℝ := fun i j => match i with
  | Sum.inl j₀ => if j = j₀.val then 1 else 0
  | Sum.inr s => (if j = s.1.val then -c s.2.val else 0) + (if j = s.2.val then c s.1.val else 0)

/-- The coefficients of the combinations are nonnegative. -/
lemma fmCoef_nonneg {c : J → ℝ} (i : fmIndex c) (j : J) : 0 ≤ fmCoef c i j := by
  rcases i with j₀ | s
  · simp only [fmCoef]
    split_ifs <;> norm_num
  · simp only [fmCoef]
    have h₁ := s.1.property
    have h₂ := s.2.property
    split_ifs <;> linarith

section Coef

variable [Fintype J] {c : J → ℝ}

/-- The combination of a vector `u`: a copied inequality. -/
lemma fmCoef_mulVec_inl (u : J → ℝ) (j₀ : {j // c j = 0}) :
    (fmCoef c *ᵥ u) (Sum.inl j₀) = u j₀.val := by
  simp only [fmCoef, mulVec, dotProduct]
  rw [sum_eq_single j₀.val (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- The combination of a vector `u`: an upper bound and a lower bound. -/
lemma fmCoef_mulVec_inr (u : J → ℝ) (s : {j // 0 < c j} × {j // c j < 0}) :
    (fmCoef c *ᵥ u) (Sum.inr s) = -c s.2.val * u s.1.val + c s.1.val * u s.2.val := by
  simp only [fmCoef, mulVec, dotProduct, add_mul, sum_add_distrib]
  rw [sum_eq_single s.1.val (fun i _ hi => by simp [hi]) (by simp),
    sum_eq_single s.2.val (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- The eliminated variable cancels. -/
lemma fmCoef_mulVec_self : fmCoef c *ᵥ c = 0 := by
  funext i
  rcases i with j₀ | s
  · rw [fmCoef_mulVec_inl]
    exact j₀.property
  · rw [fmCoef_mulVec_inr]
    simp only [Pi.zero_apply]
    ring

/-- The criterion in terms of the combinations. -/
theorem exists_forall_mul_le_iff_fmCoef {u : J → ℝ} :
    (∃ t : ℝ, ∀ j, c j * t ≤ u j) ↔ ∀ i, 0 ≤ (fmCoef c *ᵥ u) i := by
  rw [exists_forall_mul_le_iff]
  constructor
  · rintro ⟨h0, h⟩ (j₀ | s)
    · rw [fmCoef_mulVec_inl]
      exact h0 _ j₀.property
    · rw [fmCoef_mulVec_inr]
      exact h _ _ s.1.property s.2.property
  · intro h
    refine ⟨fun j hj => ?_, fun p n hp hn => ?_⟩
    · simpa [fmCoef_mulVec_inl] using h (Sum.inl ⟨j, hj⟩)
    · simpa [fmCoef_mulVec_inr] using h (Sum.inr (⟨p, hp⟩, ⟨n, hn⟩))

/-- `|{c = 0}| + |{c > 0}| |{c < 0}|` inequalities. -/
lemma card_fmIndex [DecidablePred fun j => c j = 0] [DecidablePred fun j => 0 < c j]
    [DecidablePred fun j => c j < 0] :
    Fintype.card (fmIndex c) = Fintype.card {j // c j = 0} +
      Fintype.card {j // 0 < c j} * Fintype.card {j // c j < 0} := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- The number of values split between the three classes. -/
lemma card_zero_add_pos_add_neg [DecidablePred fun j => c j = 0] [DecidablePred fun j => 0 < c j]
    [DecidablePred fun j => c j < 0] :
    Fintype.card {j // c j = 0} + Fintype.card {j // 0 < c j} + Fintype.card {j // c j < 0} =
      Fintype.card J := by
  have h : ∀ j, (if c j = 0 then 1 else 0) + (if 0 < c j then 1 else 0) +
      (if c j < 0 then 1 else 0) = 1 := fun j => by
    rcases lt_trichotomy (c j) 0 with h | h | h
    · simp [h, h.ne, h.le.not_gt]
    · simp [h]
    · simp [h, h.ne', h.le.not_gt]
  simp only [Fintype.card_subtype, card_filter, ← sum_add_distrib, h]
  simp [card_univ]

/-- **Page D-4 of [elgamal2010].** At most `k² / 4` inequalities are generated from `k`. -/
theorem four_mul_card_pos_mul_card_neg_le [DecidablePred fun j => 0 < c j]
    [DecidablePred fun j => c j < 0] :
    4 * (Fintype.card {j // 0 < c j} * Fintype.card {j // c j < 0}) ≤ Fintype.card J ^ 2 := by
  classical
  rw [← card_zero_add_pos_add_neg (c := c)]
  generalize Fintype.card {j // c j = 0} = z
  generalize Fintype.card {j // 0 < c j} = a
  generalize Fintype.card {j // c j < 0} = d
  zify
  have ha : (0 : ℤ) ≤ a := by positivity
  have hd : (0 : ℤ) ≤ d := by positivity
  have hz : (0 : ℤ) ≤ z := by positivity
  nlinarith [sq_nonneg ((a : ℤ) - d), mul_nonneg hz ha, mul_nonneg hz hd, mul_nonneg hz hz]

/-- From `k ≥ 4` inequalities, the new system has at most `k² / 4` inequalities, including the ones
that are copied. -/
theorem four_mul_card_fmIndex_le [DecidablePred fun j => c j = 0]
    [DecidablePred fun j => 0 < c j] [DecidablePred fun j => c j < 0] (hk : 4 ≤ Fintype.card J) :
    4 * Fintype.card (fmIndex c) ≤ Fintype.card J ^ 2 := by
  rw [card_fmIndex]
  rw [← card_zero_add_pos_add_neg (c := c)] at hk ⊢
  generalize Fintype.card {j // c j = 0} = z at hk ⊢
  generalize Fintype.card {j // 0 < c j} = a at hk ⊢
  generalize Fintype.card {j // c j < 0} = d at hk ⊢
  zify at hk ⊢
  have ha : (0 : ℤ) ≤ a := by positivity
  have hd : (0 : ℤ) ≤ d := by positivity
  have hz : (0 : ℤ) ≤ z := by positivity
  have h4 : (0 : ℤ) ≤ z + 2 * (a + d) - 4 := by linarith
  nlinarith [sq_nonneg ((a : ℤ) - d), mul_nonneg hz h4]

end Coef

/-- **Page D-4 of [elgamal2010].** The bound is attained: `m` upper bounds and `m` lower bounds,
which are `k = 2 m` inequalities, give `m² = k² / 4` new ones. -/
theorem card_fmIndex_worst_case (m : ℕ) :
    Fintype.card (fmIndex (Sum.elim (fun _ : Fin m => (1 : ℝ)) fun _ : Fin m => (-1 : ℝ))) =
      m * m := by
  classical
  rw [card_fmIndex]
  set c : Fin m ⊕ Fin m → ℝ := Sum.elim (fun _ => 1) fun _ => -1 with hc
  have h₀ : Fintype.card {j // c j = 0} = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨j, hj⟩ => ?_⟩
    rcases j with j | j <;> norm_num [hc] at hj
  have h₁ : Fintype.card {j // 0 < c j} = m := by
    rw [Fintype.card_of_subtype (univ.map Function.Embedding.inl)]
    · simp
    · rintro (j | j) <;> simp [hc]
  have h₂ : Fintype.card {j // c j < 0} = m := by
    rw [Fintype.card_of_subtype (univ.map Function.Embedding.inr)]
    · simp
    · rintro (j | j) <;> simp [hc]
  rw [h₀, h₁, h₂, zero_add]

section Column

variable [Fintype J]

/-- The column of the eliminated coordinate is zero. -/
theorem fmCoef_mul_apply_self (A : Matrix J ι ℝ) (v : ι) (i : fmIndex fun j => A j v) :
    (fmCoef (fun j => A j v) * A) i v = 0 := by
  have h := congrFun (fmCoef_mulVec_self (c := fun j => A j v)) i
  rw [Matrix.mul_apply]
  exact h

/-- A column that is zero stays zero. -/
lemma mul_apply_eq_zero_of_column {κ : Type*} (C : Matrix κ J ℝ) {A : Matrix J ι ℝ} {v : ι}
    (h : ∀ j, A j v = 0) (i : κ) : (C * A) i v = 0 := by
  rw [Matrix.mul_apply]
  simp [h]

end Column

section Elimination

variable [Fintype J] [Fintype ι]

/-- **Fourier–Motzkin elimination along a direction `w`.** With `c = A w`, the system
`(C A) r ≤ C b` for the nonnegative combinations `C = fmCoef c` describes the projection of the
polyhedron `{r | A r ≤ b}` along `w`. -/
theorem fm_projection (A : Matrix J ι ℝ) (b : J → ℝ) (w r : ι → ℝ) :
    (fmCoef (A *ᵥ w) * A) *ᵥ r ≤ fmCoef (A *ᵥ w) *ᵥ b ↔ ∃ t : ℝ, A *ᵥ (r + t • w) ≤ b := by
  have e₁ : ∀ t : ℝ, A *ᵥ (r + t • w) ≤ b ↔ ∀ j, (A *ᵥ w) j * t ≤ (b - A *ᵥ r) j := fun t => by
    rw [mulVec_add, mulVec_smul]
    refine forall_congr' fun j => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    constructor <;> intro h <;> linarith
  simp only [e₁]
  rw [exists_forall_mul_le_iff_fmCoef, ← mulVec_mulVec, Pi.le_def]
  refine forall_congr' fun i => ?_
  rw [mulVec_sub, Pi.sub_apply, sub_nonneg]

/-- The direction `w` is eliminated. -/
theorem fmCoef_mul_mulVec (A : Matrix J ι ℝ) (w : ι → ℝ) : (fmCoef (A *ᵥ w) * A) *ᵥ w = 0 := by
  rw [← mulVec_mulVec, fmCoef_mulVec_self]

variable [DecidableEq ι]

/-- **Fourier–Motzkin elimination of a coordinate `v`**, with `c` the column of `v`. -/
theorem fm_eliminate (A : Matrix J ι ℝ) (b : J → ℝ) (v : ι) (r : ι → ℝ) :
    (fmCoef (fun j => A j v) * A) *ᵥ r ≤ fmCoef (fun j => A j v) *ᵥ b ↔
      ∃ t : ℝ, A *ᵥ Function.update r v t ≤ b := by
  have hc : A *ᵥ Pi.single v 1 = fun j => A j v := by
    funext j
    simp [mulVec_single]
  have h := fm_projection A b (Pi.single v 1) r
  rw [hc] at h
  rw [h]
  have e : ∀ t : ℝ, r + t • Pi.single v (1 : ℝ) = Function.update r v (r v + t) := fun t => by
    funext i
    by_cases hi : i = v
    · subst hi
      simp
    · simp [hi]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨r v + t, by rwa [← e]⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - r v, ?_⟩
    rw [e, add_sub_cancel]
    exact ht

end Elimination

section First

variable [Fintype J] {d : ℕ}

/-- The system in `(r₂, …, r_d)`: the combinations with the first column removed. -/
noncomputable def fmTail (A : Matrix J (Fin (d + 1)) ℝ) :
    Matrix (fmIndex fun j => A j 0) (Fin d) ℝ :=
  (fmCoef (fun j => A j 0) * A).submatrix id Fin.succ

/-- **The elimination of `r₁` on pages D-1 to D-3 of [elgamal2010].** The projection `R' ⊆ ℝ^{d-1}`
of the polyhedron `R ⊆ ℝ^d` is the polyhedron of the new system. So if `(r₁, r₂, …, r_d) ∈ R`, then
`(r₂, …, r_d) ∈ R'`, and if `(r₂, …, r_d) ∈ R'`, then there is an `r₁` with
`(r₁, r₂, …, r_d) ∈ R`. -/
theorem fm_eliminate_cons (A : Matrix J (Fin (d + 1)) ℝ) (b : J → ℝ) (r : Fin d → ℝ) :
    fmTail A *ᵥ r ≤ fmCoef (fun j => A j 0) *ᵥ b ↔
      ∃ t : ℝ, A *ᵥ (Fin.cons t r : Fin (d + 1) → ℝ) ≤ b := by
  have h := fm_eliminate A b 0 (Fin.cons 0 r : Fin (d + 1) → ℝ)
  have e : (fmCoef (fun j => A j 0) * A) *ᵥ (Fin.cons 0 r : Fin (d + 1) → ℝ) = fmTail A *ᵥ r := by
    funext i
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero,
      zero_add]
    rfl
  rw [e] at h
  rw [h]
  simp only [Fin.update_cons_zero]

end First

section Successive

variable [Fintype J] [Fintype ι]

/-- **The elimination of several variables, page D-4 of [elgamal2010].** For a set `S` of
coordinates there are nonnegative combinations `C` of the inequalities, depending only on `A`, such
that the system `(C A) r ≤ C b` does not involve `S`, and describes the projection of
`{r | A r ≤ b}`, for every `b`. So a projection of a polyhedron is a polyhedron. -/
theorem exists_elimination (A : Matrix J ι ℝ) (S : Finset ι) :
    ∃ (m : ℕ) (C : Matrix (Fin m) J ℝ), (∀ i j, 0 ≤ C i j) ∧ (∀ v ∈ S, ∀ i, (C * A) i v = 0) ∧
      ∀ (b : J → ℝ) (r : ι → ℝ), (C * A) *ᵥ r ≤ C *ᵥ b ↔
        ∃ r' : ι → ℝ, (∀ v, v ∉ S → r' v = r v) ∧ A *ᵥ r' ≤ b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    set e := Fintype.equivFin J
    set C₀ : Matrix (Fin (Fintype.card J)) J ℝ := fun i j => if j = e.symm i then 1 else 0 with hC₀
    have hv : ∀ u : J → ℝ, C₀ *ᵥ u = u ∘ e.symm := fun u => by
      funext i
      simp only [hC₀, mulVec, dotProduct]
      rw [sum_eq_single (e.symm i) (fun j _ hj => by simp [hj]) (by simp)]
      simp
    refine ⟨Fintype.card J, C₀, fun i j => ?_, by simp, fun b r => ?_⟩
    · simp only [hC₀]
      split_ifs <;> norm_num
    · rw [← mulVec_mulVec, hv, hv]
      constructor
      · intro h
        refine ⟨r, fun _ _ => rfl, fun j => ?_⟩
        simpa using h (e j)
      · rintro ⟨r', h, hr'⟩ i
        obtain rfl : r' = r := funext fun v => h v (by simp)
        exact hr' _
  | insert v S hv ih =>
    obtain ⟨m, C, hC, hz, hS⟩ := ih
    set c : Fin m → ℝ := fun i => (C * A) i v with hc
    set e := Fintype.equivFin (fmIndex c)
    set D : Matrix (Fin (Fintype.card (fmIndex c))) (Fin m) ℝ :=
      (fmCoef c).submatrix e.symm id with hD
    have hDv : ∀ u : Fin m → ℝ, D *ᵥ u = (fmCoef c *ᵥ u) ∘ e.symm := fun _ => rfl
    refine ⟨_, D * C, fun i j => ?_, fun u hu i => ?_, fun b r => ?_⟩
    · rw [Matrix.mul_apply]
      exact sum_nonneg fun l _ => mul_nonneg (fmCoef_nonneg _ _) (hC _ _)
    · rw [Matrix.mul_assoc]
      rcases mem_insert.1 hu with rfl | hu
      · exact fmCoef_mul_apply_self (C * A) u (e.symm i)
      · exact mul_apply_eq_zero_of_column D (hz u hu) i
    · have hle : ∀ {x y : fmIndex c → ℝ}, x ∘ e.symm ≤ y ∘ e.symm ↔ x ≤ y := fun {x y} =>
        ⟨fun h i => by simpa using h (e i), fun h i => h _⟩
      have e₁ : ((D * C) * A) *ᵥ r = ((fmCoef c * (C * A)) *ᵥ r) ∘ e.symm := by
        rw [Matrix.mul_assoc, ← mulVec_mulVec, hDv, mulVec_mulVec]
      have e₂ : (D * C) *ᵥ b = (fmCoef c *ᵥ (C *ᵥ b)) ∘ e.symm := by
        rw [← mulVec_mulVec, hDv]
      rw [e₁, e₂, hle, fm_eliminate (C * A) (C *ᵥ b) v r]
      constructor
      · rintro ⟨t, ht⟩
        obtain ⟨r', h, hr'⟩ := (hS b _).1 ht
        refine ⟨r', fun u hu => ?_, hr'⟩
        rw [mem_insert, not_or] at hu
        rw [h u hu.2, Function.update_of_ne hu.1]
      · rintro ⟨r', h, hr'⟩
        refine ⟨r' v, (hS b _).2 ⟨r', fun u hu => ?_, hr'⟩⟩
        by_cases huv : u = v
        · subst huv
          simp
        · rw [Function.update_of_ne huv]
          exact h u (by simp [huv, hu])

/-- With all the variables eliminated, feasibility is a condition on `b`. -/
theorem exists_feasibility_certificate (A : Matrix J ι ℝ) :
    ∃ (m : ℕ) (C : Matrix (Fin m) J ℝ), (∀ i j, 0 ≤ C i j) ∧ C * A = 0 ∧
      ∀ b : J → ℝ, (∃ r, A *ᵥ r ≤ b) ↔ 0 ≤ C *ᵥ b := by
  obtain ⟨m, C, hC, hz, h⟩ := exists_elimination A (univ : Finset ι)
  have hz' : C * A = 0 := by
    ext i v
    exact hz v (mem_univ v) i
  refine ⟨m, C, hC, hz', fun b => ?_⟩
  have := h b 0
  rw [hz', zero_mulVec] at this
  rw [this]
  simp

/-- **Farkas's lemma.** If `A r ≤ b` has no solution, then a nonnegative combination of the
inequalities reads `0 ≤ s` with `s < 0`. -/
theorem exists_nonneg_comb_of_infeasible {A : Matrix J ι ℝ} {b : J → ℝ}
    (h : ¬ ∃ r, A *ᵥ r ≤ b) : ∃ y : J → ℝ, 0 ≤ y ∧ y ᵥ* A = 0 ∧ y ⬝ᵥ b < 0 := by
  obtain ⟨m, C, hC, hz, hb⟩ := exists_feasibility_certificate A
  rw [hb, Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine ⟨C i, fun j => hC i j, ?_, hi⟩
  funext v
  have := congrFun (congrFun hz i) v
  rw [Matrix.mul_apply] at this
  exact this

end Successive

end FourierMotzkin
