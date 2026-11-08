/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Pi

/-!
# Equivalence of linear inequalities under linear constraints

Let `Q` be a real matrix and `Φ = {h : Q h = 0}`. Two linear inequalities `b ⬝ h ≥ 0` and
`c ⬝ h ≥ 0` are *equivalent under* `Φ` if they hold for the same `h ∈ Φ`. A linear functional
vanishes on `Φ` if and only if it lies in the row space of `Q`. If `b` or `c` lies in the row space,
the inequalities are equivalent if and only if both do; otherwise they are equivalent if and only
if `c = a b + Qᵀ e` for some `a > 0`, and this solution is unique when the rows of `Q` are linearly
independent.

## Main definitions

* `rowSpace Q`: the span of the rows of `Q`.
* `IneqEquivOn Q b c`: `b ⬝ h ≥ 0` and `c ⬝ h ≥ 0` are equivalent for `Q h = 0`.

## Main statements

* `mem_span_rows_iff`: `b` is in the row space of `Q` if and only if `b ⬝ h = 0` whenever
  `Q h = 0`.
* `ineqEquivOn_iff_of_mem_span`: **Theorem 13.4** of [yeung2008].
* `ineqEquivOn_iff_existsUnique`: **Theorem 13.5** of [yeung2008].

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 13.4
-/

open Matrix Finset

@[expose] public section

namespace InfoTheory

variable {k q : Type*}

/-- The row space of a matrix: the span of its rows. -/
def rowSpace (Q : Matrix q k ℝ) : Submodule ℝ (k → ℝ) :=
  Submodule.span ℝ (Set.range fun i => Q i)

/-- `Q` has the vector `v` in its row space if `v = Qᵀ e` for some `e`. -/
lemma mem_span_rows_iff_exists [Fintype q] (Q : Matrix q k ℝ) (v : k → ℝ) :
    v ∈ rowSpace Q ↔ ∃ e, v = Qᵀ *ᵥ e := by
  rw [rowSpace, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, by rw [mulVec_transpose, vecMul_eq_sum]⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, by rw [mulVec_transpose, vecMul_eq_sum]⟩

/-- A linear functional vanishes on the null space of `Q` if and only if it lies in the row space
of `Q`. -/
theorem mem_span_rows_iff [Fintype k] [Finite q] (Q : Matrix q k ℝ) (b : k → ℝ) :
    b ∈ rowSpace Q ↔ ∀ h, Q *ᵥ h = 0 → b ⬝ᵥ h = 0 := by
  classical
  have := Fintype.ofFinite q
  constructor
  · intro hb h hQ
    obtain ⟨e, rfl⟩ := (mem_span_rows_iff_exists Q b).1 hb
    rw [mulVec_transpose, ← dotProduct_mulVec, hQ, dotProduct_zero]
  · intro H
    by_contra hb
    obtain ⟨f, hfb, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
    set h : k → ℝ := fun j => f (Pi.single j 1) with hh
    have hf : ∀ v, f v = v ⬝ᵥ h := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ f v, dotProduct]
      refine sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, hh]
      congr 2
      funext i
      simp [Pi.single_apply, eq_comm]
    have hQh : Q *ᵥ h = 0 := by
      funext i
      have hi : f (Q i) ∈ (rowSpace Q).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩ : Q i ∈ rowSpace Q)
      rw [hmap, Submodule.mem_bot, hf] at hi
      simpa [mulVec] using hi
    exact hfb (by rw [hf, H h hQh])

/-- `b ⬝ h ≥ 0` and `c ⬝ h ≥ 0` are **equivalent under the constraint** `Q h = 0`. -/
def IneqEquivOn [Fintype k] (Q : Matrix q k ℝ) (b c : k → ℝ) : Prop :=
  ∀ h, Q *ᵥ h = 0 → (0 ≤ b ⬝ᵥ h ↔ 0 ≤ c ⬝ᵥ h)

/-- A functional that is nonnegative on the null space of `Q` vanishes there. -/
lemma dotProduct_eq_zero_of_nonneg_on_ker [Fintype k] {Q : Matrix q k ℝ} {c : k → ℝ}
    (hc : ∀ h, Q *ᵥ h = 0 → 0 ≤ c ⬝ᵥ h) {h : k → ℝ} (hQ : Q *ᵥ h = 0) : c ⬝ᵥ h = 0 := by
  have h₁ := hc h hQ
  have h₂ := hc (-h) (by rw [mulVec_neg, hQ, neg_zero])
  rw [dotProduct_neg] at h₂
  linarith

variable [Fintype k]

/-- **Theorem 13.4.** If `b` or `c` is in the row space of `Q`, then `b ⬝ h ≥ 0` and `c ⬝ h ≥ 0`
are equivalent under `Q h = 0` if and only if both `b` and `c` are in the row space of `Q`. -/
theorem ineqEquivOn_iff_of_mem_span [Finite q] {Q : Matrix q k ℝ} {b c : k → ℝ}
    (h : b ∈ rowSpace Q ∨ c ∈ rowSpace Q) :
    IneqEquivOn Q b c ↔
      b ∈ rowSpace Q ∧ c ∈ rowSpace Q := by
  simp only [mem_span_rows_iff] at h ⊢
  constructor
  · intro he
    rcases h with hb | hc
    · exact ⟨hb, fun v hv =>
        dotProduct_eq_zero_of_nonneg_on_ker (fun w hw => (he w hw).1 (hb w hw).ge) hv⟩
    · exact ⟨fun v hv =>
        dotProduct_eq_zero_of_nonneg_on_ker (fun w hw => (he w hw).2 (hc w hw).ge) hv, hc⟩
  · rintro ⟨hb, hc⟩ v hv
    rw [hb v hv, hc v hv]

/-- (13.59): if `c = a b + Qᵀ e` with `a > 0`, then `b ⬝ h ≥ 0` and `c ⬝ h ≥ 0` are equivalent
under `Q h = 0`. -/
theorem ineqEquivOn_of_eq [Fintype q] {Q : Matrix q k ℝ} {b c : k → ℝ} {a : ℝ} (ha : 0 < a)
    (e : q → ℝ) (hc : c = a • b + Qᵀ *ᵥ e) : IneqEquivOn Q b c := by
  intro h hQ
  have : c ⬝ᵥ h = a * (b ⬝ᵥ h) := by
    rw [hc, add_dotProduct, smul_dotProduct, mulVec_transpose, ← dotProduct_mulVec, hQ,
      dotProduct_zero, add_zero, smul_eq_mul]
  rw [this]
  exact ⟨fun hb => mul_nonneg ha.le hb, fun hc' => nonneg_of_mul_nonneg_right hc' ha⟩

/-- (13.55)–(13.59): if neither `b` nor `c` is in the row space of `Q`, then `b ⬝ h ≥ 0` and
`c ⬝ h ≥ 0` are equivalent under `Q h = 0` if and only if `c - a b` is in the row space of `Q` for
some `a > 0`. -/
theorem ineqEquivOn_iff_exists [Finite q] {Q : Matrix q k ℝ} {b c : k → ℝ}
    (hb : b ∉ rowSpace Q) (hc : c ∉ rowSpace Q) :
    IneqEquivOn Q b c ↔ ∃ a : ℝ, 0 < a ∧ c - a • b ∈ rowSpace Q := by
  constructor
  · intro he
    have hb' := hb
    rw [mem_span_rows_iff] at hb' hc
    push Not at hb' hc
    obtain ⟨h₀, hQ₀, hb₀⟩ := hb'
    -- normalize so that `b ⬝ h₁ = 1`
    set h₁ := (b ⬝ᵥ h₀)⁻¹ • h₀ with hh₁
    have hQ₁ : Q *ᵥ h₁ = 0 := by rw [hh₁, mulVec_smul, hQ₀, smul_zero]
    have hb₁ : b ⬝ᵥ h₁ = 1 := by rw [hh₁, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hb₀]
    -- on the null space, `b ⬝ h = 0` implies `c ⬝ h = 0`
    have hker : ∀ h, Q *ᵥ h = 0 → b ⬝ᵥ h = 0 → c ⬝ᵥ h = 0 := fun h hQ hbh => by
      have h₂ := (he h hQ).1 hbh.ge
      have h₃ := (he (-h) (by rw [mulVec_neg, hQ, neg_zero])).1
        (by rw [dotProduct_neg, hbh, neg_zero])
      rw [dotProduct_neg] at h₃
      linarith
    -- so `c = a b` on the null space, with `a = c ⬝ h₁`
    have hprop : ∀ h, Q *ᵥ h = 0 → c ⬝ᵥ h = (c ⬝ᵥ h₁) * (b ⬝ᵥ h) := fun h hQ => by
      have hQ' : Q *ᵥ (h - (b ⬝ᵥ h) • h₁) = 0 := by
        rw [mulVec_sub, mulVec_smul, hQ, hQ₁, smul_zero, sub_zero]
      have := hker _ hQ' (by rw [dotProduct_sub, dotProduct_smul, hb₁, smul_eq_mul, mul_one,
        sub_self])
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at this
      linarith
    refine ⟨c ⬝ᵥ h₁, ?_, ?_⟩
    · rcases ((he h₁ hQ₁).1 (by rw [hb₁]; norm_num)).lt_or_eq with hpos | hzero
      · exact hpos
      · obtain ⟨h, hQ, hch⟩ := hc
        exact absurd (by rw [hprop h hQ, ← hzero, zero_mul]) hch
    · rw [mem_span_rows_iff]
      intro h hQ
      rw [sub_dotProduct, smul_dotProduct, hprop h hQ, smul_eq_mul, sub_self]
  · rintro ⟨a, ha, hmem⟩
    have := Fintype.ofFinite q
    obtain ⟨e, he⟩ := (mem_span_rows_iff_exists Q _).1 hmem
    exact ineqEquivOn_of_eq ha e (by rw [← he]; abel)

/-- **Theorem 13.5.** Let `Q'` have linearly independent rows spanning the row space of `Q`. If
neither `b` nor `c` is in the row space of `Q`, then `b ⬝ h ≥ 0` and `c ⬝ h ≥ 0` are equivalent
under `Q h = 0` if and only if `[Q'ᵀ b] [e; a] = c` (13.61) has a unique solution, with `a > 0`. -/
theorem ineqEquivOn_iff_existsUnique [Finite q] {q' : Type*} [Fintype q'] {Q : Matrix q k ℝ}
    {Q' : Matrix q' k ℝ} (hQ' : rowSpace Q' = rowSpace Q)
    (hind : LinearIndependent ℝ fun i => Q' i) {b c : k → ℝ} (hb : b ∉ rowSpace Q)
    (hc : c ∉ rowSpace Q) :
    IneqEquivOn Q b c ↔ ∃! p : (q' → ℝ) × ℝ, 0 < p.2 ∧ c = Q'ᵀ *ᵥ p.1 + p.2 • b := by
  rw [ineqEquivOn_iff_exists hb hc]
  constructor
  · rintro ⟨a, ha, hmem⟩
    rw [← hQ'] at hmem
    obtain ⟨e, he⟩ := (mem_span_rows_iff_exists Q' _).1 hmem
    refine ⟨(e, a), ⟨ha, by rw [← he]; abel⟩, ?_⟩
    rintro ⟨e', a'⟩ ⟨-, hc'⟩
    have h₁ : (a' - a) • b = Q'ᵀ *ᵥ (e - e') := by
      rw [mulVec_sub, ← he, hc', sub_smul]
      abel
    have haa : a' = a := by
      by_contra hne
      refine hb ?_
      rw [← hQ', mem_span_rows_iff_exists]
      refine ⟨(a' - a)⁻¹ • (e - e'), ?_⟩
      rw [mulVec_smul, ← h₁, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul]
    rw [haa, sub_self, zero_smul, mulVec_transpose, vecMul_eq_sum] at h₁
    have h₂ := Fintype.linearIndependent_iff.1 hind (e - e') h₁.symm
    exact Prod.ext (funext fun i => (sub_eq_zero.1 (h₂ i)).symm) haa
  · rintro ⟨⟨e, a⟩, ⟨ha, hce⟩, -⟩
    refine ⟨a, ha, ?_⟩
    rw [← hQ', mem_span_rows_iff_exists]
    exact ⟨e, by rw [hce]; abel⟩

end InfoTheory
