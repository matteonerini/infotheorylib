/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.SupportingHyperplane
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Convex optimization: Lagrangian duality, Slater's condition and the KKT conditions

An optimization problem `minimize g₀(x) subject to gⱼ(x) ≤ 0, A x = b` on a domain `C`, its
Lagrangian `L(x, λ, ν) = g₀(x) + ∑ⱼ λⱼ gⱼ(x) + νᵀ (A x - b)`, its dual function
`φ(λ, ν) = inf_x L(x, λ, ν)` and its dual problem.

The optimal values are extended reals: the primal value is `⊤` for an infeasible problem, and `φ`
can be `⊥`.

## Main definitions

* `ConvexOpt.Program`: an optimization problem, with `Program.IsConvex` and `Program.feasible`.
* `Program.primalValue`, `Program.IsOptimal`: `p*` and the optimal points.
* `Program.lagrangian`, `Program.dualFun`, `Program.dualValue`: `L`, `φ` and `d*`.
* `Program.IsSlaterPoint`: a strictly feasible point.

## Main statements

* `Program.dualFun_le`, `Program.dualValue_le_primalValue`: **weak duality**.
* `Program.convex_hypograph_dualFun`: the dual function is concave.
* `Program.strong_duality`: **Slater's condition** implies strong duality, and the dual optimum is
  attained if `p*` is finite.
* `Program.kkt_of_isOptimal`, `Program.isOptimal_of_kkt`, `Program.kkt_iff`,
  `Program.exists_kkt_of_slater`: **the KKT conditions**.
* `le_of_hasFDerivAt_zero`: a stationary point of a convex function minimizes it.
* `lp_lagrangian`, `lp_dualFun_of_eq`, `lp_dualFun_of_ne`, `lp_dualValue`: the dual of a linear
  program.

## References

* [S. Boyd and L. Vandenberghe, *Convex Optimization*][boyd2004]
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Appendix E
-/

open Finset Module Set Matrix

@[expose] public noncomputable section

/-! ### Separating a point from a convex set -/

section Separation

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Separation in finite dimension, with no topological assumption on the set.** A nonempty
convex set that does not contain `0` lies in a closed half space through `0`. -/
theorem exists_dual_nonneg_of_convex_of_notMem {S : Set W} (hS : Convex ℝ S) (hne : S.Nonempty)
    (h0 : (0 : W) ∉ S) : ∃ f : StrongDual ℝ W, f ≠ 0 ∧ ∀ w ∈ S, 0 ≤ f w := by
  by_cases hc : (0 : W) ∈ closure S
  · have hfr : (0 : W) ∈ frontier S := ⟨hc, fun hi => h0 (interior_subset hi)⟩
    obtain ⟨g, -, hg, hle⟩ := exists_isSupportingAt hS hfr
    refine ⟨-g, neg_ne_zero.2 hg, fun w hw => ?_⟩
    have := hle w hw
    simpa using this
  · obtain ⟨f, u, hlt, hu⟩ := geometric_hahn_banach_point_closed hS.closure isClosed_closure hc
    rw [map_zero] at hlt
    obtain ⟨w₀, hw₀⟩ := hne
    refine ⟨f, fun hf => ?_, fun w hw => (hlt.trans (hu w (subset_closure hw))).le⟩
    have := hu w₀ (subset_closure hw₀)
    simp [hf] at this
    linarith

end Separation

namespace ConvexOpt

variable {E ι m : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Page E-6 of [elgamal2010].** A stationary point of a convex differentiable function, such as
a Lagrangian, minimizes it. -/
theorem le_of_hasFDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    {L : E → ℝ} (hL : ConvexOn ℝ C L) {x : E} (hx : x ∈ C)
    (hd : HasFDerivAt L (0 : StrongDual ℝ E) x) {y : E} (hy : y ∈ C) : L x ≤ L y := by
  have hline : HasLineDerivAt ℝ L 0 x (y - x) := by
    simpa using HasFDerivAt.hasLineDerivAt hd (y - x)
  have hder : HasDerivAt (fun t : ℝ => L (x + t • (y - x))) 0 0 := hline
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1
    (hder.hasDerivWithinAt (s := Ioi 0))
  have hle : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      slope (fun t : ℝ => L (x + t • (y - x))) 0 t ≤ L y - L x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hconv := hL.2 hx hy (sub_pos.2 ht.2).le ht.1.le (by ring)
    have e : (1 - t) • x + t • y = x + t • (y - x) := by
      simp only [sub_smul, smul_sub, one_smul]
      abel
    rw [e] at hconv
    simp only [smul_eq_mul] at hconv
    have ht0 := ht.1
    rw [slope_def_field, zero_smul, add_zero, sub_zero, div_le_iff₀ ht0]
    nlinarith
  have hlim : (0 : ℝ) ≤ L y - L x := le_of_tendsto hslope hle
  linarith

/-- **Page E-1 of [elgamal2010].** The problem `minimize g₀(x) subject to gⱼ(x) ≤ 0, j ∈ ι, A x = b`
for `x` in the domain `C`. -/
structure Program (E ι m : Type*) [AddCommGroup E] [Module ℝ E] where
  /-- The domain of the functions. -/
  dom : Set E
  /-- The objective `g₀`. -/
  obj : E → ℝ
  /-- The inequality constraints `gⱼ`. -/
  ineq : ι → E → ℝ
  /-- The matrix `A` of the equality constraints, as a linear map. -/
  A : E →ₗ[ℝ] m → ℝ
  /-- The vector `b` of the equality constraints. -/
  b : m → ℝ

namespace Program

variable (P : Program E ι m)

/-- The problem is convex if the domain and the functions `g₀, g₁, …, g_k` are convex. -/
def IsConvex : Prop :=
  Convex ℝ P.dom ∧ ConvexOn ℝ P.dom P.obj ∧ ∀ j, ConvexOn ℝ P.dom (P.ineq j)

/-- The set `D` of feasible points. -/
def feasible : Set E := {x | x ∈ P.dom ∧ (∀ j, P.ineq j x ≤ 0) ∧ P.A x = P.b}

/-- The optimal value `p* = inf {g₀(x) : x ∈ D}`, which is `⊤` for an infeasible problem. -/
def primalValue : EReal := ⨅ x ∈ P.feasible, (P.obj x : EReal)

/-- A point that attains the infimum. -/
def IsOptimal (x : E) : Prop := x ∈ P.feasible ∧ ∀ y ∈ P.feasible, P.obj x ≤ P.obj y

/-- An infeasible problem has the value `⊤`. -/
lemma primalValue_eq_top (h : P.feasible = ∅) : P.primalValue = ⊤ := by
  simp [primalValue, h]

variable [Fintype ι] [Fintype m]

/-- **Page E-3 of [elgamal2010].** The Lagrangian
`L(x, λ, ν) = g₀(x) + ∑ⱼ λⱼ gⱼ(x) + νᵀ (A x - b)`. -/
def lagrangian (x : E) (l : ι → ℝ) (ν : m → ℝ) : ℝ :=
  P.obj x + ∑ j, l j * P.ineq j x + ∑ i, ν i * (P.A x i - P.b i)

/-- The dual function `φ(λ, ν) = inf_x L(x, λ, ν)`. -/
def dualFun (l : ι → ℝ) (ν : m → ℝ) : EReal := ⨅ x ∈ P.dom, (P.lagrangian x l ν : EReal)

/-- The optimal value `d*` of the dual problem `maximize φ(λ, ν) subject to λⱼ ≥ 0`. -/
def dualValue : EReal := ⨆ (l : ι → ℝ) (_ : ∀ j, 0 ≤ l j) (ν : m → ℝ), P.dualFun l ν

/-- A dual optimal point. -/
def IsDualOptimal (l : ι → ℝ) (ν : m → ℝ) : Prop :=
  (∀ j, 0 ≤ l j) ∧ ∀ (l' : ι → ℝ) (ν' : m → ℝ), (∀ j, 0 ≤ l' j) → P.dualFun l' ν' ≤ P.dualFun l ν

variable {P}

/-! ### Weak duality -/

/-- On a feasible point the Lagrangian with `λ ≥ 0` is at most the objective. -/
lemma lagrangian_le_obj {x : E} (hx : x ∈ P.feasible) {l : ι → ℝ} (hl : ∀ j, 0 ≤ l j) (ν : m → ℝ) :
    P.lagrangian x l ν ≤ P.obj x := by
  obtain ⟨-, hg, hA⟩ := hx
  have h1 : ∑ j, l j * P.ineq j x ≤ 0 :=
    sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hl j) (hg j)
  have h2 : ∑ i, ν i * (P.A x i - P.b i) = 0 := sum_eq_zero fun i _ => by simp [hA]
  simp only [lagrangian, h2]
  linarith

/-- The dual function is at most the Lagrangian. -/
lemma dualFun_le_lagrangian {x : E} (hx : x ∈ P.dom) (l : ι → ℝ) (ν : m → ℝ) :
    P.dualFun l ν ≤ P.lagrangian x l ν :=
  iInf₂_le x hx

/-- **Page E-3 of [elgamal2010].** `φ(λ, ν) ≤ g₀(x)` for `λ ≥ 0` and a feasible `x`. -/
theorem dualFun_le {x : E} (hx : x ∈ P.feasible) {l : ι → ℝ} (hl : ∀ j, 0 ≤ l j) (ν : m → ℝ) :
    P.dualFun l ν ≤ P.obj x :=
  (dualFun_le_lagrangian hx.1 l ν).trans (EReal.coe_le_coe_iff.2 (lagrangian_le_obj hx hl ν))

/-- The dual function at a dual feasible point is at most the dual value. -/
lemma dualFun_le_dualValue {l : ι → ℝ} (hl : ∀ j, 0 ≤ l j) (ν : m → ℝ) :
    P.dualFun l ν ≤ P.dualValue :=
  le_iSup_of_le l (le_iSup_of_le hl (le_iSup_of_le ν le_rfl))

omit [Fintype ι] [Fintype m] in
/-- The value at an optimal point is the optimal value. -/
lemma IsOptimal.primalValue_eq {x : E} (hx : P.IsOptimal x) : P.primalValue = P.obj x :=
  le_antisymm (iInf₂_le x hx.1) (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hx.2 y hy))

/-- **Weak duality, page E-5 of [elgamal2010].** `d* ≤ p*`. -/
theorem dualValue_le_primalValue : P.dualValue ≤ P.primalValue :=
  iSup_le fun _ => iSup_le fun hl => iSup_le fun ν => le_iInf₂ fun _ hx => dualFun_le hx hl ν

/-- **Page E-3 of [elgamal2010].** The dual function is concave, whether the primal problem is
convex or not: its hypograph is convex. -/
theorem convex_hypograph_dualFun (P : Program E ι m) :
    Convex ℝ {z : (ι → ℝ) × (m → ℝ) × ℝ | (z.2.2 : EReal) ≤ P.dualFun z.1 z.2.1} := by
  rintro ⟨l₁, ν₁, c₁⟩ h₁ ⟨l₂, ν₂, c₂⟩ h₂ a b ha hb hab
  simp only [Set.mem_ofPred_eq, dualFun, le_iInf₂_iff, EReal.coe_le_coe_iff] at h₁ h₂ ⊢
  intro x hx
  have e : P.lagrangian x (a • l₁ + b • l₂) (a • ν₁ + b • ν₂) =
      a * P.lagrangian x l₁ ν₁ + b * P.lagrangian x l₂ ν₂ := by
    have s₁ : ∑ j, (a • l₁ + b • l₂) j * P.ineq j x =
        a * ∑ j, l₁ j * P.ineq j x + b * ∑ j, l₂ j * P.ineq j x := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have s₂ : ∑ i, (a • ν₁ + b • ν₂) i * (P.A x i - P.b i) =
        a * ∑ i, ν₁ i * (P.A x i - P.b i) + b * ∑ i, ν₂ i * (P.A x i - P.b i) := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [lagrangian]
    rw [s₁, s₂]
    linear_combination (-P.obj x) * hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left (h₁ x hx) ha) (mul_le_mul_of_nonneg_left (h₂ x hx) hb)

/-! ### The KKT conditions -/

/-- **Pages E-5 and E-6 of [elgamal2010].** If `x*` is optimal and `φ(λ*, ν*) = g₀(x*)`, then `x*`
minimizes `L(x, λ*, ν*)` and `λⱼ* gⱼ(x*) = 0`. -/
theorem kkt_of_isOptimal {x : E} (hx : P.IsOptimal x) {l : ι → ℝ} (hl : ∀ j, 0 ≤ l j) {ν : m → ℝ}
    (hd : P.dualFun l ν = P.obj x) :
    (∀ y ∈ P.dom, P.lagrangian x l ν ≤ P.lagrangian y l ν) ∧ ∀ j, l j * P.ineq j x = 0 := by
  have hf := hx.1
  have hle := lagrangian_le_obj hf hl ν
  have hge : P.obj x ≤ P.lagrangian x l ν := by
    have := dualFun_le_lagrangian hf.1 l ν
    rwa [hd, EReal.coe_le_coe_iff] at this
  have heq : P.lagrangian x l ν = P.obj x := le_antisymm hle hge
  refine ⟨fun y hy => ?_, fun j => ?_⟩
  · have := dualFun_le_lagrangian hy l ν
    rw [hd, EReal.coe_le_coe_iff] at this
    linarith
  · have h2 : ∑ i, ν i * (P.A x i - P.b i) = 0 := sum_eq_zero fun i _ => by simp [hf.2.2]
    have h1 : ∑ j, l j * P.ineq j x = 0 := by
      simp only [lagrangian, h2] at heq
      linarith
    exact (sum_eq_zero_iff_of_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hl j)
      (hf.2.1 j)).1 h1 j (mem_univ j)

/-- **Page E-6 of [elgamal2010].** Conversely, if `x*` is feasible, `λ* ≥ 0`, `x*` minimizes
`L(x, λ*, ν*)` and `λⱼ* gⱼ(x*) = 0`, then `x*` is optimal, `(λ*, ν*)` is dual optimal, and strong
duality holds. -/
theorem isOptimal_of_kkt {x : E} (hx : x ∈ P.feasible) {l : ι → ℝ} (hl : ∀ j, 0 ≤ l j) {ν : m → ℝ}
    (hmin : ∀ y ∈ P.dom, P.lagrangian x l ν ≤ P.lagrangian y l ν)
    (hcs : ∀ j, l j * P.ineq j x = 0) :
    P.IsOptimal x ∧ P.IsDualOptimal l ν ∧ P.dualFun l ν = P.obj x ∧
      P.primalValue = P.obj x ∧ P.dualValue = P.obj x := by
  have heq : P.lagrangian x l ν = P.obj x := by
    have h2 : ∑ i, ν i * (P.A x i - P.b i) = 0 := sum_eq_zero fun i _ => by simp [hx.2.2]
    simp [lagrangian, h2, hcs]
  have hd : P.dualFun l ν = P.obj x := by
    refine le_antisymm (dualFun_le hx hl ν) (le_iInf₂ fun y hy => ?_)
    rw [EReal.coe_le_coe_iff, ← heq]
    exact hmin y hy
  have hopt : P.IsOptimal x := ⟨hx, fun y hy => by
    have := dualFun_le hy hl ν
    rwa [hd, EReal.coe_le_coe_iff] at this⟩
  have hp : P.primalValue = P.obj x :=
    le_antisymm (iInf₂_le x hx) (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hopt.2 y hy))
  have hdv : P.dualValue = P.obj x := by
    refine le_antisymm (hp ▸ dualValue_le_primalValue) ?_
    rw [← hd]
    exact dualFun_le_dualValue hl ν
  refine ⟨hopt, ⟨hl, fun l' ν' hl' => ?_⟩, hd, hp, hdv⟩
  rw [hd, ← hp]
  exact (dualFun_le_dualValue hl' ν').trans dualValue_le_primalValue

/-- **The KKT condition on pages E-5 and E-6 of [elgamal2010].** For a feasible `x*` and `λ* ≥ 0`,
the following are equivalent: `x*` is optimal with `φ(λ*, ν*) = g₀(x*)`; and `x*` minimizes
`L(x, λ*, ν*)` with complementary slackness. -/
theorem kkt_iff {x : E} (hx : x ∈ P.feasible) {l : ι → ℝ} (hl : ∀ j, 0 ≤ l j) {ν : m → ℝ} :
    (P.IsOptimal x ∧ P.dualFun l ν = P.obj x) ↔
      (∀ y ∈ P.dom, P.lagrangian x l ν ≤ P.lagrangian y l ν) ∧ ∀ j, l j * P.ineq j x = 0 := by
  constructor
  · rintro ⟨h, hd⟩
    exact kkt_of_isOptimal h hl hd
  · rintro ⟨hmin, hcs⟩
    obtain ⟨h, -, hd, -⟩ := isOptimal_of_kkt hx hl hmin hcs
    exact ⟨h, hd⟩

/-! ### Slater's condition -/

/-- **Page E-5 of [elgamal2010].** A strictly feasible point: `x ∈ C`, `gⱼ(x) < 0` and `A x = b`.
Moreover `A x - b` reaches each direction of the range of `A` from the domain, which holds if
`C = E` or if there is no equality constraint. -/
def IsSlaterPoint (P : Program E ι m) (x : E) : Prop :=
  x ∈ P.dom ∧ (∀ j, P.ineq j x < 0) ∧ P.A x = P.b ∧
    ∀ y, ∃ z ∈ P.dom, ∃ c : ℝ, 0 < c ∧ P.A z - P.b = c • P.A y

omit [Fintype ι] [Fintype m] in
/-- A strictly feasible point of a problem on the whole space is a Slater point. -/
lemma isSlaterPoint_of_univ (hdom : P.dom = Set.univ) {x : E} (hg : ∀ j, P.ineq j x < 0)
    (hA : P.A x = P.b) : P.IsSlaterPoint x := by
  refine ⟨by simp [hdom], hg, hA, fun y => ⟨x + y, by simp [hdom], 1, one_pos, ?_⟩⟩
  rw [map_add, hA, one_smul]
  abel

/-- The Lagrange multipliers: under Slater's condition, there are `λ ≥ 0` and `ν` such that a lower
bound `p` of `g₀` on the feasible points is a lower bound of `L(x, λ, ν)`. -/
theorem exists_multipliers (hP : P.IsConvex) {x₀ : E} (hx₀ : P.IsSlaterPoint x₀) {p : ℝ}
    (hp : ∀ y ∈ P.feasible, p ≤ P.obj y) :
    ∃ (l : ι → ℝ) (ν : m → ℝ), (∀ j, 0 ≤ l j) ∧ ∀ x ∈ P.dom, p ≤ P.lagrangian x l ν := by
  classical
  obtain ⟨hC, hobj, hineq⟩ := hP
  obtain ⟨hx₀C, hx₀g, hx₀A, hrel⟩ := hx₀
  -- The range of `A`, in which `A x - b` takes its values.
  set T : Submodule ℝ (m → ℝ) := LinearMap.range P.A with hT
  have hvT : ∀ x, P.A x - P.b ∈ T := fun x => by
    refine ⟨x - x₀, ?_⟩
    rw [map_sub, hx₀A]
  -- The convex set of values, which does not contain `0`.
  set S : Set ((ι → ℝ) × T × ℝ) := {w | ∃ x ∈ P.dom, (∀ j, P.ineq j x ≤ w.1 j) ∧
    (w.2.1 : m → ℝ) = P.A x - P.b ∧ P.obj x - p < w.2.2} with hS
  have hSc : Convex ℝ S := by
    rintro ⟨u₁, v₁, t₁⟩ ⟨x₁, hx₁, h₁₁, h₁₂, h₁₃⟩ ⟨u₂, v₂, t₂⟩ ⟨x₂, hx₂, h₂₁, h₂₂, h₂₃⟩ a b ha hb hab
    refine ⟨a • x₁ + b • x₂, hC hx₁ hx₂ ha hb hab, fun j => ?_, ?_, ?_⟩
    · have := (hineq j).2 hx₁ hx₂ ha hb hab
      simp only [smul_eq_mul] at this
      have h₁ := mul_le_mul_of_nonneg_left (h₁₁ j) ha
      have h₂ := mul_le_mul_of_nonneg_left (h₂₁ j) hb
      simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · simp only [Prod.smul_mk, Prod.mk_add_mk, Submodule.coe_add, Submodule.coe_smul]
      simp only at h₁₂ h₂₂
      rw [h₁₂, h₂₂, map_add, map_smul, map_smul]
      have : P.b = a • P.b + b • P.b := by rw [← add_smul, hab, one_smul]
      nth_rw 3 [this]
      simp only [smul_sub]
      abel
    · have := hobj.2 hx₁ hx₂ ha hb hab
      simp only [smul_eq_mul] at this
      simp only at h₁₃ h₂₃
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      rcases ha.eq_or_lt with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1
        simpa using h₂₃
      · have h₁ := mul_lt_mul_of_pos_left h₁₃ ha'
        have h₂ := mul_le_mul_of_nonneg_left h₂₃.le hb
        have hpe : p = a * p + b * p := by rw [← add_mul, hab, one_mul]
        linarith
  have hS0 : (0 : (ι → ℝ) × T × ℝ) ∉ S := by
    rintro ⟨x, hx, h₁, h₂, h₃⟩
    have hA : P.A x = P.b := by
      have : P.A x - P.b = 0 := by simpa using h₂.symm
      exact sub_eq_zero.1 this
    have := hp x ⟨hx, fun j => by simpa using h₁ j, hA⟩
    simp only [Prod.snd_zero] at h₃
    linarith
  have hSne : S.Nonempty := by
    refine ⟨(fun j => P.ineq j x₀, ⟨P.A x₀ - P.b, hvT x₀⟩, P.obj x₀ - p + 1), x₀, hx₀C,
      fun j => le_rfl, rfl, ?_⟩
    simp
  obtain ⟨f, hf, hfS⟩ := exists_dual_nonneg_of_convex_of_notMem hSc hSne hS0
  -- The components of the functional.
  set lam : ι → ℝ := fun j => f (Pi.single j 1, 0, 0) with hlam
  set mu : ℝ := f (0, 0, 1) with hmu
  set ν₀ : T →ₗ[ℝ] ℝ := f.toLinearMap ∘ₗ (LinearMap.inr ℝ (ι → ℝ) (T × ℝ)) ∘ₗ
    (LinearMap.inl ℝ T ℝ) with hν₀
  have hfe : ∀ (u : ι → ℝ) (v : T) (t : ℝ), f (u, v, t) = ∑ j, lam j * u j + ν₀ v + mu * t := by
    intro u v t
    have e : ((u, v, t) : (ι → ℝ) × T × ℝ) =
        ∑ j, u j • ((Pi.single j 1, 0, 0) : (ι → ℝ) × T × ℝ) + (0, v, 0) + t • (0, 0, 1) := by
      refine Prod.ext (funext fun i => ?_) (Prod.ext ?_ ?_)
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
      · simp [Prod.snd_sum]
    rw [e, map_add, map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    have e₁ : f (0, v, 0) = ν₀ v := rfl
    rw [e₁]
    have e₂ : ∑ j, u j * f (Pi.single j 1, 0, 0) = ∑ j, lam j * u j :=
      sum_congr rfl fun j _ => mul_comm _ _
    rw [e₂, mul_comm t]
  -- The basic inequality, for all larger values.
  have hbase : ∀ x ∈ P.dom, ∀ (u : ι → ℝ) (t : ℝ), (∀ j, P.ineq j x ≤ u j) → P.obj x - p < t →
      0 ≤ ∑ j, lam j * u j + ν₀ ⟨P.A x - P.b, hvT x⟩ + mu * t := fun x hx u t hu ht => by
    rw [← hfe]
    exact hfS _ ⟨x, hx, hu, rfl, ht⟩
  have hx₀base := hbase x₀ hx₀C
  have hv₀ : (⟨P.A x₀ - P.b, hvT x₀⟩ : T) = 0 := by
    ext i
    simp [hx₀A]
  -- `μ ≥ 0` and `λ ≥ 0`.
  have hmu0 : 0 ≤ mu := by
    by_contra hn
    push Not at hn
    set B := ∑ j, lam j * P.ineq j x₀ + ν₀ ⟨P.A x₀ - P.b, hvT x₀⟩ with hB
    set t := max (P.obj x₀ - p + 1) ((B + 1) / (-mu)) with ht
    have h1 := hx₀base (fun j => P.ineq j x₀) t (fun _ => le_rfl)
      (lt_of_lt_of_le (by linarith) (le_max_left _ _))
    have h2 : (B + 1) / (-mu) ≤ t := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at h2
    nlinarith
  have hlam0 : ∀ j, 0 ≤ lam j := by
    intro j
    by_contra hn
    push Not at hn
    set B := ∑ i, lam i * P.ineq i x₀ + ν₀ ⟨P.A x₀ - P.b, hvT x₀⟩ + mu * (P.obj x₀ - p + 1) with hB
    set s := max 0 ((B + 1) / (-lam j)) with hs
    have hs0 : 0 ≤ s := le_max_left _ _
    have h2 : (B + 1) / (-lam j) ≤ s := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at h2
    have h1 := hx₀base (fun i => P.ineq i x₀ + s * (Pi.single j 1 : ι → ℝ) i) (P.obj x₀ - p + 1)
      (fun i => by
        have : 0 ≤ s * (Pi.single j 1 : ι → ℝ) i := mul_nonneg hs0 (by
          by_cases h : i = j
          · subst h
            simp
          · simp [h])
        linarith) (by linarith)
    have e : ∑ i, lam i * (P.ineq i x₀ + s * (Pi.single j 1 : ι → ℝ) i) =
        ∑ i, lam i * P.ineq i x₀ + lam j * s := by
      simp only [mul_add, sum_add_distrib]
      congr 1
      rw [sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
      simp
    rw [e] at h1
    nlinarith
  -- The inequality at the point itself, by taking limits.
  have hmain : ∀ x ∈ P.dom,
      0 ≤ ∑ j, lam j * P.ineq j x + ν₀ ⟨P.A x - P.b, hvT x⟩ + mu * (P.obj x - p) := by
    intro x hx
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hmu1 : 0 < mu + 1 := by linarith
    have h := hbase x hx (fun j => P.ineq j x) (P.obj x - p + ε / (mu + 1)) (fun _ => le_rfl)
      (by have := div_pos hε hmu1; linarith)
    have h3 : mu * (ε / (mu + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hmu1]
      nlinarith
    rw [mul_add] at h
    linarith
  -- `μ > 0`, by the strictly feasible point.
  have hmupos : 0 < mu := by
    by_contra hn
    have hm0 : mu = 0 := le_antisymm (not_lt.1 hn) hmu0
    have hlz : ∀ j, lam j = 0 := by
      have h := hmain x₀ hx₀C
      rw [hv₀, map_zero, hm0, zero_mul, add_zero, add_zero] at h
      have hle : ∀ j ∈ (univ : Finset ι), lam j * P.ineq j x₀ ≤ 0 := fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (hlam0 j) (hx₀g j).le
      have h0 := (sum_eq_zero_iff_of_nonpos hle).1 (le_antisymm (sum_nonpos hle) h)
      intro j
      have := h0 j (mem_univ j)
      exact (mul_eq_zero.1 this).resolve_right (hx₀g j).ne
    have hνnn : ∀ y, 0 ≤ ν₀ ⟨P.A y, LinearMap.mem_range_self _ y⟩ := by
      intro y
      obtain ⟨z, hz, c, hc, hzc⟩ := hrel y
      have h := hmain z hz
      simp only [hlz, zero_mul, sum_const_zero, zero_add, hm0, add_zero] at h
      have e : (⟨P.A z - P.b, hvT z⟩ : T) = c • ⟨P.A y, LinearMap.mem_range_self _ y⟩ :=
        Subtype.ext hzc
      rw [e, map_smul, smul_eq_mul] at h
      exact nonneg_of_mul_nonneg_right h hc
    have hν0 : ν₀ = 0 := by
      ext ⟨v, y, rfl⟩
      have h1 := hνnn y
      have h2 := hνnn (-y)
      have e : (⟨P.A (-y), LinearMap.mem_range_self _ (-y)⟩ : T) =
          -⟨P.A y, LinearMap.mem_range_self _ y⟩ := by
        ext i
        simp
      rw [e, map_neg] at h2
      change ν₀ ⟨P.A y, LinearMap.mem_range_self _ y⟩ = 0
      exact le_antisymm (by linarith) h1
    apply hf
    refine ContinuousLinearMap.ext fun w => ?_
    obtain ⟨u, v, t⟩ := w
    rw [hfe]
    simp [hlz, hm0, hν0]
  -- Normalize by `μ`.
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ν₀
  have hgv : ∀ x, ν₀ ⟨P.A x - P.b, hvT x⟩ = g (P.A x - P.b) := fun x => by
    rw [← hg]
    rfl
  refine ⟨fun j => lam j / mu, fun i => g (fun k => if i = k then 1 else 0) / mu,
    fun j => div_nonneg (hlam0 j) hmupos.le, fun x hx => ?_⟩
  have h := div_nonneg (hmain x hx) hmupos.le
  rw [hgv, LinearMap.pi_apply_eq_sum_univ g (P.A x - P.b)] at h
  have e : (∑ j, lam j * P.ineq j x + ∑ i, (P.A x - P.b) i • g (fun k => if i = k then 1 else 0) +
      mu * (P.obj x - p)) / mu = P.lagrangian x (fun j => lam j / mu)
        (fun i => g (fun k => if i = k then 1 else 0) / mu) - p := by
    have hne := hmupos.ne'
    have h₁ : (∑ j, lam j * P.ineq j x) / mu = ∑ j, lam j / mu * P.ineq j x := by
      rw [sum_div]
      exact sum_congr rfl fun j _ => by ring
    have h₂ : (∑ i, (P.A x - P.b) i • g (fun k => if i = k then 1 else 0)) / mu =
        ∑ i, g (fun k => if i = k then 1 else 0) / mu * (P.A x i - P.b i) := by
      rw [sum_div]
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.sub_apply, smul_eq_mul]
      ring
    have h₃ : mu * (P.obj x - p) / mu = P.obj x - p := by field_simp
    rw [add_div, add_div, h₁, h₂, h₃, lagrangian]
    ring
  rw [e] at h
  linarith

/-- **Slater's condition, page E-5 of [elgamal2010].** If the primal problem is convex and has a
strictly feasible point, then strong duality holds, `d* = p*`. If moreover `p*` is finite, then the
dual optimum is attained. -/
theorem strong_duality (hP : P.IsConvex) {x₀ : E} (hx₀ : P.IsSlaterPoint x₀) :
    P.dualValue = P.primalValue ∧ (P.primalValue ≠ ⊥ →
      ∃ (l : ι → ℝ) (ν : m → ℝ), (∀ j, 0 ≤ l j) ∧ P.dualFun l ν = P.primalValue) := by
  have hf : x₀ ∈ P.feasible := ⟨hx₀.1, fun j => (hx₀.2.1 j).le, hx₀.2.2.1⟩
  by_cases hb : P.primalValue = ⊥
  · exact ⟨le_antisymm dualValue_le_primalValue (hb ▸ bot_le), fun h => absurd hb h⟩
  · have htop : P.primalValue ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) (iInf₂_le x₀ hf)
    obtain ⟨p, hp⟩ : ∃ p : ℝ, P.primalValue = p :=
      ⟨P.primalValue.toReal, (EReal.coe_toReal htop hb).symm⟩
    have hlow : ∀ y ∈ P.feasible, p ≤ P.obj y := fun y hy => by
      have : P.primalValue ≤ P.obj y := iInf₂_le y hy
      rwa [hp, EReal.coe_le_coe_iff] at this
    obtain ⟨l, ν, hl, hL⟩ := exists_multipliers hP hx₀ hlow
    have hd : (p : EReal) ≤ P.dualFun l ν := le_iInf₂ fun x hx => EReal.coe_le_coe_iff.2 (hL x hx)
    have hd2 : P.dualFun l ν ≤ P.dualValue := dualFun_le_dualValue hl ν
    have hup := dualValue_le_primalValue (P := P)
    refine ⟨le_antisymm hup (by rw [hp]; exact hd.trans hd2), fun _ => ⟨l, ν, hl, ?_⟩⟩
    rw [hp]
    exact le_antisymm (hd2.trans (hup.trans hp.le)) hd

/-- **The KKT condition, page E-6 of [elgamal2010].** Under Slater's condition, an optimal point
has multipliers that satisfy the KKT condition. -/
theorem exists_kkt_of_slater (hP : P.IsConvex) {x₀ : E} (hx₀ : P.IsSlaterPoint x₀) {x : E}
    (hx : P.IsOptimal x) :
    ∃ (l : ι → ℝ) (ν : m → ℝ), (∀ j, 0 ≤ l j) ∧ P.dualFun l ν = P.obj x ∧
      (∀ y ∈ P.dom, P.lagrangian x l ν ≤ P.lagrangian y l ν) ∧ ∀ j, l j * P.ineq j x = 0 := by
  obtain ⟨l, ν, hl, hL⟩ := exists_multipliers hP hx₀ hx.2
  have hd : P.dualFun l ν = P.obj x :=
    le_antisymm (dualFun_le hx.1 hl ν) (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hL y hy))
  obtain ⟨h₁, h₂⟩ := kkt_of_isOptimal hx hl hd
  exact ⟨l, ν, hl, hd, h₁, h₂⟩

end Program

/-! ### Linear programming -/

section LP

variable {n : Type*} [Fintype n]

/-- **Page E-2 of [elgamal2010].** The linear program
`minimize cᵀ x subject to A x = b and xⱼ ≥ 0 for all j`. -/
def lpProgram (c : n → ℝ) (A : Matrix m n ℝ) (b : m → ℝ) : Program (n → ℝ) n m where
  dom := Set.univ
  obj x := c ⬝ᵥ x
  ineq j x := -x j
  A := A.mulVecLin
  b := b

/-- A linear program is a convex problem. -/
theorem lpProgram_isConvex (c : n → ℝ) (A : Matrix m n ℝ) (b : m → ℝ) :
    (lpProgram c A b).IsConvex := by
  refine ⟨convex_univ, ⟨convex_univ, fun x _ y _ p q _ _ _ => le_of_eq ?_⟩,
    fun j => ⟨convex_univ, fun x _ y _ p q _ _ _ => le_of_eq ?_⟩⟩
  · simp only [lpProgram, dotProduct_add, dotProduct_smul, smul_eq_mul]
  · simp only [lpProgram, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

variable [Fintype m] {c : n → ℝ} {A : Matrix m n ℝ} {b : m → ℝ}

/-- **Page E-4 of [elgamal2010].** The Lagrangian of the linear program:
`L(x, λ, ν) = -bᵀ ν + (c + Aᵀ ν - λ)ᵀ x`. -/
theorem lp_lagrangian (x l : n → ℝ) (ν : m → ℝ) :
    (lpProgram c A b).lagrangian x l ν = -(b ⬝ᵥ ν) + (c + Aᵀ *ᵥ ν - l) ⬝ᵥ x := by
  have e₁ : ∑ i, ν i * ((A *ᵥ x) i - b i) = (Aᵀ *ᵥ ν) ⬝ᵥ x - b ⬝ᵥ ν := by
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    · rw [mulVec_transpose, ← dotProduct_mulVec]
      rfl
    · exact sum_congr rfl fun i _ => mul_comm _ _
  have e₂ : ∑ j, l j * -x j = -(l ⬝ᵥ x) := by
    simp only [dotProduct, mul_neg, sum_neg_distrib]
  simp only [Program.lagrangian, lpProgram, mulVecLin_apply, e₁, e₂, sub_dotProduct, add_dotProduct]
  ring

/-- **Page E-4 of [elgamal2010].** If `Aᵀ ν - λ + c = 0`, the dual function is `-bᵀ ν`. -/
theorem lp_dualFun_of_eq {l : n → ℝ} {ν : m → ℝ} (h : Aᵀ *ᵥ ν - l + c = 0) :
    (lpProgram c A b).dualFun l ν = (-(b ⬝ᵥ ν) : ℝ) := by
  have hc : c + Aᵀ *ᵥ ν - l = 0 := by rw [← h]; abel
  have hL : ∀ x, (lpProgram c A b).lagrangian x l ν = -(b ⬝ᵥ ν) := fun x => by
    rw [lp_lagrangian, hc, zero_dotProduct, add_zero]
  rw [Program.dualFun]
  simp only [hL]
  simp [lpProgram]

/-- **Page E-4 of [elgamal2010].** Otherwise, the dual function is `-∞`. -/
theorem lp_dualFun_of_ne {l : n → ℝ} {ν : m → ℝ} (h : Aᵀ *ᵥ ν - l + c ≠ 0) :
    (lpProgram c A b).dualFun l ν = ⊥ := by
  set d := c + Aᵀ *ᵥ ν - l with hd
  have hd0 : d ≠ 0 := fun h0 => h (by rw [← h0, hd]; abel)
  have hpos : 0 < d ⬝ᵥ d := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hd0
    have hsq : 0 < d i * d i := mul_self_pos.2 hi
    exact lt_of_lt_of_le hsq (single_le_sum (f := fun j => d j * d j)
      (fun j _ => mul_self_nonneg _) (mem_univ i))
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  -- Take `x = t d` for a large negative `t`.
  set t := (y - 1 + b ⬝ᵥ ν) / (d ⬝ᵥ d) with ht
  have hval : (lpProgram c A b).lagrangian (t • d) l ν = y - 1 := by
    rw [lp_lagrangian, ← hd, dotProduct_smul, smul_eq_mul, ht]
    field_simp
    ring
  refine lt_of_le_of_lt (Program.dualFun_le_lagrangian (x := t • d) (by simp [lpProgram]) l ν) ?_
  rw [hval, EReal.coe_lt_coe_iff]
  linarith

/-- **Page E-4 of [elgamal2010].** The dual of the linear program is the linear program
`maximize -bᵀ ν subject to Aᵀ ν - λ + c = 0 and λⱼ ≥ 0 for all j`. -/
theorem lp_dualValue :
    (lpProgram c A b).dualValue = ⨆ (l : n → ℝ) (_ : ∀ j, 0 ≤ l j) (ν : m → ℝ)
      (_ : Aᵀ *ᵥ ν - l + c = 0), ((-(b ⬝ᵥ ν) : ℝ) : EReal) := by
  refine le_antisymm (iSup_le fun l => iSup_le fun hl => iSup_le fun ν => ?_)
    (iSup_le fun l => iSup_le fun hl => iSup_le fun ν => iSup_le fun h => ?_)
  · by_cases h : Aᵀ *ᵥ ν - l + c = 0
    · rw [lp_dualFun_of_eq h]
      exact le_iSup_of_le l (le_iSup_of_le hl (le_iSup_of_le ν (le_iSup_of_le h le_rfl)))
    · rw [lp_dualFun_of_ne h]
      exact bot_le
  · rw [← lp_dualFun_of_eq h]
    exact Program.dualFun_le_dualValue hl ν

end LP

end ConvexOpt
