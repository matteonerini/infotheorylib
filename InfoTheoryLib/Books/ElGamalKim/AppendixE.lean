/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.DetMaximization
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# El Gamal & Kim, Appendix E: Convex Optimization

This file indexes the formalization of Appendix E of [elgamal2010]. The notes review these results
and refer to [boyd2004] for the proofs. We prove them: Mathlib has neither Lagrangian duality, nor
Slater's condition, nor the KKT conditions for inequality constraints.

## Conventions

* **Problems.** `ConvexOpt.Program E ι m` is `minimize g₀(x) subject to gⱼ(x) ≤ 0, A x = b` for `x`
  in a domain `C`, in a real vector space `E` with no topology. The functions are real valued on
  `E`, and matter only on `C`. The notes leave the domain implicit, and need it: `log |X + K|` and
  `log |K|` are concave only where the matrix is positive definite.
* **Values.** `p*`, `φ` and `d*` are extended reals, in `EReal`.
* **Maximization.** A maximization problem is written as the minimization of the opposite function.
* **The matrix inequality.** In `detMaxProgram`, the constraint `X ≽ 0` is the domain, and `Υ` does
  not appear as a multiplier, since `Program` has finitely many scalar constraints. `Υ` is in the
  KKT conditions `IsDetMaxKKT`, which we prove directly.

## Index

Module names are relative to `InfoTheoryLib`; the general results are in
`ForMathlib.ConvexOptimization`, in namespace `ConvexOpt`, and "here" means this file.

### The problem (page E-1)
* `Program`, `Program.IsConvex`, `Program.feasible`, `Program.primalValue`, `Program.IsOptimal`,
  `Program.primalValue_eq_top`, `Program.IsOptimal.primalValue_eq`.

### The examples (page E-2)
* Linear programming: `lpProgram`, `lpProgram_isConvex`.
* Differential entropy maximization under correlation constraints: `burgProgram`,
  `burgProgram_isConvex` (`GaussianChannel.DetMaximization`).

### The dual problem (pages E-2 to E-4)
* The Lagrangian, the dual function and the dual problem: `Program.lagrangian`, `Program.dualFun`,
  `Program.dualValue`, `Program.IsDualOptimal`.
* `φ(λ, ν) ≤ g₀(x)`: `Program.dualFun_le`.
* The dual function is concave, whether the primal problem is convex or not:
  `Program.convex_hypograph_dualFun`.
* The dual of a linear program: `lp_lagrangian`, `lp_dualFun_of_eq`, `lp_dualFun_of_ne`,
  `lp_dualValue`.

### Strong duality (page E-5)
* `d* ≤ p*`: `Program.dualValue_le_primalValue`.
* Separation in finite dimension: `exists_dual_nonneg_of_convex_of_notMem`.
* **Slater's condition:** `Program.IsSlaterPoint`, `Program.isSlaterPoint_of_univ`,
  `Program.exists_multipliers`, `Program.strong_duality`.

### The KKT condition (pages E-5 and E-6)
* Necessity: `Program.kkt_of_isOptimal`.
* Sufficiency, with dual optimality and strong duality: `Program.isOptimal_of_kkt`.
* **The condition:** `Program.kkt_iff`.
* Under Slater's condition: `Program.exists_kkt_of_slater`.
* A stationary point of a convex differentiable function: `le_of_hasFDerivAt_zero`.

### The determinant maximization problem (pages E-6 and E-7; `GaussianChannel.DetMaximization`)
* `X ≽ 0` iff `tr(Υ X) ≥ 0` for every `Υ ≽ 0`: `posSemidef_iff_forall_trace_mul_nonneg`.
* The Lagrangian form, Slater's condition and strong duality: `detMaxProgram`,
  `mem_feasible_detMaxProgram`, `detMaxProgram_isConvex`, `detMaxProgram_isSlaterPoint`,
  `detMaxProgram_strong_duality`.
* The KKT conditions: `IsDetMaxKKT`, `IsDetMaxOptimal`, `isDetMaxOptimal_of_kkt`.
* **The KKT conditions characterize the optimal `X`:** `isDetMaxOptimal_iff_kkt`.
* Their solution by water-filling and its uniqueness, which are not in the notes:
  `exists_detMaxKKT`, `eq_of_isDetMaxOptimal`, with the strict tangent bound `log_det_add_sub_lt`.
* The point `(P / 2) I` is not feasible: `printed_detMax_point_infeasible`.

## Differences from the notes

* **Domain.** `Program` has an explicit convex domain. Slater's condition then also asks that
  `A x - b` reaches each direction of the range of `A` from the domain, which holds on the whole
  space or with no equality constraint. We do not assume that `A` has full rank.
* **Strong duality.** We also prove that the dual optimum is attained when `p*` is finite.
* **KKT condition.** No convexity is needed for either direction of `Program.kkt_iff`. Convexity is
  used in `Program.exists_kkt_of_slater`, to obtain the multipliers.
* **Determinant maximization.** The notes apply Slater's condition with `Υ` as a multiplier for
  `X ≽ 0`, in the more general form with matrix inequalities. We keep `X ≽ 0` as the domain for
  strong duality. We prove the characterization by the KKT conditions directly, by the tangent bound
  of `log |X|` and water-filling, with no derivative of `log |X|`.
* **Slater's condition.** Strict feasibility is the hypothesis. See below for the relative interior.

## Not formalized

* Slater's condition for matrix inequalities, which the example on page E-6 uses implicitly, and the
  formula `(d/dY) log |Y| = Y⁻¹` of page E-7, which the direct proof does not need.
* The solution of the problem of Burg, and the max-det problem with linear matrix inequalities,
  which the notes cite.

## Issues in the notes

* **Page E-1.** `p*` is "`-∞` if the problem is infeasible". It should be `+∞`, the infimum of the
  empty set. With `-∞`, the bound `d* ≤ p*` of page E-5 fails, for instance for `g₀ = 0` and
  `g₁ = 1`, where `d* = +∞`: `printed_infeasible_value_false`.
* **Page E-4.** The dual function is written with `inf_{x ∈ D}`, which should be the infimum over
  all `x`, as on page E-3. Over the feasible set the formula does not hold.
* **Page E-5, Slater's condition.** "In the relative interior of `D`, that is, `gⱼ(x) < 0`": the two
  are not the same, and the reading with the relative interior is false. For
  `minimize x₁ subject to √(x₁² + x₂²) - x₂ ≤ 0` the feasible set is the ray `x₁ = 0, x₂ ≥ 0`, with
  the point `(0, 1)` in its relative interior, but `p* = 0` and `d* = -∞`:
  `printed_slater_relint_false`. Strict feasibility is what is needed.
* **Page E-5.** In the chain for the KKT condition, the first `≤` is an equality.
* **Page E-6.** "`X = (P/2) I` is feasible": its trace is `n P / 2`, which is larger than `P` for
  `n > 2`: `printed_detMax_point_infeasible`. The point `(P / (2 n)) I` is strictly feasible:
  `detMaxProgram_isSlaterPoint`. We need `P > 0` for it.
* **Page E-7.** The stationarity condition has `λ I` where the dual optimal point is `λ*`.
* **Page E-2.** "determininant" is a typo.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  E
* [S. Boyd and L. Vandenberghe, *Convex Optimization*][boyd2004]
-/

open Finset ConvexOpt

@[expose] public noncomputable section

namespace InfoTheory

namespace ElGamalKim

/-! ### The value of an infeasible problem -/

/-- The infeasible problem `minimize 0 subject to 1 ≤ 0`. -/
def infeasibleProgram : Program ℝ Unit (Fin 0) where
  dom := Set.univ
  obj _ := 0
  ineq _ _ := 1
  A := 0
  b := 0

/-- **The convention on page E-1 of [elgamal2010] fails.** The problem
`minimize 0 subject to 1 ≤ 0` is infeasible, and `d* = +∞`, so `d* ≤ p*` requires `p* = +∞`, and
not `p* = -∞`. -/
theorem printed_infeasible_value_false :
    infeasibleProgram.feasible = ∅ ∧ infeasibleProgram.primalValue = ⊤ ∧
      infeasibleProgram.dualValue = ⊤ := by
  have hf : infeasibleProgram.feasible = ∅ := by
    ext x
    simp [Program.feasible, infeasibleProgram]
  refine ⟨hf, Program.primalValue_eq_top _ hf, ?_⟩
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  have hd : infeasibleProgram.dualFun (fun _ => |y| + 1) (fun i => i.elim0) =
      ((|y| + 1 : ℝ) : EReal) := by
    simp [Program.dualFun, Program.lagrangian, infeasibleProgram]
  refine lt_of_lt_of_le ?_ (Program.dualFun_le_dualValue (P := infeasibleProgram)
    (l := fun _ => |y| + 1) (fun _ => by positivity) (fun i => i.elim0))
  rw [hd, EReal.coe_lt_coe_iff]
  linarith [le_abs_self y]

/-! ### Slater's condition and the relative interior -/

/-- The problem `minimize x₁ subject to √(x₁² + x₂²) - x₂ ≤ 0` on the plane. -/
def slaterGapProgram : Program (EuclideanSpace ℝ (Fin 2)) Unit (Fin 0) where
  dom := Set.univ
  obj x := x 0
  ineq _ x := ‖x‖ - x 1
  A := 0
  b := 0

lemma norm_plane (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The feasible set of the problem is the ray `x₁ = 0, x₂ ≥ 0`. -/
lemma mem_feasible_slaterGapProgram {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ slaterGapProgram.feasible ↔ x 0 = 0 ∧ 0 ≤ x 1 := by
  have e : x ∈ slaterGapProgram.feasible ↔ ‖x‖ ≤ x 1 := by
    simp [Program.feasible, slaterGapProgram]
  rw [e, norm_plane, Real.sqrt_le_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have : x 0 ^ 2 ≤ 0 := by linarith
    exact ⟨by nlinarith [sq_nonneg (x 0)], h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂, by simp [h₁]⟩

/-- The problem is convex. -/
lemma slaterGapProgram_isConvex : slaterGapProgram.IsConvex := by
  refine ⟨convex_univ, ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩,
    fun _ => ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩⟩
  · simp [slaterGapProgram]
  · have h := (convexOn_norm (E := EuclideanSpace ℝ (Fin 2)) convex_univ).2 (Set.mem_univ x)
      (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h
    simp only [slaterGapProgram, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply]
    nlinarith

/-- The Lagrangian is unbounded below: `d* = -∞`. -/
lemma slaterGapProgram_dualFun {l : Unit → ℝ} (hl : ∀ j, 0 ≤ l j) (ν : Fin 0 → ℝ) :
    slaterGapProgram.dualFun l ν = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  set c := l () with hc
  have hc0 : 0 ≤ c := hl ()
  set s := |r| + 2 with hs
  have hs0 : 0 < s := by positivity
  set y := (c + 1) * s ^ 2 + 1 with hy
  have hy0 : 0 < y := by positivity
  set x : EuclideanSpace ℝ (Fin 2) := !₂[-s, y] with hx
  have hx0 : x 0 = -s := by simp [hx]
  have hx1 : x 1 = y := by simp [hx]
  refine lt_of_le_of_lt (Program.dualFun_le_lagrangian (x := x) (by simp [slaterGapProgram]) l ν) ?_
  rw [EReal.coe_lt_coe_iff]
  simp only [Program.lagrangian, slaterGapProgram, Finset.univ_unique, sum_singleton,
    Finset.univ_eq_empty, sum_empty, add_zero, hx0, hx1]
  have hnorm : ‖x‖ ≤ y + s ^ 2 / (2 * y) := by
    rw [norm_plane, hx0, hx1, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e : (y + s ^ 2 / (2 * y)) ^ 2 = y ^ 2 + s ^ 2 + (s ^ 2 / (2 * y)) ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (s ^ 2 / (2 * y))]
  have hbound : c * (s ^ 2 / (2 * y)) ≤ 1 := by
    rw [mul_div_assoc', div_le_one (by positivity)]
    nlinarith [sq_nonneg s]
  have h1 : c * (‖x‖ - y) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith) hc0).trans hbound
  have hc2 : l PUnit.unit = c := rfl
  rw [hc2]
  have := le_abs_self r
  have := neg_abs_le r
  linarith [abs_nonneg r]

/-- **The reading of Slater's condition with the relative interior on page E-5 of [elgamal2010]
fails.** The problem `minimize x₁ subject to √(x₁² + x₂²) - x₂ ≤ 0` is convex, and the point
`(0, 1)` is feasible and in the relative interior of the feasible set, but `p* = 0` and `d* = -∞`.
At this point the constraint is active, so it is not strictly feasible. -/
theorem printed_slater_relint_false :
    slaterGapProgram.IsConvex ∧
      (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) ∈ intrinsicInterior ℝ slaterGapProgram.feasible ∧
      slaterGapProgram.ineq () !₂[0, 1] = 0 ∧
      slaterGapProgram.primalValue = 0 ∧ slaterGapProgram.dualValue = ⊥ := by
  have hmem : (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)) ∈ slaterGapProgram.feasible := by
    rw [mem_feasible_slaterGapProgram]
    simp
  refine ⟨slaterGapProgram_isConvex, ?_, ?_, ?_, ?_⟩
  · have hspan : ∀ z ∈ affineSpan ℝ slaterGapProgram.feasible, z (0 : Fin 2) = 0 := by
      intro z hz
      refine affineSpan_induction (p := fun z : EuclideanSpace ℝ (Fin 2) => z 0 = 0) hz
        (fun x hx => (mem_feasible_slaterGapProgram.1 hx).1) fun c u v w hu hv hw => ?_
      simp [hu, hv, hw]
    rw [mem_intrinsicInterior]
    refine ⟨⟨_, subset_affineSpan ℝ _ hmem⟩, ?_, rfl⟩
    rw [mem_interior]
    refine ⟨{z | 0 < (z : EuclideanSpace ℝ (Fin 2)) 1}, fun z hz => ?_, ?_, by simp⟩
    · have hz' : 0 < (z : EuclideanSpace ℝ (Fin 2)) 1 := hz
      exact mem_feasible_slaterGapProgram.2 ⟨hspan z z.property, hz'.le⟩
    · exact isOpen_lt continuous_const (by fun_prop)
  · simp [slaterGapProgram, norm_plane]
  · refine le_antisymm (iInf₂_le_of_le _ hmem ?_) (le_iInf₂ fun x hx => ?_)
    · simp [slaterGapProgram]
    · have := (mem_feasible_slaterGapProgram.1 hx).1
      simp [slaterGapProgram, this]
  · exact iSup_eq_bot.2 fun l => iSup_eq_bot.2 fun hl => iSup_eq_bot.2 fun ν =>
      slaterGapProgram_dualFun hl ν

end ElGamalKim

end InfoTheory
