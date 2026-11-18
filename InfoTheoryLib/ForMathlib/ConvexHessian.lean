/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Convex functions in several variables

The second-order criterion for the convexity of a function on an open convex set of a normed space:
a twice differentiable function is convex if and only if its Hessian is positive semidefinite. The
Hessian at `x` is the bilinear form `fderiv ℝ (fderiv ℝ g) x`.

## Main statements

* `convexOn_iff_hessian_nonneg`: the second-order criterion.
* `convexOn_iSup`: the pointwise supremum of convex functions is convex.
* `concaveOn_sum_negMulLog`: `-∑ xⱼ log xⱼ` is concave on the nonnegative orthant.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Appendix A
-/

@[expose] public section

open Set Topology Filter Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Hessian

variable {S : Set E} {g : E → ℝ}

/-- The second derivative of a function along a line. -/
lemma hasDerivAt_fderiv_line {x v : E} {t : ℝ} (hg' : DifferentiableAt ℝ (fderiv ℝ g) (x + t • v)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ g (x + s • v) v)
      (fderiv ℝ (fderiv ℝ g) (x + t • v) v v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h1 := hg'.hasFDerivAt.comp_hasDerivAt t hline
  have h2 := h1.clm_apply (hasDerivAt_const t v)
  simpa using h2

/-- The first derivative of a function along a line. -/
lemma hasDerivAt_line {x v : E} {t : ℝ} (hg : DifferentiableAt ℝ g (x + t • v)) :
    HasDerivAt (fun s : ℝ => g (x + s • v)) (fderiv ℝ g (x + t • v) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact hg.hasFDerivAt.comp_hasDerivAt t hline

/-- **The second-order criterion for convexity.** On an open convex set, a twice differentiable
function is convex if and only if its Hessian is positive semidefinite at each point. -/
theorem convexOn_iff_hessian_nonneg (hS : Convex ℝ S) (hO : IsOpen S)
    (hg : ∀ x ∈ S, DifferentiableAt ℝ g x) (hg' : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ g) x) :
    ConvexOn ℝ S g ↔ ∀ x ∈ S, ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ g) x v v := by
  constructor
  · intro hc x hx v
    -- Restrict to a short segment through `x`.
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ S := by
      have hcont : Continuous fun t : ℝ => x + t • v := by fun_prop
      have : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
        simpa using hcont.tendsto 0
      exact this.eventually (hO.mem_nhds hx)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hmem
    set D := Ioo (-ε) ε with hD
    have hDm : ∀ t ∈ D, x + t • v ∈ S := fun t ht => hball t (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ht)
    have h0D : (0 : ℝ) ∈ D := ⟨by linarith, hε⟩
    have hconv : ConvexOn ℝ D fun t => g (x + t • v) := by
      refine ⟨convex_Ioo _ _, fun s hs t ht a b ha hb hab => ?_⟩
      have h1 := hc.2 (hDm s hs) (hDm t ht) ha hb hab
      have h2 : a • (x + s • v) + b • (x + t • v) = x + (a • s + b • t) • v := by
        have : x = (a + b) • x := by rw [hab, one_smul]
        nth_rw 3 [this]
        simp only [smul_add, add_smul, smul_smul, smul_eq_mul]
        abel
      rw [h2] at h1
      exact h1
    have hmono := hconv.monotoneOn_deriv fun t ht =>
      (hasDerivAt_line (hg _ (hDm t ht))).differentiableAt
    have hder : ∀ t ∈ D, deriv (fun s : ℝ => g (x + s • v)) t = fderiv ℝ g (x + t • v) v :=
      fun t ht => (hasDerivAt_line (hg _ (hDm t ht))).deriv
    have h2nd : HasDerivAt (fun s : ℝ => fderiv ℝ g (x + s • v) v)
        (fderiv ℝ (fderiv ℝ g) x v v) 0 := by
      have := hasDerivAt_fderiv_line (g := g) (x := x) (v := v) (t := 0) (by simpa using hg' x hx)
      simpa using this
    have hslope := (hasDerivAt_iff_tendsto_slope.1 h2nd).mono_left
      (nhdsWithin_mono (0 : ℝ) (s := Ioi 0) (t := {0}ᶜ) fun t ht => ne_of_gt ht)
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    have ht' : t ∈ D := ⟨by linarith [ht.1], ht.2⟩
    have h1 := hmono h0D ht' ht.1.le
    rw [hder 0 h0D, hder t ht'] at h1
    simp only [zero_smul, add_zero] at h1
    rw [slope_def_field, zero_smul, add_zero]
    exact div_nonneg (sub_nonneg.2 h1) (by linarith [ht.1])
  · intro hH
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    set v := y - x with hv
    set pt : ℝ → E := fun t => x + t • v with hpt
    have hptm : ∀ t ∈ Icc (0 : ℝ) 1, pt t ∈ S := by
      intro t ht
      have h1 : pt t = (1 - t) • x + t • y := by
        simp only [hpt, hv, smul_sub, sub_smul, one_smul]
        abel
      rw [h1]
      exact hS hx hy (by linarith [ht.2]) ht.1 (by ring)
    have hc1 : ConvexOn ℝ (Icc (0 : ℝ) 1) fun t => g (pt t) := by
      refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
        (f' := fun t => fderiv ℝ g (pt t) v) (f'' := fun t => fderiv ℝ (fderiv ℝ g) (pt t) v v)
        (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
      · exact (hasDerivAt_line (hg _ (hptm t ht))).continuousAt.continuousWithinAt
      · exact (hasDerivAt_line (hg _ (hptm t (interior_subset ht)))).hasDerivWithinAt
      · exact (hasDerivAt_fderiv_line (hg' _ (hptm t (interior_subset ht)))).hasDerivWithinAt
      · exact hH _ (hptm t (interior_subset ht)) v
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have h2 := hc1.2 h0 h1 ha hb hab
    have e0 : pt 0 = x := by simp [hpt]
    have e1 : pt 1 = y := by simp [hpt, hv]
    have e2 : pt (a • 0 + b • 1) = a • x + b • y := by
      have ha' : a = 1 - b := by linarith
      simp only [hpt, hv, ha', smul_eq_mul, mul_zero, mul_one, zero_add, smul_sub, sub_smul,
        one_smul]
      abel
    simp only [e0, e1, e2] at h2
    exact h2

end Hessian

/-- **The pointwise supremum of convex functions is convex**, when it is finite. -/
theorem convexOn_iSup {ι : Type*} [Nonempty ι] {S : Set E} {g : ι → E → ℝ} (hS : Convex ℝ S)
    (hg : ∀ i, ConvexOn ℝ S (g i)) (hb : ∀ x ∈ S, BddAbove (range fun i => g i x)) :
    ConvexOn ℝ S fun x => ⨆ i, g i x := by
  refine ⟨hS, fun x hx y hy a b ha hb' hab => ciSup_le fun i => ?_⟩
  calc g i (a • x + b • y) ≤ a • g i x + b • g i y := (hg i).2 hx hy ha hb' hab
    _ ≤ a • (⨆ i, g i x) + b • ⨆ i, g i y := by
        have h1 := le_ciSup (hb x hx) i
        have h2 := le_ciSup (hb y hy) i
        simp only [smul_eq_mul] at *
        exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb')

/-- **Entropy.** The function `-∑ xⱼ log xⱼ` is concave on the nonnegative orthant. -/
theorem concaveOn_sum_negMulLog {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ {x : ι → ℝ | ∀ j, 0 ≤ x j} fun x => ∑ j, negMulLog (x j) := by
  refine ⟨fun x hx y hy a b ha hb hab j => ?_, fun x hx y hy a b ha hb hab => ?_⟩
  · have := add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))
    simpa using this
  · simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := concaveOn_negMulLog.2 (x := x j) (y := y j) (hx j) (hy j) ha hb hab
    simpa using this
