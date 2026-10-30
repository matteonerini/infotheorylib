/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.Log

/-!
# Integrals under linear changes of variables

## Main statements

* `integral_comp_linearEquiv`: for an additive Haar measure `μ` on a finite-dimensional real
  vector space and a linear equivalence `A`, `∫ g(A x) dμ(x) = |det A|⁻¹ ∫ g dμ`.
-/

@[expose] public section

open MeasureTheory

namespace InfoTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- Change of variables under a linear equivalence: `∫ g(A x) dμ(x) = |det A|⁻¹ ∫ g(y) dμ(y)`. -/
theorem integral_comp_linearEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃ₗ[ℝ] E)
    (g : E → ℝ) :
    ∫ x, g (A x) ∂μ = |LinearMap.det (A : E →ₗ[ℝ] E)|⁻¹ * ∫ y, g y ∂μ := by
  have hdet : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := A.isUnit_det'.ne_zero
  let e : E ≃ᵐ E := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ x, e x = A x := fun _ => rfl
  have hmap : Measure.map e μ = ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  rw [show (fun x => g (A x)) = fun x => g (e x) from funext fun x => by rw [he],
    ← integral_map_equiv e g, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_inv, smul_eq_mul]

end InfoTheory
