/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.Gaussian
public import InfoTheoryLib.DifferentialEntropy.Joint

/-!
# Estimation error with side information

Let `(X, Y)` have joint density `f(x, y)` with `X` real, and let `X̂(Y)` be an estimator of `X`
from the side information `Y`. The mean squared error is at least
`E(X - X̂(Y))² ≥ e^{2h(X|Y)}/(2πe)`. The proof applies Theorem 8.6.6 to the error
`Z = X - X̂(Y)`: shifting `X` by a function of `Y` does not change `h(X|Y)`, and conditioning
reduces differential entropy, so `h(X|Y) = h(Z|Y) ≤ h(Z)`.

## Main definitions

* `shearEquiv g`: the measurable equivalence `(x, y) ↦ (x + g(y), y)`.
* `errorPDF ν f g`: the density `f_Z(z) = ∫ f(z + X̂(y), y) dν(y)` of the error `Z = X - X̂(Y)`.

## Main statements

* `condDiffEntropy_shear`: `h(X - X̂(Y) | Y) = h(X|Y)`.
* `exp_two_mul_condDiffEntropy_div_le`: Corollary of Theorem 8.6.6,
  `E(X - X̂(Y))² ≥ e^{2h(X|Y)}/(2πe)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 8.6
-/

open Real MeasureTheory Filter

@[expose] public noncomputable section

namespace InfoTheory

variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

/-- The measurable equivalence `(x, y) ↦ (x + g(y), y)` of `ℝ × β`. -/
def shearEquiv {g : β → ℝ} (hg : Measurable g) : ℝ × β ≃ᵐ ℝ × β where
  toFun z := (z.1 + g z.2, z.2)
  invFun z := (z.1 - g z.2, z.2)
  left_inv z := by simp
  right_inv z := by simp
  measurable_toFun := (measurable_fst.add (hg.comp measurable_snd)).prodMk measurable_snd
  measurable_invFun := (measurable_fst.sub (hg.comp measurable_snd)).prodMk measurable_snd

@[simp]
lemma shearEquiv_apply {g : β → ℝ} (hg : Measurable g) (z : ℝ × β) :
    shearEquiv hg z = (z.1 + g z.2, z.2) := rfl

/-- The shear `(x, y) ↦ (x + g(y), y)` preserves the product of Lebesgue measure and `ν`. -/
lemma measurePreserving_shearEquiv [SFinite ν] {g : β → ℝ} (hg : Measurable g) :
    MeasurePreserving (shearEquiv hg) (volume.prod ν) (volume.prod ν) := by
  have hskew : MeasurePreserving (fun p : β × ℝ => (p.1, p.2 + g p.1)) (ν.prod volume)
      (ν.prod volume) :=
    (MeasurePreserving.id ν).skew_product (g := fun y x => x + g y)
      (measurable_snd.add (hg.comp measurable_fst))
      (Eventually.of_forall fun y => map_add_right_eq_self volume (g y))
  exact (Measure.measurePreserving_swap.comp hskew).comp Measure.measurePreserving_swap

/-- The density `f_Z(z) = ∫ f(z + X̂(y), y) dν(y)` of the error `Z = X - X̂(Y)`, when `(X, Y)` has
joint density `f`. -/
def errorPDF (ν : Measure β) (f : ℝ × β → ℝ) (g : β → ℝ) (z : ℝ) : ℝ := ∫ y, f (z + g y, y) ∂ν

/-- The joint density of `(X - X̂(Y), Y)`. -/
lemma IsPDF.shear [SFinite ν] {f : ℝ × β → ℝ} (hf : IsPDF (volume.prod ν) f) {g : β → ℝ}
    (hg : Measurable g) : IsPDF (volume.prod ν) (f ∘ shearEquiv hg) :=
  ⟨hf.measurable.comp (shearEquiv hg).measurable, fun _ => hf.nonneg _,
    (measurePreserving_shearEquiv hg).integrable_comp_of_integrable hf.integrable,
    by rw [← hf.integral_eq_one]; exact (measurePreserving_shearEquiv hg).integral_comp' f⟩

lemma marginalSnd_shear (f : ℝ × β → ℝ) {g : β → ℝ} (hg : Measurable g) :
    marginalSnd volume (f ∘ shearEquiv hg) = marginalSnd volume f := by
  funext y
  exact integral_add_right_eq_self (fun x => f (x, y)) (g y)

lemma marginalFst_shear (f : ℝ × β → ℝ) {g : β → ℝ} (hg : Measurable g) :
    marginalFst ν (f ∘ shearEquiv hg) = errorPDF ν f g := rfl

/-- Shifting `X` by a function of `Y` does not change the conditional differential entropy:
`h(X - X̂(Y) | Y) = h(X|Y)`. -/
theorem condDiffEntropy_shear [SFinite ν] (f : ℝ × β → ℝ) {g : β → ℝ} (hg : Measurable g) :
    condDiffEntropy volume ν (f ∘ shearEquiv hg) = condDiffEntropy volume ν f := by
  rw [condDiffEntropy, condDiffEntropy, marginalSnd_shear]
  congr 1
  exact (measurePreserving_shearEquiv hg).integral_comp'
    fun z => f z * log (f z / marginalSnd volume f z.2)

/-- **Corollary of Theorem 8.6.6 (Estimation error with side information).** For an estimator
`X̂(Y)` of `X` from side information `Y`, `E(X - X̂(Y))² ≥ e^{2h(X|Y)}/(2πe)`, with `h(X|Y)` in
nats. The differential entropies of `(X, Y)`, `Y` and the error `X - X̂(Y)` are assumed finite. -/
theorem exp_two_mul_condDiffEntropy_div_le [SigmaFinite ν] {f : ℝ × β → ℝ}
    (hf : IsPDF (volume.prod ν) f) {g : β → ℝ} (hg : Measurable g)
    (hXY : Integrable (fun z => negMulLog (f z)) (volume.prod ν))
    (hY : Integrable (fun y => negMulLog (marginalSnd volume f y)) ν)
    (hZ : Integrable fun z => negMulLog (errorPDF ν f g z))
    (h2 : Integrable (fun z => f z * (z.1 - g z.2) ^ 2) (volume.prod ν)) :
    exp (2 * condDiffEntropy volume ν f) / (2 * π * exp 1) ≤
      ∫ z, f z * (z.1 - g z.2) ^ 2 ∂(volume.prod ν) := by
  have hT := measurePreserving_shearEquiv (ν := ν) hg
  have hf' := hf.shear hg
  -- the second moment of the error
  have hcomp : (fun z => f z * (z.1 - g z.2) ^ 2) ∘ shearEquiv hg =
      fun z => (f ∘ shearEquiv hg) z * (z.1 - 0) ^ 2 := by
    funext z
    simp
  have h2' : Integrable (fun z => (f ∘ shearEquiv hg) z * (z.1 - 0) ^ 2) (volume.prod ν) :=
    hcomp ▸ hT.integrable_comp_of_integrable h2
  have hmom : Integrable fun z => errorPDF ν f g z * (z - 0) ^ 2 := by
    refine h2'.integral_prod_left.congr (Eventually.of_forall fun z => ?_)
    change ∫ y, f (z + g y, y) * (z - 0) ^ 2 ∂ν = (∫ y, f (z + g y, y) ∂ν) * (z - 0) ^ 2
    exact integral_mul_const _ _
  have hE : ∫ z, f z * (z.1 - g z.2) ^ 2 ∂(volume.prod ν) =
      ∫ z, errorPDF ν f g z * (z - 0) ^ 2 := by
    rw [← hT.integral_comp' (fun z => f z * (z.1 - g z.2) ^ 2)]
    have := (integral_mul_comp_fst hf' (G := fun z => (z - 0) ^ 2)
      ((measurable_id.sub_const 0).pow_const 2) hmom).2
    rw [marginalFst_shear] at this
    rw [← this]
    exact congrArg (fun F => ∫ z, F z ∂(volume.prod ν)) hcomp
  -- `h(X|Y) = h(Z|Y) ≤ h(Z)`
  have hXY' : Integrable (fun z => negMulLog ((f ∘ shearEquiv hg) z)) (volume.prod ν) :=
    hT.integrable_comp_of_integrable hXY
  have hle := condDiffEntropy_le hf' hXY' (by rwa [marginalFst_shear])
    (by rwa [marginalSnd_shear])
  rw [condDiffEntropy_shear, marginalFst_shear] at hle
  have hest := exp_two_mul_diffEntropy_div_le (hf'.marginalFst) hZ 0 hmom
  rw [hE]
  refine le_trans ?_ hest
  gcongr
  exact hle

end InfoTheory
