/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib

/-!
# Rational power series

The rational power series over a commutative ring `R` are the power series `p / (1 + X q)` with
`p` and `q` polynomials. They form a subring of `R⟦X⟧`, the ring `R⟨z⟩` of Section 20.2 of Yeung,
and over a field the inverse of a rational power series is rational.

## Main definitions

* `ratPowerSeries R`: the subring of the rational power series.

## Main statements

* `inv_mem_ratPowerSeries`: over a field, the inverse of a rational power series is rational.
* `isUnit_det_one_sub_X_smul`: `1 - X K` is invertible for every square matrix `K` of power series.
* `mem_ratPowerSeries_of_X_pow_mul`: a power series is rational if its product by `X ^ n` is.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 20.2
-/

open PowerSeries
open scoped Polynomial

@[expose] public noncomputable section

namespace InfoTheory

variable (R : Type*) [CommRing R]

/-- The **rational power series** over `R`: the power series `f` with `(1 + X q) f = p` for some
polynomials `p` and `q`, that is, `f = p / (1 + X q)`. -/
def ratPowerSeries : Subring R⟦X⟧ where
  carrier := {f | ∃ p q : R[X], (1 + X * (q : R⟦X⟧)) * f = (p : R⟦X⟧)}
  mul_mem' := by
    rintro f g ⟨p, q, hf⟩ ⟨p', q', hg⟩
    refine ⟨p * p', q + q' + Polynomial.X * q * q', ?_⟩
    push_cast
    linear_combination g * (1 + X * (q' : R⟦X⟧)) * hf + (p : R⟦X⟧) * hg
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro f g ⟨p, q, hf⟩ ⟨p', q', hg⟩
    refine ⟨p * (1 + Polynomial.X * q') + p' * (1 + Polynomial.X * q),
      q + q' + Polynomial.X * q * q', ?_⟩
    push_cast
    linear_combination (1 + X * (q' : R⟦X⟧)) * hf + (1 + X * (q : R⟦X⟧)) * hg
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro f ⟨p, q, hf⟩
    exact ⟨-p, q, by push_cast; linear_combination -hf⟩

variable {R}

lemma mem_ratPowerSeries {f : R⟦X⟧} :
    f ∈ ratPowerSeries R ↔ ∃ p q : R[X], (1 + X * (q : R⟦X⟧)) * f = (p : R⟦X⟧) :=
  Iff.rfl

/-- Polynomials are rational power series. -/
lemma coe_mem_ratPowerSeries (p : R[X]) : (p : R⟦X⟧) ∈ ratPowerSeries R :=
  ⟨p, 0, by simp⟩

lemma X_mem_ratPowerSeries : (X : R⟦X⟧) ∈ ratPowerSeries R := by
  simpa using coe_mem_ratPowerSeries (Polynomial.X : R[X])

lemma C_mem_ratPowerSeries (a : R) : C a ∈ ratPowerSeries R := by
  simpa using coe_mem_ratPowerSeries (Polynomial.C a)

/-- A power series is rational if its product by `X ^ n` is. -/
lemma mem_ratPowerSeries_of_X_pow_mul {f : R⟦X⟧} (n : ℕ) (h : X ^ n * f ∈ ratPowerSeries R) :
    f ∈ ratPowerSeries R := by
  induction n generalizing f with
  | zero => simpa using h
  | succ n ih =>
    refine ih ?_
    obtain ⟨p, q, hf⟩ := h
    have hp : p.coeff 0 = 0 := by
      have := congrArg constantCoeff hf
      simp only [map_mul, map_add, map_one, constantCoeff_X, zero_mul, add_zero, one_mul,
        map_pow, zero_pow n.succ_ne_zero, Polynomial.constantCoeff_coe] at this
      exact this.symm
    refine ⟨p.divX, q, X_mul_cancel ?_⟩
    have hdiv : (p : R⟦X⟧) = X * (p.divX : R⟦X⟧) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p, hp]
      simp
    rw [← hdiv, ← hf]
    ring

/-- `1 - X K` is invertible for every square matrix `K` of power series, since the constant
coefficient of its determinant is `1`. -/
lemma isUnit_det_one_sub_X_smul {E : Type*} [Fintype E] [DecidableEq E] (K : Matrix E E R⟦X⟧) :
    IsUnit (1 - (X : R⟦X⟧) • K).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff : R⟦X⟧ →+* R).mapMatrix (1 - (X : R⟦X⟧) • K) = (1 : Matrix E E R) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this, Matrix.det_one]
  exact isUnit_one

variable {k : Type*} [Field k]

/-- Over a field, the inverse of a rational power series is rational: `(p / (1 + X q))⁻¹` is
`(1 + X q) / p`, and `p = c (1 + X q')` when its constant coefficient `c` is not zero. -/
lemma inv_mem_ratPowerSeries {f : k⟦X⟧} (hf : f ∈ ratPowerSeries k) :
    f⁻¹ ∈ ratPowerSeries k := by
  obtain ⟨p, q, hpq⟩ := hf
  have hc : constantCoeff f = p.coeff 0 := by
    have := congrArg constantCoeff hpq
    simpa using this
  by_cases h0 : p.coeff 0 = 0
  · rw [PowerSeries.inv_eq_zero.mpr (hc.trans h0)]
    exact (ratPowerSeries k).zero_mem
  set c := p.coeff 0
  refine ⟨Polynomial.C c⁻¹ * (1 + Polynomial.X * q), Polynomial.C c⁻¹ * p.divX, ?_⟩
  have hpoly : 1 + Polynomial.X * (Polynomial.C c⁻¹ * p.divX) = Polynomial.C c⁻¹ * p := by
    conv_rhs => rw [← Polynomial.X_mul_divX_add p]
    rw [mul_add, ← Polynomial.C_mul, inv_mul_cancel₀ h0, Polynomial.C_1]
    ring
  have hps : 1 + X * ((Polynomial.C c⁻¹ * p.divX : k[X]) : k⟦X⟧) = C c⁻¹ * (p : k⟦X⟧) := by
    have := congrArg (fun r : k[X] => (r : k⟦X⟧)) hpoly
    push_cast at this ⊢
    exact this
  have hff : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f (hc ▸ h0)
  rw [hps, ← hpq]
  push_cast
  linear_combination (C c⁻¹ * (1 + X * (q : k⟦X⟧))) * hff

/-- A rational power series with a nonzero constant coefficient is a unit of the ring of rational
power series. -/
lemma isUnit_ratPowerSeries {f : ratPowerSeries k} (hf : constantCoeff (f : k⟦X⟧) ≠ 0) :
    IsUnit f :=
  isUnit_iff_exists_inv.mpr
    ⟨⟨_, inv_mem_ratPowerSeries f.2⟩, Subtype.ext (PowerSeries.mul_inv_cancel _ hf)⟩

end InfoTheory
