/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian

/-!
# Maximum entropy under partial covariance constraints

If only some of the second moments `E Xₐ X_b`, for `(a, b)` in a set `A`, are prescribed, the
maximum entropy density is the normal density `N(0, K)` whose covariance `K` matches the
constraints on `A` and whose inverse `K⁻¹` vanishes off `A` (Example 12.2.9). In the exponential
family form `f* = e^{λ₀ + ∑_{(a,b) ∈ A} λₐ_b xₐ x_b}` the multipliers are `λₐ_b = -½ (K⁻¹)ₐ_b`.

## Main statements

* `diffEntropy_le_of_partialCovariance`: **Example 12.2.9**, `h(g) ≤ ½ log ((2πe)ⁿ |K|)`.
* `diffEntropy_eq_of_partialCovariance_iff`: equality holds iff `g = N(0, K)`.

## Implementation notes

The book derives the maximizer from Theorem 12.1.1 with `rₐ_b(x) = xₐ x_b`. We argue directly with
the cross entropy: `-∫ g log N(0, K) = ½ log ((2π)ⁿ |K|) + ½ ∑ₐ_b (K⁻¹)ₐ_b E_g Xₐ X_b`, and only the
moments on `A` enter the sum. The constraints are on the second moments `E Xₐ X_b`, not on the
covariances, so `g` need not have mean zero.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Example 12.2.9
-/

open Real MeasureTheory Filter Matrix

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℝ}

/-- The cross entropy `-∫ g log N(0, K)` only depends on the moments `E_g Xₐ X_b` at the entries
where `K⁻¹` is nonzero. -/
lemma crossEntropy_mvGaussianPDF_of_partial (hK : K.PosDef) (A : ι → ι → Prop)
    (hA : ∀ a b, ¬A a b → K⁻¹ a b = 0) {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g)
    (hint : ∀ a b, Integrable fun x => g x * (x a * x b))
    (hcov : ∀ a b, A a b → ∫ x, g x * (x a * x b) = K a b) :
    Integrable (fun x => g x * log (mvGaussianPDF 0 K x)) ∧
      -∫ x, g x * log (mvGaussianPDF 0 K x) =
        1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) := by
  obtain ⟨h1, h2⟩ := crossEntropy_mvGaussianPDF hK.det_pos hg 0
    (fun a b => ∫ x, g x * (x a * x b)) (by simpa using hint) (by simp)
  refine ⟨h1, ?_⟩
  have hsum : ∑ a, ∑ b, K⁻¹ a b * (∫ x, g x * (x a * x b)) = ∑ a, ∑ b, K⁻¹ a b * K a b :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      by_cases hab : A a b
      · rw [hcov a b hab]
      · rw [hA a b hab, zero_mul, zero_mul]
  rw [h2, hsum, sum_inv_mul_self hK, log_two_pi_e_pow hK.det_pos]

/-- **Example 12.2.9.** Let `K` be positive definite with `(K⁻¹)ₐ_b = 0` for `(a, b) ∉ A`. Every
density `g` with the second moments `E_g Xₐ X_b = Kₐ_b` for `(a, b) ∈ A` has
`h(g) ≤ ½ log ((2πe)ⁿ |K|) = h(N(0, K))`. -/
theorem diffEntropy_le_of_partialCovariance (hK : K.PosDef) (A : ι → ι → Prop)
    (hA : ∀ a b, ¬A a b → K⁻¹ a b = 0) {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g)
    (hent : Integrable fun x => negMulLog (g x))
    (hint : ∀ a b, Integrable fun x => g x * (x a * x b))
    (hcov : ∀ a b, A a b → ∫ x, g x * (x a * x b) = K a b) :
    diffEntropy volume g ≤ 1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) := by
  obtain ⟨h1, h2⟩ := crossEntropy_mvGaussianPDF_of_partial hK A hA hg hint hcov
  rw [← h2]
  exact diffEntropy_le_crossEntropy hg (mvGaussianPDF_isPDF hK 0)
    (Eventually.of_forall fun x hx => absurd hx (mvGaussianPDF_pos hK 0 x).ne') hent h1

/-- **Example 12.2.9 (equality case).** Equality holds iff `g = N(0, K)` almost everywhere. -/
theorem diffEntropy_eq_of_partialCovariance_iff (hK : K.PosDef) (A : ι → ι → Prop)
    (hA : ∀ a b, ¬A a b → K⁻¹ a b = 0) {g : (ι → ℝ) → ℝ} (hg : IsPDF volume g)
    (hent : Integrable fun x => negMulLog (g x))
    (hint : ∀ a b, Integrable fun x => g x * (x a * x b))
    (hcov : ∀ a b, A a b → ∫ x, g x * (x a * x b) = K a b) :
    diffEntropy volume g = 1 / 2 * log ((2 * π * exp 1) ^ Fintype.card ι * K.det) ↔
      g =ᵐ[volume] mvGaussianPDF 0 K := by
  obtain ⟨h1, h2⟩ := crossEntropy_mvGaussianPDF_of_partial hK A hA hg hint hcov
  rw [← h2]
  exact diffEntropy_eq_crossEntropy_iff hg (mvGaussianPDF_isPDF hK 0)
    (Eventually.of_forall fun x hx => absurd hx (mvGaussianPDF_pos hK 0 x).ne') hent h1

/-- The normal density `N(0, K)` meets the constraints: `E Xₐ X_b = Kₐ_b`. -/
lemma integral_mvGaussianPDF_zero_mul (hK : K.PosDef) (a b : ι) :
    Integrable (fun x => mvGaussianPDF 0 K x * (x a * x b)) ∧
      ∫ x, mvGaussianPDF 0 K x * (x a * x b) = K a b := by
  simpa using integral_mvGaussianPDF_mul hK 0 a b

end InfoTheory
