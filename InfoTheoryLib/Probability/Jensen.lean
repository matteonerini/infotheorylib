/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.FinitePMF

/-!
# Jensen's inequality for finite random variables

## Main statements

* `jensen`: if `f` is convex then `f(E X) ≤ E f(X)`.
* `jensen_eq_iff`: if `f` is strictly convex, equality holds iff `X` is almost surely constant.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.6.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Theorem 2.6.2 (Jensen's inequality).** If `f` is convex then `E f(X) ≥ f(E X)`. -/
theorem jensen {μ : Ω → ℝ} (hμ : IsPMF μ) {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {X : Ω → ℝ} (hX : ∀ ω, X ω ∈ s) : f (expect μ X) ≤ expect μ (f ∘ X) := by
  have := hf.map_sum_le (t := univ) (w := μ) (p := X) (fun i _ => hμ.nonneg i) hμ.sum_eq_one
    (fun i _ => hX i)
  simpa [expect, smul_eq_mul, mul_comm] using this

/-- **Theorem 2.6.2 (Jensen's inequality, equality case).** If `f` is strictly convex, then
equality `E f(X) = f(E X)` holds iff `X = E X` with probability `1`, i.e. `X` is constant. -/
theorem jensen_eq_iff {μ : Ω → ℝ} (hμ : IsPMF μ) {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) {X : Ω → ℝ} (hX : ∀ ω, X ω ∈ s) :
    expect μ (f ∘ X) = f (expect μ X) ↔ ∀ ω, μ ω ≠ 0 → X ω = expect μ X := by
  set t := univ.filter (fun ω => μ ω ≠ 0)
  have hw : ∀ i ∈ t, 0 < μ i := fun i hi =>
    lt_of_le_of_ne (hμ.nonneg i) (Ne.symm (mem_filter.1 hi).2)
  have h1 : ∑ i ∈ t, μ i = 1 := by rw [sum_filter_ne_zero, hμ.sum_eq_one]
  have hE : expect μ X = ∑ i ∈ t, μ i • X i := by
    rw [expect, sum_filter_of_ne (fun i _ h => left_ne_zero_of_smul h)]
    simp [smul_eq_mul, mul_comm]
  have hEf : expect μ (f ∘ X) = ∑ i ∈ t, μ i • f (X i) := by
    rw [expect, sum_filter_of_ne (fun i _ h => left_ne_zero_of_smul h)]
    simp [smul_eq_mul, mul_comm]
  have key := hf.map_sum_eq_iff hw h1 (fun i _ => hX i)
  rw [hE, hEf, eq_comm, key]
  constructor
  · intro h ω hω; exact h ω (mem_filter.2 ⟨mem_univ _, hω⟩)
  · intro h ω hω; exact h ω (mem_filter.1 hω).2

end InfoTheory
