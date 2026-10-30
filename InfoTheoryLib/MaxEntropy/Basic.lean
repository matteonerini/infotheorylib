/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.RelativeEntropy
public import InfoTheoryLib.Entropy.Collision
public import InfoTheoryLib.RelativeEntropy.InformationInequality

/-!
# Maximum entropy distributions

Among the densities `f` on a support set `S` with prescribed moments `∫_S f rᵢ = αᵢ`, the
differential entropy is maximized by the exponential family member
`f*(x) = e^{λ₀ + ∑ᵢ λᵢ rᵢ(x)}` that meets the constraints, and only by it: for every such `g`,
`h(g) = -D(g ‖ f*) - ∫ g log f* ≤ -∫ g log f* = -∫ f* log f* = h(f*)`. The same holds for pmfs on a
finite set.

## Main statements

* `diffEntropy_le_of_eq_exp`, `diffEntropy_eq_of_eq_exp_iff`: **Theorem 12.1.1**.
* `entropy_le_of_eq_exp`, `entropy_eq_of_eq_exp_iff`: Theorem 12.1.1 for discrete entropy.

## Implementation notes

The support set `S` is encoded in the reference measure: densities on `S` are densities with
respect to `μ = λ|_S` (or the counting measure on `S`). The moments are integrals with respect to
`μ`, and the integrability of `g rᵢ` and of `g log g` is assumed.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 12.1
-/

open Real MeasureTheory Filter Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι]

/-! ### Densities -/

section Densities

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For `f = e^{λ₀ + ∑ᵢ λᵢ rᵢ}` and a density `g` with integrable moments,
`∫ g log f = λ₀ + ∑ᵢ λᵢ ∫ g rᵢ` (12.9). -/
lemma integral_mul_log_eq_exp {f g : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ) (lam : ι → ℝ)
    (hform : ∀ x, f x = exp (lam₀ + ∑ i, lam i * r i x)) (hg : IsPDF μ g)
    (hgr : ∀ i, Integrable (fun x => g x * r i x) μ) :
    Integrable (fun x => g x * log (f x)) μ ∧
      ∫ x, g x * log (f x) ∂μ = lam₀ + ∑ i, lam i * ∫ x, g x * r i x ∂μ := by
  have e : (fun x => g x * log (f x)) = fun x => lam₀ * g x + ∑ i, lam i * (g x * r i x) := by
    funext x
    rw [hform, log_exp, mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun i _ => by ring
  have hsum : Integrable (fun x => ∑ i, lam i * (g x * r i x)) μ :=
    integrable_finsetSum _ fun i _ => (hgr i).const_mul _
  rw [e]
  refine ⟨(hg.integrable.const_mul _).add hsum, ?_⟩
  rw [integral_add (hg.integrable.const_mul _) hsum, integral_const_mul, hg.integral_eq_one,
    mul_one, integral_finsetSum _ fun i _ => (hgr i).const_mul _]
  simp_rw [integral_const_mul]

/-- **Theorem 12.1.1 (Maximum entropy distribution), (12.5)–(12.12).** Let
`f* = e^{λ₀ + ∑ᵢ λᵢ rᵢ}` be a density. Every density `g` with the same moments
`∫ g rᵢ = ∫ f* rᵢ` has `h(g) ≤ h(f*)`. -/
theorem diffEntropy_le_of_eq_exp {f g : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ) (lam : ι → ℝ)
    (hf : IsPDF μ f) (hform : ∀ x, f x = exp (lam₀ + ∑ i, lam i * r i x))
    (hfr : ∀ i, Integrable (fun x => f x * r i x) μ) (hg : IsPDF μ g)
    (hgr : ∀ i, Integrable (fun x => g x * r i x) μ)
    (hcon : ∀ i, ∫ x, g x * r i x ∂μ = ∫ x, f x * r i x ∂μ)
    (hent : Integrable (fun x => negMulLog (g x)) μ) :
    diffEntropy μ g ≤ diffEntropy μ f := by
  obtain ⟨hgi, hge⟩ := integral_mul_log_eq_exp r lam₀ lam hform hg hgr
  obtain ⟨-, hfe⟩ := integral_mul_log_eq_exp r lam₀ lam hform hf hfr
  have hf' : diffEntropy μ f = -∫ x, g x * log (f x) ∂μ := by
    rw [hge, diffEntropy]
    simp_rw [negMulLog, neg_mul, integral_neg, hfe, hcon]
  rw [hf']
  exact diffEntropy_le_crossEntropy hg hf
    (Eventually.of_forall fun x hx => absurd hx (by rw [hform]; exact (exp_pos _).ne')) hent hgi

/-- **Theorem 12.1.1 (uniqueness).** Equality `h(g) = h(f*)` holds iff `g = f*` almost
everywhere. -/
theorem diffEntropy_eq_of_eq_exp_iff {f g : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ) (lam : ι → ℝ)
    (hf : IsPDF μ f) (hform : ∀ x, f x = exp (lam₀ + ∑ i, lam i * r i x))
    (hfr : ∀ i, Integrable (fun x => f x * r i x) μ) (hg : IsPDF μ g)
    (hgr : ∀ i, Integrable (fun x => g x * r i x) μ)
    (hcon : ∀ i, ∫ x, g x * r i x ∂μ = ∫ x, f x * r i x ∂μ)
    (hent : Integrable (fun x => negMulLog (g x)) μ) :
    diffEntropy μ g = diffEntropy μ f ↔ g =ᵐ[μ] f := by
  obtain ⟨hgi, hge⟩ := integral_mul_log_eq_exp r lam₀ lam hform hg hgr
  obtain ⟨-, hfe⟩ := integral_mul_log_eq_exp r lam₀ lam hform hf hfr
  have hf' : diffEntropy μ f = -∫ x, g x * log (f x) ∂μ := by
    rw [hge, diffEntropy]
    simp_rw [negMulLog, neg_mul, integral_neg, hfe, hcon]
  rw [hf']
  exact diffEntropy_eq_crossEntropy_iff hg hf
    (Eventually.of_forall fun x hx => absurd hx (by rw [hform]; exact (exp_pos _).ne')) hent hgi

end Densities

/-! ### Probability mass functions -/

section Discrete

variable {α : Type*} [Fintype α]

/-- `∑ₓ p(x) log p*(x) = λ₀ + ∑ᵢ λᵢ ∑ₓ p(x) rᵢ(x)` for `p* = e^{λ₀ + ∑ᵢ λᵢ rᵢ}`. -/
lemma sum_mul_log_eq_exp {f p : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ) (lam : ι → ℝ)
    (hform : ∀ x, f x = exp (lam₀ + ∑ i, lam i * r i x)) (hp : IsPMF p) :
    ∑ x, p x * log (f x) = lam₀ + ∑ i, lam i * ∑ x, p x * r i x := by
  simp only [hform, log_exp, mul_add, sum_add_distrib, ← sum_mul, hp.sum_eq_one, one_mul,
    mul_sum]
  rw [sum_comm]
  congr 1
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => by ring

private lemma entropy_eq_sub_relEntropy {f p : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ) (lam : ι → ℝ)
    (hf : IsPMF f) (hform : ∀ x, f x = exp (lam₀ + ∑ i, lam i * r i x)) (hp : IsPMF p)
    (hcon : ∀ i, ∑ x, p x * r i x = ∑ x, f x * r i x) :
    entropy p = entropy f - relEntropyReal p f := by
  have hpos : ∀ x, f x ≠ 0 := fun x => by rw [hform]; exact (exp_pos _).ne'
  have h1 := neg_entropy_sub_relEntropyReal (p := p) (r := f) fun x h => absurd h (hpos x)
  have h2 := neg_entropy_sub_relEntropyReal (p := f) (r := f) fun x h => absurd h (hpos x)
  have hD : relEntropyReal f f = 0 :=
    sum_eq_zero fun x _ => by rw [div_self (hpos x), log_one, mul_zero]
  rw [sum_mul_log_eq_exp r lam₀ lam hform hp] at h1
  rw [sum_mul_log_eq_exp r lam₀ lam hform hf, hD] at h2
  simp only [hcon] at h1
  linarith

/-- **Theorem 12.1.1 for pmfs.** Let `p* = e^{λ₀ + ∑ᵢ λᵢ rᵢ}` be a pmf. Every pmf `p` with the same
moments `∑ p rᵢ = ∑ p* rᵢ` has `H(p) ≤ H(p*)`. -/
theorem entropy_le_of_eq_exp {f p : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ) (lam : ι → ℝ)
    (hf : IsPMF f) (hform : ∀ x, f x = exp (lam₀ + ∑ i, lam i * r i x)) (hp : IsPMF p)
    (hcon : ∀ i, ∑ x, p x * r i x = ∑ x, f x * r i x) : entropy p ≤ entropy f := by
  rw [entropy_eq_sub_relEntropy r lam₀ lam hf hform hp hcon]
  have := relEntropyReal_nonneg hp hf fun x h => absurd h (by rw [hform]; exact (exp_pos _).ne')
  linarith

/-- **Theorem 12.1.1 for pmfs (uniqueness).** `H(p) = H(p*)` iff `p = p*`. -/
theorem entropy_eq_of_eq_exp_iff {f p : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ) (lam : ι → ℝ)
    (hf : IsPMF f) (hform : ∀ x, f x = exp (lam₀ + ∑ i, lam i * r i x)) (hp : IsPMF p)
    (hcon : ∀ i, ∑ x, p x * r i x = ∑ x, f x * r i x) : entropy p = entropy f ↔ p = f := by
  rw [entropy_eq_sub_relEntropy r lam₀ lam hf hform hp hcon, sub_eq_self,
    relEntropyReal_eq_zero_iff hp hf fun x h => absurd h (by rw [hform]; exact (exp_pos _).ne')]

end Discrete

end InfoTheory
