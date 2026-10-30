/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Variance

/-!
# Independent and identically distributed sequences

If `X₁, …, Xₙ` are i.i.d. with law `p`, the sequence `(X₁, …, Xₙ)` has law
`p(x₁, …, xₙ) = ∏ᵢ p(xᵢ)` on `Fin n → α`. Statements about `n` i.i.d. random variables only
involve this law, so we work on the finite space `(Fin n → α, iidPMF p n)`, where `Xᵢ` is the
`i`-th coordinate. (The coordinates are indexed from `0`.)

## Main definitions

* `iidPMF p n`: the law `∏ᵢ p(xᵢ)` of `n` i.i.d. random variables with law `p`.
* `sampleMean x`: the sample mean `(1/n) ∑ᵢ xᵢ` of a finite family of real numbers.

## Main statements

* `expect_iidPMF_prod`: `E ∏ᵢ φᵢ(Xᵢ) = ∏ᵢ E φᵢ(X)`.
* `dist_iidPMF_apply`: each coordinate `Xᵢ` has law `p`.
* `expect_sampleMean`, `variance_sampleMean`: the sample mean `(1/n) ∑ᵢ f(Xᵢ)` has mean `E f(X)`
  and variance `Var f(X) / n`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Chapter 3
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- The law `p(x₁, …, xₙ) = ∏ᵢ p(xᵢ)` of `n` i.i.d. random variables with law `p`. -/
def iidPMF (p : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := ∏ i, p (x i)

omit [Fintype α] in
lemma iidPMF_apply (p : α → ℝ) {n : ℕ} (x : Fin n → α) : iidPMF p n x = ∏ i, p (x i) := rfl

omit [Fintype α] in
lemma iidPMF_nonneg {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) {n : ℕ} (x : Fin n → α) :
    0 ≤ iidPMF p n x :=
  prod_nonneg fun i _ => hp (x i)

/-- `∑_{x} p(x₁, …, xₙ) ∏ᵢ φᵢ(xᵢ) = ∏ᵢ ∑ₐ p(a) φᵢ(a)`. -/
lemma sum_iidPMF_mul_prod (p : α → ℝ) {n : ℕ} (φ : Fin n → α → ℝ) :
    ∑ x : Fin n → α, iidPMF p n x * ∏ i, φ i (x i) = ∏ i, ∑ a, p a * φ i a := by
  rw [Fintype.prod_sum]
  simp [iidPMF, prod_mul_distrib]

lemma iidPMF_isPMF {p : α → ℝ} (hp : IsPMF p) (n : ℕ) : IsPMF (iidPMF p n) := by
  refine ⟨iidPMF_nonneg hp.nonneg, ?_⟩
  have := sum_iidPMF_mul_prod p (fun (_ : Fin n) (_ : α) => (1 : ℝ))
  simpa [hp.sum_eq_one] using this

/-- Expectations of products factor: `E ∏ᵢ φᵢ(Xᵢ) = ∏ᵢ E φᵢ(X)`. -/
lemma expect_iidPMF_prod (p : α → ℝ) {n : ℕ} (φ : Fin n → α → ℝ) :
    expect (iidPMF p n) (fun x => ∏ i, φ i (x i)) = ∏ i, expect p (φ i) := by
  simp only [expect]
  simp_rw [mul_comm _ (iidPMF p n _), mul_comm (φ _ _) (p _)]
  exact sum_iidPMF_mul_prod p φ

/-- `E f(Xⱼ) = E f(X)`. -/
lemma expect_iidPMF_apply {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (f : α → ℝ) (j : Fin n) :
    expect (iidPMF p n) (fun x => f (x j)) = expect p f := by
  have h := expect_iidPMF_prod p (fun i a => if i = j then f a else 1)
  have e1 : ∀ x : Fin n → α, (∏ i, (fun i a => if i = j then f a else 1) i (x i)) = f (x j) :=
    fun x => by simp
  have e2 : ∀ i, expect p ((fun i a => if i = j then f a else 1) i) =
      if i = j then expect p f else 1 := fun i => by
    by_cases hi : i = j
    · simp [hi]
    · simp [hi, expect_const hp]
  simp only [e1] at h
  rw [h, Finset.prod_congr rfl fun i _ => e2 i]
  simp

/-- `E f(Xⱼ) g(Xₖ) = E f(X) E g(X)` for `j ≠ k`. -/
lemma expect_iidPMF_mul_apply {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (f g : α → ℝ) {j k : Fin n}
    (hjk : j ≠ k) :
    expect (iidPMF p n) (fun x => f (x j) * g (x k)) = expect p f * expect p g := by
  set φ : Fin n → α → ℝ := fun i a => (if i = j then f a else 1) * (if i = k then g a else 1)
  have h := expect_iidPMF_prod p φ
  have e1 : ∀ x : Fin n → α, (∏ i, φ i (x i)) = f (x j) * g (x k) := fun x => by
    simp only [φ]
    rw [prod_mul_distrib]
    simp
  have e2 : ∀ i, expect p (φ i) =
      (if i = j then expect p f else 1) * (if i = k then expect p g else 1) := fun i => by
    by_cases hi : i = j
    · subst hi; simp [φ, hjk]
    · by_cases hk : i = k
      · subst hk; simp [φ, hi]
      · simp [φ, hi, hk, expect_const hp]
  simp only [e1] at h
  rw [h, Finset.prod_congr rfl fun i _ => e2 i, prod_mul_distrib]
  simp

/-- Each coordinate `Xⱼ` of an i.i.d. sequence has law `p`. -/
lemma dist_iidPMF_apply {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (j : Fin n) :
    dist (iidPMF p n) (fun x => x j) = p := by
  classical
  funext a
  have h := expect_iidPMF_apply hp (fun b => if b = a then 1 else 0) j
  simp only [expect, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true] at h
  rw [← h, dist]

/-! ### The sample mean -/

/-- The sample mean `(1/n) ∑ᵢ xᵢ` of a family of real numbers indexed by a finite type of
size `n`. -/
def sampleMean {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := (∑ i, x i) / Fintype.card ι

/-- The decomposition `∑ (xᵢ - θ)² = ∑ (xᵢ - x̄)² + n (x̄ - θ)²`. -/
lemma sum_sq_sub_eq {ι : Type*} [Fintype ι] (hn : 0 < Fintype.card ι) (x : ι → ℝ) (θ : ℝ) :
    ∑ i, (x i - θ) ^ 2 =
      ∑ i, (x i - sampleMean x) ^ 2 + Fintype.card ι * (sampleMean x - θ) ^ 2 := by
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ∑ i, x i = Fintype.card ι * sampleMean x := by rw [sampleMean]; field_simp
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
    card_univ, nsmul_eq_mul, hs]
  ring

/-- `sampleMean (fun i => f (xᵢ)) - c = (1/n) ∑ᵢ (f(xᵢ) - c)` for `n > 0`. -/
lemma sampleMean_sub {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) (c : ℝ) :
    sampleMean y - c = (∑ i, (y i - c)) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sampleMean, Fintype.card_fin, sum_sub_distrib, sum_const, card_univ,
    nsmul_eq_mul]
  field_simp

/-- The sample mean `(1/n) ∑ᵢ f(Xᵢ)` of i.i.d. random variables has mean `E f(X)`. -/
lemma expect_sampleMean {p : α → ℝ} (hp : IsPMF p) (f : α → ℝ) {n : ℕ} (hn : 0 < n) :
    expect (iidPMF p n) (fun x => sampleMean fun i => f (x i)) = expect p f := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : (fun x : Fin n → α => sampleMean fun i => f (x i)) =
      fun x => (n : ℝ)⁻¹ * ∑ i, f (x i) := by
    funext x; rw [sampleMean, Fintype.card_fin, div_eq_inv_mul]
  rw [h, expect_const_mul, expect_sum]
  simp only [expect_iidPMF_apply hp, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The sample mean `(1/n) ∑ᵢ f(Xᵢ)` of i.i.d. random variables has variance `Var f(X) / n`. -/
lemma variance_sampleMean {p : α → ℝ} (hp : IsPMF p) (f : α → ℝ) {n : ℕ} (hn : 0 < n) :
    variance (iidPMF p n) (fun x => sampleMean fun i => f (x i)) = variance p f / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set m := expect p f
  set g : α → ℝ := fun a => f a - m
  have hg : expect p g = 0 := by
    simp only [g, expect_sub, expect_const hp, m, sub_self]
  have key : ∀ j k : Fin n, expect (iidPMF p n) (fun x => g (x j) * g (x k)) =
      if j = k then variance p f else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk
      have := expect_iidPMF_apply hp (fun a => g a * g a) j
      rw [this, variance]
      simp only [g, m, sq]
    · rw [expect_iidPMF_mul_apply hp g g hjk, hg, zero_mul]
  have hpt : ∀ x : Fin n → α, ((sampleMean fun i => f (x i)) - m) ^ 2 =
      (n : ℝ)⁻¹ ^ 2 * ∑ j, ∑ k, g (x j) * g (x k) := by
    intro x
    rw [sampleMean_sub hn, div_pow, sq (∑ i, _), sum_mul_sum]
    simp only [g]
    field_simp
  rw [variance, expect_sampleMean hp f hn, funext hpt, expect_const_mul, expect_sum]
  simp only [expect_sum, key, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

end InfoTheory
