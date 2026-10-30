/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.MatrixBlock
public import InfoTheoryLib.MaxEntropy.Covariance
public import Mathlib.Data.Nat.Dist

/-!
# Burg's maximum entropy theorem

Given the autocorrelations `R(0), …, R(p)`, the Gauss–Markov process
`Xᵢ = -∑ₖ aₖ Xᵢ₋ₖ + Zᵢ`, `Zᵢ` i.i.d. `N(0, σ²)`, whose parameters `a₁, …, a_p, σ²` solve the
Yule–Walker equations, has the largest entropy among all processes with
`E Xᵢ Xᵢ₊ₖ = R(k)` for `k = 0, …, p` (Theorem 12.6.1). Its entropy rate is `½ log 2πeσ²`.

We prove the finite-dimensional statement behind the theorem: for a segment of length `n = p + m`,
the density of the AR(p) process started from its stationary distribution maximizes `h(X₁, …, Xₙ)`
under the constraints, and `h = ½ log ((2πe)ⁿ |K_{p-1}| σ^{2m})`. Dividing by `n` and letting
`m → ∞` gives the entropy rate `½ log 2πeσ²`.

## Main definitions

* `toeplitzCov R n`: the Toeplitz matrix `(R(|i - j|))ᵢⱼ` of size `n`.
* `ywExt p R a`: the Yule–Walker extension of `R(0), …, R(p)`: `R(l) = -∑ₖ aₖ R(l - k)`, `l > p`.
* `arFilter m a`: the whitening filter `(L x)ᵢ = xᵢ + ∑ₖ aₖ xᵢ₋ₖ` (`xᵢ` for the first `p` samples).
* `arInnovCov p m R σ2`: the covariance `diag(K_{p-1}, σ² I)` of `L X`.
* `arCov m R a`: the covariance of `X₁, …, X_{p+m}` for the AR(p) process.
* `sampleAutocorr`, `arSpectrum`: the sample autocorrelation (12.35) and the maximum entropy
  spectrum (12.55).

## Main statements

* `arFilter_mul_arCov_mul_transpose`: under the Yule–Walker equations,
  `L K Lᵀ = diag(K_{p-1}, σ² I)`.
* `arCov_posDef`, `det_arCov`, `inv_arCov_eq_zero`: `K` is positive definite,
  `|K| = |K_{p-1}| σ^{2m}`, and `K⁻¹` is banded: `(K⁻¹)ᵢⱼ = 0` for `|i - j| > p`.
* `diffEntropy_le_burg`, `diffEntropy_eq_burg_iff`: **Theorem 12.6.1** for a segment of length `n`.
* `tendsto_diffEntropy_arCov`: **(12.50)–(12.51)**, the entropy rate is `½ log 2πeσ²`.
* `det_toeplitzCov_succ`: **(12.56)–(12.58)**, `σ² = |K_p| / |K_{p-1}|`.

## Implementation notes

The book bounds `h(X₁, …, Xₙ)` through the chain rule and the Markov property. We use instead that
`K⁻¹ = Lᵀ diag(K_{p-1}, σ² I)⁻¹ L` vanishes outside the band `|i - j| ≤ p`, where `K` already
matches the constraints, so Example 12.2.9 applies. The coefficient `a k` stands for the book's
`a_{k+1}`. The existence of a solution of the Yule–Walker equations with `K_{p-1}` positive
definite is assumed.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 12.4–12.6
-/

open Real MeasureTheory Filter Matrix Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Definitions -/

/-- The Toeplitz matrix `(R(|i - j|))ᵢⱼ` of size `n`, the covariance matrix `K(n)` of a stationary
process (12.39). -/
def toeplitzCov (R : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => R (Nat.dist i j)

/-- **The Yule–Walker extension.** `R(l)` for `l ≤ p`, and `R(l) = -∑ₖ aₖ R(l - k)` for `l > p`. -/
def ywExt (p : ℕ) (R : ℕ → ℝ) (a : Fin p → ℝ) : ℕ → ℝ
  | l => if _h : l ≤ p then R l else -∑ k : Fin p, a k * ywExt p R a (l - (k + 1))
decreasing_by omega

/-- **(12.35)** The sample autocorrelation `R̂(k) = 1/(n - k) ∑_{i=1}^{n-k} Xᵢ Xᵢ₊ₖ`. -/
def sampleAutocorr {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  1 / (n - k) * ∑ i : Fin n, if h : (i : ℕ) + k < n then x i * x ⟨i + k, h⟩ else 0

/-- **(12.55)** The spectrum `S(λ) = σ² / |1 + ∑ₖ aₖ e^{-ikλ}|²` of the AR(p) process. -/
def arSpectrum {p : ℕ} (σ2 : ℝ) (a : Fin p → ℝ) (t : ℝ) : ℝ :=
  σ2 / ‖1 + ∑ k : Fin p, (a k : ℂ) * Complex.exp (-((k + 1 : ℕ) * t : ℝ) * Complex.I)‖ ^ 2

variable {p : ℕ}

/-- The delay by `k + 1` steps, applied from time `p` on: `(Sₖ x)ᵢ = xᵢ₋ₖ₋₁` for `i ≥ p`. -/
def arShift (m : ℕ) (k : Fin p) : Matrix (Fin (p + m)) (Fin (p + m)) ℝ :=
  fun i j => if p ≤ (i : ℕ) ∧ (j : ℕ) + (k + 1) = i then 1 else 0

/-- The whitening filter `L = 1 + ∑ₖ aₖ Sₖ`: `(L x)ᵢ = xᵢ` for `i < p` and
`xᵢ + ∑ₖ aₖ xᵢ₋ₖ₋₁` for `i ≥ p`. For the AR(p) process, `(L X)ᵢ = Zᵢ` for `i ≥ p`. -/
def arFilter (m : ℕ) (a : Fin p → ℝ) : Matrix (Fin (p + m)) (Fin (p + m)) ℝ :=
  1 + ∑ k, a k • arShift m k

/-- The covariance `diag(K_{p-1}, σ² I)` of `L X = (X₁, …, X_p, Z_{p+1}, …, Z_{p+m})`. -/
def arInnovCov (p m : ℕ) (R : ℕ → ℝ) (σ2 : ℝ) : Matrix (Fin (p + m)) (Fin (p + m)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks (toeplitzCov R p) 0 0 (diagonal fun _ => σ2))

/-- The covariance matrix of `X₁, …, X_{p+m}` for the AR(p) process: the Toeplitz matrix of the
Yule–Walker extension. -/
def arCov (m : ℕ) (R : ℕ → ℝ) (a : Fin p → ℝ) : Matrix (Fin (p + m)) (Fin (p + m)) ℝ :=
  toeplitzCov (ywExt p R a) (p + m)

/-! ### The Yule–Walker extension -/

variable {R : ℕ → ℝ} {a : Fin p → ℝ} {σ2 : ℝ}

lemma ywExt_of_le {l : ℕ} (hl : l ≤ p) : ywExt p R a l = R l := by
  rw [ywExt, dite_eq_left hl]

lemma ywExt_of_lt {l : ℕ} (hl : p < l) :
    ywExt p R a l = -∑ k : Fin p, a k * ywExt p R a (l - (k + 1)) := by
  rw [ywExt, dite_eq_right (not_le.2 hl)]

/-- **(12.53)** The Yule–Walker equations at every lag `l ≥ 1`. -/
lemma ywExt_add_sum_eq_zero (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    {l : ℕ} (hl : 1 ≤ l) : ywExt p R a l + ∑ k, a k * ywExt p R a (Nat.dist l (k + 1)) = 0 := by
  rcases le_or_gt l p with hlp | hlp
  · rw [ywExt_of_le hlp, hyw l hl hlp, neg_add_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ywExt_of_le (by simp only [Nat.dist]; omega)]
  · rw [ywExt_of_lt hlp, neg_add_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    simp only [Nat.dist]
    omega

/-- **(12.52)** The Yule–Walker equation at lag `0`. -/
lemma ywExt_zero_add_sum (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2) :
    ywExt p R a 0 + ∑ k : Fin p, a k * ywExt p R a (Nat.dist 0 (k + 1)) = σ2 := by
  rw [ywExt_of_le (Nat.zero_le _), hyw0]
  have : ∀ k : Fin p, ywExt p R a (Nat.dist 0 (k + 1)) = R (k + 1) := fun k => by
    rw [ywExt_of_le (by simp only [Nat.dist]; omega)]
    congr 1
    simp only [Nat.dist]
    omega
  simp only [this]
  ring

/-! ### The whitening filter -/

variable {m : ℕ}

lemma arShift_mul_apply (k : Fin p) (M : Matrix (Fin (p + m)) (Fin (p + m)) ℝ)
    (i l : Fin (p + m)) :
    (arShift m k * M) i l = if p ≤ (i : ℕ) then M ⟨i - (k + 1), by omega⟩ l else 0 := by
  simp only [Matrix.mul_apply, arShift, ite_mul, one_mul, zero_mul]
  by_cases h : p ≤ (i : ℕ)
  · have e : ∀ j : Fin (p + m), (p ≤ (i : ℕ) ∧ (j : ℕ) + (k + 1) = i) ↔
        j = ⟨i - (k + 1), by omega⟩ := fun j => by
      simp only [Fin.ext_iff]
      omega
    rw [ite_eq_left h]
    simp_rw [e]
    rw [Finset.sum_ite_eq']
    exact ite_eq_left (Finset.mem_univ _)
  · simp [h]

lemma arFilter_mul_apply (M : Matrix (Fin (p + m)) (Fin (p + m)) ℝ) (i l : Fin (p + m)) :
    (arFilter m a * M) i l =
      M i l + if p ≤ (i : ℕ) then ∑ k : Fin p, a k * M ⟨i - (k + 1), by omega⟩ l else 0 := by
  simp only [arFilter, add_mul, one_mul, Finset.sum_mul, smul_mul, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, arShift_mul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma arFilter_apply (i j : Fin (p + m)) :
    arFilter m a i j = (if i = j then 1 else 0) +
      ∑ k : Fin p, a k * if p ≤ (i : ℕ) ∧ (j : ℕ) + (k + 1) = i then 1 else 0 := by
  simp only [arFilter, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, arShift,
    Matrix.one_apply, smul_eq_mul]

/-- The support of the filter: `L i j ≠ 0` only for `i - p ≤ j ≤ i`, and only for `j = i` among
the first `p` rows. -/
lemma arFilter_support {i j : Fin (p + m)} (h : arFilter m a i j ≠ 0) :
    (j : ℕ) ≤ i ∧ (i : ℕ) ≤ j + p ∧ ((i : ℕ) < p → i = j) := by
  by_cases hij : i = j
  · subst hij
    exact ⟨le_rfl, by omega, fun _ => rfl⟩
  by_contra hc
  refine h ?_
  rw [arFilter_apply, ite_eq_right hij, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [ite_eq_right, mul_zero]
  rintro ⟨h1, h2⟩
  exact hc ⟨by omega, by omega, fun h3 => by omega⟩

lemma arFilter_apply_self (i : Fin (p + m)) : arFilter m a i i = 1 := by
  rw [arFilter_apply, ite_eq_left rfl]
  simp

lemma arFilter_isLowerTriangular : (arFilter m a).IsLowerTriangular := by
  intro i j hij
  by_contra h
  have := arFilter_support h
  rw [OrderDual.toDual_lt_toDual] at hij
  exact absurd this.1 (not_le.2 hij)

lemma det_arFilter : (arFilter m a).det = 1 := by
  rw [det_of_isLowerTriangular _ arFilter_isLowerTriangular]
  simp [arFilter_apply_self]

lemma isUnit_det_arFilter : IsUnit (arFilter m a).det := by
  rw [det_arFilter]
  exact isUnit_one

/-! ### The innovation covariance -/

lemma arInnovCov_apply (i j : Fin (p + m)) :
    arInnovCov p m R σ2 i j =
      if (i : ℕ) < p ∧ (j : ℕ) < p then R (Nat.dist i j) else if i = j then σ2 else 0 := by
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [arInnovCov, toeplitzCov, diagonal_apply, Fin.ext_iff] <;> omega

lemma det_arInnovCov : (arInnovCov p m R σ2).det = (toeplitzCov R p).det * σ2 ^ m := by
  rw [arInnovCov, det_reindex_self, det_fromBlocks_zero₂₁, det_diagonal]
  simp

lemma arInnovCov_posDef (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) :
    (arInnovCov p m R σ2).PosDef :=
  (posDef_fromBlocks_zero hK (PosDef.diagonal fun _ => hσ)).submatrix
    finSumFinEquiv.symm.injective

/-- `diag(K_{p-1}, σ² I)⁻¹` is block diagonal. -/
lemma inv_arInnovCov_eq_zero (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) {i j : Fin (p + m)}
    (h : ¬((i : ℕ) < p ∧ (j : ℕ) < p)) (hij : i ≠ j) : (arInnovCov p m R σ2)⁻¹ i j = 0 := by
  have hD : IsUnit (diagonal fun _ : Fin m => σ2) :=
    (isUnit_iff_isUnit_det _).2 (by simp [hσ.ne'])
  rw [arInnovCov, inv_reindex, inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hK.isUnit hD),
    inv_diagonal]
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => exact absurd ⟨by simp, by simp⟩ h
    | right j => simp
  | right i =>
    induction j using Fin.addCases with
    | left j => simp
    | right j =>
      have hij' : i ≠ j := fun e => hij (by rw [e])
      simp [diagonal_apply_ne _ hij']

/-! ### The AR covariance -/

lemma arCov_apply (i j : Fin (p + m)) : arCov m R a i j = ywExt p R a (Nat.dist i j) := rfl

lemma arCov_transpose : (arCov m R a)ᵀ = arCov m R a := by
  ext i j
  simp [arCov, toeplitzCov, Nat.dist_comm]

/-- The innovations are uncorrelated with the past: `(L K)ᵢₗ = σ² δᵢₗ` for `p ≤ i` and `l ≤ i`. -/
lemma arFilter_mul_arCov_apply (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    {i l : Fin (p + m)} (hpi : p ≤ (i : ℕ)) (hli : (l : ℕ) ≤ i) :
    (arFilter m a * arCov m R a) i l = if l = i then σ2 else 0 := by
  rw [arFilter_mul_apply, ite_eq_left hpi]
  simp only [arCov_apply]
  have e : ∀ k : Fin p, Nat.dist (i - (k + 1)) l = Nat.dist (i - l) (k + 1) := fun k => by
    simp only [Nat.dist]
    omega
  have e' : Nat.dist i l = i - l := by
    simp only [Nat.dist]
    omega
  simp only [e, e']
  by_cases hil : l = i
  · subst hil
    rw [ite_eq_left rfl, Nat.sub_self]
    exact ywExt_zero_add_sum hyw0
  · rw [ite_eq_right hil]
    exact ywExt_add_sum_eq_zero hyw (by rw [Fin.ext_iff] at hil; omega)

/-- **The Yule–Walker equations, in matrix form.** If `a₁, …, a_p, σ²` solve the Yule–Walker
equations (12.52)–(12.53), the whitening filter turns the covariance `K` of the AR(p) process
into `L K Lᵀ = diag(K_{p-1}, σ² I)`. -/
theorem arFilter_mul_arCov_mul_transpose (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1))) :
    arFilter m a * arCov m R a * (arFilter m a)ᵀ = arInnovCov p m R σ2 := by
  have hsymm : (arFilter m a * arCov m R a * (arFilter m a)ᵀ)ᵀ =
      arFilter m a * arCov m R a * (arFilter m a)ᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, arCov_transpose, mul_assoc]
  have hlow : ∀ i j : Fin (p + m), p ≤ (i : ℕ) → (j : ℕ) ≤ i →
      (arFilter m a * arCov m R a * (arFilter m a)ᵀ) i j = if i = j then σ2 else 0 := by
    intro i j hpi hji
    rw [Matrix.mul_apply]
    simp only [transpose_apply]
    rw [Finset.sum_congr rfl fun l _ => (?_ : (arFilter m a * arCov m R a) i l * arFilter m a j l =
      (if l = i then σ2 else 0) * arFilter m a j l)]
    · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      by_cases hij : i = j
      · subst hij
        rw [arFilter_apply_self, mul_one, ite_eq_left rfl]
      · rw [ite_eq_right hij]
        by_contra hc
        have := arFilter_support (right_ne_zero_of_mul hc)
        exact hij (Fin.ext (by omega))
    · by_cases hL : arFilter m a j l = 0
      · rw [hL, mul_zero, mul_zero]
      · rw [arFilter_mul_arCov_apply hyw0 hyw hpi (by have := arFilter_support hL; omega)]
  ext i j
  rw [arInnovCov_apply]
  by_cases hij : (i : ℕ) < p ∧ (j : ℕ) < p
  · rw [ite_eq_left hij, Matrix.mul_apply]
    simp only [transpose_apply]
    have hL : ∀ l, arFilter m a j l = if j = l then 1 else 0 := fun l => by
      by_cases hjl : j = l
      · subst hjl
        rw [arFilter_apply_self, ite_eq_left rfl]
      · rw [ite_eq_right hjl]
        by_contra hc
        exact hjl ((arFilter_support hc).2.2 hij.2)
    simp only [hL, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [arFilter_mul_apply, ite_eq_right (not_le.2 hij.1), add_zero, arCov_apply,
      ywExt_of_le (by simp only [Nat.dist]; omega)]
  · rw [ite_eq_right hij]
    rcases le_total (j : ℕ) i with hji | hji
    · exact hlow i j (by omega) hji
    · rw [← hsymm, transpose_apply, hlow j i (by omega) hji]
      simp only [eq_comm]

lemma arCov_eq (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1))) :
    arCov m R a = (arFilter m a)⁻¹ * arInnovCov p m R σ2 * (arFilter m a)⁻¹ᵀ := by
  have hL := isUnit_det_arFilter (m := m) (a := a)
  have hLt : IsUnit (arFilter m a)ᵀ.det := by rwa [det_transpose]
  rw [← arFilter_mul_arCov_mul_transpose hyw0 hyw, transpose_nonsing_inv]
  simp only [← mul_assoc]
  rw [nonsing_inv_mul _ hL, one_mul, mul_assoc, mul_nonsing_inv _ hLt, mul_one]

/-- The covariance matrix of the AR(p) process is positive definite. -/
theorem arCov_posDef (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) : (arCov m R a).PosDef := by
  have hinj : Function.Injective (arFilter m a)⁻¹.vecMul :=
    vecMul_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2
      (isUnit_nonsing_inv_det _ isUnit_det_arFilter))
  have := (arInnovCov_posDef (m := m) hK hσ).mul_mul_conjTranspose_same hinj
  rwa [conjTranspose_eq_transpose_of_trivial, ← arCov_eq hyw0 hyw] at this

/-- `|K| = |K_{p-1}| σ^{2m}`. -/
theorem det_arCov (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1))) :
    (arCov m R a).det = (toeplitzCov R p).det * σ2 ^ m := by
  rw [arCov_eq hyw0 hyw, det_mul, det_mul, det_transpose, det_nonsing_inv, det_arFilter,
    det_arInnovCov]
  simp

/-- `K⁻¹ = Lᵀ diag(K_{p-1}, σ² I)⁻¹ L`. -/
lemma inv_arCov (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) :
    (arCov m R a)⁻¹ = (arFilter m a)ᵀ * (arInnovCov p m R σ2)⁻¹ * arFilter m a := by
  have hL := isUnit_det_arFilter (m := m) (a := a)
  have hLt : IsUnit (arFilter m a)ᵀ.det := by rwa [det_transpose]
  have hD : IsUnit (arInnovCov p m R σ2).det :=
    (arInnovCov_posDef (m := m) hK hσ).det_pos.ne'.isUnit
  refine inv_eq_left_inv ?_
  rw [arCov_eq hyw0 hyw]
  simp only [mul_assoc]
  rw [← mul_assoc (arFilter m a) (arFilter m a)⁻¹, mul_nonsing_inv _ hL, one_mul,
    ← mul_assoc (arInnovCov p m R σ2)⁻¹, nonsing_inv_mul _ hD, one_mul, transpose_nonsing_inv,
    mul_nonsing_inv _ hLt]

/-- **The inverse covariance of an AR(p) process is banded:** `(K⁻¹)ᵢⱼ = 0` for `|i - j| > p`. -/
theorem inv_arCov_eq_zero (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) {i j : Fin (p + m)}
    (hij : p < Nat.dist i j) : (arCov m R a)⁻¹ i j = 0 := by
  rw [inv_arCov hyw0 hyw hK hσ, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [transpose_apply]
  by_cases h1 : arFilter m a k i = 0
  · rw [h1, zero_mul, zero_mul]
  by_cases h2 : arFilter m a l j = 0
  · rw [h2, mul_zero]
  by_cases h3 : (arInnovCov p m R σ2)⁻¹ k l = 0
  · rw [h3, mul_zero, zero_mul]
  exfalso
  have hk := arFilter_support h1
  have hl := arFilter_support h2
  simp only [Nat.dist] at hij
  by_cases hkl : (k : ℕ) < p ∧ (l : ℕ) < p
  · have e1 := congrArg Fin.val (hk.2.2 hkl.1)
    have e2 := congrArg Fin.val (hl.2.2 hkl.2)
    omega
  · have e := congrArg Fin.val (not_not.1 fun h => h3 (inv_arInnovCov_eq_zero hK hσ hkl h))
    omega

/-! ### Burg's theorem -/

/-- **Theorem 12.6.1 (Burg's maximum entropy theorem), (12.44)–(12.49).** Let `a₁, …, a_p, σ²`
solve the Yule–Walker equations for `R(0), …, R(p)`, with `K_{p-1} = (R(|i - j|))` positive
definite. Every density `g` of `X₁, …, Xₙ`, `n = p + m`, with `E Xᵢ Xⱼ = R(|i - j|)` for
`|i - j| ≤ p` has `h(g) ≤ ½ log ((2πe)ⁿ |K_{p-1}| σ^{2m})`, the entropy of the AR(p) process.
The process need not be zero mean, Gaussian or stationary. -/
theorem diffEntropy_le_burg (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) {g : (Fin (p + m) → ℝ) → ℝ}
    (hg : IsPDF volume g) (hent : Integrable fun x => negMulLog (g x))
    (hint : ∀ i j, Integrable fun x => g x * (x i * x j))
    (hcon : ∀ i j : Fin (p + m), Nat.dist i j ≤ p → ∫ x, g x * (x i * x j) = R (Nat.dist i j)) :
    diffEntropy volume g ≤
      1 / 2 * log ((2 * π * exp 1) ^ (p + m) * ((toeplitzCov R p).det * σ2 ^ m)) := by
  have h := diffEntropy_le_of_partialCovariance (arCov_posDef hyw0 hyw hK hσ)
    (fun i j => Nat.dist i j ≤ p) (fun i j h => inv_arCov_eq_zero hyw0 hyw hK hσ (not_le.1 h))
    hg hent hint fun i j h => by rw [hcon i j h, arCov_apply, ywExt_of_le h]
  rwa [Fintype.card_fin, det_arCov hyw0 hyw] at h

/-- **Theorem 12.6.1 (equality case).** The bound is attained only by the normal density
`N(0, K)` of the AR(p) process. -/
theorem diffEntropy_eq_burg_iff (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) {g : (Fin (p + m) → ℝ) → ℝ}
    (hg : IsPDF volume g) (hent : Integrable fun x => negMulLog (g x))
    (hint : ∀ i j, Integrable fun x => g x * (x i * x j))
    (hcon : ∀ i j : Fin (p + m), Nat.dist i j ≤ p → ∫ x, g x * (x i * x j) = R (Nat.dist i j)) :
    diffEntropy volume g =
        1 / 2 * log ((2 * π * exp 1) ^ (p + m) * ((toeplitzCov R p).det * σ2 ^ m)) ↔
      g =ᵐ[volume] mvGaussianPDF 0 (arCov m R a) := by
  have h := diffEntropy_eq_of_partialCovariance_iff (arCov_posDef hyw0 hyw hK hσ)
    (fun i j => Nat.dist i j ≤ p) (fun i j h => inv_arCov_eq_zero hyw0 hyw hK hσ (not_le.1 h))
    hg hent hint fun i j h => by rw [hcon i j h, arCov_apply, ywExt_of_le h]
  rwa [Fintype.card_fin, det_arCov hyw0 hyw] at h

/-- The AR(p) process meets the constraints: `E Xᵢ Xⱼ = R(|i - j|)` for `|i - j| ≤ p`. -/
lemma integral_mvGaussianPDF_arCov_mul (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) {i j : Fin (p + m)} (hij : Nat.dist i j ≤ p) :
    ∫ x, mvGaussianPDF 0 (arCov m R a) x * (x i * x j) = R (Nat.dist i j) := by
  rw [(integral_mvGaussianPDF_zero_mul (arCov_posDef hyw0 hyw hK hσ) i j).2, arCov_apply,
    ywExt_of_le hij]

/-- The entropy of `X₁, …, X_{p+m}` for the AR(p) process. -/
theorem diffEntropy_arCov (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1)))
    (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) :
    diffEntropy volume (mvGaussianPDF 0 (arCov m R a)) =
      1 / 2 * log ((2 * π * exp 1) ^ (p + m) * ((toeplitzCov R p).det * σ2 ^ m)) := by
  rw [diffEntropy_mvGaussianPDF (arCov_posDef hyw0 hyw hK hσ), Fintype.card_fin,
    det_arCov hyw0 hyw]

/-- **(12.50)–(12.51)** The entropy rate of the AR(p) process is `h* = ½ log 2πeσ²`:
`h(X₁, …, Xₙ) / n → ½ log 2πeσ²`. -/
theorem tendsto_diffEntropy_arCov (hK : (toeplitzCov R p).PosDef) (hσ : 0 < σ2) :
    Tendsto (fun m : ℕ =>
        1 / 2 * log ((2 * π * exp 1) ^ (p + m) * ((toeplitzCov R p).det * σ2 ^ m)) / (p + m))
      atTop (𝓝 (1 / 2 * log (2 * π * exp 1 * σ2))) := by
  set d := (toeplitzCov R p).det
  have hd : 0 < d := hK.det_pos
  set c := (log d - p * log σ2) / 2
  have hlim : Tendsto (fun m : ℕ => c / ((p : ℝ) + m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have h2 := (tendsto_const_nhds (x := 1 / 2 * log (2 * π * exp 1 * σ2))).add hlim
  rw [add_zero] at h2
  refine h2.congr' ((eventually_ge_atTop 1).mono fun m hm => ?_)
  have hpm : (0 : ℝ) < p + m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  have h2πe : 0 < 2 * π * exp 1 := by positivity
  dsimp only
  rw [log_mul (x := (2 * π * exp 1) ^ (p + m)) (by positivity) (by positivity),
    log_mul hd.ne' (by positivity), log_pow, log_pow, log_mul h2πe.ne' hσ.ne']
  push_cast
  field_simp
  ring

/-- **(12.56)–(12.58)** `|K_p| = |K_{p-1}| σ²`, so the entropy rate is
`h* = ½ log (2πe |K_p| / |K_{p-1}|)`. -/
theorem det_toeplitzCov_succ (hyw0 : R 0 = -∑ k : Fin p, a k * R (k + 1) + σ2)
    (hyw : ∀ l, 1 ≤ l → l ≤ p → R l = -∑ k, a k * R (Nat.dist l (k + 1))) :
    (toeplitzCov R (p + 1)).det = (toeplitzCov R p).det * σ2 := by
  have e : toeplitzCov R (p + 1) = arCov 1 R a := by
    ext i j
    rw [arCov_apply, ywExt_of_le (by simp only [Nat.dist]; omega)]
    rfl
  rw [e, det_arCov hyw0 hyw, pow_one]

end InfoTheory
