/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian
public import InfoTheoryLib.ForMathlib.MatrixSVD
public import InfoTheoryLib.GaussianChannel.WaterFilling

/-!
# The Gaussian vector channel: the capacity formula

For the channel `Y = G X + Z` with `Z ∼ N(0, I)`, the rate of an input covariance matrix `K` is
`½ log |G K Gᵀ + I|`, and the capacity is the maximum of the rate subject to `tr K ≤ P`. This file
studies this maximum: the singular value decomposition reduces it to parallel channels with gains
`γⱼ`, and Hadamard's inequality and water-filling solve it. The coding theorem is in
`GaussianChannel.VectorCode`.

## Main definitions

* `gvRate G K`: `½ log |G K Gᵀ + I|`, in nats.
* `gvCapacity G P`: the supremum of `gvRate G K` over `K ≽ 0` with `tr K ≤ P`.

## Main statements

* `exists_reciprocal`: **the reciprocity lemma** of Lecture 10.
* `gvCapacity_transpose`: the channels `G` and `Gᵀ` have the same capacity.
* `gvRate_le_sum`, `gvRate_diagonal`: the rate in the basis of the singular vectors.
* `gvCapacity_eq_waterFill`: water-filling on the singular values, with the optimal `K`.
* `exists_mul_gvRate_eq`: a general noise covariance `K_Z ≻ 0` can be whitened.
* `log_det_le_of_kkt`: the KKT conditions are sufficient for optimality.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 10
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]

/-- **Lecture 10 of [elgamal2010], page 10-3.** The rate `½ log |G K Gᵀ + I|` of the input
covariance matrix `K` for the Gaussian vector channel `Y = G X + Z`, in nats. -/
def gvRate (G : Matrix r t ℝ) (K : Matrix t t ℝ) : ℝ := 1 / 2 * log (G * K * Gᵀ + 1).det

/-- **Theorem 1 of Lecture 10 of [elgamal2010].** The capacity formula
`max_{K ≽ 0, tr K ≤ P} ½ log |G K Gᵀ + I|`, in nats. -/
def gvCapacity (G : Matrix r t ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ K : Matrix t t ℝ, K.PosSemidef ∧ K.trace ≤ P ∧ gvRate G K = v}

/-! ### Helpers -/

omit [Fintype t] [DecidableEq t] in
/-- `|U N Uᵀ + I| = |N + I|` for an orthogonal `U`. -/
lemma det_orth_mul_mul_add_one {U N : Matrix r r ℝ} (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) :
    (U * N * Uᵀ + 1).det = (N + 1).det := by
  have h : U * N * Uᵀ + 1 = U * (N + 1) * Uᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU']
  have hd : U.det ^ 2 = 1 := by
    have := congrArg det hU
    rw [det_mul, det_transpose, det_one] at this
    rw [sq]
    exact this
  rw [h, det_mul_mul_transpose, hd, one_mul]

/-! ### The singular value decomposition of the channel -/

section SVD

variable {G : Matrix r t ℝ} {U : Matrix r r ℝ} {Ψ : Matrix t r ℝ} {γ : r → ℝ}

omit [DecidableEq t] in
/-- With `G = U D Ψᵀ`, `|G K Gᵀ + I| = |D Ψᵀ K Ψ D + I|`. -/
lemma det_eq_of_svd (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hG : G = U * diagonal γ * Ψᵀ)
    (K : Matrix t t ℝ) :
    (G * K * Gᵀ + 1).det = (diagonal γ * (Ψᵀ * K * Ψ) * diagonal γ + 1).det := by
  have e : G * K * Gᵀ = U * (diagonal γ * (Ψᵀ * K * Ψ) * diagonal γ) * Uᵀ := by
    rw [hG]
    simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  rw [e, det_orth_mul_mul_add_one hU hU']

/-- `s = 1` if `γ ≠ 0` and `s = 0` otherwise. -/
def svdSupport (γ : r → ℝ) : r → ℝ := fun k => if γ k = 0 then 0 else 1

omit [Fintype r] [DecidableEq r] in
lemma svdSupport_cases (γ : r → ℝ) (k : r) : svdSupport γ k = 0 ∨ svdSupport γ k = 1 := by
  simp only [svdSupport]
  split_ifs <;> simp

omit [Fintype r] [DecidableEq r] in
lemma mul_svdSupport (γ : r → ℝ) (k : r) : γ k * svdSupport γ k = γ k := by
  simp only [svdSupport]
  split_ifs with h <;> simp [h]

omit [DecidableEq t] in
/-- **Lecture 10, page 10-5.** Hadamard's inequality in the basis of the singular vectors: the rate
of `K` is at most that of independent inputs with the powers `pₖ = (Ψᵀ K Ψ)ₖₖ`. -/
theorem gvRate_le_sum (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hG : G = U * diagonal γ * Ψᵀ)
    {K : Matrix t t ℝ} (hK : K.PosSemidef) :
    gvRate G K ≤ ∑ k, 1 / 2 * log (1 + γ k ^ 2 * (Ψᵀ * K * Ψ) k k) := by
  have hM := posSemidef_transpose_mul_mul hK Ψ
  have hD := posSemidef_mul_mul_transpose hM (diagonal γ)
  rw [diagonal_transpose] at hD
  have hPD := posDef_add_one hD
  have hdiag : ∀ k, (diagonal γ * (Ψᵀ * K * Ψ) * diagonal γ + 1 : Matrix r r ℝ) k k =
      1 + γ k ^ 2 * (Ψᵀ * K * Ψ : Matrix r r ℝ) k k := fun k => by
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, one_apply_eq]
    ring
  have hle := det_le_prod_diag hPD
  simp only [hdiag] at hle
  have hpos : ∀ k, 0 < 1 + γ k ^ 2 * (Ψᵀ * K * Ψ) k k := fun k => by
    have := mul_nonneg (sq_nonneg (γ k)) (hM.diag_nonneg (i := k))
    linarith
  rw [gvRate, det_eq_of_svd hU hU' hG, ← mul_sum,
    ← log_prod fun k _ => (hpos k).ne']
  exact mul_le_mul_of_nonneg_left (log_le_log hPD.det_pos hle) (by norm_num)

omit [DecidableEq t] in
/-- **Lecture 10, page 10-5.** The rate of `K = Ψ diag(p) Ψᵀ` is `∑ₖ ½ log (1 + γₖ² pₖ)`. -/
theorem gvRate_diagonal (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hG : G = U * diagonal γ * Ψᵀ)
    (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ)) {p : r → ℝ} (hp : ∀ k, 0 ≤ p k) :
    gvRate G (Ψ * diagonal p * Ψᵀ) = ∑ k, 1 / 2 * log (1 + γ k ^ 2 * p k) := by
  have e : diagonal γ * (Ψᵀ * (Ψ * diagonal p * Ψᵀ) * Ψ) * diagonal γ =
      diagonal fun k => γ k ^ 2 * p k := by
    have h : Ψᵀ * (Ψ * diagonal p * Ψᵀ) * Ψ = diagonal (svdSupport γ) * diagonal p *
        diagonal (svdSupport γ) := by
      rw [← hΨ]
      simp only [Matrix.mul_assoc]
    rw [h]
    simp only [diagonal_mul_diagonal]
    congr 1
    funext k
    have h1 := mul_svdSupport γ k
    calc γ k * (svdSupport γ k * p k * svdSupport γ k) * γ k
        = (γ k * svdSupport γ k) * p k * (γ k * svdSupport γ k) := by ring
      _ = γ k ^ 2 * p k := by rw [h1]; ring
  have hone : (diagonal (fun k => γ k ^ 2 * p k) + 1 : Matrix r r ℝ) =
      diagonal fun k => 1 + γ k ^ 2 * p k := by
    rw [← diagonal_one, diagonal_add]
    congr 1
    funext k
    ring
  have hpos : ∀ k, 0 < 1 + γ k ^ 2 * p k := fun k => by
    have := mul_nonneg (sq_nonneg (γ k)) (hp k)
    linarith
  rw [gvRate, det_eq_of_svd hU hU' hG, e, hone, det_diagonal, log_prod fun k _ => (hpos k).ne',
    mul_sum]

omit [Fintype t] [DecidableEq t] in
lemma posSemidef_mul_diagonal_mul [Finite t] (Ψ : Matrix t r ℝ) {p : r → ℝ} (hp : ∀ k, 0 ≤ p k) :
    (Ψ * diagonal p * Ψᵀ).PosSemidef :=
  posSemidef_mul_mul_transpose (posSemidef_diagonal_iff.2 hp) Ψ

omit [DecidableEq t] in
lemma trace_mul_diagonal_mul (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ)) (p : r → ℝ) :
    (Ψ * diagonal p * Ψᵀ).trace = ∑ k, svdSupport γ k * p k := by
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hΨ, diagonal_mul_diagonal, trace_diagonal]
  exact sum_congr rfl fun k _ => mul_comm _ _

end SVD

/-! ### Reciprocity -/

/-- **The reciprocity lemma (Lecture 10 of [elgamal2010], page 10-9).** For a channel matrix `G` and
`K ≽ 0` there is `K̄ ≽ 0` with `tr K̄ ≤ tr K` and `|Gᵀ K̄ G + I| = |G K Gᵀ + I|`. -/
theorem exists_reciprocal (G : Matrix r t ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) :
    ∃ K' : Matrix r r ℝ, K'.PosSemidef ∧ K'.trace ≤ K.trace ∧
      (Gᵀ * K' * G + 1).det = (G * K * Gᵀ + 1).det := by
  obtain ⟨U, Ψ, γ, hU, hU', -, hG, hΨ⟩ := exists_svd G
  have hΨ' : Ψᵀ * Ψ = diagonal (svdSupport γ) := hΨ
  set M := Ψᵀ * K * Ψ with hMd
  have hM : M.PosSemidef := posSemidef_transpose_mul_mul hK Ψ
  refine ⟨U * M * Uᵀ, posSemidef_mul_mul_transpose hM U, ?_, ?_⟩
  · rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one]
    exact trace_transpose_mul_mul_le hΨ' (svdSupport_cases γ) hK
  · rw [det_eq_of_svd hU hU' hG K, ← hMd]
    have e : Gᵀ * (U * M * Uᵀ) * G = (Ψ * (diagonal γ * M * diagonal γ)) * Ψᵀ := by
      rw [hG]
      simp only [transpose_mul, transpose_transpose, diagonal_transpose]
      calc Ψ * (diagonal γ * Uᵀ) * (U * M * Uᵀ) * (U * diagonal γ * Ψᵀ)
          = Ψ * diagonal γ * (Uᵀ * U) * M * (Uᵀ * U) * diagonal γ * Ψᵀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hU]
            simp only [Matrix.mul_assoc, Matrix.one_mul]
    rw [e, det_mul_add_one_comm]
    have e2 : Ψᵀ * (Ψ * (diagonal γ * M * diagonal γ)) = diagonal γ * M * diagonal γ := by
      rw [← Matrix.mul_assoc, hΨ', ← Matrix.mul_assoc, ← Matrix.mul_assoc, diagonal_mul_diagonal]
      congr 3
      funext k
      rw [mul_comm]
      exact mul_svdSupport γ k
    rw [e2]

private lemma gvRate_image_subset (H : Matrix r t ℝ) (P : ℝ) :
    {v | ∃ K : Matrix t t ℝ, K.PosSemidef ∧ K.trace ≤ P ∧ gvRate H K = v} ⊆
      {v | ∃ K : Matrix r r ℝ, K.PosSemidef ∧ K.trace ≤ P ∧ gvRate Hᵀ K = v} := by
  rintro v ⟨K, hK, htr, rfl⟩
  obtain ⟨K', h1, h2, h3⟩ := exists_reciprocal H hK
  refine ⟨K', h1, h2.trans htr, ?_⟩
  rw [gvRate, gvRate, transpose_transpose, h3]

/-- **Lecture 10, page 10-9.** The channels `G` and `Gᵀ` have the same capacity. -/
theorem gvCapacity_transpose (G : Matrix r t ℝ) (P : ℝ) : gvCapacity Gᵀ P = gvCapacity G P := by
  rw [gvCapacity, gvCapacity]
  congr 1
  refine Set.Subset.antisymm ?_ (gvRate_image_subset G P)
  simpa [transpose_transpose] using gvRate_image_subset Gᵀ P

/-! ### Water-filling on the singular values -/

section WaterFilling

variable {G : Matrix r t ℝ} {U : Matrix r r ℝ} {Ψ : Matrix t r ℝ} {γ : r → ℝ}

/-- The noise levels `1/γₖ²` of the subchannels with `γₖ ≠ 0`. -/
def svdNoise (γ : r → ℝ) : {k // γ k ≠ 0} → ℝ := fun k => (γ k ^ 2)⁻¹

omit [Fintype r] [DecidableEq r] in
lemma svdNoise_pos (γ : r → ℝ) (k : {k // γ k ≠ 0}) : 0 < svdNoise γ k :=
  inv_pos.2 (pow_pos (lt_of_le_of_ne (abs_nonneg _) (abs_ne_zero.2 k.2).symm) 2 |>.trans_eq
    (sq_abs _))

omit [Fintype r] [DecidableEq r] in
lemma sum_subtype_of_zero [Fintype r] (γ : r → ℝ) {f : r → ℝ}
    (hf : ∀ k, γ k = 0 → f k = 0) : ∑ k, f k = ∑ k : {k // γ k ≠ 0}, f k := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun k => γ k ≠ 0) (s := univ) (f := f)
    fun k _ hk h => hk (hf k h)]
  exact Finset.sum_subtype _ (by simp) f

omit [DecidableEq t] in
/-- **Lecture 10, page 10-5.** Water-filling bound: if `tr K ≤ ∑ₖ (ν - 1/γₖ²)⁺`, the rate of `K` is
at most `∑ₖ ½ log (1 + γₖ² (ν - 1/γₖ²)⁺)`. -/
theorem gvRate_le_waterFill (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) (hG : G = U * diagonal γ * Ψᵀ)
    (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ)) {ν : ℝ} (hν : 0 < ν) {K : Matrix t t ℝ}
    (hK : K.PosSemidef) (htr : K.trace ≤ ∑ k, waterFill (svdNoise γ) ν k) :
    gvRate G K ≤ ∑ k, 1 / 2 * log (1 + waterFill (svdNoise γ) ν k / svdNoise γ k) := by
  have hM := posSemidef_transpose_mul_mul hK Ψ
  set p : r → ℝ := fun k => (Ψᵀ * K * Ψ : Matrix r r ℝ) k k with hp
  have hp0 : ∀ k, 0 ≤ p k := fun k => hM.diag_nonneg
  have hS : ∑ k : {k // γ k ≠ 0}, p k ≤ K.trace := by
    refine le_trans ?_ (trace_transpose_mul_mul_le hΨ (svdSupport_cases γ) hK)
    rw [trace]
    simp only [diag_apply]
    classical
    have := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset (fun k => γ k ≠ 0) univ)
      (f := p) fun k _ _ => hp0 k
    refine le_trans (le_of_eq ?_) this
    exact (Finset.sum_subtype _ (by simp) p).symm
  have h1 := gvRate_le_sum hU hU' hG hK
  rw [sum_subtype_of_zero γ (fun k hk => by simp [hk])] at h1
  have h2 := sum_log_le_waterFill (svdNoise_pos γ) hν (P := fun k => p k) (fun k => hp0 k)
    (hS.trans htr)
  have e : ∀ k : {k // γ k ≠ 0}, p k / svdNoise γ k = γ k ^ 2 * p k := fun k => by
    rw [svdNoise, div_inv_eq_mul, mul_comm]
  simp only [e] at h2
  rw [← mul_sum]
  rw [← mul_sum] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))

omit [DecidableEq t] in
/-- **Lecture 10, page 10-5.** The bound is attained by `K* = Ψ diag((ν - 1/γₖ²)⁺) Ψᵀ`. -/
theorem exists_gvRate_waterFill (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hG : G = U * diagonal γ * Ψᵀ) (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ)) (ν : ℝ) :
    ∃ K : Matrix t t ℝ, K.PosSemidef ∧ K.trace = ∑ k, waterFill (svdNoise γ) ν k ∧
      gvRate G K = ∑ k, 1 / 2 * log (1 + waterFill (svdNoise γ) ν k / svdNoise γ k) := by
  classical
  set p : r → ℝ := fun k => if h : γ k ≠ 0 then waterFill (svdNoise γ) ν ⟨k, h⟩ else 0 with hpd
  have hp : ∀ k, 0 ≤ p k := fun k => by
    simp only [hpd]
    split_ifs
    · exact waterFill_nonneg _ _ _
    · exact le_rfl
  have hpv : ∀ k : {k // γ k ≠ 0}, p k = waterFill (svdNoise γ) ν k := fun k => by
    simp [hpd, k.2]
  refine ⟨Ψ * diagonal p * Ψᵀ, posSemidef_mul_diagonal_mul Ψ hp, ?_, ?_⟩
  · rw [trace_mul_diagonal_mul hΨ, sum_subtype_of_zero γ (fun k hk => by simp [svdSupport, hk])]
    refine sum_congr rfl fun k _ => ?_
    simp [svdSupport, k.2, hpv]
  · rw [gvRate_diagonal hU hU' hG hΨ hp, sum_subtype_of_zero γ (fun k hk => by simp [hk])]
    refine sum_congr rfl fun k _ => ?_
    rw [hpv, svdNoise, div_inv_eq_mul, mul_comm (γ _ ^ 2)]

omit [DecidableEq t] in
/-- **Lecture 10, pages 10-4 and 10-5.** The capacity of the Gaussian vector channel by
water-filling on the singular values: `C = ∑ₖ ½ log (1 + γₖ² (ν - 1/γₖ²)⁺)` for the water level
`ν > 0` with
`∑ₖ (ν - 1/γₖ²)⁺ = P`. -/
theorem gvCapacity_eq_waterFill (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hG : G = U * diagonal γ * Ψᵀ) (hΨ : Ψᵀ * Ψ = diagonal (svdSupport γ)) {P ν : ℝ} (hν : 0 < ν)
    (hP : ∑ k, waterFill (svdNoise γ) ν k = P) :
    gvCapacity G P = ∑ k, 1 / 2 * log (1 + waterFill (svdNoise γ) ν k / svdNoise γ k) := by
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · obtain ⟨K, h1, h2, h3⟩ := exists_gvRate_waterFill hU hU' hG hΨ ν
    exact ⟨K, h1, h2.trans_le hP.le, h3⟩
  · rintro _ ⟨K, h1, h2, rfl⟩
    exact gvRate_le_waterFill hU hU' hG hΨ hν h1 (h2.trans hP.ge)

omit [DecidableEq t] in
/-- For `P ≥ 0`, the rates are bounded by those of the subchannels at full power, so that the
supremum in the capacity formula is meaningful. -/
theorem bddAbove_gvRate (G : Matrix r t ℝ) (P : ℝ) :
    BddAbove {v | ∃ K : Matrix t t ℝ, K.PosSemidef ∧ K.trace ≤ P ∧ gvRate G K = v} := by
  classical
  obtain ⟨U, Ψ, γ, hU, hU', -, hG, hΨ⟩ := exists_svd G
  refine ⟨∑ k, 1 / 2 * log (1 + γ k ^ 2 * P), ?_⟩
  rintro _ ⟨K, hK, htr, rfl⟩
  have hM := posSemidef_transpose_mul_mul hK Ψ
  refine (gvRate_le_sum hU hU' hG hK).trans (sum_le_sum fun k _ => ?_)
  have hk0 : 0 ≤ (Ψᵀ * K * Ψ : Matrix r r ℝ) k k := hM.diag_nonneg
  have hk : (Ψᵀ * K * Ψ : Matrix r r ℝ) k k ≤ P := by
    refine le_trans ?_ ((trace_transpose_mul_mul_le hΨ (svdSupport_cases γ) hK).trans htr)
    rw [trace]
    exact single_le_sum (f := fun k => (Ψᵀ * K * Ψ : Matrix r r ℝ).diag k)
      (fun i _ => hM.diag_nonneg) (mem_univ k)
  have h1 : 0 < 1 + γ k ^ 2 * (Ψᵀ * K * Ψ : Matrix r r ℝ) k k := by
    have := mul_nonneg (sq_nonneg (γ k)) hk0
    linarith
  have h2 := mul_le_mul_of_nonneg_left hk (sq_nonneg (γ k))
  exact mul_le_mul_of_nonneg_left (log_le_log h1 (by linarith)) (by norm_num)

omit [DecidableEq t] in
/-- `0 ≤ gvRate G K` for `K ≽ 0`. -/
lemma gvRate_nonneg (G : Matrix r t ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) : 0 ≤ gvRate G K := by
  have h := one_le_det_one_add (posSemidef_mul_mul_transpose hK G)
  rw [add_comm] at h
  exact mul_nonneg (by norm_num) (log_nonneg h)

omit [DecidableEq t] in
/-- A rate of an allowed covariance matrix is at most the capacity. -/
lemma gvRate_le_gvCapacity (G : Matrix r t ℝ) {P : ℝ} {K : Matrix t t ℝ} (hK : K.PosSemidef)
    (htr : K.trace ≤ P) : gvRate G K ≤ gvCapacity G P :=
  le_csSup (bddAbove_gvRate G P) ⟨K, hK, htr, rfl⟩

end WaterFilling

/-! ### General noise covariance -/

omit [DecidableEq t] in
/-- **Remark (Lecture 10), page 10-3.** A noise covariance `K_Z ≻ 0` can be whitened: there is an
invertible `S`, namely `S = K_Z^{-1/2}` up to an orthogonal matrix, with
`|G K Gᵀ + K_Z| / |K_Z| = |(S G) K (S G)ᵀ + I|`, for all `K`. -/
theorem exists_mul_gvRate_eq {KZ : Matrix r r ℝ} (hZ : KZ.PosDef) (G : Matrix r t ℝ) :
    ∃ S : Matrix r r ℝ, IsUnit S.det ∧ ∀ K : Matrix t t ℝ,
      1 / 2 * log ((G * K * Gᵀ + KZ).det / KZ.det) = gvRate (S * G) K := by
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hZ
  have hdet := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at hdet
  have hS0 : S.det ≠ 0 := fun h => by simp [h] at hdet
  refine ⟨S, isUnit_iff_ne_zero.2 hS0, fun K => ?_⟩
  rw [gvRate]
  congr 2
  have e : S * G * K * (S * G)ᵀ + 1 = S * (G * K * Gᵀ + KZ) * Sᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, hS]
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [e, det_mul_mul_transpose, div_eq_inv_mul]
  congr 1
  exact (eq_inv_of_mul_eq_one_left hdet).symm

/-! ### The KKT conditions -/

section KKT

/-- `log |A + Δ| - log |A| ≤ tr(A⁻¹ Δ)`: the tangent bound in terms of the difference. -/
lemma log_det_add_sub_le {n : Type*} [Fintype n] [DecidableEq n] {A Δ : Matrix n n ℝ}
    (hA : A.PosDef) (hB : (A + Δ).PosDef) : log (A + Δ).det - log A.det ≤ (A⁻¹ * Δ).trace := by
  have h := log_det_le_trace_sub_card hA hB
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA.det_pos.ne'
  rw [Matrix.mul_add, nonsing_inv_mul A hu, trace_add, trace_one] at h
  linarith

/-- **The KKT conditions (Lecture 10 of [elgamal2010], page 10-12), sufficiency.** If `K* ≽ 0`,
`Υ ≽ 0` and `λ ≥ 0` satisfy `½ Gᵀ (G K* Gᵀ + K_Z)⁻¹ G + Υ = λ I`, `λ (tr K* - P) = 0` and
`tr(Υ K*) = 0`, then `K*` maximizes `log |G K Gᵀ + K_Z|` subject to `K ≽ 0` and `tr K ≤ P`. -/
theorem log_det_le_of_kkt {KZ : Matrix r r ℝ} (hZ : KZ.PosDef) (G : Matrix r t ℝ)
    {Ks Υ : Matrix t t ℝ} (hs : Ks.PosSemidef) (hΥ : Υ.PosSemidef) {lam P : ℝ} (hl : 0 ≤ lam)
    (hst : (1 / 2 : ℝ) • (Gᵀ * (G * Ks * Gᵀ + KZ)⁻¹ * G) + Υ = lam • 1)
    (hc₁ : lam * (Ks.trace - P) = 0) (hc₂ : (Υ * Ks).trace = 0) {K : Matrix t t ℝ}
    (hK : K.PosSemidef) (hP : K.trace ≤ P) :
    log (G * K * Gᵀ + KZ).det ≤ log (G * Ks * Gᵀ + KZ).det := by
  set A := G * Ks * Gᵀ + KZ with hAd
  have hA : A.PosDef := Matrix.PosDef.posSemidef_add (posSemidef_mul_mul_transpose hs G) hZ
  have hB : (G * K * Gᵀ + KZ).PosDef :=
    Matrix.PosDef.posSemidef_add (posSemidef_mul_mul_transpose hK G) hZ
  have e : G * K * Gᵀ + KZ = A + G * (K - Ks) * Gᵀ := by
    rw [hAd, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e] at hB ⊢
  have h := log_det_add_sub_le hA hB
  have htr : (A⁻¹ * (G * (K - Ks) * Gᵀ)).trace = (Gᵀ * A⁻¹ * G * (K - Ks)).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hGA : Gᵀ * A⁻¹ * G = (2 : ℝ) • (lam • 1 - Υ) := by
    rw [← hst, add_sub_cancel_right, smul_smul]
    norm_num
  have e2 : (Gᵀ * A⁻¹ * G * (K - Ks)).trace =
      2 * (lam * (K.trace - Ks.trace) - (Υ * K).trace + (Υ * Ks).trace) := by
    rw [hGA, Matrix.smul_mul, trace_smul, Matrix.sub_mul, trace_sub, Matrix.smul_mul, trace_smul,
      Matrix.one_mul, Matrix.mul_sub, trace_sub, trace_sub, smul_eq_mul, smul_eq_mul]
    ring
  rw [htr, e2, hc₂] at h
  have h0 := trace_mul_nonneg_of_posSemidef hΥ hK
  have h1 : lam * (K.trace - P) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl (by linarith)
  have h2 : lam * Ks.trace = lam * P := by linarith
  nlinarith

end KKT

/-! ### Vector writing on dirty paper -/

section DirtyPaper

variable (G : Matrix r t ℝ) (K : Matrix t t ℝ)

/-- **Lecture 10 of [elgamal2010], page 10-34.** The MMSE gain
`A = K_X Gᵀ (G K_X Gᵀ + I)⁻¹` of the estimate of `X` from `G X + Z`. -/
def mmseGain : Matrix t r ℝ := K * Gᵀ * (G * K * Gᵀ + 1)⁻¹

variable {K}

omit [DecidableEq t] in
/-- **Lecture 10, page 10-35.** The estimation error `X - A (G X + Z)` is uncorrelated with
`G X + Z`: `K_X Gᵀ - A (G K_X Gᵀ + I) = 0`. -/
theorem mmseGain_orthogonal (hK : K.PosSemidef) :
    K * Gᵀ - mmseGain G K * (G * K * Gᵀ + 1) = 0 := by
  have hu : IsUnit (G * K * Gᵀ + 1).det :=
    isUnit_iff_ne_zero.2 (posDef_add_one (posSemidef_mul_mul_transpose hK G)).det_pos.ne'
  rw [mmseGain, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, sub_self]

/-- **Lecture 10, page 10-35.** The covariance `K_E = (I - A G) K_X` of the estimation error
satisfies `|K_E| |G K_X Gᵀ + I| = |K_X|`. For `K_X ≻ 0`, this says that the rate
`h(X) - h(X - A (G X + Z)) = ½ log (|K_X| / |K_E|)` of vector writing on dirty paper is
`½ log |G K_X Gᵀ + I|`, the rate without the interference. -/
theorem det_mmseError_mul (hK : K.PosSemidef) :
    (K - mmseGain G K * G * K).det * (G * K * Gᵀ + 1).det = K.det := by
  have hPD := posDef_add_one (posSemidef_mul_mul_transpose hK G)
  have hu : IsUnit (G * K * Gᵀ + 1).det := isUnit_iff_ne_zero.2 hPD.det_pos.ne'
  have hsw : (1 - mmseGain G K * G) * (K * Gᵀ * G + 1) = 1 := by
    -- Push-through: `A (G K Gᵀ + 1) = K Gᵀ`.
    have hA : mmseGain G K * (G * K * Gᵀ + 1) = K * Gᵀ := by
      rw [mmseGain, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
    have hA' : mmseGain G K * G * (K * Gᵀ * G + 1) = K * Gᵀ * G := by
      calc mmseGain G K * G * (K * Gᵀ * G + 1)
          = mmseGain G K * (G * K * Gᵀ + 1) * G := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
        _ = K * Gᵀ * G := by rw [hA]
    rw [Matrix.sub_mul, Matrix.one_mul, hA']
    abel
  have hdet := congrArg det hsw
  rw [det_mul, det_one] at hdet
  have hsyl : (K * Gᵀ * G + 1).det = (G * K * Gᵀ + 1).det := by
    rw [det_mul_add_one_comm, Matrix.mul_assoc]
  rw [hsyl] at hdet
  have e : K - mmseGain G K * G * K = (1 - mmseGain G K * G) * K := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  rw [e, det_mul]
  calc (1 - mmseGain G K * G).det * K.det * (G * K * Gᵀ + 1).det
      = ((1 - mmseGain G K * G).det * (G * K * Gᵀ + 1).det) * K.det := by ring
    _ = K.det := by rw [hdet, one_mul]

end DirtyPaper

end InfoTheory
