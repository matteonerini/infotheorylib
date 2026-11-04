/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.GaussianVector

/-!
# The enhanced degraded channel and the spectral Gaussian BC: the formulas

The matrix algebra behind the proof of the capacity region of the Gaussian vector BC in Lecture 10,
and the region of the product of AWGN-BCs. The coding theorems are not formalized.

## Main definitions

* `enhSigma₁`, `enhSigma₂`, `enhK₁`, `enhK₂`: the noise and signal covariance matrices of the
  enhanced degraded channel built from the KKT conditions of the dual MAC.
* `spectralBCRegion P N₁ N₂`: the region of the first Theorem 4 of Lecture 10.

## Main statements

* `enhK₁_posSemidef`, `enhK₂_posSemidef`, `trace_enhK_add`: the covariance matrices are allowed.
* `det_enhK₁_add_div`, `det_enhK_add_div`: they give the rates of the corner point of the dual MAC.
* `log_det_add_sigma₂_le`: the single-user optimality for the second receiver.
* `det_smul_rpow_add`: the equality in the entropy power inequality for scaled matrices.
* `one_sub_mul_sigma_posSemidef`: the original channel is a degraded version of the enhanced one.
* `single_mem_spectralBCRegion`: the rates of parallel channels to one receiver are in the region.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 10
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The enhanced degraded channel -/

section Enhanced

variable {t : Type*} [Fintype t] [DecidableEq t]

/-- **Lecture 10 of [elgamal2010], page 10-49.** `Σ₁ = (α/(2λ)) A⁻¹`, where
`A = G₁ᵀ K₁ G₁ + G₂ᵀ K₂ G₂ + I`. -/
def enhSigma₁ (α lam : ℝ) (A : Matrix t t ℝ) : Matrix t t ℝ := (α / (2 * lam)) • A⁻¹

/-- **Lecture 10 of [elgamal2010], page 10-49.** `Σ₂ = (α/(2λ)) A⁻¹ + ((ᾱ - α)/(2λ)) B⁻¹`, where
`B = G₂ᵀ K₂ G₂ + I`. -/
def enhSigma₂ (α lam : ℝ) (A B : Matrix t t ℝ) : Matrix t t ℝ :=
  enhSigma₁ α lam A + ((1 - α - α) / (2 * lam)) • B⁻¹

/-- **Lecture 10 of [elgamal2010], page 10-50.** `K₁** = (α/(2λ)) B⁻¹ - Σ₁`. -/
def enhK₁ (α lam : ℝ) (A B : Matrix t t ℝ) : Matrix t t ℝ :=
  (α / (2 * lam)) • B⁻¹ - enhSigma₁ α lam A

/-- **Lecture 10 of [elgamal2010], page 10-50.** `K₂** = (ᾱ/(2λ)) I - K₁** - Σ₂`. -/
def enhK₂ (α lam : ℝ) (A B : Matrix t t ℝ) : Matrix t t ℝ :=
  ((1 - α) / (2 * lam)) • 1 - enhK₁ α lam A B - enhSigma₂ α lam A B

variable {α lam : ℝ} {A B : Matrix t t ℝ}

/-- `K₁** + Σ₁ = (α/(2λ)) B⁻¹`. -/
theorem enhK₁_add_sigma₁ : enhK₁ α lam A B + enhSigma₁ α lam A = (α / (2 * lam)) • B⁻¹ :=
  sub_add_cancel _ _

/-- `K₁** + Σ₂ = (ᾱ/(2λ)) B⁻¹`. -/
theorem enhK₁_add_sigma₂ (hl : lam ≠ 0) :
    enhK₁ α lam A B + enhSigma₂ α lam A B = ((1 - α) / (2 * lam)) • B⁻¹ := by
  have h : (1 - α) / (2 * lam) = α / (2 * lam) + (1 - α - α) / (2 * lam) := by
    field_simp
    ring
  rw [h, add_smul, enhSigma₂, enhK₁]
  abel

/-- `K₁** + K₂** + Σ₂ = (ᾱ/(2λ)) I`. -/
theorem enhK_add_sigma₂ :
    enhK₁ α lam A B + enhK₂ α lam A B + enhSigma₂ α lam A B = ((1 - α) / (2 * lam)) • 1 := by
  rw [enhK₂]
  abel

/-- `Σ₂ - Σ₁ = ((ᾱ - α)/(2λ)) B⁻¹`, a scaled version of `K₁** + Σ₁`. -/
theorem enhSigma₂_sub : enhSigma₂ α lam A B - enhSigma₁ α lam A = ((1 - α - α) / (2 * lam)) • B⁻¹ :=
  add_sub_cancel_left _ _

/-- **Lecture 10, page 10-50.** `K₁** ≽ 0`, as `A ≽ B`. -/
theorem enhK₁_posSemidef (hB : B.PosDef) (hAB : (A - B).PosSemidef) (hα : 0 ≤ α) (hl : 0 < lam) :
    (enhK₁ α lam A B).PosSemidef := by
  have e : enhK₁ α lam A B = (α / (2 * lam)) • (B⁻¹ - A⁻¹) := by
    rw [enhK₁, enhSigma₁, smul_sub]
  rw [e]
  exact (posSemidef_inv_sub_inv hB hAB).smul (by positivity)

/-- **Lecture 10, page 10-50.** `K₂** ≽ 0`, as `B ≽ I`. -/
theorem enhK₂_posSemidef {X : Matrix t t ℝ} (hX : X.PosSemidef) (hB : B = X + 1) (hα : α ≤ 1)
    (hl : 0 < lam) : (enhK₂ α lam A B).PosSemidef := by
  have e : enhK₂ α lam A B = ((1 - α) / (2 * lam)) • (1 - B⁻¹) := by
    have h := enhK₁_add_sigma₂ (α := α) (A := A) (B := B) hl.ne'
    rw [enhK₂, sub_sub, h, smul_sub]
  rw [e, hB]
  exact (one_sub_inv_posSemidef hX).smul (div_nonneg (by linarith) (by positivity))

/-- **Lecture 10, page 10-49.** `Σ₂ ≽ Σ₁` for `α ≤ 1/2`. -/
theorem enhSigma₂_sub_posSemidef (hB : B.PosDef) (hα : α ≤ 1 / 2) (hl : 0 < lam) :
    (enhSigma₂ α lam A B - enhSigma₁ α lam A).PosSemidef := by
  rw [enhSigma₂_sub]
  exact hB.inv.posSemidef.smul (div_nonneg (by linarith) (by positivity))

/-- **Lecture 10, page 10-49.** `Σ₁ ≻ 0` for `α > 0`. -/
theorem enhSigma₁_posDef (hA : A.PosDef) (hα : 0 < α) (hl : 0 < lam) :
    (enhSigma₁ α lam A).PosDef :=
  hA.inv.smul (by positivity)

private lemma det_inv_eq (M : Matrix t t ℝ) : M⁻¹.det = (M.det)⁻¹ := by
  rw [det_nonsing_inv, Ring.inverse_eq_inv']

/-- **Lecture 10, page 10-50.** `|K₁** + Σ₁| / |Σ₁| = |A| / |B|`, so that `R₁* = ½ log (|A| / |B|)`.
-/
theorem det_enhK₁_add_div (hA : A.PosDef) (hB : B.PosDef) (hα : 0 < α) (hl : 0 < lam) :
    (enhK₁ α lam A B + enhSigma₁ α lam A).det / (enhSigma₁ α lam A).det = A.det / B.det := by
  have hc : (α / (2 * lam)) ^ Fintype.card t ≠ 0 := pow_ne_zero _ (by positivity)
  rw [enhK₁_add_sigma₁, enhSigma₁, det_smul, det_smul, mul_div_mul_left _ _ hc, det_inv_eq A,
    det_inv_eq B]
  field_simp [hA.det_pos.ne', hB.det_pos.ne']

/-- **Lecture 10, page 10-50.** `|K₁** + K₂** + Σ₂| / |K₁** + Σ₂| = |B|`, so that
`R₂* = ½ log |B|`. -/
theorem det_enhK_add_div (hB : B.PosDef) (hα : α < 1) (hl : 0 < lam) :
    (enhK₁ α lam A B + enhK₂ α lam A B + enhSigma₂ α lam A B).det /
      (enhK₁ α lam A B + enhSigma₂ α lam A B).det = B.det := by
  have hc : ((1 - α) / (2 * lam)) ^ Fintype.card t ≠ 0 :=
    pow_ne_zero _ (div_pos (by linarith) (by positivity)).ne'
  rw [enhK_add_sigma₂, enhK₁_add_sigma₂ hl.ne', det_smul, det_smul, mul_div_mul_left _ _ hc,
    det_inv_eq B, det_one]
  field_simp [hB.det_pos.ne']

/-- **Lecture 10, page 10-58.** Matrices that are scaled versions of each other satisfy the equality
in Minkowski's inequality: `|a M|^{1/t} + |b M|^{1/t} = |(a + b) M|^{1/t}`. This is the equality in
the entropy power inequality in the proof of Lemma 4. -/
theorem det_smul_rpow_add {M : Matrix t t ℝ} (hM : M.PosDef) (ht : 0 < Fintype.card t) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • M).det ^ (1 / (Fintype.card t : ℝ)) + (b • M).det ^ (1 / (Fintype.card t : ℝ)) =
      ((a + b) • M).det ^ (1 / (Fintype.card t : ℝ)) := by
  have hn : (Fintype.card t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have key : ∀ {c : ℝ}, 0 ≤ c → (c • M).det ^ (1 / (Fintype.card t : ℝ)) =
      c * M.det ^ (1 / (Fintype.card t : ℝ)) := by
    intro c hc
    rw [det_smul, mul_rpow (pow_nonneg hc _) hM.det_pos.le, ← rpow_natCast c, ← rpow_mul hc,
      mul_one_div_cancel hn, rpow_one]
  rw [key ha, key hb, key (add_nonneg ha hb)]
  ring

omit [DecidableEq t] in
/-- **Lecture 10, page 10-53.** The KKT conditions give `I - Gⱼ Σⱼ Gⱼᵀ ≽ 0`, which makes the
original
channel a degraded version of the enhanced channel. -/
theorem one_sub_mul_sigma_posSemidef {r : Type*} [Finite r] [DecidableEq r] {G : Matrix r t ℝ}
    {Sg : Matrix t t ℝ} {U : Matrix r r ℝ} (hU : U.PosSemidef) (hl : 0 < lam)
    (h : G * Sg * Gᵀ + lam⁻¹ • U = 1) : (1 - G * Sg * Gᵀ).PosSemidef := by
  have e : 1 - G * Sg * Gᵀ = lam⁻¹ • U := by rw [← h, add_sub_cancel_left]
  rw [e]
  exact hU.smul (inv_pos.2 hl).le

omit [DecidableEq t] in
/-- `tr K = tr(K (G Σ Gᵀ + λ⁻¹ U)) = tr(Σ (Gᵀ K G))`. -/
private lemma trace_eq_of_kkt {r : Type*} [Fintype r] [DecidableEq r] {G : Matrix r t ℝ}
    {K U : Matrix r r ℝ} {Sg : Matrix t t ℝ} (h : G * Sg * Gᵀ + lam⁻¹ • U = 1)
    (hs : (U * K).trace = 0) : K.trace = (Sg * (Gᵀ * K * G)).trace := by
  have e : K.trace = ((G * Sg * Gᵀ + lam⁻¹ • U) * K).trace := by rw [h, Matrix.one_mul]
  rw [e, Matrix.add_mul, trace_add, Matrix.smul_mul, trace_smul, hs, smul_zero, add_zero]
  calc (G * Sg * Gᵀ * K).trace = (G * (Sg * (Gᵀ * K))).trace := by simp only [Matrix.mul_assoc]
    _ = (Sg * (Gᵀ * K) * G).trace := trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **Lecture 10, page 10-50.** The KKT conditions for the dual MAC give
`tr K₁** + tr K₂** = tr K₁ + tr K₂`, which is `P` as the optimal covariance matrices use full power.
-/
theorem trace_enhK_add {r₁ r₂ : Type*} [Fintype r₁] [Fintype r₂] [DecidableEq r₁] [DecidableEq r₂]
    {G₁ : Matrix r₁ t ℝ} {G₂ : Matrix r₂ t ℝ} {K₁ U₁ : Matrix r₁ r₁ ℝ} {K₂ U₂ : Matrix r₂ r₂ ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hl : lam ≠ 0) (hAd : A = G₁ᵀ * K₁ * G₁ + B)
    (hBd : B = G₂ᵀ * K₂ * G₂ + 1)
    (h₁ : G₁ * enhSigma₁ α lam A * G₁ᵀ + lam⁻¹ • U₁ = 1)
    (h₂ : G₂ * enhSigma₂ α lam A B * G₂ᵀ + lam⁻¹ • U₂ = 1)
    (hs₁ : (U₁ * K₁).trace = 0) (hs₂ : (U₂ * K₂).trace = 0) :
    (enhK₁ α lam A B + enhK₂ α lam A B).trace = K₁.trace + K₂.trace := by
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA.det_pos.ne'
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB.det_pos.ne'
  have hAA : (A⁻¹ * A).trace = (Fintype.card t : ℝ) := by
    rw [nonsing_inv_mul A hAu, trace_one]
  have hBB : (B⁻¹ * B).trace = (Fintype.card t : ℝ) := by
    rw [nonsing_inv_mul B hBu, trace_one]
  have hcd : (1 - α) / (2 * lam) = α / (2 * lam) + (1 - α - α) / (2 * lam) := by
    field_simp
    ring
  have eX₁ : G₁ᵀ * K₁ * G₁ = A - B := by rw [hAd, add_sub_cancel_right]
  have eX₂ : G₂ᵀ * K₂ * G₂ = B - 1 := by rw [hBd, add_sub_cancel_right]
  have t₁ := trace_eq_of_kkt h₁ hs₁
  have t₂ := trace_eq_of_kkt h₂ hs₂
  rw [eX₁, enhSigma₁, Matrix.smul_mul, trace_smul, Matrix.mul_sub, trace_sub, hAA, smul_eq_mul]
    at t₁
  rw [eX₂, enhSigma₂, enhSigma₁, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, trace_add,
    trace_smul, trace_smul, Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub, hBB,
    Matrix.mul_one, Matrix.mul_one, smul_eq_mul, smul_eq_mul] at t₂
  have e : enhK₁ α lam A B + enhK₂ α lam A B =
      ((1 - α) / (2 * lam)) • 1 - enhSigma₂ α lam A B := by
    rw [enhK₂]
    abel
  rw [e, trace_sub, trace_smul, trace_one, smul_eq_mul, enhSigma₂, enhSigma₁, trace_add, trace_smul,
    trace_smul, smul_eq_mul, smul_eq_mul, hcd, t₁, t₂]
  ring

/-- **Lecture 10, page 10-57.** The covariance `K₁** + K₂**`, of trace `P`, satisfies the KKT
conditions for the single-user channel `Y₂ = X + Z₂` with `Z₂ ∼ N(0, Σ₂)`, so that
`|K + Σ₂| ≤ |K₁** + K₂** + Σ₂|` in logarithm for all `K ≽ 0` with `tr K ≤ P`. -/
theorem log_det_add_sigma₂_le (hA : A.PosDef) (hB : B.PosDef) (hα : 0 < α) (hα' : α ≤ 1 / 2)
    (hl : 0 < lam) {P : ℝ} (hX : (enhK₁ α lam A B + enhK₂ α lam A B).PosSemidef)
    (htr : (enhK₁ α lam A B + enhK₂ α lam A B).trace = P) {K : Matrix t t ℝ} (hK : K.PosSemidef)
    (hP : K.trace ≤ P) :
    log (K + enhSigma₂ α lam A B).det ≤
      log (enhK₁ α lam A B + enhK₂ α lam A B + enhSigma₂ α lam A B).det := by
  have hS₂ : (enhSigma₂ α lam A B).PosDef :=
    Matrix.PosDef.add_posSemidef (enhSigma₁_posDef hA hα hl)
      (hB.inv.posSemidef.smul (div_nonneg (by linarith) (by positivity)))
  have hc : (0 : ℝ) < (1 - α) / (2 * lam) := div_pos (by linarith) (by positivity)
  have hsum := enhK_add_sigma₂ (α := α) (lam := lam) (A := A) (B := B)
  have hinv : (enhK₁ α lam A B + enhK₂ α lam A B + enhSigma₂ α lam A B)⁻¹ =
      ((1 - α) / (2 * lam))⁻¹ • (1 : Matrix t t ℝ) := by
    rw [hsum]
    refine inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc.ne',
      one_smul]
  have h := log_det_le_of_kkt (r := t) (t := t) hS₂ (1 : Matrix t t ℝ) hX PosSemidef.zero
    (lam := lam / (1 - α)) (P := P) (div_nonneg hl.le (by linarith)) (by
      simp only [transpose_one, Matrix.mul_one, Matrix.one_mul, add_zero]
      rw [hinv, smul_smul]
      congr 1
      have : 1 - α ≠ 0 := by linarith
      field_simp) (by rw [htr, sub_self, mul_zero]) (by simp) hK hP
  simpa only [transpose_one, Matrix.mul_one, Matrix.one_mul] using h

end Enhanced

/-! ### The spectral Gaussian BC -/

section Spectral

variable {d : Type*} [Fintype d]

/-- **Theorem 4 of Lecture 10 of [elgamal2010], page 10-24, the region.** The rate triples
`(R₀, R₁, R₂)` of the product of AWGN-BCs with the noise powers `N₁ₖ`, `N₂ₖ`, in nats. A power
fraction `βₖ` goes to the component `k`, of which a part `αₖ` carries the cloud center. -/
def spectralBCRegion (P : ℝ) (N₁ N₂ : d → ℝ) : Set (ℝ × ℝ × ℝ) :=
  open Classical in
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2 ∧ ∃ α β : d → ℝ, (∀ k, 0 ≤ α k ∧ α k ≤ 1) ∧
    (∀ k, 0 ≤ β k ∧ β k ≤ 1) ∧ ∑ k, β k = 1 ∧
    R.1 + R.2.1 ≤ ∑ k, (if N₁ k ≤ N₂ k then gaussCap (β k * P / N₁ k) else
      gaussCap (α k * β k * P / ((1 - α k) * β k * P + N₁ k))) ∧
    R.1 + R.2.2 ≤ ∑ k, (if N₁ k ≤ N₂ k then
      gaussCap (α k * β k * P / ((1 - α k) * β k * P + N₂ k)) else gaussCap (β k * P / N₂ k)) ∧
    R.1 + R.2.1 + R.2.2 ≤ ∑ k, (if N₁ k ≤ N₂ k then gaussCap (β k * P / N₁ k) else
      gaussCap (α k * β k * P / ((1 - α k) * β k * P + N₁ k)) +
        gaussCap ((1 - α k) * β k * P / N₂ k)) ∧
    R.1 + R.2.1 + R.2.2 ≤ ∑ k, (if N₁ k ≤ N₂ k then
      gaussCap (α k * β k * P / ((1 - α k) * β k * P + N₂ k)) +
        gaussCap ((1 - α k) * β k * P / N₁ k) else gaussCap (β k * P / N₂ k))}

/-- **Lecture 10, page 10-24.** The region contains the rates of the parallel channels to receiver
1:
all the power of a component where receiver 1 is the better one goes to satellite codewords, and the
other components carry only cloud centers. -/
theorem single_mem_spectralBCRegion {P : ℝ} {N₁ N₂ : d → ℝ} (hP : 0 ≤ P) (h₁ : ∀ k, 0 < N₁ k)
    (h₂ : ∀ k, 0 < N₂ k) {β : d → ℝ} (hβ : ∀ k, 0 ≤ β k ∧ β k ≤ 1) (hs : ∑ k, β k = 1) :
    ((0 : ℝ), ∑ k, gaussCap (β k * P / N₁ k), (0 : ℝ)) ∈ spectralBCRegion P N₁ N₂ := by
  classical
  have hpow : ∀ k, 0 ≤ β k * P := fun k => mul_nonneg (hβ k).1 hP
  have hC₁ : ∀ k, 0 ≤ gaussCap (β k * P / N₁ k) := fun k =>
    gaussCap_nonneg (div_nonneg (hpow k) (h₁ k).le)
  have hC₂ : ∀ k, 0 ≤ gaussCap (β k * P / N₂ k) := fun k =>
    gaussCap_nonneg (div_nonneg (hpow k) (h₂ k).le)
  set α : d → ℝ := fun k => if N₁ k ≤ N₂ k then 0 else 1 with hα
  have hmono : ∀ k, ¬ N₁ k ≤ N₂ k → gaussCap (β k * P / N₁ k) ≤ gaussCap (β k * P / N₂ k) :=
    fun k hk => gaussCap_le_gaussCap (div_nonneg (hpow k) (h₁ k).le)
      (div_le_div_of_nonneg_left (hpow k) (h₂ k) (not_le.1 hk).le)
  have hgc0 : gaussCap 0 = 0 := by simp [gaussCap]
  refine ⟨le_rfl, sum_nonneg fun k _ => hC₁ k, le_rfl, α, β, fun k => ?_, hβ, hs, ?_, ?_, ?_, ?_⟩
  · simp only [hα]
    split_ifs <;> norm_num
  · refine (zero_add _).le.trans (sum_le_sum fun k _ => ?_)
    by_cases hk : N₁ k ≤ N₂ k
    · simp [hk]
    · simp [hα, hk]
  · refine (add_zero (0 : ℝ)).le.trans (sum_nonneg fun k _ => ?_)
    by_cases hk : N₁ k ≤ N₂ k
    · simp only [hk, ite_true, hα, zero_mul, zero_div, hgc0]
      exact le_rfl
    · simp only [hk, ite_false]
      exact hC₂ k
  · simp only [zero_add, add_zero]
    refine sum_le_sum fun k _ => ?_
    by_cases hk : N₁ k ≤ N₂ k
    · simp [hk]
    · simp [hα, hk, hgc0]
  · simp only [zero_add, add_zero]
    refine sum_le_sum fun k _ => ?_
    by_cases hk : N₁ k ≤ N₂ k
    · simp [hα, hk, hgc0]
    · simp only [hk, ite_false]
      exact hmono k hk

end Spectral

end InfoTheory
