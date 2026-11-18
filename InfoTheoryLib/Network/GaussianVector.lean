/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Vector
public import InfoTheoryLib.Network.Gaussian

/-!
# Gaussian vector multiple-access and broadcast channels: the formulas

The rate regions of the Gaussian vector MAC and BC in terms of covariance matrices. The coding
theorems are not formalized: they are for continuous alphabets, and the converse for the BC needs
the vector entropy power inequality. What is proved here is the matrix analysis of Lecture 10.

## Main definitions

* `gvMACRates G₁ G₂ K₁ K₂`: the pentagon `R(K₁, K₂)`.
* `gvMACRegion G₁ G₂ P`: the region of Theorem 3 of Lecture 10, individual power constraints.
* `gvSumMACRegion G₁ G₂ P`: the region under the sum power constraint.
* `dpcRegion₁ G₁ G₂ P`, `dpcRegion₂ G₁ G₂ P`: the dirty paper coding regions for the two orders.

## Main statements

* `det_add_one_add_le`: `|I + X + Y| ≤ |I + X| |I + Y|`.
* `corner₁_mem_gvMACRates`, `corner₂_mem_gvMACRates`: the corner points of the pentagon.
* `log_det_mac_le_of_kkt`: the fixed points of iterative water-filling maximize the sum rate.
* `exists_dual_of_bc`, `exists_bc_of_dual`: the transformations of **the MAC–BC duality**.
* `convex_gvSumMACRegion`: the dual MAC region is convex.
* `convexHull_dpcRegion_eq`: **the MAC–BC duality lemma**, `R_DPC = C_DMAC`.

## Implementation notes

The regions are for nonnegative rates and use non-strict inequalities, so that the convex hull of
the two dirty paper coding regions is the dual MAC region as it stands, without the closure.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 10
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

section Inverse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `A = I + X` with `X ≽ 0`, then `A⁻¹ ≼ I`. -/
lemma one_sub_inv_posSemidef {X : Matrix n n ℝ} (hX : X.PosSemidef) :
    (1 - (X + 1)⁻¹).PosSemidef := by
  have hA := posDef_add_one hX
  set A := X + 1 with hAd
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA.det_pos.ne'
  have hAi : A⁻¹ * A = 1 := nonsing_inv_mul A hu
  have hAi' : A * A⁻¹ = 1 := mul_nonsing_inv A hu
  have hit : (A⁻¹)ᵀ = A⁻¹ := by
    rw [transpose_nonsing_inv]
    congr 1
    simpa [conjTranspose_eq_transpose_of_trivial] using hA.1.eq
  have hsym : (A⁻¹ * X)ᵀ = A⁻¹ * X := by
    have hXt : Xᵀ = X := by simpa [conjTranspose_eq_transpose_of_trivial] using hX.1.eq
    have e1 : A⁻¹ * X = 1 - A⁻¹ := by
      have : X = A - 1 := by rw [hAd]; abel
      rw [this, Matrix.mul_sub, hAi, Matrix.mul_one]
    rw [e1, transpose_sub, transpose_one, hit]
  have e : 1 - A⁻¹ = A⁻¹ * X * A⁻¹ + (A⁻¹ * X)ᵀ * (A⁻¹ * X) := by
    rw [hsym]
    have e1 : A⁻¹ * X = 1 - A⁻¹ := by
      have : X = A - 1 := by rw [hAd]; abel
      rw [this, Matrix.mul_sub, hAi, Matrix.mul_one]
    rw [e1]
    noncomm_ring
  rw [e]
  have h1 : (A⁻¹ * X * A⁻¹).PosSemidef := by
    have := posSemidef_mul_mul_transpose hX A⁻¹
    rwa [hit] at this
  have h2 : ((A⁻¹ * X)ᵀ * (A⁻¹ * X)).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_conjTranspose_mul_self (A⁻¹ * X)
  exact h1.add h2

/-- If `A ≽ B ≻ 0`, then `B⁻¹ ≽ A⁻¹`. -/
theorem posSemidef_inv_sub_inv {A B : Matrix n n ℝ} (hB : B.PosDef) (hAB : (A - B).PosSemidef) :
    (B⁻¹ - A⁻¹).PosSemidef := by
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hB
  have hdet := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at hdet
  have hS0 : S.det ≠ 0 := fun h => by simp [h] at hdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hS0
  have hSt : IsUnit Sᵀ.det := by rwa [det_transpose]
  have hX := posSemidef_mul_mul_transpose hAB S
  have e : S * (A - B) * Sᵀ + 1 = S * A * Sᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hS, sub_add_cancel]
  have hinv : ∀ {C : Matrix n n ℝ}, IsUnit C.det → (S * C * Sᵀ)⁻¹ = (Sᵀ)⁻¹ * C⁻¹ * S⁻¹ := by
    intro C hC
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have hAform : A = (A - B) + B := by abel
  have hApd : A.PosDef := by
    rw [hAform]
    exact Matrix.PosDef.posSemidef_add hAB hB
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hApd.det_pos.ne'
  have hBinv : B⁻¹ = Sᵀ * S := by
    have h1 : B * (Sᵀ * S) = 1 := by
      have hSS : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
      calc B * (Sᵀ * S) = (S⁻¹ * S) * B * Sᵀ * S := by
            rw [hSS, Matrix.one_mul, Matrix.mul_assoc]
        _ = S⁻¹ * (S * B * Sᵀ) * S := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hS, Matrix.mul_one, hSS]
    exact inv_eq_right_inv h1
  have h := one_sub_inv_posSemidef hX
  rw [e, hinv hAu] at h
  have h2 := posSemidef_transpose_mul_mul h S
  have e2 : Sᵀ * (1 - (Sᵀ)⁻¹ * A⁻¹ * S⁻¹) * S = B⁻¹ - A⁻¹ := by
    have h3 : Sᵀ * (Sᵀ)⁻¹ = 1 := mul_nonsing_inv _ hSt
    have h4 : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBinv]
    congr 1
    calc Sᵀ * ((Sᵀ)⁻¹ * A⁻¹ * S⁻¹) * S = (Sᵀ * (Sᵀ)⁻¹) * A⁻¹ * (S⁻¹ * S) := by
          simp only [Matrix.mul_assoc]
      _ = A⁻¹ := by rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
  rwa [e2] at h2

/-- **Subadditivity.** `|I + X + Y| ≤ |I + X| |I + Y|` for `X, Y ≽ 0`. -/
theorem det_add_one_add_le {X Y : Matrix n n ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (X + Y + 1).det ≤ (X + 1).det * (Y + 1).det := by
  have hA := posDef_add_one hX
  set A := X + 1 with hAd
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hA
  have hdet := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at hdet
  have hS0 : S.det ≠ 0 := fun h => by simp [h] at hdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hS0
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA.det_pos.ne'
  have hAinv : A⁻¹ = Sᵀ * S := by
    have h1 : A * (Sᵀ * S) = 1 := by
      have hSS : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
      calc A * (Sᵀ * S) = (S⁻¹ * S) * A * Sᵀ * S := by
            rw [hSS, Matrix.one_mul, Matrix.mul_assoc]
        _ = S⁻¹ * (S * A * Sᵀ) * S := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hS, Matrix.mul_one, hSS]
    exact inv_eq_right_inv h1
  obtain ⟨C, rfl⟩ := exists_eq_transpose_mul_self hY
  -- `|A + Cᵀ C| = |A| |I + C A⁻¹ Cᵀ|`.
  have e1 : (X + Cᵀ * C + 1) = A + Cᵀ * C := by rw [hAd]; abel
  have e2 : S.det ^ 2 * (A + Cᵀ * C).det = (C * A⁻¹ * Cᵀ + 1).det := by
    rw [← det_mul_mul_transpose, Matrix.mul_add, Matrix.add_mul, hS, add_comm, hAinv]
    have e3 : S * (Cᵀ * C) * Sᵀ + 1 = (S * Cᵀ) * (C * Sᵀ) + 1 := by
      simp only [Matrix.mul_assoc]
    rw [e3, det_mul_add_one_comm]
    simp only [Matrix.mul_assoc]
  have hle : (C * A⁻¹ * Cᵀ + 1).det ≤ (C * Cᵀ + 1).det := by
    have hin := one_sub_inv_posSemidef hX
    rw [← hAd] at hin
    have hPSD := posSemidef_mul_mul_transpose hin C
    have e4 : C * (1 - A⁻¹) * Cᵀ = (C * Cᵀ + 1) - (C * A⁻¹ * Cᵀ + 1) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      abel
    rw [e4] at hPSD
    exact det_le_det_of_posSemidef_sub
      (posDef_add_one (posSemidef_mul_mul_transpose hA.inv.posSemidef C)).posSemidef hPSD
  have hsyl : (C * Cᵀ + 1).det = (Cᵀ * C + 1).det := det_mul_add_one_comm C Cᵀ
  have hdetA : S.det ^ 2 * A.det = 1 := hdet
  have hs : 0 < S.det ^ 2 := by positivity
  rw [e1]
  have h3 : S.det ^ 2 * (A + Cᵀ * C).det ≤ S.det ^ 2 * (A.det * (Cᵀ * C + 1).det) := by
    rw [e2, ← mul_assoc, hdetA, one_mul, ← hsyl]
    exact hle
  exact le_of_mul_le_mul_left h3 hs

end Inverse

/-! ### The Gaussian vector MAC -/

section MAC

variable {r t₁ t₂ : Type*} [Fintype r] [Fintype t₁] [Fintype t₂] [DecidableEq r]
  (G₁ : Matrix r t₁ ℝ) (G₂ : Matrix r t₂ ℝ)

/-- **Lecture 10 of [elgamal2010], page 10-42.** The pentagon `R(K₁, K₂)`:
`R₁ ≤ ½ log |G₁ K₁ G₁ᵀ + I|`, `R₂ ≤ ½ log |G₂ K₂ G₂ᵀ + I|`,
`R₁ + R₂ ≤ ½ log |G₁ K₁ G₁ᵀ + G₂ K₂ G₂ᵀ + I|`, for nonnegative rates, in nats. -/
def gvMACRates (K₁ : Matrix t₁ t₁ ℝ) (K₂ : Matrix t₂ t₂ ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ R.1 ≤ gvRate G₁ K₁ ∧ R.2 ≤ gvRate G₂ K₂ ∧
    R.1 + R.2 ≤ 1 / 2 * log (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1).det}

/-- **Theorem 3 of Lecture 10 of [elgamal2010], the region.** The union of the pentagons for
`K₁, K₂ ≽ 0` with `tr K₁ ≤ P`, `tr K₂ ≤ P`. -/
def gvMACRegion (P : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (K₁ : Matrix t₁ t₁ ℝ) (K₂ : Matrix t₂ t₂ ℝ), K₁.PosSemidef ∧ K₂.PosSemidef ∧
    K₁.trace ≤ P ∧ K₂.trace ≤ P ∧ R ∈ gvMACRates G₁ G₂ K₁ K₂}

/-- **Lecture 10 of [elgamal2010], page 10-42.** The union of the pentagons under the sum power
constraint `tr K₁ + tr K₂ ≤ P`. -/
def gvSumMACRegion (P : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (K₁ : Matrix t₁ t₁ ℝ) (K₂ : Matrix t₂ t₂ ℝ), K₁.PosSemidef ∧ K₂.PosSemidef ∧
    K₁.trace + K₂.trace ≤ P ∧ R ∈ gvMACRates G₁ G₂ K₁ K₂}

variable {G₁ G₂} {K₁ : Matrix t₁ t₁ ℝ} {K₂ : Matrix t₂ t₂ ℝ}

/-- `|G₁ K₁ G₁ᵀ + I| ≤ |G₁ K₁ G₁ᵀ + G₂ K₂ G₂ᵀ + I|`. -/
lemma det_le_det_mac (hK₁ : K₁.PosSemidef) (hK₂ : K₂.PosSemidef) :
    (G₁ * K₁ * G₁ᵀ + 1).det ≤ (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1).det := by
  refine det_le_det_of_posSemidef_sub
    (posDef_add_one (posSemidef_mul_mul_transpose hK₁ G₁)).posSemidef ?_
  have e : G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1 - (G₁ * K₁ * G₁ᵀ + 1) = G₂ * K₂ * G₂ᵀ := by abel
  rw [e]
  exact posSemidef_mul_mul_transpose hK₂ G₂

/-- **Lecture 10, page 10-67.** The corner point of the pentagon with the message of sender 2
decoded first: `R₁ = ½ log |G₁ K₁ G₁ᵀ + I|`,
`R₂ = ½ log (|G₁ K₁ G₁ᵀ + G₂ K₂ G₂ᵀ + I| / |G₁ K₁ G₁ᵀ + I|)`.
-/
theorem corner₁_mem_gvMACRates (hK₁ : K₁.PosSemidef) (hK₂ : K₂.PosSemidef) :
    (gvRate G₁ K₁,
      1 / 2 * log ((G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1).det / (G₁ * K₁ * G₁ᵀ + 1).det)) ∈
      gvMACRates G₁ G₂ K₁ K₂ := by
  have h₁ := posSemidef_mul_mul_transpose hK₁ G₁
  have h₂ := posSemidef_mul_mul_transpose hK₂ G₂
  have hA := (posDef_add_one h₁).det_pos
  have hB := (posDef_add_one h₂).det_pos
  have hC : 0 < (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1).det := hA.trans_le (det_le_det_mac hK₁ hK₂)
  refine ⟨gvRate_nonneg G₁ hK₁, ?_, le_rfl, ?_, ?_⟩
  · refine mul_nonneg (by norm_num) (log_nonneg ?_)
    rw [one_le_div hA]
    exact det_le_det_mac hK₁ hK₂
  · refine mul_le_mul_of_nonneg_left (log_le_log (div_pos hC hA) ?_) (by norm_num)
    rw [div_le_iff₀ hA, mul_comm]
    exact det_add_one_add_le h₁ h₂
  · simp only [gvRate]
    rw [← mul_add, ← log_mul hA.ne' (div_pos hC hA).ne', mul_div_cancel₀ _ hA.ne']

/-- **Lecture 10, page 10-67.** The other corner point of the pentagon. -/
theorem corner₂_mem_gvMACRates (hK₁ : K₁.PosSemidef) (hK₂ : K₂.PosSemidef) :
    (1 / 2 * log ((G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1).det / (G₂ * K₂ * G₂ᵀ + 1).det),
      gvRate G₂ K₂) ∈ gvMACRates G₁ G₂ K₁ K₂ := by
  have h₁ := posSemidef_mul_mul_transpose hK₁ G₁
  have h₂ := posSemidef_mul_mul_transpose hK₂ G₂
  have hA := (posDef_add_one h₁).det_pos
  have hB := (posDef_add_one h₂).det_pos
  have hsw : G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1 = G₂ * K₂ * G₂ᵀ + G₁ * K₁ * G₁ᵀ + 1 := by abel
  have hC : 0 < (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1).det := hA.trans_le (det_le_det_mac hK₁ hK₂)
  refine ⟨?_, gvRate_nonneg G₂ hK₂, ?_, le_rfl, ?_⟩
  · refine mul_nonneg (by norm_num) (log_nonneg ?_)
    rw [one_le_div hB, hsw]
    exact det_le_det_mac hK₂ hK₁
  · refine mul_le_mul_of_nonneg_left (log_le_log (div_pos hC hB) ?_) (by norm_num)
    rw [div_le_iff₀ hB]
    exact det_add_one_add_le h₁ h₂
  · simp only [gvRate]
    rw [← mul_add, ← log_mul (div_pos hC hB).ne' hB.ne', div_mul_cancel₀ _ hB.ne']

/-- The pentagon is the part of the positive quadrant below the segment between its corner points.
-/
lemma mem_convexHull_of_mem_pentagon {a b s : ℝ} {R : ℝ × ℝ} {S : Set (ℝ × ℝ)}
    (hc₁ : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x ≤ a → y ≤ s - a → (x, y) ∈ S)
    (hc₂ : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x ≤ s - b → y ≤ b → (x, y) ∈ S)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsa : a ≤ s) (hsb : b ≤ s) (hab : s ≤ a + b)
    (h1 : 0 ≤ R.1) (h2 : 0 ≤ R.2) (hRa : R.1 ≤ a) (hRb : R.2 ≤ b) (hRs : R.1 + R.2 ≤ s) :
    R ∈ convexHull ℝ S := by
  obtain ⟨x, y⟩ := R
  simp only at h1 h2 hRa hRb hRs
  -- Move to the segment by raising the first coordinate as far as possible.
  rcases le_total x (s - b) with hx | hx
  · exact subset_convexHull ℝ S (hc₂ h1 h2 hx hRb)
  rcases le_total y (s - a) with hy | hy
  · exact subset_convexHull ℝ S (hc₁ h1 h2 hRa hy)
  -- Now `x > s - b` and `y > s - a`: write `(x, y)` as a combination of `(a, y')` and `(x', b)`.
  have hd : 0 < a + b - s ∨ a + b - s = 0 := by
    rcases (sub_nonneg.2 hab).eq_or_lt with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  rcases hd with hd | hd
  · set θ := (x - (s - b)) / (a + b - s) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
    have hθ1 : θ ≤ 1 := (div_le_one hd).2 (by linarith)
    -- `(u, v) = θ (a, s - a) + (1 - θ) (s - b, b)` has `u = x` and `v ≥ y`.
    set v := θ * (s - a) + (1 - θ) * b with hv
    have hu : θ * a + (1 - θ) * (s - b) = x := by
      rw [hθ]
      field_simp
      ring
    have hvy : y ≤ v := by
      have : θ * a + (1 - θ) * (s - b) + v = s := by
        rw [hv]
        ring
      linarith
    have hv0 : 0 < v ∨ v = 0 := by
      rcases (h2.trans hvy).eq_or_lt with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    have hy' : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ 1 ∧ y = ρ * v := by
      rcases hv0 with h | h
      · exact ⟨y / v, div_nonneg h2 h.le, (div_le_one h).2 hvy, by field_simp⟩
      · exact ⟨0, le_rfl, zero_le_one, by rw [h] at hvy; simp; linarith⟩
    obtain ⟨ρ, hρ0, hρ1, hρ⟩ := hy'
    have hm : ((x, y) : ℝ × ℝ) =
        θ • ((a, ρ * (s - a)) : ℝ × ℝ) + (1 - θ) • ((s - b, ρ * b) : ℝ × ℝ) := by
      ext
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
        exact hu.symm
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
        rw [hρ, hv]
        ring
    rw [hm]
    have hsab : 0 ≤ s - a := by linarith
    have hsbb : 0 ≤ s - b := by linarith
    refine (convex_convexHull ℝ S) (subset_convexHull ℝ S (hc₁ ha (mul_nonneg hρ0 hsab) le_rfl ?_))
      (subset_convexHull ℝ S (hc₂ hsbb (mul_nonneg hρ0 hb) le_rfl ?_)) hθ0 (by linarith)
      (by ring)
    · nlinarith
    · nlinarith
  · -- The segment is a point.
    have h3 : x ≤ s - b := by linarith
    exact subset_convexHull ℝ S (hc₂ h1 h2 h3 hRb)

end MAC

private lemma mul_combo_mul {r t : Type*} [Fintype t] (G : Matrix r t ℝ)
    (K L : Matrix t t ℝ) (a b : ℝ) :
    G * (a • K + b • L) * Gᵀ = a • (G * K * Gᵀ) + b • (G * L * Gᵀ) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- `a log |A| + b log |B| ≤ log |a A + b B|`. -/
private lemma log_det_combo {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * log A.det + b * log B.det ≤ log (a • A + b • B).det :=
  concaveOn_log_det.2 hA hB ha hb hab

section Convex

variable {r t₁ t₂ : Type*} [Fintype r] [Fintype t₁] [Fintype t₂] [DecidableEq r]

/-- **Lecture 10, page 10-44.** The rate terms are concave, so that the union of the pentagons under
the sum power constraint is convex. -/
theorem convex_gvSumMACRegion (G₁ : Matrix r t₁ ℝ) (G₂ : Matrix r t₂ ℝ) (P : ℝ) :
    Convex ℝ (gvSumMACRegion G₁ G₂ P) := by
  rintro ⟨x₁, x₂⟩ ⟨K₁, K₂, h₁, h₂, htr, hx⟩ ⟨y₁, y₂⟩ ⟨L₁, L₂, l₁, l₂, ltr, hy⟩ a b ha hb hab
  obtain ⟨x0, x0', xa, xb, xs⟩ := hx
  obtain ⟨y0, y0', ya, yb, ys⟩ := hy
  simp only at x0 x0' xa xb xs y0 y0' ya yb ys
  have hsc : ∀ {u v : Matrix r r ℝ}, a • (u + 1) + b • (v + 1) = a • u + b • v + 1 := by
    intro u v
    have : (1 : Matrix r r ℝ) = (a + b) • 1 := by rw [hab, one_smul]
    conv_rhs => rw [this, add_smul]
    simp only [smul_add]
    abel
  have hM₁ : (a • K₁ + b • L₁).PosSemidef := (h₁.smul ha).add (l₁.smul hb)
  have hM₂ : (a • K₂ + b • L₂).PosSemidef := (h₂.smul ha).add (l₂.smul hb)
  refine ⟨a • K₁ + b • L₁, a • K₂ + b • L₂, hM₁, hM₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [trace_add, trace_smul, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    positivity
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    positivity
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, gvRate] at xa ya ⊢
    rw [mul_combo_mul, ← hsc]
    have h := log_det_combo (posDef_add_one (posSemidef_mul_mul_transpose h₁ G₁))
      (posDef_add_one (posSemidef_mul_mul_transpose l₁ G₁)) ha hb hab
    nlinarith
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, gvRate] at xb yb ⊢
    rw [mul_combo_mul, ← hsc]
    have h := log_det_combo (posDef_add_one (posSemidef_mul_mul_transpose h₂ G₂))
      (posDef_add_one (posSemidef_mul_mul_transpose l₂ G₂)) ha hb hab
    nlinarith
  · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [mul_combo_mul, mul_combo_mul]
    have e : a • (G₁ * K₁ * G₁ᵀ) + b • (G₁ * L₁ * G₁ᵀ) +
        (a • (G₂ * K₂ * G₂ᵀ) + b • (G₂ * L₂ * G₂ᵀ)) + 1 =
        a • (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1) + b • (G₁ * L₁ * G₁ᵀ + G₂ * L₂ * G₂ᵀ + 1) := by
      rw [hsc]
      simp only [smul_add]
      abel
    rw [e]
    have h := log_det_combo
      (posDef_add_one
        ((posSemidef_mul_mul_transpose h₁ G₁).add (posSemidef_mul_mul_transpose h₂ G₂)))
      (posDef_add_one
        ((posSemidef_mul_mul_transpose l₁ G₁).add (posSemidef_mul_mul_transpose l₂ G₂)))
      ha hb hab
    nlinarith

end Convex

/-! ### The fixed points of iterative water-filling -/

section IterativeWaterFilling

variable {r t₁ t₂ : Type*} [Fintype r] [Fintype t₁] [Fintype t₂] [DecidableEq r]
  [DecidableEq t₁] [DecidableEq t₂] (G₁ : Matrix r t₁ ℝ) (G₂ : Matrix r t₂ ℝ)

private lemma trace_inv_mul_kkt {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t]
    [DecidableEq t]
    {A : Matrix r r ℝ} (G : Matrix r t ℝ) (K L U : Matrix t t ℝ) (l : ℝ)
    (hst : (1 / 2 : ℝ) • (Gᵀ * A⁻¹ * G) + U = l • 1) :
    (A⁻¹ * (G * (L - K) * Gᵀ)).trace =
      2 * (l * (L.trace - K.trace) - (U * L).trace + (U * K).trace) := by
  have hGA : Gᵀ * A⁻¹ * G = (2 : ℝ) • (l • 1 - U) := by
    rw [← hst, add_sub_cancel_right, smul_smul]
    norm_num
  have htr : (A⁻¹ * (G * (L - K) * Gᵀ)).trace = (Gᵀ * A⁻¹ * G * (L - K)).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [htr, hGA, Matrix.smul_mul, trace_smul, Matrix.sub_mul, trace_sub, Matrix.smul_mul,
    trace_smul, Matrix.one_mul, Matrix.mul_sub, trace_sub, trace_sub, smul_eq_mul, smul_eq_mul]
  ring

/-- **Lecture 10 of [elgamal2010], page 10-19.** If `K₁`, `K₂` satisfy the KKT conditions of the
single-user water-filling problems, each against the noise `G K Gᵀ + I` of the other sender, then
they maximize the sum rate `log |G₁ K₁ G₁ᵀ + G₂ K₂ G₂ᵀ + I|` under the individual power constraints.
These are the fixed points of iterative water-filling. -/
theorem log_det_mac_le_of_kkt {K₁ U₁ : Matrix t₁ t₁ ℝ} {K₂ U₂ : Matrix t₂ t₂ ℝ}
    (h₁ : K₁.PosSemidef) (h₂ : K₂.PosSemidef) (hU₁ : U₁.PosSemidef) (hU₂ : U₂.PosSemidef)
    {l₁ l₂ P₁ P₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hst₁ : (1 / 2 : ℝ) • (G₁ᵀ * (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1)⁻¹ * G₁) + U₁ = l₁ • 1)
    (hst₂ : (1 / 2 : ℝ) • (G₂ᵀ * (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1)⁻¹ * G₂) + U₂ = l₂ • 1)
    (hc₁ : l₁ * (K₁.trace - P₁) = 0) (hc₂ : l₂ * (K₂.trace - P₂) = 0)
    (hs₁ : (U₁ * K₁).trace = 0) (hs₂ : (U₂ * K₂).trace = 0) {L₁ : Matrix t₁ t₁ ℝ}
    {L₂ : Matrix t₂ t₂ ℝ} (hL₁ : L₁.PosSemidef) (hL₂ : L₂.PosSemidef) (hP₁ : L₁.trace ≤ P₁)
    (hP₂ : L₂.trace ≤ P₂) :
    log (G₁ * L₁ * G₁ᵀ + G₂ * L₂ * G₂ᵀ + 1).det ≤ log (G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1).det := by
  set A := G₁ * K₁ * G₁ᵀ + G₂ * K₂ * G₂ᵀ + 1 with hAd
  have hA : A.PosDef := posDef_add_one
    ((posSemidef_mul_mul_transpose h₁ G₁).add (posSemidef_mul_mul_transpose h₂ G₂))
  have hB : (G₁ * L₁ * G₁ᵀ + G₂ * L₂ * G₂ᵀ + 1).PosDef := posDef_add_one
    ((posSemidef_mul_mul_transpose hL₁ G₁).add (posSemidef_mul_mul_transpose hL₂ G₂))
  have e : G₁ * L₁ * G₁ᵀ + G₂ * L₂ * G₂ᵀ + 1 =
      A + (G₁ * (L₁ - K₁) * G₁ᵀ + G₂ * (L₂ - K₂) * G₂ᵀ) := by
    rw [hAd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e] at hB ⊢
  have h := log_det_add_sub_le hA hB
  rw [Matrix.mul_add, trace_add, trace_inv_mul_kkt G₁ K₁ L₁ U₁ l₁ hst₁,
    trace_inv_mul_kkt G₂ K₂ L₂ U₂ l₂ hst₂, hs₁, hs₂] at h
  have h0₁ := trace_mul_nonneg_of_posSemidef hU₁ hL₁
  have h0₂ := trace_mul_nonneg_of_posSemidef hU₂ hL₂
  have h1 : l₁ * (L₁.trace - P₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl₁ (by linarith)
  have h2 : l₂ * (L₂.trace - P₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl₂ (by linarith)
  nlinarith

end IterativeWaterFilling

/-! ### The MAC–BC duality -/

section Duality

variable {r₁ r₂ t : Type*} [Fintype r₁] [Fintype r₂] [Fintype t] [DecidableEq r₁] [DecidableEq r₂]
  [DecidableEq t]

/-- A whitening matrix `S` of `B ≻ 0` with its inverse `T`: `S B Sᵀ = I` and `T Tᵀ = B`. -/
private lemma exists_whitening {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ}
    (hB : B.PosDef) : ∃ S T : Matrix n n ℝ, S * B * Sᵀ = 1 ∧ T * S = 1 ∧ S * T = 1 ∧ T * Tᵀ = B ∧
      S.det ^ 2 * B.det = 1 := by
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hB
  have hdet := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at hdet
  have hS0 : S.det ≠ 0 := fun h => by simp [h] at hdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hS0
  have hTS : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
  have hST : S * S⁻¹ = 1 := mul_nonsing_inv S hSu
  refine ⟨S, S⁻¹, hS, hTS, hST, ?_, hdet⟩
  have htrans : (S⁻¹)ᵀ * Sᵀ = 1 := by rw [← transpose_mul, hST, transpose_one]
  have hright : Sᵀ * (S⁻¹)ᵀ = 1 := by rw [← transpose_mul, hTS, transpose_one]
  calc S⁻¹ * (S⁻¹)ᵀ = S⁻¹ * (S * B * Sᵀ) * (S⁻¹)ᵀ := by rw [hS, Matrix.mul_one]
    _ = (S⁻¹ * S) * B * (Sᵀ * (S⁻¹)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [hTS, hright, Matrix.one_mul, Matrix.mul_one]

/-- `|S X Sᵀ + I| = |S|² |X + B|` for a whitening matrix `S` of `B`. -/
private lemma det_whiten {n : Type*} [Fintype n] [DecidableEq n] {B S : Matrix n n ℝ}
    (hS : S * B * Sᵀ = 1) (X : Matrix n n ℝ) :
    (S * X * Sᵀ + 1).det = S.det ^ 2 * (X + B).det := by
  rw [← det_mul_mul_transpose, Matrix.mul_add, Matrix.add_mul, hS]

variable (G₁ : Matrix r₁ t ℝ) (G₂ : Matrix r₂ t ℝ)

/-- **Lecture 10 of [elgamal2010], page 10-39.** The rate
`½ log (|G (K + K') Gᵀ + I| / |G K' Gᵀ + I|)` when the signal of covariance `K'` is treated as
noise.
-/
def dpcRate {r : Type*} [Fintype r] [DecidableEq r] (G : Matrix r t ℝ) (K K' : Matrix t t ℝ) : ℝ :=
  1 / 2 * log ((G * (K + K') * Gᵀ + 1).det / (G * K' * Gᵀ + 1).det)

/-- **Lecture 10 of [elgamal2010], page 10-39.** The dirty paper coding region `R₁`, where `M₁` is
encoded first: `R₁ ≤ dpcRate G₁ K₁ K₂` and `R₂ ≤ ½ log |G₂ K₂ G₂ᵀ + I|`, for `tr K₁ + tr K₂ ≤ P`. -/
def dpcRegion₁ (P : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ K₁ K₂ : Matrix t t ℝ, K₁.PosSemidef ∧ K₂.PosSemidef ∧
    K₁.trace + K₂.trace ≤ P ∧ R.1 ≤ dpcRate G₁ K₁ K₂ ∧ R.2 ≤ gvRate G₂ K₂}

/-- **Lecture 10 of [elgamal2010], page 10-39.** The dirty paper coding region `R₂`, where `M₂` is
encoded first. -/
def dpcRegion₂ (P : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ K₁ K₂ : Matrix t t ℝ, K₁.PosSemidef ∧ K₂.PosSemidef ∧
    K₁.trace + K₂.trace ≤ P ∧ R.1 ≤ gvRate G₁ K₁ ∧ R.2 ≤ dpcRate G₂ K₂ K₁}

/-- **The MAC–BC duality (Lecture 10 of [elgamal2010], pages 10-65 to 10-68).** The covariance
matrices `K₁, K₂` of the dirty paper coding scheme give covariance matrices `K₁', K₂'` for the dual
MAC, with the same rates and no more sum power, when `M₂` is decoded before `M₁`. -/
theorem exists_dual_of_bc {K₁ K₂ : Matrix t t ℝ} (h₁ : K₁.PosSemidef) (h₂ : K₂.PosSemidef) :
    ∃ (K₁' : Matrix r₁ r₁ ℝ) (K₂' : Matrix r₂ r₂ ℝ), K₁'.PosSemidef ∧ K₂'.PosSemidef ∧
      K₁'.trace + K₂'.trace ≤ K₁.trace + K₂.trace ∧
      (G₁ᵀ * K₁' * G₁ + 1).det * (G₁ * K₂ * G₁ᵀ + 1).det = (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det ∧
      (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det =
        (G₁ᵀ * K₁' * G₁ + 1).det * (G₂ * K₂ * G₂ᵀ + 1).det := by
  -- The first sender.
  have hSg₁ := posDef_add_one (posSemidef_mul_mul_transpose h₂ G₁)
  set Sg₁ := G₁ * K₂ * G₁ᵀ + 1 with hSg₁d
  obtain ⟨S₁, -, hS₁, -, -, -, hd₁⟩ := exists_whitening hSg₁
  obtain ⟨Kb₁, hKb₁, htr₁, hdet₁⟩ := exists_reciprocal (S₁ * G₁) h₁
  set K₁' := S₁ᵀ * Kb₁ * S₁ with hK₁'
  have hK₁'p : K₁'.PosSemidef := posSemidef_transpose_mul_mul hKb₁ S₁
  have e₁ : (S₁ * G₁)ᵀ * Kb₁ * (S₁ * G₁) = G₁ᵀ * K₁' * G₁ := by
    simp only [hK₁', transpose_mul, Matrix.mul_assoc]
  have e₁' : (S₁ * G₁) * K₁ * (S₁ * G₁)ᵀ = S₁ * (G₁ * K₁ * G₁ᵀ) * S₁ᵀ := by
    simp only [transpose_mul, Matrix.mul_assoc]
  have hsum₁ : G₁ * K₁ * G₁ᵀ + Sg₁ = G₁ * (K₁ + K₂) * G₁ᵀ + 1 := by
    rw [hSg₁d, Matrix.mul_add, Matrix.add_mul, add_assoc]
  have hrate₁ : (G₁ᵀ * K₁' * G₁ + 1).det * Sg₁.det = (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det := by
    rw [← e₁, hdet₁, e₁', det_whiten hS₁, hsum₁]
    calc S₁.det ^ 2 * (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det * Sg₁.det
        = (S₁.det ^ 2 * Sg₁.det) * (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det := by ring
      _ = _ := by rw [hd₁, one_mul]
  -- The second sender.
  have hSg₂ := posDef_add_one (posSemidef_transpose_mul_mul hK₁'p G₁)
  set Sg₂ := G₁ᵀ * K₁' * G₁ + 1 with hSg₂d
  obtain ⟨S₂, T₂, hS₂, hTS₂, -, hTT₂, hd₂⟩ := exists_whitening hSg₂
  have hM : (T₂ᵀ * K₂ * T₂).PosSemidef := posSemidef_transpose_mul_mul h₂ T₂
  obtain ⟨K₂', hK₂', htr₂, hdet₂⟩ := exists_reciprocal (G₂ * S₂ᵀ) hM
  have hTS₂t : S₂ᵀ * T₂ᵀ = 1 := by rw [← transpose_mul, hTS₂, transpose_one]
  have e₂ : (G₂ * S₂ᵀ) * (T₂ᵀ * K₂ * T₂) * (G₂ * S₂ᵀ)ᵀ = G₂ * K₂ * G₂ᵀ := by
    simp only [transpose_mul, transpose_transpose]
    calc G₂ * S₂ᵀ * (T₂ᵀ * K₂ * T₂) * (S₂ * G₂ᵀ) = G₂ * (S₂ᵀ * T₂ᵀ) * K₂ * (T₂ * S₂) * G₂ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTS₂t, hTS₂, Matrix.mul_one, Matrix.mul_one]
  have e₂' : (G₂ * S₂ᵀ)ᵀ * K₂' * (G₂ * S₂ᵀ) = S₂ * (G₂ᵀ * K₂' * G₂) * S₂ᵀ := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have hrate₂ : (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det =
      Sg₂.det * (G₂ * K₂ * G₂ᵀ + 1).det := by
    rw [e₂, e₂', det_whiten hS₂] at hdet₂
    have e3 : G₂ᵀ * K₂' * G₂ + Sg₂ = G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1 := by
      rw [hSg₂d]
      abel
    rw [e3] at hdet₂
    rw [← hdet₂]
    calc (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det
        = (S₂.det ^ 2 * Sg₂.det) * (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det := by rw [hd₂, one_mul]
      _ = _ := by ring
  refine ⟨K₁', K₂', hK₁'p, hK₂', ?_, hrate₁, hrate₂⟩
  -- The sum power.
  have tr₂ : (T₂ᵀ * K₂ * T₂).trace = (K₂ * Sg₂).trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hTT₂]
    exact trace_mul_comm _ _
  have tr₃ : (K₂ * Sg₂).trace = K₂.trace + (K₁' * (Sg₁ - 1)).trace := by
    have e4 : Sg₁ - 1 = G₁ * K₂ * G₁ᵀ := by rw [hSg₁d, add_sub_cancel_right]
    rw [e4, hSg₂d, Matrix.mul_add, Matrix.mul_one, trace_add, add_comm]
    congr 1
    calc (K₂ * (G₁ᵀ * K₁' * G₁)).trace = ((K₂ * G₁ᵀ * K₁') * G₁).trace := by
          simp only [Matrix.mul_assoc]
      _ = (G₁ * (K₂ * G₁ᵀ * K₁')).trace := trace_mul_comm _ _
      _ = ((G₁ * K₂ * G₁ᵀ) * K₁').trace := by simp only [Matrix.mul_assoc]
      _ = _ := trace_mul_comm _ _
  have tr₄ : (K₁' * (Sg₁ - 1)).trace = Kb₁.trace - K₁'.trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, trace_sub]
    congr 1
    calc (K₁' * Sg₁).trace = ((S₁ᵀ * (Kb₁ * S₁)) * Sg₁).trace := by
          simp only [hK₁', Matrix.mul_assoc]
      _ = (Kb₁ * (S₁ * Sg₁ * S₁ᵀ)).trace := by
          rw [Matrix.mul_assoc, trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS₁, Matrix.mul_one]
  rw [tr₂, tr₃, tr₄] at htr₂
  linarith

/-- **The MAC–BC duality, the converse direction (Lecture 10 of [elgamal2010], page 10-65).** The
covariance matrices `K₁', K₂'` of the dual MAC, with `M₂` decoded before `M₁`, give covariance
matrices `K₁, K₂` for the dirty paper coding scheme, with the same rates and no more sum power. -/
theorem exists_bc_of_dual {K₁' : Matrix r₁ r₁ ℝ} {K₂' : Matrix r₂ r₂ ℝ} (h₁ : K₁'.PosSemidef)
    (h₂ : K₂'.PosSemidef) :
    ∃ K₁ K₂ : Matrix t t ℝ, K₁.PosSemidef ∧ K₂.PosSemidef ∧
      K₁.trace + K₂.trace ≤ K₁'.trace + K₂'.trace ∧
      (G₁ᵀ * K₁' * G₁ + 1).det * (G₁ * K₂ * G₁ᵀ + 1).det = (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det ∧
      (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det =
        (G₁ᵀ * K₁' * G₁ + 1).det * (G₂ * K₂ * G₂ᵀ + 1).det := by
  -- The second user comes first.
  have hSg₂ := posDef_add_one (posSemidef_transpose_mul_mul h₁ G₁)
  set Sg₂ := G₁ᵀ * K₁' * G₁ + 1 with hSg₂d
  obtain ⟨S₂, T₂, hS₂, hTS₂, hST₂, hTT₂, hd₂⟩ := exists_whitening hSg₂
  obtain ⟨Kb, hKb, htrb, hdetb⟩ := exists_reciprocal (G₂ * S₂ᵀ)ᵀ h₂
  rw [transpose_transpose] at hdetb
  set K₂ := S₂ᵀ * Kb * S₂ with hK₂d
  have hK₂ : K₂.PosSemidef := posSemidef_transpose_mul_mul hKb S₂
  have e₂ : (G₂ * S₂ᵀ) * Kb * (G₂ * S₂ᵀ)ᵀ = G₂ * K₂ * G₂ᵀ := by
    simp only [hK₂d, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have e₂' : (G₂ * S₂ᵀ)ᵀ * K₂' * (G₂ * S₂ᵀ) = S₂ * (G₂ᵀ * K₂' * G₂) * S₂ᵀ := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have hrate₂ : (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det =
      Sg₂.det * (G₂ * K₂ * G₂ᵀ + 1).det := by
    rw [e₂, e₂', det_whiten hS₂] at hdetb
    have e3 : G₂ᵀ * K₂' * G₂ + Sg₂ = G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1 := by
      rw [hSg₂d]
      abel
    rw [e3] at hdetb
    rw [hdetb]
    calc (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det
        = (S₂.det ^ 2 * Sg₂.det) * (G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det := by rw [hd₂, one_mul]
      _ = _ := by ring
  -- The first user.
  have hSg₁ := posDef_add_one (posSemidef_mul_mul_transpose hK₂ G₁)
  set Sg₁ := G₁ * K₂ * G₁ᵀ + 1 with hSg₁d
  obtain ⟨S₁, T₁, hS₁, hTS₁, -, hTT₁, hd₁⟩ := exists_whitening hSg₁
  have hM : (T₁ᵀ * K₁' * T₁).PosSemidef := posSemidef_transpose_mul_mul h₁ T₁
  obtain ⟨K₁, hK₁, htr₁, hdet₁⟩ := exists_reciprocal (S₁ * G₁)ᵀ hM
  rw [transpose_transpose] at hdet₁
  have hTS₁t : S₁ᵀ * T₁ᵀ = 1 := by rw [← transpose_mul, hTS₁, transpose_one]
  have e₁ : (S₁ * G₁)ᵀ * (T₁ᵀ * K₁' * T₁) * (S₁ * G₁) = G₁ᵀ * K₁' * G₁ := by
    simp only [transpose_mul]
    calc G₁ᵀ * S₁ᵀ * (T₁ᵀ * K₁' * T₁) * (S₁ * G₁) = G₁ᵀ * (S₁ᵀ * T₁ᵀ) * K₁' * (T₁ * S₁) * G₁ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTS₁t, hTS₁, Matrix.mul_one, Matrix.mul_one]
  have e₁' : (S₁ * G₁) * K₁ * (S₁ * G₁)ᵀ = S₁ * (G₁ * K₁ * G₁ᵀ) * S₁ᵀ := by
    simp only [transpose_mul, Matrix.mul_assoc]
  have hsum₁ : G₁ * K₁ * G₁ᵀ + Sg₁ = G₁ * (K₁ + K₂) * G₁ᵀ + 1 := by
    rw [hSg₁d, Matrix.mul_add, Matrix.add_mul, add_assoc]
  have hrate₁ : (G₁ᵀ * K₁' * G₁ + 1).det * Sg₁.det = (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det := by
    rw [e₁, e₁', det_whiten hS₁, hsum₁] at hdet₁
    rw [← hSg₂d, ← hdet₁] at *
    calc S₁.det ^ 2 * (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det * Sg₁.det
        = (S₁.det ^ 2 * Sg₁.det) * (G₁ * (K₁ + K₂) * G₁ᵀ + 1).det := by ring
      _ = _ := by rw [hd₁, one_mul]
  refine ⟨K₁, K₂, hK₁, hK₂, ?_, hrate₁, hrate₂⟩
  -- The sum power.
  have tr₁ : (T₁ᵀ * K₁' * T₁).trace = K₁'.trace + (K₁' * (G₁ * K₂ * G₁ᵀ)).trace := by
    have : (T₁ᵀ * K₁' * T₁).trace = (K₁' * Sg₁).trace := by
      rw [trace_mul_comm, ← Matrix.mul_assoc, hTT₁]
      exact trace_mul_comm _ _
    rw [this, hSg₁d, Matrix.mul_add, Matrix.mul_one, trace_add, add_comm]
  have tr₂ : Kb.trace = K₂.trace + (K₁' * (G₁ * K₂ * G₁ᵀ)).trace := by
    have e5 : Kb = T₂ᵀ * K₂ * T₂ := by
      have : T₂ᵀ * S₂ᵀ = 1 := by rw [← transpose_mul, hST₂, transpose_one]
      calc Kb = (T₂ᵀ * S₂ᵀ) * Kb * (S₂ * T₂) := by rw [this, hST₂, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [hK₂d, Matrix.mul_assoc]
    have e6 : (T₂ᵀ * K₂ * T₂).trace = (K₂ * Sg₂).trace := by
      rw [trace_mul_comm, ← Matrix.mul_assoc, hTT₂]
      exact trace_mul_comm _ _
    rw [e5, e6, hSg₂d, Matrix.mul_add, Matrix.mul_one, trace_add, add_comm]
    congr 1
    calc (K₂ * (G₁ᵀ * K₁' * G₁)).trace = ((K₂ * G₁ᵀ * K₁') * G₁).trace := by
          simp only [Matrix.mul_assoc]
      _ = (G₁ * (K₂ * G₁ᵀ * K₁')).trace := trace_mul_comm _ _
      _ = ((G₁ * K₂ * G₁ᵀ) * K₁').trace := by simp only [Matrix.mul_assoc]
      _ = _ := trace_mul_comm _ _
  linarith

private lemma half_log_div_eq {a c d : ℝ} (hc : 0 < c) (h : a * c = d) :
    1 / 2 * log (d / c) = 1 / 2 * log a := by
  rw [← h, mul_div_cancel_right₀ _ hc.ne']

omit [DecidableEq r₁] [DecidableEq r₂] in
lemma gvMACRates_of_le {K₁ : Matrix r₁ r₁ ℝ} {K₂ : Matrix r₂ r₂ ℝ} {c R : ℝ × ℝ}
    {H₁ : Matrix t r₁ ℝ} {H₂ : Matrix t r₂ ℝ} (hc : c ∈ gvMACRates H₁ H₂ K₁ K₂) (h1 : 0 ≤ R.1)
    (h2 : 0 ≤ R.2) (h1' : R.1 ≤ c.1) (h2' : R.2 ≤ c.2) : R ∈ gvMACRates H₁ H₂ K₁ K₂ :=
  ⟨h1, h2, h1'.trans hc.2.2.1, h2'.trans hc.2.2.2.1, (add_le_add h1' h2').trans hc.2.2.2.2⟩

/-- **Lecture 10, page 10-68.** `R₁ ⊆ C_DMAC`. -/
theorem dpcRegion₁_subset (P : ℝ) : dpcRegion₁ G₁ G₂ P ⊆ gvSumMACRegion G₁ᵀ G₂ᵀ P := by
  rintro ⟨x, y⟩ ⟨x0, y0, K₁, K₂, h₁, h₂, htr, hx, hy⟩
  obtain ⟨K₁', K₂', h₁', h₂', htr', e₁, e₂⟩ := exists_dual_of_bc G₁ G₂ h₁ h₂
  refine ⟨K₁', K₂', h₁', h₂', htr'.trans htr, ?_⟩
  have hc := corner₁_mem_gvMACRates (G₁ := G₁ᵀ) (G₂ := G₂ᵀ) h₁' h₂'
  simp only [transpose_transpose] at hc
  have hSgD := (posDef_add_one (posSemidef_mul_mul_transpose h₂ G₁)).det_pos
  have hA := (posDef_add_one (posSemidef_transpose_mul_mul h₁' G₁)).det_pos
  have hx' : x ≤ gvRate G₁ᵀ K₁' := by
    refine hx.trans (le_of_eq ?_)
    rw [dpcRate, half_log_div_eq hSgD e₁, gvRate, transpose_transpose]
  have hy' : y ≤ 1 / 2 * log ((G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det /
      (G₁ᵀ * K₁' * G₁ + 1).det) := by
    refine hy.trans (le_of_eq ?_)
    rw [half_log_div_eq hA (by rw [mul_comm]; exact e₂.symm), gvRate]
  exact gvMACRates_of_le hc x0 y0 hx' hy'

/-- **Lecture 10, page 10-68.** `R₂ ⊆ C_DMAC`. -/
theorem dpcRegion₂_subset (P : ℝ) : dpcRegion₂ G₁ G₂ P ⊆ gvSumMACRegion G₁ᵀ G₂ᵀ P := by
  rintro ⟨x, y⟩ ⟨x0, y0, K₁, K₂, h₁, h₂, htr, hx, hy⟩
  obtain ⟨K₂', K₁', h₂', h₁', htr', e₁, e₂⟩ := exists_dual_of_bc G₂ G₁ h₂ h₁
  refine ⟨K₁', K₂', h₁', h₂', by linarith, ?_⟩
  have hc := corner₂_mem_gvMACRates (G₁ := G₁ᵀ) (G₂ := G₂ᵀ) h₁' h₂'
  simp only [transpose_transpose] at hc
  have hSgD := (posDef_add_one (posSemidef_mul_mul_transpose h₁ G₂)).det_pos
  have hA := (posDef_add_one (posSemidef_transpose_mul_mul h₂' G₂)).det_pos
  have hy' : y ≤ gvRate G₂ᵀ K₂' := by
    refine hy.trans (le_of_eq ?_)
    rw [dpcRate, half_log_div_eq hSgD e₁, gvRate, transpose_transpose]
  have hsw : G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1 = G₂ᵀ * K₂' * G₂ + G₁ᵀ * K₁' * G₁ + 1 := by abel
  have hx' : x ≤ 1 / 2 * log ((G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1).det /
      (G₂ᵀ * K₂' * G₂ + 1).det) := by
    refine hx.trans (le_of_eq ?_)
    rw [hsw, half_log_div_eq hA (by rw [mul_comm]; exact e₂.symm), gvRate]
  exact gvMACRates_of_le hc x0 y0 hx' hy'

/-- **Lecture 10, pages 10-41 and 10-65.** `C_DMAC` is in the convex hull of `R₁ ∪ R₂`: each corner
point of a pentagon comes from a dirty paper coding scheme. -/
theorem gvSumMACRegion_subset_convexHull (P : ℝ) :
    gvSumMACRegion G₁ᵀ G₂ᵀ P ⊆ convexHull ℝ (dpcRegion₁ G₁ G₂ P ∪ dpcRegion₂ G₁ G₂ P) := by
  rintro R ⟨K₁', K₂', h₁', h₂', htr, hR0, hR1, hRa, hRb, hRs⟩
  simp only [transpose_transpose] at hRs
  set A₁ := G₁ᵀ * K₁' * G₁ + 1 with hA₁
  set A₂ := G₂ᵀ * K₂' * G₂ + 1 with hA₂
  set A₁₂ := G₁ᵀ * K₁' * G₁ + G₂ᵀ * K₂' * G₂ + 1 with hA₁₂
  have hX₁ := posSemidef_transpose_mul_mul h₁' G₁
  have hX₂ := posSemidef_transpose_mul_mul h₂' G₂
  have pA₁ : 0 < A₁.det := (posDef_add_one hX₁).det_pos
  have pA₂ : 0 < A₂.det := (posDef_add_one hX₂).det_pos
  have hra : gvRate G₁ᵀ K₁' = 1 / 2 * log A₁.det := by rw [gvRate, transpose_transpose]
  have hrb : gvRate G₂ᵀ K₂' = 1 / 2 * log A₂.det := by rw [gvRate, transpose_transpose]
  have le₁ : A₁.det ≤ A₁₂.det := by
    have := det_le_det_mac (G₁ := G₁ᵀ) (G₂ := G₂ᵀ) h₁' h₂'
    simpa only [transpose_transpose] using this
  have le₂ : A₂.det ≤ A₁₂.det := by
    have := det_le_det_mac (G₁ := G₂ᵀ) (G₂ := G₁ᵀ) h₂' h₁'
    simp only [transpose_transpose] at this
    rwa [show G₂ᵀ * K₂' * G₂ + G₁ᵀ * K₁' * G₁ + 1 = A₁₂ by rw [hA₁₂]; abel] at this
  have pA₁₂ : 0 < A₁₂.det := pA₁.trans_le le₁
  have hsub := det_add_one_add_le hX₁ hX₂
  have hl₁ : 1 / 2 * log A₁.det ≤ 1 / 2 * log A₁₂.det :=
    mul_le_mul_of_nonneg_left (log_le_log pA₁ le₁) (by norm_num)
  have hl₂ : 1 / 2 * log A₂.det ≤ 1 / 2 * log A₁₂.det :=
    mul_le_mul_of_nonneg_left (log_le_log pA₂ le₂) (by norm_num)
  have hl₃ : 1 / 2 * log A₁₂.det ≤ 1 / 2 * log A₁.det + 1 / 2 * log A₂.det := by
    rw [← mul_add, ← log_mul pA₁.ne' pA₂.ne']
    exact mul_le_mul_of_nonneg_left (log_le_log pA₁₂ hsub) (by norm_num)
  refine mem_convexHull_of_mem_pentagon (a := 1 / 2 * log A₁.det) (b := 1 / 2 * log A₂.det)
    (s := 1 / 2 * log A₁₂.det) ?_ ?_ (hra ▸ gvRate_nonneg G₁ᵀ h₁') (hrb ▸ gvRate_nonneg G₂ᵀ h₂')
    hl₁ hl₂ hl₃ hR0 hR1 (hRa.trans hra.le) (hRb.trans hrb.le) hRs
  · intro x y x0 y0 hx hy
    obtain ⟨K₁, K₂, h₁, h₂, htr', e₁, e₂⟩ := exists_bc_of_dual G₁ G₂ h₁' h₂'
    refine Or.inl ⟨x0, y0, K₁, K₂, h₁, h₂, htr'.trans htr, ?_, ?_⟩
    · refine hx.trans (le_of_eq ?_)
      rw [dpcRate, half_log_div_eq (posDef_add_one (posSemidef_mul_mul_transpose h₂ G₁)).det_pos e₁]
    · refine hy.trans (le_of_eq ?_)
      have hd : A₁₂.det = A₁.det * (G₂ * K₂ * G₂ᵀ + 1).det := e₂
      rw [gvRate, hd,
        log_mul pA₁.ne' (posDef_add_one (posSemidef_mul_mul_transpose h₂ G₂)).det_pos.ne']
      ring
  · intro x y x0 y0 hx hy
    obtain ⟨K₂, K₁, h₂, h₁, htr', e₁, e₂⟩ := exists_bc_of_dual G₂ G₁ h₂' h₁'
    refine Or.inr ⟨x0, y0, K₁, K₂, h₁, h₂, by linarith, ?_, ?_⟩
    · refine hx.trans (le_of_eq ?_)
      have hd : A₁₂.det = A₂.det * (G₁ * K₁ * G₁ᵀ + 1).det := by
        rw [show A₁₂ = G₂ᵀ * K₂' * G₂ + G₁ᵀ * K₁' * G₁ + 1 by rw [hA₁₂]; abel]
        exact e₂
      rw [gvRate, hd,
        log_mul pA₂.ne' (posDef_add_one (posSemidef_mul_mul_transpose h₁ G₁)).det_pos.ne']
      ring
    · refine hy.trans (le_of_eq ?_)
      rw [dpcRate, half_log_div_eq (posDef_add_one (posSemidef_mul_mul_transpose h₁ G₂)).det_pos e₁]

/-- **The MAC–BC duality lemma (Lecture 10 of [elgamal2010], page 10-41).** The dirty paper coding
region is the capacity formula of the dual MAC under the sum power constraint: `R_DPC = C_DMAC`.
With non-strict inequalities in the regions, no closure is needed. -/
theorem convexHull_dpcRegion_eq (P : ℝ) :
    convexHull ℝ (dpcRegion₁ G₁ G₂ P ∪ dpcRegion₂ G₁ G₂ P) = gvSumMACRegion G₁ᵀ G₂ᵀ P :=
  Set.Subset.antisymm
    (convexHull_min (Set.union_subset (dpcRegion₁_subset G₁ G₂ P) (dpcRegion₂_subset G₁ G₂ P))
      (convex_gvSumMACRegion G₁ᵀ G₂ᵀ P))
    (gvSumMACRegion_subset_convexHull G₁ G₂ P)

end Duality

end InfoTheory
