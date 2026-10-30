/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.ColoredNoise

/-!
# Gaussian channels with feedback

With feedback, the input `Xᵢ` of a Gaussian channel with colored noise `Zⁿ ∼ N(0, K_Z)` may depend
on the past outputs, hence on the past noise: `Xⁿ = B Zⁿ + Vⁿ` with `B` strictly lower triangular
and `Vⁿ` independent of `Zⁿ`, (9.101). The capacity with feedback is
`C_{n,FB} = max (1/2n) log (|(B + I) K_Z (B + I)ᵀ + K_V| / |K_Z|)` over `tr(B K_Z Bᵀ + K_V) ≤ nP`,
(9.102). Feedback increases the capacity by at most half a bit, `C_{n,FB} ≤ C_n + ½`, and at most
doubles it, `C_{n,FB} ≤ 2 C_n`.

## Main definitions

* `secondMoment P X`: the covariance (second-moment) matrix `K_X = E X Xᵀ` of a random vector.
* `StrictlyLowerTriangular B`: `Bᵢⱼ = 0` for `i ≤ j`.
* `capacityFB K P`: the capacity with feedback `C_{n,FB}` of (9.102).

## Main statements

* `secondMoment_add_add_sub`: Lemma 9.6.1, `K_{X+Z} + K_{X-Z} = 2K_X + 2K_Z`.
* `secondMoment_mulVec_add`: (9.101)–(9.102), `K_{BZ+V} = B K_Z Bᵀ + K_V` when `V` and `Z` are
  uncorrelated.
* `det_le_det_of_posSemidef_sub`, `det_rpow_mul_det_rpow_le` (`ForMathlib.MatrixDet`):
  Lemmas 9.6.2 and 9.6.4.
* `det_add_one_le_two_pow_mul`: Lemma 9.6.3, `|K_{X+Z}| ≤ 2ⁿ |K_X + K_Z|`.
* `det_le_det_sub_one`: Lemma 9.6.5, (9.143), `|K_{X-Z}| ≥ |K_Z|` for causally related
  `X = BZ + V`.
* `capacityFB_le_add`: Theorem 9.6.2, `C_{n,FB} ≤ C_n + ½ log 2` nats (half a bit).
* `capacityFB_le_two_mul`: Theorem 9.6.3, `C_{n,FB} ≤ 2 C_n`.

## Implementation notes

The capacities `C_n` (9.104) and `C_{n,FB}` (9.102) are defined, as in the book, as maxima over
covariance matrices, and the theorems are proved at the level of these matrices. The book's
information-theoretic proofs of Lemmas 9.6.2 and 9.6.4 use normal densities, which do not exist
for singular covariance matrices; we prove them with the spectral theorem instead
(`ForMathlib.MatrixDet`). For `X = BZ + V` with `B` strictly lower triangular, the covariance
`K_{X-Z} = (B - I) K_Z (B - I)ᵀ + K_V` dominates `(B - I) K_Z (B - I)ᵀ`, whose determinant is
`|K_Z|` since `B - I` is triangular with diagonal `-1`; this gives (9.143).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.6
-/

open Real MeasureTheory Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Covariance matrices of random vectors -/

section SecondMoment

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}

/-- The second-moment matrix `K_X = E X Xᵀ` of a random vector, its covariance matrix when
`E X = 0`. -/
def secondMoment (P : Measure Ω) (X : Ω → ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun a b => ∫ ω, X ω a * X ω b ∂P

/-- **Lemma 9.6.1.** `K_{X+Z} + K_{X-Z} = 2K_X + 2K_Z`. -/
theorem secondMoment_add_add_sub {X Z : Ω → ι → ℝ}
    (hX : ∀ a b, Integrable (fun ω => X ω a * X ω b) P)
    (hZ : ∀ a b, Integrable (fun ω => Z ω a * Z ω b) P)
    (hXZ : ∀ a b, Integrable (fun ω => X ω a * Z ω b) P) :
    secondMoment P (X + Z) + secondMoment P (X - Z) =
      (2 : ℝ) • secondMoment P X + (2 : ℝ) • secondMoment P Z := by
  ext a b
  simp only [secondMoment, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  have h1 : Integrable (fun ω => (X ω a + Z ω a) * (X ω b + Z ω b)) P :=
    (((hX a b).add (hXZ a b)).add (hXZ b a)).add (hZ a b) |>.congr
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring)
  have h2 : Integrable (fun ω => (X ω a - Z ω a) * (X ω b - Z ω b)) P :=
    (((hX a b).sub (hXZ a b)).sub (hXZ b a)).add (hZ a b) |>.congr
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have h3 : Integrable (fun ω => 2 * (X ω a * X ω b)) P := (hX a b).const_mul 2
  have h4 : Integrable (fun ω => 2 * (Z ω a * Z ω b)) P := (hZ a b).const_mul 2
  rw [← integral_add h1 h2, ← integral_const_mul, ← integral_const_mul, ← integral_add h3 h4]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)

/-- **(9.101)–(9.102)** If `V` and `Z` are uncorrelated, `E Vₐ Z_b = 0`, then
`K_{BZ+V} = B K_Z Bᵀ + K_V`. -/
theorem secondMoment_mulVec_add [Fintype ι] {Z V : Ω → ι → ℝ} (B : Matrix ι ι ℝ)
    (hZ : ∀ a b, Integrable (fun ω => Z ω a * Z ω b) P)
    (hV : ∀ a b, Integrable (fun ω => V ω a * V ω b) P)
    (hVZ : ∀ a b, Integrable (fun ω => V ω a * Z ω b) P)
    (hunc : ∀ a b, ∫ ω, V ω a * Z ω b ∂P = 0) :
    secondMoment P (fun ω => B *ᵥ Z ω + V ω) = B * secondMoment P Z * Bᵀ + secondMoment P V := by
  ext a b
  simp only [secondMoment, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, mulVec, dotProduct,
    Matrix.mul_apply, transpose_apply]
  -- Expand `(∑_c B_ac Z_c + V_a)(∑_d B_bd Z_d + V_b)`.
  have e : ∀ ω, (∑ c, B a c * Z ω c + V ω a) * (∑ d, B b d * Z ω d + V ω b) =
      ∑ c, ∑ d, B a c * B b d * (Z ω c * Z ω d) + ∑ c, B a c * (V ω b * Z ω c) +
        ∑ d, B b d * (V ω a * Z ω d) + V ω a * V ω b := by
    intro ω
    have h1 : (∑ c, B a c * Z ω c) * (∑ d, B b d * Z ω d) =
        ∑ c, ∑ d, B a c * B b d * (Z ω c * Z ω d) := by
      rw [sum_mul_sum]
      exact sum_congr rfl fun c _ => sum_congr rfl fun d _ => by ring
    have h2 : (∑ c, B a c * Z ω c) * V ω b = ∑ c, B a c * (V ω b * Z ω c) := by
      rw [sum_mul]
      exact sum_congr rfl fun c _ => by ring
    have h3 : V ω a * (∑ d, B b d * Z ω d) = ∑ d, B b d * (V ω a * Z ω d) := by
      rw [mul_sum]
      exact sum_congr rfl fun d _ => by ring
    rw [← h1, ← h2, ← h3]
    ring
  have i1 : Integrable (fun ω => ∑ c, ∑ d, B a c * B b d * (Z ω c * Z ω d)) P :=
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => (hZ c d).const_mul _
  have i2 : Integrable (fun ω => ∑ c, B a c * (V ω b * Z ω c)) P :=
    integrable_finsetSum _ fun c _ => (hVZ b c).const_mul _
  have i3 : Integrable (fun ω => ∑ d, B b d * (V ω a * Z ω d)) P :=
    integrable_finsetSum _ fun d _ => (hVZ a d).const_mul _
  have i12 : Integrable (fun ω => ∑ c, ∑ d, B a c * B b d * (Z ω c * Z ω d) +
      ∑ c, B a c * (V ω b * Z ω c)) P := i1.add i2
  have i123 : Integrable (fun ω => ∑ c, ∑ d, B a c * B b d * (Z ω c * Z ω d) +
      ∑ c, B a c * (V ω b * Z ω c) + ∑ d, B b d * (V ω a * Z ω d)) P := i12.add i3
  have e1 : ∫ ω, ∑ c, ∑ d, B a c * B b d * (Z ω c * Z ω d) ∂P =
      ∑ c, ∑ d, B a c * B b d * ∫ ω, Z ω c * Z ω d ∂P := by
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => (hZ c d).const_mul _]
    refine sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun d _ => (hZ c d).const_mul _]
    exact sum_congr rfl fun d _ => integral_const_mul _ _
  have e2 : ∫ ω, ∑ c, B a c * (V ω b * Z ω c) ∂P = 0 := by
    rw [integral_finsetSum _ fun c _ => (hVZ b c).const_mul _]
    exact sum_eq_zero fun c _ => by rw [integral_const_mul, hunc, mul_zero]
  have e3 : ∫ ω, ∑ d, B b d * (V ω a * Z ω d) ∂P = 0 := by
    rw [integral_finsetSum _ fun d _ => (hVZ a d).const_mul _]
    exact sum_eq_zero fun d _ => by rw [integral_const_mul, hunc, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add i123 (hV a b),
    integral_add i12 i3, integral_add i1 i2, e1, e2, e3, add_zero, add_zero]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun c _ => by ring

end SecondMoment

/-! ### The determinant inequalities -/

variable {n : ℕ}

/-- `B` is strictly lower triangular: in `Xⁿ = B Zⁿ + Vⁿ`, `Xᵢ` depends only on the past noise
`Z₁, …, Zᵢ₋₁`, (9.101). -/
def StrictlyLowerTriangular (B : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ i j, i ≤ j → B i j = 0

lemma StrictlyLowerTriangular.det_add_smul_one {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : StrictlyLowerTriangular B) (c : ℝ) : (B + c • 1).det = c ^ n := by
  have hlow : (B + c • 1).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    simp [hB i j hij'.le, Matrix.one_apply_ne hij'.ne]
  rw [det_of_isLowerTriangular _ hlow]
  simp [hB _ _ le_rfl]

lemma StrictlyLowerTriangular.det_add_one {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : StrictlyLowerTriangular B) : (B + 1).det = 1 := by
  simpa using hB.det_add_smul_one 1

lemma StrictlyLowerTriangular.det_sub_one_sq {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : StrictlyLowerTriangular B) : (B - 1).det ^ 2 = 1 := by
  have h := hB.det_add_smul_one (-1)
  rw [neg_one_smul, ← sub_eq_add_neg] at h
  rw [h, ← pow_mul, mul_comm, pow_mul]
  simp

/-- **Lemma 9.6.1 for `X = BZ + V`.** `K_{X+Z} + K_{X-Z} = 2(K_X + K_Z)`, with
`K_{X±Z} = (B ± I) K_Z (B ± I)ᵀ + K_V` and `K_X = B K_Z Bᵀ + K_V`. -/
lemma feedback_covariance_identity (B KZ KV : Matrix (Fin n) (Fin n) ℝ) :
    ((B + 1) * KZ * (B + 1)ᵀ + KV) + ((B - 1) * KZ * (B - 1)ᵀ + KV) =
      (2 : ℝ) • ((B * KZ * Bᵀ + KV) + KZ) := by
  rw [transpose_add, transpose_sub, transpose_one, two_smul]
  noncomm_ring

/-- **Lemma 9.6.5, (9.143).** For `X = BZ + V` with `B` strictly lower triangular,
`|K_{X-Z}| ≥ |K_Z|`. -/
theorem det_le_det_sub_one {B KZ KV : Matrix (Fin n) (Fin n) ℝ}
    (hB : StrictlyLowerTriangular B) (hZ : KZ.PosSemidef) (hV : KV.PosSemidef) :
    KZ.det ≤ ((B - 1) * KZ * (B - 1)ᵀ + KV).det := by
  have h1 : ((B - 1) * KZ * (B - 1)ᵀ).det = KZ.det := by
    rw [det_mul_mul_transpose, hB.det_sub_one_sq, one_mul]
  have hpsd : ((B - 1) * KZ * (B - 1)ᵀ).PosSemidef := by
    have := hZ.mul_mul_conjTranspose_same (B - 1)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [← h1]
  exact det_le_det_of_posSemidef_sub hpsd (by simpa using hV)

/-- The output covariance `K_{X+Z} = (B + I) K_Z (B + I)ᵀ + K_V` has `|K_{X+Z}| ≥ |K_Z|`. -/
theorem det_le_det_add_one {B KZ KV : Matrix (Fin n) (Fin n) ℝ}
    (hB : StrictlyLowerTriangular B) (hZ : KZ.PosSemidef) (hV : KV.PosSemidef) :
    KZ.det ≤ ((B + 1) * KZ * (B + 1)ᵀ + KV).det := by
  have h1 : ((B + 1) * KZ * (B + 1)ᵀ).det = KZ.det := by
    rw [det_mul_mul_transpose, hB.det_add_one, one_pow, one_mul]
  have hpsd : ((B + 1) * KZ * (B + 1)ᵀ).PosSemidef := by
    have := hZ.mul_mul_conjTranspose_same (B + 1)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [← h1]
  exact det_le_det_of_posSemidef_sub hpsd (by simpa using hV)

/-- **Lemma 9.6.3, (9.130)–(9.132).** For `X = BZ + V`, `|K_{X+Z}| ≤ 2ⁿ |K_X + K_Z|`:
`2(K_X + K_Z) - K_{X+Z} = K_{X-Z}` is positive semidefinite. -/
theorem det_add_one_le_two_pow_mul {B KZ KV : Matrix (Fin n) (Fin n) ℝ} (hZ : KZ.PosSemidef)
    (hV : KV.PosSemidef) :
    ((B + 1) * KZ * (B + 1)ᵀ + KV).det ≤ 2 ^ n * ((B * KZ * Bᵀ + KV) + KZ).det := by
  have hY : ((B + 1) * KZ * (B + 1)ᵀ + KV).PosSemidef := by
    have := hZ.mul_mul_conjTranspose_same (B + 1)
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact this.add hV
  have hXmZ : ((B - 1) * KZ * (B - 1)ᵀ + KV).PosSemidef := by
    have := hZ.mul_mul_conjTranspose_same (B - 1)
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact this.add hV
  have hsub : (2 : ℝ) • ((B * KZ * Bᵀ + KV) + KZ) - ((B + 1) * KZ * (B + 1)ᵀ + KV) =
      (B - 1) * KZ * (B - 1)ᵀ + KV := by
    rw [← feedback_covariance_identity, add_sub_cancel_left]
  have h := det_le_det_of_posSemidef_sub hY (by rw [hsub]; exact hXmZ)
  rwa [det_smul, Fintype.card_fin] at h

/-! ### Capacity with and without feedback -/

/-- **(9.102)** The capacity with feedback of `n` uses of the Gaussian channel with colored noise
`N(0, K_Z)` and power constraint `P`, in nats per transmission:
`C_{n,FB} = max (1/2n) log (|(B + I) K_Z (B + I)ᵀ + K_V| / |K_Z|)` over strictly lower triangular
`B` and positive semidefinite `K_V` with `tr(B K_Z Bᵀ + K_V) ≤ nP`. -/
def capacityFB (KZ : Matrix (Fin n) (Fin n) ℝ) (P : ℝ) : ℝ :=
  sSup {C | ∃ B KV : Matrix (Fin n) (Fin n) ℝ, StrictlyLowerTriangular B ∧ KV.PosSemidef ∧
    (B * KZ * Bᵀ + KV).trace ≤ n * P ∧
      C = 1 / (2 * n) * log (((B + 1) * KZ * (B + 1)ᵀ + KV).det / KZ.det)}

lemma capacityFB_nonempty (KZ : Matrix (Fin n) (Fin n) ℝ) {P : ℝ} (hP : 0 ≤ P) :
    {C | ∃ B KV : Matrix (Fin n) (Fin n) ℝ, StrictlyLowerTriangular B ∧ KV.PosSemidef ∧
      (B * KZ * Bᵀ + KV).trace ≤ n * P ∧
        C = 1 / (2 * n) * log (((B + 1) * KZ * (B + 1)ᵀ + KV).det / KZ.det)}.Nonempty :=
  ⟨_, 0, 0, fun _ _ _ => rfl, PosSemidef.zero, by
    simp only [zero_mul, transpose_zero, mul_zero, add_zero, trace_zero]; positivity, rfl⟩

/-- **Theorem 9.6.2.** Feedback increases the capacity of a Gaussian channel with colored noise by
at most half a bit: `C_{n,FB} ≤ C_n + ½ log 2` nats per transmission. -/
theorem capacityFB_le_add (hn : 0 < n) {KZ : Matrix (Fin n) (Fin n) ℝ} (hK : KZ.PosDef)
    {P : ℝ} (hP : 0 ≤ P) : capacityFB KZ P ≤ capacityNoFB KZ P + 1 / 2 * log 2 := by
  refine csSup_le (capacityFB_nonempty KZ hP) ?_
  rintro _ ⟨B, KV, hB, hV, htr, rfl⟩
  set KX := B * KZ * Bᵀ + KV
  have hX : KX.PosSemidef := by
    have := hK.posSemidef.mul_mul_conjTranspose_same B
    simpa [conjTranspose_eq_transpose_of_trivial] using this.add hV
  have hdetK := hK.det_pos
  have hY := det_le_det_add_one hB hK.posSemidef hV
  have hYpos : 0 < ((B + 1) * KZ * (B + 1)ᵀ + KV).det := hdetK.trans_le hY
  have hXZpos : 0 < (KX + KZ).det := (Matrix.PosDef.posSemidef_add hX hK).det_pos
  have h63 := det_add_one_le_two_pow_mul (B := B) hK.posSemidef hV
  have hle := le_capacityNoFB hn hK hP hX htr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : log (((B + 1) * KZ * (B + 1)ᵀ + KV).det / KZ.det) ≤
      n * log 2 + log ((KX + KZ).det / KZ.det) := by
    calc log (((B + 1) * KZ * (B + 1)ᵀ + KV).det / KZ.det)
        ≤ log (2 ^ n * (KX + KZ).det / KZ.det) :=
          log_le_log (div_pos hYpos hdetK) (div_le_div_of_nonneg_right h63 hdetK.le)
      _ = n * log 2 + log ((KX + KZ).det / KZ.det) := by
          rw [mul_div_assoc, log_mul (by positivity) (div_pos hXZpos hdetK).ne', log_pow]
  calc 1 / (2 * n) * log (((B + 1) * KZ * (B + 1)ᵀ + KV).det / KZ.det)
      ≤ 1 / (2 * n) * (n * log 2 + log ((KX + KZ).det / KZ.det)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 1 / (2 * n) * log ((KX + KZ).det / KZ.det) + 1 / 2 * log 2 := by
        field_simp
        ring
    _ ≤ capacityNoFB KZ P + 1 / 2 * log 2 := by linarith

/-- **Theorem 9.6.3 (Pinsker).** Feedback at most doubles the capacity of a Gaussian channel with
colored noise: `C_{n,FB} ≤ 2 C_n`. -/
theorem capacityFB_le_two_mul (hn : 0 < n) {KZ : Matrix (Fin n) (Fin n) ℝ} (hK : KZ.PosDef)
    {P : ℝ} (hP : 0 ≤ P) : capacityFB KZ P ≤ 2 * capacityNoFB KZ P := by
  refine csSup_le (capacityFB_nonempty KZ hP) ?_
  rintro _ ⟨B, KV, hB, hV, htr, rfl⟩
  set KX := B * KZ * Bᵀ + KV
  set KY := (B + 1) * KZ * (B + 1)ᵀ + KV
  set KXmZ := (B - 1) * KZ * (B - 1)ᵀ + KV
  have hX : KX.PosSemidef := by
    have := hK.posSemidef.mul_mul_conjTranspose_same B
    simpa [conjTranspose_eq_transpose_of_trivial] using this.add hV
  have hYpsd : KY.PosSemidef := by
    have := hK.posSemidef.mul_mul_conjTranspose_same (B + 1)
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact this.add hV
  have hXmZpsd : KXmZ.PosSemidef := by
    have := hK.posSemidef.mul_mul_conjTranspose_same (B - 1)
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact this.add hV
  have hdetK := hK.det_pos
  have hYpos : 0 < KY.det := hdetK.trans_le (det_le_det_add_one hB hK.posSemidef hV)
  have hXZpos : 0 < (KX + KZ).det := (Matrix.PosDef.posSemidef_add hX hK).det_pos
  -- (9.159): `K_X + K_Z = ½ K_{X+Z} + ½ K_{X-Z}`.
  have hhalf : (1 / 2 : ℝ) • KY + (1 - 1 / 2 : ℝ) • KXmZ = KX + KZ := by
    have h := feedback_covariance_identity B KZ KV
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← smul_add, h, smul_smul]
    norm_num
    rfl
  -- (9.160)–(9.161): Lemmas 9.6.4 and 9.6.5.
  have h64 := det_rpow_mul_det_rpow_le hYpsd hXmZpsd (t := 1 / 2) (by norm_num) (by norm_num)
  rw [hhalf, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at h64
  have h65 := det_le_det_sub_one hB hK.posSemidef hV
  have hkey : KY.det ^ (1 / 2 : ℝ) * KZ.det ^ (1 / 2 : ℝ) ≤ (KX + KZ).det :=
    le_trans (mul_le_mul_of_nonneg_left (rpow_le_rpow hdetK.le h65 (by norm_num))
      (rpow_nonneg hYpos.le _)) h64
  have hlog := log_le_log (by positivity) hkey
  rw [log_mul (by positivity) (by positivity), log_rpow hYpos, log_rpow hdetK] at hlog
  have hle := le_capacityNoFB hn hK hP hX htr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hineq : log (KY.det / KZ.det) ≤ 2 * log ((KX + KZ).det / KZ.det) := by
    rw [log_div hYpos.ne' hdetK.ne', log_div hXZpos.ne' hdetK.ne']
    linarith
  calc 1 / (2 * n) * log (KY.det / KZ.det)
      ≤ 1 / (2 * n) * (2 * log ((KX + KZ).det / KZ.det)) :=
        mul_le_mul_of_nonneg_left hineq (by positivity)
    _ = 2 * (1 / (2 * n) * log ((KX + KZ).det / KZ.det)) := by ring
    _ ≤ 2 * capacityNoFB KZ P := by linarith

end InfoTheory
