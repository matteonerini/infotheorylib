/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Capacity
public import InfoTheoryLib.DifferentialEntropy.AEP
public import InfoTheoryLib.DifferentialEntropy.ChainRule
public import InfoTheoryLib.DifferentialEntropy.Estimation
public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian
public import InfoTheoryLib.DifferentialEntropy.Partition
public import InfoTheoryLib.DifferentialEntropy.Quantization

/-!
# Cover & Thomas, Chapter 8: Differential Entropy

This file indexes the formalization of Chapter 8 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_8_2_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Densities.** A density is a real function `f` with `IsPDF μ f`: measurable, non-negative,
  integrable, with `∫ f dμ = 1`. The reference measure `μ` is Lebesgue measure `volume` on `ℝ`
  and on `Fin n → ℝ`, or a product measure `μ.prod ν` for a pair `(X, Y)`. The random variable
  with density `f` has law `pdfMeasure μ f`.
* **Integrability.** `h(f) = diffEntropy μ f = ∫ -f log f dμ` is a Bochner integral, which is `0`
  when the integrand is not integrable. Results about `h(f)` therefore assume that `f log f`, and
  the corresponding expressions for marginal and conditional densities, are integrable: this is
  the book's "if it exists".
* **Logarithms.** Logarithms are natural: differential entropies are in nats. The book's values in
  bits are `h / log 2`, and its `2^{nh}` is our `e^{nh}`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 8.1 Definitions
* Densities and the support set: `IsPDF`, `pdfMeasure` (`DifferentialEntropy.Basic`).
* (8.1): `diffEntropy`, `diffEntropy_eq_setIntegral_support`.
* Example 8.1.1, (8.2): `uniformPDF`, `diffEntropy_uniformPDF` (`DifferentialEntropy.Basic`), and
  `example_8_1_1` (here).
* Example 8.1.2, (8.3)–(8.8): `diffEntropy_gaussianPDFReal` (`DifferentialEntropy.Gaussian`);
  (8.9) in bits: `example_8_1_2` (here).

### 8.2 AEP for continuous random variables
* Theorem 8.2.1, (8.10): `prodPDF`, `pi_pdfMeasure`, `sampleDiffEntropy`,
  `tendstoInMeasure_sampleDiffEntropy`, and with probability `1`, `tendsto_sampleDiffEntropy_ae`
  (`DifferentialEntropy.AEP`).
* (8.11): `diffTypicalSet`, `measurableSet_diffTypicalSet`. (8.12): the volume of `A ⊆ ℝⁿ` is
  `Measure.pi (fun _ => volume) A`.
* Theorem 8.2.2, (8.13)–(8.22): `prodPDF_bounds`, `eventually_prob_diffTypicalSet_gt`,
  `volume_diffTypicalSet_le`, `eventually_volume_diffTypicalSet_ge`.
* Theorem 8.2.3: `eventually_volume_gt_of_prob_ge`.

### 8.3 Relation of differential entropy to discrete entropy
* (8.23)–(8.25): `binEdge`, `quantPMF`, `quantPMF_isPMF` (`DifferentialEntropy.Quantization`).
* (8.26)–(8.29): `entropy_quantPMF_add_log`.
* Theorem 8.3.1, (8.30): `tendsto_entropy_quantPMF_add_log`; `n`-bit quantization, (8.84):
  `tendsto_entropy_quantPMF_two_pow_sub`.
* Example 8.3.1: `quantPMF_uniformPDF`, `entropy_quantPMF_uniformPDF`, `example_8_3_1_one`,
  `example_8_3_1_two`, `example_8_3_1_three` (here).

### 8.4 Joint and conditional differential entropy
* (8.31): `diffEntropy` of a density on `Fin n → ℝ` or on a product `α × β`.
* (8.32): `marginalFst`, `marginalSnd`, `condDiffEntropy` (`DifferentialEntropy.Joint`).
* (8.33): `condDiffEntropy_eq`.
* Theorem 8.4.1, (8.34)–(8.45): `mvGaussianPDF`, `mvGaussianPDF_isPDF`,
  `integral_mvGaussianPDF_mul`, `diffEntropy_mvGaussianPDF`
  (`DifferentialEntropy.MultivariateGaussian`); (8.45) in bits: `theorem_8_4_1_bits` (here).

### 8.5 Relative entropy and mutual information
* (8.46): `relEntropyPDF` (`DifferentialEntropy.RelativeEntropy`).
* (8.47): `mutualInfoPDF` (`DifferentialEntropy.Joint`).
* (8.48): `mutualInfoPDF_eq_sub_condDiffEntropy`, `mutualInfoPDF_eq_sub_condDiffEntropy'`,
  `mutualInfoPDF_eq_add_sub`. (8.49): `mutualInfoPDF_eq_relEntropyPDF`.
* (8.53): `quantJointPMF`, `quantJointPMF_apply`, `quantMutualInfo`; (8.54): `mutualInfoSup`
  (`DifferentialEntropy.Partition`). Refining the partitions increases the mutual information:
  `quantMutualInfo_le_of_refine`. For discrete random variables (8.54) agrees with (2.28):
  `mutualInfoSup_eq_of_finite`.
* Example 8.5.1, (8.55)–(8.56): `corrCov`, `corrGaussianPDF`, `corrGaussianPDF_eq`,
  `example_8_5_1`, `example_8_5_1_indep` (here).

### 8.6 Properties of differential entropy, relative entropy, and mutual information
* Theorem 8.6.1, (8.57)–(8.61): `relEntropyPDF_nonneg`, `relEntropyPDF_eq_zero_iff`; as a bound
  on the differential entropy: `diffEntropy_le_crossEntropy`, `diffEntropy_eq_crossEntropy_iff`
  (`DifferentialEntropy.RelativeEntropy`).
* Corollaries: `mutualInfoPDF_nonneg`, `mutualInfoPDF_eq_zero_iff`, `condDiffEntropy_le`,
  `condDiffEntropy_eq_iff` (`DifferentialEntropy.Joint`).
* Theorem 8.6.2, (8.62): `condDiffEntropyLast`, `initMarginal`,
  `diffEntropy_eq_sum_condDiffEntropyLast` (`DifferentialEntropy.ChainRule`).
* Corollary (8.63): `diffEntropy_le_sum_coordMarginal`, `diffEntropy_eq_sum_coordMarginal_iff`;
  Hadamard's inequality (8.64): `det_le_prod_diag` (`DifferentialEntropy.MultivariateGaussian`).
* Theorem 8.6.3, (8.65): `pdfMeasure_map_add`, `diffEntropy_comp_sub`
  (`DifferentialEntropy.Basic`).
* Theorem 8.6.4, (8.66)–(8.70): `pdfMeasure_map_mul`, `diffEntropy_scale`; Corollary (8.71):
  `diffEntropy_linearEquiv`.
* Theorem 8.6.5, (8.72)–(8.76): `diffEntropy_le_of_covariance`, `diffEntropy_eq_of_covariance_iff`
  (`DifferentialEntropy.MultivariateGaussian`); in dimension one,
  `diffEntropy_le_of_integral_mul_sq`, `diffEntropy_eq_of_integral_mul_sq_iff`
  (`DifferentialEntropy.Gaussian`).
* Theorem 8.6.6, (8.77)–(8.80): `exp_two_mul_diffEntropy_div_le`,
  `exp_two_mul_diffEntropy_div_eq_iff` (`DifferentialEntropy.Gaussian`); Corollary (side
  information): `exp_two_mul_condDiffEntropy_div_le` (`DifferentialEntropy.Estimation`).

## Not formalized

* Figure 8.1, the chapter summary, and the remarks on Fisher information (Sections 11.10 and 17.8)
  and on the differential entropy `-∞` of a discrete random variable.
* Continuous random variables through their cumulative distribution function: densities are
  given directly, so random variables without a density are not covered.
* Theorem 8.3.1 for Riemann integrable densities: we assume that the density is continuous on a
  compact interval and vanishes outside it.
* The heuristic (8.50)–(8.52), the equivalence of (8.54) with (8.47) for random variables with a
  density, and the convergence of `I([X]_P; [Y]_Q)` along refining partitions; the monotonicity
  is proved.
* The case `ρ = ±1` of Example 8.5.1, where `K` is singular and `(X, Y)` has no density.
-/

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 8.1: Definitions -/

lemma support_uniformPDF {a b : ℝ} (hab : a < b) : Function.support (uniformPDF a b) = Icc a b := by
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  ext x
  by_cases hx : x ∈ Icc a b <;> simp [uniformPDF, hx, hba]

/-- **Example 8.1.1 (Uniform distribution), (8.2).** The uniform density on `[0, a]` has
differential entropy `h(X) = log a`. For `a < 1` it is negative, but `e^{h(X)} = a` is the volume
of the support set. -/
theorem example_8_1_1 {a : ℝ} (ha : 0 < a) :
    diffEntropy volume (uniformPDF 0 a) = log a ∧
      (a < 1 → diffEntropy volume (uniformPDF 0 a) < 0) ∧
      volume (Function.support (uniformPDF 0 a)) =
        ENNReal.ofReal (exp (diffEntropy volume (uniformPDF 0 a))) := by
  have h : diffEntropy volume (uniformPDF 0 a) = log a := by
    rw [diffEntropy_uniformPDF ha, sub_zero]
  refine ⟨h, fun ha1 => h ▸ log_neg ha ha1, ?_⟩
  rw [h, exp_log ha, support_uniformPDF ha, Real.volume_Icc, sub_zero]

/-- **Example 8.1.2 (Normal distribution), (8.9).** In bits, `h(N(m, σ²)) = ½ log₂ (2πeσ²)`. -/
theorem example_8_1_2 (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    diffEntropy volume (gaussianPDFReal m v) / log 2 = 1 / 2 * logb 2 (2 * π * exp 1 * v) := by
  rw [diffEntropy_gaussianPDFReal m hv, logb]
  ring

/-! ## Section 8.3: Relation of differential entropy to discrete entropy -/

/-- Each bin of the uniform distribution on `[a, b]` has probability `1/N`. -/
lemma quantPMF_uniformPDF {a b : ℝ} (hab : a < b) {N : ℕ} (k : Fin N) :
    quantPMF (uniformPDF a b) a b N k = 1 / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos k
  rw [quantPMF, intervalIntegral.integral_congr (g := fun _ => 1 / (b - a)) fun x hx => ?_,
    intervalIntegral.integral_const, binEdge_succ_sub, smul_eq_mul]
  · field_simp
  · rw [uIcc_of_le (binEdge_le_succ hab.le k)] at hx
    exact indicator_of_mem (Icc_binEdge_subset hab.le k.2 hx) _

/-- The quantization of the uniform distribution on `[a, b]` into `N` bins is uniform:
`H(X^Δ) = log N`. -/
lemma entropy_quantPMF_uniformPDF {a b : ℝ} (hab : a < b) {N : ℕ} (hN : N ≠ 0) :
    entropy (quantPMF (uniformPDF a b) a b N) = log N := by
  have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
  have h := entropy_uniformPMF (α := Fin N)
  rw [Fintype.card_fin] at h
  rw [← h]
  congr 1
  funext k
  rw [quantPMF_uniformPDF hab, uniformPMF, Fintype.card_fin]

/-- **Example 8.3.1 (1).** For `X` uniform on `[0, 1]`, `h(X) = 0`, and the quantization into
`2ⁿ` bins of length `Δ = 2⁻ⁿ` has `H(X^Δ) = n` bits. -/
theorem example_8_3_1_one (n : ℕ) :
    diffEntropy volume (uniformPDF 0 1) = 0 ∧ (1 - 0) / ((2 ^ n : ℕ) : ℝ) = 2⁻¹ ^ n ∧
      entropy (quantPMF (uniformPDF 0 1) 0 1 (2 ^ n)) / log 2 = n := by
  refine ⟨by rw [diffEntropy_uniformPDF one_pos, sub_zero, log_one], by simp, ?_⟩
  rw [entropy_quantPMF_uniformPDF one_pos (pow_ne_zero n two_ne_zero), Nat.cast_pow,
    Nat.cast_ofNat, log_pow, mul_div_cancel_right₀ _ (log_pos one_lt_two).ne']

/-- **Example 8.3.1 (2).** For `X` uniform on `[0, 1/8]`, `h(X) = -3` bits, and for `n ≥ 3` the
quantization into `2ⁿ⁻³` bins of length `Δ = 2⁻ⁿ` has `H(X^Δ) = n - 3` bits: the first three
bits of `X` are `0`. -/
theorem example_8_3_1_two {n : ℕ} (hn : 3 ≤ n) :
    diffEntropy volume (uniformPDF 0 (1 / 8)) / log 2 = -3 ∧
      (1 / 8 - 0) / ((2 ^ (n - 3) : ℕ) : ℝ) = 2⁻¹ ^ n ∧
      entropy (quantPMF (uniformPDF 0 (1 / 8)) 0 (1 / 8) (2 ^ (n - 3))) / log 2 = n - 3 := by
  have hlog2 := (log_pos one_lt_two).ne'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨?_, ?_, ?_⟩
  · rw [diffEntropy_uniformPDF (by norm_num), sub_zero,
      show (1 / 8 : ℝ) = 2⁻¹ ^ 3 by norm_num, log_pow, log_inv]
    field_simp
    norm_num
  · rw [Nat.add_sub_cancel_left, pow_add]
    push_cast
    field_simp
    rw [mul_assoc, ← mul_pow]
    norm_num
  · rw [entropy_quantPMF_uniformPDF (by norm_num) (pow_ne_zero _ two_ne_zero), Nat.cast_pow,
      Nat.cast_ofNat, log_pow, mul_div_cancel_right₀ _ hlog2, Nat.add_sub_cancel_left]
    push_cast
    ring

/-- `5.365 < ½ log₂ (2πe · 100) < 5.375`. -/
lemma half_logb_two_pi_e_hundred :
    5.365 < 1 / 2 * logb 2 (2 * π * exp 1 * 100) ∧
      1 / 2 * logb 2 (2 * π * exp 1 * 100) < 5.375 := by
  have hπ1 := pi_gt_d2
  have hπ2 := pi_lt_d2
  have he1 := exp_one_gt_d9
  have he2 := exp_one_lt_d9
  set y := 2 * π * exp 1 * 100 with hy
  have hy1 : 1707 < y := by rw [hy]; nlinarith [pi_pos, exp_pos 1]
  have hy2 : y < 1713 := by rw [hy]; nlinarith [pi_pos, exp_pos 1]
  have hy0 : 0 < y := by linarith
  constructor
  · have : (161 / 15 : ℝ) < logb 2 y := by
      rw [lt_logb_iff_rpow_lt one_lt_two hy0,
        ← pow_lt_pow_iff_left₀ (by positivity) hy0.le (by norm_num : (15 : ℕ) ≠ 0),
        ← rpow_natCast, ← rpow_mul (by norm_num),
        show (161 / 15 : ℝ) * ((15 : ℕ) : ℝ) = ((161 : ℕ) : ℝ) by norm_num, rpow_natCast]
      calc (2 : ℝ) ^ 161 < 1707 ^ 15 := by norm_num
        _ < y ^ 15 := by gcongr
    linarith
  · have : logb 2 y < 43 / 4 := by
      rw [logb_lt_iff_lt_rpow one_lt_two hy0,
        ← pow_lt_pow_iff_left₀ hy0.le (by positivity) (by norm_num : (4 : ℕ) ≠ 0),
        ← rpow_natCast (2 ^ _), ← rpow_mul (by norm_num),
        show (43 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((43 : ℕ) : ℝ) by norm_num, rpow_natCast]
      calc y ^ 4 < 1713 ^ 4 := by gcongr
        _ < 2 ^ 43 := by norm_num
    linarith

/-- **Example 8.3.1 (3).** For `X ∼ N(0, σ²)` with `σ² = 100`, describing `X` to `n`-bit accuracy
takes on average `n + h(X) = n + ½ log₂ (2πeσ²) ≈ n + 5.37` bits. -/
theorem example_8_3_1_three :
    diffEntropy volume (gaussianPDFReal 0 100) / log 2 = 1 / 2 * logb 2 (2 * π * exp 1 * 100) ∧
      5.365 < diffEntropy volume (gaussianPDFReal 0 100) / log 2 ∧
      diffEntropy volume (gaussianPDFReal 0 100) / log 2 < 5.375 := by
  have h : diffEntropy volume (gaussianPDFReal 0 100) / log 2 =
      1 / 2 * logb 2 (2 * π * exp 1 * 100) := by
    rw [example_8_1_2 0 (by norm_num)]
    norm_num
  rw [h]
  exact ⟨rfl, half_logb_two_pi_e_hundred⟩

/-! ## Section 8.4: Joint and conditional differential entropy -/

/-- **Theorem 8.4.1, (8.45).** In bits, `h(N(m, K)) = ½ log₂ ((2πe)ⁿ |K|)`. -/
theorem theorem_8_4_1_bits {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℝ}
    (hK : K.PosDef) (m : ι → ℝ) :
    diffEntropy volume (mvGaussianPDF m K) / log 2 =
      1 / 2 * logb 2 ((2 * π * exp 1) ^ Fintype.card ι * K.det) := by
  rw [diffEntropy_mvGaussianPDF hK, logb]
  ring

/-! ## Section 8.5: Example 8.5.1 -/

section Correlated

open Matrix

variable {v : ℝ≥0} {ρ : ℝ}

/-- **(8.55)** The covariance matrix of two normal random variables with variance `σ² = v` and
correlation coefficient `ρ`. -/
def corrCov (v : ℝ≥0) (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![(v : ℝ), ρ * v; ρ * v, v]

/-- The conditional variance `σ²(1 - ρ²)` of `Y` given `X`. -/
def condVar (v : ℝ≥0) (ρ : ℝ) : ℝ≥0 := v * (1 - ρ ^ 2).toNNReal

lemma one_sub_sq_pos (hρ : |ρ| < 1) : 0 < 1 - ρ ^ 2 := by
  have := (sq_lt_one_iff_abs_lt_one ρ).2 hρ
  linarith

lemma coe_condVar (v : ℝ≥0) (hρ : |ρ| < 1) : (condVar v ρ : ℝ) = v * (1 - ρ ^ 2) := by
  simp [condVar, Real.coe_toNNReal _ (one_sub_sq_pos hρ).le]

lemma condVar_ne_zero (hv : v ≠ 0) (hρ : |ρ| < 1) : condVar v ρ ≠ 0 := by
  intro h
  have := coe_condVar v hρ
  rw [h, NNReal.coe_zero] at this
  have hv' : (0 : ℝ) < v := by positivity
  nlinarith [one_sub_sq_pos hρ]

lemma det_corrCov : (corrCov v ρ).det = v ^ 2 * (1 - ρ ^ 2) := by
  simp [corrCov, Matrix.det_fin_two_of]
  ring

lemma inv_corrCov (hv : v ≠ 0) (hρ : |ρ| < 1) :
    (corrCov v ρ)⁻¹ = ((v : ℝ) * (1 - ρ ^ 2))⁻¹ • !![1, -ρ; -ρ, 1] := by
  apply Matrix.inv_eq_right_inv
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h1 := (one_sub_sq_pos hρ).ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corrCov, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

lemma quadForm_corrCov (hv : v ≠ 0) (hρ : |ρ| < 1) (x y : ℝ) :
    ![x, y] ⬝ᵥ ((corrCov v ρ)⁻¹ *ᵥ ![x, y]) =
      (x ^ 2 - 2 * ρ * x * y + y ^ 2) / (v * (1 - ρ ^ 2)) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h1 := (one_sub_sq_pos hρ).ne'
  rw [inv_corrCov hv hρ]
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  field_simp
  ring

lemma corrCov_posDef (hv : v ≠ 0) (hρ : |ρ| < 1) : (corrCov v ρ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [corrCov]
  · have e : star x ⬝ᵥ (corrCov v ρ *ᵥ x) =
        v * ((x 0 + ρ * x 1) ^ 2 + (1 - ρ ^ 2) * x 1 ^ 2) := by
      simp [corrCov, dotProduct, mulVec, Fin.sum_univ_two]
      ring
    rw [e]
    have hv' : (0 : ℝ) < v := by positivity
    have h1 := one_sub_sq_pos hρ
    refine mul_pos hv' ?_
    by_cases hx1 : x 1 = 0
    · have hx0 : x 0 ≠ 0 := fun hx0 => hx (funext fun i => by fin_cases i <;> simp [hx0, hx1])
      have e1 : (x 0 + ρ * x 1) ^ 2 + (1 - ρ ^ 2) * x 1 ^ 2 = x 0 ^ 2 := by
        rw [hx1]
        ring
      rw [e1]
      exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hx0).symm
    · have : 0 < (1 - ρ ^ 2) * x 1 ^ 2 := by positivity
      positivity

/-- **Example 8.5.1.** The joint density of `(X, Y) ∼ N(0, K)`, with `K` as in (8.55). -/
def corrGaussianPDF (v : ℝ≥0) (ρ : ℝ) (z : ℝ × ℝ) : ℝ :=
  mvGaussianPDF 0 (corrCov v ρ) ![z.1, z.2]

/-- Completing the square: `f(x, y) = φ_{σ²}(x) φ_{σ²(1 - ρ²)}(y - ρx)`. -/
lemma corrGaussianPDF_eq (hv : v ≠ 0) (hρ : |ρ| < 1) (x y : ℝ) :
    corrGaussianPDF v ρ (x, y) =
      gaussianPDFReal 0 v x * gaussianPDFReal (ρ * x) (condVar v ρ) y := by
  have hv' : (0 : ℝ) < v := by positivity
  have h1 := one_sub_sq_pos hρ
  rw [corrGaussianPDF, mvGaussianPDF, sub_zero, quadForm_corrCov hv hρ, det_corrCov,
    Fintype.card_fin, gaussianPDFReal_def, gaussianPDFReal_def, coe_condVar v hρ]
  simp only
  rw [mul_mul_mul_comm, ← mul_inv, ← sqrt_mul (by positivity), ← exp_add]
  congr 3
  · ring
  · field_simp
    ring

lemma corrGaussianPDF_swap (hv : v ≠ 0) (hρ : |ρ| < 1) (x y : ℝ) :
    corrGaussianPDF v ρ (x, y) = corrGaussianPDF v ρ (y, x) := by
  simp only [corrGaussianPDF, mvGaussianPDF, sub_zero]
  rw [quadForm_corrCov hv hρ, quadForm_corrCov hv hρ]
  ring_nf

lemma corrGaussianPDF_eq_comp :
    corrGaussianPDF v ρ = mvGaussianPDF 0 (corrCov v ρ) ∘ MeasurableEquiv.finTwoArrow.symm := by
  funext z
  simp only [corrGaussianPDF, Function.comp_apply]
  congr 1

lemma measurePreserving_finTwoArrow_symm :
    MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (volume.prod volume) volume :=
  MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ)

lemma corrGaussianPDF_isPDF (hv : v ≠ 0) (hρ : |ρ| < 1) :
    IsPDF (volume.prod volume) (corrGaussianPDF v ρ) := by
  have hT := measurePreserving_finTwoArrow_symm
  have hK := mvGaussianPDF_isPDF (corrCov_posDef hv hρ) 0
  rw [corrGaussianPDF_eq_comp]
  exact ⟨hK.measurable.comp (MeasurableEquiv.measurable _), fun _ => hK.nonneg _,
    hT.integrable_comp_of_integrable hK.integrable,
    by rw [← hK.integral_eq_one]; exact hT.integral_comp' _⟩

lemma marginalFst_corrGaussianPDF (hv : v ≠ 0) (hρ : |ρ| < 1) :
    marginalFst volume (corrGaussianPDF v ρ) = gaussianPDFReal 0 v := by
  funext x
  simp only [marginalFst, corrGaussianPDF_eq hv hρ]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ (condVar_ne_zero hv hρ), mul_one]

lemma marginalSnd_corrGaussianPDF (hv : v ≠ 0) (hρ : |ρ| < 1) :
    marginalSnd volume (corrGaussianPDF v ρ) = gaussianPDFReal 0 v := by
  rw [← marginalFst_corrGaussianPDF hv hρ]
  funext y
  simp only [marginalSnd, marginalFst]
  exact integral_congr_ae (Eventually.of_forall fun x => corrGaussianPDF_swap hv hρ x y)

lemma diffEntropy_corrGaussianPDF (hv : v ≠ 0) (hρ : |ρ| < 1) :
    diffEntropy (volume.prod volume) (corrGaussianPDF v ρ) =
      1 / 2 * log ((2 * π * exp 1) ^ 2 * (v ^ 2 * (1 - ρ ^ 2))) := by
  rw [corrGaussianPDF_eq_comp, diffEntropy]
  change ∫ x, negMulLog (mvGaussianPDF 0 (corrCov v ρ) (MeasurableEquiv.finTwoArrow.symm x))
    ∂(volume.prod volume) = _
  rw [measurePreserving_finTwoArrow_symm.integral_comp'
    (fun x => negMulLog (mvGaussianPDF 0 (corrCov v ρ) x)), ← diffEntropy,
    diffEntropy_mvGaussianPDF (corrCov_posDef hv hρ), Fintype.card_fin, det_corrCov]

/-- **Example 8.5.1 (Mutual information between correlated Gaussian random variables), (8.56).**
For `(X, Y) ∼ N(0, K)` with variances `σ²` and correlation `ρ`, `h(X) = h(Y) = ½ log (2πe)σ²`,
`h(X, Y) = ½ log (2πe)² σ⁴ (1 - ρ²)`, and `I(X; Y) = -½ log (1 - ρ²)`. -/
theorem example_8_5_1 (hv : v ≠ 0) (hρ : |ρ| < 1) :
    diffEntropy volume (marginalFst volume (corrGaussianPDF v ρ)) =
        1 / 2 * log (2 * π * exp 1 * v) ∧
      diffEntropy volume (marginalSnd volume (corrGaussianPDF v ρ)) =
        1 / 2 * log (2 * π * exp 1 * v) ∧
      diffEntropy (volume.prod volume) (corrGaussianPDF v ρ) =
        1 / 2 * log ((2 * π * exp 1) ^ 2 * (v ^ 2 * (1 - ρ ^ 2))) ∧
      mutualInfoPDF volume volume (corrGaussianPDF v ρ) = -(1 / 2) * log (1 - ρ ^ 2) := by
  have hf := corrGaussianPDF_isPDF hv hρ
  have hX : diffEntropy volume (marginalFst volume (corrGaussianPDF v ρ)) =
      1 / 2 * log (2 * π * exp 1 * v) := by
    rw [marginalFst_corrGaussianPDF hv hρ, diffEntropy_gaussianPDFReal 0 hv]
  have hY : diffEntropy volume (marginalSnd volume (corrGaussianPDF v ρ)) =
      1 / 2 * log (2 * π * exp 1 * v) := by
    rw [marginalSnd_corrGaussianPDF hv hρ, diffEntropy_gaussianPDFReal 0 hv]
  have hXY := diffEntropy_corrGaussianPDF hv hρ
  refine ⟨hX, hY, hXY, ?_⟩
  have iXY : Integrable (fun z => negMulLog (corrGaussianPDF v ρ z)) (volume.prod volume) := by
    rw [corrGaussianPDF_eq_comp]
    exact measurePreserving_finTwoArrow_symm.integrable_comp_of_integrable
      (integrable_negMulLog_mvGaussianPDF (corrCov_posDef hv hρ) 0)
  have iX : Integrable fun x => negMulLog (marginalFst volume (corrGaussianPDF v ρ) x) := by
    rw [marginalFst_corrGaussianPDF hv hρ]
    exact integrable_negMulLog_gaussianPDFReal 0 hv
  have iY : Integrable fun y => negMulLog (marginalSnd volume (corrGaussianPDF v ρ) y) := by
    rw [marginalSnd_corrGaussianPDF hv hρ]
    exact integrable_negMulLog_gaussianPDFReal 0 hv
  have hv' : (0 : ℝ) < v := by positivity
  have h1 := one_sub_sq_pos hρ
  rw [mutualInfoPDF_eq_add_sub hf iXY iX iY, hX, hY, hXY,
    show (2 * π * exp 1) ^ 2 * ((v : ℝ) ^ 2 * (1 - ρ ^ 2)) =
      (2 * π * exp 1 * v) ^ 2 * (1 - ρ ^ 2) by ring,
    log_mul (by positivity) h1.ne', log_pow]
  push_cast
  ring

/-- **Example 8.5.1, `ρ = 0`.** Uncorrelated jointly normal random variables are independent,
and their mutual information is `0`. -/
theorem example_8_5_1_indep (hv : v ≠ 0) :
    (corrGaussianPDF v 0 = fun z => marginalFst volume (corrGaussianPDF v 0) z.1 *
        marginalSnd volume (corrGaussianPDF v 0) z.2) ∧
      mutualInfoPDF volume volume (corrGaussianPDF v 0) = 0 := by
  have h0 : |(0 : ℝ)| < 1 := by norm_num
  refine ⟨?_, by simp [(example_8_5_1 hv h0).2.2.2]⟩
  funext z
  rw [marginalFst_corrGaussianPDF hv h0, marginalSnd_corrGaussianPDF hv h0,
    corrGaussianPDF_eq hv h0, zero_mul, show condVar v 0 = v by simp [condVar]]

end Correlated

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems of Chapter 8.
-/

/-- **Theorem 8.2.1 (AEP for continuous random variables).** -/
alias theorem_8_2_1 := tendstoInMeasure_sampleDiffEntropy

/-- **Theorem 8.2.1 (AEP for continuous random variables)**, with probability `1`. -/
alias theorem_8_2_1_ae := tendsto_sampleDiffEntropy_ae

/-- **Theorem 8.2.2, property 1.** -/
alias theorem_8_2_2_prob := eventually_prob_diffTypicalSet_gt

/-- **Theorem 8.2.2, property 2.** -/
alias theorem_8_2_2_volume_le := volume_diffTypicalSet_le

/-- **Theorem 8.2.2, property 3.** -/
alias theorem_8_2_2_volume_ge := eventually_volume_diffTypicalSet_ge

/-- **Theorem 8.2.3.** -/
alias theorem_8_2_3 := eventually_volume_gt_of_prob_ge

/-- **Theorem 8.3.1.** -/
alias theorem_8_3_1 := tendsto_entropy_quantPMF_add_log

/-- **Theorem 8.4.1 (Entropy of a multivariate normal distribution).** -/
alias theorem_8_4_1 := diffEntropy_mvGaussianPDF

/-- **Theorem 8.6.1.** -/
alias theorem_8_6_1 := relEntropyPDF_nonneg

/-- **Theorem 8.6.1 (equality case).** -/
alias theorem_8_6_1_eq_iff := relEntropyPDF_eq_zero_iff

/-- **Theorem 8.6.2 (Chain rule for differential entropy).** -/
alias theorem_8_6_2 := diffEntropy_eq_sum_condDiffEntropyLast

/-- **Theorem 8.6.3.** -/
alias theorem_8_6_3 := diffEntropy_comp_sub

/-- **Theorem 8.6.4.** -/
alias theorem_8_6_4 := diffEntropy_scale

/-- **Theorem 8.6.5.** -/
alias theorem_8_6_5 := diffEntropy_le_of_covariance

/-- **Theorem 8.6.5 (equality case).** -/
alias theorem_8_6_5_eq_iff := diffEntropy_eq_of_covariance_iff

/-- **Theorem 8.6.6 (Estimation error and differential entropy).** -/
alias theorem_8_6_6 := exp_two_mul_diffEntropy_div_le

/-- **Theorem 8.6.6 (equality case).** -/
alias theorem_8_6_6_eq_iff := exp_two_mul_diffEntropy_div_eq_iff

end InfoTheory.CoverThomas
