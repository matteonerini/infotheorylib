/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter10
public import InfoTheoryLib.Statistics.Types
public import InfoTheoryLib.Statistics.LargeDeviations
public import InfoTheoryLib.Statistics.ConditionalLimit
public import InfoTheoryLib.Statistics.HypothesisTesting
public import InfoTheoryLib.Statistics.ChernoffInformation
public import InfoTheoryLib.Statistics.FisherInformation
public import InfoTheoryLib.SourceCoding.Universal

/-!
# Cover & Thomas, Chapter 11: Information Theory and Statistics

This file indexes the formalization of Chapter 11 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_11_1_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Types.** A sequence is `x : Fin n → α` on a finite alphabet, its type is `typeOf x`, the types
  with denominator `n` form `types α n`, and `typeClass P n` is the type class `T(P)`. The
  probability `Qⁿ(E)` of a set `E` of distributions is the probability of `typeEvent E n`.
* **Logarithms.** Logarithms are natural: the book's `2^{-nD}` is our `e^{-nD}`, and its
  `1/(2 ln 2)` in Pinsker's inequality is our `1/2`.
* **Relative entropy.** `relEntropyReal P Q` is the finite relative entropy; statements assume
  `P ≪ Q`, or `Q > 0` where continuity in `P` is needed (Sanov's limit, the conditional limit
  theorem, Chernoff information).
* **Estimation.** Section 11.10 is formalized for parametric families on a finite space
  (`ParamFamily`), where differentiating under the sum is automatic; the Gaussian family of
  Example 11.10.2 is treated here. The parameter set `Θ` is open, so that unbiasedness on `Θ` gives
  `∂/∂θ E_θ T = 1`; with `Θ = ℝ` no estimator on a finite space could be unbiased, as `E_θ T` is
  bounded. `ParamFamily.isEfficient_bernoulli` shows that the hypotheses can hold.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 11.1 Method of types
* Definitions: `typeOf`, `types`, `typeClass` (`Statistics.Types`); the probability simplex is
  `{P | IsPMF P}`.
* Example 11.1.1: `example_11_1_1` (here).
* Theorem 11.1.1: `card_types_le`.
* Theorem 11.1.2: `iidPMF_eq_exp_type`; Corollary (11.15): `iidPMF_eq_exp_entropy`.
* Example 11.1.2: `example_11_1_2` (here).
* Theorem 11.1.3: `card_typeClass_le`, `exp_div_le_card_typeClass`; (11.17):
  `card_typeClass_mul_prod_factorial`; (11.23)–(11.32): `prob_typeClass_le_self`, with (11.27)
  `pow_mul_factorial_le`.
* Example 11.1.3, (11.40): `exp_binEntropy_div_le_choose`, with `typeOf_bool` (here).
* Theorem 11.1.4: `prob_typeClass_le`, `exp_div_le_prob_typeClass`.

### 11.2 Law of large numbers
* (11.63)–(11.68) and Theorem 11.2.1: `prob_relEntropy_typeOf_gt_le`,
  `tendstoInProb_relEntropy_typeOf` (`Statistics.LargeDeviations`).
* (11.71), the strongly typical set: `strongTypicalSet` (`AEP.StrongTypicality`).

### 11.3 Universal source coding
* (11.72)–(11.74): `FixedRateCode`, `FixedRateCode.errProb` (`SourceCoding.Universal`).
* (11.75)–(11.83): `adjustedRate`, `universalSet`, `card_universalSet_le`, `universalCode`.
* Theorem 11.3.1: `tendsto_errProb_universalCode`; (11.84)–(11.87), (11.297):
  `errProb_universalCode_le`.

### 11.4 Large deviation theory
* (11.89)–(11.93): `typeEvent`, `prob_typeEvent_eq_sum` (`Statistics.LargeDeviations`).
* Theorem 11.4.1 (Sanov): `prob_typeEvent_le`, `prob_typeEvent_le_sanov` (11.94), with
  `sanovExponent` (11.95); (11.96): `tendsto_log_prob_typeEvent`, using `IsRelInteriorPt` and
  `eventually_neg_sub_le_log_prob`.

### 11.5 Examples of Sanov's theorem
* (11.108)–(11.110), the closest distribution under linear constraints: `tiltedPMF`,
  `relEntropyReal_tiltedPMF_le` (`Statistics.LargeDeviations`), through the Gibbs inequality
  `neg_log_sum_le_relEntropyReal_add` (`RelativeEntropy.Gibbs`).
* Example 11.5.2: `example_11_5_2` (here).
* Example 11.5.3: the exponent `D(Q ‖ Q₀) = I(X; Y)` is `mutualInfoOf_eq_relEntropy`
  (`MutualInformation.Convexity`).

### 11.6 Conditional limit theorem
* Theorem 11.6.1: `relEntropy_pythagorean` (`Statistics.ConditionalLimit`).
* (11.131)–(11.137): `l1Dist`, `l1Dist_eq_two_mul`, `sum_sub_sum_le_l1Dist_div_two`
  (`RelativeEntropy.Pinsker`).
* Lemma 11.6.1: `pinsker`, with the binary case (11.139)–(11.143) `two_mul_sq_le_binary`.
* Theorem 11.6.2: `tendsto_condProb_first_eq`, with (11.155)–(11.170)
  `tendsto_condProb_relEntropy_gt` and `tendsto_condProb_abs_typeOf_sub`; `condProb`.
* Examples 11.6.1 and 11.6.2, (11.150) and (11.173): the conditional distributions are tilted
  distributions, `relEntropyReal_tiltedPMF_le`.

### 11.7 Hypothesis testing
* Theorem 11.7.1 (Neyman–Pearson): `lrRegion`, `lrRegion_err_ineq`, `neyman_pearson`
  (`Statistics.HypothesisTesting`).
* (11.184)–(11.186), the Gaussian likelihood ratio: `gaussian_likelihood_ratio` (here).
* (11.187)–(11.194): `log_iidPMF_div_eq`.
* (11.200), (11.232): the geometric mixtures `geomMix` (`Statistics.ChernoffInformation`).

### 11.8 Chernoff–Stein lemma
* Theorem 11.8.1: `tendstoInProb_log_likelihood`.
* (11.206): `relEntTypicalSet`; Theorem 11.8.2: `relEntTypicalSet_bounds`,
  `tendsto_prob_relEntTypicalSet`, `prob_relEntTypicalSet_le`, `le_prob_relEntTypicalSet`.
* Lemma 11.8.1: `le_prob_of_relEntTypicalSet`.
* Theorem 11.8.3: `steinBeta`, `tendsto_log_steinBeta`.

### 11.9 Chernoff information
* (11.229)–(11.230), (11.240)–(11.243): `bayesErr`, `bayesErr_le`, `bayesErr_eq_map`
  (`Statistics.ChernoffInformation`).
* Theorem 11.9.1: `tendsto_neg_log_bayesErr`; (11.231)–(11.233) and (11.239): `chernoffZ`,
  `chernoffInfo`, `exists_relEntropyReal_geomMix_eq`; (11.244)–(11.252): `min_le_exp_mul_add`,
  `bayesErr_le_chernoffZ_pow`.
* Example 11.9.1, (11.255)–(11.258): `sqrt_gaussian_mul_gaussian` (here).
* Lemma 11.9.1 (Chernoff bound): `prob_ge_le_exp_mul_expect`.

### 11.10 Fisher information and the Cramér–Rao inequality
* Definitions: `ParamFamily`, `ParamFamily.bias`, `ParamFamily.IsUnbiased`,
  `ParamFamily.IsConsistent`, `ParamFamily.Dominates` (11.263), `ParamFamily.score` (11.264),
  `ParamFamily.fisherInfo` (11.270), `ParamFamily.IsEfficient` (`Statistics.FisherInformation`).
* (11.265)–(11.269): `ParamFamily.sum_mul_score`; (11.271)–(11.279): `ParamFamily.iid`,
  `ParamFamily.score_iid`, `ParamFamily.fisherInfo_iid`.
* Theorem 11.10.1: `ParamFamily.cramerRao`; (11.290): `ParamFamily.cramerRao_bias`; an efficient
  estimator for the Bernoulli family: `ParamFamily.isEfficient_bernoulli`.
* Example 11.10.2: `hasDerivAt_log_gaussianPDFReal`, `example_11_10_2` (here).

## Not formalized

* Figures 11.1–11.13 and the chapter summary.
* The convergence with probability 1 in Theorem 11.2.1 (we prove the bound (11.69) and the
  convergence in probability), and the stronger form (11.172) of the conditional limit theorem.
* The numerical values of Examples 11.5.1, 11.5.2 (in bits) and 11.6.2, which need the Lagrange
  multipliers to be computed numerically; Example 11.5.2 is formalized as an identity.
* The heuristic arguments (11.195)–(11.200) and (11.234)–(11.238) based on Sanov's theorem, which
  are replaced by the proofs of Theorems 11.8.3 and 11.9.1; Example 11.9.2 (football).
* Example 11.10.1 (exponential estimators), the multiparameter Cramér–Rao inequality
  (11.291)–(11.292), and the Cramér–Rao inequality for densities (proved for finite families).
* Example 11.10.2 for `n` observations (`J(θ) = n/σ²`, `E(X̄ₙ - θ)² = σ²/n`): only `n = 1` is
  formalized; `fisherInfo_iid` gives `Jₙ = n J` for finite families.
* The second half of Example 11.1.2, the die with pmf `(1/3, 1/3, 1/6, 1/12, 1/12, 0)`, which is an
  instance of `iidPMF_eq_exp_entropy`.
-/

open Real MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## Section 11.1: examples -/

/-- **Example 11.1.1.** The ternary sequence `x = 11321` (symbols `1, 2, 3` are `0, 1, 2`) has type
`(3/5, 1/5, 1/5)`, and its type class has `5!/(3! 1! 1!) = 20` elements. -/
theorem example_11_1_1 :
    typeOf (![0, 0, 2, 1, 0] : Fin 5 → Fin 3) = ![3 / 5, 1 / 5, 1 / 5] ∧
      (typeClass (typeOf (![0, 0, 2, 1, 0] : Fin 5 → Fin 3)) 5).card = 20 := by
  have hc : ∀ a, symbolCount (![0, 0, 2, 1, 0] : Fin 5 → Fin 3) a = ![3, 1, 1] a := by
    intro a
    have h := symbolCount_eq_sum (![0, 0, 2, 1, 0] : Fin 5 → Fin 3) a
    rw [Fin.sum_univ_five] at h
    have h' : (symbolCount (![0, 0, 2, 1, 0] : Fin 5 → Fin 3) a : ℝ) =
        ((![3, 1, 1] a : ℕ) : ℝ) := by
      rw [h]
      fin_cases a <;> norm_num
    exact_mod_cast h'
  refine ⟨?_, ?_⟩
  · funext a
    fin_cases a <;> simp [typeOf, hc]
  · have h := card_typeClass_mul_prod_factorial (![0, 0, 2, 1, 0] : Fin 5 → Fin 3)
    simp only [hc, Fin.prod_univ_three] at h
    simp [Nat.factorial] at h
    omega

/-- **Example 11.1.2.** For a fair die, a particular sequence with `n/6` occurrences of each face
has probability `e^{-nH(1/6, …, 1/6)} = 6^{-n}`. -/
theorem example_11_1_2 {n : ℕ} {x : Fin n → Fin 6} (hx : typeOf x = uniformPMF (Fin 6)) :
    iidPMF (uniformPMF (Fin 6)) n x = exp (-(n * entropy (uniformPMF (Fin 6)))) ∧
      exp (-(n * entropy (uniformPMF (Fin 6)))) = (6 : ℝ)⁻¹ ^ n := by
  refine ⟨iidPMF_eq_exp_entropy uniformPMF_isPMF.nonneg hx, ?_⟩
  rw [entropy_uniformPMF, Fintype.card_fin]
  push_cast
  rw [← exp_log (show (0 : ℝ) < 6⁻¹ ^ n by positivity), log_pow, log_inv]
  ring_nf

/-- The type of a binary sequence with `k` ones is `(1 - k/n, k/n)`. -/
lemma typeOf_bool {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    typeOf x = fun b => if b then (symbolCount x true : ℝ) / n
      else 1 - (symbolCount x true : ℝ) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs := sum_symbolCount x
  rw [Fintype.sum_bool] at hs
  funext b
  cases b
  · simp only [typeOf, Bool.false_eq_true, ↓reduceIte]
    field_simp
    linarith
  · rfl

/-- **Example 11.1.3, (11.40)–(11.53).** For binary sequences,
`e^{nH(k/n)}/(n + 1) ≤ C(n, k) ≤ e^{nH(k/n)}`. -/
theorem exp_binEntropy_div_le_choose {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    exp (n * binEntropy (k / n)) / (n + 1) ≤ n.choose k ∧
      (n.choose k : ℝ) ≤ exp (n * binEntropy (k / n)) := by
  classical
  obtain ⟨x, hx⟩ := exists_symbolCount_eq (α := Bool) (n := n)
    (fun b : Bool => if b then k else n - k)
    (by simp; omega)
  have hx1 : symbolCount x true = k := by simpa using hx true
  have hx0 : symbolCount x false = n - k := by simpa using hx false
  -- `|T(Pₓ)| = C(n, k)`.
  have hcard : (typeClass (typeOf x) n).card = n.choose k := by
    have h := card_typeClass_mul_prod_factorial x
    rw [Fintype.prod_bool, hx1, hx0, ← Nat.choose_mul_factorial_mul_factorial hk,
      ← mul_assoc, mul_assoc, mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  have hH : entropy (typeOf x) = binEntropy (k / n) := by
    rw [typeOf_bool hn x, hx1, ← entropy_bernoulli]
  -- There are at most `n + 1` binary types.
  have htypes : ((types Bool n).card : ℝ) ≤ n + 1 := by
    have hsub : types Bool n ⊆ (range (n + 1)).image fun j : ℕ =>
        fun b : Bool => if b then (j : ℝ) / n else 1 - (j : ℝ) / n := by
      intro P hP
      obtain ⟨y, rfl⟩ := mem_types.1 hP
      exact mem_image.2 ⟨symbolCount y true, mem_range.2 (Nat.lt_succ_of_le (symbolCount_le y _)),
        (typeOf_bool hn y).symm⟩
    have := (card_le_card hsub).trans card_image_le
    rw [card_range] at this
    exact_mod_cast this
  have hlow := exp_div_card_types_le_card_typeClass hn x
  have hup := card_typeClass_le hn x
  rw [hcard, hH] at hlow hup
  have hpos : (0 : ℝ) < (types Bool n).card := by
    exact_mod_cast card_pos.2 ⟨_, typeOf_mem_types x⟩
  refine ⟨le_trans (div_le_div_of_nonneg_left (exp_pos _).le hpos htypes) hlow, hup⟩

/-! ## Section 11.5: Example 11.5.2 -/

/-- **Example 11.5.2 (Coins).** The exponent of the probability of `70%` heads with a fair coin is
`D((0.7, 0.3) ‖ (0.5, 0.5)) = log 2 - H(0.7)`. -/
theorem example_11_5_2 :
    relEntropyReal (bernoulliPMF 0.7) (bernoulliPMF 0.5) = log 2 - binEntropy 0.7 := by
  rw [relEntropyReal, Fintype.sum_bool, binEntropy_eq_mul_log_inv]
  simp only [bernoulliPMF, ↓reduceIte, Bool.false_eq_true]
  rw [show (1 : ℝ) - 0.5 = 2⁻¹ by norm_num, show (0.5 : ℝ) = 2⁻¹ by norm_num,
    div_eq_mul_inv, div_eq_mul_inv, inv_inv, log_mul (by norm_num) (by norm_num),
    log_mul (by norm_num) (by norm_num), log_inv, log_inv]
  ring

/-! ## Section 11.7: the Gaussian likelihood ratio -/

/-- **(11.184)–(11.186)** The likelihood ratio between `N(1, σ²)` and `N(-1, σ²)` is
`∏ᵢ f₁(xᵢ)/f₂(xᵢ) = e^{2 ∑ᵢ xᵢ/σ²}`: the test compares the sample mean with a threshold. -/
theorem gaussian_likelihood_ratio {v : ℝ≥0} (hv : v ≠ 0) {n : ℕ} (x : Fin n → ℝ) :
    (∏ i, gaussianPDFReal 1 v (x i)) / ∏ i, gaussianPDFReal (-1) v (x i) =
      exp (2 * ∑ i, x i / v) := by
  rw [← prod_div_distrib, mul_sum, exp_sum]
  refine prod_congr rfl fun i _ => ?_
  rw [gaussianPDFReal_def, gaussianPDFReal_def, mul_div_mul_left _ _ (by positivity), ← exp_sub]
  congr 1
  have hv' : (v : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ## Section 11.9: Example 11.9.1 -/

/-- **Example 11.9.1, (11.255)–(11.258).** The geometric mixture `√(f₁ f₂)` of `N(1, σ²)` and
`N(-1, σ²)` is `e^{-1/(2σ²)}` times the `N(0, σ²)` density, so the normalized mixture is
`N(0, σ²)`. -/
theorem sqrt_gaussian_mul_gaussian {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    √(gaussianPDFReal 1 v x * gaussianPDFReal (-1) v x) =
      exp (-(1 / (2 * v))) * gaussianPDFReal 0 v x := by
  have hv' : (v : ℝ) ≠ 0 := by positivity
  set c := (√(2 * π * v))⁻¹
  have h : gaussianPDFReal 1 v x * gaussianPDFReal (-1) v x =
      (exp (-(1 / (2 * v))) * gaussianPDFReal 0 v x) ^ 2 := by
    calc gaussianPDFReal 1 v x * gaussianPDFReal (-1) v x
        = c ^ 2 * exp (-(x - 1) ^ 2 / (2 * v) + -(x - -1) ^ 2 / (2 * v)) := by
          rw [gaussianPDFReal_def, gaussianPDFReal_def, exp_add]; ring
      _ = c ^ 2 * exp (2 * (-(1 / (2 * v)) + -(x - 0) ^ 2 / (2 * v))) := by
          congr 2; field_simp; ring
      _ = _ := by
          rw [gaussianPDFReal_def, show exp (2 * (-(1 / (2 * v)) + -(x - 0) ^ 2 / (2 * v))) =
            (exp (-(1 / (2 * v))) * exp (-(x - 0) ^ 2 / (2 * v))) ^ 2 by
              rw [← exp_add, ← exp_nat_mul]; norm_num]
          ring
  rw [h, sqrt_sq (mul_nonneg (exp_pos _).le (gaussianPDFReal_nonneg _ _ _))]

/-! ## Section 11.10: Example 11.10.2 -/

/-- The score of the family `N(θ, σ²)`: `∂/∂θ log φ_θ(x) = (x - θ)/σ²`. -/
theorem hasDerivAt_log_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) (x θ : ℝ) :
    HasDerivAt (fun t => log (gaussianPDFReal t v x)) ((x - θ) / v) θ := by
  have e : (fun t => log (gaussianPDFReal t v x)) =
      fun t => -(log (2 * π * v)) / 2 - (x - t) ^ 2 / (2 * v) := by
    funext t
    rw [log_gaussianPDFReal t hv]
    ring
  rw [e]
  have h := ((hasDerivAt_id' θ).const_sub x).pow 2 |>.div_const (2 * (v : ℝ)) |>.const_sub
    (-(log (2 * π * v)) / 2)
  convert h using 1
  have hv' : (v : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **Example 11.10.2.** For one observation `X ∼ N(θ, σ²)`, the Fisher information
`J(θ) = E_θ ((X - θ)/σ²)²` is `1/σ²`, and the unbiased estimator `T(X) = X` has
`E_θ (X - θ)² = σ² = 1/J(θ)`: it is efficient. -/
theorem example_11_10_2 {v : ℝ≥0} (hv : v ≠ 0) (θ : ℝ) :
    ∫ x, gaussianPDFReal θ v x * ((x - θ) / v) ^ 2 = 1 / v ∧
      ∫ x, gaussianPDFReal θ v x * (x - θ) ^ 2 = v := by
  have hv' : (v : ℝ) ≠ 0 := by positivity
  have h2 : ∫ x, gaussianPDFReal θ v x * (x - θ) ^ 2 = v := by
    have h := (gaussianPDFReal_sub_moments hv θ).2.2.2.1
    simpa [gaussianPDFReal_sub] using h
  refine ⟨?_, h2⟩
  have : (fun x => gaussianPDFReal θ v x * ((x - θ) / v) ^ 2) =
      fun x => (v : ℝ)⁻¹ ^ 2 * (gaussianPDFReal θ v x * (x - θ) ^ 2) := by
    funext x; field_simp
  rw [this, integral_const_mul, h2]
  field_simp

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 11.
-/

/-- **Theorem 11.1.1.** `|𝒫ₙ| ≤ (n + 1)^|𝒳|`. -/
alias theorem_11_1_1 := card_types_le

/-- **Theorem 11.1.2.** `Qⁿ(x) = e^{-n(H(Pₓ) + D(Pₓ‖Q))}`. -/
alias theorem_11_1_2 := iidPMF_eq_exp_type

/-- **Theorem 11.1.3 (upper bound).** `|T(P)| ≤ e^{nH(P)}`. -/
alias theorem_11_1_3 := card_typeClass_le

/-- **Theorem 11.1.3 (lower bound).** `|T(P)| ≥ e^{nH(P)}/(n + 1)^|𝒳|`. -/
alias theorem_11_1_3_lower := exp_div_le_card_typeClass

/-- **Theorem 11.1.4 (upper bound).** `Qⁿ(T(P)) ≤ e^{-nD(P‖Q)}`. -/
alias theorem_11_1_4 := prob_typeClass_le

/-- **Theorem 11.1.4 (lower bound).** `Qⁿ(T(P)) ≥ e^{-nD(P‖Q)}/(n + 1)^|𝒳|`. -/
alias theorem_11_1_4_lower := exp_div_le_prob_typeClass

/-- **Theorem 11.2.1.** `Pr{D(P_{Xⁿ}‖Q) > ε} ≤ (n + 1)^|𝒳| e^{-nε}`. -/
alias theorem_11_2_1 := prob_relEntropy_typeOf_gt_le

/-- **Theorem 11.3.1.** Universal source codes. -/
alias theorem_11_3_1 := tendsto_errProb_universalCode

/-- **Theorem 11.4.1 (Sanov's theorem), (11.94).** -/
alias theorem_11_4_1 := prob_typeEvent_le_sanov

/-- **Theorem 11.4.1 (Sanov's theorem), (11.96).** -/
alias theorem_11_4_1_limit := tendsto_log_prob_typeEvent

/-- **Theorem 11.6.1 (Pythagorean theorem).** `D(P‖Q) ≥ D(P‖P*) + D(P*‖Q)`. -/
alias theorem_11_6_1 := relEntropy_pythagorean

/-- **Lemma 11.6.1 (Pinsker's inequality).** `D(P₁‖P₂) ≥ ½ ‖P₁ - P₂‖₁²`. -/
alias lemma_11_6_1 := pinsker

/-- **Theorem 11.6.2 (Conditional limit theorem).** -/
alias theorem_11_6_2 := tendsto_condProb_first_eq

/-- **Theorem 11.7.1 (Neyman–Pearson lemma).** -/
alias theorem_11_7_1 := neyman_pearson

/-- **Theorem 11.8.1 (AEP for relative entropy).** -/
alias theorem_11_8_1 := tendstoInProb_log_likelihood

/-- **Theorem 11.8.2 (1).** -/
alias theorem_11_8_2_bounds := relEntTypicalSet_bounds

/-- **Theorem 11.8.2 (2).** -/
alias theorem_11_8_2_prob := tendsto_prob_relEntTypicalSet

/-- **Theorem 11.8.2 (3).** -/
alias theorem_11_8_2_upper := prob_relEntTypicalSet_le

/-- **Theorem 11.8.2 (4).** -/
alias theorem_11_8_2_lower := le_prob_relEntTypicalSet

/-- **Lemma 11.8.1.** -/
alias lemma_11_8_1 := le_prob_of_relEntTypicalSet

/-- **Theorem 11.8.3 (Chernoff–Stein lemma).** -/
alias theorem_11_8_3 := tendsto_log_steinBeta

/-- **Theorem 11.9.1 (Chernoff).** -/
alias theorem_11_9_1 := tendsto_neg_log_bayesErr

/-- **Lemma 11.9.1 (Chernoff bound).** -/
alias lemma_11_9_1 := prob_ge_le_exp_mul_expect

/-- **Theorem 11.10.1 (Cramér–Rao inequality).** -/
alias theorem_11_10_1 := ParamFamily.cramerRao

end InfoTheory.CoverThomas
