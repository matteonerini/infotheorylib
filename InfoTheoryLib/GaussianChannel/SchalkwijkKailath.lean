/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Code
public import InfoTheoryLib.Network.Gaussian

/-!
# Schalkwijk–Kailath coding

Pages 18-6 to 18-11 of the notes. For an additive noise channel with noiseless feedback, the sender
first sends the message point `θ(m)`, and then refines the receiver's knowledge of the noise `Z₀`.
Every rate below `C(P)` is achievable under an expected power constraint, and for Gaussian noise the
probability of error decays doubly exponentially.

## Main definitions

* `AddFBCode`: a feedback code for an additive noise channel.
* `IsUnitNoise`: a noise law with zero mean and unit variance.
* `skCode`: the Schalkwijk–Kailath code.

## Main statements

* `skCode_power_le`: the expected power constraint.
* `skCode_err_le`: the bound of the remark of page 18-11, for any noise, by Chebyshev's inequality.
* `skCode_err_gaussian_le`: the doubly exponential bound of page 18-9, for Gaussian noise.
* `isAchievableAddFB_of_lt`: **every rate below `C(P)` is achievable**.

## Implementation notes

The notes define the scheme by MMSE estimates. Here it is defined by its linear recursion, which is
what the remarks of pages 18-10 and 18-11 use, and the error after `n` steps is an explicit linear
combination of the noises with `∑ cⱼ² = (1 + P)⁻ⁿ`. Instead of transmitting `θ(m) ∈ [-1, 1]` at the
first time, we use `θ(m) ∈ [-√P, √P]`, so that the power of every transmission is at most `P` and
the total is at most `(n + 1) P` rather than `1 + n P`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real MeasureTheory ProbabilityTheory Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The recursion -/

section Recursion

variable (P : ℝ)

/-- The variance `(1 + P)⁻ⁱ` of the error after `i` steps. -/
def skV (i : ℕ) : ℝ := ((1 + P) ^ i)⁻¹

/-- The scaling `γᵢ₊₁` of the error: `γ² V = P`. -/
def skG (i : ℕ) : ℝ := √(P * (1 + P) ^ i)

/-- The coefficient of the output `Yᵢ₊₁` in the estimate of the receiver. -/
def skA (i : ℕ) : ℝ := √(P * skV P i) / (1 + P)

/-- The coefficients of the error as a linear combination of the noises. -/
def skC : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | k + 1, j => if j = k + 1 then -skA P k else skC k j / (1 + P)

/-- The error after `k` steps. -/
def skE (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => z 0
  | k + 1 => skE z k - skA P k * (skG P k * skE z k + z (k + 1))

variable {P}

lemma skV_pos (hP : 0 ≤ P) (i : ℕ) : 0 < skV P i := by
  have : 0 < 1 + P := by linarith
  simp only [skV]
  positivity

lemma skA_mul_skG (hP : 0 ≤ P) (i : ℕ) : skA P i * skG P i = P / (1 + P) := by
  have h1 : 0 < 1 + P := by linarith
  have hprod : √(P * skV P i) * √(P * (1 + P) ^ i) = P := by
    rw [← sqrt_mul (mul_nonneg hP (skV_pos hP i).le)]
    have : P * skV P i * (P * (1 + P) ^ i) = P ^ 2 := by
      simp only [skV]
      field_simp
    rw [this, sqrt_sq hP]
  simp only [skA, skG]
  rw [div_mul_eq_mul_div, hprod]

lemma skA_sq (hP : 0 ≤ P) (i : ℕ) : skA P i ^ 2 = P * skV P i / (1 + P) ^ 2 := by
  simp only [skA, div_pow]
  rw [sq_sqrt (mul_nonneg hP (skV_pos hP i).le)]

lemma skG_sq (hP : 0 ≤ P) (i : ℕ) : skG P i ^ 2 * skV P i = P := by
  have h1 : 0 < 1 + P := by linarith
  have h0 : 0 ≤ P * (1 + P) ^ i := by positivity
  simp only [skG, skV]
  rw [sq_sqrt h0]
  field_simp

/-- The coefficients vanish after the current time. -/
lemma skC_of_lt : ∀ (k j : ℕ), k < j → skC P k j = 0
  | 0, j, h => by simp [skC]; omega
  | k + 1, j, h => by
    simp only [skC]
    rw [ite_eq_right (by omega : j ≠ k + 1), skC_of_lt k j (by omega), zero_div]

/-- The error is a linear combination of the noises. -/
lemma skE_eq_sum (hP : 0 ≤ P) (z : ℕ → ℝ) :
    ∀ k, skE P z k = ∑ j ∈ range (k + 1), skC P k j * z j
  | 0 => by simp [skE, skC]
  | k + 1 => by
    have h1 : (1 : ℝ) + P ≠ 0 := by linarith
    rw [sum_range_succ]
    have hl : skC P (k + 1) (k + 1) = -skA P k := by simp [skC]
    have hs : ∑ j ∈ range (k + 1), skC P (k + 1) j * z j =
        (∑ j ∈ range (k + 1), skC P k j * z j) / (1 + P) := by
      rw [sum_div]
      refine sum_congr rfl fun j hj => ?_
      have : j ≠ k + 1 := by
        have := mem_range.mp hj
        omega
      simp only [skC, this, ite_false]
      ring
    rw [hs, hl, ← skE_eq_sum hP z k]
    simp only [skE]
    have h₂ := skA_mul_skG hP k
    have h₃ : skA P k * (skG P k * skE P z k + z (k + 1)) =
        (skA P k * skG P k) * skE P z k + skA P k * z (k + 1) := by ring
    rw [h₃, h₂]
    field_simp
    ring

/-- The sum of the squares of the coefficients is the variance. -/
lemma sum_skC_sq (hP : 0 ≤ P) : ∀ k, ∑ j ∈ range (k + 1), skC P k j ^ 2 = skV P k
  | 0 => by simp [skC, skV]
  | k + 1 => by
    have h1 : (1 : ℝ) + P ≠ 0 := by linarith
    rw [sum_range_succ]
    have hl : skC P (k + 1) (k + 1) = -skA P k := by simp [skC]
    have hs : ∑ j ∈ range (k + 1), skC P (k + 1) j ^ 2 =
        (∑ j ∈ range (k + 1), skC P k j ^ 2) / (1 + P) ^ 2 := by
      rw [sum_div]
      refine sum_congr rfl fun j hj => ?_
      have : j ≠ k + 1 := by
        have := mem_range.mp hj
        omega
      simp only [skC, this, ite_false, div_pow]
    rw [hs, hl, sum_skC_sq hP k, neg_sq, skA_sq hP]
    simp only [skV, pow_succ]
    field_simp

end Recursion

/-! ### Feedback codes for additive noise channels -/

/-- **Page 18-6 of [elgamal2010].** A feedback code for the additive noise channel `Yᵢ = Xᵢ + Zᵢ`:
the input at time `k` depends on the message and on the past outputs. -/
structure AddFBCode (M n : ℕ) where
  /-- The encoder. -/
  enc : ∀ k, Fin M → (Fin k → ℝ) → ℝ
  /-- The decoder. -/
  dec : (Fin n → ℝ) → Fin M
  measurable_enc : ∀ k m, Measurable (enc k m)
  measurable_dec : Measurable dec

/-- The noise, indexed by natural numbers. -/
def noiseExt {n : ℕ} (z : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then z ⟨j, h⟩ else 0

namespace AddFBCode

variable {M n : ℕ} (c : AddFBCode M n)

/-- The first `k` outputs, for the message `m` and the noise `z`. -/
def out (m : Fin M) (z : ℕ → ℝ) : ∀ k, Fin k → ℝ
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (out m z k) (c.enc k m (out m z k) + z k)

/-- The input at time `k`, for the message `m` and the noise `z`. -/
def input (m : Fin M) (z : Fin n → ℝ) (k : ℕ) : ℝ := c.enc k m (c.out m (noiseExt z) k)

/-- The probability of error of a message, for the noise law `ν`. -/
def condErr (ν : Measure ℝ) (m : Fin M) : ℝ :=
  (Measure.pi fun _ : Fin n => ν).real {z | c.dec (c.out m (noiseExt z) n) ≠ m}

/-- The average probability of error. -/
def avgErr (ν : Measure ℝ) : ℝ := (∑ m, c.condErr ν m) / M

/-- **The expected power constraint, page 18-6 of [elgamal2010].** -/
def SatisfiesPower (ν : Measure ℝ) (P : ℝ) : Prop :=
  ∀ m, ∑ k : Fin n, ∫ z, c.input m z k ^ 2 ∂(Measure.pi fun _ : Fin n => ν) ≤ n * P

end AddFBCode

/-- A rate, in nats, is achievable with feedback under the expected power constraint. -/
def IsAchievableAddFB (ν : Measure ℝ) (P R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, AddFBCode (2 ^ ⌈(n : ℝ) * R⌉₊) n,
    (∀ n, (c n).SatisfiesPower ν P) ∧ Tendsto (fun n => (c n).avgErr ν) atTop (𝓝 0)

/-- A noise law with zero mean and unit variance. -/
structure IsUnitNoise (ν : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  int : Integrable (fun x : ℝ => x) ν
  int_sq : Integrable (fun x : ℝ => x ^ 2) ν
  mean : ∫ x, x ∂ν = 0
  var : ∫ x, x ^ 2 ∂ν = 1

/-- The standard Gaussian noise. -/
lemma isUnitNoise_gaussian : IsUnitNoise (gaussianReal 0 1) := by
  have hm : MemLp id 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := hm.integrable_sq
  have hint : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := hm.integrable (by norm_num)
  have hmean : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  refine ⟨inferInstance, hint, hsq, hmean, ?_⟩
  have h := variance_eq_sub hm
  rw [variance_id_gaussianReal] at h
  have e₁ : (gaussianReal 0 1)[(id : ℝ → ℝ)] = 0 := hmean
  rw [e₁] at h
  have e₂ : (gaussianReal 0 1)[(id : ℝ → ℝ) ^ 2] = ∫ x, x ^ 2 ∂(gaussianReal 0 1) := rfl
  rw [e₂] at h
  norm_num at h
  linarith

/-! ### Linear combinations of the noises -/

section Linear

variable {N : ℕ} {ν : Measure ℝ}

/-- The second moment of a linear combination of the noises. -/
theorem integral_linear_sq (hν : IsUnitNoise ν) (d : Fin N → ℝ) :
    Integrable (fun z : Fin N → ℝ => (∑ j, d j * z j) ^ 2) (Measure.pi fun _ => ν) ∧
      ∫ z, (∑ j, d j * z j) ^ 2 ∂(Measure.pi fun _ : Fin N => ν) = ∑ j, d j ^ 2 := by
  classical
  have := hν.prob
  let μ := Measure.pi fun _ : Fin N => ν
  have hint₂ : ∀ i j : Fin N, Integrable (fun z : Fin N → ℝ => z i * z j) μ ∧
      ∫ z, z i * z j ∂μ = if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      have e : (fun z : Fin N → ℝ => z i * z i) = fun z => (fun x : ℝ => x ^ 2) (z i) := by
        funext z
        ring
      rw [e]
      refine ⟨integrable_comp_eval (μ := fun _ : Fin N => ν) (i := i) hν.int_sq, ?_⟩
      refine (integral_comp_eval (μ := fun _ : Fin N => ν) (i := i)
        hν.int_sq.aestronglyMeasurable).trans ?_
      rw [hν.var]
      simp
    · let f : Fin N → ℝ → ℝ := fun l x => if l = i ∨ l = j then x else 1
      have hprod : ∀ z : Fin N → ℝ, ∏ l, f l (z l) = z i * z j := by
        intro z
        rw [← Finset.prod_subset (Finset.subset_univ {i, j}) (fun l _ hl => by
          have : ¬ (l = i ∨ l = j) := by simpa using hl
          simp [f, this])]
        rw [Finset.prod_pair h]
        simp [f]
      have hf : ∀ l, Integrable (f l) ν := by
        intro l
        by_cases hl : l = i ∨ l = j
        · simpa [f, hl] using hν.int
        · simp [f, hl]
      constructor
      · have := Integrable.fintype_prod (f := f) (μ := fun _ => ν) hf
        simpa only [hprod] using this
      · simp_rw [← hprod]
        rw [integral_fintype_prod_eq_prod]
        rw [ite_eq_right h]
        refine Finset.prod_eq_zero (mem_univ i) ?_
        simpa [f] using hν.mean
  have hexp : ∀ z : Fin N → ℝ, (∑ j, d j * z j) ^ 2 = ∑ i, ∑ j, d i * d j * (z i * z j) := by
    intro z
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  simp_rw [hexp]
  constructor
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint₂ i j).1.const_mul _
  · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint₂ i j).1.const_mul _]
    refine sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint₂ i j).1.const_mul _]
    simp_rw [integral_const_mul, (hint₂ i _).2]
    simp [sq]

/-- **Chebyshev's inequality, for a linear combination of the noises.** -/
theorem prob_linear_ge_le (hν : IsUnitNoise ν) (d : Fin N → ℝ) {t : ℝ} (ht : 0 < t) :
    (Measure.pi fun _ : Fin N => ν).real {z | t ≤ |∑ j, d j * z j|} ≤ (∑ j, d j ^ 2) / t ^ 2 := by
  have := hν.prob
  obtain ⟨h₁, h₂⟩ := integral_linear_sq (N := N) hν d
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := Measure.pi fun _ : Fin N => ν)
    (Filter.Eventually.of_forall fun z => sq_nonneg _) h₁ (t ^ 2)
  rw [h₂] at hm
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_) (by positivity)) hm
  intro z hz
  have hz' : t ≤ |∑ j, d j * z j| := hz
  change t ^ 2 ≤ (∑ j, d j * z j) ^ 2
  rw [← sq_abs (∑ j, d j * z j)]
  exact pow_le_pow_left₀ ht.le hz' 2

/-- **The tail of a linear combination of Gaussian noises.** -/
theorem prob_linear_ge_le_gaussian (d : Fin N → ℝ) {t : ℝ} (ht : 0 < t)
    (hd : 0 < ∑ j, d j ^ 2) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).real {z | t ≤ |∑ j, d j * z j|} ≤
      2 * exp (-(t ^ 2 / (2 * ∑ j, d j ^ 2))) := by
  let μ := Measure.pi fun _ : Fin N => gaussianReal 0 1
  set v := ∑ j, d j ^ 2 with hv
  -- the moment generating function
  have hmgf : ∀ (e : Fin N → ℝ) (s : ℝ), Integrable (fun z : Fin N → ℝ => exp (s * ∑ j, e j * z j))
    μ ∧
      mgf (fun z : Fin N → ℝ => ∑ j, e j * z j) μ s = exp (s ^ 2 * (∑ j, e j ^ 2) / 2) := by
    intro e s
    have hprod : ∀ z : Fin N → ℝ, exp (s * ∑ j, e j * z j) = ∏ j, exp ((s * e j) * z j) := by
      intro z
      rw [← exp_sum, mul_sum]
      exact congrArg exp (sum_congr rfl fun j _ => by ring)
    simp_rw [hprod]
    constructor
    · exact Integrable.fintype_prod (f := fun j x => exp ((s * e j) * x)) (μ := fun _ =>
      gaussianReal 0 1)
        fun j => integrable_exp_mul_gaussianReal _
    · simp only [mgf]
      simp_rw [hprod]
      rw [integral_fintype_prod_eq_prod (f := fun j x => exp ((s * e j) * x))]
      have hone : ∀ c : ℝ, ∫ x, exp (c * x) ∂(gaussianReal 0 1) = exp (c ^ 2 / 2) := by
        intro c
        have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) c
        simp only [mgf, id] at this
        rw [this]
        congr 1
        simp
      simp_rw [hone]
      rw [← exp_sum]
      congr 1
      rw [mul_sum, sum_div]
      exact sum_congr rfl fun j _ => by ring
  have hs : 0 ≤ t / v := by positivity
  have hone : ∀ e : Fin N → ℝ, ∑ j, e j ^ 2 = v →
      μ.real {z | t ≤ ∑ j, e j * z j} ≤ exp (-(t ^ 2 / (2 * v))) := by
    intro e he
    obtain ⟨hi, hm⟩ := hmgf e (t / v)
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun z => ∑ j, e j * z j) t hs hi
    rw [hm, he, ← exp_add] at h
    refine h.trans (le_of_eq (congrArg exp ?_))
    field_simp
    ring
  have hsub : {z : Fin N → ℝ | t ≤ |∑ j, d j * z j|} ⊆
      {z | t ≤ ∑ j, d j * z j} ∪ {z | t ≤ ∑ j, (-d j) * z j} := by
    intro z hz
    have hz' : t ≤ |∑ j, d j * z j| := hz
    rcases le_abs.mp hz' with h | h
    · exact Or.inl h
    · right
      change t ≤ ∑ j, (-d j) * z j
      simp only [neg_mul, sum_neg_distrib]
      exact h
  calc _ ≤ μ.real ({z | t ≤ ∑ j, d j * z j} ∪ {z | t ≤ ∑ j, (-d j) * z j}) := measureReal_mono hsub
    _ ≤ μ.real {z | t ≤ ∑ j, d j * z j} + μ.real {z | t ≤ ∑ j, (-d j) * z j} :=
        measureReal_union_le _ _
    _ ≤ _ := by
        have h₁ := hone d rfl
        have h₂ := hone (fun j => -d j) (by simp [hv])
        linarith

end Linear

/-! ### The code -/

section Code

variable {M : ℕ} {P : ℝ}

/-- **Page 18-6 of [elgamal2010].** The message point `θ(m) ∈ [-√P, √P]`: the midpoints of `M` equal
intervals. -/
def skTheta (M : ℕ) (P : ℝ) (m : Fin M) : ℝ := √P * ((2 * m + 1 - M) / M)

/-- **Pages 18-6 and 18-7 of [elgamal2010].** The encoder: `θ(m)` at the first time, and then the
scaled error of the receiver. -/
def skEnc (M : ℕ) (P : ℝ) : ∀ k, Fin M → (Fin k → ℝ) → ℝ
  | 0, m, _ => skTheta M P m
  | k + 1, m, y => skG P k * (noiseExt y 0 - skTheta M P m -
      ∑ j ∈ range k, skA P j * noiseExt y (j + 1))

/-- The estimate of the receiver of the message point. -/
def skHat (n : ℕ) (P : ℝ) (y : Fin n → ℝ) : ℝ :=
  noiseExt y 0 - ∑ j ∈ range (n - 1), skA P j * noiseExt y (j + 1)

/-- The closest message point. -/
def skIdx (M : ℕ) [NeZero M] (P x : ℝ) : Fin M :=
  ⟨min ⌊(x / √P + 1) * M / 2⌋₊ (M - 1), by
    have := NeZero.pos M
    omega⟩

lemma measurable_noiseExt {n : ℕ} (j : ℕ) : Measurable fun y : Fin n → ℝ => noiseExt y j := by
  by_cases h : j < n
  · simp only [noiseExt, h, dite_true]
    exact measurable_pi_apply _
  · simp only [noiseExt, h, dite_false]
    exact measurable_const

/-- **The Schalkwijk–Kailath code.** -/
def skCode (M : ℕ) [NeZero M] (P : ℝ) (n : ℕ) : AddFBCode M n where
  enc := skEnc M P
  dec y := skIdx M P (skHat n P y)
  measurable_enc k m := by
    cases k with
    | zero => exact measurable_const
    | succ k =>
      change Measurable fun y : Fin (k + 1) → ℝ => skG P k * (noiseExt y 0 - skTheta M P m -
        ∑ j ∈ range k, skA P j * noiseExt y (j + 1))
      refine (((measurable_noiseExt 0).sub measurable_const).sub ?_).const_mul _
      exact Finset.measurable_sum _ fun j _ => (measurable_noiseExt _).const_mul _
  measurable_dec := by
    have hm : Measurable fun y : Fin n → ℝ => skHat n P y := by
      simp only [skHat]
      refine (measurable_noiseExt 0).sub ?_
      exact Finset.measurable_sum _ fun j _ => (measurable_noiseExt _).const_mul _
    have hf : Measurable fun x : ℝ => ⌊(x / √P + 1) * M / 2⌋₊ :=
      Nat.measurable_floor.comp (by fun_prop)
    have hg : Measurable fun a : ℕ => (⟨min a (M - 1), by
        have := NeZero.pos M
        omega⟩ : Fin M) := measurable_from_top
    exact hg.comp (hf.comp hm)

lemma noiseExt_snoc {k : ℕ} (y : Fin k → ℝ) (a : ℝ) {j : ℕ} (hj : j < k) :
    noiseExt (Fin.snoc (α := fun _ => ℝ) y a) j = noiseExt y j := by
  have h₁ : j < k + 1 := by omega
  simp only [noiseExt, hj, h₁, dite_true]
  have : (⟨j, h₁⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hj⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma noiseExt_snoc_last {k : ℕ} (y : Fin k → ℝ) (a : ℝ) :
    noiseExt (Fin.snoc (α := fun _ => ℝ) y a) k = a := by
  have h₁ : k < k + 1 := by omega
  simp only [noiseExt, h₁, dite_true]
  have : (⟨k, h₁⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [this, Fin.snoc_last]

/-- The output of the channel, for the message `m` and the noise `z`. -/
def skY (M : ℕ) (P : ℝ) (m : Fin M) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => skTheta M P m + z 0
  | j + 1 => skG P j * skE P z j + z (j + 1)

/-- The receiver computes the error. -/
lemma skY_sum (m : Fin M) (z : ℕ → ℝ) : ∀ k,
    z 0 - ∑ j ∈ range k, skA P j * skY M P m z (j + 1) = skE P z k
  | 0 => by simp [skE]
  | k + 1 => by
    rw [sum_range_succ, ← sub_sub, skY_sum m z k]
    rfl

/-- The outputs of the code. -/
lemma skCode_out [NeZero M] (m : Fin M) (z : ℕ → ℝ) (n : ℕ) : ∀ k, ∀ j, j < k →
    noiseExt ((skCode M P n).out m z k) j = skY M P m z j
  | 0, j, h => absurd h (Nat.not_lt_zero j)
  | k + 1, j, h => by
    have ih := skCode_out m z n k
    simp only [AddFBCode.out]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hj | rfl
    · rw [noiseExt_snoc _ _ hj, ih j hj]
    · rw [noiseExt_snoc_last]
      cases j with
      | zero => rfl
      | succ i =>
        have h₀ : noiseExt ((skCode M P n).out m z (i + 1)) 0 = skTheta M P m + z 0 :=
          ih 0 (by omega)
        have hs : ∑ j ∈ range i, skA P j * noiseExt ((skCode M P n).out m z (i + 1)) (j + 1) =
            ∑ j ∈ range i, skA P j * skY M P m z (j + 1) := by
          refine sum_congr rfl fun j hj => ?_
          rw [ih (j + 1) (by have := mem_range.mp hj; omega)]
        change skG P i * (noiseExt ((skCode M P n).out m z (i + 1)) 0 - skTheta M P m -
          ∑ j ∈ range i, skA P j * noiseExt ((skCode M P n).out m z (i + 1)) (j + 1)) + z (i + 1) =
            skY M P m z (i + 1)
        rw [h₀, hs, add_sub_cancel_left, skY_sum]
        rfl

/-- The input of the code. -/
lemma skCode_input [NeZero M] (m : Fin M) {n : ℕ} (z : Fin n → ℝ) (k : ℕ) :
    (skCode M P n).input m z (k + 1) = skG P k * skE P (noiseExt z) k := by
  have ih := skCode_out (P := P) m (noiseExt z) n (k + 1)
  have h₀ : noiseExt ((skCode M P n).out m (noiseExt z) (k + 1)) 0 =
      skTheta M P m + noiseExt z 0 := ih 0 (by omega)
  have hs : ∑ j ∈ range k, skA P j * noiseExt ((skCode M P n).out m (noiseExt z) (k + 1)) (j + 1) =
      ∑ j ∈ range k, skA P j * skY M P m (noiseExt z) (j + 1) := by
    refine sum_congr rfl fun j hj => ?_
    rw [ih (j + 1) (by have := mem_range.mp hj; omega)]
  change skG P k * (noiseExt ((skCode M P n).out m (noiseExt z) (k + 1)) 0 - skTheta M P m -
    ∑ j ∈ range k, skA P j * noiseExt ((skCode M P n).out m (noiseExt z) (k + 1)) (j + 1)) = _
  rw [h₀, hs, add_sub_cancel_left, skY_sum]

/-- The estimate of the receiver is the message point plus the error. -/
lemma skCode_hat [NeZero M] (m : Fin M) (z : ℕ → ℝ) (n : ℕ) :
    skHat (n + 1) P ((skCode M P (n + 1)).out m z (n + 1)) = skTheta M P m + skE P z n := by
  have ih := skCode_out (P := P) m z (n + 1) (n + 1)
  have h₀ : noiseExt ((skCode M P (n + 1)).out m z (n + 1)) 0 = skTheta M P m + z 0 :=
    ih 0 (by omega)
  have hs : ∑ j ∈ range n, skA P j * noiseExt ((skCode M P (n + 1)).out m z (n + 1)) (j + 1) =
      ∑ j ∈ range n, skA P j * skY M P m z (j + 1) := by
    refine sum_congr rfl fun j hj => ?_
    rw [ih (j + 1) (by have := mem_range.mp hj; omega)]
  simp only [skHat, Nat.add_sub_cancel]
  rw [h₀, hs, add_sub_assoc, skY_sum]

/-- The closest message point is the true one, if the error is less than half the distance. -/
lemma skIdx_eq [NeZero M] (hP : 0 < P) (m : Fin M) {e : ℝ} (he : |e| < √P / M) :
    skIdx M P (skTheta M P m + e) = m := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hs : 0 < √P := sqrt_pos.mpr hP
  have hval : (skTheta M P m + e) / √P * 1 + 1 = (2 * m + 1) / M + e / √P := by
    simp only [skTheta]
    field_simp
    ring
  have hx : ((skTheta M P m + e) / √P + 1) * M / 2 = m + (1 / 2 + e * M / (2 * √P)) := by
    have : (skTheta M P m + e) / √P + 1 = (2 * m + 1) / M + e / √P := by simpa using hval
    rw [this]
    field_simp
    ring
  have habs := abs_lt.mp he
  have h₁ : -√P < e * M := by
    have := mul_lt_mul_of_pos_right habs.1 hM
    rwa [neg_mul, div_mul_cancel₀ _ hM.ne'] at this
  have h₂ : e * M < √P := by
    have := mul_lt_mul_of_pos_right habs.2 hM
    rwa [div_mul_cancel₀ _ hM.ne'] at this
  have hd : e * M / (2 * √P) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    constructor
    · rw [lt_div_iff₀ (by positivity)]
      linarith
    · rw [div_lt_iff₀ (by positivity)]
      linarith
  have hfl : ⌊((skTheta M P m + e) / √P + 1) * M / 2⌋₊ = m := by
    rw [hx, Nat.floor_eq_iff (by have := Nat.cast_nonneg (α := ℝ) (m : ℕ); linarith [hd.1])]
    constructor <;> linarith [hd.1, hd.2]
  refine Fin.ext ?_
  simp only [skIdx, hfl]
  have := m.2
  omega

section Analysis

variable [NeZero M] {ν : Measure ℝ}

lemma skTheta_sq_le (hP : 0 ≤ P) (m : Fin M) : skTheta M P m ^ 2 ≤ P := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hm : (m : ℝ) + 1 ≤ M := by exact_mod_cast m.2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  simp only [skTheta, mul_pow]
  rw [sq_sqrt hP]
  have h : ((2 * (m : ℝ) + 1 - M) / M) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  nlinarith

/-- The error as a linear combination of the noises, for `k < N`. -/
lemma skE_noiseExt (hP : 0 ≤ P) {N : ℕ} (z : Fin N → ℝ) {k : ℕ} (hk : k < N) :
    skE P (noiseExt z) k = ∑ j : Fin N, skC P k j * z j := by
  rw [skE_eq_sum hP]
  have h₁ : ∑ j ∈ range (k + 1), skC P k j * noiseExt z j =
      ∑ j ∈ range N, skC P k j * noiseExt z j := by
    refine sum_subset (fun j hj => mem_range.mpr (by have := mem_range.mp hj; omega)) fun j _ hj =>
      ?_
    rw [skC_of_lt k j (by
      have : ¬ j < k + 1 := fun h => hj (mem_range.mpr h)
      omega), zero_mul]
  rw [h₁, ← Fin.sum_univ_eq_sum_range (fun j => skC P k j * noiseExt z j) N]
  refine sum_congr rfl fun j _ => ?_
  simp [noiseExt]

/-- The sum of the squares of the coefficients, for `k < N`. -/
lemma sum_skC_sq_fin (hP : 0 ≤ P) {N k : ℕ} (hk : k < N) :
    ∑ j : Fin N, skC P k j ^ 2 = skV P k := by
  rw [Fin.sum_univ_eq_sum_range (fun j => skC P k j ^ 2) N, ← sum_skC_sq hP k]
  symm
  refine sum_subset (fun j hj => mem_range.mpr (by have := mem_range.mp hj; omega)) fun j _ hj => ?_
  rw [skC_of_lt k j (by
    have : ¬ j < k + 1 := fun h => hj (mem_range.mpr h)
    omega)]
  simp

/-- **The expected power constraint.** Every transmission has power at most `P`. -/
theorem skCode_power_le (hν : IsUnitNoise ν) (hP : 0 ≤ P) (N : ℕ) :
    (skCode M P N).SatisfiesPower ν P := by
  have := hν.prob
  intro m
  have hk : ∀ k : Fin N, ∫ z, (skCode M P N).input m z k ^ 2 ∂(Measure.pi fun _ : Fin N => ν) ≤
    P := by
    rintro ⟨k, hk⟩
    cases k with
    | zero =>
      have h : ∀ z : Fin N → ℝ, (skCode M P N).input m z 0 = skTheta M P m := fun _ => rfl
      simp only [h]
      rw [integral_const]
      simpa using skTheta_sq_le hP m
    | succ i =>
      have hi : i < N := by omega
      simp only [skCode_input]
      have he : ∀ z : Fin N → ℝ, (skG P i * skE P (noiseExt z) i) ^ 2 =
          skG P i ^ 2 * (∑ j : Fin N, skC P i j * z j) ^ 2 := by
        intro z
        rw [skE_noiseExt hP z hi, mul_pow]
      simp_rw [he]
      rw [integral_const_mul, (integral_linear_sq hν _).2, sum_skC_sq_fin hP hi, skG_sq hP]
  calc _ ≤ ∑ _k : Fin N, P := sum_le_sum fun k _ => hk k
    _ = _ := by simp

/-- A decoding error implies that the error is at least half of the distance between the points. -/
lemma skCode_err_subset (hP : 0 < P) (m : Fin M) (n : ℕ) :
    {z : Fin (n + 1) → ℝ | (skCode M P (n + 1)).dec ((skCode M P (n + 1)).out m (noiseExt z) (n +
      1))
      ≠ m} ⊆ {z | √P / M ≤ |∑ j : Fin (n + 1), skC P n j * z j|} := by
  intro z hz
  by_contra hc
  have hc' : |∑ j : Fin (n + 1), skC P n j * z j| < √P / M := not_le.mp hc
  rw [← skE_noiseExt hP.le z (Nat.lt_succ_self n)] at hc'
  refine hz ?_
  change skIdx M P (skHat (n + 1) P _) = m
  rw [skCode_hat]
  exact skIdx_eq hP m hc'

/-- **The remark of page 18-11 of [elgamal2010].** For any noise with zero mean and unit variance,
the probability of error is at most `(1 + P)⁻ⁿ M² / P`, by Chebyshev's inequality. -/
theorem skCode_err_le (hν : IsUnitNoise ν) (hP : 0 < P) (n : ℕ) :
    (skCode M P (n + 1)).avgErr ν ≤ skV P n * M ^ 2 / P := by
  have := hν.prob
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hs : 0 < √P := sqrt_pos.mpr hP
  have hrow : ∀ m : Fin M, (skCode M P (n + 1)).condErr ν m ≤ skV P n * M ^ 2 / P := by
    intro m
    refine (measureReal_mono (skCode_err_subset hP m n)).trans ?_
    refine (prob_linear_ge_le hν _ (by positivity)).trans (le_of_eq ?_)
    rw [sum_skC_sq_fin hP.le (Nat.lt_succ_self n), div_pow, sq_sqrt hP.le]
    field_simp
  rw [AddFBCode.avgErr, div_le_iff₀ hM]
  calc _ ≤ ∑ _m : Fin M, skV P n * M ^ 2 / P := sum_le_sum fun m _ => hrow m
    _ = _ := by simp; ring

/-- **Page 18-9 of [elgamal2010].** For Gaussian noise, the probability of error decays doubly
exponentially: it is at most `2 exp (-P (1 + P)ⁿ / (2 M²))`. -/
theorem skCode_err_gaussian_le (hP : 0 < P) (n : ℕ) :
    (skCode M P (n + 1)).avgErr (gaussianReal 0 1) ≤
      2 * exp (-(P * (1 + P) ^ n / (2 * M ^ 2))) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hs : 0 < √P := sqrt_pos.mpr hP
  have h1 : 0 < 1 + P := by linarith
  have hrow : ∀ m : Fin M, (skCode M P (n + 1)).condErr (gaussianReal 0 1) m ≤
      2 * exp (-(P * (1 + P) ^ n / (2 * M ^ 2))) := by
    intro m
    refine (measureReal_mono (skCode_err_subset hP m n)).trans ?_
    have hv := sum_skC_sq_fin (P := P) hP.le (Nat.lt_succ_self n)
    refine (prob_linear_ge_le_gaussian _ (by positivity) (by rw [hv]; exact skV_pos hP.le n)).trans
      (le_of_eq ?_)
    rw [hv, div_pow, sq_sqrt hP.le]
    congr 3
    simp only [skV]
    field_simp
  rw [AddFBCode.avgErr, div_le_iff₀ hM]
  calc _ ≤ ∑ _m : Fin M, 2 * exp (-(P * (1 + P) ^ n / (2 * M ^ 2))) := sum_le_sum fun m _ => hrow m
    _ = _ := by simp; ring

end Analysis

end Code

/-! ### Achievable rates -/

/-- **Pages 18-6 to 18-11 of [elgamal2010].** For any noise with zero mean and unit variance, every
rate below `C(P)` is achievable with feedback under the expected power constraint. The rate is in
bits and `C(P)` in nats. -/
theorem isAchievableAddFB_of_lt {ν : Measure ℝ} (hν : IsUnitNoise ν) {P R : ℝ} (hP : 0 < P)
    (hR : R * log 2 < gaussCap P) : IsAchievableAddFB ν P R := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have h1 : 0 < 1 + P := by linarith
  have hC : 0 < gaussCap P := by
    simp only [gaussCap]
    have := log_pos (by linarith : 1 < 1 + P)
    linarith
  have hne : ∀ a : ℕ, NeZero (2 ^ a) := fun a => ⟨by positivity⟩
  refine ⟨fun N => skCode (2 ^ ⌈(N : ℝ) * R⌉₊) P N, fun N => skCode_power_le hν hP.le N, ?_⟩
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hgap : 0 < gaussCap P - R' * log 2 := by
    rcases le_total R 0 with h | h
    · rw [hR', max_eq_right h]
      simpa using hC
    · rw [hR', max_eq_left h]
      linarith
  set g := gaussCap P - R' * log 2 with hg
  -- the bound
  have hbound : ∀ n : ℕ, (skCode (2 ^ ⌈((n + 1 : ℕ) : ℝ) * R⌉₊) P (n + 1)).avgErr ν ≤
      exp (2 * (gaussCap P + log 2)) / P * exp (-(2 * g * ((n : ℝ) + 1))) := by
    intro n
    refine (skCode_err_le hν hP n).trans ?_
    set a := ⌈((n + 1 : ℕ) : ℝ) * R⌉₊ with ha
    have hceil : (a : ℝ) ≤ ((n : ℝ) + 1) * R' + 1 := by
      have h₀ : 0 ≤ ((n : ℝ) + 1) * R' := by positivity
      have h₁ : ((n + 1 : ℕ) : ℝ) * R ≤ ((n : ℝ) + 1) * R' := by
        push_cast
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      have h₂ : a ≤ ⌈((n : ℝ) + 1) * R'⌉₊ := Nat.ceil_le_ceil h₁
      have h₃ := Nat.ceil_lt_add_one h₀
      have h₄ : (a : ℝ) ≤ (⌈((n : ℝ) + 1) * R'⌉₊ : ℝ) := by exact_mod_cast h₂
      linarith
    have hv : skV P n = exp (-(n * (2 * gaussCap P))) := by
      have e : 2 * gaussCap P = log (1 + P) := by
        simp only [gaussCap]
        ring
      rw [e, exp_neg, exp_nat_mul, exp_log h1]
      rfl
    have hMsq : (((2 ^ a : ℕ) : ℝ)) ^ 2 = exp (2 * (a * log 2)) := by
      push_cast
      rw [← pow_mul, ← exp_log (by norm_num : (0 : ℝ) < 2), ← exp_nat_mul, exp_log (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hv, hMsq, ← exp_add]
    have hle : -(n * (2 * gaussCap P)) + 2 * (a * log 2) ≤
        2 * (gaussCap P + log 2) + -(2 * g * ((n : ℝ) + 1)) := by
      have h₃ := mul_le_mul_of_nonneg_right hceil hlog2.le
      simp only [hg]
      nlinarith
    calc exp (-(n * (2 * gaussCap P)) + 2 * (a * log 2)) / P
        ≤ exp (2 * (gaussCap P + log 2) + -(2 * g * ((n : ℝ) + 1))) / P :=
          div_le_div_of_nonneg_right (exp_le_exp.mpr hle) hP.le
      _ = _ := by
          rw [exp_add]
          ring
  have hlim : Tendsto (fun n : ℕ => exp (2 * (gaussCap P + log 2)) / P *
      exp (-(2 * g * ((n : ℝ) + 1)))) atTop (𝓝 (exp (2 * (gaussCap P + log 2)) / P * 0)) := by
    refine Tendsto.const_mul _ ?_
    refine tendsto_exp_atBot.comp ?_
    have : Tendsto (fun n : ℕ => (2 * g) * ((n : ℝ) + 1)) atTop atTop :=
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop).const_mul_atTop (by
        positivity)
    exact tendsto_neg_atTop_atBot.comp this
  rw [mul_zero] at hlim
  rw [← tendsto_add_atTop_iff_nat 1]
  refine squeeze_zero (fun n => ?_) hbound hlim
  have := hν.prob
  exact div_nonneg (sum_nonneg fun m _ => measureReal_nonneg) (Nat.cast_nonneg _)

end InfoTheory
