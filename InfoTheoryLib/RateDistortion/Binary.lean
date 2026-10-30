/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Basic
public import InfoTheoryLib.Statistics.Bernoulli
public import InfoTheoryLib.Entropy.Bounds

/-!
# The rate distortion function of a binary source

For a Bernoulli(`θ`) source with Hamming distortion,
`R(D) = H(θ) - H(D)` for `0 ≤ D ≤ min {θ, 1 - θ}` and `R(D) = 0` for larger `D`.

## Main statements

* `minDistortion_hammingDistortion`: with Hamming distortion, `D_min = 0`.
* `binEntropy_sub_le_mutualInfoOf`: (10.15)–(10.18), every test channel with `Pr{X ≠ X̂} ≤ D ≤ 1/2`
  has `I(X; X̂) ≥ H(θ) - H(D)`.
* `infoRD_bernoulli`: **Theorem 10.3.1**.

## Implementation notes

The bound is attained by the joint law of Figure 10.3: `X̂ ∼ Bernoulli(r)` with
`r = (θ - D)/(1 - 2D)` (10.21), and `X = X̂ ⊕ Z` for an independent `Z ∼ Bernoulli(D)`. The test
channel `p(x̂|x)` is obtained from this law by `infoRD_le_mutualInfo`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 10.3.1
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- With Hamming distortion, `D_min = 0`: each symbol can be reproduced exactly. -/
lemma minDistortion_hammingDistortion (p : α → ℝ) :
    minDistortion p (hammingDistortion (α := α)) = 0 := by
  classical
  refine sum_eq_zero fun x _ => ?_
  have : Nonempty α := ⟨x⟩
  have : ⨅ y, hammingDistortion x y = 0 := by
    refine le_antisymm ((ciInf_le_distortion _ x x).trans_eq (by simp [hammingDistortion])) ?_
    exact le_ciInf fun y => by unfold hammingDistortion; split_ifs <;> norm_num
  rw [this, mul_zero]

omit [Fintype α] in
lemma hammingDistortion_nonneg (x y : α) : 0 ≤ hammingDistortion x y := by
  unfold hammingDistortion; split_ifs <;> norm_num

/-- On `Bool`, the Hamming distortion is the indicator of `x ⊕ x̂ = 1`. -/
lemma hammingDistortion_bool (x y : Bool) :
    hammingDistortion x y = if xor x y then 1 else 0 := by
  cases x <;> cases y <;> simp [hammingDistortion]

/-- The law of a `Bool`-valued random variable is Bernoulli with its probability of `true`. -/
lemma dist_eq_bernoulliPMF {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : IsPMF μ) (Z : Ω → Bool) :
    dist μ Z = bernoulliPMF (dist μ Z true) := by
  funext b
  cases b
  · have h := (hμ.dist Z).sum_eq_one
    rw [Fintype.sum_bool] at h
    simp only [bernoulliPMF, Bool.false_eq_true, ↓reduceIte]
    linarith
  · simp [bernoulliPMF]

/-- **(10.15)–(10.18)** For a Bernoulli(`θ`) source and a test channel with
`Pr{X ≠ X̂} ≤ D ≤ 1/2`, `I(X; X̂) = H(θ) - H(X ⊕ X̂ | X̂) ≥ H(θ) - H(X ⊕ X̂) ≥ H(θ) - H(D)`. -/
theorem binEntropy_sub_le_mutualInfoOf {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {q : Bool → Bool → ℝ}
    (hq : IsChannel q) {D : ℝ} (hqD : expDistortion (bernoulliPMF θ) q hammingDistortion ≤ D)
    (hD : D ≤ 1 / 2) : binEntropy θ - binEntropy D ≤ mutualInfoOf (bernoulliPMF θ) q := by
  have hp := bernoulliPMF_isPMF h0 h1
  set μ := jointOf (bernoulliPMF θ) q
  have hμ : IsPMF μ := jointOf_isPMF hp hq
  set Z : Bool × Bool → Bool := fun z => xor z.1 z.2
  -- `H(X | X̂) = H(X ⊕ X̂ | X̂)`.
  have hcond : H[Prod.fst | Prod.snd ; μ] = H[Z | Prod.snd ; μ] := by
    rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
    congr 1
    refine (entropyRV_eq_of_injective μ (fun z : Bool × Bool => (z.1, xor z.2 z.1)) ?_
      fun _ => rfl).symm
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all
  -- `Pr{X ⊕ X̂ = 1} = E d(X, X̂)`.
  set t := dist μ Z true
  have ht : t = expDistortion (bernoulliPMF θ) q hammingDistortion := by
    have h := sum_dist_mul μ Z fun b => if b then (1 : ℝ) else 0
    rw [Fintype.sum_bool] at h
    simp only [↓reduceIte, mul_one, Bool.false_eq_true, mul_zero, add_zero] at h
    change dist μ Z true = _
    rw [h, expDistortion_eq_sum_jointOf]
    exact sum_congr rfl fun z _ => by rw [hammingDistortion_bool]
  have ht0 : 0 ≤ t := dist_nonneg hμ Z true
  have hZ : H[Z ; μ] = binEntropy t := by
    rw [entropyRV, dist_eq_bernoulliPMF hμ Z, entropy_bernoulliPMF]
  have hmono : binEntropy t ≤ binEntropy D :=
    binEntropy_strictMonoOn.monotoneOn ⟨ht0, by linarith⟩ ⟨ht0.trans (ht ▸ hqD), by linarith⟩
      (ht ▸ hqD)
  have hX : H[Prod.fst ; μ] = binEntropy θ := by
    rw [entropyRV, dist_jointOf_fst hq, entropy_bernoulliPMF]
  have hle := condEntropy_le_entropy hμ Z Prod.snd
  rw [mutualInfoOf, mutualInfo_eq_entropy_sub_condEntropy hμ, hX, hcond]
  linarith

/-- The test channel `x̂ ↦ x = x̂ ⊕ Z` with `Z ∼ Bernoulli(D)`, a binary symmetric channel. -/
lemma isChannel_flip {D : ℝ} (h0 : 0 ≤ D) (h1 : D ≤ 1) :
    IsChannel fun (a b : Bool) => bernoulliPMF D (xor a b) := fun a =>
  ⟨fun b => (bernoulliPMF_isPMF h0 h1).nonneg _, by
    cases a <;> simp [bernoulliPMF]⟩

/-- **(10.20)–(10.22)** For `0 ≤ D < min {θ, 1 - θ}`, the joint law of Figure 10.3 attains
`I(X; X̂) = H(θ) - H(D)` with `Pr{X ≠ X̂} = D`. -/
theorem infoRD_bernoulli_le {θ D : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hD0 : 0 ≤ D)
    (hDθ : D ≤ θ) (hDθ' : D ≤ 1 - θ) (hD2 : D < 1 / 2) :
    infoRD (bernoulliPMF θ) hammingDistortion D ≤ binEntropy θ - binEntropy D := by
  have hp := bernoulliPMF_isPMF h0 h1
  set r := (θ - D) / (1 - 2 * D)
  have h2D : 0 < 1 - 2 * D := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) h2D.le
  have hr1 : r ≤ 1 := (div_le_one h2D).2 (by linarith)
  have hr := bernoulliPMF_isPMF hr0 hr1
  set W : Bool → Bool → ℝ := fun a b => bernoulliPMF D (xor a b)
  have hW : IsChannel W := isChannel_flip hD0 (by linarith)
  set μ := jointOf (bernoulliPMF r) W
  have hμ : IsPMF μ := jointOf_isPMF hr hW
  -- (10.20) The output of the test channel is the source.
  have hr_eq : r * (1 - 2 * D) = θ - D := div_mul_cancel₀ _ h2D.ne'
  have hout : outDist (bernoulliPMF r) W = bernoulliPMF θ := by
    funext b
    cases b <;> simp only [outDist, Fintype.sum_bool, W, bernoulliPMF, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    · linear_combination (-1 : ℝ) * hr_eq
    · linear_combination hr_eq
  have hX : dist μ Prod.snd = bernoulliPMF θ := by rw [dist_jointOf_snd, hout]
  have hdist : ∑ z, μ z * hammingDistortion z.2 z.1 = D := by
    simp only [μ, jointOf, W, Fintype.sum_prod_type, Fintype.sum_bool, hammingDistortion_bool,
      bernoulliPMF, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte]
    ring
  have hI : I[Prod.snd : Prod.fst ; μ] = binEntropy θ - binEntropy D := by
    rw [mutualInfo_comm hμ, ← mutualInfoOf, mutualInfoOf_eq hr hW, hout, entropy_bernoulliPMF]
    have hent : ∀ a, entropy (W a) = binEntropy D := fun a => by
      cases a
      · simp only [W, Bool.false_xor]
        exact entropy_bernoulliPMF D
      · have : W true = bernoulliPMF (1 - D) := by
          funext b; cases b <;> simp [W, bernoulliPMF]
        rw [this, entropy_bernoulliPMF, binEntropy_one_sub]
    simp only [hent, ← sum_mul, hr.sum_eq_one, one_mul]
  have h := infoRD_le_mutualInfo (d := hammingDistortion) hp hμ (Y := Prod.fst) hX
  rwa [hdist, hI] at h

/-- **Theorem 10.3.1.** The rate distortion function of a Bernoulli(`θ`) source with Hamming
distortion is `R(D) = H(θ) - H(D)` for `0 ≤ D ≤ min {θ, 1 - θ}` and `0` for
`D > min {θ, 1 - θ}`. -/
theorem infoRD_bernoulli {θ D : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hD0 : 0 ≤ D) :
    infoRD (bernoulliPMF θ) hammingDistortion D =
      if D ≤ min θ (1 - θ) then binEntropy θ - binEntropy D else 0 := by
  have hp := bernoulliPMF_isPMF h0 h1
  -- A constant reproduction has distortion `min {θ, 1 - θ}`.
  have hzero : min θ (1 - θ) ≤ D → infoRD (bernoulliPMF θ) hammingDistortion D = 0 := by
    intro h
    rcases le_total θ (1 - θ) with hθ | hθ
    · refine infoRD_eq_zero hp (y₀ := false) ?_
      simp only [Fintype.sum_bool, bernoulliPMF, hammingDistortion, ↓reduceIte,
        Bool.true_eq_false, Bool.false_eq_true]
      have := min_eq_left hθ
      linarith
    · refine infoRD_eq_zero hp (y₀ := true) ?_
      simp only [Fintype.sum_bool, bernoulliPMF, hammingDistortion, ↓reduceIte,
        Bool.false_eq_true]
      have := min_eq_right hθ
      linarith
  split_ifs with hD
  · rcases hD.lt_or_eq with hlt | heq
    · have hDθ : D < θ := hlt.trans_le (min_le_left _ _)
      have hDθ' : D < 1 - θ := hlt.trans_le (min_le_right _ _)
      have hD2 : D < 1 / 2 := by linarith
      refine le_antisymm (infoRD_bernoulli_le h0 h1 hD0 hDθ.le hDθ'.le hD2) ?_
      obtain ⟨q, hq, hqD, he⟩ := exists_infoRD_eq (d := hammingDistortion) hp
        ((minDistortion_hammingDistortion _).trans_le hD0)
      exact he ▸ binEntropy_sub_le_mutualInfoOf h0 h1 hq hqD hD2.le
    · rw [hzero heq.ge]
      rcases le_total θ (1 - θ) with hθ | hθ
      · rw [heq, min_eq_left hθ, sub_self]
      · rw [heq, min_eq_right hθ, binEntropy_one_sub, sub_self]
  · exact hzero (not_le.1 hD).le

end InfoTheory
