/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture11
public import InfoTheoryLib.Network.MDCases

/-!
# Lecture 14 of El Gamal and Kim: the binary examples

This file proves the two examples of Lecture 14 for a Bernoulli source with Hamming distortion.

## Main statements

* `md_bernoulli_no_excess`: `(R₁, R₂) = (1/2, 1/2)` has the distortions
  `(D₀, D₁, D₂) = (0, (√2 - 1)/2, (√2 - 1)/2)`, pages 14-9 and 14-10.
* `md_bernoulli_lower`: `1/2 ≥ 1 - H(D)` for the rate pair `(1/2, 1/2)`, page 14-9.
* `isSuccessivelyRefinable_bernoulli`: a Bernoulli source is successively refinable under Hamming
  distortion, page 14-24.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 14
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ### The example without excess rate -/

section Excess

/-- The probability `1/√2`. -/
def mdSigma : ℝ := √2 / 2

lemma mdSigma_sq : mdSigma ^ 2 = 1 / 2 := by
  rw [mdSigma, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma mdSigma_pos : 0 < mdSigma := by
  rw [mdSigma]
  positivity

lemma mdSigma_gt : 7 / 10 < mdSigma := by
  nlinarith [mdSigma_sq, mdSigma_pos]

lemma mdSigma_lt : mdSigma < 3 / 4 := by
  nlinarith [mdSigma_sq, mdSigma_pos]

/-- The law of the independent `Bern(1/√2)` random variables `X̂₁`, `X̂₂`, page 14-9. -/
def mdExLaw (z : Bool × Bool) : ℝ := bernoulliPMF mdSigma z.1 * bernoulliPMF mdSigma z.2

lemma mdExLaw_isPMF : IsPMF mdExLaw := by
  have h := mdSigma_lt
  have h0 := mdSigma_pos
  have hb := bernoulliPMF_isPMF h0.le (by linarith : mdSigma ≤ 1)
  refine ⟨fun z => mul_nonneg (hb.nonneg _) (hb.nonneg _), ?_⟩
  simp [mdExLaw, Fintype.sum_prod_type, bernoulliPMF]
  ring

/-- `X = X̂₁ X̂₂`. -/
def mdExX (z : Bool × Bool) : Bool := z.1 && z.2

lemma dist_mdExX : dist mdExLaw mdExX = bernoulliPMF (1 / 2) := by
  have h := mdSigma_sq
  funext b
  cases b
  · simp [dist, mdExLaw, mdExX, Fintype.sum_prod_type, bernoulliPMF]
    nlinarith
  · simp [dist, mdExLaw, mdExX, Fintype.sum_prod_type, bernoulliPMF]
    nlinarith

/-- `H(X) = log 2`. -/
lemma entropy_mdExX : H[mdExX ; mdExLaw] = log 2 := by
  rw [entropyRV, dist_mdExX, entropy_bernoulliPMF, show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
    binEntropy_two_inv]

/-- The bound `σ H(σ) ≥ (1/2) log 2` for `σ = 1/√2`, by concavity of the binary entropy between
`1/2` and `3/4`. -/
lemma half_log_two_le : 1 / 2 * log 2 ≤ mdSigma * binEntropy mdSigma := by
  have hl := log_pos one_lt_two
  have h1 := mdSigma_gt
  have h2 := mdSigma_lt
  have hsq := mdSigma_sq
  have hlog3 : 5 * log 3 ≤ 8 * log 2 := by
    have h : log ((3 : ℝ) ^ 5) ≤ log ((2 : ℝ) ^ 8) := log_le_log (by norm_num) (by norm_num)
    simpa [log_pow] using h
  have h34 : 4 / 5 * log 2 ≤ binEntropy (3 / 4) := by
    have e : binEntropy (3 / 4) = 2 * log 2 - 3 / 4 * log 3 := by
      have e1 : log (3 / 4 : ℝ) = log 3 - 2 * log 2 := by
        rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
        norm_num
      have e2 : log (1 / 4 : ℝ) = - (2 * log 2) := by
        rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
        norm_num
      rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog,
        show (1 - 3 / 4 : ℝ) = 1 / 4 by norm_num, e1, e2]
      ring
    rw [e]
    linarith
  have h12 : binEntropy (1 / 2) = log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
  have hconc := strictConcave_binEntropy.concaveOn.2
    (show (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show 0 ≤ 3 - 4 * mdSigma by linarith) (show 0 ≤ 4 * mdSigma - 2 by linarith) (by ring)
  simp only [smul_eq_mul] at hconc
  have hx : (3 - 4 * mdSigma) * (1 / 2) + (4 * mdSigma - 2) * (3 / 4) = mdSigma := by ring
  rw [hx, h12] at hconc
  have hb : (1.4 - 0.8 * mdSigma) * log 2 ≤ binEntropy mdSigma := by
    have := mul_le_mul_of_nonneg_left h34 (by linarith : (0 : ℝ) ≤ 4 * mdSigma - 2)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hb mdSigma_pos.le
  have e3 : mdSigma * ((1.4 - 0.8 * mdSigma) * log 2) = (1.4 * mdSigma - 0.8 * mdSigma ^ 2) *
    log 2 := by
    ring
  rw [e3, hsq] at hm
  nlinarith

/-- `I(X; X̂₁) ≤ (1/2) log 2`, page 14-10. -/
lemma mutualInfo_mdExX_fst_le : I[mdExX : Prod.fst ; mdExLaw] ≤ 1 / 2 * log 2 := by
  have h1 := mdSigma_gt
  have h2 := mdSigma_lt
  have hsq := mdSigma_sq
  have hb0 : 0 ≤ mdSigma := mdSigma_pos.le
  have hb1 : mdSigma ≤ 1 := by linarith
  have hW : IsChannel fun y : Bool => bernoulliPMF (if y then mdSigma else 0) := fun y => by
    cases y
    · exact bernoulliPMF_isPMF le_rfl zero_le_one
    · exact bernoulliPMF_isPMF hb0 hb1
  have hp := bernoulliPMF_isPMF hb0 hb1
  have hc : H[mdExX | Prod.fst ; mdExLaw] = mdSigma * binEntropy mdSigma := by
    have hj := condEntropy_jointOf hp hW
    have heq : H[mdExX | Prod.fst ; mdExLaw] =
        H[Prod.snd | Prod.fst ; jointOf (bernoulliPMF mdSigma)
          fun y : Bool => bernoulliPMF (if y then mdSigma else 0)] := by
      refine condEntropy_eq_of_dist_pair_eq mdExLaw_isPMF (jointOf_isPMF hp hW) ?_
      rw [dist_pair_fst_snd]
      funext ⟨y, x⟩
      cases y <;> cases x <;>
        simp [dist, pair, mdExLaw, mdExX, jointOf, Fintype.sum_prod_type, bernoulliPMF]
      all_goals ring
    rw [heq, hj, Fintype.sum_bool]
    simp [entropy_bernoulliPMF, bernoulliPMF]
  rw [mutualInfo_eq_entropy_sub_condEntropy mdExLaw_isPMF, entropy_mdExX, hc]
  linarith [half_log_two_le]

/-- `I(X; X̂₂) ≤ (1/2) log 2`, page 14-10. -/
lemma mutualInfo_mdExX_snd_le : I[mdExX : Prod.snd ; mdExLaw] ≤ 1 / 2 * log 2 := by
  have hsym : I[mdExX : Prod.snd ; mdExLaw] = I[mdExX : Prod.fst ; mdExLaw] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    funext ⟨x, y⟩
    cases y <;> cases x <;>
      simp [dist, pair, mdExLaw, mdExX, Fintype.sum_prod_type, bernoulliPMF]
    all_goals ring
  rw [hsym]
  exact mutualInfo_mdExX_fst_le

/-- `I(X̂₁; X̂₂) = 0`: they are independent. -/
lemma mutualInfo_mdEx_fst_snd : I[(Prod.fst : Bool × Bool → Bool) : Prod.snd ; mdExLaw] = 0 := by
  refine (mutualInfo_eq_zero_iff mdExLaw_isPMF _ _).2 fun a b => ?_
  cases a <;> cases b <;>
    simp [dist, pair, mdExLaw, Fintype.sum_prod_type, bernoulliPMF] <;> ring

/-- **Lecture 14, pages 14-9 and 14-10.** The rate pair `(1/2, 1/2)` has the distortions
`(D₀, D₁, D₂) = (0, (√2 - 1)/2, (√2 - 1)/2)` for a `Bern(1/2)` source with Hamming distortion, which
is better than the simple scheme with `D₁ = D₂ = 1/4` that splits the source sequence. -/
theorem md_bernoulli_no_excess :
    ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ mdRegion (bernoulliPMF (1 / 2)) hammingDistortion hammingDistortion
      hammingDistortion 0 ((√2 - 1) / 2) ((√2 - 1) / 2) := by
  have hl := log_pos one_lt_two
  have hsq := mdSigma_sq
  have hmn : mdSigma * (1 - mdSigma) = (√2 - 1) / 2 := by
    have e : mdSigma * (1 - mdSigma) = mdSigma - mdSigma ^ 2 := by ring
    rw [e, hsq, mdSigma]
    ring
  have h := mem_mdRegion_of_le (X := mdExX) (Y₀ := mdExX) (Y₁ := Prod.fst) (Y₂ := Prod.snd)
    (d₀ := hammingDistortion) (d₁ := hammingDistortion) (d₂ := hammingDistortion) mdExLaw_isPMF
    (fun a b => by simp only [hammingDistortion]; split_ifs <;> norm_num)
    (fun a b => by simp only [hammingDistortion]; split_ifs <;> norm_num)
    (fun a b => by simp only [hammingDistortion]; split_ifs <;> norm_num)
    (R₁ := 1 / 2) (R₂ := 1 / 2) (D₀ := 0) (D₁ := (√2 - 1) / 2) (D₂ := (√2 - 1) / 2)
    mutualInfo_mdExX_fst_le mutualInfo_mdExX_snd_le
    (by
      rw [mutualInfo_mdEx_fst_snd, add_zero, mutualInfo_eq_entropy_sub_condEntropy mdExLaw_isPMF,
        entropy_mdExX]
      have := condEntropy_nonneg mdExLaw_isPMF mdExX (pair mdExX (pair Prod.fst Prod.snd))
      linarith)
    (by simp [hammingDistortion])
    (by
      refine le_of_eq ?_
      rw [← hmn]
      simp [Fintype.sum_prod_type, mdExLaw, mdExX, hammingDistortion, bernoulliPMF])
    (by
      refine le_of_eq ?_
      rw [← hmn]
      simp [Fintype.sum_prod_type, mdExLaw, mdExX, hammingDistortion, bernoulliPMF]
      ring)
  rwa [dist_mdExX] at h

/-- **Lecture 14, page 14-9.** If the rate pair `(1/2, 1/2)` has the distortion `D ≤ 1/2` at decoder
1, then, by the lossy source coding theorem, `1/2 ≥ 1 - H(D)` in bits. -/
theorem md_bernoulli_lower {D₀ D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2)
    (h : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ mdRegion (bernoulliPMF (1 / 2)) hammingDistortion
      hammingDistortion hammingDistortion D₀ D D') :
    log 2 - binEntropy D ≤ 1 / 2 * log 2 := by
  have hP := bernoulliPMF_isPMF (θ := 1 / 2) (by norm_num) (by norm_num)
  have h1 := infoRD_le_of_mem_mdRegion₁ hP h
  have hm : D ≤ min (1 / 2 : ℝ) (1 - 1 / 2) := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, min_self]
    exact hD
  rw [infoRD_bernoulli (by norm_num) (by norm_num) hD0, ite_eq_left hm,
    show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv] at h1
  norm_num at h1 ⊢
  linarith

end Excess

/-! ### Successive refinability -/

section Refinable

/-- The entropy of a row of a binary symmetric channel. -/
lemma entropy_bscKernel (a : ℝ) (y : Bool) : entropy (bscKernel a y) = binEntropy a := by
  rw [← entropy_bernoulliPMF]
  cases y
  · have : bscKernel a false = bernoulliPMF a := by
      funext u
      simp [bscKernel]
    rw [this]
  · simp only [entropy, Fintype.sum_bool, bscKernel, bernoulliPMF]
    simp
    ring

/-- The rate–distortion function at a distortion at least the minimal one is zero, and the constant
reproduction attains it. -/
lemma exists_constant_of_min_le {p D : ℝ} (hD : min p (1 - p) ≤ D) :
    ∃ c : Bool, ∑ x, bernoulliPMF p x * hammingDistortion x c ≤ D := by
  rcases le_total p (1 - p) with h | h
  · refine ⟨false, ?_⟩
    rw [min_eq_left h] at hD
    simpa [Fintype.sum_bool, bernoulliPMF, hammingDistortion] using hD
  · refine ⟨true, ?_⟩
    rw [min_eq_right h] at hD
    simpa [Fintype.sum_bool, bernoulliPMF, hammingDistortion] using hD

/-- The case of a large distortion at decoder 1: the reproduction `X̂₁` is constant. -/
lemma refinable_constant {p D₀ D₁ : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁)
    (hm : min p (1 - p) ≤ D₁) :
    ∃ κ : Bool → Bool × Bool → ℝ, IsChannel κ ∧
      MarkovChain (jointOf (bernoulliPMF p) κ) Prod.fst (fun z => z.2.1) (fun z => z.2.2) ∧
      ∑ z, jointOf (bernoulliPMF p) κ z * hammingDistortion z.1 z.2.1 ≤ D₀ ∧
      ∑ z, jointOf (bernoulliPMF p) κ z * hammingDistortion z.1 z.2.2 ≤ D₁ ∧
      I[Prod.fst : fun z : Bool × Bool × Bool => z.2.1 ; jointOf (bernoulliPMF p) κ] =
        infoRD (bernoulliPMF p) hammingDistortion D₀ ∧
      I[Prod.fst : fun z : Bool × Bool × Bool => z.2.2 ; jointOf (bernoulliPMF p) κ] =
        infoRD (bernoulliPMF p) hammingDistortion D₁ := by
  have hP := bernoulliPMF_isPMF h0 h1
  obtain ⟨q, hq, hc, he⟩ := exists_infoRD_eq (d := hammingDistortion) hP
    (D := D₀) ((minDistortion_hammingDistortion _).trans_le hD₀)
  obtain ⟨c, hcD⟩ := exists_constant_of_min_le hm
  have hμ := jointOf_isPMF hP hq
  have hX : dist (jointOf (bernoulliPMF p) q) Prod.fst = bernoulliPMF p := dist_jointOf_fst hq
  have hR : infoRD (bernoulliPMF p) hammingDistortion D₁ = 0 := by
    rw [infoRD_bernoulli h0 h1 hD₁]
    rcases hm.eq_or_lt with h | h
    · rw [← h, ite_eq_left le_rfl]
      rcases le_total p (1 - p) with h' | h'
      · rw [min_eq_left h', sub_self]
      · rw [min_eq_right h', binEntropy_one_sub, sub_self]
    · exact ite_eq_right (not_le.2 h)
  have hM : I[Prod.fst : (fun _ => c) | Prod.snd ; jointOf (bernoulliPMF p) q] = 0 := by
    have e : H[Prod.fst | pair (fun _ => c) Prod.snd ; jointOf (bernoulliPMF p) q] =
        H[Prod.fst | Prod.snd ; jointOf (bernoulliPMF p) q] :=
      condEntropy_congr_right hμ Prod.fst (fun b : Bool => (c, b))
        (fun a b h => (Prod.mk.inj h).2) (fun _ => rfl)
    rw [condMutualInfo, e, sub_self]
  obtain ⟨κ, hκ, hM', hc₀, hc₁, e₀, e₁⟩ := InfoTheory.exists_markov_channel_of_rv
    (P := bernoulliPMF p) hμ (A := Prod.fst) (B₀ := Prod.snd) (B₁ := fun _ => c) hX hM
  refine ⟨κ, hκ, hM', ?_, ?_, ?_, ?_⟩
  · rw [hc₀]
    rw [expDistortion_eq_sum_jointOf] at hc
    exact hc
  · rw [hc₁]
    have := sum_dist_mul (jointOf (bernoulliPMF p) q) Prod.fst fun x => hammingDistortion x c
    rw [hX] at this
    rw [← this]
    exact hcD
  · rw [e₀]
    exact he
  · rw [e₁, hR]
    exact mutualInfo_const_right' hμ _ c

/-- The law of the backward cascade `X̂₁ → X̂₀ → X`, page 14-24: `X̂₁ ∼ Bern(r)`, `X̂₀ = X̂₁ ⊕ Z₁`
and `X = X̂₀ ⊕ Z₀`, with `Z₁ ∼ Bern(c)` and `Z₀ ∼ Bern(D₀)`. -/
def cascadeLaw (r c D₀ : ℝ) : (Bool × Bool) × Bool → ℝ :=
  jointOf (jointOf (bernoulliPMF r) (bscKernel c)) fun v => bscKernel D₀ v.2

/-- The case of a small distortion at decoder 1: the backward cascade. -/
lemma refinable_cascade {p D₀ D₁ : ℝ} (hD₀ : 0 ≤ D₀) (hD : D₀ ≤ D₁) (hm : D₁ < min p (1 - p)) :
    ∃ κ : Bool → Bool × Bool → ℝ, IsChannel κ ∧
      MarkovChain (jointOf (bernoulliPMF p) κ) Prod.fst (fun z => z.2.1) (fun z => z.2.2) ∧
      ∑ z, jointOf (bernoulliPMF p) κ z * hammingDistortion z.1 z.2.1 ≤ D₀ ∧
      ∑ z, jointOf (bernoulliPMF p) κ z * hammingDistortion z.1 z.2.2 ≤ D₁ ∧
      I[Prod.fst : fun z : Bool × Bool × Bool => z.2.1 ; jointOf (bernoulliPMF p) κ] =
        infoRD (bernoulliPMF p) hammingDistortion D₀ ∧
      I[Prod.fst : fun z : Bool × Bool × Bool => z.2.2 ; jointOf (bernoulliPMF p) κ] =
        infoRD (bernoulliPMF p) hammingDistortion D₁ := by
  have hm₁ : D₁ < p := hm.trans_le (min_le_left _ _)
  have hm₂ : D₁ < 1 - p := hm.trans_le (min_le_right _ _)
  have h0 : 0 ≤ p := by linarith
  have h1 : p ≤ 1 := by linarith
  have hD₁0 : 0 ≤ D₁ := by linarith
  have hD₁h : D₁ < 1 / 2 := by linarith
  have hδ₁ : 0 < 1 - 2 * D₁ := by linarith
  have hδ₀ : 0 < 1 - 2 * D₀ := by linarith
  -- The parameters of the cascade.
  obtain ⟨r, hr⟩ : ∃ r, r = (p - D₁) / (1 - 2 * D₁) := ⟨_, rfl⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = (D₁ - D₀) / (1 - 2 * D₀) := ⟨_, rfl⟩
  have hr' : r * (1 - 2 * D₁) + D₁ = p := by
    rw [hr, div_mul_cancel₀ _ hδ₁.ne']
    ring
  have hc' : c * (1 - D₀) + (1 - c) * D₀ = D₁ := by
    have e : c * (1 - 2 * D₀) = D₁ - D₀ := by
      rw [hcd, div_mul_cancel₀ _ hδ₀.ne']
    linear_combination e
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact div_nonneg (by linarith) hδ₁.le
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hδ₁]
    linarith
  have hc0 : 0 ≤ c := by
    rw [hcd]
    exact div_nonneg (by linarith) hδ₀.le
  have hc1 : c ≤ 1 := by
    rw [hcd, div_le_one hδ₀]
    linarith
  have hD₀1 : D₀ ≤ 1 := by linarith
  have hD₁1 : D₁ ≤ 1 := by linarith
  have hb := bernoulliPMF_isPMF hr0 hr1
  have hch₁ : IsChannel (bscKernel c) := bscKernel_isPMF hc0 hc1
  have hch₀ : IsChannel (bscKernel D₀) := bscKernel_isPMF hD₀ hD₀1
  have hch₂ : IsChannel (bscKernel D₁) := bscKernel_isPMF hD₁0 hD₁1
  have hν := jointOf_isPMF hb hch₁
  have hchv : IsChannel fun v : Bool × Bool => bscKernel D₀ v.2 := fun v => hch₀ v.2
  have hμ : IsPMF (cascadeLaw r c D₀) := jointOf_isPMF hν hchv
  -- The source.
  have hX : dist (cascadeLaw r c D₀) Prod.snd = bernoulliPMF p := by
    funext x
    cases x
    · simp [dist, cascadeLaw, jointOf, Fintype.sum_prod_type, bscKernel, bernoulliPMF]
      linear_combination (2 * r - 1) * hc' - hr'
    · simp [dist, cascadeLaw, jointOf, Fintype.sum_prod_type, bscKernel, bernoulliPMF]
      linear_combination (1 - 2 * r) * hc' + hr'
  have hHX : H[Prod.snd ; cascadeLaw r c D₀] = binEntropy p := by
    rw [entropyRV, hX, entropy_bernoulliPMF]
  -- The conditional entropies.
  have hfst : dist (cascadeLaw r c D₀) Prod.fst = jointOf (bernoulliPMF r) (bscKernel c) :=
    dist_jointOf_fst hchv
  have hHA : H[Prod.snd | Prod.fst ; cascadeLaw r c D₀] = binEntropy D₀ := by
    rw [cascadeLaw, condEntropy_jointOf hν hchv]
    simp only [entropy_bscKernel]
    rw [← sum_mul, hν.sum_eq_one, one_mul]
  have hH₀ : H[Prod.snd | fun z : (Bool × Bool) × Bool => z.1.2 ; cascadeLaw r c D₀] =
      binEntropy D₀ := by
    have h := condEntropy_eq_comp_of_channel hμ Prod.fst Prod.snd Prod.snd hch₀ (by
      rw [dist_pair_fst_snd, hfst]
      rfl)
    rw [← hHA, h]
    rfl
  have hH₁ : H[Prod.snd | fun z : (Bool × Bool) × Bool => z.1.1 ; cascadeLaw r c D₀] =
      binEntropy D₁ := by
    have hj := condEntropy_jointOf hb hch₂
    have heq : H[Prod.snd | fun z : (Bool × Bool) × Bool => z.1.1 ; cascadeLaw r c D₀] =
        H[Prod.snd | Prod.fst ; jointOf (bernoulliPMF r) (bscKernel D₁)] := by
      refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hb hch₂) ?_
      rw [dist_pair_fst_snd]
      funext ⟨a, x⟩
      cases a <;> cases x <;>
        simp [dist, pair, cascadeLaw, jointOf, Fintype.sum_prod_type, bscKernel, bernoulliPMF]
      · linear_combination (-(1 - r)) * hc'
      · linear_combination (1 - r) * hc'
      · linear_combination r * hc'
      · linear_combination (-r) * hc'
    rw [heq, hj]
    simp only [entropy_bscKernel]
    rw [← sum_mul, hb.sum_eq_one, one_mul]
  have hM : I[Prod.snd : (fun z : (Bool × Bool) × Bool => z.1.1) |
      fun z => z.1.2 ; cascadeLaw r c D₀] = 0 := by
    have e : H[Prod.snd | pair (fun z : (Bool × Bool) × Bool => z.1.1) (fun z => z.1.2) ;
        cascadeLaw r c D₀] = binEntropy D₀ := hHA
    rw [condMutualInfo, e, hH₀, sub_self]
  obtain ⟨κ, hκ, hM', hc₀, hc₁, e₀, e₁⟩ := InfoTheory.exists_markov_channel_of_rv
    (P := bernoulliPMF p) hμ (A := Prod.snd) (B₀ := fun z => z.1.2) (B₁ := fun z => z.1.1) hX hM
  refine ⟨κ, hκ, hM', ?_, ?_, ?_, ?_⟩
  · rw [hc₀]
    refine le_of_eq ?_
    simp [cascadeLaw, jointOf, Fintype.sum_prod_type, bscKernel, bernoulliPMF, hammingDistortion]
    ring
  · rw [hc₁]
    refine le_of_eq ?_
    simp [cascadeLaw, jointOf, Fintype.sum_prod_type, bscKernel, bernoulliPMF, hammingDistortion]
    linear_combination hc'
  · rw [e₀, mutualInfo_eq_entropy_sub_condEntropy hμ, hHX, hH₀,
      infoRD_bernoulli h0 h1 hD₀, ite_eq_left (hD.trans hm.le)]
  · rw [e₁, mutualInfo_eq_entropy_sub_condEntropy hμ, hHX, hH₁,
      infoRD_bernoulli h0 h1 hD₁0, ite_eq_left hm.le]

/-- **Lecture 14, page 14-24.** A `Bern(p)` source is successively refinable under Hamming
distortion, by the cascade of backward channels `X = X̂₀ ⊕ Z₀ = (X̂₁ ⊕ Z₁) ⊕ Z₀`, where
`D' * D₀ = D₁`. -/
theorem isSuccessivelyRefinable_bernoulli {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsSuccessivelyRefinable (bernoulliPMF p) (hammingDistortion (α := Bool)) := by
  have hP := bernoulliPMF_isPMF h0 h1
  refine (isSuccessivelyRefinable_iff hP fun a b => ?_).2 fun D₀ D₁ hD₀ hD => ?_
  · simp only [hammingDistortion]
    split_ifs <;> norm_num
  · rw [minDistortion_hammingDistortion] at hD₀
    rcases lt_or_ge D₁ (min p (1 - p)) with hm | hm
    · exact refinable_cascade hD₀ hD hm
    · exact refinable_constant h0 h1 hD₀ (hD₀.trans hD) hm

end Refinable

end InfoTheory.ElGamalKim
