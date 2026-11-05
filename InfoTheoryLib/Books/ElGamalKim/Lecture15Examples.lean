/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture4
public import InfoTheoryLib.Books.ElGamalKim.Lecture9
public import InfoTheoryLib.Network.JSCCBC
public import InfoTheoryLib.RelativeEntropy.Pinsker

/-!
# Lecture 15 of El Gamal and Kim: the examples

This file proves the examples of Lecture 15 for the binary sources `(U₁, U₂)` with
`p(0, 0) = p(0, 1) = p(1, 1) = 1/3`.

## Main definitions

* `jsTriPMF`: the law of the sources.

## Main statements

* `isLosslessMAC_jsTriPMF`, `erasure_sum_le`, `entropy_jsTriPMF_gt_erasure`: over the binary erasure
  MAC
  the sources can be sent uncoded, although `H(U₁, U₂) > I(X₁, X₂; Y)`, pages 15-5 and 15-6.
* `gkCommon_jsTriPMF`, `mutualInfo_jsTriPMF`, `wynerJ_jsTriPMF`, `common_information_strict`: the
  values
  `K = 0`, `I = log 3 - (4/3) log 2` and `J = (2/3) log 2`, and the strict inequalities on page
    15-25.
* `isLosslessBC_jsTriPMF`, `gray_wyner_blackwell`: over the Blackwell channel the sources can be
  sent
  uncoded, but no rate triple of the Gray–Wyner region fits the channel, page 15-29.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-- **Lecture 15, page 15-5.** The binary sources with `p(0, 0) = p(0, 1) = p(1, 1) = 1/3` and
`p(1, 0) = 0`, with `false = 0` and `true = 1`. -/
def jsTriPMF (z : Bool × Bool) : ℝ := if z = (true, false) then 0 else 1 / 3

lemma jsTriPMF_isPMF : IsPMF jsTriPMF := by
  refine ⟨fun z => ?_, ?_⟩
  · simp only [jsTriPMF]
    split_ifs <;> norm_num
  · simp [jsTriPMF, Fintype.sum_prod_type]
    norm_num

lemma log_one_third : log (1 / 3 : ℝ) = -log 3 := by
  rw [one_div, log_inv]

/-- `H(U₁, U₂) = log 3`. -/
lemma entropy_jsTriPMF : entropy jsTriPMF = log 3 := by
  rw [entropy_eq_sum_negMulLog]
  simp [jsTriPMF, Fintype.sum_prod_type, negMulLog]
  ring

lemma log_three_gt : 4 / 3 * log 2 < log 3 := by
  have h : log ((2 : ℝ) ^ 4) < log ((3 : ℝ) ^ 3) := log_lt_log (by norm_num) (by norm_num)
  simp only [log_pow] at h
  push_cast at h
  linarith

lemma log_three_lt : log 3 < 2 * log 2 := by
  have h : log (3 : ℝ) < log ((2 : ℝ) ^ 2) := log_lt_log (by norm_num) (by norm_num)
  rwa [log_pow] at h

/-! ### The binary erasure MAC -/

/-- **Lecture 15, pages 15-5 and 15-6.** The sources can be sent over the binary erasure MAC with
`X₁ = U₁` and `X₂ = U₂`, with no coding. -/
theorem isLosslessMAC_jsTriPMF : IsLosslessMAC jsTriPMF binaryErasureMAC := by
  refine isLosslessMAC_of_uncoded (f := binaryErasureMACOut) (fun _ _ => rfl) id id
    (fun y => (decide (y = 2), decide (y ≠ 0))) fun z hz => ?_
  obtain ⟨a, b⟩ := z
  cases a <;> cases b
  · simp [binaryErasureMACOut]
  · simp [binaryErasureMACOut]
  · simp [jsTriPMF] at hz
  · simp [binaryErasureMACOut]

/-- `H(p) ≤ (1 - (p - 1/2)²) log 2`, by Pinsker's inequality. -/
lemma binEntropy_le_quadratic {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    binEntropy s ≤ (1 - (s - 1 / 2) ^ 2) * log 2 := by
  have hb := bernoulliPMF_isPMF h0 h1
  have hu := bernoulliPMF_isPMF (θ := 1 / 2) (by norm_num) (by norm_num)
  have hl := log_lt_sub_one_of_pos (x := 2) two_pos (by norm_num)
  have hl0 := log_pos one_lt_two
  have habs : AbsCont (bernoulliPMF s) (bernoulliPMF (1 / 2)) := fun b hb' => by
    have hne : bernoulliPMF (1 / 2) b ≠ 0 := by
      cases b <;> norm_num [bernoulliPMF]
    exact absurd hb' hne
  have hp := pinsker hb hu habs
  have el : l1Dist (bernoulliPMF s) (bernoulliPMF (1 / 2)) = 2 * |s - 1 / 2| := by
    simp only [l1Dist, Fintype.sum_bool, bernoulliPMF, Bool.false_eq_true, ↓reduceIte]
    have : (1 - s - (1 - 1 / 2)) = -(s - 1 / 2) := by ring
    rw [this, abs_neg]
    ring
  have er : relEntropyReal (bernoulliPMF s) (bernoulliPMF (1 / 2)) = log 2 - binEntropy s := by
    rw [← entropy_bernoulliPMF]
    simp only [relEntropyReal, entropy, Fintype.sum_bool, bernoulliPMF, Bool.false_eq_true,
      ↓reduceIte]
    have h12 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [h12]
    have key : ∀ x : ℝ, 0 ≤ x → x * log (x / (1 / 2)) = x * log x + x * log 2 := fun x hx => by
      rcases hx.eq_or_lt with h | h
      · simp [← h]
      · rw [div_eq_mul_inv, log_mul h.ne' (by norm_num)]
        have : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
        rw [this]
        ring
    rw [key s h0, key (1 - s) (by linarith)]
    ring
  rw [el, er, mul_pow, sq_abs] at hp
  nlinarith [sq_nonneg (s - 1 / 2)]

/-- **Lecture 15, page 15-5.** `max_{p(x₁) p(x₂)} I(X₁, X₂; Y) ≤ 3/2` bits for the binary erasure
  MAC.
The sum capacity is attained at `X₁, X₂ ∼ Bern(1/2)`, by `macInfo₁₂_binaryErasureMAC`. -/
theorem erasure_sum_le {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    mutualInfoOf (prodDist (bernoulliPMF p) (bernoulliPMF q)) binaryErasureMAC ≤ 3 / 2 * log 2 := by
  have hP : IsPMF (prodDist (bernoulliPMF p) (bernoulliPMF q)) :=
    (bernoulliPMF_isPMF hp0 hp1).prodDist (bernoulliPMF_isPMF hq0 hq1)
  have hl := log_pos one_lt_two
  rw [mutualInfoOf_eq hP binaryErasureMAC_isChannel]
  have hdet : ∀ x, entropy (binaryErasureMAC x) = 0 := fun x => by
    rw [entropy_eq_sum_negMulLog]
    refine sum_eq_zero fun y _ => ?_
    simp only [binaryErasureMAC, detMAC]
    split_ifs <;> simp [negMulLog]
  simp only [hdet, mul_zero, sum_const_zero, sub_zero]
  set pd := outDist (prodDist (bernoulliPMF p) (bernoulliPMF q)) binaryErasureMAC with hpd
  have hpdP : IsPMF pd := outDist_isPMF hP binaryErasureMAC_isChannel
  have h0 : pd 0 = (1 - p) * (1 - q) := by
    simp [hpd, outDist, prodDist, binaryErasureMAC, detMAC, binaryErasureMACOut,
      Fintype.sum_prod_type, bernoulliPMF]
  have h1 : pd 1 = p + q - 2 * (p * q) := by
    simp [hpd, outDist, prodDist, binaryErasureMAC, detMAC, binaryErasureMACOut,
      Fintype.sum_prod_type, bernoulliPMF]
    ring
  have h2 : pd 2 = p * q := by
    simp [hpd, outDist, prodDist, binaryErasureMAC, detMAC, binaryErasureMACOut,
      Fintype.sum_prod_type, bernoulliPMF]
  obtain ⟨s, hs⟩ : ∃ s, s = (p + q) / 2 := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hent : entropy pd = negMulLog ((1 - p) * (1 - q)) + negMulLog (p + q - 2 * (p * q)) +
      negMulLog (p * q) := by
    rw [entropy_eq_sum_negMulLog, Fin.sum_univ_three, h0, h1, h2]
  rcases hs0.eq_or_lt with hs₀ | hs₀
  · -- `p = q = 0`.
    have hp : p = 0 := by rw [hs] at hs₀; linarith
    have hq : q = 0 := by rw [hs] at hs₀; linarith
    rw [hent, hp, hq]
    have e : negMulLog ((1 - 0) * (1 - 0)) + negMulLog (0 + 0 - 2 * (0 * 0)) + negMulLog (0 * 0) = 0
      := by
      simp [negMulLog]
    rw [e]
    positivity
  rcases hs1.eq_or_lt with hs₁ | hs₁
  · -- `p = q = 1`.
    have hp : p = 1 := by rw [hs] at hs₁; linarith
    have hq : q = 1 := by rw [hs] at hs₁; linarith
    rw [hent, hp, hq]
    have e : negMulLog ((1 - 1) * (1 - 1)) + negMulLog (1 + 1 - 2 * (1 * 1)) + negMulLog (1 * 1) = 0
      := by
      norm_num [negMulLog]
    rw [e]
    positivity
  -- The reference pmf `Bin(2, s)`.
  have hsb : 0 < 1 - s := by linarith
  set r : Fin 3 → ℝ := ![(1 - s) ^ 2, 2 * s * (1 - s), s ^ 2] with hr
  have hr₀ : r 0 = (1 - s) ^ 2 := rfl
  have hr₁ : r 1 = 2 * s * (1 - s) := rfl
  have hr₂ : r 2 = s ^ 2 := rfl
  have hrpos : ∀ y, 0 < r y := fun y => by
    fin_cases y
    · exact hr₀ ▸ pow_pos hsb 2
    · exact hr₁ ▸ mul_pos (mul_pos two_pos hs₀) hsb
    · exact hr₂ ▸ pow_pos hs₀ 2
  have hrP : IsPMF r := ⟨fun y => (hrpos y).le, by
    rw [Fin.sum_univ_three, hr₀, hr₁, hr₂]
    ring⟩
  have hgibbs := relEntropyReal_nonneg' hpdP hrP fun y h => absurd h (hrpos y).ne'
  have hterm : ∀ y, pd y * log (pd y / r y) = -negMulLog (pd y) - pd y * log (r y) := fun y => by
    rcases (hpdP.nonneg y).eq_or_lt with h | h
    · simp [← h]
    · rw [log_div h.ne' (hrpos y).ne', negMulLog]
      ring
  have hcross : entropy pd ≤ -(pd 0 * log (r 0)) - pd 1 * log (r 1) - pd 2 * log (r 2) := by
    rw [relEntropyReal, Fin.sum_univ_three, hterm, hterm, hterm] at hgibbs
    rw [entropy_eq_sum_negMulLog, Fin.sum_univ_three]
    linarith
  have hr0 : log (r 0) = 2 * log (1 - s) := by
    rw [hr₀, log_pow]
    norm_num
  have hr1 : log (r 1) = log 2 + log s + log (1 - s) := by
    rw [hr₁, log_mul (by positivity) hsb.ne', log_mul two_ne_zero hs₀.ne']
  have hr2 : log (r 2) = 2 * log s := by
    rw [hr₂, log_pow]
    norm_num
  rw [hr0, hr1, hr2, h0, h1, h2] at hcross
  have hbin := binEntropy_le_quadratic hs0 hs1
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog] at hbin
  have ha : (1 - p) * (1 - q) + (p + q - 2 * (p * q)) / 2 = 1 - s := by rw [hs]; ring
  have hc : p * q + (p + q - 2 * (p * q)) / 2 = s := by rw [hs]; ring
  have hb : 2 * (s * (1 - s)) ≤ p + q - 2 * (p * q) := by
    rw [hs]
    nlinarith [sq_nonneg (p - q)]
  have hexp : -((1 - p) * (1 - q) * (2 * log (1 - s))) -
      (p + q - 2 * (p * q)) * (log 2 + log s + log (1 - s)) - p * q * (2 * log s) =
      2 * (-(s * log s) + -((1 - s) * log (1 - s))) - (p + q - 2 * (p * q)) * log 2 := by
    linear_combination (-2 * log s) * hc + (-2 * log (1 - s)) * ha
  rw [hexp] at hcross
  have hb' := mul_le_mul_of_nonneg_right hb hl.le
  nlinarith [mul_nonneg (sq_nonneg (s - 1 / 2)) hl.le]

/-- **Lecture 15, page 15-5.** `H(U₁, U₂) = log 3 > 3/2` bits, so separate source and channel coding
cannot send the sources over the binary erasure MAC. -/
theorem entropy_jsTriPMF_gt_erasure : 3 / 2 * log 2 < entropy jsTriPMF := by
  rw [entropy_jsTriPMF]
  have h : log ((2 : ℝ) ^ 3) < log ((3 : ℝ) ^ 2) := log_lt_log (by norm_num) (by norm_num)
  simp only [log_pow] at h
  push_cast at h
  linarith

/-! ### The notions of common information -/

section Common

/-- A family of channels with `X̂ = 0` for `(U₁, U₂) = (0, 0)` and `X̂ = 1` for `(1, 1)`. -/
def jsTriW (q : ℝ) (z : Bool × Bool) : Bool → ℝ :=
  bernoulliPMF (if z = (false, false) then 1 else if z = (true, true) then 0 else q)

lemma jsTriW_isChannel {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsChannel (jsTriW q) := fun z => by
  refine bernoulliPMF_isPMF ?_ ?_ <;> split_ifs <;> first | assumption | norm_num

/-- The mutual information for a channel that is `1` on `(0, 0)` and `0` on `(1, 1)`. -/
lemma mutualInfoOf_tri {W : Bool × Bool → Bool → ℝ} (hW : IsChannel W)
    (h₁ : W (false, false) true = 1) (h₂ : W (true, true) true = 0) :
    mutualInfoOf jsTriPMF W = binEntropy ((1 + W (false, true) true) / 3) -
      1 / 3 * binEntropy (W (false, true) true) := by
  have hb : ∀ z, W z = bernoulliPMF (W z true) := fun z => by
    funext b
    cases b
    · have := (hW z).sum_eq_one
      rw [Fintype.sum_bool] at this
      simp only [bernoulliPMF, Bool.false_eq_true, ↓reduceIte]
      linarith
    · simp [bernoulliPMF]
  rw [mutualInfoOf_eq jsTriPMF_isPMF hW]
  have hout : outDist jsTriPMF W = bernoulliPMF ((1 + W (false, true) true) / 3) := by
    funext b
    have e₁ := (hW (false, false)).sum_eq_one
    have e₂ := (hW (false, true)).sum_eq_one
    have e₃ := (hW (true, true)).sum_eq_one
    rw [Fintype.sum_bool] at e₁ e₂ e₃
    cases b
    · simp [outDist, jsTriPMF, Fintype.sum_prod_type, bernoulliPMF]
      linarith
    · simp [outDist, jsTriPMF, Fintype.sum_prod_type, bernoulliPMF, h₁, h₂]
      ring
  rw [hout, entropy_bernoulliPMF]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, jsTriPMF]
  rw [hb (true, true), hb (false, true), hb (false, false)]
  simp only [entropy_bernoulliPMF, bernoulliPMF, h₁, h₂]
  simp

/-- `f(q) ≥ (2/3) log 2`, by the convexity of the mutual information in the channel. -/
lemma two_thirds_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    2 / 3 * log 2 ≤ binEntropy ((1 + q) / 3) - 1 / 3 * binEntropy q := by
  have hf : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → mutualInfoOf jsTriPMF (jsTriW t) =
      binEntropy ((1 + t) / 3) - 1 / 3 * binEntropy t := fun t ht0 ht1 => by
    have := mutualInfoOf_tri (jsTriW_isChannel ht0 ht1) (by simp [jsTriW, bernoulliPMF])
      (by simp [jsTriW, bernoulliPMF])
    have e : jsTriW t (false, true) true = t := by simp [jsTriW, bernoulliPMF]
    rwa [e] at this
  have hconv := (mutualInfoOf_convex_channel (β := Bool) jsTriPMF_isPMF).2
    (show jsTriW q ∈ {W | IsChannel W} from jsTriW_isChannel h0 h1)
    (show jsTriW (1 - q) ∈ {W | IsChannel W} from jsTriW_isChannel (by linarith) (by linarith))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmix : (1 / 2 : ℝ) • jsTriW q + (1 / 2 : ℝ) • jsTriW (1 - q) = jsTriW (1 / 2) := by
    funext z b
    obtain ⟨z₁, z₂⟩ := z
    cases z₁ <;> cases z₂ <;> cases b <;> simp [jsTriW, bernoulliPMF] <;> ring
  simp only [hmix, smul_eq_mul] at hconv
  rw [hf _ (by norm_num) (by norm_num), hf q h0 h1, hf _ (by linarith) (by linarith)] at hconv
  have e1 : binEntropy ((1 + (1 - q)) / 3) = binEntropy ((1 + q) / 3) := by
    rw [← binEntropy_one_sub]
    congr 1
    ring
  have e2 : binEntropy (1 - q) = binEntropy q := binEntropy_one_sub q
  rw [e1, e2] at hconv
  have e3 : binEntropy ((1 + 1 / 2) / 3) = log 2 := by
    rw [show ((1 + 1 / 2) / 3 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
  have e4 : binEntropy (1 / 2) = log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
  rw [e3, e4] at hconv
  linarith

/-- **Lecture 15, page 15-26: the lower bound.** If `I(U₁; U₂|V) = 0`, then `I(U₁, U₂; V) ≥ 2/3`
  bits.
Conditionally on `V = v`, the pair `(1, 0)` of probability zero forces `U₁ = 0` or `U₂ = 1`. -/
theorem two_thirds_le_gwInfo {υ : Type*} [Fintype υ] {κ : Bool × Bool → υ → ℝ} (hκ : IsChannel κ)
    (h : gwResidual jsTriPMF κ = 0) : 2 / 3 * log 2 ≤ gwInfo jsTriPMF κ := by
  classical
  have hP := jsTriPMF_isPMF
  have hμ := jointOf_isPMF hP hκ
  set μ := jointOf jsTriPMF κ with hμd
  set U₁ : (Bool × Bool) × υ → Bool := fun z => z.1.1
  set U₂ : (Bool × Bool) × υ → Bool := fun z => z.1.2
  have hci : CondIndep μ U₁ U₂ Prod.snd := by
    refine (condMutualInfo_eq_zero_iff hμ _ _ _).1 ?_
    rw [condMutualInfo_eq_gwResidual hP hκ]
    exact h
  -- The value of the law on the pairs.
  have hle₁ : ∀ a b v, jsTriPMF (a, b) * κ (a, b) v ≤ dist μ (pair U₁ Prod.snd) (a, v) := fun a b v
    => by
    have := le_dist_apply hμ (pair U₁ Prod.snd) ((a, b), v)
    exact this
  have hle₂ : ∀ a b v, jsTriPMF (a, b) * κ (a, b) v ≤ dist μ (pair U₂ Prod.snd) (b, v) := fun a b v
    => by
    have := le_dist_apply hμ (pair U₂ Prod.snd) ((a, b), v)
    exact this
  -- For every `v`, `P{U₁ = 1, V = v} = 0` or `P{U₂ = 0, V = v} = 0`.
  have hkey : ∀ v, dist μ (pair U₁ Prod.snd) (true, v) = 0 ∨
      dist μ (pair U₂ Prod.snd) (false, v) = 0 := fun v => by
    by_cases hv : dist μ Prod.snd v = 0
    · left
      have := dist_pair_le_right hμ U₁ Prod.snd true v
      exact le_antisymm (hv ▸ this) (dist_nonneg hμ _ _)
    have h0 : dist μ (pair (pair U₁ U₂) Prod.snd) ((true, false), v) = 0 := by
      unfold dist
      refine sum_eq_zero fun w _ => ?_
      obtain ⟨⟨a, b⟩, c⟩ := w
      split_ifs with hw
      · have h1 : a = true := congrArg (fun t : (Bool × Bool) × υ => t.1.1) hw
        have h2 : b = false := congrArg (fun t : (Bool × Bool) × υ => t.1.2) hw
        subst h1 h2
        change jsTriPMF (true, false) * κ (true, false) c = 0
        simp [jsTriPMF]
      · rfl
    have hc := hci true false v
    have e0 : condDist μ (pair U₁ U₂) Prod.snd v (true, false) = 0 := by
      rw [condDist]
      have e : dist μ (pair Prod.snd (pair U₁ U₂)) (v, (true, false)) =
          dist μ (pair (pair U₁ U₂) Prod.snd) ((true, false), v) := dist_pair_swap _ _ _ _ _
      rw [e, h0, zero_div]
    rw [e0] at hc
    rcases mul_eq_zero.1 hc.symm with h1 | h1
    · left
      rw [condDist, div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · have e : dist μ (pair Prod.snd U₁) (v, true) = dist μ (pair U₁ Prod.snd) (true, v) :=
          dist_pair_swap _ _ _ _ _
        rwa [e] at h1
      · exact absurd h1 hv
    · right
      rw [condDist, div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · have e : dist μ (pair Prod.snd U₂) (v, false) = dist μ (pair U₂ Prod.snd) (false, v) :=
          dist_pair_swap _ _ _ _ _
        rwa [e] at h1
      · exact absurd h1 hv
  -- The binary description.
  set f : υ → Bool := fun v => decide (dist μ (pair U₁ Prod.snd) (true, v) = 0) with hf
  have hm : IsChannel (margCh κ f) := margCh_isChannel hκ f
  have hk₀ : ∀ v, f v = false → κ (false, false) v = 0 := fun v hv => by
    have hA : dist μ (pair U₁ Prod.snd) (true, v) ≠ 0 := by simpa [hf] using hv
    have hB := (hkey v).resolve_left hA
    have h3 := hle₂ false false v
    rw [hB] at h3
    have h4 : jsTriPMF (false, false) = 1 / 3 := by simp [jsTriPMF]
    rw [h4] at h3
    have h5 := (hκ (false, false)).nonneg v
    linarith
  have hk₁ : ∀ v, f v = true → κ (true, true) v = 0 := fun v hv => by
    have hA : dist μ (pair U₁ Prod.snd) (true, v) = 0 := by simpa [hf] using hv
    have h3 := hle₁ true true v
    rw [hA] at h3
    have h4 : jsTriPMF (true, true) = 1 / 3 := by simp [jsTriPMF]
    rw [h4] at h3
    have h5 := (hκ (true, true)).nonneg v
    linarith
  have hw₁ : margCh κ f (false, false) true = 1 := by
    have e := (hm (false, false)).sum_eq_one
    rw [Fintype.sum_bool] at e
    have e0 : margCh κ f (false, false) false = 0 := by
      simp only [margCh, dist]
      refine sum_eq_zero fun v _ => ?_
      by_cases hv : f v = false
      · simp [hv, hk₀ v hv]
      · simp [hv]
    linarith
  have hw₂ : margCh κ f (true, true) true = 0 := by
    simp only [margCh, dist]
    refine sum_eq_zero fun v _ => ?_
    by_cases hv : f v = true
    · simp [hv, hk₁ v hv]
    · simp [hv]
  have hq0 : 0 ≤ margCh κ f (false, true) true := (hm _).nonneg _
  have hq1 : margCh κ f (false, true) true ≤ 1 := (hm _).le_one _
  have hval := mutualInfoOf_tri hm hw₁ hw₂
  rw [mutualInfoOf_margCh] at hval
  have hbound := two_thirds_le hq0 hq1
  rw [← hval] at hbound
  refine hbound.trans ?_
  exact mutualInfo_comp_le hμ Prod.fst Prod.snd f

/-- The joint law of `(U₁, U₂)` and `V ∼ Bern(1/2)`, page 15-26. -/
lemma jsTriW_half_residual : gwResidual jsTriPMF (jsTriW (1 / 2)) = 0 := by
  have hch := jsTriW_isChannel (q := 1 / 2) (by norm_num) (by norm_num)
  have hμ := jointOf_isPMF jsTriPMF_isPMF hch
  set J := jointOf jsTriPMF (jsTriW (1 / 2)) with hJ
  have l2 : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
  have l6 : log (1 / 6 : ℝ) = -log 2 - log 3 := by
    rw [one_div, log_inv, show (6 : ℝ) = 2 * 3 by norm_num, log_mul two_ne_zero (by norm_num)]
    ring
  -- The entropy of `V`.
  have hV : H[Prod.snd ; J] = log 2 := by
    rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_bool]
    have a1 : dist J Prod.snd true = 1 / 2 := by
      simp [J, dist, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
      norm_num
    have a2 : dist J Prod.snd false = 1 / 2 := by
      simp [J, dist, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
      norm_num
    rw [a1, a2, negMulLog, l2]
    ring
  -- The entropy of `(V, U₁)`.
  have hV₁ : H[pair Prod.snd (fun z : (Bool × Bool) × Bool => z.1.1) ; J] =
      2 / 3 * log 2 + 1 / 2 * log 3 := by
    rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool]
    have a1 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.1) (true, true) =
        0 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
    have a2 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.1) (true, false) =
        1 / 2 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
      norm_num
    have a3 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.1) (false, true) =
        1 / 3 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
    have a4 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.1) (false, false) =
        1 / 6 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
      norm_num
    rw [a1, a2, a3, a4, negMulLog, negMulLog, negMulLog, negMulLog, l2, l6, log_one_third]
    simp
    ring
  -- The entropy of `(V, U₂)`.
  have hV₂ : H[pair Prod.snd (fun z : (Bool × Bool) × Bool => z.1.2) ; J] =
      2 / 3 * log 2 + 1 / 2 * log 3 := by
    rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool]
    have a1 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.2) (true, true) =
        1 / 6 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
      norm_num
    have a2 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.2) (true, false) =
        1 / 3 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
    have a3 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.2) (false, true) =
        1 / 2 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
      norm_num
    have a4 : dist J (pair Prod.snd fun z : (Bool × Bool) × Bool => z.1.2) (false, false) =
        0 := by
      simp [J, dist, pair, jointOf, jsTriPMF, jsTriW, bernoulliPMF, Fintype.sum_prod_type]
    rw [a1, a2, a3, a4, negMulLog, negMulLog, negMulLog, negMulLog, l2, l6, log_one_third]
    simp
    ring
  -- The mutual information.
  have hI : gwInfo jsTriPMF (jsTriW (1 / 2)) = 2 / 3 * log 2 := by
    have e := mutualInfoOf_tri hch (by simp [jsTriW, bernoulliPMF]) (by simp [jsTriW, bernoulliPMF])
    have e' : jsTriW (1 / 2) (false, true) true = 1 / 2 := by simp [jsTriW, bernoulliPMF]
    rw [e'] at e
    have e3 : binEntropy ((1 + 1 / 2) / 3) = log 2 := by
      rw [show ((1 + 1 / 2) / 3 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
    have e4 : binEntropy (1 / 2) = log 2 := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
    rw [e3, e4] at e
    change mutualInfoOf jsTriPMF (jsTriW (1 / 2)) = _
    rw [e]
    ring
  have h₁ : gwCond₁ jsTriPMF (jsTriW (1 / 2)) = 2 / 3 * log 2 + 1 / 2 * log 3 - log 2 := by
    rw [gwCond₁, condEntropy_eq_sub hμ, hV₁, hV]
  have h₂ : gwCond₂ jsTriPMF (jsTriW (1 / 2)) = 2 / 3 * log 2 + 1 / 2 * log 3 - log 2 := by
    rw [gwCond₂, condEntropy_eq_sub hμ, hV₂, hV]
  rw [gwResidual, h₁, h₂, hI, entropy_jsTriPMF]
  ring

/-- **Lecture 15, page 15-26.** `J(U₁; U₂) = 2/3` bits, for the description `V ∼ Bern(1/2)`. -/
theorem wynerJ_jsTriPMF : wynerJ jsTriPMF = 2 / 3 * log 2 := by
  have hch := jsTriW_isChannel (q := 1 / 2) (by norm_num) (by norm_num)
  refine le_antisymm ?_ ?_
  · have h := wynerJ_le jsTriPMF_isPMF hch jsTriW_half_residual
    refine h.trans (le_of_eq ?_)
    have e := mutualInfoOf_tri hch (by simp [jsTriW, bernoulliPMF]) (by simp [jsTriW, bernoulliPMF])
    have e' : jsTriW (1 / 2) (false, true) true = 1 / 2 := by simp [jsTriW, bernoulliPMF]
    rw [e'] at e
    have e3 : binEntropy ((1 + 1 / 2) / 3) = log 2 := by
      rw [show ((1 + 1 / 2) / 3 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
    have e4 : binEntropy (1 / 2) = log 2 := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, binEntropy_two_inv]
    rw [e3, e4] at e
    change mutualInfoOf jsTriPMF (jsTriW (1 / 2)) = _
    rw [e]
    ring
  · obtain ⟨κ, hκ, hr, e⟩ := exists_wyner_min jsTriPMF_isPMF
    rw [← e]
    exact two_thirds_le_gwInfo hκ hr

/-- **Lecture 15, page 15-25.** `K(U₁; U₂) = 0`: the pmf has one block. -/
theorem gkCommon_jsTriPMF : gkCommon jsTriPMF = 0 := by
  have h1 : commonG₁ jsTriPMF false = commonG₂ jsTriPMF true := commonG_eq (by simp [jsTriPMF])
  have h2 : commonG₁ jsTriPMF true = commonG₂ jsTriPMF true := commonG_eq (by simp [jsTriPMF])
  have e : (fun z : Bool × Bool => commonG₁ jsTriPMF z.1) = fun _ => commonG₂ jsTriPMF true := by
    funext z
    obtain ⟨a, b⟩ := z
    cases a
    · exact h1
    · exact h2
  rw [gkCommon, e, entropyRV_const jsTriPMF_isPMF]

lemma log_two_thirds : log (2 / 3 : ℝ) = log 2 - log 3 := log_div two_ne_zero (by norm_num)

/-- **Lecture 15, page 15-25.** `I(U₁; U₂) = log 3 - (4/3) log 2`. -/
theorem mutualInfo_jsTriPMF : I[Prod.fst : Prod.snd ; jsTriPMF] = log 3 - 4 / 3 * log 2 := by
  rw [mutualInfo_eq_add_sub jsTriPMF_isPMF]
  have e3 : H[pair Prod.fst Prod.snd ; jsTriPMF] = log 3 := by
    have : pair (Prod.fst : Bool × Bool → Bool) Prod.snd = id := rfl
    rw [this, entropyRV, dist_id, entropy_jsTriPMF]
  have e1 : H[Prod.fst ; jsTriPMF] = log 3 - 2 / 3 * log 2 := by
    rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_bool]
    have a1 : dist jsTriPMF Prod.fst true = 1 / 3 := by
      rw [dist_fst]
      simp [jsTriPMF]
    have a2 : dist jsTriPMF Prod.fst false = 2 / 3 := by
      rw [dist_fst]
      simp [jsTriPMF]
      norm_num
    rw [a1, a2, negMulLog, negMulLog, log_one_third, log_two_thirds]
    ring
  have e2 : H[Prod.snd ; jsTriPMF] = log 3 - 2 / 3 * log 2 := by
    rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_bool]
    have a1 : dist jsTriPMF Prod.snd true = 2 / 3 := by
      rw [dist_snd]
      simp [jsTriPMF]
      norm_num
    have a2 : dist jsTriPMF Prod.snd false = 1 / 3 := by
      rw [dist_snd]
      simp [jsTriPMF]
    rw [a1, a2, negMulLog, negMulLog, log_one_third, log_two_thirds]
    ring
  rw [e1, e2, e3]
  ring

/-- **Lecture 15, page 15-25.** The inequalities `K ≤ I ≤ J ≤ H` can be strict. -/
theorem common_information_strict :
    gkCommon jsTriPMF < I[Prod.fst : Prod.snd ; jsTriPMF] ∧
      I[Prod.fst : Prod.snd ; jsTriPMF] < wynerJ jsTriPMF ∧ wynerJ jsTriPMF < entropy jsTriPMF := by
  have hl := log_pos one_lt_two
  have h1 := log_three_gt
  have h2 := log_three_lt
  rw [gkCommon_jsTriPMF, mutualInfo_jsTriPMF, wynerJ_jsTriPMF, entropy_jsTriPMF]
  refine ⟨by linarith, by linarith, by linarith⟩

end Common

/-! ### The Blackwell channel -/

section Blackwell

/-- The input of the Blackwell channel for `(U₁, U₂)`. With the labels of `blackwell`, the inputs
`0`, `1` and `2` give `(Y₁, Y₂) = (0, 0)`, `(1, 1)` and `(0, 1)`. -/
def jsTriInput (z : Bool × Bool) : Fin 3 :=
  if z.1 then 1 else if z.2 then 2 else 0

/-- **Lecture 15, page 15-29.** The sources can be sent over the Blackwell channel with no coding,
since `Y₁` and `Y₂` determine `U₁` and `U₂`. -/
theorem isLosslessBC_jsTriPMF : IsLosslessBC jsTriPMF blackwellChannel := by
  refine isLosslessBC_of_uncoded (f := blackwell) (fun x y => by
      simp only [blackwellChannel, detChannel]
      congr!) jsTriInput
    (fun y => decide (y = 1)) (fun y => decide (y = 1)) fun z hz => ?_
  obtain ⟨a, b⟩ := z
  cases a <;> cases b
  · simp [jsTriInput, blackwell, blackwell₁, blackwell₂]
  · simp [jsTriInput, blackwell, blackwell₁, blackwell₂]
  · simp [jsTriPMF] at hz
  · simp [jsTriInput, blackwell, blackwell₁, blackwell₂]

/-- **Lecture 15, page 15-29: source–channel separation fails.** No rate triple of the Gray–Wyner
region of the sources has `R₀ + R₁ ≤ 1`, `R₀ + R₂ ≤ 1` and `R₀ + R₁ + R₂ ≤ log 3` in bits, the
bounds of the Blackwell channel. -/
theorem gray_wyner_blackwell {R₀ R₁ R₂ : ℝ} (h : (R₀, R₁, R₂) ∈ gwRegion jsTriPMF)
    (h₁ : R₀ + R₁ ≤ 1) (h₂ : R₀ + R₂ ≤ 1) (h₃ : (R₀ + R₁ + R₂) * log 2 ≤ log 3) : False := by
  have hl := log_pos one_lt_two
  obtain ⟨-, -, a3, -⟩ := gwRegion_le jsTriPMF_isPMF h
  rw [entropy_jsTriPMF] at a3
  have hs : (R₀ + R₁ + R₂) * log 2 = entropy jsTriPMF := by
    rw [entropy_jsTriPMF]
    exact le_antisymm h₃ a3
  have hJ := wynerJ_le_of_mem_gwRegion jsTriPMF_isPMF h hs
  rw [wynerJ_jsTriPMF] at hJ
  have hR : 2 / 3 ≤ R₀ := le_of_mul_le_mul_right hJ hl
  have h4 := log_three_gt
  -- `2 R₀ + R₁ + R₂ ≥ log 3 + 2/3 > 2`.
  have h5 : (2 * R₀ + R₁ + R₂) * log 2 ≤ 2 * log 2 := by
    refine mul_le_mul_of_nonneg_right ?_ hl.le
    linarith
  have h6 : (R₀ + R₁ + R₂) * log 2 + R₀ * log 2 = (2 * R₀ + R₁ + R₂) * log 2 := by ring
  linarith

end Blackwell

end InfoTheory.ElGamalKim
