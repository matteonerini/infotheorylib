/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.WiretapAchievability
public import InfoTheoryLib.Network.BinarySymmetricBC
public import InfoTheoryLib.Network.Gaussian
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The wiretap channel: special cases

The special cases of Theorem 3 of Lecture 23 of El Gamal and Kim. If `Y` is more capable than `Z`,
in particular if the channel to `Z` is a degraded version of the channel to `Y`, then the auxiliary
random variable is not needed: `C_S = max_{p(x)} (I(X; Y) - I(X; Z))`. If `Z` is less noisy than
`Y`, then `C_S = 0`.

## Main definitions

* `wiretapXValue W`: the value `max_{p(x)} (I(X; Y) - I(X; Z))`.

## Main statements

* `wiretapGap_eq_sub_sum`: `I(U; Y) - I(U; Z) = I(X; Y) - I(X; Z) - (I(X; Y | U) - I(X; Z | U))`.
* `wiretapCapacity_of_isMoreCapable`, `wiretapCapacity_of_isStochasticallyDegraded`.
* `wiretapCapacity_eq_zero_of_isLessNoisy`.
* `wiretapCapacity_bsbcIndep`, `wiretapCapacity_bsbcIndep_eq_zero`: the BS-WTC.
* `gaussianWiretap_bound`: the formula of the Gaussian WTC.

## Implementation notes

The formula for the BS-WTC on page 23-11 of the notes holds for `p₁, p₂ ≤ 1/2`, as for the BS-BC.
For `p₁ = 2/5` and `p₂ = 9/10` the printed `H(p₂) - H(p₁)` would be negative.

For the Gaussian WTC we formalize the steps on real numbers of the bound of pages 23-12 and 23-13,
from the bound of the entropy power inequality on: `h(Y)` is the only argument. The operational
capacity for continuous alphabets is not formalized here.

The MIMO formula of page 23-13 has no factor `1/2`: for a scalar channel it is twice the formula of
the Gaussian WTC above it, for real signals (see `mimo_formula_eq_two_mul`).

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section General

variable {α β γ 𝒰 : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype 𝒰] {W : α → β × γ → ℝ}

/-- **Page 23-10 of [elgamal2010]: the value without an auxiliary random variable.** -/
def wiretapXValue (W : α → β × γ → ℝ) : ℝ :=
  sSup ((fun p => mutualInfoOf p (bcMarg₁ W) - mutualInfoOf p (bcMarg₂ W)) '' {p : α → ℝ | IsPMF p})

/-- The law of `X`, as the mean of the laws given `U`. -/
lemma mean_isPMF {w : 𝒰 → ℝ} (hw : IsPMF w) {r : 𝒰 → α → ℝ} (hr : IsChannel r) :
    IsPMF (∑ u, w u • r u) := by
  refine ⟨fun x => ?_, ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_nonneg fun u _ => mul_nonneg (hw.nonneg u) ((hr u).nonneg x)
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_comm]
    simp only [← mul_sum, (hr _).sum_eq_one, mul_one, hw.sum_eq_one]

/-- **Page 23-10 of [elgamal2010].**
`I(U; Y) - I(U; Z) = I(X; Y) - I(X; Z) - ∑ᵤ p(u) (I(X; Y | U = u) - I(X; Z | U = u))`. -/
theorem wiretapGap_eq_sub_sum {w : 𝒰 → ℝ} (hw : IsPMF w) {r : 𝒰 → α → ℝ} (hr : IsChannel r)
    (hW : IsChannel W) :
    wiretapGap (fun z : 𝒰 × α => w z.1 * r z.1 z.2) W =
      mutualInfoOf (∑ u, w u • r u) (bcMarg₁ W) - mutualInfoOf (∑ u, w u • r u) (bcMarg₂ W) -
        ∑ u, w u * (mutualInfoOf (r u) (bcMarg₁ W) - mutualInfoOf (r u) (bcMarg₂ W)) := by
  have hp := mean_isPMF hw hr
  have hmean : ∀ f : α → ℝ, ∑ x, (∑ u, w u • r u) x * f x = ∑ u, w u * ∑ x, r u x * f x := fun f =>
    by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun u _ => sum_congr rfl fun x _ => by ring
  rw [wiretapGap_kernel hw hr hW, mutualInfoOf_eq hp hW.bcMarg₁, mutualInfoOf_eq hp hW.bcMarg₂,
    hmean, hmean]
  have hu : ∀ u, mutualInfoOf (r u) (bcMarg₁ W) - mutualInfoOf (r u) (bcMarg₂ W) =
      entropy (outDist (r u) (bcMarg₁ W)) - entropy (outDist (r u) (bcMarg₂ W)) -
        ∑ x, r u x * entropy (bcMarg₁ W x) + ∑ x, r u x * entropy (bcMarg₂ W x) := fun u => by
    rw [mutualInfoOf_eq (hr u) hW.bcMarg₁, mutualInfoOf_eq (hr u) hW.bcMarg₂]
    ring
  simp only [hu, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  ring

/-- `U = X`: the difference of the mutual informations is at most the value. -/
theorem sub_mutualInfoOf_le_wiretapValue [Nonempty α] (hW : IsChannel W) {p : α → ℝ}
  (hp : IsPMF p) :
    mutualInfoOf p (bcMarg₁ W) - mutualInfoOf p (bcMarg₂ W) ≤ wiretapValue W := by
  classical
  set r : α → α → ℝ := fun u x => if u = x then 1 else 0 with hr
  have hrC : IsChannel r := fun u => ⟨fun x => by simp only [hr]; split_ifs <;> norm_num, by simp
    [hr]⟩
  have hq : IsPMF fun z : α × α => p z.1 * r z.1 z.2 := by
    refine ⟨fun z => mul_nonneg (hp.nonneg _) ((hrC _).nonneg _), ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, (hrC _).sum_eq_one, mul_one, hp.sum_eq_one]
  refine le_trans (le_of_eq ?_) (wiretapGap_le_value hW hq)
  have hm : ∑ u, p u • r u = p := by
    funext x
    simp [hr]
  have ho : ∀ (T : α → β → ℝ) u, outDist (r u) T = T u := fun T u => by
    funext y
    simp [outDist, hr]
  have ho' : ∀ (T : α → γ → ℝ) u, outDist (r u) T = T u := fun T u => by
    funext y
    simp [outDist, hr]
  rw [wiretapGap_kernel hp hrC hW, hm, mutualInfoOf_eq hp hW.bcMarg₁, mutualInfoOf_eq hp hW.bcMarg₂]
  simp only [ho, ho', mul_sub, sum_sub_distrib]
  ring

/-- The maximum of `I(X; Y) - I(X; Z)` is attained. -/
theorem exists_wiretapXValue_eq [Nonempty α] (hW : IsChannel W) :
    ∃ p : α → ℝ, IsPMF p ∧
      mutualInfoOf p (bcMarg₁ W) - mutualInfoOf p (bcMarg₂ W) = wiretapXValue W := by
  obtain ⟨p, hp, hmax⟩ := isCompact_setOf_isPMF.exists_isMaxOn ⟨uniformPMF α, uniformPMF_isPMF⟩
    ((continuousOn_mutualInfoOf hW.bcMarg₁).sub (continuousOn_mutualInfoOf hW.bcMarg₂))
  refine ⟨p, hp, le_antisymm ?_ ?_⟩
  · exact le_csSup ⟨_, by
      rintro _ ⟨p', hp', rfl⟩
      exact hmax hp'⟩ ⟨p, hp, rfl⟩
  · refine csSup_le ⟨_, p, hp, rfl⟩ ?_
    rintro _ ⟨p', hp', rfl⟩
    exact hmax hp'

/-- Every input law has a difference at most the value without an auxiliary random variable. -/
theorem sub_mutualInfoOf_le_wiretapXValue [Nonempty α] (hW : IsChannel W) {p : α → ℝ}
  (hp : IsPMF p) :
    mutualInfoOf p (bcMarg₁ W) - mutualInfoOf p (bcMarg₂ W) ≤ wiretapXValue W := by
  obtain ⟨p₀, hp₀, hmax⟩ := isCompact_setOf_isPMF.exists_isMaxOn ⟨uniformPMF α, uniformPMF_isPMF⟩
    ((continuousOn_mutualInfoOf hW.bcMarg₁).sub (continuousOn_mutualInfoOf hW.bcMarg₂))
  exact le_csSup ⟨_, by
    rintro _ ⟨p', hp', rfl⟩
    exact hmax hp'⟩ ⟨p, hp, rfl⟩

/-- **Page 23-10 of [elgamal2010].** If `Y` is more capable than `Z`, the value is
`max_{p(x)} (I(X; Y) - I(X; Z))`. -/
theorem wiretapValue_eq_of_isMoreCapable [Nonempty α] (hW : IsChannel W) (h : IsMoreCapable W) :
    wiretapValue W = wiretapXValue W := by
  obtain ⟨p, hp, hpe⟩ := exists_wiretapXValue_eq hW
  refine le_antisymm ?_ (hpe ▸ sub_mutualInfoOf_le_wiretapValue hW hp)
  obtain ⟨q, hq, hqe⟩ := exists_wiretapValue_eq hW
  rw [← hqe]
  have hq' : (fun z : Fin (Fintype.card α) × α => (∑ x, q (z.1, x)) * wtPosterior q z.1 z.2) = q :=
    funext (marg_mul_wtPosterior hq)
  have hgap := wiretapGap_eq_sub_sum (W := W) (wiretapMarg_isPMF hq) (wtPosterior_isChannel hq) hW
  rw [hq'] at hgap
  rw [hgap]
  have hnn : 0 ≤ ∑ u, (∑ x, q (u, x)) * (mutualInfoOf (wtPosterior q u) (bcMarg₁ W) -
      mutualInfoOf (wtPosterior q u) (bcMarg₂ W)) :=
    sum_nonneg fun u _ => mul_nonneg ((wiretapMarg_isPMF hq).nonneg u)
      (sub_nonneg.2 (h _ (wtPosterior_isChannel hq u)))
  have hle := sub_mutualInfoOf_le_wiretapXValue hW
    (mean_isPMF (wiretapMarg_isPMF hq) (wtPosterior_isChannel hq))
  linarith

/-- **Page 23-10 of [elgamal2010].** If `Y` is more capable than `Z`, then
`C_S = max_{p(x)} (I(X; Y) - I(X; Z))`, in bits. -/
theorem wiretapCapacity_of_isMoreCapable [Nonempty α] (hW : IsChannel W) (h : IsMoreCapable W) :
    wiretapCapacity W = wiretapXValue W / log 2 := by
  rw [wiretapCapacity_eq hW, wiretapValue_eq_of_isMoreCapable hW h]

/-- **Wyner's theorem, page 23-10 of [elgamal2010].** If the channel to `Z` is a degraded version of
the channel to `Y`, then `C_S = max_{p(x)} (I(X; Y) - I(X; Z))`, in bits. -/
theorem wiretapCapacity_of_isStochasticallyDegraded [Nonempty α] (hW : IsChannel W)
    (h : IsStochasticallyDegraded W) : wiretapCapacity W = wiretapXValue W / log 2 :=
  wiretapCapacity_of_isMoreCapable hW (h.isMoreCapable hW)

/-- **Page 23-10 of [elgamal2010].** The secrecy capacity depends only on the marginal channels. -/
theorem wiretapGap_congr {W' : α → β × γ → ℝ} (h₁ : bcMarg₁ W = bcMarg₁ W')
    (h₂ : bcMarg₂ W = bcMarg₂ W') (q : 𝒰 × α → ℝ) : wiretapGap q W = wiretapGap q W' := by
  rw [wiretapGap, wiretapGap, bcInfoUY₁_eq, bcInfoUY₂_eq, bcInfoUY₁_eq, bcInfoUY₂_eq, h₁, h₂]

/-- **Page 23-27 of [elgamal2010].** If `Z` is less noisy than `Y`, then `C_S = 0`. -/
theorem wiretapCapacity_eq_zero_of_isLessNoisy [Nonempty α] (hW : IsChannel W)
    (h : IsLessNoisy (bcReceiverSwap W)) : wiretapCapacity W = 0 := by
  have hV : wiretapValue W ≤ 0 := by
    obtain ⟨q, hq, hqe⟩ := exists_wiretapValue_eq hW
    rw [← hqe, wiretapGap]
    have h₁ := h _ q hq
    have e₁ : bcInfoUY₂ q (bcReceiverSwap W) = bcInfoUY₁ q W := by
      rw [bcInfoUY₂_eq, bcInfoUY₁_eq, bcMarg₂_bcReceiverSwap]
    have e₂ : bcInfoUY₁ q (bcReceiverSwap W) = bcInfoUY₂ q W := by
      rw [bcInfoUY₁_eq, bcInfoUY₂_eq, bcMarg₁_bcReceiverSwap]
    rw [e₁, e₂] at h₁
    linarith
  rw [wiretapCapacity_eq hW, le_antisymm hV (wiretapValue_nonneg hW), zero_div]

end General

/-! ### The binary symmetric wiretap channel -/

section Binary

variable {p₁ p₂ : ℝ}

/-- `H(x ∗ p) ≥ H(x)`. -/
lemma binEntropy_le_binEntropy_binConv {x p : ℝ} (hx : x ∈ Set.Icc 0 1) (hp : p ∈ Set.Icc 0 1) :
    binEntropy x ≤ binEntropy (binConv x p) := by
  have hc := strictConcave_binEntropy.concaveOn.2 hx (show 1 - x ∈ Set.Icc 0 1 from
    ⟨by linarith [hx.2], by linarith [hx.1]⟩) (sub_nonneg.2 hp.2) hp.1 (by ring)
  simp only [smul_eq_mul, binEntropy_one_sub] at hc
  have e : (1 - p) * x + p * (1 - x) = binConv x p := by
    unfold binConv
    ring
  rw [e] at hc
  linarith

/-- For `p₁ ≤ p₂ ≤ 1/2`, `H(a ∗ p₁) ≤ H(a ∗ p₂)`: the step of page 23-11 of [elgamal2010]. -/
lemma binEntropy_binConv_mono {a : ℝ} (ha : a ∈ Set.Icc 0 1) (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂)
    (hp₂ : p₂ ≤ 1 / 2) : binEntropy (binConv a p₁) ≤ binEntropy (binConv a p₂) := by
  have hn := bsbcNoise₂_mem hp₁₂ hp₂
  have hx : binConv a p₁ ∈ Set.Icc 0 1 :=
    bsbc_binConv_mem_Icc ha ⟨hp₁, by linarith⟩
  have e : binConv a p₂ = binConv (binConv a p₁) (bsbcNoise₂ p₁ p₂) := by
    rw [bsbc_binConv_assoc, binConv_bsbcNoise₂ hp₁₂ hp₂]
  rw [e]
  exact binEntropy_le_binEntropy_binConv hx ⟨hn.1, hn.2.trans (by norm_num)⟩

/-- The mutual information of the BSC for an input with `p(true) = a`. -/
lemma mutualInfoOf_bsbcBSC {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {r : Bool → ℝ} (hr : IsPMF r) :
    mutualInfoOf r (bsbcBSC p) = binEntropy (binConv (r true) p) - binEntropy p :=
  mutualInfoOf_bscBecMarg₁ h0 h1 hr

/-- **The BS-WTC, page 23-11 of [elgamal2010].** The value of the BS-WTC with `p₁ ≤ p₂ ≤ 1/2`. -/
theorem wiretapXValue_bsbcIndep (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    wiretapXValue (bsbcIndep p₁ p₂) = binEntropy p₂ - binEntropy p₁ := by
  have hp₁' : p₁ ≤ 1 := by linarith
  have hp₂0 : 0 ≤ p₂ := hp₁.trans hp₁₂
  have hp₂' : p₂ ≤ 1 := by linarith
  have hW := bsbcIndep_isChannel hp₁ hp₁' hp₂0 hp₂'
  have e₁ := bcMarg₁_bsbcIndep (p₁ := p₁) hp₂0 hp₂'
  have e₂ := bcMarg₂_bsbcIndep (p₂ := p₂) hp₁ hp₁'
  obtain ⟨p, hp, hpe⟩ := exists_wiretapXValue_eq hW
  have hup : wiretapXValue (bsbcIndep p₁ p₂) ≤ binEntropy p₂ - binEntropy p₁ := by
    rw [← hpe, e₁, e₂, mutualInfoOf_bsbcBSC hp₁ hp₁' hp, mutualInfoOf_bsbcBSC hp₂0 hp₂' hp]
    have ha : p true ∈ Set.Icc 0 1 := by
      have h := hp.sum_eq_one
      rw [Fintype.sum_bool] at h
      exact ⟨hp.nonneg _, by linarith [hp.nonneg false]⟩
    have := binEntropy_binConv_mono ha hp₁ hp₁₂ hp₂
    linarith
  refine le_antisymm hup ?_
  have hu : IsPMF (bernoulliPMF (2⁻¹ : ℝ)) := bernoulliPMF_isPMF (by norm_num) (by norm_num)
  have h := sub_mutualInfoOf_le_wiretapXValue hW hu
  rw [e₁, e₂, mutualInfoOf_bsbcBSC hp₁ hp₁' hu, mutualInfoOf_bsbcBSC hp₂0 hp₂' hu] at h
  simp only [bernoulliPMF, ite_true, binConv_half_left] at h
  linarith

/-- **The BS-WTC, page 23-11 of [elgamal2010].** For `p₁ ≤ p₂ ≤ 1/2`, the secrecy capacity of the
BS-WTC with independent noises is `H(p₂) - H(p₁)`, in bits. -/
theorem wiretapCapacity_bsbcIndep (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    wiretapCapacity (bsbcIndep p₁ p₂) = (binEntropy p₂ - binEntropy p₁) / log 2 := by
  have hp₂0 : 0 ≤ p₂ := hp₁.trans hp₁₂
  have hW := bsbcIndep_isChannel hp₁ (by linarith) hp₂0 (by linarith)
  have hd := isStochasticallyDegraded_of_bsbc (W := bsbcIndep p₁ p₂)
    (bcMarg₁_bsbcIndep hp₂0 (by linarith)) (bcMarg₂_bsbcIndep hp₁ (by linarith)) hp₁₂ hp₂
  rw [wiretapCapacity_of_isStochasticallyDegraded hW hd, wiretapXValue_bsbcIndep hp₁ hp₁₂ hp₂]

/-- **The BS-WTC, page 23-11 of [elgamal2010].** For `p₂ ≤ p₁ ≤ 1/2`, the secrecy capacity is
`0`. -/
theorem wiretapCapacity_bsbcIndep_eq_zero (hp₂ : 0 ≤ p₂) (hp₂₁ : p₂ ≤ p₁) (hp₁ : p₁ ≤ 1 / 2) :
    wiretapCapacity (bsbcIndep p₁ p₂) = 0 := by
  have hp₁0 : 0 ≤ p₁ := hp₂.trans hp₂₁
  have hW := bsbcIndep_isChannel hp₁0 (by linarith) hp₂ (by linarith)
  refine wiretapCapacity_eq_zero_of_isLessNoisy hW ?_
  have hd := isStochasticallyDegraded_of_bsbc (W := bcReceiverSwap (bsbcIndep p₁ p₂))
    (p₁ := p₂) (p₂ := p₁)
    (by rw [bcMarg₁_bcReceiverSwap, bcMarg₂_bsbcIndep hp₁0 (by linarith)])
    (by rw [bcMarg₂_bcReceiverSwap, bcMarg₁_bsbcIndep hp₂ (by linarith)]) hp₂₁ hp₁
  exact hd.isLessNoisy hW.bcReceiverSwap

end Binary

/-! ### The Gaussian wiretap channel, on real numbers -/

section Gaussian

/-- The function `ν ↦ ½ log (a + e^{2ν}) - ν` of page 23-13 of [elgamal2010], for
`a = 2πe (N₂ - N₁)`. The notes write it with `2^ν` in bits. -/
def gaussianWiretapFun (a ν : ℝ) : ℝ := 1 / 2 * log (a + exp (2 * ν)) - ν

/-- **Page 23-13 of [elgamal2010].** The function is decreasing in `ν` for `a ≥ 0`.

The notes say "increasing". The bound `h(Z) - h(Y) ≥ ...` at the maximum `h(Y) ≤ ½ log 2πe(P + N₁)`
needs a function that does not increase. -/
theorem gaussianWiretapFun_antitone {a : ℝ} (ha : 0 ≤ a) : Antitone (gaussianWiretapFun a) := by
  intro ν₁ ν₂ h
  simp only [gaussianWiretapFun]
  have hp₁ : 0 < a + exp (2 * ν₁) := by positivity
  have hp₂ : 0 < a + exp (2 * ν₂) := by positivity
  have h₁ : (a + exp (2 * ν₂)) ≤ (a + exp (2 * ν₁)) * exp (2 * (ν₂ - ν₁)) := by
    have e : exp (2 * ν₂) = exp (2 * ν₁) * exp (2 * (ν₂ - ν₁)) := by
      rw [← exp_add]
      congr 1
      ring
    have h₃ : 1 ≤ exp (2 * (ν₂ - ν₁)) := one_le_exp (by linarith)
    rw [e, add_mul]
    nlinarith
  have h₂ := log_le_log hp₂ h₁
  rw [log_mul hp₁.ne' (exp_pos _).ne', log_exp] at h₂
  linarith

/-- **Pages 23-12 and 23-13 of [elgamal2010].** For `0 < N₁ ≤ N₂` and `0 ≤ P`: if
`h(Y) ≤ ½ log 2πe(P + N₁)` and `I(X; Y) - I(X; Z) = ½ log (N₂ / N₁) - (h(Z) - h(Y))` with the bound
of the entropy power inequality on `h(Z) - h(Y)`, then the difference is at most
`C(P / N₁) - C(P / N₂)`. -/
theorem gaussianWiretap_bound {P N₁ N₂ hY hZ : ℝ} (hP : 0 ≤ P) (hN₁ : 0 < N₁) (hN : N₁ ≤ N₂)
    (hhY : hY ≤ 1 / 2 * log (2 * π * rexp 1 * (P + N₁)))
    (hEPI : gaussianWiretapFun (2 * π * rexp 1 * (N₂ - N₁)) hY ≤ hZ - hY) :
    1 / 2 * log (N₂ / N₁) - (hZ - hY) ≤ gaussCap (P / N₁) - gaussCap (P / N₂) := by
  have hN₂ : 0 < N₂ := hN₁.trans_le hN
  have hc : 0 < 2 * π * rexp 1 := by positivity
  have ha : 0 ≤ 2 * π * rexp 1 * (N₂ - N₁) := mul_nonneg hc.le (by linarith)
  have hmono := gaussianWiretapFun_antitone ha hhY
  have hsum : 0 < P + N₁ := by linarith
  have hsum₂ : 0 < P + N₂ := by linarith
  have hval : gaussianWiretapFun (2 * π * rexp 1 * (N₂ - N₁))
      (1 / 2 * log (2 * π * rexp 1 * (P + N₁))) = 1 / 2 * log ((P + N₂) / (P + N₁)) := by
    simp only [gaussianWiretapFun]
    have e₁ : 2 * (1 / 2 * log (2 * π * rexp 1 * (P + N₁))) =
        log (2 * π * rexp 1 * (P + N₁)) := by ring
    rw [e₁, exp_log (by positivity),
      show 2 * π * rexp 1 * (N₂ - N₁) + 2 * π * rexp 1 * (P + N₁) = 2 * π * rexp 1 * (P + N₂) by
        ring, log_mul hc.ne' hsum₂.ne', log_mul hc.ne' hsum.ne',
      log_div hsum₂.ne' hsum.ne']
    ring
  rw [hval] at hmono
  have e₂ : gaussCap (P / N₁) - gaussCap (P / N₂) =
      1 / 2 * log (N₂ / N₁) - 1 / 2 * log ((P + N₂) / (P + N₁)) := by
    simp only [gaussCap]
    rw [show 1 + P / N₁ = (P + N₁) / N₁ by field_simp; ring,
      show 1 + P / N₂ = (P + N₂) / N₂ by field_simp; ring, log_div hsum.ne' hN₁.ne',
      log_div hsum₂.ne' hN₂.ne', log_div hN₂.ne' hN₁.ne', log_div hsum₂.ne' hsum.ne']
    ring
  rw [e₂]
  linarith

/-- **Page 23-13 of [elgamal2010].** For a scalar channel, the printed MIMO formula is twice the
formula of the Gaussian WTC. -/
theorem mimo_formula_eq_two_mul (G₁ G₂ P : ℝ) :
    log (1 + G₁ * P * G₁) - log (1 + G₂ * P * G₂) =
      2 * (gaussCap (G₁ ^ 2 * P) - gaussCap (G₂ ^ 2 * P)) := by
  simp only [gaussCap]
  rw [show G₁ * P * G₁ = G₁ ^ 2 * P by ring, show G₂ * P * G₂ = G₂ ^ 2 * P by ring]
  ring

end Gaussian

end InfoTheory
