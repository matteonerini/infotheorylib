/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture1
public import InfoTheoryLib.Entropy.MrsGerber
public import InfoTheoryLib.Network.SlepianWolfMany
public import InfoTheoryLib.Network.SourceHelperConverse

/-!
# El Gamal & Kim, Lecture 11: Distributed Lossless Source Coding

This file indexes the formalization of Lecture 11 of [elgamal2010] and contains the lecture's
examples. We prove the Slepian–Wolf theorem, for two sources and for `k` sources (Theorem 3), and
the optimal rate region of lossless source coding with a helper (Theorem 2).

## Conventions

* **Rates.** In bits, with the index sets `[1 : 2^{nR}) = {1, …, 2^⌊nR⌋}` of the notes.
* **Auxiliary random variables.** `U` takes values in `Fin k` for some `k`, in place of the bound
  `|U| ≤ |Y| + 1`, so that the region of Theorem 2 is stated up to closure.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The Slepian–Wolf theorem
* The codes: `SWCode` (`Network.SlepianWolf`), `IsAchievableSWBits`, `swOptimalRegionBits`,
  `swRegionBits` (`Network.SlepianWolfBits`).
* The **Slepian–Wolf theorem**: `swOptimalRegionBits_eq`, with the converse
  `IsAchievableSWBits.mem_swRegionBits` and achievability `isAchievableSWBits_of_lt`, from
  `isAchievableSW_of_lt` and `sum_bins_errProb_le` of Chapter 15 of Cover & Thomas.
* The inner bound and the corner point: `entropy_mem_swRegionBits`, `corner_mem_swRegionBits`.
* The DSBS: `entropy_dsbsPMF`, `condEntropy_dsbsPMF`, `swRegionBits_dsbsPMF` (here).
* The second example: `triPMF`, `entropy_triPMF`, `condEntropy_fst_triPMF`,
  `condEntropy_snd_triPMF`, `swRegionBits_triPMF`, `log_three_lt_separate` (here).

### Lossless source coding with a helper
* The codes: `HelperCode`, `IsAchievableHelperBits`, `helperOptimalRegionBits`
  (`Network.SourceHelper`).
* **Theorem 2**: `helperLaw`, `helperCond`, `helperInfo`, `helperRegionBits`,
  `helperOptimalRegionBits_eq` (`Network.SourceHelperConverse`).
* Achievability: `exists_bins_code` (random binning), `helperEnc`, `sum_not_mem_helperEnc_le`,
  `exists_helper_code_le`, `isAchievableHelperBits_of_lt`.
* The converse: `sum_iidPMF_mul_phi`, `entropyRV_mix`, `condEntropy_mix`,
  `HelperCode.exists_kernel_le`, `IsAchievableHelperBits.mem_closure_helperRegionBits`,
  `mem_helperRegionBits_of_kernel`.
* The DSBS, with Mrs. Gerber's lemma: `dsbsHelperRegion`, `exists_binEntropy_le_helperCond`,
  `bscKernel`, `helperCond_bsc`, `helperInfo_bsc`, `helperRegionBits_dsbsPMF` (here).

### More than two sources
* **Theorem 3**: `ManyCode`, `swPart`, `swRest`, `swCondH`, `IsAchievableManyBits`,
  `manyOptimalRegionBits`, `manyRegionBits`, `manyOptimalRegionBits_eq` (`Network.SlepianWolfMany`),
  with `ManyCode.mul_swCondH_le`, `exists_many_code_le`, `isAchievableManyBits_of_lt`.

## Not formalized

* The single-source random binning proof on pages 11-12 to 11-14 as a separate statement: it is the
  case of one source of `exists_many_code_le`, and `isAchievableLosslessRate_of_lt` of Lecture 3
  proves the theorem by another code.
* Random linear binning on pages 11-15 and 11-20, and the scheme for the DSBS with a parity check
  matrix.
* The remark on zero-error coding on page 11-19, and the extension to stationary ergodic sources on
  page 11-20.
* The bound on the cardinality of `U`, and the convexity of the region of Theorem 2.
* Theorem 4, with `k` sources and a helper.

## Issues in the notes

* **Page 11-20.** The last formula is `Ŷ₂ⁿ = X₂ⁿ ⊕ Ẑⁿ = X₂ⁿ`; it should be `X̂₂ⁿ = X₁ⁿ ⊕ Ẑⁿ = X₂ⁿ`,
  as the decoder knows `X₁ⁿ` and not `X₂ⁿ`.
* **Page 11-19.** "doubly symmetric binary symmetric sources".
* **Page 11-27.** The covering lemma gives `R₂ > I(Y; U) + δ(ε')`, not `- δ(ε')`
  (`exists_helper_code_le` has the plus sign).
* **Page 11-32.** The figure has "Encoder N" for the encoder `k`.
* **Page 11-33.** In Theorem 4, `H(X(S) | U, X(S))` should be `H(X(S) | U, X(Sᶜ))`, and
  `S ∈ [1 : k]` should be `S ⊆ [1 : k]`.
* **The converse on page 11-29.** The step (a) uses a Markov chain, which the proof of
  `HelperCode.exists_kernel_le` avoids: with `Zᵢ = (Xᵢ, Yᵢ)`,
  `I(Yᵢ; Uᵢ) = I(Yᵢ; M₂ | Zⁱ⁻¹) ≤ I(Zᵢ; M₂ | Zⁱ⁻¹)`, and the chain rule gives the bound. This is not
  an error in the notes.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 11
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Aliases -/

section Aliases

variable {α β : Type*} [Fintype α] [Fintype β] {q : α × β → ℝ}

/-- **The Slepian–Wolf theorem of Lecture 11, page 11-9.** -/
theorem slepian_wolf_theorem (hq : IsPMF q) : swOptimalRegionBits q = swRegionBits q :=
  swOptimalRegionBits_eq hq

/-- **Theorem 2 of Lecture 11, page 11-23.** Lossless source coding with a helper. -/
theorem theorem_11_2 (hq : IsPMF q) : helperOptimalRegionBits q = closure (helperRegionBits q) :=
  helperOptimalRegionBits_eq hq

/-- **Theorem 3 of Lecture 11, page 11-32.** The Slepian–Wolf theorem for `k` sources. -/
theorem theorem_11_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ι → Type*}
    [∀ j, Fintype (γ j)] {p : (∀ j, γ j) → ℝ} (hp : IsPMF p) :
    manyOptimalRegionBits p = manyRegionBits p :=
  manyOptimalRegionBits_eq hp

end Aliases

/-! ## The DSBS -/

private lemma two_negMulLog_half' (a : ℝ) : 2 * negMulLog (a / 2) = negMulLog a + a * log 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [negMulLog, negMulLog, log_div ha two_ne_zero]
    ring

/-- `H(X₁, X₂) = log 2 + H(p)` for a `DSBS(p)`. -/
theorem entropy_dsbsPMF (p : ℝ) : entropy (dsbsPMF p) = log 2 + binEntropy p := by
  rw [entropy_eq_sum_negMulLog, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [dsbsPMF, bernoulliPMF, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
    ite_true, Bool.false_eq_true, ite_false]
  have h1 := two_negMulLog_half' p
  have h2 := two_negMulLog_half' (1 - p)
  have e1 : (1 : ℝ) / 2 * p = p / 2 := by ring
  have e2 : (1 : ℝ) / 2 * (1 - p) = (1 - p) / 2 := by ring
  rw [e1, e2]
  linarith

/-- `X₂ ∼ Bern(1/2)` for a `DSBS(p)`. -/
lemma dist_snd_dsbsPMF (p : ℝ) (b : Bool) : dist (dsbsPMF p) Prod.snd b = 1 / 2 := by
  rw [dist_snd, Fintype.sum_bool]
  cases b <;> simp [dsbsPMF, bernoulliPMF] <;> ring

/-- `H(X₂) = log 2` for a `DSBS(p)`. -/
lemma entropy_snd_dsbsPMF (p : ℝ) : H[Prod.snd ; dsbsPMF p] = log 2 := by
  have e : dist (dsbsPMF p) Prod.snd = fun _ => 1 / 2 := funext (dist_snd_dsbsPMF p)
  rw [entropyRV, e, entropy_eq_sum_negMulLog, Fintype.sum_bool, negMulLog, one_div, log_inv]
  ring

/-- `H(X₁ | X₂) = H(p)` for a `DSBS(p)`. -/
theorem condEntropy_dsbsPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    H[Prod.fst | Prod.snd ; dsbsPMF p] = binEntropy p := by
  have hq := dsbsPMF_isPMF h0 h1
  have e : H[pair Prod.snd Prod.fst ; dsbsPMF p] = H[pair Prod.fst Prod.snd ; dsbsPMF p] :=
    entropyRV_eq_of_injective _ Prod.swap Prod.swap_injective fun _ => rfl
  rw [condEntropy_eq_sub hq, e, entropyRV, dist_pair_fst_snd, entropy_dsbsPMF, entropy_snd_dsbsPMF]
  ring

/-- `X₁ ∼ Bern(1/2)` for a `DSBS(p)`. -/
lemma dist_fst_dsbsPMF (p : ℝ) (b : Bool) : dist (dsbsPMF p) Prod.fst b = 1 / 2 := by
  rw [dist_fst, Fintype.sum_bool]
  cases b <;> simp [dsbsPMF, bernoulliPMF] <;> ring

/-- `H(X₁) = log 2` for a `DSBS(p)`. -/
lemma entropy_fst_dsbsPMF (p : ℝ) : H[Prod.fst ; dsbsPMF p] = log 2 := by
  have e : dist (dsbsPMF p) Prod.fst = fun _ => 1 / 2 := funext (dist_fst_dsbsPMF p)
  rw [entropyRV, e, entropy_eq_sum_negMulLog, Fintype.sum_bool, negMulLog, one_div, log_inv]
  ring

/-- **Example (Lecture 11), page 11-11.** With Slepian–Wolf coding, the `DSBS(p)` needs
`R₁ ≥ H(p)`, `R₂ ≥ H(p)`, `R₁ + R₂ ≥ 1 + H(p)`, in bits. -/
theorem swRegionBits_dsbsPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    swRegionBits (dsbsPMF p) = {R | binEntropy p / log 2 ≤ R.1 ∧ binEntropy p / log 2 ≤ R.2 ∧
      1 + binEntropy p / log 2 ≤ R.1 + R.2} := by
  have hl := log_pos one_lt_two
  have hq := dsbsPMF_isPMF h0 h1
  have e2 : H[Prod.snd | Prod.fst ; dsbsPMF p] = binEntropy p := by
    rw [condEntropy_eq_sub hq, entropyRV, dist_pair_fst_snd, entropy_dsbsPMF, entropy_fst_dsbsPMF]
    ring
  have e3 : entropy (dsbsPMF p) / log 2 = 1 + binEntropy p / log 2 := by
    rw [entropy_dsbsPMF, add_div, div_self hl.ne']
  ext R
  simp only [swRegionBits, Set.mem_ofPred_eq, condEntropy_dsbsPMF h0 h1, e2, e3]

/-! ## The second example -/

/-- **Example (Lecture 11), page 11-11.** The pmf `p(0, 0) = p(1, 0) = p(1, 1) = 1/3`, with `false`
for `0` and `true` for `1`. -/
def triPMF (z : Bool × Bool) : ℝ := if z = (false, true) then 0 else 1 / 3

lemma triPMF_isPMF : IsPMF triPMF := by
  refine ⟨fun z => ?_, ?_⟩
  · simp only [triPMF]
    split_ifs <;> norm_num
  · simp [triPMF, Fintype.sum_prod_type]
    norm_num

/-- `H(X₁, X₂) = log 3`. -/
theorem entropy_triPMF : entropy triPMF = log 3 := by
  rw [entropy_eq_sum_negMulLog, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]
  simp only [triPMF, negMulLog]
  simp
  ring

private lemma binEntropy_one_third' : binEntropy (1 / 3) = log 3 - 2 / 3 * log 2 := by
  have e : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, e, negMulLog, negMulLog,
    log_div one_ne_zero (by norm_num), log_div two_ne_zero (by norm_num), log_one]
  ring

private lemma entropy_snd_triPMF : H[Prod.snd ; triPMF] = binEntropy (1 / 3) := by
  have e : dist triPMF Prod.snd = bernoulliPMF (1 / 3) := by
    funext b
    rw [dist_snd, Fintype.sum_bool]
    cases b <;> norm_num [triPMF, bernoulliPMF]
  rw [entropyRV, e, entropy_bernoulliPMF]

private lemma entropy_fst_triPMF : H[Prod.fst ; triPMF] = binEntropy (1 / 3) := by
  have e : dist triPMF Prod.fst = bernoulliPMF (2 / 3) := by
    funext b
    rw [dist_fst, Fintype.sum_bool]
    cases b
    · simp [triPMF, bernoulliPMF]
      norm_num
    · simp [triPMF, bernoulliPMF]
      norm_num
  have e2 : (2 : ℝ) / 3 = 1 - 1 / 3 := by norm_num
  rw [entropyRV, e, entropy_bernoulliPMF, e2, binEntropy_one_sub]

/-- `H(X₁ | X₂) = log 3 - H(1/3) = (2/3) log 2`. -/
theorem condEntropy_fst_triPMF : H[Prod.fst | Prod.snd ; triPMF] = 2 / 3 * log 2 := by
  have e : H[pair Prod.snd Prod.fst ; triPMF] = H[pair Prod.fst Prod.snd ; triPMF] :=
    entropyRV_eq_of_injective _ Prod.swap Prod.swap_injective fun _ => rfl
  rw [condEntropy_eq_sub triPMF_isPMF, e, entropyRV, dist_pair_fst_snd, entropy_triPMF,
    entropy_snd_triPMF, binEntropy_one_third']
  ring

/-- `H(X₂ | X₁) = log 3 - H(1/3) = (2/3) log 2`. -/
theorem condEntropy_snd_triPMF : H[Prod.snd | Prod.fst ; triPMF] = 2 / 3 * log 2 := by
  rw [condEntropy_eq_sub triPMF_isPMF, entropyRV, dist_pair_fst_snd, entropy_triPMF,
    entropy_fst_triPMF, binEntropy_one_third']
  ring

/-- **Example (Lecture 11), page 11-11.** With Slepian–Wolf coding, this source needs `R₁ ≥ 2/3`,
`R₂ ≥ 2/3`, `R₁ + R₂ ≥ log 3`, in bits. -/
theorem swRegionBits_triPMF :
    swRegionBits triPMF = {R | 2 / 3 ≤ R.1 ∧ 2 / 3 ≤ R.2 ∧ log 3 / log 2 ≤ R.1 + R.2} := by
  have hl := log_pos one_lt_two
  have e : (2 / 3 * log 2) / log 2 = 2 / 3 := by
    field_simp
  ext R
  simp only [swRegionBits, Set.mem_ofPred_eq, condEntropy_fst_triPMF, condEntropy_snd_triPMF,
    entropy_triPMF, e]

/-- **Example (Lecture 11), page 11-11.** Compressing separately needs the sum rate `2 H(1/3)`,
which is strictly more than `log 3`, as `2⁴ < 3³`. -/
theorem log_three_lt_separate : log 3 < 2 * binEntropy (1 / 3) := by
  have h : log ((2 : ℝ) ^ 4) < log ((3 : ℝ) ^ 3) := log_lt_log (by norm_num) (by norm_num)
  rw [log_pow, log_pow] at h
  push_cast at h
  rw [binEntropy_one_third']
  linarith

/-! ## The helper for the DSBS -/

/-- **Example (Lecture 11), page 11-23.** The region `R₁ ≥ H(α ∗ p)`, `R₂ ≥ 1 - H(α)` for some
`α ∈ [0, 1/2]`, in bits. -/
def dsbsHelperRegion (p : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ a ∈ Set.Icc (0 : ℝ) (1 / 2), binEntropy (binConv a p) / log 2 ≤ R.1 ∧
    (log 2 - binEntropy a) / log 2 ≤ R.2}

section HelperDSBS

variable {p : ℝ} {k : Type*} [Fintype k] {κ : Bool → k → ℝ}

/-- The law of `(X ⊕ Y, (Y, U))` for a `DSBS(p)` pair `(X, Y)` and `U ∼ p(u | y)`. -/
private lemma dist_xor_helperLaw (κ : Bool → k → ℝ) (z y : Bool) (u : k) :
    dist (helperLaw (dsbsPMF p) κ)
        (pair (fun w => xor w.1.1 w.1.2) (pair (fun w => w.1.2) Prod.snd)) (z, (y, u)) =
      bernoulliPMF p z * (1 / 2 * κ y u) := by
  classical
  have hinj : Function.Injective fun w : (Bool × Bool) × k => (xor w.1.1 w.1.2, (w.1.2, w.2)) := by
    rintro ⟨⟨x, y⟩, u⟩ ⟨⟨x', y'⟩, u'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl, rfl⟩ := h
    have : x = x' := by
      revert h1
      cases x <;> cases x' <;> cases y <;> simp
    rw [this]
  have h := dist_comp_of_injective (helperLaw (dsbsPMF p) κ) id hinj ((xor z y, y), u)
  rw [dist_id] at h
  have e : xor (xor z y) y = z := by
    cases z <;> cases y <;> rfl
  simp only [e] at h
  refine h.trans ?_
  simp only [helperLaw, jointOf, dsbsPMF, e]
  ring

/-- **Example (Lecture 11), page 11-24.** The bound by Mrs. Gerber's lemma: for every `p(u | y)`
there is `α ∈ [0, 1/2]` with `H(X | U) ≥ H(α ∗ p)` and `I(Y; U) = log 2 - H(α)`. -/
theorem exists_binEntropy_le_helperCond (h0 : 0 ≤ p) (h1 : p ≤ 1) (hκ : ∀ y, IsPMF (κ y)) :
    ∃ a ∈ Set.Icc (0 : ℝ) (1 / 2), binEntropy (binConv a p) ≤ helperCond (dsbsPMF p) κ ∧
      log 2 - binEntropy a = helperInfo (dsbsPMF p) κ := by
  classical
  have hμ := helperLaw_isPMF (dsbsPMF_isPMF h0 h1) hκ
  set μ := helperLaw (dsbsPMF p) κ with hμd
  set Y : (Bool × Bool) × k → Bool := fun w => w.1.2
  set U : (Bool × Bool) × k → k := Prod.snd
  set Z : (Bool × Bool) × k → Bool := fun w => xor w.1.1 w.1.2
  have d3 : ∀ z y u, dist μ (pair Z (pair Y U)) (z, (y, u)) =
      bernoulliPMF p z * (1 / 2 * κ y u) := dist_xor_helperLaw κ
  have dYU : ∀ y u, dist μ (pair Y U) (y, u) = 1 / 2 * κ y u := fun y u => by
    rw [← sum_dist_pair_left μ Z (pair Y U) (y, u)]
    simp only [d3, ← sum_mul, (bernoulliPMF_isPMF h0 h1).sum_eq_one, one_mul]
  have dZ : ∀ z, dist μ Z z = bernoulliPMF p z := fun z => by
    rw [← sum_dist_pair_right μ Z (pair Y U) z, Fintype.sum_prod_type]
    simp only [d3, ← mul_sum, (hκ _).sum_eq_one, mul_one]
    simp
  have dY : ∀ y, dist μ Y y = 1 / 2 := fun y => by
    rw [← sum_dist_pair_right μ Y U y]
    simp only [dYU, ← mul_sum, (hκ y).sum_eq_one, mul_one]
  have hind : IndepRV μ Z (pair Y U) := fun z w => by
    obtain ⟨y, u⟩ := w
    rw [d3, dZ, dYU]
  have hZ : dist μ Z true = p := by
    rw [dZ]
    simp [bernoulliPMF]
  have hMG := mrsGerber_le_condEntropy_xor hμ Y U Z hZ hind
  have hX : (fun ω => xor (Y ω) (Z ω)) = fun w : (Bool × Bool) × k => w.1.1 := by
    funext w
    simp only [Y, Z]
    cases w.1.1 <;> cases w.1.2 <;> rfl
  rw [hX] at hMG
  have hv := condEntropy_bool_mem_Icc hμ Y U
  have hmem := binEntropyInv_mem hv
  have hY : H[Y ; μ] = log 2 := by
    have e : dist μ Y = fun _ => 1 / 2 := funext dY
    rw [entropyRV, e, entropy_eq_sum_negMulLog, Fintype.sum_bool, negMulLog, one_div, log_inv]
    ring
  refine ⟨binEntropyInv H[Y | U ; μ], ⟨hmem.1, by simpa using hmem.2⟩, hMG, ?_⟩
  rw [binEntropy_binEntropyInv hv]
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ Y U
  rw [hY] at hI
  exact hI.symm

/-- The channel `BSC(α)` from `Y` to `U`. -/
def bscKernel (a : ℝ) (y u : Bool) : ℝ := bernoulliPMF a (xor y u)

lemma bscKernel_isPMF {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (y : Bool) :
    IsPMF (bscKernel a y) := by
  refine ⟨fun u => (bernoulliPMF_isPMF h0 h1).nonneg _, ?_⟩
  rw [Fintype.sum_bool]
  cases y <;> simp [bscKernel, bernoulliPMF]

/-- **Example (Lecture 11), page 11-23.** With `p(u | y)` a `BSC(α)`, `H(X | U) = H(α ∗ p)`. -/
theorem helperCond_bsc (h0 : 0 ≤ p) (h1 : p ≤ 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    helperCond (dsbsPMF p) (bscKernel a) = binEntropy (binConv a p) := by
  classical
  have hμ := helperLaw_isPMF (dsbsPMF_isPMF h0 h1) (bscKernel_isPMF ha0 ha1)
  have e1 : dist (helperLaw (dsbsPMF p) (bscKernel a))
      (pair Prod.snd fun w => w.1.1) = dsbsPMF (binConv a p) := by
    funext ⟨u, x⟩
    cases u <;> cases x <;>
      simp [dist, pair, Fintype.sum_prod_type, helperLaw, jointOf, dsbsPMF, bernoulliPMF, binConv,
        bscKernel] <;> ring
  have e2 : H[Prod.snd ; helperLaw (dsbsPMF p) (bscKernel a)] = log 2 := by
    have e : (Prod.snd : (Bool × Bool) × Bool → Bool) =
        Prod.fst ∘ pair Prod.snd fun w : (Bool × Bool) × Bool => w.1.1 := rfl
    rw [entropyRV, e, dist_comp_eq, e1]
    exact entropy_fst_dsbsPMF _
  rw [helperCond, condEntropy_eq_sub hμ, e2, entropyRV, e1, entropy_dsbsPMF]
  ring

/-- **Example (Lecture 11), page 11-23.** With `p(u | y)` a `BSC(α)`, `I(Y; U) = log 2 - H(α)`. -/
theorem helperInfo_bsc (h0 : 0 ≤ p) (h1 : p ≤ 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    helperInfo (dsbsPMF p) (bscKernel a) = log 2 - binEntropy a := by
  classical
  have hμ := helperLaw_isPMF (dsbsPMF_isPMF h0 h1) (bscKernel_isPMF ha0 ha1)
  have e1 : dist (helperLaw (dsbsPMF p) (bscKernel a))
      (pair (fun w => w.1.2) Prod.snd) = dsbsPMF a := by
    funext ⟨y, u⟩
    cases y <;> cases u <;>
      simp [dist, pair, Fintype.sum_prod_type, helperLaw, jointOf, dsbsPMF, bernoulliPMF,
        bscKernel] <;> ring
  have e2 : H[fun w : (Bool × Bool) × Bool => w.1.2 ;
      helperLaw (dsbsPMF p) (bscKernel a)] = log 2 := by
    have e : (fun w : (Bool × Bool) × Bool => w.1.2) =
        Prod.fst ∘ pair (fun w : (Bool × Bool) × Bool => w.1.2) Prod.snd := rfl
    rw [entropyRV, e, dist_comp_eq, e1]
    exact entropy_fst_dsbsPMF _
  have e3 : H[Prod.snd ; helperLaw (dsbsPMF p) (bscKernel a)] = log 2 := by
    have e : (Prod.snd : (Bool × Bool) × Bool → Bool) =
        Prod.snd ∘ pair (fun w : (Bool × Bool) × Bool => w.1.2) Prod.snd := rfl
    rw [entropyRV, e, dist_comp_eq, e1]
    exact entropy_snd_dsbsPMF _
  rw [helperInfo, mutualInfo_eq_add_sub hμ, e2, e3, entropyRV, e1, entropy_dsbsPMF]
  ring

end HelperDSBS

/-- **Example (Lecture 11), page 11-23.** For a `DSBS(p)` the region of Theorem 2 reduces to
`R₁ ≥ H(α ∗ p)`, `R₂ ≥ 1 - H(α)` for some `α ∈ [0, 1/2]`, in bits. The notes take `p ∈ [0, 1/2]`. -/
theorem helperRegionBits_dsbsPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    helperRegionBits (dsbsPMF p) = dsbsHelperRegion p := by
  have hl := log_pos one_lt_two
  have hq := dsbsPMF_isPMF h0 h1
  refine Set.Subset.antisymm ?_ ?_
  · rintro R ⟨k, κ, hκ, h₁, h₂⟩
    obtain ⟨a, ha, h3, h4⟩ := exists_binEntropy_le_helperCond h0 h1 hκ
    refine ⟨a, ha, (div_le_div_of_nonneg_right h3 hl.le).trans h₁, ?_⟩
    rwa [h4]
  · rintro ⟨R₁, R₂⟩ ⟨a, ⟨ha0, ha1⟩, h₁, h₂⟩
    have ha1' : a ≤ 1 := ha1.trans (by norm_num)
    refine mem_helperRegionBits_of_kernel hq (bscKernel_isPMF ha0 ha1') ?_ ?_
    · rwa [helperCond_bsc h0 h1 ha0 ha1']
    · rwa [helperInfo_bsc h0 h1 ha0 ha1']

end InfoTheory.ElGamalKim
