/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungCases
public import InfoTheoryLib.Network.BergerTungOuter
public import InfoTheoryLib.Network.QuadraticGaussian

/-!
# El Gamal & Kim, Lecture 13: Distributed Lossy Source Coding

This file indexes the formalization of Lecture 13 of [elgamal2010]. We prove the Berger–Tung inner
bound (Theorem 1), with the Markov lemma, the mutual packing lemma and time sharing, and the
Berger–Tung outer bound (Theorem 2), as statements about codes. For the quadratic Gaussian problem
and the Gaussian CEO problem, whose sources are continuous, we prove the formulas and the algebra of
the notes.

## Conventions

* **Rates.** The operational rates are in bits, with the index sets `[1 : 2^{nR})` of the notes. The
  informations `btRate₁`, `btRate₂` and `btRate₁₂`, and the formulas of the Gaussian problems, are
  in nats.
* **Time sharing.** The informations given `Q` of Theorem 1 are the means `∑_q p(q) I(· | Q = q)`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The problem (pages 13-2 and 13-3)
* `DistLossyCode`, `DistLossyCode.output`, `DistLossyCode.distortion₁`, `DistLossyCode.distortion₂`,
  `IsAchievableDL`, `dlRegion` (`Network.BergerTung`).

### The Markov lemma and Lemma 2 (pages 13-6, 13-11 and 13-45 to 13-50)
* The Chernoff bound: `sum_prod_mul_exp_sum_le`, `sum_prod_ge_le`, `sum_prod_abs_ge_le`
  (`Typicality.MarkovLemma`).
* The conditional typicality lemma with an exponential bound: `condExpBound`,
  `one_sub_condExpBound_le_prob`, `exists_mul_condExpBound_tendsto`.
* **The Markov lemma**: `sum_not_mem_condRobust_le`, `markov_lemma` (here).
* **Lemma 2**: `firstIn`, `firstIn_spec`, `sum_codebook_firstIn_le` (`Network.BergerTung`).

### The Berger–Tung inner bound (pages 13-4 to 13-13)
* The law: `btLaw`, `btQ₃`, `btJ₁`, `btJ₂`, `btLaw_markov`, `btUU` (`Network.BergerTung`,
  `Network.BergerTungBinning`).
* The events `E₁`, `E₂` and `E₃`: `coverExp`, `sum_codebook_markov_le`, `sum_codebook_cond_le`,
  `btCoverBound`, `sum_two_codebooks_le`.
* **The mutual packing lemma**: `btPackExp`, `sum_iidPMF_snd_typical_le`,
  `sum_iidPMF_fst_typical_le`, `prob_mutual_packing_le`, `mutual_packing_lemma` (here).
* The event `E₄`, with random bins: `btIndex`, `btIndex_not_mem_le`, `sum_bins_bt_le`,
  `exists_bt_code_le`.
* The rates: `btRate₁`, `btRate₂`, `btRate₁₂`, `btRate₁_eq`, `btRate₂_eq`, `btRate₁₂_eq`,
  `eventually_bt_code` (`Network.BergerTungInner`).
* The inner bound for a constant `Q`: `btCost₁`, `btCost₂`, `isAchievableDL_of_lt`.
* Time sharing: `DistLossyCode.append`, `DistLossyCode.distortion₁_append`,
  `DistLossyCode.distortion₂_append`, `dlAchievableSet`, `convex_dlAchievableSet`,
  `exists_rate_split`, `IsAchievableDL.mono` (`Network.BergerTungSharing`).
* **Theorem 1**: `isAchievableDL_of_lt_sharing`, `theorem_13_1` (here).
* The bound on the alphabets of Theorem 1: `exists_bt_reduce₁`, `exists_bt_reduce₂`,
  `exists_bt_reduce`, `exists_bt_sharing_card` (`Network.BergerTungCardinality`).

### The special cases of the inner bound (page 13-5)
* `D₂ = 0` for the Hamming distortion: `isAchievableDL_of_side` (`Network.BergerTungCases`), with
  `btLaw_identity`, `btRate₁_identity`, `btRate₂_identity`, `btRate₁₂_identity`.
* The Wyner–Ziv rate: `isAchievableDL_of_wyner_ziv`. The Slepian–Wolf rates:
  `isAchievableDL_slepian_wolf`.

### The Berger–Tung outer bound (pages 13-14 and 13-15)
* The bound: `dlOuterAt`. **Theorem 2**: `IsAchievableDL.dlOuterAt`, `theorem_13_2` (here), with
  `DistLossyCode.dlOuterAt_of_code`, `condEntropy_mix_prefix`, `condEntropy_sub_condEntropy_le`
  (`Network.BergerTungOuter`), and `exists_mix_kernel_comp` (`RateDistortion.SideInfoConverse`).

### The quadratic Gaussian problem (pages 13-16 to 13-32 and 13-51 to 13-54)
All in `Network.QuadraticGaussian`, as formulas.
* The region of Theorem 3: `qgR`, `qgG`, `qgPhi`, `qgRegion`.
* Test channels: `qgDelta`, `qgD₁`, `qgD₂`, **Lemma 4** `qg_lemma4`, `qgG_corner`, `qgR_corner_sum`,
  `qgD_ratio`, `qg_case1`, `qg_case2_sum`.
* **Lemma 3**: `qgPhi_corner`, `qg_lemma3`.
* The converse: `qgTheta`, `qgN`, `qgR1`, `qgR2`, `qgTheta_quadratic`, `qgTheta_mem`, `qgR1_theta`,
  `qgR2_theta`, `qg_le_max`, and for Lemma 5 `qg_markov`, `qg_alpha`, `qg_lemma5_step3`.

### The Gaussian CEO problem (pages 13-33 to 13-38)
* `ceoRegion`, `ceo_bound_eq`, `ceo_test_channel` (`Network.QuadraticGaussian`), as formulas.

## Not formalized

* A bound on the alphabets in the outer bound of Theorem 2, which the notes do not state either. So
  we prove the outer bound with `Dⱼ + ε` for every `ε > 0` in place of `Dⱼ`. The technique of
  Appendix C does not give one: `U₁` and `U₂` have a joint law, so reducing `U₁` has to preserve the
  law of `(X₁, X₂, U₂)`, whose size depends on `|U₂|`, and the same holds for `U₂`.
* The tightness statements of pages 13-5 and 13-15, that is the converse of Berger and Yeung for
  `D₂ = 0`, and the outer bound for `X₂` a function of `X₁`.
* The counterexample for the doubly symmetric binary source (pages 13-39 and 13-40), the
  rate–distortion region of Kaspi and Berger, and the proof that the Berger–Tung inner bound is not
  tight.
* The coding theorems of the quadratic Gaussian problem (Theorem 3) and of the Gaussian CEO problem,
  which concern continuous sources and use the conditional entropy power inequality. We only check
  the formulas.
* Lemma 5 for the actual error covariance `K̂`, and steps (a) to (e) of its proof.
* Deterministic binning, replaced by random binning, and the analogue of Lemma 1 of Lecture 12.
* The hypergeometric proof of the Markov lemma, replaced by the change of measure below.
* More than two sources (page 13-41).

## Differences from the notes

* **The bound on the alphabets of Theorem 1.** We prove `|Uⱼ| ≤ |Xⱼ| + 3`, one less than the
  `|Xⱼ| + 4` of the notes. The three rates depend on `I(U₁; X₁)`, `I(U₂; X₂)` and `I(U₁; U₂)` only,
  so that two functions preserve them when `U₁` is reduced. The distortions may decrease.
* **The Markov lemma.** The notes bound a hypergeometric random variable.
  `sum_not_mem_condRobust_le` compares the law `φ` of `Zⁿ` with the product law on `T(Z | yⁿ)`,
  within a factor `e^{n (E - E')}`, and uses the Chernoff bound for the product law. Its hypothesis
  on `φ` is only the upper bound on `T(Z | yⁿ)`.
* **Lemma 2.** `sum_codebook_firstIn_le` gives the law of the selected codeword exactly: it is the
  law of a codeword conditioned on the typical set.

## Issues in the notes

These come from the text of the notes as extracted from the PDF.

* **Page 13-30.** `R₂(θ)` is written with `(2 (1 + θ) + N)²`. The bound of Lemma 5 gives the first
  power, `|K_X| (2 (1 + θ) + N) / (N D₁ D₂ (1 + θ)²)`, and only this makes `R₁(θ*) = R₂(θ*)` on page
  13-31 true (`qgR2`, `qgR2_theta`).
* **Page 13-23.** `R̃₁ = g₂(R̃₂, D₁)` should be `g₁(R̃₂, D₁)`.
* **Page 13-25.** "the capacity region" should be the rate–distortion region.
* **Page 13-40.** "the rate region of Theorem 5": the lecture has no Theorem 5; Theorem 1 is meant.
* **Pages 13-47 and 13-48.** Factors of `n` are missing: `|n_y - n p(y)| ≤ ε' p(y)`,
  `(1 - δ) p(x, y, z) ≤ E(K)`, and the Chernoff bound `2 e^{-(ε - δ)² p(x, y, z) / 4}`, which must
  have `n` in the exponent to tend to `0`.
* **Page 13-52.** `μᵀ μ` should be `μ μᵀ`.
* **Page 13-12.** The bound on `E₄` refers to Lemma 1 of Lecture 12, whose proof has the gap listed
  in `Books.ElGamalKim.Lecture12`. Random bins avoid it.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Aliases -/

section Aliases

variable {α₁ α₂ β₁ β₂ υ₁ υ₂ Q : Type*} [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂]
  [Fintype Q] {P : α₁ × α₂ → ℝ} {d₁ : α₁ → β₁ → ℝ} {d₂ : α₂ → β₂ → ℝ}

/-- **Theorem 1 of Lecture 13, page 13-4: the Berger–Tung inner bound.** -/
theorem theorem_13_1 [Finite β₁] [Finite β₂] (hP : IsPMF P) (hd₁ : ∀ x y, 0 ≤ d₁ x y)
    (hd₂ : ∀ x y, 0 ≤ d₂ x y) {τ : Q → ℝ} (hτ : IsPMF τ) {κ₁ : Q → α₁ → υ₁ → ℝ}
    {κ₂ : Q → α₂ → υ₂ → ℝ} (h₁ : ∀ q, IsChannel (κ₁ q)) (h₂ : ∀ q, IsChannel (κ₂ q))
    (f₁ : Q → υ₁ → υ₂ → β₁) (f₂ : Q → υ₁ → υ₂ → β₂) {R₁ R₂ D₁ D₂ : ℝ}
    (hc₁ : ∑ q, τ q * btCost₁ P (κ₁ q) (κ₂ q) d₁ (f₁ q) ≤ D₁)
    (hc₂ : ∑ q, τ q * btCost₂ P (κ₁ q) (κ₂ q) d₂ (f₂ q) ≤ D₂)
    (hR₁ : (∑ q, τ q * btRate₁ P (κ₁ q) (κ₂ q)) / log 2 < R₁)
    (hR₂ : (∑ q, τ q * btRate₂ P (κ₁ q) (κ₂ q)) / log 2 < R₂)
    (hR₁₂ : (∑ q, τ q * btRate₁₂ P (κ₁ q) (κ₂ q)) / log 2 < R₁ + R₂) :
    IsAchievableDL P d₁ d₂ R₁ R₂ D₁ D₂ :=
  isAchievableDL_of_lt_sharing hP hd₁ hd₂ hτ h₁ h₂ f₁ f₂ hc₁ hc₂ hR₁ hR₂ hR₁₂

/-- **Theorem 2 of Lecture 13, page 13-14: the Berger–Tung outer bound.** -/
theorem theorem_13_2 (hP : IsPMF P) {R₁ R₂ D₁ D₂ : ℝ} (h : IsAchievableDL P d₁ d₂ R₁ R₂ D₁ D₂)
    {ε : ℝ} (hε : 0 < ε) : dlOuterAt P d₁ d₂ R₁ R₂ (D₁ + ε) (D₂ + ε) :=
  h.dlOuterAt hP hε

end Aliases

/-- **The Markov lemma of Lecture 13, page 13-6.** -/
theorem markov_lemma {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] {q : (α × β) × γ → ℝ}
    {κ : β → γ → ℝ} {n : ℕ} {x : Fin n → α} {y : Fin n → β} {ε ε' : ℝ} (hqP : IsPMF q)
    (hκ : IsChannel κ) (hq : ∀ a b c, q ((a, b), c) = marg q (a, b) * κ b c) (hεε : ε' < ε)
    (hε1 : ε - ε' ≤ 1) (hn : 0 < n) (hxy : zipSeq x y ∈ robustTypicalSet (margFst q) n ε')
    {φ : (Fin n → γ) → ℝ} (hφ : ∀ z, 0 ≤ φ z) (A : Finset (Fin n → γ)) {E E' : ℝ}
    (hA : ∀ z ∈ A, exp (-(n * E)) ≤ channelExt κ n y z)
    (hφA : ∀ z ∈ A, φ z ≤ exp (-(n * E'))) :
    ∑ z, (open Classical in if z ∉ condRobustTypicalSet q ε (zipSeq x y) then φ z else 0) ≤
      ∑ z, (open Classical in if z ∉ A then φ z else 0) +
        exp (n * (E - E')) * condExpBound q ε' ε n :=
  sum_not_mem_condRobust_le hqP hκ hq hεε hε1 hn hxy hφ A hA hφA

/-- **The mutual packing lemma of Lecture 13, page 13-12.** -/
theorem mutual_packing_lemma {a b : Type*} [Fintype a] [Fintype b] {J : a × b → ℝ} {n : ℕ} {ε : ℝ}
    (hJ : IsPMF J) (hε : 0 ≤ ε) {L₁ L₂ : ℕ} {ρ₁ : (Fin L₁ → Fin n → a) → ℝ}
    {ρ₂ : (Fin L₂ → Fin n → b) → ℝ} (hρ₁ : IsPMF ρ₁) (hρ₂ : IsPMF ρ₂)
    (h₂ : ∀ (l : Fin L₂) (F : (Fin n → b) → ℝ), ∑ C, ρ₂ C * F (C l) =
      ∑ v, iidPMF (margSnd J) n v * F v) :
    ∑ C₁, ρ₁ C₁ * ∑ C₂, ρ₂ C₂ * (open Classical in
      if ∃ l₁ l₂, zipSeq (C₁ l₁) (C₂ l₂) ∈ robustTypicalSet J n ε then (1 : ℝ) else 0) ≤
      L₁ * L₂ * exp (-(n * btPackExp J ε)) :=
  prob_mutual_packing_le hJ hε hρ₁ hρ₂ h₂

end InfoTheory.ElGamalKim
