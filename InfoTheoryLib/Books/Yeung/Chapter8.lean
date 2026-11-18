/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Binary
public import InfoTheoryLib.RateDistortion.ExcessDistortion

/-!
# Yeung, Chapter 8: Rate-Distortion Theory

This file indexes the formalization of Chapter 8 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Logarithms and rates.** Logarithms are natural, so rates are in nats per symbol.
* **Distortion measures.** A distortion measure is `d : α → β → ℝ` with `∀ x y, 0 ≤ d x y`. The
  source law is `p : α → ℝ` with `IsPMF p`; the book's assumption that `p` has full support is not
  needed.
* **Normal distortion measures.** The book assumes from Section 8.3 on that `d` is normal, so that
  `D_min = 0`. The statements here do not: they hold for `D ≥ D_min`, where
  `D_min = ∑ₓ p(x) min_x̂ d(x, x̂)` is `minDistortion p d`, the constant `Δ` of (8.16). Below
  `D_min` no pair `(R, D)` is achievable, and `R(D)` is not defined in the book (in Lean it is
  `sInf ∅ = 0`).
* **Achievability.** The book's achievable pairs (Definition 8.10) are `IsAchievableRDProb`, with a
  probability of excess distortion. The library's `IsAchievableRD` (Cover & Thomas) asks for the
  expected distortion instead; both give the region `{(R, D) | D ≥ D_min, R ≥ R^(I)(D)}`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 8.1 Single-Letter Distortion Measures
* Definition 8.1: a function `d : α → β → ℝ`.
* Definition 8.2: `seqDistortion` (`RateDistortion.Basic`).
* Example 8.3: `squareErrorDistortion`, `isNormalDistortion_squareErrorDistortion`
  (`RateDistortion.Normal`).
* Example 8.4: `hammingDistortion` (`RateDistortion.Basic`), `isNormalDistortion_hammingDistortion`
  (`RateDistortion.Normal`). (8.7): `sum_mul_hammingDistortion` (`RateDistortion.Normal`).
* Definition 8.5: `IsNormalDistortion`, and the normalization (8.9) `normalizeDistortion`,
  `isNormalDistortion_normalizeDistortion` (`RateDistortion.Normal`).
* Example 8.6: `example_8_6` (here).
* (8.10)–(8.16): `expDistortion_normalizeDistortion` (`RateDistortion.Normal`), with
  `Δ = minDistortion p d` (`RateDistortion.Basic`).
* Definition 8.7: `dMax`, `exists_dMax_eq`, `minDistortion_le_dMax` (`RateDistortion.Normal`).
* (8.18)–(8.19): `exists_eventually_prob_const_gt_le` (`RateDistortion.ExcessDistortion`).

### 8.2 The Rate-Distortion Function R(D)
* Definition 8.8: `RDCode` (`RateDistortion.Basic`), with indices `Fin M = {0, …, M - 1}`.
* Definition 8.9: `codeRate` (`ChannelCoding.AsymptoticRate`).
* Definition 8.10: `IsAchievableRDProb`, and the remark after it, `IsAchievableRDProb.mono`
  (`RateDistortion.ExcessDistortion`).
* Definition 8.11: `rdRegionProb` (`RateDistortion.ExcessDistortion`).
* Theorem 8.12: `theorem_8_12` (here), from `isClosed_rdRegionProb` and `convex_rdRegionProb`
  (`RateDistortion.ExcessDistortion`). Both follow from the description of the region by
  `R^(I)` (`rdRegionProb_eq`), not from the book's limit and time-sharing arguments.
* Definitions 8.13 and 8.14: `rateDistortionProb`, `distortionRateProb`
  (`RateDistortion.ExcessDistortion`).
* Theorem 8.15: `theorem_8_15` (here), which is `rateDistortionProb_properties`
  (`RateDistortion.ExcessDistortion`), proved from Theorems 8.17 and 8.18.

### 8.3 The Rate-Distortion Theorem
* Definition 8.16: `infoRD`, and the minimum (8.59) is attained, `exists_infoRD_eq`
  (`RateDistortion.Basic`).
* (8.62): `infoRD_normalizeDistortion` (`RateDistortion.Normal`).
* Theorem 8.17: `theorem_8_17` (here), which is `rateDistortionProb_eq_infoRD`
  (`RateDistortion.ExcessDistortion`).
* Theorem 8.18: `theorem_8_18` (here), from `infoRD_antitoneOn`, `infoRD_convexOn`
  (`RateDistortion.Basic`), `infoRD_eq_zero_of_dMax_le` and `infoRD_le_entropy`
  (`RateDistortion.Normal`).
* Corollary 8.19: `corollary_8_19` (here), from `infoRD_pos`, `strictAntiOn_infoRD` and
  `expDistortion_eq_of_infoRD_eq` (`RateDistortion.Normal`). The hypothesis `R^(I)(0) > 0` is not
  needed: the book's proof that `R^(I)(D) > 0` for `D < D_max` does not use it.
* Example 8.20: `example_8_20` (here), from `infoRD_bernoulli` (`RateDistortion.Binary`), with
  `D_max = min(γ, 1 - γ)`, (8.99)–(8.101). The reverse BSC (8.114)–(8.123) is in the proof of
  `infoRD_bernoulli_le`.

### 8.4 The Converse
* (8.125)–(8.151): `IsAchievableRDProb.mem_epigraph` (`RateDistortion.ExcessDistortion`), with
  (8.127)–(8.141) from `RDCode.mul_infoRD_le_log` (`RateDistortion.Converse`). The limit
  (8.148)–(8.150) uses that the epigraph of `R^(I)` is closed (`isClosed_epigraph_infoRD`,
  `RateDistortion.Theorem`) instead of the continuity of `R^(I)`.

### 8.5 Achievability of R_I(D)
* (8.152)–(8.201): `isAchievableRDProb_of_expDistortion_le` (`RateDistortion.ExcessDistortion`).
* (8.156)–(8.182): `sum_codebook_miss_distortionTypicalSet_le` (`RateDistortion.ExcessDistortion`),
  with (8.171)–(8.174) in the form of `one_sub_mul_pow_le` (`RateDistortion.Achievability`). The
  encoder looks for a distortion typical codeword (`typicalRDCode`), which uses weak joint
  typicality, instead of the book's strongly typical codeword; this needs neither Theorem 6.10 nor
  Proposition 6.13.

## Not formalized

* Figures 8.1 to 8.4.
* The remark after Example 8.20 comparing the rate-distortion theorem with the source coding
  theorem.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 8
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Worked examples -/

/-- The distortion measure of Example 8.6, with source symbols `1, 2` as `0, 1 : Fin 2` and
reproduction symbols `a, b, c` as `0, 1, 2 : Fin 3`. -/
def distortion_8_6 : Fin 2 → Fin 3 → ℝ := ![![2, 7, 5], ![4, 3, 8]]

/-- Its normalization, from Example 8.6. -/
def normalized_8_6 : Fin 2 → Fin 3 → ℝ := ![![0, 5, 3], ![1, 0, 5]]

lemma ciInf_eq_of_le {f : Fin 3 → ℝ} {i : Fin 3} (h : ∀ j, f i ≤ f j) : ⨅ j, f j = f i :=
  le_antisymm (ciInf_le (Set.finite_range f).bddBelow i) (le_ciInf h)

/-- **Example 8.6.** The normalization of `distortion_8_6` is `normalized_8_6`, which is normal. -/
theorem example_8_6 :
    normalizeDistortion distortion_8_6 = normalized_8_6 ∧ IsNormalDistortion normalized_8_6 := by
  have h₀ : ⨅ j, distortion_8_6 0 j = 2 := by
    rw [ciInf_eq_of_le (i := 0) fun j => by fin_cases j <;> norm_num [distortion_8_6]]
    simp [distortion_8_6]
  have h₁ : ⨅ j, distortion_8_6 1 j = 3 := by
    rw [ciInf_eq_of_le (i := 1) fun j => by fin_cases j <;> norm_num [distortion_8_6]]
    simp [distortion_8_6]
  refine ⟨funext fun x => funext fun y => ?_, fun x => ?_⟩
  · fin_cases x
    · change distortion_8_6 0 y - ⨅ y', distortion_8_6 0 y' = normalized_8_6 0 y
      rw [h₀]
      fin_cases y <;> norm_num [distortion_8_6, normalized_8_6]
    · change distortion_8_6 1 y - ⨅ y', distortion_8_6 1 y' = normalized_8_6 1 y
      rw [h₁]
      fin_cases y <;> norm_num [distortion_8_6, normalized_8_6]
  · fin_cases x
    · exact ⟨0, by simp [normalized_8_6]⟩
    · exact ⟨1, by simp [normalized_8_6]⟩

/-- **Example 8.20 (Binary Source), (8.99)–(8.101) and (8.124).** For a binary source with
`Pr{X = 1} = γ` and the Hamming distortion measure, `D_max = min(γ, 1 - γ)` and
`R^(I)(D) = h_b(γ) - h_b(D)` for `D ≤ min(γ, 1 - γ)`, and `0` otherwise. -/
theorem example_8_20 {γ D : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (hD : 0 ≤ D) :
    dMax (bernoulliPMF γ) hammingDistortion = min γ (1 - γ) ∧
      infoRD (bernoulliPMF γ) hammingDistortion D =
        if D ≤ min γ (1 - γ) then binEntropy γ - binEntropy D else 0 := by
  refine ⟨?_, infoRD_bernoulli h0 h1 hD⟩
  have hf : ∑ x, bernoulliPMF γ x * hammingDistortion x false = γ := by
    simp [bernoulliPMF, hammingDistortion]
  have ht : ∑ x, bernoulliPMF γ x * hammingDistortion x true = 1 - γ := by
    simp [bernoulliPMF, hammingDistortion]
  refine le_antisymm (le_min ?_ ?_) (le_ciInf fun y => ?_)
  · exact (dMax_le _ _ false).trans_eq hf
  · exact (dMax_le _ _ true).trans_eq ht
  · cases y
    · rw [hf]; exact min_le_left _ _
    · rw [ht]; exact min_le_right _ _

/-! ### Aliases -/

/-- **Theorem 8.12.** The rate-distortion region is closed and convex. -/
theorem theorem_8_12 {β : Type*} [Finite β] [Nonempty β] {p : α → ℝ} {d : α → β → ℝ}
    (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) :
    IsClosed (rdRegionProb p d) ∧ Convex ℝ (rdRegionProb p d) :=
  ⟨isClosed_rdRegionProb hp hd, convex_rdRegionProb hp hd⟩

/-- **Theorem 8.15.** -/
alias theorem_8_15 := rateDistortionProb_properties

/-- **Theorem 8.17 (The Rate-Distortion Theorem).** -/
alias theorem_8_17 := rateDistortionProb_eq_infoRD

/-- **Theorem 8.18.** `R^(I)(D)` is nonincreasing and convex for `D ≥ D_min`, `R^(I)(D) = 0` for
`D ≥ D_max`, and `R^(I)(0) ≤ H(X)` for a normal distortion measure. -/
theorem theorem_8_18 [Nonempty β] {p : α → ℝ} {d : α → β → ℝ} (hp : IsPMF p) :
    AntitoneOn (infoRD p d) (Set.Ici (minDistortion p d)) ∧
      ConvexOn ℝ (Set.Ici (minDistortion p d)) (infoRD p d) ∧
      (∀ D, dMax p d ≤ D → infoRD p d D = 0) ∧
      (IsNormalDistortion d → infoRD p d 0 ≤ entropy p) :=
  ⟨infoRD_antitoneOn hp, infoRD_convexOn hp, fun _ hD => infoRD_eq_zero_of_dMax_le hp hD,
    infoRD_le_entropy hp⟩

/-- **Corollary 8.19.** `R^(I)(D)` is strictly decreasing for `D_min ≤ D ≤ D_max`, and a test
channel achieving `R^(I)(D)` there has expected distortion exactly `D`. -/
theorem corollary_8_19 [Nonempty β] {p : α → ℝ} {d : α → β → ℝ} (hp : IsPMF p) :
    StrictAntiOn (infoRD p d) (Set.Icc (minDistortion p d) (dMax p d)) ∧
      ∀ D ∈ Set.Icc (minDistortion p d) (dMax p d), ∀ q : α → β → ℝ, IsChannel q →
        expDistortion p q d ≤ D → mutualInfoOf p q = infoRD p d D → expDistortion p q d = D :=
  ⟨strictAntiOn_infoRD hp, fun _ hD _ hq hqD hqI => expDistortion_eq_of_infoRD_eq hp hD hq hqD hqI⟩

end InfoTheory.Yeung
