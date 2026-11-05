/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture14Binary
public import InfoTheoryLib.Network.MDGaussian

/-!
# El Gamal & Kim, Lecture 14: Multiple Descriptions

This file indexes the formalization of Lecture 14 of [elgamal2010]. We prove the Zhang–Berger inner
bound (Theorem 4), which gives the El Gamal–Cover inner bound (Theorem 1), the simple outer bound,
the three special cases, successive refinement (Theorem 3), Proposition 1 and the binary examples,
as statements about codes. For the quadratic Gaussian problem (Theorem 2), whose source is
continuous, we prove the formulas and the algebra, and show that the formula of the notes needs an
extra condition.

## Conventions

* **Rates.** The operational rates are in bits, with the index sets `[1 : 2^{nR})` of the notes. The
  mutual informations and the formulas of the Gaussian problem are in nats, so that
  `I(X; X̂₁) < R₁` of the notes is `I[X : Y₁ ; μ] < R₁ * log 2`.
* **Random variables.** In the inner bounds, `X`, `U`, `X̂ⱼ` are random variables on a finite
  probability space, and the source law is `dist μ X`. In the outer bound and in the regions they
    are
  given by a test channel `p(x̂₀, x̂₁, x̂₂|x)`.
* **Removing a decoder.** `Dⱼ = ∞` in the notes is the alphabet `Unit` with the distortion measure
  `0` and `Dⱼ = 0` here.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The problem (pages 14-2 and 14-3)
* `MDCode`, `MDCode.distortion₀`, `MDCode.distortion₁`, `MDCode.distortion₂`, `IsAchievableMD`,
  `mdRegion` (`Network.MultipleDescriptions`).

### The simple outer bound (page 14-6)
* `mdOuterAt`, `mutualInfo_mix_le`, `MDCode.mdOuterAt_of_code`, `isClosed_mdOuter`,
  `IsAchievableMD.mdOuter`, **`mdRegion_subset_mdOuter`**, `simple_outer_bound` (`Network.MDOuter`,
  here).
* The excess rate, page 14-7: `infoRD_le_of_mem_mdRegion₀`, `infoRD_le_of_mem_mdRegion₁`,
  `infoRD_le_of_mem_mdRegion₂` (`Network.MDCases`).

### The inner bounds (pages 14-7, 14-11 to 14-14 and 14-27 to 14-31)
* The choice of the layers: `exists_layer` (`Network.MultipleDescriptions`), `exists_three_layers`,
  `exists_zb_chain` (`Network.ZhangBerger`).
* The joint typicality lemma for random variables: `triLaw`, `prob_triLaw_le`,
  `eventually_triLaw_ge` (`Network.MDCovering`).
* The covering bounds: `eventually_sum_first_codebook_le`, `eventually_sum_last_codebook_le`.
* **The conditional multivariate covering lemma**: `eventually_sum_two_codebooks_le`.
* The code: `exists_mdCode_of_chain`, `exists_zb_code_of_bounds`, `eventually_zb_code`,
  `isAchievableMD_of_split` (`Network.ZhangBerger`).
* The Fourier–Motzkin step: `exists_zb_split`, `zb_J_eq`, `zb_J_comm`, `zb_J_ge`, `zb_sum_eq`.
* **Theorem 4 (Zhang–Berger)**: `isAchievableMD_zhangBerger`, `theorem_14_4` (here).
* **Theorem 1 (El Gamal–Cover)**: `isAchievableMD_elGamalCover` (`Network.MDCases`),
  `theorem_14_1` (here), with a constant `Q`: `isAchievableMD_of_lt`; for the closure:
  `mem_mdRegion_of_le`.
* The alternative form of the Zhang–Berger bound, one inclusion, pages 14-30 and 14-31:
  `condMutualInfo_comp_cond_le`, `isAchievableMD_of_auxiliary`.

### The special cases (pages 14-4 and 14-5)
* Case 1, no combined description: `mem_mdRegion_no_combined_iff`, `mutualInfo_pair_add_eq`
  (`Network.MDCases`).
* Case 2, one description with two reproductions: `mem_srRegion_zero_iff`.
* Case 3, combined description only: `mem_mdRegion_combined_only_iff`.
These show that the simple outer bound is tight for these cases, as page 14-6 says.

### The Bernoulli example (pages 14-9 and 14-10)
* `mdSigma`, `mdExLaw`, `mdExX`, `half_log_two_le`, `mutualInfo_mdExX_fst_le`,
  `mutualInfo_mdExX_snd_le`, `mutualInfo_mdEx_fst_snd`, **`md_bernoulli_no_excess`**,
  `md_bernoulli_lower` (`Books.ElGamalKim.Lecture14Binary`).

### The quadratic Gaussian problem (pages 14-15 to 14-21)
* The test channels: `mdNoise`, `mdNoise_var`, `mdNoise_mse`, `mdNoise_info`, `mdNoise_sub`,
  `add_mdNoise` (`Network.MDGaussian`).
* The region: `ozarowA`, `ozarowB`, `ozarowRatio`, `ozarowDelta`, `ozarowRegion`.
* High distortion: `mdNoise_high_distortion`, `exists_rho_of_high_distortion`.
* Low distortion: `ozarowA_lt_ozarowB`, `ozarow_denom_pos`, `ozarow_corr_sq`.
* The maximization in the converse: `ozarowN`, `ozarow_sq_identity`, `ozarow_ratio_le`,
  `ozarow_sqrt_eq`, `ozarow_opt`, `ozarow_ratio_ozarowN`, `ozarow_disc_identity`,
  `ozarowN_pos_iff`.
* The extra condition: `mdNoise_indep_inv`, `ozarow_counterexample`.

### Successive refinement (pages 14-22 to 14-26)
* **Theorem 3**: `srRegion`, `mem_srRegion_iff` (`Network.MDCases`), `theorem_14_3` (here).
* **Proposition 1**: `IsSuccessivelyRefinable`, `exists_markov_channel_of_rv`,
  `isSuccessivelyRefinable_iff`, `proposition_14_1` (here).
* The binary source, page 14-24: `entropy_bscKernel`, `exists_constant_of_min_le`,
  `refinable_constant`, `cascadeLaw`, `refinable_cascade`, **`isSuccessivelyRefinable_bernoulli`**
  (`Books.ElGamalKim.Lecture14Binary`).
* The Gaussian source, page 14-25: `qgR_refinement`, `gaussian_refinement_vars`
  (`Network.MDGaussian`).

## Not formalized

* The cardinality bound `|𝒰| ≤ |𝒳| + 5` of Theorem 4. The theorem is proved for every finite `𝒰`,
  which is the direction it is used in.
* The statement on page 14-27 that the Zhang–Berger region is convex.
* The other inclusion of the alternative form of the Zhang–Berger bound, page 14-31, by corner
  points, the functional representation lemma and time sharing.
* The tightness of the El Gamal–Cover bound when `X̂₁` recovers a function of `X` [2] and without
  excess rate [3], and that it is not tight in general [5]; the numerical example on page 14-30.
* `D_min ≥ 0.11` and `D_min ≤ (√2 - 1)/2` as statements about an infimum on page 14-9, and the
  optimality `D_min = (√2 - 1)/2` of [6] on page 14-10. We prove the rate pair for
  `D = (√2 - 1)/2` and the inequality `1/2 ≥ 1 - H(D)`.
* The simple scheme with `D = 1/4` on page 14-9.
* The Gaussian coding theorems: Theorem 2 as a statement about codes needs a theory of continuous
  sources and the conditional entropy power inequality, which the library does not have. The
  heuristic argument and its rigorous form [9] on page 14-25, and the remark on page 14-21.
* Extensions to more than two descriptions, page 14-32.

## Differences from the notes

* **Theorem 4 first.** We prove Theorem 4 once, and Theorem 1 is the special case `U = Q`: a time
  sharing variable independent of `X` is a common description of rate `I(U; X) = 0`. So no separate
  time sharing argument and no convexity of the region are needed, unlike page 14-14.
* **Choice of the codebooks.** The notes use one random codebook with a tree structure. We choose
  the
  codebooks one layer at a time (`exists_layer`): given the previous layers and the encoder so far,
  each conditional codebook is chosen separately by averaging. Each layer then only involves
  independent codewords of a fixed law, and the error probabilities add.
* **The middle layer.** The notes cite the multivariate covering lemma of Lecture 9 and a
  conditional
  version. We prove the conditional version directly from `sum_mutualCovering_le`, since `(xⁿ, uⁿ)`
  is fixed and the second moment bound holds for any relation between two independent families.
* **The codebook of `X̂₀ⁿ`.** The notes draw this codebook for typical pairs `(x̂₁ⁿ, x̂₂ⁿ)` only. We
  draw
  one for every index, and it is only used for typical ones.
* **The outer bound.** The notes say it "follows trivially". We use a uniform time index `Q` and
  `H(X_Q | Y_Q) ≥ H(X_Q | Q, M) ≥ (1/n) H(Xⁿ | M)`. The bound for the region has the exact `Dⱼ`, by
  compactness of the test channels (`isClosed_mdOuter`).
* **Theorem 3.** The region includes `R₂ ≥ 0`, which the notes leave implicit.
* **Special case 2.** The notes describe the rate–distortion function for `R₂ = 0`. We state it as
  the slice `R₂ = 0` of the closed region.
* **Proposition 1.** We require `D₀ ≥ D_min`, without which there is no test channel.
* **The Gaussian formulas** are in nats, with `R(x) = (1/2) log x`.

## Issues in the notes

The formula of page 14-15 was checked against the PDF, and the other items were read from its
extracted text.

* **Page 14-15, Theorem 2.** The formula for `Δ` needs the condition
  `1/D₀ + 1/P ≥ 1/D₁ + 1/D₂` in the low distortion case. Without it, the noise variance `N` of page
  14-20 is not positive (`ozarowN_pos_iff`), although the converse requires a noise `Zᵢ ∼ N(0, N)`.
  At `(P, D₀, D₁, D₂) = (1, 0.3, 0.31, 0.31)` the printed sum rate `R(P/D₀) + Δ` is about 2.94 bits,
  while sending the same description twice has the sum rate `2 R(P/D₀)`, about 1.74 bits, and
  independent noises have the sum rate `R(P/D₁) + R(P/D₂)`, about 1.69 bits, with the combined
  distortion `(1/D₁ + 1/D₂ - 1/P)⁻¹ ≈ 0.18 < D₀` (`ozarow_counterexample`, `mdNoise_indep_inv`).
    When
  the condition fails, the distortion `D₀` is not active, the sum rate is `R(P/D₁) + R(P/D₂)`, and
  the region should be evaluated with `D₀` replaced by `(1/D₁ + 1/D₂ - 1/P)⁻¹`. As the library has
    no
  Gaussian coding theorem, the formal statement is about the formulas, and these rate claims follow
  the coding scheme of the notes.
* Page 14-2: decoder 2 reproduces `X` with distortion `D₁`; it should be `D₂`.
* Page 14-5: `E(d₀(X̂₀, X))` has its arguments in the wrong order.
* Page 14-14: the multivariate covering lemma is said to be in Lecture Notes 7. It is in Lecture
  Notes 9, as page 14-11 says.
* Page 14-17: the inequality `(N₁ - N₀)(N₂ - N₀) ≥ (P + N₀)²` needs `D₁, D₂ < P`, since `Nⱼ` is not
  defined for `Dⱼ = P`, which the notes allow.
* Page 14-25: for a WGN(`P`) source, the backward channel has `X̂₁ ∼ N(0, P - D₁)` and
  `Z₀ ∼ N(0, D₀)`, not `N(0, 1 - D₁)` and `N(0, 1 - D₀)`.
* Page 14-28: `x̂₁(m₀, m₁₁)` and `x̂₂(m₀, m₂₂)` lack the superscript `n`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 14
-/

open Real

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

section Aliases

variable {Ω α υ β₀ β₁ β₂ : Type*} [Fintype Ω] [Fintype α] [Fintype υ] [Fintype β₀] [Fintype β₁]
  [Fintype β₂] {μ : Ω → ℝ} {X : Ω → α} {U : Ω → υ} {Y₀ : Ω → β₀} {Y₁ : Ω → β₁} {Y₂ : Ω → β₂}
  {d₀ : α → β₀ → ℝ} {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ} {P : α → ℝ}

/-- **Theorem 1 of Lecture 14, page 14-7: the El Gamal–Cover inner bound.** -/
theorem theorem_14_1 (hμ : IsPMF μ) (hd₀ : ∀ a b, 0 ≤ d₀ a b) (hd₁ : ∀ a b, 0 ≤ d₁ a b)
    (hd₂ : ∀ a b, 0 ≤ d₂ a b) (hQ : I[U : X ; μ] = 0) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h₁ : I[X : Y₁ | U ; μ] < R₁ * log 2) (h₂ : I[X : Y₂ | U ; μ] < R₂ * log 2)
    (h₁₂ : I[X : pair Y₀ (pair Y₁ Y₂) | U ; μ] + I[Y₁ : Y₂ | U ; μ] < (R₁ + R₂) * log 2)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂) :
    IsAchievableMD (dist μ X) d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ :=
  isAchievableMD_elGamalCover hμ hd₀ hd₁ hd₂ hQ h₁ h₂ h₁₂ hc₀ hc₁ hc₂

/-- **Theorem 3 of Lecture 14, page 14-23: successive refinement.** -/
theorem theorem_14_3 (hP : IsPMF P) (hd₀ : ∀ a b, 0 ≤ d₀ a b) (hd₁ : ∀ a b, 0 ≤ d₁ a b)
    {D₀ D₁ R₁ R₂ : ℝ} :
    (R₁, R₂) ∈ srRegion P d₀ d₁ D₀ D₁ ↔ 0 ≤ R₂ ∧ ∃ κ : α → β₀ × β₁ → ℝ, IsChannel κ ∧
      ∑ z, jointOf P κ z * d₀ z.1 z.2.1 ≤ D₀ ∧ ∑ z, jointOf P κ z * d₁ z.1 z.2.2 ≤ D₁ ∧
      I[Prod.fst : fun z : α × β₀ × β₁ => z.2.2 ; jointOf P κ] ≤ R₁ * log 2 ∧
      I[Prod.fst : Prod.snd ; jointOf P κ] ≤ (R₁ + R₂) * log 2 :=
  mem_srRegion_iff hP hd₀ hd₁

/-- **Theorem 4 of Lecture 14, page 14-27: the Zhang–Berger inner bound.** -/
theorem theorem_14_4 (hμ : IsPMF μ) (hd₀ : ∀ a b, 0 ≤ d₀ a b) (hd₁ : ∀ a b, 0 ≤ d₁ a b)
    (hd₂ : ∀ a b, 0 ≤ d₂ a b) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h₁ : I[X : pair Y₁ U ; μ] < R₁ * log 2) (h₂ : I[X : pair Y₂ U ; μ] < R₂ * log 2)
    (h₁₂ : I[X : pair Y₀ (pair Y₁ Y₂) | U ; μ] + 2 * I[U : X ; μ] + I[Y₁ : Y₂ | U ; μ] <
      (R₁ + R₂) * log 2)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂) :
    IsAchievableMD (dist μ X) d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ :=
  isAchievableMD_zhangBerger hμ hd₀ hd₁ hd₂ h₁ h₂ h₁₂ hc₀ hc₁ hc₂

/-- **Proposition 1 of Lecture 14, page 14-26.** -/
theorem proposition_14_1 [Nonempty β₀] (hP : IsPMF P) (hd : ∀ a b, 0 ≤ d₀ a b) :
    IsSuccessivelyRefinable P d₀ ↔ ∀ D₀ D₁, minDistortion P d₀ ≤ D₀ → D₀ ≤ D₁ →
      ∃ κ : α → β₀ × β₀ → ℝ, IsChannel κ ∧
        MarkovChain (jointOf P κ) Prod.fst (fun z => z.2.1) (fun z => z.2.2) ∧
        ∑ z, jointOf P κ z * d₀ z.1 z.2.1 ≤ D₀ ∧ ∑ z, jointOf P κ z * d₀ z.1 z.2.2 ≤ D₁ ∧
        I[Prod.fst : fun z : α × β₀ × β₀ => z.2.1 ; jointOf P κ] = infoRD P d₀ D₀ ∧
        I[Prod.fst : fun z : α × β₀ × β₀ => z.2.2 ; jointOf P κ] = infoRD P d₀ D₁ :=
  isSuccessivelyRefinable_iff hP hd

/-- **The simple outer bound of Lecture 14, page 14-6.** -/
theorem simple_outer_bound (hP : IsPMF P) {D₀ D₁ D₂ : ℝ} {R : ℝ × ℝ}
    (h : R ∈ mdRegion P d₀ d₁ d₂ D₀ D₁ D₂) : mdOuterAt P d₀ d₁ d₂ R.1 R.2 D₀ D₁ D₂ :=
  mdRegion_subset_mdOuter hP h

end Aliases

end InfoTheory.ElGamalKim
