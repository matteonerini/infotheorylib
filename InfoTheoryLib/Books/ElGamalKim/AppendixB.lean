/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.FunctionalRepresentation
public import InfoTheoryLib.Probability.GaussianDensity
public import InfoTheoryLib.Probability.Jensen
public import InfoTheoryLib.Probability.ProbabilityBounds
public import InfoTheoryLib.Probability.WeakLaw

/-!
# El Gamal & Kim, Appendix B: Probability and Estimation

This file indexes the formalization of Appendix B of [elgamal2010]: probability bounds and limits,
the functional representation lemma, mean squared error estimation and Gaussian random vectors.

## Conventions

* **Random variables.** The functional representation lemma and the Chernoff bound are stated with
  finite pmfs, as in the rest of the library. The other results are stated on a general probability
  space, for measurable random variables with finite second moments (`MemLp X 2 μ`).
* **Conditional pmfs.** The random variable `W` of the functional representation lemma is an
  extension of `p(x, y, z)` by a channel `κ(w | y, z)`, and the law of `((X, Y, Z), W)` is
  `jointOf p fun o => κ o.2`. The Markov chain is the vanishing of a conditional mutual information.
* **Estimates.** A linear estimate `aᵀ Y + b` is the pair `(a, b)`, and `linMSE μ X Y a b` is its
  mean squared error. The matrices `K_Y`, `K_{X Y}` are `covMatrix μ Y`, `covVec μ X Y`.
* **Gaussian vectors.** A Gaussian random vector is Mathlib's `HasGaussianLaw`. The degenerate
  Gaussian is allowed, as in the notes. Conditioning on `X₁ = x` is Mathlib's `condDistrib`, up to a
  null set of `x`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Probability bounds and limits (pages B-2 and B-3)
* **Union of events bound:** `prob_biUnion_le` (`Probability.Event`), for a finite pmf, and
  Mathlib's `measure_biUnion_finset_le`.
* **Jensen's inequality:** `jensen` (`Probability.Jensen`), for a finite pmf, and Mathlib's
  `ConvexOn.map_integral_le`.
* **Chebyshev lemma:** `chebyshev_lemma`, `chebyshev_lemma_lower`, `chebyshev_lemma_upper`
  (`Probability.ProbabilityBounds`), for a positive mean. It fails for a negative mean:
  `printed_chebyshev_false`.
* **Chernoff bound:** `chernoff_bound`, for `0 < δ ≤ 2`. It fails for large `δ`:
  `printed_chernoff_false`.
* **Weak law of large numbers:** `weak_law` (`Probability.WeakLaw`), for a finite pmf, and
  `weak_law_real`, on a general probability space.
* **Dominated convergence theorem:** Mathlib's `tendsto_integral_of_dominated_convergence`.

### Functional representation lemma (pages B-4 to B-6; `Probability.FunctionalRepresentation`)
* **The lemma:** `functional_representation`.
* A conditional pmf as a function of the input and an independent variable:
  `exists_channel_representation`.
* The example, for the doubly symmetric binary source: here `dsbs_representation`.
* The steps of the proof: `condCdf`, `quantileOf`, `quantileOf_le_iff`, `cdfThresholds`,
  `card_cdfThresholds_le`, `condCdf_quantile_law`.

### Mean squared error estimation (pages B-7 to B-10; `Probability.MMSE`)
* The decomposition of the mean squared error: `integral_sq_sub_eq`.
* The MMSE estimate is the conditional expectation: `integral_sq_condExp_le`.
* Its mean squared error: `integral_sq_sub_condExp_eq`, `integral_condVar_eq`.
* `Var X = E Var(X | Y) + Var E(X | Y)`: `integral_condVar_add_variance_condExp'`.
* **Orthogonality principle:** `linMSE_le_of_orthogonal`, `orthogonal_of_isMin`, with
  `linMSE_eq` for the mean squared error of any linear estimate, for any means. The form
  `aᵀ K_Y = K_{X Y}`: `cov_linErr_eq_zero_iff`.
* The linear MMSE estimate and its mean squared error for a nonsingular `K_Y`: `linMSE_inv`.
* `E Var(X | Y) ≤ K_X - K_{X Y} K_Y⁻¹ K_{Y X}`: `integral_condVar_le_linMSE`.
* **Matrix inversion lemma:** `matrix_inversion_lemma`.
* The additive noise example: `covMatrix_noise_inv`, `linMSE_noise`.

### Gaussian random vectors (pages B-11 and B-12)
* The definition: `hasGaussianLaw_iff_forall_linear` (`Probability.GaussianVector`).
* The joint pdf: `mvGaussianPDF` (`DifferentialEntropy.MultivariateGaussian`), and `mvGaussianLaw`,
  `map_eq_mvGaussianLaw`, `isGaussian_mvGaussianLaw`, `integral_mvGaussianLaw`,
  `covariance_mvGaussianLaw` (`Probability.GaussianDensity`).
* A Gaussian law is determined by its mean and covariance matrix: `map_eq_of_mean_of_cov`.
* **Property 1:** here `gaussian_iIndepFun_of_uncorrelated`, from Mathlib's
  `HasGaussianLaw.iIndepFun_of_covariance_eq_zero`.
* **Property 2:** `hasGaussianLaw_mulVec`, `integral_mulVec`, `covariance_mulVec`.
* **Property 3:** `hasGaussianLaw_marginal`.
* **Property 4:** `condDistrib_gaussian`, `isGaussian_shiftKernel`, `integral_shiftKernel`,
  `covariance_shiftKernel`.
* **The remark on page B-12:** `condExp_gaussian`, `indepFun_residual`.

## Differences from the notes

* **Functional representation lemma.** The proof follows the notes, with `W` indexed by the gaps
  between the sorted values of the conditional cdfs, and the cardinality bound is the one of the
  notes. Only `Y` and `Z` matter for `g`, so the lemma is proved for a channel first, and `X` is
  generated from `(Y, Z)` afterward, as in the notes. The cardinality is a bound on `m`, in
  `Fin m`, and `Z = g(Y, W)` holds on the support of the extended law.
* **Weak law.** `weak_law_real` assumes only that the variables are pairwise independent.
* **Orthogonality principle.** We prove it for any means with a covariance form, instead of first
  for zero means, and we prove the two directions separately. The criterion
  `linMSE_le_of_orthogonal` does not need `K_Y` to be nonsingular.
* **Example.** `linMSE_noise` also allows `P = 0`, which the matrix inversion lemma with
  `K₂₂ = -1 / P` does not. The inverse is checked directly in `covMatrix_noise_inv`.
* **Property 4.** The conditional law is `shiftKernel L ν`, the law of `L x + R`, where `R` is the
  residual `X₂ - L X₁` with its mean. Its mean and covariance are those of the notes. We assume that
  `K₁₁` is nonsingular, and that the coordinates are measurable, not only almost everywhere
  measurable.

## Not formalized

Nothing in the appendix is left out. The earlier lectures do not use the functional representation
lemma yet: `Lecture7` uses `prodPMF` in its place, and the inclusion on page 14-31 that needs it is
still on the list of `Lecture14`. The version for causally conditional laws, which Theorem 7 of
Lecture 18 and `Network.DirectedInfo` would need, is a different statement and is not proved.

## Issues in the notes

* **Page B-2, Chebyshev lemma.** It is stated for any finite mean, and fails for a negative one. For
  `X ≡ -1` the event `|X - E X| ≥ δ E X` has probability one, while the bound is zero:
  `printed_chebyshev_false`. The lemma holds for a positive mean.
* **Page B-3, Chernoff bound.** It is stated for all `δ > 0`, and fails for large `δ`. For `n = 1`,
  `p = 1/20` and `δ = 19` the event has probability `1/20`, and the bound is `e^{-361/80}`:
  `printed_chernoff_false`. We prove it for `0 < δ ≤ 2`. The uses on pages 13-48, 20-38 and 24-36
  have small `δ`.
* **Page B-3, dominated convergence.** The statement omits that the pointwise limit of `gₙ` has to
  exist, and its measurability.
* **Page B-4.** "DBSP(p)" should be "DSBS(p)", the doubly symmetric binary source.
* **Page B-5.** `P = {0, p, 1 - p, 0}` should end with `1`.
* **Page B-6.** `P` is defined as the set of values of `F(z | y)`, which need not contain `0`, so
  `|W| = |P| - 1` should read `|W| = |P|` with this definition. The example of page B-5 includes `0`
  in `P`. The cardinality bound holds in both readings.
* **Page B-9, matrix inversion lemma.** The invertibility of `K₁₁`, `K₂₂` and of
  `K₂₂ - K₂₁ K₁₁⁻¹ K₁₂` is implicit, and these do not follow from that of
  `K₁₁ - K₁₂ K₂₂⁻¹ K₂₁`.
* **Page B-11, Property 1.** The check by substitution into the joint pdf covers only `K ≻ 0`, as
  uncorrelated coordinates may be degenerate. Mathlib's proof with characteristic functions covers
  every case.
* **Page B-12.** Property 4 needs a nonsingular `K₁₁`. In the remark, "the observation `Ŷ`" should
  be `Y`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  B
-/

open MeasureTheory ProbabilityTheory Finset

@[expose] public noncomputable section

namespace InfoTheory

namespace ElGamalKim

/-! ### The example of the functional representation lemma -/

/-- The conditional pmf of the doubly symmetric binary source `DSBS(p)`:
`p(0 | 0) = p(1 | 1) = 1 - p` and `p(0 | 1) = p(1 | 0) = p`. -/
def dsbsChannel (p : ℝ) (y z : Bool) : ℝ := if y = z then 1 - p else p

/-- **Page B-5 of [elgamal2010].** The pmf of `W`: `(p, 1 - 2p, p)`. -/
def dsbsW (p : ℝ) : Fin 3 → ℝ := ![p, 1 - 2 * p, p]

/-- **Page B-5 of [elgamal2010].** `g(0, ·) = (0, 0, 1)` and `g(1, ·) = (0, 1, 1)`. -/
def dsbsG (y : Bool) : Fin 3 → Bool := if y then ![false, true, true] else ![false, false, true]

/-- **The example of pages B-4 and B-5 of [elgamal2010].** For `DSBS(p)` with `p < 1/2`, the ternary
`W` has a pmf, and `g(y, W)` has the conditional law of `Z` given `Y = y`. -/
theorem dsbs_representation {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1 / 2) :
    IsPMF (dsbsW p) ∧
      ∀ y z, ∑ w, (if dsbsG y w = z then dsbsW p w else 0) = dsbsChannel p y z := by
  refine ⟨⟨fun w => ?_, ?_⟩, fun y z => ?_⟩
  · fin_cases w <;> simp [dsbsW] <;> linarith
  · simp only [dsbsW, Fin.sum_univ_three]
    simp
    ring
  · cases y <;> cases z <;> simp [dsbsG, dsbsW, dsbsChannel, Fin.sum_univ_three] <;> ring

/-! ### Property 1 of Gaussian random vectors -/

/-- **Property 1 on page B-11 of [elgamal2010].** Uncorrelated coordinates of a Gaussian random
vector are independent. -/
theorem gaussian_iIndepFun_of_uncorrelated {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [Finite ι] {X : ι → Ω → ℝ} (hX : HasGaussianLaw (fun ω i => X i ω) μ)
    (h : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) : iIndepFun X μ :=
  hX.iIndepFun_of_covariance_eq_zero h

end ElGamalKim

end InfoTheory
