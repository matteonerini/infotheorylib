/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.MrsGerber
public import InfoTheoryLib.GaussianChannel.AWGN
public import InfoTheoryLib.RateDistortion.Gaussian
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# El Gamal & Kim, Lecture 1: Introduction

This file indexes the formalization of Lecture 1 of [elgamal2010]. The lecture is an informal
introduction: it states the max-flow min-cut theorem and Shannon's four point-to-point theorems,
outlines the lecture notes, and fixes the notation. Shannon's theorems are formalized in
`Books.ElGamalKim.Lecture3` and the max-flow min-cut theorem in `Books.ElGamalKim.Lecture16`; this
file gives the notation that the library defines, with the
definitions of the notes that are not in the library elsewhere: the `DSBS(p)` pmf and the
relation between `C(x)` and `R(x)`. The lecture has no numbered results, so there are no aliases.

## Conventions

* **Logarithms.** The notes use base `2`. The library's logarithms are natural; a quantity in
  bits is the quantity in nats divided by `log 2`.
* **Bits.** Binary random variables are `Bool`s, and the modulo-2 sum `⊕` is `xor`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Point-to-point information theory
* The channel coding theorem `C = max_{p(x)} I(X; Y)`: `opCapacityAvg_eq`
  (`ChannelCoding.AverageError`), Lecture 3.
* The lossless source coding theorem `R* = H(X)`: `optLosslessRate_eq`
  (`SourceCoding.LosslessRate`), Lecture 3.
* The lossy source coding theorem `R(D) = min_{p(x̂|x) : E d(X, X̂) ≤ D} I(X; X̂)`:
  `rateDistortionBits_eq` (`RateDistortion.BitRate`), Lecture 3.
* The separation theorem: `IsAchievableSCDistortion.infoRD_le_capacity`,
  `isAchievableSCDistortion_of_infoRD_lt` (`RateDistortion.SourceChannel`), for one source symbol
  per channel use; Lecture 3.

### Notation
* `ᾱ = 1 - α` and `α ∗ β = αβ̄ + βᾱ`: `binConv` (`Entropy.MrsGerber`).
* `xⁿ ⊕ yⁿ`: `fun i => xor (x i) (y i)`.
* `xⁿ`, `Xⁿ`: `Fin n → 𝒳`, `prefixRV X n` (`Probability.RandomVector`); `X(𝒥)` for a subtuple:
  a function of the tuple, as in `comp_mem_robustTypicalSet` (`Typicality.Basic`).
* `[1 : 2^a)` and `[1 : 2^a]`: `Fin (2 ^ ⌊a⌋₊)` and `Fin (2 ^ ⌈a⌉₊)`, as in
  `IsAchievableLosslessRate` (`SourceCoding.LosslessRate`) and `IsAchievableRateAvg`
  (`ChannelCoding.AverageError`).
* `X ∼ p(x)`, `p(y|x)`, `X → Y → Z`, `E(g(X))`, `Var(X)`: `dist`, `condDist`
  (`Probability.FinitePMF`, `Probability.Conditional`), `MarkovChain` (`MarkovChain.Basic`),
  `expect` (`Probability.FinitePMF`), `variance` (`Probability.Variance`); the covariance matrix
  `K_X` is the hypothesis `hcov` of `diffEntropy_le_of_covariance`
  (`DifferentialEntropy.MultivariateGaussian`).
* `Bern(p)`: `bernoulliPMF` (`Statistics.Bernoulli`); `Unif`: `uniformPMF`
  (`Probability.FinitePMF`); `N(μ, σ²)`: Mathlib's `ProbabilityTheory.gaussianPDFReal`;
  `N(μ, K)`: `mvGaussianPDF`.
* A `Bern(p)` process: `iidPMF (bernoulliPMF p)` (`Probability.IID`); a `DSBS(p)` process:
  `iidPMF (dsbsPMF p)`, with `dsbsPMF` here.
* `C(x) = ½ log(1 + x)`: `gaussianCapacityFun` (`GaussianChannel.AWGN`);
  `R(x) = ½ log x` for `x ≥ 1` and `0` otherwise: `gaussianRateFun`
  (`RateDistortion.Gaussian`); `R(1 + x) = C(x)`: `gaussianRateFun_one_add` (here).
* The `ε–δ` notation and `aₙ ≐ 2^{nb}`: the library states explicit bounds, with explicit `δ(ε)`.
* Matrices and order notation: Mathlib's `Matrix`, `Matrix.det`, `Matrix.PosDef`,
  `Matrix.PosSemidef`, `Asymptotics.IsLittleO`, `Asymptotics.IsBigO`, `Asymptotics.IsTheta`.

## Not formalized

* The separation theorem for `k` source symbols per `n` channel uses with `k ≠ n`.
* The outline, the dependency graph and the informal discussion.
* `Binom(n, p)`, `Q(x)`, and the `WGN(P)`, `2-WGN(P, ρ)` and vector `WGN(K)` processes as
  definitions; the Gaussian channels of the library state them through their densities.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 1
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

variable {Ω : Type*} [Fintype Ω]

/-! ## The doubly symmetric binary source -/

/-- **Notation (Lecture 1).** The pmf of a `DSBS(p)` pair `(X, Y)`: `X ∼ Bern(1/2)` and
`Y = X ⊕ Z` with `Z ∼ Bern(p)` independent of `X`, so `p(x, y) = p/2` if `x ≠ y` and `(1 - p)/2`
if `x = y`. -/
def dsbsPMF (p : ℝ) (z : Bool × Bool) : ℝ := 1 / 2 * bernoulliPMF p (xor z.1 z.2)

lemma dsbsPMF_isPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsPMF (dsbsPMF p) := by
  refine ⟨fun z => mul_nonneg (by norm_num) ((bernoulliPMF_isPMF h0 h1).nonneg _), ?_⟩
  simp [dsbsPMF, Fintype.sum_prod_type, bernoulliPMF]
  ring

/-- **Notation (Lecture 1).** The `DSBS(p)` pmf is symmetric: equivalently, `Y ∼ Bern(1/2)` and
`X = Y ⊕ Z` with `Z ∼ Bern(p)` independent of `Y`. -/
lemma dsbsPMF_swap (p : ℝ) (z : Bool × Bool) : dsbsPMF p z.swap = dsbsPMF p z := by
  simp [dsbsPMF, Bool.xor_comm]

/-- **Notation (Lecture 1).** If `X ∼ Bern(1/2)` and `Z ∼ Bern(p)` are independent, then
`(X, X ⊕ Z)` is a `DSBS(p)` pair. -/
theorem dist_pair_xor_eq_dsbsPMF {μ : Ω → ℝ} (X Z : Ω → Bool) {p : ℝ}
    (hX : dist μ X = bernoulliPMF (1 / 2)) (hZ : dist μ Z = bernoulliPMF p)
    (hind : IndepRV μ X Z) : dist μ (pair X fun ω => xor (X ω) (Z ω)) = dsbsPMF p := by
  set f : Bool × Bool → Bool × Bool := fun z => (z.1, xor z.1 z.2)
  have hf : Function.Injective f := fun a b h => by
    rcases a with ⟨_ | _, _ | _⟩ <;> rcases b with ⟨_ | _, _ | _⟩ <;> simp_all [f]
  have hcomp : (pair X fun ω => xor (X ω) (Z ω)) = f ∘ pair X Z := rfl
  funext ⟨a, c⟩
  have hz : ((a, c) : Bool × Bool) = f (a, xor a c) := by simp [f]
  conv_lhs => rw [hcomp, hz, dist_comp_of_injective μ (pair X Z) hf, hind, hX, hZ]
  rcases a with _ | _ <;> rcases c with _ | _ <;> simp [dsbsPMF, bernoulliPMF] <;> norm_num

/-! ## The functions `C(x)` and `R(x)` -/

/-- **Notation (Lecture 1).** `R(1 + x) = C(x)` for `x ≥ 0`. -/
theorem gaussianRateFun_one_add {x : ℝ} (hx : 0 ≤ x) :
    gaussianRateFun (1 + x) = gaussianCapacityFun x := by
  rw [gaussianRateFun, ite_eq_left (by linarith), gaussianCapacityFun]

end InfoTheory.ElGamalKim
