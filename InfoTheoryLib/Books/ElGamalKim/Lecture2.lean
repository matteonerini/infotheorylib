/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.ChainRule
public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian
public import InfoTheoryLib.DifferentialEntropy.Partition
public import InfoTheoryLib.Entropy.Concavity
public import InfoTheoryLib.Entropy.Fano
public import InfoTheoryLib.Entropy.MrsGerber
public import InfoTheoryLib.MarkovChain.DataProcessing
public import InfoTheoryLib.MutualInformation.ChainRule
public import InfoTheoryLib.MutualInformation.Convexity
public import InfoTheoryLib.MutualInformation.CsiszarSum
public import InfoTheoryLib.Probability.WeakLaw
public import InfoTheoryLib.StochasticProcess.Basic
public import InfoTheoryLib.Typicality.JointTypicalityLemma

/-!
# El Gamal & Kim, Lecture 2: Entropy, Mutual Information, and Typicality

This file indexes the formalization of Lecture 2 of [elgamal2010] and contains the lecture's
worked example, with aliases named after its results. The lecture reviews entropy, differential
entropy and mutual information, and introduces the robust notion of typicality that the notes use
in all their achievability proofs. Much of the first three parts is also in Cover & Thomas, and the
index points to the same declarations as `Books.CoverThomas.Chapter2` and
`Books.CoverThomas.Chapter8`. The results of the lecture are named, not numbered; the last section
of this file gives aliases named after them, so that the index is checked by Lean.

## Conventions

* **Logarithms.** The notes use base `2`; the library's logarithms are natural, so entropies are
  in nats and the bounds `2^{-n(H ± δ(ε))}` read `e^{-n(H ± δ(ε))}`. Most statements of the
  lecture are homogeneous in the base of the logarithm. Fano's `1 + Pₑ log |𝒳|` is not, and is
  stated in bits in `fano_weak_bits`; `H⁻¹` is defined on `[0, log 2]` (`binEntropyInv`).
* **Random variables.** Discrete random variables are functions on a finite probability space
  `(Ω, μ)`, with `IsPMF μ`; the conditioning variable of `H(Y|X)` is also discrete. Continuous
  random variables are given by their densities.
* **Sequences** `xⁿ` are functions `Fin n → 𝒳`, and the pair `(xⁿ, yⁿ)` is the sequence of pairs
  `zipSeq xⁿ yⁿ`. Families of random variables are indexed from `0` (`prefixRV`).
* **Typicality.** `T_ε^(n)(X)` is `robustTypicalSet p n ε` for the pmf `p` of `X`, and
  `T_ε^(n)(X, Y)` is `robustTypicalSet q n ε` for the joint pmf `q`; `T_ε^(n)(Y|xⁿ)` is
  `condRobustTypicalSet q ε xⁿ`. The notes' `δ(ε)` are explicit, for example `δ(ε) = εH(X)`.
  The weakly typical set `A_ε^(n)(X)` of the appendix is the `typicalSet` of Cover & Thomas.
* **Triples.** The triple `(X, Y, Z)` is the pair `((X, Y), Z)`, with pmf `q : (𝒳 × 𝒴) × 𝒵 → ℝ`.
* **`≐`.** A statement `aₙ ≐ 2^{nb}` is formalized as a pair of explicit bounds.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Entropy
* `H(X)`, nonnegative and concave, and `H(X) ≤ log |𝒳|`: `entropy`, `entropyRV`
  (`Entropy.Basic`), `entropy_concaveOn` (`Entropy.Concavity`), `entropy_le_log_card`
  (`Entropy.Bounds`).
* The binary entropy function `H(p)`: Mathlib's `Real.binEntropy`, `entropy_bernoulli`
  (`Entropy.Basic`).
* Conditional entropy, `H(Y|X) ≤ H(Y)` with equality if `X` and `Y` are independent:
  `condEntropy`, `condEntropy_eq_expect` (`Entropy.Conditional`), `condEntropy_le_entropy`,
  `condEntropy_eq_entropy_iff` (`Entropy.Bounds`).
* Joint entropy, `H(X, Y) = H(X) + H(Y|X)`: `chain_rule` (`Entropy.Conditional`);
  `H(X, Y) ≤ H(X) + H(Y)`: `entropyRV_pair_le_add` (`Entropy.Bounds`), with equality iff
  `I(X; Y) = 0`, that is iff `X` and `Y` are independent (`mutualInfo_eq_zero_iff`,
  `MutualInformation.Basic`).
* The chain rule for entropy and `H(Xⁿ) ≤ ∑ᵢ H(Xᵢ)` with equality iff independence:
  `chain_rule_entropy` (`Entropy.ChainRule`), `entropy_prefixRV_le_sum`,
  `entropy_prefixRV_eq_sum_iff` (`Entropy.Bounds`).
* The equality case of `H(g(X)) ≤ H(X)`, when `g` is one-to-one on the support of `X`:
  `entropyRV_comp_eq_iff` (`Entropy.Fano`).
* The concavity of `h(X)` in the density: `integrable_negMulLog_mix`, `diffEntropy_mix_ge`
  (`DifferentialEntropy.Basic`).
* `H(g(X)) ≤ H(X)`, with equality if `g` is one-to-one: `entropyRV_comp_le`
  (`Entropy.Conditional`), `entropyRV_comp_injective` (`Entropy.Basic`).
* Fano's inequality, `H(X|Y) ≤ H(Pₑ) + Pₑ log |𝒳| ≤ 1 + Pₑ log |𝒳|`: `fano_of_eq`, `fano_weak`
  (`Entropy.Fano`).
* Mrs. Gerber's lemma: `binConv`, `binEntropyInv` (`Entropy.MrsGerber`). The notes' scalar form
  `H⁻¹(H(Y|U)) ≥ H⁻¹(H(X|U)) ∗ p`: `binConv_binEntropyInv_le`; the vector form
  `H⁻¹(H(Yⁿ|U)/n) ≥ H⁻¹(H(Xⁿ|U)/n) ∗ p`: `binConv_binEntropyInv_le_prefixRV`. Both need
  `p ≤ 1/2` (see below). The equivalent forms `H(Y|U) ≥ H(H⁻¹(H(X|U)) ∗ p)`, valid for every `p`:
  `mrsGerber_le_condEntropy_xor`, `mrsGerber_le_condEntropy_xor_prefixRV`. The convexity of
  `H(H⁻¹(u) ∗ p)` in `u`: `mrsGerber_convexOn`.
* The entropy rate of a stationary process, as both limits: `StochasticProcess.entropyRate`,
  `StochasticProcess.IsStationary.hasEntropyRate`,
  `StochasticProcess.IsStationary.hasCondEntropyRate` (`StochasticProcess.Basic`).

### Differential entropy
* `h(X)`: `diffEntropy` (`DifferentialEntropy.Basic`); translation and scaling:
  `diffEntropy_comp_sub`, `diffEntropy_scale`.
* Conditional differential entropy and `h(Y|X) ≤ h(Y)`: `condDiffEntropy`, `condDiffEntropy_le`
  (`DifferentialEntropy.Joint`).
* `h(X) = ½ log(2πeσ²)` for `X ∼ N(μ, σ²)`: `diffEntropy_gaussianPDFReal`
  (`DifferentialEntropy.Gaussian`).
* Maximum differential entropy under an average power constraint, and
  `h(X) ≤ ½ log(2πe Var(X))`: `diffEntropy_le_of_integral_mul_sq`,
  `diffEntropy_eq_of_integral_mul_sq_iff` (`DifferentialEntropy.Gaussian`), with `m = 0` and
  `m = E(X)`.
* The chain rule `h(Xⁿ) = ∑ᵢ h(Xᵢ|Xⁱ⁻¹) ≤ ∑ᵢ h(Xᵢ)`: `diffEntropy_eq_sum_condDiffEntropyLast`,
  `diffEntropy_le_sum_coordMarginal` (`DifferentialEntropy.ChainRule`).
* Translation and scaling of random vectors, `h(AXⁿ) = h(Xⁿ) + log |det A|`:
  `diffEntropy_linearEquiv` (`DifferentialEntropy.Basic`).
* `h(Xⁿ) = ½ log((2πe)ⁿ|K|)` for `Xⁿ ∼ N(μ, K)`: `mvGaussianPDF`, `diffEntropy_mvGaussianPDF`
  (`DifferentialEntropy.MultivariateGaussian`).
* The maximum differential entropy lemma, unconditional form
  `h(Xⁿ) ≤ ½ log((2πe)ⁿ|K_X|) ≤ ½ log((2πe)ⁿ|E(XXᵀ)|)`: `diffEntropy_le_of_covariance`,
  `diffEntropy_eq_of_covariance_iff`, the second inequality being the case `m = 0`; the relaxed
  bound `h(Xⁿ) ≤ (n/2) log(2πe (1/n) ∑ᵢ E(Xᵢ²))`: `diffEntropy_le_of_covariance_trace`
  (`DifferentialEntropy.MultivariateGaussian`).

### Mutual information
* `I(X; Y)` and its expressions: `mutualInfo`, `mutualInfo_eq_sum`,
  `mutualInfo_eq_entropy_sub_condEntropy`, `mutualInfo_eq_add_sub`; `I(X; Y) ≥ 0`:
  `mutualInfo_nonneg` (`MutualInformation.Basic`).
* Concavity in `p(x)` and convexity in `p(y|x)`: `mutualInfoOf_concave_input`,
  `mutualInfoOf_convex_channel` (`MutualInformation.Convexity`).
* For densities: `mutualInfoPDF`, `mutualInfoPDF_eq_sub_condDiffEntropy`,
  `mutualInfoPDF_eq_add_sub` (`DifferentialEntropy.Joint`).
* The supremum over finite quantizations: `quantMutualInfo`, `mutualInfoSup`,
  `quantMutualInfo_le_of_refine`, and its consistency for discrete random variables
  `mutualInfoSup_eq_of_finite` (`DifferentialEntropy.Partition`).
* Conditional mutual information, `I(X; Y|Z) = H(X|Z) - H(X|Y, Z)`: `condMutualInfo`,
  `condMutualInfo_eq` (`MutualInformation.Conditional`).
* The two special cases: `p(x, y, z) = p(x)p(z)p(y|x, z)` gives `I(X; Y|Z) ≥ I(X; Y)`:
  `mutualInfo_le_condMutualInfo_of_indep`; `Z → X → Y` gives `I(X; Y|Z) ≤ I(X; Y)`:
  `condMutualInfo_le_of_markovChain_left` (`MarkovChain.DataProcessing`).
* The chain rule: `chain_rule_mutualInfo` (`MutualInformation.ChainRule`).
* The data processing inequality `I(X; Z) ≤ I(Y; Z)` for `X → Y → Z`: `data_processing'`
  (`MarkovChain.DataProcessing`).
* The Csiszár sum identity: `suffixRV`, `csiszar_sum'`, and with an extra conditioning variable
  `csiszar_sum` (`MutualInformation.CsiszarSum`).

### Typical sequences
* The empirical pmf (type) `π(x|xⁿ)`: `typeOf` (`Statistics.Types`).
* `π(x|Xⁿ) → p(x)` in probability: the law of large numbers `weak_law` (`Probability.WeakLaw`),
  and `tendsto_prob_robustTypicalSet` (`Typicality.Basic`).
* `T_ε^(n)(X)`: `robustTypicalSet`, `mem_robustTypicalSet` (`Typicality.Basic`).
* The typical average lemma: `card_mul_le_sum_of_mem_robustTypicalSet`,
  `sum_le_card_mul_of_mem_robustTypicalSet`.
* Property 1: `le_iidPMF_of_mem_robustTypicalSet`, `iidPMF_le_of_mem_robustTypicalSet`;
  property 2: `card_robustTypicalSet_le`; property 3: `tendsto_prob_robustTypicalSet`;
  property 4: `eventually_card_robustTypicalSet_ge`.

### Jointly typical sequences
* The joint type and `T_ε^(n)(X, Y) = T_ε^(n)((X, Y))`: `typeOf (zipSeq xⁿ yⁿ)`,
  `robustTypicalSet q`.
* Properties of jointly typical sequences: 1. `fst_mem_robustTypicalSet`,
  `snd_mem_robustTypicalSet` (`Typicality.Conditional`), and in general
  `comp_mem_robustTypicalSet` (`Typicality.Basic`);
  2. property 1 of typical sequences for `q`; 3. the same for the marginals, by 1;
  4. `le_channelExt_condPMF_of_mem`, `channelExt_condPMF_le_of_mem` (`Typicality.Conditional`),
  and for `p(xⁿ|yⁿ)` the same applied to the swapped pmf, `zipSeq_swap_mem_robustTypicalSet`.
* `|T_ε^(n)(X, Y)| ≐ 2^{nH(X,Y)}`: properties 2 and 4 of typical sequences for `q`.
* `T_ε^(n)(Y|xⁿ)` and `|T_ε^(n)(Y|xⁿ)| ≤ 2^{n(H(Y|X)+δ(ε))}`: `condRobustTypicalSet`,
  `card_condRobustTypicalSet_le` (`Typicality.Conditional`).
* `Y = g(X)`: `mem_condRobustTypicalSet_comp_iff`.
* The conditional typicality lemma: `tendsto_prob_condRobustTypicalSet`, in the uniform form
  `eventually_prob_condRobustTypicalSet_ge` and with the explicit rate `1 - K/n`
  `one_sub_div_le_prob_condRobustTypicalSet`. We use Chebyshev's inequality for sums of
  independent random variables, `sum_prod_mul_sq_sum_le`, in place of the law of large numbers.
* Its consequence `|T_ε^(n)(Y|xⁿ)| ≥ (1 - ε) 2^{n(H(Y|X)-δ(ε))}` for `xⁿ ∈ T_{ε'}^(n)(X)`:
  `eventually_card_condRobustTypicalSet_ge`.
* Joint typicality for random triples: properties 1–4 are those of pairs for `((X, Y), Z)`, with
  `comp_mem_robustTypicalSet` (`Typicality.Basic`) for the subtuples and
  `le_prod_condDist_of_mem`, `prod_condDist_le_of_mem` for `p(xⁿ, yⁿ|zⁿ)`
  (`Typicality.JointTypicalityLemma`).
* The Markov chain `X → Y → Z`: `p(z|x, y) = p(z|y)`, `condPMF_eq_condDist_of_markovChain`, and
  `P{(xⁿ, yⁿ, Zⁿ) ∈ T_ε^(n)(X, Y, Z)} → 1` for `(xⁿ, yⁿ) ∈ T_{ε'}^(n)(X, Y)`, uniformly:
  `eventually_prob_condRobustTypicalSet_of_markovChain`.
* The joint typicality lemma: part 1(a) `prob_condRobustTypicalSet_condDist_le` (for every
  `(xⁿ, yⁿ)`); part 1(b) `eventually_prob_condRobustTypicalSet_condDist_ge`, and in the form
  `2^{-n(I(Y;Z|X)+δ(ε))}` `eventually_exp_le_prob_condRobustTypicalSet_condDist`, both for
  `(xⁿ, yⁿ) ∈ T_{ε'}^(n)` with `ε' < ε` (see below); part 2
  `sum_mul_prob_condRobustTypicalSet_condDist_le`.

### Multivariate typical sequences
* `T_ε^(n)(X₁, …, X_k) = T_ε^(n)((X₁, …, X_k))`: `robustTypicalSet` for the pmf of the tuple;
  property 1, `xⁿ(𝒥) ∈ T_ε^(n)(X(𝒥))`: `comp_mem_robustTypicalSet`; properties 2 and 3 are those
  of pairs for `(X(𝒥), X(𝒥'))`.

### Appendix: weak typicality
* `A_ε^(n)(X)`: `typicalSet` (`AEP.TypicalSet`); properties 1–3: `tendsto_prob_typicalSet`,
  `card_typicalSet_le`, `eventually_card_typicalSet_gt`.
* `T_ε^(n) ⊆ A_δ^(n)` for `δ = εH(X)`: `robustTypicalSet_subset_typicalSet` (`Typicality.Basic`).
* Every binary sequence is weakly typical for `Bern(1/2)`, but not every one is typical:
  `typicalSet_uniform_bool`, `const_not_mem_robustTypicalSet` (here).

## Not formalized

* Conditioning on a general random variable `X ∼ F(x)`: conditioning variables are discrete.
* The maximum differential entropy lemma with the
  conditional covariance `K_{X|Y}` of the MMSE estimate; the differential entropy rate.
* The entropy power inequality (scalar, vector and conditional), as in Cover & Thomas.
* Mutual information between a discrete and a continuous random variable, and the limit of
  `I([X]ⱼ; [Y]ₖ)` along refining quantizations; the monotonicity of `I([X]ⱼ; [Y]ₖ)` is
  formalized.
* The "stronger statement" `|T_ε^(n)(Y|xⁿ)| ≥ 2^{n(H(Y|X)-δ'(ε))}` for every `xⁿ ∈ T_ε^(n)(X)`,
  and the Appendix proving it with Stirling's approximation. As stated it is false:
  `T_ε^(n)(Y|xⁿ)` can be empty. Let `X ∼ Bern(1/2)`, `Y|{X = 1} ∼ Bern(1/√2)`, `ε = 1/2`, and
  `4 ∣ n`; the sequence `xⁿ` with `π(1|xⁿ) = 3/4` is in `T_ε^(n)(X)`. A jointly typical `yⁿ`
  needs `nπ(1, y|xⁿ, yⁿ) ≤ (1 + ε) n p(1, y) = (3n/4) p(y|1)` for both `y`, and these sum to
  `nπ(1|xⁿ) = 3n/4`, so equality holds, which is impossible as `(3n/4)/√2` is irrational. The
  appendix assumes some `(xⁿ, yⁿ) ∈ T_ε^(n)(X, Y)`. The lemma holds for `xⁿ ∈ T_{ε'}^(n)(X)` with
  `ε' < ε`, as `eventually_card_condRobustTypicalSet_ge` above.
* The AEP for stationary ergodic processes (the Shannon–McMillan–Breiman theorem), as in Cover &
  Thomas.
* The figures ("useful pictures").

## Issues in the notes

* **Mrs. Gerber's lemma.** In the form `H⁻¹(H(Y|U)) ≥ H⁻¹(H(X|U)) ∗ p`, the lemma needs
  `p ≤ 1/2`: for `p = 1` and a constant `X`, `Y` is constant, the left side is `0` and the right
  side `0 ∗ 1 = 1`. The form `H(Y|U) ≥ H(H⁻¹(H(X|U)) ∗ p)` holds for every `p`.
* **Joint typicality lemma, part 1(b).** For `(xⁿ, yⁿ)` only in `T_ε^(n)(X, Y)`, the set
  `T_ε^(n)(Z|xⁿ, yⁿ)` can be empty, as in the example above, and the lower bound fails. It holds
  for `(xⁿ, yⁿ) ∈ T_{ε'}^(n)(X, Y)` with `ε' < ε`, as in the conditional typicality lemma.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Appendix: weak typicality -/

/-- **Appendix (Lecture 2).** Every binary sequence is weakly typical with respect to the
`Bern(1/2)` pmf: `A_ε^(n)(X) = {0, 1}ⁿ` for every `ε ≥ 0`. -/
theorem typicalSet_uniform_bool (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    typicalSet (uniformPMF Bool) n ε = univ := by
  have hH : entropy (uniformPMF Bool) = log 2 := by
    rw [entropy_uniformPMF, Fintype.card_bool, Nat.cast_ofNat]
  have hp : ∀ x : Fin n → Bool, iidPMF (uniformPMF Bool) n x = exp (-(n * log 2)) := fun x => by
    rw [exp_neg, exp_natCast_mul, exp_log two_pos]
    simp [iidPMF, uniformPMF]
  ext x
  simp only [typicalSet, mem_filter, mem_univ, true_and, iff_true, hp, hH, exp_le_exp]
  have : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
  constructor <;> nlinarith

/-- **Appendix (Lecture 2).** A constant binary sequence is not typical with respect to the
`Bern(1/2)` pmf for `ε < 1`: robust typicality is stronger than weak typicality. -/
theorem const_not_mem_robustTypicalSet (n : ℕ) {ε : ℝ} (hε : ε < 1) :
    (fun _ => true : Fin n → Bool) ∉ robustTypicalSet (uniformPMF Bool) n ε := by
  intro h
  have := mem_robustTypicalSet.1 h false
  have h0 : typeOf (fun _ => true : Fin n → Bool) false = 0 := by
    simp [typeOf, symbolCount]
  rw [h0] at this
  simp only [uniformPMF, Fintype.card_bool, Nat.cast_ofNat, zero_sub, abs_neg] at this
  rw [abs_of_pos (by norm_num)] at this
  linarith

/-! ## Index of named results -/

/-- **Fano's inequality (Lecture 2).** `H(X|Y) ≤ H(Pₑ) + Pₑ log |𝒳|` for `Pₑ = P{X ≠ Y}`. -/
alias fano_inequality := fano_of_eq

/-- **Mrs. Gerber's lemma (Lecture 2)**, scalar form `H⁻¹(H(Y|U)) ≥ H⁻¹(H(X|U)) ∗ p`. -/
alias mrs_gerber_lemma := binConv_binEntropyInv_le

/-- **Mrs. Gerber's lemma (Lecture 2)**, vector form. -/
alias mrs_gerber_lemma_vector := binConv_binEntropyInv_le_prefixRV

/-- **Maximum differential entropy lemma (Lecture 2)**, unconditional form. -/
alias max_diff_entropy_lemma := diffEntropy_le_of_covariance

/-- **Chain rule for mutual information (Lecture 2).** -/
alias chain_rule_mutual_information := chain_rule_mutualInfo

/-- **Data processing inequality (Lecture 2).** `I(X; Z) ≤ I(Y; Z)` for `X → Y → Z`. -/
alias data_processing_inequality := data_processing'

/-- **Csiszár sum identity (Lecture 2).** -/
alias csiszar_sum_identity := csiszar_sum'

/-- **Typical average lemma (Lecture 2)**, lower bound. -/
alias typical_average_lemma_lower := card_mul_le_sum_of_mem_robustTypicalSet

/-- **Typical average lemma (Lecture 2)**, upper bound. -/
alias typical_average_lemma_upper := sum_le_card_mul_of_mem_robustTypicalSet

/-- **Conditional typicality lemma (Lecture 2).** -/
alias conditional_typicality_lemma := tendsto_prob_condRobustTypicalSet

/-- **Joint typicality for a Markov chain `X → Y → Z` (Lecture 2).** -/
alias markov_conditional_typicality := eventually_prob_condRobustTypicalSet_of_markovChain

/-- **Joint typicality lemma (Lecture 2)**, part 1(a). -/
alias joint_typicality_lemma_1a := prob_condRobustTypicalSet_condDist_le

/-- **Joint typicality lemma (Lecture 2)**, part 1(b). -/
alias joint_typicality_lemma_1b := eventually_prob_condRobustTypicalSet_condDist_ge

/-- **Joint typicality lemma (Lecture 2)**, part 2. -/
alias joint_typicality_lemma_2 := sum_mul_prob_condRobustTypicalSet_condDist_le

end InfoTheory.ElGamalKim
