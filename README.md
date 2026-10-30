# infotheorylib

[![Lean Action CI](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-API-blue)](https://matteonerini.github.io/infotheorylib/docs/)

A Lean 4 library of information theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

The goal is to formalize the core concepts and theorems of information theory, following
T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed., Wiley, 2006), and to
organize them by topic, in the spirit of Mathlib for mathematics and Physlib for physics.

## Status

| Chapter of Cover & Thomas (2nd ed.) | Status |
|---|---|
| 1. Introduction and Preview | Formalized: all definitions and examples, with pointers to the later chapters for the announced results |
| 2. Entropy, Relative Entropy, and Mutual Information | Formalized: all definitions, lemmas, theorems, corollaries, remarks and examples |
| 3. Asymptotic Equipartition Property | Formalized: all definitions, theorems, remarks and examples, except convergence with probability 1 |
| 4. Entropy Rates of a Stochastic Process | Formalized: all definitions, lemmas, theorems, remarks and examples, including the second law of thermodynamics and hidden Markov models (see the chapter file for the facts quoted from later chapters) |
| 5. Data Compression | Formalized: all definitions, lemmas, theorems, corollaries and examples, except the Morse code example and the optimality of `D`-ary Huffman codes |
| 6. Gambling and Data Compression | Formalized: all definitions, theorems and examples, except the ergodic growth (6.37), proved in Chapter 16, and the experimental estimates of the entropy of English |
| 7. Channel Capacity | Formalized: all definitions, lemmas, theorems and examples, including both halves of the channel coding theorem, feedback capacity and source–channel separation; see the chapter file for the omitted remarks |
| 8. Differential Entropy | Formalized: all definitions, theorems, corollaries and examples, including the AEP for densities, the multivariate normal and Hadamard's inequality; Theorem 8.3.1 is proved for continuous compactly supported densities (see the chapter file for what is omitted) |
| 9. Gaussian Channel | Formalized: the information capacity and Theorem 9.1.1 (achievability and converse), the sampling theorem, bandlimited, parallel and colored-noise channels with water-filling, and Theorems 9.6.2–9.6.3 on feedback; Theorem 9.6.1 is not formalized (see the chapter file for what is omitted) |
| 10. Rate Distortion Theory | Formalized: all definitions, lemmas and theorems except Lemma 10.6.2, including the rate distortion theorem (achievability and converse), the Bernoulli source, the information rate distortion functions of Gaussian and parallel Gaussian sources (reverse water-filling), source–channel separation with distortion, strong typicality, and the Blahut–Arimoto algorithm without its convergence (see the chapter file for what is omitted) |
| 11. Information Theory and Statistics | Formalized: the method of types, the law of large numbers for types, universal source coding, Sanov's theorem, the Pythagorean theorem and Pinsker's inequality, the conditional limit theorem, the Neyman–Pearson and Chernoff–Stein lemmas, Chernoff information, and the Cramér–Rao inequality for finite parametric families (see the chapter file for what is omitted) |
| 12. Maximum Entropy | Formalized: Theorem 12.1.1 for densities and pmfs with uniqueness, all the examples of Section 12.2 (uniform, exponential, normal, Gibbs, multivariate normal, partial covariance constraints), and Burg's theorem 12.6.1 for finite segments with the entropy rate `½ log 2πeσ²`, assuming a solution of the Yule–Walker equations (see the chapter file for what is omitted) |
| 13. Universal Source Coding | Formalized: minimax redundancy equals capacity (Theorem 13.1.1, without the minimax theorem), two-stage and Laplace mixture codes for binary sequences, the probability integral transform and arithmetic coding intervals, the LZ77 and LZ78 algorithms with LZ78 decodability, Elias codes for the integers, Kac's lemma and the recurrence time code, and the optimality of LZ78 as deterministic bounds uniform over Markov models; the ergodic theorem is not formalized (see the chapter file for what is omitted) |
| 14. Kolmogorov Complexity | Formalized: computers as partial recursive functions with prefix-free programs, a universal computer constructed from Mathlib's universal partial recursive function, the universality of `K`, the upper and lower bounds of Section 14.2 with computable programs, `K` and entropy for Bernoulli sources (in expectation and in probability), the complexity of integers, incompressible sequences, universal probability, `Ω` and universal gambling, the noncomputability of `K`, and the easy half of Theorem 14.11.1 (see the chapter file for what is omitted) |
| 15. Network Information Theory | Formalized: the Gaussian multi-user formulas (onion peeling, frequency and time division, the broadcast and relay formulas), conditional joint typicality, the capacity region of the multiple-access channel (random coding with three typical groupings, time sharing, Lemma 15.3.1, the converse via Fano's inequality, Theorems 15.3.1–15.3.5), the Slepian–Wolf theorem (random binning and the converse), and the definitions of broadcast channels with Theorem 15.6.1 and degradedness (see the chapter file for what is omitted) |
| 16. Information Theory and Portfolio Theory | Formalized: growth rates and log-optimal portfolios for finite markets with positive price relatives, the Kuhn–Tucker conditions, the costs of wrong beliefs and the value of side information, causal strategies in market processes (the chain rule for `W*`, the supermartingale `Sₙ/Sₙ*`, the growth rate of stationary markets), almost sure growth and asymptotic optimality, competitive optimality, and finite-horizon universal portfolios (Theorem 16.7.1 for any number of stocks); see the chapter file for what is omitted |
| 17. Inequalities in Information Theory | Formalized: the `L₁` bound on entropy, the `χ²` approximation of relative entropy and the monotonicity of `E D(p̂ₙ‖p)`, the binomial bounds of Lemma 17.5.1, Han's inequalities (Theorems 17.6.1–17.6.4) for submodular set functions and discrete entropies, the determinant inequalities of Section 17.9 (Koteljanskii, Szász, Theorems 17.9.4–17.9.5, the Toeplitz theorem, Minkowski) and Bergstrøm's theorems of Section 17.10; de Bruijn's identity, the entropy power inequality and the Brunn–Minkowski and Young inequalities of Sections 17.7–17.8 are not formalized (see the chapter file for what is omitted) |

The library contains no `sorry` and builds without warnings under Mathlib's linter set.

## Main results

A selection of the headline theorems; every numbered result of the book is listed, with its Lean
name, in the chapter files `Book/ChapterN.lean`. Browse them in the
[API documentation](https://matteonerini.github.io/infotheorylib/docs/).

| Result (Cover & Thomas) | Lean declaration | Module |
|---|---|---|
| Data processing inequality (2.8.1) | `data_processing` | `MarkovChain.DataProcessing` |
| Fano's inequality (2.10.1) | `fano_estimator` | `Entropy.Fano` |
| Asymptotic equipartition property (3.1.1) | `aep` | `AEP.Basic` |
| Entropy rate of stationary processes (4.2.1) | `StochasticProcess.IsStationary.hasEntropyRate` | `StochasticProcess.Basic` |
| Kraft–McMillan inequality (5.5.1) | `kraft_of_isUniquelyDecodableCode` | `SourceCoding.Kraft` |
| Source coding bounds `H ≤ L* < H + 1` (5.4.1) | `minExpectedLength_bounds` | `SourceCoding.OptimalLength` |
| Optimality of Huffman codes (5.8.1) | `huffmanCode_optimal` | `SourceCoding.Huffman` |
| Channel coding theorem (7.7.1) | `isAchievableRate_of_lt_capacity`, `IsAchievableRate.le_capacity` | `ChannelCoding` |
| Feedback does not increase capacity (7.12.1) | `fbCapacity_eq_capacity` | `ChannelCoding.Converse` |
| Source–channel separation (7.13.1) | `exists_sourceChannelCode`, `entropyRate_le_capacity` | `ChannelCoding.SourceChannel` |
| Capacity of the Gaussian channel (9.1.1) | `gaussianOpCapacity_eq` | `GaussianChannel.Achievability` |
| Rate distortion theorem (10.2.1) | `rateDistortion_eq_infoRD` | `RateDistortion.Theorem` |
| Sanov's theorem (11.4.1) | `prob_typeEvent_le_sanov`, `tendsto_log_prob_typeEvent` | `Statistics.LargeDeviations` |
| Pinsker's inequality (11.6.1) | `pinsker` | `RelativeEntropy.Pinsker` |
| Chernoff–Stein lemma (11.8.3) | `tendsto_log_steinBeta` | `Statistics.HypothesisTesting` |
| Chernoff information (11.9.1) | `tendsto_neg_log_bayesErr` | `Statistics.ChernoffInformation` |
| Maximum entropy distributions (12.1.1) | `diffEntropy_le_of_eq_exp` | `MaxEntropy.Basic` |
| Minimax redundancy equals capacity (13.1.1) | `isLeast_maxRedundancy` | `SourceCoding.Minimax` |
| Kolmogorov complexity and entropy (14.3.1) | `tendsto_expected_complexity_div` | `Kolmogorov.Entropy` |
| Capacity region of the multiple-access channel (15.3.1) | `macCapacityRegion_eq` | `Network.MACCapacity` |
| Slepian–Wolf theorem (15.4.1) | `swAchievableRegion_eq` | `Network.SlepianWolf` |
| Universal portfolios (16.7.1) | `minimax_universal` | `Investment.Universal` |
| Han's inequality (17.6.1) | `subsetAvg_succ_le` | `Inequalities.Han` |
| Minkowski's determinant inequality (17.9.7) | `det_rpow_add_det_rpow_le` | `Inequalities.Determinant` |

## Getting started

You need [elan](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib is pinned in `lakefile.toml`.

```sh
lake exe cache get   # download prebuilt Mathlib files
lake build           # build the library
```

### Using the library in your project

Add the library to the `lakefile.toml` of your project:

```toml
[[require]]
name = "infotheorylib"
git = "https://github.com/matteonerini/infotheorylib"
rev = "v4.36.0-rc2"
```

then run `lake update infotheorylib` and `lake exe cache get`. A Lake project can contain only one
version of Mathlib, so your project must use the same Lean toolchain (`v4.36.0-rc2`) and Mathlib
version as the release you depend on. Releases are tagged with the Lean version they support;
the available versions are listed on the
[releases page](https://github.com/matteonerini/infotheorylib/releases).
The library uses the module system, so it can be imported from both module and non-module files.

To use the library, import it and open the `InfoTheory` namespace, which also activates the
notation `H[X ; μ]`, `H[X | Y ; μ]`, `I[X : Y ; μ]` and `I[X : Y | Z ; μ]`:

```lean
import InfoTheoryLib

open InfoTheory

-- Conditioning reduces entropy (Theorem 2.6.5).
example {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (X : Ω → α) (Y : Ω → β) : H[X | Y ; μ] ≤ H[X ; μ] :=
  condEntropy_le_entropy hμ X Y

-- The same result, looked up by its number in Cover & Thomas.
#check @CoverThomas.theorem_2_6_5
```

## Layout

The library is organized by topic. Each file starts with a docstring listing its main
definitions and statements, and the book sections it covers.

```
InfoTheoryLib.lean                 root file, imports every module (generated by `lake exe mk_all`)
InfoTheoryLib/
  ForMathlib/          general facts not specific to information theory, to upstream to Mathlib
    Log.lean             logarithm and `negMulLog` lemmas, numerical bounds on log₂ 3 and log₂ 7
    Integral.lean        change of variables `∫ g(Ax) dx = |det A|⁻¹ ∫ g` for linear maps
    WeakLaw.lean         the weak law of large numbers for product measures
    MatrixDet.lean       determinant inequalities for positive semidefinite matrices
    MatrixBlock.lean     block diagonal positive definite matrices
  Probability/         finite probability spaces
    FinitePMF.lean       pmfs (`IsPMF`), random variables, laws (`dist`), `AbsCont`, uniform pmf
    Event.lean           events and their probabilities `Pr{S}`
    Conditional.lean     conditional distributions `p(y | x)`
    Independence.lean    independence and conditional independence
    RandomVector.lean    random vectors `(X₀, …, X_{n-1})`, mutual independence
    Channel.lean         channels (transition kernels) `W(y | x)`
    Jensen.lean          Jensen's inequality
    Variance.lean        variance, Markov's and Chebyshev's inequalities
    IID.lean             i.i.d. sequences, the sample mean
    WeakLaw.lean         convergence in probability and in mean square, the weak law
  Analysis/
    LogSum.lean          the log sum inequality
  Entropy/
    Basic.lean           entropy `H(X)`, change of base
    Conditional.lean     conditional entropy `H(Y | X)`, chain rule
    ChainRule.lean       chain rule for random vectors
    Bounds.lean          `H(X) ≤ log |𝒳|`, conditioning reduces entropy, independence bound
    Concavity.lean       concavity of entropy
    Fano.lean            Fano's inequality
    Collision.lean       the probability `Pr(X = X')` that two independent variables agree
  RelativeEntropy/
    Basic.lean           relative entropy `D(p ‖ q)`
    InformationInequality.lean  `D(p ‖ q) ≥ 0`
    Conditional.lean     conditional relative entropy, chain rule
    Convexity.lean       convexity of `D(p ‖ q)`
    Gibbs.lean           the Gibbs variational principle, tilted distributions
    Pinsker.lean         the `L₁` distance and Pinsker's inequality
  MutualInformation/
    Basic.lean           mutual information `I(X; Y)`
    Conditional.lean     conditional mutual information `I(X; Y | Z)`
    ChainRule.lean       chain rule for mutual information
    Convexity.lean       concavity and convexity of `I(X; Y)`
  AEP/
    Basic.lean           the asymptotic equipartition property, sample entropy
    TypicalSet.lean      the typical set `A_ε^(n)` and its properties
    HighProbabilitySet.lean  smallest high-probability sets, `≐` (equality to first order)
    StrongTypicality.lean  strongly typical sequences, `Pr{A_ε^{*(n)}} → 1`
  StochasticProcess/
    Basic.lean           stochastic processes, stationarity, entropy rates
    Independent.lean     independent and i.i.d. processes
    Markov.lean          Markov chains as processes, the entropy rate of a Markov chain
    HiddenMarkov.lean    functions of Markov chains, hidden Markov models
    Recurrence.lean      recurrence times, Kac's lemma, the process of blocks
  SourceCoding/
    FixedLength.lean     fixed-length binary codes
    TypicalSetCode.lean  data compression with the typical set
    Code.lean            source codes: non-singular, uniquely decodable and prefix codes
    Kraft.lean           the Kraft and McMillan inequalities, finite and countable
    OptimalLength.lean   `L ≥ H_D(X)`, the Shannon code, optimal lengths, the wrong code
    Huffman.lean         Huffman codes and their optimality
    ShannonFanoElias.lean  Shannon–Fano–Elias coding
    ShannonFanoEliasBlock.lean  Shannon–Fano–Elias coding of sequences
    Competitive.lean     competitive optimality of the Shannon code
    CoinFlips.lean       generating discrete distributions from fair coin flips
    Universal.lean       universal source codes built from the method of types
    Minimax.lean         redundancy, minimax redundancy equals channel capacity
    BinarySequences.lean  two-stage and Bernoulli mixture codes, the Laplace estimate
    Arithmetic.lean      the probability integral transform, arithmetic coding intervals
    LempelZiv.lean       the LZ77 and LZ78 algorithms
    IntegerCode.lean     the Elias gamma and delta codes for the integers
    RecurrenceTime.lean  recurrence time coding, optimality of the idealized LZ77
    LempelZivOptimality.lean  Ziv's inequality, optimality of LZ78
  ChannelCoding/
    Capacity.lean        channel capacity, its properties, symmetric channels
    Code.lean            channel codes, error probabilities, achievable rates
    JointTypicality.lean  jointly typical sequences, the joint AEP
    Achievability.lean   random coding, the channel coding theorem (achievability)
    Converse.lean        Fano's inequality and the converse, zero-error codes, feedback capacity
    Hamming.lean         the (7, 4) Hamming code
    SourceChannel.lean   the joint source–channel coding theorem
  Gambling/
    HorseRace.lean       the horse race, doubling rate, proportional gambling, fair odds, cash
    SideInformation.lean  the value of side information, `ΔW = I(X; Y)`
    DependentRaces.lean  sequential betting on a stochastic process, doubling rate and entropy rate
    DataCompression.lean  data compression with a gambler and its identical twin
  MarkovChain/
    Basic.lean           Markov chains `X → Y → Z`
    Process.lean         Markov processes, stationary and doubly stochastic matrices
    DataProcessing.lean  the data processing inequality
    SecondLaw.lean       the second law of thermodynamics
    RandomWalk.lean      random walks on weighted graphs, reversibility
  DifferentialEntropy/
    Basic.lean           densities (`IsPDF`), differential entropy `h(f)`, translation and scaling
    AEP.lean             the AEP for continuous random variables, the typical set and its volume
    Quantization.lean    quantization, `H(X^Δ) + log Δ → h(X)`
    Joint.lean           joint and conditional differential entropy, mutual information `I(X; Y)`
    ChainRule.lean       chain rule for differential entropy, the independence bound
    RelativeEntropy.lean  relative entropy `D(f ‖ g)` of densities and `D(f ‖ g) ≥ 0`
    Gaussian.lean        entropy of the normal distribution, maximum entropy, estimation error
    MultivariateGaussian.lean  the multivariate normal `N(m, K)`, its entropy, Hadamard's inequality
    Partition.lean       mutual information of general random variables via finite partitions
    Estimation.lean      estimation error with side information
  GaussianChannel/
    Basic.lean           additive noise channels, bounding `I(X; Y)` by a reference output density
    Capacity.lean        the information capacity `½ log (1 + P/N)` of the Gaussian channel
    Code.lean            codes with a power constraint, error probabilities, achievable rates
    Converse.lean        the converse to the coding theorem
    Achievability.lean   random Gaussian codes, threshold decoding, Theorem 9.1.1
    Bandlimited.lean     the sampling theorem, the capacity `W log (1 + P/(N₀W))`
    WaterFilling.lean    water-filling
    Parallel.lean        parallel Gaussian channels
    ColoredNoise.lean    Gaussian channels with colored noise, the capacity `C_n`
    Feedback.lean        the capacity with feedback, `C_{n,FB} ≤ C_n + ½` and `C_{n,FB} ≤ 2C_n`
  RateDistortion/
    Basic.lean           distortion measures, rate distortion codes, `R(D)`, convexity of `R(D)`
    Converse.lean        the converse to the rate distortion theorem
    Achievability.lean   distortion typical sets, random coding, achievability
    Theorem.lean         the rate distortion region, `R(D) = R^(I)(D)`
    Binary.lean          the Bernoulli source, `R(D) = H(p) - H(D)`
    Gaussian.lean        the Gaussian source, `R(D) = ½ log (σ²/D)`
    ParallelGaussian.lean  independent Gaussian sources, reverse water-filling
    SourceChannel.lean   source–channel separation with distortion
    BlahutArimoto.lean   `R(D)` as a double minimization, the Blahut–Arimoto algorithm
  Statistics/
    SufficientStatistic.lean  sufficient and minimal sufficient statistics
    Bernoulli.lean       Bernoulli trials, the number of ones as a sufficient statistic
    Types.lean           the method of types: types, type classes and their sizes
    LargeDeviations.lean  Sanov's theorem, the law of large numbers for types
    ConditionalLimit.lean  the Pythagorean theorem for `D`, the conditional limit theorem
    HypothesisTesting.lean  the Neyman–Pearson lemma, the Chernoff–Stein lemma
    ChernoffInformation.lean  the Bayesian error exponent, Chernoff information
    FisherInformation.lean  Fisher information and the Cramér–Rao inequality
  MaxEntropy/
    Basic.lean           Theorem 12.1.1, the maximum entropy distribution under moment constraints
    Distributions.lean   uniform, exponential, normal and Gibbs maximum entropy distributions
    Covariance.lean      maximum entropy under partial covariance constraints
    Burg.lean            AR(p) covariances, the Yule–Walker equations, Burg's theorem
  Kolmogorov/
    Computer.lean        computers, universal computers, Kolmogorov complexity, Kraft, counting
    Programs.lean        computable programs: printing a string, self-delimiting lengths
    BinaryStrings.lean   strings with `k` ones, `K(x | n) ≤ n H₀(k/n) + log n + c`
    Entropy.lean         `K` and entropy, integers, incompressible sequences
    UniversalProbability.lean  universal probability, Ω, universal gambling, the structure function
    Universal.lean       the construction of a universal computer
    Noncomputable.lean   the noncomputability of `K`
  Network/
    Gaussian.lean        Gaussian multiple-access, broadcast, relay and interference formulas
    Typicality.lean      conditional joint typicality, i.i.d. pairs, Theorem 15.2.2
    MACCode.lean         multiple-access codes, achievable rates, time sharing (Theorem 15.3.2)
    MACRegion.lean       the pentagons, the time-sharing region, Lemma 15.3.1
    MACAchievability.lean  random coding for the multiple-access channel
    MACConverse.lean     the converse for the multiple-access channel
    MACCapacity.lean     the capacity region, Theorems 15.3.1 and 15.3.4, corner points
    SlepianWolf.lean     distributed source codes, random binning, Theorem 15.4.1
    Broadcast.lean       broadcast codes, Theorem 15.6.1, degraded broadcast channels
  Investment/
    Basic.lean           growth rates, log-optimal portfolios, concavity and convexity
    KuhnTucker.lean      the Kuhn–Tucker conditions, `E(S/S*) ≤ 1`
    SideInformation.lean  wrong beliefs and side information, `ΔW ≤ D(f‖g)` and `ΔW ≤ I(X; Y)`
    Causal.lean          causal strategies in market processes, the chain rule, stationary markets
    AlmostSure.lean      almost sure growth, asymptotic optimality, the sandwich lemma
    Competitive.lean     competitive optimality with fair randomization
    Universal.lean       universal portfolios, Theorem 16.7.1
  Inequalities/
    Han.lean             submodular set functions, Han's inequalities
    SubsetEntropy.lean   entropies of subsets of random variables, Theorems 17.6.1–17.6.4
    EntropyBounds.lean   the L₁ bound on entropy, the χ² approximation, `E D(p̂ₙ‖p)`
    Binomial.lean        bounds on binomial coefficients from Stirling's sequence
    Schur.lean           Schur complements, Fischer's inequality, Bergstrøm's theorems
    Determinant.lean     principal minors, Koteljanskii, Szász, Theorems 17.9.4–17.9.5, Minkowski
    Toeplitz.lean        determinants of Toeplitz matrices, Theorem 17.9.6
  Book/                Cover & Thomas, namespace `InfoTheory.CoverThomas`
    Chapter1.lean        index of Chapter 1 (the preview), worked examples
    Chapter2.lean        index of Chapter 2, worked examples, aliases `theorem_2_6_5`, …
    Chapter3.lean        index of Chapter 3, worked examples, aliases `theorem_3_1_1`, …
    Chapter4.lean        index of Chapter 4, worked examples, aliases `theorem_4_2_1`, …
    Chapter5.lean        index of Chapter 5, worked examples, aliases `theorem_5_2_1`, …
    Chapter6.lean        index of Chapter 6, worked examples, aliases `theorem_6_1_1`, …
    Chapter7.lean        index of Chapter 7, worked examples, aliases `theorem_7_2_1`, …
    Chapter8.lean        index of Chapter 8, worked examples, aliases `theorem_8_2_1`, …
    Chapter9.lean        index of Chapter 9, worked examples, aliases `theorem_9_1_1`, …
    Chapter10.lean       index of Chapter 10, worked examples, aliases `theorem_10_2_1`, …
    Chapter11.lean       index of Chapter 11, worked examples, aliases `theorem_11_1_1`, …
    Chapter12.lean       index of Chapter 12, worked examples, aliases `theorem_12_1_1`, …
    Chapter13.lean       index of Chapter 13, worked examples, aliases `theorem_13_1_1`, …
    Chapter14.lean       index of Chapter 14, worked examples, aliases `theorem_14_2_1`, …
    Chapter15.lean       index of Chapter 15, worked examples, aliases `theorem_15_3_1`, …
    Chapter16.lean       index of Chapter 16, aliases `theorem_16_2_1`, …
    Chapter17.lean       index of Chapter 17, aliases `theorem_17_1_11`, …
docs/
  references.bib       bibliography, cited in docstrings as `[cover2006]`
```

General theory goes in the topic folders. Material that is specific to the textbook (its worked
examples, its numbering, textbook-only definitions) goes in `Book/ChapterN.lean`, which also maps
each numbered result to the declaration that proves it.

## Conventions

* Alphabets are finite (`Fintype`). A pmf is a function `p : α → ℝ` with `IsPMF p`, and a random
  variable is a function `X : Ω → α` on a finite probability space `(Ω, μ)`.
* From Chapter 8 on, continuous random variables are described by a density `f` with
  `IsPDF μ f` with respect to a reference measure `μ` (Lebesgue measure on `ℝ` or `ℝⁿ`).
  Differential entropies are Bochner integrals, so results assume the integrability of the
  relevant `f log f` terms.
* Logarithms are natural, so quantities are measured in nats. Statements in bits are obtained by
  dividing by `log 2`; the data compression results use `entropyBase D` (base `D`) directly.
* A stochastic process is given by its finite-dimensional laws (`StochasticProcess`). A code is a
  map `C : X → List α` into strings over a code alphabet `α`.
* `relEntropy` takes values in `[0, ∞]` (`EReal`); most results use the real-valued
  `relEntropyReal` under absolute continuity.

See [CONTRIBUTING.md](CONTRIBUTING.md) for the full conventions and the workflow for adding
files.

## Roadmap

Chapters 1–17 are done, so every chapter of Cover & Thomas has a topic folder and a
`Book/ChapterN.lean` index. The remaining work is listed in the "Not formalized" section of each
chapter file.

## How this library was made

The definitions, statements and proofs were written by Claude, an AI model by Anthropic, working
as a coding agent in Claude Code under the direction of Matteo Nerini, who chose the scope, the
conventions and the organization, and is responsible for the project.

What is guaranteed mechanically: every proof is checked by Lean's kernel; the library contains no
`sorry`; continuous integration builds it with warnings treated as errors; and axiom audits show
that every declaration depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

What is not guaranteed mechanically: that each Lean statement says what the corresponding
statement of the book says. The statements follow the book closely, and each chapter file lists
the conventions used and the deviations from the book, but before relying on a result, read its
Lean statement.

## Relation to Mathlib

Mathlib already contains some information theory in `Mathlib/InformationTheory/` (Hamming
distance, the Kraft–McMillan inequality, and the measure-theoretic Kullback–Leibler divergence
`InformationTheory.klDiv`), as well as `Real.binEntropy` and `Real.negMulLog`. This library
reuses them where possible. Connecting the finite `relEntropyReal` to `klDiv` is a natural step
before the continuous chapters. Lemmas in `ForMathlib/` are candidates for upstreaming.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006.

## License

Released under the Apache 2.0 license, see [LICENSE](LICENSE).
