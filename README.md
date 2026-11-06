# infotheorylib

[![Lean Action CI](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-API-blue)](https://matteonerini.github.io/infotheorylib/docs/)

A [Lean 4](https://lean-lang.org) library of information theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

The goal is to formalize the core concepts and theorems of information theory and to organize them
by topic, following two texts:

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006.
* A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*,
  [arXiv:1001.3404v4](https://arxiv.org/abs/1001.3404v4), 2010.

## Status

All 17 chapters of Cover & Thomas and Lectures 1–22 of El Gamal & Kim are formalized, with some
omissions. Each [chapter](InfoTheoryLib/Books/CoverThomas/) and
[lecture](InfoTheoryLib/Books/ElGamalKim/) file indexes what is proved and has a "Not formalized"
section listing what is not. Many lecture files also record the differences from the notes and the
errors found in them.

## How this library was made

The definitions, statements and proofs were written by Claude, an AI model by Anthropic, working
as a coding agent in Claude Code under the direction of Matteo Nerini.

What is guaranteed mechanically: every proof is checked by Lean's kernel; the library contains no
`sorry`; and continuous integration builds it with warnings treated as errors and checks that every
declaration depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`
(`axiom-audit`).

What is not guaranteed mechanically: that each Lean statement says what the corresponding
statement of the text says. The statements follow the texts closely, and each chapter and lecture
file lists the conventions used and the deviations from the text, but before relying on a result,
read its Lean statement.

## Main results

A selection of the headline theorems; every formalized result of the two texts is listed, with its
Lean name, in the chapter and lecture files. Browse them in the
[API documentation](https://matteonerini.github.io/infotheorylib/docs/). Below, C&T is Cover & Thomas,
with theorem numbers, and EGK is El Gamal & Kim, with lecture numbers.

| Result | Lean declaration | Module |
|---|---|---|
| Asymptotic equipartition property (C&T 3.1.1) | `aep` | `AEP.Basic` |
| Source coding bounds `H ≤ L* < H + 1` (C&T 5.4.1) | `minExpectedLength_bounds` | `SourceCoding.OptimalLength` |
| Channel coding theorem (C&T 7.7.1) | `isAchievableRate_of_lt_capacity`, `IsAchievableRate.le_capacity` | `ChannelCoding.Achievability`, `ChannelCoding.Converse` |
| Capacity of the Gaussian channel (C&T 9.1.1) | `gaussianOpCapacity_eq` | `GaussianChannel.Achievability` |
| Rate distortion theorem (C&T 10.2.1) | `rateDistortion_eq_infoRD` | `RateDistortion.Theorem` |
| Sanov's theorem (C&T 11.4.1) | `prob_typeEvent_le_sanov`, `tendsto_log_prob_typeEvent` | `Statistics.LargeDeviations` |
| Kolmogorov complexity and entropy (C&T 14.3.1) | `tendsto_expected_complexity_div` | `Kolmogorov.Entropy` |
| Universal portfolios (C&T 16.7.1) | `minimax_universal` | `Investment.Universal` |
| Capacity region of the multiple access channel (EGK Lecture 4) | `macCapacityRegionBits_eq` | `Network.MACBits` |
| Capacity region of the degraded broadcast channel (EGK Lecture 5) | `bcCapacityRegionBits_eq_closure_degradedBCRegionBits` | `Network.BCCapacity` |
| Gelfand–Pinsker theorem (EGK Lecture 7) | `stateCapacity_noncausal_false` | `StateChannel.GPConverse` |
| Slepian–Wolf theorem (EGK Lecture 11) | `swOptimalRegionBits_eq` | `Network.SlepianWolfBits` |
| Wyner–Ziv theorem (EGK Lecture 12) | `rateWZBits_eq` | `RateDistortion.SideInfoConverse` |
| Network coding theorem (EGK Lecture 16) | `network_coding_theorem` | `Network.NetworkCoding` |
| Compress–forward lower bound for the relay channel (EGK Lecture 17) | `isAchievableRC_compressForward` | `Network.RelayCF` |
| Noisy network coding (EGK Lecture 19) | `isAchievableMN_nnc`, `isAchievableDMN_nnc` | `Network.NNCTheorem` |
| Orlitsky–Roche theorem (EGK Lecture 22) | `losslessFunBits_eq_condGraphEntropy` | `RateDistortion.GraphEntropy` |

## Getting started

You need [elan](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib is pinned in `lakefile.toml`.

```sh
git clone https://github.com/matteonerini/infotheorylib
cd infotheorylib
lake exe cache get   # download prebuilt Mathlib files
lake build           # build the library
```

The first build compiles the whole library, which takes a while.

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

The library is organized by topic. Each file starts with a docstring listing its main definitions
and statements, and the sections of the text it covers.

```
InfoTheoryLib.lean        root file, imports every module (generated by `lake exe mk_all`)
InfoTheoryLib/
  ForMathlib/             general facts not specific to information theory, to upstream to Mathlib
  Probability/            finite probability spaces: pmfs, conditioning, channels, i.i.d. sequences
  Analysis/               the log sum inequality
  Entropy/                entropy, conditional entropy, Fano's inequality, Mrs. Gerber's lemma
  RelativeEntropy/        relative entropy, the information inequality, Pinsker's inequality
  MutualInformation/      mutual information, chain rules, the Csiszár sum identity
  MarkovChain/            Markov chains, data processing, the second law, random walks
  AEP/                    the asymptotic equipartition property and typical sets
  Typicality/             robust typicality, the packing, covering and Markov lemmas
  StochasticProcess/      stochastic processes and entropy rates
  SourceCoding/           source codes, Kraft's inequality, Huffman codes, universal coding
  ChannelCoding/          channel capacity and the channel coding theorem
  Gambling/               the horse race, side information, gambling and data compression
  DifferentialEntropy/    densities, differential entropy, the Gaussian distribution
  GaussianChannel/        Gaussian channels, water-filling, feedback, vector channels, fading
  RateDistortion/         rate distortion theory, with side information
  Statistics/             sufficient statistics, the method of types, large deviations, testing
  MaxEntropy/             maximum entropy distributions and Burg's theorem
  Kolmogorov/             Kolmogorov complexity and universal probability
  Investment/             log-optimal portfolios and universal portfolios
  Inequalities/           Han's inequalities and determinant inequalities
  StateChannel/           channels with state, the compound channel, Gelfand–Pinsker
  Network/                multi-user channels, distributed source coding, networks
  Books/
    CoverThomas/          ChapterN.lean: index, worked examples and aliases for each chapter
    ElGamalKim/           LectureN.lean: index, worked examples and aliases for each lecture
docs/
  references.bib          bibliography of the API documentation
```

General theory goes in the topic folders, shared by both texts. Material that is specific to a
text (its worked examples, its numbering, text-only definitions) goes in
`Books/CoverThomas/ChapterN.lean` or `Books/ElGamalKim/LectureN.lean`, which also map each result of
the chapter or lecture to the declaration that proves it.

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
* Two notions of typicality coexist: the weak typicality of Cover & Thomas (`typicalSet`) and the
  robust typicality of El Gamal & Kim (`robustTypicalSet`); robustly typical sequences are weakly
  typical (`robustTypicalSet_subset_typicalSet`).

See [CONTRIBUTING.md](CONTRIBUTING.md) for the full conventions and the workflow for adding
files.

## Relation to Mathlib

Mathlib already contains some information theory in `Mathlib/InformationTheory/` (Hamming
distance, the Kraft–McMillan inequality, and the measure-theoretic Kullback–Leibler divergence
`InformationTheory.klDiv`), as well as `Real.binEntropy` and `Real.negMulLog`. This library
reuses them where possible. Connecting the finite `relEntropyReal` to `klDiv` is a natural next
step. Lemmas in `ForMathlib/` are candidates for upstreaming.

## License

Released under the Apache 2.0 license, see [LICENSE](LICENSE).
