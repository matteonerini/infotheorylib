# infotheorylib

[![Lean Action CI](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-API-blue)](https://matteonerini.github.io/infotheorylib/docs/)

A [Lean 4](https://lean-lang.org) library of information theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

It formalizes the core concepts and theorems of information theory, organized by topic, following
three texts:

* T. M. Cover and J. A. Thomas,
  [*Elements of Information Theory*](https://doi.org/10.1002/047174882X),
  2nd ed., Wiley, 2006.
* A. El Gamal and Y.-H. Kim,
  [*Lecture Notes on Network Information Theory*](https://arxiv.org/abs/1001.3404v4),
  arXiv:1001.3404v4, 2010.
* R. W. Yeung,
  [*Information Theory and Network Coding*](https://iest2.ie.cuhk.edu.hk/~whyeung/post/draft2.pdf),
  Springer, 2008.

All 17 chapters of Cover & Thomas, Lectures 1–24 and Appendices A–E of El Gamal & Kim, and all 21
chapters of Yeung are formalized, with some omissions. Each chapter or lecture file
([Cover & Thomas](InfoTheoryLib/Books/CoverThomas/),
[El Gamal & Kim](InfoTheoryLib/Books/ElGamalKim/), [Yeung](InfoTheoryLib/Books/Yeung/)) indexes
what is proved and has a "Not formalized" section listing what is not. Many of these files also
record the differences from the text and the errors found in it.

The library has three kinds of folders. Declarations are in the namespace `InfoTheory`, except in
some files of `ForMathlib/`, which use Mathlib-style namespaces:

* Topic folders such as `Entropy/`, `ChannelCoding/` and `Network/` hold the general theory,
  shared by the three texts.
* `Books/` has one file per chapter or lecture of each text, with its worked examples, aliases
  named after the numbers of its results (`CoverThomas.theorem_2_6_5`), and an index mapping the
  text to the library.
* `ForMathlib/` holds general lemmas, candidates for upstreaming to Mathlib.

Each file starts with a docstring listing its main definitions and statements and the sections of
the text it covers. All the definitions and theorems can be browsed in the
[API documentation](https://matteonerini.github.io/infotheorylib/docs/).

## Getting started

You need [elan](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib is pinned in `lakefile.toml`.

There are two ways to get the library: build this repository on its own, or add it to your own
project. Follow one of the two subsections below, then see [Using the library](#using-the-library).

### Building this repository

```sh
git clone https://github.com/matteonerini/infotheorylib
cd infotheorylib
lake exe cache get   # download prebuilt Mathlib files
lake build           # build the library
```

The first build compiles the whole library, which takes a while.

### Adding it to your own project

Add the library to your project's `lakefile.toml`:

```toml
[[require]]
name = "infotheorylib"
git = "https://github.com/matteonerini/infotheorylib"
rev = "v4.37.0-rc1"
```

A Lake project can contain only one version of Mathlib, so your project must use the same Lean
and Mathlib versions as the release: copy the `lean-toolchain` file of this repository into your
project, and do not require a different version of Mathlib. Then run

```sh
lake update infotheorylib
lake exe cache get   # download prebuilt Mathlib files
```

The cache covers only Mathlib, so the first build of your project also compiles this library.
Releases are tagged with the Lean version they support; the available versions are listed on the
[releases page](https://github.com/matteonerini/infotheorylib/releases). The library can be
imported from both module and non-module files.

### Using the library

Whichever way you got the library, import it and open the `InfoTheory` namespace, which also
activates the notation `H[X ; μ]`, `H[X | Y ; μ]`, `I[X : Y ; μ]` and `I[X : Y | Z ; μ]`:

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

## Conventions

* Alphabets are finite (`Fintype`). A pmf is a function `p : α → ℝ` with `IsPMF p`, and a random
  variable is a function `X : Ω → α` on a finite probability space `(Ω, μ)`.
* Continuous random variables (from Chapter 8 of Cover & Thomas on) are described by a density
  `f` with `IsPDF μ f` with respect to a reference measure `μ` (Lebesgue measure on `ℝ` or `ℝⁿ`).
  Differential entropies are Bochner integrals, so results assume the integrability of the
  relevant `f log f` terms.
* Logarithms are natural, so quantities are measured in nats. Statements in bits are obtained by
  dividing by `log 2`; the data compression results use `entropyBase D` (base `D`) directly.
* A stochastic process is given by its finite-dimensional laws (`StochasticProcess`). A code is a
  map `C : X → List α` into strings over a code alphabet `α`.
* `relEntropy` takes values in `[0, ∞]` (`EReal`); most results use the real-valued
  `relEntropyReal` under absolute continuity.
* Three notions of typicality coexist: the weak typicality of Cover & Thomas (`typicalSet`), the
  robust typicality of El Gamal & Kim (`robustTypicalSet`), and the strong typicality of Yeung, in
  variational distance (`l1TypicalSet`). Robustly typical sequences are weakly typical
  (`robustTypicalSet_subset_typicalSet`).

See [CONTRIBUTING.md](CONTRIBUTING.md) for the full conventions and the workflow for adding
files.

## Relation to Mathlib

Mathlib already contains some information theory in `Mathlib/InformationTheory/` (Hamming
distance, the Kraft–McMillan inequality, and the measure-theoretic Kullback–Leibler divergence
`InformationTheory.klDiv`), as well as `Real.binEntropy` and `Real.negMulLog`. This library
reuses them where possible. Connecting the finite `relEntropyReal` to `klDiv` is a natural next
step. Lemmas in `ForMathlib/` are candidates for upstreaming.

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

## License

Released under the Apache 2.0 license, see [LICENSE](LICENSE).
