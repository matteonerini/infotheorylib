# Contributing to infotheorylib

This file describes how the library is organized and the conventions every file follows. They
are adapted from [Mathlib's](https://leanprover-community.github.io/contribute/index.html).

## Workflow

* Build the library with `lake build`. A single module can be built with, for example,
  `lake build InfoTheoryLib.Entropy.Basic`. `lake build` uses the options in `lakefile.toml`,
  including Mathlib's linters; `lake env lean File.lean` does not.
* After adding, moving or deleting a file, run `lake exe mk_all` to regenerate the root file
  `InfoTheoryLib.lean`. `lake exe mk_all --check` checks it is up to date.
* A change is ready when `lake build --wfail` succeeds: no errors, no warnings and no `sorry`.
  A statement that is planned but not yet proved can be recorded with `proof_wanted`.
* Continuous integration also runs `axiom-audit`, since `--wfail` does not report `axiom`
  declarations.
* Before a release, replay the proofs through the kernel with `leanchecker`, which takes about 20
  minutes. It runs one module per process because of
  [lean4#16267](https://github.com/leanprover/lean4/issues/16267), which makes
  `leanchecker InfoTheoryLib` crash on this Lean version:
  ```sh
  git ls-files 'InfoTheoryLib/*.lean' | sed 's/\.lean$//; s|/|.|g' |
    LEAN_NUM_THREADS=1 lake env xargs -P 4 -n 1 leanchecker
  ```
* Also before a release, run `lake check --paranoid` once. It uses independent proof checkers too,
  but it re-checks Mathlib, so it can take a long time. On macOS, add `--inadvisably-no-sandbox`.

## Where things go

* **Topic folders** (`Probability/`, `Entropy/`, `RelativeEntropy/`, `MutualInformation/`,
  `MarkovChain/`, `Statistics/`, …) hold the general theory. A file covers one topic and its name
  says what it is about (`Entropy/Fano.lean`, not `Entropy/Section211.lean`). Split a file when it
  grows past about 1000 lines.
* **`ForMathlib/`** holds results that do not mention information theory, such as facts about
  `Real.log`. They are candidates for upstreaming to Mathlib.
* **`Books/CoverThomas/ChapterN.lean`** and **`Books/ElGamalKim/LectureN.lean`** hold material
  specific to one text: its worked examples, text-only definitions and the index of the chapter or
  lecture. Cover & Thomas is in `Books/CoverThomas/` (namespace `InfoTheory.CoverThomas`), with one
  file per chapter, and El Gamal & Kim's lecture notes are in `Books/ElGamalKim/` (namespace
  `InfoTheory.ElGamalKim`), with one file per lecture or appendix; a long lecture can have extra
  files (`Lecture14Binary.lean`). Yeung's book is in `Books/Yeung/` (namespace `InfoTheory.Yeung`),
  with one file per chapter. Each numbered lemma or theorem gets an alias
  named after its number (`theorem_2_6_5`; `theorem_3_2` for Theorem 2 of Lecture 3) pointing to the
  library declaration; a named but unnumbered result gets an alias named after it
  (`mrs_gerber_lemma`). Results that are useful beyond the text belong in a topic folder, with a
  descriptive name, and a result that both texts state is proved once and indexed in both files.
* Check Mathlib before defining something: reuse `Real.negMulLog`, `Real.binEntropy`,
  `ConvexOn`, and so on.

## File template

```lean
/-
Copyright (c) 2026 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
module

public import InfoTheoryLib.Entropy.Basic

/-!
# Title of the file

One paragraph describing the content.

## Main definitions

* `foo`: what it is.

## Main statements

* `foo_le_bar`: what it says.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.6
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]

...

end InfoTheory
```

The header linter requires the copyright block exactly in this form. Every file uses Lean's
module system: a `module` header, `public import`s, and `@[expose] public noncomputable section`
(`@[expose] public section` in a file with computable definitions, such as
`ChannelCoding/Hamming.lean`), which makes all declarations and definition bodies visible to other
files. Mathlib imports its own dependencies privately, so a lemma is available only after
importing the Mathlib file that declares it (or one that imports it publicly), and the bodies of
Mathlib definitions that are not exposed cannot be unfolded: use their characterizing lemmas
instead (see `binEntropy_eq_mul_log_inv`). Import only the modules that are needed; a few base
files, such as `ForMathlib/Log.lean` and `Probability/FinitePMF.lean`, import `Mathlib`. Add any
new reference to `docs/references.bib` and cite it by its key.

## Mathematical conventions

* **Finite spaces.** Alphabets and sample spaces are `Fintype`s. A pmf is a function
  `p : α → ℝ` with `IsPMF p`. A random variable is `X : Ω → α` on `(Ω, μ)` with `IsPMF μ`; its
  law is `dist μ X` and the pair `(X, Y)` is `pair X Y`.
* **Units.** Logarithms are natural, so quantities are in nats. Results in bits are stated by
  dividing by `log 2`, or with `entropyBits`.
* **Infinite values.** `relEntropy` is `EReal`-valued and equals `⊤` unless `AbsCont p q`.
  Results are usually stated for the real-valued `relEntropyReal` under `AbsCont p q`.
* **Indexing.** Sequences of random variables are `X : ℕ → Ω → α`, indexed from `0`, and
  `prefixRV X n = (X₀, …, X_{n-1})`.
* **Notation.** `H[X ; μ]`, `H[Y | X ; μ]`, `I[X : Y ; μ]` and `I[X : Y | Z ; μ]` are scoped in
  `InfoTheory`. New notation should also be scoped.

## Naming and style

* Follow [Mathlib's naming conventions](https://leanprover-community.github.io/contribute/naming.html):
  `snake_case` for theorems, `lowerCamelCase` for definitions of terms, `UpperCamelCase` for
  types, structures and propositions (`IsPMF`, `MarkovChain`). Names describe the statement
  (`condEntropy_le_entropy`), not the book number.
* The main concepts are `entropy`/`entropyRV`, `condEntropy`, `relEntropy`/`relEntropyReal`,
  `condRelEntropy`, `mutualInfo` and `condMutualInfo`; build new names from these.
* A docstring of a result from a book starts with its number and name in bold, for example
  `/-- **Theorem 2.6.3 (Information inequality).** ... -/`, and cites equation numbers such as
  `(2.82)`.
* Every definition and every main theorem has a docstring. Lines are at most 100 characters.
* Do not use `open Classical` or `open scoped Classical` for a whole file. Use the `classical`
  tactic inside proofs, or `open Classical in` before a single declaration whose statement needs
  it.
* When a section variable such as `[Fintype α]` is not needed in a statement, remove it with
  `omit [Fintype α] in` rather than disabling the linter.
