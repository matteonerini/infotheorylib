/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.BlahutArimoto
public import InfoTheoryLib.ForMathlib.AlternatingMaximization
public import InfoTheoryLib.RateDistortion.Normal

/-!
# Yeung, Chapter 9: The Blahut–Arimoto Algorithms

This file indexes the formalization of Chapter 9 of [yeung2008], and contains aliases named after
the numbers of the results, so the index is checked by Lean. It cites the draft of 15 November
2007, which numbers definitions, theorems and examples with one counter per chapter. The
end-of-chapter problems and the historical notes are not included.

## Conventions

* **Logarithms.** Logarithms are natural, as the book itself assumes from (9.51) on.
* **Backward channels.** A transition matrix `q(x|y)` from `Y` to `X` is `q : β → α → ℝ`, with
  `q y x = q(x|y)`. The posterior `q*(x|y)` of (9.17) and (9.48) is `posterior r W`.
* **Products.** The product `∏_y q(x|y)^{p(y|x)}` of (9.55) is `exp (∑_y p(y|x) log q(x|y))`.
* **Rate-distortion algorithm.** The library writes the Lagrangian (9.66) as
  `baObjective p d λ Q t` with `λ = -s ≥ 0`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 9.1 Alternating Optimization
* (9.3)–(9.5): `IsBestFst`, `IsBestSnd` (`ForMathlib.AlternatingMaximization`).
* (9.7)–(9.8): `altSeq` (`ForMathlib.AlternatingMaximization`).
* (9.10)–(9.13): `le_altSeq_succ` (`ForMathlib.AlternatingMaximization`).
* (9.14), the minimization, is the maximization of `-f`.

### 9.2.1 Channel Capacity
* Lemma 9.1: `lemma_9_1` (here), from `baCapObjective_posterior` and
  `baCapObjective_le_mutualInfoOf` (`ChannelCoding.BlahutArimoto`). It holds without `r > 0`, and
  the condition (9.16) on `q` is weakened to: `q(x|y) = 0` only where `r(x) p(y|x) = 0`.
* Theorem 9.2: `theorem_9_2` (here), which is `capacity_eq_sSup_pos`
  (`ChannelCoding.BlahutArimoto`). It is proved from the convergence of the algorithm rather than by
  the book's continuity argument.
* (9.39): `baCapObjective`; (9.40)–(9.41): `baCapDomain` (`ChannelCoding.BlahutArimoto`), without
  the normalization, which concavity does not need.
* (9.43)–(9.46): `baCapObjective_le_mutualInfoOf` (`ChannelCoding.BlahutArimoto`) and
  `capacity_le_log_card_input` (`ChannelCoding.Capacity`).
* (9.48): `posterior` (`RateDistortion.BlahutArimoto`).
* (9.51)–(9.55): `baCapUpdate`, `baCapObjective_le_log_sum_exp`, `baCapObjective_baCapUpdate`
  (`ChannelCoding.BlahutArimoto`). The optimality is proved by the Gibbs inequality, not by Lagrange
  multipliers.
* (9.56): `baCapIter`, `baCapIter_pos`, `baCapIter_isPMF` (`ChannelCoding.BlahutArimoto`).

### 9.2.2 The Rate-Distortion Function
* (9.57): `sInf_mutualInfoOf_sub_mul_eq` (`RateDistortion.Normal`), as an equality of infima.
* Lemma 9.3: `lemma_9_3` (here), which is `mutualInfoOf_le_relEntropy_jointOf_prodDist`
  (`RateDistortion.BlahutArimoto`), with equality at `t*` by `relEntropy_jointOf_prodDist_eq`. The
  library allows any `t` with `p(x) Q(x̂|x) ≪ p(x) t(x̂)` instead of `t > 0`.
* (9.66): `baObjective`; (9.74): `baObjective_outDist_le`; (9.77)–(9.78): `baChannel`,
  `baObjective_baChannel_le`; the iteration: `baIter`, `baObjective_iter_antitone`
  (`RateDistortion.BlahutArimoto`).

### 9.3.1 A Sufficient Condition
* (9.80)–(9.81): `altStep` (`ForMathlib.AlternatingMaximization`).
* Lemma 9.4: `lemma_9_4` (here), which is `lt_altStep` (`ForMathlib.AlternatingMaximization`), with
  (9.93)–(9.101) in `le_of_isMax_coordinatewise`. The proof uses one-sided directional derivatives,
  which are at most `0` at a maximum on a convex set, rather than the book's vanishing derivatives.
* Theorem 9.5: `theorem_9_5` (here), which is `tendsto_altSeq`
  (`ForMathlib.AlternatingMaximization`). The proof needs `A' = {u ∈ A : f' - ε ≤ f(u) ≤ f'}` to be
  compact, which the book derives from `A` being bounded; `A` also has to be closed, which the sets
  of Section 9.2 are not. The Lean statement assumes `A₁` and `A₂` compact and `c₁`, `c₂` and `f`
  continuous.

### 9.3.2 Convergence to the Channel Capacity
* (9.106)–(9.109): `baCapObjective_concaveOn`, from `mul_log_div_concave`
  (`ChannelCoding.BlahutArimoto`).
* `f⁽ᵏ⁾ → C`: `tendsto_mutualInfoOf_baCapIter`, with the rate `C - I(r⁽ᴺ⁾) ≤ D(r* ‖ r⁽⁰⁾)/N`,
  `capacity_sub_mutualInfoOf_baCapIter_le`, and the monotonicity `mutualInfoOf_baCapIter_le_succ`
  (`ChannelCoding.BlahutArimoto`). Since Theorem 9.5 does not apply to the open sets of Section
  9.2, the proof is Arimoto's telescoping bound `sum_sub_mutualInfoOf_baCapIter_le`.

## Not formalized

* The convergence of the algorithm for the rate-distortion function, (9.79), which the book omits.
* (9.64)–(9.65), the replacement of the minimum over `Q` by the infimum over `Q > 0`.
* Figures 9.1 to 9.3.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Lemma 9.1.** (9.15) -/
theorem lemma_9_1 {W : α → β → ℝ} {r : α → ℝ} (hr : IsPMF r) (hW : IsChannel W) :
    baCapObjective W r (posterior r W) = mutualInfoOf r W ∧
      ∀ q : β → α → ℝ, IsChannel q → (∀ x y, q y x = 0 → r x * W x y = 0) →
        baCapObjective W r q ≤ mutualInfoOf r W :=
  ⟨baCapObjective_posterior hr hW, fun _ hq hqW => baCapObjective_le_mutualInfoOf hr hW hq hqW⟩

/-- **Theorem 9.2.** (9.25) -/
alias theorem_9_2 := capacity_eq_sSup_pos

/-- **Lemma 9.3.** (9.60) -/
alias lemma_9_3 := mutualInfoOf_le_relEntropy_jointOf_prodDist

/-- **Lemma 9.4.** -/
alias lemma_9_4 := lt_altStep

/-- **Theorem 9.5.** -/
alias theorem_9_5 := tendsto_altSeq

end InfoTheory.Yeung
