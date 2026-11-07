/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 6: Strong Typicality

This file maps Chapter 6 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Lemma 6.4 (Chernoff Bound): `prob_ge_le_exp_mul_expect` (`Statistics.ChernoffInformation`).

## Partly in the library

* Definition 6.1: `strongTypicalSet`, `robustTypicalSet` (`AEP.StrongTypicality`,
  `Typicality.Basic`). Other definitions: the book's has a sum over the alphabet.
* Theorem 6.2 (Strong AEP): `le_iidPMF_of_mem_robustTypicalSet`,
  `iidPMF_le_of_mem_robustTypicalSet`, `tendsto_prob_strongTypicalSet` (`Typicality.Basic`,
  `AEP.StrongTypicality`). For robust typicality.
* Proposition 6.5: `robustTypicalSet_subset_typicalSet` (`Typicality.Basic`). For robust typicality.
* Definition 6.6: `jointStrongTypicalSet` (`AEP.StrongTypicality`). Other definition.
* Theorem 6.7 (Consistency): `mem_strongTypicalSet_of_mem_joint`, `fst_mem_robustTypicalSet`,
  `snd_mem_robustTypicalSet` (`AEP.StrongTypicality`, `Typicality.Conditional`). Other definitions.
* Theorem 6.8 (Preservation): `comp_mem_robustTypicalSet` (`Typicality.Basic`). For robust
  typicality.
* Theorem 6.9 (Strong JAEP): `tendsto_prob_jointStrongTypicalSet` (`AEP.StrongTypicality`). The
  probability only.
* Theorem 6.10: `card_condRobustTypicalSet_le`, `eventually_card_condRobustTypicalSet_ge`
  (`Typicality.Conditional`). For robust typicality; lower bound needs a smaller δ.

## To formalize

* Theorem 6.3: exponential bound
* Lemma 6.11
* Corollary 6.12
* Proposition 6.13

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 6
-/
