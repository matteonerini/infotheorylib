/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture15Examples

/-!
# El Gamal & Kim, Lecture 15: Joint Source–Channel Coding

This file indexes the formalization of Lecture 15 of [elgamal2010]. We prove the joint
source–channel coding theorems for the DM-MAC (Theorems 1 and 2), the Gray–Wyner theorem (Theorem
3), the relations between the common part, the mutual information and Wyner's common information and
the corners of the Gray–Wyner region, and the two examples where source–channel separation fails.
Over the DM-BC we define the codes and prove the example.

## Conventions

* **Rates.** The sources are sent at rate `1` symbol per transmission, as in the notes, so the
  conditions of Theorems 1 and 2 compare entropies and informations, both in nats. The rates of the
  Gray–Wyner system are in bits, with the index sets `[1 : 2^{nR})` of the notes, and `gwInfo`,
  `gwCond₁`, `gwCond₂`, `gkCommon` and `wynerJ` are in nats.
* **Random variables.** The law of Theorems 1 and 2 is `jsLaw P τ κ₁ κ₂ W` on the alphabet
  `JZ α₁ α₂ ω ξ₁ ξ₂ β`, with the coordinates `jU₁`, `jU₂`, `jW`, `jX₁`, `jX₂`, `jY`.
* **Common part.** Theorem 2 is proved for any functions with `g₁(U₁) = g₂(U₂)` almost surely. The
  common part of the notes is `commonG₁`, `commonG₂`, which is the largest such pair.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Joint source–channel codes over a DM-MAC (pages 15-3 and 15-4)
* `MACJSCCCode`, `MACJSCCCode.errProb`, `IsLosslessMAC` (`Network.JSCCMAC`).

### The random coding bound (pages 15-9 to 15-12 and 15-17)
* Tables of independent entries: `piLaw`, `sum_piLaw_mul_prod`, `sum_piLaw_mul_eval`,
  `sum_piLaw_mul_eval₂` (`Network.JSCCRandomCode`).
* The law of the tables and the expectation of the terms: `JSCCTable`, `jsccLaw`, `eval_true`,
  `eval_a`, `eval_b`, `eval_c`, `eval_d`, `jsccD`, `jsccDec`.
* **The bound**: `jsccF₀`, `jsccFa`, `jsccFb`, `jsccFc`, `jsccFd`, `jsccBound`,
  `exists_jscc_code_le`, `jsccBound_eq`.

### Theorems 1 and 2 (pages 15-7, 15-9 to 15-12 and 15-16 to 15-18)
* The law and the entropies: `jsLaw`, `entropy_jsLaw`, `jsGap_a`, `jsGap_b`, `jsGap_c`, `jsGap_d`
  (`Network.JSCCMACLaw`).
* The four error events: `sum_all_eq`, `sum_typical_le`, `event_a`, `event_b`, `event_c`, `event_d`,
  `event_true`, `exists_macCode_le` (`Network.JSCCMAC`).
* **Theorem 2**: `isLosslessMAC_of_lt` (`Network.JSCCMAC`), `theorem_15_2` (here).
* **Theorem 1**: `isLosslessMAC_of_lt_time` (`Network.JSCCMAC`), `theorem_15_1` (here).

### The example over the binary erasure MAC (pages 15-5 and 15-6)
* Uncoded transmission: `isLosslessMAC_of_uncoded` (`Network.JSCCMAC`).
* `jsTriPMF`, `entropy_jsTriPMF`, `isLosslessMAC_jsTriPMF`, `binEntropy_le_quadratic`,
  `erasure_sum_le`, `entropy_jsTriPMF_gt_erasure` (`Books.ElGamalKim.Lecture15Examples`).

### The common part (pages 15-14 and 15-15)
* `commonRel`, `CommonIdx`, `commonG₁`, `commonG₂`, `commonG_eq`, **`exists_common_lift`**
  (`Network.CommonInformation`).

### The Gray–Wyner system (pages 15-21 to 15-24)
* `GWCode`, `GWCode.errProb`, `IsAchievableGW`, `gwRegion`, `gwInfo`, `gwCond₁`, `gwCond₂`
  (`Network.GrayWyner`).
* The direct part: `exists_index_of_card_le`, `exists_gwCode_of_card_le`, `isAchievableGW_of_lt`.
* The converse: `sum_condEntropy_le_gw`, `GWCode.exists_channel` (`Network.GrayWynerConverse`).
* The cardinality bound: `condEntropy_of_rep`, `mutualInfo_of_rep`, `exists_rep_channel`,
  `exists_gw_reduce`.
* **Theorem 3**: `gwSet`, `isClosed_gwSet`, `mem_gwRegion_of_channel`, `gwRegion_subset_gwSet`,
  `gwRegion_eq` (`Network.GrayWynerConverse`), `theorem_15_3` (here).
* The extreme points and the four bounds: `gw_extreme_zero`, `gw_extreme_one`, `gw_extreme_two`,
  `gw_extreme_both`, `mem_gwRegion_det`, `gwRegion_le` (`Network.CommonInformation`).

### Notions of common information (pages 15-24 to 15-26)
* `gkCommon`, `gkCommon_mem_gwRegion`, **`le_gkCommon_of_mem_gwRegion`**,
  `gwInfo_le_gkCommon_of_markov`.
* `mutualInfo_of_outer`.
* `gwResidual`, `wynerSet`, `wynerJ`, `exists_wyner_min`, `wynerJ_mem_gwRegion`,
  **`wynerJ_le_of_mem_gwRegion`**.
* **`common_information_chain`**: `0 ≤ K ≤ I ≤ J ≤ H`.
* The example: `gkCommon_jsTriPMF`, `mutualInfo_jsTriPMF`, `two_thirds_le`, `two_thirds_le_gwInfo`,
  `wynerJ_jsTriPMF`, `common_information_strict` (`Books.ElGamalKim.Lecture15Examples`).

### Sources over a DM-BC (pages 15-19 and 15-29)
* `BCJSCCCode`, `BCJSCCCode.errProb`, `IsLosslessBC`, `isLosslessBC_of_uncoded` (`Network.JSCCBC`).
* The example over the Blackwell channel: `jsTriInput`, `isLosslessBC_jsTriPMF`,
  **`gray_wyner_blackwell`** (`Books.ElGamalKim.Lecture15Examples`).

## Not formalized

* **Theorem 4** (Han–Costa) and its special cases, Lemma 1 and the appendix, pages 15-30 to 15-40.
  The proof needs a three-layer covering lemma with random mappings of `(u₁ⁿ, u₂ⁿ)` on top of Marton
  coding with a common message, which Lecture 9 also leaves out.
* The separation results over the DM-BC on pages 15-20, 15-27 and 15-28, and the code-level meaning
  of the bounds `R₀ + R₁ ≤ H(Y₁)` on page 15-29. `gray_wyner_blackwell` is a statement about the
  Gray–Wyner region and these three inequalities.
* The sufficient conditions of separate coding on pages 15-4 and 15-5, the special cases of Theorem
  1 on pages 15-7 and 15-8 and the example `U₁ = U₂` on page 15-13, as corollaries.
* The DM-MAC with common message on page 15-17 and the claim that `W` need not be correlated with
  `U₀`; the claim that the scheme is not optimal in general [5].
* The characterization of `K = I = J` on page 15-25, and the value of `J` for the DSBS on page
  15-26.

## Differences from the notes

* **Theorem 2 first.** We prove Theorem 2, for any common function, and Theorem 1 is the case of a
  constant function, with `W = Q`. So time sharing is not a separate argument, unlike page 15-9.
* **Independent tables.** The codewords are drawn for all pairs `(u₁ⁿ, wⁿ)` in advance,
  independently of the table of the `wⁿ(u₀ⁿ)`, and the codeword used is `x₁ⁿ(u₁ⁿ, wⁿ(u₀ⁿ))`. The
  joint law of a few entries then has an elementary form (`sum_piLaw_mul_eval₂`). The notes draw
  `x₁ⁿ` given `wⁿ(u₀ⁿ)`.
* **The error events.** `E₄` of the notes splits into two events, for the true and for a wrong
  common part, which give the third and the fourth inequality of Theorem 2. All the events are
  bounded by `|T_ε| max p(visible) p(new)`, by `sum_typical_le` and the law of the visible
  variables.
* **The decoder** checks the common part directly, instead of relying on joint typicality for it.
* **The Gray–Wyner achievability** sends the position of `uⱼⁿ` in `T_ε(Uⱼ|vⁿ)` by an explicit index
  (`exists_index_of_card_le`), and the codebook of `vⁿ` is chosen by the averaging of
    `exists_layer`.
* **The converse of Theorem 3** uses a uniform time index `Q` with
  `V = (Q, M₀, U₁^{Q-1}, U₂^{Q-1})`.
* **`K` as the largest common rate.** The notes only state this. We prove that the conditions imply
  the two Markov chains `V → U₁ → U₂` and `V → U₂ → U₁`, that the channel `p(v|u₁, u₂)` is then a
  function of the common part (`exists_common_lift`), and that `I(U₁, U₂; V) ≤ H(U₀)`.
* **`J = 2/3` for the example.** The notes cite [8]. We prove the lower bound: if `I(U₁; U₂|V) = 0`,
  every `v` has `P{U₁ = 1, V = v} = 0` or `P{U₂ = 0, V = v} = 0`, so `I(U₁, U₂; V)` is at least the
  value for a binary `V`, whose minimum follows from the convexity of the mutual information.
* **The Blackwell channel** has the input labels of Lecture 9: the inputs `0`, `1`, `2` give
  `(Y₁, Y₂) = (0, 0)`, `(1, 1)`, `(0, 1)`, which is a relabelling of the channel on page 15-29.

## Issues in the notes

Pages 15-25 and 15-26 were checked against the PDF, and the others were read from its extracted
text.

* **Page 15-26.** The parameters of the channel that achieves `J = 2/3` are exchanged. With
  `U₂ ∼ Bern(2/3)` given `V = 0` and `U₁ ∼ Bern(1/3)` given `V = 1` the law would be
  `p(0, 0) = 1/6`, `p(0, 1) = 2/3`, `p(1, 1) = 1/6`. The correct choice is `U₂ ∼ Bern(1/3)` given
  `V = 0` and `U₁ ∼ Bern(2/3)` given `V = 1`, which is `jsTriW (1/2)` up to the labels of `V`.
* Page 15-23: the description is "sent by decoder 0"; it should be encoder 0.
* Page 15-25: `K(X; Y)` should be `K(U₁; U₂)`.
* Page 15-40: the bound on `p₃` has the argument `U₁, W₁, U₁`, with `U₁` written twice, and the last
  condition on `R₀ + R₁ + R₂` has `δ(ε)` where the other three have `3δ(ε)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

section Aliases

variable {α₁ α₂ ω ξ₁ ξ₂ β c : Type*} [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂]
  [Fintype β] [Fintype c] {P : α₁ × α₂ → ℝ} {τ : ω → ℝ} {κ₁ : α₁ × ω → ξ₁ → ℝ}
  {κ₂ : α₂ × ω → ξ₂ → ℝ} {W : ξ₁ × ξ₂ → β → ℝ}

/-- **Theorem 1 of Lecture 15, page 15-7.** -/
theorem theorem_15_1 (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hW : IsChannel W)
    (ha : H[jU₁ | jU₂ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₁ : jY | pair jX₂ (pair jU₂ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hb : H[jU₂ | jU₁ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₂ : jY | pair jX₁ (pair jU₁ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hc : H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] <
      I[pair jX₁ jX₂ : jY | jW ; jsLaw P τ κ₁ κ₂ W]) :
    IsLosslessMAC P W :=
  isLosslessMAC_of_lt_time hP hτ h₁ h₂ hW ha hb hc

/-- **Theorem 2 of Lecture 15, page 15-16.** -/
theorem theorem_15_2 (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hW : IsChannel W) {g₁ : α₁ → c} {g₂ : α₂ → c} (hg : ∀ a b, P (a, b) ≠ 0 → g₁ a = g₂ b)
    (ha : H[jU₁ | jU₂ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₁ : jY | pair jX₂ (pair jU₂ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hb : H[jU₂ | jU₁ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₂ : jY | pair jX₁ (pair jU₁ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hc : H[pair jU₁ jU₂ | (fun z => g₁ (jU₁ z)) ; jsLaw P τ κ₁ κ₂ W] <
      I[pair jX₁ jX₂ : jY | pair (fun z => g₁ (jU₁ z)) jW ; jsLaw P τ κ₁ κ₂ W])
    (hd : H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] < I[pair jX₁ jX₂ : jY ; jsLaw P τ κ₁ κ₂ W]) :
    IsLosslessMAC P W :=
  isLosslessMAC_of_lt hP hτ h₁ h₂ hW hg ha hb hc hd

/-- **Theorem 3 of Lecture 15, page 15-22: the Gray–Wyner theorem.** -/
theorem theorem_15_3 (hP : IsPMF P) : gwRegion P = gwSet P (Fintype.card (α₁ × α₂) + 2) :=
  gwRegion_eq hP

end Aliases

end InfoTheory.ElGamalKim
