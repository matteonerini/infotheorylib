/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture17Sato
public import InfoTheoryLib.Network.RelayGaussian
public import InfoTheoryLib.Network.RelayModSum
public import InfoTheoryLib.Network.RelayOrthSender

/-!
# El Gamal & Kim, Lecture 17: Relay Channels

This file indexes the formalization of Lecture 17 of [elgamal2010]. We prove the cutset bound, the
direct and multi-hop bounds, decode–forward, partial decode–forward and compress–forward; the
capacity of the degraded, reversely degraded, semi-deterministic and cascade channels, of the
channels with orthogonal components, and of the modulo-2 sum channel, for which the cutset bound is
not tight; and the bounds for the relay with unlimited lookahead and without delay, with the Sato
channel. For the AWGN relay channel, we prove the closed forms of the bounds, not the coding
theorems.

## Conventions

* **Codes.** `RCCode M n X X₁ Y Y₁` has an encoder, a relay encoder that sees the past of `Y₁`, and
  a decoder. The law of a code is a feedback law, `RCCode.law`, which the converse of Lecture 7
  already handles.
* **Rates.** Rates are in bits and `IsAchievableRC W R` has `2 ^ ⌈n R⌉` messages. The information
  quantities are in nats, so that a condition is written as `R * log 2 < I`, and a capacity is
  `V / log 2`.
* **Laws.** The notes' `p(x, x₁)` is a pmf on `X × X₁`, and the channel a map `X × X₁ → Y × Y₁ → ℝ`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Codes and the cutset bound (pages 17-3 to 17-8)
* `RCCode`, `RCCode.fbEnc`, `RCCode.law`, `RCCode.errProb`, `IsAchievableRC`, `rcCapacity`,
  `rcMacInfo`, `rcBcInfo`, `rcCutsetBound` (`Network.RelayCode`).
* **Theorem 1**: `IsAchievableRC.le_rcCutsetBound`. Here: `theorem_17_1`.
* A converse from a bound on the information: `IsAchievableRC.le_of_info_bound`.

### Direct transmission and multi-hop (pages 17-9 to 17-17)
* **Direct transmission**: `isAchievableRC_direct` and, for reversely degraded channels,
  `rcCapacity_reverselyDegraded` (`Network.RelayClasses`).
* **Multi-hop**: `isAchievableRC_multihop` (`Network.RelayDF`). **Cascade**: `rcCapacity_cascade`.

### Block Markov coding (pages 17-11 to 17-28)
* The fresh sequence bound and the random code: `sum_fresh_le`, `Tables₃`, `RelayBlock`,
  `exists_relayBlock_le` (`Network.RelayBlock`); `eventually_relayBlock` (`Network.RelayBlockIID`).
* The code of all the blocks: `RelayBlock.markov`, `RelayBlock.markov_errProb_le`
  (`Network.RelayMarkov`), `isAchievableRC_of_codes`, `isAchievableRC_of_blocks`
  (`Network.RelayRates`).

### Decode–forward (pages 17-18 to 17-35)
* **Theorem 2**: `isAchievableRC_decodeForward`, `isAchievableRC_of_lt_rcDfBound`. Here:
  `theorem_17_2`.
* **Degraded**: `IsDegradedRC`, `rcCapacity_degraded`.
* **The Sato channel (page 17-19)**: `satoW`, `sato_isDegradedRC`, `sato_rcCapacity_le`.
* **Theorem 3**: `isAchievableRC_of_pmf`, `isAchievableRC_partialDF`, `isAchievableRC_of_fun`. Here:
  `theorem_17_3`.
* **Semi-deterministic (page 17-35)**: `IsSemiDetRC`, `rcSemiBound`, `rcCapacity_semiDet`.
* **Orthogonal sender components (page 17-36)**: `rcOS`, `rcOSBound`, `rcCapacity_os`
  (`Network.RelayOrthSender`).

### Compress–forward (pages 17-39 to 17-47, 17-90 and 17-91)
* The offsets and the code of all the blocks: `CFBlock`, `CFBlock.code`, `CFBlock.sum_blockLoss`,
  `CFBlock.exists_code_le` (`Network.RelayCFBlock`).
* The bounds on the tests: `sum_fresh_point`, `sum_fresh_const`, `sum_miss_le`, `tilt_le`
  (`Network.RelayCFTest`).
* The covering step: `cfLaw`, `cfGood`, `cfPick`, `sum_cover_le` (`Network.RelayCFCover`).
* The random code: `cfBlockOf`, `sum_rowA_le`, `sum_rowB_le`, `exists_cfBlock_le`
  (`Network.RelayCFRandom`); `exists_cfBlock_gaps`, `eventually_cfBlock` (`Network.RelayCFRate`).
* **Theorem 4**: `isAchievableRC_compressForward` (`Network.RelayCF`). Here: `theorem_17_4`.
* **The original characterization, one direction of the Appendix**: `cf_terms_sub`,
  `isAchievableRC_compressForward_original`.

### Orthogonal receiver components (pages 17-50 to 17-52)
* `rcRO`, `isAchievableRC_ro`, `rcROBound`, `rcCutsetBound_ro_le` (`Network.RelayOrth`).
* **Semi-deterministic**: `IsSemiDetRO`, `rcCapacity_ro_semiDet`.
* **The modulo-2 sum channel**: `msP`, `msCap`, `isAchievableRC_modSum`, `ms_gerber`, `ms_info_le`,
  `rcCapacity_modSum` (`Network.RelayModSum`).
* **The cutset bound is not tight**: `modSum_lt_cutset`.

### The AWGN relay channel (pages 17-29 to 17-32, 17-48, 17-53, 17-54, 17-84, 17-85)
* Closed forms: `awgnMaxMin`, `awgnClosed`, `isGreatest_awgnMaxMin_of_le`,
  `isGreatest_awgnMaxMin_of_ge`, `awgn_cutset`, `awgn_decodeForward`,
  `awgn_decodeForward_lt_direct`, `awgn_multihop_le_noncoherent`, `awgn_noncoherent_eq`
  (`Network.RelayGaussian`).
* Compress–forward, optimized over `N`: `awgnCFExpr`, `isGreatest_awgnCFExpr`, `isGreatest_awgnCF`.
* The RFD channel: `gaussCap_add_rfd`, `rfd_cutset_eq`, `rfd_df_eq`, `rfd_df_eq_cutset`,
  `isGreatest_rfdCF`.

### Lookahead (pages 17-67 to 17-75)
* **Unlimited lookahead**: `LookCode`, `IsAchievableLook`, `lookCapacity`, `lookCompound`,
  `isAchievableLook_noncausal` (noncausal decode–forward), `IsAchievableLook.le_capacity`
  (`Network.RelayLookahead`). Here: `theorem_17_6`.
* **Relay without delay**: `rwdChannel`, `IsAchievableRWD`, `rwdCapacity`,
  `isAchievableRWD_instantaneous`. **Theorem 7**: `IsAchievableRWD.le_rcCutsetBound`. Here:
  `theorem_17_7`.
* **The Sato channel (pages 17-71 and 17-74)**: `sato_lookCapacity`, `sato_rwdCapacity`,
  `sato_le_log` (`Books.ElGamalKim.Lecture17Sato`). Both capacities are `log₂ (9/4)`.

## Differences from the notes

* **One code for all the blocks, and backward decoding, for decode–forward.** The notes draw a new
  codebook for every block, and use induction over the blocks. We use one fixed code. The genie run
  in which the relay always decodes correctly has independent blocks, and the actual run coincides
  with it as long as nothing goes wrong. Theorem 2 and the multi-hop bound are special cases of
  Theorem 3, with no binning: its conditions are `R' < I(U; Y₁ | X₁)`, `R'' < I(X; Y | X₁, U)` and
  `R' + R'' < I(X, X₁; Y)`.
* **Offsets for compress–forward.** The state of the relay is a random function of the past, and is
  not uniform, so the argument above does not apply. The block code is averaged over its states,
  and fixed offsets `d_j`, known to the receiver, are added to the bin index: for offsets drawn at
  random, the state is uniform and independent of the past (`CFBlock.sum_blockLoss`). The message of
  the last block is drawn in the same way. This replaces the notes' independent codebooks.
* **No conditional typicality lemma.** As in Lecture 12, the relay looks for a good description: one
  that is jointly typical with `(x₁ⁿ, y₁ⁿ)` and such that `(xⁿ, x₁ⁿ, ŷ₁ⁿ, yⁿ)` is typical with high
  probability given `(x₁ⁿ, y₁ⁿ)`, which holds for most i.i.d. sequences by Markov's inequality.
* **Random bins.** Since the bins are independent of the codebook, a description other than the
  chosen one is in its bin with probability `1 / L`, whatever the chosen one is. No analogue of
  Lemma 1 of the Wyner–Ziv proof is needed (pages 17-44 and 17-45).
* **The relay without delay** is the relay channel whose relay alphabet is the set of maps
  `Y₁ → X₁`, so that Theorem 7 is Theorem 1 for that channel.
* **Noncausal decode–forward** is the compound channel theorem of Lecture 7, for the two receivers.
* **The modulo-2 sum channel** is proved for all `p ∈ [0, 1]`. The converse is on an explicit law of
  `(M, Z₁ⁿ, Y₁ⁿ, Y''ⁿ)`, whose factorization gives the independence used in the notes.
* **The capacity is stated in nats over `log 2`**, and the capacity of the modulo-2 sum channel is
  `msCap p C₀ / log 2`.

## Not formalized

* The Gaussian coding theorems, the multi-letter characterization of `C(P)` (page 17-30) and the
  properties of `C(P)` in the Appendix; hence partial decode–forward for the AWGN channel (pages
  17-38 and 17-86 to 17-89, which need the entropy power inequality) and the SFD capacity (page
  17-37).
* Theorem 5, the linear relaying capacity of the RFD channel, amplify–forward and the AWGN channels
  with lookahead or without delay (pages 17-55 to 17-66, 17-72 and 17-75).
* The bounds on the cardinalities in Theorems 3 and 4.
* The other direction of the Appendix on compress–forward (page 17-91), which is an optimization
  over time sharing, and the time sharing extension (page 17-47). The combination of
  compress–forward and partial decode–forward (page 17-47) is cited there without a statement.
* The second term of Theorem 6 (see below), and the numerical values of the Sato channel on page
  17-19: the rates of the other schemes, and `C = 1.161878`, which the notes cite. So the strict
  inequality `C < C∞` of page 17-71 is not proved.

## Issues in the notes

* **Page 17-31, the cutset bound for the AWGN channel.** The closed form has `√(S + S₁ - S₂)` where
  it should have `√(S (S + S₁ - S₂))`. For `S = 4`, `S₁ = S₂ = 1` the printed formula is `C(9/5)`,
  which is even below the direct rate `C(4)`, while the optimum is `C(5)`: `awgn_cutset_notes_ne`.
  The statement `awgn_cutset` has the correct form.
* **Page 17-52, the cutset bound is not tight.** The notes claim strict inequality if `p ∈ (0, 1)`
  and `1 - H(p) ≤ C₀`. It fails for `C₀ = 1`, where `H⁻¹(1 - C₀) = 0` and the capacity is
  `1 - H(p)`, and for `p = 1/2`, where both are `0`. The statement `modSum_lt_cutset` has
  `p ∈ (0, 1/2)` and `0 < C₀ < 1`, and needs no comparison between `1 - H(p)` and `C₀`.
* **Page 17-70, Theorem 6.** With `Y₁ ∼ p(y₁ | x)` the bound does not make sense for a law
  `p(x, x₁)`: for `Y₁` uniform and independent of `X` and `Y = X ⊕ X₁ ⊕ Y₁`, the first term vanishes
  for all `p(x, x₁)`, while the relay can send `X₁ = Y₁` and the capacity is `1` bit. The law must
  allow `X₁` to depend on `Y₁`, that is `p(x) p(x₁ | x, y₁)`. We prove the part that is needed for
  the Sato channel: `C∞` is at most the capacity of the channel from `(X, X₁, Y₁)` to `Y`.
* **Page 17-68.** The index shift `p(y₁ᵢ | x_{i+d})` is inconsistent with unlimited lookahead, and
  we use no shift.
* **Page 17-73.** The pmf `p(v, x), x₁(u, y₁)` has `v` for `u`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

@[expose] public section

namespace InfoTheory.ElGamalKim

open Real

section Aliases

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]

/-- **Theorem 1, the cutset bound, page 17-5.** -/
theorem theorem_17_1 {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRC W R) : R * log 2 ≤ rcCutsetBound W :=
  h.le_rcCutsetBound hW

/-- **Theorem 2, the decode–forward lower bound, page 17-18.** -/
theorem theorem_17_2 [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]
    {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) {R : ℝ} (h : R * log 2 < rcDfBound W) :
    IsAchievableRC W R :=
  isAchievableRC_of_lt_rcDfBound hW h

/-- **Theorem 3, the partial decode–forward lower bound, page 17-33.** -/
theorem theorem_17_3 {U : Type*} [Fintype U] [Nonempty X] [Nonempty X₁] [Nonempty U] [Nonempty Y]
    [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} {q₃ : (X₁ × U) × X → ℝ} (hq₃ : IsPMF q₃)
    (hW : IsChannel W) {R : ℝ} (h₁ : R * log 2 < rcMacInfo (dist q₃ fun t => (t.2, t.1.1)) W)
    (h₂ : R * log 2 < I[fun z => z.1.1.2 : fun z => z.2.2 | fun z => z.1.1.1 ; rcPdfLaw q₃ W] +
      I[fun z => z.1.2 : fun z => z.2.1 | fun z => z.1.1 ; rcPdfLaw q₃ W]) :
    IsAchievableRC W R :=
  isAchievableRC_of_pmf hq₃ hW h₁ h₂

/-- **Theorem 4, the compress–forward lower bound, page 17-39.** -/
theorem theorem_17_4 {V : Type*} [Fintype V] [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]
    [Nonempty V] {W : X × X₁ → Y × Y₁ → ℝ} {p : X → ℝ} {p₁ : X₁ → ℝ} {τ : X₁ × Y₁ → V → ℝ}
    (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) {R : ℝ}
    (hR₁ : R * log 2 < I[fun z => z.1.1 : fun z => z.1.2.1 ; cfLaw p p₁ W τ] -
      I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ; cfLaw p p₁ W τ])
    (hR₂ : R * log 2 <
      I[fun z => z.1.1.1 : fun z => (z.1.2.1, z.2) | fun z => z.1.1.2 ; cfLaw p p₁ W τ]) :
    IsAchievableRC W R :=
  isAchievableRC_compressForward hp hp₁ hW hτ hR₁ hR₂

/-- **An upper bound in place of Theorem 6, page 17-70**, which is false as printed (see the module
doc). With unlimited lookahead, every achievable rate is at most the capacity of the channel from
`(X, X₁, Y₁)` to `Y`. -/
theorem theorem_17_6 [Nonempty X] [Nonempty X₁] [Nonempty Y₁] {W₁ : X → Y₁ → ℝ}
    {W₂ : X × X₁ × Y₁ → Y → ℝ} (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) {R : ℝ} (h : IsAchievableLook
      W₁ W₂ R) : R * log 2 ≤ capacity W₂ :=
  IsAchievableLook.le_capacity h₁ h₂ h

/-- **Theorem 7, the relay-without-delay cutset bound, page 17-73.** -/
theorem theorem_17_7 [DecidableEq Y₁] {W₁ : X → Y₁ → ℝ}
    {W₂ : X × X₁ × Y₁ → Y → ℝ} (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) {R : ℝ} (h : IsAchievableRWD
      W₁ W₂ R) :
    R * log 2 ≤ rcCutsetBound (rwdChannel W₁ W₂) :=
  IsAchievableRWD.le_rcCutsetBound h₁ h₂ h

end Aliases

end InfoTheory.ElGamalKim
