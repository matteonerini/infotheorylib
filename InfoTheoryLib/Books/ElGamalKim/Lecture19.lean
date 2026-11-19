/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DetNoInterference

/-!
# El Gamal & Kim, Lecture 19: Discrete Memoryless Networks

This file indexes the formalization of Lecture 19 of [elgamal2010]. We prove the cutset bounds for
multicast networks and for networks with many sources; the decode–forward lower bound, with sliding
window decoding, for any number of nodes; the noisy network coding lower bound and inner bound; the
capacity of physically degraded networks and of the relay channel with two destinations; and, for
deterministic networks, the lower bounds and the capacity of the finite-field networks and of the
networks with no interference.

## Conventions

* **Nodes.** The nodes are `Fin N`, numbered from `0`. Each node `k` has an input alphabet `X k` and
  an output alphabet `Y k`, and the channel is `W : (∀ k, X k) → (∀ k, Y k) → ℝ`.
* **Rates.** Rates are in bits with `2 ^ ⌈n R⌉` messages, and informations are in nats, so that a
  condition is written as `R * log 2 < I`.
* **Multicast.** There is one kind of code, `DMNCode`. A multicast code is a code in which only the
  source has a rate different from `0`, that is more than one message (`IsAchievableMN`). The
  convention `Y₁ = ∅` of the notes is `Y s = Unit`; if `Y s` is not trivial the source has feedback.
  The convention `X_N = ∅` is `X last = Unit`.
* **Decode–forward.** The source is the node numbered `0`, and the order of the nodes is the order
  of decoding. For `d ≠ 0`, the node `d` is the node `k + 1` of the notes.
* **Compressions.** `Ŷ_k` of the notes is `V k`, and the law is `nncLaw px W τ`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Networks and the cutset bounds (pages 19-2 to 19-7, 19-37 to 19-40)
* The code and the rates: `DMNCode`, `DMNCode.law`, `DMNCode.errProb`, `IsAchievableDMN`,
  `dmnCapacityRegion`, `IsAchievableMN`, `mnCapacity` (`Network.DMNetwork`).
* The information across a cut: `cutInfo`, `cutInfo_eq`, its concavity `sum_cutInfo_le`, its
  continuity `continuous_cutInfo`.
* **Theorem 1**: `IsAchievableMN.exists_cutset`, `mnCapacity_mul_log_le`, with the bound
  `mnCutsetBound`. Here: `theorem_19_1`.
* **Theorem 4**: `IsAchievableDMN.exists_cutset`, `exists_cutset_of_mem_dmnCapacityRegion`. The
  bound for one code is `DMNCode.exists_cutset_le`. Here: `theorem_19_4`.

### Decode–forward (pages 19-8 to 19-17)
* **Theorem 2**: `isAchievableMN_df` (`Network.DFTheorem`), with the information `dfInfo` and the
  chain rule `sum_dfE_eq`. Here: `theorem_19_2`.
* Strategies for a correlated input law: `buildAt`, `sum_strat_build` (`Network.DFStrategy`).
* The code of one block: `DFBlock`, `sum_dfBlock_true`, the bound on the test
  `sum_dfBlock_test_le` (`Network.DFBlock`).
* Sliding window decoding: `dfWin`, `dfEst`, `dfEst_eq_of_good` (`Network.DFCode`).
* The genie run: `DFGood`, the product over the window `sum_dfGenie_win_le`,
  `sum_dfGenie_not_good_le` (`Network.DFGenie`).
* The code of all the blocks: `dfCode`, `dfCode_law`, `dfCode_avg_le` (`Network.DFRun`).
* **Physically degraded networks**: `IsDegradedNet`, `cutInfo_dfLt_eq`, `dfBound`,
  `mnCapacity_of_degraded` (`Network.DFDegraded`).
* **The relay channel with two destinations**, page 19-9: `mnCapacity_relay_both`.

### Noisy network coding (pages 19-18, 19-22 to 19-36, 19-40)
* **Theorem 3**: `isAchievableMN_nnc`, `le_mnCapacity_of_nnc` (`Network.NNCTheorem`), with the
  information `nncInfo` (`Network.NNCRate`). Here: `theorem_19_3`.
* **Theorem 5**, without the time sharing variable: `isAchievableDMN_nnc`. Here: `theorem_19_5`.
* The law and the bound for the fresh nodes: `nncLaw`, `nncJ`, `nncTest`, `sum_nnc_fresh_le`
  (`Network.NNCLaw`).
* Covering at all the nodes: `nncHyb`, `nncHyb_update_le`, `nnc_cover` (`Network.NNCCover`).
* The code of one block: `NNCBlock`, `sum_nncBlock_test_le`, `sum_nncBlock_bad_eq`
  (`Network.NNCBlock`).
* The trellis of the compression indices: `pathCount_succ`, `sum_run_exists_le` (`Network.PiLaw`);
  `nnc_step`, `nnc_pathCount_le` (`Network.NNCTrellis`).
* The code of all the blocks: `nncCode`, `nncCode_law`, `nncCode_dec_eq`, `nncCode_avg_le`,
  `nnc_exists_code` (`Network.NNCCode`).
* The identity of page 19-35, as an inequality: `nncInfo_le` (`Network.NNCRate`).

### Deterministic networks (pages 19-19 to 19-21, 19-41)
* The information across a cut and the lower bounds: `detW`, `cutInfo_detW`, `nncInfo_detW`,
  `isAchievableMN_det`, `isAchievableDMN_det`, `mnCapacity_det_eq` (`Network.DetNetwork`).
* **Finite-field networks**: `ffdF`, `ffdG`, `cutInfo_ffd_le`, `cutInfo_ffd_uniform`,
  `mnCapacity_ffd` (`Network.DetFiniteField`).
* **Networks with no interference**: `niF`, `niH`, `cutInfo_ni_le`, `cutInfo_ni_prod`, `niBound`,
  `mnCapacity_ni` (`Network.DetNoInterference`).

## Differences from the notes

* **The cutset bound** is proved directly for many sources. Time sharing is replaced by the
  concavity of the information across a cut, and by compactness there is one input law for all the
  cuts, also for the closure of the achievable rates.
* **Decode–forward.** The notes draw each codeword given the codewords of the nodes after it. We
  draw random strategies, with independent entries, and the tuple built by them has law `p(xᴺ)`
  (`sum_strat_build`). The notes bound the error "by induction": we use a genie run, whose blocks
  are independent, and which coincides with the actual run on the good event. The messages need not
  be uniform: the bound holds for each sequence of messages.
* **Covering in noisy network coding.** The notes use the Markov lemma, with no details. We use a
  hybrid argument: the nodes switch from the true conditional law to their codebooks one at a time,
  and each node looks for a sequence for which the conditional probability of a bad tuple is small
  (`nncHyb_update_le`).
* **The independence of the blocks in noisy network coding.** The notes assume that all the true
  compression indices are `1`, and then factor the probability over the blocks (step (a) on pages
  19-25 and 19-32). The true index of a block depends on the codebook of that block, so this needs
  an argument. We keep the true indices as a state, and split the labels of a block by the set `A`
  of the nodes whose label differs from the true index. The bound on the test holds whatever the law
  of the sequences of the nodes that are not fresh (`sum_nnc_fresh_le`). The same bound covers the
  labels of `Sᶜ` that differ from the true index, which the notes leave to "(check!)" on page 19-33.
* **Theorem 5** has the weaker hypothesis: the cuts in which all the rates are `0` are not needed,
  so that Theorem 3 is a special case. It is stated for nonnegative rates.
* **The exponent.** The identity on page 19-35 is proved as the inequality `nncInfo_le`, which is
  enough and needs no independence.
* **Degradedness** is stated as the Markov chains that the notes use on page 19-8, for all the input
  laws, instead of the conditional laws that imply them.

## Not formalized

* The time sharing variable `Q` of Theorem 5, and the remark on page 19-40 on tightening the outer
  bound with `Q`, with the `N`-sender MAC.
* The improvements on page 19-9: removing and reordering nodes. The order of the nodes is free, but
  there is no statement over the permutations.
* Identifications with earlier models: the DM-BC with a common message, the DM-RC of Lecture 17 and
  the noiseless networks of Lecture 16 as special cases. The results for those models are proved
  directly: `isAchievableRC_compressForward` is the compress–forward bound of page 19-22,
  `rcCapacity_semiDet` covers the deterministic relay channel of page 19-21, and
  `Network.NetworkCoding` the noiseless multicast networks.
* The cited statement that compress–forward is not tight for the deterministic relay channel.

## Issues in the notes

* **Page 19-21: the capacity of a finite-field network** is printed as
  `min_{k ∈ D} max_{S} rank(G(S)) log q`, and should have a minimum over `S`, as on page 19-19.
  Here: `printed_ffd_counterexample`, a network with capacity `0` for which the printed value is
  `log 2`. The formula was confirmed against the PDF.
* The following were read from the extracted text.
* Page 19-7: `I(X_Q(S), Y_Q(Sᶜ) | …)`, twice, and `I(X(S), Y(Sᶜ) | X(Sᶜ))`, should have a colon.
* Page 19-12: `R < I(X₁; Y₃ | X₂) + I(X₂; Y₃) = I(X₁, X₂; Y₃) - 2 δ(ε)` should have the term
  `2 δ(ε)` on both sides.
* Page 19-15: "Node `N` sends `x_Nⁿ(j)` in block `j ∈ [1 : N]`" should have `[1 : b]`.
* Page 19-24: "the sender transmits `xⁿ(j, m)` is block `j`" should read `x₁ⁿ(j, m)` in block `j`.
* Page 19-33: `I₁(S) := (I(X(S); Ŷ(Sᶜ) | X(Sᶜ))` has an unmatched parenthesis.
* Page 19-36: "→ 0 as `n → 0`" should have `n → ∞`, and the rate condition is stated "for each
  destination node `k`" with `Y_j`.
* Page 19-38: the message sets are `[1 : 2^{nR₁}], …, [1 : 2^{nR_{N-1}}]`, and should go to `R_N`.
* Page 19-40: the formula of Theorem 5 has an unmatched parenthesis, and as stated it requires also
  the cuts in which all the rates are `0`, so it does not contain Theorem 3 as a special case. In
  fact it can never hold: `S = ∅` meets its side condition and gives `0 < 0`. `theorem_19_5`
  requires a positive rate in `S`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

section Printed

/-- The network of the counterexample: only the link from node `0` to node `1` is not zero. -/
def printedFfdG (j k : Fin 3) : ZMod 2 := if j = 0 ∧ k = 1 then 1 else 0

/-- **Page 19-21 of [elgamal2010]: the printed formula is wrong.** In the network with source `0`,
destination `2`, and a single link from `0` to `1`, the capacity is `0`. The cut `{0}` has rank `1`,
so the printed `min_k max_S rank(G(S)) log q` is `log 2`. -/
theorem printed_ffd_counterexample :
    mnCapacity (X := fun _ => ZMod 2) (Y := fun _ => ZMod 2) (detW (ffdF printedFfdG)) 0 {2} * log 2
      = 0
      ∧ (ffdG printedFfdG {0}).rank = 1 := by
  classical
  have h₀ : (ffdG printedFfdG {0, 1}).rank = 0 := by
    have : ffdG printedFfdG {0, 1} = 0 := by
      ext l j
      have hl : (l : Fin 3) = 2 := by
        have := l.property
        revert this
        generalize (l : Fin 3) = t
        fin_cases t <;> simp
      simp [ffdG, printedFfdG, hl]
    rw [this, Matrix.rank_zero]
  refine ⟨?_, ?_⟩
  · have h := mnCapacity_ffd (F := ZMod 2) printedFfdG (s := 0) (D := {2}) (by simp)
      (k₀ := 2) (S₀ := {0, 1}) (by simp) (by simp) (by decide) (fun k hk S hs hkS => by
        rw [h₀]
        exact Nat.zero_le _)
    rw [h, h₀]
    simp
  · refine le_antisymm ?_ ?_
    · have := Matrix.rank_le_card_width (ffdG printedFfdG {0})
      simpa using this
    · by_contra hlt
      have h0 : (ffdG printedFfdG {0}).rank = 0 := by omega
      have hr : LinearMap.range (ffdG printedFfdG {0}).mulVecLin = ⊥ :=
        Submodule.finrank_eq_zero.mp ((Matrix.finrank_range_mulVecLin _).trans h0)
      have hv : (ffdG printedFfdG {0}).mulVec (fun _ => 1) ∈
          LinearMap.range (ffdG printedFfdG {0}).mulVecLin :=
        ⟨fun _ => 1, Matrix.mulVecLin_apply _ _⟩
      rw [hr, Submodule.mem_bot] at hv
      have hl : (1 : Fin 3) ∈ (({0} : Finset (Fin 3))ᶜ : Finset (Fin 3)) := by decide
      have := congrFun hv ⟨1, hl⟩
      simp only [Matrix.mulVec, dotProduct, ffdG, Matrix.of_apply, mul_one, Pi.zero_apply] at this
      rw [Finset.sum_coe_sort {0} fun j : Fin 3 => printedFfdG j 1] at this
      simp [printedFfdG] at this

end Printed

section Aliases

variable {N : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

/-- **Theorem 1, the cutset bound, page 19-5.** -/
theorem theorem_19_1 (hW : IsChannel W) {s : Fin N} {D : Finset (Fin N)} {R : ℝ}
    (h : IsAchievableMN W s D R) :
    ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S → k ∉ S →
      R * log 2 ≤ cutInfo p W S :=
  IsAchievableMN.exists_cutset hW h

/-- **Theorem 2, the decode–forward lower bound, page 19-8.** -/
theorem theorem_19_2 {p : (∀ l, X l) → ℝ} (hp : IsPMF p) (hW : IsChannel W) {s₀ : Fin N}
    (hs : (s₀ : ℕ) = 0) {D : Finset (Fin N)} (hD : ∀ k ∈ D, (k : ℕ) ≠ 0) {R : ℝ} (hR : 0 ≤ R)
    (hrate : ∀ d : Fin N, (d : ℕ) ≠ 0 → R * log 2 < dfInfo p W d) : IsAchievableMN W s₀ D R :=
  isAchievableMN_df hp hW hs hD hR hrate

/-- **Theorem 3, the noisy network coding lower bound, page 19-18.** -/
theorem theorem_19_3 {px : ∀ k, X k → ℝ} {τ : ∀ k, X k × Y k → V k → ℝ}
    (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k)) {s : Fin N}
    {D : Finset (Fin N)} {R : ℝ} (hR : 0 ≤ R)
    (hrate : ∀ d ∈ D, ∀ S : Finset (Fin N), s ∈ S → d ∉ S →
      R * log 2 < nncInfo (nncLaw px W τ) S d) : IsAchievableMN W s D R :=
  isAchievableMN_nnc hpx hW hτ hR hrate

/-- **Theorem 4, the cutset outer bound, page 19-39.** -/
theorem theorem_19_4 (hW : IsChannel W) {D : Fin N → Finset (Fin N)} {R : Fin N → ℝ}
    (h : R ∈ dmnCapacityRegion W D) :
    ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ S, (∑ k ∈ crossing D S, R k) * log 2 ≤ cutInfo p W S :=
  exists_cutset_of_mem_dmnCapacityRegion hW h

/-- **Theorem 5, the noisy network coding inner bound, page 19-40**, without the time sharing
variable. -/
theorem theorem_19_5 {px : ∀ k, X k → ℝ} {τ : ∀ k, X k × Y k → V k → ℝ}
    (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    {D : Fin N → Finset (Fin N)} {R : Fin N → ℝ} (hR0 : ∀ k, 0 ≤ R k)
    (hrate : ∀ d ∈ univ.biUnion D, ∀ S : Finset (Fin N), d ∉ S → (∃ k ∈ S, 0 < R k) →
      (∑ k ∈ S, R k) * log 2 < nncInfo (nncLaw px W τ) S d) : IsAchievableDMN W D R :=
  isAchievableDMN_nnc hpx hW hτ hR0 hrate

end Aliases

end InfoTheory.ElGamalKim
