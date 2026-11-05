/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MultiWayExamples
public import InfoTheoryLib.Network.TwoWayLossyInner

/-!
# El Gamal & Kim, Lecture 21: Source Coding over Noiseless Networks

This file indexes the formalization of Lecture 21 of [elgamal2010]. We prove the cutset outer bound
for multiple description networks; Theorem 1 for the line network, with the converse for any tree;
Theorem 2 for the triangular network; Theorem 3, on communication for omniscience, with its two
examples; Theorem 4 of Kaspi on interactive lossy coding, with Lemma 1; and the minimum sum rate of
two-way lossless source coding through a relay.

## Conventions

* **Rates.** Rates are in bits, with `2 ^ ⌊n R⌋` indices, and informations are in nats, so that a
  bound is written as `I ≤ R * log 2`. An achievable rate has codes with distortion at most `D + ε`
  for every `ε` and all large `n`. The regions are the closures of the achievable rates.
* **Nodes.** The nodes of a network are `Fin N`, numbered so that edges go up, with the source at
  the node `s`, which is `0` in the examples. A pair that is not an edge has rate `0`.
* **Interaction.** The indices of all the rounds are kept in one tuple, in which the rounds that
  have not happened hold a default value (`runTo`). The order of the speakers `spk` is arbitrary:
  the alternating order of the notes is a special case, and the first speaker need not be node 1.
* **Theorem 4.** The law of `(X₁, X₂, U^q)` is given by the Markov chains
  `X_{j'} → (X_j, U^{l-1}) → U_l` of each round, which are the factorization of the notes by the
  chain rule (`IsKaspiLaw`).
* **Labels.** The node `k` of the notes is the node `k - 1` here: in Theorem 2, `M₁₂` is the index
  on the edge `(0, 1)`, `X̂₂` is the letter of the node `1`, and so on.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Multiple description networks (pages 21-3 to 21-12)
* The code and the region: `MDNetCode`, `MDNetCode.edge`, `MDNetCode.out`, `IsAchievableMDN`,
  `mdnRegion` (`Network.MDNetwork`).
* The cutset outer bound, for one law for all the cuts: `mdnCut`, `mdnCutset`,
  `MDNetCode.mdnCutset_of_code`, `mdnRegion_subset_mdnCutset`.
* **Theorem 1:** the converse for a tree, `IsRootedTree`, `treeEdges`, `treeDesc`, `mdnCutset_tree`;
  the layered covering, `LineCov`, `lineCov_of_rates`; achievability for the line network,
  `isAchievableMDN_line`; the region, `mdnRegion_line_eq` (`Network.MDLine`), here `theorem_21_1`.
* **Theorem 2:** `triEdges`, `IsTriLaw`, `triInner`, `exists_cond_layer`, `exists_tri_cover`,
  `isAchievableMDN_tri`, `triInner_subset_mdnRegion`, `MDNetCode.exists_tri_law`,
  `exists_triInner_of_mem_mdnRegion` (`Network.MDTriangle`), here `theorem_21_2_inner` and
  `theorem_21_2_converse`.
* A code from a description of the contents of the edges: `MDNetCode.ofParts`.

### Multi-way lossless source coding (pages 21-13 to 21-19)
* The code and the region: `MWCode`, `IsAchievableMW`, `mwOptimalRegion`, `mwRegion`
  (`Network.MultiWay`).
* The cutset bound: `MWCode.mul_swCondH_le`, `IsAchievableMW.mem_mwRegion`.
* Binning: `exists_mw_code_le`, `isAchievableMW_of_lt`.
* **Theorem 3:** `mwOptimalRegion_eq`, here `theorem_21_3`. The remark of page 21-17:
  `mwRegion_eq_iInter`.
* The examples: two nodes, which is the two-way lossless coding of page 21-14, `mwRegion_two`,
  `rCFO_two`; three nodes, `mwRegion_three`, `rCFO_three` (`Network.MultiWayExamples`).

### Two-way lossy source coding (pages 21-20 to 21-29)
* The code and the region: `KaspiCode`, `IsAchievableKaspi`, `kaspiRegion`, `IsKaspiLaw`,
  `kaspiInner` (`Network.TwoWayLossy`).
* **Lemma 1:** `condMutualInfo_of_indep`, `lemma1`, `lemma1_speak`, here `lemma_21_1`. For a code:
  `KaspiCode.condMutualInfo_trans`, `KaspiCode.condMutualInfo_speak` (`Network.TwoWayLossyLetters`).
* The converse: the auxiliary letter `KaspiCode.kU`, the claim (a) `exists_estimator_le`,
  `KaspiCode.markov_dist₁`, `KaspiCode.markov_dist₂`; the claim (b) `KaspiCode.markov_mix`; the
  rates `KaspiCode.rate₁`, `KaspiCode.rate₂`; `KaspiCode.exists_kaspi_law`,
  `exists_kaspiInner_of_mem_kaspiRegion` (`Network.TwoWayLossyConverse`), here
  `theorem_21_4_converse`.
* Achievability: one round, `exists_kaspi_round` (`Network.TwoWayLossyRound`); the protocol,
  `KProto`, `KProto.trans_code`, `KProto.view_code` (`Network.TwoWayLossyProtocol`); the choice of
  the codebooks, `exists_keyed_choice`, `KBook`, `KBook.good_step₁`, `KBook.good_step₂`
  (`Network.TwoWayLossyBook`); the rates, `kaspi_sum_rate₁`, `kaspi_sum_rate₂`, `exists_book`,
  `isAchievableKaspi_of_lt`, `kaspiInner_subset_kaspiRegion` (`Network.TwoWayLossyInner`), here
  `theorem_21_4_inner`.

### Two-way lossless source coding through a relay (pages 21-30 and 21-31)
* `TWRCode`, `IsAchievableTWR`, `twrOptimalRegion`, `twrRegion`, `twrSumRate`
  (`Network.TwoWayRelay`).
* The cutset bounds: `TWRCode.condEntropy_bounds`, `IsAchievableTWR.mem_twrRegion`.
* Slepian–Wolf coding and network coding: `addFin`, `subFin`, `isAchievableTWR_of_lt`.
* The region and the sum rate: `twrOptimalRegion_eq`, `twrSumRate_eq`, here `relay_sum_rate`.

## Differences from the notes

* **Theorem 2.** The law is any law with the source `P`. The notes ask for
  `p(u|x) p(x̂₂|u, x) p(x̂₃|u, x)`, and remark that this makes no difference since the
  bounds depend only on the pairs `(U, X̂₂)` and `(U, X̂₃)`. The proof of achievability
  uses only these pairs.
* **The first auxiliary letter.** In Theorem 4 every `U_{li}` carries the side information
  `(i, X₁^{i-1}, X_{2,i+1}^n)` of the time `i`, whereas the notes put it in `U_{1i}`.
* **The Wyner–Ziv rounds.** The codebook of a round depends on the past sequence itself, not on an
  index, and the rounds are chosen one at a time. A first codeword typical with the past and the
  source of the speaker is selected, and the law of the sources given the past is not a product
  law, so the Markov lemma of Lecture 13 is used with the typicality of `(vⁿ, x_sⁿ, x_oⁿ)` only.
* **The converses of Theorems 2 and 4** are stated with `D + ε` and `R + ε`, as in Lecture 13: with
  no bound on the alphabet of `U`, the union over the alphabets is not known to be closed.
* **Theorem 3.** The rates are nonnegative in the region, which the notes leave implicit: for
  `A = {k}` the formula does not constrain `R_k`.

## Not formalized

* Achievability of Theorem 1 for a tree that is not a line, and the extension of Theorem 2 to the
  ring of page 21-11. The notes treat only the line, and say that this is without loss of
  generality; see below.
* The cardinality bound of Theorem 4, which would give the exact distortions.
* The Gaussian examples of pages 21-11 and 21-21, the inner and outer bounds of page 21-21 as such
  (the inner bound is the case of two rounds of Theorem 4), the reduction to noiseless multicast of
  page 21-5, the diamond network, and the remark on error-free communication of page 21-14.
* The linear program for `R_CFO` of page 21-18.

## Issues in the notes

* **Page 21-17: the formula for the minimum sum rate of three nodes is wrong.** The notes have
  `R_CFO({1, 2}) = H(X₁ | X₂) + H(X₂ | X₁) + max {H(X₃ | X₁), H(X₃ | X₂)}`. The correct first two
  terms are `H(X₁ | X₂, X₃) + H(X₂ | X₁, X₃)` (`rCFO_three`). For `X₃ = X₁` a uniform bit and `X₂`
  an independent uniform bit, the printed formula gives `3` bits and the region gives `2`
  (`printed_rCFO_counterexample`). Confirmed against the PDF.
* **Page 21-10: the converse of Theorem 2 does not give the bound on `R₁₂`.** The chain ends with
  `R₁₂ ≥ I(X̂₂; X | U)`, whereas Theorem 2 has `R₁₂ ≥ I(U, X̂₂; X)`. It must start from
  `H(M₁₂, M₂₃) ≥ I(M₁₂, M₂₃; Xⁿ)`, with the term `I(M₂₃; Xⁿ)` that the notes drop. We bound
  `I(U, X̂₂; X)` directly. Confirmed against the PDF.
* **Page 21-9.** `H(M₂₃) = ∑ᵢ I(M₂₃, X^{i-1}; Xᵢ)` should be `≥`. Confirmed against the PDF.
* **Page 21-7.** "Without loss of generality, suppose the network is a line" is not justified: in a
  tree with a branch, the descriptions of the two branches must be covered jointly, while the
  rate into the branching node is only `I(X; X̂(S_kᶜ))`.
* **Page 21-5.** The cutset bound is for the sets `S` with the source node, not for all `S`.
* **Pages 21-14 and 21-16.** The decoders are functions of the indices only, but they also know the
  source of their node, as is used in the proofs.
* **Page 21-4.** "Decoder `k` assigns an estimate `x̂ⁿ_j`" should be `x̂ⁿ_k`.
* **Page 21-22.** In the cardinality bound `|U_j| ≤ |𝒳_{l_j}| ∏_{l<j} |U_l| + 1` the index is mixed
  up with the indices of the nodes.
* **Page 21-23.** The estimates are printed as `x̂₁(U^q, X₁)` and `x̂₂(U^q, X₂)`; in Theorem 4 they
  are `x̂₁(u^q, x₂)` and `x̂₂(u^q, x₁)`.
* **Page 21-26.** `I(X₁ᵢ, X₁^{i-1}; X₂^{i-1} | …)` should have `X_{1,i+1}^n` in place of `X₁^{i-1}`.
* **Page 21-30.** `R_sum(D₁, D₂)` is written for the lossless problem, which has no distortions.
* **Page 21-31.** `k₁ > H(X₁ | X₂) + δ(ε)` should be `k₁ / n`, and `V^{k₁} = U₁^{k₁} ⊕ Ũ₂^{k₂}`
  should have `Ũ₂^{k₁}`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

section Printed

/-- The two independent uniform bits of the counterexample. -/
abbrev bitLaw : Bool × Bool → ℝ := uniformPMF (Bool × Bool)

/-- The sources of the counterexample: `X₃ = X₁`, and `X₂` is independent of `X₁`. -/
def bitSrc (w : Bool × Bool) : Fin 3 → Bool := fun j => if j = 1 then w.2 else w.1

/-- The law of the sources of the counterexample. -/
def bitP : (Fin 3 → Bool) → ℝ := dist bitLaw bitSrc

lemma bitLaw_isPMF : IsPMF bitLaw := uniformPMF_isPMF

lemma bitP_isPMF : IsPMF bitP := bitLaw_isPMF.dist _

lemma entropy_bit_inj {γ : Type*} [Fintype γ] {g : Bool × Bool → γ} (hg : Function.Injective g) :
    H[g ; bitLaw] = 2 * log 2 := by
  have h := entropyRV_eq_of_injective bitLaw (Y := g) (X := id) g hg (fun _ => rfl)
  rw [h, entropyRV, dist_id, entropy_uniformPMF]
  simp only [Fintype.card_prod, Fintype.card_bool]
  rw [show ((2 * 2 : ℕ) : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num

lemma entropy_bit_fst {γ : Type*} [Fintype γ] {g : Bool × Bool → γ} (φ : Bool → γ)
    (hφ : Function.Injective φ) (hg : ∀ w, g w = φ w.1) : H[g ; bitLaw] = log 2 := by
  have h := entropyRV_eq_of_injective bitLaw (Y := g) (X := Prod.fst) φ hφ hg
  rw [h, entropyRV]
  have e : dist bitLaw Prod.fst = uniformPMF Bool := by
    funext a
    simp [dist, uniformPMF, Fintype.sum_prod_type]
    cases a <;> norm_num
  rw [e, entropy_uniformPMF]
  simp

lemma entropy_bit_snd {γ : Type*} [Fintype γ] {g : Bool × Bool → γ} (φ : Bool → γ)
    (hφ : Function.Injective φ) (hg : ∀ w, g w = φ w.2) : H[g ; bitLaw] = log 2 := by
  have h := entropyRV_eq_of_injective bitLaw (Y := g) (X := Prod.snd) φ hφ hg
  rw [h, entropyRV]
  have e : dist bitLaw Prod.snd = uniformPMF Bool := by
    funext a
    simp [dist, uniformPMF, Fintype.sum_prod_type]
    cases a <;> norm_num
  rw [e, entropy_uniformPMF]
  simp

/-- A conditional entropy of the counterexample. -/
lemma condEntropy_bit {a b : Type*} [Fintype a] [Fintype b] (A : (Fin 3 → Bool) → a)
    (B : (Fin 3 → Bool) → b) : H[A | B ; bitP] =
      H[pair (B ∘ bitSrc) (A ∘ bitSrc) ; bitLaw] - H[B ∘ bitSrc ; bitLaw] := by
  rw [bitP, condEntropy_dist bitLaw_isPMF, condEntropy_eq_sub bitLaw_isPMF]

/-- **Page 21-17 of [elgamal2010]: the printed formula for three nodes is wrong.** For `X₃ = X₁` a
uniform bit and `X₂` an independent uniform bit, the minimum sum rate for `A = {1, 2}` is `2`
bits, and the printed `H(X₁ | X₂) + H(X₂ | X₁) + max {H(X₃ | X₁), H(X₃ | X₂)}` is `3` bits. -/
theorem printed_rCFO_counterexample :
    rCFO (α := fun _ : Fin 3 => Bool) bitP {0, 1} = 2 ∧
      (H[fun x : Fin 3 → Bool => x 0 | fun x => x 1 ; bitP] +
        H[fun x : Fin 3 → Bool => x 1 | fun x => x 0 ; bitP] +
        max (H[fun x : Fin 3 → Bool => x 2 | fun x => x 0 ; bitP])
          (H[fun x : Fin 3 → Bool => x 2 | fun x => x 1 ; bitP])) / log 2 = 3 := by
  have hl2 := log_pos one_lt_two
  have h₂₀ : H[fun x : Fin 3 → Bool => x 2 | fun x => x 0 ; bitP] = 0 := by
    rw [condEntropy_bit, entropy_bit_fst (fun a => (a, a)) (fun a b h => (Prod.mk.inj h).1)
      fun w => by simp [pair, bitSrc], entropy_bit_fst id Function.injective_id
      fun w => by simp [bitSrc]]
    ring
  have h₂₁ : H[fun x : Fin 3 → Bool => x 2 | fun x => x 1 ; bitP] = log 2 := by
    rw [condEntropy_bit, entropy_bit_inj (g := pair _ _) (fun a b h => by
      have := Prod.mk.inj h
      simp only [Function.comp, bitSrc] at this
      simpa [Prod.ext_iff, and_comm] using this),
      entropy_bit_snd id Function.injective_id fun w => by simp [bitSrc]]
    ring
  have h₀₁ : H[fun x : Fin 3 → Bool => x 0 | fun x => x 1 ; bitP] = log 2 := by
    rw [condEntropy_bit, entropy_bit_inj (g := pair _ _) (fun a b h => by
      have := Prod.mk.inj h
      simp only [Function.comp, bitSrc] at this
      simpa [Prod.ext_iff, and_comm] using this),
      entropy_bit_snd id Function.injective_id fun w => by simp [bitSrc]]
    ring
  have h₁₀ : H[fun x : Fin 3 → Bool => x 1 | fun x => x 0 ; bitP] = log 2 := by
    rw [condEntropy_bit, entropy_bit_inj (g := pair _ _) (fun a b h => by
      have := Prod.mk.inj h
      simp only [Function.comp, bitSrc] at this
      simpa [Prod.ext_iff] using this),
      entropy_bit_fst id Function.injective_id fun w => by simp [bitSrc]]
    ring
  have hrest₀ : Function.Injective (swRest (α := fun _ : Fin 3 => Bool) ({0} : Finset (Fin 3)) ∘
      bitSrc) := fun a b h => by
    have h₁ := congrFun h ⟨1, by decide⟩
    have h₂ := congrFun h ⟨2, by decide⟩
    simp only [Function.comp, swRest, bitSrc] at h₁ h₂
    exact Prod.ext (by simpa using h₂) (by simpa using h₁)
  have hS₀ : swCondH (α := fun _ : Fin 3 => Bool) bitP {0} = 0 := by
    rw [swCondH, condEntropy_bit, entropy_bit_inj hrest₀, entropy_bit_inj (g := pair _ _)
      (fun a b h => hrest₀ (Prod.mk.inj h).1)]
    ring
  have hS₁ : swCondH (α := fun _ : Fin 3 => Bool) bitP {1} = log 2 := by
    have hφ : Function.Injective (fun a : Bool => (fun _ : {j : Fin 3 // j ∉ ({1} : Finset (Fin 3))}
      =>
        a)) := fun a b h => congrFun h ⟨0, by decide⟩
    have hrest : ∀ w, (swRest (α := fun _ : Fin 3 => Bool) ({1} : Finset (Fin 3)) ∘ bitSrc) w =
        (fun a : Bool => (fun _ : {j : Fin 3 // j ∉ ({1} : Finset (Fin 3))} => a)) w.1 := fun w =>
          by
      funext ⟨j, hj⟩
      have : j ≠ 1 := by simpa using hj
      simp [swRest, bitSrc, this]
    rw [swCondH, condEntropy_bit, entropy_bit_fst _ hφ hrest, entropy_bit_inj (g := pair _ _)
      (fun a b h => by
        obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
        have e₁ := congrFun h₁ ⟨0, by decide⟩
        have e₂ := congrFun h₂ ⟨1, by decide⟩
        simp only [Function.comp, swRest, swPart, bitSrc] at e₁ e₂
        exact Prod.ext (by simpa using e₁) (by simpa using e₂))]
    ring
  constructor
  · rw [rCFO_three (α := fun _ : Fin 3 => Bool) bitP_isPMF, hS₀, hS₁, h₂₀, h₂₁, max_eq_right hl2.le]
    field_simp
    ring
  · rw [h₀₁, h₁₀, h₂₀, h₂₁, max_eq_right hl2.le]
    field_simp
    ring

end Printed

section Aliases

universe u

/-- **Theorem 1, page 21-6, for the line network.** -/
theorem theorem_21_1 {α : Type*} [Fintype α] {m : ℕ} {β : Fin (m + 1) → Type*}
    [∀ l, Fintype (β l)] [∀ l, Nonempty (β l)] {P : α → ℝ} {d : ∀ l, α → β l → ℝ} (hP : IsPMF P)
    (hd : ∀ l x y, 0 ≤ d l x y) (D : Fin (m + 1) → ℝ) :
    mdnRegion P d 0 (lineEdges m) D = {R | (∀ j k, 0 ≤ R j k) ∧
      (∀ j k, (j, k) ∉ lineEdges m → R j k = 0) ∧ ∃ κ : α → (∀ l, β l) → ℝ, IsChannel κ ∧
      (∀ l, l ≠ 0 → ∑ z, jointOf P κ z * d l z.1 (z.2 l) ≤ D l) ∧
      ∀ k, k ≠ 0 →
        I[Prod.fst : fun z : α × ∀ l, β l => swRest (treeDesc (linePar m) k)ᶜ z.2 ; jointOf P κ] ≤
          R (linePar m k) k * log 2} :=
  mdnRegion_line_eq hP hd D

/-- **Theorem 2, page 21-8: the inner bound.** -/
theorem theorem_21_2_inner {α : Type u} [Fintype α] {β : Fin 3 → Type*} [∀ l, Fintype (β l)]
    [∀ l, Nonempty (β l)] {P : α → ℝ} {d : ∀ l, α → β l → ℝ} (hP : IsPMF P)
    (hd : ∀ l x y, 0 ≤ d l x y) (D : Fin 3 → ℝ) :
    triInner P d D ⊆ mdnRegion P d 0 triEdges D :=
  triInner_subset_mdnRegion hP hd D

/-- **Theorem 2, page 21-8: the converse.** -/
theorem theorem_21_2_converse {α : Type u} [Fintype α] {β : Fin 3 → Type*} [∀ l, Fintype (β l)]
    [Nonempty (β 1)] [Nonempty (β 2)] {P : α → ℝ} {d : ∀ l, α → β l → ℝ} (hP : IsPMF P)
    {D : Fin 3 → ℝ} {R : Fin 3 → Fin 3 → ℝ} (h : R ∈ mdnRegion P d 0 triEdges D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (υ : Type u) (_ : Fintype υ) (μ : α × υ × β 1 × β 2 → ℝ), IsTriLaw P μ ∧
      I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.1 ; μ] ≤ (R 1 2 + ε) * log 2 ∧
      I[Prod.fst : pair (fun z : α × υ × β 1 × β 2 => z.2.2.1) (fun z => z.2.1) ; μ] ≤
        (R 0 1 + ε) * log 2 ∧
      I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.2 | fun z => z.2.1 ; μ] ≤
        (R 0 2 + ε) * log 2 ∧
      ∑ z, μ z * d 1 z.1 z.2.2.1 ≤ D 1 + ε ∧ ∑ z, μ z * d 2 z.1 z.2.2.2 ≤ D 2 + ε :=
  exists_triInner_of_mem_mdnRegion hP h hε

/-- **Theorem 3, page 21-16.** -/
theorem theorem_21_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    {p : (∀ j, α j) → ℝ} (hp : IsPMF p) (A : Finset ι) : mwOptimalRegion p A = mwRegion p A :=
  mwOptimalRegion_eq hp A

/-- **Lemma 1, page 21-25.** -/
theorem lemma_21_1 {Ω a₁ a₂ b₁ b₂ : Type*} [Fintype Ω] [Fintype a₁] [Fintype a₂] [Fintype b₁]
    [Fintype b₂] {μ : Ω → ℝ} {q : ℕ} {A : Fin q → Type*} [∀ l, Fintype (A l)] [∀ l, Nonempty (A l)]
    {spk : Fin q → Bool} {g₁ : ∀ l, a₁ × a₂ → (∀ l', A l') → A l}
    {g₂ : ∀ l, b₁ × b₂ → (∀ l', A l') → A l} {A₁ : Ω → a₁} {A₂ : Ω → a₂} {B₁ : Ω → b₁}
    {B₂ : Ω → b₂} (hμ : IsPMF μ) (h0 : I[A₂ : B₁ | pair A₁ B₂ ; μ] = 0) :
    I[A₂ : B₁ | pair (fun ω => run (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω)) (pair A₁ B₂) ; μ] = 0 :=
  lemma1 hμ h0 q le_rfl

/-- **Theorem 4, page 21-22: the inner bound.** -/
theorem theorem_21_4_inner {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ : Type*} [Finite β₁]
    [Finite β₂] [Nonempty β₁] [Nonempty β₂] {q : ℕ} {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ}
    {d₁ : α₁ → β₁ → ℝ} {d₂ : α₂ → β₂ → ℝ} (hP : IsPMF P) (hd₁ : ∀ x y, 0 ≤ d₁ x y)
    (hd₂ : ∀ x y, 0 ≤ d₂ x y) (D₁ D₂ : ℝ) :
    kaspiInner P spk d₁ d₂ D₁ D₂ ⊆ kaspiRegion P spk d₁ d₂ D₁ D₂ := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  exact kaspiInner_subset_kaspiRegion hP hd₁ hd₂ D₁ D₂

/-- **Theorem 4, page 21-22: the converse.** -/
theorem theorem_21_4_converse {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ : Type*}
    [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂] {q : ℕ} {spk : Fin q → Bool}
    {P : α₁ × α₂ → ℝ} {d₁ : α₁ → β₁ → ℝ} {d₂ : α₂ → β₂ → ℝ} (hq : 0 < q) (hP : IsPMF P) {D₁ D₂ : ℝ}
    {R : ℝ × ℝ} (h : R ∈ kaspiRegion P spk d₁ d₂ D₁ D₂) {ε : ℝ} (hε : 0 < ε) :
    (R.1 + ε, R.2 + ε) ∈ kaspiInner P spk d₁ d₂ (D₁ + ε) (D₂ + ε) := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  exact exists_kaspiInner_of_mem_kaspiRegion hq hP h hε

/-- **Pages 21-30 and 21-31: the minimum sum rate of two-way lossless coding through a relay.** -/
theorem relay_sum_rate {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ} (hP : IsPMF P) :
    twrSumRate P = H[Prod.fst | Prod.snd ; P] / log 2 + H[Prod.snd | Prod.fst ; P] / log 2 +
      max (H[Prod.fst | Prod.snd ; P] / log 2) (H[Prod.snd | Prod.fst ; P] / log 2) :=
  twrSumRate_eq hP

end Aliases

end InfoTheory.ElGamalKim
