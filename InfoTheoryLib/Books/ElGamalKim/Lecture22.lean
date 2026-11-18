/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.CascadeComputing
public import InfoTheoryLib.Network.ComputeMAC
public import InfoTheoryLib.Network.ComputingGaussian
public import InfoTheoryLib.Network.TwoWayComputing

/-!
# El Gamal & Kim, Lecture 22: Communication for Computing

This file indexes the formalization of Lecture 22 of [elgamal2010]. We prove Yamamoto's Theorem 1,
the Orlitsky–Roche theorem with conditional graph entropy, the bounds for distributed computing with
the theorem of Körner and Marton, the `q`-round regions of Theorems 4 and 5, the lossless region of
the cascade, and the capacity for computing over a modulo-2 sum MAC, which shows that separation is
suboptimal. For the Gaussian problems, whose coding theorems need continuous sources, we prove the
formulas. In particular, we prove that the second inequality of Theorem 7 is false.

## Conventions

* **Rates.** Rates are in bits, with `2 ^ ⌊n R⌋` indices for sources, and informations are in nats.
* **Distortions.** A distortion of a function `Z = g(X, Y)` is a special case of a distortion
  `e((x, y), ẑ)`, which is what we use: take `e((x, y), ẑ) = d(g(x, y), ẑ)`.
* **Nodes.** The notes call `Z₁` the function estimated at node 1. In the library the estimate at
  node 2 comes first, as in Lecture 21: `g₁` and `d₁` here are `Z₂` and `d₂` of the notes.
* **Characteristic graph.** Its nodes are all of `𝒳`, not only the support of `X`: a letter of
  probability `0` is isolated, and this does not change the graph entropy.
* **Sources over the MAC.** The sources are binary, uniform and independent, with `k = ⌊n r⌋`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Computing with side information (pages 22-3 to 22-9)
* The codes: `WZCode.funDistortion`, `WZCode.funErrProb`, `IsAchievableFunBits`, `rateFunBits`,
  `IsLosslessFunBits` (`RateDistortion.SideInfoFunction`).
* **Theorem 1:** `funCost`, `funRD`, `exists_funRD_eq`, `isAchievableFunBits_of_lt`,
  `WZCode.exists_fun_kernel_le`, `rateFunBits_eq`, here `theorem_22_1`.
* The lossless rate of page 22-6: `IsFunOf`, `funLosslessRate`, `exists_funLosslessRate_eq`,
  `isLosslessFunBits_of_lt`, `losslessFunBits_eq`; the bounds of page 22-5:
  `condEntropy_le_funLosslessRate`, `funLosslessRate_le_condEntropy`.
* Graphs: `IsMaxIndep`, `maxIndepSets`, `IsGraphKernel`, `condGraphEntropy`, `graphEntropy`,
  `exists_condGraphEntropy_eq`, `condGraphEntropy_bot`, `condGraphEntropy_top`, `charGraph`
  (`RateDistortion.GraphEntropy`). The graph of page 22-7: `figureGraph`, `maxIndepSets_figureGraph`
  (here).
* **The Orlitsky–Roche theorem:** `funLosslessRate_eq_condGraphEntropy` (the appendix),
  `losslessFunBits_eq_condGraphEntropy`, here `orlitsky_roche`.
* The example of page 22-5: `selectLaw`, `select_charGraph`, `select_rate` (here): the rate is `m`
  bits, for `m` bits and a uniform index at the decoder.

### Distributed computing (pages 22-10 to 22-13)
* `DistFunCode`, `IsAchievableDistFun`, `distFunRegion` (`Network.DistFun`).
* The inner bound: `swRegionBits_subset_distFunRegion`. The outer bounds:
  `condEntropy_le_of_mem_distFunRegion`, `distFunRegion_subset_distFunOuter`.
* **Körner and Marton:** `exists_binMatrix_le`, `linearCode`, `exists_linearCode_le`,
  `isAchievableDistFun_add`, `distFunRegion_add_eq`; the counting: `card_mulVec_eq`
  (`ForMathlib.BinaryMatrix`); for a DSBS: `dsbsZ`, `distFunRegion_dsbsZ` (here).

### The `μ`-sum problem (pages 22-14 to 22-18)
* `muS₁`, `muS₂`, `muDelta`, `muA₁`, `muA₂`, `muSum_a_solves`, `muSum_a_sq`, `muDelta_eq`,
  `muSum_mse`, `muSum_normalization` (`Network.ComputingGaussian`).
* **Theorem 3,** as a formula: `muSumRegion`, `muSumRegion_eq_ceoRegion`, here `theorem_22_3`.

### Two-way computing (pages 22-19 to 22-23)
* **Theorem 4:** the theorem of Kaspi of Lecture 21 holds with distortions of both sources:
  `KaspiCode`, `kaspiRegion`, `kaspiInner`, `kaspiInner_subset_kaspiRegion`,
  `exists_kaspiInner_of_mem_kaspiRegion`, here `theorem_22_4_inner` and `theorem_22_4_converse`.
* **Theorem 5:** `KaspiCode.errProb₁`, `KaspiCode.errProb₂`, `IsLosslessKaspi`,
  `kaspiLosslessRegion`, `KBook.errProb₁_le`, `KBook.errProb₂_le`, `isLosslessKaspi_of_lt`,
  `exists_law_of_mem_kaspiLosslessRegion` (`Network.TwoWayComputing`), here `theorem_22_5_inner` and
  `theorem_22_5_converse`.
* The example of page 22-22: the rate of one round, `productLaw`, `product_rate` (here), and the sum
  rate of two rounds, `exists_two_round_lt` (here).

### Cascade computing (pages 22-24 to 22-29)
* `CascadeCode`, `IsLosslessCascade`, `cascadeRegion`, `isLosslessCascade_of_lt`,
  `IsLosslessCascade.entropy_le`, `cascadeRegion_eq` (`Network.CascadeComputing`).
* The Gaussian example: `forwardingSum`, `forwardingSum_ge`, `forwardingSum_opt`, `localSum`,
  `localOptD`, `localSum_ge`, `localSum_opt`, `localOpt_lt_forwardOpt`
  (`Network.ComputingGaussian`).

### Distributed lossy averaging (pages 22-30 to 22-32)
* **Theorem 6:** the Jensen step, `averaging_sum_ge`, here `theorem_22_6`.
* **Theorem 7:** `averaging_zero_rate`, `averaging_avg_distortion`; the counterexample,
  `printed_averaging_counterexample`; the correct form, `averaging_upper_le_add`.

### Computing over a MAC (pages 22-33 to 22-35)
* `ComputeCode`, `ComputeCode.errProb`, `IsComputable`, `ComputeCode.fano`, `IsComputable.le`,
  `linearCompute`, `exists_computeCode_le`, `isComputable_of_lt` (`Network.ComputeMAC`).
* Separation: `macSumChannel`, `sum_le_of_mem_macCapacityRegionBits`,
  `mem_macCapacityRegionBits_diag_iff`, `exists_isComputable_not_separate`.

## Differences from the notes

* **Theorem 1.** We prove the bound `|𝒰| ≤ |𝒳| + 1`, as in Lecture 12.
* **Körner and Marton.** The theorem is proved for any law of binary `(X₁, X₂)`, and not only for a
  DSBS. The two encoders use the same matrix, with `k = ⌊n min(R₁, R₂)⌋` rows.
* **Computing over a MAC.** The notes use two matrices `A` and `B`. For uniform sources, the matrix
  `B` alone is enough.
* **Theorem 5.** The converse has a Hamming distortion of at most `ε`, instead of
  `H(g | U^q, X) = 0`, because the library has no bound on the cardinalities of the `Uₗ`. The rounds
  may be in any order.

## Not formalized

* The Gaussian coding theorems: Theorem 3 as a statement about codes, the examples of pages 22-4 and
  22-20, the operational meaning of Theorems 6 and 7, and the Gaussian cascade.
* The necessary and sufficient conditions for the tightness of the inner bound on page 22-11 [5].
* The lossy cascade: the cutset bound of page 22-24, and the local computing, forwarding and
  combined inner bounds. Only the lossless region is proved.
* The values of the graph entropies of the two examples with a single edge on pages 22-7 and 22-8.
* The rates of the examples of pages 22-22 and 22-23 as instances of Theorem 5: for the two-round
  example, we prove the rate of one round and the inequality `H(p) + p < 1`, and not that
  `(H(p), p)` is the rate pair of the law. The three-round example of page 22-23 was checked
  numerically only.
* The results cited from the literature: the Berger–Tung bound for `μ₁ μ₂ < 0`, communication
  complexity, gossip.

## Issues in the notes

* **Page 22-32: the second inequality of Theorem 7 is false.** The notes claim
  `2 (N - 1) R(2 (N - 1)² / (N³ D)) ≤ 2 N R((N - 1) / (N² D))`, so that the cutset bound is
  achievable within a factor of 2. For `N = 3` and `D = 1 / 5 < 2 / 9` this reads
  `2 log (40 / 27) ≤ 3 log (10 / 9)`, which is false (`printed_averaging_counterexample`). Near
  `D = (N - 1) / N²`, the right side tends to `0` and the left side does not. The correct statement
  has an additive gap of `(N - 1) log 2` (`averaging_upper_le_add`).
* **Page 22-41: a gap in the proof of the Orlitsky–Roche theorem.** The set
  `w(u) = {x : p(u, x) > 0}` is shown to be independent, and the notes conclude that it is maximally
  independent, which need not hold. It must be extended to a maximally independent set
  (`condGraphEntropy_le_sideRate`).
* **Page 22-43.** The bound of Theorem 6 is written `… = R((N - 1) / (N² D))`, without the factor
  `N`, and with `Dᵢ` for `Dⱼ` under the sum. Confirmed against the PDF.
* **Pages 22-43 to 22-45.** `I(Xⱼ; X̂ⱼ) = R(D')` and `R = 2 (N - 1) R(D')` should have `R(1 / D')`.
  Confirmed against the PDF.
* **Page 22-19.** The inner bound has `R₂ > I(X₂; U₁ | X₁)`, which should be `U₂`, and `ẑ₁(u₁, x₂)`,
  `ẑ₂(u₂, x₁)`, which should be `ẑ₁(u₂, x₁)`, `ẑ₂(u₁, x₂)`. Confirmed against the PDF.
* **Page 22-20.** The product in Theorem 4 has no upper limit, and "the cardinality of `q`" should
  be of the `Uₗ`. The example mixes `(X, Y)` with `(X₁, X₂)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

universe u

/-! ### The graph of page 22-7 -/

section Figure

/-- **Lecture 22, page 22-7.** The edges of the figure, with the node `k` of the notes as
`k - 1`. -/
def figureAdj (a b : Fin 6) : Bool :=
  match a.val, b.val with
  | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 1, 3 | 3, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 5 | 5, 4 => true
  | _, _ => false

/-- **Lecture 22, page 22-7.** The graph of the figure. -/
def figureGraph : SimpleGraph (Fin 6) where
  Adj a b := figureAdj a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

/-- A finite set is maximally independent iff it is independent and every other node has a neighbor
in it. -/
lemma isMaxIndep_iff {α : Type*} (G : SimpleGraph α) (w : Finset α) :
    IsMaxIndep G w ↔ (∀ x ∈ w, ∀ y ∈ w, ¬ G.Adj x y) ∧ ∀ x, x ∉ w → ∃ y ∈ w, G.Adj x y := by
  classical
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun x hx y hy hadj => h₁ hx hy hadj.ne hadj, fun x hx => ?_⟩
    by_contra hne
    push Not at hne
    have hind : G.IsIndepSet ((insert x w : Finset α) : Set α) := by
      intro a ha b hb hab
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hne b hb
      · exact fun h => hne a ha h.symm
      · exact h₁ ha hb hab
    have := h₂ _ hind (subset_insert x w)
    exact hx (this ▸ mem_insert_self x w)
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun a ha b hb _ => h₁ a ha b hb, fun w' hw' hsub => ?_⟩
    refine (subset_antisymm hsub ?_).symm
    intro x hx
    by_contra hn
    obtain ⟨y, hy, hadj⟩ := h₂ x hn
    exact hw' hx (hsub hy) hadj.ne hadj

set_option maxRecDepth 100000 in
/-- **Lecture 22, page 22-7.** The maximally independent sets of the figure:
`Γ(G) = {{1, 3, 5}, {1, 3, 6}, {1, 4, 6}, {2, 5}, {2, 6}}`, which the notes ask to check. -/
theorem maxIndepSets_figureGraph :
    maxIndepSets figureGraph = {{0, 2, 4}, {0, 2, 5}, {0, 3, 5}, {1, 4}, {1, 5}} := by
  ext w
  rw [mem_maxIndepSets, isMaxIndep_iff]
  change ((∀ x ∈ w, ∀ y ∈ w, ¬ figureAdj x y = true) ∧
    ∀ x, x ∉ w → ∃ y ∈ w, figureAdj x y = true) ↔ _
  revert w
  decide

end Figure

/-! ### The example of page 22-5 -/

section Select

variable {m : ℕ}

/-- **Lecture 22, page 22-5.** `X = (V₁, …, V_m)` is uniform, and `Y` is a uniform index. -/
def selectLaw (m : ℕ) : (Fin m → Bool) × Fin m → ℝ := uniformPMF _

/-- The function `g(x, y) = x_y`. -/
def selectFun (m : ℕ) (z : (Fin m → Bool) × Fin m) : Bool := z.1 z.2

lemma selectLaw_ne_zero [NeZero m] (z : (Fin m → Bool) × Fin m) : selectLaw m z ≠ 0 := by
  have : Nonempty ((Fin m → Bool) × Fin m) := ⟨z⟩
  simp [selectLaw, uniformPMF, NeZero.ne m]

/-- **Lecture 22, page 22-5.** Any two distinct strings differ in some position, so the
characteristic graph is complete. -/
theorem select_charGraph [NeZero m] : charGraph (selectLaw m) (selectFun m) = ⊤ := by
  ext x x'
  simp only [SimpleGraph.top_adj]
  refine ⟨fun h => h.1, fun hne => ⟨hne, ?_⟩⟩
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  exact ⟨y, selectLaw_ne_zero _, selectLaw_ne_zero _, hy⟩

/-- **Lecture 22, page 22-5.** The optimal rate for computing `V_Y` is `m` bits, whereas
`H(V_Y | Y)` is `1` bit: the upper bound `H(X | Y)` of page 22-5 is tight. -/
theorem select_rate [NeZero m] :
    sInf {R | IsLosslessFunBits (selectLaw m) (selectFun m) R} = m := by
  classical
  have hP : IsPMF (selectLaw m) := uniformPMF_isPMF
  have hl := log_pos one_lt_two
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [losslessFunBits_eq_condGraphEntropy hP, select_charGraph, condGraphEntropy_top hP,
    condEntropy_eq_sub hP]
  have h₁ : H[pair Prod.snd Prod.fst ; selectLaw m] = m * log 2 + log m := by
    have e := entropyRV_eq_of_injective (selectLaw m) (Y := pair Prod.snd Prod.fst) (X := id)
      Prod.swap Prod.swap_injective fun _ => rfl
    rw [e, entropyRV, dist_id, selectLaw, entropy_uniformPMF]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rw [log_mul (by positivity) hm.ne', log_pow]
  have h₂ : H[Prod.snd ; selectLaw m] = log m := by
    have hd : dist (selectLaw m) Prod.snd = uniformPMF (Fin m) := by
      funext y
      rw [dist, Fintype.sum_prod_type]
      refine (sum_congr rfl fun x _ => sum_eq_single y (fun y' _ h => ?_) (by simp)).trans ?_
      · simp [h]
      · simp only [selectLaw, uniformPMF, ite_true, sum_const, card_univ, Fintype.card_prod,
          Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp
    rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_fin]
  rw [h₁, h₂, add_sub_cancel_right, mul_div_cancel_right₀ _ hl.ne']

end Select

/-! ### The example of page 22-22 -/

section Product

/-- **Lecture 22, page 22-22.** `X₂ ∼ Bern(1 / 2)` at the encoder, and `X₁ ∼ Bern(p)` at the
decoder, independent of `X₂`. -/
def productLaw (p : ℝ) (z : Bool × Bool) : ℝ := 1 / 2 * bernoulliPMF p z.2

/-- The function `Z = X₁ · X₂`. -/
def productFun (z : Bool × Bool) : Bool := z.1 && z.2

lemma productLaw_isPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsPMF (productLaw p) := by
  refine ⟨fun z => mul_nonneg (by norm_num) ?_, ?_⟩
  · simp only [bernoulliPMF]
    split_ifs <;> linarith
  · simp only [productLaw, bernoulliPMF, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    ring

/-- **Lecture 22, page 22-22.** For `p > 0`, one round of communication from node 2 to node 1 needs
a rate of `1` bit. -/
theorem product_rate {p : ℝ} (h0 : 0 < p) (h1 : p ≤ 1) :
    sInf {R | IsLosslessFunBits (productLaw p) productFun R} = 1 := by
  classical
  have hP := productLaw_isPMF h0.le h1
  have hl := log_pos one_lt_two
  have hG : charGraph (productLaw p) productFun = ⊤ := by
    ext x x'
    simp only [SimpleGraph.top_adj]
    refine ⟨fun h => h.1, fun hne => ⟨hne, true, ?_, ?_, ?_⟩⟩
    · simp [productLaw, bernoulliPMF, h0.ne']
    · simp [productLaw, bernoulliPMF, h0.ne']
    · simpa [productFun] using hne
  rw [losslessFunBits_eq_condGraphEntropy hP, hG, condGraphEntropy_top hP]
  have hdist : dist (productLaw p) Prod.fst = uniformPMF Bool := by
    funext x
    simp only [dist, productLaw, bernoulliPMF, uniformPMF, Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.card_bool]
    cases x <;> norm_num <;> ring
  have hind : IndepRV (productLaw p) Prod.fst Prod.snd := by
    intro x y
    rw [hdist]
    simp only [dist, pair, productLaw, bernoulliPMF, uniformPMF, Fintype.sum_prod_type,
      Fintype.sum_bool, Fintype.card_bool]
    cases x <;> cases y <;> norm_num <;> ring
  rw [(condEntropy_eq_entropy_iff hP _ _).2 hind, entropyRV, hdist, entropy_uniformPMF]
  simp [hl.ne']

/-- **Lecture 22, page 22-22.** The sum rate `H(p) + p` of the two-round scheme is below the rate
`1` of one round, for `p` small enough: interaction reduces the communication. -/
theorem exists_two_round_lt : ∃ p₀ > 0, ∀ p, 0 < p → p < p₀ → binEntropy p / log 2 + p < 1 := by
  have hc : Continuous fun p : ℝ => binEntropy p / log 2 + p :=
    (binEntropy_continuous.div_const _).add continuous_id
  have h := (hc.tendsto 0).eventually (gt_mem_nhds (by simp : (fun p : ℝ =>
    binEntropy p / log 2 + p) 0 < 1))
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ε, hε, fun p h0 hp => hb ?_⟩
  simp [abs_of_pos h0, hp]

end Product

/-! ### The doubly symmetric binary source -/

section DSBS

/-- `Bern(p)` on the field with two elements. -/
def bernZ (p : ℝ) (a : ZMod 2) : ℝ := if a = 0 then 1 - p else p

/-- **Lecture 22, page 22-12.** The DSBS(`p`) on the field with two elements: `X₁ ∼ Bern(1 / 2)` and
`Z = X₁ ⊕ X₂ ∼ Bern(p)` are independent. -/
def dsbsZ (p : ℝ) (z : ZMod 2 × ZMod 2) : ℝ := 1 / 2 * bernZ p (z.1 + z.2)

private lemma sum_zmod_two (f : ZMod 2 → ℝ) : ∑ a, f a = f 0 + f 1 := Fin.sum_univ_two f

private lemma one_add_one_zmod : (1 : ZMod 2) + 1 = 0 := by decide

private lemma one_ne_zero_zmod : (1 : ZMod 2) ≠ 0 := by decide

lemma dsbsZ_isPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsPMF (dsbsZ p) := by
  refine ⟨fun z => mul_nonneg (by norm_num) ?_, ?_⟩
  · simp only [bernZ]
    split_ifs <;> linarith
  · simp only [dsbsZ, bernZ, Fintype.sum_prod_type, sum_zmod_two, add_zero, zero_add,
      one_add_one_zmod, one_ne_zero_zmod, ite_true, ite_false]
    ring

/-- The law of `Z = X₁ ⊕ X₂` is `Bern(p)`. -/
lemma dist_addZ_dsbsZ (p : ℝ) : dist (dsbsZ p) addZ = bernZ p := by
  have h0 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  funext a
  rcases h0 a with rfl | rfl <;>
    simp [dist, dsbsZ, bernZ, addZ, Fintype.sum_prod_type, sum_zmod_two, one_add_one_zmod] <;> ring

/-- `H(Bern(p)) = H(p)`. -/
lemma entropy_bernZ (p : ℝ) : entropy (bernZ p) = binEntropy p := by
  rw [entropy_eq_sum_negMulLog, binEntropy_eq_negMulLog_add_negMulLog_one_sub, sum_zmod_two]
  simp [bernZ, add_comm]

/-- `X₂` is uniform. -/
lemma dist_snd_dsbsZ (p : ℝ) (b : ZMod 2) : dist (dsbsZ p) Prod.snd b = 1 / 2 := by
  have h0 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h0 b with rfl | rfl <;>
    simp [dist, dsbsZ, bernZ, Fintype.sum_prod_type, sum_zmod_two, one_add_one_zmod] <;> ring

/-- `X₁` is uniform. -/
lemma dist_fst_dsbsZ (p : ℝ) (b : ZMod 2) : dist (dsbsZ p) Prod.fst b = 1 / 2 := by
  have h0 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h0 b with rfl | rfl <;>
    simp [dist, dsbsZ, bernZ, Fintype.sum_prod_type, sum_zmod_two, one_add_one_zmod] <;> ring

/-- **Lecture 22, page 22-12.** For a DSBS(`p`), the optimal rate region for computing `X₁ ⊕ X₂` is
`R₁ ≥ H(p)`, `R₂ ≥ H(p)`, in bits: the outer bound is tight. -/
theorem distFunRegion_dsbsZ {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    distFunRegion (dsbsZ p) addZ = {R | binEntropy p / log 2 ≤ R.1 ∧ binEntropy p / log 2 ≤ R.2} :=
      by
  classical
  have hP := dsbsZ_isPMF h0 h1
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h₁ : H[addZ | Prod.snd ; dsbsZ p] = entropy (dist (dsbsZ p) addZ) := by
    refine (condEntropy_eq_entropy_iff hP _ _).2 fun a b => ?_
    rw [dist_snd_dsbsZ, dist_addZ_dsbsZ]
    rcases hz a with rfl | rfl <;> rcases hz b with rfl | rfl <;>
      simp [dist, pair, dsbsZ, bernZ, addZ, Fintype.sum_prod_type, sum_zmod_two, one_add_one_zmod]
        <;> ring
  have h₂ : H[addZ | Prod.fst ; dsbsZ p] = entropy (dist (dsbsZ p) addZ) := by
    refine (condEntropy_eq_entropy_iff hP _ _).2 fun a b => ?_
    rw [dist_fst_dsbsZ, dist_addZ_dsbsZ]
    rcases hz a with rfl | rfl <;> rcases hz b with rfl | rfl <;>
      simp [dist, pair, dsbsZ, bernZ, addZ, Fintype.sum_prod_type, sum_zmod_two, one_add_one_zmod]
        <;> ring
  rw [distFunRegion_add_eq hP h₁ h₂, dist_addZ_dsbsZ, entropy_bernZ]

end DSBS

/-! ### The results by their numbers -/

section Aliases

/-- **Theorem 1, page 22-4.** -/
theorem theorem_22_1 {α γ β : Type*} [Fintype α] [Fintype γ] [Finite β] [Nonempty β]
    {P : α × γ → ℝ} {e : α × γ → β → ℝ} (hP : IsPMF P) (he : ∀ z b, 0 ≤ e z b) {D : ℝ}
    (hD : minDistortion P e ≤ D) : rateFunBits P e D = funRD P e D / log 2 :=
  rateFunBits_eq hP he hD

/-- **The Orlitsky–Roche theorem, page 22-9.** -/
theorem orlitsky_roche {α γ β : Type*} [Fintype α] [Fintype γ] [Finite β] {P : α × γ → ℝ}
    (hP : IsPMF P) (g : α × γ → β) :
    sInf {R | IsLosslessFunBits P g R} = condGraphEntropy (charGraph P g) P / log 2 :=
  losslessFunBits_eq_condGraphEntropy hP g

/-- **Theorem 3, page 22-15,** as a formula: the region is that of the CEO problem. -/
theorem theorem_22_3 (s₁ s₂ δ D : ℝ) :
    muSumRegion s₁ s₂ δ D = ceoRegion 1 (1 / s₁) (1 / s₂) (D + δ) :=
  muSumRegion_eq_ceoRegion s₁ s₂ δ D

/-- **Theorem 4, page 22-20: the inner bound,** for any order of the speakers. -/
theorem theorem_22_4_inner {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ : Type*} [Finite β₁]
    [Finite β₂] [Nonempty β₁] [Nonempty β₂] {q : ℕ} {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ}
    {d₁ : α₁ × α₂ → β₁ → ℝ} {d₂ : α₁ × α₂ → β₂ → ℝ} (hP : IsPMF P) (hd₁ : ∀ x y, 0 ≤ d₁ x y)
    (hd₂ : ∀ x y, 0 ≤ d₂ x y) (D₁ D₂ : ℝ) :
    kaspiInner P spk d₁ d₂ D₁ D₂ ⊆ kaspiRegion P spk d₁ d₂ D₁ D₂ :=
  kaspiInner_subset_kaspiRegion hP hd₁ hd₂ D₁ D₂

/-- **Theorem 4, page 22-20: the converse,** with `ε`, as in Lecture 21. -/
theorem theorem_22_4_converse {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ : Type*}
    [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂] {q : ℕ} {spk : Fin q → Bool}
    {P : α₁ × α₂ → ℝ} {d₁ : α₁ × α₂ → β₁ → ℝ} {d₂ : α₁ × α₂ → β₂ → ℝ} (hq : 0 < q) (hP : IsPMF P)
    {D₁ D₂ : ℝ} {R : ℝ × ℝ} (h : R ∈ kaspiRegion P spk d₁ d₂ D₁ D₂) {ε : ℝ} (hε : 0 < ε) :
    (R.1 + ε, R.2 + ε) ∈ kaspiInner P spk d₁ d₂ (D₁ + ε) (D₂ + ε) :=
  exists_kaspiInner_of_mem_kaspiRegion hq hP h hε

/-- **Theorem 5, page 22-21: achievability.** -/
theorem theorem_22_5_inner {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ υ : Type*} [Fintype υ]
    [Nonempty υ] {q : ℕ} {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ} {μ : α₁ × α₂ × (Fin q → υ) → ℝ}
    (hP : IsPMF P) (hμ : IsKaspiLaw P spk μ) {g₁ : α₁ × α₂ → β₁} {g₂ : α₁ × α₂ → β₂}
    {f₁ : (Fin q → υ) → α₂ → β₁} {f₂ : (Fin q → υ) → α₁ → β₂}
    (hf₁ : ∀ z, μ z ≠ 0 → f₁ z.2.2 z.2.1 = g₁ (z.1, z.2.1))
    (hf₂ : ∀ z, μ z ≠ 0 → f₂ z.2.2 z.1 = g₂ (z.1, z.2.1)) {R : ℝ × ℝ}
    (hR₁ : I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 | fun z => z.2.1 ; μ] <
      R.1 * log 2)
    (hR₂ : I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 | fun z => z.1 ; μ] <
      R.2 * log 2) : IsLosslessKaspi P spk g₁ g₂ R :=
  isLosslessKaspi_of_lt hP hμ hf₁ hf₂ hR₁ hR₂

open Classical in
/-- **Theorem 5, page 22-21: the converse,** with a small Hamming distortion. -/
theorem theorem_22_5_converse {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ : Type*}
    [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂] {q : ℕ} {spk : Fin q → Bool}
    {P : α₁ × α₂ → ℝ} (hq : 0 < q) (hP : IsPMF P) {g₁ : α₁ × α₂ → β₁} {g₂ : α₁ × α₂ → β₂}
    {R : ℝ × ℝ} (h : R ∈ kaspiLosslessRegion P spk g₁ g₂) {ε : ℝ} (hε : 0 < ε) :
    (R.1 + ε, R.2 + ε) ∈ kaspiInner P spk (fun z b => hammingDistortion (g₁ z) b)
      (fun z b => hammingDistortion (g₂ z) b) (0 + ε) (0 + ε) :=
  exists_law_of_mem_kaspiLosslessRegion hq hP h hε

/-- **Theorem 6, page 22-31,** the step from the bound of each node to the bound of the network. -/
theorem theorem_22_6 {N : ℕ} (hN : 0 < N) {c D : ℝ} (hc : 0 < c) {Dj : Fin N → ℝ}
    (hDj : ∀ j, 0 < Dj j) (hD : (∑ j, Dj j) / N ≤ D) :
    N * qgR (c / D) ≤ ∑ j, qgR (c / Dj j) :=
  averaging_sum_ge hN hc hDj hD

end Aliases

end InfoTheory.ElGamalKim
