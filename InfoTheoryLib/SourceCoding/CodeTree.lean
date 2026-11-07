/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.Probability.SupportMixture
public import InfoTheoryLib.SourceCoding.Huffman

/-!
# The code tree of a prefix code and its redundancy

The nodes of the code tree of a `D`-ary prefix code are lists over the code alphabet. The leaves are
the codewords, and the internal nodes are the proper prefixes of the codewords. The redundancy of
the code is the sum over the internal nodes of a local redundancy, which depends only on the
probabilities of the branches at the node.

## Main definitions

* `codeRedundancy p C`: the redundancy `R = L - H_D(X)`.
* `internalNodes C`: the set `I` of the internal nodes.
* `reachProb p C k`: the reaching probability `q_k` of the node `k`.
* `branchProb p C k j`: the branching probability `p̃_{k,j}`.
* `nodeEntropy p C k`: the conditional entropy `h_k` of the node `k`.
* `localRedundancy p C k`: the local redundancy `r_k = q_k (1 - h_k)`.

## Main statements

* `entropyBase_eq_sum_reachProb_mul_nodeEntropy`: `H_D(X) = ∑_{k ∈ I} q_k h_k`.
* `expectedLength_eq_sum_reachProb`: `L = ∑_{k ∈ I} q_k`.
* `codeRedundancy_eq_sum_localRedundancy`: the local redundancy theorem, `R = ∑_{k ∈ I} r_k`.
* `codeRedundancy_nonneg`, `codeRedundancy_eq_zero_iff`: `R ≥ 0`, with equality iff all the
  internal nodes are balanced.
* `exists_prefixCode_eq_entropyBase_iff`: a prefix code achieves the entropy bound iff the
  distribution is `D`-adic.
* `length_le_of_isOptimal`: an optimal code assigns shorter codewords to larger probabilities.
* `exists_optimal_prefixCode_siblings`: there is an optimal binary code in which the two smallest
  probabilities have sibling codewords.
* `expectedLength_huffmanCode_lt`: `L < H₂(X) + 1` for a binary Huffman code.
* `tendsto_entropyBase_add_one_sub_minExpectedLength`: the bound `H_D(X) + 1` cannot be improved.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 4.3
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {X α : Type*} [Fintype X] [Fintype α] [DecidableEq α] {C : X → List α}

/-- **Definition 4.7.** The redundancy `R = L - H_D(X)` of a `D`-ary code. -/
def codeRedundancy (p : X → ℝ) (C : X → List α) : ℝ :=
  expectedLength p C - entropyBase (Fintype.card α) p

/-- The internal nodes of the code tree: the proper prefixes of the codewords. -/
def internalNodes (C : X → List α) : Finset (List α) :=
  univ.biUnion fun x => (C x).inits.toFinset.erase (C x)

/-- The reaching probability `q_k` of a node: the sum of the probabilities of the leaves descending
from it. -/
def reachProb (p : X → ℝ) (C : X → List α) (k : List α) : ℝ :=
  ∑ x, if k <+: C x then p x else 0

/-- The branching probability `p̃_{k,j}` that the `j`th branch of the node `k` is taken. -/
def branchProb (p : X → ℝ) (C : X → List α) (k : List α) (j : α) : ℝ :=
  reachProb p C (k ++ [j])

/-- **(4.53)** The conditional entropy `h_k` of a node, in base `D`. -/
def nodeEntropy (p : X → ℝ) (C : X → List α) (k : List α) : ℝ :=
  entropyBase (Fintype.card α) fun j => branchProb p C k j / reachProb p C k

/-- **(4.65)** The local redundancy `r_k = q_k (1 - h_k)` of a node. -/
def localRedundancy (p : X → ℝ) (C : X → List α) (k : List α) : ℝ :=
  reachProb p C k * (1 - nodeEntropy p C k)

omit [Fintype α] in
lemma mem_internalNodes {C : X → List α} {k : List α} :
    k ∈ internalNodes C ↔ ∃ x, k <+: C x ∧ k ≠ C x := by
  simp only [internalNodes, mem_biUnion, mem_univ, true_and, mem_erase, List.mem_toFinset,
    List.mem_inits]
  exact exists_congr fun x => and_comm

omit [Fintype X] [Fintype α] [DecidableEq α] in
/-- An internal node of a prefix code is not a codeword. -/
lemma IsPrefixCode.ne_of_proper_prefix {C : X → List α} (hC : IsPrefixCode C) {k : List α} {y : X}
    (hk : k <+: C y) (hne : k ≠ C y) (x : X) : k ≠ C x := by
  rintro rfl
  exact hne (by rw [hC x y hk])

omit [Fintype α] in
lemma IsPrefixCode.ne_of_mem_internalNodes {C : X → List α} (hC : IsPrefixCode C) {k : List α}
    (hk : k ∈ internalNodes C) (x : X) : k ≠ C x := by
  obtain ⟨y, h₁, h₂⟩ := mem_internalNodes.1 hk
  exact hC.ne_of_proper_prefix h₁ h₂ x

omit [Fintype X] [Fintype α] [DecidableEq α] in
/-- The prefixes of a list are distinct. -/
lemma nodup_inits_list (l : List α) : l.inits.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.inits_cons, List.nodup_cons]
    refine ⟨by simp, ih.map fun _ _ h => (List.cons.inj h).2⟩

omit [Fintype X] [Fintype α] in
/-- A list has as many proper prefixes as its length. -/
lemma card_erase_inits (l : List α) : #(l.inits.toFinset.erase l) = l.length := by
  rw [card_erase_of_mem (by simp), List.toFinset_card_of_nodup (nodup_inits_list l),
    List.length_inits]
  rfl

omit [Fintype α] in
/-- **Lemma 4.19.** `L = ∑_{k ∈ I} q_k`. -/
theorem expectedLength_eq_sum_reachProb (hC : IsPrefixCode C) (p : X → ℝ) :
    expectedLength p C = ∑ k ∈ internalNodes C, reachProb p C k := by
  simp only [reachProb, expectedLength]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  rw [← card_erase_inits (C x)]
  congr 1
  ext k
  simp only [mem_filter, mem_erase, List.mem_toFinset, List.mem_inits]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨mem_internalNodes.2 ⟨x, h₂, h₁⟩, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨hC.ne_of_mem_internalNodes h₁ x, h₂⟩

omit [Fintype X] [Fintype α] [DecidableEq α] in
lemma prefix_of_append_singleton_prefix {k l : List α} {j : α} (h : k ++ [j] <+: l) : k <+: l :=
  (List.prefix_append k [j]).trans h

omit [Fintype X] in
/-- The children of a proper prefix `k` of `l` include exactly one prefix of `l`. -/
lemma sum_ite_append_prefix (k l : List α) (v : ℝ) :
    (∑ j : α, if k ++ [j] <+: l then v else 0) = if k <+: l ∧ k ≠ l then v else 0 := by
  by_cases h : k <+: l ∧ k ≠ l
  · obtain ⟨⟨t, rfl⟩, hne⟩ := h
    cases t with
    | nil => simp at hne
    | cons a t =>
      have e : ∀ j : α, k ++ [j] <+: k ++ a :: t ↔ j = a := fun j => by
        rw [List.prefix_append_right_inj]
        simp
      simp only [e]
      simp [hne]
  · simp only [h, ↓reduceIte]
    refine sum_eq_zero fun j _ => ite_eq_right_iff.2 fun hj =>
      absurd ⟨prefix_of_append_singleton_prefix hj, ?_⟩ h
    rintro rfl
    have := hj.length_le
    simp at this

/-- **(4.51)** `q_k = ∑_j p̃_{k,j}` at an internal node. -/
theorem sum_branchProb (hC : IsPrefixCode C) (p : X → ℝ) {k : List α} (hk : k ∈ internalNodes C) :
    ∑ j, branchProb p C k j = reachProb p C k := by
  simp only [branchProb, reachProb]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_ite_append_prefix]
  simp [hC.ne_of_mem_internalNodes hk x]

omit [Fintype α] in
lemma reachProb_nonneg {p : X → ℝ} (hp : IsPMF p) (C : X → List α) (k : List α) :
    0 ≤ reachProb p C k :=
  sum_nonneg fun x _ => by
    split_ifs
    exacts [hp.nonneg x, le_rfl]

omit [Fintype α] in
lemma branchProb_le {p : X → ℝ} (hp : IsPMF p) (C : X → List α) (k : List α) (j : α) :
    branchProb p C k j ≤ reachProb p C k :=
  sum_le_sum fun x _ => by
    by_cases h : k ++ [j] <+: C x
    · simp [h, prefix_of_append_singleton_prefix h]
    · simp only [h, ↓reduceIte]
      split_ifs
      exacts [hp.nonneg x, le_rfl]

omit [Fintype α] in
/-- The reaching probability of a leaf is the probability of its codeword. -/
lemma reachProb_codeword (hC : IsPrefixCode C) (p : X → ℝ) (x : X) :
    reachProb p C (C x) = p x := by
  rw [reachProb, sum_eq_single x
    (fun y _ hy => ite_eq_right_iff.2 fun h => absurd (hC x y h).symm hy)
    (fun h => absurd (mem_univ x) h)]
  simp

omit [Fintype α] in
/-- The reaching probability of the root is `1`. -/
lemma reachProb_nil {p : X → ℝ} (hp : IsPMF p) (C : X → List α) : reachProb p C [] = 1 := by
  simp [reachProb, hp.sum_eq_one]

/-- At an internal node, `q_k h_k log D = ∑_j -p̃_{k,j} log p̃_{k,j} + q_k log q_k`. -/
lemma reachProb_mul_nodeEntropy (hα : 2 ≤ Fintype.card α) (hC : IsPrefixCode C) {p : X → ℝ}
    (hp : IsPMF p) {k : List α} (hk : k ∈ internalNodes C) :
    reachProb p C k * nodeEntropy p C k * log (Fintype.card α) =
      ∑ j, negMulLog (branchProb p C k j) - negMulLog (reachProb p C k) := by
  have hlog : log (Fintype.card α) ≠ 0 :=
    (log_pos (by exact_mod_cast (by omega : 1 < Fintype.card α))).ne'
  set q := reachProb p C k with hq
  rw [nodeEntropy, entropyBase_eq_div, entropy_eq_sum_negMulLog]
  rcases (reachProb_nonneg hp C k).eq_or_lt with h0 | hpos
  · have hb : ∀ j, branchProb p C k j = 0 := fun j =>
      le_antisymm (h0 ▸ branchProb_le hp C k j) (reachProb_nonneg hp C _)
    rw [← hq] at h0
    simp [hb, ← h0]
  · have hne : q ≠ 0 := hpos.ne'
    have e : ∀ j, negMulLog (branchProb p C k j) =
        branchProb p C k j / q * negMulLog q + q * negMulLog (branchProb p C k j / q) := fun j => by
      rw [← negMulLog_mul, mul_div_cancel₀ _ hne]
    have hsum : ∑ j, branchProb p C k j / q = 1 := by
      rw [← sum_div, sum_branchProb hC p hk, ← hq, div_self hne]
    simp_rw [e]
    rw [sum_add_distrib, ← sum_mul, hsum, ← mul_sum]
    field_simp
    ring

/-- The children of the internal nodes are the internal nodes other than the root, the leaves, and
nodes of probability zero. -/
lemma sum_sum_negMulLog_child [Nontrivial X] (hC : IsPrefixCode C) (p : X → ℝ) :
    ∑ k ∈ internalNodes C, ∑ j, negMulLog (branchProb p C k j) =
      ∑ k ∈ (internalNodes C).erase [], negMulLog (reachProb p C k) + ∑ x, negMulLog (p x) := by
  let e : List α × α → List α := fun t => t.1 ++ [t.2]
  have he : Function.Injective e := fun a b h => by
    obtain ⟨h₁, h₂⟩ := List.append_singleton_inj.1 h
    exact Prod.ext h₁ h₂
  have h₁ : ∑ k ∈ internalNodes C, ∑ j, negMulLog (branchProb p C k j) =
      ∑ c ∈ (internalNodes C ×ˢ (univ : Finset α)).image e, negMulLog (reachProb p C c) := by
    rw [sum_image he.injOn, sum_product]
    rfl
  -- a nonempty proper prefix of a codeword, or a nonempty codeword, is a child of an internal node
  have hchild : ∀ l : List α, l ≠ [] → (∃ y, l <+: C y) →
      l ∈ (internalNodes C ×ˢ (univ : Finset α)).image e := by
    rintro l hl ⟨y, hy⟩
    refine mem_image.2 ⟨(l.dropLast, l.getLast hl), mem_product.2 ⟨mem_internalNodes.2
      ⟨y, (List.dropLast_prefix l).trans hy, fun h => ?_⟩, mem_univ _⟩,
      List.dropLast_append_getLast hl⟩
    have h₁ := hy.length_le
    have h₂ : l.dropLast.length = (C y).length := congrArg List.length h
    have h₃ : 0 < l.length := List.length_pos_iff.2 hl
    rw [List.length_dropLast] at h₂
    omega
  have hdisj : Disjoint ((internalNodes C).erase []) (univ.image C) :=
    disjoint_left.2 fun k hk hk' => by
      obtain ⟨x, -, rfl⟩ := mem_image.1 hk'
      exact hC.ne_of_mem_internalNodes (mem_of_mem_erase hk) x rfl
  have hsub : (internalNodes C).erase [] ∪ univ.image C ⊆
      (internalNodes C ×ˢ (univ : Finset α)).image e := by
    intro l hl
    rcases mem_union.1 hl with hl | hl
    · obtain ⟨y, hy, -⟩ := mem_internalNodes.1 (mem_of_mem_erase hl)
      exact hchild l (ne_of_mem_erase hl) ⟨y, hy⟩
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hl
      exact hchild _ (hC.ne_nil x) ⟨x, List.prefix_rfl⟩
  have hzero : ∀ c ∈ (internalNodes C ×ˢ (univ : Finset α)).image e,
      c ∉ (internalNodes C).erase [] ∪ univ.image C → negMulLog (reachProb p C c) = 0 := by
    intro c hc hnot
    obtain ⟨t, -, rfl⟩ := mem_image.1 hc
    have hq : reachProb p C (e t) = 0 := sum_eq_zero fun x _ =>
      ite_eq_right_iff.2 fun h => absurd ?_ hnot
    · simp [hq]
    · by_cases hx : e t = C x
      · exact mem_union_right _ (mem_image.2 ⟨x, mem_univ _, hx.symm⟩)
      · exact mem_union_left _ (mem_erase.2 ⟨by simp [e], mem_internalNodes.2 ⟨x, h, hx⟩⟩)
  rw [h₁, ← sum_subset hsub hzero, sum_union hdisj, sum_image hC.injective.injOn]
  congr 1
  exact sum_congr rfl fun x _ => by rw [reachProb_codeword hC]

/-- **Lemma 4.18.** `H_D(X) = ∑_{k ∈ I} q_k h_k`. -/
theorem entropyBase_eq_sum_reachProb_mul_nodeEntropy [Nontrivial X] (hα : 2 ≤ Fintype.card α)
    (hC : IsPrefixCode C) {p : X → ℝ} (hp : IsPMF p) :
    entropyBase (Fintype.card α) p =
      ∑ k ∈ internalNodes C, reachProb p C k * nodeEntropy p C k := by
  have hlog : log (Fintype.card α) ≠ 0 :=
    (log_pos (by exact_mod_cast (by omega : 1 < Fintype.card α))).ne'
  have hroot : ([] : List α) ∈ internalNodes C := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    exact mem_internalNodes.2 ⟨x, List.nil_prefix, (hC.ne_nil x).symm⟩
  refine mul_right_cancel₀ hlog ?_
  rw [sum_mul, sum_congr rfl fun k hk => reachProb_mul_nodeEntropy hα hC hp hk, sum_sub_distrib,
    sum_sum_negMulLog_child hC p, ← add_sum_erase _ _ hroot, reachProb_nil hp, negMulLog_one,
    entropyBase_eq_div, entropy_eq_sum_negMulLog, div_mul_cancel₀ _ hlog]
  ring

/-- **Theorem 4.20 (Local Redundancy Theorem).** `R = ∑_{k ∈ I} r_k`, (4.66). -/
theorem codeRedundancy_eq_sum_localRedundancy [Nontrivial X] (hα : 2 ≤ Fintype.card α)
    (hC : IsPrefixCode C) {p : X → ℝ} (hp : IsPMF p) :
    codeRedundancy p C = ∑ k ∈ internalNodes C, localRedundancy p C k := by
  rw [codeRedundancy, expectedLength_eq_sum_reachProb hC p,
    entropyBase_eq_sum_reachProb_mul_nodeEntropy hα hC hp, ← sum_sub_distrib]
  exact sum_congr rfl fun k _ => by rw [localRedundancy]; ring

/-- The conditional branching distribution of a node of positive probability is a pmf. -/
lemma isPMF_branch (hC : IsPrefixCode C) {p : X → ℝ} (hp : IsPMF p) {k : List α}
    (hk : k ∈ internalNodes C) (hq : 0 < reachProb p C k) :
    IsPMF fun j => branchProb p C k j / reachProb p C k :=
  ⟨fun j => div_nonneg (reachProb_nonneg hp C _) hq.le, by
    rw [← sum_div, sum_branchProb hC p hk, div_self hq.ne']⟩

/-- **(4.65)** The local redundancy is nonnegative. -/
theorem localRedundancy_nonneg (hα : 2 ≤ Fintype.card α) (hC : IsPrefixCode C) {p : X → ℝ}
    (hp : IsPMF p) {k : List α} (hk : k ∈ internalNodes C) : 0 ≤ localRedundancy p C k := by
  have hlog : 0 < log (Fintype.card α) :=
    log_pos (by exact_mod_cast (by omega : 1 < Fintype.card α))
  rcases (reachProb_nonneg hp C k).eq_or_lt with h0 | hq
  · simp [localRedundancy, ← h0]
  · refine mul_nonneg hq.le (sub_nonneg.2 ?_)
    rw [nodeEntropy, entropyBase_eq_div, div_le_one hlog]
    exact entropy_le_log_card (isPMF_branch hC hp hk hq)

omit [DecidableEq α] in
/-- **Corollary 4.21 (Entropy Bound).** The redundancy of a prefix code is nonnegative. -/
theorem codeRedundancy_nonneg [Nontrivial X] (hα : 2 ≤ Fintype.card α) (hC : IsPrefixCode C)
    {p : X → ℝ} (hp : IsPMF p) : 0 ≤ codeRedundancy p C := by
  classical
  rw [codeRedundancy_eq_sum_localRedundancy hα hC hp]
  exact sum_nonneg fun k hk => localRedundancy_nonneg hα hC hp hk

/-- **(4.71)** The redundancy is at least the sum of the local redundancies of any set of internal
nodes. -/
theorem sum_localRedundancy_le_codeRedundancy [Nontrivial X] (hα : 2 ≤ Fintype.card α)
    (hC : IsPrefixCode C) {p : X → ℝ} (hp : IsPMF p) {I' : Finset (List α)}
    (hI : I' ⊆ internalNodes C) : ∑ k ∈ I', localRedundancy p C k ≤ codeRedundancy p C := by
  rw [codeRedundancy_eq_sum_localRedundancy hα hC hp]
  exact sum_le_sum_of_subset_of_nonneg hI fun k hk _ => localRedundancy_nonneg hα hC hp hk

/-- A node is balanced, `p̃_{k,j} = q_k / D` for all `j`, iff its local redundancy vanishes. -/
theorem localRedundancy_eq_zero_iff (hα : 2 ≤ Fintype.card α) (hC : IsPrefixCode C) {p : X → ℝ}
    (hp : IsPMF p) {k : List α} (hk : k ∈ internalNodes C) :
    localRedundancy p C k = 0 ↔ ∀ j, branchProb p C k j = reachProb p C k / Fintype.card α := by
  have hD : (0 : ℝ) < Fintype.card α := by exact_mod_cast (by omega : 0 < Fintype.card α)
  have hlog : 0 < log (Fintype.card α) :=
    log_pos (by exact_mod_cast (by omega : 1 < Fintype.card α))
  rcases (reachProb_nonneg hp C k).eq_or_lt with h0 | hq
  · have hb : ∀ j, branchProb p C k j = 0 := fun j =>
      le_antisymm (h0 ▸ branchProb_le hp C k j) (reachProb_nonneg hp C _)
    simp [localRedundancy, ← h0, hb]
  · have hpmf := isPMF_branch hC hp hk hq
    rw [localRedundancy, mul_eq_zero, or_iff_right hq.ne', sub_eq_zero, eq_comm, nodeEntropy,
      entropyBase_eq_div, div_eq_one_iff_eq hlog.ne', entropy_eq_log_card_iff hpmf, funext_iff]
    refine forall_congr' fun j => ?_
    simp only [uniformPMF]
    rw [div_eq_iff hq.ne']
    constructor
    · intro h
      rw [h]
      field_simp
    · intro h
      rw [h]
      field_simp

/-- **Corollary 4.21 (Entropy Bound).** The redundancy of a prefix code vanishes iff all the
internal nodes of the code tree are balanced. -/
theorem codeRedundancy_eq_zero_iff [Nontrivial X] (hα : 2 ≤ Fintype.card α) (hC : IsPrefixCode C)
    {p : X → ℝ} (hp : IsPMF p) :
    codeRedundancy p C = 0 ↔
      ∀ k ∈ internalNodes C, ∀ j, branchProb p C k j = reachProb p C k / Fintype.card α := by
  rw [codeRedundancy_eq_sum_localRedundancy hα hC hp,
    sum_eq_zero_iff_of_nonneg fun k hk => localRedundancy_nonneg hα hC hp hk]
  exact forall₂_congr fun k hk => localRedundancy_eq_zero_iff hα hC hp hk

/-- **Example 4.22, (4.72).** If the codewords of `x` and `y` are siblings in a binary prefix code,
the redundancy is at least the local redundancy of their parent. -/
theorem localRedundancy_siblings_le_codeRedundancy {C : X → List Bool} (hC : IsPrefixCode C)
    {p : X → ℝ} (hp : IsPMF p) {x y : X} {k : List Bool} (hx : C x = k ++ [false])
    (hy : C y = k ++ [true]) :
    (p x + p y) * (1 - entropyBase 2 fun b : Bool => if b then p y / (p x + p y)
      else p x / (p x + p y)) ≤ codeRedundancy p C := by
  have hne : x ≠ y := by
    rintro rfl
    rw [hx] at hy
    simp at hy
  have : Nontrivial X := ⟨x, y, hne⟩
  have hα : 2 ≤ Fintype.card Bool := by simp
  have hk : k ∈ internalNodes C := mem_internalNodes.2 ⟨x, by rw [hx]; exact List.prefix_append _ _,
    by rw [hx]; simp⟩
  have hf : branchProb p C k false = p x := by
    rw [branchProb, ← hx, reachProb_codeword hC]
  have ht : branchProb p C k true = p y := by
    rw [branchProb, ← hy, reachProb_codeword hC]
  have hq : reachProb p C k = p x + p y := by
    rw [← sum_branchProb hC p hk, Fintype.sum_bool, ht, hf, add_comm]
  have h := sum_localRedundancy_le_codeRedundancy hα hC hp (I' := {k}) (by simpa using hk)
  rw [sum_singleton, localRedundancy, nodeEntropy, hq] at h
  convert h using 3
  · simp only [Fintype.card_bool, Nat.cast_ofNat]
    refine congrArg _ (funext fun b => ?_)
    cases b <;> simp [hf, ht]

/-! ### Optimal codes -/

omit [DecidableEq α] in
/-- **Corollary 4.11.** There is a `D`-ary prefix code that achieves the entropy bound iff the
distribution is `D`-adic. -/
theorem exists_prefixCode_eq_entropyBase_iff (hα : 2 ≤ Fintype.card α) {p : X → ℝ}
    (hp : IsPMF p) :
    (∃ C : X → List α, IsPrefixCode C ∧ expectedLength p C = entropyBase (Fintype.card α) p) ↔
      IsDAdic (Fintype.card α) p := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  rw [← exists_lengths_eq_entropyBase_iff hp hα]
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨fun x => (C x).length, kraft_of_isPrefixCode hC, h⟩
  · rintro ⟨l, hk, h⟩
    obtain ⟨C, hC, hl⟩ := exists_prefixCode_of_kraft l hk
    exact ⟨C, hC, by simpa [expectedLength, hl] using h⟩

omit [Fintype X] [Fintype α] [DecidableEq α] in
/-- A prefix code composed with a permutation of the symbols is a prefix code. -/
lemma IsPrefixCode.comp_perm (hC : IsPrefixCode C) (σ : Equiv.Perm X) : IsPrefixCode (C ∘ σ) :=
  fun _ _ h => σ.injective (hC _ _ h)

omit [Fintype α] [DecidableEq α] in
/-- **Lemma 4.14.** In an optimal code, shorter codewords are assigned to larger probabilities. -/
theorem length_le_of_isOptimal (hC : IsPrefixCode C) {p : X → ℝ}
    (hopt : ∀ C' : X → List α, IsPrefixCode C' → expectedLength p C ≤ expectedLength p C')
    {a b : X} (hab : p b < p a) : (C a).length ≤ (C b).length := by
  classical
  by_contra hlt
  push Not at hlt
  have hne : a ≠ b := by
    rintro rfl
    exact lt_irrefl _ hab
  -- (4.30): exchanging the two codewords changes the expected length by a negative amount
  have hdiff : expectedLength p (C ∘ Equiv.swap a b) - expectedLength p C =
      (p a - p b) * ((C b).length - (C a).length) := by
    simp only [expectedLength, ← sum_sub_distrib, Function.comp_apply]
    rw [sum_eq_add a b hne (fun c _ hc => ?_) (fun h => absurd (mem_univ a) h)
      (fun h => absurd (mem_univ b) h)]
    · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hc.1 hc.2, sub_self]
  have hneg : (p a - p b) * (((C b).length : ℝ) - (C a).length) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.2 hab) (sub_neg.2 (by exact_mod_cast hlt))
  have := hopt _ (hC.comp_perm (Equiv.swap a b))
  linarith

/-- For two smallest probabilities, there are optimal lengths with equal maximal lengths on them. -/
lemma exists_lengths_siblings_aux {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) {a b : X} (hab : a ≠ b)
    (hle : p a ≤ p b) (hsmall : ∀ c, c ≠ a → c ≠ b → p a ≤ p c ∧ p b ≤ p c) (l : X → ℕ)
    (hk : ∑ x, (1 / 2 : ℝ) ^ l x ≤ 1) :
    ∃ m : X → ℕ, ∑ x, (1 / 2 : ℝ) ^ m x ≤ 1 ∧ ∑ x, p x * m x ≤ ∑ x, p x * l x ∧ m a = m b ∧
      1 ≤ m a ∧ ∀ c, m c ≤ m a := by
  classical
  have hcard : 2 ≤ Fintype.card X := by
    have : Nontrivial X := ⟨a, b, hab⟩
    exact Fintype.one_lt_card
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card X = n + 2 := ⟨Fintype.card X - 2, by omega⟩
  let e : X ≃ Fin (n + 2) := Fintype.equivFinOfCardEq hn
  let w : Fin (n + 2) → ℝ := p ∘ e.symm
  let τ := Tuple.sort w
  have hτ : Monotone (w ∘ τ) := Tuple.monotone_sort w
  -- swapping two positions of equal weight keeps the sorted order
  have hswap : ∀ {σ : Equiv.Perm (Fin (n + 2))} {i j : Fin (n + 2)}, w i = w j →
      w ∘ (Equiv.swap i j * σ) = w ∘ σ := by
    intro σ i j hij
    funext t
    simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    by_cases h₁ : σ t = i
    · rw [h₁, Equiv.swap_apply_left, hij]
    · by_cases h₂ : σ t = j
      · rw [h₂, Equiv.swap_apply_right, hij]
      · rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  have hwa : ∀ i, i ≠ e b → w (e a) ≤ w i := by
    intro i hi
    by_cases hia : i = e a
    · rw [hia]
    · have h₁ : e.symm i ≠ a := fun h => hia (by rw [← h]; simp)
      have h₂ : e.symm i ≠ b := fun h => hi (by rw [← h]; simp)
      simpa [w] using (hsmall _ h₁ h₂).1
  have hwab : w (e a) ≤ w (e b) := by simpa [w] using hle
  have hwb : ∀ i, i ≠ e a → w (e b) ≤ w i := by
    intro i hi
    by_cases hib : i = e b
    · rw [hib]
    · have h₁ : e.symm i ≠ a := fun h => hi (by rw [← h]; simp)
      have h₂ : e.symm i ≠ b := fun h => hib (by rw [← h]; simp)
      simpa [w] using (hsmall _ h₁ h₂).2
  -- first bring `a` to position `0`
  have h₀ : w (τ 0) = w (e a) := by
    refine le_antisymm ?_ ?_
    · have := hτ (Fin.zero_le (τ.symm (e a)))
      simpa using this
    · by_cases hb : τ 0 = e b
      · rw [hb]
        exact hwab
      · exact hwa _ hb
  let σ₁ := Equiv.swap (τ 0) (e a) * τ
  have hσ₁ : w ∘ σ₁ = w ∘ τ := hswap h₀
  have hσ₁0 : σ₁ 0 = e a := by simp [σ₁]
  have hmono₁ : Monotone (w ∘ σ₁) := hσ₁ ▸ hτ
  -- then bring `b` to position `1`
  have hne₁ : σ₁ 1 ≠ e a := by
    rw [← hσ₁0]
    exact fun h => absurd (σ₁.injective h) (by simp)
  have h₁ : w (σ₁ 1) = w (e b) := by
    refine le_antisymm ?_ (hwb _ hne₁)
    have hj : σ₁.symm (e b) ≠ 0 := by
      intro h
      have : e b = σ₁ 0 := by rw [← h]; simp
      rw [hσ₁0] at this
      exact hab (e.injective this.symm)
    have h1j : (1 : Fin (n + 2)) ≤ σ₁.symm (e b) := by
      rw [Fin.le_def]
      have : (σ₁.symm (e b)).val ≠ 0 := fun h => hj (Fin.ext h)
      simp only [Fin.val_one]
      omega
    have := hmono₁ h1j
    simpa using this
  let σ := Equiv.swap (σ₁ 1) (e b) * σ₁
  have hσ : w ∘ σ = w ∘ σ₁ := hswap h₁
  have hmono : Monotone (w ∘ σ) := hσ ▸ hmono₁
  have hσ1 : σ 1 = e b := by simp [σ]
  have hσ0 : σ 0 = e a := by
    have hb : e a ≠ e b := fun h => hab (e.injective h)
    simp only [σ, Equiv.Perm.mul_apply, hσ₁0]
    exact Equiv.swap_apply_of_ne_of_ne hne₁.symm hb
  -- the canonical lengths for the sorted weights
  let f : Fin (n + 2) ≃ X := σ.trans e.symm
  have hk' : ∑ i, (1 / 2 : ℝ) ^ (l ∘ f) i ≤ 1 := by
    rw [show ∑ i, (1 / 2 : ℝ) ^ (l ∘ f) i = ∑ x, (1 / 2 : ℝ) ^ l x from
      Equiv.sum_comp f fun x => (1 / 2 : ℝ) ^ l x]
    exact hk
  obtain ⟨m, hm₁, hm₂, hm₃, hm₄, hm₅⟩ := exists_canonical_lengths (w ∘ σ) hmono
    (fun i => hp _) (l ∘ f) hk'
  have hfw : ∀ i, (w ∘ σ) i = p (f i) := fun _ => rfl
  have hfa : f.symm a = 0 := by
    rw [Equiv.symm_apply_eq]
    simp [f, hσ0]
  have hfb : f.symm b = 1 := by
    rw [Equiv.symm_apply_eq]
    simp [f, hσ1]
  refine ⟨m ∘ f.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show ∑ x, (1 / 2 : ℝ) ^ (m ∘ f.symm) x = ∑ i, (1 / 2 : ℝ) ^ m i from
      Equiv.sum_comp f.symm fun i => (1 / 2 : ℝ) ^ m i]
    exact hm₁
  · have e₁ : ∑ x, p x * ((m ∘ f.symm) x : ℝ) = ∑ i, (w ∘ σ) i * (m i : ℝ) := by
      rw [← Equiv.sum_comp f]
      exact sum_congr rfl fun i _ => by
        rw [hfw i]
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
    have e₂ : ∑ x, p x * (l x : ℝ) = ∑ i, (w ∘ σ) i * ((l ∘ f) i : ℝ) := by
      rw [← Equiv.sum_comp f]
      exact sum_congr rfl fun i _ => by
        rw [hfw i]
        rfl
    rw [e₁, e₂]
    exact hm₂
  · simp only [Function.comp_apply, hfa, hfb]
    exact hm₃
  · simp only [Function.comp_apply, hfa]
    exact hm₄
  · intro c
    simp only [Function.comp_apply, hfa]
    exact hm₅ _

/-- The lengths of `exists_lengths_siblings_aux`, for any two smallest probabilities. -/
lemma exists_lengths_siblings {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) {a b : X} (hab : a ≠ b)
    (hsmall : ∀ c, c ≠ a → c ≠ b → p a ≤ p c ∧ p b ≤ p c) (l : X → ℕ)
    (hk : ∑ x, (1 / 2 : ℝ) ^ l x ≤ 1) :
    ∃ m : X → ℕ, ∑ x, (1 / 2 : ℝ) ^ m x ≤ 1 ∧ ∑ x, p x * m x ≤ ∑ x, p x * l x ∧ m a = m b ∧
      1 ≤ m a ∧ ∀ c, m c ≤ m a := by
  rcases le_total (p a) (p b) with hle | hle
  · exact exists_lengths_siblings_aux hp hab hle hsmall l hk
  · obtain ⟨m, h₁, h₂, h₃, h₄, h₅⟩ := exists_lengths_siblings_aux hp hab.symm hle
      (fun c hb ha => (hsmall c ha hb).symm) l hk
    exact ⟨m, h₁, h₂, h₃.symm, h₃ ▸ h₄, fun c => h₃ ▸ h₅ c⟩

/-- **Lemma 4.15.** There is an optimal binary prefix code in which the codewords of the two
smallest probabilities are siblings: they have the same length and differ only in the last
symbol. -/
theorem exists_optimal_prefixCode_siblings {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) {a b : X} (hab : a ≠ b)
    (hsmall : ∀ c, c ≠ a → c ≠ b → p a ≤ p c ∧ p b ≤ p c) :
    ∃ C : X → List Bool, IsPrefixCode C ∧
      (∀ C' : X → List Bool, IsPrefixCode C' → expectedLength p C ≤ expectedLength p C') ∧
        ∃ k, C a = k ++ [false] ∧ C b = k ++ [true] := by
  classical
  have : Nontrivial X := ⟨a, b, hab⟩
  have hHk := kraft_huffmanLengthsOf p
  obtain ⟨m, hm₁, hm₂, hm₃, hm₄, hm₅⟩ := exists_lengths_siblings hp hab hsmall
    (huffmanLengthsOf p) hHk.le
  -- the reduced code: the two siblings are replaced by their parent
  let Y := {x : X // x ≠ b}
  let a' : Y := ⟨a, hab⟩
  let l' : Y → ℕ := fun y => if y = a' then m a - 1 else m y
  have hhalf : (1 / 2 : ℝ) ^ (m a - 1) = (1 / 2 : ℝ) ^ m a + (1 / 2 : ℝ) ^ m b := by
    obtain ⟨t, ht⟩ : ∃ t, m a = t + 1 := ⟨m a - 1, by omega⟩
    rw [← hm₃, ht, Nat.add_sub_cancel, pow_succ]
    ring
  have hl'a : l' a' = m a - 1 := by simp [l']
  have hl'o : ∀ y : Y, y ≠ a' → l' y = m y := fun y hy => by simp [l', hy]
  have hsplit : ∑ x, (1 / 2 : ℝ) ^ m x = (1 / 2 : ℝ) ^ m b + ∑ y : Y, (1 / 2 : ℝ) ^ m y := by
    rw [← add_sum_erase univ _ (mem_univ b)]
    congr 1
    exact sum_subtype _ (fun x => by simp) _
  have hdiff : ∑ y : Y, ((1 / 2 : ℝ) ^ l' y - (1 / 2 : ℝ) ^ m y) = (1 / 2 : ℝ) ^ m b := by
    rw [sum_eq_single a' (fun y _ hy => by rw [hl'o y hy, sub_self])
      (fun h => absurd (mem_univ a') h), hl'a, hhalf]
    ring
  have hk' : ∑ y, (1 / (Fintype.card Bool : ℕ) : ℝ) ^ l' y ≤ 1 := by
    rw [sum_sub_distrib] at hdiff
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    linarith
  obtain ⟨C', hC', hlen⟩ := exists_prefixCode_of_kraft (α := Bool) l' hk'
  let C : X → List Bool := fun x =>
    if hb : x = b then C' a' ++ [true] else if x = a then C' a' ++ [false] else C' ⟨x, hb⟩
  have hCa : C a = C' a' ++ [false] := by simp [C, hab]
  have hCb : C b = C' a' ++ [true] := by simp [C]
  have hCo : ∀ x (hb : x ≠ b), x ≠ a → C x = C' ⟨x, hb⟩ := fun x hb ha => by simp [C, hb, ha]
  -- a word extending the codeword of the parent, and a codeword of another symbol
  have hext : ∀ (t : Bool) (x : X) (hb : x ≠ b), x ≠ a → ¬ C' a' ++ [t] <+: C' ⟨x, hb⟩ := by
    intro t x hb ha h
    have := hC' a' ⟨x, hb⟩ (prefix_of_append_singleton_prefix h)
    exact ha (congrArg Subtype.val this).symm
  have hext' : ∀ (t : Bool) (x : X) (hb : x ≠ b), x ≠ a → ¬ C' ⟨x, hb⟩ <+: C' a' ++ [t] := by
    intro t x hb ha h
    rcases List.prefix_concat_iff.1 h with h | h
    · have hp' : C' a' <+: C' ⟨x, hb⟩ := by
        rw [h]
        exact List.prefix_append _ _
      exact ha (congrArg Subtype.val (hC' a' ⟨x, hb⟩ hp')).symm
    · exact ha (congrArg Subtype.val (hC' ⟨x, hb⟩ a' h))
  have hdiffbit : ∀ t t' : Bool, t ≠ t' → ¬ C' a' ++ [t] <+: C' a' ++ [t'] := by
    intro t t' hne h
    rw [List.prefix_append_right_inj] at h
    simpa using hne (by simpa using h)
  have hC : IsPrefixCode C := by
    intro x y h
    by_cases hxb : x = b
    · subst hxb
      rw [hCb] at h
      by_cases hyb : y = x
      · exact hyb.symm
      · by_cases hya : y = a
        · subst hya
          rw [hCa] at h
          exact absurd h (hdiffbit _ _ (by simp))
        · rw [hCo y hyb hya] at h
          exact absurd h (hext _ y hyb hya)
    · by_cases hxa : x = a
      · subst hxa
        rw [hCa] at h
        by_cases hyb : y = b
        · subst hyb
          rw [hCb] at h
          exact absurd h (hdiffbit _ _ (by simp))
        · by_cases hya : y = x
          · exact hya.symm
          · rw [hCo y hyb hya] at h
            exact absurd h (hext _ y hyb hya)
      · rw [hCo x hxb hxa] at h
        by_cases hyb : y = b
        · subst hyb
          rw [hCb] at h
          exact absurd h (hext' _ x hxb hxa)
        · by_cases hya : y = a
          · subst hya
            rw [hCa] at h
            exact absurd h (hext' _ x hxb hxa)
          · rw [hCo y hyb hya] at h
            exact congrArg Subtype.val (hC' _ _ h)
  have hm0 : m a - 1 + 1 = m a := by omega
  have hClen : ∀ x, (C x).length = m x := by
    intro x
    by_cases hxb : x = b
    · subst hxb
      rw [hCb, List.length_append, hlen, hl'a, List.length_singleton, hm0, hm₃]
    · by_cases hxa : x = a
      · subst hxa
        rw [hCa, List.length_append, hlen, hl'a, List.length_singleton, hm0]
      · rw [hCo x hxb hxa, hlen, hl'o _ fun h => hxa (congrArg Subtype.val h)]
  refine ⟨C, hC, fun C₂ hC₂ => ?_, C' a', hCa, hCb⟩
  have h₁ : expectedLength p C = ∑ x, p x * (m x : ℝ) := by
    simp [expectedLength, hClen]
  have h₂ : expectedLength p (huffmanCode p) = ∑ x, p x * (huffmanLengthsOf p x : ℝ) := by
    simp [expectedLength, (huffmanCode_spec p).2]
  have h₃ := huffmanCode_optimal hp hC₂.isUniquelyDecodableCode'
  rw [h₁]
  rw [h₂] at h₃
  exact hm₂.trans h₃

/-! ### The bound on the Huffman code -/

/-- **Theorem 4.17, (4.35).** The expected length of a binary Huffman code is less than `H₂(X) + 1`,
for positive probabilities. -/
theorem expectedLength_huffmanCode_lt [Nontrivial X] {p : X → ℝ} (hp : IsPMF p)
    (hpos : ∀ x, 0 < p x) : expectedLength p (huffmanCode p) < entropyBase 2 p + 1 := by
  obtain ⟨C, hC, -, hlt⟩ := exists_prefixCode_shannon (α := Bool) (by simp) hp hpos
  have h := huffmanCode_optimal hp.nonneg hC.isUniquelyDecodableCode'
  simpa using h.trans_lt hlt

/-- The distributions `(1 - (D - 1) / k, 1 / k, …, 1 / k)` of (4.45), for `D = d + 2`. -/
def tightPMF (d k : ℕ) : Fin (d + 2) → ℝ := fun i => if i = 0 then 1 - (d + 1) / k else 1 / k

lemma tightPMF_isPMF {d k : ℕ} (hk : d + 2 ≤ k) : IsPMF (tightPMF d k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hle : ((d : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk0]
    exact_mod_cast (by omega : d + 1 ≤ k)
  refine ⟨fun i => ?_, ?_⟩
  · simp only [tightPMF]
    split_ifs
    · linarith
    · positivity
  · simp only [tightPMF, Fin.sum_univ_succ, Fin.succ_ne_zero, ↓reduceIte, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    ring

/-- **(4.45)** The `D`-ary Huffman code for the distributions of (4.45) has `D` codewords of length
`1`: this is the optimal expected length. -/
theorem minExpectedLength_tightPMF {d k : ℕ} (hk : d + 2 ≤ k) :
    minExpectedLength (d + 2) (tightPMF d k) = 1 := by
  have hp := tightPMF_isPMF hk
  have hD : 2 ≤ d + 2 := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine le_antisymm ?_ ?_
  · have hK : kraftSum (d + 2) (fun _ : Fin (d + 2) => 1) ≤ 1 := by
      simp only [kraftSum, pow_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have : ((d : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      exact le_rfl
    have := minExpectedLength_le hD hp hK
    simpa [hp.sum_eq_one] using this
  · refine le_csInf (minExpectedLength_set_nonempty hD _) ?_
    rintro _ ⟨l, hK, rfl⟩
    have hl : ∀ i, 1 ≤ l i := by
      intro i
      by_contra h
      have h0 : l i = 0 := by omega
      obtain ⟨j, hj⟩ : ∃ j : Fin (d + 2), j ≠ i := exists_ne i
      have hpos : ∀ t, 0 ≤ (1 / ((d + 2 : ℕ) : ℝ)) ^ l t := fun t => by positivity
      have hge : (1 / ((d + 2 : ℕ) : ℝ)) ^ l i + (1 / ((d + 2 : ℕ) : ℝ)) ^ l j ≤
          ∑ t, (1 / ((d + 2 : ℕ) : ℝ)) ^ l t := by
        calc _ = ∑ t ∈ {i, j}, (1 / ((d + 2 : ℕ) : ℝ)) ^ l t := (sum_pair hj.symm).symm
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun t _ _ => hpos t
      have hjpos : 0 < (1 / ((d + 2 : ℕ) : ℝ)) ^ l j := by positivity
      rw [h0, pow_zero] at hge
      have hK' : ∑ t, (1 / ((d + 2 : ℕ) : ℝ)) ^ l t ≤ 1 := hK
      linarith
    calc 1 = ∑ i, tightPMF d k i := hp.sum_eq_one.symm
      _ ≤ ∑ i, tightPMF d k i * l i := sum_le_sum fun i _ => by
        have h1 : (1 : ℝ) ≤ l i := by exact_mod_cast hl i
        nlinarith [hp.nonneg i]

/-- **(4.45)** The entropy of the distributions of (4.45) tends to `0`. -/
theorem tendsto_entropyBase_tightPMF (d : ℕ) :
    Filter.Tendsto (fun k : ℕ => entropyBase (d + 2 : ℕ) (tightPMF d k)) Filter.atTop (nhds 0) := by
  classical
  let e : Fin (d + 2) → ℝ := fun i => if i = 0 then 1 else 0
  have he : IsPMF e := ⟨fun i => by simp only [e]; split_ifs <;> norm_num, by simp [e]⟩
  have hlim : Filter.Tendsto (fun k : ℕ => tightPMF d k) Filter.atTop (nhds e) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    by_cases hi : i = 0
    · simp only [tightPMF, e, hi, ↓reduceIte]
      simpa using (tendsto_const_div_atTop_nhds_zero_nat ((d : ℝ) + 1)).const_sub 1
    · simp only [tightPMF, e, hi, ↓reduceIte]
      exact tendsto_const_div_atTop_nhds_zero_nat 1
  have h0 : entropy e = 0 := (entropy_eq_zero_iff he).2 ⟨0, fun x => by
    by_cases hx : x = 0 <;> simp [e, hx]⟩
  have h := (continuous_entropy.tendsto e).comp hlim
  rw [h0] at h
  simp only [entropyBase_eq_div]
  simpa using h.div_const (log ((d + 2 : ℕ) : ℝ))

/-- **Theorem 4.17, the last statement.** The bound `H_D(X) + 1` is the tightest among the upper
bounds depending only on the entropy: for the distributions of (4.45), the optimal expected length
is `1` while the entropy tends to `0`. -/
theorem tendsto_entropyBase_add_one_sub_minExpectedLength (d : ℕ) :
    Filter.Tendsto (fun k : ℕ => entropyBase (d + 2 : ℕ) (tightPMF d k) + 1 -
      minExpectedLength (d + 2) (tightPMF d k)) Filter.atTop (nhds 0) := by
  have h := (tendsto_entropyBase_tightPMF d).add_const (1 : ℝ) |>.sub_const (1 : ℝ)
  simp only [zero_add, sub_self] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (d + 2)] with k hk
  rw [minExpectedLength_tightPMF hk]

/-- **Example 4.13.** To apply the `D`-ary Huffman procedure to `m ≥ 2` symbols, at most `D - 2`
dummy symbols are needed to make the number of symbols of the form `D + k (D - 1)`. -/
theorem exists_dummy_symbols {D m : ℕ} (hD : 2 ≤ D) (hm : 2 ≤ m) :
    ∃ s k, s ≤ D - 2 ∧ m + s = D + k * (D - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 2 := ⟨D - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hdm := Nat.div_add_mod (n + 1) (e + 1)
  have hlt := Nat.mod_lt (n + 1) (Nat.succ_pos e)
  generalize (n + 1) / (e + 1) = q at hdm
  generalize (n + 1) % (e + 1) = r at hdm hlt
  have hD1 : e + 2 - 1 = e + 1 := by omega
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · cases q with
    | zero => simp at hdm
    | succ t =>
      refine ⟨0, t, by omega, ?_⟩
      rw [hD1]
      nlinarith
  · refine ⟨e + 1 - r, q, by omega, ?_⟩
    have h₁ : e + 1 - r + r = e + 1 := by omega
    rw [hD1]
    nlinarith

end InfoTheory
