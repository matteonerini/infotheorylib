/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.LinearNetworkCode
public import InfoTheoryLib.Network.MaxFlowBound

/-!
# Single-source linear network coding on acyclic networks

An acyclic network can be ordered so that every channel goes downstream (Proposition 19.1). On such
a network, a linear code multicasts a message of `ω` symbols of a field `F` from a source `s`: the
symbol on a channel `e` is `x ⬝ fₑ` for a global encoding kernel `fₑ ∈ F^ω`. The span `V_T` of the
kernels of the channels into a set of nodes `T` has dimension at most `min(ω, maxflow(T))`
(Theorem 19.10), and a linear multicast, which reaches this bound for every node with
`maxflow(t) ≥ ω`, exists over every field with more than `|V| ω` elements (Theorem 19.20).

## Main definitions

* `PtpNetwork.IsAcyclic`: a network without directed cycles.
* `srcDim s ω`, `SrcIdx s ω`: a source `s` with a message of `ω` symbols, and the index set of the
  message symbols.
* `kernelSpan G a ξ`, `nodeSpan G a T`: the spans `V_ξ` and `V_T` of (19.31)–(19.33).
* `Multigraph.crossEdges`, `Multigraph.maxflowNodes`, `Multigraph.maxflowEdges`: the max-flow from
  `s` to a collection of nodes or of channels, as the capacity of a min-cut.
* `IsLinearMulticast`, `IsLinearBroadcast`, `IsLinearDispersion`: Definition 19.12.
* `inKernels G a t`: the matrix `F_{In(t)}` of (19.42).
* `LinCoeff.transform`: the transformation of a code by a matrix, (19.49)–(19.66).

## Main statements

* `PtpNetwork.exists_rank_of_isAcyclic`: **Proposition 19.1**.
* `finrank_nodeSpan_le`: **Theorem 19.10**.
* `finrank_kernelSpan_le`: **Corollary 19.11**.
* `IsLinearDispersion.isLinearBroadcast`, `IsLinearBroadcast.isLinearMulticast`: the hierarchy of
  Definition 19.12.
* `injective_received_iff`: (19.43)–(19.44), a node decodes if and only if `dim V_t = ω`.
* `exists_isLinearMulticast`: **Theorem 19.20**.
* `globalVec_transform`, `IsLinearMulticast.transform`: the transformation (19.49)–(19.66).

## Implementation notes

A linear code is a `LinCoeff F E (srcDim s ω)` of `Network.LinearNetworkCode`: its source
coefficients `y` are the local encoding kernels `k_{d,e}` of the imaginary channels `d` at `s`, its
coefficients `x` are the other local encoding kernels, and `globalVec` gives the global encoding
kernels by (19.17). The decoding coefficients `z` play no role in the definitions of this file.
Channels have unit capacity, and parallel channels are allowed.

The book defines `maxflow(T)` and `maxflow(ξ)` as max-flows in the graphs of Figure 18.1. Here they
are the capacities of the corresponding min-cuts, written on the original graph; by the max-flow
min-cut theorem these are the same numbers.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 19
-/

open Finset Module

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Acyclic networks -/

namespace PtpNetwork

variable {V E : Type*} (G : PtpNetwork V E)

/-- Node `j` follows node `i` along a channel. -/
def Adj (i j : V) : Prop := ∃ e, G.tail e = i ∧ G.head e = j

/-- **Section 19.1.** A network is acyclic if it has no directed cycle. -/
def IsAcyclic : Prop := ∀ i, ¬ Relation.TransGen G.Adj i i

/-- A ranking that increases along every channel increases along every directed path. -/
lemma lt_of_transGen {r : V → ℕ} (hr : ∀ e, r (G.tail e) < r (G.head e)) {i j : V}
    (h : Relation.TransGen G.Adj i j) : r i < r j := by
  induction h with
  | single h => obtain ⟨e, rfl, rfl⟩ := h; exact hr e
  | tail _ h ih => obtain ⟨e, he, rfl⟩ := h; exact ih.trans (he ▸ hr e)

/-- A network with a ranking that increases along every channel is acyclic. -/
lemma isAcyclic_of_rank {r : V → ℕ} (hr : ∀ e, r (G.tail e) < r (G.head e)) : G.IsAcyclic :=
  fun _ h => lt_irrefl _ (G.lt_of_transGen hr h)

/-- **Proposition 19.1.** The nodes of a finite acyclic network can be ranked so that every channel
goes from a lower to a higher rank: the rank of a node is its number of ancestors. -/
theorem exists_rank_of_isAcyclic [Finite V] (h : G.IsAcyclic) :
    ∃ r : V → ℕ, ∀ e, r (G.tail e) < r (G.head e) := by
  classical
  have := Fintype.ofFinite V
  refine ⟨fun j => #{i | Relation.TransGen G.Adj i j}, fun e => card_lt_card ?_⟩
  refine ⟨fun i hi => ?_, fun hsub => h (G.tail e) ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.tail ⟨e, rfl, rfl⟩
  · have : G.tail e ∈ ({i | Relation.TransGen G.Adj i (G.head e)} : Finset V) := by
      simp only [mem_filter, mem_univ, true_and]
      exact .single ⟨e, rfl, rfl⟩
    simpa using hsub this

end PtpNetwork

/-! ### Linear codes from one source -/

variable {V E F : Type*} [LinearOrder V] [Fintype V] [Fintype E] [Field F]

/-- A single source `s` with a message of `ω` symbols. -/
def srcDim (s : V) (ω : ℕ) : V → ℕ := fun j => if j = s then ω else 0

/-- The indices of the message symbols. -/
abbrev SrcIdx (s : V) (ω : ℕ) := Σ j, Fin (srcDim s ω j)

omit [Fintype V] in
lemma SrcIdx.fst_eq {s : V} {ω : ℕ} (r : SrcIdx s ω) : r.1 = s := by
  by_contra h
  have := r.2.isLt
  simp [srcDim, h] at this

lemma card_srcIdx (s : V) (ω : ℕ) : Fintype.card (SrcIdx s ω) = ω := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp [srcDim]

variable (G : Multigraph V E) {s : V} {ω : ℕ}

/-- The span `V_ξ` of the global encoding kernels of the channels in `ξ`, (19.33). -/
def kernelSpan (a : LinCoeff F E (srcDim s ω)) (ξ : Set E) : Submodule F (SrcIdx s ω → F) :=
  Submodule.span F (globalVec G a '' ξ)

/-- The span `V_T` of the global encoding kernels of the channels into the nodes of `T`,
(19.31)–(19.32). -/
def nodeSpan (a : LinCoeff F E (srcDim s ω)) (T : Finset V) : Submodule F (SrcIdx s ω → F) :=
  kernelSpan G a {e | G.head e ∈ T}

/-- The channels across the cut `U`, (18.7). -/
def Multigraph.crossEdges (U : Finset V) : Finset E :=
  univ.filter fun e => G.tail e ∈ U ∧ G.head e ∉ U

/-- The max-flow from `s` to the collection of nodes `T`: the capacity of a min-cut separating `s`
from all of `T`, which is the min-cut between `s` and the node `τ` of Figure 18.1(a). -/
def Multigraph.maxflowNodes (s : V) (T : Finset V) : ℕ :=
  sInf ((fun U => #(G.crossEdges U)) '' {U | s ∈ U ∧ Disjoint U T})

/-- The max-flow from `s` to the collection of channels `ξ`: the capacity of a min-cut in the graph
of Figure 18.1(b), in which a channel `e ∈ ξ` is cut when its tail is in `U`. -/
def Multigraph.maxflowEdges [DecidableEq E] (s : V) (ξ : Finset E) : ℕ :=
  sInf ((fun U => #(G.crossEdges U \ ξ) + #(ξ.filter fun e => G.tail e ∈ U)) '' {U | s ∈ U})

/-- (19.17) without the source: off the source, a global encoding kernel is the combination of the
kernels of the channels into its tail with the local encoding kernels. -/
lemma globalVec_eq_sum (a : LinCoeff F E (srcDim s ω)) {e : E} (he : G.tail e ≠ s) :
    globalVec G a e = ∑ d : {d // G.head d = G.tail e}, a.x d.val e • globalVec G a d.val := by
  funext r
  have hr : ¬ r.1 = G.tail e := by rw [SrcIdx.fst_eq r]; exact Ne.symm he
  rw [globalVec_eq]
  simp [hr, Finset.sum_apply]

/-- **The proof of Theorem 19.10.** The global encoding kernel of a channel out of a node beyond a
cut `U` lies in the span of the kernels of the channels across the cut. -/
lemma globalVec_mem_span_crossEdges (a : LinCoeff F E (srcDim s ω)) {U : Finset V} (hs : s ∈ U)
    (e : E) (he : G.tail e ∉ U) :
    globalVec G a e ∈ Submodule.span F (globalVec G a '' (G.crossEdges U : Set E)) := by
  induction hk : G.tail e using WellFoundedLT.induction generalizing e with
  | ind k ih =>
    rw [globalVec_eq_sum G a (fun h => he (h ▸ hs))]
    refine Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ ?_
    by_cases hd : G.tail d.val ∈ U
    · refine Submodule.subset_span ⟨d.val, ?_, rfl⟩
      simp only [Multigraph.crossEdges, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      exact ⟨hd, by rw [d.property]; exact he⟩
    · exact ih _ ((G.lt d.val).trans_eq (d.property.trans hk)) d.val hd rfl

/-- The kernels of the channels into the nodes beyond a cut lie in the span of the cut. -/
lemma nodeSpan_le_span_crossEdges (a : LinCoeff F E (srcDim s ω)) {U T : Finset V} (hs : s ∈ U)
    (hT : Disjoint U T) :
    nodeSpan G a T ≤ Submodule.span F (globalVec G a '' (G.crossEdges U : Set E)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨d, hd, rfl⟩
  have hdU : G.head d ∉ U := fun h => disjoint_left.1 hT h hd
  by_cases ht : G.tail d ∈ U
  · refine Submodule.subset_span ⟨d, ?_, rfl⟩
    simp only [Multigraph.crossEdges, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨ht, hdU⟩
  · exact globalVec_mem_span_crossEdges G a hs d ht

omit [Fintype V] [Fintype E] in
lemma finrank_le_omega [Finite V] (W : Submodule F (SrcIdx s ω → F)) : finrank F W ≤ ω := by
  have := Fintype.ofFinite V
  calc finrank F W ≤ finrank F (SrcIdx s ω → F) := Submodule.finrank_le W
    _ = ω := by rw [Module.finrank_fintype_fun_eq_card, card_srcIdx]

lemma finrank_span_image_le (a : LinCoeff F E (srcDim s ω)) (ξ : Finset E) :
    finrank F (Submodule.span F (globalVec G a '' (ξ : Set E))) ≤ #ξ := by
  classical
  rw [← coe_image]
  exact (finrank_span_finset_le_card _).trans card_image_le

/-- **Theorem 19.10 (Max-Flow Bound for Linear Network Coding).** For a collection `T` of non-source
nodes, `dim V_T ≤ min(ω, maxflow(T))`, (19.34). -/
theorem finrank_nodeSpan_le (a : LinCoeff F E (srcDim s ω)) {T : Finset V} (hT : s ∉ T) :
    finrank F (nodeSpan G a T) ≤ min ω (G.maxflowNodes s T) := by
  refine le_min (finrank_le_omega _) ?_
  have hne : ((fun U => #(G.crossEdges U)) '' {U | s ∈ U ∧ Disjoint U T}).Nonempty :=
    ⟨_, {s}, ⟨mem_singleton_self s, disjoint_singleton_left.2 hT⟩, rfl⟩
  obtain ⟨U, ⟨hs, hUT⟩, hU⟩ := Nat.sInf_mem hne
  rw [Multigraph.maxflowNodes, ← hU]
  exact (Submodule.finrank_mono (nodeSpan_le_span_crossEdges G a hs hUT)).trans
    (finrank_span_image_le G a _)

/-- **Corollary 19.11.** For a collection `ξ` of channels, `dim V_ξ ≤ min(ω, maxflow(ξ))`,
(19.38). -/
theorem finrank_kernelSpan_le [DecidableEq E] (a : LinCoeff F E (srcDim s ω)) (ξ : Finset E) :
    finrank F (kernelSpan G a ξ) ≤ min ω (G.maxflowEdges s ξ) := by
  refine le_min (finrank_le_omega _) ?_
  have hne : ((fun U => #(G.crossEdges U \ ξ) + #(ξ.filter fun e => G.tail e ∈ U)) ''
      {U | s ∈ U}).Nonempty := ⟨_, {s}, mem_singleton_self s, rfl⟩
  obtain ⟨U, hs, hU⟩ := Nat.sInf_mem hne
  rw [Multigraph.maxflowEdges, ← hU]
  have hle : kernelSpan G a ξ ≤ Submodule.span F (globalVec G a ''
      ((G.crossEdges U \ ξ ∪ ξ.filter fun e => G.tail e ∈ U : Finset E) : Set E)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    by_cases ht : G.tail d ∈ U
    · exact Submodule.subset_span ⟨d, by simp [mem_coe.1 hd, ht], rfl⟩
    · refine Submodule.span_mono ?_ (globalVec_mem_span_crossEdges G a hs d ht)
      refine Set.image_mono fun e he => ?_
      have he' := mem_filter.1 he
      by_cases heξ : e ∈ ξ
      · simp [heξ, he'.2.1]
      · simp [heξ, he]
  exact (Submodule.finrank_mono hle).trans ((finrank_span_image_le G a _).trans (card_union_le _ _))

/-! ### Linear multicast, broadcast and dispersion -/

section Properties

variable (a : LinCoeff F E (srcDim s ω))

/-- **Definition 19.12, (19.39).** A linear multicast: `dim V_t = ω` for every non-source node `t`
with `maxflow(t) ≥ ω`. -/
def IsLinearMulticast : Prop :=
  ∀ t, t ≠ s → ω ≤ G.maxflowNodes s {t} → finrank F (nodeSpan G a {t}) = ω

/-- **Definition 19.12, (19.40).** A linear broadcast: `dim V_t = min(ω, maxflow(t))` for every
non-source node `t`. -/
def IsLinearBroadcast : Prop :=
  ∀ t, t ≠ s → finrank F (nodeSpan G a {t}) = min ω (G.maxflowNodes s {t})

/-- **Definition 19.12, (19.41).** A linear dispersion: `dim V_T = min(ω, maxflow(T))` for every
collection `T` of non-source nodes. -/
def IsLinearDispersion : Prop :=
  ∀ T : Finset V, s ∉ T → finrank F (nodeSpan G a T) = min ω (G.maxflowNodes s T)

variable {G a}

/-- **After Definition 19.12.** A linear dispersion is a linear broadcast. -/
lemma IsLinearDispersion.isLinearBroadcast (h : IsLinearDispersion G a) : IsLinearBroadcast G a :=
  fun t ht => h {t} (by simpa using ht.symm)

/-- **After Definition 19.12.** A linear broadcast is a linear multicast. -/
lemma IsLinearBroadcast.isLinearMulticast (h : IsLinearBroadcast G a) : IsLinearMulticast G a :=
  fun t ht hω => (h t ht).trans (min_eq_left hω)

variable (G a)

/-- The matrix `F_{In(t)}` of (19.42), with the channels into `t` as rows. -/
def inKernels (t : V) : Matrix {e // G.head e = t} (SrcIdx s ω) F :=
  fun e r => globalVec G a e.val r

lemma nodeSpan_singleton_eq (t : V) :
    nodeSpan G a {t} = Submodule.span F (Set.range (inKernels G a t).row) := by
  rw [nodeSpan, kernelSpan]
  congr 1
  ext v
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, mem_singleton.1 he⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e.val, mem_singleton.2 e.property, rfl⟩

/-- `dim V_t` is the rank of `F_{In(t)}`. -/
lemma finrank_nodeSpan_singleton (t : V) :
    finrank F (nodeSpan G a {t}) = (inKernels G a t).rank := by
  rw [← Matrix.finrank_span_range_row, nodeSpan_singleton_eq]

/-- **(19.43)–(19.44)** Node `t` can recover the message `x` from the symbols `x ⬝ fₑ` received on
its input channels if and only if `dim V_t = ω`. -/
theorem injective_received_iff (t : V) :
    Function.Injective (inKernels G a t).mulVec ↔ finrank F (nodeSpan G a {t}) = ω := by
  classical
  have hd : finrank F (SrcIdx s ω → F) = ω := by
    rw [Module.finrank_fintype_fun_eq_card, card_srcIdx]
  rw [finrank_nodeSpan_singleton, ← Matrix.finrank_range_mulVecLin]
  constructor
  · intro h
    exact (LinearMap.finrank_range_of_inj (f := (inKernels G a t).mulVecLin) h).trans hd
  · intro h
    have hk := LinearMap.finrank_range_add_finrank_ker (inKernels G a t).mulVecLin
    rw [h, hd, add_eq_left, Submodule.finrank_eq_zero] at hk
    exact LinearMap.ker_eq_bot.1 hk

/-- A nonzero determinant of a transfer matrix `Z F_{In(t)}` gives `dim V_t ≥ ω`. -/
lemma le_finrank_of_det_transfer_ne_zero (t : V) (h : (transfer G a t).det ≠ 0) :
    ω ≤ finrank F (nodeSpan G a {t}) := by
  classical
  let Z : Matrix (SrcIdx s ω) {e // G.head e = t} F := fun r e => a.z t e.val r
  have htr : transfer G a t = Z * inKernels G a t := by
    ext r r'
    rw [Matrix.mul_apply]
    rfl
  have hunit : IsUnit (Z * inKernels G a t) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (htr ▸ h))
  rw [finrank_nodeSpan_singleton]
  calc ω = Fintype.card (SrcIdx s ω) := (card_srcIdx s ω).symm
    _ = (Z * inKernels G a t).rank := (Matrix.rank_of_isUnit _ hunit).symm
    _ ≤ _ := Matrix.rank_mul_le_right _ _

end Properties

/-! ### Existence of a linear multicast -/

omit [Fintype V] in
/-- The capacity of a cut for the count matrix is the number of channels across it. -/
lemma cutCap_count [Fintype V] (S : Finset V) :
    cutCap (fun j k => (G.count j k : ℤ)) S = #(G.crossEdges S) := by
  classical
  simp only [cutCap, Multigraph.count, Multigraph.crossEdges, natCast_card_filter]
  calc ∑ j ∈ S, ∑ k ∈ Sᶜ, ∑ e, (if G.tail e = j ∧ G.head e = k then (1 : ℤ) else 0)
      = ∑ j ∈ S, ∑ e, ∑ k ∈ Sᶜ, (if G.tail e = j ∧ G.head e = k then (1 : ℤ) else 0) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ e, ∑ j ∈ S, ∑ k ∈ Sᶜ, (if G.tail e = j ∧ G.head e = k then (1 : ℤ) else 0) :=
        sum_comm
    _ = _ := sum_congr rfl fun e _ => by
        simp only [ite_and]
        rw [sum_congr rfl fun x _ => (sum_ite_irrel _ _ _ _).trans (by rw [sum_const_zero]),
          sum_ite_eq, sum_ite_eq]
        simp only [mem_compl]

/-- **Theorem 19.20.** Over a finite field with more than `|V| ω` elements there is an
`ω`-dimensional linear multicast. The determinants of the transfer matrices of the sinks are
nonzero polynomials, since routing along `ω` edge-disjoint paths makes them `1`, and Lemma 19.17
gives values of the local encoding kernels at which none of them vanishes. -/
theorem exists_isLinearMulticast [Fintype F] (s : V) (ω : ℕ)
    (hF : Fintype.card V * ω < Fintype.card F) :
    ∃ a : LinCoeff F E (srcDim s ω), IsLinearMulticast G a := by
  classical
  set T : Finset V := univ.filter fun t => t ≠ s ∧ ω ≤ G.maxflowNodes s {t}
  have hdet : ∀ t ∈ T, detGeneric (b := srcDim s ω) F G t ≠ 0 := by
    intro t ht
    obtain ⟨hts, hω⟩ := (mem_filter.1 ht).2
    refine detGeneric_ne_zero_of_cuts G t (by simp [srcDim, hts]) fun S htS => ?_
    rw [cutCap_count]
    by_cases hsS : s ∈ S
    · have hsum : ∑ j ∈ S, (srcDim s ω j : ℤ) = ω := by simp [srcDim, hsS]
      rw [hsum]
      have : G.maxflowNodes s {t} ≤ #(G.crossEdges S) :=
        Nat.sInf_le ⟨S, ⟨hsS, disjoint_singleton_right.2 htS⟩, rfl⟩
      exact_mod_cast hω.trans this
    · have hsum : ∑ j ∈ S, (srcDim s ω j : ℤ) = 0 :=
        sum_eq_zero fun j hj => by simp [srcDim, ne_of_mem_of_not_mem hj hsS]
      rw [hsum]
      positivity
  have hF' : #T * Fintype.card (SrcIdx s ω) < Fintype.card F := by
    rw [card_srcIdx]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (card_le_univ T)) hF
  obtain ⟨α, hα⟩ := exists_coeff_of_card_gt (𝕜' := F) (F := F) G hdet hF'
  refine ⟨ofAssign α, fun t hts hω => le_antisymm (finrank_le_omega _) ?_⟩
  exact le_finrank_of_det_transfer_ne_zero G _ t (hα t (by simp [T, hts, hω]))

/-! ### Transformations -/

section Transform

/-- **(19.49)–(19.66)** The transformation of a linear code by a matrix `A`: the source encodes
`x A` instead of `x`, so its local encoding kernels become `A K_s` and the others are unchanged. -/
def LinCoeff.transform (a : LinCoeff F E (srcDim s ω)) (A : Matrix (SrcIdx s ω) (SrcIdx s ω) F) :
    LinCoeff F E (srcDim s ω) :=
  ⟨fun r e => ∑ r', A r r' * a.y r' e, a.x, a.z⟩

/-- **(19.51)** The global encoding kernels of the transformation are `A fₑ`. -/
lemma globalVec_transform (a : LinCoeff F E (srcDim s ω)) (A : Matrix (SrcIdx s ω) (SrcIdx s ω) F)
    (e : E) : globalVec G (a.transform A) e = A.mulVec (globalVec G a e) := by
  induction hk : G.tail e using WellFoundedLT.induction generalizing e with
  | ind k ih =>
    funext r
    have hih : ∀ d : {d // G.head d = G.tail e}, globalVec G (a.transform A) d.val =
        A.mulVec (globalVec G a d.val) := fun d =>
      ih _ ((G.lt d.val).trans_eq (d.property.trans hk)) d.val rfl
    rw [globalVec_eq, Matrix.mulVec, dotProduct]
    simp only [globalVec_eq G a e, mul_add, sum_add_distrib]
    congr 1
    · simp only [SrcIdx.fst_eq, LinCoeff.transform, mul_ite, mul_zero]
      split_ifs <;> simp
    · have hd : ∀ d : {d // G.head d = G.tail e}, globalVec G (a.transform A) d.val r =
          ∑ r', A r r' * globalVec G a d.val r' := fun d => by rw [hih d]; rfl
      simp only [hd, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun r' _ => sum_congr rfl fun d _ => ?_
      change a.x d.val e * (A r r' * globalVec G a d.val r') =
        A r r' * (a.x d.val e * globalVec G a d.val r')
      ring

/-- The spans of the transformation are the images of the spans under `A`. -/
lemma kernelSpan_transform (a : LinCoeff F E (srcDim s ω)) (A : Matrix (SrcIdx s ω) (SrcIdx s ω) F)
    (ξ : Set E) : kernelSpan G (a.transform A) ξ = (kernelSpan G a ξ).map A.mulVecLin := by
  rw [kernelSpan, kernelSpan, Submodule.map_span, ← Set.image_comp]
  congr 1
  exact Set.image_congr fun e _ => globalVec_transform G a A e

/-- An invertible transformation keeps the dimensions of the spans. -/
lemma finrank_kernelSpan_transform (a : LinCoeff F E (srcDim s ω))
    {A : Matrix (SrcIdx s ω) (SrcIdx s ω) F} (hA : IsUnit A) (ξ : Set E) :
    finrank F (kernelSpan G (a.transform A) ξ) = finrank F (kernelSpan G a ξ) := by
  classical
  rw [kernelSpan_transform]
  have hinj : Function.Injective A.mulVecLin := Matrix.mulVec_injective_iff_isUnit.2 hA
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _).symm

variable {G}

/-- **After (19.66).** A transformation of a linear multicast by an invertible matrix is a linear
multicast. -/
lemma IsLinearMulticast.transform {a : LinCoeff F E (srcDim s ω)} (h : IsLinearMulticast G a)
    {A : Matrix (SrcIdx s ω) (SrcIdx s ω) F} (hA : IsUnit A) :
    IsLinearMulticast G (a.transform A) := fun t ht hω => by
  rw [nodeSpan, finrank_kernelSpan_transform G a hA]
  exact h t ht hω

/-- **After (19.66).** A transformation of a linear broadcast by an invertible matrix is a linear
broadcast. -/
lemma IsLinearBroadcast.transform {a : LinCoeff F E (srcDim s ω)} (h : IsLinearBroadcast G a)
    {A : Matrix (SrcIdx s ω) (SrcIdx s ω) F} (hA : IsUnit A) :
    IsLinearBroadcast G (a.transform A) := fun t ht => by
  rw [nodeSpan, finrank_kernelSpan_transform G a hA]
  exact h t ht

/-- **After (19.66).** A transformation of a linear dispersion by an invertible matrix is a linear
dispersion. -/
lemma IsLinearDispersion.transform {a : LinCoeff F E (srcDim s ω)} (h : IsLinearDispersion G a)
    {A : Matrix (SrcIdx s ω) (SrcIdx s ω) F} (hA : IsUnit A) :
    IsLinearDispersion G (a.transform A) := fun T hT => by
  rw [nodeSpan, finrank_kernelSpan_transform G a hA]
  exact h T hT

end Transform

end InfoTheory
