/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.InfoInequalities.EntropicRegion

/-!
# Multi-source network coding: the regions `R'` and `R_LP`

A multi-source network coding problem on a network has sources `s` generated at nodes
`src s`, sinks `t ∈ T` that demand the sources `β t`, and a rate constraint `R e` on each channel.
Its achievable information rate region is characterized by the region `R'` of Definition 21.4 of
Yeung, defined from the region `Γ**` of the entropy functions of random variables `Y_s` and `U_e`
with finite alphabets, `entropicRegion (σ ⊕ E)`. Replacing `Γ**` by the region `Γ` of the Shannon
inequalities gives the LP outer bound `R_LP` of (21.39), which is cut out by finitely many linear
inequalities.

## Main definitions

* `MultiSourceProblem`: the data of a multi-source network coding problem.
* `MultiSourceProblem.C₁`, …, `MultiSourceProblem.C₅`: the regions (21.27)–(21.31); the first
  one does not depend on the problem.
* `MultiSourceProblem.projY`, `downClosure`: the maps `proj_{Y_S}` and `Λ` of Section 21.4.
* `MultiSourceProblem.outerRegion Γ`: `Λ(proj_{Y_S}(cl(con(Γ ∩ C₁₂₃)) ∩ C₄ ∩ C₅))`.
* `MultiSourceProblem.rPrime`: the region `R'` of Definition 21.4.
* `MultiSourceProblem.rLP`: the LP bound `R_LP` of (21.39).

## Main statements

* `MultiSourceProblem.rPrime_subset_rLP`: `R' ⊆ R_LP`.
* `MultiSourceProblem.rLP_eq`: `R_LP = Λ(proj_{Y_S}(Γ ∩ C₁ ∩ ⋯ ∩ C₅))`, since `Γ` and the regions
  `C₁`, …, `C₅` are closed and convex.

## Implementation notes

The book assumes that the network is acyclic, that every source node has one source and no input
channel, that a sink has no output channel, and that every source is demanded by some sink. These
assumptions are not fields of `MultiSourceProblem`, since the regions do not need them; they would
be hypotheses of Theorem 21.5. Several sources may be generated at one node, and then `C₂` asks
that the output of the node be a function of all of them.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 21.3–21.5
-/

open Finset
open scoped Matrix

@[expose] public noncomputable section

namespace InfoTheory

universe u v w

/-- The linear functional `h ↦ h_A` on the entropy space, with `h_∅ = 0`. -/
def extendLM {ι : Type*} (A : Finset ι) : EntropySpace ι →ₗ[ℝ] ℝ where
  toFun h := h.extend A
  map_add' h g := by rw [EntropySpace.extend_add, Pi.add_apply]
  map_smul' c h := by
    rw [EntropySpace.extend_smul, Pi.smul_apply, RingHom.id_apply]

lemma extendLM_apply {ι : Type*} (A : Finset ι) (h : EntropySpace ι) : extendLM A h = h.extend A :=
  rfl

lemma continuous_extend {ι : Type*} [Finite ι] (A : Finset ι) :
    Continuous fun h : EntropySpace ι => h.extend A :=
  (extendLM A).continuous_of_finiteDimensional

/-- **Section 21.3.** A multi-source network coding problem on a network with nodes `V` and
channels `E`: the source `s ∈ σ` is generated at the node `src s`, the sink `t ∈ T` demands the
sources `β t`, and the channel `e` has the rate constraint `R e`. The book's assumptions on the
network, such as acyclicity, are not part of the structure. -/
structure MultiSourceProblem (V : Type u) (E : Type v) (σ : Type w) where
  /-- The node a channel leaves. -/
  tail : E → V
  /-- The node a channel enters. -/
  head : E → V
  /-- The node at which a source is generated. -/
  src : σ → V
  /-- The sink nodes. -/
  T : Finset V
  /-- The sources demanded by a sink. -/
  β : V → Finset σ
  /-- The rate constraint of a channel. -/
  R : E → ℝ

/-- **Section 21.4.** The set `Λ(B)` of the nonnegative vectors inferior to a vector of `B`. -/
def downClosure {σ : Type*} (B : Set (σ → ℝ)) : Set (σ → ℝ) :=
  {ω | 0 ≤ ω ∧ ∃ ω' ∈ B, ω ≤ ω'}

lemma downClosure_mono {σ : Type*} {B B' : Set (σ → ℝ)} (h : B ⊆ B') :
    downClosure B ⊆ downClosure B' :=
  fun _ ⟨h0, ω', hω', hle⟩ => ⟨h0, ω', h hω', hle⟩

section Regions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma convex_shannonRegion : Convex ℝ (shannonRegion ι) := by
  intro h hh g hg a b ha hb _
  have hh' : 0 ≤ elemMatrix ι *ᵥ h := hh
  have hg' : 0 ≤ elemMatrix ι *ᵥ g := hg
  change 0 ≤ elemMatrix ι *ᵥ (a • h + b • g)
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact add_nonneg (smul_nonneg ha hh') (smul_nonneg hb hg')

lemma isClosed_shannonRegion : IsClosed (shannonRegion ι) :=
  isClosed_le continuous_const (Continuous.matrix_mulVec continuous_const continuous_id)

omit [Fintype ι] [DecidableEq ι] in
/-- The vectors on which pairs of coordinates `h_A = h_B` agree form a closed convex set. -/
lemma convex_isClosed_setOf_forall_eq [Finite ι] {κ : Type*} (p : κ → Prop) (A B : κ → Finset ι) :
    Convex ℝ {h : EntropySpace ι | ∀ k, p k → h.extend (A k) = h.extend (B k)} ∧
      IsClosed {h : EntropySpace ι | ∀ k, p k → h.extend (A k) = h.extend (B k)} := by
  have : {h : EntropySpace ι | ∀ k, p k → h.extend (A k) = h.extend (B k)} =
      ⋂ k, ⋂ _ : p k, {h | (extendLM (A k) - extendLM (B k)) h = 0} := by
    ext h
    simp [extendLM_apply, sub_eq_zero]
  rw [this]
  refine ⟨convex_iInter fun k => convex_iInter fun _ =>
    convex_hyperplane (extendLM (A k) - extendLM (B k)).isLinear 0, isClosed_iInter fun k =>
      isClosed_iInter fun _ => isClosed_eq ?_ continuous_const⟩
  exact (extendLM (A k) - extendLM (B k)).continuous_of_finiteDimensional

end Regions

namespace MultiSourceProblem

variable {V : Type u} {σ : Type w} {E : Type v} [DecidableEq V] [Fintype σ] [DecidableEq σ]
  [Fintype E] [DecidableEq E] (P : MultiSourceProblem V E σ)

/-- The random variables `Y_A` and `U_B`, as a subset of the index set `σ ⊕ E`. -/
def vars (A : Finset σ) (B : Finset E) : Finset (σ ⊕ E) := A.disjSum B

/-- The input channels `In(i)` of a node. -/
def inCh (i : V) : Finset E := univ.filter (P.head · = i)

/-- The output channels `Out(i)` of a node. -/
def outCh (i : V) : Finset E := univ.filter (P.tail · = i)

variable (σ E) in
/-- **(21.27).** `h_{Y_S} = ∑_s h_{Y_s}`: the sources are independent. -/
def C₁ : Set (EntropySpace (σ ⊕ E)) :=
  {h | h.extend (vars univ ∅) = ∑ s, h.extend (vars {s} ∅)}

/-- The sources generated at a node. -/
def srcAt (i : V) : Finset σ := univ.filter (P.src · = i)

/-- **(21.28).** `h_{U_{Out(i)} | Y_{S_i}} = 0`: a source node `i` encodes the sources `S_i`
generated at it. In the book every source node has one source, and this is
`h_{U_{Out(s)} | Y_s} = 0`. -/
def C₂ : Set (EntropySpace (σ ⊕ E)) :=
  {h | ∀ s, h.extend (vars (P.srcAt (P.src s)) (P.outCh (P.src s))) =
    h.extend (vars (P.srcAt (P.src s)) ∅)}

/-- **(21.29).** `h_{U_{Out(i)} | U_{In(i)}} = 0` at a node `i` that is neither a source node nor a
sink: it encodes what it receives. -/
def C₃ : Set (EntropySpace (σ ⊕ E)) :=
  {h | ∀ i, i ∉ Set.range P.src → i ∉ P.T →
    h.extend (vars ∅ (P.outCh i ∪ P.inCh i)) = h.extend (vars ∅ (P.inCh i))}

/-- **(21.30).** `h_{U_e} ≤ R_e`: the rate constraints. -/
def C₄ : Set (EntropySpace (σ ⊕ E)) :=
  {h | ∀ e, h.extend (vars ∅ {e}) ≤ P.R e}

/-- **(21.31).** `h_{Y_{β(t)} | U_{In(t)}} = 0`: a sink decodes the sources it demands. -/
def C₅ : Set (EntropySpace (σ ⊕ E)) :=
  {h | ∀ t ∈ P.T, h.extend (vars (P.β t) (P.inCh t)) = h.extend (vars ∅ (P.inCh t))}

/-- **Section 21.4.** The projection `proj_{Y_S}` on the coordinates `h_{Y_s}`. -/
def projY (h : EntropySpace (σ ⊕ E)) : σ → ℝ := fun s => h.extend (vars {s} ∅)

/-- The region `Λ(proj_{Y_S}(cl(con(Γ ∩ C₁₂₃)) ∩ C₄ ∩ C₅))` obtained from a region `Γ` of the
entropy space. -/
def outerRegion (Γ : Set (EntropySpace (σ ⊕ E))) : Set (σ → ℝ) :=
  downClosure (projY '' (closure (convexHull ℝ (Γ ∩ C₁ σ E ∩ P.C₂ ∩ P.C₃)) ∩ P.C₄ ∩ P.C₅))

/-- **Definition 21.4.** The region `R'`, (21.32), from the region `Γ**` of the entropy functions of
random variables with finite alphabets. -/
def rPrime : Set (σ → ℝ) := P.outerRegion (entropicRegion (σ ⊕ E))

/-- **(21.39).** The LP bound `R_LP`, from the region `Γ` of the vectors satisfying the basic
inequalities. -/
def rLP : Set (σ → ℝ) := P.outerRegion (shannonRegion (σ ⊕ E))

omit [DecidableEq σ] in
lemma outerRegion_mono {Γ Γ' : Set (EntropySpace (σ ⊕ E))} (h : Γ ⊆ Γ') :
    P.outerRegion Γ ⊆ P.outerRegion Γ' := by
  refine downClosure_mono (Set.image_mono ?_)
  gcongr

/-- **Section 21.5.** `R' ⊆ R_LP`, since `Γ** ⊆ Γ`. -/
theorem rPrime_subset_rLP : P.rPrime ⊆ P.rLP :=
  P.outerRegion_mono entropicRegion_subset_shannonRegion

/-! ### `R_LP` is cut out by linear inequalities -/

omit [DecidableEq σ] [Fintype E] [DecidableEq E] in
variable (σ E) in
lemma convex_isClosed_C₁ [Finite E] : Convex ℝ (C₁ σ E) ∧ IsClosed (C₁ σ E) := by
  set L := extendLM (vars (univ : Finset σ) (∅ : Finset E)) - ∑ s, extendLM (vars {s} ∅)
  have : C₁ σ E = {h | L h = 0} := by
    ext h
    simp [C₁, L, extendLM_apply, sub_eq_zero]
  rw [this]
  exact ⟨convex_hyperplane L.isLinear 0,
    isClosed_eq L.continuous_of_finiteDimensional continuous_const⟩

/-- **Section 21.5.** `R_LP` involves only finitely many linear constraints:
`R_LP = Λ(proj_{Y_S}(Γ ∩ C₁ ∩ ⋯ ∩ C₅))`. -/
theorem rLP_eq : P.rLP =
    downClosure (projY '' (shannonRegion (σ ⊕ E) ∩ C₁ σ E ∩ P.C₂ ∩ P.C₃ ∩ P.C₄ ∩ P.C₅)) := by
  have h₂ := convex_isClosed_setOf_forall_eq (fun _ : σ => True)
    (fun s : σ => vars (P.srcAt (P.src s)) (P.outCh (P.src s)))
    (fun s : σ => vars (P.srcAt (P.src s)) ∅)
  have h₃ := convex_isClosed_setOf_forall_eq (fun i => i ∉ Set.range P.src ∧ i ∉ P.T)
    (fun i => vars (∅ : Finset σ) (P.outCh i ∪ P.inCh i)) (fun i => vars (∅ : Finset σ) (P.inCh i))
  have e₂ : P.C₂ = {h : EntropySpace (σ ⊕ E) | ∀ s, True →
      h.extend (vars (P.srcAt (P.src s)) (P.outCh (P.src s))) =
        h.extend (vars (P.srcAt (P.src s)) ∅)} := by
    ext h
    simp [C₂]
  have e₃ : P.C₃ = {h : EntropySpace (σ ⊕ E) | ∀ i, i ∉ Set.range P.src ∧ i ∉ P.T →
      h.extend (vars ∅ (P.outCh i ∪ P.inCh i)) = h.extend (vars ∅ (P.inCh i))} := by
    ext h
    simp only [C₃, Set.mem_ofPred_eq, and_imp]
  have h₁ := convex_isClosed_C₁ σ E
  have hconv : Convex ℝ (shannonRegion (σ ⊕ E) ∩ C₁ σ E ∩ P.C₂ ∩ P.C₃) := by
    rw [e₂, e₃]
    exact ((convex_shannonRegion.inter h₁.1).inter h₂.1).inter h₃.1
  have hclosed : IsClosed (shannonRegion (σ ⊕ E) ∩ C₁ σ E ∩ P.C₂ ∩ P.C₃) := by
    rw [e₂, e₃]
    exact ((isClosed_shannonRegion.inter h₁.2).inter h₂.2).inter h₃.2
  rw [rLP, outerRegion, hconv.convexHull_eq, hclosed.closure_eq]

end MultiSourceProblem

end InfoTheory
