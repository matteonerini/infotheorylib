/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.IMeasure.CondMutIndep
public import InfoTheoryLib.IMeasure.Markov
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Markov random fields and the I-Measure

Random variables `Xₗ` indexed by the vertices of a graph `G` form a Markov random field if, for
every cutset `U`, the blocks of variables on the components of `G \ U` are mutually independent
conditioning on `X_U`. Each cutset gives an FCMI `[U]`, and the images of these FCMIs make up the
Type II atoms, those `A` for which removing the complemented indices `U_A` disconnects `G`. So the
`Xₗ` form a Markov random field if and only if `μ*` vanishes on the Type II atoms
(Theorem 12.25).

For a Markov chain `X₁ → ⋯ → Xₙ`, the Type I atoms are those whose uncomplemented indices form an
interval `{l, …, u}`, and `μ*` takes the value `I(X_l; X_u | X_{U_A}) ≥ 0` there, so `μ*` is
nonnegative (Theorem 12.30). This holds both for a Markov random field on a path and for a Markov
chain in the sense of Definition 2.6.

## Main definitions

* `ReachableOutside G U l l'`: `l` and `l'` are connected in `G \ U`.
* `componentsOutside G U`: the vertex sets of the components of `G \ U`, of which there are
  `s(U)`.
* `cutFCMI G U`: the FCMI `[U]`.
* `IsMarkovField μ X G`: the `Xₗ` form a Markov random field represented by `G`.
* `IsTypeTwoAtom G A`: `A` is a Type II atom.
* `IsInterval s`: the indices in `s` are consecutive.

## Main statements

* `isMarkovField_iff`: **Theorem 12.25**.
* `not_reachableOutside_union_sdiff`: **Proposition 12.26**.
* `isTypeTwoAtom_pathGraph_iff`, `not_isTypeTwoAtom_pathGraph_iff`: **Lemma 12.29**.
* `IsMarkovField.iMeasure_nonneg_pathGraph`, `IsMarkovChain.iMeasure_nonneg`: **Theorem 12.30**.
* `IsMarkovChain.iMeasure_Icc`: (12.103)–(12.112), the value of `μ*` on a Type I atom.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 12.3 and 12.4
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Components of `G \ U` -/

section Graph

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `l` and `l'` are connected in the graph `G \ U` obtained from `G` by removing the vertices in
`U`: some walk from `l` to `l'` avoids `U`. -/
def ReachableOutside (G : SimpleGraph ι) (U : Finset ι) (l l' : ι) : Prop :=
  ∃ p : G.Walk l l', ∀ v ∈ p.support, v ∉ U

namespace ReachableOutside

variable {G : SimpleGraph ι} {U U' : Finset ι} {l l' m : ι}

omit [Fintype ι] [DecidableEq ι] in
lemma refl (hl : l ∉ U) : ReachableOutside G U l l :=
  ⟨.nil, fun v hv => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    rwa [hv]⟩

omit [Fintype ι] [DecidableEq ι] in
lemma symm (h : ReachableOutside G U l l') : ReachableOutside G U l' l := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun v hv => hp v (by simpa [SimpleGraph.Walk.support_reverse] using hv)⟩

omit [Fintype ι] [DecidableEq ι] in
lemma trans (h₁ : ReachableOutside G U l m) (h₂ : ReachableOutside G U m l') :
    ReachableOutside G U l l' := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p.append q, fun v hv =>
    ((SimpleGraph.Walk.mem_support_append_iff p q).1 hv).elim (hp v) (hq v)⟩

omit [Fintype ι] [DecidableEq ι] in
lemma of_adj (h : G.Adj l l') (hl : l ∉ U) (hl' : l' ∉ U) : ReachableOutside G U l l' :=
  ⟨.cons h .nil, fun v hv => by
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> assumption⟩

omit [Fintype ι] [DecidableEq ι] in
lemma notMem_left (h : ReachableOutside G U l l') : l ∉ U :=
  let ⟨p, hp⟩ := h
  hp l p.start_mem_support

omit [Fintype ι] [DecidableEq ι] in
lemma notMem_right (h : ReachableOutside G U l l') : l' ∉ U :=
  let ⟨p, hp⟩ := h
  hp l' p.end_mem_support

omit [Fintype ι] [DecidableEq ι] in
/-- Removing fewer vertices keeps vertices connected. -/
lemma mono (hUU' : U ⊆ U') (h : ReachableOutside G U' l l') : ReachableOutside G U l l' :=
  let ⟨p, hp⟩ := h
  ⟨p, fun v hv hvU => hp v hv (hUU' hvU)⟩

end ReachableOutside

open Classical in
/-- The vertex set of the component of `l` in `G \ U`. -/
def componentOutside (G : SimpleGraph ι) (U : Finset ι) (l : ι) : Finset ι :=
  univ.filter (ReachableOutside G U l)

/-- The vertex sets `V₁(U), …, V_{s(U)}(U)` of the components of `G \ U`; `s(U)` is their number,
and `U` is a *cutset* if `s(U) > 1`. -/
def componentsOutside (G : SimpleGraph ι) (U : Finset ι) : Finset (Finset ι) :=
  Uᶜ.image (componentOutside G U)

variable {G : SimpleGraph ι} {U : Finset ι} {l l' : ι}

omit [DecidableEq ι] in
lemma mem_componentOutside : l' ∈ componentOutside G U l ↔ ReachableOutside G U l l' := by
  classical
  simp [componentOutside]

omit [DecidableEq ι] in
lemma componentOutside_eq_iff (hl : l ∉ U) :
    componentOutside G U l = componentOutside G U l' ↔ ReachableOutside G U l l' := by
  constructor
  · intro h
    have : l ∈ componentOutside G U l' := h ▸ mem_componentOutside.2 (.refl hl)
    exact (mem_componentOutside.1 this).symm
  · intro h
    ext m
    rw [mem_componentOutside, mem_componentOutside]
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

/-- `s(U) > 1` if and only if two vertices outside `U` are not connected in `G \ U`. -/
lemma one_lt_card_componentsOutside :
    1 < #(componentsOutside G U) ↔ ∃ l ∉ U, ∃ l' ∉ U, ¬ReachableOutside G U l l' := by
  rw [one_lt_card]
  simp only [componentsOutside, mem_image, mem_compl]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, _, ⟨l', hl', rfl⟩, hne⟩
    exact ⟨l, hl, l', hl', fun h => hne ((componentOutside_eq_iff hl).2 h)⟩
  · rintro ⟨l, hl, l', hl', h⟩
    exact ⟨_, ⟨l, hl, rfl⟩, _, ⟨l', hl', rfl⟩, fun he => h ((componentOutside_eq_iff hl).1 he)⟩

/-- The FCMI `[U]`: the blocks `X_{V₁(U)}, …, X_{V_{s(U)}(U)}` are mutually independent
conditioning on `X_U`. -/
def cutFCMI (G : SimpleGraph ι) (U : Finset ι) : FCMI ι :=
  ⟨U, componentsOutside G U⟩

lemma isFull_cutFCMI : (cutFCMI G U).IsFull := by
  refine ⟨fun q hq => ?_, fun q hq q' hq' hne => ?_, ?_⟩
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hq
    exact disjoint_right.2 fun m hm => (mem_componentOutside.1 hm).notMem_right
  · obtain ⟨l, hl, rfl⟩ := mem_image.1 (mem_coe.1 hq)
    obtain ⟨l', -, rfl⟩ := mem_image.1 (mem_coe.1 hq')
    refine disjoint_left.2 fun m hm hm' => hne ?_
    exact (componentOutside_eq_iff (mem_compl.1 hl)).2
      ((mem_componentOutside.1 hm).trans (mem_componentOutside.1 hm').symm)
  · ext m
    simp only [mem_union, mem_biUnion, mem_univ, iff_true]
    by_cases hm : m ∈ U
    · exact Or.inl hm
    · exact Or.inr ⟨componentOutside G U m, mem_image_of_mem _ (mem_compl.2 hm),
        mem_componentOutside.2 (.refl hm)⟩

omit [Fintype ι] in
/-- **Proposition 12.26.** If the sets `Qᵢ` are disconnected from each other in `G \ C`, and
`Wᵢ ⊆ Qᵢ`, then the sets `Wᵢ` are disconnected from each other in `G \ (C ∪ ⋃ (Qᵢ - Wᵢ))`. -/
theorem not_reachableOutside_union_sdiff {κ : Type*} [Fintype κ] {C : Finset ι}
    {Q W : κ → Finset ι} (hW : ∀ j, W j ⊆ Q j)
    (hQ : ∀ i j, i ≠ j → ∀ l ∈ Q i, ∀ l' ∈ Q j, ¬ReachableOutside G C l l') :
    ∀ i j, i ≠ j → ∀ l ∈ W i, ∀ l' ∈ W j,
      ¬ReachableOutside G (C ∪ univ.biUnion fun j => Q j \ W j) l l' :=
  fun i j hij l hl l' hl' h => hQ i j hij l (hW i hl) l' (hW j hl') (h.mono subset_union_left)

end Graph

/-! ### Markov random fields -/

section Field

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, Fintype (A i)] {μ : Ω → ℝ} {X : ∀ i, Ω → A i} {G : SimpleGraph ι}

/-- **Definition 12.23 (Markov random field).** The `Xₗ` form a *Markov random field* represented
by the graph `G` (the global Markov property) if, for every cutset `U` of `G`, the blocks of
variables on the components of `G \ U` are mutually independent conditioning on `X_U`, (12.89). -/
def IsMarkovField (μ : Ω → ℝ) (X : ∀ i, Ω → A i) (G : SimpleGraph ι) : Prop :=
  ∀ U : Finset ι, 1 < #(componentsOutside G U) → (cutFCMI G U).Holds μ X

/-- **Definition 12.24.** A nonempty atom `A` is a *Type II* atom if `G \ U_A` is disconnected,
where `U_A` is the set of indices complemented in `A`, (12.73); otherwise it is a *Type I* atom. -/
def IsTypeTwoAtom (G : SimpleGraph ι) (a : NAtom ι) : Prop :=
  1 < #(componentsOutside G a.1ᶜ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
/-- (12.91): the image of the FCMIs of a graph is the set of Type II atoms. -/
lemma fcmiImage_cutFCMI :
    fcmiImage {K | ∃ U, 1 < #(componentsOutside G U) ∧ K = cutFCMI G U} =
      {a | IsTypeTwoAtom G a} := by
  ext a
  simp only [fcmiImage, Set.mem_iUnion, mem_coe]
  constructor
  · rintro ⟨K, ⟨U, -, rfl⟩, ha⟩
    -- (12.96)–(12.99)
    rw [FCMI.mem_image_iff isFull_cutFCMI] at ha
    obtain ⟨q, hq, q', hq', hqq', ha⟩ := ha
    obtain ⟨l₀, hl₀, rfl⟩ := mem_image.1 hq
    obtain ⟨l₀', -, rfl⟩ := mem_image.1 hq'
    simp only [mem_sdiff, mem_inter, mem_tilde, not_exists, not_and] at ha
    obtain ⟨⟨⟨l, hl, hla⟩, ⟨l', hl', hla'⟩⟩, haU⟩ := ha
    change IsTypeTwoAtom G a
    rw [IsTypeTwoAtom, one_lt_card_componentsOutside]
    refine ⟨l, by simpa using hla, l', by simpa using hla', fun h => hqq' ?_⟩
    have h' := h.mono fun x hx => mem_compl.2 (haU x hx)
    exact (componentOutside_eq_iff (mem_compl.1 hl₀)).2
      ((mem_componentOutside.1 hl).trans (h'.trans (mem_componentOutside.1 hl').symm))
  · -- (12.92)–(12.95)
    intro ha
    change IsTypeTwoAtom G a at ha
    refine ⟨cutFCMI G a.1ᶜ, ⟨a.1ᶜ, ha, rfl⟩, ?_⟩
    rw [FCMI.mem_image_iff isFull_cutFCMI]
    obtain ⟨l, hl, l', hl', h⟩ := one_lt_card_componentsOutside.1 ha
    refine ⟨componentOutside G a.1ᶜ l, mem_image_of_mem _ (mem_compl.2 hl),
      componentOutside G a.1ᶜ l', mem_image_of_mem _ (mem_compl.2 hl'),
      fun he => h ((componentOutside_eq_iff hl).1 he), ?_⟩
    simp only [mem_sdiff, mem_inter, mem_tilde, not_exists, not_and]
    exact ⟨⟨⟨l, mem_componentOutside.2 (.refl hl), by simpa using hl⟩,
      ⟨l', mem_componentOutside.2 (.refl hl'), by simpa using hl'⟩⟩,
      fun x hx hxa => mem_compl.1 hx hxa⟩

/-- **Theorem 12.25.** The `Xₗ` form a Markov random field represented by `G` if and only if `μ*`
vanishes on all the Type II atoms. -/
theorem isMarkovField_iff (hμ : IsPMF μ) :
    IsMarkovField μ X G ↔ ∀ a : NAtom ι, IsTypeTwoAtom G a → iMeasure μ X {a} = 0 := by
  have hfull : ∀ K ∈ {K | ∃ U, 1 < #(componentsOutside G U) ∧ K = cutFCMI G U},
      FCMI.IsFull K := by
    rintro K ⟨U, -, rfl⟩
    exact isFull_cutFCMI
  have hMF : IsMarkovField μ X G ↔
      ∀ K ∈ {K | ∃ U, 1 < #(componentsOutside G U) ∧ K = cutFCMI G U}, K.Holds μ X :=
    ⟨fun h K ⟨U, hU, hK⟩ => hK ▸ h U hU, fun h U hU => h _ ⟨U, hU, rfl⟩⟩
  rw [hMF, FCMI.holds_set_iff hμ hfull, fcmiImage_cutFCMI]
  rfl

end Field

/-! ### Markov chains -/

section Chain

variable {n : ℕ}

/-- The indices in `s` are consecutive: `s` contains every index between two of its elements. -/
def IsInterval (s : Finset (Fin n)) : Prop :=
  ∀ l ∈ s, ∀ u ∈ s, ∀ c, l ≤ c → c ≤ u → c ∈ s

/-- A nonempty set of consecutive indices is an interval `{l, …, u}`. -/
lemma isInterval_iff_eq_Icc {s : Finset (Fin n)} (hs : s.Nonempty) :
    IsInterval s ↔ ∃ l u, l ≤ u ∧ s = Icc l u := by
  constructor
  · intro h
    refine ⟨s.min' hs, s.max' hs, min'_le_max' s hs, Finset.ext fun c => ⟨fun hc => ?_, ?_⟩⟩
    · exact mem_Icc.2 ⟨min'_le s c hc, le_max' s c hc⟩
    · intro hc
      rw [mem_Icc] at hc
      exact h _ (min'_mem s hs) _ (max'_mem s hs) c hc.1 hc.2
  · rintro ⟨l, u, -, rfl⟩ a ha b hb c h₁ h₂
    exact mem_Icc.2 ⟨(mem_Icc.1 ha).1.trans h₁, h₂.trans (mem_Icc.1 hb).2⟩

/-- A walk on the path `0 - 1 - ⋯ - (n-1)` passes through every vertex between its ends. -/
lemma mem_support_pathGraph_of_le_of_le : ∀ {u v : Fin n}
    (p : (SimpleGraph.pathGraph n).Walk u v) {c : Fin n}, u ≤ c → c ≤ v → c ∈ p.support
  | _, _, .nil, c, h₁, h₂ => by
    rw [le_antisymm h₂ h₁, SimpleGraph.Walk.support_nil]
    exact List.mem_singleton_self _
  | u, _, .cons h p, c, h₁, h₂ => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons]
    by_cases hc : c = u
    · exact Or.inl hc
    · refine Or.inr (mem_support_pathGraph_of_le_of_le p ?_ h₂)
      have hlt : u < c := lt_of_le_of_ne h₁ (Ne.symm hc)
      rw [SimpleGraph.pathGraph_adj] at h
      rw [Fin.lt_def] at hlt
      rw [Fin.le_def]
      omega

/-- On a path, `l ≤ l'` are connected in `G \ U` if and only if no index between them is in `U`. -/
lemma reachableOutside_pathGraph_iff {U : Finset (Fin n)} {l l' : Fin n} (hll' : l ≤ l') :
    ReachableOutside (SimpleGraph.pathGraph n) U l l' ↔ ∀ c, l ≤ c → c ≤ l' → c ∉ U := by
  constructor
  · rintro ⟨p, hp⟩ c h₁ h₂
    exact hp c (mem_support_pathGraph_of_le_of_le p h₁ h₂)
  · intro h
    have key : ∀ m : ℕ, ∀ hm : l.val + m < n, l.val + m ≤ l'.val →
        ReachableOutside (SimpleGraph.pathGraph n) U l ⟨l.val + m, hm⟩ := by
      intro m
      induction m with
      | zero =>
        intro hm _
        have e : (⟨l.val + 0, hm⟩ : Fin n) = l := Fin.ext rfl
        rw [e]
        exact .refl (h l le_rfl hll')
      | succ m ih =>
        intro hm hle
        have h₁ := ih (by omega) (by omega)
        refine h₁.trans (.of_adj (SimpleGraph.pathGraph_adj.2 (Or.inl rfl)) ?_ ?_)
        · exact h _ (by rw [Fin.le_def]; simp) (by rw [Fin.le_def]; simp; omega)
        · exact h _ (by rw [Fin.le_def]; simp) (by rw [Fin.le_def]; simp; omega)
    have e : (⟨l.val + (l'.val - l.val), by omega⟩ : Fin n) = l' := by
      ext
      simp only
      rw [Fin.le_def] at hll'
      omega
    rw [← e]
    exact key _ _ (by omega)

/-- **Lemma 12.29.** For the Markov chain represented by a path, an atom is a Type II atom if and
only if the indices that are not complemented in it are not consecutive. -/
theorem isTypeTwoAtom_pathGraph_iff (a : NAtom (Fin n)) :
    IsTypeTwoAtom (SimpleGraph.pathGraph n) a ↔ ¬IsInterval a.1 := by
  rw [IsTypeTwoAtom, one_lt_card_componentsOutside]
  constructor
  · rintro ⟨l, hl, l', hl', h⟩ hint
    rw [notMem_compl] at hl hl'
    rcases le_total l l' with hle | hle
    · exact h ((reachableOutside_pathGraph_iff hle).2 fun c h₁ h₂ =>
        notMem_compl.2 (hint l hl l' hl' c h₁ h₂))
    · exact h ((reachableOutside_pathGraph_iff hle).2 fun c h₁ h₂ =>
        notMem_compl.2 (hint l' hl' l hl c h₁ h₂)).symm
  · intro hint
    simp only [IsInterval, not_forall] at hint
    obtain ⟨l, hl, u, hu, c, h₁, h₂, hc⟩ := hint
    refine ⟨l, notMem_compl.2 hl, u, notMem_compl.2 hu, fun h => ?_⟩
    exact (reachableOutside_pathGraph_iff (h₁.trans h₂)).1 h c h₁ h₂ (mem_compl.2 hc)

/-- **Lemma 12.29**, (12.102): an atom is a Type I atom if and only if its uncomplemented indices
form an interval `{l, l + 1, …, u}`. -/
theorem not_isTypeTwoAtom_pathGraph_iff (a : NAtom (Fin n)) :
    ¬IsTypeTwoAtom (SimpleGraph.pathGraph n) a ↔ ∃ l u, l ≤ u ∧ a.1 = Icc l u := by
  rw [isTypeTwoAtom_pathGraph_iff, not_not, isInterval_iff_eq_Icc a.2]

variable {Ω : Type*} [Fintype Ω] {A : Fin n → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}
  {X : ∀ i, Ω → A i}

/-- (12.107)–(12.110): if `μ*` vanishes on the atoms whose indices are not consecutive, then its
value on the atom with indices `{l, …, u}` is `I(X_l; X_u | X_{U_A})`. -/
theorem iMeasure_Icc_eq_condMutualInfo (hμ : IsPMF μ)
    (h0 : ∀ a : NAtom (Fin n), ¬IsInterval a.1 → iMeasure μ X {a} = 0) {l u : Fin n}
    (hlu : l < u) :
    iMeasure μ X {⟨Icc l u, nonempty_Icc.2 hlu.le⟩} = I[X l : X u | blockRV X (Icc l u)ᶜ ; μ] := by
  rw [← iMeasure_inter_sdiff hμ (rvEquiv_blockRV_singleton X l) (rvEquiv_blockRV_singleton X u)
    (RVEquiv.refl _), (isSignedMeasure_iMeasure μ X).eq_sum_singleton
    ((tilde {l} ∩ tilde {u}) \ tilde (Icc l u)ᶜ)]
  symm
  refine sum_eq_single_of_mem _ ?_ fun b hb hne => h0 b fun hint => hne ?_
  · simp only [mem_sdiff, mem_inter, mem_tilde, mem_singleton, exists_eq_left, mem_compl,
      not_exists, not_and]
    exact ⟨⟨mem_Icc.2 ⟨le_rfl, hlu.le⟩, mem_Icc.2 ⟨hlu.le, le_rfl⟩⟩, fun x hx => hx⟩
  · simp only [mem_sdiff, mem_inter, mem_tilde, mem_singleton, exists_eq_left, mem_compl,
      not_exists, not_and] at hb
    obtain ⟨⟨hl, hu⟩, hsub⟩ := hb
    refine Subtype.ext (Finset.ext fun c => ⟨fun hc => ?_, fun hc => ?_⟩)
    · by_contra hcI
      exact hsub c hcI hc
    rw [mem_Icc] at hc
    exact hint l hl u hu c hc.1 hc.2

/-- (12.111)–(12.113): if `μ*` vanishes on the atoms whose indices are not consecutive, then `μ*`
is nonnegative. -/
theorem iMeasure_nonneg_of_isInterval (hμ : IsPMF μ)
    (h0 : ∀ a : NAtom (Fin n), ¬IsInterval a.1 → iMeasure μ X {a} = 0)
    (F : Finset (NAtom (Fin n))) : 0 ≤ iMeasure μ X F := by
  rw [(isSignedMeasure_iMeasure μ X).eq_sum_singleton]
  refine sum_nonneg fun a _ => ?_
  by_cases ha : IsInterval a.1
  · obtain ⟨l, u, hlu, he⟩ := (isInterval_iff_eq_Icc a.2).1 ha
    rcases hlu.lt_or_eq with hlt | rfl
    · have e : a = ⟨Icc l u, nonempty_Icc.2 hlt.le⟩ := Subtype.ext he
      rw [e, iMeasure_Icc_eq_condMutualInfo hμ h0 hlt]
      exact condMutualInfo_nonneg hμ _ _ _
    · refine iMeasure_atom_nonneg hμ a ?_
      rw [he, Icc_self, card_singleton]
      norm_num
  · rw [h0 a ha]

/-- **Theorem 12.30**, for a Markov random field on a path: `μ*` is nonnegative. -/
theorem IsMarkovField.iMeasure_nonneg_pathGraph (hμ : IsPMF μ)
    (h : IsMarkovField μ X (SimpleGraph.pathGraph n)) (F : Finset (NAtom (Fin n))) :
    0 ≤ iMeasure μ X F :=
  iMeasure_nonneg_of_isInterval hμ
    (fun a ha => (isMarkovField_iff hμ).1 h a ((isTypeTwoAtom_pathGraph_iff a).2 ha)) F

end Chain

section MarkovChain

variable {n : ℕ} {Ω : Type*} [Fintype Ω] {A : ℕ → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}
  {Z : ∀ i, Ω → A i}

/-- For a Markov chain `X₁ → ⋯ → Xₙ` (Definition 2.6), `μ*` vanishes on the atoms whose
uncomplemented indices are not consecutive, the Type II atoms of Lemma 12.29. -/
theorem IsMarkovChain.iMeasure_eq_zero (hμ : IsPMF μ) (h : IsMarkovChain μ Z n)
    (a : NAtom (Fin n)) (ha : ¬IsInterval a.1) : iMeasure μ (fun i : Fin n => Z i) {a} = 0 := by
  simp only [IsInterval, not_forall] at ha
  obtain ⟨l, hl, u, hu, c, h₁, h₂, hc⟩ := ha
  have hlc : l < c := lt_of_le_of_ne h₁ fun e => hc (e ▸ hl)
  have hcu : c < u := lt_of_le_of_ne h₂ fun e => hc (e ▸ hu)
  have hn : 2 ≤ n := by
    have := u.2
    rw [Fin.lt_def] at hlc hcu
    omega
  set f := blockEntropy μ (fun i : Fin n => Z i) with hfdef
  have hf : IsPolymatroid f := isPolymatroid_blockEntropy hμ
  set G₁ := a.1.filter (· < c) with hG₁
  set G₂ := a.1.filter (c < ·) with hG₂
  have hU : a.1 = G₁ ∪ G₂ := by
    ext m
    simp only [hG₁, hG₂, mem_union, mem_filter]
    constructor
    · intro hm
      rcases lt_trichotomy m c with h' | rfl | h'
      · exact Or.inl ⟨hm, h'⟩
      · exact absurd hm hc
      · exact Or.inr ⟨hm, h'⟩
    · rintro (⟨hm, -⟩ | ⟨hm, -⟩) <;> exact hm
  have hd : Disjoint G₁ G₂ := disjoint_filter.2 fun m _ h₁ h₂ => lt_asymm h₁ h₂
  -- the Markov chain splits at `c`: `I(X_{< c}; X_{> c} | X_c) = 0`
  set D := a.1ᶜ.filter (· < c) with hD
  set E := a.1ᶜ.filter (c < ·) with hE
  have hC : a.1ᶜ = {c} ∪ D ∪ E := by
    ext m
    simp only [hD, hE, mem_union, mem_filter, mem_singleton, mem_compl]
    constructor
    · intro hm
      rcases lt_trichotomy m c with h' | rfl | h'
      · exact Or.inl (Or.inr ⟨hm, h'⟩)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨hm, h'⟩
    · rintro ((rfl | ⟨hm, -⟩) | ⟨hm, -⟩)
      exacts [hc, hm, hm]
  have hP : G₁ ∪ D = univ.filter (· < c) := by
    ext m
    simp only [hG₁, hD, mem_union, mem_filter, mem_compl, mem_univ, true_and]
    tauto
  have hF : G₂ ∪ E = univ.filter (c < ·) := by
    ext m
    simp only [hG₂, hE, mem_union, mem_filter, mem_compl, mem_univ, true_and]
    tauto
  have hM := h.blockEntropy_fin hμ hn (P := univ.filter (· < c)) (S := {c})
    (F := univ.filter (c < ·)) (b := c) (mem_singleton_self c)
    (fun i hi => (mem_filter.1 hi).2) (fun i hi => (mem_singleton.1 hi).symm.le)
    (fun i hi => (mem_filter.1 hi).2.le)
  have hle := hf.condInfo_le_condInfo_union G₁ G₂ {c} D E
  rw [← hC, hP, hF] at hle
  rw [← hfdef] at hM
  have hI : condInfo f G₁ G₂ a.1ᶜ = 0 := by
    have h0 := hf.condInfo_nonneg G₁ G₂ a.1ᶜ
    simp only [condInfo, ← union_assoc] at hle hM h0 ⊢
    linarith
  have hsingle : ({a} : Finset (NAtom (Fin n))) =
      (G₁ ∪ G₂).inf (fun l => tilde {l}) \ tilde a.1ᶜ := by
    rw [singleton_eq_inf_tilde, inf'_eq_inf, ← hU]
  rw [hsingle]
  exact iMeasure_inf_sdiff_eq_zero_of_condInfo hμ hd ⟨l, mem_filter.2 ⟨hl, hlc⟩⟩
    ⟨u, mem_filter.2 ⟨hu, hcu⟩⟩ hI

/-- **Theorem 12.30.** For a Markov chain `X₁ → X₂ → ⋯ → Xₙ`, `μ*` is nonnegative. -/
theorem IsMarkovChain.iMeasure_nonneg (hμ : IsPMF μ) (h : IsMarkovChain μ Z n)
    (F : Finset (NAtom (Fin n))) : 0 ≤ iMeasure μ (fun i : Fin n => Z i) F :=
  iMeasure_nonneg_of_isInterval hμ (fun a ha => h.iMeasure_eq_zero hμ a ha) F

/-- (12.103)–(12.104): for a Markov chain, the value of `μ*` on the Type I atom with
uncomplemented indices `{l, …, u}`, `l < u`, is `I(X_l; X_u | X_{U_A})`. -/
theorem IsMarkovChain.iMeasure_Icc (hμ : IsPMF μ) (h : IsMarkovChain μ Z n) {l u : Fin n}
    (hlu : l < u) :
    iMeasure μ (fun i : Fin n => Z i) {⟨Icc l u, nonempty_Icc.2 hlu.le⟩} =
      I[Z l : Z u | blockRV (fun i : Fin n => Z i) (Icc l u)ᶜ ; μ] :=
  iMeasure_Icc_eq_condMutualInfo hμ (fun a ha => h.iMeasure_eq_zero hμ a ha) hlu

end MarkovChain

end InfoTheory
