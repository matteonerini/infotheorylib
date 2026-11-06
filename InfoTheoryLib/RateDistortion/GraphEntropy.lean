/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.SideInfoFunction

/-!
# Graph entropy and the Orlitsky–Roche theorem

This file defines the conditional graph entropy of Körner, and the characteristic graph of
Witsenhausen, and proves the Orlitsky–Roche theorem: the optimal rate for computing `Z = g(X, Y)`
losslessly at a decoder with side information `Y` is `H_G(X | Y)`.

## Main definitions

* `IsMaxIndep`, `maxIndepSets`: the maximally independent sets `Γ(G)` of a graph.
* `IsGraphKernel`: `p(w | x)` with `W ∈ Γ(G)` and `X ∈ W`.
* `condGraphEntropy`, `graphEntropy`: `H_G(X | Y)` and `H_G(X)`.
* `charGraph`: the characteristic graph of `(X, Y, g)`.

## Main statements

* `exists_condGraphEntropy_eq`: the minimum is attained.
* `funLosslessRate_eq_condGraphEntropy`: **the single-letter form of the Orlitsky–Roche theorem**.
* `losslessFunBits_eq_condGraphEntropy`: **the Orlitsky–Roche theorem**.
* `condGraphEntropy_bot`, `condGraphEntropy_top`: the graphs with no edges and with all the edges.

## Implementation notes

In the notes, the nodes of the characteristic graph are the support of `X`. Here they are all of
`𝒳`: a letter of probability `0` is isolated, so it lies in every maximally independent set, and
this does not change the graph entropy.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α γ β υ : Type*} [Fintype α]

/-! ### Maximally independent sets -/

section Graph

/-- **Lecture 22 of [elgamal2010], page 22-6.** A set of nodes is maximally independent if it is
independent and is not a proper subset of another independent set. -/
def IsMaxIndep (G : SimpleGraph α) (w : Finset α) : Prop :=
  G.IsIndepSet (w : Set α) ∧ ∀ w' : Finset α, G.IsIndepSet (w' : Set α) → w ⊆ w' → w' = w

open Classical in
/-- **Lecture 22 of [elgamal2010], page 22-6.** The collection `Γ(G)` of maximally independent sets
of a graph. -/
def maxIndepSets (G : SimpleGraph α) : Finset (Finset α) := univ.filter (IsMaxIndep G)

omit [Fintype α] in
@[simp]
lemma mem_maxIndepSets [Fintype α] {G : SimpleGraph α} {w : Finset α} :
    w ∈ maxIndepSets G ↔ IsMaxIndep G w := by
  simp [maxIndepSets]

/-- Every independent set is contained in a maximally independent set. -/
lemma exists_maxIndep_superset (G : SimpleGraph α) {S : Finset α}
    (hS : G.IsIndepSet (S : Set α)) : ∃ w ∈ maxIndepSets G, S ⊆ w := by
  classical
  have hmem : S ∈ univ.filter fun w : Finset α => G.IsIndepSet (w : Set α) := by simpa using hS
  obtain ⟨b, hle, hb⟩ := Finset.exists_le_maximal _ hmem
  have hb1 : G.IsIndepSet (b : Set α) := by simpa using hb.prop
  refine ⟨b, mem_maxIndepSets.2 ⟨hb1, fun w' hw' hbw => ?_⟩, hle⟩
  exact le_antisymm (hb.le_of_ge (by simpa using hw') hbw) hbw

omit [Fintype α] in
/-- A singleton is independent. -/
lemma isIndepSet_singleton (G : SimpleGraph α) (x : α) :
    G.IsIndepSet (({x} : Finset α) : Set α) := by
  intro a ha b hb hab
  simp only [coe_singleton, Set.mem_singleton_iff] at ha hb
  exact absurd (ha.trans hb.symm) hab

/-- Every node lies in a maximally independent set. -/
lemma exists_mem_maxIndepSets (G : SimpleGraph α) (x : α) : ∃ w ∈ maxIndepSets G, x ∈ w :=
  let ⟨w, hw, hx⟩ := exists_maxIndep_superset G (isIndepSet_singleton G x)
  ⟨w, hw, hx (mem_singleton_self x)⟩

/-- **Lecture 22 of [elgamal2010], page 22-7.** A conditional law `p(w | x)` of `W ∈ Γ(G)` with
`X ∈ W`. -/
def IsGraphKernel (G : SimpleGraph α) (q : α → ↥(maxIndepSets G) → ℝ) : Prop :=
  IsChannel q ∧ ∀ x (w : ↥(maxIndepSets G)), x ∉ (w : Finset α) → q x w = 0

/-- There is such a law: a node chooses one of the sets that contain it. -/
lemma exists_isGraphKernel (G : SimpleGraph α) : ∃ q, IsGraphKernel G q := by
  classical
  choose τ hτ hx using exists_mem_maxIndepSets G
  refine ⟨fun x w => if w = ⟨τ x, hτ x⟩ then 1 else 0, fun x => ⟨fun w => ?_, ?_⟩, fun x w hw => ?_⟩
  · beta_reduce
    split_ifs <;> norm_num
  · simp
  · beta_reduce
    rw [ite_eq_right]
    rintro rfl
    exact absurd (hx x) hw

/-- The set of the laws is compact. -/
lemma isCompact_isGraphKernel (G : SimpleGraph α) : IsCompact {q | IsGraphKernel G q} := by
  have hcl : IsClosed {q : α → ↥(maxIndepSets G) → ℝ |
      ∀ x (w : ↥(maxIndepSets G)), x ∉ (w : Finset α) → q x w = 0} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    exact isClosed_eq (by fun_prop) continuous_const
  exact isCompact_setOf_isChannel.inter_right hcl

end Graph

/-! ### Graph entropy -/

section Entropy

variable [Fintype γ] {P : α × γ → ℝ}

/-- **Lecture 22 of [elgamal2010], page 22-8.** The conditional graph entropy
`H_G(X | Y) = min I(X; W | Y)` over `p(w | x)` with `W ∈ Γ(G)` and `X ∈ W`, in nats. -/
def condGraphEntropy (G : SimpleGraph α) (P : α × γ → ℝ) : ℝ :=
  sInf {I | ∃ q, IsGraphKernel G q ∧ sideRate 1 P q = I}

/-- **Lecture 22 of [elgamal2010], page 22-7.** The graph entropy of Körner,
`H_G(X) = min I(X; W)` over `p(w | x)` with `W ∈ Γ(G)` and `X ∈ W`, in nats. It is the conditional
graph entropy with no side information: see `graphEntropy_eq_sInf`. -/
def graphEntropy (G : SimpleGraph α) (p : α → ℝ) : ℝ :=
  condGraphEntropy G fun z : α × Unit => p z.1

/-- The minimum is attained. -/
theorem exists_condGraphEntropy_eq (hP : IsPMF P) (G : SimpleGraph α) :
    ∃ q, IsGraphKernel G q ∧ sideRate 1 P q = condGraphEntropy G P := by
  have hK : IsCompact ((fun q : α → ↥(maxIndepSets G) → ℝ => sideRate 1 P q) ''
      {q | IsGraphKernel G q}) :=
    (isCompact_isGraphKernel G).image_of_continuousOn
      ((continuousOn_sideRate hP 1).mono fun q hq => hq.1)
  obtain ⟨q₀, hq₀⟩ := exists_isGraphKernel G
  have hmem := hK.sInf_mem ⟨_, q₀, hq₀, rfl⟩
  obtain ⟨q, hq, he⟩ := hmem
  refine ⟨q, hq, he.trans ?_⟩
  rw [condGraphEntropy, Set.image]
  rfl

/-- `H_G(X | Y) ≤ I(X; W | Y)` for every such law. -/
lemma condGraphEntropy_le (hP : IsPMF P) {G : SimpleGraph α} {q : α → ↥(maxIndepSets G) → ℝ}
    (hq : IsGraphKernel G q) : condGraphEntropy G P ≤ sideRate 1 P q := by
  have hK : IsCompact ((fun q : α → ↥(maxIndepSets G) → ℝ => sideRate 1 P q) ''
      {q | IsGraphKernel G q}) :=
    (isCompact_isGraphKernel G).image_of_continuousOn
      ((continuousOn_sideRate hP 1).mono fun q hq => hq.1)
  exact csInf_le hK.bddBelow ⟨q, hq, rfl⟩

/-- `H_G(X | Y) ≥ 0`. -/
lemma condGraphEntropy_nonneg (hP : IsPMF P) (G : SimpleGraph α) : 0 ≤ condGraphEntropy G P := by
  obtain ⟨q, hq, he⟩ := exists_condGraphEntropy_eq hP G
  rw [← he]
  exact sideRate_nonneg hP hq.1 le_rfl

/-- `I(X; W | Y) = 0` if `W` is constant. -/
lemma sideRate_one_of_subsingleton [Fintype υ] [Subsingleton υ] (hP : IsPMF P)
    {q : α → υ → ℝ} (hq : IsChannel q) : sideRate 1 P q = 0 := by
  classical
  have hμ := siLaw_isPMF hP hq
  obtain ⟨z⟩ : Nonempty ((α × γ) × υ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)
  have h₁ : H[Prod.snd | fun w : (α × γ) × υ => w.1.2 ; siLaw P q] = 0 :=
    (condEntropy_eq_zero_iff hμ _ _).2 ⟨fun _ => z.2, fun w _ => Subsingleton.elim _ _⟩
  have h₂ : H[Prod.snd | pair (fun w : (α × γ) × υ => w.1.1) (fun w => w.1.2) ; siLaw P q] = 0 :=
    (condEntropy_eq_zero_iff hμ _ _).2 ⟨fun _ => z.2, fun w _ => Subsingleton.elim _ _⟩
  rw [sideRate_one hP hq, condMutualInfo_comm hμ, condMutualInfo, h₁, h₂, sub_zero]

/-- **Lecture 22 of [elgamal2010], page 22-8.** With no edges, `H_G(X | Y) = 0`: then `Γ(G)` has a
single element. -/
theorem condGraphEntropy_bot (hP : IsPMF P) : condGraphEntropy (⊥ : SimpleGraph α) P = 0 := by
  have hsub : Subsingleton ↥(maxIndepSets (⊥ : SimpleGraph α)) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have huniv : ∀ w : ↥(maxIndepSets (⊥ : SimpleGraph α)), (w : Finset α) = univ := fun w => by
      have h := mem_maxIndepSets.1 w.2
      exact (h.2 univ (fun _ _ _ _ _ => by simp) (subset_univ _)).symm
    rw [huniv a, huniv b]
  obtain ⟨q, hq, he⟩ := exists_condGraphEntropy_eq hP (⊥ : SimpleGraph α)
  rw [← he]
  exact sideRate_one_of_subsingleton hP hq.1

/-- **Lecture 22 of [elgamal2010], page 22-8.** For the complete graph, `H_G(X | Y) = H(X | Y)`,
since `W = {X}`. -/
theorem condGraphEntropy_top (hP : IsPMF P) :
    condGraphEntropy (⊤ : SimpleGraph α) P = H[Prod.fst | Prod.snd ; P] := by
  classical
  obtain ⟨q, hq, he⟩ := exists_condGraphEntropy_eq hP (⊤ : SimpleGraph α)
  have hsing : ∀ w : ↥(maxIndepSets (⊤ : SimpleGraph α)), ∀ x x', x ∈ (w : Finset α) →
      x' ∈ (w : Finset α) → x = x' := fun w x x' hx hx' => by
    by_contra hne
    exact (mem_maxIndepSets.1 w.2).1 hx hx' hne (by simpa using hne)
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hf : ∀ u : (α × γ) × ↥(maxIndepSets (⊤ : SimpleGraph α)), siLaw P q u ≠ 0 →
      (fun (w : ↥(maxIndepSets (⊤ : SimpleGraph α))) (_ : γ) =>
        if h : (w : Finset α).Nonempty then h.choose else z.1) u.2 u.1.2 = u.1.1 := fun u hu => by
    have hq0 : q u.1.1 u.2 ≠ 0 := fun h => hu (by simp [siLaw, jointOf, h])
    have hmem : u.1.1 ∈ (u.2 : Finset α) := by
      by_contra hn
      exact hq0 (hq.2 _ _ hn)
    have hne : (u.2 : Finset α).Nonempty := ⟨_, hmem⟩
    simp only [hne, dite_true]
    exact hsing _ _ _ hne.choose_spec hmem
  rw [← he]
  exact sideRate_one_eq_of_support hP hq.1 ((condEntropy_XUY_eq_zero_iff hP hq.1).2
    ⟨fun w _ => if h : (w : Finset α).Nonempty then h.choose else z.1, hf⟩)

end Entropy

/-! ### The characteristic graph and the Orlitsky–Roche theorem -/

section OrlitskyRoche

variable [Fintype γ] {P : α × γ → ℝ}

/-- **Lecture 22 of [elgamal2010], pages 22-8 and 22-9.** The characteristic graph of `(X, Y, g)`:
distinct `x`, `x'` are connected if there is a `y` with `p(x, y), p(x', y) > 0` and
`g(x, y) ≠ g(x', y)`. -/
def charGraph (P : α × γ → ℝ) (g : α × γ → β) : SimpleGraph α where
  Adj x x' := x ≠ x' ∧ ∃ y, P (x, y) ≠ 0 ∧ P (x', y) ≠ 0 ∧ g (x, y) ≠ g (x', y)
  symm := ⟨fun _ _ ⟨hne, y, h₁, h₂, h₃⟩ => ⟨hne.symm, y, h₂, h₁, h₃.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype γ] in
/-- **Lecture 22, page 22-40.** `g(x, y)` is determined by `(w, y)` on the support of a graph
kernel, so `H(Z | W, Y) = 0`. -/
lemma isFunOf_of_isGraphKernel {g : α × γ → β} {q : α → ↥(maxIndepSets (charGraph P g)) → ℝ}
    (hq : IsGraphKernel (charGraph P g) q) (z₀ : β) :
    ∃ f : ↥(maxIndepSets (charGraph P g)) → γ → β, IsFunOf P q g f := by
  classical
  refine ⟨fun w y => if h : ∃ x ∈ (w : Finset α), P (x, y) ≠ 0 then g (h.choose, y) else z₀,
    fun u hu => ?_⟩
  obtain ⟨⟨x, y⟩, w⟩ := u
  have hP0 : P (x, y) ≠ 0 := fun h => hu (by simp [siLaw, jointOf, h])
  have hq0 : q x w ≠ 0 := fun h => hu (by simp [siLaw, jointOf, h])
  have hx : x ∈ (w : Finset α) := by
    by_contra hn
    exact hq0 (hq.2 _ _ hn)
  have hex : ∃ x ∈ (w : Finset α), P (x, y) ≠ 0 := ⟨x, hx, hP0⟩
  simp only [hex, dite_true]
  obtain ⟨hx₀, hP₀⟩ := hex.choose_spec
  by_contra hne
  have hxne : hex.choose ≠ x := fun h => hne (by rw [h])
  exact (mem_maxIndepSets.1 w.2).1 hx₀ hx hxne ⟨hxne, y, hP₀, hP0, hne⟩

/-- **Lecture 22, page 22-41.** The support `{x : p(u, x) > 0}` of `U = u` is independent if
`H(Z | U, Y) = 0`. The notes say that it is maximally independent, which it need not be. -/
lemma isIndepSet_support [Finite υ] {g : α × γ → β} {q : α → υ → ℝ} {f : υ → γ → β}
    (hf : IsFunOf P q g f) (u : υ) :
    (charGraph P g).IsIndepSet
      (((univ.filter fun x => (∃ y, P (x, y) ≠ 0) ∧ q x u ≠ 0 : Finset α)) : Set α) := by
  have := Fintype.ofFinite υ
  classical
  intro x hx x' hx' _ hadj
  obtain ⟨-, y, h₁, h₂, h₃⟩ := hadj
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
  have e₁ := hf ((x, y), u) (by simp [siLaw, jointOf, h₁, hx.2])
  have e₂ := hf ((x', y), u) (by simp [siLaw, jointOf, h₂, hx'.2])
  exact h₃ (e₁.symm.trans e₂)

/-- **Lecture 22, page 22-40.** `R*_g ≤ H_G(X | Y)`. -/
lemma funLosslessRate_le_condGraphEntropy [Finite β] (hP : IsPMF P) (g : α × γ → β) :
    funLosslessRate P g ≤ condGraphEntropy (charGraph P g) P := by
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  obtain ⟨q, hq, he⟩ := exists_condGraphEntropy_eq hP (charGraph P g)
  obtain ⟨f, hf⟩ := isFunOf_of_isGraphKernel hq (g z)
  rw [← he]
  exact funLosslessRate_le hP hq.1 hf

/-- **Lecture 22, pages 22-40 and 22-41.** `H_G(X | Y) ≤ I(X; U | Y)` for every `p(u | x)` with
`H(Z | U, Y) = 0`: the set `W` of the letters that are possible given `U` can be extended to a
maximally independent set, and it is a function of `U`. -/
lemma condGraphEntropy_le_sideRate [Fintype υ] (hP : IsPMF P) {g : α × γ → β} {q : α → υ → ℝ}
    (hq : IsChannel q) {f : υ → γ → β} (hf : IsFunOf P q g f) :
    condGraphEntropy (charGraph P g) P ≤ sideRate 1 P q := by
  classical
  set G := charGraph P g with hG
  choose τ₀ hτ₀ hsub using fun u => exists_maxIndep_superset G (isIndepSet_support hf u)
  set τ : υ → ↥(maxIndepSets G) := fun u => ⟨τ₀ u, hτ₀ u⟩ with hτ
  obtain ⟨q₀, hq₀⟩ := exists_isGraphKernel G
  set q' : α → ↥(maxIndepSets G) → ℝ := fun x w =>
    if ∃ y, P (x, y) ≠ 0 then ∑ u with τ u = w, q x u else q₀ x w with hq'
  have hk : IsGraphKernel G q' := by
    refine ⟨fun x => ?_, fun x w hx => ?_⟩
    · by_cases hs : ∃ y, P (x, y) ≠ 0
      · simp only [hq', hs, ite_true]
        refine ⟨fun w => sum_nonneg fun u _ => (hq x).nonneg u, ?_⟩
        rw [← (hq x).sum_eq_one]
        exact sum_fiberwise _ _ _
      · simp only [hq', hs, ite_false]
        exact hq₀.1 x
    · by_cases hs : ∃ y, P (x, y) ≠ 0
      · simp only [hq', hs, ite_true]
        refine sum_eq_zero fun u hu => ?_
        by_contra hne
        apply hx
        have hu' : τ u = w := (mem_filter.1 hu).2
        rw [← hu']
        exact hsub u (by simpa using ⟨hs, hne⟩)
      · simp only [hq', hs, ite_false]
        exact hq₀.2 x w hx
  have hμ := siLaw_isPMF hP hq
  have hμ' := siLaw_isPMF hP hk.1
  have hlaw : siLaw P q' = dist (siLaw P q) fun z => (z.1, τ z.2) := by
    funext ⟨⟨x, y⟩, w⟩
    rw [dist, Fintype.sum_prod_type]
    rw [sum_eq_single (x, y)]
    · by_cases h0 : P (x, y) = 0
      · simp [siLaw, jointOf, h0]
      · have hs : ∃ y, P (x, y) ≠ 0 := ⟨y, h0⟩
        simp only [siLaw, jointOf, hq', hs, ite_true, Prod.mk.injEq, true_and]
        rw [mul_sum, sum_filter]
    · intro z _ hz
      refine sum_eq_zero fun u _ => ?_
      rw [ite_eq_right]
      intro h
      exact absurd (Prod.mk.inj h).1 hz
    · simp
  have hr : sideRate 1 P q' =
      I[fun z : (α × γ) × υ => z.1.1 : τ ∘ Prod.snd | fun z => z.1.2 ; siLaw P q] := by
    rw [sideRate_one hP hk.1, condMutualInfo, condMutualInfo]
    congr 1
    · refine condEntropy_eq_of_dist_pair_eq hμ' hμ ?_
      rw [show pair (fun z : (α × γ) × ↥(maxIndepSets G) => z.1.2) (fun z => z.1.1) =
        (pair Prod.snd Prod.fst) ∘ Prod.fst from rfl, dist_comp_eq, dist_siLaw_fst hk.1,
        show pair (fun z : (α × γ) × υ => z.1.2) (fun z => z.1.1) =
        (pair Prod.snd Prod.fst) ∘ Prod.fst from rfl, dist_comp_eq, dist_siLaw_fst hq]
    · refine condEntropy_eq_of_dist_pair_eq hμ' hμ ?_
      rw [hlaw, ← dist_comp_eq]
      rfl
  calc _ ≤ sideRate 1 P q' := condGraphEntropy_le hP hk
    _ = _ := hr
    _ ≤ I[fun z : (α × γ) × υ => z.1.1 : Prod.snd | fun z => z.1.2 ; siLaw P q] :=
        condMutualInfo_comp_le hμ _ Prod.snd _ τ
    _ = sideRate 1 P q := (sideRate_one hP hq).symm

/-- **The single-letter form of the Orlitsky–Roche theorem (Lecture 22, page 22-40).**
`min I(X; U | Y)` over `p(u | x)` with `H(Z | U, Y) = 0` is `H_G(X | Y)`, for the characteristic
graph `G` of `(X, Y, g)`. -/
theorem funLosslessRate_eq_condGraphEntropy [Finite β] (hP : IsPMF P) (g : α × γ → β) :
    funLosslessRate P g = condGraphEntropy (charGraph P g) P := by
  refine le_antisymm (funLosslessRate_le_condGraphEntropy hP g) ?_
  obtain ⟨q, f, hq, hf, hr⟩ := exists_funLosslessRate_eq hP g
  rw [← hr]
  exact condGraphEntropy_le_sideRate hP hq hf

/-- **The Orlitsky–Roche theorem (Lecture 22 of [elgamal2010], page 22-9).** The optimal rate for
computing `Z = g(X, Y)` losslessly at a decoder with side information `Y` is
`R*_g = H_G(X | Y)`, in bits, for the characteristic graph `G` of `(X, Y, g)`. -/
theorem losslessFunBits_eq_condGraphEntropy [Finite β] (hP : IsPMF P) (g : α × γ → β) :
    sInf {R | IsLosslessFunBits P g R} = condGraphEntropy (charGraph P g) P / log 2 := by
  rw [losslessFunBits_eq hP, funLosslessRate_eq_condGraphEntropy hP]

end OrlitskyRoche

end InfoTheory
