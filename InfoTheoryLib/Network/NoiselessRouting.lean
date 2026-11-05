/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NoiselessCode

/-!
# Noiseless networks: routing and the max-flow min-cut theorem

A routing scheme sends the bits of the messages along the edges, possibly in several copies, and
performs no other operation. It gives a code without error. By the max-flow min-cut theorem routing
achieves the capacity of a noiseless relay network, and of a multicast network in which every node
wishes to receive the message.

## Main definitions

* `RoutingScheme cap b D`: a routing scheme for edges of `cap` bits and messages of `b` bits.
* `IsRoutingAchievable`: rates achieved by routing for all large `n`.

## Main statements

* `RoutingScheme.code`, `RoutingScheme.code_correct`: a routing scheme gives a code that is always
  correct.
* `exists_routes`: when the integer cut conditions hold, all bits can be routed to one node.
* `cutCap_floor_ge`: the capacity of a cut after rounding the capacities down.
* `isRoutingAchievable_of_lt_minCut`: routing achieves every rate below the minimum cut.
* `relay_capacity`: the **max-flow min-cut theorem** of Lecture 16 of El Gamal and Kim.
* `isRoutingAchievable_all_nodes`, `all_nodes_capacity`: the case `D = [2 : N]`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {V : Type*} [LinearOrder V] [Fintype V]

/-! ### Routing schemes -/

/-- **Lecture 16 of [elgamal2010], pages 16-7 and 16-13.** A routing scheme. Node `j` has a message
of `b j` bits, and the edge `(k, l)` carries a set of at most `cap k l` bits. A bit on an edge out
of `k` either belongs to the message of `k` or came in on an edge into `k`, so nodes may forward
copies of a bit but do no other operation. Every destination receives all the bits it wants. -/
structure RoutingScheme (cap : V → V → ℕ) (b : V → ℕ) (D : V → Finset V) where
  /-- The bits carried by an edge. -/
  carry : V → V → Finset (Σ j, Fin (b j))
  /-- An edge carries at most its capacity. -/
  card_le : ∀ k l, #(carry k l) ≤ cap k l
  /-- A bit is sent by its source, or was received. -/
  forward : ∀ k l, ∀ r ∈ carry k l, r.1 = k ∨ ∃ j, j < k ∧ r ∈ carry j k
  /-- Destinations receive the bits they want. -/
  deliver : ∀ r : Σ j, Fin (b j), ∀ l ∈ D r.1, ∃ i, i < l ∧ r ∈ carry i l

section Code

variable {cap : V → V → ℕ} {b : V → ℕ} {D : V → Finset V}

open Classical in
/-- The code of a routing scheme. An index is the tuple of the bits carried by the edge. -/
def RoutingScheme.code (S : RoutingScheme cap b D) :
    NetCode V (fun k l => ↥(S.carry k l) → Bool) (fun j => Fin (b j) → Bool) where
  enc k l u mk := fun r =>
    if h : r.1.1 = k then mk (h ▸ r.1.2)
    else
      have hex := (S.forward k l r.1 r.2).resolve_left h
      u (Classical.choose hex) (Classical.choose_spec hex).1 ⟨r.1, (Classical.choose_spec hex).2⟩
  dec l j u := fun i =>
    if h : l ∈ D j then
      have hex := S.deliver ⟨j, i⟩ l h
      u (Classical.choose hex) (Classical.choose_spec hex).1 ⟨⟨j, i⟩, (Classical.choose_spec hex).2⟩
    else false

omit [Fintype V] in
/-- Every index of the code of a routing scheme is the tuple of the right bits. -/
lemma RoutingScheme.code_edge [Finite V] (S : RoutingScheme cap b D) (m : ∀ j, Fin (b j) → Bool)
    (k : V) : ∀ (l : V) (r : ↥(S.carry k l)), S.code.edge m k l r = m r.1.1 r.1.2 := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    intro l r
    rw [NetCode.edge_eq]
    simp only [RoutingScheme.code]
    split_ifs with h
    · obtain ⟨⟨j, i⟩, hr⟩ := r
      simp only at h
      subst h
      rfl
    · have hex := (S.forward k l r.1 r.2).resolve_left h
      exact ih _ (Classical.choose_spec hex).1 _ _

omit [Fintype V] in
/-- **Page 16-9 of [elgamal2010].** The code of a routing scheme has no errors. -/
theorem RoutingScheme.code_correct [Finite V] (S : RoutingScheme cap b D)
    (m : ∀ j, Fin (b j) → Bool) : S.code.Correct D m := by
  intro j l hl
  funext i
  simp only [NetCode.out, RoutingScheme.code, hl, dite_true]
  exact S.code_edge m _ _ _

end Code

section Bits

variable {N : NoiselessNetwork V} {D : V → Finset V} {R : V → ℝ} {n : ℕ}

omit [Fintype V] in
/-- A routing scheme with the right numbers of bits gives a `(2^{nR}, n)` code without error. -/
theorem RoutingScheme.exists_rateCode [Finite V]
    (S : RoutingScheme (fun k l => ⌊(n : ℝ) * N.C k l⌋₊) (fun j => ⌈(n : ℝ) * R j⌉₊) D) :
    ∃ c : RateCode N R n, ∀ m, c.Correct D m := by
  have hM : ∀ j, Nonempty (Fin (2 ^ ⌈(n : ℝ) * R j⌉₊) ↪ (Fin ⌈(n : ℝ) * R j⌉₊ → Bool)) := fun j =>
    Function.Embedding.nonempty_of_card_le (by simp)
  have hA : ∀ k l, Nonempty ((↥(S.carry k l) → Bool) ↪ Fin (2 ^ ⌊(n : ℝ) * N.C k l⌋₊)) := by
    intro k l
    refine Function.Embedding.nonempty_of_card_le ?_
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by norm_num) (S.card_le k l)
  exact S.code.exists_relabel S.code_correct (fun j => (hM j).some) (fun j => (hM j).some.injective)
    (fun k l => (hA k l).some) (fun k l => (hA k l).some.injective.injOn)

/-- **Page 16-9 of [elgamal2010].** A rate tuple is achieved by routing if routing schemes exist for
all large `n`. -/
def IsRoutingAchievable (N : NoiselessNetwork V) (D : V → Finset V) (R : V → ℝ) : Prop :=
  (∀ j, 0 ≤ R j) ∧ ∀ᶠ n : ℕ in atTop,
    Nonempty (RoutingScheme (fun k l => ⌊(n : ℝ) * N.C k l⌋₊) (fun j => ⌈(n : ℝ) * R j⌉₊) D)

/-- Rates achieved by routing are achieved with zero error. -/
theorem IsRoutingAchievable.isAchievableZE (h : IsRoutingAchievable N D R) :
    IsAchievableZE N D R :=
  ⟨h.1, h.2.mono fun _ ⟨S⟩ => S.exists_rateCode⟩

end Bits

/-! ### Routing to one node -/

/-- The bits of the message of node `k`. -/
def ownBits (b : V → ℕ) (k : V) : Finset (Σ j, Fin (b j)) :=
  Finset.univ.map ⟨Sigma.mk k, sigma_mk_injective⟩

omit [LinearOrder V] [Fintype V] in
lemma mem_ownBits {b : V → ℕ} {k : V} {r : Σ j, Fin (b j)} :
    r ∈ ownBits b k ↔ r.1 = k := by
  obtain ⟨j, i⟩ := r
  simp only [ownBits, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx⟩
    exact (congrArg Sigma.fst hx).symm
  · rintro rfl
    exact ⟨i, rfl⟩

omit [LinearOrder V] [Fintype V] in
lemma card_ownBits {b : V → ℕ} (k : V) : #(ownBits b k) = b k := by
  simp [ownBits]

/-- **Integer max-flow min-cut, with bits.** If the bits of the nodes inside any set not containing
`t` fit through its cut, all bits can be routed to `t`, each edge carrying at most its capacity. -/
theorem exists_routes {cap : V → V → ℕ} (hord : ∀ j k, 0 < cap j k → j < k) (b : V → ℕ) (t : V)
    (h : ∀ S : Finset V, t ∉ S →
      ∑ j ∈ S, (b j : ℤ) ≤ cutCap (fun j k => (cap j k : ℤ)) S) :
    ∃ B : V → V → Finset (Σ j, Fin (b j)), (∀ k l, #(B k l) ≤ cap k l) ∧
      (∀ k l, ∀ r ∈ B k l, r.1 = k ∨ ∃ j, j < k ∧ r ∈ B j k) ∧
      ∀ r : Σ j, Fin (b j), r.1 ≠ t → ∃ i, i < t ∧ r ∈ B i t := by
  obtain ⟨f, hf0, hfc, hfn⟩ := exists_supplyFlow (c := fun j k => (cap j k : ℤ))
    (fun _ _ => Int.natCast_nonneg _) t h
  have hford : ∀ j k, 0 < f j k → j < k := fun j k hjk =>
    hord j k (by have := hfc j k; omega)
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := exists_units hf0 hford t (ownBits b)
    (fun k hk => by rw [hfn k hk, card_ownBits])
  refine ⟨B, fun k l => ?_, fun k l r hr => ?_, fun r hr => hB₃ r.1 hr r (mem_ownBits.mpr rfl)⟩
  · have := (hB₁ k l).trans (hfc k l)
    exact_mod_cast this
  · exact (hB₂ k l r hr).imp mem_ownBits.mp id

/-- Rounding the capacities down loses at most `|V|²` on a cut. -/
lemma cutCap_floor_ge (C : V → V → ℝ) (x : ℝ) (S : Finset V) :
    x * cutCap C S - (Fintype.card V : ℝ) ^ 2 ≤
      ((cutCap (fun j k => ((⌊x * C j k⌋₊ : ℕ) : ℤ)) S : ℤ) : ℝ) := by
  have hcast : ((cutCap (fun j k => ((⌊x * C j k⌋₊ : ℕ) : ℤ)) S : ℤ) : ℝ) =
      ∑ j ∈ S, ∑ k ∈ Sᶜ, (⌊x * C j k⌋₊ : ℝ) := by
    simp [cutCap]
  have hle : ∀ j ∈ S, ∀ k ∈ Sᶜ, x * C j k - 1 ≤ (⌊x * C j k⌋₊ : ℝ) := fun j _ k _ =>
    (sub_le_iff_le_add.mpr (Nat.lt_floor_add_one _).le)
  have hsum : ∑ j ∈ S, ∑ k ∈ Sᶜ, (x * C j k - 1) ≤ ∑ j ∈ S, ∑ k ∈ Sᶜ, (⌊x * C j k⌋₊ : ℝ) :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hle j hj k hk
  have hval : ∑ j ∈ S, ∑ k ∈ Sᶜ, (x * C j k - 1) = x * cutCap C S - (#S * #Sᶜ : ℝ) := by
    simp only [cutCap, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      mul_one]
  have hS : (#S : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ S
  have hSc : (#Sᶜ : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ Sᶜ
  have hprod : (#S * #Sᶜ : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    rw [sq]
    exact mul_le_mul hS hSc (by positivity) (by positivity)
  rw [hcast]
  linarith

omit [LinearOrder V] [Fintype V] in
/-- The rounded capacities of a network go up. -/
lemma floor_acyclic [LinearOrder V] {C : V → V → ℝ} (hC : ∀ j k, 0 < C j k → j < k) {x : ℝ}
    (hx : 0 ≤ x) (j k : V) (h : 0 < ⌊x * C j k⌋₊) : j < k := by
  refine hC j k ?_
  by_contra hjk
  have hle : x * C j k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (not_lt.mp hjk)
  have : ⌊x * C j k⌋₊ = 0 := Nat.floor_of_nonpos hle
  omega

/-! ### The max-flow min-cut theorem -/

section MaxFlow

variable (N : NoiselessNetwork V)

omit [Fintype V] in
lemma ceil_singleRate_of_ne (s : V) (R : ℝ) (n : ℕ) {j : V} (hj : j ≠ s) :
    ⌈(n : ℝ) * singleRate s R j⌉₊ = 0 := by
  simp [singleRate, hj]

/-- **Achievability in the max-flow min-cut theorem, page 16-7 of [elgamal2010].** Routing achieves
every rate below the capacity of a minimum cut. -/
theorem isRoutingAchievable_of_lt_minCut {s t : V} (hst : s ≠ t) {R : ℝ} (hR : 0 ≤ R)
    (hlt : R < minCut N.C s t) :
    IsRoutingAchievable N (multicastD s {t}) (singleRate s R) := by
  refine ⟨fun j => ?_, ?_⟩
  · simp only [singleRate]
    split_ifs <;> simp [hR]
  have hgap : 0 < minCut N.C s t - R := sub_pos.mpr hlt
  have hev : ∀ᶠ n : ℕ in atTop, (Fintype.card V : ℝ) ^ 2 + 1 ≤ (n : ℝ) * (minCut N.C s t - R) :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hgap |>.eventually_ge_atTop _
  filter_upwards [hev] with n hn
  have hcut : ∀ S : Finset V, t ∉ S → ∑ j ∈ S, ((⌈(n : ℝ) * singleRate s R j⌉₊ : ℕ) : ℤ) ≤
      cutCap (fun j k => ((⌊(n : ℝ) * N.C j k⌋₊ : ℕ) : ℤ)) S := by
    intro S htS
    have hnonneg : 0 ≤ cutCap (fun j k => ((⌊(n : ℝ) * N.C j k⌋₊ : ℕ) : ℤ)) S :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
    by_cases hs : s ∈ S
    · rw [Finset.sum_eq_single_of_mem s hs fun j _ hj => by
        rw [ceil_singleRate_of_ne s R n hj]; rfl]
      have h₁ := cutCap_floor_ge N.C n S
      have h₂ : minCut N.C s t ≤ cutCap N.C S := minCut_le N.C hs htS
      have h₃ : (n : ℝ) * minCut N.C s t ≤ (n : ℝ) * cutCap N.C S :=
        mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg n)
      have h₄ : ((⌈(n : ℝ) * singleRate s R s⌉₊ : ℕ) : ℝ) < (n : ℝ) * R + 1 := by
        have := Nat.ceil_lt_add_one (a := (n : ℝ) * R) (by positivity)
        simpa [singleRate] using this
      have h₅ : (((⌈(n : ℝ) * singleRate s R s⌉₊ : ℕ) : ℤ) : ℝ) ≤
          ((cutCap (fun j k => ((⌊(n : ℝ) * N.C j k⌋₊ : ℕ) : ℤ)) S : ℤ) : ℝ) := by
        push_cast at h₄ h₁ ⊢
        nlinarith
      exact_mod_cast h₅
    · rwa [Finset.sum_eq_zero fun j hj => by
        rw [ceil_singleRate_of_ne s R n fun h => hs (h ▸ hj)]; rfl]
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := exists_routes
    (floor_acyclic N.acyclic (Nat.cast_nonneg n)) _ t hcut
  refine ⟨⟨B, hB₁, hB₂, fun r l hl => ?_⟩⟩
  by_cases hrs : r.1 = s
  · have hlt' : l = t := by simpa [multicastD, hrs] using hl
    subst hlt'
    exact hB₃ r fun h => hst (hrs.symm.trans h)
  · simp [multicastD, hrs] at hl

/-- **Max-flow min-cut theorem, page 16-5 of [elgamal2010].** The capacity of a noiseless relay
network is the capacity of a minimum cut. -/
theorem relay_capacity {s t : V} (hst : s ≠ t) :
    multicastCapacity N s {t} = minCut N.C s t :=
  multicastCapacity_eq
    (fun _ hR hlt => (isRoutingAchievable_of_lt_minCut N hst hR hlt).isAchievableZE.isAchievable)
    (fun _ h => h.le_minCut (Finset.mem_singleton_self t) hst)

end MaxFlow

/-! ### Every node wants the message -/

section AllNodes

variable (N : NoiselessNetwork V)

/-- A set of `v` bits fits on edges of capacities `c j` with `v ≤ ∑ c j`. -/
private lemma exists_cover {ι β : Type*} [Fintype ι] [Fintype β]
    (c : ι → ℕ) (h : Fintype.card β ≤ ∑ j, c j) :
    ∃ B : ι → Finset β, (∀ j, #(B j) ≤ c j) ∧ ∀ r, ∃ j, r ∈ B j := by
  have hcard : Fintype.card β ≤ Fintype.card (Σ j, Fin (c j)) := by
    simpa using h
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun j => Finset.univ.filter fun r => (e r).1 = j, fun j => ?_,
    fun r => ⟨(e r).1, by simp⟩⟩
  have hle := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun r => (e r).1 = j)
    (t := (Finset.univ.map ⟨Sigma.mk j, sigma_mk_injective⟩ : Finset (Σ j, Fin (c j)))) e
    (fun r hr => by
      have hr' : (e r).1 = j := by simpa using hr
      have : e r = ⟨j, hr' ▸ (e r).2⟩ := by
        rw [Sigma.ext_iff]
        exact ⟨hr', by simp⟩
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      exact ⟨_, this.symm⟩)
    e.injective.injOn
  simpa using hle

/-- **Page 16-12 of [elgamal2010].** If every node wishes to receive the message then routing, with
copies at the relays, achieves every rate below the cutset bound. Each node receives all the bits
over its incoming edges, from lower nodes, which know them all. Only the cuts `S = {k}ᶜ` are
used. -/
theorem isRoutingAchievable_all_nodes {s : V} {R : ℝ} (hR : 0 ≤ R)
    (hlt : ∀ k, k ≠ s → R < minCut N.C s k) :
    IsRoutingAchievable N (multicastD s (Finset.univ.erase s)) (singleRate s R) := by
  classical
  refine ⟨fun j => ?_, ?_⟩
  · simp only [singleRate]
    split_ifs <;> simp [hR]
  -- for large `n`, the bits fit into the incoming edges of each node
  have hev : ∀ k, ∀ᶠ n : ℕ in atTop, k ≠ s →
      (Fintype.card V : ℝ) ^ 2 + 1 ≤ (n : ℝ) * (cutCap N.C {k}ᶜ - R) := by
    intro k
    by_cases hk : k = s
    · exact Eventually.of_forall fun _ h => absurd hk h
    · have hgap : 0 < cutCap N.C {k}ᶜ - R := sub_pos.mpr ((hlt k hk).trans_le
        (minCut_le _ (by simpa using Ne.symm hk) (by simp)))
      exact (tendsto_natCast_atTop_atTop.atTop_mul_const hgap |>.eventually_ge_atTop _).mono
        fun _ h _ => h
  filter_upwards [Filter.eventually_all.mpr hev] with n hn
  -- all the bits, and the bits of the nodes other than `s` do not exist
  have hempty : ∀ r : Σ j, Fin (⌈(n : ℝ) * singleRate s R j⌉₊), r.1 = s := by
    rintro ⟨j, i⟩
    by_contra hj
    have h0 := ceil_singleRate_of_ne s R n (j := j) hj
    have hi := i.2
    omega
  have hcover : ∀ k, k ≠ s → Fintype.card (Σ j, Fin (⌈(n : ℝ) * singleRate s R j⌉₊)) ≤
      ∑ j, ⌊(n : ℝ) * N.C j k⌋₊ := by
    intro k hk
    have hcards : Fintype.card (Σ j, Fin (⌈(n : ℝ) * singleRate s R j⌉₊)) =
        ⌈(n : ℝ) * singleRate s R s⌉₊ := by
      rw [Fintype.card_sigma, Finset.sum_eq_single s]
      · simp
      · intro j _ hj
        simp [ceil_singleRate_of_ne s R n hj]
      · simp
    rw [hcards]
    have h₁ := cutCap_floor_ge N.C n {k}ᶜ
    have h₄ : ((⌈(n : ℝ) * singleRate s R s⌉₊ : ℕ) : ℝ) < (n : ℝ) * R + 1 := by
      have := Nat.ceil_lt_add_one (a := (n : ℝ) * R) (by positivity)
      simpa [singleRate] using this
    have hval : ((cutCap (fun j l => ((⌊(n : ℝ) * N.C j l⌋₊ : ℕ) : ℤ)) {k}ᶜ : ℤ) : ℝ) ≤
        ∑ j, (⌊(n : ℝ) * N.C j k⌋₊ : ℝ) := by
      simp only [cutCap, compl_compl, Finset.sum_singleton]
      push_cast
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => Nat.cast_nonneg _
    have hfin : ((⌈(n : ℝ) * singleRate s R s⌉₊ : ℕ) : ℝ) ≤ ∑ j, (⌊(n : ℝ) * N.C j k⌋₊ : ℝ) := by
      have := hn k hk
      nlinarith
    exact_mod_cast hfin
  choose! B hB₁ hB₂ using fun k (hk : k ≠ s) => exists_cover (β := Σ j, Fin (⌈(n : ℝ) *
    singleRate s R j⌉₊)) (fun j => ⌊(n : ℝ) * N.C j k⌋₊) (hcover k hk)
  -- the edges into `s` carry nothing
  have hlt' : ∀ j k r, k ≠ s → r ∈ B k j → j < k := by
    intro j k r hk hr
    have hpos : 0 < #(B k j) := Finset.card_pos.mpr ⟨r, hr⟩
    exact floor_acyclic N.acyclic (Nat.cast_nonneg n) j k (hpos.trans_le (hB₁ k hk j))
  refine ⟨⟨fun j k => if k = s then ∅ else B k j, fun k l => ?_, fun k l r hr => ?_,
    fun r l hl => ?_⟩⟩
  · by_cases hl : l = s
    · simp [hl]
    · simpa [hl] using hB₁ l hl k
  · by_cases hks : k = s
    · exact Or.inl ((hempty r).trans hks.symm)
    · obtain ⟨j, hj⟩ := hB₂ k hks r
      exact Or.inr ⟨j, hlt' j k r hks hj, by simpa [hks] using hj⟩
  · have hls : l ≠ s := by
      have : l ∈ Finset.univ.erase s := by simpa [multicastD, hempty r] using hl
      exact Finset.ne_of_mem_erase this
    obtain ⟨j, hj⟩ := hB₂ l hls r
    exact ⟨j, hlt' j l r hls hj, by simpa [hls] using hj⟩

/-- **Page 16-12 of [elgamal2010].** If every node wishes to receive the message then the capacity
is the cutset bound, and routing achieves it. -/
theorem all_nodes_capacity {s : V} (hne : (Finset.univ.erase s).Nonempty) :
    multicastCapacity N s (Finset.univ.erase s) =
      (Finset.univ.erase s).inf' hne (minCut N.C s) := by
  refine multicastCapacity_eq (fun R hR hlt => ?_) (fun R h => ?_)
  · refine (isRoutingAchievable_all_nodes N hR fun k hk => ?_).isAchievableZE.isAchievable
    exact (Finset.lt_inf'_iff _).mp hlt k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  · refine (Finset.le_inf'_iff _ _).mpr fun k hk => ?_
    exact h.le_minCut hk (Finset.ne_of_mem_erase hk).symm

end AllNodes

end InfoTheory
