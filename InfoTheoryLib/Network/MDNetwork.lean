/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MDOuter
public import InfoTheoryLib.Network.SlepianWolfMany

/-!
# Multiple description networks: codes and the cutset bound

Section 1 of Lecture 21 of El Gamal and Kim. A source node observes `Xⁿ`, the indices travel over a
noiseless directed acyclic graph and each other node reconstructs `Xⁿ` with its own distortion
measure.

## Main definitions

* `MDNetCode s M n α β`: a code, with source node `s` and `M j k` indices on the edge `(j, k)`.
* `MDNetCode.edge`, `MDNetCode.out`: the index on an edge and the reconstruction at a node.
* `IsAchievableMDN`, `mdnRegion`: the achievable rates and the rate–distortion region.
* `mdnCut S`: the edges across the cut `S`.
* `mdnCutset`: the cutset outer bound holds.

## Main statements

* `MDNetCode.out_congr`: a node outside the cut decodes from the indices across the cut.
* `MDNetCode.mdnCutset_of_code`: the cutset bound for one code.
* `mdnRegion_subset_mdnCutset`: **the cutset outer bound of page 21-5**.
* `mdnCutset_tree`: the converse of Theorem 1, for a tree.
* `MDNetCode.ofParts`: a code from a description of the contents of each edge.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {N : ℕ} {α : Type*} {β : Fin N → Type*}

/-- **Lecture 21 of [elgamal2010], page 21-4.** A code for a multiple description network. The nodes
are numbered so that edges go up; a pair that is not an edge has one index. A node sends a function
of the indices it has received, and only the source node `s` may also use the source sequence. -/
structure MDNetCode (s : Fin N) (M : Fin N → Fin N → ℕ) (n : ℕ) (α : Type*) (β : Fin N → Type*)
  where
  /-- The encoder of the edge `(k, l)`. -/
  enc : ∀ k l, (∀ j, j < k → Fin (M j k)) → (Fin n → α) → Fin (M k l)
  /-- Only the source node uses the source sequence. -/
  relay : ∀ k l h x x', k ≠ s → enc k l h x = enc k l h x'
  /-- The decoder at the node `l`. -/
  dec : ∀ l, (∀ k, k < l → Fin (M k l)) → Fin n → β l

namespace MDNetCode

variable {s : Fin N} {M : Fin N → Fin N → ℕ} {n : ℕ}

/-- The index on the edge `(k, l)`. -/
def edge (c : MDNetCode s M n α β) (x : Fin n → α) (k l : Fin N) : Fin (M k l) :=
  c.enc k l (fun j _ => c.edge x j k) x
termination_by k
decreasing_by assumption

lemma edge_eq (c : MDNetCode s M n α β) (x : Fin n → α) (k l : Fin N) :
    c.edge x k l = c.enc k l (fun j _ => c.edge x j k) x := by
  rw [edge]

/-- The reconstruction at the node `l`. -/
def out (c : MDNetCode s M n α β) (x : Fin n → α) (l : Fin N) : Fin n → β l :=
  c.dec l fun k _ => c.edge x k l

/-- If two source sequences give the same indices across the cut `S`, which contains the source
node, then all the indices out of the nodes outside `S` agree. -/
lemma edge_congr (c : MDNetCode s M n α β) {x x' : Fin n → α} {S : Finset (Fin N)} (hs : s ∈ S)
    (he : ∀ j ∈ S, ∀ k, k ∉ S → c.edge x j k = c.edge x' j k) :
    ∀ j, j ∉ S → ∀ k, c.edge x j k = c.edge x' j k := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    intro hj k
    rw [c.edge_eq x, c.edge_eq x', c.relay j k _ x x' fun h => hj (h ▸ hs)]
    congr 1
    funext i hi
    by_cases hiS : i ∈ S
    · exact he i hiS j hj
    · exact ih i hi hiS j

/-- **A node outside the cut decodes from the indices across the cut.** -/
lemma out_congr (c : MDNetCode s M n α β) {x x' : Fin n → α} {S : Finset (Fin N)} (hs : s ∈ S)
    (he : ∀ j ∈ S, ∀ k, k ∉ S → c.edge x j k = c.edge x' j k) {l : Fin N} (hl : l ∉ S) :
    c.out x l = c.out x' l := by
  simp only [out]
  congr 1
  funext k _
  by_cases hk : k ∈ S
  · exact he k hk l hl
  · exact c.edge_congr hs he k hk l

/-- The expected distortion at the node `l`. -/
def distortion [Fintype α] (c : MDNetCode s M n α β) (P : α → ℝ) (d : ∀ l, α → β l → ℝ)
    (l : Fin N) : ℝ :=
  ∑ x, iidPMF P n x * seqDistortion (d l) x (c.out x l)

end MDNetCode

variable [Fintype α] [∀ l, Fintype (β l)]

/-- **Lecture 21 of [elgamal2010], page 21-4.** A rate tuple, in bits, on the edges `E`, is
achievable at the distortions `D` if for every `ε` and all large `n` there is a code with
distortions at most `D l + ε`. The rates of the pairs that are not edges are `0`. -/
def IsAchievableMDN (P : α → ℝ) (d : ∀ l, α → β l → ℝ) (s : Fin N) (E : Finset (Fin N × Fin N))
    (R : Fin N → Fin N → ℝ) (D : Fin N → ℝ) : Prop :=
  (∀ j k, 0 ≤ R j k) ∧ (∀ j k, (j, k) ∉ E → R j k = 0) ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    ∃ c : MDNetCode s (fun j k => 2 ^ ⌊n * R j k⌋₊) n α β, ∀ l, l ≠ s → c.distortion P d l ≤ D l + ε

/-- **Lecture 21 of [elgamal2010], page 21-4.** The rate–distortion region. -/
def mdnRegion (P : α → ℝ) (d : ∀ l, α → β l → ℝ) (s : Fin N) (E : Finset (Fin N × Fin N))
    (D : Fin N → ℝ) : Set (Fin N → Fin N → ℝ) :=
  closure {R | IsAchievableMDN P d s E R D}

/-- The edges from the cut `S` to its complement. -/
def mdnCut (S : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  univ.filter fun e => e.1 ∈ S ∧ e.2 ∉ S

/-- **Page 21-5 of [elgamal2010].** The cutset outer bound: for some `p(x̂ | x)` with the prescribed
distortions, `∑_{j ∈ S, k ∉ S} R_{jk} ≥ I(X; X̂(Sᶜ))` for all the cuts `S` with the source node. -/
def mdnCutset (P : α → ℝ) (d : ∀ l, α → β l → ℝ) (s : Fin N) (R : Fin N → Fin N → ℝ)
    (D : Fin N → ℝ) : Prop :=
  ∃ κ : α → (∀ l, β l) → ℝ, IsChannel κ ∧
    (∀ l, l ≠ s → ∑ z, jointOf P κ z * d l z.1 (z.2 l) ≤ D l) ∧
    ∀ S : Finset (Fin N), s ∈ S →
      I[Prod.fst : fun z : α × ∀ l, β l => swRest S z.2 ; jointOf P κ] ≤
        (∑ e ∈ mdnCut S, R e.1 e.2) * log 2

/-! ### The bound for one code -/

section Code

variable {P : α → ℝ} {d : ∀ l, α → β l → ℝ} {s : Fin N} {M : Fin N → Fin N → ℕ} {n : ℕ}

/-- **Page 21-5 of [elgamal2010]: the cutset bound for one code.** -/
theorem MDNetCode.mdnCutset_of_code (hP : IsPMF P) (hn : 0 < n) (c : MDNetCode s M n α β)
    {R : Fin N → Fin N → ℝ} (hM : ∀ j k, log (M j k) ≤ n * (R j k * log 2))
    (hM0 : ∀ j k, 0 < M j k) :
    mdnCutset P d s R fun l => c.distortion P d l := by
  classical
  obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  set ν := mixLaw (iidPMF P n) (Fin n) with hνd
  set W : (Fin n → α) × Fin n → α × ∀ l, β l := fun z =>
    (z.1 z.2, fun l => c.out z.1 l z.2) with hW
  have hr : IsPMF (dist ν W) := hν.dist W
  have hne : Nonempty (∀ l, β l) := by
    obtain ⟨z⟩ : Nonempty ((Fin n → α) × Fin n) := ⟨(fun _ => a₀, ⟨0, hn⟩)⟩
    exact ⟨(W z).2⟩
  obtain ⟨κ, hκ, hker⟩ := exists_kernel hr
  have hfst : dist (dist ν W) Prod.fst = P := by
    rw [← dist_comp_eq]
    exact dist_mix_coord hP hn
  have hL : jointOf P κ = dist ν W := by
    funext ⟨a, b⟩
    rw [hker a b, hfst]
    rfl
  have hcost : ∀ f : (α × ∀ l, β l) → ℝ, ∑ z, jointOf P κ z * f z = ∑ z, ν z * f (W z) :=
    fun f => by
      rw [hL]
      exact sum_dist_mul ν W f
  refine ⟨κ, hκ, fun l _ => ?_, fun S hS => ?_⟩
  · rw [hcost]
    exact le_of_eq (sum_mix_mul hn fun x i => d l (x i) (c.out x l i))
  · set τ := ∀ e : {e // e ∈ mdnCut S}, Fin (M e.val.1 e.val.2) with hτ
    let Mx : (Fin n → α) → τ := fun x e => c.edge x e.val.1 e.val.2
    let f : (Fin n → α) → Fin n → ∀ j : {j // j ∉ S}, β j := fun x i j => c.out x j i
    have hfM : ∀ x x', Mx x = Mx x' → f x = f x' := fun x x' h => by
      funext i j
      have hout := c.out_congr hS (x := x) (x' := x') (S := S) (fun a ha b hb => by
        exact congrFun h ⟨(a, b), mem_filter.2 ⟨mem_univ _, ha, hb⟩⟩) j.property
      simp only [f]
      rw [hout]
    let Y : Fin n → τ → ∀ j : {j // j ∉ S}, β j := fun i t =>
      if h : ∃ x, Mx x = t then f h.choose i else (hne.some · )
    have hY : ∀ i x, Y i (Mx x) = f x i := fun i x => by
      have h : ∃ x', Mx x' = Mx x := ⟨x, rfl⟩
      simp only [Y, h, ↓reduceDIte]
      rw [hfM _ _ h.choose_spec]
    have hb := mutualInfo_mix_le hP hn Mx Y
    have hcard : log (Fintype.card τ) ≤ n * ((∑ e ∈ mdnCut S, R e.1 e.2) * log 2) := by
      rw [Fintype.card_pi]
      simp only [Fintype.card_fin]
      push_cast
      rw [log_prod fun e _ => by exact_mod_cast (hM0 _ _).ne',
        ← sum_coe_sort (mdnCut S) fun e => R e.1 e.2, sum_mul, mul_sum]
      exact sum_le_sum fun e _ => hM _ _
    have e₁ : I[Prod.fst : fun z : α × ∀ l, β l => swRest S z.2 ; jointOf P κ] =
        I[fun z : (Fin n → α) × Fin n => z.1 z.2 : fun z => Y z.2 (Mx z.1) ; ν] := by
      rw [hL, ← mutualInfo_comp W]
      congr 1
      funext z
      rw [hY]
      rfl
    rw [e₁]
    refine hb.trans ?_
    rw [inv_mul_le_iff₀ hn']
    exact hcard

end Code

/-! ### The cutset outer bound -/

section Outer

variable {P : α → ℝ} {d : ∀ l, α → β l → ℝ} {s : Fin N}

/-- The set of the rates and distortions satisfying the cutset bound is closed. -/
theorem isClosed_mdnCutset (hP : IsPMF P) (d : ∀ l, α → β l → ℝ) (s : Fin N) :
    IsClosed {t : (Fin N → Fin N → ℝ) × (Fin N → ℝ) | mdnCutset P d s t.1 t.2} := by
  classical
  set F : Finset (Fin N) → (α → (∀ l, β l) → ℝ) → ℝ := fun S κ =>
    H[Prod.fst ; jointOf P κ] + H[fun z : α × ∀ l, β l => swRest S z.2 ; jointOf P κ] -
      H[pair Prod.fst (fun z : α × ∀ l, β l => swRest S z.2) ; jointOf P κ] with hF
  have hc : ∀ S, Continuous (F S) := fun S => ((continuous_entropyRV_jointOf P _).add
    (continuous_entropyRV_jointOf P _)).sub (continuous_entropyRV_jointOf P _)
  have hT : IsClosed {p : (α → (∀ l, β l) → ℝ) × (Fin N → Fin N → ℝ) × (Fin N → ℝ) |
      (∀ l, l ≠ s → ∑ z, jointOf P p.1 z * d l z.1 (z.2 l) ≤ p.2.2 l) ∧
      ∀ S : Finset (Fin N), s ∈ S → F S p.1 ≤ (∑ e ∈ mdnCut S, p.2.1 e.1 e.2) * log 2} := by
    have e : {p : (α → (∀ l, β l) → ℝ) × (Fin N → Fin N → ℝ) × (Fin N → ℝ) |
        (∀ l, l ≠ s → ∑ z, jointOf P p.1 z * d l z.1 (z.2 l) ≤ p.2.2 l) ∧
        ∀ S : Finset (Fin N), s ∈ S → F S p.1 ≤ (∑ e ∈ mdnCut S, p.2.1 e.1 e.2) * log 2} =
        (⋂ l, ⋂ _ : l ≠ s, {p : (α → (∀ l, β l) → ℝ) × (Fin N → Fin N → ℝ) × (Fin N → ℝ) |
          ∑ z, jointOf P p.1 z * d l z.1 (z.2 l) ≤ p.2.2 l}) ∩
        ⋂ S : Finset (Fin N), ⋂ _ : s ∈ S,
          {p : (α → (∀ l, β l) → ℝ) × (Fin N → Fin N → ℝ) × (Fin N → ℝ) |
            F S p.1 ≤ (∑ e ∈ mdnCut S, p.2.1 e.1 e.2) * log 2} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iInter]
      rfl
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun l => isClosed_iInter fun _ => ?_)
      (isClosed_iInter fun S => isClosed_iInter fun _ => ?_)
    · refine isClosed_le (?_ : Continuous _) (by fun_prop)
      exact (continuous_sum_jointOf (β := ∀ l, β l) P fun z => d l z.1 (z.2 l)).comp continuous_fst
    · refine isClosed_le ((hc S).comp continuous_fst) ?_
      refine Continuous.mul (continuous_finsetSum _ fun e _ => ?_) continuous_const
      fun_prop
  have h := isClosed_exists_mem_compact (isCompact_setOf_isChannel (α := α) (β := ∀ l, β l)) hT
  convert h using 1
  ext t
  simp only [Set.mem_ofPred_eq, mdnCutset]
  refine exists_congr fun κ => ?_
  constructor
  · rintro ⟨hκ, a, b⟩
    have hμ := jointOf_isPMF hP hκ
    refine ⟨hκ, a, fun S hS => ?_⟩
    have := b S hS
    rwa [mutualInfo_eq_add_sub hμ] at this
  · rintro ⟨hκ, a, b⟩
    have hκ' : IsChannel κ := hκ
    have hμ := jointOf_isPMF hP hκ'
    refine ⟨hκ', a, fun S hS => ?_⟩
    rw [mutualInfo_eq_add_sub hμ]
    exact b S hS

/-- An achievable rate tuple satisfies the cutset bound. -/
theorem IsAchievableMDN.mdnCutset (hP : IsPMF P) {E : Finset (Fin N × Fin N)}
    {R : Fin N → Fin N → ℝ} {D : Fin N → ℝ} (h : IsAchievableMDN P d s E R D) :
    mdnCutset P d s R D := by
  obtain ⟨hR, -, hc⟩ := h
  have hε : ∀ ε > 0, InfoTheory.mdnCutset P d s R fun l => D l + ε := fun ε hε => by
    obtain ⟨n, ⟨c, hd⟩, hn⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
    obtain ⟨κ, hκ, a, b⟩ := c.mdnCutset_of_code (d := d) hP hn (R := R)
      (fun j k => log_two_pow_floor_le n (hR j k)) (fun j k => by positivity)
    exact ⟨κ, hκ, fun l hl => (a l hl).trans (hd l hl), b⟩
  have hlim : Tendsto (fun k : ℕ => ((R, fun l => D l + 1 / ((k : ℝ) + 1)) :
      (Fin N → Fin N → ℝ) × (Fin N → ℝ))) atTop (𝓝 (R, D)) := by
    refine tendsto_const_nhds.prodMk_nhds (tendsto_pi_nhds.2 fun l => ?_)
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact (isClosed_mdnCutset hP d s).mem_of_tendsto hlim
    (Eventually.of_forall fun k => hε _ (by positivity))

/-- **Page 21-5 of [elgamal2010]: the cutset outer bound on the rate–distortion region.** -/
theorem mdnRegion_subset_mdnCutset (hP : IsPMF P) {E : Finset (Fin N × Fin N)} {D : Fin N → ℝ}
    {R : Fin N → Fin N → ℝ} (h : R ∈ mdnRegion P d s E D) : mdnCutset P d s R D := by
  have hslice : IsClosed {R : Fin N → Fin N → ℝ | InfoTheory.mdnCutset P d s R D} :=
    (isClosed_mdnCutset hP d s).preimage
      (f := fun R : Fin N → Fin N → ℝ => (R, D)) (by fun_prop)
  exact closure_minimal (fun R' hR' => IsAchievableMDN.mdnCutset hP hR') hslice h

end Outer

/-! ### Trees -/

section Tree

variable {P : α → ℝ} {d : ∀ l, α → β l → ℝ} {s : Fin N}

/-- The edges of the tree with the parent function `par`. -/
def treeEdges (s : Fin N) (par : Fin N → Fin N) : Finset (Fin N × Fin N) :=
  (univ.filter fun k => k ≠ s).image fun k => (par k, k)

open Classical in
/-- `S_kᶜ` of page 21-6: the node `k` and the nodes whose path from the source goes through `k`. -/
def treeDesc (par : Fin N → Fin N) (k : Fin N) : Finset (Fin N) :=
  univ.filter fun l => ∃ t : ℕ, par^[t] l = k

/-- A rooted tree: the root is its own parent, and the parents of the other nodes are lower. -/
structure IsRootedTree (s : Fin N) (par : Fin N → Fin N) : Prop where
  /-- The root. -/
  root : par s = s
  /-- The parents are lower. -/
  lt : ∀ k, k ≠ s → par k < k

lemma IsRootedTree.iterate_le {par : Fin N → Fin N} (h : IsRootedTree s par) (t : ℕ) (l : Fin N) :
    par^[t] l ≤ l := by
  induction t generalizing l with
  | zero => exact le_rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    refine (ih _).trans ?_
    by_cases hl : l = s
    · rw [hl, h.root]
    · exact (h.lt l hl).le

/-- **Theorem 1 of Lecture 21 of [elgamal2010], page 21-6: the converse, for a tree.** The rate of
the edge into `k` is at least `I(X; X̂(S_kᶜ))`, where `S_kᶜ` is `k` with the nodes after it. -/
theorem mdnCutset_tree (hP : IsPMF P) {par : Fin N → Fin N} (hpar : IsRootedTree s par)
    {D : Fin N → ℝ} {R : Fin N → Fin N → ℝ} (h : R ∈ mdnRegion P d s (treeEdges s par) D)
    (h0 : ∀ j k, (j, k) ∉ treeEdges s par → R j k = 0) :
    ∃ κ : α → (∀ l, β l) → ℝ, IsChannel κ ∧
      (∀ l, l ≠ s → ∑ z, jointOf P κ z * d l z.1 (z.2 l) ≤ D l) ∧
      ∀ k, k ≠ s →
        I[Prod.fst : fun z : α × ∀ l, β l => swRest (treeDesc par k)ᶜ z.2 ; jointOf P κ] ≤
          R (par k) k * log 2 := by
  classical
  obtain ⟨κ, hκ, a, b⟩ := mdnRegion_subset_mdnCutset hP h
  refine ⟨κ, hκ, a, fun k hk => ?_⟩
  have hs : s ∈ (treeDesc par k)ᶜ := by
    simp only [treeDesc, mem_compl, mem_filter, mem_univ, true_and, not_exists]
    intro t ht
    have hst : par^[t] s = s := Function.iterate_fixed hpar.root t
    exact hk (ht.symm.trans hst)
  refine (b _ hs).trans (le_of_eq ?_)
  congr 1
  refine sum_eq_single (par k, k) (fun e he hne => ?_) fun hn => ?_
  · obtain ⟨a', b'⟩ := e
    refine h0 _ _ fun hE => hne ?_
    obtain ⟨l, hl, hl'⟩ := mem_image.1 hE
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl'
    have hc := (mem_filter.1 he).2
    have hb : l ∈ treeDesc par k := by simpa using hc.2
    obtain ⟨t, ht⟩ := (mem_filter.1 hb).2
    cases t with
    | zero =>
      have : l = k := ht
      rw [this]
    | succ t =>
      rw [Function.iterate_succ_apply] at ht
      have hm : par l ∈ treeDesc par k := mem_filter.2 ⟨mem_univ _, t, ht⟩
      exact absurd hm (mem_compl.1 hc.1)
  · refine absurd (mem_filter.2 ⟨mem_univ _, ?_, ?_⟩) hn
    · simp only [treeDesc, mem_compl, mem_filter, mem_univ, true_and, not_exists]
      intro t ht
      have h₁ := hpar.iterate_le t (par k)
      rw [ht] at h₁
      exact absurd (hpar.lt k hk) (not_lt.2 h₁)
    · simp only [treeDesc, mem_compl, mem_filter, mem_univ, true_and, not_not]
      exact ⟨0, rfl⟩

end Tree

/-! ### Codes from the contents of the edges -/

section Parts

variable {s : Fin N} {M : Fin N → Fin N → ℕ} {n : ℕ} {T : Type*} [Finite T] [Nonempty T]

omit [Fintype α] [∀ l, Fintype (β l)] in
open Classical in
/-- **A code from a description of the contents of the edges.** The value `t` of a finite type is
known at the source node. The edge `(j, k)` carries `part j k t`. The node `k` knows `know k t`,
which it computes from what it receives, and from which it computes what it sends. -/
theorem MDNetCode.ofParts (part : Fin N → Fin N → T → T)
    (know : Fin N → T → T) (merge : ∀ k, (∀ j, j < k → T) → T) (e : (Fin n → α) → T)
    (C : ∀ l, T → Fin n → β l)
    (hcard : ∀ j k, Nat.card (Set.range (part j k)) ≤ M j k)
    (hmerge : ∀ k t, k ≠ s → merge k (fun j _ => part j k t) = know k t)
    (hpk : ∀ k l t, k ≠ s → part k l (know k t) = part k l t)
    (hC : ∀ l t, l ≠ s → C l (know l t) = C l t) :
    ∃ c : MDNetCode s M n α β, ∀ x l, l ≠ s → c.out x l = C l (e x) := by
  have := Fintype.ofFinite T
  have hemb : ∀ j k, Nonempty (Set.range (part j k) ↪ Fin (M j k)) := fun j k => by
    refine Function.Embedding.nonempty_of_card_le ?_
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hcard j k
  let emb : ∀ j k, Set.range (part j k) ↪ Fin (M j k) := fun j k => (hemb j k).some
  have hne : ∀ j k, Nonempty (Set.range (part j k)) := fun j k =>
    ⟨⟨part j k (Classical.arbitrary T), ⟨_, rfl⟩⟩⟩
  let idx : ∀ j k, T → Fin (M j k) := fun j k t => emb j k ⟨part j k t, ⟨t, rfl⟩⟩
  let unidx : ∀ j k, Fin (M j k) → T := fun j k m => (Function.invFun (emb j k) m).val
  have hun : ∀ j k t, unidx j k (idx j k t) = part j k t := fun j k t => by
    simp only [unidx, idx]
    rw [Function.leftInverse_invFun (emb j k).injective]
  have hidx : ∀ j k t t', part j k t = part j k t' → idx j k t = idx j k t' := fun j k t t' h => by
    simp only [idx]
    congr 2
  let c : MDNetCode s M n α β :=
    { enc := fun k l h x => idx k l (if k = s then e x else merge k fun j hj => unidx j k (h j hj))
      relay := fun k l h x x' hk => by simp [hk]
      dec := fun l h => C l (merge l fun j hj => unidx j l (h j hj)) }
  have hedge : ∀ x k l, c.edge x k l = idx k l (e x) := by
    intro x k
    induction k using WellFoundedLT.induction with
    | ind k ih =>
      intro l
      rw [c.edge_eq]
      by_cases hk : k = s
      · simp only [c, hk, ↓reduceIte]
      · have h₁ : (fun j (hj : j < k) => unidx j k (c.edge x j k)) = fun j _ => part j k (e x) := by
          funext j hj
          rw [ih j hj k, hun]
        simp only [c, hk, ↓reduceIte]
        refine hidx _ _ _ _ ?_
        have h₂ := congrArg (merge k) h₁
        simp only [c] at h₂
        rw [h₂, hmerge k _ hk, hpk k l _ hk]
  refine ⟨c, fun x l hl => ?_⟩
  simp only [MDNetCode.out]
  have h₁ : (fun j (hj : j < l) => unidx j l (c.edge x j l)) = fun j _ => part j l (e x) := by
    funext j hj
    rw [hedge, hun]
  have h₂ : C l (merge l fun j hj => unidx j l (c.edge x j l)) =
      C l (merge l fun j _ => part j l (e x)) := by
    rw [h₁]
  change C l (merge l fun j hj => unidx j l (c.edge x j l)) = C l (e x)
  rw [h₂, hmerge l _ hl, hC l _ hl]

end Parts

end InfoTheory
