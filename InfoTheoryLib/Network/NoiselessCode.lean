/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.FlowDecomposition

/-!
# Noiseless networks: codes and the cutset bound

A noiseless network is a weighted directed acyclic graph. Every node has a message, which may be
trivial, and every node may wish to decode the messages of other nodes. This is the setup of page
16-24 of El Gamal and Kim; relay and multicast networks are the case of one nonzero rate.

## Main definitions

* `NoiselessNetwork V`: a network with capacities `C j k`, going up in the order of the nodes.
* `NetCode V A M`: a code with edge alphabets `A` and message alphabets `M`.
* `NetCode.edge`, `NetCode.out`: the index sent on an edge and the message decoded by a node.
* `NetCode.errProb`: the probability of error.
* `RateCode`, `IsAchievable`, `capacityRegion`, `IsAchievableZE`: codes with rates in bits.
* `cutSources`, `cutsetRegion`: the cutset outer bound.
* `multicastD`, `singleRate`, `multicastCapacity`: the case of one source.

## Main statements

* `NetCode.cut_bound`: the counting form of the cutset bound.
* `IsAchievable.mem_cutsetRegion`: the cutset outer bound of page 16-25.
* `NetCode.exists_relabel`: a code that is always correct keeps working with other alphabets.

## Implementation notes

The notes prove the cutset bound with Fano's inequality. Here the correctly decoded message tuples
are counted: on them, the messages outside the cut's sources and the indices across the cut
determine the tuple. This gives `(1 - P_e) 2^{n ∑ R_j} ≤ 2^{n C(S)}`, so the bound is a strong
converse.

A pair of nodes that is not an edge has capacity `0`, so its index set has one element. Edges carry
`2 ^ ⌊n C⌋` indices and messages have `2 ^ ⌈n R⌉` values.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {V : Type*}

/-! ### Networks and codes -/

/-- **Lecture 16 of [elgamal2010], page 16-2.** A noiseless network: a weighted directed acyclic
graph. The nodes are ordered so that edges go up, as on page 16-23, and a pair that is not an edge
has capacity `0`. -/
structure NoiselessNetwork (V : Type*) [LT V] where
  /-- The capacities of the edges. -/
  C : V → V → ℝ
  /-- Capacities are nonnegative. -/
  nonneg : ∀ j k, 0 ≤ C j k
  /-- Edges go up. -/
  acyclic : ∀ j k, 0 < C j k → j < k

/-- **Lecture 16 of [elgamal2010], page 16-24.** A code for a noiseless network: encoder `k` maps
the indices received from lower nodes and its own message to an index on each edge, and node `l`
decodes the message of node `j` from the indices it receives. -/
structure NetCode (V : Type*) [LT V] (A : V → V → Type*) (M : V → Type*) where
  /-- The encoder of edge `(k, l)`. -/
  enc : ∀ k l, (∀ j, j < k → A j k) → M k → A k l
  /-- The decoder at node `l` of the message of node `j`. -/
  dec : ∀ l j, (∀ k, k < l → A k l) → M j

section Eval

/-- The index sent on the edge `(k, l)` when the messages are `m`. -/
def NetCode.edge [LinearOrder V] [Finite V] {A : V → V → Type*} {M : V → Type*}
    (c : NetCode V A M) (m : ∀ j, M j) (k l : V) : A k l :=
  c.enc k l (fun j _ => c.edge m j k) (m k)
termination_by (wellFounded_lt (α := V)).wrap k
decreasing_by assumption

variable [LinearOrder V] [Finite V] {A : V → V → Type*} {M : V → Type*}

lemma NetCode.edge_eq (c : NetCode V A M) (m : ∀ j, M j) (k l : V) :
    c.edge m k l = c.enc k l (fun j _ => c.edge m j k) (m k) := by
  rw [NetCode.edge]

/-- The message of node `j` decoded by node `l` when the messages are `m`. -/
def NetCode.out (c : NetCode V A M) (m : ∀ j, M j) (l j : V) : M j :=
  c.dec l j fun k _ => c.edge m k l

/-- All destinations decode correctly. -/
def NetCode.Correct (c : NetCode V A M) (D : V → Finset V) (m : ∀ j, M j) : Prop :=
  ∀ j, ∀ l ∈ D j, c.out m l j = m j

/-- If two message tuples agree outside `S` and the indices across the cut `S` agree, then all
indices out of nodes outside `S` agree. -/
lemma NetCode.edge_congr (c : NetCode V A M) {m m' : ∀ j, M j} {S : Finset V}
    (hm : ∀ j, j ∉ S → m j = m' j) (he : ∀ j ∈ S, ∀ k, k ∉ S → c.edge m j k = c.edge m' j k) :
    ∀ j, j ∉ S → ∀ k, c.edge m j k = c.edge m' j k := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    intro hj k
    rw [c.edge_eq m, c.edge_eq m', hm j hj]
    congr 1
    funext i hi
    by_cases hiS : i ∈ S
    · exact he i hiS j hj
    · exact ih i hi hiS j

/-- A node outside `S` decodes the same when the messages outside `S` and the indices across the cut
`S` agree. -/
lemma NetCode.out_congr (c : NetCode V A M) {m m' : ∀ j, M j} {S : Finset V}
    (hm : ∀ j, j ∉ S → m j = m' j) (he : ∀ j ∈ S, ∀ k, k ∉ S → c.edge m j k = c.edge m' j k)
    {l : V} (hl : l ∉ S) (j : V) : c.out m l j = c.out m' l j := by
  simp only [NetCode.out]
  congr 1
  funext k _
  by_cases hk : k ∈ S
  · exact he k hk l hl
  · exact c.edge_congr hm he k hk l

end Eval

/-! ### The probability of error and the cutset bound -/

/-- **Page 16-25 of [elgamal2010].** The nodes of `S` with a destination outside `S`. -/
def cutSources [DecidableEq V] [Fintype V] (D : V → Finset V) (S : Finset V) : Finset V :=
  S.filter fun j => (D j ∩ Sᶜ).Nonempty

section Prob

variable [LinearOrder V] [Fintype V] {A : V → V → Type*} {M : V → Type*}
  [∀ j, Fintype (M j)]

open Classical in
/-- **Page 16-24 of [elgamal2010].** The probability of error, for uniform messages. -/
def NetCode.errProb (c : NetCode V A M) (D : V → Finset V) : ℝ :=
  (#{m : ∀ j, M j | ¬ c.Correct D m} : ℝ) / Fintype.card (∀ j, M j)

lemma NetCode.errProb_nonneg (c : NetCode V A M) (D : V → Finset V) : 0 ≤ c.errProb D := by
  unfold NetCode.errProb
  positivity

open Classical in
lemma NetCode.one_sub_errProb [∀ j, Nonempty (M j)] (c : NetCode V A M) (D : V → Finset V) :
    1 - c.errProb D = (#{m : ∀ j, M j | c.Correct D m} : ℝ) / Fintype.card (∀ j, M j) := by
  have hpos : (0 : ℝ) < Fintype.card (∀ j, M j) := by
    exact_mod_cast Fintype.card_pos
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (∀ j, M j)))
    (fun m => c.Correct D m)
  rw [Finset.card_univ] at hsum
  unfold NetCode.errProb
  rw [eq_div_iff hpos.ne', sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
  have : (#{m : ∀ j, M j | c.Correct D m} : ℝ) + #{m : ∀ j, M j | ¬ c.Correct D m} =
      Fintype.card (∀ j, M j) := by exact_mod_cast hsum
  linarith

lemma NetCode.errProb_le_one [∀ j, Nonempty (M j)] (c : NetCode V A M) (D : V → Finset V) :
    c.errProb D ≤ 1 := by
  classical
  have h := c.one_sub_errProb D
  have : (0 : ℝ) ≤ (#{m : ∀ j, M j | c.Correct D m} : ℝ) / Fintype.card (∀ j, M j) := by
    positivity
  linarith

lemma NetCode.errProb_eq_zero (c : NetCode V A M) {D : V → Finset V}
    (h : ∀ m, c.Correct D m) : c.errProb D = 0 := by
  classical
  unfold NetCode.errProb
  rw [Finset.filter_false_of_mem fun m _ => not_not.mpr (h m)]
  simp

variable [∀ j k, Fintype (A j k)]

/-- **The cutset bound, counting form.** The fraction of correctly decoded message tuples, times the
number of messages of the sources of a cut, is at most the number of index tuples across the cut. -/
theorem NetCode.cut_bound [∀ j, Nonempty (M j)] (c : NetCode V A M) (D : V → Finset V)
    (S : Finset V) :
    (1 - c.errProb D) * ∏ j ∈ cutSources D S, (Fintype.card (M j) : ℝ) ≤
      ∏ j ∈ S, ∏ k ∈ Sᶜ, (Fintype.card (A j k) : ℝ) := by
  classical
  set T := cutSources D S with hT
  have hTS : ∀ j, j ∉ S → j ∉ T := fun j hj hjT => hj (Finset.mem_filter.mp hjT).1
  let Φ : (∀ j, M j) → (∀ j : ↥(Tᶜ), M j) × (∀ p : ↥(S ×ˢ Sᶜ), A p.1.1 p.1.2) :=
    fun m => (fun j => m j, fun p => c.edge m p.1.1 p.1.2)
  have hinj : Set.InjOn Φ {m | c.Correct D m} := by
    intro m hm m' hm' hΦ
    have h₁ : ∀ j, j ∉ T → m j = m' j := fun j hj =>
      congrFun (congrArg Prod.fst hΦ) ⟨j, Finset.mem_compl.mpr hj⟩
    have h₂ : ∀ j ∈ S, ∀ k, k ∉ S → c.edge m j k = c.edge m' j k := fun j hj k hk =>
      congrFun (congrArg Prod.snd hΦ)
        ⟨(j, k), Finset.mem_product.mpr ⟨hj, Finset.mem_compl.mpr hk⟩⟩
    funext j
    by_cases hj : j ∈ T
    · obtain ⟨hjS, l, hl⟩ := Finset.mem_filter.mp hj
      obtain ⟨hlD, hlS⟩ := Finset.mem_inter.mp hl
      rw [← hm j l hlD, ← hm' j l hlD]
      exact c.out_congr (fun i hi => h₁ i (hTS i hi)) h₂ (Finset.mem_compl.mp hlS) j
    · exact h₁ j hj
  have hcard : #{m : ∀ j, M j | c.Correct D m} ≤
      Fintype.card ((∀ j : ↥(Tᶜ), M j) × (∀ p : ↥(S ×ˢ Sᶜ), A p.1.1 p.1.2)) :=
    Finset.card_le_card_of_injOn Φ (fun _ _ => Finset.mem_univ _)
      (fun m hm m' hm' h => hinj (by simpa using hm) (by simpa using hm') h)
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi] at hcard
  have hX : (∏ p : ↥(S ×ˢ Sᶜ), (Fintype.card (A p.1.1 p.1.2) : ℝ)) =
      ∏ j ∈ S, ∏ k ∈ Sᶜ, (Fintype.card (A j k) : ℝ) := by
    rw [← Finset.prod_product']
    exact Finset.prod_coe_sort (S ×ˢ Sᶜ) fun p : V × V => (Fintype.card (A p.1 p.2) : ℝ)
  have hY : (∏ j : ↥(Tᶜ), (Fintype.card (M j) : ℝ)) = ∏ j ∈ Tᶜ, (Fintype.card (M j) : ℝ) :=
    Finset.prod_coe_sort Tᶜ fun j => (Fintype.card (M j) : ℝ)
  have hcard' : (#{m : ∀ j, M j | c.Correct D m} : ℝ) ≤
      (∏ j ∈ Tᶜ, (Fintype.card (M j) : ℝ)) * ∏ j ∈ S, ∏ k ∈ Sᶜ, (Fintype.card (A j k) : ℝ) := by
    rw [← hX, ← hY]
    exact_mod_cast hcard
  have hposT : (0 : ℝ) < ∏ j ∈ T, (Fintype.card (M j) : ℝ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast Fintype.card_pos
  have hposC : (0 : ℝ) < ∏ j ∈ Tᶜ, (Fintype.card (M j) : ℝ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast Fintype.card_pos
  have hall : (Fintype.card (∀ j, M j) : ℝ) =
      (∏ j ∈ T, (Fintype.card (M j) : ℝ)) * ∏ j ∈ Tᶜ, (Fintype.card (M j) : ℝ) := by
    rw [Finset.prod_mul_prod_compl, Fintype.card_pi]
    push_cast
    rfl
  rw [c.one_sub_errProb D, hall, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : (#{m : ∀ j, M j | c.Correct D m} : ℝ) * ∏ j ∈ T, (Fintype.card (M j) : ℝ) ≤
      ((∏ j ∈ Tᶜ, (Fintype.card (M j) : ℝ)) *
        ∏ j ∈ S, ∏ k ∈ Sᶜ, (Fintype.card (A j k) : ℝ)) * ∏ j ∈ T, (Fintype.card (M j) : ℝ) :=
    mul_le_mul_of_nonneg_right hcard' hposT.le
  linarith

end Prob

/-! ### Codes with rates -/

section Rates

variable [LinearOrder V] [Fintype V]

/-- **Page 16-24 of [elgamal2010].** A `(2^{nR_1}, …, 2^{nR_N}, n)` code: messages have `2 ^ ⌈n R⌉`
values and an edge of capacity `C` carries `2 ^ ⌊n C⌋` indices. -/
abbrev RateCode (N : NoiselessNetwork V) (R : V → ℝ) (n : ℕ) :=
  NetCode V (fun k l => Fin (2 ^ ⌊(n : ℝ) * N.C k l⌋₊)) (fun j => Fin (2 ^ ⌈(n : ℝ) * R j⌉₊))

instance (a : ℕ) : Nonempty (Fin (2 ^ a)) := ⟨⟨0, by positivity⟩⟩

instance (N : NoiselessNetwork V) (R : V → ℝ) (n : ℕ) : Nonempty (RateCode N R n) :=
  ⟨⟨fun _ _ _ _ => Classical.arbitrary _, fun _ _ _ => Classical.arbitrary _⟩⟩

/-- **Page 16-24 of [elgamal2010].** A rate tuple is achievable if there are codes whose probability
of error tends to zero. -/
def IsAchievable (N : NoiselessNetwork V) (D : V → Finset V) (R : V → ℝ) : Prop :=
  (∀ j, 0 ≤ R j) ∧ ∃ c : ∀ n, RateCode N R n, Tendsto (fun n => (c n).errProb D) atTop (𝓝 0)

/-- A rate tuple is achievable with zero error if, for all large `n`, there is a code that is always
correct. -/
def IsAchievableZE (N : NoiselessNetwork V) (D : V → Finset V) (R : V → ℝ) : Prop :=
  (∀ j, 0 ≤ R j) ∧ ∀ᶠ n in atTop, ∃ c : RateCode N R n, ∀ m, c.Correct D m

/-- **Page 16-24 of [elgamal2010].** The capacity region: the closure of the set of achievable rate
tuples. -/
def capacityRegion (N : NoiselessNetwork V) (D : V → Finset V) : Set (V → ℝ) :=
  closure {R | IsAchievable N D R}

/-- **Page 16-25 of [elgamal2010].** The cutset outer bound. A cut without sources gives the trivial
condition `0 ≤ C(S)`. -/
def cutsetRegion (N : NoiselessNetwork V) (D : V → Finset V) : Set (V → ℝ) :=
  {R | (∀ j, 0 ≤ R j) ∧ ∀ S : Finset V, ∑ j ∈ cutSources D S, R j ≤ cutCap N.C S}

lemma IsAchievableZE.isAchievable {N : NoiselessNetwork V} {D : V → Finset V} {R : V → ℝ}
    (h : IsAchievableZE N D R) : IsAchievable N D R := by
  refine ⟨h.1, ?_⟩
  have hex : ∀ n, ∃ c : RateCode N R n, (∃ c' : RateCode N R n, ∀ m, c'.Correct D m) →
      ∀ m, c.Correct D m := fun n => by
    by_cases hn : ∃ c' : RateCode N R n, ∀ m, c'.Correct D m
    · obtain ⟨c', hc'⟩ := hn
      exact ⟨c', fun _ => hc'⟩
    · exact ⟨Classical.arbitrary _, fun h' => absurd h' hn⟩
  choose c hc using hex
  refine ⟨c, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [h.2] with n hn
  exact ((c n).errProb_eq_zero (hc n hn)).symm

/-- **The cutset bound, in bits.** This is a strong converse: if the rates of the sources of a cut
exceed its capacity then the probability of correct decoding tends to zero exponentially fast. -/
theorem RateCode.cut_bound {N : NoiselessNetwork V} {R : V → ℝ} {n : ℕ} (c : RateCode N R n)
    (D : V → Finset V) (S : Finset V) :
    (1 - c.errProb D) * (2 : ℝ) ^ ((n : ℝ) * ∑ j ∈ cutSources D S, R j) ≤
      (2 : ℝ) ^ ((n : ℝ) * cutCap N.C S) := by
  have hb := NetCode.cut_bound c D S
  have h1 : 0 ≤ 1 - c.errProb D := sub_nonneg.mpr (c.errProb_le_one D)
  have hL : (2 : ℝ) ^ ((n : ℝ) * ∑ j ∈ cutSources D S, R j) ≤
      ∏ j ∈ cutSources D S, (Fintype.card (Fin (2 ^ ⌈(n : ℝ) * R j⌉₊)) : ℝ) := by
    rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
    refine prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
    rw [Fintype.card_fin]
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have hU : ∏ j ∈ S, ∏ k ∈ Sᶜ, (Fintype.card (Fin (2 ^ ⌊(n : ℝ) * N.C j k⌋₊)) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * cutCap N.C S) := by
    unfold cutCap
    rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
    refine prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
    rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
    refine prod_le_prod₀ (fun _ _ => by positivity) fun k _ => ?_
    rw [Fintype.card_fin]
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (N.nonneg _ _)))
  calc _ ≤ (1 - c.errProb D) * ∏ j ∈ cutSources D S,
        (Fintype.card (Fin (2 ^ ⌈(n : ℝ) * R j⌉₊)) : ℝ) := mul_le_mul_of_nonneg_left hL h1
    _ ≤ _ := hb
    _ ≤ _ := hU

/-- If `(1 - P) 2^{n a} ≤ 2^{n b}` for all `n`, and `P → 0`, then `a ≤ b`. -/
lemma le_of_tendsto_one_sub_mul_rpow {P : ℕ → ℝ} {a b : ℝ} (hP : Tendsto P atTop (𝓝 0))
    (h : ∀ n : ℕ, (1 - P n) * (2 : ℝ) ^ ((n : ℝ) * a) ≤ (2 : ℝ) ^ ((n : ℝ) * b)) : a ≤ b := by
  by_contra hab
  push Not at hab
  have hgap : 0 < a - b := sub_pos.mpr hab
  -- `1 - P n ≤ 2^{-n (a - b)} → 0`
  have hbound : ∀ n : ℕ, 1 - P n ≤ ((2 : ℝ) ^ (-(a - b))) ^ n := by
    intro n
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * a) := by positivity
    have hn := h n
    rw [← le_div_iff₀ hpos] at hn
    refine hn.trans (le_of_eq ?_)
    rw [← Real.rpow_sub (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hr : (2 : ℝ) ^ (-(a - b)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr
  have h1 : Tendsto (fun n => 1 - P n) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hP
  have := le_of_tendsto_of_tendsto' h1 hlim hbound
  norm_num at this

/-- **Cutset outer bound, page 16-25 of [elgamal2010].** -/
theorem IsAchievable.mem_cutsetRegion {N : NoiselessNetwork V} {D : V → Finset V} {R : V → ℝ}
    (h : IsAchievable N D R) : R ∈ cutsetRegion N D := by
  obtain ⟨h0, c, hc⟩ := h
  exact ⟨h0, fun S => le_of_tendsto_one_sub_mul_rpow hc fun n => (c n).cut_bound D S⟩

/-- The cutset outer bound is closed. -/
lemma isClosed_cutsetRegion (N : NoiselessNetwork V) (D : V → Finset V) :
    IsClosed (cutsetRegion N D) := by
  have : cutsetRegion N D = (⋂ j, {R : V → ℝ | 0 ≤ R j}) ∩
      ⋂ S : Finset V, {R : V → ℝ | ∑ j ∈ cutSources D S, R j ≤ cutCap N.C S} := by
    ext R
    simp [cutsetRegion]
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun j => ?_) (isClosed_iInter fun S => ?_)
  · exact isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (by fun_prop) continuous_const

/-- **Cutset outer bound, page 16-25 of [elgamal2010].** The capacity region lies in the cutset
region. -/
theorem capacityRegion_subset_cutsetRegion (N : NoiselessNetwork V) (D : V → Finset V) :
    capacityRegion N D ⊆ cutsetRegion N D :=
  closure_minimal (fun _ h => IsAchievable.mem_cutsetRegion h) (isClosed_cutsetRegion N D)

/-! ### One source -/

/-- **Page 16-23 of [elgamal2010].** Only node `s` has destinations. -/
def multicastD (s : V) (D : Finset V) : V → Finset V := fun j => if j = s then D else ∅

/-- **Page 16-23 of [elgamal2010].** Only node `s` has a message of positive rate. -/
def singleRate (s : V) (R : ℝ) : V → ℝ := fun j => if j = s then R else 0

/-- **Page 16-3 and page 16-11 of [elgamal2010].** The capacity of a noiseless multicast network:
the supremum of the achievable rates. A relay network is the case `D = {t}`. -/
def multicastCapacity (N : NoiselessNetwork V) (s : V) (D : Finset V) : ℝ :=
  sSup {R | IsAchievable N (multicastD s D) (singleRate s R)}

/-- **Cutset upper bound, page 16-12 of [elgamal2010].** -/
theorem IsAchievable.le_minCut {N : NoiselessNetwork V} {s t : V} {D : Finset V} {R : ℝ}
    (h : IsAchievable N (multicastD s D) (singleRate s R)) (ht : t ∈ D) (hst : s ≠ t) :
    R ≤ minCut N.C s t := by
  refine InfoTheory.le_minCut _ hst fun S hs htS => ?_
  have hb := h.mem_cutsetRegion.2 S
  have hT : cutSources (multicastD s D) S = {s} := by
    ext j
    rw [Finset.mem_singleton]
    constructor
    · intro hj
      obtain ⟨-, hj⟩ := Finset.mem_filter.mp hj
      by_contra hjs
      simp [multicastD, hjs] at hj
    · rintro rfl
      exact Finset.mem_filter.mpr ⟨hs, t, by simp [multicastD, ht, htS]⟩
  rw [hT, Finset.sum_singleton] at hb
  simpa [singleRate] using hb

/-- With rates zero there is nothing to send. -/
lemma isAchievable_zero (N : NoiselessNetwork V) (D : V → Finset V) :
    IsAchievable N D fun _ => 0 := by
  refine IsAchievableZE.isAchievable ⟨fun _ => le_rfl, Eventually.of_forall fun n => ?_⟩
  refine ⟨Classical.arbitrary _, fun m j l _ => ?_⟩
  have : Subsingleton (Fin (2 ^ ⌈(n : ℝ) * (fun _ : V => (0 : ℝ)) j⌉₊)) := by
    simp only [mul_zero, Nat.ceil_zero, pow_zero]
    infer_instance
  exact Subsingleton.elim _ _

/-- The capacity from the two directions of a coding theorem. -/
lemma multicastCapacity_eq {N : NoiselessNetwork V} {s : V} {D : Finset V} {C : ℝ}
    (h₁ : ∀ R, 0 ≤ R → R < C → IsAchievable N (multicastD s D) (singleRate s R))
    (h₂ : ∀ R, IsAchievable N (multicastD s D) (singleRate s R) → R ≤ C) :
    multicastCapacity N s D = C := by
  have h0 : IsAchievable N (multicastD s D) (singleRate s 0) := by
    have : singleRate s (0 : ℝ) = fun _ : V => (0 : ℝ) := by
      funext j
      simp [singleRate]
    rw [this]
    exact isAchievable_zero N _
  refine le_antisymm (csSup_le ⟨0, h0⟩ h₂) (le_of_forall_lt fun a ha => ?_)
  by_cases ha0 : a < 0
  · exact lt_of_lt_of_le ha0 (le_csSup ⟨C, h₂⟩ h0)
  · obtain ⟨b, hab, hbC⟩ := exists_between ha
    exact lt_of_lt_of_le hab
      (le_csSup ⟨C, h₂⟩ (h₁ b (by linarith [not_lt.mp ha0]) hbC))

end Rates

/-! ### Changing the alphabets -/

section Relabel

variable [LinearOrder V] [Finite V] {A A' : V → V → Type*} {M M' : V → Type*}

/-- A code that is always correct keeps working when the messages are restricted to a subset, and
each edge alphabet is replaced by one with at least as many elements as the indices the edge really
uses. So the alphabet of a pair that is not an edge can be a single point if its index is constant.
-/
theorem NetCode.exists_relabel (c : NetCode V A M) {D : V → Finset V}
    (h : ∀ m, c.Correct D m) [∀ j, Nonempty (M j)] [∀ j, Nonempty (M' j)]
    [∀ j k, Nonempty (A' j k)] (μ : ∀ j, M' j → M j) (hμ : ∀ j, Function.Injective (μ j))
    (ι : ∀ j k, A j k → A' j k)
    (hι : ∀ j k, Set.InjOn (ι j k) (Set.range fun m : ∀ j, M j => c.edge m j k)) :
    ∃ c' : NetCode V A' M', ∀ m, c'.Correct D m := by
  classical
  have hA : ∀ j k, Nonempty (A j k) := fun j k =>
    ⟨c.edge (fun _ => Classical.arbitrary _) j k⟩
  let ρ : ∀ j k, A' j k → A j k := fun j k =>
    Function.invFunOn (ι j k) (Set.range fun m : ∀ j, M j => c.edge m j k)
  have hρ : ∀ j k (m : ∀ j, M j), ρ j k (ι j k (c.edge m j k)) = c.edge m j k := fun j k m =>
    (hι j k).leftInvOn_invFunOn ⟨m, rfl⟩
  let c' : NetCode V A' M' :=
    ⟨fun k l u m' => ι k l (c.enc k l (fun j hj => ρ j k (u j hj)) (μ k m')),
      fun l j u => Function.invFun (μ j) (c.dec l j fun k hk => ρ k l (u k hk))⟩
  have hedge : ∀ (m' : ∀ j, M' j) (k l : V),
      c'.edge m' k l = ι k l (c.edge (fun j => μ j (m' j)) k l) := by
    intro m' k
    induction k using WellFoundedLT.induction with
    | ind k ih =>
      intro l
      rw [c'.edge_eq, c.edge_eq]
      change ι k l (c.enc k l (fun j hj => ρ j k (c'.edge m' j k)) (μ k (m' k))) = _
      congr 2
      funext j hj
      rw [ih j hj k, hρ]
  refine ⟨c', fun m' j l hl => ?_⟩
  have hout : c'.out m' l j = Function.invFun (μ j) (c.out (fun j => μ j (m' j)) l j) := by
    change Function.invFun (μ j) (c.dec l j fun k hk => ρ k l (c'.edge m' k l)) = _
    congr 2
    funext k _
    rw [hedge, hρ]
  rw [hout, h _ j l hl]
  exact Function.leftInverse_invFun (hμ j) _

end Relabel

end InfoTheory
