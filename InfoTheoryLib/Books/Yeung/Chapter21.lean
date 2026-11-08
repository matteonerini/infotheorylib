/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.Yeung.Chapter20
public import InfoTheoryLib.Network.MultiSource
public import InfoTheoryLib.Network.NoiselessRouting

/-!
# Yeung, Chapter 21: Multi-Source Network Coding

This file indexes the formalization of Chapter 21 of [yeung2008], and contains its worked examples,
so the index is checked by Lean. It cites the draft of 15 November 2007, which numbers definitions,
theorems and examples with one counter per chapter. The end-of-chapter problems and the historical
notes are not included.

## Conventions

* **Codes and achievability.** The block codes, achievable rate tuples and the achievable rate
  region of Definitions 21.1–21.3 are those of the noiseless networks of Lecture 16 of
  [elgamal2010]: `NetCode`, `RateCode`, `IsAchievable` and `capacityRegion`
  (`Network.NoiselessCode`). There every node has a message, possibly of rate `0`, and may demand
  the messages of other nodes; the nodes are ordered upstream to downstream; an edge of capacity `C`
  carries `2^{⌊n C⌋}` indices, instead of `η_e` with `n⁻¹ log η_e ≤ R_e + ε`; and the error
  criterion is the probability `P_e` that some demand is decoded wrongly. Every probability `Δ_t` at
  a sink is at most `P_e`, and `P_e ≤ ∑_t Δ_t`.
* **Figures 21.1 and 21.3.** The two sources are generated at node `1`, while a message of
  `NetCode` belongs to one node. They are the messages of two dummy nodes `0` and `1` with edges of
  capacity `2` into node `1`, so the nodes `1, 2, 3, 4` of the book are `2, 3, 4, 5`
  (`twoLayerNet`).
* **The regions of Section 21.4.** A problem is a `MultiSourceProblem V E σ`, with sources `σ`, and
  the random variables `Y_s` and `U_e` of (21.21) are indexed by `σ ⊕ E`. The region `Γ**_N` of
  (21.25) is `entropicRegion (σ ⊕ E)`, whose random variables have finite alphabets, and `Γ_N` of
  Section 21.5 is `shannonRegion (σ ⊕ E)` (`InfoInequalities`).

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 21.1 The Max-Flow Bounds
* Figure 21.1: `twoLayerNet`, `fig211D` (here).
* (21.1)–(21.3): `fig211_maxflow_bounds` (here), from the cutset bound
  `IsAchievable.mem_cutsetRegion` (`Network.NoiselessCode`).
* The achievability of the max-flow bounds of Figure 21.1, by the routing scheme of Figure 21.1(b):
  `fig211Routing`, `fig211_isAchievable_iff` (here).
* Figure 21.3: `fig213D`, with (21.4)–(21.5) in `fig213_maxflow_bounds` (here).
* The rate pair `(1, 1)` is not achievable for Figure 21.3: `fig213_not_isAchievable` (here). The
  book argues with codes that send one bit of each source once; here every achievable pair
  satisfies `2 ω₁ + ω₂ ≤ 2`, `fig213_converse`, by the counting bound `fig213_card_correct_le`
  and `card_le_sqrt_mul` (here).

### 21.3 A Network Code for Acyclic Networks
* The model: `MultiSourceProblem`, with `MultiSourceProblem.inCh`, `MultiSourceProblem.outCh`
  (`Network.MultiSource`).
* Definitions 21.1 and 21.2: `RateCode`, `IsAchievable` (`Network.NoiselessCode`), in the form of
  Lecture 16 of [elgamal2010].

### 21.4 The Achievable Information Rate Region
* Definition 21.3: `capacityRegion` (`Network.NoiselessCode`), the closure of the set of achievable
  rate tuples; the remark after it says that this set is closed.
* (21.27)–(21.31): `MultiSourceProblem.C₁`, …, `MultiSourceProblem.C₅`, with
  `MultiSourceProblem.projY` and `downClosure` for the projection and `Λ` (`Network.MultiSource`).
* Definition 21.4: `MultiSourceProblem.rPrime` (`Network.MultiSource`).

### 21.5 Explicit Inner and Outer Bounds
* (21.39): `MultiSourceProblem.rLP`, with the inclusion of the region of Definition 21.4 in it,
  `MultiSourceProblem.rPrime_subset_rLP`, and the remark that the LP bound is given by finitely
  many linear constraints, `MultiSourceProblem.rLP_eq` (`Network.MultiSource`).

## Not formalized

* Section 21.2, the multilevel diversity coding and satellite communication networks of
  Figures 21.5–21.7.
* Theorem 21.5, `R = R'`, with its converse in Section 21.6 (Lemmas 21.6 and 21.7) and its
  achievability in Section 21.7 (Lemmas 21.8–21.11). The converse needs Fano's inequality for every
  sink of a network code and a compactness argument, and the achievability a random code built
  from typical sequences of the auxiliary random variables. Hence the LP bound is not proved to be
  an outer bound on the achievable rate region either.
* Figures 21.2 and 21.4, the plots of the max-flow bounds.

## References

Numbers without a source refer to [yeung2008].

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 21
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-! ### 21.1 The Max-Flow Bounds -/

/-- **Figures 21.1(a) and 21.3.** The nodes `1, 2, 3, 4` of the book are `2, 3, 4, 5`. The sources
`X₁` and `X₂`, both generated at node `1`, are the messages of the dummy nodes `0` and `1`, which
reach node `1` by edges of capacity `2`. The edges `(1, 2)`, `(1, 3)`, `(2, 4)` and `(3, 4)` have
capacity `1`. -/
def twoLayerNet : NoiselessNetwork (Fin 6) where
  C := ![![0, 0, 2, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0]]
  nonneg j k := by fin_cases j <;> fin_cases k <;> norm_num
  acyclic j k := by fin_cases j <;> fin_cases k <;> simp

/-- The rates `ω₁` and `ω₂` of `X₁` and `X₂`; the other nodes have no message. -/
def twoRates (ω₁ ω₂ : ℝ) : Fin 6 → ℝ := ![ω₁, ω₂, 0, 0, 0, 0]

/-- **Figure 21.1.** `X₁` is multicast to nodes `2` and `4`, and `X₂` to nodes `3` and `4`. -/
def fig211D : Fin 6 → Finset (Fin 6) := ![{3, 5}, {4, 5}, ∅, ∅, ∅, ∅]

/-- **Figure 21.3.** `X₁` is multicast to nodes `2`, `3` and `4`, and `X₂` to node `4`. -/
def fig213D : Fin 6 → Finset (Fin 6) := ![{3, 4, 5}, {5}, ∅, ∅, ∅, ∅]

/-- The cutset bound for `twoLayerNet` and the cut `S`, in a form that `decide` can evaluate. -/
lemma twoLayerNet_cut {D : Fin 6 → Finset (Fin 6)} {ω₁ ω₂ : ℝ}
    (h : IsAchievable twoLayerNet D (twoRates ω₁ ω₂)) (S : Finset (Fin 6)) :
    ∑ j ∈ cutSources D S, twoRates ω₁ ω₂ j ≤ cutCap twoLayerNet.C S :=
  h.mem_cutsetRegion.2 S

/-- **(21.1)–(21.3).** The max-flow bounds of Figure 21.1, from the cutset bound at nodes `2`, `3`
and `4`. -/
theorem fig211_maxflow_bounds {ω₁ ω₂ : ℝ} (h : IsAchievable twoLayerNet fig211D (twoRates ω₁ ω₂)) :
    ω₁ ≤ 1 ∧ ω₂ ≤ 1 ∧ ω₁ + ω₂ ≤ 2 := by
  have h₁ := twoLayerNet_cut h {0, 1, 2, 4, 5}
  have h₂ := twoLayerNet_cut h {0, 1, 2, 3, 5}
  have h₃ := twoLayerNet_cut h {0, 1, 2, 3, 4}
  rw [show cutSources fig211D {0, 1, 2, 4, 5} = {0} by decide, cutCap,
    show ({0, 1, 2, 4, 5} : Finset (Fin 6))ᶜ = {3} by decide] at h₁
  rw [show cutSources fig211D {0, 1, 2, 3, 5} = {1} by decide, cutCap,
    show ({0, 1, 2, 3, 5} : Finset (Fin 6))ᶜ = {4} by decide] at h₂
  rw [show cutSources fig211D {0, 1, 2, 3, 4} = {0, 1} by decide, cutCap,
    show ({0, 1, 2, 3, 4} : Finset (Fin 6))ᶜ = {5} by decide] at h₃
  refine ⟨by simpa [twoRates, twoLayerNet] using h₁, by simpa [twoRates, twoLayerNet] using h₂, ?_⟩
  have : ω₁ + ω₂ ≤ 1 + 1 := by simpa [twoRates, twoLayerNet] using h₃
  linarith

/-- The bits of the message of node `j`. -/
def bitsOf {b : Fin 6 → ℕ} (j : Fin 6) : Finset (Σ j, Fin (b j)) := univ.filter (·.1 = j)

lemma mem_bitsOf {b : Fin 6 → ℕ} {j : Fin 6} {r : Σ j, Fin (b j)} : r ∈ bitsOf j ↔ r.1 = j := by
  simp [bitsOf]

lemma card_bitsOf {b : Fin 6 → ℕ} (j : Fin 6) : #(bitsOf (b := b) j) = b j := by
  rw [bitsOf, ← card_fin (b j)]
  refine card_bij (fun r hr => (mem_filter.1 hr).2 ▸ r.2) (fun _ _ => mem_univ _) ?_ ?_
  · rintro ⟨j₁, r₁⟩ h₁ ⟨j₂, r₂⟩ h₂ h
    obtain rfl := (mem_filter.1 h₁).2
    obtain rfl := (mem_filter.1 h₂).2
    simp_all
  · exact fun r _ => ⟨⟨j, r⟩, by simp⟩

/-- **Figure 21.1(b).** The routing scheme that sends `X₁` along `1 → 2 → 4` and `X₂` along
`1 → 3 → 4`. -/
def fig211Routing {ω₁ ω₂ : ℝ} (h₁ : ω₁ ≤ 1) (h₂ : ω₂ ≤ 1) (n : ℕ) :
    RoutingScheme (fun k l => ⌊(n : ℝ) * twoLayerNet.C k l⌋₊)
      (fun j => ⌈(n : ℝ) * twoRates ω₁ ω₂ j⌉₊) fig211D where
  carry k l :=
    if k = 0 ∧ l = 2 ∨ k = 2 ∧ l = 3 ∨ k = 3 ∧ l = 5 then bitsOf 0
    else if k = 1 ∧ l = 2 ∨ k = 2 ∧ l = 4 ∨ k = 4 ∧ l = 5 then bitsOf 1 else ∅
  card_le k l := by
    have hn := n.cast_nonneg (α := ℝ)
    have hr₁ : (n : ℝ) * ω₁ ≤ n := by nlinarith
    have hr₂ : (n : ℝ) * ω₂ ≤ n := by nlinarith
    have h2n : (n : ℝ) ≤ ⌊(n : ℝ) * 2⌋₊ := by
      exact_mod_cast Nat.le_floor (by push_cast; linarith)
    split_ifs with h0 h1
    · rw [card_bitsOf]
      fin_cases k <;> fin_cases l <;> simp [twoRates, twoLayerNet] at h0 ⊢ <;> linarith
    · rw [card_bitsOf]
      fin_cases k <;> fin_cases l <;> simp [twoRates, twoLayerNet] at h1 ⊢ <;> linarith
    · simp
  forward k l r hr := by
    by_cases hk : r.1 = k
    · exact Or.inl hk
    refine Or.inr ⟨if k = 2 then r.1 else 2, ?_, ?_⟩ <;>
      fin_cases k <;> fin_cases l <;> simp_all [mem_bitsOf]
  deliver r l hl := by
    refine ⟨if l = 5 then (if r.1 = 0 then 3 else 4) else 2, ?_, ?_⟩ <;>
      obtain ⟨j, i⟩ := r <;> fin_cases j <;> fin_cases l <;> simp_all [fig211D, mem_bitsOf]

/-- **Figure 21.1.** The rate pairs that satisfy the max-flow bounds (21.1)–(21.3) are achievable,
by routing, since they are inferior to `(1, 1)`. -/
theorem fig211_isAchievable_iff {ω₁ ω₂ : ℝ} :
    IsAchievable twoLayerNet fig211D (twoRates ω₁ ω₂) ↔ 0 ≤ ω₁ ∧ 0 ≤ ω₂ ∧ ω₁ ≤ 1 ∧ ω₂ ≤ 1 := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, -⟩ := fig211_maxflow_bounds h
    exact ⟨h.1 0, h.1 1, h₁, h₂⟩
  · rintro ⟨h₀₁, h₀₂, h₁, h₂⟩
    refine IsAchievableZE.isAchievable (IsRoutingAchievable.isAchievableZE ⟨fun j => ?_, ?_⟩)
    · fin_cases j <;> simp [twoRates, h₀₁, h₀₂]
    · exact Eventually.of_forall fun n => ⟨fig211Routing h₁ h₂ n⟩

/-- **(21.4)–(21.5).** The max-flow bounds of Figure 21.3, from the cutset bound at nodes `2` and
`4`. -/
theorem fig213_maxflow_bounds {ω₁ ω₂ : ℝ} (h : IsAchievable twoLayerNet fig213D (twoRates ω₁ ω₂)) :
    ω₁ ≤ 1 ∧ ω₁ + ω₂ ≤ 2 := by
  have h₁ := twoLayerNet_cut h {0, 1, 2, 4, 5}
  have h₃ := twoLayerNet_cut h {0, 1, 2, 3, 4}
  rw [show cutSources fig213D {0, 1, 2, 4, 5} = {0} by decide, cutCap,
    show ({0, 1, 2, 4, 5} : Finset (Fin 6))ᶜ = {3} by decide] at h₁
  rw [show cutSources fig213D {0, 1, 2, 3, 4} = {0, 1} by decide, cutCap,
    show ({0, 1, 2, 3, 4} : Finset (Fin 6))ᶜ = {5} by decide] at h₃
  refine ⟨by simpa [twoRates, twoLayerNet] using h₁, ?_⟩
  have : ω₁ + ω₂ ≤ 1 + 1 := by simpa [twoRates, twoLayerNet] using h₃
  linarith

/-- If `v` determines `x` on `C`, the images under `v` of the sets of elements of `C` with the same
value of `x` are disjoint. -/
lemma sum_card_image_le {α Y X : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq X] {C : Finset α}
    {x : α → X} (v : α → Y) (hv : ∀ a ∈ C, ∀ a' ∈ C, v a = v a' → x a = x a') :
    ∑ ξ ∈ C.image x, #({a ∈ C | x a = ξ}.image v) ≤ Fintype.card Y := by
  rw [← card_biUnion]
  · exact card_le_univ _
  · intro ξ _ ξ' _ hne
    refine disjoint_left.2 fun y hy hy' => hne ?_
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    obtain ⟨a', ha', hva⟩ := mem_image.1 hy'
    rw [← (mem_filter.1 ha).2, ← (mem_filter.1 ha').2]
    exact (hv a' (mem_filter.1 ha').1 a (mem_filter.1 ha).1 hva).symm

/-- The counting behind the converse for Figure 21.3. On a set `C` of messages, let `u` and `w`
together determine the message, and each of them determine its first part `x`, which leaves at most
`K` messages. Then `|C| ≤ √K (|U| + |W|) / 2`: the first parts split `U` and `W` into disjoint
pieces, and a first part with pieces of sizes `a` and `b` has at most `min(K, ab) ≤ √K (a + b) / 2`
messages. -/
lemma card_le_sqrt_mul {α U W X : Type*} [Fintype U] [Fintype W] [DecidableEq X] {C : Finset α}
    {x : α → X} {u : α → U} {w : α → W} {K : ℕ}
    (hinj : ∀ a ∈ C, ∀ a' ∈ C, u a = u a' → w a = w a' → a = a')
    (hu : ∀ a ∈ C, ∀ a' ∈ C, u a = u a' → x a = x a')
    (hw : ∀ a ∈ C, ∀ a' ∈ C, w a = w a' → x a = x a')
    (hK : ∀ ξ, #{a ∈ C | x a = ξ} ≤ K) :
    (#C : ℝ) ≤ √K * (Fintype.card U + Fintype.card W) / 2 := by
  classical
  -- one first part
  have hfib : ∀ ξ, (#{a ∈ C | x a = ξ} : ℝ) ≤
      √K * (#({a ∈ C | x a = ξ}.image u) + #({a ∈ C | x a = ξ}.image w)) / 2 := by
    intro ξ
    have h₁ : #{a ∈ C | x a = ξ} ≤
        #({a ∈ C | x a = ξ}.image u) * #({a ∈ C | x a = ξ}.image w) := by
      rw [← card_product]
      refine card_le_card_of_injOn (fun a => (u a, w a))
        (fun a ha => mem_product.2 ⟨mem_image_of_mem _ ha, mem_image_of_mem _ ha⟩) ?_
      intro a ha a' ha' h
      exact hinj a (mem_filter.1 ha).1 a' (mem_filter.1 ha').1 (congrArg Prod.fst h)
        (congrArg Prod.snd h)
    have hc : ((#{a ∈ C | x a = ξ} : ℕ) : ℝ) ≤ K := by exact_mod_cast hK ξ
    have hpq : ((#{a ∈ C | x a = ξ} : ℕ) : ℝ) ≤
        ((#({a ∈ C | x a = ξ}.image u) : ℕ) : ℝ) * ((#({a ∈ C | x a = ξ}.image w) : ℕ) : ℝ) := by
      exact_mod_cast h₁
    set c : ℝ := ((#{a ∈ C | x a = ξ} : ℕ) : ℝ)
    set p : ℝ := ((#({a ∈ C | x a = ξ}.image u) : ℕ) : ℝ)
    set q : ℝ := ((#({a ∈ C | x a = ξ}.image w) : ℕ) : ℝ)
    have hc0 : 0 ≤ c := by positivity
    have hc2 : c ^ 2 ≤ K * ((p + q) / 2) ^ 2 := by
      have : c * c ≤ K * (p * q) := mul_le_mul hc hpq hc0 (by positivity)
      nlinarith [sq_nonneg (p - q)]
    calc c = √(c ^ 2) := (Real.sqrt_sq hc0).symm
      _ ≤ √(K * ((p + q) / 2) ^ 2) := Real.sqrt_le_sqrt hc2
      _ = √K * ((p + q) / 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ = √K * (p + q) / 2 := by ring
  have hU := sum_card_image_le u hu
  have hW := sum_card_image_le w hw
  calc (#C : ℝ) = ∑ ξ ∈ C.image x, (#{a ∈ C | x a = ξ} : ℝ) := by
        rw [card_eq_sum_card_image x C]
        push_cast
        rfl
    _ ≤ ∑ ξ ∈ C.image x,
        √K * (#({a ∈ C | x a = ξ}.image u) + #({a ∈ C | x a = ξ}.image w)) / 2 :=
      sum_le_sum fun ξ _ => hfib ξ
    _ = √K * ((∑ ξ ∈ C.image x, (#({a ∈ C | x a = ξ}.image u) : ℝ)) +
        ∑ ξ ∈ C.image x, (#({a ∈ C | x a = ξ}.image w) : ℝ)) / 2 := by
      rw [← sum_div, ← mul_sum, sum_add_distrib]
    _ ≤ √K * (Fintype.card U + Fintype.card W) / 2 := by
      gcongr
      · exact_mod_cast hU
      · exact_mod_cast hW

/-- Messages of rate `0` have one value. -/
lemma msg_eq_of_rate_eq_zero {n : ℕ} {r : ℝ} (hr : r = 0) (a b : Fin (2 ^ ⌈(n : ℝ) * r⌉₊)) :
    a = b := by
  subst hr
  have : Subsingleton (Fin (2 ^ ⌈(n : ℝ) * 0⌉₊)) := by
    simp only [mul_zero, Nat.ceil_zero, pow_zero]
    infer_instance
  exact Subsingleton.elim a b

/-- Edges of capacity `0` carry one index. -/
lemma idx_eq_of_cap_eq_zero {n : ℕ} {C : ℝ} (hC : C = 0) (a b : Fin (2 ^ ⌊(n : ℝ) * C⌋₊)) :
    a = b := by
  subst hC
  have : Subsingleton (Fin (2 ^ ⌊(n : ℝ) * 0⌋₊)) := by
    simp only [mul_zero, Nat.floor_zero, pow_zero]
    infer_instance
  exact Subsingleton.elim a b

/-- The edges of `twoLayerNet` that leave `{0, 1, 2}` other than `(2, 3)` and `(2, 4)` have
capacity `0`. -/
lemma twoLayerNet_C_cut₅ {j k : Fin 6} (hj : j ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hk : k ∉ ({0, 1, 2} : Finset (Fin 6))) (h₃ : ¬(j = 2 ∧ k = 3)) (h₄ : ¬(j = 2 ∧ k = 4)) :
    twoLayerNet.C j k = 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [twoLayerNet]

/-- The edges of `twoLayerNet` into node `3` other than `(2, 3)` have capacity `0`. -/
lemma twoLayerNet_C_cut₃ {j k : Fin 6} (hj : j ∈ ({0, 1, 2, 4, 5} : Finset (Fin 6)))
    (hk : k ∉ ({0, 1, 2, 4, 5} : Finset (Fin 6))) (h₃ : ¬(j = 2 ∧ k = 3)) :
    twoLayerNet.C j k = 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [twoLayerNet]

/-- The edges of `twoLayerNet` into node `4` other than `(2, 4)` have capacity `0`. -/
lemma twoLayerNet_C_cut₄ {j k : Fin 6} (hj : j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 6)))
    (hk : k ∉ ({0, 1, 2, 3, 5} : Finset (Fin 6))) (h₄ : ¬(j = 2 ∧ k = 4)) :
    twoLayerNet.C j k = 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [twoLayerNet]

open Classical in
/-- A code on `twoLayerNet` with rates `(ω₁, ω₂)`, and its correctly decoded message tuples for the
demands of Figure 21.3, `|C| ≤ 2^{⌈n ω₂⌉ / 2} 2^n`. -/
lemma fig213_card_correct_le {ω₁ ω₂ : ℝ} {n : ℕ} (c : RateCode twoLayerNet (twoRates ω₁ ω₂) n) :
    (#{m | c.Correct fig213D m} : ℝ) ≤ √(2 ^ ⌈(n : ℝ) * ω₂⌉₊ : ℕ) * 2 ^ n := by
  classical
  -- the messages of the other nodes, and the indices on the edges of capacity `0`, are trivial
  have hmsg : ∀ (m m' : ∀ j, Fin (2 ^ ⌈(n : ℝ) * twoRates ω₁ ω₂ j⌉₊)) (j : Fin 6), j ≠ 0 →
      j ≠ 1 → m j = m' j := fun m m' j h₀ h₁ =>
    msg_eq_of_rate_eq_zero (by fin_cases j <;> simp_all [twoRates]) _ _
  have hidx : ∀ (m m' : ∀ j, Fin (2 ^ ⌈(n : ℝ) * twoRates ω₁ ω₂ j⌉₊)) (j k : Fin 6),
      twoLayerNet.C j k = 0 → c.edge m j k = c.edge m' j k := fun m m' j k h =>
    idx_eq_of_cap_eq_zero h _ _
  have hcard : ∀ k l : Fin 6, twoLayerNet.C k l = 1 →
      Fintype.card (Fin (2 ^ ⌊(n : ℝ) * twoLayerNet.C k l⌋₊)) = 2 ^ n := fun k l h => by
    simp [h]
  have key := card_le_sqrt_mul (C := {m | c.Correct fig213D m}) (x := fun m => m 0)
    (u := fun m => c.edge m 2 3) (w := fun m => c.edge m 2 4) (K := 2 ^ ⌈(n : ℝ) * ω₂⌉₊)
    ?_ ?_ ?_ ?_
  · rw [hcard 2 3 (by simp [twoLayerNet]), hcard 2 4 (by simp [twoLayerNet])] at key
    push_cast at key ⊢
    linarith
  · -- node `4` decodes both sources from the edges `(1, 2)` and `(1, 3)`
    intro m hm m' hm' hu hw
    simp only [mem_filter, mem_univ, true_and] at hm hm'
    have hout := fun j => c.out_congr (S := {0, 1, 2}) (m := m) (m' := m')
      (fun j hj => hmsg m m' j (by rintro rfl; simp at hj) (by rintro rfl; simp at hj))
      (fun j hj k hk => by
        by_cases h₃ : j = 2 ∧ k = 3
        · obtain ⟨rfl, rfl⟩ := h₃
          exact hu
        by_cases h₄ : j = 2 ∧ k = 4
        · obtain ⟨rfl, rfl⟩ := h₄
          exact hw
        exact hidx m m' j k (twoLayerNet_C_cut₅ hj hk h₃ h₄))
      (l := 5) (by decide) j
    funext j
    by_cases h₀ : j = 0
    · subst h₀
      rw [← hm 0 5 (by simp [fig213D]), ← hm' 0 5 (by simp [fig213D]), hout]
    by_cases h₁ : j = 1
    · subst h₁
      rw [← hm 1 5 (by simp [fig213D]), ← hm' 1 5 (by simp [fig213D]), hout]
    exact hmsg m m' j h₀ h₁
  · -- node `2` decodes `X₁` from the edge `(1, 2)`
    intro m hm m' hm' hu
    simp only [mem_filter, mem_univ, true_and] at hm hm'
    have hout := c.out_congr (S := {0, 1, 2, 4, 5}) (m := m) (m' := m')
      (fun j hj => hmsg m m' j (by rintro rfl; simp at hj) (by rintro rfl; simp at hj))
      (fun j hj k hk => by
        by_cases h₃ : j = 2 ∧ k = 3
        · obtain ⟨rfl, rfl⟩ := h₃
          exact hu
        exact hidx m m' j k (twoLayerNet_C_cut₃ hj hk h₃))
      (l := 3) (by decide) 0
    rw [← hm 0 3 (by simp [fig213D]), ← hm' 0 3 (by simp [fig213D]), hout]
  · -- node `3` decodes `X₁` from the edge `(1, 3)`
    intro m hm m' hm' hw
    simp only [mem_filter, mem_univ, true_and] at hm hm'
    have hout := c.out_congr (S := {0, 1, 2, 3, 5}) (m := m) (m' := m')
      (fun j hj => hmsg m m' j (by rintro rfl; simp at hj) (by rintro rfl; simp at hj))
      (fun j hj k hk => by
        by_cases h₄ : j = 2 ∧ k = 4
        · obtain ⟨rfl, rfl⟩ := h₄
          exact hw
        exact hidx m m' j k (twoLayerNet_C_cut₄ hj hk h₄))
      (l := 4) (by decide) 0
    rw [← hm 0 4 (by simp [fig213D]), ← hm' 0 4 (by simp [fig213D]), hout]
  · -- given `X₁`, the tuple is determined by `X₂`
    intro ξ
    calc #{m ∈ ({m | c.Correct fig213D m} : Finset _) | m 0 = ξ}
        ≤ #(univ : Finset (Fin (2 ^ ⌈(n : ℝ) * twoRates ω₁ ω₂ 1⌉₊))) := by
          refine card_le_card_of_injOn (fun m => m 1) (fun _ _ => mem_univ _) ?_
          intro m hm m' hm' h
          simp only [coe_filter, mem_filter, mem_univ, true_and] at hm hm'
          funext j
          by_cases h₀ : j = 0
          · subst h₀
            rw [hm.2, hm'.2]
          by_cases h₁ : j = 1
          · subst h₁
            exact h
          exact hmsg m m' j h₀ h₁
      _ = 2 ^ ⌈(n : ℝ) * ω₂⌉₊ := by
        rw [card_univ, Fintype.card_fin]
        simp [twoRates]

/-- **Figure 21.3.** Every achievable rate pair satisfies `2 ω₁ + ω₂ ≤ 2`, a strong converse: by
`fig213_card_correct_le`, the probability of correct decoding is at most `2^{n (1 - ω₁ - ω₂ / 2)}`.
Sending `X₁` on both edges out of node `1` and splitting `X₂` between them meets this bound, which
shows that source separation is optimal, the exercise of the book; that direction is not
formalized. -/
theorem fig213_converse {ω₁ ω₂ : ℝ} (h : IsAchievable twoLayerNet fig213D (twoRates ω₁ ω₂)) :
    2 * ω₁ + ω₂ ≤ 2 := by
  classical
  obtain ⟨-, c, hc⟩ := h
  suffices ω₁ + ω₂ / 2 ≤ 1 by linarith
  refine le_of_tendsto_one_sub_mul_rpow hc fun n => ?_
  have hcard : (Fintype.card (∀ j, Fin (2 ^ ⌈(n : ℝ) * twoRates ω₁ ω₂ j⌉₊)) : ℝ) =
      2 ^ ⌈(n : ℝ) * ω₁⌉₊ * 2 ^ ⌈(n : ℝ) * ω₂⌉₊ := by
    rw [Fintype.card_eq_nat_card, Nat.card_pi, Fin.prod_univ_six]
    simp [twoRates]
  have hC := fig213_card_correct_le (c n)
  push_cast at hC
  rw [(c n).one_sub_errProb fig213D, hcard]
  have hA : (2 : ℝ) ^ ((n : ℝ) * ω₁) ≤ 2 ^ ⌈(n : ℝ) * ω₁⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have hK : (2 : ℝ) ^ ((n : ℝ) * ω₂ / 2) ≤ √(2 ^ ⌈(n : ℝ) * ω₂⌉₊) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have := Nat.le_ceil ((n : ℝ) * ω₂)
    linarith
  set A : ℝ := 2 ^ ⌈(n : ℝ) * ω₁⌉₊
  set K : ℝ := 2 ^ ⌈(n : ℝ) * ω₂⌉₊
  have hE : (2 : ℝ) ^ ((n : ℝ) * (ω₁ + ω₂ / 2)) ≤ A * √K := by
    rw [show (n : ℝ) * (ω₁ + ω₂ / 2) = n * ω₁ + n * ω₂ / 2 by ring,
      Real.rpow_add (by norm_num)]
    exact mul_le_mul hA hK (by positivity) (by positivity)
  have hKK : √K * √K = K := Real.mul_self_sqrt (by positivity)
  calc (#{m | (c n).Correct fig213D m} : ℝ) / (A * K) * (2 : ℝ) ^ ((n : ℝ) * (ω₁ + ω₂ / 2))
      ≤ (#{m | (c n).Correct fig213D m} : ℝ) / (A * K) * (A * √K) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 2 ^ n := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc (#{m | (c n).Correct fig213D m} : ℝ) * (A * √K) ≤ (√K * 2 ^ n) * (A * √K) :=
            mul_le_mul_of_nonneg_right hC (by positivity)
        _ = 2 ^ n * (A * K) := by linear_combination (2 ^ n * A) * hKK
    _ = (2 : ℝ) ^ ((n : ℝ) * 1) := by rw [mul_one, Real.rpow_natCast]

/-- **Figure 21.3.** The rate pair `(1, 1)` satisfies the max-flow bounds (21.4) and (21.5) but is
not achievable. -/
theorem fig213_not_isAchievable : ¬ IsAchievable twoLayerNet fig213D (twoRates 1 1) := by
  intro h
  have := fig213_converse h
  norm_num at this

end InfoTheory.Yeung
