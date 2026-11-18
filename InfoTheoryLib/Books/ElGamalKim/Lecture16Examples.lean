/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NetworkCoding

/-!
# Lecture 16: examples of noiseless networks

## Main statements

* `example_capacity`: the network of page 16-6 has capacity `3`.
* `printed_dual_ge_four`: the dual problem printed on page 16-8 has value at least `4` on it.
* `butterfly_capacity`, `butterfly_isAchievableZE`: the butterfly network has capacity `2`, achieved
  with zero error by the XOR of two bitstreams.
* `butterfly_routing_split`: with the splitting of the source of page 16-13, routing has `R ≤ 1`.
* `butterfly_routing_le`, `butterfly_routing_of_lt`: if the source may also send copies then the
  rate of routing is exactly `3/2`.
* `unicast_iff`, `unicast_routing_le`, `printed_unicast_routing`: the variant of the butterfly
  network of page 16-26.
* `km_transfer`, `km_det`: the linear code of page 16-18 and its determinant.
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ### Networks with integer capacities -/

/-- The network with integer capacities `w`. -/
def natNet {V : Type*} [LT V] (w : V → V → ℕ) (h : ∀ j k, 0 < w j k → j < k) :
    NoiselessNetwork V :=
  ⟨fun j k => w j k, fun _ _ => Nat.cast_nonneg _, fun j k hjk => h j k (by exact_mod_cast hjk)⟩

lemma cutCap_natCast {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℕ) (S : Finset V) :
    cutCap (fun j k => (w j k : ℝ)) S = ((∑ j ∈ S, ∑ k ∈ Sᶜ, w j k : ℕ) : ℝ) := by
  simp [cutCap]

/-- A flow with values in the natural numbers. -/
lemma isFlow_nat {V : Type*} [Fintype V] {w f : V → V → ℕ} {s t : V} {v : ℕ}
    (hle : ∀ j k, f j k ≤ w j k)
    (hcons : ∀ k, k ≠ s → k ≠ t → ∑ l, f k l = ∑ j, f j k)
    (hval : ∑ l, f s l = v + ∑ j, f j s) :
    IsFlow (fun j k => (w j k : ℝ)) s t (fun j k => (f j k : ℝ)) v := by
  refine ⟨fun _ _ => Nat.cast_nonneg _, fun j k => by exact_mod_cast hle j k, fun k hs ht => ?_, ?_⟩
  · simp only [netOut]
    rw [sub_eq_zero]
    exact_mod_cast hcons k hs ht
  · simp only [netOut]
    have : ((∑ l, f s l : ℕ) : ℝ) = ((v + ∑ j, f j s : ℕ) : ℝ) := by rw [hval]
    push_cast at this
    linarith

/-! ### The network of page 16-6 -/

/-- **Page 16-6 of [elgamal2010].** The capacities of the example, with nodes numbered from `0`. -/
def exampleW : Fin 6 → Fin 6 → ℕ :=
  ![![0, 2, 2, 0, 0, 0],
    ![0, 0, 1, 1, 2, 0],
    ![0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 1, 2],
    ![0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0]]

/-- The network of page 16-6. -/
def exampleNet : NoiselessNetwork (Fin 6) := natNet exampleW (by decide)

/-- The flow of page 16-6: one bit along `1 → 2 → 4 → 6` and two bits along `1 → 3 → 5 → 6`. -/
def exampleFlow : Fin 6 → Fin 6 → ℕ :=
  ![![0, 1, 2, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0]]

lemma example_minCut : minCut exampleNet.C 0 5 = 3 := by
  have hflow : IsFlow (fun j k => (exampleW j k : ℝ)) 0 5 (fun j k => (exampleFlow j k : ℝ))
      (3 : ℕ) :=
    isFlow_nat (by decide) (by decide) (by decide)
  refine le_antisymm ?_ (le_minCut _ (by decide) fun S hs ht => ?_)
  · have h := minCut_le exampleNet.C (S := {0, 1, 2, 4}) (s := 0) (t := 5) (by decide) (by decide)
    have hval : cutCap exampleNet.C {0, 1, 2, 4} = 3 := by
      change cutCap (fun j k => (exampleW j k : ℝ)) _ = 3
      rw [cutCap_natCast]
      have : (∑ j ∈ ({0, 1, 2, 4} : Finset (Fin 6)), ∑ k ∈ ({0, 1, 2, 4} : Finset (Fin 6))ᶜ,
          exampleW j k) = 3 := by decide
      rw [this]
      norm_num
    linarith
  · have h := hflow.le_cutCap hs ht
    have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3] at h
    exact h

/-- **Page 16-6 of [elgamal2010].** The network of the example has capacity `3`. -/
theorem example_capacity : multicastCapacity exampleNet 0 {5} = 3 := by
  rw [relay_capacity _ (by decide), example_minCut]

/-- **The dual problem as printed on page 16-8 of [elgamal2010] is not the dual of the flow
problem.** With the constraints `νⱼ - νₖ = λⱼₖ ≥ 0` printed there, every feasible point of the
network of page 16-6 has value at least `4`, while the capacity is `3`. The minimum cut
`{1, 2, 3, 5}` is not feasible because the edge `(4, 5)` goes back across it. The dual of the flow
problem has `νⱼ - νₖ ≤ λⱼₖ`. -/
theorem printed_dual_ge_four {ν : Fin 6 → ℝ} (hν : ∀ j k, 0 < exampleW j k → 0 ≤ ν j - ν k)
    (h1 : ν 0 - ν 5 = 1) : 4 ≤ ∑ j, ∑ k, (exampleW j k : ℝ) * (ν j - ν k) := by
  have h₁ := hν 3 4 (by decide)
  have h₂ := hν 1 2 (by decide)
  have h₃ := hν 1 3 (by decide)
  have h₄ := hν 2 4 (by decide)
  have h₅ := hν 3 5 (by decide)
  have h₆ := hν 4 5 (by decide)
  have h₇ := hν 0 1 (by decide)
  have h₈ := hν 0 2 (by decide)
  have h₉ := hν 1 4 (by decide)
  have hval : ∑ j, ∑ k, (exampleW j k : ℝ) * (ν j - ν k) =
      2 * (ν 0 - ν 1) + 2 * (ν 0 - ν 2) + (ν 1 - ν 2) + (ν 1 - ν 3) + 2 * (ν 1 - ν 4) +
        2 * (ν 2 - ν 4) + (ν 3 - ν 4) + 2 * (ν 3 - ν 5) + 2 * (ν 4 - ν 5) := by
    simp only [Fin.sum_univ_six, exampleW]
    simp
    ring
  rw [hval]
  linarith

/-! ### Codes over bitstreams -/

section FunCode

variable {V Ω M : Type*} [LinearOrder V] [Fintype V] [Zero Ω]

/-- A code with one alphabet: an encoder reads the symbols received from all lower nodes, and sees
`0` from the other nodes. -/
def funCode (f : V → V → (V → Ω) → M → Ω) (g : V → V → (V → Ω) → M) :
    NetCode V (fun _ _ => Ω) (fun _ => M) where
  enc k l u m := f k l (fun j => if h : j < k then u j h else 0) m
  dec l j u := g l j fun k => if h : k < l then u k h else 0

omit [Fintype V] in
lemma funCode_edge [Finite V] (f : V → V → (V → Ω) → M → Ω) (g : V → V → (V → Ω) → M) (m : V → M)
    (k l : V) : (funCode f g).edge m k l = f k l
    (fun j => if j < k then (funCode f g).edge m j k else 0) (m k) := by
  rw [NetCode.edge_eq]
  simp only [funCode, dite_eq_ite]

omit [Fintype V] in
lemma funCode_out [Finite V] (f : V → V → (V → Ω) → M → Ω) (g : V → V → (V → Ω) → M) (m : V → M)
    (l j : V) : (funCode f g).out m l j = g l j fun k => if k < l then (funCode f g).edge m k l
    else 0 := by
  simp only [NetCode.out, funCode, dite_eq_ite]

end FunCode

/-- An `n`-bit stream. -/
abbrev Bitstream (n : ℕ) := Fin n → ZMod 2

lemma stream_add_add (n : ℕ) (a b : Bitstream n) : a + (a + b) = b := by
  funext i
  have : ∀ x y : ZMod 2, x + (x + y) = y := by decide
  exact this _ _

/-- A code over `n`-bit streams on a network of unit capacities is a `(2^{nR}, n)` code, if it sends
`0` on the pairs that are not edges and there are enough messages. -/
lemma exists_rateCode_unit {V : Type*} [LinearOrder V] [Finite V] {w : V → V → ℕ}
    (hw : ∀ j k, 0 < w j k → j < k) (hw₁ : ∀ j k, w j k ≤ 1) {R : V → ℝ} {n : ℕ} {M : Type*}
    [Fintype M] [Nonempty M] {D : V → Finset V}
    (c : NetCode V (fun _ _ => Bitstream n) (fun _ => M)) (hc : ∀ m, c.Correct D m)
    (hz : ∀ m k l, w k l = 0 → c.edge m k l = 0)
    (hM : ∀ j, 2 ^ ⌈(n : ℝ) * R j⌉₊ ≤ Fintype.card M) :
    ∃ c' : RateCode (natNet w hw) R n, ∀ m, c'.Correct D m := by
  have hμ : ∀ j, Nonempty (Fin (2 ^ ⌈(n : ℝ) * R j⌉₊) ↪ M) := fun j =>
    Function.Embedding.nonempty_of_card_le (by simpa using hM j)
  have hι : ∀ k l, ∃ ι : Bitstream n → Fin (2 ^ ⌊(n : ℝ) * (natNet w hw).C k l⌋₊),
      Set.InjOn ι (Set.range fun m : V → M => c.edge m k l) := by
    intro k l
    have hcase : w k l = 0 ∨ w k l = 1 := by have := hw₁ k l; omega
    rcases hcase with h | h
    · refine ⟨fun _ => ⟨0, by positivity⟩, ?_⟩
      rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩ _
      exact (hz m k l h).trans (hz m' k l h).symm
    · have hcard : ⌊(n : ℝ) * (natNet w hw).C k l⌋₊ = n := by
        simp [natNet, h]
      have hemb : Nonempty (Bitstream n ↪ Fin (2 ^ ⌊(n : ℝ) * (natNet w hw).C k l⌋₊)) := by
        refine Function.Embedding.nonempty_of_card_le ?_
        rw [hcard]
        simp [ZMod.card]
      exact ⟨hemb.some, hemb.some.injective.injOn⟩
  choose ι hι using hι
  exact c.exists_relabel hc (fun j => (hμ j).some) (fun j => (hμ j).some.injective) ι hι

/-! ### The butterfly network -/

/-- **Page 16-13 of [elgamal2010].** The butterfly network, with nodes numbered from `0`. -/
def butterflyW : Fin 7 → Fin 7 → ℕ :=
  ![![0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]

/-- The butterfly network. -/
def butterflyNet : NoiselessNetwork (Fin 7) := natNet butterflyW (by decide)

/-- **Page 16-14 of [elgamal2010].** The code of the butterfly network: node `4` sends the XOR of
its two incoming bitstreams, and the others forward. -/
def butterflyCode (n : ℕ) :
    NetCode (Fin 7) (fun _ _ => Bitstream n) (fun _ => Bitstream n × Bitstream n) :=
  funCode
    (fun k l u m => if butterflyW k l = 0 then 0 else
      if k = 0 then (if l = 1 then m.1 else m.2)
      else if k = 3 then u 1 + u 2
      else if k = 4 then u 3
      else u 0)
    (fun l _ u => if l = 5 then (u 1, u 1 + u 4) else (u 2 + u 4, u 2))

lemma butterflyCode_correct (n : ℕ) (m : Fin 7 → Bitstream n × Bitstream n) :
    (butterflyCode n).Correct (multicastD 0 {5, 6}) m := by
  have e01 : (butterflyCode n).edge m 0 1 = (m 0).1 := by
    rw [butterflyCode, funCode_edge]
    simp [butterflyW]
  have e02 : (butterflyCode n).edge m 0 2 = (m 0).2 := by
    rw [butterflyCode, funCode_edge]
    simp [butterflyW]
  have e13 : (butterflyCode n).edge m 1 3 = (m 0).1 := by
    rw [← e01, butterflyCode, funCode_edge]
    simp [butterflyW]
  have e15 : (butterflyCode n).edge m 1 5 = (m 0).1 := by
    rw [← e01, butterflyCode, funCode_edge]
    simp [butterflyW]
  have e23 : (butterflyCode n).edge m 2 3 = (m 0).2 := by
    rw [← e02, butterflyCode, funCode_edge]
    simp [butterflyW]
  have e26 : (butterflyCode n).edge m 2 6 = (m 0).2 := by
    rw [← e02, butterflyCode, funCode_edge]
    simp [butterflyW]
  have e34 : (butterflyCode n).edge m 3 4 = (m 0).1 + (m 0).2 := by
    rw [← e13, ← e23, butterflyCode, funCode_edge]
    simp [butterflyW]
  have e45 : (butterflyCode n).edge m 4 5 = (m 0).1 + (m 0).2 := by
    rw [← e34, butterflyCode, funCode_edge]
    simp [butterflyW]
  have e46 : (butterflyCode n).edge m 4 6 = (m 0).1 + (m 0).2 := by
    rw [← e34, butterflyCode, funCode_edge]
    simp [butterflyW]
  intro j l hl
  by_cases hj : j = 0
  · subst hj
    have hl' : l = 5 ∨ l = 6 := by simpa [multicastD] using hl
    rw [butterflyCode, funCode_out, ← butterflyCode]
    rcases hl' with rfl | rfl
    · simp [e15, e45, stream_add_add]
    · simp only [show ¬ (6 : Fin 7) = 5 by decide, ite_false,
        show (2 : Fin 7) < 6 by decide, show (4 : Fin 7) < 6 by decide, ite_true, e26, e46]
      rw [add_comm (m 0).1, stream_add_add]
  · simp [multicastD, hj] at hl

/-- **Page 16-14 of [elgamal2010].** The XOR code achieves every rate up to the cutset bound `2`,
with zero error and for all block lengths. -/
theorem butterfly_isAchievableZE {R : ℝ} (h0 : 0 ≤ R) (h2 : R ≤ 2) :
    IsAchievableZE butterflyNet (multicastD 0 {5, 6}) (singleRate 0 R) := by
  refine ⟨fun j => ?_, Eventually.of_forall fun n => ?_⟩
  · simp only [singleRate]
    split_ifs <;> simp [h0]
  refine exists_rateCode_unit _ (by decide) (butterflyCode n) (butterflyCode_correct n)
    (fun m k l hkl => ?_) fun j => ?_
  · rw [butterflyCode, funCode_edge]
    simp [hkl]
  · have hcard : Fintype.card (Bitstream n × Bitstream n) = 2 ^ (2 * n) := by
      simp [ZMod.card, two_mul, pow_add]
    rw [hcard]
    refine Nat.pow_le_pow_right (by norm_num) (Nat.ceil_le.mpr ?_)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    simp only [singleRate]
    split_ifs
    · nlinarith
    · simp only [mul_zero]
      positivity

lemma butterfly_minCut_le (t : Fin 7) (ht : t = 5 ∨ t = 6) : minCut butterflyNet.C 0 t ≤ 2 := by
  have hcut : ∀ t : Fin 7, t = 5 ∨ t = 6 → (0 : Fin 7) ∈ ({t}ᶜ : Finset (Fin 7)) ∧
      t ∉ ({t}ᶜ : Finset (Fin 7)) ∧
      ∑ j ∈ ({t}ᶜ : Finset (Fin 7)), ∑ k ∈ ({t}ᶜ : Finset (Fin 7))ᶜ, butterflyW j k = 2 := by
    decide
  obtain ⟨h₁, h₂, h₃⟩ := hcut t ht
  have h := minCut_le butterflyNet.C h₁ h₂
  have hval : cutCap butterflyNet.C {t}ᶜ = 2 := by
    change cutCap (fun j k => (butterflyW j k : ℝ)) _ = 2
    rw [cutCap_natCast, h₃]
    norm_num
  linarith

/-- **Page 16-13 of [elgamal2010].** The cutset upper bound `C ≤ 2`. -/
theorem butterfly_le_two {R : ℝ}
    (h : IsAchievable butterflyNet (multicastD 0 {5, 6}) (singleRate 0 R)) : R ≤ 2 :=
  (h.le_minCut (t := 5) (by simp) (by decide)).trans (butterfly_minCut_le 5 (Or.inl rfl))

/-- **Page 16-14 of [elgamal2010].** The capacity of the butterfly network is `2`. -/
theorem butterfly_capacity : multicastCapacity butterflyNet 0 {5, 6} = 2 :=
  multicastCapacity_eq (fun _ h0 h2 => (butterfly_isAchievableZE h0 h2.le).isAchievable)
    fun _ h => butterfly_le_two h

/-! ### Routing on the butterfly network -/

section ButterflyRouting

variable {cap : Fin 7 → Fin 7 → ℕ} {b : Fin 7 → ℕ} {n : ℕ}

/-- The sets of bits on the edges of the butterfly network. All the bits of a routing scheme reach
destination `5` either on the edge from node `1` or through `(3, 4)`, and similarly for `6`. -/
private lemma butterfly_bits (S : RoutingScheme cap b (multicastD 0 {5, 6}))
    (hz : ∀ j k, butterflyW j k = 0 → cap j k = 0) (hb : ∀ j, j ≠ 0 → b j = 0)
    (r : Σ j, Fin (b j)) :
    (r ∈ S.carry 0 1 ∨ r ∈ S.carry 3 4) ∧ (r ∈ S.carry 0 2 ∨ r ∈ S.carry 3 4) ∧
      (r ∈ S.carry 3 4 → r ∈ S.carry 0 1 ∨ r ∈ S.carry 0 2) := by
  have hr0 : r.1 = 0 := by
    by_contra h
    have hi := r.2.2
    have := hb r.1 h
    omega
  have hempty : ∀ j k, butterflyW j k = 0 → r ∉ S.carry j k := by
    intro j k hjk hr
    have := S.card_le j k
    rw [hz j k hjk] at this
    exact absurd hr (by simp [Finset.card_eq_zero.mp (Nat.le_zero.mp this)])
  -- going back along an edge
  have hback : ∀ k l, k ≠ 0 → r ∈ S.carry k l → ∀ P : Fin 7 → Prop,
      (∀ j, butterflyW j k ≠ 0 → P j) → ∃ j, P j ∧ r ∈ S.carry j k := by
    intro k l hk hr P hP
    rcases S.forward k l r hr with h | ⟨j, -, hj⟩
    · exact absurd (hr0.symm.trans h) (Ne.symm hk)
    · refine ⟨j, hP j fun hne => ?_, hj⟩
      exact hempty j k hne hj
  have h₁ : ∀ l, r ∈ S.carry 1 l → r ∈ S.carry 0 1 := by
    intro l hr
    obtain ⟨j, rfl, hj⟩ := hback 1 l (by decide) hr (· = 0) (by decide)
    exact hj
  have h₂ : ∀ l, r ∈ S.carry 2 l → r ∈ S.carry 0 2 := by
    intro l hr
    obtain ⟨j, rfl, hj⟩ := hback 2 l (by decide) hr (· = 0) (by decide)
    exact hj
  have h₃ : ∀ l, r ∈ S.carry 3 l → r ∈ S.carry 1 3 ∨ r ∈ S.carry 2 3 := by
    intro l hr
    obtain ⟨j, hP, hj⟩ := hback 3 l (by decide) hr (fun j => j = 1 ∨ j = 2) (by decide)
    rcases hP with rfl | rfl
    · exact Or.inl hj
    · exact Or.inr hj
  have h₄ : ∀ l, r ∈ S.carry 4 l → r ∈ S.carry 3 4 := by
    intro l hr
    obtain ⟨j, rfl, hj⟩ := hback 4 l (by decide) hr (· = 3) (by decide)
    exact hj
  have h₅ : r ∈ S.carry 0 1 ∨ r ∈ S.carry 3 4 := by
    obtain ⟨i, -, hi⟩ := S.deliver r 5 (by simp [multicastD, hr0])
    have hi' : i = 1 ∨ i = 4 := by
      by_contra hne
      have hall : ∀ i : Fin 7, ¬ (i = 1 ∨ i = 4) → butterflyW i 5 = 0 := by decide
      exact hempty i 5 (hall i hne) hi
    rcases hi' with rfl | rfl
    · exact Or.inl (h₁ 5 hi)
    · exact Or.inr (h₄ 5 hi)
  have h₆ : r ∈ S.carry 0 2 ∨ r ∈ S.carry 3 4 := by
    obtain ⟨i, -, hi⟩ := S.deliver r 6 (by simp [multicastD, hr0])
    have hi' : i = 2 ∨ i = 4 := by
      by_contra hne
      have hall : ∀ i : Fin 7, ¬ (i = 2 ∨ i = 4) → butterflyW i 6 = 0 := by decide
      exact hempty i 6 (hall i hne) hi
    rcases hi' with rfl | rfl
    · exact Or.inl (h₂ 6 hi)
    · exact Or.inr (h₄ 6 hi)
  refine ⟨h₅, h₆, fun hr => ?_⟩
  rcases h₃ 4 hr with h | h
  · exact Or.inl (h₁ 3 h)
  · exact Or.inr (h₂ 3 h)

/-- **Page 16-13 of [elgamal2010].** If the source splits its message, so that the edges out of it
carry different bits, then every bit goes through the bottleneck `(3, 4)`: `R₁ + R₂ ≤ 1`, even when
relay nodes forward copies. -/
theorem butterfly_routing_split (S : RoutingScheme cap b (multicastD 0 {5, 6}))
    (hz : ∀ j k, butterflyW j k = 0 → cap j k = 0) (hb : ∀ j, j ≠ 0 → b j = 0)
    (hcap : cap 3 4 ≤ n) (hsplit : Disjoint (S.carry 0 1) (S.carry 0 2)) : b 0 ≤ n := by
  have hsub : (ownBits b 0) ⊆ S.carry 3 4 := by
    intro r _
    obtain ⟨h₁, h₂, -⟩ := butterfly_bits S hz hb r
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact absurd h₂ (Finset.disjoint_left.mp hsplit h₁)
      · exact h₂
    · exact h₁
  have := Finset.card_le_card hsub
  rw [card_ownBits] at this
  exact this.trans ((S.card_le 3 4).trans hcap)

/-- If the source may send a bit on both of its edges then routing is limited by `2 b ≤ 3 n`, which
is more than the rate `1` of `butterfly_routing_split`. -/
theorem butterfly_routing_le (S : RoutingScheme cap b (multicastD 0 {5, 6}))
    (hz : ∀ j k, butterflyW j k = 0 → cap j k = 0) (hb : ∀ j, j ≠ 0 → b j = 0)
    (hcap : ∀ j k, cap j k ≤ n) : 2 * b 0 ≤ 3 * n := by
  classical
  have hU : ownBits b 0 ⊆ (S.carry 0 1 ∩ S.carry 0 2) ∪ S.carry 3 4 := by
    intro r _
    obtain ⟨h₁, h₂, -⟩ := butterfly_bits S hz hb r
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have hV : ownBits b 0 ⊆ S.carry 0 1 ∪ S.carry 0 2 := by
    intro r _
    obtain ⟨h₁, -, h₃⟩ := butterfly_bits S hz hb r
    simp only [Finset.mem_union]
    tauto
  have h₁ := (Finset.card_le_card hU).trans (Finset.card_union_le _ _)
  have h₂ := Finset.card_le_card hV
  have h₃ := Finset.card_union_add_card_inter (S.carry 0 1) (S.carry 0 2)
  rw [card_ownBits] at h₁ h₂
  have h₄ := (S.card_le 0 1).trans (hcap 0 1)
  have h₅ := (S.card_le 0 2).trans (hcap 0 2)
  have h₆ := (S.card_le 3 4).trans (hcap 3 4)
  omega

/-- The index sets of the routing scheme with three groups of bits: the first `q`, the next `q` and
the last `q`. -/
def butterflyBits (q : ℕ) (k l : Fin 7) (i : ℕ) : Prop :=
  if k = 0 then (if l = 1 then i < 2 * q else q ≤ i)
  else if k = 1 then (if l = 3 then i < q else i < 2 * q)
  else if k = 2 then (if l = 3 then 2 * q ≤ i else q ≤ i)
  else i < q ∨ 2 * q ≤ i

instance (q : ℕ) (k l : Fin 7) (i : ℕ) : Decidable (butterflyBits q k l i) := by
  unfold butterflyBits
  infer_instance

/-- Each edge of the routing scheme carries at most `2 q` of the indices below `3 q`. -/
lemma exists_butterflyBits_index (q : ℕ) (k l : Fin 7) :
    ∃ I : Finset ℕ, #I ≤ 2 * q ∧ ∀ i < 3 * q, butterflyBits q k l i → i ∈ I := by
  have h₁ : ∃ I : Finset ℕ, #I ≤ 2 * q ∧ ∀ i < 3 * q, i < 2 * q → i ∈ I :=
    ⟨Finset.range (2 * q), by simp, fun i _ h => Finset.mem_range.mpr h⟩
  have h₂ : ∃ I : Finset ℕ, #I ≤ 2 * q ∧ ∀ i < 3 * q, q ≤ i → i ∈ I :=
    ⟨Finset.Ico q (3 * q), by simp; omega, fun i h h' => Finset.mem_Ico.mpr ⟨h', h⟩⟩
  have h₃ : ∃ I : Finset ℕ, #I ≤ 2 * q ∧ ∀ i < 3 * q, i < q ∨ 2 * q ≤ i → i ∈ I := by
    refine ⟨Finset.range q ∪ Finset.Ico (2 * q) (3 * q), ?_, fun i h h' => ?_⟩
    · refine (Finset.card_union_le _ _).trans ?_
      simp
      omega
    · rcases h' with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h')
      · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h', h⟩)
  unfold butterflyBits
  obtain ⟨I₁, hI₁, hi₁⟩ := h₁
  obtain ⟨I₂, hI₂, hi₂⟩ := h₂
  obtain ⟨I₃, hI₃, hi₃⟩ := h₃
  split_ifs
  · exact ⟨I₁, hI₁, hi₁⟩
  · exact ⟨I₂, hI₂, hi₂⟩
  · exact ⟨I₁, hI₁, fun i h h' => hi₁ i h (by omega)⟩
  · exact ⟨I₁, hI₁, hi₁⟩
  · exact ⟨I₂, hI₂, fun i h h' => hi₂ i h (by omega)⟩
  · exact ⟨I₂, hI₂, hi₂⟩
  · exact ⟨I₃, hI₃, hi₃⟩

/-- A routing scheme of rate `3/2`: the source sends the middle group of bits on both of its edges.
-/
def butterflyScheme {b : Fin 7 → ℕ} {n q : ℕ} (hb : ∀ j, j ≠ 0 → b j = 0) (hq : 2 * q ≤ n)
    (hv : b 0 ≤ 3 * q) :
    RoutingScheme (fun k l => butterflyW k l * n) b (multicastD 0 {5, 6}) where
  carry k l := Finset.univ.filter fun r => butterflyW k l ≠ 0 ∧ butterflyBits q k l r.2.val
  card_le k l := by
    have hr0 : ∀ r : Σ j, Fin (b j), r.1 = 0 := by
      intro r
      by_contra h
      have hi := r.2.2
      have := hb r.1 h
      omega
    by_cases hkl : butterflyW k l = 0
    · simp [hkl]
    · obtain ⟨I, hI₁, hI₂⟩ := exists_butterflyBits_index q k l
      have hw : 1 ≤ butterflyW k l := Nat.one_le_iff_ne_zero.mpr hkl
      have hle : #(Finset.univ.filter fun r : Σ j, Fin (b j) =>
          butterflyW k l ≠ 0 ∧ butterflyBits q k l r.2.val) ≤ #I := by
        refine Finset.card_le_card_of_injOn (fun r => r.2.val) (fun r hr => ?_) ?_
        · have hr' := (Finset.mem_filter.mp hr).2.2
          have hlt : r.2.val < 3 * q := by
            have hi := r.2.2
            have hb0 : b r.1 = b 0 := by rw [hr0 r]
            omega
          exact hI₂ _ hlt hr'
        · rintro ⟨j, i⟩ _ ⟨j', i'⟩ _ h
          have hj : j = 0 := hr0 ⟨j, i⟩
          have hj' : j' = 0 := hr0 ⟨j', i'⟩
          subst hj hj'
          simp only at h
          rw [Fin.val_inj.mp h]
      calc _ ≤ #I := hle
        _ ≤ 2 * q := hI₁
        _ ≤ n := hq
        _ ≤ butterflyW k l * n := Nat.le_mul_of_pos_left _ hw
  forward k l r hr := by
    obtain ⟨hw, hp⟩ := (Finset.mem_filter.mp hr).2
    have hr0 : r.1 = 0 := by
      by_contra h
      have hi := r.2.2
      have := hb r.1 h
      omega
    have hall : ∀ k l : Fin 7, butterflyW k l ≠ 0 → k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      decide
    have hk := hall k l hw
    have hmem : ∀ a c : Fin 7, butterflyW a c ≠ 0 → butterflyBits q a c r.2.val →
        r ∈ Finset.univ.filter fun r : Σ j, Fin (b j) =>
          butterflyW a c ≠ 0 ∧ butterflyBits q a c r.2.val :=
      fun a c h₁ h₂ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁, h₂⟩
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hr0
    · refine Or.inr ⟨0, by decide, hmem 0 1 (by decide) ?_⟩
      simp only [butterflyBits] at hp ⊢
      simp only [Fin.isValue, one_ne_zero, ite_false, ite_true] at hp ⊢
      split_ifs at hp <;> omega
    · refine Or.inr ⟨0, by decide, hmem 0 2 (by decide) ?_⟩
      simp only [butterflyBits] at hp ⊢
      simp only [show (2 : Fin 7) ≠ 0 by decide, show (2 : Fin 7) ≠ 1 by decide, ite_false,
        ite_true] at hp ⊢
      split_ifs at hp <;> omega
    · simp only [butterflyBits, show (3 : Fin 7) ≠ 0 by decide, show (3 : Fin 7) ≠ 1 by decide,
        show (3 : Fin 7) ≠ 2 by decide, ite_false] at hp
      rcases hp with hp | hp
      · refine Or.inr ⟨1, by decide, hmem 1 3 (by decide) ?_⟩
        simpa [butterflyBits] using hp
      · refine Or.inr ⟨2, by decide, hmem 2 3 (by decide) ?_⟩
        simpa [butterflyBits] using hp
    · refine Or.inr ⟨3, by decide, hmem 3 4 (by decide) ?_⟩
      simpa [butterflyBits] using hp
  deliver r l hl := by
    have hr0 : r.1 = 0 := by
      by_contra h
      have hi := r.2.2
      have := hb r.1 h
      omega
    have hl' : l = 5 ∨ l = 6 := by simpa [multicastD, hr0] using hl
    have hmem : ∀ a c : Fin 7, butterflyW a c ≠ 0 → butterflyBits q a c r.2.val →
        r ∈ Finset.univ.filter fun r : Σ j, Fin (b j) =>
          butterflyW a c ≠ 0 ∧ butterflyBits q a c r.2.val :=
      fun a c h₁ h₂ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁, h₂⟩
    rcases hl' with rfl | rfl
    · by_cases hi : r.2.val < 2 * q
      · exact ⟨1, by decide, hmem 1 5 (by decide) (by simpa [butterflyBits] using hi)⟩
      · refine ⟨4, by decide, hmem 4 5 (by decide) ?_⟩
        simp only [butterflyBits, show (4 : Fin 7) ≠ 0 by decide, show (4 : Fin 7) ≠ 1 by decide,
          show (4 : Fin 7) ≠ 2 by decide, ite_false]
        omega
    · by_cases hi : q ≤ r.2.val
      · exact ⟨2, by decide, hmem 2 6 (by decide) (by simpa [butterflyBits] using hi)⟩
      · refine ⟨4, by decide, hmem 4 6 (by decide) ?_⟩
        simp only [butterflyBits, show (4 : Fin 7) ≠ 0 by decide, show (4 : Fin 7) ≠ 1 by decide,
          show (4 : Fin 7) ≠ 2 by decide, ite_false]
        omega

end ButterflyRouting

/-- The numbers of bits on the edges of a network with integer capacities. -/
lemma floor_natNet {V : Type*} [LT V] (w : V → V → ℕ) (h : ∀ j k, 0 < w j k → j < k) (n : ℕ) :
    (fun k l => ⌊(n : ℝ) * (natNet w h).C k l⌋₊) = fun k l => w k l * n := by
  funext k l
  have : (n : ℝ) * (natNet w h).C k l = ((w k l * n : ℕ) : ℝ) := by
    simp [natNet, mul_comm]
  rw [this, Nat.floor_natCast]

/-- Rate `3/2` is the limit of routing with copies at the source, too. -/
theorem butterfly_routing_of_lt {R : ℝ} (h0 : 0 ≤ R) (h : R < 3 / 2) :
    IsRoutingAchievable butterflyNet (multicastD 0 {5, 6}) (singleRate 0 R) := by
  refine ⟨fun j => ?_, ?_⟩
  · simp only [singleRate]
    split_ifs <;> simp [h0]
  have hgap : 0 < 3 / 2 - R := sub_pos.mpr h
  have hev : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ (n : ℝ) * (3 / 2 - R) :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hgap |>.eventually_ge_atTop _
  filter_upwards [hev] with n hn
  rw [butterflyNet, floor_natNet]
  refine ⟨butterflyScheme (q := n / 2) (fun j hj => ceil_singleRate_of_ne 0 R n hj)
    (by omega) ?_⟩
  refine Nat.ceil_le.mpr ?_
  have hq : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    exact_mod_cast this
  simp only [singleRate, ite_true]
  push_cast
  nlinarith

/-- The rate of routing on the butterfly network is at most `3/2`. -/
theorem butterfly_routing_rate_le {R : ℝ}
    (h : IsRoutingAchievable butterflyNet (multicastD 0 {5, 6}) (singleRate 0 R)) : R ≤ 3 / 2 := by
  obtain ⟨n, ⟨S⟩, hn⟩ := (h.2.and (eventually_gt_atTop 0)).exists
  rw [butterflyNet, floor_natNet] at S
  have hbound := butterfly_routing_le (n := n) S (fun j k hjk => by simp [hjk])
    (fun j hj => ceil_singleRate_of_ne 0 R n hj) (fun j k => by
      have hall : ∀ j k : Fin 7, butterflyW j k ≤ 1 := by decide
      exact Nat.mul_le_of_le_div _ _ _ (by simpa [Nat.div_self hn] using hall j k))
  have hle : (n : ℝ) * R ≤ ((⌈(n : ℝ) * singleRate 0 R 0⌉₊ : ℕ) : ℝ) := by
    simpa [singleRate] using Nat.le_ceil ((n : ℝ) * R)
  have hb : (2 : ℝ) * ((⌈(n : ℝ) * singleRate 0 R 0⌉₊ : ℕ) : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast hbound
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-! ### The multiple unicast network of page 16-26 -/

/-- **Page 16-26 of [elgamal2010].** The variant of the butterfly network, numbered from `0`. -/
def unicastW : Fin 6 → Fin 6 → ℕ :=
  ![![0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0]]

/-- The network of page 16-26. -/
def unicastNet : NoiselessNetwork (Fin 6) := natNet unicastW (by decide)

/-- The destinations of the figure of page 16-26: the message of node `1` goes to node `6` and the
message of node `2` goes to node `5`. Nodes are numbered from `0` here. -/
def unicastD : Fin 6 → Finset (Fin 6) := ![{5}, {4}, ∅, ∅, ∅, ∅]

/-- The destinations as printed in the text of page 16-26. With them each message has a direct edge
to its destination, so routing achieves `(1, 1)`, see `printed_unicast_routing`. -/
def printedUnicastD : Fin 6 → Finset (Fin 6) := ![{4}, {5}, ∅, ∅, ∅, ∅]

/-- The code of page 16-27: the bottleneck carries the XOR of the two messages. -/
def unicastCode (n : ℕ) : NetCode (Fin 6) (fun _ _ => Bitstream n) (fun _ => Bitstream n) :=
  funCode
    (fun k l u m => if unicastW k l = 0 then 0 else
      if k = 0 ∨ k = 1 then m else if k = 2 then u 0 + u 1 else u 2)
    (fun l _ u => if l = 5 then u 3 + u 1 else u 3 + u 0)

lemma unicastCode_correct (n : ℕ) (m : Fin 6 → Bitstream n) :
    (unicastCode n).Correct unicastD m := by
  have e02 : (unicastCode n).edge m 0 2 = m 0 := by
    rw [unicastCode, funCode_edge]
    simp [unicastW]
  have e04 : (unicastCode n).edge m 0 4 = m 0 := by
    rw [unicastCode, funCode_edge]
    simp [unicastW]
  have e12 : (unicastCode n).edge m 1 2 = m 1 := by
    rw [unicastCode, funCode_edge]
    simp [unicastW]
  have e15 : (unicastCode n).edge m 1 5 = m 1 := by
    rw [unicastCode, funCode_edge]
    simp [unicastW]
  have e23 : (unicastCode n).edge m 2 3 = m 0 + m 1 := by
    rw [← e02, ← e12, unicastCode, funCode_edge]
    simp [unicastW]
  have e34 : (unicastCode n).edge m 3 4 = m 0 + m 1 := by
    rw [← e23, unicastCode, funCode_edge]
    simp [unicastW]
  have e35 : (unicastCode n).edge m 3 5 = m 0 + m 1 := by
    rw [← e23, unicastCode, funCode_edge]
    simp [unicastW]
  intro j l hl
  have hj : (j = 0 ∧ l = 5) ∨ (j = 1 ∧ l = 4) := by
    have hall : ∀ j l : Fin 6, l ∈ unicastD j → (j = 0 ∧ l = 5) ∨ (j = 1 ∧ l = 4) := by decide
    exact hall j l hl
  rw [unicastCode, funCode_out, ← unicastCode]
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [ite_true, show (3 : Fin 6) < 5 by decide, show (1 : Fin 6) < 5 by decide, e35, e15]
    have hsum : m 0 + m 1 + m 1 = m 1 + (m 1 + m 0) := by abel
    rw [hsum, stream_add_add]
  · simp only [show ¬ (4 : Fin 6) = 5 by decide, ite_false, show (3 : Fin 6) < 4 by decide,
      show (0 : Fin 6) < 4 by decide, ite_true, e34, e04]
    rw [add_comm, stream_add_add]

/-- **Page 16-27 of [elgamal2010].** Linear network coding achieves all rates up to `1` with zero
error. -/
theorem unicast_isAchievableZE {R : Fin 6 → ℝ} (h0 : ∀ j, 0 ≤ R j) (hR : ∀ j, 2 ≤ j → R j = 0)
    (h₁ : R 0 ≤ 1) (h₂ : R 1 ≤ 1) : IsAchievableZE unicastNet unicastD R := by
  refine ⟨h0, Eventually.of_forall fun n => ?_⟩
  refine exists_rateCode_unit _ (by decide) (unicastCode n) (unicastCode_correct n)
    (fun m k l hkl => ?_) fun j => ?_
  · rw [unicastCode, funCode_edge]
    simp [hkl]
  · have hcard : Fintype.card (Bitstream n) = 2 ^ n := by simp [ZMod.card]
    rw [hcard]
    refine Nat.pow_le_pow_right (by norm_num) (Nat.ceil_le.mpr ?_)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hRj : R j ≤ 1 := by
      have hall : ∀ j : Fin 6, j = 0 ∨ j = 1 ∨ 2 ≤ j := by decide
      rcases hall j with rfl | rfl | h
      · exact h₁
      · exact h₂
      · rw [hR j h]
        norm_num
    nlinarith

/-- A cut of a network with integer capacities, evaluated by computation. -/
lemma cut_bound_nat {V : Type*} [LinearOrder V] [Fintype V] {w : V → V → ℕ}
    {hw : ∀ j k, 0 < w j k → j < k} {D : V → Finset V} {R : V → ℝ}
    (h : IsAchievable (natNet w hw) D R) (S : Finset V) :
    ∑ j ∈ cutSources D S, R j ≤ ((∑ j ∈ S, ∑ k ∈ Sᶜ, w j k : ℕ) : ℝ) := by
  have hb := (IsAchievable.mem_cutsetRegion h).2 S
  have hc : cutCap (natNet w hw).C S = ((∑ j ∈ S, ∑ k ∈ Sᶜ, w j k : ℕ) : ℝ) := cutCap_natCast w S
  rwa [hc] at hb

/-- **Page 16-27 of [elgamal2010].** The cutset outer bound `R₁, R₂ ≤ 1`, from the cuts
`{1, 3, 4, 5}` and `{2, 3, 4, 6}`. -/
theorem unicast_le_one {R : Fin 6 → ℝ} (h : IsAchievable unicastNet unicastD R) :
    R 0 ≤ 1 ∧ R 1 ≤ 1 := by
  constructor
  · have h₁ := cut_bound_nat h {0, 2, 3, 4}
    have hs : cutSources unicastD {0, 2, 3, 4} = {0} := by decide
    have hc : (∑ j ∈ ({0, 2, 3, 4} : Finset (Fin 6)), ∑ k ∈ ({0, 2, 3, 4} : Finset (Fin 6))ᶜ,
        unicastW j k) = 1 := by decide
    rw [hs, hc] at h₁
    simpa using h₁
  · have h₁ := cut_bound_nat h {1, 2, 3, 5}
    have hs : cutSources unicastD {1, 2, 3, 5} = {1} := by decide
    have hc : (∑ j ∈ ({1, 2, 3, 5} : Finset (Fin 6)), ∑ k ∈ ({1, 2, 3, 5} : Finset (Fin 6))ᶜ,
        unicastW j k) = 1 := by decide
    rw [hs, hc] at h₁
    simpa using h₁

/-- **Page 16-27 of [elgamal2010].** The achievable rates of the network of page 16-26: network
coding achieves the cutset outer bound exactly. -/
theorem unicast_iff {R : Fin 6 → ℝ} (h0 : ∀ j, 0 ≤ R j) (hR : ∀ j, 2 ≤ j → R j = 0) :
    IsAchievable unicastNet unicastD R ↔ R 0 ≤ 1 ∧ R 1 ≤ 1 :=
  ⟨unicast_le_one, fun h => (unicast_isAchievableZE h0 hR h.1 h.2).isAchievable⟩

/-- **Page 16-27 of [elgamal2010].** Routing is limited by the bottleneck edge `(3, 4)`: all the
bits of both messages have to go through it. -/
theorem unicast_routing_bound {cap : Fin 6 → Fin 6 → ℕ} {b : Fin 6 → ℕ}
    (S : RoutingScheme cap b unicastD) (hz : ∀ j k, unicastW j k = 0 → cap j k = 0)
    (hb : ∀ j, 2 ≤ j → b j = 0) : b 0 + b 1 ≤ cap 2 3 := by
  have hempty : ∀ j k (r : Σ j, Fin (b j)), unicastW j k = 0 → r ∉ S.carry j k := by
    intro j k r hjk hr
    have := S.card_le j k
    rw [hz j k hjk] at this
    exact absurd hr (by simp [Finset.card_eq_zero.mp (Nat.le_zero.mp this)])
  have hsrc : ∀ r : Σ j, Fin (b j), r.1 = 0 ∨ r.1 = 1 := by
    intro r
    have hall : ∀ j : Fin 6, j = 0 ∨ j = 1 ∨ 2 ≤ j := by decide
    rcases hall r.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have hi := r.2.2
      have := hb r.1 h
      omega
  have hthrough : ∀ l (r : Σ j, Fin (b j)), r ∈ S.carry 3 l → r ∈ S.carry 2 3 := by
    intro l r hr
    rcases S.forward 3 l r hr with h | ⟨j, -, hj⟩
    · rcases hsrc r with h' | h' <;> exact absurd (h'.symm.trans h) (by decide)
    · have hall : ∀ j : Fin 6, j ≠ 2 → unicastW j 3 = 0 := by decide
      by_cases hj2 : j = 2
      · exact hj2 ▸ hj
      · exact absurd hj (hempty j 3 r (hall j hj2))
  have hmem : ∀ r : Σ j, Fin (b j), r ∈ S.carry 2 3 := by
    intro r
    rcases hsrc r with h0 | h1
    · obtain ⟨i, -, hi⟩ := S.deliver r 5 (by simp [h0, unicastD])
      have hall : ∀ i : Fin 6, i ≠ 1 → i ≠ 3 → unicastW i 5 = 0 := by decide
      by_cases hi1 : i = 1
      · subst hi1
        rcases S.forward 1 5 r hi with h | ⟨j, hj, hjr⟩
        · exact absurd (h0.symm.trans h) (by decide)
        · have hj0 : ∀ j : Fin 6, j < 1 → unicastW j 1 = 0 := by decide
          exact absurd hjr (hempty j 1 r (hj0 j hj))
      · by_cases hi3 : i = 3
        · subst hi3
          exact hthrough 5 r hi
        · exact absurd hi (hempty i 5 r (hall i hi1 hi3))
    · obtain ⟨i, -, hi⟩ := S.deliver r 4 (by simp [h1, unicastD])
      have hall : ∀ i : Fin 6, i ≠ 0 → i ≠ 3 → unicastW i 4 = 0 := by decide
      by_cases hi0 : i = 0
      · subst hi0
        rcases S.forward 0 4 r hi with h | ⟨j, hj, -⟩
        · exact absurd (h1.symm.trans h) (by decide)
        · exact absurd hj (by simp)
      · by_cases hi3 : i = 3
        · subst hi3
          exact hthrough 4 r hi
        · exact absurd hi (hempty i 4 r (hall i hi0 hi3))
  have hdisj : Disjoint (ownBits b 0) (ownBits b 1) := by
    refine Finset.disjoint_left.mpr fun r h₀ h₁ => ?_
    have := (mem_ownBits.mp h₀).symm.trans (mem_ownBits.mp h₁)
    exact absurd this (by decide)
  have hcard := Finset.card_le_card (s := ownBits b 0 ∪ ownBits b 1) (t := S.carry 2 3)
    fun r _ => hmem r
  rw [Finset.card_union_of_disjoint hdisj, card_ownBits, card_ownBits] at hcard
  exact hcard.trans (S.card_le 2 3)

/-- **Page 16-27 of [elgamal2010].** Routing can achieve at most `R₁ + R₂ ≤ 1`. -/
theorem unicast_routing_le {R : Fin 6 → ℝ} (hR : ∀ j, 2 ≤ j → R j = 0)
    (h : IsRoutingAchievable unicastNet unicastD R) : R 0 + R 1 ≤ 1 := by
  obtain ⟨n, ⟨S⟩, hn⟩ := (h.2.and (eventually_gt_atTop 0)).exists
  rw [unicastNet, floor_natNet] at S
  have hbound := unicast_routing_bound S (fun j k hjk => by simp [hjk])
    (fun j hj => by simp [hR j hj])
  have h₀ : (n : ℝ) * R 0 ≤ ((⌈(n : ℝ) * R 0⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h₁ : (n : ℝ) * R 1 ≤ ((⌈(n : ℝ) * R 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hw : unicastW 2 3 = 1 := by decide
  rw [hw, one_mul] at hbound
  have hb : ((⌈(n : ℝ) * R 0⌉₊ : ℕ) : ℝ) + ((⌈(n : ℝ) * R 1⌉₊ : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hbound
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-- With the destinations printed in the text of page 16-26, routing alone achieves `(1, 1)`, which
contradicts the bound `R₁ + R₂ ≤ 1` stated there. So the destinations of the text have to be
exchanged, as in the figure. -/
theorem printed_unicast_routing {R : Fin 6 → ℝ} (h0 : ∀ j, 0 ≤ R j) (h₁ : R 0 ≤ 1) (h₂ : R 1 ≤ 1) :
    IsRoutingAchievable unicastNet printedUnicastD R := by
  refine ⟨h0, Eventually.of_forall fun n => ?_⟩
  rw [unicastNet, floor_natNet]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb₀ : ⌈(n : ℝ) * R 0⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hb₁ : ⌈(n : ℝ) * R 1⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hwa : unicastW 0 4 = 1 := by decide
  have hwb : unicastW 1 5 = 1 := by decide
  refine ⟨⟨fun k l => if k = 0 ∧ l = 4 then ownBits _ 0 else
    if k = 1 ∧ l = 5 then ownBits _ 1 else ∅, fun k l => ?_, fun k l r hr => ?_, fun r l hl => ?_⟩⟩
  · split_ifs with h h'
    · obtain ⟨rfl, rfl⟩ := h
      rw [card_ownBits, hwa, one_mul]
      exact hb₀
    · obtain ⟨rfl, rfl⟩ := h'
      rw [card_ownBits, hwb, one_mul]
      exact hb₁
    · simp
  · split_ifs at hr with h h'
    · exact Or.inl ((mem_ownBits.mp hr).trans h.1.symm)
    · exact Or.inl ((mem_ownBits.mp hr).trans h'.1.symm)
    · simp at hr
  · have hall : ∀ j l : Fin 6, l ∈ printedUnicastD j → (j = 0 ∧ l = 4) ∨ (j = 1 ∧ l = 5) := by
      decide
    rcases hall r.1 l hl with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
    · exact ⟨0, by decide, by simpa using mem_ownBits.mpr hj⟩
    · exact ⟨1, by decide, by simpa using mem_ownBits.mpr hj⟩

/-! ### The linear code of page 16-18 -/

/-- **Page 16-18 of [elgamal2010].** The multigraph of the example: the edges are `(1, 2)`,
`(1, 3)`, `(2, 3)`, `(2, 4)` and `(3, 4)`, with nodes numbered from `0`. -/
def kmGraph : Multigraph (Fin 4) (Fin 5) :=
  ⟨![0, 0, 1, 1, 2], ![1, 2, 2, 3, 3], by decide⟩

/-- Node `1` has a message of two symbols. -/
def kmB : Fin 4 → ℕ := ![2, 0, 0, 0]

/-- The symbols of the message. -/
def kmBit (i : Fin 2) : Σ j, Fin (kmB j) := ⟨0, i⟩

section KM

variable {K : Type*} [CommRing K] (α : Fin 12 → K)

/-- **Page 16-18 of [elgamal2010].** The coefficients `α₁, …, α₁₂` of the example, here
  `α 0, …, α 11`.
-/
def kmCoeff : LinCoeff K (Fin 5) kmB where
  y r e := if e = 0 then (if r.2.val = 0 then α 0 else α 1)
    else if e = 1 then (if r.2.val = 0 then α 2 else α 3) else 0
  x e' e := if e' = 0 ∧ e = 2 then α 4 else if e' = 0 ∧ e = 3 then α 5
    else if e' = 1 ∧ e = 4 then α 6 else if e' = 2 ∧ e = 4 then α 7 else 0
  z _ e r := if e = 3 then (if r.2.val = 0 then α 8 else α 10)
    else if e = 4 then (if r.2.val = 0 then α 9 else α 11) else 0

lemma sum_subtype_five {M : Type*} [AddCommMonoid M] (p : Fin 5 → Prop) [DecidablePred p]
    [Fintype {e // p e}] (f : Fin 5 → M) : ∑ e : {e // p e}, f e.1 =
      ∑ e, if p e then f e else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

/-- **Page 16-18 of [elgamal2010].** The linear transformation induced by the code of the
example. -/
theorem km_transfer (i i' : Fin 2) :
    transfer kmGraph (kmCoeff α) 3 (kmBit i) (kmBit i') =
      (!![α 8, α 9; α 10, α 11] * !![α 5, 0; α 4 * α 7, α 6] * !![α 0, α 1; α 2, α 3]) i i' := by
  set c := kmCoeff α with hc
  have h₀ : globalVec kmGraph c 0 (kmBit i') = if i' = 0 then α 0 else α 1 := by
    rw [globalVec_eq, sum_subtype_five (fun e' => kmGraph.head e' = kmGraph.tail 0)
      (fun e' => c.x e' 0 * globalVec kmGraph c e' (kmBit i'))]
    fin_cases i' <;> simp [kmGraph, kmBit, hc, kmCoeff]
  have h₁ : globalVec kmGraph c 1 (kmBit i') = if i' = 0 then α 2 else α 3 := by
    rw [globalVec_eq, sum_subtype_five (fun e' => kmGraph.head e' = kmGraph.tail 1)
      (fun e' => c.x e' 1 * globalVec kmGraph c e' (kmBit i'))]
    fin_cases i' <;> simp [kmGraph, kmBit, hc, kmCoeff]
  have h₂ : globalVec kmGraph c 2 (kmBit i') = α 4 * globalVec kmGraph c 0 (kmBit i') := by
    rw [globalVec_eq, sum_subtype_five (fun e' => kmGraph.head e' = kmGraph.tail 2)
      (fun e' => c.x e' 2 * globalVec kmGraph c e' (kmBit i'))]
    simp [Fin.sum_univ_five, kmGraph, kmBit, hc, kmCoeff]
  have h₃ : globalVec kmGraph c 3 (kmBit i') = α 5 * globalVec kmGraph c 0 (kmBit i') := by
    rw [globalVec_eq, sum_subtype_five (fun e' => kmGraph.head e' = kmGraph.tail 3)
      (fun e' => c.x e' 3 * globalVec kmGraph c e' (kmBit i'))]
    simp [Fin.sum_univ_five, kmGraph, kmBit, hc, kmCoeff]
  have h₄ : globalVec kmGraph c 4 (kmBit i') = α 6 * globalVec kmGraph c 1 (kmBit i') +
      α 7 * globalVec kmGraph c 2 (kmBit i') := by
    rw [globalVec_eq, sum_subtype_five (fun e' => kmGraph.head e' = kmGraph.tail 4)
      (fun e' => c.x e' 4 * globalVec kmGraph c e' (kmBit i'))]
    simp [Fin.sum_univ_five, kmGraph, kmBit, hc, kmCoeff]
  have hA : transfer kmGraph c 3 (kmBit i) (kmBit i') =
      (if i = 0 then α 8 else α 10) * globalVec kmGraph c 3 (kmBit i') +
        (if i = 0 then α 9 else α 11) * globalVec kmGraph c 4 (kmBit i') := by
    simp only [transfer]
    rw [sum_subtype_five (fun e => kmGraph.head e = 3)
      (fun e => c.z 3 e (kmBit i) * globalVec kmGraph c e (kmBit i'))]
    fin_cases i <;> simp [Fin.sum_univ_five, kmGraph, kmBit, hc, kmCoeff]
  rw [hA, h₃, h₄, h₂, h₀, h₁]
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Page 16-20 of [elgamal2010].** The transformation of the example with indeterminates, and its
determinant. Here `x k` stands for `x_{k+1}`. -/
theorem km_det (x : Fin 12 → K) :
    (!![x 8, x 9; x 10, x 11] * !![x 5, 0; x 4 * x 7, x 6] * !![x 0, x 1; x 2, x 3]).det =
      (x 0 * (x 5 * x 8 + x 4 * x 7 * x 9) + x 2 * x 6 * x 9) *
          (x 1 * (x 5 * x 10 + x 4 * x 7 * x 11) + x 3 * x 6 * x 11) -
        (x 0 * (x 5 * x 10 + x 4 * x 7 * x 11) + x 2 * x 6 * x 11) *
          (x 1 * (x 5 * x 8 + x 4 * x 7 * x 9) + x 3 * x 6 * x 9) := by
  simp [Matrix.det_fin_two]
  ring

end KM

end InfoTheory.ElGamalKim
