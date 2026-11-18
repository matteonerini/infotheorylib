/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture16Examples

/-!
# Lecture 16: a network for which the cutset outer bound is loose

The network of page 16-27 of El Gamal and Kim: node `1` sends its message to nodes `3`, `4` and `5`,
and node `2` sends its message to node `5`. The capacity region is `R₁ ≤ 1`, `2 R₁ + R₂ ≤ 2`, while
the cutset outer bound is `R₁ ≤ 1`, `R₁ + R₂ ≤ 2`. Nodes are numbered from `0` here.

## Main statements

* `yeung_count`: the bound `(1 - P_e) |M₁| √|M₂| ≤ √|A₂₃| √|A₂₄|`.
* `yeung_le`: every achievable rate pair has `2 R₁ + R₂ ≤ 2`.
* `yeung_isRoutingAchievable`: forwarding achieves the rest.
* `yeung_capacityRegion`, `yeung_cutsetRegion`: the two regions.
* `yeung_cutset_loose`: `(1, 1)` is in the cutset region and not in the capacity region.

## Implementation notes

The notes state the capacity region without a proof. Given the message of node `1`, the indices on
the edges `(2, 3)` and `(2, 4)` lie in the sets decoded to it, whose sizes add up to the size of an
alphabet. Counting correctly decoded messages and applying the Cauchy–Schwarz inequality gives a
strong converse.
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-- **Page 16-27 of [elgamal2010].** The capacities, with nodes numbered from `0`. -/
def yeungW : Fin 5 → Fin 5 → ℕ :=
  ![![0, 1, 0, 0, 0],
    ![0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0]]

/-- The network of page 16-27. -/
def yeungNet : NoiselessNetwork (Fin 5) := natNet yeungW (by decide)

/-- The destinations of page 16-27. -/
def yeungD : Fin 5 → Finset (Fin 5) := ![{2, 3, 4}, {4}, ∅, ∅, ∅]

/-- The rate tuple with `R₃ = R₄ = R₅ = 0`. -/
def yeungRate (p : ℝ × ℝ) : Fin 5 → ℝ := ![p.1, p.2, 0, 0, 0]

section Count

variable {A : Fin 5 → Fin 5 → Type*} {M : Fin 5 → Type*} [∀ j k, Fintype (A j k)]
  [∀ j, Fintype (M j)] [∀ j, Nonempty (M j)]

/-- **The converse of page 16-28, counting form.** -/
theorem yeung_count (c : NetCode (Fin 5) A M) (hA : ∀ j k, yeungW j k = 0 → Subsingleton (A j k))
    (hM : ∀ j, 2 ≤ j → Subsingleton (M j)) :
    (1 - c.errProb yeungD) * Fintype.card (M 0) * √(Fintype.card (M 1) : ℝ) ≤
      √(Fintype.card (A 1 2) : ℝ) * √(Fintype.card (A 1 3) : ℝ) := by
  classical
  -- agreement across a cut
  have hcong : ∀ (S : Finset (Fin 5)) (m m' : ∀ j, M j), (∀ j, j ∉ S → 2 ≤ j) →
      (∀ j ∈ S, ∀ k, k ∉ S → yeungW j k ≠ 0 → c.edge m j k = c.edge m' j k) →
      ∀ l, l ∉ S → ∀ j, c.out m l j = c.out m' l j := by
    intro S m m' hS he l hl j
    refine c.out_congr (S := S) (fun i hi => (hM i (hS i hi)).elim _ _) (fun i hi k hk => ?_) hl j
    by_cases hw : yeungW i k = 0
    · exact (hA i k hw).elim _ _
    · exact he i hi k hk hw
  have hext : ∀ m m' : ∀ j, M j, m 0 = m' 0 → m 1 = m' 1 → m = m' := by
    intro m m' h₀ h₁
    funext j
    have hall : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ 2 ≤ j := by decide
    rcases hall j with rfl | rfl | h
    · exact h₀
    · exact h₁
    · exact (hM j h).elim _ _
  let Good : Finset (∀ j, M j) := Finset.univ.filter fun m => c.Correct yeungD m
  let G : M 0 → Finset (∀ j, M j) := fun a => Good.filter fun m => m 0 = a
  let xs : M 0 → Finset (A 1 2) := fun a => (G a).image fun m => c.edge m 1 2
  let ys : M 0 → Finset (A 1 3) := fun a => (G a).image fun m => c.edge m 1 3
  have hG : ∀ a m, m ∈ G a → c.Correct yeungD m ∧ m 0 = a := by
    intro a m hm
    obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hm
    exact ⟨(Finset.mem_filter.mp h₁).2, h₂⟩
  -- the indices of different messages of node `1` are different
  have hxdisj : ∀ a a', a ≠ a' → Disjoint (xs a) (xs a') := by
    intro a a' haa
    refine Finset.disjoint_left.mpr fun ξ h₁ h₂ => haa ?_
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨m', hm', hx⟩ := Finset.mem_image.mp h₂
    obtain ⟨hc, rfl⟩ := hG a m hm
    obtain ⟨hc', rfl⟩ := hG a' m' hm'
    have hout := hcong {0, 1, 3, 4} m m' (by decide) (fun j hj k hk hw => ?_) 2 (by decide) 0
    · rw [← hc 0 2 (by decide), hout]
      exact hc' 0 2 (by decide)
    · have hall : ∀ j ∈ ({0, 1, 3, 4} : Finset (Fin 5)), ∀ k, k ∉ ({0, 1, 3, 4} : Finset (Fin 5)) →
          yeungW j k ≠ 0 → j = 1 ∧ k = 2 := by decide
      obtain ⟨rfl, rfl⟩ := hall j hj k hk hw
      exact hx.symm
  have hydisj : ∀ a a', a ≠ a' → Disjoint (ys a) (ys a') := by
    intro a a' haa
    refine Finset.disjoint_left.mpr fun ξ h₁ h₂ => haa ?_
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨m', hm', hx⟩ := Finset.mem_image.mp h₂
    obtain ⟨hc, rfl⟩ := hG a m hm
    obtain ⟨hc', rfl⟩ := hG a' m' hm'
    have hout := hcong {0, 1, 2, 4} m m' (by decide) (fun j hj k hk hw => ?_) 3 (by decide) 0
    · rw [← hc 0 3 (by decide), hout]
      exact hc' 0 3 (by decide)
    · have hall : ∀ j ∈ ({0, 1, 2, 4} : Finset (Fin 5)), ∀ k, k ∉ ({0, 1, 2, 4} : Finset (Fin 5)) →
          yeungW j k ≠ 0 → j = 1 ∧ k = 3 := by decide
      obtain ⟨rfl, rfl⟩ := hall j hj k hk hw
      exact hx.symm
  have hxsum : ∑ a, #(xs a) ≤ Fintype.card (A 1 2) := by
    rw [← Finset.card_biUnion fun a _ a' _ h => hxdisj a a' h]
    exact Finset.card_le_univ _
  have hysum : ∑ a, #(ys a) ≤ Fintype.card (A 1 3) := by
    rw [← Finset.card_biUnion fun a _ a' _ h => hydisj a a' h]
    exact Finset.card_le_univ _
  -- the fibers
  have hG₁ : ∀ a, #(G a) ≤ #(xs a) * #(ys a) := by
    intro a
    rw [← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun m => (c.edge m 1 2, c.edge m 1 3))
      (fun m hm => Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ hm, Finset.mem_image_of_mem _ hm⟩) ?_
    intro m hm m' hm' he
    have he₁ : c.edge m 1 2 = c.edge m' 1 2 := congrArg Prod.fst he
    have he₂ : c.edge m 1 3 = c.edge m' 1 3 := congrArg Prod.snd he
    obtain ⟨hc, h₀⟩ := hG a m hm
    obtain ⟨hc', h₀'⟩ := hG a m' hm'
    have hout := hcong {0, 1} m m' (by decide) (fun j hj k hk hw => ?_) 4 (by decide) 1
    · refine hext m m' (h₀.trans h₀'.symm) ?_
      rw [← hc 1 4 (by decide), hout]
      exact hc' 1 4 (by decide)
    · have hall : ∀ j ∈ ({0, 1} : Finset (Fin 5)), ∀ k, k ∉ ({0, 1} : Finset (Fin 5)) →
          yeungW j k ≠ 0 → (j = 1 ∧ k = 2) ∨ (j = 1 ∧ k = 3) := by decide
      rcases hall j hj k hk hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact he₁
      · exact he₂
  have hG₂ : ∀ a, #(G a) ≤ Fintype.card (M 1) := by
    intro a
    refine Finset.card_le_card_of_injOn (t := Finset.univ) (fun m => m 1)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
    intro m hm m' hm' he
    exact hext m m' ((hG a m hm).2.trans (hG a m' hm').2.symm) he
  have hsum : #Good = ∑ a, #(G a) :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  -- Cauchy–Schwarz
  have hfib : ∀ a, (#(G a) : ℝ) ≤ √(Fintype.card (M 1) : ℝ) *
    (√(#(xs a) : ℝ) * √(#(ys a) : ℝ)) := by
    intro a
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine Real.le_sqrt_of_sq_le ?_
    have h₁ : (#(G a) : ℝ) ≤ #(xs a) * #(ys a) := by exact_mod_cast hG₁ a
    have h₂ : (#(G a) : ℝ) ≤ Fintype.card (M 1) := by exact_mod_cast hG₂ a
    have h₀ : (0 : ℝ) ≤ #(G a) := Nat.cast_nonneg _
    rw [sq]
    exact mul_le_mul h₂ h₁ h₀ (Nat.cast_nonneg _)
  have hgood : (#Good : ℝ) ≤ √(Fintype.card (M 1) : ℝ) *
      (√(Fintype.card (A 1 2) : ℝ) * √(Fintype.card (A 1 3) : ℝ)) := by
    have hcs := Real.sum_sqrt_mul_sqrt_le Finset.univ (f := fun a => (#(xs a) : ℝ))
      (g := fun a => (#(ys a) : ℝ)) (fun _ => Nat.cast_nonneg _) fun _ => Nat.cast_nonneg _
    have hx : √(∑ a, (#(xs a) : ℝ)) ≤ √(Fintype.card (A 1 2) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hxsum)
    have hy : √(∑ a, (#(ys a) : ℝ)) ≤ √(Fintype.card (A 1 3) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hysum)
    calc (#Good : ℝ) = ∑ a, (#(G a) : ℝ) := by rw [hsum]; push_cast; rfl
      _ ≤ ∑ a, √(Fintype.card (M 1) : ℝ) * (√(#(xs a) : ℝ) * √(#(ys a) : ℝ)) :=
        Finset.sum_le_sum fun a _ => hfib a
      _ = √(Fintype.card (M 1) : ℝ) * ∑ a, √(#(xs a) : ℝ) * √(#(ys a) : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (Real.sqrt_nonneg _)
        exact mul_le_mul hx hy (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the number of messages
  have hone : ∀ j, 2 ≤ j → Fintype.card (M j) = 1 := fun j hj =>
    le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr (hM j hj)) Fintype.card_pos
  have hall : (Fintype.card (∀ j, M j) : ℝ) = Fintype.card (M 0) * Fintype.card (M 1) := by
    rw [Fintype.card_pi, Fin.prod_univ_five, hone 2 (by decide), hone 3 (by decide),
      hone 4 (by decide)]
    simp
  have hM₀ : (0 : ℝ) < Fintype.card (M 0) := by exact_mod_cast Fintype.card_pos
  have hM₁ : (0 : ℝ) < Fintype.card (M 1) := by exact_mod_cast Fintype.card_pos
  have hw : 0 < √(Fintype.card (M 1) : ℝ) := Real.sqrt_pos.mpr hM₁
  have hsq : √(Fintype.card (M 1) : ℝ) * √(Fintype.card (M 1) : ℝ) = Fintype.card (M 1) :=
    Real.mul_self_sqrt hM₁.le
  rw [c.one_sub_errProb, hall]
  have hval : (#{m : ∀ j, M j | c.Correct yeungD m} : ℝ) /
      (Fintype.card (M 0) * (Fintype.card (M 1) : ℝ)) * Fintype.card (M 0) *
        √(Fintype.card (M 1) : ℝ) = (#Good : ℝ) / √(Fintype.card (M 1) : ℝ) := by
    change (#Good : ℝ) / (Fintype.card (M 0) * (Fintype.card (M 1) : ℝ)) * _ * _ = _
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (by positivity) hw.ne',
      mul_assoc ((#Good : ℝ) * _), hsq]
    ring
  rw [hval, div_le_iff₀ hw, mul_comm (√(Fintype.card (A 1 2) : ℝ) * _)]
  exact hgood

end Count

/-! ### The converse in bits -/

/-- **Page 16-28 of [elgamal2010].** Every achievable rate pair has `2 R₁ + R₂ ≤ 2`. -/
theorem yeung_le {p : ℝ × ℝ} (h : IsAchievable yeungNet yeungD (yeungRate p)) :
    2 * p.1 + p.2 ≤ 2 := by
  obtain ⟨-, c, hc⟩ := h
  have hC : ∀ j k, yeungNet.C j k = (yeungW j k : ℝ) := fun _ _ => rfl
  have hbound : ∀ n : ℕ, (1 - (c n).errProb yeungD) *
      (2 : ℝ) ^ ((n : ℝ) * (p.1 + p.2 / 2)) ≤ (2 : ℝ) ^ ((n : ℝ) * 1) := by
    intro n
    have hcount := yeung_count (c n)
      (fun j k hjk => by
        have : ⌊(n : ℝ) * yeungNet.C j k⌋₊ = 0 := by simp [hC, hjk]
        rw [this, pow_zero]
        infer_instance)
      (fun j hj => by
        have hall : ∀ j : Fin 5, 2 ≤ j → yeungRate p j = 0 := by
          intro j hj
          have hcases : ∀ j : Fin 5, 2 ≤ j → j = 2 ∨ j = 3 ∨ j = 4 := by decide
          rcases hcases j hj with rfl | rfl | rfl <;> rfl
        have : ⌈(n : ℝ) * yeungRate p j⌉₊ = 0 := by simp [hall j hj]
        rw [this, pow_zero]
        infer_instance)
    have h1 : 0 ≤ 1 - (c n).errProb yeungD := sub_nonneg.mpr ((c n).errProb_le_one _)
    have hcard : ∀ a : ℕ, (Fintype.card (Fin (2 ^ a)) : ℝ) = (2 : ℝ) ^ (a : ℝ) := by
      intro a
      rw [Fintype.card_fin, Real.rpow_natCast]
      push_cast
      rfl
    have hedge₁ : ⌊(n : ℝ) * yeungNet.C 1 2⌋₊ = n := by
      have : yeungW 1 2 = 1 := by decide
      simp [hC, this]
    have hedge₂ : ⌊(n : ℝ) * yeungNet.C 1 3⌋₊ = n := by
      have : yeungW 1 3 = 1 := by decide
      simp [hC, this]
    rw [hedge₁, hedge₂, Real.mul_self_sqrt (by positivity), hcard n] at hcount
    have hp₀ : yeungRate p 0 = p.1 := rfl
    have hp₁ : yeungRate p 1 = p.2 := rfl
    rw [hcard, hcard, hp₀, hp₁] at hcount
    have hL₀ : (2 : ℝ) ^ ((n : ℝ) * p.1) ≤ (2 : ℝ) ^ ((⌈(n : ℝ) * p.1⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    have hL₁ : (2 : ℝ) ^ ((n : ℝ) * (p.2 / 2)) ≤ √((2 : ℝ) ^ ((⌈(n : ℝ) * p.2⌉₊ : ℕ) : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have := Nat.le_ceil ((n : ℝ) * p.2)
      linarith
    have hprod : (2 : ℝ) ^ ((n : ℝ) * (p.1 + p.2 / 2)) =
        (2 : ℝ) ^ ((n : ℝ) * p.1) * (2 : ℝ) ^ ((n : ℝ) * (p.2 / 2)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    rw [hprod, mul_one]
    calc _ ≤ (1 - (c n).errProb yeungD) * (2 : ℝ) ^ ((⌈(n : ℝ) * p.1⌉₊ : ℕ) : ℝ) *
          √((2 : ℝ) ^ ((⌈(n : ℝ) * p.2⌉₊ : ℕ) : ℝ)) := by
          rw [← mul_assoc]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hL₀ h1) hL₁ (by positivity) (by positivity)
      _ ≤ _ := hcount
  have := le_of_tendsto_one_sub_mul_rpow hc hbound
  linarith

/-! ### Forwarding -/

/-- Which bits an edge carries: all the bits of node `1`, the first `p` bits of node `2` through
node `3`, and the other bits of node `2` through node `4`. -/
def yeungBits {b : Fin 5 → ℕ} (p : ℕ) (k l : Fin 5) (r : Σ j, Fin (b j)) : Prop :=
  if k = 0 then r.1 = 0
  else if k = 1 ∧ l = 2 ∨ k = 2 then r.1 = 0 ∨ (r.1 = 1 ∧ r.2.val < p)
  else r.1 = 0 ∨ (r.1 = 1 ∧ p ≤ r.2.val)

instance {b : Fin 5 → ℕ} (p : ℕ) (k l : Fin 5) : DecidablePred (yeungBits (b := b) p k l) := by
  intro r
  unfold yeungBits
  infer_instance

section Bits

variable {b : Fin 5 → ℕ} (p : ℕ) (r : Σ j, Fin (b j))

lemma yeungBits_01 : yeungBits p 0 1 r ↔ r.1 = 0 := by
  unfold yeungBits
  rw [ite_eq_left (show (0 : Fin 5) = 0 from rfl)]

lemma yeungBits_12 : yeungBits p 1 2 r ↔ r.1 = 0 ∨ (r.1 = 1 ∧ r.2.val < p) := by
  unfold yeungBits
  rw [ite_eq_right (show ¬ ((1 : Fin 5) = 0) by decide),
    ite_eq_left (show (1 : Fin 5) = 1 ∧ (2 : Fin 5) = 2 ∨ (1 : Fin 5) = 2 by decide)]

lemma yeungBits_13 : yeungBits p 1 3 r ↔ r.1 = 0 ∨ (r.1 = 1 ∧ p ≤ r.2.val) := by
  unfold yeungBits
  rw [ite_eq_right (show ¬ ((1 : Fin 5) = 0) by decide),
    ite_eq_right (show ¬ ((1 : Fin 5) = 1 ∧ (3 : Fin 5) = 2 ∨ (1 : Fin 5) = 2) by decide)]

lemma yeungBits_24 : yeungBits p 2 4 r ↔ r.1 = 0 ∨ (r.1 = 1 ∧ r.2.val < p) := by
  unfold yeungBits
  rw [ite_eq_right (show ¬ ((2 : Fin 5) = 0) by decide),
    ite_eq_left (show (2 : Fin 5) = 1 ∧ (4 : Fin 5) = 2 ∨ (2 : Fin 5) = 2 by decide)]

lemma yeungBits_34 : yeungBits p 3 4 r ↔ r.1 = 0 ∨ (r.1 = 1 ∧ p ≤ r.2.val) := by
  unfold yeungBits
  rw [ite_eq_right (show ¬ ((3 : Fin 5) = 0) by decide),
    ite_eq_right (show ¬ ((3 : Fin 5) = 1 ∧ (4 : Fin 5) = 2 ∨ (3 : Fin 5) = 2) by decide)]

end Bits

/-- **Page 16-28 of [elgamal2010].** The forwarding scheme. -/
def yeungScheme {b : Fin 5 → ℕ} {n p : ℕ} (hb : ∀ j, 2 ≤ j → b j = 0) (h₁ : b 0 + p ≤ n)
    (h₂ : b 1 ≤ 2 * p) : RoutingScheme (fun k l => yeungW k l * n) b yeungD where
  carry k l := Finset.univ.filter fun r => yeungW k l ≠ 0 ∧ yeungBits p k l r
  card_le k l := by
    by_cases hkl : yeungW k l = 0
    · simp [hkl]
    · have hw : 1 ≤ yeungW k l := Nat.one_le_iff_ne_zero.mpr hkl
      -- the bits of node `2` on the edge
      have hsrc : ∀ r : Σ j, Fin (b j), r.1 = 0 ∨ r.1 = 1 := by
        intro r
        have hall : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ 2 ≤ j := by decide
        rcases hall r.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have hi := r.2.2
          have := hb r.1 h
          omega
      have hle : ∀ I : Finset ℕ, #I ≤ p → (∀ r : Σ j, Fin (b j), r.1 = 1 →
          yeungBits p k l r → r.2.val ∈ I) →
          #(Finset.univ.filter fun r : Σ j, Fin (b j) => yeungW k l ≠ 0 ∧ yeungBits p k l r) ≤
            n := by
        intro I hI hmem
        let f : (Σ j, Fin (b j)) → ℕ ⊕ ℕ := fun r =>
          if r.1 = 0 then Sum.inl r.2.val else Sum.inr r.2.val
        have hinj : Function.Injective f := by
          rintro ⟨j, i⟩ ⟨j', i'⟩ h
          rcases hsrc ⟨j, i⟩ with hj | hj <;> rcases hsrc ⟨j', i'⟩ with hj' | hj'
          · obtain rfl : j = 0 := hj
            obtain rfl : j' = 0 := hj'
            simp only [f, ite_true, Sum.inl.injEq] at h
            rw [Fin.val_inj.mp h]
          · obtain rfl : j = 0 := hj
            obtain rfl : j' = 1 := hj'
            simp [f] at h
          · obtain rfl : j = 1 := hj
            obtain rfl : j' = 0 := hj'
            simp [f] at h
          · obtain rfl : j = 1 := hj
            obtain rfl : j' = 1 := hj'
            simp only [f, one_ne_zero, ite_false, Sum.inr.injEq] at h
            rw [Fin.val_inj.mp h]
        have hcard := Finset.card_le_card_of_injOn (s := Finset.univ.filter
          fun r : Σ j, Fin (b j) => yeungW k l ≠ 0 ∧ yeungBits p k l r)
          (t := (Finset.range (b 0)).disjSum I) f
          (fun r hr => by
            have hr' := (Finset.mem_filter.mp hr).2.2
            rcases hsrc r with h | h
            · simp only [Finset.mem_coe, f, h, ite_true]
              refine Finset.inl_mem_disjSum.mpr (Finset.mem_range.mpr ?_)
              have hi := r.2.2
              have hb0 : b r.1 = b 0 := by rw [h]
              omega
            · simp only [Finset.mem_coe, f, h, one_ne_zero, ite_false]
              exact Finset.inr_mem_disjSum.mpr (hmem r h hr')) hinj.injOn
        rw [Finset.card_disjSum, Finset.card_range] at hcard
        omega
      refine (?_ : _ ≤ n).trans (Nat.le_mul_of_pos_left _ hw)
      by_cases hc : k = 1 ∧ l = 2 ∨ k = 2
      · by_cases hk : k = 0
        · refine hle ∅ (by simp) fun r hr hp => ?_
          simp only [yeungBits, hk, ite_true] at hp
          exact absurd (hp.symm.trans hr) (by decide)
        · refine hle (Finset.range p) (by simp) fun r hr hp => ?_
          simp only [yeungBits, hk, ite_false, hc, ite_true] at hp
          rcases hp with hp | hp
          · exact absurd (hp.symm.trans hr) (by decide)
          · exact Finset.mem_range.mpr hp.2
      · by_cases hk : k = 0
        · refine hle ∅ (by simp) fun r hr hp => ?_
          simp only [yeungBits, hk, ite_true] at hp
          exact absurd (hp.symm.trans hr) (by decide)
        · refine hle (Finset.Ico p (2 * p)) (by simp; omega) fun r hr hp => ?_
          simp only [yeungBits, hk, ite_false, hc] at hp
          rcases hp with hp | hp
          · exact absurd (hp.symm.trans hr) (by decide)
          · refine Finset.mem_Ico.mpr ⟨hp.2, ?_⟩
            have hi := r.2.2
            have hb1 : b r.1 = b 1 := by rw [hr]
            omega
  forward k l r hr := by
    obtain ⟨hw, hp⟩ := (Finset.mem_filter.mp hr).2
    have hall : ∀ k l : Fin 5, yeungW k l ≠ 0 →
        (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 2) ∨ (k = 1 ∧ l = 3) ∨ (k = 2 ∧ l = 4) ∨
          (k = 3 ∧ l = 4) := by
      decide
    have hmem : ∀ a c : Fin 5, yeungW a c ≠ 0 → yeungBits p a c r →
        r ∈ Finset.univ.filter fun r : Σ j, Fin (b j) => yeungW a c ≠ 0 ∧ yeungBits p a c r :=
      fun a c h₁ h₂ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁, h₂⟩
    rcases hall k l hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ((yeungBits_01 p r).mp hp)
    · rcases (yeungBits_12 p r).mp hp with hp | hp
      · exact Or.inr ⟨0, by decide, hmem 0 1 (by decide) ((yeungBits_01 p r).mpr hp)⟩
      · exact Or.inl hp.1
    · rcases (yeungBits_13 p r).mp hp with hp | hp
      · exact Or.inr ⟨0, by decide, hmem 0 1 (by decide) ((yeungBits_01 p r).mpr hp)⟩
      · exact Or.inl hp.1
    · refine Or.inr ⟨1, by decide, hmem 1 2 (by decide) ?_⟩
      exact (yeungBits_12 p r).mpr ((yeungBits_24 p r).mp hp)
    · refine Or.inr ⟨1, by decide, hmem 1 3 (by decide) ?_⟩
      exact (yeungBits_13 p r).mpr ((yeungBits_34 p r).mp hp)
  deliver r l hl := by
    have hall : ∀ j l : Fin 5, l ∈ yeungD j →
        (j = 0 ∧ l = 2) ∨ (j = 0 ∧ l = 3) ∨ (j = 0 ∧ l = 4) ∨ (j = 1 ∧ l = 4) := by decide
    have hmem : ∀ a c : Fin 5, yeungW a c ≠ 0 → yeungBits p a c r →
        r ∈ Finset.univ.filter fun r : Σ j, Fin (b j) => yeungW a c ≠ 0 ∧ yeungBits p a c r :=
      fun a c h₁ h₂ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁, h₂⟩
    rcases hall r.1 l hl with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact ⟨1, by decide, hmem 1 2 (by decide) ((yeungBits_12 p r).mpr (Or.inl h))⟩
    · exact ⟨1, by decide, hmem 1 3 (by decide) ((yeungBits_13 p r).mpr (Or.inl h))⟩
    · exact ⟨2, by decide, hmem 2 4 (by decide) ((yeungBits_24 p r).mpr (Or.inl h))⟩
    · by_cases hi : r.2.val < p
      · exact ⟨2, by decide, hmem 2 4 (by decide) ((yeungBits_24 p r).mpr (Or.inr ⟨h, hi⟩))⟩
      · exact ⟨3, by decide, hmem 3 4 (by decide)
          ((yeungBits_34 p r).mpr (Or.inr ⟨h, not_lt.mp hi⟩))⟩

/-- **Page 16-28 of [elgamal2010].** Forwarding achieves the rate pairs with `2 R₁ + R₂ < 2`. -/
theorem yeung_isRoutingAchievable {p : ℝ × ℝ} (h₁ : 0 ≤ p.1) (h₂ : 0 ≤ p.2)
    (h₄ : 2 * p.1 + p.2 < 2) : IsRoutingAchievable yeungNet yeungD (yeungRate p) := by
  refine ⟨fun j => ?_, ?_⟩
  · have hall : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
    rcases hall j with rfl | rfl | rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
  have hgap : 0 < 2 - (2 * p.1 + p.2) := sub_pos.mpr h₄
  have hev : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ (n : ℝ) * (2 - (2 * p.1 + p.2)) :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hgap |>.eventually_ge_atTop _
  filter_upwards [hev] with n hn
  rw [yeungNet, floor_natNet]
  have hb₀ : yeungRate p 0 = p.1 := rfl
  have hb₁ : yeungRate p 1 = p.2 := rfl
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc₀ : ⌈(n : ℝ) * p.1⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hlt₀ : ((⌈(n : ℝ) * p.1⌉₊ : ℕ) : ℝ) < (n : ℝ) * p.1 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hlt₁ : ((⌈(n : ℝ) * p.2⌉₊ : ℕ) : ℝ) < (n : ℝ) * p.2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsum : 2 * ⌈(n : ℝ) * p.1⌉₊ + ⌈(n : ℝ) * p.2⌉₊ ≤ 2 * n := by
    have : ((2 * ⌈(n : ℝ) * p.1⌉₊ + ⌈(n : ℝ) * p.2⌉₊ : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  refine ⟨yeungScheme (p := n - ⌈(n : ℝ) * p.1⌉₊) (fun j hj => ?_) ?_ ?_⟩
  · have hcases : ∀ j : Fin 5, 2 ≤ j → yeungRate p j = 0 := by
      intro j hj
      have hc : ∀ j : Fin 5, 2 ≤ j → j = 2 ∨ j = 3 ∨ j = 4 := by decide
      rcases hc j hj with rfl | rfl | rfl <;> rfl
    simp [hcases j hj]
  · rw [hb₀]
    omega
  · rw [hb₁]
    omega

/-! ### The two regions -/

/-- **Page 16-28 of [elgamal2010].** The capacity region of the network, for `R₃ = R₄ = R₅ = 0`: the
pairs with `R₁ ≤ 1` and `2 R₁ + R₂ ≤ 2`. -/
theorem yeung_capacityRegion :
    closure {p : ℝ × ℝ | IsAchievable yeungNet yeungD (yeungRate p)} =
      {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ 1 ∧ 2 * p.1 + p.2 ≤ 2} := by
  refine Set.Subset.antisymm (closure_minimal (fun p hp => ?_) ?_) fun p hp => ?_
  · obtain ⟨h1, h2, h3, h4⟩ : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ 1 ∧ 2 * p.1 + p.2 ≤ 2 := by
      refine ⟨hp.1 0, hp.1 1, ?_, yeung_le hp⟩
      have hb := cut_bound_nat hp {0}
      have hs : cutSources yeungD {0} = {0} := by decide
      have hc : (∑ j ∈ ({0} : Finset (Fin 5)), ∑ k ∈ ({0} : Finset (Fin 5))ᶜ, yeungW j k) = 1 := by
        decide
      have hp0 : yeungRate p 0 = p.1 := rfl
      rw [hs, hc, Finset.sum_singleton, hp0] at hb
      simpa using hb
    exact ⟨h1, h2, h3, h4⟩
  · have hc₁ : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
    have hc₂ : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
    refine (isClosed_le continuous_const hc₁).inter ((isClosed_le continuous_const hc₂).inter
      ((isClosed_le hc₁ continuous_const).inter
        (isClosed_le (show Continuous fun p : ℝ × ℝ => 2 * p.1 + p.2 by fun_prop)
          continuous_const)))
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    refine mem_closure_of_forall_smul fun θ hθ hθ₁ => ?_
    refine (yeung_isRoutingAchievable (p := θ • p) ?_ ?_ ?_).isAchievableZE.isAchievable
    · exact mul_nonneg hθ.le h1
    · exact mul_nonneg hθ.le h2
    · change 2 * (θ * p.1) + θ * p.2 < 2
      nlinarith

set_option maxRecDepth 100000 in
/-- All the cuts of the network, by computation. -/
private lemma yeung_cuts : ∀ S : Finset (Fin 5),
    cutSources yeungD S = ∅ ∨
    (cutSources yeungD S = {0} ∧ 1 ≤ ∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k) ∨
    (cutSources yeungD S = {1} ∧ 2 ≤ ∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k) ∨
    (cutSources yeungD S = {0, 1} ∧ 2 ≤ ∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k) := by
  decide

/-- **Page 16-28 of [elgamal2010].** The cutset outer bound of the network, for
`R₃ = R₄ = R₅ = 0`: the pairs with `R₁ ≤ 1` and `R₁ + R₂ ≤ 2`. -/
theorem yeung_cutsetRegion :
    {p : ℝ × ℝ | yeungRate p ∈ cutsetRegion yeungNet yeungD} =
      {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ 1 ∧ p.1 + p.2 ≤ 2} := by
  have hcap : ∀ S : Finset (Fin 5), cutCap yeungNet.C S =
      ((∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k : ℕ) : ℝ) := fun S => cutCap_natCast yeungW S
  ext p
  constructor
  · rintro ⟨h0, hS⟩
    refine ⟨h0 0, h0 1, ?_, ?_⟩
    · have hb := hS {0}
      have hs : cutSources yeungD {0} = {0} := by decide
      have hc : (∑ j ∈ ({0} : Finset (Fin 5)), ∑ k ∈ ({0} : Finset (Fin 5))ᶜ, yeungW j k) = 1 := by
        decide
      have hp0 : yeungRate p 0 = p.1 := rfl
      rw [hcap, hs, hc, Finset.sum_singleton, hp0] at hb
      simpa using hb
    · have hb := hS {0, 1}
      have hs : cutSources yeungD {0, 1} = {0, 1} := by decide
      have hc : (∑ j ∈ ({0, 1} : Finset (Fin 5)), ∑ k ∈ ({0, 1} : Finset (Fin 5))ᶜ,
          yeungW j k) = 2 := by decide
      have hp0 : yeungRate p 0 = p.1 := rfl
      have hp1 : yeungRate p 1 = p.2 := rfl
      rw [hcap, hs, hc, Finset.sum_pair (by decide), hp0, hp1] at hb
      simpa using hb
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun j => ?_, fun S => ?_⟩
    · have hall : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
      rcases hall j with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl
    · rw [hcap]
      have hnn : (0 : ℝ) ≤ ((∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k : ℕ) : ℝ) := Nat.cast_nonneg _
      rcases yeung_cuts S with h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
      · rw [h]
        simpa using hnn
      · rw [h, Finset.sum_singleton]
        have : (1 : ℝ) ≤ ((∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k : ℕ) : ℝ) := by exact_mod_cast hc
        exact h3.trans this
      · rw [h, Finset.sum_singleton]
        have : (2 : ℝ) ≤ ((∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k : ℕ) : ℝ) := by exact_mod_cast hc
        change p.2 ≤ _
        linarith
      · rw [h, Finset.sum_pair (by decide)]
        have : (2 : ℝ) ≤ ((∑ j ∈ S, ∑ k ∈ Sᶜ, yeungW j k : ℕ) : ℝ) := by exact_mod_cast hc
        change p.1 + p.2 ≤ _
        linarith

/-- **Page 16-27 of [elgamal2010].** The cutset outer bound is loose: the rate pair `(1, 1)`
satisfies it and is not in the capacity region. -/
theorem yeung_cutset_loose :
    yeungRate (1, 1) ∈ cutsetRegion yeungNet yeungD ∧
      ((1, 1) : ℝ × ℝ) ∉ closure {p : ℝ × ℝ | IsAchievable yeungNet yeungD (yeungRate p)} := by
  constructor
  · have : ((1, 1) : ℝ × ℝ) ∈ {p : ℝ × ℝ | yeungRate p ∈ cutsetRegion yeungNet yeungD} := by
      rw [yeung_cutsetRegion]
      norm_num
    exact this
  · rw [yeung_capacityRegion]
    norm_num

end InfoTheory.ElGamalKim
