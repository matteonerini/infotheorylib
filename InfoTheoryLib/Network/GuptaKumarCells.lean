/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.GuptaKumar

/-!
# The Gupta–Kumar random network: the cells

Lemma 1 of Lecture 20 of El Gamal and Kim, on the number of sources and of routes in a cell of the
cellular time division scheme.

The positions of the nodes matter only through their cells, so `N` source-destination pairs are `N`
independent uniform pairs of cells of an `m × m` grid. A pair is served along a route that
follows the row of the source and then the column of the destination, instead of the straight line
of the notes. The probability that a route passes through a given cell is then at most `2 / m`
by an elementary count, with no torus and no geometry, and it has the order of the notes.

## Main definitions

* `gkProb E`: the probability of an event for the uniform law on a finite type.
* `gkRoute s d c`: the cell `c` is on the route from `s` to `d`.
* `gkS ω`, `gkL ω`: the numbers `S(N)` of sources and `L(N)` of routes.
* `gkSide N`: the side `⌊(N / log N)^{1/2}⌋` of the grid.
* `gkArea N`: the area of a cell, between `log N` and `4 log N`.

## Main statements

* `gkProb_count_ge`: **the Chernoff bound** for a number of successes.
* `gkProb_empty_le`, `gkProb_gkS_ge`, `gkProb_gkL_ge`: the bounds for a fixed grid.
* `gk_lemma1`: **Lemma 1**: with probability tending to one no cell is empty and
  `S(N) + L(N) < 13 (N log N)^{1/2}`.
* `gkRate_whp`: **the lower bound on the rate**: with probability tending to one, the rate of the
  cellular scheme is `Ω(N^{-1/2} (log N)^{-(ν+1)/2})`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 20
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The uniform law on a finite type -/

section Prob

variable {Ω : Type*} [Fintype Ω]

open Classical in
/-- The probability of an event, for the uniform law on a finite type. -/
def gkProb (E : Ω → Prop) : ℝ := (#{ω | E ω} : ℝ) / Fintype.card Ω

lemma gkProb_nonneg (E : Ω → Prop) : 0 ≤ gkProb E := by
  unfold gkProb
  positivity

lemma gkProb_mono {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) : gkProb E ≤ gkProb F := by
  classical
  unfold gkProb
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast card_le_card fun ω hω => by
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    exact h ω hω

lemma gkProb_or (E F : Ω → Prop) : gkProb (fun ω => E ω ∨ F ω) ≤ gkProb E + gkProb F := by
  classical
  unfold gkProb
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  norm_cast
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro ω hω
  simpa using hω

lemma gkProb_exists {ι : Type*} [Fintype ι] (E : ι → Ω → Prop) :
    gkProb (fun ω => ∃ i, E i ω) ≤ ∑ i, gkProb (E i) := by
  classical
  unfold gkProb
  rw [← sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  norm_cast
  refine (card_le_card ?_).trans card_biUnion_le
  intro ω hω
  simpa using hω

/-- **Markov's inequality.** -/
lemma gkProb_le_sum {E : Ω → Prop} {g : Ω → ℝ} (hg : ∀ ω, 0 ≤ g ω) (hE : ∀ ω, E ω → 1 ≤ g ω) :
    gkProb E ≤ (∑ ω, g ω) / Fintype.card Ω := by
  classical
  unfold gkProb
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc (#{ω | E ω} : ℝ) = ∑ _ω ∈ ({ω | E ω} : Finset Ω), (1 : ℝ) := by simp
    _ ≤ ∑ ω ∈ ({ω | E ω} : Finset Ω), g ω := sum_le_sum fun ω hω => hE ω (by simpa using hω)
    _ ≤ ∑ ω, g ω := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun ω _ _ => hg ω

end Prob

/-! ### The Chernoff bound -/

section Chernoff

variable {α : Type*} [Fintype α] [Nonempty α] (A : α → Prop) [DecidablePred A]

/-- **The Chernoff bound of page 20-38 of [elgamal2010].** Let `q` bound the probability of the
event `A`. The probability that at least `s` of `n` independent letters are in `A` is at most
`exp (n q (e^t - 1) - t s)` for all `t ≥ 0`. -/
theorem gkProb_count_ge {q : ℝ} (hq : (#{a | A a} : ℝ) / Fintype.card α ≤ q) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (s : ℝ) :
    gkProb (fun ω : Fin n → α => s ≤ (#{j | A (ω j)} : ℝ)) ≤
      exp ((n : ℝ) * q * (exp t - 1) - t * s) := by
  set w : α → ℝ := fun a => exp (t * if A a then 1 else 0) with hw
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcount : ∀ ω : Fin n → α, (#{j | A (ω j)} : ℝ) = ∑ j, if A (ω j) then (1 : ℝ) else 0 := by
    intro ω
    exact natCast_card_filter _ _
  have hprod : ∀ ω : Fin n → α, exp (t * ((#{j | A (ω j)} : ℝ) - s)) =
      exp (-(t * s)) * ∏ j, w (ω j) := by
    intro ω
    rw [hcount, hw]
    simp only
    rw [← exp_sum, ← exp_add, mul_sub, ← mul_sum]
    congr 1
    ring
  have hsum : ∑ a, w a = Fintype.card α + (#{a | A a} : ℝ) * (exp t - 1) := by
    have h₁ : ∀ a, w a = 1 + (if A a then 1 else 0) * (exp t - 1) := by
      intro a
      by_cases h : A a <;> simp [hw, h]
    simp only [h₁, sum_add_distrib, ← sum_mul]
    simp
  have hexp : 0 ≤ exp t - 1 := by linarith [one_le_exp ht]
  have hsum₂ : ∑ a, w a ≤ Fintype.card α * exp (q * (exp t - 1)) := by
    rw [hsum]
    have h₁ : (#{a | A a} : ℝ) ≤ q * Fintype.card α := (div_le_iff₀ hcard).1 hq
    have h₂ := add_one_le_exp (q * (exp t - 1))
    have h₃ : (#{a | A a} : ℝ) * (exp t - 1) ≤ q * Fintype.card α * (exp t - 1) :=
      mul_le_mul_of_nonneg_right h₁ hexp
    nlinarith
  have hw0 : 0 ≤ ∑ a, w a := sum_nonneg fun a _ => (exp_pos _).le
  refine (gkProb_le_sum (g := fun ω : Fin n → α => exp (t * ((#{j | A (ω j)} : ℝ) - s)))
    (fun ω => (exp_pos _).le) fun ω hω => ?_).trans ?_
  · exact one_le_exp (mul_nonneg ht (by linarith))
  · simp only [hprod]
    rw [← mul_sum, ← Fintype.sum_pow, Fintype.card_fun, Fintype.card_fin]
    push_cast
    have h₄ := pow_le_pow_left₀ hw0 hsum₂ n
    rw [mul_pow, ← exp_nat_mul] at h₄
    have hpos : (0 : ℝ) < (Fintype.card α : ℝ) ^ n := by positivity
    rw [div_le_iff₀ hpos]
    calc exp (-(t * s)) * (∑ a, w a) ^ n
        ≤ exp (-(t * s)) * ((Fintype.card α : ℝ) ^ n * exp (n * (q * (exp t - 1)))) :=
          mul_le_mul_of_nonneg_left h₄ (exp_pos _).le
      _ = _ := by
          rw [show (n : ℝ) * q * (exp t - 1) - t * s = n * (q * (exp t - 1)) + -(t * s) by ring,
            exp_add]
          ring

/-- The probability that no letter is in `A`. -/
theorem gkProb_forall_not {p : ℝ} (hp : p ≤ (#{a | A a} : ℝ) / Fintype.card α) (n : ℕ) :
    gkProb (fun ω : Fin n → α => ∀ j, ¬A (ω j)) ≤ exp (-((n : ℝ) * p)) := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  set w : α → ℝ := fun a => if A a then 0 else 1 with hw
  have hw0 : ∀ a, 0 ≤ w a := fun a => by
    simp only [hw]
    split_ifs <;> norm_num
  refine (gkProb_le_sum (g := fun ω : Fin n → α => ∏ j, w (ω j))
    (fun ω => prod_nonneg fun j _ => hw0 _) fun ω hω => ?_).trans ?_
  · simp [hw, hω]
  · rw [← Fintype.sum_pow, Fintype.card_fun, Fintype.card_fin]
    have hsum : ∑ a, w a = Fintype.card α - (#{a | A a} : ℝ) := by
      have h₁ : ∀ a, w a = 1 - if A a then 1 else 0 := by
        intro a
        by_cases h : A a <;> simp [hw, h]
      simp only [h₁, sum_sub_distrib]
      simp
    have hle : ∑ a, w a ≤ Fintype.card α * exp (-p) := by
      rw [hsum]
      have h₁ : p * Fintype.card α ≤ (#{a | A a} : ℝ) := (le_div_iff₀ hcard).1 hp
      have h₂ := one_sub_le_exp_neg p
      nlinarith
    have h₄ := pow_le_pow_left₀ (sum_nonneg fun a _ => hw0 a) hle n
    rw [mul_pow, ← exp_nat_mul] at h₄
    push_cast
    have hpos : (0 : ℝ) < (Fintype.card α : ℝ) ^ n := by positivity
    rw [div_le_iff₀ hpos]
    calc _ ≤ _ := h₄
      _ = _ := by
          rw [mul_comm]
          congr 2
          ring

end Chernoff

/-! ### The cells -/

section Cells

/-- The cells of an `m × m` grid. -/
abbrev GKCell (m : ℕ) := Fin m × Fin m

variable {m : ℕ}

/-- The cell `c` is on the route from `s` to `d`: the route follows the row of `s` and then the
column of `d`. -/
def gkRoute (s d c : GKCell m) : Prop :=
  (c.1 = s.1 ∧ min s.2 d.2 ≤ c.2 ∧ c.2 ≤ max s.2 d.2) ∨
    (c.2 = d.2 ∧ min s.1 d.1 ≤ c.1 ∧ c.1 ≤ max s.1 d.1)

instance (s d c : GKCell m) : Decidable (gkRoute s d c) := by
  unfold gkRoute
  infer_instance

lemma gkRoute_source (s d : GKCell m) : gkRoute s d s :=
  Or.inl ⟨rfl, min_le_left _ _, le_max_left _ _⟩

lemma gkRoute_dest (s d : GKCell m) : gkRoute s d d :=
  Or.inr ⟨rfl, min_le_right _ _, le_max_right _ _⟩

/-- The route is connected: it contains the corner cell, which is in the row of the source and in
the column of the destination. -/
lemma gkRoute_corner (s d : GKCell m) : gkRoute s d (s.1, d.2) :=
  Or.inl ⟨rfl, min_le_right _ _, le_max_right _ _⟩

/-- The number `S(N)` of sources in a cell, maximized over the cells. -/
def gkS {N : ℕ} (ω : Fin N → GKCell m × GKCell m) : ℕ :=
  univ.sup fun c : GKCell m => #{j | (ω j).1 = c}

/-- The number `L(N)` of routes through a cell, maximized over the cells. -/
def gkL {N : ℕ} (ω : Fin N → GKCell m × GKCell m) : ℕ :=
  univ.sup fun c : GKCell m => #{j | gkRoute (ω j).1 (ω j).2 c}

lemma card_pair_cell : (Fintype.card (GKCell m × GKCell m) : ℝ) = (m : ℝ) ^ 4 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

/-- The probability that the source of a pair is in a cell is `1 / m²`. -/
lemma prob_source (hm : 0 < m) (c : GKCell m) :
    (#{p : GKCell m × GKCell m | p.1 = c} : ℝ) / Fintype.card (GKCell m × GKCell m) =
      1 / (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [card_pair_cell]
  have h : (#{p : GKCell m × GKCell m | p.1 = c} : ℝ) = (m : ℝ) ^ 2 := by
    rw [natCast_card_filter, Fintype.sum_prod_type]
    simp [sq]
  rw [h]
  field_simp

/-- The probability that a route passes through a cell is at most `2 / m`. This replaces the
computation with the torus of pages 20-36 and 20-37 of [elgamal2010]. -/
lemma prob_route_le (hm : 0 < m) (c : GKCell m) :
    (#{p : GKCell m × GKCell m | gkRoute p.1 p.2 c} : ℝ) / Fintype.card (GKCell m × GKCell m) ≤
      2 / (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [card_pair_cell]
  have h₁ : (#{p : GKCell m × GKCell m | p.1.1 = c.1} : ℝ) = (m : ℝ) ^ 3 := by
    rw [natCast_card_filter]
    simp only [Fintype.sum_prod_type]
    have h : ∀ x : Fin m, (∑ _y : Fin m, ∑ _a : Fin m, ∑ _b : Fin m,
        if x = c.1 then (1 : ℝ) else 0) = if x = c.1 then (m : ℝ) ^ 3 else 0 := by
      intro x
      split_ifs
      · simp
        ring
      · simp
    simp only [h]
    simp
  have h₂ : (#{p : GKCell m × GKCell m | p.2.2 = c.2} : ℝ) = (m : ℝ) ^ 3 := by
    rw [natCast_card_filter]
    simp only [Fintype.sum_prod_type]
    simp
    ring
  have hsub : ({p : GKCell m × GKCell m | gkRoute p.1 p.2 c} : Finset _) ⊆
      ({p | p.1.1 = c.1} : Finset (GKCell m × GKCell m)) ∪
        ({p | p.2.2 = c.2} : Finset (GKCell m × GKCell m)) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_union] at hp ⊢
    rcases hp with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.1.symm
  have hle : (#{p : GKCell m × GKCell m | gkRoute p.1 p.2 c} : ℝ) ≤ 2 * (m : ℝ) ^ 3 := by
    have h₃ := (card_le_card hsub).trans (card_union_le _ _)
    have h₄ : (#{p : GKCell m × GKCell m | gkRoute p.1 p.2 c} : ℝ) ≤
        (#{p : GKCell m × GKCell m | p.1.1 = c.1} : ℝ) +
          (#{p : GKCell m × GKCell m | p.2.2 = c.2} : ℝ) := by
      exact_mod_cast h₃
    rw [h₁, h₂] at h₄
    linarith
  rw [div_le_div_iff₀ (by positivity) hm']
  nlinarith [pow_pos hm' 4]

/-- **Page 20-26 of [elgamal2010]: a cell with no source.** -/
theorem gkProb_empty_le (hm : 0 < m) (N : ℕ) :
    gkProb (fun ω : Fin N → GKCell m × GKCell m => ∃ c : GKCell m, ∀ j, ¬(ω j).1 = c) ≤
      (m : ℝ) ^ 2 * exp (-((N : ℝ) * (1 / (m : ℝ) ^ 2))) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine (gkProb_exists _).trans ?_
  calc _ ≤ ∑ _c : GKCell m, exp (-((N : ℝ) * (1 / (m : ℝ) ^ 2))) := sum_le_sum fun c _ =>
        gkProb_forall_not (fun p : GKCell m × GKCell m => p.1 = c) (prob_source hm c).ge N
    _ = _ := by
        simp [sq]

/-- **Page 20-36 of [elgamal2010]: the number of sources in a cell.** -/
theorem gkProb_gkS_ge (hm : 0 < m) (N : ℕ) (s : ℝ) :
    gkProb (fun ω : Fin N → GKCell m × GKCell m => s ≤ (gkS ω : ℝ)) ≤
      (m : ℝ) ^ 2 * exp ((N : ℝ) * (1 / (m : ℝ) ^ 2) * (exp 1 - 1) - s) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hsub : ∀ ω : Fin N → GKCell m × GKCell m, s ≤ (gkS ω : ℝ) →
      ∃ c : GKCell m, s ≤ (#{j | (ω j).1 = c} : ℝ) := by
    intro ω hω
    obtain ⟨c, _, hc⟩ := exists_mem_eq_sup univ univ_nonempty
      fun c : GKCell m => #{j | (ω j).1 = c}
    refine ⟨c, ?_⟩
    rw [← hc]
    exact hω
  refine (gkProb_mono hsub).trans ((gkProb_exists _).trans ?_)
  calc _ ≤ ∑ _c : GKCell m, exp ((N : ℝ) * (1 / (m : ℝ) ^ 2) * (exp 1 - 1) - s) :=
        sum_le_sum fun c _ => by
          have := gkProb_count_ge (fun p : GKCell m × GKCell m => p.1 = c)
            (prob_source hm c).le N (t := 1) zero_le_one s
          simpa using this
    _ = _ := by
        simp [sq]

/-- **Page 20-38 of [elgamal2010]: the number of routes through a cell.** -/
theorem gkProb_gkL_ge (hm : 0 < m) (N : ℕ) (s : ℝ) :
    gkProb (fun ω : Fin N → GKCell m × GKCell m => s ≤ (gkL ω : ℝ)) ≤
      (m : ℝ) ^ 2 * exp ((N : ℝ) * (2 / (m : ℝ)) * (exp 1 - 1) - s) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hsub : ∀ ω : Fin N → GKCell m × GKCell m, s ≤ (gkL ω : ℝ) →
      ∃ c : GKCell m, s ≤ (#{j | gkRoute (ω j).1 (ω j).2 c} : ℝ) := by
    intro ω hω
    obtain ⟨c, _, hc⟩ := exists_mem_eq_sup univ univ_nonempty
      fun c : GKCell m => #{j | gkRoute (ω j).1 (ω j).2 c}
    refine ⟨c, ?_⟩
    rw [← hc]
    exact hω
  refine (gkProb_mono hsub).trans ((gkProb_exists _).trans ?_)
  calc _ ≤ ∑ _c : GKCell m, exp ((N : ℝ) * (2 / (m : ℝ)) * (exp 1 - 1) - s) :=
        sum_le_sum fun c _ => by
          have := gkProb_count_ge (fun p : GKCell m × GKCell m => gkRoute p.1 p.2 c)
            (prob_route_le hm c) N (t := 1) zero_le_one s
          simpa using this
    _ = _ := by
        simp [sq]

end Cells

/-! ### Lemma 1 -/

section Lemma1

/-- The side of the grid: the cells have area about `log N`. -/
def gkSide (N : ℕ) : ℕ := ⌊√((N : ℝ) / log N)⌋₊

/-- The area of a cell, in a square of area `N`. It is between `log N` and `4 log N`. -/
def gkArea (N : ℕ) : ℝ := (N : ℝ) / (gkSide N : ℝ) ^ 2

/-- The size of the grid. -/
lemma gkSide_facts {N : ℕ} (hN : 3 ≤ N) :
    0 < gkSide N ∧ 1 ≤ log (N : ℝ) ∧ ((gkSide N : ℝ) ^ 2 ≤ (N : ℝ) / log N) ∧
      (N : ℝ) / log N ≤ 4 * (gkSide N : ℝ) ^ 2 := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ log (N : ℝ) := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  have hLN : log (N : ℝ) ≤ N := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hX : 1 ≤ (N : ℝ) / log N := (one_le_div (by linarith)).2 hLN
  set x := √((N : ℝ) / log N) with hx
  have hx1 : 1 ≤ x := one_le_sqrt.2 hX
  have hxx : x ^ 2 = (N : ℝ) / log N := sq_sqrt (by linarith)
  have hm : 0 < ⌊x⌋₊ := Nat.floor_pos.2 hx1
  have hm' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hm
  have h₁ : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h₂ : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  refine ⟨hm, hL, ?_, ?_⟩
  · rw [← hxx]
    exact pow_le_pow_left₀ (by positivity) h₁ 2
  · rw [← hxx]
    have : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith
    calc x ^ 2 ≤ (2 * (⌊x⌋₊ : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
      _ = 4 * (⌊x⌋₊ : ℝ) ^ 2 := by ring

/-- **Lemma 1 of Lecture 20 of [elgamal2010], with routes along the rows and columns.** With
probability tending to one, no cell is empty and `S(N) + L(N) < 13 (N log N)^{1/2}`. -/
theorem gk_lemma1 :
    Tendsto (fun N : ℕ => gkProb (fun ω : Fin N → GKCell (gkSide N) × GKCell (gkSide N) =>
      (∃ c : GKCell (gkSide N), ∀ j, ¬(ω j).1 = c) ∨
        13 * ((N : ℝ) * log N) ^ (1 / 2 : ℝ) ≤ (gkS ω : ℝ) + gkL ω)) atTop (𝓝 0) := by
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => 3 / log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogN
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => gkProb_nonneg _) ?_
  filter_upwards [eventually_ge_atTop 58564] with N hN
  obtain ⟨hm, hL, hmle, hmge⟩ := gkSide_facts (N := N) (by omega)
  set m := gkSide N with hmd
  set L := log (N : ℝ) with hLd
  have hN' : (58564 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < L := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set x := ((N : ℝ) * L) ^ (1 / 2 : ℝ) with hx
  have hx' : x = √((N : ℝ) * L) := (sqrt_eq_rpow _).symm
  have hxx : x ^ 2 = (N : ℝ) * L := by
    rw [hx', sq_sqrt (by positivity)]
  have hx0 : 0 ≤ x := by
    rw [hx']
    exact sqrt_nonneg _
  have hexp : exp 1 - 1 ≤ 2 := by linarith [exp_one_lt_d9]
  have hexp0 : 0 ≤ exp 1 - 1 := by linarith [one_le_exp (zero_le_one' ℝ)]
  -- the common bound
  have hcommon : ∀ y : ℝ, L ≤ y → (m : ℝ) ^ 2 * exp (-y) ≤ 1 / L := by
    intro y hy
    have h₁ : exp (-y) ≤ 1 / N := by
      calc exp (-y) ≤ exp (-L) := exp_le_exp.2 (by linarith)
        _ = 1 / N := by rw [exp_neg, hLd, exp_log hN0, one_div]
    calc (m : ℝ) ^ 2 * exp (-y) ≤ ((N : ℝ) / L) * (1 / N) :=
          mul_le_mul hmle h₁ (exp_pos _).le (by positivity)
      _ = 1 / L := by
          field_simp
  have hNm : L ≤ (N : ℝ) * (1 / (m : ℝ) ^ 2) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hL0] at hmle
    linarith
  have hNm₂ : (N : ℝ) * (1 / (m : ℝ) ^ 2) ≤ 4 * L := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hL0] at hmge
    linarith
  have hNm₃ : L ≤ (N : ℝ) / m := by
    rw [le_div_iff₀ hm0]
    rw [le_div_iff₀ hL0] at hmle
    nlinarith
  have hNm₄ : (N : ℝ) / m ≤ 2 * x := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).1 ?_
    have : ((N : ℝ) / m) ^ 2 = N * ((N : ℝ) * (1 / (m : ℝ) ^ 2)) := by
      rw [div_pow, mul_one_div, sq, mul_div_assoc]
    rw [this, mul_pow, hxx]
    nlinarith
  -- the logarithm against the square root
  have hLx : 11 * L ≤ x := by
    have hs : (242 : ℝ) ≤ √(N : ℝ) := by
      rw [le_sqrt' (by norm_num)]
      linarith
    have hss : √(N : ℝ) * √(N : ℝ) = N := mul_self_sqrt hN0.le
    have hlogs : L = 2 * log √(N : ℝ) := by
      rw [hLd, log_sqrt hN0.le]
      ring
    have h₁ := log_le_sub_one_of_pos (show 0 < √(N : ℝ) by linarith)
    have h₂ : 121 * L ≤ N := by nlinarith
    refine (sq_le_sq₀ (by positivity) hx0).1 ?_
    rw [hxx]
    nlinarith
  -- the three events
  have hE₁ := (gkProb_empty_le (m := m) hm N).trans (hcommon _ hNm)
  have hE₂ : gkProb (fun ω : Fin N → GKCell m × GKCell m => 11 * L ≤ (gkS ω : ℝ)) ≤ 1 / L := by
    refine (gkProb_gkS_ge hm N _).trans ?_
    have := hcommon (-((N : ℝ) * (1 / (m : ℝ) ^ 2) * (exp 1 - 1) - 11 * L)) (by
      have : (N : ℝ) * (1 / (m : ℝ) ^ 2) * (exp 1 - 1) ≤ 4 * L * 2 :=
        mul_le_mul hNm₂ hexp hexp0 (by positivity)
      linarith)
    rwa [neg_neg] at this
  have hE₃ : gkProb (fun ω : Fin N → GKCell m × GKCell m => 12 * x ≤ (gkL ω : ℝ)) ≤ 1 / L := by
    refine (gkProb_gkL_ge hm N _).trans ?_
    have := hcommon (-((N : ℝ) * (2 / (m : ℝ)) * (exp 1 - 1) - 12 * x)) (by
      have e : (N : ℝ) * (2 / (m : ℝ)) = 2 * ((N : ℝ) / m) := by
        field_simp
      have : (N : ℝ) * (2 / (m : ℝ)) * (exp 1 - 1) ≤ 2 * ((N : ℝ) / m) * 2 := by
        rw [e]
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
      linarith)
    rwa [neg_neg] at this
  have hsplit : ∀ ω : Fin N → GKCell m × GKCell m,
      ((∃ c : GKCell m, ∀ j, ¬(ω j).1 = c) ∨ 13 * x ≤ (gkS ω : ℝ) + gkL ω) →
      (∃ c : GKCell m, ∀ j, ¬(ω j).1 = c) ∨ (11 * L ≤ (gkS ω : ℝ) ∨ 12 * x ≤ (gkL ω : ℝ)) := by
    intro ω hω
    refine hω.imp id fun h => ?_
    by_contra hcon
    push Not at hcon
    linarith [hcon.1, hcon.2]
  refine (gkProb_mono hsplit).trans ((gkProb_or _ _).trans ?_)
  have h₂ := gkProb_or (fun ω : Fin N → GKCell m × GKCell m => 11 * L ≤ (gkS ω : ℝ))
    fun ω => 12 * x ≤ (gkL ω : ℝ)
  have e : 3 / L = 1 / L + (1 / L + 1 / L) := by ring
  rw [e]
  exact add_le_add hE₁ (h₂.trans (add_le_add hE₂ hE₃))

/-- **The lower bound of Theorem 1 of page 20-21 of [elgamal2010], at the level of the rates.** With
probability tending to one, the rate of the cellular scheme, with `S(N) + L(N)` node-blocks in a
cell-block and cells of area `gkArea N`, is at least `c' N^{-1/2} (log N)^{-(ν+1)/2}`. -/
theorem gkRate_whp {ν P : ℝ} (hν : 2 < ν) (hP : 0 < P) :
    ∃ c' > 0, Tendsto (fun N : ℕ =>
      gkProb (fun ω : Fin N → GKCell (gkSide N) × GKCell (gkSide N) =>
        gkRate ν P (gkArea N) ((gkS ω : ℝ) + gkL ω) <
          c' * ((N : ℝ) ^ (-(1 / 2) : ℝ) * (log N) ^ (-((ν + 1) / 2))))) atTop (𝓝 0) := by
  obtain ⟨c', hc', h⟩ := gkRate_ge hν hP (c := 13) (by norm_num)
  refine ⟨c', hc', tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds gk_lemma1
    (Eventually.of_forall fun _ => gkProb_nonneg _) ?_⟩
  filter_upwards [h, eventually_ge_atTop 3] with N hN hN3
  refine gkProb_mono fun ω hω => ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hlt⟩ := hcon
  have hS : 1 ≤ gkS ω := by
    let j₀ : Fin N := ⟨0, by omega⟩
    refine le_trans ?_ (le_sup (f := fun c : GKCell (gkSide N) => #{j | (ω j).1 = c})
      (mem_univ (ω j₀).1))
    exact card_pos.2 ⟨j₀, by simp⟩
  have hS' : (1 : ℝ) ≤ gkS ω := by exact_mod_cast hS
  have hL0 : (0 : ℝ) ≤ gkL ω := Nat.cast_nonneg _
  obtain ⟨hm, hL, hmle, hmge⟩ := gkSide_facts hN3
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL₀ : 0 < log (N : ℝ) := by linarith
  have hm0 : (0 : ℝ) < gkSide N := by exact_mod_cast hm
  have hA₁ : log (N : ℝ) ≤ gkArea N := by
    rw [gkArea, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hL₀] at hmle
    linarith
  have hA₂ : gkArea N ≤ 4 * log (N : ℝ) := by
    rw [gkArea, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hL₀] at hmge
    linarith
  exact absurd hω (not_lt.2 (hN _ _ hA₁ hA₂ (by linarith) hlt.le))

end Lemma1

end InfoTheory
