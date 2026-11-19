/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Networking.AsyncDecoder

/-!
# The error of the decoder for the asynchronous multiple-access channel

The union bound over the hypotheses of the decoder of Theorem 2 of Lecture 24 of El Gamal and Kim,
for fixed true messages and delays, averaged over the random tables.

## Main definitions

* `asyncMGF r l`: the expectation of `r^{-l}` at one slot.
* `asyncE`: the expectation over the tables and the outputs.

## Main statements

* `macInfo₁_eq_sum_log`, `macInfo₂_eq_sum_log`, `macInfo₁₂_eq_sum_log`: the mutual informations as
  expected log densities.
* `exists_asyncMGF_le`: the Chernoff exponent of a density.
* `asyncE_fail_le`: the bound for the true entries.
* `card_fresh_fiber_le`: the number of hypotheses with a given set of fresh sub-messages.
* `async_exponent_le`: the exponent of a pattern of errors.
* `asyncE_decA_le`: the bound for the error of the decoder.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset Real

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]
  {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} {W : α₁ × α₂ → β → ℝ} {n k b V₁ V₂ M₁ M₂ : ℕ}

/-! ### The mutual informations as expected log densities -/

lemma macInfo₁_eq_sum_log (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁ p₁ p₂ W = ∑ x₁, ∑ x₂, ∑ y,
      p₁ x₁ * (p₂ x₂ * (W (x₁, x₂) y * log (macRatio₁ p₁ W x₁ x₂ y))) := by
  rw [macInfo₁_eq_sum hp₁ hp₂ hW]
  have h : ∀ x₂, p₂ x₂ * mutualInfoOf p₁ (fun a => W (a, x₂)) =
      ∑ x₁, ∑ y, p₁ x₁ * (p₂ x₂ * (W (x₁, x₂) y * log (macRatio₁ p₁ W x₁ x₂ y))) := by
    intro x₂
    rw [mutualInfoOf_eq_sum_log hp₁ fun a => hW (a, x₂), mul_sum]
    refine sum_congr rfl fun x₁ _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun y _ => by ring
  simp only [h]
  exact sum_comm

lemma macInfo₂_eq_sum_log (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₂ p₁ p₂ W = ∑ x₁, ∑ x₂, ∑ y,
      p₁ x₁ * (p₂ x₂ * (W (x₁, x₂) y * log (macRatio₂ p₂ W x₁ x₂ y))) := by
  rw [macInfo₂_eq_sum hp₁ hp₂ hW]
  refine sum_congr rfl fun x₁ _ => ?_
  rw [mutualInfoOf_eq_sum_log hp₂ fun b => hW (x₁, b), mul_sum]
  refine sum_congr rfl fun x₂ _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

lemma macInfo₁₂_eq_sum_log (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁₂ p₁ p₂ W = ∑ x₁, ∑ x₂, ∑ y,
      p₁ x₁ * (p₂ x₂ * (W (x₁, x₂) y * log (macRatio₁₂ p₁ p₂ W x₁ x₂ y))) := by
  have h : macInfo₁₂ p₁ p₂ W = mutualInfoOf (prodDist p₁ p₂) W := rfl
  rw [h, mutualInfoOf_eq_sum_log (hp₁.prodDist hp₂) hW, Fintype.sum_prod_type]
  refine sum_congr rfl fun x₁ _ => sum_congr rfl fun x₂ _ => sum_congr rfl fun y _ => ?_
  simp only [prodDist]
  ring

/-- The expectation of `r^{-l}` at one slot. -/
def asyncMGF (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (r : α₁ → α₂ → β → ℝ) (l : ℝ) : ℝ :=
  ∑ x₁, p₁ x₁ * ∑ x₂, p₂ x₂ * ∑ y, W (x₁, x₂) y * exp (-(l * log (r x₁ x₂ y)))

lemma asyncMGF_nonneg (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (r : α₁ → α₂ → β → ℝ)
    (l : ℝ) : 0 ≤ asyncMGF p₁ p₂ W r l :=
  sum_nonneg fun _ _ => mul_nonneg (hp₁.nonneg _) (sum_nonneg fun _ _ =>
    mul_nonneg (hp₂.nonneg _) (sum_nonneg fun _ _ => mul_nonneg ((hW _).nonneg _) (exp_pos _).le))

/-- **The Chernoff exponent of a density** whose expected log is `I`. -/
theorem exists_asyncMGF_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W)
    (r : α₁ → α₂ → β → ℝ) {I c : ℝ} (hI : I = ∑ x₁, ∑ x₂, ∑ y,
      p₁ x₁ * (p₂ x₂ * (W (x₁, x₂) y * log (r x₁ x₂ y)))) (hc : 0 < c) :
    ∃ l > 0, asyncMGF p₁ p₂ W r l ≤ exp (-(l * (I - c))) := by
  set μ : α₁ × α₂ × β → ℝ := fun z => p₁ z.1 * (p₂ z.2.1 * W (z.1, z.2.1) z.2.2) with hμ
  have hsum : ∀ f : α₁ → α₂ → β → ℝ, ∑ z, μ z * f z.1 z.2.1 z.2.2 =
      ∑ x₁, ∑ x₂, ∑ y, p₁ x₁ * (p₂ x₂ * (W (x₁, x₂) y * f x₁ x₂ y)) := by
    intro f
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun x₁ _ => ?_
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun x₂ _ => sum_congr rfl fun y _ => by simp only [hμ]; ring
  have hμp : IsPMF μ := by
    refine ⟨fun z => mul_nonneg (hp₁.nonneg _) (mul_nonneg (hp₂.nonneg _) ((hW _).nonneg _)), ?_⟩
    have h := hsum fun _ _ _ => 1
    simp only [mul_one] at h
    rw [h]
    simp only [← mul_sum, (hW _).sum_eq_one, mul_one, hp₂.sum_eq_one, hp₁.sum_eq_one]
  obtain ⟨l, hl, hle⟩ := exists_chernoff hμp (fun z => log (r z.1 z.2.1 z.2.2)) hc
  refine ⟨l, hl, ?_⟩
  have h1 := hsum fun x₁ x₂ y => log (r x₁ x₂ y)
  have h2 := hsum fun x₁ x₂ y => exp (-(l * log (r x₁ x₂ y)))
  rw [h1, ← hI, h2] at hle
  refine le_trans (le_of_eq ?_) hle
  unfold asyncMGF
  simp only [mul_sum]

/-! ### The expectation over the tables and the outputs -/

/-- The expectation of `f` over the tables and the outputs, for the true entries `a` and `b`. -/
def asyncE (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) {L₁ L₂ T : Type*} [Fintype L₁]
    [Fintype L₂] [Fintype T] [DecidableEq L₁] [DecidableEq L₂] [DecidableEq T] (a : T → L₁)
      (b : T → L₂) (f : (L₁ → α₁) → (L₂ → α₂) → (T → β) → ℝ) :
    ℝ :=
  ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
    (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) * f τ₁ τ₂ y

section Expect

variable {L₁ L₂ T : Type*} [Fintype L₁] [Fintype L₂] [Fintype T] [DecidableEq L₁] [DecidableEq L₂]
  [DecidableEq T]

lemma asyncE_mono (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (a : T → L₁) (b : T → L₂)
    {f g : (L₁ → α₁) → (L₂ → α₂) → (T → β) → ℝ} (h : ∀ τ₁ τ₂ y, f τ₁ τ₂ y ≤ g τ₁ τ₂ y) :
    asyncE p₁ p₂ W a b f ≤ asyncE p₁ p₂ W a b g :=
  sum_le_sum fun τ₁ _ => mul_le_mul_of_nonneg_left
    (sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left
      (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h τ₁ τ₂ y)
        (prod_nonneg fun _ _ => (hW _).nonneg _)) (tableLaw_nonneg hp₂ τ₂))
    (tableLaw_nonneg hp₁ τ₁)

lemma asyncE_add (a : T → L₁) (b : T → L₂) (f g : (L₁ → α₁) → (L₂ → α₂) → (T → β) → ℝ) :
    asyncE p₁ p₂ W a b (fun τ₁ τ₂ y => f τ₁ τ₂ y + g τ₁ τ₂ y) =
      asyncE p₁ p₂ W a b f + asyncE p₁ p₂ W a b g := by
  unfold asyncE
  rw [← sum_add_distrib]
  refine sum_congr rfl fun τ₁ _ => ?_
  rw [← mul_add]
  congr 1
  rw [← sum_add_distrib]
  refine sum_congr rfl fun τ₂ _ => ?_
  rw [← mul_add]
  congr 1
  rw [← sum_add_distrib]
  exact sum_congr rfl fun y _ => by ring

lemma asyncE_sum {ι : Type*} (s : Finset ι) (a : T → L₁) (b : T → L₂)
    (f : ι → (L₁ → α₁) → (L₂ → α₂) → (T → β) → ℝ) :
    asyncE p₁ p₂ W a b (fun τ₁ τ₂ y => ∑ i ∈ s, f i τ₁ τ₂ y) =
      ∑ i ∈ s, asyncE p₁ p₂ W a b (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [asyncE]
  | insert i s hi ih =>
    simp only [sum_insert hi]
    rw [asyncE_add, ih]

end Expect

/-! ### The true hypothesis -/

/-- **The bound for the true entries.** The product of the densities over a group `G` of the test
set falls below `e^{|G| I - D}` with probability at most `e^{-l D / 2}`, if the Chernoff exponent of
the density at slope `l` is `I - c` and `n c ≤ D / 2`. -/
theorem asyncE_fail_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (hk : 0 < k) {D : ℝ}
    (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂)
    (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂) (d₁ d₂ : Fin n) {G : Finset (Fin (2 * n - 1))}
    (hG : G ⊆ asyncTest k d₁ d₂) (r : α₁ → α₂ → β → ℝ)
    (hr : ∀ x₁ x₂ y, 0 < p₁ x₁ → 0 < p₂ x₂ → 0 < W (x₁, x₂) y → 0 < r x₁ x₂ y) {l I c : ℝ}
    (hl : 0 < l) (hM : asyncMGF p₁ p₂ W r l ≤ exp (-(l * (I - c)))) (hc : 0 ≤ c)
    (hcD : n * c ≤ D / 2) (f : (Fin n × Fin V₁ → α₁) → (Fin n × Fin V₂ → α₂) →
      (Fin (2 * n - 1) → β) → ℝ)
    (hf : ∀ τ₁ τ₂ y, f τ₁ τ₂ y ≤ (open Classical in
      if ∏ t ∈ G, r (τ₁ (asyncTrue k b sub₁ m₁ d₁ t)) (τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t) <
        exp (G.card * I - D) then 1 else 0)) :
    asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂) f ≤ exp (-(l * D / 2)) :=
      by
  classical
  have hcard : G.card ≤ n := by
    have hinj : Set.InjOn (asyncPos d₁) (G : Finset _) := fun t ht t' ht' he =>
      asyncPos_injOn_test hk d₁ (hG (by exact_mod_cast ht)) (hG (by exact_mod_cast ht')) he
    have := card_le_card_of_injOn (s := G) (t := univ) (asyncPos d₁) (fun _ _ => mem_univ _) hinj
    simpa using this
  have hmain := sum_tables_fail_le hp₁ hp₂ hW (asyncTrue k b sub₁ m₁ d₁)
    (asyncTrue k b sub₂ m₂ d₂) (asyncTrue_injOn hk sub₁ m₁ d₁ d₁ d₂ G hG)
    (asyncTrue_injOn hk sub₂ m₂ d₂ d₁ d₂ G hG) r hr hl.le (G.card * I - D)
  have h1 : exp (l * (G.card * I - D)) * (∑ x₁, p₁ x₁ * ∑ x₂, p₂ x₂ * ∑ y, W (x₁, x₂) y *
      exp (-(l * log (r x₁ x₂ y)))) ^ G.card ≤ exp (-(l * D / 2)) := by
    have h2 : (∑ x₁, p₁ x₁ * ∑ x₂, p₂ x₂ * ∑ y, W (x₁, x₂) y *
        exp (-(l * log (r x₁ x₂ y)))) ^ G.card ≤ exp (-(l * (I - c))) ^ G.card :=
      pow_le_pow_left₀ (asyncMGF_nonneg hp₁ hp₂ hW r l) hM _
    have h3 : exp (-(l * (I - c))) ^ G.card = exp (G.card * (-(l * (I - c)))) :=
      (exp_natCast_mul _ _).symm
    rw [h3] at h2
    calc _ ≤ exp (l * (G.card * I - D)) * exp (G.card * (-(l * (I - c)))) :=
          mul_le_mul_of_nonneg_left h2 (exp_pos _).le
      _ = exp (l * (G.card * c - D)) := by
          rw [← exp_add]
          congr 1
          ring
      _ ≤ _ := by
          refine exp_le_exp.2 ?_
          have h4 : (G.card : ℝ) * c ≤ n * c :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc
          nlinarith
  refine le_trans ?_ (hmain.trans h1)
  refine asyncE_mono hp₁ hp₂ hW _ _ fun τ₁ τ₂ y => (hf τ₁ τ₂ y).trans ?_
  split_ifs <;> exact le_rfl

/-! ### Counting the hypotheses -/

/-- The segments of `D` on which the sub-messages `v` are fresh. -/
def asyncFresh {V : ℕ} (D : Finset (Fin (b + 3))) (Th : Fin (b + 3) → Finset (Fin V))
    (v : Fin (b + 3) → Fin V) : Finset (Fin (b + 3)) :=
  D.filter fun j => v j ∉ Th j

lemma card_asyncThree_le {M V : ℕ} (sub : Fin M → Fin (b + 3) → Fin V) (m : Fin 3 → Fin M)
    (j : Fin (b + 3)) : (asyncThree sub m j).card ≤ 3 := by
  classical
  unfold asyncThree
  exact card_image_le.trans (by simp)

/-- **The number of hypotheses with a given set of fresh sub-messages.** A fresh segment has `V`
choices, and any other one has at most `4`: its value is `0` or one of the three sent values. -/
theorem card_fresh_fiber_le {V : ℕ} [NeZero V] (D J : Finset (Fin (b + 3)))
    (Th : Fin (b + 3) → Finset (Fin V)) (hTh : ∀ j, (Th j).card ≤ 3) :
    ((asyncHyp D).filter fun v => asyncFresh D Th v = J).card ≤ V ^ J.card * 4 ^ (b + 3) := by
  classical
  set s : Fin (b + 3) → Finset (Fin V) := fun j => if j ∈ J then univ else insert 0 (Th j) with hs
  have hsub : (asyncHyp D).filter (fun v => asyncFresh D Th v = J) ⊆ Fintype.piFinset s := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
    simp only [asyncHyp, mem_filter, mem_univ, true_and] at hv1
    rw [Fintype.mem_piFinset]
    intro j
    simp only [hs]
    split_ifs with hj
    · exact mem_univ _
    · by_cases hjD : j ∈ D
      · have : v j ∈ Th j := by
          by_contra hne
          apply hj
          rw [← hv2]
          exact mem_filter.2 ⟨hjD, hne⟩
        exact mem_insert_of_mem this
      · rw [hv1 j hjD]
        exact mem_insert_self _ _
  refine (card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  have hle : ∀ j, (s j).card ≤ if j ∈ J then V else 4 := by
    intro j
    simp only [hs]
    split_ifs
    · simp
    · exact (card_insert_le _ _).trans (by have := hTh j; omega)
  calc ∏ j, (s j).card ≤ ∏ j, (if j ∈ J then V else 4) := prod_le_prod fun j _ => hle j
    _ = V ^ J.card * 4 ^ (univ.filter fun j => j ∉ J).card := by
        rw [prod_ite, prod_const, prod_const]
        simp
    _ ≤ V ^ J.card * 4 ^ (b + 3) := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) ?_)
        calc (univ.filter fun j => j ∉ J).card ≤ (univ : Finset (Fin (b + 3))).card :=
              card_le_card (filter_subset _ _)
          _ = b + 3 := by simp

/-- **The exponent of a pattern of errors.** The numbers of slots of the three groups pay for the
sub-messages of the wrong segments. -/
theorem async_exponent_le {K a a' c₂ c₃ c₄ r₁ r₂ I₁ I₂ I₁₂ γ : ℝ} (hK : 0 ≤ K) (ha1 : a = 0 ∨ 1 ≤ a)
    (ha1' : a' = 0 ∨ 1 ≤ a') (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) (hr₁ : 0 ≤ r₁)
    (hr₂ : 0 ≤ r₂) (hγ : 0 < γ) (h₁ : a * K ≤ c₂ + c₄) (h₂ : a' * K ≤ c₃ + c₄)
    (ha0 : a = 0 → c₂ = 0 ∧ c₄ = 0) (ha0' : a' = 0 → c₃ = 0 ∧ c₄ = 0)
    (hA : a ≠ 0 → r₁ + γ ≤ I₁) (hB : a' ≠ 0 → r₂ + γ ≤ I₂)
    (hAB : a ≠ 0 → a' ≠ 0 → r₁ + r₂ + γ ≤ I₁₂) (hne : a ≠ 0 ∨ a' ≠ 0) :
    a * K * r₁ + a' * K * r₂ - (c₂ * I₁ + c₃ * I₂ + c₄ * I₁₂) ≤ -(γ * K) := by
  have e1 : a * K * r₁ ≤ (c₂ + c₄) * r₁ := mul_le_mul_of_nonneg_right h₁ hr₁
  have e2 : a' * K * r₂ ≤ (c₃ + c₄) * r₂ := mul_le_mul_of_nonneg_right h₂ hr₂
  by_cases ha : a = 0
  · have hb : a' ≠ 0 := by
      rcases hne with h | h
      · exact absurd ha h
      · exact h
    obtain ⟨h3, h4⟩ := ha0 ha
    subst h3 h4
    have hb1 : 1 ≤ a' := by
      rcases ha1' with h | h
      · exact absurd h hb
      · exact h
    have h5 : K ≤ c₃ := by nlinarith
    have h6 := hB hb
    rw [ha]
    nlinarith
  · have ha2 : 1 ≤ a := by
      rcases ha1 with h | h
      · exact absurd h ha
      · exact h
    have h3 := hA ha
    by_cases hb : a' = 0
    · obtain ⟨h4, h5⟩ := ha0' hb
      subst h4 h5
      have h6 : K ≤ c₂ := by nlinarith
      rw [hb]
      nlinarith
    · have h4 := hB hb
      have h5 := hAB ha hb
      have h6 : K ≤ c₂ + c₄ := by nlinarith
      nlinarith [mul_nonneg hc₂ hγ.le, mul_nonneg hc₃ hγ.le, mul_nonneg hc₄ hγ.le]

/-- A sum of a function of `g` over `s`, grouped by the values of `g`. -/
lemma sum_comp_fiber {X Y : Type*} [Fintype Y] [DecidableEq Y] (s : Finset X) (g : X → Y)
    (f : Y → ℝ) : ∑ x ∈ s, f (g x) = ∑ y, ((s.filter fun x => g x = y).card : ℝ) * f y := by
  classical
  rw [← sum_fiberwise s g]
  refine sum_congr rfl fun y _ => ?_
  have : ∀ x ∈ s.filter fun x => g x = y, f (g x) = f y := fun x hx => by
    rw [(mem_filter.1 hx).2]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]

/-- The two groups of slots with sender `A` in `J` contain the whole segments of `J`. -/
lemma mul_le_card_groups {T S : Type*} [DecidableEq S] (Θ : Finset T) (f g : T → S)
    (J J' : Finset S) {k : ℕ} (h : ∀ j ∈ J, k ≤ (Θ.filter fun t => f t = j).card) :
    J.card * k ≤ (Θ.filter fun t => f t ∈ J ∧ g t ∉ J').card +
      (Θ.filter fun t => f t ∈ J ∧ g t ∈ J').card := by
  classical
  have h1 : (Θ.filter fun t => f t ∈ J).card = (Θ.filter fun t => f t ∈ J ∧ g t ∉ J').card +
      (Θ.filter fun t => f t ∈ J ∧ g t ∈ J').card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext t
      simp only [mem_filter, mem_union]
      tauto
    · exact disjoint_left.2 fun t h h' => (mem_filter.1 h).2.2 (mem_filter.1 h').2.2
  have h2 := card_eq_sum_card_fiberwise (f := f) (s := Θ.filter fun t => f t ∈ J) (t := J)
    (fun t ht => (mem_filter.1 ht).2)
  rw [← h1, h2]
  calc J.card * k = ∑ _j ∈ J, k := by simp
    _ ≤ _ := sum_le_sum fun j hj => by
      refine (h j hj).trans (card_le_card fun t ht => ?_)
      obtain ⟨h2, h3⟩ := mem_filter.1 ht
      exact mem_filter.2 ⟨mem_filter.2 ⟨h2, h3 ▸ hj⟩, h3⟩

lemma two_le_of_ne {V : ℕ} {x y : Fin V} (h : x ≠ y) : 2 ≤ V := by
  by_contra hV
  apply h
  have hx := x.isLt
  have hy := y.isLt
  exact Fin.ext (by omega)

/-- `V^a ≤ 2^S e^{a k r}` for `a ≤ S`, if `V ≤ 2 e^{k r}`. -/
lemma pow_le_two_pow_exp {V a S : ℕ} {K r : ℝ} (hV : (V : ℝ) ≤ 2 * exp (K * r)) (ha : a ≤ S) :
    (V : ℝ) ^ a ≤ 2 ^ S * exp (a * K * r) := by
  calc (V : ℝ) ^ a ≤ (2 * exp (K * r)) ^ a := pow_le_pow_left₀ (by positivity) hV _
    _ = 2 ^ a * exp (a * K * r) := by
        rw [mul_pow, ← exp_natCast_mul]
        congr 2
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ one_le_two ha) (exp_pos _).le

section Count

variable [NeZero V₁] [NeZero V₂]

/-- The total information of the groups of a pair of sets of segments. -/
def asyncC (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (k b : ℕ) (dA dB : Fin n)
    (J J' : Finset (Fin (b + 3))) : ℝ :=
  (asyncG₂ k b dA dB J J').card * macInfo₁ p₁ p₂ W +
    (asyncG₃ k b dA dB J J').card * macInfo₂ p₁ p₂ W +
    (asyncG₄ k b dA dB J J').card * macInfo₁₂ p₁ p₂ W

open Classical in
/-- The bound for one hypothesis, with fresh sets `J` and `J'`. -/
def asyncB (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (k b : ℕ) (dA dB : Fin n) (D γ : ℝ)
    (J J' : Finset (Fin (b + 3))) : ℝ :=
  if J = ∅ ∧ J' = ∅ then exp (-((γ * k - D) / 2)) else exp
    (-(asyncC p₁ p₂ W k b dA dB J J' - 3 * D))

omit [NeZero V₁] [NeZero V₂] in
lemma asyncB_nonneg (dA dB : Fin n) (D γ : ℝ) (J J' : Finset (Fin (b + 3))) :
    0 ≤ asyncB p₁ p₂ W k b dA dB D γ J J' := by
  unfold asyncB
  split_ifs <;> exact (exp_pos _).le

/-- The number of hypotheses with the fresh set `J`. -/
def asyncN {V : ℕ} [NeZero V] (D : Finset (Fin (b + 3))) (Th : Fin (b + 3) → Finset (Fin V))
    (J : Finset (Fin (b + 3))) : ℕ :=
  ((asyncHyp D).filter fun v => asyncFresh D Th v = J).card

omit [NeZero V₁] [NeZero V₂] in
/-- **The bound for one hypothesis with a wrong message.** -/
theorem asyncE_passes_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (hk : 0 < k)
    (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) {D : ℝ} (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁)
    (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂) (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂)
    (d₁ d₂ dA dB : Fin n) {r₁ γ : ℝ} (hr₁ : 0 ≤ r₁) (hγ : 0 < γ)
    (hA : 2 ≤ V₁ → r₁ + γ ≤ macInfo₁ p₁ p₂ W) {vA : Fin (b + 3) → Fin V₁}
    (hvA : ∃ j ∈ asyncMsg b, vA j ≠ sub₁ (m₁ 1) j) (vB : Fin (b + 3) → Fin V₂)
    (D₂ : Finset (Fin (b + 3))) :
    asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂)
        (fun τ₁ τ₂ y => open Classical in
          if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then 1 else 0) ≤
      asyncB p₁ p₂ W k b dA dB D γ (asyncFresh (asyncMsg b) (asyncThree sub₁ m₁) vA)
        (asyncFresh D₂ (asyncThree sub₂ m₂) vB) := by
  classical
  obtain ⟨j, hj, hjw⟩ := hvA
  by_cases hemp : asyncFresh (asyncMsg b) (asyncThree sub₁ m₁) vA = ∅ ∧
      asyncFresh D₂ (asyncThree sub₂ m₂) vB = ∅
  · rw [asyncB, ite_eq_left hemp]
    have h2V : 2 ≤ V₁ := two_le_of_ne hjw
    have hI := hA h2V
    have hconf := asyncPasses_conflict_le hp₁ hp₂ hW hk hl hu D sub₁ sub₂ m₁ m₂ d₁ d₂ dA dB vA vB
      hj hjw (by linarith) (fun τ₁ τ₂ y => if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then
        1 else 0) (fun τ₁ τ₂ y => le_of_eq (by congr))
    refine hconf.trans (exp_le_exp.2 ?_)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have : γ * k ≤ k * macInfo₁ p₁ p₂ W := by nlinarith
    linarith
  · rw [asyncB, ite_eq_right hemp]
    exact asyncPasses_fresh_le hp₁ hp₂ hW hk D sub₁ sub₂ m₁ m₂ d₁ d₂ dA dB vA vB _ _
      (fun j hj => (mem_filter.1 hj).2) (fun j hj => (mem_filter.1 hj).2)
      (fun τ₁ τ₂ y => if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then 1 else 0)
      (fun τ₁ τ₂ y => le_of_eq (by congr))

omit [NeZero V₁] [NeZero V₂] in
/-- The arithmetic of one pattern. -/
lemma async_term_arith {N N' Va Vb Ea Eb E₀ e₁ : ℝ} {S : ℕ} (hN'0 : 0 ≤ N')
    (hNle : N ≤ Va * 4 ^ S) (hN'le : N' ≤ Vb * 4 ^ S) (hVa : Va ≤ 2 ^ S * Ea)
    (hVb : Vb ≤ 2 ^ S * Eb) (hEa : 0 ≤ Ea) (hE₀ : 0 ≤ E₀)
    (h : Ea * (Eb * E₀) ≤ e₁) : N * (N' * E₀) ≤ 64 ^ S * e₁ := by
  have hS4 : (0 : ℝ) ≤ 4 ^ S := by positivity
  have h7 : N ≤ 2 ^ S * Ea * 4 ^ S := hNle.trans (mul_le_mul_of_nonneg_right hVa hS4)
  have h8 : N' ≤ 2 ^ S * Eb * 4 ^ S := hN'le.trans (mul_le_mul_of_nonneg_right hVb hS4)
  have h9 : N * (N' * E₀) ≤ (2 ^ S * Ea * 4 ^ S) * ((2 ^ S * Eb * 4 ^ S) * E₀) :=
    mul_le_mul h7 (mul_le_mul_of_nonneg_right h8 hE₀) (mul_nonneg hN'0 hE₀) (by positivity)
  have h11 : (64 : ℝ) ^ S = 2 ^ S * 4 ^ S * (2 ^ S * 4 ^ S) := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have h10 : (2 ^ S * Ea * 4 ^ S) * ((2 ^ S * Eb * 4 ^ S) * E₀) = 64 ^ S * (Ea * (Eb * E₀)) := by
    rw [h11]
    ring
  rw [h10] at h9
  exact h9.trans (mul_le_mul_of_nonneg_left h (by positivity))

/-- The sizes of the groups pay for the fresh segments. -/
lemma asyncGroups_ge (hk : 0 < k) (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) (dA dB : Fin n)
    {J J' : Finset (Fin (b + 3))} (hJ : J ⊆ asyncMsg b) (hJ' : J' ⊆ asyncSegsB k b dA dB) :
    ((J.card : ℝ) * k ≤ (asyncG₂ k b dA dB J J').card + (asyncG₄ k b dA dB J J').card) ∧
    ((J'.card : ℝ) * k ≤ (asyncG₃ k b dA dB J J').card + (asyncG₄ k b dA dB J J').card) := by
  classical
  constructor
  · have := mul_le_card_groups (asyncTest k dA dB) (fun t => asyncSeg k b (asyncPos dA t))
      (fun t => asyncSeg k b (asyncPos dB t)) J J'
      (fun j hj => le_card_filter_segA hk hl hu dA dB (hJ hj))
    exact_mod_cast this
  · have := mul_le_card_groups (asyncTest k dA dB) (fun t => asyncSeg k b (asyncPos dB t))
      (fun t => asyncSeg k b (asyncPos dA t)) J' J
      (fun j hj => by
        obtain ⟨h3, h4⟩ := mem_filter.1 (hJ' hj)
        exact le_card_filter_segB hk hl hu dA dB h3 h4)
    have e3 : ((asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dB t) ∈ J' ∧
        asyncSeg k b (asyncPos dA t) ∉ J) = asyncG₃ k b dA dB J J' :=
      filter_congr fun t _ => and_comm
    have e4 : ((asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dB t) ∈ J' ∧
        asyncSeg k b (asyncPos dA t) ∈ J) = asyncG₄ k b dA dB J J' :=
      filter_congr fun t _ => and_comm
    rw [e3, e4] at this
    exact_mod_cast this

/-- The exponent of a nonempty pattern, in terms of the fresh sets. -/
lemma asyncC_exponent (hk : 0 < k) (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) (dA dB : Fin n)
    {J J' : Finset (Fin (b + 3))} (hJ : J ⊆ asyncMsg b) (hJ' : J' ⊆ asyncSegsB k b dA dB)
    {r₁ r₂ γ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hγ : 0 < γ)
    (hA : J ≠ ∅ → r₁ + γ ≤ macInfo₁ p₁ p₂ W) (hB : J' ≠ ∅ → r₂ + γ ≤ macInfo₂ p₁ p₂ W)
    (hAB : J ≠ ∅ → J' ≠ ∅ → r₁ + r₂ + γ ≤ macInfo₁₂ p₁ p₂ W) (hemp : ¬ (J = ∅ ∧ J' = ∅)) :
    (J.card : ℝ) * k * r₁ + (J'.card : ℝ) * k * r₂ - asyncC p₁ p₂ W k b dA dB J J' ≤ -(γ * k) := by
  obtain ⟨hg1, hg2⟩ := asyncGroups_ge hk hl hu dA dB hJ hJ'
  have hnat : ∀ m : ℕ, (m : ℝ) = 0 ∨ 1 ≤ (m : ℝ) := fun m => by
    rcases Nat.eq_zero_or_pos m with h | h
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  have hne : ∀ {A : Finset (Fin (b + 3))}, (A.card : ℝ) ≠ 0 → A ≠ ∅ := fun h he => h (by simp [he])
  refine async_exponent_le (by positivity) (hnat _) (hnat _) (by positivity) (by positivity)
    (by positivity) hr₁ hr₂ hγ hg1 hg2 ?_ ?_ (fun h => hA (hne h)) (fun h => hB (hne h))
    (fun h h' => hAB (hne h) (hne h')) ?_
  · intro h
    have hJ0 : J = ∅ := card_eq_zero.1 (by exact_mod_cast h)
    subst hJ0
    simp [asyncG₂, asyncG₄]
  · intro h
    have hJ0 : J' = ∅ := card_eq_zero.1 (by exact_mod_cast h)
    subst hJ0
    simp [asyncG₃, asyncG₄]
  · by_contra hcon
    push Not at hcon
    exact hemp ⟨card_eq_zero.1 (by exact_mod_cast hcon.1),
      card_eq_zero.1 (by exact_mod_cast hcon.2)⟩

/-- If the fresh set of a hypothesis is nonempty, the table has at least two sub-messages. -/
lemma two_le_of_fresh {V M : ℕ} [NeZero V] {D : Finset (Fin (b + 3))}
    {sub : Fin M → Fin (b + 3) → Fin V} {m : Fin 3 → Fin M} {J : Finset (Fin (b + 3))}
    (hN : asyncN D (asyncThree sub m) J ≠ 0) (hJ : J ≠ ∅) : 2 ≤ V := by
  classical
  obtain ⟨v, hv⟩ : ((asyncHyp D).filter fun v => asyncFresh D (asyncThree sub m) v = J).Nonempty :=
    card_pos.1 (Nat.pos_of_ne_zero hN)
  obtain ⟨j, hj⟩ := ne_empty_iff_nonempty.1 hJ
  rw [← (mem_filter.1 hv).2] at hj
  have h3 : v j ∉ asyncThree sub m j := (mem_filter.1 hj).2
  have h4 : sub (m 0) j ∈ asyncThree sub m j := mem_image_of_mem _ (mem_univ _)
  exact two_le_of_ne (x := v j) (y := sub (m 0) j) fun he => h3 (he ▸ h4)

lemma subset_of_fresh {V : ℕ} [NeZero V] {D : Finset (Fin (b + 3))}
    {Th : Fin (b + 3) → Finset (Fin V)} {J : Finset (Fin (b + 3))} (hN : asyncN D Th J ≠ 0) :
    J ⊆ D := by
  classical
  obtain ⟨v, hv⟩ : ((asyncHyp D).filter fun v => asyncFresh D Th v = J).Nonempty :=
    card_pos.1 (Nat.pos_of_ne_zero hN)
  rw [← (mem_filter.1 hv).2]
  exact filter_subset _ _

/-- **The bound for one pattern of fresh sets.** -/
theorem asyncTerm_le (hk : 0 < k) (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) {D : ℝ}
    (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂)
    (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂) (dA dB : Fin n) {r₁ r₂ γ : ℝ} (hr₁ : 0 ≤ r₁)
    (hr₂ : 0 ≤ r₂) (hγ : 0 < γ) (hV₁ : (V₁ : ℝ) ≤ 2 * exp (k * r₁))
    (hV₂ : (V₂ : ℝ) ≤ 2 * exp (k * r₂)) (hA : 2 ≤ V₁ → r₁ + γ ≤ macInfo₁ p₁ p₂ W)
    (hB : 2 ≤ V₂ → r₂ + γ ≤ macInfo₂ p₁ p₂ W)
    (hAB : 2 ≤ V₁ → 2 ≤ V₂ → r₁ + r₂ + γ ≤ macInfo₁₂ p₁ p₂ W) (J J' : Finset (Fin (b + 3))) :
    (asyncN (asyncMsg b) (asyncThree sub₁ m₁) J : ℝ) *
      ((asyncN (asyncSegsB k b dA dB) (asyncThree sub₂ m₂) J' : ℝ) *
        asyncB p₁ p₂ W k b dA dB D γ J J') ≤
      64 ^ (b + 3) * exp (-(γ * k - 3 * D)) + 16 ^ (b + 3) * exp (-((γ * k - D) / 2)) := by
  classical
  set N := asyncN (asyncMsg b) (asyncThree sub₁ m₁) J with hN
  set N' := asyncN (asyncSegsB k b dA dB) (asyncThree sub₂ m₂) J' with hN'
  have hNle : (N : ℝ) ≤ (V₁ : ℝ) ^ J.card * 4 ^ (b + 3) := by
    have := card_fresh_fiber_le (b := b) (V := V₁) (asyncMsg b) J (asyncThree sub₁ m₁)
      (card_asyncThree_le sub₁ m₁)
    exact_mod_cast this
  have hN'le : (N' : ℝ) ≤ (V₂ : ℝ) ^ J'.card * 4 ^ (b + 3) := by
    have := card_fresh_fiber_le (b := b) (V := V₂) (asyncSegsB k b dA dB) J' (asyncThree sub₂ m₂)
      (card_asyncThree_le sub₂ m₂)
    exact_mod_cast this
  have he₁ : 0 ≤ (64 : ℝ) ^ (b + 3) * exp (-(γ * k - 3 * D)) := by positivity
  have he₂ : 0 ≤ (16 : ℝ) ^ (b + 3) * exp (-((γ * k - D) / 2)) := by positivity
  by_cases hemp : J = ∅ ∧ J' = ∅
  · rw [asyncB, ite_eq_left hemp]
    have h1 : (N : ℝ) ≤ 4 ^ (b + 3) := by simpa [hemp.1] using hNle
    have h2 : (N' : ℝ) ≤ 4 ^ (b + 3) := by simpa [hemp.2] using hN'le
    have h3 := mul_le_mul h1 (mul_le_mul_of_nonneg_right h2
      (exp_pos (-((γ * k - D) / 2))).le) (by positivity) (by positivity)
    have h4 : (4 : ℝ) ^ (b + 3) * (4 ^ (b + 3) * exp (-((γ * k - D) / 2))) =
        16 ^ (b + 3) * exp (-((γ * k - D) / 2)) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    linarith
  · rw [asyncB, ite_eq_right hemp]
    by_cases hzero : N = 0 ∨ N' = 0
    · rcases hzero with h | h
      · rw [h]
        simp only [Nat.cast_zero, zero_mul]
        linarith
      · rw [h]
        simp only [Nat.cast_zero, zero_mul, mul_zero]
        linarith
    · push Not at hzero
      have hJ := subset_of_fresh (hN ▸ hzero.1)
      have hJ' := subset_of_fresh (hN' ▸ hzero.2)
      have hexpo := asyncC_exponent (p₁ := p₁) (p₂ := p₂) (W := W) hk hl hu dA dB hJ hJ' hr₁ hr₂ hγ
        (fun h => hA (two_le_of_fresh (hN ▸ hzero.1) h))
        (fun h => hB (two_le_of_fresh (hN' ▸ hzero.2) h))
        (fun h h' => hAB (two_le_of_fresh (hN ▸ hzero.1) h) (two_le_of_fresh (hN' ▸ hzero.2) h'))
        hemp
      have hcardJ : ∀ A : Finset (Fin (b + 3)), A.card ≤ b + 3 := fun A => by
        calc A.card ≤ (univ : Finset (Fin (b + 3))).card := card_le_card (subset_univ _)
          _ = b + 3 := by simp
      have h9 := async_term_arith (N := N) (N' := N') (Va := (V₁ : ℝ) ^ J.card)
        (Vb := (V₂ : ℝ) ^ J'.card) (Ea := exp (J.card * k * r₁)) (Eb := exp (J'.card * k * r₂))
        (E₀ := exp (-(asyncC p₁ p₂ W k b dA dB J J' - 3 * D)))
        (e₁ := exp (-(γ * k - 3 * D))) (by positivity) hNle hN'le
        (pow_le_two_pow_exp hV₁ (hcardJ J)) (pow_le_two_pow_exp hV₂ (hcardJ J'))
        (exp_pos _).le (exp_pos _).le (by
          rw [← exp_add, ← exp_add]
          refine exp_le_exp.2 ?_
          linarith)
      linarith

/-- **The union bound for fixed delays of a hypothesis.** The hypotheses with a wrong message of
sender `A` pass the tests with small probability, in total. -/
theorem sum_asyncE_passes_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (hk : 0 < k)
    (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) {D : ℝ} (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁)
    (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂) (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂)
    (d₁ d₂ dA dB : Fin n) {r₁ r₂ γ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hγ : 0 < γ)
    (hV₁ : (V₁ : ℝ) ≤ 2 * exp (k * r₁)) (hV₂ : (V₂ : ℝ) ≤ 2 * exp (k * r₂))
    (hA : 2 ≤ V₁ → r₁ + γ ≤ macInfo₁ p₁ p₂ W) (hB : 2 ≤ V₂ → r₂ + γ ≤ macInfo₂ p₁ p₂ W)
    (hAB : 2 ≤ V₁ → 2 ≤ V₂ → r₁ + r₂ + γ ≤ macInfo₁₂ p₁ p₂ W) :
    ∑ vA ∈ (asyncHyp (asyncMsg b)).filter (fun v : Fin (b + 3) → Fin V₁ =>
        ∃ j ∈ asyncMsg b, v j ≠ sub₁ (m₁ 1) j),
      ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
      asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂)
        (fun τ₁ τ₂ y => open Classical in
          if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then 1 else 0) ≤
    4 ^ (b + 3) * (64 ^ (b + 3) * exp (-(γ * k - 3 * D)) +
      16 ^ (b + 3) * exp (-((γ * k - D) / 2))) := by
  classical
  set B := asyncB p₁ p₂ W k b dA dB D γ with hBdef
  set JA := asyncFresh (V := V₁) (asyncMsg b) (asyncThree sub₁ m₁) with hJA
  set JB := asyncFresh (V := V₂) (asyncSegsB k b dA dB) (asyncThree sub₂ m₂) with hJB
  calc _ ≤ ∑ vA ∈ (asyncHyp (asyncMsg b)).filter (fun v : Fin (b + 3) → Fin V₁ =>
        ∃ j ∈ asyncMsg b, v j ≠ sub₁ (m₁ 1) j),
        ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB), B (JA vA) (JB vB) :=
        sum_le_sum fun vA hvA => sum_le_sum fun vB _ =>
          asyncE_passes_le hp₁ hp₂ hW hk hl hu sub₁ sub₂ m₁ m₂ d₁ d₂ dA dB hr₁ hγ hA
            (mem_filter.1 hvA).2 vB _
    _ ≤ ∑ vA ∈ asyncHyp (asyncMsg b), ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
        B (JA vA) (JB vB) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun vA _ _ => sum_nonneg fun vB _ => asyncB_nonneg _ _ _ _ _ _
    _ = ∑ J, ∑ J', (asyncN (asyncMsg b) (asyncThree sub₁ m₁) J : ℝ) *
        ((asyncN (asyncSegsB k b dA dB) (asyncThree sub₂ m₂) J' : ℝ) * B J J') := by
        have h1 : ∀ vA : Fin (b + 3) → Fin V₁, ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
            B (JA vA) (JB vB) = ∑ J', (asyncN (asyncSegsB k b dA dB) (asyncThree sub₂ m₂) J' : ℝ) *
              B (JA vA) J' := fun vA => sum_comp_fiber _ JB (B (JA vA))
        simp only [h1]
        rw [sum_comp_fiber _ JA (fun J => ∑ J', (asyncN (asyncSegsB k b dA dB)
          (asyncThree sub₂ m₂) J' : ℝ) * B J J')]
        refine sum_congr rfl fun J _ => ?_
        rw [mul_sum]
        rfl
    _ ≤ ∑ _J : Finset (Fin (b + 3)), ∑ _J' : Finset (Fin (b + 3)),
        (64 ^ (b + 3) * exp (-(γ * k - 3 * D)) + 16 ^ (b + 3) * exp (-((γ * k - D) / 2))) :=
        sum_le_sum fun J _ => sum_le_sum fun J' _ =>
          asyncTerm_le hk hl hu sub₁ sub₂ m₁ m₂ dA dB hr₁ hr₂ hγ hV₁ hV₂ hA hB hAB J J'
    _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        have : (4 : ℝ) ^ (b + 3) = 2 ^ (b + 3) * 2 ^ (b + 3) := by
          rw [← mul_pow]
          norm_num
        rw [this]
        ring

end Count

end InfoTheory
