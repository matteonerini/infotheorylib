/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Networking.AsyncTable
public import InfoTheoryLib.Networking.AsyncWindow

/-!
# The decoder for the asynchronous multiple-access channel

The hypotheses and the tests of the achievability of Theorem 2 of Lecture 24 of El Gamal and Kim. A
sender's codebook is a table of independent letters, one for each position in a block and each
sub-message of its segment, so different positions never share a letter. The decoder of sender `A`
looks for delays, a message of sender `A` and sub-messages of sender `B` that pass the
information-density tests on every group of slots.

There is no separate synchronization. A hypothesis with a wrong delay reads letters that are
independent of the outputs unless it uses a sub-message that was actually sent. There are few such
hypotheses, and each one is excluded by splitting its slots into two classes without conflicts.

## Main definitions

* `asyncLetter k b v p`: the entry of the table read at position `p`, for the sub-messages `v`.
* `asyncG₂`, `asyncG₃`, `asyncG₄`: the groups of slots of a pair of sets of segments.
* `AsyncPasses`: a hypothesis passes all the tests.
* `asyncThree sub m j`: the sub-messages actually sent in segment `j`.

## Main statements

* `asyncPasses_fresh_le`: the bound for a hypothesis with fresh sub-messages.
* `asyncPasses_conflict_le`: the bound for a hypothesis using only sub-messages actually sent.
* `asyncPasses_true`: if the true entries pass the tests, so does the true hypothesis.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset Real

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]
  {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} {W : α₁ × α₂ → β → ℝ} {n k b V₁ V₂ : ℕ}

/-- The entry of the table read at position `p`, for the sub-messages `v` of the segments. -/
def asyncLetter (k b : ℕ) {V : ℕ} (v : Fin (b + 3) → Fin V) (p : Fin n) : Fin n × Fin V :=
  (p, v (asyncSeg k b p))

/-- The slots of the test set with sender `A` in `JA` and sender `B` out of `JB`. -/
def asyncG₂ (k b : ℕ) (dA dB : Fin n) (JA JB : Finset (Fin (b + 3))) :
    Finset (Fin (2 * n - 1)) :=
  (asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dA t) ∈ JA ∧
    asyncSeg k b (asyncPos dB t) ∉ JB

/-- The slots of the test set with sender `A` out of `JA` and sender `B` in `JB`. -/
def asyncG₃ (k b : ℕ) (dA dB : Fin n) (JA JB : Finset (Fin (b + 3))) :
    Finset (Fin (2 * n - 1)) :=
  (asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dA t) ∉ JA ∧
    asyncSeg k b (asyncPos dB t) ∈ JB

/-- The slots of the test set with sender `A` in `JA` and sender `B` in `JB`. -/
def asyncG₄ (k b : ℕ) (dA dB : Fin n) (JA JB : Finset (Fin (b + 3))) :
    Finset (Fin (2 * n - 1)) :=
  (asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dA t) ∈ JA ∧
    asyncSeg k b (asyncPos dB t) ∈ JB

/-- **The tests of a hypothesis.** The delays `dA, dB` and the sub-messages `vA, vB` pass if on each
group of slots the product of the densities is at least `e^{|G| I - D}`, for the mutual information
`I` of that group. -/
def AsyncPasses (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (k b : ℕ) (D : ℝ)
    (τ₁ : Fin n × Fin V₁ → α₁) (τ₂ : Fin n × Fin V₂ → α₂) (dA dB : Fin n)
    (vA : Fin (b + 3) → Fin V₁) (vB : Fin (b + 3) → Fin V₂) (y : Fin (2 * n - 1) → β) : Prop :=
  ∀ JA JB : Finset (Fin (b + 3)),
    exp ((asyncG₂ k b dA dB JA JB).card * macInfo₁ p₁ p₂ W - D) ≤
      ∏ t ∈ asyncG₂ k b dA dB JA JB, macRatio₁ p₁ W (τ₁ (asyncLetter k b vA (asyncPos dA t)))
        (τ₂ (asyncLetter k b vB (asyncPos dB t))) (y t) ∧
    exp ((asyncG₃ k b dA dB JA JB).card * macInfo₂ p₁ p₂ W - D) ≤
      ∏ t ∈ asyncG₃ k b dA dB JA JB, macRatio₂ p₂ W (τ₁ (asyncLetter k b vA (asyncPos dA t)))
        (τ₂ (asyncLetter k b vB (asyncPos dB t))) (y t) ∧
    exp ((asyncG₄ k b dA dB JA JB).card * macInfo₁₂ p₁ p₂ W - D) ≤
      ∏ t ∈ asyncG₄ k b dA dB JA JB, macRatio₁₂ p₁ p₂ W (τ₁ (asyncLetter k b vA (asyncPos dA t)))
        (τ₂ (asyncLetter k b vB (asyncPos dB t))) (y t)

/-- The sub-messages actually sent in segment `j`, over the three blocks of the window. -/
def asyncThree {M V : ℕ} (sub : Fin M → Fin (b + 3) → Fin V) (m : Fin 3 → Fin M)
    (j : Fin (b + 3)) : Finset (Fin V) :=
  univ.image fun r => sub (m r) j

/-- The entry of the table read by the true messages. -/
def asyncTrue (k b : ℕ) {M V : ℕ} (sub : Fin M → Fin (b + 3) → Fin V) (m : Fin 3 → Fin M)
    (d : Fin n) (t : Fin (2 * n - 1)) : Fin n × Fin V :=
  asyncLetter k b (sub (m (asyncOff d t))) (asyncPos d t)

lemma asyncLetter_ne_true {M V : ℕ} {sub : Fin M → Fin (b + 3) → Fin V} {m : Fin 3 → Fin M}
    {v : Fin (b + 3) → Fin V} {d d' : Fin n} {t t' : Fin (2 * n - 1)}
    (hv : v (asyncSeg k b (asyncPos d t)) ∉ asyncThree sub m (asyncSeg k b (asyncPos d t))) :
    asyncLetter k b v (asyncPos d t) ≠ asyncTrue k b sub m d' t' := by
  intro h
  have h1 : asyncPos d t = asyncPos d' t' := congrArg Prod.fst h
  have h2 : v (asyncSeg k b (asyncPos d t)) =
      sub (m (asyncOff d' t')) (asyncSeg k b (asyncPos d' t')) := congrArg Prod.snd h
  apply hv
  rw [h1] at h2 ⊢
  rw [h2]
  exact mem_image_of_mem _ (mem_univ _)

variable {M₁ M₂ : ℕ}

/-- **The bound for a hypothesis with fresh sub-messages.** On the segments of `JA` and `JB` the
hypothesis uses sub-messages that were not sent, so the letters it reads there are independent of
all the rest. The hypothesis passes with probability at most
`e^{-(|G₂| I₁ + |G₃| I₂ + |G₄| I₁₂ - 3 D)}`. -/
theorem asyncPasses_fresh_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hW : IsChannel W) (hk : 0 < k) (D : ℝ) (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁)
    (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂) (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂)
    (d₁ d₂ dA dB : Fin n) (vA : Fin (b + 3) → Fin V₁) (vB : Fin (b + 3) → Fin V₂)
    (JA JB : Finset (Fin (b + 3))) (hJA : ∀ j ∈ JA, vA j ∉ asyncThree sub₁ m₁ j)
    (hJB : ∀ j ∈ JB, vB j ∉ asyncThree sub₂ m₂ j) (P : (Fin n × Fin V₁ → α₁) →
      (Fin n × Fin V₂ → α₂) → (Fin (2 * n - 1) → β) → ℝ)
    (hP : ∀ τ₁ τ₂ y, P τ₁ τ₂ y ≤ (open Classical in
      if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then 1 else 0)) :
    ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ *
      ∑ y : Fin (2 * n - 1) → β,
      (∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) *
        P τ₁ τ₂ y ≤
      exp (-(((asyncG₂ k b dA dB JA JB).card * macInfo₁ p₁ p₂ W +
        (asyncG₃ k b dA dB JA JB).card * macInfo₂ p₁ p₂ W +
        (asyncG₄ k b dA dB JA JB).card * macInfo₁₂ p₁ p₂ W) - 3 * D)) := by
  classical
  set G₂ := asyncG₂ k b dA dB JA JB with hG₂
  set G₃ := asyncG₃ k b dA dB JA JB with hG₃
  set G₄ := asyncG₄ k b dA dB JA JB with hG₄
  set ah : Fin (2 * n - 1) → Fin n × Fin V₁ := fun t => asyncLetter k b vA (asyncPos dA t) with hah
  set bh : Fin (2 * n - 1) → Fin n × Fin V₂ := fun t => asyncLetter k b vB (asyncPos dB t) with hbh
  have hm₂ : ∀ {t}, t ∈ G₂ → t ∈ asyncTest k dA dB ∧ asyncSeg k b (asyncPos dA t) ∈ JA ∧
      asyncSeg k b (asyncPos dB t) ∉ JB := fun h => by simpa [hG₂, asyncG₂] using h
  have hm₃ : ∀ {t}, t ∈ G₃ → t ∈ asyncTest k dA dB ∧ asyncSeg k b (asyncPos dA t) ∉ JA ∧
      asyncSeg k b (asyncPos dB t) ∈ JB := fun h => by simpa [hG₃, asyncG₃] using h
  have hm₄ : ∀ {t}, t ∈ G₄ → t ∈ asyncTest k dA dB ∧ asyncSeg k b (asyncPos dA t) ∈ JA ∧
      asyncSeg k b (asyncPos dB t) ∈ JB := fun h => by simpa [hG₄, asyncG₄] using h
  have h₂₃ : Disjoint G₂ G₃ := disjoint_left.2 fun t h h' => (hm₃ h').2.1 (hm₂ h).2.1
  have h₂₄ : Disjoint G₂ G₄ := disjoint_left.2 fun t h h' => (hm₂ h).2.2 (hm₄ h').2.2
  have h₃₄ : Disjoint G₃ G₄ := disjoint_left.2 fun t h h' => (hm₃ h).2.1 (hm₄ h').2.1
  have hA24 : ∀ {t}, t ∈ G₂ ∪ G₄ → t ∈ asyncTest k dA dB ∧ asyncSeg k b (asyncPos dA t) ∈ JA := by
    intro t h
    rcases mem_union.1 h with h | h
    · exact ⟨(hm₂ h).1, (hm₂ h).2.1⟩
    · exact ⟨(hm₄ h).1, (hm₄ h).2.1⟩
  have hB34 : ∀ {t}, t ∈ G₃ ∪ G₄ → t ∈ asyncTest k dA dB ∧ asyncSeg k b (asyncPos dB t) ∈ JB := by
    intro t h
    rcases mem_union.1 h with h | h
    · exact ⟨(hm₃ h).1, (hm₃ h).2.2⟩
    · exact ⟨(hm₄ h).1, (hm₄ h).2.2⟩
  have hmain := sum_tables_test_le hp₁ hp₂ hW (asyncTrue k b sub₁ m₁ d₁) ah
    (asyncTrue k b sub₂ m₂ d₂) bh h₂₃ h₂₄ h₃₄
    (fun t ht t' ht' he => asyncPos_injOn_test hk dA (hA24 (by exact_mod_cast ht)).1
      (hA24 (by exact_mod_cast ht')).1 (congrArg Prod.fst he))
    (fun t ht t' ht' he => asyncPos_injOn_test hk dB (hB34 (by exact_mod_cast ht)).1
      (hB34 (by exact_mod_cast ht')).1 (congrArg Prod.fst he))
    (fun t ht t' _ => asyncLetter_ne_true (hJA _ (hA24 ht).2))
    (fun t ht t' ht' he => (hm₃ ht').2.1 (by
      have := asyncPos_injOn_test hk dA (hA24 ht).1 (hm₃ ht').1 (congrArg Prod.fst he)
      rw [← this]
      exact (hA24 ht).2))
    (fun t ht t' _ => asyncLetter_ne_true (hJB _ (hB34 ht).2))
    (G₂.card * macInfo₁ p₁ p₂ W - D) (G₃.card * macInfo₂ p₁ p₂ W - D)
    (G₄.card * macInfo₁₂ p₁ p₂ W - D)
  have e : -((G₂.card : ℝ) * macInfo₁ p₁ p₂ W - D + ((G₃.card : ℝ) * macInfo₂ p₁ p₂ W - D) +
      ((G₄.card : ℝ) * macInfo₁₂ p₁ p₂ W - D)) =
      -(((G₂.card : ℝ) * macInfo₁ p₁ p₂ W + (G₃.card : ℝ) * macInfo₂ p₁ p₂ W +
        (G₄.card : ℝ) * macInfo₁₂ p₁ p₂ W) - 3 * D) := by
    ring
  rw [e] at hmain
  refine le_trans ?_ hmain
  refine sum_le_sum fun τ₁ _ => mul_le_mul_of_nonneg_left
    (sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left
      (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_
        (prod_nonneg fun t _ => (hW _).nonneg _)) (tableLaw_nonneg hp₂ τ₂))
    (tableLaw_nonneg hp₁ τ₁)
  refine (hP τ₁ τ₂ y).trans ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1 JA JB) h2
  · exact zero_le_one
  · exact le_rfl

/-- **The bound for a hypothesis using only sub-messages actually sent.** Suppose the hypothesis has
a sub-message `vA j` different from the current one in a message segment `j`. Its letters can then
only meet the true letters of another block, at one fixed shift of the time. So the slots of the
segment split into two classes without conflicts, and each class has expected density at most `1`.
The hypothesis passes with probability at most `e^{-(k I₁ - D) / 2}`. -/
theorem asyncPasses_conflict_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (hk : 0 < k)
    (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) (D : ℝ) (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁)
    (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂) (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂)
    (d₁ d₂ dA dB : Fin n) (vA : Fin (b + 3) → Fin V₁) (vB : Fin (b + 3) → Fin V₂)
    {j : Fin (b + 3)} (hj : j ∈ asyncMsg b) (hwrong : vA j ≠ sub₁ (m₁ 1) j)
    (hI : 0 ≤ macInfo₁ p₁ p₂ W) (P : (Fin n × Fin V₁ → α₁) →
      (Fin n × Fin V₂ → α₂) → (Fin (2 * n - 1) → β) → ℝ)
    (hP : ∀ τ₁ τ₂ y, P τ₁ τ₂ y ≤ (open Classical in
      if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then 1 else 0)) :
    ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ *
      ∑ y : Fin (2 * n - 1) → β,
      (∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) *
        P τ₁ τ₂ y ≤ exp (-((k * macInfo₁ p₁ p₂ W - D) / 2)) := by
  classical
  set a := asyncTrue k b sub₁ m₁ d₁ with ha
  set ah : Fin (2 * n - 1) → Fin n × Fin V₁ := fun t => asyncLetter k b vA (asyncPos dA t) with hah
  set bh : Fin (2 * n - 1) → Fin n × Fin V₂ := fun t => asyncLetter k b vB (asyncPos dB t) with hbh
  set G := (asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dA t) = j with hG
  have hcard : k ≤ G.card := le_card_filter_segA hk hl hu dA dB hj
  have hGm : ∀ {t}, t ∈ G → t ∈ asyncTest k dA dB ∧ asyncSeg k b (asyncPos dA t) = j :=
    fun h => mem_filter.1 h
  have hdA := dA.isLt
  -- The slots of the segment are close to each other.
  have hbound : ∀ {t}, t ∈ G → (dA : ℕ) + (j : ℕ) * k ≤ t ∧ (t : ℕ) < dA + (j : ℕ) * k + k := by
    intro t ht
    obtain ⟨h1, h2⟩ := hGm ht
    obtain ⟨h3, h4⟩ := asyncTest_bounds hk h1
    have h5 := (asyncPos_of_mem dA h3 h4).1
    have h6 : (asyncPos dA t : ℕ) / k = j := by
      rw [← asyncSeg_val hu (asyncPos dA t).isLt, h2]
    have h7 := Nat.div_add_mod' (asyncPos dA t : ℕ) k
    have h8 := Nat.mod_lt (asyncPos dA t : ℕ) hk
    rw [h6] at h7
    omega
  have h2k : 2 * k ≤ n := by nlinarith
  have hc : ∀ {x y : Fin (2 * n - 1)}, x ∈ G → y ∈ G → 2 * (x : ℕ) < 2 * y + n := by
    intro x y hx hy
    have := hbound hx
    have := hbound hy
    omega
  -- A conflict cannot be at the same time.
  have hne : ∀ {t}, t ∈ G → ah t ≠ a t := by
    intro t ht he
    obtain ⟨h1, h2⟩ := hGm ht
    obtain ⟨h3, h4⟩ := asyncTest_bounds hk h1
    have h5 := (asyncPos_of_mem dA h3 h4).1
    have h6 : asyncPos dA t = asyncPos d₁ t := congrArg Prod.fst he
    have h7 : vA (asyncSeg k b (asyncPos dA t)) =
        sub₁ (m₁ (asyncOff d₁ t)) (asyncSeg k b (asyncPos d₁ t)) := congrArg Prod.snd he
    have h8 := asyncPos_spec d₁ t
    have h9 : (asyncPos dA t : ℕ) = asyncPos d₁ t := congrArg Fin.val h6
    have ho := (asyncOff d₁ t).isLt
    have hd₁ := d₁.isLt
    have ho1 : (asyncOff d₁ t : ℕ) = 1 := by
      generalize (asyncOff d₁ t : ℕ) = o at *
      interval_cases o <;> omega
    have ho2 : asyncOff d₁ t = 1 := Fin.ext ho1
    rw [← h6, h2, ho2] at h7
    exact hwrong h7
  -- The two classes.
  obtain ⟨A₁, A₂, hG', hd, hf₁, hf₂⟩ : ∃ A₁ A₂ : Finset (Fin (2 * n - 1)), A₁ ∪ A₂ = G ∧
      Disjoint A₁ A₂ ∧ (∀ t ∈ A₁, ∀ t' ∈ A₁, ah t ≠ a t') ∧
      (∀ t ∈ A₂, ∀ t' ∈ A₂, ah t ≠ a t') := by
    by_cases hex : ∃ t₀ ∈ G, ∃ t₀' ∈ G, ah t₀ = a t₀'
    · obtain ⟨t₀, ht₀, t₀', ht₀', he₀⟩ := hex
      have hne₀ : (t₀ : ℕ) ≠ t₀' := fun h => hne ht₀ (by
        have : t₀ = t₀' := Fin.ext h
        rw [← this] at he₀
        exact he₀)
      set s : ℕ := max (t₀ : ℕ) t₀' - min (t₀ : ℕ) t₀' with hs
      have hs0 : 0 < s := by omega
      refine ⟨G.filter fun t => (t : ℕ) / s % 2 = 0, G.filter fun t => ¬ (t : ℕ) / s % 2 = 0,
        filter_union_filter_not_eq _ _, disjoint_filter_filter_not _ _ _, ?_, ?_⟩
      all_goals
        intro t ht t' ht' he
        obtain ⟨htG, hpar⟩ := mem_filter.1 ht
        obtain ⟨htG', hpar'⟩ := mem_filter.1 ht'
        have hp₀ : asyncPos dA t₀ = asyncPos d₁ t₀' := congrArg Prod.fst he₀
        have hp : asyncPos dA t = asyncPos d₁ t' := congrArg Prod.fst he
        have hsh := asyncPos_shift_unique hp₀ hp (fun x y hx hy => by
          have hxG : ∀ {z : ℕ}, z = t₀ ∨ z = t₀' ∨ z = t ∨ z = t' →
              ∃ w : Fin (2 * n - 1), w ∈ G ∧ z = w := by
            rintro z (h | h | h | h)
            · exact ⟨t₀, ht₀, h⟩
            · exact ⟨t₀', ht₀', h⟩
            · exact ⟨t, htG, h⟩
            · exact ⟨t', htG', h⟩
          obtain ⟨w, hw, rfl⟩ := hxG hx
          obtain ⟨w', hw', rfl⟩ := hxG hy
          exact hc hw hw')
        have hdiv : (t' : ℕ) = t + s ∨ (t : ℕ) = t' + s := by omega
        rcases hdiv with h | h
        · have h1 : (t' : ℕ) / s = (t : ℕ) / s + 1 := by rw [h, Nat.add_div_right _ hs0]
          omega
        · have h1 : (t : ℕ) / s = (t' : ℕ) / s + 1 := by rw [h, Nat.add_div_right _ hs0]
          omega
    · push Not at hex
      exact ⟨G, ∅, union_empty _, disjoint_empty_right _,
        fun t ht t' ht' => hex t ht t' ht', by simp⟩
  have hmain := sum_tables_halves_le hp₁ hp₂ hW a ah (asyncTrue k b sub₂ m₂ d₂) bh hG' hd
    (fun t ht t' ht' he => asyncPos_injOn_test hk dA (hGm (by exact_mod_cast ht)).1
      (hGm (by exact_mod_cast ht')).1 (congrArg Prod.fst he)) hf₁ hf₂
    (G.card * macInfo₁ p₁ p₂ W - D)
  have hexp : exp (-(((G.card : ℝ) * macInfo₁ p₁ p₂ W - D) / 2)) ≤
      exp (-((k * macInfo₁ p₁ p₂ W - D) / 2)) := by
    refine exp_le_exp.2 ?_
    have : (k : ℝ) * macInfo₁ p₁ p₂ W ≤ G.card * macInfo₁ p₁ p₂ W :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hI
    linarith
  refine le_trans ?_ (hmain.trans hexp)
  refine sum_le_sum fun τ₁ _ => mul_le_mul_of_nonneg_left
    (sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left
      (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_
        (prod_nonneg fun t _ => (hW _).nonneg _)) (tableLaw_nonneg hp₂ τ₂))
    (tableLaw_nonneg hp₁ τ₁)
  refine (hP τ₁ τ₂ y).trans ?_
  have hgroup : asyncG₂ k b dA dB {j} ∅ = G := by
    unfold asyncG₂
    rw [hG]
    refine filter_congr fun t _ => ?_
    simp
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso
    apply h2
    have h3 := (h1 {j} ∅).1
    rw [hgroup] at h3
    exact h3
  · exact zero_le_one
  · exact le_rfl

/-- The entries read by a sender in the test set are all different. -/
lemma asyncTrue_injOn {M V : ℕ} (hk : 0 < k) (sub : Fin M → Fin (b + 3) → Fin V)
    (m : Fin 3 → Fin M) (d dA dB : Fin n) (G : Finset (Fin (2 * n - 1)))
    (hG : G ⊆ asyncTest k dA dB) : Set.InjOn (asyncTrue k b sub m d) (G : Finset _) := by
  intro t ht t' ht' he
  exact asyncPos_injOn_test hk d (hG (by exact_mod_cast ht)) (hG (by exact_mod_cast ht'))
    (congrArg Prod.fst he)

/-! ### The hypothesis of the true messages -/

/-- The message segments of sender `B` that the test set meets. -/
def asyncSegsB (k b : ℕ) (dA dB : Fin n) : Finset (Fin (b + 3)) :=
  (asyncMsg b).filter fun j => ∃ t ∈ asyncTest k dA dB, asyncSeg k b (asyncPos dB t) = j

/-- The sub-messages that are zero outside `D`. -/
def asyncHyp {V : ℕ} [NeZero V] (D : Finset (Fin (b + 3))) : Finset (Fin (b + 3) → Fin V) :=
  univ.filter fun v => ∀ j ∉ D, v j = 0

/-- A map from messages to sub-messages: pilots carry `0`, and the message segments determine the
message. -/
structure IsAsyncSub {M V : ℕ} [NeZero V] (sub : Fin M → Fin (b + 3) → Fin V) : Prop where
  pilot : ∀ m, ∀ j ∉ asyncMsg b, sub m j = 0
  inj : ∀ m m', (∀ j ∈ asyncMsg b, sub m j = sub m' j) → m = m'

open Classical in
/-- The sub-messages of sender `B` in the test set, for the true messages. -/
def asyncTrueV {M V : ℕ} [NeZero V] (k : ℕ) (sub : Fin M → Fin (b + 3) → Fin V)
    (m : Fin 3 → Fin M) (dA dB : Fin n) (j : Fin (b + 3)) : Fin V :=
  if h : j ∈ asyncSegsB k b dA dB then
    sub (m (asyncOff dB (mem_filter.1 h).2.choose)) j else 0

lemma asyncTrueV_mem {M V : ℕ} [NeZero V] (sub : Fin M → Fin (b + 3) → Fin V)
    (m : Fin 3 → Fin M) (dA dB : Fin n) :
    asyncTrueV k sub m dA dB ∈ asyncHyp (asyncSegsB k b dA dB) := by
  simp only [asyncHyp, mem_filter, mem_univ, true_and]
  intro j hj
  simp [asyncTrueV, hj]

/-- In the test set, the true sub-messages read the true entries. -/
lemma asyncLetter_trueV {M V : ℕ} [NeZero V] (hk : 0 < k) (hu : n < (b + 3) * k)
    {sub : Fin M → Fin (b + 3) → Fin V} (hsub : IsAsyncSub sub) (m : Fin 3 → Fin M)
    {dA dB : Fin n} {t : Fin (2 * n - 1)} (ht : t ∈ asyncTest k dA dB) :
    asyncLetter k b (asyncTrueV k sub m dA dB) (asyncPos dB t) = asyncTrue k b sub m dB t := by
  classical
  unfold asyncTrue asyncLetter
  refine Prod.ext rfl ?_
  simp only
  set j := asyncSeg k b (asyncPos dB t) with hj
  by_cases hm : j ∈ asyncMsg b
  · have h : j ∈ asyncSegsB k b dA dB := mem_filter.2 ⟨hm, t, ht, rfl⟩
    have hch := (mem_filter.1 h).2.choose_spec
    have hoff := asyncOff_eq_of_seg_eq hk hu hch.1 ht (hch.2.trans hj)
    simp only [asyncTrueV, h, ↓reduceDIte]
    rw [hoff]
  · have h : j ∉ asyncSegsB k b dA dB := fun h' => hm (mem_filter.1 h').1
    simp only [asyncTrueV, h, ↓reduceDIte]
    rw [hsub.pilot _ _ hm]

/-- In the test set of sender `A`, the true messages of sender `A` read the true entries. -/
lemma asyncLetter_true_current {M V : ℕ} (hk : 0 < k) (sub : Fin M → Fin (b + 3) → Fin V)
    (m : Fin 3 → Fin M) {dA dB : Fin n} {t : Fin (2 * n - 1)} (ht : t ∈ asyncTest k dA dB) :
    asyncLetter k b (sub (m 1)) (asyncPos dA t) = asyncTrue k b sub m dA t := by
  obtain ⟨h3, h4⟩ := asyncTest_bounds hk ht
  have h5 : asyncOff dA t = 1 := Fin.ext (asyncPos_of_mem dA h3 h4).2
  simp [asyncTrue, h5]

/-- If the true entries pass the tests, so does the true hypothesis. -/
lemma asyncPasses_true [NeZero V₂] (hk : 0 < k) (hu : n < (b + 3) * k) {D : ℝ}
    {sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁} {sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂}
    (hsub₂ : IsAsyncSub sub₂) (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂) (d₁ d₂ : Fin n)
    (τ₁ : Fin n × Fin V₁ → α₁) (τ₂ : Fin n × Fin V₂ → α₂) (y : Fin (2 * n - 1) → β)
    (h : ∀ JA JB : Finset (Fin (b + 3)),
      exp ((asyncG₂ k b d₁ d₂ JA JB).card * macInfo₁ p₁ p₂ W - D) ≤
        ∏ t ∈ asyncG₂ k b d₁ d₂ JA JB, macRatio₁ p₁ W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t))
          (τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t) ∧
      exp ((asyncG₃ k b d₁ d₂ JA JB).card * macInfo₂ p₁ p₂ W - D) ≤
        ∏ t ∈ asyncG₃ k b d₁ d₂ JA JB, macRatio₂ p₂ W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t))
          (τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t) ∧
      exp ((asyncG₄ k b d₁ d₂ JA JB).card * macInfo₁₂ p₁ p₂ W - D) ≤
        ∏ t ∈ asyncG₄ k b d₁ d₂ JA JB, macRatio₁₂ p₁ p₂ W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t))
          (τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) :
    AsyncPasses p₁ p₂ W k b D τ₁ τ₂ d₁ d₂ (sub₁ (m₁ 1)) (asyncTrueV k sub₂ m₂ d₁ d₂) y := by
  intro JA JB
  obtain ⟨h1, h2, h3⟩ := h JA JB
  have hl₁ : ∀ t ∈ asyncTest k d₁ d₂, τ₁ (asyncLetter k b (sub₁ (m₁ 1)) (asyncPos d₁ t)) =
      τ₁ (asyncTrue k b sub₁ m₁ d₁ t) := fun t ht => by
    rw [asyncLetter_true_current hk sub₁ m₁ ht]
  have hl₂ : ∀ t ∈ asyncTest k d₁ d₂, τ₂ (asyncLetter k b (asyncTrueV k sub₂ m₂ d₁ d₂)
      (asyncPos d₂ t)) = τ₂ (asyncTrue k b sub₂ m₂ d₂ t) := fun t ht => by
    rw [asyncLetter_trueV hk hu hsub₂ m₂ ht]
  refine ⟨?_, ?_, ?_⟩
  · rw [prod_congr rfl fun t ht => by
      rw [hl₁ t (mem_filter.1 ht).1, hl₂ t (mem_filter.1 ht).1]]
    exact h1
  · rw [prod_congr rfl fun t ht => by
      rw [hl₁ t (mem_filter.1 ht).1, hl₂ t (mem_filter.1 ht).1]]
    exact h2
  · rw [prod_congr rfl fun t ht => by
      rw [hl₁ t (mem_filter.1 ht).1, hl₂ t (mem_filter.1 ht).1]]
    exact h3

/-! ### The decoder -/

/-- A message of sender `A` is accepted if it passes the tests for some delays and some sub-messages
of sender `B` in the segments the test set meets. -/
def AsyncAccepts [NeZero V₂] (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (k b : ℕ) (D : ℝ)
    (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (τ₁ : Fin n × Fin V₁ → α₁) (τ₂ : Fin n × Fin V₂ → α₂)
    (y : Fin (2 * n - 1) → β) (m : Fin M₁) : Prop :=
  ∃ (dA dB : Fin n), ∃ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
    AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB (sub₁ m) vB y

open Classical in
/-- **The decoder of sender `A`:** the unique accepted message. -/
def asyncDecA [NeZero V₂] [NeZero M₁] (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (k b : ℕ)
    (D : ℝ) (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (τ₁ : Fin n × Fin V₁ → α₁)
    (τ₂ : Fin n × Fin V₂ → α₂) (y : Fin (2 * n - 1) → β) : Fin M₁ :=
  if h : ∃! m, AsyncAccepts (V₂ := V₂) p₁ p₂ W k b D sub₁ τ₁ τ₂ y m then h.choose else 0

/-- The decoder errs only if the true message is rejected or another one is accepted. -/
lemma asyncDecA_ne [NeZero V₂] [NeZero M₁] {D : ℝ} {sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁}
    {τ₁ : Fin n × Fin V₁ → α₁} {τ₂ : Fin n × Fin V₂ → α₂} {y : Fin (2 * n - 1) → β} {m : Fin M₁}
    (h : asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m) :
    ¬ AsyncAccepts (V₂ := V₂) p₁ p₂ W k b D sub₁ τ₁ τ₂ y m ∨
      ∃ m' ≠ m, AsyncAccepts (V₂ := V₂) p₁ p₂ W k b D sub₁ τ₁ τ₂ y m' := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hu : ∃! m', AsyncAccepts (V₂ := V₂) p₁ p₂ W k b D sub₁ τ₁ τ₂ y m' :=
    ⟨m, h1, fun m' hm' => by
      by_contra hne
      exact h2 m' hne hm'⟩
  apply h
  unfold asyncDecA
  simp only [hu, ↓reduceDIte]
  by_contra hne
  exact h2 _ hne hu.choose_spec.1

end InfoTheory
