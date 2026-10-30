/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.OptimalLength

/-!
# Huffman codes

Huffman's algorithm builds an optimal binary prefix code by repeatedly merging the two least
likely symbols. We formalize it at the level of codeword lengths: `huffmanLengths w` are the depths
of the leaves of the Huffman tree for the weights `w`, and `huffmanCost w = ∑ᵢ wᵢ lᵢ` is its
weighted length. A binary prefix code with these lengths exists by the Kraft inequality
(`huffmanCode`); since only the lengths matter, it has the same expected length as the code read
off the tree.

## Main definitions

* `huffmanMerge s`: merge the first two weights of `s`.
* `huffmanCost n w`, `huffmanLengths n w`: the cost and the codeword lengths of the Huffman code
  for the weights `w : Fin n → ℝ`.
* `huffmanCode p`: a binary Huffman code for a distribution `p` on a finite type.

## Main statements

* `kraft_huffmanLengths`, `cost_huffmanLengths`: the Huffman lengths satisfy the Kraft inequality
  with equality, and have weighted length `huffmanCost`.
* `cost_comp_swap`, `kraft_update_of_unique_max`, `exists_canonical_lengths`: Lemma 5.8.1, the
  exchange and trimming arguments: some optimal lengths give the two least likely symbols the
  same, maximal, length.
* `huffmanCost_le`: Theorem 5.8.1 at the level of lengths, for any non-negative weights (also
  Section 5.7, comment 2).
* `huffmanCode_optimal`: Theorem 5.8.1, Huffman coding is optimal among binary uniquely
  decodable codes.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 5.6–5.8
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-- Merge the first two weights: `(s₀ + s₁, s₂, …, sₙ₊₁)`. -/
def huffmanMerge {n : ℕ} (s : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (s 0 + s 1) fun i : Fin n => s i.succ.succ

/-- The cost (weighted codeword length) of the Huffman code for the weights `w`: sort the weights,
merge the two smallest, and add their sum to the cost of the reduced problem. -/
def huffmanCost : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | n + 2, w => (w ∘ Tuple.sort w) 0 + (w ∘ Tuple.sort w) 1 +
      huffmanCost (n + 1) (huffmanMerge (w ∘ Tuple.sort w))

/-- The codeword lengths of the Huffman code for the weights `w`: the two least likely symbols get
the length of their merged symbol plus one. -/
def huffmanLengths : (n : ℕ) → (Fin n → ℝ) → Fin n → ℕ
  | 0, _ => fun _ => 0
  | 1, _ => fun _ => 0
  | n + 2, w =>
    (Fin.cons (huffmanLengths (n + 1) (huffmanMerge (w ∘ Tuple.sort w)) 0 + 1)
      (Fin.cons (huffmanLengths (n + 1) (huffmanMerge (w ∘ Tuple.sort w)) 0 + 1)
        fun i : Fin n => huffmanLengths (n + 1) (huffmanMerge (w ∘ Tuple.sort w)) i.succ) :
      Fin (n + 2) → ℕ) ∘ (Tuple.sort w).symm

lemma huffmanCost_succ_succ {n : ℕ} (w : Fin (n + 2) → ℝ) :
    huffmanCost (n + 2) w = (w ∘ Tuple.sort w) 0 + (w ∘ Tuple.sort w) 1 +
      huffmanCost (n + 1) (huffmanMerge (w ∘ Tuple.sort w)) := by
  rw [huffmanCost]

/-- To compute `huffmanCost`, any permutation sorting the weights may be used. -/
lemma huffmanCost_of_monotone {n : ℕ} (w : Fin (n + 2) → ℝ) (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : Monotone (w ∘ σ)) :
    huffmanCost (n + 2) w = (w ∘ σ) 0 + (w ∘ σ) 1 + huffmanCost (n + 1) (huffmanMerge (w ∘ σ)) := by
  rw [huffmanCost_succ_succ, (Tuple.comp_sort_eq_comp_iff_monotone.2 hσ).symm]

/-- The cost of a single symbol is `0`. -/
@[simp] lemma huffmanCost_one (w : Fin 1 → ℝ) : huffmanCost 1 w = 0 := rfl

lemma huffmanMerge_eq {n : ℕ} (s : Fin (n + 2) → ℝ) :
    huffmanMerge s = Matrix.vecCons (s 0 + s 1) fun i : Fin n => s i.succ.succ := rfl

/-- One step of Huffman's algorithm, for computations: if `σ` sorts the weights, the two smallest
weights `w (σ 0) + w (σ 1) = a` are merged into the reduced weights `v`. -/
lemma huffmanCost_step {n : ℕ} (w : Fin (n + 2) → ℝ) (σ : Equiv.Perm (Fin (n + 2)))
    (hσ : Monotone (w ∘ σ)) {a : ℝ} (ha : w (σ 0) + w (σ 1) = a) {v : Fin (n + 1) → ℝ}
    (hv : huffmanMerge (w ∘ σ) = v) : huffmanCost (n + 2) w = a + huffmanCost (n + 1) v := by
  rw [huffmanCost_of_monotone w σ hσ, hv, ← ha]
  rfl

lemma huffmanMerge_nonneg {n : ℕ} {s : Fin (n + 2) → ℝ} (hs : ∀ i, 0 ≤ s i) (i : Fin (n + 1)) :
    0 ≤ huffmanMerge s i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [huffmanMerge, add_nonneg (hs 0) (hs 1)]
  · simp [huffmanMerge, hs]

/-! ### The Huffman lengths -/

/-- The Huffman lengths satisfy the Kraft inequality with equality: the Huffman tree is complete. -/
theorem kraft_huffmanLengths (n : ℕ) (w : Fin (n + 1) → ℝ) :
    ∑ i, (1 / 2 : ℝ) ^ huffmanLengths (n + 1) w i = 1 := by
  induction n with
  | zero => simp [huffmanLengths]
  | succ n ih =>
    set l' := huffmanLengths (n + 1) (huffmanMerge (w ∘ Tuple.sort w))
    have h : ∑ i, (1 / 2 : ℝ) ^ huffmanLengths (n + 2) w i = ∑ j, (1 / 2 : ℝ) ^ l' j := by
      rw [huffmanLengths, ← Equiv.sum_comp (Tuple.sort w)]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_succ (f := fun j => (1 / 2 : ℝ) ^ l' j)]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one, Fin.cons_one]
      rw [pow_succ]
      ring
    rw [h, ih]

/-- The Huffman lengths have weighted length `huffmanCost`. -/
theorem cost_huffmanLengths (n : ℕ) (w : Fin n → ℝ) :
    ∑ i, w i * huffmanLengths n w i = huffmanCost n w := by
  induction n with
  | zero => simp [huffmanCost]
  | succ n ih =>
    cases n with
    | zero => simp [huffmanLengths, huffmanCost]
    | succ n =>
      rw [huffmanLengths, huffmanCost, ← ih, ← Equiv.sum_comp (Tuple.sort w)]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.cons_succ, huffmanMerge, Fin.succ_zero_eq_one]
      push_cast
      ring

/-! ### Lemma 5.8.1: properties of optimal codeword lengths -/

/-- **Lemma 5.8.1, swapping, (5.62)–(5.64).** Exchanging the codeword lengths of the symbols `a`
and `b` changes the weighted length by `(s_a - s_b)(l_b - l_a)`. -/
lemma cost_comp_swap {n : ℕ} (s : Fin n → ℝ) (l : Fin n → ℕ) (a b : Fin n) :
    ∑ i, s i * l (Equiv.swap a b i) = ∑ i, s i * l i + (s a - s b) * (l b - l a) := by
  classical
  by_cases hab : a = b
  · subst hab; simp
  have h1 : ∑ i, s i * l (Equiv.swap a b i) = ∑ i, s (Equiv.swap a b i) * l i := by
    rw [← Equiv.sum_comp (Equiv.swap a b) (fun i => s (Equiv.swap a b i) * l i)]
    simp
  rw [h1, ← sub_eq_iff_eq_add', ← sum_sub_distrib]
  rw [← sum_subset (subset_univ {a, b}) (fun i _ hi => by
    simp only [mem_insert, mem_singleton, not_or] at hi
    rw [Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, sub_self]), sum_pair hab]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

lemma kraft_comp_perm {n : ℕ} (l : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    ∑ i, (1 / 2 : ℝ) ^ l (σ i) = ∑ i, (1 / 2 : ℝ) ^ l i :=
  Equiv.sum_comp σ fun i => (1 / 2 : ℝ) ^ l i

/-- **Lemma 5.8.1, trimming.** If the longest codeword is unique, it can be shortened by one digit
without violating the (binary) Kraft inequality. Hence in an optimal code the two longest
codewords have the same length. -/
lemma kraft_update_of_unique_max {n : ℕ} (l : Fin n → ℕ) (a : Fin n) (ha : 1 ≤ l a)
    (hmax : ∀ j, j ≠ a → l j < l a) (hk : ∑ i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∑ i, (1 / 2 : ℝ) ^ Function.update l a (l a - 1) i ≤ 1 := by
  classical
  set L := l a
  -- Scale by `2^L`: `∑ 2^{L - lᵢ} ≤ 2^L`, where all terms but the one at `a` are even.
  have hscale : ∀ i, (1 / 2 : ℝ) ^ l i = (2 ^ (L - l i) : ℕ) / 2 ^ L := by
    intro i
    have hi : l i ≤ L := by
      by_cases h : i = a
      · rw [h]
      · exact (hmax i h).le
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ _ two_ne_zero hi, one_div_pow]
    field_simp
  have hsplit : ∀ f : Fin n → ℝ, ∑ i, f i = f a + ∑ i ∈ univ.erase a, f i := fun f =>
    (add_sum_erase _ _ (mem_univ a)).symm
  set T : ℕ := ∑ i ∈ univ.erase a, 2 ^ (L - l i - 1)
  have hT : ∑ i ∈ univ.erase a, (2 : ℕ) ^ (L - l i) = 2 * T := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have := hmax i (ne_of_mem_erase hi)
    rw [← pow_succ']
    congr 1
    omega
  have hk' : 2 * T + 1 ≤ 2 ^ L := by
    have h1 : ((2 * T + 1 : ℕ) : ℝ) / 2 ^ L ≤ 1 := by
      rw [hsplit, hscale a, Nat.sub_self, pow_zero] at hk
      simp only [hscale] at hk
      rw [← sum_div, ← add_div, ← Nat.cast_sum, hT] at hk
      push_cast at hk ⊢
      rwa [add_comm] at hk
    rw [div_le_one (by positivity)] at h1
    exact_mod_cast h1
  have hL : 2 ^ L = 2 * 2 ^ (L - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hsplit]
  simp only [Function.update_self]
  have hrest : ∑ i ∈ univ.erase a, (1 / 2 : ℝ) ^ Function.update l a (L - 1) i =
      ∑ i ∈ univ.erase a, (1 / 2 : ℝ) ^ l i :=
    sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [hrest]
  simp only [hscale]
  rw [← sum_div, ← Nat.cast_sum, hT]
  have hLr : (2 : ℝ) ^ L = 2 * 2 ^ (L - 1) := by exact_mod_cast hL
  have h2 : (1 / 2 : ℝ) ^ (L - 1) = 2 / 2 ^ L := by
    rw [hLr, one_div_pow]; field_simp
  rw [h2, ← add_div, div_le_one (by positivity)]
  exact_mod_cast (by omega : 2 + 2 * T ≤ 2 ^ L)

/-- **Lemma 5.8.1.** For weights `s₀ ≤ s₁ ≤ ⋯` and lengths satisfying the Kraft inequality, there
are lengths `m`, still satisfying the Kraft inequality and with no larger weighted length, in
which the two least likely symbols `0` and `1` have the same maximal length (at least one). -/
theorem exists_canonical_lengths {n : ℕ} (s : Fin (n + 2) → ℝ) (hs : Monotone s)
    (hs0 : ∀ i, 0 ≤ s i) (l : Fin (n + 2) → ℕ) (hk : ∑ i, (1 / 2 : ℝ) ^ l i ≤ 1) :
    ∃ m : Fin (n + 2) → ℕ, ∑ i, (1 / 2 : ℝ) ^ m i ≤ 1 ∧
      ∑ i, s i * m i ≤ ∑ i, s i * l i ∧ m 0 = m 1 ∧ 1 ≤ m 0 ∧ ∀ i, m i ≤ m 0 := by
  classical
  -- Step 1 (swapping): give a longest codeword to symbol `0`.
  obtain ⟨j₀, -, hj₀⟩ := exists_max_image univ l univ_nonempty
  set l₁ := l ∘ Equiv.swap 0 j₀
  have hl₁k : ∑ i, (1 / 2 : ℝ) ^ l₁ i ≤ 1 := by rwa [show l₁ = l ∘ Equiv.swap 0 j₀ from rfl,
    Function.comp_def, kraft_comp_perm]
  have hl₁c : ∑ i, s i * l₁ i ≤ ∑ i, s i * l i := by
    rw [show l₁ = l ∘ Equiv.swap 0 j₀ from rfl]
    simp only [Function.comp_apply]
    rw [cost_comp_swap]
    have h1 : s 0 ≤ s j₀ := hs (Fin.zero_le _)
    have h2 : (l 0 : ℝ) ≤ l j₀ := by exact_mod_cast hj₀ 0 (mem_univ _)
    nlinarith
  have hl₁max : ∀ i, l₁ i ≤ l₁ 0 := fun i => by
    simp only [l₁, Function.comp_apply, Equiv.swap_apply_left]
    exact hj₀ _ (mem_univ _)
  -- Step 2 (trimming): shorten a unique longest codeword until the maximum is attained twice.
  have step2 : ∀ v (m : Fin (n + 2) → ℕ), m 0 = v → (∀ i, m i ≤ m 0) →
      ∑ i, (1 / 2 : ℝ) ^ m i ≤ 1 →
      ∃ m' : Fin (n + 2) → ℕ, ∑ i, (1 / 2 : ℝ) ^ m' i ≤ 1 ∧ ∑ i, s i * m' i ≤ ∑ i, s i * m i ∧
        (∀ i, m' i ≤ m' 0) ∧ ∃ j, j ≠ 0 ∧ m' j = m' 0 := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro m hv hmax hk
      by_cases hex : ∃ j, j ≠ 0 ∧ m j = m 0
      · exact ⟨m, hk, le_rfl, hmax, hex⟩
      push Not at hex
      have hlt : ∀ j, j ≠ 0 → m j < m 0 := fun j hj => lt_of_le_of_ne (hmax j) (hex j hj)
      have h1 : 1 ≤ m 0 := by
        have := hlt 1 (by simp)
        omega
      set m₂ := Function.update m 0 (m 0 - 1)
      have hk₂ := kraft_update_of_unique_max m 0 h1 hlt hk
      have hc₂ : ∑ i, s i * m₂ i ≤ ∑ i, s i * m i := by
        refine sum_le_sum fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          simp only [m₂, Function.update_self]
          have : ((m 0 - 1 : ℕ) : ℝ) ≤ m 0 := by exact_mod_cast Nat.sub_le _ _
          exact mul_le_mul_of_nonneg_left this (hs0 0)
        · simp [m₂, Function.update_of_ne hi]
      have hmax₂ : ∀ i, m₂ i ≤ m₂ 0 := fun i => by
        by_cases hi : i = 0
        · rw [hi]
        · simp only [m₂, Function.update_of_ne hi, Function.update_self]
          have := hlt i hi
          omega
      obtain ⟨m', hk', hc', hmax', hj⟩ :=
        ih (m 0 - 1) (by omega) m₂ (by simp [m₂]) hmax₂ hk₂
      exact ⟨m', hk', hc'.trans hc₂, hmax', hj⟩
  obtain ⟨m, hmk, hmc, hmmax, j, hj0, hjm⟩ := step2 _ l₁ rfl hl₁max hl₁k
  -- Step 3 (rearranging): give the other longest codeword to symbol `1`.
  set m₃ := m ∘ Equiv.swap 1 j
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp
  have hm₃0 : m₃ 0 = m 0 := by
    simp only [m₃, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)]
  have hm₃1 : m₃ 1 = m 0 := by simp [m₃, hjm]
  refine ⟨m₃, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show m₃ = m ∘ Equiv.swap 1 j from rfl, Function.comp_def, kraft_comp_perm]; exact hmk
  · refine le_trans ?_ (hmc.trans hl₁c)
    simp only [m₃, Function.comp_apply]
    rw [cost_comp_swap]
    have h1 : s 1 ≤ s j := hs (Fin.one_le_of_ne_zero hj0)
    have h2 : (m 1 : ℝ) ≤ m j := by rw [hjm]; exact_mod_cast hmmax 1
    nlinarith
  · rw [hm₃0, hm₃1]
  · rw [hm₃0]
    by_contra! h
    have hz : ∀ i, m i = 0 := fun i => by have := hmmax i; omega
    have := hmk
    simp only [hz, pow_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at this
    push_cast at this
    linarith
  · intro i
    rw [hm₃0]
    exact hmmax _

/-! ### Optimality of Huffman coding -/

/-- **Theorem 5.8.1 (lengths).** For non-negative weights `w`, the Huffman cost is at most the
weighted length `∑ᵢ wᵢ lᵢ` of any lengths satisfying the binary Kraft inequality. The weights
need not sum to one (Section 5.7, comment 2). -/
theorem huffmanCost_le (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (l : Fin n → ℕ)
    (hl : ∑ i, (1 / 2 : ℝ) ^ l i ≤ 1) : huffmanCost n w ≤ ∑ i, w i * l i := by
  induction n with
  | zero => simp [huffmanCost]
  | succ n ih =>
    cases n with
    | zero => simpa using mul_nonneg (hw 0) (Nat.cast_nonneg (l 0))
    | succ n =>
      set σ := Tuple.sort w
      set s := w ∘ σ
      have hs : Monotone s := Tuple.monotone_sort w
      have hs0 : ∀ i, 0 ≤ s i := fun i => hw _
      have hcost : ∑ i, w i * l i = ∑ i, s i * (l ∘ σ) i :=
        (Equiv.sum_comp σ fun i => w i * l i).symm
      have hk : ∑ i, (1 / 2 : ℝ) ^ (l ∘ σ) i ≤ 1 := by
        rwa [Function.comp_def, kraft_comp_perm]
      obtain ⟨m, hmk, hmc, hm01, hm1, -⟩ := exists_canonical_lengths s hs hs0 _ hk
      -- The lengths for the merged problem.
      set m' : Fin (n + 1) → ℕ := Fin.cons (m 0 - 1) fun i => m i.succ.succ
      have hm'k : ∑ i, (1 / 2 : ℝ) ^ m' i ≤ 1 := by
        refine le_trans (le_of_eq ?_) hmk
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [m', Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one, ← hm01]
        have : (1 / 2 : ℝ) ^ (m 0 - 1) = (1 / 2) ^ m 0 + (1 / 2) ^ m 0 := by
          rw [← two_mul, show m 0 = m 0 - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel]
          ring
        rw [this]
        ring
      have hm'c : ∑ i, huffmanMerge s i * m' i = ∑ i, s i * m i - s 0 - s 1 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [m', huffmanMerge, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one, ← hm01]
        rw [Nat.cast_sub hm1]
        push_cast
        ring
      have hih := ih (huffmanMerge s) (huffmanMerge_nonneg hs0) m' hm'k
      rw [huffmanCost_succ_succ, hcost]
      change s 0 + s 1 + huffmanCost (n + 1) (huffmanMerge s) ≤ _
      linarith

/-! ### Huffman codes for distributions -/

variable {X : Type*} [Fintype X]

/-- The Huffman codeword lengths for a distribution `p` on a finite type, computed through an
enumeration of the symbols. -/
def huffmanLengthsOf (p : X → ℝ) (x : X) : ℕ :=
  huffmanLengths (Fintype.card X) (p ∘ (Fintype.equivFin X).symm) (Fintype.equivFin X x)

lemma kraft_huffmanLengthsOf [Nonempty X] (p : X → ℝ) :
    ∑ x, (1 / 2 : ℝ) ^ huffmanLengthsOf p x = 1 := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card X = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    Fintype.card_pos).symm⟩
  rw [← (Fintype.equivFin X).symm.sum_comp]
  simp only [huffmanLengthsOf, Equiv.apply_symm_apply]
  generalize (p ∘ (Fintype.equivFin X).symm) = w
  revert w
  rw [hn]
  exact kraft_huffmanLengths n

lemma cost_huffmanLengthsOf (p : X → ℝ) :
    ∑ x, p x * huffmanLengthsOf p x =
      huffmanCost (Fintype.card X) (p ∘ (Fintype.equivFin X).symm) := by
  rw [← cost_huffmanLengths, ← (Fintype.equivFin X).symm.sum_comp]
  simp [huffmanLengthsOf]

/-- A binary Huffman code for the distribution `p`: a prefix code over `Bool` whose codeword
lengths are the Huffman lengths. -/
def huffmanCode [Nonempty X] (p : X → ℝ) : X → List Bool :=
  Classical.choose (exists_prefixCode_of_kraft (α := Bool) (huffmanLengthsOf p)
    (by rw [Fintype.card_bool]; push_cast; exact (kraft_huffmanLengthsOf p).le))

lemma huffmanCode_spec [Nonempty X] (p : X → ℝ) :
    IsPrefixCode (huffmanCode p) ∧ ∀ x, (huffmanCode p x).length = huffmanLengthsOf p x :=
  Classical.choose_spec (exists_prefixCode_of_kraft (α := Bool) (huffmanLengthsOf p)
    (by rw [Fintype.card_bool]; push_cast; exact (kraft_huffmanLengthsOf p).le))

/-- The Huffman code is an instantaneous code. -/
lemma huffmanCode_isPrefixCode [Nonempty X] (p : X → ℝ) : IsPrefixCode (huffmanCode p) :=
  (huffmanCode_spec p).1

/-- The expected length of the Huffman code is the Huffman cost. -/
lemma expectedLength_huffmanCode [Nonempty X] (p : X → ℝ) :
    expectedLength p (huffmanCode p) =
      huffmanCost (Fintype.card X) (p ∘ (Fintype.equivFin X).symm) := by
  rw [expectedLength, ← cost_huffmanLengthsOf]
  simp [(huffmanCode_spec p).2]

/-- **Theorem 5.8.1.** Huffman coding is optimal: if `C*` is the Huffman code and `C'` is any other
binary uniquely decodable code (in particular any prefix code), then `L(C*) ≤ L(C')`. -/
theorem huffmanCode_optimal [Nonempty X] {p : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    {C' : X → List Bool} (hC' : IsUniquelyDecodableCode C') :
    expectedLength p (huffmanCode p) ≤ expectedLength p C' := by
  rw [expectedLength_huffmanCode, expectedLength]
  have hk := kraft_of_isUniquelyDecodableCode hC'
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hk
  have := huffmanCost_le (Fintype.card X) (p ∘ (Fintype.equivFin X).symm) (fun i => hp _)
    (fun i => (C' ((Fintype.equivFin X).symm i)).length) (by
      rw [(Fintype.equivFin X).symm.sum_comp (fun x => (1 / 2 : ℝ) ^ (C' x).length)]
      exact hk)
  simp only [Function.comp_apply] at this
  rwa [(Fintype.equivFin X).symm.sum_comp (fun x => p x * ((C' x).length : ℝ))] at this

/-- **Theorem 5.8.1 (codes).** For non-negative weights `w`, the Huffman cost is at most the
weighted length of any uniquely decodable code over a binary alphabet. In particular a code whose
weighted length equals the Huffman cost is optimal. -/
theorem huffmanCost_le_expectedLength {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) {α : Type*}
    [Fintype α] (hα : Fintype.card α = 2) {C : Fin n → List α} (hC : IsUniquelyDecodableCode C) :
    huffmanCost n w ≤ expectedLength w C := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  have hk := kraft_of_isUniquelyDecodableCode hC
  rw [hα] at hk
  push_cast at hk
  exact huffmanCost_le n w hw _ hk

end InfoTheory
