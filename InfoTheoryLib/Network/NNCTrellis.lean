/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NNCBlock

/-!
# Noisy network coding: the trellis of the compression indices

The decoder of noisy network coding looks for a message and for a sequence of compression indices
that pass the test in all the blocks. This file bounds the expected number of wrong sequences of
indices, for a wrong message.

## Main definitions

* `nncP`, `nncNx`, `nncTst`: the law of a block, the next state, and the test.
* `nncS`: the set of the nodes whose row in the path differs from the true row.

## Main statements

* `nnc_step`: **one step of the trellis**.
* `nnc_pathCount_le`: the bound on the expected number of paths.
* `nnc_true_le`: the true path fails with small probability.

## Implementation notes

The notes bound the number of paths on pages 19-26, 19-27 and 19-33, assuming that the true indices
are `1`. Since the true index `L_j` depends on the codebook of block `j`, we do not condition on it.
Instead the sum over the labels of block `j` is split by the set `A` of the nodes whose label
differs from the true index, and the bound on the test does not depend on the law of the sequences
of the nodes that are not fresh, so this is harmless. The set `A` is what the next block sees.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Trellis

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {M K : Fin N → ℕ} {px : ∀ k, X k → ℝ} {q : ∀ k, X k → V k → ℝ}
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {τ : ∀ k, X k × Y k → V k → ℝ}

/-- The randomness of a block: the code and the outputs. -/
abbrev NNCΞ (M K : Fin N → ℕ) (n : ℕ) (X Y V : Fin N → Type*) :=
  NNCBlock M K n X V × (Fin n → ∀ k, Y k)

/-- The rows for a tuple of messages and a tuple of indices. -/
def nncBr (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K k)) : ∀ k, NNCBr M K k := fun k => (m k, a k)

/-- The law of a block, given the messages and the previous indices. -/
def nncP (px : ∀ k, X k → ℝ) (q : ∀ k, X k → V k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ)
    (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K k)) (ξ : NNCΞ M K n X Y V) : ℝ :=
  nncBlockLaw px q M K n ξ.1 * seqChan W n (xAt (nncX ξ.1 (nncBr m a))) ξ.2

/-- The compression indices of a block. -/
def nncNx (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K k)) (ξ : NNCΞ M K n X Y V) : ∀ k, Fin (K k) :=
  fun k => pk k (ξ.1 k (m k, a k)).1 (ξ.1 k (m k, a k)).2 (yOf k ξ.2)

/-- The sequences of the nodes for a message `m'`, a previous label `l` and a label `l'`. -/
def nncPathSeq (C : NNCBlock M K n X V) (m' : ∀ k, Fin (M k)) (l l' : ∀ k, Fin (K k)) (k : Fin N) :
    (Fin n → X k) × (Fin n → V k) :=
  ((C k (m' k, l k)).1, (C k (m' k, l k)).2 (l' k))

/-- **Page 19-31 of [elgamal2010].** The test of the decoder `d` in one block: the label of `d` is
its own compression index, which it knows, and the sequences are jointly typical. -/
def nncTst (L : NNCΩ X Y V → ℝ) (d : Fin N) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (m m' : ∀ k, Fin (M k)) (a l l' : ∀ k, Fin (K k)) (ξ : NNCΞ M K n X Y V) : Prop :=
  l' d = nncNx pk m a ξ d ∧ nncTest L d ε (nncPathSeq ξ.1 m' l l') (yOf d ξ.2)

/-- The nodes whose row in the path differs from the true row. -/
def nncS (m m' : ∀ k, Fin (M k)) (a l : ∀ k, Fin (K k)) : Finset (Fin N) :=
  univ.filter fun k => (m' k, l k) ≠ (m k, a k)

/-- The sets of the nodes that can differ from the true row: not `d`, and all the nodes with a wrong
message. -/
def nncAdm (m m' : ∀ k, Fin (M k)) (d : Fin N) : Finset (Finset (Fin N)) :=
  univ.filter fun A => d ∉ A ∧ univ.filter (fun k => m' k ≠ m k) ⊆ A

/-- The exponent of the test. -/
def nncE (L : NNCΩ X Y V → ℝ) (n : ℕ) (d : Fin N) (ε : ℝ) (S : Finset (Fin N)) : ℝ :=
  exp (-(n * (nncJ L S d - ε * nncC L S d)))

lemma nncE_pos (L : NNCΩ X Y V → ℝ) (n : ℕ) (d : Fin N) (ε : ℝ) (S : Finset (Fin N)) :
    0 < nncE L n d ε S := exp_pos _

/-- A tuple of indices from its part on `A` and the rest. -/
def nncMergeIdx (A : Finset (Fin N)) (u : ∀ k : A, Fin (K k)) (L' : ∀ k, Fin (K k)) (k : Fin N) :
    Fin (K k) :=
  if h : k ∈ A then u ⟨k, h⟩ else L' k

open Classical in
/-- The sum of indicators is a number of elements. -/
lemma sum_ind_eq_card {α : Type*} [Fintype α] (P : α → Prop) :
    ∑ a, ind (P a) = ((univ.filter P).card : ℝ) := by
  simp only [ind]
  rw [sum_boole]

open Classical in
/-- The labels with a given set of differences from the true index are counted by their values on
that set. -/
lemma sum_ind_le_card (L' : ∀ k, Fin (K k)) (m m' : ∀ k, Fin (M k)) (A : Finset (Fin N))
    (T : (∀ k, Fin (K k)) → Prop) :
    ∑ l' : ∀ k, Fin (K k), ind (T l' ∧ nncS m m' L' l' = A) ≤
      ∑ u : ∀ k : A, Fin (K k), ind (T (nncMergeIdx A u L')) := by
  rw [sum_ind_eq_card, sum_ind_eq_card]
  norm_cast
  refine card_le_card_of_injOn (fun l' (k : A) => l' k) (fun l' hl' => ?_) (fun a ha b hb hab => ?_)
  · have h : T l' ∧ nncS m m' L' l' = A := by simpa using hl'
    have hm : nncMergeIdx A (fun k : A => l' k) L' = l' := by
      funext k
      by_cases hk : k ∈ A
      · simp [nncMergeIdx, hk]
      · have hk' : k ∉ nncS m m' L' l' := by rwa [h.2]
        simp only [nncS, mem_filter, mem_univ, true_and, not_not] at hk'
        simp only [nncMergeIdx, hk, dite_false]
        exact (Prod.ext_iff.mp hk').2.symm
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [hm]
    exact h.1
  · have ha' : nncS m m' L' a = A := (by simpa using ha : T a ∧ nncS m m' L' a = A).2
    have hb' : nncS m m' L' b = A := (by simpa using hb : T b ∧ nncS m m' L' b = A).2
    funext k
    by_cases hk : k ∈ A
    · exact congrFun hab ⟨k, hk⟩
    · have h₁ : k ∉ nncS m m' L' a := by rwa [ha']
      have h₂ : k ∉ nncS m m' L' b := by rwa [hb']
      simp only [nncS, mem_filter, mem_univ, true_and, not_not] at h₁ h₂
      exact (Prod.ext_iff.mp h₁).2.trans (Prod.ext_iff.mp h₂).2.symm

/-- **One step of the trellis.** Let `Ψ` be a function that depends on the state and on the label
only through the set of differences, up to the bound `ψ`. Then the expected value of `Ψ` over the
labels that pass the test is at most `exp(-n J(S))` times the sum over the sets of differences `A`
of the number of labels with that set times `ψ A`. -/
theorem nnc_step (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    (hq : ∀ k a b, nncRho (nncLaw px W τ) k (a, b) =
      dist (nncLaw px W τ) (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    (hqc : ∀ k, IsChannel (q k)) (d : Fin N) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    {m m' : ∀ k, Fin (M k)} (hd : m' d = m d) {Ψ : (∀ k, Fin (K k)) → (∀ k, Fin (K k)) → ℝ}
    {ψ : Finset (Fin N) → ℝ} (hψ0 : ∀ A, 0 ≤ ψ A) (hΨ : ∀ a l, Ψ a l ≤ ψ (nncS m m' a l))
    (a l : ∀ k, Fin (K k)) :
    ∑ ξ : NNCΞ M K n X Y V, nncP px q W m a ξ * ∑ l', ind (nncTst (nncLaw px W τ) d ε pk m m' a l l'
      ξ) *
        Ψ (nncNx pk m a ξ) l' ≤
      nncE (nncLaw px W τ) n d ε (nncS m m' a l) *
        ∑ A ∈ nncAdm m m' d, (∏ k ∈ A, (K k : ℝ)) * ψ A := by
  classical
  set L := nncLaw px W τ with hLd
  have hP0 : ∀ ξ : NNCΞ M K n X Y V, 0 ≤ nncP px q W m a ξ := fun ξ =>
    mul_nonneg ((nncBlockLaw_isPMF hpx hqc).nonneg _) ((seqChan_isChannel hW n _).nonneg _)
  -- for a fixed block
  have hin : ∀ ξ : NNCΞ M K n X Y V, ∑ l', ind (nncTst L d ε pk m m' a l l' ξ) *
      Ψ (nncNx pk m a ξ) l' ≤ ∑ A ∈ nncAdm m m' d, ψ A * ∑ u : ∀ k : A, Fin (K k),
        ind (nncTest L d ε (nncPathSeq ξ.1 m' l (nncMergeIdx A u (nncNx pk m a ξ))) (yOf d ξ.2)) :=
          by
    intro ξ
    set L' := nncNx pk m a ξ with hL'
    have hpt : ∀ l' : ∀ k, Fin (K k), ind (nncTst L d ε pk m m' a l l' ξ) * Ψ L' l' ≤
        ∑ A ∈ nncAdm m m' d, ψ A * ind (nncTest L d ε (nncPathSeq ξ.1 m' l l') (yOf d ξ.2) ∧
          nncS m m' L' l' = A) := by
      intro l'
      by_cases hT : nncTst L d ε pk m m' a l l' ξ
      · rw [ind_of_pos hT, one_mul]
        have hA : nncS m m' L' l' ∈ nncAdm m m' d := by
          refine mem_filter.mpr ⟨mem_univ _, ?_, fun k hk => ?_⟩
          · simp only [nncS, mem_filter, mem_univ, true_and, not_not]
            exact Prod.ext hd hT.1
          · simp only [nncS, mem_filter, mem_univ, true_and]
            exact fun h => (mem_filter.mp hk).2 (Prod.ext_iff.mp h).1
        refine (hΨ L' l').trans ?_
        refine le_trans ?_ (single_le_sum (f := fun A => ψ A * ind (nncTest L d ε
          (nncPathSeq ξ.1 m' l l') (yOf d ξ.2) ∧ nncS m m' L' l' = A))
          (fun A _ => mul_nonneg (hψ0 A) (ind_nonneg _)) hA)
        rw [ind_of_pos ⟨hT.2, rfl⟩, mul_one]
      · rw [ind_of_neg hT, zero_mul]
        exact sum_nonneg fun A _ => mul_nonneg (hψ0 A) (ind_nonneg _)
    calc _ ≤ ∑ l' : ∀ k, Fin (K k), ∑ A ∈ nncAdm m m' d, ψ A * ind (nncTest L d ε
          (nncPathSeq ξ.1 m' l l') (yOf d ξ.2) ∧ nncS m m' L' l' = A) :=
          sum_le_sum fun l' _ => hpt l'
      _ = ∑ A ∈ nncAdm m m' d, ψ A * ∑ l' : ∀ k, Fin (K k), ind (nncTest L d ε
          (nncPathSeq ξ.1 m' l l') (yOf d ξ.2) ∧ nncS m m' L' l' = A) := by
          rw [sum_comm]
          exact sum_congr rfl fun A _ => (mul_sum _ _ _).symm
      _ ≤ _ := sum_le_sum fun A _ => mul_le_mul_of_nonneg_left
          (sum_ind_le_card L' m m' A fun l' => nncTest L d ε (nncPathSeq ξ.1 m' l l') (yOf d ξ.2))
          (hψ0 A)
  -- the bound on the test
  have htest : ∀ (A : Finset (Fin N)) (u : ∀ k : A, Fin (K k)), ∑ ξ : NNCΞ M K n X Y V,
      nncP px q W m a ξ * ind (nncTest L d ε
        (nncPathSeq ξ.1 m' l (nncMergeIdx A u (nncNx pk m a ξ))) (yOf d ξ.2)) ≤
      nncE L n d ε (nncS m m' a l) := by
    intro A u
    let idx : ∀ k, NNCRow n (K k) (X k) (V k) → (Fin n → Y k) → Fin (K k) := fun k r y =>
      if h : k ∈ A then u ⟨k, h⟩ else pk k r.1 r.2 y
    have h := sum_nncBlock_test_le (M := M) (K := K) hpx hW hτ hq hqc (nncBr m a) (nncBr m' l) idx d
      ε
    have e₁ : (univ.filter fun k => nncBr m' l k ≠ nncBr (K := K) m a k) = nncS m m' a l := rfl
    rw [e₁] at h
    refine le_trans (le_of_eq ?_) h
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun C _ => ?_
    simp only [nncP]
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_assoc]
    congr 3
  have hcard : ∀ A : Finset (Fin N), ∑ _u : ∀ k : A, Fin (K k), (1 : ℝ) = ∏ k ∈ A, (K k : ℝ) := by
    intro A
    rw [sum_const, card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [Nat.cast_prod, Finset.prod_coe_sort A fun k => (K k : ℝ)]
  calc _ ≤ ∑ ξ : NNCΞ M K n X Y V, nncP px q W m a ξ * ∑ A ∈ nncAdm m m' d, ψ A *
        ∑ u : ∀ k : A, Fin (K k), ind (nncTest L d ε
          (nncPathSeq ξ.1 m' l (nncMergeIdx A u (nncNx pk m a ξ))) (yOf d ξ.2)) :=
        sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (hin ξ) (hP0 ξ)
    _ = ∑ A ∈ nncAdm m m' d, ψ A * ∑ u : ∀ k : A, Fin (K k), ∑ ξ : NNCΞ M K n X Y V,
        nncP px q W m a ξ * ind (nncTest L d ε
          (nncPathSeq ξ.1 m' l (nncMergeIdx A u (nncNx pk m a ξ))) (yOf d ξ.2)) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun A _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun u _ => sum_congr rfl fun ξ _ => ?_
        ring
    _ ≤ ∑ A ∈ nncAdm m m' d, ψ A * ∑ _u : ∀ k : A, Fin (K k), nncE L n d ε (nncS m m' a l) :=
        sum_le_sum fun A _ => mul_le_mul_of_nonneg_left
          (sum_le_sum fun u _ => htest A u) (hψ0 A)
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun A _ => ?_
        rw [← mul_one (nncE L n d ε (nncS m m' a l)), ← mul_sum, hcard]
        ring

/-- The number of sets of differences is at most `2 ^ N`. -/
lemma card_nncAdm_le (m m' : ∀ k, Fin (M k)) (d : Fin N) :
    ((nncAdm m m' d).card : ℝ) ≤ 2 ^ N := by
  classical
  have h : (nncAdm m m' d).card ≤ (univ : Finset (Finset (Fin N))).card := card_le_card (subset_univ
    _)
  have e : (univ : Finset (Finset (Fin N))).card = 2 ^ N := by
    rw [card_univ, Fintype.card_finset, Fintype.card_fin]
  rw [e] at h
  exact_mod_cast h

/-- The product over a set of nodes is at most the product over all the nodes. -/
lemma prod_K_le [∀ k, NeZero (K k)] (A : Finset (Fin N)) :
    ∏ k ∈ A, (K k : ℝ) ≤ ∏ k, (K k : ℝ) := by
  have h : ∏ k ∈ A, K k ≤ ∏ k, K k :=
    prod_le_prod_of_subset_of_one_le (subset_univ A) fun k _ _ => NeZero.pos (K k)
  exact_mod_cast h

variable [∀ k, NeZero (K k)]

/-- The expected number of paths of a trellis of `t` blocks. -/
def nncCount (L : NNCΩ X Y V → ℝ) (px : ∀ k, X k → ℝ) (q : ∀ k, X k → V k → ℝ)
    (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (d : Fin N) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (m m' : ∀ k, Fin (M k)) (dξ : NNCΞ M K n X Y V) (t : ℕ) (a l : ∀ k, Fin (K k)) : ℝ :=
  pathCount (nncP px q W m) (nncNx pk m) dξ (nncTst L d ε pk m m') t a l

/-- **The bound on the expected number of paths.** Assume that `exp(-n J(A))` times the number of
labels with the set of differences `A` is at most `γ`, for all the sets `A`. Then the expected
number of paths of `t + 1` blocks is at most `exp(-n J(S)) (2 ^ N γ) ^ t 2 ^ N ∏ K_k`. -/
theorem nnc_pathCount_le (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    (hq : ∀ k a b, nncRho (nncLaw px W τ) k (a, b) =
      dist (nncLaw px W τ) (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    (hqc : ∀ k, IsChannel (q k)) (d : Fin N) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    {m m' : ∀ k, Fin (M k)} (hd : m' d = m d) (dξ : NNCΞ M K n X Y V) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ A ∈ nncAdm m m' d, nncE (nncLaw px W τ) n d ε A * ∏ k ∈ A, (K k : ℝ) ≤ γ) :
    ∀ (t : ℕ) (a l : ∀ k, Fin (K k)), nncCount (nncLaw px W τ) px q W d ε pk m m' dξ (t + 1) a l ≤
      nncE (nncLaw px W τ) n d ε (nncS m m' a l) *
        ((2 ^ N * γ) ^ t * (2 ^ N * ∏ k, (K k : ℝ))) := by
  classical
  have hK0 : 0 ≤ ∏ k, (K k : ℝ) := prod_nonneg fun k _ => Nat.cast_nonneg _
  have hKA : ∀ A : Finset (Fin N), 0 ≤ ∏ k ∈ A, (K k : ℝ) := fun A =>
    prod_nonneg fun k _ => Nat.cast_nonneg _
  intro t
  induction t with
  | zero =>
    intro a l
    rw [nncCount, pathCount_succ]
    have hzero : ∀ a' l', pathCount (nncP px q W m) (nncNx pk m) dξ
        (nncTst (nncLaw px W τ) d ε pk m m') 0 a' l' = 1 := by
      intro a' l'
      simp only [pathCount, runProb]
      simp [ind_of_pos]
    simp_rw [hzero]
    have h := nnc_step (M := M) hpx hW hτ hq hqc d ε pk hd (Ψ := fun _ _ => 1) (ψ := fun _ => 1)
      (fun _ => zero_le_one) (fun _ _ => le_rfl) a l
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (nncE_pos _ _ _ _ _).le)
    simp only [mul_one, pow_zero, one_mul]
    calc _ ≤ ∑ _A ∈ nncAdm m m' d, ∏ k, (K k : ℝ) := sum_le_sum fun A _ => prod_K_le A
      _ = ((nncAdm m m' d).card : ℝ) * ∏ k, (K k : ℝ) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (card_nncAdm_le m m' d) hK0
  | succ t ih =>
    intro a l
    set Λ := (2 ^ N * γ) ^ t * (2 ^ N * ∏ k, (K k : ℝ)) with hΛ
    have hΛ0 : 0 ≤ Λ := mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hγ0) _)
      (mul_nonneg (by positivity) hK0)
    rw [nncCount, pathCount_succ]
    have h := nnc_step (M := M) hpx hW hτ hq hqc d ε pk hd
      (Ψ := fun a l => pathCount (nncP px q W m) (nncNx pk m) dξ
        (nncTst (nncLaw px W τ) d ε pk m m') (t + 1) a l)
      (ψ := fun A => nncE (nncLaw px W τ) n d ε A * Λ)
      (fun A => mul_nonneg (nncE_pos _ _ _ _ _).le hΛ0) (fun a l => ih a l) a l
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (nncE_pos _ _ _ _ _).le)
    calc _ ≤ ∑ _A ∈ nncAdm m m' d, γ * Λ := sum_le_sum fun A hA => by
          have := mul_le_mul_of_nonneg_right (hγ A hA) hΛ0
          calc _ = (nncE (nncLaw px W τ) n d ε A * ∏ k ∈ A, (K k : ℝ)) * Λ := by ring
            _ ≤ _ := this
      _ = ((nncAdm m m' d).card : ℝ) * (γ * Λ) := by simp
      _ ≤ 2 ^ N * (γ * Λ) := mul_le_mul_of_nonneg_right (card_nncAdm_le m m' d)
          (mul_nonneg hγ0 hΛ0)
      _ = _ := by
          rw [hΛ, pow_succ]
          ring

omit [∀ k, NeZero (K k)] in
/-- **The true path.** If the tuple of the true rows is typical, the true path passes the test. -/
lemma nncTst_true {m : ∀ k, Fin (M k)} {L : NNCΩ X Y V → ℝ} {d : Fin N} {ε : ℝ}
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (a : ∀ k, Fin (K k)) (ξ : NNCΞ M K n X Y V)
    (h : ¬ nncBad L ε (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2)) :
    nncTst L d ε pk m m a a (nncNx pk m a ξ) ξ := by
  refine ⟨rfl, ?_⟩
  have hm : nncFull (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2) ∈
      robustTypicalSet L n ε := not_not.mp h
  exact comp_mem_robustTypicalSet hm fun ω : NNCΩ X Y V => (ω.1, ω.2.1 d, ω.2.2)

omit [∀ k, NeZero (K k)] in
/-- **The probability that the tuple of a block is not typical**, for any state. -/
lemma nnc_true_le (hpx : ∀ k, IsPMF (px k)) (hqc : ∀ k, IsChannel (q k)) {L : NNCΩ X Y V → ℝ}
    {ε : ℝ} (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K k)) :
    ∑ ξ : NNCΞ M K n X Y V, nncP px q W m a ξ *
      ind (nncBad L ε (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2)) =
    nncHyb px W (fun k => nncSel (seqChan (q k) n) (K k) (pk k)) (nncBad L ε) := by
  rw [← sum_nncBlock_bad_eq hpx hqc (nncBr m a) pk, Fintype.sum_prod_type]
  refine sum_congr rfl fun C _ => ?_
  simp only [nncP]
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  ring

end Trellis

end InfoTheory
