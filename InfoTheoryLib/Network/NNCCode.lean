/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NNCTrellis
public import InfoTheoryLib.Network.RelayMarkov

/-!
# Noisy network coding: the code of all the blocks

A code for each block is fixed, and a message is sent over all the blocks. In block `j`, node `k`
sends the sequence of its row for its message and for the compression index of block `j - 1`. At the
end, each decoder looks for a tuple of messages and for compression indices that pass its test in
all the blocks.

## Main definitions

* `nncStK`: the state of a node after `j` blocks.
* `nncCode`: the code of all the blocks.

## Main statements

* `nncCode_law`: the law of the code as a product over the blocks.
* `nncCode_dec_eq`: the decoder finds the messages if the true path passes the tests, and no path
  with other messages does.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Code

variable {N n : ℕ} {X Y V : Fin N → Type*} {M K : Fin N → ℕ}

/-- The state of node `k` after `j` blocks: its compression index of block `j - 1`. -/
def nncStK [∀ k, NeZero (K k)] (k : Fin N)
    (pkk : (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Ck : ℕ → NNCBr M K k → NNCRow n (K k) (X k) (V k)) (mk : Fin (M k))
    (Z : ℕ → Fin n → Y k) : ℕ → Fin (K k)
  | 0 => 0
  | j + 1 => pkk (Ck j (mk, nncStK k pkk Ck mk Z j)).1 (Ck j (mk, nncStK k pkk Ck mk Z j)).2 (Z j)

lemma nncStK_congr [∀ k, NeZero (K k)] (k : Fin N)
    (pkk : (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Ck : ℕ → NNCBr M K k → NNCRow n (K k) (X k) (V k)) (mk : Fin (M k))
    {Z Z' : ℕ → Fin n → Y k} : ∀ j, (∀ j', j' < j → Z j' = Z' j') →
      nncStK k pkk Ck mk Z j = nncStK k pkk Ck mk Z' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [nncStK]
    rw [nncStK_congr k pkk Ck mk j fun j' hj' => h j' (hj'.trans (Nat.lt_succ_self j)),
      h j (Nat.lt_succ_self j)]

variable [∀ k, NeZero (K k)]

/-- **Page 19-31 of [elgamal2010].** A tuple of messages and a path of labels pass the test of node
`k`, for its message `mk` and its received blocks `Z`. The first label is `0`. -/
def nncPass [∀ k, Fintype (X k)] [∀ k, Fintype (V k)] [∀ k, Fintype (Y k)]
    (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Cs : ℕ → NNCBlock M K n X V) (t : ℕ) (k : Fin N) (mk : Fin (M k)) (Z : ℕ → Fin n → Y k)
    (m' : ∀ k, Fin (M k)) (ℓ : Fin t → ∀ k, Fin (K k)) : Prop :=
  m' k = mk ∧ ∀ j : Fin t, ℓ j k = nncStK k (pk k) (fun i => Cs i k) mk Z (j + 1) ∧
    nncTest L k ε (nncPathSeq (Cs j) m' (pathPrev 0 ℓ j) (ℓ j)) (Z j)

open Classical in
/-- The unique tuple of messages with a property, or a default value. -/
def nncDecOf (hM : ∀ k, 0 < M k) (P : (∀ k, Fin (M k)) → Prop) : ∀ j, Fin (M j) :=
  if h : ∃! m', P m' then Classical.choose h else fun j => ⟨0, hM j⟩

omit [∀ k, NeZero (K k)] in
lemma nncDecOf_eq (hM : ∀ k, 0 < M k) {P : (∀ k, Fin (M k)) → Prop} {m : ∀ k, Fin (M k)} (hP : P m)
    (hu : ∀ m', P m' → m' = m) : nncDecOf hM P = m := by
  have h : ∃! m', P m' := ⟨m, hP, hu⟩
  simp only [nncDecOf, h, dite_true]
  exact hu _ (Classical.choose_spec h).1

variable [NeZero n]

/-- **Pages 19-29 to 19-31 of [elgamal2010].** The code of `t` blocks. Its length `N'` can be longer
than `t n`: the rest is not used. -/
def nncCode [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)]
    (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Cs : ℕ → NNCBlock M K n X V) (t : ℕ) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k) (N' : ℕ) :
    DMNCode M N' X Y where
  enc k i mk y := (Cs (i / n) k (mk, nncStK k (pk k) (fun j => Cs j k) mk
    (getBlock (dY k) y) (i / n))).1 ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩
  dec k mk y := nncDecOf hM fun m' => ∃ ℓ, nncPass L ε pk Cs t k mk (getBlock (dY k) y) m' ℓ

/-! ### The state of the nodes -/

section State

variable {Ξ : Type*}

/-- The received block of a node, from the outputs of the blocks. -/
def nncZOf (Z : ℕ → Fin n → ∀ k, Y k) (k : Fin N) (j : ℕ) : Fin n → Y k := yOf k (Z j)

omit [NeZero n] in
/-- The state of all the nodes is the tuple of the states of the nodes. -/
lemma stOf_nncNx (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (m : ∀ k, Fin (M k)) (ξ : ℕ → NNCΞ M K n X Y V) : ∀ (j : ℕ) (k : Fin N),
    stOf (nncNx pk m) 0 ξ j k = nncStK k (pk k) (fun i => (ξ i).1 k) (m k)
      (fun i => yOf k (ξ i).2) j
  | 0, _ => rfl
  | j + 1, k => by
    simp only [stOf, nncNx, nncStK]
    rw [stOf_nncNx pk m ξ j k]

end State

end Code

/-! ### The law of the code -/

section Law

variable {N n t : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {M K : Fin N → ℕ} [∀ k, NeZero (K k)] [NeZero n]
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

/-- The received symbols, block by block. -/
def nncBlocks {β : Type*} (z : Fin (t * n) → β) (j : Fin t) : Fin n → β :=
  fun i => z (finProdFinEquiv (j, i))

/-- The received symbols, block by block, as an equivalence. -/
def nncBlockEquiv (β : Type*) : (Fin (t * n) → β) ≃ (Fin t → Fin n → β) where
  toFun := nncBlocks
  invFun Z k := Z (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv z := by
    funext k
    have h : finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2) = k :=
      finProdFinEquiv.apply_symm_apply k
    simp only [nncBlocks, h]
  right_inv Z := by
    funext j i
    simp [nncBlocks]

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] [∀ k, NeZero (K k)]
  [NeZero n] in
lemma finProd_div_mod' (hn : 0 < n) (j : Fin t) (i : Fin n) :
    ((finProdFinEquiv (j, i) : Fin (t * n)) : ℕ) / n = j ∧
      ((finProdFinEquiv (j, i) : Fin (t * n)) : ℕ) % n = i := by
  have hval : ((finProdFinEquiv (j, i) : Fin (t * n)) : ℕ) = i + n * j := rfl
  rw [hval]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt i.2, zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]

/-- The state of a node, for the blocks of a code of `t * n` symbols. -/
def nncSt (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Cs : ℕ → NNCBlock M K n X V) (dY : ∀ k, Y k) (m : ∀ k, Fin (M k))
    (z : Fin (t * n) → ∀ k, Y k) (j : ℕ) (k : Fin N) : Fin (K k) :=
  nncStK k (pk k) (fun i => Cs i k) (m k) (getBlock (dY k) (fun s => z s k)) j

/-- **The law of the code of all the blocks** is a product over the blocks. -/
theorem nncCode_law (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Cs : ℕ → NNCBlock M K n X V) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k)
    (m : ∀ k, Fin (M k)) (z : Fin (t * n) → ∀ k, Y k) :
    (nncCode L ε pk Cs t dY hM (t * n)).law W (m, z) =
      uniformPMF (∀ k, Fin (M k)) m * ∏ j : Fin t, seqChan W n
        (xAt (nncX (Cs j) (nncBr m (nncSt pk Cs dY m z j)))) (nncBlocks z j) := by
  rw [DMNCode.law, fbLaw_eq_prod]
  congr 1
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  refine prod_congr rfl fun j _ => ?_
  simp only [seqChan]
  refine prod_congr rfl fun i _ => ?_
  obtain ⟨hdiv, hmod⟩ := finProd_div_mod' (t := t) (NeZero.pos n) j i
  have hin : (⟨((finProdFinEquiv (j, i) : Fin (t * n)) : ℕ) % n,
      Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = i := Fin.ext hmod
  congr 1
  funext k
  simp only [DMNCode.fbEnc, nncCode, xAt, nncX, nncBr, nncSt]
  rw [hdiv, hin]
  have hst : nncStK k (pk k) (fun j => Cs j k) (m k) (getBlock (dY k)
      fun s : Fin (finProdFinEquiv (j, i) : Fin (t * n)) =>
        z ⟨s, s.2.trans (finProdFinEquiv (j, i)).2⟩ k) j =
      nncStK k (pk k) (fun i => Cs i k) (m k) (getBlock (dY k) fun s => z s k) j := by
    refine nncStK_congr k (pk k) _ (m k) j fun j' hj' => ?_
    funext i'
    have hlt : i'.val + n * j' < ((finProdFinEquiv (j, i) : Fin (t * n)) : ℕ) := by
      have hval : ((finProdFinEquiv (j, i) : Fin (t * n)) : ℕ) = i + n * j := rfl
      rw [hval]
      have h₁ : n * (j' + 1) ≤ n * j := Nat.mul_le_mul_left _ hj'
      have h₂ := i'.2
      rw [Nat.mul_add, Nat.mul_one] at h₁
      omega
    have hlt' : i'.val + n * j' < t * n := lt_trans hlt (finProdFinEquiv (j, i)).2
    simp only [getBlock, dite_eq_left hlt, dite_eq_left hlt']
  rw [hst]

end Law

/-! ### The decoder -/

section Dec

variable {N n t : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {M K : Fin N → ℕ} [∀ k, NeZero (K k)] [NeZero n]

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] [∀ k, NeZero (K k)]
  [NeZero n] in
lemma arrOf_fst {A B' : Type*} (d : A × B') (ξ : Fin t → A × B') (j : ℕ) :
    (arrOf d ξ j).1 = arrOf d.1 (fun i => (ξ i).1) j := by
  by_cases h : j < t <;> simp [arrOf, h]

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] [∀ k, NeZero (K k)]
  [NeZero n] in
lemma pathPrev_of_st {St : Type*} {l : St} {ℓ : Fin t → St} {st : ℕ → St} (h0 : st 0 = l)
    (hs : ∀ j : Fin t, ℓ j = st (j + 1)) (j : Fin t) : pathPrev l ℓ j = st j := by
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => simpa [pathPrev] using h0.symm
  | succ i =>
    have := hs ⟨i, by omega⟩
    simp only [pathPrev]
    rw [show (⟨i + 1, hj⟩ : Fin t).castSucc = (⟨i, by omega⟩ : Fin t).succ from by ext; simp,
      Fin.cons_succ, this]

/-- **The decoder finds the messages** if the true path passes the tests, and no path with other
messages does. -/
theorem nncCode_dec_eq (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (dξ : NNCΞ M K n X Y V) (ξ : Fin t → NNCΞ M K n X Y V) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k)
    {N' : ℕ} (d : Fin N) (m : ∀ k, Fin (M k)) {y : Fin N' → Y d}
    (hy : ∀ j : Fin t, getBlock (dY d) y j = yOf d (ξ j).2)
    (h₁ : ∀ j : Fin t, ¬ nncBad L ε (nncX (ξ j).1 (nncBr m (stOf (nncNx pk m) 0 (arrOf dξ ξ) j)))
      (ξ j).2 (nncVOf (ξ j).1 (nncBr m (stOf (nncNx pk m) 0 (arrOf dξ ξ) j)) pk (ξ j).2))
    (h₂ : ∀ m' : ∀ k, Fin (M k), m' ≠ m → m' d = m d → ∀ ℓ : Fin t → ∀ k, Fin (K k), ¬ ∀ j : Fin t,
      nncTst L d ε pk m m' (stOf (nncNx pk m) 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j)) :
    (nncCode L ε pk (fun j => (arrOf dξ ξ j).1) t dY hM N').dec d (m d) y = m := by
  set st := stOf (nncNx pk m) 0 (arrOf dξ ξ) with hst
  set Cs : ℕ → NNCBlock M K n X V := fun j => (arrOf dξ ξ j).1 with hCs
  -- the state of the decoder
  have harr : ∀ j : Fin t, arrOf dξ ξ j = ξ j := arrOf_coe dξ ξ
  have hstk : ∀ (j : ℕ), j ≤ t → nncStK d (pk d) (fun i => Cs i d) (m d) (getBlock (dY d) y) j =
      st j d := by
    intro j hj
    rw [hst, stOf_nncNx pk m (arrOf dξ ξ) j d]
    refine nncStK_congr d (pk d) _ (m d) j fun j' hj' => ?_
    have hlt : j' < t := by omega
    rw [hy ⟨j', hlt⟩, ← harr ⟨j', hlt⟩]
  refine nncDecOf_eq hM ?_ ?_
  · -- the true path
    refine ⟨fun j => st (j + 1), rfl, fun j => ⟨?_, ?_⟩⟩
    · exact (hstk (j + 1) j.2).symm
    · have hp : pathPrev (0 : ∀ k, Fin (K k)) (fun j : Fin t => st (j + 1)) j = st j :=
        pathPrev_of_st (st := st) rfl (fun _ => rfl) j
      rw [hp]
      change nncTest L d ε (nncPathSeq (Cs j) m (st j) (st (j + 1))) (getBlock (dY d) y j)
      have hT := (nncTst_true (d := d) (m := m) pk (st j) (ξ j) (h₁ j)).2
      have hst' : st (j + 1) = nncNx pk m (st j) (ξ j) := by
        rw [hst]
        simp only [stOf]
        rw [harr j]
      rw [hst', hy j]
      have hC : Cs j = (ξ j).1 := by
        simp only [hCs, harr j]
      rw [hC]
      exact hT
  · -- no other messages
    rintro m' ⟨ℓ, hd, hℓ⟩
    by_contra hne
    refine h₂ m' hne hd ℓ fun j => ⟨?_, ?_⟩
    · have := (hℓ j).1
      rw [hstk (j + 1) j.2] at this
      rw [this, hst]
      simp only [stOf]
      rw [harr j]
    · have := (hℓ j).2
      rw [hy j] at this
      have hC : Cs j = (ξ j).1 := by
        simp only [hCs, harr j]
      rwa [hC] at this

end Dec

/-! ### The average error -/

section Avg

variable {N n t : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {M K : Fin N → ℕ} [∀ k, NeZero (K k)] [NeZero n]
  {px : ∀ k, X k → ℝ} {q : ∀ k, X k → V k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] [∀ k, NeZero (K k)]
  [NeZero n] in
lemma getBlock_nncBlocks {β : Type*} (d : β) (z : Fin (t * n) → β) (j : Fin t) :
    getBlock d z j = nncBlocks z j := by
  funext i
  have hlt : i.val + n * j < t * n := (finProdFinEquiv (j, i) : Fin (t * n)).2
  simp only [getBlock, dite_eq_left hlt]
  rfl

omit [∀ k, NeZero (K k)] [NeZero n] in
lemma nncP_isPMF (hpx : ∀ k, IsPMF (px k)) (hqc : ∀ k, IsChannel (q k)) (hW : IsChannel W)
    (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K k)) :
    IsPMF (nncP (n := n) (X := X) (Y := Y) (V := V) px q W m a) := by
  have hB := nncBlockLaw_isPMF (X := X) (V := V) (M := M) (K := K) (n := n) hpx hqc
  refine ⟨fun ξ => mul_nonneg (hB.nonneg _) ((seqChan_isChannel hW n _).nonneg _), ?_⟩
  simp only [nncP, Fintype.sum_prod_type]
  simp_rw [← mul_sum, (seqChan_isChannel hW n _).sum_eq_one, mul_one]
  exact hB.sum_eq_one

/-- The received symbols and the codes are a sequence of the randomness of the blocks. -/
def nncSeqOf (Cst : Fin t → NNCBlock M K n X V) (z : Fin (t * n) → ∀ k, Y k) :
    Fin t → NNCΞ M K n X Y V :=
  fun j => (Cst j, nncBlocks z j)

/-- The event of an error of the code of `t` blocks, for the randomness of the blocks. -/
theorem nncCode_ind_wrong_le (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (dξ : NNCΞ M K n X Y V) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k) (D : Fin N → Finset (Fin N))
    (Cst : Fin t → NNCBlock M K n X V) (m : ∀ k, Fin (M k)) (z : Fin (t * n) → ∀ k, Y k) :
    ind ((nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).Wrong D (m, z)) ≤
      ind (∃ j : Fin t, (fun (a : ∀ k, Fin (K k)) (ξ : NNCΞ M K n X Y V) => nncBad L ε
          (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2))
        (stOf (nncNx pk m) 0 (arrOf dξ (nncSeqOf Cst z)) j) (nncSeqOf Cst z j)) +
      ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k), ind (m' ≠ m ∧ m' d = m d) *
        ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t, nncTst L d ε pk m m'
          (stOf (nncNx pk m) 0 (arrOf dξ (nncSeqOf Cst z)) j) (pathPrev 0 ℓ j) (ℓ j)
          (nncSeqOf Cst z j)) := by
  classical
  set ξ := nncSeqOf Cst z with hξ
  set B₁ := ∃ j : Fin t, (fun (a : ∀ k, Fin (K k)) (ξ : NNCΞ M K n X Y V) => nncBad L ε
    (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2))
      (stOf (nncNx pk m) 0 (arrOf dξ ξ) j) (ξ j) with hB₁
  set T := ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k), ind (m' ≠ m ∧ m' d = m d) *
    ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t, nncTst L d ε pk m m'
      (stOf (nncNx pk m) 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j)) with hT
  have hT0 : 0 ≤ T := sum_nonneg fun d _ => sum_nonneg fun m' _ => mul_nonneg (ind_nonneg _)
    (sum_nonneg fun ℓ _ => ind_nonneg _)
  by_cases hB : B₁
  · rw [ind_of_pos hB]
    have := ind_le_one ((nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).Wrong D (m, z))
    linarith
  by_cases hX : ∃ d ∈ univ.biUnion D, ∃ m' : ∀ k, Fin (M k), m' ≠ m ∧ m' d = m d ∧
      ∃ ℓ : Fin t → ∀ k, Fin (K k), ∀ j : Fin t, nncTst L d ε pk m m'
        (stOf (nncNx pk m) 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j)
  · obtain ⟨d, hd, m', hne, hdm, ℓ, hℓ⟩ := hX
    have h₁ : (1 : ℝ) ≤ T := by
      have h₂ : (1 : ℝ) ≤ ind (m' ≠ m ∧ m' d = m d) *
          ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t, nncTst L d ε pk m m'
            (stOf (nncNx pk m) 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j)) := by
        rw [ind_of_pos ⟨hne, hdm⟩, one_mul]
        refine le_trans (le_of_eq (ind_of_pos hℓ).symm) (single_le_sum
          (f := fun ℓ : Fin t → ∀ k, Fin (K k) => ind (∀ j : Fin t, nncTst L d ε pk m m'
            (stOf (nncNx pk m) 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j)))
          (fun _ _ => ind_nonneg _) (mem_univ ℓ))
      refine h₂.trans (le_trans ?_ (single_le_sum (f := fun d => ∑ m' : ∀ k, Fin (M k),
        ind (m' ≠ m ∧ m' d = m d) * ∑ ℓ : Fin t → ∀ k, Fin (K k),
          ind (∀ j : Fin t, nncTst L d ε pk m m' (stOf (nncNx pk m) 0 (arrOf dξ ξ) j)
            (pathPrev 0 ℓ j) (ℓ j) (ξ j))) (fun d _ => sum_nonneg fun m' _ =>
          mul_nonneg (ind_nonneg _) (sum_nonneg fun ℓ _ => ind_nonneg _)) hd))
      exact single_le_sum (f := fun m' : ∀ k, Fin (M k) => ind (m' ≠ m ∧ m' d = m d) *
        ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t, nncTst L d ε pk m m'
          (stOf (nncNx pk m) 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j)))
        (fun m' _ => mul_nonneg (ind_nonneg _) (sum_nonneg fun ℓ _ => ind_nonneg _)) (mem_univ m')
    have := ind_le_one ((nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).Wrong D (m, z))
    linarith [ind_nonneg B₁]
  -- no error
  rw [ind_of_neg]
  · exact add_nonneg (ind_nonneg _) hT0
  rintro ⟨j, k, hk, hne⟩
  have hkd : k ∈ univ.biUnion D := mem_biUnion.mpr ⟨j, mem_univ j, hk⟩
  apply hne
  have hC : arrOf dξ.1 Cst = fun j => (arrOf dξ ξ j).1 := by
    funext i
    rw [arrOf_fst]
    rfl
  have hdec := nncCode_dec_eq (N' := t * n) L ε pk dξ ξ dY hM k m (y := fun i => z i k)
    (fun j => by
      rw [getBlock_nncBlocks]
      rfl)
    (fun j hj => hB ⟨j, hj⟩)
    (fun m' hm' hd ℓ hℓ => hX ⟨k, hkd, m', hm', hd, ℓ, hℓ⟩)
  rw [hC]
  exact congrFun hdec j

/-- The law of the code of the blocks, as a run of the trellis. -/
theorem nncCode_law_run (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (dξ : NNCΞ M K n X Y V) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k)
    (Cst : Fin t → NNCBlock M K n X V) (m : ∀ k, Fin (M k)) (z : Fin (t * n) → ∀ k, Y k) :
    piLaw (fun _ => nncBlockLaw px q M K n) Cst *
        (nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).law W (m, z) =
      uniformPMF (∀ k, Fin (M k)) m *
        runProb (nncP px q W m) (nncNx pk m) dξ 0 (nncSeqOf Cst z) := by
  rw [nncCode_law]
  simp only [runProb, nncP, prod_mul_distrib, piLaw, nncSeqOf]
  have hst : ∀ j : Fin t, nncSt pk (arrOf dξ.1 Cst) dY m z j =
      stOf (nncNx pk m) 0 (arrOf dξ (nncSeqOf Cst z)) j := by
    intro j
    funext k
    rw [stOf_nncNx pk m (arrOf dξ (nncSeqOf Cst z)) j k, nncSt]
    have hC : (fun i => arrOf dξ.1 Cst i k) = fun i =>
        (arrOf dξ (nncSeqOf Cst z) i).1 k := by
      funext i
      rw [arrOf_fst]
      rfl
    rw [hC]
    refine nncStK_congr k (pk k) _ (m k) j fun j' hj' => ?_
    have hlt : j' < t := hj'.trans j.2
    have e₁ : arrOf dξ (nncSeqOf Cst z) j' = (Cst ⟨j', hlt⟩, nncBlocks z ⟨j', hlt⟩) :=
      arrOf_coe dξ _ ⟨j', hlt⟩
    rw [e₁]
    exact getBlock_nncBlocks (dY k) (fun s => z s k) ⟨j', hlt⟩
  have hC : ∀ j : Fin t, arrOf dξ.1 Cst j = Cst j := arrOf_coe dξ.1 Cst
  simp_rw [hst, hC]
  ring

set_option synthInstance.maxSize 1024 in
/-- **The average of the probability of error over the codes of the blocks.** -/
theorem nncCode_avg_le (L : NNCΩ X Y V → ℝ) (hpx : ∀ k, IsPMF (px k)) (hqc : ∀ k, IsChannel (q k))
    (hW : IsChannel W) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (dξ : NNCΞ M K n X Y V) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k) (D : Fin N → Finset (Fin N))
    {η β : ℝ}
    (hη : ∀ (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K k)), ∑ ξ : NNCΞ M K n X Y V, nncP px q W m a ξ *
      ind (nncBad L ε (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2)) ≤ η)
    (hβ : ∀ (m : ∀ k, Fin (M k)), ∀ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k),
      ind (m' ≠ m ∧ m' d = m d) * nncCount L px q W d ε pk m m' dξ t 0 0 ≤ β) :
    ∑ Cst : Fin t → NNCBlock M K n X V, piLaw (fun _ => nncBlockLaw px q M K n) Cst *
        (nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).errProb W D ≤
      t * η + (univ.biUnion D).card * β := by
  classical
  have : Nonempty (∀ k, Fin (M k)) := ⟨fun k => ⟨0, hM k⟩⟩
  have hU : IsPMF (uniformPMF (∀ k, Fin (M k))) := uniformPMF_isPMF
  have hP := fun m a => nncP_isPMF (n := n) (X := X) (Y := Y) (V := V) (M := M) (K := K) hpx hqc hW
    m a
  -- for one tuple of messages
  have hrow : ∀ m : ∀ k, Fin (M k), ∑ Cst : Fin t → NNCBlock M K n X V, ∑ z : Fin (t * n) → ∀ k, Y
    k,
      runProb (nncP px q W m) (nncNx pk m) dξ 0 (nncSeqOf Cst z) *
        ind ((nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).Wrong D (m, z)) ≤
      t * η + (univ.biUnion D).card * β := by
    intro m
    set P := nncP (n := n) (X := X) (Y := Y) (V := V) (M := M) (K := K) px q W m with hPd
    set nx := nncNx (M := M) (K := K) (n := n) (X := X) (Y := Y) (V := V) pk m with hnx
    let e : (Fin t → NNCBlock M K n X V) × (Fin (t * n) → ∀ k, Y k) ≃ (Fin t → NNCΞ M K n X Y V) :=
      (Equiv.prodCongr (Equiv.refl _) (nncBlockEquiv _)).trans
        (Equiv.arrowProdEquivProdArrow _ _ _).symm
    have he : ∀ (Cst : Fin t → NNCBlock M K n X V) (z : Fin (t * n) → ∀ k, Y k),
        e (Cst, z) = nncSeqOf Cst z := fun _ _ => rfl
    have hsum : ∀ F : (Fin t → NNCΞ M K n X Y V) → ℝ,
        ∑ Cst : Fin t → NNCBlock M K n X V, ∑ z : Fin (t * n) → ∀ k, Y k, F (nncSeqOf Cst z) =
          ∑ ξ, F ξ := by
      intro F
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv e (fun p => F (nncSeqOf p.1 p.2)) F fun p => by
        rw [← he]
    let Bad : (∀ k, Fin (K k)) → NNCΞ M K n X Y V → Prop := fun a ξ => nncBad L ε
      (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2)
    have h₁ := sum_run_exists_le (P := P) (hP m) nx dξ Bad (hη m) t 0
    have h₂ : ∑ ξ : Fin t → NNCΞ M K n X Y V, runProb P nx dξ 0 ξ *
        ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k), ind (m' ≠ m ∧ m' d = m d) *
          ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t, nncTst L d ε pk m m'
            (stOf nx 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j)) ≤
        (univ.biUnion D).card * β := by
      calc _ = ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k), ind (m' ≠ m ∧ m' d = m d) *
            nncCount L px q W d ε pk m m' dξ t 0 0 := by
            simp only [nncCount, pathCount]
            simp_rw [mul_sum]
            rw [sum_comm]
            refine sum_congr rfl fun d _ => ?_
            rw [sum_comm]
            refine sum_congr rfl fun m' _ => ?_
            refine sum_congr rfl fun ξ _ => sum_congr rfl fun ℓ _ => ?_
            ring
        _ ≤ ∑ d ∈ univ.biUnion D, β := sum_le_sum fun d hd => hβ m d hd
        _ = _ := by simp
    have h₃ : ∀ (Cst : Fin t → NNCBlock M K n X V) (z : Fin (t * n) → ∀ k, Y k),
        runProb P nx dξ 0 (nncSeqOf Cst z) *
          ind ((nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).Wrong D (m, z)) ≤
        runProb P nx dξ 0 (nncSeqOf Cst z) * ind (∃ j : Fin t, Bad
          (stOf nx 0 (arrOf dξ (nncSeqOf Cst z)) j) (nncSeqOf Cst z j)) +
        runProb P nx dξ 0 (nncSeqOf Cst z) * ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k),
          ind (m' ≠ m ∧ m' d = m d) * ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t,
            nncTst L d ε pk m m' (stOf nx 0 (arrOf dξ (nncSeqOf Cst z)) j) (pathPrev 0 ℓ j) (ℓ j)
              (nncSeqOf Cst z j)) := by
      intro Cst z
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (nncCode_ind_wrong_le L ε pk dξ dY hM D Cst m z)
        (runProb_nonneg (hP m) nx dξ 0 _)
    calc _ ≤ ∑ Cst : Fin t → NNCBlock M K n X V, ∑ z : Fin (t * n) → ∀ k, Y k,
          (runProb P nx dξ 0 (nncSeqOf Cst z) * ind (∃ j : Fin t, Bad
          (stOf nx 0 (arrOf dξ (nncSeqOf Cst z)) j) (nncSeqOf Cst z j)) +
        runProb P nx dξ 0 (nncSeqOf Cst z) * ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k),
          ind (m' ≠ m ∧ m' d = m d) * ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t,
            nncTst L d ε pk m m' (stOf nx 0 (arrOf dξ (nncSeqOf Cst z)) j) (pathPrev 0 ℓ j) (ℓ j)
              (nncSeqOf Cst z j))) :=
          sum_le_sum fun Cst _ => sum_le_sum fun z _ => h₃ Cst z
      _ = ∑ ξ : Fin t → NNCΞ M K n X Y V, (runProb P nx dξ 0 ξ *
          ind (∃ j : Fin t, Bad (stOf nx 0 (arrOf dξ ξ) j) (ξ j)) +
        runProb P nx dξ 0 ξ * ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k),
          ind (m' ≠ m ∧ m' d = m d) * ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t,
            nncTst L d ε pk m m' (stOf nx 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j))) :=
          hsum fun ξ => runProb P nx dξ 0 ξ *
            ind (∃ j : Fin t, Bad (stOf nx 0 (arrOf dξ ξ) j) (ξ j)) +
            runProb P nx dξ 0 ξ * ∑ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k),
              ind (m' ≠ m ∧ m' d = m d) * ∑ ℓ : Fin t → ∀ k, Fin (K k), ind (∀ j : Fin t,
                nncTst L d ε pk m m' (stOf nx 0 (arrOf dξ ξ) j) (pathPrev 0 ℓ j) (ℓ j) (ξ j))
      _ ≤ _ := by
          rw [sum_add_distrib]
          exact add_le_add h₁ h₂
  -- the average over the messages
  have hexp : ∑ Cst : Fin t → NNCBlock M K n X V, piLaw (fun _ => nncBlockLaw px q M K n) Cst *
      (nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).errProb W D =
      ∑ m : ∀ k, Fin (M k), uniformPMF (∀ k, Fin (M k)) m * ∑ Cst : Fin t → NNCBlock M K n X V,
        ∑ z : Fin (t * n) → ∀ k, Y k, runProb (nncP px q W m) (nncNx pk m) dξ 0 (nncSeqOf Cst z) *
          ind ((nncCode L ε pk (arrOf dξ.1 Cst) t dY hM (t * n)).Wrong D (m, z)) := by
    simp only [DMNCode.errProb, Fintype.sum_prod_type, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun Cst _ => sum_congr rfl fun z _ => ?_
    rw [← mul_assoc, nncCode_law_run L ε pk dξ dY hM Cst m z]
    ring
  rw [hexp]
  calc _ ≤ ∑ m : ∀ k, Fin (M k), uniformPMF (∀ k, Fin (M k)) m *
        (t * η + (univ.biUnion D).card * β) :=
        sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hrow m) (hU.nonneg m)
    _ = _ := by rw [← sum_mul, hU.sum_eq_one, one_mul]

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] [NeZero n] in
/-- The test of a decoder only depends on the first `t` blocks. -/
lemma nncPass_congr [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)]
    (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Cs : ℕ → NNCBlock M K n X V) (k : Fin N) (mk : Fin (M k)) {Z Z' : ℕ → Fin n → Y k}
    (h : ∀ j, j < t → Z j = Z' j) (m' : ∀ k, Fin (M k)) (ℓ : Fin t → ∀ k, Fin (K k)) :
    nncPass L ε pk Cs t k mk Z m' ℓ ↔ nncPass L ε pk Cs t k mk Z' m' ℓ := by
  have hst : ∀ j : Fin t, nncStK k (pk k) (fun i => Cs i k) mk Z (j + 1) =
      nncStK k (pk k) (fun i => Cs i k) mk Z' (j + 1) := fun j =>
    nncStK_congr k (pk k) _ mk _ fun j' hj' => h j' (by have := j.2; omega)
  simp only [nncPass]
  refine and_congr_right fun _ => forall_congr' fun j => ?_
  rw [hst j, h j j.2]

/-- **A longer code.** The rest of the symbols are not used, so the error is the same. -/
theorem nncCode_errProb_pad (hW : IsChannel W) (L : NNCΩ X Y V → ℝ) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Cs : ℕ → NNCBlock M K n X V) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k)
    (D : Fin N → Finset (Fin N)) {N' : ℕ} (hN : t * n ≤ N') :
    (nncCode L ε pk Cs t dY hM N').errProb W D =
      (nncCode L ε pk Cs t dY hM (t * n)).errProb W D := by
  classical
  set c' := nncCode L ε pk Cs t dY hM N' with hc'
  set c := nncCode L ε pk Cs t dY hM (t * n) with hc
  let T : (∀ k, Fin (M k)) × (Fin N' → ∀ k, Y k) → (∀ k, Fin (M k)) × (Fin (t * n) → ∀ k, Y k) :=
    fun z => (z.1, fun s => z.2 ⟨s, lt_of_lt_of_le s.2 hN⟩)
  have hlaw : dist (c'.law W) T = c.law W := dist_fbLaw_prefix hW (t * n) N' hN
  have hdec : ∀ z, c'.Wrong D z ↔ c.Wrong D (T z) := by
    intro z
    have hval : ∀ k j, c'.dec k (z.1 k) (fun i => z.2 i k) j =
        c.dec k (z.1 k) (fun i => (T z).2 i k) j := by
      intro k j
      have hP : (fun m' => ∃ ℓ, nncPass L ε pk Cs t k (z.1 k)
          (getBlock (dY k) fun i => z.2 i k) m' ℓ) = fun m' => ∃ ℓ, nncPass L ε pk Cs t k (z.1 k)
          (getBlock (dY k) fun i => (T z).2 i k) m' ℓ := by
        funext m'
        refine propext (exists_congr fun ℓ => nncPass_congr L ε pk Cs k (z.1 k) (fun j hj => ?_) m'
          ℓ)
        funext i
        have hlt : i.val + n * j < t * n := by
          have h₁ : n * (j + 1) ≤ n * t := Nat.mul_le_mul_left _ hj
          have h₂ := i.2
          rw [Nat.mul_add, Nat.mul_one] at h₁
          rw [Nat.mul_comm t n]
          omega
        have hlt' := lt_of_lt_of_le hlt hN
        simp only [getBlock, dite_eq_left hlt, dite_eq_left hlt']
        rfl
      simp only [hc', hc, nncCode]
      rw [hP]
    simp only [DMNCode.Wrong]
    refine exists_congr fun j => exists_congr fun k => and_congr_right fun _ => ?_
    rw [hval k j]
  simp only [DMNCode.errProb]
  rw [← hlaw, sum_dist_mul]
  refine sum_congr rfl fun z _ => ?_
  congr 1
  simp only [ind, hdec z]

set_option synthInstance.maxSize 1024 in
/-- **There is a code of `t` blocks whose error is at most the average.** -/
theorem nnc_exists_code (L : NNCΩ X Y V → ℝ) (hpx : ∀ k, IsPMF (px k)) (hqc : ∀ k, IsChannel (q k))
    (hW : IsChannel W) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (dξ : NNCΞ M K n X Y V) (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k) (D : Fin N → Finset (Fin N))
    {η β : ℝ}
    (hη : ∀ (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K k)), ∑ ξ : NNCΞ M K n X Y V, nncP px q W m a ξ *
      ind (nncBad L ε (nncX ξ.1 (nncBr m a)) ξ.2 (nncVOf ξ.1 (nncBr m a) pk ξ.2)) ≤ η)
    (hβ : ∀ (m : ∀ k, Fin (M k)), ∀ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k),
      ind (m' ≠ m ∧ m' d = m d) * nncCount L px q W d ε pk m m' dξ t 0 0 ≤ β)
    {N' : ℕ} (hN : t * n ≤ N') :
    ∃ c : DMNCode M N' X Y, c.errProb W D ≤ t * η + (univ.biUnion D).card * β := by
  have havg := nncCode_avg_le (t := t) L hpx hqc hW ε pk dξ dY hM D hη hβ
  have hlaw : IsPMF (piLaw fun _ : Fin t => nncBlockLaw (X := X) (V := V) px q M K n) :=
    piLaw_isPMF fun _ => nncBlockLaw_isPMF hpx hqc
  obtain ⟨Cst, hC⟩ := exists_le_of_sum_mul_le hlaw havg
  refine ⟨nncCode L ε pk (arrOf dξ.1 Cst) t dY hM N', ?_⟩
  rw [nncCode_errProb_pad hW L ε pk _ dY hM D hN]
  exact hC

end Avg

end InfoTheory
