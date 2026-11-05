/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NNCCover

/-!
# Noisy network coding: the random code of one block

In each block, node `k` has for each message `m_k` and each previous index `l` a row: a sequence
`x_kⁿ(m_k, l)` and `K_k` sequences `v_kⁿ(l' | m_k, l)`. All the rows are independent.

## Main definitions

* `NNCBlock`: the code of one block.
* `nncRow`: the law of a row.
* `nncBlockLaw`: the law of the code of one block.

## Main statements

* `sum_nncBlock_test_le`: the probability of the test for a wrong row. The node may use any index
  that depends on its true row and on its received sequence.
* `sum_nncBlock_bad_eq`: the probability that the tuple of the true rows is not typical.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The law of a row -/

section Row

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A row of the code of a node: a sequence and a codebook. -/
abbrev NNCRow (n K : ℕ) (A B : Type*) := (Fin n → A) × (Fin K → Fin n → B)

/-- The law of a row: an i.i.d. sequence, and independent sequences given that sequence. -/
def nncRow (p : A → ℝ) (q : A → B → ℝ) (n K : ℕ) (r : NNCRow n K A B) : ℝ :=
  iidPMF p n r.1 * iidPMF (seqChan q n r.1) K r.2

variable {p : A → ℝ} {q : A → B → ℝ} {n K : ℕ}

lemma nncRow_isPMF (hp : IsPMF p) (hq : IsChannel q) : IsPMF (nncRow p q n K) := by
  refine ⟨fun r => mul_nonneg ((iidPMF_isPMF hp n).nonneg _)
    ((iidPMF_isPMF (seqChan_isChannel hq n _) K).nonneg _), ?_⟩
  simp only [nncRow, Fintype.sum_prod_type]
  simp_rw [← mul_sum, (iidPMF_isPMF (seqChan_isChannel hq n _) K).sum_eq_one, mul_one]
  exact (iidPMF_isPMF hp n).sum_eq_one

/-- The law of the sequence of a row. -/
lemma sum_nncRow_fst (hq : IsChannel q) (G : (Fin n → A) → ℝ) :
    ∑ r, nncRow p q n K r * G r.1 = ∑ x, iidPMF p n x * G x := by
  simp only [nncRow, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  calc _ = iidPMF p n x * G x * ∑ C : Fin K → Fin n → B, iidPMF (seqChan q n x) K C := by
        rw [mul_sum]
        exact sum_congr rfl fun C _ => by ring
    _ = _ := by rw [(iidPMF_isPMF (seqChan_isChannel hq n _) K).sum_eq_one, mul_one]

/-- The law of one sequence of the codebook of a row. -/
lemma sum_nncRow_entry (hq : IsChannel q) (l : Fin K) (G : (Fin n → A) → (Fin n → B) → ℝ) :
    ∑ r, nncRow p q n K r * G r.1 (r.2 l) =
      ∑ x, iidPMF p n x * ∑ v, seqChan q n x v * G x v := by
  classical
  simp only [nncRow, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [mul_assoc]
  rw [← mul_sum]
  congr 1
  exact sum_piLaw_mul_eval (ν := fun _ : Fin K => seqChan q n x)
    (fun _ => seqChan_isChannel hq n x) l (G x)

/-- A sequence and an entry of a fresh row. -/
lemma sum_nncRow_ind_entry (hq : IsChannel q) (l : Fin K)
    (c : (Fin n → A) × (Fin n → B)) :
    ∑ r, nncRow p q n K r * ind ((r.1, r.2 l) = c) = iidPMF p n c.1 * seqChan q n c.1 c.2 := by
  classical
  rw [sum_nncRow_entry hq l fun x v => ind ((x, v) = c), Finset.sum_eq_single c.1]
  · rw [Finset.sum_eq_single c.2]
    · rw [ind_of_pos rfl, mul_one]
    · exact fun v _ hv => by
        rw [ind_of_neg fun h => hv (Prod.ext_iff.mp h).2, mul_zero]
    · simp
  · intro x _ hx
    refine mul_eq_zero_of_right _ (sum_eq_zero fun v _ => ?_)
    rw [ind_of_neg fun h => hx (Prod.ext_iff.mp h).1, mul_zero]
  · simp

end Row

/-! ### The code of one block -/

section Block

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {M K : Fin N → ℕ}

/-- The rows of a node are indexed by its message and its previous index. -/
abbrev NNCBr (M K : Fin N → ℕ) (k : Fin N) := Fin (M k) × Fin (K k)

/-- **Page 19-29 of [elgamal2010].** The code of one block. -/
abbrev NNCBlock (M K : Fin N → ℕ) (n : ℕ) (X V : Fin N → Type*) :=
  ∀ k, NNCBr M K k → NNCRow n (K k) (X k) (V k)

/-- The law of the rows of a node. -/
def nncNodeLaw (px : ∀ k, X k → ℝ) (q : ∀ k, X k → V k → ℝ) (M K : Fin N → ℕ) (n : ℕ) (k : Fin N)
    (c : NNCBr M K k → NNCRow n (K k) (X k) (V k)) : ℝ :=
  piLaw (fun _ => nncRow (px k) (q k) n (K k)) c

/-- The law of the code of one block. -/
def nncBlockLaw (px : ∀ k, X k → ℝ) (q : ∀ k, X k → V k → ℝ) (M K : Fin N → ℕ) (n : ℕ)
    (C : NNCBlock M K n X V) : ℝ :=
  prodLaw (nncNodeLaw px q M K n) C

/-- The input sequences of a block, for a choice of the rows. -/
def nncX (C : NNCBlock M K n X V) (b : ∀ k, NNCBr M K k) : ∀ k, Fin n → X k :=
  fun k => (C k (b k)).1

variable {px : ∀ k, X k → ℝ} {q : ∀ k, X k → V k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

lemma nncNodeLaw_isPMF (hpx : ∀ k, IsPMF (px k)) (hq : ∀ k, IsChannel (q k)) (k : Fin N) :
    IsPMF (nncNodeLaw px q M K n k) :=
  piLaw_isPMF fun _ => nncRow_isPMF (hpx k) (hq k)

lemma nncBlockLaw_isPMF (hpx : ∀ k, IsPMF (px k)) (hq : ∀ k, IsChannel (q k)) :
    IsPMF (nncBlockLaw (X := X) (V := V) px q M K n) :=
  prodLaw_isPMF (nncNodeLaw_isPMF hpx hq)

/-- The law of the rows of a node, restricted to an input sequence. -/
def nncNodeAt (px : ∀ k, X k → ℝ) (q : ∀ k, X k → V k → ℝ) (M K : Fin N → ℕ) (n : ℕ)
    (b : ∀ k, NNCBr M K k) (x : ∀ k, Fin n → X k) (k : Fin N)
    (c : NNCBr M K k → NNCRow n (K k) (X k) (V k)) : ℝ :=
  nncNodeLaw px q M K n k c * ind ((c (b k)).1 = x k)

/-- **Fixing the input sequences.** Given the input sequences, the rows are still independent. -/
lemma sum_nncBlock_split (b : ∀ k, NNCBr M K k)
    (G : NNCBlock M K n X V → (Fin n → ∀ k, Y k) → ℝ) :
    ∑ C, nncBlockLaw px q M K n C * ∑ y, seqChan W n (xAt (nncX C b)) y * G C y =
      ∑ x, ∑ y, seqChan W n (xAt x) y * ∑ C, prodLaw (nncNodeAt px q M K n b x) C * G C y := by
  classical
  have hprod : ∀ (x : ∀ k, Fin n → X k) (C : NNCBlock M K n X V),
      prodLaw (nncNodeAt px q M K n b x) C = nncBlockLaw px q M K n C * ind (nncX C b = x) := by
    intro x C
    simp only [prodLaw, nncNodeAt, nncBlockLaw, prod_mul_distrib]
    congr 1
    by_cases h : nncX C b = x
    · rw [ind_of_pos h]
      exact prod_eq_one fun k _ => ind_of_pos (congrFun h k)
    · rw [ind_of_neg h]
      obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact prod_eq_zero (mem_univ k) (ind_of_neg hk)
  simp_rw [hprod]
  calc _ = ∑ C, ∑ x, nncBlockLaw px q M K n C * ind (nncX C b = x) *
        ∑ y, seqChan W n (xAt x) y * G C y := by
        refine sum_congr rfl fun C _ => ?_
        rw [Finset.sum_eq_single (nncX C b)]
        · rw [ind_of_pos rfl, mul_one]
        · exact fun x _ hx => by rw [ind_of_neg (Ne.symm hx), mul_zero, zero_mul]
        · simp
    _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun C _ => ?_
        ring

/-- The total mass of the rows of a node, given the input sequence. -/
lemma sum_nncNodeAt (hpx : ∀ k, IsPMF (px k)) (hq : ∀ k, IsChannel (q k)) (b : ∀ k, NNCBr M K k)
    (x : ∀ k, Fin n → X k) (k : Fin N) :
    ∑ c, nncNodeAt px q M K n b x k c = iidPMF (px k) n (x k) := by
  classical
  have h₁ := sum_piLaw_mul_eval (ν := fun _ : NNCBr M K k => nncRow (px k) (q k) n (K k))
    (fun _ => nncRow_isPMF (hpx k) (hq k)) (b k) fun r => ind (r.1 = x k)
  have h₂ := sum_nncRow_fst (p := px k) (K := K k) (hq k) (n := n) fun a => ind (a = x k)
  simp only [nncNodeAt, nncNodeLaw]
  rw [h₁, h₂, Finset.sum_eq_single (x k)]
  · rw [ind_of_pos rfl, mul_one]
  · exact fun a _ ha => by rw [ind_of_neg ha, mul_zero]
  · simp

lemma nncNodeAt_nonneg (hpx : ∀ k, IsPMF (px k)) (hq : ∀ k, IsChannel (q k))
    (b : ∀ k, NNCBr M K k) (x : ∀ k, Fin n → X k) (k : Fin N)
    (c : NNCBr M K k → NNCRow n (K k) (X k) (V k)) : 0 ≤ nncNodeAt px q M K n b x k c :=
  mul_nonneg ((nncNodeLaw_isPMF hpx hq k).nonneg c) (ind_nonneg _)

end Block

/-! ### The test for a wrong row -/

section Test

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {M K : Fin N → ℕ} {px : ∀ k, X k → ℝ} {q : ∀ k, X k → V k → ℝ}
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {τ : ∀ k, X k × Y k → V k → ℝ}

/-- The sequences of a node for the test: the sequence of the row `b' k` and the sequence of index
`idx` of its codebook. -/
def nncCon (C : NNCBlock M K n X V) (b b' : ∀ k, NNCBr M K k)
    (idx : ∀ k, NNCRow n (K k) (X k) (V k) → (Fin n → Y k) → Fin (K k))
    (y : Fin n → ∀ k, Y k) (k : Fin N) : (Fin n → X k) × (Fin n → V k) :=
  ((C k (b' k)).1, (C k (b' k)).2 (idx k (C k (b k)) (yOf k y)))

/-- **The bound on the probability of the test.** The nodes of `S` are those for which the row that
is tested is not the true row. Whatever the index of each node, as long as it is a function of its
true row and of its received sequence, the test passes with probability about `exp(-n J(S))`. -/
theorem sum_nncBlock_test_le (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W)
    (hτ : ∀ k, IsChannel (τ k))
    (hq : ∀ k a b, nncRho (nncLaw px W τ) k (a, b) =
      dist (nncLaw px W τ) (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    (hqc : ∀ k, IsChannel (q k)) (b b' : ∀ k, NNCBr M K k)
    (idx : ∀ k, NNCRow n (K k) (X k) (V k) → (Fin n → Y k) → Fin (K k)) (d : Fin N) (ε : ℝ) :
    ∑ C, nncBlockLaw px q M K n C * ∑ y, seqChan W n (xAt (nncX C b)) y *
      ind (nncTest (nncLaw px W τ) d ε (nncCon C b b' idx y) (yOf d y)) ≤
    exp (-(n * (nncJ (nncLaw px W τ) (univ.filter fun k => b' k ≠ b k) d -
      ε * nncC (nncLaw px W τ) (univ.filter fun k => b' k ≠ b k) d))) := by
  classical
  have hL := nncLaw_isPMF hpx hW hτ (V := V)
  set L := nncLaw px W τ with hLd
  set S := univ.filter fun k => b' k ≠ b k with hS
  set E := exp (-(n * (nncJ L S d - ε * nncC L S d))) with hE
  rw [sum_nncBlock_split]
  have hin : ∀ (x : ∀ k, Fin n → X k) (y : Fin n → ∀ k, Y k),
      ∑ C, prodLaw (nncNodeAt px q M K n b x) C * ind (nncTest L d ε (nncCon C b b' idx y) (yOf d
        y))
        ≤ (∏ k, iidPMF (px k) n (x k)) * E := by
    intro x y
    let f : ∀ k, (NNCBr M K k → NNCRow n (K k) (X k) (V k)) → (Fin n → X k) × (Fin n → V k) :=
      fun k c => ((c (b' k)).1, (c (b' k)).2 (idx k (c (b k)) (yOf k y)))
    have h₁ := sum_prodLaw_comp (nncNodeAt px q M K n b x) f
      fun c => ind (nncTest L d ε c (yOf d y))
    have h₂ : ∀ C : NNCBlock M K n X V, (fun k => f k (C k)) = nncCon C b b' idx y := fun _ => rfl
    simp_rw [h₂] at h₁
    rw [h₁]
    let μ : ∀ k, (Fin n → X k) × (Fin n → V k) → ℝ := fun k => dist (nncNodeAt px q M K n b x k) (f
      k)
    have hμ0 : ∀ k c, 0 ≤ μ k c := fun k c => sum_nonneg fun _ _ => by
      split_ifs
      · exact nncNodeAt_nonneg hpx hqc b x k _
      · exact le_rfl
    have hsum : ∀ k, ∑ c, μ k c = iidPMF (px k) n (x k) := fun k => by
      rw [sum_dist]
      exact sum_nncNodeAt hpx hqc b x k
    have hdist : ∀ k, dist L (fun ω : NNCΩ X Y V => ω.1 k) = px k :=
      fun k => dist_nncLaw_x hpx hW hτ k
    have hfresh := sum_nnc_fresh_le hL hq hqc S d (a := fun k => iidPMF (px k) n (x k))
      (fun k => (iidPMF_isPMF (hpx k) n).nonneg _) μ hμ0 (fun k hk c => ?_)
      (fun k _ => (hsum k).le) (yd := yOf d y) (ε := ε)
    · exact hfresh
    -- the sequences of a fresh node
    have hne : b k ≠ b' k := (mem_filter.mp hk).2.symm
    have hval : μ k c = ∑ a : NNCBr M K k → NNCRow n (K k) (X k) (V k),
        nncNodeLaw px q M K n k a * (ind ((a (b k)).1 = x k) *
          ind (((a (b' k)).1, (a (b' k)).2 (idx k (a (b k)) (yOf k y))) = c)) := by
      simp only [μ, dist, nncNodeAt, f, ind]
      refine sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    have h₃ := sum_piLaw_mul_eval₂ (ν := fun _ : NNCBr M K k => nncRow (px k) (q k) n (K k))
      (fun _ => nncRow_isPMF (hpx k) (hqc k)) hne fun r r' => ind (r.1 = x k) *
        ind ((r'.1, r'.2 (idx k r (yOf k y))) = c)
    have hval' : μ k c = iidPMF (px k) n (x k) *
      (iidPMF (px k) n c.1 * seqChan (q k) n c.1 c.2) := by
      rw [hval]
      refine h₃.trans ?_
      have h₄ : ∀ r : NNCRow n (K k) (X k) (V k), ∑ r', nncRow (px k) (q k) n (K k) r *
          nncRow (px k) (q k) n (K k) r' * (ind (r.1 = x k) *
            ind ((r'.1, r'.2 (idx k r (yOf k y))) = c)) =
          nncRow (px k) (q k) n (K k) r * ind (r.1 = x k) *
            (iidPMF (px k) n c.1 * seqChan (q k) n c.1 c.2) := by
        intro r
        rw [← sum_nncRow_ind_entry (hqc k) (idx k r (yOf k y)) c, mul_sum]
        exact sum_congr rfl fun r' _ => by ring
      simp_rw [h₄]
      rw [← sum_mul, sum_nncRow_fst (hqc k) fun a => ind (a = x k), Finset.sum_eq_single (x k)]
      · rw [ind_of_pos rfl, mul_one]
      · exact fun a _ ha => by rw [ind_of_neg ha, mul_zero]
      · simp
    rw [hval', hdist]
  calc _ ≤ ∑ x, ∑ y, seqChan W n (xAt x) y * ((∏ k, iidPMF (px k) n (x k)) * E) :=
        sum_le_sum fun x _ => sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hin x y)
          ((seqChan_isChannel hW n _).nonneg _)
    _ = (∑ x : ∀ k, Fin n → X k, ∑ y : Fin n → ∀ k, Y k, nncXY px W x y) * E := by
        rw [sum_mul]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun y _ => ?_
        simp only [nncXY]
        ring
    _ = E := by rw [sum_nncXY hpx hW, one_mul]

/-- The descriptions of a block: each node picks a sequence of its true row. -/
def nncVOf (C : NNCBlock M K n X V) (b : ∀ k, NNCBr M K k)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (y : Fin n → ∀ k, Y k) (k : Fin N) : Fin n → V k :=
  (C k (b k)).2 (pk k (C k (b k)).1 (C k (b k)).2 (yOf k y))

/-- **The probability that the tuple of the true rows is not typical** is a probability of the
hybrid argument. -/
theorem sum_nncBlock_bad_eq (hpx : ∀ k, IsPMF (px k)) (hqc : ∀ k, IsChannel (q k))
    (b : ∀ k, NNCBr M K k)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop) :
    ∑ C, nncBlockLaw px q M K n C * ∑ y, seqChan W n (xAt (nncX C b)) y *
      ind (Bad (nncX C b) y (nncVOf C b pk y)) =
    nncHyb px W (fun k => nncSel (seqChan (q k) n) (K k) (pk k)) Bad := by
  classical
  rw [sum_nncBlock_split]
  simp only [nncHyb]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [nncXY]
  rw [mul_comm (∏ k, iidPMF (px k) n (x k)), mul_assoc]
  congr 1
  -- the left side, as a sum over the codebooks of the true rows
  let f : ∀ k, (NNCBr M K k → NNCRow n (K k) (X k) (V k)) → (Fin (K k) → Fin n → V k) :=
    fun k c => (c (b k)).2
  let g : (∀ k, Fin (K k) → Fin n → V k) → ℝ := fun t =>
    ind (Bad x y fun k => t k (pk k (x k) (t k) (yOf k y)))
  have hsup : ∀ C : NNCBlock M K n X V, prodLaw (nncNodeAt px q M K n b x) C *
      ind (Bad (nncX C b) y (nncVOf C b pk y)) =
      prodLaw (nncNodeAt px q M K n b x) C * g fun k => f k (C k) := by
    intro C
    by_cases h : nncX C b = x
    · have hv : nncVOf C b pk y = fun k => (C k (b k)).2 (pk k (x k) (C k (b k)).2 (yOf k y)) := by
        funext k
        have := congrFun h k
        simp only [nncX] at this
        simp only [nncVOf, this]
      rw [h, hv]
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      have h0 : prodLaw (nncNodeAt px q M K n b x) C = 0 := by
        refine prod_eq_zero (mem_univ k) ?_
        simp only [nncNodeAt]
        rw [ind_of_neg (show ¬ (C k (b k)).1 = x k from hk), mul_zero]
      rw [h0, zero_mul, zero_mul]
  simp_rw [hsup]
  rw [sum_prodLaw_comp (nncNodeAt px q M K n b x) f g]
  have hd : ∀ k (t : Fin (K k) → Fin n → V k), dist (nncNodeAt px q M K n b x k) (f k) t =
      iidPMF (px k) n (x k) * iidPMF (seqChan (q k) n (x k)) (K k) t := by
    intro k t
    have h₁ := sum_piLaw_mul_eval (ν := fun _ : NNCBr M K k => nncRow (px k) (q k) n (K k))
      (fun _ => nncRow_isPMF (hpx k) (hqc k)) (b k) fun r => ind (r.1 = x k) * ind (r.2 = t)
    have h₂ : dist (nncNodeAt px q M K n b x k) (f k) t =
        ∑ c, nncNodeLaw px q M K n k c * (ind ((c (b k)).1 = x k) * ind ((c (b k)).2 = t)) := by
      simp only [dist, nncNodeAt, f, ind]
      refine sum_congr rfl fun c _ => ?_
      split_ifs <;> simp
    rw [h₂]
    refine h₁.trans ?_
    simp only [nncRow, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (x k)]
    · rw [Finset.sum_eq_single t]
      · rw [ind_of_pos rfl, ind_of_pos rfl, mul_one, mul_one]
      · exact fun u _ hu => by rw [ind_of_neg hu, mul_zero, mul_zero]
      · simp
    · intro a _ ha
      refine sum_eq_zero fun u _ => ?_
      rw [ind_of_neg ha, zero_mul, mul_zero]
    · simp
  -- the right side
  let f' : ∀ k, (Fin (K k) → Fin n → V k) → Fin n → V k :=
    fun k t => t (pk k (x k) t (yOf k y))
  have h₃ := sum_prodLaw_comp (fun k => iidPMF (seqChan (q k) n (x k)) (K k)) f'
    fun v => ind (Bad x y v)
  have hsel : ∀ k (c : Fin n → V k), dist (iidPMF (seqChan (q k) n (x k)) (K k)) (f' k) c =
      nncSel (seqChan (q k) n) (K k) (pk k) (x k) (yOf k y) c := by
    intro k c
    simp only [dist, nncSel, f', ind]
    refine sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  simp only [prodLaw, hsel] at h₃
  rw [← h₃, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  simp only [prodLaw, hd, prod_mul_distrib]
  simp only [g, f']
  ring

end Test

end InfoTheory
