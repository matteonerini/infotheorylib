/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DMNetwork

/-!
# Independent families and trellises

Two tools for the codes of Lecture 19, where the random objects are families indexed by the nodes
and sequences of blocks.

## Main definitions

* `prodLaw ν`: the law of an independent family, with possibly different types.
* `stOf nx a ξ j`: the state after `j` blocks, for a sequence `ξ` of the randomness of the blocks.
* `runProb P nx a ξ`: the probability of a sequence, when the law of a block depends on the state.

## Main statements

* `sum_prodLaw_comp`: the law of a family of functions of the members of an independent family.
* `sum_runProb`: the probabilities of the runs through a trellis sum to one.
* `sum_run_exists_le`: the union bound over the blocks.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Independent families -/

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : ι → Type*} [∀ k, Fintype (A k)]
  [∀ k, Fintype (B k)]

/-- The law of an independent family. -/
def prodLaw (ν : ∀ k, A k → ℝ) (c : ∀ k, A k) : ℝ := ∏ k, ν k (c k)

/-- A sum of products over a family is a product of sums. -/
lemma sum_prod_pi (g : ∀ k, A k → ℝ) : ∑ c : ∀ k, A k, ∏ k, g k (c k) = ∏ k, ∑ a, g k a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

omit [DecidableEq ι] in
lemma prodLaw_nonneg {ν : ∀ k, A k → ℝ} (hν : ∀ k, IsPMF (ν k)) (c : ∀ k, A k) :
    0 ≤ prodLaw ν c :=
  prod_nonneg fun k _ => (hν k).nonneg _

lemma prodLaw_isPMF {ν : ∀ k, A k → ℝ} (hν : ∀ k, IsPMF (ν k)) : IsPMF (prodLaw ν) := by
  refine ⟨prodLaw_nonneg hν, ?_⟩
  simp only [prodLaw]
  rw [sum_prod_pi]
  simp [(hν _).sum_eq_one]

/-- **Functions of the members of an independent family are independent.** -/
theorem sum_prodLaw_comp (ν : ∀ k, A k → ℝ) (f : ∀ k, A k → B k)
    (g : (∀ k, B k) → ℝ) :
    ∑ c : ∀ k, A k, prodLaw ν c * g (fun k => f k (c k)) =
      ∑ r : ∀ k, B k, prodLaw (fun k => dist (ν k) (f k)) r * g r := by
  classical
  have hr : ∀ r : ∀ k, B k, prodLaw (fun k => dist (ν k) (f k)) r =
      ∑ c : ∀ k, A k, ∏ k, if f k (c k) = r k then ν k (c k) else 0 := by
    intro r
    simp only [prodLaw, dist]
    exact (sum_prod_pi (A := A) fun k a => if f k a = r k then ν k a else 0).symm
  simp_rw [hr, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single fun k => f k (c k)]
  · simp [prodLaw]
  · intro r _ hr'
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hr'
    rw [prod_eq_zero (mem_univ k) (ite_eq_right fun h => absurd h.symm hk), zero_mul]
  · simp

/-- The sum over the other members of a family, with one member fixed. -/
lemma sum_ind_prod_erase {ν : ∀ k, A k → ℝ} (hν : ∀ k, IsPMF (ν k)) (j : ι) (a : A j) :
    ∑ c : ∀ k, A k, ind (c j = a) * ∏ k ∈ univ.erase j, ν k (c k) = 1 := by
  classical
  have h₁ : ∀ c : ∀ k, A k, ind (c j = a) * ∏ k ∈ univ.erase j, ν k (c k) =
      ∏ k, (if h : k = j then ind (c k = h ▸ a) else ν k (c k)) := by
    intro c
    rw [← mul_prod_erase univ _ (mem_univ j)]
    simp only [dite_true]
    congr 1
    refine prod_congr rfl fun k hk => ?_
    rw [dite_eq_right (fun h => absurd h (ne_of_mem_erase hk))]
  simp_rw [h₁]
  have h₂ := sum_prod_pi (A := A) fun k (b : A k) =>
    if h : k = j then ind (b = h ▸ a) else ν k b
  rw [h₂]
  refine prod_eq_one fun k _ => ?_
  by_cases h : k = j
  · subst h
    simp only [dite_true]
    rw [Finset.sum_eq_single a]
    · exact ind_of_pos rfl
    · exact fun b _ hb => ind_of_neg hb
    · simp
  · simp only [h, dite_false]
    exact (hν k).sum_eq_one

end Family

/-! ### Trellises -/

section Trellis

variable {Ξ St Lb : Type*}

/-- The state after `j` blocks, for a sequence `ξ` of the randomness of the blocks. -/
def stOf (nx : St → Ξ → St) (a : St) (ξ : ℕ → Ξ) : ℕ → St
  | 0 => a
  | j + 1 => nx (stOf nx a ξ j) (ξ j)

lemma stOf_succ' (nx : St → Ξ → St) (a : St) (ξ : ℕ → Ξ) : ∀ j,
    stOf nx a ξ (j + 1) = stOf nx (nx a (ξ 0)) (fun i => ξ (i + 1)) j
  | 0 => rfl
  | j + 1 => by
    rw [stOf, stOf_succ' nx a ξ j]
    rfl

/-- A finite sequence, extended to the natural numbers by a default value. -/
def arrOf (d : Ξ) {t : ℕ} (ξ : Fin t → Ξ) (j : ℕ) : Ξ := if h : j < t then ξ ⟨j, h⟩ else d

lemma arrOf_coe (d : Ξ) {t : ℕ} (ξ : Fin t → Ξ) (j : Fin t) : arrOf d ξ j = ξ j := by
  simp [arrOf]

lemma arrOf_cons_zero (d : Ξ) {t : ℕ} (x : Ξ) (ξ : Fin t → Ξ) :
    arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ) 0 = x := by
  simp [arrOf]

lemma arrOf_cons_succ (d : Ξ) {t : ℕ} (x : Ξ) (ξ : Fin t → Ξ) (j : ℕ) :
    arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ) (j + 1) = arrOf d ξ j := by
  by_cases h : j < t
  · have h' : j + 1 < t + 1 := by omega
    simp only [arrOf, h, h', dite_true]
    exact Fin.cons_succ (α := fun _ => Ξ) x ξ ⟨j, h⟩
  · have h' : ¬ j + 1 < t + 1 := by omega
    simp [arrOf, h, h']

/-- The probability of a sequence, when the law of a block depends on the state. -/
def runProb (P : St → Ξ → ℝ) (nx : St → Ξ → St) (d : Ξ) (a : St) {t : ℕ} (ξ : Fin t → Ξ) : ℝ :=
  ∏ j : Fin t, P (stOf nx a (arrOf d ξ) j) (ξ j)

lemma runProb_cons (P : St → Ξ → ℝ) (nx : St → Ξ → St) (d : Ξ) (a : St) {t : ℕ} (x : Ξ)
    (ξ : Fin t → Ξ) :
    runProb P nx d a (Fin.cons x ξ : Fin (t + 1) → Ξ) = P a x * runProb P nx d (nx a x) ξ := by
  simp only [runProb]
  rw [Fin.prod_univ_succ]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  have h₁ : stOf nx a (arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ)) (j.succ : Fin (t + 1)) =
      stOf nx (nx a x) (arrOf d ξ) j := by
    have e : ((j.succ : Fin (t + 1)) : ℕ) = (j : ℕ) + 1 := rfl
    rw [e, stOf_succ', arrOf_cons_zero]
    congr 1
    funext i
    exact arrOf_cons_succ d x ξ i
  rw [h₁, Fin.cons_succ]

variable [Fintype Ξ]

/-- A sum over a sequence, from the first element. -/
lemma sum_fin_cons {t : ℕ} (F : (Fin (t + 1) → Ξ) → ℝ) :
    ∑ ξ, F ξ = ∑ x, ∑ ξ : Fin t → Ξ, F (Fin.cons x ξ) := by
  classical
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Ξ) _ _ fun _ => rfl).symm

/-- The total probability of a run is one. -/
lemma sum_runProb {P : St → Ξ → ℝ} (hP : ∀ s, IsPMF (P s)) (nx : St → Ξ → St) (d : Ξ) :
    ∀ (t : ℕ) (a : St), ∑ ξ : Fin t → Ξ, runProb P nx d a ξ = 1
  | 0, a => by simp [runProb]
  | t + 1, a => by
    rw [sum_fin_cons]
    simp_rw [runProb_cons, ← mul_sum, sum_runProb hP nx d t, mul_one, (hP a).sum_eq_one]

lemma runProb_nonneg {P : St → Ξ → ℝ} (hP : ∀ s, IsPMF (P s)) (nx : St → Ξ → St) (d : Ξ) (a : St)
    {t : ℕ} (ξ : Fin t → Ξ) : 0 ≤ runProb P nx d a ξ :=
  prod_nonneg fun _ _ => (hP _).nonneg _

/-- **The union bound over the blocks.** If in each state a block is bad with probability at most
`η`, the probability that some block is bad is at most `t η`. -/
theorem sum_run_exists_le {P : St → Ξ → ℝ} (hP : ∀ s, IsPMF (P s)) (nx : St → Ξ → St) (d : Ξ)
    (Bad : St → Ξ → Prop) {η : ℝ} (hη : ∀ s, ∑ x, P s x * ind (Bad s x) ≤ η) :
    ∀ (t : ℕ) (a : St), ∑ ξ : Fin t → Ξ, runProb P nx d a ξ *
      ind (∃ j : Fin t, Bad (stOf nx a (arrOf d ξ) j) (ξ j)) ≤ t * η
  | 0, a => by simp [ind_of_neg, runProb]
  | t + 1, a => by
    rw [sum_fin_cons]
    have hstep : ∀ (x : Ξ) (ξ : Fin t → Ξ),
        ind (∃ j : Fin (t + 1), Bad (stOf nx a (arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ)) j)
          ((Fin.cons x ξ : Fin (t + 1) → Ξ) j)) ≤
        ind (Bad a x) + ind (∃ j : Fin t, Bad (stOf nx (nx a x) (arrOf d ξ) j) (ξ j)) := by
      intro x ξ
      by_cases h : ∃ j : Fin (t + 1), Bad (stOf nx a (arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ)) j)
          ((Fin.cons x ξ : Fin (t + 1) → Ξ) j)
      · rw [ind_of_pos h]
        obtain ⟨j, hj⟩ := h
        refine Fin.cases (fun hj => ?_) (fun i hj => ?_) j hj
        · have : Bad a x := by simpa [stOf] using hj
          rw [ind_of_pos this]
          linarith [ind_nonneg (∃ j : Fin t, Bad (stOf nx (nx a x) (arrOf d ξ) j) (ξ j))]
        · have e : ((i.succ : Fin (t + 1)) : ℕ) = (i : ℕ) + 1 := rfl
          rw [e, stOf_succ', arrOf_cons_zero, Fin.cons_succ] at hj
          have e₂ : (fun j => arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ) (j + 1)) = arrOf d ξ :=
            funext fun j => arrOf_cons_succ d x ξ j
          rw [e₂] at hj
          rw [ind_of_pos (⟨i, hj⟩ : ∃ j : Fin t, Bad (stOf nx (nx a x) (arrOf d ξ) j) (ξ j))]
          linarith [ind_nonneg (Bad a x)]
      · rw [ind_of_neg h]
        exact add_nonneg (ind_nonneg _) (ind_nonneg _)
    calc _ ≤ ∑ x, ∑ ξ : Fin t → Ξ, P a x * runProb P nx d (nx a x) ξ * (ind (Bad a x) +
          ind (∃ j : Fin t, Bad (stOf nx (nx a x) (arrOf d ξ) j) (ξ j))) := by
          refine sum_le_sum fun x _ => sum_le_sum fun ξ _ => ?_
          rw [runProb_cons]
          exact mul_le_mul_of_nonneg_left (hstep x ξ)
            (mul_nonneg ((hP a).nonneg x) (runProb_nonneg hP nx d _ ξ))
      _ = ∑ x, P a x * (ind (Bad a x) + ∑ ξ : Fin t → Ξ, runProb P nx d (nx a x) ξ *
            ind (∃ j : Fin t, Bad (stOf nx (nx a x) (arrOf d ξ) j) (ξ j))) := by
          refine sum_congr rfl fun x _ => ?_
          have e : ∀ ξ : Fin t → Ξ, P a x * runProb P nx d (nx a x) ξ * (ind (Bad a x) +
              ind (∃ j : Fin t, Bad (stOf nx (nx a x) (arrOf d ξ) j) (ξ j))) =
              P a x * (runProb P nx d (nx a x) ξ * ind (Bad a x)) +
              P a x * (runProb P nx d (nx a x) ξ *
                ind (∃ j : Fin t, Bad (stOf nx (nx a x) (arrOf d ξ) j) (ξ j))) := fun ξ => by ring
          simp_rw [e]
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_mul, sum_runProb hP nx d t, one_mul,
            mul_add]
      _ ≤ ∑ x, P a x * ind (Bad a x) + ∑ x, P a x * (t * η) := by
          rw [← sum_add_distrib]
          refine sum_le_sum fun x _ => ?_
          rw [mul_add]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (sum_run_exists_le hP nx d Bad hη t (nx a x)) ((hP a).nonneg x))
      _ ≤ _ := by
          rw [← sum_mul, (hP a).sum_eq_one, one_mul]
          push_cast
          linarith [hη a]

variable [Fintype Lb]

/-- The labels of a path, with the first label `l`. -/
def pathPrev (l : Lb) {t : ℕ} (ℓ : Fin t → Lb) (j : Fin t) : Lb :=
  (Fin.cons l ℓ : Fin (t + 1) → Lb) j.castSucc

/-- The expected number of paths through the trellis. -/
def pathCount (P : St → Ξ → ℝ) (nx : St → Ξ → St) (d : Ξ) (tst : St → Lb → Lb → Ξ → Prop)
    (t : ℕ) (a : St) (l : Lb) : ℝ :=
  ∑ ξ : Fin t → Ξ, runProb P nx d a ξ * ∑ ℓ : Fin t → Lb,
    ind (∀ j : Fin t, tst (stOf nx a (arrOf d ξ) j) (pathPrev l ℓ j) (ℓ j) (ξ j))

/-- **The recursion of the expected number of paths.** -/
theorem pathCount_succ (P : St → Ξ → ℝ) (nx : St → Ξ → St) (d : Ξ)
    (tst : St → Lb → Lb → Ξ → Prop) (t : ℕ) (a : St) (l : Lb) :
    pathCount P nx d tst (t + 1) a l = ∑ x, P a x * ∑ l', ind (tst a l l' x) *
      pathCount P nx d tst t (nx a x) l' := by
  simp only [pathCount]
  rw [sum_fin_cons]
  refine sum_congr rfl fun x _ => ?_
  have hsplit : ∀ (ξ : Fin t → Ξ) (ℓ' : Fin t → Lb) (l' : Lb),
      ind (∀ j : Fin (t + 1), tst (stOf nx a (arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ)) j)
        (pathPrev l (Fin.cons l' ℓ' : Fin (t + 1) → Lb) j)
        ((Fin.cons l' ℓ' : Fin (t + 1) → Lb) j) ((Fin.cons x ξ : Fin (t + 1) → Ξ) j)) =
      ind (tst a l l' x) * ind (∀ j : Fin t, tst (stOf nx (nx a x) (arrOf d ξ) j)
        (pathPrev l' ℓ' j) (ℓ' j) (ξ j)) := by
    intro ξ ℓ' l'
    have hiff : (∀ j : Fin (t + 1), tst (stOf nx a (arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ)) j)
        (pathPrev l (Fin.cons l' ℓ' : Fin (t + 1) → Lb) j)
        ((Fin.cons l' ℓ' : Fin (t + 1) → Lb) j) ((Fin.cons x ξ : Fin (t + 1) → Ξ) j)) ↔
        tst a l l' x ∧ ∀ j : Fin t, tst (stOf nx (nx a x) (arrOf d ξ) j)
          (pathPrev l' ℓ' j) (ℓ' j) (ξ j) := by
      rw [Fin.forall_fin_succ]
      refine and_congr ?_ (forall_congr' fun j => ?_)
      · simp [pathPrev, stOf]
      · have e : ((j.succ : Fin (t + 1)) : ℕ) = (j : ℕ) + 1 := rfl
        have e₂ : (fun i => arrOf d (Fin.cons x ξ : Fin (t + 1) → Ξ) (i + 1)) = arrOf d ξ :=
          funext fun i => arrOf_cons_succ d x ξ i
        have e₃ : pathPrev l (Fin.cons l' ℓ' : Fin (t + 1) → Lb) j.succ = pathPrev l' ℓ' j := by
          simp only [pathPrev]
          rw [← Fin.succ_castSucc, Fin.cons_succ]
        rw [e, stOf_succ', arrOf_cons_zero, e₂, e₃, Fin.cons_succ, Fin.cons_succ]
    by_cases h₁ : tst a l l' x
    · by_cases h₂ : ∀ j : Fin t, tst (stOf nx (nx a x) (arrOf d ξ) j)
          (pathPrev l' ℓ' j) (ℓ' j) (ξ j)
      · rw [ind_of_pos (hiff.2 ⟨h₁, h₂⟩), ind_of_pos h₁, ind_of_pos h₂, one_mul]
      · rw [ind_of_neg fun h => h₂ (hiff.1 h).2, ind_of_neg h₂, mul_zero]
    · rw [ind_of_neg fun h => h₁ (hiff.1 h).1, ind_of_neg h₁, zero_mul]
  calc _ = ∑ ξ : Fin t → Ξ, P a x * runProb P nx d (nx a x) ξ * ∑ l', ind (tst a l l' x) *
        ∑ ℓ' : Fin t → Lb, ind (∀ j : Fin t, tst (stOf nx (nx a x) (arrOf d ξ) j)
          (pathPrev l' ℓ' j) (ℓ' j) (ξ j)) := by
        refine sum_congr rfl fun ξ _ => ?_
        rw [runProb_cons, sum_fin_cons]
        congr 1
        refine sum_congr rfl fun l' _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun ℓ' _ => hsplit ξ ℓ' l'
    _ = _ := by
        simp only [mul_assoc]
        rw [← mul_sum]
        congr 1
        calc _ = ∑ ξ : Fin t → Ξ, ∑ l', ind (tst a l l' x) * (runProb P nx d (nx a x) ξ *
              ∑ ℓ' : Fin t → Lb, ind (∀ j : Fin t, tst (stOf nx (nx a x) (arrOf d ξ) j)
                (pathPrev l' ℓ' j) (ℓ' j) (ξ j))) := by
              refine sum_congr rfl fun ξ _ => ?_
              rw [mul_sum]
              exact sum_congr rfl fun l' _ => by ring
          _ = _ := by
              rw [sum_comm]
              exact sum_congr rfl fun l' _ => (mul_sum _ _ _).symm

end Trellis

end InfoTheory
