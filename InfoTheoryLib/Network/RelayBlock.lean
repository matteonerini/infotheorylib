/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.JSCCMAC
public import InfoTheoryLib.Network.RelayCode

/-!
# The relay channel: the random code of one block

Partial decode–forward uses one code in all blocks, with three layers of codewords: `x₁ⁿ(l)`,
`uⁿ(a | l)` and `xⁿ(c | a, l)`. The relay knows `l` and decodes `a`. The receiver, going backward,
knows `a` and decodes `(l, c)`. This file proves the random coding bound for these two decoders.

## Main definitions

* `ind P`: the indicator of a proposition, as a real number.
* `seqChan κ n`: `n` uses of the channel `κ`.
* `RelayBlock`, `RelayBlock.err`, `RelayBlock.avgErr`: a code for one block and its errors.

## Main statements

* `sum_fresh_le`: the bound for a fresh sequence, which covers all the error events.
* `eval_true₃`, `eval_a₃`, `eval_c₃`, `eval_l₃`: the law of the entries of the tables of a code.
* `sum_tablesLaw_err_le`, `exists_relayBlock_le`: **the random coding bound**.

## Implementation notes

As in the joint source–channel code of Lecture 15, the entries of the tables are indexed also by the
sequences that they are conditioned on, so that all the entries are independent.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Indicators -/

open Classical in
/-- The indicator of a proposition. -/
def ind (P : Prop) : ℝ := if P then 1 else 0

lemma ind_nonneg (P : Prop) : 0 ≤ ind P := by
  unfold ind
  split_ifs <;> norm_num

lemma ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num

lemma ind_of_pos {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]

lemma ind_of_neg {P : Prop} (h : ¬ P) : ind P = 0 := by simp [ind, h]

lemma ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  by_cases hP : P
  · rw [ind_of_pos hP, ind_of_pos (h hP)]
  · rw [ind_of_neg hP]
    exact ind_nonneg Q

lemma ind_or_le (P Q : Prop) : ind (P ∨ Q) ≤ ind P + ind Q := by
  by_cases hP : P
  · rw [ind_of_pos (Or.inl hP), ind_of_pos hP]
    linarith [ind_nonneg Q]
  · by_cases hQ : Q
    · rw [ind_of_pos (Or.inr hQ), ind_of_pos hQ]
      linarith [ind_nonneg P]
    · rw [ind_of_neg (by tauto)]
      exact add_nonneg (ind_nonneg _) (ind_nonneg _)

/-- The indicator of an existence statement is at most the sum of the indicators. -/
lemma ind_exists_le {ι : Type*} [Fintype ι] (P : ι → Prop) : ind (∃ i, P i) ≤ ∑ i, ind (P i) := by
  by_cases h : ∃ i, P i
  · obtain ⟨i, hi⟩ := h
    rw [ind_of_pos ⟨i, hi⟩]
    calc (1 : ℝ) = ind (P i) := (ind_of_pos hi).symm
      _ ≤ _ := single_le_sum (f := fun i => ind (P i)) (fun i _ => ind_nonneg _) (mem_univ i)
  · rw [ind_of_neg h]
    exact sum_nonneg fun i _ => ind_nonneg _

/-- The same over a finite set. -/
lemma ind_exists_mem_le {ι : Type*} (s : Finset ι) (P : ι → Prop) :
    ind (∃ i, i ∈ s ∧ P i) ≤ ∑ i ∈ s, ind (P i) := by
  by_cases h : ∃ i, i ∈ s ∧ P i
  · obtain ⟨i, hs, hi⟩ := h
    rw [ind_of_pos ⟨i, hs, hi⟩]
    calc (1 : ℝ) = ind (P i) := (ind_of_pos hi).symm
      _ ≤ _ := single_le_sum (f := fun i => ind (P i)) (fun i _ => ind_nonneg _) hs
  · rw [ind_of_neg h]
    exact sum_nonneg fun i _ => ind_nonneg _

/-! ### Uses of a channel -/

section Seq

variable {K N : Type*} [Fintype N]

/-- `n` uses of the channel `κ`. -/
def seqChan (κ : K → N → ℝ) (n : ℕ) (k : Fin n → K) (t : Fin n → N) : ℝ := ∏ i, κ (k i) (t i)

lemma seqChan_isChannel {κ : K → N → ℝ} (hκ : IsChannel κ) (n : ℕ) : IsChannel (seqChan κ n) := by
  classical
  intro k
  refine ⟨fun t => prod_nonneg fun i _ => (hκ _).nonneg _, ?_⟩
  simp only [seqChan]
  rw [← Fintype.piFinset_univ, ← prod_univ_sum]
  exact prod_eq_one fun i _ => (hκ _).sum_eq_one

end Seq

/-! ### A fresh sequence -/

section Fresh

variable {V N K : Type*} [Fintype V] [Fintype N] [Fintype K]

/-- **The bound for a fresh sequence.** Let `(V, T) ∼ L`. Let a sequence `tⁿ` be generated, given
`vⁿ`, by `n` uses of the conditional law of `T` given `K = g(V)`. Then the probability that
`(vⁿ, tⁿ)` is jointly typical is about `exp(-n I(T; V | K))`. All the error events of the decoders
are of this form. -/
theorem sum_fresh_le {L : V × N → ℝ} (hL : IsPMF L) (g : V → K) {κ : K → N → ℝ}
    (hκ : ∀ k t, dist L (fun z => (g z.1, z.2)) (k, t) = dist L (fun z => g z.1) k * κ k t)
    (hκc : IsChannel κ) {n : ℕ} {ε : ℝ} (Test : (Fin n → V) → (Fin n → N) → Prop)
    (hT : ∀ r t, Test r t → (fun i => (r i, t i)) ∈ robustTypicalSet L n ε) :
    ∑ r, iidPMF (dist L Prod.fst) n r * ∑ t, seqChan κ n (fun i => g (r i)) t * ind (Test r t) ≤
      exp (-(n * (H[Prod.fst ; L] + H[fun z => (g z.1, z.2) ; L] - H[fun z => g z.1 ; L] -
        entropy L - ε * (entropy L + H[Prod.fst ; L] + H[fun z => (g z.1, z.2) ; L] +
          H[fun z => g z.1 ; L])))) := by
  classical
  set q := dist L Prod.fst with hq
  have hqP : IsPMF q := hL.dist _
  set LK := dist L fun z : V × N => (g z.1, z.2) with hLK
  have hLKP : IsPMF LK := hL.dist _
  set qK := dist L fun z : V × N => g z.1 with hqK
  have hqKP : IsPMF qK := hL.dist _
  set HV := H[Prod.fst ; L] with hHV
  set HKN := H[fun z => (g z.1, z.2) ; L] with hHKN
  set HK := H[fun z => g z.1 ; L] with hHK
  have hHV' : entropy q = HV := rfl
  have hHKN' : entropy LK = HKN := rfl
  have hHK' : entropy qK = HK := rfl
  let w : (Fin n → V) × (Fin n → N) → ℝ := fun x =>
    iidPMF q n x.1 * (seqChan κ n (fun i => g (x.1 i)) x.2 * ind (Test x.1 x.2))
  have hflat : ∑ r, iidPMF q n r * ∑ t, seqChan κ n (fun i => g (r i)) t * ind (Test r t) =
      ∑ x, w x := by
    simp only [w, mul_sum, Fintype.sum_prod_type]
  rw [hflat]
  let M : ℝ := exp (-(n * (HV - ε * HV))) * (exp (-(n * (HKN - ε * HKN))) * exp (n * (HK + ε * HK)))
  have hM : 0 ≤ M := by positivity
  have hbound := sum_typical_le (w := w) (fun x i => (x.1 i, x.2 i)) (robustTypicalSet L n ε) hM
    (fun x hx => by
      have : ¬ Test x.1 x.2 := fun h => hx (hT _ _ h)
      simp [w, ind_of_neg this])
    (fun x y _ _ he => by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · exact (Prod.ext_iff.mp (congrFun he i)).1
      · exact (Prod.ext_iff.mp (congrFun he i)).2)
    (fun x hx => by
      -- the three typical sequences
      have h₁ : x.1 ∈ robustTypicalSet q n ε := comp_mem_robustTypicalSet hx Prod.fst
      have h₂ : (fun i => g (x.1 i)) ∈ robustTypicalSet qK n ε :=
        comp_mem_robustTypicalSet hx fun z : V × N => g z.1
      have h₃ : (fun i => (g (x.1 i), x.2 i)) ∈ robustTypicalSet LK n ε :=
        comp_mem_robustTypicalSet hx fun z : V × N => (g z.1, z.2)
      have e₁ := iidPMF_le_of_mem_robustTypicalSet hqP h₁
      have e₂ := le_iidPMF_of_mem_robustTypicalSet hqKP h₂
      have e₃ := iidPMF_le_of_mem_robustTypicalSet hLKP h₃
      rw [hHV'] at e₁
      rw [hHK'] at e₂
      rw [hHKN'] at e₃
      have hfac : iidPMF LK n (fun i => (g (x.1 i), x.2 i)) =
          iidPMF qK n (fun i => g (x.1 i)) * seqChan κ n (fun i => g (x.1 i)) x.2 := by
        simp only [iidPMF, seqChan, ← prod_mul_distrib]
        exact prod_congr rfl fun i _ => hκ _ _
      have hpos : 0 < iidPMF qK n (fun i => g (x.1 i)) := lt_of_lt_of_le (exp_pos _) e₂
      have hs : seqChan κ n (fun i => g (x.1 i)) x.2 ≤
          exp (-(n * (HKN - ε * HKN))) * exp (n * (HK + ε * HK)) := by
        have h0 : seqChan κ n (fun i => g (x.1 i)) x.2 =
            iidPMF LK n (fun i => (g (x.1 i), x.2 i)) / iidPMF qK n (fun i => g (x.1 i)) := by
          rw [hfac]
          field_simp
        rw [h0, div_le_iff₀ hpos]
        refine e₃.trans ?_
        have hprod : exp (-(n * (HKN - ε * HKN))) = exp (-(n * (HKN - ε * HKN))) *
            exp (n * (HK + ε * HK)) * exp (-(n * (HK + ε * HK))) := by
          rw [mul_assoc, ← exp_add]
          simp
        calc _ = _ := hprod
          _ ≤ _ := mul_le_mul_of_nonneg_left e₂ (mul_pos (exp_pos _) (exp_pos _)).le
      have hc0 := (seqChan_isChannel hκc n (fun i => g (x.1 i))).nonneg x.2
      calc w x ≤ iidPMF q n x.1 * (seqChan κ n (fun i => g (x.1 i)) x.2 * 1) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ind_le_one _) hc0)
              (iidPMF_isPMF hqP n |>.nonneg _)
        _ ≤ M := by
            rw [mul_one]
            exact mul_le_mul e₁ hs hc0 (exp_pos _).le)
  refine hbound.trans ?_
  have hcard := card_robustTypicalSet_le hL n ε
  refine (mul_le_mul_of_nonneg_right hcard hM).trans (le_of_eq ?_)
  simp only [M]
  rw [← exp_add, ← exp_add, ← exp_add]
  congr 1
  ring

end Fresh

/-! ### The tables of a code -/

section Tables

variable {Ma Mc : ℕ} {S U X : Type*} [Fintype S] [Fintype U] [Fintype X] [DecidableEq S]
  [DecidableEq U]

/-- The tables of the three layers. An entry of a layer is indexed also by the entries of the lower
layers that it is generated from. -/
abbrev Tables₃ (Ma Mc : ℕ) (S U X : Type*) : Type _ :=
  (Fin Ma → S) × (Fin Ma × Fin Ma × S → U) × (Fin Ma × Fin Ma × Fin Mc × S × U → X)

variable (τ : S → ℝ) (A : S → U → ℝ) (B : S × U → X → ℝ)

/-- The law of the tables. -/
def tablesLaw (T : Tables₃ Ma Mc S U X) : ℝ :=
  piLaw (fun _ => τ) T.1 * (piLaw (fun i : Fin Ma × Fin Ma × S => A i.2.2) T.2.1 *
    piLaw (fun i : Fin Ma × Fin Ma × Fin Mc × S × U => B i.2.2.2) T.2.2)

variable {τ A B}

/-- The sequence `x₁ⁿ(l)` of the tables. -/
def Tables₃.s (T : Tables₃ Ma Mc S U X) (l : Fin Ma) : S := T.1 l

/-- The sequence `uⁿ(a | l)` of the tables. -/
def Tables₃.u (T : Tables₃ Ma Mc S U X) (l a : Fin Ma) : U := T.2.1 (l, a, T.s l)

/-- The sequence `xⁿ(c | a, l)` of the tables. -/
def Tables₃.x (T : Tables₃ Ma Mc S U X) (l a : Fin Ma) (c : Fin Mc) : X :=
  T.2.2 (l, a, c, T.s l, T.u l a)

open Classical in
lemma sum_tablesLaw_mul (G : (Fin Ma → S) → (Fin Ma × Fin Ma × S → U) →
    (Fin Ma × Fin Ma × Fin Mc × S × U → X) → ℝ) :
    ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * G T.1 T.2.1 T.2.2 =
      ∑ L : Fin Ma → S, piLaw (fun _ => τ) L * ∑ V : Fin Ma × Fin Ma × S → U,
        piLaw (fun i : Fin Ma × Fin Ma × S => A i.2.2) V *
        ∑ Z : Fin Ma × Fin Ma × Fin Mc × S × U → X,
          piLaw (fun i : Fin Ma × Fin Ma × Fin Mc × S × U => B i.2.2.2) Z * G L V Z := by
  simp only [Fintype.sum_prod_type, tablesLaw, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

open Classical in
/-- The sequences of the true triple have the true law. -/
lemma eval_true₃ (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (l a : Fin Ma) (c : Fin Mc)
    (F : S → U → X → ℝ) :
    ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * F (T.s l) (T.u l a) (T.x l a c) =
      ∑ s, τ s * ∑ u, A s u * ∑ x, B (s, u) x * F s u x := by
  refine (sum_tablesLaw_mul (τ := τ) (A := A) (B := B) fun L V Z => F (L l) (V (l, a, L l)) (Z (l,
    a, c, L l, V (l, a, L l)))).trans ?_
  rw [← sum_piLaw_mul_eval (ν := fun _ : Fin Ma => τ) (fun _ => hτ) l
    (fun s => ∑ u, A s u * ∑ x, B (s, u) x * F s u x)]
  refine sum_congr rfl fun L _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval (ν := fun i : Fin Ma × Fin Ma × S => A i.2.2) (fun i => hA i.2.2)
    (l, a, L l) fun u => ∑ x, B (L l, u) x * F (L l) u x]
  refine sum_congr rfl fun V _ => ?_
  congr 1
  exact sum_piLaw_mul_eval (ν := fun i : Fin Ma × Fin Ma × Fin Mc × S × U => B i.2.2.2)
    (fun i => hB i.2.2.2) (l, a, c, L l, V (l, a, L l)) fun x => F (L l) (V (l, a, L l)) x

open Classical in
/-- A wrong index `a'`, given `l`. -/
lemma eval_a₃ (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (l : Fin Ma) {a a' : Fin Ma}
    (ha : a ≠ a') (c : Fin Mc) (F : S → U → U → X → ℝ) :
    ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * F (T.s l) (T.u l a) (T.u l a') (T.x l a c) =
      ∑ s, τ s * ∑ u, A s u * ∑ u', A s u' * ∑ x, B (s, u) x * F s u u' x := by
  refine (sum_tablesLaw_mul (τ := τ) (A := A) (B := B) fun L V Z => F (L l) (V (l, a, L l)) (V (l,
    a', L l))
    (Z (l, a, c, L l, V (l, a, L l)))).trans ?_
  rw [← sum_piLaw_mul_eval (ν := fun _ : Fin Ma => τ) (fun _ => hτ) l
    (fun s => ∑ u, A s u * ∑ u', A s u' * ∑ x, B (s, u) x * F s u u' x)]
  refine sum_congr rfl fun L _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval₂' (ν := fun i : Fin Ma × Fin Ma × S => A i.2.2) (fun i => hA i.2.2)
    (i := (l, a, L l)) (j := (l, a', L l)) (fun e => ha (congrArg (fun z => z.2.1) e))
    fun u u' => ∑ x, B (L l, u) x * F (L l) u u' x]
  refine sum_congr rfl fun V _ => ?_
  congr 1
  exact sum_piLaw_mul_eval (ν := fun i : Fin Ma × Fin Ma × Fin Mc × S × U => B i.2.2.2)
    (fun i => hB i.2.2.2) (l, a, c, L l, V (l, a, L l))
    fun x => F (L l) (V (l, a, L l)) (V (l, a', L l)) x

open Classical in
/-- A wrong index `c'`, given `(l, a)`. -/
lemma eval_c₃ (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (l a : Fin Ma) {c c' : Fin Mc}
    (hc : c ≠ c') (F : S → U → X → X → ℝ) :
    ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * F (T.s l) (T.u l a) (T.x l a c) (T.x l a c') =
      ∑ s, τ s * ∑ u, A s u * ∑ x, B (s, u) x * ∑ x', B (s, u) x' * F s u x x' := by
  refine (sum_tablesLaw_mul (τ := τ) (A := A) (B := B) fun L V Z => F (L l) (V (l, a, L l)) (Z (l,
    a, c, L l, V (l, a, L l)))
    (Z (l, a, c', L l, V (l, a, L l)))).trans ?_
  rw [← sum_piLaw_mul_eval (ν := fun _ : Fin Ma => τ) (fun _ => hτ) l
    (fun s => ∑ u, A s u * ∑ x, B (s, u) x * ∑ x', B (s, u) x' * F s u x x')]
  refine sum_congr rfl fun L _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval (ν := fun i : Fin Ma × Fin Ma × S => A i.2.2) (fun i => hA i.2.2)
    (l, a, L l) fun u => ∑ x, B (L l, u) x * ∑ x', B (L l, u) x' * F (L l) u x x']
  refine sum_congr rfl fun V _ => ?_
  congr 1
  exact sum_piLaw_mul_eval₂' (ν := fun i : Fin Ma × Fin Ma × Fin Mc × S × U => B i.2.2.2)
    (fun i => hB i.2.2.2) (i := (l, a, c, L l, V (l, a, L l)))
    (j := (l, a, c', L l, V (l, a, L l))) (fun e => hc (congrArg (fun z => z.2.2.1) e))
    fun x x' => F (L l) (V (l, a, L l)) x x'

open Classical in
/-- A wrong index `l'`, with any `c'`. -/
lemma eval_l₃ (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) {l l' : Fin Ma} (hl : l ≠ l')
    (a : Fin Ma) (c c' : Fin Mc) (F : S → U → X → S → U → X → ℝ) :
    ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
        F (T.s l) (T.u l a) (T.x l a c) (T.s l') (T.u l' a) (T.x l' a c') =
      ∑ s, τ s * ∑ s', τ s' * ∑ u, A s u * ∑ u', A s' u' * ∑ x, B (s, u) x *
        ∑ x', B (s', u') x' * F s u x s' u' x' := by
  refine (sum_tablesLaw_mul (τ := τ) (A := A) (B := B) fun L V Z => F (L l) (V (l, a, L l)) (Z (l,
    a, c, L l, V (l, a, L l)))
    (L l') (V (l', a, L l')) (Z (l', a, c', L l', V (l', a, L l')))).trans ?_
  rw [← sum_piLaw_mul_eval₂' (ν := fun _ : Fin Ma => τ) (fun _ => hτ) hl
    (fun s s' => ∑ u, A s u * ∑ u', A s' u' * ∑ x, B (s, u) x *
      ∑ x', B (s', u') x' * F s u x s' u' x')]
  refine sum_congr rfl fun L _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval₂' (ν := fun i : Fin Ma × Fin Ma × S => A i.2.2) (fun i => hA i.2.2)
    (i := (l, a, L l)) (j := (l', a, L l')) (fun e => hl (congrArg Prod.fst e))
    fun u u' => ∑ x, B (L l, u) x * ∑ x', B (L l', u') x' * F (L l) u x (L l') u' x']
  refine sum_congr rfl fun V _ => ?_
  congr 1
  exact sum_piLaw_mul_eval₂' (ν := fun i : Fin Ma × Fin Ma × Fin Mc × S × U => B i.2.2.2)
    (fun i => hB i.2.2.2) (i := (l, a, c, L l, V (l, a, L l)))
    (j := (l', a, c', L l', V (l', a, L l'))) (fun e => hl (congrArg Prod.fst e))
    fun x x' => F (L l) (V (l, a, L l)) x (L l') (V (l', a, L l')) x'

end Tables

/-! ### Codes for one block -/

/-- **A code for one block**, on a channel from `X × S` to `Y × Y₁`. The sender sends `x l a c`, the
relay sends `s l`. The relay, knowing `l`, decodes `a`, and the receiver, knowing `a`, decodes
`(l, c)`. -/
structure RelayBlock (Ma Mc : ℕ) (S X Y Y₁ : Type*) where
  /-- The codewords of the relay. -/
  s : Fin Ma → S
  /-- The codewords of the sender. -/
  x : Fin Ma → Fin Ma → Fin Mc → X
  /-- The decoder of the relay. -/
  rDec : Fin Ma → Y₁ → Fin Ma
  /-- The decoder of the receiver. -/
  dDec : Fin Ma → Y → Fin Ma × Fin Mc

section Block

variable {Ma Mc : ℕ} {S U X Y Y₁ : Type*} [Fintype S] [Fintype U] [Fintype X] [Fintype Y]
  [Fintype Y₁]

/-- The probability that one of the two decoders is wrong, for the indices `(l, a, c)`. -/
def RelayBlock.err (C : RelayBlock Ma Mc S X Y Y₁) (V : X × S → Y × Y₁ → ℝ) (l a : Fin Ma)
    (c : Fin Mc) : ℝ :=
  ∑ z, V (C.x l a c, C.s l) z * (ind (C.rDec l z.2 ≠ a) + ind (C.dDec a z.1 ≠ (l, c)))

/-- The errors that matter: for the first block, where `l` is fixed, for the blocks in the middle,
and for the last block, where `a` and `c` are fixed. -/
def RelayBlock.avgErr [NeZero Ma] [NeZero Mc] (C : RelayBlock Ma Mc S X Y Y₁)
    (V : X × S → Y × Y₁ → ℝ) : ℝ :=
  (∑ a, ∑ c, C.err V 0 a c) / (Ma * Mc) + (∑ l, ∑ a, ∑ c, C.err V l a c) / (Ma * Ma * Mc) +
    (∑ l, C.err V l 0 0) / Ma

variable [DecidableEq S] [DecidableEq U] {τ : S → ℝ} {A : S → U → ℝ} {B : S × U → X → ℝ}
  {V : X × S → Y × Y₁ → ℝ} {T₁ : S → U → Y₁ → Prop} {T₂ : S → U → X → Y → Prop}

open Classical in
/-- The code of the tables, with the decoders that look for the unique index that passes the test.
-/
def Tables₃.code [NeZero Ma] [NeZero Mc] (T : Tables₃ Ma Mc S U X) (T₁ : S → U → Y₁ → Prop)
    (T₂ : S → U → X → Y → Prop) : RelayBlock Ma Mc S X Y Y₁ where
  s := T.s
  x := T.x
  rDec l y₁ := if h : ∃! a, T₁ (T.s l) (T.u l a) y₁ then Classical.choose h else 0
  dDec a y := if h : ∃! p : Fin Ma × Fin Mc, T₂ (T.s p.1) (T.u p.1 a) (T.x p.1 a p.2) y
    then Classical.choose h else (0, 0)

omit [Fintype S] [Fintype U] [Fintype X] [Fintype Y] [Fintype Y₁] [DecidableEq S]
  [DecidableEq U] in
lemma Tables₃.rDec_ne [NeZero Ma] [NeZero Mc] (T : Tables₃ Ma Mc S U X) {l a : Fin Ma} {y₁ : Y₁}
    (h : (T.code (Y := Y) T₁ T₂).rDec l y₁ ≠ a) :
    ¬ T₁ (T.s l) (T.u l a) y₁ ∨ ∃ a', a' ≠ a ∧ T₁ (T.s l) (T.u l a') y₁ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have hu : ∃! a', T₁ (T.s l) (T.u l a') y₁ := ⟨a, h₁, fun a' ha' => by
    by_contra hne
    exact h₂ a' hne ha'⟩
  refine h ?_
  simp only [Tables₃.code, dite_eq_left hu]
  exact hu.unique (Classical.choose_spec hu).1 h₁

omit [Fintype S] [Fintype U] [Fintype X] [Fintype Y] [Fintype Y₁] [DecidableEq S]
  [DecidableEq U] in
lemma Tables₃.dDec_ne [NeZero Ma] [NeZero Mc] (T : Tables₃ Ma Mc S U X) {l a : Fin Ma}
    {c : Fin Mc} {y : Y} (h : (T.code (Y₁ := Y₁) T₁ T₂).dDec a y ≠ (l, c)) :
    ¬ T₂ (T.s l) (T.u l a) (T.x l a c) y ∨
      (∃ c', c' ≠ c ∧ T₂ (T.s l) (T.u l a) (T.x l a c') y) ∨
      ∃ l', l' ≠ l ∧ ∃ c', T₂ (T.s l') (T.u l' a) (T.x l' a c') y := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂, h₃⟩ := hcon
  have hu : ∃! p : Fin Ma × Fin Mc, T₂ (T.s p.1) (T.u p.1 a) (T.x p.1 a p.2) y := by
    refine ⟨(l, c), h₁, ?_⟩
    rintro ⟨l', c'⟩ hp
    by_cases hl : l' = l
    · subst hl
      by_cases hc : c' = c
      · rw [hc]
      · exact absurd hp (h₂ c' hc)
    · exact absurd hp (h₃ l' hl c')
  refine h ?_
  simp only [Tables₃.code, dite_eq_left hu]
  exact hu.unique (Classical.choose_spec hu).1 h₁

variable (τ A B V T₁ T₂)

/-- The probability that the true sequences do not pass the tests. -/
def relayF₀ : ℝ :=
  ∑ s, τ s * ∑ u, A s u * ∑ x, B (s, u) x * ∑ z, V (x, s) z *
    ind (¬ T₁ s u z.2 ∨ ¬ T₂ s u x z.1)

/-- The probability that a wrong `a'` passes the test of the relay. -/
def relayFa : ℝ :=
  ∑ s, τ s * ∑ u, A s u * ∑ u', A s u' * ∑ x, B (s, u) x * ∑ z, V (x, s) z * ind (T₁ s u' z.2)

/-- The probability that a wrong `c'` passes the test of the receiver. -/
def relayFc : ℝ :=
  ∑ s, τ s * ∑ u, A s u * ∑ x, B (s, u) x * ∑ x', B (s, u) x' * ∑ z, V (x, s) z *
    ind (T₂ s u x' z.1)

/-- The probability that a wrong `l'`, with any `c'`, passes the test of the receiver. -/
def relayFl : ℝ :=
  ∑ s, τ s * ∑ s', τ s' * ∑ u, A s u * ∑ u', A s' u' * ∑ x, B (s, u) x *
    ∑ x', B (s', u') x' * ∑ z, V (x, s) z * ind (T₂ s' u' x' z.1)

variable {τ A B V T₁ T₂}

section Nonneg

omit [DecidableEq S] [DecidableEq U]

lemma relayF₀_nonneg (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V) :
    0 ≤ relayF₀ τ A B V T₁ T₂ :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) <| sum_nonneg fun u _ =>
    mul_nonneg ((hA s).nonneg u) <| sum_nonneg fun x _ =>
    mul_nonneg ((hB _).nonneg x) <| sum_nonneg fun z _ => mul_nonneg ((hV _).nonneg z) (ind_nonneg
      _)

lemma relayFa_nonneg (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V) :
    0 ≤ relayFa τ A B V T₁ :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) <| sum_nonneg fun u _ =>
    mul_nonneg ((hA s).nonneg u) <| sum_nonneg fun u' _ =>
    mul_nonneg ((hA s).nonneg u') <| sum_nonneg fun x _ =>
    mul_nonneg ((hB _).nonneg x) <| sum_nonneg fun z _ => mul_nonneg ((hV _).nonneg z) (ind_nonneg
      _)

lemma relayFc_nonneg (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V) :
    0 ≤ relayFc τ A B V T₂ :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) <| sum_nonneg fun u _ =>
    mul_nonneg ((hA s).nonneg u) <| sum_nonneg fun x _ =>
    mul_nonneg ((hB _).nonneg x) <| sum_nonneg fun x' _ =>
    mul_nonneg ((hB _).nonneg x') <| sum_nonneg fun z _ =>
      mul_nonneg ((hV _).nonneg z) (ind_nonneg _)

lemma relayFl_nonneg (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V) :
    0 ≤ relayFl τ A B V T₂ :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) <| sum_nonneg fun s' _ =>
    mul_nonneg (hτ.nonneg s') <| sum_nonneg fun u _ =>
    mul_nonneg ((hA s).nonneg u) <| sum_nonneg fun u' _ =>
    mul_nonneg ((hA s').nonneg u') <| sum_nonneg fun x _ =>
    mul_nonneg ((hB _).nonneg x) <| sum_nonneg fun x' _ =>
    mul_nonneg ((hB _).nonneg x') <| sum_nonneg fun z _ =>
      mul_nonneg ((hV _).nonneg z) (ind_nonneg _)

end Nonneg

lemma tablesLaw_isPMF (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) :
    IsPMF (tablesLaw (Ma := Ma) (Mc := Mc) τ A B) := by
  classical
  have h₁ : IsPMF (piLaw fun _ : Fin Ma => τ) := piLaw_isPMF fun _ => hτ
  have h₂ : IsPMF (piLaw fun i : Fin Ma × Fin Ma × S => A i.2.2) := piLaw_isPMF fun i => hA i.2.2
  have h₃ : IsPMF (piLaw fun i : Fin Ma × Fin Ma × Fin Mc × S × U => B i.2.2.2) :=
    piLaw_isPMF fun i => hB i.2.2.2
  refine ⟨fun T => mul_nonneg (h₁.nonneg _) (mul_nonneg (h₂.nonneg _) (h₃.nonneg _)), ?_⟩
  simp only [Fintype.sum_prod_type, tablesLaw, ← mul_sum, h₃.sum_eq_one, h₂.sum_eq_one,
    h₁.sum_eq_one, mul_one]

open Classical in
/-- **The random coding bound.** The expected probability of error of the code of the tables, for
any indices. -/
theorem sum_tablesLaw_err_le [NeZero Ma] [NeZero Mc] (hτ : IsPMF τ) (hA : IsChannel A)
    (hB : IsChannel B) (hV : IsChannel V) (l a : Fin Ma) (c : Fin Mc) :
    ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * (T.code T₁ T₂).err V l a c ≤
      2 * relayF₀ τ A B V T₁ T₂ + (Ma - 1) * relayFa τ A B V T₁ + (Mc - 1) * relayFc τ A B V T₂ +
        (Ma * Mc) * relayFl τ A B V T₂ := by
  have hlaw := (tablesLaw_isPMF (Ma := Ma) (Mc := Mc) hτ hA hB).nonneg
  -- the pointwise bound
  let G₀ : S → U → X → ℝ := fun s u x => ∑ z, V (x, s) z * ind (¬ T₁ s u z.2 ∨ ¬ T₂ s u x z.1)
  let Ga : S → U → U → X → ℝ := fun s _ u' x => ∑ z, V (x, s) z * ind (T₁ s u' z.2)
  let Gc : S → U → X → X → ℝ := fun s u x x' => ∑ z, V (x, s) z * ind (T₂ s u x' z.1)
  let Gl : S → U → X → S → U → X → ℝ := fun s _ x s' u' x' =>
    ∑ z, V (x, s) z * ind (T₂ s' u' x' z.1)
  have hswap : ∀ {ι : Type _} (t : Finset ι) (v : Y × Y₁ → ℝ) (f : ι → Y × Y₁ → ℝ),
      ∑ z, v z * ∑ i ∈ t, f i z = ∑ i ∈ t, ∑ z, v z * f i z := by
    intro ι t v f
    simp_rw [mul_sum]
    exact sum_comm
  have hpoint : ∀ T : Tables₃ Ma Mc S U X, (T.code T₁ T₂).err V l a c ≤
      2 * G₀ (T.s l) (T.u l a) (T.x l a c) +
      ∑ a' ∈ univ.erase a, Ga (T.s l) (T.u l a) (T.u l a') (T.x l a c) +
      ∑ c' ∈ univ.erase c, Gc (T.s l) (T.u l a) (T.x l a c) (T.x l a c') +
      ∑ l' ∈ univ.erase l, ∑ c', Gl (T.s l) (T.u l a) (T.x l a c) (T.s l') (T.u l' a)
        (T.x l' a c') := by
    intro T
    set v : Y × Y₁ → ℝ := V (T.x l a c, T.s l) with hv
    have hv0 : ∀ z, 0 ≤ v z := fun z => (hV _).nonneg z
    let E₀ : Y × Y₁ → Prop := fun z =>
      ¬ T₁ (T.s l) (T.u l a) z.2 ∨ ¬ T₂ (T.s l) (T.u l a) (T.x l a c) z.1
    have hr : ∀ z : Y × Y₁, ind ((T.code T₁ T₂).rDec l z.2 ≠ a) ≤ ind (E₀ z) +
        ∑ a' ∈ univ.erase a, ind (T₁ (T.s l) (T.u l a') z.2) := by
      intro z
      refine le_trans (ind_mono fun h => ?_) (ind_or_le (E₀ z)
        (∃ a', a' ∈ univ.erase a ∧ T₁ (T.s l) (T.u l a') z.2)) |>.trans
        (add_le_add le_rfl (ind_exists_mem_le _ _))
      rcases T.rDec_ne (Y := Y) h with h' | ⟨a', hne, ha'⟩
      · exact Or.inl (Or.inl h')
      · exact Or.inr ⟨a', mem_erase.mpr ⟨hne, mem_univ _⟩, ha'⟩
    have hd : ∀ z : Y × Y₁, ind ((T.code T₁ T₂).dDec a z.1 ≠ (l, c)) ≤ ind (E₀ z) +
        (∑ c' ∈ univ.erase c, ind (T₂ (T.s l) (T.u l a) (T.x l a c') z.1) +
          ∑ l' ∈ univ.erase l, ∑ c', ind (T₂ (T.s l') (T.u l' a) (T.x l' a c') z.1)) := by
      intro z
      have hlast : ind (∃ l', l' ∈ univ.erase l ∧ ∃ c', T₂ (T.s l') (T.u l' a) (T.x l' a c') z.1) ≤
          ∑ l' ∈ univ.erase l, ∑ c', ind (T₂ (T.s l') (T.u l' a) (T.x l' a c') z.1) :=
        (ind_exists_mem_le _ _).trans (sum_le_sum fun l' _ => ind_exists_le _)
      refine le_trans (ind_mono fun h => ?_) (ind_or_le (E₀ z)
        ((∃ c', c' ∈ univ.erase c ∧ T₂ (T.s l) (T.u l a) (T.x l a c') z.1) ∨
          ∃ l', l' ∈ univ.erase l ∧ ∃ c', T₂ (T.s l') (T.u l' a) (T.x l' a c') z.1)) |>.trans
        (add_le_add le_rfl ((ind_or_le _ _).trans
          (add_le_add (ind_exists_mem_le _ _) hlast)))
      rcases T.dDec_ne (Y₁ := Y₁) h with h' | ⟨c', hne, hc'⟩ | ⟨l', hne, c', hc'⟩
      · exact Or.inl (Or.inr h')
      · exact Or.inr (Or.inl ⟨c', mem_erase.mpr ⟨hne, mem_univ _⟩, hc'⟩)
      · exact Or.inr (Or.inr ⟨l', mem_erase.mpr ⟨hne, mem_univ _⟩, c', hc'⟩)
    have hstep : (T.code T₁ T₂).err V l a c ≤ ∑ z, v z * (2 * ind (E₀ z) +
        ∑ a' ∈ univ.erase a, ind (T₁ (T.s l) (T.u l a') z.2) +
        ∑ c' ∈ univ.erase c, ind (T₂ (T.s l) (T.u l a) (T.x l a c') z.1) +
        ∑ l' ∈ univ.erase l, ∑ c', ind (T₂ (T.s l') (T.u l' a) (T.x l' a c') z.1)) := by
      refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hv0 z)
      linarith [hr z, hd z]
    refine hstep.trans (le_of_eq ?_)
    simp only [mul_add, sum_add_distrib, G₀, Ga, Gc, Gl]
    rw [hswap, hswap, hswap]
    simp_rw [hswap]
    congr 3
    rw [mul_sum]
    exact sum_congr rfl fun z _ => by ring
  -- the expectations
  have ha : ∑ a' ∈ univ.erase a, ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
      Ga (T.s l) (T.u l a) (T.u l a') (T.x l a c) ≤ (Ma - 1) * relayFa τ A B V T₁ := by
    refine le_of_eq ?_
    calc _ = ∑ _a' ∈ univ.erase a, relayFa τ A B V T₁ :=
          sum_congr rfl fun a' ha' => eval_a₃ hτ hA hB l (ne_of_mem_erase ha').symm c Ga
      _ = #(univ.erase a) * relayFa τ A B V T₁ := by rw [sum_const, nsmul_eq_mul]
      _ = _ := by
          rw [card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin,
            Nat.cast_sub (NeZero.pos Ma)]
          norm_num
  have hc : ∑ c' ∈ univ.erase c, ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
      Gc (T.s l) (T.u l a) (T.x l a c) (T.x l a c') ≤ (Mc - 1) * relayFc τ A B V T₂ := by
    refine le_of_eq ?_
    calc _ = ∑ _c' ∈ univ.erase c, relayFc τ A B V T₂ :=
          sum_congr rfl fun c' hc' => eval_c₃ hτ hA hB l a (ne_of_mem_erase hc').symm Gc
      _ = #(univ.erase c) * relayFc τ A B V T₂ := by rw [sum_const, nsmul_eq_mul]
      _ = _ := by
          rw [card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin,
            Nat.cast_sub (NeZero.pos Mc)]
          norm_num
  have hl : ∑ l' ∈ univ.erase l, ∑ c', ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
      Gl (T.s l) (T.u l a) (T.x l a c) (T.s l') (T.u l' a) (T.x l' a c') ≤
      (Ma * Mc) * relayFl τ A B V T₂ := by
    have hF := relayFl_nonneg (T₂ := T₂) hτ hA hB hV
    calc _ = ∑ _l' ∈ univ.erase l, ∑ _c' : Fin Mc, relayFl τ A B V T₂ :=
          sum_congr rfl fun l' hl' => sum_congr rfl fun c' _ =>
            eval_l₃ hτ hA hB (ne_of_mem_erase hl').symm a c c' Gl
      _ = #(univ.erase l) * (Mc * relayFl τ A B V T₂) := by
          simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]
      _ ≤ _ := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) hF
          have : #(univ.erase l) ≤ Ma := (card_le_univ _).trans (by simp)
          exact_mod_cast this
  have h₀ : ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * G₀ (T.s l) (T.u l a) (T.x l a c) =
      relayF₀ τ A B V T₁ T₂ := eval_true₃ hτ hA hB l a c G₀
  calc _ ≤ ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
        (2 * G₀ (T.s l) (T.u l a) (T.x l a c) +
        ∑ a' ∈ univ.erase a, Ga (T.s l) (T.u l a) (T.u l a') (T.x l a c) +
        ∑ c' ∈ univ.erase c, Gc (T.s l) (T.u l a) (T.x l a c) (T.x l a c') +
        ∑ l' ∈ univ.erase l, ∑ c', Gl (T.s l) (T.u l a) (T.x l a c) (T.s l') (T.u l' a)
          (T.x l' a c')) := sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hpoint T) (hlaw T)
    _ = 2 * relayF₀ τ A B V T₁ T₂ + ∑ a' ∈ univ.erase a, ∑ T : Tables₃ Ma Mc S U X,
          tablesLaw τ A B T * Ga (T.s l) (T.u l a) (T.u l a') (T.x l a c) +
        ∑ c' ∈ univ.erase c, ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
          Gc (T.s l) (T.u l a) (T.x l a c) (T.x l a c') +
        ∑ l' ∈ univ.erase l, ∑ c', ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
          Gl (T.s l) (T.u l a) (T.x l a c) (T.s l') (T.u l' a) (T.x l' a c') := by
        rw [← h₀, mul_sum]
        simp only [mul_add, sum_add_distrib, mul_sum]
        congr 1
        · congr 1
          · congr 1
            · exact sum_congr rfl fun T _ => by ring
            · exact sum_comm
          · exact sum_comm
        · rw [sum_comm]
          exact sum_congr rfl fun l' _ => sum_comm
    _ ≤ _ := by linarith

omit [DecidableEq S] [DecidableEq U] in
/-- **The random coding bound**, with the three kinds of blocks. -/
theorem exists_relayBlock_le [NeZero Ma] [NeZero Mc] (hτ : IsPMF τ) (hA : IsChannel A)
    (hB : IsChannel B) (hV : IsChannel V) :
    ∃ C : RelayBlock Ma Mc S X Y Y₁, C.avgErr V ≤ 3 * (2 * relayF₀ τ A B V T₁ T₂ +
      (Ma - 1) * relayFa τ A B V T₁ + (Mc - 1) * relayFc τ A B V T₂ +
        (Ma * Mc) * relayFl τ A B V T₂) := by
  classical
  set β := 2 * relayF₀ τ A B V T₁ T₂ + (Ma - 1) * relayFa τ A B V T₁ +
    (Mc - 1) * relayFc τ A B V T₂ + (Ma * Mc) * relayFl τ A B V T₂ with hβ
  have hP := tablesLaw_isPMF (Ma := Ma) (Mc := Mc) hτ hA hB
  have hMa : (0 : ℝ) < Ma := by exact_mod_cast NeZero.pos Ma
  have hMc : (0 : ℝ) < Mc := by exact_mod_cast NeZero.pos Mc
  have hE := sum_tablesLaw_err_le (T₁ := T₁) (T₂ := T₂) (Ma := Ma) (Mc := Mc) hτ hA hB hV
  by_contra hcon
  push Not at hcon
  have hgt : ∀ T : Tables₃ Ma Mc S U X, 3 * β < (T.code T₁ T₂).avgErr V := fun T => hcon _
  have hsum : ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * (T.code T₁ T₂).avgErr V ≤ 3 * β := by
    have h₁ : ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
        ((∑ a, ∑ c, (T.code T₁ T₂).err V 0 a c) / (Ma * Mc)) ≤ β := by
      simp_rw [mul_div_assoc', mul_sum, ← sum_div]
      rw [div_le_iff₀ (by positivity)]
      calc _ = ∑ a : Fin Ma, ∑ c : Fin Mc, ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
            (T.code T₁ T₂).err V 0 a c := by
            rw [sum_comm]
            exact sum_congr rfl fun a _ => sum_comm
        _ ≤ ∑ _a : Fin Ma, ∑ _c : Fin Mc, β :=
            sum_le_sum fun a _ => sum_le_sum fun c _ => hE 0 a c
        _ = _ := by simp; ring
    have h₂ : ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
        ((∑ l, ∑ a, ∑ c, (T.code T₁ T₂).err V l a c) / (Ma * Ma * Mc)) ≤ β := by
      simp_rw [mul_div_assoc', mul_sum, ← sum_div]
      rw [div_le_iff₀ (by positivity)]
      calc _ = ∑ l : Fin Ma, ∑ a : Fin Ma, ∑ c : Fin Mc, ∑ T : Tables₃ Ma Mc S U X,
            tablesLaw τ A B T * (T.code T₁ T₂).err V l a c := by
            rw [sum_comm]
            refine sum_congr rfl fun l _ => ?_
            rw [sum_comm]
            exact sum_congr rfl fun a _ => sum_comm
        _ ≤ ∑ _l : Fin Ma, ∑ _a : Fin Ma, ∑ _c : Fin Mc, β :=
            sum_le_sum fun l _ => sum_le_sum fun a _ => sum_le_sum fun c _ => hE l a c
        _ = _ := by simp; ring
    have h₃ : ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
        ((∑ l, (T.code T₁ T₂).err V l 0 0) / Ma) ≤ β := by
      simp_rw [mul_div_assoc', mul_sum, ← sum_div]
      rw [div_le_iff₀ (by positivity)]
      calc _ = ∑ l : Fin Ma, ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T *
            (T.code T₁ T₂).err V l 0 0 := sum_comm
        _ ≤ ∑ _l : Fin Ma, β := sum_le_sum fun l _ => hE l 0 0
        _ = _ := by simp; ring
    simp only [RelayBlock.avgErr, mul_add, sum_add_distrib]
    linarith
  have hlt : 3 * β < ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * (T.code T₁ T₂).avgErr V := by
    have hne : ∃ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T ≠ 0 := by
      by_contra hz
      push Not at hz
      have := hP.sum_eq_one
      simp [hz] at this
    obtain ⟨T₀, hT₀⟩ := hne
    calc 3 * β = ∑ T : Tables₃ Ma Mc S U X, tablesLaw τ A B T * (3 * β) := by
          rw [← sum_mul, hP.sum_eq_one, one_mul]
      _ < _ := sum_lt_sum (fun T _ => mul_le_mul_of_nonneg_left (hgt T).le (hP.nonneg T))
          ⟨T₀, mem_univ _, mul_lt_mul_of_pos_left (hgt T₀)
            (lt_of_le_of_ne (hP.nonneg T₀) (Ne.symm hT₀))⟩
  linarith

end Block

end InfoTheory
