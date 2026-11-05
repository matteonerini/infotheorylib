/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DFCode

/-!
# Decode–forward: the genie run

In the genie run, all the nodes know the messages. Since a new code is drawn for each block, the
blocks of the genie run are independent, and the probability that a wrong message passes the tests
of a decoder is a product over its window of blocks.

## Main definitions

* `dfPB`: the law of a block of the genie run.
* `DFGood`: the good event of the genie run.

## Main statements

* `sum_dfPB_not_typ`: the probability that a block is not typical.
* `sum_dfGenie_win_le`: **the probability that a wrong message passes the tests**.
* `sum_dfGenie_not_good_le`: the probability that the genie run is not good.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Genie

variable {N Mm n : ℕ} {X Y : Fin N → Type*} [NeZero Mm] [∀ k, Fintype (X k)]
  [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] (d₀ : ∀ l, X l) {p : (∀ l, X l) → ℝ}
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {κ : ∀ k, (∀ l, X l) → X k → ℝ}

/-- The randomness of a block: the code and the outputs. -/
abbrev DFΞ (N Mm n : ℕ) (X Y : Fin N → Type*) := DFBlock N Mm n X × (Fin n → ∀ k, Y k)

/-- The law of a block of the genie run, for a tag. -/
def dfPB (κ : ∀ k, (∀ l, X l) → X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (τ : DFTag N Mm)
    (ξ : DFΞ N Mm n X Y) : ℝ :=
  dfBlockLaw κ Mm n ξ.1 * seqChan W n (dfX d₀ ξ.1 τ) ξ.2

omit [NeZero Mm] in
lemma dfPB_isPMF [NeZero Mm] (hκc : ∀ k, IsChannel (κ k)) (hW : IsChannel W) (τ : DFTag N Mm) :
    IsPMF (dfPB (n := n) d₀ κ W τ) := by
  have hB := dfBlockLaw_isPMF (X := X) (Mm := Mm) (n := n) hκc
  refine ⟨fun ξ => mul_nonneg (hB.nonneg _) ((seqChan_isChannel hW n _).nonneg _), ?_⟩
  simp only [dfPB, Fintype.sum_prod_type]
  simp_rw [← mul_sum, (seqChan_isChannel hW n _).sum_eq_one, mul_one]
  exact hB.sum_eq_one

/-- The event that a block is typical. -/
def dfTyp (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ) (τ : DFTag N Mm) (ξ : DFΞ N Mm n X Y) : Prop :=
  (fun i => (dfX d₀ ξ.1 τ i, ξ.2 i)) ∈ robustTypicalSet L₀ n ε

/-- **The probability that a block is not typical.** -/
theorem sum_dfPB_not_typ (hp : IsPMF p) (hW : IsChannel W) (hκc : ∀ k, IsChannel (κ k))
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) (ε : ℝ)
    (τ : DFTag N Mm) :
    ∑ ξ : DFΞ N Mm n X Y, dfPB d₀ κ W τ ξ * ind (¬ dfTyp d₀ (jointOf p W) ε τ ξ) =
      1 - prob (iidPMF (jointOf p W) n) (robustTypicalSet (jointOf p W) n ε) := by
  classical
  have hL := iidPMF_isPMF (jointOf_isPMF hp hW) n
  simp only [dfPB, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← mul_sum]
  have h₁ := sum_dfBlock_true (Mm := Mm) d₀ hp hκc hκ τ
    (G := fun x : Fin n → ∀ l, X l => ∑ y, seqChan W n x y *
      ind ((fun i => (x i, y i)) ∉ robustTypicalSet (jointOf p W) n ε))
  refine h₁.trans ?_
  have e₂ : prob (iidPMF (jointOf p W) n) (robustTypicalSet (jointOf p W) n ε) =
      ∑ ω, if ω ∈ robustTypicalSet (jointOf p W) n ε then iidPMF (jointOf p W) n ω else 0 := by
    rw [prob, sum_ite_mem, univ_inter]
  let e : (Fin n → (∀ l, X l) × (∀ l, Y l)) ≃ (Fin n → ∀ l, X l) × (Fin n → ∀ l, Y l) :=
    Equiv.arrowProdEquivProdArrow _ _ _
  have hz : ∀ ω : Fin n → (∀ l, X l) × (∀ l, Y l), iidPMF (jointOf p W) n ω =
      iidPMF p n (e ω).1 * seqChan W n (e ω).1 (e ω).2 := fun ω => by
    simp only [iidPMF, seqChan, jointOf, prod_mul_distrib]
    rfl
  rw [eq_sub_iff_add_eq, e₂, ← hL.sum_eq_one]
  have hs : ∑ ω, iidPMF (jointOf p W) n ω = ∑ x, ∑ y, iidPMF p n x * seqChan W n x y := by
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv e _ _ hz
  have hs' : ∑ ω, (if ω ∈ robustTypicalSet (jointOf p W) n ε then iidPMF (jointOf p W) n ω else 0) =
      ∑ x, ∑ y, iidPMF p n x * seqChan W n x y *
        ind ((fun i => (x i, y i)) ∈ robustTypicalSet (jointOf p W) n ε) := by
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv e _ _ fun ω => ?_
    rw [← hz]
    simp only [ind]
    have : (fun i => ((e ω).1 i, (e ω).2 i)) = ω := rfl
    rw [this]
    split_ifs <;> simp
  rw [hs', hs, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : (fun i => (x i, y i)) ∈ robustTypicalSet (jointOf p W) n ε
  · rw [ind_of_neg (not_not.mpr h), ind_of_pos h]
    ring
  · rw [ind_of_pos h, ind_of_neg h]
    ring

/-- The test of the decoder `d` at the position `t` of its window, for the message `m_j`. -/
def dfEvt (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ) (d : Fin N) (a : ℕ → Fin Mm) (j t : ℕ)
    (ξ : DFΞ N Mm n X Y) : Prop :=
  if h : t < N then dfTest d₀ L₀ ⟨t, h⟩ d ε (dfX d₀ ξ.1 (dfTagOf a (j + t))) (fun i => ξ.2 i d)
  else True

/-- The exponent of the tests of the decoder `d`:
`∑_{k < d} I(X_k; Y_d | X_{k+1}^N) = I(X^{d-1}; Y_d | X_d^N)`, up to the typicality parameter. -/
def dfEd (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ) (d : Fin N) : ℝ :=
  ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < d), (dfE d₀ L₀ k d - ε * dfC d₀ L₀ k d)

set_option synthInstance.maxSize 1024 in
/-- **Page 19-17 of [elgamal2010]: the probability that a wrong message passes the tests.** The
blocks are independent, so this is a product over the window of the decoder. -/
theorem sum_dfGenie_win_le (hp : IsPMF p) (hW : IsChannel W) (hκc : ∀ k, IsChannel (κ k))
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) {b : ℕ}
    (msg : ℕ → Fin Mm) (d : Fin N) {j : ℕ} (hj : ∀ t, t < (d : ℕ) → j + t < b) {m : Fin Mm}
    (hm : m ≠ msg j) (ε : ℝ) (dξ : DFΞ N Mm n X Y) :
    ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw (fun B : Fin b => dfPB d₀ κ W (dfTagOf msg B)) ξ *
      ind (∀ t, t < (d : ℕ) →
        dfEvt d₀ (jointOf p W) ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) ≤
    exp (-(n * dfEd d₀ (jointOf p W) ε d)) := by
  classical
  set L₁ := jointOf p W with hL₁
  have hν := fun B : Fin b => dfPB_isPMF (n := n) d₀ (Y := Y) hκc hW (dfTagOf (N := N) msg B)
  -- the factors
  let h : Fin b → DFΞ N Mm n X Y → ℝ := fun B v =>
    if j ≤ (B : ℕ) ∧ (B : ℕ) - j < d then
      ind (dfEvt d₀ L₁ ε d (Function.update msg j m) j ((B : ℕ) - j) v) else 1
  have hind : ∀ ξ : Fin b → DFΞ N Mm n X Y, ind (∀ t, t < (d : ℕ) →
      dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) ≤ ∏ B, h B (ξ B) := by
    intro ξ
    by_cases hw : ∀ t, t < (d : ℕ) →
        dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))
    · rw [ind_of_pos hw]
      refine le_of_eq (prod_eq_one fun B _ => ?_).symm
      simp only [h]
      split_ifs with hB
      · refine ind_of_pos ?_
        have := hw ((B : ℕ) - j) hB.2
        have e : j + ((B : ℕ) - j) = B := by omega
        rw [e, arrOf_coe] at this
        exact this
      · rfl
    · rw [ind_of_neg hw]
      refine prod_nonneg fun B _ => ?_
      simp only [h]
      split_ifs
      · exact ind_nonneg _
      · exact zero_le_one
  -- the factor of a block
  set e' : ℕ → ℝ := fun t => if ht : t < N then
    exp (-(n * (dfE d₀ L₁ ⟨t, ht⟩ d - ε * dfC d₀ L₁ ⟨t, ht⟩ d))) else 1 with he'
  have hfac : ∀ B : Fin b, ∑ v, dfPB d₀ κ W (dfTagOf msg B) v * h B v ≤
      if j ≤ (B : ℕ) ∧ (B : ℕ) - j < d then e' ((B : ℕ) - j) else 1 := by
    intro B
    by_cases hB : j ≤ (B : ℕ) ∧ (B : ℕ) - j < d
    · simp only [h, hB, and_self, ite_true]
      have htN : (B : ℕ) - j < N := hB.2.trans d.2
      have ht := sum_dfBlock_test_le (Mm := Mm) (n := n) d₀ hW hp hκc hκ
        (τ := dfTagOf msg B) (τ' := dfTagOf (Function.update msg j m) B)
        ⟨(B : ℕ) - j, htN⟩ d (by
          simp only [dfTagOf]
          have h₁ : (B : ℕ) - j ≤ B := Nat.sub_le _ _
          rw [ite_eq_left h₁, ite_eq_left h₁]
          have h₂ : (B : ℕ) - ((B : ℕ) - j) = j := by omega
          rw [h₂, Function.update_self]
          exact hm) (fun l hl => by
          simp only [dfTagOf] at hl ⊢
          split_ifs with hle
          · refine Function.update_of_ne ?_ _ _
            omega
          · rfl) ε
      simp only [he', htN, dite_true]
      refine le_trans (le_of_eq ?_) ht
      simp only [dfPB, Fintype.sum_prod_type, dfEvt, htN, dite_true]
      refine sum_congr rfl fun C _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun y _ => ?_
      have e : j + ((B : ℕ) - j) = B := by omega
      rw [e, mul_assoc]
    · simp only [h, hB, ite_false, mul_one]
      exact (hν B).sum_eq_one.le
  have hc0 : ∀ B : Fin b, 0 ≤ ∑ v, dfPB d₀ κ W (dfTagOf msg B) v * h B v := fun B =>
    sum_nonneg fun v _ => mul_nonneg ((hν B).nonneg v) (by
      simp only [h]
      split_ifs
      · exact ind_nonneg _
      · exact zero_le_one)
  have hprod : ∏ B : Fin b, (if j ≤ (B : ℕ) ∧ (B : ℕ) - j < d then e' ((B : ℕ) - j) else 1) =
      exp (-(n * dfEd d₀ L₁ ε d)) := by
    rw [← prod_filter]
    have h₁ : exp (-(n * dfEd d₀ L₁ ε d)) =
        ∏ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < d), e' k := by
      rw [dfEd, mul_sum, ← sum_neg_distrib, exp_sum]
      refine prod_congr rfl fun k _ => ?_
      simp only [he', k.2, dite_true]
    rw [h₁]
    refine prod_bij (fun B hB => (⟨(B : ℕ) - j, by
      have := (mem_filter.mp hB).2.2
      have := d.2
      omega⟩ : Fin N)) (fun B hB => ?_) (fun a ha a' ha' he => ?_) (fun k hk => ?_) fun B _ => rfl
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hB).2.2⟩
    · have h₂ := (mem_filter.mp ha).2.1
      have h₃ := (mem_filter.mp ha').2.1
      have h₄ := congrArg Fin.val he
      simp only at h₄
      exact Fin.ext (by omega)
    · have hk' : (k : ℕ) < d := (mem_filter.mp hk).2
      refine ⟨⟨j + k, hj k hk'⟩, mem_filter.mpr ⟨mem_univ _, by simp; omega⟩, ?_⟩
      exact Fin.ext (by simp)
  calc _ ≤ ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw (fun B : Fin b => dfPB d₀ κ W (dfTagOf msg B)) ξ *
        ∏ B, h B (ξ B) :=
        sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (hind ξ) (piLaw_nonneg hν ξ)
    _ = ∏ B : Fin b, ∑ v, dfPB d₀ κ W (dfTagOf msg B) v * h B v := sum_piLaw_mul_prod _ h
    _ ≤ ∏ B : Fin b, (if j ≤ (B : ℕ) ∧ (B : ℕ) - j < d then e' ((B : ℕ) - j) else 1) :=
        prod_le_prod₀ (fun B _ => hc0 B) fun B _ => hfac B
    _ = _ := hprod

set_option synthInstance.maxSize 1024 in
/-- The good event of the genie run: the blocks are typical, and no wrong message passes the tests
of a decoder. -/
def DFGood (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ) (msg : ℕ → Fin Mm) (B' : ℕ) {b : ℕ}
    (dξ : DFΞ N Mm n X Y) (ξ : Fin b → DFΞ N Mm n X Y) : Prop :=
  (∀ B : Fin b, dfTyp d₀ L₀ ε (dfTagOf msg B) (ξ B)) ∧ ∀ d : Fin N, (d : ℕ) ≠ 0 → ∀ j, j < B' →
    ∀ m, m ≠ msg j → ¬ ∀ t, t < (d : ℕ) →
      dfEvt d₀ L₀ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))

set_option synthInstance.maxSize 1024 in
/-- **The probability that the genie run is not good.** -/
theorem sum_dfGenie_not_good_le (hp : IsPMF p) (hW : IsChannel W) (hκc : ∀ k, IsChannel (κ k))
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) {b B' : ℕ}
    (hb : B' + N ≤ b) (msg : ℕ → Fin Mm) (ε : ℝ) (dξ : DFΞ N Mm n X Y) {e : ℝ}
    (he : ∀ d : Fin N, (d : ℕ) ≠ 0 → exp (-(n * dfEd d₀ (jointOf p W) ε d)) ≤ e) (he0 : 0 ≤ e) :
    ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw (fun B : Fin b => dfPB d₀ κ W (dfTagOf msg B)) ξ *
      ind (¬ DFGood d₀ (jointOf p W) ε msg B' dξ ξ) ≤
    b * (1 - prob (iidPMF (jointOf p W) n) (robustTypicalSet (jointOf p W) n ε)) +
      N * (B' * (Mm * e)) := by
  classical
  set L₁ := jointOf p W with hL₁
  have hν := fun B : Fin b => dfPB_isPMF (n := n) d₀ (Y := Y) hκc hW (dfTagOf (N := N) msg B)
  set ν := fun B : Fin b => dfPB (n := n) d₀ κ W (dfTagOf (N := N) msg B) with hνd
  -- the union bound
  have hunion : ∀ ξ : Fin b → DFΞ N Mm n X Y, ind (¬ DFGood d₀ L₁ ε msg B' dξ ξ) ≤
      ∑ B : Fin b, ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) (ξ B)) +
      ∑ d : Fin N, ∑ j ∈ range B', ∑ m : Fin Mm, ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧ ∀ t, t < (d : ℕ) →
        dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) := by
    intro ξ
    have h₀ : 0 ≤ ∑ B : Fin b, ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) (ξ B)) :=
      sum_nonneg fun _ _ => ind_nonneg _
    have h₀' : 0 ≤ ∑ d : Fin N, ∑ j ∈ range B', ∑ m : Fin Mm, ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧
        ∀ t, t < (d : ℕ) →
          dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => ind_nonneg _
    by_cases hg : DFGood d₀ L₁ ε msg B' dξ ξ
    · rw [ind_of_neg (not_not.mpr hg)]
      linarith
    rw [ind_of_pos hg]
    simp only [DFGood, not_and_or] at hg
    rcases hg with hg | hg
    · push Not at hg
      obtain ⟨B, hB⟩ := hg
      have : (1 : ℝ) ≤ ∑ B : Fin b, ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) (ξ B)) := by
        refine le_trans (le_of_eq (ind_of_pos hB).symm) (single_le_sum
          (f := fun B : Fin b => ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) (ξ B)))
          (fun _ _ => ind_nonneg _) (mem_univ B))
      linarith
    · push Not at hg
      obtain ⟨d, hd, j, hjB, m, hm, hw⟩ := hg
      have : (1 : ℝ) ≤ ∑ d : Fin N, ∑ j ∈ range B', ∑ m : Fin Mm, ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧
          ∀ t, t < (d : ℕ) →
            dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) := by
        refine le_trans ?_ (single_le_sum (f := fun d : Fin N => ∑ j ∈ range B', ∑ m : Fin Mm,
          ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧ ∀ t, t < (d : ℕ) →
            dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))))
          (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => ind_nonneg _) (mem_univ d))
        refine le_trans ?_ (single_le_sum (f := fun j => ∑ m : Fin Mm,
          ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧ ∀ t, t < (d : ℕ) →
            dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))))
          (fun _ _ => sum_nonneg fun _ _ => ind_nonneg _) (mem_range.mpr hjB))
        refine le_trans (le_of_eq (ind_of_pos ⟨hd, hm, hw⟩).symm) (single_le_sum
          (f := fun m : Fin Mm => ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧ ∀ t, t < (d : ℕ) →
            dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))))
          (fun _ _ => ind_nonneg _) (mem_univ m))
      linarith
  -- the terms of the union bound
  have htyp : ∀ B : Fin b, ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw ν ξ *
      ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) (ξ B)) = 1 - prob (iidPMF L₁ n) (robustTypicalSet L₁ n ε)
        := by
    intro B
    rw [sum_piLaw_mul_eval hν B fun v => ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) v)]
    exact sum_dfPB_not_typ d₀ hp hW hκc hκ ε _
  have hwin : ∀ (d : Fin N) (j : ℕ), j ∈ range B' → ∀ m : Fin Mm,
      ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw ν ξ * ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧ ∀ t, t < (d : ℕ) →
        dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) ≤ e := by
    intro d j hj m
    by_cases hc : (d : ℕ) ≠ 0 ∧ m ≠ msg j
    · have hjb : ∀ t, t < (d : ℕ) → j + t < b := fun t ht => by
        have := mem_range.mp hj
        have := d.2
        omega
      have h₁ := sum_dfGenie_win_le d₀ hp hW hκc hκ msg d hjb hc.2 ε dξ
      refine le_trans (sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (ind_mono fun h => h.2.2)
        (piLaw_nonneg hν ξ)) (h₁.trans (he d hc.1))
    · have : ∀ ξ : Fin b → DFΞ N Mm n X Y, piLaw ν ξ * ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧
          ∀ t, t < (d : ℕ) →
            dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) = 0 := fun ξ => by
        rw [ind_of_neg fun h => hc ⟨h.1, h.2.1⟩, mul_zero]
      simp_rw [this]
      simpa using he0
  calc _ ≤ ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw ν ξ *
        (∑ B : Fin b, ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) (ξ B)) +
        ∑ d : Fin N, ∑ j ∈ range B', ∑ m : Fin Mm, ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧ ∀ t, t < (d : ℕ) →
          dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t)))) :=
        sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (hunion ξ) (piLaw_nonneg hν ξ)
    _ = ∑ B : Fin b, ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw ν ξ *
          ind (¬ dfTyp d₀ L₁ ε (dfTagOf msg B) (ξ B)) +
        ∑ d : Fin N, ∑ j ∈ range B', ∑ m : Fin Mm, ∑ ξ : Fin b → DFΞ N Mm n X Y, piLaw ν ξ *
          ind ((d : ℕ) ≠ 0 ∧ m ≠ msg j ∧ ∀ t, t < (d : ℕ) →
            dfEvt d₀ L₁ ε d (Function.update msg j m) j t (arrOf dξ ξ (j + t))) := by
        simp_rw [mul_add, sum_add_distrib, mul_sum]
        congr 1
        · exact sum_comm
        · rw [sum_comm]
          refine sum_congr rfl fun d _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          exact sum_comm
    _ ≤ ∑ _B : Fin b, (1 - prob (iidPMF L₁ n) (robustTypicalSet L₁ n ε)) +
        ∑ _d : Fin N, ∑ _j ∈ range B', ∑ _m : Fin Mm, e :=
        add_le_add (sum_le_sum fun B _ => (htyp B).le)
          (sum_le_sum fun d _ => sum_le_sum fun j hj => sum_le_sum fun m _ => hwin d j hj m)
    _ = _ := by
        simp [sum_const, card_univ, nsmul_eq_mul]
        ring

/-- On the good event, the true message passes the tests of the decoders. -/
lemma dfWin_true_of_good {L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ} {ε : ℝ} {msg : ℕ → Fin Mm} {B' b : ℕ}
    (hb : B' + N ≤ b) {dξ : DFΞ N Mm n X Y} {ξ : Fin b → DFΞ N Mm n X Y}
    (h : ∀ B : Fin b, dfTyp d₀ L₀ ε (dfTagOf msg B) (ξ B)) (d : Fin N) {j : ℕ} (hj : j < B') :
    dfWin d₀ L₀ ε (fun B => (arrOf dξ ξ B).1) d (fun B i => (arrOf dξ ξ B).2 i d) j msg := by
  intro k hk
  have hjk : j + k < b := by
    have := k.2
    omega
  have h₁ := h ⟨j + k, hjk⟩
  have e : arrOf dξ ξ (j + k) = ξ ⟨j + k, hjk⟩ := arrOf_coe dξ ξ ⟨j + k, hjk⟩
  simp only [e]
  exact comp_mem_robustTypicalSet h₁ fun ω : (∀ l, X l) × (∀ l, Y l) =>
    ((fillGe d₀ (k + 1) ω.1, ω.2 d), ω.1 k)

/-- On the good event, no wrong message passes the tests of the decoders. -/
lemma dfWin_wrong_of_good {L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ} {ε : ℝ} {msg : ℕ → Fin Mm} {B' b : ℕ}
    {dξ : DFΞ N Mm n X Y} {ξ : Fin b → DFΞ N Mm n X Y}
    (h : DFGood d₀ L₀ ε msg B' dξ ξ) {d : Fin N} (hd : (d : ℕ) ≠ 0) {j : ℕ} (hj : j < B') {m : Fin
      Mm}
    (hm : m ≠ msg j) :
    ¬ dfWin d₀ L₀ ε (fun B => (arrOf dξ ξ B).1) d (fun B i => (arrOf dξ ξ B).2 i d) j
      (Function.update msg j m) := by
  intro hw
  refine h.2 d hd j hj m hm fun t ht => ?_
  have htN : t < N := ht.trans d.2
  simp only [dfEvt, htN, dite_true]
  exact hw ⟨t, htN⟩ ht

end Genie

end InfoTheory
