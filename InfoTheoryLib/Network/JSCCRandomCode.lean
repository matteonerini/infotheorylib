/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.CommonInformation

/-!
# Joint source–channel coding over a MAC: the random coding bound

This file proves the random coding bound behind the joint source–channel coding schemes of
Lecture 15 of El Gamal and Kim, for arbitrary finite sets of sequences. Each source sequence `u₁`
with common part `c = g₁(u₁)` gets a codeword `x₁(u₁, w(c))`, where `w(c)` is a random sequence that
represents the common part. The decoder looks for a pair of source sequences with the same common
part whose sequences satisfy a test. The error events split according to which of the source
sequences, and whether the common part, differ from the true ones.

## Main definitions

* `piLaw ν`: the law of a table `T` of independent entries, with `T i ∼ ν i`.
* `jsccF₀`, `jsccFa`, `jsccFb`, `jsccFc`, `jsccFd`, `jsccBound`: the five terms of the bound.

## Main statements

* `sum_piLaw_mul_eval`, `sum_piLaw_mul_eval₂`: the law of one and of two entries of a table.
* `exists_jscc_code_le`: **the random coding bound**.

## Implementation notes

The codewords of `u₁` are a table indexed by `(u₁, s)` for all sequences `s`, independent of the
table of the `w(c)`. The codeword is then `x₁(u₁, w(c))`. In this way all the entries are
independent, and conditioning on `w` is just a matter of evaluating the tables at the right indices.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Tables of independent entries -/

section Table

variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]

/-- The law of a table `T` of independent entries, with `T i ∼ ν i`. -/
def piLaw (ν : I → X → ℝ) (T : I → X) : ℝ := ∏ i, ν i (T i)

omit [DecidableEq I] in
lemma piLaw_nonneg {ν : I → X → ℝ} (hν : ∀ i, IsPMF (ν i)) (T : I → X) : 0 ≤ piLaw ν T :=
  prod_nonneg fun i _ => (hν i).nonneg _

/-- The product of independent functions of the entries. -/
lemma sum_piLaw_mul_prod (ν : I → X → ℝ) (φ : I → X → ℝ) :
    ∑ T : I → X, piLaw ν T * ∏ i, φ i (T i) = ∏ i, ∑ v, ν i v * φ i v := by
  rw [Finset.prod_univ_sum]
  simp only [piLaw, ← prod_mul_distrib, Fintype.piFinset_univ]

lemma piLaw_isPMF {ν : I → X → ℝ} (hν : ∀ i, IsPMF (ν i)) : IsPMF (piLaw ν) := by
  refine ⟨piLaw_nonneg hν, ?_⟩
  have h := sum_piLaw_mul_prod ν fun _ _ => 1
  simp only [prod_const_one, mul_one, (hν _).sum_eq_one] at h
  simpa using h

/-- **The law of one entry of a table.** -/
theorem sum_piLaw_mul_eval {ν : I → X → ℝ} (hν : ∀ i, IsPMF (ν i)) (i : I) (G : X → ℝ) :
    ∑ T : I → X, piLaw ν T * G (T i) = ∑ v, ν i v * G v := by
  have h := sum_piLaw_mul_prod ν fun k v => if k = i then G v else 1
  have e₁ : ∀ T : I → X, ∏ k, (if k = i then G (T k) else 1) = G (T i) := fun T => by
    rw [prod_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have e₂ : ∏ k, ∑ v, ν k v * (if k = i then G v else 1) = ∑ v, ν i v * G v := by
    rw [prod_eq_single i]
    · simp
    · intro k _ hk
      simp [hk, (hν k).sum_eq_one]
    · simp
  simpa only [e₁, e₂] using h

/-- **The law of two different entries of a table: they are independent.** -/
theorem sum_piLaw_mul_eval₂ {ν : I → X → ℝ} (hν : ∀ i, IsPMF (ν i)) {i j : I} (hij : i ≠ j)
    (G : X → X → ℝ) :
    ∑ T : I → X, piLaw ν T * G (T i) (T j) = ∑ v, ∑ v', ν i v * ν j v' * G v v' := by
  classical
  have hsplit : ∀ T : I → X, G (T i) (T j) = ∑ v, ∑ v', G v v' *
      ∏ k, (if k = i then (if T k = v then 1 else 0) else
        if k = j then (if T k = v' then 1 else 0) else 1) := fun T => by
    have e : ∀ v v', (∏ k, (if k = i then (if T k = v then (1 : ℝ) else 0) else
        if k = j then (if T k = v' then 1 else 0) else 1)) =
        (if T i = v then 1 else 0) * (if T j = v' then 1 else 0) := fun v v' => by
      rw [← prod_erase_mul _ _ (mem_univ i), ← prod_erase_mul _ _ (mem_erase.2 ⟨hij.symm, mem_univ
        j⟩)]
      rw [prod_eq_one]
      · simp [hij.symm]
        split_ifs <;> simp
      · intro k hk
        have h1 := (mem_erase.1 (mem_erase.1 hk).2).1
        have h2 := (mem_erase.1 hk).1
        simp [h1, h2]
    simp only [e]
    rw [sum_eq_single (T i), sum_eq_single (T j)]
    · simp
    · intro v' _ hv'
      simp [hv'.symm]
    · simp
    · intro v _ hv
      refine sum_eq_zero fun v' _ => ?_
      simp [hv.symm]
    · simp
  have hprod : ∀ v v', ∑ T : I → X, piLaw ν T *
      ∏ k, (if k = i then (if T k = v then (1 : ℝ) else 0) else
        if k = j then (if T k = v' then 1 else 0) else 1) = ν i v * ν j v' := fun v v' => by
    rw [sum_piLaw_mul_prod ν fun k x => if k = i then (if x = v then (1 : ℝ) else 0) else
      if k = j then (if x = v' then 1 else 0) else 1]
    rw [← prod_erase_mul _ _ (mem_univ i), ← prod_erase_mul _ _ (mem_erase.2 ⟨hij.symm, mem_univ
      j⟩)]
    rw [prod_eq_one]
    · simp [hij.symm]
      ring
    · intro k hk
      have h1 := (mem_erase.1 (mem_erase.1 hk).2).1
      have h2 := (mem_erase.1 hk).1
      simp [h1, h2, (hν k).sum_eq_one]
  simp only [hsplit, mul_sum]
  calc ∑ T : I → X, ∑ v, ∑ v', piLaw ν T * (G v v' * ∏ k, (if k = i then
        (if T k = v then (1 : ℝ) else 0) else if k = j then (if T k = v' then 1 else 0) else 1))
      = ∑ v, ∑ v', ∑ T : I → X, G v v' * (piLaw ν T * ∏ k, (if k = i then
        (if T k = v then (1 : ℝ) else 0) else if k = j then (if T k = v' then 1 else 0) else 1)) :=
          by
        rw [sum_comm]
        refine sum_congr rfl fun v _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun v' _ => sum_congr rfl fun T _ => by ring
    _ = ∑ v, ∑ v', ν i v * ν j v' * G v v' := by
        refine sum_congr rfl fun v _ => sum_congr rfl fun v' _ => ?_
        rw [← mul_sum, hprod]
        ring

end Table

/-! ### The random coding bound -/

section Bound

variable {A₁ A₂ C S X₁ X₂ Y : Type*} [Fintype A₁] [Fintype A₂] [Fintype C] [Fintype S]
  [Fintype X₁] [Fintype X₂] [Fintype Y]

open Classical in
/-- The term of the true sequences failing the test, for one pair of source sequences. -/
def jsccF₀ (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (V : X₁ × X₂ → Y → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ : A₂) : ℝ :=
  ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
    (if Test u₁ u₂ s a b y then 0 else 1)

open Classical in
/-- The term of a wrong first source sequence `u₁'`. -/
def jsccFa (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (V : X₁ × X₂ → Y → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ : A₂)
    (u₁' : A₁) : ℝ :=
  ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ a', A (u₁', s) a' * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
    (if Test u₁' u₂ s a' b y then 1 else 0)

open Classical in
/-- The term of a wrong second source sequence `u₂'`. -/
def jsccFb (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (V : X₁ × X₂ → Y → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ u₂' : A₂) : ℝ :=
  ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ b', B (u₂', s) b' * ∑ y, V (a, b) y *
    (if Test u₁ u₂' s a b' y then 1 else 0)

open Classical in
/-- The term of two wrong source sequences with the true common part. -/
def jsccFc (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (V : X₁ × X₂ → Y → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ : A₂)
    (u₁' : A₁) (u₂' : A₂) : ℝ :=
  ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ a', A (u₁', s) a' * ∑ b, B (u₂, s) b * ∑ b', B (u₂', s) b' *
    ∑ y, V (a, b) y * (if Test u₁' u₂' s a' b' y then 1 else 0)

open Classical in
/-- The term of two wrong source sequences with a wrong common part. -/
def jsccFd (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (V : X₁ × X₂ → Y → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ : A₂)
    (u₁' : A₁) (u₂' : A₂) : ℝ :=
  ∑ s, τ s * ∑ s', τ s' * ∑ a, A (u₁, s) a * ∑ a', A (u₁', s') a' * ∑ b, B (u₂, s) b *
    ∑ b', B (u₂', s') b' * ∑ y, V (a, b) y * (if Test u₁' u₂' s' a' b' y then 1 else 0)

/-- The sum of the five terms for one pair of source sequences. -/
def jsccBound (g₁ : A₁ → C) (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (V : X₁ × X₂ → Y → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ : A₂) : ℝ :=
  open Classical in
  jsccF₀ τ A B V Test u₁ u₂ + ∑ u₁', jsccFa τ A B V Test u₁ u₂ u₁' +
    ∑ u₂', jsccFb τ A B V Test u₁ u₂ u₂' +
    ∑ u₁', ∑ u₂', (if g₁ u₁' = g₁ u₁ then 1 else 0) * jsccFc τ A B V Test u₁ u₂ u₁' u₂' +
    ∑ u₁', ∑ u₂', jsccFd τ A B V Test u₁ u₂ u₁' u₂'

variable {Q : A₁ × A₂ → ℝ} {τ : S → ℝ} {A : A₁ × S → X₁ → ℝ} {B : A₂ × S → X₂ → ℝ}
  {V : X₁ × X₂ → Y → ℝ} {Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop} {g₁ : A₁ → C} {g₂ : A₂ → C}

/-- The tables of the sequences `w(c)` and of the codewords. -/
abbrev JSCCTable (A₁ A₂ C S X₁ X₂ : Type*) : Type _ :=
  (C → S) × (A₁ × S → X₁) × (A₂ × S → X₂)

/-- The law of the tables. -/
def jsccLaw (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (T : JSCCTable A₁ A₂ C S X₁ X₂) : ℝ :=
  piLaw (fun _ => τ) T.1 * (piLaw A T.2.1 * piLaw B T.2.2)

/-- The law of two entries of a table, in nested form. -/
lemma sum_piLaw_mul_eval₂' {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I] {ν : I → X → ℝ}
    (hν : ∀ i, IsPMF (ν i)) {i j : I} (hij : i ≠ j) (G : X → X → ℝ) :
    ∑ T : I → X, piLaw ν T * G (T i) (T j) = ∑ v, ν i v * ∑ v', ν j v' * G v v' := by
  rw [sum_piLaw_mul_eval₂ hν hij]
  refine sum_congr rfl fun v _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun v' _ => by ring

open Classical in
lemma sum_jsccLaw_mul (G : (C → S) → (A₁ × S → X₁) → (A₂ × S → X₂) → ℝ) :
    ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T * G T.1 T.2.1 T.2.2 =
      ∑ w : C → S, piLaw (fun _ => τ) w * ∑ x₁ : A₁ × S → X₁, piLaw A x₁ *
        ∑ x₂ : A₂ × S → X₂, piLaw B x₂ * G w x₁ x₂ := by
  simp only [Fintype.sum_prod_type, jsccLaw, mul_sum]
  refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

open Classical in
/-- The sequences of the true pair have the true law. -/
lemma eval_true (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (c : C) (u₁ : A₁)
    (u₂ : A₂) (F : S → X₁ → X₂ → ℝ) :
    ∑ w : C → S, piLaw (fun _ => τ) w * ∑ x₁ : A₁ × S → X₁, piLaw A x₁ *
      ∑ x₂ : A₂ × S → X₂, piLaw B x₂ * F (w c) (x₁ (u₁, w c)) (x₂ (u₂, w c)) =
    ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * F s a b := by
  rw [← sum_piLaw_mul_eval (ν := fun _ : C => τ) (fun _ => hτ) c
    (fun s => ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * F s a b)]
  refine sum_congr rfl fun w _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval hA (u₁, w c) fun a => ∑ b, B (u₂, w c) b * F (w c) a b]
  refine sum_congr rfl fun x₁ _ => ?_
  congr 1
  exact sum_piLaw_mul_eval hB (u₂, w c) fun b => F (w c) (x₁ (u₁, w c)) b

open Classical in
/-- A wrong first source sequence, with the same common part. -/
lemma eval_a (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (c : C) {u₁ u₁' : A₁}
    (h : u₁ ≠ u₁') (u₂ : A₂) (F : S → X₁ → X₁ → X₂ → ℝ) :
    ∑ w : C → S, piLaw (fun _ => τ) w * ∑ x₁ : A₁ × S → X₁, piLaw A x₁ *
      ∑ x₂ : A₂ × S → X₂, piLaw B x₂ * F (w c) (x₁ (u₁, w c)) (x₁ (u₁', w c)) (x₂ (u₂, w c)) =
    ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ a', A (u₁', s) a' * ∑ b, B (u₂, s) b * F s a a' b := by
  rw [← sum_piLaw_mul_eval (ν := fun _ : C => τ) (fun _ => hτ) c
    (fun s => ∑ a, A (u₁, s) a * ∑ a', A (u₁', s) a' * ∑ b, B (u₂, s) b * F s a a' b)]
  refine sum_congr rfl fun w _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval₂' hA (i := (u₁, w c)) (j := (u₁', w c))
    (fun e => h (congrArg Prod.fst e)) fun a a' => ∑ b, B (u₂, w c) b * F (w c) a a' b]
  refine sum_congr rfl fun x₁ _ => ?_
  congr 1
  exact sum_piLaw_mul_eval hB (u₂, w c) fun b => F (w c) (x₁ (u₁, w c)) (x₁ (u₁', w c)) b

open Classical in
/-- A wrong second source sequence, with the same common part. -/
lemma eval_b (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (c : C) (u₁ : A₁) {u₂ u₂' : A₂}
    (h : u₂ ≠ u₂') (F : S → X₁ → X₂ → X₂ → ℝ) :
    ∑ w : C → S, piLaw (fun _ => τ) w * ∑ x₁ : A₁ × S → X₁, piLaw A x₁ *
      ∑ x₂ : A₂ × S → X₂, piLaw B x₂ * F (w c) (x₁ (u₁, w c)) (x₂ (u₂, w c)) (x₂ (u₂', w c)) =
    ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ b', B (u₂', s) b' * F s a b b' := by
  rw [← sum_piLaw_mul_eval (ν := fun _ : C => τ) (fun _ => hτ) c
    (fun s => ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ b', B (u₂', s) b' * F s a b b')]
  refine sum_congr rfl fun w _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval hA (u₁, w c)
    fun a => ∑ b, B (u₂, w c) b * ∑ b', B (u₂', w c) b' * F (w c) a b b']
  refine sum_congr rfl fun x₁ _ => ?_
  congr 1
  exact sum_piLaw_mul_eval₂' hB (i := (u₂, w c)) (j := (u₂', w c))
    (fun e => h (congrArg Prod.fst e)) fun b b' => F (w c) (x₁ (u₁, w c)) b b'

open Classical in
/-- Two wrong source sequences, with the same common part. -/
lemma eval_c (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (c : C) {u₁ u₁' : A₁}
    {u₂ u₂' : A₂} (h₁ : u₁ ≠ u₁') (h₂ : u₂ ≠ u₂') (F : S → X₁ → X₁ → X₂ → X₂ → ℝ) :
    ∑ w : C → S, piLaw (fun _ => τ) w * ∑ x₁ : A₁ × S → X₁, piLaw A x₁ *
      ∑ x₂ : A₂ × S → X₂, piLaw B x₂ * F (w c) (x₁ (u₁, w c)) (x₁ (u₁', w c)) (x₂ (u₂, w c))
        (x₂ (u₂', w c)) =
    ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ a', A (u₁', s) a' * ∑ b, B (u₂, s) b *
      ∑ b', B (u₂', s) b' * F s a a' b b' := by
  rw [← sum_piLaw_mul_eval (ν := fun _ : C => τ) (fun _ => hτ) c
    (fun s => ∑ a, A (u₁, s) a * ∑ a', A (u₁', s) a' * ∑ b, B (u₂, s) b *
      ∑ b', B (u₂', s) b' * F s a a' b b')]
  refine sum_congr rfl fun w _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval₂' hA (i := (u₁, w c)) (j := (u₁', w c))
    (fun e => h₁ (congrArg Prod.fst e))
    fun a a' => ∑ b, B (u₂, w c) b * ∑ b', B (u₂', w c) b' * F (w c) a a' b b']
  refine sum_congr rfl fun x₁ _ => ?_
  congr 1
  exact sum_piLaw_mul_eval₂' hB (i := (u₂, w c)) (j := (u₂', w c))
    (fun e => h₂ (congrArg Prod.fst e)) fun b b' => F (w c) (x₁ (u₁, w c)) (x₁ (u₁', w c)) b b'

open Classical in
/-- Two wrong source sequences, with a different common part. -/
lemma eval_d (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) {c c' : C} (hc : c ≠ c')
    {u₁ u₁' : A₁} {u₂ u₂' : A₂} (h₁ : u₁ ≠ u₁') (h₂ : u₂ ≠ u₂')
    (F : S → S → X₁ → X₁ → X₂ → X₂ → ℝ) :
    ∑ w : C → S, piLaw (fun _ => τ) w * ∑ x₁ : A₁ × S → X₁, piLaw A x₁ *
      ∑ x₂ : A₂ × S → X₂, piLaw B x₂ * F (w c) (w c') (x₁ (u₁, w c)) (x₁ (u₁', w c'))
        (x₂ (u₂, w c)) (x₂ (u₂', w c')) =
    ∑ s, τ s * ∑ s', τ s' * ∑ a, A (u₁, s) a * ∑ a', A (u₁', s') a' * ∑ b, B (u₂, s) b *
      ∑ b', B (u₂', s') b' * F s s' a a' b b' := by
  rw [← sum_piLaw_mul_eval₂' (ν := fun _ : C => τ) (fun _ => hτ) hc
    (fun s s' => ∑ a, A (u₁, s) a * ∑ a', A (u₁', s') a' * ∑ b, B (u₂, s) b *
      ∑ b', B (u₂', s') b' * F s s' a a' b b')]
  refine sum_congr rfl fun w _ => ?_
  congr 1
  rw [← sum_piLaw_mul_eval₂' hA (i := (u₁, w c)) (j := (u₁', w c'))
    (fun e => h₁ (congrArg Prod.fst e))
    fun a a' => ∑ b, B (u₂, w c) b * ∑ b', B (u₂', w c') b' * F (w c) (w c') a a' b b']
  refine sum_congr rfl fun x₁ _ => ?_
  congr 1
  exact sum_piLaw_mul_eval₂' hB (i := (u₂, w c)) (j := (u₂', w c'))
    (fun e => h₂ (congrArg Prod.fst e))
    fun b b' => F (w c) (w c') (x₁ (u₁, w c)) (x₁ (u₁', w c')) b b'

/-- The decoding test for a pair of source sequences, for given tables. -/
def jsccD (g₁ : A₁ → C) (g₂ : A₂ → C) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop)
    (T : JSCCTable A₁ A₂ C S X₁ X₂) (u₁ : A₁) (u₂ : A₂) (y : Y) : Prop :=
  g₁ u₁ = g₂ u₂ ∧ Test u₁ u₂ (T.1 (g₁ u₁)) (T.2.1 (u₁, T.1 (g₁ u₁))) (T.2.2 (u₂, T.1 (g₂ u₂))) y

open Classical in
/-- The decoder for given tables. -/
def jsccDec [Nonempty A₁] [Nonempty A₂] (g₁ : A₁ → C) (g₂ : A₂ → C)
    (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (T : JSCCTable A₁ A₂ C S X₁ X₂) (y : Y) : A₁ × A₂ :=
  if h : ∃ p : A₁ × A₂, jsccD g₁ g₂ Test T p.1 p.2 y then h.choose else Classical.arbitrary _

omit [Fintype C] [Fintype S] [Fintype X₁] [Fintype X₂] [Fintype Y] in
open Classical in
/-- The error of the decoder is at most that of the union of the events. -/
lemma ite_jsccDec_le [Nonempty A₁] [Nonempty A₂] (T : JSCCTable A₁ A₂ C S X₁ X₂) (u₁ : A₁)
    (u₂ : A₂) (y : Y) :
    (if jsccDec g₁ g₂ Test T y = (u₁, u₂) then (0 : ℝ) else 1) ≤
      (if jsccD g₁ g₂ Test T u₁ u₂ y then 0 else 1) +
        ∑ p : A₁ × A₂, if p ≠ (u₁, u₂) ∧ jsccD g₁ g₂ Test T p.1 p.2 y then 1 else 0 := by
  have h0 : ∀ p : A₁ × A₂, (0 : ℝ) ≤
      if p ≠ (u₁, u₂) ∧ jsccD g₁ g₂ Test T p.1 p.2 y then 1 else 0 := fun p => by
    split_ifs <;> norm_num
  by_cases hD : jsccD g₁ g₂ Test T u₁ u₂ y
  · have hex : ∃ p : A₁ × A₂, jsccD g₁ g₂ Test T p.1 p.2 y := ⟨(u₁, u₂), hD⟩
    have hspec := hex.choose_spec
    have hdec : jsccDec g₁ g₂ Test T y = hex.choose := by
      simp only [jsccDec, hex, ↓reduceDIte]
    by_cases he : hex.choose = (u₁, u₂)
    · rw [hdec, he]
      simp only [ite_true, hD, zero_add]
      exact sum_nonneg fun p _ => h0 p
    · rw [hdec, ite_eq_right he]
      have := single_le_sum (fun p _ => h0 p) (mem_univ hex.choose)
      simp only [ne_eq, he, not_false_eq_true, hspec, and_self, ite_true] at this
      simp only [hD, ite_true, zero_add]
      exact this
  · have := sum_nonneg fun p (_ : p ∈ univ) => h0 p
    simp only [hD, ite_false]
    split_ifs <;> linarith

variable [Nonempty A₁] [Nonempty A₂]

section Nonneg

variable (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V)

include hV in
omit [Fintype A₁] [Fintype A₂] [Fintype C] [Fintype S] [Fintype X₁] [Fintype X₂]
  [Nonempty A₁] [Nonempty A₂] in
open Classical in
private lemma inner_nonneg (a : X₁) (b : X₂) (t : Y → Prop) :
    0 ≤ ∑ y, V (a, b) y * (if t y then (1 : ℝ) else 0) :=
  sum_nonneg fun y _ => mul_nonneg ((hV (a, b)).nonneg y) (by split_ifs <;> norm_num)

include hτ hA hB hV

omit [Fintype A₁] [Fintype A₂] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
lemma jsccFa_nonneg (u₁ : A₁) (u₂ : A₂) (u₁' : A₁) : 0 ≤ jsccFa τ A B V Test u₁ u₂ u₁' :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) (sum_nonneg fun a _ =>
    mul_nonneg ((hA _).nonneg a) (sum_nonneg fun a' _ => mul_nonneg ((hA _).nonneg a')
      (sum_nonneg fun b _ => mul_nonneg ((hB _).nonneg b) (inner_nonneg hV a b _))))

omit [Fintype A₁] [Fintype A₂] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
lemma jsccFb_nonneg (u₁ : A₁) (u₂ u₂' : A₂) : 0 ≤ jsccFb τ A B V Test u₁ u₂ u₂' :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) (sum_nonneg fun a _ =>
    mul_nonneg ((hA _).nonneg a) (sum_nonneg fun b _ => mul_nonneg ((hB _).nonneg b)
      (sum_nonneg fun b' _ => mul_nonneg ((hB _).nonneg b') (inner_nonneg hV a b _))))

omit [Fintype A₁] [Fintype A₂] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
lemma jsccFc_nonneg (u₁ : A₁) (u₂ : A₂) (u₁' : A₁) (u₂' : A₂) :
    0 ≤ jsccFc τ A B V Test u₁ u₂ u₁' u₂' :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) (sum_nonneg fun a _ =>
    mul_nonneg ((hA _).nonneg a) (sum_nonneg fun a' _ => mul_nonneg ((hA _).nonneg a')
      (sum_nonneg fun b _ => mul_nonneg ((hB _).nonneg b) (sum_nonneg fun b' _ =>
        mul_nonneg ((hB _).nonneg b') (inner_nonneg hV a b _)))))

omit [Fintype A₁] [Fintype A₂] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
lemma jsccFd_nonneg (u₁ : A₁) (u₂ : A₂) (u₁' : A₁) (u₂' : A₂) :
    0 ≤ jsccFd τ A B V Test u₁ u₂ u₁' u₂' :=
  sum_nonneg fun s _ => mul_nonneg (hτ.nonneg s) (sum_nonneg fun s' _ =>
    mul_nonneg (hτ.nonneg s') (sum_nonneg fun a _ => mul_nonneg ((hA _).nonneg a)
      (sum_nonneg fun a' _ => mul_nonneg ((hA _).nonneg a') (sum_nonneg fun b _ =>
        mul_nonneg ((hB _).nonneg b) (sum_nonneg fun b' _ =>
          mul_nonneg ((hB _).nonneg b') (inner_nonneg hV a b _))))))

end Nonneg

open Classical in
/-- The four terms that bound the expected error of a wrong pair `p`. -/
def jsccPairBound (g₁ : A₁ → C) (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (V : X₁ × X₂ → Y → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ : A₂)
    (p : A₁ × A₂) : ℝ :=
  (if p.2 = u₂ then jsccFa τ A B V Test u₁ u₂ p.1 else 0) +
    (if p.1 = u₁ then jsccFb τ A B V Test u₁ u₂ p.2 else 0) +
    (if g₁ p.1 = g₁ u₁ then 1 else 0) * jsccFc τ A B V Test u₁ u₂ p.1 p.2 +
    jsccFd τ A B V Test u₁ u₂ p.1 p.2

omit [Fintype A₁] [Fintype A₂] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
lemma jsccPairBound_nonneg (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V)
    (u₁ : A₁) (u₂ : A₂) (p : A₁ × A₂) : 0 ≤ jsccPairBound g₁ τ A B V Test u₁ u₂ p := by
  have h1 := jsccFa_nonneg (Test := Test) hτ hA hB hV u₁ u₂ p.1
  have h2 := jsccFb_nonneg (Test := Test) hτ hA hB hV u₁ u₂ p.2
  have h3 := jsccFc_nonneg (Test := Test) hτ hA hB hV u₁ u₂ p.1 p.2
  have h4 := jsccFd_nonneg (Test := Test) hτ hA hB hV u₁ u₂ p.1 p.2
  rw [jsccPairBound]
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) (mul_nonneg ?_ h3)) h4
  · split_ifs
    · exact h1
    · exact le_rfl
  · split_ifs
    · exact h2
    · exact le_rfl
  · split_ifs <;> norm_num

omit [Nonempty A₁] [Nonempty A₂] in
open Classical in
/-- The expected error term of a wrong pair `(u₁', u₂')`. -/
lemma sum_jsccLaw_pair_le (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V)
    {u₁ u₁' : A₁} {u₂ u₂' : A₂} (hc : g₁ u₁ = g₂ u₂) (hne : (u₁', u₂') ≠ (u₁, u₂)) :
    ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
      ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccD g₁ g₂ Test T u₁' u₂' y then 1 else 0) ≤
      jsccPairBound g₁ τ A B V Test u₁ u₂ (u₁', u₂') := by
  have hTa := jsccFa_nonneg (Test := Test) hτ hA hB hV u₁ u₂ u₁'
  have hTb := jsccFb_nonneg (Test := Test) hτ hA hB hV u₁ u₂ u₂'
  have hTc := jsccFc_nonneg (Test := Test) hτ hA hB hV u₁ u₂ u₁' u₂'
  have hTd := jsccFd_nonneg (Test := Test) hτ hA hB hV u₁ u₂ u₁' u₂'
  by_cases hg : g₁ u₁' = g₂ u₂'
  swap
  · -- The test fails for a pair with different common parts.
    have hzero : ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
        ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
          (if jsccD g₁ g₂ Test T u₁' u₂' y then 1 else 0) = 0 := by
      refine sum_eq_zero fun T _ => ?_
      have : ∀ y, ¬ jsccD g₁ g₂ Test T u₁' u₂' y := fun y h => hg h.1
      simp [this]
    rw [hzero]
    exact jsccPairBound_nonneg hτ hA hB hV u₁ u₂ _
  -- The law of the tables.
  have hE' : ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
      ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccD g₁ g₂ Test T u₁' u₂' y then 1 else 0) =
      ∑ w : C → S, piLaw (fun _ => τ) w * ∑ x₁ : A₁ × S → X₁, piLaw A x₁ *
      ∑ x₂ : A₂ × S → X₂, piLaw B x₂ * ∑ y, V (x₁ (u₁, w (g₁ u₁)), x₂ (u₂, w (g₁ u₁))) y *
        (if Test u₁' u₂' (w (g₁ u₁')) (x₁ (u₁', w (g₁ u₁'))) (x₂ (u₂', w (g₁ u₁'))) y
          then 1 else 0) := by
    refine Eq.trans (sum_congr rfl fun T _ => ?_) (sum_jsccLaw_mul (τ := τ) (A := A) (B := B)
      (fun w x₁ x₂ => ∑ y, V (x₁ (u₁, w (g₁ u₁)), x₂ (u₂, w (g₁ u₁))) y *
        (if Test u₁' u₂' (w (g₁ u₁')) (x₁ (u₁', w (g₁ u₁'))) (x₂ (u₂', w (g₁ u₁'))) y
          then 1 else 0)))
    congr 1
    refine sum_congr rfl fun y _ => ?_
    rw [← hc]
    congr 1
    exact if_congr (by rw [jsccD, ← hg]; simp) rfl rfl
  rw [hE', jsccPairBound]
  simp only
  by_cases h₂ : u₂' = u₂
  · -- Only the first source sequence is wrong.
    subst h₂
    have h₁ : u₁ ≠ u₁' := fun e => hne (by rw [e])
    have hgc : g₁ u₁' = g₁ u₁ := by rw [hg, hc]
    rw [hgc]
    have hv := eval_a hτ hA hB (g₁ u₁) h₁ u₂' (fun s a a' b => ∑ y, V (a, b) y *
      (if Test u₁' u₂' s a' b y then 1 else 0))
    rw [hv, ite_eq_left rfl, ite_eq_right h₁.symm, add_zero]
    have h3 := mul_nonneg (show (0 : ℝ) ≤ if g₁ u₁ = g₁ u₁ then 1 else 0 by split_ifs <;> norm_num)
      hTc
    have e : jsccFa τ A B V Test u₁ u₂' u₁' = ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ a', A (u₁', s) a' *
        ∑ b, B (u₂', s) b * ∑ y, V (a, b) y * (if Test u₁' u₂' s a' b y then 1 else 0) := rfl
    rw [← e]
    linarith
  by_cases h₁ : u₁' = u₁
  · -- Only the second source sequence is wrong.
    subst h₁
    have h₂' : u₂ ≠ u₂' := fun e => h₂ e.symm
    have hv := eval_b hτ hA hB (g₁ u₁') u₁' h₂' (fun s a b b' => ∑ y, V (a, b) y *
      (if Test u₁' u₂' s a b' y then 1 else 0))
    rw [hv, ite_eq_right h₂, zero_add, ite_eq_left rfl]
    have h3 := mul_nonneg (show (0 : ℝ) ≤ if g₁ u₁' = g₁ u₁' then 1 else 0 by split_ifs <;>
      norm_num)
      hTc
    have e : jsccFb τ A B V Test u₁' u₂ u₂' = ∑ s, τ s * ∑ a, A (u₁', s) a * ∑ b, B (u₂, s) b *
        ∑ b', B (u₂', s) b' * ∑ y, V (a, b) y * (if Test u₁' u₂' s a b' y then 1 else 0) := rfl
    rw [← e]
    linarith
  -- Both source sequences are wrong.
  have h₁' : u₁ ≠ u₁' := fun e => h₁ e.symm
  have h₂' : u₂ ≠ u₂' := fun e => h₂ e.symm
  rw [ite_eq_right h₂, ite_eq_right h₁, zero_add, zero_add]
  by_cases hcc : g₁ u₁' = g₁ u₁
  · rw [hcc]
    have hv := eval_c hτ hA hB (g₁ u₁) h₁' h₂' (fun s a a' b b' => ∑ y, V (a, b) y *
      (if Test u₁' u₂' s a' b' y then 1 else 0))
    rw [hv, ite_eq_left rfl, one_mul]
    have e : jsccFc τ A B V Test u₁ u₂ u₁' u₂' = ∑ s, τ s * ∑ a, A (u₁, s) a *
        ∑ a', A (u₁', s) a' * ∑ b, B (u₂, s) b * ∑ b', B (u₂', s) b' * ∑ y, V (a, b) y *
          (if Test u₁' u₂' s a' b' y then 1 else 0) := rfl
    rw [← e]
    linarith
  · have hcc' : g₁ u₁ ≠ g₁ u₁' := fun e => hcc e.symm
    have hv := eval_d hτ hA hB hcc' h₁' h₂' (fun s s' a a' b b' => ∑ y, V (a, b) y *
      (if Test u₁' u₂' s' a' b' y then 1 else 0))
    rw [hv, ite_eq_right hcc, zero_mul, zero_add]
    exact le_rfl

omit [Fintype C] [Nonempty A₁] [Nonempty A₂] in
open Classical in
/-- The sum over the wrong pairs of the four terms is the sum in `jsccBound`. -/
lemma sum_jsccPairBound (u₁ : A₁) (u₂ : A₂) :
    ∑ p, jsccPairBound g₁ τ A B V Test u₁ u₂ p =
      ∑ u₁', jsccFa τ A B V Test u₁ u₂ u₁' + ∑ u₂', jsccFb τ A B V Test u₁ u₂ u₂' +
      ∑ u₁', ∑ u₂', (if g₁ u₁' = g₁ u₁ then 1 else 0) * jsccFc τ A B V Test u₁ u₂ u₁' u₂' +
      ∑ u₁', ∑ u₂', jsccFd τ A B V Test u₁ u₂ u₁' u₂' := by
  simp only [jsccPairBound]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
  congr 1
  · congr 1
    · congr 1
      · rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun u₁' _ => ?_
        rw [sum_ite_eq' univ u₂]
        simp
      · rw [Fintype.sum_prod_type_right]
        refine sum_congr rfl fun u₂' _ => ?_
        rw [sum_ite_eq' univ u₁]
        simp
    · rw [Fintype.sum_prod_type]
  · rw [Fintype.sum_prod_type]

open Classical in
/-- The expected error for one pair of source sequences. -/
lemma sum_jsccLaw_err_le (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hV : IsChannel V)
    {u₁ : A₁} {u₂ : A₂} (hc : g₁ u₁ = g₂ u₂) :
    ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
      ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccDec g₁ g₂ Test T y = (u₁, u₂) then 0 else 1) ≤
      jsccBound g₁ τ A B V Test u₁ u₂ := by
  have hL0 : ∀ T : JSCCTable A₁ A₂ C S X₁ X₂, 0 ≤ jsccLaw τ A B T := fun T =>
    mul_nonneg (piLaw_nonneg (fun _ => hτ) _)
      (mul_nonneg (piLaw_nonneg hA _) (piLaw_nonneg hB _))
  -- The union bound.
  have hunion : ∀ T : JSCCTable A₁ A₂ C S X₁ X₂,
      ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccDec g₁ g₂ Test T y = (u₁, u₂) then 0 else 1) ≤
      ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccD g₁ g₂ Test T u₁ u₂ y then 0 else 1) +
      ∑ p : A₁ × A₂, (if p ≠ (u₁, u₂) then
        ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
          (if jsccD g₁ g₂ Test T p.1 p.2 y then 1 else 0) else 0) := fun T => by
    have h1 := sum_le_sum fun y (_ : y ∈ univ) => mul_le_mul_of_nonneg_left
      (ite_jsccDec_le (g₁ := g₁) (g₂ := g₂) (Test := Test) T u₁ u₂ y)
      ((hV (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂)))).nonneg y)
    refine h1.trans (le_of_eq ?_)
    simp only [mul_add, mul_sum]
    rw [sum_add_distrib]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    by_cases hp : p = (u₁, u₂)
    · simp [hp]
    · simp only [ne_eq, hp, not_false_eq_true, true_and, ite_true]
  -- The true pair.
  have h₀ : ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
      ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccD g₁ g₂ Test T u₁ u₂ y then 0 else 1) = jsccF₀ τ A B V Test u₁ u₂ := by
    have hv := eval_true hτ hA hB (g₁ u₁) u₁ u₂ (fun s a b => ∑ y, V (a, b) y *
      (if Test u₁ u₂ s a b y then 0 else 1))
    refine Eq.trans ?_ hv
    refine Eq.trans (sum_congr rfl fun T _ => ?_) (sum_jsccLaw_mul (τ := τ) (A := A) (B := B)
      (fun w x₁ x₂ => ∑ y, V (x₁ (u₁, w (g₁ u₁)), x₂ (u₂, w (g₁ u₁))) y *
        (if Test u₁ u₂ (w (g₁ u₁)) (x₁ (u₁, w (g₁ u₁))) (x₂ (u₂, w (g₁ u₁))) y then 0 else 1)))
    congr 1
    refine sum_congr rfl fun y _ => ?_
    rw [← hc]
    congr 1
    exact if_congr (by simp [jsccD, hc]) rfl rfl
  -- The wrong pairs.
  have hp : ∀ p : A₁ × A₂, ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
      (if p ≠ (u₁, u₂) then
        ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
          (if jsccD g₁ g₂ Test T p.1 p.2 y then 1 else 0) else 0) ≤
      jsccPairBound g₁ τ A B V Test u₁ u₂ p := fun p => by
    by_cases he : p = (u₁, u₂)
    · simp only [he, ne_eq, not_true_eq_false, ite_false, mul_zero, sum_const_zero]
      exact jsccPairBound_nonneg hτ hA hB hV u₁ u₂ _
    · simp only [ne_eq, he, not_false_eq_true, ite_true]
      exact sum_jsccLaw_pair_le hτ hA hB hV hc he
  calc _ ≤ ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
        (∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
          (if jsccD g₁ g₂ Test T u₁ u₂ y then 0 else 1) +
        ∑ p : A₁ × A₂, (if p ≠ (u₁, u₂) then
          ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
            (if jsccD g₁ g₂ Test T p.1 p.2 y then 1 else 0) else 0)) :=
        sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hunion T) (hL0 T)
    _ = jsccF₀ τ A B V Test u₁ u₂ + ∑ p : A₁ × A₂, ∑ T : JSCCTable A₁ A₂ C S X₁ X₂,
        jsccLaw τ A B T * (if p ≠ (u₁, u₂) then
          ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
            (if jsccD g₁ g₂ Test T p.1 p.2 y then 1 else 0) else 0) := by
        simp only [mul_add]
        rw [sum_add_distrib, h₀]
        congr 1
        simp only [mul_sum]
        rw [sum_comm]
    _ ≤ jsccF₀ τ A B V Test u₁ u₂ + ∑ p, jsccPairBound g₁ τ A B V Test u₁ u₂ p :=
        add_le_add le_rfl (sum_le_sum fun p _ => hp p)
    _ = jsccBound g₁ τ A B V Test u₁ u₂ := by
        rw [sum_jsccPairBound, jsccBound]
        ring

omit [Fintype C] in
open Classical in
/-- **The random coding bound.** There are encoders and a decoder such that the error probability
is at most the average of the five terms. -/
theorem exists_jscc_code_le [Finite C] (hQ : IsPMF Q) (hτ : IsPMF τ) (hA : IsChannel A)
    (hB : IsChannel B) (hV : IsChannel V) (hg : ∀ u₁ u₂, Q (u₁, u₂) ≠ 0 → g₁ u₁ = g₂ u₂) : ∃
    (e₁ : A₁ → X₁) (e₂ : A₂ → X₂) (dec : Y → A₁ × A₂), ∑ u₁, ∑ u₂, Q (u₁, u₂) * ∑ y, V
    (e₁ u₁, e₂ u₂) y * (if dec y = (u₁, u₂) then 0 else 1) ≤ ∑ u₁, ∑ u₂, Q (u₁, u₂) * jsccBound g₁
    τ A B V Test u₁ u₂ := by
  have := Fintype.ofFinite C
  have hL : IsPMF (jsccLaw (C := C) τ A B) := by
    refine ⟨fun T => mul_nonneg (piLaw_nonneg (fun _ => hτ) _)
      (mul_nonneg (piLaw_nonneg hA _) (piLaw_nonneg hB _)), ?_⟩
    have h1 := (piLaw_isPMF (I := C) fun _ => hτ).sum_eq_one
    have h2 := (piLaw_isPMF hA).sum_eq_one
    have h3 := (piLaw_isPMF hB).sum_eq_one
    simp only [Fintype.sum_prod_type, jsccLaw, ← mul_sum, h3, mul_one, h2, h1]
  suffices h : ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
      (∑ u₁, ∑ u₂, Q (u₁, u₂) * ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccDec g₁ g₂ Test T y = (u₁, u₂) then 0 else 1)) ≤
      ∑ u₁, ∑ u₂, Q (u₁, u₂) * jsccBound g₁ τ A B V Test u₁ u₂ by
    obtain ⟨T, hT⟩ := exists_le_of_sum_mul_le hL h
    exact ⟨fun u₁ => T.2.1 (u₁, T.1 (g₁ u₁)), fun u₂ => T.2.2 (u₂, T.1 (g₂ u₂)),
      jsccDec g₁ g₂ Test T, hT⟩
  have hswap : ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
      (∑ u₁, ∑ u₂, Q (u₁, u₂) * ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
        (if jsccDec g₁ g₂ Test T y = (u₁, u₂) then 0 else 1)) =
      ∑ u₁, ∑ u₂, Q (u₁, u₂) * ∑ T : JSCCTable A₁ A₂ C S X₁ X₂, jsccLaw τ A B T *
        ∑ y, V (T.2.1 (u₁, T.1 (g₁ u₁)), T.2.2 (u₂, T.1 (g₂ u₂))) y *
          (if jsccDec g₁ g₂ Test T y = (u₁, u₂) then 0 else 1) := by
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u₁ _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun u₂ _ => sum_congr rfl fun T _ => sum_congr rfl fun y _ => by ring
  rw [hswap]
  refine sum_le_sum fun u₁ _ => sum_le_sum fun u₂ _ => ?_
  by_cases hQ0 : Q (u₁, u₂) = 0
  · simp [hQ0]
  exact mul_le_mul_of_nonneg_left (sum_jsccLaw_err_le hτ hA hB hV (hg u₁ u₂ hQ0)) (hQ.nonneg _)

/-! ### The bound in a form for evaluation -/

section Form

variable {J I : Type*} [Fintype J] [Fintype I]

omit [Fintype A₁] [Fintype A₂] [Fintype C] [Fintype S] [Fintype X₁] [Fintype X₂] [Fintype Y]
  [Nonempty A₁] [Nonempty A₂] in
/-- Exchange a weighted sum with another sum. -/
lemma sum_mul_sum_swap' (c : J → ℝ) (w : I → ℝ) (F : J → I → ℝ) :
    ∑ j, c j * ∑ i, w i * F j i = ∑ i, w i * ∑ j, c j * F j i := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

omit [Fintype A₁] [Fintype A₂] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
/-- Exchange a weighted sum with the sums over the channel variables. -/
lemma sum_mul_four_swap (c : J → ℝ) (F : J → S → X₁ → X₂ → Y → ℝ) (u₁ : A₁) (u₂ : A₂) :
    ∑ j, c j * ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y * F j s a b y =
      ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y * ∑ j, c j *
        F j s a b y := by
  refine (sum_mul_sum_swap' _ _ _).trans (sum_congr rfl fun s _ => congrArg _ ?_)
  refine (sum_mul_sum_swap' _ _ _).trans (sum_congr rfl fun a _ => congrArg _ ?_)
  refine (sum_mul_sum_swap' _ _ _).trans (sum_congr rfl fun b _ => congrArg _ ?_)
  exact sum_mul_sum_swap' _ _ _

/-- The test term of the true sequences. -/
def jsccΦ₀ (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (u₂ : A₂) (s : S) (a : X₁) (b : X₂)
    (y : Y) : ℝ :=
  open Classical in if Test u₁ u₂ s a b y then 0 else 1

/-- The test term of a wrong first source sequence. -/
def jsccΦa (A : A₁ × S → X₁ → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₂ : A₂) (s : S)
    (b : X₂) (y : Y) : ℝ :=
  open Classical in
  ∑ u₁', ∑ a', A (u₁', s) a' * (if Test u₁' u₂ s a' b y then 1 else 0)

/-- The test term of a wrong second source sequence. -/
def jsccΦb (B : A₂ × S → X₂ → ℝ) (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (u₁ : A₁) (s : S)
    (a : X₁) (y : Y) : ℝ :=
  open Classical in
  ∑ u₂', ∑ b', B (u₂', s) b' * (if Test u₁ u₂' s a b' y then 1 else 0)

/-- The test term of two wrong source sequences with the true common part `c`. -/
def jsccΦc (g₁ : A₁ → C) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (c : C) (s : S) (y : Y) : ℝ :=
  open Classical in
  ∑ u₁', ∑ u₂', (if g₁ u₁' = c then 1 else 0) * ∑ a', A (u₁', s) a' * ∑ b', B (u₂', s) b' *
    (if Test u₁' u₂' s a' b' y then 1 else 0)

/-- The test term of two wrong source sequences with a wrong common part. -/
def jsccΦd (τ : S → ℝ) (A : A₁ × S → X₁ → ℝ) (B : A₂ × S → X₂ → ℝ)
    (Test : A₁ → A₂ → S → X₁ → X₂ → Y → Prop) (y : Y) : ℝ :=
  open Classical in
  ∑ u₁', ∑ u₂', ∑ s', τ s' * ∑ a', A (u₁', s') a' * ∑ b', B (u₂', s') b' *
    (if Test u₁' u₂' s' a' b' y then 1 else 0)

omit [Fintype A₂] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
open Classical in
lemma sum_jsccFa_eq (u₁ : A₁) (u₂ : A₂) :
    ∑ u₁', jsccFa τ A B V Test u₁ u₂ u₁' = ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b *
      ∑ y, V (a, b) y * jsccΦa A Test u₂ s b y := by
  have h : ∀ u₁', jsccFa τ A B V Test u₁ u₂ u₁' = ∑ s, τ s * ∑ a, A (u₁, s) a *
      ∑ b, B (u₂, s) b * ∑ y, V (a, b) y * ∑ a', A (u₁', s) a' *
        (if Test u₁' u₂ s a' b y then 1 else 0) := fun u₁' => by
    refine sum_congr rfl fun s _ => congrArg _ (sum_congr rfl fun a _ => congrArg _ ?_)
    refine (sum_mul_sum_swap' _ _ _).trans (sum_congr rfl fun b _ => congrArg _ ?_)
    exact sum_mul_sum_swap' _ _ _
  simp only [h]
  have := sum_mul_four_swap (τ := τ) (A := A) (B := B) (V := V) (fun _ : A₁ => (1 : ℝ))
    (fun u₁' s _ b y => ∑ a', A (u₁', s) a' * (if Test u₁' u₂ s a' b y then 1 else 0)) u₁ u₂
  simpa only [one_mul, jsccΦa] using this

omit [Fintype A₁] [Fintype C] [Nonempty A₁] [Nonempty A₂] in
open Classical in
lemma sum_jsccFb_eq (u₁ : A₁) (u₂ : A₂) :
    ∑ u₂', jsccFb τ A B V Test u₁ u₂ u₂' = ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b *
      ∑ y, V (a, b) y * jsccΦb B Test u₁ s a y := by
  have h : ∀ u₂', jsccFb τ A B V Test u₁ u₂ u₂' = ∑ s, τ s * ∑ a, A (u₁, s) a *
      ∑ b, B (u₂, s) b * ∑ y, V (a, b) y * ∑ b', B (u₂', s) b' *
        (if Test u₁ u₂' s a b' y then 1 else 0) := fun u₂' => by
    refine sum_congr rfl fun s _ => congrArg _ (sum_congr rfl fun a _ => congrArg _
      (sum_congr rfl fun b _ => congrArg _ ?_))
    exact sum_mul_sum_swap' _ _ _
  simp only [h]
  have := sum_mul_four_swap (τ := τ) (A := A) (B := B) (V := V) (fun _ : A₂ => (1 : ℝ))
    (fun u₂' s a _ y => ∑ b', B (u₂', s) b' * (if Test u₁ u₂' s a b' y then 1 else 0)) u₁ u₂
  simpa only [one_mul, jsccΦb] using this

omit [Fintype C] [Nonempty A₁] [Nonempty A₂] in
open Classical in
lemma sum_jsccFc_eq (u₁ : A₁) (u₂ : A₂) :
    ∑ u₁', ∑ u₂', (if g₁ u₁' = g₁ u₁ then 1 else 0) * jsccFc τ A B V Test u₁ u₂ u₁' u₂' =
      ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
        jsccΦc g₁ A B Test (g₁ u₁) s y := by
  have h : ∀ u₁' u₂', jsccFc τ A B V Test u₁ u₂ u₁' u₂' = ∑ s, τ s * ∑ a, A (u₁, s) a *
      ∑ b, B (u₂, s) b * ∑ y, V (a, b) y * ∑ a', A (u₁', s) a' * ∑ b', B (u₂', s) b' *
        (if Test u₁' u₂' s a' b' y then 1 else 0) := fun u₁' u₂' => by
    refine sum_congr rfl fun s _ => congrArg _ (sum_congr rfl fun a _ => congrArg _ ?_)
    refine (sum_mul_sum_swap' _ _ _).trans (sum_congr rfl fun b _ => congrArg _ ?_)
    refine (sum_congr rfl fun a' _ => congrArg _ (sum_mul_sum_swap' _ _ _)).trans ?_
    exact sum_mul_sum_swap' _ _ _
  simp only [h]
  have hin : ∀ u₁', ∑ u₂', (if g₁ u₁' = g₁ u₁ then (1 : ℝ) else 0) *
      ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
        ∑ a', A (u₁', s) a' * ∑ b', B (u₂', s) b' * (if Test u₁' u₂' s a' b' y then 1 else 0) =
      ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
        ∑ u₂', (if g₁ u₁' = g₁ u₁ then (1 : ℝ) else 0) * ∑ a', A (u₁', s) a' *
          ∑ b', B (u₂', s) b' * (if Test u₁' u₂' s a' b' y then 1 else 0) := fun u₁' =>
    sum_mul_four_swap (τ := τ) (A := A) (B := B) (V := V) (fun _ => _)
      (fun u₂' s _ _ y => ∑ a', A (u₁', s) a' * ∑ b', B (u₂', s) b' *
        (if Test u₁' u₂' s a' b' y then 1 else 0)) u₁ u₂
  simp only [hin]
  have := sum_mul_four_swap (τ := τ) (A := A) (B := B) (V := V) (fun _ : A₁ => (1 : ℝ))
    (fun u₁' s _ _ y => ∑ u₂', (if g₁ u₁' = g₁ u₁ then (1 : ℝ) else 0) * ∑ a', A (u₁', s) a' *
      ∑ b', B (u₂', s) b' * (if Test u₁' u₂' s a' b' y then 1 else 0)) u₁ u₂
  simpa only [one_mul, jsccΦc] using this

omit [Fintype C] [Nonempty A₁] [Nonempty A₂] in
open Classical in
lemma sum_jsccFd_eq (u₁ : A₁) (u₂ : A₂) :
    ∑ u₁', ∑ u₂', jsccFd τ A B V Test u₁ u₂ u₁' u₂' =
      ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
        jsccΦd τ A B Test y := by
  have h : ∀ u₁' u₂', jsccFd τ A B V Test u₁ u₂ u₁' u₂' = ∑ s, τ s * ∑ a, A (u₁, s) a *
      ∑ b, B (u₂, s) b * ∑ y, V (a, b) y * ∑ s', τ s' * ∑ a', A (u₁', s') a' *
        ∑ b', B (u₂', s') b' * (if Test u₁' u₂' s' a' b' y then 1 else 0) := fun u₁' u₂' => by
    refine sum_congr rfl fun s _ => congrArg _ ?_
    refine (sum_mul_sum_swap' _ _ _).trans (sum_congr rfl fun a _ => congrArg _ ?_)
    refine (sum_congr rfl fun s' _ => congrArg _ (sum_mul_sum_swap' _ _ _)).trans ?_
    refine (sum_mul_sum_swap' _ _ _).trans (sum_congr rfl fun b _ => congrArg _ ?_)
    refine (sum_congr rfl fun s' _ => congrArg _ (sum_congr rfl fun a' _ =>
      congrArg _ (sum_mul_sum_swap' _ _ _))).trans ?_
    refine (sum_congr rfl fun s' _ => congrArg _ (sum_mul_sum_swap' _ _ _)).trans ?_
    exact sum_mul_sum_swap' _ _ _
  simp only [h]
  have hin : ∀ u₁', ∑ u₂', ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
      ∑ s', τ s' * ∑ a', A (u₁', s') a' * ∑ b', B (u₂', s') b' *
        (if Test u₁' u₂' s' a' b' y then 1 else 0) =
      ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b * ∑ y, V (a, b) y *
        ∑ u₂', ∑ s', τ s' * ∑ a', A (u₁', s') a' * ∑ b', B (u₂', s') b' *
          (if Test u₁' u₂' s' a' b' y then 1 else 0) := fun u₁' => by
    have := sum_mul_four_swap (τ := τ) (A := A) (B := B) (V := V) (fun _ : A₂ => (1 : ℝ))
      (fun u₂' _ _ _ y => ∑ s', τ s' * ∑ a', A (u₁', s') a' * ∑ b', B (u₂', s') b' *
        (if Test u₁' u₂' s' a' b' y then 1 else 0)) u₁ u₂
    simpa only [one_mul] using this
  simp only [hin]
  have := sum_mul_four_swap (τ := τ) (A := A) (B := B) (V := V) (fun _ : A₁ => (1 : ℝ))
    (fun u₁' _ _ _ y => ∑ u₂', ∑ s', τ s' * ∑ a', A (u₁', s') a' * ∑ b', B (u₂', s') b' *
      (if Test u₁' u₂' s' a' b' y then 1 else 0)) u₁ u₂
  simpa only [one_mul, jsccΦd] using this

omit [Fintype C] [Nonempty A₁] [Nonempty A₂] in
open Classical in
/-- The bound as an expectation of the test terms under the true law. -/
lemma jsccBound_eq (u₁ : A₁) (u₂ : A₂) :
    jsccBound g₁ τ A B V Test u₁ u₂ = ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b *
      ∑ y, V (a, b) y * (jsccΦ₀ Test u₁ u₂ s a b y + jsccΦa A Test u₂ s b y +
        jsccΦb B Test u₁ s a y + jsccΦc g₁ A B Test (g₁ u₁) s y + jsccΦd τ A B Test y) := by
  have e0 : jsccF₀ τ A B V Test u₁ u₂ = ∑ s, τ s * ∑ a, A (u₁, s) a * ∑ b, B (u₂, s) b *
      ∑ y, V (a, b) y * jsccΦ₀ Test u₁ u₂ s a b y := rfl
  rw [jsccBound, e0, sum_jsccFa_eq, sum_jsccFb_eq, sum_jsccFc_eq, sum_jsccFd_eq]
  simp only [← sum_add_distrib, ← mul_add]

end Form

end Bound

end InfoTheory
