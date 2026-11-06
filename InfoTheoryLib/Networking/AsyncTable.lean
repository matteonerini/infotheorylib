/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACBounds

/-!
# Random letter tables and information-density tests

The probabilistic core of the achievability of Theorem 2 of Lecture 24 of El Gamal and Kim. The
codebook of a sender is a table of independent letters. A message hypothesis reads some entries of
the table, and the true messages read others. If a hypothesis reads entries that the true messages
do not read, then those entries are independent of everything else, and a change of measure bounds
the probability that the hypothesis passes an information-density test. No joint typicality lemma
is needed, and the bound holds for arbitrary partitions of the slots into groups, which is what the
partial overlaps of an asynchronous code require.

## Main definitions

* `tableLaw p τ`: the law of a table of independent letters.
* `infoRatio ρ V x y`: the density `V(y | x) / ∑ ρ(x') V(y | x')`.

## Main statements

* `sum_tableLaw_update`: the tower property of a coordinate of a table.
* `sum_tableLaw_prod_le`: integrating out distinct coordinates of a table, one for each factor.
* `sum_tables_prod_le`: **the change of measure** for fresh entries.
* `sum_tables_test_le`: the probability that a hypothesis with fresh entries passes the tests.
* `sum_tables_halves_le`: the same for a hypothesis whose entries conflict with the true ones.
* `sum_tables_fail_le`: the probability that the true messages fail a test.
* `mutualInfoOf_eq_sum_log`, `exists_chernoff`: the exponential bound for the true messages.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset Filter Topology Real

namespace InfoTheory

/-! ### Tables of independent letters -/

section Table

variable {L α : Type*} [Fintype L] [DecidableEq L] [Fintype α]

/-- The law of a table of independent letters with law `p`. -/
def tableLaw (p : α → ℝ) (τ : L → α) : ℝ := ∏ ℓ, p (τ ℓ)

variable {p : α → ℝ}

omit [DecidableEq L] in
lemma tableLaw_nonneg (hp : IsPMF p) (τ : L → α) : 0 ≤ tableLaw p τ :=
  prod_nonneg fun _ _ => hp.nonneg _

lemma sum_tableLaw (hp : IsPMF p) : ∑ τ : L → α, tableLaw p τ = 1 := by
  have h := (Fintype.prod_sum fun (_ : L) (x : α) => p x).symm
  simp only [hp.sum_eq_one, prod_const_one] at h
  exact h

omit [Fintype α] in
/-- Resampling a coordinate swaps two letters in the joint law of the table and a new letter. -/
lemma tableLaw_mul_update (τ : L → α) (ℓ : L) (x : α) :
    tableLaw p τ * p x = tableLaw p (Function.update τ ℓ x) * p (τ ℓ) := by
  unfold tableLaw
  rw [← mul_prod_erase univ _ (mem_univ ℓ),
    ← mul_prod_erase univ (fun j => p (Function.update τ ℓ x j)) (mem_univ ℓ)]
  have : ∏ j ∈ univ.erase ℓ, p (Function.update τ ℓ x j) = ∏ j ∈ univ.erase ℓ, p (τ j) :=
    prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  ring

/-- **The tower property.** Resampling a coordinate of a table does not change an expectation. -/
theorem sum_tableLaw_update (hp : IsPMF p) (ℓ : L) (Φ : (L → α) → ℝ) :
    ∑ τ, tableLaw p τ * Φ τ = ∑ τ, tableLaw p τ * ∑ x, p x * Φ (Function.update τ ℓ x) := by
  -- The map `(τ, x) ↦ (update τ ℓ x, τ ℓ)` is an involution.
  let e : (L → α) × α → (L → α) × α := fun z => (Function.update z.1 ℓ z.2, z.1 ℓ)
  have he : Function.Involutive e := by
    rintro ⟨τ, x⟩
    simp [e]
  have h1 : ∑ τ, tableLaw p τ * ∑ x, p x * Φ (Function.update τ ℓ x) =
      ∑ z : (L → α) × α, tableLaw p z.1 * p z.2 * Φ (Function.update z.1 ℓ z.2) := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun τ _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by ring
  have h2 : ∑ z : (L → α) × α, tableLaw p z.1 * p z.2 * Φ (Function.update z.1 ℓ z.2) =
      ∑ z : (L → α) × α, tableLaw p z.1 * p z.2 * Φ z.1 := by
    rw [← Equiv.sum_comp he.toPerm (fun z : (L → α) × α => tableLaw p z.1 * p z.2 * Φ z.1)]
    refine sum_congr rfl fun z _ => ?_
    simp only [Function.Involutive.coe_toPerm, e]
    rw [← tableLaw_mul_update]
  rw [h1, h2, Fintype.sum_prod_type]
  refine sum_congr rfl fun τ _ => ?_
  have : ∑ x, tableLaw p τ * p x * Φ τ = tableLaw p τ * Φ τ * ∑ x, p x := by
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by ring
  rw [this, hp.sum_eq_one, mul_one]

/-- **Integrating out distinct coordinates of a table.** Each factor `h t` is bounded, after
averaging over its own coordinate `ℓ t`, by `g t`, and it does not depend on the coordinates of the
other factors. -/
theorem sum_tableLaw_prod_le {ι : Type*} (hp : IsPMF p) (A : Finset ι) (ℓ : ι → L)
    (hℓ : Set.InjOn ℓ A) (F : (L → α) → ℝ) (h g : ι → (L → α) → ℝ) (hF0 : ∀ τ, 0 ≤ F τ)
    (hF : ∀ t ∈ A, ∀ τ x, F (Function.update τ (ℓ t) x) = F τ) (hh0 : ∀ t ∈ A, ∀ τ, 0 ≤ h t τ)
    (hg0 : ∀ t ∈ A, ∀ τ, 0 ≤ g t τ)
    (hh : ∀ t ∈ A, ∀ t' ∈ A, t' ≠ t → ∀ τ x, h t (Function.update τ (ℓ t') x) = h t τ)
    (hg : ∀ t ∈ A, ∀ t' ∈ A, ∀ τ x, g t (Function.update τ (ℓ t') x) = g t τ)
    (hb : ∀ t ∈ A, ∀ τ, ∑ x, p x * h t (Function.update τ (ℓ t) x) ≤ g t τ) :
    ∑ τ, tableLaw p τ * (F τ * ∏ t ∈ A, h t τ) ≤ ∑ τ, tableLaw p τ * (F τ * ∏ t ∈ A, g t τ) := by
  classical
  induction A using Finset.induction_on generalizing F with
  | empty => simp
  | insert t₀ A ht₀ ih =>
    have hmem : t₀ ∈ insert t₀ A := mem_insert_self _ _
    have hsub : ∀ t ∈ A, t ∈ insert t₀ A := fun t ht => mem_insert_of_mem ht
    have hne : ∀ t ∈ A, t ≠ t₀ := fun t ht h' => ht₀ (h' ▸ ht)
    set G : (L → α) → ℝ := fun τ => F τ * ∏ t ∈ A, h t τ with hG
    have hG0 : ∀ τ, 0 ≤ G τ := fun τ =>
      mul_nonneg (hF0 τ) (prod_nonneg fun t ht => hh0 t (hsub t ht) τ)
    have hGu : ∀ τ x, G (Function.update τ (ℓ t₀) x) = G τ := by
      intro τ x
      simp only [hG]
      rw [hF t₀ hmem]
      congr 1
      exact prod_congr rfl fun t ht => hh t (hsub t ht) t₀ hmem (hne t ht).symm τ x
    -- Integrate the coordinate `ℓ t₀`.
    have h1 : ∑ τ, tableLaw p τ * (F τ * ∏ t ∈ insert t₀ A, h t τ) ≤
        ∑ τ, tableLaw p τ * ((F τ * g t₀ τ) * ∏ t ∈ A, h t τ) := by
      have e1 : ∀ τ, F τ * ∏ t ∈ insert t₀ A, h t τ = G τ * h t₀ τ := by
        intro τ
        rw [prod_insert ht₀]
        simp only [hG]
        ring
      simp only [e1]
      rw [sum_tableLaw_update hp (ℓ t₀)]
      refine sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left ?_ (tableLaw_nonneg hp τ)
      have e2 : ∑ x, p x * (G (Function.update τ (ℓ t₀) x) * h t₀ (Function.update τ (ℓ t₀) x)) =
          G τ * ∑ x, p x * h t₀ (Function.update τ (ℓ t₀) x) := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [hGu]
        ring
      rw [e2]
      calc G τ * ∑ x, p x * h t₀ (Function.update τ (ℓ t₀) x) ≤ G τ * g t₀ τ :=
            mul_le_mul_of_nonneg_left (hb t₀ hmem τ) (hG0 τ)
        _ = F τ * g t₀ τ * ∏ t ∈ A, h t τ := by
            simp only [hG]
            ring
    refine h1.trans ?_
    -- The remaining coordinates, by induction.
    have h2 := ih (fun t₁ ht₁ t₂ ht₂ he => hℓ (hsub t₁ ht₁) (hsub t₂ ht₂) he)
      (fun τ => F τ * g t₀ τ) (fun τ => mul_nonneg (hF0 τ) (hg0 t₀ hmem τ))
      (fun t ht τ x => by
        rw [hF t (hsub t ht), hg t₀ hmem t (hsub t ht)])
      (fun t ht τ => hh0 t (hsub t ht) τ) (fun t ht τ => hg0 t (hsub t ht) τ)
      (fun t ht t' ht' hn τ x => hh t (hsub t ht) t' (hsub t' ht') hn τ x)
      (fun t ht t' ht' τ x => hg t (hsub t ht) t' (hsub t' ht') τ x)
      (fun t ht τ => hb t (hsub t ht) τ)
    refine h2.trans (le_of_eq ?_)
    refine sum_congr rfl fun τ _ => ?_
    rw [prod_insert ht₀]
    ring

/-- A real expectation over a table is attained somewhere. -/
lemma exists_le_of_sum_tableLaw_le (hp : IsPMF p) {f : (L → α) → ℝ} {c : ℝ}
    (h : ∑ τ, tableLaw p τ * f τ ≤ c) : ∃ τ, f τ ≤ c := by
  by_contra hcon
  push Not at hcon
  have h1 : ∑ τ : L → α, tableLaw p τ * c < ∑ τ, tableLaw p τ * f τ := by
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ : L → α, 0 < tableLaw p τ := by
      by_contra hno
      push Not at hno
      have h0 : ∑ τ : L → α, tableLaw p τ ≤ 0 := sum_nonpos fun τ _ => hno τ
      rw [(sum_tableLaw hp : ∑ τ : L → α, tableLaw p τ = 1)] at h0
      linarith
    refine sum_lt_sum (fun τ _ => mul_le_mul_of_nonneg_left (hcon τ).le (tableLaw_nonneg hp τ))
      ⟨τ₀, mem_univ _, mul_lt_mul_of_pos_left (hcon τ₀) hτ₀⟩
  rw [← sum_mul, (sum_tableLaw hp : ∑ τ : L → α, tableLaw p τ = 1), one_mul] at h1
  linarith

end Table

/-! ### The information density -/

section Ratio

variable {γ β : Type*} [Fintype γ] [Fintype β]

/-- The density `V(y | x) / ∑ ρ(x') V(y | x')` of a channel `V` with input law `ρ`. -/
def infoRatio (ρ : γ → ℝ) (V : γ → β → ℝ) (x : γ) (y : β) : ℝ :=
  V x y / ∑ x', ρ x' * V x' y

variable {ρ : γ → ℝ} {V : γ → β → ℝ}

lemma infoRatio_nonneg (hρ : IsPMF ρ) (hV : IsChannel V) (x : γ) (y : β) :
    0 ≤ infoRatio ρ V x y :=
  div_nonneg ((hV x).nonneg y) (sum_nonneg fun x' _ => mul_nonneg (hρ.nonneg _) ((hV x').nonneg y))

omit [Fintype β] in
/-- **The change of measure.** The density averages to at most `1` over the input. -/
lemma sum_mul_infoRatio_le (y : β) :
    ∑ x, ρ x * infoRatio ρ V x y ≤ 1 := by
  set q := ∑ x', ρ x' * V x' y with hq
  have h1 : ∑ x, ρ x * infoRatio ρ V x y = q / q := by
    unfold infoRatio
    rw [hq, sum_div]
    exact sum_congr rfl fun x _ => by ring
  rw [h1]
  exact div_self_le_one q

/-- On the support of the joint law the density is positive. -/
lemma infoRatio_pos (hρ : IsPMF ρ) (hV : IsChannel V) {x : γ} {y : β} (hx : 0 < ρ x)
    (hy : 0 < V x y) : 0 < infoRatio ρ V x y := by
  refine div_pos hy ?_
  have h1 : 0 < ρ x * V x y := mul_pos hx hy
  exact lt_of_lt_of_le h1 (single_le_sum (f := fun x' => ρ x' * V x' y)
    (fun x' _ => mul_nonneg (hρ.nonneg _) ((hV x').nonneg y)) (mem_univ x))

/-- `I(X; Y) = ∑ ρ(x) V(y | x) log(V(y | x) / q(y))`. -/
theorem mutualInfoOf_eq_sum_log (hρ : IsPMF ρ) (hV : IsChannel V) :
    mutualInfoOf ρ V = ∑ x, ∑ y, ρ x * V x y * log (infoRatio ρ V x y) := by
  rw [mutualInfoOf_eq_sum hρ hV]
  have h1 : ∀ y, negMulLog (∑ x, ρ x * V x y) =
      - ∑ x, ρ x * V x y * log (∑ x', ρ x' * V x' y) := by
    intro y
    rw [negMulLog, ← sum_mul, neg_mul]
  have h2 : ∀ x, ρ x * entropy (V x) = - ∑ y, ρ x * V x y * log (V x y) := by
    intro x
    rw [entropy_eq_sum_negMulLog, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun y _ => ?_
    rw [negMulLog]
    ring
  have key : ∀ x y, ρ x * V x y * log (infoRatio ρ V x y) =
      ρ x * V x y * log (V x y) - ρ x * V x y * log (∑ x', ρ x' * V x' y) := by
    intro x y
    by_cases h0 : ρ x * V x y = 0
    · simp [h0]
    · have hx : 0 < ρ x := lt_of_le_of_ne (hρ.nonneg x) fun h => h0 (by rw [← h, zero_mul])
      have hy : 0 < V x y := lt_of_le_of_ne ((hV x).nonneg y) fun h => h0 (by rw [← h, mul_zero])
      have hq : 0 < ∑ x', ρ x' * V x' y := lt_of_lt_of_le (mul_pos hx hy)
        (single_le_sum (f := fun x' => ρ x' * V x' y)
          (fun x' _ => mul_nonneg (hρ.nonneg _) ((hV x').nonneg y)) (mem_univ x))
      rw [infoRatio, Real.log_div hy.ne' hq.ne']
      ring
  simp only [h1, h2, key, sum_sub_distrib, sum_neg_distrib]
  rw [sum_comm (f := fun y x => ρ x * V x y * log (∑ x', ρ x' * V x' y))]
  ring

end Ratio

/-! ### Summing over a window of outputs -/

section Slots

variable {β T : Type*} [Fintype β] [Fintype T] [DecidableEq T]

/-- **Summing out the outputs.** The outputs outside `G` disappear, and those in `G` factor. -/
lemma sum_prod_window (V : T → β → ℝ) (hV : ∀ t, ∑ y, V t y = 1) (G : Finset T)
    (e : T → β → ℝ) :
    ∑ y : T → β, (∏ t, V t (y t)) * ∏ t ∈ G, e t (y t) = ∏ t ∈ G, ∑ b, V t b * e t b := by
  classical
  set f : T → β → ℝ := fun t b => V t b * (if t ∈ G then e t b else 1) with hf
  have h1 : ∀ y : T → β, (∏ t, V t (y t)) * ∏ t ∈ G, e t (y t) = ∏ t, f t (y t) := by
    intro y
    simp only [hf]
    rw [prod_mul_distrib, prod_ite_mem univ G, univ_inter]
  simp only [h1]
  rw [← Fintype.prod_sum f]
  have h2 : ∀ t, ∑ b, f t b = if t ∈ G then ∑ b, V t b * e t b else 1 := by
    intro t
    by_cases ht : t ∈ G
    · simp [hf, ht]
    · simp [hf, ht, hV]
  simp only [h2]
  rw [prod_ite_mem univ G, univ_inter]

end Slots

/-! ### The change of measure for fresh entries -/

section Fresh

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]
  {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} {W : α₁ × α₂ → β → ℝ}

/-- The density of sender 1 given sender 2. -/
abbrev macRatio₁ (p₁ : α₁ → ℝ) (W : α₁ × α₂ → β → ℝ) (x₁ : α₁) (x₂ : α₂) (y : β) : ℝ :=
  infoRatio p₁ (fun a => W (a, x₂)) x₁ y

/-- The density of sender 2 given sender 1. -/
abbrev macRatio₂ (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (x₁ : α₁) (x₂ : α₂) (y : β) : ℝ :=
  infoRatio p₂ (fun b => W (x₁, b)) x₂ y

/-- The density of the two senders together. -/
abbrev macRatio₁₂ (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (x₁ : α₁) (x₂ : α₂) (y : β) :
    ℝ := infoRatio (prodDist p₁ p₂) W (x₁, x₂) y

/-- The expected density of sender 1 at a slot, given the true inputs `x₁, x₂`, for the hypothesized
inputs `u₁, u₂`. -/
def slotR₁ (p₁ : α₁ → ℝ) (W : α₁ × α₂ → β → ℝ) (x₁ : α₁) (x₂ : α₂) (u₁ : α₁) (u₂ : α₂) : ℝ :=
  ∑ y, W (x₁, x₂) y * macRatio₁ p₁ W u₁ u₂ y

/-- The expected density of sender 2 at a slot. -/
def slotR₂ (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (x₁ : α₁) (x₂ : α₂) (u₁ : α₁) (u₂ : α₂) : ℝ :=
  ∑ y, W (x₁, x₂) y * macRatio₂ p₂ W u₁ u₂ y

/-- The expected density of the two senders at a slot. -/
def slotR₁₂ (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (x₁ : α₁) (x₂ : α₂) (u₁ : α₁)
    (u₂ : α₂) : ℝ :=
  ∑ y, W (x₁, x₂) y * macRatio₁₂ p₁ p₂ W u₁ u₂ y

/-- `slotR₁₂` after averaging over the letter of sender 1. -/
def slotM (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (x₁ : α₁) (x₂ : α₂) (u₂ : α₂) : ℝ :=
  ∑ y, W (x₁, x₂) y * ∑ u₁, p₁ u₁ * macRatio₁₂ p₁ p₂ W u₁ u₂ y

omit [Fintype α₂] in
lemma slotR₁_nonneg (hp₁ : IsPMF p₁) (hW : IsChannel W) (x₁ : α₁) (x₂ : α₂) (u₁ : α₁) (u₂ : α₂) :
    0 ≤ slotR₁ p₁ W x₁ x₂ u₁ u₂ :=
  sum_nonneg fun y _ => mul_nonneg ((hW _).nonneg y)
    (infoRatio_nonneg hp₁ (fun a => hW (a, u₂)) _ _)

omit [Fintype α₁] in
lemma slotR₂_nonneg (hp₂ : IsPMF p₂) (hW : IsChannel W) (x₁ : α₁) (x₂ : α₂) (u₁ : α₁) (u₂ : α₂) :
    0 ≤ slotR₂ p₂ W x₁ x₂ u₁ u₂ :=
  sum_nonneg fun y _ => mul_nonneg ((hW _).nonneg y)
    (infoRatio_nonneg hp₂ (fun b => hW (u₁, b)) _ _)

lemma slotR₁₂_nonneg (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (x₁ : α₁) (x₂ : α₂)
    (u₁ : α₁) (u₂ : α₂) : 0 ≤ slotR₁₂ p₁ p₂ W x₁ x₂ u₁ u₂ :=
  sum_nonneg fun y _ => mul_nonneg ((hW _).nonneg y)
    (infoRatio_nonneg (hp₁.prodDist hp₂) hW _ _)

lemma slotM_nonneg (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (x₁ : α₁) (x₂ : α₂)
    (u₂ : α₂) : 0 ≤ slotM p₁ p₂ W x₁ x₂ u₂ :=
  sum_nonneg fun y _ => mul_nonneg ((hW _).nonneg y) (sum_nonneg fun _ _ =>
    mul_nonneg (hp₁.nonneg _) (infoRatio_nonneg (hp₁.prodDist hp₂) hW _ _))

omit [Fintype α₂] in
/-- Averaging over a fresh letter of sender 1. -/
lemma sum_mul_slotR₁_le (hW : IsChannel W) (x₁ : α₁) (x₂ : α₂) (u₂ : α₂) :
    ∑ u, p₁ u * slotR₁ p₁ W x₁ x₂ u u₂ ≤ 1 := by
  calc ∑ u, p₁ u * slotR₁ p₁ W x₁ x₂ u u₂
      = ∑ y, W (x₁, x₂) y * ∑ u, p₁ u * macRatio₁ p₁ W u u₂ y := by
        unfold slotR₁
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun y _ => sum_congr rfl fun u _ => by ring
    _ ≤ ∑ y, W (x₁, x₂) y * 1 :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (sum_mul_infoRatio_le _) ((hW _).nonneg y)
    _ = 1 := by simp [(hW _).sum_eq_one]

omit [Fintype α₁] in
/-- Averaging over a fresh letter of sender 2. -/
lemma sum_mul_slotR₂_le (hW : IsChannel W) (x₁ : α₁) (x₂ : α₂) (u₁ : α₁) :
    ∑ u, p₂ u * slotR₂ p₂ W x₁ x₂ u₁ u ≤ 1 := by
  calc ∑ u, p₂ u * slotR₂ p₂ W x₁ x₂ u₁ u
      = ∑ y, W (x₁, x₂) y * ∑ u, p₂ u * macRatio₂ p₂ W u₁ u y := by
        unfold slotR₂
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun y _ => sum_congr rfl fun u _ => by ring
    _ ≤ ∑ y, W (x₁, x₂) y * 1 :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (sum_mul_infoRatio_le _) ((hW _).nonneg y)
    _ = 1 := by simp [(hW _).sum_eq_one]

lemma sum_mul_slotR₁₂ (x₁ : α₁) (x₂ : α₂) (u₂ : α₂) :
    ∑ u, p₁ u * slotR₁₂ p₁ p₂ W x₁ x₂ u u₂ = slotM p₁ p₂ W x₁ x₂ u₂ := by
  unfold slotR₁₂ slotM
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun u _ => by ring

/-- Averaging over a fresh pair of letters. -/
lemma sum_mul_slotM_le (hW : IsChannel W) (x₁ : α₁) (x₂ : α₂) :
    ∑ u, p₂ u * slotM p₁ p₂ W x₁ x₂ u ≤ 1 := by
  have hpt : ∀ y, ∑ u₂, p₂ u₂ * ∑ u₁, p₁ u₁ * macRatio₁₂ p₁ p₂ W u₁ u₂ y ≤ 1 := by
    intro y
    have h := sum_mul_infoRatio_le (ρ := prodDist p₁ p₂) (V := W) y
    rw [Fintype.sum_prod_type, sum_comm] at h
    refine le_trans (le_of_eq ?_) h
    refine sum_congr rfl fun u₂ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u₁ _ => ?_
    simp only [prodDist]
    ring
  calc ∑ u, p₂ u * slotM p₁ p₂ W x₁ x₂ u
      = ∑ y, W (x₁, x₂) y * ∑ u₂, p₂ u₂ * ∑ u₁, p₁ u₁ * macRatio₁₂ p₁ p₂ W u₁ u₂ y := by
        unfold slotM
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun u _ => ?_
        exact sum_congr rfl fun v _ => by ring
    _ ≤ ∑ y, W (x₁, x₂) y * 1 :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpt y) ((hW _).nonneg y)
    _ = 1 := by simp [(hW _).sum_eq_one]

variable {L₁ L₂ T : Type*} [Fintype L₁] [Fintype L₂] [Fintype T] [DecidableEq L₁] [DecidableEq L₂]
  [DecidableEq T]

omit [Fintype T] in
/-- **The change of measure for fresh entries.** A hypothesis reads the entries `ah t`, `bh t`, and
the true messages read `a t`, `b t`. On the group `G₂` the entries of sender 1 are fresh, on `G₃`
those of sender 2, and on `G₄` both. The expected product of the densities is at most `1`. -/
theorem sum_tables_prod_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W)
    (a ah : T → L₁) (b bh : T → L₂) {G₂ G₃ G₄ : Finset T} (h₂₄ : Disjoint G₂ G₄)
    (h₃₄ : Disjoint G₃ G₄) (hah : Set.InjOn ah (G₂ ∪ G₄ : Finset T))
    (hbh : Set.InjOn bh (G₃ ∪ G₄ : Finset T))
    (hfa : ∀ t ∈ G₂ ∪ G₄, ∀ t' ∈ G₂ ∪ G₃ ∪ G₄, ah t ≠ a t')
    (hfa' : ∀ t ∈ G₂ ∪ G₄, ∀ t' ∈ G₃, ah t ≠ ah t')
    (hfb : ∀ t ∈ G₃ ∪ G₄, ∀ t' ∈ G₂ ∪ G₃ ∪ G₄, bh t ≠ b t') :
    ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ *
      ((∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t)))) ≤ 1 := by
  classical
  -- Integrate the fresh entries of sender 1.
  have hA : ∀ τ₂ : L₂ → α₂, ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ *
      ((∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t)))) ≤
      ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ *
      ((∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        ∏ t ∈ G₄, slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t))) := by
    intro τ₂
    set H : T → (L₁ → α₁) → ℝ := fun t τ₁ =>
      if t ∈ G₂ then slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))
      else slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t)) with hH
    set g : T → (L₁ → α₁) → ℝ := fun t τ₁ =>
      if t ∈ G₂ then 1 else slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t)) with hg
    have hT := sum_tableLaw_prod_le hp₁ (G₂ ∪ G₄) ah hah
      (fun τ₁ => ∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) H g
      (fun τ₁ => prod_nonneg fun t _ => slotR₂_nonneg hp₂ hW _ _ _ _)
      (fun t ht τ₁ x => by
        refine prod_congr rfl fun t' ht' => ?_
        have h1 := hfa t ht t' (by simp [ht'])
        have h2 := hfa' t ht t' ht'
        rw [Function.update_of_ne h1.symm, Function.update_of_ne h2.symm])
      (fun t _ τ₁ => by
        simp only [hH]
        split_ifs
        · exact slotR₁_nonneg hp₁ hW _ _ _ _
        · exact slotR₁₂_nonneg hp₁ hp₂ hW _ _ _ _)
      (fun t _ τ₁ => by
        simp only [hg]
        split_ifs
        · exact zero_le_one
        · exact slotM_nonneg hp₁ hp₂ hW _ _ _)
      (fun t ht t' ht' hn τ₁ x => by
        have h1 := hfa t' ht' t (by rcases mem_union.1 ht with h | h <;> simp [h])
        have h2 : ah t ≠ ah t' := fun he => hn (hah (by exact_mod_cast ht') (by exact_mod_cast ht)
          he.symm)
        simp only [hH]
        rw [Function.update_of_ne h1.symm, Function.update_of_ne h2])
      (fun t ht t' ht' τ₁ x => by
        have h1 := hfa t' ht' t (by rcases mem_union.1 ht with h | h <;> simp [h])
        simp only [hg]
        rw [Function.update_of_ne h1.symm])
      (fun t ht τ₁ => by
        have h1 := hfa t ht t (by rcases mem_union.1 ht with h | h <;> simp [h])
        simp only [hH, hg]
        by_cases h2 : t ∈ G₂
        · simp only [h2, ite_true, Function.update_of_ne h1.symm, Function.update_self]
          exact sum_mul_slotR₁_le hW _ _ _
        · simp only [h2, ite_false, Function.update_of_ne h1.symm, Function.update_self]
          exact le_of_eq (sum_mul_slotR₁₂ _ _ _))
    have e1 : ∀ τ₁ : L₁ → α₁, ∏ t ∈ G₂ ∪ G₄, H t τ₁ =
        (∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
          ∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t)) := by
      intro τ₁
      rw [prod_union h₂₄]
      congr 1
      · exact prod_congr rfl fun t ht => by simp [hH, ht]
      · exact prod_congr rfl fun t ht => by simp [hH, disjoint_right.1 h₂₄ ht]
    have e2 : ∀ τ₁ : L₁ → α₁, ∏ t ∈ G₂ ∪ G₄, g t τ₁ =
        ∏ t ∈ G₄, slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t)) := by
      intro τ₁
      rw [prod_union h₂₄]
      have h1 : ∏ t ∈ G₂, g t τ₁ = 1 := prod_eq_one fun t ht => by simp [hg, ht]
      rw [h1, one_mul]
      exact prod_congr rfl fun t ht => by simp [hg, disjoint_right.1 h₂₄ ht]
    simp only [e1, e2] at hT
    refine le_trans (le_of_eq ?_) hT
    exact sum_congr rfl fun τ₁ _ => by ring
  -- Integrate the fresh entries of sender 2.
  have hB : ∀ τ₁ : L₁ → α₁, ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ *
      ((∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        ∏ t ∈ G₄, slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t))) ≤ 1 := by
    intro τ₁
    set H : T → (L₂ → α₂) → ℝ := fun t τ₂ =>
      if t ∈ G₃ then slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))
      else slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t)) with hH
    have hT := sum_tableLaw_prod_le hp₂ (G₃ ∪ G₄) bh hbh (fun _ => 1) H (fun _ _ => 1)
      (fun _ => zero_le_one) (fun _ _ _ _ => rfl)
      (fun t _ τ₂ => by
        simp only [hH]
        split_ifs
        · exact slotR₂_nonneg hp₂ hW _ _ _ _
        · exact slotM_nonneg hp₁ hp₂ hW _ _ _)
      (fun _ _ _ => zero_le_one)
      (fun t ht t' ht' hn τ₂ x => by
        have h1 := hfb t' ht' t (by rcases mem_union.1 ht with h | h <;> simp [h])
        have h2 : bh t ≠ bh t' := fun he => hn (hbh (by exact_mod_cast ht') (by exact_mod_cast ht)
          he.symm)
        simp only [hH]
        rw [Function.update_of_ne h1.symm, Function.update_of_ne h2])
      (fun _ _ _ _ _ _ => rfl)
      (fun t ht τ₂ => by
        have h1 := hfb t ht t (by rcases mem_union.1 ht with h | h <;> simp [h])
        simp only [hH]
        by_cases h2 : t ∈ G₃
        · simp only [h2, ite_true, Function.update_of_ne h1.symm, Function.update_self]
          exact sum_mul_slotR₂_le hW _ _ _
        · simp only [h2, ite_false, Function.update_of_ne h1.symm, Function.update_self]
          exact sum_mul_slotM_le hW _ _)
    have e1 : ∀ τ₂ : L₂ → α₂, ∏ t ∈ G₃ ∪ G₄, H t τ₂ =
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
          ∏ t ∈ G₄, slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t)) := by
      intro τ₂
      rw [prod_union h₃₄]
      congr 1
      · exact prod_congr rfl fun t ht => by simp [hH, ht]
      · exact prod_congr rfl fun t ht => by simp [hH, disjoint_right.1 h₃₄ ht]
    simp only [e1, one_mul, prod_const_one, mul_one] at hT
    rw [sum_tableLaw hp₂] at hT
    exact hT
  calc _ = ∑ τ₂ : L₂ → α₂, ∑ τ₁ : L₁ → α₁, tableLaw p₂ τ₂ * (tableLaw p₁ τ₁ *
      ((∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))))) := by
        exact (sum_congr rfl fun τ₁ _ => mul_sum _ _ _).trans (sum_comm.trans
          (sum_congr rfl fun τ₂ _ => sum_congr rfl fun τ₁ _ => by ring))
    _ = ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ *
      ((∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t)))) :=
        sum_congr rfl fun τ₂ _ => (mul_sum _ _ _).symm
    _ ≤ ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ *
      ((∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        ∏ t ∈ G₄, slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t))) :=
        sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left (hA τ₂) (tableLaw_nonneg hp₂ τ₂)
    _ = ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ *
      ((∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        ∏ t ∈ G₄, slotM p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₂ (bh t))) := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun τ₁ _ => sum_congr rfl fun τ₂ _ => by ring
    _ ≤ ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * 1 :=
        sum_le_sum fun τ₁ _ => mul_le_mul_of_nonneg_left (hB τ₁) (tableLaw_nonneg hp₁ τ₁)
    _ = 1 := by simp [sum_tableLaw hp₁]

/-- **A hypothesis with fresh entries rarely passes the tests.** The probability that the products
of the densities over the three groups exceed `e^{A₂}`, `e^{A₃}` and `e^{A₄}` is at most
`e^{-(A₂ + A₃ + A₄)}`. -/
theorem sum_tables_test_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W)
    (a ah : T → L₁) (b bh : T → L₂) {G₂ G₃ G₄ : Finset T} (h₂₃ : Disjoint G₂ G₃)
    (h₂₄ : Disjoint G₂ G₄) (h₃₄ : Disjoint G₃ G₄) (hah : Set.InjOn ah (G₂ ∪ G₄ : Finset T))
    (hbh : Set.InjOn bh (G₃ ∪ G₄ : Finset T))
    (hfa : ∀ t ∈ G₂ ∪ G₄, ∀ t' ∈ G₂ ∪ G₃ ∪ G₄, ah t ≠ a t')
    (hfa' : ∀ t ∈ G₂ ∪ G₄, ∀ t' ∈ G₃, ah t ≠ ah t')
    (hfb : ∀ t ∈ G₃ ∪ G₄, ∀ t' ∈ G₂ ∪ G₃ ∪ G₄, bh t ≠ b t') (A₂ A₃ A₄ : ℝ) :
    ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
      (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
      (if exp A₂ ≤ ∏ t ∈ G₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) ∧
          exp A₃ ≤ ∏ t ∈ G₃, macRatio₂ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) ∧
          exp A₄ ≤ ∏ t ∈ G₄, macRatio₁₂ p₁ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) then 1 else 0) ≤
      exp (-(A₂ + A₃ + A₄)) := by
  classical
  set c := exp (-(A₂ + A₃ + A₄)) with hc
  have hc0 : 0 ≤ c := (exp_pos _).le
  -- The bound for fixed tables.
  have hpt : ∀ (τ₁ : L₁ → α₁) (τ₂ : L₂ → α₂), ∑ y : T → β,
      (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
      (if exp A₂ ≤ ∏ t ∈ G₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) ∧
          exp A₃ ≤ ∏ t ∈ G₃, macRatio₂ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) ∧
          exp A₄ ≤ ∏ t ∈ G₄, macRatio₁₂ p₁ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) then 1 else 0) ≤
      c * ((∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t)))) := by
    intro τ₁ τ₂
    set e : T → β → ℝ := fun t y =>
      if t ∈ G₂ then macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) y
      else if t ∈ G₃ then macRatio₂ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) y
      else macRatio₁₂ p₁ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) y with he
    have hd : Disjoint (G₂ ∪ G₃) G₄ := disjoint_union_left.2 ⟨h₂₄, h₃₄⟩
    have hsum := sum_prod_window (fun t y => W (τ₁ (a t), τ₂ (b t)) y)
      (fun t => (hW _).sum_eq_one) (G₂ ∪ G₃ ∪ G₄) e
    -- Splitting a product over the three groups.
    have hsplit : ∀ φ : T → ℝ, ∀ φ₂ φ₃ φ₄ : T → ℝ, (∀ t ∈ G₂, φ t = φ₂ t) → (∀ t ∈ G₃, φ t = φ₃ t) →
        (∀ t ∈ G₄, φ t = φ₄ t) →
        ∏ t ∈ G₂ ∪ G₃ ∪ G₄, φ t = (∏ t ∈ G₂, φ₂ t) * (∏ t ∈ G₃, φ₃ t) * ∏ t ∈ G₄, φ₄ t := by
      intro φ φ₂ φ₃ φ₄ h2 h3 h4
      rw [prod_union hd, prod_union h₂₃, prod_congr rfl h2, prod_congr rfl h3, prod_congr rfl h4]
    have he2 : ∀ t ∈ G₃, t ∉ G₂ := fun t ht => disjoint_right.1 h₂₃ ht
    have he3 : ∀ t ∈ G₄, t ∉ G₂ := fun t ht => disjoint_right.1 h₂₄ ht
    have he4 : ∀ t ∈ G₄, t ∉ G₃ := fun t ht => disjoint_right.1 h₃₄ ht
    have hrhs : ∏ t ∈ G₂ ∪ G₃ ∪ G₄, ∑ y, W (τ₁ (a t), τ₂ (b t)) y * e t y =
        (∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) := by
      refine hsplit _ _ _ _ (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
      · simp [he, ht, slotR₁]
      · simp [he, ht, he2 t ht, slotR₂]
      · simp [he, he3 t ht, he4 t ht, slotR₁₂]
    rw [hrhs] at hsum
    rw [← hsum, mul_sum]
    refine sum_le_sum fun y _ => ?_
    have hW0 : 0 ≤ ∏ t, W (τ₁ (a t), τ₂ (b t)) (y t) := prod_nonneg fun t _ => (hW _).nonneg _
    have hprod : ∏ t ∈ G₂ ∪ G₃ ∪ G₄, e t (y t) =
        (∏ t ∈ G₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) *
        (∏ t ∈ G₃, macRatio₂ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) *
        (∏ t ∈ G₄, macRatio₁₂ p₁ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) := by
      refine hsplit _ _ _ _ (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
      · simp [he, ht]
      · simp [he, ht, he2 t ht]
      · simp [he, he3 t ht, he4 t ht]
    rw [hprod]
    set S₁ := ∏ t ∈ G₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)
    set S₂ := ∏ t ∈ G₃, macRatio₂ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)
    set S₃ := ∏ t ∈ G₄, macRatio₁₂ p₁ p₂ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)
    have hS₁ : 0 ≤ S₁ := prod_nonneg fun t _ => infoRatio_nonneg hp₁ (fun a => hW (a, _)) _ _
    have hS₂ : 0 ≤ S₂ := prod_nonneg fun t _ => infoRatio_nonneg hp₂ (fun b => hW (_, b)) _ _
    have hS₃ : 0 ≤ S₃ := prod_nonneg fun t _ => infoRatio_nonneg (hp₁.prodDist hp₂) hW _ _
    have hind : (if exp A₂ ≤ S₁ ∧ exp A₃ ≤ S₂ ∧ exp A₄ ≤ S₃ then (1 : ℝ) else 0) ≤
        c * (S₁ * S₂ * S₃) := by
      split_ifs with hpass
      · obtain ⟨h1, h2, h3⟩ := hpass
        have h4 : exp A₂ * exp A₃ ≤ S₁ * S₂ := mul_le_mul h1 h2 (exp_pos _).le hS₁
        have h5 : exp A₂ * exp A₃ * exp A₄ ≤ S₁ * S₂ * S₃ :=
          mul_le_mul h4 h3 (exp_pos _).le (mul_nonneg hS₁ hS₂)
        have h6 : c * (exp A₂ * exp A₃ * exp A₄) = 1 := by
          rw [hc, ← exp_add, ← exp_add, ← exp_add]
          convert exp_zero using 2
          ring
        calc (1 : ℝ) = c * (exp A₂ * exp A₃ * exp A₄) := h6.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h5 hc0
      · exact mul_nonneg hc0 (mul_nonneg (mul_nonneg hS₁ hS₂) hS₃)
    calc _ ≤ (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) * (c * (S₁ * S₂ * S₃)) :=
          mul_le_mul_of_nonneg_left hind hW0
      _ = _ := by ring
  have hmain := sum_tables_prod_le hp₁ hp₂ hW a ah b bh h₂₄ h₃₄ hah hbh hfa hfa' hfb
  calc _ ≤ ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * (c *
        ((∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))))) :=
        sum_le_sum fun τ₁ _ => mul_le_mul_of_nonneg_left
          (sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left (hpt τ₁ τ₂) (tableLaw_nonneg hp₂ τ₂))
          (tableLaw_nonneg hp₁ τ₁)
    _ = c * ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ *
        ((∏ t ∈ G₂, slotR₁ p₁ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₃, slotR₂ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t))) *
        (∏ t ∈ G₄, slotR₁₂ p₁ p₂ W (τ₁ (a t)) (τ₂ (b t)) (τ₁ (ah t)) (τ₂ (bh t)))) := by
        simp only [mul_sum]
        refine sum_congr rfl fun τ₁ _ => sum_congr rfl fun τ₂ _ => by ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hmain hc0
    _ = c := mul_one c

/-- **The bound for a test with conflicts.** If the group `G` splits into two parts, each reading
entries that its own true letters do not read, the product of the densities over `G` exceeds `e^A`
with probability at most `e^{-A / 2}`. -/
theorem sum_tables_halves_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W)
    (a ah : T → L₁) (b : T → L₂) (bh : T → L₂) {G A₁ A₂ : Finset T} (hG : A₁ ∪ A₂ = G)
    (hd : Disjoint A₁ A₂) (hah : Set.InjOn ah (G : Finset T))
    (hf₁ : ∀ t ∈ A₁, ∀ t' ∈ A₁, ah t ≠ a t') (hf₂ : ∀ t ∈ A₂, ∀ t' ∈ A₂, ah t ≠ a t') (A : ℝ) :
    ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
      (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
      (if exp A ≤ ∏ t ∈ G, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) then 1 else 0) ≤
      exp (-(A / 2)) := by
  classical
  have hsub₁ : A₁ ⊆ G := hG ▸ subset_union_left
  have hsub₂ : A₂ ⊆ G := hG ▸ subset_union_right
  -- A part alone has expected density at most `1`.
  have hpart : ∀ B : Finset T, B ⊆ G → (∀ t ∈ B, ∀ t' ∈ B, ah t ≠ a t') →
      ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
        (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
        ∏ t ∈ B, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) ≤ 1 := by
    intro B hB hfB
    have h := sum_tables_prod_le (G₂ := B) (G₃ := ∅) (G₄ := ∅) hp₁ hp₂ hW a ah b bh
      (disjoint_empty_right _) (disjoint_empty_left _)
      (by
        rw [union_empty]
        exact hah.mono (by exact_mod_cast hB))
      (by simp)
      (by simpa using hfB) (by simp) (by simp)
    simp only [prod_empty, mul_one] at h
    refine le_trans (le_of_eq ?_) h
    refine sum_congr rfl fun τ₁ _ => ?_
    congr 1
    refine sum_congr rfl fun τ₂ _ => ?_
    congr 1
    exact sum_prod_window (fun t y => W (τ₁ (a t), τ₂ (b t)) y) (fun t => (hW _).sum_eq_one) B _
  have h1 := hpart A₁ hsub₁ hf₁
  have h2 := hpart A₂ hsub₂ hf₂
  set c := exp (-(A / 2)) with hc
  have hc0 : 0 < c := exp_pos _
  -- For fixed outputs, the indicator is bounded by the arithmetic mean of the two products.
  have hind : ∀ (τ₁ : L₁ → α₁) (τ₂ : L₂ → α₂) (y : T → β),
      (if exp A ≤ ∏ t ∈ G, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) then (1 : ℝ) else 0) ≤
      c / 2 * ((∏ t ∈ A₁, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) +
        ∏ t ∈ A₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) := by
    intro τ₁ τ₂ y
    set u := ∏ t ∈ A₁, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)
    set v := ∏ t ∈ A₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)
    have hu : 0 ≤ u := prod_nonneg fun t _ => infoRatio_nonneg hp₁ (fun a => hW (a, _)) _ _
    have hv : 0 ≤ v := prod_nonneg fun t _ => infoRatio_nonneg hp₁ (fun a => hW (a, _)) _ _
    have hprod : ∏ t ∈ G, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t) = u * v := by
      rw [← hG, prod_union hd]
    rw [hprod]
    split_ifs with hpass
    · -- `e^{A/2} ≤ √(uv) ≤ (u + v) / 2`.
      have hs : exp (A / 2) * exp (A / 2) = exp A := by
        rw [← exp_add]
        congr 1
        ring
      have h3 : exp (A / 2) * exp (A / 2) ≤ u * v := hs ▸ hpass
      have h4 : 2 * exp (A / 2) ≤ u + v := by
        have hE := exp_pos (A / 2)
        nlinarith [sq_nonneg (u - v), sq_nonneg (u + v - 2 * exp (A / 2))]
      have h5 : c * exp (A / 2) = 1 := by
        rw [hc, ← exp_add]
        simp
      calc (1 : ℝ) = c / 2 * (2 * exp (A / 2)) := by
            rw [← h5]
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
    · positivity
  calc _ ≤ ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
        (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
        (c / 2 * ((∏ t ∈ A₁, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) +
          ∏ t ∈ A₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t))) :=
        sum_le_sum fun τ₁ _ => mul_le_mul_of_nonneg_left
          (sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left
            (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hind τ₁ τ₂ y)
              (prod_nonneg fun t _ => (hW _).nonneg _)) (tableLaw_nonneg hp₂ τ₂))
          (tableLaw_nonneg hp₁ τ₁)
    _ = c / 2 * ((∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
          (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
          ∏ t ∈ A₁, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) +
        ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
          (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
          ∏ t ∈ A₂, macRatio₁ p₁ W (τ₁ (ah t)) (τ₂ (bh t)) (y t)) := by
        rw [← sum_add_distrib, mul_sum]
        refine sum_congr rfl fun τ₁ _ => ?_
        rw [← mul_add, mul_left_comm]
        congr 1
        rw [← sum_add_distrib, mul_sum]
        refine sum_congr rfl fun τ₂ _ => ?_
        rw [← mul_add, mul_left_comm]
        congr 1
        rw [← sum_add_distrib, mul_sum]
        exact sum_congr rfl fun y _ => by ring
    _ ≤ c / 2 * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = c := by ring

/-- **The true messages fail a test only with small probability.** For any density `r` positive on
the support of the joint law, the product of the densities over `G` falls below `e^A` with
probability at most `e^{λ A} M^{|G|}`, where `M` is the expectation of `r^{-λ}` at one slot. -/
theorem sum_tables_fail_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (a : T → L₁)
    (b : T → L₂) {G : Finset T} (ha : Set.InjOn a (G : Finset T)) (hb : Set.InjOn b (G : Finset T))
    (r : α₁ → α₂ → β → ℝ)
    (hr : ∀ x₁ x₂ y, 0 < p₁ x₁ → 0 < p₂ x₂ → 0 < W (x₁, x₂) y → 0 < r x₁ x₂ y) {l : ℝ} (hl : 0 ≤ l)
    (A : ℝ) :
    ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ y : T → β,
      (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
      (if ∏ t ∈ G, r (τ₁ (a t)) (τ₂ (b t)) (y t) < exp A then 1 else 0) ≤
      exp (l * A) * (∑ x₁, p₁ x₁ * ∑ x₂, p₂ x₂ * ∑ y, W (x₁, x₂) y * exp (-(l * log (r x₁ x₂ y)))) ^
        G.card := by
  classical
  set K : α₁ → α₂ → ℝ := fun x₁ x₂ => ∑ y, W (x₁, x₂) y * exp (-(l * log (r x₁ x₂ y))) with hK
  have hK0 : ∀ x₁ x₂, 0 ≤ K x₁ x₂ := fun x₁ x₂ =>
    sum_nonneg fun y _ => mul_nonneg ((hW _).nonneg y) (exp_pos _).le
  set K₂ : α₂ → ℝ := fun x₂ => ∑ x₁, p₁ x₁ * K x₁ x₂ with hK₂
  have hK₂0 : ∀ x₂, 0 ≤ K₂ x₂ := fun x₂ =>
    sum_nonneg fun x₁ _ => mul_nonneg (hp₁.nonneg _) (hK0 _ _)
  set M := ∑ x₁, p₁ x₁ * ∑ x₂, p₂ x₂ * K x₁ x₂ with hM
  have hM0 : 0 ≤ M := sum_nonneg fun x₁ _ => mul_nonneg (hp₁.nonneg _)
    (sum_nonneg fun x₂ _ => mul_nonneg (hp₂.nonneg _) (hK0 _ _))
  have hMeq : M = ∑ x₂, p₂ x₂ * K₂ x₂ := by
    simp only [hM, hK₂, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun x₂ _ => sum_congr rfl fun x₁ _ => by ring
  -- The indicator is bounded on the support of the law.
  have hpt : ∀ (τ₁ : L₁ → α₁) (τ₂ : L₂ → α₂) (y : T → β),
      tableLaw p₁ τ₁ * (tableLaw p₂ τ₂ * ((∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
      (if ∏ t ∈ G, r (τ₁ (a t)) (τ₂ (b t)) (y t) < exp A then 1 else 0))) ≤
      tableLaw p₁ τ₁ * (tableLaw p₂ τ₂ * ((∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
        (exp (l * A) * ∏ t ∈ G, exp (-(l * log (r (τ₁ (a t)) (τ₂ (b t)) (y t))))))) := by
    intro τ₁ τ₂ y
    have hw₁ := tableLaw_nonneg hp₁ τ₁
    have hw₂ := tableLaw_nonneg hp₂ τ₂
    have hY : 0 ≤ ∏ t, W (τ₁ (a t), τ₂ (b t)) (y t) := prod_nonneg fun t _ => (hW _).nonneg _
    have hE : 0 ≤ exp (l * A) * ∏ t ∈ G, exp (-(l * log (r (τ₁ (a t)) (τ₂ (b t)) (y t)))) :=
      mul_nonneg (exp_pos _).le (prod_nonneg fun t _ => (exp_pos _).le)
    by_cases hpos : 0 < tableLaw p₁ τ₁ ∧ 0 < tableLaw p₂ τ₂ ∧
        0 < ∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)
    · obtain ⟨h1, h2, h3⟩ := hpos
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ?_ hY) hw₂) hw₁
      split_ifs with hlt
      · -- All the densities are positive.
        have hrp : ∀ t ∈ G, 0 < r (τ₁ (a t)) (τ₂ (b t)) (y t) := by
          intro t _
          have e1 : 0 < p₁ (τ₁ (a t)) := lt_of_le_of_ne (hp₁.nonneg _) fun h =>
            h1.ne' (prod_eq_zero (mem_univ (a t)) h.symm)
          have e2 : 0 < p₂ (τ₂ (b t)) := lt_of_le_of_ne (hp₂.nonneg _) fun h =>
            h2.ne' (prod_eq_zero (mem_univ (b t)) h.symm)
          have e3 : 0 < W (τ₁ (a t), τ₂ (b t)) (y t) := lt_of_le_of_ne ((hW _).nonneg _) fun h =>
            h3.ne' (prod_eq_zero (mem_univ t) h.symm)
          exact hr _ _ _ e1 e2 e3
        have hlog : ∑ t ∈ G, log (r (τ₁ (a t)) (τ₂ (b t)) (y t)) < A := by
          rw [← Real.log_prod fun t ht => (hrp t ht).ne']
          exact (Real.log_lt_iff_lt_exp (prod_pos hrp)).2 hlt
        rw [← exp_sum, ← exp_add]
        refine one_le_exp ?_
        rw [sum_neg_distrib, ← mul_sum]
        nlinarith
      · exact hE
    · -- Off the support both sides vanish.
      have h0 : tableLaw p₁ τ₁ = 0 ∨ tableLaw p₂ τ₂ = 0 ∨ ∏ t, W (τ₁ (a t), τ₂ (b t)) (y t) = 0 :=
        by
        by_contra hcon
        push Not at hcon
        exact hpos ⟨lt_of_le_of_ne hw₁ (Ne.symm hcon.1), lt_of_le_of_ne hw₂ (Ne.symm hcon.2.1),
          lt_of_le_of_ne hY (Ne.symm hcon.2.2)⟩
      rcases h0 with h0 | h0 | h0 <;> simp [h0]
  -- Integrate the entries of sender 1, then those of sender 2.
  have hA : ∀ τ₂ : L₂ → α₂, ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ *
      ∏ t ∈ G, K (τ₁ (a t)) (τ₂ (b t)) ≤ ∏ t ∈ G, K₂ (τ₂ (b t)) := by
    intro τ₂
    have hT := sum_tableLaw_prod_le hp₁ G a ha (fun _ => 1)
      (fun t τ₁ => K (τ₁ (a t)) (τ₂ (b t))) (fun t _ => K₂ (τ₂ (b t))) (fun _ => zero_le_one)
      (fun _ _ _ _ => rfl) (fun _ _ _ => hK0 _ _) (fun _ _ _ => hK₂0 _)
      (fun t ht t' ht' hn τ₁ x => by
        have h1 : a t ≠ a t' := fun he => hn (ha (by exact_mod_cast ht') (by exact_mod_cast ht)
          he.symm)
        simp only [Function.update_of_ne h1])
      (fun _ _ _ _ _ _ => rfl)
      (fun t _ τ₁ => by simp [hK₂])
    simp only [one_mul] at hT
    rw [sum_congr rfl fun τ₁ _ => mul_comm (tableLaw p₁ τ₁) _] at hT
    rw [← sum_mul, sum_tableLaw hp₁, one_mul] at hT
    simpa only [mul_comm] using hT
  have hB : ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∏ t ∈ G, K₂ (τ₂ (b t)) ≤ M ^ G.card := by
    have hT := sum_tableLaw_prod_le hp₂ G b hb (fun _ => 1)
      (fun t τ₂ => K₂ (τ₂ (b t))) (fun _ _ => M) (fun _ => zero_le_one)
      (fun _ _ _ _ => rfl) (fun _ _ _ => hK₂0 _) (fun _ _ _ => hM0)
      (fun t ht t' ht' hn τ₂ x => by
        have h1 : b t ≠ b t' := fun he => hn (hb (by exact_mod_cast ht') (by exact_mod_cast ht)
          he.symm)
        simp only [Function.update_of_ne h1])
      (fun _ _ _ _ _ _ => rfl)
      (fun t _ τ₂ => by simp [hMeq])
    simp only [one_mul, prod_const] at hT
    rw [← sum_mul, sum_tableLaw hp₂, one_mul] at hT
    exact hT
  have hE0 : 0 ≤ exp (l * A) := (exp_pos _).le
  calc _ = ∑ τ₁ : L₁ → α₁, ∑ τ₂ : L₂ → α₂, ∑ y : T → β,
        tableLaw p₁ τ₁ * (tableLaw p₂ τ₂ * ((∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
        (if ∏ t ∈ G, r (τ₁ (a t)) (τ₂ (b t)) (y t) < exp A then 1 else 0))) := by
        simp only [mul_sum]
    _ ≤ ∑ τ₁ : L₁ → α₁, ∑ τ₂ : L₂ → α₂, ∑ y : T → β,
        tableLaw p₁ τ₁ * (tableLaw p₂ τ₂ * ((∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
        (exp (l * A) * ∏ t ∈ G, exp (-(l * log (r (τ₁ (a t)) (τ₂ (b t)) (y t))))))) :=
        sum_le_sum fun τ₁ _ => sum_le_sum fun τ₂ _ => sum_le_sum fun y _ => hpt τ₁ τ₂ y
    _ = exp (l * A) * ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∑ τ₁ : L₁ → α₁, tableLaw p₁ τ₁ *
        ∏ t ∈ G, K (τ₁ (a t)) (τ₂ (b t)) := by
        have hwin : ∀ (τ₁ : L₁ → α₁) (τ₂ : L₂ → α₂), ∑ y : T → β,
            (∏ t, W (τ₁ (a t), τ₂ (b t)) (y t)) *
            ∏ t ∈ G, exp (-(l * log (r (τ₁ (a t)) (τ₂ (b t)) (y t)))) =
            ∏ t ∈ G, K (τ₁ (a t)) (τ₂ (b t)) := fun τ₁ τ₂ =>
          sum_prod_window (fun t y => W (τ₁ (a t), τ₂ (b t)) y) (fun t => (hW _).sum_eq_one) G
            (fun t y => exp (-(l * log (r (τ₁ (a t)) (τ₂ (b t)) y))))
        simp only [← hwin, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun τ₂ _ => sum_congr rfl fun τ₁ _ => sum_congr rfl fun y _ => ?_
        ring
    _ ≤ exp (l * A) * M ^ G.card := by
        refine mul_le_mul_of_nonneg_left ?_ hE0
        calc _ ≤ ∑ τ₂ : L₂ → α₂, tableLaw p₂ τ₂ * ∏ t ∈ G, K₂ (τ₂ (b t)) :=
              sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left (hA τ₂) (tableLaw_nonneg hp₂ τ₂)
          _ ≤ _ := hB

/-- **The Chernoff bound for one slot.** For small `l > 0`, the expectation of `e^{-l f}` is at most
`e^{-l (E f - c)}`. -/
theorem exists_chernoff {Z : Type*} [Fintype Z] {μ : Z → ℝ} (hμ : IsPMF μ) (f : Z → ℝ) {c : ℝ}
    (hc : 0 < c) : ∃ l > 0, ∑ z, μ z * exp (-(l * f z)) ≤ exp (-(l * (∑ z, μ z * f z - c))) := by
  set B := ∑ z, |f z| + 1 with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ z, |f z| := sum_nonneg fun z _ => abs_nonneg _
    linarith
  have hfB : ∀ z, |f z| ≤ B := fun z => by
    have := single_le_sum (f := fun z => |f z|) (fun z _ => abs_nonneg _) (mem_univ z)
    linarith
  set l := min (1 / B) (c / B ^ 2) with hl
  have hl0 : 0 < l := lt_min (by positivity) (by positivity)
  have hl1 : l * B ≤ 1 := by
    calc l * B ≤ 1 / B * B := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = 1 := by field_simp
  have hl2 : l * B ^ 2 ≤ c := by
    calc l * B ^ 2 ≤ c / B ^ 2 * B ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = c := by field_simp
  refine ⟨l, hl0, ?_⟩
  have hpt : ∀ z, exp (-(l * f z)) ≤ 1 - l * f z + l ^ 2 * B ^ 2 := by
    intro z
    have h1 : |-(l * f z)| ≤ 1 := by
      rw [abs_neg, abs_mul, abs_of_pos hl0]
      exact (mul_le_mul_of_nonneg_left (hfB z) hl0.le).trans hl1
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have h3 := (abs_le.1 h2).2
    have h4 : (-(l * f z)) ^ 2 ≤ l ^ 2 * B ^ 2 := by
      rw [neg_sq, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact sq_le_sq' (by linarith [(abs_le.1 (hfB z)).1]) (abs_le.1 (hfB z)).2
    linarith
  calc ∑ z, μ z * exp (-(l * f z)) ≤ ∑ z, μ z * (1 - l * f z + l ^ 2 * B ^ 2) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (hμ.nonneg z)
    _ = 1 - l * ∑ z, μ z * f z + l ^ 2 * B ^ 2 := by
        have : ∀ z, μ z * (1 - l * f z + l ^ 2 * B ^ 2) =
            μ z * (1 + l ^ 2 * B ^ 2) - l * (μ z * f z) := fun z => by ring
        simp only [this]
        rw [sum_sub_distrib, ← sum_mul, hμ.sum_eq_one, ← mul_sum]
        ring
    _ ≤ 1 + -(l * (∑ z, μ z * f z - c)) := by nlinarith
    _ ≤ _ := by
        have := add_one_le_exp (-(l * (∑ z, μ z * f z - c)))
        linarith

end Fresh


end InfoTheory
