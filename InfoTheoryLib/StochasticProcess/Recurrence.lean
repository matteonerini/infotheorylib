/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StochasticProcess.Basic

/-!
# Recurrence times and Kac's lemma

For a stationary process and a symbol `u` with `p(u) > 0`, let `Q_u(i)` be the probability that,
given `X₀ = u`, the next occurrence of `u` is at time `i`. Kac's lemma states that the mean
recurrence time is `∑ᵢ i Q_u(i) = 1/p(u)`, as soon as `u` recurs with probability one (for
instance, for an ergodic process). Applied to the process of blocks
`Uᵢ = (Xᵢ, …, Xᵢ₊ₙ₋₁)`, it gives the mean recurrence time `1/p(xⁿ)` of a block, the basis of the
optimality of the sliding window Lempel–Ziv algorithm.

## Main definitions

* `StochasticProcess.noVisitProb P u m`: `Pr{X₀ ≠ u, …, X_{m-1} ≠ u}`.
* `StochasticProcess.visitNoReturnProb P u m`: `Pr{X₀ = u, X₁ ≠ u, …, X_m ≠ u}`.
* `StochasticProcess.firstReturnProb P u m`: `Pr{X₀ = u, X₁ ≠ u, …, X_m ≠ u, X_{m+1} = u}`, that
  is `p(u) Q_u(m + 1)`.
* `StochasticProcess.IsRecurrent P u`: `u` occurs eventually with probability one.
* `StochasticProcess.blocks P n`: the process of blocks `Uᵢ = (Xᵢ, …, Xᵢ₊ₙ₋₁)`.

## Main statements

* `StochasticProcess.sum_range_mul_firstReturnProb`: the finite form of Kac's identity,
  `∑_{i ≤ N} i p(u) Q_u(i) = 1 - Pr{u ∉ X₀ⁿ⁻¹} - N Pr{X₀ = u, u ∉ X₁ᴺ}`.
* `StochasticProcess.sum_range_mul_firstReturnProb_le`: `∑ᵢ i Q_u(i) ≤ 1/p(u)` always.
* `StochasticProcess.hasSum_firstReturnProb`: Poincaré recurrence, the recurrence time is finite
  with probability one.
* `StochasticProcess.hasSum_mul_firstReturnProb`: **Lemma 13.5.2 (Kac)**, `∑ᵢ i Q_u(i) = 1/p(u)`
  for a recurrent symbol.
* `StochasticProcess.blocks_isStationary`, `StochasticProcess.blocks_law_one`: the block process
  is stationary and its one-dimensional law is the law of `Xⁿ`, so Kac's lemma gives the
  **Corollary (13.73)**.

## Implementation notes

Processes are given by their finite-dimensional laws on the time set `{0, 1, 2, …}`. The book
looks backward from time `0` to the last occurrence of `u`; by stationarity this is the same as
looking forward from an occurrence of `u` at time `0` to the next one, which is what we do.
Ergodicity is not available in this setting: we assume instead that `u` recurs with probability
one, `Pr{X₀ ≠ u, …, X_{m-1} ≠ u} → 0`, which holds for an ergodic process.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 13.5.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

namespace StochasticProcess

variable {α : Type*} [Fintype α] [DecidableEq α] (P : StochasticProcess α) (u : α)

/-! ### Return probabilities -/

/-- `Pr{X₀ ≠ u, …, X_{m-1} ≠ u}`. -/
def noVisitProb (m : ℕ) : ℝ := ∑ x : Fin m → α, if ∀ i, x i ≠ u then P.law m x else 0

/-- `Pr{X₀ = u, X₁ ≠ u, …, X_m ≠ u}`. -/
def visitNoReturnProb (m : ℕ) : ℝ :=
  ∑ x : Fin (m + 1) → α, if x 0 = u ∧ ∀ i : Fin m, x i.succ ≠ u then P.law (m + 1) x else 0

/-- `Pr{X₀ = u, X₁ ≠ u, …, X_m ≠ u, X_{m+1} = u}`: the first return to `u` after time `0` is at
time `m + 1`. This is `p(u) Q_u(m + 1)`. -/
def firstReturnProb (m : ℕ) : ℝ :=
  ∑ x : Fin (m + 2) → α,
    if x 0 = u ∧ (∀ i : Fin m, x i.succ.castSucc ≠ u) ∧ x (Fin.last (m + 1)) = u then
      P.law (m + 2) x else 0

/-- **(13.62)** The recurrence time distribution `Q_u(i)`, `i ≥ 1`, conditional on `X₀ = u`. -/
def recurrenceDist (i : ℕ) : ℝ := firstReturnProb P u (i - 1) / P.law 1 (fun _ => u)

/-- The symbol `u` recurs with probability one: `Pr{X₀ ≠ u, …, X_{m-1} ≠ u} → 0`. -/
def IsRecurrent : Prop := Tendsto (noVisitProb P u) atTop (𝓝 0)

lemma noVisitProb_nonneg (m : ℕ) : 0 ≤ noVisitProb P u m :=
  sum_nonneg fun x _ => by split_ifs <;> simp [(P.isPMF m).nonneg x]

lemma visitNoReturnProb_nonneg (m : ℕ) : 0 ≤ visitNoReturnProb P u m :=
  sum_nonneg fun x _ => by split_ifs <;> simp [(P.isPMF _).nonneg x]

lemma firstReturnProb_nonneg (m : ℕ) : 0 ≤ firstReturnProb P u m :=
  sum_nonneg fun x _ => by split_ifs <;> simp [(P.isPMF _).nonneg x]

lemma noVisitProb_zero : noVisitProb P u 0 = 1 := by
  have h := (P.isPMF 0).sum_eq_one
  simp only [noVisitProb, IsEmpty.forall_iff, ite_true]
  exact h

/-- `Pr{X₀ = u, (no further condition)} = p(u)`. -/
lemma visitNoReturnProb_zero : visitNoReturnProb P u 0 = P.law 1 (fun _ => u) := by
  rw [visitNoReturnProb]
  have : ∀ x : Fin 1 → α, (x 0 = u ∧ ∀ i : Fin 0, x i.succ ≠ u) ↔ x = fun _ => u := fun x => by
    simp only [IsEmpty.forall_iff, and_true]
    exact ⟨fun h => funext fun i => by rw [Subsingleton.elim i 0, h], fun h => by rw [h]⟩
  simp only [this, sum_ite_eq', mem_univ, ite_true]

variable {P}

/-- By stationarity, `Pr{X₁ ≠ u, …, X_m ≠ u} = Pr{X₀ = u, X₁ ≠ u, …} + Pr{X₀ ≠ u, X₁ ≠ u, …}`. -/
lemma noVisitProb_eq (hP : P.IsStationary) (m : ℕ) :
    noVisitProb P u m = visitNoReturnProb P u m + noVisitProb P u (m + 1) := by
  have h1 : noVisitProb P u m = ∑ x : Fin (m + 1) → α,
      if ∀ i : Fin m, x i.succ ≠ u then P.law (m + 1) x else 0 := by
    rw [noVisitProb, sum_cons, sum_comm]
    refine sum_congr rfl fun y _ => ?_
    simp only [Fin.cons_succ]
    split_ifs
    · exact (hP m y).symm
    · simp
  rw [h1, visitNoReturnProb, noVisitProb, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  simp only [Fin.forall_fin_succ]
  by_cases h0 : x 0 = u <;> by_cases hs : ∀ i : Fin m, x i.succ ≠ u <;> simp [h0, hs]

/-- By consistency, `Pr{X₀ = u, X₁ ≠ u, …, X_m ≠ u} = p(u) Q_u(m + 1) + Pr{X₀ = u, X₁ ≠ u, …,
X_{m+1} ≠ u}`. -/
lemma visitNoReturnProb_eq (m : ℕ) :
    visitNoReturnProb P u m = firstReturnProb P u m + visitNoReturnProb P u (m + 1) := by
  have h1 : visitNoReturnProb P u m = ∑ x : Fin (m + 2) → α,
      if x 0 = u ∧ ∀ i : Fin m, x i.succ.castSucc ≠ u then P.law (m + 2) x else 0 := by
    rw [visitNoReturnProb]
    conv_rhs => rw [sum_snoc]
    refine sum_congr rfl fun y _ => ?_
    have e : ∀ a, (Fin.snoc y a : Fin (m + 2) → α) 0 = y 0 := fun a => by
      rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc from rfl, Fin.snoc_castSucc]
    have e' : ∀ a (i : Fin m), (Fin.snoc y a : Fin (m + 2) → α) i.succ.castSucc = y i.succ :=
      fun a i => Fin.snoc_castSucc _ _ _
    simp only [e, e']
    split_ifs
    · exact (P.consistent _ y).symm
    · simp
  rw [h1, firstReturnProb, visitNoReturnProb, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  have hsplit : (∀ i : Fin (m + 1), x i.succ ≠ u) ↔
      (∀ i : Fin m, x i.succ.castSucc ≠ u) ∧ x (Fin.last (m + 1)) ≠ u := by
    rw [Fin.forall_fin_succ']
    simp only [Fin.succ_castSucc, Fin.succ_last]
  simp only [hsplit]
  by_cases h0 : x 0 = u <;> by_cases hl : x (Fin.last (m + 1)) = u <;> simp [h0, hl]

/-- `p(u) Q_u(m + 1) ≤ p(u)`. -/
lemma firstReturnProb_le (m : ℕ) : firstReturnProb P u m ≤ P.law 1 (fun _ => u) := by
  rw [← visitNoReturnProb_zero]
  have h : ∀ k, firstReturnProb P u m ≤ visitNoReturnProb P u (m - k) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.sub_zero, visitNoReturnProb_eq u m]
      linarith [visitNoReturnProb_nonneg P u (m + 1)]
    | succ k ih =>
      rcases Nat.lt_or_ge k m with hk | hk
      · have e : m - k = (m - (k + 1)) + 1 := by omega
        rw [e] at ih
        refine ih.trans ?_
        rw [visitNoReturnProb_eq u (m - (k + 1))]
        linarith [firstReturnProb_nonneg P u (m - (k + 1))]
      · rw [show m - (k + 1) = m - k by omega]
        exact ih
  simpa using h m

/-! ### Kac's lemma -/

/-- `∑_{m < N} Pr{X₀ = u, X₁ ≠ u, …, X_m ≠ u} = 1 - Pr{X₀ ≠ u, …, X_{N-1} ≠ u}`. -/
lemma sum_range_visitNoReturnProb (hP : P.IsStationary) (N : ℕ) :
    ∑ m ∈ range N, visitNoReturnProb P u m = 1 - noVisitProb P u N := by
  induction N with
  | zero => simp [noVisitProb_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, noVisitProb_eq u hP N]
    ring

/-- **Kac's identity, finite form.** `∑_{i ≤ N} i p(u) Q_u(i) = 1 - Pr{X₀ ≠ u, …, X_{N-1} ≠ u} -
N Pr{X₀ = u, X₁ ≠ u, …, X_N ≠ u}`. -/
theorem sum_range_mul_firstReturnProb (hP : P.IsStationary) (N : ℕ) :
    ∑ m ∈ range N, ((m : ℝ) + 1) * firstReturnProb P u m =
      1 - noVisitProb P u N - N * visitNoReturnProb P u N := by
  induction N with
  | zero => simp [noVisitProb_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, noVisitProb_eq u hP N, visitNoReturnProb_eq u N]
    push_cast
    ring

/-- The mean recurrence time is at most `1/p(u)`: `∑_{i ≤ N} i p(u) Q_u(i) ≤ 1`. -/
theorem sum_range_mul_firstReturnProb_le (hP : P.IsStationary) (N : ℕ) :
    ∑ m ∈ range N, ((m : ℝ) + 1) * firstReturnProb P u m ≤ 1 := by
  rw [sum_range_mul_firstReturnProb u hP]
  have := noVisitProb_nonneg P u N
  have := visitNoReturnProb_nonneg P u N
  have : (0 : ℝ) ≤ N * visitNoReturnProb P u N := by positivity
  linarith

lemma summable_visitNoReturnProb (hP : P.IsStationary) : Summable (visitNoReturnProb P u) :=
  summable_of_sum_range_le (c := 1) (visitNoReturnProb_nonneg P u) fun N => by
    rw [sum_range_visitNoReturnProb u hP]
    linarith [noVisitProb_nonneg P u N]

lemma tendsto_visitNoReturnProb (hP : P.IsStationary) :
    Tendsto (visitNoReturnProb P u) atTop (𝓝 0) :=
  (summable_visitNoReturnProb u hP).tendsto_atTop_zero

/-- **Poincaré recurrence.** For a stationary process, a visit to `u` is followed by a return
with probability one: `∑ᵢ p(u) Q_u(i) = p(u)`. -/
theorem hasSum_firstReturnProb (hP : P.IsStationary) :
    HasSum (firstReturnProb P u) (P.law 1 fun _ => u) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (firstReturnProb_nonneg P u)]
  have h : ∀ N, ∑ m ∈ range N, firstReturnProb P u m =
      P.law 1 (fun _ => u) - visitNoReturnProb P u N := fun N => by
    induction N with
    | zero => simp [visitNoReturnProb_zero]
    | succ N ih =>
      rw [sum_range_succ, ih, visitNoReturnProb_eq u N]
      ring
  simp only [h]
  simpa using tendsto_const_nhds.sub (tendsto_visitNoReturnProb u hP)

/-- **Lemma 13.5.2 (Kac), (13.63).** If `u` recurs with probability one, the mean recurrence time
is `∑ᵢ i Q_u(i) = 1/p(u)`: `∑ᵢ i p(u) Q_u(i) = 1`. -/
theorem hasSum_mul_firstReturnProb (hP : P.IsStationary) (hu : IsRecurrent P u) :
    HasSum (fun m : ℕ => ((m : ℝ) + 1) * firstReturnProb P u m) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg fun m => mul_nonneg (by positivity)
    (firstReturnProb_nonneg P u m)]
  -- `Aₙ = ∑_{j < N} (h_j - h_N)`, where `h_j = Pr{X₀ = u, X₁ ≠ u, …, X_j ≠ u}`.
  set h := visitNoReturnProb P u
  have hA : ∀ N, ∑ m ∈ range N, ((m : ℝ) + 1) * firstReturnProb P u m =
      ∑ j ∈ range N, (h j - h N) := fun N => by
    rw [sum_range_mul_firstReturnProb u hP, sum_sub_distrib, sum_const, card_range,
      nsmul_eq_mul, sum_range_visitNoReturnProb u hP]
  have hanti : Antitone h := antitone_nat_of_succ_le fun m => by
    change visitNoReturnProb P u (m + 1) ≤ visitNoReturnProb P u m
    rw [visitNoReturnProb_eq u m]
    linarith [firstReturnProb_nonneg P u m]
  have hsum : Tendsto (fun N => ∑ j ∈ range N, h j) atTop (𝓝 1) := by
    simp only [h, sum_range_visitNoReturnProb u hP]
    simpa using tendsto_const_nhds.sub hu
  have hle : ∀ N, ∑ m ∈ range N, ((m : ℝ) + 1) * firstReturnProb P u m ≤ 1 :=
    sum_range_mul_firstReturnProb_le u hP
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun N => (hle N).trans_lt ha⟩
  -- Choose `J` with `∑_{j < J} h_j > (1 + a)/2`, then `N ≥ J` with `J h_N < (1 - a)/2`.
  obtain ⟨J, hJ⟩ := ((tendsto_order.1 hsum).1 ((1 + a) / 2) (by linarith)).exists
  have hJN : ∀ᶠ N in atTop, (J : ℝ) * h N < (1 - a) / 2 := by
    have := (tendsto_visitNoReturnProb u hP).const_mul (J : ℝ)
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 _ (by linarith)
  filter_upwards [hJN, eventually_ge_atTop J] with N hN hNJ
  rw [hA]
  have hmono : ∑ j ∈ range J, (h j - h N) ≤ ∑ j ∈ range N, (h j - h N) :=
    sum_le_sum_of_subset_of_nonneg (range_mono hNJ) fun j _ _ => by
      have : h N ≤ h j := hanti (by
        have := mem_range.1 ‹j ∈ range N›
        omega)
      linarith
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hmono
  linarith

/-! ### The process of blocks -/

variable (P)

/-- Whether the blocks `u₀, …, u_{m-1}` are the windows `(yᵢ, …, yᵢ₊ₙ₋₁)` of the string `y`. -/
def IsBlocksOf {n m : ℕ} (b : Fin m → Fin n → α) (y : Fin (n + m) → α) : Prop :=
  ∀ (i : Fin m) (j : Fin n), b i j = y ⟨i + j, by omega⟩

instance {n m : ℕ} (b : Fin m → Fin n → α) (y : Fin (n + m) → α) :
    Decidable (IsBlocksOf b y) := by
  unfold IsBlocksOf; infer_instance

/-- The windows of `y`. -/
def blocksOf {n m : ℕ} (y : Fin (n + m) → α) : Fin m → Fin n → α := fun i j => y ⟨i + j, by omega⟩

omit [Fintype α] [DecidableEq α] in
lemma isBlocksOf_iff {n m : ℕ} (b : Fin m → Fin n → α) (y : Fin (n + m) → α) :
    IsBlocksOf b y ↔ b = blocksOf y := by
  constructor
  · intro h
    funext i j
    exact h i j
  · rintro rfl i j
    rfl

/-- The law of `(U₀, …, U_{m-1})`, `Uᵢ = (Xᵢ, …, Xᵢ₊ₙ₋₁)`, as a law on `n + m` symbols. -/
def blocksLaw (n m : ℕ) (b : Fin m → Fin n → α) : ℝ :=
  ∑ y : Fin (n + m) → α, if IsBlocksOf b y then P.law (n + m) y else 0

lemma blocksLaw_isPMF (n m : ℕ) : IsPMF (blocksLaw P n m) := by
  refine ⟨fun b => sum_nonneg fun y _ => by split_ifs <;> simp [(P.isPMF _).nonneg y], ?_⟩
  unfold blocksLaw
  rw [sum_comm]
  simp only [isBlocksOf_iff, sum_ite_eq', mem_univ, ite_true]
  exact (P.isPMF _).sum_eq_one

omit [Fintype α] [DecidableEq α] in
lemma isBlocksOf_snoc {n m : ℕ} (b : Fin m → Fin n → α) (a : Fin n → α)
    (y : Fin (n + m) → α) (c : α) :
    IsBlocksOf (Fin.snoc b a : Fin (m + 1) → Fin n → α) (Fin.snoc y c : Fin (n + m + 1) → α) ↔
      IsBlocksOf b y ∧
        a = fun j : Fin n => (Fin.snoc y c : Fin (n + m + 1) → α) ⟨m + j, by omega⟩ := by
  rw [IsBlocksOf, Fin.forall_fin_succ', IsBlocksOf, funext_iff]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  refine and_congr (forall_congr' fun i => forall_congr' fun j => ?_) Iff.rfl
  rw [show (⟨i + j, by omega⟩ : Fin (n + m + 1)) = (⟨i + j, by omega⟩ : Fin (n + m)).castSucc
    from rfl, Fin.snoc_castSucc]

omit [Fintype α] [DecidableEq α] in
lemma isBlocksOf_cons {n m : ℕ} (a : Fin n → α) (b : Fin m → Fin n → α) (c : α)
    (y : Fin (n + m) → α) :
    IsBlocksOf (Fin.cons a b : Fin (m + 1) → Fin n → α) (Fin.cons c y : Fin (n + m + 1) → α) ↔
      IsBlocksOf b y ∧
        (a = fun j : Fin n => (Fin.cons c y : Fin (n + m + 1) → α) ⟨j, by omega⟩) := by
  rw [IsBlocksOf, Fin.forall_fin_succ, IsBlocksOf, funext_iff, and_comm]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, zero_add, Fin.val_succ]
  refine and_congr (forall_congr' fun i => forall_congr' fun j => ?_) Iff.rfl
  rw [show (⟨i + 1 + j, by omega⟩ : Fin (n + m + 1)) = (⟨i + j, by omega⟩ : Fin (n + m)).succ
    from Fin.ext (by simp; omega), Fin.cons_succ]

lemma blocksLaw_consistent (n m : ℕ) (b : Fin m → Fin n → α) :
    ∑ a, blocksLaw P n (m + 1) (Fin.snoc b a) = blocksLaw P n m b := by
  unfold blocksLaw
  rw [sum_comm]
  change ∑ y : Fin (n + m + 1) → α, _ = _
  rw [sum_snoc]
  refine sum_congr rfl fun y _ => ?_
  simp only [isBlocksOf_snoc, ite_and]
  split_ifs
  · simp only [sum_ite_eq', mem_univ, ite_true]
    exact P.consistent _ y
  · simp

lemma blocksLaw_stationary (hP : P.IsStationary) (n m : ℕ) (b : Fin m → Fin n → α) :
    ∑ a, blocksLaw P n (m + 1) (Fin.cons a b) = blocksLaw P n m b := by
  unfold blocksLaw
  rw [sum_comm]
  change ∑ y : Fin (n + m + 1) → α, _ = _
  rw [sum_cons, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  simp only [isBlocksOf_cons, ite_and]
  split_ifs
  · simp only [sum_ite_eq', mem_univ, ite_true]
    exact hP _ y
  · simp

/-- **The process of blocks** `Uᵢ = (Xᵢ, …, Xᵢ₊ₙ₋₁)`. -/
def blocks (n : ℕ) : StochasticProcess (Fin n → α) where
  law := blocksLaw P n
  isPMF := blocksLaw_isPMF P n
  consistent m b := blocksLaw_consistent P n m b

/-- The block process of a stationary process is stationary. -/
theorem blocks_isStationary (hP : P.IsStationary) (n : ℕ) : (P.blocks n).IsStationary :=
  fun m b => blocksLaw_stationary P hP n m b

/-- The one-dimensional law of the block process is the law of `Xⁿ`: `Pr{U₀ = xⁿ} = p(xⁿ)`. -/
theorem blocks_law_one (n : ℕ) (x : Fin n → α) : (P.blocks n).law 1 (fun _ => x) = P.law n x := by
  change blocksLaw P n 1 (fun _ => x) = P.law n x
  have hcond : ∀ (y : Fin n → α) c,
      IsBlocksOf (fun _ : Fin 1 => x) (Fin.snoc y c : Fin (n + 1) → α) ↔ x = y := fun y c => by
    rw [IsBlocksOf, Fin.forall_fin_one, funext_iff]
    refine forall_congr' fun j => ?_
    rw [show (⟨((0 : Fin 1) : ℕ) + j, by omega⟩ : Fin (n + 1)) = j.castSucc from
      Fin.ext (by simp), Fin.snoc_castSucc]
  unfold blocksLaw
  rw [sum_snoc]
  simp only [hcond]
  rw [sum_eq_single x (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
  simp only [ite_true]
  exact P.consistent n x

end StochasticProcess

end InfoTheory
