/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NNCTheorem

/-!
# Decode–forward: strategies for a correlated input law

The code of multi-hop decode–forward is a tree of superposed codewords: the codeword of node `k`
is drawn from `p(x_k | x_{k+1}, …, x_N)` given the codewords of the nodes after `k`. To keep all the
entries of the code independent, we draw a random strategy for each node. A strategy of node `k`
maps the inputs of the nodes after `k` to an input of node `k`. Running the strategies from the last
node to the first gives a tuple with law `p(xᴺ)`.

## Main definitions

* `fillGe d₀ j x`: the tuple `x` with the entries before `j` replaced by a default value.
* `buildAt s j`: the tuple built by the strategies `s` of the nodes from `j` on.
* `prod_kernel_eq`: the law of a tuple is the product of the conditional laws of `X_k` given
  `X_{k+1}, …, X_N`.
* `netStratLaw`: the law of a random strategy.

## Main statements

* `buildAt_eq_fillGe`: the tuple from `j` on is the part from `j` on of the whole tuple.
* `build_eq_iff`: when strategies build a given tuple.
* `sum_strat_build`: **the law of the tuple built by independent strategies is `p`**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Build

variable {N : ℕ} {X : Fin N → Type*}

/-- The tuple `x` with the entries before `j` replaced by a default value. -/
def fillGe (d₀ : ∀ l, X l) (j : ℕ) (x : ∀ l, X l) : ∀ l, X l :=
  fun l => if j ≤ l then x l else d₀ l

/-- A strategy of node `k`: its input as a function of the inputs of the nodes after `k`. -/
abbrev NetStrat (X : Fin N → Type*) (k : Fin N) := (∀ l, X l) → X k

/-- The tuple built by the strategies from node `j` on, with default values before `j`. -/
def buildAt [∀ k, DecidableEq (X k)] (d₀ : ∀ l, X l) (s : ∀ k, NetStrat X k) (j : ℕ) : ∀ l, X l :=
  if h : j < N then
    Function.update (buildAt d₀ s (j + 1)) ⟨j, h⟩ (s ⟨j, h⟩ (buildAt d₀ s (j + 1)))
  else d₀
termination_by N - j

variable [∀ k, DecidableEq (X k)] (d₀ : ∀ l, X l)

lemma buildAt_of_lt (s : ∀ k, NetStrat X k) {j : ℕ} (h : j < N) :
    buildAt d₀ s j = Function.update (buildAt d₀ s (j + 1)) ⟨j, h⟩
      (s ⟨j, h⟩ (buildAt d₀ s (j + 1))) := by
  rw [buildAt, dite_eq_left h]

lemma buildAt_of_ge (s : ∀ k, NetStrat X k) {j : ℕ} (h : N ≤ j) : buildAt d₀ s j = d₀ := by
  rw [buildAt, dite_eq_right (not_lt.mpr h)]

/-- The entries before `j` have the default value. -/
lemma buildAt_lt (s : ∀ k, NetStrat X k) (l : Fin N) : ∀ t j, N - j = t → (l : ℕ) < j →
    buildAt d₀ s j l = d₀ l := by
  intro t
  induction t with
  | zero =>
    intro j hj hl
    rw [buildAt_of_ge d₀ s (by omega)]
  | succ t ih =>
    intro j hj hl
    have hjN : j < N := by omega
    rw [buildAt_of_lt d₀ s hjN, Function.update_of_ne (fun h => by
      have := congrArg Fin.val h
      simp at this
      omega)]
    exact ih (j + 1) (by omega) (by omega)

/-- The entry `l` does not change when going from `l` to an earlier node. -/
lemma buildAt_ge (s : ∀ k, NetStrat X k) (l : Fin N) : ∀ t j, (l : ℕ) - j = t → j ≤ l →
    buildAt d₀ s j l = buildAt d₀ s l l := by
  intro t
  induction t with
  | zero =>
    intro j hj hl
    have : j = l := by omega
    rw [this]
  | succ t ih =>
    intro j hj hl
    have hjN : j < N := lt_of_le_of_lt hl l.2
    rw [buildAt_of_lt d₀ s hjN, Function.update_of_ne (fun h => by
      have := congrArg Fin.val h
      simp at this
      omega)]
    exact ih (j + 1) (by omega) (by omega)

/-- The tuple built from `j` on is the part from `j` on of the whole tuple. -/
theorem buildAt_eq_fillGe (s : ∀ k, NetStrat X k) (j : ℕ) :
    buildAt d₀ s j = fillGe d₀ j (buildAt d₀ s 0) := by
  funext l
  simp only [fillGe]
  split_ifs with h
  · rw [buildAt_ge d₀ s l _ j rfl h, buildAt_ge d₀ s l _ 0 rfl (Nat.zero_le _)]
  · exact buildAt_lt d₀ s l _ j rfl (by omega)

/-- The value of the entry `l` of the whole tuple. -/
lemma buildAt_zero_apply (s : ∀ k, NetStrat X k) (l : Fin N) :
    buildAt d₀ s 0 l = s l (fillGe d₀ (l + 1) (buildAt d₀ s 0)) := by
  rw [buildAt_ge d₀ s l _ 0 rfl (Nat.zero_le _), buildAt_of_lt d₀ s l.2, Function.update_self,
    buildAt_eq_fillGe d₀ s]

/-- **When strategies build a given tuple.** -/
theorem build_eq_iff (s : ∀ k, NetStrat X k) (x : ∀ l, X l) :
    buildAt d₀ s 0 = x ↔ ∀ k, s k (fillGe d₀ (k + 1) x) = x k := by
  constructor
  · rintro rfl k
    exact (buildAt_zero_apply d₀ s k).symm
  · intro h
    -- by descending induction
    have hdesc : ∀ t j, N - j = t → buildAt d₀ s j = fillGe d₀ j x := by
      intro t
      induction t with
      | zero =>
        intro j hj
        rw [buildAt_of_ge d₀ s (by omega)]
        funext l
        have := l.2
        simp only [fillGe]
        rw [ite_eq_right (by omega)]
      | succ t ih =>
        intro j hj
        have hjN : j < N := by omega
        rw [buildAt_of_lt d₀ s hjN, ih (j + 1) (by omega), h ⟨j, hjN⟩]
        funext l
        by_cases hl : l = ⟨j, hjN⟩
        · subst hl
          simp [fillGe]
        · rw [Function.update_of_ne hl]
          have hne : (l : ℕ) ≠ j := fun e => hl (Fin.ext e)
          simp only [fillGe]
          by_cases hle : j + 1 ≤ (l : ℕ)
          · rw [ite_eq_left hle, ite_eq_left (by omega)]
          · rw [ite_eq_right hle, ite_eq_right (by omega)]
    have := hdesc _ 0 rfl
    rw [this]
    funext l
    simp [fillGe]

/-- The entries of the tuple from `j` on depend only on the strategies from `j` on. -/
theorem buildAt_congr {s s' : ∀ k, NetStrat X k} : ∀ t j, N - j = t →
    (∀ k : Fin N, j ≤ k → s k = s' k) → buildAt d₀ s j = buildAt d₀ s' j := by
  intro t
  induction t with
  | zero =>
    intro j hj _
    rw [buildAt_of_ge d₀ s (by omega), buildAt_of_ge d₀ s' (by omega)]
  | succ t ih =>
    intro j hj h
    have hjN : j < N := by omega
    rw [buildAt_of_lt d₀ s hjN, buildAt_of_lt d₀ s' hjN, ih (j + 1) (by omega)
      fun k hk => h k (by omega), h ⟨j, hjN⟩ (by simp)]

end Build

/-! ### The law of the tuple -/

section Law

variable {N : ℕ} {X : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)]

/-- The law of a random strategy with the conditional law `κ`: an independent entry for each
tuple. -/
def netStratLaw {k : Fin N} (κ : (∀ l, X l) → X k → ℝ) (s : NetStrat X k) : ℝ :=
  piLaw (fun c => κ c) s

variable {p : (∀ l, X l) → ℝ} (d₀ : ∀ l, X l)

/-- The law of the tuple `(fillGe (k + 1) x, x_k)`. -/
def dfJoint (p : (∀ l, X l) → ℝ) (d₀ : ∀ l, X l) (k : Fin N) : (∀ l, X l) × X k → ℝ :=
  dist p fun x => (fillGe d₀ (k + 1) x, x k)

omit [∀ k, DecidableEq (X k)] in
/-- The law of a tuple is the product of the conditional laws. -/
theorem prod_kernel_eq {κ : ∀ k, (∀ l, X l) → X k → ℝ} (hp : IsPMF p)
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) (x : ∀ l, X l) :
    ∏ k, κ k (fillGe d₀ (k + 1) x) (x k) = p x := by
  classical
  -- the mass of the part from `j` on
  let P : ℕ → ℝ := fun j => dist p (fillGe d₀ j) (fillGe d₀ j x)
  have hstep : ∀ k : Fin N, P k = P (k + 1) * κ k (fillGe d₀ (k + 1) x) (x k) := by
    intro k
    have h₁ : P k = dfJoint p d₀ k (fillGe d₀ (k + 1) x, x k) := by
      simp only [P, dfJoint, dist]
      refine sum_congr rfl fun z _ => ?_
      have hiff : fillGe d₀ k z = fillGe d₀ k x ↔
          (fillGe d₀ (k + 1) z, z k) = (fillGe d₀ (k + 1) x, x k) := by
        constructor
        · intro h
          refine Prod.ext (funext fun l => ?_) ?_
          · simp only [fillGe]
            by_cases hl : (k : ℕ) + 1 ≤ l
            · have := congrFun h l
              simp only [fillGe] at this
              rw [ite_eq_left (by omega), ite_eq_left (by omega)] at this
              rw [ite_eq_left hl, ite_eq_left hl, this]
            · rw [ite_eq_right hl, ite_eq_right hl]
          · have := congrFun h k
            simpa [fillGe] using this
        · intro h
          funext l
          simp only [fillGe]
          by_cases hl : (k : ℕ) ≤ l
          · rw [ite_eq_left hl, ite_eq_left hl]
            by_cases hlk : l = k
            · subst hlk
              exact (Prod.ext_iff.mp h).2
            · have hne : (l : ℕ) ≠ k := fun e => hlk (Fin.ext e)
              have := congrFun (Prod.ext_iff.mp h).1 l
              simp only [fillGe] at this
              rw [ite_eq_left (by omega), ite_eq_left (by omega)] at this
              exact this
          · rw [ite_eq_right hl, ite_eq_right hl]
      simp only [hiff]
      congr
    have h₂ : marg (dfJoint p d₀ k) (fillGe d₀ (k + 1) x) = P (k + 1) := by
      rw [marg_eq_dist, dfJoint, ← dist_comp_eq]
      simp only [P]
      have e : (Prod.fst ∘ fun x : ∀ l, X l => (fillGe d₀ (k + 1) x, x k)) = fillGe d₀ (k + 1) :=
        rfl
      rw [e]
    rw [h₁, hκ, h₂]
  have hP0 : P 0 = p x := by
    have e : fillGe d₀ 0 = id := by
      funext z l
      simp [fillGe]
    simp only [P]
    rw [e, dist_id]
    rfl
  have hPN : ∀ j, N ≤ j → P j = 1 := by
    intro j hj
    simp only [P]
    have e : ∀ z : ∀ l, X l, fillGe d₀ j z = d₀ := fun z => by
      funext l
      have := l.2
      simp only [fillGe]
      rw [ite_eq_right (by omega)]
    simp only [dist, e, ite_true]
    exact hp.sum_eq_one
  -- the telescoping product
  have htel : ∀ t j, N - j = t → P j =
      ∏ k ∈ univ.filter (fun k : Fin N => j ≤ k), κ k (fillGe d₀ (k + 1) x) (x k) := by
    intro t
    induction t with
    | zero =>
      intro j hj
      rw [hPN j (by omega), filter_false_of_mem, prod_empty]
      intro k _
      have := k.2
      omega
    | succ t ih =>
      intro j hj
      have hjN : j < N := by omega
      have hins : univ.filter (fun k : Fin N => j ≤ k) =
          insert ⟨j, hjN⟩ (univ.filter fun k : Fin N => j + 1 ≤ k) := by
        ext k
        simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
        omega
      rw [hins, prod_insert (by simp), ← ih (j + 1) (by omega)]
      have := hstep ⟨j, hjN⟩
      simp only at this
      rw [this]
      ring
  have := htel _ 0 rfl
  rw [hP0] at this
  rw [this]
  exact (prod_congr (by ext k; simp) fun _ _ => rfl)

/-- The law of the entries that are used: a strategy at one tuple. -/
lemma sum_stratLaw_eval {k : Fin N} {κ : (∀ l, X l) → X k → ℝ} (hκ : IsChannel κ) (c : ∀ l, X l)
    (G : X k → ℝ) : ∑ s : NetStrat X k, netStratLaw κ s * G (s c) = ∑ a, κ c a * G a :=
  sum_piLaw_mul_eval (ν := fun c => κ c) hκ c G

lemma netStratLaw_isPMF {k : Fin N} {κ : (∀ l, X l) → X k → ℝ} (hκ : IsChannel κ) :
    IsPMF (netStratLaw κ) :=
  piLaw_isPMF hκ

/-- **The law of the tuple built by independent strategies is `p`.** -/
theorem sum_strat_build {κ : ∀ k, (∀ l, X l) → X k → ℝ} (hp : IsPMF p)
    (hκc : ∀ k, IsChannel (κ k))
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) (x : ∀ l, X l) :
    ∑ s : ∀ k, NetStrat X k, prodLaw (fun k => netStratLaw (κ k)) s * ind (buildAt d₀ s 0 = x) =
      p x := by
  classical
  have h₁ : ∀ s : ∀ k, NetStrat X k, prodLaw (fun k => netStratLaw (κ k)) s * ind (buildAt d₀ s 0 =
    x) =
      ∏ k, (netStratLaw (κ k) (s k) * ind (s k (fillGe d₀ (k + 1) x) = x k)) := by
    intro s
    rw [prod_mul_distrib]
    congr 1
    by_cases h : ∀ k, s k (fillGe d₀ (k + 1) x) = x k
    · rw [ind_of_pos ((build_eq_iff d₀ s x).2 h)]
      exact (prod_eq_one fun k _ => ind_of_pos (h k)).symm
    · rw [ind_of_neg fun h' => h ((build_eq_iff d₀ s x).1 h')]
      push Not at h
      obtain ⟨k, hk⟩ := h
      exact (prod_eq_zero (mem_univ k) (ind_of_neg hk)).symm
  simp_rw [h₁]
  rw [sum_prod_pi (A := NetStrat X) fun k s => netStratLaw (κ k) s * ind (s (fillGe d₀ (k + 1) x) =
    x k)]
  rw [← prod_kernel_eq d₀ hp hκ x]
  refine prod_congr rfl fun k _ => ?_
  rw [sum_stratLaw_eval (hκc k) (fillGe d₀ (k + 1) x) fun a => ind (a = x k),
    Finset.sum_eq_single (x k)]
  · rw [ind_of_pos rfl, mul_one]
  · exact fun a _ ha => by rw [ind_of_neg ha, mul_zero]
  · simp

end Law

end InfoTheory
