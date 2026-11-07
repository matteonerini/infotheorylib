/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DFBlock

/-!
# Decode–forward: sliding window decoding

A sequence of messages is sent over the blocks. In block `B` the tag has the entry `m_{B-l}` at node
`l`. Node `d` decodes `m_j` from the blocks `j, j + 1, …, j + d - 1`, using its estimates of the
earlier messages.

## Main definitions

* `dfTagOf a B`: the tag of block `B` for a sequence `a` of messages.
* `dfWin`: the tests of a decoder in its window of blocks.
* `dfEstA`, `dfEst`: the estimates of a node.
* `dfTagD`: the tag that node `d` knows in block `B`.
* `DFGood`: the good event of the genie run.

## Main statements

* `dfEst_eq_of_good`: on the good event, the estimates are the messages.
* `dfX_tagD_eq_of_good`: on the good event, the nodes know the tags.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Window

variable {N Mm n : ℕ} {X Y : Fin N → Type*} [NeZero Mm] [∀ k, Fintype (X k)]
  [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)]

/-- **Page 19-14 of [elgamal2010].** The tag of block `B`, for a sequence of messages: node `l`
forwards the message `m_{B-l}`, and the index `0` when `B < l`. -/
def dfTagOf (a : ℕ → Fin Mm) (B : ℕ) : DFTag N Mm := fun l => if (l : ℕ) ≤ B then a (B - l) else 0

variable (d₀ : ∀ l, X l) (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ)
  (Cs : ℕ → DFBlock N Mm n X)

/-- **Page 19-16 of [elgamal2010].** The tests of the decoder `d` for the message `m_j`, in the
blocks `j, …, j + d - 1`, for a sequence of messages. -/
def dfWin (d : Fin N) (Zd : ℕ → Fin n → Y d) (j : ℕ) (a : ℕ → Fin Mm) : Prop :=
  ∀ k : Fin N, (k : ℕ) < d →
    dfTest d₀ L₀ k d ε (dfX d₀ (Cs (j + k)) (dfTagOf a (j + k))) (Zd (j + k))

omit [∀ k, DecidableEq (X k)] in
/-- The tests depend only on the messages up to `m_j`. -/
lemma dfWin_congr (d : Fin N) (Zd : ℕ → Fin n → Y d) (j : ℕ) {a a' : ℕ → Fin Mm}
    (h : ∀ i, i ≤ j → a i = a' i) : dfWin d₀ L₀ ε Cs d Zd j a ↔ dfWin d₀ L₀ ε Cs d Zd j a' := by
  refine forall_congr' fun k => forall_congr' fun _ => ?_
  have htag : ∀ l : Fin N, (k : ℕ) ≤ l →
      (dfTagOf a (j + k) : DFTag N Mm) l = dfTagOf a' (j + k) l := by
    intro l hl
    simp only [dfTagOf]
    split_ifs with hle
    · exact h _ (by omega)
    · rfl
  simp only [dfTest]
  have e : (fun i => ((fillGe d₀ (k + 1) (dfX d₀ (Cs (j + k)) (dfTagOf a (j + k)) i), Zd (j + k) i),
      dfX d₀ (Cs (j + k)) (dfTagOf a (j + k)) i k)) =
      (fun i => ((fillGe d₀ (k + 1) (dfX d₀ (Cs (j + k)) (dfTagOf a' (j + k)) i), Zd (j + k) i),
      dfX d₀ (Cs (j + k)) (dfTagOf a' (j + k)) i k)) := by
    funext i
    rw [fillGe_dfX_congr d₀ (Cs (j + k)) (τ := dfTagOf a (j + k)) (τ' := dfTagOf a' (j + k))
      (fun l hl => htag l (by omega)) i, dfX_congr d₀ (Cs (j + k)) htag i]
  rw [e]

open Classical in
/-- The unique message with a property, or `0`. -/
def dfUniq (P : Fin Mm → Prop) : Fin Mm := if h : ∃! m, P m then Classical.choose h else 0

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] in
lemma dfUniq_eq {P : Fin Mm → Prop} {m : Fin Mm} (hP : P m) (hu : ∀ m', P m' → m' = m) :
    dfUniq P = m := by
  have h : ∃! m, P m := ⟨m, hP, hu⟩
  simp only [dfUniq, h, dite_true]
  exact hu _ (Classical.choose_spec h).1

/-- The message that passes the tests, or `0`. -/
def dfPick (d : Fin N) (Zd : ℕ → Fin n → Y d) (j : ℕ) (a : ℕ → Fin Mm) : Fin Mm :=
  dfUniq fun m => dfWin d₀ L₀ ε Cs d Zd j (Function.update a j m)

/-- The estimates of node `d` after decoding `j` messages. -/
def dfEstA (B' : ℕ) (d : Fin N) (Zd : ℕ → Fin n → Y d) : ℕ → ℕ → Fin Mm
  | 0 => fun _ => 0
  | j + 1 => Function.update (dfEstA B' d Zd j) j
      (if j < B' then dfPick d₀ L₀ ε Cs d Zd j (dfEstA B' d Zd j) else 0)

/-- The estimate of the message `m_i` at node `d`. -/
def dfEst (B' : ℕ) (d : Fin N) (Zd : ℕ → Fin n → Y d) (i : ℕ) : Fin Mm :=
  dfEstA d₀ L₀ ε Cs B' d Zd (i + 1) i

/-- The tag that node `d` knows in block `B`: its estimates, at the nodes from `d` on. -/
def dfTagD (B' : ℕ) (d : Fin N) (Zd : ℕ → Fin n → Y d) (B : ℕ) : DFTag N Mm :=
  fun l => if (d : ℕ) ≤ l ∧ (l : ℕ) ≤ B then dfEst d₀ L₀ ε Cs B' d Zd (B - l) else 0

omit [∀ k, DecidableEq (X k)] in
/-- The estimates are causal. -/
lemma dfEstA_congr (B' : ℕ) (d : Fin N) {Zd Zd' : ℕ → Fin n → Y d} : ∀ j : ℕ,
    (∀ B, B + 1 < j + d → Zd B = Zd' B) →
    dfEstA d₀ L₀ ε Cs B' d Zd j = dfEstA d₀ L₀ ε Cs B' d Zd' j
  | 0, _ => rfl
  | j + 1, h => by
    have ih := dfEstA_congr B' d j fun B hB => h B (by omega)
    simp only [dfEstA]
    rw [ih]
    congr 1
    by_cases hj : j < B'
    · simp only [hj, ite_true]
      have hw : ∀ a : ℕ → Fin Mm, dfWin d₀ L₀ ε Cs d Zd j a ↔ dfWin d₀ L₀ ε Cs d Zd' j a := by
        intro a
        refine forall_congr' fun k => forall_congr' fun hk => ?_
        rw [h (j + k) (by omega)]
      simp only [dfPick]
      congr 1
      funext m
      exact propext (hw _)
    · simp [hj]

omit [∀ k, DecidableEq (X k)] in
lemma dfEst_congr (B' : ℕ) (d : Fin N) {Zd Zd' : ℕ → Fin n → Y d} (i : ℕ)
    (h : ∀ B, B < i + d → Zd B = Zd' B) :
    dfEst d₀ L₀ ε Cs B' d Zd i = dfEst d₀ L₀ ε Cs B' d Zd' i := by
  simp only [dfEst]
  rw [dfEstA_congr d₀ L₀ ε Cs B' d (i + 1) fun B hB => h B (by omega)]

omit [∀ k, DecidableEq (X k)] in
/-- The tag that a node knows in block `B` depends only on the earlier blocks. -/
lemma dfTagD_congr (B' : ℕ) (d : Fin N) {Zd Zd' : ℕ → Fin n → Y d} (B : ℕ)
    (h : ∀ B', B' < B → Zd B' = Zd' B') :
    (dfTagD d₀ L₀ ε Cs B' d Zd B : DFTag N Mm) = dfTagD d₀ L₀ ε Cs B' d Zd' B := by
  funext l
  simp only [dfTagD]
  split_ifs with hl
  · exact dfEst_congr d₀ L₀ ε Cs B' d _ fun B₁ hB₁ => h B₁ (by omega)
  · rfl

omit [∀ k, DecidableEq (X k)] in
/-- **On the good event, the estimates are the messages.** -/
theorem dfEstA_eq_of_good {B' : ℕ} {d : Fin N} {Zd : ℕ → Fin n → Y d} {msg : ℕ → Fin Mm}
    (h0 : ∀ i, B' ≤ i → msg i = 0)
    (htrue : ∀ j, j < B' → dfWin d₀ L₀ ε Cs d Zd j msg)
    (hwrong : ∀ j, j < B' → ∀ m, m ≠ msg j →
      ¬ dfWin d₀ L₀ ε Cs d Zd j (Function.update msg j m)) :
    ∀ j i, i < j → dfEstA d₀ L₀ ε Cs B' d Zd j i = msg i
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | j + 1, i, hi => by
    have ih := dfEstA_eq_of_good h0 htrue hwrong j
    simp only [dfEstA]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      by_cases hj : i < B'
      · simp only [hj, ite_true]
        have hag : ∀ m : Fin Mm, ∀ t, t ≤ i → Function.update (dfEstA d₀ L₀ ε Cs B' d Zd i) i m t =
            Function.update msg i m t := by
          intro m t ht
          by_cases hti : t = i
          · subst hti
            simp
          · rw [Function.update_of_ne hti, Function.update_of_ne hti]
            exact ih t (by omega)
        have hiff : ∀ m : Fin Mm, dfWin d₀ L₀ ε Cs d Zd i
            (Function.update (dfEstA d₀ L₀ ε Cs B' d Zd i) i m) ↔
            dfWin d₀ L₀ ε Cs d Zd i (Function.update msg i m) :=
          fun m => dfWin_congr d₀ L₀ ε Cs d Zd i (hag m)
        have hyes : dfWin d₀ L₀ ε Cs d Zd i
            (Function.update (dfEstA d₀ L₀ ε Cs B' d Zd i) i (msg i)) := by
          rw [hiff, Function.update_eq_self]
          exact htrue i hj
        have huniq : ∀ m, dfWin d₀ L₀ ε Cs d Zd i
            (Function.update (dfEstA d₀ L₀ ε Cs B' d Zd i) i m) → m = msg i := by
          intro m hm
          by_contra hne
          exact hwrong i hj m hne ((hiff m).1 hm)
        exact dfUniq_eq hyes huniq
      · simp only [hj, ite_false]
        exact (h0 i (by omega)).symm
    · rw [Function.update_of_ne hij]
      exact ih i (by omega)

omit [∀ k, DecidableEq (X k)] in
/-- **On the good event, the estimates are the messages.** -/
theorem dfEst_eq_of_good {B' : ℕ} {d : Fin N} {Zd : ℕ → Fin n → Y d} {msg : ℕ → Fin Mm}
    (h0 : ∀ i, B' ≤ i → msg i = 0)
    (htrue : ∀ j, j < B' → dfWin d₀ L₀ ε Cs d Zd j msg)
    (hwrong : ∀ j, j < B' → ∀ m, m ≠ msg j →
      ¬ dfWin d₀ L₀ ε Cs d Zd j (Function.update msg j m)) (i : ℕ) :
    dfEst d₀ L₀ ε Cs B' d Zd i = msg i :=
  dfEstA_eq_of_good d₀ L₀ ε Cs h0 htrue hwrong (i + 1) i (Nat.lt_succ_self i)

omit [∀ k, DecidableEq (X k)] in
/-- **On the good event, the node knows the tag from itself on.** -/
theorem dfX_tagD_eq_of_good {B' : ℕ} {d : Fin N} {Zd : ℕ → Fin n → Y d} {msg : ℕ → Fin Mm}
    (h0 : ∀ i, B' ≤ i → msg i = 0)
    (htrue : ∀ j, j < B' → dfWin d₀ L₀ ε Cs d Zd j msg)
    (hwrong : ∀ j, j < B' → ∀ m, m ≠ msg j →
      ¬ dfWin d₀ L₀ ε Cs d Zd j (Function.update msg j m)) (B : ℕ) (i : Fin n) :
    dfX d₀ (Cs B) (dfTagD d₀ L₀ ε Cs B' d Zd B) i d = dfX d₀ (Cs B) (dfTagOf msg B) i d := by
  refine dfX_congr d₀ (Cs B) (fun l hl => ?_) i
  simp only [dfTagD, dfTagOf]
  by_cases hB : (l : ℕ) ≤ B
  · rw [ite_eq_left ⟨hl, hB⟩, ite_eq_left hB]
    exact dfEst_eq_of_good d₀ L₀ ε Cs h0 htrue hwrong _
  · rw [ite_eq_right fun h => hB h.2, ite_eq_right hB]

end Window

end InfoTheory
