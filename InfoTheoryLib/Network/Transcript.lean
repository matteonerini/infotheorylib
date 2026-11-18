/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Transcripts of interactive protocols

In an interactive protocol the index of round `l` is a function of the indices of the previous
rounds. We keep all the indices in one tuple, in which the rounds that have not happened yet hold a
default value. This avoids dependent types for the histories.

## Main definitions

* `runTo g r`: the tuple of the indices after the first `r` rounds.
* `run g`: the transcript.

## Main statements

* `run_apply`: the index of round `l` is `g l` of the indices of the previous rounds.
* `runTo_congr`: two protocols that agree along the run have the same transcript.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

@[expose] public noncomputable section

namespace InfoTheory

variable {q : ℕ} {A : Fin q → Type*} [∀ l, Nonempty (A l)]

open Classical in
/-- The tuple of the indices after the first `r` rounds of the protocol `g`. The rounds that have
not happened hold a fixed default value. -/
def runTo (g : ∀ l, (∀ l', A l') → A l) : ℕ → ∀ l, A l
  | 0 => fun _ => Classical.arbitrary _
  | r + 1 => fun l => if (l : ℕ) = r then g l (runTo g r) else runTo g r l

/-- The transcript of the protocol `g`. -/
def run (g : ∀ l, (∀ l', A l') → A l) : ∀ l, A l := runTo g q

/-- A round before `r` keeps the value it was given. -/
lemma runTo_of_lt (g : ∀ l, (∀ l', A l') → A l) {r : ℕ} {l : Fin q} (h : (l : ℕ) < r) :
    runTo g r l = g l (runTo g l) := by
  induction r with
  | zero => omega
  | succ r ih =>
    simp only [runTo]
    split_ifs with he
    · rw [he]
    · exact ih (by omega)

/-- A round from `r` on holds the default value. -/
lemma runTo_of_le (g : ∀ l, (∀ l', A l') → A l) {r : ℕ} {l : Fin q} (h : r ≤ (l : ℕ)) :
    runTo g r l = Classical.arbitrary _ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [runTo]
    rw [ite_eq_right (by omega)]
    exact ih (by omega)

/-- The index of round `l` of the transcript. -/
lemma run_apply (g : ∀ l, (∀ l', A l') → A l) (l : Fin q) : run g l = g l (runTo g l) :=
  runTo_of_lt g l.2

/-- Two protocols that agree along the run of the first one have the same run. -/
lemma runTo_congr {g g' : ∀ l, (∀ l', A l') → A l} {r : ℕ}
    (h : ∀ l : Fin q, (l : ℕ) < r → g l (runTo g l) = g' l (runTo g l)) :
    runTo g r = runTo g' r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have ih' := ih fun l hl => h l (by omega)
    funext l
    simp only [runTo]
    split_ifs with he
    · have hl := h l (by omega)
      rw [he] at hl
      rw [hl, ih']
    · rw [ih']

/-- Two protocols that agree along the run of the first one have the same transcript. -/
lemma run_congr {g g' : ∀ l, (∀ l', A l') → A l}
    (h : ∀ l : Fin q, g l (runTo g l) = g' l (runTo g l)) : run g = run g' :=
  runTo_congr fun l _ => h l

end InfoTheory
