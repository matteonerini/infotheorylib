/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.InformationTheory.Coding.Kraft
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Computers and Kolmogorov complexity

A computer reads a binary program `p` (and possibly some side information `y`), and either halts
with an output string or runs forever. Its programs are read from left to right, never going
back, so the halting programs form a prefix-free set. The Kolmogorov complexity `K_A(x | y)` of a
string `x` is the length of the shortest program that makes the computer `A` print `x`. A
universal computer `U` simulates every computer `A` after a fixed prefix `s_A`, so that
`K_U(x) ≤ K_A(x) + c_A` (Theorem 14.2.1).

## Main definitions

* `Computer`: a partial recursive function `p, y ↦ A(p, y)` from binary programs and side
  information `y ∈ ℕ` to binary strings, whose halting programs are prefix-free for each `y`.
* `Computer.IsUniversal U`: for every computer `A` there is a program prefix `s` with
  `U(s p, y) = A(p, y)` for all `p` and `y`.
* `Computer.complexity A x y`: the conditional Kolmogorov complexity `K_A(x | y)` (14.1)–(14.2).
* `Computer.HasProgram A x y`: some program prints `x`, so that `K_A(x | y)` is a minimum.

## Main statements

* `Computer.complexity_le`, `Computer.exists_program_eq_complexity`.
* `Computer.IsUniversal.complexity_le`: **Theorem 14.2.1**, `K_U(x | y) ≤ K_A(x | y) + c_A`.
* `Computer.IsUniversal.abs_complexity_sub_le`: **(14.6)**, for two universal computers.
* `Computer.tsum_halting_le_one`: **Lemma 14.3.1**, `∑_{p halts} 2^{-l(p)} ≤ 1`.
* `Computer.card_lt_two_pow_of_complexity_lt`: **Theorem 14.2.4**, fewer than `2ᵏ` strings have
  complexity less than `k`.

## Implementation notes

Programs and outputs are `List Bool`. Computability is that of Mathlib (`Partrec₂`), the side
information is a natural number, and the unconditional complexity `K(x)` is `K(x | 0)`; a string
`y` serves as side information through its code `Encodable.encode y`, and the length `l(x)` of `x`
through `x.length`. The complexity is a natural number: it is the minimum program length when a
program exists (always the case for a universal computer, see `Kolmogorov.Programs`), and `0`
otherwise. A universal computer is constructed in `Kolmogorov.Universal`, so the results stated
for an arbitrary universal computer are not vacuous.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 14.1–14.2
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-- **Section 14.1** A computer with prefix-free programs: a partial recursive function of the
binary program `p` and the side information `y`, whose halting programs form a prefix-free set
for every `y`. -/
structure Computer where
  /-- The output `A(p, y)` of the program `p` with side information `y`, if it halts. -/
  run : List Bool → ℕ →. List Bool
  partrec : Partrec₂ run
  prefixFree : ∀ y, InformationTheory.IsPrefixFree {p | (run p y).Dom}

namespace Computer

variable (A : Computer)

/-- The computer `U` is universal if it simulates every computer `A`: there is a program prefix
`s` (the simulation program) with `U(s p, y) = A(p, y)` for all `p` and `y`. -/
def IsUniversal (U : Computer) : Prop :=
  ∀ A : Computer, ∃ s : List Bool, ∀ p y, U.run (s ++ p) y = A.run p y

/-- Some program prints `x` with side information `y`. -/
def HasProgram (x : List Bool) (y : ℕ) : Prop := ∃ p, x ∈ A.run p y

/-- **(14.1)–(14.2)** The (conditional) Kolmogorov complexity `K_A(x | y)`: the length of the
shortest program that prints `x` given `y` (`0` if there is none). -/
def complexity (x : List Bool) (y : ℕ) : ℕ :=
  sInf {l | ∃ p : List Bool, p.length = l ∧ x ∈ A.run p y}

variable {A}

lemma complexity_le {x p : List Bool} {y : ℕ} (h : x ∈ A.run p y) :
    A.complexity x y ≤ p.length :=
  Nat.sInf_le ⟨p, rfl, h⟩

lemma exists_program_eq_complexity {x : List Bool} {y : ℕ} (h : A.HasProgram x y) :
    ∃ p, x ∈ A.run p y ∧ p.length = A.complexity x y := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq, hx⟩ := Nat.sInf_mem (s := {l | ∃ p : List Bool, p.length = l ∧ x ∈ A.run p y})
    ⟨_, p, rfl, hp⟩
  exact ⟨q, hx, hq⟩

/-- `K_A(x | y) ≤ l` if and only if some program of length at most `l` prints `x`. -/
lemma complexity_le_iff {x : List Bool} {y l : ℕ} (h : A.HasProgram x y) :
    A.complexity x y ≤ l ↔ ∃ p, x ∈ A.run p y ∧ p.length ≤ l := by
  constructor
  · intro hl
    obtain ⟨p, hp, hlen⟩ := exists_program_eq_complexity h
    exact ⟨p, hp, hlen ▸ hl⟩
  · rintro ⟨p, hp, hl⟩
    exact (complexity_le hp).trans hl

/-- A program prints at most one string. -/
lemma eq_of_mem_run {x x' p : List Bool} {y : ℕ} (h : x ∈ A.run p y) (h' : x' ∈ A.run p y) :
    x = x' :=
  Part.mem_unique h h'

lemma dom_of_mem_run {x p : List Bool} {y : ℕ} (h : x ∈ A.run p y) : (A.run p y).Dom :=
  Part.dom_iff_mem.2 ⟨x, h⟩

/-! ### Universality -/

/-- A universal computer prints `x` after the simulation prefix of `A`. -/
lemma IsUniversal.mem_run {U : Computer} (hU : U.IsUniversal) (A : Computer) :
    ∃ s : List Bool, ∀ {x p : List Bool} {y : ℕ}, x ∈ A.run p y → x ∈ U.run (s ++ p) y := by
  obtain ⟨s, hs⟩ := hU A
  exact ⟨s, fun {x p y} h => by rw [hs]; exact h⟩

/-- **Theorem 14.2.1 (Universality of Kolmogorov complexity), (14.3)–(14.5).** For a universal
computer `U` and every computer `A` there is a constant `c_A` with
`K_U(x | y) ≤ K_A(x | y) + c_A` for all strings `x` that `A` can print. -/
theorem IsUniversal.complexity_le {U : Computer} (hU : U.IsUniversal) (A : Computer) :
    ∃ c, ∀ x y, A.HasProgram x y → U.complexity x y ≤ A.complexity x y + c := by
  obtain ⟨s, hs⟩ := hU.mem_run A
  refine ⟨s.length, fun x y hx => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_program_eq_complexity hx
  calc U.complexity x y ≤ (s ++ p).length := Computer.complexity_le (hs hp)
    _ = A.complexity x y + s.length := by rw [List.length_append, hlen, add_comm]

/-- A universal computer can print whatever another computer prints. -/
lemma IsUniversal.hasProgram {U : Computer} (hU : U.IsUniversal) (A : Computer) {x : List Bool}
    {y : ℕ} (h : A.HasProgram x y) : U.HasProgram x y := by
  obtain ⟨s, hs⟩ := hU.mem_run A
  obtain ⟨p, hp⟩ := h
  exact ⟨s ++ p, hs hp⟩

/-- **(14.6)** The complexities with respect to two universal computers differ by a bounded
amount, for the strings both can print. -/
theorem IsUniversal.abs_complexity_sub_le {U V : Computer} (hU : U.IsUniversal)
    (hV : V.IsUniversal) :
    ∃ c, ∀ x y, U.HasProgram x y →
      |(U.complexity x y : ℤ) - V.complexity x y| ≤ c := by
  obtain ⟨c₁, h₁⟩ := hU.complexity_le V
  obtain ⟨c₂, h₂⟩ := hV.complexity_le U
  refine ⟨max c₁ c₂, fun x y hx => ?_⟩
  have hVx := hV.hasProgram U hx
  have a := h₁ x y hVx
  have b := h₂ x y hx
  rw [abs_le]
  constructor <;> omega

/-! ### Kraft's inequality for programs -/

variable (A) in
/-- The set of programs that halt with side information `y`. -/
abbrev haltingSet (y : ℕ) : Set (List Bool) := {p | (A.run p y).Dom}

lemma summable_halting (y : ℕ) :
    Summable fun p : A.haltingSet y => (1 / 2 : ℝ) ^ (p : List Bool).length := by
  have := (A.prefixFree y).summable_one_div_card_pow_length (α := Bool)
  simpa [Fintype.card_bool] using this

/-- **Lemma 14.3.1, (14.26).** The halting programs of a computer satisfy the Kraft inequality,
`∑_{p : U(p) halts} 2^{-l(p)} ≤ 1`. -/
theorem tsum_halting_le_one (y : ℕ) :
    ∑' p : A.haltingSet y, (1 / 2 : ℝ) ^ (p : List Bool).length ≤ 1 := by
  have := (A.prefixFree y).tsum_one_div_card_pow_length_le_one (α := Bool)
  simpa [Fintype.card_bool] using this

/-- The shortest programs of distinct strings are distinct, and form a prefix-free set: the
complexities satisfy the Kraft inequality `∑ₓ 2^{-K(x | y)} ≤ 1` over every finite set of strings
that the computer can print. -/
theorem sum_two_pow_neg_complexity_le_one (y : ℕ) (F : Finset (List Bool))
    (hF : ∀ x ∈ F, A.HasProgram x y) : ∑ x ∈ F, (1 / 2 : ℝ) ^ A.complexity x y ≤ 1 := by
  classical
  choose! P hP hlen using fun x hx => exists_program_eq_complexity (hF x hx)
  have hinj : Set.InjOn P F := fun x hx x' hx' h =>
    eq_of_mem_run (hP x hx) (h ▸ hP x' hx')
  have hS : InformationTheory.IsPrefixFree (↑(F.image P) : Set (List Bool)) :=
    (A.prefixFree y).anti fun p hp => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      exact dom_of_mem_run (hP x hx)
  have h := hS.finsetSum_one_div_card_pow_length_le_one
  rw [Finset.sum_image hinj] at h
  calc ∑ x ∈ F, (1 / 2 : ℝ) ^ A.complexity x y = ∑ x ∈ F, (1 / 2 : ℝ) ^ (P x).length :=
        Finset.sum_congr rfl fun x hx => by rw [hlen x hx]
    _ ≤ 1 := by simpa [Fintype.card_bool] using h

/-! ### Counting -/

/-- There are `2ᵏ - 1` binary strings of length less than `k`. -/
lemma card_short_le (k : ℕ) :
    ((range k).biUnion fun j => univ.image fun w : Fin j → Bool => List.ofFn w).card < 2 ^ k := by
  calc ((range k).biUnion fun j => univ.image fun w : Fin j → Bool => List.ofFn w).card
      ≤ ∑ j ∈ range k, (univ.image fun w : Fin j → Bool => List.ofFn w).card := card_biUnion_le
    _ ≤ ∑ j ∈ range k, 2 ^ j := sum_le_sum fun j _ => card_image_le.trans (by simp)
    _ < 2 ^ k := by
      have : ∑ j ∈ range k, 2 ^ j + 1 = 2 ^ k := by
        induction k with
        | zero => simp
        | succ k ih => rw [sum_range_succ, pow_succ]; omega
      omega

lemma mem_short {p : List Bool} {k : ℕ} (hp : p.length < k) :
    p ∈ (range k).biUnion fun j => univ.image fun w : Fin j → Bool => List.ofFn w :=
  mem_biUnion.2 ⟨p.length, mem_range.2 hp, mem_image.2 ⟨fun i => p[i], mem_univ _,
    List.ofFn_getElem⟩⟩

/-- **Theorem 14.2.4 (Lower bound on Kolmogorov complexity), (14.10)–(14.12).** Fewer than `2ᵏ`
strings have complexity less than `k`: there are only `2ᵏ - 1` programs of length less than `k`,
and each prints at most one string. -/
theorem card_lt_two_pow_of_complexity_lt {y k : ℕ} (F : Finset (List Bool))
    (hF : ∀ x ∈ F, A.HasProgram x y ∧ A.complexity x y < k) : F.card < 2 ^ k := by
  classical
  choose! P hP hlen using fun x hx => exists_program_eq_complexity (hF x hx).1
  have hinj : Set.InjOn P F := fun x hx x' hx' h =>
    eq_of_mem_run (hP x hx) (h ▸ hP x' hx')
  refine lt_of_le_of_lt ?_ (card_short_le k)
  rw [← card_image_of_injOn hinj]
  refine card_le_card fun p hp => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hp
  exact mem_short (by rw [hlen x hx]; exact (hF x hx).2)

end Computer

end InfoTheory
