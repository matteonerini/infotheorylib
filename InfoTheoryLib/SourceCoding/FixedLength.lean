/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib

/-!
# Fixed-length binary codes

A finite set `S` with `|S| ≤ 2ᵏ` can be described with `k` bits: enumerate its elements and write
the index of each element in binary. Codewords are binary strings, represented as `List Bool`.

## Main definitions

* `binaryDigits k m`: the `k` least significant binary digits of `m`.
* `fixedLengthCode S k`: the code sending the `i`-th element of `S` to the `k` binary digits of
  `i`.

## Main statements

* `fixedLengthCode_injOn`: if `|S| ≤ 2ᵏ`, the code is one-to-one on `S`.
* `card_le_two_pow_ceil`: if `|S| ≤ e^t`, then `|S| ≤ 2^⌈t / log 2⌉`, so `⌈t / log 2⌉` bits
  suffice.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 3.2
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-- The `k` least significant binary digits of `m`, least significant first. -/
def binaryDigits (k m : ℕ) : List Bool := List.ofFn fun j : Fin k => m.testBit j

@[simp] lemma length_binaryDigits (k m : ℕ) : (binaryDigits k m).length = k :=
  List.length_ofFn

/-- Numbers below `2ᵏ` are determined by their `k` least significant binary digits. -/
lemma binaryDigits_inj {k m₁ m₂ : ℕ} (h₁ : m₁ < 2 ^ k) (h₂ : m₂ < 2 ^ k)
    (h : binaryDigits k m₁ = binaryDigits k m₂) : m₁ = m₂ := by
  rw [binaryDigits, binaryDigits, List.ofFn_inj] at h
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < k
  · exact congrFun h ⟨i, hi⟩
  · have hk : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (not_lt.1 hi)
    rw [Nat.testBit_eq_false_of_lt (h₁.trans_le hk), Nat.testBit_eq_false_of_lt (h₂.trans_le hk)]

open Classical in
/-- The fixed-length code of a finite set `S`: the `i`-th element of `S` (in some fixed
enumeration) is sent to the `k` binary digits of `i`. Elements outside `S` are sent to the empty
string. -/
def fixedLengthCode {β : Type*} (S : Finset β) (k : ℕ) (x : β) : List Bool :=
  if h : x ∈ S then binaryDigits k (S.equivFin ⟨x, h⟩) else []

lemma length_fixedLengthCode {β : Type*} {S : Finset β} (k : ℕ) {x : β} (hx : x ∈ S) :
    (fixedLengthCode S k x).length = k := by
  simp [fixedLengthCode, hx]

/-- If `|S| ≤ 2ᵏ`, the fixed-length code is one-to-one on `S`. -/
lemma fixedLengthCode_injOn {β : Type*} {S : Finset β} {k : ℕ} (hS : S.card ≤ 2 ^ k) :
    Set.InjOn (fixedLengthCode S k) S := by
  intro x hx y hy h
  simp only [fixedLengthCode, mem_coe.1 hx, mem_coe.1 hy, dite_true] at h
  have h' := binaryDigits_inj ((S.equivFin ⟨x, hx⟩).isLt.trans_le hS)
    ((S.equivFin ⟨y, hy⟩).isLt.trans_le hS) h
  have := S.equivFin.injective (Fin.ext h')
  exact congrArg Subtype.val this

/-- If `m ≤ e^t`, then `m ≤ 2^⌈t / log 2⌉`: `⌈t / log 2⌉` bits suffice to index `m` objects. -/
lemma card_le_two_pow_ceil {m : ℕ} {t : ℝ} (h : (m : ℝ) ≤ exp t) :
    m ≤ 2 ^ ⌈t / log 2⌉₊ := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have : exp t ≤ (2 : ℝ) ^ (⌈t / log 2⌉₊ : ℝ) := by
    rw [rpow_def_of_pos two_pos]
    exact exp_le_exp.2 (by
      have := Nat.le_ceil (t / log 2)
      rw [div_le_iff₀ h2] at this
      linarith)
  rw [rpow_natCast] at this
  exact_mod_cast h.trans this

end InfoTheory
