/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import InfoTheoryLib.SourceCoding.Code

/-!
# Prefix codes for the integers

A positive integer `k` has `⌊log₂ k⌋ + 1` binary digits, the leading one being `1`. Its digits
alone do not form a prefix code, since the receiver does not know where they end. Sending first
the number of digits in unary gives the code `C₁(k) = 0^{⌊log₂ k⌋} 1 x₁ ⋯` of length
`2 ⌊log₂ k⌋ + 1`; sending the number of digits with `C₁` instead gives a code of length
`log₂ k + 2 log₂ log₂ k + O(1)` (Lemma 13.5.1). These are the Elias gamma and delta codes.

## Main definitions

* `lowBits k`: the `⌊log₂ k⌋` binary digits of `k` after the leading `1`.
* `eliasGamma k`: `C₁(k)`, `⌊log₂ k⌋` zeros, then the digits of `k` (13.61).
* `eliasDelta k`: `C₁(⌊log₂ k⌋ + 1)` followed by the digits of `k` after the leading `1`.

## Main statements

* `eliasGamma_isPrefixCode`, `length_eliasGamma`: a prefix code of length `2 ⌊log₂ k⌋ + 1`.
* `eliasDelta_isPrefixCode`: the delta code is a prefix code.
* `length_eliasDelta_le`, `length_eliasDelta_le'`: **Lemma 13.5.1**, the length of the
  codeword of `k` is at most `log₂ k + 2 log₂ log₂ k + 3`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Lemma 13.5.1
-/

@[expose] public section

open Real

namespace InfoTheory

/-! ### Binary digits -/

/-- The `⌊log₂ k⌋` binary digits of `k` below the leading one, least significant first. -/
def lowBits (k : ℕ) : List Bool := List.ofFn fun i : Fin (Nat.log2 k) => k.testBit i

@[simp] lemma length_lowBits (k : ℕ) : (lowBits k).length = Nat.log2 k := by simp [lowBits]

/-- A positive integer is determined by the number of its digits and its digits below the leading
one. -/
lemma eq_of_lowBits_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hlog : Nat.log2 a = Nat.log2 b)
    (h : lowBits a = lowBits b) : a = b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rcases lt_trichotomy i (Nat.log2 a) with hi | hi | hi
  · have := congrArg (fun l => l[i]?) h
    simp only [lowBits, List.getElem?_ofFn] at this
    rw [dite_eq_left hi, dite_eq_left (hlog ▸ hi)] at this
    exact Option.some_injective _ this
  · rw [hi, Nat.testBit_log2 ha, hlog, Nat.testBit_log2 hb]
  · have h1 : a < 2 ^ i := Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right
      (by norm_num) hi)
    have h2 : b < 2 ^ i := Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right
      (by norm_num) (hlog ▸ hi))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-! ### The Elias gamma code -/

/-- **(13.61)** The code `C₁(k)`: the number `⌊log₂ k⌋` of digits after the leading one, in
unary, then the binary digits of `k` starting with the leading `1`. -/
def eliasGamma (k : ℕ) : List Bool := List.replicate (Nat.log2 k) false ++ true :: lowBits k

lemma length_eliasGamma (k : ℕ) : (eliasGamma k).length = 2 * Nat.log2 k + 1 := by
  simp [eliasGamma]
  ring

lemma replicate_prefix_replicate {m n : ℕ} {u v : List Bool}
    (h : List.replicate m false ++ true :: u <+: List.replicate n false ++ true :: v) :
    m = n ∧ u <+: v := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simpa using h
    | succ n => simp [List.replicate_succ] at h
  | succ m ih =>
    cases n with
    | zero => simp [List.replicate_succ] at h
    | succ n =>
      simp only [List.replicate_succ, List.cons_append, List.cons_prefix_cons, true_and] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by rw [h1], h2⟩

lemma eq_of_eliasGamma_prefix {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : eliasGamma a <+: eliasGamma b) : a = b := by
  obtain ⟨hlog, hpre⟩ := replicate_prefix_replicate h
  exact eq_of_lowBits_eq ha hb hlog (hpre.eq_of_length (by simp [hlog]))

/-- `C₁` is a prefix code for the positive integers. -/
theorem eliasGamma_isPrefixCode : IsPrefixCode fun k : ℕ+ => eliasGamma k := fun a b h =>
  PNat.coe_injective (eq_of_eliasGamma_prefix a.ne_zero b.ne_zero h)

/-! ### The Elias delta code -/

/-- **Lemma 13.5.1** The code `C₂(k)`: the number `⌊log₂ k⌋ + 1` of digits of `k`, coded with
`C₁`, then the digits of `k` after the leading `1`. -/
def eliasDelta (k : ℕ) : List Bool := eliasGamma (Nat.log2 k + 1) ++ lowBits k

lemma length_eliasDelta (k : ℕ) :
    (eliasDelta k).length = 2 * Nat.log2 (Nat.log2 k + 1) + 1 + Nat.log2 k := by
  simp [eliasDelta, length_eliasGamma]

lemma eq_of_eliasDelta_prefix {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : eliasDelta a <+: eliasDelta b) : a = b := by
  have h1 : eliasGamma (Nat.log2 a + 1) <+: eliasDelta b :=
    (List.prefix_append _ _).trans h
  have h2 : eliasGamma (Nat.log2 b + 1) <+: eliasDelta b := List.prefix_append _ _
  have hlog : Nat.log2 a = Nat.log2 b := by
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h3 | h3
    · exact Nat.succ_injective (eq_of_eliasGamma_prefix (by omega) (by omega) h3)
    · exact (Nat.succ_injective (eq_of_eliasGamma_prefix (by omega) (by omega) h3)).symm
  rw [eliasDelta, eliasDelta, hlog, List.prefix_append_right_inj] at h
  exact eq_of_lowBits_eq ha hb hlog (h.eq_of_length (by simp [hlog]))

/-- **Lemma 13.5.1** `C₂` is a prefix code for the positive integers. -/
theorem eliasDelta_isPrefixCode : IsPrefixCode fun k : ℕ+ => eliasDelta k := fun a b h =>
  PNat.coe_injective (eq_of_eliasDelta_prefix a.ne_zero b.ne_zero h)

/-- **Lemma 13.5.1** The codeword of `k` has length at most
`log₂ k + 2 log₂ (log₂ k + 1) + 1`. -/
theorem length_eliasDelta_le (k : ℕ) :
    ((eliasDelta k).length : ℝ) ≤ logb 2 k + 2 * logb 2 (logb 2 k + 1) + 1 := by
  rw [length_eliasDelta]
  push_cast
  have h1 : (Nat.log2 k : ℝ) ≤ logb 2 k := log2_le_logb k
  have h2 : (Nat.log2 (Nat.log2 k + 1) : ℝ) ≤ logb 2 (logb 2 k + 1) := by
    refine (log2_le_logb _).trans (logb_le_logb_of_le (by norm_num) (by positivity) ?_)
    push_cast
    linarith
  linarith

/-- **Lemma 13.5.1** For `k ≥ 2`, the codeword of `k` has length at most
`log₂ k + 2 log₂ log₂ k + 3`. -/
theorem length_eliasDelta_le' {k : ℕ} (hk : 2 ≤ k) :
    ((eliasDelta k).length : ℝ) ≤ logb 2 k + 2 * logb 2 (logb 2 k) + 3 := by
  have hl : 1 ≤ logb 2 (k : ℝ) := by
    rw [le_logb_iff_rpow_le (by norm_num) (by positivity), rpow_one]
    exact_mod_cast hk
  have h := length_eliasDelta_le k
  have h2 : logb 2 (logb 2 k + 1) ≤ logb 2 (logb 2 k) + 1 := by
    have : logb 2 k + 1 ≤ 2 * logb 2 k := by linarith
    calc logb 2 (logb 2 k + 1) ≤ logb 2 (2 * logb 2 k) :=
          logb_le_logb_of_le (by norm_num) (by positivity) this
      _ = logb 2 (logb 2 k) + 1 := by
        rw [logb_mul (by norm_num) (by positivity), logb_self_eq_one (by norm_num), add_comm]
  linarith

end InfoTheory
