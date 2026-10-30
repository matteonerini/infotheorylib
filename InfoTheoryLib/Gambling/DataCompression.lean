/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.ShannonFanoElias

/-!
# Data compression and gambling

A gambler who bets `b(x)` on each sequence `x` of `n` binary outcomes, at `2`-for-`1` odds per
outcome, ends with wealth `S(x) = 2ⁿ b(x)`. An identical twin of the gambler can serve as a
decompressor. Arrange the sequences in order, and describe `x` by
`k = ⌈log (1/b(x))⌉ = ⌈n - log S(x)⌉` bits pinning down a point of the interval `[F(x⁻), F(x))`
of length `b(x)`, where
`F(x) = ∑_{x' ≤ x} b(x')`. The twin, who can compute `b` and hence `F`, recovers `x`. So a sequence
on which the gambler wins `S(x)` is compressed to fewer than `n - log S(x) + 1` bits. If the gambler
bets proportionally (`b = p`), the expected description length is less than `H(X₁, …, Xₙ) + 1`.

We work with any finite linearly ordered set of outcomes `X`, which covers the sequences of `n`
outcomes in lexicographic order (`Lex (Fin n → Bool)`).

## Implementation notes

The book encodes the first `k` bits of `F(x)`. We encode the smallest `k`-bit dyadic number
`⌈F(x⁻) 2^k⌉ / 2^k` at or above `F(x⁻) = ∑_{x' < x} b(x')`, which lies in `[F(x⁻), F(x))` and is
below `1`, so that it always has a `k`-bit binary expansion. The codewords identify the sequences
(the code is non-singular), but the code need not be a prefix code: as in the book, the decoder
knows `n` and hence where a description ends. Adding one bit gives the Shannon–Fano–Elias code,
which is a prefix code (`sfeCode`).

## Main definitions

* `gamblerCode b`: the description of the outcome `x` derived from the bets `b`.

## Main statements

* `gamblerCode_injective`: the twin recovers the outcome from its description.
* `length_gamblerCode_lt`: the description has fewer than `n - log₂ S(x) + 1` bits, where
  `S(x) = 2ⁿ b(x)` is the gambler's wealth.
* `expectedLength_gamblerCode_lt`: with proportional betting the expected description length is
  less than `H(X) + 1` bits.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 6.5
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {X : Type*} [Fintype X] [LinearOrder X]

/-- The integer `⌈F(x⁻) 2^k⌉`, with `k = ⌈log₂ (1/b(x))⌉`, whose `k`-bit binary expansion
describes `x`. -/
def gamblerNum (b : X → ℝ) (x : X) : ℕ := ⌈cdfLT b x * 2 ^ shannonLength 2 b x⌉₊

/-- **Section 6.5.** The description of the outcome `x` derived from the gambler's bets `b`: the
`k = ⌈log₂ (1/b(x))⌉` binary digits of a point of `[F(x⁻), F(x))`. -/
def gamblerCode (b : X → ℝ) (x : X) : List (Fin 2) :=
  natToWord 2 (shannonLength 2 b x) (gamblerNum b x)

@[simp] lemma length_gamblerCode (b : X → ℝ) (x : X) :
    (gamblerCode b x).length = shannonLength 2 b x :=
  length_natToWord _ _

/-- The dyadic point `⌈F(x⁻) 2^k⌉ / 2^k` lies in `[F(x⁻), F(x))`, since `2^{-k} ≤ b(x)`. -/
lemma gamblerNum_div_mem {b : X → ℝ} (hb : IsPMF b) {x : X} (hx : 0 < b x) :
    cdfLT b x ≤ gamblerNum b x / 2 ^ shannonLength 2 b x ∧
      (gamblerNum b x : ℝ) / 2 ^ shannonLength 2 b x < cdf b x := by
  set k := shannonLength 2 b x
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have h0 : 0 ≤ cdfLT b x * 2 ^ k := mul_nonneg (cdfLT_nonneg hb.nonneg x) hk.le
  have h1 := Nat.le_ceil (cdfLT b x * 2 ^ k)
  have h2 := Nat.ceil_lt_add_one h0
  have h3 := one_div_pow_shannonLength_le (D := 2) le_rfl hb hx
  push_cast at h3
  rw [one_div_pow, div_le_iff₀ hk] at h3
  rw [cdf_eq_cdfLT_add]
  constructor
  · rw [le_div_iff₀ hk]
    exact h1
  · rw [div_lt_iff₀ hk, add_mul]
    change ((gamblerNum b x : ℕ) : ℝ) < _ at h2
    linarith

lemma gamblerNum_lt {b : X → ℝ} (hb : IsPMF b) {x : X} (hx : 0 < b x) :
    gamblerNum b x < 2 ^ shannonLength 2 b x := by
  have h := (gamblerNum_div_mem hb hx).2.trans_le (cdf_le_one hb x)
  rw [div_lt_one (by positivity)] at h
  exact_mod_cast h

/-- **Section 6.5.** The identical twin recovers the outcome from its description: the
description map is injective. -/
theorem gamblerCode_injective {b : X → ℝ} (hb : IsPMF b) (hpos : ∀ x, 0 < b x) :
    Function.Injective (gamblerCode b) := by
  intro x y h
  have hk : shannonLength 2 b x = shannonLength 2 b y := by
    simpa using congrArg List.length h
  have hN : gamblerNum b x = gamblerNum b y := by
    have hv := congrArg (wordVal 2) h
    simp only [gamblerCode, wordVal_natToWord, Nat.mod_eq_of_lt (gamblerNum_lt hb (hpos _))]
      at hv
    exact hv
  have hval : (gamblerNum b x : ℝ) / 2 ^ shannonLength 2 b x =
      gamblerNum b y / 2 ^ shannonLength 2 b y := by
    rw [hN, hk]
  obtain ⟨hx1, hx2⟩ := gamblerNum_div_mem hb (hpos x)
  obtain ⟨hy1, hy2⟩ := gamblerNum_div_mem hb (hpos y)
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := cdf_le_cdfLT_of_lt hb.nonneg hxy
    linarith
  · exact hxy
  · have := cdf_le_cdfLT_of_lt hb.nonneg hxy
    linarith

/-- **Section 6.5.** If the gambler's wealth on the outcome `x` of `n` binary races is
`S(x) = 2ⁿ b(x)`, the description of `x` has `⌈n - log₂ S(x)⌉ < n - log₂ S(x) + 1` bits: about
`log₂ S(x)` bits are saved. -/
theorem length_gamblerCode_lt {b : X → ℝ} (hb : IsPMF b) {x : X} (hx : 0 < b x) (n : ℕ) :
    (gamblerCode b x).length = ⌈n - logb 2 (2 ^ n * b x)⌉₊ ∧
      ((gamblerCode b x).length : ℝ) < n - logb 2 (2 ^ n * b x) + 1 := by
  have hlog : n - logb 2 (2 ^ n * b x) = logb 2 (1 / b x) := by
    rw [logb_mul (by positivity) hx.ne', logb_pow, logb_self_eq_one one_lt_two, one_div,
      logb_inv]
    ring
  have h := (shannonLength_bounds (D := 2) le_rfl hb hx).2
  push_cast at h
  rw [length_gamblerCode, hlog]
  exact ⟨rfl, h⟩

/-- **Section 6.5.** With proportional betting `b = p`, the expected description length is less
than `H(X) + 1` bits. -/
theorem expectedLength_gamblerCode_lt {p : X → ℝ} (hp : IsPMF p) (hpos : ∀ x, 0 < p x) :
    expectedLength p (gamblerCode p) < entropyBase 2 p + 1 := by
  have h := (shannon_expectedLength_bounds (D := 2) le_rfl hp hpos).2
  push_cast at h
  simpa [expectedLength] using h

end InfoTheory
