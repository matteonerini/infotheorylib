/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.OptimalLength

/-!
# Shannon–Fano–Elias coding

Let the symbols of `X` be linearly ordered and have positive probabilities. The cumulative
distribution function `F` is a staircase with a step of height `p(x)` at each `x`. The
Shannon–Fano–Elias code describes `x` by the first `l(x) = ⌈log (1/p(x))⌉ + 1` bits of the
midpoint `F̄(x)` of its step. The dyadic interval of the codeword lies inside the step, so the
intervals of distinct codewords are disjoint and the code is a prefix code, with expected length
less than `H(X) + 2` bits.

The code alphabet is `Fin 2`, and a codeword `z₁ ⋯ z_l` stands for the number `0.z₁ ⋯ z_l`
(`wordVal 2 z / 2^l`).

## Main definitions

* `cdf p x`: the cumulative distribution function `F(x) = ∑_{a ≤ x} p(a)`, (5.72).
* `cdfLT p x`: `∑_{a < x} p(a)`, the bottom of the step of `F` at `x`.
* `midCdf p x`: the modified cumulative distribution function `F̄(x)`, (5.73).
* `truncBits l t`: `t` truncated to `l` binary digits, `⌊t⌋_l`.
* `sfeLength p x`, `sfeCode p x`: the Shannon–Fano–Elias codeword length and codeword.

## Main statements

* `midCdf_strictMono`: with positive probabilities, `F̄(x)` determines `x`.
* `sub_truncBits_lt`, `one_div_two_pow_sfeLength_le`: (5.74) and (5.75).
* `sfeNum_div_mem_step`: the interval of the codeword of `x` lies within the step at `x`.
* `wordVal_interval_of_prefix`: the interval of a word contains the intervals of its extensions.
* `sfeCode_isPrefixCode`: the Shannon–Fano–Elias code is a prefix code.
* `expectedLength_sfeCode_lt`: (5.76), `L < H(X) + 2` bits.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 5.9
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Words as dyadic intervals -/

/-- A word `u` over `Fin D` stands for the interval `[0.u, 0.u + D^{-|u|})`. If `u` is a prefix of
`v`, the interval of `v` lies within that of `u`. -/
lemma wordVal_interval_of_prefix {D : ℕ} (hD : 0 < D) {u v : List (Fin D)} (h : u <+: v) :
    (wordVal D u : ℝ) / D ^ u.length ≤ wordVal D v / D ^ v.length ∧
      (wordVal D v : ℝ) / D ^ v.length < (wordVal D u + 1) / D ^ u.length := by
  obtain ⟨t, rfl⟩ := h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have ht : (wordVal D t : ℝ) < (D : ℝ) ^ t.length := by exact_mod_cast wordVal_lt t
  have hu : (0 : ℝ) < (D : ℝ) ^ u.length := by positivity
  have hv : (0 : ℝ) < (D : ℝ) ^ t.length := by positivity
  rw [wordVal_append, List.length_append, pow_add]
  push_cast
  rw [add_div, mul_div_mul_right _ _ hv.ne']
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · rw [add_div (wordVal D u : ℝ)]
    refine add_lt_add_right ?_ _
    rw [div_lt_div_iff₀ (by positivity) hu]
    calc (wordVal D t : ℝ) * D ^ u.length < D ^ t.length * D ^ u.length :=
          mul_lt_mul_of_pos_right ht hu
      _ = 1 * (D ^ u.length * D ^ t.length) := by ring

variable {X : Type*} [Fintype X] [LinearOrder X]

/-! ### The cumulative distribution function -/

/-- **(5.72)** The cumulative distribution function `F(x) = ∑_{a ≤ x} p(a)`. -/
def cdf (p : X → ℝ) (x : X) : ℝ := ∑ a ∈ univ.filter (· ≤ x), p a

/-- The sum `∑_{a < x} p(a)` of the probabilities of the symbols below `x`: the bottom of the
step of `F` at `x` (`F(x - 1)` in the book). -/
def cdfLT (p : X → ℝ) (x : X) : ℝ := ∑ a ∈ univ.filter (· < x), p a

/-- **(5.73)** The modified cumulative distribution function `F̄(x) = ∑_{a < x} p(a) + p(x)/2`,
the midpoint of the step of `F` at `x`. -/
def midCdf (p : X → ℝ) (x : X) : ℝ := cdfLT p x + p x / 2

/-- The step of `F` at `x` has height `p(x)`. -/
lemma cdf_eq_cdfLT_add (p : X → ℝ) (x : X) : cdf p x = cdfLT p x + p x := by
  have : univ.filter (· ≤ x) = insert x (univ.filter (· < x)) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    exact le_iff_eq_or_lt
  rw [cdf, cdfLT, this, sum_insert (by simp), add_comm]

lemma cdfLT_nonneg {p : X → ℝ} (hp : ∀ a, 0 ≤ p a) (x : X) : 0 ≤ cdfLT p x :=
  sum_nonneg fun a _ => hp a

lemma midCdf_nonneg {p : X → ℝ} (hp : ∀ a, 0 ≤ p a) (x : X) : 0 ≤ midCdf p x :=
  add_nonneg (cdfLT_nonneg hp x) (by linarith [hp x])

lemma cdf_le_one {p : X → ℝ} (hp : IsPMF p) (x : X) : cdf p x ≤ 1 := by
  rw [← hp.sum_eq_one]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => hp.nonneg a

/-- The steps of `F` at `x < y` do not overlap: `F(x) ≤ ∑_{a < y} p(a)`. -/
lemma cdf_le_cdfLT_of_lt {p : X → ℝ} (hp : ∀ a, 0 ≤ p a) {x y : X} (h : x < y) :
    cdf p x ≤ cdfLT p y :=
  sum_le_sum_of_subset_of_nonneg (fun a ha => by
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact ha.trans_lt h) fun a _ _ => hp a

lemma cdfLT_lt_midCdf {p : X → ℝ} {x : X} (hx : 0 < p x) : cdfLT p x < midCdf p x := by
  rw [midCdf]; linarith

lemma midCdf_lt_cdf {p : X → ℝ} {x : X} (hx : 0 < p x) : midCdf p x < cdf p x := by
  rw [midCdf, cdf_eq_cdfLT_add]; linarith

/-- Since all the probabilities are positive, `F̄` is strictly monotone. -/
lemma midCdf_strictMono {p : X → ℝ} (hp : ∀ a, 0 < p a) : StrictMono (midCdf p) := fun x y h =>
  (midCdf_lt_cdf (hp x)).trans_le
    ((cdf_le_cdfLT_of_lt (fun a => (hp a).le) h).trans (cdfLT_lt_midCdf (hp y)).le)

/-- Since all the probabilities are positive, `F̄(a) ≠ F̄(b)` if `a ≠ b`, so `F̄(x)` determines `x`
and can be used as a code for `x`. -/
lemma midCdf_injective {p : X → ℝ} (hp : ∀ a, 0 < p a) : Function.Injective (midCdf p) :=
  (midCdf_strictMono hp).injective

/-! ### Truncation to `l` bits -/

/-- The number `t ≥ 0` truncated to `l` binary digits, `⌊t⌋_l = ⌊t 2^l⌋ / 2^l`. -/
def truncBits (l : ℕ) (t : ℝ) : ℝ := ⌊t * 2 ^ l⌋₊ / 2 ^ l

lemma truncBits_le (l : ℕ) {t : ℝ} (ht : 0 ≤ t) : truncBits l t ≤ t := by
  rw [truncBits, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

/-- **(5.74)** Truncating to `l` bits loses less than `2^{-l}`. -/
lemma sub_truncBits_lt (l : ℕ) (t : ℝ) : t - truncBits l t < 1 / 2 ^ l := by
  have h := Nat.lt_floor_add_one (t * 2 ^ l)
  rw [truncBits, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ (by positivity)]
  linarith

/-! ### The Shannon–Fano–Elias code -/

/-- **(5.75)** The Shannon–Fano–Elias codeword length `l(x) = ⌈log (1/p(x))⌉ + 1`. -/
def sfeLength (p : X → ℝ) (x : X) : ℕ := shannonLength 2 p x + 1

/-- The integer `⌊F̄(x) 2^{l(x)}⌋`, so that `⌊F̄(x)⌋_{l(x)} = sfeNum p x / 2^{l(x)}`. -/
def sfeNum (p : X → ℝ) (x : X) : ℕ := ⌊midCdf p x * 2 ^ sfeLength p x⌋₊

/-- **Shannon–Fano–Elias code.** The codeword of `x` is the first `l(x)` bits of `F̄(x)`, the
`l(x)`-digit binary expansion of `⌊F̄(x) 2^{l(x)}⌋`. -/
def sfeCode (p : X → ℝ) (x : X) : List (Fin 2) := natToWord 2 (sfeLength p x) (sfeNum p x)

@[simp] lemma length_sfeCode (p : X → ℝ) (x : X) : (sfeCode p x).length = sfeLength p x :=
  length_natToWord _ _

lemma truncBits_midCdf (p : X → ℝ) (x : X) :
    truncBits (sfeLength p x) (midCdf p x) = sfeNum p x / 2 ^ sfeLength p x := rfl

omit [LinearOrder X] in
/-- **(5.75)** `2^{-l(x)} ≤ p(x)/2 = F̄(x) - F(x - 1)`. -/
lemma one_div_two_pow_sfeLength_le {p : X → ℝ} (hp : IsPMF p) {x : X} (hx : 0 < p x) :
    (1 / 2 : ℝ) ^ sfeLength p x ≤ p x / 2 := by
  have h := one_div_pow_shannonLength_le (D := 2) le_rfl hp hx
  push_cast at h
  rw [sfeLength, pow_succ]
  linarith

/-- The interval `[⌊F̄(x)⌋_{l(x)}, ⌊F̄(x)⌋_{l(x)} + 2^{-l(x)})` of the codeword of `x` lies within
the step of `F` at `x`: the truncation lies in the lower half of the step, and the interval is
at most half as long as the step. -/
lemma sfeNum_div_mem_step {p : X → ℝ} (hp : IsPMF p) {x : X} (hx : 0 < p x) :
    cdfLT p x < sfeNum p x / 2 ^ sfeLength p x ∧
      (sfeNum p x + 1 : ℝ) / 2 ^ sfeLength p x ≤ cdf p x := by
  have h1 := sub_truncBits_lt (sfeLength p x) (midCdf p x)
  have h2 := truncBits_le (sfeLength p x) (midCdf_nonneg hp.nonneg x)
  have h3 := one_div_two_pow_sfeLength_le hp hx
  rw [one_div_pow] at h3
  rw [truncBits_midCdf] at h1 h2
  rw [midCdf] at h1 h2
  constructor
  · linarith
  · rw [add_div, cdf_eq_cdfLT_add]
    linarith

lemma sfeNum_lt {p : X → ℝ} (hp : IsPMF p) {x : X} (hx : 0 < p x) :
    sfeNum p x < 2 ^ sfeLength p x := by
  have h := (sfeNum_div_mem_step hp hx).2.trans (cdf_le_one hp x)
  rw [div_le_one (by positivity)] at h
  exact_mod_cast (show (sfeNum p x : ℝ) < 2 ^ sfeLength p x by linarith)

lemma wordVal_sfeCode {p : X → ℝ} (hp : IsPMF p) {x : X} (hx : 0 < p x) :
    wordVal 2 (sfeCode p x) = sfeNum p x := by
  rw [sfeCode, wordVal_natToWord, Nat.mod_eq_of_lt (sfeNum_lt hp hx)]

/-- **Section 5.9.** The Shannon–Fano–Elias code is a prefix code: the intervals of distinct
codewords lie within distinct steps of `F`, so they are disjoint. -/
theorem sfeCode_isPrefixCode {p : X → ℝ} (hp : IsPMF p) (hpos : ∀ x, 0 < p x) :
    IsPrefixCode (sfeCode p) := by
  intro x y h
  have hI := wordVal_interval_of_prefix two_pos h
  simp only [length_sfeCode, wordVal_sfeCode hp (hpos _), Nat.cast_ofNat] at hI
  obtain ⟨hx1, hx2⟩ := sfeNum_div_mem_step hp (hpos x)
  obtain ⟨hy1, hy2⟩ := sfeNum_div_mem_step hp (hpos y)
  have hy3 : (sfeNum p y : ℝ) / 2 ^ sfeLength p y < (sfeNum p y + 1) / 2 ^ sfeLength p y :=
    div_lt_div_of_pos_right (by linarith) (by positivity)
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := cdf_le_cdfLT_of_lt hp.nonneg hxy
    linarith
  · exact hxy
  · have := cdf_le_cdfLT_of_lt hp.nonneg hxy
    linarith

/-- **(5.76)** The Shannon–Fano–Elias code has expected length `L < H(X) + 2` bits. -/
theorem expectedLength_sfeCode_lt {p : X → ℝ} (hp : IsPMF p) (hpos : ∀ x, 0 < p x) :
    expectedLength p (sfeCode p) < entropyBase 2 p + 2 := by
  have h := (shannon_expectedLength_bounds (D := 2) le_rfl hp hpos).2
  push_cast at h
  have : expectedLength p (sfeCode p) = ∑ x, p x * shannonLength 2 p x + 1 := by
    simp only [expectedLength, length_sfeCode, sfeLength]
    push_cast
    simp only [mul_add_one, sum_add_distrib, hp.sum_eq_one]
  rw [this]
  linarith

end InfoTheory
