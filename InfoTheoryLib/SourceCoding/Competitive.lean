/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.OptimalLength
public import InfoTheoryLib.Probability.Event

/-!
# Competitive optimality of the Shannon code

Huffman codes minimize the expected length, but this says nothing about individual source
symbols. Consider a game in which two players design codes for the same source, and a player
scores when its codeword for the drawn symbol is shorter. The binary Shannon code
`l(x) = ⌈log (1/p(x))⌉` does well in this game. No code beats it by `c` bits or more with
probability above `2^{1-c}`. For dyadic distributions, no uniquely decodable code is strictly
shorter more often than it is strictly longer.

Codes enter only through their codeword lengths `l'`, which satisfy the binary Kraft inequality
for every uniquely decodable code (`kraft_of_isUniquelyDecodableCode`).

## Main statements

* `prob_shannonLength_ge_add_le`: Theorem 5.10.1, `Pr(l(X) ≥ l'(X) + c) ≤ 2^{1-c}`, (5.77).
* `sign_le_two_zpow_sub_one`, `sign_eq_two_zpow_sub_one_iff`: `sgn(t) ≤ 2^t - 1` on the integers,
  with equality iff `t ∈ {0, 1}`, (5.87).
* `prob_lt_sub_prob_gt_eq`: `Pr(l' < l) - Pr(l' > l) = E sgn(l - l')`, (5.88)–(5.90).
* `expect_le_zero_of_dyadic`: for dyadic `p`, `E f(l(X) - l'(X)) ≤ 0` for every `f` with
  `f(t) ≤ 2^t - 1` on the integers (the closing remark of Section 5.10).
* `prob_gt_le_prob_lt_of_dyadic`, `prob_gt_eq_prob_lt_iff_of_dyadic`: Theorem 5.10.2, the Shannon
  code is uniquely competitively optimal for dyadic distributions, (5.85).
* `expect_sign_sub_one_le_zero`: the corollary (5.97) for general distributions.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 5.10
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {X : Type*} [Fintype X]

lemma kraftSum_two (l : X → ℕ) : kraftSum 2 l = ∑ x, (1 / 2 : ℝ) ^ l x := by
  simp only [kraftSum, Nat.cast_ofNat]

/-- For the binary Shannon lengths, `p(x) 2^{l(x)} < 2`, from `l(x) < log (1/p(x)) + 1`. -/
lemma mul_two_pow_shannonLength_lt {p : X → ℝ} (hp : IsPMF p) {x : X} (hx : 0 < p x) :
    p x * 2 ^ shannonLength 2 p x < 2 := by
  have h := (shannonLength_bounds (D := 2) le_rfl hp hx).2
  push_cast at h
  have h1 : (shannonLength 2 p x : ℝ) - 1 < logb 2 (1 / p x) := by linarith
  rw [lt_logb_iff_rpow_lt one_lt_two (by positivity), rpow_sub two_pos, rpow_natCast, rpow_one,
    lt_div_iff₀ hx] at h1
  calc p x * 2 ^ shannonLength 2 p x = 2 * (2 ^ shannonLength 2 p x / 2 * p x) := by ring
    _ < 2 * 1 := by gcongr
    _ = 2 := mul_one 2

/-! ### Theorem 5.10.1 -/

/-- **Theorem 5.10.1, (5.77)–(5.84).** Let `l` be the binary Shannon lengths and `l'` the lengths
of any other code (lengths satisfying the Kraft inequality). Then
`Pr(l(X) ≥ l'(X) + c) ≤ 2^{1-c}`. -/
theorem prob_shannonLength_ge_add_le {p : X → ℝ} (hp : IsPMF p) (l' : X → ℕ)
    (hl' : kraftSum 2 l' ≤ 1) (c : ℕ) :
    prob p (univ.filter fun x => l' x + c ≤ shannonLength 2 p x) ≤ (2 : ℝ) ^ (1 - (c : ℤ)) := by
  have key : ∀ x ∈ univ.filter (fun x => l' x + c ≤ shannonLength 2 p x),
      p x ≤ 2 * (1 / 2 : ℝ) ^ c * (1 / 2 : ℝ) ^ l' x := by
    intro x hx
    rw [mem_filter] at hx
    rcases (hp.nonneg x).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have h1 := mul_two_pow_shannonLength_lt hp h0
      have h2 : (2 : ℝ) ^ (l' x + c) ≤ 2 ^ shannonLength 2 p x := pow_le_pow_right₀ one_le_two hx.2
      have h3 : p x * 2 ^ (l' x + c) < 2 := (mul_le_mul_of_nonneg_left h2 h0.le).trans_lt h1
      rw [pow_add] at h3
      rw [one_div_pow, one_div_pow,
        show 2 * (1 / 2 ^ c) * (1 / 2 ^ l' x) = (2 : ℝ) / (2 ^ l' x * 2 ^ c) by ring,
        le_div_iff₀ (by positivity)]
      exact h3.le
  calc prob p (univ.filter fun x => l' x + c ≤ shannonLength 2 p x)
      ≤ ∑ x ∈ univ.filter (fun x => l' x + c ≤ shannonLength 2 p x),
          2 * (1 / 2 : ℝ) ^ c * (1 / 2 : ℝ) ^ l' x := sum_le_sum key
    _ ≤ ∑ x, 2 * (1 / 2 : ℝ) ^ c * (1 / 2 : ℝ) ^ l' x :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
    _ = 2 * (1 / 2 : ℝ) ^ c * kraftSum 2 l' := by rw [kraftSum_two, mul_sum]
    _ ≤ 2 * (1 / 2 : ℝ) ^ c * 1 := by gcongr
    _ = (2 : ℝ) ^ (1 - (c : ℤ)) := by
        rw [zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast, mul_one, one_div_pow, mul_one_div]

/-- **Theorem 5.10.1** for codes: the probability that a binary uniquely decodable code `C'` beats
the Shannon code by `c` or more bits is at most `2^{1-c}`. -/
theorem prob_shannonLength_ge_add_le_of_code {α : Type*} [Fintype α] (hα : Fintype.card α = 2)
    {p : X → ℝ} (hp : IsPMF p) {C' : X → List α} (hC' : IsUniquelyDecodableCode C') (c : ℕ) :
    prob p (univ.filter fun x => (C' x).length + c ≤ shannonLength 2 p x) ≤
      (2 : ℝ) ^ (1 - (c : ℤ)) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  have hk := kraft_of_isUniquelyDecodableCode hC'
  rw [hα] at hk
  exact prob_shannonLength_ge_add_le hp (fun x => (C' x).length) hk c

/-! ### The sign function -/

/-- **(5.87)** `sgn(t) ≤ 2^t - 1` for all integers `t` (Figure 5.6). -/
lemma sign_le_two_zpow_sub_one (t : ℤ) : (t.sign : ℝ) ≤ (2 : ℝ) ^ t - 1 := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · have := zpow_pos (two_pos : (0 : ℝ) < 2) t
    rw [Int.sign_eq_neg_one_of_neg h]
    push_cast
    linarith
  · simp
  · have : (2 : ℝ) ^ (1 : ℤ) ≤ 2 ^ t := zpow_le_zpow_right₀ one_le_two (by omega)
    rw [zpow_one] at this
    rw [Int.sign_eq_one_of_pos h]
    push_cast
    linarith

/-- Equality holds in `sgn(t) ≤ 2^t - 1` iff `t = 0` or `t = 1`. -/
lemma sign_eq_two_zpow_sub_one_iff (t : ℤ) : (t.sign : ℝ) = (2 : ℝ) ^ t - 1 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have := zpow_pos (two_pos : (0 : ℝ) < 2) t
      rw [Int.sign_eq_neg_one_of_neg ht] at h
      push_cast at h
      linarith
    · exact Or.inl rfl
    · rw [Int.sign_eq_one_of_pos ht] at h
      by_contra hne
      have : (2 : ℝ) ^ (2 : ℤ) ≤ 2 ^ t := zpow_le_zpow_right₀ one_le_two (by omega)
      push_cast at h
      norm_num at this
      linarith
  · rintro (rfl | rfl) <;> norm_num

/-- The integers satisfy `t ≤ 2^t - 1`. -/
lemma intCast_le_two_zpow_sub_one (t : ℤ) : (t : ℝ) ≤ (2 : ℝ) ^ t - 1 := by
  rcases le_or_gt 0 t with ht | ht
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) n
    rw [zpow_natCast]
    push_cast
    norm_num at this
    linarith
  · have h1 : (t : ℝ) ≤ -1 := by exact_mod_cast (by omega : t ≤ -1)
    have := zpow_pos (two_pos : (0 : ℝ) < 2) t
    linarith

/-- **(5.88)–(5.90)** `Pr(l'(X) < l(X)) - Pr(l'(X) > l(X)) = E sgn(l(X) - l'(X))`. -/
lemma prob_lt_sub_prob_gt_eq (p : X → ℝ) (l l' : X → ℕ) :
    prob p (univ.filter fun x => l' x < l x) - prob p (univ.filter fun x => l x < l' x) =
      ∑ x, p x * (((l x : ℤ) - l' x).sign : ℝ) := by
  simp only [prob, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rcases lt_trichotomy (l x) (l' x) with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg (by omega)]
    simp [h, not_lt_of_gt h]
  · simp [h]
  · rw [Int.sign_eq_one_of_pos (by omega)]
    simp [h, not_lt_of_gt h]

/-! ### Theorem 5.10.2 -/

omit [Fintype X] in
/-- For dyadic `p(x) = 2^{-l(x)}`, `p(x) (2^{l(x) - l'(x)} - 1) = 2^{-l'(x)} - p(x)`. -/
lemma mul_two_zpow_sub_one_of_dyadic {p : X → ℝ} {l l' : X → ℕ} (hl : ∀ x, p x = (1 / 2 : ℝ) ^ l x)
    (x : X) : p x * ((2 : ℝ) ^ ((l x : ℤ) - l' x) - 1) = (1 / 2 : ℝ) ^ l' x - p x := by
  rw [hl, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, one_div_pow, one_div_pow]
  field_simp

/-- **(5.91)–(5.96)** For a dyadic distribution `p(x) = 2^{-l(x)}` and lengths `l'` satisfying the
Kraft inequality, `E f(l(X) - l'(X)) ≤ 0` for every `f` with `f(t) ≤ 2^t - 1` on the integers;
for instance `f = sgn`, or `f(t) = t`, which gives `E l(X) ≤ E l'(X)`. -/
theorem expect_le_zero_of_dyadic {p : X → ℝ} {l l' : X → ℕ} (hl : ∀ x, p x = (1 / 2 : ℝ) ^ l x)
    (hsum : ∑ x, p x = 1) (hl' : kraftSum 2 l' ≤ 1) {f : ℤ → ℝ}
    (hf : ∀ t, f t ≤ (2 : ℝ) ^ t - 1) : ∑ x, p x * f ((l x : ℤ) - l' x) ≤ 0 := by
  calc ∑ x, p x * f ((l x : ℤ) - l' x)
      ≤ ∑ x, p x * ((2 : ℝ) ^ ((l x : ℤ) - l' x) - 1) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf _) (by rw [hl]; positivity)
    _ = ∑ x, (1 / 2 : ℝ) ^ l' x - ∑ x, p x := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun x _ => mul_two_zpow_sub_one_of_dyadic hl x
    _ ≤ 0 := by rw [hsum, ← kraftSum_two]; linarith

omit [Fintype X] in
lemma eq_one_div_two_pow_of_isDAdic {p : X → ℝ} (hd : IsDAdic 2 p) (x : X) :
    p x = (1 / 2 : ℝ) ^ shannonLength 2 p x := by
  obtain ⟨k, hk⟩ := hd x
  rw [shannonLength_of_eq_pow le_rfl hk, hk]
  push_cast
  rfl

/-- **Theorem 5.10.2, (5.85).** For a dyadic distribution, the binary Shannon code
`l(x) = log (1/p(x))` is competitively optimal: for the lengths `l'` of any other uniquely decodable
code, `Pr(l(X) < l'(X)) ≥ Pr(l(X) > l'(X))`. -/
theorem prob_gt_le_prob_lt_of_dyadic {p : X → ℝ} (hp : IsPMF p) (hd : IsDAdic 2 p) (l' : X → ℕ)
    (hl' : kraftSum 2 l' ≤ 1) :
    prob p (univ.filter fun x => l' x < shannonLength 2 p x) ≤
      prob p (univ.filter fun x => shannonLength 2 p x < l' x) := by
  have h := expect_le_zero_of_dyadic (eq_one_div_two_pow_of_isDAdic hd) hp.sum_eq_one hl'
    sign_le_two_zpow_sub_one
  rw [← prob_lt_sub_prob_gt_eq] at h
  linarith

/-- **Theorem 5.10.2, equality.** The Shannon code is *uniquely* competitively optimal: equality
holds in `Pr(l(X) < l'(X)) ≥ Pr(l(X) > l'(X))` iff `l' = l`. -/
theorem prob_gt_eq_prob_lt_iff_of_dyadic {p : X → ℝ} (hp : IsPMF p) (hd : IsDAdic 2 p)
    (l' : X → ℕ) (hl' : kraftSum 2 l' ≤ 1) :
    prob p (univ.filter fun x => l' x < shannonLength 2 p x) =
        prob p (univ.filter fun x => shannonLength 2 p x < l' x) ↔
      l' = shannonLength 2 p := by
  have hl := eq_one_div_two_pow_of_isDAdic hd
  set l := shannonLength 2 p
  have hpos : ∀ x, 0 < p x := fun x => by rw [hl]; positivity
  constructor
  · intro heq
    -- `g x = p(x) sgn(l(x) - l'(x)) ≤ d x = 2^{-l'(x)} - p(x)`, with `∑ g = 0` and `∑ d ≤ 0`.
    set g : X → ℝ := fun x => p x * (((l x : ℤ) - l' x).sign : ℝ)
    set d : X → ℝ := fun x => (1 / 2 : ℝ) ^ l' x - p x
    have hgd : ∀ x, g x ≤ d x := fun x => by
      change _ ≤ (1 / 2 : ℝ) ^ l' x - p x
      rw [← mul_two_zpow_sub_one_of_dyadic hl x]
      exact mul_le_mul_of_nonneg_left (sign_le_two_zpow_sub_one _) (hpos x).le
    have hg : ∑ x, g x = 0 := by rw [← prob_lt_sub_prob_gt_eq, heq, sub_self]
    have hd0 : ∑ x, d x ≤ 0 := by
      simp only [d, sum_sub_distrib, hp.sum_eq_one]
      rw [← kraftSum_two]
      linarith
    -- Equality in `sgn(t) ≤ 2^t - 1` everywhere, so `l'(x) ∈ {l(x) - 1, l(x)}`.
    have hzero : ∀ x, d x - g x = 0 := by
      have hsum : ∑ x, (d x - g x) = 0 := by
        refine le_antisymm ?_ (sum_nonneg fun x _ => sub_nonneg.2 (hgd x))
        rw [sum_sub_distrib, hg]
        linarith
      exact fun x => (sum_eq_zero_iff_of_nonneg fun x _ => sub_nonneg.2 (hgd x)).1 hsum x
        (mem_univ x)
    have hle : ∀ x, l' x ≤ l x := by
      intro x
      have h := hzero x
      simp only [d, g, ← mul_two_zpow_sub_one_of_dyadic hl x] at h
      have h' : (((l x : ℤ) - l' x).sign : ℝ) = 2 ^ ((l x : ℤ) - l' x) - 1 := by
        have := (hpos x).ne'
        have h2 : p x * ((2 : ℝ) ^ ((l x : ℤ) - l' x) - 1 - (((l x : ℤ) - l' x).sign : ℝ)) = 0 := by
          rw [mul_sub]; linarith
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 this
        · linarith
      rcases (sign_eq_two_zpow_sub_one_iff _).1 h' with h4 | h4 <;> omega
    -- Then `2^{-l'(x)} ≥ 2^{-l(x)}` and `∑ 2^{-l'(x)} ≤ 1 = ∑ 2^{-l(x)}` force `l' = l`.
    have hd_nonneg : ∀ x, 0 ≤ d x := fun x => by
      simp only [d, hl x, sub_nonneg]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hle x)
    have hd_zero : ∀ x, d x = 0 := fun x =>
      (sum_eq_zero_iff_of_nonneg fun x _ => hd_nonneg x).1
        (le_antisymm hd0 (sum_nonneg fun x _ => hd_nonneg x)) x (mem_univ x)
    funext x
    have h := hd_zero x
    simp only [d, hl x, sub_eq_zero] at h
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) h
  · intro h
    rw [h]

/-! ### The non-dyadic case -/

/-- **Corollary, (5.97).** For any distribution, the binary Shannon lengths
`l(x) = ⌈log (1/p(x))⌉` and the lengths `l'` of any other code satisfy
`E sgn(l(X) - l'(X) - 1) ≤ 0`. -/
theorem expect_sign_sub_one_le_zero {p : X → ℝ} (hp : IsPMF p) (l' : X → ℕ)
    (hl' : kraftSum 2 l' ≤ 1) :
    ∑ x, p x * (((shannonLength 2 p x : ℤ) - l' x - 1).sign : ℝ) ≤ 0 := by
  set l := shannonLength 2 p
  have key : ∀ x, p x * (((l x : ℤ) - l' x - 1).sign : ℝ) ≤ (1 / 2 : ℝ) ^ l' x - p x := by
    intro x
    rcases (hp.nonneg x).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    have hpl := mul_two_pow_shannonLength_lt hp h0
    have e : p x * (2 : ℝ) ^ ((l x : ℤ) - l' x - 1) = (p x * 2 ^ l x / 2) * (1 / 2) ^ l' x := by
      rw [zpow_sub₀ two_ne_zero, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, zpow_one,
        one_div_pow]
      field_simp
    have h1 : p x * 2 ^ l x / 2 ≤ 1 := by rw [div_le_one two_pos]; exact hpl.le
    calc p x * (((l x : ℤ) - l' x - 1).sign : ℝ)
        ≤ p x * ((2 : ℝ) ^ ((l x : ℤ) - l' x - 1) - 1) :=
          mul_le_mul_of_nonneg_left (sign_le_two_zpow_sub_one _) h0.le
      _ = (p x * 2 ^ l x / 2) * (1 / 2) ^ l' x - p x := by rw [mul_sub, e, mul_one]
      _ ≤ 1 * (1 / 2) ^ l' x - p x :=
          sub_le_sub_right (mul_le_mul_of_nonneg_right h1 (by positivity)) _
      _ = (1 / 2 : ℝ) ^ l' x - p x := by rw [one_mul]
  calc ∑ x, p x * (((l x : ℤ) - l' x - 1).sign : ℝ)
      ≤ ∑ x, ((1 / 2 : ℝ) ^ l' x - p x) := sum_le_sum fun x _ => key x
    _ ≤ 0 := by
        rw [sum_sub_distrib, hp.sum_eq_one, ← kraftSum_two]
        linarith

end InfoTheory
