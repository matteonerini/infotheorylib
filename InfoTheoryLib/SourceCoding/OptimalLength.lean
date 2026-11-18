/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.Kraft
public import InfoTheoryLib.RelativeEntropy.InformationInequality
public import InfoTheoryLib.AEP.Basic
public import InfoTheoryLib.StochasticProcess.Basic

/-!
# Optimal codeword lengths

The expected length `L = ∑ₓ p(x) l(x)` of a `D`-ary prefix code is at least the entropy `H_D(X)`,
and the Shannon code `l(x) = ⌈log_D (1/p(x))⌉` comes within one digit of it.

## Main definitions

* `kraftSum D l`: the Kraft sum `∑ₓ D^{-l(x)}`.
* `IsDAdic D p`: every probability is a power of `1/D`.
* `shannonLength D p x`: the Shannon codeword length `⌈log_D (1/p(x))⌉`.
* `minExpectedLength D p`: the minimal expected length `L*` over codeword lengths satisfying the
  Kraft inequality, i.e. over prefix codes.

## Main statements

* `entropyBase_le_expectedLength`, `entropyBase_eq_expectedLength_iff`: Theorem 5.3.1,
  `L ≥ H_D(X)` with equality iff `D^{-lᵢ} = pᵢ`.
* `entropyBase_le_sum_mul_real`: the bound for real-valued lengths, attained by
  `lᵢ* = -log_D pᵢ`, (5.13)–(5.20).
* `exists_lengths_eq_entropyBase_iff`: the entropy is attained iff the distribution is `D`-adic.
* `shannonLength_bounds`, `exists_prefixCode_shannon`: (5.27)–(5.32), the Shannon code.
* `minExpectedLength_bounds`: Theorem 5.4.1, `H_D(X) ≤ L* < H_D(X) + 1`.
* `minExpectedLength_iid_bounds`: (5.37), block coding of i.i.d. sources.
* `minExpectedLength_process_bounds`, `tendsto_minExpectedLength`: Theorem 5.4.2.
* `wrongCode_bounds`: Theorem 5.4.3, a code designed for `q` costs `D(p‖q)` extra digits.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 5.3 and
  5.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X : Type*} [Fintype X]

/-- The Kraft sum `∑ₓ D^{-l(x)}`. -/
def kraftSum (D : ℕ) (l : X → ℕ) : ℝ := ∑ x, (1 / D : ℝ) ^ l x

lemma one_div_pow_eq_rpow {D : ℕ} (hD : 0 < D) (n : ℕ) :
    (1 / D : ℝ) ^ n = (D : ℝ) ^ (-(n : ℝ)) := by
  rw [rpow_neg (by positivity), rpow_natCast, one_div, inv_pow]

/-! ### The entropy bound -/

/-- **(5.13)–(5.20).** For real-valued lengths with `∑ D^{-lᵢ} ≤ 1`, `∑ pᵢ lᵢ ≥ H_D(p)`, with
equality iff `pᵢ = D^{-lᵢ}`. The key identity is `L - H_D = D(p‖r) / log D + log_D (1/c)`
with `c = ∑ D^{-lᵢ}` and `rᵢ = D^{-lᵢ}/c`, (5.22)–(5.25). -/
theorem entropyBase_le_sum_mul_real {p : X → ℝ} (hp : IsPMF p) {D : ℕ} (hD : 2 ≤ D)
    (l : X → ℝ) (hk : ∑ x, (D : ℝ) ^ (-l x) ≤ 1) :
    entropyBase D p ≤ ∑ x, p x * l x ∧
      (entropyBase D p = ∑ x, p x * l x ↔ ∀ x, p x = (D : ℝ) ^ (-l x)) := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hlogD : 0 < log (D : ℝ) := log_pos hD1
  have : Nonempty X := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  set c := ∑ x, (D : ℝ) ^ (-l x)
  have hc : 0 < c := sum_pos (fun x _ => rpow_pos_of_pos hD0 _) univ_nonempty
  set r : X → ℝ := fun x => (D : ℝ) ^ (-l x) / c
  have hr : IsPMF r := ⟨fun x => div_nonneg (rpow_pos_of_pos hD0 _).le hc.le, by
    simp only [r, ← sum_div]; exact div_self hc.ne'⟩
  have hrpos : ∀ x, 0 < r x := fun x => div_pos (rpow_pos_of_pos hD0 _) hc
  have habs : AbsCont p r := fun x hx => absurd hx (hrpos x).ne'
  -- `(L log D - H) = D(p‖r) - log c`.
  have key : (∑ x, p x * l x) * log D - entropy p = relEntropyReal p r - log c := by
    have hterm : ∀ x, p x * log (p x / r x) =
        p x * log (p x) + p x * l x * log D + p x * log c := by
      intro x
      rcases (hp.nonneg x).eq_or_lt with h | h
      · simp [← h]
      · rw [log_div h.ne' (hrpos x).ne', log_div (rpow_pos_of_pos hD0 _).ne' hc.ne',
          log_rpow hD0]
        ring
    rw [relEntropyReal]
    simp only [hterm, sum_add_distrib, ← sum_mul, hp.sum_eq_one, one_mul, entropy]
    ring
  have hlogc : log c ≤ 0 := log_nonpos hc.le hk
  have hrel := relEntropyReal_nonneg hp hr habs
  rw [entropyBase_eq_div]
  have hle : entropy p / log D ≤ ∑ x, p x * l x := by
    rw [div_le_iff₀ hlogD]; linarith
  refine ⟨hle, ⟨fun heq => ?_, fun h => ?_⟩⟩
  · have h0 : (∑ x, p x * l x) * log D - entropy p = 0 := by
      rw [← heq, div_mul_cancel₀ _ hlogD.ne', sub_self]
    have hrel0 : relEntropyReal p r = 0 := by linarith
    have hc1 : log c = 0 := by linarith
    have hpr := (relEntropyReal_eq_zero_iff hp hr habs).1 hrel0
    have hc1' : c = 1 := by
      rcases log_eq_zero.1 hc1 with h | h | h
      · exact absurd h hc.ne'
      · exact h
      · linarith
    intro x
    rw [hpr]; simp [r, hc1']
  · have hpr : p = r := by
      have hc1 : c = 1 := by rw [← hp.sum_eq_one]; exact (sum_congr rfl fun x _ => (h x).symm)
      funext x; simp [r, hc1, h x]
    have : relEntropyReal p r = 0 := by rw [hpr]; exact relEntropyReal_self r
    have hc1 : c = 1 := by rw [← hp.sum_eq_one]; exact (sum_congr rfl fun x _ => (h x).symm)
    rw [hc1, log_one, sub_zero, this] at key
    field_simp
    linarith

/-- **Theorem 5.3.1, (5.21).** The expected length of a `D`-ary instantaneous code is at least the
entropy: if `∑ₓ D^{-l(x)} ≤ 1`, then `∑ₓ p(x) l(x) ≥ H_D(X)`. -/
theorem entropyBase_le_expectedLength {p : X → ℝ} (hp : IsPMF p) {D : ℕ} (hD : 2 ≤ D)
    (l : X → ℕ) (hk : kraftSum D l ≤ 1) : entropyBase D p ≤ ∑ x, p x * l x := by
  have hD0 : 0 < D := by omega
  refine (entropyBase_le_sum_mul_real hp hD (fun x => l x) ?_).1
  simpa [kraftSum, one_div_pow_eq_rpow hD0] using hk

/-- **Theorem 5.3.1 (equality).** `L = H_D(X)` iff `D^{-lᵢ} = pᵢ`. -/
theorem entropyBase_eq_expectedLength_iff {p : X → ℝ} (hp : IsPMF p) {D : ℕ} (hD : 2 ≤ D)
    (l : X → ℕ) (hk : kraftSum D l ≤ 1) :
    entropyBase D p = ∑ x, p x * l x ↔ ∀ x, p x = (1 / D : ℝ) ^ l x := by
  have hD0 : 0 < D := by omega
  have := (entropyBase_le_sum_mul_real hp hD (fun x => l x) (by
    simpa [kraftSum, one_div_pow_eq_rpow hD0] using hk)).2
  simpa [one_div_pow_eq_rpow hD0] using this

/-- **(5.19)–(5.20).** The non-integer lengths `lᵢ* = log_D (1/pᵢ)` give expected length exactly
`H_D(X)`. -/
lemma sum_mul_logb_inv_eq_entropyBase (p : X → ℝ) (D : ℕ) :
    ∑ x, p x * logb D (1 / p x) = entropyBase D p := by
  simp [entropyBase, one_div, logb_inv, sum_neg_distrib]

/-- **Definition.** A distribution is `D`-adic if each probability is `D^{-n}` for some `n`. -/
def IsDAdic (D : ℕ) (p : X → ℝ) : Prop := ∀ x, ∃ n : ℕ, p x = (1 / D : ℝ) ^ n

/-- **Theorem 5.3.1.** Some codeword lengths satisfying the Kraft inequality achieve `L = H_D(X)`
iff the distribution of `X` is `D`-adic. -/
theorem exists_lengths_eq_entropyBase_iff {p : X → ℝ} (hp : IsPMF p) {D : ℕ} (hD : 2 ≤ D) :
    (∃ l : X → ℕ, kraftSum D l ≤ 1 ∧ ∑ x, p x * l x = entropyBase D p) ↔ IsDAdic D p := by
  constructor
  · rintro ⟨l, hk, heq⟩ x
    exact ⟨l x, (entropyBase_eq_expectedLength_iff hp hD l hk).1 heq.symm x⟩
  · intro h
    choose l hl using h
    have hk : kraftSum D l ≤ 1 := by
      have : kraftSum D l = ∑ x, p x := sum_congr rfl fun x _ => (hl x).symm
      rw [this, hp.sum_eq_one]
    exact ⟨l, hk, ((entropyBase_eq_expectedLength_iff hp hD l hk).2 hl).symm⟩

/-! ### The Shannon code -/

/-- **(5.29)** The Shannon codeword length `⌈log_D (1/p(x))⌉`. -/
def shannonLength (D : ℕ) (p : X → ℝ) (x : X) : ℕ := ⌈logb D (1 / p x)⌉₊

lemma logb_one_div_nonneg {D : ℕ} (hD : 2 ≤ D) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    0 ≤ logb D (1 / t) :=
  logb_nonneg (by exact_mod_cast (by omega : 1 < D)) (by rw [le_div_iff₀ h0]; linarith)

/-- **(5.31)** `log_D (1/p) ≤ l < log_D (1/p) + 1`. -/
lemma shannonLength_bounds {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p) {x : X}
    (hx : 0 < p x) :
    logb D (1 / p x) ≤ shannonLength D p x ∧ (shannonLength D p x : ℝ) < logb D (1 / p x) + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (logb_one_div_nonneg hD hx (hp.le_one x))⟩

omit [Fintype X] in
/-- For a `D`-adic probability `p(x) = D^{-k}`, the Shannon length is `k = log_D (1/p(x))`. -/
lemma shannonLength_of_eq_pow {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} {x : X} {k : ℕ}
    (h : p x = (1 / D : ℝ) ^ k) : shannonLength D p x = k := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  rw [shannonLength, h, one_div_pow, one_div_one_div, logb_pow, logb_self_eq_one hD1, mul_one,
    Nat.ceil_natCast]

omit [Fintype X] in
/-- The Shannon length is `k ≥ 1` iff `D^{k-1} < 1/p(x) ≤ D^k`. -/
lemma shannonLength_eq_iff {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} {x : X} (hx : 0 < p x) {k : ℕ}
    (hk : k ≠ 0) :
    shannonLength D p x = k ↔ (D : ℝ) ^ (k - 1) < 1 / p x ∧ 1 / p x ≤ (D : ℝ) ^ k := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  rw [shannonLength, Nat.ceil_eq_iff hk, lt_logb_iff_rpow_lt hD1 (by positivity),
    logb_le_iff_le_rpow hD1 (by positivity), rpow_natCast, rpow_natCast]

/-- **(5.30)** `D^{-l(x)} ≤ p(x)` for the Shannon lengths, so they satisfy the Kraft inequality. -/
lemma one_div_pow_shannonLength_le {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p) {x : X}
    (hx : 0 < p x) : (1 / D : ℝ) ^ shannonLength D p x ≤ p x := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast hD
  have hD0 : 0 < D := by omega
  rw [one_div_pow_eq_rpow hD0]
  calc (D : ℝ) ^ (-(shannonLength D p x : ℝ)) ≤ (D : ℝ) ^ (-logb D (1 / p x)) :=
        rpow_le_rpow_of_exponent_le hD1.le (neg_le_neg (shannonLength_bounds hD hp hx).1)
    _ = p x := by
        rw [rpow_neg (by linarith), rpow_logb (by linarith) hD1.ne' (by positivity)]
        simp

lemma kraftSum_shannonLength_le {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p)
    (hpos : ∀ x, 0 < p x) : kraftSum D (shannonLength D p) ≤ 1 := by
  rw [kraftSum]
  exact (sum_le_sum fun x _ => one_div_pow_shannonLength_le hD hp (hpos x)).trans
    hp.sum_eq_one.le

/-- **(5.32)** The Shannon code has `H_D(X) ≤ L < H_D(X) + 1`. -/
theorem shannon_expectedLength_bounds {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p)
    (hpos : ∀ x, 0 < p x) :
    entropyBase D p ≤ ∑ x, p x * shannonLength D p x ∧
      ∑ x, p x * shannonLength D p x < entropyBase D p + 1 := by
  refine ⟨entropyBase_le_expectedLength hp hD _ (kraftSum_shannonLength_le hD hp hpos), ?_⟩
  have : Nonempty X := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  have h1 : ∑ x, p x * shannonLength D p x < ∑ x, p x * (logb D (1 / p x) + 1) :=
    sum_lt_sum_of_nonempty univ_nonempty fun x _ =>
      mul_lt_mul_of_pos_left (shannonLength_bounds hD hp (hpos x)).2 (hpos x)
  have h2 : ∑ x, p x * (logb D (1 / p x) + 1) = entropyBase D p + 1 := by
    simp only [mul_add_one, sum_add_distrib, sum_mul_logb_inv_eq_entropyBase, hp.sum_eq_one]
  linarith

/-- **(5.27)** There is a `D`-ary prefix code with `H_D(X) ≤ L < H_D(X) + 1`: the Shannon code. -/
theorem exists_prefixCode_shannon {α : Type*} [Fintype α] (hα : 2 ≤ Fintype.card α)
    {p : X → ℝ} (hp : IsPMF p) (hpos : ∀ x, 0 < p x) :
    ∃ C : X → List α, IsPrefixCode C ∧
      entropyBase (Fintype.card α) p ≤ expectedLength p C ∧
        expectedLength p C < entropyBase (Fintype.card α) p + 1 := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨C, hC, hl⟩ := exists_prefixCode_of_kraft (shannonLength (Fintype.card α) p)
    (kraftSum_shannonLength_le hα hp hpos)
  refine ⟨C, hC, ?_⟩
  simpa [expectedLength, hl] using shannon_expectedLength_bounds hα hp hpos

/-! ### The optimal expected length -/

/-- The minimal expected length `L* = min ∑ₓ p(x) l(x)` over codeword lengths satisfying the
Kraft inequality, that is, over `D`-ary prefix (or uniquely decodable) codes. -/
def minExpectedLength (D : ℕ) (p : X → ℝ) : ℝ :=
  sInf {L | ∃ l : X → ℕ, kraftSum D l ≤ 1 ∧ L = ∑ x, p x * l x}

lemma kraftSum_const_card_le {D : ℕ} (hD : 2 ≤ D) :
    kraftSum D (fun _ : X => Fintype.card X) ≤ 1 := by
  rw [kraftSum, sum_const, card_univ, nsmul_eq_mul]
  have h2 : (1 / D : ℝ) ^ Fintype.card X ≤ (1 / 2) ^ Fintype.card X :=
    pow_le_pow_left₀ (by positivity)
      (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hD)) _
  have h3 : (Fintype.card X : ℝ) * (1 / 2) ^ Fintype.card X ≤ 1 := by
    rw [one_div_pow, mul_one_div, div_le_one (by positivity)]
    exact_mod_cast (Nat.lt_two_pow_self).le
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / D by positivity) (Fintype.card X)]

lemma minExpectedLength_set_nonempty {D : ℕ} (hD : 2 ≤ D) (p : X → ℝ) :
    {L | ∃ l : X → ℕ, kraftSum D l ≤ 1 ∧ L = ∑ x, p x * l x}.Nonempty :=
  ⟨_, fun _ => Fintype.card X, kraftSum_const_card_le hD, rfl⟩

lemma minExpectedLength_set_bddBelow {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p) :
    BddBelow {L | ∃ l : X → ℕ, kraftSum D l ≤ 1 ∧ L = ∑ x, p x * l x} :=
  ⟨entropyBase D p, by rintro _ ⟨l, hk, rfl⟩; exact entropyBase_le_expectedLength hp hD l hk⟩

lemma le_minExpectedLength {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p) :
    entropyBase D p ≤ minExpectedLength D p :=
  le_csInf (minExpectedLength_set_nonempty hD p) (by
    rintro _ ⟨l, hk, rfl⟩; exact entropyBase_le_expectedLength hp hD l hk)

lemma minExpectedLength_le {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p) {l : X → ℕ}
    (hk : kraftSum D l ≤ 1) : minExpectedLength D p ≤ ∑ x, p x * l x :=
  csInf_le (minExpectedLength_set_bddBelow hD hp) ⟨l, hk, rfl⟩

/-- The optimal expected length is at most the expected length of any uniquely decodable (in
particular any prefix) code over an alphabet of size `D`. -/
lemma minExpectedLength_le_expectedLength {α : Type*} [Fintype α] (hα : 2 ≤ Fintype.card α)
    {p : X → ℝ} (hp : IsPMF p) {C : X → List α} (hC : IsUniquelyDecodableCode C) :
    minExpectedLength (Fintype.card α) p ≤ expectedLength p C := by
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  exact minExpectedLength_le hα hp (l := fun x => (C x).length)
    (kraft_of_isUniquelyDecodableCode hC)

/-- **Theorem 5.4.1, (5.33).** The optimal expected length satisfies `H_D(X) ≤ L* < H_D(X) + 1`.
We assume `p > 0`: with a symbol of probability `0` the strict upper bound can fail, e.g. for
`p = (1, 0)` and `D = 2`, where `H = 0` and `L* = 1`. -/
theorem minExpectedLength_bounds {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p)
    (hpos : ∀ x, 0 < p x) :
    entropyBase D p ≤ minExpectedLength D p ∧ minExpectedLength D p < entropyBase D p + 1 :=
  ⟨le_minExpectedLength hD hp, (minExpectedLength_le hD hp
    (kraftSum_shannonLength_le hD hp hpos)).trans_lt (shannon_expectedLength_bounds hD hp hpos).2⟩

/-! ### The wrong code -/

/-- **Theorem 5.4.3, (5.42).** The code `l(x) = ⌈log_D (1/q(x))⌉` designed for `q` has, under
`p`, expected length between `H_D(p) + D_D(p‖q)` and `H_D(p) + D_D(p‖q) + 1`, where
`D_D(p‖q) = D(p‖q) / log D`. -/
theorem wrongCode_bounds {D : ℕ} (hD : 2 ≤ D) {p q : X → ℝ} (hp : IsPMF p) (hq : IsPMF q)
    (hqpos : ∀ x, 0 < q x) :
    entropyBase D p + relEntropyReal p q / log D ≤ ∑ x, p x * shannonLength D q x ∧
      ∑ x, p x * shannonLength D q x < entropyBase D p + relEntropyReal p q / log D + 1 := by
  have hlogD : 0 < log (D : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < D))
  have : Nonempty X := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  -- `∑ p log_D (1/q) = H_D(p) + D_D(p‖q)`.
  have hid : ∑ x, p x * logb D (1 / q x) = entropyBase D p + relEntropyReal p q / log D := by
    rw [entropyBase_eq_div, relEntropyReal, ← add_div, entropy, ← sum_neg_distrib,
      ← sum_add_distrib, sum_div]
    refine sum_congr rfl fun x _ => ?_
    rcases (hp.nonneg x).eq_or_lt with h | h
    · simp [← h]
    · rw [logb, log_div h.ne' (hqpos x).ne', one_div, log_inv]
      ring
  constructor
  · rw [← hid]
    exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
      (shannonLength_bounds hD hq (hqpos x)).1 (hp.nonneg x)
  · obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < p x := by
      by_contra! h
      have := hp.sum_eq_one
      rw [sum_eq_zero fun x _ => le_antisymm (h x) (hp.nonneg x)] at this
      exact zero_ne_one this
    have h1 : ∑ x, p x * shannonLength D q x < ∑ x, p x * (logb D (1 / q x) + 1) :=
      sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left
        (shannonLength_bounds hD hq (hqpos x)).2.le (hp.nonneg x))
        ⟨x₀, mem_univ _, mul_lt_mul_of_pos_left (shannonLength_bounds hD hq (hqpos x₀)).2 hx₀⟩
    have h2 : ∑ x, p x * (logb D (1 / q x) + 1) =
        entropyBase D p + relEntropyReal p q / log D + 1 := by
      simp only [mul_add_one, sum_add_distrib, hid, hp.sum_eq_one]
    linarith

/-- Without assuming `p > 0`, the optimal expected length still satisfies
`L* ≤ H_D(X) + 1`: code with the mixture `q = (1 - ε) p + ε u` and let `ε → 0`. -/
theorem minExpectedLength_le_add_one {D : ℕ} (hD : 2 ≤ D) {p : X → ℝ} (hp : IsPMF p) :
    minExpectedLength D p ≤ entropyBase D p + 1 := by
  have : Nonempty X := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  have hlogD : 0 < log (D : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < D))
  have hu := uniformPMF_isPMF (α := X)
  have hupos : ∀ x, 0 < uniformPMF X x := fun x => by
    simp [uniformPMF, Fintype.card_pos]
  -- For `ε ∈ (0, 1)`, `L* < H_D(p) + 1 - log (1 - ε) / log D`.
  have hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      minExpectedLength D p ≤ entropyBase D p + 1 - log (1 - ε) / log D := by
    intro ε hε0 hε1
    set q : X → ℝ := fun x => (1 - ε) * p x + ε * uniformPMF X x
    have hq : IsPMF q := ⟨fun x => by
      have := hp.nonneg x; have := hu.nonneg x; simp only [q]; nlinarith, by
      simp [q, sum_add_distrib, ← mul_sum, hp.sum_eq_one, hu.sum_eq_one]⟩
    have hqpos : ∀ x, 0 < q x := fun x => by
      have := hp.nonneg x; have := hupos x; simp only [q]; nlinarith
    have hD' : relEntropyReal p q ≤ -log (1 - ε) := by
      have hsum : ∑ x, p x * (-log (1 - ε)) = -log (1 - ε) := by
        rw [← sum_mul, hp.sum_eq_one, one_mul]
      rw [relEntropyReal, ← hsum]
      refine sum_le_sum fun x _ => ?_
      rcases (hp.nonneg x).eq_or_lt with h | h
      · simp [← h]
      · refine mul_le_mul_of_nonneg_left ?_ h.le
        have : p x / q x ≤ 1 / (1 - ε) := by
          rw [div_le_div_iff₀ (hqpos x) (by linarith)]
          have := hupos x
          simp only [q]; nlinarith
        calc log (p x / q x) ≤ log (1 / (1 - ε)) :=
              log_le_log (div_pos h (hqpos x)) this
          _ = -log (1 - ε) := by rw [one_div, log_inv]
    have h1 := (wrongCode_bounds hD hp hq hqpos).2
    have h2 := minExpectedLength_le hD hp (kraftSum_shannonLength_le hD hq hqpos)
    have h3 : relEntropyReal p q / log D ≤ -log (1 - ε) / log D :=
      div_le_div_of_nonneg_right hD' hlogD.le
    rw [neg_div] at h3
    linarith
  -- Let `ε → 0`.
  have hlim : Tendsto (fun ε : ℝ => entropyBase D p + 1 - log (1 - ε) / log D)
      (𝓝[>] 0) (𝓝 (entropyBase D p + 1 - log (1 - 0) / log D)) := by
    refine (tendsto_const_nhds.sub (((continuousAt_const.sub continuousAt_id).log
      (by norm_num)).tendsto.div_const _)).mono_left nhdsWithin_le_nhds
  rw [sub_zero, log_one, zero_div, sub_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact hbound ε hε.1 hε.2

/-! ### Block coding -/

/-- **(5.37)** For `n` i.i.d. symbols coded as one block, the optimal expected length per symbol
satisfies `H_D(X) ≤ L*ₙ / n < H_D(X) + 1/n`. -/
theorem minExpectedLength_iid_bounds {α : Type*} [Fintype α] {D : ℕ} (hD : 2 ≤ D)
    {p : α → ℝ} (hp : IsPMF p) (hpos : ∀ a, 0 < p a) {n : ℕ} (hn : 0 < n) :
    entropyBase D p ≤ minExpectedLength D (iidPMF p n) / n ∧
      minExpectedLength D (iidPMF p n) / n < entropyBase D p + 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := iidPMF_isPMF hp n
  have hqpos : ∀ x, 0 < iidPMF p n x := fun x => prod_pos fun i _ => hpos (x i)
  have hH : entropyBase D (iidPMF p n) = n * entropyBase D p := by
    rw [entropyBase_eq_div, entropyBase_eq_div, entropy_iidPMF hp, mul_div_assoc]
  obtain ⟨h1, h2⟩ := minExpectedLength_bounds hD hq hqpos
  rw [hH] at h1 h2
  constructor
  · rw [le_div_iff₀ hn']; linarith
  · rw [div_lt_iff₀ hn', add_mul, one_div_mul_cancel hn'.ne']; linarith

/-- **(5.38)–(5.39)** For a stochastic process, the optimal expected length per symbol of codes for
blocks of `n` symbols satisfies `H_D(X₁, …, Xₙ)/n ≤ L*ₙ/n ≤ H_D(X₁, …, Xₙ)/n + 1/n`. The book's
upper bound is strict, which can fail when a block has probability `0`, as in
`minExpectedLength_bounds`. -/
theorem minExpectedLength_process_bounds {α : Type*} [Fintype α] {D : ℕ} (hD : 2 ≤ D)
    (P : StochasticProcess α) {n : ℕ} (hn : 0 < n) :
    P.jointEntropy n / log D / n ≤ minExpectedLength D (P.law n) / n ∧
      minExpectedLength D (P.law n) / n ≤ P.jointEntropy n / log D / n + 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := le_minExpectedLength hD (P.isPMF n)
  have h2 := minExpectedLength_le_add_one hD (P.isPMF n)
  rw [entropyBase_eq_div] at h1 h2
  constructor
  · exact div_le_div_of_nonneg_right h1 hn'.le
  · rw [← add_div]; exact div_le_div_of_nonneg_right h2 hn'.le

/-- **Theorem 5.4.2, (5.41).** For a stationary process the minimal expected codeword length per
symbol tends to the entropy rate, `L*ₙ / n → H(𝒳)` (in base `D`). -/
theorem tendsto_minExpectedLength {α : Type*} [Fintype α] {D : ℕ} (hD : 2 ≤ D)
    {P : StochasticProcess α} (hP : P.IsStationary) :
    Tendsto (fun n : ℕ => minExpectedLength D (P.law n) / n) atTop
      (𝓝 (P.entropyRate / log D)) := by
  have hrate := hP.hasEntropyRate
  have hlow : Tendsto (fun n : ℕ => P.jointEntropy n / log D / n) atTop
      (𝓝 (P.entropyRate / log D)) := by
    have := hrate.div_const (log D)
    refine this.congr fun n => ?_
    ring
  have hup : Tendsto (fun n : ℕ => P.jointEntropy n / log D / n + 1 / n) atTop
      (𝓝 (P.entropyRate / log D)) := by
    simpa using hlow.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (minExpectedLength_process_bounds hD P hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (minExpectedLength_process_bounds hD P hn).2

end InfoTheory
