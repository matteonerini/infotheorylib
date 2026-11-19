/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.TypicalSet
public import InfoTheoryLib.SourceCoding.FixedLength

/-!
# Data compression with the typical set

The typical set gives a simple one-to-one code for sequences of i.i.d. random variables. A
typical sequence is described by a flag bit `0` followed by its index in `A_ε^(n)`, which takes
about `n(H + ε)` bits. Any other sequence is described by a flag bit `1` followed by its index in
`𝒳ⁿ`, which takes about `n log |𝒳|` bits. Since the typical set has probability close to `1`, the
expected length per symbol is close to `H`.

## Main definitions

* `typicalSetCode p n ε`: the code described above, mapping `𝒳ⁿ` to binary strings.

## Main statements

* `typicalSetCode_injective`: the code is one-to-one, hence invertible.
* `length_typicalSetCode_of_mem`: typical sequences have descriptions of length at most
  `n(H + ε) + 2` bits.
* `expect_length_typicalSetCode_le`: the expected length is at most
  `n(H + ε) + Pr{(A_ε^(n))ᶜ} n log |𝒳| + 2` bits, (3.17)–(3.21).
* `exists_code_expect_length_le`: Theorem 3.2.1, there are one-to-one codes with
  `E[(1/n) l(Xⁿ)] ≤ H + ε` for `n` large.

## Implementation notes

Codeword lengths are numbers of bits, so in this file entropies are converted to bits by dividing
by `log 2`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 3.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- The number `⌈n (H + ε) / log 2⌉` of bits used to index the typical set. -/
def typicalLength (p : α → ℝ) (n : ℕ) (ε : ℝ) : ℕ := ⌈n * (entropy p + ε) / log 2⌉₊

/-- The number `⌈n log |𝒳| / log 2⌉` of bits used to index all sequences of length `n`. -/
def rawLength (α : Type*) [Fintype α] (n : ℕ) : ℕ := ⌈n * log (Fintype.card α) / log 2⌉₊

open Classical in
/-- The code of Section 3.2: a typical sequence is sent to `0` followed by its index in the
typical set, any other sequence to `1` followed by its index in `𝒳ⁿ`. -/
def typicalSetCode (p : α → ℝ) (n : ℕ) (ε : ℝ) (x : Fin n → α) : List Bool :=
  if x ∈ typicalSet p n ε then false :: fixedLengthCode (typicalSet p n ε) (typicalLength p n ε) x
  else true :: fixedLengthCode univ (rawLength α n) x

lemma typicalSetCode_of_mem {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α}
    (hx : x ∈ typicalSet p n ε) :
    typicalSetCode p n ε x =
      false :: fixedLengthCode (typicalSet p n ε) (typicalLength p n ε) x := by
  simp [typicalSetCode, hx]

lemma typicalSetCode_of_notMem {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α}
    (hx : x ∉ typicalSet p n ε) :
    typicalSetCode p n ε x = true :: fixedLengthCode univ (rawLength α n) x := by
  simp [typicalSetCode, hx]

lemma card_typicalSet_le_two_pow {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (ε : ℝ) :
    (typicalSet p n ε).card ≤ 2 ^ typicalLength p n ε :=
  card_le_two_pow_ceil (card_typicalSet_le hp n ε)

lemma card_univ_le_two_pow {p : α → ℝ} (hp : IsPMF p) (n : ℕ) :
    (univ : Finset (Fin n → α)).card ≤ 2 ^ rawLength α n := by
  apply card_le_two_pow_ceil
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hp
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, exp_natCast_mul, exp_log hα]

/-- **The code is one-to-one** (and therefore invertible): the initial bit is a flag telling
whether the sequence is typical, and each part is indexed injectively. -/
theorem typicalSetCode_injective {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (ε : ℝ) :
    Function.Injective (typicalSetCode p n ε) := by
  intro x y h
  by_cases hx : x ∈ typicalSet p n ε <;> by_cases hy : y ∈ typicalSet p n ε
  · rw [typicalSetCode_of_mem hx, typicalSetCode_of_mem hy, List.cons.injEq] at h
    exact fixedLengthCode_injOn (card_typicalSet_le_two_pow hp n ε) hx hy h.2
  · rw [typicalSetCode_of_mem hx, typicalSetCode_of_notMem hy, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · rw [typicalSetCode_of_notMem hx, typicalSetCode_of_mem hy, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · rw [typicalSetCode_of_notMem hx, typicalSetCode_of_notMem hy, List.cons.injEq] at h
    exact fixedLengthCode_injOn (card_univ_le_two_pow hp n) (mem_univ x) (mem_univ y) h.2

/-- A typical sequence has a description of at most `n(H + ε) + 2` bits. -/
theorem length_typicalSetCode_of_mem {p : α → ℝ} (hp : IsPMF p) {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {x : Fin n → α} (hx : x ∈ typicalSet p n ε) :
    ((typicalSetCode p n ε x).length : ℝ) ≤ n * (entropy p + ε) / log 2 + 2 := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hnn : 0 ≤ n * (entropy p + ε) / log 2 :=
    div_nonneg (mul_nonneg n.cast_nonneg (add_nonneg (entropy_nonneg hp) hε)) h2.le
  rw [typicalSetCode_of_mem hx, List.length_cons, length_fixedLengthCode _ hx]
  have := Nat.ceil_lt_add_one hnn
  push_cast
  rw [typicalLength]
  linarith

/-- An atypical sequence has a description of at most `n log |𝒳| + 2` bits. -/
theorem length_typicalSetCode_of_notMem {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α}
    (hx : x ∉ typicalSet p n ε) :
    ((typicalSetCode p n ε x).length : ℝ) ≤ n * log (Fintype.card α) / log 2 + 2 := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hnn : 0 ≤ n * log (Fintype.card α) / log 2 :=
    div_nonneg (mul_nonneg n.cast_nonneg (log_natCast_nonneg _)) h2.le
  rw [typicalSetCode_of_notMem hx, List.length_cons, length_fixedLengthCode _ (mem_univ x)]
  have := Nat.ceil_lt_add_one hnn
  push_cast
  rw [rawLength]
  linarith

/-- **(3.17)–(3.21)** The expected length of the typical-set code is at most
`n(H + ε) + Pr{(A_ε^(n))ᶜ} n log |𝒳| + 2` bits. -/
theorem expect_length_typicalSetCode_le [DecidableEq α] {p : α → ℝ} (hp : IsPMF p) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    expect (iidPMF p n) (fun x => ((typicalSetCode p n ε x).length : ℝ)) ≤
      n * (entropy p + ε) / log 2 +
        prob (iidPMF p n) (typicalSet p n ε)ᶜ * (n * log (Fintype.card α) / log 2) + 2 := by
  have hq := iidPMF_isPMF hp n
  set A := typicalSet p n ε
  set a := n * (entropy p + ε) / log 2
  set b := n * log (Fintype.card α) / log 2
  have ha : 0 ≤ a := div_nonneg (mul_nonneg n.cast_nonneg
    (add_nonneg (entropy_nonneg hp) hε)) (log_pos one_lt_two).le
  -- Bound the length pointwise, by `a + 2` on `A` and `b + 2` off `A`.
  have hpt : ∀ x, ((typicalSetCode p n ε x).length : ℝ) ≤
      (b + 2) + (a - b) * (if x ∈ A then 1 else 0) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [hx, ite_true]
      linarith [length_typicalSetCode_of_mem hp hε hx]
    · simp only [hx, ite_false]
      linarith [length_typicalSetCode_of_notMem (p := p) hx]
  refine (expect_mono hq.nonneg hpt).trans ?_
  rw [expect_add, expect_const hq, expect_const_mul, ← prob_eq_expect, prob_compl hq]
  have h1 := prob_le_one hq A
  nlinarith [prob_nonneg hq.nonneg A]

/-- **Theorem 3.2.1.** Let `Xⁿ` be i.i.d. `∼ p(x)` and `ε > 0`. For `n` sufficiently large there
is a one-to-one code mapping sequences `xⁿ` of length `n` into binary strings with
`E[(1/n) l(Xⁿ)] ≤ H(X) + ε` (3.23), where `H(X) = entropy p / log 2` is the entropy in bits. -/
theorem exists_code_expect_length_le {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ c : (Fin n → α) → List Bool, Function.Injective c ∧
      expect (iidPMF p n) (fun x => ((c x).length : ℝ)) / n ≤ entropy p / log 2 + ε := by
  classical
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  set L := log (Fintype.card α)
  have hL : 0 ≤ L := log_natCast_nonneg _
  -- Choose `ε₁` with `ε₁ (1 + log |𝒳|) / log 2 = ε / 2`.
  set ε₁ := ε * log 2 / (2 * (1 + L))
  have hε₁ : 0 < ε₁ := div_pos (mul_pos hε h2) (by linarith)
  have hε₁' : ε₁ * (1 + L) / log 2 = ε / 2 := by
    simp only [ε₁]; field_simp
  filter_upwards [eventually_prob_typicalSet_gt hp hε₁, eventually_gt_atTop 0,
    eventually_ge_atTop ⌈4 / ε⌉₊] with n hA hn hn4
  refine ⟨typicalSetCode p n ε₁, typicalSetCode_injective hp n ε₁, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn4' : 4 / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn4)
  have h4 : 4 ≤ ε * n := by rw [div_le_iff₀ hε] at hn4'; linarith
  have hc : prob (iidPMF p n) (typicalSet p n ε₁)ᶜ ≤ ε₁ := by
    rw [prob_compl (iidPMF_isPMF hp n)]; linarith
  have hbnn : 0 ≤ n * L / log 2 := div_nonneg (mul_nonneg hn'.le hL) h2.le
  have hE := expect_length_typicalSetCode_le hp n hε₁.le
  rw [div_le_iff₀ hn']
  have key : n * (entropy p + ε₁) / log 2 + ε₁ * (n * L / log 2) + 2 =
      n * (entropy p / log 2) + n * (ε₁ * (1 + L) / log 2) + 2 := by
    field_simp; ring
  have hmul : prob (iidPMF p n) (typicalSet p n ε₁)ᶜ * (n * L / log 2) ≤ ε₁ * (n * L / log 2) :=
    mul_le_mul_of_nonneg_right hc hbnn
  rw [hε₁'] at key
  nlinarith

end InfoTheory
