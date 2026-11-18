/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic

/-!
# The Hamming code

The `(7, 4, 3)` Hamming code is the null space of the parity check matrix `H` whose columns are
the seven non-zero binary vectors of length `3`. It has `16` codewords of block length `7`, it is
linear, and its minimum distance is `3`, so it corrects any single error. The syndrome `Hr` of a
received word `r = c + eᵢ` is the `i`-th column of `H`, which locates the error.

Binary vectors are `Fin 7 → ZMod 2`, and the Hamming weight and distance are Mathlib's
`hammingNorm` and `hammingDist`.

## Main definitions

* `hammingH`: the parity check matrix `H`, (7.117).
* `hammingCode`: the set of codewords, the null space of `H`.
* `hammingDecode`: syndrome decoding.

## Main statements

* `card_hammingCode`, `hammingCode_eq`: the code has `16` codewords, those listed in Section 7.11.
* `add_mem_hammingCode`: the code is linear.
* `three_le_hammingNorm`, `three_le_hammingDist`, `exists_hammingNorm_eq_three`: the minimum
  weight and the minimum distance are `3`.
* `mulVec_add_single`, `hammingDecode_add_single`, `hammingDecode_of_mem`: (7.118), the syndrome
  of a single error is the corresponding column of `H`, so syndrome decoding corrects one error.
* `hammingCode_systematic`: the first `4` bits of the codewords run through all `2⁴` messages.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 7.11
-/

@[expose] public section

open Matrix Finset

namespace InfoTheory

/-- **(7.117)** The parity check matrix of the `(7, 4)` Hamming code: its columns are the binary
expansions of `1, …, 7`. -/
def hammingH : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![0, 0, 0, 1, 1, 1, 1; 0, 1, 1, 0, 0, 1, 1; 1, 0, 1, 0, 1, 0, 1]

/-- **Section 7.11.** The `(7, 4)` Hamming code: the binary vectors `c` with `Hc = 0`. -/
def hammingCode : Finset (Fin 7 → ZMod 2) := univ.filter fun c => hammingH *ᵥ c = 0

lemma mem_hammingCode {c : Fin 7 → ZMod 2} : c ∈ hammingCode ↔ hammingH *ᵥ c = 0 := by
  simp [hammingCode]

/-- **Section 7.11.** The Hamming code has `2⁴ = 16` codewords. -/
theorem card_hammingCode : hammingCode.card = 16 := by
  decide

/-- **Section 7.11.** The codewords of the `(7, 4)` Hamming code. -/
theorem hammingCode_eq : hammingCode =
    {![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 0, 1, 1, 0],
      ![0, 0, 1, 1, 0, 0, 1], ![0, 1, 0, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 1, 0],
      ![0, 1, 1, 0, 0, 1, 1], ![0, 1, 1, 1, 1, 0, 0], ![1, 0, 0, 0, 0, 1, 1],
      ![1, 0, 0, 1, 1, 0, 0], ![1, 0, 1, 0, 1, 0, 1], ![1, 0, 1, 1, 0, 1, 0],
      ![1, 1, 0, 0, 1, 1, 0], ![1, 1, 0, 1, 0, 0, 1], ![1, 1, 1, 0, 0, 0, 0],
      ![1, 1, 1, 1, 1, 1, 1]} := by
  decide +kernel

/-- **Section 7.11.** The Hamming code is linear: the sum of two codewords is a codeword. -/
theorem add_mem_hammingCode {c c' : Fin 7 → ZMod 2} (hc : c ∈ hammingCode)
    (hc' : c' ∈ hammingCode) : c + c' ∈ hammingCode := by
  rw [mem_hammingCode] at *
  rw [mulVec_add, hc, hc', add_zero]

/-- **Section 7.11.** The minimum weight of the Hamming code is at least `3`: every non-zero
codeword has at least three `1`s. -/
theorem three_le_hammingNorm {c : Fin 7 → ZMod 2} (hc : c ∈ hammingCode) (h0 : c ≠ 0) :
    3 ≤ hammingNorm c := by
  have key : ∀ c : Fin 7 → ZMod 2, hammingH *ᵥ c = 0 → c ≠ 0 → 3 ≤ hammingNorm c := by
    decide +kernel
  exact key c (mem_hammingCode.1 hc) h0

/-- **Section 7.11.** The minimum weight is exactly `3`. -/
theorem exists_hammingNorm_eq_three : ∃ c ∈ hammingCode, hammingNorm c = 3 :=
  ⟨![0, 0, 1, 0, 1, 1, 0], by decide, by decide⟩

/-- **Section 7.11.** The minimum distance of the Hamming code is `3`: two distinct codewords
differ in at least three places. -/
theorem three_le_hammingDist {c c' : Fin 7 → ZMod 2} (hc : c ∈ hammingCode)
    (hc' : c' ∈ hammingCode) (h : c ≠ c') : 3 ≤ hammingDist c c' := by
  have hpair : ∀ a b : ZMod 2, a - b = a + b ∧ -a + b = a + b ∧ (a + b = 0 → a = b) := by
    decide
  have hne : c + c' ≠ 0 := fun h0 =>
    h (funext fun i => (hpair (c i) (c' i)).2.2 (congrFun h0 i))
  have h3 := three_le_hammingNorm (add_mem_hammingCode hc hc') hne
  rw [hammingDist_eq_hammingNorm]
  convert h3 using 2
  funext i
  simp only [Pi.add_apply, Pi.neg_apply]
  exact (hpair (c i) (c' i)).2.1

/-- The columns of `H` are distinct and non-zero. -/
lemma hammingH_col_injective :
    Function.Injective fun j : Fin 7 => fun r : Fin 3 => hammingH r j := by
  decide

/-- **(7.118)** If the codeword `c` is corrupted in position `i`, the syndrome of the received
word `c + eᵢ` is the `i`-th column of `H`. -/
theorem mulVec_add_single {c : Fin 7 → ZMod 2} (hc : c ∈ hammingCode) (i : Fin 7) :
    hammingH *ᵥ (c + Pi.single i 1) = fun r => hammingH r i := by
  rw [mulVec_add, mem_hammingCode.1 hc, zero_add]
  funext r
  simp [mulVec, dotProduct, Pi.single_apply]

open Classical in
/-- **Section 7.11.** Syndrome decoding: if the syndrome `Hr` is the `i`-th column of `H`, flip the
`i`-th bit of `r`. -/
noncomputable def hammingDecode (r : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  if h : ∃ i : Fin 7, hammingH *ᵥ r = fun s => hammingH s i then r + Pi.single h.choose 1 else r

/-- **Section 7.11.** Syndrome decoding corrects any single error. -/
theorem hammingDecode_add_single {c : Fin 7 → ZMod 2} (hc : c ∈ hammingCode) (i : Fin 7) :
    hammingDecode (c + Pi.single i 1) = c := by
  have hs := mulVec_add_single hc i
  have h : ∃ j : Fin 7, hammingH *ᵥ (c + Pi.single i 1) = fun s => hammingH s j := ⟨i, hs⟩
  unfold hammingDecode
  split
  · next h' =>
    have hj : h'.choose = i := hammingH_col_injective (h'.choose_spec.symm.trans hs)
    rw [hj, add_assoc]
    have : (Pi.single i 1 : Fin 7 → ZMod 2) + Pi.single i 1 = 0 := by
      rw [← Pi.single_add]
      simp [show (1 : ZMod 2) + 1 = 0 from rfl]
    rw [this, add_zero]
  · next h' => exact absurd h h'

/-- **Section 7.11.** Syndrome decoding leaves codewords unchanged. -/
theorem hammingDecode_of_mem {c : Fin 7 → ZMod 2} (hc : c ∈ hammingCode) : hammingDecode c = c := by
  have h : ¬ ∃ i : Fin 7, hammingH *ᵥ c = fun s => hammingH s i := by
    rintro ⟨i, hi⟩
    rw [mem_hammingCode.1 hc] at hi
    have : ∀ i : Fin 7, (0 : Fin 3 → ZMod 2) ≠ fun s => hammingH s i := by decide
    exact this i hi
  unfold hammingDecode
  split
  · next h' => exact absurd h' h
  · rfl

/-- **Section 7.11.** The code is systematic: the first `4` bits of the codewords run through all
`2⁴` messages, and the last `3` bits are parity checks. -/
theorem hammingCode_systematic : ∀ m : Fin 4 → ZMod 2,
    (hammingCode.filter fun c => ∀ i : Fin 4, c (Fin.castLE (by norm_num) i) = m i).card = 1 := by
  decide +kernel

end InfoTheory
