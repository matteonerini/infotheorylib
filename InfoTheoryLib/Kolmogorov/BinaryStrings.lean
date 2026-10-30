/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Kolmogorov.Programs
public import InfoTheoryLib.SourceCoding.BinarySequences

/-!
# Kolmogorov complexity of binary strings with `k` ones

A binary string `x` of length `n` with `k` ones is printed by the program "generate, in
lexicographic order, all sequences with `k` ones; of these sequences, print the `i`-th", which
only needs `k` (`⌈log₂ (n + 1)⌉` bits, since `n` is known) and the index `i` (`⌈log₂ C(n, k)⌉`
bits). Hence `K(x | n) ≤ n H₀(k/n) + log₂ (n + 1) + c` (Example 14.2.8, Theorem 14.2.5).

## Main definitions

* `allStrings n`: the `2ⁿ` binary strings of length `n`.
* `ones x`: the number of ones of `x`.
* `typeList n k`: the strings of length `n` with `k` ones, in the order of `allStrings n`.
* `bitLen m`: the least `l` with `m ≤ 2ˡ`, the number of bits needed for the indices below `m`.
* `typeIndexComputer`: the computer reading `k` and the index of the string among the strings
  with `k` ones.

## Main statements

* `length_typeList`: there are `C(n, k)` strings of length `n` with `k` ones.
* `complexity_le_binEntropy`: **Theorem 14.2.5**, `K(x | n) ≤ n H₀(k/n) + log₂ (n + 1) + c`.
* `complexity_le_binEntropy_sub`: **(14.21)–(14.23)**, for `0 < k < n`,
  `K(x | n) ≤ n H₀(k/n) + ½ log₂ n - ½ log₂ (π (k/n) (1 - k/n)) + c`.

## Implementation notes

The book states (14.24) with `½ log n` for all strings, but its proof uses (14.14), which holds
only for `0 < k < n`, and the term `-½ log (π (k/n)(1 - k/n))` it drops is itself of order
`½ log n` when `k` or `n - k` is bounded (for `k = 1`, `K(x | n) ≈ 2 log n` while
`n H₀(1/n) ≈ log n`). We prove the bound with `log₂ (n + 1)` for all strings, which is what the
later theorems use, and the refined bound for `0 < k < n` with the extra term. Entropies are
in bits here: `H₀ = binEntropy / log 2`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Example 14.2.8,
  Theorem 14.2.5
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### All strings of a given length -/

/-- The `2ⁿ` binary strings of length `n`. -/
def allStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allStrings n).flatMap fun w => [false :: w, true :: w]

lemma mem_allStrings {n : ℕ} {w : List Bool} : w ∈ allStrings n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [allStrings]
  | succ n ih =>
    simp only [allStrings, List.mem_flatMap, ih, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨v, hv, rfl | rfl⟩ <;> simp [hv]
    · intro hw
      cases w with
      | nil => simp at hw
      | cons b v =>
        refine ⟨v, by simpa using hw, ?_⟩
        cases b <;> simp

lemma nodup_allStrings (n : ℕ) : (allStrings n).Nodup := by
  induction n with
  | zero => simp [allStrings]
  | succ n ih =>
    rw [allStrings, List.nodup_flatMap]
    refine ⟨fun w _ => by simp, ?_⟩
    refine ih.pairwise_of_forall_ne fun v _ w _ hvw => ?_
    intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;> simp_all

lemma primrec_allStrings : Primrec allStrings := by
  have h := Primrec.nat_rec (f := fun _ : ℕ => [[]]) (g := fun _ (p : ℕ × List (List Bool)) =>
      p.2.flatMap fun w => [false :: w, true :: w]) (Primrec.const [[]])
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
        (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
          (Primrec.const []))).to₂).to₂
  refine (h.comp Primrec.id Primrec.id).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allStrings, ← ih]
    rfl

/-! ### Strings with `k` ones -/

/-- The number of ones of a binary string. -/
def ones (w : List Bool) : ℕ := (w.filter fun b => decide (b = true)).length

lemma primrec_ones : Primrec ones :=
  Primrec.list_length.comp (Primrec.listFilter (p := fun b : Bool => b = true)
    ((Primrec.eq (α := Bool)).comp Primrec.id (Primrec.const true)))

@[simp] lemma ones_cons (b : Bool) (w : List Bool) :
    ones (b :: w) = ones w + if b then 1 else 0 := by
  cases b <;> simp [ones]

lemma ones_le_length (w : List Bool) : ones w ≤ w.length := List.length_filter_le _ _

/-- The strings of length `n` with `k` ones, in the order of `allStrings n`. -/
def typeList (n k : ℕ) : List (List Bool) := (allStrings n).filter fun w => decide (ones w = k)

lemma mem_typeList {n k : ℕ} {w : List Bool} : w ∈ typeList n k ↔ w.length = n ∧ ones w = k := by
  simp [typeList, mem_allStrings]

lemma primrec_typeList : Primrec₂ typeList :=
  (PrimrecRel.listFilter (R := fun w k => ones w = k)
    ((Primrec.eq (α := ℕ)).comp (primrec_ones.comp Primrec.fst) Primrec.snd)).comp
      (primrec_allStrings.comp Primrec.fst) Primrec.snd

lemma length_filter_flatMap (L : List (List Bool)) (P : List Bool → Bool) :
    ((L.flatMap fun w => [false :: w, true :: w]).filter P).length =
      (L.filter fun w => P (false :: w)).length + (L.filter fun w => P (true :: w)).length := by
  induction L with
  | nil => simp
  | cons v L ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append, ih, List.filter_cons,
      List.filter_nil]
    split_ifs <;> simp <;> omega

/-- There are `C(n, k)` strings of length `n` with `k` ones. -/
theorem length_typeList (n k : ℕ) : (typeList n k).length = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp [typeList, allStrings, ones]
  | succ n ih =>
    rw [typeList, allStrings, length_filter_flatMap]
    simp only [ones_cons, Bool.false_eq_true, ite_false, add_zero, ite_true]
    rcases k with _ | k
    · have : ((allStrings n).filter fun w => decide (ones w + 1 = 0)).length = 0 := by simp
      rw [this, add_zero]
      simpa [typeList] using ih 0
    · have e : ∀ w : List Bool, decide (ones w + 1 = k + 1) = decide (ones w = k) := by simp
      simp only [e]
      rw [Nat.choose_succ_succ', ← ih k, ← ih (k + 1)]
      simp only [typeList]
      ring

/-! ### Fixed-length binary encodings -/

/-- `2ˡ`, computed by iteration. -/
def pow2 (l : ℕ) : ℕ := (fun x => 2 * x)^[l] 1

lemma pow2_eq (l : ℕ) : pow2 l = 2 ^ l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [pow2, Function.iterate_succ_apply', ← pow2, ih, pow_succ]; ring

lemma primrec_pow2 : Primrec pow2 :=
  Primrec.nat_iterate Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂

/-- The least `l` with `m ≤ 2ˡ`: `l` bits suffice to write the indices `0, …, m - 1`. -/
def bitLen (m : ℕ) : ℕ := (List.range (m + 1)).findIdx fun l => decide (m ≤ pow2 l)

lemma primrec_bitLen : Primrec bitLen :=
  Primrec.list_findIdx (Primrec.list_range.comp Primrec.succ)
    (Primrec.nat_le.decide.comp Primrec.fst (primrec_pow2.comp Primrec.snd)).to₂

lemma lt_two_pow_self' (m : ℕ) : m < 2 ^ m := Nat.lt_two_pow_self

lemma bitLen_lt (m : ℕ) : bitLen m < m + 1 := by
  have h : ∃ l ∈ List.range (m + 1), decide (m ≤ pow2 l) = true :=
    ⟨m, List.mem_range.2 (by omega), by simpa [pow2_eq] using (lt_two_pow_self' m).le⟩
  have := List.findIdx_lt_length_of_exists h
  rw [List.length_range] at this
  exact this

lemma le_two_pow_bitLen (m : ℕ) : m ≤ 2 ^ bitLen m := by
  have h := List.findIdx_getElem (w := by rw [List.length_range]; exact bitLen_lt m)
    (p := fun l => decide (m ≤ pow2 l)) (xs := List.range (m + 1))
  simpa [bitLen, pow2_eq] using h

lemma two_pow_lt_of_lt_bitLen {m l : ℕ} (hl : l < bitLen m) : 2 ^ l < m := by
  have h := List.not_of_lt_findIdx (p := fun l => decide (m ≤ pow2 l)) (xs := List.range (m + 1))
    (i := l) (by simpa [bitLen] using hl)
  simpa [pow2_eq] using h

/-- `bitLen m ≤ log₂ m + 1` for `m ≥ 1`. -/
lemma bitLen_le_logb {m : ℕ} (hm : 1 ≤ m) : (bitLen m : ℝ) ≤ logb 2 m + 1 := by
  rcases Nat.eq_zero_or_pos (bitLen m) with h | h
  · rw [h, Nat.cast_zero]
    have : 0 ≤ logb 2 (m : ℝ) := logb_nonneg (by norm_num) (by exact_mod_cast hm)
    linarith
  · have h2 := two_pow_lt_of_lt_bitLen (show bitLen m - 1 < bitLen m by omega)
    have h3 : ((2 : ℝ) ^ (bitLen m - 1 : ℕ)) < m := by exact_mod_cast h2
    have h4 : ((bitLen m - 1 : ℕ) : ℝ) < logb 2 m := by
      rw [lt_logb_iff_rpow_lt (by norm_num) (by positivity), rpow_natCast]
      exact h3
    have : ((bitLen m - 1 : ℕ) : ℝ) = bitLen m - 1 := by rw [Nat.cast_sub h]; simp
    linarith

/-- The `l` low binary digits of `i`, least significant first. -/
def toBitsFixed (l i : ℕ) : List Bool := (List.range l).map fun j => decide (i / pow2 j % 2 = 1)

@[simp] lemma length_toBitsFixed (l i : ℕ) : (toBitsFixed l i).length = l := by
  simp [toBitsFixed]

lemma primrec_toBitsFixed : Primrec₂ toBitsFixed :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    ((Primrec.eq (α := ℕ)).decide.comp (Primrec.nat_mod.comp (Primrec.nat_div.comp
      (Primrec.snd.comp Primrec.fst) (primrec_pow2.comp Primrec.snd)) (Primrec.const 2))
      (Primrec.const 1)).to₂

lemma fromBits_toBitsFixed {l i : ℕ} (hi : i < 2 ^ l) : fromBits (toBitsFixed l i) = i := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_fromBits]
  rcases lt_or_ge j l with h | h
  · simp only [toBitsFixed, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h,
      Option.map_some, Option.getD_some, pow2_eq]
    rw [Nat.testBit_eq_decide_div_mod_eq]
  · rw [List.getD_eq_default _ _ (by simpa using h), Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) h))]

/-! ### The two-part program -/

/-- The decoder of the two-part description: `k` in `bitLen (n + 1)` bits, then the index of the
string among `typeList n k` in `bitLen |typeList n k|` bits. -/
def typeIndexDecode (q : List Bool) (n : ℕ) : Option (List Bool) :=
  let l₁ := bitLen (n + 1)
  let S := typeList n (fromBits (q.take l₁))
  bif decide (q.length = l₁ + bitLen S.length) then S[fromBits (q.drop l₁)]? else none

lemma computable_typeIndexDecode : Computable₂ typeIndexDecode := by
  have hl₁ : Primrec fun a : List Bool × ℕ => bitLen (a.2 + 1) :=
    primrec_bitLen.comp (Primrec.succ.comp Primrec.snd)
  have hS : Primrec fun a : List Bool × ℕ =>
      typeList a.2 (fromBits (a.1.take (bitLen (a.2 + 1)))) :=
    primrec_typeList.comp Primrec.snd (primrec_fromBits.comp
      (Primrec.list_take.comp hl₁ Primrec.fst))
  exact (Primrec.cond ((Primrec.eq (α := ℕ)).decide.comp (Primrec.list_length.comp Primrec.fst)
    (Primrec.nat_add.comp hl₁ (primrec_bitLen.comp (Primrec.list_length.comp hS))))
    (Primrec.list_getElem?.comp hS (primrec_fromBits.comp (Primrec.list_drop.comp hl₁
      Primrec.fst))) (Primrec.const none)).to_comp

/-- **Example 14.2.8** The computer that prints the string of a given index among the strings of
length `n` (the side information) with a given number of ones. -/
def typeIndexComputer : Computer :=
  Computer.ofOption typeIndexDecode computable_typeIndexDecode fun n q hq q' hq' hqq' => by
    simp only [Set.mem_ofPred_eq, typeIndexDecode] at hq hq'
    have hlen : ∀ {r : List Bool}, (typeIndexDecode r n).isSome →
        r.length = bitLen (n + 1) + bitLen (typeList n (fromBits (r.take (bitLen (n + 1))))).length
        := fun {r} h => by
      by_contra hc
      simp [typeIndexDecode, hc] at h
    have h1 := hlen hq
    have h2 := hlen hq'
    have htake : q.take (bitLen (n + 1)) = q'.take (bitLen (n + 1)) := by
      obtain ⟨t, rfl⟩ := hqq'
      rw [List.take_append_of_le_length (by omega)]
    rw [htake] at h1
    exact hqq'.eq_of_length (h1.trans h2.symm)

/-- The two-part program for `x`: the number of ones, then the index of `x`. -/
def typeIndexProgram (x : List Bool) : List Bool :=
  toBitsFixed (bitLen (x.length + 1)) (ones x) ++
    toBitsFixed (bitLen (typeList x.length (ones x)).length)
      ((typeList x.length (ones x)).idxOf x)

lemma mem_typeIndexComputer (x : List Bool) :
    x ∈ typeIndexComputer.run (typeIndexProgram x) x.length := by
  refine Computer.mem_ofOption_run ?_
  set n := x.length
  set k := ones x
  set S := typeList n k
  have hk : k < 2 ^ bitLen (n + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_of_le (ones_le_length x)) (le_two_pow_bitLen _)
  have hxS : x ∈ S := mem_typeList.2 ⟨rfl, rfl⟩
  have hi : S.idxOf x < 2 ^ bitLen S.length :=
    lt_of_lt_of_le (List.idxOf_lt_length_of_mem hxS) (le_two_pow_bitLen _)
  have h1 : (typeIndexProgram x).take (bitLen (n + 1)) = toBitsFixed (bitLen (n + 1)) k := by
    simp [typeIndexProgram, n, k]
  have h2 : (typeIndexProgram x).drop (bitLen (n + 1)) =
      toBitsFixed (bitLen S.length) (S.idxOf x) := by
    simp [typeIndexProgram, n, k, S]
  simp only [typeIndexDecode, h1, h2, fromBits_toBitsFixed hk, fromBits_toBitsFixed hi]
  simp [typeIndexProgram, S, n, k, List.getElem?_idxOf hxS]

lemma length_typeIndexProgram (x : List Bool) :
    (typeIndexProgram x).length =
      bitLen (x.length + 1) + bitLen (x.length.choose (ones x)) := by
  simp [typeIndexProgram, length_typeList]

/-- `K(x | n) ≤ log₂ (n + 1) + log₂ C(n, k) + c`, (14.21). -/
theorem complexity_le_log_choose {U : Computer} (hU : U.IsUniversal) :
    ∃ c : ℝ, ∀ x : List Bool, (U.complexity x x.length : ℝ) ≤
      logb 2 (x.length + 1) + logb 2 (x.length.choose (ones x)) + c := by
  obtain ⟨s, hs⟩ := hU.mem_run typeIndexComputer
  refine ⟨s.length + 2, fun x => ?_⟩
  have h := Computer.complexity_le (hs (mem_typeIndexComputer x))
  rw [List.length_append, length_typeIndexProgram] at h
  have h1 := bitLen_le_logb (m := x.length + 1) (by omega)
  have hC : 1 ≤ x.length.choose (ones x) := Nat.choose_pos (ones_le_length x)
  have h2 := bitLen_le_logb hC
  push_cast at h1
  have : (U.complexity x x.length : ℝ) ≤ s.length + (bitLen (x.length + 1) +
      bitLen (x.length.choose (ones x))) := by exact_mod_cast h
  linarith

/-- **Theorem 14.2.5, (14.24).** `K(x₁ ⋯ xₙ | n) ≤ n H₀(k/n) + log₂ (n + 1) + c` for every
binary string with `k` ones, `H₀` the binary entropy in bits. -/
theorem complexity_le_binEntropy {U : Computer} (hU : U.IsUniversal) :
    ∃ c : ℝ, ∀ x : List Bool, (U.complexity x x.length : ℝ) ≤
      x.length * (binEntropy (ones x / x.length) / log 2) + logb 2 (x.length + 1) + c := by
  obtain ⟨c, hc⟩ := complexity_le_log_choose hU
  refine ⟨c, fun x => ?_⟩
  have h := hc x
  have hC : (0 : ℝ) < x.length.choose (ones x) := by
    exact_mod_cast Nat.choose_pos (ones_le_length x)
  have hb := choose_le_exp_binEntropy (ones_le_length x)
  have : logb 2 (x.length.choose (ones x) : ℝ) ≤
      x.length * (binEntropy (ones x / x.length) / log 2) := by
    rw [logb, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (log_pos (by norm_num)).le
    have := log_le_log hC hb
    rwa [log_exp] at this
  linarith

/-- **(14.21)–(14.23)** For `0 < k < n`,
`K(x | n) ≤ n H₀(k/n) + ½ log₂ n - ½ log₂ (π (k/n) (1 - k/n)) + c`. -/
theorem complexity_le_binEntropy_sub {U : Computer} (hU : U.IsUniversal) :
    ∃ c : ℝ, ∀ x : List Bool, 0 < ones x → ones x < x.length →
      (U.complexity x x.length : ℝ) ≤ x.length * (binEntropy (ones x / x.length) / log 2) +
        1 / 2 * logb 2 x.length -
          1 / 2 * logb 2 (π * (ones x / x.length) * ((x.length - ones x) / x.length)) + c := by
  obtain ⟨c, hc⟩ := complexity_le_log_choose hU
  refine ⟨c + 1, fun x hk hkn => ?_⟩
  set n := x.length
  set k := ones x
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hl : 0 < log 2 := log_pos (by norm_num)
  have h := hc x
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (ones_le_length x)
  -- `log₂ (n + 1) ≤ log₂ n + 1`.
  have hn1 : logb 2 ((n : ℝ) + 1) ≤ logb 2 n + 1 := by
    have : (n : ℝ) + 1 ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hk.trans hkn
      linarith
    calc logb 2 ((n : ℝ) + 1) ≤ logb 2 (2 * n) :=
          logb_le_logb_of_le (by norm_num) (by positivity) this
      _ = logb 2 n + 1 := by
          rw [logb_mul (by norm_num) hn.ne', logb_self_eq_one (by norm_num)]; ring
  -- `(13.31)`, in bits.
  have hb := choose_le_sqrt_mul_exp_binEntropy hk hkn
  have hlogC : logb 2 (n.choose k : ℝ) ≤ n * (binEntropy (k / n) / log 2) - 1 / 2 * logb 2 n -
      1 / 2 * logb 2 (π * (k / n) * ((n - k) / n)) := by
    have hm : (0 : ℝ) < n - k := by
      have : (k : ℝ) < n := by exact_mod_cast hkn
      linarith
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have := log_le_log hC hb
    rw [log_mul (by positivity) (exp_pos _).ne', log_exp, Real.log_sqrt (by positivity)] at this
    have e : (n : ℝ) / (π * k * (n - k)) = (n * (π * (k / n) * ((n - k) / n)))⁻¹ := by
      field_simp
    rw [e, log_inv, log_mul hn.ne' (by positivity)] at this
    simp only [logb]
    rw [div_le_iff₀ hl] at *
    have e2 : (n * (binEntropy (k / n) / log 2) - 1 / 2 * (log n / log 2) -
        1 / 2 * (log (π * (k / n) * ((n - k) / n)) / log 2)) * log 2 =
        n * binEntropy (k / n) - 1 / 2 * log n - 1 / 2 * log (π * (k / n) * ((n - k) / n)) := by
      field_simp
    rw [e2]
    linarith
  linarith

end InfoTheory
