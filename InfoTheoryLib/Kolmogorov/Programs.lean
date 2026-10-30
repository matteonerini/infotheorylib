/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Nat.Bits
public import InfoTheoryLib.Kolmogorov.Computer
public import InfoTheoryLib.SourceCoding.IntegerCode

/-!
# Simple programs and upper bounds on Kolmogorov complexity

An upper bound on `K(x)` is a program that prints `x`. We build a few computers, prove that they
are partial recursive with prefix-free programs, and let a universal computer simulate them:

* "print the following `l`-bit sequence", when `l` is known: `K(x | l(x)) ≤ l(x) + c`
  (Theorem 14.2.2);
* the same, preceded by a self-delimiting description of `l(x)` in `2 log l(x) + O(1)` bits:
  `K(x) ≤ K(x | l(x)) + 2 log l(x) + c` (Theorem 14.2.3); in particular every string has a
  program on a universal computer;
* "print `n` zeros" and "print `n` alternating bits": `K(0ⁿ | n) ≤ c` (Examples 14.2.1 and
  14.2.4).

## Main definitions

* `fromBits l`: the number with binary digits `l`, least significant first.
* `sdParse q`: the decoder of the self-delimiting code `eliasGamma` of a positive integer,
  returning the rest of the input and the integer minus one.
* `Computer.ofOption f`, `lengthComputer`, `Computer.withLength B`, `zerosComputer`,
  `alternatingComputer`.

## Main statements

* `sdParse_eliasGamma_append`, `eq_of_sdParse_eq_some`: the decoder inverts the code.
* `complexity_length_le`: **Theorem 14.2.2**, `K(x | l(x)) ≤ l(x) + c`.
* `complexity_le_complexity_length_add`: **Theorem 14.2.3**,
  `K(x | y) ≤ K(x | l(x)) + 2 log₂ (l(x) + 1) + c`.
* `Computer.IsUniversal.hasProgram_all`: a universal computer prints every string.
* `complexity_le_length_add`: `K(x | y) ≤ l(x) + 2 log₂ (l(x) + 1) + c`.
* `complexity_zeros_le`, `complexity_alternating_le`: **Examples 14.2.1 and 14.2.4**.

## Implementation notes

The book describes `l(x) = n` by doubling the bits of `n` and ending with `01`. We use instead
the Elias gamma code of `n + 1` (Lemma 13.5.1), of length `2 ⌊log₂ (n + 1)⌋ + 1`, whose decoder
is primitive recursive: count the leading zeros, then read as many bits after the following one.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 14.2
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Binary digits -/

/-- The number with binary digits `l`, least significant first. -/
def fromBits (l : List Bool) : ℕ := l.foldr (fun b s => bif b then 2 * s + 1 else 2 * s) 0

@[simp] lemma fromBits_nil : fromBits [] = 0 := rfl

lemma fromBits_cons (b : Bool) (l : List Bool) : fromBits (b :: l) = Nat.bit b (fromBits l) := rfl

lemma testBit_fromBits (l : List Bool) (i : ℕ) : (fromBits l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [fromBits_cons]
    cases i with
    | zero => simp
    | succ i => rw [Nat.testBit_bit_succ, ih]; simp

lemma fromBits_lowBits {k : ℕ} (hk : k ≠ 0) : fromBits (lowBits k ++ [true]) = k := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_fromBits]
  rcases lt_trichotomy i (Nat.log2 k) with h | h | h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [lowBits, List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp [h])]
    simp [h, Nat.testBit_log2 hk]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by norm_num) h))).symm

/-! ### The self-delimiting code of an integer -/

/-- The number of leading zeros of `q`. -/
def sdLead (q : List Bool) : ℕ := (q.takeWhile fun b => !b).length

/-- Whether `q` begins with a codeword `0ᶻ 1 b₁ ⋯ b_z` of the Elias gamma code. -/
def sdValid (q : List Bool) : Bool :=
  decide ((q.drop (sdLead q)).head? = some true) && decide (2 * sdLead q + 1 ≤ q.length)

/-- The integer coded by the Elias gamma codeword at the start of `q`. -/
def sdValue (q : List Bool) : ℕ := fromBits (((q.drop (sdLead q + 1)).take (sdLead q)) ++ [true])

/-- The rest of `q` after the codeword. -/
def sdRest (q : List Bool) : List Bool := q.drop (2 * sdLead q + 1)

/-- The decoder of the self-delimiting code `n ↦ eliasGamma (n + 1)`: the rest of the input and
`n`, if the input starts with a codeword. -/
def sdParse (q : List Bool) : Option (List Bool × ℕ) :=
  bif sdValid q then some (sdRest q, sdValue q - 1) else none

lemma takeWhile_replicate_append (z : ℕ) (r : List Bool) :
    (List.replicate z false ++ true :: r).takeWhile (fun b => !b) = List.replicate z false := by
  induction z with
  | zero => simp
  | succ z ih => simp [List.replicate_succ, ih]

lemma sdLead_eliasGamma_append {k : ℕ} (p : List Bool) :
    sdLead (eliasGamma k ++ p) = Nat.log2 k := by
  simp [sdLead, eliasGamma, List.append_assoc]

/-- **The decoder inverts the code**: `sdParse (eliasGamma (n + 1) ++ p) = (p, n)`. -/
theorem sdParse_eliasGamma_append (n : ℕ) (p : List Bool) :
    sdParse (eliasGamma (n + 1) ++ p) = some (p, n) := by
  have hz := sdLead_eliasGamma_append (k := n + 1) p
  have hlen : (lowBits (n + 1)).length = Nat.log2 (n + 1) := length_lowBits _
  simp only [sdParse, sdValid, sdValue, sdRest, hz]
  have h1 : (eliasGamma (n + 1) ++ p).drop (Nat.log2 (n + 1)) = true :: (lowBits (n + 1) ++ p) := by
    simp [eliasGamma]
  have h2 : (eliasGamma (n + 1) ++ p).drop (Nat.log2 (n + 1) + 1) = lowBits (n + 1) ++ p := by
    rw [← List.drop_drop, h1]
    simp
  have h3 : (eliasGamma (n + 1) ++ p).drop (2 * Nat.log2 (n + 1) + 1) = p := by
    rw [show 2 * Nat.log2 (n + 1) + 1 = Nat.log2 (n + 1) + 1 + Nat.log2 (n + 1) by ring,
      ← List.drop_drop, h2, List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le
      (by omega), List.nil_append]
  have hl : 2 * Nat.log2 (n + 1) + 1 ≤ (eliasGamma (n + 1) ++ p).length := by
    rw [List.length_append, length_eliasGamma]
    omega
  rw [h1, h2, h3, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    fromBits_lowBits (by omega)]
  have hl' : 2 * (n + 1).log2 < (eliasGamma (n + 1)).length + p.length := by
    rw [length_eliasGamma]
    omega
  simp [hl']

/-- **The code can be read back**: an input accepted by the decoder starts with the codeword of
the decoded integer. -/
theorem eq_of_sdParse_eq_some {q p : List Bool} {n : ℕ} (h : sdParse q = some (p, n)) :
    q = eliasGamma (n + 1) ++ p := by
  simp only [sdParse] at h
  cases hv : sdValid q
  · simp [hv] at h
  simp only [hv, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hp, hn⟩ := h
  simp only [sdValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hhead, hle⟩ := hv
  set z := sdLead q
  -- `q = 0ᶻ 1 bits rest`.
  have hq1 : q = List.replicate z false ++ q.drop z := by
    have htw : q.takeWhile (fun b => !b) = List.replicate z false := by
      refine List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩
      have := List.mem_takeWhile_imp hb
      simpa using this
    have htake : q.take z = q.takeWhile (fun b => !b) :=
      (List.prefix_iff_eq_take.1 (List.takeWhile_prefix _)).symm
    rw [← htw, ← htake, List.take_append_drop]
  obtain ⟨t, ht⟩ : ∃ t, q.drop z = true :: t := by
    rcases hd : q.drop z with _ | ⟨b, t⟩
    · simp [hd] at hhead
    · rw [hd] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      exact ⟨t, by rw [hhead]⟩
  have htlen : z ≤ t.length := by
    have := congrArg List.length ht
    simp at this
    omega
  set bits := t.take z
  have hbits : bits.length = z := by simp [bits, htlen]
  have hrest : p = t.drop z := by
    rw [← hp, sdRest, show 2 * z + 1 = z + 1 + z by ring, ← List.drop_drop, ← List.drop_drop, ht]
    simp
  have hval : n + 1 = fromBits (bits ++ [true]) := by
    have hpos : 1 ≤ fromBits (bits ++ [true]) := by
      have : (fromBits (bits ++ [true])).testBit z = true := by
        rw [testBit_fromBits, List.getD_append_right _ _ _ _ (by omega)]
        simp [hbits]
      have := Nat.ge_two_pow_of_testBit this
      have : 1 ≤ 2 ^ z := Nat.one_le_two_pow
      omega
    rw [← hn, sdValue]
    have : (q.drop (z + 1)).take z = bits := by
      rw [← List.drop_drop, ht]
      simp [bits]
    rw [this]
    omega
  set m := fromBits (bits ++ [true])
  have hm0 : m ≠ 0 := by omega
  have hbit : ∀ i, m.testBit i = (bits ++ [true]).getD i false := testBit_fromBits _
  have hlog : Nat.log2 m = z := by
    rw [Nat.log2_eq_iff hm0]
    constructor
    · have htop : m.testBit z = true := by
        rw [hbit, List.getD_append_right _ _ _ _ (by omega)]
        simp [hbits]
      exact Nat.ge_two_pow_of_testBit htop
    · refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
      rw [hbit, List.getD_eq_default _ _ (by simp [hbits]; omega)]
  have hlow : lowBits m = bits := by
    refine List.ext_getElem (by simp [hlog, hbits]) fun i h1 h2 => ?_
    simp only [lowBits, List.getElem_ofFn]
    rw [hbit, List.getD_append _ _ _ _ h2, List.getD_eq_getElem _ _ h2]
  rw [hval, eliasGamma, hlog, hlow, hrest, hq1, ht]
  simp only [List.append_assoc, List.cons_append]
  congr 2
  exact (List.take_append_drop z t).symm

/-! ### Computability of the decoder -/

lemma primrec_fromBits : Primrec fromBits := by
  have h := Primrec.list_foldr (f := fun l : List Bool => l) (g := fun _ => 0)
    (h := fun _ (bs : Bool × ℕ) => bif bs.1 then 2 * bs.2 + 1 else 2 * bs.2)
    Primrec.id (Primrec.const 0)
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂
  exact h

lemma primrec_sdLead : Primrec sdLead :=
  Primrec.list_length.comp (Primrec.list_takeWhile (p := fun b : Bool => !b) Primrec.not)

lemma primrec_sdValid : Primrec sdValid := by
  unfold sdValid
  refine Primrec.and.comp ?_ ?_
  · exact Primrec.eq.decide.comp (Primrec.list_head?.comp (Primrec.list_drop.comp primrec_sdLead
      Primrec.id)) (Primrec.const (some true))
  · exact Primrec.nat_le.decide.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      primrec_sdLead)) Primrec.list_length

lemma primrec_sdParse : Primrec sdParse := by
  unfold sdParse sdRest sdValue
  refine Primrec.cond primrec_sdValid (Primrec.option_some.comp (Primrec.pair ?_ ?_))
    (Primrec.const none)
  · exact Primrec.list_drop.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      primrec_sdLead)) Primrec.id
  · exact Primrec.nat_sub.comp (primrec_fromBits.comp (Primrec.list_append.comp
      (Primrec.list_take.comp primrec_sdLead (Primrec.list_drop.comp
        (Primrec.succ.comp primrec_sdLead) Primrec.id)) (Primrec.const [true])))
      (Primrec.const 1)

/-! ### Computers from computable functions -/

namespace Computer

/-- A computer defined by a computable function returning `none` on the programs that do not
halt. -/
def ofOption (f : List Bool → ℕ → Option (List Bool)) (hf : Computable₂ f)
    (hpf : ∀ y, InformationTheory.IsPrefixFree {p | (f p y).isSome}) : Computer where
  run p y := (f p y : Part (List Bool))
  partrec := (Computable.ofOption hf).to₂
  prefixFree y := by
    simpa only [Part.ofOption_dom] using hpf y

@[simp] lemma ofOption_run {f : List Bool → ℕ → Option (List Bool)} {hf : Computable₂ f}
    {hpf : ∀ y, InformationTheory.IsPrefixFree {p | (f p y).isSome}} {p : List Bool} {y : ℕ} :
    (ofOption f hf hpf).run p y = (f p y : Part (List Bool)) := rfl

lemma mem_ofOption_run {f : List Bool → ℕ → Option (List Bool)} {hf : Computable₂ f}
    {hpf : ∀ y, InformationTheory.IsPrefixFree {p | (f p y).isSome}} {x p : List Bool} {y : ℕ}
    (h : f p y = some x) : x ∈ (ofOption f hf hpf).run p y := by
  simp [h]

end Computer

/-! ### Theorem 14.2.2: printing a string of known length -/

/-- "Print the following `l`-bit sequence", the length `l` being the side information. -/
def printLength (p : List Bool) (n : ℕ) : Option (List Bool) :=
  bif decide (p.length = n) then some p else none

lemma computable_printLength : Computable₂ printLength :=
  (Primrec.cond ((Primrec.eq (α := ℕ)).decide.comp (Primrec.list_length.comp Primrec.fst)
    Primrec.snd)
    (Primrec.option_some.comp Primrec.fst) (Primrec.const none)).to_comp

/-- The computer that prints its program, whose length is the side information. -/
def lengthComputer : Computer :=
  Computer.ofOption printLength computable_printLength fun n p hp q hq hpq => by
    simp only [Set.mem_ofPred_eq, printLength] at hp hq
    have h1 : p.length = n := by by_contra h; simp [h] at hp
    have h2 : q.length = n := by by_contra h; simp [h] at hq
    exact hpq.eq_of_length (h1.trans h2.symm)

lemma mem_lengthComputer (x : List Bool) : x ∈ lengthComputer.run x x.length :=
  Computer.mem_ofOption_run (by simp [printLength])

/-- **Theorem 14.2.2 (Conditional complexity is less than the length of the sequence), (14.7).**
`K(x | l(x)) ≤ l(x) + c`: the program "print the following `l(x)` bits" needs no description of
`l(x)`, which is given. -/
theorem complexity_length_le {U : Computer} (hU : U.IsUniversal) :
    ∃ c, ∀ x : List Bool, U.complexity x x.length ≤ x.length + c := by
  obtain ⟨s, hs⟩ := hU.mem_run lengthComputer
  exact ⟨s.length, fun x => (Computer.complexity_le (hs (mem_lengthComputer x))).trans
    (by rw [List.length_append, add_comm])⟩

/-! ### Theorem 14.2.3: a self-delimiting description of the length -/

namespace Computer

/-- The computer that reads a self-delimiting description of a number `n` and then runs `B` with
side information `n`, ignoring its own side information. -/
def withLength (B : Computer) : Computer where
  run q _ := (sdParse q : Part (List Bool × ℕ)).bind fun r => B.run r.1 r.2
  partrec := by
    refine Partrec.to₂ (f := fun a : List Bool × ℕ =>
      (sdParse a.1 : Part (List Bool × ℕ)).bind fun r => B.run r.1 r.2) ?_
    exact (Computable.ofOption (primrec_sdParse.to_comp.comp Computable.fst)).bind
      (B.partrec.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).to₂
  prefixFree _ := by
    intro q hq q' hq' hqq'
    simp only [Set.mem_ofPred_eq, Part.bind_dom] at hq hq'
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨h1', h2'⟩ := hq'
    -- Both inputs parse: `q = γ(n + 1) p`, `q' = γ(n' + 1) p'`.
    obtain ⟨⟨p, n⟩, hpn⟩ := Option.isSome_iff_exists.1 (by simpa [Part.ofOption_dom] using h1)
    obtain ⟨⟨p', n'⟩, hpn'⟩ := Option.isSome_iff_exists.1 (by simpa [Part.ofOption_dom] using h1')
    have e := eq_of_sdParse_eq_some hpn
    have e' := eq_of_sdParse_eq_some hpn'
    have hB : (B.run p n).Dom := by
      rw [Part.get_eq_of_mem (Part.mem_coe.2 hpn) h1] at h2
      exact h2
    have hB' : (B.run p' n').Dom := by
      rw [Part.get_eq_of_mem (Part.mem_coe.2 hpn') h1'] at h2'
      exact h2'
    -- The codewords are comparable, hence equal.
    have hc : eliasGamma (n + 1) <+: q' := (List.prefix_append _ _).trans (e ▸ hqq')
    have hc' : eliasGamma (n' + 1) <+: q' := e' ▸ List.prefix_append _ _
    have hn : n = n' := by
      rcases List.prefix_or_prefix_of_prefix hc hc' with h | h
      · exact Nat.succ_injective (eq_of_eliasGamma_prefix (by omega) (by omega) h)
      · exact (Nat.succ_injective (eq_of_eliasGamma_prefix (by omega) (by omega) h)).symm
    subst hn
    rw [e, e', List.prefix_append_right_inj] at hqq'
    rw [e, e', B.prefixFree n p hB p' hB' hqq']

lemma mem_withLength {B : Computer} {x p : List Bool} {n y : ℕ} (h : x ∈ B.run p n) :
    x ∈ (withLength B).run (eliasGamma (n + 1) ++ p) y := by
  simp only [withLength, sdParse_eliasGamma_append, Part.coe_some, Part.bind_some]
  exact h

end Computer

/-- The program `γ(l(x) + 1) x` prints `x` whatever the side information. -/
lemma mem_withLength_lengthComputer (x : List Bool) (y : ℕ) :
    x ∈ (Computer.withLength lengthComputer).run (eliasGamma (x.length + 1) ++ x) y :=
  Computer.mem_withLength (mem_lengthComputer x)

/-- A universal computer prints every string, with any side information: the complexity is
always a minimum program length. -/
theorem Computer.IsUniversal.hasProgram_all {U : Computer} (hU : U.IsUniversal) (x : List Bool)
    (y : ℕ) : U.HasProgram x y :=
  hU.hasProgram _ ⟨_, mem_withLength_lengthComputer x y⟩

lemma log2_le_logb (n : ℕ) : (Nat.log2 n : ℝ) ≤ logb 2 n := Real.log2_le_logb n

/-- **Theorem 14.2.3 (Upper bound on Kolmogorov complexity), (14.8).**
`K(x | y) ≤ K(x | l(x)) + 2 log₂ (l(x) + 1) + c`: a self-delimiting description of `l(x)` in
`2 ⌊log₂ (l(x) + 1)⌋ + 1` bits, followed by the shortest program for `x` given `l(x)`. -/
theorem complexity_le_complexity_length_add {U : Computer} (hU : U.IsUniversal) :
    ∃ c, ∀ (x : List Bool) (y : ℕ),
      (U.complexity x y : ℝ) ≤ U.complexity x x.length + 2 * logb 2 (x.length + 1) + c := by
  obtain ⟨s, hs⟩ := hU.mem_run (Computer.withLength U)
  refine ⟨s.length + 1, fun x y => ?_⟩
  obtain ⟨p, hp, hlen⟩ := Computer.exists_program_eq_complexity (hU.hasProgram_all x x.length)
  have h := Computer.complexity_le (hs (Computer.mem_withLength (y := y) hp))
  rw [List.length_append, List.length_append, length_eliasGamma, hlen] at h
  have hlog := log2_le_logb (x.length + 1)
  push_cast at hlog
  have : (U.complexity x y : ℝ) ≤ s.length + (2 * Nat.log2 (x.length + 1) + 1 +
      U.complexity x x.length) := by exact_mod_cast h
  linarith

/-- Combining Theorems 14.2.2 and 14.2.3, `K(x | y) ≤ l(x) + 2 log₂ (l(x) + 1) + c`. -/
theorem complexity_le_length_add {U : Computer} (hU : U.IsUniversal) :
    ∃ c, ∀ (x : List Bool) (y : ℕ),
      (U.complexity x y : ℝ) ≤ x.length + 2 * logb 2 (x.length + 1) + c := by
  obtain ⟨c₁, h₁⟩ := complexity_length_le hU
  obtain ⟨c₂, h₂⟩ := complexity_le_complexity_length_add hU
  refine ⟨c₁ + c₂, fun x y => ?_⟩
  have := h₂ x y
  have h1 : (U.complexity x x.length : ℝ) ≤ x.length + c₁ := by exact_mod_cast h₁ x
  linarith

/-! ### Examples 14.2.1 and 14.2.4 -/

/-- The empty program prints `f n` given `n`; no other program halts. -/
def printFixed (f : ℕ → List Bool) (p : List Bool) (n : ℕ) : Option (List Bool) :=
  bif decide (p = []) then some (f n) else none

lemma computable_printFixed {f : ℕ → List Bool} (hf : Primrec f) : Computable₂ (printFixed f) :=
  (Primrec.cond ((Primrec.eq (α := List Bool)).decide.comp Primrec.fst (Primrec.const []))
    (Primrec.option_some.comp (hf.comp Primrec.snd)) (Primrec.const none)).to_comp

/-- The computer printing `f n` from the empty program. -/
def fixedComputer (f : ℕ → List Bool) (hf : Primrec f) : Computer :=
  Computer.ofOption (printFixed f) (computable_printFixed hf) fun n p hp q hq _ => by
    simp only [Set.mem_ofPred_eq, printFixed] at hp hq
    cases p <;> cases q <;> simp_all

/-- A string computable from its length has bounded complexity given its length. -/
theorem complexity_fixed_le {U : Computer} (hU : U.IsUniversal) {f : ℕ → List Bool}
    (hf : Primrec f) : ∃ c, ∀ n, U.complexity (f n) n ≤ c := by
  obtain ⟨s, hs⟩ := hU.mem_run (fixedComputer f hf)
  refine ⟨s.length, fun n => ?_⟩
  have h : f n ∈ (fixedComputer f hf).run [] n := Computer.mem_ofOption_run (by simp [printFixed])
  simpa using Computer.complexity_le (hs h)

/-- **Example 14.2.1 (A sequence of `n` zeros), (14.15).** `K(00 ⋯ 0 | n) ≤ c` for all `n`. -/
theorem complexity_zeros_le {U : Computer} (hU : U.IsUniversal) :
    ∃ c, ∀ n, U.complexity (List.replicate n false) n ≤ c := by
  have hf : Primrec fun n : ℕ => List.replicate n false :=
    (Primrec.list_map Primrec.list_range (Primrec.const false).to₂).of_eq fun n => by
      simp [List.map_const']
  exact complexity_fixed_le hU hf

/-- The alternating sequence `0101 ⋯` of length `n`. -/
def alternating (n : ℕ) : List Bool := (List.range n).map fun i => decide (i % 2 = 1)

/-- **Example 14.2.4 (Repeating sequence `0101 ⋯ 01`), (14.18).** `K(0101 ⋯ | n) ≤ c`. -/
theorem complexity_alternating_le {U : Computer} (hU : U.IsUniversal) :
    ∃ c, ∀ n, U.complexity (alternating n) n ≤ c := by
  have hf : Primrec alternating :=
    Primrec.list_map Primrec.list_range (Primrec.eq.decide.comp (Primrec.nat_mod.comp
      Primrec.snd (Primrec.const 2)) (Primrec.const 1)).to₂
  exact complexity_fixed_le hU hf

end InfoTheory
