/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Kolmogorov.BinaryStrings

/-!
# Universal probability, Chaitin's Ω and universal gambling

Feeding a computer a program of fair coin flips, it halts with probability
`Ω = ∑_{p halts} 2^{-l(p)} ≤ 1`, and prints `x` with probability
`P_U(x) = ∑_{U(p) = x} 2^{-l(p)}`, the universal probability of `x`. A universal computer
dominates every other one, `P_U(x) ≥ 2^{-c_A} P_A(x)` (Theorem 14.6.1), and
`P_U(x) ≥ 2^{-K(x)}` (the easy half of Theorem 14.11.1). Betting `2^{-K(x)}` on each string at
fair odds yields wealth `S(x) ≥ 2^{l(x) - K(x)}` (Theorem 14.9.1).

## Main definitions

* `Computer.universalProb A x y`: `P_A(x | y)` (14.66).
* `Computer.omega A`: Chaitin's `Ω` (14.70).
* `Computer.gamblingWealth U x`: the wealth `S(x)` of universal gambling (14.76)–(14.79).
* `indicatorString n S`, `Computer.structureFunction U k x n`: the Kolmogorov structure function
  `K_k(xⁿ | n)` (14.107), and `Computer.minimalSufficientLength`, the least `k` of (14.108).

## Main statements

* `Computer.universalProb_le_one`, `Computer.omega_le_one`, `Computer.IsUniversal.omega_pos`.
* `Computer.IsUniversal.universalProb_ge`: **Theorem 14.6.1**, `P_U(x) ≥ 2^{-c_A} P_A(x)`.
* `Computer.two_pow_neg_complexity_le_universalProb`: **(14.69), (14.91)**, the lower half of
  **Theorem 14.11.1**, `2^{-K(x)} ≤ P_U(x)`, that is `log₂ 1/P_U(x) ≤ K(x)` (14.90).
* `Computer.summable_two_pow_neg_complexity`, `Computer.tsum_two_pow_neg_complexity_le_omega`:
  **(14.77)**, the bets of universal gambling sum to at most `Ω ≤ 1`.
* `Computer.length_le_logb_gamblingWealth_add`: **Theorem 14.9.1**, `log₂ S(x) + K(x) ≥ l(x)`.
* `Computer.IsUniversal.structureFunction_le_length`,
  `Computer.IsUniversal.structureFunction_eq_zero`, `Computer.structureFunction_antitone`:
  properties of the structure function (Section 14.12).

## Implementation notes

All quantities are taken with side information `0` (no information) unless stated. The
upper half of Theorem 14.11.1, `K(x) ≤ log₂ 1/P_U(x) + c`, requires simulating all programs of
the universal computer to build a code tree; it is not formalized, and neither are the
properties of `Ω` that rest on such simulations (its noncomputability and Theorem 14.8.1).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 14.6–14.12
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

namespace Computer

variable (A : Computer)

/-- The programs that print `x` given `y`. -/
abbrev programsFor (x : List Bool) (y : ℕ) : Set (List Bool) := {p | x ∈ A.run p y}

lemma isPrefixFree_programsFor (x : List Bool) (y : ℕ) :
    InformationTheory.IsPrefixFree (A.programsFor x y) :=
  (A.prefixFree y).anti fun _ hp => dom_of_mem_run hp

/-- **(14.66)** The universal probability `P_A(x | y) = ∑_{A(p, y) = x} 2^{-l(p)}`, the probability
that a program of fair coin flips prints `x`. -/
def universalProb (x : List Bool) (y : ℕ) : ℝ :=
  ∑' p : A.programsFor x y, (1 / 2 : ℝ) ^ (p : List Bool).length

lemma summable_programsFor (x : List Bool) (y : ℕ) :
    Summable fun p : A.programsFor x y => (1 / 2 : ℝ) ^ (p : List Bool).length := by
  have := (A.isPrefixFree_programsFor x y).summable_one_div_card_pow_length (α := Bool)
  simpa [Fintype.card_bool] using this

lemma universalProb_nonneg (x : List Bool) (y : ℕ) : 0 ≤ A.universalProb x y :=
  tsum_nonneg fun _ => by positivity

lemma universalProb_le_one (x : List Bool) (y : ℕ) : A.universalProb x y ≤ 1 := by
  have := (A.isPrefixFree_programsFor x y).tsum_one_div_card_pow_length_le_one (α := Bool)
  simpa [Fintype.card_bool, universalProb] using this

variable {A}

/-- **(14.69), (14.91)** The shortest program contributes `2^{-K(x | y)}`:
`2^{-K(x | y)} ≤ P(x | y)`, the lower half of **Theorem 14.11.1**. -/
theorem two_pow_neg_complexity_le_universalProb {x : List Bool} {y : ℕ} (hx : A.HasProgram x y) :
    (1 / 2 : ℝ) ^ A.complexity x y ≤ A.universalProb x y := by
  obtain ⟨p, hp, hlen⟩ := exists_program_eq_complexity hx
  have := (A.summable_programsFor x y).le_tsum (⟨p, hp⟩ : A.programsFor x y)
    fun _ _ => by positivity
  rw [← hlen]
  exact this

/-- **(14.90)** `log₂ 1/P(x | y) ≤ K(x | y)`. -/
theorem logb_inv_universalProb_le {x : List Bool} {y : ℕ} (hx : A.HasProgram x y) :
    logb 2 (A.universalProb x y)⁻¹ ≤ A.complexity x y := by
  have h := two_pow_neg_complexity_le_universalProb hx
  have hpos : 0 < (1 / 2 : ℝ) ^ A.complexity x y := by positivity
  have h' : (A.universalProb x y)⁻¹ ≤ 2 ^ A.complexity x y := by
    rw [inv_le_comm₀ (hpos.trans_le h) (by positivity)]
    simpa [one_div] using h
  calc logb 2 (A.universalProb x y)⁻¹ ≤ logb 2 ((2 : ℝ) ^ A.complexity x y) :=
        logb_le_logb_of_le (by norm_num) (inv_pos.2 (hpos.trans_le h)) h'
    _ = A.complexity x y := by rw [logb_pow, logb_self_eq_one (by norm_num), mul_one]

/-- **Theorem 14.6.1, (14.67)–(14.68).** A universal computer dominates every computer:
`P_U(x | y) ≥ 2^{-c_A} P_A(x | y)`, where `c_A` is the length of the simulation program. -/
theorem IsUniversal.universalProb_ge {U : Computer} (hU : U.IsUniversal) (A : Computer) :
    ∃ c : ℕ, ∀ x y, (1 / 2 : ℝ) ^ c * A.universalProb x y ≤ U.universalProb x y := by
  obtain ⟨s, hs⟩ := hU A
  refine ⟨s.length, fun x y => ?_⟩
  set e : A.programsFor x y → U.programsFor x y := fun p => ⟨s ++ p, by
    change x ∈ U.run (s ++ p) y
    rw [hs]
    exact p.2⟩
  have he : Function.Injective e := fun p q h => by
    have := congrArg Subtype.val h
    exact Subtype.ext (List.append_cancel_left this)
  rw [universalProb, ← tsum_mul_left]
  refine ((A.summable_programsFor x y).mul_left _).tsum_le_tsum_of_inj e he
    (fun _ _ => by positivity) (fun p => le_of_eq ?_) (U.summable_programsFor x y)
  simp only [e, List.length_append, pow_add]

/-! ### Chaitin's Ω -/

variable (A) in
/-- **(14.70)** Chaitin's `Ω = ∑_{p halts} 2^{-l(p)}`, the probability that the computer halts on
a program of fair coin flips. -/
def omega : ℝ := ∑' p : A.haltingSet 0, (1 / 2 : ℝ) ^ (p : List Bool).length

lemma omega_nonneg : 0 ≤ A.omega := tsum_nonneg fun _ => by positivity

/-- `Ω ≤ 1`, by the Kraft inequality. -/
lemma omega_le_one : A.omega ≤ 1 := A.tsum_halting_le_one 0

/-- A universal computer halts with positive probability: `Ω > 0`. -/
lemma IsUniversal.omega_pos {U : Computer} (hU : U.IsUniversal) : 0 < U.omega := by
  obtain ⟨p, hp⟩ := hU.hasProgram_all [] 0
  exact (U.summable_halting 0).tsum_pos (fun _ => by positivity)
    ⟨p, dom_of_mem_run hp⟩ (by positivity)

/-- The shortest programs of distinct strings are distinct halting programs: over every finite set
of strings, `∑ₓ 2^{-K(x)} ≤ Ω`. -/
lemma sum_two_pow_neg_complexity_le_omega {U : Computer} (hU : U.IsUniversal)
    (F : Finset (List Bool)) : ∑ x ∈ F, (1 / 2 : ℝ) ^ U.complexity x 0 ≤ U.omega := by
  classical
  choose P hP hlen using fun x => exists_program_eq_complexity (hU.hasProgram_all x 0)
  set e : List Bool → U.haltingSet 0 := fun x => ⟨P x, dom_of_mem_run (hP x)⟩
  have he : Set.InjOn e F := fun x _ x' _ h => by
    have h' : P x = P x' := congrArg Subtype.val h
    exact eq_of_mem_run (hP x) (h' ▸ hP x')
  calc ∑ x ∈ F, (1 / 2 : ℝ) ^ U.complexity x 0
      = ∑ p ∈ F.image e, (1 / 2 : ℝ) ^ (p : List Bool).length := by
        rw [sum_image he]
        exact sum_congr rfl fun x _ => by rw [← hlen x]
    _ ≤ U.omega := (U.summable_halting 0).sum_le_tsum _ fun _ _ => by positivity

/-- **(14.77)** The bets `2^{-K(x)}` of universal gambling are summable. -/
lemma summable_two_pow_neg_complexity {U : Computer} (hU : U.IsUniversal) :
    Summable fun x : List Bool => (1 / 2 : ℝ) ^ U.complexity x 0 :=
  summable_of_sum_le (fun _ => by positivity) (sum_two_pow_neg_complexity_le_omega hU)

/-- **(14.77)** The bets of universal gambling sum to at most `Ω ≤ 1`:
`∑ₓ 2^{-K(x)} ≤ ∑_{p halts} 2^{-l(p)} = Ω`. -/
theorem tsum_two_pow_neg_complexity_le_omega {U : Computer} (hU : U.IsUniversal) :
    ∑' x : List Bool, (1 / 2 : ℝ) ^ U.complexity x 0 ≤ U.omega :=
  (summable_two_pow_neg_complexity hU).tsum_le_of_sum_le (sum_two_pow_neg_complexity_le_omega hU)

/-! ### Universal gambling -/

variable (A) in
/-- **(14.76)–(14.79)** The wealth after betting on the string `x` at fair odds, when the bets
`b(x') = 2^{-K(x')}` are placed on all strings: `S(x) = 2^{l(x)} ∑_{x' ⊒ x} b(x')`. -/
def gamblingWealth (x : List Bool) : ℝ :=
  2 ^ x.length * ∑' x' : {x' : List Bool // x <+: x'}, (1 / 2 : ℝ) ^ A.complexity x' 0

/-- **Theorem 14.9.1, (14.78)–(14.79).** The logarithm of the wealth of universal gambling plus
the complexity of the sequence is at least its length: `log₂ S(x) + K(x) ≥ l(x)`. -/
theorem length_le_logb_gamblingWealth_add {U : Computer} (hU : U.IsUniversal) (x : List Bool) :
    (x.length : ℝ) ≤ logb 2 (U.gamblingWealth x) + U.complexity x 0 := by
  have hs : Summable fun x' : {x' : List Bool // x <+: x'} => (1 / 2 : ℝ) ^ U.complexity x' 0 :=
    (summable_two_pow_neg_complexity hU).comp_injective Subtype.val_injective
  have h1 : (1 / 2 : ℝ) ^ U.complexity x 0 ≤
      ∑' x' : {x' : List Bool // x <+: x'}, (1 / 2 : ℝ) ^ U.complexity x' 0 :=
    hs.le_tsum (⟨x, List.prefix_refl x⟩ : {x' : List Bool // x <+: x'}) fun _ _ => by positivity
  have hpos : 0 < (1 / 2 : ℝ) ^ U.complexity x 0 := by positivity
  have h2 : (2 : ℝ) ^ x.length * (1 / 2) ^ U.complexity x 0 ≤ U.gamblingWealth x :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 := logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h2
  rw [logb_mul (by positivity) hpos.ne', logb_pow, logb_pow, logb_self_eq_one (by norm_num),
    one_div, logb_inv, logb_self_eq_one (by norm_num)] at h3
  linarith

/-! ### The Kolmogorov structure function -/

/-- The indicator string of a set `S` of strings of length `n`, in the order of `allStrings n`. -/
def indicatorString (n : ℕ) (S : Finset (List Bool)) : List Bool :=
  (allStrings n).map fun w => decide (w ∈ S)

lemma indicatorString_injective {n : ℕ} {S T : Finset (List Bool)}
    (hS : ∀ w ∈ S, w.length = n) (hT : ∀ w ∈ T, w.length = n)
    (h : indicatorString n S = indicatorString n T) : S = T := by
  ext w
  constructor <;> intro hw
  · have hl := hS w hw
    have hmem : w ∈ allStrings n := mem_allStrings.2 hl
    have := List.map_inj_left.1 h w hmem
    simpa [hw] using this
  · have hl := hT w hw
    have hmem : w ∈ allStrings n := mem_allStrings.2 hl
    have := List.map_inj_left.1 h w hmem
    simpa [hw] using this

variable (A) in
/-- The values `log₂ |S|` of the sets `S ∋ x` of strings of length `n` whose indicator is printed
by a program of length at most `k`. -/
def structureValues (k : ℕ) (x : List Bool) (n : ℕ) : Set ℝ :=
  {r | ∃ (p : List Bool) (S : Finset (List Bool)), p.length ≤ k ∧ (∀ w ∈ S, w.length = n) ∧
    x ∈ S ∧ indicatorString n S ∈ A.run p n ∧ r = logb 2 S.card}

variable (A) in
/-- **(14.107)** The Kolmogorov structure function `K_k(xⁿ | n)`: the least `log₂ |S|` over the sets
`S ∋ xⁿ` of strings of length `n` whose indicator a program of length at most `k` prints. -/
def structureFunction (k : ℕ) (x : List Bool) (n : ℕ) : ℝ := sInf (A.structureValues k x n)

lemma structureValues_nonneg {k n : ℕ} {x : List Bool} {r : ℝ} (hr : r ∈ A.structureValues k x n) :
    0 ≤ r := by
  obtain ⟨p, S, -, -, hx, -, rfl⟩ := hr
  exact logb_nonneg (by norm_num) (by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩)

/-- The structure function is nonincreasing in `k`. -/
theorem structureFunction_antitone {k k' n : ℕ} {x : List Bool} (hkk' : k ≤ k')
    (hne : (A.structureValues k x n).Nonempty) :
    A.structureFunction k' x n ≤ A.structureFunction k x n :=
  csInf_le_csInf ⟨0, fun _ hr => structureValues_nonneg hr⟩ hne
    fun _ ⟨p, S, hp, hS, hx, hrun, hr⟩ => ⟨p, S, hp.trans hkk', hS, hx, hrun, hr⟩

lemma length_allStrings (n : ℕ) : (allStrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allStrings, List.length_flatMap]
    simp [ih, pow_succ, mul_comm]

/-- **Section 14.12** For `k` beyond a constant, the whole set `{0, 1}ⁿ` is describable, so
`K_k(xⁿ | n) ≤ n`. -/
theorem IsUniversal.structureFunction_le_length {U : Computer} (hU : U.IsUniversal) :
    ∃ c, ∀ k ≥ c, ∀ x : List Bool, U.structureFunction k x x.length ≤ x.length := by
  classical
  have hf : Primrec fun n => indicatorString n (allStrings n).toFinset := by
    refine (Primrec.list_map primrec_allStrings (Primrec.const true).to₂).of_eq fun n => ?_
    have : ∀ w ∈ allStrings n, decide (w ∈ (allStrings n).toFinset) = true := fun w hw => by
      simpa using hw
    rw [indicatorString, List.map_congr_left this]
  obtain ⟨s, hs⟩ := hU.mem_run (fixedComputer _ hf)
  refine ⟨s.length, fun k hk x => ?_⟩
  have hmem : indicatorString x.length (allStrings x.length).toFinset ∈
      U.run (s ++ []) x.length :=
    hs (Computer.mem_ofOption_run (by simp [printFixed]))
  have hval : (x.length : ℝ) ∈ U.structureValues k x x.length := by
    refine ⟨s ++ [], (allStrings x.length).toFinset, by simpa using hk,
      fun w hw => mem_allStrings.1 (List.mem_toFinset.1 hw), List.mem_toFinset.2
        (mem_allStrings.2 rfl), hmem, ?_⟩
    rw [List.toFinset_card_of_nodup (nodup_allStrings _), length_allStrings]
    push_cast
    rw [logb_pow, logb_self_eq_one (by norm_num), mul_one]
  exact csInf_le ⟨0, fun _ hr => structureValues_nonneg hr⟩ hval

/-- **Section 14.12** For `k ≥ K(1_{xⁿ} | n)`, the singleton `{xⁿ}` is describable and
`K_k(xⁿ | n) = 0`. -/
theorem IsUniversal.structureFunction_eq_zero {U : Computer} (hU : U.IsUniversal)
    {x : List Bool} {k : ℕ} (hk : U.complexity (indicatorString x.length {x}) x.length ≤ k) :
    U.structureFunction k x x.length = 0 := by
  obtain ⟨p, hp, hlen⟩ := exists_program_eq_complexity (hU.hasProgram_all
    (indicatorString x.length {x}) x.length)
  have hval : (0 : ℝ) ∈ U.structureValues k x x.length :=
    ⟨p, {x}, hlen ▸ hk, by simp, by simp, hp, by simp⟩
  exact le_antisymm (csInf_le ⟨0, fun _ hr => structureValues_nonneg hr⟩ hval)
    (le_csInf ⟨0, hval⟩ fun _ hr => structureValues_nonneg hr)

variable (A) in
/-- **(14.108)** The length `k*` of a Kolmogorov minimal sufficient statistic: the least `k` with
`K_k(xⁿ | n) + k ≤ K(xⁿ | n) + c`. -/
def minimalSufficientLength (c : ℝ) (x : List Bool) : ℕ :=
  sInf {k : ℕ | A.structureFunction k x x.length + k ≤ A.complexity x x.length + c}

end Computer

end InfoTheory
