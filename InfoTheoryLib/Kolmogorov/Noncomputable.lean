/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Kolmogorov.Programs

/-!
# The noncomputability of Kolmogorov complexity

Kolmogorov complexity is not computable (Section 14.7). The proof is the Berry paradox: if
`K` were computable, the program "print the first string `x` with `K(x) ≥ n`" would describe
such a string with `2 log n + c` bits, which is less than `n` for `n` large.

## Main definitions

* `berryTest K n m`: the string coded by `m` has `K ≥ n`.
* `berryComputer K hK`: for a computable `K`, the computer printing the first string (in the
  order of the codes) with `K ≥ n`, from a self-delimiting description of `n`.

## Main statements

* `not_computable_complexity`: **Section 14.7**, the Kolmogorov complexity `x ↦ K_U(x)` of a
  universal computer is not computable.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 14.7
-/

open Encodable

@[expose] public noncomputable section

namespace InfoTheory

/-- The string coded by `m` has complexity at least `n`. -/
def berryTest (K : List Bool → ℕ) (n m : ℕ) : Bool :=
  Option.casesOn (decode (α := List Bool) m) false fun x => decide (n ≤ K x)

/-- Accept only a self-delimiting description of a number, with nothing after it. -/
def sdParseExact (q : List Bool) : Option ℕ :=
  (sdParse q).bind fun r => bif decide (r.1 = []) then some r.2 else none

lemma computable_sdParseExact : Computable sdParseExact :=
  (Primrec.option_bind primrec_sdParse (Primrec.cond ((Primrec.eq (α := List Bool)).decide.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.const [])) (Primrec.option_some.comp
      (Primrec.snd.comp Primrec.snd)) (Primrec.const none)).to₂).to_comp

lemma eq_of_sdParseExact {q : List Bool} {n : ℕ} (h : sdParseExact q = some n) :
    q = eliasGamma (n + 1) := by
  simp only [sdParseExact, Option.bind_eq_some_iff] at h
  obtain ⟨⟨p, k⟩, hpk, h⟩ := h
  cases hp : decide (p = [])
  · simp [hp] at h
  · simp only [hp, Bool.cond_true, Option.some.injEq] at h
    simp only [decide_eq_true_eq] at hp
    subst hp h
    simpa using eq_of_sdParse_eq_some hpk

/-- The run of the Berry computer: decode `n`, then print the first string with `K ≥ n`. -/
def berryRun (K : List Bool → ℕ) (q : List Bool) (_ : ℕ) : Part (List Bool) :=
  (sdParseExact q : Part ℕ).bind fun n =>
    (Nat.rfind fun m => Part.some (berryTest K n m)).bind fun m =>
      (decode (α := List Bool) m : Part (List Bool))

/-- **The Berry computer**, for a computable complexity function `K`. -/
def berryComputer (K : List Bool → ℕ) (hK : Computable K) : Computer where
  run := berryRun K
  partrec := by
    have ht : Computable₂ fun (n m : ℕ) => berryTest K n m :=
      (Computable.option_casesOn (Computable.decode.comp Computable.snd) (Computable.const false)
        ((Primrec.nat_le.decide.to_comp.comp (Computable.fst.comp Computable.fst)
          (hK.comp Computable.snd)).to₂)).of_eq fun _ => rfl
    have hn : Partrec fun n : ℕ => (Nat.rfind fun m => Part.some (berryTest K n m)).bind
        fun m => (decode (α := List Bool) m : Part (List Bool)) :=
      (Partrec.rfind ht.partrec₂).bind (Computable.ofOption (Computable.decode.comp
        Computable.snd)).to₂
    refine Partrec.to₂ (f := fun a : List Bool × ℕ => berryRun K a.1 a.2) ?_
    exact (Computable.ofOption (computable_sdParseExact.comp Computable.fst)).bind
      (hn.comp Computable.snd).to₂
  prefixFree _ := by
    intro q hq q' hq' hqq'
    simp only [Set.mem_ofPred_eq, berryRun, Part.bind_dom] at hq hq'
    obtain ⟨h1, -⟩ := hq
    obtain ⟨h1', -⟩ := hq'
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (by simpa [Part.ofOption_dom] using h1)
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.1 (by simpa [Part.ofOption_dom] using h1')
    rw [eq_of_sdParseExact hn, eq_of_sdParseExact hn'] at hqq' ⊢
    rw [eq_of_eliasGamma_prefix (by omega) (by omega) hqq']

/-- Some string has complexity at least `n`. -/
lemma exists_complexity_ge {U : Computer} (hU : U.IsUniversal) (n : ℕ) :
    ∃ x : List Bool, n ≤ U.complexity x 0 := by
  classical
  by_contra h
  push Not at h
  have := U.card_lt_two_pow_of_complexity_lt (y := 0) (k := n)
    (Finset.univ.image (List.ofFn : (Fin n → Bool) → List Bool))
    fun w _ => ⟨hU.hasProgram_all w 0, h w⟩
  rw [Finset.card_image_of_injective _ List.ofFn_injective] at this
  simp at this

/-- **Section 14.7 (Noncomputability of Kolmogorov complexity).** The complexity
`x ↦ K_U(x)` of a universal computer is not computable. -/
theorem not_computable_complexity {U : Computer} (hU : U.IsUniversal) :
    ¬ Computable fun x => U.complexity x 0 := by
  intro hK
  obtain ⟨s, hs⟩ := hU.mem_run (berryComputer _ hK)
  obtain ⟨a, ha⟩ : ∃ a, a = s.length + 2 := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = 4 ^ a := ⟨_, rfl⟩
  -- The Berry program for `n` halts with a string of complexity at least `n`.
  obtain ⟨x₀, hx₀⟩ := exists_complexity_ge hU n
  have htest : berryTest (fun x => U.complexity x 0) n (encode x₀) = true := by
    simp [berryTest, encodek, hx₀]
  obtain ⟨m, hm, -⟩ := Nat.rfind_min' (p := berryTest (fun x => U.complexity x 0) n) htest
  have hm' := Nat.rfind_spec hm
  simp only [PFun.coe_val, Part.mem_some_iff] at hm'
  unfold berryTest at hm'
  rcases hd : decode (α := List Bool) m with _ | x
  · simp [hd] at hm'
  simp only [hd] at hm'
  have hnx : n ≤ U.complexity x 0 := of_decide_eq_true hm'.symm
  have hrun : x ∈ (berryComputer (fun x => U.complexity x 0) hK).run (eliasGamma (n + 1)) 0 := by
    change x ∈ berryRun (fun x => U.complexity x 0) (eliasGamma (n + 1)) 0
    have hparse : sdParseExact (eliasGamma (n + 1)) = some n := by
      have := sdParse_eliasGamma_append n []
      simp only [List.append_nil] at this
      simp [sdParseExact, this]
    rw [berryRun, hparse, Part.coe_some, Part.bind_some, Part.mem_bind_iff]
    exact ⟨m, hm, Part.mem_coe.2 hd⟩
  -- Its complexity is at most `|s| + 2 log₂ (n + 1) + 1 < n`.
  have hle := Computer.complexity_le (hs hrun)
  rw [List.length_append, length_eliasGamma] at hle
  have hlog : Nat.log2 (n + 1) ≤ 2 * a := by
    have : Nat.log2 (n + 1) < 2 * a + 1 := by
      rw [Nat.log2_lt (n := n + 1) (by omega)]
      have : n + 1 < 2 ^ (2 * a + 1) := by
        have h4 : n = 2 ^ (2 * a) := by rw [hn, pow_mul]; norm_num
        have h5 : 2 ≤ n := by
          rw [hn]
          calc 2 ≤ 4 := by norm_num
            _ ≤ 4 ^ a := Nat.le_self_pow (by omega) 4
        have h6 : 2 ^ (2 * a + 1) = n + n := by rw [pow_succ, ← h4]; ring
        rw [h6]
        omega
      exact this
    omega
  have hbig : s.length + (2 * (2 * a) + 1) < n := by
    have h1 : s.length + 1 ≤ 4 ^ s.length := Nat.lt_pow_self (by norm_num)
    have h2 : n = 16 * 4 ^ s.length := by rw [hn, ha, pow_add]; ring
    rw [h2]
    generalize 4 ^ s.length = P at h1 ⊢
    rw [ha]
    omega
  omega

end InfoTheory
