/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Computability.PartrecCode
public import InfoTheoryLib.Kolmogorov.Programs

/-!
# A universal computer

We construct a universal computer, so that the results of this chapter, stated for an arbitrary
universal computer, are not vacuous. The construction follows the classical one. A program for
`U` is a self-delimiting description of the index `e` of a partial recursive function `φₑ`
(Mathlib's `Nat.Partrec.Code`), followed by a program `p` for it. The function `φₑ` need not have
a prefix-free domain, so `U` runs `φₑ` step by step and accepts `p` only if no program
comparable with `p` (a prefix or an extension of `p`) halted at an earlier or the same step.
This keeps the halting programs of `U` prefix-free, and does not change `φₑ` when its domain is
already prefix-free.

## Main definitions

* `haltTest c m t`: the code `c` halts on the input `m` within `t` steps.
* `firstAmongComparable c p y t`: no program comparable with `p` (other than `p`) halts with side
  information `y` within `t` steps.
* `universalComputer`: the universal computer.

## Main statements

* `universalComputer_isUniversal`: the universal computer simulates every computer.
* `exists_isUniversal`: a universal computer exists.

## Implementation notes

The step-bounded evaluation is `Nat.Partrec.Code.evaln`, which only halts on inputs smaller than
the number of steps, so that the condition of `firstAmongComparable` involves finitely many
programs. Programs and side information `(p, y)` are passed to the codes through their
`Encodable` code.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 14.1
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code Encodable Denumerable

@[expose] public noncomputable section

namespace InfoTheory

/-- The code `c` halts on the input `m` within `t` steps. -/
def haltTest (c : Code) (m t : ℕ) : Bool := (evaln t c m).isSome

/-- `u` and `v` are comparable: one is a prefix of the other. -/
def comparableB (u v : List Bool) : Bool :=
  decide (v.take u.length = u) || decide (u.take v.length = v)

lemma comparableB_iff {u v : List Bool} : comparableB u v = true ↔ u <+: v ∨ v <+: u := by
  simp only [comparableB, Bool.or_eq_true, decide_eq_true_eq, List.prefix_iff_eq_take]
  constructor <;> rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr h.symm
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- The condition at the input `m`: if `m` codes a program `q` comparable with and distinct from
`p`, with the side information `y`, then `c` has not halted on it within `t` steps. -/
def notEarlierAt (c : Code) (p : List Bool) (y t m : ℕ) : Bool :=
  Option.elim (decode₂ (List Bool × ℕ) m) true fun r =>
    !(decide (r.2 = y) && comparableB r.1 p && !decide (r.1 = p)) || !(evaln t c m).isSome

/-- No program comparable with `p` (other than `p`) halts with side information `y` within `t`
steps. -/
def firstAmongComparable (c : Code) (p : List Bool) (y t : ℕ) : Bool :=
  (List.range t).foldr (fun m b => notEarlierAt c p y t m && b) true

lemma foldr_and_eq_true {g : ℕ → Bool} (l : List ℕ) :
    l.foldr (fun m b => g m && b) true = true ↔ ∀ m ∈ l, g m = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma firstAmongComparable_iff {c : Code} {p : List Bool} {y t : ℕ} :
    firstAmongComparable c p y t = true ↔ ∀ m < t, notEarlierAt c p y t m = true := by
  rw [firstAmongComparable, foldr_and_eq_true]
  simp

lemma notEarlierAt_some {c : Code} {p q : List Bool} {y y' t m : ℕ}
    (hm : decode₂ (List Bool × ℕ) m = some (q, y')) :
    notEarlierAt c p y t m = true ↔
      (y' = y → comparableB q p = true → q ≠ p → evaln t c m = none) := by
  simp only [notEarlierAt, hm, Option.elim_some]
  by_cases hy : y' = y <;> cases hb : comparableB q p <;> by_cases hqp : q = p <;>
    cases he : evaln t c m <;> simp_all

lemma notEarlierAt_encode {c : Code} {p q : List Bool} {y t : ℕ} :
    notEarlierAt c p y t (encode (q, y)) = true ↔
      ((q <+: p ∨ p <+: q) → q ≠ p → evaln t c (encode (q, y)) = none) := by
  rw [notEarlierAt_some (encodek₂ (q, y)), ← comparableB_iff]
  simp

/-! ### Computability -/

lemma primrec_comparableB : Primrec₂ comparableB :=
  Primrec.or.comp
    ((Primrec.eq (α := List Bool)).decide.comp (Primrec.list_take.comp
      (Primrec.list_length.comp Primrec.fst) Primrec.snd) Primrec.fst)
    ((Primrec.eq (α := List Bool)).decide.comp (Primrec.list_take.comp
      (Primrec.list_length.comp Primrec.snd) Primrec.fst) Primrec.snd)

/-- The arguments of the computation: the code, the program, the side information. -/
abbrev Args := Code × List Bool × ℕ

lemma primrec_evaln_args {t : Args × ℕ → ℕ} {m : Args × ℕ → ℕ} (ht : Primrec t) (hm : Primrec m) :
    Primrec fun b : Args × ℕ => evaln (t b) b.1.1 (m b) :=
  primrec_evaln.comp ((ht.pair (Primrec.fst.comp Primrec.fst)).pair hm)

lemma primrec_notEarlierAt :
    Primrec fun b : (Args × ℕ) × ℕ => notEarlierAt b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2 b.2 := by
  have hdec : Primrec fun b : (Args × ℕ) × ℕ => decode₂ (List Bool × ℕ) b.2 :=
    Primrec.decode₂.comp Primrec.snd
  have hev : Primrec fun b : (Args × ℕ) × ℕ => evaln b.1.2 b.1.1.1 b.2 :=
    primrec_evaln.comp ((Primrec.snd.comp Primrec.fst).pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) |>.pair Primrec.snd)
  have hg : Primrec₂ fun (b : (Args × ℕ) × ℕ) (r : List Bool × ℕ) =>
      !(decide (r.2 = b.1.1.2.2) && comparableB r.1 b.1.1.2.1 && !decide (r.1 = b.1.1.2.1)) ||
        !(evaln b.1.2 b.1.1.1 b.2).isSome := by
    refine Primrec.or.comp (Primrec.not.comp (Primrec.and.comp (Primrec.and.comp ?_ ?_)
      (Primrec.not.comp ?_))) (Primrec.not.comp (Primrec.option_isSome.comp (hev.comp
        Primrec.fst)))
    · exact (Primrec.eq (α := ℕ)).decide.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    · exact primrec_comparableB.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    · exact (Primrec.eq (α := List Bool)).decide.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  refine (Primrec.option_casesOn hdec (Primrec.const true) hg).of_eq fun b => ?_
  simp only [notEarlierAt]
  cases decode₂ (List Bool × ℕ) b.2 <;> rfl

lemma primrec_firstAmongComparable :
    Primrec fun b : Args × ℕ => firstAmongComparable b.1.1 b.1.2.1 b.1.2.2 b.2 := by
  have h := Primrec.list_foldr (f := fun b : Args × ℕ => List.range b.2) (g := fun _ => true)
    (h := fun b (mb : ℕ × Bool) => notEarlierAt b.1.1 b.1.2.1 b.1.2.2 b.2 mb.1 && mb.2)
    (Primrec.list_range.comp Primrec.snd) (Primrec.const true)
    (Primrec.and.comp (primrec_notEarlierAt.comp (Primrec.fst.pair (Primrec.fst.comp
      Primrec.snd))) (Primrec.snd.comp Primrec.snd)).to₂
  exact h

/-- The output after `t` steps, if the program was the first among the comparable ones to halt. -/
def trimmedOut (c : Code) (p : List Bool) (y t : ℕ) : Option (List Bool) :=
  bif firstAmongComparable c p y t then (evaln t c (encode (p, y))).bind fun v => decode v
  else none

lemma primrec_trimmedOut : Primrec fun b : Args × ℕ => trimmedOut b.1.1 b.1.2.1 b.1.2.2 b.2 := by
  refine Primrec.cond primrec_firstAmongComparable (Primrec.option_bind
    (primrec_evaln_args Primrec.snd (Primrec.encode.comp ((Primrec.fst.comp (Primrec.snd.comp
      Primrec.fst)).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
    (Primrec.decode.comp Primrec.snd).to₂) (Primrec.const none)

lemma primrec_haltTest_args :
    Primrec fun b : Args × ℕ => haltTest b.1.1 (encode (b.1.2.1, b.1.2.2)) b.2 :=
  Primrec.option_isSome.comp (primrec_evaln_args Primrec.snd (Primrec.encode.comp
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))

/-- The simulation of the code `c` on the program `p` with side information `y`: find the first
step `t` at which it halts, and output its result if no comparable program halted by then. -/
def simulate (a : Args) : Part (List Bool) :=
  (Nat.rfind fun t => Part.some (haltTest a.1 (encode (a.2.1, a.2.2)) t)).bind fun t =>
    (trimmedOut a.1 a.2.1 a.2.2 t : Part (List Bool))

lemma partrec_simulate : Partrec simulate := by
  have hp : Computable₂ fun (a : Args) (t : ℕ) => haltTest a.1 (encode (a.2.1, a.2.2)) t :=
    primrec_haltTest_args.to_comp
  have ho : Computable₂ fun (a : Args) (t : ℕ) => trimmedOut a.1 a.2.1 a.2.2 t :=
    primrec_trimmedOut.to_comp
  exact (Partrec.rfind hp.partrec₂).bind (Computable.ofOption ho).to₂

/-- **The universal computer**: read a self-delimiting index `e`, then simulate the `e`-th partial
recursive function on the rest of the program. -/
def universalRun (q : List Bool) (y : ℕ) : Part (List Bool) :=
  (sdParse q : Part (List Bool × ℕ)).bind fun r => simulate (ofNat Code r.2, r.1, y)

lemma partrec_universalRun : Partrec₂ universalRun := by
  refine Partrec.to₂ (f := fun a : List Bool × ℕ => universalRun a.1 a.2) ?_
  exact (Computable.ofOption (primrec_sdParse.to_comp.comp Computable.fst)).bind
    (partrec_simulate.comp ((Computable.ofNat Code |>.comp
      (Computable.snd.comp Computable.snd)).pair
      ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.fst)))).to₂

/-! ### The halting programs of a simulation -/

lemma mem_simulate {c : Code} {p : List Bool} {y : ℕ} {x : List Bool} :
    x ∈ simulate (c, p, y) ↔ ∃ t, (evaln t c (encode (p, y))).isSome = true ∧
      (∀ s < t, (evaln s c (encode (p, y))).isSome = false) ∧
      firstAmongComparable c p y t = true ∧
      ((evaln t c (encode (p, y))).bind fun v => decode v) = some x := by
  rw [simulate, Part.mem_bind_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨h1, h2⟩ := Nat.mem_rfind.1 ht
    have h1' := (Part.mem_some_iff.1 h1).symm
    refine ⟨t, h1', fun s hs => (Part.mem_some_iff.1 (h2 hs)).symm, ?_⟩
    simp only [trimmedOut] at hx
    cases hf : firstAmongComparable c p y t
    · simp [hf] at hx
    · simp only [hf, Bool.cond_true, Part.mem_coe] at hx
      exact ⟨rfl, hx⟩
  · rintro ⟨t, h1, h2, hf, hx⟩
    refine ⟨t, Nat.mem_rfind.2 ⟨Part.mem_some_iff.2 h1.symm, fun {s} hs =>
      Part.mem_some_iff.2 (h2 s hs).symm⟩, ?_⟩
    simp only [trimmedOut, hf, Bool.cond_true]
    exact Part.mem_coe.2 hx

/-- The halting programs of a simulation, with a given side information, are prefix-free. -/
lemma simulate_prefixFree (c : Code) (y : ℕ) :
    InformationTheory.IsPrefixFree {p | (simulate (c, p, y)).Dom} := by
  intro p hp p' hp' hpp'
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 hp
  obtain ⟨x', hx'⟩ := Part.dom_iff_mem.1 hp'
  obtain ⟨t, h1, -, hf, -⟩ := mem_simulate.1 hx
  obtain ⟨t', h1', -, hf', -⟩ := mem_simulate.1 hx'
  by_contra hne
  rcases le_total t t' with htt | htt
  · -- `p` halted by step `t ≤ t'`, so `p'` was not the first.
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1
    have hb := evaln_bound (Option.mem_def.2 hv)
    have h := (firstAmongComparable_iff.1 hf') _ (lt_of_lt_of_le hb htt)
    rw [notEarlierAt_encode] at h
    have := h (Or.inl hpp') hne
    rw [evaln_mono htt (Option.mem_def.2 hv)] at this
    exact Option.some_ne_none _ this
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1'
    have hb := evaln_bound (Option.mem_def.2 hv)
    have h := (firstAmongComparable_iff.1 hf) _ (lt_of_lt_of_le hb htt)
    rw [notEarlierAt_encode] at h
    have := h (Or.inr hpp') (Ne.symm hne)
    rw [evaln_mono htt (Option.mem_def.2 hv)] at this
    exact Option.some_ne_none _ this

/-- **The universal computer.** -/
def universalComputer : Computer where
  run := universalRun
  partrec := partrec_universalRun
  prefixFree y := by
    intro q hq q' hq' hqq'
    simp only [Set.mem_ofPred_eq, universalRun, Part.bind_dom] at hq hq'
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨h1', h2'⟩ := hq'
    obtain ⟨⟨p, n⟩, hpn⟩ := Option.isSome_iff_exists.1 (by simpa [Part.ofOption_dom] using h1)
    obtain ⟨⟨p', n'⟩, hpn'⟩ := Option.isSome_iff_exists.1 (by simpa [Part.ofOption_dom] using h1')
    have e := eq_of_sdParse_eq_some hpn
    have e' := eq_of_sdParse_eq_some hpn'
    rw [Part.get_eq_of_mem (Part.mem_coe.2 hpn) h1] at h2
    rw [Part.get_eq_of_mem (Part.mem_coe.2 hpn') h1'] at h2'
    have hc : eliasGamma (n + 1) <+: q' := (List.prefix_append _ _).trans (e ▸ hqq')
    have hc' : eliasGamma (n' + 1) <+: q' := e' ▸ List.prefix_append _ _
    have hn : n = n' := by
      rcases List.prefix_or_prefix_of_prefix hc hc' with h | h
      · exact Nat.succ_injective (eq_of_eliasGamma_prefix (by omega) (by omega) h)
      · exact (Nat.succ_injective (eq_of_eliasGamma_prefix (by omega) (by omega) h)).symm
    subst hn
    rw [e, e', List.prefix_append_right_inj] at hqq'
    rw [e, e', simulate_prefixFree (ofNat Code n) y p h2 p' h2' hqq']

/-! ### Universality -/

/-- The simulation of a code computing a computer with prefix-free programs reproduces it. -/
lemma simulate_eq {A : Computer} {c : Code}
    (hc : ∀ p y, eval c (encode (p, y)) = (A.run p y).map encode) (p : List Bool) (y : ℕ) :
    simulate (c, p, y) = A.run p y := by
  ext x
  rw [mem_simulate]
  constructor
  · rintro ⟨t, -, -, -, hx⟩
    obtain ⟨v, hv, hdec⟩ := Option.bind_eq_some_iff.1 hx
    have hev := evaln_sound (Option.mem_def.2 hv)
    rw [hc, Part.mem_map_iff] at hev
    obtain ⟨x', hx', rfl⟩ := hev
    rw [encodek] at hdec
    rw [← Option.some_injective _ hdec]
    exact hx'
  · intro hx
    have hev : encode x ∈ eval c (encode (p, y)) := by
      rw [hc]
      exact Part.mem_map _ hx
    obtain ⟨k, hk⟩ := evaln_complete.1 hev
    classical
    have hex : ∃ t, (evaln t c (encode (p, y))).isSome = true :=
      ⟨k, by rw [Option.mem_def.1 hk]; rfl⟩
    set t := Nat.find hex
    have ht : (evaln t c (encode (p, y))).isSome = true := Nat.find_spec hex
    have hmin : ∀ s < t, (evaln s c (encode (p, y))).isSome = false := fun s hs => by
      simpa using Nat.find_min hex hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ht
    have hvx : v = encode x := by
      have := evaln_sound (Option.mem_def.2 hv)
      rw [hc] at this
      obtain ⟨x', hx', rfl⟩ := (Part.mem_map_iff _).1 this
      rw [Part.mem_unique hx' hx]
    refine ⟨t, ht, hmin, ?_, by rw [hv, hvx]; simp [encodek]⟩
    -- No comparable program has halted by step `t`, since `A`'s programs are prefix-free.
    refine firstAmongComparable_iff.2 fun m _ => ?_
    rcases hd : decode₂ (List Bool × ℕ) m with _ | ⟨q, y'⟩
    · simp [notEarlierAt, hd]
    · rw [notEarlierAt_some hd]
      rintro rfl hcmp hqp
      have hm : encode (q, y') = m := Encodable.mem_decode₂.1 hd
      by_contra hne
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
      have hw' := evaln_sound (Option.mem_def.2 hw)
      rw [← hm, hc] at hw'
      obtain ⟨z, hz, -⟩ := (Part.mem_map_iff _).1 hw'
      have hpre := A.prefixFree y'
      rcases comparableB_iff.1 hcmp with h | h
      · exact hqp (hpre q (Computer.dom_of_mem_run hz) p (Computer.dom_of_mem_run hx) h)
      · exact hqp (hpre p (Computer.dom_of_mem_run hx) q (Computer.dom_of_mem_run hz) h).symm

/-- **The universal computer simulates every computer**: the simulation prefix of a computer `A`
is the self-delimiting description of the index of a code computing `A`. -/
theorem universalComputer_isUniversal : universalComputer.IsUniversal := by
  intro A
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 A.partrec
  refine ⟨eliasGamma (encode c + 1), fun p y => ?_⟩
  have hc' : ∀ p y, eval c (encode (p, y)) = (A.run p y).map encode := fun p y => by
    rw [hc]
    simp [encodek]
  change universalRun _ y = _
  rw [universalRun, sdParse_eliasGamma_append, Part.coe_some, Part.bind_some]
  simp only [ofNat_encode]
  exact simulate_eq hc' p y

/-- **A universal computer exists.** -/
theorem exists_isUniversal : ∃ U : Computer, U.IsUniversal :=
  ⟨universalComputer, universalComputer_isUniversal⟩

end InfoTheory
