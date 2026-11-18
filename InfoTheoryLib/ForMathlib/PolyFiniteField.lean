/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib

/-!
# Nonzero polynomials over large finite fields

A nonzero polynomial over a field has few zeros in a large extension field, by the Schwartz–Zippel
lemma of Mathlib.

## Main statements

* `card_aeval_eq_zero_le`: the fraction of zeros of a polynomial in an extension field.
* `exists_aeval_ne_zero`: a polynomial of small degree has a nonzero value.
* `exists_aeval_ne_zero_of_degreeOf`: a nonzero polynomial whose degree in each variable is less
  than the size of the field has a nonzero value. This is Lemma 19.17 of Yeung.
* `exists_eval_ne_zero_of_degreeOf_lt_card`: a nonzero polynomial over a domain has a nonzero
  value on `S^m` when `S` has more elements than its degree in each variable. This is Lemma 20.12
  of Yeung.
* `exists_aeval_galoisField_ne_zero`: a nonzero polynomial over `𝔽₂` has a nonzero value in
  `𝔽_{2^m}` for all large `m`. This is Lemma 1 of Lecture 16 of El Gamal and Kim.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Lemmas 19.17 and 20.12
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {X k F : Type*} [Fintype X] [Field k] [Field F] [Fintype F] [Algebra k F]

open Classical in
/-- **Schwartz–Zippel lemma** for polynomials over a subfield and for variables of any finite type:
the fraction of the zeros of `P` in `F` is at most `deg P / |F|`. -/
theorem card_aeval_eq_zero_le {P : MvPolynomial X k} (hP : P ≠ 0) :
    (#{α : X → F | MvPolynomial.aeval α P = 0} : ℝ) / (Fintype.card F : ℝ) ^ Fintype.card X ≤
      (P.totalDegree : ℝ) / Fintype.card F := by
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let Q : MvPolynomial (Fin (Fintype.card X)) F :=
    MvPolynomial.map (algebraMap k F) (MvPolynomial.rename e P)
  have hQ : Q ≠ 0 := by
    intro h
    have h₁ : MvPolynomial.rename e P = 0 :=
      MvPolynomial.map_injective _ (algebraMap k F).injective (by simpa [Q] using h)
    exact hP (MvPolynomial.rename_injective e e.injective (by simpa using h₁))
  have hdeg : Q.totalDegree ≤ P.totalDegree :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      (MvPolynomial.totalDegree_rename_le _ _)
  have heval : ∀ f : Fin (Fintype.card X) → F,
      MvPolynomial.eval f Q = MvPolynomial.aeval (f ∘ e) P := by
    intro f
    simp only [Q, MvPolynomial.eval_map, MvPolynomial.aeval_def, MvPolynomial.eval₂_rename]
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hQ (Finset.univ : Finset F)
  have hcard : #{f ∈ Fintype.piFinset fun _ : Fin (Fintype.card X) => (Finset.univ : Finset F) |
      MvPolynomial.eval f Q = 0} = #{α : X → F | MvPolynomial.aeval α P = 0} := by
    refine Finset.card_bij' (fun f _ => f ∘ e) (fun α _ => α ∘ e.symm) ?_ ?_ ?_ ?_
    · intro f hf
      simpa [heval] using hf
    · intro α hα
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, implies_true, true_and]
      rw [heval]
      simpa [Function.comp_assoc] using hα
    · intro f _
      ext i
      simp
    · intro α _
      ext i
      simp
  rw [hcard] at hsz
  have hsz' : ((#{α : X → F | MvPolynomial.aeval α P = 0} : ℚ≥0) /
      ((#(Finset.univ : Finset F)) ^ Fintype.card X : ℚ≥0) : ℚ≥0) ≤
      (Q.totalDegree : ℚ≥0) / #(Finset.univ : Finset F) := hsz
  have hreal : ((#{α : X → F | MvPolynomial.aeval α P = 0} : ℝ) /
      ((Fintype.card F : ℝ) ^ Fintype.card X)) ≤ (Q.totalDegree : ℝ) / Fintype.card F := by
    have := (NNRat.cast_le (K := ℝ)).mpr hsz'
    simpa [Finset.card_univ] using this
  refine hreal.trans ?_
  have hpos : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right (by exact_mod_cast hdeg) hpos

omit [Fintype X] in
/-- A nonzero polynomial whose degree is less than the size of the field has a nonzero value. -/
theorem exists_aeval_ne_zero [Finite X] {P : MvPolynomial X k} (hP : P ≠ 0)
    (hF : P.totalDegree < Fintype.card F) : ∃ α : X → F, MvPolynomial.aeval α P ≠ 0 := by
  classical
  have := Fintype.ofFinite X
  by_contra hall
  push Not at hall
  have h := card_aeval_eq_zero_le (F := F) hP
  have hfull : #{α : X → F | MvPolynomial.aeval α P = 0} =
      Fintype.card F ^ Fintype.card X := by
    rw [Finset.filter_true_of_mem fun α _ => hall α, Finset.card_univ, Fintype.card_fun]
  have hposF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [hfull] at h
  push_cast at h
  rw [div_self (by positivity), le_div_iff₀ hposF, one_mul] at h
  exact absurd (by exact_mod_cast h) (not_le.mpr hF)

/-- A nonzero polynomial over a domain whose degree in each variable is less than the size of a
finite set `S` has a nonzero value at a point with coordinates in `S`, by the combinatorial
Nullstellensatz of Mathlib. -/
theorem exists_eval_ne_zero_of_degreeOf_lt_card {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R]
    {P : MvPolynomial σ R} (hP : P ≠ 0) (S : Finset R) (hS : ∀ i, P.degreeOf i < #S) :
    ∃ a : σ → R, (∀ i, a i ∈ S) ∧ MvPolynomial.eval a P ≠ 0 := by
  by_contra h
  push Not at h
  exact hP (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _ => S) hS h)

omit [Fintype X] in
/-- A nonzero polynomial whose degree in each variable is less than the size of the field has a
nonzero value, by the combinatorial Nullstellensatz of Mathlib. -/
theorem exists_aeval_ne_zero_of_degreeOf [Finite X] {P : MvPolynomial X k} (hP : P ≠ 0)
    (hd : ∀ i, P.degreeOf i < Fintype.card F) : ∃ α : X → F, MvPolynomial.aeval α P ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  let Q : MvPolynomial X F := MvPolynomial.map (algebraMap k F) P
  have hdeg : ∀ i, Q.degreeOf i < #(Finset.univ : Finset F) := by
    intro i
    rw [Finset.card_univ]
    refine lt_of_le_of_lt ?_ (hd i)
    refine MvPolynomial.degreeOf_le_iff.mpr fun m hm => ?_
    exact MvPolynomial.monomial_le_degreeOf i (MvPolynomial.support_map_subset _ _ hm)
  have hQ : Q = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun _ => Finset.univ) hdeg
      fun x _ => ?_
    have := hall x
    simpa [Q, MvPolynomial.eval_map, MvPolynomial.aeval_def] using this
  exact hP (MvPolynomial.map_injective _ (algebraMap k F).injective (by simpa [Q] using hQ))

omit [Fintype X] in
/-- **Lemma 1 of Lecture 16 of [elgamal2010], page 16-21.** A nonzero polynomial over `𝔽₂` has a
nonzero value in `𝔽_{2^m}`, for all large `m`. The proof in the notes is by induction on the number
of variables; here it follows from the Schwartz–Zippel lemma. -/
theorem exists_aeval_galoisField_ne_zero [Finite X] {P : MvPolynomial X (ZMod 2)} (hP : P ≠ 0) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ α : X → GaloisField 2 m, MvPolynomial.aeval α P ≠ 0 := by
  refine ⟨P.totalDegree + 1, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  refine exists_aeval_ne_zero hP ?_
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m hm0]
  calc P.totalDegree < P.totalDegree + 1 := Nat.lt_succ_self _
    _ ≤ m := hm
    _ < 2 ^ m := Nat.lt_two_pow_self

end InfoTheory
