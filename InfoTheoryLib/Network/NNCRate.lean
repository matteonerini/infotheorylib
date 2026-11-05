/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NNCCode

/-!
# Noisy network coding: the rates

The information across a cut in the noisy network coding bound.

## Main definitions

* `nncInfo L S d`: `I(X(S); Ŷ(Sᶜ), Y_d | X(Sᶜ)) - I(Y(S); Ŷ(S) | Xᴺ, Ŷ(Sᶜ), Y_d)`, in nats.

## Main statements

* `condEntropy_restr_le`: the conditional entropy of a tuple is at most the sum over its members.
* `nncInfo_le`: the information across a cut is at most the exponent of the test minus the rates of
  the compressions of the nodes of the cut.

## Implementation notes

The notes prove equality in `nncInfo_le`, on page 19-35. The inequality is enough, and it needs
no independence.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Sub

variable {Ω c : Type*} [Fintype Ω] [Fintype c] {N : ℕ} {β : Fin N → Type*} [∀ k, Fintype (β k)]

/-- **The conditional entropy of a tuple is at most the sum over its members.** -/
theorem condEntropy_restr_le {μ : Ω → ℝ} (hμ : IsPMF μ) (Z : Ω → ∀ k, β k) (C : Ω → c)
    (S : Finset (Fin N)) :
    H[fun ω => restr S (Z ω) | C ; μ] ≤ ∑ k ∈ S, H[fun ω => Z ω k | C ; μ] := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h₁ := condEntropy_le_entropy hμ (fun ω => restr ∅ (Z ω)) C
    have h₂ := entropyRV_le_log_card hμ (fun ω => restr ∅ (Z ω))
    have h₃ : Fintype.card (∀ k : (∅ : Finset (Fin N)), β k) = 1 := Fintype.card_unique
    rw [h₃] at h₂
    simp only [Nat.cast_one, log_one] at h₂
    simpa using h₁.trans h₂
  | insert k S hk ih =>
    rw [sum_insert hk]
    let g : (∀ j : (insert k S : Finset (Fin N)), β j) → β k × (∀ j : S, β j) := fun r =>
      (r ⟨k, mem_insert_self k S⟩, fun j => r ⟨j, mem_insert_of_mem j.2⟩)
    have hg : Function.Injective g := by
      intro r r' h
      funext j
      rcases mem_insert.mp j.2 with hj | hj
      · have e : j = ⟨k, mem_insert_self k S⟩ := Subtype.ext hj
        rw [e]
        exact (Prod.ext_iff.mp h).1
      · exact congrFun (Prod.ext_iff.mp h).2 ⟨j, hj⟩
    have h₁ : H[pair (fun ω => Z ω k) (fun ω => restr S (Z ω)) | C ; μ] =
        H[fun ω => restr (insert k S) (Z ω) | C ; μ] :=
      condEntropy_congr_left hμ C g hg fun _ => rfl
    rw [← h₁, chain_rule_cond hμ]
    have h₂ := condEntropy_le_condEntropy hμ (fun ω => restr S (Z ω)) (fun ω => Z ω k) C
    linarith

end Sub

/-! ### The information across a cut -/

section Info

variable {N : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)]

/-- **Theorem 3 of Lecture 19 of [elgamal2010], page 19-18.** The information across the cut `S` for
the destination `d`, `I(X(S); Ŷ(Sᶜ), Y_d | X(Sᶜ)) - I(Y(S); Ŷ(S) | Xᴺ, Ŷ(Sᶜ), Y_d)`, in nats. -/
def nncInfo (L : NNCΩ X Y V → ℝ) (S : Finset (Fin N)) (d : Fin N) : ℝ :=
  I[fun ω : NNCΩ X Y V => restr S ω.1 : fun ω => (restr Sᶜ ω.2.2, ω.2.1 d) |
    fun ω => restr Sᶜ ω.1 ; L] -
  I[fun ω : NNCΩ X Y V => restr S ω.2.1 : fun ω => restr S ω.2.2 |
    fun ω => ((ω.1, restr Sᶜ ω.2.2), ω.2.1 d) ; L]

variable {L : NNCΩ X Y V → ℝ}

/-- **Page 19-35 of [elgamal2010].** The information across a cut is at most the exponent of the
test minus the rates of the compressions of the nodes of the cut. -/
theorem nncInfo_le (hL : IsPMF L) (S : Finset (Fin N)) (d : Fin N) :
    nncInfo L S d ≤ nncJ L S d - ∑ k ∈ S, nncI L k := by
  classical
  let A : NNCΩ X Y V → ∀ k : S, X k := fun ω => restr S ω.1
  let B : NNCΩ X Y V → ∀ k : (Sᶜ : Finset (Fin N)), X k := fun ω => restr Sᶜ ω.1
  let Vc : NNCΩ X Y V → ∀ k : (Sᶜ : Finset (Fin N)), V k := fun ω => restr Sᶜ ω.2.2
  let Yd : NNCΩ X Y V → Y d := fun ω => ω.2.1 d
  let E : NNCΩ X Y V → ∀ k : S, V k := fun ω => restr S ω.2.2
  let F : NNCΩ X Y V → ∀ k : S, Y k := fun ω => restr S ω.2.1
  let G : NNCΩ X Y V → ((∀ k, X k) × ∀ k : (Sᶜ : Finset (Fin N)), V k) × Y d :=
    fun ω => ((ω.1, Vc ω), Yd ω)
  -- the terms of the informations
  have h₁ : I[A : pair Vc Yd | B ; L] = H[A | B ; L] - H[A | pair (pair Vc Yd) B ; L] := rfl
  have h₂ : I[F : E | G ; L] = H[E | G ; L] - H[E | pair G F ; L] := by
    rw [condMutualInfo_comm hL, condMutualInfo_eq' hL]
  have h₃ : nncInfo L S d = I[A : pair Vc Yd | B ; L] - I[F : E | G ; L] := rfl
  -- the term of the exponent
  have h₄ : H[nncF S | nncZ S d ; L] = H[A | pair (pair Vc Yd) B ; L] + H[E | G ; L] := by
    have e₁ : H[nncF S | nncZ S d ; L] = H[A | nncZ S d ; L] + H[E | pair A (nncZ S d) ; L] :=
      chain_rule_cond hL A E (nncZ S d)
    have e₂ : H[A | pair (pair Vc Yd) B ; L] = H[A | nncZ S d ; L] := by
      refine condEntropy_congr_right hL A
        (fun z : ((∀ k : (Sᶜ : Finset (Fin N)), X k) × ∀ k : (Sᶜ : Finset (Fin N)), V k) × Y d =>
          ((z.1.2, z.2), z.1.1)) (fun a b h => ?_) fun _ => rfl
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.2 h.1.1) h.1.2
    have e₃ : H[E | pair A (nncZ S d) ; L] = H[E | G ; L] := by
      refine (condEntropy_congr_right hL E
        (fun z : ((∀ k, X k) × ∀ k : (Sᶜ : Finset (Fin N)), V k) × Y d =>
          ((restr S z.1.1 : ∀ k : S, X k), ((restr Sᶜ z.1.1, z.1.2), z.2)))
        (fun a b h => ?_) fun _ => rfl)
      simp only [Prod.mk.injEq] at h
      have hx := restr_compl_restr_injective S (Prod.ext h.2.1.1 h.1)
      exact Prod.ext (Prod.ext hx h.2.1.2) h.2.2
    rw [e₁, e₂, e₃]
  -- the two inequalities
  have h₅ : H[A | B ; L] ≤ ∑ k ∈ S, H[fun ω : NNCΩ X Y V => ω.1 k ; L] := by
    have e₁ := condEntropy_le_entropy hL A B
    have e₂ := condEntropy_restr_le hL (fun ω : NNCΩ X Y V => ω.1) (fun _ => ()) S
    have e₃ : H[A ; L] = H[A | (fun _ => ()) ; L] := (condEntropy_const hL A ()).symm
    have e₄ : ∀ k, H[fun ω : NNCΩ X Y V => ω.1 k | (fun _ => ()) ; L] =
        H[fun ω : NNCΩ X Y V => ω.1 k ; L] := fun k => condEntropy_const hL _ ()
    simp_rw [e₄] at e₂
    rw [e₃] at e₁
    exact e₁.trans e₂
  have h₆ : H[E | pair G F ; L] ≤ ∑ k ∈ S, H[Prod.snd | Prod.fst ; nncRho3 L k] := by
    refine (condEntropy_restr_le hL (fun ω : NNCΩ X Y V => ω.2.2) (pair G F) S).trans
      (sum_le_sum fun k hk => ?_)
    have e₁ : H[Prod.snd | Prod.fst ; nncRho3 L k] =
        H[fun ω : NNCΩ X Y V => ω.2.2 k | fun ω => (ω.1 k, ω.2.1 k) ; L] := by
      refine condEntropy_eq_of_dist_pair_eq (hL.dist _) hL ?_
      rw [pair_fst_snd, dist_id]
      rfl
    rw [e₁]
    exact condEntropy_le_condEntropy_comp hL (fun ω : NNCΩ X Y V => ω.2.2 k) (pair G F)
      fun t => (t.1.1.1 k, t.2 ⟨k, hk⟩)
  have h₇ : nncJ L S d - ∑ k ∈ S, nncI L k = ∑ k ∈ S, H[fun ω : NNCΩ X Y V => ω.1 k ; L] +
      ∑ k ∈ S, H[Prod.snd | Prod.fst ; nncRho3 L k] - H[nncF S | nncZ S d ; L] := by
    simp only [nncJ, nncHk, nncI, sum_add_distrib, sum_sub_distrib]
    ring
  rw [h₃, h₁, h₂, h₇, h₄]
  linarith

end Info

end InfoTheory
