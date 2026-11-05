/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayBlock

/-!
# The relay channel: the error exponents of the code of one block

The codewords of the block code are i.i.d. Each term of the random coding bound of
`Network.RelayBlock` is then bounded by a typical set argument.

## Main definitions

* `relayLaw τ A B W`: the law of `(X₁, U, X, Y, Y₁)`.
* `relaySeq W n`: `n` uses of the relay channel.
* `relayT₁`, `relayT₂`: the typicality tests of the relay and of the receiver.

## Main statements

* `sum_relay_all`: the sum over all the sequences of a block is an i.i.d. expectation.
* `relayF₀_le`, `relayFa_le`, `relayFc_le`, `relayFl_le`: the terms of the random coding bound.
* `eventually_relayBlock`: **codes for one block**, for rates below the three gaps.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X₁ U X Y Y₁ : Type*} [Fintype X₁] [Fintype U] [Fintype X] [Fintype Y] [Fintype Y₁]

/-- The law of `((X₁, U), X), (Y, Y₁))`: `p(x₁) p(u | x₁) p(x | x₁, u) p(y, y₁ | x, x₁)`. -/
def relayLaw (τ : X₁ → ℝ) (A : X₁ → U → ℝ) (B : X₁ × U → X → ℝ) (W : X × X₁ → Y × Y₁ → ℝ) :
    ((X₁ × U) × X) × (Y × Y₁) → ℝ :=
  jointOf (jointOf (jointOf τ A) B) fun t => W (t.2, t.1.1)

/-- `n` uses of the relay channel. -/
def relaySeq (W : X × X₁ → Y × Y₁ → ℝ) (n : ℕ) :
    (Fin n → X) × (Fin n → X₁) → (Fin n → Y) × (Fin n → Y₁) → ℝ :=
  fun a z => ∏ i, W (a.1 i, a.2 i) (z.1 i, z.2 i)

variable {τ : X₁ → ℝ} {A : X₁ → U → ℝ} {B : X₁ × U → X → ℝ} {W : X × X₁ → Y × Y₁ → ℝ} {n : ℕ}

omit [Fintype X₁] [Fintype U] [Fintype X] in
lemma relaySeq_isChannel (hW : IsChannel W) (n : ℕ) : IsChannel (relaySeq W n) := by
  classical
  intro a
  refine ⟨fun z => prod_nonneg fun i _ => (hW _).nonneg _, ?_⟩
  simp only [relaySeq]
  rw [Fintype.sum_prod_type]
  have h := sum_zip (F := fun o : Fin n → Y × Y₁ => ∏ i, W (a.1 i, a.2 i) (o i))
  refine h.symm.trans ?_
  rw [← Fintype.piFinset_univ, ← prod_univ_sum]
  exact prod_eq_one fun i _ => (hW _).sum_eq_one

lemma relayLaw_isPMF (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    IsPMF (relayLaw τ A B W) :=
  jointOf_isPMF (jointOf_isPMF (jointOf_isPMF hτ hA) hB) fun _ => hW _

/-- A sum over sequences of tuples is a sum over the sequences of the components. -/
lemma sum_relay_split (F : (Fin n → ((X₁ × U) × X) × (Y × Y₁)) → ℝ) :
    ∑ ζ, F ζ = ∑ s : Fin n → X₁, ∑ u : Fin n → U, ∑ x : Fin n → X,
      ∑ z : (Fin n → Y) × (Fin n → Y₁), F fun i => (((s i, u i), x i), (z.1 i, z.2 i)) := by
  calc ∑ ζ, F ζ = ∑ t, ∑ o, F (zipSeq t o) := sum_zip F
    _ = ∑ tt, ∑ x, ∑ o, F (zipSeq (zipSeq tt x) o) := sum_zip fun t => ∑ o, F (zipSeq t o)
    _ = ∑ s, ∑ u, ∑ x, ∑ o, F (zipSeq (zipSeq (zipSeq s u) x) o) :=
        sum_zip fun tt => ∑ x, ∑ o, F (zipSeq (zipSeq tt x) o)
    _ = _ := by
        refine sum_congr rfl fun s _ => sum_congr rfl fun u _ => sum_congr rfl fun x _ => ?_
        rw [sum_zip, Fintype.sum_prod_type]
        rfl

/-- **The sum over all the sequences of a block is an i.i.d. expectation.** -/
theorem sum_relay_all (G : (Fin n → X₁) → (Fin n → U) → (Fin n → X) →
    (Fin n → Y) × (Fin n → Y₁) → ℝ) :
    ∑ s, iidPMF τ n s * ∑ u, seqChan A n s u * ∑ x, seqChan B n (zipSeq s u) x *
      ∑ z, relaySeq W n (x, s) z * G s u x z =
    ∑ ζ, iidPMF (relayLaw τ A B W) n ζ * G (fun i => (ζ i).1.1.1) (fun i => (ζ i).1.1.2)
      (fun i => (ζ i).1.2) (fun i => (ζ i).2.1, fun i => (ζ i).2.2) := by
  rw [sum_relay_split]
  simp only [mul_sum]
  refine sum_congr rfl fun s _ => sum_congr rfl fun u _ => sum_congr rfl fun x _ =>
    sum_congr rfl fun z _ => ?_
  have h : iidPMF (relayLaw τ A B W) n (fun i => (((s i, u i), x i), (z.1 i, z.2 i))) =
      iidPMF τ n s * (seqChan A n s u * (seqChan B n (zipSeq s u) x * relaySeq W n (x, s) z)) := by
    simp only [iidPMF, seqChan, relaySeq, relayLaw, jointOf, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by simp [zipSeq]; ring
  rw [h]
  ring

/-! ### The tests -/

/-- The variables of the test of the relay, in the form of `sum_fresh_le`. -/
def relayR₁ (z : ((X₁ × U) × X) × (Y × Y₁)) : (X₁ × Y₁) × U := ((z.1.1.1, z.2.2), z.1.1.2)

/-- The variables of the test of the receiver. -/
def relayR₂ (z : ((X₁ × U) × X) × (Y × Y₁)) : ((X₁ × U) × X) × Y := (z.1, z.2.1)

/-- The test of the relay. -/
def relayT₁ (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) (n : ℕ) (ε : ℝ) (s : Fin n → X₁) (u : Fin n → U)
    (y₁ : Fin n → Y₁) : Prop :=
  (fun i => ((s i, y₁ i), u i)) ∈ robustTypicalSet (dist L relayR₁) n ε

/-- The test of the receiver. -/
def relayT₂ (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) (n : ℕ) (ε : ℝ) (s : Fin n → X₁) (u : Fin n → U)
    (x : Fin n → X) (y : Fin n → Y) : Prop :=
  (fun i => (((s i, u i), x i), y i)) ∈ robustTypicalSet (dist L relayR₂) n ε

/-! ### The terms of the bound -/

/-- Exchanging two sums, with weights. -/
lemma sum_inner_swap {I J : Type*} [Fintype I] [Fintype J] (a : I → ℝ) (b : J → ℝ)
    (f : I → J → ℝ) : ∑ i, a i * ∑ j, b j * f i j = ∑ j, b j * ∑ i, a i * f i j := by
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

/-- The entropy of a function under a pushforward. -/
lemma entropyRV_dist {Ω a b : Type*} [Fintype Ω] [Fintype a] [Fintype b] (L : Ω → ℝ) (R : Ω → a)
    (f : a → b) : H[f ; dist L R] = H[f ∘ R ; L] := by
  rw [entropyRV, entropyRV, dist_comp_eq]

/-- The gap of a wrong `a'`: `I(U; Y₁ | X₁)`. -/
def rGapA (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) : ℝ :=
  H[fun z => (z.1.1.1, z.2.2) ; L] + H[fun z => z.1.1 ; L] - H[fun z => z.1.1.1 ; L] -
    H[relayR₁ ; L]

/-- The correction to the gap of a wrong `a'`. -/
def rErrA (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) : ℝ :=
  H[relayR₁ ; L] + H[fun z => (z.1.1.1, z.2.2) ; L] + H[fun z => z.1.1 ; L] +
    H[fun z => z.1.1.1 ; L]

/-- The variables for a wrong `c'`. -/
def relayRc (z : ((X₁ × U) × X) × (Y × Y₁)) : ((X₁ × U) × Y) × X := ((z.1.1, z.2.1), z.1.2)

/-- The gap of a wrong `c'`: `I(X; Y | X₁, U)`. -/
def rGapC (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) : ℝ :=
  H[fun z => (z.1.1, z.2.1) ; L] + H[Prod.fst ; L] - H[fun z => z.1.1 ; L] - H[relayRc ; L]

/-- The correction to the gap of a wrong `c'`. -/
def rErrC (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) : ℝ :=
  H[relayRc ; L] + H[fun z => (z.1.1, z.2.1) ; L] + H[Prod.fst ; L] + H[fun z => z.1.1 ; L]

/-- The variables for a wrong `l'`. -/
def relayRl (z : ((X₁ × U) × X) × (Y × Y₁)) : Y × ((X₁ × U) × X) := (z.2.1, z.1)

/-- The gap of a wrong `l'`: `I(X₁, U, X; Y)`. -/
def rGapL (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) : ℝ :=
  H[fun z => z.2.1 ; L] + H[Prod.fst ; L] - H[relayRl ; L]

/-- The correction to the gap of a wrong `l'`. -/
def rErrL (L : ((X₁ × U) × X) × (Y × Y₁) → ℝ) : ℝ :=
  H[relayRl ; L] + H[fun z => z.2.1 ; L] + H[Prod.fst ; L]

section Terms

variable (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) {ε : ℝ}
include hτ hA hB hW

/-- The sequences of the block are typical, except with a small probability. -/
theorem relayF₀_le :
    relayF₀ (iidPMF τ n) (seqChan A n) (fun p => seqChan B n (zipSeq p.1 p.2))
        (fun a => relaySeq W n (a.1, a.2))
        (relayT₁ (relayLaw τ A B W) n ε) (relayT₂ (relayLaw τ A B W) n ε) ≤
      1 - prob (iidPMF (relayLaw τ A B W) n) (robustTypicalSet (relayLaw τ A B W) n ε) := by
  classical
  have hL := relayLaw_isPMF hτ hA hB hW
  set L := relayLaw τ A B W with hLd
  have hsum := sum_relay_all (τ := τ) (A := A) (B := B) (W := W) (n := n)
    fun s u x z => ind (¬ relayT₁ L n ε s u z.2 ∨ ¬ relayT₂ L n ε s u x z.1)
  refine (le_of_eq hsum).trans ?_
  rw [← prob_compl (iidPMF_isPMF hL n), prob]
  rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ robustTypicalSet L n ε)]
  have h₁ : ∑ ζ ∈ univ.filter (· ∈ robustTypicalSet L n ε), iidPMF L n ζ *
      ind (¬ relayT₁ L n ε (fun i => (ζ i).1.1.1) (fun i => (ζ i).1.1.2) (fun i => (ζ i).2.2) ∨
        ¬ relayT₂ L n ε (fun i => (ζ i).1.1.1) (fun i => (ζ i).1.1.2) (fun i => (ζ i).1.2)
          (fun i => (ζ i).2.1)) = 0 := by
    refine sum_eq_zero fun ζ hζ => ?_
    have hζ' := (mem_filter.mp hζ).2
    have ht₁ : relayT₁ L n ε (fun i => (ζ i).1.1.1) (fun i => (ζ i).1.1.2) (fun i => (ζ i).2.2) :=
      comp_mem_robustTypicalSet hζ' relayR₁
    have ht₂ : relayT₂ L n ε (fun i => (ζ i).1.1.1) (fun i => (ζ i).1.1.2) (fun i => (ζ i).1.2)
        (fun i => (ζ i).2.1) := comp_mem_robustTypicalSet hζ' relayR₂
    rw [ind_of_neg (by tauto), mul_zero]
  rw [h₁, zero_add]
  have hset : univ.filter (· ∉ robustTypicalSet L n ε) = (robustTypicalSet L n ε)ᶜ := by
    ext ζ
    simp
  rw [hset]
  refine sum_le_sum fun ζ _ => ?_
  have := mul_le_mul_of_nonneg_left (ind_le_one (¬ relayT₁ L n ε (fun i => (ζ i).1.1.1)
    (fun i => (ζ i).1.1.2) (fun i => (ζ i).2.2) ∨ ¬ relayT₂ L n ε (fun i => (ζ i).1.1.1)
      (fun i => (ζ i).1.1.2) (fun i => (ζ i).1.2) (fun i => (ζ i).2.1)))
    ((iidPMF_isPMF hL n).nonneg ζ)
  simpa using this

omit hτ in
/-- The marginals of the law. -/
lemma relayLaw_marg :
    dist (relayLaw τ A B W) Prod.fst = jointOf (jointOf τ A) B ∧
    dist (relayLaw τ A B W) (fun z => z.1.1) = jointOf τ A ∧
    dist (relayLaw τ A B W) (fun z => z.1.1.1) = τ := by
  have h₁ : dist (relayLaw τ A B W) Prod.fst = jointOf (jointOf τ A) B :=
    dist_jointOf_fst fun _ => hW _
  have h₂ : dist (relayLaw τ A B W) (fun z => z.1.1) = jointOf τ A := by
    have e : (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1) = Prod.fst ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, h₁]
    exact dist_jointOf_fst hB
  refine ⟨h₁, h₂, ?_⟩
  have e : (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1.1) = Prod.fst ∘ fun z => z.1.1 := rfl
  rw [e, dist_comp_eq, h₂]
  exact dist_jointOf_fst hA

/-- A wrong `a'` passes the test of the relay with a small probability. -/
theorem relayFa_le :
    relayFa (iidPMF τ n) (seqChan A n) (fun p => seqChan B n (zipSeq p.1 p.2))
        (fun a => relaySeq W n (a.1, a.2)) (relayT₁ (relayLaw τ A B W) n ε) ≤
      exp (-(n * (rGapA (relayLaw τ A B W) - ε * rErrA (relayLaw τ A B W)))) := by
  classical
  have hL := relayLaw_isPMF hτ hA hB hW
  obtain ⟨-, hd₂, hd₃⟩ := relayLaw_marg hA hB hW
  set L := relayLaw τ A B W with hLd
  let Rv : ((X₁ × U) × X) × (Y × Y₁) → X₁ × Y₁ := fun z => (z.1.1.1, z.2.2)
  let Ψ : (Fin n → X₁ × Y₁) → ℝ := fun r => ∑ t, seqChan A n (fun i => (r i).1) t *
    ind (relayT₁ L n ε (fun i => (r i).1) t fun i => (r i).2)
  have hrearr : relayFa (iidPMF τ n) (seqChan A n) (fun p => seqChan B n (zipSeq p.1 p.2))
      (fun a => relaySeq W n (a.1, a.2)) (relayT₁ L n ε) =
      ∑ s, iidPMF τ n s * ∑ u, seqChan A n s u * ∑ x, seqChan B n (zipSeq s u) x *
        ∑ z, relaySeq W n (x, s) z * ∑ t, seqChan A n s t * ind (relayT₁ L n ε s t z.2) := by
    simp only [relayFa]
    refine sum_congr rfl fun s _ => congrArg _ <| sum_congr rfl fun u _ => congrArg _ ?_
    rw [sum_inner_swap]
    refine sum_congr rfl fun x _ => congrArg _ ?_
    exact sum_inner_swap _ _ _
  rw [hrearr, sum_relay_all (τ := τ) (A := A) (B := B) (W := W) (n := n)
    fun s _ _ z => ∑ t, seqChan A n s t * ind (relayT₁ L n ε s t z.2)]
  have hcomp := sum_iid_comp L n Rv Ψ
  refine (le_of_eq hcomp).trans ?_
  have hfresh := sum_fresh_le (L := dist L relayR₁) (hL.dist _) (Prod.fst : X₁ × Y₁ → X₁) (κ := A)
    (fun k t => by
      have e₁ : dist (dist L relayR₁) (fun z => (z.1.1, z.2)) = jointOf τ A := by
        rw [← dist_comp_eq]
        exact hd₂
      have e₂ : dist (dist L relayR₁) (fun z => z.1.1) = τ := by
        rw [← dist_comp_eq]
        exact hd₃
      rw [e₁, e₂]
      rfl) hA (n := n) (ε := ε)
    (fun r t => relayT₁ L n ε (fun i => (r i).1) t fun i => (r i).2) (fun r t h => h)
  have e₀ : dist (dist L relayR₁) Prod.fst = dist L Rv := by
    rw [← dist_comp_eq]
    rfl
  rw [e₀] at hfresh
  refine hfresh.trans (le_of_eq ?_)
  simp only [entropyRV_dist]
  rfl

/-- A wrong `c'` passes the test of the receiver with a small probability. -/
theorem relayFc_le :
    relayFc (iidPMF τ n) (seqChan A n) (fun p => seqChan B n (zipSeq p.1 p.2))
        (fun a => relaySeq W n (a.1, a.2)) (relayT₂ (relayLaw τ A B W) n ε) ≤
      exp (-(n * (rGapC (relayLaw τ A B W) - ε * rErrC (relayLaw τ A B W)))) := by
  classical
  have hL := relayLaw_isPMF hτ hA hB hW
  obtain ⟨hd₁, hd₂, -⟩ := relayLaw_marg hA hB hW
  set L := relayLaw τ A B W with hLd
  let Rv : ((X₁ × U) × X) × (Y × Y₁) → (X₁ × U) × Y := fun z => (z.1.1, z.2.1)
  let Ψ : (Fin n → (X₁ × U) × Y) → ℝ := fun r => ∑ t, seqChan B n (fun i => (r i).1) t *
    ind (relayT₂ L n ε (fun i => (r i).1.1) (fun i => (r i).1.2) t fun i => (r i).2)
  have hrearr : relayFc (iidPMF τ n) (seqChan A n) (fun p => seqChan B n (zipSeq p.1 p.2))
      (fun a => relaySeq W n (a.1, a.2)) (relayT₂ L n ε) =
      ∑ s, iidPMF τ n s * ∑ u, seqChan A n s u * ∑ x, seqChan B n (zipSeq s u) x *
        ∑ z, relaySeq W n (x, s) z * ∑ t, seqChan B n (zipSeq s u) t *
          ind (relayT₂ L n ε s u t z.1) := by
    simp only [relayFc]
    refine sum_congr rfl fun s _ => congrArg _ <| sum_congr rfl fun u _ => congrArg _ <|
      sum_congr rfl fun x _ => congrArg _ ?_
    exact sum_inner_swap _ _ _
  rw [hrearr, sum_relay_all (τ := τ) (A := A) (B := B) (W := W) (n := n)
    fun s u _ z => ∑ t, seqChan B n (zipSeq s u) t * ind (relayT₂ L n ε s u t z.1)]
  have hcomp := sum_iid_comp L n Rv Ψ
  refine (le_of_eq hcomp).trans ?_
  have hfresh := sum_fresh_le (L := dist L relayRc) (hL.dist _) (Prod.fst : (X₁ × U) × Y → X₁ × U)
    (κ := B)
    (fun k t => by
      have e₁ : dist (dist L relayRc) (fun z => (z.1.1, z.2)) = jointOf (jointOf τ A) B := by
        rw [← dist_comp_eq]
        exact hd₁
      have e₂ : dist (dist L relayRc) (fun z => z.1.1) = jointOf τ A := by
        rw [← dist_comp_eq]
        exact hd₂
      rw [e₁, e₂]
      rfl) hB (n := n) (ε := ε)
    (fun r t => relayT₂ L n ε (fun i => (r i).1.1) (fun i => (r i).1.2) t fun i => (r i).2)
    (fun r t h => by
      have := comp_mem_robustTypicalSet h
        (fun p : ((X₁ × U) × X) × Y => ((p.1.1, p.2), p.1.2))
      rw [← dist_comp_eq] at this
      exact this)
  have e₀ : dist (dist L relayRc) Prod.fst = dist L Rv := by
    rw [← dist_comp_eq]
    rfl
  rw [e₀] at hfresh
  refine hfresh.trans (le_of_eq ?_)
  simp only [entropyRV_dist]
  rfl

/-- A wrong `l'`, with any `c'`, passes the test of the receiver with a small probability. -/
theorem relayFl_le :
    relayFl (iidPMF τ n) (seqChan A n) (fun p => seqChan B n (zipSeq p.1 p.2))
        (fun a => relaySeq W n (a.1, a.2)) (relayT₂ (relayLaw τ A B W) n ε) ≤
      exp (-(n * (rGapL (relayLaw τ A B W) - ε * rErrL (relayLaw τ A B W)))) := by
  classical
  have hL := relayLaw_isPMF hτ hA hB hW
  obtain ⟨hd₁, -, -⟩ := relayLaw_marg (τ := τ) hA hB hW
  set L := relayLaw τ A B W with hLd
  let q := jointOf (jointOf τ A) B
  have hq : IsPMF q := jointOf_isPMF (jointOf_isPMF hτ hA) hB
  let Ψ : (Fin n → Y) → ℝ := fun y => ∑ t, iidPMF q n t *
    ind (relayT₂ L n ε (fun i => (t i).1.1) (fun i => (t i).1.2) (fun i => (t i).2) y)
  have hΨ : ∀ y, ∑ s', iidPMF τ n s' * ∑ u', seqChan A n s' u' *
      ∑ x', seqChan B n (zipSeq s' u') x' * ind (relayT₂ L n ε s' u' x' y) = Ψ y := by
    intro y
    simp only [Ψ]
    rw [sum_zip, sum_zip (F := fun tt => ∑ x, iidPMF q n (zipSeq tt x) * _)]
    simp only [mul_sum]
    refine sum_congr rfl fun s' _ => sum_congr rfl fun u' _ => sum_congr rfl fun x' _ => ?_
    have h : iidPMF q n (zipSeq (zipSeq s' u') x') =
        iidPMF τ n s' * (seqChan A n s' u' * seqChan B n (zipSeq s' u') x') := by
      simp only [iidPMF, seqChan, q, jointOf, ← prod_mul_distrib]
      exact prod_congr rfl fun i _ => by simp [zipSeq]; ring
    rw [h]
    simp only [zipSeq]
    ring
  have hrearr : relayFl (iidPMF τ n) (seqChan A n) (fun p => seqChan B n (zipSeq p.1 p.2))
      (fun a => relaySeq W n (a.1, a.2)) (relayT₂ L n ε) =
      ∑ s, iidPMF τ n s * ∑ u, seqChan A n s u * ∑ x, seqChan B n (zipSeq s u) x *
        ∑ z, relaySeq W n (x, s) z * Ψ z.1 := by
    simp only [relayFl, ← hΨ]
    refine sum_congr rfl fun s _ => congrArg _ ?_
    rw [sum_inner_swap]
    refine sum_congr rfl fun u _ => congrArg _ ?_
    have hin : ∀ s' : Fin n → X₁, ∑ u', seqChan A n s' u' * ∑ x, seqChan B n (zipSeq s u) x *
        ∑ x', seqChan B n (zipSeq s' u') x' * ∑ z, relaySeq W n (x, s) z *
          ind (relayT₂ L n ε s' u' x' z.1) =
        ∑ x, seqChan B n (zipSeq s u) x * ∑ z, relaySeq W n (x, s) z *
          ∑ u', seqChan A n s' u' * ∑ x', seqChan B n (zipSeq s' u') x' *
            ind (relayT₂ L n ε s' u' x' z.1) := by
      intro s'
      rw [sum_inner_swap]
      refine sum_congr rfl fun x _ => congrArg _ ?_
      have hin₂ : ∀ u' : Fin n → U, ∑ x', seqChan B n (zipSeq s' u') x' *
          ∑ z, relaySeq W n (x, s) z * ind (relayT₂ L n ε s' u' x' z.1) =
          ∑ z, relaySeq W n (x, s) z * ∑ x', seqChan B n (zipSeq s' u') x' *
            ind (relayT₂ L n ε s' u' x' z.1) := fun u' => sum_inner_swap _ _ _
      simp_rw [hin₂]
      exact sum_inner_swap _ _ _
    simp_rw [hin]
    rw [sum_inner_swap]
    refine sum_congr rfl fun x _ => congrArg _ ?_
    exact sum_inner_swap _ _ _
  rw [hrearr, sum_relay_all (τ := τ) (A := A) (B := B) (W := W) (n := n) fun _ _ _ z => Ψ z.1]
  have hcomp := sum_iid_comp L n (fun z => z.2.1) Ψ
  refine (le_of_eq hcomp).trans ?_
  have hfresh := sum_fresh_le (L := dist L relayRl) (hL.dist _) (fun _ : Y => ())
    (κ := fun _ : Unit => q)
    (fun k t => by
      have e₂ : dist (dist L relayRl) (fun z => ()) = fun _ => 1 := by
        funext k
        have hc := dist_const (hL.dist relayRl) ()
        rw [hc]
        simp
      have e₁ : dist (dist L relayRl) (fun z => ((), z.2)) (k, t) = q t := by
        have := dist_comp_of_injective (dist L relayRl) (fun z => z.2)
          (f := fun t => ((), t)) (fun a b h => (Prod.mk.inj h).2) t
        have e₃ : dist (dist L relayRl) (fun z => z.2) = q := by
          rw [← dist_comp_eq]
          exact hd₁
        rw [e₃] at this
        exact this
      rw [e₁, e₂, one_mul]) (fun _ => hq) (n := n) (ε := ε)
    (fun r t => relayT₂ L n ε (fun i => (t i).1.1) (fun i => (t i).1.2) (fun i => (t i).2) r)
    (fun r t h => by
      have := comp_mem_robustTypicalSet h (fun p : ((X₁ × U) × X) × Y => (p.2, p.1))
      rw [← dist_comp_eq] at this
      exact this)
  have e₀ : dist (dist L relayRl) Prod.fst = dist L fun z => z.2.1 := by
    rw [← dist_comp_eq]
    rfl
  rw [e₀] at hfresh
  refine hfresh.trans (le_of_eq ?_)
  have hunit : H[fun z : Y × ((X₁ × U) × X) => ((), z.2) ; dist L relayRl] =
      H[Prod.fst ; L] := by
    rw [entropyRV_eq_of_injective (dist L relayRl) (X := Prod.snd)
      (fun t => ((), t)) (fun a b h => (Prod.mk.inj h).2) fun _ => rfl,
      entropyRV_dist]
    rfl
  have hzero : H[fun _ : Y × ((X₁ × U) × X) => () ; dist L relayRl] = 0 :=
    entropyRV_const (hL.dist _) _
  have hfst : H[Prod.fst ; dist L relayRl] = H[fun z => z.2.1 ; L] := entropyRV_dist _ _ _
  rw [hunit, hzero, hfst]
  simp only [rGapL, rErrL]
  congr 2
  have : entropy (dist L relayRl) = H[relayRl ; L] := rfl
  rw [this]
  ring

end Terms

/-! ### Codes for one block -/

instance neZero_ceil_exp (x : ℝ) : NeZero ⌈exp x⌉₊ := ⟨(Nat.ceil_pos.mpr (exp_pos x)).ne'⟩

/-- **Codes for one block.** For rates in nats below the three gaps, and for all large `n`, there is
a code for one block with `⌈exp (n R')⌉` values of `l` and `a` and `⌈exp (n R'')⌉` values of `c`
whose error is arbitrarily small. -/
theorem eventually_relayBlock (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B)
    (hW : IsChannel W) {R' R'' : ℝ} (hR' : 0 ≤ R') (hR'' : 0 ≤ R'')
    (ha : R' = 0 ∨ R' < rGapA (relayLaw τ A B W)) (hc : R'' = 0 ∨ R'' < rGapC (relayLaw τ A B W))
    (hl : R' + R'' < rGapL (relayLaw τ A B W)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ C : RelayBlock ⌈exp (n * R')⌉₊ ⌈exp (n * R'')⌉₊ (Fin n → X₁) (Fin n → X)
      (Fin n → Y) (Fin n → Y₁), C.avgErr (relaySeq W n) ≤ δ := by
  classical
  have hL := relayLaw_isPMF hτ hA hB hW
  set L := relayLaw τ A B W with hLd
  classical
  set γ := min (min (if R' = 0 then 1 else rGapA L - R') (if R'' = 0 then 1 else rGapC L - R''))
    (rGapL L - (R' + R'')) with hγ
  have hγpos : 0 < γ := by
    refine lt_min (lt_min ?_ ?_) (by linarith)
    · split_ifs with h
      · norm_num
      · have := ha.resolve_left h
        linarith
    · split_ifs with h
      · norm_num
      · have := hc.resolve_left h
        linarith
  have hEa : 0 ≤ rErrA L := by
    simp only [rErrA]
    have := entropyRV_nonneg hL (relayR₁ : _ → (X₁ × Y₁) × U)
    have := entropyRV_nonneg hL (fun z : ((X₁ × U) × X) × (Y × Y₁) => (z.1.1.1, z.2.2))
    have := entropyRV_nonneg hL (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1)
    have := entropyRV_nonneg hL (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1.1)
    linarith
  have hEc : 0 ≤ rErrC L := by
    simp only [rErrC]
    have := entropyRV_nonneg hL (relayRc : _ → ((X₁ × U) × Y) × X)
    have := entropyRV_nonneg hL (fun z : ((X₁ × U) × X) × (Y × Y₁) => (z.1.1, z.2.1))
    have := entropyRV_nonneg hL (Prod.fst : ((X₁ × U) × X) × (Y × Y₁) → _)
    have := entropyRV_nonneg hL (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1)
    linarith
  have hEl : 0 ≤ rErrL L := by
    simp only [rErrL]
    have := entropyRV_nonneg hL (relayRl : _ → Y × ((X₁ × U) × X))
    have := entropyRV_nonneg hL (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.2.1)
    have := entropyRV_nonneg hL (Prod.fst : ((X₁ × U) × X) × (Y × Y₁) → _)
    linarith
  -- a small `ε`
  set E := rErrA L + rErrC L + rErrL L + 1 with hE
  have hEpos : 0 < E := by linarith
  set ε := γ / (2 * E) with hε
  have hεpos : 0 < ε := by positivity
  have hεE : ε * E = γ / 2 := by
    rw [hε]
    field_simp
  have hea : ε * rErrA L ≤ γ / 2 := by
    rw [← hεE]
    exact mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have hec : ε * rErrC L ≤ γ / 2 := by
    rw [← hεE]
    exact mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have hel : ε * rErrL L ≤ γ / 2 := by
    rw [← hεE]
    exact mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have hγa : R' ≠ 0 → γ ≤ rGapA L - R' := fun h => by
    have := (min_le_left _ _).trans (min_le_left _ _) (a := γ) |>.trans_eq (ite_eq_right h)
    exact this
  have hγc : R'' ≠ 0 → γ ≤ rGapC L - R'' := fun h => by
    have := (min_le_left _ _).trans (min_le_right _ _) (a := γ) |>.trans_eq (ite_eq_right h)
    exact this
  have hγl : γ ≤ rGapL L - (R' + R'') := min_le_right _ _
  -- the limit of the bound
  have hprob := tendsto_prob_robustTypicalSet hL hεpos
  have hexp : Tendsto (fun n : ℕ => exp (-(n * (γ / 2)))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_nat (by positivity)
  have hlim : Tendsto (fun n : ℕ => 3 * (2 * (1 - prob (iidPMF L n) (robustTypicalSet L n ε)) +
      8 * exp (-(n * (γ / 2))))) atTop (𝓝 (3 * (2 * (1 - 1) + 8 * 0))) :=
    ((tendsto_const_nhds.sub hprob).const_mul _ |>.add (hexp.const_mul _)).const_mul _
  have hlim' : ∀ᶠ n : ℕ in atTop, 3 * (2 * (1 - prob (iidPMF L n) (robustTypicalSet L n ε)) +
      8 * exp (-(n * (γ / 2)))) < δ := by
    refine (tendsto_order.mp hlim).2 δ ?_
    simpa using hδ
  filter_upwards [hlim'] with n hn
  obtain ⟨C, hC⟩ := exists_relayBlock_le (Ma := ⌈exp (n * R')⌉₊) (Mc := ⌈exp (n * R'')⌉₊)
    (τ := iidPMF τ n) (A := seqChan A n) (B := fun p => seqChan B n (zipSeq p.1 p.2))
    (V := relaySeq W n) (T₁ := relayT₁ L n ε) (T₂ := relayT₂ L n ε)
    (iidPMF_isPMF hτ n) (seqChan_isChannel hA n) (fun p => seqChan_isChannel hB n _)
    (relaySeq_isChannel hW n)
  refine ⟨C, hC.trans (le_of_lt (lt_of_le_of_lt ?_ hn))⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hceil : ∀ r : ℝ, 0 ≤ r → ((⌈exp (n * r)⌉₊ : ℕ) : ℝ) ≤ 2 * exp (n * r) := by
    intro r hr
    have h₁ := Nat.ceil_lt_add_one (exp_pos (n * r)).le
    have h₂ : 1 ≤ exp (n * r) := one_le_exp (mul_nonneg hn0 hr)
    linarith
  have hF₀ := relayF₀_le (ε := ε) (n := n) hτ hA hB hW
  have hFa := relayFa_le (ε := ε) (n := n) hτ hA hB hW
  have hFc := relayFc_le (ε := ε) (n := n) hτ hA hB hW
  have hFl := relayFl_le (ε := ε) (n := n) hτ hA hB hW
  have hFa0 := relayFa_nonneg (T₁ := relayT₁ L n ε) (iidPMF_isPMF hτ n) (seqChan_isChannel hA n)
    (fun p => seqChan_isChannel hB n (zipSeq p.1 p.2)) (relaySeq_isChannel hW n)
  have hexpb : exp (-(n * (γ / 2))) ≥ 0 := (exp_pos _).le
  -- each term
  have t₁ : (((⌈exp (n * R')⌉₊ : ℕ) : ℝ) - 1) * relayFa (iidPMF τ n) (seqChan A n)
      (fun p => seqChan B n (zipSeq p.1 p.2)) (relaySeq W n) (relayT₁ L n ε) ≤
      2 * exp (-(n * (γ / 2))) := by
    by_cases h0 : R' = 0
    · have : ((⌈exp (n * R')⌉₊ : ℕ) : ℝ) = 1 := by simp [h0]
      rw [this]
      simp only [sub_self, zero_mul]
      positivity
    have hγ' := hγa h0
    calc _ ≤ ((⌈exp (n * R')⌉₊ : ℕ) : ℝ) * relayFa (iidPMF τ n) (seqChan A n)
          (fun p => seqChan B n (zipSeq p.1 p.2)) (relaySeq W n) (relayT₁ L n ε) :=
          mul_le_mul_of_nonneg_right (by linarith) hFa0
      _ ≤ (2 * exp (n * R')) * exp (-(n * (rGapA L - ε * rErrA L))) :=
          mul_le_mul (hceil _ hR') hFa hFa0 (by positivity)
      _ = 2 * exp (n * R' + -(n * (rGapA L - ε * rErrA L))) := by rw [mul_assoc, exp_add]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
          nlinarith
  have hFc0 := relayFc_nonneg (T₂ := relayT₂ L n ε) (iidPMF_isPMF hτ n) (seqChan_isChannel hA n)
    (fun p => seqChan_isChannel hB n (zipSeq p.1 p.2)) (relaySeq_isChannel hW n)
  have t₂ : (((⌈exp (n * R'')⌉₊ : ℕ) : ℝ) - 1) * relayFc (iidPMF τ n) (seqChan A n)
      (fun p => seqChan B n (zipSeq p.1 p.2)) (relaySeq W n) (relayT₂ L n ε) ≤
      2 * exp (-(n * (γ / 2))) := by
    by_cases h0 : R'' = 0
    · have : ((⌈exp (n * R'')⌉₊ : ℕ) : ℝ) = 1 := by simp [h0]
      rw [this]
      simp only [sub_self, zero_mul]
      positivity
    have hγ' := hγc h0
    calc _ ≤ ((⌈exp (n * R'')⌉₊ : ℕ) : ℝ) * relayFc (iidPMF τ n) (seqChan A n)
          (fun p => seqChan B n (zipSeq p.1 p.2)) (relaySeq W n) (relayT₂ L n ε) :=
          mul_le_mul_of_nonneg_right (by linarith) hFc0
      _ ≤ (2 * exp (n * R'')) * exp (-(n * (rGapC L - ε * rErrC L))) :=
          mul_le_mul (hceil _ hR'') hFc hFc0 (by positivity)
      _ = 2 * exp (n * R'' + -(n * (rGapC L - ε * rErrC L))) := by rw [mul_assoc, exp_add]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
          nlinarith
  have hFl0 := relayFl_nonneg (T₂ := relayT₂ L n ε) (iidPMF_isPMF hτ n) (seqChan_isChannel hA n)
    (fun p => seqChan_isChannel hB n (zipSeq p.1 p.2)) (relaySeq_isChannel hW n)
  have t₃ : ((⌈exp (n * R')⌉₊ : ℕ) : ℝ) * ((⌈exp (n * R'')⌉₊ : ℕ) : ℝ) *
      relayFl (iidPMF τ n) (seqChan A n)
      (fun p => seqChan B n (zipSeq p.1 p.2)) (relaySeq W n) (relayT₂ L n ε) ≤
      4 * exp (-(n * (γ / 2))) := by
    calc _ ≤ ((2 * exp (n * R')) * (2 * exp (n * R''))) *
          exp (-(n * (rGapL L - ε * rErrL L))) :=
          mul_le_mul (mul_le_mul (hceil _ hR') (hceil _ hR'') (Nat.cast_nonneg _) (by positivity))
            hFl hFl0 (by positivity)
      _ = 4 * exp (n * R' + n * R'' + -(n * (rGapL L - ε * rErrL L))) := by
          rw [exp_add, exp_add]
          ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
          nlinarith
  linarith

end InfoTheory
