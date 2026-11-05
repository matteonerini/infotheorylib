/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayStrategy

/-!
# Massey's directed information

Pages 18-53 to 18-57 of the notes.

## Main definitions

* `directedInfo`: the directed information `I(Xⁿ → Yⁿ)`.
* `causalDirectedInfo`: the directed information `I(Xⁿ → Yⁿ || Zⁿ)` causally conditioned on `Zⁿ`.

## Main statements

* `directedInfo_le_mutualInfo`: **Massey's inequality** `I(Xⁿ → Yⁿ) ≤ I(Xⁿ; Yⁿ)`.
* `condMutualInfo_markov_step`: the step that keeps two messages independent given the past.
* `cInfo_stratW_eq_causalDirectedInfo`: **the information of two strategies is a directed
  information**: `I(T₁; Yⁿ | T₂) = I(X₁ⁿ → Yⁿ || X₂ⁿ)`.

## Implementation notes

The notes define the regions of Theorem 7 with causally conditional laws `p(x₁ⁿ || yⁿ⁻¹)`, while
`twcMultiRegion` uses random strategies; we do not prove the functional representation that relates
the two. The last theorem above identifies the two expressions of the rates. The statement for
`I(X₂ⁿ → Yⁿ || X₁ⁿ)` is the same theorem for the channel with the inputs exchanged.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section Defs

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] {n : ℕ}

/-- **Page 18-53 of [elgamal2010].** The directed information
`I(Xⁿ → Yⁿ) = ∑ᵢ I(Xⁱ; Yᵢ | Yⁱ⁻¹)`. -/
def directedInfo (μ : Ω → ℝ) (X : Ω → Fin n → α) (Y : Ω → Fin n → β) : ℝ :=
  ∑ i : Fin n, I[fun ω => degradedBCPast ((i : ℕ) + 1) (X ω) : fun ω => Y ω i |
    fun ω => degradedBCPast (i : ℕ) (Y ω) ; μ]

/-- **Page 18-53 of [elgamal2010].** The directed information causally conditioned on `Zⁿ`,
`I(Xⁿ → Yⁿ || Zⁿ) = ∑ᵢ I(Xⁱ; Yᵢ | Yⁱ⁻¹, Zⁱ)`. -/
def causalDirectedInfo (μ : Ω → ℝ) (X : Ω → Fin n → α) (Y : Ω → Fin n → β) (Z : Ω → Fin n → γ) :
    ℝ :=
  ∑ i : Fin n, I[fun ω => degradedBCPast ((i : ℕ) + 1) (X ω) : fun ω => Y ω i |
    pair (fun ω => degradedBCPast (i : ℕ) (Y ω)) (fun ω => degradedBCPast ((i : ℕ) + 1) (Z ω)) ; μ]

variable {μ : Ω → ℝ}

/-- **Massey's inequality.** `I(Xⁿ → Yⁿ) ≤ I(Xⁿ; Yⁿ)`. -/
theorem directedInfo_le_mutualInfo (hμ : IsPMF μ) (X : Ω → Fin n → α) (Y : Ω → Fin n → β) :
    directedInfo μ X Y ≤ I[X : Y ; μ] := by
  classical
  have hI : I[X : Y ; μ] = H[Y | fun _ => () ; μ] - H[Y | X ; μ] := by
    have hc : H[Y | fun _ : Ω => () ; μ] = H[Y ; μ] := by
      rw [condEntropy_eq_sub hμ]
      have h₁ : H[pair (fun _ : Ω => ()) Y ; μ] = H[Y ; μ] :=
        entropyRV_eq_of_injective μ (fun y => ((), y)) (fun _ _ h => (Prod.ext_iff.mp h).2)
          fun _ => rfl
      have h₂ : H[fun _ : Ω => () ; μ] = 0 := by
        have hc : dist μ (fun _ => ()) = fun _ => 1 := by
          funext k
          simpa [dist] using hμ.sum_eq_one
        simp [entropyRV, hc, entropy]
      rw [h₁, h₂, sub_zero]
    rw [hc, mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
  rw [hI, condEntropy_eq_sum_past hμ, condEntropy_eq_sum_past hμ, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  have e₁ : H[fun ω => Y ω i | pair (fun ω => degradedBCPast (i : ℕ) (Y ω)) (fun _ => ()) ; μ] =
      H[fun ω => Y ω i | fun ω => degradedBCPast (i : ℕ) (Y ω) ; μ] :=
    condEntropy_congr_right hμ _ (fun p => (p, ())) (fun _ _ h => (Prod.ext_iff.mp h).1)
      fun _ => rfl
  have hL : I[fun ω => degradedBCPast ((i : ℕ) + 1) (X ω) : fun ω => Y ω i |
      fun ω => degradedBCPast (i : ℕ) (Y ω) ; μ] =
      H[fun ω => Y ω i | fun ω => degradedBCPast (i : ℕ) (Y ω) ; μ] -
        H[fun ω => Y ω i | pair (fun ω => degradedBCPast (i : ℕ) (Y ω))
          (fun ω => degradedBCPast ((i : ℕ) + 1) (X ω)) ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
  have h₂ := condEntropy_le_condEntropy_comp hμ (fun ω => Y ω i)
    (pair (fun ω => degradedBCPast (i : ℕ) (Y ω)) X)
    (fun t : (Fin n → Option β) × (Fin n → α) => (t.1, degradedBCPast ((i : ℕ) + 1) t.2))
  have e₃ : (fun t : (Fin n → Option β) × (Fin n → α) =>
      (t.1, degradedBCPast ((i : ℕ) + 1) t.2)) ∘ pair (fun ω => degradedBCPast (i : ℕ) (Y ω)) X =
      pair (fun ω => degradedBCPast (i : ℕ) (Y ω))
        (fun ω => degradedBCPast ((i : ℕ) + 1) (X ω)) := rfl
  rw [e₃] at h₂
  rw [hL, e₁]
  linarith

end Defs

section Step

variable {Ω a b c d : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  {μ : Ω → ℝ}

/-- **The step that keeps two messages independent given the past.** Let `A` and `B` be independent
given `C`, and suppose that `O` does not depend on `B` given `(C, A)`. Then `A` and `B` are
independent given `(C, O)`, and `O` does not depend on `B` given `C`. -/
theorem condMutualInfo_markov_step (hμ : IsPMF μ) (A : Ω → a) (B : Ω → b) (O : Ω → d) (C : Ω → c)
    {S : ℝ} (h₀ : I[A : B | C ; μ] = 0) (h₁ : H[O | pair C A ; μ] ≤ S)
    (h₂ : S ≤ H[O | pair (pair C A) B ; μ]) :
    I[A : B | pair C O ; μ] = 0 ∧ I[B : O | C ; μ] = 0 := by
  have hi := condMutualInfo_interaction hμ B A O C
  have hz : I[B : O | pair C A ; μ] = 0 := by
    refine le_antisymm ?_ (condMutualInfo_nonneg hμ _ _ _)
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    linarith
  have e₀ : I[B : A | C ; μ] = 0 := by
    rw [condMutualInfo_comm hμ]
    exact h₀
  rw [hz, e₀] at hi
  have n₁ := condMutualInfo_nonneg hμ B A (pair C O)
  have n₂ := condMutualInfo_nonneg hμ B O C
  have z₁ : I[B : A | pair C O ; μ] = 0 := by linarith
  have z₂ : I[B : O | C ; μ] = 0 := by linarith
  refine ⟨?_, z₂⟩
  rw [condMutualInfo_comm hμ]
  exact z₁

/-- Conditioning on a function of `B` and `C` does not increase `I(A; B | C)`. -/
theorem condMutualInfo_cond_comp_le (hμ : IsPMF μ) (A : Ω → a) (B : Ω → b) (C : Ω → c)
    (f : c × b → d) : I[A : B | pair C (f ∘ pair C B) ; μ] ≤ I[A : B | C ; μ] := by
  have hi := condMutualInfo_interaction hμ A B (f ∘ pair C B) C
  have hz : I[A : f ∘ pair C B | pair C B ; μ] ≤ 0 := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ, condEntropy_comp_self hμ]
    have := condEntropy_nonneg hμ (f ∘ pair C B) (pair (pair C B) A)
    linarith
  have hn := condMutualInfo_nonneg hμ A (f ∘ pair C B) C
  linarith

end Step

/-! ### Strategies -/

section Strategies

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y] {V : X₁ × X₂ → Y → ℝ} {n : ℕ}
  [Nonempty X₁] [Nonempty X₂] [Nonempty Y]

/-- The past inputs of a strategy from the masked past outputs. -/
def xFromPast {α : Type*} (s : Strat n α Y) (k' : ℕ) (p : Fin n → Option Y) : Fin n → Option α :=
  fun j => if (j : ℕ) < k' then
    some (s j fun t => (p ⟨t, t.2.trans j.2⟩).getD (Classical.arbitrary Y)) else none

/-- The inputs of a strategy, as a sequence. -/
def stratSeq {α : Type*} (s : Strat n α Y) (y : Fin n → Y) : Fin n → α :=
  fun j => s j (fbPre j y)

omit [Fintype X₁] [Fintype X₂] [Fintype Y] [Nonempty X₁] [Nonempty X₂] in
/-- The inputs before a time from the outputs before that time. -/
lemma xFromPast_eq {α : Type*} (s : Strat n α Y) {i k' : ℕ} (h : k' ≤ i + 1) (y : Fin n → Y) :
    xFromPast s k' (degradedBCPast i y) = degradedBCPast k' (stratSeq s y) := by
  funext j
  by_cases hj : (j : ℕ) < k'
  · have ht : ∀ t : Fin j, (t : ℕ) < i := fun t => by
      have := t.2
      omega
    simp only [xFromPast, degradedBCPast, hj, ite_true, stratSeq]
    congr 2
    funext t
    simp [ht t]
    rfl
  · simp [xFromPast, degradedBCPast, hj]

/-- The law of two independent strategies and of the outputs. -/
abbrev stratLaw (p₁ : Strat n X₁ Y → ℝ) (p₂ : Strat n X₂ Y → ℝ) (V : X₁ × X₂ → Y → ℝ) :
    (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → ℝ :=
  jointOf (prodDist p₁ p₂) (stratW V n)

variable {p₁ : Strat n X₁ Y → ℝ} {p₂ : Strat n X₂ Y → ℝ}

omit [Fintype X₁] [Fintype X₂] [Fintype Y] [Nonempty Y] in
/-- The law of two independent strategies is the law of a code with feedback. -/
lemma stratLaw_eq :
    stratLaw p₁ p₂ V = fbLaw (prodDist p₁ p₂) V (stratEnc n) n := by
  funext ⟨s, y⟩
  rw [fbLaw_eq_prod, stratLaw, jointOf, stratW_eq_prod]

/-- **The information of two strategies is a directed information.**
`I(T₁; Yⁿ | T₂) = I(X₁ⁿ → Yⁿ || X₂ⁿ)`. -/
theorem cInfo_stratW_eq_causalDirectedInfo (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hV : IsChannel V) :
    cInfo (prodDist p₁ p₂) (stratW V n) =
      causalDirectedInfo (stratLaw p₁ p₂ V) (fun z => stratSeq z.1.1 z.2) Prod.snd
        (fun z => stratSeq z.1.2 z.2) := by
  classical
  have hP := hp₁.prodDist hp₂
  have hS : IsChannel (stratW V n) := stratW_isChannel hV
  have hμ : IsPMF (stratLaw p₁ p₂ V) := jointOf_isPMF hP hS
  set μ := stratLaw p₁ p₂ V with hμd
  let T₁ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → Strat n X₁ Y := fun z => z.1.1
  let T₂ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → Strat n X₂ Y := fun z => z.1.2
  let P : ℕ → (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → Fin n → Option Y :=
    fun i z => degradedBCPast i z.2
  let Q₁ : ℕ → (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → Fin n → Option X₁ :=
    fun i z => degradedBCPast i (stratSeq z.1.1 z.2)
  let Q₂ : ℕ → (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → Fin n → Option X₂ :=
    fun i z => degradedBCPast i (stratSeq z.1.2 z.2)
  let O : Fin n → (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → Y := fun i z => z.2 i
  let X : Fin n → (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) → X₁ × X₂ :=
    fun i z => (stratSeq z.1.1 z.2 i, stratSeq z.1.2 z.2 i)
  let Si : Fin n → ℝ := fun i => ∑ a, dist μ (X i) a * entropy (V a)
  -- the entropy of the output given the inputs
  have hX : ∀ i, H[O i | X i ; μ] = Si i := by
    intro i
    have hlaw : ∀ t b, dist μ (pair (X i) (O i)) (t, b) = dist μ (X i) t * V t b := by
      intro t b
      have h := dist_fbLaw_letter (ν := prodDist p₁ p₂) (W := V) (enc := stratEnc n) hV i
        (fun t : (Strat n X₁ Y × Strat n X₂ Y) × (Fin i → Y) => stratEnc n i t.1 t.2) id
        (fun _ _ => rfl) t b
      rw [← stratLaw_eq] at h
      have e : (fun z : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) =>
          stratEnc n i z.1 (fbPre i z.2)) = X i := by
        funext z
        simp [stratEnc, X, stratSeq, i.2]
      rw [e] at h
      exact h
    exact condEntropy_of_channel (W := V) id hlaw
  have hT : ∀ i, H[O i | pair (P i) Prod.fst ; μ] = Si i := by
    intro i
    have hinj : H[O i | pair (P i) Prod.fst ; μ] =
        H[O i | pair (fun z => fbPre i z.2) Prod.fst ; μ] :=
      condEntropy_congr_right hμ _ (fun t : (Fin i → Y) × (Strat n X₁ Y × Strat n X₂ Y) =>
        (BCFBCode.mask i t.1, t.2))
        (fun a b h => Prod.ext (BCFBCode.mask_injective i (Prod.ext_iff.mp h).1)
          (Prod.ext_iff.mp h).2)
        fun z => by simp only [pair, BCFBCode.mask_fbPre, P]
    rw [hinj]
    have hlaw : ∀ t b, dist μ (pair (pair (fun z => fbPre i z.2) Prod.fst) (O i)) (t, b) =
        dist μ (pair (fun z => fbPre i z.2) Prod.fst) t *
          V (stratEnc n i t.2 t.1) b := by
      intro t b
      have h := dist_fbLaw_letter (ν := prodDist p₁ p₂) (W := V) (enc := stratEnc n) hV i
        (fun t : (Strat n X₁ Y × Strat n X₂ Y) × (Fin i → Y) => (t.2, t.1))
        (fun t => stratEnc n i t.2 t.1) (fun _ _ => rfl) t b
      rw [← stratLaw_eq] at h
      exact h
    have hch := condEntropy_of_channel (W := V) (μ := μ) (fun t : (Fin i → Y) ×
      (Strat n X₁ Y × Strat n X₂ Y) => stratEnc n i t.2 t.1) hlaw
    rw [hch]
    have e : (fun t : (Fin i → Y) × (Strat n X₁ Y × Strat n X₂ Y) => stratEnc n i t.2 t.1) ∘
        pair (fun z => fbPre i z.2) Prod.fst = X i := by
      funext z
      simp [stratEnc, X, stratSeq, i.2, pair]
    rw [e]
  let ar : Y := Classical.arbitrary Y
  let C : Fin n → (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) →
      (Fin n → Option Y) × (Fin n → Option X₂) := fun i => pair (P i) (Q₂ ((i : ℕ) + 1))
  have hfpre : ∀ (i : Fin n) (y : Fin n → Y),
      (fun t : Fin i => (degradedBCPast (i : ℕ) y ⟨t, t.2.trans i.2⟩).getD ar) = fbPre i y := by
    intro i y
    funext t
    simp [degradedBCPast]
    rfl
  -- the two bounds
  have hL : ∀ i, H[O i | pair (C i) T₁ ; μ] ≤ Si i := by
    intro i
    have h := condEntropy_le_condEntropy_comp hμ (O i) (pair (C i) T₁)
      (fun t : ((Fin n → Option Y) × (Fin n → Option X₂)) × Strat n X₁ Y =>
        (t.2 i fun u => (t.1.1 ⟨u, u.2.trans i.2⟩).getD ar,
          (t.1.2 i).getD (Classical.arbitrary X₂)))
    have e : (fun t : ((Fin n → Option Y) × (Fin n → Option X₂)) × Strat n X₁ Y =>
        (t.2 i fun u => (t.1.1 ⟨u, u.2.trans i.2⟩).getD ar,
          (t.1.2 i).getD (Classical.arbitrary X₂))) ∘ pair (C i) T₁ = X i := by
      funext z
      simp only [Function.comp, pair, C, P, Q₂, T₁, X, hfpre]
      simp [degradedBCPast, stratSeq]
    rw [e, hX] at h
    exact h
  have hR : ∀ i, Si i ≤ H[O i | pair (pair (C i) T₁) T₂ ; μ] := by
    intro i
    have h := condEntropy_le_condEntropy_comp hμ (O i) (pair (P i) Prod.fst)
      (fun t : (Fin n → Option Y) × (Strat n X₁ Y × Strat n X₂ Y) =>
        (((t.1, xFromPast t.2.2 ((i : ℕ) + 1) t.1), t.2.1), t.2.2))
    have e : (fun t : (Fin n → Option Y) × (Strat n X₁ Y × Strat n X₂ Y) =>
        (((t.1, xFromPast t.2.2 ((i : ℕ) + 1) t.1), t.2.1), t.2.2)) ∘ pair (P i) Prod.fst =
        pair (pair (C i) T₁) T₂ := by
      funext z
      simp only [Function.comp, pair, C, P, Q₂, T₁, T₂, xFromPast_eq _ le_rfl]
    rw [e, hT] at h
    exact h
  -- the base of the induction
  have hbase : I[T₁ : T₂ | pair (P 0) (Q₂ 0) ; μ] = 0 := by
    have hc : pair (P 0) (Q₂ 0) = fun _ => ((fun _ => none), (fun _ => none)) := by
      funext z
      refine Prod.ext ?_ ?_ <;> funext j <;> simp [pair, P, Q₂, degradedBCPast]
    have hd : dist μ Prod.fst = prodDist p₁ p₂ := dist_jointOf_fst hS
    have hd₁ : H[T₁ ; μ] = entropy p₁ := by
      have ee : T₁ = Prod.fst ∘ Prod.fst := rfl
      rw [entropyRV, ee, dist_dist_comp, hd, dist_prodDist_fst hp₂]
    have hd₂ : H[T₂ ; μ] = entropy p₂ := by
      have ee : T₂ = Prod.snd ∘ Prod.fst := rfl
      rw [entropyRV, ee, dist_dist_comp, hd, dist_prodDist_snd hp₁]
    have hd₃ : H[Prod.fst ; μ] = entropy p₁ + entropy p₂ := by
      rw [entropyRV, hd, entropy_prodDist hp₁ hp₂]
    set c₀ : (Fin n → Option Y) × (Fin n → Option X₂) := ((fun _ => none), (fun _ => none)) with hc₀
    have e₁ : H[pair (fun _ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => c₀) T₁ ; μ] = H[T₁ ; μ]
      :=
      entropyRV_eq_of_injective _ (fun a => (c₀, a)) (fun s t h => (Prod.ext_iff.mp h).2)
        fun _ => rfl
    have e₂ : H[pair (fun _ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => c₀) T₂ ; μ] = H[T₂ ; μ]
      :=
      entropyRV_eq_of_injective _ (fun a => (c₀, a)) (fun s t h => (Prod.ext_iff.mp h).2)
        fun _ => rfl
    have e₃ : H[pair (pair (fun _ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => c₀) T₂) T₁ ; μ] =
        H[Prod.fst ; μ] :=
      entropyRV_eq_of_injective _ (fun w : Strat n X₁ Y × Strat n X₂ Y => ((c₀, w.2), w.1))
        (fun s t h => by simpa [Prod.ext_iff, and_comm] using h) fun _ => rfl
    have e₄ : H[fun _ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => c₀ ; μ] = 0 := by
      have hu : H[fun _ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => c₀ ; μ] =
          H[fun _ : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => () ; μ] :=
        entropyRV_eq_of_injective _ (fun _ : Unit => c₀) (fun _ _ _ => rfl) fun _ => rfl
      have hc' : dist μ (fun _ => ()) = fun _ => 1 := by
        funext k
        simpa [dist] using hμ.sum_eq_one
      rw [hu, entropyRV, hc']
      simp [entropy]
    rw [hc, condMutualInfo_eq_entropies hμ, e₁, e₂, e₃, e₄, hd₁, hd₂, hd₃]
    ring
  -- the induction
  have hstep : ∀ i : Fin n, I[T₁ : T₂ | pair (P i) (Q₂ i) ; μ] = 0 →
      I[T₁ : T₂ | pair (P ((i : ℕ) + 1)) (Q₂ ((i : ℕ) + 1)) ; μ] = 0 ∧ I[T₂ : O i | C i ; μ] = 0 :=
        by
    intro i h0
    -- conditioning on the present input of sender 2
    have h₁ : I[T₁ : T₂ | C i ; μ] = 0 := by
      refine le_antisymm ?_ (condMutualInfo_nonneg hμ _ _ _)
      have hle := condMutualInfo_cond_comp_le hμ T₁ T₂ (pair (P i) (Q₂ i))
        (fun t : ((Fin n → Option Y) × (Fin n → Option X₂)) × Strat n X₂ Y =>
          t.2 i fun u => (t.1.1 ⟨u, u.2.trans i.2⟩).getD ar)
      rw [h0] at hle
      refine le_trans (le_of_eq ?_) hle
      refine condMutualInfo_cond_congr' hμ T₁ T₂
        (fun t : ((Fin n → Option Y) × (Fin n → Option X₂)) × X₂ =>
          (t.1.1, Function.update t.1.2 i (some t.2)))
        (fun t : (Fin n → Option Y) × (Fin n → Option X₂) =>
          ((t.1, Function.update t.2 i none), (t.2 i).getD (Classical.arbitrary X₂))) ?_ ?_
      · funext z
        refine Prod.ext rfl ?_
        funext j
        simp only [Function.comp, pair, C, P, Q₂, T₂, degradedBCPast, Function.update_apply]
        by_cases hj : j = i
        · subst hj
          simp [stratSeq]
          rfl
        · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
          have : ((j : ℕ) < i + 1) ↔ (j : ℕ) < i := by omega
          simp [hj, this]
      · funext z
        refine Prod.ext (Prod.ext rfl ?_) ?_
        · funext j
          simp only [Function.comp, pair, C, P, Q₂, degradedBCPast, Function.update_apply]
          by_cases hj : j = i
          · subst hj
            simp
          · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
            have : ((j : ℕ) < i + 1) ↔ (j : ℕ) < i := by omega
            simp [hj, this]
        · simp only [Function.comp, pair, C, Q₂, T₂]
          refine (congrArg (z.1.2 i) (hfpre i z.2)).trans ?_
          simp [degradedBCPast, stratSeq]
    obtain ⟨h₂, h₃⟩ := condMutualInfo_markov_step hμ T₁ T₂ (O i) (C i) h₁ (hL i) (hR i)
    refine ⟨?_, h₃⟩
    refine (condMutualInfo_cond_congr' hμ T₁ T₂
      (fun t : ((Fin n → Option Y) × (Fin n → Option X₂)) × Y =>
        (Function.update t.1.1 i (some t.2), t.1.2))
      (fun t : (Fin n → Option Y) × (Fin n → Option X₂) =>
        ((Function.update t.1 i none, t.2), (t.1 i).getD ar)) ?_ ?_).trans h₂
    · funext z
      refine Prod.ext ?_ rfl
      funext j
      simp only [Function.comp, pair, C, P, O, degradedBCPast, Function.update_apply]
      by_cases hj : j = i
      · subst hj
        simp
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        have : ((j : ℕ) < i + 1) ↔ (j : ℕ) < i := by omega
        simp [hj, this]
    · funext z
      refine Prod.ext (Prod.ext ?_ rfl) ?_
      · funext j
        simp only [Function.comp, pair, C, P, degradedBCPast, Function.update_apply]
        by_cases hj : j = i
        · subst hj
          simp
        · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
          have : ((j : ℕ) < i + 1) ↔ (j : ℕ) < i := by omega
          simp [hj, this]
      · simp [Function.comp, pair, P, O, degradedBCPast]
  have hall : ∀ (i : ℕ) (hi : i ≤ n), I[T₁ : T₂ | pair (P i) (Q₂ i) ; μ] = 0 := by
    intro i
    induction i with
    | zero => exact fun _ => hbase
    | succ j ih =>
      intro hj
      exact (hstep ⟨j, hj⟩ (ih (Nat.le_of_succ_le hj))).1
  have hM : ∀ i : Fin n, I[T₂ : O i | C i ; μ] = 0 := fun i =>
    (hstep i (hall i i.2.le)).2
  -- the terms of the sum
  have hterm₁ : ∀ i : Fin n, H[O i | pair (P i) T₂ ; μ] = H[O i | C i ; μ] := by
    intro i
    have h := hM i
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ] at h
    have e : H[O i | pair (C i) T₂ ; μ] = H[O i | pair (P i) T₂ ; μ] :=
      condEntropy_congr_right hμ _
        (fun t : (Fin n → Option Y) × Strat n X₂ Y =>
          ((t.1, xFromPast t.2 ((i : ℕ) + 1) t.1), t.2))
        (fun s t h => by
          have h' := Prod.ext_iff.mp h
          exact Prod.ext (Prod.ext_iff.mp h'.1).1 h'.2)
        fun z => by simp only [pair, C, P, Q₂, T₂, xFromPast_eq _ le_rfl]
    rw [e] at h
    linarith
  have hterm₂ : ∀ i : Fin n, H[O i | pair (C i) (Q₁ ((i : ℕ) + 1)) ; μ] = Si i := by
    intro i
    refine le_antisymm ?_ ?_
    · have h := condEntropy_le_condEntropy_comp hμ (O i) (pair (C i) (Q₁ ((i : ℕ) + 1)))
        (fun t : ((Fin n → Option Y) × (Fin n → Option X₂)) × (Fin n → Option X₁) =>
          ((t.2 i).getD (Classical.arbitrary X₁), (t.1.2 i).getD (Classical.arbitrary X₂)))
      have e : (fun t : ((Fin n → Option Y) × (Fin n → Option X₂)) × (Fin n → Option X₁) =>
          ((t.2 i).getD (Classical.arbitrary X₁), (t.1.2 i).getD (Classical.arbitrary X₂))) ∘
          pair (C i) (Q₁ ((i : ℕ) + 1)) = X i := by
        funext z
        simp [Function.comp, pair, C, Q₁, Q₂, X, degradedBCPast]
      rw [e, hX] at h
      exact h
    · have h := condEntropy_le_condEntropy_comp hμ (O i) (pair (P i) Prod.fst)
        (fun t : (Fin n → Option Y) × (Strat n X₁ Y × Strat n X₂ Y) =>
          ((t.1, xFromPast t.2.2 ((i : ℕ) + 1) t.1), xFromPast t.2.1 ((i : ℕ) + 1) t.1))
      have e : (fun t : (Fin n → Option Y) × (Strat n X₁ Y × Strat n X₂ Y) =>
          ((t.1, xFromPast t.2.2 ((i : ℕ) + 1) t.1), xFromPast t.2.1 ((i : ℕ) + 1) t.1)) ∘
          pair (P i) Prod.fst = pair (C i) (Q₁ ((i : ℕ) + 1)) := by
        funext z
        simp only [Function.comp, pair, C, P, Q₁, Q₂, xFromPast_eq _ le_rfl]
      rw [e, hT] at h
      exact h
  -- the sum
  have hc : cInfo (prodDist p₁ p₂) (stratW V n) =
      H[Prod.snd | T₂ ; μ] - H[Prod.snd | Prod.fst ; μ] := by
    have e : cInfo (prodDist p₁ p₂) (stratW V n) = I[T₁ : Prod.snd | T₂ ; μ] := rfl
    rw [e, condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    congr 1
    exact condEntropy_congr_right hμ _ (fun w : Strat n X₁ Y × Strat n X₂ Y => (w.2, w.1))
      (fun a b h => Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1) fun _ => rfl
  rw [hc, condEntropy_eq_sum_past hμ, condEntropy_eq_sum_past hμ, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  have e₁ : H[fun ω : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => ω.2 i |
      pair (fun ω => degradedBCPast (i : ℕ) ω.2) T₂ ; μ] = H[O i | pair (P i) T₂ ; μ] := rfl
  have e₂ : H[fun ω : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => ω.2 i |
      pair (fun ω => degradedBCPast (i : ℕ) ω.2) Prod.fst ; μ] =
      H[O i | pair (P i) Prod.fst ; μ] := rfl
  rw [e₁, e₂, hterm₁, hT]
  have e₃ : I[fun ω : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) =>
      degradedBCPast ((i : ℕ) + 1) (stratSeq ω.1.1 ω.2) : fun ω => ω.2 i |
      pair (fun ω => degradedBCPast (i : ℕ) ω.2)
        (fun ω => degradedBCPast ((i : ℕ) + 1) (stratSeq ω.1.2 ω.2)) ; μ] =
      I[Q₁ ((i : ℕ) + 1) : O i | C i ; μ] := rfl
  rw [e₃, condMutualInfo_comm hμ, condMutualInfo_eq' hμ, hterm₂]

end Strategies

end InfoTheory
