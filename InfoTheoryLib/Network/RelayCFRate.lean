/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungBinning
public import InfoTheoryLib.Network.RelayCFRandom
public import InfoTheoryLib.Network.RelayDF
public import InfoTheoryLib.StateChannel.GPDerandomize

/-!
# Codes for one block of compress–forward

We fix the tests of the random code of compress–forward, and bound its average error.

## Main definitions

* `cfT₁`, `cfT₂`, `cfTj`: the tests of the decoder of the state of the relay, of the decoder of the
  message, and of the relay.
* `cfGapU`, `cfGapX`, `cfGapV`, `cfGapW`, `cfGapC`: the exponents of the error events.

## Main statements

* `exists_cfBlock_gaps`: the random coding bound in terms of the gaps.
* `eventually_cfBlock`: **codes for one block**, for rates that satisfy the conditions of the notes.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X U Y S V : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype S] [Fintype V]

/-- `(Y, X₁)`. -/
def cfF₁ (z : ((X × U) × (Y × S)) × V) : Y × U := (z.1.2.1, z.1.1.2)

/-- `((X₁, Ŷ₁, Y), X)`. -/
def cfF₂ (z : ((X × U) × (Y × S)) × V) : (U × V × Y) × X := ((z.1.1.2, z.2, z.1.2.1), z.1.1.1)

/-- `((X₁, Y₁), Ŷ₁)`. -/
def cfFJ (z : ((X × U) × (Y × S)) × V) : (U × S) × V := ((z.1.1.2, z.1.2.2), z.2)

/-- `((X₁, Y), X)`. -/
def cfF₄ (z : ((X × U) × (Y × S)) × V) : (U × Y) × X := ((z.1.1.2, z.1.2.1), z.1.1.1)

/-- `(((X₁, Y), X), Ŷ₁)`. -/
def cfF₃ (z : ((X × U) × (Y × S)) × V) : ((U × Y) × X) × V := (cfF₄ z, z.2)

/-- The test of the decoder of the state of the relay. -/
def cfT₁ (μ : ((X × U) × (Y × S)) × V → ℝ) (n : ℕ) (ε : ℝ) (u : Fin n → U) (y : Fin n → Y) : Prop :=
  (fun i => (y i, u i)) ∈ robustTypicalSet (dist μ cfF₁) n ε

/-- The test of the decoder of the message. -/
def cfT₂ (μ : ((X × U) × (Y × S)) × V → ℝ) (n : ℕ) (ε : ℝ) (x : Fin n → X) (u : Fin n → U)
    (v : Fin n → V) (y : Fin n → Y) : Prop :=
  (fun i => ((u i, v i, y i), x i)) ∈ robustTypicalSet (dist μ cfF₂) n ε

/-- The test of the relay. -/
def cfTj (μ : ((X × U) × (Y × S)) × V → ℝ) (n : ℕ) (ε : ℝ) (u : Fin n → U) (s : Fin n → S)
    (v : Fin n → V) : Prop :=
  (fun i => ((u i, s i), v i)) ∈ robustTypicalSet (dist μ cfFJ) n ε

/-- The gap of a wrong state of the relay: `I(X₁; Y)`. -/
def cfGapU (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[fun z => z.1.2.1 ; μ] + H[fun z => z.1.1.2 ; μ] - H[cfF₁ ; μ]

/-- The correction to the gap of a wrong state. -/
def cfErrU (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[cfF₁ ; μ] + H[fun z => z.1.2.1 ; μ] + H[fun z => z.1.1.2 ; μ]

/-- The gap of a wrong message for the chosen description: `I(X; X₁, Ŷ₁, Y)`. -/
def cfGapX (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[fun z => (z.1.1.2, z.2, z.1.2.1) ; μ] + H[fun z => z.1.1.1 ; μ] - H[cfF₂ ; μ]

/-- The correction to the gap of a wrong message. -/
def cfErrX (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[cfF₂ ; μ] + H[fun z => (z.1.1.2, z.2, z.1.2.1) ; μ] + H[fun z => z.1.1.1 ; μ]

/-- The gap of a wrong description given a wrong message: `I(Ŷ₁; X, Y | X₁)`. -/
def cfGapV (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[cfF₄ ; μ] + H[fun z => (z.1.1.2, z.2) ; μ] - H[fun z => z.1.1.2 ; μ] - H[cfF₃ ; μ]

/-- The correction to the gap of a wrong description. -/
def cfErrV (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[cfF₃ ; μ] + H[cfF₄ ; μ] + H[fun z => (z.1.1.2, z.2) ; μ] + H[fun z => z.1.1.2 ; μ]

/-- The gap of a wrong message, for the test without the description: `I(X; X₁, Y)`. -/
def cfGapW (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[fun z => (z.1.1.2, z.1.2.1) ; μ] + H[fun z => z.1.1.1 ; μ] - H[cfF₄ ; μ]

/-- The correction to that gap. -/
def cfErrW (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[cfF₄ ; μ] + H[fun z => (z.1.1.2, z.1.2.1) ; μ] + H[fun z => z.1.1.1 ; μ]

/-- The rate of the covering: `I(Y₁; Ŷ₁ | X₁)`. -/
def cfGapC (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[fun z => (z.1.1.2, z.1.2.2) ; μ] + H[fun z => (z.1.1.2, z.2) ; μ] - H[fun z => z.1.1.2 ; μ] -
    H[cfFJ ; μ]

/-- The correction to the rate of the covering. -/
def cfErrC (μ : ((X × U) × (Y × S)) × V → ℝ) : ℝ :=
  H[fun z => (z.1.1.2, z.1.2.2) ; μ] + H[fun z => (z.1.1.2, z.2) ; μ] + H[fun z => z.1.1.2 ; μ] +
    H[cfFJ ; μ]

variable {p : X → ℝ} {p₁ : U → ℝ} {W : X × U → Y × S → ℝ} {τ : U × S → V → ℝ}

section Marg

/-- The law of a function of the inputs. -/
lemma cfLaw_dist_inputs {β : Type*} (hW : IsChannel W) (hτ : IsChannel τ) (f : X × U → β) :
    dist (cfLaw p p₁ W τ) (fun z => f z.1.1) = dist (prodDist p p₁) f := by
  have h₁ : dist (cfLaw p p₁ W τ) Prod.fst = jointOf (prodDist p p₁) W :=
    dist_jointOf_fst fun _ => hτ _
  have h₂ : dist (jointOf (prodDist p p₁) W) Prod.fst = prodDist p p₁ := dist_jointOf_fst hW
  have e₁ : (fun z : ((X × U) × (Y × S)) × V => f z.1.1) =
      (fun t : (X × U) × (Y × S) => f t.1) ∘ Prod.fst := rfl
  have e₂ : (fun t : (X × U) × (Y × S) => f t.1) = f ∘ Prod.fst := rfl
  rw [e₁, dist_comp_eq, h₁, e₂, dist_comp_eq, h₂]

/-- The marginals of the law. -/
lemma cfLaw_marg (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) :
    dist (cfLaw p p₁ W τ) (fun z => z.1.1.1) = p ∧ dist (cfLaw p p₁ W τ) (fun z => z.1.1.2) = p₁ :=
  ⟨(cfLaw_dist_inputs hW hτ Prod.fst).trans (dist_prodDist_fst hp₁ p),
    (cfLaw_dist_inputs hW hτ Prod.snd).trans (dist_prodDist_snd hp p₁)⟩

end Marg

section Fresh

variable {μ : ((X × U) × (Y × S)) × V → ℝ} {n : ℕ} {ε : ℝ}

/-- A wrong state of the relay. -/
lemma sum_cfT₁_le (hμ : IsPMF μ) (hm : dist μ (fun z => z.1.1.2) = p₁) (y : Fin n → Y) :
    ∑ u, iidPMF p₁ n u * ind (cfT₁ μ n ε u y) ≤ exp (-(n * (cfGapU μ - ε * cfErrU μ))) := by
  have h := sum_fresh_const (hμ.dist cfF₁) (n := n) (ε := ε) (fun r t => cfT₁ μ n ε t r)
    (fun _ _ ht => ht) y
  have e : dist (dist μ cfF₁) Prod.snd = p₁ := by
    rw [← dist_comp_eq]
    exact hm
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  congr 2
  simp only [cfGapU, cfErrU, entropyRV_dist]
  rfl

/-- A wrong message, for a fixed description. -/
lemma sum_cfT₂_le (hμ : IsPMF μ) (hm : dist μ (fun z => z.1.1.1) = p) (u : Fin n → U)
    (v : Fin n → V) (y : Fin n → Y) :
    ∑ x, iidPMF p n x * ind (cfT₂ μ n ε x u v y) ≤ exp (-(n * (cfGapX μ - ε * cfErrX μ))) := by
  have h := sum_fresh_const (hμ.dist cfF₂) (n := n) (ε := ε)
    (fun r t => cfT₂ μ n ε t (fun i => (r i).1) (fun i => (r i).2.1) (fun i => (r i).2.2))
    (fun _ _ ht => ht) (fun i => (u i, v i, y i))
  have e : dist (dist μ cfF₂) Prod.snd = p := by
    rw [← dist_comp_eq]
    exact hm
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  congr 2
  simp only [cfGapX, cfErrX, entropyRV_dist]
  rfl

/-- The test without the description. -/
lemma sum_cfT₄_le (hμ : IsPMF μ) (hm : dist μ (fun z => z.1.1.1) = p) (u : Fin n → U)
    (y : Fin n → Y) :
    ∑ x, iidPMF p n x * ind ((fun i => ((u i, y i), x i)) ∈ robustTypicalSet (dist μ cfF₄) n ε) ≤
      exp (-(n * (cfGapW μ - ε * cfErrW μ))) := by
  have h := sum_fresh_const (hμ.dist cfF₄) (n := n) (ε := ε)
    (fun r t => (fun i => (r i, t i)) ∈ robustTypicalSet (dist μ cfF₄) n ε)
    (fun _ _ ht => ht) (fun i => (u i, y i))
  have e : dist (dist μ cfF₄) Prod.snd = p := by
    rw [← dist_comp_eq]
    exact hm
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  congr 2
  simp only [cfGapW, cfErrW, entropyRV_dist]
  rfl

/-- A wrong description, for a fixed input. -/
lemma sum_cfT₃_le (hμ : IsPMF μ) {q : U → V → ℝ} (hq : IsChannel q)
    (hqd : ∀ a c, dist μ (fun z => (z.1.1.2, z.2)) (a, c) = dist μ (fun z => z.1.1.2) a * q a c)
    (x : Fin n → X) (u : Fin n → U) (y : Fin n → Y) :
    ∑ v, seqChan q n u v * ind (cfT₂ μ n ε x u v y) ≤
      ind ((fun i => ((u i, y i), x i)) ∈ robustTypicalSet (dist μ cfF₄) n ε) *
        exp (-(n * (cfGapV μ - ε * cfErrV μ))) := by
  classical
  by_cases hT : (fun i => ((u i, y i), x i)) ∈ robustTypicalSet (dist μ cfF₄) n ε
  · rw [ind_of_pos hT, one_mul]
    have hcomp : ∀ (x : Fin n → X) (u : Fin n → U) (y : Fin n → Y) (v : Fin n → V),
        cfT₂ μ n ε x u v y →
        (fun i => (((u i, y i), x i), v i)) ∈ robustTypicalSet (dist μ cfF₃) n ε := by
      intro x u y v hv
      have h := comp_mem_robustTypicalSet hv
        fun t : (U × V × Y) × X => (((t.1.1, t.1.2.2), t.2), t.1.2.1)
      rw [← dist_comp_eq] at h
      exact h
    have h := sum_fresh_point (hμ.dist cfF₃) (K := U) (fun t : (U × Y) × X => t.1.1) (κ := q)
      (fun k t => by
        have e₁ : dist (dist μ cfF₃) (fun z : ((U × Y) × X) × V => (z.1.1.1, z.2)) =
            dist μ fun z => (z.1.1.2, z.2) := (dist_comp_eq _ _ _).symm
        have e₂ : dist (dist μ cfF₃) (fun z : ((U × Y) × X) × V => z.1.1.1) =
            dist μ fun z => z.1.1.2 := (dist_comp_eq _ _ _).symm
        rw [e₁, e₂]
        exact hqd k t) hq (n := n) (ε := ε)
      (fun r t => cfT₂ μ n ε (fun i => (r i).2) (fun i => (r i).1.1) t (fun i => (r i).1.2))
      (fun r t ht => hcomp _ _ _ t ht) (fun i => ((u i, y i), x i))
    refine h.trans (le_of_eq ?_)
    congr 2
    simp only [cfGapV, cfErrV, entropyRV_dist]
    rfl
  · rw [ind_of_neg hT, zero_mul]
    refine le_of_eq (sum_eq_zero fun v _ => ?_)
    have : ¬ cfT₂ μ n ε x u v y := by
      intro hv
      have h := comp_mem_robustTypicalSet hv fun t : (U × V × Y) × X => ((t.1.1, t.1.2.2), t.2)
      rw [← dist_comp_eq] at h
      exact hT h
    rw [ind_of_neg this, mul_zero]

end Fresh

section Bound

variable {n M L K : ℕ} [NeZero M] [NeZero L] [NeZero K] {ε δ : ℝ}

/-- The law of `((X₁, Y₁), Ŷ₁)` satisfies the hypotheses of `tilt_le`. -/
lemma cfLaw_tilt (hτ : IsChannel τ) (a : U × S) (c : V) :
    dist (cfLaw p p₁ W τ) cfFJ (a, c) = dist (dist (cfLaw p p₁ W τ) cfFJ) Prod.fst a * τ a c := by
  have h : dist (cfLaw p p₁ W τ) cfFJ =
      jointOf (dist (jointOf (prodDist p p₁) W) fun t => (t.1.2, t.2.2)) τ :=
    dist_jointOf_map (Q := jointOf (prodDist p p₁) W) (fun t => (t.1.2, t.2.2)) τ
  rw [h, dist_jointOf_fst hτ]
  rfl

/-- The rate of the covering is nonnegative. -/
lemma cfGapC_nonneg {μ : ((X × U) × (Y × S)) × V → ℝ} (hμ : IsPMF μ) : 0 ≤ cfGapC μ := by
  have h := condMutualInfo_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.2) (fun z => z.1.2.2)
    (fun z => z.1.1.2)
  rw [condMutualInfo_eq_entropies hμ] at h
  have e : H[pair (pair (fun z : ((X × U) × (Y × S)) × V => z.1.1.2) fun z => z.1.2.2) fun z => z.2
    ;
      μ] = H[cfFJ ; μ] := rfl
  rw [e] at h
  have e₁ : H[pair (fun z : ((X × U) × (Y × S)) × V => z.1.1.2) fun z => z.2 ; μ] =
      H[fun z => (z.1.1.2, z.2) ; μ] := rfl
  have e₂ : H[pair (fun z : ((X × U) × (Y × S)) × V => z.1.1.2) fun z => z.1.2.2 ; μ] =
      H[fun z => (z.1.1.2, z.1.2.2) ; μ] := rfl
  rw [e₁, e₂] at h
  simp only [cfGapC]
  linarith

lemma cfErrC_nonneg {μ : ((X × U) × (Y × S)) × V → ℝ} (hμ : IsPMF μ) : 0 ≤ cfErrC μ := by
  simp only [cfErrC]
  have h₁ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2))
  have h₂ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.2))
  have h₃ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.1.1.2)
  have h₄ := entropyRV_nonneg hμ (cfFJ : ((X × U) × (Y × S)) × V → _)
  linarith

/-- **The random coding bound of compress–forward, in terms of the gaps.** -/
theorem exists_cfBlock_gaps [Nonempty V] (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W)
    (hτ : IsChannel τ) (hε : 0 ≤ ε) (hδ : 0 < δ) :
    ∃ C : CFBlock M L n X U Y S, C.avgErr (relaySeq W n) ≤
      (1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε)) +
      ((L : ℝ) - 1) * exp (-(n * (cfGapU (cfLaw p p₁ W τ) - ε * cfErrU (cfLaw p p₁ W τ)))) +
      (δ + exp (-(exp (-(n * (cfGapC (cfLaw p p₁ W τ) + ε * cfErrC (cfLaw p p₁ W τ)))) * K)) +
      ((1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε)) +
        (1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε)) / δ) +
      ((M : ℝ) - 1) * (exp (-(n * (cfGapX (cfLaw p p₁ W τ) - ε * cfErrX (cfLaw p p₁ W τ)))) +
        (K : ℝ) / L * (exp (-(n * (cfGapW (cfLaw p p₁ W τ) - ε * cfErrW (cfLaw p p₁ W τ)))) *
          exp (-(n * (cfGapV (cfLaw p p₁ W τ) - ε * cfErrV (cfLaw p p₁ W τ))))))) := by
  classical
  have hμ := cfLaw_isPMF hp hp₁ hW hτ
  set μ := cfLaw p p₁ W τ with hμd
  obtain ⟨hmx, hmu⟩ := cfLaw_marg (p := p) (p₁ := p₁) (W := W) (τ := τ) hp hp₁ hW hτ
  -- the law of the descriptions given the input of the relay
  obtain ⟨q, hq, hqd⟩ := exists_kernel (hμ.dist fun z => (z.1.1.2, z.2))
  have hqd' : ∀ a c, dist μ (fun z => (z.1.1.2, z.2)) (a, c) =
      dist μ (fun z => z.1.1.2) a * q a c := by
    intro a c
    have h := hqd a c
    rwa [← dist_comp_eq] at h
  set T₁ := cfT₁ μ n ε with hT₁
  set T := cfT₂ (X := X) μ n ε with hT
  set Tj := cfTj μ n ε with hTj
  have hTω : ∀ ω ∈ robustTypicalSet μ n ε, T (fun i => (ω i).1.1.1) (fun i => (ω i).1.1.2)
      (fun i => (ω i).2) (fun i => (ω i).1.2.1) := fun ω hω => comp_mem_robustTypicalSet hω cfF₂
  have hTjω : ∀ ω ∈ robustTypicalSet μ n ε, Tj (fun i => (ω i).1.1.2) (fun i => (ω i).1.2.2)
      (fun i => (ω i).2) := fun ω hω => comp_mem_robustTypicalSet hω cfFJ
  have hT₁ω : ∀ ω ∈ robustTypicalSet μ n ε, T₁ (fun i => (ω i).1.1.2) (fun i => (ω i).1.2.1) :=
    fun ω hω => comp_mem_robustTypicalSet hω cfF₁
  set y := exp (-(n * (cfGapC μ + ε * cfErrC μ))) with hy
  have hy1 : y ≤ 1 := by
    refine exp_le_one_iff.mpr ?_
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (add_nonneg (cfGapC_nonneg hμ)
      (mul_nonneg hε (cfErrC_nonneg hμ)))
    linarith
  have hyt : ∀ (u : Fin n → U) (s : Fin n → S) (v : Fin n → V), Tj u s v →
      seqChan τ n (fun i => (u i, s i)) v * y ≤ seqChan q n u v := by
    intro u s v hv
    have h := tilt_le (hμ.dist cfFJ) (τ := τ) (q := q) (cfLaw_tilt hτ)
      (fun a c => by
        have e₁ : dist (dist μ cfFJ) (fun z : (U × S) × V => (z.1.1, z.2)) =
            dist μ fun z => (z.1.1.2, z.2) := (dist_comp_eq _ _ _).symm
        have e₂ : dist (dist μ cfFJ) (fun z : (U × S) × V => z.1.1) =
            dist μ fun z => z.1.1.2 := (dist_comp_eq _ _ _).symm
        rw [e₁, e₂]
        exact hqd' a c) hv
    refine le_trans (le_of_eq ?_) h
    congr 3
    simp only [entropyRV_dist]
    rfl
  have hcov := sum_cover_le (K := K) hp hp₁ hW hq hτ (ε := ε) hδ hy1 T Tj hTω hTjω hyt
  have hA : ∑ x, iidPMF p n x * ∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ *
      ind (¬ T₁ u ζ.1) ≤ 1 - prob (iidPMF μ n) (robustTypicalSet μ n ε) := by
    have h := sum_cf_le (V := V) (S := S) (Y := Y) (τ := τ) hp hp₁ hW hτ (ε := ε) (n := n)
      (fun _ u ζ _ => ¬ T₁ u ζ.1) (fun ω hω => not_not.mpr (hT₁ω ω hω))
    refine le_trans (le_of_eq ?_) h
    rw [sum_inner_swap]
    refine sum_congr rfl fun u _ => congrArg _ (sum_congr rfl fun x _ => congrArg _
      (sum_congr rfl fun ζ _ => congrArg _ ?_))
    rw [← sum_mul, (seqChan_isChannel hτ n _).sum_eq_one, one_mul]
  have h₃ : ∀ (u : Fin n → U) (y' : Fin n → Y), ∑ x, iidPMF p n x * ∑ v, seqChan q n u v *
      ind (T x u v y') ≤ exp (-(n * (cfGapW μ - ε * cfErrW μ))) *
        exp (-(n * (cfGapV μ - ε * cfErrV μ))) := by
    intro u y'
    calc _ ≤ ∑ x, iidPMF p n x * (ind ((fun i => ((u i, y' i), x i)) ∈
          robustTypicalSet (dist μ cfF₄) n ε) * exp (-(n * (cfGapV μ - ε * cfErrV μ)))) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (sum_cfT₃_le hμ hq hqd' x u y')
            ((iidPMF_isPMF hp n).nonneg x)
      _ = (∑ x, iidPMF p n x * ind ((fun i => ((u i, y' i), x i)) ∈
          robustTypicalSet (dist μ cfF₄) n ε)) * exp (-(n * (cfGapV μ - ε * cfErrV μ))) := by
          rw [sum_mul]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_cfT₄_le hμ hmx u y') (exp_pos _).le
  obtain ⟨C, hC⟩ := exists_cfBlock_le (M := M) (L := L) (K := K) (T₁ := T₁) (T := T)
    (Good := cfGood p W T Tj δ) hp hp₁ hq hW (fun y' => sum_cfT₁_le hμ hmu y')
    (fun u v y' => sum_cfT₂_le hμ hmx u v y') h₃ hA
  refine ⟨C, hC.trans ?_⟩
  have hM : (0 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
    linarith
  have hcov' : cfCov p p₁ W q T (cfGood p W T Tj δ) K ≤ _ := hcov
  linarith

end Bound

section Rates

lemma cfErrU_nonneg {μ : ((X × U) × (Y × S)) × V → ℝ} (hμ : IsPMF μ) : 0 ≤ cfErrU μ := by
  simp only [cfErrU]
  have h₁ := entropyRV_nonneg hμ (cfF₁ : ((X × U) × (Y × S)) × V → _)
  have h₂ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.1.2.1)
  have h₃ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.1.1.2)
  linarith

lemma cfErrX_nonneg {μ : ((X × U) × (Y × S)) × V → ℝ} (hμ : IsPMF μ) : 0 ≤ cfErrX μ := by
  simp only [cfErrX]
  have h₁ := entropyRV_nonneg hμ (cfF₂ : ((X × U) × (Y × S)) × V → _)
  have h₂ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.2, z.1.2.1))
  have h₃ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.1.1.1)
  linarith

lemma cfErrV_nonneg {μ : ((X × U) × (Y × S)) × V → ℝ} (hμ : IsPMF μ) : 0 ≤ cfErrV μ := by
  simp only [cfErrV]
  have h₁ := entropyRV_nonneg hμ (cfF₃ : ((X × U) × (Y × S)) × V → _)
  have h₂ := entropyRV_nonneg hμ (cfF₄ : ((X × U) × (Y × S)) × V → _)
  have h₃ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.2))
  have h₄ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.1.1.2)
  linarith

lemma cfErrW_nonneg {μ : ((X × U) × (Y × S)) × V → ℝ} (hμ : IsPMF μ) : 0 ≤ cfErrW μ := by
  simp only [cfErrW]
  have h₁ := entropyRV_nonneg hμ (cfF₄ : ((X × U) × (Y × S)) × V → _)
  have h₂ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.1))
  have h₃ := entropyRV_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.1.1.1)
  linarith

/-- **Codes for one block of compress–forward**, for rates that satisfy the conditions of the notes,
pages 17-42 to 17-45. -/
theorem eventually_cfBlock [Nonempty V] (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W)
    (hτ : IsChannel τ) {R₀ R₁ R₂ : ℝ} (hR₂ : 0 ≤ R₂)
    (hU : R₁ = 0 ∨ R₁ < cfGapU (cfLaw p p₁ W τ)) (hX : R₀ < cfGapX (cfLaw p p₁ W τ))
    (hC : cfGapC (cfLaw p p₁ W τ) < R₂)
    (hV : R₀ + R₂ - R₁ < cfGapW (cfLaw p p₁ W τ) + cfGapV (cfLaw p p₁ W τ)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ C : CFBlock ⌈exp (n * R₀)⌉₊ ⌈exp (n * R₁)⌉₊ n X U Y S,
      C.avgErr (relaySeq W n) ≤ δ := by
  classical
  have hμ := cfLaw_isPMF hp hp₁ hW hτ
  set μ := cfLaw p p₁ W τ with hμd
  set γ := min (min (if R₁ = 0 then 1 else cfGapU μ - R₁) (cfGapX μ - R₀))
    (min (R₂ - cfGapC μ) (cfGapW μ + cfGapV μ - (R₀ + R₂ - R₁))) with hγ
  have hγpos : 0 < γ := by
    refine lt_min (lt_min ?_ (by linarith)) (lt_min (by linarith) (by linarith))
    split_ifs with h
    · norm_num
    · have := hU.resolve_left h
      linarith
  have hγU : R₁ ≠ 0 → γ ≤ cfGapU μ - R₁ := fun h => by
    have := (min_le_left _ _).trans (min_le_left _ _) (a := γ) |>.trans_eq (ite_eq_right h)
    exact this
  have hγX : γ ≤ cfGapX μ - R₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hγC : γ ≤ R₂ - cfGapC μ := (min_le_right _ _).trans (min_le_left _ _)
  have hγV : γ ≤ cfGapW μ + cfGapV μ - (R₀ + R₂ - R₁) := (min_le_right _ _).trans (min_le_right _ _)
  have hEU := cfErrU_nonneg hμ
  have hEX := cfErrX_nonneg hμ
  have hEV := cfErrV_nonneg hμ
  have hEW := cfErrW_nonneg hμ
  have hEC := cfErrC_nonneg hμ
  -- a small `ε`
  set E := cfErrU μ + cfErrX μ + cfErrV μ + cfErrW μ + cfErrC μ + 1 with hE
  have hEpos : 0 < E := by linarith
  set ε := γ / 2 / E with hε
  have hεpos : 0 < ε := by positivity
  have hεE : ε * E = γ / 2 := by
    rw [hε]
    field_simp
  have heU : ε * cfErrU μ ≤ γ / 2 := by
    rw [← hεE]
    exact mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have heX : ε * cfErrX μ ≤ γ / 2 := by
    rw [← hεE]
    exact mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have heVW : ε * (cfErrV μ + cfErrW μ) ≤ γ / 2 := by
    rw [← hεE]
    exact mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have heC : ε * cfErrC μ ≤ γ / 2 := by
    rw [← hεE]
    exact mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  -- the limit of the bound
  have hδ₂ : 0 < δ / 2 := by positivity
  have hprob := tendsto_prob_robustTypicalSet hμ hεpos
  have hexp : Tendsto (fun n : ℕ => exp (-(n * (γ / 2)))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_nat (by positivity)
  have hlim : Tendsto (fun n : ℕ => (1 - prob (iidPMF μ n) (robustTypicalSet μ n ε)) *
      (2 + 1 / (δ / 2)) + 5 * exp (-(n * (γ / 2)))) atTop
        (𝓝 ((1 - 1) * (2 + 1 / (δ / 2)) + 5 * 0)) :=
    ((tendsto_const_nhds.sub hprob).mul_const _).add (hexp.const_mul _)
  have hlim' : ∀ᶠ n : ℕ in atTop, (1 - prob (iidPMF μ n) (robustTypicalSet μ n ε)) *
      (2 + 1 / (δ / 2)) + 5 * exp (-(n * (γ / 2))) < δ / 2 := by
    refine (tendsto_order.mp hlim).2 _ ?_
    simpa using hδ₂
  filter_upwards [hlim'] with n hn
  obtain ⟨C, hC'⟩ := exists_cfBlock_gaps (M := ⌈exp (n * R₀)⌉₊) (L := ⌈exp (n * R₁)⌉₊)
    (K := ⌈exp (n * R₂)⌉₊) (n := n) (p := p) (p₁ := p₁) (W := W) (τ := τ) hp hp₁ hW hτ hεpos.le hδ₂
  refine ⟨C, hC'.trans ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set e := exp (-(n * (γ / 2))) with he
  have he0 : 0 < e := exp_pos _
  have hM₁ : ∀ r : ℝ, ((⌈exp (n * r)⌉₊ : ℕ) : ℝ) - 1 ≤ exp (n * r) := fun r => by
    have := Nat.ceil_lt_add_one (exp_pos (n * r)).le
    linarith
  have hge : ∀ r : ℝ, exp (n * r) ≤ ((⌈exp (n * r)⌉₊ : ℕ) : ℝ) := fun r => Nat.le_ceil _
  -- the wrong state
  have t₁ : (((⌈exp (n * R₁)⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (cfGapU μ - ε * cfErrU μ))) ≤ e := by
    by_cases h0 : R₁ = 0
    · have : ((⌈exp (n * R₁)⌉₊ : ℕ) : ℝ) = 1 := by simp [h0]
      rw [this, sub_self, zero_mul]
      exact he0.le
    · refine (mul_le_mul_of_nonneg_right (hM₁ R₁) (exp_pos _).le).trans ?_
      rw [← exp_add, he]
      refine exp_le_exp.mpr ?_
      have h : γ / 2 ≤ cfGapU μ - R₁ - ε * cfErrU μ := by
        have := hγU h0
        linarith
      have h' := mul_le_mul_of_nonneg_left h hn0
      have e' : n * R₁ + -(n * (cfGapU μ - ε * cfErrU μ)) =
          -(n * (cfGapU μ - R₁ - ε * cfErrU μ)) := by ring
      rw [e']
      linarith
  -- the covering
  have t₂ : exp (-(exp (-(n * (cfGapC μ + ε * cfErrC μ))) * ((⌈exp (n * R₂)⌉₊ : ℕ) : ℝ))) ≤ e := by
    rw [he]
    refine exp_le_exp.mpr (neg_le_neg ?_)
    have h₁ : exp (n * (γ / 2)) ≤ exp (-(n * (cfGapC μ + ε * cfErrC μ))) *
        ((⌈exp (n * R₂)⌉₊ : ℕ) : ℝ) := by
      calc exp (n * (γ / 2)) ≤ exp (-(n * (cfGapC μ + ε * cfErrC μ))) * exp (n * R₂) := by
            rw [← exp_add]
            refine exp_le_exp.mpr ?_
            have h : γ / 2 ≤ R₂ - cfGapC μ - ε * cfErrC μ := by linarith
            have h' := mul_le_mul_of_nonneg_left h hn0
            have e' : -(n * (cfGapC μ + ε * cfErrC μ)) + n * R₂ =
                n * (R₂ - cfGapC μ - ε * cfErrC μ) := by ring
            rw [e']
            exact h'
        _ ≤ _ := mul_le_mul_of_nonneg_left (hge R₂) (exp_pos _).le
    have h₂ := add_one_le_exp ((n : ℝ) * (γ / 2))
    linarith
  -- the wrong message
  have hM0 : 0 ≤ ((⌈exp (n * R₀)⌉₊ : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ((⌈exp (n * R₀)⌉₊ : ℕ) : ℝ) := by exact_mod_cast NeZero.one_le
    linarith
  have t₃ : (((⌈exp (n * R₀)⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (cfGapX μ - ε * cfErrX μ))) ≤ e := by
    refine (mul_le_mul_of_nonneg_right (hM₁ R₀) (exp_pos _).le).trans ?_
    rw [← exp_add, he]
    refine exp_le_exp.mpr ?_
    have h : γ / 2 ≤ cfGapX μ - R₀ - ε * cfErrX μ := by linarith
    have h' := mul_le_mul_of_nonneg_left h hn0
    have e' : n * R₀ + -(n * (cfGapX μ - ε * cfErrX μ)) =
        -(n * (cfGapX μ - R₀ - ε * cfErrX μ)) := by ring
    rw [e']
    linarith
  -- the wrong message and the wrong description
  have hKL : ((⌈exp (n * R₂)⌉₊ : ℕ) : ℝ) / ((⌈exp (n * R₁)⌉₊ : ℕ) : ℝ) ≤
      2 * exp (n * R₂) * exp (-(n * R₁)) := by
    have hL0 : 0 < ((⌈exp (n * R₁)⌉₊ : ℕ) : ℝ) := by exact_mod_cast NeZero.pos _
    have hK : ((⌈exp (n * R₂)⌉₊ : ℕ) : ℝ) ≤ 2 * exp (n * R₂) := by
      have h₁ := hM₁ R₂
      have h₂ : 1 ≤ exp (n * R₂) := one_le_exp (mul_nonneg hn0 hR₂)
      linarith
    rw [div_le_iff₀ hL0]
    refine hK.trans ?_
    have h₃ : 2 * exp (n * R₂) = 2 * exp (n * R₂) * exp (-(n * R₁)) * exp (n * R₁) := by
      rw [mul_assoc (2 * exp (n * R₂)), ← exp_add]
      simp
    calc 2 * exp (n * R₂) = _ := h₃
      _ ≤ _ := mul_le_mul_of_nonneg_left (hge R₁) (by positivity)
  have t₄ : (((⌈exp (n * R₀)⌉₊ : ℕ) : ℝ) - 1) * (((⌈exp (n * R₂)⌉₊ : ℕ) : ℝ) /
      ((⌈exp (n * R₁)⌉₊ : ℕ) : ℝ) * (exp (-(n * (cfGapW μ - ε * cfErrW μ))) *
        exp (-(n * (cfGapV μ - ε * cfErrV μ))))) ≤ 2 * e := by
    calc _ ≤ exp (n * R₀) * ((2 * exp (n * R₂) * exp (-(n * R₁))) *
          (exp (-(n * (cfGapW μ - ε * cfErrW μ))) * exp (-(n * (cfGapV μ - ε * cfErrV μ))))) := by
          refine mul_le_mul (hM₁ R₀) (mul_le_mul_of_nonneg_right hKL (by positivity)) ?_
            (exp_pos _).le
          positivity
      _ = 2 * exp (n * R₀ + n * R₂ + -(n * R₁) + (-(n * (cfGapW μ - ε * cfErrW μ)) +
          -(n * (cfGapV μ - ε * cfErrV μ)))) := by
          simp only [exp_add]
          ring
      _ ≤ _ := by
          rw [he]
          refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
          have h : γ / 2 ≤ cfGapW μ + cfGapV μ - (R₀ + R₂ - R₁) - ε * (cfErrV μ + cfErrW μ) := by
            linarith
          have h' := mul_le_mul_of_nonneg_left h hn0
          have e' : n * R₀ + n * R₂ + -(n * R₁) + (-(n * (cfGapW μ - ε * cfErrW μ)) +
              -(n * (cfGapV μ - ε * cfErrV μ))) = -(n * (cfGapW μ + cfGapV μ - (R₀ + R₂ - R₁) -
                ε * (cfErrV μ + cfErrW μ))) := by ring
          rw [e']
          linarith
  have hcE : 0 ≤ 1 - prob (iidPMF μ n) (robustTypicalSet μ n ε) :=
    sub_nonneg.mpr (prob_le_one (iidPMF_isPMF hμ n) _)
  set cE := 1 - prob (iidPMF μ n) (robustTypicalSet μ n ε) with hcEd
  have hsum : (((⌈exp (n * R₀)⌉₊ : ℕ) : ℝ) - 1) * (exp (-(n * (cfGapX μ - ε * cfErrX μ))) +
      ((⌈exp (n * R₂)⌉₊ : ℕ) : ℝ) / ((⌈exp (n * R₁)⌉₊ : ℕ) : ℝ) *
        (exp (-(n * (cfGapW μ - ε * cfErrW μ))) * exp (-(n * (cfGapV μ - ε * cfErrV μ))))) ≤
      3 * e := by
    rw [mul_add]
    linarith
  have hexp₂ : cE * (2 + 1 / (δ / 2)) = cE + cE + cE / (δ / 2) := by ring
  rw [hexp₂] at hn
  linarith

end Rates

end InfoTheory
