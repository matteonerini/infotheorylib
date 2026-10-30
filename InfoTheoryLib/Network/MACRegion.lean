/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MutualInformation.Conditional
public import InfoTheoryLib.Probability.Channel
public import Mathlib.Analysis.Convex.Combination

/-!
# The rate regions of the multiple-access channel

For a product input distribution `p₁(x₁) p₂(x₂)` on a multiple-access channel `p(y | x₁, x₂)`, the
three mutual informations `I₁ = I(X₁; Y | X₂)`, `I₂ = I(X₂; Y | X₁)` and `I₃ = I(X₁, X₂; Y)`
define the pentagon `R₁ < I₁`, `R₂ < I₂`, `R₁ + R₂ < I₃` of (15.56)–(15.58). Since the inputs are
independent, `max (I₁, I₂) ≤ I₃ ≤ I₁ + I₂`.

The capacity region is the closure of the convex hull of the union of the pentagons
(Theorem 15.3.1), or, with a time-sharing variable `Q`, the closure of the set of rate pairs with
`R₁ ≤ I(X₁; Y | X₂, Q)`, `R₂ ≤ I(X₂; Y | X₁, Q)`, `R₁ + R₂ ≤ I(X₁, X₂; Y | Q)` (Theorem 15.3.4).
Lemma 15.3.1 relates the two: a rate pair strictly inside the region defined by a convex
combination of the vectors `(I₁, I₂, I₃)` is the same convex combination of points of the
pentagons. This uses `I₃ ≤ I₁ + I₂`, without which the lemma fails, (15.81)–(15.83).

## Main definitions

* `macJoint p₁ p₂ W`: the joint law `p₁(x₁) p₂(x₂) p(y | x₁, x₂)` of `((X₁, X₂), Y)`.
* `macInfo₁`, `macInfo₂`, `macInfo₁₂`: `I(X₁; Y | X₂)`, `I(X₂; Y | X₁)` and `I(X₁, X₂; Y)`.
* `macRateRegion W p₁ p₂`: **(15.56)–(15.58)** the pentagon of a product input distribution.
* `macRateRegions W`: the union of the pentagons over all product input distributions.
* `macRegion W`: **(15.89)** the rate pairs with `R₁ ≤ ∑_q p(q) I(X₁; Y | X₂, Q = q)`, … for a
  time-sharing variable `Q` with finitely many values.

## Main statements

* `macInfo₁_le_macInfo₁₂`, `macInfo₂_le_macInfo₁₂`, `macInfo₁₂_le_add`: (Section 15.3.3)
  `max (I₁, I₂) ≤ I₃ ≤ I₁ + I₂`.
* `exists_pentagon_decomp`: **Lemma 15.3.1** in the form we use.
* `sub_mem_convexHull_of_mem_macRegion`, `macRegion_subset_closure_convexHull`:
  **Theorem 15.3.3**, the region defined by mixtures of the mutual information vectors is in the
  closure of the convex hull of the pentagons.

## Implementation notes

The time-sharing variable `Q` takes the values `0, …, k - 1` with probabilities `q`, and given
`Q = i` the inputs are independent with laws `p₁ i` and `p₂ i`. We do not bound `k`
(Carathéodory's theorem gives `k ≤ 4`, Theorem 15.3.5). Rates are in nats.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 15.3.2 and
  15.3.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]

/-- The joint law `p₁(x₁) p₂(x₂) p(y | x₁, x₂)` of the inputs and the output of a multiple-access
channel with independent inputs. -/
def macJoint (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) : (α₁ × α₂) × β → ℝ :=
  jointOf (prodDist p₁ p₂) W

/-- `I(X₁; Y | X₂)` for the inputs `X₁ ∼ p₁`, `X₂ ∼ p₂`. -/
def macInfo₁ (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) : ℝ :=
  I[fun z : (α₁ × α₂) × β => z.1.1 : Prod.snd | fun z => z.1.2 ; macJoint p₁ p₂ W]

/-- `I(X₂; Y | X₁)` for the inputs `X₁ ∼ p₁`, `X₂ ∼ p₂`. -/
def macInfo₂ (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) : ℝ :=
  I[fun z : (α₁ × α₂) × β => z.1.2 : Prod.snd | fun z => z.1.1 ; macJoint p₁ p₂ W]

/-- `I(X₁, X₂; Y)` for the inputs `X₁ ∼ p₁`, `X₂ ∼ p₂`. -/
def macInfo₁₂ (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) : ℝ :=
  I[Prod.fst : Prod.snd ; macJoint p₁ p₂ W]

/-- **(15.56)–(15.58)** The pentagon `R₁ < I(X₁; Y | X₂)`, `R₂ < I(X₂; Y | X₁)`,
`R₁ + R₂ < I(X₁, X₂; Y)` of the product input distribution `p₁(x₁) p₂(x₂)`. -/
def macRateRegion (W : α₁ × α₂ → β → ℝ) (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | R.1 < macInfo₁ p₁ p₂ W ∧ R.2 < macInfo₂ p₁ p₂ W ∧ R.1 + R.2 < macInfo₁₂ p₁ p₂ W}

/-- The union of the pentagons (15.56)–(15.58) over all product input distributions. -/
def macRateRegions (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ R ∈ macRateRegion W p₁ p₂}

/-- **(15.89)** The rate pairs with `R₁ ≤ I(X₁; Y | X₂, Q)`, `R₂ ≤ I(X₂; Y | X₁, Q)` and
`R₁ + R₂ ≤ I(X₁, X₂; Y | Q)` for some time-sharing variable `Q` with law `q` on `{0, …, k - 1}` and
inputs independent given `Q`, with laws `p₁ i` and `p₂ i` given `Q = i`. -/
def macRegion (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k → ℝ) (p₁ : Fin k → α₁ → ℝ) (p₂ : Fin k → α₂ → ℝ),
    IsPMF q ∧ (∀ i, IsPMF (p₁ i)) ∧ (∀ i, IsPMF (p₂ i)) ∧
    R.1 ≤ ∑ i, q i * macInfo₁ (p₁ i) (p₂ i) W ∧ R.2 ≤ ∑ i, q i * macInfo₂ (p₁ i) (p₂ i) W ∧
    R.1 + R.2 ≤ ∑ i, q i * macInfo₁₂ (p₁ i) (p₂ i) W}

/-! ### The joint law -/

variable {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} {W : α₁ × α₂ → β → ℝ}

lemma macJoint_isPMF (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    IsPMF (macJoint p₁ p₂ W) :=
  jointOf_isPMF (hp₁.prodDist hp₂) hW

lemma dist_prodDist_fst {q : α₂ → ℝ} (hq : IsPMF q) (p : α₁ → ℝ) :
    dist (prodDist p q) Prod.fst = p := by
  funext a
  rw [dist_fst]
  simp [prodDist, ← mul_sum, hq.sum_eq_one]

lemma dist_prodDist_snd {p : α₁ → ℝ} (hp : IsPMF p) (q : α₂ → ℝ) :
    dist (prodDist p q) Prod.snd = q := by
  funext b
  rw [dist_snd]
  simp [prodDist, ← sum_mul, hp.sum_eq_one]

lemma dist_macJoint_inputs (hW : IsChannel W) :
    dist (macJoint p₁ p₂ W) Prod.fst = prodDist p₁ p₂ :=
  dist_jointOf_fst hW

lemma dist_macJoint_fst (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    dist (macJoint p₁ p₂ W) (fun z => z.1.1) = p₁ := by
  calc dist (macJoint p₁ p₂ W) (fun z => z.1.1)
      = dist (dist (macJoint p₁ p₂ W) Prod.fst) Prod.fst := dist_comp_eq _ Prod.fst Prod.fst
    _ = p₁ := by rw [dist_macJoint_inputs hW, dist_prodDist_fst hp₂]

lemma dist_macJoint_snd (hp₁ : IsPMF p₁) (hW : IsChannel W) :
    dist (macJoint p₁ p₂ W) (fun z => z.1.2) = p₂ := by
  calc dist (macJoint p₁ p₂ W) (fun z => z.1.2)
      = dist (dist (macJoint p₁ p₂ W) Prod.fst) Prod.snd := dist_comp_eq _ Prod.fst Prod.snd
    _ = p₂ := by rw [dist_macJoint_inputs hW, dist_prodDist_snd hp₁]

/-- The inputs are independent: `I(X₂; X₁) = 0`. -/
lemma mutualInfo_inputs_eq_zero (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    I[fun z : (α₁ × α₂) × β => z.1.2 : fun z => z.1.1 ; macJoint p₁ p₂ W] = 0 := by
  rw [mutualInfo_eq_zero_iff (macJoint_isPMF hp₁ hp₂ hW)]
  intro b a
  rw [dist_macJoint_fst hp₂ hW, dist_macJoint_snd hp₁ hW, dist_pair_swap]
  have : pair (fun z : (α₁ × α₂) × β => z.1.1) (fun z => z.1.2) = Prod.fst := rfl
  rw [this, dist_macJoint_inputs hW]
  simp [prodDist, mul_comm]

/-- The chain rule `I(X₁, X₂; Y) = I(Y; X₂) + I(X₁; Y | X₂)`. -/
lemma macInfo₁₂_eq_add₁ (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁₂ p₁ p₂ W =
      I[Prod.snd : fun z : (α₁ × α₂) × β => z.1.2 ; macJoint p₁ p₂ W] + macInfo₁ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  rw [macInfo₁₂, mutualInfo_comm hμ]
  have h := chain_rule_mutualInfo₂ hμ (Prod.snd : (α₁ × α₂) × β → β) (fun z => z.1.1)
    (fun z => z.1.2)
  have e : pair (fun z : (α₁ × α₂) × β => z.1.1) (fun z => z.1.2) = Prod.fst := rfl
  rw [e] at h
  rw [h, macInfo₁, condMutualInfo_comm hμ]

/-- The chain rule `I(X₁, X₂; Y) = I(Y; X₁) + I(X₂; Y | X₁)`. -/
lemma macInfo₁₂_eq_add₂ (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁₂ p₁ p₂ W =
      I[Prod.snd : fun z : (α₁ × α₂) × β => z.1.1 ; macJoint p₁ p₂ W] + macInfo₂ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  rw [macInfo₁₂, mutualInfo_comm hμ]
  have h := chain_rule_mutualInfo₂ hμ (Prod.snd : (α₁ × α₂) × β → β) (fun z => z.1.2)
    (fun z => z.1.1)
  have e : I[Prod.snd : pair (fun z : (α₁ × α₂) × β => z.1.2) (fun z => z.1.1) ;
      macJoint p₁ p₂ W] = I[Prod.snd : Prod.fst ; macJoint p₁ p₂ W] :=
    mutualInfo_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  rw [e] at h
  rw [h, macInfo₂, condMutualInfo_comm hμ]

lemma macInfo₁_nonneg (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    0 ≤ macInfo₁ p₁ p₂ W :=
  condMutualInfo_nonneg (macJoint_isPMF hp₁ hp₂ hW) _ _ _

lemma macInfo₂_nonneg (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    0 ≤ macInfo₂ p₁ p₂ W :=
  condMutualInfo_nonneg (macJoint_isPMF hp₁ hp₂ hW) _ _ _

/-- `I(X₁; Y | X₂) ≤ I(X₁, X₂; Y)`. -/
lemma macInfo₁_le_macInfo₁₂ (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁ p₁ p₂ W ≤ macInfo₁₂ p₁ p₂ W := by
  rw [macInfo₁₂_eq_add₁ hp₁ hp₂ hW]
  linarith [mutualInfo_nonneg (macJoint_isPMF hp₁ hp₂ hW) (Prod.snd : (α₁ × α₂) × β → β)
    (fun z => z.1.2)]

/-- `I(X₂; Y | X₁) ≤ I(X₁, X₂; Y)`. -/
lemma macInfo₂_le_macInfo₁₂ (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₂ p₁ p₂ W ≤ macInfo₁₂ p₁ p₂ W := by
  rw [macInfo₁₂_eq_add₂ hp₁ hp₂ hW]
  linarith [mutualInfo_nonneg (macJoint_isPMF hp₁ hp₂ hW) (Prod.snd : (α₁ × α₂) × β → β)
    (fun z => z.1.1)]

/-- **(Section 15.3.3)** For independent inputs, `I(X₁, X₂; Y) ≤ I(X₁; Y | X₂) + I(X₂; Y | X₁)`:
`I(X₂; Y | X₁) = I(X₂; Y, X₁) ≥ I(X₂; Y)`. -/
lemma macInfo₁₂_le_add (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁₂ p₁ p₂ W ≤ macInfo₁ p₁ p₂ W + macInfo₂ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  set X₁ : (α₁ × α₂) × β → α₁ := fun z => z.1.1
  set X₂ : (α₁ × α₂) × β → α₂ := fun z => z.1.2
  set Y : (α₁ × α₂) × β → β := Prod.snd
  -- `I(X₂; Y, X₁) = I(X₂; X₁) + I(X₂; Y | X₁) = I(X₂; Y | X₁)`.
  have h1 := chain_rule_mutualInfo₂ hμ X₂ Y X₁
  have h0 := mutualInfo_inputs_eq_zero hp₁ hp₂ hW
  -- `I(X₂; Y, X₁) = I(X₂; Y) + I(X₂; X₁ | Y) ≥ I(X₂; Y)`.
  have h2 : I[X₂ : pair Y X₁ ; macJoint p₁ p₂ W] = I[X₂ : pair X₁ Y ; macJoint p₁ p₂ W] :=
    mutualInfo_congr_right hμ X₂ Prod.swap Prod.swap_injective fun _ => rfl
  have h3 := chain_rule_mutualInfo₂ hμ X₂ X₁ Y
  have h4 := condMutualInfo_nonneg hμ X₂ X₁ Y
  have h5 := macInfo₁₂_eq_add₁ hp₁ hp₂ hW
  have h6 : I[Y : X₂ ; macJoint p₁ p₂ W] = I[X₂ : Y ; macJoint p₁ p₂ W] := mutualInfo_comm hμ _ _
  have h7 : macInfo₂ p₁ p₂ W = I[X₂ : Y | X₁ ; macJoint p₁ p₂ W] := rfl
  linarith

/-! ### Lemma 15.3.1 -/

/-- **Lemma 15.3.1, Theorem 15.3.3.** Let `(aᵢ, bᵢ, cᵢ)` be vectors with `cᵢ ≤ aᵢ + bᵢ` and `q` a
probability vector. A rate pair strictly inside the region `R₁ < ∑ qᵢ aᵢ`, `R₂ < ∑ qᵢ bᵢ`,
`R₁ + R₂ < ∑ qᵢ cᵢ` defined by the mixture of the vectors is the mixture `∑ qᵢ rᵢ` of points `rᵢ`
strictly inside the regions defined by the vectors. -/
theorem exists_pentagon_decomp {k : ℕ} {q : Fin k → ℝ} (hq : IsPMF q) {a b c : Fin k → ℝ}
    (habc : ∀ i, c i ≤ a i + b i) {R₁ R₂ : ℝ} (h₁ : R₁ < ∑ i, q i * a i)
    (h₂ : R₂ < ∑ i, q i * b i) (h₃ : R₁ + R₂ < ∑ i, q i * c i) :
    ∃ r₁ r₂ : Fin k → ℝ, (∀ i, r₁ i < a i ∧ r₂ i < b i ∧ r₁ i + r₂ i < c i) ∧
      ∑ i, q i * r₁ i = R₁ ∧ ∑ i, q i * r₂ i = R₂ := by
  set A := ∑ i, q i * a i
  set B := ∑ i, q i * b i
  set C := ∑ i, q i * c i
  have hD : 0 ≤ A + B - C := by
    have : A + B - C = ∑ i, q i * (a i + b i - c i) := by
      simp only [A, B, C, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
    rw [this]
    exact sum_nonneg fun i _ => mul_nonneg (hq.nonneg i) (by linarith [habc i])
  -- A point `(F, C - F)` of the dominant face of the mixture, strictly above `R`.
  set F := min A (max (C - B) ((R₁ + C - R₂) / 2))
  have hF1 : F ≤ A := min_le_left _ _
  have hF2 : C - B ≤ F := le_min (by linarith) (le_max_left _ _)
  have hF3 : R₁ < F := lt_min h₁ (lt_max_of_lt_right (by linarith))
  have hF4 : F < C - R₂ := (min_le_right _ _).trans_lt (max_lt (by linarith) (by linarith))
  -- It is the mixture of the points `(1 - θ) (aᵢ, cᵢ - aᵢ) + θ (cᵢ - bᵢ, bᵢ)` of the faces.
  set θ := (A - F) / (A + B - C)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hD
  have hθ1 : θ ≤ 1 := div_le_one_of_le₀ (by linarith) hD
  have hθ : θ * (A + B - C) = A - F := by
    rcases hD.lt_or_eq with hD' | hD'
    · exact div_mul_cancel₀ _ hD'.ne'
    · have : F = A := le_antisymm hF1 (by linarith)
      rw [← hD', this]
      ring
  have hsum := hq.sum_eq_one
  refine ⟨fun i => (1 - θ) * a i + θ * (c i - b i) - (F - R₁),
    fun i => (1 - θ) * (c i - a i) + θ * b i - (C - F - R₂), fun i => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have e : (1 - θ) * a i + θ * (c i - b i) - (F - R₁) = a i + θ * (c i - b i - a i) - (F - R₁) :=
      by ring
    have : θ * (c i - b i - a i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ0 (by linarith [habc i])
    dsimp only
    rw [e]
    linarith
  · have e : (1 - θ) * (c i - a i) + θ * b i - (C - F - R₂) =
        b i + (1 - θ) * (c i - a i - b i) - (C - F - R₂) := by ring
    have : (1 - θ) * (c i - a i - b i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [habc i])
    dsimp only
    rw [e]
    linarith
  · have e : (1 - θ) * a i + θ * (c i - b i) - (F - R₁) +
        ((1 - θ) * (c i - a i) + θ * b i - (C - F - R₂)) = c i - (F - R₁) - (C - F - R₂) := by
      ring
    dsimp only
    rw [e]
    linarith
  · have e : ∀ i, q i * ((1 - θ) * a i + θ * (c i - b i) - (F - R₁)) =
        (1 - θ) * (q i * a i) + θ * (q i * c i) - θ * (q i * b i) - (F - R₁) * q i :=
      fun i => by ring
    simp only [e, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsum]
    linear_combination -hθ
  · have e : ∀ i, q i * ((1 - θ) * (c i - a i) + θ * b i - (C - F - R₂)) =
        (1 - θ) * (q i * c i) - (1 - θ) * (q i * a i) + θ * (q i * b i) - (C - F - R₂) * q i :=
      fun i => by ring
    simp only [e, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsum]
    linear_combination hθ

/-- **Theorem 15.3.3.** If `R` is in the region (15.89), `R - (δ, δ)` is in the convex hull of the
pentagons (15.56)–(15.58), for every `δ > 0`. -/
theorem sub_mem_convexHull_of_mem_macRegion (hW : IsChannel W) {R : ℝ × ℝ}
    (hR : R ∈ macRegion W) {δ : ℝ} (hδ : 0 < δ) :
    (R.1 - δ, R.2 - δ) ∈ convexHull ℝ (macRateRegions W) := by
  obtain ⟨k, q, p₁, p₂, hq, hp₁, hp₂, h1, h2, h3⟩ := hR
  obtain ⟨r₁, r₂, hr, hs₁, hs₂⟩ := exists_pentagon_decomp hq
    (fun i => macInfo₁₂_le_add (hp₁ i) (hp₂ i) hW) (R₁ := R.1 - δ) (R₂ := R.2 - δ)
    (by linarith) (by linarith) (by linarith)
  have e : (R.1 - δ, R.2 - δ) = ∑ i, q i • (r₁ i, r₂ i) := by
    ext
    · simp [Prod.fst_sum, hs₁]
    · simp [Prod.snd_sum, hs₂]
  rw [e]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hq.nonneg i) hq.sum_eq_one
    fun i _ => subset_convexHull ℝ _ ⟨p₁ i, p₂ i, hp₁ i, hp₂ i, hr i⟩

/-- **Theorem 15.3.3.** The region (15.89) is in the closure of the convex hull of the pentagons. -/
theorem macRegion_subset_closure_convexHull (hW : IsChannel W) :
    macRegion W ⊆ closure (convexHull ℝ (macRateRegions W)) := by
  intro R hR
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 : Tendsto (fun k : ℕ => R.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.1 - 0)) :=
    tendsto_const_nhds.sub h
  have h2 : Tendsto (fun k : ℕ => R.2 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.2 - 0)) :=
    tendsto_const_nhds.sub h
  rw [sub_zero] at h1 h2
  exact mem_closure_of_tendsto (h1.prodMk_nhds h2)
    (Eventually.of_forall fun k => sub_mem_convexHull_of_mem_macRegion hW hR (by positivity))

/-- Each pentagon is in the region (15.89), with a constant time-sharing variable. -/
theorem macRateRegions_subset_macRegion : macRateRegions W ⊆ macRegion W := by
  rintro R ⟨p₁, p₂, hp₁, hp₂, h1, h2, h3⟩
  refine ⟨1, fun _ => 1, fun _ => p₁, fun _ => p₂, ⟨fun _ => zero_le_one, by simp⟩,
    fun _ => hp₁, fun _ => hp₂, ?_, ?_, ?_⟩ <;> simp <;> linarith

end InfoTheory
