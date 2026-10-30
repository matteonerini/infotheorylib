/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Conditional
public import InfoTheoryLib.Entropy.Basic

/-!
# Conditional entropy

## Main definitions

* `condEntropyAt μ Y X x`: the entropy `H(Y | X = x)` of the conditional distribution.
* `condEntropy μ Y X`: the conditional entropy `H(Y | X) = ∑ₓ p(x) H(Y | X = x)`, with notation
  `H[Y | X ; μ]`.

## Main statements

* `chain_rule`: `H(X, Y) = H(X) + H(Y | X)`.
* `chain_rule_cond`: `H(X, Y | Z) = H(X | Z) + H(Y | X, Z)`.
* `condEntropy_eq_expect`: `H(Y | X) = -E log p(Y | X)`.

## Notation

* `H[Y | X ; μ]`: the conditional entropy of `Y` given `X` (scoped in `InfoTheory`).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- The entropy `H(Y | X = x)` of the conditional distribution `p(· | x)`. -/
def condEntropyAt (μ : Ω → ℝ) (Y : Ω → β) (X : Ω → α) (x : α) : ℝ :=
  entropy (condDist μ Y X x)

/-- **Definition (2.10).** The conditional entropy `H(Y|X) = ∑ₓ p(x) H(Y | X = x)`. -/
def condEntropy (μ : Ω → ℝ) (Y : Ω → β) (X : Ω → α) : ℝ :=
  ∑ x, dist μ X x * condEntropyAt μ Y X x

/-- `H[Y | X ; μ]` is the conditional entropy `H(Y|X)`. -/
scoped notation3:max "H[" Y " | " X " ; " μ "]" => condEntropy μ Y X

/-- `H(Y|X) ≥ 0`. -/
lemma condEntropy_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) :
    0 ≤ H[Y | X ; μ] := by
  refine sum_nonneg fun x _ => ?_
  rcases (dist_nonneg hμ X x).eq_or_lt with h | h
  · rw [← h, zero_mul]
  · exact mul_nonneg h.le (entropy_nonneg (condDist_isPMF hμ Y X h.ne'))

/-- (2.11) `H(Y|X) = -∑ₓ p(x) ∑ᵧ p(y|x) log p(y|x)`. -/
lemma condEntropy_eq_sum_cond (μ : Ω → ℝ) (Y : Ω → β) (X : Ω → α) :
    H[Y | X ; μ] = -∑ x, dist μ X x * ∑ y, condDist μ Y X x y * log (condDist μ Y X x y) := by
  simp [condEntropy, condEntropyAt, entropy, sum_neg_distrib]

/-- (2.12) `H(Y|X) = -∑ₓ ∑ᵧ p(x, y) log p(y|x)`. -/
lemma condEntropy_eq_sum_joint {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) :
    H[Y | X ; μ] = -∑ x, ∑ y, dist μ (pair X Y) (x, y) * log (condDist μ Y X x y) := by
  rw [condEntropy_eq_sum_cond]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [← mul_assoc, dist_mul_condDist hμ]

/-- (2.13) `H(Y|X) = -E log p(Y|X)`. -/
lemma condEntropy_eq_expect {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) :
    H[Y | X ; μ] = -∑ ω, μ ω * log (condDist μ Y X (X ω) (Y ω)) := by
  rw [condEntropy_eq_sum_joint hμ, ← Fintype.sum_prod_type',
    sum_dist_mul μ (pair X Y) (fun z => log (condDist μ Y X z.1 z.2))]
  rfl

/-- **Theorem 2.2.1 (Chain rule).** `H(X, Y) = H(X) + H(Y|X)`. -/
theorem chain_rule {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[pair X Y ; μ] = H[X ; μ] + H[Y | X ; μ] := by
  rw [jointEntropy_eq_expect, entropyRV_eq, condEntropy_eq_expect hμ, ← neg_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun ω _ => ?_
  rcases (hμ.nonneg ω).eq_or_lt with h | h
  · simp [← h]
  · rw [log_dist_pair_eq hμ X Y h]; ring

lemma condEntropy_eq_sub {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α) :
    H[Y | X ; μ] = H[pair X Y ; μ] - H[X ; μ] := by
  rw [chain_rule hμ]; ring

/-- Conditioning on an injective function of `X` is the same as conditioning on `X`. -/
lemma condEntropy_comp_right_injective {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α)
    {f : α → γ} (hf : Function.Injective f) : H[Y | f ∘ X ; μ] = H[Y | X ; μ] := by
  have h : H[pair (f ∘ X) Y ; μ] = H[pair X Y ; μ] :=
    entropyRV_eq_of_injective μ (Prod.map f id) (hf.prodMap Function.injective_id)
      (fun _ => rfl)
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ, entropyRV_comp_injective μ X hf, h]

/-- The conditional entropy of an injective function of `Y` equals that of `Y`. -/
lemma condEntropy_comp_left_injective {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (X : Ω → α)
    {f : β → γ} (hf : Function.Injective f) : H[f ∘ Y | X ; μ] = H[Y | X ; μ] := by
  have h : H[pair X (f ∘ Y) ; μ] = H[pair X Y ; μ] :=
    entropyRV_eq_of_injective μ (Prod.map id f) (Function.injective_id.prodMap hf)
      (fun _ => rfl)
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ, h]

/-- `H(Y | X)` only depends on `X` up to injective relabelling. -/
lemma condEntropy_congr_right {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) {X : Ω → α}
    {X' : Ω → γ} (f : α → γ) (hf : Function.Injective f) (h : ∀ ω, X' ω = f (X ω)) :
    H[Y | X' ; μ] = H[Y | X ; μ] := by
  rw [show X' = f ∘ X from funext h]; exact condEntropy_comp_right_injective hμ Y X hf

/-- `H(Y | X)` only depends on `Y` up to injective relabelling. -/
lemma condEntropy_congr_left {μ : Ω → ℝ} (hμ : IsPMF μ) {Y : Ω → β} {Y' : Ω → γ} (X : Ω → α)
    (f : β → γ) (hf : Function.Injective f) (h : ∀ ω, Y' ω = f (Y ω)) :
    H[Y' | X ; μ] = H[Y | X ; μ] := by
  rw [show Y' = f ∘ Y from funext h]; exact condEntropy_comp_left_injective hμ Y X hf

/-- Conditioning on a constant does nothing: `H(Y | c) = H(Y)`. -/
lemma condEntropy_const {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : Ω → β) (c : α) :
    H[Y | (fun _ => c) ; μ] = H[Y ; μ] := by
  rw [condEntropy_eq_sub hμ, entropyRV_const hμ, sub_zero]
  exact entropyRV_eq_of_injective μ (fun y => (c, y)) (fun _ _ h => (Prod.mk.inj h).2)
    (fun _ => rfl)

/-- **Corollary (2.21).** `H(X, Y | Z) = H(X|Z) + H(Y|X, Z)`. -/
theorem chain_rule_cond {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    H[pair X Y | Z ; μ] = H[X | Z ; μ] + H[Y | pair X Z ; μ] := by
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  have : H[pair Z (pair X Y) ; μ] = H[pair (pair X Z) Y ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (α × γ) × β => (t.1.2, t.1.1, t.2))
      (fun a b h => by
        obtain ⟨⟨a1, a2⟩, a3⟩ := a; obtain ⟨⟨b1, b2⟩, b3⟩ := b
        simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl)
  rw [this, entropyRV_pair_comm μ Z X]; ring

/-- **Remark (after Example 2.2.1).** `H(X) - H(X|Y) = H(Y) - H(Y|X)`. -/
lemma entropy_sub_condEntropy_symm {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[X ; μ] - H[X | Y ; μ] = H[Y ; μ] - H[Y | X ; μ] := by
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ, entropyRV_pair_comm μ Y X]; ring

/-- `H(f(X) | X) = 0`. -/
lemma condEntropy_comp_self {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (f : α → β) :
    H[f ∘ X | X ; μ] = 0 := by
  rw [condEntropy_eq_sub hμ, sub_eq_zero]
  exact entropyRV_eq_of_injective μ (fun a => (a, f a))
    (fun a b h => (Prod.mk.inj h).1) (fun _ => rfl)

/-- The entropy of a function of `X` is at most the entropy of `X`: `H(f(X)) ≤ H(X)`. -/
lemma entropyRV_comp_le {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (f : α → β) :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have h1 := chain_rule hμ X (f ∘ X)
  have h2 := chain_rule hμ (f ∘ X) X
  rw [condEntropy_comp_self hμ, add_zero, entropyRV_pair_comm] at h1
  linarith [condEntropy_nonneg hμ X (f ∘ X)]

/-- `H(X | X) = 0`, used in (2.42). -/
lemma condEntropy_self {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) : H[X | X ; μ] = 0 :=
  condEntropy_comp_self hμ X id

/-- `H(Y | X)` depends only on the joint law of `(X, Y)`. -/
lemma condEntropy_eq_of_dist_pair_eq {Ω' : Type*} [Fintype Ω'] {μ : Ω → ℝ} {ν : Ω' → ℝ}
    (hμ : IsPMF μ) (hν : IsPMF ν) {X : Ω → α} {Y : Ω → β} {X' : Ω' → α} {Y' : Ω' → β}
    (h : dist μ (pair X Y) = dist ν (pair X' Y')) : H[Y | X ; μ] = H[Y' | X' ; ν] := by
  have hX : dist μ X = dist ν X' := by
    funext x; rw [← sum_dist_pair_right μ X Y, ← sum_dist_pair_right ν X' Y', h]
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hν, entropyRV, entropyRV, entropyRV, entropyRV,
    h, hX]

end InfoTheory
