/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.ChainRule
public import InfoTheoryLib.MutualInformation.Conditional

/-!
# Bounds on entropy

## Main statements

* `entropy_le_log_card`: `H(X) ≤ log |𝒳|`, with equality iff `X` is uniform
  (`entropy_eq_log_card_iff`).
* `condEntropy_le_entropy`: conditioning reduces entropy, `H(X | Y) ≤ H(X)`, with equality iff
  `X` and `Y` are independent (`condEntropy_eq_entropy_iff`).
* `entropy_prefixRV_le_sum`: the independence bound `H(X₁, …, Xₙ) ≤ ∑ᵢ H(Xᵢ)`, with equality iff
  the `Xᵢ` are independent (`entropy_prefixRV_eq_sum_iff`).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006],
  Theorems 2.6.4, 2.6.5 and 2.6.6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Theorem 2.6.4.** `H(X) ≤ log |𝒳|`. -/
theorem entropy_le_log_card {p : α → ℝ} (hp : IsPMF p) : entropy p ≤ log (Fintype.card α) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  have := relEntropyReal_nonneg hp uniformPMF_isPMF
    (fun x hx => absurd hx (by simp [uniformPMF, Fintype.card_ne_zero]))
  rw [relEntropyReal_uniform hp] at this
  linarith

/-- **Theorem 2.6.4 (equality case).** `H(X) = log |𝒳|` iff `X` is uniformly distributed. -/
theorem entropy_eq_log_card_iff {p : α → ℝ} (hp : IsPMF p) :
    entropy p = log (Fintype.card α) ↔ p = uniformPMF α := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  rw [← relEntropyReal_eq_zero_iff hp uniformPMF_isPMF
    (fun x hx => absurd hx (by simp [uniformPMF, Fintype.card_ne_zero])),
    relEntropyReal_uniform hp]
  constructor <;> intro h <;> linarith

/-- **Theorem 2.6.4** for a random variable: `H(X) ≤ log |𝒳|`. -/
theorem entropyRV_le_log_card {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) :
    H[X ; μ] ≤ log (Fintype.card α) :=
  entropy_le_log_card (hμ.dist X)

/-- **Theorem 2.6.5 (Conditioning reduces entropy).** `H(X|Y) ≤ H(X)`. -/
theorem condEntropy_le_entropy {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[X | Y ; μ] ≤ H[X ; μ] := by
  have := mutualInfo_nonneg hμ X Y
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ] at this
  linarith

/-- **Theorem 2.6.5 (equality case).** `H(X|Y) = H(X)` iff `X` and `Y` are independent. -/
theorem condEntropy_eq_entropy_iff {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[X | Y ; μ] = H[X ; μ] ↔ IndepRV μ X Y := by
  rw [← mutualInfo_eq_zero_iff hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
  constructor <;> intro h <;> linarith

/-- Conditioning reduces conditional entropy: `H(X | Y, Z) ≤ H(X | Z)`. -/
theorem condEntropy_le_condEntropy {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : H[X | pair Y Z ; μ] ≤ H[X | Z ; μ] := by
  have := condMutualInfo_nonneg hμ X Y Z
  rw [condMutualInfo] at this
  linarith

/-- **Theorem 2.6.6 (Independence bound on entropy).** `H(X₁, …, Xₙ) ≤ ∑ᵢ H(Xᵢ)`. -/
theorem entropy_prefixRV_le_sum {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (n : ℕ) :
    H[prefixRV X n ; μ] ≤ ∑ i ∈ range n, H[X i ; μ] := by
  rw [chain_rule_entropy hμ]
  exact sum_le_sum fun i _ => condEntropy_le_entropy hμ _ _

/-- **Theorem 2.6.6 (equality case).** `H(X₁, …, Xₙ) = ∑ᵢ H(Xᵢ)` iff the `Xᵢ` are independent. -/
theorem entropy_prefixRV_eq_sum_iff {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (n : ℕ) :
    H[prefixRV X n ; μ] = ∑ i ∈ range n, H[X i ; μ] ↔ IndepFamily μ X n := by
  rw [chain_rule_entropy hμ, sum_eq_sum_iff_of_le (fun i _ => condEntropy_le_entropy hμ _ _),
    indepFamily_iff hμ]
  refine forall₂_congr fun i _ => ?_
  rw [condEntropy_eq_entropy_iff hμ]
  exact ⟨IndepRV.symm, IndepRV.symm⟩

/-- An entropy bound for a pmf supported on a set `S`: `H(p) ≤ log |S|`. -/
lemma entropy_le_log_card_of_support {p : α → ℝ} (hp : IsPMF p) (S : Finset α)
    (hS : ∀ x ∉ S, p x = 0) : entropy p ≤ log #S := by
  have hsum : ∀ f : ℝ → ℝ, f 0 = 0 → ∑ x, f (p x) = ∑ x : S, f (p x) := by
    intro f hf
    rw [← sum_subset (subset_univ S) (fun x _ hx => by rw [hS x hx, hf]), ← sum_coe_sort]
  have hpS : IsPMF (fun x : S => p x) :=
    ⟨fun x => hp.nonneg x, by
      have := hsum id rfl
      simp only [id] at this
      rw [← this]; exact hp.sum_eq_one⟩
  have := entropy_le_log_card hpS
  rw [Fintype.card_coe] at this
  rw [entropy_eq_sum_negMulLog, hsum negMulLog negMulLog_zero]
  rwa [entropy_eq_sum_negMulLog] at this

/-- Conditioning on less information increases the conditional entropy:
`H(X | Y) ≤ H(X | h(Y))`. -/
lemma condEntropy_le_condEntropy_comp {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (h : β → γ) : H[X | Y ; μ] ≤ H[X | h ∘ Y ; μ] := by
  have e : H[X | Y ; μ] = H[X | pair Y (h ∘ Y) ; μ] :=
    (condEntropy_congr_right hμ X (fun y => (y, h y)) (fun a b hab => (Prod.mk.inj hab).1)
      (fun _ => rfl)).symm
  rw [e]
  exact condEntropy_le_condEntropy hμ X Y (h ∘ Y)

/-- `H(X, Y) ≤ H(X) + H(Y)`, with equality iff `X` and `Y` are independent
(`condEntropy_eq_entropy_iff`). -/
theorem entropyRV_pair_le_add {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[pair X Y ; μ] ≤ H[X ; μ] + H[Y ; μ] := by
  have h1 := chain_rule hμ X Y
  have h2 := condEntropy_le_entropy hμ Y X
  linarith

end InfoTheory
