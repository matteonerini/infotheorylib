/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.RandomVector
public import InfoTheoryLib.Entropy.Conditional

/-!
# The chain rule for the entropy of a random vector

## Main statements

* `chain_rule_entropy`: `H(X₁, …, Xₙ) = ∑ᵢ H(Xᵢ | X_{i-1}, …, X₁)`.
* `chain_rule_entropy_cond`: the same chain rule conditionally on a random variable `Y`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.5.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma entropyRV_prefixRV_succ (μ : Ω → ℝ) (X : ℕ → Ω → α) (n : ℕ) :
    H[prefixRV X (n + 1) ; μ] = H[pair (prefixRV X n) (X n) ; μ] :=
  entropyRV_eq_of_injective μ _ (snoc_injective2 n) (fun ω => prefixRV_succ X n ω)

/-- **Theorem 2.5.1 (Chain rule for entropy).**
`H(X₁, X₂, …, Xₙ) = ∑ᵢ H(Xᵢ | X_{i-1}, …, X₁)`. -/
theorem chain_rule_entropy {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (n : ℕ) :
    H[prefixRV X n ; μ] = ∑ i ∈ range n, H[X i | prefixRV X i ; μ] := by
  induction n with
  | zero => rw [prefixRV_zero_eq, entropyRV_const hμ, sum_range_zero]
  | succ n ih => rw [entropyRV_prefixRV_succ, chain_rule hμ, ih, sum_range_succ]

/-- The conditional chain rule `H(X₁, …, Xₙ | Y) = ∑ᵢ H(Xᵢ | Y, X_{i-1}, …, X₁)`. -/
theorem chain_rule_entropy_cond {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (Y : Ω → β)
    (n : ℕ) : H[prefixRV X n | Y ; μ] = ∑ i ∈ range n, H[X i | pair Y (prefixRV X i) ; μ] := by
  induction n with
  | zero =>
    rw [prefixRV_zero_eq, sum_range_zero, condEntropy_eq_sub hμ, sub_eq_zero]
    exact entropyRV_eq_of_injective μ (fun y => (y, (Fin.elim0 : Fin 0 → α)))
      (fun a b h => (Prod.mk.inj h).1) (fun _ => rfl)
  | succ n ih =>
    have hswap : H[X n | pair (prefixRV X n) Y ; μ] = H[X n | pair Y (prefixRV X n) ; μ] :=
      condEntropy_congr_right hμ (X n) Prod.swap Prod.swap_injective (fun _ => rfl)
    rw [condEntropy_congr_left hμ (Y := pair (prefixRV X n) (X n)) Y _ (snoc_injective2 n)
      (fun ω => prefixRV_succ X n ω), chain_rule_cond hμ, ih, sum_range_succ, hswap]

end InfoTheory
