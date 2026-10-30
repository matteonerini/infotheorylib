/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Inequalities.Han
public import InfoTheoryLib.MutualInformation.Conditional

/-!
# Entropy rates of subsets

For random variables `X₀, …, Xₙ₋₁` and a subset `S` of the indices, `X(S) = (Xᵢ)_{i ∈ S}`. The
entropy `h(S) = H(X(S))` of the subsets is submodular, because conditioning reduces entropy:
`H(X(A ∪ B)) + H(X(A ∩ B)) ≤ H(X(A)) + H(X(B))` is `I(X(A \ B); X(B \ A) | X(A ∩ B)) ≥ 0`. Han's
inequalities (Theorems 17.6.1–17.6.4) follow from `Inequalities.Han`.

We write `X(S)` as the vector `i ↦ some Xᵢ` for `i ∈ S` and `none` otherwise, so that all the
subsets have values in the same finite type.

## Main definitions

* `subRV X S`: the random vector `X(S)`.
* `subsetEntropy μ X S`: `H(X(S))`.

## Main statements

* `isSubmodular_subsetEntropy`: the entropy of subsets is submodular.
* `condEntropy_subRV_compl`, `mutualInfo_subRV_compl`: `H(X(S) | X(Sᶜ)) = H(X) - H(X(Sᶜ))` and
  `I(X(S); X(Sᶜ)) = H(X(S)) + H(X(Sᶜ)) - H(X)`.
* `subsetAvg_entropy_succ_le`: **Theorem 17.6.1 (Han)** for entropies.
* `subsetExpAvg_entropy_succ_le`: **Theorem 17.6.2** for entropies.
* `subsetCondAvg_entropy_le_succ`: **Theorem 17.6.3 (Han)** for entropies.
* `subsetMutAvg_entropy_succ_le`: **Theorem 17.6.4** for entropies.

## Implementation notes

The book states these results for differential entropies; the proofs only use the chain rule and
the fact that conditioning reduces entropy, and we state them for discrete random variables. The
Gaussian case, which gives the determinant inequalities of Section 17.9, is
`Inequalities.Determinant`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 17.6
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α γ : Type*} [Fintype Ω] [Fintype α] [Fintype γ] {n : ℕ}

/-- The random vector `X(S) = (Xᵢ)_{i ∈ S}`, as `i ↦ some Xᵢ` on `S` and `none` elsewhere. -/
def subRV (X : Fin n → Ω → α) (S : Finset (Fin n)) : Ω → Fin n → Option α :=
  fun ω i => if i ∈ S then some (X i ω) else none

/-- The entropy `H(X(S))` of the subset `S` of the random variables. -/
def subsetEntropy (μ : Ω → ℝ) (X : Fin n → Ω → α) (S : Finset (Fin n)) : ℝ := H[subRV X S ; μ]

variable {μ : Ω → ℝ} {X : Fin n → Ω → α}

/-- Two random variables that are functions of each other have the same entropy. -/
lemma entropyRV_eq_of_comp {β δ : Type*} [Fintype β] [Fintype δ] (hμ : IsPMF μ) {Y : Ω → β}
    {Z : Ω → δ} (f : δ → β) (g : β → δ) (h1 : ∀ ω, Y ω = f (Z ω)) (h2 : ∀ ω, Z ω = g (Y ω)) :
    H[Y ; μ] = H[Z ; μ] := by
  refine le_antisymm ?_ ?_
  · rw [show Y = f ∘ Z from funext h1]
    exact entropyRV_comp_le hμ Z f
  · rw [show Z = g ∘ Y from funext h2]
    exact entropyRV_comp_le hμ Y g

/-- Keep the coordinates in `C` of a vector. -/
def maskVec (C : Finset (Fin n)) (m : Fin n → Option α) : Fin n → Option α :=
  fun i => if i ∈ C then m i else none

omit [Fintype Ω] [Fintype α] in
lemma maskVec_subRV (S T : Finset (Fin n)) (ω : Ω) (hT : T ⊆ S) :
    maskVec T (subRV X S ω) = subRV X T ω := by
  funext i
  simp only [maskVec, subRV]
  by_cases h : i ∈ T
  · simp [h, hT h]
  · simp [h]

/-- `H(Z, X(S ∪ T)) = H(Z, X(S), X(T))`. -/
lemma entropy_pair_subRV_union (hμ : IsPMF μ) (Z : Ω → γ) (S T : Finset (Fin n)) :
    H[pair Z (subRV X (S ∪ T)) ; μ] = H[pair Z (pair (subRV X S) (subRV X T)) ; μ] := by
  refine entropyRV_eq_of_comp hμ
    (fun p => (p.1, fun i => if i ∈ S then p.2.1 i else p.2.2 i))
    (fun p => (p.1, maskVec S p.2, maskVec T p.2)) (fun ω => ?_) (fun ω => ?_)
  · simp only [pair, Prod.mk.injEq, true_and]
    funext i
    simp only [subRV, mem_union]
    by_cases hS : i ∈ S <;> simp [hS]
  · simp only [pair, Prod.mk.injEq, true_and]
    exact ⟨(maskVec_subRV _ _ ω subset_union_left).symm,
      (maskVec_subRV _ _ ω subset_union_right).symm⟩

/-- `H(X(S ∪ T)) = H(X(S), X(T))`. -/
lemma entropy_subRV_union (hμ : IsPMF μ) (S T : Finset (Fin n)) :
    H[subRV X (S ∪ T) ; μ] = H[pair (subRV X S) (subRV X T) ; μ] := by
  have h := entropy_pair_subRV_union (X := X) hμ (fun _ : Ω => ()) S T
  have e1 : H[pair (fun _ : Ω => ()) (subRV X (S ∪ T)) ; μ] = H[subRV X (S ∪ T) ; μ] :=
    entropyRV_eq_of_comp hμ (fun m => ((), m)) (fun p => p.2) (fun _ => rfl) (fun _ => rfl)
  have e2 : H[pair (fun _ : Ω => ()) (pair (subRV X S) (subRV X T)) ; μ] =
      H[pair (subRV X S) (subRV X T) ; μ] :=
    entropyRV_eq_of_comp hμ (fun m => ((), m)) (fun p => p.2) (fun _ => rfl) (fun _ => rfl)
  rw [← e1, h, e2]

lemma subsetEntropy_empty (hμ : IsPMF μ) : subsetEntropy μ X ∅ = 0 := by
  have : subRV X ∅ = fun _ _ => none := by funext ω i; simp [subRV]
  rw [subsetEntropy, this]
  exact entropyRV_const hμ _

/-- The entropy of the subsets of the random variables is submodular:
`H(X(A ∪ B)) + H(X(A ∩ B)) ≤ H(X(A)) + H(X(B))`. -/
theorem isSubmodular_subsetEntropy (hμ : IsPMF μ) : IsSubmodular (subsetEntropy μ X) := by
  intro A B
  have hA : subsetEntropy μ X A = H[pair (subRV X (A ∩ B)) (subRV X (A \ B)) ; μ] := by
    rw [← entropy_subRV_union hμ, union_comm, sdiff_union_inter, subsetEntropy]
  have hB : subsetEntropy μ X B = H[pair (subRV X (A ∩ B)) (subRV X (B \ A)) ; μ] := by
    rw [← entropy_subRV_union hμ, union_comm, inter_comm, sdiff_union_inter, subsetEntropy]
  have hAB : subsetEntropy μ X (A ∪ B) =
      H[pair (subRV X (A ∩ B)) (pair (subRV X (A \ B)) (subRV X (B \ A))) ; μ] := by
    have e : A ∪ B = (A ∩ B) ∪ ((A \ B) ∪ (B \ A)) := by
      ext i; simp only [mem_union, mem_inter, mem_sdiff]; tauto
    rw [subsetEntropy, e, entropy_subRV_union hμ, entropy_pair_subRV_union hμ]
  have h := condMutualInfo_nonneg hμ (subRV X (A \ B)) (subRV X (B \ A)) (subRV X (A ∩ B))
  rw [condMutualInfo_eq hμ] at h
  rw [hA, hB, hAB, subsetEntropy]
  linarith

/-- `H(X(S) | X(Sᶜ)) = H(X) - H(X(Sᶜ))`: the conditional quantities of Theorem 17.6.3. -/
theorem condEntropy_subRV_compl (hμ : IsPMF μ) (S : Finset (Fin n)) :
    H[subRV X S | subRV X Sᶜ ; μ] = subsetEntropy μ X univ - subsetEntropy μ X Sᶜ := by
  rw [condEntropy_eq_sub hμ, ← entropy_subRV_union hμ, union_comm, union_compl, subsetEntropy,
    subsetEntropy]

/-- `I(X(S); X(Sᶜ)) = H(X(S)) + H(X(Sᶜ)) - H(X)`: the quantities of Theorem 17.6.4. -/
theorem mutualInfo_subRV_compl (hμ : IsPMF μ) (S : Finset (Fin n)) :
    I[subRV X S : subRV X Sᶜ ; μ] =
      subsetEntropy μ X S + subsetEntropy μ X Sᶜ - subsetEntropy μ X univ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, condEntropy_subRV_compl hμ]
  simp only [subsetEntropy]
  ring

/-- **Theorem 17.6.1 (Han), (17.51)–(17.54).** The average entropy per element of the `k`-element
subsets of the random variables decreases with `k`. -/
theorem subsetAvg_entropy_succ_le (hμ : IsPMF μ) {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    subsetAvg (subsetEntropy μ X) (k + 1) ≤ subsetAvg (subsetEntropy μ X) k :=
  subsetAvg_succ_le (isSubmodular_subsetEntropy hμ) (subsetEntropy_empty hμ) hk hkn

/-- **Theorem 17.6.2, (17.55)–(17.58).** For `r ≥ 0`, the averages of `e^{r H(X(S))/k}` over the
`k`-element subsets decrease with `k`. -/
theorem subsetExpAvg_entropy_succ_le (hμ : IsPMF μ) {r : ℝ} (hr : 0 ≤ r) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k + 1 ≤ n) :
    subsetExpAvg (subsetEntropy μ X) r (k + 1) ≤ subsetExpAvg (subsetEntropy μ X) r k :=
  subsetExpAvg_succ_le (isSubmodular_subsetEntropy hμ) (subsetEntropy_empty hμ) hr hk hkn

/-- **Theorem 17.6.3 (Han), (17.59)–(17.64).** The average conditional entropy per element
`H(X(S) | X(Sᶜ))/k` of the `k`-element subsets increases with `k`. -/
theorem subsetCondAvg_entropy_le_succ (hμ : IsPMF μ) {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    subsetCondAvg (subsetEntropy μ X) k ≤ subsetCondAvg (subsetEntropy μ X) (k + 1) :=
  subsetCondAvg_le_succ (isSubmodular_subsetEntropy hμ) hk hkn

/-- **Theorem 17.6.4, (17.65)–(17.66).** The average mutual information per element
`I(X(S); X(Sᶜ))/k` of the `k`-element subsets decreases with `k`. -/
theorem subsetMutAvg_entropy_succ_le (hμ : IsPMF μ) {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    subsetMutAvg (subsetEntropy μ X) (k + 1) ≤ subsetMutAvg (subsetEntropy μ X) k :=
  subsetMutAvg_succ_le (isSubmodular_subsetEntropy hμ) (subsetEntropy_empty hμ) hk hkn

end InfoTheory
