/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Channel
public import InfoTheoryLib.MutualInformation.Basic
public import InfoTheoryLib.Entropy.Concavity

/-!
# Concavity and convexity of mutual information

For an input distribution `p(x)` and a channel `W(y | x)`, `mutualInfoOf p W` is the mutual
information of the pair with joint law `p(x) W(y | x)`.

## Main statements

* `mutualInfoOf_concave_input`: `I(X; Y)` is concave in `p(x)` for a fixed channel.
* `mutualInfoOf_convex_channel`: `I(X; Y)` is convex in the channel for a fixed `p(x)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 2.7.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- The mutual information `I(X;Y)` of the pair with joint law `p(x) W(y|x)`. -/
def mutualInfoOf (p : α → ℝ) (W : α → β → ℝ) : ℝ := I[Prod.fst : Prod.snd ; jointOf p W]

lemma condEntropy_jointOf {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    H[Prod.snd | Prod.fst ; jointOf p W] = ∑ x, p x * entropy (W x) := by
  rw [condEntropy, dist_jointOf_fst hW]
  refine sum_congr rfl fun x _ => ?_
  rcases (hp.nonneg x).eq_or_lt with h | h
  · rw [← h, zero_mul, zero_mul]
  · congr 1
    unfold condEntropyAt condDist
    congr 1
    funext y
    rw [dist_pair_fst_snd, dist_jointOf_fst hW, jointOf]
    field_simp

/-- `I(X;Y) = H(Y) - ∑ₓ p(x) H(Y | X = x)` (2.111). -/
lemma mutualInfoOf_eq {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    mutualInfoOf p W = entropy (outDist p W) - ∑ x, p x * entropy (W x) := by
  rw [mutualInfoOf, mutualInfo_eq_entropy_sub_condEntropy' (jointOf_isPMF hp hW),
    condEntropy_jointOf hp hW, entropyRV, dist_jointOf_snd]

/-- `I(X;Y) = D(p(x) W(y|x) ‖ p(x) p(y))`. -/
lemma mutualInfoOf_eq_relEntropy {p : α → ℝ} {W : α → β → ℝ} (hW : IsChannel W) :
    mutualInfoOf p W = relEntropyReal (jointOf p W) (prodDist p (outDist p W)) := by
  rw [mutualInfoOf, mutualInfo, dist_pair_fst_snd, dist_jointOf_fst hW, dist_jointOf_snd]

/-- **Theorem 2.7.4 (first part).** `I(X;Y)` is a concave function of `p(x)` for fixed
`p(y|x)`. -/
theorem mutualInfoOf_concave_input {W : α → β → ℝ} (hW : IsChannel W) :
    ConcaveOn ℝ {p : α → ℝ | IsPMF p} (fun p => mutualInfoOf p W) := by
  refine ⟨fun p₁ h₁ p₂ h₂ s t hs ht hst => h₁.mix h₂ hs ht hst, ?_⟩
  intro p₁ h₁ p₂ h₂ s t hs ht hst
  have hmix := h₁.mix h₂ hs ht hst
  simp only [smul_eq_mul]
  rw [mutualInfoOf_eq h₁ hW, mutualInfoOf_eq h₂ hW, mutualInfoOf_eq hmix hW]
  have hout : outDist (s • p₁ + t • p₂) W = s • outDist p₁ W + t • outDist p₂ W := by
    funext y
    simp [outDist, add_mul, sum_add_distrib, mul_sum, mul_assoc]
  have hH := entropy_concaveOn.2 (outDist_isPMF h₁ hW) (outDist_isPMF h₂ hW) hs ht hst
  rw [hout]
  simp only [smul_eq_mul] at hH
  have hlin : ∑ x, (s • p₁ + t • p₂) x * entropy (W x) =
      s * ∑ x, p₁ x * entropy (W x) + t * ∑ x, p₂ x * entropy (W x) := by
    simp [add_mul, sum_add_distrib, mul_sum, mul_assoc]
  rw [hlin]
  linarith

/-- **Theorem 2.7.4 (second part).** `I(X;Y)` is a convex function of `p(y|x)` for fixed
`p(x)`. -/
theorem mutualInfoOf_convex_channel {p : α → ℝ} (hp : IsPMF p) :
    ConvexOn ℝ {W : α → β → ℝ | IsChannel W} (fun W => mutualInfoOf p W) := by
  refine ⟨fun W₁ h₁ W₂ h₂ s t hs ht hst => h₁.mix h₂ hs ht hst, ?_⟩
  intro W₁ h₁ W₂ h₂ s t hs ht hst
  obtain rfl : t = 1 - s := by linarith
  simp only [smul_eq_mul]
  rw [mutualInfoOf_eq_relEntropy h₁, mutualInfoOf_eq_relEntropy h₂,
    mutualInfoOf_eq_relEntropy (h₁.mix h₂ hs ht hst)]
  have hj : jointOf p (s • W₁ + (1 - s) • W₂) =
      fun z => s * jointOf p W₁ z + (1 - s) * jointOf p W₂ z := by
    funext z; simp [jointOf]; ring
  have hq : prodDist p (outDist p (s • W₁ + (1 - s) • W₂)) =
      fun z => s * prodDist p (outDist p W₁) z + (1 - s) * prodDist p (outDist p W₂) z := by
    funext z
    simp only [prodDist, outDist, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      sum_add_distrib, mul_sum]
    congr 1 <;> refine sum_congr rfl fun x _ => by ring
  rw [hj, hq]
  have habs : ∀ W : α → β → ℝ, IsChannel W →
      AbsCont (jointOf p W) (prodDist p (outDist p W)) := fun W hW => by
    have := absCont_dist_pair_prodDist (jointOf_isPMF hp hW) Prod.fst Prod.snd
    rwa [dist_pair_fst_snd, dist_jointOf_fst hW, dist_jointOf_snd] at this
  exact relEntropyReal_convex_pair (jointOf_isPMF hp h₁).nonneg
    ((hp.prodDist (outDist_isPMF hp h₁))).nonneg (jointOf_isPMF hp h₂).nonneg
    ((hp.prodDist (outDist_isPMF hp h₂))).nonneg (habs W₁ h₁) (habs W₂ h₂) hs (by linarith)

end InfoTheory
