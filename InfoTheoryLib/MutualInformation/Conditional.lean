/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MutualInformation.Basic

/-!
# Conditional mutual information

## Main definitions

* `condMutualInfo μ X Y Z`: `I(X; Y | Z) = H(X | Z) - H(X | Y, Z)`, with notation
  `I[X : Y | Z ; μ]`.

## Main statements

* `condMutualInfo_eq_relEntropy`: `I(X; Y | Z) = D(p(x, y, z) ‖ p(z) p(x | z) p(y | z))`.
* `condMutualInfo_nonneg`: `I(X; Y | Z) ≥ 0`, with equality iff `X` and `Y` are conditionally
  independent given `Z` (`condMutualInfo_eq_zero_iff`).
* `chain_rule_mutualInfo₂`: `I(X; Y, Z) = I(X; Z) + I(X; Y | Z)`.
* `condMutualInfo_self`: `I(X; X | Z) = H(X | Z)`.
* `condMutualInfo_eq_add_sub`: `I(X; Y | Z) = H(X | Z) + H(Y | Z) - H(X, Y | Z)`.

## Notation

* `I[X : Y | Z ; μ]`: the conditional mutual information (scoped in `InfoTheory`).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 2.5 and 2.6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Definition (2.60).** The conditional mutual information
`I(X;Y|Z) = H(X|Z) - H(X|Y, Z)`. -/
def condMutualInfo (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : ℝ :=
  H[X | Z ; μ] - H[X | pair Y Z ; μ]

/-- `I[X : Y | Z ; μ]` is the conditional mutual information `I(X;Y|Z)`. -/
scoped notation3:max "I[" X " : " Y " | " Z " ; " μ "]" => condMutualInfo μ X Y Z

/-- `I(X;Y|Z)` in terms of joint entropies. -/
lemma condMutualInfo_eq {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    I[X : Y | Z ; μ] =
      H[pair Z X ; μ] + H[pair Z Y ; μ] - H[Z ; μ] - H[pair Z (pair X Y) ; μ] := by
  rw [condMutualInfo, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  have h1 : H[pair (pair Y Z) X ; μ] = H[pair Z (pair X Y) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : γ × α × β => ((t.2.2, t.1), t.2.1))
      (fun a b h => by
        obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
        simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl)
  rw [h1, entropyRV_pair_comm μ Y Z]; ring

/-- `I(X;Y|Z) = I(Y;X|Z)`. -/
lemma condMutualInfo_comm {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    I[X : Y | Z ; μ] = I[Y : X | Z ; μ] := by
  rw [condMutualInfo_eq hμ, condMutualInfo_eq hμ]
  have : H[pair Z (pair X Y) ; μ] = H[pair Z (pair Y X) ; μ] :=
    entropyRV_eq_of_injective μ (Prod.map id Prod.swap)
      (Function.injective_id.prodMap Prod.swap_injective) (fun _ => rfl)
  rw [this]; ring

/-- `I(X;Y|Z)` with the conditioning variable written first, `H(X|Z) - H(X|Z, Y)`. -/
lemma condMutualInfo_eq' {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | pair Z Y ; μ] := by
  have hswap : H[X | pair Y Z ; μ] = H[X | pair Z Y ; μ] :=
    condEntropy_congr_right hμ X Prod.swap Prod.swap_injective (fun _ => rfl)
  rw [condMutualInfo, hswap]

/-- (2.61) `I(X;Y|Z) = E log (p(X, Y|Z) / (p(X|Z) p(Y|Z)))`. -/
theorem condMutualInfo_eq_expect {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : I[X : Y | Z ; μ] = ∑ ω, μ ω * log (condDist μ (pair X Y) Z (Z ω) (X ω, Y ω) /
      (condDist μ X Z (Z ω) (X ω) * condDist μ Y Z (Z ω) (Y ω))) := by
  have key : ∀ ω, μ ω * log (condDist μ (pair X Y) Z (Z ω) (X ω, Y ω) /
      (condDist μ X Z (Z ω) (X ω) * condDist μ Y Z (Z ω) (Y ω))) =
        μ ω * log (dist μ (pair Z (pair X Y)) (Z ω, X ω, Y ω)) + μ ω * log (dist μ Z (Z ω))
        - μ ω * log (dist μ (pair Z X) (Z ω, X ω)) - μ ω * log (dist μ (pair Z Y) (Z ω, Y ω)) := by
    intro ω
    rcases (hμ.nonneg ω).eq_or_lt with h | h
    · simp [← h]
    · have e : ((X ω, Y ω) : α × β) = pair X Y ω := rfl
      have h1 := condDist_pos hμ (pair X Y) Z h
      have h2 := condDist_pos hμ X Z h
      have h3 := condDist_pos hμ Y Z h
      rw [e, log_div h1.ne' (mul_pos h2 h3).ne', log_mul h2.ne' h3.ne', log_condDist hμ _ _ h,
        log_condDist hμ _ _ h, log_condDist hμ _ _ h]
      simp only [pair_apply]
      ring
  rw [condMutualInfo_eq hμ, entropyRV_eq, entropyRV_eq, entropyRV_eq, entropyRV_eq]
  simp only [key, sum_sub_distrib, sum_add_distrib, pair_apply]
  ring

/-- `I(X;Y|c) = I(X;Y)` for a constant `c`. -/
lemma condMutualInfo_const {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (c : γ) :
    I[X : Y | (fun _ => c) ; μ] = I[X : Y ; μ] := by
  have h : H[X | pair Y (fun _ => c) ; μ] = H[X | Y ; μ] :=
    condEntropy_congr_right hμ X (fun y => (y, c)) (fun a b h => (Prod.mk.inj h).1)
      (fun _ => rfl)
  rw [condMutualInfo, condEntropy_const hμ, h, mutualInfo_eq_entropy_sub_condEntropy hμ]

/-- The two-variable chain rule `I(X; Y, Z) = I(X; Z) + I(X; Y | Z)` (2.119). -/
theorem chain_rule_mutualInfo₂ {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    I[X : pair Y Z ; μ] = I[X : Z ; μ] + I[X : Y | Z ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_eq_entropy_sub_condEntropy hμ,
    condMutualInfo]; ring

/-- `I(X;Y|Z) = D(p(x, y, z) ‖ p(z) p(x|z) p(y|z))`. -/
theorem condMutualInfo_eq_relEntropy {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    I[X : Y | Z ; μ] = relEntropyReal (dist μ (pair Z (pair X Y))) (condProdDist μ X Y Z) := by
  rw [relEntropyReal, sum_dist_mul μ (pair Z (pair X Y))
    (fun t => log (dist μ (pair Z (pair X Y)) t / condProdDist μ X Y Z t)),
    condMutualInfo_eq hμ, entropyRV_eq, entropyRV_eq, entropyRV_eq, entropyRV_eq]
  have key : ∀ ω, μ ω * log (dist μ (pair Z (pair X Y)) (pair Z (pair X Y) ω) /
      condProdDist μ X Y Z (pair Z (pair X Y) ω)) =
        μ ω * log (dist μ (pair Z (pair X Y)) (pair Z (pair X Y) ω)) + μ ω * log (dist μ Z (Z ω))
        - μ ω * log (dist μ (pair Z X) (pair Z X ω))
        - μ ω * log (dist μ (pair Z Y) (pair Z Y ω)) := by
    intro ω
    rcases (hμ.nonneg ω).eq_or_lt with h | h
    · simp [← h]
    · have h1 := dist_pos hμ (pair Z (pair X Y)) h
      have h2 := dist_pos hμ (pair Z X) h
      have h3 := dist_pos hμ (pair Z Y) h
      have h4 := dist_pos hμ Z h
      simp only [condProdDist, pair_apply] at h1 h2 h3 ⊢
      rw [log_div h1.ne' (by positivity), log_div (by positivity) h4.ne',
        log_mul h2.ne' h3.ne']
      ring
  simp only [key, sum_sub_distrib, sum_add_distrib]
  ring

/-- **Corollary (2.92).** `I(X;Y|Z) ≥ 0`. -/
theorem condMutualInfo_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_relEntropy hμ]
  exact relEntropyReal_nonneg (hμ.dist _) (condProdDist_isPMF hμ X Y Z)
    (absCont_condProdDist hμ X Y Z)

/-- **Corollary (2.92), equality case.** `I(X;Y|Z) = 0` iff `X` and `Y` are conditionally
independent given `Z`. -/
theorem condMutualInfo_eq_zero_iff {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : I[X : Y | Z ; μ] = 0 ↔ CondIndep μ X Y Z := by
  rw [condMutualInfo_eq_relEntropy hμ, condIndep_iff_dist_eq hμ]
  exact relEntropyReal_eq_zero_iff (hμ.dist _) (condProdDist_isPMF hμ X Y Z)
    (absCont_condProdDist hμ X Y Z)

/-- Conditional chain rule `I(X; Y, Z | W) = I(X; Z | W) + I(X; Y | Z, W)`. -/
lemma chain_rule_condMutualInfo {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (W : Ω → δ) :
    I[X : pair Y Z | W ; μ] = I[X : Z | W ; μ] + I[X : Y | pair Z W ; μ] := by
  have h : H[X | pair (pair Y Z) W ; μ] = H[X | pair Y (pair Z W) ; μ] :=
    condEntropy_congr_right hμ X (fun t : (β × γ) × δ => (t.1.1, t.1.2, t.2))
      (fun a b h => by
        obtain ⟨⟨a1, a2⟩, a3⟩ := a; obtain ⟨⟨b1, b2⟩, b3⟩ := b
        simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl) |>.symm
  rw [condMutualInfo, condMutualInfo, condMutualInfo, h]; ring

/-- Processing `Y` cannot increase the conditional information: `I(X; g(Y) | Z) ≤ I(X; Y | Z)`. -/
lemma condMutualInfo_comp_le {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (g : β → δ) : I[X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have h1 : I[X : Y | Z ; μ] = I[X : pair Y (g ∘ Y) | Z ; μ] := by
    rw [condMutualInfo, condMutualInfo]
    congr 1
    exact (condEntropy_congr_right hμ X (X := pair Y Z) (X' := pair (pair Y (g ∘ Y)) Z)
      (fun t : β × γ => ((t.1, g t.1), t.2))
      (fun a b h => Prod.ext (Prod.mk.inj (Prod.mk.inj h).1).1 (Prod.mk.inj h).2)
      (fun _ => rfl)).symm
  rw [h1, chain_rule_condMutualInfo hμ]
  linarith [condMutualInfo_nonneg hμ X Y (pair (g ∘ Y) Z)]

/-- **Proposition 2.21 of [yeung2008].** `I(X; X | Z) = H(X | Z)`. -/
theorem condMutualInfo_self {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Z : Ω → γ) :
    I[X : X | Z ; μ] = H[X | Z ; μ] := by
  have h : H[X | pair Z X ; μ] = 0 := condEntropy_comp_self hμ (pair Z X) Prod.snd
  rw [condMutualInfo_eq' hμ, h, sub_zero]

/-- `I(X; Y | Z) = H(Y | Z) - H(Y | X, Z)`. -/
theorem condMutualInfo_eq_sub_right {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : I[X : Y | Z ; μ] = H[Y | Z ; μ] - H[Y | pair X Z ; μ] := by
  rw [condMutualInfo_comm hμ, condMutualInfo]

/-- `I(X; Y | Z) = H(X | Z) + H(Y | Z) - H(X, Y | Z)`. -/
theorem condMutualInfo_eq_add_sub {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[pair X Y | Z ; μ] := by
  rw [condMutualInfo_eq hμ, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  ring

end InfoTheory
