/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Independence
public import InfoTheoryLib.Entropy.Conditional
public import InfoTheoryLib.RelativeEntropy.InformationInequality

/-!
# Mutual information

## Main definitions

* `mutualInfo μ X Y`: the mutual information `I(X; Y) = D(p(x, y) ‖ p(x) p(y))`, with notation
  `I[X : Y ; μ]`.

## Main statements

* `mutualInfo_eq_entropy_sub_condEntropy`: `I(X; Y) = H(X) - H(X | Y)`.
* `mutualInfo_eq_add_sub`: `I(X; Y) = H(X) + H(Y) - H(X, Y)`.
* `mutualInfo_comm`, `mutualInfo_self`: `I(X; Y) = I(Y; X)` and `I(X; X) = H(X)`.
* `mutualInfo_nonneg`: `I(X; Y) ≥ 0`, with equality iff `X` and `Y` are independent
  (`mutualInfo_eq_zero_iff`).
* `mutualInfo_le_sum_log_div`: `I(X; Y) ≤ D(p(x, y) ‖ p(x) Q(y))` for every pmf `Q`.

## Notation

* `I[X : Y ; μ]`: the mutual information of `X` and `Y` (scoped in `InfoTheory`).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006],
  Sections 2.3, 2.4 and 2.6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Definition (2.28)–(2.29).** The mutual information `I(X;Y)` is the relative entropy between
the joint distribution `p(x, y)` and the product distribution `p(x) p(y)`. Since
`p(x, y) ≪ p(x) p(y)` (`absCont_dist_pair_prodDist`), it is finite and we define it as a real
number; see `mutualInfo_eq_relEntropy`. -/
def mutualInfo (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) : ℝ :=
  relEntropyReal (dist μ (pair X Y)) (prodDist (dist μ X) (dist μ Y))

/-- `I[X : Y ; μ]` is the mutual information `I(X;Y)`. -/
scoped notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo μ X Y

/-- (2.29) `I(X;Y) = D(p(x, y) ‖ p(x) p(y))`. -/
lemma mutualInfo_eq_relEntropy {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    (I[X : Y ; μ] : EReal) = relEntropy (dist μ (pair X Y)) (prodDist (dist μ X) (dist μ Y)) :=
  (relEntropy_of_absCont (absCont_dist_pair_prodDist hμ X Y)).symm

/-- (2.28) `I(X;Y) = ∑ₓ ∑ᵧ p(x, y) log (p(x, y) / (p(x) p(y)))`. -/
lemma mutualInfo_eq_sum (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) :
    I[X : Y ; μ] = ∑ x, ∑ y, dist μ (pair X Y) (x, y) *
      log (dist μ (pair X Y) (x, y) / (dist μ X x * dist μ Y y)) := by
  rw [mutualInfo, relEntropyReal, Fintype.sum_prod_type]; rfl

/-- (2.30) `I(X;Y) = E log (p(X, Y) / (p(X) p(Y)))`. -/
lemma mutualInfo_eq_expect (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) :
    I[X : Y ; μ] = ∑ ω, μ ω *
      log (dist μ (pair X Y) (X ω, Y ω) / (dist μ X (X ω) * dist μ Y (Y ω))) := by
  rw [mutualInfo, relEntropyReal]
  exact sum_dist_mul μ (pair X Y) (fun z => log (dist μ (pair X Y) z / prodDist _ _ z))

/-- (2.45) `I(X;Y) = H(X) + H(Y) - H(X, Y)`. -/
theorem mutualInfo_eq_add_sub {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[pair X Y ; μ] := by
  have key : ∀ ω, μ ω * log (dist μ (pair X Y) (X ω, Y ω) / (dist μ X (X ω) * dist μ Y (Y ω)))
      = μ ω * log (dist μ (pair X Y) (X ω, Y ω)) - μ ω * log (dist μ X (X ω))
        - μ ω * log (dist μ Y (Y ω)) := by
    intro ω
    rcases (hμ.nonneg ω).eq_or_lt with h | h
    · simp [← h]
    · have h1 : 0 < dist μ (pair X Y) (X ω, Y ω) := dist_pos hμ (pair X Y) h
      have h2 : 0 < dist μ X (X ω) := dist_pos hμ X h
      have h3 : 0 < dist μ Y (Y ω) := dist_pos hμ Y h
      rw [log_div h1.ne' (mul_pos h2 h3).ne', log_mul h2.ne' h3.ne']
      ring
  rw [mutualInfo_eq_expect, entropyRV_eq, entropyRV_eq, entropyRV_eq]
  simp only [key, sum_sub_distrib, pair_apply]
  ring

/-- (2.39), (2.43) `I(X;Y) = H(X) - H(X|Y)`: the reduction in the uncertainty of `X` due to the
knowledge of `Y`. -/
theorem mutualInfo_eq_entropy_sub_condEntropy {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α)
    (Y : Ω → β) : I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInfo_eq_add_sub hμ, condEntropy_eq_sub hμ, entropyRV_pair_comm μ Y X]; ring

/-- (2.40), (2.44) `I(X;Y) = H(Y) - H(Y|X)`. -/
theorem mutualInfo_eq_entropy_sub_condEntropy' {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α)
    (Y : Ω → β) : I[X : Y ; μ] = H[Y ; μ] - H[Y | X ; μ] := by
  rw [mutualInfo_eq_add_sub hμ, condEntropy_eq_sub hμ]; ring

/-- (2.46) `I(X;Y) = I(Y;X)`: `X` says as much about `Y` as `Y` says about `X`. -/
theorem mutualInfo_comm {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    I[X : Y ; μ] = I[Y : X ; μ] := by
  rw [mutualInfo_eq_add_sub hμ, mutualInfo_eq_add_sub hμ, entropyRV_pair_comm μ X Y]; ring

/-- (2.42), (2.47) `I(X;X) = H(X)`: entropy is self-information. -/
theorem mutualInfo_self {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) : I[X : X ; μ] = H[X ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, condEntropy_self hμ, sub_zero]

/-- **Corollary (Non-negativity of mutual information) (2.90).** `I(X;Y) ≥ 0`. -/
theorem mutualInfo_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    0 ≤ I[X : Y ; μ] :=
  relEntropyReal_nonneg (hμ.dist _) ((hμ.dist X).prodDist (hμ.dist Y))
    (absCont_dist_pair_prodDist hμ X Y)

/-- **Corollary (2.90), equality case.** `I(X;Y) = 0` iff `X` and `Y` are independent. -/
theorem mutualInfo_eq_zero_iff {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    I[X : Y ; μ] = 0 ↔ IndepRV μ X Y := by
  rw [indepRV_iff_dist_eq]
  exact relEntropyReal_eq_zero_iff (hμ.dist _) ((hμ.dist X).prodDist (hμ.dist Y))
    (absCont_dist_pair_prodDist hμ X Y)

/-- `I(X; e(Y)) = I(X; Y)` for injective `e`. -/
lemma mutualInfo_congr_right {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) {Y : Ω → β} {Y' : Ω → γ}
    (e : β → γ) (he : Function.Injective e) (h : ∀ ω, Y' ω = e (Y ω)) :
    I[X : Y' ; μ] = I[X : Y ; μ] := by
  rw [mutualInfo_eq_add_sub hμ, mutualInfo_eq_add_sub hμ, entropyRV_eq_of_injective μ e he h,
    entropyRV_eq_of_injective μ (X := pair X Y) (Y := pair X Y') (Prod.map id e)
      (Function.injective_id.prodMap he) (fun ω => by simp [h])]

/-- `I(X; Y)` depends only on the joint law of `(X, Y)`. -/
lemma mutualInfo_eq_of_dist_pair_eq {Ω' γ' δ' : Type*} [Fintype Ω'] [Fintype γ']
    [Fintype δ'] {μ : Ω → ℝ} {ν : Ω' → ℝ} {X : Ω → γ'} {Y : Ω → δ'} {X' : Ω' → γ'}
    {Y' : Ω' → δ'} (h : dist μ (pair X Y) = dist ν (pair X' Y')) :
    I[X : Y ; μ] = I[X' : Y' ; ν] := by
  have hX : dist μ X = dist ν X' := by
    funext x; rw [← sum_dist_pair_right μ X Y, ← sum_dist_pair_right ν X' Y', h]
  have hY : dist μ Y = dist ν Y' := by
    funext y; rw [← sum_dist_pair_left μ X Y, ← sum_dist_pair_left ν X' Y', h]
  rw [mutualInfo, mutualInfo, h, hX, hY]

/-- Comparing the joint law with the product of the law of `X` and any pmf `Q` of the second
coordinate bounds the mutual information:
`I(X; Y) ≤ ∑ p(x, y) log (p(x, y)/(p(x) Q(y))) = D(p(x, y) ‖ p(x) Q(y))`. The difference is
`D(p(y) ‖ Q) ≥ 0`. -/
theorem mutualInfo_le_sum_log_div {μ : α × β → ℝ} (hμ : IsPMF μ) {Q : β → ℝ} (hQ : IsPMF Q)
    (hQμ : ∀ a b, Q b = 0 → μ (a, b) = 0) :
    I[Prod.fst : Prod.snd ; μ] ≤
      ∑ a, ∑ b, μ (a, b) * log (μ (a, b) / (dist μ Prod.fst a * Q b)) := by
  set pA := dist μ Prod.fst
  set pB := dist μ Prod.snd
  have hpB : IsPMF pB := hμ.dist _
  -- The difference of the two sums is `D(p(y) ‖ Q)`.
  have hterm : ∀ a b, μ (a, b) * log (μ (a, b) / (pA a * Q b)) =
      μ (a, b) * log (μ (a, b) / (pA a * pB b)) + μ (a, b) * log (pB b / Q b) := by
    intro a b
    rcases eq_or_ne (μ (a, b)) 0 with h0 | h0
    · simp [h0]
    have hA : pA a ≠ 0 := by
      have : μ (a, b) ≤ pA a := by
        rw [show pA a = ∑ b', μ (a, b') from dist_fst μ a]
        exact single_le_sum (fun b' _ => hμ.nonneg (a, b')) (mem_univ b)
      exact (lt_of_lt_of_le (lt_of_le_of_ne (hμ.nonneg _) (Ne.symm h0)) this).ne'
    have hB : pB b ≠ 0 := by
      have : μ (a, b) ≤ pB b := by
        rw [show pB b = ∑ a', μ (a', b) from dist_snd μ b]
        exact single_le_sum (fun a' _ => hμ.nonneg (a', b)) (mem_univ a)
      exact (lt_of_lt_of_le (lt_of_le_of_ne (hμ.nonneg _) (Ne.symm h0)) this).ne'
    have hQb : Q b ≠ 0 := fun h => h0 (hQμ a b h)
    rw [← mul_add, log_div h0 (mul_ne_zero hA hQb), log_div h0 (mul_ne_zero hA hB),
      log_div hB hQb, log_mul hA hQb, log_mul hA hB]
    ring
  have hD : ∑ a, ∑ b, μ (a, b) * log (pB b / Q b) = relEntropyReal pB Q := by
    rw [relEntropyReal, sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [← sum_mul, show pB b = ∑ a', μ (a', b) from dist_snd μ b]
  have hnn : 0 ≤ relEntropyReal pB Q := relEntropyReal_nonneg hpB hQ fun b hb => by
    rw [show pB b = ∑ a', μ (a', b) from dist_snd μ b]
    exact sum_eq_zero fun a _ => hQμ a b hb
  rw [mutualInfo_eq_sum, dist_pair_fst_snd]
  simp only [hterm, sum_add_distrib, hD]
  linarith

end InfoTheory
