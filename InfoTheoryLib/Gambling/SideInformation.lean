/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Gambling.HorseRace
public import InfoTheoryLib.MutualInformation.Basic

/-!
# Gambling and side information

A gambler who observes side information `Y` before a horse race `X` can bet according to a
conditional scheme `b(x | y)`. The best such scheme is conditionally proportional gambling
`b(x | y) = p(x | y)`, and the increase in the optimal doubling rate due to the side information
is the mutual information `I(X; Y)`.

The race and the side information are random variables `X : Ω → α`, `Y : Ω → β` on a finite
probability space `(Ω, μ)`. A conditional betting scheme is `b : β → α → ℝ`, with `b y` the bets
placed when `Y = y`. Logarithms are natural.

## Main definitions

* `condDoublingRate μ X Y b o`: the doubling rate `E log b(X | Y) o(X)` of a conditional betting
  scheme, (6.23).
* `optCondDoublingRate μ X Y o`: the optimal doubling rate `W*(X | Y)` with side information.

## Main statements

* `condDoublingRate_le`, `condDoublingRate_condDist`, `optCondDoublingRate_eq`: (6.26)–(6.28),
  `W*(X | Y) = ∑ p(x) log o(x) - H(X | Y)`, achieved by `b(x | y) = p(x | y)`.
* `optDoublingRate_dist`: (6.29), `W*(X) = ∑ p(x) log o(x) - H(X)`.
* `optCondDoublingRate_sub`: Theorem 6.2.1, `ΔW = W*(X | Y) - W*(X) = I(X; Y)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 6.2
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]

/-- **Definition (6.23).** The doubling rate `E log b(X | Y) o(X) = ∑ p(x, y) log b(x | y) o(x)` of
the conditional betting scheme `b(x | y) = b y x`, which bets on the race `X` after observing the
side information `Y`. -/
def condDoublingRate (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (b : β → α → ℝ) (o : α → ℝ) : ℝ :=
  ∑ y, ∑ x, dist μ (pair Y X) (y, x) * log (b y x * o x)

/-- A conditional betting scheme: `b(· | y)` is a pmf for every `y` that can occur, and the
gambler bets on every horse that can win given `y`. -/
def IsCondBet (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (b : β → α → ℝ) : Prop :=
  (∀ y, dist μ Y y ≠ 0 → IsPMF (b y)) ∧ ∀ y x, b y x = 0 → dist μ (pair Y X) (y, x) = 0

/-- **Definition (6.23).** The optimal doubling rate `W*(X | Y)` with side information `Y`. -/
def optCondDoublingRate (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (o : α → ℝ) : ℝ :=
  sSup {w | ∃ b, IsCondBet μ X Y b ∧ condDoublingRate μ X Y b o = w}

/-- The conditional doubling rate averages the doubling rates of the races given `Y = y`. -/
lemma condDoublingRate_eq_sum {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (b : β → α → ℝ) (o : α → ℝ) :
    condDoublingRate μ X Y b o = ∑ y, dist μ Y y * doublingRate (b y) o (condDist μ X Y y) := by
  refine sum_congr rfl fun y _ => ?_
  rw [doublingRate, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, dist_mul_condDist hμ X Y y x]

/-- `∑_y p(y) (∑_x p(x | y) log o(x) - H(X | Y = y)) = ∑_x p(x) log o(x) - H(X | Y)`. -/
lemma sum_dist_mul_cond {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (o : α → ℝ) :
    ∑ y, dist μ Y y * (∑ x, condDist μ X Y y x * log (o x) - entropy (condDist μ X Y y)) =
      ∑ x, dist μ X x * log (o x) - H[X | Y ; μ] := by
  have h1 : ∑ y, dist μ Y y * ∑ x, condDist μ X Y y x * log (o x) =
      ∑ x, dist μ X x * log (o x) := by
    simp_rw [mul_sum, ← mul_assoc, dist_mul_condDist hμ X Y]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_mul, sum_dist_pair_left]
  simp only [mul_sub, sum_sub_distrib, h1, condEntropy, condEntropyAt]

/-- **(6.26)–(6.28)** Every conditional betting scheme has
`E log b(X | Y) o(X) ≤ ∑ p(x) log o(x) - H(X | Y)`. -/
theorem condDoublingRate_le {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β}
    {b : β → α → ℝ} (hb : IsCondBet μ X Y b) {o : α → ℝ} (ho : ∀ x, 0 < o x) :
    condDoublingRate μ X Y b o ≤ ∑ x, dist μ X x * log (o x) - H[X | Y ; μ] := by
  rw [condDoublingRate_eq_sum hμ, ← sum_dist_mul_cond hμ]
  refine sum_le_sum fun y _ => ?_
  by_cases hy : dist μ Y y = 0
  · simp [hy]
  · refine mul_le_mul_of_nonneg_left ?_ (dist_nonneg hμ Y y)
    refine doublingRate_le (condDist_isPMF hμ X Y hy) (hb.1 y hy) (fun x hx => ?_) ho
    rw [condDist, hb.2 y x hx, zero_div]

omit [Fintype β] in
/-- Conditionally proportional gambling `b(x | y) = p(x | y)` is a conditional betting scheme. -/
lemma isCondBet_condDist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    IsCondBet μ X Y (condDist μ X Y) := by
  refine ⟨fun y hy => condDist_isPMF hμ X Y hy, fun y x hx => ?_⟩
  rcases div_eq_zero_iff.1 hx with h | h
  · exact h
  · exact dist_pair_eq_zero_of_left hμ Y X h x

/-- **(6.26)–(6.28)** Conditionally proportional gambling `b(x | y) = p(x | y)` achieves
`∑ p(x) log o(x) - H(X | Y)`. -/
theorem condDoublingRate_condDist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    {o : α → ℝ} (ho : ∀ x, 0 < o x) :
    condDoublingRate μ X Y (condDist μ X Y) o = ∑ x, dist μ X x * log (o x) - H[X | Y ; μ] := by
  rw [condDoublingRate_eq_sum hμ, ← sum_dist_mul_cond hμ]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : dist μ Y y = 0
  · simp [hy]
  · rw [doublingRate_self (condDist_isPMF hμ X Y hy) ho]

/-- **(6.28)** `W*(X | Y) = ∑ p(x) log o(x) - H(X | Y)`. -/
theorem optCondDoublingRate_eq {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    {o : α → ℝ} (ho : ∀ x, 0 < o x) :
    optCondDoublingRate μ X Y o = ∑ x, dist μ X x * log (o x) - H[X | Y ; μ] :=
  IsGreatest.csSup_eq ⟨⟨_, isCondBet_condDist hμ X Y, condDoublingRate_condDist hμ X Y ho⟩,
    fun _ ⟨_, hb, hw⟩ => hw ▸ condDoublingRate_le hμ hb ho⟩

/-- **(6.29)** Without side information, `W*(X) = ∑ p(x) log o(x) - H(X)`. -/
theorem optDoublingRate_dist {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) {o : α → ℝ}
    (ho : ∀ x, 0 < o x) :
    optDoublingRate o (dist μ X) = ∑ x, dist μ X x * log (o x) - H[X ; μ] :=
  optDoublingRate_eq (hμ.dist X) ho

/-- **Theorem 6.2.1, (6.25), (6.30).** The increase `ΔW = W*(X | Y) - W*(X)` in the optimal
doubling rate due to the side information `Y` is the mutual information `I(X; Y)`. In particular,
independent side information does not increase the doubling rate. -/
theorem optCondDoublingRate_sub {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    {o : α → ℝ} (ho : ∀ x, 0 < o x) :
    optCondDoublingRate μ X Y o - optDoublingRate o (dist μ X) = I[X : Y ; μ] := by
  rw [optCondDoublingRate_eq hμ X Y ho, optDoublingRate_dist hμ X ho,
    mutualInfo_eq_entropy_sub_condEntropy hμ]
  ring

end InfoTheory
