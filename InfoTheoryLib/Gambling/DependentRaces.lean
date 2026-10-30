/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Gambling.HorseRace
public import InfoTheoryLib.StochasticProcess.Basic

/-!
# Dependent horse races and entropy rate

When the outcomes `X₁, X₂, …` of successive races form a stochastic process, the gambler can bet
on each race according to the results of the previous ones. A sequential betting strategy assigns
the probability `b(x₁, …, xₙ) = ∏ₖ b(xₖ | xₖ₋₁, …, x₁)` to every sequence of outcomes, so that with
`c`-for-`1` odds the wealth after `n` races is `Sₙ = cⁿ b(x₁, …, xₙ)`. Sequential betting is thus
betting on whole sequences, (6.41)–(6.43). The best strategy is conditionally proportional
betting, and `E log Sₙ = n log c - H(X₁, …, Xₙ)`: the doubling rate and the entropy rate add up
to `log c`, (6.36). For any strategy `log c - (1/n) E log Sₙ` bounds the entropy rate from above,
which is the basis of the gambling estimate of the entropy of English, (6.45)–(6.50).

Logarithms are natural.

## Main definitions

* `seqBetProb bet n`: the probability `b(x₁, …, xₙ)` that a sequential strategy assigns to a
  sequence of outcomes, (6.43).
* `seqWealth o bet n`: the wealth after `n` races, (6.32), (6.41).
* `propBet P`: conditionally proportional betting, `b(xₖ | xₖ₋₁, …, x₁) = p(xₖ | xₖ₋₁, …, x₁)`.
* `expectedLogWealth P o bet n`: `E log Sₙ`.

## Main statements

* `seqWealth_const`, `seqBetProb_isPMF`: (6.41)–(6.43), sequential betting is betting on
  sequences.
* `seqBetProb_propBet`: conditionally proportional betting bets `p(x₁, …, xₙ)` on each sequence.
* `expectedLogWealth_eq`, `expectedLogWealth_le`: (6.45)–(6.49),
  `E log Sₙ = n log c - H(X₁, …, Xₙ) - D(p‖b) ≤ n log c - H(X₁, …, Xₙ)`.
* `expectedLogWealth_propBet`, `expectedLogWealth_propBet_succ_sub`: (6.31)–(6.35), proportional
  betting achieves the bound, gaining `log c - H(Xₖ₊₁ | Xₖ, …, X₁)` in race `k + 1`.
* `tendsto_expectedLogWealth_propBet`: (6.36), `(1/n) E log Sₙ → log c - H(𝒳)`.
* `expectedLogWealth_div_le`: (6.50), `(1/n) E log Sₙ ≤ log c - H(𝒳)` for every strategy.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 6.3 and
  6.6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### Sequential betting -/

/-- **(6.43)** The probability `b(x₁, …, xₙ) = ∏ₖ b(xₖ | xₖ₋₁, …, x₁)` that the sequential betting
strategy `bet` assigns to a sequence, where `bet k y a` is the fraction of wealth bet on
`Xₖ₊₁ = a` after observing `y = (x₁, …, xₖ)`. -/
def seqBetProb (bet : ∀ k, (Fin k → α) → α → ℝ) : (n : ℕ) → (Fin n → α) → ℝ
  | 0, _ => 1
  | n + 1, x => seqBetProb bet n (Fin.init x) * bet n (Fin.init x) (x (Fin.last n))

/-- **(6.32)** The wealth after `n` races, starting from one unit and reinvesting:
`Sₙ₊₁ = Sₙ o(xₙ₊₁) b(xₙ₊₁ | xₙ, …, x₁)`. -/
def seqWealth (o : α → ℝ) (bet : ∀ k, (Fin k → α) → α → ℝ) : (n : ℕ) → (Fin n → α) → ℝ
  | 0, _ => 1
  | n + 1, x => seqWealth o bet n (Fin.init x) *
      (o (x (Fin.last n)) * bet n (Fin.init x) (x (Fin.last n)))

variable {bet : ∀ k, (Fin k → α) → α → ℝ}

omit [Fintype α] in
lemma seqBetProb_snoc (n : ℕ) (y : Fin n → α) (a : α) :
    seqBetProb bet (n + 1) (Fin.snoc y a) = seqBetProb bet n y * bet n y a := by
  simp [seqBetProb, Fin.init_snoc]

omit [Fintype α] in
/-- **(6.41)** The wealth is `Sₙ = (∏ₖ o(xₖ)) b(x₁, …, xₙ)`. -/
lemma seqWealth_eq (o : α → ℝ) (n : ℕ) (x : Fin n → α) :
    seqWealth o bet n x = (∏ i, o (x i)) * seqBetProb bet n x := by
  induction n with
  | zero => simp [seqWealth, seqBetProb]
  | succ n ih =>
    rw [seqWealth, seqBetProb, ih, Fin.prod_univ_castSucc]
    simp only [Fin.init]
    ring

omit [Fintype α] in
/-- **(6.41)–(6.42)** With `c`-for-`1` odds on every outcome, `Sₙ = cⁿ b(x₁, …, xₙ)`: sequential
betting is betting on whole sequences of outcomes. -/
lemma seqWealth_const (c : ℝ) (n : ℕ) (x : Fin n → α) :
    seqWealth (fun _ => c) bet n x = c ^ n * seqBetProb bet n x := by
  rw [seqWealth_eq]
  simp

/-- **(6.43)** If each `b(· | xₖ₋₁, …, x₁)` is a pmf, so is `b(x₁, …, xₙ)` on sequences. -/
lemma seqBetProb_isPMF (hbet : ∀ k y, IsPMF (bet k y)) (n : ℕ) : IsPMF (seqBetProb bet n) := by
  induction n with
  | zero => exact ⟨fun _ => zero_le_one, by simp [seqBetProb]⟩
  | succ n ih =>
    refine ⟨fun x => mul_nonneg (ih.nonneg _) ((hbet _ _).nonneg _), ?_⟩
    rw [sum_snoc]
    simp only [seqBetProb_snoc, ← mul_sum, (hbet _ _).sum_eq_one, mul_one]
    exact ih.sum_eq_one

/-! ### Conditionally proportional betting -/

/-- Conditionally proportional betting `b(xₖ₊₁ | xₖ, …, x₁) = p(xₖ₊₁ | xₖ, …, x₁)` on the
process `P`. -/
def propBet (P : StochasticProcess α) (k : ℕ) (y : Fin k → α) (a : α) : ℝ :=
  P.law (k + 1) (Fin.snoc y a) / P.law k y

namespace StochasticProcess

variable (P : StochasticProcess α)

lemma law_zero (x : Fin 0 → α) : P.law 0 x = 1 := by
  have h := (P.isPMF 0).sum_eq_one
  rwa [Fintype.sum_unique, Subsingleton.elim default x] at h

lemma law_snoc_le {n : ℕ} (y : Fin n → α) (a : α) : P.law (n + 1) (Fin.snoc y a) ≤ P.law n y := by
  rw [← P.consistent n y]
  exact single_le_sum (fun b _ => (P.isPMF _).nonneg _) (mem_univ a)

end StochasticProcess

/-- Conditionally proportional betting bets `b(x₁, …, xₙ) = p(x₁, …, xₙ)` on each sequence: the
conditional probabilities telescope. -/
theorem seqBetProb_propBet (P : StochasticProcess α) (n : ℕ) (x : Fin n → α) :
    seqBetProb (propBet P) n x = P.law n x := by
  induction n with
  | zero => simp [seqBetProb, P.law_zero]
  | succ n ih =>
    rw [seqBetProb, ih, propBet, Fin.snoc_init_self]
    by_cases h : P.law n (Fin.init x) = 0
    · have h1 := P.law_snoc_le (Fin.init x) (x (Fin.last n))
      rw [Fin.snoc_init_self, h] at h1
      rw [h, zero_mul]
      exact (le_antisymm h1 ((P.isPMF _).nonneg x)).symm
    · exact mul_div_cancel₀ _ h

/-! ### The expected log wealth -/

/-- The expected log wealth `E log Sₙ` after `n` races of the process `P`. -/
def expectedLogWealth (P : StochasticProcess α) (o : α → ℝ) (bet : ∀ k, (Fin k → α) → α → ℝ)
    (n : ℕ) : ℝ :=
  ∑ x, P.law n x * log (seqWealth o bet n x)

/-- **(6.45)–(6.48)** With `c`-for-`1` odds, a sequential strategy that bets on every sequence
that can occur has `E log Sₙ = n log c - H(X₁, …, Xₙ) - D(p‖b)`, where `b` is the probability it
assigns to sequences. -/
theorem expectedLogWealth_eq (P : StochasticProcess α) {c : ℝ} (hc : 0 < c)
    (hbet : ∀ k y, IsPMF (bet k y)) {n : ℕ} (habs : AbsCont (P.law n) (seqBetProb bet n)) :
    expectedLogWealth P (fun _ => c) bet n =
      n * log c - P.jointEntropy n - relEntropyReal (P.law n) (seqBetProb bet n) := by
  have hpn := P.isPMF n
  have hb := seqBetProb_isPMF hbet n
  have : n * log c - P.jointEntropy n - relEntropyReal (P.law n) (seqBetProb bet n) =
      ∑ x, (P.law n x * (n * log c) + P.law n x * log (P.law n x) -
        P.law n x * log (P.law n x / seqBetProb bet n x)) := by
    simp only [StochasticProcess.jointEntropy, entropy, relEntropyReal, sum_add_distrib,
      sum_sub_distrib, ← sum_mul, hpn.sum_eq_one]
    ring
  rw [this, expectedLogWealth]
  refine sum_congr rfl fun x _ => ?_
  rcases (hpn.nonneg x).eq_or_lt with h0 | h0
  · simp [← h0]
  · have hbx : 0 < seqBetProb bet n x := (hb.nonneg x).lt_of_ne fun h => h0.ne' (habs x h.symm)
    rw [seqWealth_const, log_mul (pow_ne_zero _ hc.ne') hbx.ne', log_pow, log_div h0.ne' hbx.ne']
    ring

/-- **(6.49)** With `c`-for-`1` odds, every sequential strategy has
`E log Sₙ ≤ n log c - H(X₁, …, Xₙ)`. -/
theorem expectedLogWealth_le (P : StochasticProcess α) {c : ℝ} (hc : 0 < c)
    (hbet : ∀ k y, IsPMF (bet k y)) {n : ℕ} (habs : AbsCont (P.law n) (seqBetProb bet n)) :
    expectedLogWealth P (fun _ => c) bet n ≤ n * log c - P.jointEntropy n := by
  rw [expectedLogWealth_eq P hc hbet habs]
  linarith [relEntropyReal_nonneg (P.isPMF n) (seqBetProb_isPMF hbet n) habs]

/-- **(6.33)–(6.35)** Conditionally proportional betting achieves
`E log Sₙ = n log c - H(X₁, …, Xₙ)`. -/
theorem expectedLogWealth_propBet (P : StochasticProcess α) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    expectedLogWealth P (fun _ => c) (propBet P) n = n * log c - P.jointEntropy n := by
  have : n * log c - P.jointEntropy n =
      ∑ x, (P.law n x * (n * log c) + P.law n x * log (P.law n x)) := by
    simp only [StochasticProcess.jointEntropy, entropy, sum_add_distrib, ← sum_mul,
      (P.isPMF n).sum_eq_one]
    ring
  rw [this, expectedLogWealth]
  refine sum_congr rfl fun x _ => ?_
  rw [seqWealth_const, seqBetProb_propBet]
  rcases ((P.isPMF n).nonneg x).eq_or_lt with h0 | h0
  · simp [← h0]
  · rw [log_mul (pow_ne_zero _ hc.ne') h0.ne', log_pow]
    ring

/-- **(6.31)** With conditionally proportional betting, race `k + 1` increases the expected log
wealth by the optimal conditional doubling rate `log c - H(Xₖ₊₁ | Xₖ, …, X₁)`. -/
theorem expectedLogWealth_propBet_succ_sub (P : StochasticProcess α) {c : ℝ} (hc : 0 < c)
    (k : ℕ) :
    expectedLogWealth P (fun _ => c) (propBet P) (k + 1) -
        expectedLogWealth P (fun _ => c) (propBet P) k = log c - P.condEntropyLast k := by
  rw [expectedLogWealth_propBet P hc, expectedLogWealth_propBet P hc,
    StochasticProcess.jointEntropy_eq_sum, StochasticProcess.jointEntropy_eq_sum, sum_range_succ]
  push_cast
  ring

/-- **(6.36)** If the process has entropy rate `H(𝒳)`, conditionally proportional betting has
`(1/n) E log Sₙ → log c - H(𝒳)`: the doubling rate and the entropy rate add up to `log c`. -/
theorem tendsto_expectedLogWealth_propBet (P : StochasticProcess α) {c : ℝ} (hc : 0 < c)
    {h : ℝ} (hP : P.HasEntropyRate h) :
    Tendsto (fun n : ℕ => expectedLogWealth P (fun _ => c) (propBet P) n / n) atTop
      (𝓝 (log c - h)) := by
  refine (tendsto_const_nhds.sub hP).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [expectedLogWealth_propBet P hc]
  field_simp

/-- **(6.49)–(6.50)** With `c`-for-`1` odds, every sequential strategy has
`(1/n) E log Sₙ ≤ log c - (1/n) H(X₁, …, Xₙ) ≤ log c - H(𝒳)`. Hence `log c - (1/n) E log Sₙ` is an
upper bound on the entropy rate `H(𝒳)` of a stationary process. -/
theorem expectedLogWealth_div_le (P : StochasticProcess α) {c : ℝ} (hc : 0 < c)
    (hbet : ∀ k y, IsPMF (bet k y)) {n : ℕ} (hn : 0 < n)
    (habs : AbsCont (P.law n) (seqBetProb bet n)) :
    expectedLogWealth P (fun _ => c) bet n / n ≤ log c - P.jointEntropy n / n ∧
      log c - P.jointEntropy n / n ≤ log c - P.entropyRate := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [div_le_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne', mul_comm]
    exact expectedLogWealth_le P hc hbet habs
  · have := P.mul_entropyRate_le_jointEntropy n
    rw [sub_le_sub_iff_left, le_div_iff₀ hn', mul_comm]
    exact this

end InfoTheory
