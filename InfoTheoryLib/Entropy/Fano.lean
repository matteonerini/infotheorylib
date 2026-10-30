/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.MarkovChain.DataProcessing

/-!
# Fano's inequality

Let `X̂` be an estimate of `X` computed from an observation `Y`, so that `X → Y → X̂` is a Markov
chain, with probability of error `Pₑ = Pr{X̂ ≠ X}`. The estimator may be random (a random variable
on the same space as `X` and `Y`), and its alphabet `𝒳̂` may be larger than the alphabet `𝒳` of
`X`: we take `𝒳 ⊆ 𝒳̂` through an injection `ι : 𝒳 → 𝒳̂`.

## Main definitions

* `estErrProb μ X X̂ ι`: the probability of error `Pₑ = Pr{X̂ ≠ X}` of an estimator `X̂`.
* `errProb μ X Y g`: the probability of error `Pr{g(Y) ≠ X}` of a deterministic estimator
  `X̂ = g(Y)` with values in `𝒳`.
* `errRV X Y g`: the error indicator `E = 1{g(Y) ≠ X}`.

## Main statements

* `fano_estimator`: Theorem 2.10.1, `H(Pₑ) + Pₑ log |𝒳| ≥ H(X | X̂) ≥ H(X | Y)`.
* `fano_estimator_weak`, `fano_estimator_lower_bound`: the weakened forms (2.131)–(2.132),
  `1 + Pₑ log |𝒳| ≥ H(X | Y)` and `Pₑ ≥ (H(X | Y) - 1) / log |𝒳|` (in bits).
* `fano_of_eq`: Corollary (2.139), `H(p) + p log |𝒳| ≥ H(X | Y)` for `p = Pr{X ≠ Y}`.
* `fano`: Corollary (2.140), `H(Pₑ) + Pₑ log (|𝒳| - 1) ≥ H(X | Y)` for `X̂ = g(Y) ∈ 𝒳`, with the
  weakened forms `fano_weak`, `fano_lower_bound`.
* `condEntropy_eq_zero_iff`: `H(X | Y) = 0` iff `X` is a function of `Y`.
* `fano_no_side_info`, `fano_sharp`: (2.143)–(2.144), Fano's inequality is sharp.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.10
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

open Classical in
/-- The probability of error `Pₑ = Pr{X̂ ≠ X}` (2.129) of the deterministic estimate `X̂ = g(Y)`
of `X`. -/
def errProb (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (g : β → α) : ℝ :=
  ∑ ω, if g (Y ω) ≠ X ω then μ ω else 0

open Classical in
/-- The error random variable `E = 1` if `X̂ ≠ X` and `E = 0` if `X̂ = X` (2.133). -/
def errRV (X : Ω → α) (Y : Ω → β) (g : β → α) : Ω → Bool := fun ω => decide (g (Y ω) ≠ X ω)

omit [Fintype α] [Fintype β] in
lemma dist_errRV_true (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    dist μ (errRV X Y g) true = errProb μ X Y g := by
  classical
  simp [dist, errRV, errProb]

omit [Fintype α] [Fintype β] in
lemma dist_errRV_false {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    dist μ (errRV X Y g) false = 1 - errProb μ X Y g := by
  have := (hμ.dist (errRV X Y g)).sum_eq_one
  rw [Fintype.sum_bool, dist_errRV_true] at this
  linarith

omit [Fintype α] [Fintype β] in
lemma errProb_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    0 ≤ errProb μ X Y g := by
  rw [← dist_errRV_true]; exact dist_nonneg hμ _ _

omit [Fintype α] [Fintype β] in
lemma errProb_le_one {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    errProb μ X Y g ≤ 1 := by
  rw [← dist_errRV_true]; exact (hμ.dist _).le_one _

omit [Fintype α] [Fintype β] in
/-- Since `E` is a binary random variable, `H(E) = H(Pₑ)`. -/
lemma entropy_errRV {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    H[errRV X Y g ; μ] = binEntropy (errProb μ X Y g) := by
  rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_bool, dist_errRV_true,
    dist_errRV_false hμ, binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_comm]

/-- The bound `H(X | E, Y) ≤ Pₑ log (|𝒳| - 1)` (2.141)–(2.142). Given `E = 0`, `X = g(Y)`; given
`E = 1`, `X` takes one of the `|𝒳| - 1` values different from `g(Y)`. -/
lemma condEntropy_given_err_le {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (g : β → α) :
    H[X | pair (errRV X Y g) Y ; μ] ≤ errProb μ X Y g * log ((Fintype.card α : ℝ) - 1) := by
  classical
  set E := errRV X Y g
  rw [condEntropy, Fintype.sum_prod_type, Fintype.sum_bool, ← dist_errRV_true,
    ← sum_dist_pair_right μ E Y true, sum_mul, ← add_zero (∑ y, _ * log _)]
  refine add_le_add (sum_le_sum fun y _ => ?_) (le_of_eq (sum_eq_zero fun y _ => ?_))
  · -- given `E = 1` and `Y = y`, `X ≠ g y`
    rcases (dist_nonneg hμ (pair E Y) (true, y)).eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ h.le
      have hcond := condDist_isPMF hμ X (pair E Y) h.ne'
      have hsupp : ∀ x ∉ univ.erase (g y), condDist μ X (pair E Y) (true, y) x = 0 := by
        intro x hx
        have hx : x = g y := by simpa using hx
        simp only [condDist]
        rw [dist_eq_zero_of_forall_ne μ (fun ω hω => ?_), zero_div]
        simp only [pair_apply, Prod.mk.injEq, E, errRV] at hω
        obtain ⟨⟨h1, h2⟩, h3⟩ := hω
        rw [h2, h3, hx] at h1
        simp at h1
      have := entropy_le_log_card_of_support hcond _ hsupp
      rw [card_erase_of_mem (mem_univ _), card_univ] at this
      have hpos : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨g y⟩
      rw [Nat.cast_sub hpos, Nat.cast_one] at this
      exact this
  · -- given `E = 0` and `Y = y`, `X = g y`
    rcases (dist_nonneg hμ (pair E Y) (false, y)).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · have hcond := condDist_isPMF hμ X (pair E Y) h.ne'
      have hsupp : ∀ x ∉ ({g y} : Finset α), condDist μ X (pair E Y) (false, y) x = 0 := by
        intro x hx
        have hx : x ≠ g y := by simpa using hx
        simp only [condDist]
        rw [dist_eq_zero_of_forall_ne μ (fun ω hω => ?_), zero_div]
        simp only [pair_apply, Prod.mk.injEq, E, errRV] at hω
        obtain ⟨⟨h1, h2⟩, h3⟩ := hω
        rw [h2, h3] at h1
        simp only [ne_eq, decide_eq_false_iff_not, not_not] at h1
        exact hx h1.symm
      have h1 := entropy_le_log_card_of_support hcond _ hsupp
      rw [card_singleton, Nat.cast_one, log_one] at h1
      have h2 := entropy_nonneg hcond
      rw [condEntropyAt, le_antisymm h1 h2, mul_zero]

omit [Fintype α] [Fintype β] in
lemma errProb_eq_zero_iff {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    errProb μ X Y g = 0 ↔ ∀ ω, μ ω ≠ 0 → X ω = g (Y ω) := by
  rw [errProb, sum_eq_zero_iff_of_nonneg fun ω _ => by split_ifs <;> simp [hμ.nonneg ω]]
  refine forall_congr' fun ω => ?_
  simp only [mem_univ, true_implies, ite_eq_right_iff]
  constructor
  · intro h hω; by_contra hne; exact hω (h (Ne.symm hne))
  · intro h hne; by_contra hω; exact hne (h hω).symm

/-! ### Fano's inequality for an arbitrary estimator -/

open Classical in
/-- **(2.129)** The probability of error `Pₑ = Pr{X̂ ≠ X}` of an estimator `X̂` of `X`. The alphabet
`𝒳` of `X` is included in the alphabet `𝒳̂` of `X̂` through the injection `ι`. -/
def estErrProb (μ : Ω → ℝ) (X : Ω → α) (Xhat : Ω → γ) (ι : α → γ) : ℝ :=
  ∑ ω, if Xhat ω ≠ ι (X ω) then μ ω else 0

open Classical in
/-- The error random variable `E = 1{X̂ ≠ X}` (2.133) of an estimator `X̂`. -/
def estErrRV (X : Ω → α) (Xhat : Ω → γ) (ι : α → γ) : Ω → Bool :=
  fun ω => decide (Xhat ω ≠ ι (X ω))

omit [Fintype α] [Fintype γ] in
lemma dist_estErrRV_true (μ : Ω → ℝ) (X : Ω → α) (Xhat : Ω → γ) (ι : α → γ) :
    dist μ (estErrRV X Xhat ι) true = estErrProb μ X Xhat ι := by
  classical
  simp [dist, estErrRV, estErrProb]

omit [Fintype α] [Fintype γ] in
lemma dist_estErrRV_false {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Xhat : Ω → γ) (ι : α → γ) :
    dist μ (estErrRV X Xhat ι) false = 1 - estErrProb μ X Xhat ι := by
  have := (hμ.dist (estErrRV X Xhat ι)).sum_eq_one
  rw [Fintype.sum_bool, dist_estErrRV_true] at this
  linarith

omit [Fintype α] [Fintype γ] in
lemma estErrProb_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Xhat : Ω → γ) (ι : α → γ) :
    0 ≤ estErrProb μ X Xhat ι := by
  rw [← dist_estErrRV_true]; exact dist_nonneg hμ _ _

omit [Fintype α] [Fintype γ] in
/-- `H(E) = H(Pₑ)` for the error indicator of an estimator. -/
lemma entropy_estErrRV {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Xhat : Ω → γ) (ι : α → γ) :
    H[estErrRV X Xhat ι ; μ] = binEntropy (estErrProb μ X Xhat ι) := by
  rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_bool, dist_estErrRV_true,
    dist_estErrRV_false hμ, binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_comm]

/-- **(2.136)** `H(X | E, X̂) ≤ Pₑ log |𝒳|`. Given `E = 0`, `X̂ = X` determines `X`; given `E = 1`,
the conditional entropy is at most the log of the number of possible outcomes. -/
lemma condEntropy_given_estErr_le {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Xhat : Ω → γ)
    {ι : α → γ} (hι : Function.Injective ι) :
    H[X | pair (estErrRV X Xhat ι) Xhat ; μ] ≤
      estErrProb μ X Xhat ι * log (Fintype.card α) := by
  classical
  set E := estErrRV X Xhat ι
  rw [condEntropy, Fintype.sum_prod_type, Fintype.sum_bool, ← dist_estErrRV_true,
    ← sum_dist_pair_right μ E Xhat true, sum_mul, ← add_zero (∑ y, _ * log _)]
  refine add_le_add (sum_le_sum fun y _ => ?_) (le_of_eq (sum_eq_zero fun y _ => ?_))
  · -- given `E = 1`, the conditional entropy is at most `log |𝒳|`
    rcases (dist_nonneg hμ (pair E Xhat) (true, y)).eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left
        (entropy_le_log_card (condDist_isPMF hμ X (pair E Xhat) h.ne')) h.le
  · -- given `E = 0` and `X̂ = y`, `X` is the unique `x` with `ι x = y`
    rcases (dist_nonneg hμ (pair E Xhat) (false, y)).eq_or_lt with h | h
    · rw [← h, zero_mul]
    · have hcond := condDist_isPMF hμ X (pair E Xhat) h.ne'
      set S := univ.filter fun a => ι a = y
      have hS : S.card ≤ 1 := card_le_one.2 fun a ha b hb => by
        simp only [S, mem_filter, mem_univ, true_and] at ha hb
        exact hι (ha.trans hb.symm)
      have hsupp : ∀ x ∉ S, condDist μ X (pair E Xhat) (false, y) x = 0 := by
        intro x hx
        simp only [S, mem_filter, mem_univ, true_and] at hx
        simp only [condDist]
        rw [dist_eq_zero_of_forall_ne μ (fun ω hω => ?_), zero_div]
        simp only [pair_apply, Prod.mk.injEq, E, estErrRV] at hω
        obtain ⟨⟨h1, h2⟩, h3⟩ := hω
        simp only [ne_eq, decide_eq_false_iff_not, not_not] at h1
        exact hx (h3 ▸ h2 ▸ h1.symm)
      have h1 := entropy_le_log_card_of_support hcond S hsupp
      have hlog : log (S.card : ℝ) ≤ 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h0 | h0 <;> simp [h0]
      rw [condEntropyAt, le_antisymm (h1.trans hlog) (entropy_nonneg hcond), mul_zero]

/-- **(2.137)** For any estimator `X̂` of `X`, `H(Pₑ) + Pₑ log |𝒳| ≥ H(X | X̂)`. -/
theorem condEntropy_le_estErrProb {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Xhat : Ω → γ)
    {ι : α → γ} (hι : Function.Injective ι) :
    H[X | Xhat ; μ] ≤ binEntropy (estErrProb μ X Xhat ι) +
      estErrProb μ X Xhat ι * log (Fintype.card α) := by
  classical
  set E := estErrRV X Xhat ι
  -- `H(E, X | X̂) = H(X | X̂) + H(E | X, X̂)` with `H(E | X, X̂) = 0` (2.134)
  have h1 := chain_rule_cond hμ X E Xhat
  have h0 : H[E | pair X Xhat ; μ] = 0 :=
    condEntropy_comp_self hμ (pair X Xhat) (fun z => decide (z.2 ≠ ι z.1))
  -- `H(E, X | X̂) = H(E | X̂) + H(X | E, X̂)` (2.135)
  have h2 := chain_rule_cond hμ E X Xhat
  have hswap : H[pair X E | Xhat ; μ] = H[pair E X | Xhat ; μ] :=
    condEntropy_congr_left hμ Xhat Prod.swap Prod.swap_injective (fun _ => rfl)
  -- `H(E | X̂) ≤ H(E) = H(Pₑ)` and `H(X | E, X̂) ≤ Pₑ log |𝒳|`
  have h3 := condEntropy_le_entropy hμ E Xhat
  have h4 := condEntropy_given_estErr_le hμ X Xhat hι
  rw [entropy_estErrRV hμ] at h3
  linarith

/-- **Theorem 2.10.1 (Fano's inequality) (2.130).** For any estimator `X̂` such that
`X → Y → X̂`, with `Pₑ = Pr(X ≠ X̂)`, `H(Pₑ) + Pₑ log |𝒳| ≥ H(X | X̂) ≥ H(X | Y)`. The estimator
may be random, and its alphabet may be larger than `𝒳`. -/
theorem fano_estimator {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Xhat : Ω → γ)
    {ι : α → γ} (hι : Function.Injective ι) (h : MarkovChain μ X Y Xhat) :
    H[X | Y ; μ] ≤ H[X | Xhat ; μ] ∧
      H[X | Xhat ; μ] ≤ binEntropy (estErrProb μ X Xhat ι) +
        estErrProb μ X Xhat ι * log (Fintype.card α) := by
  refine ⟨?_, condEntropy_le_estErrProb hμ X Xhat hι⟩
  -- the data-processing inequality `I(X; X̂) ≤ I(X; Y)` (2.138)
  have := data_processing hμ h
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_eq_entropy_sub_condEntropy hμ] at this
  linarith

omit [Fintype γ] in
/-- **Fano's inequality, weakened form (2.131).** In nats: `log 2 + Pₑ log |𝒳| ≥ H(X|Y)`. -/
theorem fano_estimator_weak [Finite γ] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Xhat : Ω → γ) {ι : α → γ} (hι : Function.Injective ι) (h : MarkovChain μ X Y Xhat) :
    H[X | Y ; μ] ≤ log 2 + estErrProb μ X Xhat ι * log (Fintype.card α) := by
  have := Fintype.ofFinite γ
  obtain ⟨h1, h2⟩ := fano_estimator hμ X Y Xhat hι h
  linarith [binEntropy_le_log_two (p := estErrProb μ X Xhat ι)]

omit [Fintype γ] in
/-- **Fano's inequality, weakened form (2.131)**, in bits: `1 + Pₑ log₂ |𝒳| ≥ H(X|Y)`. -/
theorem fano_estimator_weak_bits [Finite γ] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Xhat : Ω → γ) {ι : α → γ} (hι : Function.Injective ι) (h : MarkovChain μ X Y Xhat) :
    H[X | Y ; μ] / log 2 ≤ 1 + estErrProb μ X Xhat ι * (log (Fintype.card α) / log 2) := by
  have h2 := log_two_pos'
  rw [div_le_iff₀ h2, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ h2.ne']
  linarith [fano_estimator_weak hμ X Y Xhat hι h]

omit [Fintype γ] in
/-- **Fano's inequality (2.132).** `Pₑ ≥ (H(X|Y) - 1) / log |𝒳|` (in bits; the ratio is the same
in nats with `1` replaced by `log 2`). -/
theorem fano_estimator_lower_bound [Finite γ] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Xhat : Ω → γ) {ι : α → γ} (hι : Function.Injective ι) (h : MarkovChain μ X Y Xhat)
    (hα : 2 ≤ Fintype.card α) :
    (H[X | Y ; μ] / log 2 - 1) / (log (Fintype.card α) / log 2) ≤ estErrProb μ X Xhat ι := by
  have h2 := log_two_pos'
  have hc : 0 < log (Fintype.card α) := log_pos (by exact_mod_cast hα)
  rw [div_le_iff₀ (div_pos hc h2)]
  linarith [fano_estimator_weak_bits hμ X Y Xhat hι h]

/-! ### Estimators with values in `𝒳` -/

/-- **Corollary (2.140) of Theorem 2.10.1 (Fano's inequality).** For an estimator `X̂ = g(Y)` with
values in `𝒳` and `Pₑ = Pr{X̂ ≠ X}`, `H(Pₑ) + Pₑ log (|𝒳| - 1) ≥ H(X|Y)`. -/
theorem fano {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    H[X | Y ; μ] ≤ binEntropy (errProb μ X Y g) +
      errProb μ X Y g * log ((Fintype.card α : ℝ) - 1) := by
  classical
  set E := errRV X Y g
  -- `H(E, X | Y) = H(X | Y) + H(E | X, Y)` with `H(E | X, Y) = 0` (2.134)
  have h1 := chain_rule_cond hμ X E Y
  have h0 : H[E | pair X Y ; μ] = 0 := by
    have := condEntropy_comp_self hμ (pair X Y) (fun z => decide (g z.2 ≠ z.1))
    exact this
  -- `H(E, X | Y) = H(E | Y) + H(X | E, Y)` (2.135)
  have h2 := chain_rule_cond hμ E X Y
  have hswap : H[pair X E | Y ; μ] = H[pair E X | Y ; μ] :=
    condEntropy_congr_left hμ Y Prod.swap Prod.swap_injective (fun _ => rfl)
  -- `H(E | Y) ≤ H(E) = H(Pₑ)` and `H(X | E, Y) ≤ Pₑ log (|𝒳| - 1)`
  have h3 := condEntropy_le_entropy hμ E Y
  have h4 := condEntropy_given_err_le hμ X Y g
  rw [entropy_errRV hμ] at h3
  linarith

/-- **Corollary (2.139).** For any two random variables `X` and `Y` with values in `𝒳`, let
`p = Pr(X ≠ Y)`. Then `H(p) + p log |𝒳| ≥ H(X|Y)`. -/
theorem fano_of_eq {μ : Ω → ℝ} (hμ : IsPMF μ) (X Y : Ω → α) :
    H[X | Y ; μ] ≤ binEntropy (errProb μ X Y id) + errProb μ X Y id * log (Fintype.card α) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hμ.dist X))
  have h := fano hμ X Y id
  have h2 := mul_le_mul_of_nonneg_left (log_card_sub_one_le_log_card (α := α))
    (errProb_nonneg hμ X Y id)
  linarith

/-- **Fano's inequality, weakened form (2.131)**, for a deterministic estimator `g(Y)`. In nats:
`log 2 + Pₑ log |𝒳| ≥ H(X|Y)`. -/
theorem fano_weak {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    H[X | Y ; μ] ≤ log 2 + errProb μ X Y g * log (Fintype.card α) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hμ.dist X))
  have h := fano hμ X Y g
  have h1 := binEntropy_le_log_two (p := errProb μ X Y g)
  have h2 := mul_le_mul_of_nonneg_left (log_card_sub_one_le_log_card (α := α))
    (errProb_nonneg hμ X Y g)
  linarith

/-- **Fano's inequality, weakened form (2.131)**, in bits: `1 + Pₑ log₂ |𝒳| ≥ H(X|Y)`. -/
theorem fano_weak_bits {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    H[X | Y ; μ] / log 2 ≤ 1 + errProb μ X Y g * (log (Fintype.card α) / log 2) := by
  have h2 := log_two_pos'
  rw [div_le_iff₀ h2, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ h2.ne']
  linarith [fano_weak hμ X Y g]

/-- **Fano's inequality (2.132)** for a deterministic estimator `g(Y)`:
`Pₑ ≥ (H(X|Y) - 1) / log |𝒳|` (in bits). -/
theorem fano_lower_bound {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (g : β → α)
    (hα : 2 ≤ Fintype.card α) :
    (H[X | Y ; μ] / log 2 - 1) / (log (Fintype.card α) / log 2) ≤ errProb μ X Y g := by
  have h2 := log_two_pos'
  have hc : 0 < log (Fintype.card α) := log_pos (by exact_mod_cast hα)
  rw [div_le_iff₀ (div_pos hc h2)]
  linarith [fano_weak_bits hμ X Y g]

/-- **Remark after Theorem 2.10.1.** `Pₑ = 0` implies `H(X|Y) = 0`. -/
theorem condEntropy_eq_zero_of_errProb_eq_zero {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α)
    (Y : Ω → β) (g : β → α) (h : errProb μ X Y g = 0) : H[X | Y ; μ] = 0 := by
  have := fano hμ X Y g
  rw [h, binEntropy_zero, zero_mul, add_zero] at this
  have h' : 0 ≤ H[X | Y ; μ] := by
    have := condEntropy_eq_sub hμ X Y
    rw [condEntropy, ← sum_const_zero (s := (univ : Finset β))] 
    refine sum_le_sum fun y _ => mul_nonneg (dist_nonneg hμ _ _) ?_
    rcases (dist_nonneg hμ Y y).eq_or_lt with hy | hy
    · simp [condEntropyAt, condDist, ← hy, entropy]
    · exact entropy_nonneg (condDist_isPMF hμ X Y hy.ne')
  linarith

/-- **Section 2.10 (Problem 2.5).** `H(X|Y) = 0` iff `X` is a function of `Y` (with
probability `1`). Hence `X` can be estimated from `Y` with zero probability of error iff
`H(X|Y) = 0`. -/
theorem condEntropy_eq_zero_iff {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[X | Y ; μ] = 0 ↔ ∃ g : β → α, ∀ ω, μ ω ≠ 0 → X ω = g (Y ω) := by
  classical
  constructor
  · intro h
    have hterm : ∀ y, dist μ Y y * condEntropyAt μ X Y y = 0 := by
      have hnn : ∀ y ∈ univ, 0 ≤ dist μ Y y * condEntropyAt μ X Y y := fun y _ => by
        rcases (dist_nonneg hμ Y y).eq_or_lt with hy | hy
        · rw [← hy, zero_mul]
        · exact mul_nonneg hy.le (entropy_nonneg (condDist_isPMF hμ X Y hy.ne'))
      exact fun y => (sum_eq_zero_iff_of_nonneg hnn).1 h y (mem_univ y)
    have hdet : ∀ y, 0 < dist μ Y y → ∃ a, ∀ x, condDist μ X Y y x = if x = a then 1 else 0 :=
      fun y hy => (entropy_eq_zero_iff (condDist_isPMF hμ X Y hy.ne')).1
        ((mul_eq_zero.1 (hterm y)).resolve_left hy.ne')
    obtain ⟨ω₀⟩ := Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)
    refine ⟨fun y => if hy : 0 < dist μ Y y then (hdet y hy).choose else X ω₀,
      fun ω hω => ?_⟩
    have hω' : 0 < μ ω := lt_of_le_of_ne (hμ.nonneg ω) (Ne.symm hω)
    have hy := dist_pos hμ Y hω'
    simp only [hy, ↓reduceDIte]
    have hspec := (hdet (Y ω) hy).choose_spec (X ω)
    have hpos : 0 < condDist μ X Y (Y ω) (X ω) := condDist_pos hμ X Y hω'
    by_contra hne
    simp only [hne, ite_false] at hspec
    linarith
  · rintro ⟨g, hg⟩
    exact condEntropy_eq_zero_of_errProb_eq_zero hμ X Y g ((errProb_eq_zero_iff hμ X Y g).2 hg)

/-- **Remark (no knowledge of `Y`).** Guessing `X` by a constant `a` has error probability
`Pₑ = 1 - p(a)` (minimized by the most likely value, `best_guess`), and Fano's inequality reads
`H(Pₑ) + Pₑ log (|𝒳| - 1) ≥ H(X)` (2.143). -/
theorem fano_no_side_info {p : α → ℝ} (hp : IsPMF p) (a : α) :
    entropy p ≤ binEntropy (1 - p a) + (1 - p a) * log ((Fintype.card α : ℝ) - 1) := by
  classical
  have h := fano (μ := p) hp id (fun _ => ()) (fun _ => a)
  rw [condEntropy_const hp, entropyRV, dist_id] at h
  have he : errProb p id (fun _ => ()) (fun _ => a) = 1 - p a := by
    have : ∀ x, (if a ≠ x then p x else 0) = p x - (if a = x then p x else 0) := by
      intro x; by_cases h : a = x <;> simp [h]
    simp only [errProb, id]
    rw [sum_congr rfl fun x _ => this x, sum_sub_distrib, hp.sum_eq_one, sum_ite_eq]
    simp
  rwa [he] at h

omit [Fintype α] in
/-- The best constant guess is the most likely value: `1 - p(a) ≤ 1 - p(c)` whenever `p(a) ≥ p(c)`
for all `c`. -/
lemma best_guess {p : α → ℝ} {a : α} (ha : ∀ c, p c ≤ p a) (c : α) : 1 - p a ≤ 1 - p c := by
  linarith [ha c]

/-- The pmf `(1 - Pₑ, Pₑ/(m-1), …, Pₑ/(m-1))` on `m = k + 1` points (2.144). -/
def fanoPMF (k : ℕ) (Pe : ℝ) : Fin (k + 1) → ℝ := fun i => if i = 0 then 1 - Pe else Pe / k

/-- **Remark (sharpness) (2.144).** The pmf `(1 - Pₑ, Pₑ/(m-1), …)`
achieves Fano's bound with equality: `H(X) = H(Pₑ) + Pₑ log (m - 1)`, where `Pₑ = 1 - p(1)` is
the error probability of the guess `X̂ = 1`. Thus Fano's inequality is sharp. -/
theorem fano_sharp {k : ℕ} (hk : 0 < k) {Pe : ℝ} (h0 : 0 ≤ Pe) (h1 : Pe ≤ 1) :
    IsPMF (fanoPMF k Pe) ∧ 1 - fanoPMF k Pe 0 = Pe ∧
      entropy (fanoPMF k Pe) =
        binEntropy Pe + Pe * log ((Fintype.card (Fin (k + 1)) : ℝ) - 1) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : ∀ i : Fin k, fanoPMF k Pe i.succ = Pe / k := fun i => by
    simp [fanoPMF, Fin.succ_ne_zero]
  have e0 : fanoPMF k Pe 0 = 1 - Pe := by simp [fanoPMF]
  refine ⟨⟨fun i => ?_, ?_⟩, by rw [e0]; ring, ?_⟩
  · simp only [fanoPMF]; split_ifs
    · linarith
    · positivity
  · rw [Fin.sum_univ_succ]
    simp only [e, e0, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · rw [entropy_eq_sum_negMulLog, Fin.sum_univ_succ]
    simp only [e, e0, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, add_sub_cancel_right]
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    rcases h0.eq_or_lt with rfl | hpos
    · simp
    · simp only [negMulLog]
      rw [log_div hpos.ne' hk']
      field_simp
      ring

end InfoTheory
