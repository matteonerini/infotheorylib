/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.BlahutArimoto
public import InfoTheoryLib.SourceCoding.Minimax

/-!
# Computing the channel capacity: the Blahut–Arimoto algorithm

The capacity is a double maximization: `C = sup_r max_q f(r, q)`, where
`f(r, q) = ∑ₓ ∑_y r(x) p(y|x) log (q(x|y) / r(x))`. For a fixed input distribution `r` the best
backward channel `q` is the posterior (Lemma 9.1), and for a fixed `q` the best `r` is
`r(x) ∝ ∏_y q(x|y)^{p(y|x)}`. Alternating the two steps from a positive `r⁽⁰⁾` gives input
distributions `r⁽ᵏ⁾` with `I(r⁽ᵏ⁾) ↑ C`.

## Main definitions

* `baCapObjective W r q`: the function `f(r, q)` of (9.39).
* `baCapUpdate W q`: the input distribution `r(x) ∝ exp (∑_y p(y|x) log q(x|y))`, (9.55).
* `baCapIter W r₀ k`: the iteration (9.48), (9.56).

## Main statements

* `baCapObjective_le_mutualInfoOf`, `baCapObjective_posterior`: Lemma 9.1.
* `baCapObjective_le_log_sum_exp`, `baCapObjective_baCapUpdate`: the `r` step is optimal.
* `mutualInfoOf_baCapIter_le_succ`: the values `I(r⁽ᵏ⁾)` increase.
* `sum_sub_mutualInfoOf_baCapIter_le`: Arimoto's bound `∑ₖ (C - I(r⁽ᵏ⁺¹⁾)) ≤ D(r* ‖ r⁽⁰⁾)`.
* `capacity_sub_mutualInfoOf_baCapIter_le`, `tendsto_mutualInfoOf_baCapIter`: `I(r⁽ᵏ⁾) → C`, with
  error at most `D(r* ‖ r⁽⁰⁾) / k`.
* `capacity_eq_sSup_pos`: Theorem 9.2, the capacity is a supremum over positive inputs.
* `baCapObjective_concaveOn`: `f` is concave, (9.106)–(9.109).

## Implementation notes

The book proves convergence from its general Theorem 9.5 and the concavity of `f`. We prove it
directly, by Arimoto's telescoping bound, which also gives the rate `1/k`. The product
`∏_y q(x|y)^{p(y|x)}` is written `exp (∑_y p(y|x) log q(x|y))`. Logarithms are natural.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 9.2.1 and 9.3.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β] {W : α → β → ℝ}

/-- **(9.39)** `f(r, q) = ∑ₓ ∑_y r(x) p(y|x) log (q(x|y) / r(x))`, for a backward channel
`q(x|y) = q y x`. -/
def baCapObjective (W : α → β → ℝ) (r : α → ℝ) (q : β → α → ℝ) : ℝ :=
  ∑ x, ∑ y, r x * W x y * log (q y x / r x)

/-- The exponent `∑_y p(y|x) log q(x|y)` of the `r` step. -/
def baCapExponent (W : α → β → ℝ) (q : β → α → ℝ) (x : α) : ℝ := ∑ y, W x y * log (q y x)

/-- **(9.55)** The input distribution `r(x) ∝ ∏_y q(x|y)^{p(y|x)}` that maximizes `f(·, q)`. -/
def baCapUpdate (W : α → β → ℝ) (q : β → α → ℝ) (x : α) : ℝ :=
  exp (baCapExponent W q x) / ∑ x', exp (baCapExponent W q x')

/-- **(9.48), (9.56)** The input distributions of the Blahut–Arimoto algorithm for the capacity:
`r⁽ᵏ⁺¹⁾` maximizes `f(·, q⁽ᵏ⁾)`, where `q⁽ᵏ⁾` is the posterior of `r⁽ᵏ⁾`. -/
def baCapIter (W : α → β → ℝ) (r₀ : α → ℝ) : ℕ → α → ℝ
  | 0 => r₀
  | k + 1 => baCapUpdate W (posterior (baCapIter W r₀ k) W)

lemma baCapUpdate_pos [Nonempty α] (q : β → α → ℝ) (x : α) : 0 < baCapUpdate W q x :=
  div_pos (exp_pos _) (sum_pos (fun _ _ => exp_pos _) univ_nonempty)

lemma baCapUpdate_isPMF [Nonempty α] (q : β → α → ℝ) : IsPMF (baCapUpdate W q) :=
  ⟨fun x => (baCapUpdate_pos q x).le, by
    simp only [baCapUpdate, ← sum_div]
    exact div_self (sum_pos (fun _ _ => exp_pos _) univ_nonempty).ne'⟩

variable {r₀ : α → ℝ}

lemma baCapIter_pos (hr₀ : IsPMF r₀) (h₀ : ∀ x, 0 < r₀ x) (k : ℕ) (x : α) :
    0 < baCapIter W r₀ k x := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hr₀)
  cases k with
  | zero => exact h₀ x
  | succ k => exact baCapUpdate_pos _ x

lemma baCapIter_isPMF (hr₀ : IsPMF r₀) (k : ℕ) : IsPMF (baCapIter W r₀ k) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hr₀)
  cases k with
  | zero => exact hr₀
  | succ k => exact baCapUpdate_isPMF _

/-! ### Lemma 9.1 -/

/-- **Lemma 9.1, (9.20)–(9.24).** `f(r, q) ≤ I(X; Y)` for every backward channel `q` that vanishes
only where `r(x) p(y|x)` does. -/
theorem baCapObjective_le_mutualInfoOf {r : α → ℝ} (hr : IsPMF r) (hW : IsChannel W)
    {q : β → α → ℝ} (hq : IsChannel q) (hqW : ∀ x y, q y x = 0 → r x * W x y = 0) :
    baCapObjective W r q ≤ mutualInfoOf r W :=
  sum_mul_log_div_le_mutualInfoOf hr hW hq hqW

/-- **Lemma 9.1, (9.15) and (9.17).** The posterior `q*(x|y)` attains the maximum
`f(r, q*) = I(X; Y)`. -/
theorem baCapObjective_posterior {r : α → ℝ} (hr : IsPMF r) (hW : IsChannel W) :
    baCapObjective W r (posterior r W) = mutualInfoOf r W :=
  sum_mul_log_posterior_eq hr hW

/-- The posterior is positive where `r(x) p(y|x)` is. -/
lemma posterior_pos {r : α → ℝ} (hr : IsPMF r) (hW : IsChannel W) {x : α} {y : β}
    (hx : 0 < r x) (hy : 0 < W x y) : 0 < posterior r W y x := by
  have ho : 0 < outDist r W y := (mul_pos hx hy).trans_le (jointOf_le_outDist hr hW x y)
  simp only [posterior, ho.ne', ↓reduceIte]
  exact div_pos (mul_pos hx hy) ho

/-! ### The `r` step -/

/-- `f(s, q) = ∑ₓ s(x) (∑_y p(y|x) log q(x|y) - log s(x))`, when `q` does not vanish where `s(x)
p(y|x) > 0`. -/
lemma baCapObjective_eq_sum {s : α → ℝ} (hs : IsPMF s) (hW : IsChannel W) {q : β → α → ℝ}
    (hq : ∀ x y, 0 < s x → 0 < W x y → q y x ≠ 0) :
    baCapObjective W s q = ∑ x, s x * (baCapExponent W q x - log (s x)) := by
  refine sum_congr rfl fun x _ => ?_
  rcases (hs.nonneg x).eq_or_lt with h0 | hpos
  · simp [← h0]
  have h : ∀ y, s x * W x y * log (q y x / s x) =
      s x * (W x y * log (q y x)) - s x * W x y * log (s x) := by
    intro y
    rcases ((hW x).nonneg y).eq_or_lt with hw | hw
    · simp [← hw]
    · rw [log_div (hq x y hpos hw) hpos.ne']
      ring
  rw [sum_congr rfl fun y _ => h y, sum_sub_distrib, ← mul_sum, ← sum_mul, ← mul_sum,
    (hW x).sum_eq_one, baCapExponent]
  ring

/-- **(9.51)–(9.55)** For a fixed `q`, `f(s, q) ≤ log ∑ₓ ∏_y q(x|y)^{p(y|x)}`. -/
theorem baCapObjective_le_log_sum_exp {s : α → ℝ} (hs : IsPMF s) (hW : IsChannel W)
    {q : β → α → ℝ} (hq : ∀ x y, 0 < s x → 0 < W x y → q y x ≠ 0) :
    baCapObjective W s q ≤ log (∑ x, exp (baCapExponent W q x)) := by
  rw [baCapObjective_eq_sum hs hW hq]
  exact sum_mul_sub_log_le_log_sum_exp hs _

/-- **(9.55)** The update attains the bound: `f(r', q) = log ∑ₓ ∏_y q(x|y)^{p(y|x)}`. -/
theorem baCapObjective_baCapUpdate [Nonempty α] (hW : IsChannel W) {q : β → α → ℝ}
    (hq : ∀ x y, 0 < W x y → q y x ≠ 0) :
    baCapObjective W (baCapUpdate W q) q = log (∑ x, exp (baCapExponent W q x)) := by
  have hZ : 0 < ∑ x, exp (baCapExponent W q x) := sum_pos (fun _ _ => exp_pos _) univ_nonempty
  rw [baCapObjective_eq_sum (baCapUpdate_isPMF q) hW fun x y _ hy => hq x y hy]
  have h : ∀ x, baCapUpdate W q x * (baCapExponent W q x - log (baCapUpdate W q x)) =
      baCapUpdate W q x * log (∑ x, exp (baCapExponent W q x)) := by
    intro x
    rw [baCapUpdate, log_div (exp_pos _).ne' hZ.ne', log_exp]
    ring
  rw [sum_congr rfl fun x _ => h x, ← sum_mul, (baCapUpdate_isPMF q).sum_eq_one, one_mul]

/-- The exponent of the posterior: `∑_y p(y|x) log q*(x|y) = log r(x) + D(p(·|x) ‖ p_Y)`. -/
lemma baCapExponent_posterior {r : α → ℝ} (hr : IsPMF r) (hW : IsChannel W) {x : α}
    (hx : 0 < r x) :
    baCapExponent W (posterior r W) x = log (r x) + relEntropyReal (W x) (outDist r W) := by
  have h : ∀ y, W x y * log (posterior r W y x) =
      W x y * log (r x) + W x y * log (W x y / outDist r W y) := by
    intro y
    rcases ((hW x).nonneg y).eq_or_lt with hw | hw
    · simp [← hw]
    have ho : 0 < outDist r W y := (mul_pos hx hw).trans_le (jointOf_le_outDist hr hW x y)
    simp only [posterior, ho.ne', ↓reduceIte]
    rw [log_div (mul_pos hx hw).ne' ho.ne', log_mul hx.ne' hw.ne', log_div hw.ne' ho.ne']
    ring
  rw [baCapExponent, sum_congr rfl fun y _ => h y, sum_add_distrib, ← sum_mul,
    (hW x).sum_eq_one, one_mul, relEntropyReal]

/-! ### Convergence -/

/-- The normalizing constant `Z⁽ᵏ⁾ = ∑ₓ ∏_y q⁽ᵏ⁾(x|y)^{p(y|x)}` of the `r` step. -/
abbrev baCapNorm (W : α → β → ℝ) (r₀ : α → ℝ) (k : ℕ) : ℝ :=
  ∑ x, exp (baCapExponent W (posterior (baCapIter W r₀ k) W) x)

omit [Fintype β] in
/-- `D(p ‖ q) = ∑ₓ p(x) (log p(x) - log q(x))` for a positive `q`. -/
lemma relEntropyReal_eq_sum_sub {p q : α → ℝ} (hq : ∀ x, 0 < q x) :
    relEntropyReal p q = ∑ x, p x * (log (p x) - log (q x)) := by
  refine sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (p x) 0 with h | h
  · simp [h]
  · rw [log_div h (hq x).ne']

section Iteration

variable (hr₀ : IsPMF r₀) (h₀ : ∀ x, 0 < r₀ x) (hW : IsChannel W)
include hr₀ h₀ hW


lemma posterior_baCapIter_ne_zero (k : ℕ) {x : α} {y : β} (hy : 0 < W x y) :
    posterior (baCapIter W r₀ k) W y x ≠ 0 :=
  (posterior_pos (baCapIter_isPMF hr₀ k) hW (baCapIter_pos hr₀ h₀ k x) hy).ne'

/-- `log Z⁽ᵏ⁾ ≤ I(r⁽ᵏ⁺¹⁾)`. -/
lemma log_zk_le (k : ℕ) : log (baCapNorm W r₀ k) ≤ mutualInfoOf (baCapIter W r₀ (k + 1)) W := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hr₀)
  rw [← baCapObjective_baCapUpdate hW fun x y hy => posterior_baCapIter_ne_zero hr₀ h₀ hW k hy]
  refine baCapObjective_le_mutualInfoOf (baCapIter_isPMF hr₀ (k + 1)) hW
    (posterior_isChannel (baCapIter_isPMF hr₀ k) hW) fun x y hq => ?_
  rcases ((hW x).nonneg y).eq_or_lt with hw | hw
  · simp [← hw]
  · exact absurd hq (posterior_baCapIter_ne_zero hr₀ h₀ hW k hw)

/-- **(9.10)–(9.13)** `I(r⁽ᵏ⁾) ≤ I(r⁽ᵏ⁺¹⁾)`. -/
theorem mutualInfoOf_baCapIter_le_succ (k : ℕ) :
    mutualInfoOf (baCapIter W r₀ k) W ≤ mutualInfoOf (baCapIter W r₀ (k + 1)) W := by
  have h := baCapObjective_le_log_sum_exp (baCapIter_isPMF (W := W) hr₀ k) hW
    (q := posterior (baCapIter W r₀ k) W) fun x y _ hy =>
      posterior_baCapIter_ne_zero hr₀ h₀ hW k hy
  rw [baCapObjective_posterior (baCapIter_isPMF hr₀ k) hW] at h
  exact h.trans (log_zk_le hr₀ h₀ hW k)

/-- `log r⁽ᵏ⁺¹⁾(x) - log r⁽ᵏ⁾(x) = D(p(·|x) ‖ p_Y⁽ᵏ⁾) - log Z⁽ᵏ⁾`. -/
lemma log_baCapIter_succ_sub (k : ℕ) (x : α) :
    log (baCapIter W r₀ (k + 1) x) - log (baCapIter W r₀ k x) =
      relEntropyReal (W x) (outDist (baCapIter W r₀ k) W) - log (baCapNorm W r₀ k) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hr₀)
  have hZ : 0 < baCapNorm W r₀ k := sum_pos (fun _ _ => exp_pos _) univ_nonempty
  change log (baCapUpdate W _ x) - _ = _
  rw [baCapUpdate, log_div (exp_pos _).ne' hZ.ne', log_exp,
    baCapExponent_posterior (baCapIter_isPMF hr₀ k) hW (baCapIter_pos hr₀ h₀ k x)]
  ring

/-- `∑ₓ r*(x) log (r⁽ᵏ⁺¹⁾(x) / r⁽ᵏ⁾(x)) ≥ I(r*) - log Z⁽ᵏ⁾`. -/
lemma sub_log_zk_le {rs : α → ℝ} (hrs : IsPMF rs) (k : ℕ) :
    mutualInfoOf rs W - log (baCapNorm W r₀ k) ≤
      ∑ x, rs x * (log (baCapIter W r₀ (k + 1) x) - log (baCapIter W r₀ k x)) := by
  have hr := baCapIter_isPMF hr₀ (W := W) k
  have habs : AbsCont (outDist rs W) (outDist (baCapIter W r₀ k) W) := by
    intro y hy
    have hzero := (sum_eq_zero_iff_of_nonneg fun x _ =>
      mul_nonneg (hr.nonneg x) ((hW x).nonneg y)).1 hy
    refine sum_eq_zero fun x _ => ?_
    have := hzero x (mem_univ x)
    rw [(mul_eq_zero.1 this).resolve_left (baCapIter_pos hr₀ h₀ k x).ne', mul_zero]
  have h := mutualInfoOf_le_sum_relEntropy hrs hW (outDist_isPMF hr hW) habs
  simp only [log_baCapIter_succ_sub hr₀ h₀ hW, mul_sub, sum_sub_distrib, ← sum_mul,
    hrs.sum_eq_one, one_mul]
  linarith

/-- **Arimoto's bound.** For every input distribution `r*`,
`∑_{k < N} (I(r*) - I(r⁽ᵏ⁺¹⁾)) ≤ D(r* ‖ r⁽⁰⁾)`. -/
theorem sum_sub_mutualInfoOf_baCapIter_le {rs : α → ℝ} (hrs : IsPMF rs) (N : ℕ) :
    ∑ k ∈ range N, (mutualInfoOf rs W - mutualInfoOf (baCapIter W r₀ (k + 1)) W) ≤
      relEntropyReal rs r₀ := by
  -- Each term is at most `∑ₓ r*(x) log (r⁽ᵏ⁺¹⁾(x) / r⁽ᵏ⁾(x))`, which telescopes.
  have h₁ : ∀ k ∈ range N, mutualInfoOf rs W - mutualInfoOf (baCapIter W r₀ (k + 1)) W ≤
      ∑ x, rs x * (log (baCapIter W r₀ (k + 1) x) - log (baCapIter W r₀ k x)) := fun k _ =>
    by linarith [sub_log_zk_le hr₀ h₀ hW hrs k, log_zk_le hr₀ h₀ hW k]
  refine (sum_le_sum h₁).trans ?_
  have h₂ : ∑ k ∈ range N, ∑ x, rs x * (log (baCapIter W r₀ (k + 1) x) -
      log (baCapIter W r₀ k x)) = ∑ x, rs x * (log (baCapIter W r₀ N x) - log (r₀ x)) := by
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [← mul_sum, sum_range_sub (fun k => log (baCapIter W r₀ k x))]
    rfl
  -- `D(r* ‖ r⁽ᴺ⁾) ≥ 0`.
  have h₃ := relEntropyReal_nonneg hrs (baCapIter_isPMF (W := W) hr₀ N)
    (fun x h => absurd h (baCapIter_pos hr₀ h₀ N x).ne')
  rw [relEntropyReal_eq_sum_sub (baCapIter_pos hr₀ h₀ N)] at h₃
  rw [h₂, relEntropyReal_eq_sum_sub h₀]
  have h₄ : ∑ x, rs x * (log (baCapIter W r₀ N x) - log (r₀ x)) =
      ∑ x, rs x * (log (rs x) - log (r₀ x)) - ∑ x, rs x * (log (rs x) -
        log (baCapIter W r₀ N x)) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  linarith

/-- **Convergence with rate.** `C - I(r⁽ᴺ⁾) ≤ D(r* ‖ r⁽⁰⁾) / N`, where `r*` achieves the capacity.
-/
theorem capacity_sub_mutualInfoOf_baCapIter_le {rs : α → ℝ} (hrs : IsPMF rs)
    (hC : mutualInfoOf rs W = capacity W) {N : ℕ} (hN : 0 < N) :
    capacity W - mutualInfoOf (baCapIter W r₀ N) W ≤ relEntropyReal rs r₀ / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : Monotone fun k => mutualInfoOf (baCapIter W r₀ k) W :=
    monotone_nat_of_le_succ (mutualInfoOf_baCapIter_le_succ hr₀ h₀ hW)
  have h₁ := sum_sub_mutualInfoOf_baCapIter_le hr₀ h₀ hW hrs N
  rw [hC] at h₁
  have h₂ : ∑ _k ∈ range N, (capacity W - mutualInfoOf (baCapIter W r₀ N) W) ≤
      ∑ k ∈ range N, (capacity W - mutualInfoOf (baCapIter W r₀ (k + 1)) W) :=
    sum_le_sum fun k hk => by
      have := hmono (show k + 1 ≤ N from mem_range.1 hk)
      linarith
  rw [sum_const, card_range, nsmul_eq_mul] at h₂
  rw [le_div_iff₀ hN']
  linarith

/-- **Section 9.3.2.** The Blahut–Arimoto algorithm started at a positive input distribution
converges: `I(r⁽ᵏ⁾) → C`. -/
theorem tendsto_mutualInfoOf_baCapIter :
    Tendsto (fun k => mutualInfoOf (baCapIter W r₀ k) W) atTop (𝓝 (capacity W)) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hr₀)
  obtain ⟨rs, hrs, hC⟩ := exists_capacity_eq hW
  have hlim : Tendsto (fun N : ℕ => capacity W - relEntropyReal rs r₀ / N) atTop
      (𝓝 (capacity W)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (relEntropyReal rs r₀)).const_sub
      (capacity W)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_
    (Eventually.of_forall fun k => mutualInfoOf_le_capacity (baCapIter_isPMF hr₀ k) hW)
  filter_upwards [eventually_gt_atTop 0] with N hN
  linarith [capacity_sub_mutualInfoOf_baCapIter_le hr₀ h₀ hW hrs hC hN]

end Iteration

/-- **Theorem 9.2, (9.26)–(9.38).** The capacity is the supremum of `I(X; Y)` over the positive
input distributions, and by Lemma 9.1 the inner maximum over `q` is `I(X; Y)`. -/
theorem capacity_eq_sSup_pos [Nonempty α] (hW : IsChannel W) :
    capacity W = sSup {I | ∃ r : α → ℝ, IsPMF r ∧ (∀ x, 0 < r x) ∧ mutualInfoOf r W = I} := by
  have hu : IsPMF (uniformPMF α) := uniformPMF_isPMF
  have hu₀ : ∀ x, 0 < uniformPMF α x := fun x => by
    simp [uniformPMF, Fintype.card_pos]
  have hbdd : BddAbove {I | ∃ r : α → ℝ, IsPMF r ∧ (∀ x, 0 < r x) ∧ mutualInfoOf r W = I} :=
    ⟨capacity W, by rintro _ ⟨r, hr, -, rfl⟩; exact mutualInfoOf_le_capacity hr hW⟩
  refine le_antisymm (le_of_tendsto' (tendsto_mutualInfoOf_baCapIter hu hu₀ hW) fun k =>
    le_csSup hbdd ⟨_, baCapIter_isPMF hu k, baCapIter_pos hu hu₀ k, rfl⟩) ?_
  exact csSup_le ⟨_, uniformPMF α, hu, hu₀, rfl⟩ fun _ ⟨r, hr, _, h⟩ =>
    h ▸ mutualInfoOf_le_capacity hr hW

/-! ### Concavity -/

/-- The two-point form of the concavity of `(a, b) ↦ a log (b / a)`, from the log sum inequality,
(9.107)–(9.108). -/
lemma mul_log_div_concave {a₁ a₂ b₁ b₂ l m : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁)
    (hb₂ : 0 < b₂) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    l * (a₁ * log (b₁ / a₁)) + m * (a₂ * log (b₂ / a₂)) ≤
      (l * a₁ + m * a₂) * log ((l * b₁ + m * b₂) / (l * a₁ + m * a₂)) := by
  have hls := log_sum_inequality univ (a := ![l * a₁, m * a₂]) (b := ![l * b₁, m * b₂])
    (fun i _ => by
      fin_cases i
      · exact mul_nonneg hl ha₁.le
      · exact mul_nonneg hm ha₂.le)
    (fun i _ => by
      fin_cases i
      · exact mul_nonneg hl hb₁.le
      · exact mul_nonneg hm hb₂.le)
    (fun i _ h => by
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at h ⊢
        rcases mul_eq_zero.1 h with h | h
        · simp [h]
        · exact absurd h hb₁.ne'
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h ⊢
        rcases mul_eq_zero.1 h with h | h
        · simp [h]
        · exact absurd h hb₂.ne')
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hls
  have e : ∀ {l a b : ℝ}, 0 < a → 0 < b → 0 ≤ l → l * a * log (l * a / (l * b)) =
      l * (a * log (a / b)) := by
    intro l a b ha hb hl
    rcases hl.eq_or_lt with h | h
    · simp [← h]
    · rw [mul_div_mul_left _ _ h.ne']
      ring
  rw [e ha₁ hb₁ hl, e ha₂ hb₂ hm] at hls
  have flip : ∀ a b : ℝ, a * log (b / a) = -(a * log (a / b)) := fun a b => by
    rw [← inv_div, log_inv]
    ring
  rw [flip a₁, flip a₂, flip]
  linarith

/-- The domain of `f`: positive input distributions and backward channels positive where
`p(y|x) > 0`, the cone over the sets (9.40)–(9.41). -/
def baCapDomain (W : α → β → ℝ) : Set ((α → ℝ) × (β → α → ℝ)) :=
  {z | (∀ x, 0 < z.1 x) ∧ ∀ x y, 0 < W x y → 0 < z.2 y x}

omit [Fintype α] [Fintype β] in
lemma convex_baCapDomain : Convex ℝ (baCapDomain W) := by
  rintro z₁ ⟨h₁, h₁'⟩ z₂ ⟨h₂, h₂'⟩ a b ha hb hab
  have key : ∀ {p q : ℝ}, 0 < p → 0 < q → 0 < a * p + b * q := fun {p q} hp hq => by
    nlinarith [min_le_left p q, min_le_right p q, lt_min hp hq]
  exact ⟨fun x => by simpa using key (h₁ x) (h₂ x),
    fun x y hy => by simpa using key (h₁' x y hy) (h₂' x y hy)⟩

/-- **(9.106)–(9.109)** `f(r, q)` is concave. -/
theorem baCapObjective_concaveOn (hW : ∀ x y, 0 ≤ W x y) :
    ConcaveOn ℝ (baCapDomain W) fun z => baCapObjective W z.1 z.2 := by
  refine ⟨convex_baCapDomain, fun z₁ ⟨h₁, h₁'⟩ z₂ ⟨h₂, h₂'⟩ a b ha hb _ => ?_⟩
  simp only [baCapObjective, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rcases (hW x y).eq_or_lt with hw | hw
  · simp [← hw]
  have := mul_log_div_concave (h₁ x) (h₂ x) (h₁' x y hw) (h₂' x y hw) ha hb
  have e : ∀ r q : ℝ, r * W x y * log (q / r) = W x y * (r * log (q / r)) := fun r q => by ring
  rw [e, e, e]
  nlinarith

end InfoTheory
