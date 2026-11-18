/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Investment.Causal

/-!
# Universal portfolios

For an individual sequence `x₁, …, xₙ` of market vectors, with no statistical assumption, compare
a causal strategy with the best constant rebalanced portfolio in hindsight,
`Sₙ*(xⁿ) = max_b ∏ᵢ bᵗxᵢ` (Section 16.7). Expanding the product of sums,
`∏ᵢ bᵗxᵢ = ∑_{jⁿ} w(jⁿ) x(jⁿ)` with `w(jⁿ) = ∏ᵢ b_{jᵢ}` and `x(jⁿ) = ∏ᵢ x_{i jᵢ}`,
(16.105)–(16.107): an `n`-day market is a one-day market with `mⁿ` assets. Any pmf `ŵ` on the
sequences `jⁿ` is achieved by a causal strategy, which bets on each day in proportion to the
wealth so far of the sequences continuing with each stock, (16.132)–(16.134).

The best constant rebalanced portfolio puts at most `w*(jⁿ) = ∏ᵢ (n_{jᵢ}/n)` on `jⁿ`, where `n_k` is
the number of occurrences of `k` in `jⁿ`. Betting `ŵ = Vₙ w*` achieves `Ŝₙ ≥ Vₙ Sₙ*` on every
sequence, and on the extremal sequences, with one nonzero stock each day, no causal strategy does
better (Theorem 16.7.1).

## Main definitions

* `crpWealth b xs`: **(16.91)** the wealth `Sₙ(b, xⁿ) = ∏ᵢ bᵗxᵢ` of a constant rebalanced
  portfolio.
* `seqReturn xs j`: **(16.106)** the return `x(jⁿ) = ∏ᵢ x_{i jᵢ}` of the sequence `jⁿ` of stocks.
* `occ j k`: the number of occurrences of stock `k` in `jⁿ`.
* `bestWeight j`: **(16.111)–(16.112)** `w*(jⁿ) = ∏ᵢ (n_{jᵢ}/n)`.
* `minimaxRatio n m`: **(16.95), (16.114)** `Vₙ = (∑_{jⁿ} w*(jⁿ))⁻¹`.
* `weightStrategy w`: **(16.132)** the causal strategy betting the weights `w` on the sequences.

## Main statements

* `ratio_sum_ge`: **Lemma 16.7.1**.
* `crpWealth_eq_sum`: **(16.105)–(16.107)**.
* `prod_le_bestWeight`: **(16.110)–(16.113)** `∏ᵢ b_{jᵢ} ≤ w*(jⁿ)`.
* `stratWealth_weightStrategy`: **(16.132)–(16.134)** the wealth of `weightStrategy w` is
  `∑_{jⁿ} w(jⁿ) x(jⁿ)`.
* `le_stratWealth_of_weights`: **Lemma 16.7.2**, if `ŵ ≥ c w*` then `Ŝₙ ≥ c Sₙ*`.
* `exists_universal`, `exists_extremal_le`, `minimax_universal`: **Theorem 16.7.1**, (16.94).
* `stratWealth_mixture`: **(16.141)–(16.146)** for a finite mixture of constant rebalanced
  portfolios, the universal portfolio earns the mixture of their wealths.
* `minimaxRatio_two_one`: the example `n = 1`, `m = 2` of Section 16.7.1.

## Implementation notes

The market vectors are arbitrary nonnegative vectors (zeros allowed), and the strategies are
`CausalStrategy m (Fin m → ℝ)`, whose outcomes are the market vectors themselves. Ratios are stated
multiplicatively: `Ŝₙ ≥ Vₙ Sₙ(b)` for every constant rebalanced portfolio `b` means
`Ŝₙ/Sₙ* ≥ Vₙ`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 16.7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {m n : ℕ}

/-- **Lemma 16.7.1, (16.96)–(16.98).** `∑ᵢ pᵢ / ∑ᵢ qᵢ ≥ minᵢ pᵢ/qᵢ`: if `c qᵢ ≤ pᵢ` for all `i`,
then `c ∑ᵢ qᵢ ≤ ∑ᵢ pᵢ`; and for positive `qᵢ` some `pᵢ/qᵢ` is at most `∑ᵢ pᵢ / ∑ᵢ qᵢ`. -/
theorem ratio_sum_ge {α : Type*} (s : Finset α) (p q : α → ℝ) :
    (∀ c, (∀ i ∈ s, c * q i ≤ p i) → c * ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) ∧
      (s.Nonempty → (∀ i ∈ s, 0 < q i) →
        ∃ i ∈ s, p i / q i ≤ (∑ i ∈ s, p i) / ∑ i ∈ s, q i) := by
  refine ⟨fun c h => by rw [mul_sum]; exact sum_le_sum h, fun hs hq => ?_⟩
  by_contra hne
  push Not at hne
  have hQ : 0 < ∑ i ∈ s, q i := sum_pos hq hs
  set c := (∑ i ∈ s, p i) / ∑ i ∈ s, q i
  have h1 : ∀ i ∈ s, c * q i < p i := fun i hi => by
    have := hne i hi
    rwa [lt_div_iff₀ (hq i hi)] at this
  have h2 : c * ∑ i ∈ s, q i < ∑ i ∈ s, p i := by
    rw [mul_sum]
    exact sum_lt_sum_of_nonempty hs h1
  rw [div_mul_cancel₀ _ hQ.ne'] at h2
  exact lt_irrefl _ h2

/-! ### Sequences of stocks -/

/-- **(16.91)** The wealth `Sₙ(b, xⁿ) = ∏ᵢ bᵗxᵢ` of the constant rebalanced portfolio `b`. -/
def crpWealth (b : Fin m → ℝ) (xs : Fin n → Fin m → ℝ) : ℝ := ∏ i, wealthRel b (xs i)

/-- **(16.106)** The return `x(jⁿ) = ∏ᵢ x_{i jᵢ}` of the sequence of stocks `jⁿ`. -/
def seqReturn (xs : Fin n → Fin m → ℝ) (j : Fin n → Fin m) : ℝ := ∏ i, xs i (j i)

/-- The number `n_k` of occurrences of the stock `k` in the sequence `jⁿ`. -/
def occ (j : Fin n → Fin m) (k : Fin m) : ℕ := #(univ.filter fun i => j i = k)

/-- **(16.111)–(16.112)** `w*(jⁿ) = ∏ᵢ (n_{jᵢ}/n) = ∏ₖ (n_k/n)^{n_k}`, the largest weight that a
constant rebalanced portfolio puts on `jⁿ`. -/
def bestWeight (j : Fin n → Fin m) : ℝ := ∏ i, (occ j (j i) : ℝ) / n

/-- **(16.95), (16.114)** `Vₙ = (∑_{jⁿ} w*(jⁿ))⁻¹ = (∑_{n₁+⋯+nₘ=n} (n choose n₁, …, nₘ)
∏ₖ (n_k/n)^{n_k})⁻¹`. -/
def minimaxRatio (n m : ℕ) : ℝ := (∑ j : Fin n → Fin m, bestWeight j)⁻¹

lemma seqReturn_nonneg {xs : Fin n → Fin m → ℝ} (hxs : ∀ i k, 0 ≤ xs i k) (j : Fin n → Fin m) :
    0 ≤ seqReturn xs j :=
  prod_nonneg fun i _ => hxs i (j i)

lemma bestWeight_pos (j : Fin n → Fin m) : 0 < bestWeight j := by
  refine prod_pos fun i _ => div_pos ?_ ?_
  · exact_mod_cast card_pos.2 ⟨i, by simp⟩
  · exact_mod_cast Fin.pos i

lemma minimaxRatio_mul_sum (n m : ℕ) [Nonempty (Fin n → Fin m)] :
    minimaxRatio n m * ∑ j : Fin n → Fin m, bestWeight j = 1 := by
  have : 0 < ∑ j : Fin n → Fin m, bestWeight j :=
    sum_pos (fun j _ => bestWeight_pos j) univ_nonempty
  rw [minimaxRatio, inv_mul_cancel₀ this.ne']

/-- The wealth relative of the market vector with a single nonzero stock `k`, of return `1`. -/
lemma wealthRel_pi_single (b : Fin m → ℝ) (k : Fin m) : wealthRel b (Pi.single k 1) = b k := by
  simp [wealthRel, Pi.single_apply]

/-- **(16.105)–(16.107)** `∏ᵢ bᵗxᵢ = ∑_{jⁿ} (∏ᵢ b_{jᵢ}) x(jⁿ)`: the wealth of a constant rebalanced
portfolio as an investment on the sequences of stocks. -/
theorem crpWealth_eq_sum (b : Fin m → ℝ) (xs : Fin n → Fin m → ℝ) :
    crpWealth b xs = ∑ j : Fin n → Fin m, (∏ i, b (j i)) * seqReturn xs j := by
  simp only [crpWealth, wealthRel, seqReturn, ← prod_mul_distrib]
  exact Fintype.prod_sum fun i k => b k * xs i k

/-- `∑ᵢ f(jᵢ) = ∑ₖ n_k f(k)`. -/
lemma sum_comp_eq_sum_occ (j : Fin n → Fin m) (f : Fin m → ℝ) :
    ∑ i, f (j i) = ∑ k, (occ j k : ℝ) * f k := by
  classical
  rw [← sum_fiberwise univ j (fun i => f (j i))]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, nsmul_eq_mul]
  rfl

lemma sum_occ (j : Fin n → Fin m) : ∑ k, (occ j k : ℝ) = n := by
  have := sum_comp_eq_sum_occ j fun _ => 1
  simpa using this.symm

/-- **(16.110)–(16.113)** The weight `∏ᵢ b_{jᵢ} = ∏ₖ b_k^{n_k}` of a constant rebalanced portfolio
on the sequence `jⁿ` is at most `w*(jⁿ)`, attained by the empirical distribution `b = (n_k/n)`. -/
theorem prod_le_bestWeight {b : Fin m → ℝ} (hb : IsPMF b) (j : Fin n → Fin m) :
    ∏ i, b (j i) ≤ bestWeight j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [bestWeight]
  by_cases h0 : ∃ i, b (j i) = 0
  · obtain ⟨i, hi⟩ := h0
    rw [prod_eq_zero (mem_univ i) hi]
    exact (bestWeight_pos j).le
  push Not at h0
  have hpos : ∀ i, 0 < b (j i) := fun i => (hb.nonneg _).lt_of_ne (h0 i).symm
  have hocc : ∀ i, (0 : ℝ) < occ j (j i) := fun i => by
    exact_mod_cast card_pos.2 ⟨i, by simp⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp : ∀ i, 0 < (occ j (j i) : ℝ) / n := fun i => div_pos (hocc i) hn
  rw [bestWeight, ← log_le_log_iff (prod_pos fun i _ => hpos i) (prod_pos fun i _ => hp i),
    log_prod fun i _ => (hpos i).ne', log_prod fun i _ => (hp i).ne', ← sub_nonpos,
    ← sum_sub_distrib]
  -- `∑ᵢ log (b_{jᵢ}/p_{jᵢ}) ≤ ∑ᵢ (b_{jᵢ}/p_{jᵢ} - 1) = ∑_{n_k > 0} (n b_k - n_k) ≤ 0`.
  calc ∑ i, (log (b (j i)) - log ((occ j (j i) : ℝ) / n))
      ≤ ∑ i, (b (j i) / ((occ j (j i) : ℝ) / n) - 1) := sum_le_sum fun i _ => by
        rw [← log_div (hpos i).ne' (hp i).ne']
        exact log_le_sub_one_of_pos (div_pos (hpos i) (hp i))
    _ = ∑ k, (occ j k : ℝ) * (b k / ((occ j k : ℝ) / n) - 1) :=
        sum_comp_eq_sum_occ j fun k => b k / ((occ j k : ℝ) / n) - 1
    _ = ∑ k, ((if occ j k = 0 then 0 else n * b k) - occ j k) := sum_congr rfl fun k _ => by
        split_ifs with hk
        · simp [hk]
        · have : (occ j k : ℝ) ≠ 0 := by exact_mod_cast hk
          field_simp
    _ ≤ ∑ k, (n * b k - occ j k) := sum_le_sum fun k _ => by
        split_ifs
        · nlinarith [hb.nonneg k]
        · exact le_rfl
    _ = 0 := by rw [sum_sub_distrib, ← mul_sum, hb.sum_eq_one, sum_occ]; ring

/-- The empirical distribution `(n_k/n)` of the stocks in `jⁿ`. -/
def empiricalPortfolio (j : Fin n → Fin m) (k : Fin m) : ℝ := (occ j k : ℝ) / n

lemma empiricalPortfolio_isPMF (hn : 0 < n) (j : Fin n → Fin m) :
    IsPMF (empiricalPortfolio j) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun k => div_nonneg (Nat.cast_nonneg _) hn'.le, ?_⟩
  simp only [empiricalPortfolio, ← sum_div, sum_occ, div_self hn'.ne']

/-! ### Betting on sequences of stocks -/

/-- The return `∏_{l < i} y_l(j_l)` of the first `i` days of the sequence of stocks `j`. -/
def prefixReturn {i : ℕ} (hi : i ≤ n) (j : Fin n → Fin m) (ys : Fin i → Fin m → ℝ) : ℝ :=
  ∏ l, ys l (j (Fin.castLE hi l))

/-- The wealth `∑_{jⁿ} w(jⁿ) ∏_{l < i} y_l(j_l)` after `i` days of the investment `w` on the
sequences of stocks. -/
def prefixWealth (w : (Fin n → Fin m) → ℝ) {i : ℕ} (hi : i ≤ n) (ys : Fin i → Fin m → ℝ) : ℝ :=
  ∑ j, w j * prefixReturn hi j ys

/-- **(16.132)** The causal strategy betting the weights `w` on the sequences of stocks: on day `i`,
the fraction of the wealth on stock `k` is the share of the current wealth of the sequences with
`jᵢ = k`. When the current wealth is `0`, or after day `n`, it uses the portfolio `b₀`. -/
def weightStrategy (w : (Fin n → Fin m) → ℝ) (b₀ : Fin m → ℝ) :
    CausalStrategy m (Fin m → ℝ) := fun i ys =>
  if hi : i < n then
    if prefixWealth w hi.le ys = 0 then b₀ else
      fun k => (∑ j, if j ⟨i, hi⟩ = k then w j * prefixReturn hi.le j ys else 0) /
        prefixWealth w hi.le ys
  else b₀

variable {w : (Fin n → Fin m) → ℝ}

lemma prefixReturn_nonneg {i : ℕ} (hi : i ≤ n) (j : Fin n → Fin m) {ys : Fin i → Fin m → ℝ}
    (hys : ∀ l k, 0 ≤ ys l k) : 0 ≤ prefixReturn hi j ys :=
  prod_nonneg fun l _ => hys l _

lemma prefixWealth_nonneg (hw : ∀ j, 0 ≤ w j) {i : ℕ} (hi : i ≤ n) {ys : Fin i → Fin m → ℝ}
    (hys : ∀ l k, 0 ≤ ys l k) : 0 ≤ prefixWealth w hi ys :=
  sum_nonneg fun j _ => mul_nonneg (hw j) (prefixReturn_nonneg hi j hys)

lemma weightStrategy_isValid (hw : ∀ j, 0 ≤ w j) {b₀ : Fin m → ℝ} (hb₀ : IsPMF b₀) {i : ℕ}
    (ys : Fin i → Fin m → ℝ) (hys : ∀ l k, 0 ≤ ys l k) : IsPMF (weightStrategy w b₀ i ys) := by
  unfold weightStrategy
  split_ifs with hi hA
  · exact hb₀
  · have hA' : 0 < prefixWealth w hi.le ys :=
      (prefixWealth_nonneg hw hi.le hys).lt_of_ne (Ne.symm hA)
    refine ⟨fun k => div_nonneg (sum_nonneg fun j _ => ?_) hA'.le, ?_⟩
    · split_ifs
      · exact mul_nonneg (hw j) (prefixReturn_nonneg _ j hys)
      · exact le_rfl
    · rw [← sum_div, sum_comm]
      simp only [sum_ite_eq, mem_univ, ↓reduceIte]
      exact div_self hA
  · exact hb₀

lemma prefixReturn_snoc {i : ℕ} (hi : i + 1 ≤ n) (j : Fin n → Fin m)
    (ys : Fin (i + 1) → Fin m → ℝ) :
    prefixReturn hi j ys =
      prefixReturn (Nat.le_of_succ_le hi) j (Fin.init ys) * ys (Fin.last i) (j ⟨i, hi⟩) := by
  rw [prefixReturn, Fin.prod_univ_castSucc]
  rfl

/-- **(16.132)–(16.134)** After `i ≤ n` days, the wealth of `weightStrategy w` is the wealth
`∑_{jⁿ} w(jⁿ) ∏_{l < i} y_l(j_l)` of the investment `w` on the sequences of stocks. -/
theorem stratWealth_weightStrategy_prefix (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (b₀ : Fin m → ℝ) :
    ∀ (i : ℕ) (hi : i ≤ n) (ys : Fin i → Fin m → ℝ), (∀ l k, 0 ≤ ys l k) →
      stratWealth (weightStrategy w b₀) id i ys = prefixWealth w hi ys := by
  intro i
  induction i with
  | zero =>
    intro hi ys _
    simp [prefixWealth, prefixReturn, hw1]
  | succ i ih =>
    intro hi ys hys
    have hi' : i < n := hi
    have hinit : ∀ l k, 0 ≤ Fin.init ys l k := fun l k => hys _ k
    rw [stratWealth, ih (Nat.le_of_succ_le hi) _ hinit]
    simp only [id]
    -- Regroup the sequences by the stock of day `i`.
    have hregroup : prefixWealth w hi ys = ∑ k, ys (Fin.last i) k *
        ∑ j, if j ⟨i, hi'⟩ = k then w j * prefixReturn hi'.le j (Fin.init ys) else 0 := by
      simp only [prefixWealth, prefixReturn_snoc hi, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_eq_single (j ⟨i, hi'⟩) (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
      simp only [↓reduceIte]
      ring
    rw [hregroup]
    unfold weightStrategy
    simp only [hi', ↓reduceDIte]
    split_ifs with hA
    · -- All the sequences have lost their wealth.
      have hz : ∀ j, w j * prefixReturn hi'.le j (Fin.init ys) = 0 := fun j =>
        (sum_eq_zero_iff_of_nonneg fun j _ =>
          mul_nonneg (hw j) (prefixReturn_nonneg _ j hinit)).1 hA j (mem_univ j)
      simp only [hA, zero_mul, hz, ite_self, sum_const_zero, mul_zero]
    · simp only [wealthRel]
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      field_simp

/-- **(16.132)–(16.134)** The wealth of `weightStrategy w` after `n` days is
`∑_{jⁿ} w(jⁿ) x(jⁿ)`. -/
theorem stratWealth_weightStrategy (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (b₀ : Fin m → ℝ)
    (xs : Fin n → Fin m → ℝ) (hxs : ∀ i k, 0 ≤ xs i k) :
    stratWealth (weightStrategy w b₀) id n xs = ∑ j, w j * seqReturn xs j := by
  rw [stratWealth_weightStrategy_prefix hw hw1 b₀ n le_rfl xs hxs]
  rfl

/-- **Lemma 16.7.2, (16.147)–(16.155).** If the causal investor puts at least `c w*(jⁿ)` on every
sequence of stocks, then `Ŝₙ ≥ c Sₙ(b)` for every constant rebalanced portfolio `b`:
`Ŝₙ/Sₙ* ≥ c`. -/
theorem le_stratWealth_of_weights (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (b₀ : Fin m → ℝ)
    {c : ℝ} (hc : ∀ j, c * bestWeight j ≤ w j) (xs : Fin n → Fin m → ℝ)
    (hxs : ∀ i k, 0 ≤ xs i k) {b : Fin m → ℝ} (hb : IsPMF b) (hc0 : 0 ≤ c) :
    c * crpWealth b xs ≤ stratWealth (weightStrategy w b₀) id n xs := by
  rw [stratWealth_weightStrategy hw hw1 b₀ xs hxs, crpWealth_eq_sum, mul_sum]
  refine sum_le_sum fun j _ => ?_
  have h1 := prod_le_bestWeight hb j
  have h2 := seqReturn_nonneg hxs j
  calc c * ((∏ i, b (j i)) * seqReturn xs j) ≤ c * (bestWeight j * seqReturn xs j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) hc0
    _ = c * bestWeight j * seqReturn xs j := by ring
    _ ≤ w j * seqReturn xs j := mul_le_mul_of_nonneg_right (hc j) h2

/-- **Theorem 16.7.1 (lower bound), (16.116)–(16.120).** The causal strategy betting
`ŵ(jⁿ) = Vₙ w*(jⁿ)` achieves `Ŝₙ(xⁿ) ≥ Vₙ Sₙ(b, xⁿ)` for every market sequence and every
constant rebalanced portfolio: `Ŝₙ/Sₙ* ≥ Vₙ`. -/
theorem exists_universal (hm : 0 < m) :
    ∃ β : CausalStrategy m (Fin m → ℝ), (∀ i ys, (∀ l k, 0 ≤ ys l k) → IsPMF (β i ys)) ∧
      ∀ xs : Fin n → Fin m → ℝ, (∀ i k, 0 ≤ xs i k) → ∀ b, IsPMF b →
        minimaxRatio n m * crpWealth b xs ≤ stratWealth β id n xs := by
  set w : (Fin n → Fin m) → ℝ := fun j => minimaxRatio n m * bestWeight j
  have hV : 0 ≤ minimaxRatio n m := inv_nonneg.2 (sum_nonneg fun j _ => (bestWeight_pos j).le)
  have hw : ∀ j, 0 ≤ w j := fun j => mul_nonneg hV (bestWeight_pos j).le
  have : Nonempty (Fin n → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
  have hw1 : ∑ j, w j = 1 := by rw [← mul_sum, minimaxRatio_mul_sum]
  refine ⟨weightStrategy w (Pi.single ⟨0, hm⟩ 1), fun i ys hys =>
    weightStrategy_isValid hw (isPMF_single _) ys hys, fun xs hxs b hb => ?_⟩
  exact le_stratWealth_of_weights hw hw1 _ (fun j => le_rfl) xs hxs hb hV

/-! ### Extremal sequences -/

/-- **(16.121)** The extremal market sequence in which only stock `jᵢ` has a nonzero return, `1`,
on day `i`. -/
def extremalSeq (j : Fin n → Fin m) : Fin n → Fin m → ℝ := fun i => Pi.single (j i) 1

/-- **(16.123)** On the extremal sequences, the wealths of a causal strategy sum to `1`. -/
theorem sum_stratWealth_extremal {β : CausalStrategy m (Fin m → ℝ)}
    (hβ : ∀ i ys, (∀ l k, 0 ≤ ys l k) → IsPMF (β i ys)) :
    ∀ n, ∑ j : Fin n → Fin m, stratWealth β id n (extremalSeq j) = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_snoc]
    have e : ∀ (j : Fin n → Fin m) (k : Fin m),
        extremalSeq (Fin.snoc j k : Fin (n + 1) → Fin m) =
          Fin.snoc (extremalSeq j) (Pi.single k 1) := fun j k => by
      funext i
      refine Fin.lastCases ?_ (fun l => ?_) i
      · simp [extremalSeq]
      · simp [extremalSeq]
    simp only [e, stratWealth_snoc, id, wealthRel_pi_single]
    rw [← ih]
    refine sum_congr rfl fun j _ => ?_
    have hval : IsPMF (β n (extremalSeq j)) := hβ n _ fun l k => by
      simp only [extremalSeq, Pi.single_apply]
      split_ifs <;> norm_num
    rw [← mul_sum, hval.sum_eq_one, mul_one]

/-- **(16.125)** On the extremal sequence of `jⁿ`, the empirical portfolio of `jⁿ` earns
`w*(jⁿ)`. -/
lemma crpWealth_extremal (j : Fin n → Fin m) :
    crpWealth (empiricalPortfolio j) (extremalSeq j) = bestWeight j := by
  simp only [crpWealth, extremalSeq, wealthRel_pi_single, bestWeight, empiricalPortfolio]

/-- **Theorem 16.7.1 (upper bound), (16.121)–(16.131).** No causal strategy does better than `Vₙ`
in the worst case: on some extremal sequence, `Ŝₙ ≤ Vₙ Sₙ*`, with `Sₙ*` the wealth of the
empirical portfolio of the sequence. -/
theorem exists_extremal_le (hn : 0 < n) {β : CausalStrategy m (Fin m → ℝ)}
    (hβ : ∀ i ys, (∀ l k, 0 ≤ ys l k) → IsPMF (β i ys)) :
    ∃ j : Fin n → Fin m, IsPMF (empiricalPortfolio j) ∧
      stratWealth β id n (extremalSeq j) ≤
        minimaxRatio n m * crpWealth (empiricalPortfolio j) (extremalSeq j) := by
  by_contra hne
  push Not at hne
  have hlt : ∀ j : Fin n → Fin m,
      minimaxRatio n m * bestWeight j < stratWealth β id n (extremalSeq j) := fun j => by
    rw [← crpWealth_extremal]
    exact hne j (empiricalPortfolio_isPMF hn j)
  have hne : Nonempty (Fin n → Fin m) := by
    rcases isEmpty_or_nonempty (Fin n → Fin m) with h | h
    · have := sum_stratWealth_extremal hβ n
      simp at this
    · exact h
  have hne' : (univ : Finset (Fin n → Fin m)).Nonempty := univ_nonempty
  have := sum_lt_sum_of_nonempty hne' fun j _ => hlt j
  rw [← mul_sum, minimaxRatio_mul_sum, sum_stratWealth_extremal hβ n] at this
  exact lt_irrefl _ this

/-- **Theorem 16.7.1, (16.94).** `max_{b̂} min_{xⁿ} Ŝₙ(xⁿ)/Sₙ*(xⁿ) = Vₙ`: some causal strategy
achieves `Ŝₙ ≥ Vₙ Sₙ(b)` on every sequence and for every constant rebalanced portfolio `b`, and
for every causal strategy some sequence and some `b` have `Ŝₙ ≤ Vₙ Sₙ(b)`. -/
theorem minimax_universal (hm : 0 < m) (hn : 0 < n) :
    (∃ β : CausalStrategy m (Fin m → ℝ), (∀ i ys, (∀ l k, 0 ≤ ys l k) → IsPMF (β i ys)) ∧
      ∀ xs : Fin n → Fin m → ℝ, (∀ i k, 0 ≤ xs i k) → ∀ b, IsPMF b →
        minimaxRatio n m * crpWealth b xs ≤ stratWealth β id n xs) ∧
    ∀ β : CausalStrategy m (Fin m → ℝ), (∀ i ys, (∀ l k, 0 ≤ ys l k) → IsPMF (β i ys)) →
      ∃ xs : Fin n → Fin m → ℝ, (∀ i k, 0 ≤ xs i k) ∧ ∃ b, IsPMF b ∧
        stratWealth β id n xs ≤ minimaxRatio n m * crpWealth b xs := by
  refine ⟨exists_universal hm, fun β hβ => ?_⟩
  obtain ⟨j, hj, h⟩ := exists_extremal_le hn hβ
  refine ⟨extremalSeq j, fun i k => ?_, _, hj, h⟩
  simp only [extremalSeq, Pi.single_apply]
  split_ifs <;> norm_num

/-! ### Mixtures of constant rebalanced portfolios -/

/-- **(16.141)–(16.146)** For a finite mixture `μ` of constant rebalanced portfolios `b_a`, the
causal strategy betting the mixed weights `∑ₐ μₐ ∏ᵢ b_{a,jᵢ}` on the sequences of stocks earns the
mixture `∑ₐ μₐ Sₙ(b_a, xⁿ)` of the wealths. -/
theorem stratWealth_mixture {A : Type*} [Fintype A] {μ : A → ℝ} (hμ : IsPMF μ)
    {bs : A → Fin m → ℝ} (hbs : ∀ a, IsPMF (bs a)) (b₀ : Fin m → ℝ) (xs : Fin n → Fin m → ℝ)
    (hxs : ∀ i k, 0 ≤ xs i k) :
    stratWealth (weightStrategy (fun j : Fin n → Fin m => ∑ a, μ a * ∏ i, bs a (j i)) b₀) id n xs =
      ∑ a, μ a * crpWealth (bs a) xs := by
  have hw : ∀ j : Fin n → Fin m, 0 ≤ ∑ a, μ a * ∏ i, bs a (j i) := fun j =>
    sum_nonneg fun a _ => mul_nonneg (hμ.nonneg a) (prod_nonneg fun i _ => (hbs a).nonneg _)
  have hw1 : ∑ j : Fin n → Fin m, ∑ a, μ a * ∏ i, bs a (j i) = 1 := by
    rw [sum_comm]
    simp only [← mul_sum]
    have : ∀ a, ∑ j : Fin n → Fin m, ∏ i, bs a (j i) = 1 := fun a => by
      rw [← Fintype.prod_sum fun (i : Fin n) k => bs a k]
      simp [(hbs a).sum_eq_one]
    simp only [this, mul_one, hμ.sum_eq_one]
  rw [stratWealth_weightStrategy hw hw1 b₀ xs hxs]
  simp only [crpWealth_eq_sum, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun j _ => by ring

/-! ### An example -/

/-- **Section 16.7.1** For one day and two stocks, `1/V₁ = 2`: the best strategy puts half of the
wealth on each stock, and it earns at least half of the best stock. (The book prints `Vₙ = 2`
here.) -/
theorem minimaxRatio_two_one : minimaxRatio 1 2 = 1 / 2 := by
  have h : ∀ j : Fin 1 → Fin 2, bestWeight j = 1 := fun j => by
    simp only [bestWeight, occ, Fin.prod_univ_one]
    rw [filter_true_of_mem fun i _ => by rw [Subsingleton.elim i 0]]
    simp
  simp only [minimaxRatio, h, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin]
  norm_num

end InfoTheory
