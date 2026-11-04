/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.CoverThomas.Chapter3
public import InfoTheoryLib.MarkovChain.RandomWalk
public import InfoTheoryLib.StochasticProcess.HiddenMarkov
public import InfoTheoryLib.StochasticProcess.Independent
public import InfoTheoryLib.MarkovChain.SecondLaw

/-!
# Cover & Thomas, Chapter 4: Entropy Rates of a Stochastic Process

This file indexes the formalization of Chapter 4 of [cover2006] and contains the chapter's worked
examples. The general theory lives in the topic modules of `InfoTheoryLib`. The list below gives
each numbered result with the declaration that proves it, and the last section of this file
defines aliases `theorem_4_2_1`, … for them.

The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Processes.** A stochastic process is given by its finite-dimensional laws
  (`StochasticProcess`), with time indexed from `0`; the book's `Xₙ` is the coordinate `n - 1`.
  `condEntropyLast n` is the book's `H(Xₙ₊₁ | Xₙ, …, X₁)`.
* **Markov chains.** A time-invariant chain is `markovProcess μ r`, with initial distribution `μ`
  and transition matrix `r a b = Pr{Xₙ₊₁ = b | Xₙ = a}`. In Section 4.4 the law of the state at
  time `n` is `(step r)^[n] μ`, and the law of `(X₀, Xₙ)` is `jointOf μ (transPow r n)`.
* **Logarithms.** Entropies and entropy rates are in nats.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 4.1 Markov chains
* Stochastic processes, (4.1) stationarity: `StochasticProcess`, `StochasticProcess.IsStationary`,
  `StochasticProcess.IsStationary.dist_shift` (`StochasticProcess.Basic`).
* (4.2)–(4.4) Markov chains: `markovLaw`, `markovLaw_snoc`, `markovProcess`
  (`StochasticProcess.Markov`).
* Irreducible and aperiodic chains: `IsIrreducible`, `IsAperiodic`, `isAperiodic_of_pos`
  (`StochasticProcess.Markov`).
* (4.5) and stationary distributions: `dist_markovLaw_last`, `IsStationaryDist`,
  `markovProcess_isStationary` (`StochasticProcess.Markov`, `MarkovChain.Process`).
* Example 4.1.1, (4.6)–(4.9): `example_4_1_1_balance`, `example_4_1_1`,
  `example_4_1_1_entropy` (here).

### 4.2 Entropy rate
* (4.10) and (4.14): `StochasticProcess.HasEntropyRate`, `StochasticProcess.HasCondEntropyRate`
  (`StochasticProcess.Basic`).
* Examples 1–3: `uniformProcess_hasEntropyRate`, `iidProcess_hasEntropyRate` (4.11),
  `jointEntropy_indepProcess` (4.12) (`StochasticProcess.Independent`), and the process (4.13)
  without an entropy rate, `example_4_2_no_entropy_rate` (here).
* Theorems 4.2.1–4.2.3: `StochasticProcess.IsStationary.hasEntropyRate`,
  `StochasticProcess.IsStationary.condEntropyLast_antitone`,
  `StochasticProcess.IsStationary.hasCondEntropyRate`, `cesaro_mean`, with the chain rule
  (4.22) `StochasticProcess.jointEntropy_eq_sum` (`StochasticProcess.Basic`).
* (4.25)–(4.26), Theorem 4.2.4: `markovProcess_condEntropyLast`, `IsStationaryDist`,
  `markovProcess_hasEntropyRate`, `sum_mul_entropy_eq` (`StochasticProcess.Markov`).
* Example 4.2.1, (4.28): `example_4_2_1` (here).
* Remark after Example 4.2.1: `markovProcess_hasEntropyRate_of_tendsto`
  (`StochasticProcess.Markov`).

### 4.3 Example: entropy rate of a random walk on a weighted graph
* (4.29)–(4.42): `nodeWeight`, `totalWeight`, `walkMatrix`, `walkStationary_isStationaryDist`,
  `walk_entropy_rate`, `walk_entropy_rate_unweighted` (`MarkovChain.RandomWalk`).
* Example 4.3.1: `example_4_3_1_degrees`, `example_4_3_1_stationary`, `example_4_3_1_rate`,
  `example_4_3_1_approx`, and the rook `example_4_3_1_rook` (here).
* Remark, (4.43) and its converse: `walk_isReversible`, `markovLaw_comp_rev`,
  `exists_walk_of_isReversible` (`MarkovChain.RandomWalk`).

### 4.4 Second law of thermodynamics
* Interpretation 1, (4.44)–(4.45): `relEntropy_step_le`, `relEntropy_iterate_antitone`
  (`MarkovChain.SecondLaw`).
* Interpretation 2, (4.46): `relEntropy_stationary_antitone`, `relEntropy_stationary_tendsto`.
* Interpretation 3, (4.47): `entropy_iterate_monotone`, with the counterexample
  `entropy_can_decrease` (here).
* (4.48)–(4.49) and Remark: `IsDoublyStochastic`, `uniform_stationary_iff`
  (`MarkovChain.Process`).
* Interpretation 4, (4.50)–(4.55): `entropy_stationary_const`, `condEntropy_stationary_monotone`
  (`MarkovChain.SecondLaw`), and for any Markov chain `condEntropy_initial_monotone`.
* Interpretation 5, (4.56): `entropy_shuffle`, `entropy_shuffle_deck` (`MarkovChain.SecondLaw`).

### 4.5 Functions of Markov chains
* Lemma 4.5.1, (4.57)–(4.64): `hmmLower_le_hmmUpper`, `hmmLower_le_entropyRate`
  (`StochasticProcess.HiddenMarkov`).
* Lemma 4.5.2, (4.65)–(4.72): `hmmUpper_sub_hmmLower`, `tendsto_hmmUpper_sub_hmmLower`.
* Theorem 4.5.1, (4.73)–(4.74): `hmm_bounds`, `tendsto_hmmLower`, `hmmUpper_tendsto`.
* Hidden Markov models, (4.75): `hmmTrans`, `markovLaw_hmmTrans`, `hiddenMarkovProcess`,
  `hiddenMarkov_bounds`, `tendsto_hiddenMarkov_lower`, `hmmLower_hmmTrans_eq`.

## Not formalized

* Figures 4.1 and 4.2.
* The facts quoted without proof in Section 4.1: an irreducible aperiodic chain has a unique
  stationary distribution, to which the law of `Xₙ` converges. The remark after Example 4.2.1 is
  formalized with this convergence as a hypothesis.
* The AEP (4.24) for stationary ergodic processes, which the book proves in Section 16.8.
* The question about the freedom of queens and bishops at the end of Example 4.3.1.
* The claim of Section 4.4 that `D(μₙ ‖ μ) → 0` when the stationary distribution is unique,
  which the book mentions without proof, and the heuristic example of the wealth distributions in
  Canada and England.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Chapter 4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.CoverThomas

/-! ## 4.1 Markov chains -/

/-- **(4.6)** The two-state transition matrix `P = [[1 - α, α], [β, 1 - β]]`. -/
def twoStateMatrix (a b : ℝ) : Fin 2 → Fin 2 → ℝ := ![![1 - a, a], ![b, 1 - b]]

/-- **(4.8)** The stationary distribution `(β/(α+β), α/(α+β))` of the two-state chain. -/
def twoStateStationary (a b : ℝ) : Fin 2 → ℝ := ![b / (a + b), a / (a + b)]

lemma twoStateMatrix_isStochastic {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : IsStochastic (twoStateMatrix a b) := by
  intro i
  fin_cases i
  · exact ⟨fun j => by fin_cases j <;> simp [twoStateMatrix] <;> linarith,
      by simp [twoStateMatrix, Fin.sum_univ_two]⟩
  · exact ⟨fun j => by fin_cases j <;> simp [twoStateMatrix] <;> linarith,
      by simp [twoStateMatrix, Fin.sum_univ_two]⟩

lemma twoStateStationary_isPMF {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    IsPMF (twoStateStationary a b) :=
  ⟨fun i => by
    fin_cases i
    · exact div_nonneg hb hab.le
    · exact div_nonneg ha hab.le, by
    simp only [twoStateStationary, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring⟩

/-- **Example 4.1.1, (4.7)** Balancing the probability flow across the cut between the two
states: `μ₁ α = μ₂ β`. -/
lemma example_4_1_1_balance (a b : ℝ) :
    twoStateStationary a b 0 * a = twoStateStationary a b 1 * b := by
  simp [twoStateStationary]
  ring

/-- **Example 4.1.1, (4.8)** `(β/(α+β), α/(α+β))` is a stationary distribution of the two-state
chain. -/
theorem example_4_1_1 {a b : ℝ} (hab : 0 < a + b) :
    IsStationaryDist (twoStateMatrix a b) (twoStateStationary a b) := by
  funext j
  simp only [step, outDist, Fin.sum_univ_two]
  fin_cases j <;> simp [twoStateMatrix, twoStateStationary] <;> field_simp <;> ring

lemma entropy_fin_two (p q : ℝ) (hpq : p + q = 1) : entropy ![p, q] = binEntropy q := by
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_two, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - q = p by linarith]
  simp [add_comm]

/-- **Example 4.1.1, (4.9)** For the chain started from the stationary distribution, the state
`Xₙ` has entropy `H(α/(α+β))`. -/
theorem example_4_1_1_entropy {a b : ℝ} (hab : 0 < a + b) (n : ℕ) :
    entropy (dist (markovLaw (twoStateStationary a b) (twoStateMatrix a b) (n + 1))
      fun x => x (Fin.last n)) = binEntropy (a / (a + b)) := by
  have hsum : b / (a + b) + a / (a + b) = 1 := by
    rw [← add_div, add_comm, div_self hab.ne']
  rw [dist_markovLaw_last, (example_4_1_1 hab).iterate, twoStateStationary,
    entropy_fin_two _ _ hsum]

/-! ## 4.2 Entropy rate -/

/-- **Example 4.2.1, (4.28)** The entropy rate of the two-state chain is
`β/(α+β) H(α) + α/(α+β) H(β)`. -/
theorem example_4_2_1 {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : 0 < a + b) :
    (markovProcess _ _ (twoStateStationary_isPMF ha0 hb0 hab)
      (twoStateMatrix_isStochastic ha0 ha1 hb0 hb1)).HasEntropyRate
        (b / (a + b) * binEntropy a + a / (a + b) * binEntropy b) := by
  have h := markovProcess_hasEntropyRate (twoStateStationary_isPMF ha0 hb0 hab)
    (twoStateMatrix_isStochastic ha0 ha1 hb0 hb1) (example_4_1_1 hab)
  have e0 : entropy (twoStateMatrix a b 0) = binEntropy a :=
    entropy_fin_two (1 - a) a (by ring)
  have e1 : entropy (twoStateMatrix a b 1) = binEntropy b := by
    have : twoStateMatrix a b 1 = ![b, 1 - b] := rfl
    rw [this, entropy_fin_two b (1 - b) (by ring), binEntropy_one_sub]
  rwa [Fin.sum_univ_two, e0, e1] at h

/-! ### A process without an entropy rate -/

/-- **(4.13)** `pᵢ = 1/2` if `2k < log log i ≤ 2k + 1` and `pᵢ = 0` if
`2k + 1 < log log i ≤ 2k + 2`, with logarithms to base 2. Equivalently, `pᵢ = 1/2` iff
`⌈log log i⌉ = clog₂ (clog₂ i)` is odd. Indexed from `0`: `oscillatingProb i = p_{i+1}`. -/
def oscillatingProb (i : ℕ) : ℝ := if Odd (Nat.clog 2 (Nat.clog 2 (i + 1))) then 1 / 2 else 0

lemma oscillatingProb_isPMF (i : ℕ) : IsPMF (bernoulliPMF (oscillatingProb i)) :=
  bernoulliPMF_isPMF (by unfold oscillatingProb; split_ifs <;> norm_num)
    (by unfold oscillatingProb; split_ifs <;> norm_num)

/-- The process of independent Bernoulli(`pᵢ`) random variables of (4.13). -/
def oscillatingProcess : StochasticProcess Bool :=
  indepProcess (fun i => bernoulliPMF (oscillatingProb i)) oscillatingProb_isPMF

/-- The number of `i < N` with `pᵢ₊₁ = 1/2`. -/
def oscillatingCount (N : ℕ) : ℕ :=
  ((range N).filter fun i => Odd (Nat.clog 2 (Nat.clog 2 (i + 1)))).card

lemma jointEntropy_oscillatingProcess (N : ℕ) :
    oscillatingProcess.jointEntropy N = oscillatingCount N * log 2 := by
  rw [oscillatingProcess, jointEntropy_indepProcess, oscillatingCount, card_eq_sum_ones,
    Nat.cast_sum, sum_mul, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  rw [entropy_bernoulliPMF, oscillatingProb]
  split_ifs
  · rw [one_div, binEntropy_two_inv]; simp
  · simp

/-- On the block `2^{2^m} < j ≤ 2^{2^{m+1}}`, `⌈log log j⌉ = m + 1`. -/
lemma clog_clog_eq {m j : ℕ} (h1 : 2 ^ 2 ^ m < j) (h2 : j ≤ 2 ^ 2 ^ (m + 1)) :
    Nat.clog 2 (Nat.clog 2 j) = m + 1 := by
  have a1 : Nat.clog 2 j ≤ 2 ^ (m + 1) := Nat.clog_le_of_le_pow h2
  have a2 : 2 ^ m < Nat.clog 2 j := (Nat.lt_clog_iff_pow_lt one_lt_two).2 h1
  exact le_antisymm (Nat.clog_le_of_le_pow a1) (Nat.succ_le_of_lt
    ((Nat.lt_clog_iff_pow_lt one_lt_two).2 a2))

lemma oscillatingCount_ge (t : ℕ) :
    2 ^ 2 ^ (2 * t + 1) - 2 ^ 2 ^ (2 * t) ≤ oscillatingCount (2 ^ 2 ^ (2 * t + 1)) := by
  rw [oscillatingCount, ← Nat.card_Ico]
  refine card_le_card fun i hi => ?_
  rw [mem_Ico] at hi
  rw [mem_filter, mem_range]
  refine ⟨hi.2, ?_⟩
  rw [clog_clog_eq (m := 2 * t) (by omega) (by omega)]
  exact ⟨t, rfl⟩

lemma oscillatingCount_le (t : ℕ) :
    oscillatingCount (2 ^ 2 ^ (2 * t + 2)) ≤ 2 ^ 2 ^ (2 * t + 1) := by
  rw [oscillatingCount, ← card_range (2 ^ 2 ^ (2 * t + 1))]
  refine card_le_card fun i hi => ?_
  rw [mem_filter, mem_range] at hi
  rw [mem_range]
  by_contra! h
  rw [clog_clog_eq (m := 2 * t + 1) (by omega)
    (by rw [show 2 * t + 1 + 1 = 2 * t + 2 by ring]; omega)] at hi
  exact (Nat.not_odd_iff_even.2 ⟨t + 1, by ring⟩) hi.2

/-- **Example 3 of Section 4.2.** For the independent process (4.13), the running average of the
entropies `H(Xᵢ)` oscillates, and the entropy rate does not exist. -/
theorem example_4_2_no_entropy_rate : ¬ ∃ h, oscillatingProcess.HasEntropyRate h := by
  rintro ⟨h, hh⟩
  have hl2 := log_pos one_lt_two
  have hM : ∀ k : ℕ, k ≤ 2 ^ 2 ^ k := fun k =>
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right two_pos (Nat.lt_two_pow_self).le)
  have hT1 : Tendsto (fun t : ℕ => 2 ^ 2 ^ (2 * t + 1)) atTop atTop :=
    tendsto_atTop_mono (fun t => (by omega : t ≤ 2 * t + 1).trans (hM _)) tendsto_id
  have hT2 : Tendsto (fun t : ℕ => 2 ^ 2 ^ (2 * t + 2)) atTop atTop :=
    tendsto_atTop_mono (fun t => (by omega : t ≤ 2 * t + 2).trans (hM _)) tendsto_id
  -- At the end of a block of fair coins, the average is at least `(1/2) log 2`.
  have hlo : log 2 / 2 ≤ h := by
    refine ge_of_tendsto (hh.comp hT1) (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, jointEntropy_oscillatingProcess]
    set N := 2 ^ 2 ^ (2 * t + 1)
    have hN : (0 : ℝ) < N := by positivity
    have hd : 2 * 2 ^ 2 ^ (2 * t) ≤ N := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right two_pos
        (by rw [pow_succ]; have := Nat.one_le_two_pow (n := 2 * t); omega)
    have hc : ((N - 2 ^ 2 ^ (2 * t) : ℕ) : ℝ) ≤ oscillatingCount N := by
      exact_mod_cast oscillatingCount_ge t
    rw [Nat.cast_sub (by omega)] at hc
    have hd' : (2 : ℝ) * ((2 ^ 2 ^ (2 * t) : ℕ) : ℝ) ≤ N := by exact_mod_cast hd
    rw [le_div_iff₀ hN]
    nlinarith
  -- At the end of a block of constants, the average is at most `(1/4) log 2`.
  have hhi : h ≤ log 2 / 4 := by
    refine le_of_tendsto (hh.comp hT2) (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, jointEntropy_oscillatingProcess]
    set N := 2 ^ 2 ^ (2 * t + 2)
    have hN : (0 : ℝ) < N := by positivity
    have hd : 4 * 2 ^ 2 ^ (2 * t + 1) ≤ N := by
      rw [show 4 = 2 ^ 2 from rfl, ← pow_add]
      exact Nat.pow_le_pow_right two_pos (by
        rw [show 2 * t + 2 = (2 * t + 1) + 1 by ring, pow_succ]
        have := Nat.one_le_two_pow (n := 2 * t + 1)
        have : 2 ≤ 2 ^ (2 * t + 1) := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (2 * t + 1) := Nat.pow_le_pow_right two_pos (by omega)
        omega)
    have hc : (oscillatingCount N : ℝ) * 4 ≤ N := by
      exact_mod_cast (Nat.mul_le_mul_right 4 (oscillatingCount_le t)).trans (by omega)
    rw [div_le_iff₀ hN]
    nlinarith
  linarith

/-! ## 4.3 Example 4.3.1: random walk on a chessboard -/

/-- The king's moves on an `8 × 8` chessboard: adjacent squares, including diagonals. -/
def kingAdj (s t : Fin 8 × Fin 8) : Bool :=
  s ≠ t && s.1.val ≤ t.1.val + 1 && t.1.val ≤ s.1.val + 1 && s.2.val ≤ t.2.val + 1 &&
    t.2.val ≤ s.2.val + 1

/-- The number of moves of a king from a square. -/
def kingDegree (s : Fin 8 × Fin 8) : ℕ := (univ.filter fun t => kingAdj s t = true).card

/-- The unweighted king graph. -/
def kingWeights (s t : Fin 8 × Fin 8) : ℝ := if kingAdj s t = true then 1 else 0

set_option maxRecDepth 100000 in
/-- **Example 4.3.1.** The king has 8 moves in the interior (36 squares), 5 at the edges
(24 squares) and 3 at the corners (4 squares), so `2E = 420`. -/
theorem example_4_3_1_degrees :
    univ.image kingDegree = {3, 5, 8} ∧ (univ.filter fun s => kingDegree s = 8).card = 36 ∧
      (univ.filter fun s => kingDegree s = 5).card = 24 ∧
      (univ.filter fun s => kingDegree s = 3).card = 4 ∧ ∑ s, kingDegree s = 420 := by
  decide

set_option maxRecDepth 100000 in
lemma kingAdj_comm : ∀ s t, kingAdj s t = kingAdj t s := by decide

lemma king_isWeightedGraph : IsWeightedGraph kingWeights :=
  ⟨fun s t => by unfold kingWeights; split_ifs <;> norm_num, fun s t => by
    simp only [kingWeights, kingAdj_comm s t]⟩

lemma king_nodeWeight (s : Fin 8 × Fin 8) : nodeWeight kingWeights s = kingDegree s := by
  simp [nodeWeight, kingWeights, kingDegree, sum_boole]

lemma kingDegree_pos (s : Fin 8 × Fin 8) : 0 < kingDegree s := by
  have h := example_4_3_1_degrees.1
  have : kingDegree s ∈ univ.image kingDegree := mem_image_of_mem _ (mem_univ s)
  rw [h] at this
  simp only [mem_insert, mem_singleton] at this
  omega

lemma king_totalWeight : totalWeight kingWeights = 420 := by
  simp only [totalWeight, king_nodeWeight]
  exact_mod_cast example_4_3_1_degrees.2.2.2.2

/-- **Example 4.3.1.** The stationary probability of a square is `8/420`, `5/420` or `3/420`, in
proportion to the number of moves of the king. -/
theorem example_4_3_1_stationary (s : Fin 8 × Fin 8) :
    walkStationary kingWeights s = kingDegree s / 420 := by
  rw [walkStationary, king_nodeWeight, king_totalWeight]

/-- From a square with `d` moves, the king's next position is uniform over `d` squares, which has
entropy `log d`. -/
lemma entropy_king_walkMatrix (s : Fin 8 × Fin 8) :
    entropy (walkMatrix kingWeights s) = log (kingDegree s) := by
  have hd : (0 : ℝ) < kingDegree s := by exact_mod_cast kingDegree_pos s
  rw [entropy_eq_sum_negMulLog]
  simp only [walkMatrix, king_nodeWeight, kingWeights]
  have h : ∀ t, negMulLog ((if kingAdj s t = true then (1 : ℝ) else 0) / kingDegree s) =
      if kingAdj s t = true then (kingDegree s : ℝ)⁻¹ * log (kingDegree s) else 0 := by
    intro t
    split_ifs
    · rw [negMulLog, one_div, log_inv]; ring
    · simp
  simp only [h]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  change ((kingDegree s : ℕ) : ℝ) * _ = _
  field_simp

set_option maxRecDepth 100000 in
/-- **Example 4.3.1.** The entropy rate of the king's random walk is
`(36·8 log 8 + 24·5 log 5 + 4·3 log 3) / 420`. -/
theorem example_4_3_1_rate :
    ∑ s, walkStationary kingWeights s * entropy (walkMatrix kingWeights s) =
      (288 * log 8 + 120 * log 5 + 12 * log 3) / 420 := by
  simp only [example_4_3_1_stationary, entropy_king_walkMatrix]
  rw [sum_comp (fun d : ℕ => (d : ℝ) / 420 * log d) kingDegree, example_4_3_1_degrees.1]
  have h8 := example_4_3_1_degrees.2.1
  have h5 := example_4_3_1_degrees.2.2.1
  have h3 := example_4_3_1_degrees.2.2.2.1
  simp only [sum_insert (show (3 : ℕ) ∉ ({5, 8} : Finset ℕ) by decide),
    sum_insert (show (5 : ℕ) ∉ ({8} : Finset ℕ) by decide), sum_singleton]
  simp only [h8, h5, h3, nsmul_eq_mul]
  push_cast
  ring

/-- `2.32 < log₂ 5 < 2.33`. -/
lemma log_five_div_log_two_bounds : 2.32 < log 5 / log 2 ∧ log 5 / log 2 < 2.33 := by
  have h2 := log_pos one_lt_two
  constructor
  · rw [lt_div_iff₀ h2]
    have h : (2 : ℝ) ^ 232 < 5 ^ 100 := by norm_num
    have := log_lt_log (by positivity) h
    rw [log_pow, log_pow] at this
    push_cast at this
    linarith
  · rw [div_lt_iff₀ h2]
    have h : (5 : ℝ) ^ 100 < 2 ^ 233 := by norm_num
    have := log_lt_log (by positivity) h
    rw [log_pow, log_pow] at this
    push_cast at this
    linarith

/-- **Example 4.3.1.** The entropy rate of the king's random walk is `0.92 log 8`: it lies
between `0.92 log 8` and `0.93 log 8`. The factor `0.92` is due to edge effects. -/
theorem example_4_3_1_approx :
    0.92 * log 8 < ∑ s, walkStationary kingWeights s * entropy (walkMatrix kingWeights s) ∧
      ∑ s, walkStationary kingWeights s * entropy (walkMatrix kingWeights s) < 0.93 * log 8 := by
  rw [example_4_3_1_rate]
  have h2 := log_pos one_lt_two
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
  obtain ⟨a1, a2⟩ := log_three_div_log_two_bounds
  obtain ⟨b1, b2⟩ := log_five_div_log_two_bounds
  rw [lt_div_iff₀ h2] at a1 b1
  rw [div_lt_iff₀ h2] at a2 b2
  rw [h8]
  constructor <;> nlinarith

/-- The rook's moves: squares in the same row or column. -/
def rookAdj (s t : Fin 8 × Fin 8) : Bool := s ≠ t && (s.1 = t.1 || s.2 = t.2)

/-- The unweighted rook graph. -/
def rookWeights (s t : Fin 8 × Fin 8) : ℝ := if rookAdj s t = true then 1 else 0

set_option maxRecDepth 100000 in
lemma rook_degree (s : Fin 8 × Fin 8) : (univ.filter fun t => rookAdj s t = true).card = 14 := by
  revert s; decide

/-- **Example 4.3.1.** The rook always has 14 moves, so its random walk has entropy rate
`log 14`. -/
theorem example_4_3_1_rook :
    ∑ s, walkStationary rookWeights s * entropy (walkMatrix rookWeights s) = log 14 := by
  have hw : ∀ s, nodeWeight rookWeights s = 14 := fun s => by
    simp [nodeWeight, rookWeights, sum_boole, rook_degree s]
  have hT : totalWeight rookWeights = 64 * 14 := by simp [totalWeight, hw]
  have hH : ∀ s, entropy (walkMatrix rookWeights s) = log 14 := fun s => by
    rw [entropy_eq_sum_negMulLog]
    simp only [walkMatrix, hw, rookWeights]
    have h : ∀ t, negMulLog ((if rookAdj s t = true then (1 : ℝ) else 0) / 14) =
        if rookAdj s t = true then (14 : ℝ)⁻¹ * log 14 else 0 := by
      intro t
      split_ifs
      · rw [negMulLog, one_div, log_inv]; ring
      · simp
    simp only [h]
    rw [← sum_filter, sum_const, rook_degree, nsmul_eq_mul]
    push_cast
    field_simp
  simp only [walkStationary, hw, hT, hH, sum_const, card_univ]
  simp
  field_simp

/-! ## 4.4 Second law of thermodynamics -/

/-- **Second law, interpretation 3 (counterexample).** In general the entropy need not increase:
for a chain whose stationary distribution `(1/4, 3/4)` is not uniform, started from the uniform
(maximum entropy) distribution, the entropy decreases. -/
theorem entropy_can_decrease :
    ∃ (r : Fin 2 → Fin 2 → ℝ) (μ : Fin 2 → ℝ), IsStochastic r ∧ IsPMF μ ∧
      entropy (step r μ) < entropy μ := by
  refine ⟨fun _ => ![1 / 4, 3 / 4], uniformPMF (Fin 2), fun _ => ⟨?_, ?_⟩,
    uniformPMF_isPMF, ?_⟩
  · intro y; fin_cases y <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · have hstep : step (fun _ => ![1 / 4, 3 / 4]) (uniformPMF (Fin 2)) = ![1 / 4, 3 / 4] := by
      funext y
      simp [step, outDist, ← sum_mul, (uniformPMF_isPMF (α := Fin 2)).sum_eq_one]
    rw [hstep, (entropy_eq_log_card_iff uniformPMF_isPMF).2 rfl]
    have h := (entropy_eq_log_card_iff (p := (![1 / 4, 3 / 4] : Fin 2 → ℝ))
      ⟨fun y => by fin_cases y <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩)
    have hle := entropy_le_log_card (p := (![1 / 4, 3 / 4] : Fin 2 → ℝ))
      ⟨fun y => by fin_cases y <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩
    refine lt_of_le_of_ne hle fun heq => ?_
    have := congrFun (h.1 heq) 0
    norm_num [uniformPMF] at this

/-! ## Index of numbered results

Aliases of the library declarations proving the numbered theorems and lemmas of Chapter 4.
-/

/-- **Theorem 4.2.1.** For a stationary process the entropy rate exists and equals
`lim H(Xₙ | Xₙ₋₁, …, X₁)`. -/
alias theorem_4_2_1 := StochasticProcess.IsStationary.hasEntropyRate

/-- **Theorem 4.2.2.** For a stationary process `H(Xₙ | Xₙ₋₁, …, X₁)` has a limit. -/
alias theorem_4_2_2 := StochasticProcess.IsStationary.hasCondEntropyRate

/-- **Theorem 4.2.3 (Cesàro mean).** -/
alias theorem_4_2_3 := cesaro_mean

/-- **Theorem 4.2.4.** The entropy rate of a stationary Markov chain. -/
alias theorem_4_2_4 := markovProcess_hasEntropyRate

/-- **Lemma 4.5.1.** `H(Yₙ | Yₙ₋₁, …, Y₂, X₁) ≤ H(𝒴)`. -/
alias lemma_4_5_1 := hmmLower_le_entropyRate

/-- **Lemma 4.5.2.** `H(Yₙ | Yₙ₋₁, …, Y₁) - H(Yₙ | Yₙ₋₁, …, Y₁, X₁) → 0`. -/
alias lemma_4_5_2 := tendsto_hmmUpper_sub_hmmLower

/-- **Theorem 4.5.1.** `H(Yₙ | Yₙ₋₁, …, Y₁, X₁) ≤ H(𝒴) ≤ H(Yₙ | Yₙ₋₁, …, Y₁)`. -/
alias theorem_4_5_1 := hmm_bounds

/-- **Theorem 4.5.1 (limits).** Both bounds converge to `H(𝒴)`. -/
alias theorem_4_5_1_tendsto := tendsto_hmmLower

end InfoTheory.CoverThomas
