/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StochasticProcess.Markov

/-!
# Random walks on weighted graphs

A particle walks on an undirected graph with symmetric non-negative edge weights `Wᵢⱼ`. From
node `i` it moves to node `j` with probability proportional to `Wᵢⱼ`, that is
`Pᵢⱼ = Wᵢⱼ / Wᵢ`, where `Wᵢ = ∑ⱼ Wᵢⱼ` is the total weight of the edges at `i`.

## Main definitions

* `IsWeightedGraph W`: `W` is symmetric and non-negative.
* `nodeWeight W i`: the total weight `Wᵢ` of the edges at node `i`, (4.29).
* `totalWeight W`: `∑ᵢ Wᵢ`, which is twice the total edge weight `2W`, (4.30).
* `walkMatrix W`: the transition matrix `Pᵢⱼ = Wᵢⱼ / Wᵢ`.
* `walkStationary W`: the distribution `μᵢ = Wᵢ / 2W`.
* `IsReversible r μ`: the detailed balance condition `μᵢ Pᵢⱼ = μⱼ Pⱼᵢ`.

## Main statements

* `walkStationary_isStationaryDist`: `μᵢ = Wᵢ / 2W` is a stationary distribution, (4.32)–(4.35).
* `walk_entropy_rate`: the entropy rate of the stationary walk is
  `H(…, Wᵢⱼ/2W, …) - H(…, Wᵢ/2W, …)`, (4.36)–(4.41).
* `walk_entropy_rate_unweighted`: with equal weights, the entropy rate is
  `log 2E - H(E₁/2E, …, Eₘ/2E)`, (4.42).
* `markovLaw_comp_rev`: a stationary reversible chain, such as a random walk, has the same law
  forwards and backwards in time, (4.43).
* `exists_walk_of_isReversible`: conversely, every reversible chain is a random walk on a
  weighted graph.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 4.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- An undirected weighted graph: the weights `Wᵢⱼ = Wⱼᵢ ≥ 0`, with `Wᵢⱼ = 0` if `i` and `j` are
not connected. -/
structure IsWeightedGraph (W : α → α → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ W i j
  symm : ∀ i j, W i j = W j i

/-- **(4.29)** The total weight `Wᵢ = ∑ⱼ Wᵢⱼ` of the edges at node `i`. -/
def nodeWeight (W : α → α → ℝ) (i : α) : ℝ := ∑ j, W i j

/-- **(4.30)** `∑ᵢ Wᵢ`, which is `2W` for the total edge weight `W`. -/
def totalWeight (W : α → α → ℝ) : ℝ := ∑ i, nodeWeight W i

/-- The transition matrix `Pᵢⱼ = Wᵢⱼ / Wᵢ` of the random walk. -/
def walkMatrix (W : α → α → ℝ) (i j : α) : ℝ := W i j / nodeWeight W i

/-- **(4.31)** The stationary distribution `μᵢ = Wᵢ / 2W` of the random walk. -/
def walkStationary (W : α → α → ℝ) (i : α) : ℝ := nodeWeight W i / totalWeight W

/-- The distribution `Wᵢⱼ / 2W` on ordered pairs of nodes. -/
def edgePMF (W : α → α → ℝ) (e : α × α) : ℝ := W e.1 e.2 / totalWeight W

variable {W : α → α → ℝ}

lemma totalWeight_pos [Nonempty α] (hpos : ∀ i, 0 < nodeWeight W i) : 0 < totalWeight W :=
  sum_pos (fun i _ => hpos i) univ_nonempty

lemma walkMatrix_isStochastic (hW : IsWeightedGraph W) (hpos : ∀ i, 0 < nodeWeight W i) :
    IsStochastic (walkMatrix W) := fun i =>
  ⟨fun j => div_nonneg (hW.nonneg i j) (hpos i).le, by
    simp only [walkMatrix, ← sum_div]
    exact div_self (hpos i).ne'⟩

lemma walkStationary_isPMF [Nonempty α] (hpos : ∀ i, 0 < nodeWeight W i) :
    IsPMF (walkStationary W) :=
  ⟨fun i => div_nonneg (hpos i).le (totalWeight_pos hpos).le, by
    simp only [walkStationary, ← sum_div]
    exact div_self (totalWeight_pos hpos).ne'⟩

lemma edgePMF_isPMF [Nonempty α] (hW : IsWeightedGraph W) (hpos : ∀ i, 0 < nodeWeight W i) :
    IsPMF (edgePMF W) :=
  ⟨fun e => div_nonneg (hW.nonneg _ _) (totalWeight_pos hpos).le, by
    rw [Fintype.sum_prod_type]
    simp only [edgePMF, ← sum_div]
    exact div_self (totalWeight_pos hpos).ne'⟩

/-- **(4.32)–(4.35)** `μᵢ = Wᵢ / 2W` is a stationary distribution of the random walk: the
stationary probability of a node is proportional to the weight of its edges. -/
theorem walkStationary_isStationaryDist (hW : IsWeightedGraph W)
    (hpos : ∀ i, 0 < nodeWeight W i) : IsStationaryDist (walkMatrix W) (walkStationary W) := by
  funext j
  change ∑ i, walkStationary W i * walkMatrix W i j = walkStationary W j
  have h : ∀ i, walkStationary W i * walkMatrix W i j = W j i / totalWeight W := fun i => by
    simp only [walkStationary, walkMatrix]
    rw [hW.symm i j]; field_simp [(hpos i).ne']
  rw [sum_congr rfl fun i _ => h i, ← sum_div]
  rfl

/-- **(4.36)–(4.41)** The entropy rate of the stationary random walk,
`∑ᵢ μᵢ H(Pᵢ) = H(…, Wᵢⱼ/2W, …) - H(…, Wᵢ/2W, …)`. -/
theorem walk_entropy_rate [Nonempty α] (hW : IsWeightedGraph W) (hpos : ∀ i, 0 < nodeWeight W i) :
    ∑ i, walkStationary W i * entropy (walkMatrix W i) =
      entropy (edgePMF W) - entropy (walkStationary W) := by
  have hT := (totalWeight_pos hpos).ne'
  -- `Wᵢⱼ / 2W = (Wᵢ / 2W) (Wᵢⱼ / Wᵢ)`, and `-x log x` is multiplicative up to cross terms.
  have h : ∀ i j, negMulLog (W i j / totalWeight W) = walkMatrix W i j *
      negMulLog (walkStationary W i) + walkStationary W i * negMulLog (walkMatrix W i j) := by
    intro i j
    rw [← negMulLog_mul]
    congr 1
    simp only [walkStationary, walkMatrix]
    field_simp [(hpos i).ne']
  have hrow : ∀ i, ∑ j, walkMatrix W i j = 1 := fun i =>
    ((walkMatrix_isStochastic hW hpos) i).sum_eq_one
  rw [entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog, Fintype.sum_prod_type]
  simp only [edgePMF, h, sum_add_distrib, ← sum_mul, hrow, one_mul, ← mul_sum,
    entropy_eq_sum_negMulLog]
  ring

/-- The entropy rate of the stationary random walk, as a `HasEntropyRate` statement. -/
theorem walk_hasEntropyRate [Nonempty α] (hW : IsWeightedGraph W)
    (hpos : ∀ i, 0 < nodeWeight W i) :
    (markovProcess (walkStationary W) (walkMatrix W) (walkStationary_isPMF hpos)
      (walkMatrix_isStochastic hW hpos)).HasEntropyRate
        (entropy (edgePMF W) - entropy (walkStationary W)) := by
  rw [← walk_entropy_rate hW hpos]
  exact markovProcess_hasEntropyRate _ _ (walkStationary_isStationaryDist hW hpos)

/-- **(4.42)** If all edges have equal weight (`W` is the `0/1` adjacency matrix, `2E` the sum
of the degrees), the entropy rate of the random walk is `log 2E - H(E₁/2E, …, Eₘ/2E)`. -/
theorem walk_entropy_rate_unweighted [Nonempty α] (hW : IsWeightedGraph W)
    (h01 : ∀ i j, W i j = 0 ∨ W i j = 1) (hpos : ∀ i, 0 < nodeWeight W i) :
    ∑ i, walkStationary W i * entropy (walkMatrix W i) =
      log (totalWeight W) - entropy (walkStationary W) := by
  rw [walk_entropy_rate hW hpos]
  congr 1
  have hT := totalWeight_pos hpos
  rw [entropy_eq_sum_negMulLog]
  have h : ∀ e : α × α, negMulLog (edgePMF W e) = W e.1 e.2 / totalWeight W *
      log (totalWeight W) := by
    intro e
    rcases h01 e.1 e.2 with h | h
    · simp [edgePMF, h]
    · simp [edgePMF, h, negMulLog, log_inv]
  have hsum := (edgePMF_isPMF hW hpos).sum_eq_one
  simp only [edgePMF] at hsum
  simp only [h, ← sum_mul, hsum, one_mul]

/-! ### Time reversibility -/

/-- The detailed balance condition `μᵢ Pᵢⱼ = μⱼ Pⱼᵢ`: the chain started from `μ` is
time-reversible. -/
def IsReversible (r : α → α → ℝ) (μ : α → ℝ) : Prop := ∀ i j, μ i * r i j = μ j * r j i

/-- A random walk on a weighted graph is reversible. -/
theorem walk_isReversible (hW : IsWeightedGraph W) (hpos : ∀ i, 0 < nodeWeight W i) :
    IsReversible (walkMatrix W) (walkStationary W) := by
  intro i j
  simp only [walkStationary, walkMatrix]
  field_simp [(hpos i).ne', (hpos j).ne']
  rw [hW.symm]

omit [Fintype α] in
lemma snoc_comp_rev {n : ℕ} (x : Fin (n + 1) → α) (b : α) :
    (Fin.snoc x b : Fin (n + 2) → α) ∘ Fin.rev = Fin.cons b (x ∘ Fin.rev) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.snoc_last]
  · simp [Fin.rev_succ, Fin.snoc_castSucc]

omit [Fintype α] in
lemma markovLaw_succ_comp_rev {r : α → α → ℝ} {μ : α → ℝ} (hrev : IsReversible r μ) (n : ℕ) :
    ∀ x : Fin (n + 1) → α, markovLaw μ r (n + 1) (x ∘ Fin.rev) = markovLaw μ r (n + 1) x := by
  induction n with
  | zero =>
    intro x
    have : x ∘ Fin.rev = x := by funext i; fin_cases i; rfl
    rw [this]
  | succ n ih =>
    intro x
    obtain ⟨y, b, rfl⟩ : ∃ y b, x = Fin.snoc y b :=
      ⟨Fin.init x, x (Fin.last _), (Fin.snoc_init_self x).symm⟩
    rw [snoc_comp_rev, markovLaw_snoc, markovLaw_succ, pathProb_cons, ← ih, markovLaw_succ]
    simp only [Fin.cons_zero, Function.comp_apply, Fin.rev_zero]
    have h := hrev b (y (Fin.last n))
    calc μ b * (r b (y (Fin.last n)) * pathProb r n (y ∘ Fin.rev))
        = μ b * r b (y (Fin.last n)) * pathProb r n (y ∘ Fin.rev) := by ring
      _ = μ (y (Fin.last n)) * r (y (Fin.last n)) b * pathProb r n (y ∘ Fin.rev) := by rw [h]
      _ = _ := by ring

omit [Fintype α] in
/-- **(4.43)** A reversible chain has the same law forwards and backwards in time:
`Pr{X₁ = x₁, …, Xₙ = xₙ} = Pr{Xₙ = x₁, …, X₁ = xₙ}`. -/
theorem markovLaw_comp_rev {r : α → α → ℝ} {μ : α → ℝ} (hrev : IsReversible r μ) (n : ℕ)
    (x : Fin n → α) : markovLaw μ r n (x ∘ Fin.rev) = markovLaw μ r n x := by
  cases n with
  | zero => rfl
  | succ n => exact markovLaw_succ_comp_rev hrev n x

/-- Conversely, every reversible chain with positive `μ` is a random walk on a weighted graph,
with weights `Wᵢⱼ = μᵢ Pᵢⱼ`. -/
theorem exists_walk_of_isReversible {r : α → α → ℝ} (hr : IsStochastic r) {μ : α → ℝ}
    (hμ : ∀ i, 0 < μ i) (hrev : IsReversible r μ) :
    ∃ W : α → α → ℝ, IsWeightedGraph W ∧ (∀ i, 0 < nodeWeight W i) ∧ walkMatrix W = r := by
  refine ⟨fun i j => μ i * r i j, ⟨fun i j => mul_nonneg (hμ i).le ((hr i).nonneg j), hrev⟩,
    fun i => ?_, ?_⟩
  · simp [nodeWeight, ← mul_sum, (hr i).sum_eq_one, hμ i]
  · funext i j
    simp only [walkMatrix, nodeWeight, ← mul_sum, (hr i).sum_eq_one, mul_one]
    field_simp [(hμ i).ne']

end InfoTheory
