/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MutualInformation.Convexity
public import InfoTheoryLib.Entropy.Bounds

/-!
# Channel capacity

A discrete memoryless channel with input alphabet `α` and output alphabet `β` is given by its
transition matrix `W x y = p(y | x)` (`IsChannel W`). Its (information) capacity is the largest
mutual information `C = max_{p(x)} I(X; Y)` between the input and the output, over the input
distributions `p`.

Logarithms are natural, so capacities are in nats per channel use; the book's capacities in bits
are `C / log 2`.

## Main definitions

* `capacity W`: the information capacity `C = max_{p(x)} I(X; Y)`, (7.1).
* `IsWeaklySymmetric W`, `IsSymmetricChannel W`: weakly symmetric and symmetric channels.

## Main statements

* `capacity_nonneg`, `capacity_le_log_card_input`, `capacity_le_log_card_output`: properties 1–3
  of Section 7.3, `0 ≤ C ≤ min (log |𝒳|) (log |𝒴|)`.
* `continuousOn_mutualInfoOf`, `exists_capacity_eq`: properties 4–5 of Section 7.3, `I(X; Y)` is
  continuous in `p(x)` (it is concave by `mutualInfoOf_concave_input`), so the capacity is a
  maximum, attained by some input distribution.
* `capacity_of_isWeaklySymmetric`: Theorem 7.2.1, a weakly symmetric channel has capacity
  `log |𝒴| - H(row of the transition matrix)`, achieved by the uniform input distribution.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 7.1–7.3
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Definition (7.1).** The information capacity `C = max_{p(x)} I(X; Y)` of the channel `W`. -/
def capacity (W : α → β → ℝ) : ℝ := sSup {c | ∃ p, IsPMF p ∧ mutualInfoOf p W = c}

lemma mutualInfoOf_nonneg {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    0 ≤ mutualInfoOf p W :=
  mutualInfo_nonneg (jointOf_isPMF hp hW) _ _

/-- `I(X; Y) ≤ H(X) ≤ log |𝒳|`. -/
lemma mutualInfoOf_le_log_card_input {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p)
    (hW : IsChannel W) : mutualInfoOf p W ≤ log (Fintype.card α) := by
  have hq := jointOf_isPMF hp hW
  rw [mutualInfoOf, mutualInfo_eq_entropy_sub_condEntropy hq]
  linarith [condEntropy_nonneg hq (Prod.fst : α × β → α) Prod.snd,
    entropyRV_le_log_card hq (Prod.fst : α × β → α)]

/-- `I(X; Y) ≤ H(Y) ≤ log |𝒴|`. -/
lemma mutualInfoOf_le_log_card_output {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p)
    (hW : IsChannel W) : mutualInfoOf p W ≤ log (Fintype.card β) := by
  have hq := jointOf_isPMF hp hW
  rw [mutualInfoOf, mutualInfo_eq_entropy_sub_condEntropy' hq]
  linarith [condEntropy_nonneg hq (Prod.snd : α × β → β) Prod.fst,
    entropyRV_le_log_card hq (Prod.snd : α × β → β)]

lemma bddAbove_mutualInfoOf {W : α → β → ℝ} (hW : IsChannel W) :
    BddAbove {c | ∃ p, IsPMF p ∧ mutualInfoOf p W = c} :=
  ⟨log (Fintype.card β), fun _ ⟨_, hp, hc⟩ => hc ▸ mutualInfoOf_le_log_card_output hp hW⟩

/-- Every input distribution has `I(X; Y) ≤ C`. -/
lemma mutualInfoOf_le_capacity {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    mutualInfoOf p W ≤ capacity W :=
  le_csSup (bddAbove_mutualInfoOf hW) ⟨p, hp, rfl⟩

lemma capacity_set_nonempty [Nonempty α] (W : α → β → ℝ) :
    {c | ∃ p, IsPMF p ∧ mutualInfoOf p W = c}.Nonempty :=
  ⟨_, uniformPMF α, uniformPMF_isPMF, rfl⟩

/-- **Section 7.3, property 1.** `C ≥ 0`. -/
theorem capacity_nonneg [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) : 0 ≤ capacity W :=
  (mutualInfoOf_nonneg uniformPMF_isPMF hW).trans (mutualInfoOf_le_capacity uniformPMF_isPMF hW)

/-- **Section 7.3, property 2.** `C ≤ log |𝒳|`. -/
theorem capacity_le_log_card_input [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) :
    capacity W ≤ log (Fintype.card α) :=
  csSup_le (capacity_set_nonempty W) fun _ ⟨_, hp, hc⟩ => hc ▸ mutualInfoOf_le_log_card_input hp hW

/-- **Section 7.3, property 3.** `C ≤ log |𝒴|`. -/
theorem capacity_le_log_card_output [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) :
    capacity W ≤ log (Fintype.card β) :=
  csSup_le (capacity_set_nonempty W) fun _ ⟨_, hp, hc⟩ =>
    hc ▸ mutualInfoOf_le_log_card_output hp hW

/-! ### The capacity is a maximum -/

/-- The set of input distributions is compact. -/
lemma isCompact_setOf_isPMF : IsCompact {p : α → ℝ | IsPMF p} := by
  have hset : {p : α → ℝ | IsPMF p} =
      (⋂ x, {p : α → ℝ | 0 ≤ p x}) ∩ {p | ∑ x, p x = 1} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h.nonneg, h.sum_eq_one⟩, fun h => ⟨h.1, h.2⟩⟩
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [hset]
    refine (isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)).inter ?_
    exact isClosed_eq (continuous_finsetSum _ fun x _ => continuous_apply x) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : α → ℝ)) (r := 1)).subset fun p hp => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hp.nonneg x)]
    exact hp.le_one x

/-- `I(X; Y)` as an explicitly continuous function of the input distribution `p`. -/
lemma mutualInfoOf_eq_sum {p : α → ℝ} {W : α → β → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    mutualInfoOf p W = ∑ y, negMulLog (∑ x, p x * W x y) - ∑ x, p x * entropy (W x) := by
  rw [mutualInfoOf_eq hp hW, entropy_eq_sum_negMulLog]
  rfl

/-- **Section 7.3, property 4.** `I(X; Y)` is a continuous function of `p(x)`. -/
theorem continuousOn_mutualInfoOf {W : α → β → ℝ} (hW : IsChannel W) :
    ContinuousOn (fun p => mutualInfoOf p W) {p : α → ℝ | IsPMF p} := by
  have hc : Continuous fun p : α → ℝ =>
      ∑ y, negMulLog (∑ x, p x * W x y) - ∑ x, p x * entropy (W x) := by
    refine (continuous_finsetSum _ fun y _ => continuous_negMulLog.comp ?_).sub ?_
    · exact continuous_finsetSum _ fun x _ => (continuous_apply x).mul continuous_const
    · exact continuous_finsetSum _ fun x _ => (continuous_apply x).mul continuous_const
  exact hc.continuousOn.congr fun p hp => mutualInfoOf_eq_sum hp hW

/-- **Section 7.3.** Since `I(X; Y)` is continuous on the compact set of input distributions, the
capacity is a maximum: some input distribution `p*` achieves `I(X; Y) = C`. -/
theorem exists_capacity_eq [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) :
    ∃ p, IsPMF p ∧ mutualInfoOf p W = capacity W := by
  obtain ⟨p, hp, hmax⟩ := isCompact_setOf_isPMF.exists_isMaxOn
    ⟨uniformPMF α, uniformPMF_isPMF⟩ (continuousOn_mutualInfoOf hW)
  refine ⟨p, hp, le_antisymm (mutualInfoOf_le_capacity hp hW) ?_⟩
  exact csSup_le (capacity_set_nonempty W) fun _ ⟨q, hq, hc⟩ => hc ▸ hmax hq

/-! ### Symmetric channels -/

/-- **Definition (Section 7.2).** A channel is weakly symmetric if every row of the transition
matrix is a permutation of every other row and all the column sums `∑ₓ p(y | x)` are equal. -/
def IsWeaklySymmetric (W : α → β → ℝ) : Prop :=
  (∀ x x', ∃ σ : Equiv.Perm β, ∀ y, W x' y = W x (σ y)) ∧ ∀ y y', ∑ x, W x y = ∑ x, W x y'

/-- **Definition (Section 7.2).** A channel is symmetric if the rows of the transition matrix are
permutations of each other, and so are the columns. -/
def IsSymmetricChannel (W : α → β → ℝ) : Prop :=
  (∀ x x', ∃ σ : Equiv.Perm β, ∀ y, W x' y = W x (σ y)) ∧
    ∀ y y', ∃ τ : Equiv.Perm α, ∀ x, W x y' = W (τ x) y

omit [Fintype β] in
/-- A symmetric channel is weakly symmetric. -/
lemma IsSymmetricChannel.isWeaklySymmetric {W : α → β → ℝ} (h : IsSymmetricChannel W) :
    IsWeaklySymmetric W := by
  refine ⟨h.1, fun y y' => ?_⟩
  obtain ⟨τ, hτ⟩ := h.2 y y'
  simp only [hτ]
  exact (Equiv.sum_comp τ fun x => W x y).symm

/-- The entropy of the uniform distribution is `log |α|`. -/
lemma entropy_uniformPMF [Nonempty α] : entropy (uniformPMF α) = log (Fintype.card α) := by
  have h := relEntropyReal_uniform (uniformPMF_isPMF (α := α))
  rw [relEntropyReal_self] at h
  linarith

/-- **Theorem 7.2.1, (7.19)–(7.25).** A weakly symmetric channel has capacity
`C = log |𝒴| - H(r)`, where `r` is any row of the transition matrix, and the uniform input
distribution achieves it. -/
theorem capacity_of_isWeaklySymmetric [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W)
    (hs : IsWeaklySymmetric W) (x₀ : α) :
    capacity W = log (Fintype.card β) - entropy (W x₀) ∧
      mutualInfoOf (uniformPMF α) W = capacity W := by
  have : Nonempty β := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hW x₀))
  -- All the rows have the same entropy.
  have hrow : ∀ x, entropy (W x) = entropy (W x₀) := fun x => by
    obtain ⟨σ, hσ⟩ := hs.1 x₀ x
    rw [show W x = W x₀ ∘ σ from funext hσ, entropy_comp_equiv]
  have hI : ∀ p, IsPMF p → mutualInfoOf p W = entropy (outDist p W) - entropy (W x₀) := by
    intro p hp
    rw [mutualInfoOf_eq hp hW]
    simp only [hrow, ← sum_mul, hp.sum_eq_one, one_mul]
  -- The uniform input gives a uniform output, (7.22).
  have hout : outDist (uniformPMF α) W = uniformPMF β := by
    obtain ⟨y₀⟩ := (inferInstance : Nonempty β)
    have hconst : ∀ y, outDist (uniformPMF α) W y = outDist (uniformPMF α) W y₀ := fun y => by
      simp only [outDist, uniformPMF, ← mul_sum, hs.2 y y₀]
    have hsum := (outDist_isPMF (uniformPMF_isPMF (α := α)) hW).sum_eq_one
    simp only [hconst, sum_const, card_univ, nsmul_eq_mul] at hsum
    have hc : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
    funext y
    rw [hconst, uniformPMF, eq_div_iff hc.ne']
    linarith
  have hmax : mutualInfoOf (uniformPMF α) W = log (Fintype.card β) - entropy (W x₀) := by
    rw [hI _ uniformPMF_isPMF, hout, entropy_uniformPMF]
  have hle : ∀ p, IsPMF p → mutualInfoOf p W ≤ log (Fintype.card β) - entropy (W x₀) :=
    fun p hp => by
      rw [hI p hp]
      linarith [entropy_le_log_card (outDist_isPMF hp hW)]
  have hC : capacity W = log (Fintype.card β) - entropy (W x₀) :=
    IsGreatest.csSup_eq ⟨⟨_, uniformPMF_isPMF, hmax⟩, fun _ ⟨p, hp, hc⟩ => hc ▸ hle p hp⟩
  exact ⟨hC, hmax.trans hC.symm⟩

/-- If all the rates below `C` are in `A` and all the rates in `A` are at most `C`, `sSup A = C`. -/
lemma sSup_eq_of_forall_mem {A : Set ℝ} {C : ℝ} (h₁ : ∀ R ∈ A, R ≤ C) (h₂ : ∀ R < C, R ∈ A) :
    sSup A = C :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨C - 1, h₂ _ (by linarith)⟩ h₁ fun R hR =>
    ⟨(R + C) / 2, h₂ _ (by linarith), by linarith⟩

end InfoTheory
