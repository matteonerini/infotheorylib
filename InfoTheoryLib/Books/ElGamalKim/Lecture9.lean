/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCCutSet
public import InfoTheoryLib.Network.BCDegradedMessages
public import InfoTheoryLib.Network.BCSemiDeterministic

/-!
# El Gamal & Kim, Lecture 9: General Broadcast Channels

This file indexes the formalization of Lecture 9 of [elgamal2010] and contains the lecture's two
worked examples. We prove the capacity region with degraded message sets, the mutual covering lemma,
Marton's inner bound and the capacity regions of the semi-deterministic and deterministic broadcast
channels.

## Conventions

* **Rates.** In bits, as in Lecture 5, and the message sets are `[1 : 2^{nR}] = {1, …, 2^⌈nR⌉}`.
* **Nonnegative rates.** `martonRegionBits` and `coverVanDerMeulenRegionBits` are for nonnegative
  rates, which is what the coding scheme gives. `dmsRegionBits` and `dmsCapacityRegionBits` are too:
  with `R₁ < 0` the bound on `R₀ + R₁` would no longer make receiver 1 able to decode `M₀`.
* **Auxiliary random variables.** They take values in `Fin k` for some `k`, which replaces the
  bounds on their cardinalities. So the capacity regions are stated up to closure.
* **The mutual covering lemma.** It is stated for i.i.d. sequences, which is what Marton coding
  needs, while the notes assume pairwise independence within each family. It is a quantitative
  bound that tends to `0` when `r₁ + r₂ > I(U₁; U₂) + δ` and both families grow, `r₁, r₂ > 2δ`,
  which is the case Marton coding uses; the case `r₁ = 0` of the notes is not covered.
* **Numbering.** The notes number the results in the order Theorem 1, Theorem 5, Theorem 1,
  Theorem 2, Theorem 3, Theorem 4. `theorem_9_1` is the first one, on degraded message sets, and
  the second Theorem 1 is `cover_van_der_meulen_inner_bound`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### DM-BC with degraded message sets
* Codes and capacity region: `DMSCode`, `IsAchievableDMSBits`, `dmsCapacityRegionBits`
  (`Network.BCDegradedMessages`).
* **Theorem 1**: `dmsRegionBits`, `dmsCapacityRegionBits_eq`, with achievability
  `isAchievableDMSBits_of_lt` from `sum_codebook_dmsDecode_le`, and the converse
  `IsAchievableDMSBits.mem_closure_dmsRegionBits`.
* The alternative characterization: `moreCapableAltRegionBits`, with
  `mem_superpositionClosedRegionBits_of_mem_moreCapableAltRegionBits` (`Network.BCMoreCapable`).
  This replaces the rate splitting of pages 9-5 and 9-6, which the notes call unnecessary.

### The 3-receiver multilevel DM-BC
* The example of pages 9-17 and 9-18, for the formulas that the notes obtain for it:
  `multilevelInnerRegion`, `multilevelCapacityRegion`, with `multilevelInnerRegion_subset`,
  `multilevel_inner_mem`, `multilevel_inner_le`, `multilevel_capacity_mem`,
  `multilevel_capacity_le`, `multilevelInnerRegion_ssubset` (here).

### Inner bounds for private messages
* The **Cover–van der Meulen inner bound**: `coverVanDerMeulenRegionBits`,
  `coverVanDerMeulenRegionBits_subset`, `coverVanDerMeulenRegionBits_subset_martonRegionBits`
  (`Network.BCMarton`).
* **Theorem 2 (Marton's inner bound)**: `martonRegionBits`, `martonRegionBits_subset`, from the
  random coding bound `exists_marton_code_le`.
* The remark that the region does not increase with general conditional pmfs `p(x | u₁, u₂)`:
  `martonMix₁`, `martonMix₂`, `martonMixInfo₁`, `martonMixInfo₂`, `isAchievableBCBits_of_marton_mix`
  (`Network.BCSemiDeterministic`).
* The **mutual covering lemma**: `mutual_covering_lemma` (here), which is
  `eventually_sum_mutualCovering_typical_le`, from the second moment bound `sum_mutualCovering_le`
  (`Typicality.MutualCovering`).

### Semi-deterministic and deterministic broadcast channels
* The capacity region of the semi-deterministic DM-BC: `IsSemiDeterministicBC`,
  `bcCapacityRegionBits_eq_of_isSemiDeterministicBC` (`Network.BCSemiDeterministic`), for the region
  `bcOuterRegionBits` (`Network.BCDegradedMessages`), with
  `I(X; Y₁) = H(Y₁)` and `I(X; Y₁ | U) = H(Y₁ | U)`: `bcInfoXY₁_eq_entropy`,
  `bcInfoXY₁U_eq_condEntropy` (`Network.BCSemiDeterministic`).
* The capacity region of the deterministic DM-BC: `IsDeterministicBC`, `bcCutSetRegionBits`,
  `bcCapacityRegionBits_eq_of_isDeterministicBC`, with `isAchievableBCBits_of_det` and
  `IsAchievableBCBits.mem_closure_bcCutSetRegionBits` (`Network.BCCutSet`).
* The Blackwell channel of pages 9-22 and 9-23: `blackwell`, `blackwellChannel`, `blackwellPMF`,
  `entropy_dist_blackwell₁`, `entropy_dist_blackwell₂`, `entropy_dist_blackwell`,
  `blackwellCapacity_eq`, `mem_blackwellCapacity`, `blackwell_sum_le`, `blackwellCorner_mem`,
  `blackwellCorner_sum` (here).

### Outer bounds
* The bound with `U₂ = U` of page 9-40, a weakening of the Nair–El Gamal outer bound for private
  messages: `bcOuterRegionBits`, `IsAchievableBCBits.mem_closure_bcOuterRegionBits`
  (`Network.BCDegradedMessages`). It is tight for the semi-deterministic DM-BC.

## Not formalized

* The capacity region of the 3-receiver multilevel DM-BC (Theorem 5), with indirect decoding and the
  rate splitting that it needs, and the reduction of the multilevel product example to the formulas
  on page 9-18.
* The relationship to the Gelfand–Pinsker theorem on page 9-30, which is a remark, and the remark on
  page 9-20 that Marton's region is not convex in general.
* The AWGN-BC via writing on dirty paper (pages 9-31 and 9-32): the coding theorems of Lecture 7 and
  of this lecture are for finite alphabets. The capacity region of the AWGN-BC itself is in
  Lecture 5.
* Marton's inner bound with a common message (Theorem 3), its equivalent region, the deterministic
  channel with a common message, and the bound with `U₀` for private messages on page 9-36.
* The Nair–El Gamal outer bound (Theorem 4) in general, with the auxiliary pair `(U₁, U₂)` and a
  common message.
* The BSC–BEC example on pages 9-39 to 9-41 and the numerical bounds on the sum capacity of the
  binary skew-symmetric channel on pages 9-42 to 9-44.
* The extensions to more than 2 receivers on pages 9-45 to 9-52: the multivariate covering lemma,
  the extended Marton inner bound and the proposition on 3-receiver degraded message sets.
* The bounds on the cardinalities of the auxiliary random variables, except for the sum rate of
  the Marton inner bound: `exists_marton_card` (`Network.MartonCardinality`, Appendix C).
* The description of the capacity region of the Blackwell channel as a union over `α ∈ [1/2, 2/3]`:
  we have the capacity region as the closure of the region over all `p(x)`, the rate pairs for each
  `α`, the bound on the sum rate and the corner of the figure.

## Issues in the notes

* **Page 9-22.** The region of the Blackwell channel is inconsistent with the pmf given for it. With
  `p_X(0) = p_X(2) = α/2` and `p_X(1) = ᾱ` we have `H(Y₁) = H(α)`, `H(Y₂) = H(α/2)`,
  `H(Y₁, Y₂) = H(α) + α` (`entropy_dist_blackwell₁`, `entropy_dist_blackwell₂`,
  `entropy_dist_blackwell`), and the boundary in the figure corresponds to `α ∈ [1/2, 2/3]`.
  The notes print `H(α) + ᾱ` and `α ∈ [1/3, 1/2]`. This is not a matter of notation only: the corner
  `(log 3 - 2/3, 2/3)` of the figure is in the capacity region (`blackwellCorner_mem`) but not in
  the printed union (`blackwellCorner_not_mem_printed`).
* **Page 9-29.** The bound `R̃₂ < I(U₂; Y₂) + δ(ε)` should have `- δ(ε)`, as is written further
  down.
* **Page 9-48.** The private message is printed as `M₁ ∈ [1 : 2^{nR₀}]`; it should be `2^{nR₁}`.
* **Page 9-60.** "as `n → 0`" should be "as `n → ∞`".
* **Page 9-20.** "(R1.R2)" should be "(R1, R2)", and likewise "(m1.m2)" on page 9-43.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 9
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Aliases -/

section Aliases

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

/-- **Theorem 1 of Lecture 9, page 9-4.** The capacity region of the DM-BC with degraded message
sets. -/
theorem theorem_9_1 [Nonempty α] (hW : IsChannel W) :
    dmsCapacityRegionBits W = closure (dmsRegionBits W) :=
  dmsCapacityRegionBits_eq hW

omit [Fintype α] in
/-- **The second Theorem 1 of Lecture 9, page 9-19.** The Cover–van der Meulen inner bound. -/
theorem cover_van_der_meulen_inner_bound [Finite α] (hW : IsChannel W) :
    coverVanDerMeulenRegionBits W ⊆ {R | IsAchievableBCBits W R.1 R.2} :=
  coverVanDerMeulenRegionBits_subset hW

omit [Fintype α] in
/-- **Theorem 2 of Lecture 9, page 9-20.** Marton's inner bound. -/
theorem theorem_9_2 [Finite α] (hW : IsChannel W) :
    martonRegionBits W ⊆ {R | IsAchievableBCBits W R.1 R.2} :=
  martonRegionBits_subset hW

/-- **The mutual covering lemma of Lecture 9, page 9-27**, for i.i.d. families, in the
quantitative form described in the conventions. -/
alias mutual_covering_lemma := eventually_sum_mutualCovering_typical_le

/-- **Lecture 9, page 9-21.** The capacity region of the semi-deterministic DM-BC. -/
theorem semi_deterministic_bc_capacity [Nonempty α] (hW : IsChannel W)
    (h : IsSemiDeterministicBC W) : bcCapacityRegionBits W = closure (bcOuterRegionBits W) :=
  bcCapacityRegionBits_eq_of_isSemiDeterministicBC hW h

/-- **Lecture 9, page 9-21.** The capacity region of the deterministic DM-BC. -/
theorem deterministic_bc_capacity [Nonempty α] (hW : IsChannel W) (h : IsDeterministicBC W) :
    bcCapacityRegionBits W = closure (bcCutSetRegionBits W) :=
  bcCapacityRegionBits_eq_of_isDeterministicBC hW h

end Aliases

/-! ## The Blackwell channel -/

/-- **Example (Lecture 9), page 9-22.** The output `Y₁` of the Blackwell channel. -/
def blackwell₁ : Fin 3 → Fin 2 := ![0, 1, 0]

/-- **Example (Lecture 9), page 9-22.** The output `Y₂` of the Blackwell channel. -/
def blackwell₂ : Fin 3 → Fin 2 := ![0, 1, 1]

/-- The pair of outputs of the Blackwell channel. -/
def blackwell : Fin 3 → Fin 2 × Fin 2 := fun x => (blackwell₁ x, blackwell₂ x)

/-- **Example (Lecture 9), page 9-22.** The Blackwell channel. -/
def blackwellChannel : Fin 3 → Fin 2 × Fin 2 → ℝ := detChannel blackwell

/-- **Example (Lecture 9), page 9-22.** The pmf `p_X(0) = p_X(2) = α/2`, `p_X(1) = ᾱ`. -/
def blackwellPMF (a : ℝ) : Fin 3 → ℝ := ![a / 2, 1 - a, a / 2]

/-- The pmf `p_X(1) = p_X(2) = α/2`, `p_X(0) = ᾱ` for the second region of page 9-22, with the roles
of the receivers exchanged. -/
def blackwellPMF' (a : ℝ) : Fin 3 → ℝ := ![1 - a, a / 2, a / 2]

lemma blackwellChannel_isChannel : IsChannel blackwellChannel :=
  detChannel_isChannel _

lemma isDeterministicBC_blackwellChannel : IsDeterministicBC blackwellChannel :=
  ⟨blackwell₁, blackwell₂, rfl⟩

lemma blackwellPMF_isPMF {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsPMF (blackwellPMF a) := by
  refine ⟨fun x => ?_, ?_⟩
  · fin_cases x <;> simp [blackwellPMF] <;> linarith
  · simp only [blackwellPMF, Fin.sum_univ_three]
    simp
    ring

lemma blackwellPMF'_isPMF {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsPMF (blackwellPMF' a) := by
  refine ⟨fun x => ?_, ?_⟩
  · fin_cases x <;> simp [blackwellPMF'] <;> linarith
  · simp only [blackwellPMF', Fin.sum_univ_three]
    simp
    ring

private lemma two_negMulLog_half (a : ℝ) : 2 * negMulLog (a / 2) = negMulLog a + a * log 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [negMulLog, negMulLog, log_div ha two_ne_zero]
    ring

/-- The entropy of the input: `H(X) = H(α) + α`. -/
lemma entropy_blackwellPMF (a : ℝ) :
    entropy (blackwellPMF a) = binEntropy a + a * log 2 := by
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_three, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [blackwellPMF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linarith [two_negMulLog_half a]

/-- `H(Y₁) = H(α)`. -/
theorem entropy_dist_blackwell₁ (a : ℝ) :
    entropy (dist (blackwellPMF a) blackwell₁) = binEntropy a := by
  have h0 : dist (blackwellPMF a) blackwell₁ 0 = a := by
    simp [dist, Fin.sum_univ_three, blackwellPMF, blackwell₁]
  have h1 : dist (blackwellPMF a) blackwell₁ 1 = 1 - a := by
    simp [dist, Fin.sum_univ_three, blackwellPMF, blackwell₁]
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_two, h0, h1,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- `H(Y₂) = H(α/2)`. -/
theorem entropy_dist_blackwell₂ (a : ℝ) :
    entropy (dist (blackwellPMF a) blackwell₂) = binEntropy (a / 2) := by
  have h0 : dist (blackwellPMF a) blackwell₂ 0 = a / 2 := by
    simp [dist, Fin.sum_univ_three, blackwellPMF, blackwell₂]
  have h1 : dist (blackwellPMF a) blackwell₂ 1 = 1 - (a / 2) := by
    simp [dist, Fin.sum_univ_three, blackwellPMF, blackwell₂]
    ring
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_two, h0, h1,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- The outputs determine the input, so that `H(Y₁, Y₂) = H(X)`. -/
private lemma entropy_dist_blackwell_of_injective (p : Fin 3 → ℝ) :
    entropy (dist p blackwell) = entropy p := by
  have hv : ∀ x, dist p blackwell (blackwell x) = p x := fun x => by
    fin_cases x <;> simp [dist, Fin.sum_univ_three, blackwell, blackwell₁, blackwell₂]
  have h10 : dist p blackwell (1, 0) = 0 := by
    simp [dist, Fin.sum_univ_three, blackwell, blackwell₁, blackwell₂]
  have e0 : ((0 : Fin 2), (0 : Fin 2)) = blackwell 0 := by
    simp [blackwell, blackwell₁, blackwell₂]
  have e1 : ((1 : Fin 2), (1 : Fin 2)) = blackwell 1 := by
    simp [blackwell, blackwell₁, blackwell₂]
  have e2 : ((0 : Fin 2), (1 : Fin 2)) = blackwell 2 := by
    simp [blackwell, blackwell₁, blackwell₂]
  rw [entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_three, h10, e0, e1, e2, hv, hv, hv]
  simp
  ring

/-- `H(Y₁, Y₂) = H(α) + α`. The notes print `H(α) + ᾱ`. -/
theorem entropy_dist_blackwell (a : ℝ) :
    entropy (dist (blackwellPMF a) blackwell) = binEntropy a + a * log 2 := by
  rw [entropy_dist_blackwell_of_injective, entropy_blackwellPMF]

/-- `H(Y₂) = H(α)` for the second pmf. -/
theorem entropy_dist_blackwell₂' (a : ℝ) :
    entropy (dist (blackwellPMF' a) blackwell₂) = binEntropy a := by
  have h0 : dist (blackwellPMF' a) blackwell₂ 0 = 1 - a := by
    simp [dist, Fin.sum_univ_three, blackwellPMF', blackwell₂]
  have h1 : dist (blackwellPMF' a) blackwell₂ 1 = a := by
    simp [dist, Fin.sum_univ_three, blackwellPMF', blackwell₂]
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_two, h0, h1,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- `H(Y₁) = H(α/2)` for the second pmf. -/
theorem entropy_dist_blackwell₁' (a : ℝ) :
    entropy (dist (blackwellPMF' a) blackwell₁) = binEntropy (a / 2) := by
  have h0 : dist (blackwellPMF' a) blackwell₁ 0 = 1 - a / 2 := by
    simp [dist, Fin.sum_univ_three, blackwellPMF', blackwell₁]
    ring
  have h1 : dist (blackwellPMF' a) blackwell₁ 1 = a / 2 := by
    simp [dist, Fin.sum_univ_three, blackwellPMF', blackwell₁]
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_two, h0, h1,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring_nf

/-- `H(Y₁, Y₂) = H(α) + α` for the second pmf. -/
theorem entropy_dist_blackwell' (a : ℝ) :
    entropy (dist (blackwellPMF' a) blackwell) = binEntropy a + a * log 2 := by
  rw [entropy_dist_blackwell_of_injective, entropy_eq_sum_negMulLog, Fin.sum_univ_three,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [blackwellPMF', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linarith [two_negMulLog_half a]

/-- **Example (Lecture 9), page 9-22.** The capacity region of the Blackwell channel is the closure
of the cut-set region. -/
theorem blackwellCapacity_eq :
    bcCapacityRegionBits blackwellChannel = closure (bcCutSetRegionBits blackwellChannel) :=
  bcCapacityRegionBits_eq_of_isDeterministicBC blackwellChannel_isChannel
    isDeterministicBC_blackwellChannel

private lemma mem_blackwellCapacity_of_pmf {p : Fin 3 → ℝ} (hp : IsPMF p) {R₁ R₂ : ℝ}
    (h₁ : R₁ ≤ entropy (dist p blackwell₁) / log 2) (h₂ : R₂ ≤ entropy (dist p blackwell₂) / log 2)
    (h₃ : R₁ + R₂ ≤ entropy (dist p blackwell) / log 2) :
    (R₁, R₂) ∈ bcCapacityRegionBits blackwellChannel := by
  rw [blackwellCapacity_eq]
  refine subset_closure ⟨p, hp, ?_, ?_, ?_⟩
  · have e : bcMarg₁ blackwellChannel = detChannel blackwell₁ := bcMarg₁_det _ _
    rwa [e, mutualInfoOf_detChannel hp]
  · have e : bcMarg₂ blackwellChannel = detChannel blackwell₂ := bcMarg₂_det _ _
    rwa [e, mutualInfoOf_detChannel hp]
  · simpa only [blackwellChannel, mutualInfoOf_detChannel hp] using h₃

/-- **Example (Lecture 9), page 9-22.** Every `α ∈ [0, 1]` gives rate pairs in the capacity region,
in the two ways of the notes, with the values of the entropies computed above. -/
theorem mem_blackwellCapacity {a R₁ R₂ : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1)
    (h : (R₁ ≤ binEntropy a / log 2 ∧ R₂ ≤ binEntropy (a / 2) / log 2) ∨
      (R₁ ≤ binEntropy (a / 2) / log 2 ∧ R₂ ≤ binEntropy a / log 2))
    (hs : R₁ + R₂ ≤ (binEntropy a + a * log 2) / log 2) :
    (R₁, R₂) ∈ bcCapacityRegionBits blackwellChannel := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine mem_blackwellCapacity_of_pmf (blackwellPMF_isPMF h0 h1) ?_ ?_ ?_
    · rwa [entropy_dist_blackwell₁]
    · rwa [entropy_dist_blackwell₂]
    · rwa [entropy_dist_blackwell]
  · refine mem_blackwellCapacity_of_pmf (blackwellPMF'_isPMF h0 h1) ?_ ?_ ?_
    · rwa [entropy_dist_blackwell₁']
    · rwa [entropy_dist_blackwell₂']
    · rwa [entropy_dist_blackwell']

/-- **Example (Lecture 9), page 9-23.** The sum rate is at most `log 3`. -/
theorem blackwell_sum_le {R : ℝ × ℝ} (hR : R ∈ bcCapacityRegionBits blackwellChannel) :
    R.1 + R.2 ≤ log 3 / log 2 := by
  rw [blackwellCapacity_eq] at hR
  have hc : IsClosed {R : ℝ × ℝ | R.1 + R.2 ≤ log 3 / log 2} :=
    isClosed_le (by fun_prop) continuous_const
  refine closure_minimal ?_ hc hR
  rintro R ⟨p, hp, -, -, h⟩
  refine h.trans (div_le_div_of_nonneg_right ?_ (log_pos one_lt_two).le)
  simpa using mutualInfoOf_le_log_card_input hp blackwellChannel_isChannel

private lemma binEntropy_one_third : binEntropy (1 / 3) = log 3 - 2 / 3 * log 2 := by
  have e : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, e, negMulLog, negMulLog,
    log_div one_ne_zero (by norm_num), log_div two_ne_zero (by norm_num), log_one]
  ring

private lemma binEntropy_two_thirds : binEntropy (2 / 3) = log 3 - 2 / 3 * log 2 := by
  have e := binEntropy_one_sub (1 / 3)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at e
  rw [e, binEntropy_one_third]

/-- `(4/3) log 2 ≤ log 3`, as `16 ≤ 27`. -/
private lemma four_log_two_le : 4 * log 2 ≤ 3 * log 3 := by
  have h : log ((2 : ℝ) ^ 4) ≤ log ((3 : ℝ) ^ 3) := log_le_log (by norm_num) (by norm_num)
  simpa [log_pow] using h

/-- **Example (Lecture 9), page 9-23.** The corner `(log 3 - 2/3, 2/3)` of the figure, with `log` to
the base 2, is in the capacity region. It comes from the uniform input, `α = 2/3`. -/
theorem blackwellCorner_mem :
    (log 3 / log 2 - 2 / 3, (2 / 3 : ℝ)) ∈ bcCapacityRegionBits blackwellChannel := by
  have hl := log_pos one_lt_two
  have hc := four_log_two_le
  have ha : (2 : ℝ) / 3 / 2 = 1 / 3 := by norm_num
  refine mem_blackwellCapacity (a := 2 / 3) (by norm_num) (by norm_num) (Or.inl ⟨?_, ?_⟩) ?_
  · rw [binEntropy_two_thirds, le_div_iff₀ hl, sub_mul, div_mul_cancel₀ _ hl.ne']
  · rw [ha, binEntropy_one_third, le_div_iff₀ hl]
    linarith
  · rw [binEntropy_two_thirds, le_div_iff₀ hl, sub_add_cancel, div_mul_cancel₀ _ hl.ne']
    linarith

/-- **Example (Lecture 9), page 9-23.** The corner is on the boundary of the capacity region: its
sum rate is `log 3`, the largest one by `blackwell_sum_le`. -/
theorem blackwellCorner_sum : (log 3 / log 2 - 2 / 3) + (2 / 3 : ℝ) = log 3 / log 2 := by
  ring

/-- The union of the two regions as printed on page 9-22 of the notes, in bits. -/
def blackwellPrintedRegion : Set (ℝ × ℝ) :=
  {R | ∃ a ∈ Set.Icc (1 / 3 : ℝ) (1 / 2),
    ((R.1 ≤ binEntropy a / log 2 ∧ R.2 ≤ binEntropy (a / 2) / log 2) ∨
      (R.1 ≤ binEntropy (a / 2) / log 2 ∧ R.2 ≤ binEntropy a / log 2)) ∧
    R.1 + R.2 ≤ (binEntropy a + (1 - a) * log 2) / log 2}

/-- `H(1/6) < (2/3) log 2`, as `6⁶ < 5⁵ 2⁴`. -/
private lemma binEntropy_one_sixth_lt : binEntropy (1 / 6) < 2 / 3 * log 2 := by
  have e : (1 : ℝ) - 1 / 6 = 5 / 6 := by norm_num
  have h6 : log 6 = log 2 + log 3 := by
    rw [← log_mul two_ne_zero (by norm_num)]
    norm_num
  have hn : log ((6 : ℝ) ^ 6) < log ((5 : ℝ) ^ 5 * 2 ^ 4) := log_lt_log (by norm_num) (by norm_num)
  rw [log_mul (by norm_num) (by norm_num), log_pow, log_pow, log_pow] at hn
  push_cast at hn
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, e, negMulLog, negMulLog,
    log_div one_ne_zero (by norm_num), log_div (by norm_num) (by norm_num), log_one]
  linarith

/-- **Issue in the notes, page 9-22.** The corner of the figure is not in the printed union, so the
printed union is not the capacity region. -/
theorem blackwellCorner_not_mem_printed :
    (log 3 / log 2 - 2 / 3, (2 / 3 : ℝ)) ∉ blackwellPrintedRegion := by
  have hl := log_pos one_lt_two
  rintro ⟨a, ⟨ha₁, ha₂⟩, hc, hs⟩
  simp only at hc hs
  rw [le_div_iff₀ hl, add_mul, sub_mul, div_mul_cancel₀ _ hl.ne'] at hs
  -- The bound on the sum rate is met only for `a = 1 / 3`, by the maximum of the entropy.
  have hp : IsPMF (blackwellPMF (1 - a)) := blackwellPMF_isPMF (by linarith) (by linarith)
  have hle := entropy_le_log_card hp
  rw [entropy_blackwellPMF, binEntropy_one_sub, Fintype.card_fin] at hle
  rcases hc with ⟨-, h₂⟩ | ⟨h₁, -⟩
  · have heq : entropy (blackwellPMF (1 - a)) = log ((Fintype.card (Fin 3) : ℕ) : ℝ) := by
      rw [entropy_blackwellPMF, binEntropy_one_sub, Fintype.card_fin]
      refine le_antisymm hle ?_
      push_cast at hle ⊢
      linarith
    have hu := congrFun ((entropy_eq_log_card_iff hp).1 heq) 1
    simp only [blackwellPMF, Matrix.cons_val_one, Matrix.cons_val_zero, uniformPMF,
      Fintype.card_fin] at hu
    have ha : a = 1 / 3 := by
      push_cast at hu
      linarith
    subst ha
    rw [le_div_iff₀ hl] at h₂
    have e : (1 : ℝ) / 3 / 2 = 1 / 6 := by norm_num
    rw [e] at h₂
    linarith [binEntropy_one_sixth_lt]
  · -- For the second region, `H(a / 2) ≤ H(1 / 4) < H(1 / 3)`.
    rw [le_div_iff₀ hl, sub_mul, div_mul_cancel₀ _ hl.ne'] at h₁
    have h3 : binEntropy (a / 2) < binEntropy (1 / 3) := by
      refine binEntropy_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩
        (by linarith)
    rw [binEntropy_one_third] at h3
    linarith

/-! ## The multilevel product example -/

/-- **Example (Lecture 9), page 9-18.** The extended superposition coding inner bound of the
example: `R₀ ≤ min{p/6 + q/2, p}`, `R₁ ≤ (1 - p)/2 + 1 - q` for some `0 ≤ p, q ≤ 1`. -/
def multilevelInnerRegion : Set (ℝ × ℝ) :=
  {R | ∃ p q : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 ∧ R.1 ≤ min (p / 6 + q / 2) p ∧
    R.2 ≤ (1 - p) / 2 + 1 - q}

/-- **Example (Lecture 9), page 9-18.** The capacity region of the example:
`R₀ ≤ min{r/6 + s/2, t}`, `R₁ ≤ (1 - r)/2 + 1 - s`, `R₀ + R₁ ≤ t + (1 - t)/2 + 1 - s` for some
`0 ≤ r ≤ t ≤ 1`, `0 ≤ s ≤ 1`. -/
def multilevelCapacityRegion : Set (ℝ × ℝ) :=
  {R | ∃ r s t : ℝ, 0 ≤ r ∧ r ≤ t ∧ t ≤ 1 ∧ 0 ≤ s ∧ s ≤ 1 ∧ R.1 ≤ min (r / 6 + s / 2) t ∧
    R.2 ≤ (1 - r) / 2 + 1 - s ∧ R.1 + R.2 ≤ t + (1 - t) / 2 + 1 - s}

/-- **Example (Lecture 9), page 9-18.** Substituting `r = t` gives the inner bound. -/
theorem multilevelInnerRegion_subset : multilevelInnerRegion ⊆ multilevelCapacityRegion := by
  rintro R ⟨p, q, hp0, hp1, hq0, hq1, h₁, h₂⟩
  refine ⟨p, q, p, hp0, le_rfl, hp1, hq0, hq1, h₁, h₂, ?_⟩
  have := h₁.trans (min_le_right _ _)
  linarith

/-- **Example (Lecture 9), page 9-18.** `(1/2, 5/12)` is in the inner bound. -/
theorem multilevel_inner_mem : ((1 / 2 : ℝ), (5 / 12 : ℝ)) ∈ multilevelInnerRegion := by
  refine ⟨1 / 2, 5 / 6, by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  norm_num

/-- **Example (Lecture 9), page 9-18.** For `R₀ = 1/2`, the largest `R₁` in the inner bound is
`5/12`. -/
theorem multilevel_inner_le {R : ℝ × ℝ} (hR : R ∈ multilevelInnerRegion) (h : 1 / 2 ≤ R.1) :
    R.2 ≤ 5 / 12 := by
  obtain ⟨p, q, -, -, -, -, h₁, h₂⟩ := hR
  have h₁₁ := h₁.trans (min_le_left _ _)
  have h₁₂ := h₁.trans (min_le_right _ _)
  linarith

/-- **Example (Lecture 9), page 9-18.** `(1/2, 1/2)` is in the capacity region, with `r = 0`,
`s = 1`, `t = 1`. -/
theorem multilevel_capacity_mem : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ multilevelCapacityRegion := by
  refine ⟨0, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num,
    by norm_num⟩
  norm_num

/-- **Example (Lecture 9), page 9-18.** `(1/2, 1/2)` is on the boundary of the capacity region: for
`R₀ = 1/2`, the largest `R₁` is `1/2`. -/
theorem multilevel_capacity_le {R : ℝ × ℝ} (hR : R ∈ multilevelCapacityRegion) (h : 1 / 2 ≤ R.1) :
    R.2 ≤ 1 / 2 := by
  obtain ⟨r, s, t, hr, -, -, -, -, h₁, h₂, -⟩ := hR
  have h₁₁ := h₁.trans (min_le_left _ _)
  linarith

/-- **Example (Lecture 9), page 9-18.** The capacity region is strictly larger than the extended
superposition coding inner bound. -/
theorem multilevelInnerRegion_ssubset : multilevelInnerRegion ⊂ multilevelCapacityRegion := by
  refine ⟨multilevelInnerRegion_subset, fun h => ?_⟩
  have := multilevel_inner_le (h multilevel_capacity_mem) (by norm_num)
  norm_num at this

end InfoTheory.ElGamalKim
