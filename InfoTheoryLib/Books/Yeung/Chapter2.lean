/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Analysis.LogSum
public import InfoTheoryLib.Entropy.Fano
public import InfoTheoryLib.Entropy.Range
public import InfoTheoryLib.MarkovChain.Sequence
public import InfoTheoryLib.MaxEntropy.Basic
public import InfoTheoryLib.MutualInformation.ChainRule
public import InfoTheoryLib.MutualInformation.Continuity
public import InfoTheoryLib.RelativeEntropy.Pinsker
public import InfoTheoryLib.StochasticProcess.Independent

/-!
# Yeung, Chapter 2: Information Measures

This file indexes the formalization of Chapter 2 of [yeung2008], and contains aliases named after
the numbers of the results, so the index is checked by Lean. It cites the draft of 15 November
2007, which numbers definitions, theorems and examples with one counter per chapter. The
end-of-chapter problems and the historical notes are not included.

## Conventions

* **Alphabets.** The book's alphabets are countable unless stated otherwise; here they are finite.
* **Indexing.** The book's `X₁, …, Xₙ` are `X₀, …, X_{n-1}` here.
* **Families.** Mutually independent families and the chain rules use `X : ℕ → Ω → α`, with one
  alphabet for all the variables, as the rest of the library does. Markov chains use
  `X : ∀ i, Ω → A i`, since Proposition 2.10 needs alphabets that depend on `i`.
* **Logarithms.** All quantities are in nats. The book's base is arbitrary, and the results hold in
  any base after dividing by the logarithm of the base. In Theorem 2.33 and Corollary 2.48, written
  for bits in the book, `1 / (2 ln 2)` and `1` become `1 / 2` and `log 2`.
* **Infinite divergence.** The book's `D(p‖q)` takes values in `[0, ∞]`; it is `relEntropy`.
* **Estimators.** In Section 2.8, `P_e` is `errProb μ X X̂ id`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 2.1 Independence and Markov Chains
* Definitions 2.1 and 2.2: `IndepRV` (`Probability.Independence`), `IndepFamily`
  (`Probability.RandomVector`).
* Definition 2.3: `PairwiseIndep`, and `IndepFamily.pairwiseIndep` for the implication after it
  (`Probability.RandomVector`). The converse fails, which the book leaves as an exercise:
  `pairwiseIndep_xorTriple`, `not_indepFamily_xorTriple` (here).
* Definition 2.4: `CondIndep` (`Probability.Independence`), with (2.3) `condIndep_iff_mul` and
  (2.4) `condIndep_iff_condDist` (`MarkovChain.CondIndep`).
* Proposition 2.5: `condIndep_iff_factorization` (`MarkovChain.CondIndep`).
* Definition 2.6: `IsMarkovChain`, with (2.16) `isMarkovChain_iff_condDist` and the case of three
  variables `isMarkovChain_three_iff` (`MarkovChain.Sequence`). `X ⊥ Z | Y` is `X → Y → Z`:
  `markovChain_iff_condIndep` (`MarkovChain.Basic`).
* Propositions 2.7, 2.8, 2.9 and 2.10: `isMarkovChain_reverse_iff`,
  `isMarkovChain_iff_forall_markovChain`, `isMarkovChain_iff_factorization`, `IsMarkovChain.block`
  (`MarkovChain.Sequence`).
* Example 2.11: `example_2_11` (here).
* Proposition 2.12 and the example after it: `condIndep_intersection`,
  `condIndep_intersection_counterexample` (`MarkovChain.CondIndep`).

### 2.2 Shannon's Information Measures
* Definition 2.13 and (2.37): `entropy`, `entropyRV`, `entropy_eq_expect` (`Entropy.Basic`).
* (2.38)–(2.39): Mathlib's `Real.binEntropy`.
* Definitions 2.14 and 2.15, and (2.42)–(2.43): `jointEntropy_def` (`Entropy.Basic`), `condEntropy`,
  `condEntropy_eq_sum_joint` (`Entropy.Conditional`).
* Proposition 2.16: `proposition_2_16` (here).
* Definition 2.17: `mutualInfo`, `mutualInfo_eq_sum` (`MutualInformation.Basic`).
* Propositions 2.18 and 2.19: `mutualInfo_self`, `proposition_2_19` (here).
* Definition 2.20: `condMutualInfo`, `condMutualInfo_eq_expect` (`MutualInformation.Conditional`).
* Propositions 2.21 and 2.22: `condMutualInfo_self` (`MutualInformation.Conditional`),
  `proposition_2_22` (here).
* Special cases of `I(X; Y | Z)` at the end of the section: `condMutualInfo_self`,
  `condMutualInfo_const` (`MutualInformation.Conditional`).

### 2.3 Continuity of Shannon's Information Measures for Fixed Finite Alphabets
* Definition 2.23: `l1Dist` (`RelativeEntropy.Pinsker`).
* (2.74)–(2.76), continuity of the entropy: `continuous_entropy` (`Probability.SupportMixture`).
* (2.77): `condMutualInfo_eq` (`MutualInformation.Conditional`).
* (2.78)–(2.84), continuity of `I(X; Y | Z)`: `continuousOn_condMutualInfo`
  (`MutualInformation.Continuity`).

### 2.4 Chain Rules
* Propositions 2.24 and 2.25: `chain_rule_entropy`, `chain_rule_entropy_cond` (`Entropy.ChainRule`).
* Propositions 2.26 and 2.27: `chain_rule_mutualInfo`, `chain_rule_condMutualInfo_prefix`
  (`MutualInformation.ChainRule`).

### 2.5 Informational Divergence
* Definition 2.28: `relEntropy`, `relEntropyReal` (`RelativeEntropy.Basic`).
* Lemma 2.29 and Corollary 2.30: `lemma_2_29`, `corollary_2_30` (here).
* Theorem 2.31: `theorem_2_31` (here).
* Theorem 2.32: `theorem_2_32` (here). Terms with `aᵢ > 0 = bᵢ`, for which the left side of (2.111)
  is infinite, are excluded by a hypothesis.
* Theorem 2.33: `pinsker` (`RelativeEntropy.Pinsker`), under `AbsCont p q`, as otherwise
  `D(p‖q) = ∞`.

### 2.6 The Basic Inequalities
* Theorem 2.34: `theorem_2_34` (here).
* Propositions 2.35, 2.36 and 2.37: `entropy_eq_zero_iff` (`Entropy.Basic`),
  `condEntropy_eq_zero_iff` (`Entropy.Fano`), `mutualInfo_eq_zero_iff`
  (`MutualInformation.Basic`). In 2.36, "function" means on the outcomes of positive probability.

### 2.7 Some Useful Information Inequalities
* Theorems 2.38 and 2.39: `theorem_2_38`, `theorem_2_39` (here).
* Theorem 2.40: `theorem_2_40` (here).
* Lemma 2.41: `lemma_2_41` (here).
* Theorem 2.42: `IsMarkovChain.data_processing` (`MarkovChain.Sequence`).

### 2.8 Fano's Inequality
* Theorem 2.43: `theorem_2_43` (here).
* Corollary 2.44: `exists_entropy_eq` (`Entropy.Range`).
* Theorem 2.47: `theorem_2_47` (here), a special case of `fano` (`Entropy.Fano`).
* Corollary 2.48: `corollary_2_48` (here), a special case of `fano_lt` (`Entropy.Fano`).

### 2.9 Maximum Entropy Distributions
* Theorem 2.50 and Corollary 2.51: `theorem_2_50`, `corollary_2_51` (here), and the equality case
  `entropy_eq_of_eq_exp_iff` (`MaxEntropy.Basic`). The set `S` is the alphabet.
* Example 2.52: `entropy_le_log_card`, `entropy_eq_log_card_iff` (`Entropy.Bounds`).

### 2.10 Entropy Rate of Stationary Source
* Definitions 2.54 and 2.57: `StochasticProcess.HasEntropyRate`,
  `StochasticProcess.IsStationary` (`StochasticProcess.Basic`).
* Example 2.55: `iidProcess_hasEntropyRate` (`StochasticProcess.Independent`).
* (2.220): `StochasticProcess.HasCondEntropyRate` (`StochasticProcess.Basic`).
* Lemma 2.58, with (2.223)–(2.224): `StochasticProcess.IsStationary.hasCondEntropyRate`,
  `StochasticProcess.IsStationary.condEntropyLast_antitone` (`StochasticProcess.Basic`).
* Lemma 2.59: `cesaro_mean` (`StochasticProcess.Basic`).
* Theorem 2.60: `StochasticProcess.IsStationary.hasEntropyRate` (`StochasticProcess.Basic`).

## Not formalized

* Examples 2.45, 2.46, 2.49 and 2.53, and Appendix 2.A: countably infinite alphabets, which this
  library does not have.
* Example 2.56: a source with a growing alphabet, whose entropy rate does not exist.
* The continuity argument of (2.31)–(2.34) that fails after Proposition 2.12. It is a discussion;
  what it shows is `condIndep_intersection_counterexample`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.Yeung

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-! ### Worked examples -/

/-- The sets of **Example 2.11**, with indices shifted by one: `{1, 2}`, `{4}`, `{6, 8}`, `{10}` in
the book. -/
def example_2_11_blocks : ℕ → Finset ℕ
  | 0 => {0, 1}
  | 1 => {3}
  | 2 => {5, 7}
  | _ => {9}

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] in
/-- **Example 2.11.** If `X₁ → X₂ → ⋯ → X₁₀` is a Markov chain, then so is
`(X₁, X₂) → X₄ → (X₆, X₈) → X₁₀` (2.21). -/
theorem example_2_11 {A : ℕ → Type*} [∀ i, Finite (A i)] {μ : Ω → ℝ} (hμ : IsPMF μ)
    {X : ∀ i, Ω → A i} (h : IsMarkovChain μ X 10) :
    IsMarkovChain μ (fun j => blockRV X (example_2_11_blocks j)) 4 := by
  refine h.block hμ (by norm_num) (by norm_num) _ (fun j hj i hi => ?_) (fun j hj₀ hj => ?_)
    (fun j j' hjj' hj' i hi i' hi' => ?_)
  · interval_cases j <;> simp [example_2_11_blocks] at hi <;> omega
  · have hj' : j < 3 := by omega
    interval_cases j <;> simp [example_2_11_blocks]
  · interval_cases j' <;> interval_cases j <;> simp [example_2_11_blocks] at hi hi' <;> omega

/-! ### Aliases -/

/-- **Proposition 2.5.** -/
alias proposition_2_5 := condIndep_iff_factorization

/-- **Proposition 2.7.** -/
alias proposition_2_7 := isMarkovChain_reverse_iff

/-- **Proposition 2.8.** -/
alias proposition_2_8 := isMarkovChain_iff_forall_markovChain

/-- **Proposition 2.9.** -/
alias proposition_2_9 := isMarkovChain_iff_factorization

/-- **Proposition 2.10 (Markov subchains).** -/
alias proposition_2_10 := IsMarkovChain.block

/-- **Proposition 2.12.** -/
alias proposition_2_12 := condIndep_intersection

/-- **Proposition 2.16.** (2.47)–(2.48) -/
theorem proposition_2_16 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[pair X Y ; μ] = H[X ; μ] + H[Y | X ; μ] ∧ H[pair X Y ; μ] = H[Y ; μ] + H[X | Y ; μ] :=
  ⟨chain_rule hμ X Y, by rw [entropyRV_pair_comm μ X Y]; exact chain_rule hμ Y X⟩

/-- **Proposition 2.18.** -/
alias proposition_2_18 := mutualInfo_self

/-- **Proposition 2.19.** (2.57)–(2.59) -/
theorem proposition_2_19 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] ∧ I[X : Y ; μ] = H[Y ; μ] - H[Y | X ; μ] ∧
      I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[pair X Y ; μ] :=
  ⟨mutualInfo_eq_entropy_sub_condEntropy hμ X Y, mutualInfo_eq_entropy_sub_condEntropy' hμ X Y,
    mutualInfo_eq_add_sub hμ X Y⟩

/-- **Proposition 2.21.** -/
alias proposition_2_21 := condMutualInfo_self

/-- **Proposition 2.22.** (2.65)–(2.67) -/
theorem proposition_2_22 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | pair Y Z ; μ] ∧
      I[X : Y | Z ; μ] = H[Y | Z ; μ] - H[Y | pair X Z ; μ] ∧
        I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[pair X Y | Z ; μ] :=
  ⟨rfl, condMutualInfo_eq_sub_right hμ X Y Z, condMutualInfo_eq_add_sub hμ X Y Z⟩

/-- **Proposition 2.24 (Chain Rule for Entropy).** (2.85) -/
alias proposition_2_24 := chain_rule_entropy

/-- **Proposition 2.25 (Chain Rule for Conditional Entropy).** (2.89) -/
alias proposition_2_25 := chain_rule_entropy_cond

/-- **Proposition 2.26 (Chain Rule for Mutual Information).** (2.95) -/
alias proposition_2_26 := chain_rule_mutualInfo

/-- **Proposition 2.27 (Chain Rule for Conditional Mutual Information).** (2.99) -/
alias proposition_2_27 := chain_rule_condMutualInfo_prefix

/-- **Lemma 2.29 (Fundamental Inequality).** (2.101) -/
theorem lemma_2_29 {a : ℝ} (ha : 0 < a) : log a ≤ a - 1 ∧ (log a = a - 1 ↔ a = 1) :=
  ⟨log_le_sub_one_of_pos ha, log_eq_sub_one_iff ha⟩

/-- **Corollary 2.30.** (2.102) -/
theorem corollary_2_30 {a : ℝ} (ha : 0 < a) : 1 - a⁻¹ ≤ log a ∧ (log a = 1 - a⁻¹ ↔ a = 1) :=
  ⟨one_sub_inv_le_log_of_pos ha, log_eq_one_sub_inv_iff ha⟩

/-- **Theorem 2.31 (Divergence Inequality).** (2.103) -/
theorem theorem_2_31 {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q) :
    0 ≤ relEntropy p q ∧ (relEntropy p q = 0 ↔ p = q) :=
  ⟨relEntropy_nonneg hp hq, relEntropy_eq_zero_iff hp hq⟩

/-- **Theorem 2.32 (Log-Sum Inequality).** (2.111) -/
theorem theorem_2_32 {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * log (a i / b i) ∧
      ((∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) = ∑ i ∈ s, a i * log (a i / b i) ↔
        ∃ c : ℝ, ∀ i ∈ s, a i = c * b i) :=
  ⟨log_sum_inequality s ha hb hab, log_sum_inequality_eq_iff s ha hb hab⟩

/-- **Theorem 2.33 (Pinsker's Inequality).** (2.116), in nats. -/
alias theorem_2_33 := pinsker

/-- **Theorem 2.34.** (2.117) -/
theorem theorem_2_34 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ I[X : Y | Z ; μ] ∧ (I[X : Y | Z ; μ] = 0 ↔ CondIndep μ X Y Z) :=
  ⟨condMutualInfo_nonneg hμ X Y Z, condMutualInfo_eq_zero_iff hμ X Y Z⟩

/-- **Proposition 2.35.** -/
alias proposition_2_35 := entropy_eq_zero_iff

/-- **Proposition 2.36.** -/
alias proposition_2_36 := condEntropy_eq_zero_iff

/-- **Proposition 2.37.** -/
alias proposition_2_37 := mutualInfo_eq_zero_iff

/-- **Theorem 2.38 (Conditioning Does Not Increase Entropy).** (2.127) -/
theorem theorem_2_38 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) :
    H[Y | X ; μ] ≤ H[Y ; μ] ∧ (H[Y | X ; μ] = H[Y ; μ] ↔ IndepRV μ X Y) :=
  ⟨condEntropy_le_entropy hμ Y X, by
    rw [condEntropy_eq_entropy_iff hμ Y X]
    exact ⟨IndepRV.symm, IndepRV.symm⟩⟩

/-- **Theorem 2.39 (Independence Bound for Entropy).** (2.129) -/
theorem theorem_2_39 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (n : ℕ) :
    H[prefixRV X n ; μ] ≤ ∑ i ∈ range n, H[X i ; μ] ∧
      (H[prefixRV X n ; μ] = ∑ i ∈ range n, H[X i ; μ] ↔ IndepFamily μ X n) :=
  ⟨entropy_prefixRV_le_sum hμ X n, entropy_prefixRV_eq_sum_iff hμ X n⟩

/-- **Theorem 2.40.** (2.142) -/
theorem theorem_2_40 {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    I[X : Y ; μ] ≤ I[X : pair Y Z ; μ] ∧
      (I[X : pair Y Z ; μ] = I[X : Y ; μ] ↔ MarkovChain μ X Y Z) :=
  ⟨mutualInfo_le_mutualInfo_pair hμ X Y Z, mutualInfo_pair_eq_iff hμ X Y Z⟩

/-- **Lemma 2.41.** (2.144)–(2.145) -/
theorem lemma_2_41 {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : MarkovChain μ X Y Z) : I[X : Z ; μ] ≤ I[X : Y ; μ] ∧ I[X : Z ; μ] ≤ I[Y : Z ; μ] :=
  ⟨data_processing hμ h, data_processing' hμ h⟩

/-- **Theorem 2.42 (Data Processing Theorem).** (2.154) -/
alias theorem_2_42 := IsMarkovChain.data_processing

/-- **Theorem 2.43.** (2.157) -/
theorem theorem_2_43 {p : α → ℝ} (hp : IsPMF p) :
    entropy p ≤ log (Fintype.card α) ∧ (entropy p = log (Fintype.card α) ↔ p = uniformPMF α) :=
  ⟨entropy_le_log_card hp, entropy_eq_log_card_iff hp⟩

/-- **Corollary 2.44.** -/
alias corollary_2_44 := exists_entropy_eq

/-- **Theorem 2.47 (Fano's Inequality).** (2.171) -/
theorem theorem_2_47 {μ : Ω → ℝ} (hμ : IsPMF μ) (X X' : Ω → α) :
    H[X | X' ; μ] ≤ binEntropy (errProb μ X X' id) +
      errProb μ X X' id * log ((Fintype.card α : ℝ) - 1) :=
  fano hμ X X' id

/-- **Corollary 2.48.** In nats, the `1` of the book being `log 2`. -/
theorem corollary_2_48 {μ : Ω → ℝ} (hμ : IsPMF μ) (X X' : Ω → α) :
    H[X | X' ; μ] < log 2 + errProb μ X X' id * log (Fintype.card α) :=
  fano_lt hμ X X' id

/-- **Theorem 2.50.** (2.193)–(2.194) -/
theorem theorem_2_50 {ι : Type*} [Fintype ι] {f p : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ)
    (lam a : ι → ℝ) (hf : IsPMF f) (hform : ∀ x, f x = exp (-lam₀ - ∑ i, lam i * r i x))
    (hfc : ∀ i, ∑ x, f x * r i x = a i) (hp : IsPMF p) (hcon : ∀ i, ∑ x, p x * r i x = a i) :
    entropy p ≤ entropy f :=
  entropy_le_of_eq_exp r (-lam₀) (fun i => -lam i) hf
    (fun x => by rw [hform]; simp [sub_eq_add_neg, sum_neg_distrib]) hp
    fun i => (hcon i).trans (hfc i).symm

/-- **Corollary 2.51.** (2.205) -/
theorem corollary_2_51 {ι : Type*} [Fintype ι] {f p : α → ℝ} (r : ι → α → ℝ) (lam₀ : ℝ)
    (lam : ι → ℝ) (hf : IsPMF f) (hform : ∀ x, f x = exp (-lam₀ - ∑ i, lam i * r i x))
    (hp : IsPMF p) (hcon : ∀ i, ∑ x, p x * r i x = ∑ x, f x * r i x) :
    entropy p ≤ entropy f :=
  theorem_2_50 r lam₀ lam _ hf hform (fun _ => rfl) hp hcon

/-- **Example 2.52.** Without constraints, the uniform distribution has the largest entropy. -/
alias example_2_52 := entropy_le_log_card

/-- **Example 2.55.** -/
alias example_2_55 := iidProcess_hasEntropyRate

/-- **Lemma 2.58.** -/
alias lemma_2_58 := StochasticProcess.IsStationary.hasCondEntropyRate

/-- **Lemma 2.59 (Cesáro Mean).** -/
alias lemma_2_59 := cesaro_mean

/-- **Theorem 2.60.** -/
alias theorem_2_60 := StochasticProcess.IsStationary.hasEntropyRate

/-! ### Pairwise independence does not imply mutual independence -/

/-- The bits `X₀`, `X₁` of a uniform pair and their sum `X₂ = X₀ ⊕ X₁`. -/
def xorTriple : ℕ → Bool × Bool → Bool := fun i ω =>
  if i = 0 then ω.1 else if i = 1 then ω.2 else xor ω.1 ω.2

/-- **The remark after Definition 2.3.** `X₀`, `X₁` and `X₀ ⊕ X₁` are pairwise independent. -/
theorem pairwiseIndep_xorTriple : PairwiseIndep (uniformPMF (Bool × Bool)) xorTriple 3 := by
  intro i j hij hj x y
  interval_cases j <;> interval_cases i <;>
    cases x <;> cases y <;> simp [dist, pair, xorTriple, uniformPMF, Fintype.sum_prod_type] <;>
      norm_num

/-- **The remark after Definition 2.3.** `X₀`, `X₁` and `X₀ ⊕ X₁` are not mutually independent:
the three bits cannot all be `1`. -/
theorem not_indepFamily_xorTriple : ¬IndepFamily (uniformPMF (Bool × Bool)) xorTriple 3 := by
  intro h
  have := h ![true, true, true]
  simp [dist, prefixRV, xorTriple, uniformPMF, Fintype.sum_prod_type, funext_iff,
    Fin.forall_fin_succ, Fin.prod_univ_three] at this

end InfoTheory.Yeung
