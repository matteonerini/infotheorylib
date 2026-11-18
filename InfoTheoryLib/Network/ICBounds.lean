/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.ICCode
public import InfoTheoryLib.Network.MACMultiLetter

/-!
# Outer bounds on the capacity region of the interference channel

Fano's inequality at each receiver, and the fact that the capacity region of the DM-IC depends only
on the conditional marginals, give Sato's outer bound: for every channel `p̃(y₁, y₂ | x₁, x₂)` with
the same conditional marginals, `R₁ ≤ I(X₁; Y₁ | X₂, Q)`, `R₂ ≤ I(X₂; Y₂ | X₁, Q)`,
`R₁ + R₂ ≤ I(X₁, X₂; Y₁, Y₂ | Q)`.

## Main definitions

* `icAvg₁ q p₁ p₂ V`, `icAvg₂ q p₁ p₂ V`, `icAvg₁₂ q p₁ p₂ V`: the informations `I(X₁; Y | X₂, Q)`,
  `I(X₂; Y | X₁, Q)` and `I(X₁, X₂; Y | Q)` for `p(q) p(x₁ | q) p(x₂ | q) p(y | x₁, x₂)`.
* `icSatoRegionBits W W'`: Sato's outer bound for the channel `W'`, in bits.
* `ICCode.letter₁`, `ICCode.letter₂`: the laws of the inputs at each time.

## Main statements

* `ICCode.log_le_sum_macInfo₁`, `ICCode.log_le_sum_macInfo₂`: Fano's inequality and
  `I(X₁ⁿ; Y₁ⁿ) ≤ ∑ᵢ I(X₁ᵢ; Y₁ᵢ | X₂ᵢ)` for a single code.
* `tendsto_icEps`, `mem_closure_of_sub_icEps`: the limit argument of the converses.
* `IsAchievableICBits.mem_closure_icSatoRegionBits`: **Sato's outer bound**.
* `icCapacityRegionBits_subset_outer`: the simple outer bound `R₁ ≤ C₁`, `R₂ ≤ C₂`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 6
-/

open Real Finset Filter Topology Set

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
  {W W' : α₁ × α₂ → β₁ × β₂ → ℝ}

/-! ### The informations with a time-sharing variable -/

section Avg

variable {β : Type*} [Fintype β] {k : ℕ}

/-- `I(X₁; Y | X₂, Q)` for `p(q) p(x₁ | q) p(x₂ | q) p(y | x₁, x₂)`. -/
def icAvg₁ (q : Fin k → ℝ) (p₁ : Fin k → α₁ → ℝ) (p₂ : Fin k → α₂ → ℝ)
    (V : α₁ × α₂ → β → ℝ) : ℝ := ∑ i, q i * macInfo₁ (p₁ i) (p₂ i) V

/-- `I(X₂; Y | X₁, Q)` for `p(q) p(x₁ | q) p(x₂ | q) p(y | x₁, x₂)`. -/
def icAvg₂ (q : Fin k → ℝ) (p₁ : Fin k → α₁ → ℝ) (p₂ : Fin k → α₂ → ℝ)
    (V : α₁ × α₂ → β → ℝ) : ℝ := ∑ i, q i * macInfo₂ (p₁ i) (p₂ i) V

/-- `I(X₁, X₂; Y | Q)` for `p(q) p(x₁ | q) p(x₂ | q) p(y | x₁, x₂)`. -/
def icAvg₁₂ (q : Fin k → ℝ) (p₁ : Fin k → α₁ → ℝ) (p₂ : Fin k → α₂ → ℝ)
    (V : α₁ × α₂ → β → ℝ) : ℝ := ∑ i, q i * macInfo₁₂ (p₁ i) (p₂ i) V

end Avg

/-- **Sato's outer bound (Lecture 6 of [elgamal2010]).** The rate pairs with
`R₁ ≤ I(X₁; Y₁ | X₂, Q)`, `R₂ ≤ I(X₂; Y₂ | X₁, Q)` and `R₁ + R₂ ≤ I(X₁, X₂; Y₁, Y₂ | Q)` for some
`p(q) p(x₁ | q) p(x₂ | q)`, in bits, where the last information is computed with the channel `W'`,
which has the same conditional marginals as `W`. -/
def icSatoRegionBits (W W' : α₁ × α₂ → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k → ℝ) (p₁ : Fin k → α₁ → ℝ) (p₂ : Fin k → α₂ → ℝ),
    IsPMF q ∧ (∀ i, IsPMF (p₁ i)) ∧ (∀ i, IsPMF (p₂ i)) ∧
    R.1 ≤ icAvg₁ q p₁ p₂ (bcMarg₁ W) / log 2 ∧ R.2 ≤ icAvg₂ q p₁ p₂ (bcMarg₂ W) / log 2 ∧
    R.1 + R.2 ≤ icAvg₁₂ q p₁ p₂ W' / log 2}

/-! ### The bounds for a single code -/

namespace ICCode

variable {M₁ M₂ n : ℕ} (c : ICCode M₁ M₂ n α₁ α₂ β₁ β₂)

/-- The law of the codeword of sender 1, for a uniform message. -/
def codeword₁ : (Fin n → α₁) → ℝ := dist (uniformPMF (Fin M₁)) c.enc₁

/-- The law of the codeword of sender 2, for a uniform message. -/
def codeword₂ : (Fin n → α₂) → ℝ := dist (uniformPMF (Fin M₂)) c.enc₂

/-- The law of the input `X₁ᵢ` of sender 1 at time `i`. -/
def letter₁ (i : Fin n) : α₁ → ℝ := dist c.codeword₁ fun x => x i

/-- The law of the input `X₂ᵢ` of sender 2 at time `i`. -/
def letter₂ (i : Fin n) : α₂ → ℝ := dist c.codeword₂ fun x => x i

variable (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
include hW h₁ h₂

omit [Fintype α₁] [Fintype α₂] in
/-- **(Lecture 6 of [elgamal2010]).** Fano's inequality at receiver 1:
`H(M₁ | Y₁ⁿ) ≤ log 2 + P₁ log M₁`. -/
lemma condEntropy_msg₁_le :
    H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁) => z.1.1 | Prod.snd ;
      (c.toMACOf fun y => (c.dec₁ y, (⟨0, h₂⟩ : Fin M₂))).jointLaw (bcMarg₁ W)] ≤
      log 2 + c.errProb₁ W * log M₁ := by
  classical
  have hμ := (c.toMACOf fun y => (c.dec₁ y, (⟨0, h₂⟩ : Fin M₂))).jointLaw_isPMF hW.bcMarg₁ h₁ h₂
  have h := fano_weak hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁) => z.1.1) Prod.snd c.dec₁
  rw [Fintype.card_fin] at h
  have e : InfoTheory.errProb
      ((c.toMACOf fun y => (c.dec₁ y, (⟨0, h₂⟩ : Fin M₂))).jointLaw (bcMarg₁ W))
      (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁) => z.1.1) Prod.snd c.dec₁ = c.errProb₁ W := by
    rw [ICCode.errProb₁_eq]
    simp only [InfoTheory.errProb, Fintype.sum_prod_type, MACCode.jointLaw, codeLaw, uniformPMF,
      Fintype.card_prod, Fintype.card_fin, MACCode.input, toMACOf]
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    push_cast
    split_ifs <;> ring
  rwa [e] at h

omit [Fintype α₁] [Fintype α₂] in
/-- **(Lecture 6 of [elgamal2010]).** Fano's inequality at receiver 2:
`H(M₂ | Y₂ⁿ) ≤ log 2 + P₂ log M₂`. -/
lemma condEntropy_msg₂_le :
    H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₂) => z.1.2 | Prod.snd ;
      (c.toMACOf fun y => ((⟨0, h₁⟩ : Fin M₁), c.dec₂ y)).jointLaw (bcMarg₂ W)] ≤
      log 2 + c.errProb₂ W * log M₂ := by
  classical
  have hμ := (c.toMACOf fun y => ((⟨0, h₁⟩ : Fin M₁), c.dec₂ y)).jointLaw_isPMF hW.bcMarg₂ h₁ h₂
  have h := fano_weak hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₂) => z.1.2) Prod.snd c.dec₂
  rw [Fintype.card_fin] at h
  have e : InfoTheory.errProb
      ((c.toMACOf fun y => ((⟨0, h₁⟩ : Fin M₁), c.dec₂ y)).jointLaw (bcMarg₂ W))
      (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₂) => z.1.2) Prod.snd c.dec₂ = c.errProb₂ W := by
    rw [ICCode.errProb₂_eq]
    simp only [InfoTheory.errProb, Fintype.sum_prod_type, MACCode.jointLaw, codeLaw, uniformPMF,
      Fintype.card_prod, Fintype.card_fin, MACCode.input, toMACOf]
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    push_cast
    split_ifs <;> ring
  rwa [e] at h

/-- **(Lecture 6 of [elgamal2010]).** `log M₁ ≤ I(X₁ⁿ; Y₁ⁿ) + log 2 + P₁ log M₁`. -/
theorem log_le_mutualInfoOf_codeword₁ :
    log M₁ ≤ mutualInfoOf c.codeword₁ (macChannel₁ (macExt (bcMarg₁ W) n) c.codeword₂) + log 2 +
      c.errProb₁ W * log M₁ := by
  have h0 := (c.toMACOf fun y => (c.dec₁ y, (⟨0, h₂⟩ : Fin M₂))).log_le_mutualInfoOf₁_add
    hW.bcMarg₁ h₁ h₂
  have h5 := c.condEntropy_msg₁_le hW h₁ h₂
  have e : mutualInfoOf (c.toMACOf fun y => (c.dec₁ y, (⟨0, h₂⟩ : Fin M₂))).codewordDist₁
      (macChannel₁ (macExt (bcMarg₁ W) n)
        (c.toMACOf fun y => (c.dec₁ y, (⟨0, h₂⟩ : Fin M₂))).codewordDist₂) =
      mutualInfoOf c.codeword₁ (macChannel₁ (macExt (bcMarg₁ W) n) c.codeword₂) := rfl
  rw [e] at h0
  linarith

/-- **(Lecture 6 of [elgamal2010]).** `log M₂ ≤ I(X₂ⁿ; Y₂ⁿ) + log 2 + P₂ log M₂`. -/
theorem log_le_mutualInfoOf_codeword₂ :
    log M₂ ≤ mutualInfoOf c.codeword₂ (macChannel₂ (macExt (bcMarg₂ W) n) c.codeword₁) + log 2 +
      c.errProb₂ W * log M₂ := by
  have h0 := (c.toMACOf fun y => ((⟨0, h₁⟩ : Fin M₁), c.dec₂ y)).log_le_mutualInfoOf₂_add
    hW.bcMarg₂ h₁ h₂
  have h5 := c.condEntropy_msg₂_le hW h₁ h₂
  have e : mutualInfoOf (c.toMACOf fun y => ((⟨0, h₁⟩ : Fin M₁), c.dec₂ y)).codewordDist₂
      (macChannel₂ (macExt (bcMarg₂ W) n)
        (c.toMACOf fun y => ((⟨0, h₁⟩ : Fin M₁), c.dec₂ y)).codewordDist₁) =
      mutualInfoOf c.codeword₂ (macChannel₂ (macExt (bcMarg₂ W) n) c.codeword₁) := rfl
  rw [e] at h0
  linarith

/-- **(Lecture 6 of [elgamal2010]).** `log M₁ ≤ ∑ᵢ I(X₁ᵢ; Y₁ᵢ | X₂ᵢ) + log 2 + P₁ log M₁`. -/
theorem log_le_sum_macInfo₁ :
    log M₁ ≤ ∑ i, macInfo₁ (c.letter₁ i) (c.letter₂ i) (bcMarg₁ W) + log 2 +
      c.errProb₁ W * log M₁ := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hP₁ : IsPMF c.codeword₁ := uniformPMF_isPMF.dist _
  have hP₂ : IsPMF c.codeword₂ := uniformPMF_isPMF.dist _
  have h0 := c.log_le_mutualInfoOf_codeword₁ hW h₁ h₂
  have h1 := mutualInfoOf_macChannel₁_le hP₁ hP₂ (macExt_isChannel hW.bcMarg₁ n)
  have h2 := (macInfo_macExt_le hP₁ hP₂ hW.bcMarg₁).1
  simp only [letter₁, letter₂]
  linarith

/-- **(Lecture 6 of [elgamal2010]).** `log M₂ ≤ ∑ᵢ I(X₂ᵢ; Y₂ᵢ | X₁ᵢ) + log 2 + P₂ log M₂`. -/
theorem log_le_sum_macInfo₂ :
    log M₂ ≤ ∑ i, macInfo₂ (c.letter₁ i) (c.letter₂ i) (bcMarg₂ W) + log 2 +
      c.errProb₂ W * log M₂ := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hP₁ : IsPMF c.codeword₁ := uniformPMF_isPMF.dist _
  have hP₂ : IsPMF c.codeword₂ := uniformPMF_isPMF.dist _
  have h0 := c.log_le_mutualInfoOf_codeword₂ hW h₁ h₂
  have h1 := mutualInfoOf_macChannel₂_le hP₁ hP₂ (macExt_isChannel hW.bcMarg₂ n)
  have h2 := (macInfo_macExt_le hP₁ hP₂ hW.bcMarg₂).2.1
  simp only [letter₁, letter₂]
  linarith

omit hW in
/-- **Sato's outer bound (Lecture 6 of [elgamal2010]), for one code.** Both receivers together
decode both messages: `log (M₁ M₂) ≤ ∑ᵢ I(X₁ᵢ, X₂ᵢ; Y₁ᵢ, Y₂ᵢ) + log 2 + P_e log (M₁ M₂)`. -/
theorem log_mul_le_sum_macInfo₁₂ (hW' : IsChannel W') :
    log (M₁ * M₂) ≤ ∑ i, macInfo₁₂ (c.letter₁ i) (c.letter₂ i) W' + log 2 +
      c.errProb W' * log (M₁ * M₂) := by
  classical
  set m : MACCode M₁ M₂ n α₁ α₂ (β₁ × β₂) :=
    c.toMACOf fun y => (c.dec₁ fun i => (y i).1, c.dec₂ fun i => (y i).2)
  have h0 := m.log_mul_le_macInfo₁₂ hW' h₁ h₂
  have e₁ : ∀ i, m.letterDist₁ i = c.letter₁ i := fun i =>
    (dist_comp_eq (uniformPMF (Fin M₁)) c.enc₁ fun x => x i)
  have e₂ : ∀ i, m.letterDist₂ i = c.letter₂ i := fun i =>
    (dist_comp_eq (uniformPMF (Fin M₂)) c.enc₂ fun x => x i)
  have e₃ : m.avgErrProb W' = c.errProb W' := by
    simp only [MACCode.avgErrProb, MACCode.condErrProb, ICCode.errProb, BCCode.errProb,
      Fintype.sum_prod_type, m, toMACOf, toBC, MACCode.input, ne_eq, Prod.mk.injEq, not_and_or]
    congr!
  simp only [e₁, e₂, e₃] at h0
  exact h0

end ICCode

/-! ### The limit argument -/

section Limit

lemma log_two_pow_ceil_bounds (n : ℕ) (R : ℝ) :
    n * R * log 2 ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ∧
      log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ (n * |R| + 1) * log 2 := by
  have hl := log_pos one_lt_two
  have e : log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) = ⌈n * R⌉₊ * log 2 := by
    push_cast
    rw [log_pow]
  rw [e]
  refine ⟨mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl.le,
    mul_le_mul_of_nonneg_right ?_ hl.le⟩
  have hR : (n : ℝ) * R ≤ n * |R| := mul_le_mul_of_nonneg_left (le_abs_self R) (Nat.cast_nonneg n)
  have h0 : 0 ≤ (n : ℝ) * |R| := by positivity
  exact (Nat.cast_le.2 (Nat.ceil_mono hR)).trans (Nat.ceil_lt_add_one h0).le

/-- The excess rate `εₙ = (2 log 2 + Pₙ (log M₁ + log M₂)) / (n log 2)` of the converses, with
`Mⱼ = 2^⌈nRⱼ⌉`. -/
def icEps (R₁ R₂ : ℝ) (P : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 * log 2 + P n * (log ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) + log ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ))) / (n * log 2)

lemma icEps_nonneg {R₁ R₂ : ℝ} {P : ℕ → ℝ} (hP : ∀ n, 0 ≤ P n) (n : ℕ) : 0 ≤ icEps R₁ R₂ P n := by
  have hl := log_pos one_lt_two
  have hM : ∀ R : ℝ, 0 ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := fun R =>
    log_natCast_nonneg _
  have := mul_nonneg (hP n) (add_nonneg (hM R₁) (hM R₂))
  exact div_nonneg (by linarith) (by positivity)

/-- **(Lecture 6 of [elgamal2010]).** `εₙ → 0` when `Pₙ → 0`. -/
lemma tendsto_icEps {R₁ R₂ : ℝ} {P : ℕ → ℝ} (hP : ∀ n, 0 ≤ P n) (hP0 : Tendsto P atTop (𝓝 0)) :
    Tendsto (icEps R₁ R₂ P) atTop (𝓝 0) := by
  have hl := log_pos one_lt_two
  set K := |R₁| + |R₂| + 2
  have hup : Tendsto (fun n : ℕ => 2 / (n : ℝ) + P n * K) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add (hP0.mul_const K)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => icEps_nonneg hP n) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have b₁ := (log_two_pow_ceil_bounds n R₁).2
  have b₂ := (log_two_pow_ceil_bounds n R₂).2
  have hA : log ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) + log ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ) ≤ n * K * log 2 := by
    have : (n * |R₁| + 1) * log 2 + (n * |R₂| + 1) * log 2 ≤ n * K * log 2 := by
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ hl.le
      simp only [K]
      nlinarith
    linarith
  rw [icEps, div_le_iff₀ (by positivity)]
  have h3 := mul_le_mul_of_nonneg_left hA (hP n)
  have e : (2 / (n : ℝ) + P n * K) * (n * log 2) = 2 * log 2 + P n * (n * K * log 2) := by
    field_simp
  rw [e]
  linarith

/-- The points `(R₁ - εₙ, R₂ - εₙ)` tend to `(R₁, R₂)`. -/
lemma mem_closure_of_sub_icEps {S : Set (ℝ × ℝ)} {R₁ R₂ : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ S) :
    (R₁, R₂) ∈ closure S := by
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono h)

/-- A bound `n a log 2 ≤ S + (2 log 2 + P (A + B))` on the rate `a` of a code of block length `n`
gives `a - εₙ ≤ (1/n) S / log 2`. -/
lemma sub_icEps_le {R₁ R₂ a S : ℝ} {P : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (h : n * a * log 2 ≤ S + (2 * log 2 + P n * (log ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) +
      log ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ)))) :
    a - icEps R₁ R₂ P n ≤ (1 / n * S) / log 2 := by
  have hl := log_pos one_lt_two
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sub_le_iff_le_add, icEps, div_eq_mul_inv (1 / (n : ℝ) * S), one_div_mul_eq_div]
  have e : S / n * (log 2)⁻¹ = S / (n * log 2) := by field_simp
  rw [e, ← add_div, le_div_iff₀ (by positivity)]
  linarith

end Limit

/-! ### Sato's outer bound -/

omit [Fintype α₁] [Fintype α₂] in
lemma two_pow_ceil_pos (n : ℕ) (R : ℝ) : 0 < 2 ^ ⌈n * R⌉₊ := by positivity

/-- **Sato's outer bound (Lecture 6 of [elgamal2010]).** Every achievable rate pair of the DM-IC is
in the closure of the rate pairs with `R₁ ≤ I(X₁; Y₁ | X₂, Q)`, `R₂ ≤ I(X₂; Y₂ | X₁, Q)` and
`R₁ + R₂ ≤ I(X₁, X₂; Y₁, Y₂ | Q)`, the last information being computed with any channel `W'` with
the same conditional marginals. The time-sharing variable `Q` is uniform on the `n` positions. -/
theorem IsAchievableICBits.mem_closure_icSatoRegionBits (hW : IsChannel W) (hW' : IsChannel W')
    (h₁ : bcMarg₁ W = bcMarg₁ W') (h₂ : bcMarg₂ W = bcMarg₂ W') {R₁ R₂ : ℝ}
    (h : IsAchievableICBits W R₁ R₂) : (R₁, R₂) ∈ closure (icSatoRegionBits W W') := by
  obtain ⟨c, hc⟩ := h
  have hl := log_pos one_lt_two
  set P : ℕ → ℝ := fun n => 2 * (c n).errProb W
  have hP : ∀ n, 0 ≤ P n := fun n => mul_nonneg (by norm_num) ((c n).errProb_nonneg hW)
  have hP0 : Tendsto P atTop (𝓝 0) := by simpa using hc.const_mul 2
  refine mem_closure_of_sub_icEps (tendsto_icEps (R₁ := R₁) (R₂ := R₂) hP hP0) fun n hn => ?_
  have hM₁ := two_pow_ceil_pos n R₁
  have hM₂ := two_pow_ceil_pos n R₂
  have : Nonempty (Fin (2 ^ ⌈n * R₁⌉₊)) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin (2 ^ ⌈n * R₂⌉₊)) := ⟨⟨0, hM₂⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A := log ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ)
  set B := log ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ)
  have hA : 0 ≤ A := log_natCast_nonneg _
  have hB : 0 ≤ B := log_natCast_nonneg _
  have l₁ : n * R₁ * log 2 ≤ A := (log_two_pow_ceil_bounds n R₁).1
  have l₂ : n * R₂ * log 2 ≤ B := (log_two_pow_ceil_bounds n R₂).1
  have hAB : log (((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) * ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ)) = A + B :=
    log_mul (by exact_mod_cast hM₁.ne') (by exact_mod_cast hM₂.ne')
  have b₁ := (c n).log_le_sum_macInfo₁ hW hM₁ hM₂
  have b₂ := (c n).log_le_sum_macInfo₂ hW hM₁ hM₂
  have b₃ := (c n).log_mul_le_sum_macInfo₁₂ (W' := W') hM₁ hM₂ hW'
  rw [hAB] at b₃
  have e₁ := (c n).errProb₁_le hW
  have e₂ := (c n).errProb₂_le hW
  have e₁0 := (c n).errProb₁_nonneg hW
  have e₂0 := (c n).errProb₂_nonneg hW
  have e₃ : (c n).errProb W' ≤ P n := by
    have := (c n).errProb_le_add hW'
    rw [← (c n).errProb₁_congr h₁, ← (c n).errProb₂_congr h₂] at this
    simp only [P]
    linarith
  have m₁ := mul_le_mul_of_nonneg_right e₁ hA
  have m₂ := mul_le_mul_of_nonneg_right e₂ hB
  have m₃ := mul_le_mul_of_nonneg_right e₃ (add_nonneg hA hB)
  have mA : (c n).errProb W * A ≥ 0 := mul_nonneg ((c n).errProb_nonneg hW) hA
  have mB : (c n).errProb W * B ≥ 0 := mul_nonneg ((c n).errProb_nonneg hW) hB
  have hPe : P n * (A + B) = 2 * ((c n).errProb W * A) + 2 * ((c n).errProb W * B) := by
    simp only [P]
    ring
  have hE := icEps_nonneg (R₁ := R₁) (R₂ := R₂) hP n
  have hsum : (R₁ + R₂) - icEps R₁ R₂ P n ≤
      (1 / n * ∑ i, macInfo₁₂ ((c n).letter₁ i) ((c n).letter₂ i) W') / log 2 :=
    sub_icEps_le hn (by nlinarith)
  refine ⟨n, fun _ => 1 / n, fun i => (c n).letter₁ i, fun i => (c n).letter₂ i,
    ⟨fun _ => by positivity, by simp [hn'.ne']⟩, fun i => (uniformPMF_isPMF.dist _).dist _,
    fun i => (uniformPMF_isPMF.dist _).dist _, ?_, ?_, ?_⟩
  · simp only [icAvg₁, ← mul_sum]
    exact sub_icEps_le hn (by nlinarith)
  · simp only [icAvg₂, ← mul_sum]
    exact sub_icEps_le hn (by nlinarith)
  · simp only [icAvg₁₂, ← mul_sum]
    linarith

/-- **The simple outer bound (Lecture 6 of [elgamal2010]).** Every rate pair in the capacity region
of the DM-IC has `R₁ ≤ C₁ = max_{p(x₁), x₂} I(X₁; Y₁ | X₂ = x₂)` and
`R₂ ≤ C₂ = max_{p(x₂), x₁} I(X₂; Y₂ | X₁ = x₁)`. -/
theorem icCapacityRegionBits_subset_outer (hW : IsChannel W) :
    icCapacityRegionBits W ⊆
      {R | R.1 ≤ macC₁ (bcMarg₁ W) / log 2 ∧ R.2 ≤ macC₂ (bcMarg₂ W) / log 2} := by
  have hl := log_pos one_lt_two
  have hc : IsClosed {R : ℝ × ℝ | R.1 ≤ macC₁ (bcMarg₁ W) / log 2 ∧
      R.2 ≤ macC₂ (bcMarg₂ W) / log 2} :=
    (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le continuous_snd continuous_const)
  refine closure_minimal (fun R hR => ?_) hc
  have h := IsAchievableICBits.mem_closure_icSatoRegionBits hW hW rfl rfl hR
  refine closure_minimal ?_ hc h
  rintro S ⟨k, q, p₁, p₂, hq, hp₁, hp₂, h₁, h₂, -⟩
  have hb : ∀ (f : Fin k → ℝ) (C : ℝ), (∀ i, f i ≤ C) → ∑ i, q i * f i ≤ C := fun f C hf => by
    calc ∑ i, q i * f i ≤ ∑ i, q i * C :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (hq.nonneg i)
      _ = C := by rw [← sum_mul, hq.sum_eq_one, one_mul]
  exact ⟨h₁.trans (div_le_div_of_nonneg_right
      (hb _ _ fun i => macInfo₁_le_macC₁ (hp₁ i) (hp₂ i) hW.bcMarg₁) hl.le),
    h₂.trans (div_le_div_of_nonneg_right
      (hb _ _ fun i => macInfo₂_le_macC₂ (hp₁ i) (hp₂ i) hW.bcMarg₂) hl.le)⟩

end InfoTheory
