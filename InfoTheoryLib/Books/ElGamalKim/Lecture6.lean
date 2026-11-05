/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture4
public import InfoTheoryLib.Network.ICAchievability

/-!
# El Gamal & Kim, Lecture 6: Interference Channels

This file indexes the formalization of Lecture 6 of [elgamal2010] and contains the lecture's worked
examples, with aliases named after its results. The capacity region of the DM-IC is known in only a
few cases. We formalize the discrete memoryless part up to strong interference (Theorem 1), and for
the AWGN-IC only the formulas: its coding theorems need differential entropy tools that the library
does not have.

## Conventions

* **Rates.** Rates are in bits, with message sets `[1 : 2^{nRⱼ}] = {1, …, 2^⌈nRⱼ⌉}`, as in
  Lecture 3. Information quantities such as `icAvg₁` are in nats, and a bound in bits is the
  quantity divided by `log 2`.
* **Regions.** Rate regions are sets of pairs `R : ℝ × ℝ`, and are not intersected with
  `R₁, R₂ ≥ 0`. The capacity region is `icCapacityRegionBits W`.
* **Time sharing.** `Q` takes values in `Fin k`, for some `k`, with `q : Fin k → ℝ`, and the inputs
  have laws `p₁ i`, `p₂ i` given `Q = i`. As `k` is not bounded, Theorem 1 is stated up to closure.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Problem setup
* The DM-IC and a `(2^{nR₁}, 2^{nR₂}, n)` code: `ICCode`, `ICCode.toBC`, `ICCode.errProb`,
  `ICCode.errProb₁`, `ICCode.errProb₂` (`Network.ICCode`).
* Achievable rate pairs and the capacity region: `IsAchievableICBits`, `icCapacityRegionBits`.
* The capacity region depends only on the marginals: `isAchievableICBits_congr`,
  `icCapacityRegionBits_eq_of_marg_eq`.

### Inner and outer bounds
* The simple outer bound: `icCapacityRegionBits_subset_outer` (`Network.ICBounds`).
* The modulo-2 sum IC, whose capacity region is the time-division bound: `icSameOutput`,
  `moduloTwoIC`, `icCapacityRegionBits_moduloTwoIC` (here).
* Sato's outer bound: `icSatoRegionBits`, `IsAchievableICBits.mem_closure_icSatoRegionBits`, with
  Fano's inequality at each receiver `ICCode.log_le_sum_macInfo₁`, `ICCode.log_le_sum_macInfo₂`,
  `ICCode.log_mul_le_sum_macInfo₁₂`.
* The simultaneous decoding inner bound: `icSimultaneousRegionBits`,
  `icSimultaneousRegionBits_subset` (`Network.ICAchievability`), by compound random coding
  `exists_icCode_err_le` (`Network.ICSuperLetter`) and, in place of coded time sharing,
  super-letters: `exists_timeSharing_pattern`, `macInfo₁_macExt_indexedPMF`,
  `macInfo₂_macExt_indexedPMF`, `macInfo₁₂_macExt_indexedPMF`, `ICCode.flatten`,
  `ICCode.err₁_flatten`, `ICCode.err₂_flatten`.
* The IC with the same marginals is a DM-MAC: `isAchievableICBits_iff_of_same_marg`,
  `icCapacityRegionBits_eq_of_same_marg` (`Network.ICCode`).

### Strong interference
* Very strong and strong interference: `IsVeryStrongIC`, `IsStrongIC`, `IsVeryStrongIC.isStrongIC`
  (`Network.ICStrong`).
* The example `Y₁ = Y₂ = X₁ + X₂`, strong but not very strong: `sumIC`, `sumIC_isStrongIC`,
  `sumIC_not_isVeryStrongIC` (here).
* Lemma 1: `IsStrongIC.macInfo₁_macExt_le`, `IsStrongIC.macInfo₂_macExt_le`, from the fact that a
  product of more capable channels is more capable: `mutualInfoOf_indexedExt_le`,
  `mutualInfoOf_side_indexedExt_le`, `mutualInfoOf_sideOut`.
* Theorem 1: `icStrongRegionBits`, `icCapacityRegionBits_eq_closure_icStrongRegionBits`
  (`Network.ICAchievability`), with the converse `IsAchievableICBits.mem_closure_icStrongRegionBits`
  (`Network.ICStrong`).

### AWGN interference channel (formulas)
* The region of Theorem 2 and of the simultaneous decoding inner bound: `awgnICRegion` (here).
* The very strong condition makes the sum-rate bound inactive, so that the region is a rectangle:
  `awgnICRegion_eq_of_veryStrong` (here).
* The symmetric degrees of freedom: `symmetricDoF`, with the redundant bound `(d)` of page 6-52
  `symmetricDoF_eq` and the "W" shape `symmetricDoF_half`, `symmetricDoF_two_thirds`,
  `symmetricDoF_one`, `symmetricDoF_of_two_le` (here).

## Not formalized

* The time-division inner bound in general (the time-sharing code for the DM-IC), and the
  treat-interference-as-noise inner bound.
* The tighter inner bound on page 6-7, where a receiver need not decode the other message correctly.
* The cardinality bound `|Q| ≤ 4` in Theorem 1.
* The Han–Kobayashi inner bound (Theorem 4) with its Fourier–Motzkin elimination, the deterministic
  IC (Theorem 5), and the semideterministic IC with Lemma 3 and Proposition 5.
* All the coding theorems for the AWGN-IC: Theorem 2, the sum capacity under weak interference
  (Theorem 3) with Lemma 2, the half-bit theorem and the limit `d*(α)` of the degrees of freedom.
  They need conditional differential entropy, jointly Gaussian variables and the fact that Gaussian
  noise is the worst additive noise.
* The `q`-ary expansion deterministic IC, its linear codes, and more than two user pairs.

## Issues in the notes

* The numbered results are out of order: Theorem 4 and Theorem 5 come before Theorem 3, and the
  gap result is called Proposition 5, although there is no Proposition 1–4.
* **Page 6-9.** "decoder `j` transmits `xⱼⁿ(m_k)`" should be "encoder `j` transmits `xⱼⁿ(mⱼ)`".
* **Page 6-29.** "decoder 2 knows `T₂ⁿ`" should be "decoder 2 knows `T₁ⁿ`".
* **Page 6-52.** The bound `(d)` is said to be tight only at `α = 2/3`; it is also tight at `α = 0`,
  where all the bounds equal `1`. It is redundant, as the notes say: `symmetricDoF_eq`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 6
-/

open Real Finset Set

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Interference channels with the same output -/

section SameOutput

variable {α₁ α₂ β : Type*} [Fintype β] [DecidableEq β]

/-- The DM-IC with the same output at both receivers, `Y₁ = Y₂`, each with `p(y | x₁, x₂)`. -/
def icSameOutput (V : α₁ × α₂ → β → ℝ) : α₁ × α₂ → β × β → ℝ :=
  fun x y => if y.1 = y.2 then V x y.1 else 0

lemma bcMarg₁_icSameOutput (V : α₁ × α₂ → β → ℝ) : bcMarg₁ (icSameOutput V) = V := by
  funext x y
  simp [bcMarg₁, icSameOutput]

lemma bcMarg₂_icSameOutput (V : α₁ × α₂ → β → ℝ) : bcMarg₂ (icSameOutput V) = V := by
  funext x y
  simp [bcMarg₂, icSameOutput]

lemma icSameOutput_isChannel {V : α₁ × α₂ → β → ℝ} (hV : IsChannel V) :
    IsChannel (icSameOutput V) := fun x => by
  refine ⟨fun y => ?_, ?_⟩
  · unfold icSameOutput
    split_ifs
    · exact (hV x).nonneg _
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    simpa [icSameOutput] using (hV x).sum_eq_one

/-- With the same output, the capacity region is the one of the DM-MAC with that output. -/
theorem icCapacityRegionBits_icSameOutput {V : α₁ × α₂ → β → ℝ} (hV : IsChannel V) :
    icCapacityRegionBits (icSameOutput V) = macCapacityRegionBits V :=
  icCapacityRegionBits_eq_of_same_marg (icSameOutput_isChannel hV) (bcMarg₁_icSameOutput V)
    (bcMarg₂_icSameOutput V)

variable [Fintype α₁] [Fintype α₂]

/-- With the same output, the interference is strong: the two conditions are equalities. -/
theorem icSameOutput_isStrongIC (V : α₁ × α₂ → β → ℝ) : IsStrongIC (icSameOutput V) :=
  fun _ _ _ _ => by simp [bcMarg₁_icSameOutput, bcMarg₂_icSameOutput]

end SameOutput

/-! ## The modulo-2 sum IC -/

/-- **Example (Lecture 6): modulo-2 sum IC.** `X₁, X₂, Y₁, Y₂` are binary and
`Y₁ = Y₂ = X₁ ⊕ X₂`. -/
def moduloTwoIC : Bool × Bool → Bool × Bool → ℝ := icSameOutput (detMAC fun x => xor x.1 x.2)

/-- **Example (Lecture 6): modulo-2 sum IC.** The capacity region coincides with the time-division
inner bound: it is `R₁ + R₂ ≤ 1` (with `R₁, R₂ ≤ 1`), in bits. -/
theorem icCapacityRegionBits_moduloTwoIC :
    icCapacityRegionBits moduloTwoIC = {R | R.1 ≤ 1 ∧ R.2 ≤ 1 ∧ R.1 + R.2 ≤ 1} := by
  have hl := log_pos one_lt_two
  set V : Bool × Bool → Bool → ℝ := detMAC fun x => xor x.1 x.2
  have hV : IsChannel V := detMAC_isChannel _
  have e₂ : (fun a => V (a, false)) = CoverThomas.noiselessChannel := by
    funext a y
    simp [V, detMAC, CoverThomas.noiselessChannel, eq_comm]
  have e₁ : (fun b => V (false, b)) = CoverThomas.noiselessChannel := by
    funext b y
    simp [V, detMAC, CoverThomas.noiselessChannel, eq_comm]
  have hC₁ : 1 ≤ macC₁ V / log 2 := by
    rw [le_div_iff₀ hl, one_mul]
    have h := le_ciSup (f := fun b => capacity fun a => V (a, b))
      (Set.finite_range _).bddAbove false
    simp only [e₂, CoverThomas.capacity_noiselessChannel.1] at h
    exact h
  have hC₂ : 1 ≤ macC₂ V / log 2 := by
    rw [le_div_iff₀ hl, one_mul]
    have h := le_ciSup (f := fun a => capacity fun b => V (a, b))
      (Set.finite_range _).bddAbove false
    simp only [e₁, CoverThomas.capacity_noiselessChannel.1] at h
    exact h
  rw [moduloTwoIC, icCapacityRegionBits_icSameOutput hV]
  refine le_antisymm ?_ ?_
  · intro R hR
    rw [macCapacityRegionBits_eq_smul hV] at hR
    obtain ⟨S, hS, rfl⟩ := hR
    obtain ⟨h1, h2, h3⟩ := le_log_card_of_mem_macCapacityRegion hV hS
    simp only [Fintype.card_bool, Nat.cast_ofNat] at h1 h2 h3
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← mul_add,
      inv_mul_le_iff₀ hl, mul_one]
    exact ⟨h1, h2, h3⟩
  · rintro R ⟨h1, h2, h3⟩
    refine macTimeDivisionBits_subset hV ?_
    rcases le_or_gt R.1 0 with h0 | h0
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using h0, by nlinarith⟩
    · exact ⟨R.1, ⟨h0.le, h1⟩, by nlinarith, by nlinarith⟩

/-! ## Strong but not very strong interference -/

/-- **Example (Lecture 6), page 6-12.** The DM-IC with binary inputs and ternary outputs
`Y₁ = Y₂ = X₁ + X₂`. -/
def sumIC : Bool × Bool → Fin 3 × Fin 3 → ℝ := icSameOutput binaryErasureMAC

/-- **Example (Lecture 6), page 6-12.** This DM-IC has strong interference. -/
theorem sumIC_isStrongIC : IsStrongIC sumIC := icSameOutput_isStrongIC _

/-- **Example (Lecture 6), page 6-12.** This DM-IC does not have very strong interference: with
`X₁, X₂ ∼ Bern(1/2)`, `I(X₁; Y₁ | X₂) = 1` bit while `I(X₁; Y₂) = 1/2` bit. -/
theorem sumIC_not_isVeryStrongIC : ¬ IsVeryStrongIC sumIC := by
  intro h
  have hl := log_pos one_lt_two
  have hp := uniformPMF_isPMF (α := Bool)
  have hV := binaryErasureMAC_isChannel
  have h₁ : macInfo₁ (uniformPMF Bool) (uniformPMF Bool) binaryErasureMAC = log 2 := by
    rw [macInfo₁_eq_sum hp hp hV]
    simp [mutualInfoOf_binaryErasureMAC₁, uniformPMF]
  have h₂ : macInfo₂ (uniformPMF Bool) (uniformPMF Bool) binaryErasureMAC = log 2 := by
    rw [macInfo₂_eq_sum hp hp hV]
    simp [mutualInfoOf_binaryErasureMAC₂, uniformPMF]
  have h₃ := macInfo₁₂_eq_mutualInfoOf_add hp hp hV
  rw [macInfo₁₂_binaryErasureMAC, h₂] at h₃
  have := (h _ _ hp hp).1
  rw [sumIC, bcMarg₁_icSameOutput, bcMarg₂_icSameOutput, h₁] at this
  linarith

/-! ## The AWGN interference channel -/

/-- **Theorem 2 (Lecture 6)**, the region only. With the signal-to-noise ratios `S₁, S₂` and the
interference-to-noise ratios `I₁, I₂`: `R₁ ≤ C(S₁)`, `R₂ ≤ C(S₂)`,
`R₁ + R₂ ≤ min {C(S₁ + I₁), C(S₂ + I₂)}`. The notes achieve it by simultaneous decoding. -/
def awgnICRegion (S₁ S₂ I₁ I₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | R.1 ≤ gaussCap S₁ ∧ R.2 ≤ gaussCap S₂ ∧
    R.1 + R.2 ≤ min (gaussCap (S₁ + I₁)) (gaussCap (S₂ + I₂))}

/-- **Lecture 6, page 6-21.** Under the conditions `S₂ ≤ I₁/(1 + S₁)` and `S₁ ≤ I₂/(1 + S₂)` of very
strong interference, the sum-rate bound is inactive, so that interference does not impair
communication: the region is the rectangle `R₁ ≤ C(S₁)`, `R₂ ≤ C(S₂)`. -/
theorem awgnICRegion_eq_of_veryStrong {S₁ S₂ I₁ I₂ : ℝ} (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂)
    (h₁₂ : S₂ ≤ I₁ / (1 + S₁)) (h₂₁ : S₁ ≤ I₂ / (1 + S₂)) :
    awgnICRegion S₁ S₂ I₁ I₂ = {R | R.1 ≤ gaussCap S₁ ∧ R.2 ≤ gaussCap S₂} := by
  have key : ∀ {a b c : ℝ}, 0 ≤ a → 0 ≤ b → b ≤ c / (1 + a) →
      gaussCap a + gaussCap b ≤ gaussCap (a + c) := fun {a b c} ha hb h => by
    have hpos : 0 < 1 + a := by linarith
    rw [le_div_iff₀ hpos] at h
    have hsum := gaussCap_add_gaussCap (N := 1) (P₁ := a) (P₂ := b * (1 + a)) ha
      (mul_nonneg hb hpos.le) one_pos
    have e : b * (1 + a) / (a + 1) = b := by rw [add_comm a 1, mul_div_cancel_right₀ _ hpos.ne']
    rw [div_one, div_one, e] at hsum
    rw [hsum]
    exact gaussCap_le_gaussCap (add_nonneg ha (mul_nonneg hb hpos.le)) (by linarith)
  have k₁ := key h₁ h₂ h₁₂
  have k₂ := key h₂ h₁ h₂₁
  ext R
  simp only [awgnICRegion, Set.mem_ofPred_eq, le_min_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

/-- **Lecture 6, page 6-51.** The symmetric degrees of freedom `d*(α)`, with `I = S^α`, as the
minimum of the four bounds `(a)`, `(b)`, `(c)` and `(d)` in the notes. Only the formula: its value
as a limit of the symmetric capacity is not formalized. -/
def symmetricDoF (α : ℝ) : ℝ :=
  min 1 (min (max (α / 2) (1 - α / 2)) (min (max α (1 - α))
    (max (2 / 3) (2 * α / 3) + max (1 / 3) (2 * α / 3) - 2 * α / 3)))

/-- **Lecture 6, page 6-52.** The bound `(d)` is redundant:
`d*(α) = min {1, max {α, 1 - α}, max {α/2, 1 - α/2}}`. -/
theorem symmetricDoF_eq {α : ℝ} (hα : 0 ≤ α) :
    symmetricDoF α = min 1 (min (max (α / 2) (1 - α / 2)) (max α (1 - α))) := by
  have hd : min 1 (min (max (α / 2) (1 - α / 2)) (max α (1 - α))) ≤
      max (2 / 3) (2 * α / 3) + max (1 / 3) (2 * α / 3) - 2 * α / 3 := by
    rcases le_total α (1 / 2) with h₁ | h₁
    · have e₁ : max (2 / 3 : ℝ) (2 * α / 3) = 2 / 3 := max_eq_left (by linarith)
      have e₂ : max (1 / 3 : ℝ) (2 * α / 3) = 1 / 3 := max_eq_left (by linarith)
      have e₃ : max α (1 - α) = 1 - α := max_eq_right (by linarith)
      rw [e₁, e₂]
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      rw [e₃]
      linarith
    have e₂ : max (1 / 3 : ℝ) (2 * α / 3) = 2 * α / 3 := max_eq_right (by linarith)
    rw [e₂]
    rcases le_total α (2 / 3) with h₃ | h₃
    · have e₁ : max (2 / 3 : ℝ) (2 * α / 3) = 2 / 3 := max_eq_left (by linarith)
      have e₃ : max α (1 - α) = α := max_eq_left (by linarith)
      rw [e₁]
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      rw [e₃]
      linarith
    · refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
      refine max_le ?_ ?_
      · linarith [le_max_right (2 / 3 : ℝ) (2 * α / 3)]
      · linarith [le_max_left (2 / 3 : ℝ) (2 * α / 3)]
  rw [symmetricDoF, ← min_assoc (max (α / 2) (1 - α / 2)), ← min_assoc 1, min_eq_left hd]

/-- **Lecture 6, page 6-51.** The first minimum of the "W" curve: `d*(1/2) = 1/2`. -/
theorem symmetricDoF_half : symmetricDoF (1 / 2) = 1 / 2 := by
  rw [symmetricDoF_eq (by norm_num)]
  norm_num

/-- **Lecture 6, page 6-51.** The maximum of the "W" curve: `d*(2/3) = 2/3`. -/
theorem symmetricDoF_two_thirds : symmetricDoF (2 / 3) = 2 / 3 := by
  rw [symmetricDoF_eq (by norm_num)]
  norm_num

/-- **Lecture 6, page 6-51.** The second minimum of the "W" curve: `d*(1) = 1/2`. -/
theorem symmetricDoF_one : symmetricDoF 1 = 1 / 2 := by
  rw [symmetricDoF_eq (by norm_num)]
  norm_num

/-- **Lecture 6, page 6-52.** For very strong interference, interference does not impair capacity:
`d*(α) = 1` for `α ≥ 2`. -/
theorem symmetricDoF_of_two_le {α : ℝ} (hα : 2 ≤ α) : symmetricDoF α = 1 := by
  rw [symmetricDoF_eq (by linarith)]
  exact min_eq_left (le_min (le_max_of_le_left (by linarith)) (le_max_of_le_left (by linarith)))

/-! ## Index of numbered and named results -/

/-- **Theorem 1 (Lecture 6).** The capacity region of the DM-IC with strong interference. -/
alias theorem_6_1 := icCapacityRegionBits_eq_closure_icStrongRegionBits

/-- **Lemma 1 (Lecture 6).** `I(X₁ⁿ; Y₁ⁿ | X₂ⁿ) ≤ I(X₁ⁿ; Y₂ⁿ | X₂ⁿ)` with strong interference. -/
alias lemma_6_1 := IsStrongIC.macInfo₁_macExt_le

/-- **Sato's outer bound (Lecture 6).** -/
alias sato_outer_bound := IsAchievableICBits.mem_closure_icSatoRegionBits

/-- **The simultaneous decoding inner bound (Lecture 6).** -/
alias simultaneous_decoding_inner_bound := icSimultaneousRegionBits_subset

end InfoTheory.ElGamalKim
