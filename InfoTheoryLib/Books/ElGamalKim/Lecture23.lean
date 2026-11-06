/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyMultiNodeCapacity

/-!
# El Gamal & Kim, Lecture 23: Information Theoretic Secrecy

This file indexes the formalization of Lecture 23 of [elgamal2010]. We prove Shannon's Theorem 1,
the secrecy capacity with a shared key of Theorem 2, the secrecy capacity of the wiretap channel of
Theorem 3 with the bound `|𝒰| ≤ |𝒳|`, the one-way secret key capacity of Theorem 6, the upper bound
of Theorem 8 and the cases in which it is tight, and the multi-node secret key capacity of Theorem
9. We also prove that Theorem 7 as printed is false, and that the definition of the secret key
capacity needs a bound on the alphabet of the key.

## Conventions

* **Rates.** Rates are in bits, with `2 ^ ⌈n R⌉` messages and keys, and informations are in nats.
* **Decoders.** The notes allow a decoder to declare an error, which does not help, so our decoders
  always return a message or a key.
* **Randomization.** Encoders of the wiretap channel are channels `p(xⁿ | m)`. In the secret key
  problems, randomization is a private random variable of each node, as on page 23-49.
* **Order of the speakers.** The notes take a round robin. Any other order is the same, with trivial
  indices, so the order of the speakers is arbitrary.
* **Keys.** The keys take values in `[1 : 2 ^ ⌈n R⌉]`: see `unbounded_key_counterexample`.
* **Suprema.** Theorems 6 and 8 state a maximum and a minimum with no bound on the alphabets of the
  auxiliary random variables. We take a supremum and an infimum over finite alphabets.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Shannon's secrecy system (pages 23-2 to 23-4; `Secrecy.Shannon`)
* **Theorem 1:** `entropy_le_of_perfectSecrecy` (necessity), `oneTimePad_perfectSecrecy`,
  `oneTimePad_entropy` (sufficiency, for the key that the proof chooses), here `theorem_23_1`.
* A key with enough entropy need not suffice: `prob_key_le_of_perfectSecrecy`,
  `not_perfectSecrecy_of_entropy_ge`.

### Secure communication over a DMC (pages 23-5 to 23-7; `Secrecy.KeyedChannel`)
* `KeyedSecrecyCode`, `IsAchievableKeyed`, `keyedSecrecyCapacity`.
* The converse: `KeyedSecrecyCode.one_sub_errProb_mul_log_le_key`,
  `KeyedSecrecyCode.one_sub_errProb_mul_log_le_capacity`, `IsAchievableKeyed.le`.
* The one-time pad on a channel code: `padCode`, `padCode_leakage`, `padCode_errProb`,
  `isAchievableKeyed_of_lt`.
* **Theorem 2:** `keyedSecrecyCapacity_eq`, here `theorem_23_2`.

### The wiretap channel (pages 23-8 to 23-20)
* `WiretapCode`, `IsAchievableWiretap`, `wiretapCapacity`, `wiretapGap`, `wiretapValue`
  (`Secrecy.Wiretap`).
* The bound `|𝒰| ≤ |𝒳|`: `exists_support_le_of_linear`, `exists_wiretapGap_reduce`,
  `exists_wiretapValue_eq`, `wiretapGap_le_value`.
* The converse: `mutualInfo_sub_mutualInfo_eq_sum` (the Csiszár sum identity),
  `condMutualInfo_eq_sum_condLawOf`, `condGap_le_wiretapValue` (fixing `V = v`), `dist_coord_eq`,
  `WiretapCode.one_sub_errProb_mul_log_le`, `IsAchievableWiretap.le`.
* The achievability (`Secrecy.WiretapAchievability`): `wiretapCodeOf`,
  `sum_codebook_codebookInfo_le` (`I(L; Zⁿ | 𝒞) ≤ n I(U; Z)`), `mutualInfo_wtBinLaw_le`,
  `exists_wiretap_code_le`, `isAchievableWiretap_of_lt`.
* **Theorem 3:** `wiretapCapacity_eq`, here `theorem_23_3`.
* Special cases (`Secrecy.WiretapExamples`): `wiretapXValue`, `wiretapGap_eq_sub_sum`,
  `wiretapCapacity_of_isMoreCapable`, `wiretapCapacity_of_isStochasticallyDegraded`,
  `wiretapGap_congr` (only the marginals matter), `wiretapCapacity_eq_zero_of_isLessNoisy`.
* The BS-WTC: `wiretapCapacity_bsbcIndep`, `wiretapCapacity_bsbcIndep_eq_zero`.
* The Gaussian WTC, on real numbers: `gaussianWiretapFun_antitone`, `gaussianWiretap_bound`,
  `mimo_formula_eq_two_mul`.

### Secret key agreement: the source model (pages 23-27 to 23-51)
* `KeyCode`, `keyLaw`, `IsAchievableKey`, `keyCapacityOf`, `keyCapacity` (`Secrecy.KeyAgreement`).
* **Theorem 8:** `KeyCode.condMutualInfo_trans_le`, `KeyCode.entropy_key_le`,
  `KeyCode.entropyKey₁_le`, `IsAchievableKey.le`, `intrinsicInfo`, `keyCapacity_le`,
  `keyCapacity_le_of_channel`, here `theorem_23_8`.
* The example of pages 23-48 and 23-49 (here): `mwSource`, `mwChannel`, `mwSource_condInfo`,
  `mwSource_intrinsic`, `keyCapacity_mwSource`.
* Double binning (`Secrecy.DoubleBinning`): `entropy_key_ge_of_decodable`,
  `mutualInfo_key_le_of_decodable`, `key_transfer`, `exists_doubleBin`, `eventually_doubleBin`.
* **Theorem 6:** `oneWayGap` (`Secrecy.KeyOneWay`), `isAchievableKey_of_lt_oneWayGap`,
  `oneWayValue`, `condMutualInfo_sub_eq_sum`, `exists_channel_coord`, `letterGap_le_value`,
  `KeyCode.entropyKey₁_le_oneWay`, `IsAchievableKey.le_oneWayValue`, `keyCapacity₁₂_eq`
  (`Secrecy.KeyOneWayConverse`), `srcSwap`, `IsAchievableKey.swap`, `keyCapacity₂₁_eq`,
  `keyCapacityOneWay_eq` (`Secrecy.KeySpecialCases`), here `theorem_23_6`.
* Tight cases (`Secrecy.KeySpecialCases`): `keyCapacity_of_markov₁`, `keyCapacity_of_markov₂`,
  `keyCapacity_of_nodes_know`, `keyCapacity_of_indep`.
* Maurer's example for a uniform input (here): `maurerSource`, `keyCapacity_maurer`.
* **Errors in the notes (here):** `printed_theorem7_false`, `unbounded_key_counterexample`.

### Many nodes, with `Z` known to all (pages 23-52 to 23-59)
* `zCondH`, `zRegion`, `rCFOZ`, `MultiKeyCode`, `IsAchievableMultiKey`, `multiKeyCapacity`,
  `swCondH_zTuple`, `condEntropy_runTo`, `condEntropy_viewB_eq_sum`, `condEntropy_viewB_compl`
  (`Secrecy.KeyMultiNode`).
* The converse (`Secrecy.KeyMultiNodeConverse`): `MultiKeyCode.mul_zCondH_le`,
  `MultiKeyCode.mul_entropy_eq`, `MultiKeyCode.entropy_key_le`, `IsAchievableMultiKey.le`.
* The achievability: `card_rivals_le`, `exists_multiBin` (`Secrecy.KeyMultiNodeBinning`),
  `eventually_multiBin`, `multiCode`, `isAchievableMultiKey_of_lt` (`Secrecy.KeyMultiNodeCapacity`).
* **Theorem 9:** `multiKeyCapacity_eq`, `zRegion_eq_mwRegion`, `rCFOZ_eq_rCFO`, here `theorem_23_9`.

## Differences from the notes

* **Theorem 3.** The notes bound `H(L | Zⁿ, M)` with Chebyshev's inequality (Lemma 1), with a bin
  rate above `I(U; Z)`. We take the bin rate just below `I(U; Z)`, so that the eavesdropper can
  decode `L` given `M`, and use Fano's inequality.
* **The bound `|𝒰| ≤ |𝒳|`.** The notes use the Fenchel–Eggleston strengthening of the support lemma.
  We use that the objective is linear in `p(u)` for a fixed `p(x)`, and take a basic solution.
* **Theorems 6 and 9.** The notes use Chebyshev's inequality (Lemmas 2 and 3). If the sequence can
  be decoded from the public index, the key and the observation of the eavesdropper, entropy
  inequalities give the same results, so we only need a packing argument.
* **The source model and the wiretap channel (pages 23-65 and 23-66).** We do not need the virtual
  wiretap channel for Theorem 6, for the same reason.
* **Theorem 9.** The notes give the converse without randomization. With private random variables
  their entropies have to be subtracted from the rates `R'ⱼ`. The theorem needs `N ≥ 2`: for
  `N = 1`, a node with private randomness can draw any key.

## Not formalized

* **Theorem 7 and the example of pages 23-43 and 23-44.** The corrected lower bound for interactive
  communication, for which the notes only give an outline, and the example that shows that it can
  exceed the one-way capacity.
* **Statements without proofs in the notes.** The secrecy capacity with a key of page 23-21, the
  bounds for two legitimate receivers and Theorem 4, Theorem 5, the rate-limited one-way capacity of
  page 23-38, the secret key capacity with helpers of page 23-59, and the bounds of page 23-60.
* **The channel model.** The notes define it only informally and do not prove the upper bound of
  page 23-64. We prove the source form of Maurer's example. The wiretap channel of Theorem 3 needs
  no feedback.
* **Continuous alphabets.** For the Gaussian WTC we prove the steps on real numbers, not an
  operational theorem.

## Issues in the notes

* **Page 23-3.** `H(K) ≥ H(M)` is not sufficient for a given key, only for a key that can be chosen:
  `not_perfectSecrecy_of_entropy_ge`.
* **Page 23-11.** The formula of the BS-WTC needs `p₁, p₂ ≤ 1/2`: for `p₁ = 2/5` and `p₂ = 9/10` the
  formula would be negative.
* **Page 23-13.** The function `½ log(2πe(N₂ - N₁) + 2^ν) - ν` is decreasing, not increasing, and
  `2^ν` should be `2^{2ν}`: `gaussianWiretapFun_antitone`. The MIMO formula has no factor `1/2`:
  `mimo_formula_eq_two_mul`.
* **Page 23-15.** The bin `C(m)` should be `B(m)`.
* **Page 23-20.** `(d)` misses a factor `n`, and the step `(e)` is not labelled.
* **Page 23-22.** `I(U; Y₁) - I(U; Y₃)` should be `I(U; Y₁) - I(U; Z)`.
* **Page 23-29.** `2^{R_l}` should be `2^{n R_l}`, and the key alphabet needs a bound:
  `unbounded_key_counterexample`.
* **Page 23-39.** The conditional pmf of Theorem 7 is wrong: `printed_theorem7_false`.
* **Page 23-43.** `U₂ = X₂₁` should be `U₂ = X₂₂`.
* **Page 23-63.** `1 - h(p₁)` uses `h` for the binary entropy `H`.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

namespace ElGamalKim

/-! ### Maurer's example -/

section Maurer

variable {p₁ p₂ : ℝ}

/-- **Pages 23-61 to 23-64 of [elgamal2010].** The sources of Maurer's example: `X` is uniform,
`Y = X ⊕ Z₁` and `Z = X ⊕ Z₂`. -/
def maurerSource (p₁ p₂ : ℝ) : srcLetter Bool Bool Bool → ℝ :=
  jointOf (uniformPMF Bool) (bsbcIndep p₁ p₂)

lemma maurerSource_isPMF (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    IsPMF (maurerSource p₁ p₂) :=
  jointOf_isPMF uniformPMF_isPMF (bsbcIndep_isChannel hp₁ hp₁' hp₂ hp₂')

/-- The conditional entropy of `Y` from a function of `(Y's input)`. -/
lemma maurer_condEntropy_x (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    H[(fun a : srcLetter Bool Bool Bool => a.2.1) | Prod.fst ; maurerSource p₁ p₂] =
      binEntropy p₁ := by
  have hP := maurerSource_isPMF hp₁ hp₁' hp₂ hp₂'
  have h := condEntropy_of_channel (μ := maurerSource p₁ p₂)
    (Z := (Prod.fst : srcLetter Bool Bool Bool → Bool)) (Y := fun a => a.2.1)
    (W := bsbcBSC p₁) id fun z y => by
      cases z <;> cases y <;>
        simp [dist, pair, Fintype.sum_prod_type, maurerSource, jointOf, bsbcIndep, bsbcBSC,
          uniformPMF] <;> ring
  rw [h]
  simp only [entropy_bsbcBSC hp₁ hp₁', ← sum_mul, (hP.dist _).sum_eq_one, one_mul]

/-- The conditional entropy of `Y` given `(Z, X)`. -/
lemma maurer_condEntropy_zx (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    H[(fun a : srcLetter Bool Bool Bool => a.2.1) | pair (fun a => a.2.2) Prod.fst ;
      maurerSource p₁ p₂] = binEntropy p₁ := by
  have hP := maurerSource_isPMF hp₁ hp₁' hp₂ hp₂'
  have h := condEntropy_of_channel (μ := maurerSource p₁ p₂)
    (Z := pair (fun a : srcLetter Bool Bool Bool => a.2.2) Prod.fst) (Y := fun a => a.2.1)
    (W := bsbcBSC p₁) Prod.snd fun z y => by
      obtain ⟨z₁, z₂⟩ := z
      cases z₁ <;> cases z₂ <;> cases y <;>
        simp [dist, pair, Fintype.sum_prod_type, maurerSource, jointOf, bsbcIndep, bsbcBSC,
          uniformPMF] <;> ring
  rw [h]
  simp only [entropy_bsbcBSC hp₁ hp₁', ← sum_mul, (hP.dist _).sum_eq_one, one_mul]

/-- The conditional entropy of `Y` given `Z`: `Y` comes from `Z` through a `BSC(p₁ ∗ p₂)`. -/
lemma maurer_condEntropy_z (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    H[(fun a : srcLetter Bool Bool Bool => a.2.1) | (fun a => a.2.2) ; maurerSource p₁ p₂] =
      binEntropy (binConv p₁ p₂) := by
  have hP := maurerSource_isPMF hp₁ hp₁' hp₂ hp₂'
  have hc := bsbc_binConv_mem_Icc (a := p₁) (p := p₂) ⟨hp₁, hp₁'⟩ ⟨hp₂, hp₂'⟩
  have h := condEntropy_of_channel (μ := maurerSource p₁ p₂)
    (Z := fun a : srcLetter Bool Bool Bool => a.2.2) (Y := fun a => a.2.1)
    (W := bsbcBSC (binConv p₁ p₂)) id fun z y => by
      cases z <;> cases y <;>
        simp [dist, pair, Fintype.sum_prod_type, maurerSource, jointOf, bsbcIndep, bsbcBSC,
          uniformPMF, binConv] <;> ring
  rw [h]
  simp only [entropy_bsbcBSC hc.1 hc.2, ← sum_mul, (hP.dist _).sum_eq_one, one_mul]

/-- **Pages 23-61 to 23-64 of [elgamal2010]: Maurer's example, for the sources from a uniform
input.** The secret key capacity is `H(p₁ ∗ p₂) - H(p₁)`, in bits, even when `p₁ > p₂`, where the
wiretap channel has secrecy capacity `0`. It is achieved with one message from the node that
observes `Y`. -/
theorem keyCapacity_maurer (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    keyCapacity (maurerSource p₁ p₂) = (binEntropy (binConv p₁ p₂) - binEntropy p₁) / log 2 := by
  have hP := maurerSource_isPMF hp₁ hp₁' hp₂ hp₂'
  have hm : I[(fun a : srcLetter Bool Bool Bool => a.2.1) : (fun a => a.2.2) | Prod.fst ;
      maurerSource p₁ p₂] = 0 := by
    rw [condMutualInfo_eq' hP, maurer_condEntropy_x hp₁ hp₁' hp₂ hp₂']
    have e : H[(fun a : srcLetter Bool Bool Bool => a.2.1) | pair Prod.fst (fun a => a.2.2) ;
        maurerSource p₁ p₂] = H[(fun a : srcLetter Bool Bool Bool => a.2.1) |
        pair (fun a => a.2.2) Prod.fst ; maurerSource p₁ p₂] :=
      condEntropy_congr_right hP _ Prod.swap Prod.swap_injective fun _ => rfl
    rw [e, maurer_condEntropy_zx hp₁ hp₁' hp₂ hp₂', sub_self]
  rw [(keyCapacity_of_markov₂ hP hm).2, condMutualInfo_comm hP, condMutualInfo,
    maurer_condEntropy_z hp₁ hp₁' hp₂ hp₂']
  have e : H[(fun a : srcLetter Bool Bool Bool => a.2.1) | pair Prod.fst (fun a => a.2.2) ;
      maurerSource p₁ p₂] = H[(fun a : srcLetter Bool Bool Bool => a.2.1) |
      pair (fun a => a.2.2) Prod.fst ; maurerSource p₁ p₂] :=
    condEntropy_congr_right hP _ Prod.swap Prod.swap_injective fun _ => rfl
  rw [e, maurer_condEntropy_zx hp₁ hp₁' hp₂ hp₂']

end Maurer

/-! ### Theorem 7 is misprinted -/

section Theorem7

/-- Two independent uniform bits, and a constant for the eavesdropper. -/
def indepBits : srcLetter Bool Bool Unit → ℝ := fun _ => 1 / 4

lemma indepBits_isPMF : IsPMF indepBits :=
  ⟨fun _ => by norm_num [indepBits], by simp [indepBits]⟩

/-- **Theorem 7 of Lecture 23 of [elgamal2010], page 23-39, as printed, is false.** The notes
require `p(uₗ | u^{l-1}, x_{jₗ})`, with `j₁ = 2`. For `q = 1` and `U₁ = X₂`, the printed lower bound
is `I(U₁; X₂) - I(U₁; Z) = H(X₂) = 1` bit, for independent `X₁` and `X₂` and a constant `Z`. But
these sources have secret key capacity `0`, by Theorem 8. The outline of the proof shows that `Uₗ`
should be generated at the other node, from `X_{j'ₗ}` with `j'ₗ ≠ jₗ`. -/
theorem printed_theorem7_false :
    keyCapacity indepBits = 0 ∧
      I[(fun a : srcLetter Bool Bool Unit => a.2.1) : (fun a => a.2.1) ; indepBits] -
        I[(fun a : srcLetter Bool Bool Unit => a.2.1) : (fun a => a.2.2) ; indepBits] = log 2 := by
  have hP := indepBits_isPMF
  have hd : dist indepBits (fun a : srcLetter Bool Bool Unit => a.2.1) = uniformPMF Bool := by
    funext y
    cases y <;> simp [dist, indepBits, Fintype.sum_prod_type, uniformPMF] <;> norm_num
  have hH : H[(fun a : srcLetter Bool Bool Unit => a.2.1) ; indepBits] = log 2 := by
    rw [entropyRV, hd, entropy_uniformPMF]
    simp
  constructor
  · have hi : I[(fun a : srcLetter Bool Bool Unit => a.2.2) : (fun a => (a.1, a.2.1)) ; indepBits] =
        0 := by
      rw [mutualInfo_eq_entropy_sub_condEntropy hP]
      rw [condEntropy_unit_eq_zero hP, ]
      have h₀ := entropyRV_le_log_card hP (fun a : srcLetter Bool Bool Unit => a.2.2)
      have h₁ := entropyRV_nonneg hP (fun a : srcLetter Bool Bool Unit => a.2.2)
      simp only [Fintype.card_unique, Nat.cast_one, log_one] at h₀
      linarith
    rw [keyCapacity_of_indep hP hi]
    have hz : I[(Prod.fst : srcLetter Bool Bool Unit → Bool) : (fun a => a.2.1) ; indepBits] = 0 :=
      by
      rw [mutualInfo_eq_zero_iff hP]
      intro x y
      cases x <;> cases y <;>
        simp [dist, pair, indepBits, Fintype.sum_prod_type] <;> norm_num
    rw [hz, zero_div]
  · rw [mutualInfo_self hP, hH]
    have h₂ : I[(fun a : srcLetter Bool Bool Unit => a.2.1) : (fun a => a.2.2) ; indepBits] = 0 :=
      by
      rw [mutualInfo_eq_entropy_sub_condEntropy' hP, condEntropy_unit_eq_zero hP]
      have h₀ := entropyRV_le_log_card hP (fun a : srcLetter Bool Bool Unit => a.2.2)
      have h₁ := entropyRV_nonneg hP (fun a : srcLetter Bool Bool Unit => a.2.2)
      simp only [Fintype.card_unique, Nat.cast_one, log_one] at h₀
      linarith
    rw [h₂, sub_zero]

end Theorem7

/-! ### The example of Theorem 8 -/

section Theorem8

/-- The weights of the atoms of the example of page 23-48. -/
def mwWeight : Fin 6 → ℝ := ![1 / 8, 1 / 8, 1 / 8, 1 / 8, 1 / 4, 1 / 4]

/-- The atoms `(x₁, x₂, z)` of the example of page 23-48. -/
def mwAtom : Fin 6 → srcLetter (Fin 4) (Fin 4) (Fin 4) :=
  ![(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0), (2, 2, 2), (3, 3, 3)]

/-- **Page 23-48 of [elgamal2010].** The source of the example of Maurer and Wolf. -/
def mwSource : srcLetter (Fin 4) (Fin 4) (Fin 4) → ℝ := dist mwWeight mwAtom

/-- **Page 23-49 of [elgamal2010].** The channel `p(z̄ | z)` of the example. -/
def mwChannel : Fin 4 → Fin 4 → ℝ :=
  ![![1 / 2, 1 / 2, 0, 0], ![1 / 2, 1 / 2, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

lemma mwWeight_isPMF : IsPMF mwWeight := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [mwWeight]
  · simp [mwWeight, Fin.sum_univ_succ]
    norm_num

lemma mwChannel_isChannel : IsChannel mwChannel := fun z => by
  refine ⟨fun z' => ?_, ?_⟩
  · fin_cases z <;> fin_cases z' <;> norm_num [mwChannel]
  · fin_cases z <;> simp [mwChannel, Fin.sum_univ_succ] <;> norm_num

lemma mwSource_isPMF : IsPMF mwSource := mwWeight_isPMF.dist _

lemma negMulLog_one_div_two_pow (k : ℕ) :
    negMulLog (1 / (2 : ℝ) ^ k) = k * log 2 / 2 ^ k := by
  rw [negMulLog, one_div, log_inv, log_pow]
  field_simp

lemma negMulLog_eighth : negMulLog (1 / 8 : ℝ) = 3 / 8 * log 2 := by
  have h := negMulLog_one_div_two_pow 3
  norm_num at h ⊢
  rw [h]
  ring

lemma negMulLog_fourth : negMulLog (1 / 4 : ℝ) = 1 / 2 * log 2 := by
  have h := negMulLog_one_div_two_pow 2
  norm_num at h ⊢
  rw [h]
  ring

lemma negMulLog_sixteenth : negMulLog (1 / 16 : ℝ) = 1 / 4 * log 2 := by
  have h := negMulLog_one_div_two_pow 4
  norm_num at h ⊢
  rw [h]
  ring

lemma negMulLog_eighth' : negMulLog (8⁻¹ : ℝ) = 3 / 8 * log 2 := by
  rw [← one_div]
  exact negMulLog_eighth

lemma negMulLog_fourth' : negMulLog (4⁻¹ : ℝ) = 1 / 2 * log 2 := by
  rw [← one_div]
  exact negMulLog_fourth

lemma negMulLog_sixteenth' : negMulLog (16⁻¹ : ℝ) = 1 / 4 * log 2 := by
  rw [← one_div]
  exact negMulLog_sixteenth

/-- The entropy of the atoms. -/
lemma entropy_mwWeight : H[id ; mwWeight] = 5 / 2 * log 2 := by
  rw [entropyRV, dist_id, entropy_eq_sum_negMulLog, Fin.sum_univ_six]
  have e : ∀ i, mwWeight i = ![1 / 8, 1 / 8, 1 / 8, 1 / 8, 1 / 4, 1 / 4] i := fun _ => rfl
  simp only [e, Matrix.cons_val]
  rw [negMulLog_eighth, negMulLog_fourth]
  ring

/-- `H(Z) = 2` bits, in the example. -/
lemma entropy_mwAtom_z : H[(fun i => (mwAtom i).2.2) ; mwWeight] = 2 * log 2 := by
  have hd : dist mwWeight (fun i => (mwAtom i).2.2) = uniformPMF (Fin 4) := by
    funext k
    fin_cases k <;> simp [dist, Fin.sum_univ_six, mwWeight, mwAtom, uniformPMF] <;> norm_num
  rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_fin]
  rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num

/-- **Page 23-49 of [elgamal2010].** In the example, `I(X₁; X₂ | Z) = 1/2` bit. -/
theorem mwSource_condInfo :
    I[(Prod.fst : srcLetter (Fin 4) (Fin 4) (Fin 4) → Fin 4) : (fun a => a.2.1) | (fun a => a.2.2) ;
      mwSource] = 1 / 2 * log 2 := by
  have hP := mwSource_isPMF
  rw [condMutualInfo_eq hP, mwSource, ← entropyRV_comp_of_dist, ← entropyRV_comp_of_dist,
    ← entropyRV_comp_of_dist, ← entropyRV_comp_of_dist]
  have hi : ∀ {b : Type} [Fintype b] (g : Fin 6 → b), Function.Injective g →
      H[g ; mwWeight] = 5 / 2 * log 2 := fun g hg => by
      rw [← entropy_mwWeight]
      exact entropyRV_eq_of_injective _ g hg fun _ => rfl
  have h₁ := hi (pair (fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) => a.2.2) Prod.fst ∘ mwAtom) (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [mwAtom, pair])
  have h₂ := hi (pair (fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) => a.2.2) (fun a => a.2.1) ∘
    mwAtom)
    (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [mwAtom, pair])
  have h₃ := hi (pair (fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) => a.2.2)
    (pair Prod.fst (fun a => a.2.1)) ∘ mwAtom) (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [mwAtom, pair])
  have h₄ : H[(fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) => a.2.2) ∘ mwAtom ; mwWeight] =
      2 * log 2 := entropy_mwAtom_z
  rw [h₁, h₂, h₃, h₄]
  ring

/-- The law of the atoms with the letter of `Z̄`. -/
def mwExtWeight : Fin 6 × Fin 4 → ℝ := jointOf mwWeight fun i => mwChannel (mwAtom i).2.2

/-- The letter of the extended source of an atom with the letter of `Z̄`. -/
def mwExtAtom (w : Fin 6 × Fin 4) : srcLetter (Fin 4) (Fin 4) (Fin 4) × Fin 4 := (mwAtom w.1, w.2)

lemma dist_mwExtAtom : dist mwExtWeight mwExtAtom = extSource mwSource mwChannel := by
  classical
  funext ⟨l, z'⟩
  simp only [dist, Fintype.sum_prod_type, mwExtWeight, mwExtAtom, jointOf, Prod.mk.injEq, extSource,
    mwSource, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single z' (fun b _ hb => by simp [hb]) (by simp)]
  by_cases h : mwAtom i = l
  · subst h
    simp
  · simp [h]

/-- `H(Z̄, X₁) = 5/2` bits. -/
lemma entropy_mwExt_x₁ : H[(fun w : Fin 6 × Fin 4 => (w.2, (mwAtom w.1).1)) ; mwExtWeight] =
    5 / 2 * log 2 := by
  classical
  set t : Fin 4 × Fin 4 → ℝ := fun v =>
    if v.1.val < 2 ∧ v.2.val < 2 then 1 / 8 else if v.1 = v.2 then 1 / 4 else 0 with ht
  have hd : dist mwExtWeight (fun w : Fin 6 × Fin 4 => (w.2, (mwAtom w.1).1)) = t := by
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [dist, Fintype.sum_prod_type, Fin.sum_univ_six, Fin.sum_univ_four, mwExtWeight, jointOf,
        mwWeight, mwAtom, mwChannel, ht] <;> norm_num
  rw [entropyRV, hd, entropy_eq_sum_negMulLog, Fintype.sum_prod_type]
  simp [Fin.sum_univ_four, ht, negMulLog_eighth', negMulLog_fourth']
  ring

/-- `H(Z̄, X₂) = 5/2` bits. -/
lemma entropy_mwExt_x₂ : H[(fun w : Fin 6 × Fin 4 => (w.2, (mwAtom w.1).2.1)) ; mwExtWeight] =
    5 / 2 * log 2 := by
  classical
  set t : Fin 4 × Fin 4 → ℝ := fun v =>
    if v.1.val < 2 ∧ v.2.val < 2 then 1 / 8 else if v.1 = v.2 then 1 / 4 else 0 with ht
  have hd : dist mwExtWeight (fun w : Fin 6 × Fin 4 => (w.2, (mwAtom w.1).2.1)) = t := by
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [dist, Fintype.sum_prod_type, Fin.sum_univ_six, Fin.sum_univ_four, mwExtWeight, jointOf,
        mwWeight, mwAtom, mwChannel, ht] <;> norm_num
  rw [entropyRV, hd, entropy_eq_sum_negMulLog, Fintype.sum_prod_type]
  simp [Fin.sum_univ_four, ht, negMulLog_eighth', negMulLog_fourth']
  ring

/-- `H(Z̄) = 2` bits. -/
lemma entropy_mwExt_z : H[(fun w : Fin 6 × Fin 4 => w.2) ; mwExtWeight] = 2 * log 2 := by
  have hd : dist mwExtWeight (fun w : Fin 6 × Fin 4 => w.2) = uniformPMF (Fin 4) := by
    funext k
    fin_cases k <;>
      simp [dist, Fintype.sum_prod_type, Fin.sum_univ_six, mwExtWeight, jointOf,
        mwWeight, mwAtom, mwChannel, uniformPMF] <;> norm_num
  rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_fin]
  rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num

/-- `H(Z̄, X₁, X₂) = 3` bits. -/
lemma entropy_mwExt_all : H[(fun w : Fin 6 × Fin 4 => (w.2, (mwAtom w.1).1, (mwAtom w.1).2.1)) ;
    mwExtWeight] = 3 * log 2 := by
  have hinj : Function.Injective fun w : Fin 6 × Fin 4 =>
      (w.2, (mwAtom w.1).1, (mwAtom w.1).2.1) := by
    rintro ⟨a, a'⟩ ⟨b, b'⟩ h
    simp only [Prod.mk.injEq] at h
    refine Prod.ext ?_ h.1
    have h₂ := h.2
    clear h
    fin_cases a <;> fin_cases b <;> simp_all [mwAtom]
  have h₁ : H[(fun w : Fin 6 × Fin 4 => (w.2, (mwAtom w.1).1, (mwAtom w.1).2.1)) ; mwExtWeight] =
      H[id ; mwExtWeight] := entropyRV_eq_of_injective _ _ hinj fun _ => rfl
  rw [h₁, entropyRV, dist_id, entropy_eq_sum_negMulLog, Fintype.sum_prod_type]
  have e : ((8 : ℝ)⁻¹ * 2⁻¹) = 16⁻¹ := by norm_num
  simp [Fin.sum_univ_six, Fin.sum_univ_four, mwExtWeight, jointOf, mwWeight, mwAtom, mwChannel,
    negMulLog_fourth', e, negMulLog_sixteenth']
  ring

/-- **Page 23-49 of [elgamal2010].** In the example, `I(X₁; X₂ | Z̄) = 0`, for the channel of the
example. So the bound of Theorem 8 with `Z̄` is strictly tighter than the bound with `Z`. -/
theorem mwSource_intrinsic : intrinsicInfoOf mwSource mwChannel = 0 := by
  have hQ' : IsChannel fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) => mwChannel a.2.2 :=
    fun a => mwChannel_isChannel _
  have hP : IsPMF (extSource mwSource mwChannel) := jointOf_isPMF mwSource_isPMF hQ'
  rw [intrinsicInfoOf, condMutualInfo_eq hP, ← dist_mwExtAtom, ← entropyRV_comp_of_dist,
    ← entropyRV_comp_of_dist, ← entropyRV_comp_of_dist, ← entropyRV_comp_of_dist]
  have h₁ : H[pair Prod.snd (fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) × Fin 4 => a.1.1) ∘
    mwExtAtom ;
      mwExtWeight] = 5 / 2 * log 2 := entropy_mwExt_x₁
  have h₂ : H[pair Prod.snd (fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) × Fin 4 => a.1.2.1) ∘
      mwExtAtom ; mwExtWeight] = 5 / 2 * log 2 := entropy_mwExt_x₂
  have h₃ : H[(Prod.snd : srcLetter (Fin 4) (Fin 4) (Fin 4) × Fin 4 → Fin 4) ∘ mwExtAtom ;
      mwExtWeight] = 2 * log 2 := entropy_mwExt_z
  have h₄ : H[pair Prod.snd (pair (fun a : srcLetter (Fin 4) (Fin 4) (Fin 4) × Fin 4 => a.1.1)
      (fun a => a.1.2.1)) ∘ mwExtAtom ; mwExtWeight] = 3 * log 2 := entropy_mwExt_all
  rw [h₁, h₂, h₃, h₄]
  ring

/-- **Pages 23-48 and 23-49 of [elgamal2010].** In the example, the secret key capacity is `0`,
while `I(X₁; X₂ | Z) = 1/2` bit. -/
theorem keyCapacity_mwSource : keyCapacity mwSource = 0 := by
  have hl := log_pos one_lt_two
  have h := keyCapacity_le_of_channel (fun _ _ => True) mwSource_isPMF mwChannel_isChannel
  rw [mwSource_intrinsic, zero_div] at h
  exact le_antisymm h (Real.sSup_nonneg fun R hR => hR.1)

end Theorem8

/-! ### Keys with an unbounded alphabet -/

section Unbounded

variable {α₁ α₂ γ : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] {P : srcLetter α₁ α₂ γ → ℝ}

/-- The law of a key: `0` with probability `1 - ε`, and uniform on the other `K` values
otherwise. -/
def rareKeyLaw (K : ℕ) (ε : ℝ) : Fin (K + 1) → ℝ :=
  Fin.cons (1 - ε) fun _ => ε / K

lemma rareKeyLaw_isPMF {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    IsPMF (rareKeyLaw K ε) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  refine ⟨fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [rareKeyLaw, hε₁]
    · simp only [rareKeyLaw, Fin.cons_succ]
      positivity
  · rw [Fin.sum_univ_succ]
    simp only [rareKeyLaw, Fin.cons_zero, Fin.cons_succ, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring

/-- The entropy of the key is at least `ε log K`. -/
lemma le_entropy_rareKeyLaw {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ε * log K ≤ entropy (rareKeyLaw K ε) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_succ]
  simp only [rareKeyLaw, Fin.cons_zero, Fin.cons_succ, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have h₁ : 0 ≤ negMulLog (1 - ε) := negMulLog_nonneg (by linarith) (by linarith)
  have h₂ : (K : ℝ) * negMulLog (ε / K) = ε * (log K - log ε) := by
    rw [negMulLog, log_div hε.ne' hK'.ne']
    field_simp
    ring
  have h₃ : log ε ≤ 0 := log_nonpos hε.le hε₁
  rw [h₂]
  nlinarith

/-- **The definition of page 23-30 of [elgamal2010] needs a bound on the alphabet of the key.** With
keys in `ℤ⁺`, as in the notes, the proof of Theorem 8 does not work and its statement fails. For
every source, block length, `ε` and `B`, there is a protocol, with no communication at all, in which
each node draws a huge private key with probability `ε`: the keys differ with probability at most
`2 ε`, the leakage is `0`, and `H(Kⱼ) ≥ B`. Letting `ε → 0` with `B = n R`, every rate would be
achievable. This is why `IsAchievableKey` takes keys in `[1 : 2 ^ ⌈nR⌉]`. -/
theorem unbounded_key_counterexample (hP : IsPMF P) (n : ℕ) {ε B : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ (K : ℕ) (θ : Fin (K + 1) → ℝ)
      (c : KeyCode (q := 0) Fin.elim0 (fun _ => 1) (K + 1)
        ((Fin n → α₁) × Fin (K + 1)) ((Fin n → α₂) × Fin (K + 1))),
      IsPMF θ ∧ c.errProbB P θ θ ≤ 2 * ε ∧ c.leak₁ P θ θ = 0 ∧ c.leak₂ P θ θ = 0 ∧
        B ≤ c.entropyKey₁ P θ θ ∧ B ≤ c.entropyKey₂ P θ θ := by
  classical
  set K := ⌈exp (B / ε)⌉₊ + 1 with hK
  have hK0 : 0 < K := by omega
  have hKe : B ≤ ε * log K := by
    have h₁ : exp (B / ε) ≤ K := by
      have := Nat.le_ceil (exp (B / ε))
      have h₂ : (⌈exp (B / ε)⌉₊ : ℝ) ≤ K := by
        rw [hK]
        push_cast
        linarith
      linarith
    have h₂ := (le_log_iff_exp_le (by exact_mod_cast hK0)).2 h₁
    rw [div_le_iff₀ hε] at h₂
    linarith
  set θ := rareKeyLaw K ε with hθ
  have hθP : IsPMF θ := rareKeyLaw_isPMF hK0 hε.le hε₁
  set c : KeyCode (q := 0) Fin.elim0 (fun _ => 1) (K + 1)
      ((Fin n → α₁) × Fin (K + 1)) ((Fin n → α₂) × Fin (K + 1)) :=
    ⟨fun l => l.elim0, fun l => l.elim0, fun a _ => a.2, fun a _ => a.2⟩ with hc
  have hμ : IsPMF (keyLaw P θ θ n) := secBlockLaw_isPMF hP (hθP.prodDist hθP) n
  have hT : ∀ (w : (Fin n → srcLetter α₁ α₂ γ) × Fin (K + 1) × Fin (K + 1)),
      c.transB Prod.fst (fun a => a.2.1) w = fun l => l.elim0 := fun w => funext fun l => l.elim0
  have hunit : H[(fun _ : srcLetter α₁ α₂ γ => ()) ; P] = 0 := entropyRV_const hP ()
  have hH₁ : H[(fun w : (Fin n → srcLetter α₁ α₂ γ) × Fin (K + 1) × Fin (K + 1) => w.2.1) ;
      keyLaw P θ θ n] = H[Prod.fst ; prodDist θ θ] := by
    rw [entropy_keyLaw_of hP hθP hθP n (fun _ => ()) Prod.fst _ (fun v => v.2)
      (fun a b h => Prod.ext (funext fun _ => rfl) h) fun _ => rfl, hunit]
    ring
  have hH₂ : H[(fun w : (Fin n → srcLetter α₁ α₂ γ) × Fin (K + 1) × Fin (K + 1) => w.2.2) ;
      keyLaw P θ θ n] = H[Prod.snd ; prodDist θ θ] := by
    rw [entropy_keyLaw_of hP hθP hθP n (fun _ => ()) Prod.snd _ (fun v => v.2)
      (fun a b h => Prod.ext (funext fun _ => rfl) h) fun _ => rfl, hunit]
    ring
  have hfst : H[Prod.fst ; prodDist θ θ] = entropy θ := by
    rw [entropyRV, dist_prodDist_fst hθP]
  have hsnd : H[Prod.snd ; prodDist θ θ] = entropy θ := by
    rw [entropyRV, dist_prodDist_snd hθP]
  have hleak : ∀ g : Fin (K + 1) × Fin (K + 1) → Fin (K + 1),
      I[(fun w : (Fin n → srcLetter α₁ α₂ γ) × Fin (K + 1) × Fin (K + 1) => g w.2) :
        pair KeyCode.eveB (c.transB Prod.fst fun a => a.2.1) ; keyLaw P θ θ n] = 0 := fun g => by
    rw [mutualInfo_eq_add_sub hμ]
    have h₁ := entropy_keyLaw_of hP hθP hθP n (fun _ => ()) g
      (fun w : (Fin n → srcLetter α₁ α₂ γ) × Fin (K + 1) × Fin (K + 1) => g w.2) (fun v => v.2)
      (fun a b h => Prod.ext (funext fun _ => rfl) h) fun _ => rfl
    have h₂ := entropy_keyLaw_of hP hθP hθP n (fun a : srcLetter α₁ α₂ γ => a.2.2) (fun _ => ())
      (pair KeyCode.eveB (c.transB Prod.fst fun a => a.2.1)) (fun v => (v.1, fun l => l.elim0))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 rfl) fun w => Prod.ext rfl (hT w)
    have h₃ := entropy_keyLaw_of hP hθP hθP n (fun a : srcLetter α₁ α₂ γ => a.2.2) g
      (pair (fun w : (Fin n → srcLetter α₁ α₂ γ) × Fin (K + 1) × Fin (K + 1) => g w.2)
        (pair KeyCode.eveB (c.transB Prod.fst fun a => a.2.1)))
      (fun v => (v.2, v.1, fun l => l.elim0))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 h.1) fun w => Prod.ext rfl (Prod.ext rfl (hT w))
    have h₄ := entropy_seeds_const (hθP.prodDist hθP)
    rw [h₁, h₂, h₃, hunit, h₄]
    ring
  refine ⟨K, θ, c, hθP, ?_, hleak Prod.fst, hleak Prod.snd, ?_, ?_⟩
  · -- The keys differ only if one of them is not `0`.
    simp only [KeyCode.errProbB, InfoTheory.errProb]
    have hz : ∑ a, θ a * (if a ≠ 0 then (1 : ℝ) else 0) = ε := by
      have h₁ : ∀ a, θ a * (if a ≠ 0 then (1 : ℝ) else 0) = θ a - if a = 0 then θ a else 0 :=
        fun a => by by_cases h : a = 0 <;> simp [h]
      simp only [h₁]
      rw [sum_sub_distrib, hθP.sum_eq_one, sum_ite_eq' univ (0 : Fin (K + 1))]
      simp [hθ, rareKeyLaw]
    have hseed : ∀ g : Fin (K + 1) × Fin (K + 1) → ℝ, ∑ w, keyLaw P θ θ n w * g w.2 =
        ∑ u, prodDist θ θ u * g u := fun g => by
      have h₁ := sum_dist_mul (keyLaw P θ θ n) Prod.snd g
      have h₂ : dist (keyLaw P θ θ n) Prod.snd = prodDist θ θ :=
        dist_prodDist_snd (iidPMF_isPMF hP n) _
      rw [h₂] at h₁
      exact h₁.symm
    have h₁ : ∑ w, keyLaw P θ θ n w * (if w.2.1 ≠ 0 then (1 : ℝ) else 0) = ε := by
      rw [hseed fun u => if u.1 ≠ 0 then (1 : ℝ) else 0, Fintype.sum_prod_type, ← hz]
      refine sum_congr rfl fun a _ => ?_
      simp only [prodDist]
      have e : ∀ b, θ a * θ b * (if a ≠ 0 then (1 : ℝ) else 0) =
          θ a * (if a ≠ 0 then (1 : ℝ) else 0) * θ b := fun b => by ring
      simp only [e, ← mul_sum, hθP.sum_eq_one, mul_one]
    have h₂ : ∑ w, keyLaw P θ θ n w * (if w.2.2 ≠ 0 then (1 : ℝ) else 0) = ε := by
      rw [hseed fun u => if u.2 ≠ 0 then (1 : ℝ) else 0, Fintype.sum_prod_type, ← hz]
      simp only [prodDist, mul_assoc, ← mul_sum, hz, ← sum_mul, hθP.sum_eq_one, one_mul]
    have hfin : ∑ w, (keyLaw P θ θ n w * (if w.2.1 ≠ 0 then (1 : ℝ) else 0) +
        keyLaw P θ θ n w * (if w.2.2 ≠ 0 then (1 : ℝ) else 0)) ≤ 2 * ε := by
      rw [sum_add_distrib, h₁, h₂]
      linarith
    refine le_trans (sum_le_sum fun w _ => ?_) hfin
    have h₀ := hμ.nonneg w
    have hi₁ : (0 : ℝ) ≤ keyLaw P θ θ n w * (if w.2.1 ≠ 0 then (1 : ℝ) else 0) :=
      mul_nonneg h₀ (by split_ifs <;> norm_num)
    have hi₂ : (0 : ℝ) ≤ keyLaw P θ θ n w * (if w.2.2 ≠ 0 then (1 : ℝ) else 0) :=
      mul_nonneg h₀ (by split_ifs <;> norm_num)
    by_cases hne : w.2.2 = w.2.1
    · have e : id (c.keyB₂ Prod.fst (fun a => a.2.1) w) = c.keyB₁ Prod.fst (fun a => a.2.1) w := hne
      rw [ite_eq_right (not_not.2 e)]
      positivity
    · have e : id (c.keyB₂ Prod.fst (fun a => a.2.1) w) ≠ c.keyB₁ Prod.fst (fun a => a.2.1) w := hne
      rw [ite_eq_left e]
      by_cases h₃ : w.2.1 = 0
      · have h₄ : w.2.2 ≠ 0 := fun h => hne (h.trans h₃.symm)
        simp only [h₄, ne_eq, not_false_eq_true, ite_true, mul_one]
        linarith
      · simp only [h₃, ne_eq, not_false_eq_true, ite_true, mul_one]
        linarith
  · change B ≤ H[(fun w => w.2.1) ; keyLaw P θ θ n]
    rw [hH₁, hfst]
    exact hKe.trans (le_entropy_rareKeyLaw hK0 hε hε₁)
  · change B ≤ H[(fun w => w.2.2) ; keyLaw P θ θ n]
    rw [hH₂, hsnd]
    exact hKe.trans (le_entropy_rareKeyLaw hK0 hε hε₁)

end Unbounded

/-! ### The results by number -/

section Aliases

variable {α β γ α₁ α₂ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype α₁] [Fintype α₂]

/-- **Theorem 1 of Lecture 23 of [elgamal2010].** Perfect secrecy implies `H(M) ≤ H(K)`. -/
theorem theorem_23_1 {Ω 𝓜 𝓚 𝓛 : Type*} [Fintype Ω] [Fintype 𝓜] [Fintype 𝓚] [Fintype 𝓛] {μ : Ω → ℝ}
    (hμ : IsPMF μ) (M : Ω → 𝓜) (K : Ω → 𝓚) (L : Ω → 𝓛) (dec : 𝓛 → 𝓚 → 𝓜)
    (hdec : ∀ ω, μ ω ≠ 0 → M ω = dec (L ω) (K ω)) (hsec : I[M : L ; μ] = 0) :
    H[M ; μ] ≤ H[K ; μ] :=
  entropy_le_of_perfectSecrecy hμ M K L dec hdec hsec

/-- **Theorem 2 of Lecture 23 of [elgamal2010].** `C(R_K) = min {R_K, max_{p(x)} I(X; Y)}`. -/
theorem theorem_23_2 [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) {RK : ℝ} (hRK : 0 ≤ RK) :
    keyedSecrecyCapacity W RK = min RK (capacity W / log 2) :=
  keyedSecrecyCapacity_eq hW hRK

/-- **Theorem 3 of Lecture 23 of [elgamal2010].** `C_S = max_{p(u, x)} (I(U; Y) - I(U; Z))`, with
`|𝒰| ≤ |𝒳|`. -/
theorem theorem_23_3 [Nonempty α] {W : α → β × γ → ℝ} (hW : IsChannel W) :
    wiretapCapacity W = wiretapValue W / log 2 :=
  wiretapCapacity_eq hW

/-- **Theorem 6 of Lecture 23 of [elgamal2010].** The one-way secret key capacity. -/
theorem theorem_23_6 {P : srcLetter α₁ α₂ γ → ℝ} (hP : IsPMF P) :
    keyCapacityOneWay P = max (oneWayValue P / log 2) (oneWayValue (srcSwap P) / log 2) :=
  keyCapacityOneWay_eq hP

/-- **Theorem 8 of Lecture 23 of [elgamal2010].** `C_K ≤ inf_{p(z̄ | z)} I(X₁; X₂ | Z̄)`. -/
theorem theorem_23_8 {P : srcLetter α₁ α₂ γ → ℝ} (hP : IsPMF P) :
    keyCapacity P ≤ intrinsicInfo P / log 2 :=
  keyCapacity_le _ hP

/-- **Theorem 9 of Lecture 23 of [elgamal2010].** For `N ≥ 2`, when all the nodes know `Z`,
`C_K = H(X^N | Z) - R_CFO([1 : N] | Z)`. -/
theorem theorem_23_9 {N : ℕ} {α' : Fin N → Type*} [∀ j, Fintype (α' j)] {p : mLetter α' γ → ℝ}
    (hp : IsPMF p) (hN : 2 ≤ N) :
    multiKeyCapacity p = H[Prod.fst | Prod.snd ; p] / log 2 - rCFOZ p :=
  multiKeyCapacity_eq hp hN

end Aliases

end ElGamalKim

end InfoTheory
