/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Fading
public import InfoTheoryLib.Network.Fading

/-!
# El Gamal & Kim, Lecture 8: Fading Channels

This file indexes the formalization of Lecture 8 of [elgamal2010] and contains the lecture's
two-state example. The notes state most of the results of this lecture with references for the
proofs, and the lecture has no numbered results. We prove the compound capacity of the slowly fading
channel as a coding theorem; everything else is about the formulas of the notes, which are
performance metrics or capacities whose coding theorems are not formalized.

## Conventions

* **Fading states.** There are finitely many: a state `s` has probability `q(s)` and gain `g(s)`, so
  that `E f(G) = ∑ₛ q(s) f(g(s))`. The notes allow general stationary ergodic gain processes.
* **Rates.** The coding theorems are in bits, as in Lecture 3. The formulas are in nats, in terms of
  `gaussCap x = ½ log(1 + x)`.
* **Water-filling.** `(λ - 1/g²)⁺` is `0` for `g = 0`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Gaussian fading channel: fast fading (formulas)
* `C_SI-D = E C(G²P)`: `fadingErgodic` (`GaussianChannel.Fading`).
* `C_SI-ED = max_φ E C(G²φ(G))`: `fadingPowerRate`, `IsFadingPower`, `fadingPowerValue`.
* Water-filling in time: `fadingWaterFill`, `fadingPowerRate_le_of_waterFill`,
  `exists_fadingWaterFill_eq`, `fadingPowerValue_eq_of_waterFill`.
* At high SNR the gain from power control vanishes: `tendsto_fadingPowerValue_sub_fadingErgodic`.

### Gaussian fading channel: slow fading
* The compound channel approach, as a coding theorem, for finitely many nonzero gains:
  `IsAchievableFadingCompound`, `fadingCompoundCapacity`, `fadingCompoundValue`,
  `fadingCompoundCapacity_eq` (`GaussianChannel.FadingCompound`), by the degradedness in the gain
  `map_noiseLaw_prod`, `GaussianCode.exists_dec_degraded`.
* With the gain also at the encoder: `IsAchievableFadingCompoundE`, `fadingCompoundCapacityE`,
  `fadingCompoundCapacityE_eq`.
* The outage capacity: `fadingOutage`, `fadingCompoundValue_le_fadingOutage`, `fadingOutage_zero`
  (`GaussianChannel.Fading`), and for two states `fadingOutage_twoState_of_lt`,
  `fadingOutage_twoState_of_le` (here).
* The broadcasting approach: `fadingBroadcastRate`, `fadingBroadcastValue`,
  `fadingBroadcastRate_eq`, `gaussCap_common`.
* Adaptive coding, with and without power control: `fadingErgodic`, `fadingPowerValue`.
* The example with two fading states: `twoQ`, `twoG`, `fadingErgodic_twoState`,
  `fadingCompoundValue_twoState`, and the order `C_C ≤ C_BC ≤ C_A ≤ C_PA`:
  `twoState_compound_le_broadcast`, `twoState_broadcast_le_adaptive`, `twoState_adaptive_le_power`
  (here), with `mul_gaussCap_le_fadingBroadcastValue`.

### Gaussian fading MAC (formulas)
* The ergodic regions: `fadingMACRates`, `fadingMACRegionD`, `fadingMACRegionDSI`,
  `fadingMACRegionED`, `fadingMACRegionD_subset`, `fadingMACRegionDSI_subset`, and the corner point
  `corner_mem_fadingMACRates` (`Network.Fading`).
* Adaptive coding and the sum capacities: `IsAdaptiveMAC`, `adaptiveSum`, `macSumC`, `macSumA`,
  `macSumPA`, `macSumDSI`, `macSumED`, with the order `macSumC_le_macSumA`, `macSumA_le_macSumPA`,
  `macSumPA_le_macSumDSI`, `macSumDSI_le_macSumED`.

### Gaussian fading BC (formulas)
* The region of the notes: `fadingBCInfo₁`, `fadingBCInfo₂`, `fadingBCRegion` (`Network.Fading`).
* With a split depending on the state: `fadingBCPolicyRegion`, `fadingBCRegion_subset_policy`,
  `half_mem_fadingBCPolicyRegion`, `not_mem_fadingBCRegion_alternating`.
* The compound region: `fadingBCCompoundRegion`, `endpoints_mem_fadingBCCompoundRegion`.

### Gaussian fading IC (formulas)
* Time division and treating the interference as noise: `icTimeDivision`, `icTreatAsNoise`, with the
  rate per user `tendsto_icTimeDivision_div`, `tendsto_icTreatAsNoise_div` (`Network.Fading`).
* Ergodic interference alignment: `icAlignment`, `icTimeDivision_le_icAlignment`,
  `icTreatAsNoise_le_icAlignment`. The conjugate matrices: `gainMatrix`, `conjSigns`,
  `conjSigns_conjSigns`, `conjSigns_ne`, `gain_add_conj`, `alignment_snr`, `card_gainMatrices`.
* The step of the converse from the pairs of users to the sum: `sum_le_of_pairwise`.

## Not formalized

* The coding theorems of fast fading: the ergodic capacities of the channel, of the MAC, of the BC
  and of the IC, for which we only study the formulas. They need coding over the gain process for
  continuous alphabets, which the library has only for a fixed gain (`GaussianChannel.AWGN`).
* General stationary ergodic gain processes, and block fading with a coherence time `k > 1`.
* The operational meaning of the outage, broadcasting and adaptive metrics, which the notes call
  performance metrics, not capacities in the Shannon sense.
* The compound channel with a zero gain or infinitely many gains; the infimum on page 8-10.
* The equivalent multiple MACs on page 8-19 with the Fourier–Motzkin elimination, the optimization
  of the sum capacities, the figures on pages 8-12, 8-22 and 8-23 beyond the order of the metrics,
  and the outage capacity region of the BC.
* The achievability and the two-user AWGN-IC bound in the converse of ergodic interference
  alignment, and its extension to symmetric fading distributions.

## Issues in the notes

* **Page 8-6.** The claim that the gain from power control vanishes at high SNR needs
  `P{G = 0} = 0`, which holds if `G ⊆ ℝ₊` of page 8-3 excludes `0` (the notes do not define `ℝ₊`).
  With `P{G = 0} = q₀ > 0` the gap tends to `((1 - q₀)/2) log(1/(1 - q₀)) > 0`.
  `tendsto_fadingPowerValue_sub_fadingErgodic` assumes nonzero gains.
* **Page 8-8.** The outage capacity is written with `{g : P{G ≤ g} ≤ p_out}`. Sending at the rate
  `C(g²P)` is in outage exactly when `G < g`, and with finitely many gains the set for `p_out = 0`
  contains no gain of the support and has no maximum. `fadingOutage` uses `P{G < g} ≤ p_out`.
* **Page 8-20.** The optimization for the adaptive sum capacity has `φ₁`, `φ₂` in place of `P`:
  `R₂(g₂) ≤ C(g₂²φ₂(g₂))` and `R₁(g₁) + R₂(g₂) ≤ C(g₁²φ₁(g₁) + g₂²φ₂(g₂))`; there is no power
  control in this case. The next page has the form with `φ`.
* **Page 8-25.** The region stated as the ergodic capacity region of the BC, with a fixed `α`, is
  too small: the split must be allowed to depend on the state. With two equally likely states in
  which only one receiver has the gain `g`, giving all the power to that receiver gives
  `(½ C(g²P), ½ C(g²P))`, which is not in the region: `half_mem_fadingBCPolicyRegion`,
  `not_mem_fadingBCRegion_alternating`. The coding theorem for the larger region is not formalized.
* **Page 8-25.** The compound region is printed with `g₁*`, `g₂*` in place of `g₁*²`, `g₂*²`.
* **Page 8-28.** The second AWGN-IC is printed with two outputs `Yⱼ`; the second one should be
  `Yⱼ'`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 8
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Two fading states -/

/-- **Example (Lecture 8), page 8-12.** The state `true` has probability `p`. -/
def twoQ (p : ℝ) : Bool → ℝ := fun s => if s then p else 1 - p

/-- **Example (Lecture 8), page 8-12.** The state `true` has the gain `g₁`, the state `false` the
gain `g₂`. -/
def twoG (g₁ g₂ : ℝ) : Bool → ℝ := fun s => if s then g₁ else g₂

variable {p g₁ g₂ P : ℝ}

lemma twoQ_isPMF (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsPMF (twoQ p) := by
  refine ⟨fun s => ?_, by simp [twoQ]⟩
  cases s <;> simp [twoQ] <;> linarith

/-- `C_A = p C(g₁²P) + (1 - p) C(g₂²P)`. -/
theorem fadingErgodic_twoState :
    fadingErgodic (twoQ p) (twoG g₁ g₂) P =
      p * gaussCap (g₁ ^ 2 * P) + (1 - p) * gaussCap (g₂ ^ 2 * P) := by
  simp [fadingErgodic, twoQ, twoG]

/-- `C_C = C(g₂²P)` for `0 ≤ g₂ ≤ g₁`. -/
theorem fadingCompoundValue_twoState (h2 : 0 ≤ g₂) (h : g₂ ≤ g₁) (hP : 0 ≤ P) :
    fadingCompoundValue (twoG g₁ g₂) P = gaussCap (g₂ ^ 2 * P) := by
  refine le_antisymm (inf'_le (fun s => gaussCap (twoG g₁ g₂ s ^ 2 * P)) (mem_univ false)) ?_
  refine le_inf' _ _ fun s _ => ?_
  cases s
  · exact le_rfl
  · exact gaussCap_le_gaussCap (mul_nonneg (sq_nonneg _) hP)
      (mul_le_mul_of_nonneg_right (sq_le_sq_of_gain h2 h) hP)

/-- **Example (Lecture 8), page 8-12.** `C_C ≤ C_BC`. -/
theorem twoState_compound_le_broadcast (h0 : 0 ≤ p) (h1 : p ≤ 1) (h2 : 0 ≤ g₂) (h : g₂ ≤ g₁)
    (hP : 0 ≤ P) :
    fadingCompoundValue (twoG g₁ g₂) P ≤ fadingBroadcastValue p (g₁ ^ 2) (g₂ ^ 2) P := by
  rw [fadingCompoundValue_twoState h2 h hP]
  exact gaussCap_le_fadingBroadcastValue ⟨h0, h1⟩ (sq_nonneg _) (sq_le_sq_of_gain h2 h) hP

/-- **Example (Lecture 8), page 8-12.** `C_BC ≤ C_A`. -/
theorem twoState_broadcast_le_adaptive (h0 : 0 ≤ p) (h1 : p ≤ 1) (h2 : 0 ≤ g₂) (h : g₂ ≤ g₁)
    (hP : 0 ≤ P) :
    fadingBroadcastValue p (g₁ ^ 2) (g₂ ^ 2) P ≤ fadingErgodic (twoQ p) (twoG g₁ g₂) P := by
  rw [fadingErgodic_twoState]
  exact fadingBroadcastValue_le ⟨h0, h1⟩ (sq_nonneg _) (sq_le_sq_of_gain h2 h) hP

/-- **Example (Lecture 8), page 8-12.** `C_A ≤ C_PA`. -/
theorem twoState_adaptive_le_power (h0 : 0 ≤ p) (h1 : p ≤ 1) (hP : 0 ≤ P) :
    fadingErgodic (twoQ p) (twoG g₁ g₂) P ≤ fadingPowerValue (twoQ p) (twoG g₁ g₂) P :=
  fadingErgodic_le_fadingPowerValue (twoQ_isPMF h0 h1) _ hP

/-- **Example (Lecture 8), page 8-12.** If `p_out` is below the probability of the weak state, only
the rate `C(g₂²P)` meets the outage constraint: `C_out = C(g₂²P)`. -/
theorem fadingOutage_twoState_of_lt {pout : ℝ} (h2 : g₂ < g₁) (hpout0 : 0 ≤ pout)
    (hpout : pout < 1 - p) :
    fadingOutage (twoQ p) (twoG g₁ g₂) P pout = gaussCap (g₂ ^ 2 * P) := by
  classical
  have hset : {v | ∃ s, ∑ t with twoG g₁ g₂ t < twoG g₁ g₂ s, twoQ p t ≤ pout ∧
      gaussCap (twoG g₁ g₂ s ^ 2 * P) = v} = {gaussCap (g₂ ^ 2 * P)} := by
    ext v
    constructor
    · rintro ⟨s, hs, rfl⟩
      cases s
      · rfl
      · exfalso
        have hf : (univ.filter fun t => twoG g₁ g₂ t < twoG g₁ g₂ true) = {false} := by
          ext t
          cases t <;> simp [twoG, h2]
        rw [hf, sum_singleton] at hs
        simp only [twoQ, Bool.false_eq_true, ite_false] at hs
        linarith
    · rintro rfl
      refine ⟨false, ?_, rfl⟩
      have hf : (univ.filter fun t => twoG g₁ g₂ t < twoG g₁ g₂ false) = ∅ := by
        ext t
        cases t <;> simp [twoG, h2.le]
      rw [hf, sum_empty]
      exact hpout0
  rw [fadingOutage, hset, csSup_singleton]

/-- **Example (Lecture 8), page 8-12.** From the probability of the weak state on, the rate
`C(g₁²P)` is allowed: `C_out = C(g₁²P)`. -/
theorem fadingOutage_twoState_of_le {pout : ℝ} (h20 : 0 ≤ g₂) (h2 : g₂ < g₁) (hP : 0 ≤ P)
    (hpout : 1 - p ≤ pout) :
    fadingOutage (twoQ p) (twoG g₁ g₂) P pout = gaussCap (g₁ ^ 2 * P) := by
  classical
  have hf : (univ.filter fun t => twoG g₁ g₂ t < twoG g₁ g₂ true) = {false} := by
    ext t
    cases t <;> simp [twoG, h2]
  refine le_antisymm (csSup_le ?_ ?_) (le_csSup (bddAbove_fadingOutage _ _ _ _) ?_)
  · refine ⟨_, true, ?_, rfl⟩
    rw [hf, sum_singleton]
    simpa [twoQ] using hpout
  · rintro _ ⟨s, -, rfl⟩
    cases s
    · exact gaussCap_le_gaussCap (mul_nonneg (sq_nonneg _) hP)
        (mul_le_mul_of_nonneg_right (sq_le_sq_of_gain h20 h2.le) hP)
    · exact le_rfl
  · refine ⟨true, ?_, rfl⟩
    rw [hf, sum_singleton]
    simpa [twoQ] using hpout

end InfoTheory.ElGamalKim
