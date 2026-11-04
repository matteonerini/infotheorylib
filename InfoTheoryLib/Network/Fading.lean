/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.Gaussian
public import InfoTheoryLib.Probability.FinitePMF

/-!
# Gaussian fading networks: the formulas

Lecture 8 of El Gamal and Kim states the regions of the Gaussian fading MAC and BC and the sum
capacity of a fading interference channel, in terms of `C(x) = ½ log(1 + x)`, with references for
the proofs. This file studies these formulas for finitely many fading states; they are not coding
theorems.

## Main definitions

* `fadingMACRates`, `fadingMACRegionD`, `fadingMACRegionDSI`, `fadingMACRegionED`: the ergodic
  regions of the MAC with the gains at the decoder, at their respective encoders and the decoder,
  and at both encoders and the decoder.
* `IsAdaptiveMAC`, `macSumC`, `macSumA`, `macSumPA`, `macSumDSI`, `macSumED`: the sum capacities.
* `fadingBCRegion`, `fadingBCPolicyRegion`: the ergodic region of the BC as in the notes, and with a
  power split that depends on the state.
* `icTimeDivision`, `icTreatAsNoise`, `icAlignment`: the sum rates of the fading interference
  channel.

## Main statements

* `fadingMACRegionD_subset`, `fadingMACRegionDSI_subset`: the order of the regions.
* `macSumC_le_macSumA`, `macSumA_le_macSumPA`, `macSumPA_le_macSumDSI`, `macSumDSI_le_macSumED`: the
  order of the sum capacities.
* `corner_mem_fadingMACRates`: the sum rate of the MAC is attained at a corner point.
* `fadingBCRegion_subset_policy`, `not_mem_fadingBCRegion_alternating`: the region with a fixed
  split is strictly smaller.
* `sum_le_of_pairwise`: the pairwise bounds give the converse of ergodic interference alignment.
* `icTimeDivision_le_icAlignment`, `icTreatAsNoise_le_icAlignment`,
  `tendsto_icTimeDivision_div`, `tendsto_icTreatAsNoise_div`: the comparison of the schemes.
* `gain_add_conj`: the conjugate channel gain matrix cancels the interference.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 8
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- `C(a + b) ≤ C(a) + C(b)`. -/
lemma gaussCap_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    gaussCap (a + b) ≤ gaussCap a + gaussCap b := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  simp only [gaussCap]
  rw [← mul_add, ← log_mul h1.ne' h2.ne']
  refine mul_le_mul_of_nonneg_left (log_le_log (by linarith) ?_) (by norm_num)
  nlinarith [mul_nonneg ha hb]

/-- `C(x) ≤ x/2`. -/
lemma gaussCap_le_half_self {x : ℝ} (hx : 0 ≤ x) : gaussCap x ≤ x / 2 := by
  simp only [gaussCap]
  have := log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
  linarith

/-! ### The fading MAC -/

section MAC

variable {𝒢₁ 𝒢₂ : Type*} [Fintype 𝒢₁] [Fintype 𝒢₂] {q : 𝒢₁ × 𝒢₂ → ℝ} {h₁ : 𝒢₁ → ℝ} {h₂ : 𝒢₂ → ℝ}
  {P : ℝ}

/-- `E C(G₁² φ₁)`. -/
def fadingMACInfo₁ (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (φ₁ : 𝒢₁ × 𝒢₂ → ℝ) : ℝ :=
  ∑ s, q s * gaussCap (h₁ s.1 ^ 2 * φ₁ s)

/-- `E C(G₂² φ₂)`. -/
def fadingMACInfo₂ (q : 𝒢₁ × 𝒢₂ → ℝ) (h₂ : 𝒢₂ → ℝ) (φ₂ : 𝒢₁ × 𝒢₂ → ℝ) : ℝ :=
  ∑ s, q s * gaussCap (h₂ s.2 ^ 2 * φ₂ s)

/-- `E C(G₁² φ₁ + G₂² φ₂)`, the sum rate. -/
def fadingMACSum (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (φ₁ φ₂ : 𝒢₁ × 𝒢₂ → ℝ) : ℝ :=
  ∑ s, q s * gaussCap (h₁ s.1 ^ 2 * φ₁ s + h₂ s.2 ^ 2 * φ₂ s)

/-- The rate pairs of the power allocations `φ₁`, `φ₂`. -/
def fadingMACRates (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (φ₁ φ₂ : 𝒢₁ × 𝒢₂ → ℝ) :
    Set (ℝ × ℝ) :=
  {R | R.1 ≤ fadingMACInfo₁ q h₁ φ₁ ∧ R.2 ≤ fadingMACInfo₂ q h₂ φ₂ ∧
    R.1 + R.2 ≤ fadingMACSum q h₁ h₂ φ₁ φ₂}

/-- A power allocation with `φ ≥ 0` and `E φ(G₁, G₂) ≤ P`. -/
def IsFadingMACPower (q φ : 𝒢₁ × 𝒢₂ → ℝ) (P : ℝ) : Prop := (∀ s, 0 ≤ φ s) ∧ ∑ s, q s * φ s ≤ P

/-- **Lecture 8 of [elgamal2010], page 8-14.** The ergodic region with the gains at the decoder. -/
def fadingMACRegionD (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : Set (ℝ × ℝ) :=
  fadingMACRates q h₁ h₂ (fun _ => P) fun _ => P

/-- **Lecture 8 of [elgamal2010], page 8-15.** The ergodic region with the gains at their respective
encoders and the decoder: `φⱼ` depends only on `Gⱼ`. -/
def fadingMACRegionDSI (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (f₁ : 𝒢₁ → ℝ) (f₂ : 𝒢₂ → ℝ), IsFadingMACPower q (fun s => f₁ s.1) P ∧
    IsFadingMACPower q (fun s => f₂ s.2) P ∧
    R ∈ fadingMACRates q h₁ h₂ (fun s => f₁ s.1) fun s => f₂ s.2}

/-- **Lecture 8 of [elgamal2010], page 8-14.** The ergodic region with the gains at both encoders
and the decoder. -/
def fadingMACRegionED (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ φ₁ φ₂, IsFadingMACPower q φ₁ P ∧ IsFadingMACPower q φ₂ P ∧
    R ∈ fadingMACRates q h₁ h₂ φ₁ φ₂}

lemma isFadingMACPower_const (hq : IsPMF q) (hP : 0 ≤ P) :
    IsFadingMACPower q (fun _ => P) P :=
  ⟨fun _ => hP, by rw [← sum_mul, hq.sum_eq_one, one_mul]⟩

/-- More knowledge at the encoders can only help. -/
theorem fadingMACRegionD_subset (hq : IsPMF q) (hP : 0 ≤ P) :
    fadingMACRegionD q h₁ h₂ P ⊆ fadingMACRegionDSI q h₁ h₂ P := fun _ hR =>
  ⟨fun _ => P, fun _ => P, isFadingMACPower_const hq hP, isFadingMACPower_const hq hP, hR⟩

/-- More knowledge at the encoders can only help. -/
theorem fadingMACRegionDSI_subset : fadingMACRegionDSI q h₁ h₂ P ⊆ fadingMACRegionED q h₁ h₂ P := by
  rintro _ ⟨f₁, f₂, h1, h2, hR⟩
  exact ⟨_, _, h1, h2, hR⟩

/-- **Lecture 8 of [elgamal2010], page 8-14.** The bound on the sum rate is attained at a corner
point: `R₂ = E C(G₂²P)`, `R₁ = E C((G₁² + G₂²)P) - E C(G₂²P)`. -/
theorem corner_mem_fadingMACRates (hq : ∀ s, 0 ≤ q s) (hP : 0 ≤ P) :
    (fadingMACSum q h₁ h₂ (fun _ => P) (fun _ => P) - fadingMACInfo₂ q h₂ fun _ => P,
      fadingMACInfo₂ q h₂ fun _ => P) ∈ fadingMACRegionD q h₁ h₂ P := by
  refine ⟨?_, le_rfl, by simp⟩
  rw [sub_le_iff_le_add, fadingMACSum, fadingMACInfo₁, fadingMACInfo₂, ← sum_add_distrib]
  refine sum_le_sum fun s _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (gaussCap_add_le (mul_nonneg (sq_nonneg _) hP)
    (mul_nonneg (sq_nonneg _) hP)) (hq s)

/-! ### Adaptive coding and the sum capacities -/

/-- **Lecture 8 of [elgamal2010], pages 8-20 and 8-21.** The adaptive rates `R₁(g₁)`, `R₂(g₂)` for
the power allocations `φ₁(g₁)`, `φ₂(g₂)`: each message is decoded whatever the gain of the other
sender. -/
def IsAdaptiveMAC (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (φ₁ : 𝒢₁ → ℝ) (φ₂ : 𝒢₂ → ℝ) (R₁ : 𝒢₁ → ℝ)
    (R₂ : 𝒢₂ → ℝ) : Prop :=
  (∀ g₁, R₁ g₁ ≤ gaussCap (h₁ g₁ ^ 2 * φ₁ g₁)) ∧ (∀ g₂, R₂ g₂ ≤ gaussCap (h₂ g₂ ^ 2 * φ₂ g₂)) ∧
    ∀ g₁ g₂, R₁ g₁ + R₂ g₂ ≤ gaussCap (h₁ g₁ ^ 2 * φ₁ g₁ + h₂ g₂ ^ 2 * φ₂ g₂)

/-- `E R₁(G₁) + E R₂(G₂)`. -/
def adaptiveSum (q : 𝒢₁ × 𝒢₂ → ℝ) (R₁ : 𝒢₁ → ℝ) (R₂ : 𝒢₂ → ℝ) : ℝ :=
  ∑ s, q s * (R₁ s.1 + R₂ s.2)

/-- **Lecture 8 of [elgamal2010], page 8-17.** The compound sum capacity: constant rates. -/
def macSumC (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ r₁ r₂ : ℝ, IsAdaptiveMAC h₁ h₂ (fun _ => P) (fun _ => P) (fun _ => r₁) (fun _ => r₂) ∧
    adaptiveSum q (fun _ => r₁) (fun _ => r₂) = v}

/-- **Lecture 8 of [elgamal2010], page 8-20.** The adaptive sum capacity. -/
def macSumA (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ R₁ R₂, IsAdaptiveMAC h₁ h₂ (fun _ => P) (fun _ => P) R₁ R₂ ∧ adaptiveSum q R₁ R₂ = v}

/-- **Lecture 8 of [elgamal2010], page 8-21.** The power-control adaptive sum capacity. -/
def macSumPA (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ f₁ f₂ R₁ R₂, IsFadingMACPower q (fun s => f₁ s.1) P ∧
    IsFadingMACPower q (fun s => f₂ s.2) P ∧ IsAdaptiveMAC h₁ h₂ f₁ f₂ R₁ R₂ ∧
    adaptiveSum q R₁ R₂ = v}

/-- **Lecture 8 of [elgamal2010], page 8-16.** The ergodic sum capacity with the gains at their
respective encoders and the decoder. -/
def macSumDSI (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ (f₁ : 𝒢₁ → ℝ) (f₂ : 𝒢₂ → ℝ), IsFadingMACPower q (fun s => f₁ s.1) P ∧
    IsFadingMACPower q (fun s => f₂ s.2) P ∧
    fadingMACSum q h₁ h₂ (fun s => f₁ s.1) (fun s => f₂ s.2) = v}

/-- **Lecture 8 of [elgamal2010], page 8-14.** The ergodic sum capacity with the gains at both
encoders and the decoder. -/
def macSumED (q : 𝒢₁ × 𝒢₂ → ℝ) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ φ₁ φ₂, IsFadingMACPower q φ₁ P ∧ IsFadingMACPower q φ₂ P ∧
    fadingMACSum q h₁ h₂ φ₁ φ₂ = v}

/-- The sum rates of `macSumED` are bounded above. -/
lemma bddAbove_macSumED (hq : ∀ s, 0 ≤ q s) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) :
    BddAbove {v | ∃ φ₁ φ₂, IsFadingMACPower q φ₁ P ∧ IsFadingMACPower q φ₂ P ∧
      fadingMACSum q h₁ h₂ φ₁ φ₂ = v} := by
  set K := (∑ g, h₁ g ^ 2) + ∑ g, h₂ g ^ 2
  have hK₁ : ∀ g, h₁ g ^ 2 ≤ K := fun g => by
    have a := single_le_sum (f := fun g => h₁ g ^ 2) (fun g _ => sq_nonneg _) (mem_univ g)
    have b : 0 ≤ ∑ g, h₂ g ^ 2 := sum_nonneg fun g _ => sq_nonneg _
    simp only [K]
    linarith
  have hK₂ : ∀ g, h₂ g ^ 2 ≤ K := fun g => by
    have a := single_le_sum (f := fun g => h₂ g ^ 2) (fun g _ => sq_nonneg _) (mem_univ g)
    have b : 0 ≤ ∑ g, h₁ g ^ 2 := sum_nonneg fun g _ => sq_nonneg _
    simp only [K]
    linarith
  have hK0 : 0 ≤ K := add_nonneg (sum_nonneg fun g _ => sq_nonneg _)
    (sum_nonneg fun g _ => sq_nonneg _)
  refine ⟨K / 2 * (P + P), ?_⟩
  rintro _ ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩
  have hs : ∀ s, q s * gaussCap (h₁ s.1 ^ 2 * φ₁ s + h₂ s.2 ^ 2 * φ₂ s) ≤
      K / 2 * (q s * φ₁ s + q s * φ₂ s) := fun s => by
    have a := mul_nonneg (sq_nonneg (h₁ s.1)) (hφ₁.1 s)
    have b := mul_nonneg (sq_nonneg (h₂ s.2)) (hφ₂.1 s)
    have c := gaussCap_le_half_self (add_nonneg a b)
    have d := mul_le_mul_of_nonneg_left c (hq s)
    refine d.trans ?_
    have e1 := mul_le_mul_of_nonneg_right (hK₁ s.1) (mul_nonneg (hq s) (hφ₁.1 s))
    have e2 := mul_le_mul_of_nonneg_right (hK₂ s.2) (mul_nonneg (hq s) (hφ₂.1 s))
    nlinarith
  calc fadingMACSum q h₁ h₂ φ₁ φ₂ ≤ ∑ s, K / 2 * (q s * φ₁ s + q s * φ₂ s) :=
        sum_le_sum fun s _ => hs s
    _ = K / 2 * (∑ s, q s * φ₁ s + ∑ s, q s * φ₂ s) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hφ₁.2 hφ₂.2) (by positivity)

/-- `sSup S ≤ sSup T` if every element of the nonempty `S` is below an element of `T`. -/
lemma csSup_le_csSup_of_forall {S T : Set ℝ} (hS : S.Nonempty) (hT : BddAbove T)
    (h : ∀ a ∈ S, ∃ b ∈ T, a ≤ b) : sSup S ≤ sSup T :=
  csSup_le hS fun a ha => by
    obtain ⟨b, hb, hab⟩ := h a ha
    exact hab.trans (le_csSup hT hb)

omit [Fintype 𝒢₁] [Fintype 𝒢₂] in
lemma isAdaptiveMAC_zero (hP : 0 ≤ P) :
    IsAdaptiveMAC h₁ h₂ (fun _ => P) (fun _ => P) (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun g => gaussCap_nonneg (mul_nonneg (sq_nonneg _) hP),
    fun g => gaussCap_nonneg (mul_nonneg (sq_nonneg _) hP), fun g₁ g₂ => ?_⟩
  rw [add_zero]
  exact gaussCap_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) hP) (mul_nonneg (sq_nonneg _) hP))

/-- `E(R₁(G₁) + R₂(G₂)) ≤ E C(G₁²φ₁ + G₂²φ₂)`. -/
lemma adaptiveSum_le (hq : ∀ s, 0 ≤ q s) {f₁ : 𝒢₁ → ℝ} {f₂ : 𝒢₂ → ℝ} {R₁ : 𝒢₁ → ℝ} {R₂ : 𝒢₂ → ℝ}
    (h : IsAdaptiveMAC h₁ h₂ f₁ f₂ R₁ R₂) :
    adaptiveSum q R₁ R₂ ≤ fadingMACSum q h₁ h₂ (fun s => f₁ s.1) fun s => f₂ s.2 :=
  sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h.2.2 s.1 s.2) (hq s)

/-- `macSumDSI` is bounded above. -/
lemma bddAbove_macSumDSI (hq : ∀ s, 0 ≤ q s) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) :
    BddAbove {v | ∃ (f₁ : 𝒢₁ → ℝ) (f₂ : 𝒢₂ → ℝ), IsFadingMACPower q (fun s => f₁ s.1) P ∧
      IsFadingMACPower q (fun s => f₂ s.2) P ∧
      fadingMACSum q h₁ h₂ (fun s => f₁ s.1) (fun s => f₂ s.2) = v} := by
  obtain ⟨K, hK⟩ := bddAbove_macSumED hq h₁ h₂ P
  exact ⟨K, fun _ ⟨f₁, f₂, a, b, hv⟩ => hK ⟨_, _, a, b, hv⟩⟩

/-- `macSumPA` is bounded above. -/
lemma bddAbove_macSumPA (hq : ∀ s, 0 ≤ q s) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) (P : ℝ) :
    BddAbove {v | ∃ f₁ f₂ R₁ R₂, IsFadingMACPower q (fun s => f₁ s.1) P ∧
      IsFadingMACPower q (fun s => f₂ s.2) P ∧ IsAdaptiveMAC h₁ h₂ f₁ f₂ R₁ R₂ ∧
      adaptiveSum q R₁ R₂ = v} := by
  obtain ⟨K, hK⟩ := bddAbove_macSumED hq h₁ h₂ P
  refine ⟨K, ?_⟩
  rintro _ ⟨f₁, f₂, R₁, R₂, a, b, hR, rfl⟩
  exact (adaptiveSum_le hq hR).trans (hK ⟨_, _, a, b, rfl⟩)

/-- `macSumA` is bounded above. -/
lemma bddAbove_macSumA (hq : IsPMF q) (hP : 0 ≤ P) (h₁ : 𝒢₁ → ℝ) (h₂ : 𝒢₂ → ℝ) :
    BddAbove {v | ∃ R₁ R₂, IsAdaptiveMAC h₁ h₂ (fun _ => P) (fun _ => P) R₁ R₂ ∧
      adaptiveSum q R₁ R₂ = v} := by
  obtain ⟨K, hK⟩ := bddAbove_macSumPA hq.nonneg h₁ h₂ P
  refine ⟨K, ?_⟩
  rintro _ ⟨R₁, R₂, hR, rfl⟩
  exact hK ⟨_, _, R₁, R₂, isFadingMACPower_const hq hP, isFadingMACPower_const hq hP, hR, rfl⟩

/-- **Lecture 8 of [elgamal2010], pages 8-22 and 8-23.** `C_C ≤ C_A`. -/
theorem macSumC_le_macSumA (hq : IsPMF q) (hP : 0 ≤ P) :
    macSumC q h₁ h₂ P ≤ macSumA q h₁ h₂ P := by
  refine csSup_le_csSup_of_forall ⟨_, 0, 0, isAdaptiveMAC_zero hP, rfl⟩
    (bddAbove_macSumA hq hP h₁ h₂) ?_
  rintro _ ⟨r₁, r₂, hR, rfl⟩
  exact ⟨_, ⟨_, _, hR, rfl⟩, le_rfl⟩

/-- **Lecture 8 of [elgamal2010], pages 8-22 and 8-23.** `C_A ≤ C_PA`. -/
theorem macSumA_le_macSumPA (hq : IsPMF q) (hP : 0 ≤ P) :
    macSumA q h₁ h₂ P ≤ macSumPA q h₁ h₂ P := by
  refine csSup_le_csSup_of_forall ⟨_, fun _ => 0, fun _ => 0, isAdaptiveMAC_zero hP, rfl⟩
    (bddAbove_macSumPA hq.nonneg h₁ h₂ P) ?_
  rintro _ ⟨R₁, R₂, hR, rfl⟩
  exact ⟨_, ⟨_, _, R₁, R₂, isFadingMACPower_const hq hP, isFadingMACPower_const hq hP, hR, rfl⟩,
    le_rfl⟩

/-- **Lecture 8 of [elgamal2010], pages 8-22 and 8-23.** `C_PA ≤ C_DSI-ED`. -/
theorem macSumPA_le_macSumDSI (hq : IsPMF q) (hP : 0 ≤ P) :
    macSumPA q h₁ h₂ P ≤ macSumDSI q h₁ h₂ P := by
  refine csSup_le_csSup_of_forall ⟨_, fun _ => P, fun _ => P, fun _ => 0, fun _ => 0,
    isFadingMACPower_const hq hP, isFadingMACPower_const hq hP, isAdaptiveMAC_zero hP, rfl⟩
    (bddAbove_macSumDSI hq.nonneg h₁ h₂ P) ?_
  rintro _ ⟨f₁, f₂, R₁, R₂, a, b, hR, rfl⟩
  exact ⟨_, ⟨f₁, f₂, a, b, rfl⟩, adaptiveSum_le hq.nonneg hR⟩

/-- **Lecture 8 of [elgamal2010], pages 8-22 and 8-23.** `C_DSI-ED ≤ C_SI-ED`. -/
theorem macSumDSI_le_macSumED (hq : IsPMF q) (hP : 0 ≤ P) :
    macSumDSI q h₁ h₂ P ≤ macSumED q h₁ h₂ P := by
  refine csSup_le_csSup_of_forall ⟨_, fun _ => P, fun _ => P, isFadingMACPower_const hq hP,
    isFadingMACPower_const hq hP, rfl⟩ (bddAbove_macSumED hq.nonneg h₁ h₂ P) ?_
  rintro _ ⟨f₁, f₂, a, b, rfl⟩
  exact ⟨_, ⟨_, _, a, b, rfl⟩, le_rfl⟩

end MAC

/-! ### The fading BC -/

section BC

variable {𝒢 : Type*} [Fintype 𝒢]

open Classical in
/-- The rate to receiver 1 with the split `a` in a state: it treats the signal for receiver 2 as
noise if `g₂ ≥ g₁`. -/
def fadingBCInfo₁ (g₁ g₂ P a : ℝ) : ℝ :=
  gaussCap (a * g₁ ^ 2 * P / (1 + (1 - a) * g₁ ^ 2 * P * if g₁ ≤ g₂ then 1 else 0))

open Classical in
/-- The rate to receiver 2 with the split `a` in a state: it treats the signal for receiver 1 as
noise if `g₂ < g₁`. -/
def fadingBCInfo₂ (g₁ g₂ P a : ℝ) : ℝ :=
  gaussCap ((1 - a) * g₂ ^ 2 * P / (1 + a * g₂ ^ 2 * P * if g₁ ≤ g₂ then 0 else 1))

/-- **Lecture 8 of [elgamal2010], page 8-25.** The region stated in the notes as the ergodic
capacity region of the BC with the gains at the encoder and the decoders: a fixed power split `α`.
-/ def fadingBCRegion (q g₁ g₂ : 𝒢 → ℝ) (P : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ a ∈ Set.Icc (0 : ℝ) 1, R.1 ≤ ∑ s, q s * fadingBCInfo₁ (g₁ s) (g₂ s) P a ∧
    R.2 ≤ ∑ s, q s * fadingBCInfo₂ (g₁ s) (g₂ s) P a}

/-- The same with a power split `α(g₁, g₂)` that depends on the state, which the encoder knows. -/
def fadingBCPolicyRegion (q g₁ g₂ : 𝒢 → ℝ) (P : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ a : 𝒢 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) 1) ∧
    R.1 ≤ ∑ s, q s * fadingBCInfo₁ (g₁ s) (g₂ s) P (a s) ∧
    R.2 ≤ ∑ s, q s * fadingBCInfo₂ (g₁ s) (g₂ s) P (a s)}

/-- A fixed split is a particular split depending on the state. -/
theorem fadingBCRegion_subset_policy (q g₁ g₂ : 𝒢 → ℝ) (P : ℝ) :
    fadingBCRegion q g₁ g₂ P ⊆ fadingBCPolicyRegion q g₁ g₂ P := by
  rintro R ⟨a, ha, h1, h2⟩
  exact ⟨fun _ => a, fun _ => ha, h1, h2⟩

/-- Two equally likely states, in which only one of the receivers has a nonzero gain `g`. -/
def alternatingQ : Bool → ℝ := fun _ => 1 / 2

/-- The gain of receiver 1 in the alternating states. -/
def alternating₁ (g : ℝ) : Bool → ℝ := fun s => if s then g else 0

/-- The gain of receiver 2 in the alternating states. -/
def alternating₂ (g : ℝ) : Bool → ℝ := fun s => if s then 0 else g

/-- **Lecture 8 of [elgamal2010], page 8-25.** With a split depending on the state, each receiver
gets all the power in its own state: the rate pair `(½ C(g²P), ½ C(g²P))`. -/
theorem half_mem_fadingBCPolicyRegion {g P : ℝ} (hg : 0 < g) :
    ((1 / 2 * gaussCap (g ^ 2 * P), 1 / 2 * gaussCap (g ^ 2 * P)) : ℝ × ℝ) ∈
      fadingBCPolicyRegion alternatingQ (alternating₁ g) (alternating₂ g) P := by
  refine ⟨fun s => if s then 1 else 0, fun s => by cases s <;> simp, ?_, ?_⟩
  · simp [alternatingQ, alternating₁, alternating₂, fadingBCInfo₁, hg.not_ge]
  · simp [alternatingQ, alternating₁, alternating₂, fadingBCInfo₂]

/-- **Lecture 8 of [elgamal2010], page 8-25.** With a fixed split `α` this rate pair is not in the
region of the notes: it would need `α = 1` and `α = 0`. So the region of the notes, with a fixed
`α`, is not the whole ergodic capacity region: the split, and the power, must depend on the state.
-/ theorem not_mem_fadingBCRegion_alternating {g P : ℝ} (hg : 0 < g) (hP : 0 < P) :
    ((1 / 2 * gaussCap (g ^ 2 * P), 1 / 2 * gaussCap (g ^ 2 * P)) : ℝ × ℝ) ∉
      fadingBCRegion alternatingQ (alternating₁ g) (alternating₂ g) P := by
  rintro ⟨a, ha, h1, h2⟩
  have hx : 0 < g ^ 2 * P := by positivity
  have e₁ : fadingBCInfo₁ g 0 P a = gaussCap (a * (g ^ 2 * P)) := by
    simp only [fadingBCInfo₁, hg.not_ge, ite_false, mul_zero, add_zero, div_one]
    congr 1
    ring
  have e₁' : fadingBCInfo₁ 0 g P a = 0 := by
    simp [fadingBCInfo₁]
  have e₂ : fadingBCInfo₂ 0 g P a = gaussCap ((1 - a) * (g ^ 2 * P)) := by
    simp only [fadingBCInfo₂, hg.le, ite_true, mul_zero, add_zero, div_one]
    congr 1
    ring
  have e₂' : fadingBCInfo₂ g 0 P a = 0 := by
    simp [fadingBCInfo₂]
  simp only [Fintype.sum_bool, alternatingQ, alternating₁, alternating₂, ite_true, ite_false,
    Bool.false_eq_true, e₁, e₁', e₂, e₂'] at h1 h2
  have ha1 : 1 ≤ a := by
    by_contra hlt
    have hlt' : a < 1 := not_le.1 hlt
    have := gaussCap_lt_gaussCap (mul_nonneg ha.1 hx.le)
      (show a * (g ^ 2 * P) < g ^ 2 * P by nlinarith)
    linarith
  have ha0 : a ≤ 0 := by
    by_contra hlt
    have hlt' : 0 < a := not_le.1 hlt
    have := gaussCap_lt_gaussCap (mul_nonneg (by linarith [ha.2] : 0 ≤ 1 - a) hx.le)
      (show (1 - a) * (g ^ 2 * P) < g ^ 2 * P by nlinarith)
    linarith
  linarith

/-- **Lecture 8 of [elgamal2010], page 8-25.** The compound region of the BC, with `x₁ = g₁*²`,
`x₂ = g₂*²` for the lowest gains. The notes print `g₁*`, `g₂*` without the squares. -/
def fadingBCCompoundRegion (x₁ x₂ P : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ a ∈ Set.Icc (0 : ℝ) 1, R.1 ≤ gaussCap (x₁ * a * P) ∧
    R.2 ≤ gaussCap (x₂ * (1 - a) * P / (1 + x₂ * a * P))}

/-- The end points of the compound region: all the power to one of the receivers. -/
theorem endpoints_mem_fadingBCCompoundRegion (x₁ x₂ P : ℝ) :
    ((gaussCap (x₁ * P), 0) : ℝ × ℝ) ∈ fadingBCCompoundRegion x₁ x₂ P ∧
      ((0, gaussCap (x₂ * P)) : ℝ × ℝ) ∈ fadingBCCompoundRegion x₁ x₂ P := by
  constructor
  · exact ⟨1, by simp, by simp, by simp⟩
  · exact ⟨0, by simp, by simp, by simp⟩

end BC

/-! ### The fading interference channel -/

section IC

/-- **Lecture 8 of [elgamal2010], page 8-27.** The sum rate of time division with power control,
`C(g²kP)`, with `x = g²P`. -/
def icTimeDivision (k : ℕ) (x : ℝ) : ℝ := gaussCap (k * x)

/-- **Lecture 8 of [elgamal2010], page 8-27.** The sum rate of treating the interference as Gaussian
noise, `k C(g²P/(g²(k - 1)P + 1))`, with `x = g²P`. -/
def icTreatAsNoise (k : ℕ) (x : ℝ) : ℝ := k * gaussCap (x / (x * (k - 1) + 1))

/-- **Lecture 8 of [elgamal2010], page 8-27.** The ergodic sum capacity with interference alignment,
`(k/2) C(2g²P)`, with `x = g²P`. -/
def icAlignment (k : ℕ) (x : ℝ) : ℝ := k / 2 * gaussCap (2 * x)

/-- **Lecture 8 of [elgamal2010], page 8-27.** Alignment beats time division: `C(kx) ≤ (k/2) C(2x)`
for `k ≥ 2`, by the concavity of the logarithm. -/
theorem icTimeDivision_le_icAlignment {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    icTimeDivision k x ≤ icAlignment k x := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB := one_add_mul_self_le_rpow_one_add (s := 2 * x) (p := k / 2) (by linarith) (by linarith)
  have h1 : 1 + (k : ℝ) * x = 1 + k / 2 * (2 * x) := by ring
  have hpos : 0 < 1 + (k : ℝ) * x := by positivity
  have h2 : log (1 + (k : ℝ) * x) ≤ k / 2 * log (1 + 2 * x) := by
    rw [← log_rpow (by linarith), h1]
    exact log_le_log (by rw [← h1]; exact hpos) hB
  simp only [icTimeDivision, icAlignment, gaussCap]
  nlinarith

/-- **Lecture 8 of [elgamal2010], page 8-27.** Alignment beats treating the interference as noise.
-/ theorem icTreatAsNoise_le_icAlignment {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    icTreatAsNoise k x ≤ icAlignment k x := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : 0 < 1 + x := by linarith
  have hd : 0 < x * (k - 1) + 1 := by nlinarith
  have h1 : x / (x * (k - 1) + 1) ≤ x / (1 + x) :=
    div_le_div_of_nonneg_left hx hx1 (by nlinarith)
  have h0 : 0 ≤ x / (x * (k - 1) + 1) := by positivity
  have h2 : gaussCap (x / (x * (k - 1) + 1)) ≤ gaussCap (x / (1 + x)) := gaussCap_le_gaussCap h0 h1
  have h3 : gaussCap (x / (1 + x)) ≤ 1 / 2 * gaussCap (2 * x) := by
    simp only [gaussCap]
    have e : 1 + x / (1 + x) = (1 + 2 * x) / (1 + x) := by
      field_simp
      ring
    rw [e]
    have p1 : 0 < (1 + 2 * x) / (1 + x) := by positivity
    have hsq : ((1 + 2 * x) / (1 + x)) ^ 2 ≤ 1 + 2 * x := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx]
    have := log_le_log (by positivity) hsq
    rw [log_pow] at this
    push_cast at this
    linarith
  rw [icTreatAsNoise, icAlignment]
  have hk0 : (0 : ℝ) ≤ k := by linarith
  calc (k : ℝ) * gaussCap (x / (x * (k - 1) + 1)) ≤ k * (1 / 2 * gaussCap (2 * x)) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hk0
    _ = _ := by ring

/-- **Lecture 8 of [elgamal2010], page 8-27.** With time division, the rate per user tends to `0`.
-/ theorem tendsto_icTimeDivision_div {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k : ℕ => icTimeDivision k x / k) atTop (𝓝 0) := by
  have hy : Tendsto (fun k : ℕ => 1 + (k : ℝ) * x) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hx)
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 / x) (-(1 / x)) 1
    (by positivity)).comp hy
  have h2 := h.const_mul (1 / 2)
  simp only [mul_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp, pow_one, icTimeDivision, gaussCap]
  have e : 1 / x * (1 + (k : ℝ) * x) + -(1 / x) = k := by
    field_simp
    ring
  rw [e]
  ring

/-- **Lecture 8 of [elgamal2010], page 8-27.** Treating the interference as noise, the rate per user
tends to `0`. -/
theorem tendsto_icTreatAsNoise_div {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k : ℕ => icTreatAsNoise k x / k) atTop (𝓝 0) := by
  have hd : Tendsto (fun k : ℕ => x * ((k : ℝ) - 1) + 1) atTop atTop := by
    refine tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop hx ?_)
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun k : ℕ => 1 + x / (x * ((k : ℝ) - 1) + 1)) atTop (𝓝 1) := by
    simpa using (hd.const_div_atTop x).const_add 1
  have hl := ((continuousAt_log one_ne_zero).tendsto.comp ht).const_mul (1 / 2)
  rw [log_one, mul_zero] at hl
  refine hl.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [Function.comp, icTreatAsNoise, gaussCap]
  field_simp

/-- **Lecture 8 of [elgamal2010], page 8-27.** The converse of ergodic interference alignment: if
`Rⱼ + Rⱼ' ≤ C` for every pair of users, then `∑ⱼ Rⱼ ≤ (k/2) C`. -/
theorem sum_le_of_pairwise {k : ℕ} (hk : 2 ≤ k) (R : Fin k → ℝ) {C : ℝ}
    (h : ∀ j j', j ≠ j' → R j + R j' ≤ C) : ∑ j, R j ≤ k / 2 * C := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hne : ∀ j : Fin (m + 2), j ≠ j + 1 := fun j hj => by
    have : (1 : Fin (m + 2)) = 0 := by
      have := left_eq_add.1 hj
      exact this
    simp at this
  have hshift : ∑ j : Fin (m + 2), R (j + 1) = ∑ j, R j :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 2))) R
  have hsum : ∑ j : Fin (m + 2), (R j + R (j + 1)) ≤ ∑ _j : Fin (m + 2), C :=
    sum_le_sum fun j _ => h j (j + 1) (hne j)
  rw [sum_add_distrib, hshift, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast at hsum ⊢
  linarith

/-! ### Conjugate channel gain matrices -/

variable {k : ℕ}

/-- **Lecture 8 of [elgamal2010], page 8-26.** A channel gain matrix, with `Gⱼⱼ' ∈ {-g, +g}`. -/
def gainMatrix (g : ℝ) (S : Fin k → Fin k → Bool) (j j' : Fin k) : ℝ := if S j j' then g else -g

/-- **Lecture 8 of [elgamal2010], page 8-28.** The conjugate matrix `Ḡ`: the off-diagonal signs are
flipped. -/
def conjSigns (S : Fin k → Fin k → Bool) : Fin k → Fin k → Bool :=
  fun j j' => if j = j' then S j j' else !S j j'

/-- The conjugate of the conjugate is the matrix. -/
theorem conjSigns_conjSigns (S : Fin k → Fin k → Bool) : conjSigns (conjSigns S) = S := by
  funext j j'
  by_cases h : j = j' <;> simp [conjSigns, h]

/-- For `k ≥ 2`, a matrix is not its own conjugate, so that the matrices come in pairs. -/
theorem conjSigns_ne (hk : 2 ≤ k) (S : Fin k → Fin k → Bool) : conjSigns S ≠ S := by
  intro h
  have h' := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
  simp [conjSigns] at h'

/-- **Lecture 8 of [elgamal2010], page 8-29.** `G + Ḡ` is diagonal: repeating each codeword in the
states `G` and `Ḡ` cancels the interference. -/
theorem gain_add_conj (g : ℝ) (S : Fin k → Fin k → Bool) (j j' : Fin k) :
    gainMatrix g S j j' + gainMatrix g (conjSigns S) j j' =
      if j = j' then 2 * gainMatrix g S j j' else 0 := by
  by_cases h : j = j'
  · simp only [h, ite_true, conjSigns, gainMatrix]
    ring
  · simp only [h, ite_false, conjSigns, gainMatrix]
    cases S j j' <;> simp

/-- **Lecture 8 of [elgamal2010], page 8-29.** The effective channel `Ỹ = (G + Ḡ)X + Z + Z̄` has
gain `2g` and noise power `2`: its signal-to-noise ratio is `(2g)²P/2 = 2g²P`. -/
theorem alignment_snr (g P : ℝ) : (2 * g) ^ 2 * P / 2 = 2 * (g ^ 2 * P) := by ring

/-- There are `2^{k²}` channel gain matrices. -/
theorem card_gainMatrices : Fintype.card (Fin k → Fin k → Bool) = 2 ^ (k * k) := by
  simp [← pow_mul]

end IC

end InfoTheory
