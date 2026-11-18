/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.Gaussian

/-!
# The AWGN multiple access channel with feedback: the formulas

Pages 18-28 to 18-30 of the notes. We state the two regions and prove the algebra around them; we do
not prove the coding theorems, which need continuous alphabets.

## Main definitions

* `macFBGaussRegion`: the region of Theorem 3, in nats.
* `clGaussRegion`: the Cover–Leung region for the AWGN multiple access channel, in nats.

## Main statements

* `clGaussRegion_subset`: the Cover–Leung region is inside the region of Theorem 3.
* `exists_rhoStar`: the correlation `ρ*` of the proof of Theorem 3, in the symmetric case, and the
  identity of page 18-34.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Set

@[expose] public noncomputable section

namespace InfoTheory

/-- **Theorem 3, page 18-29 of [elgamal2010].** The capacity region of the AWGN multiple access
channel with feedback, in nats. -/
def macFBGaussRegion (S₁ S₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ ρ ∈ Icc (0 : ℝ) 1, R.1 ≤ gaussCap ((1 - ρ ^ 2) * S₁) ∧ R.2 ≤ gaussCap ((1 - ρ ^ 2) * S₂) ∧
    R.1 + R.2 ≤ gaussCap (S₁ + S₂ + 2 * ρ * √(S₁ * S₂))}

/-- **Page 18-28 of [elgamal2010].** The Cover–Leung region for the AWGN multiple access channel, in
nats. -/
def clGaussRegion (S₁ S₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ α₁ ∈ Icc (0 : ℝ) 1, ∃ α₂ ∈ Icc (0 : ℝ) 1, R.1 ≤ gaussCap ((1 - α₁) * S₁) ∧
    R.2 ≤ gaussCap ((1 - α₂) * S₂) ∧ R.1 + R.2 ≤ gaussCap (S₁ + S₂ + 2 * √(α₁ * α₂ * S₁ * S₂))}

/-- The Cover–Leung region is inside the region of Theorem 3: take `ρ = √(α₁ α₂)`. -/
theorem clGaussRegion_subset {S₁ S₂ : ℝ} (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) :
    clGaussRegion S₁ S₂ ⊆ macFBGaussRegion S₁ S₂ := by
  rintro R ⟨α₁, ⟨h₁0, h₁1⟩, α₂, ⟨h₂0, h₂1⟩, r₁, r₂, r₃⟩
  have hprod : 0 ≤ α₁ * α₂ := mul_nonneg h₁0 h₂0
  have hsq : √(α₁ * α₂) ^ 2 = α₁ * α₂ := sq_sqrt hprod
  refine ⟨√(α₁ * α₂), ⟨sqrt_nonneg _, ?_⟩, ?_, ?_, ?_⟩
  · exact sqrt_le_one.mpr (by nlinarith)
  · refine r₁.trans (gaussCap_le_gaussCap (mul_nonneg (by linarith) h₁) ?_)
    rw [hsq]
    exact mul_le_mul_of_nonneg_right (by nlinarith) h₁
  · refine r₂.trans (gaussCap_le_gaussCap (mul_nonneg (by linarith) h₂) ?_)
    rw [hsq]
    exact mul_le_mul_of_nonneg_right (by nlinarith) h₂
  · refine r₃.trans (le_of_eq ?_)
    have e : α₁ * α₂ * S₁ * S₂ = (α₁ * α₂) * (S₁ * S₂) := by ring
    rw [e, sqrt_mul hprod]
    ring_nf

/-- **The correlation `ρ*`, page 18-30 of [elgamal2010], in the symmetric case**: it balances
`2 C((1 - ρ²) S) = C(2 (1 + ρ) S)`, and the identity
`C((1 + ρ)² S / ((1 - ρ²) S + 1)) = C((1 - ρ²) S)` of page 18-34 holds. -/
theorem exists_rhoStar {S : ℝ} (hS : 0 < S) :
    ∃ ρ ∈ Ioo (0 : ℝ) 1, 2 * gaussCap ((1 - ρ ^ 2) * S) = gaussCap (2 * (1 + ρ) * S) ∧
      gaussCap ((1 + ρ) ^ 2 * S / ((1 - ρ ^ 2) * S + 1)) = gaussCap ((1 - ρ ^ 2) * S) := by
  -- the equation `(1 + ρ) (1 - ρ)² S = 2 ρ`
  let f : ℝ → ℝ := fun ρ => (1 + ρ) * (1 - ρ) ^ 2 * S - 2 * ρ
  have hf : Continuous f := by
    fun_prop
  have h0 : 0 < f 0 := by
    simp [f, hS]
  have h1 : f 1 < 0 := by
    simp [f]
  obtain ⟨ρ, hρ, hfρ⟩ := intermediate_value_Ioo' (zero_le_one) hf.continuousOn
    (show (0 : ℝ) ∈ Ioo (f 1) (f 0) from ⟨h1, h0⟩)
  have hρ₀ := hρ.1
  have hρ₁ := hρ.2
  have heq : (1 + ρ) * (1 - ρ) ^ 2 * S = 2 * ρ := by
    have : (1 + ρ) * (1 - ρ) ^ 2 * S - 2 * ρ = 0 := hfρ
    linarith
  have hu : 0 < (1 - ρ ^ 2) * S := mul_pos (by nlinarith) hS
  refine ⟨ρ, hρ, ?_, ?_⟩
  · have hsq : (1 + (1 - ρ ^ 2) * S) ^ 2 = 1 + 2 * (1 + ρ) * S := by
      have e : (1 - ρ ^ 2) ^ 2 * S ^ 2 = 2 * ρ * (1 + ρ) * S := by
        calc (1 - ρ ^ 2) ^ 2 * S ^ 2 = (1 + ρ) * S * ((1 + ρ) * (1 - ρ) ^ 2 * S) := by ring
          _ = _ := by rw [heq]; ring
      nlinarith
    simp only [gaussCap]
    rw [← hsq, log_pow]
    push_cast
    ring
  · have hne : (1 - ρ ^ 2) * S + 1 ≠ 0 := by positivity
    have e : (1 + ρ) ^ 2 * S / ((1 - ρ ^ 2) * S + 1) = (1 - ρ ^ 2) * S := by
      rw [div_eq_iff hne]
      have : (1 - ρ ^ 2) * ((1 - ρ ^ 2) * S + 1) = (1 + ρ) ^ 2 := by
        have h₂ : (1 - ρ ^ 2) ^ 2 * S = 2 * ρ * (1 + ρ) := by
          calc (1 - ρ ^ 2) ^ 2 * S = (1 + ρ) * ((1 + ρ) * (1 - ρ) ^ 2 * S) := by ring
            _ = _ := by rw [heq]; ring
        nlinarith
      calc (1 + ρ) ^ 2 * S = (1 - ρ ^ 2) * ((1 - ρ ^ 2) * S + 1) * S := by rw [this]
        _ = _ := by ring
    rw [e]

end InfoTheory
