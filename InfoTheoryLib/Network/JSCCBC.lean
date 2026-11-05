/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.JSCCMAC

/-!
# Joint source–channel coding over a broadcast channel

This file defines the joint source–channel codes for sending a 2-DMS over a DM-BC, on page 15-19 of
Lecture 15 of El Gamal and Kim, and proves the bound of uncoded transmission over a deterministic
channel, which the notes use to show that source–channel separation fails.

## Main definitions

* `BCJSCCCode n α₁ α₂ ξ β₁ β₂`: the codes, and `BCJSCCCode.errProb`.
* `IsLosslessBC P W`: the sources can be sent losslessly.

## Main statements

* `isLosslessBC_of_uncoded`: uncoded transmission over a deterministic channel.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ ξ β₁ β₂ : Type*}

/-- **Lecture 15 of [elgamal2010], page 15-19.** A joint source–channel code of rate pair `(1, 1)`
  for a
2-DMS over a DM-BC. -/
structure BCJSCCCode (n : ℕ) (α₁ α₂ ξ β₁ β₂ : Type*) where
  /-- The encoder of the pair of sources. -/
  enc : (Fin n → α₁ × α₂) → Fin n → ξ
  /-- The first decoder. -/
  dec₁ : (Fin n → β₁) → Fin n → α₁
  /-- The second decoder. -/
  dec₂ : (Fin n → β₂) → Fin n → α₂

variable [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂] {n : ℕ}

open Classical in
/-- The probability of error of a code. -/
def BCJSCCCode.errProb (C : BCJSCCCode n α₁ α₂ ξ β₁ β₂) (P : α₁ × α₂ → ℝ)
    (W : ξ → β₁ × β₂ → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * ∑ y, channelExt W n (C.enc ω) y *
    (if C.dec₁ (fun i => (y i).1) = fstSeq ω ∧ C.dec₂ (fun i => (y i).2) = sndSeq ω then 0 else 1)

/-- **Lecture 15 of [elgamal2010], page 15-19.** The sources are transmitted losslessly over the
  DM-BC
if there is a sequence of codes with `P_e → 0`. -/
def IsLosslessBC (P : α₁ × α₂ → ℝ) (W : ξ → β₁ × β₂ → ℝ) : Prop :=
  ∃ C : ∀ n : ℕ, BCJSCCCode n α₁ α₂ ξ β₁ β₂, Tendsto (fun n => (C n).errProb P W) atTop (𝓝 0)

/-- **Lecture 15, page 15-29: uncoded transmission.** If the channel is deterministic with
`(Y₁, Y₂) = f(X)`, and `Uⱼ` can be recovered from `Yⱼ` for `X = e(U₁, U₂)` for every pair of
  positive
probability, then the sources can be sent losslessly, with no coding. -/
theorem isLosslessBC_of_uncoded [DecidableEq β₁] [DecidableEq β₂] {P : α₁ × α₂ → ℝ}
    {W : ξ → β₁ × β₂ → ℝ} {f : ξ → β₁ × β₂} (hW : ∀ x y, W x y = if f x = y then 1 else 0)
    (e : α₁ × α₂ → ξ) (d₁ : β₁ → α₁) (d₂ : β₂ → α₂)
    (hd : ∀ z, P z ≠ 0 → d₁ (f (e z)).1 = z.1 ∧ d₂ (f (e z)).2 = z.2) : IsLosslessBC P W := by
  classical
  refine ⟨fun n => ⟨fun ω i => e (ω i), fun y i => d₁ (y i), fun y i => d₂ (y i)⟩, ?_⟩
  have hzero : ∀ n : ℕ, (⟨fun ω i => e (ω i), fun y i => d₁ (y i), fun y i => d₂ (y i)⟩ :
      BCJSCCCode n α₁ α₂ ξ β₁ β₂).errProb P W = 0 := fun n => by
    refine sum_eq_zero fun ω _ => ?_
    by_cases hω : iidPMF P n ω = 0
    · rw [hω, zero_mul]
    have hne : ∀ i, P (ω i) ≠ 0 := fun i h0 => hω (prod_eq_zero (mem_univ i) h0)
    refine mul_eq_zero_of_right _ (sum_eq_zero fun y _ => ?_)
    by_cases hy : ∀ i, f (e (ω i)) = y i
    · have h1 : (fun i => d₁ (y i).1) = fstSeq ω := funext fun i => by
        rw [← hy i]
        exact (hd (ω i) (hne i)).1
      have h2 : (fun i => d₂ (y i).2) = sndSeq ω := funext fun i => by
        rw [← hy i]
        exact (hd (ω i) (hne i)).2
      simp only [h1, h2, and_self, ite_true, mul_zero]
    · push Not at hy
      obtain ⟨i, hi⟩ := hy
      refine mul_eq_zero_of_left (prod_eq_zero (mem_univ i) ?_) _
      rw [hW]
      exact ite_eq_right hi
  simp only [hzero]
  exact tendsto_const_nhds

end InfoTheory
