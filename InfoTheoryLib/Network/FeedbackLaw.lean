/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCDegraded
public import InfoTheoryLib.Network.RelayCode

/-!
# Feedback laws: one use of the channel

The law of a code with feedback is a feedback law `fbLaw`. This file proves that the output at time
`i` is produced by the channel from any function of the message and of the past outputs that
determines the input at time `i`. This is the memoryless property used in all the converses of
Lecture 18.

## Main definitions

* `fbPre i z`: the outputs before time `i`.

## Main statements

* `dist_fbLaw_prefix`: the law of the first outputs.
* `dist_fbLaw_letter`: **the memoryless property**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒲 α β γ : Type*} [Fintype 𝒲] [Fintype β] {ν : 𝒲 → ℝ} {W : α → β → ℝ}
  {enc : ∀ k, 𝒲 → (Fin k → β) → α}

/-- The outputs before time `i`. -/
def fbPre {n : ℕ} (i : Fin n) (z : Fin n → β) : Fin i → β := fun t => z ⟨t, t.2.trans i.2⟩

/-- **The law of the first `m` outputs.** -/
lemma dist_fbLaw_prefix (hW : IsChannel W) (m : ℕ) : ∀ k (h : m ≤ k),
    dist (fbLaw ν W enc k) (fun z => (z.1, fun t : Fin m => z.2 ⟨t, lt_of_lt_of_le t.2 h⟩)) =
      fbLaw ν W enc m := by
  intro k h
  induction k, h using Nat.le_induction with
  | base =>
    have e : (fun z : 𝒲 × (Fin m → β) => (z.1, fun t : Fin m => z.2 ⟨t, lt_of_lt_of_le t.2 le_rfl⟩))
      = id := rfl
    rw [e, dist_id]
  | succ k hk ih =>
    have e : (fun z : 𝒲 × (Fin (k + 1) → β) =>
        (z.1, fun t : Fin m => z.2 ⟨t, lt_of_lt_of_le t.2 (hk.trans (Nat.le_succ k))⟩)) =
        (fun z : 𝒲 × (Fin k → β) => (z.1, fun t : Fin m => z.2 ⟨t, lt_of_lt_of_le t.2 hk⟩)) ∘
          fun z => (z.1, Fin.init z.2) := rfl
    rw [e, dist_comp_eq, dist_fbLaw_init hW k, ih]

/-- **The memoryless property.** Let `G₀` be a function of the message and of the past outputs that
determines the input at time `i`. Then the output at time `i` is produced by the channel from
`G₀`. -/
theorem dist_fbLaw_letter [Finite γ] (hW : IsChannel W) {n : ℕ} (i : Fin n)
    (G₀ : 𝒲 × (Fin i → β) → γ)
    (f : γ → α) (hf : ∀ w u, enc i w u = f (G₀ (w, u))) (c : γ) (b : β) :
    dist (fbLaw ν W enc n) (pair (fun z => G₀ (z.1, fbPre i z.2)) fun z => z.2 i) (c, b) =
      dist (fbLaw ν W enc n) (fun z => G₀ (z.1, fbPre i z.2)) c * W (f c) b := by
  have : Fintype γ := Fintype.ofFinite γ
  classical
  have hT := dist_fbLaw_prefix (ν := ν) (enc := enc) hW (i + 1) n i.2
  set T : 𝒲 × (Fin n → β) → 𝒲 × (Fin (i + 1) → β) := fun z =>
    (z.1, fun t : Fin (i + 1) => z.2 ⟨t, lt_of_lt_of_le t.2 i.2⟩) with hTd
  set μ := fbLaw ν W enc n with hμ
  -- the input is a function of the past and of the message
  let Q : 𝒲 × (Fin n → β) → (Fin i → β) × 𝒲 := fun z => (fbPre i z.2, z.1)
  have hA : ∀ (z : (Fin i → β) × 𝒲) (b : β), dist μ (pair Q fun z => z.2 i) (z, b) =
      dist μ Q z * W (enc i z.2 z.1) b := by
    intro z b
    have h := dist_fbLaw_chan (ν := ν) (enc := enc) hW (i : ℕ) z b
    have e₁ : (pair Q fun z : 𝒲 × (Fin n → β) => z.2 i) =
        (pair (pair (fun z : 𝒲 × (Fin (i + 1) → β) => Fin.init z.2) Prod.fst)
          fun z => z.2 (Fin.last i)) ∘ T := rfl
    have e₂ : Q = (pair (fun z : 𝒲 × (Fin (i + 1) → β) => Fin.init z.2) Prod.fst) ∘ T := rfl
    rw [e₁, dist_comp_eq, hT, e₂, dist_comp_eq, hT]
    exact h
  have e₃ : (fun z : 𝒲 × (Fin n → β) => G₀ (z.1, fbPre i z.2)) =
      (fun t : (Fin i → β) × 𝒲 => G₀ (t.2, t.1)) ∘ Q := rfl
  rw [e₃]
  exact dist_pair_comp_of_channel (ρ := fun t : (Fin i → β) × 𝒲 => enc i t.2 t.1) hA
    (fun t : (Fin i → β) × 𝒲 => G₀ (t.2, t.1)) f (fun t => (hf t.2 t.1).symm) c b

/-- The memoryless property, for a function of the output. -/
theorem dist_fbLaw_letter_view [Finite γ] {δ : Type*} (hW : IsChannel W) {n : ℕ}
    (i : Fin n) (G₀ : 𝒲 × (Fin i → β) → γ) (f : γ → α) (hf : ∀ w u, enc i w u = f (G₀ (w, u)))
    (v : β → δ) (c : γ) (d : δ) :
    dist (fbLaw ν W enc n) (pair (fun z => G₀ (z.1, fbPre i z.2)) fun z => v (z.2 i)) (c, d) =
      dist (fbLaw ν W enc n) (fun z => G₀ (z.1, fbPre i z.2)) c * dist (W (f c)) v d := by
  have : Fintype γ := Fintype.ofFinite γ
  classical
  have e : (pair (fun z : 𝒲 × (Fin n → β) => G₀ (z.1, fbPre i z.2)) fun z => v (z.2 i)) =
      (fun t : γ × β => (t.1, v t.2)) ∘
        pair (fun z : 𝒲 × (Fin n → β) => G₀ (z.1, fbPre i z.2)) fun z => z.2 i := rfl
  rw [e, dist_comp, Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  rw [sum_eq_single c]
  · have h₁ : ∀ b, dist (fbLaw ν W enc n) (fun z => G₀ (z.1, fbPre i z.2)) c *
        (if v b = d then W (f c) b else 0) = (if c = c ∧ v b = d then dist (fbLaw ν W enc n)
          (pair (fun z => G₀ (z.1, fbPre i z.2)) fun z => z.2 i) (c, b) else 0) := by
      intro b
      by_cases h : v b = d
      · rw [ite_eq_left h, ite_eq_left ⟨rfl, h⟩]
        exact (dist_fbLaw_letter hW i G₀ f hf c b).symm
      · rw [ite_eq_right h, ite_eq_right fun t => h t.2, mul_zero]
    have h₂ : dist (W (f c)) v d = ∑ b, if v b = d then W (f c) b else 0 := rfl
    rw [h₂, mul_sum]
    exact (sum_congr rfl fun b _ => h₁ b).symm
  · intro c' _ hc
    exact sum_eq_zero fun b _ => ite_eq_right fun h => absurd h.1 hc
  · simp

end InfoTheory
