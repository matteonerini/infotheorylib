/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayLossy

/-!
# Two-way lossy source coding: the auxiliary variables of the converse

The identifications of pages 21-25 to 21-28 of El Gamal and Kim. The auxiliary letter of the round
`l` at the time `i` is `U_{li} = (i, X₁^{i-1}, X_{2,i+1}^n, M_l)`, so that all the rounds carry what
the notes put in the first one. The letters of a sequence that are hidden are replaced by `none`.

## Main definitions

* `maskLt t x`, `maskGe t x`: the letters of `x` before `t` and from `t` on.

## Main statements

* `KaspiCode.condMutualInfo_trans`, `KaspiCode.condMutualInfo_speak`: Lemma 1 for a code and a time.
* `condMutualInfo_mix_zero`: conditional independence survives uniform time sharing.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Masks -/

section Mask

variable {γ : Type*} {n : ℕ}

/-- The letters of `x` before `t`. -/
def maskLt (t : ℕ) (x : Fin n → γ) : Fin n → Option γ :=
  fun i => if (i : ℕ) < t then some (x i) else none

/-- The letters of `x` from `t` on. -/
def maskGe (t : ℕ) (x : Fin n → γ) : Fin n → Option γ :=
  fun i => if (i : ℕ) < t then none else some (x i)

/-- The sequence from its two parts. -/
def unmask (a₀ : γ) (m₁ m₂ : Fin n → Option γ) : Fin n → γ :=
  fun i => (m₁ i).getD ((m₂ i).getD a₀)

lemma unmask_mask (a₀ : γ) (t : ℕ) (x : Fin n → γ) : unmask a₀ (maskLt t x) (maskGe t x) = x := by
  funext i
  by_cases h : (i : ℕ) < t <;> simp [unmask, maskLt, maskGe, h]

lemma maskGe_apply_self {t : ℕ} {x : Fin n → γ} {i : Fin n} (h : t ≤ i) :
    maskGe t x i = some (x i) := by
  simp [maskGe, not_lt.2 h]

lemma maskLt_apply_self {t : ℕ} {x : Fin n → γ} {i : Fin n} (h : (i : ℕ) < t) :
    maskLt t x i = some (x i) := by
  simp [maskLt, h]

end Mask

/-! ### Lemma 1 for a code -/

section Code

universe u

variable {α₁ α₂ : Type u} {β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] {q : ℕ} {spk : Fin q → Bool}
  {M : Fin q → ℕ} [∀ l, NeZero (M l)] {n : ℕ} {P : α₁ × α₂ → ℝ}

namespace KaspiCode

variable (c : KaspiCode spk M n α₁ α₂ β₁ β₂)

/-- The history of the code before the round `r`. -/
def hist (ω : Fin n → α₁ × α₂) (r : ℕ) : ∀ l, Fin (M l) :=
  runTo (c.step (fstSeq ω) (sndSeq ω)) r

/-- The transcript of the code. -/
def tr (ω : Fin n → α₁ × α₂) : ∀ l, Fin (M l) := c.trans (fstSeq ω) (sndSeq ω)

omit [Fintype α₁] [Fintype α₂] in
lemma tr_apply (ω : Fin n → α₁ × α₂) (l : Fin q) :
    c.tr ω l = c.step (fstSeq ω) (sndSeq ω) l (c.hist ω l) :=
  run_apply _ l

omit [Fintype α₁] [Fintype α₂] [∀ (l : Fin q), NeZero (M l)] in
/-- The protocol of the code, in the terms of Lemma 1. -/
lemma lemProtocol_eq (a₀ : α₁) (b₀ : α₂) (t : ℕ) (ω : Fin n → α₁ × α₂) :
    lemProtocol spk (fun l w h => c.enc₁ l (unmask a₀ w.1 w.2) h)
      (fun l w h => c.enc₂ l (unmask b₀ w.1 w.2) h)
      (fun ω => maskLt t (fstSeq ω)) (fun ω => maskGe t (fstSeq ω))
      (fun ω => maskLt t (sndSeq ω)) (fun ω => maskGe t (sndSeq ω)) ω =
      c.step (fstSeq ω) (sndSeq ω) := by
  funext l h
  simp only [lemProtocol, step, unmask_mask]

/-- The start of Lemma 1 for a code: the letters before and after a time are independent. -/
lemma condMutualInfo_mask (hP : IsPMF P) (t : ℕ) :
    I[fun ω : Fin n → α₁ × α₂ => maskGe t (fstSeq ω) : fun ω => maskLt t (sndSeq ω) |
      pair (fun ω => maskLt t (fstSeq ω)) (fun ω => maskGe t (sndSeq ω)) ; iidPMF P n] = 0 := by
  refine condMutualInfo_of_indep (iidPMF_isPMF hP n) ?_
  refine mutualInfo_iid_split hP (fun i => (i : ℕ) < t) (fun ω ω' h => ?_) fun ω ω' h => ?_
  · refine Prod.ext ?_ ?_ <;> funext i
    · by_cases hi : (i : ℕ) < t
      · simp only [pair, maskLt, hi, ite_true, sndSeq, h i hi]
      · simp only [pair, maskLt, hi, ite_false]
    · by_cases hi : (i : ℕ) < t
      · simp only [pair, maskLt, hi, ite_true, fstSeq, h i hi]
      · simp only [pair, maskLt, hi, ite_false]
  · refine Prod.ext ?_ ?_ <;> funext i
    · by_cases hi : (i : ℕ) < t
      · simp only [pair, maskGe, hi, ite_true]
      · simp only [pair, maskGe, hi, ite_false, fstSeq, h i hi]
    · by_cases hi : (i : ℕ) < t
      · simp only [pair, maskGe, hi, ite_true]
      · simp only [pair, maskGe, hi, ite_false, sndSeq, h i hi]

/-- **Lemma 1 for a code.** `I(X₁^{≥t}; X₂^{<t} | M^q, X₁^{<t}, X₂^{≥t}) = 0`. -/
theorem condMutualInfo_trans (hP : IsPMF P) (a₀ : α₁) (b₀ : α₂) (t : ℕ) :
    I[fun ω : Fin n → α₁ × α₂ => maskGe t (fstSeq ω) : fun ω => maskLt t (sndSeq ω) |
      pair c.tr (pair (fun ω => maskLt t (fstSeq ω)) (fun ω => maskGe t (sndSeq ω))) ;
      iidPMF P n] = 0 := by
  have h := lemma1 (spk := spk) (g₁ := fun l w h => c.enc₁ l (unmask a₀ w.1 w.2) h)
    (g₂ := fun l w h => c.enc₂ l (unmask b₀ w.1 w.2) h) (iidPMF_isPMF hP n)
    (condMutualInfo_mask hP t) q le_rfl
  simp only [c.lemProtocol_eq a₀ b₀ t] at h
  exact h

/-- **Lemma 1 for a code.** The index of a round of node 1 gives no information on `X₂^{<t}`, and
the index of a round of node 2 gives no information on `X₁^{≥t}`. -/
theorem condMutualInfo_speak (hP : IsPMF P) (a₀ : α₁) (b₀ : α₂) (t : ℕ) (l : Fin q) :
    (spk l = true → I[fun ω : Fin n → α₁ × α₂ => maskLt t (sndSeq ω) : fun ω => c.tr ω l |
      pair (fun ω => c.hist ω l) (pair (fun ω => maskLt t (fstSeq ω))
        (fun ω => maskGe t (sndSeq ω))) ; iidPMF P n] = 0) ∧
    (spk l = false → I[fun ω : Fin n → α₁ × α₂ => maskGe t (fstSeq ω) : fun ω => c.tr ω l |
      pair (fun ω => c.hist ω l) (pair (fun ω => maskLt t (fstSeq ω))
        (fun ω => maskGe t (sndSeq ω))) ; iidPMF P n] = 0) := by
  have h := lemma1_speak (spk := spk) (g₁ := fun l w h => c.enc₁ l (unmask a₀ w.1 w.2) h)
    (g₂ := fun l w h => c.enc₂ l (unmask b₀ w.1 w.2) h) (iidPMF_isPMF hP n)
    (condMutualInfo_mask hP t) l
  simp only [c.lemProtocol_eq a₀ b₀ t] at h
  have e : ∀ ω : Fin n → α₁ × α₂, c.step (fstSeq ω) (sndSeq ω) l (runTo (c.step (fstSeq ω)
      (sndSeq ω)) l) = c.tr ω l := fun ω => (c.tr_apply ω l).symm
  simp only [e] at h
  exact h

end KaspiCode

end Code

/-! ### Time sharing -/

section Mix

variable {Ω ι a b κ : Type*} [Fintype Ω] [Fintype ι] [Fintype a] [Fintype b] [Fintype κ]
  [Nonempty ι] {μ : Ω → ℝ}

/-- **Conditional independence survives uniform time sharing**, if the time is known from the
conditioning variable. -/
theorem condMutualInfo_mix_zero (hμ : IsPMF μ) (A : Ω × ι → a) (B : Ω × ι → b) (C : Ω × ι → κ)
    (r : κ → ι) (hr : ∀ z, r (C z) = z.2)
    (h : ∀ i, I[fun ω => A (ω, i) : fun ω => B (ω, i) | fun ω => C (ω, i) ; μ] = 0) :
    I[A : B | C ; mixLaw μ ι] = 0 := by
  classical
  have hν : IsPMF (mixLaw μ ι) := mixLaw_isPMF hμ
  have e₁ : H[A | C ; mixLaw μ ι] = (Fintype.card ι : ℝ)⁻¹ * ∑ i, H[fun ω => A (ω, i) |
      fun ω => C (ω, i) ; μ] := by
    have := condEntropy_mix hμ (fun i ω => A (ω, i)) (b := fun _ : ι => κ) fun i ω => C (ω, i)
    rw [← this]
    refine condEntropy_eq_of_comp hν _ (fun c => (⟨r c, c⟩ : Σ _ : ι, κ)) (fun s => s.2) ?_ rfl
    funext z
    simp [hr]
  have e₂ : H[A | pair B C ; mixLaw μ ι] = (Fintype.card ι : ℝ)⁻¹ * ∑ i, H[fun ω => A (ω, i) |
      pair (fun ω => B (ω, i)) (fun ω => C (ω, i)) ; μ] := by
    have := condEntropy_mix hμ (fun i ω => A (ω, i)) (b := fun _ : ι => b × κ)
      fun i ω => pair (fun ω => B (ω, i)) (fun ω => C (ω, i)) ω
    rw [← this]
    refine condEntropy_eq_of_comp hν _ (fun c => (⟨r c.2, c⟩ : Σ _ : ι, b × κ)) (fun s => s.2) ?_
      rfl
    funext z
    simp [hr, pair]
  rw [condMutualInfo, e₁, e₂, ← mul_sub, ← sum_sub_distrib]
  rw [sum_eq_zero fun i _ => by
    have := h i
    rwa [condMutualInfo] at this, mul_zero]

end Mix

end InfoTheory
