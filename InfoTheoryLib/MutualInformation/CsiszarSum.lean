/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.MutualInformation.Conditional
public import InfoTheoryLib.Probability.RandomVector

/-!
# The Csiszár sum identity

For random sequences `Xⁿ`, `Yⁿ` and a random variable `U`,
`∑ᵢ I(X_{i+1}ⁿ; Yᵢ | Y^{i-1}, U) = ∑ᵢ I(Y^{i-1}; Xᵢ | X_{i+1}ⁿ, U)`.
The identity is used in many converse proofs of network information theory, for instance for
the broadcast channel with degraded message sets and for the wiretap channel. The proof
telescopes `Tᵢ = I(Y^i; X_{i+1}ⁿ | U)`: the differences `Tᵢ - T_{i-1}` are the differences of the
terms of the two sums, and `T₀ = Tₙ = 0`.

## Main definitions

* `suffixRV X i n`: the random vector `(Xᵢ, …, X_{n-1})`.

## Main statements

* `condMutualInfo_pair_sub_condMutualInfo_pair`: the identity behind one step of the telescoping
  sum, `I(A, B; D | U) - I(A; C, D | U) = I(D; B | A, U) - I(A; C | D, U)`.
* `csiszar_sum`: **the Csiszár sum identity**, and `csiszar_sum'` without `U`.

## Implementation notes

Families are indexed from `0`, as in `prefixRV`: the notes' `Y^{i-1} = (Y₁, …, Y_{i-1})` and
`X_{i+1}ⁿ = (X_{i+1}, …, Xₙ)` for `i = 1, …, n` are `prefixRV Y i = (Y₀, …, Y_{i-1})` and
`suffixRV X (i + 1) n = (X_{i+1}, …, X_{n-1})` for `i = 0, …, n - 1`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ ε : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [Fintype ε]

/-! ### Invariance and constants -/

/-- `I(X;Y|Z)` only depends on `X` up to injective relabelling. -/
lemma condMutualInfo_congr_left {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {X' : Ω → δ} (Y : Ω → β)
    (Z : Ω → γ) (f : α → δ) (hf : Function.Injective f) (h : ∀ ω, X' ω = f (X ω)) :
    I[X' : Y | Z ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo, condMutualInfo, condEntropy_congr_left hμ Z f hf h,
    condEntropy_congr_left hμ (pair Y Z) f hf h]

/-- `I(X;Y|Z)` only depends on `Y` up to injective relabelling. -/
lemma condMutualInfo_congr_mid {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) {Y : Ω → β} {Y' : Ω → δ}
    (Z : Ω → γ) (f : β → δ) (hf : Function.Injective f) (h : ∀ ω, Y' ω = f (Y ω)) :
    I[X : Y' | Z ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo, condMutualInfo, condEntropy_congr_right hμ X (X := pair Y Z)
    (X' := pair Y' Z) (Prod.map f id) (hf.prodMap Function.injective_id)
    fun ω => by simp [pair, h]]

/-- `I(c; Y|Z) = 0` for a constant `c`. -/
lemma condMutualInfo_const_left {μ : Ω → ℝ} (hμ : IsPMF μ) (c : α) (Y : Ω → β) (Z : Ω → γ) :
    I[(fun _ => c) : Y | Z ; μ] = 0 := by
  have h1 := condEntropy_le_entropy hμ (fun _ : Ω => c) Z
  have h2 := condEntropy_le_entropy hμ (fun _ : Ω => c) (pair Y Z)
  rw [entropyRV_const hμ] at h1 h2
  rw [condMutualInfo, le_antisymm h1 (condEntropy_nonneg hμ _ _),
    le_antisymm h2 (condEntropy_nonneg hμ _ _), sub_zero]

/-- `I(X; c|Z) = 0` for a constant `c`. -/
lemma condMutualInfo_const_mid {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (c : β) (Z : Ω → γ) :
    I[X : (fun _ => c) | Z ; μ] = 0 := by
  rw [condMutualInfo, condEntropy_congr_right hμ X (X := Z) (X' := pair (fun _ => c) Z)
    (fun z => (c, z)) (fun _ _ h => (Prod.mk.inj h).2) fun _ => rfl, sub_self]

/-! ### One step of the telescoping sum -/

/-- `I(A, B; D | U) - I(A; C, D | U) = I(D; B | A, U) - I(A; C | D, U)`. -/
theorem condMutualInfo_pair_sub_condMutualInfo_pair {μ : Ω → ℝ} (hμ : IsPMF μ) (A : Ω → α)
    (B : Ω → β) (C : Ω → γ) (D : Ω → δ) (U : Ω → ε) :
    I[pair A B : D | U ; μ] - I[A : pair C D | U ; μ] =
      I[D : B | pair A U ; μ] - I[A : C | pair D U ; μ] := by
  simp only [condMutualInfo_eq hμ]
  have e1 : H[pair U (pair A B) ; μ] = H[pair (pair A U) B ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (α × ε) × β => (t.1.2, (t.1.1, t.2)))
      (Function.LeftInverse.injective (g := fun s => ((s.2.1, s.1), s.2.2)) fun _ => rfl)
      fun _ => rfl
  have e2 : H[pair U D ; μ] = H[pair D U ; μ] := entropyRV_pair_comm μ U D
  have e3 : H[pair U (pair (pair A B) D) ; μ] = H[pair (pair A U) (pair D B) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (α × ε) × δ × β => (t.1.2, ((t.1.1, t.2.2), t.2.1)))
      (Function.LeftInverse.injective (g := fun s => ((s.2.1.1, s.1), (s.2.2, s.2.1.2)))
        fun _ => rfl) fun _ => rfl
  have e4 : H[pair U A ; μ] = H[pair A U ; μ] := entropyRV_pair_comm μ U A
  have e5 : H[pair U (pair C D) ; μ] = H[pair (pair D U) C ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (δ × ε) × γ => (t.1.2, (t.2, t.1.1)))
      (Function.LeftInverse.injective (g := fun s => ((s.2.2, s.1), s.2.1)) fun _ => rfl)
      fun _ => rfl
  have e6 : H[pair U (pair A (pair C D)) ; μ] = H[pair (pair D U) (pair A C) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (δ × ε) × α × γ => (t.1.2, (t.2.1, (t.2.2, t.1.1))))
      (Function.LeftInverse.injective (g := fun s => ((s.2.2.2, s.1), (s.2.1, s.2.2.1)))
        fun _ => rfl) fun _ => rfl
  have e7 : H[pair (pair A U) D ; μ] = H[pair (pair D U) A ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (δ × ε) × α => ((t.2, t.1.2), t.1.1))
      (Function.LeftInverse.injective (g := fun s => ((s.2, s.1.2), s.1.1)) fun _ => rfl)
      fun _ => rfl
  linarith

/-! ### Suffixes and the Csiszár sum identity -/

/-- The random vector `(Xᵢ, …, X_{n-1})` built from a sequence of random variables. -/
def suffixRV (X : ℕ → Ω → α) (i n : ℕ) : Ω → (Fin (n - i) → α) := fun ω j => X (i + j) ω

omit [Fintype Ω] [Fintype α] in
/-- `(Xᵢ, …, X_{n-1})` is `(Xᵢ, (X_{i+1}, …, X_{n-1}))`, through an injective map. -/
lemma suffixRV_eq_cons (X : ℕ → Ω → α) {i n : ℕ} (hi : i < n) :
    ∃ f : (Fin (n - i) → α) → α × (Fin (n - (i + 1)) → α), Function.Injective f ∧
      ∀ ω, (X i ω, suffixRV X (i + 1) n ω) = f (suffixRV X i n ω) := by
  refine ⟨fun v => (v ⟨0, by omega⟩, fun j => v ⟨j + 1, by omega⟩), fun v w h => ?_, fun ω => ?_⟩
  · simp only [Prod.mk.injEq] at h
    funext j
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · rw [show j = ⟨0, by omega⟩ from Fin.ext hj, h.1]
    · have := congrFun h.2 ⟨j - 1, by omega⟩
      simp only at this
      rwa [show (⟨j - 1 + 1, by omega⟩ : Fin (n - i)) = j from Fin.ext (by simp; omega)] at this
  · simp only [suffixRV, Prod.mk.injEq]
    refine ⟨by simp, funext fun j => ?_⟩
    simp only [suffixRV]
    congr 1
    omega

omit [Fintype Ω] [Fintype α] in
/-- The empty suffix `(Xₙ, …, X_{n-1})` is constant. -/
lemma suffixRV_self (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    suffixRV X n n ω = fun j => absurd j.isLt (by simp) := by
  funext j
  exact absurd j.isLt (by simp)

/-- **Csiszár sum identity (Lecture 2).** For random sequences `Xⁿ`, `Yⁿ` and a random
variable `U`, `∑ᵢ I(X_{i+1}ⁿ; Yᵢ | Y^{i-1}, U) = ∑ᵢ I(Y^{i-1}; Xᵢ | X_{i+1}ⁿ, U)`. -/
theorem csiszar_sum {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (Y : ℕ → Ω → β) (U : Ω → γ)
    (n : ℕ) :
    ∑ i ∈ range n, I[suffixRV X (i + 1) n : Y i | pair (prefixRV Y i) U ; μ] =
      ∑ i ∈ range n, I[prefixRV Y i : X i | pair (suffixRV X (i + 1) n) U ; μ] := by
  set T : ℕ → ℝ := fun i => I[prefixRV Y i : suffixRV X i n | U ; μ]
  have hstep : ∀ i ∈ range n, T (i + 1) - T i =
      I[suffixRV X (i + 1) n : Y i | pair (prefixRV Y i) U ; μ] -
        I[prefixRV Y i : X i | pair (suffixRV X (i + 1) n) U ; μ] := fun i hi => by
    obtain ⟨f, hf, hfX⟩ := suffixRV_eq_cons X (mem_range.1 hi)
    have h1 : T (i + 1) = I[pair (prefixRV Y i) (Y i) : suffixRV X (i + 1) n | U ; μ] :=
      condMutualInfo_congr_left hμ _ U _ (snoc_injective2 i) fun ω => prefixRV_succ Y i ω
    have h2 : T i = I[prefixRV Y i : pair (X i) (suffixRV X (i + 1) n) | U ; μ] :=
      (condMutualInfo_congr_mid hμ _ U f hf hfX).symm
    rw [h1, h2, condMutualInfo_pair_sub_condMutualInfo_pair hμ]
  have h0 : T 0 = 0 := by
    simp only [T, prefixRV_zero_eq]
    exact condMutualInfo_const_left hμ _ _ _
  have hn : T n = 0 := by
    simp only [T]
    rw [show suffixRV X n n = fun _ => fun j => absurd j.isLt (by simp) from
      funext (suffixRV_self X n)]
    exact condMutualInfo_const_mid hμ _ _ _
  have := sum_range_sub T n
  rw [sum_congr rfl hstep, hn, h0, sub_zero, sum_sub_distrib] at this
  linarith

/-- `I(X;Y|Z)` only depends on `Z` up to injective relabelling. -/
lemma condMutualInfo_congr_cond {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β) {Z : Ω → γ}
    {Z' : Ω → δ} (f : γ → δ) (hf : Function.Injective f) (h : ∀ ω, Z' ω = f (Z ω)) :
    I[X : Y | Z' ; μ] = I[X : Y | Z ; μ] := by
  rw [condMutualInfo, condMutualInfo, condEntropy_congr_right hμ X f hf h,
    condEntropy_congr_right hμ X (X := pair Y Z) (X' := pair Y Z') (Prod.map id f)
      (Function.injective_id.prodMap hf) fun ω => by simp [pair, h]]

/-- **Csiszár sum identity (Lecture 2)**, without the conditioning variable `U`, as stated in the
lecture notes: `∑ᵢ I(X_{i+1}ⁿ; Yᵢ | Y^{i-1}) = ∑ᵢ I(Y^{i-1}; Xᵢ | X_{i+1}ⁿ)`. -/
theorem csiszar_sum' {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ℕ → Ω → α) (Y : ℕ → Ω → β) (n : ℕ) :
    ∑ i ∈ range n, I[suffixRV X (i + 1) n : Y i | prefixRV Y i ; μ] =
      ∑ i ∈ range n, I[prefixRV Y i : X i | suffixRV X (i + 1) n ; μ] := by
  have h := csiszar_sum hμ X Y (fun _ => ()) n
  have e1 : ∀ i, I[suffixRV X (i + 1) n : Y i | pair (prefixRV Y i) (fun _ => ()) ; μ] =
      I[suffixRV X (i + 1) n : Y i | prefixRV Y i ; μ] := fun i =>
    condMutualInfo_congr_cond hμ _ _ (fun v => (v, ())) (fun _ _ h => (Prod.mk.inj h).1)
      fun _ => rfl
  have e2 : ∀ i, I[prefixRV Y i : X i | pair (suffixRV X (i + 1) n) (fun _ => ()) ; μ] =
      I[prefixRV Y i : X i | suffixRV X (i + 1) n ; μ] := fun i =>
    condMutualInfo_congr_cond hμ _ _ (fun v => (v, ())) (fun _ _ h => (Prod.mk.inj h).1)
      fun _ => rfl
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_congr rfl fun i _ => e2 i] at h
  exact h

end InfoTheory
