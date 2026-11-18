/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCCapacity

/-!
# Single-code bounds for the less noisy and more capable broadcast channels

The multi-letter part of the converses of Lecture 5 of El Gamal and Kim, for the DM-BC.

## Main definitions

* `moreCapableAux`: the auxiliary random variable `Vᵢ = (Y^{i-1}, Z_{i+1}ⁿ, A)`.
* `BCCode.moreCapableLetterLaw W c A i`: the law of `(Vᵢ, Xᵢ)`, for
  `Vᵢ = (Y₁^{i-1}, Y₂_{i+1}ⁿ, A(M₁, M₂))`.

## Main statements

* `condEntropy_sub_condEntropy_eq_sum_moreCapableAux`: the Csiszár sum identity in telescoped form,
  `H(Yⁿ | A) - H(Zⁿ | A) = ∑ᵢ (H(Yᵢ | Vᵢ) - H(Zᵢ | Vᵢ))`.
* `BCCode.log_le_sum_bcInfoUY₂_moreCapable`, `BCCode.log_add_log_le_sum_bcInfoXY₁U_add_bcInfoUY₂`,
  `BCCode.log_add_log_le_sum_bcInfoUY₁_add_bcInfoXY₂U`: the bounds for a single code (the fourth,
  `BCCode.log_add_log_le_sum_bcInfoXY₁`, is in `Network.BCMoreCapable`).

## Implementation notes

The notes bound the mutual information terms one by one and invoke the Csiszár sum identity. We use
the identity in telescoped form, along the hybrid sequences `(Y₁^k, Y₂_{k+1}ⁿ)`, so that the bounds
for a code are a few lines of entropy bookkeeping.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The telescoping identity -/

section Hybrid

/-- The outputs from time `k` on as a vector of fixed length: `y_k, …, y_{n-1}`, masked by `none` at
the earlier positions. It is the counterpart of `degradedBCPast`. -/
def moreCapableFuture {n : ℕ} {γ : Type*} (k : ℕ) (y : Fin n → γ) : Fin n → Option γ :=
  fun j => if k ≤ (j : ℕ) then some (y j) else none

variable {Ω γ₁ γ₂ δ : Type*} [Fintype Ω] [Fintype γ₁] [Fintype γ₂] [Fintype δ] {μ : Ω → ℝ} {n : ℕ}

/-- The auxiliary random variable `(Y^{i-1}, Z_{i+1}ⁿ, A)`, with `Y` and `Z` two sequences. -/
def moreCapableAux (Y : Ω → Fin n → γ₁) (Z : Ω → Fin n → γ₂) (A : Ω → δ) (i : ℕ) :
    Ω → ((Fin n → Option γ₁) × (Fin n → Option γ₂)) × δ :=
  fun ω => ((degradedBCPast i (Y ω), moreCapableFuture (i + 1) (Z ω)), A ω)

/-- **The Csiszár sum identity, telescoped.** For two random sequences `Yⁿ`, `Zⁿ` and a random
variable `A`, with `Vᵢ = (Y^{i-1}, Z_{i+1}ⁿ, A)`,
`H(Yⁿ | A) - H(Zⁿ | A) = ∑ᵢ (H(Yᵢ | Vᵢ) - H(Zᵢ | Vᵢ))`. The two sides telescope along the hybrid
sequences `(Y^k, Z_{k+1}ⁿ)`. -/
theorem condEntropy_sub_condEntropy_eq_sum_moreCapableAux (hμ : IsPMF μ) (Y : Ω → Fin n → γ₁)
    (Z : Ω → Fin n → γ₂) (A : Ω → δ) :
    H[Y | A ; μ] - H[Z | A ; μ] = ∑ i : Fin n,
      (H[fun ω => Y ω i | moreCapableAux Y Z A (i : ℕ) ; μ] -
        H[fun ω => Z ω i | moreCapableAux Y Z A (i : ℕ) ; μ]) := by
  classical
  set T : ℕ → Ω → (Fin n → Option γ₁) × (Fin n → Option γ₂) :=
    fun k ω => (degradedBCPast k (Y ω), moreCapableFuture k (Z ω)) with hT
  have step : ∀ (k : ℕ) (hk : k < n), H[T (k + 1) | A ; μ] - H[T k | A ; μ] =
      H[fun ω => Y ω ⟨k, hk⟩ | moreCapableAux Y Z A k ; μ] -
        H[fun ω => Z ω ⟨k, hk⟩ | moreCapableAux Y Z A k ; μ] := by
    intro k hk
    set C : Ω → (Fin n → Option γ₁) × (Fin n → Option γ₂) :=
      fun ω => (degradedBCPast k (Y ω), moreCapableFuture (k + 1) (Z ω)) with hC
    have e1 : H[T (k + 1) | A ; μ] = H[pair C (some ∘ fun ω => Y ω ⟨k, hk⟩) | A ; μ] := by
      refine degradedBC_condEntropy_eq_of_comp_eq hμ A
        (fun p => ((fun j : Fin n => if (j : ℕ) = k then p.2 else p.1.1 j), p.1.2))
        (fun p => (((fun j : Fin n => if (j : ℕ) < k then p.1 j else none), p.2), p.1 ⟨k, hk⟩))
        ?_ ?_
      · intro ω
        refine Prod.ext ?_ rfl
        funext j
        by_cases hj : (j : ℕ) = k
        · have : j = ⟨k, hk⟩ := Fin.ext hj
          subst this
          simp [hT, hC, pair, degradedBCPast]
        · by_cases hj' : (j : ℕ) < k
          · simp [hT, hC, pair, degradedBCPast, hj, hj', Nat.lt_succ_of_lt hj']
          · have : ¬ (j : ℕ) < k + 1 := by omega
            simp [hT, hC, pair, degradedBCPast, hj, hj', this]
      · intro ω
        refine Prod.ext (Prod.ext ?_ rfl) ?_
        · funext j
          by_cases hj' : (j : ℕ) < k
          · simp [hT, hC, pair, degradedBCPast, hj', Nat.lt_succ_of_lt hj']
          · simp [hC, pair, degradedBCPast, hj']
        · simp [hT, pair, degradedBCPast]
    have e2 : H[T k | A ; μ] = H[pair C (some ∘ fun ω => Z ω ⟨k, hk⟩) | A ; μ] := by
      refine degradedBC_condEntropy_eq_of_comp_eq hμ A
        (fun p => (p.1.1, (fun j : Fin n => if (j : ℕ) = k then p.2 else p.1.2 j)))
        (fun p => ((p.1, (fun j : Fin n => if k + 1 ≤ (j : ℕ) then p.2 j else none)), p.2 ⟨k, hk⟩))
        ?_ ?_
      · intro ω
        refine Prod.ext rfl ?_
        funext j
        by_cases hj : (j : ℕ) = k
        · have : j = ⟨k, hk⟩ := Fin.ext hj
          subst this
          simp [hT, hC, pair, moreCapableFuture]
        · by_cases hj' : k + 1 ≤ (j : ℕ)
          · have : k ≤ (j : ℕ) := by omega
            simp [hT, hC, pair, moreCapableFuture, hj, hj', this]
          · have : ¬ k ≤ (j : ℕ) := by omega
            simp [hT, hC, pair, moreCapableFuture, hj, hj', this]
      · intro ω
        refine Prod.ext (Prod.ext rfl ?_) ?_
        · funext j
          by_cases hj' : k + 1 ≤ (j : ℕ)
          · have : k ≤ (j : ℕ) := by omega
            simp [hT, hC, pair, moreCapableFuture, hj', this]
          · simp [hC, pair, moreCapableFuture, hj']
        · simp [hT, pair, moreCapableFuture]
    rw [e1, e2, chain_rule_cond hμ, chain_rule_cond hμ,
      condEntropy_comp_left_injective hμ _ _ (Option.some_injective γ₁),
      condEntropy_comp_left_injective hμ _ _ (Option.some_injective γ₂)]
    change _ - _ = H[fun ω => Y ω ⟨k, hk⟩ | pair C A ; μ] - H[fun ω => Z ω ⟨k, hk⟩ | pair C A ; μ]
    ring
  have hend : H[T n | A ; μ] = H[Y | A ; μ] :=
    condEntropy_congr_left hμ A
      (fun y : Fin n → γ₁ => ((fun j => some (y j)), fun _ => none))
      (fun a b h => funext fun j => Option.some_injective γ₁ (congrFun (Prod.mk.inj h).1 j))
      (fun ω => by
        refine Prod.ext ?_ ?_
        · funext j
          simp [hT, degradedBCPast]
        · funext j
          have : ¬ n ≤ (j : ℕ) := by omega
          simp [hT, moreCapableFuture, this])
  have hstart : H[T 0 | A ; μ] = H[Z | A ; μ] :=
    condEntropy_congr_left hμ A
      (fun z : Fin n → γ₂ => ((fun _ => none), fun j => some (z j)))
      (fun a b h => funext fun j => Option.some_injective γ₂ (congrFun (Prod.mk.inj h).2 j))
      (fun ω => by
        refine Prod.ext ?_ ?_
        · funext j
          simp [hT, degradedBCPast]
        · funext j
          simp [hT, moreCapableFuture])
  have hsum : ∀ i : Fin n,
      H[fun ω => Y ω i | moreCapableAux Y Z A (i : ℕ) ; μ] -
        H[fun ω => Z ω i | moreCapableAux Y Z A (i : ℕ) ; μ] =
        (fun k => H[T (k + 1) | A ; μ] - H[T k | A ; μ]) (i : ℕ) := fun i =>
    (step i i.isLt).symm
  rw [sum_congr rfl fun i _ => hsum i, Fin.sum_univ_eq_sum_range
    (fun k => H[T (k + 1) | A ; μ] - H[T k | A ; μ]) n, sum_range_sub (fun k => H[T k | A ; μ]) n,
    hend, hstart]

/-- **Chain rule along the past.** `H(Yⁿ | A) = ∑ᵢ H(Yᵢ | Y^{i-1}, A)`. -/
private lemma moreCapable_chain_past (hμ : IsPMF μ) (Y : Ω → Fin n → γ₁) (A : Ω → δ) :
    H[Y | A ; μ] =
      ∑ i : Fin n, H[fun ω => Y ω i | moreCapableAux Y (fun _ _ => ()) A (i : ℕ) ; μ] := by
  have h := condEntropy_sub_condEntropy_eq_sum_moreCapableAux hμ Y (fun _ _ => ()) A
  rw [condEntropy_comp_self hμ A (fun _ _ => ()), sub_zero] at h
  rw [h]
  refine sum_congr rfl fun i _ => ?_
  rw [condEntropy_comp_self hμ (moreCapableAux Y (fun _ _ => ()) A (i : ℕ)) (fun _ => ()), sub_zero]

/-- **Chain rule along the future.** `H(Zⁿ | A) = ∑ᵢ H(Zᵢ | Z_{i+1}ⁿ, A)`. -/
private lemma moreCapable_chain_future (hμ : IsPMF μ) (Z : Ω → Fin n → γ₂) (A : Ω → δ) :
    H[Z | A ; μ] =
      ∑ i : Fin n, H[fun ω => Z ω i | moreCapableAux (fun _ _ => ()) Z A (i : ℕ) ; μ] := by
  have h := condEntropy_sub_condEntropy_eq_sum_moreCapableAux hμ (fun _ _ => ()) Z A
  rw [condEntropy_comp_self hμ A (fun _ _ => ()), zero_sub] at h
  rw [← neg_inj, h, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [condEntropy_comp_self hμ (moreCapableAux (fun _ _ => ()) Z A (i : ℕ)) (fun _ => ()), zero_sub]

omit [Fintype γ₂] [Fintype δ] in
private lemma moreCapable_entropy_le_sum (hμ : IsPMF μ) (Y : Ω → Fin n → γ₁) :
    H[Y ; μ] ≤ ∑ i : Fin n, H[fun z => Y z i ; μ] := by
  have := condEntropy_pi_le_sum hμ Y (fun _ => ())
  simpa only [condEntropy_const hμ] using this

/-- **Fano's inequality**, as `H(A | C) ≤ I(A; Y | C) + log 2 + Pₑ log |𝓐|`. -/
private lemma moreCapable_fano_cond {M : ℕ} (hμ : IsPMF μ) (A : Ω → Fin M) (C : Ω → γ₂)
    (Y : Ω → γ₁) (g : γ₁ → Fin M) : H[A | C ; μ] ≤ H[Y | C ; μ] - H[Y | pair A C ; μ] + log 2 +
      InfoTheory.errProb μ A Y g * log M := by
  have h0 := condEntropy_le_condEntropy_comp hμ A (pair Y C) Prod.fst
  have h3 := fano_weak hμ A Y g
  rw [Fintype.card_fin] at h3
  have h1 : H[A | C ; μ] - H[A | pair Y C ; μ] = H[Y | C ; μ] - H[Y | pair A C ; μ] := by
    rw [← condMutualInfo, condMutualInfo_comm hμ, condMutualInfo]
  have h2 : H[A | pair Y C ; μ] ≤ H[A | Y ; μ] := h0
  linarith

/-- **Fano's inequality**, as `H(A) ≤ I(A; Y) + log 2 + Pₑ log |𝓐|`. -/
private lemma moreCapable_fano {M : ℕ} (hμ : IsPMF μ) (A : Ω → Fin M) (Y : Ω → γ₁)
    (g : γ₁ → Fin M) : H[A ; μ] ≤ H[Y ; μ] - H[Y | A ; μ] + log 2 +
      InfoTheory.errProb μ A Y g * log M := by
  have h3 := fano_weak hμ A Y g
  rw [Fintype.card_fin] at h3
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ A Y
  have hI' := mutualInfo_eq_entropy_sub_condEntropy' hμ A Y
  linarith

end Hybrid

/-! ### The memoryless channel -/

section Memoryless

/-- If `S` does not depend on the coordinate `i`, the sum `∑_y S(y) g(yᵢ)` only depends on
`∑_b g(b)`. -/
private lemma moreCapable_sum_mul_apply {β : Type*} [Fintype β] {n : ℕ} (i : Fin n)
    {S : (Fin n → β) → ℝ} (hS : ∀ y b, S (Function.update y i b) = S y) {g g' : β → ℝ}
    (h : ∑ b, g b = ∑ b, g' b) : ∑ y, S y * g (y i) = ∑ y, S y * g' (y i) := by
  classical
  set e := Equiv.funSplitAt i β
  have hi : ∀ b r, e.symm (b, r) i = b := fun b r => by simp [e, Equiv.funSplitAt]
  have key : ∀ g : β → ℝ, ∑ y, S y * g (y i) = ∑ b, ∑ r, S (e.symm (b, r)) * g b := fun g => by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [hi]
  have hT : ∀ b b' r, S (e.symm (b, r)) = S (e.symm (b', r)) := fun b b' r => by
    rw [← hS (e.symm (b', r)) b]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [hi]
    · rw [Function.update_of_ne hj]
      simp [e, Equiv.funSplitAt, hj]
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b₀⟩⟩
  · rw [key, key]; simp
  · rw [key, key]
    simp_rw [hT _ b₀, ← sum_mul]
    rw [← mul_sum, ← mul_sum, h]

variable {𝒲 α β γ : Type*} [Fintype 𝒲] [Fintype β] {ν : 𝒲 → ℝ} {W : α → β → ℝ} {n : ℕ}
  {x : 𝒲 → Fin n → α}

/-- **Memorylessness.** Given a function `G` of the message and of the outputs at the other times,
which determines the `i`-th input `xᵢ(W) = f(G)`, the `i`-th output is produced by the channel from
`f(G)`. -/
private lemma moreCapable_dist_letter (hW : IsChannel W) (i : Fin n)
    (G : 𝒲 × (Fin n → β) → γ) (hG : ∀ w y b, G (w, Function.update y i b) = G (w, y))
    (f : γ → α) (hf : ∀ z, x z.1 i = f (G z)) (c : γ) (b : β) :
    dist (codeLaw ν W x) (pair G (fun z => z.2 i)) (c, b) =
      dist (codeLaw ν W x) G c * W (f c) b := by
  classical
  have hR : ∀ w y, channelExt W n (x w) y =
      W (x w i) (y i) * ∏ j ∈ {i}ᶜ, W (x w j) (y j) := fun w y => by
    unfold channelExt
    rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [dist, Fintype.sum_prod_type, pair_apply, Prod.mk.injEq, codeLaw]
  rw [sum_mul]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_mul]
  set S : (Fin n → β) → ℝ := fun y =>
    if G (w, y) = c then ν w * ∏ j ∈ ({i}ᶜ : Finset (Fin n)), W (x w j) (y j) else 0 with hSdef
  have hS : ∀ y b', S (Function.update y i b') = S y := fun y b' => by
    simp only [hSdef, hG]
    congr 2
    refine prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (by simpa using hj)]
  have hL : ∀ y, (if G (w, y) = c ∧ y i = b then ν w * channelExt W n (x w) y else 0) =
      S y * (fun b' => W (x w i) b' * if b' = b then 1 else 0) (y i) := fun y => by
    simp only [hSdef, hR]
    by_cases h1 : G (w, y) = c <;> by_cases h2 : y i = b <;> simp [h1, h2]
    ring
  have hRR : ∀ y, (if G (w, y) = c then ν w * channelExt W n (x w) y else 0) * W (f c) b =
      S y * (fun b' => W (x w i) b' * W (x w i) b) (y i) := fun y => by
    simp only [hSdef, hR]
    by_cases h1 : G (w, y) = c
    · have : x w i = f c := by rw [← h1]; exact hf (w, y)
      simp only [h1, ↓reduceIte, this]
      ring
    · simp [h1]
  rw [sum_congr rfl fun y _ => hL y, sum_congr rfl fun y _ => hRR y]
  refine moreCapable_sum_mul_apply i hS (g := fun b' => W (x w i) b' * if b' = b then 1 else 0)
    (g' := fun b' => W (x w i) b' * W (x w i) b) ?_
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, ← sum_mul,
    (hW (x w i)).sum_eq_one, one_mul]

omit [Fintype 𝒲] [Fintype β] in
/-- The masked past of a function of the outputs does not depend on the present output. -/
private lemma moreCapable_past_update {β' : Type*} (φ : β → β') (i : Fin n) (y : Fin n → β)
    (b : β) :
    degradedBCPast (i : ℕ) (fun j => φ (Function.update y i b j)) =
      degradedBCPast (i : ℕ) (fun j => φ (y j)) := by
  funext j
  by_cases hj : (j : ℕ) < i
  · have hne : j ≠ i := fun h => by simp [h] at hj
    simp [degradedBCPast, hj, Function.update_of_ne hne]
  · simp [degradedBCPast, hj]

omit [Fintype 𝒲] [Fintype β] in
/-- The masked future of a function of the outputs does not depend on the present output. -/
private lemma moreCapable_future_update {β' : Type*} (φ : β → β') (i : Fin n) (y : Fin n → β)
    (b : β) :
    moreCapableFuture ((i : ℕ) + 1) (fun j => φ (Function.update y i b j)) =
      moreCapableFuture ((i : ℕ) + 1) (fun j => φ (y j)) := by
  funext j
  by_cases hj : (i : ℕ) + 1 ≤ j
  · have hne : j ≠ i := fun h => by simp [h] at hj
    simp [moreCapableFuture, hj, Function.update_of_ne hne]
  · simp [moreCapableFuture, hj]

end Memoryless

/-! ### The laws of the auxiliary random variables of a code -/

section Code

variable {α β₁ β₂ δ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] [Fintype δ] {M₁ M₂ n : ℕ}
  {W : α → β₁ × β₂ → ℝ}

/-- The outputs `Y₁ⁿ` of receiver 1. -/
abbrev moreCapableY₁ {𝒲 : Type*} : 𝒲 × (Fin n → β₁ × β₂) → Fin n → β₁ := fun z j => (z.2 j).1

/-- The outputs `Y₂ⁿ` of receiver 2. -/
abbrev moreCapableY₂ {𝒲 : Type*} : 𝒲 × (Fin n → β₁ × β₂) → Fin n → β₂ := fun z j => (z.2 j).2

/-- The auxiliary random variable `(Y₁^{i-1}, Y₂_{i+1}ⁿ, A(M₁, M₂))` of a code. The notes use
`A = M₂` for `Uᵢ` and `A = M₁` for `Vᵢ`. -/
abbrev moreCapableV (A : Fin M₁ × Fin M₂ → δ) (i : ℕ) :
    (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) →
      ((Fin n → Option β₁) × (Fin n → Option β₂)) × δ :=
  moreCapableAux moreCapableY₁ moreCapableY₂ (fun z => A z.1) i

/-- The law of `(Vᵢ, Xᵢ)` for a code, with the auxiliary random variable
`Vᵢ = (Y₁^{i-1}, Y₂_{i+1}ⁿ, A(M₁, M₂))`. -/
def BCCode.moreCapableLetterLaw (W : α → β₁ × β₂ → ℝ) (c : BCCode M₁ M₂ n α β₁ β₂)
    (A : Fin M₁ × Fin M₂ → δ) (i : Fin n) :
    (((Fin n → Option β₁) × (Fin n → Option β₂)) × δ) × α → ℝ :=
  dist (c.degradedJointLaw W) fun z => (moreCapableV A (i : ℕ) z, c.enc z.1 i)

/-- The conditional entropy `H(Y₁ᵢ | Xᵢ) = ∑ₓ p(xᵢ) H(Y₁ | X = x)`. -/
def BCCode.moreCapableH₁ (W : α → β₁ × β₂ → ℝ) (c : BCCode M₁ M₂ n α β₁ β₂) (i : Fin n) : ℝ :=
  ∑ x, dist (c.degradedJointLaw W) (fun z => c.enc z.1 i) x * entropy (bcMarg₁ W x)

/-- The conditional entropy `H(Y₂ᵢ | Xᵢ) = ∑ₓ p(xᵢ) H(Y₂ | X = x)`. -/
def BCCode.moreCapableH₂ (W : α → β₁ × β₂ → ℝ) (c : BCCode M₁ M₂ n α β₁ β₂) (i : Fin n) : ℝ :=
  ∑ x, dist (c.degradedJointLaw W) (fun z => c.enc z.1 i) x * entropy (bcMarg₂ W x)

variable (c : BCCode M₁ M₂ n α β₁ β₂)

omit [Fintype α] in
private lemma BCCode.moreCapableJointLaw_isPMF (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    IsPMF (c.degradedJointLaw W) :=
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  codeLaw_isPMF uniformPMF_isPMF hW

open Classical in
/-- If `G` determines the input `Xᵢ` and does not depend on the `i`-th output, then the output
`φ(Yᵢ)` with conditional law `T` has `H(φ(Yᵢ) | G) = ∑ₓ p(xᵢ) H(T(· | x))`. -/
private lemma BCCode.moreCapable_condEntropy_out {γ β' : Type*} [Fintype γ] [Fintype β']
    (φ : β₁ × β₂ → β') (T : α → β' → ℝ) (hT : ∀ x b, T x b = ∑ y, if φ y = b then W x y else 0)
    (hW : IsChannel W) (i : Fin n) (G : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → γ)
    (hG : ∀ w y b, G (w, Function.update y i b) = G (w, y)) (f : γ → α)
    (hf : ∀ z, c.enc z.1 i = f (G z)) :
    H[fun z => φ (z.2 i) | G ; c.degradedJointLaw W] =
      ∑ x, dist (c.degradedJointLaw W) (fun z => c.enc z.1 i) x * entropy (T x) := by
  classical
  have h := moreCapable_dist_letter (ν := uniformPMF (Fin M₁ × Fin M₂)) (x := c.enc) hW i G hG f hf
  have hch : ∀ g b, dist (c.degradedJointLaw W) (pair G fun z => φ (z.2 i)) (g, b) =
      dist (c.degradedJointLaw W) G g * T (f g) b := by
    intro g b
    have e1 : pair G (fun z => φ (z.2 i)) = Prod.map id φ ∘ pair G (fun z => z.2 i) := rfl
    rw [e1, dist_comp, Fintype.sum_prod_type, sum_eq_single g
      (fun g' _ hg' => sum_eq_zero fun y _ => by simp [hg']) (by simp), hT, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases hy : φ y = b
    · simpa [hy, BCCode.degradedJointLaw] using h g y
    · simp [hy]
  rw [condEntropy_of_channel f hch, show f ∘ G = fun z => c.enc z.1 i from
    funext fun z => (hf z).symm]

/-- `H(Y₁ᵢ | G) = H(Y₁ᵢ | Xᵢ)`, if `G` determines `Xᵢ` and does not depend on the `i`-th output. -/
private lemma BCCode.moreCapable_condEntropy₁ {γ : Type*} [Fintype γ] (hW : IsChannel W)
    (i : Fin n) (G : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → γ)
    (hG : ∀ w y b, G (w, Function.update y i b) = G (w, y)) (f : γ → α)
    (hf : ∀ z, c.enc z.1 i = f (G z)) :
    H[fun z => (z.2 i).1 | G ; c.degradedJointLaw W] = c.moreCapableH₁ W i :=
  c.moreCapable_condEntropy_out Prod.fst (bcMarg₁ W) (fun x b => by
    rw [Fintype.sum_prod_type, sum_eq_single b
      (fun b' _ hb' => sum_eq_zero fun y _ => by simp [hb']) (by simp)]
    simp [bcMarg₁]) hW i G hG f hf

/-- `H(Y₂ᵢ | G) = H(Y₂ᵢ | Xᵢ)`, if `G` determines `Xᵢ` and does not depend on the `i`-th output. -/
private lemma BCCode.moreCapable_condEntropy₂ {γ : Type*} [Fintype γ] (hW : IsChannel W)
    (i : Fin n) (G : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → γ)
    (hG : ∀ w y b, G (w, Function.update y i b) = G (w, y)) (f : γ → α)
    (hf : ∀ z, c.enc z.1 i = f (G z)) :
    H[fun z => (z.2 i).2 | G ; c.degradedJointLaw W] = c.moreCapableH₂ W i :=
  c.moreCapable_condEntropy_out Prod.snd (bcMarg₂ W) (fun x b => by
    rw [Fintype.sum_prod_type_right, sum_eq_single b
      (fun b' _ hb' => sum_eq_zero fun y _ => by simp [hb']) (by simp)]
    simp [bcMarg₂]) hW i G hG f hf

variable (A : Fin M₁ × Fin M₂ → δ)

omit [Fintype α] [Fintype β₁] [Fintype β₂] [Fintype δ] in
/-- `Vᵢ` does not depend on the outputs at time `i`. -/
private lemma moreCapableV_update (i : Fin n) (w : Fin M₁ × Fin M₂) (y : Fin n → β₁ × β₂)
    (b : β₁ × β₂) :
    moreCapableV (β₁ := β₁) (β₂ := β₂) A (i : ℕ) (w, Function.update y i b) =
      moreCapableV A (i : ℕ) (w, y) := by
  simp only [moreCapableV, moreCapableAux]
  rw [moreCapable_past_update Prod.fst i y b, moreCapable_future_update Prod.snd i y b]

omit [Fintype α] [Fintype δ] in
/-- The law of `((Vᵢ, Xᵢ), (Y₁ᵢ, Y₂ᵢ))` is `p(vᵢ, xᵢ) p(y₁, y₂ | xᵢ)`. -/
private lemma BCCode.dist_moreCapable_letter (hW : IsChannel W) (i : Fin n) :
    dist (c.degradedJointLaw W) (fun z => ((moreCapableV A (i : ℕ) z, c.enc z.1 i), z.2 i)) =
      bcJoint (c.moreCapableLetterLaw W A i) W := by
  funext s
  exact moreCapable_dist_letter hW i (fun z => (moreCapableV A (i : ℕ) z, c.enc z.1 i))
    (fun w y b => by simp only [moreCapableV_update]) Prod.snd (fun _ => rfl) s.1 s.2

lemma BCCode.moreCapableLetterLaw_isPMF (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (i : Fin n) : IsPMF (c.moreCapableLetterLaw W A i) :=
  (c.moreCapableJointLaw_isPMF hW h₁ h₂).dist _

/-- `I(Xᵢ; Y₁ᵢ | Vᵢ) = H(Y₁ᵢ | Vᵢ) - H(Y₁ᵢ | Xᵢ)`. -/
private lemma BCCode.moreCapable_bcInfoXY₁U (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (i : Fin n) : bcInfoXY₁U (c.moreCapableLetterLaw W A i) W =
      H[fun z => (z.2 i).1 | moreCapableV A (i : ℕ) ; c.degradedJointLaw W] -
        c.moreCapableH₁ W i := by
  have hμ := c.moreCapableJointLaw_isPMF hW h₁ h₂
  have e := condMutualInfo_comp hμ (fun z => ((moreCapableV A (i : ℕ) z, c.enc z.1 i), z.2 i))
    (fun t => t.1.2) (fun t => t.2.1) (fun t => t.1.1)
  rw [c.dist_moreCapable_letter A hW i] at e
  rw [bcInfoXY₁U, ← e, condMutualInfo_comm hμ, condMutualInfo]
  congr 1
  exact c.moreCapable_condEntropy₁ hW i (pair (fun z => c.enc z.1 i) (moreCapableV A (i : ℕ)))
    (fun w y b => by simp only [pair_apply, moreCapableV_update]) Prod.fst (fun _ => rfl)

/-- `I(Xᵢ; Y₂ᵢ | Vᵢ) = H(Y₂ᵢ | Vᵢ) - H(Y₂ᵢ | Xᵢ)`. -/
private lemma BCCode.moreCapable_bcInfoXY₂U (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (i : Fin n) : bcInfoXY₂U (c.moreCapableLetterLaw W A i) W =
      H[fun z => (z.2 i).2 | moreCapableV A (i : ℕ) ; c.degradedJointLaw W] -
        c.moreCapableH₂ W i := by
  have hμ := c.moreCapableJointLaw_isPMF hW h₁ h₂
  have e := condMutualInfo_comp hμ (fun z => ((moreCapableV A (i : ℕ) z, c.enc z.1 i), z.2 i))
    (fun t => t.1.2) (fun t => t.2.2) (fun t => t.1.1)
  rw [c.dist_moreCapable_letter A hW i] at e
  rw [bcInfoXY₂U, ← e, condMutualInfo_comm hμ, condMutualInfo]
  congr 1
  exact c.moreCapable_condEntropy₂ hW i (pair (fun z => c.enc z.1 i) (moreCapableV A (i : ℕ)))
    (fun w y b => by simp only [pair_apply, moreCapableV_update]) Prod.fst (fun _ => rfl)

/-- `I(Vᵢ; Y₂ᵢ) = H(Y₂ᵢ) - H(Y₂ᵢ | Vᵢ)`. -/
private lemma BCCode.moreCapable_bcInfoUY₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (i : Fin n) : bcInfoUY₂ (c.moreCapableLetterLaw W A i) W =
      H[fun z => (z.2 i).2 ; c.degradedJointLaw W] -
        H[fun z => (z.2 i).2 | moreCapableV A (i : ℕ) ; c.degradedJointLaw W] := by
  have hμ := c.moreCapableJointLaw_isPMF hW h₁ h₂
  have e := mutualInfo_comp (μ := c.degradedJointLaw W)
    (fun z => ((moreCapableV A (i : ℕ) z, c.enc z.1 i), z.2 i)) (fun t => t.1.1) (fun t => t.2.2)
  rw [c.dist_moreCapable_letter A hW i, mutualInfo_eq_entropy_sub_condEntropy' hμ] at e
  exact e.symm

/-- `I(Vᵢ; Y₁ᵢ) = H(Y₁ᵢ) - H(Y₁ᵢ | Vᵢ)`. -/
private lemma BCCode.moreCapable_bcInfoUY₁ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (i : Fin n) : bcInfoUY₁ (c.moreCapableLetterLaw W A i) W =
      H[fun z => (z.2 i).1 ; c.degradedJointLaw W] -
        H[fun z => (z.2 i).1 | moreCapableV A (i : ℕ) ; c.degradedJointLaw W] := by
  have hμ := c.moreCapableJointLaw_isPMF hW h₁ h₂
  have e := mutualInfo_comp (μ := c.degradedJointLaw W)
    (fun z => ((moreCapableV A (i : ℕ) z, c.enc z.1 i), z.2 i)) (fun t => t.1.1) (fun t => t.2.1)
  rw [c.dist_moreCapable_letter A hW i, mutualInfo_eq_entropy_sub_condEntropy' hμ] at e
  exact e.symm

/-- `I(Xᵢ; Y₁ᵢ) = H(Y₁ᵢ) - H(Y₁ᵢ | Xᵢ)`, whatever the auxiliary random variable. -/
lemma BCCode.moreCapable_bcInfoXY₁ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (i : Fin n) : bcInfoXY₁ (c.moreCapableLetterLaw W A i) W =
      H[fun z => (z.2 i).1 ; c.degradedJointLaw W] - c.moreCapableH₁ W i := by
  rw [bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U (c.moreCapableLetterLaw_isPMF A hW h₁ h₂ i) hW,
    c.moreCapable_bcInfoUY₁ A hW h₁ h₂ i, c.moreCapable_bcInfoXY₁U A hW h₁ h₂ i]
  ring

omit [Fintype α] [Fintype δ] in
private lemma BCCode.moreCapable_errProb :
    InfoTheory.errProb (c.degradedJointLaw W) (fun z => z.1.1) moreCapableY₁ c.dec₁ =
        c.errProb₁ W ∧
      InfoTheory.errProb (c.degradedJointLaw W) (fun z => z.1.2) moreCapableY₂ c.dec₂ =
        c.errProb₂ W := by
  classical
  constructor <;> first | rw [c.errProb₁_eq] | rw [c.errProb₂_eq]
  all_goals
    rw [InfoTheory.errProb, Fintype.sum_prod_type, sum_div]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    simp only [BCCode.degradedJointLaw, codeLaw, uniformPMF, Fintype.card_prod, Fintype.card_fin]
    push_cast
    split_ifs <;> ring

omit [Fintype α] [Fintype δ] in
private lemma BCCode.moreCapable_entropy (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    H[Prod.fst ; c.degradedJointLaw W] = log (M₁ * M₂) := by
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  have hd := dist_codeLaw_comp_fst (ν := uniformPMF (Fin M₁ × Fin M₂)) (x := c.enc) hW
    (id : Fin M₁ × Fin M₂ → Fin M₁ × Fin M₂)
  rw [dist_id] at hd
  rw [entropyRV, show (Prod.fst : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → _) = id ∘ Prod.fst
    from rfl, BCCode.degradedJointLaw, hd, entropy_uniformPMF, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  push_cast
  rfl

omit [Fintype α] [Fintype δ] in
private lemma BCCode.moreCapable_entropy_comp {M : ℕ} (hM : 0 < M) (hW : IsChannel W)
    (F : Fin M₁ × Fin M₂ → Fin M)
    (hF : dist (uniformPMF (Fin M₁ × Fin M₂)) F = uniformPMF (Fin M)) :
    H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => F z.1 ; c.degradedJointLaw W] = log M := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hd := dist_codeLaw_comp_fst (ν := uniformPMF (Fin M₁ × Fin M₂)) (x := c.enc) hW F
  rw [hF] at hd
  rw [entropyRV, show (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => F z.1) = F ∘ Prod.fst
    from rfl, BCCode.degradedJointLaw, hd, entropy_uniformPMF, Fintype.card_fin]

omit [Fintype α] [Fintype δ] in
private lemma BCCode.moreCapable_entropy₁ (hW : IsChannel W) (h₂ : 0 < M₂) (h₁ : 0 < M₁) :
    H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.1 ; c.degradedJointLaw W] = log M₁ :=
  c.moreCapable_entropy_comp h₁ hW (fun w => w.1) (by
    have := MACCode.dist_uniformPMF_prod_fst (M₁ := M₁) h₂ id
    rwa [dist_id] at this)

omit [Fintype α] [Fintype δ] in
private lemma BCCode.moreCapable_entropy₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2 ; c.degradedJointLaw W] = log M₂ :=
  c.moreCapable_entropy_comp h₂ hW (fun w => w.2) (by
    have := MACCode.dist_uniformPMF_prod_snd (M₂ := M₂) h₁ id
    rwa [dist_id] at this)

/-- `H(Y₁ⁿ | M₁, M₂) = ∑ᵢ H(Y₁ᵢ | Xᵢ)`. -/
private lemma BCCode.moreCapable_sum_H₁ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    ∑ i, c.moreCapableH₁ W i = H[moreCapableY₁ | Prod.fst ; c.degradedJointLaw W] := by
  rw [moreCapable_chain_past (c.moreCapableJointLaw_isPMF hW h₁ h₂)]
  refine sum_congr rfl fun i _ => (c.moreCapable_condEntropy₁ hW i _ (fun w y b => ?_)
    (fun g => c.enc g.2 i) fun _ => rfl).symm
  simp only [moreCapableAux]
  rw [moreCapable_past_update Prod.fst i y b]

/-- `H(Y₂ⁿ | M₁, M₂) = ∑ᵢ H(Y₂ᵢ | Xᵢ)`. -/
private lemma BCCode.moreCapable_sum_H₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    ∑ i, c.moreCapableH₂ W i = H[moreCapableY₂ | Prod.fst ; c.degradedJointLaw W] := by
  rw [moreCapable_chain_future (c.moreCapableJointLaw_isPMF hW h₁ h₂)]
  refine sum_congr rfl fun i _ => (c.moreCapable_condEntropy₂ hW i _ (fun w y b => ?_)
    (fun g => c.enc g.2 i) fun _ => rfl).symm
  simp only [moreCapableAux]
  rw [moreCapable_future_update Prod.snd i y b]

omit [Fintype α] in
/-- `∑ᵢ H(Y₂ᵢ | Vᵢ) ≤ H(Y₂ⁿ | A)`: the chain rule along the future outputs, and conditioning on
the past outputs of receiver 1 reduces entropy. -/
private lemma BCCode.moreCapable_sum_condEntropy_le (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    ∑ i : Fin n, H[fun z => (z.2 i).2 | moreCapableV A (i : ℕ) ; c.degradedJointLaw W] ≤
      H[moreCapableY₂ | fun z => A z.1 ; c.degradedJointLaw W] := by
  have hμ := c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂
  rw [moreCapable_chain_future hμ]
  refine sum_le_sum fun i _ => (condEntropy_le_condEntropy_comp hμ
    (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => (z.2 i).2) (moreCapableV A (i : ℕ))
    (fun p => ((degradedBCPast (i : ℕ) (fun _ : Fin n => ()), p.1.2), p.2))).trans (le_of_eq ?_)
  congr 1

omit [Fintype α] [Fintype δ] in
/-- Receiver 1, Fano: `log |𝓜₁| ≤ I(M₁; Y₁ⁿ | M₂) + log 2 + P₁ log |𝓜₁|`. -/
private lemma BCCode.moreCapable_fano₁_cond (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₁ ≤ H[moreCapableY₁ | fun z => z.1.2 ; c.degradedJointLaw W] -
      H[moreCapableY₁ | Prod.fst ; c.degradedJointLaw W] + log 2 + c.errProb₁ W * log M₁ := by
  have hμ := c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂
  have hH : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.1 | fun z => z.1.2 ;
      c.degradedJointLaw W] = log M₁ := by
    have e : H[pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2) (fun z => z.1.1) ;
        c.degradedJointLaw W] = H[Prod.fst ; c.degradedJointLaw W] :=
      entropyRV_eq_of_injective _ Prod.swap Prod.swap_injective fun _ => rfl
    rw [condEntropy_eq_sub hμ, e, c.moreCapable_entropy hW h₁ h₂, c.moreCapable_entropy₂ hW h₁ h₂,
      log_mul (by exact_mod_cast h₁.ne') (by exact_mod_cast h₂.ne')]
    ring
  have h := moreCapable_fano_cond hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.1)
    (fun z => z.1.2) moreCapableY₁ c.dec₁
  rw [hH, c.moreCapable_errProb.1] at h
  exact h

omit [Fintype α] [Fintype δ] in
/-- Receiver 2, Fano: `log |𝓜₂| ≤ I(M₂; Y₂ⁿ | M₁) + log 2 + P₂ log |𝓜₂|`. -/
private lemma BCCode.moreCapable_fano₂_cond (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₂ ≤ H[moreCapableY₂ | fun z => z.1.1 ; c.degradedJointLaw W] -
      H[moreCapableY₂ | Prod.fst ; c.degradedJointLaw W] + log 2 + c.errProb₂ W * log M₂ := by
  have hμ := c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂
  have hH : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2 | fun z => z.1.1 ;
      c.degradedJointLaw W] = log M₂ := by
    have e : H[pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.1) (fun z => z.1.2) ;
        c.degradedJointLaw W] = log (M₁ * M₂) := c.moreCapable_entropy hW h₁ h₂
    rw [condEntropy_eq_sub hμ, e, c.moreCapable_entropy₁ hW h₂ h₁,
      log_mul (by exact_mod_cast h₁.ne') (by exact_mod_cast h₂.ne')]
    ring
  have h := moreCapable_fano_cond hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2)
    (fun z => z.1.1) moreCapableY₂ c.dec₂
  rw [hH, c.moreCapable_errProb.2, show H[moreCapableY₂ | pair (fun z => z.1.2) (fun z => z.1.1) ;
    c.degradedJointLaw W] = H[moreCapableY₂ | Prod.fst ; c.degradedJointLaw W] from
    condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl] at h
  exact h

omit [Fintype α] [Fintype δ] in
/-- Receiver 1, Fano: `log |𝓜₁| ≤ I(M₁; Y₁ⁿ) + log 2 + P₁ log |𝓜₁|`. -/
private lemma BCCode.moreCapable_fano₁ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₁ ≤ H[moreCapableY₁ ; c.degradedJointLaw W] -
      H[moreCapableY₁ | fun z => z.1.1 ; c.degradedJointLaw W] + log 2 +
        c.errProb₁ W * log M₁ := by
  have h := moreCapable_fano (c.moreCapableJointLaw_isPMF hW h₁ h₂)
    (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.1) moreCapableY₁ c.dec₁
  rwa [c.moreCapable_entropy₁ hW h₂ h₁, c.moreCapable_errProb.1] at h

omit [Fintype α] [Fintype δ] in
/-- Receiver 2, Fano: `log |𝓜₂| ≤ I(M₂; Y₂ⁿ) + log 2 + P₂ log |𝓜₂|`. -/
private lemma BCCode.moreCapable_fano₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₂ ≤ H[moreCapableY₂ ; c.degradedJointLaw W] -
      H[moreCapableY₂ | fun z => z.1.2 ; c.degradedJointLaw W] + log 2 +
        c.errProb₂ W * log M₂ := by
  have h := moreCapable_fano (c.moreCapableJointLaw_isPMF hW h₁ h₂)
    (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2) moreCapableY₂ c.dec₂
  rwa [c.moreCapable_entropy₂ hW h₁ h₂, c.moreCapable_errProb.2] at h

/-- **Lecture 5 of [elgamal2010], page 5-43 (first inequality).** With `Uᵢ = (M₂, Y₁^{i-1},
Y₂_{i+1}ⁿ)`, `log |𝓜₂| ≤ ∑ᵢ I(Uᵢ; Y₂ᵢ) + log 2 + P₂ log |𝓜₂|`. -/
theorem BCCode.log_le_sum_bcInfoUY₂_moreCapable (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₂ ≤ ∑ i, bcInfoUY₂ (c.moreCapableLetterLaw W (fun w => w.2) i) W + log 2 +
      c.errProb₂ W * log M₂ := by
  have hF := c.moreCapable_fano₂ (W := W) hW h₁ h₂
  have hY := moreCapable_entropy_le_sum (c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂)
    (moreCapableY₂ (n := n) (β₁ := β₁) (β₂ := β₂) (𝒲 := Fin M₁ × Fin M₂))
  have hle := c.moreCapable_sum_condEntropy_le (W := W) (fun w => w.2) hW h₁ h₂
  have hsum : ∑ i, bcInfoUY₂ (c.moreCapableLetterLaw W (fun w => w.2) i) W =
      ∑ i : Fin n, H[fun z => (z.2 i).2 ; c.degradedJointLaw W] -
        ∑ i : Fin n, H[fun z => (z.2 i).2 | moreCapableV (fun w => w.2) (i : ℕ) ;
          c.degradedJointLaw W] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => c.moreCapable_bcInfoUY₂ _ hW h₁ h₂ i
  linarith

/-- **Lecture 5 of [elgamal2010], pages 5-42 and 5-43 (second inequality).** With
`Uᵢ = (M₂, Y₁^{i-1}, Y₂_{i+1}ⁿ)`, `log |𝓜₁| + log |𝓜₂|` is at most
`∑ᵢ (I(Xᵢ; Y₁ᵢ | Uᵢ) + I(Uᵢ; Y₂ᵢ)) + 2 log 2 + P₁ log |𝓜₁| + P₂ log |𝓜₂|`. -/
theorem BCCode.log_add_log_le_sum_bcInfoXY₁U_add_bcInfoUY₂ (hW : IsChannel W) (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) :
    log M₁ + log M₂ ≤ ∑ i, (bcInfoXY₁U (c.moreCapableLetterLaw W (fun w => w.2) i) W +
      bcInfoUY₂ (c.moreCapableLetterLaw W (fun w => w.2) i) W) + 2 * log 2 +
        c.errProb₁ W * log M₁ + c.errProb₂ W * log M₂ := by
  have hμ := c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂
  have hF₁ := c.moreCapable_fano₁_cond (W := W) hW h₁ h₂
  have hF₂ := c.moreCapable_fano₂ (W := W) hW h₁ h₂
  have hY := moreCapable_entropy_le_sum (c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂)
    (moreCapableY₂ (n := n) (β₁ := β₁) (β₂ := β₂) (𝒲 := Fin M₁ × Fin M₂))
  have hC := condEntropy_sub_condEntropy_eq_sum_moreCapableAux hμ moreCapableY₁ moreCapableY₂
    (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2)
  have hH := c.moreCapable_sum_H₁ (W := W) hW h₁ h₂
  have hsum : ∑ i, (bcInfoXY₁U (c.moreCapableLetterLaw W (fun w => w.2) i) W +
      bcInfoUY₂ (c.moreCapableLetterLaw W (fun w => w.2) i) W) =
      ∑ i : Fin n, (H[fun z => (z.2 i).1 | moreCapableV (fun w => w.2) (i : ℕ) ;
          c.degradedJointLaw W] -
        H[fun z => (z.2 i).2 | moreCapableV (fun w => w.2) (i : ℕ) ; c.degradedJointLaw W]) -
        ∑ i, c.moreCapableH₁ W i + ∑ i : Fin n, H[fun z => (z.2 i).2 ; c.degradedJointLaw W] := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [c.moreCapable_bcInfoXY₁U _ hW h₁ h₂ i, c.moreCapable_bcInfoUY₂ _ hW h₁ h₂ i]
    ring
  have hC' : H[moreCapableY₁ | fun z => z.1.2 ; c.degradedJointLaw W] -
      H[moreCapableY₂ | fun z => z.1.2 ; c.degradedJointLaw W] =
      ∑ i : Fin n, (H[fun z => (z.2 i).1 | moreCapableV (fun w => w.2) (i : ℕ) ;
          c.degradedJointLaw W] -
        H[fun z => (z.2 i).2 | moreCapableV (fun w => w.2) (i : ℕ) ; c.degradedJointLaw W]) := hC
  linarith

/-- **Lecture 5 of [elgamal2010], page 5-44 (third inequality).** With
`Vᵢ = (M₁, Y₁^{i-1}, Y₂_{i+1}ⁿ)`, `log |𝓜₁| + log |𝓜₂|` is at most
`∑ᵢ (I(Vᵢ; Y₁ᵢ) + I(Xᵢ; Y₂ᵢ | Vᵢ)) + 2 log 2 + P₁ log |𝓜₁| + P₂ log |𝓜₂|`. -/
theorem BCCode.log_add_log_le_sum_bcInfoUY₁_add_bcInfoXY₂U (hW : IsChannel W) (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) :
    log M₁ + log M₂ ≤ ∑ i, (bcInfoUY₁ (c.moreCapableLetterLaw W (fun w => w.1) i) W +
      bcInfoXY₂U (c.moreCapableLetterLaw W (fun w => w.1) i) W) + 2 * log 2 +
        c.errProb₁ W * log M₁ + c.errProb₂ W * log M₂ := by
  have hμ := c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂
  have hF₁ := c.moreCapable_fano₁ (W := W) hW h₁ h₂
  have hF₂ := c.moreCapable_fano₂_cond (W := W) hW h₁ h₂
  have hY := moreCapable_entropy_le_sum (c.moreCapableJointLaw_isPMF (W := W) hW h₁ h₂)
    (moreCapableY₁ (n := n) (β₁ := β₁) (β₂ := β₂) (𝒲 := Fin M₁ × Fin M₂))
  have hC := condEntropy_sub_condEntropy_eq_sum_moreCapableAux hμ moreCapableY₁ moreCapableY₂
    (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.1)
  have hH := c.moreCapable_sum_H₂ (W := W) hW h₁ h₂
  have hsum : ∑ i, (bcInfoUY₁ (c.moreCapableLetterLaw W (fun w => w.1) i) W +
      bcInfoXY₂U (c.moreCapableLetterLaw W (fun w => w.1) i) W) =
      ∑ i : Fin n, H[fun z => (z.2 i).1 ; c.degradedJointLaw W] -
        ∑ i : Fin n, (H[fun z => (z.2 i).1 | moreCapableV (fun w => w.1) (i : ℕ) ;
          c.degradedJointLaw W] -
        H[fun z => (z.2 i).2 | moreCapableV (fun w => w.1) (i : ℕ) ; c.degradedJointLaw W]) -
        ∑ i, c.moreCapableH₂ W i := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [c.moreCapable_bcInfoUY₁ _ hW h₁ h₂ i, c.moreCapable_bcInfoXY₂U _ hW h₁ h₂ i]
    ring
  have hC' : H[moreCapableY₁ | fun z => z.1.1 ; c.degradedJointLaw W] -
      H[moreCapableY₂ | fun z => z.1.1 ; c.degradedJointLaw W] =
      ∑ i : Fin n, (H[fun z => (z.2 i).1 | moreCapableV (fun w => w.1) (i : ℕ) ;
          c.degradedJointLaw W] -
        H[fun z => (z.2 i).2 | moreCapableV (fun w => w.1) (i : ℕ) ; c.degradedJointLaw W]) := hC
  linarith

end Code

end InfoTheory
