/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCDegradedLaws
public import InfoTheoryLib.Network.BCTimeSharing

/-!
# The degraded broadcast channel: converse, and the region of superposition coding

Theorem 2 of Lecture 5 of El Gamal and Kim: the private-message capacity region of the degraded
DM-BC is the set of rate pairs with `R₁ ≤ I(X; Y₁ | U)` and `R₂ ≤ I(U; Y₂)` for some `p(u, x)`.
This file proves the converse, and that this region lies in the closure of the superposition coding
inner bound.

## Main definitions

* `degradedBCPast k y`: the outputs before time `k`, as a vector of fixed length.
* `BCCode.degradedJointLaw W c`: the joint law of the uniform messages and the outputs of a code.
* `BCCode.degradedLetterLaw W c i`: the law of `(Uᵢ, Xᵢ)`, for `Uᵢ = (Y₁^{i-1}, Y₂^{i-1}, M₂)`.

## Main statements

* `BCCode.log_le_sum_bcInfoXY₁U`, `BCCode.log_le_sum_bcInfoUY₂`: the bounds for a single code.
* `IsAchievableBCBits.mem_closure_degradedBCRegionBits`: **Theorem 2 (converse)** for a physically
  degraded channel.
* `IsAchievableBCBits.mem_closure_degradedBCRegionBits_of_stochasticallyDegraded`: the same for a
  stochastically degraded channel.
* `bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U` (`Network.BCDegradedLaws`):
  `I(X; Y₁) = I(U; Y₁) + I(X; Y₁ | U)`.
* `IsStochasticallyDegraded.bcInfoUY₂_le_bcInfoUY₁`,
  `IsStochasticallyDegraded.bcInfoUY₂_add_bcInfoXY₁U_le_bcInfoXY₁`: the facts that make the sum-rate
  bound of superposition coding inactive for a degraded channel.
* `degradedBCRegionBits_subset_closure`: **Theorem 2 (achievability)**, the region lies in the
  closure of the superposition coding inner bound.

## Implementation notes

The notes take `Uᵢ = (M₂, Y₁^{i-1})`, and use physical degradedness for the Markov chain
`Y₂^{i-1} → (M₂, Y₁^{i-1}) → Y₂ᵢ` in the bound on `R₂`. We take `Uᵢ = (M₂, Y₁^{i-1}, Y₂^{i-1})`, the
last alternative in the remark on page 5-25 of the notes. The bound on `R₂` then needs no assumption
on the channel, and physical degradedness is used once, in the single-letter identity
`I(X; Y₁, Y₂ | U) = I(X; Y₁ | U)`. The past outputs have a fixed alphabet thanks to
`degradedBCPast`, which masks the later positions by `none`, so that `U = (Q, U_Q)` is a single
random variable, relabelled to `Fin k` by `Fintype.equivFin`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The past outputs and the memoryless channel -/

section Past

/-- The outputs before time `k` as a vector of fixed length: `y₀, …, y_{k-1}`, masked by `none`
at the later positions. This gives `Y^{k-1}` the same alphabet for all `k`. -/
def degradedBCPast {n : ℕ} {γ : Type*} (k : ℕ) (y : Fin n → γ) : Fin n → Option γ :=
  fun j => if (j : ℕ) < k then some (y j) else none

/-- The past outputs do not depend on the output at the present time. -/
lemma degradedBCPast_update {n : ℕ} {γ : Type*} (i : Fin n) (y : Fin n → γ) (b : γ) :
    degradedBCPast (i : ℕ) (Function.update y i b) = degradedBCPast (i : ℕ) y := by
  funext j
  by_cases hj : (j : ℕ) < i
  · have hne : j ≠ i := fun h => by simp [h] at hj
    simp [degradedBCPast, hj, Function.update_of_ne hne]
  · simp [degradedBCPast, hj]

/-- If `S` does not depend on the coordinate `i`, the sum `∑_y S(y) g(yᵢ)` only depends on
`∑_b g(b)`. -/
private lemma sum_mul_apply_eq_of_update {β : Type*} [Fintype β] {n : ℕ} (i : Fin n)
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
private lemma dist_codeLaw_pair_letter (hW : IsChannel W) (i : Fin n)
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
  refine sum_mul_apply_eq_of_update i hS (g := fun b' => W (x w i) b' * if b' = b then 1 else 0)
    (g' := fun b' => W (x w i) b' * W (x w i) b) ?_
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, ← sum_mul,
    (hW (x w i)).sum_eq_one, one_mul]

/-- **Chain rule along the past outputs.** `H(Zⁿ | A) = ∑ᵢ H(Zᵢ | Z^{i-1}, A)`. -/
lemma condEntropy_eq_sum_past {Ω γ δ : Type*} [Fintype Ω] [Fintype γ] [Fintype δ]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (Z : Ω → Fin n → γ) (A : Ω → δ) :
    H[Z | A ; μ] = ∑ i : Fin n,
      H[fun ω => Z ω i | pair (fun ω => degradedBCPast (i : ℕ) (Z ω)) A ; μ] := by
  classical
  set P : ℕ → Ω → Fin n → Option γ := fun k ω => degradedBCPast k (Z ω) with hP
  have step : ∀ (k : ℕ) (hk : k < n), H[P (k + 1) | A ; μ] =
      H[P k | A ; μ] + H[fun ω => Z ω ⟨k, hk⟩ | pair (P k) A ; μ] := by
    intro k hk
    have e1 : H[P (k + 1) | A ; μ] =
        H[pair (P k) (some ∘ fun ω => Z ω ⟨k, hk⟩) | A ; μ] := by
      refine (degradedBC_condEntropy_eq_of_comp_eq hμ A
        (fun p : (Fin n → Option γ) × Option γ =>
          (fun j : Fin n => if (j : ℕ) = k then p.2 else p.1 j))
        (fun p : Fin n → Option γ =>
          ((fun j : Fin n => if (j : ℕ) < k then p j else none), p ⟨k, hk⟩)) ?_ ?_)
      · intro ω
        funext j
        by_cases hj : (j : ℕ) = k
        · have : j = ⟨k, hk⟩ := Fin.ext hj
          subst this
          simp [hP, degradedBCPast]
        · by_cases hj' : (j : ℕ) < k
          · simp [hP, degradedBCPast, hj, hj', Nat.lt_succ_of_lt hj']
          · have : ¬ (j : ℕ) < k + 1 := by omega
            simp [hP, degradedBCPast, hj, hj', this]
      · intro ω
        refine Prod.ext ?_ ?_
        · funext j
          by_cases hj' : (j : ℕ) < k
          · simp [hP, degradedBCPast, hj', Nat.lt_succ_of_lt hj']
          · simp [hP, degradedBCPast, hj']
        · simp [hP, degradedBCPast]
    rw [e1, chain_rule_cond hμ,
      condEntropy_comp_left_injective hμ _ _ (Option.some_injective γ)]
  have hend : H[P n | A ; μ] = H[Z | A ; μ] :=
    condEntropy_congr_left hμ A (fun (y : Fin n → γ) j => some (y j))
      (fun a b h => funext fun j => Option.some_injective γ (congrFun h j))
      (fun ω => by
        funext j
        simp [hP, degradedBCPast])
  have hstart : H[P 0 | A ; μ] = 0 := by
    have : P 0 = (fun _ _ => none) ∘ A := by
      funext ω j
      simp [hP, degradedBCPast]
    rw [this]
    exact condEntropy_comp_self hμ A _
  have hsum : ∀ i : Fin n,
      H[fun ω => Z ω i | pair (fun ω => degradedBCPast (i : ℕ) (Z ω)) A ; μ] =
        (fun k => H[P (k + 1) | A ; μ] - H[P k | A ; μ]) (i : ℕ) := fun i => by
    have := step i i.isLt
    simp only [Fin.eta] at this
    simp only [this, add_sub_cancel_left]
    rfl
  rw [sum_congr rfl fun i _ => hsum i, Fin.sum_univ_eq_sum_range
    (fun k => H[P (k + 1) | A ; μ] - H[P k | A ; μ]) n, sum_range_sub (fun k => H[P k | A ; μ]) n,
    hend, hstart, sub_zero]

end Past

/-! ### The bounds for a single code -/

section Code

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {M₁ M₂ n : ℕ}
  {W : α → β₁ × β₂ → ℝ}

/-- The joint law `2^{-n(R₁ + R₂)} p(yⁿ | xⁿ(m₁, m₂))` of the independent uniform messages
`(M₁, M₂)` and of the outputs `(Y₁ⁿ, Y₂ⁿ)`. -/
def BCCode.degradedJointLaw (W : α → β₁ × β₂ → ℝ) (c : BCCode M₁ M₂ n α β₁ β₂) :
    (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → ℝ :=
  codeLaw (uniformPMF (Fin M₁ × Fin M₂)) W c.enc

/-- The law of `(Uᵢ, Xᵢ)` for a code, with the auxiliary random variable
`Uᵢ = ((Y₁^{i-1}, Y₂^{i-1}), M₂)`. -/
def BCCode.degradedLetterLaw (W : α → β₁ × β₂ → ℝ) (c : BCCode M₁ M₂ n α β₁ β₂) (i : Fin n) :
    ((Fin n → Option (β₁ × β₂)) × Fin M₂) × α → ℝ :=
  dist (c.degradedJointLaw W) fun z => ((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc z.1 i)

variable (c : BCCode M₁ M₂ n α β₁ β₂)

omit [Fintype α] in
private lemma BCCode.degradedJointLaw_isPMF (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    IsPMF (c.degradedJointLaw W) :=
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  codeLaw_isPMF uniformPMF_isPMF hW

omit [Fintype α] in
/-- The law of `((Uᵢ, Xᵢ), (Y₁ᵢ, Y₂ᵢ))` is `p(uᵢ, xᵢ) p(y₁, y₂ | xᵢ)`: `Uᵢ → Xᵢ → (Y₁ᵢ, Y₂ᵢ)`. -/
private lemma BCCode.dist_degradedJointLaw_letter (hW : IsChannel W) (i : Fin n) :
    dist (c.degradedJointLaw W)
        (fun z => (((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc z.1 i), z.2 i)) =
      bcJoint (c.degradedLetterLaw W i) W := by
  funext s
  exact dist_codeLaw_pair_letter hW i
    (fun z => ((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc z.1 i))
    (fun w y b => by simp only [degradedBCPast_update]) Prod.snd (fun _ => rfl) s.1 s.2

/-- `H(Yᵢ | Uᵢ) - H(Yᵢ | Xᵢ) = I(Xᵢ; Y₁ᵢ | Uᵢ)` for a physically degraded channel. -/
private lemma BCCode.degraded_term₁ (hW : IsChannel W) (hd : IsPhysicallyDegraded W)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (i : Fin n) :
    H[fun z => z.2 i | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ; c.degradedJointLaw W] -
      H[fun z => z.2 i | fun z => c.enc z.1 i ; c.degradedJointLaw W] =
      bcInfoXY₁U (c.degradedLetterLaw W i) W := by
  have hμ := c.degradedJointLaw_isPMF hW h₁ h₂
  have hq : IsPMF (c.degradedLetterLaw W i) := hμ.dist _
  have hA : H[fun z => z.2 i | fun z => c.enc z.1 i ; c.degradedJointLaw W] =
      ∑ x, dist (c.degradedJointLaw W) (fun z => c.enc z.1 i) x * entropy (W x) :=
    condEntropy_of_channel id (dist_codeLaw_pair_letter hW i (fun z => c.enc z.1 i)
      (fun _ _ _ => rfl) id (fun _ => rfl))
  have hB : H[fun z => z.2 i | pair (fun z => c.enc z.1 i)
      (fun z => (degradedBCPast (i : ℕ) z.2, z.1.2)) ; c.degradedJointLaw W] =
      ∑ x, dist (c.degradedJointLaw W) (fun z => c.enc z.1 i) x * entropy (W x) :=
    condEntropy_of_channel Prod.fst (dist_codeLaw_pair_letter hW i
      (pair (fun z => c.enc z.1 i) (fun z => (degradedBCPast (i : ℕ) z.2, z.1.2)))
      (fun w y b => by simp only [pair_apply, degradedBCPast_update]) Prod.fst (fun _ => rfl))
  have e := condMutualInfo_comp hμ
    (fun z => (((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc z.1 i), z.2 i))
    (fun t => t.1.2) Prod.snd (fun t => t.1.1)
  rw [c.dist_degradedJointLaw_letter hW i, degradedBC_condMutualInfo_out_eq hq hW hd,
    condMutualInfo_comm hμ, condMutualInfo] at e
  rw [← e]
  change _ = H[fun z => z.2 i | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ;
    c.degradedJointLaw W] - H[fun z => z.2 i | pair (fun z => c.enc z.1 i)
      (fun z => (degradedBCPast (i : ℕ) z.2, z.1.2)) ; c.degradedJointLaw W]
  rw [hA, hB]

/-- `H(Y₂ᵢ) - H(Y₂ᵢ | Uᵢ) = I(Uᵢ; Y₂ᵢ)`. -/
private lemma BCCode.degraded_term₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (i : Fin n) :
    H[fun z => (z.2 i).2 ; c.degradedJointLaw W] -
      H[fun z => (z.2 i).2 | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ;
        c.degradedJointLaw W] = bcInfoUY₂ (c.degradedLetterLaw W i) W := by
  have hμ := c.degradedJointLaw_isPMF hW h₁ h₂
  have e := mutualInfo_comp (μ := c.degradedJointLaw W)
    (fun z => (((degradedBCPast (i : ℕ) z.2, z.1.2), c.enc z.1 i), z.2 i))
    (fun t => t.1.1) (fun t => t.2.2)
  rw [c.dist_degradedJointLaw_letter hW i, mutualInfo_eq_entropy_sub_condEntropy' hμ] at e
  exact e

omit [Fintype α] in
private lemma BCCode.errProb_degradedJointLaw₁ :
    InfoTheory.errProb (c.degradedJointLaw W) (fun z => z.1.1) (fun z j => (z.2 j).1) c.dec₁ =
      c.errProb₁ W := by
  classical
  rw [c.errProb₁_eq, InfoTheory.errProb, Fintype.sum_prod_type, sum_div]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun y _ => ?_
  simp only [BCCode.degradedJointLaw, codeLaw, uniformPMF, Fintype.card_prod, Fintype.card_fin]
  push_cast
  split_ifs <;> ring

omit [Fintype α] in
private lemma BCCode.errProb_degradedJointLaw₂ :
    InfoTheory.errProb (c.degradedJointLaw W) (fun z => z.1.2) (fun z j => (z.2 j).2) c.dec₂ =
      c.errProb₂ W := by
  classical
  rw [c.errProb₂_eq, InfoTheory.errProb, Fintype.sum_prod_type, sum_div]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun y _ => ?_
  simp only [BCCode.degradedJointLaw, codeLaw, uniformPMF, Fintype.card_prod, Fintype.card_fin]
  push_cast
  split_ifs <;> ring

omit [Fintype α] in
private lemma BCCode.entropy_degradedJointLaw (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
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

omit [Fintype α] in
private lemma BCCode.entropy_degradedJointLaw₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2 ; c.degradedJointLaw W] = log M₂ := by
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hd := dist_codeLaw_comp_fst (ν := uniformPMF (Fin M₁ × Fin M₂)) (x := c.enc) hW
    (fun w : Fin M₁ × Fin M₂ => w.2)
  have hu : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.2) = uniformPMF (Fin M₂) := by
    have := MACCode.dist_uniformPMF_prod_snd (M₂ := M₂) h₁ id
    rw [dist_id] at this
    exact this
  rw [hu] at hd
  rw [entropyRV, show (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => z.1.2) =
    (fun w : Fin M₁ × Fin M₂ => w.2) ∘ Prod.fst from rfl, BCCode.degradedJointLaw, hd,
    entropy_uniformPMF, Fintype.card_fin]

/-- **Lecture 5 of [elgamal2010], Proof of Converse.** For a physically degraded channel,
`log |𝓜₁| ≤ ∑ᵢ I(Xᵢ; Y₁ᵢ | Uᵢ) + log 2 + P₁ log |𝓜₁|`: Fano's inequality for receiver 1,
`H(M₁ | M₂) = I(M₁; Yⁿ | M₂) + H(M₁ | Yⁿ, M₂)`, the chain rule along the past outputs and the
memoryless channel. -/
theorem BCCode.log_le_sum_bcInfoXY₁U (hW : IsChannel W) (hd : IsPhysicallyDegraded W)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₁ ≤ ∑ i, bcInfoXY₁U (c.degradedLetterLaw W i) W + log 2 + c.errProb₁ W * log M₁ := by
  have hμ := c.degradedJointLaw_isPMF (W := W) hW h₁ h₂
  set μ := c.degradedJointLaw W with hμdef
  set Mv : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₁ × Fin M₂ := Prod.fst
  set A : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₁ := fun z => z.1.1
  set B : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₂ := fun z => z.1.2
  set Y : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin n → β₁ × β₂ := Prod.snd
  have hH : H[A | B ; μ] = log M₁ := by
    rw [condEntropy_eq_sub hμ]
    have e : H[pair B A ; μ] = H[Mv ; μ] :=
      entropyRV_eq_of_injective μ Prod.swap Prod.swap_injective fun _ => rfl
    have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
    have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
    rw [e, c.entropy_degradedJointLaw hW h₁ h₂, c.entropy_degradedJointLaw₂ hW h₁ h₂,
      log_mul hM₁ hM₂]
    ring
  have hF : H[A | pair Y B ; μ] ≤ log 2 + c.errProb₁ W * log M₁ := by
    have h0 := condEntropy_le_condEntropy_comp hμ A (pair Y B)
      (fun p (j : Fin n) => (p.1 j).1)
    have h3 := fano_weak hμ A (fun z j => (z.2 j).1) c.dec₁
    rw [c.errProb_degradedJointLaw₁, Fintype.card_fin] at h3
    exact h0.trans h3
  have hI : I[A : Y | B ; μ] = H[Y | B ; μ] - H[Y | Mv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
    rfl
  have hchain := condEntropy_eq_sum_past hμ Y B
  have hcode : H[Y | Mv ; μ] = ∑ i, H[fun z => z.2 i | fun z => c.enc z.1 i ; μ] :=
    condEntropy_codeLaw hW
  have hsum : ∑ i, bcInfoXY₁U (c.degradedLetterLaw W i) W =
      ∑ i, H[fun ω => Y ω i | pair (fun ω => degradedBCPast (i : ℕ) (Y ω)) B ; μ] -
        ∑ i, H[fun z => z.2 i | fun z => c.enc z.1 i ; μ] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => (c.degraded_term₁ hW hd h₁ h₂ i).symm
  have hfano : H[A | B ; μ] = I[A : Y | B ; μ] + H[A | pair Y B ; μ] := by
    rw [condMutualInfo]; ring
  linarith

/-- **Lecture 5 of [elgamal2010], Proof of Converse.**
`log |𝓜₂| ≤ ∑ᵢ I(Uᵢ; Y₂ᵢ) + log 2 + P₂ log |𝓜₂|`: Fano's inequality for receiver 2,
`H(Y₂ⁿ) ≤ ∑ᵢ H(Y₂ᵢ)` and `H(Y₂ⁿ | M₂) = ∑ᵢ H(Y₂ᵢ | Y₂^{i-1}, M₂) ≥ ∑ᵢ H(Y₂ᵢ | Uᵢ)`. -/
theorem BCCode.log_le_sum_bcInfoUY₂ (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₂ ≤ ∑ i, bcInfoUY₂ (c.degradedLetterLaw W i) W + log 2 + c.errProb₂ W * log M₂ := by
  have hμ := c.degradedJointLaw_isPMF (W := W) hW h₁ h₂
  set μ := c.degradedJointLaw W with hμdef
  set B : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin M₂ := fun z => z.1.2
  set Y₂ : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) → Fin n → β₂ := fun z j => (z.2 j).2
  have hH : H[B ; μ] = log M₂ := c.entropy_degradedJointLaw₂ hW h₁ h₂
  have hF : H[B | Y₂ ; μ] ≤ log 2 + c.errProb₂ W * log M₂ := by
    have h3 := fano_weak hμ B Y₂ c.dec₂
    rwa [c.errProb_degradedJointLaw₂, Fintype.card_fin] at h3
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ B Y₂
  have hI' := mutualInfo_eq_entropy_sub_condEntropy' hμ B Y₂
  have hY : H[Y₂ ; μ] ≤ ∑ i, H[fun z => (z.2 i).2 ; μ] := by
    have := condEntropy_pi_le_sum hμ Y₂ (fun _ => ())
    simp only [condEntropy_const hμ] at this
    exact this
  have hchain := condEntropy_eq_sum_past hμ Y₂ B
  have hle : ∀ i : Fin n, H[fun z => (z.2 i).2 | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ; μ] ≤
      H[fun ω => Y₂ ω i | pair (fun ω => degradedBCPast (i : ℕ) (Y₂ ω)) B ; μ] := by
    intro i
    have h := condEntropy_le_condEntropy_comp hμ (fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) =>
      (z.2 i).2) (fun z => (degradedBCPast (i : ℕ) z.2, z.1.2))
      (fun p => ((fun j => (p.1 j).map Prod.snd), p.2))
    have e : ((fun p : (Fin n → Option (β₁ × β₂)) × Fin M₂ =>
        ((fun j => (p.1 j).map Prod.snd), p.2)) ∘
        fun z : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) => (degradedBCPast (i : ℕ) z.2, z.1.2)) =
        pair (fun ω => degradedBCPast (i : ℕ) (Y₂ ω)) B := by
      funext z
      refine Prod.ext ?_ rfl
      funext j
      by_cases hj : j < i <;> simp [degradedBCPast, Y₂, pair_apply, hj]
    rw [e] at h
    exact h
  have hsum : ∑ i, bcInfoUY₂ (c.degradedLetterLaw W i) W =
      ∑ i, H[fun z => (z.2 i).2 ; μ] -
        ∑ i : Fin n, H[fun z => (z.2 i).2 | fun z => (degradedBCPast (i : ℕ) z.2, z.1.2) ; μ] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => (c.degraded_term₂ hW h₁ h₂ i).symm
  have hle' := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin n))) => hle i
  linarith

end Code

/-! ### The converse -/

section Converse

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

/-- The arithmetic of the converse: a bound on `log 2^⌈nR⌉` is a bound on `R` in bits. -/
lemma degradedBC_rate_le {R S P Pj : ℝ} {n b : ℕ} (hn : 0 < n) (hP : 0 ≤ P) (hPj : Pj ≤ P)
    (h : log ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) ≤ S + log 2 +
      Pj * log ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ)) :
    R - (1 + P * ((⌈(n : ℝ) * R⌉₊ : ℝ) + b)) / n ≤ S / n / log 2 := by
  have hL := log_two_pos'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a := ⌈(n : ℝ) * R⌉₊ with ha
  have hlog : log ((2 ^ a : ℕ) : ℝ) = a * log 2 := by
    push_cast
    rw [log_pow]
  rw [hlog] at h
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hnR : (n : ℝ) * R ≤ a := Nat.le_ceil _
  have h1 : Pj * (a * log 2) ≤ P * ((a + b) * log 2) := by
    calc Pj * (a * log 2) ≤ P * (a * log 2) :=
          mul_le_mul_of_nonneg_right hPj (mul_nonneg ha0 hL.le)
      _ ≤ P * ((a + b) * log 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hP
          nlinarith
  have h2 : (n : ℝ) * R * log 2 ≤ a * log 2 := mul_le_mul_of_nonneg_right hnR hL.le
  rw [sub_le_iff_le_add, div_div, div_add_div _ _ (mul_pos hn' hL).ne' hn'.ne', le_div_iff₀
    (mul_pos (mul_pos hn' hL) hn')]
  have h3 : (n : ℝ) * R * log 2 ≤ S + (1 + P * ((a + b : ℝ))) * log 2 := by nlinarith
  calc R * (↑n * log 2 * ↑n) = (n : ℝ) * R * log 2 * n := by ring
    _ ≤ (S + (1 + P * ((a + b : ℝ))) * log 2) * n := mul_le_mul_of_nonneg_right h3 hn'.le
    _ = _ := by ring

lemma degradedBC_sum_uniform {n : ℕ} (I : Fin n → ℝ) :
    ∑ i, uniformPMF (Fin n) i * I i = (∑ i, I i) / n := by
  simp only [uniformPMF, Fintype.card_fin]
  rw [← mul_sum, one_div_mul_eq_div]

/-- **Theorem 2 of [elgamal2010], Lecture 5 (converse), pages 5-23 to 5-26.** Every achievable rate
pair of a physically degraded DM-BC is in the closure of the region `R₁ ≤ I(X; Y₁ | U)`,
`R₂ ≤ I(U; Y₂)`. The auxiliary random variable is `U = (Q, U_Q)`, with `Q` uniform on the `n`
positions and `Uᵢ = (M₂, Y₁^{i-1}, Y₂^{i-1})`, one of the alternatives in the remark of the notes;
physical degradedness gives `I(Xᵢ; Y₁ᵢ, Y₂ᵢ | Uᵢ) = I(Xᵢ; Y₁ᵢ | Uᵢ)`. -/
theorem IsAchievableBCBits.mem_closure_degradedBCRegionBits (hW : IsChannel W)
    (hd : IsPhysicallyDegraded W) {R₁ R₂ : ℝ} (h : IsAchievableBCBits W R₁ R₂) :
    (R₁, R₂) ∈ closure (degradedBCRegionBits W) := by
  obtain ⟨c, hc⟩ := h
  set a₁ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₁⌉₊ with ha₁
  set a₂ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₂⌉₊ with ha₂
  set P : ℕ → ℝ := fun n => (c n).errProb W with hPdef
  set ε : ℕ → ℝ := fun n => (1 + P n * ((a₁ n : ℝ) + a₂ n)) / n with hεdef
  have hP₁ : ∀ n, (c n).errProb₁ W ≤ P n := fun n =>
    (le_max_left _ _).trans ((c n).max_errProb_le hW)
  have hP₂ : ∀ n, (c n).errProb₂ W ≤ P n := fun n =>
    (le_max_right _ _).trans ((c n).max_errProb_le hW)
  have hP0 : ∀ n, 0 ≤ P n := fun n => ((c n).errProb₁_nonneg hW).trans (hP₁ n)
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg zero_le_one
    (mul_nonneg (hP0 n) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Nat.cast_nonneg n)
  have hL := log_two_pos'
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ degradedBCRegionBits W := by
    intro n hn
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hM₁ : 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := by positivity
    have hM₂ : 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := by positivity
    have hμ := (c n).degradedJointLaw_isPMF (W := W) hW hM₁ hM₂
    have hq : ∀ i, IsPMF ((c n).degradedLetterLaw W i) := fun i => hμ.dist _
    have hw : IsPMF (uniformPMF (Fin n)) := uniformPMF_isPMF
    have hbar := degradedBCTimeShare_isPMF hw hq
    have b₁ := (c n).log_le_sum_bcInfoXY₁U hW hd hM₁ hM₂
    have b₂ := (c n).log_le_sum_bcInfoUY₂ hW hM₁ hM₂
    refine ⟨_, degradedBCRelabelLaw (Fintype.equivFin _)
      (degradedBCTimeShare (uniformPMF (Fin n)) ((c n).degradedLetterLaw W)),
      degradedBCRelabelLaw_isPMF _ hbar, ?_, ?_⟩
    · rw [degradedBC_bcInfoXY₁U_relabel _ hbar hW, bcInfoXY₁U_degradedBCTimeShare hw hq hW,
        degradedBC_sum_uniform]
      exact degradedBC_rate_le (b := a₂ n) hn (hP0 n) (hP₁ n) (by exact_mod_cast b₁)
    · rw [degradedBC_bcInfoUY₂_relabel _ hbar hW]
      have h1 := sum_mul_bcInfoUY₂_le_degradedBCTimeShare (W := W) hw hq hW
      rw [degradedBC_sum_uniform] at h1
      have h2 := degradedBC_rate_le (b := a₁ n) hn (hP0 n) (hP₂ n) (by exact_mod_cast b₂)
      have h3 : ε n = (1 + P n * ((a₂ n : ℝ) + a₁ n)) / n := by
        simp only [hεdef, add_comm]
      rw [h3]
      exact h2.trans (div_le_div_of_nonneg_right h1 hL.le)
  have hε : Tendsto ε atTop (𝓝 0) := by
    set K := |R₁| + |R₂| + 2
    have hP0' : Tendsto P atTop (𝓝 0) := hc
    have hup : Tendsto (fun n : ℕ => 1 / (n : ℝ) + P n * K) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add (hP0'.mul_const K)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall hε0) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hceil : ∀ x : ℝ, (⌈x⌉₊ : ℝ) ≤ |x| + 1 := fun x => by
      have h1 : (⌈x⌉₊ : ℝ) ≤ ⌈|x|⌉₊ := by exact_mod_cast Nat.ceil_mono (le_abs_self x)
      linarith [Nat.ceil_lt_add_one (abs_nonneg x)]
    have h1 := hceil ((n : ℝ) * R₁)
    have h2 := hceil ((n : ℝ) * R₂)
    rw [abs_mul, Nat.abs_cast] at h1 h2
    have hab : (a₁ n : ℝ) + a₂ n ≤ n * K := by
      simp only [ha₁, ha₂, K]
      nlinarith
    simp only [hεdef]
    rw [add_div, mul_div_assoc]
    gcongr
    · exact hP0 n
    · rw [div_le_iff₀ hn']
      linarith
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

/-! ### Stochastically degraded channels -/

omit [Fintype α] in
/-- A stochastically degraded channel has the conditional marginals of a physically degraded
channel. -/
private lemma exists_physicallyDegraded_of_stochasticallyDegraded (hW : IsChannel W)
    (hd : IsStochasticallyDegraded W) : ∃ W' : α → β₁ × β₂ → ℝ, IsChannel W' ∧
      IsPhysicallyDegraded W' ∧ bcMarg₁ W' = bcMarg₁ W ∧ bcMarg₂ W' = bcMarg₂ W := by
  obtain ⟨V, hV, h⟩ := hd
  refine ⟨fun x y => bcMarg₁ W x y.1 * V y.1 y.2, fun x =>
    ⟨fun y => mul_nonneg ((hW.bcMarg₁ x).nonneg _) ((hV _).nonneg _), ?_⟩,
    ⟨bcMarg₁ W, V, hW.bcMarg₁, hV, fun _ _ _ => rfl⟩, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [← mul_sum, (hV _).sum_eq_one, mul_one]
    exact (hW.bcMarg₁ x).sum_eq_one
  · funext x y₁
    simp only [bcMarg₁, ← mul_sum, (hV y₁).sum_eq_one, mul_one]
  · funext x y₂
    rw [h]
    rfl

/-- **Theorem 2 of [elgamal2010], Lecture 5 (converse).** Every achievable rate pair of a
stochastically degraded DM-BC is in the closure of the region `R₁ ≤ I(X; Y₁ | U)`,
`R₂ ≤ I(U; Y₂)`: achievability and the region only depend on the conditional marginals, which are
those of a physically degraded channel. -/
theorem IsAchievableBCBits.mem_closure_degradedBCRegionBits_of_stochasticallyDegraded
    (hW : IsChannel W) (hd : IsStochasticallyDegraded W) {R₁ R₂ : ℝ}
    (h : IsAchievableBCBits W R₁ R₂) : (R₁, R₂) ∈ closure (degradedBCRegionBits W) := by
  obtain ⟨W', hW', hp, h₁, h₂⟩ := exists_physicallyDegraded_of_stochasticallyDegraded hW hd
  have h' := ((isAchievableBCBits_congr hW' hW h₁ h₂).2 h).mem_closure_degradedBCRegionBits hW' hp
  refine closure_mono ?_ h'
  rintro R ⟨k, q, hq, hR₁, hR₂⟩
  refine ⟨k, q, hq, ?_, ?_⟩
  · rwa [degradedBC_bcInfoXY₁U_eq_jointOf hq hW, ← h₁, ← degradedBC_bcInfoXY₁U_eq_jointOf hq hW']
  · rwa [degradedBC_bcInfoUY₂_eq_jointOf, ← h₂, ← degradedBC_bcInfoUY₂_eq_jointOf]

end Converse

/-! ### Superposition coding achieves the region of a degraded channel -/

section Achievability

variable {α β₁ β₂ 𝒰 : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] [Fintype 𝒰]
  {q : 𝒰 × α → ℝ} {W : α → β₁ × β₂ → ℝ}

/-- **Lecture 5 of [elgamal2010], page 5-22.** For a stochastically degraded channel,
`I(U; Y₂) ≤ I(U; Y₁)`, by data processing for the physically degraded channel with the same
conditional marginals. -/
theorem IsStochasticallyDegraded.bcInfoUY₂_le_bcInfoUY₁ (hW : IsChannel W)
    (hd : IsStochasticallyDegraded W) (hq : IsPMF q) : bcInfoUY₂ q W ≤ bcInfoUY₁ q W := by
  obtain ⟨W', hW', hp, h₁, h₂⟩ := exists_physicallyDegraded_of_stochasticallyDegraded hW hd
  have h := degradedBC_bcInfoUY₂_le_bcInfoUY₁_of_physicallyDegraded hq hW' hp
  rwa [degradedBC_bcInfoUY₂_eq_jointOf, degradedBC_bcInfoUY₁_eq_jointOf, h₁, h₂,
    ← degradedBC_bcInfoUY₂_eq_jointOf,
    ← degradedBC_bcInfoUY₁_eq_jointOf] at h

/-- **Lecture 5 of [elgamal2010], page 5-22.** For a stochastically degraded channel,
`I(U; Y₂) + I(X; Y₁ | U) ≤ I(X; Y₁)`, so that the sum-rate bound of the superposition coding inner
bound is inactive. -/
theorem IsStochasticallyDegraded.bcInfoUY₂_add_bcInfoXY₁U_le_bcInfoXY₁ (hW : IsChannel W)
    (hd : IsStochasticallyDegraded W) (hq : IsPMF q) :
    bcInfoUY₂ q W + bcInfoXY₁U q W ≤ bcInfoXY₁ q W := by
  rw [bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U hq hW]
  linarith [hd.bcInfoUY₂_le_bcInfoUY₁ hW hq]

/-- **Theorem 2 of [elgamal2010], Lecture 5 (achievability), page 5-22.** For a stochastically
degraded channel, the region `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` lies in the closure of the
superposition coding inner bound: its points are the limits of the points `R - (t, t)`, `t → 0⁺`. -/
theorem degradedBCRegionBits_subset_closure (hW : IsChannel W)
    (hd : IsStochasticallyDegraded W) :
    degradedBCRegionBits W ⊆ closure (superpositionRegionBits W) := by
  rintro ⟨R₁, R₂⟩ ⟨k, q, hq, hR₁, hR₂⟩
  simp only at hR₁ hR₂
  have hL := log_two_pos'
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => (R₁ - 1 / ((n : ℝ) + 1), R₂ - 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n : ℕ => R₁ - 1 / ((n : ℝ) + 1)) atTop (𝓝 (R₁ - 0)) :=
      tendsto_const_nhds.sub ht
    have h2 : Tendsto (fun n : ℕ => R₂ - 1 / ((n : ℝ) + 1)) atTop (𝓝 (R₂ - 0)) :=
      tendsto_const_nhds.sub ht
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsum := div_le_div_of_nonneg_right (hd.bcInfoUY₂_add_bcInfoXY₁U_le_bcInfoXY₁ hW hq) hL.le
  rw [add_div] at hsum
  refine ⟨k, q, hq, ?_, ?_, ?_⟩
  · simp only; linarith
  · simp only; linarith
  · simp only; linarith

end Achievability

end InfoTheory
