/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTung
public import InfoTheoryLib.RateDistortion.SideInfoConverse

/-!
# The Berger–Tung outer bound

This file proves Theorem 2 of Lecture 13. For a code, the auxiliary random variables are
`Uⱼᵢ = (Mⱼ, Zⁱ⁻¹)`, with `Zᵢ = (X₁ᵢ, X₂ᵢ)`, as in the notes, together with a uniform time sharing
variable `Q`, which replaces the convexity argument.

## Main definitions

* `dlOuterAt`: the rates and the distortions of the outer bound.

## Main statements

* `condEntropy_mix_prefix`: `H(Z_Q | Q, M, Z^{Q-1}) = (1 / n) H(Zⁿ | M)`.
* `DistLossyCode.dlOuterAt`: the single-letter bounds for one code.
* `IsAchievableDL.dlOuterAt`: **the Berger–Tung outer bound (Theorem 2 of Lecture 13)**.

## Implementation notes

The notes state the outer bound with the distortion constraints `Dⱼ ≥ E dⱼ(Xⱼ, X̂ⱼ)`. As `U₁` and
`U₂`
have no bounded cardinality here, we get `Dⱼ + ε ≥ E dⱼ(Xⱼ, X̂ⱼ)` for every `ε > 0`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ} {d₁ : α₁ → β₁ → ℝ}
  {d₂ : α₂ → β₂ → ℝ} {n : ℕ}

/-- **Theorem 2 of Lecture 13 of [elgamal2010], page 13-14.** The outer bound holds at `(R₁, R₂)`
and
`(D₁, D₂)`: for some `p(u₁, u₂ | x₁, x₂)` with `U₁ → X₁ → X₂` and `X₁ → X₂ → U₂` and functions
`x̂ⱼ(u₁, u₂)`, we have `E dⱼ(Xⱼ, X̂ⱼ) ≤ Dⱼ`, and, in bits, `R₁ ≥ I(X₁, X₂; U₁ | U₂)`,
`R₂ ≥ I(X₁, X₂; U₂ | U₁)` and `R₁ + R₂ ≥ I(X₁, X₂; U₁, U₂)`. The auxiliary random variables take
values
in `Fin k₁` and `Fin k₂`. -/
def dlOuterAt (P : α₁ × α₂ → ℝ) (d₁ : α₁ → β₁ → ℝ) (d₂ : α₂ → β₂ → ℝ) (R₁ R₂ D₁ D₂ : ℝ) : Prop :=
  ∃ (k₁ k₂ : ℕ) (κ : α₁ × α₂ → Fin k₁ × Fin k₂ → ℝ) (κ₁ : α₁ → Fin k₁ → ℝ) (κ₂ : α₂ → Fin k₂ → ℝ)
    (f₁ : Fin k₁ → Fin k₂ → β₁) (f₂ : Fin k₁ → Fin k₂ → β₂),
    IsChannel κ ∧ IsChannel κ₁ ∧ IsChannel κ₂ ∧
    dist (jointOf P κ) (fun w => (w.1, w.2.1)) = jointOf P (fun z => κ₁ z.1) ∧
    dist (jointOf P κ) (fun w => (w.1, w.2.2)) = jointOf P (fun z => κ₂ z.2) ∧
    ∑ w, jointOf P κ w * d₁ w.1.1 (f₁ w.2.1 w.2.2) ≤ D₁ ∧
    ∑ w, jointOf P κ w * d₂ w.1.2 (f₂ w.2.1 w.2.2) ≤ D₂ ∧
    I[Prod.fst : fun w : (α₁ × α₂) × Fin k₁ × Fin k₂ => w.2.1 | fun w => w.2.2 ; jointOf P κ] ≤
      R₁ * log 2 ∧
    I[Prod.fst : fun w : (α₁ × α₂) × Fin k₁ × Fin k₂ => w.2.2 | fun w => w.2.1 ; jointOf P κ] ≤
      R₂ * log 2 ∧
    I[Prod.fst : Prod.snd ; jointOf P κ] ≤ (R₁ + R₂) * log 2

/-! ### The time sharing variable -/

section Mix

variable (z₀ : α₁ × α₂) {τ : Type*} [Fintype τ]

/-- **Lecture 13, page 13-15.** `H(Z_Q | Q, M, Z^{Q-1}) = (1 / n) H(Zⁿ | M)`, by the chain rule. -/
theorem condEntropy_mix_prefix (hP : IsPMF P) (hn : 0 < n) (M : (Fin n → α₁ × α₂) → τ) :
    H[fun z : (Fin n → α₁ × α₂) × Fin n => z.1 z.2 | fun z =>
        (⟨z.2, M z.1, prefixRV (seqZ z₀) z.2 z.1⟩ : Σ i : Fin n, τ × (Fin i → α₁ × α₂)) ;
        mixLaw (iidPMF P n) (Fin n)] =
      (n : ℝ)⁻¹ * H[id | M ; iidPMF P n] := by
  classical
  have hμ := iidPMF_isPMF hP n
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α₁ × α₂) => ω i)
    (b := fun i : Fin n => τ × (Fin i → α₁ × α₂)) fun i => pair M (prefixRV (seqZ z₀) i)
  simp only [Fintype.card_fin] at h
  refine h.trans ?_
  congr 1
  have hc := chain_rule_entropy_cond hμ (seqZ z₀) M n
  have hp : prefixRV (seqZ z₀) n = (id : (Fin n → α₁ × α₂) → Fin n → α₁ × α₂) := by
    funext ω j
    simp only [prefixRV, seqZ_coe, id]
  rw [hp, sum_range] at hc
  rw [hc]
  refine sum_congr rfl fun i _ => ?_
  have hZ : seqZ z₀ (i : ℕ) = fun ω : Fin n → α₁ × α₂ => ω i := funext fun ω => seqZ_coe z₀ i ω
  rw [hZ]

/-- `H(Z | M₂) - H(Z | M₁, M₂) ≤ log |𝓜₁|`. -/
lemma condEntropy_sub_condEntropy_le {Ω Z : Type*} [Fintype Ω] [Fintype Z] {μ : Ω → ℝ}
    (hμ : IsPMF μ) (X : Ω → Z) {m₁ : ℕ} (M₁ : Ω → Fin m₁) (M₂ : Ω → τ) :
    H[X | M₂ ; μ] - H[X | pair M₁ M₂ ; μ] ≤ log m₁ := by
  have hc1 := chain_rule_cond hμ X M₁ M₂
  have hc2 := chain_rule_cond hμ M₁ X M₂
  have hswap : H[pair X M₁ | M₂ ; μ] = H[pair M₁ X | M₂ ; μ] :=
    condEntropy_congr_left hμ M₂ Prod.swap Prod.swap_injective fun _ => rfl
  have h0 := condEntropy_nonneg hμ M₁ (pair X M₂)
  have h1 := condEntropy_le_entropy hμ M₁ M₂
  have h2 := entropyRV_le_log_card hμ M₁
  rw [Fintype.card_fin] at h2
  linarith

/-- `H(Z_Q | U) = (1 / n) H(Zⁿ | M)` for any injective relabelling `U` of `(Q, M, Z^{Q-1})`. -/
theorem condEntropy_mix_prefix_of_inj (hP : IsPMF P) (hn : 0 < n) (M : (Fin n → α₁ × α₂) → τ)
    {σ : Type*} [Fintype σ] (U : (Fin n → α₁ × α₂) × Fin n → σ)
    (f : (Σ i : Fin n, τ × (Fin i → α₁ × α₂)) → σ) (hf : Function.Injective f)
    (hU : ∀ z, U z = f ⟨z.2, M z.1, prefixRV (seqZ z₀) z.2 z.1⟩) :
    H[fun z : (Fin n → α₁ × α₂) × Fin n => z.1 z.2 | U ; mixLaw (iidPMF P n) (Fin n)] =
      (n : ℝ)⁻¹ * H[id | M ; iidPMF P n] := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hν := mixLaw_isPMF (ι := Fin n) (iidPMF_isPMF hP n)
  rw [condEntropy_congr_right hν _ f hf hU]
  exact condEntropy_mix_prefix z₀ hP hn M

end Mix

/-! ### The bounds for one code -/

section Code

variable {M₁ M₂ : ℕ}

omit [Fintype α₁] [Fintype α₂] in
lemma fstSeq_update (ω : Fin n → α₁ × α₂) (i : Fin n) {c : α₁ × α₂} (h : c.1 = (ω i).1) :
    fstSeq (Function.update ω i c) = fstSeq ω := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [fstSeq, h]
  · simp [fstSeq, hj]

omit [Fintype α₁] [Fintype α₂] in
lemma sndSeq_update (ω : Fin n → α₁ × α₂) (i : Fin n) {c : α₁ × α₂} (h : c.2 = (ω i).2) :
    sndSeq (Function.update ω i c) = sndSeq ω := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [sndSeq, h]
  · simp [sndSeq, hj]

/-- The average under the time sharing variable of a function of the coordinate. -/
lemma sum_mixLaw_mul (hn : 0 < n) (G : (Fin n → α₁ × α₂) → Fin n → ℝ) :
    ∑ z, mixLaw (iidPMF P n) (Fin n) z * G z.1 z.2 =
      ∑ ω, iidPMF P n ω * ((∑ i, G ω i) / n) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  rw [sum_div, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [mixLaw, prodDist, uniformPMF, Fintype.card_fin]
  ring

/-- **Lecture 13, page 13-15.** The single-letter bounds for one code. -/
theorem DistLossyCode.dlOuterAt_of_code (hP : IsPMF P) (hn : 0 < n)
    (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂) {R₁ R₂ : ℝ} (hM₁ : log M₁ ≤ n * (R₁ * log 2))
    (hM₂ : log M₂ ≤ n * (R₂ * log 2)) :
    dlOuterAt P d₁ d₂ R₁ R₂ (c.distortion₁ P d₁) (c.distortion₂ P d₂) := by
  classical
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set ν := mixLaw (iidPMF P n) (Fin n) with hν
  have hνP : IsPMF ν := mixLaw_isPMF hμ
  set e₁ := Fintype.equivFin (Σ i : Fin n, Fin M₁ × (Fin i → α₁ × α₂)) with he₁
  set e₂ := Fintype.equivFin (Σ i : Fin n, Fin M₂ × (Fin i → α₁ × α₂)) with he₂
  set A₁ : (Fin n → α₁ × α₂) → Fin M₁ := fun ω => c.enc₁ (fstSeq ω) with hA₁
  set A₂ : (Fin n → α₁ × α₂) → Fin M₂ := fun ω => c.enc₂ (sndSeq ω) with hA₂
  set S₁ : Fin n → (Fin n → α₁ × α₂) → Σ i : Fin n, Fin M₁ × (Fin i → α₁ × α₂) :=
    fun i ω => ⟨i, A₁ ω, prefixRV (seqZ z₀) i ω⟩ with hS₁
  set S₂ : Fin n → (Fin n → α₁ × α₂) → Σ i : Fin n, Fin M₂ × (Fin i → α₁ × α₂) :=
    fun i ω => ⟨i, A₂ ω, prefixRV (seqZ z₀) i ω⟩ with hS₂
  obtain ⟨κ, hκ, hlaw⟩ := exists_mix_kernel_comp hP hn id (fun i ω => (e₁ (S₁ i ω), e₂ (S₂ i ω)))
    fun i ω c' h => by
      have h' : c' = ω i := h
      rw [h', Function.update_eq_self]
  obtain ⟨κ₁, hκ₁, hlaw₁⟩ := exists_mix_kernel_comp hP hn Prod.fst (fun i ω => e₁ (S₁ i ω))
    fun i ω c' h => by
      simp only [hS₁, hA₁, fstSeq_update ω i h, prefixRV_update]
  obtain ⟨κ₂, hκ₂, hlaw₂⟩ := exists_mix_kernel_comp hP hn Prod.snd (fun i ω => e₂ (S₂ i ω))
    fun i ω c' h => by
      simp only [hS₂, hA₂, sndSeq_update ω i h, prefixRV_update]
  have hL : jointOf P κ = dist ν fun z => (z.1 z.2, (e₁ (S₁ z.2 z.1), e₂ (S₂ z.2 z.1))) := hlaw
  have hLP : IsPMF (jointOf P κ) := jointOf_isPMF hP hκ
  set f₁ : Fin _ → Fin _ → β₁ := fun a b =>
    (c.dec ((e₁.symm a).2.1, (e₂.symm b).2.1)).1 (e₁.symm a).1 with hf₁
  set f₂ : Fin _ → Fin _ → β₂ := fun a b =>
    (c.dec ((e₁.symm a).2.1, (e₂.symm b).2.1)).2 (e₁.symm a).1 with hf₂
  -- The entropies.
  set Zq : (Fin n → α₁ × α₂) × Fin n → α₁ × α₂ := fun z => z.1 z.2 with hZq
  have hX₂ : H[Prod.fst | fun w : (α₁ × α₂) × Fin _ × Fin _ => w.2.2 ; jointOf P κ] =
      (n : ℝ)⁻¹ * H[id | A₂ ; iidPMF P n] := by
    have h1 := condEntropy_mix_prefix_of_inj z₀ hP hn A₂ (fun z => e₂ (S₂ z.2 z.1)) e₂
      e₂.injective fun z => rfl
    rw [← h1]
    refine condEntropy_eq_of_dist_pair_eq hLP hνP ?_
    rw [hL, ← dist_comp_eq]
    rfl
  have hX₁ : H[Prod.fst | fun w : (α₁ × α₂) × Fin _ × Fin _ => w.2.1 ; jointOf P κ] =
      (n : ℝ)⁻¹ * H[id | A₁ ; iidPMF P n] := by
    have h1 := condEntropy_mix_prefix_of_inj z₀ hP hn A₁ (fun z => e₁ (S₁ z.2 z.1)) e₁
      e₁.injective fun z => rfl
    rw [← h1]
    refine condEntropy_eq_of_dist_pair_eq hLP hνP ?_
    rw [hL, ← dist_comp_eq]
    rfl
  have hX₁₂ : H[Prod.fst | pair (fun w : (α₁ × α₂) × Fin _ × Fin _ => w.2.1) (fun w => w.2.2) ;
      jointOf P κ] = (n : ℝ)⁻¹ * H[id | pair A₁ A₂ ; iidPMF P n] := by
    have h1 := condEntropy_mix_prefix_of_inj z₀ hP hn (pair A₁ A₂)
      (fun z => (e₁ (S₁ z.2 z.1), e₂ (S₂ z.2 z.1)))
      (fun s => (e₁ ⟨s.1, s.2.1.1, s.2.2⟩, e₂ ⟨s.1, s.2.1.2, s.2.2⟩))
      (by
        rintro ⟨i, ⟨a, b⟩, p⟩ ⟨i', ⟨a', b'⟩, p'⟩ h
        have h1 := e₁.injective (Prod.mk.inj h).1
        have h2 := e₂.injective (Prod.mk.inj h).2
        simp only [Sigma.mk.injEq] at h1 h2
        obtain ⟨rfl, h3⟩ := h1
        obtain ⟨-, h4⟩ := h2
        simp only [heq_eq_eq, Prod.mk.injEq] at h3 h4
        rw [h3.1, h3.2, h4.1]) fun z => rfl
    rw [← h1]
    refine condEntropy_eq_of_dist_pair_eq hLP hνP ?_
    rw [hL, ← dist_comp_eq]
    rfl
  have hX₂₁ : H[Prod.fst | pair (fun w : (α₁ × α₂) × Fin _ × Fin _ => w.2.2) (fun w => w.2.1) ;
      jointOf P κ] = (n : ℝ)⁻¹ * H[id | pair A₂ A₁ ; iidPMF P n] := by
    have h1 := condEntropy_mix_prefix_of_inj z₀ hP hn (pair A₂ A₁)
      (fun z => (e₂ (S₂ z.2 z.1), e₁ (S₁ z.2 z.1)))
      (fun s => (e₂ ⟨s.1, s.2.1.1, s.2.2⟩, e₁ ⟨s.1, s.2.1.2, s.2.2⟩))
      (by
        rintro ⟨i, ⟨a, b⟩, p⟩ ⟨i', ⟨a', b'⟩, p'⟩ h
        have h1 := e₂.injective (Prod.mk.inj h).1
        have h2 := e₁.injective (Prod.mk.inj h).2
        simp only [Sigma.mk.injEq] at h1 h2
        obtain ⟨rfl, h3⟩ := h1
        obtain ⟨-, h4⟩ := h2
        simp only [heq_eq_eq, Prod.mk.injEq] at h3 h4
        rw [h3.1, h3.2, h4.1]) fun z => rfl
    rw [← h1]
    refine condEntropy_eq_of_dist_pair_eq hLP hνP ?_
    rw [hL, ← dist_comp_eq]
    rfl
  have hHZ : H[Prod.fst ; jointOf P κ] = (n : ℝ)⁻¹ * H[id ; iidPMF P n] := by
    have e1 : H[Prod.fst ; jointOf P κ] = entropy P := by
      rw [entropyRV, dist_jointOf_fst hκ]
    have e2 : H[id ; iidPMF P n] = n * entropy P := by
      rw [entropyRV, dist_id, entropy_iidPMF hP]
    rw [e1, e2, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  -- The costs.
  have hs₀ : ∀ s, (e₁.symm (e₁ s)).1 = s.1 := fun s => by rw [Equiv.symm_apply_apply]
  have hs₁ : ∀ s, (e₁.symm (e₁ s)).2.1 = s.2.1 := fun s => by rw [Equiv.symm_apply_apply]
  have hs₂ : ∀ s, (e₂.symm (e₂ s)).2.1 = s.2.1 := fun s => by rw [Equiv.symm_apply_apply]
  have hc₁ : ∑ w, jointOf P κ w * d₁ w.1.1 (f₁ w.2.1 w.2.2) = c.distortion₁ P d₁ := by
    rw [hL, sum_dist_mul ν (fun z => (z.1 z.2, (e₁ (S₁ z.2 z.1), e₂ (S₂ z.2 z.1))))
      fun w => d₁ w.1.1 (f₁ w.2.1 w.2.2)]
    rw [sum_mixLaw_mul hn fun ω i => d₁ (ω i).1 (f₁ (e₁ (S₁ i ω)) (e₂ (S₂ i ω)))]
    refine sum_congr rfl fun ω _ => ?_
    simp only [hf₁, hs₀, hs₁, hs₂, seqDistortion, hS₁, hS₂, hA₁, hA₂, DistLossyCode.output]
    rfl
  have hc₂ : ∑ w, jointOf P κ w * d₂ w.1.2 (f₂ w.2.1 w.2.2) = c.distortion₂ P d₂ := by
    rw [hL, sum_dist_mul ν (fun z => (z.1 z.2, (e₁ (S₁ z.2 z.1), e₂ (S₂ z.2 z.1))))
      fun w => d₂ w.1.2 (f₂ w.2.1 w.2.2)]
    rw [sum_mixLaw_mul hn fun ω i => d₂ (ω i).2 (f₂ (e₁ (S₁ i ω)) (e₂ (S₂ i ω)))]
    refine sum_congr rfl fun ω _ => ?_
    simp only [hf₂, hs₀, hs₁, hs₂, seqDistortion, hS₁, hS₂, hA₁, hA₂, DistLossyCode.output]
    rfl
  have hinvm : ∀ {x y : ℝ}, x ≤ n * y → (n : ℝ)⁻¹ * x ≤ y := fun {x y} h => by
    rw [inv_mul_le_iff₀ hn']
    exact h
  have hsub₁ := condEntropy_sub_condEntropy_le hμ (id : (Fin n → α₁ × α₂) → _) A₁ A₂
  have hsub₂ := condEntropy_sub_condEntropy_le hμ (id : (Fin n → α₁ × α₂) → _) A₂ A₁
  have hsub₃ : H[id ; iidPMF P n] - H[id | A₂ ; iidPMF P n] ≤ log M₂ := by
    rw [← mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_comm hμ,
      mutualInfo_eq_entropy_sub_condEntropy hμ]
    have h1 := condEntropy_nonneg hμ A₂ (id : (Fin n → α₁ × α₂) → _)
    have h2 := entropyRV_le_log_card hμ A₂
    rw [Fintype.card_fin] at h2
    linarith
  refine ⟨_, _, κ, κ₁, κ₂, f₁, f₂, hκ, hκ₁, hκ₂, ?_, ?_, hc₁.le, hc₂.le, ?_, ?_, ?_⟩
  · rw [hlaw₁, hL, ← dist_comp_eq]
    rfl
  · rw [hlaw₂, hL, ← dist_comp_eq]
    rfl
  · rw [condMutualInfo, hX₂, hX₁₂, ← mul_sub]
    exact hinvm (hsub₁.trans hM₁)
  · rw [condMutualInfo, hX₁, hX₂₁, ← mul_sub]
    exact hinvm (hsub₂.trans hM₂)
  · rw [mutualInfo_eq_entropy_sub_condEntropy hLP]
    have e : H[Prod.fst | Prod.snd ; jointOf P κ] =
        H[Prod.fst | pair (fun w : (α₁ × α₂) × Fin _ × Fin _ => w.2.1) (fun w => w.2.2) ;
          jointOf P κ] := rfl
    rw [e, hHZ, hX₁₂, ← mul_sub]
    refine hinvm ?_
    have : H[id ; iidPMF P n] - H[id | pair A₁ A₂ ; iidPMF P n] ≤ log M₁ + log M₂ := by
      linarith
    refine this.trans ?_
    rw [add_mul, mul_add]
    exact add_le_add hM₁ hM₂

/-- **Theorem 2 of Lecture 13 of [elgamal2010], page 13-14: the Berger–Tung outer bound.** If
`(R₁, R₂)`
is achievable with `(D₁, D₂)`, then the outer bound holds at `(R₁, R₂)` and `(D₁ + ε, D₂ + ε)`, for
every
`ε > 0`. -/
theorem IsAchievableDL.dlOuterAt (hP : IsPMF P) {R₁ R₂ D₁ D₂ : ℝ}
    (h : IsAchievableDL P d₁ d₂ R₁ R₂ D₁ D₂) {ε : ℝ} (hε : 0 < ε) :
    dlOuterAt P d₁ d₂ R₁ R₂ (D₁ + ε) (D₂ + ε) := by
  obtain ⟨hR₁, hR₂, c, hc⟩ := h
  obtain ⟨n, hn, hn0⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
  obtain ⟨k₁, k₂, κ, κ₁, κ₂, f₁, f₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    (c n).dlOuterAt_of_code (d₁ := d₁) (d₂ := d₂) hP hn0 (R₁ := R₁) (R₂ := R₂)
      (log_two_pow_floor_le n hR₁) (log_two_pow_floor_le n hR₂)
  exact ⟨k₁, k₂, κ, κ₁, κ₂, f₁, f₂, h1, h2, h3, h4, h5, h6.trans hn.1, h7.trans hn.2, h8, h9, h10⟩

end Code

end InfoTheory
