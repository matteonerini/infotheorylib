/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StateChannel.GPDerandomize
public import InfoTheoryLib.MutualInformation.CsiszarSum
public import InfoTheoryLib.StateChannel.Causal

/-!
# The Gelfand–Pinsker theorem

This file proves the converse of the Gelfand–Pinsker theorem and concludes: with the state available
noncausally at the encoder only, the capacity of the DMC with DM state is
`max_{p(u|s), x(u, s)} (I(U; Y) - I(U; S))`.

With `Uᵢ = (Yⁱ⁻¹, S_{i+1}ⁿ, M)`, the Csiszár sum identity gives
`I(M; Yⁿ) ≤ ∑ᵢ (I(Uᵢ; Yᵢ) - I(Uᵢ; Sᵢ))`, and each term is at most the Gelfand–Pinsker value by
`sub_le_gpValue_of_law`.

## Main statements

* `mutualInfo_le_sum_gp`: the single-letterization, for any random sequences.
* `StateCode.one_sub_errProb_mul_log_le_gpValue`: `(1 - P_e^(n)) log M ≤ log 2 + n C`.
* `stateCapacity_noncausal_false`: **the Gelfand–Pinsker theorem**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The single-letterization -/

section SingleLetter

variable {Ω 𝓜 σ β : Type*} [Fintype Ω] [Fintype 𝓜] [Fintype σ] [Fintype β] {μ : Ω → ℝ}

/-- The auxiliary random variable `Uᵢ = (Yⁱ⁻¹, S_{i+1}ⁿ, M)`. -/
def gpAux (S : ℕ → Ω → σ) (Y : ℕ → Ω → β) (M : Ω → 𝓜) (n i : ℕ) :
    Ω → (Fin i → β) × (Fin (n - (i + 1)) → σ) × 𝓜 :=
  pair (prefixRV Y i) (pair (suffixRV S (i + 1) n) M)

/-- `I(M; Yᵏ) = ∑_{i<k} I(M; Yᵢ | Yⁱ⁻¹)`. -/
lemma mutualInfo_prefixRV_eq_sum (hμ : IsPMF μ) (M : Ω → 𝓜) (Y : ℕ → Ω → β) (k : ℕ) :
    I[M : prefixRV Y k ; μ] = ∑ i ∈ range k, I[M : Y i | prefixRV Y i ; μ] := by
  induction k with
  | zero =>
    rw [mutualInfo_eq_entropy_sub_condEntropy' hμ]
    have h1 := entropyRV_le_log_card hμ (prefixRV Y 0)
    have h2 := condEntropy_nonneg hμ (prefixRV Y 0) M
    have h0 := entropyRV_nonneg hμ (prefixRV Y 0)
    have h3 := condEntropy_le_entropy hμ (prefixRV Y 0) M
    simp only [Fintype.card_unique, Nat.cast_one, log_one] at h1
    simp only [range_zero, sum_empty]
    linarith
  | succ k ih =>
    have h1 : I[M : prefixRV Y (k + 1) ; μ] = I[M : pair (Y k) (prefixRV Y k) ; μ] :=
      mutualInfo_congr_right hμ M (fun v : β × (Fin k → β) => (Fin.snoc v.2 v.1 : Fin (k + 1) → β))
        (fun a b hab => by
          have := snoc_injective2 (α := β) k (a₁ := (a.2, a.1)) (a₂ := (b.2, b.1)) hab
          simp only [Prod.mk.injEq] at this
          exact Prod.ext this.2 this.1)
        fun ω => prefixRV_succ Y k ω
    rw [h1, chain_rule_mutualInfo₂ hμ, ih, sum_range_succ]

/-- **Lecture 7 of [elgamal2010], pages 7-36 and 7-37.** If `(M, S_{i+1}ⁿ)` is independent of `Sᵢ`
for every `i`, then `I(M; Yⁿ) ≤ ∑ᵢ (I(Uᵢ; Yᵢ) - I(Uᵢ; Sᵢ))`, by the Csiszár sum identity. -/
theorem mutualInfo_le_sum_gp (hμ : IsPMF μ) (S : ℕ → Ω → σ) (Y : ℕ → Ω → β) (M : Ω → 𝓜) (n : ℕ)
    (hind : ∀ i < n, I[pair (suffixRV S (i + 1) n) M : S i ; μ] = 0) :
    I[M : prefixRV Y n ; μ] ≤
      ∑ i ∈ range n, (I[gpAux S Y M n i : Y i ; μ] - I[gpAux S Y M n i : S i ; μ]) := by
  have hcs := csiszar_sum hμ S Y M n
  have hY : ∀ i, I[M : Y i | prefixRV Y i ; μ] +
      I[suffixRV S (i + 1) n : Y i | pair (prefixRV Y i) M ; μ] ≤ I[gpAux S Y M n i : Y i ; μ] := by
    intro i
    have h1 : I[Y i : gpAux S Y M n i ; μ] =
        I[Y i : pair (suffixRV S (i + 1) n) (pair (prefixRV Y i) M) ; μ] :=
      mutualInfo_congr_right hμ (Y i)
        (fun a : (Fin (n - (i + 1)) → σ) × (Fin i → β) × 𝓜 => (a.2.1, a.1, a.2.2))
        (fun a b hab => by
          simp only [Prod.mk.injEq] at hab
          exact Prod.ext hab.2.1 (Prod.ext hab.1 hab.2.2)) (fun _ => rfl)
    have h2 := chain_rule_mutualInfo₂ hμ (Y i) (suffixRV S (i + 1) n) (pair (prefixRV Y i) M)
    have h3 : I[Y i : pair (prefixRV Y i) M ; μ] = I[Y i : pair M (prefixRV Y i) ; μ] :=
      mutualInfo_congr_right hμ (Y i) (fun a : 𝓜 × (Fin i → β) => (a.2, a.1))
        (fun a b hab => by
          simp only [Prod.mk.injEq] at hab
          exact Prod.ext hab.2 hab.1) (fun _ => rfl)
    have h4 := chain_rule_mutualInfo₂ hμ (Y i) M (prefixRV Y i)
    have h5 := mutualInfo_nonneg hμ (Y i) (prefixRV Y i)
    rw [mutualInfo_comm hμ (gpAux S Y M n i), h1, h2, h3, h4,
      condMutualInfo_comm hμ M, condMutualInfo_comm hμ (suffixRV S (i + 1) n)]
    linarith
  have hS : ∀ i < n, I[gpAux S Y M n i : S i ; μ] =
      I[prefixRV Y i : S i | pair (suffixRV S (i + 1) n) M ; μ] := by
    intro i hi
    have h1 := chain_rule_mutualInfo₂ hμ (S i) (prefixRV Y i) (pair (suffixRV S (i + 1) n) M)
    have h2 : I[S i : pair (suffixRV S (i + 1) n) M ; μ] = 0 := by
      rw [mutualInfo_comm hμ]
      exact hind i hi
    have e : gpAux S Y M n i = pair (prefixRV Y i) (pair (suffixRV S (i + 1) n) M) := rfl
    rw [mutualInfo_comm hμ, e, h1, h2, zero_add, condMutualInfo_comm hμ]
  rw [mutualInfo_prefixRV_eq_sum hμ]
  calc ∑ i ∈ range n, I[M : Y i | prefixRV Y i ; μ]
      = ∑ i ∈ range n, (I[M : Y i | prefixRV Y i ; μ] +
          I[suffixRV S (i + 1) n : Y i | pair (prefixRV Y i) M ; μ] -
          I[prefixRV Y i : S i | pair (suffixRV S (i + 1) n) M ; μ]) := by
        rw [sum_sub_distrib, sum_add_distrib, hcs]
        ring
    _ ≤ _ := sum_le_sum fun i hi => by
        rw [hS i (mem_range.1 hi)]
        linarith [hY i]

end SingleLetter

/-! ### The independence of the coordinates -/

section Coordinates

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
/-- If `F` does not depend on the coordinate `i` of the i.i.d. sequence, then
`E F(Sⁿ) g(Sᵢ) = E F(Sⁿ) · E g(S)`: use the involution `(sⁿ, a) ↦ (sⁿ with sᵢ = a, sᵢ)`. -/
lemma sum_iidPMF_mul_coord {p : σ → ℝ} (hp : IsPMF p) {n : ℕ} (i : Fin n) {F : (Fin n → σ) → ℝ}
    (hF : ∀ s a, F (Function.update s i a) = F s) (g : σ → ℝ) :
    ∑ s, iidPMF p n s * (F s * g (s i)) = (∑ s, iidPMF p n s * F s) * ∑ a, p a * g a := by
  classical
  set Φ : (Fin n → σ) × σ → (Fin n → σ) × σ := fun z => (Function.update z.1 i z.2, z.1 i)
  have hΦ : Function.Involutive Φ := fun z => by
    simp [Φ]
  have hiid : ∀ s a, iidPMF p n (Function.update s i a) * p (s i) = iidPMF p n s * p a := by
    intro s a
    simp only [iidPMF]
    rw [← mul_prod_erase univ _ (mem_univ i), ← mul_prod_erase univ (fun j => p (s j)) (mem_univ i)]
    have e : ∏ j ∈ univ.erase i, p (Function.update s i a j) = ∏ j ∈ univ.erase i, p (s j) :=
      prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.1 hj).1]
    rw [e, Function.update_self]
    ring
  have h := Equiv.sum_comp (hΦ.toPerm)
    (fun z : (Fin n → σ) × σ => iidPMF p n z.1 * (F z.1 * g (z.1 i)) * p z.2)
  have hL : ∑ z : (Fin n → σ) × σ, iidPMF p n z.1 * (F z.1 * g (z.1 i)) * p z.2 =
      ∑ s, iidPMF p n s * (F s * g (s i)) := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, hp.sum_eq_one, mul_one]
  have hR : ∑ z : (Fin n → σ) × σ, iidPMF p n (Φ z).1 * (F (Φ z).1 * g ((Φ z).1 i)) * p (Φ z).2 =
      (∑ s, iidPMF p n s * F s) * ∑ a, p a * g a := by
    rw [Fintype.sum_prod_type, sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [Φ, hF, Function.update_self]
    have := hiid s a
    linear_combination (F s * g a) * this
  rw [← hL, ← hR]
  exact h.symm

end Coordinates

/-! ### The law of a code -/

section Code

variable {σ α β : Type*} [Fintype σ] [Fintype α] [Fintype β] {W : α × σ → β → ℝ} {p : σ → ℝ}
  {𝒲 : Type*} [Fintype 𝒲] {ν : 𝒲 → ℝ} {𝒳 : Type*} {V : 𝒳 → β → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β) → 𝒳}

omit [Fintype σ] [Fintype α] in
/-- The marginal on the first outputs of the law of the message and the outputs. -/
lemma dist_fbLaw_restrict (hV : IsChannel V) {k n : ℕ} (h : k ≤ n) :
    dist (fbLaw ν V enc n) (fun z => (z.1, fun i : Fin k => z.2 (Fin.castLE h i))) =
      fbLaw ν V enc k := by
  classical
  induction n, h using Nat.le_induction with
  | base =>
    have : (fun z : 𝒲 × (Fin k → β) => (z.1, fun i : Fin k => z.2 (Fin.castLE le_rfl i))) = id := by
      funext z
      rfl
    rw [this, dist_id]
  | succ n hn ih =>
    have e : (fun z : 𝒲 × (Fin (n + 1) → β) =>
        (z.1, fun i : Fin k => z.2 (Fin.castLE (by omega) i))) =
        (fun z : 𝒲 × (Fin n → β) => (z.1, fun i : Fin k => z.2 (Fin.castLE hn i))) ∘
          fun z => (z.1, Fin.init z.2) := rfl
    rw [e, dist_comp_eq, dist_fbLaw_init hV n, ih]

omit [Fintype σ] [Fintype α] in
/-- Given the message and the past outputs, the output at time `i` is the output of the channel. -/
lemma dist_pair_fbLaw_coord (hV : IsChannel V) {n i : ℕ} (hi : i < n)
    (z : 𝒲 × (Fin i → β)) (b : β) :
    dist (fbLaw ν V enc n)
        (pair (fun ω => (ω.1, fun j : Fin i => ω.2 (Fin.castLE hi.le j))) fun ω => ω.2 ⟨i, hi⟩)
        (z, b) =
      dist (fbLaw ν V enc n) (fun ω => (ω.1, fun j : Fin i => ω.2 (Fin.castLE hi.le j))) z *
        V (enc i z.1 z.2) b := by
  classical
  obtain ⟨w, u⟩ := z
  have hG : Function.Injective fun v : 𝒲 × (Fin (i + 1) → β) =>
      (((v.1, Fin.init v.2), v.2 (Fin.last i)) : (𝒲 × (Fin i → β)) × β) := fun a c hac => by
    simp only [Prod.mk.injEq] at hac
    refine Prod.ext hac.1.1 ?_
    rw [← Fin.snoc_init_self a.2, ← Fin.snoc_init_self c.2, hac.1.2, hac.2]
  have e1 := dist_comp_of_injective (fbLaw ν V enc n)
    (fun z => (z.1, fun j : Fin (i + 1) => z.2 (Fin.castLE (by omega) j))) hG (w, Fin.snoc u b)
  rw [dist_fbLaw_restrict hV] at e1
  simp only [Fin.init_snoc, Fin.snoc_last] at e1
  rw [fbLaw_snoc] at e1
  have e2 := dist_fbLaw_restrict (ν := ν) (enc := enc) hV hi.le
  rw [e2]
  exact e1

omit [Fintype σ] [Fintype α] [Fintype β] [Fintype 𝒲] in
/-- If `Y` is a channel output given `Z`, depending on `Z` through `τ(Z)` and `ξ(Z)`, then
`p(t, y) = ∑ₐ p(t, a) K(y | t, a)`. -/
lemma dist_pair_comp_of_kernel {Ω ζ τ' 𝒜 β' : Type*} [Fintype Ω] [Finite ζ] [Finite τ']
    [Fintype 𝒜] [Finite β'] (μ : Ω → ℝ) (Z : Ω → ζ) (Y : Ω → β') (τ : ζ → τ') (ξ : ζ → 𝒜)
    (K : τ' → 𝒜 → β' → ℝ)
    (h : ∀ z b, dist μ (pair Z Y) (z, b) = dist μ Z z * K (τ z) (ξ z) b) (t : τ') (b : β') :
    dist μ (pair (τ ∘ Z) Y) (t, b) = ∑ a, dist μ (pair (τ ∘ Z) (ξ ∘ Z)) (t, a) * K t a b := by
  classical
  have := Fintype.ofFinite ζ
  have := Fintype.ofFinite τ'
  have := Fintype.ofFinite β'
  have e1 : dist μ (pair (τ ∘ Z) Y) (t, b) =
      ∑ z, if τ z = t then dist μ Z z * K t (ξ z) b else 0 := by
    have : pair (τ ∘ Z) Y = (fun q : ζ × β' => (τ q.1, q.2)) ∘ pair Z Y := rfl
    rw [this, dist_comp_eq]
    simp only [dist.eq_1 (dist μ (pair Z Y)), Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
    refine sum_congr rfl fun z _ => ?_
    by_cases hz : τ z = t
    · simp only [hz, ite_true]
      rw [sum_ite_eq' univ b]
      simp only [mem_univ, ite_true]
      rw [h, hz]
    · simp [hz]
  have e2 : ∀ a, dist μ (pair (τ ∘ Z) (ξ ∘ Z)) (t, a) =
      ∑ z, if τ z = t ∧ ξ z = a then dist μ Z z else 0 := fun a => by
    have : pair (τ ∘ Z) (ξ ∘ Z) = (fun z => (τ z, ξ z)) ∘ Z := rfl
    rw [this, dist_comp_eq]
    simp [dist.eq_1 (dist μ Z), Prod.mk.injEq]
  rw [e1]
  simp_rw [e2, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : τ z = t
  · simp only [hz, true_and, ite_true, ite_mul, zero_mul]
    rw [sum_ite_eq univ (ξ z)]
    simp
  · simp [hz]

/-- The law `p(m) p(sⁿ)` of the message and the state sequence. -/
def gpPrior (u : 𝒲 → ℝ) (p : σ → ℝ) (n : ℕ) : 𝒲 × (Fin n → σ) → ℝ :=
  fun w => u w.1 * iidPMF p n w.2

lemma gpPrior_isPMF {u : 𝒲 → ℝ} (hu : IsPMF u) (hp : IsPMF p) (n : ℕ) :
    IsPMF (gpPrior u p n) := by
  have hi := iidPMF_isPMF hp n
  refine ⟨fun w => mul_nonneg (hu.nonneg _) (hi.nonneg _), ?_⟩
  simp only [gpPrior, Fintype.sum_prod_type, ← mul_sum, hi.sum_eq_one, mul_one, hu.sum_eq_one]

lemma dist_gpPrior_fst {u : 𝒲 → ℝ} (hp : IsPMF p) (n : ℕ) :
    dist (gpPrior u p n) Prod.fst = u := by
  funext m
  rw [dist_fst]
  simp [gpPrior, ← mul_sum, (iidPMF_isPMF hp n).sum_eq_one]

/-- The sum over the prior of a function of `(m, sⁿ)`. -/
lemma sum_gpPrior (u : 𝒲 → ℝ) (p : σ → ℝ) (n : ℕ) (f : 𝒲 × (Fin n → σ) → ℝ) :
    ∑ w, gpPrior u p n w * f w = ∑ m, u m * ∑ s, iidPMF p n s * f (m, s) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun s _ => mul_assoc _ _ _

lemma dist_gpPrior_coord {u : 𝒲 → ℝ} (hu : IsPMF u) (hp : IsPMF p) {n : ℕ} (i : Fin n) :
    dist (gpPrior u p n) (fun w => w.2 i) = p := by
  classical
  funext b
  have h := sum_gpPrior u p n fun w => if w.2 i = b then 1 else 0
  have e : dist (gpPrior u p n) (fun w => w.2 i) b =
      ∑ w, gpPrior u p n w * (if w.2 i = b then 1 else 0) := by
    simp [dist]
  rw [e, h]
  have hc : ∀ m : 𝒲, u m * ∑ s : Fin n → σ, iidPMF p n s * (if s i = b then (1 : ℝ) else 0) =
      u m * p b := fun m => by
    congr 1
    simpa using sum_iidPMF_eval hp i fun a => if a = b then (1 : ℝ) else 0
  exact (sum_congr rfl fun m _ => hc m).trans (by rw [← sum_mul, hu.sum_eq_one, one_mul])

/-- `(M, S_{i+1}ⁿ)` is independent of `Sᵢ`. -/
lemma indepRV_gpPrior {u : 𝒲 → ℝ} (hu : IsPMF u) (hp : IsPMF p) {n : ℕ} (i : Fin n) {τ : Type*}
    [Finite τ] (T : (Fin n → σ) → τ) (hT : ∀ s a, T (Function.update s i a) = T s) :
    IndepRV (gpPrior u p n) (fun w => (T w.2, w.1)) (fun w => w.2 i) := by
  classical
  have := Fintype.ofFinite τ
  rintro ⟨t, m⟩ b
  have hF : ∀ s a, (if T (Function.update s i a) = t then (1 : ℝ) else 0) =
      if T s = t then 1 else 0 := fun s a => by rw [hT]
  have h1 : dist (gpPrior u p n) (pair (fun w => (T w.2, w.1)) fun w => w.2 i) ((t, m), b) =
      u m * ((∑ s, iidPMF p n s * if T s = t then 1 else 0) * p b) := by
    have e : dist (gpPrior u p n) (pair (fun w => (T w.2, w.1)) fun w => w.2 i) ((t, m), b) =
        ∑ w, gpPrior u p n w * (if w.1 = m then (if T w.2 = t then 1 else 0) *
          (if w.2 i = b then 1 else 0) else 0) := by
      simp only [dist, pair, Prod.mk.injEq]
      refine sum_congr rfl fun w _ => ?_
      by_cases h₁ : T w.2 = t <;> by_cases h₂ : w.1 = m <;> by_cases h₃ : w.2 i = b <;>
        simp [h₁, h₂, h₃]
    rw [e, sum_gpPrior]
    rw [sum_eq_single m (fun m' _ hm' => by simp [hm']) (by simp)]
    simp only [ite_true]
    have := sum_iidPMF_mul_coord hp i (F := fun s => if T s = t then 1 else 0) hF
      fun a => if a = b then 1 else 0
    rw [this]
    simp
  have h2 : dist (gpPrior u p n) (fun w => (T w.2, w.1)) (t, m) =
      u m * ∑ s, iidPMF p n s * if T s = t then 1 else 0 := by
    have e : dist (gpPrior u p n) (fun w => (T w.2, w.1)) (t, m) =
        ∑ w, gpPrior u p n w * (if w.1 = m then (if T w.2 = t then 1 else 0) else 0) := by
      simp only [dist, Prod.mk.injEq]
      refine sum_congr rfl fun w _ => ?_
      by_cases h₁ : T w.2 = t <;> by_cases h₂ : w.1 = m <;> simp [h₁, h₂]
    rw [e, sum_gpPrior]
    rw [sum_eq_single m (fun m' _ hm' => by simp [hm']) (by simp)]
    simp
  rw [h1, h2, dist_gpPrior_coord hu hp i]
  ring

/-- The channel inputs `(xᵢ, sᵢ)` of a code, for the message and the state sequence. -/
def StateCode.gpInput {M n : ℕ} (c : StateCode M n σ α β) : Fin M × (Fin n → σ) → Fin n → α × σ :=
  fun w => zipSeq (c.enc w.1 w.2) w.2

/-- The state at time `i`, with a default value out of range. -/
def stateAt {n : ℕ} (s₀ : σ) (i : ℕ) (s : Fin n → σ) : σ := if h : i < n then s ⟨i, h⟩ else s₀

omit [Fintype α] in
/-- **Converse of the Gelfand–Pinsker theorem (Lecture 7 of [elgamal2010]).** By Fano's inequality
and the Csiszár sum identity, a code using the state noncausally at the encoder only has
`(1 - P_e^(n)) log M ≤ log 2 + n C`. -/
theorem StateCode.one_sub_errProb_mul_log_le_gpValue [Finite α] [Nonempty α] (hW : IsChannel W)
    (hp : IsPMF p) {M n : ℕ} (hM : 0 < M) (c : StateCode M n σ α β) (hd : c.DecIgnoresState) :
    (1 - c.errProb W p) * log M ≤ log 2 + n * gpValue W p := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨s₀⟩ := hp.nonempty_type
  obtain ⟨x₀⟩ := ‹Nonempty α›
  have : Nonempty α := ⟨x₀⟩
  have : Nonempty (α × σ) := ⟨(x₀, s₀)⟩
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨y₀⟩ := (hW (x₀, s₀)).nonempty_type
  have hu : IsPMF (uniformPMF (Fin M)) := uniformPMF_isPMF
  have hν := gpPrior_isPMF hu hp n
  set ν := gpPrior (uniformPMF (Fin M)) p n
  set μ := fbLaw ν W (nfEnc c.gpInput) n
  have hμ : IsPMF μ := fbLaw_isPMF hν hW n
  have hfst : dist μ Prod.fst = ν := dist_fst_fbLaw hW n
  set S : ℕ → (Fin M × (Fin n → σ)) × (Fin n → β) → σ := fun i ω => stateAt s₀ i ω.1.2
  set Y : ℕ → (Fin M × (Fin n → σ)) × (Fin n → β) → β := fun i ω =>
    if h : i < n then ω.2 ⟨i, h⟩ else y₀
  set Mv : (Fin M × (Fin n → σ)) × (Fin n → β) → Fin M := fun ω => ω.1.1
  -- `(M, S_{i+1}ⁿ)` is independent of `Sᵢ`.
  have hind : ∀ i < n, I[pair (suffixRV S (i + 1) n) Mv : S i ; μ] = 0 := fun i hi => by
    set T : (Fin n → σ) → Fin (n - (i + 1)) → σ := fun s j => stateAt s₀ (i + 1 + j) s
    have hT : ∀ s a, T (Function.update s ⟨i, hi⟩ a) = T s := fun s a => by
      funext j
      simp only [T, stateAt]
      split_ifs with h
      · refine Function.update_of_ne ?_ _ _
        intro h'
        have := congrArg Fin.val h'
        simp only at this
        omega
      · rfl
    have hI := (mutualInfo_eq_zero_iff hν (fun w => (T w.2, w.1)) fun w => w.2 ⟨i, hi⟩).2
      (indepRV_gpPrior hu hp ⟨i, hi⟩ T hT)
    rw [← hI]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    have e : pair (pair (suffixRV S (i + 1) n) Mv) (S i) =
        (pair (fun w : Fin M × (Fin n → σ) => (T w.2, w.1)) fun w => w.2 ⟨i, hi⟩) ∘ Prod.fst := by
      funext ω
      simp only [pair, Function.comp, S, stateAt, hi, dite_true]
      rfl
    rw [e, dist_comp_eq, hfst]
  have hsl := mutualInfo_le_sum_gp hμ S Y Mv n hind
  -- Each term is at most the Gelfand–Pinsker value.
  have hletter : ∀ i ∈ range n,
      I[gpAux S Y Mv n i : Y i ; μ] - I[gpAux S Y Mv n i : S i ; μ] ≤ gpValue W p := fun i hi' => by
    have hi := mem_range.1 hi'
    set Z : (Fin M × (Fin n → σ)) × (Fin n → β) → (Fin M × (Fin n → σ)) × (Fin i → β) :=
      fun ω => (ω.1, fun j : Fin i => ω.2 (Fin.castLE hi.le j))
    set τ : (Fin M × (Fin n → σ)) × (Fin i → β) →
        σ × (Fin i → β) × (Fin (n - (i + 1)) → σ) × Fin M := fun z =>
      (z.1.2 ⟨i, hi⟩, z.2, (fun j : Fin (n - (i + 1)) => stateAt s₀ (i + 1 + j) z.1.2), z.1.1)
    set ξ : (Fin M × (Fin n → σ)) × (Fin i → β) → α := fun z => c.enc z.1.1 z.1.2 ⟨i, hi⟩
    have hYi : Y i = fun ω => ω.2 ⟨i, hi⟩ := by
      funext ω
      simp [Y, hi]
    have hτ1 : ∀ ω, (τ (Z ω)).1 = S i ω := fun ω => by
      simp [τ, Z, S, stateAt, hi]
    have hτ2 : ∀ ω, (τ (Z ω)).2 = gpAux S Y Mv n i ω := fun ω => by
      refine Prod.ext ?_ rfl
      funext j
      have hj : (j : ℕ) < n := lt_trans j.2 hi
      simp [τ, Z, gpAux, pair, prefixRV, Y, hj]
      rfl
    set K : (σ × (Fin i → β) × (Fin (n - (i + 1)) → σ) × Fin M) → α → β → ℝ :=
      fun t a b => W (a, t.1) b
    have hchan : ∀ z b, dist μ (pair Z (Y i)) (z, b) = dist μ Z z * K (τ z) (ξ z) b := fun z b => by
      rw [hYi]
      refine (dist_pair_fbLaw_coord hW hi z b).trans ?_
      congr 2
      simp [nfEnc, hi, StateCode.gpInput, zipSeq, τ, ξ]
    have gen := dist_pair_comp_of_kernel μ Z (Y i) τ ξ K hchan
    have hr : IsPMF (dist μ (pair (τ ∘ Z) (ξ ∘ Z))) := hμ.dist _
    have hS : dist (dist μ (pair (τ ∘ Z) (ξ ∘ Z))) (fun z => z.1.1) = p := by
      rw [← dist_comp_eq]
      have e : (fun z : (σ × (Fin i → β) × (Fin (n - (i + 1)) → σ) × Fin M) × α => z.1.1) ∘
          pair (τ ∘ Z) (ξ ∘ Z) = (fun w : Fin M × (Fin n → σ) => w.2 ⟨i, hi⟩) ∘ Prod.fst := rfl
      rw [e, dist_comp_eq, hfst]
      exact dist_gpPrior_coord hu hp ⟨i, hi⟩
    have law := sub_le_gpValue_of_law (𝒰 := (Fin i → β) × (Fin (n - (i + 1)) → σ) × Fin M) (β := β)
      hp hW hr hS
    have hJ : (fun z : (σ × (Fin i → β) × (Fin (n - (i + 1)) → σ) × Fin M) × β =>
        ∑ a, dist μ (pair (τ ∘ Z) (ξ ∘ Z)) (z.1, a) * W (a, z.1.1) z.2) =
        dist μ (pair (τ ∘ Z) (Y i)) := by
      funext ⟨t, b⟩
      exact (gen t b).symm
    rw [hJ] at law
    have h1 : I[fun z : (σ × (Fin i → β) × (Fin (n - (i + 1)) → σ) × Fin M) × β => z.1.2 :
        Prod.snd ; dist μ (pair (τ ∘ Z) (Y i))] = I[gpAux S Y Mv n i : Y i ; μ] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [← dist_comp_eq]
      congr 1
      funext ω
      exact Prod.ext (hτ2 ω) rfl
    have h2 : I[fun z : (σ × (Fin i → β) × (Fin (n - (i + 1)) → σ) × Fin M) × β => z.1.2 :
        fun z => z.1.1 ; dist μ (pair (τ ∘ Z) (Y i))] = I[gpAux S Y Mv n i : S i ; μ] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [← dist_comp_eq]
      congr 1
      funext ω
      exact Prod.ext (hτ2 ω) (hτ1 ω)
    rwa [h1, h2] at law
  have hsum : I[Mv : prefixRV Y n ; μ] ≤ n * gpValue W p := by
    refine hsl.trans ((sum_le_sum hletter).trans (le_of_eq ?_))
    simp
  -- Fano's inequality.
  have hYn : prefixRV Y n = Prod.snd := by
    funext ω i
    simp [prefixRV, Y, i.2]
  set s₀' : Fin n → σ := fun _ => s₀
  rw [hYn] at hsum
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ Mv Prod.snd
  have h2 := fano_weak hμ Mv Prod.snd (c.dec s₀')
  have hH : H[Mv ; μ] = log M := by
    have e : Mv = Prod.fst ∘ Prod.fst := rfl
    rw [entropyRV, e, dist_comp_eq, hfst, dist_gpPrior_fst hp, entropy_uniformPMF,
      Fintype.card_fin]
  have herr : InfoTheory.errProb μ Mv Prod.snd (c.dec s₀') = c.errProb W p := by
    simp only [InfoTheory.errProb, StateCode.errProb, StateCode.condErr]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_div]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun y _ => ?_
    have hdy : c.dec s y = c.dec s₀' y := hd s s₀' y
    simp only [Mv]
    rw [hdy]
    by_cases hw : c.dec s₀' y ≠ m
    · simp only [hw, ne_eq, not_false_eq_true, ite_true, μ, fbLaw_nfEnc]
      simp only [ν, gpPrior, uniformPMF, Fintype.card_fin]
      have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp
      rfl
    · simp [hw]
  rw [herr, Fintype.card_fin] at h2
  linarith [sub_mul 1 (c.errProb W p) (log (M : ℝ)), mul_comm (c.errProb W p) (log (M : ℝ))]

omit [Fintype α] in
/-- The converse: a rate achievable with the state noncausally at the encoder is at most the
Gelfand–Pinsker value. -/
theorem IsAchievableStateRate.le_gpValue [Finite α] [Nonempty α] (hW : IsChannel W)
    (hp : IsPMF p) {R : ℝ} (h : IsAchievableStateRate W p .noncausal false R) :
    R ≤ gpValue W p / log 2 := by
  obtain ⟨c, hc, hlim⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  exact le_div_log_two_of_converse hlim (fun n => (c n).errProb_le_one hW hp (hpos n))
    fun n => (c n).one_sub_errProb_mul_log_le_gpValue hW hp (hpos n) ((hc n).2 rfl)

omit [Fintype α] in
/-- **The Gelfand–Pinsker theorem (Lecture 7 of [elgamal2010]).** With the state available
noncausally at the encoder only, the capacity of the DMC with DM state is
`C_SI-E = max_{p(u|s), x(u, s)} (I(U; Y) - I(U; S))`, in bits. -/
theorem stateCapacity_noncausal_false [Finite α] [Nonempty α] (hW : IsChannel W) (hp : IsPMF p) :
    stateCapacity W p .noncausal false = gpValue W p / log 2 := by
  have := Fintype.ofFinite α
  have hl := log_pos one_lt_two
  obtain ⟨x₀⟩ := ‹Nonempty α›
  have : Nonempty α := ⟨x₀⟩
  refine sSup_eq_of_forall_mem (fun _ h => h.le_gpValue hW hp) fun R hR => ?_
  have hRC : R * log 2 < gpValue W p := (lt_div_iff₀ hl).1 hR
  have hne : Set.Nonempty {v | ∃ (k : ℕ) (ρ : σ → Fin k → ℝ) (x : Fin k → σ → α),
      (∀ s, IsPMF (ρ s)) ∧ gpRate p ρ x W = v} :=
    ⟨_, 1, fun _ _ => 1, fun _ _ => x₀, fun _ => ⟨fun _ => zero_le_one, by simp⟩, rfl⟩
  obtain ⟨_, ⟨k, ρ, x, hρ, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hRC
  exact isAchievableStateRate_noncausal_false_of_lt hp hρ hW x ((lt_div_iff₀ hl).2 hlt)

omit [Fintype α] in
/-- **Lecture 7 of [elgamal2010], page 7-38.** The cost of causality: the capacity with the state
causally at the encoder is at most the Gelfand–Pinsker capacity, as a causal code is a noncausal
code. -/
theorem causalValue_le_gpValue [Finite α] [Nonempty α] (hW : IsChannel W) (hp : IsPMF p) :
    causalValue W p ≤ gpValue W p := by
  classical
  have := Fintype.ofFinite α
  have hl := log_pos one_lt_two
  rw [causalValue_eq_capacity hW hp]
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  have hR : r / log 2 < capacity (strategyChannel W p fun f : σ → α => f) / log 2 :=
    div_lt_div_of_pos_right hr hl
  have := (isAchievableStateRate_causal_false_of_lt hW hp hR).causal_noncausal.le_gpValue hW hp
  exact (div_le_div_iff_of_pos_right hl).1 this

/-- `max_{p(u|s), x(u, s)} (I(U; Y) - I(U; S)) ≤ max_{p(x|s)} I(X; Y | S)`. -/
theorem gpValue_le_stateKnownValue [Nonempty α] (hW : IsChannel W) (hp : IsPMF p) :
    gpValue W p ≤ stateKnownValue W p := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  have : Nonempty α := ⟨x₀⟩
  refine csSup_le ⟨_, 1, fun _ _ => 1, fun _ _ => x₀, fun _ => ⟨fun _ => zero_le_one, by simp⟩,
    rfl⟩ ?_
  rintro _ ⟨k, ρ, x, hρ, rfl⟩
  exact gpRate_le_stateKnownValue hp hρ hW x

end Code

end InfoTheory
