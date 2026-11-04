/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StateChannel.GelfandPinsker

/-!
# Deterministic mappings in the Gelfand–Pinsker formula

The converse of the Gelfand–Pinsker theorem gives `I(U; Y) - I(U; S)` for a law `p(u, x | s)`, and
it remains to show that it suffices to consider `p(u | s)` and functions `x(u, s)`.

The notes observe that `I(U; Y)` is convex in `p(x | u, s)` for fixed `p(u | s)` and use the extreme
points. We avoid the extreme points: with `X = V(U, S)` for a random function `V` independent of
`(S, U)`, the pair `U' = (U, V)` satisfies `I(U'; S) = I(U; S)` and `I(U'; Y) ≥ I(U; Y)`, and `X` is
a function of `(U', S)`. The alphabet of `U` grows, which does not matter as it is not bounded here.

## Main statements

* `gpRate_le_gpValue`: `gpValue` bounds `gpRate` for `U` on any finite type.
* `gpMix_rate_le_gpValue`: the same for a random mapping `p(x | u, s)`.
* `sub_le_gpValue_of_law`: the same for any law `p(s, u, x)` with `S ∼ p(s)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {σ α β 𝒰 : Type*} [Fintype σ] [Fintype α] [Fintype β] [Fintype 𝒰]
  {p : σ → ℝ} {W : α × σ → β → ℝ}

omit [Fintype α] in
lemma bddAbove_gpValue [Finite α] [Nonempty α] (hp : IsPMF p) (hW : IsChannel W) :
    BddAbove {v | ∃ (k : ℕ) (ρ : σ → Fin k → ℝ) (x : Fin k → σ → α), (∀ s, IsPMF (ρ s)) ∧
      gpRate p ρ x W = v} := by
  have := Fintype.ofFinite α
  refine ⟨stateKnownValue W p, ?_⟩
  rintro _ ⟨k, ρ, x, hρ, rfl⟩
  exact gpRate_le_stateKnownValue hp hρ hW x

/-! ### Relabelling `U` -/

omit [Fintype σ] [Fintype α] [Fintype β] [Fintype 𝒰] in
/-- The law of a function under a relabelled sample space. -/
lemma dist_comp_equiv' {Ω Ω' γ : Type*} [Fintype Ω] [Fintype Ω'] (T : Ω' ≃ Ω) (μ : Ω → ℝ)
    (f : Ω → γ) : dist (fun ω => μ (T ω)) (fun ω => f (T ω)) = dist μ f := by
  classical
  funext a
  simp only [dist]
  exact T.sum_comp fun ω => if f ω = a then μ ω else 0

omit [Fintype σ] [Fintype α] [Fintype β] [Fintype 𝒰] in
/-- The mutual information does not depend on the labels. -/
lemma mutualInfo_relabel {Ω Ω' 𝒜 𝒜' γ : Type*} [Fintype Ω] [Fintype Ω'] [Fintype 𝒜] [Fintype 𝒜']
    [Fintype γ] (T : Ω' ≃ Ω) (E : 𝒜' ≃ 𝒜) {μ : Ω → ℝ} (hμ : IsPMF (fun ω => μ (T ω))) (A : Ω → 𝒜)
    (A' : Ω' → 𝒜') (hA : ∀ ω, A (T ω) = E (A' ω)) (Z : Ω → γ) :
    I[A : Z ; μ] = I[A' : fun ω => Z (T ω) ; fun ω => μ (T ω)] := by
  have h1 : I[A' : fun ω => Z (T ω) ; fun ω => μ (T ω)] =
      I[fun ω => A (T ω) : fun ω => Z (T ω) ; fun ω => μ (T ω)] := by
    rw [mutualInfo_comm hμ, mutualInfo_comm hμ (fun ω => A (T ω))]
    exact (mutualInfo_congr_right hμ _ E E.injective hA).symm
  rw [h1]
  refine mutualInfo_eq_of_dist_pair_eq ?_
  exact (dist_comp_equiv' T μ (pair A Z)).symm

omit [Fintype α] in
/-- The value `I(U; Y) - I(U; S)` does not depend on the labels of `U`. -/
lemma gpRate_le_gpValue [Finite α] [Nonempty α] (hp : IsPMF p) {ρ : σ → 𝒰 → ℝ}
    (hρ : ∀ s, IsPMF (ρ s)) (hW : IsChannel W) (x : 𝒰 → σ → α) : gpRate p ρ x W ≤ gpValue W p := by
  classical
  set E := Fintype.equivFin 𝒰
  set ρ' : σ → Fin (Fintype.card 𝒰) → ℝ := fun s i => ρ s (E.symm i)
  set x' : Fin (Fintype.card 𝒰) → σ → α := fun i s => x (E.symm i) s
  have hρ' : ∀ s, IsPMF (ρ' s) := fun s => ⟨fun i => (hρ s).nonneg _, by
    rw [← (hρ s).sum_eq_one]
    exact E.symm.sum_comp (ρ s)⟩
  refine le_of_eq_of_le ?_ (le_csSup (bddAbove_gpValue hp hW) ⟨_, ρ', x', hρ', rfl⟩)
  set T : (σ × Fin (Fintype.card 𝒰)) × β ≃ (σ × 𝒰) × β :=
    Equiv.prodCongr (Equiv.prodCongr (Equiv.refl σ) E.symm) (Equiv.refl β)
  have hμ' : IsPMF (fun ω => gpJoint p ρ x W (T ω)) := gpJoint_isPMF (x := x') hp hρ' hW
  have h1 := mutualInfo_relabel T E.symm hμ' (fun z : (σ × 𝒰) × β => z.1.2)
    (fun z => z.1.2) (fun _ => rfl) Prod.snd
  have h2 := mutualInfo_relabel T E.symm hμ' (fun z : (σ × 𝒰) × β => z.1.2)
    (fun z => z.1.2) (fun _ => rfl) (fun z => z.1.1)
  simp only [gpRate]
  rw [h1, h2]
  rfl

/-! ### A random mapping -/

/-- The channel `p(y | s, u) = ∑ₓ p(x | u, s) p(y | x, s)`. -/
def gpMix (κ : 𝒰 × σ → α → ℝ) (W : α × σ → β → ℝ) : σ × 𝒰 → β → ℝ :=
  fun z y => ∑ a, κ (z.2, z.1) a * W (a, z.1) y

omit [Fintype σ] [Fintype 𝒰] in
lemma gpMix_isChannel {κ : 𝒰 × σ → α → ℝ} (hκ : ∀ a, IsPMF (κ a)) (hW : IsChannel W) :
    IsChannel (gpMix κ W) := fun z => by
  refine ⟨fun y => sum_nonneg fun a _ => mul_nonneg ((hκ _).nonneg a) ((hW _).nonneg y), ?_⟩
  simp only [gpMix]
  rw [sum_comm]
  simp only [← mul_sum, (hW _).sum_eq_one, mul_one, (hκ _).sum_eq_one]

/-- **Lecture 7 of [elgamal2010], page 7-37.** It suffices to consider functions `x(u, s)`: for a
random mapping `p(x | u, s)`, the random function `V` with independent values
`V(u, s) ∼ p(x | u, s)` is independent of `(S, U)`, and `X = V(U, S)` is a function of
`U' = (U, V)` and `S`, with `I(U'; S) = I(U; S)` and `I(U'; Y) ≥ I(U; Y)`. -/
theorem gpMix_rate_le_gpValue [Nonempty α] (hp : IsPMF p) {ρ : σ → 𝒰 → ℝ} (hρ : ∀ s, IsPMF (ρ s))
    {κ : 𝒰 × σ → α → ℝ} (hκ : ∀ a, IsPMF (κ a)) (hW : IsChannel W) :
    I[fun z : (σ × 𝒰) × β => z.1.2 : Prod.snd ; jointOf (gpSU p ρ) (gpMix κ W)] -
      I[fun z : (σ × 𝒰) × β => z.1.2 : fun z => z.1.1 ; jointOf (gpSU p ρ) (gpMix κ W)] ≤
      gpValue W p := by
  classical
  have hP := prodPMF_isPMF hκ
  set P := prodPMF κ
  set ρ' : σ → 𝒰 × (𝒰 × σ → α) → ℝ := fun s z => ρ s z.1 * P z.2
  set x' : 𝒰 × (𝒰 × σ → α) → σ → α := fun z s => z.2 (z.1, s)
  have hρ' : ∀ s, IsPMF (ρ' s) := fun s => by
    refine ⟨fun z => mul_nonneg ((hρ s).nonneg _) (hP.nonneg _), ?_⟩
    simp only [ρ', Fintype.sum_prod_type, ← mul_sum, hP.sum_eq_one, mul_one, (hρ s).sum_eq_one]
  set J' := gpJoint p ρ' x' W
  set Jr := jointOf (gpSU p ρ) (gpMix κ W)
  have hJ' : IsPMF J' := gpJoint_isPMF hp hρ' hW
  have hJr : IsPMF Jr := jointOf_isPMF (gpSU_isPMF hp hρ) (gpMix_isChannel hκ hW)
  set proj : (σ × 𝒰 × (𝒰 × σ → α)) × β → (σ × 𝒰) × β := fun z => ((z.1.1, z.1.2.1), z.2)
  have hproj : dist J' proj = Jr := by
    funext ⟨⟨s, u⟩, y⟩
    simp only [dist, proj, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
    rw [sum_eq_single s (fun s' _ h => by simp [h]) (by simp)]
    simp only [ite_true]
    rw [sum_eq_single u (fun u' _ h => by simp [h]) (by simp)]
    simp only [ite_true]
    have e : ∀ v : 𝒰 × σ → α, (∑ y', if y' = y then J' ((s, u, v), y') else 0) =
        p s * ρ s u * (P v * W (v (u, s), s) y) := fun v => by
      rw [sum_ite_eq' univ y]
      simp only [mem_univ, ite_true, J', gpJoint, jointOf, gpSU, gpChannel, ρ', x']
      ring
    simp_rw [e, ← mul_sum]
    rw [sum_prodPMF_mul_eval hκ (u, s) fun a => W (a, s) y]
    rfl
  -- The pieces of `U' = (U, V)`.
  set Sv : (σ × 𝒰 × (𝒰 × σ → α)) × β → σ := fun z => z.1.1
  set Uv : (σ × 𝒰 × (𝒰 × σ → α)) × β → 𝒰 := fun z => z.1.2.1
  set Vv : (σ × 𝒰 × (𝒰 × σ → α)) × β → (𝒰 × σ → α) := fun z => z.1.2.2
  set Up : (σ × 𝒰 × (𝒰 × σ → α)) × β → 𝒰 × (𝒰 × σ → α) := fun z => z.1.2
  have hY : I[Uv : Prod.snd ; J'] =
      I[fun z : (σ × 𝒰) × β => z.1.2 : Prod.snd ; Jr] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [← hproj, ← dist_comp_eq]
    rfl
  have hS : I[Uv : Sv ; J'] =
      I[fun z : (σ × 𝒰) × β => z.1.2 : fun z => z.1.1 ; Jr] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [← hproj, ← dist_comp_eq]
    rfl
  -- `I(U'; Y) ≥ I(U; Y)`.
  have hYle : I[Uv : Prod.snd ; J'] ≤ I[Up : Prod.snd ; J'] := by
    rw [mutualInfo_comm hJ', mutualInfo_comm hJ' Up]
    exact mutualInfo_comp_le hJ' Prod.snd Up Prod.fst
  -- `V` is independent of `(S, U)`.
  have hSU : ∀ s u, dist J' (pair Sv Uv) (s, u) = gpSU p ρ (s, u) := fun s u => by
    have e : pair Sv Uv = Prod.fst ∘ proj := rfl
    rw [e, dist_comp_eq, hproj]
    exact congrFun (dist_jointOf_fst (gpMix_isChannel hκ hW)) (s, u)
  have hJ'fst : dist J' Prod.fst = gpSU p ρ' := margFst_gpJoint hW
  have hjoint : ∀ v s u, dist J' (pair Vv (pair Sv Uv)) (v, (s, u)) = P v * gpSU p ρ (s, u) :=
    fun v s u => by
      have hinj : Function.Injective
          (fun a : σ × 𝒰 × (𝒰 × σ → α) => (a.2.2, (a.1, a.2.1))) := fun a b hab => by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext hab.2.1 (Prod.ext hab.2.2 hab.1)
      have := dist_comp_of_injective J' Prod.fst hinj (s, u, v)
      rw [hJ'fst] at this
      refine this.trans ?_
      simp only [gpSU, ρ']
      ring
  have hV : ∀ v, dist J' Vv v = P v := fun v => by
    rw [← sum_dist_pair_right J' Vv (pair Sv Uv) v, Fintype.sum_prod_type]
    simp_rw [hjoint, ← mul_sum]
    have := (gpSU_isPMF hp hρ).sum_eq_one
    rw [Fintype.sum_prod_type] at this
    rw [this, mul_one]
  have hind : IndepRV J' Vv (pair Sv Uv) := fun v ⟨s, u⟩ => by
    rw [hjoint, hV, hSU]
  have hI0 : I[Vv : pair Sv Uv ; J'] = 0 := (mutualInfo_eq_zero_iff hJ' _ _).2 hind
  have hcond : I[Vv : Sv | Uv ; J'] = 0 := by
    have h1 := chain_rule_mutualInfo₂ hJ' Vv Sv Uv
    have h2 := mutualInfo_nonneg hJ' Vv Uv
    have h3 := condMutualInfo_nonneg hJ' Vv Sv Uv
    linarith
  have hSeq : I[Up : Sv ; J'] = I[Uv : Sv ; J'] := by
    have h1 : I[Sv : Up ; J'] = I[Sv : pair Vv Uv ; J'] :=
      mutualInfo_congr_right hJ' Sv (fun a : (𝒰 × σ → α) × 𝒰 => (a.2, a.1))
        (fun a b hab => by
          simp only [Prod.mk.injEq] at hab
          exact Prod.ext hab.2 hab.1) (fun _ => rfl)
    have h2 := chain_rule_mutualInfo₂ hJ' Sv Vv Uv
    have h3 : I[Sv : Vv | Uv ; J'] = 0 := by rw [condMutualInfo_comm hJ', hcond]
    rw [mutualInfo_comm hJ', h1, h2, h3, add_zero, mutualInfo_comm hJ']
  have hfinal := gpRate_le_gpValue hp hρ' hW x'
  have hrate : gpRate p ρ' x' W = I[Up : Prod.snd ; J'] - I[Up : Sv ; J'] := rfl
  rw [hrate, hSeq] at hfinal
  rw [← hY, ← hS]
  linarith

/-! ### A law `p(s, u, x)` -/

omit [Fintype σ] [Fintype α] [Fintype β] [Fintype 𝒰] in
/-- A pmf on a product is a marginal times a kernel. -/
lemma exists_kernel {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] {r : A × B → ℝ}
    (hr : IsPMF r) : ∃ κ : A → B → ℝ, (∀ a, IsPMF (κ a)) ∧
      ∀ a b, r (a, b) = dist r Prod.fst a * κ a b := by
  classical
  have hm : ∀ a, dist r Prod.fst a = ∑ b, r (a, b) := fun a => dist_fst r a
  have h0 : ∀ a, dist r Prod.fst a = 0 → ∀ b, r (a, b) = 0 := fun a ha b => by
    rw [hm] at ha
    exact (sum_eq_zero_iff_of_nonneg fun b _ => hr.nonneg _).1 ha b (mem_univ b)
  refine ⟨fun a b => if dist r Prod.fst a = 0 then uniformPMF B b else
    r (a, b) / dist r Prod.fst a, fun a => ?_, fun a b => ?_⟩
  · by_cases ha : dist r Prod.fst a = 0
    · simpa [ha] using (uniformPMF_isPMF : IsPMF (uniformPMF B))
    · have hpos : 0 < dist r Prod.fst a :=
        lt_of_le_of_ne ((hr.dist _).nonneg a) (Ne.symm ha)
      simp only [ha, ite_false]
      refine ⟨fun b => div_nonneg (hr.nonneg _) hpos.le, ?_⟩
      rw [← sum_div, ← hm, div_self ha]
  · by_cases ha : dist r Prod.fst a = 0
    · simp [ha, h0 a ha b]
    · simp only [ha, ite_false]
      field_simp

/-- **Lecture 7 of [elgamal2010], page 7-37.** For any law `p(s, u, x)` with `S ∼ p(s)` and
`Y ∼ p(y | x, s)` given `(S, U, X)`, `I(U; Y) - I(U; S)` is at most the Gelfand–Pinsker value. -/
theorem sub_le_gpValue_of_law (hp : IsPMF p) (hW : IsChannel W) {r : (σ × 𝒰) × α → ℝ}
    (hr : IsPMF r) (hS : dist r (fun z => z.1.1) = p) :
    I[fun z : (σ × 𝒰) × β => z.1.2 : Prod.snd ;
        fun z => ∑ a, r (z.1, a) * W (a, z.1.1) z.2] -
      I[fun z : (σ × 𝒰) × β => z.1.2 : fun z => z.1.1 ;
        fun z => ∑ a, r (z.1, a) * W (a, z.1.1) z.2] ≤ gpValue W p := by
  classical
  have hne : Nonempty ((σ × 𝒰) × α) := hr.nonempty_type
  have : Nonempty α := ⟨hne.some.2⟩
  have : Nonempty 𝒰 := ⟨hne.some.1.2⟩
  have hSU : IsPMF (dist r Prod.fst) := hr.dist _
  obtain ⟨ρ, hρ, hρe⟩ := exists_kernel hSU
  obtain ⟨κ₀, hκ₀, hκe⟩ := exists_kernel hr
  have hm : dist (dist r Prod.fst) Prod.fst = p := by
    rw [← dist_comp_eq]
    exact hS
  rw [hm] at hρe
  set κ : 𝒰 × σ → α → ℝ := fun a => κ₀ (a.2, a.1)
  have hJ : (fun z : (σ × 𝒰) × β => ∑ a, r (z.1, a) * W (a, z.1.1) z.2) =
      jointOf (gpSU p ρ) (gpMix κ W) := by
    funext ⟨⟨s, u⟩, y⟩
    simp only [jointOf, gpSU, gpMix, κ, mul_sum, ← hρe]
    refine sum_congr rfl fun a _ => ?_
    rw [hκe (s, u) a]
    ring
  rw [hJ]
  exact gpMix_rate_le_gpValue hp hρ (fun a => hκ₀ _) hW

end InfoTheory
