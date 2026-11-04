/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACBounds
public import InfoTheoryLib.Network.MACConverse

/-!
# The multi-letter characterization of the capacity region of the multiple access channel

Theorem 1 of Lecture 4 of El Gamal and Kim characterizes the capacity region of the DM-MAC through
`k` uses of the channel: `𝒞_k` is the set of rate pairs with `R₁ ≤ (1/k) I(X₁ᵏ; Yᵏ)` and
`R₂ ≤ (1/k) I(X₂ᵏ; Yᵏ)` for some product input distribution `p(x₁ᵏ) p(x₂ᵏ)`, and the capacity
region is the closure of `⋃ₖ 𝒞_k`.

## Main definitions

* `macChannel₁ W p₂`, `macChannel₂ W p₁`: the channel from one input when the other input has law
  `p₂` (resp. `p₁`), so that `I(X₁; Y) = mutualInfoOf p₁ (macChannel₁ W p₂)`.
* `macExt W k`: `k` uses of the multiple access channel, as a multiple access channel with input
  alphabets `𝒳₁ᵏ` and `𝒳₂ᵏ`.
* `macMultiLetterRegion W k`, `macMultiLetterRegionBits W k`: the region `𝒞_k`, in nats and in
  bits.

## Main statements

* `macMultiLetterRegion_subset_macRegion`: `𝒞_k` lies in the single-letter region, by the same
  steps as the converse: `I(X₁ᵏ; Yᵏ) ≤ I(X₁ᵏ; Yᵏ | X₂ᵏ) ≤ ∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ)`.
* `MACCode.log_le_mutualInfoOf₁`, `MACCode.log_le_mutualInfoOf₂`: Fano's inequality,
  `log M₁ ≤ I(X₁ⁿ; Yⁿ) + log 2 + P_e^(n) log (M₁ M₂)` for a single code.
* `macCapacityRegion_eq_closure_iUnion`, `macCapacityRegionBits_eq_closure_iUnion`:
  **Theorem 1 of [elgamal2010], Lecture 4 (van der Meulen)**.

## Implementation notes

The notes prove `𝒞_k ⊆ 𝒞` by coding over super-letters of `k` symbols. We derive it from the
single-letter characterization instead, as `𝒞_k` lies in the region of Theorem 3 with a time
sharing variable uniform on the `k` positions. The notes write `𝒞 = ⋃ₖ 𝒞_k`; the union need not
be closed, and the capacity region is its closure.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 4
-/

open Real Finset Filter Topology Set

open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The channel from one input -/

section General

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}
  {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ}

/-- The channel `p(y | x₁) = ∑_{x₂} p₂(x₂) p(y | x₁, x₂)` from the first input, when the second
input is independent with law `p₂`. -/
def macChannel₁ (W : α₁ × α₂ → β → ℝ) (p₂ : α₂ → ℝ) : α₁ → β → ℝ :=
  fun a => outDist p₂ fun b => W (a, b)

/-- The channel `p(y | x₂) = ∑_{x₁} p₁(x₁) p(y | x₁, x₂)` from the second input. -/
def macChannel₂ (W : α₁ × α₂ → β → ℝ) (p₁ : α₁ → ℝ) : α₂ → β → ℝ :=
  fun b => outDist p₁ fun a => W (a, b)

omit [Fintype α₁] in
lemma macChannel₁_isChannel (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    IsChannel (macChannel₁ W p₂) := fun a => outDist_isPMF hp₂ fun b => hW (a, b)

omit [Fintype α₂] in
lemma macChannel₂_isChannel (hp₁ : IsPMF p₁) (hW : IsChannel W) :
    IsChannel (macChannel₂ W p₁) := fun b => outDist_isPMF hp₁ fun a => hW (a, b)

/-- `I(X₁; Y)` for independent inputs is the mutual information of the channel from `X₁`. -/
lemma mutualInfoOf_macChannel₁ (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    mutualInfoOf p₁ (macChannel₁ W p₂) =
      I[fun z : (α₁ × α₂) × β => z.1.1 : Prod.snd ; macJoint p₁ p₂ W] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [dist_pair_fst_snd]
  funext ⟨a, y⟩
  rw [dist_macJoint_fst_out hp₂ hW, dist_macJoint_fst hp₂ hW]
  rfl

/-- `I(X₂; Y)` for independent inputs is the mutual information of the channel from `X₂`. -/
lemma mutualInfoOf_macChannel₂ (hp₁ : IsPMF p₁) (hW : IsChannel W) :
    mutualInfoOf p₂ (macChannel₂ W p₁) =
      I[fun z : (α₁ × α₂) × β => z.1.2 : Prod.snd ; macJoint p₁ p₂ W] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [dist_pair_fst_snd]
  funext ⟨b, y⟩
  rw [dist_macJoint_snd_out hp₁ hW, dist_macJoint_snd hp₁ hW]
  rfl

/-- For independent inputs, `I(X₁; Y) ≤ I(X₁; Y | X₂)`. -/
lemma mutualInfoOf_macChannel₁_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    mutualInfoOf p₁ (macChannel₁ W p₂) ≤ macInfo₁ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  rw [mutualInfoOf_macChannel₁ hp₂ hW, mutualInfo_comm hμ]
  linarith [macInfo₁₂_eq_add₂ hp₁ hp₂ hW, macInfo₁₂_le_add hp₁ hp₂ hW]

/-- For independent inputs, `I(X₂; Y) ≤ I(X₂; Y | X₁)`. -/
lemma mutualInfoOf_macChannel₂_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    mutualInfoOf p₂ (macChannel₂ W p₁) ≤ macInfo₂ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  rw [mutualInfoOf_macChannel₂ hp₁ hW, mutualInfo_comm hμ]
  linarith [macInfo₁₂_eq_add₁ hp₁ hp₂ hW, macInfo₁₂_le_add hp₁ hp₂ hW]

/-- For independent inputs, `I(X₁; Y) + I(X₂; Y) ≤ I(X₁, X₂; Y)`. -/
lemma add_mutualInfoOf_macChannel_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    mutualInfoOf p₁ (macChannel₁ W p₂) + mutualInfoOf p₂ (macChannel₂ W p₁) ≤
      macInfo₁₂ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  rw [mutualInfoOf_macChannel₁ hp₂ hW, mutualInfoOf_macChannel₂ hp₁ hW, mutualInfo_comm hμ,
    mutualInfo_comm hμ (fun z : (α₁ × α₂) × β => z.1.2)]
  linarith [macInfo₁₂_eq_add₁ hp₁ hp₂ hW, macInfo₁₂_eq_add₂ hp₁ hp₂ hW,
    macInfo₁₂_le_add hp₁ hp₂ hW]

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
/-- The marginals of a product: `(f(X), g(X'))` has law `p_f(X) p_g(X')`. -/
lemma dist_prodDist_map {γ δ ε ζ : Type*} [Fintype γ] [Fintype δ] {p : γ → ℝ} {q : δ → ℝ}
    (f : γ → ε) (g : δ → ζ) :
    dist (prodDist p q) (fun w => (f w.1, g w.2)) = prodDist (dist p f) (dist q g) := by
  classical
  funext ⟨a, b⟩
  simp only [dist, prodDist, Fintype.sum_prod_type, Prod.mk.injEq]
  rw [sum_mul_sum]
  refine sum_congr rfl fun w _ => sum_congr rfl fun w' _ => ?_
  by_cases ha : f w = a <;> by_cases hb : g w' = b <;> simp [ha, hb]

end General

/-! ### `k` uses of the channel -/

section Block

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ} {k : ℕ}
  {P₁ : (Fin k → α₁) → ℝ} {P₂ : (Fin k → α₂) → ℝ}

/-- `k` uses of the memoryless multiple access channel `W`, as a multiple access channel with
inputs `x₁ᵏ` and `x₂ᵏ` and output `yᵏ`. -/
def macExt (W : α₁ × α₂ → β → ℝ) (k : ℕ) : (Fin k → α₁) × (Fin k → α₂) → (Fin k → β) → ℝ :=
  fun x => channelExt W k (zipSeq x.1 x.2)

omit [Fintype α₁] [Fintype α₂] in
lemma macExt_isChannel (hW : IsChannel W) (k : ℕ) : IsChannel (macExt W k) :=
  fun x => (hW.ext k) (zipSeq x.1 x.2)

/-- The law of `((X₁ᵢ, X₂ᵢ), Yᵢ)` for product block inputs is `p₁ᵢ(x₁) p₂ᵢ(x₂) p(y | x₁, x₂)`. -/
lemma dist_macJoint_macExt_letter (hW : IsChannel W) (i : Fin k) :
    dist (macJoint P₁ P₂ (macExt W k)) (fun z => ((z.1.1 i, z.1.2 i), z.2 i)) =
      macJoint (dist P₁ fun x => x i) (dist P₂ fun x => x i) W := by
  funext ⟨u, b⟩
  have h := dist_codeLaw_letter (ν := prodDist P₁ P₂) (x := fun w => zipSeq w.1 w.2) hW
    (fun w : (Fin k → α₁) × (Fin k → α₂) => (w.1 i, w.2 i)) id i (fun w => rfl) u b
  have hX : dist (codeLaw (prodDist P₁ P₂) W fun w => zipSeq w.1 w.2)
      ((fun w : (Fin k → α₁) × (Fin k → α₂) => (w.1 i, w.2 i)) ∘ Prod.fst) =
      prodDist (dist P₁ fun x => x i) (dist P₂ fun x => x i) := by
    rw [dist_codeLaw_comp_fst hW]
    exact dist_prodDist_map (p := P₁) (q := P₂) (fun x : Fin k → α₁ => x i)
      (fun x : Fin k → α₂ => x i)
  rw [hX] at h
  exact h

/-- The three single-letterization steps, for product block inputs. -/
theorem macInfo_macExt_le (hP₁ : IsPMF P₁) (hP₂ : IsPMF P₂) (hW : IsChannel W) :
    macInfo₁ P₁ P₂ (macExt W k) ≤ ∑ i, macInfo₁ (dist P₁ fun x => x i) (dist P₂ fun x => x i) W ∧
    macInfo₂ P₁ P₂ (macExt W k) ≤ ∑ i, macInfo₂ (dist P₁ fun x => x i) (dist P₂ fun x => x i) W ∧
    macInfo₁₂ P₁ P₂ (macExt W k) ≤
      ∑ i, macInfo₁₂ (dist P₁ fun x => x i) (dist P₂ fun x => x i) W := by
  set μ := macJoint P₁ P₂ (macExt W k)
  have hμ : IsPMF μ := macJoint_isPMF hP₁ hP₂ (macExt_isChannel hW k)
  set X₁ : ((Fin k → α₁) × (Fin k → α₂)) × (Fin k → β) → Fin k → α₁ := fun z => z.1.1
  set X₂ : ((Fin k → α₁) × (Fin k → α₂)) × (Fin k → β) → Fin k → α₂ := fun z => z.1.2
  set Y : ((Fin k → α₁) × (Fin k → α₂)) × (Fin k → β) → Fin k → β := Prod.snd
  set L := fun i : Fin k =>
    fun z : ((Fin k → α₁) × (Fin k → α₂)) × (Fin k → β) => ((z.1.1 i, z.1.2 i), z.2 i)
  have hL := fun i => dist_macJoint_macExt_letter (P₁ := P₁) (P₂ := P₂) hW i
  -- `H(Yᵏ | X₁ᵏ, X₂ᵏ) = ∑ᵢ H(Yᵢ | X₁ᵢ, X₂ᵢ)`.
  have hcond : H[Y | Prod.fst ; μ] = ∑ i, H[fun z => z.2 i | fun z => (z.1.1 i, z.1.2 i) ; μ] :=
    condEntropy_codeLaw (ν := prodDist P₁ P₂) (x := fun w => zipSeq w.1 w.2) hW
  -- Each letter.
  have hlet₁ : ∀ i, H[fun z => z.2 i | fun z => z.1.2 i ; μ] -
      H[fun z => z.2 i | fun z => (z.1.1 i, z.1.2 i) ; μ] =
      macInfo₁ (dist P₁ fun x => x i) (dist P₂ fun x => x i) W := fun i => by
    have e1 := condMutualInfo_comp hμ (L i) (fun t => t.1.1) Prod.snd (fun t => t.1.2)
    rw [hL i] at e1
    rw [macInfo₁, ← e1, condMutualInfo_comm hμ, condMutualInfo]
    rfl
  have hlet₂ : ∀ i, H[fun z => z.2 i | fun z => z.1.1 i ; μ] -
      H[fun z => z.2 i | fun z => (z.1.1 i, z.1.2 i) ; μ] =
      macInfo₂ (dist P₁ fun x => x i) (dist P₂ fun x => x i) W := fun i => by
    have e1 := condMutualInfo_comp hμ (L i) (fun t => t.1.2) Prod.snd (fun t => t.1.1)
    rw [hL i] at e1
    rw [macInfo₂, ← e1, condMutualInfo_comm hμ, condMutualInfo]
    exact congrArg _ (condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl)
  have hlet₁₂ : ∀ i, H[fun z => z.2 i ; μ] -
      H[fun z => z.2 i | fun z => (z.1.1 i, z.1.2 i) ; μ] =
      macInfo₁₂ (dist P₁ fun x => x i) (dist P₂ fun x => x i) W := fun i => by
    have e1 := mutualInfo_comp (μ := μ) (L i) Prod.fst Prod.snd
    rw [hL i] at e1
    rw [macInfo₁₂, ← e1, mutualInfo_eq_entropy_sub_condEntropy' hμ]
    rfl
  -- The block quantities.
  have hY₂ : H[Y | X₂ ; μ] ≤ ∑ i, H[fun z => z.2 i | fun z => z.1.2 i ; μ] :=
    (condEntropy_pi_le_sum hμ Y X₂).trans (sum_le_sum fun i _ =>
      condEntropy_le_condEntropy_comp hμ _ X₂ (fun x => x i))
  have hY₁ : H[Y | X₁ ; μ] ≤ ∑ i, H[fun z => z.2 i | fun z => z.1.1 i ; μ] :=
    (condEntropy_pi_le_sum hμ Y X₁).trans (sum_le_sum fun i _ =>
      condEntropy_le_condEntropy_comp hμ _ X₁ (fun x => x i))
  have hY : H[Y ; μ] ≤ ∑ i, H[fun z => z.2 i ; μ] := by
    have := condEntropy_pi_le_sum hμ Y (fun _ => ())
    simp only [condEntropy_const hμ] at this
    exact this
  have hI₁ : macInfo₁ P₁ P₂ (macExt W k) = H[Y | X₂ ; μ] - H[Y | Prod.fst ; μ] := by
    rw [macInfo₁, condMutualInfo_comm hμ, condMutualInfo]
    rfl
  have hI₂ : macInfo₂ P₁ P₂ (macExt W k) = H[Y | X₁ ; μ] - H[Y | Prod.fst ; μ] := by
    rw [macInfo₂, condMutualInfo_comm hμ, condMutualInfo]
    exact congrArg _ (condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl)
  have hI₁₂ : macInfo₁₂ P₁ P₂ (macExt W k) = H[Y ; μ] - H[Y | Prod.fst ; μ] := by
    rw [macInfo₁₂, mutualInfo_eq_entropy_sub_condEntropy' hμ]
  refine ⟨?_, ?_, ?_⟩
  · rw [hI₁, hcond, ← sum_congr rfl fun i _ => hlet₁ i, sum_sub_distrib]
    linarith
  · rw [hI₂, hcond, ← sum_congr rfl fun i _ => hlet₂ i, sum_sub_distrib]
    linarith
  · rw [hI₁₂, hcond, ← sum_congr rfl fun i _ => hlet₁₂ i, sum_sub_distrib]
    linarith

end Block

/-! ### The region `𝒞_k` -/

section Region

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}

/-- **Theorem 1 of [elgamal2010], Lecture 4.** The region `𝒞_k`: the rate pairs (in nats) with
`R₁ ≤ (1/k) I(X₁ᵏ; Yᵏ)` and `R₂ ≤ (1/k) I(X₂ᵏ; Yᵏ)` for some product input distribution
`p(x₁ᵏ) p(x₂ᵏ)`. -/
def macMultiLetterRegion (W : α₁ × α₂ → β → ℝ) (k : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ (P₁ : (Fin k → α₁) → ℝ) (P₂ : (Fin k → α₂) → ℝ), IsPMF P₁ ∧ IsPMF P₂ ∧
    R.1 ≤ mutualInfoOf P₁ (macChannel₁ (macExt W k) P₂) / k ∧
    R.2 ≤ mutualInfoOf P₂ (macChannel₂ (macExt W k) P₁) / k}

/-- `𝒞_k` lies in the single-letter region, with a time sharing variable uniform on the `k`
positions. -/
theorem macMultiLetterRegion_subset_macRegion (hW : IsChannel W) {k : ℕ} (hk : 0 < k) :
    macMultiLetterRegion W k ⊆ macRegion W := by
  rintro R ⟨P₁, P₂, hP₁, hP₂, h₁, h₂⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hV := macExt_isChannel hW k
  obtain ⟨b₁, b₂, b₃⟩ := macInfo_macExt_le hP₁ hP₂ hW
  have hq : IsPMF (fun _ : Fin k => (1 : ℝ) / k) := ⟨fun _ => by positivity, by simp [hk'.ne']⟩
  have hm₁ : ∀ i : Fin k, IsPMF (dist P₁ fun x => x i) := fun i => hP₁.dist _
  have hm₂ : ∀ i : Fin k, IsPMF (dist P₂ fun x => x i) := fun i => hP₂.dist _
  refine ⟨k, fun _ => 1 / k, fun i => dist P₁ fun x => x i, fun i => dist P₂ fun x => x i, hq,
    hm₁, hm₂, ?_, ?_, ?_⟩ <;> rw [← mul_sum, one_div_mul_eq_div]
  · exact h₁.trans (div_le_div_of_nonneg_right
      ((mutualInfoOf_macChannel₁_le hP₁ hP₂ hV).trans b₁) hk'.le)
  · exact h₂.trans (div_le_div_of_nonneg_right
      ((mutualInfoOf_macChannel₂_le hP₁ hP₂ hV).trans b₂) hk'.le)
  · have := add_le_add h₁ h₂
    rw [← add_div] at this
    exact this.trans (div_le_div_of_nonneg_right
      ((add_mutualInfoOf_macChannel_le hP₁ hP₂ hV).trans b₃) hk'.le)

end Region

/-! ### Fano's inequality for one code -/

namespace MACCode

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}
  {M₁ M₂ n : ℕ} (c : MACCode M₁ M₂ n α₁ α₂ β)

/-- The law `p(x₁ⁿ)` of the first codeword, for a uniform message. -/
def codewordDist₁ : (Fin n → α₁) → ℝ := dist (uniformPMF (Fin M₁)) c.enc₁

/-- The law `p(x₂ⁿ)` of the second codeword, for a uniform message. -/
def codewordDist₂ : (Fin n → α₂) → ℝ := dist (uniformPMF (Fin M₂)) c.enc₂

section Bounds

variable (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
include hW h₁ h₂

omit [Fintype α₁] in
/-- Given the first message `w`, the output is produced from `x₁ⁿ(w)` by the channel from the
first input, the second codeword having law `p(x₂ⁿ)`. -/
lemma dist_jointLaw_msg₁ (w : Fin M₁) (y : Fin n → β) :
    dist (c.jointLaw W) (pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1) Prod.snd) (w, y) =
      dist (c.jointLaw W) (fun z => z.1.1) w *
        macChannel₁ (macExt W n) c.codewordDist₂ (c.enc₁ w) y := by
  classical
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hd : dist (c.jointLaw W) (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1) w = 1 / M₁ := by
    have := c.dist_jointLaw_comp_fst hW (fun v : Fin M₁ × Fin M₂ => v.1)
    rw [show (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1) =
      (fun v : Fin M₁ × Fin M₂ => v.1) ∘ Prod.fst from rfl, this]
    have h := congrFun (dist_uniformPMF_prod_fst (M₁ := M₁) h₂ id) w
    simp only [id, dist_id] at h
    rw [h]
    simp [uniformPMF]
  rw [hd, macChannel₁, outDist, codewordDist₂]
  rw [sum_dist_mul (uniformPMF (Fin M₂)) c.enc₂ fun x => macExt W n (c.enc₁ w, x) y]
  simp only [dist, pair, jointLaw, codeLaw, uniformPMF, Fintype.card_prod, Fintype.card_fin,
    Fintype.sum_prod_type, Prod.mk.injEq, input, macExt]
  rw [sum_eq_single w (fun w' _ hw' => by simp [hw']) (by simp)]
  rw [mul_sum]
  refine sum_congr rfl fun w₂ _ => ?_
  rw [sum_eq_single y (fun y' _ hy' => by simp [hy']) (by simp)]
  simp only [and_self, ite_true]
  push_cast
  field_simp

omit [Fintype α₂] in
/-- Given the second message `w`, the output is produced from `x₂ⁿ(w)` by the channel from the
second input. -/
lemma dist_jointLaw_msg₂ (w : Fin M₂) (y : Fin n → β) :
    dist (c.jointLaw W) (pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2) Prod.snd) (w, y) =
      dist (c.jointLaw W) (fun z => z.1.2) w *
        macChannel₂ (macExt W n) c.codewordDist₁ (c.enc₂ w) y := by
  classical
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hd : dist (c.jointLaw W) (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2) w = 1 / M₂ := by
    have := c.dist_jointLaw_comp_fst hW (fun v : Fin M₁ × Fin M₂ => v.2)
    rw [show (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2) =
      (fun v : Fin M₁ × Fin M₂ => v.2) ∘ Prod.fst from rfl, this]
    have h := congrFun (dist_uniformPMF_prod_snd (M₂ := M₂) h₁ id) w
    simp only [id, dist_id] at h
    rw [h]
    simp [uniformPMF]
  rw [hd, macChannel₂, outDist, codewordDist₁]
  rw [sum_dist_mul (uniformPMF (Fin M₁)) c.enc₁ fun x => macExt W n (x, c.enc₂ w) y]
  simp only [dist, pair, jointLaw, codeLaw, uniformPMF, Fintype.card_prod, Fintype.card_fin,
    Fintype.sum_prod_type, Prod.mk.injEq, input, macExt]
  rw [mul_sum]
  refine sum_congr rfl fun w₁ _ => ?_
  rw [sum_eq_single w (fun w' _ hw' => by simp [hw']) (by simp)]
  rw [sum_eq_single y (fun y' _ hy' => by simp [hy']) (by simp)]
  simp only [and_self, ite_true]
  push_cast
  field_simp

/-- `log M₁ = H(M₁) = I(M₁; Yⁿ) + H(M₁ | Yⁿ) ≤ I(X₁ⁿ; Yⁿ) + H(M₁ | Yⁿ)`: the first half of the
converse of Theorem 1, for any decoder. -/
theorem log_le_mutualInfoOf₁_add :
    log M₁ ≤ mutualInfoOf c.codewordDist₁ (macChannel₁ (macExt W n) c.codewordDist₂) +
      H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 | Prod.snd ; c.jointLaw W] := by
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  set μ := c.jointLaw W
  have hμ : IsPMF μ := c.jointLaw_isPMF hW h₁ h₂
  set W₁ : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₁ := fun z => z.1.1
  set Y : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin n → β := Prod.snd
  have hV : IsChannel (macChannel₁ (macExt W n) c.codewordDist₂) :=
    macChannel₁_isChannel (uniformPMF_isPMF.dist _) (macExt_isChannel hW n)
  have he := entropy_sub_condEntropy_eq_mutualInfoOf c.enc₁ hμ hV (c.dist_jointLaw_msg₁ hW h₁ h₂)
  have hd : dist μ (c.enc₁ ∘ W₁) = c.codewordDist₁ := by
    rw [show c.enc₁ ∘ W₁ = (fun v : Fin M₁ × Fin M₂ => c.enc₁ v.1) ∘ Prod.fst from rfl,
      c.dist_jointLaw_comp_fst hW]
    exact dist_uniformPMF_prod_fst h₂ c.enc₁
  rw [hd] at he
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ W₁ Y
  have h2 := mutualInfo_eq_entropy_sub_condEntropy' hμ W₁ Y
  have h3 := c.entropy_msg₁ hW h₁ h₂
  linarith

/-- `log M₂ = H(M₂) = I(M₂; Yⁿ) + H(M₂ | Yⁿ) ≤ I(X₂ⁿ; Yⁿ) + H(M₂ | Yⁿ)`. -/
theorem log_le_mutualInfoOf₂_add :
    log M₂ ≤ mutualInfoOf c.codewordDist₂ (macChannel₂ (macExt W n) c.codewordDist₁) +
      H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 | Prod.snd ; c.jointLaw W] := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  set μ := c.jointLaw W
  have hμ : IsPMF μ := c.jointLaw_isPMF hW h₁ h₂
  set W₂ : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₂ := fun z => z.1.2
  set Y : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin n → β := Prod.snd
  have hV : IsChannel (macChannel₂ (macExt W n) c.codewordDist₁) :=
    macChannel₂_isChannel (uniformPMF_isPMF.dist _) (macExt_isChannel hW n)
  have he := entropy_sub_condEntropy_eq_mutualInfoOf c.enc₂ hμ hV (c.dist_jointLaw_msg₂ hW h₁ h₂)
  have hd : dist μ (c.enc₂ ∘ W₂) = c.codewordDist₂ := by
    rw [show c.enc₂ ∘ W₂ = (fun v : Fin M₁ × Fin M₂ => c.enc₂ v.2) ∘ Prod.fst from rfl,
      c.dist_jointLaw_comp_fst hW]
    exact dist_uniformPMF_prod_snd h₁ c.enc₂
  rw [hd] at he
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ W₂ Y
  have h2 := mutualInfo_eq_entropy_sub_condEntropy' hμ W₂ Y
  have h3 := c.entropy_msg₂ hW h₁ h₂
  linarith

/-- **Theorem 1 of [elgamal2010], Lecture 4 (converse), for one code.** Fano's inequality gives
`log M₁ ≤ I(X₁ⁿ; Yⁿ) + log 2 + P_e^(n) log (M₁ M₂)`. -/
theorem log_le_mutualInfoOf₁ :
    log M₁ ≤ mutualInfoOf c.codewordDist₁ (macChannel₁ (macExt W n) c.codewordDist₂) + log 2 +
      c.avgErrProb W * log (M₁ * M₂) := by
  have h0 := c.log_le_mutualInfoOf₁_add hW h₁ h₂
  have h4 := condEntropy_comp_le (c.jointLaw_isPMF hW h₁ h₂)
    (Prod.fst : (Fin M₁ × Fin M₂) × (Fin n → β) → _) Prod.snd (fun v : Fin M₁ × Fin M₂ => v.1)
  have h5 := c.condEntropy_msg_le hW h₁ h₂
  have e : (fun v : Fin M₁ × Fin M₂ => v.1) ∘ Prod.fst =
      fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 := rfl
  rw [e] at h4
  linarith

/-- **Theorem 1 of [elgamal2010], Lecture 4 (converse), for one code.**
`log M₂ ≤ I(X₂ⁿ; Yⁿ) + log 2 + P_e^(n) log (M₁ M₂)`. -/
theorem log_le_mutualInfoOf₂ :
    log M₂ ≤ mutualInfoOf c.codewordDist₂ (macChannel₂ (macExt W n) c.codewordDist₁) + log 2 +
      c.avgErrProb W * log (M₁ * M₂) := by
  have h0 := c.log_le_mutualInfoOf₂_add hW h₁ h₂
  have h4 := condEntropy_comp_le (c.jointLaw_isPMF hW h₁ h₂)
    (Prod.fst : (Fin M₁ × Fin M₂) × (Fin n → β) → _) Prod.snd (fun v : Fin M₁ × Fin M₂ => v.2)
  have h5 := c.condEntropy_msg_le hW h₁ h₂
  have e : (fun v : Fin M₁ × Fin M₂ => v.2) ∘ Prod.fst =
      fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 := rfl
  rw [e] at h4
  linarith

end Bounds

end MACCode

/-! ### Theorem 1 -/

section Theorem

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}

/-- **Theorem 1 of [elgamal2010], Lecture 4 (converse).** Every achievable rate pair is in the
closure of `⋃ₖ 𝒞_k`: for the codes of block length `n`, `(R₁ - εₙ, R₂ - εₙ) ∈ 𝒞ₙ` with
`εₙ = (log 2 + P_e^(n) log (M₁ M₂))/n → 0`. -/
theorem IsAchievableMAC.mem_closure_iUnion_macMultiLetterRegion (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h : IsAchievableMAC W R₁ R₂) :
    (R₁, R₂) ∈ closure (⋃ (k : ℕ) (_ : 0 < k), macMultiLetterRegion W k) := by
  obtain ⟨c, hc⟩ := h
  set M₁ : ℕ → ℕ := fun n => ⌈exp (n * R₁)⌉₊
  set M₂ : ℕ → ℕ := fun n => ⌈exp (n * R₂)⌉₊
  set P : ℕ → ℝ := fun n => (c n).avgErrProb W
  set ε : ℕ → ℝ := fun n => (log 2 + P n * log (M₁ n * M₂ n)) / n
  have hM₁ : ∀ n, 0 < M₁ n := fun n => one_le_ceil_exp _
  have hM₂ : ∀ n, 0 < M₂ n := fun n => one_le_ceil_exp _
  have hlog : ∀ n, 0 ≤ log ((M₁ n : ℝ) * M₂ n) := fun n => by
    have h1 : (1 : ℝ) ≤ M₁ n := by exact_mod_cast hM₁ n
    have h2 : (1 : ℝ) ≤ M₂ n := by exact_mod_cast hM₂ n
    exact log_nonneg (by nlinarith)
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg (log_pos one_lt_two).le
    (mul_nonneg ((c n).avgErrProb_nonneg hW) (hlog n))) (Nat.cast_nonneg n)
  -- `(R₁ - εₙ, R₂ - εₙ) ∈ 𝒞ₙ`, with the laws of the codewords.
  have hmem : ∀ n : ℕ, 0 < n →
      (R₁ - ε n, R₂ - ε n) ∈ ⋃ (k : ℕ) (_ : 0 < k), macMultiLetterRegion W k := by
    intro n hn
    have : Nonempty (Fin (M₁ n)) := ⟨⟨0, hM₁ n⟩⟩
    have : Nonempty (Fin (M₂ n)) := ⟨⟨0, hM₂ n⟩⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have b₁ := (c n).log_le_mutualInfoOf₁ hW (hM₁ n) (hM₂ n)
    have b₂ := (c n).log_le_mutualInfoOf₂ hW (hM₁ n) (hM₂ n)
    have l₁ : n * R₁ ≤ log (M₁ n) := le_log_ceil_exp _
    have l₂ : n * R₂ ≤ log (M₂ n) := le_log_ceil_exp _
    have key : ∀ (a S : ℝ), n * a ≤ S + (log 2 + P n * log (M₁ n * M₂ n)) →
        a - ε n ≤ S / n := fun a S h => by
      simp only [ε]
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn']
      linarith
    refine mem_iUnion₂.2 ⟨n, hn, (c n).codewordDist₁, (c n).codewordDist₂,
      uniformPMF_isPMF.dist _, uniformPMF_isPMF.dist _, ?_, ?_⟩
    · exact key _ _ (by linarith)
    · exact key _ _ (by linarith)
  -- `εₙ → 0`.
  have hε : Tendsto ε atTop (𝓝 0) := by
    set K := |R₁| + |R₂| + 2
    have hP0 : Tendsto P atTop (𝓝 0) := hc
    have hup : Tendsto (fun n : ℕ => log 2 / n + P n * K) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (log 2)).add (hP0.mul_const K)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall hε0) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl₁ := log_ceil_exp_le (n * R₁)
    have hl₂ := log_ceil_exp_le (n * R₂)
    rw [abs_mul, Nat.abs_cast] at hl₁ hl₂
    have hl : log ((M₁ n : ℝ) * M₂ n) ≤ n * K := by
      rw [log_mul (by exact_mod_cast (hM₁ n).ne') (by exact_mod_cast (hM₂ n).ne')]
      have : log 2 < 1 := by
        have := log_two_lt_d9
        linarith
      simp only [M₁, M₂, K]
      nlinarith
    simp only [ε]
    rw [add_div, mul_div_assoc]
    gcongr
    · exact (c n).avgErrProb_nonneg hW
    · rw [div_le_iff₀ hn']
      linarith
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

/-- **Theorem 1 of [elgamal2010], Lecture 4 (van der Meulen)**, in nats. The capacity region of
the DM-MAC is the closure of `⋃ₖ 𝒞_k`. -/
theorem macCapacityRegion_eq_closure_iUnion [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macCapacityRegion W = closure (⋃ (k : ℕ) (_ : 0 < k), macMultiLetterRegion W k) := by
  refine le_antisymm (closure_minimal (fun R hR =>
    IsAchievableMAC.mem_closure_iUnion_macMultiLetterRegion hW hR) isClosed_closure) ?_
  refine closure_minimal (iUnion₂_subset fun k hk => ?_) isClosed_closure
  rw [macCapacityRegion_eq_closure_macRegion hW]
  exact (macMultiLetterRegion_subset_macRegion hW hk).trans subset_closure

/-- **Theorem 1 of [elgamal2010], Lecture 4.** The region `𝒞_k` in bits:
`R₁ ≤ (1/k) I(X₁ᵏ; Yᵏ)` and `R₂ ≤ (1/k) I(X₂ᵏ; Yᵏ)` bits. -/
def macMultiLetterRegionBits (W : α₁ × α₂ → β → ℝ) (k : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ (P₁ : (Fin k → α₁) → ℝ) (P₂ : (Fin k → α₂) → ℝ), IsPMF P₁ ∧ IsPMF P₂ ∧
    R.1 ≤ mutualInfoOf P₁ (macChannel₁ (macExt W k) P₂) / (k * log 2) ∧
    R.2 ≤ mutualInfoOf P₂ (macChannel₂ (macExt W k) P₁) / (k * log 2)}

lemma macMultiLetterRegionBits_eq_smul (k : ℕ) :
    macMultiLetterRegionBits W k = (log 2)⁻¹ • macMultiLetterRegion W k := by
  have hl := log_pos one_lt_two
  ext R
  rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne'), inv_inv]
  simp only [macMultiLetterRegionBits, macMultiLetterRegion, Set.mem_ofPred_eq, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, div_mul_eq_div_div, le_div_iff₀ hl, mul_comm (log 2)]

/-- **Theorem 1 of [elgamal2010], Lecture 4 (van der Meulen).** The capacity region of the DM-MAC,
in bits, is the closure of `⋃ₖ 𝒞_k`, where `𝒞_k` is the set of rate pairs with
`R₁ ≤ (1/k) I(X₁ᵏ; Yᵏ)` and `R₂ ≤ (1/k) I(X₂ᵏ; Yᵏ)` for some `p(x₁ᵏ) p(x₂ᵏ)`. -/
theorem macCapacityRegionBits_eq_closure_iUnion [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    macCapacityRegionBits W =
      closure (⋃ (k : ℕ) (_ : 0 < k), macMultiLetterRegionBits W k) := by
  simp only [macMultiLetterRegionBits_eq_smul]
  rw [macCapacityRegionBits_eq_smul hW, macCapacityRegion_eq_closure_iUnion hW, ← closure_smul₀,
    smul_set_iUnion₂]

end Theorem

end InfoTheory
