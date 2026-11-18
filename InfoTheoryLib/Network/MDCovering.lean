/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACConverse
public import InfoTheoryLib.Network.MultipleDescriptions
public import InfoTheoryLib.Typicality.Covering
public import InfoTheoryLib.Typicality.MutualCovering

/-!
# The covering bounds of the three layers of Zhang–Berger coding

The Zhang–Berger scheme of Lecture 14 has three layers. For random variables `X`, `U`, `X̂₀`, `X̂₁`,
`X̂₂` on a finite probability space, this file bounds, for each layer, the probability that a random
codebook does not cover a given typical sequence:

1. a codebook of `uⁿ` sequences, by the covering lemma;
2. two conditionally independent codebooks of `x̂₁ⁿ` and `x̂₂ⁿ` sequences given `uⁿ`, by a
   conditional version of the multivariate covering lemma, proved with the second moment method;
3. a codebook of `x̂₀ⁿ` sequences given `(uⁿ, x̂₁ⁿ, x̂₂ⁿ)`, by the covering lemma.

## Main definitions

* `triLaw μ U W Y`: the law of `((U, W), Y)`.

## Main statements

* `prob_triLaw_le`, `eventually_triLaw_ge`: the joint typicality lemma for random variables on a
  finite probability space.
* `eventually_sum_first_codebook_le`: the first layer.
* `eventually_sum_two_codebooks_le`: **the conditional multivariate covering lemma**.
* `eventually_sum_last_codebook_le`: the third layer.

## Implementation notes

The errors `δ(ε)` are bounded with the sizes of the alphabets, so that they do not depend on the
layer: `H(Y | ·) ≤ log |𝒴|`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lectures 9 and 14
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω υ γ β : Type*} [Fintype Ω] [Fintype υ] [Fintype γ] [Fintype β] {μ : Ω → ℝ} {n : ℕ}
  {ε : ℝ}

/-! ### The joint typicality lemma for random variables -/

section Tri

variable {U : Ω → υ} {W : Ω → γ} {Y : Ω → β}

/-- The law of `((U, W), Y)`. -/
def triLaw (μ : Ω → ℝ) (U : Ω → υ) (W : Ω → γ) (Y : Ω → β) : (υ × γ) × β → ℝ :=
  dist μ (pair (pair U W) Y)

lemma triLaw_isPMF (hμ : IsPMF μ) : IsPMF (triLaw μ U W Y) := hμ.dist _

lemma margFst_triLaw : margFst (triLaw μ U W Y) = dist μ (pair U W) := by
  rw [margFst, triLaw, ← dist_comp_eq]
  rfl

lemma condDist_triLaw :
    condDist (triLaw μ U W Y) Prod.snd (Prod.fst ∘ Prod.fst) = condDist μ Y U := by
  funext a b
  simp only [condDist, triLaw]
  rw [← dist_comp_eq, ← dist_comp_eq]
  rfl

lemma condMutualInfo_triLaw (hμ : IsPMF μ) :
    I[Prod.snd ∘ Prod.fst : Prod.snd | Prod.fst ∘ Prod.fst ; triLaw μ U W Y] = I[W : Y | U ; μ] :=
  (condMutualInfo_comp hμ (pair (pair U W) Y) _ _ _).symm

omit [Fintype Ω] [Fintype υ] [Fintype γ] in
/-- A conditional entropy is at most the logarithm of the size of the alphabet. -/
lemma condEntropy_le_log_card' {Ω' σ : Type*} [Fintype Ω'] [Fintype σ] {ν : Ω' → ℝ} (hν : IsPMF ν)
    (A : Ω' → β) (B : Ω' → σ) : H[A | B ; ν] ≤ log (Fintype.card β) :=
  (condEntropy_le_entropy hν A B).trans (entropyRV_le_log_card hν A)

lemma condEntropy_triLaw_le (hμ : IsPMF μ) :
    H[Prod.snd | Prod.fst ; triLaw μ U W Y] + H[Prod.snd | Prod.fst ∘ Prod.fst ; triLaw μ U W Y] ≤
      2 * log (Fintype.card β) := by
  have h1 := condEntropy_le_log_card' (triLaw_isPMF (U := U) (W := W) (Y := Y) hμ) Prod.snd Prod.fst
  have h2 := condEntropy_le_log_card' (triLaw_isPMF (U := U) (W := W) (Y := Y) hμ) Prod.snd
    (Prod.fst ∘ Prod.fst)
  linarith

/-- **Joint typicality lemma, part 1(a), for random variables.** For arbitrary `(uⁿ, wⁿ)` and
`Yⁿ ∼ ∏ᵢ p(yᵢ|uᵢ)`, `P{(uⁿ, wⁿ, Yⁿ) ∈ T_ε^(n)} ≤ e^{-n(I(W;Y|U) - 2 ε log |𝒴|)}`. -/
theorem prob_triLaw_le (hμ : IsPMF μ) (hε : 0 ≤ ε) (u : Fin n → υ) (w : Fin n → γ) :
    prob (channelExt (condDist μ Y U) n u) (condRobustTypicalSet (triLaw μ U W Y) ε (zipSeq u w)) ≤
      exp (-(n * (I[W : Y | U ; μ] - ε * (2 * log (Fintype.card β))))) := by
  have h := prob_condRobustTypicalSet_condDist_le (triLaw_isPMF (U := U) (W := W) (Y := Y) hμ) n ε
    u w
  rw [condDist_triLaw, condMutualInfo_triLaw hμ] at h
  refine h.trans (exp_le_exp.2 ?_)
  have h1 := mul_le_mul_of_nonneg_left (condEntropy_triLaw_le (U := U) (W := W) (Y := Y) hμ) hε
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left h1 hn]

/-- **Joint typicality lemma, part 1(b), for random variables.** Let `ε' < ε ≤ 1`. For `n`
sufficiently large, every typical `(uⁿ, wⁿ)` and `Yⁿ ∼ ∏ᵢ p(yᵢ|uᵢ)`,
`P{(uⁿ, wⁿ, Yⁿ) ∈ T_ε^(n)} ≥ (1 - ε) e^{-n(I(W;Y|U) + 2 ε log |𝒴|)}`. -/
theorem eventually_triLaw_ge (hμ : IsPMF μ) {ε' : ℝ} (hεε : ε' < ε) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : Fin n → υ) (w : Fin n → γ),
      zipSeq u w ∈ robustTypicalSet (dist μ (pair U W)) n ε' →
        (1 - ε) * exp (-(n * (I[W : Y | U ; μ] + ε * (2 * log (Fintype.card β))))) ≤
          prob (channelExt (condDist μ Y U) n u)
            (condRobustTypicalSet (triLaw μ U W Y) ε (zipSeq u w)) := by
  have hq := triLaw_isPMF (U := U) (W := W) (Y := Y) hμ
  filter_upwards [eventually_prob_condRobustTypicalSet_condDist_ge hq hεε hε] with n hn u w huw
  have h := hn u w (by rwa [margFst_triLaw])
  rw [condDist_triLaw, condMutualInfo_triLaw hμ] at h
  refine le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by linarith)) h
  have h1 := mul_le_mul_of_nonneg_left (condEntropy_triLaw_le (U := U) (W := W) (Y := Y) hμ) hε.le
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left h1 hn']

omit [Fintype υ] [Fintype γ] in
/-- `p(yⁿ|uⁿ)` is a pmf when `p(uᵢ) > 0` for every `i`. -/
lemma channelExt_condDist_isPMF (hμ : IsPMF μ) (Y : Ω → β) (U : Ω → υ) {u : Fin n → υ}
    (hu : ∀ i, dist μ U (u i) ≠ 0) : IsPMF (channelExt (condDist μ Y U) n u) := by
  classical
  refine ⟨fun z => prod_nonneg fun _ _ => condDist_nonneg hμ _ _ _ _, ?_⟩
  rw [show ∑ z, channelExt (condDist μ Y U) n u z = ∏ i, ∑ b, condDist μ Y U (u i) b from
    (Fintype.prod_sum _).symm]
  exact prod_eq_one fun i _ => (condDist_isPMF hμ Y U (hu i)).sum_eq_one

/-- If `(uⁿ, wⁿ)` is typical, then `p(uᵢ) > 0` for every `i`. -/
lemma dist_ne_zero_of_mem (hμ : IsPMF μ) {U : Ω → υ} {W : Ω → γ} {u : Fin n → υ} {w : Fin n → γ}
    (h : zipSeq u w ∈ robustTypicalSet (dist μ (pair U W)) n ε) (i : Fin n) :
    dist μ U (u i) ≠ 0 := by
  have h1 := pos_of_mem_robustTypicalSet (hμ.dist (pair U W)).nonneg h i
  have h2 := dist_pair_le_left hμ U W (u i) (w i)
  exact (h1.trans_le h2).ne'

end Tri

/-! ### Expectations of typicality indicators -/

section Indicator

variable {κ : Type*} [Fintype κ]

open Classical in
omit [Fintype υ] [Fintype γ] [Fintype Ω] in
/-- The probability of a conditionally typical set as an expectation. -/
lemma sum_mul_ite_mem_eq_prob (ν : (Fin n → β) → ℝ) (q : κ × β → ℝ) (ε : ℝ) (a : Fin n → κ) :
    ∑ z, ν z * (if zipSeq a z ∈ robustTypicalSet q n ε then 1 else 0) =
      prob ν (condRobustTypicalSet q ε a) := by
  rw [prob, ← univ_inter (condRobustTypicalSet q ε a), ← sum_ite_mem]
  refine sum_congr rfl fun z _ => ?_
  by_cases h : zipSeq a z ∈ robustTypicalSet q n ε
  · simp [h, mem_condRobustTypicalSet.2 h]
  · have : z ∉ condRobustTypicalSet q ε a := fun h' => h (mem_condRobustTypicalSet.1 h')
    simp [h, this]

end Indicator

/-! ### The first layer -/

section First

variable {α : Type*} [Fintype α]

open Classical in
/-- **The first layer.** For `xⁿ` typical and `L` codewords `Uⁿ(m)` drawn i.i.d. from `∏ᵢ p(uᵢ)`,
the probability that no codeword is jointly typical with `xⁿ` is at most
`exp(-L (1 - ε) e^{-n(I(X; U) + 2 ε log |𝒰|)})`. -/
theorem eventually_sum_first_codebook_le (hμ : IsPMF μ) (X : Ω → α) (U : Ω → υ) {ε₀ : ℝ}
    (hεε : ε₀ < ε) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ robustTypicalSet (dist μ X) n ε₀, ∀ L : ℕ,
      ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF (dist μ U) n) L C *
          (if ∀ m, ¬ zipSeq x (C m) ∈ robustTypicalSet (dist μ (pair X U)) n ε then 1 else 0) ≤
        exp (-(L * ((1 - ε) * exp (-(n * (I[U : X ; μ] + ε * (2 * log (Fintype.card υ)))))))) := by
  have hq : IsPMF (dist μ (pair X U)) := hμ.dist _
  have hm₁ : margFst (dist μ (pair X U)) = dist μ X := by
    rw [margFst, ← dist_comp_eq]
    rfl
  have hm₂ : margSnd (dist μ (pair X U)) = dist μ U := by
    rw [margSnd, ← dist_comp_eq]
    rfl
  have hI : I[Prod.snd : Prod.fst ; dist μ (pair X U)] = I[U : X ; μ] :=
    (mutualInfo_comp (pair X U) _ _).symm
  filter_upwards [eventually_le_prob_iidPMF_condRobustTypicalSet hq hεε hε] with n hn x hx L
  have h := hn x (by rwa [hm₁])
  rw [hm₂, hI] at h
  have hs := sum_iidPMF_ite_forall_not_mem_le (iidPMF_isPMF (hμ.dist U) n) L
    (condRobustTypicalSet (dist μ (pair X U)) ε x)
  refine le_trans (le_of_eq (sum_congr rfl fun C _ => ?_)) (hs.trans (exp_le_exp.2 ?_))
  · have hk := forall_congr' fun m => not_congr
      (mem_condRobustTypicalSet (q := dist μ (pair X U)) (ε := ε) (x := x) (y := C m)).symm
    congr 1
    split_ifs with a b b
    · rfl
    · exact absurd (hk.1 a) b
    · exact absurd (hk.2 b) a
    · rfl
  · have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    refine neg_le_neg (mul_le_mul_of_nonneg_left (le_trans ?_ h) hL)
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by linarith)
    have h1 := entropyRV_le_log_card hq (Prod.snd : α × υ → υ)
    have h2 := condEntropy_le_log_card' hq (Prod.snd : α × υ → υ) Prod.fst
    have h3 : ε * (H[Prod.snd ; dist μ (pair X U)] + H[Prod.snd | Prod.fst ; dist μ (pair X U)]) ≤
        ε * (2 * log (Fintype.card υ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hε.le
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left h3 hn']

end First

/-! ### The last layer -/

section Last

variable {α : Type*} [Fintype α]

open Classical in
/-- **The last layer.** For `(vⁿ, xⁿ)` typical and `L` codewords `Yⁿ(m)` drawn i.i.d. from
`∏ᵢ p(yᵢ|vᵢ)`, the probability that no codeword is jointly typical with `(vⁿ, xⁿ)` is at most
`exp(-L (1 - ε) e^{-n(I(X; Y | V) + 2 ε log |𝒴|)})`. -/
theorem eventually_sum_last_codebook_le (hμ : IsPMF μ) (V : Ω → υ) (X : Ω → α) (Y : Ω → β) {ε' : ℝ}
    (hεε : ε' < ε) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Fin n → υ) (x : Fin n → α),
      zipSeq v x ∈ robustTypicalSet (dist μ (pair V X)) n ε' → ∀ L : ℕ,
      ∑ C : Fin L → Fin n → β, iidPMF (channelExt (condDist μ Y V) n v) L C *
          (if ∀ m, ¬ zipSeq (zipSeq v x) (C m) ∈ robustTypicalSet (triLaw μ V X Y) n ε
            then 1 else 0) ≤
        exp (-(L * ((1 - ε) * exp (-(n * (I[X : Y | V ; μ] +
          ε * (2 * log (Fintype.card β)))))))) := by
  filter_upwards [eventually_triLaw_ge (U := V) (W := X) (Y := Y) hμ hεε hε hε1] with n hn v x hvx L
  have hP : IsPMF (channelExt (condDist μ Y V) n v) := channelExt_condDist_isPMF hμ Y V fun i =>
    dist_ne_zero_of_mem hμ hvx i
  have h := hn v x hvx
  have hs := sum_iidPMF_ite_forall_not_mem_le hP L
    (condRobustTypicalSet (triLaw μ V X Y) ε (zipSeq v x))
  refine le_trans (le_of_eq (sum_congr rfl fun C _ => ?_)) (hs.trans (exp_le_exp.2 ?_))
  · have hk := forall_congr' fun m => not_congr
      (mem_condRobustTypicalSet (q := triLaw μ V X Y) (ε := ε) (x := zipSeq v x) (y := C m)).symm
    congr 1
    split_ifs with a b b
    · rfl
    · exact absurd (hk.1 a) b
    · exact absurd (hk.2 b) a
    · rfl
  · exact neg_le_neg (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg L))

end Last

/-! ### The middle layer -/

section Two

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {X : Ω → α} {U : Ω → υ}
  {Y₁ : Ω → β₁} {Y₂ : Ω → β₂}

open Classical in
/-- **The conditional multivariate covering lemma (Lectures 9 and 14).** Let `ε₁ < ε' < ε ≤ 1/2`.
For `(uⁿ, xⁿ)` typical, let `X̂₁ⁿ(m₁)`, `m₁ ∈ [1 : L₁]`, and `X̂₂ⁿ(m₂)`, `m₂ ∈ [1 : L₂]`, be
independent sequences drawn from `∏ᵢ p(x̂₁ᵢ|uᵢ)` and from `∏ᵢ p(x̂₂ᵢ|uᵢ)`. Then the probability that
no pair of them is jointly typical with `(uⁿ, xⁿ)` is at most
`4 (e^{n(J + 2δ)}/(L₁ L₂) + e^{n(I(X; X̂₁|U) + 3δ)}/L₁ + e^{n(I(X; X̂₂|U) + 3δ)}/L₂)`, where
`J = I(X; X̂₁, X̂₂|U) + I(X̂₁; X̂₂|U)` and `δ = 2 ε (log |𝒳̂₁| + log |𝒳̂₂|)`. The law `J` is given
in its two forms, one for each order of the codebooks. -/
theorem eventually_sum_two_codebooks_le (hμ : IsPMF μ) {ε₁ ε' : ℝ} (hε₁ : ε₁ < ε') (hε' : ε' < ε)
    (hε'0 : 0 < ε') (hε : ε ≤ 1 / 2) {J : ℝ}
    (hJ : J = I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ])
    (hJ' : J = I[X : Y₂ | U ; μ] + I[pair X Y₂ : Y₁ | U ; μ]) :
    ∀ᶠ n : ℕ in atTop, ∀ (u : Fin n → υ) (x : Fin n → α),
      zipSeq u x ∈ robustTypicalSet (dist μ (pair U X)) n ε₁ → ∀ {L₁ L₂ : ℕ}, 0 < L₁ → 0 < L₂ →
      IsPMF (coverLaw (channelExt (condDist μ Y₁ U) n u) (channelExt (condDist μ Y₂ U) n u) L₁ L₂) ∧
      ∑ D, coverLaw (channelExt (condDist μ Y₁ U) n u) (channelExt (condDist μ Y₂ U) n u) L₁ L₂ D *
          (if ∀ l₁ l₂, ¬ zipSeq (zipSeq u (zipSeq x (D.1 l₁))) (D.2 l₂) ∈
            robustTypicalSet (triLaw μ U (pair X Y₁) Y₂) n ε then 1 else 0) ≤
        4 * (exp (n * (J + 2 * (ε * (2 * (log (Fintype.card β₁) + log (Fintype.card β₂)))))) /
            (L₁ * L₂) +
          exp (n * (I[X : Y₁ | U ; μ] +
            3 * (ε * (2 * (log (Fintype.card β₁) + log (Fintype.card β₂)))))) / L₁ +
          exp (n * (I[X : Y₂ | U ; μ] +
            3 * (ε * (2 * (log (Fintype.card β₁) + log (Fintype.card β₂)))))) / L₂) := by
  have hε0 : 0 < ε := hε'0.trans hε'
  set c₁ := log (Fintype.card β₁) with hc₁
  set c₂ := log (Fintype.card β₂) with hc₂
  have hc₁0 : 0 ≤ c₁ := log_natCast_nonneg _
  have hc₂0 : 0 ≤ c₂ := log_natCast_nonneg _
  set δ := ε * (2 * (c₁ + c₂)) with hδ
  set I₁ := I[X : Y₁ | U ; μ] with hI₁
  set I₂ := I[X : Y₂ | U ; μ] with hI₂
  set I₂' := I[pair X Y₁ : Y₂ | U ; μ] with hI₂'
  set I₁' := I[pair X Y₂ : Y₁ | U ; μ] with hI₁'
  have hl1 := eventually_triLaw_ge (U := U) (W := X) (Y := Y₁) hμ hε₁ hε'0 (by linarith)
  have hl2 := eventually_triLaw_ge (U := U) (W := pair X Y₁) (Y := Y₂) hμ hε' hε0 (by linarith)
  filter_upwards [hl1, hl2] with n hn1 hn2 u x hux L₁ L₂ hL₁ hL₂
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hP₁ : IsPMF (channelExt (condDist μ Y₁ U) n u) :=
    channelExt_condDist_isPMF hμ Y₁ U fun i => dist_ne_zero_of_mem hμ hux i
  have hP₂ : IsPMF (channelExt (condDist μ Y₂ U) n u) :=
    channelExt_condDist_isPMF hμ Y₂ U fun i => dist_ne_zero_of_mem hμ hux i
  set μ₁ := channelExt (condDist μ Y₁ U) n u with hμ₁
  set μ₂ := channelExt (condDist μ Y₂ U) n u with hμ₂
  refine ⟨coverLaw_isPMF hP₁ hP₂, ?_⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin n → β₁) → (Fin n → β₂) → Prop, ∀ c₁ c₂, e c₁ c₂ ↔
      zipSeq (zipSeq u (zipSeq x c₁)) c₂ ∈ robustTypicalSet (triLaw μ U (pair X Y₁) Y₂) n ε :=
    ⟨_, fun _ _ => Iff.rfl⟩
  -- The upper bounds.
  have hδ₁ : ε * (2 * c₁) ≤ δ := by
    rw [hδ]
    exact mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have hδ₂ : ε * (2 * c₂) ≤ δ := by
    rw [hδ]
    exact mul_le_mul_of_nonneg_left (by linarith) hε0.le
  set a₁ := exp (-(n * (I₂' - δ))) with ha₁d
  set a₂ := exp (-(n * (I₁' - δ))) with ha₂d
  have ha₁ : ∀ z₁, ∑ z₂, μ₂ z₂ * (if e z₁ z₂ then 1 else 0) ≤ a₁ := fun z₁ => by
    have h := prob_triLaw_le (U := U) (W := pair X Y₁) (Y := Y₂) hμ hε0.le u (zipSeq x z₁)
    rw [← sum_mul_ite_mem_eq_prob] at h
    refine le_trans (le_of_eq (sum_congr rfl fun z₂ _ => ?_)) (h.trans (exp_le_exp.2 ?_))
    · rw [if_congr (he z₁ z₂) rfl rfl]
      congr!
    · nlinarith [mul_le_mul_of_nonneg_left hδ₂ hn0]
  have ha₂ : ∀ z₂, ∑ z₁, μ₁ z₁ * (if e z₁ z₂ then 1 else 0) ≤ a₂ := fun z₂ => by
    have h := prob_triLaw_le (U := U) (W := pair X Y₂) (Y := Y₁) hμ hε0.le u (zipSeq x z₂)
    rw [← sum_mul_ite_mem_eq_prob] at h
    refine le_trans (sum_le_sum fun z₁ _ => ?_) (h.trans (exp_le_exp.2 ?_))
    · refine mul_le_mul_of_nonneg_left ?_ (hP₁.nonneg z₁)
      by_cases hz : e z₁ z₂
      · have h1 := comp_mem_robustTypicalSet ((he z₁ z₂).1 hz)
          (fun t : (υ × α × β₁) × β₂ => ((t.1.1, t.1.2.1, t.2), t.1.2.2))
        have h2 : dist (triLaw μ U (pair X Y₁) Y₂)
            (fun t : (υ × α × β₁) × β₂ => ((t.1.1, t.1.2.1, t.2), t.1.2.2)) =
            triLaw μ U (pair X Y₂) Y₁ := by
          rw [triLaw, ← dist_comp_eq]
          rfl
        rw [h2] at h1
        have h3 : zipSeq (zipSeq u (zipSeq x z₂)) z₁ ∈
            robustTypicalSet (triLaw μ U (pair X Y₂) Y₁) n ε := h1
        simp only [hz, h3, ite_true]
        exact le_rfl
      · simp only [hz, ite_false]
        split_ifs <;> norm_num
    · nlinarith [mul_le_mul_of_nonneg_left hδ₁ hn0]
  -- The lower bound.
  set low := (1 / 4 : ℝ) * exp (-(n * (J + 2 * δ))) with hlow
  have hlow0 : 0 < low := by positivity
  have hp : low ≤ coverProb μ₁ μ₂ e := by
    set S := condRobustTypicalSet (triLaw μ U X Y₁) ε' (zipSeq u x) with hS
    set l₁ := (1 / 2 : ℝ) * exp (-(n * (I₁ + δ))) with hl₁
    set l₂ := (1 / 2 : ℝ) * exp (-(n * (I₂' + δ))) with hl₂
    have hS1 : l₁ ≤ prob μ₁ S := by
      refine le_trans (mul_le_mul (by linarith) (exp_le_exp.2 ?_) (exp_pos _).le (by linarith))
        (hn1 u x hux)
      have : ε' * (2 * c₁) ≤ ε * (2 * c₁) :=
        mul_le_mul_of_nonneg_right hε'.le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left (this.trans hδ₁) hn0]
    have hS2 : ∀ z₁ ∈ S, l₂ ≤ ∑ z₂, μ₂ z₂ * (if e z₁ z₂ then 1 else 0) := fun z₁ hz₁ => by
      have h1 := comp_mem_robustTypicalSet (mem_condRobustTypicalSet.1 hz₁)
        (fun t : (υ × α) × β₁ => (t.1.1, t.1.2, t.2))
      have h2 : dist (triLaw μ U X Y₁) (fun t : (υ × α) × β₁ => (t.1.1, t.1.2, t.2)) =
          dist μ (pair U (pair X Y₁)) := by
        rw [triLaw, ← dist_comp_eq]
        rfl
      rw [h2] at h1
      have h3 := hn2 u (zipSeq x z₁) h1
      rw [← sum_mul_ite_mem_eq_prob] at h3
      refine le_trans (mul_le_mul (by linarith) (exp_le_exp.2 ?_) (exp_pos _).le (by linarith))
        (h3.trans (le_of_eq (sum_congr rfl fun z₂ _ => ?_)))
      · nlinarith [mul_le_mul_of_nonneg_left hδ₂ hn0]
      · rw [if_congr (he z₁ z₂) rfl rfl]
        congr!
    have hsum : coverProb μ₁ μ₂ e = ∑ z₁, μ₁ z₁ * ∑ z₂, μ₂ z₂ * (if e z₁ z₂ then 1 else 0) := by
      simp only [coverProb, mul_sum, mul_assoc]
    have hinner0 : ∀ z₁, 0 ≤ ∑ z₂, μ₂ z₂ * (if e z₁ z₂ then (1 : ℝ) else 0) := fun z₁ =>
      sum_nonneg fun z₂ _ => mul_nonneg (hP₂.nonneg z₂) (by split_ifs <;> norm_num)
    have hl₂0 : 0 ≤ l₂ := by positivity
    have hbig : prob μ₁ S * l₂ ≤ coverProb μ₁ μ₂ e := by
      rw [hsum, prob, sum_mul]
      refine (sum_le_sum fun z₁ hz₁ => mul_le_mul_of_nonneg_left (hS2 z₁ hz₁)
        (hP₁.nonneg z₁)).trans ?_
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z₁ _ _ =>
        mul_nonneg (hP₁.nonneg z₁) (hinner0 z₁)
    refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_right hS1 hl₂0).trans hbig)
    rw [hlow, hl₁, hl₂, hJ]
    have : exp (-(n * (I₁ + I₂' + 2 * δ))) = exp (-(n * (I₁ + δ))) * exp (-(n * (I₂' + δ))) := by
      rw [← exp_add]
      ring_nf
    rw [this]
    ring
  have hppos : 0 < coverProb μ₁ μ₂ e := hlow0.trans_le hp
  have hb := sum_mutualCovering_le hP₁ hP₂ e ha₁ ha₂ hL₁ hL₂ hppos
  set p₁ := coverProb μ₁ μ₂ e
  have hL₁' : (0 : ℝ) < L₁ := by exact_mod_cast hL₁
  have hL₂' : (0 : ℝ) < L₂ := by exact_mod_cast hL₂
  have hE := exp_pos (n * (J + 2 * δ))
  have hinv : 1 / p₁ ≤ 4 * exp (n * (J + 2 * δ)) := by
    rw [div_le_iff₀ hppos]
    have e1 : exp (n * (J + 2 * δ)) * exp (-(n * (J + 2 * δ))) = 1 := by
      rw [← exp_add]
      simp
    calc (1 : ℝ) = 4 * exp (n * (J + 2 * δ)) * low := by
          rw [hlow]
          linear_combination -e1
      _ ≤ 4 * exp (n * (J + 2 * δ)) * p₁ := mul_le_mul_of_nonneg_left hp (by positivity)
  have ha₁0 : 0 ≤ a₁ := (exp_pos _).le
  have ha₂0 : 0 ≤ a₂ := (exp_pos _).le
  have hmid₁ : a₁ * (1 / p₁) ≤ 4 * exp (n * (I₁ + 3 * δ)) := by
    refine (mul_le_mul_of_nonneg_left hinv ha₁0).trans (le_of_eq ?_)
    rw [ha₁d, mul_left_comm, ← exp_add]
    congr 2
    rw [hJ]
    ring
  have hmid₂ : a₂ * (1 / p₁) ≤ 4 * exp (n * (I₂ + 3 * δ)) := by
    refine (mul_le_mul_of_nonneg_left hinv ha₂0).trans (le_of_eq ?_)
    rw [ha₂d, mul_left_comm, ← exp_add]
    congr 2
    rw [hJ']
    ring
  have t1 : 1 / (L₁ * L₂ * p₁) ≤ 4 * (exp (n * (J + 2 * δ)) / (L₁ * L₂)) := by
    have : 1 / ((L₁ : ℝ) * L₂ * p₁) = 1 / p₁ / (L₁ * L₂) := by
      field_simp
    rw [this, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hinv (by positivity)
  have t2 : a₁ / (L₁ * p₁) ≤ 4 * (exp (n * (I₁ + 3 * δ)) / L₁) := by
    calc a₁ / (L₁ * p₁) = a₁ * (1 / p₁) / L₁ := by field_simp
      _ ≤ 4 * exp (n * (I₁ + 3 * δ)) / L₁ := div_le_div_of_nonneg_right hmid₁ hL₁'.le
      _ = _ := by ring
  have t3 : a₂ / (L₂ * p₁) ≤ 4 * (exp (n * (I₂ + 3 * δ)) / L₂) := by
    calc a₂ / (L₂ * p₁) = a₂ * (1 / p₁) / L₂ := by field_simp
      _ ≤ 4 * exp (n * (I₂ + 3 * δ)) / L₂ := div_le_div_of_nonneg_right hmid₂ hL₂'.le
      _ = _ := by ring
  refine le_trans (le_of_eq (sum_congr rfl fun D _ => ?_)) (hb.trans ?_)
  · congr 1
    exact if_congr (by simp only [he]) rfl rfl
  · linarith

end Two

end InfoTheory
