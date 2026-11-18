/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCBits
public import InfoTheoryLib.Network.BCSuperposition
public import InfoTheoryLib.Typicality.MutualCovering

/-!
# Marton's inner bound

Marton's inner bound for the DM-BC with private messages says that `(R₁, R₂)` is achievable if
`R₁ < I(U₁; Y₁)`, `R₂ < I(U₂; Y₂)` and `R₁ + R₂ < I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)` for some
`p(u₁, u₂)` and `x(u₁, u₂)`: the codewords for independent messages can be jointly distributed
according to any desired pmf, at the cost of the term `I(U₁; U₂)`. With independent `U₁`, `U₂` this
is the Cover–van der Meulen inner bound.

Each message `mⱼ` has a subcodebook of `Lⱼ` sequences, generated independently. The encoder looks
for a jointly typical pair in the product of the two subcodebooks and transmits
`xᵢ = x(u₁ᵢ, u₂ᵢ)`; the mutual covering lemma says that there is such a pair. Each decoder looks for
a sequence jointly typical with its output.

## Main definitions

* `martonK₁`, `martonK₂`: the channels from `(U₁, U₂)` to `Y₁` and to `Y₂`.
* `martonInfo₁`, `martonInfo₂`: `I(U₁; Y₁)`, `I(U₂; Y₂)`; `martonInfo₁₂`: `I(U₁; U₂)`.
* `martonRegionBits W`: Marton's inner bound in bits.
* `coverVanDerMeulenRegionBits W`: the Cover–van der Meulen inner bound in bits.

## Main statements

* `sum_subcode_side_le`: the bound on the probability of error at one receiver.
* `exists_marton_code_le`: the random coding bound.
* `martonRegionBits_subset`: **Marton's inner bound (Theorem 2 of Lecture 9)**.
* `coverVanDerMeulenRegionBits_subset`: **the Cover–van der Meulen inner bound**.

## Implementation notes

The regions are for nonnegative rates: the scheme uses a subcodebook of more than one sequence for
each message, also for a rate equal to `0`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### One receiver -/

section Side

variable {𝒵 𝒰 β : Type*} [Fintype 𝒵] [Fintype 𝒰] [Fintype β]

open Classical in
/-- For `zⁿ` typical for `q`, the output of the channel `K` is jointly typical with `f(zⁿ)` with
probability at least `1 - K₀/n`, by the conditional typicality lemma. -/
lemma sum_ite_not_mem_comp_le {q : 𝒵 → ℝ} (hq : IsPMF q) {K : 𝒵 → β → ℝ} (hK : IsChannel K)
    (f : 𝒵 → 𝒰) {n : ℕ} (hn : 0 < n) {ε' ε : ℝ} (hεε : ε' < ε) {z : Fin n → 𝒵}
    (hz : z ∈ robustTypicalSet q n ε') :
    ∑ y, (if zipSeq y (f ∘ z) ∉ robustTypicalSet (dist (jointOf q K) fun w => (w.2, f w.1)) n ε then
        channelExt K n z y else 0) ≤
      condTypicalityConst (jointOf q K) ε' ε / n := by
  have hJ := jointOf_isPMF hq hK
  have hm : margFst (jointOf q K) = q := dist_jointOf_fst hK
  have hz' : z ∈ robustTypicalSet (margFst (jointOf q K)) n ε' := by rwa [hm]
  have h1 := one_sub_div_le_prob_condRobustTypicalSet hJ hεε hn hz'
  have hcond : ∀ w, q w ≠ 0 → ∀ y, condPMF (jointOf q K) w y = K w y := fun w hw y => by
    rw [condPMF, marg_eq_dist]
    have : dist (jointOf q K) Prod.fst w = q w := congrFun hm w
    rw [this]
    simp only [jointOf]
    field_simp
  have hext : ∀ y, channelExt (condPMF (jointOf q K)) n z y = channelExt K n z y := fun y =>
    prod_congr rfl fun i _ =>
      hcond _ (pos_of_mem_robustTypicalSet hq.nonneg hz i).ne' (y i)
  have h2 : prob (channelExt (condPMF (jointOf q K)) n z)
      (condRobustTypicalSet (jointOf q K) ε z) ≤
      1 - ∑ y, (if zipSeq y (f ∘ z) ∉
        robustTypicalSet (dist (jointOf q K) fun w => (w.2, f w.1)) n ε then
          channelExt K n z y else 0) := by
    have hsum := ((hK.ext n) z).sum_eq_one
    have e : prob (channelExt (condPMF (jointOf q K)) n z)
        (condRobustTypicalSet (jointOf q K) ε z) =
        ∑ y, if y ∈ condRobustTypicalSet (jointOf q K) ε z then channelExt K n z y else 0 := by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, prob]
      exact sum_congr rfl fun y _ => hext y
    rw [e, ← hsum, le_sub_iff_add_le, ← sum_add_distrib]
    refine sum_le_sum fun y _ => ?_
    have hE := channelExt_nonneg hK z y
    by_cases hy : y ∈ condRobustTypicalSet (jointOf q K) ε z
    · have hT : zipSeq y (f ∘ z) ∈
          robustTypicalSet (dist (jointOf q K) fun w => (w.2, f w.1)) n ε :=
        comp_mem_robustTypicalSet (mem_condRobustTypicalSet.1 hy) fun w => (w.2, f w.1)
      simp [hy, hT]
    · simp only [hy, ite_false, zero_add]
      split_ifs
      · exact hE
      · exact le_rfl
  linarith

/-- The pmf of `(Y, U)` for `U = f(Z)`. -/
def compYU (q : 𝒵 → ℝ) (K : 𝒵 → β → ℝ) (f : 𝒵 → 𝒰) : β × 𝒰 → ℝ :=
  dist (jointOf q K) fun w => (w.2, f w.1)

variable {X Ξ : Type*} [Fintype X] [Fintype Ξ]

omit [Fintype 𝒵] in
open Classical in
/-- **The error at one receiver.** The subcodebooks of the receiver have `L` sequences drawn from
`μ`, the rest of the codebook is independent and described by `ξ ∼ ν`. If for a good pair `(D, ξ)`
the probability that no sequence of `D` is related to the output is at most `B`, then the
probability of error is at most `B` plus the probability of a bad pair plus `M L η`. -/
theorem sum_subcode_side_le {n M L M' : ℕ} {μ : X → ℝ} (hμ : IsPMF μ) {ν : Ξ → ℝ} (hν : IsPMF ν)
    (m₀ m : Fin M) (m' : Fin M') (A : X → (Fin n → β) → Prop) {K : 𝒵 → β → ℝ} (hK : IsChannel K)
    (enc : (Fin L → X) → Ξ → Fin n → 𝒵) {η : ℝ} (hη₀ : 0 ≤ η)
    (hη : ∀ y, ∑ x, μ x * (if A x y then 1 else 0) ≤ η) {B : ℝ} (hB : 0 ≤ B)
    (G : (Fin L → X) → Ξ → Prop)
    (hG : ∀ D ξ, G D ξ → ∑ y, (if ∀ l, ¬ A (D l) y then channelExt K n (enc D ξ) y else 0) ≤ B) :
    ∑ C' : Fin M' → Ξ, iidPMF ν M' C' * ∑ C : Fin M → Fin L → X, iidPMF (iidPMF μ L) M C *
        ∑ y, (if subcodeDecode A C m₀ y ≠ m then channelExt K n (enc (C m) (C' m')) y else 0) ≤
      B + ∑ D : Fin L → X, ∑ ξ, iidPMF μ L D * ν ξ * (if G D ξ then 0 else 1) + M * (L * η) := by
  have hνM := iidPMF_isPMF hν M'
  have hμL := iidPMF_isPMF hμ L
  have hE0 : ∀ z y, 0 ≤ channelExt K n z y := fun z y => channelExt_nonneg hK z y
  have hE1 : ∀ z, ∑ y, channelExt K n z y = 1 := fun z => ((hK.ext n) z).sum_eq_one
  set F : Ξ → ℝ := fun ξ => ∑ D : Fin L → X, iidPMF μ L D *
    ∑ y, (if ∀ l, ¬ A (D l) y then channelExt K n (enc D ξ) y else 0)
  have hC' : ∀ C' : Fin M' → Ξ, ∑ C : Fin M → Fin L → X, iidPMF (iidPMF μ L) M C *
      ∑ y, (if subcodeDecode A C m₀ y ≠ m then channelExt K n (enc (C m) (C' m')) y else 0) ≤
      F (C' m') + M * (L * η) := fun C' =>
    sum_codebook_subcode_le hμ m₀ A (fun D y => channelExt K n (enc D (C' m')) y)
      (fun D y => hE0 _ _) (fun D => (hE1 _).le) hη₀ hη m
  have hFb : ∀ ξ, F ξ ≤ B + ∑ D : Fin L → X, iidPMF μ L D * (if G D ξ then 0 else 1) := fun ξ => by
    have hD : ∀ D, iidPMF μ L D *
        ∑ y, (if ∀ l, ¬ A (D l) y then channelExt K n (enc D ξ) y else 0) ≤
        iidPMF μ L D * B + iidPMF μ L D * (if G D ξ then 0 else 1) := fun D => by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (hμL.nonneg D)
      split_ifs with hg
      · simpa using hG D ξ hg
      · have : ∑ y, (if ∀ l, ¬ A (D l) y then channelExt K n (enc D ξ) y else 0) ≤
            ∑ y, channelExt K n (enc D ξ) y := sum_le_sum fun y _ => by
          split_ifs
          · exact le_rfl
          · exact hE0 _ _
        rw [hE1] at this
        linarith
    refine (sum_le_sum fun D _ => hD D).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_mul, hμL.sum_eq_one, one_mul]
  calc ∑ C' : Fin M' → Ξ, iidPMF ν M' C' * ∑ C : Fin M → Fin L → X, iidPMF (iidPMF μ L) M C *
        ∑ y, (if subcodeDecode A C m₀ y ≠ m then channelExt K n (enc (C m) (C' m')) y else 0)
      ≤ ∑ C' : Fin M' → Ξ, iidPMF ν M' C' * (F (C' m') + M * (L * η)) :=
        sum_le_sum fun C' _ => mul_le_mul_of_nonneg_left (hC' C') (hνM.nonneg C')
    _ = ∑ ξ, ν ξ * F ξ + M * (L * η) := by
        rw [← sum_iidPMF_eval hν m' F]
        simp_rw [mul_add]
        rw [sum_add_distrib, ← sum_mul, hνM.sum_eq_one, one_mul]
    _ ≤ ∑ ξ, ν ξ * (B + ∑ D : Fin L → X, iidPMF μ L D * (if G D ξ then 0 else 1)) +
          M * (L * η) :=
        add_le_add (sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (hFb ξ) (hν.nonneg ξ)) le_rfl
    _ = _ := by
        simp_rw [mul_add]
        rw [sum_add_distrib, ← sum_mul, hν.sum_eq_one, one_mul]
        congr 2
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

end Side

/-! ### Marton's scheme -/

section Marton

variable {𝒰₁ 𝒰₂ α β₁ β₂ : Type*} [Fintype 𝒰₁] [Fintype 𝒰₂] [Fintype β₁] [Fintype β₂]
  {q : 𝒰₁ × 𝒰₂ → ℝ} {W : α → β₁ × β₂ → ℝ}

/-- The channel `p(y₁ | u₁, u₂) = p(y₁ | x(u₁, u₂))`. -/
def martonK₁ (x : 𝒰₁ × 𝒰₂ → α) (W : α → β₁ × β₂ → ℝ) : 𝒰₁ × 𝒰₂ → β₁ → ℝ := fun z => bcMarg₁ W (x z)

/-- The channel `p(y₂ | u₁, u₂) = p(y₂ | x(u₁, u₂))`. -/
def martonK₂ (x : 𝒰₁ × 𝒰₂ → α) (W : α → β₁ × β₂ → ℝ) : 𝒰₁ × 𝒰₂ → β₂ → ℝ := fun z => bcMarg₂ W (x z)

/-- `I(U₁; Y₁)`. -/
def martonInfo₁ (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun w : (𝒰₁ × 𝒰₂) × β₁ => w.1.1 : Prod.snd ; jointOf q (martonK₁ x W)]

/-- `I(U₂; Y₂)`. -/
def martonInfo₂ (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  I[fun w : (𝒰₁ × 𝒰₂) × β₂ => w.1.2 : Prod.snd ; jointOf q (martonK₂ x W)]

/-- `I(U₁; U₂)`. -/
def martonInfo₁₂ (q : 𝒰₁ × 𝒰₂ → ℝ) : ℝ := I[Prod.fst : Prod.snd ; q]

omit [Fintype 𝒰₁] [Fintype 𝒰₂] [Fintype β₁] in
lemma martonK₁_isChannel [Fintype β₁] (hW : IsChannel W) (x : 𝒰₁ × 𝒰₂ → α) :
    IsChannel (martonK₁ x W) := fun z => hW.bcMarg₁ (x z)

omit [Fintype 𝒰₁] [Fintype 𝒰₂] in
lemma martonK₂_isChannel (hW : IsChannel W) (x : 𝒰₁ × 𝒰₂ → α) :
    IsChannel (martonK₂ x W) := fun z => hW.bcMarg₂ (x z)

/-- `I(U; Y)` in terms of the pmf of `(Y, U)`. -/
lemma mutualInfo_compYU {𝒵 𝒰 β : Type*} [Fintype 𝒵] [Fintype 𝒰] [Fintype β] (q : 𝒵 → ℝ)
    (K : 𝒵 → β → ℝ) (f : 𝒵 → 𝒰) :
    I[Prod.snd : Prod.fst ; compYU q K f] =
      I[fun w : 𝒵 × β => f w.1 : Prod.snd ; jointOf q K] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [compYU, ← dist_comp_eq]
  rfl

/-- The second marginal of `(Y, U)` is the law of `U`. -/
lemma margSnd_compYU {𝒵 𝒰 β : Type*} [Fintype 𝒵] [Fintype 𝒰] [Fintype β] {q : 𝒵 → ℝ}
    {K : 𝒵 → β → ℝ} (hK : IsChannel K) (f : 𝒵 → 𝒰) : margSnd (compYU q K f) = dist q f := by
  rw [margSnd, compYU, ← dist_comp_eq]
  have e : (Prod.snd ∘ fun w : 𝒵 × β => (w.2, f w.1)) = f ∘ Prod.fst := rfl
  rw [e, dist_comp_eq, dist_jointOf_fst hK]

open Classical in
/-- The encoder: a pair of sequences of the two subcodebooks in the set `T`, if there is one. -/
def martonEnc {n L₁ L₂ : ℕ} (T : Finset (Fin n → 𝒰₁ × 𝒰₂)) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (D₁ : Fin L₁ → Fin n → 𝒰₁) (D₂ : Fin L₂ → Fin n → 𝒰₂) : Fin n → 𝒰₁ × 𝒰₂ :=
  if h : ∃ p : Fin L₁ × Fin L₂, zipSeq (D₁ p.1) (D₂ p.2) ∈ T then
    zipSeq (D₁ h.choose.1) (D₂ h.choose.2) else zipSeq (D₁ ⟨0, hL₁⟩) (D₂ ⟨0, hL₂⟩)

omit [Fintype 𝒰₁] [Fintype 𝒰₂] [Fintype β₁] [Fintype β₂] in
/-- If there is a pair in `T`, the encoder picks one. -/
lemma martonEnc_spec {n L₁ L₂ : ℕ} {T : Finset (Fin n → 𝒰₁ × 𝒰₂)} {hL₁ : 0 < L₁} {hL₂ : 0 < L₂}
    {D₁ : Fin L₁ → Fin n → 𝒰₁} {D₂ : Fin L₂ → Fin n → 𝒰₂}
    (h : ∃ l₁ l₂, zipSeq (D₁ l₁) (D₂ l₂) ∈ T) :
    martonEnc T hL₁ hL₂ D₁ D₂ ∈ T ∧ (∃ l₁, Prod.fst ∘ martonEnc T hL₁ hL₂ D₁ D₂ = D₁ l₁) ∧
      ∃ l₂, Prod.snd ∘ martonEnc T hL₁ hL₂ D₁ D₂ = D₂ l₂ := by
  obtain ⟨l₁, l₂, hl⟩ := h
  have h' : ∃ p : Fin L₁ × Fin L₂, zipSeq (D₁ p.1) (D₂ p.2) ∈ T := ⟨(l₁, l₂), hl⟩
  have e : martonEnc T hL₁ hL₂ D₁ D₂ = zipSeq (D₁ h'.choose.1) (D₂ h'.choose.2) := by
    simp [martonEnc, h']
  rw [e]
  exact ⟨h'.choose_spec, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

open Classical in
/-- **Random coding for Marton's scheme.** With `L₁`, `L₂` sequences in the subcodebooks, there is a
code with probability of error at most `K₁/n + K₂/n + 2 P₀ + M₁ L₁ η₁ + M₂ L₂ η₂`, where `P₀` is the
probability of the error of the mutual covering lemma and `ηⱼ = e^{-n(I(Uⱼ; Yⱼ) - δ)}`. -/
theorem exists_marton_code_le [Finite α] (hq : IsPMF q) (hW : IsChannel W) (x : 𝒰₁ × 𝒰₂ → α)
    {n M₁ M₂ L₁ L₂ : ℕ} (hn : 0 < n) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {ε' ε : ℝ} (hεε : ε' < ε) :
    ∃ c : BCCode M₁ M₂ n α β₁ β₂, c.errProb W ≤
      (condTypicalityConst (jointOf q (martonK₁ x W)) ε' ε / n +
        (∑ D, coverLaw (iidPMF (margFst q) n) (iidPMF (margSnd q) n) L₁ L₂ D *
          (if ∀ l₁ l₂, zipSeq (D.1 l₁) (D.2 l₂) ∉ robustTypicalSet q n ε' then 1 else 0)) +
        M₁ * (L₁ * exp (-(n * (I[Prod.snd : Prod.fst ; compYU q (martonK₁ x W) Prod.fst] -
          ε * (H[Prod.snd ; compYU q (martonK₁ x W) Prod.fst] +
            H[Prod.snd | Prod.fst ; compYU q (martonK₁ x W) Prod.fst])))))) +
      (condTypicalityConst (jointOf q (martonK₂ x W)) ε' ε / n +
        (∑ D, coverLaw (iidPMF (margFst q) n) (iidPMF (margSnd q) n) L₁ L₂ D *
          (if ∀ l₁ l₂, zipSeq (D.1 l₁) (D.2 l₂) ∉ robustTypicalSet q n ε' then 1 else 0)) +
        M₂ * (L₂ * exp (-(n * (I[Prod.snd : Prod.fst ; compYU q (martonK₂ x W) Prod.snd] -
          ε * (H[Prod.snd ; compYU q (martonK₂ x W) Prod.snd] +
            H[Prod.snd | Prod.fst ; compYU q (martonK₂ x W) Prod.snd])))))) := by
  cases nonempty_fintype α
  have hK₁ := martonK₁_isChannel hW x
  have hK₂ := martonK₂_isChannel hW x
  set T := robustTypicalSet q n ε'
  have hμ₁ : IsPMF (iidPMF (margFst q) n) := iidPMF_isPMF (hq.dist _) n
  have hμ₂ : IsPMF (iidPMF (margSnd q) n) := iidPMF_isPMF (hq.dist _) n
  set q₁ := compYU q (martonK₁ x W) Prod.fst
  set q₂ := compYU q (martonK₂ x W) Prod.snd
  have hq₁ : IsPMF q₁ := (jointOf_isPMF hq hK₁).dist _
  have hq₂ : IsPMF q₂ := (jointOf_isPMF hq hK₂).dist _
  have hm₁ : margSnd q₁ = margFst q := margSnd_compYU hK₁ _
  have hm₂ : margSnd q₂ = margSnd q := margSnd_compYU hK₂ _
  obtain ⟨A₁, hA₁⟩ : ∃ A : (Fin n → 𝒰₁) → (Fin n → β₁) → Prop, ∀ u y, A u y ↔
      zipSeq y u ∈ robustTypicalSet q₁ n ε := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : (Fin n → 𝒰₂) → (Fin n → β₂) → Prop, ∀ u y, A u y ↔
      zipSeq y u ∈ robustTypicalSet q₂ n ε := ⟨_, fun _ _ => Iff.rfl⟩
  have hη₁ : ∀ y, ∑ u, iidPMF (margFst q) n u * (if A₁ u y then 1 else 0) ≤
      exp (-(n * (I[Prod.snd : Prod.fst ; q₁] - ε * (H[Prod.snd ; q₁] +
        H[Prod.snd | Prod.fst ; q₁])))) := fun y => by
    have hb := prob_iidPMF_condRobustTypicalSet_le hq₁ ε y
    rw [hm₁] at hb
    refine le_trans (le_of_eq ?_) hb
    rw [prob]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    congr 1
    ext u
    simp [hA₁, mem_condRobustTypicalSet]
  have hη₂ : ∀ y, ∑ u, iidPMF (margSnd q) n u * (if A₂ u y then 1 else 0) ≤
      exp (-(n * (I[Prod.snd : Prod.fst ; q₂] - ε * (H[Prod.snd ; q₂] +
        H[Prod.snd | Prod.fst ; q₂])))) := fun y => by
    have hb := prob_iidPMF_condRobustTypicalSet_le hq₂ ε y
    rw [hm₂] at hb
    refine le_trans (le_of_eq ?_) hb
    rw [prob]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    congr 1
    ext u
    simp [hA₂, mem_condRobustTypicalSet]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hB₁ : 0 ≤ condTypicalityConst (jointOf q (martonK₁ x W)) ε' ε / n :=
    div_nonneg (sum_nonneg fun z _ => by positivity) hn'.le
  have hB₂ : 0 ≤ condTypicalityConst (jointOf q (martonK₂ x W)) ε' ε / n :=
    div_nonneg (sum_nonneg fun z _ => by positivity) hn'.le
  set enc : (Fin L₁ → Fin n → 𝒰₁) → (Fin L₂ → Fin n → 𝒰₂) → Fin n → 𝒰₁ × 𝒰₂ :=
    martonEnc T hL₁ hL₂
  obtain ⟨G, hGd⟩ : ∃ G : (Fin L₁ → Fin n → 𝒰₁) → (Fin L₂ → Fin n → 𝒰₂) → Prop, ∀ D₁ D₂,
      G D₁ D₂ ↔ ∃ l₁ l₂, zipSeq (D₁ l₁) (D₂ l₂) ∈ T := ⟨_, fun _ _ => Iff.rfl⟩
  have hG₁ : ∀ D₁ D₂, G D₁ D₂ → ∑ y, (if ∀ l, ¬ A₁ (D₁ l) y then
      channelExt (martonK₁ x W) n (enc D₁ D₂) y else 0) ≤
      condTypicalityConst (jointOf q (martonK₁ x W)) ε' ε / n := fun D₁ D₂ h => by
    obtain ⟨hT, ⟨l₁, hl⟩, -⟩ := martonEnc_spec (hL₁ := hL₁) (hL₂ := hL₂) ((hGd _ _).1 h)
    have hb := sum_ite_not_mem_comp_le hq hK₁ Prod.fst hn hεε hT
    refine le_trans (sum_le_sum fun y _ => ?_) hb
    by_cases hAl : ∀ l, ¬ A₁ (D₁ l) y
    · have hne : zipSeq y (Prod.fst ∘ enc D₁ D₂) ∉
          robustTypicalSet (dist (jointOf q (martonK₁ x W)) fun w => (w.2, w.1.1)) n ε := by
        have h' := hAl l₁
        rw [hA₁] at h'
        change zipSeq y (Prod.fst ∘ martonEnc T hL₁ hL₂ D₁ D₂) ∉ _
        rw [hl]
        exact h'
      have e : (if ∀ l, ¬ A₁ (D₁ l) y then channelExt (martonK₁ x W) n (enc D₁ D₂) y else 0) =
          channelExt (martonK₁ x W) n (enc D₁ D₂) y := by
        split_ifs
        rfl
      rw [e]
      split_ifs with h
      · exact absurd h hne
      · exact le_rfl
    · have e : (if ∀ l, ¬ A₁ (D₁ l) y then channelExt (martonK₁ x W) n (enc D₁ D₂) y else 0) =
          0 := by
        split_ifs
        rfl
      rw [e]
      split_ifs
      · exact le_rfl
      · exact channelExt_nonneg hK₁ _ _
  have hG₂ : ∀ D₂ D₁, G D₁ D₂ → ∑ y, (if ∀ l, ¬ A₂ (D₂ l) y then
      channelExt (martonK₂ x W) n (enc D₁ D₂) y else 0) ≤
      condTypicalityConst (jointOf q (martonK₂ x W)) ε' ε / n := fun D₂ D₁ h => by
    obtain ⟨hT, -, ⟨l₂, hl⟩⟩ := martonEnc_spec (hL₁ := hL₁) (hL₂ := hL₂) ((hGd _ _).1 h)
    have hb := sum_ite_not_mem_comp_le hq hK₂ Prod.snd hn hεε hT
    refine le_trans (sum_le_sum fun y _ => ?_) hb
    by_cases hAl : ∀ l, ¬ A₂ (D₂ l) y
    · have hne : zipSeq y (Prod.snd ∘ enc D₁ D₂) ∉
          robustTypicalSet (dist (jointOf q (martonK₂ x W)) fun w => (w.2, w.1.2)) n ε := by
        have h' := hAl l₂
        rw [hA₂] at h'
        change zipSeq y (Prod.snd ∘ martonEnc T hL₁ hL₂ D₁ D₂) ∉ _
        rw [hl]
        exact h'
      have e : (if ∀ l, ¬ A₂ (D₂ l) y then channelExt (martonK₂ x W) n (enc D₁ D₂) y else 0) =
          channelExt (martonK₂ x W) n (enc D₁ D₂) y := by
        split_ifs
        rfl
      rw [e]
      split_ifs with h
      · exact absurd h hne
      · exact le_rfl
    · have e : (if ∀ l, ¬ A₂ (D₂ l) y then channelExt (martonK₂ x W) n (enc D₁ D₂) y else 0) =
          0 := by
        split_ifs
        rfl
      rw [e]
      split_ifs
      · exact le_rfl
      · exact channelExt_nonneg hK₂ _ _
  -- The probability of no jointly typical pair.
  set P0 := ∑ D, coverLaw (iidPMF (margFst q) n) (iidPMF (margSnd q) n) L₁ L₂ D *
    (if ∀ l₁ l₂, zipSeq (D.1 l₁) (D.2 l₂) ∉ T then 1 else 0)
  have hbad₁ : ∑ D₁, ∑ D₂, iidPMF (iidPMF (margFst q) n) L₁ D₁ *
      iidPMF (iidPMF (margSnd q) n) L₂ D₂ * (if G D₁ D₂ then 0 else 1) = P0 := by
    simp only [P0]
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun D₁ _ => sum_congr rfl fun D₂ _ => ?_
    simp only [coverLaw]
    congr 1
    by_cases h : G D₁ D₂
    · have h' : ¬ ∀ l₁ l₂, zipSeq (D₁ l₁) (D₂ l₂) ∉ T := by
        obtain ⟨l₁, l₂, hl⟩ := (hGd _ _).1 h
        exact fun hn => hn l₁ l₂ hl
      simp [h, h']
    · have h' : ∀ l₁ l₂, zipSeq (D₁ l₁) (D₂ l₂) ∉ T := fun l₁ l₂ hl =>
        h ((hGd _ _).2 ⟨l₁, l₂, hl⟩)
      simp [h, h']
  have hbad₂ : ∑ D₂, ∑ D₁, iidPMF (iidPMF (margSnd q) n) L₂ D₂ *
      iidPMF (iidPMF (margFst q) n) L₁ D₁ * (if G D₁ D₂ then 0 else 1) = P0 := by
    rw [← hbad₁, sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hP := coverLaw_isPMF (iidPMF_isPMF hμ₁ L₁) (iidPMF_isPMF hμ₂ L₂) (L₁ := M₁) (L₂ := M₂)
  set m₁ : Fin M₁ := ⟨0, hM₁⟩
  set m₂ : Fin M₂ := ⟨0, hM₂⟩
  let code : (Fin M₁ → Fin L₁ → Fin n → 𝒰₁) × (Fin M₂ → Fin L₂ → Fin n → 𝒰₂) →
      BCCode M₁ M₂ n α β₁ β₂ := fun θ =>
    ⟨fun w i => x (enc (θ.1 w.1) (θ.2 w.2) i), subcodeDecode A₁ θ.1 m₁, subcodeDecode A₂ θ.2 m₂⟩
  obtain ⟨θ, hθ⟩ := exists_bcCode_errProb_le_of_sum_codebook hP hW hM₁ hM₂ code
    (b₁ := condTypicalityConst (jointOf q (martonK₁ x W)) ε' ε / n + P0 +
      M₁ * (L₁ * exp (-(n * (I[Prod.snd : Prod.fst ; q₁] - ε * (H[Prod.snd ; q₁] +
        H[Prod.snd | Prod.fst ; q₁]))))))
    (b₂ := condTypicalityConst (jointOf q (martonK₂ x W)) ε' ε / n + P0 +
      M₂ * (L₂ * exp (-(n * (I[Prod.snd : Prod.fst ; q₂] - ε * (H[Prod.snd ; q₂] +
        H[Prod.snd | Prod.fst ; q₂]))))))
    (fun w => by
      have side := sum_subcode_side_le hμ₁ (iidPMF_isPMF hμ₂ L₂) m₁ w.1 w.2 A₁ hK₁ enc
        (exp_pos _).le hη₁ hB₁ G hG₁
      rw [hbad₁] at side
      refine le_trans (le_of_eq ?_) side
      rw [Fintype.sum_prod_type_right]
      refine sum_congr rfl fun C₂ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun C₁ _ => ?_
      simp only [coverLaw]
      rw [mul_comm (iidPMF _ M₁ C₁), mul_assoc]
      rfl)
    (fun w => by
      have side := sum_subcode_side_le hμ₂ (iidPMF_isPMF hμ₁ L₁) m₂ w.2 w.1 A₂ hK₂
        (fun D₂ D₁ => enc D₁ D₂) (exp_pos _).le hη₂ hB₂ (fun D₂ D₁ => G D₁ D₂) hG₂
      rw [hbad₂] at side
      refine le_trans (le_of_eq ?_) side
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun C₁ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun C₂ _ => ?_
      simp only [coverLaw]
      rw [mul_assoc]
      rfl)
  exact ⟨code θ, hθ⟩

/-! ### The inner bound -/

/-- If `exp(n r) ≤ L`, then `exp(n s) / L ≤ exp(n (s - r))`. -/
lemma exp_div_le_of_le {n : ℕ} {r s : ℝ} {L : ℕ} (hL : exp (n * r) ≤ L) :
    exp (n * s) / L ≤ exp (n * (s - r)) := by
  have hpos : (0 : ℝ) < L := lt_of_lt_of_le (exp_pos _) hL
  rw [div_le_iff₀ hpos]
  calc exp (n * s) = exp (n * (s - r)) * exp (n * r) := by
        rw [← exp_add]
        congr 1
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hL (exp_pos _).le

/-- The packing term tends to `0` if the exponents add up to `-γ`. -/
lemma marton_pack_le {n L : ℕ} {R r I γ η : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (he : n * (R * log 2) + (n * r + -(n * (I - γ))) = -(n * γ))
    (hη : η ≤ exp (-(n * (I - γ)))) (hη0 : 0 ≤ η) (hL : L = ⌈exp (n * r)⌉₊) :
    ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) * ((L : ℝ) * η) ≤ 4 * exp (-(n * γ)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hLle : (L : ℝ) ≤ 2 * exp (n * r) := by
    have h1 := (Nat.ceil_lt_add_one (exp_pos (n * r)).le).le
    have h2 := one_le_exp (mul_nonneg hn0 hr)
    rw [hL]
    linarith
  have hM := two_pow_ceil_le n hR
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  calc ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) * ((L : ℝ) * η)
      ≤ (2 * exp (n * (R * log 2))) * ((2 * exp (n * r)) * exp (-(n * (I - γ)))) :=
        mul_le_mul hM (mul_le_mul hLle hη hη0 (by positivity)) (mul_nonneg hL0 hη0)
          (by positivity)
    _ = 4 * (exp (n * (R * log 2)) * (exp (n * r) * exp (-(n * (I - γ))))) := by ring
    _ = 4 * exp (-(n * γ)) := by
        rw [← exp_add, ← exp_add, he]

/-- The bound of the mutual covering lemma tends to `0`. -/
lemma marton_cover_le {n L₁ L₂ : ℕ} {Iu d r₁ r₂ γ : ℝ} (hL₁ : L₁ = ⌈exp (n * r₁)⌉₊)
    (hL₂ : L₂ = ⌈exp (n * r₂)⌉₊) (h1 : Iu + d ≤ -γ + (r₁ + r₂)) (h2 : 2 * d - r₁ ≤ -γ)
    (h3 : 2 * d - r₂ ≤ -γ) :
    4 * (exp (n * (Iu + d)) / (L₁ * L₂) + exp (n * (2 * d)) / L₁ + exp (n * (2 * d)) / L₂) ≤
      12 * exp (-(n * γ)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL₁ge : exp (n * r₁) ≤ (L₁ : ℝ) := by rw [hL₁]; exact Nat.le_ceil _
  have hL₂ge : exp (n * r₂) ≤ (L₂ : ℝ) := by rw [hL₂]; exact Nat.le_ceil _
  have hA : exp (n * (Iu + d)) / (L₁ * L₂) ≤ exp (-(n * γ)) := by
    have hprod : exp (n * (r₁ + r₂)) ≤ (L₁ : ℝ) * L₂ := by
      rw [mul_add, exp_add]
      exact mul_le_mul hL₁ge hL₂ge (exp_pos _).le (le_trans (exp_pos _).le hL₁ge)
    have hpos : (0 : ℝ) < (L₁ : ℝ) * L₂ := lt_of_lt_of_le (exp_pos _) hprod
    rw [div_le_iff₀ hpos]
    calc exp (n * (Iu + d)) ≤ exp (-(n * γ)) * exp (n * (r₁ + r₂)) := by
          rw [← exp_add]
          exact exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left h1 hn0])
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (exp_pos _).le
  have hB₁ : exp (n * (2 * d)) / L₁ ≤ exp (-(n * γ)) :=
    (exp_div_le_of_le hL₁ge).trans
      (exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left h2 hn0]))
  have hB₂ : exp (n * (2 * d)) / L₂ ≤ exp (-(n * γ)) :=
    (exp_div_le_of_le hL₂ge).trans
      (exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left h3 hn0]))
  linarith

/-- The exponent `η` of the packing term, for the slack `2 ε' c ≤ γ`. -/
lemma marton_eta_le {n : ℕ} {I c ε' γ : ℝ} (h : 2 * ε' * c ≤ γ) :
    exp (-(n * (I - 2 * ε' * c))) ≤ exp (-(n * (I - γ))) :=
  exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) n)])

/-- Marton's scheme, for given parameters. -/
theorem isAchievableBCBits_of_marton_aux [Finite α] (hq : IsPMF q) (hW : IsChannel W)
    (x : 𝒰₁ × 𝒰₂ → α) {R₁ R₂ ε' γ r₁ r₂ : ℝ} (h₁ : 0 ≤ R₁) (h₂ : 0 ≤ R₂) (hε' : 0 < ε')
    (hε'12 : ε' ≤ 1 / 2) (hγ : 0 < γ) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hc₁ : 2 * ε' * (H[Prod.snd ; compYU q (martonK₁ x W) Prod.fst] +
      H[Prod.snd | Prod.fst ; compYU q (martonK₁ x W) Prod.fst]) ≤ γ)
    (hc₂ : 2 * ε' * (H[Prod.snd ; compYU q (martonK₂ x W) Prod.snd] +
      H[Prod.snd | Prod.fst ; compYU q (martonK₂ x W) Prod.snd]) ≤ γ)
    (e₁ : R₁ * log 2 + r₁ + -(I[Prod.snd : Prod.fst ; compYU q (martonK₁ x W) Prod.fst] - γ) = -γ)
    (e₂ : R₂ * log 2 + r₂ + -(I[Prod.snd : Prod.fst ; compYU q (martonK₂ x W) Prod.snd] - γ) = -γ)
    (hu : I[Prod.snd : Prod.fst ; q] + ε' * mutualCoveringConst q ≤ -γ + (r₁ + r₂))
    (hd₁ : 2 * (ε' * mutualCoveringConst q) - r₁ ≤ -γ)
    (hd₂ : 2 * (ε' * mutualCoveringConst q) - r₂ ≤ -γ) : IsAchievableBCBits W R₁ R₂ := by
  cases nonempty_fintype α
  classical
  have hev := eventually_sum_mutualCovering_typical_le hq hε' hε'12
  have hL₁ : ∀ n : ℕ, 0 < ⌈exp (n * r₁)⌉₊ := fun n => Nat.ceil_pos.2 (exp_pos _)
  have hL₂ : ∀ n : ℕ, 0 < ⌈exp (n * r₂)⌉₊ := fun n => Nat.ceil_pos.2 (exp_pos _)
  have hM₁ : ∀ n : ℕ, 0 < 2 ^ ⌈n * R₁⌉₊ := fun n => by positivity
  have hM₂ : ∀ n : ℕ, 0 < 2 ^ ⌈n * R₂⌉₊ := fun n => by positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K, K = condTypicalityConst (jointOf q (martonK₁ x W)) ε' (2 * ε') := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K, K = condTypicalityConst (jointOf q (martonK₂ x W)) ε' (2 * ε') := ⟨_, rfl⟩
  have hcode : ∀ n : ℕ, ∃ c : BCCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α β₁ β₂, 0 < n →
      (∑ D, coverLaw (iidPMF (margFst q) n) (iidPMF (margSnd q) n) ⌈exp (n * r₁)⌉₊
          ⌈exp (n * r₂)⌉₊ D *
          (if ∀ l₁ l₂, zipSeq (D.1 l₁) (D.2 l₂) ∉ robustTypicalSet q n ε' then 1 else 0)) ≤
          12 * exp (-(n * γ)) →
      c.errProb W ≤ K₁ / n + K₂ / n + 32 * exp (-(n * γ)) := fun n => by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · obtain ⟨z₀⟩ : Nonempty (𝒰₁ × 𝒰₂) := by
        by_contra h
        rw [not_nonempty_iff] at h
        simpa using hq.sum_eq_one
      exact ⟨⟨fun _ _ => x z₀, fun _ => ⟨0, hM₁ n⟩, fun _ => ⟨0, hM₂ n⟩⟩,
        fun h => absurd h (by omega)⟩
    obtain ⟨c, hc⟩ := exists_marton_code_le hq hW x hn (hM₁ n) (hM₂ n) (hL₁ n) (hL₂ n)
      (ε' := ε') (ε := 2 * ε') (by linarith)
    refine ⟨c, fun _ hP => hc.trans ?_⟩
    have p₁ := marton_pack_le (n := n) (R := R₁) (r := r₁) (γ := γ) (L := ⌈exp (n * r₁)⌉₊)
      (I := I[Prod.snd : Prod.fst ; compYU q (martonK₁ x W) Prod.fst]) h₁ hr₁
      (by linear_combination (n : ℝ) * e₁)
      (marton_eta_le hc₁) (exp_pos _).le rfl
    have p₂ := marton_pack_le (n := n) (R := R₂) (r := r₂) (γ := γ) (L := ⌈exp (n * r₂)⌉₊)
      (I := I[Prod.snd : Prod.fst ; compYU q (martonK₂ x W) Prod.snd]) h₂ hr₂
      (by linear_combination (n : ℝ) * e₂)
      (marton_eta_le hc₂) (exp_pos _).le rfl
    rw [← hK₁, ← hK₂]
    linarith
  choose c hc using hcode
  refine ⟨c, ?_⟩
  have hGlim : Tendsto (fun n : ℕ => K₁ / n + K₂ / n + 32 * exp (-(n * γ))) atTop (𝓝 0) := by
    have h1 := tendsto_const_div_atTop_nhds_zero_nat K₁
    have h2 := tendsto_const_div_atTop_nhds_zero_nat K₂
    have h3 := (tendsto_exp_neg_mul_nat hγ).const_mul 32
    simpa using (h1.add h2).add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hGlim
    (Eventually.of_forall fun n => superposition_errProb_nonneg hW (c n)) ?_
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  exact hc n hn0 ((hn (hL₁ n) (hL₂ n)).trans (marton_cover_le rfl rfl hu hd₁ hd₂))

/-- **Achievability for Marton's scheme.** A pair of nonnegative rates `(R₁, R₂)` is achievable if
`R₁ < I(U₁; Y₁)`, `R₂ < I(U₂; Y₂)` and `R₁ + R₂ < I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)`, in bits. -/
theorem isAchievableBCBits_of_marton [Finite α] (hq : IsPMF q) (hW : IsChannel W)
    (x : 𝒰₁ × 𝒰₂ → α) {R₁ R₂ : ℝ} (h₁ : 0 ≤ R₁) (h₂ : 0 ≤ R₂)
    (h1 : R₁ * log 2 < martonInfo₁ q x W) (h2 : R₂ * log 2 < martonInfo₂ q x W)
    (h12 : (R₁ + R₂) * log 2 < martonInfo₁ q x W + martonInfo₂ q x W - martonInfo₁₂ q) :
    IsAchievableBCBits W R₁ R₂ := by
  have hK₁ := martonK₁_isChannel hW x
  have hK₂ := martonK₂_isChannel hW x
  have hq₁ : IsPMF (compYU q (martonK₁ x W) Prod.fst) := (jointOf_isPMF hq hK₁).dist _
  have hq₂ : IsPMF (compYU q (martonK₂ x W) Prod.snd) := (jointOf_isPMF hq hK₂).dist _
  have eI₁ : I[Prod.snd : Prod.fst ; compYU q (martonK₁ x W) Prod.fst] = martonInfo₁ q x W :=
    mutualInfo_compYU q (martonK₁ x W) Prod.fst
  have eI₂ : I[Prod.snd : Prod.fst ; compYU q (martonK₂ x W) Prod.snd] = martonInfo₂ q x W :=
    mutualInfo_compYU q (martonK₂ x W) Prod.snd
  have eIu : martonInfo₁₂ q = I[Prod.snd : Prod.fst ; q] := mutualInfo_comm hq _ _
  rw [eIu] at h12
  obtain ⟨a, ha⟩ : ∃ a, a = martonInfo₁ q x W - R₁ * log 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = martonInfo₂ q x W - R₂ * log 2 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = a + b - I[Prod.snd : Prod.fst ; q] := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hg0 : 0 < g := by
    rw [hg, ha, hb]
    linarith
  obtain ⟨γ, hγ0, hγa, hγb, hγg⟩ : ∃ γ : ℝ, 0 < γ ∧ 6 * γ ≤ a ∧ 6 * γ ≤ b ∧ 6 * γ ≤ g := by
    refine ⟨min a (min b g) / 6, div_pos (lt_min ha0 (lt_min hb0 hg0)) (by norm_num), ?_, ?_, ?_⟩
    · linarith [min_le_left a (min b g)]
    · linarith [(min_le_right a (min b g)).trans (min_le_left b g)]
    · linarith [(min_le_right a (min b g)).trans (min_le_right b g)]
  obtain ⟨C, hCd⟩ : ∃ C, C = mutualCoveringConst q := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCd ▸ mutualCoveringConst_nonneg hq
  obtain ⟨c₁, hc₁d⟩ : ∃ c, c = H[Prod.snd ; compYU q (martonK₁ x W) Prod.fst] +
      H[Prod.snd | Prod.fst ; compYU q (martonK₁ x W) Prod.fst] := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂d⟩ : ∃ c, c = H[Prod.snd ; compYU q (martonK₂ x W) Prod.snd] +
      H[Prod.snd | Prod.fst ; compYU q (martonK₂ x W) Prod.snd] := ⟨_, rfl⟩
  have hc₁ : 0 ≤ c₁ := by
    rw [hc₁d]
    exact add_nonneg (entropyRV_nonneg hq₁ _) (condEntropy_nonneg hq₁ _ _)
  have hc₂ : 0 ≤ c₂ := by
    rw [hc₂d]
    exact add_nonneg (entropyRV_nonneg hq₂ _) (condEntropy_nonneg hq₂ _ _)
  have hden : 0 < 1 + C + 2 * c₁ + 2 * c₂ := by linarith
  obtain ⟨ε', hε'⟩ : ∃ ε', ε' = min (1 / 2) (γ / (1 + C + 2 * c₁ + 2 * c₂)) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by
    rw [hε']
    exact lt_min (by norm_num) (div_pos hγ0 hden)
  have hε'12 : ε' ≤ 1 / 2 := by
    rw [hε']
    exact min_le_left _ _
  have hε'γ : ε' * (1 + C + 2 * c₁ + 2 * c₂) ≤ γ := by
    refine (le_div_iff₀ hden).1 ?_
    rw [hε']
    exact min_le_right _ _
  have hεC : ε' * C ≤ γ := by nlinarith [mul_nonneg hε'0.le hc₁, mul_nonneg hε'0.le hc₂]
  have hεc₁ : 2 * ε' * c₁ ≤ γ := by nlinarith [mul_nonneg hε'0.le hC, mul_nonneg hε'0.le hc₂]
  have hεc₂ : 2 * ε' * c₂ ≤ γ := by nlinarith [mul_nonneg hε'0.le hC, mul_nonneg hε'0.le hc₁]
  refine isAchievableBCBits_of_marton_aux hq hW x (ε' := ε') (γ := γ) (r₁ := a - 2 * γ)
    (r₂ := b - 2 * γ) h₁ h₂ hε'0 hε'12 hγ0 (by linarith) (by linarith) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hc₁d]
    exact hεc₁
  · rw [← hc₂d]
    exact hεc₂
  · rw [eI₁, ha]
    ring
  · rw [eI₂, hb]
    ring
  · rw [← hCd]
    linarith
  · rw [← hCd]
    linarith
  · rw [← hCd]
    linarith

/-- **Theorem 2 of [elgamal2010], Lecture 9 (Marton's inner bound)**, in bits, with `Uⱼ` on `Fin kⱼ`
and nonnegative rates: `R₁ < I(U₁; Y₁)`, `R₂ < I(U₂; Y₂)`,
`R₁ + R₂ < I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)` for some `p(u₁, u₂)` and `x(u₁, u₂)`. -/
def martonRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ (k₁ k₂ : ℕ) (q : Fin k₁ × Fin k₂ → ℝ) (x : Fin k₁ × Fin k₂ → α),
    IsPMF q ∧ R.1 < martonInfo₁ q x W / log 2 ∧ R.2 < martonInfo₂ q x W / log 2 ∧
      R.1 + R.2 < (martonInfo₁ q x W + martonInfo₂ q x W - martonInfo₁₂ q) / log 2}

/-- **Theorem 2 of [elgamal2010], Lecture 9 (Marton's inner bound).** -/
theorem martonRegionBits_subset [Finite α] (hW : IsChannel W) :
    martonRegionBits W ⊆ {R | IsAchievableBCBits W R.1 R.2} := by
  rintro R ⟨h₁, h₂, k₁, k₂, q, x, hq, h1, h2, h12⟩
  have hl := log_pos one_lt_two
  exact isAchievableBCBits_of_marton hq hW x h₁ h₂ ((lt_div_iff₀ hl).1 h1) ((lt_div_iff₀ hl).1 h2)
    ((lt_div_iff₀ hl).1 h12)

/-- `I(U₁; U₂) = 0` for independent `U₁`, `U₂`. -/
lemma martonInfo₁₂_prodDist {p₁ : 𝒰₁ → ℝ} {p₂ : 𝒰₂ → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) :
    martonInfo₁₂ (prodDist p₁ p₂) = 0 := by
  classical
  have hq := hp₁.prodDist hp₂
  refine (mutualInfo_eq_zero_iff hq _ _).2 fun a b => ?_
  have h1 : dist (prodDist p₁ p₂) Prod.fst a = p₁ a := by
    rw [dist_fst]
    simp [prodDist, ← mul_sum, hp₂.sum_eq_one]
  have h2 : dist (prodDist p₁ p₂) Prod.snd b = p₂ b := by
    rw [dist_snd]
    simp [prodDist, ← sum_mul, hp₁.sum_eq_one]
  rw [h1, h2, dist_pair_fst_snd]
  rfl

/-- **Theorem 1 of [elgamal2010], Lecture 9 (the Cover–van der Meulen inner bound)**, in bits:
`R₁ < I(U₁; Y₁)`, `R₂ < I(U₂; Y₂)` for some `p(u₁) p(u₂)` and `x(u₁, u₂)`. -/
def coverVanDerMeulenRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ (k₁ k₂ : ℕ) (p₁ : Fin k₁ → ℝ) (p₂ : Fin k₂ → ℝ)
    (x : Fin k₁ × Fin k₂ → α), IsPMF p₁ ∧ IsPMF p₂ ∧
      R.1 < martonInfo₁ (prodDist p₁ p₂) x W / log 2 ∧
      R.2 < martonInfo₂ (prodDist p₁ p₂) x W / log 2}

/-- Marton's inner bound reduces to the Cover–van der Meulen bound for independent `U₁`, `U₂`. -/
theorem coverVanDerMeulenRegionBits_subset_martonRegionBits :
    coverVanDerMeulenRegionBits W ⊆ martonRegionBits W := by
  rintro R ⟨h₁, h₂, k₁, k₂, p₁, p₂, x, hp₁, hp₂, h1, h2⟩
  refine ⟨h₁, h₂, k₁, k₂, prodDist p₁ p₂, x, hp₁.prodDist hp₂, h1, h2, ?_⟩
  rw [martonInfo₁₂_prodDist hp₁ hp₂, sub_zero, add_div]
  linarith

/-- **Theorem 1 of [elgamal2010], Lecture 9 (the Cover–van der Meulen inner bound).** -/
theorem coverVanDerMeulenRegionBits_subset [Finite α] (hW : IsChannel W) :
    coverVanDerMeulenRegionBits W ⊆ {R | IsAchievableBCBits W R.1 R.2} :=
  coverVanDerMeulenRegionBits_subset_martonRegionBits.trans (martonRegionBits_subset hW)

end Marton

end InfoTheory
