/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCMoreCapableLaws

/-!
# The less noisy and more capable broadcast channels: converses

The converses for the less noisy and the more capable DM-BC of Lecture 5 of El Gamal and Kim. The
capacity region of a less noisy DM-BC is the closure of the set of rate pairs with
`R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` for some `p(u, x)`, and that of a more capable DM-BC is the
closure of the set of rate pairs with `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ I(X; Y₁)`.

## Main definitions

* `moreCapableAltRegionBits W`, `lessNoisyAltRegionBits W`: the alternative characterizations of
  pages 5-41 and 5-45 of the notes.

## Main statements

* `IsMoreCapable.bcInfoXY₂U_le_bcInfoXY₁U`: `I(X; Y₂ | V) ≤ I(X; Y₁ | V)` if `Y₁` is more capable.
* `mem_superpositionClosedRegionBits_of_mem_moreCapableAltRegionBits`: the "check!" of page 5-41,
  the alternative region with `R₂ ≥ 0` lies in the superposition coding region.
* `IsAchievableBCBits.mem_closure_superpositionClosedRegionBits`,
  `bcCapacityRegionBits_eq_closure_superpositionClosedRegionBits`: the more capable DM-BC.
* `IsAchievableBCBits.mem_closure_degradedBCRegionBits_of_isLessNoisy`,
  `IsLessNoisy.bcCapacityRegionBits_eq_closure_degradedBCRegionBits`: the less noisy DM-BC.

## Implementation notes

The formal regions are not intersected with `R₁, R₂ ≥ 0`. The alternative regions then contain
points with a very negative `R₂` and a very large `R₁`, which are not achievable, so the passage to
the superposition coding region assumes `R₂ ≥ 0`. The final statements need no such assumption,
since `⌈nR⌉₊ = ⌈n max(R, 0)⌉₊`, and both the capacity region and the regions are closed under
lowering the rates.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The more capable condition, conditioned on an auxiliary random variable -/

section SingleLetter

variable {α β 𝒰 : Type*} [Fintype α] [Fintype β] [Fintype 𝒰]

private lemma moreCapable_cond_isPMF {q : 𝒰 × α → ℝ} (hq : IsPMF q) {u : 𝒰}
    (hu : ∑ x, q (u, x) ≠ 0) : IsPMF fun x => q (u, x) / ∑ x', q (u, x') := by
  have h0 : 0 ≤ ∑ x, q (u, x) := sum_nonneg fun x _ => hq.nonneg _
  refine ⟨fun x => div_nonneg (hq.nonneg _) h0, ?_⟩
  rw [← sum_div, div_self hu]

private lemma moreCapable_eq_zero_of_sum {q : 𝒰 × α → ℝ} (hq : IsPMF q) {u : 𝒰}
    (hu : ∑ x, q (u, x) = 0) (x : α) : q (u, x) = 0 :=
  (sum_eq_zero_iff_of_nonneg fun _ _ => hq.nonneg _).1 hu x (mem_univ x)

/-- `I(X; Y | U) = ∑ᵤ p(u) I(X; Y | U = u)` for the law `p(u, x) p(y | x)`, where the term of `u` is
the mutual information for the input `p(x | u)`. -/
theorem condMutualInfo_jointOf_eq_sum_mutualInfoOf {q : 𝒰 × α → ℝ} (hq : IsPMF q)
    {T : α → β → ℝ} (hT : IsChannel T) :
    I[fun t : (𝒰 × α) × β => t.1.2 : Prod.snd | fun t => t.1.1 ; jointOf q fun t => T t.2] =
      ∑ u, (∑ x, q (u, x)) * mutualInfoOf (fun x => q (u, x) / ∑ x', q (u, x')) T := by
  classical
  have hT' : IsChannel fun t : 𝒰 × α => T t.2 := fun t => hT t.2
  have hJ := jointOf_isPMF hq hT'
  set J := jointOf q fun t : 𝒰 × α => T t.2 with hJdef
  have hU : ∀ u, dist J (fun t : (𝒰 × α) × β => t.1.1) u = ∑ x, q (u, x) := fun u => by
    have h := dist_comp_eq J Prod.fst (Prod.fst : 𝒰 × α → 𝒰)
    rw [dist_jointOf_fst hT'] at h
    have h' : dist J (fun t : (𝒰 × α) × β => t.1.1) = dist q Prod.fst := h
    rw [h', dist_fst]
  have hUY : ∀ u y, dist J (pair (fun t : (𝒰 × α) × β => t.1.1) Prod.snd) (u, y) =
      ∑ x, q (u, x) * T x y := fun u y => by
    simp only [hJdef, dist, jointOf, pair_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and,
      sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  have hch : ∀ u y, dist J (pair (fun t : (𝒰 × α) × β => t.1.1) Prod.snd) (u, y) =
      dist J (fun t : (𝒰 × α) × β => t.1.1) u *
        outDist (fun x => q (u, x) / ∑ x', q (u, x')) T y := fun u y => by
    rw [hUY, hU, outDist]
    by_cases hu : ∑ x, q (u, x) = 0
    · rw [sum_eq_zero fun x _ => by rw [moreCapable_eq_zero_of_sum hq hu, zero_mul], hu, zero_mul]
    · rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      field_simp
  have hA := condEntropy_of_channel (W := fun u => outDist (fun x => q (u, x) / ∑ x', q (u, x')) T)
    id hch
  have hB : H[Prod.snd | pair (fun t : (𝒰 × α) × β => t.1.2) (fun t => t.1.1) ; J] =
      ∑ z : 𝒰 × α, q z * entropy (T z.2) := by
    rw [← condEntropy_jointOf hq hT']
    exact condEntropy_congr_right hJ _ Prod.swap Prod.swap_injective fun _ => rfl
  rw [condMutualInfo_comm hJ, condMutualInfo, hA, hB, Fintype.sum_prod_type, ← sum_sub_distrib]
  refine sum_congr rfl fun u _ => ?_
  rw [Function.id_comp, hU]
  by_cases hu : ∑ x, q (u, x) = 0
  · have h0 : ∑ y, q (u, y) * entropy (T (u, y).2) = 0 :=
      sum_eq_zero fun x _ => by rw [moreCapable_eq_zero_of_sum hq hu, zero_mul]
    rw [h0, hu]
    simp
  · rw [mutualInfoOf_eq (moreCapable_cond_isPMF hq hu) hT, mul_sub, mul_sum]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    field_simp

variable {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] {q : 𝒰 × α → ℝ} {W : α → β₁ × β₂ → ℝ}

/-- `I(X; Y₁ | U) = ∑ᵤ p(u) I(X; Y₁ | U = u)`. -/
lemma bcInfoXY₁U_eq_sum_mutualInfoOf (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₁U q W =
      ∑ u, (∑ x, q (u, x)) * mutualInfoOf (fun x => q (u, x) / ∑ x', q (u, x')) (bcMarg₁ W) := by
  rw [degradedBC_bcInfoXY₁U_eq_jointOf hq hW]
  exact condMutualInfo_jointOf_eq_sum_mutualInfoOf hq hW.bcMarg₁

/-- `I(X; Y₂ | U) = ∑ᵤ p(u) I(X; Y₂ | U = u)`. -/
lemma bcInfoXY₂U_eq_sum_mutualInfoOf (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₂U q W =
      ∑ u, (∑ x, q (u, x)) * mutualInfoOf (fun x => q (u, x) / ∑ x', q (u, x')) (bcMarg₂ W) := by
  classical
  have hd : dist (bcJoint q W) (fun z => (z.1, z.2.2)) = jointOf q fun t => bcMarg₂ W t.2 := by
    funext ⟨t, y₂⟩
    rw [dist, Fintype.sum_prod_type, sum_eq_single t
      (fun t' _ ht' => sum_eq_zero fun y _ => by simp [ht']) (by simp), Fintype.sum_prod_type,
      sum_comm, sum_eq_single y₂ (fun b _ hb => sum_eq_zero fun y₁ _ => by simp [hb]) (by simp)]
    simp [bcJoint, jointOf, bcMarg₂, mul_sum]
  have e := condMutualInfo_comp (bcJoint_isPMF hq hW) (fun z => (z.1, z.2.2))
    (fun t : (𝒰 × α) × β₂ => t.1.2) Prod.snd (fun t => t.1.1)
  rw [hd] at e
  refine e.trans ?_
  exact condMutualInfo_jointOf_eq_sum_mutualInfoOf hq hW.bcMarg₂

/-- **Lecture 5 of [elgamal2010], page 5-44.** The more capable condition implies
`I(X; Y₂ | V) ≤ I(X; Y₁ | V)` whenever `V → X → (Y₁, Y₂)`: apply the condition to each input
`p(x | v)`. -/
theorem IsMoreCapable.bcInfoXY₂U_le_bcInfoXY₁U (h : IsMoreCapable W) (hq : IsPMF q)
    (hW : IsChannel W) : bcInfoXY₂U q W ≤ bcInfoXY₁U q W := by
  rw [bcInfoXY₁U_eq_sum_mutualInfoOf hq hW, bcInfoXY₂U_eq_sum_mutualInfoOf hq hW]
  refine sum_le_sum fun u _ => ?_
  by_cases hu : ∑ x, q (u, x) = 0
  · simp [hu]
  · exact mul_le_mul_of_nonneg_left (h _ (moreCapable_cond_isPMF hq hu))
      (sum_nonneg fun x _ => hq.nonneg _)

/-- `I(X; Y₁)` does not change when the auxiliary random variable is relabelled. -/
lemma moreCapable_bcInfoXY₁_relabel {𝒰' : Type*} [Fintype 𝒰'] (e : 𝒰 ≃ 𝒰') (q : 𝒰 × α → ℝ) :
    bcInfoXY₁ (degradedBCRelabelLaw e q) W = bcInfoXY₁ q W := by
  rw [bcInfoXY₁_eq, bcInfoXY₁_eq]
  congr 1
  funext x
  exact e.symm.sum_comp fun u => q (u, x)

/-- **Time sharing.** `∑ᵢ w(i) I(X; Y₁ | Q = i) ≤ I(X; Y₁)`, by the concavity of the mutual
information in the input. -/
theorem sum_mul_bcInfoXY₁_le_degradedBCTimeShare {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : IsPMF w)
    {q : ι → 𝒰 × α → ℝ} (hq : ∀ i, IsPMF (q i)) (hW : IsChannel W) :
    ∑ i, w i * bcInfoXY₁ (q i) W ≤ bcInfoXY₁ (degradedBCTimeShare w q) W := by
  have hp : ∀ i, IsPMF fun x => ∑ u, q i (u, x) := fun i =>
    ⟨fun x => sum_nonneg fun u _ => (hq i).nonneg _, by
      rw [← (hq i).sum_eq_one, Fintype.sum_prod_type_right]⟩
  have h := (mutualInfoOf_concave_input hW.bcMarg₁).le_map_sum (t := univ) (w := w)
    (p := fun i x => ∑ u, q i (u, x)) (fun i _ => hw.nonneg i) hw.sum_eq_one (fun i _ => hp i)
  simp only [smul_eq_mul] at h
  simp only [bcInfoXY₁_eq]
  refine h.trans (le_of_eq ?_)
  congr 1
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, degradedBCTimeShare,
    Fintype.sum_prod_type, mul_sum]

/-- The law of `(U₀, X)` with `U₀ = u₀` constant, and the same marginal `p(x)` as `q`. -/
def moreCapableConstLaw [DecidableEq 𝒰] (u₀ : 𝒰) (q : 𝒰 × α → ℝ) : 𝒰 × α → ℝ :=
  fun z => if z.1 = u₀ then ∑ u, q (u, z.2) else 0

omit [Fintype α] in
private lemma moreCapableConstLaw_marginal [DecidableEq 𝒰] (u₀ : 𝒰) (q : 𝒰 × α → ℝ) (x : α) :
    ∑ u, moreCapableConstLaw u₀ q (u, x) = ∑ u, q (u, x) := by
  simp [moreCapableConstLaw]

private lemma moreCapableConstLaw_isPMF [DecidableEq 𝒰] (u₀ : 𝒰) (hq : IsPMF q) :
    IsPMF (moreCapableConstLaw u₀ q) := by
  refine ⟨fun z => ?_, ?_⟩
  · simp only [moreCapableConstLaw]
    split_ifs
    exacts [sum_nonneg fun u _ => hq.nonneg _, le_rfl]
  · rw [Fintype.sum_prod_type_right, ← hq.sum_eq_one, Fintype.sum_prod_type_right]
    exact sum_congr rfl fun x _ => moreCapableConstLaw_marginal u₀ q x

/-- For a constant auxiliary random variable, `I(X; Y₁ | U₀) = I(X; Y₁)`. -/
private lemma bcInfoXY₁U_moreCapableConstLaw [DecidableEq 𝒰] (u₀ : 𝒰) (hq : IsPMF q)
    (hW : IsChannel W) : bcInfoXY₁U (moreCapableConstLaw u₀ q) W = bcInfoXY₁ q W := by
  have hp : ∑ x, ∑ u, q (u, x) = 1 := by
    rw [← hq.sum_eq_one, Fintype.sum_prod_type_right]
  have hs : ∀ u, ∑ x, moreCapableConstLaw u₀ q (u, x) = if u = u₀ then 1 else 0 := fun u => by
    by_cases hu : u = u₀
    · simp [moreCapableConstLaw, hu, hp]
    · simp [moreCapableConstLaw, hu]
  rw [bcInfoXY₁U_eq_sum_mutualInfoOf (moreCapableConstLaw_isPMF u₀ hq) hW, bcInfoXY₁_eq,
    sum_eq_single u₀ (fun u _ hu => by rw [hs, ite_eq_right_iff.2 fun h => absurd h hu, zero_mul])
      (by simp)]
  simp only [hs, ite_true, one_mul, div_one]
  congr 1
  funext x
  simp [moreCapableConstLaw]

/-- **Time sharing with a constant auxiliary random variable.** With probability `t` the auxiliary
random variable is replaced by a constant: `I(X; Y₁ | U')` is the mixture of `I(X; Y₁)` and
`I(X; Y₁ | U)`, `I(U'; Y₂) ≥ (1 - t) I(U; Y₂)`, and `I(X; Y₁)` does not decrease. -/
theorem exists_moreCapable_timeShare {k : ℕ} {q : Fin k × α → ℝ} (hq : IsPMF q) (hW : IsChannel W)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : ∃ (k' : ℕ) (q' : Fin k' × α → ℝ), IsPMF q' ∧
      bcInfoXY₁U q' W = t * bcInfoXY₁ q W + (1 - t) * bcInfoXY₁U q W ∧
      (1 - t) * bcInfoUY₂ q W ≤ bcInfoUY₂ q' W ∧ bcInfoXY₁ q W ≤ bcInfoXY₁ q' W := by
  classical
  have hk : Nonempty (Fin k) := by
    by_contra hne
    have : IsEmpty (Fin k) := not_nonempty_iff.1 hne
    have h1 := hq.sum_eq_one
    simp at h1
  obtain ⟨u₀⟩ := hk
  have hq₀ := moreCapableConstLaw_isPMF u₀ hq
  set w : Fin 2 → ℝ := ![t, 1 - t] with hwdef
  set qs : Fin 2 → Fin k × α → ℝ := ![moreCapableConstLaw u₀ q, q] with hqsdef
  have hw : IsPMF w := ⟨fun i => by
    fin_cases i
    · exact ht₀
    · simpa [hwdef] using ht₁, by simp [hwdef, Fin.sum_univ_two]⟩
  have hqs : ∀ i, IsPMF (qs i) := fun i => by
    fin_cases i
    · exact hq₀
    · exact hq
  have hbar := degradedBCTimeShare_isPMF hw hqs
  have hc₀ : bcInfoXY₁ (moreCapableConstLaw u₀ q) W = bcInfoXY₁ q W := by
    rw [bcInfoXY₁_eq, bcInfoXY₁_eq]
    congr 1
    funext x
    exact moreCapableConstLaw_marginal u₀ q x
  have hb₀ : 0 ≤ bcInfoUY₂ (moreCapableConstLaw u₀ q) W :=
    mutualInfo_nonneg (bcJoint_isPMF hq₀ hW) _ _
  refine ⟨_, degradedBCRelabelLaw (Fintype.equivFin _) (degradedBCTimeShare w qs),
    degradedBCRelabelLaw_isPMF _ hbar, ?_, ?_, ?_⟩
  · rw [degradedBC_bcInfoXY₁U_relabel _ hbar hW, bcInfoXY₁U_degradedBCTimeShare hw hqs hW,
      Fin.sum_univ_two]
    simp only [hwdef, hqsdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      bcInfoXY₁U_moreCapableConstLaw u₀ hq hW]
  · rw [degradedBC_bcInfoUY₂_relabel _ hbar hW]
    have h := sum_mul_bcInfoUY₂_le_degradedBCTimeShare (W := W) hw hqs hW
    rw [Fin.sum_univ_two] at h
    simp only [hwdef, hqsdef, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    nlinarith [mul_nonneg ht₀ hb₀]
  · rw [moreCapable_bcInfoXY₁_relabel]
    have h := sum_mul_bcInfoXY₁_le_degradedBCTimeShare (W := W) hw hqs hW
    rw [Fin.sum_univ_two] at h
    simp only [hwdef, hqsdef, Matrix.cons_val_zero, Matrix.cons_val_one, hc₀] at h
    linarith

end SingleLetter

/-! ### The alternative regions -/

section Regions

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

/-- **Lecture 5 of [elgamal2010], page 5-41.** The alternative characterization for the more capable
DM-BC: `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ I(X; Y₁ | U) + I(U; Y₂)`, `R₁ + R₂ ≤ I(X; Y₁)` for some
`p(u, x)`, in bits. As the formal regions are not intersected with `R₁, R₂ ≥ 0`, this set contains
points with a very negative `R₂` and a very large `R₁`, which are not achievable. -/
def moreCapableAltRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧ R.2 ≤ bcInfoUY₂ q W / log 2 ∧
    R.1 + R.2 ≤ (bcInfoXY₁U q W + bcInfoUY₂ q W) / log 2 ∧ R.1 + R.2 ≤ bcInfoXY₁ q W / log 2}

/-- **Lecture 5 of [elgamal2010], page 5-45.** The alternative characterization for the less noisy
DM-BC: `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ I(X; Y₁ | U) + I(U; Y₂)` for some `p(u, x)`, in bits. As the
formal regions are not intersected with `R₁, R₂ ≥ 0`, this set contains points with a very negative
`R₂` and a very large `R₁`, which are not achievable. -/
def lessNoisyAltRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q ∧ R.2 ≤ bcInfoUY₂ q W / log 2 ∧
    R.1 + R.2 ≤ (bcInfoXY₁U q W + bcInfoUY₂ q W) / log 2}

/-- The superposition coding region lies in the alternative region: add the first two bounds. -/
theorem superpositionClosedRegionBits_subset_moreCapableAltRegionBits (W : α → β₁ × β₂ → ℝ) :
    superpositionClosedRegionBits W ⊆ moreCapableAltRegionBits W := by
  rintro R ⟨k, q, hq, h₁, h₂, h₃⟩
  refine ⟨k, q, hq, h₂, ?_, h₃⟩
  rw [add_div]
  linarith

/-- The region `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` lies in the alternative region. -/
theorem degradedBCRegionBits_subset_lessNoisyAltRegionBits (W : α → β₁ × β₂ → ℝ) :
    degradedBCRegionBits W ⊆ lessNoisyAltRegionBits W := by
  rintro R ⟨k, q, hq, h₁, h₂⟩
  refine ⟨k, q, hq, h₂, ?_⟩
  rw [add_div]
  linarith

/-- **Lecture 5 of [elgamal2010], page 5-41 (the "check!").** A point of the alternative region with
`R₂ ≥ 0` lies in the superposition coding region. If `R₁ > I(X; Y₁ | U)`, the auxiliary random
variable is replaced by a constant with probability `t`, where `(1 - t) I(U; Y₂) = R₂`. The
hypothesis `0 ≤ R₂` cannot be dropped, as the alternative region is not bounded in `R₁`. -/
theorem mem_superpositionClosedRegionBits_of_mem_moreCapableAltRegionBits (hW : IsChannel W)
    {R : ℝ × ℝ} (hR : R ∈ moreCapableAltRegionBits W) (hR₂ : 0 ≤ R.2) :
    R ∈ superpositionClosedRegionBits W := by
  obtain ⟨k, q, hq, h₂, h₁₂, h₃⟩ := hR
  have hL := log_two_pos'
  by_cases hcase : R.1 ≤ bcInfoXY₁U q W / log 2
  · exact ⟨k, q, hq, hcase, h₂, h₃⟩
  push Not at hcase
  set a := bcInfoXY₁U q W / log 2 with ha
  set b := bcInfoUY₂ q W / log 2 with hb
  set d := bcInfoXY₁ q W / log 2 with hd
  have h₁₂' : R.1 + R.2 ≤ a + b := by rwa [add_div] at h₁₂
  have hb0 : 0 < b := by linarith
  set s := R.2 / b with hs
  have hs0 : 0 ≤ s := div_nonneg hR₂ hb0.le
  have hs1 : s ≤ 1 := (div_le_one hb0).2 (by linarith)
  have hsb : s * b = R.2 := div_mul_cancel₀ _ hb0.ne'
  obtain ⟨k', q', hq', e₁, e₂, e₃⟩ := exists_moreCapable_timeShare (W := W) hq hW
    (t := 1 - s) (by linarith) (by linarith)
  rw [sub_sub_cancel] at e₁ e₂
  refine ⟨k', q', hq', ?_, ?_, ?_⟩
  · rw [e₁, add_div, mul_div_assoc, mul_div_assoc, ← hd, ← ha]
    rcases le_total b (d - a) with hc | hc
    · nlinarith
    · nlinarith
  · calc R.2 = s * b := hsb.symm
      _ = (s * bcInfoUY₂ q W) / log 2 := by rw [hb, mul_div_assoc]
      _ ≤ _ := div_le_div_of_nonneg_right e₂ hL.le
  · exact h₃.trans (div_le_div_of_nonneg_right e₃ hL.le)

end Regions

/-! ### The converses -/

section Converse

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}
  {M₁ M₂ n : ℕ}

/-- **Lecture 5 of [elgamal2010], page 5-44.** For a more capable channel,
`log |𝓜₁| + log |𝓜₂| ≤ ∑ᵢ I(Xᵢ; Y₁ᵢ) + 2 log 2 + P₁ log |𝓜₁| + P₂ log |𝓜₂|`. The proof
uses `Vᵢ = (M₁, Y₁^{i-1}, Y₂_{i+1}ⁿ)` and `I(Xᵢ; Y₂ᵢ | Vᵢ) ≤ I(Xᵢ; Y₁ᵢ | Vᵢ)`. -/
theorem BCCode.log_add_log_le_sum_bcInfoXY₁ (c : BCCode M₁ M₂ n α β₁ β₂) (hW : IsChannel W)
    (h : IsMoreCapable W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log M₁ + log M₂ ≤ ∑ i, bcInfoXY₁ (c.moreCapableLetterLaw W (fun w => w.2) i) W + 2 * log 2 +
      c.errProb₁ W * log M₁ + c.errProb₂ W * log M₂ := by
  have hb := c.log_add_log_le_sum_bcInfoUY₁_add_bcInfoXY₂U (W := W) hW h₁ h₂
  have hle : ∑ i, (bcInfoUY₁ (c.moreCapableLetterLaw W (fun w => w.1) i) W +
      bcInfoXY₂U (c.moreCapableLetterLaw W (fun w => w.1) i) W) ≤
      ∑ i, bcInfoXY₁ (c.moreCapableLetterLaw W (fun w => w.2) i) W := by
    refine sum_le_sum fun i _ => ?_
    have hq := c.moreCapableLetterLaw_isPMF (fun w => w.1) hW h₁ h₂ i
    have e := bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U hq hW
    have e' := c.moreCapable_bcInfoXY₁ (fun w => w.1) hW h₁ h₂ i
    have e'' := c.moreCapable_bcInfoXY₁ (fun w => w.2) hW h₁ h₂ i
    have hm := h.bcInfoXY₂U_le_bcInfoXY₁U hq hW
    linarith
  linarith

/-- The arithmetic of the converse: a bound on `A log 2` is a bound on `r` in bits. -/
private lemma moreCapable_rate_le {r A S P B : ℝ} {n : ℕ} (hn : 0 < n) (hr : (n : ℝ) * r ≤ A)
    (h : A * log 2 ≤ S + 2 * log 2 + P * B * log 2) :
    r - (2 + P * B) / n ≤ S / n / log 2 := by
  have hL := log_two_pos'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) * r * log 2 ≤ S + (2 + P * B) * log 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hr hL.le]
  rw [sub_le_iff_le_add, div_div, div_add_div _ _ (mul_pos hn' hL).ne' hn'.ne', le_div_iff₀
    (mul_pos (mul_pos hn' hL) hn')]
  calc r * (↑n * log 2 * ↑n) = (n : ℝ) * r * log 2 * n := by ring
    _ ≤ (S + (2 + P * B) * log 2) * n := mul_le_mul_of_nonneg_right h1 hn'.le
    _ = _ := by ring

private lemma moreCapable_sum_uniform {n : ℕ} (I : Fin n → ℝ) :
    ∑ i, uniformPMF (Fin n) i * I i = (∑ i, I i) / n := by
  simp only [uniformPMF, Fintype.card_fin]
  rw [← mul_sum, one_div_mul_eq_div]

/-- `n R ≤ ⌈n R⌉₊` also for the positive part of `R`. -/
private lemma moreCapable_mul_max_le (n : ℕ) (R : ℝ) :
    (n : ℝ) * max R 0 ≤ (⌈(n : ℝ) * R⌉₊ : ℝ) := by
  rcases le_total R 0 with h | h
  · rw [max_eq_right h, mul_zero]
    exact Nat.cast_nonneg _
  · rw [max_eq_left h]
    exact Nat.le_ceil _

/-- The converse with the auxiliary random variable `Uᵢ = (M₂, Y₁^{i-1}, Y₂_{i+1}ⁿ)`, for a sequence
of codes for which the bound on the sum rate with `I(X; Y₁)` holds. There is `εₙ → 0` with
`(R₁ - εₙ, R₂ - εₙ)` in the region `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ I(X; Y₁)`. -/
theorem exists_eps_mem_superpositionClosedRegionBits (hW : IsChannel W) {R₁ R₂ : ℝ}
    (c : ∀ n : ℕ, BCCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α β₁ β₂) {P : ℕ → ℝ}
    (hc : Tendsto P atTop (𝓝 0)) (hP₁ : ∀ n, (c n).errProb₁ W ≤ P n)
    (hP₂ : ∀ n, (c n).errProb₂ W ≤ P n) (hP0 : ∀ n, 0 ≤ P n)
    (hb₃ : ∀ n : ℕ, log ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) + log ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ) ≤
      ∑ i, bcInfoXY₁ ((c n).moreCapableLetterLaw W (fun w => w.2) i) W + 2 * log 2 +
        P n * (log ((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) + log ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ))) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ n, 0 ≤ ε n) ∧
      ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ superpositionClosedRegionBits W := by
  set a₁ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₁⌉₊ with ha₁
  set a₂ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₂⌉₊ with ha₂
  set ε : ℕ → ℝ := fun n => (2 + P n * ((a₁ n : ℝ) + a₂ n)) / n with hεdef
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg zero_le_two
    (mul_nonneg (hP0 n) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Nat.cast_nonneg n)
  have hL := log_two_pos'
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ superpositionClosedRegionBits W := by
    intro n hn
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hM₁ : 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := by positivity
    have hM₂ : 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := by positivity
    set q := fun i => (c n).moreCapableLetterLaw W (fun w => w.2) i with hqdef
    have hq : ∀ i, IsPMF (q i) := fun i =>
      (c n).moreCapableLetterLaw_isPMF _ hW hM₁ hM₂ i
    have hw : IsPMF (uniformPMF (Fin n)) := uniformPMF_isPMF
    have hbar := degradedBCTimeShare_isPMF hw hq
    have hlog₁ : log ((2 ^ a₁ n : ℕ) : ℝ) = a₁ n * log 2 := by push_cast; rw [log_pow]
    have hlog₂ : log ((2 ^ a₂ n : ℕ) : ℝ) = a₂ n * log 2 := by push_cast; rw [log_pow]
    have b₂ := (c n).log_le_sum_bcInfoUY₂_moreCapable hW hM₁ hM₂
    have b₁₂ := (c n).log_add_log_le_sum_bcInfoXY₁U_add_bcInfoUY₂ hW hM₁ hM₂
    have b₃ := hb₃ n
    rw [show ((2 ^ ⌈(n : ℝ) * R₂⌉₊ : ℕ) : ℝ) = ((2 ^ a₂ n : ℕ) : ℝ) from rfl, hlog₂] at b₂
    rw [show ((2 ^ ⌈(n : ℝ) * R₁⌉₊ : ℕ) : ℝ) = ((2 ^ a₁ n : ℕ) : ℝ) from rfl,
      show ((2 ^ ⌈(n : ℝ) * R₂⌉₊ : ℕ) : ℝ) = ((2 ^ a₂ n : ℕ) : ℝ) from rfl, hlog₁, hlog₂] at b₁₂ b₃
    have ha₁0 : (0 : ℝ) ≤ a₁ n := Nat.cast_nonneg _
    have ha₂0 : (0 : ℝ) ≤ a₂ n := Nat.cast_nonneg _
    have hPa₁ : (c n).errProb₁ W * (a₁ n * log 2) ≤ P n * a₁ n * log 2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hP₁ n) (mul_nonneg ha₁0 hL.le)
    have hPa₂ : (c n).errProb₂ W * (a₂ n * log 2) ≤ P n * a₂ n * log 2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hP₂ n) (mul_nonneg ha₂0 hL.le)
    have hPa₁0 : 0 ≤ P n * a₁ n * log 2 := mul_nonneg (mul_nonneg (hP0 n) ha₁0) hL.le
    have hPa₂0 : 0 ≤ P n * a₂ n * log 2 := mul_nonneg (mul_nonneg (hP0 n) ha₂0) hL.le
    have hdist : P n * ((a₁ n : ℝ) + a₂ n) * log 2 = P n * a₁ n * log 2 + P n * a₂ n * log 2 := by
      ring
    have hdist₃ : P n * ((a₁ n : ℝ) * log 2 + a₂ n * log 2) =
        P n * a₁ n * log 2 + P n * a₂ n * log 2 := by
      ring
    set Rp₁ := max R₁ 0 with hRp₁
    set Rp₂ := max R₂ 0 with hRp₂
    have hRp₂0 : 0 ≤ Rp₂ := le_max_right _ _
    have hr₂ := moreCapable_mul_max_le n R₂
    have hr₁ := moreCapable_mul_max_le n R₁
    have r₂ : Rp₂ - ε n ≤ (∑ i, bcInfoUY₂ (q i) W) / n / log 2 :=
      moreCapable_rate_le (A := a₂ n) hn hr₂ (by linarith [hL])
    have r₁₂ : Rp₁ + Rp₂ - ε n ≤ (∑ i, (bcInfoXY₁U (q i) W + bcInfoUY₂ (q i) W)) / n / log 2 :=
      moreCapable_rate_le (A := (a₁ n : ℝ) + a₂ n) hn (by rw [mul_add]; exact add_le_add hr₁ hr₂)
        (by linarith)
    have r₃ : Rp₁ + Rp₂ - ε n ≤ (∑ i, bcInfoXY₁ (q i) W) / n / log 2 :=
      moreCapable_rate_le (A := (a₁ n : ℝ) + a₂ n) hn (by rw [mul_add]; exact add_le_add hr₁ hr₂)
        (by linarith)
    set qbar := degradedBCRelabelLaw (Fintype.equivFin _)
      (degradedBCTimeShare (uniformPMF (Fin n)) q) with hqbar
    have hqbar' : IsPMF qbar := degradedBCRelabelLaw_isPMF _ hbar
    have hXU : bcInfoXY₁U qbar W = (∑ i, bcInfoXY₁U (q i) W) / n := by
      rw [hqbar, degradedBC_bcInfoXY₁U_relabel _ hbar hW,
        bcInfoXY₁U_degradedBCTimeShare hw hq hW, moreCapable_sum_uniform]
    have hUY : (∑ i, bcInfoUY₂ (q i) W) / n ≤ bcInfoUY₂ qbar W := by
      rw [hqbar, degradedBC_bcInfoUY₂_relabel _ hbar hW]
      have h1 := sum_mul_bcInfoUY₂_le_degradedBCTimeShare (W := W) hw hq hW
      rwa [moreCapable_sum_uniform] at h1
    have hX : (∑ i, bcInfoXY₁ (q i) W) / n ≤ bcInfoXY₁ qbar W := by
      rw [hqbar, moreCapable_bcInfoXY₁_relabel]
      have h1 := sum_mul_bcInfoXY₁_le_degradedBCTimeShare (W := W) hw hq hW
      rwa [moreCapable_sum_uniform] at h1
    have hUY0 : 0 ≤ bcInfoUY₂ qbar W / log 2 :=
      div_nonneg (mutualInfo_nonneg (bcJoint_isPMF hqbar' hW) _ _) hL.le
    have hUYd := div_le_div_of_nonneg_right hUY hL.le
    have hXd := div_le_div_of_nonneg_right hX hL.le
    have hsplit : (∑ i, (bcInfoXY₁U (q i) W + bcInfoUY₂ (q i) W)) / n / log 2 =
        (∑ i, bcInfoXY₁U (q i) W) / n / log 2 + (∑ i, bcInfoUY₂ (q i) W) / n / log 2 := by
      rw [sum_add_distrib]
      ring
    have hkey : ∀ S, Rp₁ + Rp₂ - ε n ≤ S → Rp₁ - ε n + max (Rp₂ - ε n) 0 ≤ S := fun S hS => by
      rcases le_total (Rp₂ - ε n) 0 with hc | hc
      · rw [max_eq_right hc]
        linarith
      · rw [max_eq_left hc]
        linarith [hε0 n]
    have hmem' : (Rp₁ - ε n, max (Rp₂ - ε n) 0) ∈ moreCapableAltRegionBits W := by
      refine ⟨_, qbar, hqbar', max_le (by simpa using r₂.trans hUYd) hUY0, hkey _ ?_,
        hkey _ (r₃.trans hXd)⟩
      rw [add_div, hXU]
      linarith
    obtain ⟨k', q', hq', e₁, e₂, e₃⟩ :=
      mem_superpositionClosedRegionBits_of_mem_moreCapableAltRegionBits hW hmem'
        (le_max_right _ _)
    simp only at e₁ e₂ e₃
    have hR₁ : R₁ ≤ Rp₁ := le_max_left _ _
    have hR₂ : R₂ ≤ Rp₂ := le_max_left _ _
    have hmax : Rp₂ - ε n ≤ max (Rp₂ - ε n) 0 := le_max_left _ _
    have hmax0 : 0 ≤ max (Rp₂ - ε n) 0 := le_max_right _ _
    exact ⟨k', q', hq', by simp only; linarith, by simp only; linarith,
      by simp only; linarith [hε0 n]⟩
  have hε : Tendsto ε atTop (𝓝 0) := by
    set K := |R₁| + |R₂| + 2
    have hP0' : Tendsto P atTop (𝓝 0) := hc
    have hup : Tendsto (fun n : ℕ => 2 / (n : ℝ) + P n * K) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add (hP0'.mul_const K)
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
  exact ⟨ε, hε, hε0, hmem⟩

/-- **The converse for the more capable DM-BC ([elgamal2010], Lecture 5, pages 5-41 to 5-44).**
Every achievable rate pair of a more capable DM-BC is in the closure of the region
`R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ I(X; Y₁)`. The auxiliary random variable is
`U = (Q, U_Q)`, with `Q` uniform on the `n` positions and `Uᵢ = (M₂, Y₁^{i-1}, Y₂_{i+1}ⁿ)`. This
gives a point of the alternative region, which is moved to the region by
`mem_superpositionClosedRegionBits_of_mem_moreCapableAltRegionBits`. -/
theorem IsAchievableBCBits.mem_closure_superpositionClosedRegionBits (hW : IsChannel W)
    (h : IsMoreCapable W) {R₁ R₂ : ℝ} (ha : IsAchievableBCBits W R₁ R₂) :
    (R₁, R₂) ∈ closure (superpositionClosedRegionBits W) := by
  obtain ⟨c, hc⟩ := ha
  have hP₁ : ∀ n, (c n).errProb₁ W ≤ (c n).errProb W := fun n =>
    (le_max_left _ _).trans ((c n).max_errProb_le hW)
  have hP₂ : ∀ n, (c n).errProb₂ W ≤ (c n).errProb W := fun n =>
    (le_max_right _ _).trans ((c n).max_errProb_le hW)
  have hP0 : ∀ n, 0 ≤ (c n).errProb W := fun n => ((c n).errProb₁_nonneg hW).trans (hP₁ n)
  obtain ⟨ε, hε, -, hmem⟩ := exists_eps_mem_superpositionClosedRegionBits hW c hc hP₁ hP₂ hP0
    fun n => by
      have hM₁ : 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := by positivity
      have hM₂ : 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := by positivity
      have b₃ := (c n).log_add_log_le_sum_bcInfoXY₁ hW h hM₁ hM₂
      have hA : 0 ≤ log (((2 : ℕ) ^ ⌈(n : ℝ) * R₁⌉₊ : ℕ) : ℝ) := log_natCast_nonneg _
      have hB : 0 ≤ log (((2 : ℕ) ^ ⌈(n : ℝ) * R₂⌉₊ : ℕ) : ℝ) := log_natCast_nonneg _
      have h1 := mul_le_mul_of_nonneg_right (hP₁ n) hA
      have h2 := mul_le_mul_of_nonneg_right (hP₂ n) hB
      linarith
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

/-- **The capacity region of the more capable DM-BC ([elgamal2010], Lecture 5, page 5-39).** It
is the closure of the set of rate pairs with `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)`,
`R₁ + R₂ ≤ I(X; Y₁)` for some `p(u, x)`. -/
theorem bcCapacityRegionBits_eq_closure_superpositionClosedRegionBits (hW : IsChannel W)
    (h : IsMoreCapable W) :
    bcCapacityRegionBits W = closure (superpositionClosedRegionBits W) := by
  refine Set.Subset.antisymm (closure_minimal (fun R hR => ?_) isClosed_closure) ?_
  · exact IsAchievableBCBits.mem_closure_superpositionClosedRegionBits hW h hR
  · exact closure_minimal (superpositionClosedRegionBits_subset hW) isClosed_closure

/-- **Lecture 5 of [elgamal2010], page 5-45.** For a less noisy DM-BC, the points of the alternative
region with `R₂ ≥ 0` lie in the region `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)`: the bound
`R₁ + R₂ ≤ I(X; Y₁)` is implied, as `I(X; Y₁) ≥ I(X; Y₁ | U) + I(U; Y₂)` for a less noisy
channel. -/
theorem IsLessNoisy.mem_degradedBCRegionBits_of_mem_lessNoisyAltRegionBits (hW : IsChannel W)
    (h : IsLessNoisy W) {R : ℝ × ℝ} (hR : R ∈ lessNoisyAltRegionBits W) (hR₂ : 0 ≤ R.2) :
    R ∈ degradedBCRegionBits W := by
  obtain ⟨k, q, hq, h₂, h₁₂⟩ := hR
  have hsum : bcInfoXY₁U q W + bcInfoUY₂ q W ≤ bcInfoXY₁ q W := by
    rw [bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U hq hW]
    linarith [h k q hq]
  obtain ⟨k', q', hq', e₁, e₂, -⟩ :=
    mem_superpositionClosedRegionBits_of_mem_moreCapableAltRegionBits hW
      (R := R) ⟨k, q, hq, h₂, h₁₂, h₁₂.trans (div_le_div_of_nonneg_right hsum log_two_pos'.le)⟩ hR₂
  exact ⟨k', q', hq', e₁, e₂⟩

/-- **The converse for the less noisy DM-BC ([elgamal2010], Lecture 5, page 5-45).** Every
achievable rate pair of a less noisy DM-BC is in the closure of the region `R₁ ≤ I(X; Y₁ | U)`,
`R₂ ≤ I(U; Y₂)`. A less noisy channel is more capable, and the third bound is dropped. -/
theorem IsAchievableBCBits.mem_closure_degradedBCRegionBits_of_isLessNoisy (hW : IsChannel W)
    (h : IsLessNoisy W) {R₁ R₂ : ℝ} (ha : IsAchievableBCBits W R₁ R₂) :
    (R₁, R₂) ∈ closure (degradedBCRegionBits W) := by
  refine closure_mono ?_ (ha.mem_closure_superpositionClosedRegionBits hW (h.isMoreCapable hW))
  rintro R ⟨k, q, hq, h₁, h₂, -⟩
  exact ⟨k, q, hq, h₁, h₂⟩

/-- **The capacity region of the less noisy DM-BC ([elgamal2010], Lecture 5, page 5-38).** It is
the closure of the set of rate pairs with `R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` for some
`p(u, x)`. -/
theorem IsLessNoisy.bcCapacityRegionBits_eq_closure_degradedBCRegionBits (hW : IsChannel W)
    (h : IsLessNoisy W) : bcCapacityRegionBits W = closure (degradedBCRegionBits W) := by
  refine Set.Subset.antisymm (closure_minimal (fun R hR => ?_) isClosed_closure) ?_
  · exact IsAchievableBCBits.mem_closure_degradedBCRegionBits_of_isLessNoisy hW h hR
  · exact closure_minimal (IsLessNoisy.degradedBCRegionBits_subset hW h) isClosed_closure

end Converse

end InfoTheory
