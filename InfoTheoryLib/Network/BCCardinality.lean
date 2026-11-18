/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCCapacity
public import InfoTheoryLib.Network.BCMoreCapable
public import InfoTheoryLib.Network.CardinalityBound
public import InfoTheoryLib.Secrecy.Wiretap

/-!
# The cardinality bound of the degraded broadcast channel

For every `(U, X)` there is `(U', X')` with `|𝒰'| ≤ min {|𝒳|, |𝒴₁|, |𝒴₂|} + 1` and the same values
of `I(X; Y₁ | U)` and `I(U; Y₂)`, as in Appendix C of El Gamal and Kim. So the capacity region of a
degraded DM-BC is the region with a bounded `U`, which is closed: Theorem 2 of Lecture 5 of the
notes holds without a closure.

## Main definitions

* `degradedBCRegionCardBits W K`: the region of Theorem 2 with `U` on `Fin K`.
* `superpositionClosedRegionCardBits W K`: the region with `R₁ + R₂ ≤ I(X; Y₁)`, with `U` on
  `Fin K`.

## Main statements

* `bcInfoXY₁U_kernel`: `I(X; Y₁ | U) = ∑_u p(u) I(X; Y₁ | U = u)`.
* `exists_degradedBC_card`: the bound, for an output `T` that determines the output `Y₂`.
* `exists_degradedBC_card_input`, `exists_degradedBC_card_Y₂`, `exists_degradedBC_card_Y₁`: the
  three bounds `|𝒳| + 1`, `|𝒴₂| + 1` and `|𝒴₁| + 1`.
* `exists_degradedBC_card_min`: the bound with the minimum.
* `degradedBCRegionBits_eq_card`, `isClosed_degradedBCRegionCardBits`,
  `bcCapacityRegionBits_eq_card`: the capacity region without a closure.
* `IsLessNoisy.bcCapacityRegionBits_eq_card`: the same for a less noisy channel, with
  `|𝒰| ≤ min {|𝒳|, |𝒴₂|} + 1`.
* `IsMoreCapable.bcCapacityRegionBits_eq_card`: the same for a more capable channel, with
  `|𝒰| ≤ |𝒳| + 1`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ 𝒰 : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] [Fintype 𝒰]
  {W : α → β₁ × β₂ → ℝ}

omit [Fintype β₂] in
/-- The law `p(u) p(x | u)` of a mixture is a pmf. -/
lemma kernelLaw_isPMF {w : 𝒰 → ℝ} (hw : IsPMF w) {r : 𝒰 → α → ℝ} (hr : IsChannel r) :
    IsPMF fun z : 𝒰 × α => w z.1 * r z.1 z.2 := by
  refine ⟨fun z => mul_nonneg (hw.nonneg _) ((hr _).nonneg _), ?_⟩
  simp only [Fintype.sum_prod_type, ← mul_sum, (hr _).sum_eq_one, mul_one, hw.sum_eq_one]

omit [Fintype β₁] [Fintype β₂] in
/-- The mean of the conditional pmfs is a pmf. -/
lemma mean_isPMF {w : 𝒰 → ℝ} (hw : IsPMF w) {r : 𝒰 → α → ℝ} (hr : IsChannel r) :
    IsPMF (∑ u, w u • r u) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [Finset.sum_apply]
    exact sum_nonneg fun u _ => mul_nonneg (hw.nonneg u) ((hr u).nonneg x)
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_comm]
    simp only [← mul_sum, (hr _).sum_eq_one, mul_one, hw.sum_eq_one]

/-- `I(X; Y₁ | U) = ∑_u p(u) I(X; Y₁ | U = u)`, where given `U = u` the input has law `r u`. -/
theorem bcInfoXY₁U_kernel {w : 𝒰 → ℝ} (hw : IsPMF w) {r : 𝒰 → α → ℝ} (hr : IsChannel r)
    (hW : IsChannel W) :
    bcInfoXY₁U (fun z : 𝒰 × α => w z.1 * r z.1 z.2) W =
      ∑ u, w u * mutualInfoOf (r u) (bcMarg₁ W) := by
  have hM := hW.bcMarg₁
  have h := bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U (kernelLaw_isPMF hw hr) hW
  have e1 : (fun x => ∑ u, (fun z : 𝒰 × α => w z.1 * r z.1 z.2) (u, x)) = ∑ u, w u • r u := by
    funext x
    simp [Finset.sum_apply]
  rw [bcInfoXY₁_eq, e1, bcInfoUY₁_kernel, mutualInfoOf_eq (mean_isPMF hw hr) hM,
    mutualInfoOf_eq hw (hr.throughKernel hM), outDist_throughKernel] at h
  have e2 : ∑ x, (∑ u, w u • r u) x * entropy (bcMarg₁ W x) =
      ∑ u, w u * ∑ x, r u x * entropy (bcMarg₁ W x) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun u _ => sum_congr rfl fun x _ => by ring
  have e3 : ∑ u, w u * mutualInfoOf (r u) (bcMarg₁ W) =
      ∑ u, w u * entropy (outDist (r u) (bcMarg₁ W)) -
        ∑ u, w u * ∑ x, r u x * entropy (bcMarg₁ W x) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun u _ => ?_
    rw [mutualInfoOf_eq (hr u) hM, mul_sub]
  simp only [throughKernel] at h
  rw [e3]
  linarith

/-- `I(U; Y₂) = H(Y₂) - ∑_u p(u) H(Y₂ | U = u)`. -/
theorem bcInfoUY₂_kernel_eq {w : 𝒰 → ℝ} (hw : IsPMF w) {r : 𝒰 → α → ℝ} (hr : IsChannel r)
    (hW : IsChannel W) :
    bcInfoUY₂ (fun z : 𝒰 × α => w z.1 * r z.1 z.2) W =
      entropy (outDist (∑ u, w u • r u) (bcMarg₂ W)) -
        ∑ u, w u * entropy (outDist (r u) (bcMarg₂ W)) := by
  rw [bcInfoUY₂_kernel, mutualInfoOf_eq hw (hr.throughKernel hW.bcMarg₂), outDist_throughKernel]
  rfl

/-- **The cardinality bound of Appendix C of [elgamal2010].** If the output `T` determines the
output `Y₂`, through `p(y₂ | x) = ∑ₐ T(a | x) V(y₂ | a)`, then for every `(U, X)` there is
`(U', X')` with `|𝒰'| = |A| + 1` and the same `I(X; Y₁ | U)`, `I(U; Y₂)` and law of the output
`T`. -/
theorem exists_degradedBC_card {A : Type*} [Fintype A] {T : α → A → ℝ} (hT : IsChannel T)
    {V : A → β₂ → ℝ} (hV : ∀ x y, bcMarg₂ W x y = ∑ a, T x a * V a y) {q : 𝒰 × α → ℝ} (hq : IsPMF q)
    (hW : IsChannel W) :
    ∃ q' : Fin (Fintype.card A + 1) × α → ℝ, IsPMF q' ∧ bcInfoXY₁U q' W = bcInfoXY₁U q W ∧
      bcInfoUY₂ q' W = bcInfoUY₂ q W ∧
        outDist (fun x => ∑ u, q' (u, x)) T = outDist (fun x => ∑ u, q (u, x)) T := by
  classical
  obtain ⟨z₀⟩ : Nonempty (𝒰 × α) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  have hα : Nonempty α := ⟨z₀.2⟩
  have hApos : 0 < Fintype.card A := card_pos_of_isPMF (hT z₀.2)
  set w : 𝒰 → ℝ := fun u => ∑ x, q (u, x) with hw
  set r := wtPosterior q with hrd
  have hwP : IsPMF w := wiretapMarg_isPMF hq
  have hr : IsChannel r := wtPosterior_isChannel hq
  have hqe : q = fun z : 𝒰 × α => w z.1 * r z.1 z.2 := funext fun z =>
    (marg_mul_wtPosterior hq z).symm
  set f : Bool → (α → ℝ) → ℝ := fun b t =>
    if b then mutualInfoOf t (bcMarg₁ W) else entropy (outDist t (bcMarg₂ W)) with hf
  have hfc : ∀ b, ContinuousOn (f b) {p | IsPMF p} := by
    rintro (_ | _)
    · simpa [hf] using (continuous_entropy_outDist (bcMarg₂ W)).continuousOn
    · simpa [hf] using continuousOn_mutualInfoOf hW.bcMarg₁
  obtain ⟨w', r', hw', hr', hmean, hmix⟩ := exists_mixture_preserving (κ := Bool) hT hfc hwP hr
    (n := Fintype.card A + 1) (by rw [Fintype.card_bool]; omega)
  have hm := hmix true
  have hh := hmix false
  simp only [hf, ite_true, Bool.false_eq_true, ite_false] at hm hh
  have hout : outDist (∑ i, w' i • r' i) (bcMarg₂ W) = outDist (∑ u, w u • r u) (bcMarg₂ W) := by
    have hc : bcMarg₂ W = fun x y => ∑ a, T x a * V a y := funext fun x => funext fun y => hV x y
    rw [hc, ← outDist_outDist, ← outDist_outDist, outDist_mean w' r' T, outDist_mean w r T, hmean]
  refine ⟨fun z => w' z.1 * r' z.1 z.2, kernelLaw_isPMF hw' hr', ?_, ?_, ?_⟩
  · rw [hqe, bcInfoXY₁U_kernel hw' hr' hW, bcInfoXY₁U_kernel hwP hr hW, hm]
  · rw [hqe, bcInfoUY₂_kernel_eq hw' hr' hW, bcInfoUY₂_kernel_eq hwP hr hW, hout, hh]
  · have e₁ : (fun x => ∑ u, (fun z : Fin (Fintype.card A + 1) × α => w' z.1 * r' z.1 z.2) (u, x)) =
        ∑ u, w' u • r' u := by
      funext x
      simp [Finset.sum_apply]
    have e₂ : (fun x => ∑ u, q (u, x)) = ∑ u, w u • r u := by
      funext x
      rw [hqe]
      simp [Finset.sum_apply]
    rw [e₁, e₂, outDist_mean, outDist_mean, hmean]

/-- **The bound `|𝒰| ≤ |𝒳| + 1` of Appendix C of [elgamal2010]**, which fixes `p(x)`, and so also
`I(X; Y₁)`. -/
theorem exists_degradedBC_card_input {q : 𝒰 × α → ℝ} (hq : IsPMF q) (hW : IsChannel W) :
    ∃ q' : Fin (Fintype.card α + 1) × α → ℝ, IsPMF q' ∧ bcInfoXY₁U q' W = bcInfoXY₁U q W ∧
      bcInfoUY₂ q' W = bcInfoUY₂ q W ∧ bcInfoXY₁ q' W = bcInfoXY₁ q W := by
  classical
  obtain ⟨q', hq', e₁, e₂, e₃⟩ := exists_degradedBC_card
    (T := fun x a => if x = a then 1 else 0) (V := bcMarg₂ W)
    (fun x => ⟨fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩) (fun x y => by simp) hq hW
  have hO : ∀ t : α → ℝ, outDist t (fun x a => if x = a then 1 else 0) = t := fun t => by
    funext y
    simp [outDist]
  rw [hO, hO] at e₃
  refine ⟨q', hq', e₁, e₂, ?_⟩
  rw [bcInfoXY₁_eq, bcInfoXY₁_eq, e₃]

/-- **The bound `|𝒰| ≤ |𝒴₂| + 1` of Appendix C of [elgamal2010]**, which fixes `p(y₂)`. -/
theorem exists_degradedBC_card_Y₂ {q : 𝒰 × α → ℝ} (hq : IsPMF q) (hW : IsChannel W) :
    ∃ q' : Fin (Fintype.card β₂ + 1) × α → ℝ, IsPMF q' ∧ bcInfoXY₁U q' W = bcInfoXY₁U q W ∧
      bcInfoUY₂ q' W = bcInfoUY₂ q W := by
  classical
  obtain ⟨q', hq', e₁, e₂, -⟩ := exists_degradedBC_card (T := bcMarg₂ W)
    (V := fun a y => if a = y then 1 else 0) hW.bcMarg₂ (fun x y => by simp) hq hW
  exact ⟨q', hq', e₁, e₂⟩

/-- **The bound `|𝒰| ≤ |𝒴₁| + 1` of Appendix C of [elgamal2010]**, which fixes `p(y₁)`, and so
`p(y₂)` by degradedness. -/
theorem exists_degradedBC_card_Y₁ (hd : IsStochasticallyDegraded W) {q : 𝒰 × α → ℝ} (hq : IsPMF q)
    (hW : IsChannel W) :
    ∃ q' : Fin (Fintype.card β₁ + 1) × α → ℝ, IsPMF q' ∧ bcInfoXY₁U q' W = bcInfoXY₁U q W ∧
      bcInfoUY₂ q' W = bcInfoUY₂ q W := by
  obtain ⟨V, -, hV⟩ := hd
  obtain ⟨q', hq', e₁, e₂, -⟩ := exists_degradedBC_card hW.bcMarg₁ hV hq hW
  exact ⟨q', hq', e₁, e₂⟩

/-- **The cardinality bound of Appendix C of [elgamal2010].** For a degraded DM-BC and every
`(U, X)` there is `(U', X')` with `|𝒰'| = min {|𝒳|, |𝒴₁|, |𝒴₂|} + 1`, and the same `I(X; Y₁ | U)`
and `I(U; Y₂)`. -/
theorem exists_degradedBC_card_min (hd : IsStochasticallyDegraded W) {q : 𝒰 × α → ℝ} (hq : IsPMF q)
    (hW : IsChannel W) :
    ∃ q' : Fin (min (min (Fintype.card α) (Fintype.card β₁)) (Fintype.card β₂) + 1) × α → ℝ,
      IsPMF q' ∧ bcInfoXY₁U q' W = bcInfoXY₁U q W ∧ bcInfoUY₂ q' W = bcInfoUY₂ q W := by
  rcases min_choice (min (Fintype.card α) (Fintype.card β₁)) (Fintype.card β₂) with h | h
  · rw [h]
    rcases min_choice (Fintype.card α) (Fintype.card β₁) with h' | h' <;> rw [h']
    · obtain ⟨q', hq', e₁, e₂, -⟩ := exists_degradedBC_card_input hq hW
      exact ⟨q', hq', e₁, e₂⟩
    · exact exists_degradedBC_card_Y₁ hd hq hW
  · rw [h]
    exact exists_degradedBC_card_Y₂ hq hW

/-- **Theorem 2 of Lecture 5 of [elgamal2010] with the cardinality bound of Appendix C.** The region
`R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` in bits, for some `p(u, x)` with `U` on `Fin K`. -/
def degradedBCRegionCardBits (W : α → β₁ × β₂ → ℝ) (K : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ q : Fin K × α → ℝ, IsPMF q ∧ R.1 ≤ bcInfoXY₁U q W / log 2 ∧ R.2 ≤ bcInfoUY₂ q W / log 2}

/-- The auxiliary alphabet of the degraded DM-BC can be bounded. -/
theorem degradedBCRegionBits_eq_card (hW : IsChannel W) (hd : IsStochasticallyDegraded W) :
    degradedBCRegionBits W = degradedBCRegionCardBits W
      (min (min (Fintype.card α) (Fintype.card β₁)) (Fintype.card β₂) + 1) := by
  refine Set.Subset.antisymm ?_ fun R ⟨q, hq, h₁, h₂⟩ => ⟨_, q, hq, h₁, h₂⟩
  rintro R ⟨k, q, hq, h₁, h₂⟩
  obtain ⟨q', hq', e₁, e₂⟩ := exists_degradedBC_card_min hd hq hW
  exact ⟨q', hq', by rwa [e₁], by rwa [e₂]⟩

/-- With a bounded auxiliary alphabet the region is closed. -/
theorem isClosed_degradedBCRegionCardBits (hW : IsChannel W) (K : ℕ) :
    IsClosed (degradedBCRegionCardBits W K) := by
  have hK : IsChannel fun z : Fin K × α => W z.2 := fun z => hW z.2
  have h := isClosed_exists_forall_le (J := Bool) (E := ℝ × ℝ) (K := {q : Fin K × α → ℝ | IsPMF q})
    isCompact_setOf_isPMF (L := fun b R => if b then R.1 else R.2)
    (F := fun b q => if b then bcInfoXY₁U q W / log 2 else bcInfoUY₂ q W / log 2)
    (by
      rintro (_ | _)
      · simpa using continuous_snd
      · simpa using continuous_fst) (by
      rintro (_ | _)
      · simp only [Bool.false_eq_true, ite_false]
        exact (continuousOn_mutualInfo_jointOf hK (fun z => z.1.1) fun z => z.2.2).div_const _
      · simp only [ite_true]
        exact (continuousOn_condMutualInfo_jointOf hK (fun z => z.1.2) (fun z => z.2.1)
          fun z => z.1.1).div_const _)
  convert h using 1
  ext R
  simp [degradedBCRegionCardBits, Bool.forall_bool, and_comm]

/-- **Theorem 2 of Lecture 5 of [elgamal2010], with the cardinality bound of Appendix C.** The
capacity region of a degraded DM-BC is the region with `|𝒰| ≤ min {|𝒳|, |𝒴₁|, |𝒴₂|} + 1`, with no
closure. -/
theorem bcCapacityRegionBits_eq_card (hW : IsChannel W) (hd : IsStochasticallyDegraded W) :
    bcCapacityRegionBits W = degradedBCRegionCardBits W
      (min (min (Fintype.card α) (Fintype.card β₁)) (Fintype.card β₂) + 1) := by
  rw [bcCapacityRegionBits_eq_closure_degradedBCRegionBits hW hd,
    degradedBCRegionBits_eq_card hW hd, (isClosed_degradedBCRegionCardBits hW _).closure_eq]

/-- **Less noisy channels.** The bound `|𝒰| ≤ min {|𝒳|, |𝒴₂|} + 1` does not use degradedness. -/
theorem degradedBCRegionBits_eq_card_of_input_Y₂ (hW : IsChannel W) :
    degradedBCRegionBits W =
      degradedBCRegionCardBits W (min (Fintype.card α) (Fintype.card β₂) + 1) := by
  refine Set.Subset.antisymm ?_ fun R ⟨q, hq, h₁, h₂⟩ => ⟨_, q, hq, h₁, h₂⟩
  rintro R ⟨k, q, hq, h₁, h₂⟩
  rcases min_choice (Fintype.card α) (Fintype.card β₂) with h | h <;> rw [h]
  · obtain ⟨q', hq', e₁, e₂, -⟩ := exists_degradedBC_card_input hq hW
    exact ⟨q', hq', by rwa [e₁], by rwa [e₂]⟩
  · obtain ⟨q', hq', e₁, e₂⟩ := exists_degradedBC_card_Y₂ hq hW
    exact ⟨q', hq', by rwa [e₁], by rwa [e₂]⟩

/-- **The capacity region of a less noisy DM-BC (Lecture 5 of [elgamal2010]) with the cardinality
bound of Appendix C**, with no closure. -/
theorem IsLessNoisy.bcCapacityRegionBits_eq_card (hW : IsChannel W) (h : IsLessNoisy W) :
    bcCapacityRegionBits W =
      degradedBCRegionCardBits W (min (Fintype.card α) (Fintype.card β₂) + 1) := by
  rw [IsLessNoisy.bcCapacityRegionBits_eq_closure_degradedBCRegionBits hW h,
    degradedBCRegionBits_eq_card_of_input_Y₂ hW,
    (isClosed_degradedBCRegionCardBits hW _).closure_eq]

/-- **Lecture 5 of [elgamal2010] with the cardinality bound of Appendix C.** The region
`R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)`, `R₁ + R₂ ≤ I(X; Y₁)` in bits, for some `p(u, x)` with `U` on
`Fin K`. -/
def superpositionClosedRegionCardBits (W : α → β₁ × β₂ → ℝ) (K : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ q : Fin K × α → ℝ, IsPMF q ∧ R.1 ≤ bcInfoXY₁U q W / log 2 ∧
    R.2 ≤ bcInfoUY₂ q W / log 2 ∧ R.1 + R.2 ≤ bcInfoXY₁ q W / log 2}

/-- The auxiliary alphabet of the region can be bounded: `|𝒰| ≤ |𝒳| + 1`. -/
theorem superpositionClosedRegionBits_eq_card (hW : IsChannel W) :
    superpositionClosedRegionBits W =
      superpositionClosedRegionCardBits W (Fintype.card α + 1) := by
  refine Set.Subset.antisymm ?_ fun R ⟨q, hq, h₁, h₂, h₃⟩ => ⟨_, q, hq, h₁, h₂, h₃⟩
  rintro R ⟨k, q, hq, h₁, h₂, h₃⟩
  obtain ⟨q', hq', e₁, e₂, e₃⟩ := exists_degradedBC_card_input hq hW
  exact ⟨q', hq', by rwa [e₁], by rwa [e₂], by rwa [e₃]⟩

/-- With a bounded auxiliary alphabet the region is closed. -/
theorem isClosed_superpositionClosedRegionCardBits (hW : IsChannel W) (K : ℕ) :
    IsClosed (superpositionClosedRegionCardBits W K) := by
  have hK : IsChannel fun z : Fin K × α => W z.2 := fun z => hW z.2
  have h := isClosed_exists_forall_le (J := Fin 3) (E := ℝ × ℝ)
    (K := {q : Fin K × α → ℝ | IsPMF q}) isCompact_setOf_isPMF
    (L := ![fun R => R.1, fun R => R.2, fun R => R.1 + R.2])
    (F := ![fun q => bcInfoXY₁U q W / log 2, fun q => bcInfoUY₂ q W / log 2,
      fun q => bcInfoXY₁ q W / log 2])
    (by
      intro j
      fin_cases j
      · exact continuous_fst
      · exact continuous_snd
      · exact continuous_fst.add continuous_snd)
    (by
      intro j
      fin_cases j
      · exact (continuousOn_condMutualInfo_jointOf hK (fun z => z.1.2) (fun z => z.2.1)
          fun z => z.1.1).div_const _
      · exact (continuousOn_mutualInfo_jointOf hK (fun z => z.1.1) fun z => z.2.2).div_const _
      · exact (continuousOn_mutualInfo_jointOf hK (fun z => z.1.2) fun z => z.2.1).div_const _)
  convert h using 1
  ext R
  constructor
  · rintro ⟨q, hq, h₁, h₂, h₃⟩
    refine ⟨q, hq, fun j => ?_⟩
    fin_cases j
    exacts [h₁, h₂, h₃]
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, h 0, h 1, h 2⟩

/-- **The capacity region of a more capable DM-BC (Lecture 5 of [elgamal2010]) with the cardinality
bound of Appendix C**, with no closure. -/
theorem IsMoreCapable.bcCapacityRegionBits_eq_card (hW : IsChannel W) (h : IsMoreCapable W) :
    bcCapacityRegionBits W = superpositionClosedRegionCardBits W (Fintype.card α + 1) := by
  rw [bcCapacityRegionBits_eq_closure_superpositionClosedRegionBits hW h,
    superpositionClosedRegionBits_eq_card hW,
    (isClosed_superpositionClosedRegionCardBits hW _).closure_eq]

end InfoTheory
