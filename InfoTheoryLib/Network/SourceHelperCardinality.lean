/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.CardinalityBound
public import InfoTheoryLib.Network.SourceHelperConverse
public import InfoTheoryLib.RateDistortion.SideInfo

/-!
# The cardinality bound of lossless source coding with a helper

The optimal rate region of Theorem 2 of Lecture 11 of El Gamal and Kim has `|𝒰| ≤ |𝒴| + 1`, by the
technique of Appendix C of the notes. With a bounded alphabet the region is closed, so the theorem
needs no closure.

The law `p(x, y) p(u | y)` is the law `siLaw` of source coding with side information, with the two
sources exchanged, so that we can use the reduction of `RateDistortion.SideInfo`.

## Main definitions

* `helperRegionCardBits q K`: the region of Theorem 2 of Lecture 11 with `U` on `Fin K`.

## Main statements

* `helperInfo_eq_sideRate`, `helperCond_eq_sideRate`: the two quantities as rates of `siLaw`.
* `exists_helper_reduce`: **the bound**.
* `convex_helperRegionBits`: the region is convex.
* `helperRegionBits_eq_card`, `isClosed_helperRegionCardBits`, `helperOptimalRegionBits_eq_card`:
  **Theorem 2 of Lecture 11**, with the bound and no closure.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 11 and Appendix C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β 𝒰 : Type*} [Fintype α] [Fintype β] [Fintype 𝒰] {q : α × β → ℝ}

/-- The law `p(y, x)` with the two sources exchanged. -/
def helperSwap (q : α × β → ℝ) : β × α → ℝ := fun z => q z.swap

lemma helperSwap_isPMF (hq : IsPMF q) : IsPMF (helperSwap q) :=
  ⟨fun _ => hq.nonneg _, by
    rw [← hq.sum_eq_one]
    exact (Equiv.prodComm β α).sum_comp q⟩

/-- Exchanging the two sources in `((X, Y), U)`. -/
private def swapEquiv (α β 𝒰 : Type*) : (α × β) × 𝒰 ≃ (β × α) × 𝒰 :=
  (Equiv.prodComm α β).prodCongr (Equiv.refl 𝒰)

/-- The helper law is the side information law with the sources exchanged. -/
private lemma dist_helperLaw_swap (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) :
    dist (helperLaw q κ) (swapEquiv α β 𝒰) = siLaw (helperSwap q) κ := by
  have h := dist_comp_equiv (siLaw (helperSwap q) κ) (swapEquiv α β 𝒰)
  rw [← h]
  rfl

/-- `I(Y; U)` as a rate of `siLaw`. -/
theorem helperInfo_eq_sideRate (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) :
    helperInfo q κ = sideRate 0 (helperSwap q) κ := by
  have e := mutualInfo_comp (μ := helperLaw q κ) (swapEquiv α β 𝒰)
    (fun t : (β × α) × 𝒰 => t.1.1) Prod.snd
  rw [dist_helperLaw_swap] at e
  rw [sideRate, zero_mul, sub_zero, ← e]
  rfl

/-- `I(X; U)` as a difference of rates of `siLaw`. -/
private lemma mutualInfo_X_U (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) :
    I[fun z : (α × β) × 𝒰 => z.1.1 : Prod.snd ; helperLaw q κ] =
      sideRate 0 (helperSwap q) κ - sideRate 1 (helperSwap q) κ := by
  have e := mutualInfo_comp (μ := helperLaw q κ) (swapEquiv α β 𝒰)
    (fun t : (β × α) × 𝒰 => t.1.2) Prod.snd
  rw [dist_helperLaw_swap] at e
  simp only [sideRate, zero_mul, sub_zero, one_mul]
  rw [sub_sub_cancel, ← e]
  rfl

/-- `H(X | U) = H(X) - I(X; U)`, as rates of `siLaw`. -/
theorem helperCond_eq_sideRate (hq : IsPMF q) {κ : β → 𝒰 → ℝ} (hκ : ∀ y, IsPMF (κ y)) :
    helperCond q κ = H[Prod.fst ; q] -
      (sideRate 0 (helperSwap q) κ - sideRate 1 (helperSwap q) κ) := by
  have hμ := helperLaw_isPMF hq hκ
  have hX : H[fun z : (α × β) × 𝒰 => z.1.1 ; helperLaw q κ] = H[Prod.fst ; q] := by
    have e : (fun z : (α × β) × 𝒰 => z.1.1) = Prod.fst ∘ Prod.fst := rfl
    have e₂ : dist (jointOf q fun z : α × β => κ z.2) Prod.fst = q :=
      dist_jointOf_fst fun z => hκ z.2
    rw [entropyRV, e, dist_comp_eq, helperLaw, e₂]
    rfl
  rw [← mutualInfo_X_U, mutualInfo_eq_entropy_sub_condEntropy hμ, hX, helperCond]
  ring

/-- **The bound `|𝒰| ≤ |𝒴| + 1`, page 11-23 and Appendix C of [elgamal2010].** For every `p(u | y)`
there is a `p(u' | y)` with `|𝒰'| = |𝒴| + 1`, and the same `H(X | U)` and `I(Y; U)`. -/
theorem exists_helper_reduce (hq : IsPMF q) {κ : β → 𝒰 → ℝ} (hκ : ∀ y, IsPMF (κ y)) :
    ∃ κ' : β → Fin (Fintype.card β + 1) → ℝ, (∀ y, IsPMF (κ' y)) ∧
      helperCond q κ' = helperCond q κ ∧ helperInfo q κ' = helperInfo q κ := by
  obtain ⟨κ', hκ', e₀, e₁⟩ := exists_side_reduce₂ (helperSwap_isPMF hq) hκ rfl
  refine ⟨κ', hκ', ?_, ?_⟩
  · rw [helperCond_eq_sideRate hq hκ', helperCond_eq_sideRate hq hκ, e₀, e₁]
  · rw [helperInfo_eq_sideRate, helperInfo_eq_sideRate, e₀]

/-- **Lecture 11 of [elgamal2010].** The region of Theorem 2 is convex: a time-sharing variable is
part of the auxiliary random variable. -/
theorem convex_helperRegionBits (hq : IsPMF q) : Convex ℝ (helperRegionBits q) := by
  have hl := log_pos one_lt_two
  have hS := helperSwap_isPMF hq
  rintro ⟨x₁, x₂⟩ ⟨k, κ, hκ, h₁, h₂⟩ ⟨y₁, y₂⟩ ⟨k', κ', hκ', h₃, h₄⟩ a b ha hb hab
  simp only at h₁ h₂ h₃ h₄
  obtain ⟨hC, e₀⟩ := sideRate_sumElim hS (show IsChannel κ from hκ) (show IsChannel κ' from hκ') ha
    hb hab 0
  obtain ⟨-, e₁⟩ := sideRate_sumElim hS (show IsChannel κ from hκ) (show IsChannel κ' from hκ') ha
    hb hab 1
  have eC := helperCond_eq_sideRate hq hC
  have eI := helperInfo_eq_sideRate q (fun x => Sum.elim (fun u => a * κ x u) fun v => b * κ' x v)
  have c₁ := helperCond_eq_sideRate hq hκ
  have c₂ := helperCond_eq_sideRate hq hκ'
  have i₁ := helperInfo_eq_sideRate q κ
  have i₂ := helperInfo_eq_sideRate q κ'
  refine mem_helperRegionBits_of_kernel hq hC ?_ ?_
  · have h : a * (helperCond q κ / log 2) + b * (helperCond q κ' / log 2) ≤ a * x₁ + b * y₁ :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₃ hb)
    refine le_trans (le_of_eq ?_) (by simpa using h)
    rw [eC, e₀, e₁, c₁, c₂]
    field_simp
    linear_combination (-H[Prod.fst ; q]) * hab
  · have h : a * (helperInfo q κ / log 2) + b * (helperInfo q κ' / log 2) ≤ a * x₂ + b * y₂ :=
      add_le_add (mul_le_mul_of_nonneg_left h₂ ha) (mul_le_mul_of_nonneg_left h₄ hb)
    refine le_trans (le_of_eq ?_) (by simpa using h)
    rw [eI, e₀, i₁, i₂]
    ring

/-- **Theorem 2 of Lecture 11 of [elgamal2010], the region with the bound.** `R₁ ≥ H(X | U)`,
`R₂ ≥ I(Y; U)` for some `p(u | y)` with `U` on `Fin K`, in bits. -/
def helperRegionCardBits (q : α × β → ℝ) (K : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ κ : β → Fin K → ℝ, (∀ y, IsPMF (κ y)) ∧ helperCond q κ / log 2 ≤ R.1 ∧
    helperInfo q κ / log 2 ≤ R.2}

/-- The auxiliary alphabet can be bounded. -/
theorem helperRegionBits_eq_card (hq : IsPMF q) :
    helperRegionBits q = helperRegionCardBits q (Fintype.card β + 1) := by
  refine Set.Subset.antisymm ?_ fun R ⟨κ, hκ, h₁, h₂⟩ => ⟨_, κ, hκ, h₁, h₂⟩
  rintro R ⟨k, κ, hκ, h₁, h₂⟩
  obtain ⟨κ', hκ', e₁, e₂⟩ := exists_helper_reduce hq hκ
  exact ⟨κ', hκ', by rwa [e₁], by rwa [e₂]⟩

/-- With a bounded auxiliary alphabet the region is closed. -/
theorem isClosed_helperRegionCardBits (hq : IsPMF q) (K : ℕ) :
    IsClosed (helperRegionCardBits q K) := by
  have hc₀ := continuousOn_sideRate (υ := Fin K) (helperSwap_isPMF hq) 0
  have hc₁ := continuousOn_sideRate (υ := Fin K) (helperSwap_isPMF hq) 1
  have hC : ContinuousOn (fun κ : β → Fin K → ℝ => helperCond q κ) {κ | IsChannel κ} := by
    have h₀ : ContinuousOn (fun κ : β → Fin K → ℝ => H[Prod.fst ; q] -
        (sideRate 0 (helperSwap q) κ - sideRate 1 (helperSwap q) κ)) {κ | IsChannel κ} :=
      continuousOn_const.sub (hc₀.sub hc₁)
    exact h₀.congr fun κ hκ => helperCond_eq_sideRate hq hκ
  have hI : ContinuousOn (fun κ : β → Fin K → ℝ => helperInfo q κ) {κ | IsChannel κ} :=
    hc₀.congr fun κ _ => helperInfo_eq_sideRate q κ
  have h := isClosed_exists_forall_le (J := Bool) (E := ℝ × ℝ)
    (K := {κ : β → Fin K → ℝ | IsChannel κ}) isCompact_setOf_isChannel
    (L := fun b R => if b then -R.1 else -R.2)
    (F := fun b κ => if b then -(helperCond q κ / log 2) else -(helperInfo q κ / log 2))
    (by
      rintro (_ | _)
      · simp only [Bool.false_eq_true, ite_false]
        exact continuous_snd.neg
      · simp only [ite_true]
        exact continuous_fst.neg) (by
      rintro (_ | _)
      · simp only [Bool.false_eq_true, ite_false]
        exact (hI.div_const _).neg
      · simp only [ite_true]
        exact (hC.div_const _).neg)
  convert h using 1
  ext R
  simp only [helperRegionCardBits, Set.mem_ofPred_eq, Bool.forall_bool, Bool.false_eq_true,
    ite_false, ite_true, neg_le_neg_iff]
  constructor
  · rintro ⟨κ, hκ, h₁, h₂⟩
    exact ⟨κ, hκ, h₂, h₁⟩
  · rintro ⟨κ, hκ, h₂, h₁⟩
    exact ⟨κ, hκ, h₁, h₂⟩

/-- **Theorem 2 of Lecture 11 of [elgamal2010], page 11-23.** The optimal rate region for lossless
source coding with a helper is `R₁ ≥ H(X | U)`, `R₂ ≥ I(Y; U)` for some `p(u | y)` with
`|𝒰| ≤ |𝒴| + 1`, with no closure. -/
theorem helperOptimalRegionBits_eq_card (hq : IsPMF q) :
    helperOptimalRegionBits q = helperRegionCardBits q (Fintype.card β + 1) := by
  rw [helperOptimalRegionBits_eq hq, helperRegionBits_eq_card hq,
    (isClosed_helperRegionCardBits hq _).closure_eq]

end InfoTheory
