/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture15Examples
public import InfoTheoryLib.Network.MACFeedbackMarkov
public import InfoTheoryLib.Network.TwoWayExamples

/-!
# Lecture 18 of El Gamal and Kim: the binary erasure MAC with feedback

Page 18-24 of the notes evaluates the Cover–Leung inner bound for the binary erasure MAC with
`U ∼ Bern(1/2)` and `Xⱼ = U ⊕ Vⱼ`, where `Vⱼ ∼ Bern(0.2377)`. We take `Vⱼ ∼ Bern(1/4)`, for which
the entropies are explicit.

## Main definitions

* `clErasureA`: the law of an input given `U`.

## Main statements

* `isAchievableMACFB_binaryErasureMAC`: the symmetric rate `25 / 32` is achievable with feedback.
* `feedback_enlarges_binaryErasureMAC`: **feedback enlarges the capacity region** of the binary
  erasure MAC, since `2 · 25 / 32 > 3 / 2`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-- The law of an input given `U`: `X = U ⊕ V` with `V ∼ Bern(1/4)`. -/
def clErasureA (u : Bool) : Bool → ℝ := msBern (if u then 3 / 4 else 1 / 4)

lemma clErasureA_isChannel : IsChannel clErasureA := fun u => by
  cases u
  · exact msBern_isPMF (by norm_num) (by norm_num)
  · exact msBern_isPMF (by norm_num) (by norm_num)

/-- The law of `U`. -/
def clErasureU : Bool → ℝ := msBern (1 / 2)

lemma clErasureU_isPMF : IsPMF clErasureU := msBern_isPMF (by norm_num) (by norm_num)

/-- The law of `((U, X₁, X₂), Y)`. -/
def clErasureLaw : (Bool × (Bool × Bool)) × Fin 3 → ℝ :=
  clLaw clErasureU clErasureA clErasureA binaryErasureMAC

lemma clErasureLaw_isPMF : IsPMF clErasureLaw :=
  clLaw_isPMF clErasureU_isPMF clErasureA_isChannel clErasureA_isChannel
    binaryErasureMAC_isChannel

/-- The output takes only the values of the channel. -/
lemma clErasureLaw_eq_zero {z : (Bool × (Bool × Bool)) × Fin 3}
    (h : z.2 ≠ binaryErasureMACOut z.1.2) : clErasureLaw z = 0 := by
  simp only [clErasureLaw, clLaw, jointOf, binaryErasureMAC, detMAC]
  rw [ite_eq_right h, mul_zero]

/-- `∑ᵤ p(u) H(X | U = u) = H(1 / 4)`. -/
lemma sum_entropy_clErasureA : ∑ k, clErasureU k * entropy (clErasureA k) = binEntropy (3 / 4) := by
  have h₁ : entropy (clErasureA true) = binEntropy (3 / 4) := by
    simp only [clErasureA, ite_true]
    exact entropy_msBern (by norm_num) (by norm_num)
  have h₂ : entropy (clErasureA false) = binEntropy (3 / 4) := by
    simp only [clErasureA, Bool.false_eq_true, ite_false]
    rw [entropy_msBern (by norm_num) (by norm_num), show (1 / 4 : ℝ) = 1 - 3 / 4 by norm_num,
      binEntropy_one_sub]
  simp only [Fintype.sum_bool, h₁, h₂, clErasureU, msBern, ite_true, Bool.false_eq_true,
    ite_false]
  ring

/-- `I(X₁; Y | X₂, U) = H(1 / 4)`. -/
lemma info₁_clErasure :
    I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ; clErasureLaw] =
      binEntropy (3 / 4) := by
  classical
  have hμ := clErasureLaw_isPMF
  have hH := clLaw_dist₂ (pu := clErasureU) (A := clErasureA) (B := clErasureA)
    binaryErasureMAC_isChannel
  have h₁ := (tw_cond hμ clErasureA_isChannel clErasureA_isChannel hH).2
  have h₂ := tw_condEntropy hμ clErasureU_isPMF clErasureA_isChannel clErasureA_isChannel hH
  have h₀ : H[fun z : (Bool × (Bool × Bool)) × Fin 3 => z.1.2.1 |
      pair (fun z => (z.1.1, z.1.2.2)) Prod.snd ; clErasureLaw] = 0 := by
    refine condEntropy_eq_zero_of_errProb_eq_zero hμ _ _
      (fun t : (Bool × Bool) × Fin 3 => if t.2 = 2 then true else if t.2 = 0 then false else !t.1.2)
        ?_
    refine sum_eq_zero fun z _ => ?_
    obtain ⟨⟨u, a, b⟩, y⟩ := z
    by_cases hy : y = binaryErasureMACOut (a, b)
    · subst hy
      cases a <;> cases b <;> simp [pair, binaryErasureMACOut]
    · rw [clErasureLaw_eq_zero hy]
      exact ite_self 0
  rw [condMutualInfo_eq' hμ, h₀, sub_zero]
  exact h₁.trans (h₂.trans sum_entropy_clErasureA)

/-- `I(X₂; Y | X₁, U) = H(1 / 4)`. -/
lemma info₂_clErasure :
    I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ; clErasureLaw] =
      binEntropy (3 / 4) := by
  classical
  have hμ := clErasureLaw_isPMF
  have hH := clLaw_dist₁ (pu := clErasureU) (A := clErasureA) (B := clErasureA)
    binaryErasureMAC_isChannel
  have h₁ := (tw_cond hμ clErasureA_isChannel clErasureA_isChannel hH).2
  have h₂ := tw_condEntropy hμ clErasureU_isPMF clErasureA_isChannel clErasureA_isChannel hH
  have h₀ : H[fun z : (Bool × (Bool × Bool)) × Fin 3 => z.1.2.2 |
      pair (fun z => (z.1.1, z.1.2.1)) Prod.snd ; clErasureLaw] = 0 := by
    refine condEntropy_eq_zero_of_errProb_eq_zero hμ _ _
      (fun t : (Bool × Bool) × Fin 3 => if t.2 = 2 then true else if t.2 = 0 then false else !t.1.2)
        ?_
    refine sum_eq_zero fun z _ => ?_
    obtain ⟨⟨u, a, b⟩, y⟩ := z
    by_cases hy : y = binaryErasureMACOut (a, b)
    · subst hy
      cases a <;> cases b <;> simp [pair, binaryErasureMACOut]
    · rw [clErasureLaw_eq_zero hy]
      exact ite_self 0
  rw [condMutualInfo_eq' hμ, h₀, sub_zero]
  exact h₁.trans (h₂.trans sum_entropy_clErasureA)

/-- The law of the inputs. -/
def clErasureP (x : Bool × Bool) : ℝ := if x.1 = x.2 then 5 / 16 else 3 / 16

lemma dist_twIn_clErasure : dist (twIn clErasureU clErasureA clErasureA) Prod.snd = clErasureP := by
  funext ⟨a, b⟩
  cases a <;> cases b <;>
    simp [dist, twIn, jointOf, prodDist, clErasureU, clErasureA, clErasureP, msBern,
      Fintype.sum_prod_type] <;> norm_num

/-- `I(X₁, X₂; Y) = H(Y)`, with the law `(5 / 16, 3 / 8, 5 / 16)`. -/
lemma info₃_clErasure :
    I[fun z => z.1.2 : Prod.snd ; clErasureLaw] =
      negMulLog (5 / 16) + negMulLog (3 / 8) + negMulLog (5 / 16) := by
  have hp : IsPMF clErasureP := by
    rw [← dist_twIn_clErasure]
    exact (jointOf_isPMF clErasureU_isPMF fun k =>
      (clErasureA_isChannel k).prodDist (clErasureA_isChannel k)).dist _
  rw [clErasureLaw, cl_info₃ clErasureU_isPMF clErasureA_isChannel clErasureA_isChannel
    binaryErasureMAC_isChannel, dist_twIn_clErasure]
  unfold binaryErasureMAC
  rw [mutualInfoOf_eq hp (detMAC_isChannel binaryErasureMACOut)]
  have he : ∀ x : Bool × Bool, entropy (detMAC binaryErasureMACOut x) = 0 := fun x => by
    obtain ⟨a, b⟩ := x
    cases a <;> cases b <;>
      simp [entropy_eq_sum_negMulLog, Fin.sum_univ_three, detMAC, binaryErasureMACOut]
  simp only [he, mul_zero, sum_const_zero, sub_zero]
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_three]
  have e₀ : outDist clErasureP (detMAC binaryErasureMACOut) 0 = 5 / 16 := by
    simp [outDist, Fintype.sum_prod_type, clErasureP, detMAC, binaryErasureMACOut]
  have e₁ : outDist clErasureP (detMAC binaryErasureMACOut) 1 = 3 / 8 := by
    simp [outDist, Fintype.sum_prod_type, clErasureP, detMAC, binaryErasureMACOut]
    norm_num
  have e₂ : outDist clErasureP (detMAC binaryErasureMACOut) 2 = 5 / 16 := by
    simp [outDist, Fintype.sum_prod_type, clErasureP, detMAC, binaryErasureMACOut]
  rw [e₀, e₁, e₂]

/-- The value of `H(Y)`: it exceeds `25 / 16` bits. -/
lemma entropy_clErasure_gt :
    (25 / 32 + 25 / 32 : ℝ) * log 2 < negMulLog (5 / 16) + negMulLog (3 / 8) + negMulLog (5 / 16) :=
      by
  have h : 10 * log 5 + 6 * log 3 < 33 * log 2 := by
    have hlt : ((5 : ℝ) ^ 10 * 3 ^ 6) < 2 ^ 33 := by norm_num
    have := log_lt_log (by positivity) hlt
    rw [log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow] at this
    exact_mod_cast this
  have e₁ : log (5 / 16 : ℝ) = log 5 - 4 * log 2 := by
    rw [log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
    norm_num
  have e₂ : log (3 / 8 : ℝ) = log 3 - 3 * log 2 := by
    rw [log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    norm_num
  simp only [negMulLog]
  rw [e₁, e₂]
  linarith

/-- The value of `H(1 / 4)`: it exceeds `25 / 32` bits. -/
lemma binEntropy_clErasure_gt : (25 / 32 : ℝ) * log 2 < binEntropy (3 / 4) := by
  have h := three_fifths_le_binEntropy
  have hl : 0 < log 2 := log_pos (by norm_num)
  linarith

/-- **Page 18-24 of [elgamal2010].** The symmetric rate `25 / 32` is achievable for the binary
erasure MAC with feedback. The notes state the larger value `0.7911`. -/
theorem isAchievableMACFB_binaryErasureMAC :
    IsAchievableMACFB binaryErasureMAC (25 / 32) (25 / 32) := by
  refine isAchievableMACFB_coverLeung (pu := clErasureU) (A := clErasureA) (B := clErasureA)
    clErasureU_isPMF clErasureA_isChannel clErasureA_isChannel binaryErasureMAC_isChannel
    (by norm_num) (by norm_num) ?_ ?_ ?_
  · refine lt_of_lt_of_eq binEntropy_clErasure_gt info₁_clErasure.symm
  · refine lt_of_lt_of_eq binEntropy_clErasure_gt info₂_clErasure.symm
  · refine lt_of_lt_of_eq entropy_clErasure_gt info₃_clErasure.symm

/-- **Lecture 4.** Without feedback the sum of the rates of the binary erasure MAC is at most
`3 / 2`. -/
theorem macCapacityRegionBits_binaryErasureMAC_sum_le :
    macCapacityRegionBits binaryErasureMAC ⊆ {R : ℝ × ℝ | R.1 + R.2 ≤ 3 / 2} := by
  have hl := log_pos one_lt_two
  have hS : IsClosed {R : ℝ × ℝ | R.1 + R.2 ≤ 3 / 2} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hC : Convex ℝ {R : ℝ × ℝ | R.1 + R.2 ≤ 3 / 2} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy ⊢
    have h₁ := mul_le_mul_of_nonneg_left hx ha
    have h₂ := mul_le_mul_of_nonneg_left hy hb
    have e : a * (3 / 2) + b * (3 / 2) = 3 / 2 := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  rw [macCapacityRegionBits_eq binaryErasureMAC_isChannel]
  refine closure_minimal (convexHull_min ?_ hC) hS
  rintro R ⟨p₁, p₂, hp₁, hp₂, -, -, h₃⟩
  have hb : ∀ p : Bool → ℝ, IsPMF p → p = bernoulliPMF (p true) := by
    intro p hp
    have hs := hp.sum_eq_one
    simp only [Fintype.sum_bool] at hs
    funext b
    cases b
    · simp only [bernoulliPMF, Bool.false_eq_true, ite_false]
      linarith
    · simp [bernoulliPMF]
  have hr : ∀ p : Bool → ℝ, IsPMF p → 0 ≤ p true ∧ p true ≤ 1 := by
    intro p hp
    have hs := hp.sum_eq_one
    simp only [Fintype.sum_bool] at hs
    have := hp.nonneg false
    exact ⟨hp.nonneg true, by linarith⟩
  have hsum := erasure_sum_le (hr p₁ hp₁).1 (hr p₁ hp₁).2 (hr p₂ hp₂).1 (hr p₂ hp₂).2
  rw [← hb p₁ hp₁, ← hb p₂ hp₂] at hsum
  have h₄ : macInfo₁₂ p₁ p₂ binaryErasureMAC / log 2 ≤ 3 / 2 := by
    rw [div_le_iff₀ hl]
    exact hsum
  exact le_trans h₃ h₄

/-- **Page 18-19 of [elgamal2010]: feedback enlarges the capacity region.** Without feedback the sum
of the rates of the binary erasure MAC is at most `3 / 2`, and with feedback the symmetric rate
`25 / 32 > 3 / 4` is achievable. -/
theorem feedback_enlarges_binaryErasureMAC :
    ((25 / 32 : ℝ), (25 / 32 : ℝ)) ∈ macfbCapacityRegion binaryErasureMAC ∧
      ((25 / 32 : ℝ), (25 / 32 : ℝ)) ∉ macCapacityRegionBits binaryErasureMAC := by
  refine ⟨subset_closure isAchievableMACFB_binaryErasureMAC, fun h => ?_⟩
  have := macCapacityRegionBits_binaryErasureMAC_sum_le h
  simp only [Set.mem_ofPred_eq] at this
  norm_num at this

end InfoTheory.ElGamalKim
