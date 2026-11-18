/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.InfoInequalities.ZhangYeung
public import InfoTheoryLib.RelativeEntropy.Gibbs

/-!
# Non-Shannon-type inequalities

The Zhang–Yeung inequality (15.62) is not implied by the basic inequalities: the vector `h̃(a)` of
(15.85) satisfies all the elemental inequalities but not (15.62). So `Γ*₄` and its closure are
strictly smaller than `Γ₄` (Theorem 15.11). Since `h̃(a)` makes 14 Shannon's information measures
vanish, (15.62) stays non-Shannon-type under any of the constraints that set some of them to zero
(Theorem 15.12).

Under `I(X₁; X₂) = I(X₁; X₂ | X₃) = 0`, the inequality `I(X₃; X₄) ≤ I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂)`
holds (Theorem 15.14). The proof compares `p` with the distribution `p̃` of `(X₁, X̃₂, X₃, X₄)` on
the copy (Lemma 15.13), through the divergence inequality for the sub-probability `p̂` of (15.124).
The same vector `h̃(a)` shows that this constrained inequality is non-Shannon-type as well
(Theorems 15.15 and 15.16).

## Main definitions

* `condInfoFunctional S T K`: `I(X_S; X_T | X_K)` as a linear functional on the entropy space.
* `canonicalForm L`: the coefficient vector `b` of a linear functional, `L h = b ⬝ h`.
* `zyFunctional`, `zyCoeff`: the inequality (15.62) in canonical form, (16.114).
* `zyPoint a`: the vector `h̃(a)` of (15.85).
* `copyTilde X`: the vector `(X₁, X̃₂, X₃, X₄)` on the copy, and `pHat μ X`: `p̂` of (15.124).
* `zyConstrainedFunctional`, `zyConstrainedCoeff`, `zyConstraint`: the inequality (15.113) and
  the constraints (15.112) in the entropy space.

## Main statements

* `infoExpr_zyCoeff_nonneg`: (15.62) holds on `Γ*₄`.
* `zyPoint_mem_shannonRegion`, `zyFunctional_zyPoint`: `h̃(a) ∈ Γ₄` violates (15.62).
* `not_isShannonType_zyCoeff`, `entropicRegion_fin_four_ne`, `closure_entropicRegion_fin_four_ne`:
  **Theorem 15.11**.
* `not_isShannonType_zyCoeff_constrained`: **Theorem 15.12**.
* `dist_copyTilde`: **Lemma 15.13**.
* `sum_pHat_le_one`: (15.126)–(15.143).
* `zhangYeung_constrained`, `ineqAlwaysHolds_zyConstrainedCoeff`: **Theorem 15.14**.
* `not_isShannonType_zyConstrainedCoeff_zyConstraint`: **Theorem 15.15**.
* `not_isShannonType_zyConstrainedCoeff`: **Theorem 15.16**.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 15.2 and 15.3
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Linear functionals and canonical forms -/

section Functional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient vector `b` of a linear functional `L` on the entropy space, so that
`L h = b ⬝ h`: the canonical form of Section 13.2. -/
def canonicalForm (L : EntropySpace ι →ₗ[ℝ] ℝ) : EntropySpace ι := fun α => L (Pi.single α 1)

lemma infoExpr_canonicalForm (L : EntropySpace ι →ₗ[ℝ] ℝ) (h : EntropySpace ι) :
    infoExpr (canonicalForm L) h = L h := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ L h, infoExpr]
  refine sum_congr rfl fun α _ => ?_
  rw [smul_eq_mul, mul_comm, canonicalForm]
  congr 2
  funext β
  simp [Pi.single_apply, eq_comm]

omit [Fintype ι] in
lemma condInfo_add (f g : Finset ι → ℝ) (S T K : Finset ι) :
    condInfo (f + g) S T K = condInfo f S T K + condInfo g S T K := by
  simp only [condInfo, Pi.add_apply]
  ring

omit [Fintype ι] in
lemma condInfo_smul (c : ℝ) (f : Finset ι → ℝ) (S T K : Finset ι) :
    condInfo (c • f) S T K = c * condInfo f S T K := by
  simp only [condInfo, Pi.smul_apply, smul_eq_mul]
  ring

/-- `I(X_S; X_T | X_K)` as a linear functional of the entropy function. -/
def condInfoFunctional (S T K : Finset ι) : EntropySpace ι →ₗ[ℝ] ℝ where
  toFun h := condInfo h.extend S T K
  map_add' h g := by rw [EntropySpace.extend_add, condInfo_add]
  map_smul' c h := by rw [EntropySpace.extend_smul, condInfo_smul, RingHom.id_apply, smul_eq_mul]

omit [Fintype ι] in
@[simp] lemma condInfoFunctional_apply (S T K : Finset ι) (h : EntropySpace ι) :
    condInfoFunctional S T K h = condInfo h.extend S T K := rfl

omit [Fintype ι] in
/-- `condInfo` of a natural-number valued set function, as an integer. -/
lemma condInfo_natCast (g : Finset ι → ℕ) (S T K : Finset ι) :
    condInfo (fun s => (g s : ℝ)) S T K =
      (((g (K ∪ S) + g (K ∪ T) : ℕ) : ℤ) - g (K ∪ S ∪ T) - g K : ℤ) := by
  simp only [condInfo]
  push_cast
  ring

end Functional

/-! ### The inequality in canonical form -/

/-- The inequality (15.62) as the linear functional
`I(X₁; X₂) + I(X₁; X₃, X₄) + 3 I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂) - 2 I(X₃; X₄) ≥ 0`. -/
def zyFunctional : EntropySpace (Fin 4) →ₗ[ℝ] ℝ :=
  condInfoFunctional {0} {1} ∅ + condInfoFunctional {0} {2, 3} ∅ +
    (3 : ℝ) • condInfoFunctional {2} {3} {0} + condInfoFunctional {2} {3} {1} -
      (2 : ℝ) • condInfoFunctional {2} {3} ∅

/-- The coefficient vector of (15.62), whose canonical form is (16.114). -/
def zyCoeff : EntropySpace (Fin 4) := canonicalForm zyFunctional

/-- **Theorem 15.7**, on `Γ*₄`: the inequality (15.62) always holds. -/
theorem infoExpr_zyCoeff_nonneg {h : EntropySpace (Fin 4)} (hh : h ∈ entropicRegion (Fin 4)) :
    0 ≤ infoExpr zyCoeff h := by
  obtain ⟨Ω, _, A, _, μ, X, hμ, rfl⟩ := hh
  rw [zyCoeff, infoExpr_canonicalForm]
  simp only [zyFunctional, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    condInfoFunctional_apply, smul_eq_mul, extend_entropyVector hμ]
  have := zhangYeung_of_copy (isPolymatroid_blockEntropy (isPMF_copyMeasure hμ))
    (copy_fst (X := X) hμ) (copy_snd hμ) (copy_markov hμ)
  linarith

/-! ### The vector `h̃(a)` -/

/-- The entropies of `h̃(1)`, (15.85): `2` on singletons, `4` on `{1, 2}`, `3` on the other pairs
and `4` on the larger sets. -/
def zyNat (s : Finset (Fin 4)) : ℕ :=
  if s = ∅ then 0 else if #s = 1 then 2 else if s = {0, 1} then 4 else if #s = 2 then 3 else 4

/-- The vector `h̃(a)` of (15.85). -/
def zyPoint (a : ℝ) : EntropySpace (Fin 4) := fun α => a * zyNat α.1

lemma extend_zyPoint (a : ℝ) : (zyPoint a).extend = a • fun s => (zyNat s : ℝ) := by
  funext s
  rw [EntropySpace.extend]
  split_ifs with hs
  · rfl
  · simp [not_nonempty_iff_eq_empty.1 hs, zyNat]

lemma isPolymatroid_zyNat : IsPolymatroid fun s => (zyNat s : ℝ) := by
  have hm : ∀ s t : Finset (Fin 4), s ⊆ t → zyNat s ≤ zyNat t := by decide
  have hs : ∀ s t : Finset (Fin 4), zyNat (s ∪ t) + zyNat (s ∩ t) ≤ zyNat s + zyNat t := by
    decide
  refine ⟨by simp [zyNat], fun s t hst => by exact_mod_cast hm s t hst, fun s t => ?_⟩
  exact_mod_cast hs s t

/-- `h̃(a)` satisfies the elemental inequalities for `a ≥ 0`. -/
theorem zyPoint_mem_shannonRegion {a : ℝ} (ha : 0 ≤ a) : zyPoint a ∈ shannonRegion (Fin 4) := by
  rw [mem_shannonRegion_iff, extend_zyPoint]
  exact isPolymatroid_zyNat.const_smul ha

lemma condInfo_zyPoint (a : ℝ) (S T K : Finset (Fin 4)) :
    condInfo (zyPoint a).extend S T K =
      a * (((zyNat (K ∪ S) + zyNat (K ∪ T) : ℕ) : ℤ) - zyNat (K ∪ S ∪ T) - zyNat K : ℤ) := by
  rw [extend_zyPoint, condInfo_smul, condInfo_natCast]

/-- (15.86): `h̃(a)` violates (15.62): the right side minus the left side is `-a`. -/
theorem zyFunctional_zyPoint (a : ℝ) : zyFunctional (zyPoint a) = -a := by
  simp only [zyFunctional, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    condInfoFunctional_apply, smul_eq_mul, condInfo_zyPoint]
  have e : ((((zyNat (∅ ∪ {0}) + zyNat (∅ ∪ {1}) : ℕ) : ℤ) - zyNat (∅ ∪ {0} ∪ {1}) -
      zyNat ∅ : ℤ) : ℝ) = 0 ∧
      ((((zyNat (∅ ∪ {0}) + zyNat (∅ ∪ {2, 3}) : ℕ) : ℤ) - zyNat (∅ ∪ {0} ∪ {2, 3}) -
        zyNat ∅ : ℤ) : ℝ) = 1 ∧
      ((((zyNat ({0} ∪ {2}) + zyNat ({0} ∪ {3}) : ℕ) : ℤ) - zyNat ({0} ∪ {2} ∪ {3}) -
        zyNat {0} : ℤ) : ℝ) = 0 ∧
      ((((zyNat ({1} ∪ {2}) + zyNat ({1} ∪ {3}) : ℕ) : ℤ) - zyNat ({1} ∪ {2} ∪ {3}) -
        zyNat {1} : ℤ) : ℝ) = 0 ∧
      ((((zyNat (∅ ∪ {2}) + zyNat (∅ ∪ {3}) : ℕ) : ℤ) - zyNat (∅ ∪ {2} ∪ {3}) -
        zyNat ∅ : ℤ) : ℝ) = 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_cast
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]
  ring

/-- **Theorem 15.11.** The inequality (15.62) is a non-Shannon-type inequality. -/
theorem not_isShannonType_zyCoeff : ¬IsShannonType zyCoeff Set.univ := fun h => by
  have := h (zyPoint 1) ⟨zyPoint_mem_shannonRegion zero_le_one, Set.mem_univ _⟩
  rw [zyCoeff, infoExpr_canonicalForm, zyFunctional_zyPoint] at this
  norm_num at this

/-- **Theorem 15.11.** `Γ*₄` is strictly smaller than `Γ₄`. -/
theorem entropicRegion_fin_four_ne : entropicRegion (Fin 4) ≠ shannonRegion (Fin 4) := by
  intro h
  have := infoExpr_zyCoeff_nonneg (h ▸ zyPoint_mem_shannonRegion zero_le_one :
    zyPoint 1 ∈ entropicRegion (Fin 4))
  rw [zyCoeff, infoExpr_canonicalForm, zyFunctional_zyPoint] at this
  norm_num at this

/-- **Theorem 15.11.** The closure of `Γ*₄` is strictly smaller than `Γ₄`, (15.86)–(15.90). -/
theorem closure_entropicRegion_fin_four_ne :
    closure (entropicRegion (Fin 4)) ≠ shannonRegion (Fin 4) := by
  intro h
  have hsub := (ineqAlwaysHolds_iff_closure_subset zyCoeff).1
    fun x hx => infoExpr_zyCoeff_nonneg hx.1
  have := hsub (h ▸ zyPoint_mem_shannonRegion zero_le_one : zyPoint 1 ∈ closure _)
  simp only [Set.mem_ofPred_eq] at this
  rw [zyCoeff, infoExpr_canonicalForm, zyFunctional_zyPoint] at this
  norm_num at this

/-- The 14 Shannon's information measures of (15.94) that vanish at `h̃(a)`, as `(S, T, K)` for
`I(X_S; X_T | X_K)`; `H(Xᵢ | X_K)` is `I(Xᵢ; Xᵢ | X_K)`. -/
def zyMeasures : Fin 14 → Finset (Fin 4) × Finset (Fin 4) × Finset (Fin 4) :=
  ![({0}, {1}, ∅), ({0}, {1}, {2}), ({0}, {1}, {3}), ({0}, {2}, {3}), ({0}, {3}, {2}),
    ({1}, {2}, {3}), ({1}, {3}, {2}), ({2}, {3}, {0}), ({2}, {3}, {1}), ({2}, {3}, {0, 1}),
    ({0}, {0}, {1, 2, 3}), ({1}, {1}, {0, 2, 3}), ({2}, {2}, {0, 1, 3}), ({3}, {3}, {0, 1, 2})]

lemma condInfo_zyPoint_zyMeasures (a : ℝ) (k : Fin 14) :
    condInfo (zyPoint a).extend (zyMeasures k).1 (zyMeasures k).2.1 (zyMeasures k).2.2 = 0 := by
  rw [condInfo_zyPoint]
  have : ∀ k : Fin 14, ((zyNat ((zyMeasures k).2.2 ∪ (zyMeasures k).1) +
      zyNat ((zyMeasures k).2.2 ∪ (zyMeasures k).2.1) : ℕ) : ℤ) -
      zyNat ((zyMeasures k).2.2 ∪ (zyMeasures k).1 ∪ (zyMeasures k).2.1) -
        zyNat (zyMeasures k).2.2 = 0 := by decide
  rw [this k, Int.cast_zero, mul_zero]

/-- **Theorem 15.12.** The inequality (15.62) is a non-Shannon-type inequality under the
constraint that any subset of the 14 Shannon's information measures (15.94) vanishes. -/
theorem not_isShannonType_zyCoeff_constrained (P : Finset (Fin 14)) :
    ¬IsShannonType zyCoeff {h | ∀ k ∈ P,
      condInfo h.extend (zyMeasures k).1 (zyMeasures k).2.1 (zyMeasures k).2.2 = 0} := fun h => by
  have := h (zyPoint 1) ⟨zyPoint_mem_shannonRegion zero_le_one,
    fun k _ => condInfo_zyPoint_zyMeasures 1 k⟩
  rw [zyCoeff, infoExpr_canonicalForm, zyFunctional_zyPoint] at this
  norm_num at this

/-! ### A constrained non-Shannon-type inequality -/

section Constrained

variable {Ω : Type*} [Fintype Ω] {A : Fin 4 → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}
  {X : ∀ i, Ω → A i}

/-- The vector `(X₁, X̃₂, X₃, X₄)` on the copy, whose distribution is `p̃` of (15.98). -/
def copyTilde (X : ∀ i, Ω → A i) (q : Ω × Ω) : A 0 × A 1 × A 2 × A 3 :=
  (X 0 q.1, X 1 q.2, X 2 q.1, X 3 q.1)

omit [∀ i, Fintype (A i)] in
/-- **Lemma 15.13.** `p̃(x) = p(x₁, x₃, x₄) p(x₂, x₃, x₄) / p(x₃, x₄)` (15.98) is the distribution
of `(X₁, X̃₂, X₃, X₄)`, and `p̃(x₁, x₃, x₄) = p(x₁, x₃, x₄)` and `p̃(x₂, x₃, x₄) = p(x₂, x₃, x₄)`
(15.99)–(15.100). -/
theorem dist_copyTilde [∀ i, Finite (A i)] (hμ : IsPMF μ) :
    (∀ y, dist (copyMeasure μ X) (copyTilde X) y =
      dist μ (pair (X 0) (copyBase X)) (y.1, y.2.2) *
        dist μ (pair (X 1) (copyBase X)) (y.2.1, y.2.2) / dist μ (copyBase X) y.2.2) ∧
    (∀ z, dist (copyMeasure μ X) (fun q => (X 0 q.1, X 2 q.1, X 3 q.1)) z =
      dist μ (fun ω => (X 0 ω, X 2 ω, X 3 ω)) z) ∧
    (∀ z, dist (copyMeasure μ X) (fun q => (X 1 q.2, X 2 q.1, X 3 q.1)) z =
      dist μ (fun ω => (X 1 ω, X 2 ω, X 3 ω)) z) := by
  refine ⟨fun y => ?_, fun z => dist_copyMeasure_fst hμ (fun ω => (X 0 ω, X 2 ω, X 3 ω)) z,
    fun z => ?_⟩
  · obtain ⟨y₀, y₁, y₂, y₃⟩ := y
    rw [← dist_copyMeasure_triple (X 0) (X 1) y₀ (y₂, y₃) y₁]
    exact dist_congr_of_iff _ fun q => by
      simp only [copyTilde, copyBase, pair, Prod.mk.injEq]
      tauto
  · rw [← dist_copyMeasure_snd (X := X) hμ (fun ω => (X 1 ω, X 2 ω, X 3 ω)) z]
    refine dist_copyMeasure_congr (fun q hq => ?_) z
    have hK := copyMeasure_ne_zero hq
    simp only [copyBase, pair, Prod.mk.injEq] at hK
    rw [hK.1, hK.2]

/-- `∑_y p(y) log P(pr y) = -H(P)` when `P` is the distribution of `pr` of the random variable. -/
lemma sum_dist_mul_log_comp {Ω' β γ : Type*} [Fintype Ω'] [Fintype β] [Fintype γ]
    (ν : Ω' → ℝ) (V : Ω' → β) (pr : β → γ) {P : γ → ℝ} (hP : dist ν (pr ∘ V) = P) :
    ∑ y, dist ν V y * log (P (pr y)) = -entropy P := by
  calc ∑ y, dist ν V y * log (P (pr y)) = ∑ ω, ν ω * log (P (pr (V ω))) :=
        sum_dist_mul ν V _
    _ = ∑ z, dist ν (pr ∘ V) z * log (P z) := (sum_dist_mul ν (pr ∘ V) fun z => log (P z)).symm
    _ = -entropy P := by
        rw [hP, entropy_eq_sum_negMulLog, ← sum_neg_distrib]
        exact sum_congr rfl fun z _ => by rw [negMulLog]; ring

/-- The function `p̂` of (15.124). -/
def pHat (μ : Ω → ℝ) (X : ∀ i, Ω → A i) (y : A 0 × A 1 × A 2 × A 3) : ℝ :=
  dist μ (pair (X 0) (X 2)) (y.1, y.2.2.1) * dist μ (pair (X 0) (X 3)) (y.1, y.2.2.2) *
    dist μ (pair (X 1) (X 2)) (y.2.1, y.2.2.1) * dist μ (pair (X 1) (X 3)) (y.2.1, y.2.2.2) /
      (dist μ (X 0) y.1 * dist μ (X 1) y.2.1 * dist μ (X 2) y.2.2.1 * dist μ (X 3) y.2.2.2)

omit [∀ i, Fintype (A i)] in
lemma pHat_nonneg (hμ : IsPMF μ) (y : A 0 × A 1 × A 2 × A 3) : 0 ≤ pHat μ X y := by
  unfold pHat
  refine div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_)
    (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) <;> exact dist_nonneg hμ _ _

/-- (15.126)–(15.143): under `I(X₁; X₂) = I(X₁; X₂ | X₃) = 0`, `p̂` is a sub-probability. -/
lemma sum_pHat_le_one (hμ : IsPMF μ) (hI : IndepRV μ (X 0) (X 1))
    (hC : CondIndep μ (X 0) (X 1) (X 2)) : ∑ y, pHat μ X y ≤ 1 := by
  classical
  have hmul := (condIndep_iff_mul hμ (X 0) (X 2) (X 1)).1 hC
  set T : A 0 → A 2 → A 1 → ℝ := fun a c b => dist μ (pair (X 0) (pair (X 2) (X 1))) (a, c, b)
  -- (15.126): `p̂(a, b, c, d) = p(a, c, b) p(a, d) p(b, d) / (p(a) p(b) p(d))`
  have hp : ∀ a b c d, pHat μ X (a, b, c, d) = T a c b * dist μ (pair (X 0) (X 3)) (a, d) *
      dist μ (pair (X 1) (X 3)) (b, d) / (dist μ (X 0) a * dist μ (X 1) b * dist μ (X 3) d) := by
    intro a b c d
    simp only [pHat]
    by_cases hc : dist μ (X 2) c = 0
    · have hT : T a c b = 0 := le_antisymm (by
        have h₁ := dist_pair_le_right hμ (X 0) (pair (X 2) (X 1)) a (c, b)
        have h₂ := dist_pair_le_left hμ (X 2) (X 1) c b
        rw [hc] at h₂
        exact h₁.trans h₂) (dist_nonneg hμ _ _)
      rw [hc, hT]
      simp
    · have e := hmul a c b
      rw [dist_pair_swap μ (X 1) (X 2)] at e
      have key : dist μ (pair (X 0) (X 2)) (a, c) * dist μ (pair (X 0) (X 3)) (a, d) *
          dist μ (pair (X 1) (X 2)) (b, c) * dist μ (pair (X 1) (X 3)) (b, d) =
          dist μ (X 2) c * (T a c b * dist μ (pair (X 0) (X 3)) (a, d) *
            dist μ (pair (X 1) (X 3)) (b, d)) := by
        linear_combination -(dist μ (pair (X 0) (X 3)) (a, d) *
          dist μ (pair (X 1) (X 3)) (b, d)) * e
      rw [key, show dist μ (X 0) a * dist μ (X 1) b * dist μ (X 2) c * dist μ (X 3) d =
        dist μ (X 2) c * (dist μ (X 0) a * dist μ (X 1) b * dist μ (X 3) d) by ring,
        mul_div_mul_left _ _ hc]
  -- summing out `c`, (15.133)–(15.135)
  have hsumc : ∀ a b, ∑ c, T a c b = dist μ (X 0) a * dist μ (X 1) b := fun a b => by
    rw [← hI a b, ← sum_dist_pair_right μ (pair (X 0) (X 1)) (X 2) (a, b)]
    exact sum_congr rfl fun c _ => dist_congr_of_iff μ fun ω => by
      simp only [pair, Prod.mk.injEq]
      tauto
  have hstep : ∑ y, pHat μ X y = ∑ a, ∑ b, ∑ d,
      dist μ (X 0) a * dist μ (X 1) b * dist μ (pair (X 0) (X 3)) (a, d) *
        dist μ (pair (X 1) (X 3)) (b, d) /
          (dist μ (X 0) a * dist μ (X 1) b * dist μ (X 3) d) := by
    simp only [Fintype.sum_prod_type, hp]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [sum_comm, ← hsumc a b]
    refine sum_congr rfl fun d _ => ?_
    rw [← sum_div, ← sum_mul, ← sum_mul]
  rw [hstep]
  -- (15.136)–(15.143)
  calc ∑ a, ∑ b, ∑ d, dist μ (X 0) a * dist μ (X 1) b * dist μ (pair (X 0) (X 3)) (a, d) *
        dist μ (pair (X 1) (X 3)) (b, d) / (dist μ (X 0) a * dist μ (X 1) b * dist μ (X 3) d)
      ≤ ∑ a, ∑ b, ∑ d, dist μ (pair (X 0) (X 3)) (a, d) * dist μ (pair (X 1) (X 3)) (b, d) /
          dist μ (X 3) d := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun d _ => ?_
        by_cases h0 : dist μ (X 0) a * dist μ (X 1) b = 0
        · rw [h0, zero_mul, zero_mul, zero_mul, zero_div]
          exact div_nonneg (mul_nonneg (dist_nonneg hμ _ _) (dist_nonneg hμ _ _))
            (dist_nonneg hμ _ _)
        · rw [mul_assoc (dist μ (X 0) a * dist μ (X 1) b), mul_div_mul_left _ _ h0]
    _ = ∑ a, ∑ d, ∑ b, dist μ (pair (X 0) (X 3)) (a, d) * dist μ (pair (X 1) (X 3)) (b, d) /
          dist μ (X 3) d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ d, ∑ a, ∑ b, dist μ (pair (X 0) (X 3)) (a, d) * dist μ (pair (X 1) (X 3)) (b, d) /
          dist μ (X 3) d := sum_comm
    _ = ∑ d, dist μ (X 3) d * dist μ (X 3) d / dist μ (X 3) d := by
        refine sum_congr rfl fun d _ => ?_
        have e : ∑ a, ∑ b, dist μ (pair (X 0) (X 3)) (a, d) * dist μ (pair (X 1) (X 3)) (b, d) /
            dist μ (X 3) d = (∑ a, dist μ (pair (X 0) (X 3)) (a, d)) *
              (∑ b, dist μ (pair (X 1) (X 3)) (b, d)) / dist μ (X 3) d := by
          rw [sum_mul_sum, sum_div]
          exact sum_congr rfl fun a _ => by rw [sum_div]
        rw [e, sum_dist_pair_left, sum_dist_pair_left]
    _ ≤ ∑ d, dist μ (X 3) d := sum_le_sum fun d _ => by
        by_cases hd : dist μ (X 3) d = 0
        · rw [hd]
          simp
        · rw [mul_div_assoc, div_self hd, mul_one]
    _ = 1 := (hμ.dist _).sum_eq_one

omit [∀ i, Fintype (A i)] in
/-- A positive probability of `V = y` makes the distribution `P` of `pr ∘ V` positive at `pr y`. -/
lemma pos_of_dist_comp {Ω' β γ : Type*} [Fintype Ω'] {ν : Ω' → ℝ} (hν : IsPMF ν) (V : Ω' → β)
    (pr : β → γ) {P : γ → ℝ} (hP : dist ν (pr ∘ V) = P) {y : β} (hy : dist ν V y ≠ 0) :
    0 < P (pr y) :=
  hP ▸ (lt_of_le_of_ne (dist_nonneg hν _ _) (Ne.symm hy)).trans_le (dist_le_dist_comp hν V pr y)

omit [∀ i, Fintype (A i)] in
/-- The marginal of `(X₁, X̃₂, X₃, X₄)` on a function of `(X₁, X₃, X₄)` is that of `p`. -/
lemma dist_comp_copyTilde_fst [∀ i, Finite (A i)] (hμ : IsPMF μ) {γ : Type*}
    (pr : A 0 × A 1 × A 2 × A 3 → γ) (F : Ω → γ) (h : ∀ q, pr (copyTilde X q) = F q.1) :
    dist (copyMeasure μ X) (pr ∘ copyTilde X) = dist μ F := funext fun c => by
  rw [← dist_copyMeasure_fst (X := X) hμ F c, show pr ∘ copyTilde X = fun q => F q.1 from funext h]

omit [∀ i, Fintype (A i)] in
/-- The marginal of `(X₁, X̃₂, X₃, X₄)` on a function of `(X̃₂, X₃, X₄)` is that of `p`. -/
lemma dist_comp_copyTilde_snd [∀ i, Finite (A i)] (hμ : IsPMF μ) {γ : Type*}
    (pr : A 0 × A 1 × A 2 × A 3 → γ)
    (F : A 1 → A 2 × A 3 → γ) (h : ∀ q, pr (copyTilde X q) = F (X 1 q.2) (copyBase X q.1)) :
    dist (copyMeasure μ X) (pr ∘ copyTilde X) = dist μ fun ω => F (X 1 ω) (copyBase X ω) :=
  funext fun c => by
    rw [← dist_copyMeasure_snd (X := X) hμ (fun ω => F (X 1 ω) (copyBase X ω)) c,
      show pr ∘ copyTilde X = fun q => F (X 1 q.2) (copyBase X q.1) from funext h]
    refine dist_copyMeasure_congr (fun q hq => ?_) c
    simp only [copyMeasure_ne_zero hq]

/-- **Theorem 15.14.** If `I(X₁; X₂) = I(X₁; X₂ | X₃) = 0`, then
`I(X₃; X₄) ≤ I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂)` (15.112)–(15.113). -/
theorem zhangYeung_constrained (hμ : IsPMF μ) (h₁ : I[X 0 : X 1 ; μ] = 0)
    (h₂ : I[X 0 : X 1 | X 2 ; μ] = 0) :
    I[X 2 : X 3 ; μ] ≤ I[X 2 : X 3 | X 0 ; μ] + I[X 2 : X 3 | X 1 ; μ] := by
  classical
  have hI := (mutualInfo_eq_zero_iff hμ _ _).1 h₁
  have hC := (condMutualInfo_eq_zero_iff hμ _ _ _).1 h₂
  have hν := isPMF_copyMeasure (X := X) hμ
  obtain ⟨hform, -, -⟩ := dist_copyTilde (X := X) hμ
  set Q := dist (copyMeasure μ X) (copyTilde X) with hQ
  -- the marginals of `p̃` that enter (15.114)–(15.115)
  have m0 : dist (copyMeasure μ X) ((fun y : A 0 × A 1 × A 2 × A 3 => y.1) ∘ copyTilde X) =
      dist μ (X 0) := dist_comp_copyTilde_fst hμ _ _ fun _ => rfl
  have m1 : dist (copyMeasure μ X) ((fun y : A 0 × A 1 × A 2 × A 3 => y.2.1) ∘ copyTilde X) =
      dist μ (X 1) := dist_comp_copyTilde_snd hμ _ (fun b _ => b) fun _ => rfl
  have m2 : dist (copyMeasure μ X) ((fun y : A 0 × A 1 × A 2 × A 3 => y.2.2.1) ∘ copyTilde X) =
      dist μ (X 2) := dist_comp_copyTilde_fst hμ _ _ fun _ => rfl
  have m3 : dist (copyMeasure μ X) ((fun y : A 0 × A 1 × A 2 × A 3 => y.2.2.2) ∘ copyTilde X) =
      dist μ (X 3) := dist_comp_copyTilde_fst hμ _ _ fun _ => rfl
  have m02 : dist (copyMeasure μ X)
      ((fun y : A 0 × A 1 × A 2 × A 3 => (y.1, y.2.2.1)) ∘ copyTilde X) =
      dist μ (pair (X 0) (X 2)) := dist_comp_copyTilde_fst hμ _ _ fun _ => rfl
  have m03 : dist (copyMeasure μ X)
      ((fun y : A 0 × A 1 × A 2 × A 3 => (y.1, y.2.2.2)) ∘ copyTilde X) =
      dist μ (pair (X 0) (X 3)) := dist_comp_copyTilde_fst hμ _ _ fun _ => rfl
  have m12 : dist (copyMeasure μ X)
      ((fun y : A 0 × A 1 × A 2 × A 3 => (y.2.1, y.2.2.1)) ∘ copyTilde X) =
      dist μ (pair (X 1) (X 2)) := dist_comp_copyTilde_snd hμ _ (fun b c => (b, c.1)) fun _ => rfl
  have m13 : dist (copyMeasure μ X)
      ((fun y : A 0 × A 1 × A 2 × A 3 => (y.2.1, y.2.2.2)) ∘ copyTilde X) =
      dist μ (pair (X 1) (X 3)) := dist_comp_copyTilde_snd hμ _ (fun b c => (b, c.2)) fun _ => rfl
  have m023 : dist (copyMeasure μ X)
      ((fun y : A 0 × A 1 × A 2 × A 3 => (y.1, y.2.2)) ∘ copyTilde X) =
      dist μ (pair (X 0) (copyBase X)) := dist_comp_copyTilde_fst hμ _ _ fun _ => rfl
  have m123 : dist (copyMeasure μ X)
      ((fun y : A 0 × A 1 × A 2 × A 3 => (y.2.1, y.2.2)) ∘ copyTilde X) =
      dist μ (pair (X 1) (copyBase X)) :=
    dist_comp_copyTilde_snd hμ _ (fun b c => (b, c)) fun _ => rfl
  have m23 : dist (copyMeasure μ X)
      ((fun y : A 0 × A 1 × A 2 × A 3 => y.2.2) ∘ copyTilde X) =
      dist μ (copyBase X) := dist_comp_copyTilde_fst hμ _ _ fun _ => rfl
  -- `E_p̃ log p̃ = -H(X₁, X₃, X₄) - H(X₂, X₃, X₄) + H(X₃, X₄)`, by (15.98)
  have eQ : ∑ y, Q y * log (Q y) = -H[pair (X 0) (pair (X 2) (X 3)) ; μ] -
      H[pair (X 1) (pair (X 2) (X 3)) ; μ] + H[pair (X 2) (X 3) ; μ] := by
    have hl : ∀ y, Q y * log (Q y) =
        Q y * log (dist μ (pair (X 0) (copyBase X)) (y.1, y.2.2)) +
        Q y * log (dist μ (pair (X 1) (copyBase X)) (y.2.1, y.2.2)) -
        Q y * log (dist μ (copyBase X) y.2.2) := fun y => by
      by_cases hy : Q y = 0
      · simp [hy]
      have p023 : 0 < dist μ (pair (X 0) (copyBase X)) (y.1, y.2.2) :=
        pos_of_dist_comp hν _ _ m023 hy
      have p123 : 0 < dist μ (pair (X 1) (copyBase X)) (y.2.1, y.2.2) :=
        pos_of_dist_comp hν _ _ m123 hy
      have p23 : 0 < dist μ (copyBase X) y.2.2 := pos_of_dist_comp hν _ _ m23 hy
      have hlog : log (Q y) = log (dist μ (pair (X 0) (copyBase X)) (y.1, y.2.2)) +
          log (dist μ (pair (X 1) (copyBase X)) (y.2.1, y.2.2)) -
          log (dist μ (copyBase X) y.2.2) := by
        rw [hform y, log_div (mul_pos p023 p123).ne' p23.ne', log_mul p023.ne' p123.ne']
      rw [hlog]
      ring
    have s023 : ∑ y, Q y * log (dist μ (pair (X 0) (copyBase X)) (y.1, y.2.2)) =
        -H[pair (X 0) (pair (X 2) (X 3)) ; μ] := sum_dist_mul_log_comp _ _ _ m023
    have s123 : ∑ y, Q y * log (dist μ (pair (X 1) (copyBase X)) (y.2.1, y.2.2)) =
        -H[pair (X 1) (pair (X 2) (X 3)) ; μ] := sum_dist_mul_log_comp _ _ _ m123
    have s23 : ∑ y, Q y * log (dist μ (copyBase X) y.2.2) = -H[pair (X 2) (X 3) ; μ] :=
      sum_dist_mul_log_comp _ _ _ m23
    rw [sum_congr rfl fun y _ => hl y, sum_sub_distrib, sum_add_distrib, s023, s123, s23]
    ring
  -- `E_p̃ log p̂` in terms of the entropies of `p`, (15.115)–(15.123)
  have eP : ∑ y, Q y * log (pHat μ X y) = -H[pair (X 0) (X 2) ; μ] - H[pair (X 0) (X 3) ; μ] -
      H[pair (X 1) (X 2) ; μ] - H[pair (X 1) (X 3) ; μ] + H[X 0 ; μ] + H[X 1 ; μ] +
      H[X 2 ; μ] + H[X 3 ; μ] := by
    have hl : ∀ y, Q y * log (pHat μ X y) =
        Q y * log (dist μ (pair (X 0) (X 2)) (y.1, y.2.2.1)) +
        Q y * log (dist μ (pair (X 0) (X 3)) (y.1, y.2.2.2)) +
        Q y * log (dist μ (pair (X 1) (X 2)) (y.2.1, y.2.2.1)) +
        Q y * log (dist μ (pair (X 1) (X 3)) (y.2.1, y.2.2.2)) -
        Q y * log (dist μ (X 0) y.1) - Q y * log (dist μ (X 1) y.2.1) -
        Q y * log (dist μ (X 2) y.2.2.1) - Q y * log (dist μ (X 3) y.2.2.2) := fun y => by
      by_cases hy : Q y = 0
      · simp [hy]
      have p02 : 0 < dist μ (pair (X 0) (X 2)) (y.1, y.2.2.1) := pos_of_dist_comp hν _ _ m02 hy
      have p03 : 0 < dist μ (pair (X 0) (X 3)) (y.1, y.2.2.2) := pos_of_dist_comp hν _ _ m03 hy
      have p12 : 0 < dist μ (pair (X 1) (X 2)) (y.2.1, y.2.2.1) :=
        pos_of_dist_comp hν _ _ m12 hy
      have p13 : 0 < dist μ (pair (X 1) (X 3)) (y.2.1, y.2.2.2) :=
        pos_of_dist_comp hν _ _ m13 hy
      have p0 : 0 < dist μ (X 0) y.1 := pos_of_dist_comp hν _ _ m0 hy
      have p1 : 0 < dist μ (X 1) y.2.1 := pos_of_dist_comp hν _ _ m1 hy
      have p2 : 0 < dist μ (X 2) y.2.2.1 := pos_of_dist_comp hν _ _ m2 hy
      have p3 : 0 < dist μ (X 3) y.2.2.2 := pos_of_dist_comp hν _ _ m3 hy
      rw [pHat, log_div (mul_pos (mul_pos (mul_pos p02 p03) p12) p13).ne'
          (mul_pos (mul_pos (mul_pos p0 p1) p2) p3).ne',
        log_mul (mul_pos (mul_pos p02 p03) p12).ne' p13.ne',
        log_mul (mul_pos p02 p03).ne' p12.ne', log_mul p02.ne' p03.ne',
        log_mul (mul_pos (mul_pos p0 p1) p2).ne' p3.ne', log_mul (mul_pos p0 p1).ne' p2.ne',
        log_mul p0.ne' p1.ne']
      ring
    rw [sum_congr rfl fun y _ => hl y]
    simp only [sum_add_distrib, sum_sub_distrib]
    rw [sum_dist_mul_log_comp _ _ _ m02, sum_dist_mul_log_comp _ _ _ m03,
      sum_dist_mul_log_comp _ _ _ m12, sum_dist_mul_log_comp _ _ _ m13,
      sum_dist_mul_log_comp _ _ _ m0, sum_dist_mul_log_comp _ _ _ m1,
      sum_dist_mul_log_comp _ _ _ m2, sum_dist_mul_log_comp _ _ _ m3]
    simp only [entropyRV]
    ring
  -- Gibbs, (15.124)–(15.125), with `p̂` a sub-probability
  have hpos : ∀ y, Q y ≠ 0 → 0 < pHat μ X y := fun y hy =>
    div_pos (mul_pos (mul_pos (mul_pos (pos_of_dist_comp hν _ _ m02 hy)
      (pos_of_dist_comp hν _ _ m03 hy)) (pos_of_dist_comp hν _ _ m12 hy))
        (pos_of_dist_comp hν _ _ m13 hy))
      (mul_pos (mul_pos (mul_pos (pos_of_dist_comp hν _ _ m0 hy)
        (pos_of_dist_comp hν _ _ m1 hy)) (pos_of_dist_comp hν _ _ m2 hy))
          (pos_of_dist_comp hν _ _ m3 hy))
  have gibbs := sum_mul_log_le_of_sum_le_one (hν.dist (copyTilde X)) (pHat_nonneg hμ)
    (sum_pHat_le_one hμ hI hC) hpos
  rw [mutualInfo_eq_add_sub hμ, condMutualInfo_eq hμ, condMutualInfo_eq hμ]
  linarith

end Constrained

/-! ### The constrained inequality in the entropy space -/

/-- The inequality (15.113) as the linear functional
`I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂) - I(X₃; X₄) ≥ 0`. -/
def zyConstrainedFunctional : EntropySpace (Fin 4) →ₗ[ℝ] ℝ :=
  condInfoFunctional {2} {3} {0} + condInfoFunctional {2} {3} {1} - condInfoFunctional {2} {3} ∅

/-- The coefficient vector of (15.113). -/
def zyConstrainedCoeff : EntropySpace (Fin 4) := canonicalForm zyConstrainedFunctional

/-- The constraints (15.112), `I(X₁; X₂) = I(X₁; X₂ | X₃) = 0`. -/
def zyConstraint : Set (EntropySpace (Fin 4)) :=
  {h | condInfo h.extend {0} {1} ∅ = 0 ∧ condInfo h.extend {0} {1} {2} = 0}

/-- **Theorem 15.14**, on `Γ*₄`: (15.113) always holds under the constraints (15.112). -/
theorem ineqAlwaysHolds_zyConstrainedCoeff : IneqAlwaysHolds zyConstrainedCoeff zyConstraint := by
  rintro h ⟨⟨Ω, _, A, _, μ, X, hμ, rfl⟩, hc⟩
  simp only [zyConstraint, Set.mem_ofPred_eq, extend_entropyVector hμ] at hc
  rw [zyConstrainedCoeff, infoExpr_canonicalForm]
  simp only [zyConstrainedFunctional, LinearMap.sub_apply, LinearMap.add_apply,
    condInfoFunctional_apply, extend_entropyVector hμ]
  have s := rvEquiv_blockRV_singleton X
  have := zhangYeung_constrained hμ (by rw [mutualInfo_eq_condInfo hμ (s 0) (s 1)]; exact hc.1)
    (by rw [condMutualInfo_eq_condInfo hμ (s 0) (s 1) (s 2)]; exact hc.2)
  rw [mutualInfo_eq_condInfo hμ (s 2) (s 3), condMutualInfo_eq_condInfo hμ (s 2) (s 3) (s 0),
    condMutualInfo_eq_condInfo hμ (s 2) (s 3) (s 1)] at this
  linarith

/-- (15.148): at `h̃(a)` the right side of (15.113) minus the left side is `-a`. -/
theorem zyConstrainedFunctional_zyPoint (a : ℝ) : zyConstrainedFunctional (zyPoint a) = -a := by
  simp only [zyConstrainedFunctional, LinearMap.sub_apply, LinearMap.add_apply,
    condInfoFunctional_apply, condInfo_zyPoint]
  have e : ((((zyNat ({0} ∪ {2}) + zyNat ({0} ∪ {3}) : ℕ) : ℤ) - zyNat ({0} ∪ {2} ∪ {3}) -
        zyNat {0} : ℤ) : ℝ) = 0 ∧
      ((((zyNat ({1} ∪ {2}) + zyNat ({1} ∪ {3}) : ℕ) : ℤ) - zyNat ({1} ∪ {2} ∪ {3}) -
        zyNat {1} : ℤ) : ℝ) = 0 ∧
      ((((zyNat (∅ ∪ {2}) + zyNat (∅ ∪ {3}) : ℕ) : ℤ) - zyNat (∅ ∪ {2} ∪ {3}) -
        zyNat ∅ : ℤ) : ℝ) = 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> norm_cast
  rw [e.1, e.2.1, e.2.2]
  ring

/-- **Theorem 15.16.** The constrained inequality (15.113) is a non-Shannon-type inequality under
the constraint that any subset of the 14 Shannon's information measures (15.94) vanishes; the
first two are those of (15.112), and the other twelve are those of (15.145). -/
theorem not_isShannonType_zyConstrainedCoeff (P : Finset (Fin 14)) :
    ¬IsShannonType zyConstrainedCoeff {h | ∀ k ∈ P,
      condInfo h.extend (zyMeasures k).1 (zyMeasures k).2.1 (zyMeasures k).2.2 = 0} := fun h => by
  have := h (zyPoint 1) ⟨zyPoint_mem_shannonRegion zero_le_one,
    fun k _ => condInfo_zyPoint_zyMeasures 1 k⟩
  rw [zyConstrainedCoeff, infoExpr_canonicalForm, zyConstrainedFunctional_zyPoint] at this
  norm_num at this

/-- **Theorem 15.15.** The constrained inequality of Theorem 15.14 is a non-Shannon-type
inequality. -/
theorem not_isShannonType_zyConstrainedCoeff_zyConstraint :
    ¬IsShannonType zyConstrainedCoeff zyConstraint := fun h => by
  have := h (zyPoint 1) ⟨zyPoint_mem_shannonRegion zero_le_one,
    condInfo_zyPoint_zyMeasures 1 0, condInfo_zyPoint_zyMeasures 1 1⟩
  rw [zyConstrainedCoeff, infoExpr_canonicalForm, zyConstrainedFunctional_zyPoint] at this
  norm_num at this

end InfoTheory
