/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Achievability

/-!
# The rate distortion theorem

For an i.i.d. source with a bounded distortion measure, the rate distortion region is
`{(R, D) | D ≥ D_min, R ≥ R^(I)(D)}`, and the rate distortion function equals the information rate
distortion function: `R(D) = R^(I)(D)`.

## Main statements

* `isClosed_epigraph_infoRD`: the set `{(R, D) | D ≥ D_min, R ≥ R^(I)(D)}` is closed.
* `rdRegion_eq`: the rate distortion region.
* `rateDistortion_eq_infoRD`: **Theorem 10.2.1**, `R(D) = R^(I)(D)`.
* `distortionRate_eq`: the distortion rate function `D(R) = min {D ≥ D_min | R^(I)(D) ≤ R}`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 10.2.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty β] {p : α → ℝ} {d : α → β → ℝ}

/-- The set `{(R, D) | D ≥ D_min, R ≥ R^(I)(D)}` is closed. -/
theorem isClosed_epigraph_infoRD (hp : IsPMF p) :
    IsClosed {z : ℝ × ℝ | minDistortion p d ≤ z.2 ∧ infoRD p d z.2 ≤ z.1} := by
  refine IsSeqClosed.isClosed fun x z hx hlim => ⟨?_, ?_⟩
  · exact ge_of_tendsto ((continuous_snd.tendsto z).comp hlim)
      (Eventually.of_forall fun k => (hx k).1)
  · exact infoRD_le_of_tendsto hp (fun k => (hx k).1) (fun k => (hx k).2)
      ((continuous_snd.tendsto z).comp hlim) ((continuous_fst.tendsto z).comp hlim)

/-- **The rate distortion region.** For a bounded distortion measure, `(R, D)` is in the rate
distortion region iff `D ≥ D_min` and `R ≥ R^(I)(D)`. -/
theorem rdRegion_eq (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) :
    rdRegion p d = {z : ℝ × ℝ | minDistortion p d ≤ z.2 ∧ infoRD p d z.2 ≤ z.1} := by
  refine Set.Subset.antisymm ?_ fun z hz => ?_
  · refine closure_minimal (fun z hz => ?_) (isClosed_epigraph_infoRD hp)
    exact ⟨IsAchievableRD.minDistortion_le hp hz, IsAchievableRD.infoRD_le hp hz⟩
  · -- `(R + 1/(k+1), D)` is achievable and tends to `(R, D)`.
    refine mem_closure_of_tendsto (b := atTop) (f := fun k : ℕ => (z.1 + 1 / (k + 1), z.2)) ?_
      (Eventually.of_forall fun k => ?_)
    · have h := (tendsto_const_nhds (x := z.1)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [add_zero] at h
      exact h.prodMk_nhds tendsto_const_nhds
    · have : (0 : ℝ) < 1 / (k + 1) := by positivity
      exact isAchievableRD_of_infoRD_lt hp hd hz.1 (by linarith [hz.2])

/-- **Theorem 10.2.1 (the rate distortion theorem).** For an i.i.d. source and a bounded distortion
measure, the rate distortion function equals the information rate distortion function:
`R(D) = R^(I)(D) = min_{p(x̂|x) : E d(X, X̂) ≤ D} I(X; X̂)`. (For `D < D_min` no rate achieves `D`
and both sides are `0` by convention.) -/
theorem rateDistortion_eq_infoRD (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) (D : ℝ) :
    rateDistortion p d D = infoRD p d D := by
  rw [rateDistortion, rdRegion_eq hp hd]
  by_cases hD : minDistortion p d ≤ D
  · simp only [Set.mem_ofPred_eq, hD, true_and]
    exact csInf_Ici
  · simp only [Set.mem_ofPred_eq, hD, false_and, Set.ofPred_false, Real.sInf_empty]
    have hempty : {I | ∃ q : α → β → ℝ, IsChannel q ∧ expDistortion p q d ≤ D ∧
        mutualInfoOf p q = I} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨q, hq, hqD, _⟩ =>
        hD ((minDistortion_le_expDistortion hp hq d).trans hqD)
    rw [infoRD, hempty, Real.sInf_empty]

/-- The distortion rate function: `D(R) = inf {D ≥ D_min | R^(I)(D) ≤ R}`. -/
theorem distortionRate_eq (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) (R : ℝ) :
    distortionRate p d R = sInf {D | minDistortion p d ≤ D ∧ infoRD p d D ≤ R} := by
  rw [distortionRate, rdRegion_eq hp hd]
  rfl

end InfoTheory
