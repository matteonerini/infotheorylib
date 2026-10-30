/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The weak law of large numbers for product measures

If `x₁, …, xₙ` are drawn i.i.d. from a probability measure `ρ` and `V` is integrable, the sample
mean `(1/n) ∑ᵢ V(xᵢ)` is close to `E V` with probability tending to `1`. This is the weak law of
large numbers stated on the product measures `ρⁿ`; we deduce it from the strong law applied to the
infinite product measure.

## Main statements

* `map_infinitePi_fin`: the first `n` coordinates of an i.i.d. sequence have law `ρⁿ`.
* `tendsto_pi_measure_abs_mean_sub_ge`: `ρⁿ {x | ε ≤ |(1/n) ∑ᵢ V(xᵢ) - E V|} → 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace InfoTheory

variable {α : Type*} [MeasurableSpace α]

/-- The first `n` coordinates of an i.i.d. sequence have the product law. -/
lemma map_infinitePi_fin (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun ω (i : Fin n) => ω i) =
      Measure.pi fun _ : Fin n => ν := by
  have hind : iIndepFun (fun i (ω : ℕ → α) => ω i) (Measure.infinitePi fun _ : ℕ => ν) :=
    iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  have hind' : iIndepFun (fun (i : Fin n) (ω : ℕ → α) => ω i)
      (Measure.infinitePi fun _ : ℕ => ν) :=
    hind.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun i => (measurable_pi_apply _).aemeasurable).1 hind']
  congr 1
  funext i
  exact Measure.infinitePi_map_eval _ _

/-- **The weak law of large numbers.** For i.i.d. draws `x₁, …, xₙ ∼ ρ` and an integrable `V`,
`Pr{|(1/n) ∑ᵢ V(xᵢ) - E V| ≥ ε} → 0`. -/
theorem tendsto_pi_measure_abs_mean_sub_ge (ρ : Measure α) [IsProbabilityMeasure ρ] {V : α → ℝ}
    (hV : Measurable V) (hint : Integrable V ρ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n => ρ)
      {x | ε ≤ |(n : ℝ)⁻¹ * ∑ i, V (x i) - ∫ a, V a ∂ρ|}) atTop (𝓝 0) := by
  set P := Measure.infinitePi fun _ : ℕ => ρ
  set Y : ℕ → (ℕ → α) → ℝ := fun i ω => V (ω i)
  have hY : ∀ i, Measurable (Y i) := fun i => hV.comp (measurable_pi_apply i)
  have hind : iIndepFun (fun i (ω : ℕ → α) => ω i) P :=
    iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  have hlaw : ∀ i, P.map (fun ω => ω i) = ρ := fun i => Measure.infinitePi_map_eval _ i
  have hYint : Integrable (Y 0) P :=
    (integrable_map_measure hV.aestronglyMeasurable (measurable_pi_apply 0).aemeasurable).1
      (by rw [hlaw 0]; exact hint)
  have hYmean : ∫ ω, Y 0 ω ∂P = ∫ a, V a ∂ρ := by
    rw [← hlaw 0, integral_map (measurable_pi_apply 0).aemeasurable hV.aestronglyMeasurable]
  have hindep' : Pairwise fun i j => Y i ⟂ᵢ[P] Y j := fun i j hij =>
    (hind.indepFun hij).comp hV hV
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    (⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [hlaw i, hlaw 0]⟩ : IdentDistrib (fun ω : ℕ → α => ω i) (fun ω => ω 0) P P).comp hV
  have hslln := strong_law_ae Y hYint hindep' hident
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ range n, Y i ω) P :=
    fun n => (Measurable.const_smul (Finset.measurable_sum (range n) fun i _ => hY i)
      ((n : ℝ)⁻¹)).aestronglyMeasurable
  have h := tendstoInMeasure_of_tendsto_ae hmeas hslln (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε)
  refine h.congr' (Eventually.of_forall fun n => ?_)
  have hS : MeasurableSet {x : Fin n → α | ε ≤ |(n : ℝ)⁻¹ * ∑ i, V (x i) - ∫ a, V a ∂ρ|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp
      (((Finset.measurable_sum _ fun i _ => hV.comp (measurable_pi_apply i)).const_mul _).sub_const
        _))
  have hproj : Measurable fun (ω : ℕ → α) (i : Fin n) => ω i :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  dsimp only
  rw [← map_infinitePi_fin ρ n, Measure.map_apply hproj hS]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, edist_dist, Real.dist_eq, hYmean, smul_eq_mul,
    ENNReal.ofReal_le_ofReal_iff (abs_nonneg _), Y]
  rw [← Fin.sum_univ_eq_sum_range (fun i => V (ω i)) n]

end InfoTheory
