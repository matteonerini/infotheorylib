/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Investment.AlmostSure
public import Mathlib.Probability.Density

/-!
# Competitive optimality of the log-optimal portfolio

The log-optimal investor need not be ahead of a competitor with high probability, but with a fair
randomization of the initial wealth, the competitor is ahead with probability at most `1/2`
(Theorem 16.6.1). The log-optimal investor exchanges the initial wealth for a wealth `U*` uniform
on `[0, 2]`, and the competitor for any fair `V ≥ 0` with `E V = 1`. Since `W = V S/S*` has
`E W ≤ 1` by the Kuhn–Tucker conditions, and `Pr(W ≥ U*) = E min(W, 2)/2 ≤ E W/2`, the competitor
wins with probability at most `1/2`, (16.79)–(16.90).

## Main statements

* `measure_le_of_isUniform`: if `U` is uniform on `[0, 2]` and independent of `W ≥ 0`, then
  `Pr(U ≤ W) ≤ E W / 2`, (16.83)–(16.89).
* `competitive_optimality`: **Theorem 16.6.1 (Competitive optimality)**,
  `Pr(V S ≥ U* S*) ≤ 1/2`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 16.6
-/

open Real Finset Filter Topology MeasureTheory ProbabilityTheory

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- For `U` uniform on `[0, 2]`, `Pr(U ≤ r) ≤ r/2`. -/
lemma map_Iic_le_of_isUniform {U : Ω → ℝ} (hU : pdf.IsUniform U (Set.Icc 0 2) P) (r : ℝ) :
    P.map U (Set.Iic r) ≤ ENNReal.ofReal (r / 2) := by
  rw [hU.map_eq, cond_apply measurableSet_Icc, Real.volume_Icc]
  have hsub : Set.Icc (0 : ℝ) 2 ∩ Set.Iic r ⊆ Set.Icc 0 (max r 0) := fun u hu =>
    ⟨hu.1.1, le_max_of_le_left hu.2⟩
  calc (ENNReal.ofReal (2 - 0))⁻¹ * volume (Set.Icc (0 : ℝ) 2 ∩ Set.Iic r)
      ≤ (ENNReal.ofReal 2)⁻¹ * volume (Set.Icc 0 (max r 0)) := by
        rw [sub_zero]
        gcongr
    _ = ENNReal.ofReal (max r 0 / 2) := by
        rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_div_of_pos two_pos, ENNReal.div_eq_inv_mul]
    _ = ENNReal.ofReal (r / 2) := by
        rcases le_total r 0 with h | h
        · rw [max_eq_right h, zero_div, ENNReal.ofReal_zero,
            ENNReal.ofReal_of_nonpos (by linarith)]
        · rw [max_eq_left h]

/-- **(16.83)–(16.89)** If `U` is uniform on `[0, 2]` and independent of `W ≥ 0`, then
`Pr(U ≤ W) ≤ E W / 2`. -/
theorem measure_le_of_isUniform {U W : Ω → ℝ} (hU : pdf.IsUniform U (Set.Icc 0 2) P)
    (hUm : Measurable U) (hWm : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (hWi : Integrable W P)
    (hind : IndepFun U W P) :
    P {ω | U ω ≤ W ω} ≤ ENNReal.ofReal ((∫ ω, W ω ∂P) / 2) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hpair : Measurable fun ω => (U ω, W ω) := hUm.prodMk hWm
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hUm.aemeasurable hWm.aemeasurable).1 hind
  calc P {ω | U ω ≤ W ω} = P.map (fun ω => (U ω, W ω)) {p : ℝ × ℝ | p.1 ≤ p.2} := by
        rw [Measure.map_apply hpair hs]
        rfl
    _ = ∫⁻ w, P.map U (Set.Iic w) ∂(P.map W) := by
        rw [hmap, Measure.prod_apply_symm hs]
        rfl
    _ ≤ ∫⁻ w, ENNReal.ofReal (w / 2) ∂(P.map W) :=
        lintegral_mono fun w => map_Iic_le_of_isUniform hU w
    _ = ∫⁻ ω, ENNReal.ofReal (W ω / 2) ∂P :=
        lintegral_map (ENNReal.measurable_ofReal.comp (measurable_id.div_const 2)) hWm
    _ = ENNReal.ofReal ((∫ ω, W ω ∂P) / 2) := by
        rw [← integral_div, ofReal_integral_eq_lintegral_ofReal (hWi.div_const 2)
          (Eventually.of_forall fun ω => div_nonneg (hW0 ω) zero_le_two)]

variable {m : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {F : ι → ℝ} {x : ι → Fin m → ℝ}

/-- **Theorem 16.6.1 (Competitive optimality), (16.79)–(16.90).** Let the market outcome `Y` have
law `F`, let `S* = b*ᵗx(Y)` be the wealth relative of the log-optimal portfolio and `S = bᵗx(Y)`
that of any portfolio. Let `U*` be uniform on `[0, 2]` and `V ≥ 0` with `E V = 1`, with `V`
independent of `Y` and `U*` independent of `(V, Y)`. Then `Pr(V S ≥ U* S*) ≤ 1/2`. -/
theorem competitive_optimality (hF : IsPMF F) (hx : IsPosMarket x) {bs : Fin m → ℝ}
    (hbs : IsLogOptimal F x bs) {b : Fin m → ℝ} (hb : IsPMF b) {Y : Ω → ι} {U V : Ω → ℝ}
    (hY : Measurable Y) (hlaw : ∀ k, P.real (Y ⁻¹' {k}) = F k) (hUm : Measurable U)
    (hU : pdf.IsUniform U (Set.Icc 0 2) P) (hVm : Measurable V) (hV0 : ∀ ω, 0 ≤ V ω)
    (hVi : Integrable V P) (hV1 : ∫ ω, V ω ∂P = 1) (hVY : IndepFun V Y P)
    (hUVY : IndepFun U (fun ω => (V ω, Y ω)) P) :
    P {ω | U ω * wealthRel bs (x (Y ω)) ≤ V ω * wealthRel b (x (Y ω))} ≤ 1 / 2 := by
  set g : ι → ℝ := fun k => wealthRel b (x k) / wealthRel bs (x k)
  have hg0 : ∀ k, 0 ≤ g k := fun k =>
    (div_pos (wealthRel_pos hb (hx k)) (wealthRel_pos hbs.1 (hx k))).le
  set W : Ω → ℝ := fun ω => V ω * g (Y ω)
  have hgm : Measurable g := measurable_of_countable g
  have hWm : Measurable W := hVm.mul (hgm.comp hY)
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => mul_nonneg (hV0 ω) (hg0 _)
  -- `E W = E V · E(S/S*) ≤ 1`, (16.82).
  have hgY : ∫ ω, g (Y ω) ∂P ≤ 1 := by
    rw [integral_comp_of_finite hY g]
    simp only [hlaw]
    have := hbs.sum_ratio_le hF.nonneg hx hb
    rwa [hF.sum_eq_one] at this
  have hWint : ∫ ω, W ω ∂P ≤ 1 := by
    have h := (hVY.comp measurable_id hgm).integral_mul_eq_mul_integral
      hVm.aestronglyMeasurable (hgm.comp hY).aestronglyMeasurable
    simp only [Function.id_comp] at h
    have e : ∫ ω, W ω ∂P = ∫ ω, (V * (g ∘ Y)) ω ∂P := rfl
    rw [e, h, hV1, one_mul]
    exact hgY
  have hWi : Integrable W P := by
    refine (hVi.mul_const (∑ k, g k)).mono' hWm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 ω)]
    exact mul_le_mul_of_nonneg_left (single_le_sum (fun k _ => hg0 k) (mem_univ (Y ω))) (hV0 ω)
  have hind : IndepFun U W P :=
    hUVY.comp measurable_id ((measurable_fst.mul (hgm.comp measurable_snd)))
  have hset : {ω | U ω * wealthRel bs (x (Y ω)) ≤ V ω * wealthRel b (x (Y ω))} =
      {ω | U ω ≤ W ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, W, g, mul_div_assoc']
    rw [le_div_iff₀ (wealthRel_pos hbs.1 (hx _))]
  rw [hset]
  calc P {ω | U ω ≤ W ω} ≤ ENNReal.ofReal ((∫ ω, W ω ∂P) / 2) :=
        measure_le_of_isUniform hU hUm hWm hW0 hWi hind
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal (by linarith)
    _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos two_pos]; simp

end InfoTheory
