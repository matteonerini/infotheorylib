/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Water-filling

Given noise levels `N₁, …, N_k > 0` and a total power `P`, the allocation of powers `Pᵢ ≥ 0` with
`∑ᵢ Pᵢ ≤ P` maximizing `∑ᵢ log (1 + Pᵢ/Nᵢ)` is `Pᵢ = (ν - Nᵢ)⁺`, where the water level `ν` is chosen
so that `∑ᵢ (ν - Nᵢ)⁺ = P`: power is poured into the channels with the lowest noise, as water into
a vessel.

## Main definitions

* `waterFill N ν i`: the allocation `(ν - Nᵢ)⁺`, (9.76).

## Main statements

* `exists_waterLevel`: (9.77), there is a water level `ν ≥ minᵢ Nᵢ` with `∑ᵢ (ν - Nᵢ)⁺ = P`.
* `sum_log_le_waterFill`: (9.73)–(9.78), water-filling maximizes `∑ᵢ log (1 + Pᵢ/Nᵢ)`.

## Implementation notes

The book derives the solution with Lagrange multipliers and the Kuhn–Tucker conditions. We verify
it directly with the tangent line bound `log x ≤ log a + (x - a)/a` of the concave logarithm at
`a = max(ν, Nᵢ)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.4
-/

@[expose] public section

open Real Finset

namespace InfoTheory

variable {ι : Type*}

/-- **(9.76)** The water-filling allocation `Pᵢ = (ν - Nᵢ)⁺` at water level `ν`. -/
noncomputable def waterFill (N : ι → ℝ) (ν : ℝ) (i : ι) : ℝ := max (ν - N i) 0

lemma waterFill_nonneg (N : ι → ℝ) (ν : ℝ) (i : ι) : 0 ≤ waterFill N ν i := le_max_right _ _

/-- `Nᵢ + (ν - Nᵢ)⁺ = max(ν, Nᵢ)`. -/
lemma add_waterFill (N : ι → ℝ) (ν : ℝ) (i : ι) : N i + waterFill N ν i = max ν (N i) := by
  unfold waterFill
  rcases le_total ν (N i) with h | h
  · rw [max_eq_right (by linarith), max_eq_right h, add_zero]
  · rw [max_eq_left (by linarith), max_eq_left h]
    ring

variable [Fintype ι]

lemma continuous_sum_waterFill (N : ι → ℝ) : Continuous fun ν => ∑ i, waterFill N ν i :=
  continuous_finsetSum _ fun _ _ => (continuous_id.sub continuous_const).max continuous_const

/-- **(9.77)** For every power `P ≥ 0` there is a water level `ν ≥ minᵢ Nᵢ` with
`∑ᵢ (ν - Nᵢ)⁺ = P`. -/
theorem exists_waterLevel [Nonempty ι] (N : ι → ℝ) {P : ℝ} (hP : 0 ≤ P) :
    ∃ ν, (∀ i, ν ≤ N i → waterFill N ν i = 0) ∧ (∃ i, N i ≤ ν) ∧ ∑ i, waterFill N ν i = P := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image univ N univ_nonempty
  set a := N i₀
  set b := N i₀ + P
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hfa : ∑ i, waterFill N a i = 0 :=
    sum_eq_zero fun i _ => max_eq_right (by linarith [hi₀ i (mem_univ i)])
  have hfb : P ≤ ∑ i, waterFill N b i := by
    have h1 : P ≤ waterFill N b i₀ := by
      simp only [waterFill, b]
      exact le_max_of_le_left (by linarith)
    exact h1.trans (single_le_sum (fun i _ => waterFill_nonneg N b i) (mem_univ i₀))
  obtain ⟨ν, hν, hνP⟩ := intermediate_value_Icc hab (continuous_sum_waterFill N).continuousOn
    ⟨hfa ▸ hP, hfb⟩
  refine ⟨ν, fun i hi => max_eq_right (by linarith), ⟨i₀, hν.1⟩, hνP⟩

/-- `log (1 + x/N) ≤ log (1 + a/N) + (x - a)/(N + a)`: the tangent line bound for the concave
function `x ↦ log (N + x)`. -/
lemma log_one_add_div_le {N x a : ℝ} (hN : 0 < N) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    log (1 + x / N) ≤ log (1 + a / N) + (x - a) / (N + a) := by
  have hNa : 0 < N + a := by linarith
  have hNx : 0 < N + x := by linarith
  have e1 : 1 + x / N = (N + x) / N := by field_simp
  have e2 : 1 + a / N = (N + a) / N := by field_simp
  rw [e1, e2, log_div hNx.ne' hN.ne', log_div hNa.ne' hN.ne']
  have h := log_le_sub_one_of_pos (div_pos hNx hNa)
  rw [log_div hNx.ne' hNa.ne'] at h
  have e3 : (N + x) / (N + a) - 1 = (x - a) / (N + a) := by field_simp; ring
  linarith

/-- **(9.73)–(9.78) Water-filling.** For noise levels `Nᵢ > 0`, a water level `ν > 0` and powers
`Pᵢ ≥ 0` with `∑ᵢ Pᵢ ≤ ∑ᵢ (ν - Nᵢ)⁺`, the allocation `(ν - Nᵢ)⁺` is better:
`∑ᵢ log (1 + Pᵢ/Nᵢ) ≤ ∑ᵢ log (1 + (ν - Nᵢ)⁺/Nᵢ)`. -/
theorem sum_log_le_waterFill {N : ι → ℝ} (hN : ∀ i, 0 < N i) {ν : ℝ} (hν : 0 < ν)
    {P : ι → ℝ} (hP : ∀ i, 0 ≤ P i) (hsum : ∑ i, P i ≤ ∑ i, waterFill N ν i) :
    ∑ i, log (1 + P i / N i) ≤ ∑ i, log (1 + waterFill N ν i / N i) := by
  -- Each term is at most the water-filling term plus `(Pᵢ - (ν - Nᵢ)⁺)/ν`.
  have hterm : ∀ i, log (1 + P i / N i) ≤
      log (1 + waterFill N ν i / N i) + (P i - waterFill N ν i) / ν := by
    intro i
    refine (log_one_add_div_le (hN i) (hP i) (waterFill_nonneg N ν i)).trans ?_
    rw [add_waterFill]
    refine add_le_add le_rfl ?_
    rcases le_total ν (N i) with h | h
    · rw [max_eq_right h, show waterFill N ν i = 0 from max_eq_right (by linarith), sub_zero]
      exact div_le_div_of_nonneg_left (hP i) hν h
    · rw [max_eq_left h]
  calc ∑ i, log (1 + P i / N i)
      ≤ ∑ i, (log (1 + waterFill N ν i / N i) + (P i - waterFill N ν i) / ν) :=
        sum_le_sum fun i _ => hterm i
    _ = ∑ i, log (1 + waterFill N ν i / N i) + (∑ i, P i - ∑ i, waterFill N ν i) / ν := by
        rw [sum_add_distrib, ← Finset.sum_div, sum_sub_distrib]
    _ ≤ ∑ i, log (1 + waterFill N ν i / N i) := by
        have : (∑ i, P i - ∑ i, waterFill N ν i) / ν ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hν.le
        linarith

end InfoTheory
