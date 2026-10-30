/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Probability.CDF
public import InfoTheoryLib.SourceCoding.ShannonFanoEliasBlock

/-!
# Arithmetic coding

Arithmetic coding represents a sequence `x₁ ⋯ xₙ` by a subinterval of `[0, 1)`: starting from
`[0, 1)`, each symbol `a` narrows the current interval `[l, l + w)` to
`[l + w F(a⁻), l + w F(a⁻) + w p(a))`, where `F(a⁻) = ∑_{b < a} p(b)`. For an i.i.d. source the
final interval is `[F(xⁿ⁻), F(xⁿ⁻) + p(xⁿ))`, where `F(xⁿ⁻)` is the probability of the strings
below `xⁿ` in lexicographic order: it is the interval of the Shannon–Fano–Elias code of the
block, computed one symbol at a time. The motivation is the probability integral transform:
`F(Y)` is uniform on `[0, 1]` for a continuous distribution function `F` (Lemma 13.3.1).

## Main definitions

* `arithStep q I a`: narrow the interval `I = (l, w)` to the subinterval of the symbol `a`.
* `arithInterval q xs`: the interval of the sequence `xs`.

## Main statements

* `map_cdf_eq_uniform`: **Lemma 13.3.1**, the probability integral transform.
* `arithInterval_ofFn`: **(13.53)–(13.59)**, the arithmetic coding interval of `xⁿ` is
  `[F(xⁿ⁻), F(xⁿ⁻) + p(xⁿ))`.
* `arithInterval_append_subset`: the intervals are nested as the sequence grows.
* `eq_of_mem_arithInterval`: the intervals of distinct sequences of the same length are
  disjoint, so a point of the interval identifies the sequence.

## Implementation notes

As in the book, we use exact real arithmetic. The rescaling that keeps the computation in finite
precision, and the incremental output of bits, are not formalized. The prefix code obtained from
the final interval is `blockSfeCode` (`SourceCoding.ShannonFanoEliasBlock`), of length
`⌈log 1/p(xⁿ)⌉ + 1` bits.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 13.3
-/

open Real Finset MeasureTheory

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The probability integral transform -/

/-- **Lemma 13.3.1 (probability integral transform).** If the distribution function `F` of a
real random variable `Y` is continuous, then `U = F(Y)` is uniformly distributed on `[0, 1]`. -/
theorem map_cdf_eq_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : Continuous (ProbabilityTheory.cdf μ)) :
    μ.map (ProbabilityTheory.cdf μ) = volume.restrict (Set.Icc 0 1) := by
  have hmeas : Measurable (ProbabilityTheory.cdf μ) := (ProbabilityTheory.monotone_cdf μ).measurable
  have : IsProbabilityMeasure (μ.map (ProbabilityTheory.cdf μ)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  refine Measure.ext_of_Iic _ _ fun u => ?_
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  set S := ProbabilityTheory.cdf μ ⁻¹' Set.Iic u
  rcases lt_or_ge u 0 with hu | hu
  · -- No point has `F(y) ≤ u < 0`.
    have hS : S = ∅ := Set.eq_empty_of_forall_notMem fun y hy =>
      absurd (hy.trans_lt hu) (not_lt.2 (ProbabilityTheory.cdf_nonneg μ y))
    have : Set.Iic u ∩ Set.Icc (0 : ℝ) 1 = ∅ := Set.eq_empty_of_forall_notMem fun y hy =>
      absurd (hy.1.trans_lt hu) (not_lt.2 hy.2.1)
    rw [hS, this, measure_empty, measure_empty]
  rcases le_or_gt 1 u with hu1 | hu1
  · -- Every point has `F(y) ≤ 1 ≤ u`.
    have hS : S = Set.univ :=
      Set.eq_univ_of_forall fun y => (ProbabilityTheory.cdf_le_one μ y).trans hu1
    have : Set.Iic u ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 :=
      Set.inter_eq_right.2 fun y hy => hy.2.trans hu1
    rw [hS, this, measure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have hvol : volume (Set.Iic u ∩ Set.Icc (0 : ℝ) 1) = ENNReal.ofReal u := by
    have : Set.Iic u ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 u := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, h2.trans hu1.le⟩
    rw [this, Real.volume_Icc, sub_zero]
  rw [hvol]
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- Then `u < F(y)` for all `y`, and `F(y) → 0` at `-∞` forces `u = 0`.
    have hu0 : u = 0 := by
      refine le_antisymm (ge_of_tendsto (ProbabilityTheory.tendsto_cdf_atBot μ) ?_) hu
      exact Filter.Eventually.of_forall fun y => le_of_lt (not_le.1 fun h =>
        (Set.eq_empty_iff_forall_notMem.1 hS) y h)
    rw [hS, measure_empty, hu0, ENNReal.ofReal_zero]
  -- `S = (-∞, s]` with `F(s) = u`.
  have hbdd : BddAbove S := by
    obtain ⟨b, hb⟩ := Filter.eventually_atTop.1
      ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (lt_mem_nhds hu1))
    refine ⟨b, fun y hy => le_of_not_gt fun hyb => ?_⟩
    exact absurd (hb y hyb.le) (not_lt.2 hy)
  have hclosed : IsClosed S := isClosed_Iic.preimage hF
  set s := sSup S
  have hs : s ∈ S := hclosed.csSup_mem hS hbdd
  have hSeq : S = Set.Iic s := by
    ext y
    exact ⟨fun hy => le_csSup hbdd hy, fun hy => ((ProbabilityTheory.monotone_cdf μ) hy).trans hs⟩
  have hFs : ProbabilityTheory.cdf μ s = u := by
    refine le_antisymm hs (le_of_not_gt fun hlt => ?_)
    -- By continuity, `F < u` slightly to the right of `s`.
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.continuous_iff.1 hF s (u - ProbabilityTheory.cdf μ s) (by linarith)
    have hmem : s + δ / 2 ∈ S := by
      have := hball (s + δ / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
      rw [Real.dist_eq] at this
      change ProbabilityTheory.cdf μ (s + δ / 2) ≤ u
      linarith [le_abs_self (ProbabilityTheory.cdf μ (s + δ / 2) - ProbabilityTheory.cdf μ s)]
    have := le_csSup hbdd hmem
    linarith
  rw [hSeq, ← ProbabilityTheory.ofReal_cdf, hFs]

/-! ### Arithmetic coding intervals -/

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- One step of arithmetic coding: the interval `[l, l + w)` is narrowed to the subinterval
`[l + w F(a⁻), l + w F(a⁻) + w p(a))` of the symbol `a`. An interval is a pair `(l, w)` of its
lower end and its width. -/
def arithStep (q : α → ℝ) (I : ℝ × ℝ) (a : α) : ℝ × ℝ := (I.1 + I.2 * cdfLT q a, I.2 * q a)

/-- The arithmetic coding interval of a sequence, computed one symbol at a time from `[0, 1)`. -/
def arithInterval (q : α → ℝ) (xs : List α) : ℝ × ℝ := xs.foldl (arithStep q) (0, 1)

omit [Fintype α] [LinearOrder α] in
lemma prod_filter_lt_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) (k : Fin n) :
    ∏ i ∈ univ.filter (· < k.castSucc), f i = ∏ i ∈ univ.filter (· < k), f i.castSucc := by
  rw [prod_filter, prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, not_lt.2 (Fin.castSucc_lt_last k).le, ite_false,
    mul_one]

omit [Fintype α] [LinearOrder α] in
lemma prod_filter_lt_last {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∏ i ∈ univ.filter (· < Fin.last n), f i = ∏ i : Fin n, f i.castSucc := by
  rw [prod_filter, Fin.prod_univ_castSucc]
  simp [Fin.castSucc_lt_last]

/-- For an i.i.d. source, `F((xⁿ a)⁻) = F(xⁿ⁻) + p(xⁿ) F(a⁻)`. -/
lemma cdfLT_lex_iid_snoc {q : α → ℝ} (hq : IsPMF q) {n : ℕ} (x : Fin n → α) (a : α) :
    cdfLT (iidPMF q (n + 1) ∘ ofLex) (toLex (Fin.snoc x a : Fin (n + 1) → α)) =
      cdfLT (iidPMF q n ∘ ofLex) (toLex x) + iidPMF q n x * cdfLT q a := by
  rw [cdfLT_lex_iid hq, cdfLT_lex_iid hq, Fin.sum_univ_castSucc]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [prod_filter_lt_castSucc]
    simp [Fin.snoc_castSucc]
  · rw [prod_filter_lt_last]
    simp [Fin.snoc_castSucc, Fin.snoc_last, iidPMF, cdfLT]

/-- **(13.53)–(13.59)** For an i.i.d. source, the arithmetic coding interval of `xⁿ` is
`[F(xⁿ⁻), F(xⁿ⁻) + p(xⁿ))`, where `F(xⁿ⁻) = ∑_{yⁿ < xⁿ} p(yⁿ)` in lexicographic order. -/
theorem arithInterval_ofFn {q : α → ℝ} (hq : IsPMF q) {n : ℕ} (x : Fin n → α) :
    arithInterval q (List.ofFn x) = (cdfLT (iidPMF q n ∘ ofLex) (toLex x), iidPMF q n x) := by
  induction n with
  | zero =>
    have : cdfLT (iidPMF q 0 ∘ ofLex) (toLex x) = 0 := by
      rw [cdfLT_lex_iid hq]
      simp
    simp [arithInterval, this, iidPMF]
  | succ n ih =>
    rw [← Fin.snoc_init_self x, List.ofFn_succ', List.concat_eq_append, arithInterval,
      List.foldl_append, ← arithInterval]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [show (fun i : Fin n => Fin.init x i) = Fin.init x from rfl, ih, List.foldl_cons,
      List.foldl_nil, arithStep, cdfLT_lex_iid_snoc hq, iidPMF_snoc]

/-- The arithmetic coding intervals are nested: the interval of `xs ++ [a]` lies in the interval
of `xs`. -/
theorem arithInterval_append_subset {q : α → ℝ} (hq : IsPMF q) (xs : List α) (a : α) :
    Set.Ico (arithInterval q (xs ++ [a])).1
        ((arithInterval q (xs ++ [a])).1 + (arithInterval q (xs ++ [a])).2) ⊆
      Set.Ico (arithInterval q xs).1 ((arithInterval q xs).1 + (arithInterval q xs).2) := by
  have hw : 0 ≤ (arithInterval q xs).2 := by
    rw [arithInterval]
    generalize hI : ((0 : ℝ), (1 : ℝ)) = I
    have hI2 : 0 ≤ I.2 := by rw [← hI]; norm_num
    clear hI
    induction xs generalizing I with
    | nil => exact hI2
    | cons b xs ih => exact ih _ (mul_nonneg hI2 (hq.nonneg b))
  rw [arithInterval, List.foldl_append, ← arithInterval, List.foldl_cons, List.foldl_nil,
    arithStep]
  set l := (arithInterval q xs).1
  set w := (arithInterval q xs).2
  refine Set.Ico_subset_Ico ?_ ?_
  · have := cdfLT_nonneg hq.nonneg a
    simp only
    nlinarith
  · have h1 := cdf_le_one hq a
    rw [cdf_eq_cdfLT_add] at h1
    simp only
    nlinarith

/-- **Decodability.** The arithmetic coding intervals of distinct sequences of the same length are
disjoint, so any point of the interval of `xⁿ` identifies `xⁿ`. -/
theorem eq_of_mem_arithInterval {q : α → ℝ} (hq : IsPMF q) {n : ℕ} {x y : Fin n → α} {u : ℝ}
    (hx : u ∈ Set.Ico (arithInterval q (List.ofFn x)).1
      ((arithInterval q (List.ofFn x)).1 + (arithInterval q (List.ofFn x)).2))
    (hy : u ∈ Set.Ico (arithInterval q (List.ofFn y)).1
      ((arithInterval q (List.ofFn y)).1 + (arithInterval q (List.ofFn y)).2)) : x = y := by
  rw [arithInterval_ofFn hq] at hx hy
  have hp : ∀ z, 0 ≤ (iidPMF q n ∘ ofLex) z := fun z => (iidPMF_isPMF hq n).nonneg _
  by_contra hne
  rcases lt_or_gt_of_ne (toLex.injective.ne hne) with h | h
  · have := cdf_le_cdfLT_of_lt hp h
    rw [cdf_eq_cdfLT_add] at this
    simp only [Function.comp_apply, ofLex_toLex] at this
    rw [Set.mem_Ico] at hx hy
    linarith [hx.2, hy.1]
  · have := cdf_le_cdfLT_of_lt hp h
    rw [cdf_eq_cdfLT_add] at this
    simp only [Function.comp_apply, ofLex_toLex] at this
    rw [Set.mem_Ico] at hx hy
    linarith [hx.1, hy.2]

end InfoTheory
