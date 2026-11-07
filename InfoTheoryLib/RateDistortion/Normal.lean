/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Basic

/-!
# Normal distortion measures and the shape of `R^(I)(D)`

A distortion measure is normal if every source symbol can be reproduced with zero distortion.
Subtracting from `d(x, x̂)` its minimum over `x̂` gives a normal distortion measure, and shifts
every expected distortion by the same constant `Δ = ∑ₓ p(x) min_x̂ d(x, x̂)`, so that
`R^(I)` only moves by `Δ`. The largest distortion of interest is `D_max = min_x̂ E d(X, x̂)`, the
distortion of the best constant reproduction: `R^(I)(D) = 0` for `D ≥ D_max`, `R^(I)(D) > 0` for
`D < D_max`, and `R^(I)` is strictly decreasing up to `D_max`.

## Main definitions

* `IsNormalDistortion d`: every `x` has some `x̂` with `d(x, x̂) = 0`.
* `normalizeDistortion d`: the normalization `d̃(x, x̂) = d(x, x̂) - min_x̂' d(x, x̂')`.
* `dMax p d`: the distortion `D_max = min_x̂ E d(X, x̂)` of the best constant reproduction.
* `squareErrorDistortion f g`: the square-error distortion measure.

## Main statements

* `expDistortion_normalizeDistortion`, `infoRD_normalizeDistortion`: (8.10)–(8.16) and (8.62).
* `infoRD_eq_zero_of_dMax_le`, `infoRD_le_entropy`: properties 3 and 4 of `R^(I)(D)`.
* `infoRD_pos`, `strictAntiOn_infoRD`, `expDistortion_eq_of_infoRD_eq`: Corollary 8.19.
* `sum_mul_hammingDistortion`: (8.7), the expected Hamming distortion is a probability of error.
* `sInf_mutualInfoOf_sub_mul_eq`: (9.57), the tangents to `R^(I)`.

## References

Numbers without a source refer to [yeung2008].

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], (10.4)
* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 8.1 to 8.3 and
  9.2.2
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β] {p : α → ℝ} {d : α → β → ℝ}

/-! ### Normal distortion measures -/

/-- **Definition 8.5.** A distortion measure is normal if every source symbol can be reproduced with
zero distortion, `c_x = min_x̂ d(x, x̂) = 0`, (8.8). -/
def IsNormalDistortion (d : α → β → ℝ) : Prop := ∀ x, ∃ y, d x y = 0

/-- **(8.9)** The normalization `d̃(x, x̂) = d(x, x̂) - c_x` of a distortion measure. -/
def normalizeDistortion (d : α → β → ℝ) : α → β → ℝ := fun x y => d x y - ⨅ y', d x y'

omit [Fintype α] [Fintype β] in
lemma normalizeDistortion_nonneg [Finite β] (d : α → β → ℝ) (x : α) (y : β) :
    0 ≤ normalizeDistortion d x y :=
  sub_nonneg.2 (ciInf_le_distortion d x y)

omit [Fintype α] [Fintype β] in
/-- The normalization of a distortion measure is normal. -/
lemma isNormalDistortion_normalizeDistortion [Finite β] [Nonempty β] (d : α → β → ℝ) :
    IsNormalDistortion (normalizeDistortion d) := fun x => by
  obtain ⟨y, hy⟩ := exists_eq_ciInf_of_finite (f := d x)
  exact ⟨y, by rw [normalizeDistortion, hy, sub_self]⟩

omit [Fintype α] [Fintype β] in
/-- A normal measure has `min_x̂ d(x, x̂) = 0` for every `x`. -/
lemma IsNormalDistortion.ciInf_eq_zero [Finite β] [Nonempty β] (hd : ∀ x y, 0 ≤ d x y)
    (h : IsNormalDistortion d) (x : α) : ⨅ y, d x y = 0 := by
  obtain ⟨y, hy⟩ := h x
  exact le_antisymm (hy ▸ ciInf_le_distortion d x y) (le_ciInf fun y' => hd x y')

omit [Fintype β] in
/-- A normal measure has `D_min = 0`. -/
lemma IsNormalDistortion.minDistortion_eq_zero [Finite β] [Nonempty β] (hd : ∀ x y, 0 ≤ d x y)
    (h : IsNormalDistortion d) : minDistortion p d = 0 := by
  simp [minDistortion, h.ciInf_eq_zero hd]

/-- **(8.10)–(8.16)** `E d(X, X̂) = E d̃(X, X̂) + Δ`, where `Δ = ∑ₓ p(x) c_x` is `D_min`. -/
theorem expDistortion_normalizeDistortion {q : α → β → ℝ} (hq : IsChannel q) :
    expDistortion p q (normalizeDistortion d) = expDistortion p q d - minDistortion p d := by
  simp only [expDistortion, normalizeDistortion, minDistortion, mul_sub, sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_mul, ← mul_sum, (hq x).sum_eq_one, mul_one]

/-- **(8.62)** Normalizing `d` shifts `R^(I)` by `Δ`: `R^(I)_d̃(D) = R^(I)_d(D + Δ)`. -/
theorem infoRD_normalizeDistortion (D : ℝ) :
    infoRD p (normalizeDistortion d) D = infoRD p d (D + minDistortion p d) := by
  unfold infoRD
  congr 1
  ext I
  refine exists_congr fun q => and_congr_right fun hq => ?_
  rw [expDistortion_normalizeDistortion hq, sub_le_iff_le_add]

/-- **Example 8.3.** The square-error distortion measure `d(x, x̂) = (x - x̂)²`, for symbols that
represent the real values `f x` and `g x̂`. -/
def squareErrorDistortion (f : α → ℝ) (g : β → ℝ) : α → β → ℝ := fun x y => (f x - g y) ^ 2

omit [Fintype α] [Fintype β] in
/-- The square-error distortion measure is normal when every source value can be reproduced. -/
lemma isNormalDistortion_squareErrorDistortion {f : α → ℝ} {g : β → ℝ}
    (h : ∀ x, ∃ y, g y = f x) : IsNormalDistortion (squareErrorDistortion f g) := fun x => by
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, by simp [squareErrorDistortion, hy]⟩

omit [Fintype α] in
/-- The Hamming distortion measure is normal. -/
lemma isNormalDistortion_hammingDistortion : IsNormalDistortion (hammingDistortion (α := α)) :=
  fun x => ⟨x, by simp [hammingDistortion]⟩

open Classical in
omit [Fintype α] in
/-- **(8.7), and (10.4) of [cover2006].** The expected Hamming distortion between `X` and an
estimate `X̂` is the probability of error `Pr{X ≠ X̂}`. -/
theorem sum_mul_hammingDistortion {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (X Y : Ω → α) :
    ∑ ω, μ ω * hammingDistortion (X ω) (Y ω) = prob μ (univ.filter fun ω => X ω ≠ Y ω) := by
  rw [prob, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : X ω = Y ω <;> simp [hammingDistortion, h]

/-! ### The largest distortion of interest -/

/-- **Definition 8.7.** `D_max = min_x̂ E d(X, x̂)`, the least expected distortion of a constant
reproduction, (8.17). -/
def dMax (p : α → ℝ) (d : α → β → ℝ) : ℝ := ⨅ y, ∑ x, p x * d x y

omit [Fintype β] in
lemma exists_dMax_eq [Finite β] [Nonempty β] (p : α → ℝ) (d : α → β → ℝ) :
    ∃ y, ∑ x, p x * d x y = dMax p d :=
  exists_eq_ciInf_of_finite

omit [Fintype β] in
lemma dMax_le [Finite β] (p : α → ℝ) (d : α → β → ℝ) (y : β) : dMax p d ≤ ∑ x, p x * d x y :=
  ciInf_le (Set.finite_range _).bddBelow y

omit [Fintype β] in
/-- `D_min ≤ D_max`. -/
lemma minDistortion_le_dMax [Finite β] [Nonempty β] (hp : IsPMF p) :
    minDistortion p d ≤ dMax p d := by
  obtain ⟨y, hy⟩ := exists_dMax_eq p d
  rw [← hy, minDistortion]
  exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ciInf_le_distortion d x y) (hp.nonneg x)

/-- **Theorem 8.18 (3).** `R^(I)(D) = 0` for `D ≥ D_max`, (8.76)–(8.79). -/
theorem infoRD_eq_zero_of_dMax_le [Nonempty β] (hp : IsPMF p) {D : ℝ} (hD : dMax p d ≤ D) :
    infoRD p d D = 0 := by
  obtain ⟨y, hy⟩ := exists_dMax_eq p d
  exact infoRD_eq_zero hp (hy ▸ hD)

/-- **Theorem 8.18 (4).** For a normal distortion measure, `R^(I)(0) ≤ H(X)`, (8.80)–(8.84). -/
theorem infoRD_le_entropy (hp : IsPMF p) (h : IsNormalDistortion d) :
    infoRD p d 0 ≤ entropy p := by
  choose f hf using h
  have hq := detChannel_isChannel f
  have hD : expDistortion p (detChannel f) d ≤ 0 := by
    rw [expDistortion_detChannel]
    simp [hf]
  refine (infoRD_le hp hq hD).trans ?_
  have hμ := jointOf_isPMF hp hq
  rw [mutualInfoOf, mutualInfo_eq_entropy_sub_condEntropy hμ, entropyRV, dist_jointOf_fst hq]
  linarith [condEntropy_nonneg hμ Prod.fst Prod.snd]

/-! ### Corollary 8.19 -/

/-- **Corollary 8.19, (8.85)–(8.94).** `R^(I)(D) > 0` for `D < D_max`: a test channel with
`I(X; X̂) = 0` makes `X̂` independent of `X`, so its expected distortion is at least `D_max`. -/
theorem infoRD_pos [Nonempty β] (hp : IsPMF p) {D : ℝ} (hD₀ : minDistortion p d ≤ D)
    (hD : D < dMax p d) : 0 < infoRD p d D := by
  refine (infoRD_nonneg hp D).lt_of_ne fun h => ?_
  obtain ⟨q, hq, hqD, hqI⟩ := exists_infoRD_eq hp hD₀
  have hμ := jointOf_isPMF hp hq
  have hind := (mutualInfo_eq_zero_iff hμ Prod.fst Prod.snd).1 (by rw [← mutualInfoOf, hqI, ← h])
  -- `p(x) q(x̂|x) = p(x) r(x̂)` with `r` the law of `X̂`.
  have hpq : ∀ x y, p x * q x y = p x * outDist p q y := fun x y => by
    have := hind x y
    rwa [dist_pair_fst_snd, dist_jointOf_fst hq, dist_jointOf_snd] at this
  have hE : expDistortion p q d = ∑ y, outDist p q y * ∑ x, p x * d x y := by
    rw [expDistortion, sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hpq]
    ring
  have hr := outDist_isPMF hp hq
  have hge : dMax p d ≤ expDistortion p q d := by
    rw [hE]
    calc dMax p d = ∑ y, outDist p q y * dMax p d := by rw [← sum_mul, hr.sum_eq_one, one_mul]
      _ ≤ _ := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (dMax_le p d y) (hr.nonneg y)
  linarith

/-- **Corollary 8.19.** `R^(I)(D)` is strictly decreasing for `D_min ≤ D ≤ D_max`. The book assumes
`R^(I)(0) > 0`; the proof does not need it. -/
theorem strictAntiOn_infoRD [Nonempty β] (hp : IsPMF p) :
    StrictAntiOn (infoRD p d) (Set.Icc (minDistortion p d) (dMax p d)) := by
  intro a ha b hb hab
  have hpos := infoRD_pos hp ha.1 (hab.trans_le hb.2)
  rcases hb.2.lt_or_eq with hb' | hb'
  · -- `b` is a convex combination of `a` and `D_max`.
    set t := (dMax p d - b) / (dMax p d - a) with ht
    have hda : 0 < dMax p d - a := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hda
    have ht1 : t < 1 := (div_lt_one hda).2 (by linarith)
    have hcomb : t * a + (1 - t) * dMax p d = b := by
      have h' : t * (dMax p d - a) = dMax p d - b := div_mul_cancel₀ _ hda.ne'
      linear_combination (-1 : ℝ) * h'
    have hconv : infoRD p d (t * a + (1 - t) * dMax p d) ≤
        t * infoRD p d a + (1 - t) * infoRD p d (dMax p d) := by
      have := (infoRD_convexOn (d := d) hp).2 ha.1 (minDistortion_le_dMax hp) ht0.le
        (show 0 ≤ 1 - t by linarith) (show t + (1 - t) = 1 by ring)
      simpa only [smul_eq_mul] using this
    rw [hcomb, infoRD_eq_zero_of_dMax_le hp le_rfl, mul_zero, add_zero] at hconv
    nlinarith
  · rw [hb', infoRD_eq_zero_of_dMax_le hp le_rfl]
    exact hpos

/-- **Corollary 8.19, (8.95)–(8.97).** For `D_min ≤ D ≤ D_max`, a test channel achieving `R^(I)(D)`
has expected distortion exactly `D`: the constraint `E d(X, X̂) ≤ D` can be replaced by an
equality. -/
theorem expDistortion_eq_of_infoRD_eq [Nonempty β] (hp : IsPMF p) {D : ℝ}
    (hD : D ∈ Set.Icc (minDistortion p d) (dMax p d)) {q : α → β → ℝ} (hq : IsChannel q)
    (hqD : expDistortion p q d ≤ D) (hqI : mutualInfoOf p q = infoRD p d D) :
    expDistortion p q d = D := by
  refine hqD.eq_or_lt.resolve_right fun hlt => ?_
  have hmin := minDistortion_le_expDistortion hp hq (d := d)
  have h₁ := strictAntiOn_infoRD hp ⟨hmin, hqD.trans hD.2⟩ hD hlt
  have h₂ := infoRD_le hp hq (le_refl (expDistortion p q d))
  linarith

/-! ### Tangents to `R^(I)` -/

/-- **(9.57)** For a slope `s ≤ 0`, the minimum over test channels of `I(X; X̂) - s E d(X, X̂)` is
the minimum over `D ≥ D_min` of `R^(I)(D) - s D`: the intercept of the tangent to `R^(I)` with slope
`s`. -/
theorem sInf_mutualInfoOf_sub_mul_eq [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) {s : ℝ}
    (hs : s ≤ 0) :
    sInf {v | ∃ q : α → β → ℝ, IsChannel q ∧ mutualInfoOf p q - s * expDistortion p q d = v} =
      sInf {v | ∃ D, minDistortion p d ≤ D ∧ infoRD p d D - s * D = v} := by
  have hmin : 0 ≤ minDistortion p d :=
    sum_nonneg fun x _ => mul_nonneg (hp.nonneg x) (le_ciInf fun y => hd x y)
  obtain ⟨y₀⟩ := ‹Nonempty β›
  have hq₀ := detChannel_isChannel (fun _ : α => y₀)
  have hbdd₁ : BddBelow {v | ∃ q : α → β → ℝ, IsChannel q ∧
      mutualInfoOf p q - s * expDistortion p q d = v} := ⟨0, by
    rintro _ ⟨q, hq, rfl⟩
    have h₁ := mutualInfoOf_nonneg hp hq
    have h₂ := (minDistortion_le_expDistortion hp hq (d := d))
    nlinarith⟩
  have hbdd₂ : BddBelow {v | ∃ D, minDistortion p d ≤ D ∧ infoRD p d D - s * D = v} := ⟨0, by
    rintro _ ⟨D, hD, rfl⟩
    have := infoRD_nonneg (d := d) hp D
    nlinarith⟩
  refine le_antisymm (le_csInf ⟨_, _, le_rfl, rfl⟩ ?_) (le_csInf ⟨_, _, hq₀, rfl⟩ ?_)
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨q, hq, hqD, hqI⟩ := exists_infoRD_eq hp hD
    refine (csInf_le hbdd₁ ⟨q, hq, rfl⟩).trans ?_
    rw [hqI]
    nlinarith
  · rintro _ ⟨q, hq, rfl⟩
    refine (csInf_le hbdd₂ ⟨_, minDistortion_le_expDistortion hp hq d, rfl⟩).trans ?_
    linarith [infoRD_le hp hq (le_refl (expDistortion p q d))]

end InfoTheory
