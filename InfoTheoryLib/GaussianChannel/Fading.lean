/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.FadingCompound

/-!
# Performance metrics of the Gaussian fading channel

Consider the Gaussian fading channel `Yᵢ = Gᵢ Xᵢ + Zᵢ`, with finitely many fading states: a state
`s` has probability `q(s)` and gain `g(s)`. Lecture 8 of El Gamal and Kim states several metrics, in
terms of the capacity `C(x) = ½ log(1 + x)`. This file studies these formulas; they are not coding
theorems (see `GaussianChannel.FadingCompound` for the compound channel).

## Main definitions

* `fadingErgodic q g P`: `E C(G²P)`, the ergodic capacity with the gain at the decoder, and the
  adaptive capacity.
* `fadingPowerRate q g φ`, `fadingPowerValue q g P`: `E C(G²φ(G))` and
  `max_{φ : E φ(G) ≤ P} E C(G²φ(G))`, the ergodic capacity with the gain at both ends, and the
  power-control adaptive capacity.
* `fadingWaterFill g lam s`: the allocation `(λ - 1/g²)⁺`.
* `fadingOutage q g P pout`: the outage capacity.
* `fadingBroadcastRate`, `fadingBroadcastValue`: the broadcasting approach for two fading states.

## Main statements

* `fadingPowerRate_le_of_waterFill`: water-filling in time is optimal.
* `exists_fadingWaterFill_eq`: the water level exists.
* `tendsto_fadingPowerValue_sub_fadingErgodic`: at high SNR, power control does not help.
* `fadingCompoundValue_le_fadingErgodic`, `fadingErgodic_le_fadingPowerValue`: the order of the
  metrics, and the same for `fadingBroadcastValue` with two states.

## Implementation notes

The notes write `(λ - 1/g²)⁺`, with `1/0 = ∞`; here the allocation is `0` for `g = 0`. The outage
capacity is defined with `P{G < g} ≤ p_out`, not `P{G ≤ g} ≤ p_out` as in the notes: see the
docstring of `fadingOutage`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 8
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒢 : Type*} [Fintype 𝒢]

/-! ### Fast fading -/

/-- **Lecture 8 of [elgamal2010], pages 8-4 and 8-10.** `E C(G²P)`: the ergodic capacity with the
gain at the decoder only, and the adaptive capacity. -/
def fadingErgodic (q g : 𝒢 → ℝ) (P : ℝ) : ℝ := ∑ s, q s * gaussCap (g s ^ 2 * P)

/-- `E C(G²φ(G))` for a power allocation `φ`. -/
def fadingPowerRate (q g φ : 𝒢 → ℝ) : ℝ := ∑ s, q s * gaussCap (g s ^ 2 * φ s)

/-- A power allocation `φ ≥ 0` with `E φ(G) ≤ P`. -/
def IsFadingPower (q φ : 𝒢 → ℝ) (P : ℝ) : Prop := (∀ s, 0 ≤ φ s) ∧ ∑ s, q s * φ s ≤ P

/-- **Lecture 8 of [elgamal2010], pages 8-5 and 8-11.** `max_{φ : E φ(G) ≤ P} E C(G²φ(G))`: the
ergodic capacity with the gain at both the encoder and the decoder, and the power-control adaptive
capacity. -/
def fadingPowerValue (q g : 𝒢 → ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ φ, IsFadingPower q φ P ∧ fadingPowerRate q g φ = v}

open Classical in
/-- **Lecture 8 of [elgamal2010], page 8-5.** The allocation `φ*(g) = (λ - 1/g²)⁺`, which is `0` for
`g = 0`. -/
def fadingWaterFill (g : 𝒢 → ℝ) (lam : ℝ) (s : 𝒢) : ℝ :=
  if g s = 0 then 0 else max (lam - 1 / g s ^ 2) 0

omit [Fintype 𝒢] in
lemma fadingWaterFill_nonneg (g : 𝒢 → ℝ) (lam : ℝ) (s : 𝒢) : 0 ≤ fadingWaterFill g lam s := by
  unfold fadingWaterFill
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

omit [Fintype 𝒢] in
/-- The tangent inequality for one state: the slope of `log(1 + g²x)` at `φ*` is at most `1/λ`, with
equality where `φ* > 0`. -/
lemma log_le_of_fadingWaterFill (g : 𝒢 → ℝ) {lam : ℝ} (hlam : 0 < lam) (s : 𝒢) {x : ℝ}
    (hx : 0 ≤ x) :
    log (1 + g s ^ 2 * x) ≤ log (1 + g s ^ 2 * fadingWaterFill g lam s) +
      (x - fadingWaterFill g lam s) / lam := by
  by_cases hg : g s = 0
  · simp only [fadingWaterFill, hg, ite_true]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, log_one,
      sub_zero, zero_add]
    positivity
  · have hg2 : 0 < g s ^ 2 := by positivity
    set φ := fadingWaterFill g lam s with hφ
    have hφ0 : 0 ≤ φ := fadingWaterFill_nonneg g lam s
    have hd : 0 < 1 + g s ^ 2 * φ := by positivity
    have hn : 0 < 1 + g s ^ 2 * x := by positivity
    -- `log (a/b) ≤ a/b - 1`.
    have h1 := log_le_sub_one_of_pos (div_pos hn hd)
    rw [log_div hn.ne' hd.ne'] at h1
    have h2 : (1 + g s ^ 2 * x) / (1 + g s ^ 2 * φ) - 1 ≤ (x - φ) / lam := by
      have e : (1 + g s ^ 2 * x) / (1 + g s ^ 2 * φ) - 1 =
          g s ^ 2 * (x - φ) / (1 + g s ^ 2 * φ) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ hd hlam]
      simp only [hφ, fadingWaterFill, hg, ite_false]
      rcases le_total (lam - 1 / g s ^ 2) 0 with hl | hl
      · rw [max_eq_right hl]
        have hl' : lam * g s ^ 2 ≤ 1 := by
          have : lam ≤ 1 / g s ^ 2 := by linarith
          rwa [le_div_iff₀ hg2] at this
        nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ 1 - lam * g s ^ 2)]
      · rw [max_eq_left hl]
        have e2 : g s ^ 2 * (lam - 1 / g s ^ 2) = g s ^ 2 * lam - 1 := by
          field_simp
        rw [e2]
        have e3 : (1 + (g s ^ 2 * lam - 1)) = g s ^ 2 * lam := by ring
        rw [e3]
        apply le_of_eq
        ring
    linarith

/-- **Lecture 8 of [elgamal2010], page 8-5.** Water-filling in time: if the allocation
`φ*(g) = (λ - 1/g²)⁺` has `E φ*(G) = P`, it maximizes `E C(G²φ(G))`. -/
theorem fadingPowerRate_le_of_waterFill {q g φ : 𝒢 → ℝ} (hq : ∀ s, 0 ≤ q s) {P lam : ℝ}
    (hlam : 0 < lam) (hP : ∑ s, q s * fadingWaterFill g lam s = P) (hφ : IsFadingPower q φ P) :
    fadingPowerRate q g φ ≤ fadingPowerRate q g (fadingWaterFill g lam) := by
  have hs : ∀ s, gaussCap (g s ^ 2 * φ s) ≤ gaussCap (g s ^ 2 * fadingWaterFill g lam s) +
      (φ s - fadingWaterFill g lam s) / (2 * lam) := fun s => by
    have := log_le_of_fadingWaterFill g hlam s (hφ.1 s)
    simp only [gaussCap]
    have e : (φ s - fadingWaterFill g lam s) / (2 * lam) =
        1 / 2 * ((φ s - fadingWaterFill g lam s) / lam) := by
      field_simp
    rw [e]
    linarith
  have hsum := sum_le_sum fun s (_ : s ∈ univ) => mul_le_mul_of_nonneg_left (hs s) (hq s)
  have hrest : ∑ s, q s * ((φ s - fadingWaterFill g lam s) / (2 * lam)) ≤ 0 := by
    have e : ∑ s, q s * ((φ s - fadingWaterFill g lam s) / (2 * lam)) =
        (∑ s, q s * φ s - ∑ s, q s * fadingWaterFill g lam s) / (2 * lam) := by
      rw [← sum_sub_distrib, sum_div]
      exact sum_congr rfl fun s _ => by ring
    rw [e, hP]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hφ.2]) (by positivity)
  simp only [mul_add] at hsum
  rw [sum_add_distrib] at hsum
  simp only [fadingPowerRate]
  linarith

/-- The water level exists: for `P > 0` and a state of positive probability with a nonzero gain,
there is `λ > 0` with `E[(λ - 1/G²)⁺] = P`. -/
theorem exists_fadingWaterFill_eq {q g : 𝒢 → ℝ} (hq : ∀ s, 0 ≤ q s) {P : ℝ} (hP : 0 < P)
    {s₀ : 𝒢} (hs₀ : 0 < q s₀) (hg₀ : g s₀ ≠ 0) :
    ∃ lam, 0 < lam ∧ ∑ s, q s * fadingWaterFill g lam s = P := by
  classical
  have hcont : Continuous fun lam => ∑ s, q s * fadingWaterFill g lam s := by
    refine continuous_finsetSum _ fun s _ => continuous_const.mul ?_
    unfold fadingWaterFill
    split_ifs
    · exact continuous_const
    · fun_prop
  have h0 : ∑ s, q s * fadingWaterFill g 0 s = 0 := by
    refine sum_eq_zero fun s _ => ?_
    simp only [fadingWaterFill]
    split_ifs
    · simp
    · have : max (0 - 1 / g s ^ 2) 0 = 0 := max_eq_right (by
        have : 0 ≤ 1 / g s ^ 2 := by positivity
        linarith)
      rw [this, mul_zero]
  set L := P / q s₀ + 1 / g s₀ ^ 2
  have hL : P ≤ ∑ s, q s * fadingWaterFill g L s := by
    have h1 : q s₀ * fadingWaterFill g L s₀ = P := by
      have h2 : L - 1 / g s₀ ^ 2 = P / q s₀ := by simp [L]
      have h3 : 0 ≤ P / q s₀ := by positivity
      simp only [fadingWaterFill, hg₀, ite_false, h2, max_eq_left h3]
      field_simp
    rw [← h1]
    exact single_le_sum (f := fun s => q s * fadingWaterFill g L s)
      (fun s _ => mul_nonneg (hq s) (fadingWaterFill_nonneg g L s)) (mem_univ s₀)
  have hL0 : 0 ≤ L := by positivity
  obtain ⟨lam, hlam, hlamP⟩ := intermediate_value_Icc hL0 hcont.continuousOn
    (show P ∈ Set.Icc (∑ s, q s * fadingWaterFill g 0 s) (∑ s, q s * fadingWaterFill g L s) by
      rw [h0]
      exact ⟨hP.le, hL⟩)
  refine ⟨lam, lt_of_le_of_ne hlam.1 ?_, hlamP⟩
  rintro rfl
  have h' : ∑ s, q s * fadingWaterFill g 0 s = P := hlamP
  rw [h0] at h'
  exact hP.ne h'

/-- The value is the one of the water-filling allocation. -/
theorem fadingPowerValue_eq_of_waterFill {q g : 𝒢 → ℝ} (hq : ∀ s, 0 ≤ q s) {P lam : ℝ}
    (hlam : 0 < lam) (hP : ∑ s, q s * fadingWaterFill g lam s = P) :
    fadingPowerValue q g P = fadingPowerRate q g (fadingWaterFill g lam) := by
  have hmem : IsFadingPower q (fadingWaterFill g lam) P :=
    ⟨fadingWaterFill_nonneg g lam, hP.le⟩
  refine le_antisymm (csSup_le ⟨_, fadingWaterFill g lam, hmem, rfl⟩ ?_)
    (le_csSup ?_ ⟨fadingWaterFill g lam, hmem, rfl⟩)
  · rintro _ ⟨φ, hφ, rfl⟩
    exact fadingPowerRate_le_of_waterFill hq hlam hP hφ
  · refine ⟨fadingPowerRate q g (fadingWaterFill g lam), ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact fadingPowerRate_le_of_waterFill hq hlam hP hφ

/-! ### High SNR -/

/-- The set of `E C(G²φ(G))` is bounded above: `C(x) ≤ x/2`. -/
lemma bddAbove_fadingPowerValue {q : 𝒢 → ℝ} (hq : ∀ s, 0 ≤ q s) (g : 𝒢 → ℝ) (P : ℝ) :
    BddAbove {v | ∃ φ, IsFadingPower q φ P ∧ fadingPowerRate q g φ = v} := by
  have hK : 0 ≤ ∑ t, g t ^ 2 := sum_nonneg fun t _ => sq_nonneg _
  refine ⟨1 / 2 * (∑ t, g t ^ 2) * P, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  have hs : ∀ s, q s * gaussCap (g s ^ 2 * φ s) ≤ 1 / 2 * (∑ t, g t ^ 2) * (q s * φ s) := by
    intro s
    have hx : 0 ≤ g s ^ 2 * φ s := mul_nonneg (sq_nonneg _) (hφ.1 s)
    have h1 : gaussCap (g s ^ 2 * φ s) ≤ 1 / 2 * (g s ^ 2 * φ s) := by
      simp only [gaussCap]
      have := log_le_sub_one_of_pos (by linarith : 0 < 1 + g s ^ 2 * φ s)
      linarith
    have h2 : g s ^ 2 ≤ ∑ t, g t ^ 2 :=
      single_le_sum (f := fun t => g t ^ 2) (fun t _ => sq_nonneg _) (mem_univ s)
    have h3 := mul_nonneg (hq s) (hφ.1 s)
    calc q s * gaussCap (g s ^ 2 * φ s) ≤ q s * (1 / 2 * (g s ^ 2 * φ s)) :=
          mul_le_mul_of_nonneg_left h1 (hq s)
      _ = 1 / 2 * g s ^ 2 * (q s * φ s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) h3
  calc fadingPowerRate q g φ ≤ ∑ s, 1 / 2 * (∑ t, g t ^ 2) * (q s * φ s) :=
        sum_le_sum fun s _ => hs s
    _ = 1 / 2 * (∑ t, g t ^ 2) * ∑ s, q s * φ s := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hφ.2 (by positivity)

/-- **Lecture 8 of [elgamal2010], page 8-11.** The constant allocation `φ = P`: power control can
only help, `C_A ≤ C_PA`. -/
theorem fadingErgodic_le_fadingPowerValue {q : 𝒢 → ℝ} (hq : IsPMF q) (g : 𝒢 → ℝ) {P : ℝ}
    (hP : 0 ≤ P) : fadingErgodic q g P ≤ fadingPowerValue q g P := by
  refine le_csSup (bddAbove_fadingPowerValue hq.nonneg g P) ⟨fun _ => P, ⟨fun _ => hP, ?_⟩, rfl⟩
  rw [← sum_mul, hq.sum_eq_one, one_mul]

/-- For a large power every state gets power: `φ*(g) = λ - 1/g²` with `λ = P + E[1/G²]`. -/
lemma fadingPowerValue_eq_of_large {q g : 𝒢 → ℝ} (hq : IsPMF q) (hg : ∀ s, g s ≠ 0) {P : ℝ}
    (hP : ∑ s, 1 / g s ^ 2 ≤ P) :
    fadingPowerValue q g P =
      ∑ s, q s * (1 / 2 * log (g s ^ 2 * (P + ∑ t, q t * (1 / g t ^ 2)))) := by
  set c := ∑ t, q t * (1 / g t ^ 2) with hc
  have hc0 : 0 ≤ c := sum_nonneg fun t _ => mul_nonneg (hq.nonneg t) (by positivity)
  have hone : ∀ s, 1 / g s ^ 2 ≤ P := fun s =>
    (single_le_sum (f := fun t => 1 / g t ^ 2) (fun t _ => by positivity) (mem_univ s)).trans hP
  have hP0 : 0 ≤ P := (sum_nonneg fun t _ => by positivity).trans hP
  have hφ : ∀ s, fadingWaterFill g (P + c) s = P + c - 1 / g s ^ 2 := fun s => by
    simp only [fadingWaterFill, hg s, ite_false]
    exact max_eq_left (by linarith [hone s])
  have hne : Nonempty 𝒢 := by
    by_contra h
    rw [not_nonempty_iff] at h
    simpa using hq.sum_eq_one
  obtain ⟨s₀⟩ := hne
  have hpos : 0 < P + c := by
    have h1 : 0 < 1 / g s₀ ^ 2 := by
      have := hg s₀
      positivity
    linarith [hone s₀]
  have hE : ∑ s, q s * fadingWaterFill g (P + c) s = P := by
    simp_rw [hφ, mul_sub, sum_sub_distrib, mul_comm (q _) (P + c)]
    rw [← mul_sum, hq.sum_eq_one, mul_one]
    simp only [mul_comm (q _)] at hc ⊢
    rw [← hc]
    ring
  rw [fadingPowerValue_eq_of_waterFill hq.nonneg hpos hE, fadingPowerRate]
  refine sum_congr rfl fun s _ => ?_
  congr 1
  rw [hφ, gaussCap]
  congr 2
  have := hg s
  field_simp
  ring

/-- **Lecture 8 of [elgamal2010], page 8-6.** At high SNR, the capacity gain from power control
vanishes: `C_SI-ED - C_SI-D → 0` as `P → ∞`. -/
theorem tendsto_fadingPowerValue_sub_fadingErgodic {q g : 𝒢 → ℝ} (hq : IsPMF q)
    (hg : ∀ s, g s ≠ 0) :
    Tendsto (fun P => fadingPowerValue q g P - fadingErgodic q g P) atTop (𝓝 0) := by
  set c := ∑ t, q t * (1 / g t ^ 2)
  have hs : ∀ s, Tendsto (fun P : ℝ => q s * (1 / 2 * log (g s ^ 2 * (P + c) / (1 + g s ^ 2 * P))))
      atTop (𝓝 0) := fun s => by
    have hg2 : 0 < g s ^ 2 := by
      have := hg s
      positivity
    have h1 : Tendsto (fun P : ℝ => 1 + g s ^ 2 * P) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hg2)
    have h2 : Tendsto (fun P : ℝ => 1 + (g s ^ 2 * c - 1) / (1 + g s ^ 2 * P)) atTop (𝓝 1) := by
      simpa using (h1.const_div_atTop (g s ^ 2 * c - 1)).const_add 1
    have h3 : Tendsto (fun P : ℝ => log (1 + (g s ^ 2 * c - 1) / (1 + g s ^ 2 * P))) atTop
        (𝓝 (log 1)) := (continuousAt_log one_ne_zero).tendsto.comp h2
    rw [log_one] at h3
    have h4 := (h3.const_mul (1 / 2)).const_mul (q s)
    simp only [mul_zero] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with P hP
    have hd : 0 < 1 + g s ^ 2 * P := by positivity
    congr 3
    field_simp
    ring
  have hsum := tendsto_finsetSum (univ : Finset 𝒢) fun s _ => hs s
  simp only [sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (∑ s, 1 / g s ^ 2), eventually_gt_atTop (0 : ℝ)] with P hP hP0
  rw [fadingPowerValue_eq_of_large hq hg hP, fadingErgodic, ← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  have hg2 : 0 < g s ^ 2 := by
    have := hg s
    positivity
  have hd : 0 < 1 + g s ^ 2 * P := by positivity
  have hc0 : 0 ≤ c := sum_nonneg fun t _ => mul_nonneg (hq.nonneg t) (by positivity)
  have hn : 0 < g s ^ 2 * (P + c) := by positivity
  rw [log_div hn.ne' hd.ne', gaussCap]
  ring

/-! ### Slow fading -/

/-- **Lecture 8 of [elgamal2010], page 8-8.** `C_CC ≤ E C(G²P)`: the adaptive capacity is at least
the compound capacity. -/
theorem fadingCompoundValue_le_fadingErgodic [Nonempty 𝒢] {q : 𝒢 → ℝ} (hq : IsPMF q) (g : 𝒢 → ℝ)
    (P : ℝ) : fadingCompoundValue g P ≤ fadingErgodic q g P := by
  calc fadingCompoundValue g P = ∑ s, q s * fadingCompoundValue g P := by
        rw [← sum_mul, hq.sum_eq_one, one_mul]
    _ ≤ _ := sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (inf'_le (fun s => gaussCap (g s ^ 2 * P)) (mem_univ s)) (hq.nonneg s)

open Classical in
/-- **Lecture 8 of [elgamal2010], page 8-8.** The outage capacity for the outage probability
`p_out`: the maximum of `C(g²P)` over the gains `g` with `P{G < g} ≤ p_out`.

The notes write `P{G ≤ g} ≤ p_out`. With finitely many states and `p_out = 0`, no gain in the
support would satisfy it, and the supremum would not be attained, whereas sending at the rate
`C(g²P)` is in outage exactly when `G < g`. -/
def fadingOutage (q g : 𝒢 → ℝ) (P pout : ℝ) : ℝ :=
  sSup {v | ∃ s, ∑ t with g t < g s, q t ≤ pout ∧ gaussCap (g s ^ 2 * P) = v}

omit [Fintype 𝒢] in
lemma sq_le_sq_of_gain {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  pow_le_pow_left₀ ha hab 2

open Classical in
lemma bddAbove_fadingOutage (q g : 𝒢 → ℝ) (P pout : ℝ) :
    BddAbove {v | ∃ s, ∑ t with g t < g s, q t ≤ pout ∧ gaussCap (g s ^ 2 * P) = v} := by
  refine BddAbove.mono ?_ (Set.finite_range fun s => gaussCap (g s ^ 2 * P)).bddAbove
  rintro _ ⟨s, _, hs⟩
  exact ⟨s, hs⟩

/-- **Lecture 8 of [elgamal2010], page 8-8.** `C_CC ≤ C_out`. -/
theorem fadingCompoundValue_le_fadingOutage [Nonempty 𝒢] {q g : 𝒢 → ℝ} {P pout : ℝ}
    (hpout : 0 ≤ pout) : fadingCompoundValue g P ≤ fadingOutage q g P pout := by
  classical
  obtain ⟨s₀, -, hs₀⟩ := exists_min_image (univ : Finset 𝒢) g univ_nonempty
  have h0 : ∑ t with g t < g s₀, q t = 0 := by
    refine sum_eq_zero fun t ht => ?_
    exact absurd (hs₀ t (mem_univ t)) (not_le.2 (mem_filter.1 ht).2)
  refine (inf'_le (fun s => gaussCap (g s ^ 2 * P)) (mem_univ s₀)).trans ?_
  exact le_csSup (bddAbove_fadingOutage q g P pout) ⟨s₀, h0.le.trans hpout, rfl⟩

/-- **Lecture 8 of [elgamal2010], page 8-8.** With no outage, and all the states of positive
probability, the outage capacity is the compound capacity. -/
theorem fadingOutage_zero [Nonempty 𝒢] {q g : 𝒢 → ℝ} {P : ℝ} (hq : ∀ s, 0 < q s)
    (hg : ∀ s, 0 ≤ g s) (hP : 0 ≤ P) : fadingOutage q g P 0 = fadingCompoundValue g P := by
  classical
  refine le_antisymm ?_ (fadingCompoundValue_le_fadingOutage le_rfl)
  obtain ⟨s₀, -, hs₀⟩ := exists_min_image (univ : Finset 𝒢) g univ_nonempty
  refine csSup_le ?_ ?_
  · refine ⟨_, s₀, ?_, rfl⟩
    have h0 : ∑ t with g t < g s₀, q t = 0 := by
      refine sum_eq_zero fun t ht => ?_
      exact absurd (hs₀ t (mem_univ t)) (not_le.2 (mem_filter.1 ht).2)
    exact h0.le
  · rintro _ ⟨s, hs, rfl⟩
    refine le_inf' _ _ fun t _ => ?_
    have hmin : g s ≤ g t := by
      by_contra hlt
      have hmem : t ∈ univ.filter fun t => g t < g s := mem_filter.2 ⟨mem_univ t, not_le.1 hlt⟩
      have := single_le_sum (f := q) (fun t _ => (hq t).le) hmem
      linarith [hq t]
    exact gaussCap_le_gaussCap (mul_nonneg (sq_nonneg _) hP)
      (mul_le_mul_of_nonneg_right (sq_le_sq_of_gain (hg s) hmin) hP)

/-! ### The broadcasting approach -/

section Broadcast

variable {p x₁ x₂ P a : ℝ}

/-- **Lecture 8 of [elgamal2010], page 8-9.** The rate
`p C(g₁² ᾱ P) + C(g₂² α P/(1 + ᾱ g₂² P))` of the broadcasting approach with two fading states, with
`x₁ = g₁²`, `x₂ = g₂²`: the common message at the rate `R̃₂` is decoded for both gains, and the
private message at the rate `R̃₁` only for the gain `g₁`. -/
def fadingBroadcastRate (p x₁ x₂ P a : ℝ) : ℝ :=
  p * gaussCap (x₁ * ((1 - a) * P)) + gaussCap (x₂ * a * P / (1 + (1 - a) * x₂ * P))

/-- **Lecture 8 of [elgamal2010], page 8-9.** `C_BC = max_α (p R₁ + (1 - p) R₂)`. -/
def fadingBroadcastValue (p x₁ x₂ P : ℝ) : ℝ :=
  sSup {v | ∃ a ∈ Set.Icc (0 : ℝ) 1, fadingBroadcastRate p x₁ x₂ P a = v}

/-- `p R₁ + (1 - p) R₂ = p R̃₁ + R̃₂` for `R₁ = R̃₁ + R̃₂`, `R₂ = R̃₂`. -/
lemma fadingBroadcastRate_eq (p x₁ x₂ P a : ℝ) :
    p * (gaussCap (x₁ * ((1 - a) * P)) + gaussCap (x₂ * a * P / (1 + (1 - a) * x₂ * P))) +
        (1 - p) * gaussCap (x₂ * a * P / (1 + (1 - a) * x₂ * P)) =
      fadingBroadcastRate p x₁ x₂ P a := by
  simp only [fadingBroadcastRate]
  ring

/-- The rate of the common message, by successive cancellation:
`C(g² α P/(1 + ᾱ g² P)) = C(g² P) - C(g² ᾱ P)`. -/
lemma gaussCap_common (hx : 0 ≤ x₂) (hP : 0 ≤ P) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    gaussCap (x₂ * a * P / (1 + (1 - a) * x₂ * P)) =
      gaussCap (x₂ * P) - gaussCap (x₂ * ((1 - a) * P)) := by
  have h1 : 0 ≤ 1 - a := by linarith [ha.2]
  have hd : 0 < 1 + (1 - a) * x₂ * P := by positivity
  have hd' : 0 < 1 + x₂ * ((1 - a) * P) := by positivity
  have hn : 0 < 1 + x₂ * P := by positivity
  have e : 1 + x₂ * a * P / (1 + (1 - a) * x₂ * P) = (1 + x₂ * P) / (1 + x₂ * ((1 - a) * P)) := by
    field_simp
    ring
  simp only [gaussCap]
  rw [e, log_div hn.ne' hd'.ne']
  ring

/-- The rate of a refinement grows with the gain: `C(xP) - C(xᾱP)` is increasing in `x`. -/
lemma gaussCap_sub_mono (hx : 0 ≤ x₂) (hx' : x₂ ≤ x₁) (hP : 0 ≤ P) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    gaussCap (x₂ * P) - gaussCap (x₂ * ((1 - a) * P)) ≤
      gaussCap (x₁ * P) - gaussCap (x₁ * ((1 - a) * P)) := by
  have hx₁ : 0 ≤ x₁ := hx.trans hx'
  have h1 : 0 ≤ 1 - a := by linarith [ha.2]
  have p1 : 0 < 1 + x₂ * P := by positivity
  have p2 : 0 < 1 + x₂ * ((1 - a) * P) := by positivity
  have p3 : 0 < 1 + x₁ * P := by positivity
  have p4 : 0 < 1 + x₁ * ((1 - a) * P) := by positivity
  simp only [gaussCap]
  have h : (1 + x₂ * P) / (1 + x₂ * ((1 - a) * P)) ≤ (1 + x₁ * P) / (1 + x₁ * ((1 - a) * P)) := by
    rw [div_le_div_iff₀ p2 p4]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hx') hP) ha.1]
  have := log_le_log (div_pos p1 p2) h
  rw [log_div p1.ne' p2.ne', log_div p3.ne' p4.ne'] at this
  linarith

/-- **Lecture 8 of [elgamal2010], page 8-12.** `C_BC ≤ C_A`: the rate of the broadcasting approach
is at most the adaptive capacity `p C(g₁²P) + (1 - p) C(g₂²P)`. -/
theorem fadingBroadcastRate_le (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x₂) (hx' : x₂ ≤ x₁)
    (hP : 0 ≤ P) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    fadingBroadcastRate p x₁ x₂ P a ≤ p * gaussCap (x₁ * P) + (1 - p) * gaussCap (x₂ * P) := by
  have h1 : 0 ≤ 1 - a := by linarith [ha.2]
  have h2 := gaussCap_sub_mono hx hx' hP ha
  have h3 : 0 ≤ gaussCap (x₂ * ((1 - a) * P)) := gaussCap_nonneg (by positivity)
  rw [fadingBroadcastRate, gaussCap_common hx hP ha]
  have hp0 := hp.1
  have hp1 : 0 ≤ 1 - p := by linarith [hp.2]
  nlinarith [mul_le_mul_of_nonneg_left h2 hp0, mul_nonneg hp1 h3]

lemma bddAbove_fadingBroadcast (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x₂) (hx' : x₂ ≤ x₁)
    (hP : 0 ≤ P) : BddAbove {v | ∃ a ∈ Set.Icc (0 : ℝ) 1, fadingBroadcastRate p x₁ x₂ P a = v} :=
  ⟨p * gaussCap (x₁ * P) + (1 - p) * gaussCap (x₂ * P), fun _ ⟨_, ha, hv⟩ =>
    hv ▸ fadingBroadcastRate_le hp hx hx' hP ha⟩

/-- **Lecture 8 of [elgamal2010], page 8-12.** `C_CC ≤ C_BC`: `α = 1`. -/
theorem gaussCap_le_fadingBroadcastValue (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x₂)
    (hx' : x₂ ≤ x₁) (hP : 0 ≤ P) : gaussCap (x₂ * P) ≤ fadingBroadcastValue p x₁ x₂ P := by
  refine le_csSup (bddAbove_fadingBroadcast hp hx hx' hP) ⟨1, by simp, ?_⟩
  simp [fadingBroadcastRate]

/-- **Lecture 8 of [elgamal2010], page 8-12.** `p C(g₁²P) ≤ C_BC`: `α = 0`, sending only to the
strong state. -/
theorem mul_gaussCap_le_fadingBroadcastValue (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x₂)
    (hx' : x₂ ≤ x₁) (hP : 0 ≤ P) : p * gaussCap (x₁ * P) ≤ fadingBroadcastValue p x₁ x₂ P := by
  refine le_csSup (bddAbove_fadingBroadcast hp hx hx' hP) ⟨0, by simp, ?_⟩
  simp [fadingBroadcastRate]

/-- **Lecture 8 of [elgamal2010], page 8-12.** `C_BC ≤ C_A`. -/
theorem fadingBroadcastValue_le (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x₂) (hx' : x₂ ≤ x₁)
    (hP : 0 ≤ P) :
    fadingBroadcastValue p x₁ x₂ P ≤ p * gaussCap (x₁ * P) + (1 - p) * gaussCap (x₂ * P) :=
  csSup_le ⟨_, 0, by simp, rfl⟩ fun _ ⟨_, ha, hv⟩ => hv ▸ fadingBroadcastRate_le hp hx hx' hP ha

end Broadcast

end InfoTheory
