/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.BlahutArimoto
public import InfoTheoryLib.ChannelCoding.Capacity
public import InfoTheoryLib.Entropy.Collision

/-!
# Minimax redundancy and channel capacity

A source emits `X ~ p_θ` for an unknown `θ` in a finite family. Coding with the ideal lengths
`l(x) = log 1/q(x)` of a distribution `q` costs the redundancy `E_{p_θ} l(X) - H(p_θ) = D(p_θ ‖ q)`
over the best code for `p_θ`. The minimax redundancy `min_q max_θ D(p_θ ‖ q)` equals the capacity of
the channel `θ → X` whose rows are the `p_θ`, and the minimax code distribution is the output
distribution `q* = ∑_θ π*(θ) p_θ` of a capacity-achieving input `π*` (Theorem 13.1.1).

## Main definitions

* `redundancy p q`: `E_p log 1/q(X) - H(p)` (13.2).

## Main statements

* `redundancy_eq_relEntropyReal`: **(13.2)–(13.6)**, the redundancy is `D(p ‖ q)`.
* `sum_relEntropy_eq`: **(13.14)–(13.20)**, `∑_θ π(θ) D(p_θ ‖ q) = I_π(θ; X) + D(q_π ‖ q)`.
* `mutualInfoOf_le_sum_relEntropy`: **(13.21)–(13.23)**, the output distribution minimizes the
  average redundancy, and the minimum is `I_π(θ; X)`.
* `relEntropy_le_capacity`: every row has `D(p_θ ‖ q*) ≤ C` at the output distribution of a
  capacity-achieving input, with equality on the support of the input.
* `isLeast_maxRedundancy`: **Theorem 13.1.1**, `C = min_q max_θ D(p_θ ‖ q)`.
* `eq_outDist_of_relEntropy_le_capacity`: the minimax distribution is unique, `q = q*`.

## Implementation notes

The book derives Theorem 13.1.1 from von Neumann's minimax theorem. We avoid it: the bound
`max_θ D(p_θ ‖ q) ≥ ∑_θ π*(θ) D(p_θ ‖ q) ≥ C` is (13.22), and for the reverse inequality we
perturb the capacity-achieving input toward a single row, `π_t = (1 - t) π* + t δ_θ`. Since
`I(π_t) ≤ C`, (13.20) gives `D(p_θ ‖ (1 - t) q* + t p_θ) ≤ C` for `0 < t < 1`, and we let
`t → 0`. Redundancies are measured in nats and the integer constraint on the lengths is
ignored, as in the book.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 13.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Redundancy -/

/-- **(13.2)** The redundancy of coding `X ~ p` with the ideal lengths `l(x) = log 1/q(x)` of `q`:
`R(p, q) = E_p l(X) - H(p)`. -/
def redundancy (p q : β → ℝ) : ℝ := ∑ y, p y * (-log (q y)) - entropy p

/-- **(13.2)–(13.6)** The redundancy is the relative entropy: `R(p, q) = D(p ‖ q)`. -/
theorem redundancy_eq_relEntropyReal {p q : β → ℝ} (hpq : AbsCont p q) :
    redundancy p q = relEntropyReal p q := by
  have h := neg_entropy_sub_relEntropyReal hpq
  simp only [redundancy, mul_neg, sum_neg_distrib]
  linarith

/-! ### The average redundancy -/

variable {p : α → ℝ} {W : α → β → ℝ}

/-- **(13.14)–(13.20)** `∑_θ π(θ) D(p_θ ‖ q) = I_π(θ; X) + D(q_π ‖ q)`, for every `q` with
`q_π ≪ q`. -/
theorem sum_relEntropy_eq (hp : IsPMF p) (hW : IsChannel W) {q : β → ℝ}
    (hq : AbsCont (outDist p W) q) :
    ∑ x, p x * relEntropyReal (W x) q = mutualInfoOf p W + relEntropyReal (outDist p W) q := by
  rw [← relEntropyReal_jointOf_prodDist, relEntropy_jointOf_prodDist_eq hp hW hq]

/-- `I_π(θ; X) = ∑_θ π(θ) D(p_θ ‖ q_π)`. -/
lemma mutualInfoOf_eq_sum_relEntropy (hp : IsPMF p) (hW : IsChannel W) :
    mutualInfoOf p W = ∑ x, p x * relEntropyReal (W x) (outDist p W) := by
  rw [sum_relEntropy_eq hp hW fun _ h => h, relEntropyReal_self, add_zero]

/-- **(13.21)–(13.23)** The output distribution `q_π` minimizes the average redundancy
`∑_θ π(θ) D(p_θ ‖ q)`, and the minimum is `I_π(θ; X)`. -/
theorem mutualInfoOf_le_sum_relEntropy (hp : IsPMF p) (hW : IsChannel W) {q : β → ℝ}
    (hq : IsPMF q) (hqW : AbsCont (outDist p W) q) :
    mutualInfoOf p W ≤ ∑ x, p x * relEntropyReal (W x) q := by
  rw [sum_relEntropy_eq hp hW hqW]
  linarith [relEntropyReal_nonneg (outDist_isPMF hp hW) hq hqW]

omit [Fintype β] in
/-- If every row is absolutely continuous with respect to `q`, so is every output distribution. -/
lemma absCont_outDist {q : β → ℝ} (hq : ∀ x, AbsCont (W x) q) : AbsCont (outDist p W) q :=
  fun y hy => sum_eq_zero fun x _ => by rw [hq x y hy, mul_zero]

/-! ### The capacity-achieving output distribution -/

section Mix

variable [DecidableEq α]

/-- The mixture `(1 - t) π + t δ_θ` of an input distribution with a point mass. -/
def mixPoint (p : α → ℝ) (t : ℝ) (x₀ : α) : α → ℝ :=
  fun x => (1 - t) * p x + t * if x = x₀ then 1 else 0

omit [Fintype α] in
lemma mixPoint_nonneg (hp : ∀ x, 0 ≤ p x) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x₀ x : α) :
    0 ≤ mixPoint p t x₀ x := by
  unfold mixPoint
  have := hp x
  have : 0 ≤ 1 - t := by linarith
  split_ifs <;> positivity

lemma mixPoint_isPMF (hp : IsPMF p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x₀ : α) :
    IsPMF (mixPoint p t x₀) := by
  refine ⟨mixPoint_nonneg hp.nonneg ht0 ht1 x₀, ?_⟩
  simp only [mixPoint, sum_add_distrib, ← mul_sum, hp.sum_eq_one, sum_ite_eq', mem_univ,
    ite_true]
  ring

omit [Fintype β] in
lemma outDist_mixPoint (t : ℝ) (x₀ : α) (y : β) :
    outDist (mixPoint p t x₀) W y = (1 - t) * outDist p W y + t * W x₀ y := by
  simp only [outDist, mixPoint, add_mul, sum_add_distrib, mul_assoc, ← mul_sum, ite_mul, one_mul,
    zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- For the output distribution `q*` of a capacity-achieving input and every row `p_θ`,
`D(p_θ ‖ (1 - t) q* + t p_θ) ≤ C` for `0 < t < 1`. -/
lemma relEntropy_mix_le (hp : IsPMF p) (hW : IsChannel W) (hcap : ∀ u, IsPMF u →
    mutualInfoOf u W ≤ mutualInfoOf p W) (x₀ : α) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    relEntropyReal (W x₀) (outDist (mixPoint p t x₀) W) ≤ mutualInfoOf p W := by
  set q := outDist (mixPoint p t x₀) W
  have hmix := mixPoint_isPMF hp ht0.le ht1.le x₀
  have hq := outDist_isPMF hmix hW
  have hI := mutualInfoOf_eq_sum_relEntropy hmix hW
  -- `q*` is absolutely continuous with respect to `q`.
  have hac : AbsCont (outDist p W) q := fun y hy => by
    have hy : outDist (mixPoint p t x₀) W y = 0 := hy
    rw [outDist_mixPoint] at hy
    have h1 : 0 ≤ outDist p W y := (outDist_isPMF hp hW).nonneg y
    have h2 : 0 ≤ W x₀ y := (hW x₀).nonneg y
    have : (1 - t) * outDist p W y = 0 := by nlinarith
    exact (mul_eq_zero.1 this).resolve_left (by linarith)
  have hlow := mutualInfoOf_le_sum_relEntropy hp hW hq hac
  have hsplit : ∑ x, mixPoint p t x₀ x * relEntropyReal (W x) q =
      (1 - t) * ∑ x, p x * relEntropyReal (W x) q + t * relEntropyReal (W x₀) q := by
    simp only [mixPoint, add_mul, sum_add_distrib, mul_assoc, ← mul_sum, ite_mul, one_mul,
      zero_mul, sum_ite_eq', mem_univ, ite_true]
  have hle := hcap _ hmix
  rw [hI, hsplit] at hle
  nlinarith

end Mix

/-- The relative entropy `D(w ‖ (1 - t) r + t w)` is large when `t` is small and `w` charges a
point where `r` vanishes. -/
lemma exists_relEntropy_mix_gt {w r : β → ℝ} (hw : IsPMF w) (hr : IsPMF r) {y₀ : β}
    (hw₀ : 0 < w y₀) (hr₀ : r y₀ = 0) (C : ℝ) :
    ∃ t, 0 < t ∧ t < 1 ∧ C < relEntropyReal w (fun y => (1 - t) * r y + t * w y) := by
  classical
  set A := ∑ y ∈ univ.erase y₀, w y * log (w y)
  set t := min (1 / 2) (exp (-(C - A + 1) / w y₀))
  have ht0 : 0 < t := lt_min (by norm_num) (exp_pos _)
  have ht1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hlogt : log t ≤ -(C - A + 1) / w y₀ :=
    (log_le_log ht0 (min_le_right _ _)).trans (log_exp _).le
  refine ⟨t, ht0, ht1, ?_⟩
  rw [relEntropyReal, ← add_sum_erase _ _ (mem_univ y₀)]
  have hterm₀ : w y₀ * log (w y₀ / ((1 - t) * r y₀ + t * w y₀)) = -(w y₀ * log t) := by
    rw [hr₀, mul_zero, zero_add, div_mul_cancel_right₀ hw₀.ne', log_inv, mul_neg]
  have hterm : ∀ y ∈ univ.erase y₀,
      w y * log (w y) ≤ w y * log (w y / ((1 - t) * r y + t * w y)) := fun y _ => by
    have hwy := hw.nonneg y
    have hry := hr.nonneg y
    rcases hwy.eq_or_lt with h | h
    · rw [← h]; simp
    have hden : 0 < (1 - t) * r y + t * w y := by
      have : 0 ≤ (1 - t) * r y := mul_nonneg (by linarith) hry
      positivity
    have hden1 : (1 - t) * r y + t * w y ≤ 1 := by
      have := hr.le_one y
      have := hw.le_one y
      nlinarith
    refine mul_le_mul_of_nonneg_left (log_le_log h ?_) hwy
    rw [le_div_iff₀ hden]
    nlinarith
  have hsum := sum_le_sum hterm
  rw [hterm₀]
  have : -(w y₀ * log t) ≥ C - A + 1 := by
    have := mul_le_mul_of_nonneg_left hlogt hw₀.le
    rw [mul_div_cancel₀ _ hw₀.ne'] at this
    linarith
  linarith

/-- At the output distribution `q*` of a capacity-achieving input `π*`, every row `p_θ` is
absolutely continuous with respect to `q*` and has `D(p_θ ‖ q*) ≤ C`. -/
theorem relEntropy_le_capacity [Nonempty α] (hp : IsPMF p) (hW : IsChannel W)
    (hpC : mutualInfoOf p W = capacity W) (x₀ : α) :
    AbsCont (W x₀) (outDist p W) ∧ relEntropyReal (W x₀) (outDist p W) ≤ capacity W := by
  classical
  have hcap : ∀ u, IsPMF u → mutualInfoOf u W ≤ mutualInfoOf p W := fun u hu =>
    hpC ▸ mutualInfoOf_le_capacity hu hW
  have hmix := fun t (ht0 : 0 < t) (ht1 : t < 1) => relEntropy_mix_le hp hW hcap x₀ ht0 ht1
  simp only [funext (outDist_mixPoint (W := W) (p := p) _ x₀)] at hmix
  have hq := outDist_isPMF hp hW
  have hac : AbsCont (W x₀) (outDist p W) := by
    intro y₀ hy₀
    by_contra hne
    have hw₀ : 0 < W x₀ y₀ := lt_of_le_of_ne ((hW x₀).nonneg y₀) (Ne.symm hne)
    obtain ⟨t, ht0, ht1, hgt⟩ := exists_relEntropy_mix_gt (hW x₀) hq hw₀ hy₀ (mutualInfoOf p W)
    exact absurd (hmix t ht0 ht1) (not_le.2 hgt)
  refine ⟨hac, hpC ▸ ?_⟩
  -- Let `t → 0`: each term of `D(p_θ ‖ (1 - t) q* + t p_θ)` is continuous at `t = 0`.
  have hcont : Tendsto (fun t => relEntropyReal (W x₀) fun y => (1 - t) * outDist p W y +
      t * W x₀ y) (𝓝[>] 0) (𝓝 (relEntropyReal (W x₀) (outDist p W))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    refine tendsto_finsetSum _ fun y _ => ?_
    by_cases hwy : W x₀ y = 0
    · simp only [hwy, zero_mul]
      exact tendsto_const_nhds
    have hqy : outDist p W y ≠ 0 := fun h => hwy (hac y h)
    have hc : ContinuousAt (fun t : ℝ => (1 - t) * outDist p W y + t * W x₀ y) 0 := by fun_prop
    have hc' : ContinuousAt (fun t : ℝ => W x₀ y * log (W x₀ y /
        ((1 - t) * outDist p W y + t * W x₀ y))) 0 := by
      refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
      · exact continuousAt_const.div hc (by simp [hqy])
      · simp [hwy, hqy]
    simpa using hc'.tendsto
  refine le_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact hmix t ht.1 ht.2

/-- The rows charged by a capacity-achieving input are at distance exactly `C` from `q*`. -/
theorem relEntropy_eq_capacity [Nonempty α] (hp : IsPMF p) (hW : IsChannel W)
    (hpC : mutualInfoOf p W = capacity W) {x₀ : α} (hx₀ : 0 < p x₀) :
    relEntropyReal (W x₀) (outDist p W) = capacity W := by
  have hle := fun x => (relEntropy_le_capacity hp hW hpC x).2
  refine le_antisymm (hle x₀) (by_contra fun hlt => ?_)
  push Not at hlt
  have hI := mutualInfoOf_eq_sum_relEntropy hp hW
  rw [hpC] at hI
  have : ∑ x, p x * relEntropyReal (W x) (outDist p W) < ∑ x, p x * capacity W := by
    refine sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (hle x) (hp.nonneg x))
      ⟨x₀, mem_univ _, mul_lt_mul_of_pos_left hlt hx₀⟩
  rw [← sum_mul, hp.sum_eq_one, one_mul] at this
  linarith

/-! ### Theorem 13.1.1 -/

/-- **(13.22), (13.28)–(13.29)** For every coding distribution `q`, the worst-case redundancy
is at least the capacity: some row has `D(p_θ ‖ q) ≥ C`. -/
theorem exists_capacity_le_relEntropy [Nonempty α] (hW : IsChannel W) {q : β → ℝ}
    (hq : IsPMF q) (hqW : ∀ x, AbsCont (W x) q) : ∃ x, capacity W ≤ relEntropyReal (W x) q := by
  obtain ⟨u, hu, huC⟩ := exists_capacity_eq hW
  have h := mutualInfoOf_le_sum_relEntropy hu hW hq (absCont_outDist (p := u) hqW)
  by_contra hc
  push Not at hc
  have : ∑ x, u x * relEntropyReal (W x) q < ∑ x, u x * capacity W := by
    obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < u x := by
      by_contra h
      push Not at h
      have : ∑ x, u x ≤ 0 := sum_nonpos fun x _ => h x
      linarith [hu.sum_eq_one]
    exact sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (hc x).le (hu.nonneg x))
      ⟨x₀, mem_univ _, mul_lt_mul_of_pos_left (hc x₀) hx₀⟩
  rw [← sum_mul, hu.sum_eq_one, one_mul] at this
  linarith

/-- **Theorem 13.1.1 (Gallager, Ryabko), (13.11).** The capacity of the channel `θ → X` with
rows `p_θ` is the minimax redundancy: `C = min_q max_θ D(p_θ ‖ q)`, the minimum being attained
at the output distribution `q*` of a capacity-achieving input (13.12). -/
theorem isLeast_maxRedundancy [Nonempty α] (hW : IsChannel W) :
    IsLeast {R | ∃ q, IsPMF q ∧ (∀ x, AbsCont (W x) q) ∧ ∀ x, relEntropyReal (W x) q ≤ R}
      (capacity W) := by
  obtain ⟨u, hu, huC⟩ := exists_capacity_eq hW
  refine ⟨⟨outDist u W, outDist_isPMF hu hW, fun x => (relEntropy_le_capacity hu hW huC x).1,
    fun x => (relEntropy_le_capacity hu hW huC x).2⟩, ?_⟩
  rintro R ⟨q, hq, hqW, hR⟩
  obtain ⟨x, hx⟩ := exists_capacity_le_relEntropy hW hq hqW
  exact hx.trans (hR x)

/-- **Theorem 13.1.1 (uniqueness).** A coding distribution `q` with worst-case redundancy `C` is
the output distribution `q*` of every capacity-achieving input. -/
theorem eq_outDist_of_relEntropy_le_capacity [Nonempty α] (hp : IsPMF p) (hW : IsChannel W)
    (hpC : mutualInfoOf p W = capacity W) {q : β → ℝ} (hq : IsPMF q)
    (hqW : ∀ x, AbsCont (W x) q) (hR : ∀ x, relEntropyReal (W x) q ≤ capacity W) :
    q = outDist p W := by
  have hac := absCont_outDist (p := p) hqW
  have h := sum_relEntropy_eq hp hW hac
  have hle : ∑ x, p x * relEntropyReal (W x) q ≤ capacity W := by
    calc ∑ x, p x * relEntropyReal (W x) q ≤ ∑ x, p x * capacity W :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hR x) (hp.nonneg x)
      _ = capacity W := by rw [← sum_mul, hp.sum_eq_one, one_mul]
  have hD : relEntropyReal (outDist p W) q = 0 :=
    le_antisymm (by linarith) (relEntropyReal_nonneg (outDist_isPMF hp hW) hq hac)
  exact ((relEntropyReal_eq_zero_iff (outDist_isPMF hp hW) hq hac).1 hD).symm

end InfoTheory
