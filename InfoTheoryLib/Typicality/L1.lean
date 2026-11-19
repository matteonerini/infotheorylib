/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Statistics.ChernoffInformation
public import InfoTheoryLib.Typicality.Basic

/-!
# Strong typicality in variational distance

A sequence `x` is strongly `δ`-typical for `p` if no symbol outside the support of `p` occurs in it
and its type is within `δ` of `p` in variational distance: `∑ₐ |N(a; x)/n - p(a)| ≤ δ`. This is the
definition of [yeung2008]. The library has two other forms of strong typicality: `strongTypicalSet`
bounds each symbol by `δ/|𝒳|`, and `robustTypicalSet` bounds each symbol relative to `p(a)`.

## Main definitions

* `l1TypicalSet p n δ`: the strongly typical set `T_{[X]δ}ⁿ`.
* `jointL1TypicalSet q n δ`: the strongly jointly typical set `T_{[XY]δ}ⁿ`.
* `maxNegLog p`: the constant `-log minₓ p(x)`, with the minimum over the support.

## Main statements

* `exp_le_iidPMF_of_mem_l1TypicalSet`, `eventually_prob_l1TypicalSet_gt`, `card_l1TypicalSet_le`,
  `eventually_card_l1TypicalSet_ge`: the strong AEP.
* `eventually_l1TypicalSet_nonempty`: strongly typical sequences exist for `n` large.
* `exists_eventually_prob_l1TypicalSet_compl_lt`: the probability of a non-typical sequence decays
  exponentially.
* `prob_le_le_exp_mul_expect`: the lower tail of the Chernoff bound.
* `l1TypicalSet_subset_typicalSet`: strong typicality implies weak typicality.
* `comp_mem_l1TypicalSet`, `fst_mem_l1TypicalSet`, `snd_mem_l1TypicalSet`: preservation by functions
  and consistency.
* `exp_le_jointIid_of_mem_jointL1TypicalSet`, `eventually_prob_jointL1TypicalSet_gt`,
  `card_jointL1TypicalSet_le`, `eventually_card_jointL1TypicalSet_ge`: the strong joint AEP.

## Implementation notes

Logarithms are natural, so `2^{-n(H ± η)}` is `e^{-n(H ± η)}` with `H` and `η` in nats. The relative
frequency `N(a; x)/n` is `typeOf x a`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 6.1 to 6.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### The typical set -/

open Classical in
/-- **Definition 6.1.** The strongly typical set `T_{[X]δ}ⁿ` with respect to `p`: the sequences with
`N(a; x) = 0` for `a` outside the support of `p` and `∑ₐ |N(a; x)/n - p(a)| ≤ δ`. -/
def l1TypicalSet (p : α → ℝ) (n : ℕ) (δ : ℝ) : Finset (Fin n → α) :=
  univ.filter fun x => (∀ a, p a = 0 → symbolCount x a = 0) ∧ ∑ a, |typeOf x a - p a| ≤ δ

lemma mem_l1TypicalSet {p : α → ℝ} {n : ℕ} {δ : ℝ} {x : Fin n → α} :
    x ∈ l1TypicalSet p n δ ↔
      (∀ a, p a = 0 → symbolCount x a = 0) ∧ ∑ a, |typeOf x a - p a| ≤ δ := by
  classical
  simp [l1TypicalSet]

/-- The constant `-log minₓ p(x)` of (6.15), with the minimum over the support of `p`. Since
`log 0 = 0` in Lean, the supremum may be taken over all symbols. -/
def maxNegLog (p : α → ℝ) : ℝ := ⨆ a, -log (p a)

omit [Fintype α] in
lemma neg_log_le_maxNegLog [Finite α] (p : α → ℝ) (a : α) : -log (p a) ≤ maxNegLog p :=
  le_ciSup (f := fun a => -log (p a)) (Set.finite_range _).bddAbove a

lemma neg_log_nonneg_of_isPMF {p : α → ℝ} (hp : IsPMF p) (a : α) : 0 ≤ -log (p a) :=
  neg_nonneg.2 (log_nonpos (hp.nonneg a) (hp.le_one a))

lemma maxNegLog_nonneg {p : α → ℝ} (hp : IsPMF p) : 0 ≤ maxNegLog p := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  obtain ⟨a⟩ := ‹Nonempty α›
  exact (neg_log_nonneg_of_isPMF hp a).trans (neg_log_le_maxNegLog p a)

omit [Fintype α] in
/-- A symbol that does not occur differs from every coordinate of the sequence. -/
lemma apply_ne_of_symbolCount_eq_zero {n : ℕ} {x : Fin n → α} {a : α} (h : symbolCount x a = 0)
    (i : Fin n) : x i ≠ a := by
  classical
  rw [symbolCount, card_eq_zero, filter_eq_empty_iff] at h
  exact h (mem_univ i)

omit [Fintype α] in
lemma symbolCount_eq_zero_of_forall_ne {n : ℕ} {x : Fin n → α} {a : α} (h : ∀ i, x i ≠ a) :
    symbolCount x a = 0 := by
  classical
  rw [symbolCount, card_eq_zero, filter_eq_empty_iff]
  exact fun i _ => h i

/-- A strongly typical sequence has positive probability. -/
lemma iidPMF_pos_of_mem_l1TypicalSet {p : α → ℝ} (hp : IsPMF p) {n : ℕ} {δ : ℝ} {x : Fin n → α}
    (hx : x ∈ l1TypicalSet p n δ) : 0 < iidPMF p n x := by
  refine prod_pos fun i _ => (hp.nonneg _).lt_of_ne' fun h => ?_
  exact apply_ne_of_symbolCount_eq_zero ((mem_l1TypicalSet.1 hx).1 _ h) i rfl

omit [Fintype α] in
lemma symbolCount_eq_mul_typeOf (n : ℕ) (x : Fin n → α) (a : α) :
    (symbolCount x a : ℝ) = n * typeOf x a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := symbolCount_le x a
    simp [Nat.le_zero.1 this]
  · exact (mul_typeOf hn x a).symm

/-- (6.5)–(6.9): `-log p(x) = n (H(X) + ∑ₐ (N(a; x)/n - p(a)) (-log p(a)))`. -/
lemma neg_log_iidPMF_eq {p : α → ℝ} {n : ℕ} {x : Fin n → α} (h : iidPMF p n x ≠ 0) :
    -log (iidPMF p n x) = n * (entropy p + ∑ a, (typeOf x a - p a) * -log (p a)) := by
  have hH : entropy p = ∑ a, p a * -log (p a) := by
    rw [← expect_neg_log p, expect]
    exact sum_congr rfl fun a _ => mul_comm _ _
  rw [log_iidPMF h, ← sum_neg_distrib,
    sum_comp_eq_sum_symbolCount x fun a => -log (p a), hH, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [symbolCount_eq_mul_typeOf]
  ring

/-- (6.11)–(6.14): the bound `|∑ₐ (N(a; x)/n - p(a)) (-log p(a))| ≤ δ (-log minₓ p(x))`. -/
lemma abs_sum_deviation_le {p : α → ℝ} (hp : IsPMF p) {n : ℕ} {δ : ℝ} {x : Fin n → α}
    (hx : x ∈ l1TypicalSet p n δ) :
    |∑ a, (typeOf x a - p a) * -log (p a)| ≤ δ * maxNegLog p := by
  calc |∑ a, (typeOf x a - p a) * -log (p a)|
      ≤ ∑ a, |typeOf x a - p a| * maxNegLog p := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
        rw [abs_mul, abs_of_nonneg (neg_log_nonneg_of_isPMF hp a)]
        exact mul_le_mul_of_nonneg_left (neg_log_le_maxNegLog p a) (abs_nonneg _)
    _ = (∑ a, |typeOf x a - p a|) * maxNegLog p := by rw [sum_mul]
    _ ≤ δ * maxNegLog p :=
        mul_le_mul_of_nonneg_right (mem_l1TypicalSet.1 hx).2 (maxNegLog_nonneg hp)

/-! ### The strong AEP -/

/-- **Theorem 6.2 (1).** If `x` is strongly `δ`-typical, then
`e^{-n(H(X) + η)} ≤ p(x) ≤ e^{-n(H(X) - η)}`, with `η = δ (-log minₓ p(x))`. -/
theorem exp_le_iidPMF_of_mem_l1TypicalSet {p : α → ℝ} (hp : IsPMF p) {n : ℕ} {δ : ℝ}
    {x : Fin n → α} (hx : x ∈ l1TypicalSet p n δ) :
    exp (-(n * (entropy p + δ * maxNegLog p))) ≤ iidPMF p n x ∧
      iidPMF p n x ≤ exp (-(n * (entropy p - δ * maxNegLog p))) := by
  have hpos := iidPMF_pos_of_mem_l1TypicalSet hp hx
  have h₁ := neg_log_iidPMF_eq hpos.ne'
  have h₂ := abs_le.1 (abs_sum_deviation_le hp hx)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rw [← le_log_iff_exp_le hpos]
    have := mul_le_mul_of_nonneg_left h₂.2 hn
    nlinarith
  · rw [← log_le_iff_le_exp hpos]
    have := mul_le_mul_of_nonneg_left h₂.1 hn
    nlinarith

/-- **Proposition 6.5.** Strong typicality implies weak typicality:
`T_{[X]δ}ⁿ ⊆ W_{[X]η}ⁿ` with `η = δ (-log minₓ p(x))`. -/
theorem l1TypicalSet_subset_typicalSet {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (δ : ℝ) :
    l1TypicalSet p n δ ⊆ typicalSet p n (δ * maxNegLog p) :=
  fun _ hx => mem_typicalSet.2 (exp_le_iidPMF_of_mem_l1TypicalSet hp hx)

/-- The per-symbol typical set of the library is contained in `l1TypicalSet`. -/
lemma strongTypicalSet_subset_l1TypicalSet {p : α → ℝ} (hp : IsPMF p) {n : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) : strongTypicalSet p n δ ⊆ l1TypicalSet p n δ := by
  intro x hx
  have h := mem_strongTypicalSet.1 hx
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hp
  refine mem_l1TypicalSet.2 ⟨fun a ha => (h a).2 ha, ?_⟩
  calc ∑ a, |typeOf x a - p a| ≤ ∑ _a : α, δ / Fintype.card α := by
        refine sum_le_sum fun a _ => ?_
        rcases (hp.nonneg a).eq_or_lt with h₀ | h₀
        · simp only [typeOf, (h a).2 h₀.symm, ← h₀]
          simpa using div_nonneg hδ hc.le
        · exact ((h a).1 h₀).le
    _ = δ := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        field_simp

/-- `Pr{X ∈ T_{[X]δ}ⁿ} → 1`. -/
theorem tendsto_prob_l1TypicalSet {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => prob (iidPMF p n) (l1TypicalSet p n δ)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_prob_strongTypicalSet hp hδ)
    tendsto_const_nhds (fun n => ?_) (fun n => prob_le_one (iidPMF_isPMF hp n) _)
  exact prob_mono (iidPMF_isPMF hp n).nonneg (strongTypicalSet_subset_l1TypicalSet hp hδ.le)

/-- The remark after Theorem 6.2: for `δ > 0` and `n` sufficiently large, there is a strongly
`δ`-typical sequence. -/
theorem eventually_l1TypicalSet_nonempty {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, (l1TypicalSet p n δ).Nonempty := by
  filter_upwards [(tendsto_prob_l1TypicalSet hp hδ).eventually (lt_mem_nhds one_pos)] with n hn
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  rw [h, prob_empty] at hn
  exact lt_irrefl _ hn

/-- **Theorem 6.2 (2).** For `n` sufficiently large, `Pr{X ∈ T_{[X]δ}ⁿ} > 1 - δ`. -/
theorem eventually_prob_l1TypicalSet_gt {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, 1 - δ < prob (iidPMF p n) (l1TypicalSet p n δ) :=
  (tendsto_prob_l1TypicalSet hp hδ).eventually (lt_mem_nhds (by linarith))

/-- **Theorem 6.2 (3), the upper bound.** `|T_{[X]δ}ⁿ| ≤ e^{n(H(X) + η)}`, for every `n`. -/
theorem card_l1TypicalSet_le {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (δ : ℝ) :
    ((l1TypicalSet p n δ).card : ℝ) ≤ exp (n * (entropy p + δ * maxNegLog p)) := by
  have h₁ : ((l1TypicalSet p n δ).card : ℝ) * exp (-(n * (entropy p + δ * maxNegLog p))) ≤
      prob (iidPMF p n) (l1TypicalSet p n δ) :=
    card_mul_le_prob fun x hx => (exp_le_iidPMF_of_mem_l1TypicalSet hp hx).1
  have h₂ := prob_le_one (iidPMF_isPMF hp n) (l1TypicalSet p n δ)
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)] at h₁
  exact h₁.trans (mul_le_of_le_one_left (exp_pos _).le h₂)

/-- **Theorem 6.2 (3), the lower bound.** For `n` sufficiently large,
`(1 - δ) e^{n(H(X) - η)} ≤ |T_{[X]δ}ⁿ|`. -/
theorem eventually_card_l1TypicalSet_ge {p : α → ℝ} (hp : IsPMF p) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (1 - δ) * exp (n * (entropy p - δ * maxNegLog p)) ≤ (l1TypicalSet p n δ).card := by
  filter_upwards [eventually_prob_l1TypicalSet_gt hp hδ] with n hn
  have h₁ : prob (iidPMF p n) (l1TypicalSet p n δ) ≤
      (l1TypicalSet p n δ).card * exp (-(n * (entropy p - δ * maxNegLog p))) :=
    prob_le_card_mul fun x hx => (exp_le_iidPMF_of_mem_l1TypicalSet hp hx).2
  have h₂ : (1 - δ) ≤
      (l1TypicalSet p n δ).card * exp (-(n * (entropy p - δ * maxNegLog p))) := by linarith
  rwa [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)] at h₂

/-! ### The exponential bound -/

/-- **Lemma 6.4, (6.38).** The lower tail of the Chernoff bound: for `s ≥ 0`,
`Pr{Y ≤ a} ≤ e^{sa} E e^{-sY}`. -/
theorem prob_le_le_exp_mul_expect {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (Y : Ω → ℝ) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    prob μ (univ.filter fun ω => Y ω ≤ a) ≤ exp (s * a) * expect μ (fun ω => exp (-s * Y ω)) := by
  have h := prob_ge_le_exp_mul_expect hμ (fun ω => -Y ω) (-a) hs
  simp only [neg_le_neg_iff, mul_neg, neg_neg] at h
  simpa only [neg_mul] using h

open Classical in
/-- (6.45)–(6.47): `E e^{t N(a; X)} ≤ e^{n p(a) (e^t - 1)}`. -/
lemma expect_exp_symbolCount_le {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (a : α) (t : ℝ) :
    expect (iidPMF p n) (fun x => exp (t * symbolCount x a)) ≤
      exp (n * (p a * (exp t - 1))) := by
  have h₁ : ∀ x : Fin n → α, exp (t * symbolCount x a) =
      ∏ i, (fun (_ : Fin n) b => if b = a then exp t else 1) i (x i) := by
    intro x
    rw [symbolCount_eq_sum, mul_sum, exp_sum]
    refine prod_congr rfl fun i _ => ?_
    by_cases h : x i = a <;> simp [h]
  have h₂ : expect p (fun b => if b = a then exp t else 1) = 1 + p a * (exp t - 1) := by
    have h₃ : ∀ b, (if b = a then exp t else 1) * p b =
        p b + (if b = a then p a * (exp t - 1) else 0) := by
      intro b
      split_ifs with h
      · rw [h]; ring
      · ring
    rw [expect, sum_congr rfl fun b _ => h₃ b, sum_add_distrib, hp.sum_eq_one]
    simp
  rw [show (fun x : Fin n → α => exp (t * symbolCount x a)) = _ from funext h₁,
    expect_iidPMF_prod p (fun (_ : Fin n) b => if b = a then exp t else 1)]
  simp only [h₂, prod_const, card_univ, Fintype.card_fin]
  have hnn : 0 ≤ 1 + p a * (exp t - 1) := by
    have := hp.nonneg a
    have := hp.le_one a
    nlinarith [exp_pos t]
  calc (1 + p a * (exp t - 1)) ^ n ≤ exp (p a * (exp t - 1)) ^ n :=
        pow_le_pow_left₀ hnn (by linarith [add_one_le_exp (p a * (exp t - 1))]) n
    _ = exp (n * (p a * (exp t - 1))) := by rw [← exp_natCast_mul]

/-- The Chernoff exponent `s (δ - s) ≥ s δ / 2` used in the proof of Theorem 6.3, with
`s = min (1, δ / 2)`. -/
def chernoffRate (δ : ℝ) : ℝ := min 1 (δ / 2) * (δ / 2)

lemma chernoffRate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < chernoffRate δ :=
  mul_pos (lt_min one_pos (by linarith)) (by linarith)

/-- (6.44)–(6.57): `Pr{N(a; X) ≥ n (p(a) + δ)} ≤ e^{-n ρ(δ)}`. -/
lemma prob_symbolCount_ge_le {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (a : α) {δ : ℝ} (hδ : 0 < δ) :
    prob (iidPMF p n) (univ.filter fun x => n * (p a + δ) ≤ symbolCount x a) ≤
      exp (-(n * chernoffRate δ)) := by
  set s := min 1 (δ / 2) with hs_def
  have hs : 0 < s := lt_min one_pos (by linarith)
  have hs₁ : s ≤ 1 := min_le_left _ _
  have hs₂ : s ≤ δ / 2 := min_le_right _ _
  have hμ := (iidPMF_isPMF hp n).nonneg
  have h₁ := prob_ge_le_exp_mul_expect hμ (fun x => (symbolCount x a : ℝ)) (n * (p a + δ)) hs.le
  have h₂ := expect_exp_symbolCount_le hp n a s
  have h₃ := abs_le.1 (abs_exp_sub_one_sub_id_le (x := s) (by rw [abs_of_pos hs]; exact hs₁))
  refine h₁.trans ?_
  calc exp (-(s * (n * (p a + δ)))) * expect (iidPMF p n) (fun x => exp (s * symbolCount x a))
      ≤ exp (-(s * (n * (p a + δ)))) * exp (n * (p a * (exp s - 1))) :=
        mul_le_mul_of_nonneg_left h₂ (exp_pos _).le
    _ = exp (-(n * (s * (p a + δ) - p a * (exp s - 1)))) := by
        rw [← exp_add]; congr 1; ring
    _ ≤ exp (-(n * chernoffRate δ)) := by
        refine exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)))
        have hp₀ := hp.nonneg a
        have hp₁ := hp.le_one a
        have h₄ : p a * (exp s - 1) ≤ p a * (s + s ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [h₃.2]) hp₀
        have h₅ : p a * s ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
        have h₆ : s * (δ / 2) ≤ s * (δ - s) := mul_le_mul_of_nonneg_left (by linarith) hs.le
        rw [chernoffRate, ← hs_def]
        nlinarith

/-- (6.58)–(6.65): `Pr{N(a; X) ≤ n (p(a) - δ)} ≤ e^{-n ρ(δ)}`. -/
lemma prob_symbolCount_le_le {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (a : α) {δ : ℝ} (hδ : 0 < δ) :
    prob (iidPMF p n) (univ.filter fun x => (symbolCount x a : ℝ) ≤ n * (p a - δ)) ≤
      exp (-(n * chernoffRate δ)) := by
  set s := min 1 (δ / 2) with hs_def
  have hs : 0 < s := lt_min one_pos (by linarith)
  have hs₁ : s ≤ 1 := min_le_left _ _
  have hs₂ : s ≤ δ / 2 := min_le_right _ _
  have hμ := (iidPMF_isPMF hp n).nonneg
  have h₁ := prob_le_le_exp_mul_expect hμ (fun x => (symbolCount x a : ℝ)) (n * (p a - δ)) hs.le
  have h₂ := expect_exp_symbolCount_le hp n a (-s)
  have h₃ := abs_le.1 (abs_exp_sub_one_sub_id_le (x := -s)
    (by rw [abs_neg, abs_of_pos hs]; exact hs₁))
  refine h₁.trans ?_
  calc exp (s * (n * (p a - δ))) * expect (iidPMF p n) (fun x => exp (-s * symbolCount x a))
      ≤ exp (s * (n * (p a - δ))) * exp (n * (p a * (exp (-s) - 1))) :=
        mul_le_mul_of_nonneg_left h₂ (exp_pos _).le
    _ = exp (-(n * (-(s * (p a - δ)) - p a * (exp (-s) - 1)))) := by
        rw [← exp_add]; congr 1; ring
    _ ≤ exp (-(n * chernoffRate δ)) := by
        refine exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)))
        have hp₀ := hp.nonneg a
        have hp₁ := hp.le_one a
        have h₄ : p a * (exp (-s) - 1) ≤ p a * (-s + s ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [h₃.2]) hp₀
        have h₅ : p a * s ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
        have h₆ : s * (δ / 2) ≤ s * (δ - s) := mul_le_mul_of_nonneg_left (by linarith) hs.le
        rw [chernoffRate, ← hs_def]
        nlinarith

/-- (6.67)–(6.72): `Pr{|N(a; X)/n - p(a)| ≥ δ} ≤ 2 e^{-n ρ(δ)}`. -/
lemma prob_abs_typeOf_sub_ge_le {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (hn : 0 < n) (a : α) {δ : ℝ}
    (hδ : 0 < δ) :
    prob (iidPMF p n) (univ.filter fun x => δ ≤ |typeOf x a - p a|) ≤
      2 * exp (-(n * chernoffRate δ)) := by
  classical
  have hμ := (iidPMF_isPMF hp n).nonneg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : (univ.filter fun x : Fin n → α => δ ≤ |typeOf x a - p a|) ⊆
      (univ.filter fun x => n * (p a + δ) ≤ symbolCount x a) ∪
        (univ.filter fun x => (symbolCount x a : ℝ) ≤ n * (p a - δ)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    have hN := symbolCount_eq_mul_typeOf n x a
    rcases le_abs.1 hx with h | h
    · left; rw [hN]; exact mul_le_mul_of_nonneg_left (by linarith) hn'.le
    · right; rw [hN]; exact mul_le_mul_of_nonneg_left (by linarith) hn'.le
  calc _ ≤ _ := prob_mono hμ hsub
    _ ≤ _ := prob_union_le hμ _ _
    _ ≤ exp (-(n * chernoffRate δ)) + exp (-(n * chernoffRate δ)) :=
        add_le_add (prob_symbolCount_ge_le hp n a hδ) (prob_symbolCount_le_le hp n a hδ)
    _ = _ := by ring

/-- **Theorem 6.3.** There is `φ > 0` such that `Pr{X ∉ T_{[X]δ}ⁿ} < e^{-nφ}` for `n` sufficiently
large. -/
theorem exists_eventually_prob_l1TypicalSet_compl_lt [DecidableEq α] {p : α → ℝ} (hp : IsPMF p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ > 0, ∀ᶠ n : ℕ in atTop, prob (iidPMF p n) (l1TypicalSet p n δ)ᶜ < exp (-(n * φ)) := by
  classical
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hp
  set δ' := δ / Fintype.card α with hδ'_def
  have hδ' : 0 < δ' := div_pos hδ hc
  set ρ := chernoffRate δ' with hρ_def
  have hρ : 0 < ρ := chernoffRate_pos hδ'
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  -- `2 |𝒳| < e^{n ρ / 2}` for `n` large.
  have hlim : Tendsto (fun n : ℕ => exp (n * (ρ / 2))) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (half_pos hρ))
  filter_upwards [hlim.eventually_gt_atTop (2 * (Fintype.card α : ℝ)), eventually_gt_atTop 0]
    with n hlarge hn
  have hμ := iidPMF_isPMF hp n
  -- Outside of a set of probability zero, a non-typical sequence has a large deviation.
  have hsub : ∀ x ∈ (l1TypicalSet p n δ)ᶜ, iidPMF p n x ≠ 0 →
      x ∈ univ.biUnion fun a => univ.filter fun x : Fin n → α => δ' ≤ |typeOf x a - p a| := by
    intro x hx hne
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    by_contra! hlt
    refine (mem_compl.1 hx) (mem_l1TypicalSet.2 ⟨fun a ha => ?_, ?_⟩)
    · by_contra hN
      obtain ⟨i, hi⟩ : ∃ i, x i = a := by
        by_contra! hall
        exact hN (symbolCount_eq_zero_of_forall_ne hall)
      exact hne (prod_eq_zero (mem_univ i) (by rw [hi]; exact ha))
    · calc ∑ a, |typeOf x a - p a| ≤ ∑ _a : α, δ' := sum_le_sum fun a _ => (hlt a).le
        _ = δ := by
          rw [sum_const, card_univ, nsmul_eq_mul, hδ'_def]
          field_simp
  have h₁ : prob (iidPMF p n) (l1TypicalSet p n δ)ᶜ ≤
      prob (iidPMF p n) (univ.biUnion fun a =>
        univ.filter fun x : Fin n → α => δ' ≤ |typeOf x a - p a|) :=
    prob_le_prob_of_ae hμ.nonneg hsub
  have h₂ := prob_biUnion_le hμ.nonneg univ fun a =>
    univ.filter fun x : Fin n → α => δ' ≤ |typeOf x a - p a|
  have h₃ : ∑ a : α, prob (iidPMF p n) (univ.filter fun x : Fin n → α => δ' ≤ |typeOf x a - p a|) ≤
      Fintype.card α * (2 * exp (-(n * ρ))) := by
    calc _ ≤ ∑ _a : α, 2 * exp (-(n * ρ)) :=
          sum_le_sum fun a _ => prob_abs_typeOf_sub_ge_le hp hn a hδ'
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  refine (h₁.trans (h₂.trans h₃)).trans_lt ?_
  have h₄ : exp (-(n * ρ)) = exp (-(n * (ρ / 2))) * exp (-(n * (ρ / 2))) := by
    rw [← exp_add]; congr 1; ring
  have h₅ : exp (-(n * (ρ / 2))) * exp (n * (ρ / 2)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  have h₆ := exp_pos (-(n * (ρ / 2)))
  rw [h₄]
  nlinarith [mul_lt_mul_of_pos_right hlarge h₆]

/-! ### Preservation and consistency -/

/-- **Theorem 6.8 (Preservation).** If `Y = f(X)` and `x` is strongly `δ`-typical for `X`, then
`f(x)` is strongly `δ`-typical for `Y`. -/
theorem comp_mem_l1TypicalSet {p : α → ℝ} (hp : IsPMF p) {n : ℕ} {δ : ℝ} {x : Fin n → α}
    (hx : x ∈ l1TypicalSet p n δ) (f : α → β) : f ∘ x ∈ l1TypicalSet (dist p f) n δ := by
  classical
  obtain ⟨h₁, h₂⟩ := mem_l1TypicalSet.1 hx
  refine mem_l1TypicalSet.2 ⟨fun b hb => ?_, ?_⟩
  · -- A symbol `b` outside the support of `Y` has no preimage in the sequence.
    refine symbolCount_eq_zero_of_forall_ne fun i hi => ?_
    have ha : p (x i) = 0 := by
      have h₃ := (sum_eq_zero_iff_of_nonneg fun a _ => by
        split_ifs
        · exact hp.nonneg a
        · exact le_rfl).1 hb (x i) (mem_univ _)
      simpa [show f (x i) = b from hi] using h₃
    exact apply_ne_of_symbolCount_eq_zero (h₁ _ ha) i rfl
  · refine le_trans ?_ h₂
    calc ∑ b, |typeOf (f ∘ x) b - dist p f b|
        ≤ ∑ b, ∑ a, if f a = b then |typeOf x a - p a| else 0 := by
          refine sum_le_sum fun b _ => ?_
          rw [typeOf_comp, dist, dist, ← sum_sub_distrib]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
          split_ifs <;> simp
      _ = ∑ a, |typeOf x a - p a| := by
          rw [sum_comm]
          simp

/-! ### Joint typicality -/

open Classical in
/-- **Definition 6.6.** The strongly jointly typical set `T_{[XY]δ}ⁿ`: the pairs of sequences whose
sequence of pairs is strongly `δ`-typical for `q`. -/
def jointL1TypicalSet (q : α × β → ℝ) (n : ℕ) (δ : ℝ) : Finset ((Fin n → α) × (Fin n → β)) :=
  univ.filter fun z => zipSeq z.1 z.2 ∈ l1TypicalSet q n δ

lemma mem_jointL1TypicalSet {q : α × β → ℝ} {n : ℕ} {δ : ℝ} {z : (Fin n → α) × (Fin n → β)} :
    z ∈ jointL1TypicalSet q n δ ↔ zipSeq z.1 z.2 ∈ l1TypicalSet q n δ := by
  classical
  simp [jointL1TypicalSet]

/-- **Theorem 6.7 (Consistency).** If `(x, y)` is strongly jointly `δ`-typical, then `x` is strongly
`δ`-typical. -/
theorem fst_mem_l1TypicalSet {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {δ : ℝ}
    {z : (Fin n → α) × (Fin n → β)} (hz : z ∈ jointL1TypicalSet q n δ) :
    z.1 ∈ l1TypicalSet (margFst q) n δ :=
  comp_mem_l1TypicalSet hq (mem_jointL1TypicalSet.1 hz) Prod.fst

/-- **Theorem 6.7 (Consistency).** If `(x, y)` is strongly jointly `δ`-typical, then `y` is strongly
`δ`-typical. -/
theorem snd_mem_l1TypicalSet {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {δ : ℝ}
    {z : (Fin n → α) × (Fin n → β)} (hz : z ∈ jointL1TypicalSet q n δ) :
    z.2 ∈ l1TypicalSet (margSnd q) n δ :=
  comp_mem_l1TypicalSet hq (mem_jointL1TypicalSet.1 hz) Prod.snd

/-- `(x, y) ↦ ((x₁, y₁), …, (xₙ, yₙ))` is a bijection from `T_{[XY]δ}ⁿ` to the typical set of the
pairs. -/
lemma card_jointL1TypicalSet (q : α × β → ℝ) (n : ℕ) (δ : ℝ) :
    (jointL1TypicalSet q n δ).card = (l1TypicalSet q n δ).card := by
  classical
  refine card_bij (fun z _ => zipSeq z.1 z.2) (fun z hz => mem_jointL1TypicalSet.1 hz)
    (fun z₁ _ z₂ _ h => zipSeq_injective n h) (fun w hw => ?_)
  refine ⟨(Prod.fst ∘ w, Prod.snd ∘ w), mem_jointL1TypicalSet.2 hw, rfl⟩

/-- The probability of `T_{[XY]δ}ⁿ` is that of the typical set of the pairs. -/
lemma prob_jointL1TypicalSet (q : α × β → ℝ) (n : ℕ) (δ : ℝ) :
    prob (jointIid q n) (jointL1TypicalSet q n δ) = prob (iidPMF q n) (l1TypicalSet q n δ) := by
  classical
  have h := sum_jointIid q n fun w => if w ∈ l1TypicalSet q n δ then 1 else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [prob, prob, jointL1TypicalSet, sum_filter, h, ← sum_filter, filter_mem_eq_inter, univ_inter]

/-- **Theorem 6.9 (1).** If `(x, y)` is strongly jointly `δ`-typical, then
`e^{-n(H(X, Y) + λ)} ≤ p(x, y) ≤ e^{-n(H(X, Y) - λ)}`, with `λ = δ (-log min p(x, y))`. -/
theorem exp_le_jointIid_of_mem_jointL1TypicalSet {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {δ : ℝ}
    {z : (Fin n → α) × (Fin n → β)} (hz : z ∈ jointL1TypicalSet q n δ) :
    exp (-(n * (entropy q + δ * maxNegLog q))) ≤ jointIid q n z ∧
      jointIid q n z ≤ exp (-(n * (entropy q - δ * maxNegLog q))) :=
  exp_le_iidPMF_of_mem_l1TypicalSet hq (mem_jointL1TypicalSet.1 hz)

/-- **Theorem 6.9 (2).** For `n` sufficiently large, `Pr{(X, Y) ∈ T_{[XY]δ}ⁿ} > 1 - δ`. -/
theorem eventually_prob_jointL1TypicalSet_gt {q : α × β → ℝ} (hq : IsPMF q) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, 1 - δ < prob (jointIid q n) (jointL1TypicalSet q n δ) := by
  simp only [prob_jointL1TypicalSet]
  exact eventually_prob_l1TypicalSet_gt hq hδ

/-- **Theorem 6.9 (3), the upper bound.** `|T_{[XY]δ}ⁿ| ≤ e^{n(H(X, Y) + λ)}`, for every `n`. -/
theorem card_jointL1TypicalSet_le {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) (δ : ℝ) :
    ((jointL1TypicalSet q n δ).card : ℝ) ≤ exp (n * (entropy q + δ * maxNegLog q)) := by
  rw [card_jointL1TypicalSet]
  exact card_l1TypicalSet_le hq n δ

/-- **Theorem 6.9 (3), the lower bound.** For `n` sufficiently large,
`(1 - δ) e^{n(H(X, Y) - λ)} ≤ |T_{[XY]δ}ⁿ|`. -/
theorem eventually_card_jointL1TypicalSet_ge {q : α × β → ℝ} (hq : IsPMF q) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (1 - δ) * exp (n * (entropy q - δ * maxNegLog q)) ≤ (jointL1TypicalSet q n δ).card := by
  simp only [card_jointL1TypicalSet]
  exact eventually_card_l1TypicalSet_ge hq hδ

end InfoTheory
