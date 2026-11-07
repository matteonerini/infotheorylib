/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.SupportMixture
public import InfoTheoryLib.Typicality.L1

/-!
# Conditional strong typicality in variational distance

For a typical `x`, the sequences `y` that are strongly jointly typical with `x` form the set
`T_{[Y|X]δ}ⁿ(x)`. If this set is nonempty, it has about `e^{nH(Y|X)}` elements. The structure of the
strong joint typicality array gives a typicality proof of the basic inequality
`H(X, Y | Z) ≤ H(X | Z) + H(Y | Z)`.

## Main definitions

* `condL1TypicalSet q n δ x`: the set `T_{[Y|X]δ}ⁿ(x)`, (6.110).
* `l1TypicalProjection q n δ`: the set `S_{[X]δ}ⁿ` of the `x` with `T_{[Y|X]δ}ⁿ(x)` nonempty.

## Main statements

* `card_condL1TypicalSet_le`, `eventually_exp_le_card_condL1TypicalSet`,
  `exists_card_condL1TypicalSet_bounds`: Theorem 6.10.
* `eventually_card_l1TypicalProjection_ge`: Corollary 6.12.
* `eventually_prob_l1TypicalProjection_gt`: Proposition 6.13.
* `prob_indep_jointL1TypicalSet_le`: Lemma 7.17.
* `card_condL1TypicalSet_pair_le`: (6.153)–(6.154).
* `condEntropy_le_add_of_typicality`: (6.155)–(6.156).
* `card_typeClass_zip_le`: a joint type class is at most the type class of `x` times the
  sequences `y` that complete `x` to that joint type.

## Implementation notes

The book bounds the size of a conditional type class with the factorial bounds of Lemma 6.11, and
leaves a degenerate case to the reader. We use `card_typeClass_zip_le` and the bounds on type
classes of `Statistics.Types` instead, which needs no special case.

Logarithms are natural. The conditional entropy `H(Y|X)` is `H[Prod.snd | Prod.fst ; q]`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 6.3, 6.4 and 7.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

open Classical in
/-- **(6.110)** The set `T_{[Y|X]δ}ⁿ(x)` of the `y ∈ T_{[Y]δ}ⁿ` with `(x, y) ∈ T_{[XY]δ}ⁿ`. -/
def condL1TypicalSet (q : α × β → ℝ) (n : ℕ) (δ : ℝ) (x : Fin n → α) : Finset (Fin n → β) :=
  univ.filter fun y => y ∈ l1TypicalSet (margSnd q) n δ ∧ (x, y) ∈ jointL1TypicalSet q n δ

lemma mem_condL1TypicalSet {q : α × β → ℝ} {n : ℕ} {δ : ℝ} {x : Fin n → α} {y : Fin n → β} :
    y ∈ condL1TypicalSet q n δ x ↔
      y ∈ l1TypicalSet (margSnd q) n δ ∧ (x, y) ∈ jointL1TypicalSet q n δ := by
  classical
  simp [condL1TypicalSet]

/-- `H(Y|X) = H(X, Y) - H(X)` for a joint pmf. -/
lemma condEntropy_snd_fst {q : α × β → ℝ} (hq : IsPMF q) :
    H[Prod.snd | Prod.fst ; q] = entropy q - entropy (margFst q) := by
  rw [condEntropy_eq_sub hq, entropyRV, dist_pair_fst_snd, entropyRV]

/-- (6.121): `p(x) = ∑_y p(x, y)`. -/
lemma sum_jointIid_right (q : α × β → ℝ) {n : ℕ} (x : Fin n → α) :
    ∑ y, jointIid q n (x, y) = iidPMF (margFst q) n x := by
  classical
  simp only [jointIid, iidPMF, zipSeq]
  rw [← Fintype.prod_sum fun i b => q (x i, b)]
  exact prod_congr rfl fun i _ => (dist_fst q (x i)).symm

/-- **Theorem 6.10, the upper bound, (6.120)–(6.125).** For `x ∈ T_{[X]δ}ⁿ`,
`|T_{[Y|X]δ}ⁿ(x)| ≤ e^{n(H(Y|X) + ν)}` with `ν = δ (M_X + M_{XY})`, for every `n`. -/
theorem card_condL1TypicalSet_le {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {δ : ℝ} {x : Fin n → α}
    (hx : x ∈ l1TypicalSet (margFst q) n δ) :
    ((condL1TypicalSet q n δ x).card : ℝ) ≤
      exp (n * (H[Prod.snd | Prod.fst ; q] + δ * (maxNegLog (margFst q) + maxNegLog q))) := by
  have h₁ : ((condL1TypicalSet q n δ x).card : ℝ) * exp (-(n * (entropy q + δ * maxNegLog q))) ≤
      ∑ y ∈ condL1TypicalSet q n δ x, jointIid q n (x, y) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun y hy => (exp_le_jointIid_of_mem_jointL1TypicalSet hq
      (mem_condL1TypicalSet.1 hy).2).1
  have h₂ : ∑ y ∈ condL1TypicalSet q n δ x, jointIid q n (x, y) ≤ iidPMF (margFst q) n x := by
    rw [← sum_jointIid_right]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun y _ _ => jointIid_nonneg hq.nonneg n _
  have h₃ := (exp_le_iidPMF_of_mem_l1TypicalSet (hq.dist Prod.fst) hx).2
  have h₄ := h₁.trans (h₂.trans h₃)
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _), ← exp_add] at h₄
  refine h₄.trans_eq ?_
  rw [condEntropy_snd_fst hq]
  congr 1
  ring

/-! ### Counting with types -/

omit [Fintype α] in
lemma symbolCount_eq_of_typeOf_eq {n : ℕ} {x y : Fin n → α} (h : typeOf x = typeOf y) (a : α) :
    symbolCount x a = symbolCount y a := by
  have h₁ := symbolCount_eq_mul_typeOf n x a
  have h₂ := symbolCount_eq_mul_typeOf n y a
  rw [h] at h₁
  exact_mod_cast h₁.trans h₂.symm

/-- Typicality only depends on the type of a sequence. -/
lemma mem_l1TypicalSet_of_typeOf_eq {p : α → ℝ} {n : ℕ} {δ : ℝ} {x y : Fin n → α}
    (h : typeOf y = typeOf x) (hx : x ∈ l1TypicalSet p n δ) : y ∈ l1TypicalSet p n δ := by
  obtain ⟨h₁, h₂⟩ := mem_l1TypicalSet.1 hx
  exact mem_l1TypicalSet.2 ⟨fun a ha => by rw [symbolCount_eq_of_typeOf_eq h a]; exact h₁ a ha,
    by rwa [h]⟩

open Classical in
/-- A joint type class has at most `|T(Pₓ)|` times as many elements as there are sequences `y` that
complete `x` to that joint type. In fact equality holds, since the rearrangements of `x` have
fibers of the same size. -/
theorem card_typeClass_zip_le {n : ℕ} (x : Fin n → α) (y₀ : Fin n → β) :
    (typeClass (typeOf (zipSeq x y₀)) n).card ≤ (typeClass (typeOf x) n).card *
      (univ.filter fun y : Fin n → β => typeOf (zipSeq x y) = typeOf (zipSeq x y₀)).card := by
  set P := typeOf (zipSeq x y₀) with hP
  have hmaps : ∀ z ∈ typeClass P n, Prod.fst ∘ z ∈ typeClass (typeOf x) n := by
    intro z hz
    refine mem_typeClass.2 (funext fun a => ?_)
    rw [typeOf_comp, mem_typeClass.1 hz, hP, ← typeOf_comp]
    rfl
  rw [card_eq_sum_card_fiberwise hmaps, ← smul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun x' hx' => ?_
  obtain ⟨τ, hτ⟩ := exists_perm_of_symbolCount_eq
    (symbolCount_eq_of_typeOf_eq (mem_typeClass.1 hx').symm)
  refine card_le_card_of_injOn (fun z => Prod.snd ∘ z ∘ τ.symm) (fun z hz => ?_) ?_
  · obtain ⟨hz₁, hz₂⟩ := mem_filter.1 (mem_coe.1 hz)
    refine mem_coe.2 (mem_filter.2 ⟨mem_univ _, ?_⟩)
    have h : zipSeq x (Prod.snd ∘ z ∘ τ.symm) = z ∘ τ.symm := by
      funext i
      have h₁ := congrFun (hz₂.trans hτ) (τ.symm i)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at h₁
      exact Prod.ext h₁.symm rfl
    rw [h, typeOf_comp_perm]
    exact mem_typeClass.1 hz₁
  · intro z₁ hz₁ z₂ hz₂ h
    obtain ⟨-, h₁⟩ := mem_filter.1 (mem_coe.1 hz₁)
    obtain ⟨-, h₂⟩ := mem_filter.1 (mem_coe.1 hz₂)
    funext i
    have h₃ := congrFun h (τ i)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at h₃
    exact Prod.ext (congrFun (h₁.trans h₂.symm) i) h₃

open Classical in
/-- The number of sequences `y` completing `x` to the joint type of `(x, y₀)` is at least
`e^{n(H(Pₓᵧ) - H(Pₓ))} / (n + 1)^{|𝒳||𝒴|}`. -/
theorem exp_div_le_card_completions {n : ℕ} (hn : 0 < n) (x : Fin n → α) (y₀ : Fin n → β) :
    exp (n * (entropy (typeOf (zipSeq x y₀)) - entropy (typeOf x))) /
        (n + 1) ^ Fintype.card (α × β) ≤
      ((univ.filter fun y : Fin n → β => typeOf (zipSeq x y) = typeOf (zipSeq x y₀)).card : ℝ) := by
  set C := (univ.filter fun y : Fin n → β => typeOf (zipSeq x y) = typeOf (zipSeq x y₀)).card
  have h₁ := exp_div_le_card_typeClass hn (zipSeq x y₀)
  have h₂ : ((typeClass (typeOf (zipSeq x y₀)) n).card : ℝ) ≤
      (typeClass (typeOf x) n).card * C := by exact_mod_cast card_typeClass_zip_le x y₀
  have h₃ := mul_le_mul_of_nonneg_right (card_typeClass_le hn x) (Nat.cast_nonneg C)
  have h₄ : exp (n * (entropy (typeOf (zipSeq x y₀)) - entropy (typeOf x))) =
      exp (n * entropy (typeOf (zipSeq x y₀))) * exp (-(n * entropy (typeOf x))) := by
    rw [← exp_add]; congr 1; ring
  have hpow : (0 : ℝ) < (n + 1) ^ Fintype.card (α × β) := by positivity
  have h₅ := h₁.trans (h₂.trans h₃)
  rw [div_le_iff₀ hpow] at h₅ ⊢
  rw [h₄]
  calc exp (n * entropy (typeOf (zipSeq x y₀))) * exp (-(n * entropy (typeOf x)))
      ≤ (exp (n * entropy (typeOf x)) * C * (n + 1) ^ Fintype.card (α × β)) *
          exp (-(n * entropy (typeOf x))) :=
        mul_le_mul_of_nonneg_right h₅ (exp_pos _).le
    _ = C * (n + 1) ^ Fintype.card (α × β) * (exp (n * entropy (typeOf x)) *
          exp (-(n * entropy (typeOf x)))) := by ring
    _ = _ := by rw [← exp_add, add_neg_cancel, exp_zero, mul_one]

/-- Entropy is continuous in variational distance. -/
lemma exists_abs_entropy_sub_lt (p : α → ℝ) {ν : ℝ} (hν : 0 < ν) :
    ∃ δ > 0, ∀ P : α → ℝ, ∑ a, |P a - p a| ≤ δ → |entropy P - entropy p| < ν := by
  obtain ⟨δ', hδ', h⟩ := Metric.continuous_iff.1 (continuous_entropy (α := α)) p ν hν
  refine ⟨δ' / 2, half_pos hδ', fun P hP => ?_⟩
  have hd : Dist.dist P p ≤ δ' / 2 := (dist_pi_le_iff (half_pos hδ').le).2 fun a => by
    rw [Real.dist_eq]
    exact (single_le_sum (f := fun a => |P a - p a|) (fun _ _ => abs_nonneg _) (mem_univ a)).trans
      hP
  have := h P (hd.trans_lt (half_lt_self hδ'))
  rwa [Real.dist_eq] at this

/-- A polynomial in `n` is eventually below `e^{nc}`. -/
lemma eventually_add_one_pow_le_exp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ k ≤ exp (n * c) := by
  have h₁ : Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
    have h₂ := (isLittleO_log_id_atTop.comp_tendsto (tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop)).tendsto_div_nhds_zero
    have h₃ : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have h₄ := h₂.mul h₃
    simp only [mul_one] at h₄
    refine h₄.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [Function.comp_apply, id]
    field_simp
  have h₅ : ∀ᶠ n : ℕ in atTop, log ((n : ℝ) + 1) / n < c / (k + 1) :=
    h₁.eventually (gt_mem_nhds (by positivity))
  filter_upwards [h₅, eventually_gt_atTop 0] with n hn hn₀
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn₀
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hn', div_mul_eq_mul_div, lt_div_iff₀ hk] at hn
  rw [← log_le_iff_le_exp (by positivity), log_pow]
  have hlog : 0 ≤ log ((n : ℝ) + 1) := log_nonneg (by linarith [hn'.le])
  nlinarith

/-- **Theorem 6.10, the lower bound, (6.126)–(6.147).** For `ν > 0`, there is `δ₀ > 0` such that,
for `δ ≤ δ₀` and `n` sufficiently large, every `x` with `T_{[Y|X]δ}ⁿ(x)` nonempty has
`e^{n(H(Y|X) - ν)} ≤ |T_{[Y|X]δ}ⁿ(x)|`. -/
theorem eventually_exp_le_card_condL1TypicalSet {q : α × β → ℝ} (hq : IsPMF q) {ν : ℝ}
    (hν : 0 < ν) :
    ∃ δ₀ > 0, ∀ δ ≤ δ₀, ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → α,
      (condL1TypicalSet q n δ x).Nonempty →
        exp (n * (H[Prod.snd | Prod.fst ; q] - ν)) ≤ (condL1TypicalSet q n δ x).card := by
  classical
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_abs_entropy_sub_lt q (show 0 < ν / 3 by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_abs_entropy_sub_lt (margFst q) (show 0 < ν / 3 by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ => ?_⟩
  filter_upwards [eventually_add_one_pow_le_exp (Fintype.card (α × β))
    (show 0 < ν / 3 by linarith), eventually_gt_atTop 0] with n hpoly hn x hne
  obtain ⟨y₀, hy₀⟩ := hne
  have hz := (mem_condL1TypicalSet.1 hy₀).2
  have hx := fst_mem_l1TypicalSet hq hz
  have hzip := mem_jointL1TypicalSet.1 hz
  -- The entropies of the types are close to the true ones.
  have e₁ := abs_lt.1 (h₁ _ ((mem_l1TypicalSet.1 hzip).2.trans (hδ.trans (min_le_left _ _))))
  have e₂ := abs_lt.1 (h₂ _ ((mem_l1TypicalSet.1 hx).2.trans (hδ.trans (min_le_right _ _))))
  -- Every completion of `x` to the joint type of `(x, y₀)` is in the conditional set.
  have hsub : (univ.filter fun y : Fin n → β => typeOf (zipSeq x y) = typeOf (zipSeq x y₀)) ⊆
      condL1TypicalSet q n δ x := by
    intro y hy
    have hjoint : (x, y) ∈ jointL1TypicalSet q n δ :=
      mem_jointL1TypicalSet.2 (mem_l1TypicalSet_of_typeOf_eq (mem_filter.1 hy).2 hzip)
    exact mem_condL1TypicalSet.2 ⟨snd_mem_l1TypicalSet hq hjoint, hjoint⟩
  have hcard : ((univ.filter fun y : Fin n → β => typeOf (zipSeq x y) = typeOf (zipSeq x y₀)).card
      : ℝ) ≤ (condL1TypicalSet q n δ x).card := by exact_mod_cast card_le_card hsub
  refine le_trans ?_ ((exp_div_le_card_completions hn x y₀).trans hcard)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (0 : ℝ) < ((n : ℝ) + 1) ^ Fintype.card (α × β) := by positivity
  rw [le_div_iff₀ hpow]
  calc exp (n * (H[Prod.snd | Prod.fst ; q] - ν)) * ((n : ℝ) + 1) ^ Fintype.card (α × β)
      ≤ exp (n * (H[Prod.snd | Prod.fst ; q] - ν)) * exp (n * (ν / 3)) :=
        mul_le_mul_of_nonneg_left hpoly (exp_pos _).le
    _ = exp (n * (H[Prod.snd | Prod.fst ; q] - 2 * (ν / 3))) := by
        rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
        refine exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hn'.le)
        rw [condEntropy_snd_fst hq]
        linarith [e₁.1, e₂.2]

/-- **Theorem 6.10.** For `ν > 0`, there is `δ₀ > 0` such that, for `0 < δ ≤ δ₀` and `n`
sufficiently large, every `x ∈ T_{[X]δ}ⁿ` with `T_{[Y|X]δ}ⁿ(x)` nonempty has
`e^{n(H(Y|X) - ν)} ≤ |T_{[Y|X]δ}ⁿ(x)| ≤ e^{n(H(Y|X) + ν)}`. -/
theorem exists_card_condL1TypicalSet_bounds {q : α × β → ℝ} (hq : IsPMF q) {ν : ℝ} (hν : 0 < ν) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ᶠ n : ℕ in atTop, ∀ x ∈ l1TypicalSet (margFst q) n δ,
      (condL1TypicalSet q n δ x).Nonempty →
        exp (n * (H[Prod.snd | Prod.fst ; q] - ν)) ≤ (condL1TypicalSet q n δ x).card ∧
          ((condL1TypicalSet q n δ x).card : ℝ) ≤ exp (n * (H[Prod.snd | Prod.fst ; q] + ν)) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := eventually_exp_le_card_condL1TypicalSet hq hν
  have hM : 0 ≤ maxNegLog (margFst q) + maxNegLog q :=
    add_nonneg (maxNegLog_nonneg (hq.dist _)) (maxNegLog_nonneg hq)
  set M := maxNegLog (margFst q) + maxNegLog q with hM_def
  refine ⟨min δ₁ (ν / (M + 1)), lt_min hδ₁ (by positivity), fun δ hδ hle => ?_⟩
  filter_upwards [h₁ δ (hle.trans (min_le_left _ _))] with n hn x hx hne
  refine ⟨hn x hne, (card_condL1TypicalSet_le hq hx).trans
    (exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)))⟩
  have h₂ : δ ≤ ν / (M + 1) := hle.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h₂
  nlinarith

/-! ### The projection of the jointly typical set -/

open Classical in
/-- **Corollary 6.12.** The set `S_{[X]δ}ⁿ` of the `x ∈ T_{[X]δ}ⁿ` with `T_{[Y|X]δ}ⁿ(x)`
nonempty. -/
def l1TypicalProjection (q : α × β → ℝ) (n : ℕ) (δ : ℝ) : Finset (Fin n → α) :=
  (l1TypicalSet (margFst q) n δ).filter fun x => (condL1TypicalSet q n δ x).Nonempty

lemma mem_l1TypicalProjection {q : α × β → ℝ} {n : ℕ} {δ : ℝ} {x : Fin n → α} :
    x ∈ l1TypicalProjection q n δ ↔
      x ∈ l1TypicalSet (margFst q) n δ ∧ (condL1TypicalSet q n δ x).Nonempty := by
  classical
  simp [l1TypicalProjection]

/-- (6.149): the first sequence of a jointly typical pair is in `S_{[X]δ}ⁿ`. -/
lemma fst_mem_l1TypicalProjection {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {δ : ℝ}
    {z : (Fin n → α) × (Fin n → β)} (hz : z ∈ jointL1TypicalSet q n δ) :
    z.1 ∈ l1TypicalProjection q n δ :=
  mem_l1TypicalProjection.2 ⟨fst_mem_l1TypicalSet hq hz,
    z.2, mem_condL1TypicalSet.2 ⟨snd_mem_l1TypicalSet hq hz, hz⟩⟩

/-- **Corollary 6.12.** For `n` sufficiently large, `(1 - δ) e^{n(H(X) - ψ)} ≤ |S_{[X]δ}ⁿ|`, with
`ψ = δ (M_X + 2 M_{XY})`. The book's `ψ` also depends on `n`; this one does not. -/
theorem eventually_card_l1TypicalProjection_ge {q : α × β → ℝ} (hq : IsPMF q) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (1 - δ) * exp (n * (entropy (margFst q) - δ * (maxNegLog (margFst q) + 2 * maxNegLog q))) ≤
        (l1TypicalProjection q n δ).card := by
  classical
  filter_upwards [eventually_card_jointL1TypicalSet_ge hq hδ] with n hn
  set E := exp (n * (H[Prod.snd | Prod.fst ; q] + δ * (maxNegLog (margFst q) + maxNegLog q)))
    with hE
  -- (6.150): `|T_{[XY]δ}ⁿ| ≤ |S_{[X]δ}ⁿ| e^{n(H(Y|X) + ν)}`.
  have h₁ : ((jointL1TypicalSet q n δ).card : ℝ) ≤ (l1TypicalProjection q n δ).card * E := by
    have hmaps : ∀ z ∈ jointL1TypicalSet q n δ, z.1 ∈ l1TypicalProjection q n δ :=
      fun z hz => fst_mem_l1TypicalProjection hq hz
    rw [card_eq_sum_card_fiberwise hmaps]
    push_cast
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun x hx => ?_
    have h₂ : ((jointL1TypicalSet q n δ).filter fun z => z.1 = x).card ≤
        (condL1TypicalSet q n δ x).card := by
      refine card_le_card_of_injOn Prod.snd (fun z hz => ?_) ?_
      · obtain ⟨hz₁, rfl⟩ := mem_filter.1 (mem_coe.1 hz)
        exact mem_coe.2 (mem_condL1TypicalSet.2 ⟨snd_mem_l1TypicalSet hq hz₁, hz₁⟩)
      · intro z₁ hz₁ z₂ hz₂ h
        exact Prod.ext (((mem_filter.1 (mem_coe.1 hz₁)).2).trans
          ((mem_filter.1 (mem_coe.1 hz₂)).2).symm) h
    exact (Nat.cast_le.2 h₂).trans
      (card_condL1TypicalSet_le hq (mem_l1TypicalProjection.1 hx).1)
  have h₂ := hn.trans h₁
  have hE₀ : 0 < E := exp_pos _
  rw [← div_le_iff₀ hE₀] at h₂
  refine le_trans (le_of_eq ?_) h₂
  rw [mul_div_assoc, hE, ← exp_sub, condEntropy_snd_fst hq]
  congr 2
  ring

/-- **Proposition 6.13.** For `δ > 0` and `n` sufficiently large, `Pr{X ∈ S_{[X]δ}ⁿ} > 1 - δ`. -/
theorem eventually_prob_l1TypicalProjection_gt {q : α × β → ℝ} (hq : IsPMF q) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ n in atTop, 1 - δ < prob (iidPMF (margFst q) n) (l1TypicalProjection q n δ) := by
  classical
  filter_upwards [eventually_prob_jointL1TypicalSet_gt hq hδ] with n hn
  refine hn.trans_le ?_
  have h := sum_jointIid_fst q n fun x => if x ∈ l1TypicalProjection q n δ then 1 else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [prob, prob, ← univ_inter (l1TypicalProjection q n δ), ← filter_mem_eq_inter, sum_filter, ← h]
  rw [← sum_filter]
  refine sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
    fun z _ _ => jointIid_nonneg hq.nonneg n z
  exact mem_filter.2 ⟨mem_univ _, fst_mem_l1TypicalProjection hq hz⟩

/-! ### Independent sequences -/

/-- **Lemma 7.17, (7.136)–(7.145).** Let `(X', Y')` be `n` i.i.d. copies of a pair with `X'` and
`Y'` independent and with the marginals of `q`. Then
`Pr{(X', Y') ∈ T_{[XY]δ}ⁿ} ≤ e^{-n(I(X; Y) - τ)}`, with `τ = δ (M_{XY} + M_X + M_Y)`. -/
theorem prob_indep_jointL1TypicalSet_le {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) (δ : ℝ) :
    prob (fun z : (Fin n → α) × (Fin n → β) => iidPMF (margFst q) n z.1 * iidPMF (margSnd q) n z.2)
        (jointL1TypicalSet q n δ) ≤
      exp (-(n * (I[Prod.fst : Prod.snd ; q] -
        δ * (maxNegLog q + maxNegLog (margFst q) + maxNegLog (margSnd q))))) := by
  set A := exp (-(n * (entropy (margFst q) - δ * maxNegLog (margFst q))))
  set B := exp (-(n * (entropy (margSnd q) - δ * maxNegLog (margSnd q))))
  set C := exp (n * (entropy q + δ * maxNegLog q))
  have h₁ : ∀ z ∈ jointL1TypicalSet q n δ, iidPMF (margFst q) n z.1 * iidPMF (margSnd q) n z.2 ≤
      A * B := fun z hz =>
    mul_le_mul (exp_le_iidPMF_of_mem_l1TypicalSet (hq.dist _) (fst_mem_l1TypicalSet hq hz)).2
      (exp_le_iidPMF_of_mem_l1TypicalSet (hq.dist _) (snd_mem_l1TypicalSet hq hz)).2
      (iidPMF_nonneg (hq.dist _).nonneg _) (exp_pos _).le
  have h₂ := prob_le_card_mul h₁
  have h₃ := card_jointL1TypicalSet_le hq n δ
  refine h₂.trans ((mul_le_mul_of_nonneg_right h₃ (mul_pos (exp_pos _) (exp_pos _)).le).trans
    (le_of_eq ?_))
  rw [← exp_add, ← exp_add, mutualInfo_eq_add_sub hq, entropyRV, entropyRV, entropyRV,
    dist_pair_fst_snd]
  congr 1
  ring

/-! ### An interpretation of the basic inequalities -/

/-- The law of `(Z, X)` for a pmf of `(Z, (X, Y))`. -/
abbrev margLeft (r : γ × (α × β) → ℝ) : γ × α → ℝ := dist r fun w => (w.1, w.2.1)

/-- The law of `(Z, Y)` for a pmf of `(Z, (X, Y))`. -/
abbrev margRight (r : γ × (α × β) → ℝ) : γ × β → ℝ := dist r fun w => (w.1, w.2.2)

lemma margLeft_isPMF {r : γ × (α × β) → ℝ} (hr : IsPMF r) : IsPMF (margLeft r) := hr.dist _

lemma margRight_isPMF {r : γ × (α × β) → ℝ} (hr : IsPMF r) : IsPMF (margRight r) := hr.dist _

lemma mem_jointL1TypicalSet_margLeft {r : γ × (α × β) → ℝ} (hr : IsPMF r) {n : ℕ} {δ : ℝ}
    {z : Fin n → γ} {t : Fin n → α × β} (h : (z, t) ∈ jointL1TypicalSet r n δ) :
    (z, Prod.fst ∘ t) ∈ jointL1TypicalSet (margLeft r) n δ :=
  mem_jointL1TypicalSet.2 (comp_mem_l1TypicalSet hr (mem_jointL1TypicalSet.1 h) _)

lemma mem_jointL1TypicalSet_margRight {r : γ × (α × β) → ℝ} (hr : IsPMF r) {n : ℕ} {δ : ℝ}
    {z : Fin n → γ} {t : Fin n → α × β} (h : (z, t) ∈ jointL1TypicalSet r n δ) :
    (z, Prod.snd ∘ t) ∈ jointL1TypicalSet (margRight r) n δ :=
  mem_jointL1TypicalSet.2 (comp_mem_l1TypicalSet hr (mem_jointL1TypicalSet.1 h) _)

/-- **(6.153)–(6.154)** `|T_{[XY|Z]δ}ⁿ(z)| ≤ |T_{[X|Z]δ}ⁿ(z)| |T_{[Y|Z]δ}ⁿ(z)|`. -/
theorem card_condL1TypicalSet_pair_le {r : γ × (α × β) → ℝ} (hr : IsPMF r) {n : ℕ} {δ : ℝ}
    (z : Fin n → γ) :
    (condL1TypicalSet r n δ z).card ≤
      (condL1TypicalSet (margLeft r) n δ z).card * (condL1TypicalSet (margRight r) n δ z).card := by
  rw [← card_product]
  refine card_le_card_of_injOn (fun t => (Prod.fst ∘ t, Prod.snd ∘ t)) (fun t ht => ?_) ?_
  · have h := (mem_condL1TypicalSet.1 (mem_coe.1 ht)).2
    have h₁ := mem_jointL1TypicalSet_margLeft hr h
    have h₂ := mem_jointL1TypicalSet_margRight hr h
    exact mem_coe.2 (mem_product.2 ⟨mem_condL1TypicalSet.2
        ⟨snd_mem_l1TypicalSet (margLeft_isPMF hr) h₁, h₁⟩,
      mem_condL1TypicalSet.2 ⟨snd_mem_l1TypicalSet (margRight_isPMF hr) h₂, h₂⟩⟩)
  · intro t₁ _ t₂ _ h
    obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 h
    funext i
    exact Prod.ext (congrFun h₁ i) (congrFun h₂ i)

/-- **(6.155)–(6.156)** A proof of `H(X, Y | Z) ≤ H(X | Z) + H(Y | Z)` from the structure of the
strong joint typicality array, for a pmf `r` of `(Z, (X, Y))`. The conditional entropies on the
right are computed from the laws of `(Z, X)` and `(Z, Y)`. -/
theorem condEntropy_le_add_of_typicality {r : γ × (α × β) → ℝ} (hr : IsPMF r) :
    H[Prod.snd | Prod.fst ; r] ≤
      H[Prod.snd | Prod.fst ; margLeft r] + H[Prod.snd | Prod.fst ; margRight r] := by
  classical
  refine le_of_forall_pos_le_add fun ν hν => ?_
  have hν₃ : 0 < ν / 3 := by linarith
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_card_condL1TypicalSet_bounds hr hν₃
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_card_condL1TypicalSet_bounds (margLeft_isPMF hr) hν₃
  obtain ⟨δ₃, hδ₃, h₃⟩ := exists_card_condL1TypicalSet_bounds (margRight_isPMF hr) hν₃
  set δ := min (min δ₁ δ₂) (min δ₃ (1 / 2)) with hδ_def
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ (by norm_num))
  have le₁ : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have le₂ : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have le₃ : δ ≤ δ₃ := (min_le_right _ _).trans (min_le_left _ _)
  have le₄ : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n, hn₁, hn₂, hn₃, hn₄, hn₀⟩ := ((h₁ δ hδ le₁).and ((h₂ δ hδ le₂).and ((h₃ δ hδ le₃).and
    ((eventually_prob_l1TypicalProjection_gt hr hδ).and (eventually_gt_atTop 0))))).exists
  -- Some `z` is in the projection, since it has positive probability.
  have hne : (l1TypicalProjection r n δ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, prob_empty] at hn₄
    linarith
  obtain ⟨z, hz⟩ := hne
  obtain ⟨hzT, t, ht⟩ := mem_l1TypicalProjection.1 hz
  have hj := (mem_condL1TypicalSet.1 ht).2
  have hj₁ := mem_jointL1TypicalSet_margLeft hr hj
  have hj₂ := mem_jointL1TypicalSet_margRight hr hj
  have b₁ := (hn₁ z hzT ⟨t, ht⟩).1
  have b₂ := (hn₂ z (fst_mem_l1TypicalSet (margLeft_isPMF hr) hj₁)
    ⟨_, mem_condL1TypicalSet.2 ⟨snd_mem_l1TypicalSet (margLeft_isPMF hr) hj₁, hj₁⟩⟩).2
  have b₃ := (hn₃ z (fst_mem_l1TypicalSet (margRight_isPMF hr) hj₂)
    ⟨_, mem_condL1TypicalSet.2 ⟨snd_mem_l1TypicalSet (margRight_isPMF hr) hj₂, hj₂⟩⟩).2
  have hcard : ((condL1TypicalSet r n δ z).card : ℝ) ≤
      (condL1TypicalSet (margLeft r) n δ z).card * (condL1TypicalSet (margRight r) n δ z).card := by
    exact_mod_cast card_condL1TypicalSet_pair_le hr z
  have h₄ := b₁.trans (hcard.trans (mul_le_mul b₂ b₃ (Nat.cast_nonneg _) (exp_pos _).le))
  rw [← exp_add, exp_le_exp] at h₄
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn₀
  have h₅ : (n : ℝ) * (H[Prod.snd | Prod.fst ; r] - ν / 3) ≤ n *
      ((H[Prod.snd | Prod.fst ; margLeft r] + ν / 3) +
        (H[Prod.snd | Prod.fst ; margRight r] + ν / 3)) := by linarith
  have h₆ := le_of_mul_le_mul_left h₅ hn'
  linarith

end InfoTheory
