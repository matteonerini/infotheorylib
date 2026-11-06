/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Basic
public import InfoTheoryLib.ForMathlib.SupportLemma
public import InfoTheoryLib.Probability.Channel

/-!
# Replacing a mixture of pmfs by a mixture of few pmfs

The form of the support lemma used to bound the cardinality of an auxiliary random variable, as in
Appendix C of El Gamal and Kim. A mixture of pmfs can be replaced by a mixture of few pmfs that
preserves an output law, or the mean itself, and the means of some continuous functions.

## Main statements

* `isConnected_setOf_isPMF`: the set of pmfs is connected.
* `exists_mixture_preserving`: **the support lemma for pmfs**, with an output preserved.
* `exists_mixture_preserving_mean`: the same, with the mean of the pmfs preserved.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α]

/-- The set of pmfs is convex. -/
lemma convex_setOf_isPMF : Convex ℝ {p : α → ℝ | IsPMF p} := by
  intro p hp p' hp' a b ha hb hab
  refine ⟨fun x => ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha (hp.nonneg x)) (mul_nonneg hb (hp'.nonneg x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      hp.sum_eq_one, hp'.sum_eq_one, mul_one, hab]

/-- The set of pmfs is connected. -/
lemma isConnected_setOf_isPMF [Nonempty α] : IsConnected {p : α → ℝ | IsPMF p} :=
  ⟨⟨uniformPMF α, uniformPMF_isPMF⟩, convex_setOf_isPMF.isPreconnected⟩

/-- The output of a mean of inputs is the mean of the outputs. -/
lemma outDist_mean {ι : Type*} [Fintype ι] (a : ι → ℝ) (b : ι → α → ℝ) (T : α → β → ℝ) :
    outDist (∑ i, a i • b i) T = ∑ i, a i • outDist (b i) T := by
  funext y
  simp only [outDist, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => by ring

/-- The output of the output is the output of the composed channel. -/
lemma outDist_outDist {γ : Type*} [Fintype β] (t : α → ℝ) (T : α → β → ℝ) (V : β → γ → ℝ) :
    outDist (outDist t T) V = outDist t fun x y => ∑ b, T x b * V b y := by
  funext y
  simp only [outDist, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun b _ => by ring

/-- The entropy is continuous. -/
lemma continuous_entropy : Continuous fun t : α → ℝ => entropy t := by
  simp only [entropy_eq_sum_negMulLog]
  exact continuous_finsetSum _ fun x _ => continuous_negMulLog.comp (continuous_apply x)

/-- The entropy of the law of a random variable is continuous in the law. -/
lemma continuous_entropy_dist {a : Type*} [Fintype a] (f : α → a) :
    Continuous fun t : α → ℝ => entropy (dist t f) := by
  classical
  simp only [entropy_eq_sum_negMulLog, dist]
  refine continuous_finsetSum _ fun v _ => continuous_negMulLog.comp ?_
  refine continuous_finsetSum _ fun x _ => ?_
  split_ifs
  exacts [continuous_apply x, continuous_const]

/-- The entropy of the output is continuous in the input. -/
lemma continuous_entropy_outDist [Fintype β] (T : α → β → ℝ) :
    Continuous fun t : α → ℝ => entropy (outDist t T) := by
  simp only [entropy_eq_sum_negMulLog, outDist]
  exact continuous_finsetSum _ fun y _ => continuous_negMulLog.comp (by fun_prop)

/-- The mean output sums to one. -/
lemma sum_mean_outDist {ν A ι : Type*} [Fintype ν] [Fintype A] [Fintype ι] {L : ν → A → ℝ}
    (hL : IsChannel L) {c : ι → ℝ} {d : ι → ν → ℝ} (hc : IsPMF c) (hd : IsChannel d) :
    ∑ y, (∑ i, c i • outDist (d i) L) y = 1 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_comm]
  simp only [← mul_sum, (outDist_isPMF (hd _) hL).sum_eq_one, mul_one, hc.sum_eq_one]

/-- **The support lemma for pmfs.** A mixture of pmfs on `ν` with weights `a` can be replaced by a
mixture of `|A| - 1 + |κ|` pmfs that preserves the mean output of a channel `L : ν → A` and the
means of `|κ|` continuous functions. -/
theorem exists_mixture_preserving {ν A κ ι : Type*} [Fintype ν] [Fintype A] [Fintype κ] [Fintype ι]
    [Nonempty κ] [Nonempty ν] {L : ν → A → ℝ} (hL : IsChannel L) {f : κ → (ν → ℝ) → ℝ}
    (hf : ∀ k, ContinuousOn (f k) {p | IsPMF p}) {a : ι → ℝ} (ha : IsPMF a) {b : ι → ν → ℝ}
    (hb : IsChannel b) {n : ℕ} (hn : Fintype.card A - 1 + Fintype.card κ = n) :
    ∃ (w : Fin n → ℝ) (z : Fin n → ν → ℝ), IsPMF w ∧ IsChannel z ∧
      ∑ i, w i • outDist (z i) L = ∑ i, a i • outDist (b i) L ∧
        ∀ k, ∑ i, w i * f k (z i) = ∑ i, a i * f k (b i) := by
  classical
  obtain ⟨ν₀⟩ := ‹Nonempty ν›
  have hA : Nonempty A := by
    obtain ⟨y⟩ : Nonempty A := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hL ν₀))
    exact ⟨y⟩
  obtain ⟨a₀⟩ := hA
  have hcard : Fintype.card ({y : A // y ≠ a₀} ⊕ κ) = n := by
    rw [Fintype.card_sum, ← hn]
    simp [Fintype.card_subtype_compl]
  subst hcard
  set g : {y : A // y ≠ a₀} ⊕ κ → (ν → ℝ) → ℝ :=
    Sum.elim (fun y t => outDist t L y) (fun k t => f k t) with hg
  have hgc : ∀ j, ContinuousOn (g j) {p | IsPMF p} := by
    rintro (y | k)
    · simp only [hg, Sum.elim_inl, outDist]
      exact Continuous.continuousOn (by fun_prop)
    · exact hf k
  have : Nonempty ({y : A // y ≠ a₀} ⊕ κ) := ⟨Sum.inr (Classical.arbitrary κ)⟩
  obtain ⟨w, z, hz, hw0, hw1, h⟩ := exists_fin_mixture_eq_sum (g := g)
    isConnected_setOf_isPMF hgc ha.nonneg ha.sum_eq_one (r := b) hb
  refine ⟨w, z, ⟨hw0, hw1⟩, hz, ?_, fun k => h (Sum.inr k)⟩
  have hne : ∀ y, y ≠ a₀ → (∑ i, w i • outDist (z i) L) y = (∑ i, a i • outDist (b i) L) y := by
    intro y hy
    have e := h (Sum.inl ⟨y, hy⟩)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg, Sum.elim_inl] using e
  funext y
  by_cases hy : y = a₀
  · subst hy
    have e1 := sum_mean_outDist hL (c := w) (d := z) ⟨hw0, hw1⟩ hz
    have e2 := sum_mean_outDist hL ha hb
    rw [← Finset.add_sum_erase _ _ (mem_univ y)] at e1 e2
    have e3 : ∑ y' ∈ univ.erase y, (∑ i, w i • outDist (z i) L) y' =
        ∑ y' ∈ univ.erase y, (∑ i, a i • outDist (b i) L) y' :=
      sum_congr rfl fun y' hy' => hne y' (ne_of_mem_erase hy')
    linarith
  · exact hne y hy

/-- **The support lemma for pmfs, with the mean preserved.** A mixture of pmfs on `ν` with weights
`a` can be replaced by a mixture of `|ν| - 1 + |κ|` pmfs that preserves the mean of the pmfs and the
means of `|κ|` continuous functions. -/
theorem exists_mixture_preserving_mean {ν κ ι : Type*} [Fintype ν] [Fintype κ] [Fintype ι]
    [Nonempty κ] [Nonempty ν] {f : κ → (ν → ℝ) → ℝ} (hf : ∀ k, ContinuousOn (f k) {p | IsPMF p})
    {a : ι → ℝ} (ha : IsPMF a) {b : ι → ν → ℝ} (hb : IsChannel b) {n : ℕ}
    (hn : Fintype.card ν - 1 + Fintype.card κ = n) :
    ∃ (w : Fin n → ℝ) (z : Fin n → ν → ℝ), IsPMF w ∧ IsChannel z ∧
      (∀ x, ∑ i, w i * z i x = ∑ i, a i * b i x) ∧
        ∀ k, ∑ i, w i * f k (z i) = ∑ i, a i * f k (b i) := by
  classical
  set d : ν → ν → ℝ := fun x y => if x = y then 1 else 0 with hd
  have hdC : IsChannel d := fun x =>
    ⟨fun y => by simp only [hd]; split_ifs <;> norm_num, by simp [hd]⟩
  have hdO : ∀ t : ν → ℝ, outDist t d = t := fun t => by
    funext y
    simp [outDist, hd]
  obtain ⟨w, z, hw, hz, hmean, hmix⟩ := exists_mixture_preserving hdC hf ha hb hn
  refine ⟨w, z, hw, hz, fun x => ?_, hmix⟩
  simp only [hdO] at hmean
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hmean x

end InfoTheory
