/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse

/-!
# The functional representation lemma

Any conditional pmf `p(z | y)` can be represented as a function `z = g(y, w)` of the input and of an
independent random variable `W` with `|𝒲| ≤ |𝒴| (|𝒵| - 1) + 1` (Willems and van der Meulen). We
follow the proof in Appendix B of El Gamal and Kim. The thresholds are the values of the conditional
cdfs in `(0, 1]`, the law of `W` consists of their gaps, and `g(y, w)` is the quantile function of
`p(z | y)` at the threshold `w`.

## Main definitions

* `thrPrev T t`, `thrMass T t`: the previous threshold and the gap below `t`.
* `condCdf q z`: the cdf of a pmf on an ordered set.

## Main statements

* `sum_thrMass`: the gaps up to a threshold add up to the threshold.
* `sum_quantile_eq`, `exists_channel_representation`: the representation of a conditional pmf.
* `functional_representation`: **the functional representation lemma**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Appendix B
-/

@[expose] public noncomputable section

open Finset

namespace InfoTheory

/-! ### Thresholds -/

/-- The largest element of `T` below `t`, or `0`. -/
def thrPrev (T : Finset ℝ) (t : ℝ) : ℝ :=
  (insert 0 (T.filter fun s => s < t)).max' (insert_nonempty _ _)

/-- The gap between `t` and the previous threshold. -/
def thrMass (T : Finset ℝ) (t : ℝ) : ℝ := t - thrPrev T t

lemma thrPrev_lt {T : Finset ℝ} {t : ℝ} (ht : 0 < t) : thrPrev T t < t := by
  have h := (insert 0 (T.filter fun s => s < t)).max'_mem (insert_nonempty _ _)
  rcases mem_insert.1 h with h0 | h1
  · change thrPrev T t = 0 at h0
    rw [h0]
    exact ht
  · exact (mem_filter.1 h1).2

lemma thrMass_pos {T : Finset ℝ} {t : ℝ} (ht : 0 < t) : 0 < thrMass T t :=
  sub_pos.2 (thrPrev_lt ht)

/-- **The gaps up to a threshold add up to the threshold.** -/
theorem sum_thrMass {T : Finset ℝ} (hT : ∀ t ∈ T, 0 < t) {c : ℝ} (hc : c ∈ T) :
    ∑ t ∈ T.filter (· ≤ c), thrMass T t = c := by
  induction h : (T.filter fun s => s < c).card using Nat.strong_induction_on generalizing c with
  | _ m ih =>
    have hdecomp : T.filter (· ≤ c) = insert c (T.filter fun s => s < c) := by
      ext t
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases h2.lt_or_eq with h3 | h3
        · exact Or.inr ⟨h1, h3⟩
        · exact Or.inl h3
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨hc, le_rfl⟩
        · exact ⟨h1, h2.le⟩
    rw [hdecomp, sum_insert (by simp)]
    rcases (T.filter fun s => s < c).eq_empty_or_nonempty with hemp | hne
    · have : thrPrev T c = 0 := by
        simp [thrPrev, hemp]
      simp [hemp, thrMass, this]
    · set c' := (T.filter fun s => s < c).max' hne with hc'
      have hc'm := (T.filter fun s => s < c).max'_mem hne
      have hc'T : c' ∈ T := (mem_filter.1 hc'm).1
      have hc'lt : c' < c := (mem_filter.1 hc'm).2
      have hprev : thrPrev T c = c' := by
        unfold thrPrev
        refine le_antisymm (max'_le _ _ _ fun y hy => ?_)
          (le_max' _ _ (mem_insert_of_mem hc'm))
        rcases mem_insert.1 hy with rfl | hy
        · exact (hT c' hc'T).le
        · exact le_max' _ _ hy
      have hset : (T.filter fun s => s < c) = T.filter (· ≤ c') := by
        ext t
        simp only [mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, le_max' _ _ (mem_filter.2 ⟨h1, h2⟩)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, lt_of_le_of_lt h2 hc'lt⟩
      have hlt : (T.filter fun s => s < c').card < m := by
        rw [← h]
        refine card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩
        · obtain ⟨h1, h2⟩ := mem_filter.1 ht
          exact mem_filter.2 ⟨h1, h2.trans hc'lt⟩
        · have := (mem_filter.1 (hsub hc'm)).2
          exact lt_irrefl _ this
      have hrec := ih _ hlt hc'T rfl
      rw [hset, hrec, thrMass, hprev]
      ring

/-! ### The cdf -/

section Representation

variable {Y Z : Type*} [Fintype Y] [Fintype Z] [LinearOrder Z]

/-- The cdf of a function on a finite ordered set. -/
def condCdf (q : Z → ℝ) (z : Z) : ℝ := ∑ z' ∈ univ.filter (· ≤ z), q z'

lemma condCdf_nonneg {q : Z → ℝ} (hq : ∀ z, 0 ≤ q z) (z : Z) : 0 ≤ condCdf q z :=
  sum_nonneg fun z' _ => hq z'

lemma condCdf_mono {q : Z → ℝ} (hq : ∀ z, 0 ≤ q z) {z z' : Z} (h : z ≤ z') :
    condCdf q z ≤ condCdf q z' :=
  sum_le_sum_of_subset_of_nonneg (fun _ hw => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hw).2.trans
    h⟩)
    fun w _ _ => hq w

/-- The cdf is at most `1`. -/
lemma condCdf_le_one {q : Z → ℝ} (hq : IsPMF q) (z : Z) : condCdf q z ≤ 1 := by
  rw [← hq.sum_eq_one]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ => hq.nonneg w

/-- A function is determined by its cdf. -/
lemma eq_of_condCdf_eq {q r : Z → ℝ} (h : ∀ z, condCdf q z = condCdf r z) (z : Z) : q z = r z := by
  induction z using WellFoundedLT.induction with
  | _ z ih =>
    have hdec : ∀ f : Z → ℝ, condCdf f z = f z + ∑ w ∈ univ.filter (· < z), f w := by
      intro f
      have hset : univ.filter (· ≤ z) = insert z (univ.filter (· < z)) := by
        ext w
        simp only [mem_filter, mem_univ, true_and, mem_insert]
        exact le_iff_eq_or_lt
      unfold condCdf
      rw [hset, sum_insert (by simp)]
    have h1 := h z
    rw [hdec, hdec] at h1
    have h2 : ∑ w ∈ univ.filter (· < z), q w = ∑ w ∈ univ.filter (· < z), r w :=
      sum_congr rfl fun w hw => ih w (mem_filter.1 hw).2
    linarith

variable [Nonempty Z]

/-- The quantile function: the smallest `z` with `t ≤ F(z)`, or the largest element of `Z`. -/
def quantileOf (q : Z → ℝ) (t : ℝ) : Z :=
  if h : (univ.filter fun z => t ≤ condCdf q z).Nonempty then
    (univ.filter fun z => t ≤ condCdf q z).min' h
  else univ.max' univ_nonempty

/-- The quantile function is at most `z` if and only if the threshold is at most `F(z)`. -/
lemma quantileOf_le_iff {q : Z → ℝ} (hq : IsPMF q) {t : ℝ} (ht : t ≤ 1) (z : Z) :
    quantileOf q t ≤ z ↔ t ≤ condCdf q z := by
  have htop : condCdf q (univ.max' univ_nonempty) = 1 := by
    rw [← hq.sum_eq_one]
    refine sum_congr ?_ fun _ _ => rfl
    ext w
    simpa using le_max' _ _ (mem_univ w)
  have hne : (univ.filter fun z => t ≤ condCdf q z).Nonempty :=
    ⟨univ.max' univ_nonempty, mem_filter.2 ⟨mem_univ _, by rw [htop]; exact ht⟩⟩
  unfold quantileOf
  simp only [hne, ↓reduceDIte]
  constructor
  · intro h
    have h1 := (mem_filter.1 ((univ.filter fun z => t ≤ condCdf q z).min'_mem hne)).2
    exact h1.trans (condCdf_mono hq.nonneg h)
  · intro h
    exact min'_le _ z (mem_filter.2 ⟨mem_univ z, h⟩)

/-- The thresholds: the positive values of the cdfs at the elements other than the largest one,
and `1`. -/
def cdfThresholds (q : Y → Z → ℝ) : Finset ℝ :=
  insert 1 (((univ : Finset (Y × Z)).filter fun x => x.2 ≠ univ.max' univ_nonempty).image
    (fun x => condCdf (q x.1) x.2) |>.filter fun t => 0 < t)

lemma card_cdfThresholds_le (q : Y → Z → ℝ) :
    (cdfThresholds q).card ≤ Fintype.card Y * (Fintype.card Z - 1) + 1 := by
  classical
  refine (card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  refine (card_filter_le _ _).trans (card_image_le.trans ?_)
  have hsub : ((univ : Finset (Y × Z)).filter fun x => x.2 ≠ univ.max' univ_nonempty) =
      (univ : Finset Y) ×ˢ (univ.erase (univ.max' univ_nonempty)) := by
    ext ⟨y, z⟩
    simp
  rw [hsub, card_product, card_erase_of_mem (mem_univ _)]
  simp

/-- The thresholds are positive and at most `1`. -/
lemma mem_cdfThresholds_bounds {q : Y → Z → ℝ} (hq : IsChannel q) {t : ℝ}
    (ht : t ∈ cdfThresholds q) : 0 < t ∧ t ≤ 1 := by
  classical
  rcases mem_insert.1 ht with rfl | h
  · exact ⟨one_pos, le_rfl⟩
  · obtain ⟨h1, h2⟩ := mem_filter.1 h
    obtain ⟨x, -, rfl⟩ := mem_image.1 h1
    exact ⟨h2, condCdf_le_one (hq x.1) x.2⟩

/-- The cdf of the law of the quantile of a random threshold. -/
lemma condCdf_quantile_law {q : Z → ℝ} (hq : IsPMF q) {T : Finset ℝ} (hT : ∀ t ∈ T, t ≤ 1)
    (m : ℝ → ℝ) (z : Z) :
    condCdf (fun z => ∑ t ∈ T, if quantileOf q t = z then m t else 0) z =
      ∑ t ∈ T.filter (· ≤ condCdf q z), m t := by
  classical
  rw [sum_filter]
  rw [condCdf, sum_comm]
  refine sum_congr rfl fun t ht => ?_
  rw [sum_ite_eq]
  simp only [mem_filter, mem_univ, true_and]
  exact if_congr (quantileOf_le_iff hq (hT t ht) z) rfl rfl

/-- **The representation of a conditional pmf.** The thresholds are the possible values of the
random variable `W`, with the gaps as its law, and `g(y, w)` is the quantile of `q(· | y)` at
`w`. -/
theorem sum_quantile_eq {q : Y → Z → ℝ} (hq : IsChannel q) (y : Y) (z : Z) :
    ∑ t ∈ cdfThresholds q, (if quantileOf (q y) t = z then thrMass (cdfThresholds q) t else 0) =
      q y z := by
  classical
  set T := cdfThresholds q with hT
  have hTb : ∀ t ∈ T, 0 < t ∧ t ≤ 1 := fun t ht => mem_cdfThresholds_bounds hq ht
  set M : Z → ℝ := fun z => ∑ t ∈ T, if quantileOf (q y) t = z then thrMass T t else 0 with hM
  refine eq_of_condCdf_eq (q := M) (r := q y) (fun z => ?_) z
  rw [hM, condCdf_quantile_law (hq y) (fun t ht => (hTb t ht).2)]
  rcases (condCdf_nonneg (hq y).nonneg z).eq_or_lt with h0 | hpos
  · have hemp : T.filter (· ≤ condCdf (q y) z) = ∅ :=
      filter_eq_empty_iff.2 fun t ht => not_le.2 (by rw [← h0]; exact (hTb t ht).1)
    rw [hemp, sum_empty, ← h0]
  · -- The value of the cdf is a threshold.
    have hmem : condCdf (q y) z ∈ T := by
      by_cases htop : z = univ.max' univ_nonempty
      · have hone : condCdf (q y) z = 1 := by
          rw [← (hq y).sum_eq_one]
          refine sum_congr ?_ fun _ _ => rfl
          ext w
          simpa [htop] using le_max' _ _ (mem_univ w)
        rw [hone]
        exact mem_insert_self _ _
      · refine mem_insert_of_mem (mem_filter.2 ⟨?_, hpos⟩)
        exact mem_image.2 ⟨(y, z), mem_filter.2 ⟨mem_univ _, htop⟩, rfl⟩
    exact sum_thrMass (fun t ht => (hTb t ht).1) hmem

/-- The gaps form a pmf on the thresholds. -/
theorem sum_thrMass_cdfThresholds {q : Y → Z → ℝ} (hq : IsChannel q) :
    ∑ t ∈ cdfThresholds q, thrMass (cdfThresholds q) t = 1 := by
  have hb := fun t (ht : t ∈ cdfThresholds q) => mem_cdfThresholds_bounds hq ht
  have h1 : (1 : ℝ) ∈ cdfThresholds q := mem_insert_self _ _
  have h2 := sum_thrMass (fun t ht => (hb t ht).1) h1
  rwa [filter_true_of_mem fun t ht => (hb t ht).2] at h2

end Representation

/-! ### The lemma -/

section Lemma

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- **The representation of a conditional pmf**, with `W` in `Fin m`. -/
theorem exists_channel_representation [Nonempty Z] [DecidableEq Z] {q : Y → Z → ℝ}
    (hq : IsChannel q) :
    ∃ m ≤ Fintype.card Y * (Fintype.card Z - 1) + 1, ∃ (π' : Fin m → ℝ) (g : Y → Fin m → Z),
      IsPMF π' ∧ ∀ y z, ∑ w, (if g y w = z then π' w else 0) = q y z := by
  classical
  let _ : LinearOrder Z := LinearOrder.lift' (Fintype.equivFin Z) (Equiv.injective _)
  set T := cdfThresholds q with hT
  have hTb : ∀ t ∈ T, 0 < t ∧ t ≤ 1 := fun t ht => mem_cdfThresholds_bounds hq ht
  set e := T.equivFin with he
  refine ⟨T.card, card_cdfThresholds_le q, fun w => thrMass T (e.symm w),
    fun y w => quantileOf (q y) (e.symm w),
      ⟨fun w => (thrMass_pos (hTb _ (e.symm w).property).1).le, ?_⟩,
    fun y z => ?_⟩
  · rw [e.symm.sum_comp (fun t : T => thrMass T t), sum_coe_sort T (thrMass T)]
    exact sum_thrMass_cdfThresholds hq
  · have h := sum_quantile_eq hq y z
    rw [← h, e.symm.sum_comp (fun t : T => if quantileOf (q y) t = z then thrMass T t else 0),
      sum_coe_sort T (fun t => if quantileOf (q y) t = z then thrMass T t else 0)]
    exact sum_congr rfl fun t _ => by congr

/-- **The core of the functional representation lemma**, for a pmf on `𝒴 × 𝒵`. The random variable
`W` is generated from `(Y, Z)` through the channel `κ`. -/
theorem exists_representation_pair [Nonempty Z] {ν : Y × Z → ℝ} (hν : IsPMF ν) :
    ∃ m ≤ Fintype.card Y * (Fintype.card Z - 1) + 1, ∃ (π' : Fin m → ℝ) (g : Y → Fin m → Z)
      (κ : Y × Z → Fin m → ℝ), IsPMF π' ∧ IsChannel κ ∧
        (∀ y w, ∑ z, ν (y, z) * κ (y, z) w = (∑ z, ν (y, z)) * π' w) ∧
        ∀ y z w, ν (y, z) ≠ 0 → κ (y, z) w ≠ 0 → z = g y w := by
  classical
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  set pY : Y → ℝ := fun y => ∑ z, ν (y, z) with hpY
  have hpY0 : ∀ y, 0 ≤ pY y := fun y => sum_nonneg fun z _ => hν.nonneg _
  set q : Y → Z → ℝ := fun y z => if 0 < pY y then ν (y, z) / pY y else if z = z₀ then 1 else 0
    with hq
  have hqc : IsChannel q := by
    intro y
    by_cases hy : 0 < pY y
    · refine ⟨fun z => ?_, ?_⟩
      · simp only [hq, hy, ite_true]
        exact div_nonneg (hν.nonneg _) hy.le
      · simp only [hq, hy, ite_true]
        rw [← sum_div]
        exact div_self hy.ne'
    · refine ⟨fun z => ?_, ?_⟩
      · simp only [hq, hy, ite_false]
        split_ifs <;> norm_num
      · simp [hq, hy]
  obtain ⟨m, hm, π', g, hπ, hrep⟩ := exists_channel_representation hqc
  -- The channel from `(Y, Z)` to `W`.
  set κ : Y × Z → Fin m → ℝ := fun x w =>
    if 0 < q x.1 x.2 then (if g x.1 w = x.2 then π' w else 0) / q x.1 x.2 else π' w with hκ
  have hκc : IsChannel κ := by
    intro x
    by_cases hx : 0 < q x.1 x.2
    · refine ⟨fun w => ?_, ?_⟩
      · simp only [hκ, hx, ite_true]
        refine div_nonneg ?_ hx.le
        split_ifs
        · exact hπ.nonneg w
        · exact le_rfl
      · simp only [hκ, hx, ite_true]
        rw [← sum_div, hrep]
        exact div_self hx.ne'
    · simpa [hκ, hx] using hπ
  refine ⟨m, hm, π', g, κ, hπ, hκc, fun y w => ?_, fun y z w hν0 hκ0 => ?_⟩
  · by_cases hy : 0 < pY y
    · -- The value of `W` has positive probability, so its `z` has positive probability.
      have hterm : ∀ z, ν (y, z) * κ (y, z) w = pY y * (if g y w = z then π' w else 0) := by
        intro z
        have hνq : ν (y, z) = pY y * q y z := by
          simp only [hq, hy, ite_true]
          field_simp
        by_cases hqz : 0 < q y z
        · simp only [hκ, hqz, ite_true]
          rw [hνq]
          field_simp
        · have hq0 : q y z = 0 := le_antisymm (not_lt.1 hqz) ((hqc y).nonneg z)
          have hzero : (if g y w = z then π' w else 0) = 0 := by
            split_ifs with h
            · by_contra hne
              have hpos : 0 < π' w := lt_of_le_of_ne (hπ.nonneg w) (Ne.symm hne)
              have h1 := hrep y z
              have h2 := single_le_sum (f := fun w' => if g y w' = z then π' w' else 0)
                (fun w' _ => by
                  split_ifs
                  · exact hπ.nonneg w'
                  · exact le_rfl) (mem_univ w)
              simp only [h, ite_true] at h2
              rw [h1, hq0] at h2
              linarith
            · rfl
          rw [hzero, hνq, hq0]
          simp
      simp only [hterm]
      rw [← mul_sum, sum_ite_eq, ite_eq_left (mem_univ _)]
    · have h0 : pY y = 0 := le_antisymm (not_lt.1 hy) (hpY0 y)
      have hz : ∀ z, ν (y, z) = 0 := fun z =>
        (sum_eq_zero_iff_of_nonneg fun z _ => hν.nonneg (y, z)).1 h0 z (mem_univ z)
      simp [hz]
  · have hpos : 0 < ν (y, z) := lt_of_le_of_ne (hν.nonneg _) (Ne.symm hν0)
    have hy : 0 < pY y := lt_of_lt_of_le hpos (single_le_sum (f := fun z => ν (y, z))
      (fun z _ => hν.nonneg _) (mem_univ z))
    have hqz : 0 < q y z := by
      simp only [hq, hy, ite_true]
      exact div_pos hpos hy
    by_contra hne
    apply hκ0
    simp only [hκ, hqz, ite_true]
    rw [ite_eq_right (Ne.symm hne), zero_div]

/-- The law of the output of a channel that only uses a function `g` of the input. -/
private lemma dist_pair_of_comp {A B C : Type*} [Fintype A] [Fintype C] {p : A → ℝ}
    {κ : B → C → ℝ} (hκ : IsChannel κ) (g : A → B) (b : B) (w : C) :
    dist (jointOf p fun a => κ (g a)) (pair (g ∘ Prod.fst) Prod.snd) (b, w) =
      dist (jointOf p fun a => κ (g a)) (g ∘ Prod.fst) b * κ b w := by
  classical
  have h1 : dist (jointOf p fun a => κ (g a)) (g ∘ Prod.fst) = dist p g := by
    rw [dist_comp_eq, dist_jointOf_fst fun a => hκ (g a)]
  rw [h1]
  simp only [dist, pair, jointOf, Function.comp, Prod.mk.injEq, Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single w (fun c _ hc => by simp [hc]) (by simp)]
  by_cases h : g a = b
  · simp [h]
  · simp [h]

/-- **The functional representation lemma of Appendix B of El Gamal and Kim.** For `(X, Y, Z) ∼ p`,
there is a random variable `W` with `|𝒲| ≤ |𝒴| (|𝒵| - 1) + 1`, generated from `(Y, Z)` through a
channel `κ`, such that `W` is independent of `Y`, `Z` is a function of `(Y, W)` and
`X → (Y, Z) → W` form a Markov chain. The law of `(X, Y, Z)` is `p` by construction. -/
theorem functional_representation {p : X × Y × Z → ℝ} (hp : IsPMF p) :
    ∃ m ≤ Fintype.card Y * (Fintype.card Z - 1) + 1, ∃ (π' : Fin m → ℝ) (g : Y → Fin m → Z)
      (κ : Y × Z → Fin m → ℝ), IsPMF π' ∧ IsChannel κ ∧
        (∀ y w, dist (jointOf p fun o => κ o.2) (fun o => (o.1.2.1, o.2)) (y, w) =
          dist p (fun o => o.2.1) y * π' w) ∧
        (∀ o, jointOf p (fun o => κ o.2) o ≠ 0 → o.1.2.2 = g o.1.2.1 o.2) ∧
        I[fun o : (X × Y × Z) × Fin m => o.1.1 : Prod.snd | fun o => o.1.2 ;
          jointOf p fun o => κ o.2] = 0 := by
  classical
  have hne : Nonempty (X × Y × Z) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hp.sum_eq_one
    simp at this
  have : Nonempty Z := ⟨(Classical.arbitrary (X × Y × Z)).2.2⟩
  set ν : Y × Z → ℝ := dist p (fun o => o.2) with hν
  have hνp : IsPMF ν := hp.dist _
  obtain ⟨m, hm, π', g, κ, hπ, hκ, hind, hfun⟩ := exists_representation_pair hνp
  set L := jointOf p fun o : X × Y × Z => κ o.2 with hL
  have hLp : IsPMF L := jointOf_isPMF hp fun o => hκ o.2
  have hLC : dist L ((fun o : X × Y × Z => o.2) ∘ Prod.fst) = ν := by
    rw [dist_comp_eq, dist_jointOf_fst fun o : X × Y × Z => hκ o.2]
  have hCW : ∀ c w, dist L (pair ((fun o : X × Y × Z => o.2) ∘ Prod.fst) Prod.snd) (c, w) =
      ν c * κ c w := fun c w => by
    rw [hL, dist_pair_of_comp hκ (fun o : X × Y × Z => o.2) c w, ← hL, hLC]
  refine ⟨m, hm, π', g, κ, hπ, hκ, fun y w => ?_, fun o ho => ?_, ?_⟩
  · -- `W` is independent of `Y`.
    have h1 : (fun o : (X × Y × Z) × Fin m => (o.1.2.1, o.2)) =
        (fun t : (Y × Z) × Fin m => (t.1.1, t.2)) ∘
          pair ((fun o : X × Y × Z => o.2) ∘ Prod.fst) Prod.snd := rfl
    have h2 : dist p (fun o => o.2.1) y = ∑ z, ν (y, z) := by
      have h3 : (fun o : X × Y × Z => o.2.1) = Prod.fst ∘ fun o : X × Y × Z => o.2 := rfl
      rw [h3, dist_comp_eq, dist_fst]
    rw [h1, dist_comp_eq, h2, ← hind y w]
    generalize dist L (pair ((fun o : X × Y × Z => o.2) ∘ Prod.fst) Prod.snd) = D at hCW
    simp only [dist, Fintype.sum_prod_type, Prod.mk.injEq]
    rw [sum_eq_single y]
    · refine sum_congr rfl fun z _ => ?_
      rw [sum_eq_single w]
      · simp only [and_self, ite_true]
        exact hCW (y, z) w
      · intro w' _ hw'
        simp [hw']
      · simp
    · intro y' _ hy'
      simp [hy']
    · simp
  · obtain ⟨⟨x, y, z⟩, w⟩ := o
    have h1 : p (x, y, z) ≠ 0 := fun h => ho (by simp [jointOf, h])
    have h2 : κ (y, z) w ≠ 0 := fun h => ho (by simp [jointOf, h])
    have h3 : ν (y, z) ≠ 0 := by
      intro h0
      have h4 : p (x, y, z) ≤ ν (y, z) := by
        have h5 := single_le_sum (f := fun o : X × Y × Z => if o.2 = (y, z) then p o else 0)
          (fun o _ => by
            split_ifs
            · exact hp.nonneg o
            · exact le_rfl) (mem_univ (x, y, z))
        simp only [ite_true] at h5
        refine h5.trans (le_of_eq ?_)
        simp only [hν, dist]
        exact sum_congr rfl fun o _ => by congr
      rw [h0] at h4
      exact h1 (le_antisymm h4 (hp.nonneg _))
    exact hfun y z w h3 h2
  · -- The channel only uses `(Y, Z)`.
    set Xv : (X × Y × Z) × Fin m → X := fun o => o.1.1 with hXv
    set C : (X × Y × Z) × Fin m → Y × Z := fun o => o.1.2 with hC
    set Wv : (X × Y × Z) × Fin m → Fin m := Prod.snd with hWv
    rw [condMutualInfo_comm hLp]
    unfold condMutualInfo
    have hC' : dist L C = ν := hLC
    have h1 := condEntropy_of_channel (μ := L) (Z := C) (Y := Wv) (W := κ) id
      (fun c w => by
        rw [hC']
        exact hCW c w)
    have h2 := condEntropy_of_channel (μ := L) (Z := pair Xv C) (Y := Wv) (W := κ) Prod.snd
      (fun c w => by
        have h3 := dist_pair_of_comp (p := p) (κ := fun c : X × (Y × Z) => κ c.2)
          (fun c => hκ c.2) (fun o : X × Y × Z => (o.1, o.2)) c w
        exact h3)
    have h3 : (Prod.snd ∘ pair Xv C) = C := rfl
    have h4 : (id ∘ C) = C := rfl
    rw [h1, h2, h3, h4, sub_self]

end Lemma

end InfoTheory
