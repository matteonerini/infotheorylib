/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.SlepianWolfMany
public import InfoTheoryLib.RateDistortion.Achievability
public import InfoTheoryLib.RateDistortion.SideInfo

/-!
# Covering and binning for side information at the decoder

The encoder of Lecture 12 describes `Xⁿ` by a sequence `Uⁿ(l)` of a random codebook drawn i.i.d.
from `p(u)`.

We show directly that `(Xⁿ, Yⁿ, Uⁿ(L))` falls in any given sequence of sets `Tₙ` of typical triples,
that is any sets with `P{(Xⁿ, Yⁿ, Uⁿ) ∈ Tₙ} → 1` for i.i.d. triples. Instead of the conditional
typicality lemma, we call a pair `(xⁿ, uⁿ)` good if it is jointly typical and `yⁿ` given `xⁿ` falls
in `Tₙ` with probability at least `1 - δ`. By Markov's inequality, i.i.d. pairs are good with
probability tending to `1`, and the covering argument of Lemma 10.5.2 of [cover2006] finds a good
codeword.

For noncausal side information, we bin the codewords, and the decoder finds the sequence of the bin
that is jointly typical with `Yⁿ`.

## Main statements

* `sum_codebook_miss_le`: the probability that a random codebook misses a set of typical pairs.
* `sum_codebook_triple_le`: the covering bound for typical triples.
* `exists_wz_code_le`: the covering and binning bound.
* `eventually_causal_code`, `eventually_wz_code`: codes for any sets of typical triples.

## Implementation notes

Lecture 12 of [elgamal2010] bins the codewords deterministically, and bounds the probability of
the error event `E₃` by its Lemma 1, proved in its Appendix. Step (b) of that proof uses that,
given `L = l`, every collection of the other codewords has the same distribution. For an encoder
that selects the *smallest* index `l` with `(xⁿ, uⁿ(l))` typical, this is not so: codewords with
index smaller than `l` are known not to be typical with `xⁿ`, and those with a larger index are
not. We bin at random, as Section 15.9 of [cover2006] does, independently of the codebook: given
the codebook and `(Xⁿ, Yⁿ)`, another codeword falls in the bin of `Uⁿ(L)` with probability
`1 / M`, whatever `L` is, so the event `E₃` needs no conditioning at all.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 12
* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 15.9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α γ β υ : Type*} [Fintype α] [Fintype γ] [Fintype υ]

/-! ### Sequences of pairs -/

/-- The sequence of the source `(ωᵢ.1)`. -/
def fstSeq {n : ℕ} (ω : Fin n → α × γ) : Fin n → α := fun i => (ω i).1

/-- The sequence of the side information `(ωᵢ.2)`. -/
def sndSeq {n : ℕ} (ω : Fin n → α × γ) : Fin n → γ := fun i => (ω i).2

/-! ### Covering a set of typical pairs -/

section Miss

variable {p : α → ℝ} {q : α → υ → ℝ}

open Classical in
/-- **Lecture 12, page 12-10, and (10.89)–(10.101) of [cover2006].** A random codebook of `M`
sequences drawn i.i.d. from `p(u)` misses a set `A` of typical pairs `(xⁿ, uⁿ)`, for `xⁿ` i.i.d.
from `p(x)`, with probability at most `P{(Xⁿ, Uⁿ) ∉ A} + exp(-M e^{-n(I(X; U) + 3ε)})`. -/
theorem sum_codebook_miss_le (hp : IsPMF p) (hq : IsChannel q) {n M : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (A : Finset ((Fin n → α) × (Fin n → υ))) (hA : ∀ z ∈ A, z ∈ jointTypicalSet (jointOf p q) n ε) :
    ∑ C : Fin M → Fin n → υ, iidPMF (iidPMF (outDist p q) n) M C *
        ∑ x, iidPMF p n x * ∏ w, (if (x, C w) ∈ A then (0 : ℝ) else 1) ≤
      1 - prob (jointIid (jointOf p q) n) A +
        exp (-(exp (-(n * (mutualInfoOf p q + 3 * ε))) * M)) := by
  set r := outDist p q
  have hr : IsPMF r := outDist_isPMF hp hq
  have hrn : IsPMF (iidPMF r n) := iidPMF_isPMF hr n
  have hpn : IsPMF (iidPMF p n) := iidPMF_isPMF hp n
  set y := exp (-(n * (mutualInfoOf p q + 3 * ε)))
  have hy1 : y ≤ 1 := exp_le_one_iff.2 (by
    have := mutualInfoOf_nonneg hp hq
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : 0 ≤ (n : ℝ) * (mutualInfoOf p q + 3 * ε) := mul_nonneg this (by linarith)
    linarith)
  set φ : (Fin n → α) → (Fin n → υ) → ℝ := fun x z => if (x, z) ∈ A then 0 else 1
  have havg : ∀ x, ∑ C : Fin M → Fin n → υ, iidPMF (iidPMF r n) M C * ∏ w, φ x (C w) =
      (∑ z, iidPMF r n z * φ x z) ^ M := fun x => by
    rw [sum_iidPMF_mul_prod (iidPMF r n) fun _ z => φ x z, prod_const, card_univ,
      Fintype.card_fin]
  set K : (Fin n → α) → ℝ := fun x => ∑ z, channelExt q n x z * (if (x, z) ∈ A then 1 else 0)
  have hK0 : ∀ x, 0 ≤ K x := fun x => sum_nonneg fun z _ =>
    mul_nonneg (channelExt_nonneg hq x z) (by split_ifs <;> norm_num)
  have hK1 : ∀ x, K x ≤ 1 := fun x => by
    calc K x ≤ ∑ z, channelExt q n x z := sum_le_sum fun z _ => by
          split_ifs <;> simp [channelExt_nonneg hq x z]
      _ = 1 := ((hq.ext n) x).sum_eq_one
  have hmiss : ∀ x, (∑ z, iidPMF r n z * φ x z) ^ M ≤ 1 - K x + exp (-(y * M)) := by
    intro x
    have hsplit : ∑ z, iidPMF r n z * φ x z =
        1 - ∑ z, iidPMF r n z * (if (x, z) ∈ A then 1 else 0) := by
      rw [eq_sub_iff_add_eq, ← sum_add_distrib]
      refine (sum_congr rfl fun z _ => ?_).trans hrn.sum_eq_one
      simp only [φ]
      split_ifs <;> ring
    have hlow : y * K x ≤ ∑ z, iidPMF r n z * (if (x, z) ∈ A then 1 else 0) := by
      rw [mul_sum]
      refine sum_le_sum fun z _ => ?_
      split_ifs with hz
      · rw [mul_one, mul_one, mul_comm]
        exact channelExt_mul_exp_le_iidPMF hp hq (hA _ hz)
      · simp
    have h0 : 0 ≤ ∑ z, iidPMF r n z * φ x z :=
      sum_nonneg fun z _ => mul_nonneg (hrn.nonneg z) (by simp only [φ]; split_ifs <;> norm_num)
    calc (∑ z, iidPMF r n z * φ x z) ^ M ≤ (1 - K x * y) ^ M :=
          pow_le_pow_left₀ h0 (by linarith) M
      _ ≤ 1 - K x + exp (-(y * M)) := one_sub_mul_pow_le (hK0 x) (hK1 x) hy1 M
  have hprob : ∑ x, iidPMF p n x * K x = prob (jointIid (jointOf p q) n) A := by
    rw [prob, ← univ_inter A, ← sum_ite_mem, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    simp only [K, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [jointIid_jointOf]
    split_ifs <;> ring
  calc ∑ C : Fin M → Fin n → υ, iidPMF (iidPMF r n) M C * ∑ x, iidPMF p n x * ∏ w, φ x (C w)
      = ∑ x, iidPMF p n x *
          ∑ C : Fin M → Fin n → υ, iidPMF (iidPMF r n) M C * ∏ w, φ x (C w) := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_congr rfl fun C _ => by ring
    _ ≤ ∑ x, iidPMF p n x * (1 - K x + exp (-(y * M))) := by
        gcongr with x
        · exact hpn.nonneg x
        · rw [havg x]; exact hmiss x
    _ = _ := by
        rw [← hprob]
        simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, ← sum_mul,
          hpn.sum_eq_one, one_mul]

end Miss

/-! ### Covering typical triples -/

section Triple

variable {P : α × γ → ℝ} {q : α → υ → ℝ} {W : α → γ → ℝ} {n : ℕ}

omit [Fintype α] [Fintype γ] in
lemma iidPMF_zip_eq [Fintype α] [Fintype γ] (hPW : ∀ x y, P (x, y) = margFst P x * W x y)
    (x : Fin n → α) (y : Fin n → γ) :
    iidPMF P n (zipSeq x y) = iidPMF (margFst P) n x * channelExt W n x y := by
  simp only [iidPMF, channelExt, zipSeq, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => hPW _ _

omit [Fintype α] [Fintype γ] [Fintype υ] in
lemma iidPMF_siLaw_zip (ω : Fin n → α × γ) (u : Fin n → υ) :
    iidPMF (siLaw P q) n (zipSeq ω u) = iidPMF P n ω * channelExt q n (fstSeq ω) u := by
  simp only [iidPMF, channelExt, zipSeq, siLaw, jointOf, fstSeq, prod_mul_distrib]

/-- A sum against the i.i.d. triples, in terms of `p(xⁿ) p(uⁿ | xⁿ) p(yⁿ | xⁿ)`. -/
lemma sum_iidPMF_siLaw (hPW : ∀ x y, P (x, y) = margFst P x * W x y)
    (F : (Fin n → (α × γ) × υ) → ℝ) :
    ∑ t, iidPMF (siLaw P q) n t * F t =
      ∑ z, jointIid (jointOf (margFst P) q) n z *
        ∑ y, channelExt W n z.1 y * F (zipSeq (zipSeq z.1 y) z.2) := by
  rw [← sum_jointIid (siLaw P q) n F, Fintype.sum_prod_type]
  simp only [jointIid, iidPMF_siLaw_zip]
  have e : ∀ ω : Fin n → α × γ, ∑ u, iidPMF P n ω * channelExt q n (fstSeq ω) u * F (zipSeq ω u) =
      iidPMF P n ω * ∑ u, channelExt q n (fstSeq ω) u * F (zipSeq ω u) := fun ω => by
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by ring
  simp only [e]
  rw [← sum_jointIid P n fun ω => ∑ u, channelExt q n (fstSeq ω) u * F (zipSeq ω u),
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  simp only [jointIid, iidPMF_zip_eq hPW]
  have e2 : ∀ u, iidPMF (jointOf (margFst P) q) n (zipSeq x u) =
      iidPMF (margFst P) n x * channelExt q n x u := fun u => jointIid_jointOf _ _ n (x, u)
  simp only [e2, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => sum_congr rfl fun y _ => ?_
  change _ * (channelExt q n x u * F (zipSeq (zipSeq x y) u)) = _
  ring

open Classical in
/-- `P{(xⁿ, Yⁿ, uⁿ) ∉ T}`, for `Yⁿ` given `xⁿ` from the memoryless channel `W`. -/
def coverBad (W : α → γ → ℝ) (T : Finset (Fin n → (α × γ) × υ)) (x : Fin n → α)
    (u : Fin n → υ) : ℝ :=
  ∑ y, channelExt W n x y * (if zipSeq (zipSeq x y) u ∈ T then 0 else 1)

open Classical in
/-- `E P{(xⁿ, Yⁿ, uⁿ) ∉ T} = P{(Xⁿ, Yⁿ, Uⁿ) ∉ T}`. -/
lemma sum_coverBad (hP : IsPMF P) (hq : IsChannel q) (hPW : ∀ x y, P (x, y) = margFst P x * W x y)
    (T : Finset (Fin n → (α × γ) × υ)) :
    ∑ z, jointIid (jointOf (margFst P) q) n z * coverBad W T z.1 z.2 =
      1 - prob (iidPMF (siLaw P q) n) T := by
  have hμ := iidPMF_isPMF (siLaw_isPMF hP hq) n
  have h := sum_iidPMF_siLaw (q := q) (n := n) hPW fun t => if t ∈ T then (0 : ℝ) else 1
  have e : (∑ t, iidPMF (siLaw P q) n t * if t ∈ T then (0 : ℝ) else 1) +
      prob (iidPMF (siLaw P q) n) T = ∑ t, iidPMF (siLaw P q) n t := by
    have e' : prob (iidPMF (siLaw P q) n) T =
        ∑ t, if t ∈ T then iidPMF (siLaw P q) n t else 0 := by
      rw [prob, sum_ite_mem, univ_inter]
    rw [e', ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  rw [hμ.sum_eq_one] at e
  rw [eq_sub_iff_add_eq, ← e, h]
  rfl

/-- The good pairs: the jointly typical pairs `(xⁿ, uⁿ)` with `P{(xⁿ, Yⁿ, uⁿ) ∉ T} ≤ δ`. -/
def coverSet (W : α → γ → ℝ) (T : Finset (Fin n → (α × γ) × υ)) (J : α × υ → ℝ) (ε δ : ℝ) :
    Finset ((Fin n → α) × (Fin n → υ)) :=
  open Classical in (jointTypicalSet J n ε).filter fun z => coverBad W T z.1 z.2 ≤ δ

omit [Fintype α] [Fintype υ] in
lemma coverBad_nonneg (hW : IsChannel W) (T : Finset (Fin n → (α × γ) × υ)) (x : Fin n → α)
    (u : Fin n → υ) : 0 ≤ coverBad W T x u := by
  classical
  exact sum_nonneg fun y _ => mul_nonneg (channelExt_nonneg hW x y) (by split_ifs <;> norm_num)

omit [Fintype α] [Fintype υ] in
lemma coverBad_le_one (hW : IsChannel W) (T : Finset (Fin n → (α × γ) × υ)) (x : Fin n → α)
    (u : Fin n → υ) : coverBad W T x u ≤ 1 := by
  classical
  calc coverBad W T x u ≤ ∑ y, channelExt W n x y := sum_le_sum fun y _ => by
        split_ifs <;> simp [channelExt_nonneg hW x y]
    _ = 1 := ((hW.ext n) x).sum_eq_one

open Classical in
/-- By Markov's inequality, i.i.d. pairs are good with probability at least
`P{(Xⁿ, Uⁿ) typical} - P{(Xⁿ, Yⁿ, Uⁿ) ∉ T} / δ`. -/
lemma prob_coverSet_ge (hP : IsPMF P) (hq : IsChannel q) (hW : IsChannel W)
    (hPW : ∀ x y, P (x, y) = margFst P x * W x y) (T : Finset (Fin n → (α × γ) × υ)) (ε : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    prob (jointIid (jointOf (margFst P) q) n)
        (jointTypicalSet (jointOf (margFst P) q) n ε) -
      (1 - prob (iidPMF (siLaw P q) n) T) / δ ≤
    prob (jointIid (jointOf (margFst P) q) n) (coverSet W T (jointOf (margFst P) q) ε δ) := by
  set J := jointOf (margFst P) q
  have hJ : IsPMF J := jointOf_isPMF (hP.dist _) hq
  have h0 := jointIid_nonneg hJ.nonneg n
  have hsplit : prob (jointIid J n) (coverSet W T J ε δ) +
      ∑ z ∈ (jointTypicalSet J n ε).filter (fun z => ¬ coverBad W T z.1 z.2 ≤ δ), jointIid J n z =
      prob (jointIid J n) (jointTypicalSet J n ε) := by
    rw [prob, prob, coverSet]
    exact sum_filter_add_sum_filter_not _ _ _
  have hle : ∑ z ∈ (jointTypicalSet J n ε).filter (fun z => ¬ coverBad W T z.1 z.2 ≤ δ),
      jointIid J n z ≤ (1 - prob (iidPMF (siLaw P q) n) T) / δ := by
    rw [le_div_iff₀ hδ, ← sum_coverBad hP hq hPW T, sum_mul]
    refine (sum_le_sum fun z hz => ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun z _ _ => mul_nonneg (h0 z) (coverBad_nonneg hW T z.1 z.2))
    have := (mem_filter.1 hz).2
    exact mul_le_mul_of_nonneg_left (not_le.1 this).le (h0 z)
  linarith

open Classical in
/-- **Lecture 12, pages 12-9 and 12-10.** Over a random codebook of `L` sequences, the triple
`(Xⁿ, Yⁿ, Uⁿ(L))` for the first good codeword is not in `T` with probability at most
`δ + P{(Xⁿ, Uⁿ) not typical} + P{(Xⁿ, Yⁿ, Uⁿ) ∉ T} / δ + exp(-L e^{-n(I(X; U) + 3ε)})`. -/
theorem sum_codebook_triple_le (hP : IsPMF P) (hq : IsChannel q) (hW : IsChannel W)
    (hPW : ∀ x y, P (x, y) = margFst P x * W x y) {L : ℕ} (l₀ : Fin L) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : 0 < δ) (T : Finset (Fin n → (α × γ) × υ)) :
    ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF (outDist (margFst P) q) n) L C *
      ∑ ω, iidPMF P n ω * (if zipSeq ω (C (typicalEncode
        (coverSet W T (jointOf (margFst P) q) ε δ) C l₀ (fstSeq ω))) ∈ T then 0 else 1) ≤
    δ + (1 - prob (jointIid (jointOf (margFst P) q) n)
        (jointTypicalSet (jointOf (margFst P) q) n ε)) +
      (1 - prob (iidPMF (siLaw P q) n) T) / δ +
      exp (-(exp (-(n * (mutualInfoOf (margFst P) q + 3 * ε))) * L)) := by
  set p := margFst P with hp'
  have hp : IsPMF p := hP.dist _
  set J := jointOf p q
  set A := coverSet W T J ε δ
  have hA : ∀ z ∈ A, z ∈ jointTypicalSet J n ε := fun z hz => (mem_filter.1 hz).1
  have hpn := iidPMF_isPMF hp n
  have hlaw := iidPMF_isPMF (iidPMF_isPMF (outDist_isPMF hp hq) n) L
  have hmiss := sum_codebook_miss_le hp hq (n := n) (M := L) hε A hA
  have hprobA := prob_coverSet_ge hP hq hW hPW T ε (n := n) hδ
  -- For a fixed codebook.
  have hfix : ∀ C : Fin L → Fin n → υ,
      ∑ ω, iidPMF P n ω * (if zipSeq ω (C (typicalEncode A C l₀ (fstSeq ω))) ∈ T then 0 else 1) ≤
      δ + ∑ x, iidPMF p n x * ∏ w, (if (x, C w) ∈ A then (0 : ℝ) else 1) := fun C => by
    rw [← sum_jointIid P n fun ω =>
      if zipSeq ω (C (typicalEncode A C l₀ (fstSeq ω))) ∈ T then 0 else 1, Fintype.sum_prod_type]
    have e : ∀ x, ∑ y, jointIid P n (x, y) * (if zipSeq (zipSeq x y)
        (C (typicalEncode A C l₀ (fstSeq (zipSeq x y)))) ∈ T then (0 : ℝ) else 1) =
        iidPMF p n x * coverBad W T x (C (typicalEncode A C l₀ x)) := fun x => by
      simp only [coverBad, mul_sum]
      refine sum_congr rfl fun y _ => ?_
      change iidPMF P n (zipSeq x y) * _ = _
      rw [iidPMF_zip_eq hPW]
      have : fstSeq (zipSeq x y) = x := rfl
      rw [this]
      ring
    simp only [e]
    have hbd : ∀ x, coverBad W T x (C (typicalEncode A C l₀ x)) ≤
        δ + ∏ w, (if (x, C w) ∈ A then (0 : ℝ) else 1) := fun x => by
      by_cases hex : ∃ w, (x, C w) ∈ A
      · obtain ⟨w, hw⟩ := hex
        rw [prod_eq_zero (mem_univ w) (by simp [hw]), add_zero]
        exact (mem_filter.1 (typicalEncode_mem l₀ ⟨w, hw⟩)).2
      · push Not at hex
        rw [prod_eq_one fun w _ => by simp [hex w]]
        linarith [coverBad_le_one hW T x (C (typicalEncode A C l₀ x))]
    calc ∑ x, iidPMF p n x * coverBad W T x (C (typicalEncode A C l₀ x))
        ≤ ∑ x, iidPMF p n x * (δ + ∏ w, (if (x, C w) ∈ A then (0 : ℝ) else 1)) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hbd x) (hpn.nonneg x)
      _ = _ := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hpn.sum_eq_one, one_mul]
  calc ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF (outDist p q) n) L C *
      ∑ ω, iidPMF P n ω * (if zipSeq ω (C (typicalEncode A C l₀ (fstSeq ω))) ∈ T then 0 else 1)
      ≤ ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF (outDist p q) n) L C *
        (δ + ∑ x, iidPMF p n x * ∏ w, (if (x, C w) ∈ A then (0 : ℝ) else 1)) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hfix C) (hlaw.nonneg C)
    _ = δ + ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF (outDist p q) n) L C *
        ∑ x, iidPMF p n x * ∏ w, (if (x, C w) ∈ A then (0 : ℝ) else 1) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hlaw.sum_eq_one, one_mul]
    _ ≤ _ := by linarith

end Triple

/-! ### Binning -/

section Binning

variable {P : α × γ → ℝ} {q : α → υ → ℝ} {W : α → γ → ℝ} {n L M : ℕ}

open Classical in
/-- **Lecture 12, page 12-22.** The decoder of a binning: an index of the bin `m` whose codeword is
in `S` with `yⁿ`, and `l₀` if there is none. -/
def wzIndex (B : Fin L → Fin M) (S : Finset ((Fin n → γ) × (Fin n → υ))) (C : Fin L → Fin n → υ)
    (l₀ : Fin L) (m : Fin M) (y : Fin n → γ) : Fin L :=
  if h : ∃ l, B l = m ∧ (y, C l) ∈ S then h.choose else l₀

open Classical in
omit [Fintype α] [Fintype γ] [Fintype υ] in
/-- **Lecture 12, page 12-23.** The decoder recovers the index `l` unless `(ω, uⁿ(l)) ∉ T` or
another codeword of the bin is in `S` with `yⁿ`. -/
lemma wzIndex_not_mem_le {B : Fin L → Fin M} {S : Finset ((Fin n → γ) × (Fin n → υ))}
    {C : Fin L → Fin n → υ} (l₀ l : Fin L) {T : Finset (Fin n → (α × γ) × υ)}
    (hTS : ∀ (ω : Fin n → α × γ) (u : Fin n → υ), zipSeq ω u ∈ T → (sndSeq ω, u) ∈ S)
    (ω : Fin n → α × γ) :
    (if zipSeq ω (C (wzIndex B S C l₀ (B l) (sndSeq ω))) ∈ T then (0 : ℝ) else 1) ≤
      (if zipSeq ω (C l) ∈ T then 0 else 1) + ∑ l' ∈ univ.erase l,
        (if B l' = B l then 1 else 0) * (if (sndSeq ω, C l') ∈ S then 1 else 0) := by
  have hn0 : (0 : ℝ) ≤ ∑ l' ∈ univ.erase l,
      (if B l' = B l then 1 else 0) * (if (sndSeq ω, C l') ∈ S then 1 else 0) :=
    sum_nonneg fun l' _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
  by_cases hl : zipSeq ω (C l) ∈ T
  · by_cases hu : ∀ l', B l' = B l → (sndSeq ω, C l') ∈ S → l' = l
    · have hex : ∃ l', B l' = B l ∧ (sndSeq ω, C l') ∈ S := ⟨l, rfl, hTS ω _ hl⟩
      have hd : wzIndex B S C l₀ (B l) (sndSeq ω) = l := by
        simp only [wzIndex, hex, ↓reduceDIte]
        exact hu _ hex.choose_spec.1 hex.choose_spec.2
      simp only [hd, hl, ite_true, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨l', hb, hs, hne⟩ := hu
      have h1 : (1 : ℝ) ≤ ∑ l' ∈ univ.erase l,
          (if B l' = B l then 1 else 0) * (if (sndSeq ω, C l') ∈ S then 1 else 0) := by
        have := single_le_sum (f := fun l' => (if B l' = B l then (1 : ℝ) else 0) *
          (if (sndSeq ω, C l') ∈ S then 1 else 0))
          (fun _ _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num))
          (mem_erase.2 ⟨hne, mem_univ l'⟩)
        simpa [hb, hs] using this
      split_ifs <;> linarith
  · simp only [hl, ite_false]
    split_ifs <;> linarith

/-- **Lecture 12, page 12-23.** Over random bins, the codewords other than the one of `l` that fall
in its bin have a total weight of at most `(∑_{l'} Z(l')) / M`, whatever `l` is. -/
lemma sum_bins_erase_le (hM : 0 < M) (l : Fin L) {Z : Fin L → ℝ} (hZ : ∀ l', 0 ≤ Z l') :
    ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B * ∑ l' ∈ univ.erase l,
      (if B l' = B l then 1 else 0) * Z l' ≤ (∑ l', Z l') / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e : ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B * ∑ l' ∈ univ.erase l,
      (if B l' = B l then 1 else 0) * Z l' = ∑ l' ∈ univ.erase l, Z l' / M := by
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun l' hl' => ?_
    have h := sum_bins_eq_eq hM (N := L) (mem_erase.1 hl').1.symm
    calc ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
        ((if B l' = B l then 1 else 0) * Z l') =
        (∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
          (if B l' = B l then (1 : ℝ) else 0)) * Z l' := by
          rw [sum_mul]
          exact sum_congr rfl fun B _ => by ring
      _ = Z l' / M := by rw [h]; ring
  rw [e, ← sum_div]
  exact div_le_div_of_nonneg_right
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun l' _ _ => hZ l') hM'.le

open Classical in
/-- `E #{l : (Yⁿ, Uⁿ(l)) ∈ S} = L P{(Ỹⁿ, Ũⁿ) ∈ S}`, for independent `Ỹⁿ` and `Ũⁿ`. -/
lemma sum_codebook_count_eq {r : υ → ℝ} (hr : IsPMF r)
    (S : Finset ((Fin n → γ) × (Fin n → υ))) :
    ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * ∑ ω, iidPMF P n ω *
      ∑ l, (if (sndSeq ω, C l) ∈ S then (1 : ℝ) else 0) =
    L * ∑ z ∈ S, iidPMF (margSnd P) n z.1 * iidPMF r n z.2 := by
  have hrn := iidPMF_isPMF hr n
  have hsnd : ∀ g : (Fin n → γ) → ℝ, ∑ ω, iidPMF P n ω * g (sndSeq ω) =
      ∑ y, iidPMF (margSnd P) n y * g y := fun g => by
    rw [← sum_jointIid P n fun ω => g (sndSeq ω)]
    exact sum_jointIid_snd P n g
  have hsnd' : ∀ C : Fin L → Fin n → υ, ∑ ω, iidPMF P n ω *
      ∑ l, (if (sndSeq ω, C l) ∈ S then (1 : ℝ) else 0) = ∑ y, iidPMF (margSnd P) n y *
        ∑ l, (if (y, C l) ∈ S then (1 : ℝ) else 0) := fun C =>
    hsnd fun y => ∑ l, if (y, C l) ∈ S then (1 : ℝ) else 0
  simp only [hsnd']
  have e : ∀ y : Fin n → γ, ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C *
      ∑ l, (if (y, C l) ∈ S then (1 : ℝ) else 0) =
      L * ∑ u, iidPMF r n u * (if (y, u) ∈ S then (1 : ℝ) else 0) := fun y => by
    simp only [mul_sum]
    rw [sum_comm]
    simp only [← mul_sum]
    rw [sum_congr rfl fun l _ => sum_iidPMF_eval hrn l fun u => if (y, u) ∈ S then (1 : ℝ) else 0,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum]
  calc ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * ∑ y, iidPMF (margSnd P) n y *
      ∑ l, (if (y, C l) ∈ S then (1 : ℝ) else 0)
      = ∑ y, iidPMF (margSnd P) n y * ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C *
          ∑ l, (if (y, C l) ∈ S then (1 : ℝ) else 0) := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun C _ => sum_congr rfl fun l _ => by ring
    _ = _ := by
        simp only [e]
        have e' : ∑ z ∈ S, iidPMF (margSnd P) n z.1 * iidPMF r n z.2 =
            ∑ z, if z ∈ S then iidPMF (margSnd P) n z.1 * iidPMF r n z.2 else 0 := by
          rw [sum_ite_mem, univ_inter]
        rw [e', Fintype.sum_prod_type, mul_sum]
        refine sum_congr rfl fun y _ => ?_
        simp only [mul_sum]
        refine sum_congr rfl fun u _ => ?_
        split_ifs <;> ring

/-- The law of `(Y, U)`. -/
def siYU (P : α × γ → ℝ) (q : α → υ → ℝ) : γ × υ → ℝ :=
  dist (siLaw P q) fun z => (z.1.2, z.2)

lemma siYU_isPMF (hP : IsPMF P) (hq : IsChannel q) : IsPMF (siYU P q) :=
  (siLaw_isPMF hP hq).dist _

lemma margFst_siYU (hq : IsChannel q) : margFst (siYU P q) = margSnd P := by
  have h := dist_comp_eq (siLaw P q) (fun z : (α × γ) × υ => (z.1.2, z.2)) Prod.fst
  rw [← (dist_siLaw_Y (P := P) hq)]
  exact h.symm

lemma margSnd_siYU :
    margSnd (siYU P q) = outDist (margFst P) q := by
  classical
  have h := dist_comp_eq (siLaw P q) (fun z : (α × γ) × υ => (z.1.2, z.2)) Prod.snd
  have e : (Prod.snd ∘ fun z : (α × γ) × υ => (z.1.2, z.2)) = Prod.snd := rfl
  rw [e] at h
  rw [show margSnd (siYU P q) = dist (dist (siLaw P q) fun z : (α × γ) × υ => (z.1.2, z.2)) Prod.snd
    from rfl, ← h]
  funext u
  rw [← sum_dist_pair_right (siLaw P q) Prod.snd (fun z : (α × γ) × υ => z.1.1) u]
  simp only [dist_siLaw_UX, outDist]

/-- `I(Y; U)` under the law of `(Y, U)`. -/
lemma mutualInfo_siYU :
    I[Prod.fst : Prod.snd ; siYU P q] = I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [dist_pair_fst_snd]
  rfl

/-- `I(X; U)` is `mutualInfoOf`. -/
lemma mutualInfoOf_side :
    mutualInfoOf (margFst P) q = I[fun z : (α × γ) × υ => z.1.1 : Prod.snd ; siLaw P q] := by
  classical
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [dist_pair_fst_snd]
  funext ⟨x, u⟩
  rw [dist_pair_swap, dist_siLaw_UX]
  rfl

open Classical in
/-- **Lecture 12, pages 12-22 to 12-24.** The bound of covering and binning: with `L` codewords and
`M` bins there is a code with `(Xⁿ, Yⁿ, Uⁿ(L)) ∈ T` except with probability at most
`δ + P{(Xⁿ, Uⁿ) not typical} + P{(Xⁿ, Yⁿ, Uⁿ) ∉ T} / δ + exp(-L e^{-n(I(X; U) + 3ε)}) +
(L / M) e^{-n(I(Y; U) - 3ε)}`,
if `T` forces `(Yⁿ, Uⁿ)` to be jointly typical. -/
theorem exists_wz_code_le (hP : IsPMF P) (hq : IsChannel q) (hW : IsChannel W)
    (hPW : ∀ x y, P (x, y) = margFst P x * W x y) (hL : 0 < L) (hM : 0 < M) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : 0 < δ) (T : Finset (Fin n → (α × γ) × υ))
    (hTS : ∀ (ω : Fin n → α × γ) (u : Fin n → υ), zipSeq ω u ∈ T →
      (sndSeq ω, u) ∈ jointTypicalSet (siYU P q) n ε) :
    ∃ (enc : (Fin n → α) → Fin M) (dec : Fin M → (Fin n → γ) → Fin n → υ),
      ∑ ω, iidPMF P n ω * (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ T then 0 else 1) ≤
      δ + (1 - prob (jointIid (jointOf (margFst P) q) n)
          (jointTypicalSet (jointOf (margFst P) q) n ε)) +
        (1 - prob (iidPMF (siLaw P q) n) T) / δ +
        exp (-(exp (-(n * (mutualInfoOf (margFst P) q + 3 * ε))) * L)) +
        L / M * exp (-(n * (I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q] - 3 * ε))) := by
  have hne : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set l₀ : Fin L := ⟨0, hL⟩
  set r := outDist (margFst P) q with hr'
  have hp : IsPMF (margFst P) := hP.dist _
  have hr : IsPMF r := outDist_isPMF hp hq
  have hYU := siYU_isPMF hP hq
  set S := jointTypicalSet (siYU P q) n ε
  set A := coverSet W T (jointOf (margFst P) q) ε δ
  set enc : (Fin L → Fin n → υ) → (Fin n → α) → Fin L := fun C => typicalEncode A C l₀
  have hlaw := iidPMF_isPMF (iidPMF_isPMF hr n) L
  have hB : IsPMF (iidPMF (uniformPMF (Fin M)) L) := iidPMF_isPMF uniformPMF_isPMF L
  have hμ := iidPMF_isPMF hP n
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set Bad₁ : (Fin L → Fin n → υ) → ℝ := fun C =>
    ∑ ω, iidPMF P n ω * (if zipSeq ω (C (enc C (fstSeq ω))) ∈ T then 0 else 1) with hBad₁
  set Cnt : (Fin L → Fin n → υ) → ℝ := fun C => ∑ ω, iidPMF P n ω *
    ∑ l, (if (sndSeq ω, C l) ∈ S then (1 : ℝ) else 0) with hCnt
  -- For a fixed codebook, over the bins.
  have hfix : ∀ C : Fin L → Fin n → υ, ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
      ∑ ω, iidPMF P n ω * (if zipSeq ω (C (wzIndex B S C l₀ (B (enc C (fstSeq ω))) (sndSeq ω))) ∈ T
        then 0 else 1) ≤ Bad₁ C + Cnt C / M := fun C => by
    have h1 : ∀ B : Fin L → Fin M, ∑ ω, iidPMF P n ω *
        (if zipSeq ω (C (wzIndex B S C l₀ (B (enc C (fstSeq ω))) (sndSeq ω))) ∈ T then 0 else 1) ≤
        Bad₁ C + ∑ ω, iidPMF P n ω * ∑ l' ∈ univ.erase (enc C (fstSeq ω)),
          (if B l' = B (enc C (fstSeq ω)) then 1 else 0) *
            (if (sndSeq ω, C l') ∈ S then 1 else 0) := fun B => by
      rw [hBad₁, ← sum_add_distrib]
      refine sum_le_sum fun ω _ => ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (wzIndex_not_mem_le l₀ _ hTS ω) (hμ.nonneg ω)
    calc _ ≤ ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B * (Bad₁ C +
          ∑ ω, iidPMF P n ω * ∑ l' ∈ univ.erase (enc C (fstSeq ω)),
            (if B l' = B (enc C (fstSeq ω)) then 1 else 0) *
              (if (sndSeq ω, C l') ∈ S then 1 else 0)) :=
          sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (h1 B) (hB.nonneg B)
      _ = Bad₁ C + ∑ ω, iidPMF P n ω * ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
            ∑ l' ∈ univ.erase (enc C (fstSeq ω)),
              (if B l' = B (enc C (fstSeq ω)) then 1 else 0) *
                (if (sndSeq ω, C l') ∈ S then 1 else 0) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hB.sum_eq_one, one_mul]
          congr 1
          simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun ω _ => sum_congr rfl fun B _ => sum_congr rfl fun l' _ => ?_
          ring
      _ ≤ Bad₁ C + ∑ ω, iidPMF P n ω *
            ((∑ l', if (sndSeq ω, C l') ∈ S then (1 : ℝ) else 0) / M) := by
          gcongr with ω
          · exact hμ.nonneg ω
          · exact sum_bins_erase_le hM _ fun l' => by split_ifs <;> norm_num
      _ = _ := by
          simp only [hCnt, sum_div, mul_sum]
          congr 1
          refine sum_congr rfl fun ω _ => sum_congr rfl fun l _ => by ring
  -- Over the codebooks.
  have hC₁ := sum_codebook_triple_le hP hq hW hPW l₀ hε hδ T
  have hC₂ := sum_codebook_count_eq (L := L) (P := P) hr S
  have hind : ∑ z ∈ S, iidPMF (margSnd P) n z.1 * iidPMF r n z.2 ≤
      exp (-(n * (I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q] - 3 * ε))) := by
    have := prob_indep_jointTypicalSet_le hYU n ε
    rwa [margFst_siYU hq, margSnd_siYU, mutualInfo_siYU] at this
  have hbound : ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * (Bad₁ C + Cnt C / M) ≤
      δ + (1 - prob (jointIid (jointOf (margFst P) q) n)
          (jointTypicalSet (jointOf (margFst P) q) n ε)) +
        (1 - prob (iidPMF (siLaw P q) n) T) / δ +
        exp (-(exp (-(n * (mutualInfoOf (margFst P) q + 3 * ε))) * L)) +
        L / M * exp (-(n * (I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q] - 3 * ε))) := by
    have e0 : ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * (Bad₁ C + Cnt C / M) =
        ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * Bad₁ C +
          ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * (Cnt C / M) := by
      simp only [mul_add, sum_add_distrib]
    rw [e0]
    refine add_le_add hC₁ ?_
    have e : ∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * (Cnt C / M) =
        (∑ C : Fin L → Fin n → υ, iidPMF (iidPMF r n) L C * Cnt C) / M := by
      rw [sum_div]
      exact sum_congr rfl fun C _ => by ring
    rw [e, hC₂, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hM']
    exact mul_le_mul_of_nonneg_left hind (Nat.cast_nonneg L)
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hlaw hbound
  obtain ⟨B, hBd⟩ := exists_le_of_sum_mul_le hB ((hfix C).trans hC)
  exact ⟨fun x => B (enc C x), fun m y => C (wzIndex B S C l₀ m y), hBd⟩

end Binning

/-! ### Codes for typical triples -/

section Limits

variable {P : α × γ → ℝ} {q : α → υ → ℝ}

/-- If `a < b` and `L n ≥ e^{nb} / 2`, then `exp(-e^{-na} L n) → 0`. -/
lemma tendsto_exp_neg_cover {a b : ℝ} (hab : a < b) {L : ℕ → ℕ}
    (hL : ∀ n : ℕ, exp (n * b - log 2) ≤ L n) :
    Tendsto (fun n : ℕ => exp (-(exp (-(n * a)) * L n))) atTop (𝓝 0) := by
  refine tendsto_exp_neg_atTop_nhds_zero.comp ?_
  have hlow : ∀ n : ℕ, exp (n * (b - a) - log 2) ≤ exp (-(n * a)) * L n := fun n => by
    calc exp (n * (b - a) - log 2) = exp (-(n * a)) * exp (n * b - log 2) := by
          rw [← exp_add]
          ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (hL n) (exp_pos _).le
  refine tendsto_atTop_mono hlow (tendsto_exp_atTop.comp ?_)
  exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const
    (sub_pos.2 hab))

/-- **Lecture 12, pages 12-9 and 12-10.** If `R > I(X; U)` and `Tₙ` are sets of typical triples,
there are codebooks of `2^⌊nR⌋` sequences with `(Xⁿ, Yⁿ, Uⁿ(M)) ∈ Tₙ` except with probability at
most `δ`, for `n` large. -/
theorem eventually_causal_code (hP : IsPMF P) (hq : IsChannel q) {R : ℝ}
    (hR : mutualInfoOf (margFst P) q < R * log 2) (T : ∀ n : ℕ, Finset (Fin n → (α × γ) × υ))
    (hT : Tendsto (fun n => prob (iidPMF (siLaw P q) n) (T n)) atTop (𝓝 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ (enc : (Fin n → α) → Fin (2 ^ ⌊n * R⌋₊))
      (C : Fin (2 ^ ⌊n * R⌋₊) → Fin n → υ),
      ∑ ω, iidPMF P n ω *
        (open Classical in if zipSeq ω (C (enc (fstSeq ω))) ∈ T n then (0 : ℝ) else 1) ≤ δ := by
  classical
  obtain ⟨W, hW, hPW⟩ := exists_side_channel hP
  set I := mutualInfoOf (margFst P) q with hI
  have hp : IsPMF (margFst P) := hP.dist _
  have hJ : IsPMF (jointOf (margFst P) q) := jointOf_isPMF hp hq
  set ε := (R * log 2 - I) / 4 with hε'
  have hε : 0 < ε := by rw [hε']; linarith
  have ha : I + 3 * ε < R * log 2 := by rw [hε']; linarith
  have t₁ : Tendsto (fun n => 1 - prob (jointIid (jointOf (margFst P) q) n)
      (jointTypicalSet (jointOf (margFst P) q) n ε)) atTop (𝓝 0) := by
    simpa using (tendsto_prob_jointTypicalSet hJ hε).const_sub 1
  have t₂ : Tendsto (fun n => (1 - prob (iidPMF (siLaw P q) n) (T n)) / (δ / 2)) atTop (𝓝 0) := by
    simpa using (hT.const_sub 1).div_const (δ / 2)
  have t₃ := tendsto_exp_neg_cover ha fun n => exp_le_two_pow_floor n R
  have hsum := (t₁.add t₂).add t₃
  simp only [add_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds (half_pos hδ))] with n hn
  have hL : 0 < 2 ^ ⌊n * R⌋₊ := by positivity
  have hb := sum_codebook_triple_le hP hq hW hPW (⟨0, hL⟩ : Fin (2 ^ ⌊n * R⌋₊)) hε.le (half_pos hδ)
    (T n)
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (iidPMF_isPMF (iidPMF_isPMF (outDist_isPMF hp hq) n) (2 ^ ⌊n * R⌋₊)) hb
  refine ⟨_, C, hC.trans ?_⟩
  simp only [hI] at hn
  linarith

/-- `P{(Yⁿ, Uⁿ) jointly typical} → 1` for i.i.d. triples. -/
private lemma prob_typical_YU (n : ℕ) (S : Finset ((Fin n → γ) × (Fin n → υ))) :
    prob (jointIid (siYU P q) n) S = ∑ t : Fin n → (α × γ) × υ, iidPMF (siLaw P q) n t *
      (open Classical in if (fun i => (t i).1.2, fun i => (t i).2) ∈ S then (1 : ℝ) else 0) := by
  classical
  have e : ∀ F : (Fin n → γ × υ) → ℝ, ∑ w, iidPMF (siYU P q) n w * F w =
      ∑ t : Fin n → (α × γ) × υ, iidPMF (siLaw P q) n t * F fun i => ((t i).1.2, (t i).2) :=
    fun F => by
      have h := dist_iidPMF_comp (siLaw P q) n fun z => (z.1.2, z.2)
      have h2 := sum_dist_mul (iidPMF (siLaw P q) n) (fun t i => ((t i).1.2, (t i).2)) F
      rw [h] at h2
      exact h2
  rw [show (∑ t : Fin n → (α × γ) × υ, iidPMF (siLaw P q) n t *
    (if (fun i => (t i).1.2, fun i => (t i).2) ∈ S then (1 : ℝ) else 0)) = _ from
    (e fun w => if (fun i => (w i).1, fun i => (w i).2) ∈ S then (1 : ℝ) else 0).symm,
    ← sum_jointIid (siYU P q) n]
  have e' : prob (jointIid (siYU P q) n) S = ∑ z, if z ∈ S then jointIid (siYU P q) n z else 0 := by
    rw [prob, sum_ite_mem, univ_inter]
  rw [e']
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : z ∈ S
  · have : ((fun i => (zipSeq z.1 z.2 i).1, fun i => (zipSeq z.1 z.2 i).2) :
      (Fin n → γ) × (Fin n → υ)) = z := rfl
    simp [this, hz]
  · have : ((fun i => (zipSeq z.1 z.2 i).1, fun i => (zipSeq z.1 z.2 i).2) :
      (Fin n → γ) × (Fin n → υ)) = z := rfl
    simp [this, hz]

/-- **Lecture 12, pages 12-23 and 12-24.** If `R > I(X; U) - I(Y; U)` and `Tₙ` are sets of typical
triples, there are codes with `2^⌊nR⌋` indices and with `(Xⁿ, Yⁿ, Uⁿ(M, Yⁿ)) ∈ Tₙ` except with
probability at most `δ`, for `n` large. -/
theorem eventually_wz_code (hP : IsPMF P) (hq : IsChannel q) {R : ℝ}
    (hR : sideRate 1 P q < R * log 2) (T : ∀ n : ℕ, Finset (Fin n → (α × γ) × υ))
    (hT : Tendsto (fun n => prob (iidPMF (siLaw P q) n) (T n)) atTop (𝓝 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ (enc : (Fin n → α) → Fin (2 ^ ⌊n * R⌋₊))
      (dec : Fin (2 ^ ⌊n * R⌋₊) → (Fin n → γ) → Fin n → υ),
      ∑ ω, iidPMF P n ω * (open Classical in
        if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ T n then (0 : ℝ) else 1) ≤ δ := by
  classical
  obtain ⟨W, hW, hPW⟩ := exists_side_channel hP
  set I := mutualInfoOf (margFst P) q with hI
  set I' := I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q] with hI'
  have hrate : sideRate 1 P q = I - I' := by
    rw [sideRate, one_mul, hI, mutualInfoOf_side]
  rw [hrate] at hR
  have hI0 : 0 ≤ I := by
    rw [hI, mutualInfoOf_side]
    exact mutualInfo_nonneg (siLaw_isPMF hP hq) _ _
  have hp : IsPMF (margFst P) := hP.dist _
  have hJ : IsPMF (jointOf (margFst P) q) := jointOf_isPMF hp hq
  have hYU := siYU_isPMF (P := P) hP hq
  set ε := (R * log 2 - (I - I')) / 8 with hε'
  have hε : 0 < ε := by rw [hε']; linarith
  set G := R * log 2 - (I - I') - 7 * ε with hG
  have hG0 : 0 < G := by simp only [hG, hε']; linarith
  set b := I + 4 * ε with hb
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  set Ln : ℕ → ℕ := fun n => ⌈exp (n * b)⌉₊ with hLn
  have hLle : ∀ n : ℕ, exp (n * b) ≤ Ln n := fun n => Nat.le_ceil _
  have hLub : ∀ n : ℕ, (Ln n : ℝ) ≤ 2 * exp (n * b) := fun n => by
    have h1 : 1 ≤ exp (n * b) := one_le_exp (by positivity)
    have := (Nat.ceil_lt_add_one (exp_pos (n * b)).le).le
    simp only [hLn]
    linarith
  -- The sets of typical triples, with `(Yⁿ, Uⁿ)` jointly typical.
  set S := fun n : ℕ => jointTypicalSet (siYU P q) n ε with hS
  set T' := fun n : ℕ => (T n).filter fun t => (fun i => (t i).1.2, fun i => (t i).2) ∈ S n with hT'
  have hT'lim : Tendsto (fun n => prob (iidPMF (siLaw P q) n) (T' n)) atTop (𝓝 1) := by
    have hS' := tendsto_prob_jointTypicalSet hYU hε
    have hlow : ∀ n, prob (iidPMF (siLaw P q) n) (T n) -
        (1 - prob (jointIid (siYU P q) n) (S n)) ≤ prob (iidPMF (siLaw P q) n) (T' n) := fun n => by
      have hμ := iidPMF_isPMF (siLaw_isPMF hP hq) n
      have e1 : prob (iidPMF (siLaw P q) n) (T n) =
          ∑ t, if t ∈ T n then iidPMF (siLaw P q) n t else 0 := by
        rw [prob, sum_ite_mem, univ_inter]
      have e2 : prob (iidPMF (siLaw P q) n) (T' n) =
          ∑ t, if t ∈ T' n then iidPMF (siLaw P q) n t else 0 := by
        rw [prob, sum_ite_mem, univ_inter]
      have key : ∑ t : Fin n → (α × γ) × υ, ((if t ∈ T n then iidPMF (siLaw P q) n t else 0) +
          iidPMF (siLaw P q) n t *
            (if (fun i => (t i).1.2, fun i => (t i).2) ∈ S n then (1 : ℝ) else 0) -
          iidPMF (siLaw P q) n t) ≤ ∑ t, if t ∈ T' n then iidPMF (siLaw P q) n t else 0 := by
        refine sum_le_sum fun t _ => ?_
        have h0 := hμ.nonneg t
        by_cases h1 : t ∈ T n <;> by_cases h2 : (fun i => (t i).1.2, fun i => (t i).2) ∈ S n <;>
          simp [hT', h1, h2, h0]
      rw [sum_sub_distrib, sum_add_distrib, hμ.sum_eq_one] at key
      rw [prob_typical_YU, e1, e2]
      linarith
    have hup : ∀ n, prob (iidPMF (siLaw P q) n) (T' n) ≤ 1 := fun n =>
      prob_le_one (iidPMF_isPMF (siLaw_isPMF hP hq) n) _
    have hlim : Tendsto (fun n => prob (iidPMF (siLaw P q) n) (T n) -
        (1 - prob (jointIid (siYU P q) n) (S n))) atTop (𝓝 1) := by
      simpa using hT.sub (hS'.const_sub 1)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup
  have hTS : ∀ n (ω : Fin n → α × γ) (u : Fin n → υ), zipSeq ω u ∈ T' n →
      (sndSeq ω, u) ∈ jointTypicalSet (siYU P q) n ε := fun n ω u h =>
    (mem_filter.1 h).2
  have ha : I + 3 * ε < b := by rw [hb]; linarith
  have t₁ : Tendsto (fun n => 1 - prob (jointIid (jointOf (margFst P) q) n)
      (jointTypicalSet (jointOf (margFst P) q) n ε)) atTop (𝓝 0) := by
    simpa using (tendsto_prob_jointTypicalSet hJ hε).const_sub 1
  have t₂ : Tendsto (fun n => (1 - prob (iidPMF (siLaw P q) n) (T' n)) / (δ / 2)) atTop (𝓝 0) := by
    simpa using (hT'lim.const_sub 1).div_const (δ / 2)
  have t₃ := tendsto_exp_neg_cover ha (L := Ln) fun n =>
    (exp_le_exp.2 (by linarith [log_pos one_lt_two])).trans (hLle n)
  have t₄ : Tendsto (fun n : ℕ => 4 * exp (-(n * G))) atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_mul_nat hG0).const_mul 4
  have hsum := ((t₁.add t₂).add t₃).add t₄
  simp only [add_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds (half_pos hδ))] with n hn
  have hM : 0 < 2 ^ ⌊n * R⌋₊ := by positivity
  have hL : 0 < Ln n := Nat.ceil_pos.2 (exp_pos _)
  obtain ⟨enc, dec, hbd⟩ := exists_wz_code_le hP hq hW hPW hL hM hε.le (half_pos hδ) (T' n)
    (hTS n)
  refine ⟨enc, dec, ?_⟩
  -- The binning term.
  have hbin : ((Ln n : ℕ) : ℝ) / ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) * exp (-(n * (I' - 3 * ε))) ≤
      4 * exp (-(n * G)) := by
    have hMlow := exp_le_two_pow_floor n R
    have hdiv : ((Ln n : ℕ) : ℝ) / ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) ≤
        2 * exp (n * b) / exp (n * (R * log 2) - log 2) :=
      div_le_div₀ (by positivity) (hLub n) (exp_pos _) hMlow
    calc _ ≤ 2 * exp (n * b) / exp (n * (R * log 2) - log 2) * exp (-(n * (I' - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hdiv (exp_pos _).le
      _ = 4 * exp (-(n * G)) := by
          have e4 : (4 : ℝ) = 2 * exp (log 2) := by rw [exp_log two_pos]; norm_num
          rw [e4, mul_assoc, mul_div_assoc, ← exp_sub, mul_assoc, ← exp_add, ← exp_add]
          congr 2
          simp only [hG, hb]
          ring
  have hmono : ∀ ω, iidPMF P n ω * (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ T n then
      (0 : ℝ) else 1) ≤ iidPMF P n ω * (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ T' n then
      (0 : ℝ) else 1) := fun ω => by
    refine mul_le_mul_of_nonneg_left ?_ (iidPMF_isPMF hP n |>.nonneg ω)
    by_cases h : zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ T' n
    · have := (mem_filter.1 h).1
      simp [h, this]
    · split_ifs <;> norm_num
  refine (sum_le_sum fun ω _ => hmono ω).trans (hbd.trans ?_)
  simp only [hI, hLn] at hn hbin ⊢
  linarith

end Limits

end InfoTheory
