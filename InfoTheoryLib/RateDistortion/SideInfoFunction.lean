/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.SideInfoConverse

/-!
# Coding for computing with side information

This file proves Theorem 1 of Lecture 22 of [elgamal2010], of Yamamoto: the rate–distortion function
for estimating a function `Z = g(X, Y)` at a decoder with side information `Y`. We allow any
distortion measure `e((x, y), ẑ)`, of which `d(g(x, y), ẑ)` is a special case. We also prove the
optimal rate for computing `Z` losslessly.

## Main definitions

* `WZCode.funDistortion`, `WZCode.funErrProb`: the performance of a code for computing a function.
* `IsAchievableFunBits`, `rateFunBits`: achievable rates, and the rate–distortion function, in bits.
* `funCost`, `funRD`: `min I(X; U | Y)` over `p(u | x)` and `ẑ(u, y)` with `E e(X, Y, Ẑ) ≤ D`.
* `IsLosslessFunBits`, `funLosslessRate`: lossless computing.

## Main statements

* `isAchievableFunBits_of_lt`, `WZCode.exists_fun_kernel_le`: achievability, and the converse.
* `rateFunBits_eq`: **Theorem 1 of Lecture 22**.
* `losslessFunBits_eq`: the optimal lossless rate `R*_g = min I(X; U | Y)` over `p(u | x)` with
  `H(Z | U, Y) = 0`.
* `condEntropy_le_funLosslessRate`, `funLosslessRate_le_condEntropy`: `H(Z | Y) ≤ R*_g ≤ H(X | Y)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α γ β υ : Type*} [Fintype α] [Fintype γ] [Fintype υ] {P : α × γ → ℝ}

/-! ### The problem -/

/-- The expected distortion `E e((Xⁿ, Yⁿ), Ẑⁿ)` of a code. -/
def WZCode.funDistortion {M n : ℕ} (c : WZCode M n α γ β) (P : α × γ → ℝ) (e : α × γ → β → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * seqDistortion e ω (c.dec (c.enc (fstSeq ω)) (sndSeq ω))

open Classical in
/-- The probability of error `P{Ẑⁿ ≠ Zⁿ}` of a code for computing `Z = g(X, Y)`. -/
def WZCode.funErrProb {M n : ℕ} (c : WZCode M n α γ β) (P : α × γ → ℝ) (g : α × γ → β) : ℝ :=
  ∑ ω, if c.dec (c.enc (fstSeq ω)) (sndSeq ω) ≠ fun i => g (ω i) then iidPMF P n ω else 0

/-- **Lecture 22 of [elgamal2010], page 22-3.** A pair `(R, D)`, with `R` in bits, is achievable for
computing with side information if there are `(2^{nR}, n)` codes with
`limsup E e(X, Y, Ẑ) ≤ D`. -/
def IsAchievableFunBits (P : α × γ → ℝ) (e : α × γ → β → ℝ) (R D : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, WZCode (2 ^ ⌊n * R⌋₊) n α γ β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).funDistortion P e ≤ D + ε

/-- **Lecture 22 of [elgamal2010], page 22-3.** The rate–distortion function `R_g(D)`, in bits. -/
def rateFunBits (P : α × γ → ℝ) (e : α × γ → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | IsAchievableFunBits P e R D}

/-- The cost `e((x, y), ẑ(u, y))`. -/
def funCost (e : α × γ → β → ℝ) (f : υ → γ → β) : υ → α → γ → ℝ := fun u x y => e (x, y) (f u y)

/-- **Theorem 1 of Lecture 22 of [elgamal2010], page 22-4.** `min I(X; U | Y)` over `p(u | x)` and
`ẑ(u, y)` with `E e(X, Y, Ẑ) ≤ D`, with `U` on `Fin k` for some `k`, in nats. -/
def funRD (P : α × γ → ℝ) (e : α × γ → β → ℝ) (D : ℝ) : ℝ :=
  sInf {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
    sideCost P q (funCost e f) ≤ D ∧ sideRate 1 P q = I}

/-! ### The minimum -/

section Min

variable {q : α → υ → ℝ} {e : α × γ → β → ℝ}

/-- The cardinality bound for a function: `|𝒰'| = |𝒳| + 3`. -/
theorem exists_fun_reduce (hP : IsPMF P) (hq : IsChannel q) (e : α × γ → β → ℝ) (f : υ → γ → β) :
    ∃ (q' : α → Fin (Fintype.card α + 3) → ℝ) (f' : Fin (Fintype.card α + 3) → γ → β),
      IsChannel q' ∧ sideRate 1 P q' = sideRate 1 P q ∧
        sideCost P q' (funCost e f') = sideCost P q (funCost e f) := by
  obtain ⟨q', g, hq', h1, h2⟩ := exists_side_reduce (κ := Unit) hP hq 1
    (fun _ => funCost e f) (N := Fintype.card α + 3) (by simp only [Fintype.card_unit])
  exact ⟨q', fun j => f (g j), hq', h1, h2 ()⟩

/-- The set of the rates is that for `|𝒰| = |𝒳| + 3`. -/
lemma funRD_set_eq (hP : IsPMF P) (e : α × γ → β → ℝ) (D : ℝ) :
    {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
      sideCost P q (funCost e f) ≤ D ∧ sideRate 1 P q = I} =
    ⋃ f : Fin (Fintype.card α + 3) → γ → β, (fun q : α → Fin (Fintype.card α + 3) → ℝ =>
      sideRate 1 P q) '' {q | IsChannel q ∧ sideCost P q (funCost e f) ≤ D} := by
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨k, q, f, hq, hD, rfl⟩
    obtain ⟨q', f', hq', h1, h2⟩ := exists_fun_reduce hP hq e f
    exact ⟨f', q', ⟨hq', h2.le.trans hD⟩, h1⟩
  · rintro ⟨f, q, ⟨hq, hD⟩, rfl⟩
    exact ⟨_, q, f, hq, hD, rfl⟩

lemma isCompact_funRD_set [Finite β] (hP : IsPMF P) (e : α × γ → β → ℝ) (D : ℝ) :
    IsCompact {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
      sideCost P q (funCost e f) ≤ D ∧ sideRate 1 P q = I} := by
  rw [funRD_set_eq hP]
  exact isCompact_iUnion fun f => isCompact_side_rates hP 1 _ D

/-- `min I(X; U | Y) ≤ I(X; U | Y)` for every `p(u | x)` and `ẑ(u, y)` with `E e(X, Y, Ẑ) ≤ D`,
with `U` on any finite set. -/
theorem funRD_le [Finite β] (hP : IsPMF P) (hq : IsChannel q) (f : υ → γ → β) {D : ℝ}
    (hD : sideCost P q (funCost e f) ≤ D) : funRD P e D ≤ sideRate 1 P q := by
  obtain ⟨q', f', hq', h1, h2⟩ := exists_fun_reduce hP hq e f
  exact csInf_le (isCompact_funRD_set hP e D).bddBelow ⟨_, q', f', hq', h2.le.trans hD, h1⟩

omit [Fintype υ] in
/-- `E c(U, X, Y)` for `U = X`. -/
lemma sideCost_identityKernel [DecidableEq α] (P : α × γ → ℝ) (c : α → α → γ → ℝ) :
    sideCost P identityKernel c = ∑ z, P z * c z.1 z.1 z.2 := by
  rw [sideCost, Fintype.sum_prod_type]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_eq_single z.1]
  · simp [siLaw, jointOf, identityKernel]
  · intro u _ hu
    simp [siLaw, jointOf, identityKernel, hu]
  · simp

/-- With `U = X` the decoder can minimize the distortion for each `(x, y)`: every `D ≥ D_min` is
feasible, where `D_min = E min_ẑ e(X, Y, ẑ)`. -/
lemma exists_fun_feasible [Finite β] [Nonempty β] [DecidableEq α] (e : α × γ → β → ℝ) {D : ℝ}
    (hD : minDistortion P e ≤ D) :
    ∃ f : α → γ → β, sideCost P identityKernel (funCost e f) ≤ D := by
  choose f hf using fun z : α × γ => exists_eq_ciInf_of_finite (f := e z)
  refine ⟨fun x y => f (x, y), ?_⟩
  rw [sideCost_identityKernel]
  refine le_trans (le_of_eq ?_) hD
  rw [minDistortion]
  exact sum_congr rfl fun z _ => by simp only [funCost, hf]

/-- **Lecture 22, page 22-4.** The minimum is attained, with `|𝒰| ≤ |𝒳| + 3`, for `D ≥ D_min`. -/
theorem exists_funRD_eq [Finite β] [Nonempty β] (hP : IsPMF P) {D : ℝ}
    (hD : minDistortion P e ≤ D) :
    ∃ (q : α → Fin (Fintype.card α + 3) → ℝ) (f : Fin (Fintype.card α + 3) → γ → β),
      IsChannel q ∧ sideCost P q (funCost e f) ≤ D ∧ sideRate 1 P q = funRD P e D := by
  classical
  have hne : {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
      sideCost P q (funCost e f) ≤ D ∧ sideRate 1 P q = I}.Nonempty := by
    obtain ⟨f₀, hf₀⟩ := exists_fun_feasible (P := P) e hD
    obtain ⟨q', f', hq', -, h2⟩ := exists_fun_reduce hP (identityKernel_isChannel (α := α)) e f₀
    exact ⟨_, _, q', f', hq', h2.le.trans hf₀, rfl⟩
  have hmem := (isCompact_funRD_set hP e D).sInf_mem hne
  rw [funRD_set_eq hP] at hmem
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨f, q, ⟨hq, hc⟩, he⟩ := hmem
  refine ⟨q, f, hq, hc, he.trans ?_⟩
  rw [funRD, funRD_set_eq hP]

/-- **The closedness of the rates and distortions.** If there are, for every `ε > 0`, `p(u | x)` and
`ẑ(u, y)` on `Fin N` with `E e(X, Y, Ẑ) ≤ D + ε` and `I(X; U | Y) ≤ R`, then there are such laws
with `E e(X, Y, Ẑ) ≤ D`. -/
theorem exists_le_of_forall_fun [Finite β] {N : ℕ} (hP : IsPMF P) {R D : ℝ}
    (h : ∀ ε > 0, ∃ (q : α → Fin N → ℝ) (f : Fin N → γ → β), IsChannel q ∧
      sideCost P q (funCost e f) ≤ D + ε ∧ sideRate 1 P q ≤ R) :
    ∃ (q : α → Fin N → ℝ) (f : Fin N → γ → β), IsChannel q ∧
      sideCost P q (funCost e f) ≤ D ∧ sideRate 1 P q ≤ R := by
  have hK : IsCompact {q : α → Fin N → ℝ | IsChannel q ∧ sideRate 1 P q ≤ R} := by
    have hcl : IsClosed ({q : α → Fin N → ℝ | IsChannel q} ∩
        (fun q => sideRate 1 P q) ⁻¹' Set.Iic R) :=
      (continuousOn_sideRate hP 1).preimage_isClosed_of_isClosed
        isCompact_setOf_isChannel.isClosed isClosed_Iic
    exact isCompact_setOf_isChannel.of_isClosed_subset hcl fun q hq => hq.1
  set C : Set ℝ := ⋃ f : Fin N → γ → β,
    (fun q : α → Fin N → ℝ => sideCost P q (funCost e f)) ''
      {q | IsChannel q ∧ sideRate 1 P q ≤ R} with hC
  have hCc : IsCompact C := isCompact_iUnion fun f => hK.image (continuous_sideCost P _)
  have hmemC : ∀ ε > 0, ∃ c ∈ C, c ≤ D + ε := fun ε hε => by
    obtain ⟨q, f, hq, hc, hr⟩ := h ε hε
    exact ⟨_, Set.mem_iUnion.2 ⟨f, q, ⟨hq, hr⟩, rfl⟩, hc⟩
  have hne : C.Nonempty :=
    let ⟨c, hc, _⟩ := hmemC 1 one_pos
    ⟨c, hc⟩
  have hmin := hCc.sInf_mem hne
  simp only [hC, Set.mem_iUnion, Set.mem_image] at hmin
  obtain ⟨f, q, ⟨hq, hr⟩, he⟩ := hmin
  refine ⟨q, f, hq, ?_, hr⟩
  rw [he]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨c, hc, hle⟩ := hmemC ε hε
  exact (csInf_le hCc.bddBelow hc).trans hle

end Min

/-! ### Achievability -/

section Achievability

variable {q : α → υ → ℝ} {e : α × γ → β → ℝ}

/-- The cost of a triple. -/
def funLetter (e : α × γ → β → ℝ) (f : υ → γ → β) (z : (α × γ) × υ) : ℝ := e z.1 (f z.2 z.1.2)

lemma expect_funLetter (P : α × γ → ℝ) (q : α → υ → ℝ) (e : α × γ → β → ℝ) (f : υ → γ → β) :
    expect (siLaw P q) (funLetter e f) = sideCost P q (funCost e f) := by
  simp only [expect, sideCost]
  exact sum_congr rfl fun z _ => mul_comm _ _

/-- The triples whose average cost is typical. -/
def funTypical (P : α × γ → ℝ) (q : α → υ → ℝ) (e : α × γ → β → ℝ) (f : υ → γ → β) (ε : ℝ) (n : ℕ) :
    Finset (Fin n → (α × γ) × υ) :=
  open Classical in univ.filter fun t =>
    |(sampleMean fun i => funLetter e f (t i)) - expect (siLaw P q) (funLetter e f)| < ε

/-- By the weak law of large numbers, i.i.d. triples have a typical average cost. -/
lemma tendsto_prob_funTypical (hP : IsPMF P) (hq : IsChannel q) (e : α × γ → β → ℝ) (f : υ → γ → β)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF (siLaw P q) n) (funTypical P q e f ε n)) atTop (𝓝 1) := by
  classical
  have hl := weak_law (siLaw_isPMF hP hq) (funLetter e f) ε hε
  have h' : ∀ n, prob (iidPMF (siLaw P q) n) (funTypical P q e f ε n) =
      1 - prob (iidPMF (siLaw P q) n) (univ.filter fun t =>
        ε ≤ |(sampleMean fun i => funLetter e f (t i)) - expect (siLaw P q) (funLetter e f)|) :=
    fun n => by
      have h := sum_filter_add_sum_filter_not univ (fun t : Fin n → (α × γ) × υ =>
        |(sampleMean fun i => funLetter e f (t i)) - expect (siLaw P q) (funLetter e f)| < ε)
        (iidPMF (siLaw P q) n)
      rw [(iidPMF_isPMF (siLaw_isPMF hP hq) n).sum_eq_one] at h
      simp only [not_lt] at h
      rw [eq_sub_iff_add_eq]
      convert h using 2 <;> rfl
  simp only [h']
  simpa using hl.const_sub 1

/-- The distortion of a sequence is at most `E e(X, Y, Ẑ) + ε` on the typical triples, and at most
`d_max` otherwise. -/
lemma seqDistortion_le_of_funTypical [Finite β] [Nonempty β] (hP : IsPMF P) (hq : IsChannel q)
    (he : ∀ z b, 0 ≤ e z b) (f : υ → γ → β) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n)
    (ω : Fin n → α × γ) (u : Fin n → υ) :
    seqDistortion e ω (fun i => f (u i) (ω i).2) ≤
      sideCost P q (funCost e f) + ε + maxDistortion e *
        (open Classical in if zipSeq ω u ∈ funTypical P q e f ε n then (0 : ℝ) else 1) := by
  classical
  have hE : 0 ≤ sideCost P q (funCost e f) :=
    sum_nonneg fun z _ => mul_nonneg ((siLaw_isPMF hP hq).nonneg z) (he _ _)
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty (α × γ) := ⟨z⟩
  have h0 := maxDistortion_nonneg he
  by_cases ht : zipSeq ω u ∈ funTypical P q e f ε n
  · have h := (mem_filter.1 ht).2
    rw [expect_funLetter] at h
    simp only [ht, ite_true, mul_zero, add_zero]
    have e' : seqDistortion e ω (fun i => f (u i) (ω i).2) =
        sampleMean fun i => funLetter e f (zipSeq ω u i) := by
      simp only [seqDistortion, sampleMean, Fintype.card_fin]
      rfl
    rw [e']
    linarith [(abs_lt.1 h).2]
  · simp only [ht, ite_false, mul_one]
    have := seqDistortion_le_maxDistortion e hn ω fun i => f (u i) (ω i).2
    linarith

/-- **Theorem 1 of Lecture 22, achievability.** For `p(u | x)` and `ẑ(u, y)` with
`E e(X, Y, Ẑ) ≤ D`, every rate `R > I(X; U | Y)` bits is achievable. -/
theorem isAchievableFunBits_of_lt [Finite β] (hP : IsPMF P) (he : ∀ z b, 0 ≤ e z b)
    (hq : IsChannel q) (f : υ → γ → β) {R D : ℝ}
    (hD : sideCost P q (funCost e f) ≤ D) (hR : sideRate 1 P q / log 2 < R) :
    IsAchievableFunBits P e R D := by
  classical
  have hl := log_pos one_lt_two
  have hI : sideRate 1 P q < R * log 2 := (div_lt_iff₀ hl).1 hR
  have hR0 : 0 ≤ R := by
    have h0 := sideRate_nonneg (θ := 1) hP hq le_rfl
    exact (div_nonneg h0 hl.le).trans hR.le
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  obtain ⟨u₀, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF (hq z.1))
  have hβ : Nonempty β := ⟨f u₀ z.2⟩
  have hne := fun n : ℕ => WZCode.nonempty (α := α) (γ := γ) (β := β) (n := n)
    (M := 2 ^ ⌊n * R⌋₊) (by positivity)
  obtain ⟨c, hc⟩ := exists_seq_of_eventually (C := fun n => WZCode (2 ^ ⌊n * R⌋₊) n α γ β)
    (fun n c => c.funDistortion P e) (a := D) fun ε hε => by
      have hne' : Nonempty (α × γ) := ⟨z⟩
      have hm := maxDistortion_nonneg he
      have hδ : 0 < ε / 2 / (maxDistortion e + 1) := by positivity
      filter_upwards [eventually_wz_code hP hq hI (funTypical P q e f (ε / 2))
        (tendsto_prob_funTypical hP hq e f (half_pos hε)) hδ, eventually_gt_atTop 0]
        with n ⟨enc, dec, hC⟩ hn
      refine ⟨⟨enc, fun m y i => f (dec m y i) (y i)⟩, ?_⟩
      have hle : WZCode.funDistortion ⟨enc, fun m y i => f (dec m y i) (y i)⟩ P e ≤
          ∑ ω, iidPMF P n ω * (sideCost P q (funCost e f) + ε / 2 + maxDistortion e *
            (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ funTypical P q e f (ε / 2) n then
              (0 : ℝ) else 1)) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
          (seqDistortion_le_of_funTypical (q := q) hP hq he f (half_pos hε) hn ω
            (dec (enc (fstSeq ω)) (sndSeq ω))) ((iidPMF_isPMF hP n).nonneg ω)
      refine hle.trans ?_
      have e' : ∑ ω, iidPMF P n ω * (sideCost P q (funCost e f) + ε / 2 +
          maxDistortion e * (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈
            funTypical P q e f (ε / 2) n then (0 : ℝ) else 1)) =
          sideCost P q (funCost e f) + ε / 2 +
          maxDistortion e * ∑ ω, iidPMF P n ω * (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈
            funTypical P q e f (ε / 2) n then (0 : ℝ) else 1) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, (iidPMF_isPMF hP n).sum_eq_one, one_mul]
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun ω _ => by ring
      rw [e']
      have hb : maxDistortion e * ∑ ω, iidPMF P n ω *
          (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈
            funTypical P q e f (ε / 2) n then (0 : ℝ) else 1) ≤ ε / 2 := by
        calc _ ≤ maxDistortion e * (ε / 2 / (maxDistortion e + 1)) :=
              mul_le_mul_of_nonneg_left hC hm
          _ ≤ (maxDistortion e + 1) * (ε / 2 / (maxDistortion e + 1)) := by
              gcongr
              linarith
          _ = ε / 2 := by field_simp
      linarith
  exact ⟨hR0, c, hc⟩

end Achievability

/-! ### The converse and the theorem -/

section Converse

variable {e : α × γ → β → ℝ}

/-- **Lecture 22, page 22-4.** The single-letter bounds: every code gives `p(u | x)` and `ẑ(u, y)`
with `E e(X, Y, Ẑ) = E e(Xⁿ, Yⁿ, Ẑⁿ)` and `n I(X; U | Y) ≤ log M`, with `|𝒰| ≤ |𝒳| + 3`. -/
theorem WZCode.exists_fun_kernel_le {M n : ℕ} (c : WZCode M n α γ β) (hP : IsPMF P) (hn : 0 < n)
    (hM : 0 < M) (e : α × γ → β → ℝ) :
    ∃ (q : α → Fin (Fintype.card α + 3) → ℝ) (f : Fin (Fintype.card α + 3) → γ → β), IsChannel q ∧
      sideCost P q (funCost e f) = c.funDistortion P e ∧ n * sideRate 1 P q ≤ log M := by
  obtain ⟨y₀, q, hq, he, hr⟩ := WZCode.exists_aux_law hP hn hM c.enc
  have hcost : sideCost P q (funCost e (wzRecon c)) = c.funDistortion P e := by
    rw [he]
    refine sum_congr rfl fun ω _ => ?_
    congr 1
    simp only [seqDistortion, funCost, wzRecon_aux]
  obtain ⟨q', f', hq', h1, h2⟩ := exists_fun_reduce hP hq e (wzRecon c)
  exact ⟨q', f', hq', h2.trans hcost, by rwa [h1]⟩

/-- **Theorem 1 of Lecture 22, the converse.** If `(R, D)` is achievable, there are `p(u | x)` and
`ẑ(u, y)` with `E e(X, Y, Ẑ) ≤ D` and `I(X; U | Y) ≤ R`, in bits. -/
theorem IsAchievableFunBits.exists_kernel [Finite β] (hP : IsPMF P) {R D : ℝ}
    (h : IsAchievableFunBits P e R D) :
    ∃ (q : α → Fin (Fintype.card α + 3) → ℝ) (f : Fin (Fintype.card α + 3) → γ → β), IsChannel q ∧
      sideCost P q (funCost e f) ≤ D ∧ sideRate 1 P q ≤ R * log 2 := by
  obtain ⟨hR, c, hc⟩ := h
  refine exists_le_of_forall_fun hP fun ε hε => ?_
  obtain ⟨n, hn1, hn2⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
  obtain ⟨q, f, hq, h1, h2⟩ := (c n).exists_fun_kernel_le hP hn2 (by positivity) e
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn2
  exact ⟨q, f, hq, h1.trans_le hn1, le_of_mul_le_mul_left (h2.trans
    (by simpa using log_two_pow_floor_le n hR)) hn'⟩

/-- **Theorem 1 of Lecture 22 of [elgamal2010], page 22-4.** The rate–distortion function for
computing with side information at the decoder is `R_g(D) = min I(X; U | Y)`, over `p(u | x)` and
`ẑ(u, y)` with `E e(X, Y, Ẑ) ≤ D`, for `D ≥ D_min`, in bits. By `exists_funRD_eq`, the minimum is
attained with `|𝒰| ≤ |𝒳| + 3`. For `Z = g(X, Y)` take `e((x, y), ẑ) = d(g(x, y), ẑ)`. -/
theorem rateFunBits_eq [Finite β] [Nonempty β] (hP : IsPMF P) (he : ∀ z b, 0 ≤ e z b) {D : ℝ}
    (hD : minDistortion P e ≤ D) : rateFunBits P e D = funRD P e D / log 2 := by
  have hl := log_pos one_lt_two
  obtain ⟨q, f, hq, hc, hr⟩ := exists_funRD_eq (e := e) hP hD
  have hach : ∀ R, funRD P e D / log 2 < R → IsAchievableFunBits P e R D := fun R hR =>
    isAchievableFunBits_of_lt hP he hq f hc (by rwa [hr])
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, hach _ (lt_add_one _)⟩ (fun R hR => ?_)
    fun w hw => ⟨(funRD P e D / log 2 + w) / 2, hach _ (by linarith), by linarith⟩
  obtain ⟨q', f', hq', hc', hr'⟩ := hR.exists_kernel hP
  rw [div_le_iff₀ hl]
  exact (funRD_le hP hq' f' hc').trans hr'

end Converse

/-! ### Lossless computing -/

section Lossless

variable {q : α → υ → ℝ}

/-- **Lecture 22 of [elgamal2010], page 22-5.** A rate `R`, in bits, is achievable for computing
`Z = g(X, Y)` losslessly if there are `(2^{nR}, n)` codes with `P{Ẑⁿ ≠ Zⁿ} → 0`. -/
def IsLosslessFunBits (P : α × γ → ℝ) (g : α × γ → β) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, WZCode (2 ^ ⌊n * R⌋₊) n α γ β,
    Tendsto (fun n => (c n).funErrProb P g) atTop (𝓝 0)

/-- `Z` is a function `ẑ(u, y)` on the support of `p(x, y) p(u | x)`, which is `H(Z | U, Y) = 0`. -/
def IsFunOf (P : α × γ → ℝ) (q : α → υ → ℝ) (g : α × γ → β) (f : υ → γ → β) : Prop :=
  ∀ z, siLaw P q z ≠ 0 → f z.2 z.1.2 = g z.1

/-- **Lecture 22 of [elgamal2010], page 22-6.** `R*_g = min I(X; U | Y)` over `p(u | x)` with
`H(Z | U, Y) = 0`, with `U` on `Fin k` for some `k`, in nats. -/
def funLosslessRate (P : α × γ → ℝ) (g : α × γ → β) : ℝ :=
  sInf {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧ IsFunOf P q g f ∧
    sideRate 1 P q = I}

open Classical in
/-- The Hamming distortion of `Z`. -/
def funHamming (g : α × γ → β) : α × γ → β → ℝ := fun z b => hammingDistortion (g z) b

/-- The Hamming distortion of `Z` vanishes iff `Z = ẑ(U, Y)` almost surely. -/
lemma sideCost_funHamming_le_zero_iff (hP : IsPMF P) (hq : IsChannel q) (g : α × γ → β)
    (f : υ → γ → β) : sideCost P q (funCost (funHamming g) f) ≤ 0 ↔ IsFunOf P q g f := by
  have hμ := siLaw_isPMF hP hq
  have h0 : ∀ z ∈ (univ : Finset ((α × γ) × υ)), 0 ≤ siLaw P q z * funCost (funHamming g) f z.2
      z.1.1 z.1.2 := fun z _ => mul_nonneg (hμ.nonneg z) (by
    simp only [funCost, funHamming, hammingDistortion]
    split_ifs <;> norm_num)
  constructor
  · intro h z hz
    have h1 := (sum_eq_zero_iff_of_nonneg h0).1 (le_antisymm h (sum_nonneg h0)) z (mem_univ z)
    have h2 := (mul_eq_zero.1 h1).resolve_left hz
    simp only [funCost, funHamming, hammingDistortion] at h2
    by_contra hne
    exact absurd h2 (by simp [Ne.symm hne])
  · intro h
    refine (sum_eq_zero fun z _ => ?_).le
    by_cases hz : siLaw P q z = 0
    · rw [hz, zero_mul]
    · have := h z hz
      simp [funCost, funHamming, hammingDistortion, this]

/-- The Hamming distortion is at most the indicator of a block error. -/
lemma funDistortion_le_funErrProb {M n : ℕ}
    (c : WZCode M n α γ β) (hP : IsPMF P) (g : α × γ → β) :
    c.funDistortion P (funHamming g) ≤ c.funErrProb P g := by
  classical
  refine sum_le_sum fun ω _ => ?_
  have h0 := (iidPMF_isPMF hP n).nonneg ω
  have := seqDistortion_hamming_le (x := fun i => g (ω i))
    (y := c.dec (c.enc (fstSeq ω)) (sndSeq ω))
  have e' : seqDistortion (funHamming g) ω (c.dec (c.enc (fstSeq ω)) (sndSeq ω)) =
      seqDistortion hammingDistortion (fun i => g (ω i))
        (c.dec (c.enc (fstSeq ω)) (sndSeq ω)) := by
    simp only [seqDistortion, funHamming]
  rw [e']
  convert (mul_le_mul_of_nonneg_left this h0).trans_eq ?_ using 1
  split_ifs <;> simp

/-- **Lecture 22, pages 22-5 and 22-6, achievability.** If `H(Z | U, Y) = 0`, every rate
`R > I(X; U | Y)` bits is achievable for computing `Z` losslessly. -/
theorem isLosslessFunBits_of_lt [Finite β] (hP : IsPMF P) (hq : IsChannel q) {g : α × γ → β}
  {f : υ → γ → β}
    (hf : IsFunOf P q g f) {R : ℝ} (hR : sideRate 1 P q / log 2 < R) : IsLosslessFunBits P g R := by
  classical
  have hl := log_pos one_lt_two
  have hI : sideRate 1 P q < R * log 2 := (div_lt_iff₀ hl).1 hR
  have hR0 : 0 ≤ R := by
    have h0 := sideRate_nonneg (θ := 1) hP hq le_rfl
    exact (div_nonneg h0 hl.le).trans hR.le
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hβ : Nonempty β := ⟨g z⟩
  have hne := fun n : ℕ => WZCode.nonempty (α := α) (γ := γ) (β := β) (n := n)
    (M := 2 ^ ⌊n * R⌋₊) (by positivity)
  have hT : Tendsto (fun n => prob (iidPMF (siLaw P q) n) (supportTriples P q n)) atTop (𝓝 1) := by
    simp only [prob_supportTriples hP hq]
    exact tendsto_const_nhds
  obtain ⟨c, hc⟩ := exists_seq_of_eventually (C := fun n => WZCode (2 ^ ⌊n * R⌋₊) n α γ β)
    (fun n c => c.funErrProb P g) (a := 0) fun ε hε => by
      filter_upwards [eventually_wz_code hP hq hI (supportTriples P q) hT hε]
        with n ⟨enc, dec, hC⟩
      refine ⟨⟨enc, fun m y i => f (dec m y i) (y i)⟩, ?_⟩
      rw [zero_add]
      refine le_trans (sum_le_sum fun ω _ => ?_) hC
      by_cases ht : zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ supportTriples P q n
      · have hout : (fun i => f (dec (enc (fstSeq ω)) (sndSeq ω) i) (sndSeq ω i)) =
            fun i => g (ω i) := by
          funext i
          exact hf _ ((mem_filter.1 ht).2 i)
        simp [hout, ht]
      · simp only [ht, ite_false, mul_one]
        split_ifs
        · exact le_rfl
        · exact (iidPMF_isPMF hP n).nonneg ω
  exact ⟨hR0, c, tendsto_zero_of_eventually_le (fun n => sum_nonneg fun ω _ => by
    split_ifs
    · exact (iidPMF_isPMF hP n).nonneg ω
    · exact le_rfl) hc⟩

/-- A lossless code is a code of distortion `0` for the Hamming distortion of `Z`. -/
theorem IsLosslessFunBits.isAchievable {g : α × γ → β} {R : ℝ} (hP : IsPMF P)
    (h : IsLosslessFunBits P g R) : IsAchievableFunBits P (funHamming g) R 0 := by
  obtain ⟨hR, c, hc⟩ := h
  refine ⟨hR, c, fun ε hε => ?_⟩
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
  rw [zero_add]
  exact (funDistortion_le_funErrProb (c n) hP g).trans hn.le

omit [Fintype α] [Fintype γ] in
/-- The functions `ẑ(u, y) = g(u, y)` with `U = X`. -/
lemma isFunOf_identityKernel [DecidableEq α] (P : α × γ → ℝ) (g : α × γ → β) :
    IsFunOf P identityKernel g fun u y => g (u, y) := fun z hz => by
  have hu : z.2 = z.1.1 := by
    by_contra hne
    exact hz (by simp [siLaw, jointOf, identityKernel, hne])
  simp only [hu]

/-- The set of the rates of lossless computing is compact, and it is the set for `|𝒰| = |𝒳| + 3`. -/
lemma funLosslessRate_set_eq (hP : IsPMF P) (g : α × γ → β) :
    {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧ IsFunOf P q g f ∧
      sideRate 1 P q = I} =
    {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
      sideCost P q (funCost (funHamming g) f) ≤ 0 ∧ sideRate 1 P q = I} := by
  ext I
  constructor
  · rintro ⟨k, q, f, hq, hf, hr⟩
    exact ⟨k, q, f, hq, (sideCost_funHamming_le_zero_iff hP hq g f).2 hf, hr⟩
  · rintro ⟨k, q, f, hq, hf, hr⟩
    exact ⟨k, q, f, hq, (sideCost_funHamming_le_zero_iff hP hq g f).1 hf, hr⟩

/-- `R*_g` is the rate–distortion function at distortion `0`. -/
lemma funLosslessRate_eq_funRD (hP : IsPMF P) (g : α × γ → β) :
    funLosslessRate P g = funRD P (funHamming g) 0 := by
  rw [funLosslessRate, funLosslessRate_set_eq hP, funRD]

/-- `R*_g ≤ I(X; U | Y)` for every `p(u | x)` with `H(Z | U, Y) = 0`, with `U` on any finite set. -/
theorem funLosslessRate_le [Finite β] (hP : IsPMF P) (hq : IsChannel q) {g : α × γ → β}
    {f : υ → γ → β} (hf : IsFunOf P q g f) : funLosslessRate P g ≤ sideRate 1 P q := by
  rw [funLosslessRate_eq_funRD hP]
  exact funRD_le hP hq f ((sideCost_funHamming_le_zero_iff hP hq g f).2 hf)

/-- The minimum is attained. -/
theorem exists_funLosslessRate_eq [Finite β] (hP : IsPMF P) (g : α × γ → β) :
    ∃ (q : α → Fin (Fintype.card α + 3) → ℝ) (f : Fin (Fintype.card α + 3) → γ → β),
      IsChannel q ∧ IsFunOf P q g f ∧ sideRate 1 P q = funLosslessRate P g := by
  classical
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hβ : Nonempty β := ⟨g z⟩
  have hD : minDistortion P (funHamming g) ≤ 0 := by
    refine (sum_eq_zero fun z _ => ?_).le
    have : ⨅ b, funHamming g z b = 0 := by
      refine le_antisymm ((ciInf_le_distortion _ z (g z)).trans_eq (by simp [funHamming,
        hammingDistortion])) (le_ciInf fun b => ?_)
      simp only [funHamming, hammingDistortion]
      split_ifs <;> norm_num
    rw [this, mul_zero]
  obtain ⟨q, f, hq, hc, hr⟩ := exists_funRD_eq (e := funHamming g) hP hD
  exact ⟨q, f, hq, (sideCost_funHamming_le_zero_iff hP hq g f).1 hc, by
    rw [hr, funLosslessRate_eq_funRD hP]⟩

/-- **Lecture 22 of [elgamal2010], pages 22-5 and 22-6.** The optimal rate for computing `Z`
losslessly is `R*_g = min I(X; U | Y)` over `p(u | x)` with `H(Z | U, Y) = 0`, in bits. -/
theorem losslessFunBits_eq [Finite β] (hP : IsPMF P) (g : α × γ → β) :
    sInf {R | IsLosslessFunBits P g R} = funLosslessRate P g / log 2 := by
  have hl := log_pos one_lt_two
  obtain ⟨q, f, hq, hf, hr⟩ := exists_funLosslessRate_eq hP g
  have hach : ∀ R, funLosslessRate P g / log 2 < R → IsLosslessFunBits P g R := fun R hR =>
    isLosslessFunBits_of_lt hP hq hf (by rwa [hr])
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, hach _ (lt_add_one _)⟩ (fun R hR => ?_)
    fun w hw => ⟨(funLosslessRate P g / log 2 + w) / 2, hach _ (by linarith), by linarith⟩
  obtain ⟨q', f', hq', hc', hr'⟩ := (hR.isAchievable hP).exists_kernel hP
  rw [div_le_iff₀ hl]
  exact (funLosslessRate_le hP hq' ((sideCost_funHamming_le_zero_iff hP hq' g f').1 hc')).trans hr'

/-- A lossless rate is at least `R*_g`. -/
theorem IsLosslessFunBits.le [Finite β] (hP : IsPMF P) {g : α × γ → β} {R : ℝ}
    (hR : IsLosslessFunBits P g R) : funLosslessRate P g ≤ R * log 2 := by
  obtain ⟨q', f', hq', hc', hr'⟩ := (hR.isAchievable hP).exists_kernel hP
  exact (funLosslessRate_le hP hq' ((sideCost_funHamming_le_zero_iff hP hq' g f').1 hc')).trans hr'

/-- `I(X; U | Y) ≥ H(Z | Y)` if `H(Z | U, Y) = 0`, since `Z` is a function of `(X, Y)`. -/
lemma condEntropy_le_sideRate [Fintype β] (hP : IsPMF P) (hq : IsChannel q) {g : α × γ → β}
    {f : υ → γ → β} (hf : IsFunOf P q g f) :
    H[fun z : α × γ => g z | Prod.snd ; P] ≤ sideRate 1 P q := by
  classical
  have hμ := siLaw_isPMF hP hq
  set Z : (α × γ) × υ → β := fun w => g w.1 with hZ
  set Y : (α × γ) × υ → γ := fun w => w.1.2 with hY
  set X : (α × γ) × υ → α := fun w => w.1.1 with hX
  have e1 : H[fun z : α × γ => g z | Prod.snd ; P] = H[Z | Y ; siLaw P q] := by
    refine condEntropy_eq_of_dist_pair_eq hP hμ ?_
    rw [show pair Y Z = (pair Prod.snd (fun z : α × γ => g z)) ∘ Prod.fst from rfl, dist_comp_eq,
      dist_siLaw_fst hq]
  have h0 : H[Z | pair Prod.snd Y ; siLaw P q] = 0 := by
    rw [condEntropy_eq_zero_iff hμ]
    refine ⟨fun w => f w.1 w.2, fun w hw => ?_⟩
    exact (hf w hw).symm
  have c1 := chain_rule_cond hμ Z Prod.snd Y
  have c2 := chain_rule_cond hμ Prod.snd Z Y
  have sw : H[pair Z Prod.snd | Y ; siLaw P q] = H[pair Prod.snd Z | Y ; siLaw P q] :=
    condEntropy_congr_left hμ Y Prod.swap Prod.swap_injective fun _ => rfl
  have h3 : H[Prod.snd | pair X Y ; siLaw P q] ≤ H[Prod.snd | pair Z Y ; siLaw P q] :=
    condEntropy_le_condEntropy_comp hμ Prod.snd (pair X Y) fun w : α × γ => (g w, w.2)
  rw [e1, sideRate_one hP hq, condMutualInfo_comm hμ, condMutualInfo]
  linarith

/-- **Lecture 22, page 22-5.** The lower bound `H(Z | Y) ≤ R*_g`, in nats. -/
theorem condEntropy_le_funLosslessRate [Fintype β] (hP : IsPMF P) (g : α × γ → β) :
    H[fun z : α × γ => g z | Prod.snd ; P] ≤ funLosslessRate P g := by
  obtain ⟨q, f, hq, hf, hr⟩ := exists_funLosslessRate_eq hP g
  rw [← hr]
  exact condEntropy_le_sideRate hP hq hf

/-- **Lecture 22, page 22-5.** The upper bound `R*_g ≤ H(X | Y)`, in nats. -/
theorem funLosslessRate_le_condEntropy [Finite β] (hP : IsPMF P) (g : α × γ → β) :
    funLosslessRate P g ≤ H[Prod.fst | Prod.snd ; P] := by
  classical
  have hid : IsChannel (identityKernel (α := α)) := identityKernel_isChannel
  have hf : ∀ z : (α × γ) × α, siLaw P identityKernel z ≠ 0 →
      (fun (u : α) (_ : γ) => u) z.2 z.1.2 = z.1.1 := fun z hz => by
    by_contra hne
    apply hz
    simp [siLaw, jointOf, identityKernel, hne]
  have hrate : sideRate 1 P (identityKernel (α := α)) = H[Prod.fst | Prod.snd ; P] :=
    sideRate_one_eq_of_support hP hid
      ((condEntropy_XUY_eq_zero_iff hP hid).2 ⟨fun u _ => u, hf⟩)
  rw [← hrate]
  exact funLosslessRate_le hP hid (isFunOf_identityKernel P g)

end Lossless

end InfoTheory
