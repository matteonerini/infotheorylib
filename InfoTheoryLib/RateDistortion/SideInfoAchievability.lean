/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.SideInfoCovering

/-!
# Source coding with side information at the decoder: achievability

This file defines the codes of Lecture 12 for side information available causally and noncausally at
the decoder, and proves the achievability of Theorems 1 and 2 and of the Wyner–Ziv theorem, from the
codes for typical triples of `RateDistortion.SideInfoCovering`.

## Main definitions

* `CausalCode M n α γ β`, `WZCode M n α γ β`: the codes, with their `output`, `distortion` and
  `errProb`.
* `IsAchievableCausalBits`, `IsAchievableWZBits`: achievable rates and distortions, in bits.
* `rateCausalBits`, `rateWZBits`: the rate–distortion functions, in bits.
* `IsLosslessCausalBits`, `IsLosslessWZBits`: rates for lossless source coding, in bits.

## Main statements

* `isAchievableCausalBits_of_lt`, `isAchievableWZBits_of_lt`: **the achievability of Theorem 1 and
  of the Wyner–Ziv theorem**.
* `isLosslessCausalBits_of_lt`, `isLosslessWZBits_of_lt`: **the achievability of Theorem 2**, and
  the fact that the Slepian–Wolf rate is a special case of the Wyner–Ziv theorem.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 12
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α γ β υ : Type*} [Fintype α] [Fintype γ] [Fintype υ]

/-! ### The codes -/

/-- The prefix `yⁱ` of a sequence, with the coordinates up to `i` included. -/
def prefixSeq {n : ℕ} (y : Fin n → γ) (i : Fin n) : Fin (i + 1) → γ :=
  fun j => y (Fin.castLE (Nat.succ_le_of_lt i.2) j)

/-- **Lecture 12 of [elgamal2010], page 12-5.** A rate–distortion code with side information
available causally at the decoder: an encoder `m(xⁿ)` and a decoder `x̂ᵢ(m, yⁱ)`. -/
structure CausalCode (M n : ℕ) (α γ β : Type*) where
  /-- The encoder. -/
  enc : (Fin n → α) → Fin M
  /-- The decoder at the time `i`. -/
  dec : Fin M → ∀ i : Fin n, (Fin (i + 1) → γ) → β

/-- The reconstruction `x̂ᵢ(m, yⁱ)`. -/
def CausalCode.output {M n : ℕ} (c : CausalCode M n α γ β) (m : Fin M) (y : Fin n → γ) :
    Fin n → β := fun i => c.dec m i (prefixSeq y i)

/-- The expected distortion `E d(Xⁿ, X̂ⁿ)` of a code. -/
def CausalCode.distortion {M n : ℕ} (c : CausalCode M n α γ β) (P : α × γ → ℝ)
    (d : α → β → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * seqDistortion d (fstSeq ω) (c.output (c.enc (fstSeq ω)) (sndSeq ω))

open Classical in
/-- The probability of error `P{X̂ⁿ ≠ Xⁿ}` of a code. -/
def CausalCode.errProb {M n : ℕ} (c : CausalCode M n α γ α) (P : α × γ → ℝ) : ℝ :=
  ∑ ω, if c.output (c.enc (fstSeq ω)) (sndSeq ω) ≠ fstSeq ω then iidPMF P n ω else 0

/-- **Lecture 12 of [elgamal2010], page 12-16.** A rate–distortion code with side information
available noncausally at the decoder: an encoder `m(xⁿ)` and a decoder `x̂ⁿ(m, yⁿ)`. -/
structure WZCode (M n : ℕ) (α γ β : Type*) where
  /-- The encoder. -/
  enc : (Fin n → α) → Fin M
  /-- The decoder. -/
  dec : Fin M → (Fin n → γ) → Fin n → β

/-- The expected distortion `E d(Xⁿ, X̂ⁿ)` of a code. -/
def WZCode.distortion {M n : ℕ} (c : WZCode M n α γ β) (P : α × γ → ℝ) (d : α → β → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * seqDistortion d (fstSeq ω) (c.dec (c.enc (fstSeq ω)) (sndSeq ω))

open Classical in
/-- The probability of error `P{X̂ⁿ ≠ Xⁿ}` of a code. -/
def WZCode.errProb {M n : ℕ} (c : WZCode M n α γ α) (P : α × γ → ℝ) : ℝ :=
  ∑ ω, if c.dec (c.enc (fstSeq ω)) (sndSeq ω) ≠ fstSeq ω then iidPMF P n ω else 0

/-- **Lecture 12 of [elgamal2010], page 12-5.** A pair `(R, D)`, with `R` in bits, is achievable
with causal side information if there are `(2^{nR}, n)` codes with `limsup E d(Xⁿ, X̂ⁿ) ≤ D`. -/
def IsAchievableCausalBits (P : α × γ → ℝ) (d : α → β → ℝ) (R D : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, CausalCode (2 ^ ⌊n * R⌋₊) n α γ β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion P d ≤ D + ε

/-- **Lecture 12 of [elgamal2010], page 12-5.** The rate–distortion function `R_CSI-D(D)`, in bits.
-/
def rateCausalBits (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | IsAchievableCausalBits P d R D}

/-- **Lecture 12 of [elgamal2010], page 12-16.** A pair `(R, D)`, with `R` in bits, is achievable
with noncausal side information if there are `(2^{nR}, n)` codes with `limsup E d(Xⁿ, X̂ⁿ) ≤ D`. -/
def IsAchievableWZBits (P : α × γ → ℝ) (d : α → β → ℝ) (R D : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, WZCode (2 ^ ⌊n * R⌋₊) n α γ β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion P d ≤ D + ε

/-- **Lecture 12 of [elgamal2010], page 12-17.** The rate–distortion function `R_SI-D(D)`, in bits.
-/
def rateWZBits (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | IsAchievableWZBits P d R D}

/-- **Lecture 12 of [elgamal2010], page 12-13.** A rate `R`, in bits, is achievable for lossless
source coding with causal side information if there are `(2^{nR}, n)` codes with
`P{X̂ⁿ ≠ Xⁿ} → 0`. -/
def IsLosslessCausalBits (P : α × γ → ℝ) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, CausalCode (2 ^ ⌊n * R⌋₊) n α γ α,
    Tendsto (fun n => (c n).errProb P) atTop (𝓝 0)

/-- A rate `R`, in bits, is achievable for lossless source coding with noncausal side information if
there are `(2^{nR}, n)` codes with `P{X̂ⁿ ≠ Xⁿ} → 0`. -/
def IsLosslessWZBits (P : α × γ → ℝ) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, WZCode (2 ^ ⌊n * R⌋₊) n α γ α,
    Tendsto (fun n => (c n).errProb P) atTop (𝓝 0)

/-- To get a sequence of codes it is enough to find, for every `ε > 0` and all large `n`, a code
with cost at most `a + ε`: the codes of least cost then form a sequence. -/
lemma exists_seq_of_eventually {C : ℕ → Type*} [∀ n, Finite (C n)] [∀ n, Nonempty (C n)]
    (g : ∀ n, C n → ℝ) {a : ℝ} (h : ∀ ε > 0, ∀ᶠ n in atTop, ∃ c, g n c ≤ a + ε) :
    ∃ c : ∀ n, C n, ∀ ε > 0, ∀ᶠ n in atTop, g n (c n) ≤ a + ε := by
  choose c hc using fun n => Finite.exists_min (g n)
  exact ⟨c, fun ε hε => (h ε hε).mono fun n ⟨c', hc'⟩ => (hc n c').trans hc'⟩

/-! ### The distortion on typical triples -/

section Distortion

variable {P : α × γ → ℝ} {q : α → υ → ℝ} {d : α → β → ℝ} {f : υ → γ → β}

/-- The cost of a triple. -/
def sideLetter (d : α → β → ℝ) (f : υ → γ → β) (z : (α × γ) × υ) : ℝ := d z.1.1 (f z.2 z.1.2)

omit [Fintype α] [Fintype γ] in
lemma expect_siLaw (P : α × γ → ℝ) (q : α → υ → ℝ) (d : α → β → ℝ) (f : υ → γ → β) [Fintype α]
    [Fintype γ] :
    expect (siLaw P q) (sideLetter d f) = sideCost P q fun u x y => d x (f u y) := by
  simp only [expect, sideCost, sideLetter, mul_comm]

/-- The triples whose average cost is typical. -/
def costTypical (P : α × γ → ℝ) (q : α → υ → ℝ) (d : α → β → ℝ) (f : υ → γ → β) (ε : ℝ) (n : ℕ) :
    Finset (Fin n → (α × γ) × υ) :=
  open Classical in univ.filter fun t =>
    |(sampleMean fun i => sideLetter d f (t i)) - expect (siLaw P q) (sideLetter d f)| < ε

/-- By the weak law of large numbers, i.i.d. triples have a typical average cost. -/
lemma tendsto_prob_costTypical (hP : IsPMF P) (hq : IsChannel q) (d : α → β → ℝ) (f : υ → γ → β)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF (siLaw P q) n) (costTypical P q d f ε n)) atTop (𝓝 1) := by
  classical
  have hl := weak_law (siLaw_isPMF hP hq) (sideLetter d f) ε hε
  have e : ∀ n, prob (iidPMF (siLaw P q) n) (costTypical P q d f ε n) =
      1 - prob (iidPMF (siLaw P q) n) (univ.filter fun t =>
        ε ≤ |(sampleMean fun i => sideLetter d f (t i)) - expect (siLaw P q) (sideLetter d f)|) :=
    fun n => by
      have h := sum_filter_add_sum_filter_not univ (fun t : Fin n → (α × γ) × υ =>
        |(sampleMean fun i => sideLetter d f (t i)) - expect (siLaw P q) (sideLetter d f)| < ε)
        (iidPMF (siLaw P q) n)
      rw [(iidPMF_isPMF (siLaw_isPMF hP hq) n).sum_eq_one] at h
      simp only [not_lt] at h
      rw [eq_sub_iff_add_eq]
      convert h using 2 <;> rfl
  simp only [e]
  simpa using hl.const_sub 1

/-- **Lecture 12, page 12-10.** The distortion of a sequence is at most `E d(X, X̂) + ε` on the
typical triples, and at most `d_max` otherwise. -/
lemma seqDistortion_le_of_costTypical [Finite β] (hP : IsPMF P) (hq : IsChannel q)
    (hd : ∀ x y, 0 ≤ d x y) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) (ω : Fin n → α × γ)
    (u : Fin n → υ) :
    seqDistortion d (fstSeq ω) (fun i => f (u i) (ω i).2) ≤
      (sideCost P q fun u x y => d x (f u y)) + ε + maxDistortion d *
        (open Classical in if zipSeq ω u ∈ costTypical P q d f ε n then (0 : ℝ) else 1) := by
  classical
  have hE : 0 ≤ sideCost P q fun u x y => d x (f u y) :=
    sum_nonneg fun z _ => mul_nonneg ((siLaw_isPMF hP hq).nonneg z) (hd _ _)
  have hne : Nonempty β := ⟨f (u ⟨0, hn⟩) (ω ⟨0, hn⟩).2⟩
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α := ⟨z.1⟩
  have h0 := maxDistortion_nonneg hd
  by_cases ht : zipSeq ω u ∈ costTypical P q d f ε n
  · have h := (mem_filter.1 ht).2
    rw [expect_siLaw] at h
    simp only [ht, ite_true, mul_zero, add_zero]
    have e : seqDistortion d (fstSeq ω) (fun i => f (u i) (ω i).2) =
        sampleMean fun i => sideLetter d f (zipSeq ω u i) := by
      simp only [seqDistortion, sampleMean, Fintype.card_fin]
      rfl
    rw [e]
    linarith [(abs_lt.1 h).2]
  · simp only [ht, ite_false, mul_one]
    have := seqDistortion_le_maxDistortion d hn (fstSeq ω) fun i => f (u i) (ω i).2
    linarith

end Distortion

/-! ### Theorems 1 and 2 and the Wyner–Ziv theorem, achievability -/

section Achievability

variable {P : α × γ → ℝ} {q : α → υ → ℝ} {d : α → β → ℝ}

omit [Fintype α] [Fintype γ] [Fintype υ] in
instance CausalCode.finite [Finite α] [Finite γ] [Finite β] {M n : ℕ} :
    Finite (CausalCode M n α γ β) :=
  Finite.of_injective (fun c : CausalCode M n α γ β => (c.enc, c.dec)) fun c c' h => by
    cases c
    cases c'
    simpa using h

omit [Fintype α] [Fintype γ] [Fintype υ] in
instance WZCode.finite [Finite α] [Finite γ] [Finite β] {M n : ℕ} : Finite (WZCode M n α γ β) :=
  Finite.of_injective (fun c : WZCode M n α γ β => (c.enc, c.dec)) fun c c' h => by
    cases c
    cases c'
    simpa using h

omit [Fintype α] [Fintype γ] [Fintype υ] in
lemma CausalCode.nonempty [Nonempty β] {M n : ℕ} (hM : 0 < M) :
    Nonempty (CausalCode M n α γ β) :=
  ⟨⟨fun _ => ⟨0, hM⟩, fun _ _ _ => Classical.arbitrary β⟩⟩

omit [Fintype α] [Fintype γ] [Fintype υ] in
lemma WZCode.nonempty [Nonempty β] {M n : ℕ} (hM : 0 < M) : Nonempty (WZCode M n α γ β) :=
  ⟨⟨fun _ => ⟨0, hM⟩, fun _ _ _ => Classical.arbitrary β⟩⟩

/-- The code of a codebook of `U`: `x̂ᵢ(m, yⁱ) = x̂(uᵢ(m), yᵢ)`. -/
def causalCodeOf {M n : ℕ} (enc : (Fin n → α) → Fin M) (C : Fin M → Fin n → υ) (f : υ → γ → β) :
    CausalCode M n α γ β :=
  ⟨enc, fun m i s => f (C m i) (s (Fin.last _))⟩

omit [Fintype α] [Fintype γ] [Fintype υ] in
lemma output_causalCodeOf {M n : ℕ} (enc : (Fin n → α) → Fin M) (C : Fin M → Fin n → υ)
    (f : υ → γ → β) (m : Fin M) (y : Fin n → γ) (i : Fin n) :
    (causalCodeOf enc C f).output m y i = f (C m i) (y i) := by
  simp only [CausalCode.output, causalCodeOf, prefixSeq]
  congr 2

/-- **Theorem 1 of Lecture 12, achievability.** For `p(u | x)` and `x̂(u, y)` with `E d(X, X̂) ≤ D`,
every rate `R > I(X; U)` bits is achievable. -/
theorem isAchievableCausalBits_of_lt [Finite β] (hP : IsPMF P) (hd : ∀ x y, 0 ≤ d x y)
    (hq : IsChannel q) (f : υ → γ → β) {R D : ℝ}
    (hD : sideCost P q (fun u x y => d x (f u y)) ≤ D) (hR : sideRate 0 P q / log 2 < R) :
    IsAchievableCausalBits P d R D := by
  classical
  have hl := log_pos one_lt_two
  have hI : mutualInfoOf (margFst P) q < R * log 2 := by
    have := (div_lt_iff₀ hl).1 hR
    rwa [sideRate, zero_mul, sub_zero, ← mutualInfoOf_side] at this
  have hR0 : 0 ≤ R := by
    have h0 := sideRate_nonneg (θ := 0) hP hq zero_le_one
    exact (div_nonneg h0 hl.le).trans hR.le
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  obtain ⟨u₀, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF (hq z.1))
  have hβ : Nonempty β := ⟨f u₀ z.2⟩
  have hne := fun n : ℕ => CausalCode.nonempty (α := α) (γ := γ) (β := β) (n := n)
    (M := 2 ^ ⌊n * R⌋₊) (by positivity)
  obtain ⟨c, hc⟩ := exists_seq_of_eventually (C := fun n => CausalCode (2 ^ ⌊n * R⌋₊) n α γ β)
    (fun n c => c.distortion P d) (a := D) fun ε hε => by
      have hne' : Nonempty α := ⟨z.1⟩
      have hm := maxDistortion_nonneg hd
      have hδ : 0 < ε / 2 / (maxDistortion d + 1) := by positivity
      filter_upwards [eventually_causal_code hP hq hI (costTypical P q d f (ε / 2))
        (tendsto_prob_costTypical hP hq d f (half_pos hε)) hδ, eventually_gt_atTop 0]
        with n ⟨enc, C, hC⟩ hn
      refine ⟨causalCodeOf enc C f, ?_⟩
      have hle : (causalCodeOf enc C f).distortion P d ≤ ∑ ω, iidPMF P n ω *
          ((sideCost P q fun u x y => d x (f u y)) + ε / 2 + maxDistortion d *
            (if zipSeq ω (C (enc (fstSeq ω))) ∈
          costTypical P q d f (ε / 2) n then (0 : ℝ) else 1)) := by
        refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ ((iidPMF_isPMF hP n).nonneg ω)
        have := seqDistortion_le_of_costTypical (f := f) (q := q) hP hq hd (half_pos hε) hn ω
          (C (enc (fstSeq ω)))
        convert this using 2
        funext i
        rw [output_causalCodeOf]
        rfl
      refine hle.trans ?_
      have e : ∑ ω, iidPMF P n ω * ((sideCost P q fun u x y => d x (f u y)) + ε / 2 +
          maxDistortion d * (if zipSeq ω (C (enc (fstSeq ω))) ∈ costTypical P q d f (ε / 2) n then
            (0 : ℝ) else 1)) = (sideCost P q fun u x y => d x (f u y)) + ε / 2 +
          maxDistortion d * ∑ ω, iidPMF P n ω * (if zipSeq ω (C (enc (fstSeq ω))) ∈
            costTypical P q d f (ε / 2) n then (0 : ℝ) else 1) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, (iidPMF_isPMF hP n).sum_eq_one, one_mul]
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun ω _ => by ring
      rw [e]
      have hb : maxDistortion d * ∑ ω, iidPMF P n ω * (if zipSeq ω (C (enc (fstSeq ω))) ∈
          costTypical P q d f (ε / 2) n then (0 : ℝ) else 1) ≤ ε / 2 := by
        calc _ ≤ maxDistortion d * (ε / 2 / (maxDistortion d + 1)) :=
              mul_le_mul_of_nonneg_left hC hm
          _ ≤ (maxDistortion d + 1) * (ε / 2 / (maxDistortion d + 1)) := by
              gcongr
              linarith
          _ = ε / 2 := by field_simp
      linarith
  exact ⟨hR0, c, hc⟩

/-- **The Wyner–Ziv theorem, achievability.** For `p(u | x)` and `x̂(u, y)` with `E d(X, X̂) ≤ D`,
every rate `R > I(X; U) - I(Y; U)` bits is achievable. -/
theorem isAchievableWZBits_of_lt [Finite β] (hP : IsPMF P) (hd : ∀ x y, 0 ≤ d x y)
    (hq : IsChannel q) (f : υ → γ → β) {R D : ℝ}
    (hD : sideCost P q (fun u x y => d x (f u y)) ≤ D) (hR : sideRate 1 P q / log 2 < R) :
    IsAchievableWZBits P d R D := by
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
    (fun n c => c.distortion P d) (a := D) fun ε hε => by
      have hne' : Nonempty α := ⟨z.1⟩
      have hm := maxDistortion_nonneg hd
      have hδ : 0 < ε / 2 / (maxDistortion d + 1) := by positivity
      filter_upwards [eventually_wz_code hP hq hI (costTypical P q d f (ε / 2))
        (tendsto_prob_costTypical hP hq d f (half_pos hε)) hδ, eventually_gt_atTop 0]
        with n ⟨enc, dec, hC⟩ hn
      refine ⟨⟨enc, fun m y i => f (dec m y i) (y i)⟩, ?_⟩
      have hle : WZCode.distortion ⟨enc, fun m y i => f (dec m y i) (y i)⟩ P d ≤ ∑ ω, iidPMF P n ω *
          ((sideCost P q fun u x y => d x (f u y)) + ε / 2 + maxDistortion d *
            (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ costTypical P q d f (ε / 2) n then
              (0 : ℝ) else 1)) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
          (seqDistortion_le_of_costTypical (f := f) (q := q) hP hq hd (half_pos hε) hn ω
            (dec (enc (fstSeq ω)) (sndSeq ω))) ((iidPMF_isPMF hP n).nonneg ω)
      refine hle.trans ?_
      have e : ∑ ω, iidPMF P n ω * ((sideCost P q fun u x y => d x (f u y)) + ε / 2 +
          maxDistortion d * (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈
            costTypical P q d f (ε / 2) n then (0 : ℝ) else 1)) =
          (sideCost P q fun u x y => d x (f u y)) + ε / 2 +
          maxDistortion d * ∑ ω, iidPMF P n ω * (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈
            costTypical P q d f (ε / 2) n then (0 : ℝ) else 1) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, (iidPMF_isPMF hP n).sum_eq_one, one_mul]
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun ω _ => by ring
      rw [e]
      have hb : maxDistortion d * ∑ ω, iidPMF P n ω *
          (if zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈
            costTypical P q d f (ε / 2) n then (0 : ℝ) else 1) ≤ ε / 2 := by
        calc _ ≤ maxDistortion d * (ε / 2 / (maxDistortion d + 1)) :=
              mul_le_mul_of_nonneg_left hC hm
          _ ≤ (maxDistortion d + 1) * (ε / 2 / (maxDistortion d + 1)) := by
              gcongr
              linarith
          _ = ε / 2 := by field_simp
      linarith
  exact ⟨hR0, c, hc⟩

/-- The triples of positive probability in every coordinate. -/
def supportTriples (P : α × γ → ℝ) (q : α → υ → ℝ) (n : ℕ) : Finset (Fin n → (α × γ) × υ) :=
  open Classical in univ.filter fun t => ∀ i, siLaw P q (t i) ≠ 0

lemma prob_supportTriples (hP : IsPMF P) (hq : IsChannel q) (n : ℕ) :
    prob (iidPMF (siLaw P q) n) (supportTriples P q n) = 1 := by
  classical
  rw [prob, ← (iidPMF_isPMF (siLaw_isPMF hP hq) n).sum_eq_one]
  refine sum_subset (subset_univ _) fun t _ ht => ?_
  simp only [supportTriples, mem_filter, mem_univ, true_and, not_forall, not_not] at ht
  obtain ⟨i, hi⟩ := ht
  exact prod_eq_zero (mem_univ i) hi

/-- A tendency to `0` from the bounds `≤ ε` eventually. -/
lemma tendsto_zero_of_eventually_le {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, g n ≤ 0 + ε) : Tendsto g atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (h0 n),
    fun b hb => ?_⟩
  filter_upwards [h (b / 2) (half_pos hb)] with n hn
  linarith

open Classical in
/-- **Theorem 2 of Lecture 12, achievability.** If `x = x̂(u, y)` on the support of
`p(x, y) p(u | x)`, every rate `R > I(X; U)` bits is achievable for lossless source coding with
causal side information. -/
theorem isLosslessCausalBits_of_lt (hP : IsPMF P) (hq : IsChannel q) (f : υ → γ → α)
    (hf : ∀ z, siLaw P q z ≠ 0 → f z.2 z.1.2 = z.1.1) {R : ℝ}
    (hR : sideRate 0 P q / log 2 < R) : IsLosslessCausalBits P R := by
  have hl := log_pos one_lt_two
  have hI : mutualInfoOf (margFst P) q < R * log 2 := by
    have := (div_lt_iff₀ hl).1 hR
    rwa [sideRate, zero_mul, sub_zero, ← mutualInfoOf_side] at this
  have hR0 : 0 ≤ R := by
    have h0 := sideRate_nonneg (θ := 0) hP hq zero_le_one
    exact (div_nonneg h0 hl.le).trans hR.le
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hα : Nonempty α := ⟨z.1⟩
  have hne := fun n : ℕ => CausalCode.nonempty (α := α) (γ := γ) (β := α) (n := n)
    (M := 2 ^ ⌊n * R⌋₊) (by positivity)
  have hT : Tendsto (fun n => prob (iidPMF (siLaw P q) n) (supportTriples P q n)) atTop (𝓝 1) := by
    simp only [prob_supportTriples hP hq]
    exact tendsto_const_nhds
  obtain ⟨c, hc⟩ := exists_seq_of_eventually (C := fun n => CausalCode (2 ^ ⌊n * R⌋₊) n α γ α)
    (fun n c => c.errProb P) (a := 0) fun ε hε => by
      filter_upwards [eventually_causal_code hP hq hI (supportTriples P q) hT hε]
        with n ⟨enc, C, hC⟩
      refine ⟨causalCodeOf enc C f, ?_⟩
      rw [zero_add]
      refine le_trans (sum_le_sum fun ω _ => ?_) hC
      by_cases ht : zipSeq ω (C (enc (fstSeq ω))) ∈ supportTriples P q n
      · have hout : (causalCodeOf enc C f).output
            ((causalCodeOf enc C f).enc (fstSeq ω)) (sndSeq ω) = fstSeq ω := by
          funext i
          rw [output_causalCodeOf]
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

open Classical in
/-- **Lecture 12, page 12-25.** If `x = x̂(u, y)` on the support of `p(x, y) p(u | x)`, every rate
`R > I(X; U) - I(Y; U)` bits is achievable for lossless source coding with noncausal side
information. With `U = X`, this gives the corner point of the Slepian–Wolf theorem: the Slepian–Wolf
theorem is a special case of the Wyner–Ziv theorem, with deterministic instead of random binning of
the source.
-/
theorem isLosslessWZBits_of_lt (hP : IsPMF P) (hq : IsChannel q) (f : υ → γ → α)
    (hf : ∀ z, siLaw P q z ≠ 0 → f z.2 z.1.2 = z.1.1) {R : ℝ}
    (hR : sideRate 1 P q / log 2 < R) : IsLosslessWZBits P R := by
  have hl := log_pos one_lt_two
  have hI : sideRate 1 P q < R * log 2 := (div_lt_iff₀ hl).1 hR
  have hR0 : 0 ≤ R := by
    have h0 := sideRate_nonneg (θ := 1) hP hq le_rfl
    exact (div_nonneg h0 hl.le).trans hR.le
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hα : Nonempty α := ⟨z.1⟩
  have hne := fun n : ℕ => WZCode.nonempty (α := α) (γ := γ) (β := α) (n := n)
    (M := 2 ^ ⌊n * R⌋₊) (by positivity)
  have hT : Tendsto (fun n => prob (iidPMF (siLaw P q) n) (supportTriples P q n)) atTop (𝓝 1) := by
    simp only [prob_supportTriples hP hq]
    exact tendsto_const_nhds
  obtain ⟨c, hc⟩ := exists_seq_of_eventually (C := fun n => WZCode (2 ^ ⌊n * R⌋₊) n α γ α)
    (fun n c => c.errProb P) (a := 0) fun ε hε => by
      filter_upwards [eventually_wz_code hP hq hI (supportTriples P q) hT hε]
        with n ⟨enc, dec, hC⟩
      refine ⟨⟨enc, fun m y i => f (dec m y i) (y i)⟩, ?_⟩
      rw [zero_add]
      refine le_trans (sum_le_sum fun ω _ => ?_) hC
      by_cases ht : zipSeq ω (dec (enc (fstSeq ω)) (sndSeq ω)) ∈ supportTriples P q n
      · have hout : (fun i => f (dec (enc (fstSeq ω)) (sndSeq ω) i) (sndSeq ω i)) = fstSeq ω := by
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

end Achievability

end InfoTheory
