/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayLossyInner

/-!
# Two-way coding for lossless computing

This file proves Theorem 5 of Lecture 22 of [elgamal2010]: the `q`-round rate region for computing
functions of two sources losslessly at both nodes. Theorem 4, the lossy version, is Kaspi's theorem
of Lecture 21 with distortions that depend on both sources.

## Main definitions

* `KaspiCode.errProb₁`, `KaspiCode.errProb₂`: the probabilities of a block error at the two nodes.
* `IsLosslessKaspi`, `kaspiLosslessRegion`: lossless computing.

## Main statements

* `isLosslessKaspi_of_lt`: **Theorem 5, achievability**.
* `IsLosslessKaspi.isAchievableKaspi`, `exists_law_of_mem_kaspiLosslessRegion`: **the converse**,
  with arbitrarily small Hamming distortions, since the library has no cardinality bound for `U^q`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

variable {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ : Type*}
  {υ : Type*} [Fintype υ] [Nonempty υ] {q n : ℕ} {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ}
  {μ : α₁ × α₂ × (Fin q → υ) → ℝ} {ε₂ εd : Fin q → ℝ} {L M : Fin q → ℕ} [∀ l, NeZero (L l)]
  [∀ l, NeZero (M l)]

open Classical in
/-- The probability of a block error of the estimate of `g₁(X₁, X₂)` at node 2. -/
def KaspiCode.errProb₁ (c : KaspiCode spk M n α₁ α₂ β₁ β₂) (P : α₁ × α₂ → ℝ) (g₁ : α₁ × α₂ → β₁) :
    ℝ :=
  ∑ ω : Fin n → α₁ × α₂, if c.dec₁ (fun i => (ω i).2)
    (c.trans (fun i => (ω i).1) fun i => (ω i).2) ≠ (fun i => g₁ (ω i)) then iidPMF P n ω else 0

open Classical in
/-- The probability of a block error of the estimate of `g₂(X₁, X₂)` at node 1. -/
def KaspiCode.errProb₂ (c : KaspiCode spk M n α₁ α₂ β₁ β₂) (P : α₁ × α₂ → ℝ) (g₂ : α₁ × α₂ → β₂) :
    ℝ :=
  ∑ ω : Fin n → α₁ × α₂, if c.dec₂ (fun i => (ω i).1)
    (c.trans (fun i => (ω i).1) fun i => (ω i).2) ≠ (fun i => g₂ (ω i)) then iidPMF P n ω else 0

/-- **Lecture 22 of [elgamal2010], page 22-21.** A rate pair, in bits, is achievable with `q` rounds
for computing `g₁(X₁, X₂)` at node 2 and `g₂(X₁, X₂)` at node 1 losslessly. -/
def IsLosslessKaspi {q : ℕ} (P : α₁ × α₂ → ℝ) (spk : Fin q → Bool) (g₁ : α₁ × α₂ → β₁)
    (g₂ : α₁ × α₂ → β₂) (R : ℝ × ℝ) : Prop :=
  0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (M : Fin q → ℕ) (_ : ∀ l, NeZero (M l))
    (c : KaspiCode spk M n α₁ α₂ β₁ β₂),
    ∏ l with spk l = true, M l ≤ 2 ^ ⌊n * R.1⌋₊ ∧ ∏ l with spk l = false, M l ≤ 2 ^ ⌊n * R.2⌋₊ ∧
      c.errProb₁ P g₁ ≤ ε ∧ c.errProb₂ P g₂ ≤ ε

/-- **Lecture 22 of [elgamal2010], page 22-21.** The optimal `q`-round rate region. -/
def kaspiLosslessRegion {q : ℕ} (P : α₁ × α₂ → ℝ) (spk : Fin q → Bool) (g₁ : α₁ × α₂ → β₁)
    (g₂ : α₁ × α₂ → β₂) : Set (ℝ × ℝ) :=
  closure {R | IsLosslessKaspi P spk g₁ g₂ R}

/-! ### Achievability -/

/-- A letter of a robustly typical sequence has positive probability. -/
lemma ne_zero_of_mem_robustTypicalSet {a : Type*} [Fintype a] {p : a → ℝ} {m : ℕ} {ε : ℝ}
    {x : Fin m → a} (hx : x ∈ robustTypicalSet p m ε) (i : Fin m) : p (x i) ≠ 0 := by
  classical
  intro h0
  have h := mem_robustTypicalSet.1 hx (x i)
  rw [h0, mul_zero, sub_zero, abs_nonpos_iff] at h
  have hm : (0 : ℝ) < m := by exact_mod_cast i.pos
  have hc : (0 : ℝ) < symbolCount x (x i) := by
    have : 0 < symbolCount x (x i) := by
      rw [symbolCount]
      exact card_pos.2 ⟨i, by simp⟩
    exact_mod_cast this
  rw [typeOf] at h
  exact absurd h (div_pos hc hm).ne'

omit [Fintype α₁] [Fintype α₂] in
/-- The law at the last round has the letters of `μ`. -/
lemma exists_of_dist_kState_ne_zero [Fintype α₁] [Fintype α₂] {w : (α₁ × α₂) × (Fin q → υ)}
    (h : dist μ (kState q) w ≠ 0) : ∃ z, μ z ≠ 0 ∧ z.1 = w.1.1 ∧ z.2.1 = w.1.2 ∧ z.2.2 = w.2 := by
  classical
  obtain ⟨z, -, hz⟩ := exists_ne_zero_of_sum_ne_zero h
  by_cases e : kState q z = w
  · rw [ite_eq_left e] at hz
    subst e
    exact ⟨z, hz, rfl, rfl, by simp only [kState, truncU_top]⟩
  · rw [ite_eq_right e] at hz
    exact absurd rfl hz

open Classical in
/-- **Lecture 22, page 22-21.** The estimate of `g₁(X₁, X₂)` at node 2 is correct if all the rounds
are good and `g₁` is determined by `(U^q, X₂)`. -/
theorem KBook.errProb₁_le (B : KBook L M n υ) (hP : IsPMF P) {g₁ : α₁ × α₂ → β₁}
    {f₁ : (Fin q → υ) → α₂ → β₁} (f₂ : (Fin q → υ) → α₁ → β₂)
    (hf₁ : ∀ z, μ z ≠ 0 → f₁ z.2.2 z.2.1 = g₁ (z.1, z.2.1)) (ε : ℝ) :
    ((B.proto spk μ ε₂ εd).code f₁ f₂).errProb₁ P g₁ ≤
      ∑ ω, iidPMF P n ω * (if B.Good spk μ ε₂ εd q ε ω then 0 else 1) := by
  refine sum_le_sum fun ω _ => ?_
  have h0 := iidPMF_nonneg hP.nonneg ω
  by_cases hg : B.Good spk μ ε₂ εd q ε ω
  · obtain ⟨h₁, h₂⟩ := (B.proto spk μ ε₂ εd).view_code (f₁ := f₁) (f₂ := f₂)
      (x₁ := fstSeq ω) (x₂ := sndSeq ω) fun l => hg.2 l l.2
    have hdec : ((B.proto spk μ ε₂ εd).code f₁ f₂).dec₁ (fun i => (ω i).2)
        (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2) =
        fun i => g₁ (ω i) := by
      funext i
      change f₁ ((B.proto spk μ ε₂ εd).view₂ (sndSeq ω)
        (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fstSeq ω) (sndSeq ω)) q i) (ω i).2 = _
      rw [h₂]
      obtain ⟨z, hz, e₁, e₂, e₃⟩ := exists_of_dist_kState_ne_zero
        (ne_zero_of_mem_robustTypicalSet hg.1 i)
      have := hf₁ z hz
      rw [e₁, e₂, e₃] at this
      exact this
    simp [hdec, hg]
  · simp only [hg, ite_false, mul_one]
    split_ifs
    · exact le_rfl
    · exact h0

open Classical in
/-- The same at node 1. -/
theorem KBook.errProb₂_le (B : KBook L M n υ) (hP : IsPMF P) {g₂ : α₁ × α₂ → β₂}
    (f₁ : (Fin q → υ) → α₂ → β₁) {f₂ : (Fin q → υ) → α₁ → β₂}
    (hf₂ : ∀ z, μ z ≠ 0 → f₂ z.2.2 z.1 = g₂ (z.1, z.2.1)) (ε : ℝ) :
    ((B.proto spk μ ε₂ εd).code f₁ f₂).errProb₂ P g₂ ≤
      ∑ ω, iidPMF P n ω * (if B.Good spk μ ε₂ εd q ε ω then 0 else 1) := by
  refine sum_le_sum fun ω _ => ?_
  have h0 := iidPMF_nonneg hP.nonneg ω
  by_cases hg : B.Good spk μ ε₂ εd q ε ω
  · obtain ⟨h₁, h₂⟩ := (B.proto spk μ ε₂ εd).view_code (f₁ := f₁) (f₂ := f₂)
      (x₁ := fstSeq ω) (x₂ := sndSeq ω) fun l => hg.2 l l.2
    have hdec : ((B.proto spk μ ε₂ εd).code f₁ f₂).dec₂ (fun i => (ω i).1)
        (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2) =
        fun i => g₂ (ω i) := by
      funext i
      change f₂ ((B.proto spk μ ε₂ εd).view₁ (fstSeq ω)
        (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fstSeq ω) (sndSeq ω)) q i) (ω i).1 = _
      rw [h₁]
      obtain ⟨z, hz, e₁, e₂, e₃⟩ := exists_of_dist_kState_ne_zero
        (ne_zero_of_mem_robustTypicalSet hg.1 i)
      have := hf₂ z hz
      rw [e₁, e₂, e₃] at this
      exact this
    simp [hdec, hg]
  · simp only [hg, ite_false, mul_one]
    split_ifs
    · exact le_rfl
    · exact h0

/-- **Theorem 5 of Lecture 22 of [elgamal2010], page 22-21: achievability.** For a law of the rounds
with `H(g₁ | U^q, X₂) = 0` and `H(g₂ | U^q, X₁) = 0`, a rate pair strictly above the bounds is
achievable. -/
theorem isLosslessKaspi_of_lt (hP : IsPMF P) (hμ : IsKaspiLaw P spk μ) {g₁ : α₁ × α₂ → β₁}
    {g₂ : α₁ × α₂ → β₂} {f₁ : (Fin q → υ) → α₂ → β₁} {f₂ : (Fin q → υ) → α₁ → β₂}
    (hf₁ : ∀ z, μ z ≠ 0 → f₁ z.2.2 z.2.1 = g₁ (z.1, z.2.1))
    (hf₂ : ∀ z, μ z ≠ 0 → f₂ z.2.2 z.1 = g₂ (z.1, z.2.1)) {R : ℝ × ℝ}
    (hR₁ : I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 | fun z => z.2.1 ; μ] <
      R.1 * log 2)
    (hR₂ : I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 | fun z => z.1 ; μ] <
      R.2 * log 2) : IsLosslessKaspi P spk g₁ g₂ R := by
  classical
  have hp := hμ.isPMF
  have hl2 := log_pos one_lt_two
  obtain ⟨I₁, hI₁⟩ : ∃ I₁, I₁ = I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 |
    fun z => z.2.1 ; μ] := ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ I₂, I₂ = I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 |
    fun z => z.1 ; μ] := ⟨_, rfl⟩
  rw [← hI₁] at hR₁
  rw [← hI₂] at hR₂
  have hI₁0 : 0 ≤ I₁ := hI₁ ▸ condMutualInfo_nonneg hp _ _ _
  have hI₂0 : 0 ≤ I₂ := hI₂ ▸ condMutualInfo_nonneg hp _ _ _
  have hR₁0 : 0 ≤ R.1 := by
    by_contra h
    nlinarith [not_le.1 h]
  have hR₂0 : 0 ≤ R.2 := by
    by_contra h
    nlinarith [not_le.1 h]
  refine ⟨hR₁0, hR₂0, fun ε hε => ?_⟩
  obtain ⟨δ, hδ0, hδ₁, hδ₂⟩ : ∃ δ > 0, I₁ + (3 * (q : ℝ) + 2) * δ ≤ R.1 * log 2 ∧
      I₂ + (3 * (q : ℝ) + 2) * δ ≤ R.2 * log 2 := by
    have hQ0 : 0 < 3 * (q : ℝ) + 2 := by positivity
    refine ⟨min (R.1 * log 2 - I₁) (R.2 * log 2 - I₂) / (3 * (q : ℝ) + 2),
      div_pos (lt_min (by linarith) (by linarith)) hQ0, ?_, ?_⟩
    · have := min_le_left (R.1 * log 2 - I₁) (R.2 * log 2 - I₂)
      rw [mul_div_cancel₀ _ hQ0.ne']
      linarith
    · have := min_le_right (R.1 * log 2 - I₁) (R.2 * log 2 - I₂)
      rw [mul_div_cancel₀ _ hQ0.ne']
      linarith
  obtain ⟨c, hc⟩ : ∃ c, c = log (Fintype.card υ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ log_natCast_nonneg _
  obtain ⟨εt, hεt⟩ : ∃ εt, εt = min 1 (δ / (2 * c + 1)) := ⟨_, rfl⟩
  have hεt0 : 0 < εt := by
    rw [hεt]
    exact lt_min one_pos (by positivity)
  have hεt1 : εt ≤ 1 := by
    rw [hεt]
    exact min_le_left _ _
  have hεtc : εt * (2 * log (Fintype.card υ)) ≤ δ := by
    have h₁ : εt ≤ δ / (2 * c + 1) := by
      rw [hεt]
      exact min_le_right _ _
    rw [← hc]
    calc εt * (2 * c) ≤ δ / (2 * c + 1) * (2 * c) := mul_le_mul_of_nonneg_right h₁ (by positivity)
      _ ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  obtain ⟨εs, ε₂, hεs0, hεsq, hround⟩ := exists_kaspi_params (spk := spk) hμ hδ0 hεt0 hεt1 hεtc
  obtain ⟨η, hη⟩ : ∃ η, η = ε / ((q : ℝ) + 1) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    positivity
  have hgood : ((q : ℝ) + 1) * η = ε := by
    rw [hη]
    field_simp
  have htyp := tendsto_prob_robustTypicalSet hP (hεs0 0)
  have ht : Tendsto (fun n => 1 - prob (iidPMF P n) (robustTypicalSet P n (εs 0))) atTop (𝓝 0) := by
    simpa using htyp.const_sub 1
  have hsize : ∀ᶠ n : ℕ in atTop, ((q : ℝ) + 1) * log 2 ≤ n * δ :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hδ0).eventually_ge_atTop _
  filter_upwards [eventually_all.2 fun l => hround l η hη0, (tendsto_order.1 ht).2 η hη0, hsize]
    with n hrn hst hns
  have hw := iidPMF_isPMF hP n
  have h₀ : ∑ ω, iidPMF P n ω * (if ω ∈ robustTypicalSet P n (εs 0) then (0 : ℝ) else 1) ≤ η := by
    refine le_trans (le_of_eq ?_) hst.le
    have h2 : prob (iidPMF P n) (robustTypicalSet P n (εs 0)) =
        ∑ x, if x ∈ robustTypicalSet P n (εs 0) then iidPMF P n x else 0 := by
      rw [sum_ite_mem, univ_inter]
      rfl
    rw [h2]
    calc ∑ x, iidPMF P n x * (if x ∈ robustTypicalSet P n (εs 0) then (0 : ℝ) else 1)
        = ∑ x, (iidPMF P n x - if x ∈ robustTypicalSet P n (εs 0) then iidPMF P n x else 0) :=
          sum_congr rfl fun x _ => by split_ifs <;> simp
      _ = _ := by rw [sum_sub_distrib, hw.sum_eq_one]
  have hLne : ∀ l : Fin q, NeZero ⌈exp ((n : ℝ) * (kInfoS μ spk l + δ))⌉₊ := fun l =>
    ⟨(Nat.ceil_pos.2 (exp_pos _)).ne'⟩
  have hMne : ∀ l : Fin q, NeZero ⌈exp ((n : ℝ) * (kInfoS μ spk l - kInfoO μ spk l + 3 * δ))⌉₊ :=
    fun l => ⟨(Nat.ceil_pos.2 (exp_pos _)).ne'⟩
  obtain ⟨B, hB⟩ := exists_book (spk := spk) (μ := μ) (ε₂ := ε₂) (εd := fun l => εs (l + 1))
    (rc := fun l => kInfoS μ spk l + δ) (rm := fun l => kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
    (εs := εs) (M := fun l => ⌈exp ((n : ℝ) * (kInfoS μ spk l - kInfoO μ spk l + 3 * δ))⌉₊)
    hμ hP hη0.le (fun _ => rfl) (fun l => Nat.le_ceil _) hLne (fun l hs => (hrn l).1 hs)
    (fun l hs => (hrn l).2 hs) h₀
  rw [hεsq, hgood] at hB
  have hsub := kInfo_sub_nonneg hμ
  refine ⟨_, hMne, (B.proto spk μ ε₂ fun l => εs (l + 1)).code f₁ f₂, ?_, ?_, ?_, ?_⟩
  · exact prod_size_le _ hsub hδ0 (hI₁.trans (kaspi_sum_rate₁ hμ)) hδ₁ hns
  · exact prod_size_le _ hsub hδ0 (hI₂.trans (kaspi_sum_rate₂ hμ)) hδ₂ hns
  · refine (B.errProb₁_le hP f₂ hf₁ εt).trans ?_
    convert hB
  · refine (B.errProb₂_le hP f₁ hf₂ εt).trans ?_
    convert hB

/-! ### The converse -/

open Classical in
/-- A lossless code has a small Hamming distortion. -/
theorem IsLosslessKaspi.isAchievableKaspi {g₁ : α₁ × α₂ → β₁} {g₂ : α₁ × α₂ → β₂} {R : ℝ × ℝ}
    (hP : IsPMF P) (h : IsLosslessKaspi P spk g₁ g₂ R) :
    IsAchievableKaspi P spk (fun z b => hammingDistortion (g₁ z) b)
      (fun z b => hammingDistortion (g₂ z) b) 0 0 R := by
  obtain ⟨h₁, h₂, h⟩ := h
  refine ⟨h₁, h₂, fun ε hε => ?_⟩
  filter_upwards [h ε hε] with n ⟨M, hM, c, hs₁, hs₂, he₁, he₂⟩
  refine ⟨M, hM, c, hs₁, hs₂, ?_, ?_⟩
  · rw [zero_add]
    refine le_trans (sum_le_sum fun ω _ => ?_) he₁
    have h0 := iidPMF_nonneg hP.nonneg ω
    have := seqDistortion_hamming_le (x := fun i => g₁ (ω i))
      (y := c.dec₁ (fun i => (ω i).2) (c.trans (fun i => (ω i).1) fun i => (ω i).2))
    split_ifs at this ⊢ with h1
    · exact mul_le_of_le_one_right h0 this
    · exact mul_nonpos_of_nonneg_of_nonpos h0 this
  · rw [zero_add]
    refine le_trans (sum_le_sum fun ω _ => ?_) he₂
    have h0 := iidPMF_nonneg hP.nonneg ω
    have := seqDistortion_hamming_le (x := fun i => g₂ (ω i))
      (y := c.dec₂ (fun i => (ω i).1) (c.trans (fun i => (ω i).1) fun i => (ω i).2))
    split_ifs at this ⊢ with h1
    · exact mul_le_of_le_one_right h0 this
    · exact mul_nonpos_of_nonneg_of_nonpos h0 this

/-- **Theorem 5 of Lecture 22 of [elgamal2010], page 22-21: the converse.** For every rate pair of
the region and every `ε > 0`, there is a law of the rounds with rates at most `R + ε` for which `g₁`
and `g₂` are estimated from `(U^q, X₂)` and `(U^q, X₁)` with Hamming distortion at most `ε`. The
notes have `ε = 0`, which needs a bound on the cardinalities of the `Uₗ`. -/
theorem exists_law_of_mem_kaspiLosslessRegion [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂]
    (hq : 0 < q) (hP : IsPMF P) {g₁ : α₁ × α₂ → β₁} {g₂ : α₁ × α₂ → β₂} {R : ℝ × ℝ}
    (h : R ∈ kaspiLosslessRegion P spk g₁ g₂) {ε : ℝ} (hε : 0 < ε) :
    open Classical in
    (R.1 + ε, R.2 + ε) ∈ kaspiInner P spk (fun z b => hammingDistortion (g₁ z) b)
      (fun z b => hammingDistortion (g₂ z) b) (0 + ε) (0 + ε) := by
  classical
  refine exists_kaspiInner_of_mem_kaspiRegion hq hP ?_ hε
  exact closure_mono (fun R hR => IsLosslessKaspi.isAchievableKaspi hP hR) h

end InfoTheory
