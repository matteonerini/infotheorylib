/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungInner

/-!
# Multiple description codes

This file defines the multiple description codes of Lecture 14 of El Gamal and Kim and proves two
general tools for layered coding schemes.

A source `Xⁿ` is described by two indices. Decoder 1 sees the first index, decoder 2 the second one
and decoder 0 sees both.

## Main definitions

* `MDCode M₁ M₂ n α β₀ β₁ β₂`: the codes.
* `IsAchievableMD`, `mdRegion`: the achievable rate pairs and the rate–distortion region
  `R(D₀, D₁, D₂)`, in bits.

## Main statements

* `exists_layer`: the choice of the codebooks of one layer of a superposition scheme.
* `MDCode.exists_of_index`: a code from encoders and decoders with arbitrary finite index sets.
* `isAchievableMD_of_eventually`: to show achievability it is enough to find, for every `ε > 0` and
  all large `n`, a code with distortions at most `Dⱼ + ε`.

## Implementation notes

The notes draw one large random codebook with a tree structure. We instead choose the layers one at
a time: given the codewords of the previous layers and the encoder so far, the codebooks of the next
layer attached to each previous index are chosen separately, by the averaging argument. In this way
each layer only involves independent codewords with a fixed law, and the error probabilities add.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 14
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₀ β₁ β₂ : Type*}

/-! ### The codes -/

/-- **Lecture 14 of [elgamal2010], page 14-2.** A multiple description code: two encoders, a decoder
of each index and a decoder of the pair of indices. -/
structure MDCode (M₁ M₂ n : ℕ) (α β₀ β₁ β₂ : Type*) where
  /-- The first encoder. -/
  enc₁ : (Fin n → α) → Fin M₁
  /-- The second encoder. -/
  enc₂ : (Fin n → α) → Fin M₂
  /-- The decoder of both indices. -/
  dec₀ : Fin M₁ × Fin M₂ → Fin n → β₀
  /-- The decoder of the first index. -/
  dec₁ : Fin M₁ → Fin n → β₁
  /-- The decoder of the second index. -/
  dec₂ : Fin M₂ → Fin n → β₂

section Code

variable [Fintype α] {M₁ M₂ n : ℕ}

/-- The expected distortion `E d₀(Xⁿ, X̂₀ⁿ)` of a code. -/
def MDCode.distortion₀ (c : MDCode M₁ M₂ n α β₀ β₁ β₂) (P : α → ℝ) (d₀ : α → β₀ → ℝ) : ℝ :=
  ∑ x, iidPMF P n x * seqDistortion d₀ x (c.dec₀ (c.enc₁ x, c.enc₂ x))

/-- The expected distortion `E d₁(Xⁿ, X̂₁ⁿ)` of a code. -/
def MDCode.distortion₁ (c : MDCode M₁ M₂ n α β₀ β₁ β₂) (P : α → ℝ) (d₁ : α → β₁ → ℝ) : ℝ :=
  ∑ x, iidPMF P n x * seqDistortion d₁ x (c.dec₁ (c.enc₁ x))

/-- The expected distortion `E d₂(Xⁿ, X̂₂ⁿ)` of a code. -/
def MDCode.distortion₂ (c : MDCode M₁ M₂ n α β₀ β₁ β₂) (P : α → ℝ) (d₂ : α → β₂ → ℝ) : ℝ :=
  ∑ x, iidPMF P n x * seqDistortion d₂ x (c.dec₂ (c.enc₂ x))

/-- **Lecture 14 of [elgamal2010], page 14-3.** A rate pair, in bits, is achievable with the
distortion triple `(D₀, D₁, D₂)` if there are `(2^{nR₁}, 2^{nR₂}, n)` codes with
`limsup E dⱼ(Xⁿ, X̂ⱼⁿ) ≤ Dⱼ`. -/
def IsAchievableMD (P : α → ℝ) (d₀ : α → β₀ → ℝ) (d₁ : α → β₁ → ℝ) (d₂ : α → β₂ → ℝ)
    (R₁ R₂ D₀ D₁ D₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ ∃ c : ∀ n : ℕ, MDCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β₀ β₁ β₂,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion₀ P d₀ ≤ D₀ + ε ∧ (c n).distortion₁ P d₁ ≤ D₁ + ε ∧
      (c n).distortion₂ P d₂ ≤ D₂ + ε

/-- **Lecture 14 of [elgamal2010], page 14-3.** The rate–distortion region `R(D₀, D₁, D₂)`: the
closure of the set of the achievable rate pairs. -/
def mdRegion (P : α → ℝ) (d₀ : α → β₀ → ℝ) (d₁ : α → β₁ → ℝ) (d₂ : α → β₂ → ℝ)
    (D₀ D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableMD P d₀ d₁ d₂ R.1 R.2 D₀ D₁ D₂}

omit [Fintype α] in
instance MDCode.finite [Finite α] [Finite β₀] [Finite β₁] [Finite β₂] :
    Finite (MDCode M₁ M₂ n α β₀ β₁ β₂) :=
  Finite.of_injective (fun c : MDCode M₁ M₂ n α β₀ β₁ β₂ =>
      (c.enc₁, c.enc₂, c.dec₀, c.dec₁, c.dec₂))
    fun c c' h => by
      cases c
      cases c'
      simpa using h

omit [Fintype α] in
lemma MDCode.nonempty [Nonempty β₀] [Nonempty β₁] [Nonempty β₂] (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    Nonempty (MDCode M₁ M₂ n α β₀ β₁ β₂) :=
  ⟨⟨fun _ => ⟨0, h₁⟩, fun _ => ⟨0, h₂⟩, fun _ _ => Classical.arbitrary β₀,
    fun _ _ => Classical.arbitrary β₁, fun _ _ => Classical.arbitrary β₂⟩⟩

/-- To show that a rate pair is achievable it is enough to find, for every `ε > 0` and all large
`n`, a code with distortions at most `Dⱼ + ε`. -/
theorem isAchievableMD_of_eventually [Finite β₀] [Finite β₁] [Finite β₂] [Nonempty β₀]
    [Nonempty β₁] [Nonempty β₂] {P : α → ℝ} {d₀ : α → β₀ → ℝ} {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ}
    {R₁ R₂ D₀ D₁ D₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ c : MDCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β₀ β₁ β₂,
      c.distortion₀ P d₀ ≤ D₀ + ε ∧ c.distortion₁ P d₁ ≤ D₁ + ε ∧ c.distortion₂ P d₂ ≤ D₂ + ε) :
    IsAchievableMD P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  have hne := fun n : ℕ => MDCode.nonempty (α := α) (β₀ := β₀) (β₁ := β₁) (β₂ := β₂)
    (n := n) (M₁ := 2 ^ ⌊n * R₁⌋₊) (M₂ := 2 ^ ⌊n * R₂⌋₊) (by positivity) (by positivity)
  obtain ⟨c, hc⟩ := exists_seq_of_eventually
    (C := fun n : ℕ => MDCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β₀ β₁ β₂)
    (fun n c => max (c.distortion₀ P d₀ - D₀) (max (c.distortion₁ P d₁ - D₁)
      (c.distortion₂ P d₂ - D₂))) (a := 0) fun ε hε => by
      filter_upwards [h ε hε] with n ⟨c, h0, h1, h2⟩
      exact ⟨c, by
        rw [zero_add]
        exact max_le (by linarith) (max_le (by linarith) (by linarith))⟩
  refine ⟨hR₁, hR₂, c, fun ε hε => ?_⟩
  filter_upwards [hc ε hε] with n hn
  rw [zero_add] at hn
  have h0 := (le_max_left _ _).trans hn
  have h1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have h2 := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A larger rate pair or a larger distortion triple keeps a pair achievable. -/
theorem IsAchievableMD.mono {P : α → ℝ} {d₀ : α → β₀ → ℝ}
    {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ} {R₁ R₂ D₀ D₁ D₂ D₀' D₁' D₂' : ℝ}
    (h : IsAchievableMD P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂) (h₀ : D₀ ≤ D₀') (h₁ : D₁ ≤ D₁')
    (h₂ : D₂ ≤ D₂') : IsAchievableMD P d₀ d₁ d₂ R₁ R₂ D₀' D₁' D₂' := by
  obtain ⟨hR₁, hR₂, c, hc⟩ := h
  refine ⟨hR₁, hR₂, c, fun ε hε => ?_⟩
  filter_upwards [hc ε hε] with n ⟨a, b, c'⟩
  exact ⟨by linarith, by linarith, by linarith⟩

omit [Fintype α] in
/-- A code from encoders and decoders with arbitrary finite index sets, which are not larger than
the sets of indices of the code. -/
theorem MDCode.exists_of_index {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁]
    [Nonempty ι₂] (h₁ : Fintype.card ι₁ ≤ M₁) (h₂ : Fintype.card ι₂ ≤ M₂)
    (i₁ : (Fin n → α) → ι₁) (i₂ : (Fin n → α) → ι₂) (D₀ : ι₁ × ι₂ → Fin n → β₀)
    (D₁ : ι₁ → Fin n → β₁) (D₂ : ι₂ → Fin n → β₂) :
    ∃ c : MDCode M₁ M₂ n α β₀ β₁ β₂, ∀ x, c.dec₀ (c.enc₁ x, c.enc₂ x) = D₀ (i₁ x, i₂ x) ∧
      c.dec₁ (c.enc₁ x) = D₁ (i₁ x) ∧ c.dec₂ (c.enc₂ x) = D₂ (i₂ x) := by
  obtain ⟨e₁⟩ := Function.Embedding.nonempty_of_card_le (α := ι₁) (β := Fin M₁) (by simpa using h₁)
  obtain ⟨e₂⟩ := Function.Embedding.nonempty_of_card_le (α := ι₂) (β := Fin M₂) (by simpa using h₂)
  have hg₁ := Function.leftInverse_invFun e₁.injective
  have hg₂ := Function.leftInverse_invFun e₂.injective
  refine ⟨⟨fun x => e₁ (i₁ x), fun x => e₂ (i₂ x),
    fun m => D₀ (Function.invFun e₁ m.1, Function.invFun e₂ m.2),
    fun m => D₁ (Function.invFun e₁ m), fun m => D₂ (Function.invFun e₂ m)⟩, fun x => ?_⟩
  simp only [hg₁ (i₁ x), hg₂ (i₂ x), and_self]

end Code

/-! ### The choice of one layer -/

section Layer

variable {A I 𝒟 J : Type*} [Fintype A] [Finite I] [Fintype 𝒟]

open Classical in
/-- **The choice of one layer of a superposition code.** Let `e x` be the index of the previous
layers for the source sequence `x`, and let `G` be the set of the good source sequences. Suppose
that, for every good `x`, a codebook `D` drawn from the law `ν (e x)` has a word `j` with
`R (e x) D x j`, except with probability at most `η`. Then one can fix a codebook `D i` for every
index `i` and a word `f x` for every `x` such that the source sequences that are good and have
`R (e x) (D (e x)) x (f x)` have probability at least `P(G) - η`. -/
theorem exists_layer [Nonempty 𝒟] [Nonempty J] {w : A → ℝ} (hw : IsPMF w) (e : A → I) (G : A → Prop)
    (ν : I → 𝒟 → ℝ) (R : I → 𝒟 → A → J → Prop) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x, G x → IsPMF (ν (e x)) ∧
      ∑ D, ν (e x) D * (if ∀ j, ¬ R (e x) D x j then 1 else 0) ≤ η) :
    ∃ (D : I → 𝒟) (f : A → J),
      ∑ x, w x * (if G x ∧ R (e x) (D (e x)) x (f x) then 0 else 1) ≤
        ∑ x, w x * (if G x then 0 else 1) + η := by
  have := Fintype.ofFinite I
  set fail : I → 𝒟 → A → ℝ := fun i D x => if ∀ j, ¬ R i D x j then 1 else 0 with hfail
  have hfail0 : ∀ i D x, 0 ≤ fail i D x := fun i D x => by
    simp only [hfail]
    split_ifs <;> norm_num
  set S : I → Finset A := fun i => univ.filter fun x => G x ∧ e x = i with hS
  -- The choice for one index.
  have hchoice : ∀ i, ∃ D, ∑ x ∈ S i, w x * fail i D x ≤ η * ∑ x ∈ S i, w x := fun i => by
    by_cases hne : (S i).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hx₀' := (mem_filter.1 hx₀).2
      have hν : IsPMF (ν i) := by
        have := (h x₀ hx₀'.1).1
        rwa [hx₀'.2] at this
      refine exists_le_of_sum_mul_le hν ?_
      calc ∑ D, ν i D * ∑ x ∈ S i, w x * fail i D x
          = ∑ x ∈ S i, w x * ∑ D, ν i D * fail i D x := by
            simp only [mul_sum]
            rw [sum_comm]
            exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
        _ ≤ ∑ x ∈ S i, w x * η := sum_le_sum fun x hx => by
            have hx' := (mem_filter.1 hx).2
            have := (h x hx'.1).2
            rw [hx'.2] at this
            exact mul_le_mul_of_nonneg_left this (hw.nonneg x)
        _ = η * ∑ x ∈ S i, w x := by
            rw [mul_sum]
            exact sum_congr rfl fun _ _ => mul_comm _ _
    · rw [not_nonempty_iff_eq_empty] at hne
      exact ⟨Classical.arbitrary 𝒟, by simp [hne]⟩
  choose D hD using hchoice
  set f : A → J := fun x =>
    if h : ∃ j, R (e x) (D (e x)) x j then h.choose else Classical.arbitrary J with hf
  refine ⟨D, f, ?_⟩
  have hpt : ∀ x, w x * (if G x ∧ R (e x) (D (e x)) x (f x) then 0 else 1) ≤
      w x * (if G x then 0 else 1) + (if G x then w x * fail (e x) (D (e x)) x else 0) :=
        fun x => by
    by_cases hG : G x
    · by_cases hex : ∃ j, R (e x) (D (e x)) x j
      · have hR : R (e x) (D (e x)) x (f x) := by
          simp only [hf, hex, ↓reduceDIte]
          exact hex.choose_spec
        have := mul_nonneg (hw.nonneg x) (hfail0 (e x) (D (e x)) x)
        simp [hG, hR, this]
      · have hR : ¬ R (e x) (D (e x)) x (f x) := fun hr => hex ⟨_, hr⟩
        have hall : ∀ j, ¬ R (e x) (D (e x)) x j := fun j hj => hex ⟨j, hj⟩
        simp [hG, hR, hfail, hall]
    · have := hw.nonneg x
      simp [hG]
  refine (sum_le_sum fun x _ => hpt x).trans ?_
  rw [sum_add_distrib]
  refine add_le_add le_rfl ?_
  -- The sum over the indices.
  have hsum : ∑ x, (if G x then w x * fail (e x) (D (e x)) x else 0) =
      ∑ i, ∑ x ∈ S i, w x * fail i (D i) x := by
    have h1 := sum_fiberwise (univ.filter G) e fun x => w x * fail (e x) (D (e x)) x
    rw [sum_filter] at h1
    rw [← h1]
    refine sum_congr rfl fun i _ => ?_
    rw [filter_filter]
    refine sum_congr rfl fun x hx => ?_
    rw [(mem_filter.1 hx).2.2]
  have hmass : ∑ i, ∑ x ∈ S i, w x ≤ 1 := by
    have h1 := sum_fiberwise (univ.filter G) e w
    have h2 : ∑ x ∈ univ.filter G, w x ≤ ∑ x, w x :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => hw.nonneg x
    rw [hw.sum_eq_one] at h2
    rw [← h1] at h2
    refine le_trans (le_of_eq ?_) h2
    refine sum_congr rfl fun i _ => ?_
    rw [filter_filter]
  rw [hsum]
  calc ∑ i, ∑ x ∈ S i, w x * fail i (D i) x ≤ ∑ i, η * ∑ x ∈ S i, w x :=
        sum_le_sum fun i _ => hD i
    _ = η * ∑ i, ∑ x ∈ S i, w x := (mul_sum _ _ _).symm
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left hmass hη
    _ = η := mul_one η

end Layer

end InfoTheory
