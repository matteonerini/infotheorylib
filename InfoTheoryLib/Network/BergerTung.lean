/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.SideInfoCovering
public import InfoTheoryLib.StateChannel.Multicoding
public import InfoTheoryLib.Typicality.MarkovLemma

/-!
# Distributed lossy source coding: the covering step of Berger–Tung coding

This file defines the distributed lossy source codes of Lecture 13 and proves the covering step of
the Berger–Tung inner bound. Each encoder selects the first codeword of its random codebook that is
jointly typical with its source sequence, and we show that the two selected codewords are jointly
typical with the two source sequences.

The first codeword of a random codebook in a set `A` has exactly the law of a codeword conditioned
on
`A`, which is Lemma 2 of the notes in a sharper form. The Markov lemma then gives the joint
typicality.

## Main definitions

* `DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂`, `IsAchievableDL`, `dlRegion`: the codes and the
  rate–distortion
  region.
* `btLaw P κ₁ κ₂`: the law `p(x₁, x₂) p(u₁ | x₁) p(u₂ | x₂)` of `((X₁, U₁), X₂), U₂)`.
* `firstIn S C l₀`: the first codeword of the codebook `C` in `S`.

## Main statements

* `sum_codebook_firstIn_le`: **the law of the selected codeword (Lemma 2 of Lecture 13)**.
* `sum_codebook_markov_le`: the selected codeword of encoder 2 is typical with `(X₁ⁿ, U₁ⁿ, X₂ⁿ)`.
* `sum_codebook_cond_le`: the selected codeword of encoder 1 is typical with `(X₁ⁿ, X₂ⁿ)`.
* `sum_two_codebooks_le`: the bound for the two encoders together.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ β₂ υ₁ υ₂ : Type*}

/-! ### The codes -/

/-- **Lecture 13 of [elgamal2010], page 13-3.** A distributed lossy source code: two encoders and a
decoder of the pair of source sequences. -/
structure DistLossyCode (M₁ M₂ n : ℕ) (α₁ α₂ β₁ β₂ : Type*) where
  /-- The encoder of the first source. -/
  enc₁ : (Fin n → α₁) → Fin M₁
  /-- The encoder of the second source. -/
  enc₂ : (Fin n → α₂) → Fin M₂
  /-- The decoder. -/
  dec : Fin M₁ × Fin M₂ → (Fin n → β₁) × (Fin n → β₂)

/-- The reconstructions of a code for the sequence of pairs `ω`. -/
def DistLossyCode.output {M₁ M₂ n : ℕ} (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂)
    (ω : Fin n → α₁ × α₂) : (Fin n → β₁) × (Fin n → β₂) :=
  c.dec (c.enc₁ (fstSeq ω), c.enc₂ (sndSeq ω))

/-- The expected distortion `E d₁(X₁ⁿ, X̂₁ⁿ)` of a code. -/
def DistLossyCode.distortion₁ [Fintype α₁] [Fintype α₂] {M₁ M₂ n : ℕ}
    (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂) (P : α₁ × α₂ → ℝ) (d₁ : α₁ → β₁ → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * seqDistortion d₁ (fstSeq ω) (c.output ω).1

/-- The expected distortion `E d₂(X₂ⁿ, X̂₂ⁿ)` of a code. -/
def DistLossyCode.distortion₂ [Fintype α₁] [Fintype α₂] {M₁ M₂ n : ℕ}
    (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂) (P : α₁ × α₂ → ℝ) (d₂ : α₂ → β₂ → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * seqDistortion d₂ (sndSeq ω) (c.output ω).2

/-- **Lecture 13 of [elgamal2010], page 13-3.** A rate pair, in bits, is achievable with the
distortion
pair `(D₁, D₂)` if there are `(2^{nR₁}, 2^{nR₂}, n)` codes with `limsup E dⱼ(Xⱼⁿ, X̂ⱼⁿ) ≤ Dⱼ`. -/
def IsAchievableDL [Fintype α₁] [Fintype α₂] (P : α₁ × α₂ → ℝ) (d₁ : α₁ → β₁ → ℝ)
    (d₂ : α₂ → β₂ → ℝ) (R₁ R₂ D₁ D₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ ∃ c : ∀ n : ℕ, DistLossyCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂ β₁ β₂,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion₁ P d₁ ≤ D₁ + ε ∧ (c n).distortion₂ P d₂ ≤ D₂ + ε

/-- **Lecture 13 of [elgamal2010], page 13-3.** The rate–distortion region `R(D₁, D₂)`: the closure
of
the set of the achievable rate pairs. -/
def dlRegion [Fintype α₁] [Fintype α₂] (P : α₁ × α₂ → ℝ) (d₁ : α₁ → β₁ → ℝ) (d₂ : α₂ → β₂ → ℝ)
    (D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableDL P d₁ d₂ R.1 R.2 D₁ D₂}

/-! ### The first codeword in a set -/

section First

variable {X : Type*} [Fintype X] {L : ℕ}

open Classical in
/-- **Lecture 13 of [elgamal2010], page 13-9.** The first index of the codebook `C` whose codeword
is in
`S`, and `l₀` if there is none. -/
def firstIn (S : Finset X) (C : Fin L → X) (l₀ : Fin L) : Fin L :=
  if h : (univ.filter fun l => C l ∈ S).Nonempty then (univ.filter fun l => C l ∈ S).min' h else l₀

omit [Fintype X] in
open Classical in
lemma firstIn_spec {S : Finset X} {C : Fin L → X} (l₀ : Fin L) (h : ∃ l, C l ∈ S) :
    C (firstIn S C l₀) ∈ S ∧ ∀ l < firstIn S C l₀, C l ∉ S := by
  have hne : (univ.filter fun l => C l ∈ S).Nonempty :=
    let ⟨l, hl⟩ := h
    ⟨l, by simp [hl]⟩
  simp only [firstIn, hne, ↓reduceDIte]
  refine ⟨by simpa using min'_mem _ hne, fun l hl hmem => ?_⟩
  exact absurd (min'_le _ l (by simp [hmem])) (not_le.2 hl)

/-- The product over the indices: the codewords before `l` miss `S`, and the codeword `l` is in `S`.
-/
private def firstFactor (S : Finset X) (f : X → ℝ) (l l' : Fin L) (z : X) : ℝ :=
  open Classical in
  if l' < l then (if z ∉ S then 1 else 0) else if l' = l then (if z ∈ S then f z else 0) else 1

open Classical in
omit [Fintype X] in
private lemma ite_exists_le_sum {S : Finset X} {f : X → ℝ} (hf : ∀ z, 0 ≤ f z) (C : Fin L → X)
    (l₀ : Fin L) :
    (if ∃ l, C l ∈ S then f (C (firstIn S C l₀)) else 0) ≤
      ∑ l, ∏ l', firstFactor S f l l' (C l') := by
  have hnn : ∀ (l l' : Fin L) (z : X), 0 ≤ firstFactor S f l l' z := fun l l' z => by
    simp only [firstFactor]
    split_ifs
    all_goals first | exact zero_le_one | exact le_rfl | exact hf z
  have hsum : ∀ l, 0 ≤ ∏ l', firstFactor S f l l' (C l') := fun l =>
    prod_nonneg fun l' _ => hnn l l' _
  split_ifs with h
  · obtain ⟨h1, h2⟩ := firstIn_spec l₀ h
    set l₁ := firstIn S C l₀
    refine le_trans (le_of_eq ?_) (single_le_sum (fun l _ => hsum l) (mem_univ l₁))
    rw [prod_eq_single l₁]
    · simp [firstFactor, h1]
    · intro l' _ hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [firstFactor, hlt, h2 l' hlt]
      · simp [firstFactor, not_lt.2 hgt.le, hne]
    · simp
  · exact sum_nonneg fun l _ => hsum l

/-- **Lemma 2 of Lecture 13, pages 13-11 and 13-49.** The first codeword of a random codebook in a
set
`S` of probability `a > 0` has at most the law of a codeword conditioned on `S`:
`E f(Uⁿ(L)) ≤ (1 / a) ∑_{u ∈ S} p(u) f(u)` on the event that some codeword is in `S`. -/
theorem sum_codebook_firstIn_le {μ : X → ℝ} (hμ : IsPMF μ) {S : Finset X} (hS : 0 < prob μ S)
    {f : X → ℝ} (hf : ∀ z, 0 ≤ f z) (l₀ : Fin L) :
    ∑ C : Fin L → X, iidPMF μ L C *
        (open Classical in if ∃ l, C l ∈ S then f (C (firstIn S C l₀)) else 0) ≤
      (∑ z ∈ S, μ z * f z) / prob μ S := by
  classical
  set a := prob μ S
  set b := ∑ z ∈ S, μ z * f z
  have hb0 : 0 ≤ b := sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (hf z)
  have ha1 : a ≤ 1 := prob_le_one hμ S
  have hlaw := iidPMF_isPMF hμ L
  -- The sums of the factors.
  have hmiss : ∑ z, μ z * (if z ∉ S then (1 : ℝ) else 0) = 1 - a := by
    have e : a = ∑ z, if z ∈ S then μ z else 0 := by
      simp only [a, prob]
      rw [sum_ite_mem, univ_inter]
    have h : ∑ z, μ z * (if z ∉ S then (1 : ℝ) else 0) + ∑ z, (if z ∈ S then μ z else 0) =
        ∑ z, μ z := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun z _ => ?_
      split_ifs <;> simp
    rw [hμ.sum_eq_one] at h
    rw [e]
    linarith
  have hhit : ∑ z, μ z * (if z ∈ S then f z else 0) = b := by
    simp only [b, mul_ite, mul_zero]
    rw [sum_ite_mem, univ_inter]
  have hprod : ∀ l : Fin L, ∑ C : Fin L → X, iidPMF μ L C * ∏ l', firstFactor S f l l' (C l') =
      (1 - a) ^ (l : ℕ) * b := fun l => by
    rw [sum_iidPMF_mul_prod μ fun l' z => firstFactor S f l l' z]
    have hval : ∀ l', ∑ z, μ z * firstFactor S f l l' z =
        if l' < l then 1 - a else if l' = l then b else 1 := fun l' => by
      by_cases h1 : l' < l
      · simp only [firstFactor, h1, ↓reduceIte, hmiss]
      · by_cases h2 : l' = l
        · simp only [firstFactor, h2, lt_irrefl, ↓reduceIte, hhit]
        · simp only [firstFactor, h1, h2, ↓reduceIte, mul_one, hμ.sum_eq_one]
    simp only [hval]
    have hcard : (univ.filter fun x : Fin L => x < l).card = (l : ℕ) := by
      rw [show (univ.filter fun x : Fin L => x < l) = Iio l from by ext; simp, Fin.card_Iio]
    rw [prod_ite, prod_const, hcard, prod_eq_single l]
    · simp
    · intro l' h3 hne
      simp [hne]
    · intro hl
      simp at hl
  have hgeom : ∑ l : Fin L, (1 - a) ^ (l : ℕ) ≤ 1 / a := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (1 - a) ^ i) L, le_div_iff₀ hS]
    have h := geom_sum_mul (1 - a) L
    have h2 : ((1 - a) ^ L : ℝ) ≥ 0 := pow_nonneg (by linarith) L
    have h3 : (∑ i ∈ range L, (1 - a) ^ i) * ((1 - a) - 1) = (1 - a) ^ L - 1 := h
    nlinarith
  calc ∑ C : Fin L → X, iidPMF μ L C *
        (if ∃ l, C l ∈ S then f (C (firstIn S C l₀)) else 0)
      ≤ ∑ C : Fin L → X, iidPMF μ L C * ∑ l, ∏ l', firstFactor S f l l' (C l') :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (ite_exists_le_sum hf C l₀) (hlaw.nonneg C)
    _ = ∑ l : Fin L, ∑ C : Fin L → X, iidPMF μ L C * ∏ l', firstFactor S f l l' (C l') := by
        simp only [mul_sum]
        exact sum_comm
    _ = (∑ l : Fin L, (1 - a) ^ (l : ℕ)) * b := by
        simp only [hprod, sum_mul]
    _ ≤ 1 / a * b := mul_le_mul_of_nonneg_right hgeom hb0
    _ = b / a := by ring

end First

/-! ### The law of the sources and the auxiliary random variables -/

section Law

variable [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] {P : α₁ × α₂ → ℝ}
  {κ₁ : α₁ → υ₁ → ℝ} {κ₂ : α₂ → υ₂ → ℝ}

/-- The law `p(x₁, x₂) p(u₁ | x₁)` of `((X₁, U₁), X₂)`. -/
def btQ₃ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) : (α₁ × υ₁) × α₂ → ℝ :=
  fun z => P (z.1.1, z.2) * κ₁ z.1.1 z.1.2

/-- **Lecture 13 of [elgamal2010], page 13-9.** The law `p(x₁, x₂) p(u₁ | x₁) p(u₂ | x₂)` of
`(((X₁, U₁), X₂), U₂)`. -/
def btLaw (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) :
    ((α₁ × υ₁) × α₂) × υ₂ → ℝ :=
  jointOf (btQ₃ P κ₁) fun w => κ₂ w.2

/-- The law of `(X₁, U₁)`. -/
abbrev btJ₁ (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) : α₁ × υ₁ → ℝ := jointOf (margFst P) κ₁

/-- The law of `(X₂, U₂)`. -/
abbrev btJ₂ (P : α₁ × α₂ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) : α₂ × υ₂ → ℝ := jointOf (margSnd P) κ₂

lemma btJ₁_isPMF (hP : IsPMF P) (h₁ : IsChannel κ₁) : IsPMF (btJ₁ P κ₁) :=
  jointOf_isPMF (hP.dist _) h₁

lemma btJ₂_isPMF (hP : IsPMF P) (h₂ : IsChannel κ₂) : IsPMF (btJ₂ P κ₂) :=
  jointOf_isPMF (hP.dist _) h₂

lemma btQ₃_isPMF (hP : IsPMF P) (h₁ : IsChannel κ₁) : IsPMF (btQ₃ P κ₁) := by
  refine ⟨fun z => mul_nonneg (hP.nonneg _) ((h₁ _).nonneg _), ?_⟩
  rw [← hP.sum_eq_one, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun x₁ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun x₂ _ => ?_
  simp only [btQ₃]
  rw [← mul_sum, (h₁ x₁).sum_eq_one, mul_one]

lemma btLaw_isPMF (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) :
    IsPMF (btLaw P κ₁ κ₂) :=
  jointOf_isPMF (btQ₃_isPMF hP h₁) fun w => h₂ w.2

/-- The first marginal of the law is the law of `((X₁, U₁), X₂)`. -/
lemma margFst_btLaw (h₂ : IsChannel κ₂) : margFst (btLaw P κ₁ κ₂) = btQ₃ P κ₁ :=
  dist_jointOf_fst fun w => h₂ w.2

/-- The first marginal of `((X₁, U₁), X₂)` is the law of `(X₁, U₁)`. -/
lemma margFst_btQ₃ : margFst (btQ₃ P κ₁) = btJ₁ P κ₁ := by
  funext ⟨x₁, u₁⟩
  have e : dist (btQ₃ P κ₁) Prod.fst (x₁, u₁) = ∑ x₂, btQ₃ P κ₁ ((x₁, u₁), x₂) := dist_fst _ _
  change dist (btQ₃ P κ₁) Prod.fst (x₁, u₁) = _
  rw [e]
  simp only [btQ₃, jointOf]
  rw [← sum_mul, margFst_apply]

omit [Fintype α₁] [Fintype α₂] [Fintype υ₁] in
/-- The Markov chain `(X₁, U₁) → X₂ → U₂`. -/
lemma btLaw_markov [Finite α₁] [Finite α₂] [Finite υ₁] (h₂ : IsChannel κ₂) (a : α₁ × υ₁) (b : α₂)
    (c : υ₂) :
    btLaw P κ₁ κ₂ ((a, b), c) = marg (btLaw P κ₁ κ₂) (a, b) * κ₂ b c := by
  have := Fintype.ofFinite α₁
  have := Fintype.ofFinite α₂
  have := Fintype.ofFinite υ₁
  have hm : marg (btLaw P κ₁ κ₂) (a, b) = btQ₃ P κ₁ (a, b) := by
    rw [marg_eq_dist]
    exact congrFun (margFst_btLaw h₂) (a, b)
  rw [hm]
  rfl

end Law

/-! ### The codeword of encoder 2 -/

section Markov

variable [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] {P : α₁ × α₂ → ℝ}
  {κ₁ : α₁ → υ₁ → ℝ} {κ₂ : α₂ → υ₂ → ℝ} {n L : ℕ} {ε ε₁ ε₂ : ℝ}

omit [Fintype α₁] [Fintype υ₁] [Fintype α₂] in
/-- On the jointly typical sequences, the channel of `jointOf` is the channel. -/
lemma channelExt_condPMF_jointOf [Finite α₂] {p : α₂ → ℝ} (hκ : IsChannel κ₂) {x : Fin n → α₂}
    (hx : ∀ i, p (x i) ≠ 0) : channelExt (condPMF (jointOf p κ₂)) n x = channelExt κ₂ n x := by
  have := Fintype.ofFinite α₂
  funext z
  refine prod_congr rfl fun i _ => ?_
  have hm : marg (jointOf p κ₂) (x i) = p (x i) := by
    rw [marg_eq_dist]
    exact congrFun (dist_jointOf_fst hκ) (x i)
  simp only [condPMF, hm, jointOf]
  field_simp [hx i]

/-- The exponent of the covering lemma for a channel `κ`: `I(X; U) + ε (H(U) + H(U | X))`. -/
def coverExp (J : α₂ × υ₂ → ℝ) (ε : ℝ) : ℝ :=
  I[Prod.snd : Prod.fst ; J] + ε * (H[Prod.snd ; J] + H[Prod.snd | Prod.fst ; J])

/-- **Lecture 13, page 13-11.** For `(x₁ⁿ, u₁ⁿ, x₂ⁿ)` typical, the codeword of encoder 2 is typical
with
`(x₁ⁿ, u₁ⁿ, x₂ⁿ)`, over the random codebooks, by the Markov lemma and Lemma 2. -/
theorem sum_codebook_markov_le (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hε : ε₁ < ε) (hε1 : ε - ε₁ ≤ 1) (hε₂ : ε₂ ≤ 1 / 2) (hn : 0 < n) (l₀ : Fin L)
    {a : Fin n → α₁ × υ₁} {x₂ : Fin n → α₂}
    (ht : zipSeq a x₂ ∈ robustTypicalSet (btQ₃ P κ₁) n ε₁)
    (hlow : (1 - ε₂) * exp (-(n * coverExp (btJ₂ P κ₂) ε₂)) ≤
      prob (iidPMF (margSnd (btJ₂ P κ₂)) n) (condRobustTypicalSet (btJ₂ P κ₂) ε₂ x₂)) :
    ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF (margSnd (btJ₂ P κ₂)) n) L C *
      (open Classical in if zipSeq (zipSeq a x₂) (C (firstIn
        (condRobustTypicalSet (btJ₂ P κ₂) ε₂ x₂) C l₀)) ∈ robustTypicalSet (btLaw P κ₁ κ₂) n ε
        then 0 else 1) ≤
    exp (-(L * ((1 - ε₂) * exp (-(n * coverExp (btJ₂ P κ₂) ε₂))))) +
      2 * (exp (n * (2 * (ε₂ * (H[Prod.snd ; btJ₂ P κ₂] + H[Prod.snd | Prod.fst ; btJ₂ P κ₂])))) *
        condExpBound (btLaw P κ₁ κ₂) ε₁ ε n) := by
  classical
  have hJ := btJ₂_isPMF (P := P) hP h₂
  set J := btJ₂ P κ₂ with hJd
  set r := margSnd J with hr
  have hrP : IsPMF r := hJ.dist _
  have hrn := iidPMF_isPMF hrP n
  have hlaw := iidPMF_isPMF hrn L
  set A := condRobustTypicalSet J ε₂ x₂ with hA
  set T := condRobustTypicalSet (btLaw P κ₁ κ₂) ε (zipSeq a x₂) with hT
  set low := (1 - ε₂) * exp (-(n * coverExp J ε₂)) with hlowd
  have hε₂1 : 0 < 1 - ε₂ := by linarith
  have hlow0 : 0 < low := mul_pos hε₂1 (exp_pos _)
  have ha0 : 0 < prob (iidPMF r n) A := hlow0.trans_le hlow
  set Hu := H[Prod.snd ; J]
  set Hc := H[Prod.snd | Prod.fst ; J]
  have hI : I[Prod.snd : Prod.fst ; J] = Hu - Hc := mutualInfo_eq_entropy_sub_condEntropy hJ _ _
  set f : (Fin n → υ₂) → ℝ := fun z => if z ∉ T then 1 else 0 with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by simp only [hf]; split_ifs <;> norm_num
  have hmem : ∀ z, (if zipSeq (zipSeq a x₂) z ∈ robustTypicalSet (btLaw P κ₁ κ₂) n ε then
      (0 : ℝ) else 1) = f z := fun z => by
    simp only [hf, hT, mem_condRobustTypicalSet]
    split_ifs <;> simp_all
  -- The codeword is in `A`, or no codeword is.
  have hsplit : ∀ C : Fin L → Fin n → υ₂, f (C (firstIn A C l₀)) ≤
      (if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) +
        (if ∀ l, C l ∉ A then 1 else 0) := fun C => by
    by_cases h : ∃ l, C l ∈ A
    · have h' : ¬ ∀ l, C l ∉ A := by
        push Not
        exact h
      simp [h, h']
    · have h' : ∀ l, C l ∉ A := fun l hl => h ⟨l, hl⟩
      rw [ite_eq_right h, ite_eq_left h', zero_add]
      simp only [hf]
      split_ifs <;> norm_num
  have h1 := sum_codebook_firstIn_le hrn ha0 hf0 l₀ (L := L)
  have h2 := sum_iidPMF_ite_forall_not_mem_le hrn L A
  -- The Markov lemma.
  set φ : (Fin n → υ₂) → ℝ := fun z => if z ∈ A then iidPMF r n z / prob (iidPMF r n) A / 2 else 0
    with hφ
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    simp only [hφ]
    split_ifs
    · exact div_nonneg (div_nonneg (hrn.nonneg z) ha0.le) (by norm_num)
    · exact le_rfl
  have hpos : ∀ z ∈ A, ∀ i, margSnd P (x₂ i) ≠ 0 := fun z hz i h => by
    have := pos_of_mem_robustTypicalSet hJ.nonneg (mem_condRobustTypicalSet.1 hz) i
    simp only [zipSeq, hJd, btJ₂, jointOf, h, zero_mul] at this
    exact lt_irrefl _ this
  have hAk : ∀ z ∈ A, exp (-(n * (Hc + ε₂ * Hc))) ≤ channelExt κ₂ n x₂ z := fun z hz => by
    have h3 := le_channelExt_condPMF_of_mem hJ (mem_condRobustTypicalSet.1 hz)
    rwa [hJd, channelExt_condPMF_jointOf h₂ (hpos z hz)] at h3
  have hφA : ∀ z ∈ A, φ z ≤ exp (-(n * (Hu - ε₂ * Hu - coverExp J ε₂))) := fun z hz => by
    have h3 : iidPMF r n z ≤ exp (-(n * (Hu - ε₂ * Hu))) :=
      iidPMF_le_of_mem_robustTypicalSet (hJ.dist _) (snd_mem_robustTypicalSet
        (mem_condRobustTypicalSet.1 hz))
    simp only [hφ, hz, ite_true]
    have h4 : iidPMF r n z / prob (iidPMF r n) A / 2 ≤
        exp (-(n * (Hu - ε₂ * Hu))) / low / 2 := by
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      exact div_le_div₀ (exp_pos _).le h3 hlow0 hlow
    refine h4.trans (le_of_le_of_eq (b := exp (-(n * (Hu - ε₂ * Hu))) *
      exp (n * coverExp J ε₂)) ?_ ?_)
    · simp only [hlowd]
      rw [div_div, div_le_iff₀ (by positivity)]
      have h5 : 1 ≤ (1 - ε₂) * 2 := by linarith
      have hE := mul_pos (exp_pos (-(n * (Hu - ε₂ * Hu)))) (exp_pos (n * coverExp J ε₂))
      have hrw : exp (n * coverExp J ε₂) * exp (-(n * coverExp J ε₂)) = 1 := by
        rw [← exp_add]
        simp
      calc exp (-(n * (Hu - ε₂ * Hu))) = exp (-(n * (Hu - ε₂ * Hu))) *
            (exp (n * coverExp J ε₂) * exp (-(n * coverExp J ε₂))) := by rw [hrw, mul_one]
        _ ≤ exp (-(n * (Hu - ε₂ * Hu))) * exp (n * coverExp J ε₂) *
            ((1 - ε₂) * exp (-(n * coverExp J ε₂)) * 2) := by
            have := exp_pos (-(n * coverExp J ε₂))
            nlinarith [mul_le_mul_of_nonneg_left h5 (mul_pos hE this).le]
    · rw [← exp_add]
      congr 1
      ring
  have hm := sum_not_mem_condRobust_le (q := btLaw P κ₁ κ₂) (κ := κ₂)
    (btLaw_isPMF hP h₁ h₂) h₂ (fun a b c => btLaw_markov h₂ a b c) hε hε1 hn
    (by rwa [margFst_btLaw h₂]) hφ0 A hAk hφA
  have hoff : ∑ z, (if z ∉ A then φ z else 0) = 0 := sum_eq_zero fun z _ => by
    simp only [hφ]
    split_ifs <;> simp_all
  rw [hoff, zero_add] at hm
  have hE : n * (Hc + ε₂ * Hc - (Hu - ε₂ * Hu - coverExp J ε₂)) = n * (2 * (ε₂ * (Hu + Hc))) := by
    simp only [coverExp, hI]
    ring
  rw [hE] at hm
  have hsum : (∑ z ∈ A, iidPMF r n z * f z) / prob (iidPMF r n) A =
      2 * ∑ z, (if z ∉ T then φ z else 0) := by
    have hA' : ∑ z ∈ A, iidPMF r n z * f z = ∑ z, if z ∈ A then iidPMF r n z * f z else 0 := by
      rw [sum_ite_mem, univ_inter]
    rw [hA', sum_div, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    simp only [hφ, hf]
    by_cases h3 : z ∈ A <;> by_cases h4 : z ∈ T <;> simp [h3, h4]
    field_simp
  have hmiss : exp (-(L * prob (iidPMF r n) A)) ≤ exp (-(L * low)) :=
    exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg L)))
  calc ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF r n) L C *
        (if zipSeq (zipSeq a x₂) (C (firstIn A C l₀)) ∈ robustTypicalSet (btLaw P κ₁ κ₂) n ε
          then 0 else 1)
      = ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF r n) L C * f (C (firstIn A C l₀)) :=
        sum_congr rfl fun C _ => by rw [hmem]
    _ ≤ ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF r n) L C *
          ((if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) +
            (if ∀ l, C l ∉ A then 1 else 0)) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hsplit C) (hlaw.nonneg C)
    _ = ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF r n) L C *
          (if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) +
        ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF r n) L C *
          (if ∀ l, C l ∉ A then 1 else 0) := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun C _ => mul_add _ _ _
    _ ≤ _ := by
        have h3 : (∑ z ∈ A, iidPMF r n z * f z) / prob (iidPMF r n) A ≤
            2 * (exp (n * (2 * (ε₂ * (Hu + Hc)))) * condExpBound (btLaw P κ₁ κ₂) ε₁ ε n) := by
          rw [hsum]
          have hm' : ∑ z, (if z ∉ T then φ z else 0) ≤
              exp (n * (2 * (ε₂ * (Hu + Hc)))) * condExpBound (btLaw P κ₁ κ₂) ε₁ ε n := hm
          exact mul_le_mul_of_nonneg_left hm' (by norm_num)
        have h4 : ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF r n) L C *
            (if ∀ l, C l ∉ A then 1 else 0) ≤ exp (-(L * low)) := by
          refine le_trans (le_of_eq ?_) (h2.trans hmiss)
          exact sum_congr rfl fun C _ => by congr
        have h5 : ∑ C : Fin L → Fin n → υ₂, iidPMF (iidPMF r n) L C *
            (if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) ≤
            2 * (exp (n * (2 * (ε₂ * (Hu + Hc)))) * condExpBound (btLaw P κ₁ κ₂) ε₁ ε n) := by
          refine le_trans (le_of_eq ?_) (h1.trans h3)
          exact sum_congr rfl fun C _ => by congr
        rw [add_comm]
        exact add_le_add h4 h5

end Markov

/-! ### The codeword of encoder 1 and the two encoders together -/

section Two

variable [Fintype α₁] [Fintype α₂] [Fintype υ₁] [Fintype υ₂] {P : α₁ × α₂ → ℝ}
  {κ₁ : α₁ → υ₁ → ℝ} {κ₂ : α₂ → υ₂ → ℝ} {W : α₁ → α₂ → ℝ} {n L₁ L₂ : ℕ} {ε ε₁ ε₂ ε₃ : ℝ}

omit [Fintype υ₁] in
/-- The Markov chain `U₁ → X₁ → X₂`: given `(x₁ⁿ, u₁ⁿ)`, the sequence `X₂ⁿ` has the law
`W(x₂ | x₁)`. -/
lemma channelExt_condPMF_btQ₃ [Finite υ₁] (hPW : ∀ x y, P (x, y) = margFst P x * W x y)
    {x₁ : Fin n → α₁} {u₁ : Fin n → υ₁}
    (h : ∀ i, btJ₁ P κ₁ (x₁ i, u₁ i) ≠ 0) :
    channelExt (condPMF (btQ₃ P κ₁)) n (zipSeq x₁ u₁) = channelExt W n x₁ := by
  have := Fintype.ofFinite υ₁
  funext x₂
  refine prod_congr rfl fun i _ => ?_
  have hm : marg (btQ₃ P κ₁) (x₁ i, u₁ i) = btJ₁ P κ₁ (x₁ i, u₁ i) := by
    rw [marg_eq_dist]
    exact congrFun margFst_btQ₃ _
  have hne := h i
  simp only [condPMF, zipSeq, hm, btQ₃]
  rw [hPW]
  simp only [btJ₁, jointOf] at hne ⊢
  rw [show margFst P (x₁ i) * W (x₁ i) (x₂ i) * κ₁ (x₁ i) (u₁ i) =
    W (x₁ i) (x₂ i) * (margFst P (x₁ i) * κ₁ (x₁ i) (u₁ i)) by ring, mul_div_assoc, div_self hne,
    mul_one]

open Classical in
/-- **Lecture 13, page 13-11.** For a fixed `x₁ⁿ` and a random codebook, `(x₁ⁿ, U₁ⁿ(L₁), X₂ⁿ)` is
typical
for `X₂ⁿ` from the channel `W`, except if no codeword is typical with `x₁ⁿ`, by the conditional
typicality lemma. -/
theorem sum_codebook_cond_le (hP : IsPMF P) (h₁ : IsChannel κ₁) (hW : IsChannel W)
    (hPW : ∀ x y, P (x, y) = margFst P x * W x y) (hε : ε₂ < ε₁) (hn : 0 < n) (l₀ : Fin L₁)
    (x₁ : Fin n → α₁) (C : Fin L₁ → Fin n → υ₁) :
    ∑ x₂, channelExt W n x₁ x₂ *
      (if zipSeq (zipSeq x₁ (C (firstIn (condRobustTypicalSet (btJ₁ P κ₁) ε₂ x₁) C l₀))) x₂ ∈
        robustTypicalSet (btQ₃ P κ₁) n ε₁ then 0 else 1) ≤
    (if ∀ l, C l ∉ condRobustTypicalSet (btJ₁ P κ₁) ε₂ x₁ then 1 else 0) +
      condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n := by
  set A := condRobustTypicalSet (btJ₁ P κ₁) ε₂ x₁ with hA
  have hK : 0 ≤ condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n :=
    div_nonneg (sum_nonneg fun z _ => by positivity) (Nat.cast_nonneg n)
  have hμ := hW.ext n x₁
  by_cases h : ∃ l, C l ∈ A
  · obtain ⟨hmem, -⟩ := firstIn_spec l₀ h
    set u := C (firstIn A C l₀) with hu
    have h' : ¬ ∀ l, C l ∉ A := by
      push Not
      exact h
    rw [ite_eq_right h', zero_add]
    have hz : zipSeq x₁ u ∈ robustTypicalSet (btJ₁ P κ₁) n ε₂ := mem_condRobustTypicalSet.1 hmem
    have hJ := btJ₁_isPMF (P := P) hP h₁
    have hne : ∀ i, btJ₁ P κ₁ (x₁ i, u i) ≠ 0 := fun i =>
      (pos_of_mem_robustTypicalSet hJ.nonneg hz i).ne'
    have hb := one_sub_div_le_prob_condRobustTypicalSet (q := btQ₃ P κ₁) (x := zipSeq x₁ u)
      (btQ₃_isPMF hP h₁) hε hn (by rwa [margFst_btQ₃])
    rw [channelExt_condPMF_btQ₃ hPW hne] at hb
    set T := condRobustTypicalSet (btQ₃ P κ₁) ε₁ (zipSeq x₁ u)
    have e : ∑ x₂, channelExt W n x₁ x₂ *
        (if zipSeq (zipSeq x₁ u) x₂ ∈ robustTypicalSet (btQ₃ P κ₁) n ε₁ then (0 : ℝ) else 1) =
        1 - prob (channelExt W n x₁) T := by
      have e1 : prob (channelExt W n x₁) T = ∑ x₂, if x₂ ∈ T then channelExt W n x₁ x₂ else 0 := by
        rw [prob, sum_ite_mem, univ_inter]
      have e2 : ∑ x₂, channelExt W n x₁ x₂ *
          (if zipSeq (zipSeq x₁ u) x₂ ∈ robustTypicalSet (btQ₃ P κ₁) n ε₁ then (0 : ℝ) else 1) +
          ∑ x₂, (if x₂ ∈ T then channelExt W n x₁ x₂ else 0) = ∑ x₂, channelExt W n x₁ x₂ := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun x₂ _ => ?_
        by_cases h3 : x₂ ∈ T
        · have h4 := mem_condRobustTypicalSet.1 h3
          simp [h3, h4]
        · have h4 : zipSeq (zipSeq x₁ u) x₂ ∉ robustTypicalSet (btQ₃ P κ₁) n ε₁ := fun h5 =>
            h3 (mem_condRobustTypicalSet.2 h5)
          simp [h3, h4]
      rw [hμ.sum_eq_one] at e2
      rw [e1]
      linarith
    rw [e]
    linarith
  · have h' : ∀ l, C l ∉ A := fun l hl => h ⟨l, hl⟩
    rw [ite_eq_left h']
    calc _ ≤ ∑ x₂, channelExt W n x₁ x₂ := sum_le_sum fun x₂ _ => by
          refine mul_le_of_le_one_right (hμ.nonneg x₂) ?_
          split_ifs <;> norm_num
      _ = 1 := hμ.sum_eq_one
      _ ≤ _ := le_add_of_nonneg_right hK

/-- The four sequences of a block, as a sequence of quadruples. -/
abbrev btSeq (ω : Fin n → α₁ × α₂) (u₁ : Fin n → υ₁) (u₂ : Fin n → υ₂) :
    Fin n → ((α₁ × υ₁) × α₂) × υ₂ :=
  zipSeq (zipSeq (zipSeq (fstSeq ω) u₁) (sndSeq ω)) u₂

/-- The bound of the covering step of Berger–Tung coding. -/
def btCoverBound (P : α₁ × α₂ → ℝ) (κ₁ : α₁ → υ₁ → ℝ) (κ₂ : α₂ → υ₂ → ℝ) (ε ε₁ ε₂ ε₃ : ℝ)
    (n L₁ L₂ : ℕ) : ℝ :=
  exp (-(L₂ * ((1 - ε₂) * exp (-(n * coverExp (btJ₂ P κ₂) ε₂))))) +
    2 * (exp (n * (2 * (ε₂ * (H[Prod.snd ; btJ₂ P κ₂] + H[Prod.snd | Prod.fst ; btJ₂ P κ₂])))) *
      condExpBound (btLaw P κ₁ κ₂) ε₁ ε n) +
    (1 - prob (iidPMF (margSnd P) n) (robustTypicalSet (margSnd P) n ε₃)) +
    (1 - prob (iidPMF (margFst P) n) (robustTypicalSet (margFst P) n ε₃)) +
    exp (-(L₁ * ((1 - ε₂) * exp (-(n * coverExp (btJ₁ P κ₁) ε₂))))) +
    condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n

/-- `E 1_{Sᶜ} = 1 - P(S)`. -/
lemma sum_mul_ite_zero_one {X : Type*} [Fintype X] {p : X → ℝ} (hp : IsPMF p) (S : Finset X) :
    ∑ x, p x * (open Classical in if x ∈ S then (0 : ℝ) else 1) = 1 - prob p S := by
  classical
  have e : prob p S = ∑ x, if x ∈ S then p x else 0 := by
    rw [prob, sum_ite_mem, univ_inter]
  have h : ∑ x, p x * (if x ∈ S then (0 : ℝ) else 1) + ∑ x, (if x ∈ S then p x else 0) =
      ∑ x, p x := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [hp.sum_eq_one] at h
  rw [e]
  linarith

/-- `E (e 1_S + 1_{Sᶜ}) ≤ (1 - P(S)) + e`. -/
lemma sum_mul_ite_le {X : Type*} [Fintype X] {p : X → ℝ} (hp : IsPMF p) (S : Finset X) {e : ℝ}
    (he : 0 ≤ e) :
    ∑ x, p x * (open Classical in if x ∈ S then e else 1) ≤ (1 - prob p S) + e := by
  classical
  have h1 := sum_mul_ite_zero_one hp S
  have h2 : ∑ x, p x * (if x ∈ S then e else 1) ≤
      ∑ x, (p x * (if x ∈ S then (0 : ℝ) else 1) + p x * e) := sum_le_sum fun x _ => by
    have := hp.nonneg x
    split_ifs
    · simp
    · nlinarith [mul_nonneg this he]
  rw [sum_add_distrib, h1, ← sum_mul, hp.sum_eq_one, one_mul] at h2
  exact h2

/-- The nonnegativity of the bound. -/
lemma condExpBound_nonneg {α β : Type*} [Fintype α] [Fintype β] (q : α × β → ℝ) (ε' ε : ℝ) (n : ℕ) :
    0 ≤ condExpBound q ε' ε n :=
  sum_nonneg fun _ _ => mul_nonneg (by norm_num) (exp_pos _).le

open Classical in
/-- **Lecture 13, pages 13-10 and 13-11.** The errors `E₁`, `E₂` and `E₃`: over the two random
codebooks,
the selected codewords are jointly typical with the two source sequences, except with probability
`btCoverBound`. -/
theorem sum_two_codebooks_le (hP : IsPMF P) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hε₁₂ : ε₂ < ε₁) (hε : ε₁ < ε) (hε1 : ε - ε₁ ≤ 1) (hε₂ : ε₂ ≤ 1 / 2) (hn : 0 < n)
    (l₁ : Fin L₁) (l₂ : Fin L₂)
    (hlow₁ : ∀ x ∈ robustTypicalSet (margFst P) n ε₃,
      (1 - ε₂) * exp (-(n * coverExp (btJ₁ P κ₁) ε₂)) ≤
        prob (iidPMF (margSnd (btJ₁ P κ₁)) n) (condRobustTypicalSet (btJ₁ P κ₁) ε₂ x))
    (hlow₂ : ∀ x ∈ robustTypicalSet (margSnd P) n ε₃,
      (1 - ε₂) * exp (-(n * coverExp (btJ₂ P κ₂) ε₂)) ≤
        prob (iidPMF (margSnd (btJ₂ P κ₂)) n) (condRobustTypicalSet (btJ₂ P κ₂) ε₂ x)) :
    ∑ C₁ : Fin L₁ → Fin n → υ₁, iidPMF (iidPMF (margSnd (btJ₁ P κ₁)) n) L₁ C₁ *
      ∑ C₂ : Fin L₂ → Fin n → υ₂, iidPMF (iidPMF (margSnd (btJ₂ P κ₂)) n) L₂ C₂ *
        ∑ ω, iidPMF P n ω *
          (if btSeq ω (C₁ (firstIn (condRobustTypicalSet (btJ₁ P κ₁) ε₂ (fstSeq ω)) C₁ l₁))
              (C₂ (firstIn (condRobustTypicalSet (btJ₂ P κ₂) ε₂ (sndSeq ω)) C₂ l₂)) ∈
            robustTypicalSet (btLaw P κ₁ κ₂) n ε then 0 else 1) ≤
    btCoverBound P κ₁ κ₂ ε ε₁ ε₂ ε₃ n L₁ L₂ := by
  obtain ⟨W, hW, hPW⟩ := exists_side_channel hP
  have hJ₁ := btJ₁_isPMF (P := P) hP h₁
  have hJ₂ := btJ₂_isPMF (P := P) hP h₂
  have hlaw₁ := iidPMF_isPMF (iidPMF_isPMF (hJ₁.dist Prod.snd) n) L₁
  have hlaw₂ := iidPMF_isPMF (iidPMF_isPMF (hJ₂.dist Prod.snd) n) L₂
  have hμ := iidPMF_isPMF hP n
  have hp₁ := iidPMF_isPMF (hP.dist Prod.fst) n
  have hp₂ := iidPMF_isPMF (hP.dist Prod.snd) n
  set law₁ := iidPMF (iidPMF (margSnd (btJ₁ P κ₁)) n) L₁
  set law₂ := iidPMF (iidPMF (margSnd (btJ₂ P κ₂)) n) L₂
  set A₁ := fun x : Fin n → α₁ => condRobustTypicalSet (btJ₁ P κ₁) ε₂ x with hA₁
  set A₂ := fun x : Fin n → α₂ => condRobustTypicalSet (btJ₂ P κ₂) ε₂ x with hA₂
  set T := robustTypicalSet (btLaw P κ₁ κ₂) n ε
  set T₁ := robustTypicalSet (btQ₃ P κ₁) n ε₁
  set Tp₁ := robustTypicalSet (margFst P) n ε₃
  set Tp₂ := robustTypicalSet (margSnd P) n ε₃
  set e₁ := exp (-(L₁ * ((1 - ε₂) * exp (-(n * coverExp (btJ₁ P κ₁) ε₂)))))
  set η := exp (-(L₂ * ((1 - ε₂) * exp (-(n * coverExp (btJ₂ P κ₂) ε₂))))) +
    2 * (exp (n * (2 * (ε₂ * (H[Prod.snd ; btJ₂ P κ₂] + H[Prod.snd | Prod.fst ; btJ₂ P κ₂])))) *
      condExpBound (btLaw P κ₁ κ₂) ε₁ ε n) with hη
  have hη0 : 0 ≤ η := add_nonneg (exp_pos _).le
    (mul_nonneg (by norm_num) (mul_nonneg (exp_pos _).le (condExpBound_nonneg _ _ _ _)))
  have hK : 0 ≤ condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n :=
    div_nonneg (sum_nonneg fun z _ => by positivity) (Nat.cast_nonneg n)
  -- Encoder 2, for a fixed `ω` and a fixed codebook of encoder 1.
  have hstep : ∀ (ω : Fin n → α₁ × α₂) (u₁ : Fin n → υ₁),
      ∑ C₂ : Fin L₂ → Fin n → υ₂, law₂ C₂ *
        (if btSeq ω u₁ (C₂ (firstIn (A₂ (sndSeq ω)) C₂ l₂)) ∈ T then 0 else 1) ≤
      η + (if zipSeq (zipSeq (fstSeq ω) u₁) (sndSeq ω) ∈ T₁ then 0 else 1) +
        (if sndSeq ω ∈ Tp₂ then 0 else 1) := fun ω u₁ => by
    have hle1 : ∑ C₂ : Fin L₂ → Fin n → υ₂, law₂ C₂ *
        (if btSeq ω u₁ (C₂ (firstIn (A₂ (sndSeq ω)) C₂ l₂)) ∈ T then (0 : ℝ) else 1) ≤ 1 := by
      refine (sum_le_sum fun C₂ _ => mul_le_of_le_one_right (hlaw₂.nonneg C₂) ?_).trans
        hlaw₂.sum_eq_one.le
      split_ifs <;> norm_num
    by_cases h3 : zipSeq (zipSeq (fstSeq ω) u₁) (sndSeq ω) ∈ T₁
    · by_cases h4 : sndSeq ω ∈ Tp₂
      · simp only [h3, h4, ite_true, add_zero]
        exact sum_codebook_markov_le hP h₁ h₂ hε hε1 hε₂ hn l₂ h3 (hlow₂ _ h4)
      · simp only [h3, h4, ite_true, ite_false, add_zero]
        linarith
    · simp only [h3, ite_false]
      have : (0 : ℝ) ≤ if sndSeq ω ∈ Tp₂ then (0 : ℝ) else 1 := by split_ifs <;> norm_num
      linarith
  -- The sum over `ω`, for the term of encoder 1.
  have hω₁ : ∀ C₁ : Fin L₁ → Fin n → υ₁, ∑ ω, iidPMF P n ω *
      (if zipSeq (zipSeq (fstSeq ω) (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))) (sndSeq ω) ∈ T₁
        then (0 : ℝ) else 1) ≤
      ∑ x₁, iidPMF (margFst P) n x₁ *
        ((if ∀ l, C₁ l ∉ A₁ x₁ then 1 else 0) + condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n) :=
    fun C₁ => by
      rw [← sum_jointIid P n fun ω =>
        if zipSeq (zipSeq (fstSeq ω) (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))) (sndSeq ω) ∈ T₁
          then (0 : ℝ) else 1, Fintype.sum_prod_type]
      refine sum_le_sum fun x₁ _ => ?_
      have e : ∀ x₂, jointIid P n (x₁, x₂) * (if zipSeq (zipSeq (fstSeq (zipSeq x₁ x₂))
          (C₁ (firstIn (A₁ (fstSeq (zipSeq x₁ x₂))) C₁ l₁))) (sndSeq (zipSeq x₁ x₂)) ∈ T₁
          then (0 : ℝ) else 1) = iidPMF (margFst P) n x₁ * (channelExt W n x₁ x₂ *
          (if zipSeq (zipSeq x₁ (C₁ (firstIn (A₁ x₁) C₁ l₁))) x₂ ∈ T₁ then 0 else 1)) :=
        fun x₂ => by
          change iidPMF P n (zipSeq x₁ x₂) * _ = _
          rw [iidPMF_zip_eq hPW]
          have e1 : fstSeq (zipSeq x₁ x₂) = x₁ := rfl
          have e2 : sndSeq (zipSeq x₁ x₂) = x₂ := rfl
          rw [e1, e2]
          ring
      simp only [e, ← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_codebook_cond_le hP h₁ hW hPW hε₁₂ hn l₁ x₁ C₁)
        (hp₁.nonneg x₁)
  have hmiss : ∀ x₁, ∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ *
      (if ∀ l, C₁ l ∉ A₁ x₁ then (1 : ℝ) else 0) ≤ if x₁ ∈ Tp₁ then e₁ else 1 := fun x₁ => by
    split_ifs with hx
    · refine le_trans (le_of_eq ?_) ((sum_iidPMF_ite_forall_not_mem_le
        (iidPMF_isPMF (hJ₁.dist Prod.snd) n) L₁ (A₁ x₁)).trans (exp_le_exp.2 (neg_le_neg
          (mul_le_mul_of_nonneg_left (hlow₁ x₁ hx) (Nat.cast_nonneg L₁)))))
      exact sum_congr rfl fun C _ => by congr
    · refine (sum_le_sum fun C₁ _ => mul_le_of_le_one_right (hlaw₁.nonneg C₁) ?_).trans
        hlaw₁.sum_eq_one.le
      split_ifs <;> norm_num
  have he₁0 : 0 ≤ e₁ := (exp_pos _).le
  -- The term of encoder 1.
  have hterm₁ : ∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ * ∑ ω, iidPMF P n ω *
      (if zipSeq (zipSeq (fstSeq ω) (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))) (sndSeq ω) ∈ T₁
        then (0 : ℝ) else 1) ≤
      (1 - prob (iidPMF (margFst P) n) Tp₁) + e₁ +
        condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n := by
    calc _ ≤ ∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ * ∑ x₁, iidPMF (margFst P) n x₁ *
          ((if ∀ l, C₁ l ∉ A₁ x₁ then 1 else 0) + condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n) :=
          sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left (hω₁ C₁) (hlaw₁.nonneg C₁)
      _ = ∑ x₁, iidPMF (margFst P) n x₁ * (∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ *
            (if ∀ l, C₁ l ∉ A₁ x₁ then 1 else 0) +
            condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n) := by
          have e1 : ∀ x₁, ∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ *
              ((if ∀ l, C₁ l ∉ A₁ x₁ then 1 else 0) +
                condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n) =
              ∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ * (if ∀ l, C₁ l ∉ A₁ x₁ then 1 else 0) +
                condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n := fun x₁ => by
            simp only [mul_add, sum_add_distrib, ← sum_mul, hlaw₁.sum_eq_one, one_mul]
          simp only [← e1]
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun x₁ _ => sum_congr rfl fun C₁ _ => by ring
      _ ≤ ∑ x₁, iidPMF (margFst P) n x₁ * ((if x₁ ∈ Tp₁ then e₁ else 1) +
            condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n) :=
          sum_le_sum fun x₁ _ => mul_le_mul_of_nonneg_left (add_le_add (hmiss x₁) le_rfl)
            (hp₁.nonneg x₁)
      _ ≤ _ := by
          have h3 : ∑ x₁, iidPMF (margFst P) n x₁ * (if x₁ ∈ Tp₁ then e₁ else 1) ≤
              (1 - prob (iidPMF (margFst P) n) Tp₁) + e₁ :=
            le_trans (le_of_eq (sum_congr rfl fun y _ => by congr)) (sum_mul_ite_le hp₁ Tp₁ he₁0)
          rw [show ∑ x₁, iidPMF (margFst P) n x₁ * ((if x₁ ∈ Tp₁ then e₁ else 1) +
              condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n) =
              ∑ x₁, iidPMF (margFst P) n x₁ * (if x₁ ∈ Tp₁ then e₁ else 1) +
                condTypicalityConst (btQ₃ P κ₁) ε₂ ε₁ / n from by
            simp only [mul_add, sum_add_distrib, ← sum_mul, hp₁.sum_eq_one, one_mul]]
          linarith
  -- The term of the second source.
  have hterm₂ : ∑ ω, iidPMF P n ω * (if sndSeq ω ∈ Tp₂ then (0 : ℝ) else 1) =
      1 - prob (iidPMF (margSnd P) n) Tp₂ := by
    have e1 : ∑ ω, iidPMF P n ω * (if sndSeq ω ∈ Tp₂ then (0 : ℝ) else 1) =
        ∑ y, iidPMF (margSnd P) n y * (if y ∈ Tp₂ then (0 : ℝ) else 1) := by
      rw [← sum_jointIid P n fun ω => if sndSeq ω ∈ Tp₂ then (0 : ℝ) else 1]
      exact sum_jointIid_snd P n fun y => if y ∈ Tp₂ then (0 : ℝ) else 1
    rw [e1]
    exact Eq.trans (sum_congr rfl fun y _ => by congr) (sum_mul_ite_zero_one hp₂ Tp₂)
  -- All the terms.
  have hC₁ : ∀ C₁ : Fin L₁ → Fin n → υ₁,
      ∑ C₂ : Fin L₂ → Fin n → υ₂, law₂ C₂ * ∑ ω, iidPMF P n ω *
        (if btSeq ω (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))
          (C₂ (firstIn (A₂ (sndSeq ω)) C₂ l₂)) ∈ T then 0 else 1) ≤
      η + ∑ ω, iidPMF P n ω * (if zipSeq (zipSeq (fstSeq ω)
          (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))) (sndSeq ω) ∈ T₁ then (0 : ℝ) else 1) +
        (1 - prob (iidPMF (margSnd P) n) Tp₂) := fun C₁ => by
    have e1 : ∑ C₂ : Fin L₂ → Fin n → υ₂, law₂ C₂ * ∑ ω, iidPMF P n ω *
        (if btSeq ω (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))
          (C₂ (firstIn (A₂ (sndSeq ω)) C₂ l₂)) ∈ T then (0 : ℝ) else 1) =
        ∑ ω, iidPMF P n ω * ∑ C₂ : Fin L₂ → Fin n → υ₂, law₂ C₂ *
          (if btSeq ω (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))
            (C₂ (firstIn (A₂ (sndSeq ω)) C₂ l₂)) ∈ T then (0 : ℝ) else 1) := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun ω _ => sum_congr rfl fun C₂ _ => by ring
    rw [e1, ← hterm₂]
    calc _ ≤ ∑ ω, iidPMF P n ω * (η + (if zipSeq (zipSeq (fstSeq ω)
          (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))) (sndSeq ω) ∈ T₁ then 0 else 1) +
          (if sndSeq ω ∈ Tp₂ then 0 else 1)) :=
          sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hstep ω _) (hμ.nonneg ω)
      _ = _ := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul]
  calc _ ≤ ∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ * (η + ∑ ω, iidPMF P n ω *
        (if zipSeq (zipSeq (fstSeq ω) (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))) (sndSeq ω) ∈ T₁
          then (0 : ℝ) else 1) + (1 - prob (iidPMF (margSnd P) n) Tp₂)) :=
        sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left (hC₁ C₁) (hlaw₁.nonneg C₁)
    _ = η + ∑ C₁ : Fin L₁ → Fin n → υ₁, law₁ C₁ * ∑ ω, iidPMF P n ω *
        (if zipSeq (zipSeq (fstSeq ω) (C₁ (firstIn (A₁ (fstSeq ω)) C₁ l₁))) (sndSeq ω) ∈ T₁
          then (0 : ℝ) else 1) + (1 - prob (iidPMF (margSnd P) n) Tp₂) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hlaw₁.sum_eq_one, one_mul]
    _ ≤ _ := by
        simp only [btCoverBound]
        linarith

end Two

end InfoTheory
