/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Capacity
public import InfoTheoryLib.Probability.IID

/-!
# Rate distortion codes and the information rate distortion function

A source `X ∼ p(x)` on a finite alphabet `𝒳` is described with the reproduction alphabet `𝒳̂`, and
a distortion measure `d : 𝒳 × 𝒳̂ → ℝ₊` is the cost of representing `x` by `x̂`. A `(M, n)` rate
distortion code describes `Xⁿ` by an index `f(Xⁿ) ∈ {0, …, M - 1}` and reproduces it as
`X̂ⁿ = g(f(Xⁿ))`; its distortion is `E d(Xⁿ, X̂ⁿ)`. The information rate distortion function is

  `R(D) = min_{p(x̂|x) : E d(X, X̂) ≤ D} I(X; X̂)`.

It is nonincreasing and convex in `D` (Lemma 10.4.1), and its epigraph is closed.

## Main definitions

* `hammingDistortion`, `maxDistortion`, `seqDistortion`: the Hamming distortion (10.4), the bound
  `d_max` (10.3) and the distortion between sequences (10.6).
* `expDistortion p q d`: the expected distortion `∑ p(x) q(x̂|x) d(x, x̂)` of a test channel `q`.
* `minDistortion p d`: the least distortion `∑ₓ p(x) min_x̂ d(x, x̂)` of any test channel.
* `RDCode M n α β`: a `(M, n)` rate distortion code (10.7)–(10.8), and `RDCode.distortion` (10.10).
* `IsAchievableRD`, `rdRegion`, `rateDistortion`, `distortionRate`: achievable pairs, the rate
  distortion region, the rate distortion function and the distortion rate function.
* `infoRD p d D`: the information rate distortion function `R^(I)(D)` (10.11).

## Main statements

* `exists_infoRD_eq`: the infimum in (10.11) is a minimum.
* `infoRD_antitoneOn`, `infoRD_convexOn`: **Lemma 10.4.1**.
* `infoRD_le_of_tendsto`: if `R^(I)(Dₖ) ≤ Rₖ`, `Dₖ → D` and `Rₖ → R`, then `R^(I)(D) ≤ R`.
* `infoRD_le_mutualInfo`: any pair `(X, X̂)` with `X ∼ p` has `I(X; X̂) ≥ R^(I)(E d(X, X̂))`.

## Implementation notes

Rates are in nats. A code with rate `R` has `⌊e^{nR}⌋` codewords, the largest number allowed by
the book's `(2^{nR}, n)` codes with `R` in bits; there is no such code for `R < 0`. The pair
`(R, D)` is achievable if a sequence of such codes has `limsup E d(Xⁿ, X̂ⁿ) ≤ D`, stated as
`E d(Xⁿ, X̂ⁿ) ≤ D + ε` eventually, for every `ε > 0`.

The set of test channels with `E d ≤ D` is empty for `D < D_min = minDistortion p d`, and the
infimum `R^(I)(D)` is then `0` by convention. The properties of `R^(I)` are stated for
`D ≥ D_min`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 10.2
  and 10.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Distortion measures -/

open Classical in
/-- **Definition (10.4).** The Hamming (probability of error) distortion: `0` if `x = x̂` and `1`
otherwise. -/
def hammingDistortion (x x' : α) : ℝ := if x = x' then 0 else 1

/-- **Definition (10.3).** The maximum `d_max = max_{x, x̂} d(x, x̂)` of a distortion measure, which
is finite for finite alphabets. -/
def maxDistortion (d : α → β → ℝ) : ℝ := ⨆ z : α × β, d z.1 z.2

omit [Fintype α] [Fintype β] in
lemma le_maxDistortion [Finite α] [Finite β] (d : α → β → ℝ) (x : α) (y : β) :
    d x y ≤ maxDistortion d :=
  le_ciSup (f := fun z : α × β => d z.1 z.2) (Set.finite_range _).bddAbove (x, y)

omit [Fintype α] [Fintype β] in
lemma maxDistortion_nonneg [Finite α] [Finite β] [Nonempty α] [Nonempty β] {d : α → β → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) :
    0 ≤ maxDistortion d :=
  (hd (Classical.arbitrary α) (Classical.arbitrary β)).trans (le_maxDistortion d _ _)

omit [Fintype α] [Fintype β] in
/-- **Definition (10.6).** The distortion `d(xⁿ, x̂ⁿ) = (1/n) ∑ᵢ d(xᵢ, x̂ᵢ)` between sequences. -/
def seqDistortion (d : α → β → ℝ) {n : ℕ} (x : Fin n → α) (y : Fin n → β) : ℝ :=
  (∑ i, d (x i) (y i)) / n

omit [Fintype α] [Fintype β] in
lemma seqDistortion_nonneg {d : α → β → ℝ} (hd : ∀ x y, 0 ≤ d x y) {n : ℕ} (x : Fin n → α)
    (y : Fin n → β) : 0 ≤ seqDistortion d x y :=
  div_nonneg (sum_nonneg fun _ _ => hd _ _) (Nat.cast_nonneg n)

omit [Fintype α] [Fintype β] in
lemma seqDistortion_le_maxDistortion [Finite α] [Finite β] (d : α → β → ℝ) {n : ℕ} (hn : 0 < n)
    (x : Fin n → α) (y : Fin n → β) : seqDistortion d x y ≤ maxDistortion d := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [seqDistortion, div_le_iff₀ hn']
  calc ∑ i, d (x i) (y i) ≤ ∑ _i : Fin n, maxDistortion d :=
        sum_le_sum fun i _ => le_maxDistortion d _ _
    _ = maxDistortion d * n := by simp [mul_comm]

/-- The expected distortion `E d(X, X̂) = ∑_{x, x̂} p(x) q(x̂|x) d(x, x̂)` of the test channel
`q(x̂|x)`. -/
def expDistortion (p : α → ℝ) (q : α → β → ℝ) (d : α → β → ℝ) : ℝ :=
  ∑ x, ∑ y, p x * q x y * d x y

lemma expDistortion_eq_sum_jointOf (p : α → ℝ) (q : α → β → ℝ) (d : α → β → ℝ) :
    expDistortion p q d = ∑ z, jointOf p q z * d z.1 z.2 := by
  rw [expDistortion, Fintype.sum_prod_type]
  rfl

lemma continuous_expDistortion (p : α → ℝ) (d : α → β → ℝ) :
    Continuous fun q : α → β → ℝ => expDistortion p q d := by
  unfold expDistortion
  fun_prop

/-- The least expected distortion `D_min = ∑ₓ p(x) min_x̂ d(x, x̂)` of a test channel. -/
def minDistortion (p : α → ℝ) (d : α → β → ℝ) : ℝ := ∑ x, p x * ⨅ y, d x y

omit [Fintype α] [Fintype β] in
lemma ciInf_le_distortion [Finite β] (d : α → β → ℝ) (x : α) (y : β) : ⨅ y', d x y' ≤ d x y :=
  ciInf_le (Set.finite_range _).bddBelow y

lemma minDistortion_le_expDistortion {p : α → ℝ} (hp : IsPMF p) {q : α → β → ℝ}
    (hq : IsChannel q) (d : α → β → ℝ) : minDistortion p d ≤ expDistortion p q d := by
  refine sum_le_sum fun x _ => ?_
  calc p x * ⨅ y, d x y = ∑ y, p x * q x y * ⨅ y', d x y' := by
        rw [← sum_mul, ← mul_sum, (hq x).sum_eq_one, mul_one]
    _ ≤ ∑ y, p x * q x y * d x y := sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (ciInf_le_distortion d x y)
          (mul_nonneg (hp.nonneg x) ((hq x).nonneg y))

open Classical in
/-- The deterministic test channel `x ↦ f(x)`. -/
def detChannel (f : α → β) (x : α) (y : β) : ℝ := if f x = y then 1 else 0

omit [Fintype α] in
lemma detChannel_isChannel (f : α → β) : IsChannel (detChannel f) := fun x => by
  classical
  refine ⟨fun y => by unfold detChannel; split_ifs <;> norm_num, ?_⟩
  simp [detChannel]

lemma expDistortion_detChannel (p : α → ℝ) (f : α → β) (d : α → β → ℝ) :
    expDistortion p (detChannel f) d = ∑ x, p x * d x (f x) := by
  classical
  refine sum_congr rfl fun x _ => ?_
  simp [detChannel, mul_ite]

/-- A deterministic test channel mapping each `x` to a closest `x̂` attains `D_min`. -/
lemma exists_expDistortion_eq_minDistortion [Nonempty β] (p : α → ℝ) (d : α → β → ℝ) :
    ∃ q : α → β → ℝ, IsChannel q ∧ expDistortion p q d = minDistortion p d := by
  choose f hf using fun x => exists_eq_ciInf_of_finite (f := fun y => d x y)
  refine ⟨detChannel f, detChannel_isChannel f, ?_⟩
  rw [expDistortion_detChannel, minDistortion]
  simp only [hf]

/-! ### Rate distortion codes -/

/-- **Definition (10.7)–(10.8).** A `(M, n)` rate distortion code: an encoding function `enc`
mapping each source sequence to an index in `{0, …, M - 1}`, and a decoding (reproduction)
function `dec` mapping each index to a reproduction sequence. -/
structure RDCode (M n : ℕ) (α β : Type*) where
  /-- The encoding function `fₙ : 𝒳ⁿ → {0, …, M - 1}`. -/
  enc : (Fin n → α) → Fin M
  /-- The decoding function `gₙ : {0, …, M - 1} → 𝒳̂ⁿ`; its values form the codebook. -/
  dec : Fin M → Fin n → β

/-- **Definition (10.9)–(10.10).** The distortion `D = E d(Xⁿ, gₙ(fₙ(Xⁿ)))` of a rate distortion
code for an i.i.d. source `Xᵢ ∼ p`. -/
def RDCode.distortion {M n : ℕ} (p : α → ℝ) (d : α → β → ℝ) (c : RDCode M n α β) : ℝ :=
  ∑ x, iidPMF p n x * seqDistortion d x (c.dec (c.enc x))

/-- **Definition (Section 10.2).** A rate distortion pair `(R, D)` (with `R` in nats) is achievable
if there is a sequence of `(⌊e^{nR}⌋, n)` rate distortion codes with
`limsup E d(Xⁿ, gₙ(fₙ(Xⁿ))) ≤ D`. -/
def IsAchievableRD (p : α → ℝ) (d : α → β → ℝ) (R D : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, RDCode ⌊exp (n * R)⌋₊ n α β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion p d ≤ D + ε

/-- **Definition (Section 10.2).** The rate distortion region: the closure of the set of
achievable pairs `(R, D)`. -/
def rdRegion (p : α → ℝ) (d : α → β → ℝ) : Set (ℝ × ℝ) :=
  closure {z | IsAchievableRD p d z.1 z.2}

/-- **Definition (Section 10.2).** The rate distortion function `R(D)`: the infimum of the rates
`R` such that `(R, D)` is in the rate distortion region. -/
def rateDistortion (p : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | (R, D) ∈ rdRegion p d}

/-- **Definition (Section 10.2).** The distortion rate function `D(R)`: the infimum of the
distortions `D` such that `(R, D)` is in the rate distortion region. -/
def distortionRate (p : α → ℝ) (d : α → β → ℝ) (R : ℝ) : ℝ :=
  sInf {D | (R, D) ∈ rdRegion p d}

/-! ### The information rate distortion function -/

/-- **Definition (10.11).** The information rate distortion function
`R^(I)(D) = min_{p(x̂|x) : E d(X, X̂) ≤ D} I(X; X̂)`. -/
def infoRD (p : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {I | ∃ q : α → β → ℝ, IsChannel q ∧ expDistortion p q d ≤ D ∧ mutualInfoOf p q = I}

variable {p : α → ℝ} {d : α → β → ℝ}

lemma infoRD_set_nonempty [Nonempty β] {D : ℝ} (hD : minDistortion p d ≤ D) :
    {I | ∃ q : α → β → ℝ, IsChannel q ∧ expDistortion p q d ≤ D ∧ mutualInfoOf p q = I}.Nonempty :=
  let ⟨q, hq, he⟩ := exists_expDistortion_eq_minDistortion p d
  ⟨_, q, hq, he.le.trans hD, rfl⟩

lemma infoRD_set_bddBelow (hp : IsPMF p) (D : ℝ) :
    BddBelow {I | ∃ q : α → β → ℝ, IsChannel q ∧ expDistortion p q d ≤ D ∧
      mutualInfoOf p q = I} :=
  ⟨0, fun _ ⟨_, hq, _, h⟩ => h ▸ mutualInfoOf_nonneg hp hq⟩

/-- `R^(I)(D) ≤ I(X; X̂)` for every test channel with `E d(X, X̂) ≤ D`. -/
lemma infoRD_le (hp : IsPMF p) {q : α → β → ℝ} (hq : IsChannel q) {D : ℝ}
    (hD : expDistortion p q d ≤ D) : infoRD p d D ≤ mutualInfoOf p q :=
  csInf_le (infoRD_set_bddBelow hp D) ⟨q, hq, hD, rfl⟩

lemma infoRD_nonneg (hp : IsPMF p) (D : ℝ) : 0 ≤ infoRD (d := d) p D := by
  by_cases h : {I | ∃ q : α → β → ℝ, IsChannel q ∧ expDistortion p q d ≤ D ∧
      mutualInfoOf p q = I}.Nonempty
  · exact le_csInf h fun _ ⟨_, hq, _, he⟩ => he ▸ mutualInfoOf_nonneg hp hq
  · rw [infoRD, Set.not_nonempty_iff_eq_empty.1 h, Real.sInf_empty]

omit [Fintype α] in
/-- The set of test channels is compact. -/
lemma isCompact_setOf_isChannel : IsCompact {q : α → β → ℝ | IsChannel q} := by
  have : {q : α → β → ℝ | IsChannel q} = Set.univ.pi fun _ => {r : β → ℝ | IsPMF r} := by
    ext q; simp [IsChannel]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_setOf_isPMF

/-- `I(X; X̂)` is a continuous function of the test channel `p(x̂|x)`. -/
theorem continuousOn_mutualInfoOf_channel (hp : IsPMF p) :
    ContinuousOn (fun q => mutualInfoOf p q) {q : α → β → ℝ | IsChannel q} := by
  have hc : Continuous fun q : α → β → ℝ =>
      ∑ y, negMulLog (∑ x, p x * q x y) - ∑ x, p x * ∑ y, negMulLog (q x y) := by
    refine (continuous_finsetSum _ fun y _ => continuous_negMulLog.comp ?_).sub ?_
    · exact continuous_finsetSum _ fun x _ =>
        continuous_const.mul ((continuous_apply y).comp (continuous_apply x))
    · exact continuous_finsetSum _ fun x _ => continuous_const.mul
        (continuous_finsetSum _ fun y _ =>
          continuous_negMulLog.comp ((continuous_apply y).comp (continuous_apply x)))
  refine hc.continuousOn.congr fun q hq => ?_
  rw [mutualInfoOf_eq_sum hp hq]
  simp only [entropy_eq_sum_negMulLog]

/-- **(10.11)** The infimum defining `R^(I)(D)` is attained: for `D ≥ D_min` some test channel with
`E d(X, X̂) ≤ D` has `I(X; X̂) = R^(I)(D)`. -/
theorem exists_infoRD_eq [Nonempty β] (hp : IsPMF p) {D : ℝ} (hD : minDistortion p d ≤ D) :
    ∃ q : α → β → ℝ, IsChannel q ∧ expDistortion p q d ≤ D ∧ mutualInfoOf p q = infoRD p d D := by
  set S := {q : α → β → ℝ | IsChannel q} ∩ {q | expDistortion p q d ≤ D}
  have hS : IsCompact S :=
    isCompact_setOf_isChannel.inter_right (isClosed_le (continuous_expDistortion p d)
      continuous_const)
  obtain ⟨q₀, hq₀, he₀⟩ := exists_expDistortion_eq_minDistortion p d
  obtain ⟨q, ⟨hq, hqD⟩, hmin⟩ := hS.exists_isMinOn ⟨q₀, hq₀, he₀.le.trans hD⟩
    ((continuousOn_mutualInfoOf_channel hp).mono Set.inter_subset_left)
  refine ⟨q, hq, hqD, le_antisymm ?_ (infoRD_le hp hq hqD)⟩
  exact le_csInf (infoRD_set_nonempty hD) fun _ ⟨q', hq', hD', he⟩ => he ▸ hmin ⟨hq', hD'⟩

/-- **Lemma 10.4.1 (first part).** `R^(I)(D)` is nonincreasing in `D ≥ D_min`: it is the minimum
of `I(X; X̂)` over larger sets as `D` increases. -/
theorem infoRD_antitoneOn [Nonempty β] (hp : IsPMF p) :
    AntitoneOn (infoRD p d) (Set.Ici (minDistortion p d)) := by
  intro D₁ hD₁ D₂ _ h
  obtain ⟨q, hq, hqD, he⟩ := exists_infoRD_eq hp hD₁
  exact he ▸ infoRD_le hp hq (hqD.trans h)

/-- **Lemma 10.4.1 (second part).** `R^(I)(D)` is a convex function of `D ≥ D_min`: mixing the
optimal test channels for `D₁` and `D₂` gives the distortion `λD₁ + (1 - λ)D₂`, and `I(X; X̂)` is
convex in the test channel (Theorem 2.7.4). -/
theorem infoRD_convexOn [Nonempty β] (hp : IsPMF p) :
    ConvexOn ℝ (Set.Ici (minDistortion p d)) (infoRD p d) := by
  refine ⟨convex_Ici _, fun D₁ hD₁ D₂ hD₂ s t hs ht hst => ?_⟩
  obtain ⟨q₁, hq₁, hD₁', he₁⟩ := exists_infoRD_eq hp hD₁
  obtain ⟨q₂, hq₂, hD₂', he₂⟩ := exists_infoRD_eq hp hD₂
  have hmix := hq₁.mix hq₂ hs ht hst
  have hdist : expDistortion p (s • q₁ + t • q₂) d =
      s * expDistortion p q₁ d + t * expDistortion p q₂ d := by
    simp only [expDistortion, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun y _ => by ring
  have hconv := (mutualInfoOf_convex_channel hp).2 hq₁ hq₂ hs ht hst
  simp only [smul_eq_mul] at hconv ⊢
  calc infoRD p d (s * D₁ + t * D₂) ≤ mutualInfoOf p (s • q₁ + t • q₂) := by
        refine infoRD_le hp hmix ?_
        rw [hdist]
        gcongr
    _ ≤ s * mutualInfoOf p q₁ + t * mutualInfoOf p q₂ := hconv
    _ = s * infoRD p d D₁ + t * infoRD p d D₂ := by rw [he₁, he₂]

/-- **Closedness of the epigraph of `R^(I)`.** If `R^(I)(Dₖ) ≤ Rₖ` with `Dₖ ≥ D_min`, `Dₖ → D` and
`Rₖ → R`, then `R^(I)(D) ≤ R`. The optimal test channels for `Dₖ` have a limit point, which is a
test channel for `D`. -/
theorem infoRD_le_of_tendsto [Nonempty β] (hp : IsPMF p) {Dₖ Rₖ : ℕ → ℝ} {D R : ℝ}
    (hDₖ : ∀ k, minDistortion p d ≤ Dₖ k) (hle : ∀ k, infoRD p d (Dₖ k) ≤ Rₖ k)
    (hD : Tendsto Dₖ atTop (𝓝 D)) (hR : Tendsto Rₖ atTop (𝓝 R)) : infoRD p d D ≤ R := by
  choose q hq hqD he using fun k => exists_infoRD_eq hp (hDₖ k)
  obtain ⟨q', hq', φ, hφ, hlim⟩ := isCompact_setOf_isChannel.tendsto_subseq hq
  have hD' : expDistortion p q' d ≤ D :=
    le_of_tendsto_of_tendsto (((continuous_expDistortion p d).tendsto q').comp hlim)
      (hD.comp hφ.tendsto_atTop) (Eventually.of_forall fun k => hqD (φ k))
  have hI : Tendsto (fun k => mutualInfoOf p (q (φ k))) atTop (𝓝 (mutualInfoOf p q')) :=
    ((continuousOn_mutualInfoOf_channel hp).continuousWithinAt hq').tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => hq (φ k)⟩)
  calc infoRD p d D ≤ mutualInfoOf p q' := infoRD_le hp hq' hD'
    _ ≤ R := le_of_tendsto_of_tendsto hI (hR.comp hφ.tendsto_atTop)
        (Eventually.of_forall fun k => (he (φ k)).le.trans (hle (φ k)))

/-- `R^(I)(D) = 0` as soon as a constant reproduction `x̂₀` has `E d(X, x̂₀) ≤ D`. -/
theorem infoRD_eq_zero (hp : IsPMF p) {y₀ : β} {D : ℝ} (hD : ∑ x, p x * d x y₀ ≤ D) :
    infoRD p d D = 0 := by
  refine le_antisymm ?_ (infoRD_nonneg hp D)
  have hq := detChannel_isChannel (fun _ : α => y₀)
  refine (infoRD_le hp hq ((expDistortion_detChannel p _ d).trans_le hD)).trans_eq ?_
  rw [mutualInfoOf, mutualInfo_eq_zero_iff (jointOf_isPMF hp hq)]
  intro a b
  rw [dist_pair_fst_snd, dist_jointOf_fst hq, dist_jointOf_snd]
  simp only [jointOf, outDist, detChannel]
  split_ifs <;> simp [hp.sum_eq_one]

/-! ### Joint laws with a given source marginal -/

section Joint

variable {Ω : Type*} [Fintype Ω]

/-- **(10.67)** Any pair `(X, X̂)` with `X ∼ p` defines a test channel `p(x̂|x)`, hence
`I(X; X̂) ≥ R^(I)(E d(X, X̂))`. -/
theorem infoRD_le_mutualInfo (hp : IsPMF p) {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β}
    (hX : dist μ X = p) : infoRD p d (∑ ω, μ ω * d (X ω) (Y ω)) ≤ I[X : Y ; μ] := by
  classical
  have : Nonempty Ω := by
    obtain ⟨ω, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hμ)
    exact ⟨ω⟩
  let y₀ : β := Y (Classical.arbitrary Ω)
  set J := dist μ (pair X Y)
  have hJ : IsPMF J := hμ.dist _
  have hmarg : marg J = p := by
    funext x
    rw [← hX, ← sum_dist_pair_right μ X Y x]
    rfl
  set q : α → β → ℝ := fun x => if marg J x = 0 then detChannel (fun _ => y₀) x else condPMF J x
  have hq : IsChannel q := fun x => by
    by_cases h : marg J x = 0
    · simp only [q, h, ↓reduceIte]; exact detChannel_isChannel _ x
    · simp only [q, h, ↓reduceIte]; exact condPMF_isPMF hJ.nonneg h
  have hj : jointOf p q = J := by
    funext z
    obtain ⟨x, y⟩ := z
    simp only [jointOf, ← hmarg, q]
    split_ifs with h
    · rw [h, zero_mul]
      exact (le_antisymm (h ▸ le_marg hJ.nonneg x y) (hJ.nonneg _)).symm
    · exact marg_mul_condPMF hJ.nonneg x y
  have hD : expDistortion p q d = ∑ ω, μ ω * d (X ω) (Y ω) := by
    rw [expDistortion_eq_sum_jointOf, hj]
    exact sum_dist_mul μ (pair X Y) fun z => d z.1 z.2
  have hI : mutualInfoOf p q = I[X : Y ; μ] := by
    rw [mutualInfoOf, hj]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
  exact hI ▸ infoRD_le hp hq hD.le

end Joint

end InfoTheory
