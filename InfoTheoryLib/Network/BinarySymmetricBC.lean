/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCBits
public import InfoTheoryLib.Entropy.MrsGerber
public import InfoTheoryLib.ChannelCoding.Converse
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The binary symmetric broadcast channel

The binary symmetric broadcast channel (BS-BC) has conditional marginals `BSC(p₁)` and `BSC(p₂)`,
with `p₁ ≤ p₂ ≤ 1/2`. This file shows that it is degraded, computes the region
`R₁ ≤ I(X; Y₁ | U)`, `R₂ ≤ I(U; Y₂)` of the degraded DM-BC for it, and compares this region with
time division.

## Main definitions

* `bsbcBSC p`: the transition matrix of `BSC(p)`.
* `bsbcNoise₂ p₁ p₂`: the crossover probability `p̃₂ = (p₂ - p₁) / (1 - 2 p₁)`, with
  `p₁ ∗ p̃₂ = p₂`.
* `bsbcDegraded p₁ p₂`, `bsbcIndep p₁ p₂`: the physically degraded BS-BC `X → Y₁ → Y₂`, and the
  BS-BC with independent noises.
* `bsbcDSBS a`: the law of `(U, X) ∼ DSBS(a)`.
* `bsbcSuperpositionRegion p₁ p₂`, `bsbcTimeDivisionRegion p₁ p₂`: the superposition coding and
  time-division inner bounds of the BS-BC, in bits.

## Main statements

* `isStochasticallyDegraded_of_bsbc`: the BS-BC is degraded.
* `bsbc_not_forall_binConv_mul`: the formula `p̃₂ = (p₂ - p₁)(1 - 2 p₁)` of the notes is a typo.
* `bsbc_mrsGerber_le`: Mrs. Gerber's lemma for the BS-BC, `H(Y₂ | U) ≥ H(H⁻¹(H(Y₁ | U)) ∗ p̃₂)`.
* `degradedBCRegionBits_bsbc`: **the Proposition of Lecture 5**, the region of the degraded DM-BC
  is `R₁ ≤ H(a ∗ p₁) - H(p₁)`, `R₂ ≤ 1 - H(a ∗ p₂)` for some `a ∈ [0, 1/2]`.
* `isClosed_bsbcSuperpositionRegion`: this region is closed.
* `bsbcTimeDivisionRegion_subset`, `bsbcTimeDivisionRegion_ssubset`: superposition coding contains
  time division, strictly for `p₁ = 0` and `p₂ = 1/4`.

## Implementation notes

The statements hold for any channel with the marginals `BSC(p₁)` and `BSC(p₂)`, so there is no need
to reduce to the physically degraded channel. For the same reason `bsbc_mrsGerber_le` is proved by
the convexity of `v ↦ H(H⁻¹(v) ∗ p̃₂)` from the conditional laws of `Y₁` and `Y₂` given `U`, rather
than by applying `mrsGerber_le_condEntropy_xor` on a probability space carrying `Z̃₂`.

The hypotheses `0 ≤ p₁ ≤ p₂ ≤ 1/2` are weaker than the `p₁ < p₂ < 1/2` of the notes. For
`p₁ = p₂ = 1/2`, Lean's `0 / 0 = 0` gives `bsbcNoise₂ p₁ p₂ = 0`, which is still a valid choice.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The binary symmetric channel and the BS-BC -/

/-- The transition matrix `p(y | x)` of the binary symmetric channel `BSC(p)`: the input is
flipped with probability `p`. -/
def bsbcBSC (p : ℝ) : Bool → Bool → ℝ := fun x y => if x = y then 1 - p else p

lemma bsbcBSC_isChannel {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsChannel (bsbcBSC p) :=
  fun x => ⟨fun y => by unfold bsbcBSC; split_ifs <;> linarith, by
    cases x <;> simp [bsbcBSC]⟩

lemma bsbcBSC_true (p : ℝ) (x : Bool) :
    bsbcBSC p x true = if x then 1 - p else p := by
  cases x <;> simp [bsbcBSC]

/-- The entropy of a row of `BSC(p)` is `H(p)`. -/
lemma entropy_bsbcBSC {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Bool) :
    entropy (bsbcBSC p x) = binEntropy p := by
  rw [entropy_bool (bsbcBSC_isChannel h0 h1 x), bsbcBSC_true]
  cases x <;> simp [binEntropy_one_sub]

/-- `(a ∗ p) ∗ p' = a ∗ (p ∗ p')`: the binary convolution is associative. -/
lemma bsbc_binConv_assoc (a p p' : ℝ) : binConv (binConv a p) p' = binConv a (binConv p p') := by
  unfold binConv; ring

/-- `BSC(p) ∘ BSC(p') = BSC(p ∗ p')`: the cascade of two binary symmetric channels. -/
lemma sum_bsbcBSC_mul (p p' : ℝ) (x y : Bool) :
    ∑ z, bsbcBSC p x z * bsbcBSC p' z y = bsbcBSC (binConv p p') x y := by
  cases x <;> cases y <;> simp [bsbcBSC, binConv] <;> ring

/-- The crossover probability `p̃₂ = (p₂ - p₁) / (1 - 2 p₁)` of the channel `BSC(p̃₂)` from `Y₁`
to `Y₂` that makes the BS-BC physically degraded: `p₁ ∗ p̃₂ = p₂`. -/
def bsbcNoise₂ (p₁ p₂ : ℝ) : ℝ := (p₂ - p₁) / (1 - 2 * p₁)

variable {p₁ p₂ : ℝ}

lemma bsbcNoise₂_mem (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) : bsbcNoise₂ p₁ p₂ ∈ Set.Icc 0 2⁻¹ := by
  unfold bsbcNoise₂
  rcases (show 0 ≤ 1 - 2 * p₁ by linarith).eq_or_lt with h | h
  · rw [← h, div_zero]; norm_num
  · exact ⟨div_nonneg (by linarith) h.le, (div_le_iff₀ h).2 (by linarith)⟩

/-- `p₁ ∗ p̃₂ = p₂`. -/
lemma binConv_bsbcNoise₂ (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    binConv p₁ (bsbcNoise₂ p₁ p₂) = p₂ := by
  have e : binConv p₁ (bsbcNoise₂ p₁ p₂) = p₁ + (1 - 2 * p₁) * bsbcNoise₂ p₁ p₂ := by
    unfold binConv; ring
  rw [e]
  unfold bsbcNoise₂
  rcases (show 0 ≤ 1 - 2 * p₁ by linarith).eq_or_lt with h | h
  · rw [← h]; simp; linarith
  · rw [mul_div_cancel₀ _ h.ne']; ring

/-- The physically degraded BS-BC `X → Y₁ → Y₂` (page 5-21 of the notes): `Y₁ = X ⊕ Z₁` and
`Y₂ = Y₁ ⊕ Z̃₂`, with `Z₁ ∼ Bern(p₁)` and `Z̃₂ ∼ Bern(p̃₂)` independent. -/
def bsbcDegraded (p₁ p₂ : ℝ) : Bool → Bool × Bool → ℝ :=
  fun x y => bsbcBSC p₁ x y.1 * bsbcBSC (bsbcNoise₂ p₁ p₂) y.1 y.2

/-- The BS-BC with independent noises (page 5-8 of the notes): `Y₁ = X ⊕ Z₁` and `Y₂ = X ⊕ Z₂`,
with `Z₁ ∼ Bern(p₁)` and `Z₂ ∼ Bern(p₂)` independent. -/
def bsbcIndep (p₁ p₂ : ℝ) : Bool → Bool × Bool → ℝ :=
  fun x y => bsbcBSC p₁ x y.1 * bsbcBSC p₂ x y.2

lemma bsbcIndep_isChannel (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    IsChannel (bsbcIndep p₁ p₂) := fun x =>
  ⟨fun y => mul_nonneg ((bsbcBSC_isChannel hp₁ hp₁' x).nonneg _)
    ((bsbcBSC_isChannel hp₂ hp₂' x).nonneg _), by
    simp only [bsbcIndep, Fintype.sum_prod_type, ← mul_sum,
      (bsbcBSC_isChannel hp₂ hp₂' x).sum_eq_one, mul_one,
      (bsbcBSC_isChannel hp₁ hp₁' x).sum_eq_one]⟩

lemma bsbcDegraded_isChannel (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    IsChannel (bsbcDegraded p₁ p₂) := by
  have hn := bsbcNoise₂_mem hp₁₂ hp₂
  have hV := bsbcBSC_isChannel hn.1 (hn.2.trans (by norm_num))
  have hW₁ := bsbcBSC_isChannel hp₁ (by linarith)
  exact fun x => ⟨fun y => mul_nonneg ((hW₁ x).nonneg _) ((hV _).nonneg _), by
    simp only [bsbcDegraded, Fintype.sum_prod_type, ← mul_sum, (hV _).sum_eq_one, mul_one,
      (hW₁ x).sum_eq_one]⟩

lemma bcMarg₁_bsbcIndep (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    bcMarg₁ (bsbcIndep p₁ p₂) = bsbcBSC p₁ := by
  funext x y
  simp only [bcMarg₁, bsbcIndep, ← mul_sum, (bsbcBSC_isChannel hp₂ hp₂' x).sum_eq_one, mul_one]

lemma bcMarg₂_bsbcIndep (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) :
    bcMarg₂ (bsbcIndep p₁ p₂) = bsbcBSC p₂ := by
  funext x y
  simp only [bcMarg₂, bsbcIndep, ← sum_mul, (bsbcBSC_isChannel hp₁ hp₁' x).sum_eq_one, one_mul]

lemma bcMarg₁_bsbcDegraded : bcMarg₁ (bsbcDegraded p₁ p₂) = bsbcBSC p₁ := by
  funext x y
  have : ∑ y₂, bsbcBSC (bsbcNoise₂ p₁ p₂) y y₂ = 1 := by cases y <;> simp [bsbcBSC]
  simp only [bcMarg₁, bsbcDegraded, ← mul_sum, this, mul_one]

lemma bcMarg₂_bsbcDegraded (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    bcMarg₂ (bsbcDegraded p₁ p₂) = bsbcBSC p₂ := by
  funext x y
  simp only [bcMarg₂, bsbcDegraded, sum_bsbcBSC_mul, binConv_bsbcNoise₂ hp₁₂ hp₂]

/-- The BS-BC `X → Y₁ → Y₂` of `bsbcDegraded` is physically degraded. -/
theorem isPhysicallyDegraded_bsbcDegraded (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    IsPhysicallyDegraded (bsbcDegraded p₁ p₂) := by
  have hn := bsbcNoise₂_mem hp₁₂ hp₂
  exact ⟨bsbcBSC p₁, bsbcBSC (bsbcNoise₂ p₁ p₂), bsbcBSC_isChannel hp₁ (by linarith),
    bsbcBSC_isChannel hn.1 (hn.2.trans (by norm_num)), fun _ _ _ => rfl⟩

/-- **Example (Lecture 5 of [elgamal2010], page 5-21).** The BS-BC is degraded: a broadcast channel
whose conditional marginals are `BSC(p₁)` and `BSC(p₂)` with `p₁ ≤ p₂ ≤ 1/2` is stochastically
degraded, `Y₂` being the output of `BSC(p̃₂)` with input `Y₁`, where `p̃₂ = (p₂ - p₁)/(1 - 2p₁)`
satisfies `p₁ ∗ p̃₂ = p₂`. (The notes write `p̃₂ = (p₂ - p₁)(1 - 2p₁)`, see
`bsbc_not_forall_binConv_mul`.) -/
theorem isStochasticallyDegraded_of_bsbc {W : Bool → Bool × Bool → ℝ}
    (h₁ : bcMarg₁ W = bsbcBSC p₁) (h₂ : bcMarg₂ W = bsbcBSC p₂) (hp₁₂ : p₁ ≤ p₂)
    (hp₂ : p₂ ≤ 1 / 2) : IsStochasticallyDegraded W := by
  have hn := bsbcNoise₂_mem hp₁₂ hp₂
  refine ⟨bsbcBSC (bsbcNoise₂ p₁ p₂), bsbcBSC_isChannel hn.1 (hn.2.trans (by norm_num)),
    fun x y₂ => ?_⟩
  rw [h₁, h₂, sum_bsbcBSC_mul, binConv_bsbcNoise₂ hp₁₂ hp₂]

/-- The formula `p̃₂ = (p₂ - p₁)(1 - 2p₁)` of the notes (page 5-21) is a typo: for `p₁ = 1/4` and
`p₂ = 3/8` it gives `p₁ ∗ p̃₂ = 9/32 ≠ p₂`. The right value is `bsbcNoise₂ p₁ p₂`. -/
lemma bsbc_not_forall_binConv_mul :
    ¬ ∀ p₁ p₂ : ℝ, 0 ≤ p₁ → p₁ < p₂ → p₂ < 1 / 2 → binConv p₁ ((p₂ - p₁) * (1 - 2 * p₁)) = p₂ :=
  fun h => by
    have := h (1 / 4) (3 / 8) (by norm_num) (by norm_num) (by norm_num)
    norm_num [binConv] at this

/-! ### Information quantities of the BS-BC -/

/-- If, given `U = u`, the law of the binary `Y` is the output of `BSC(p)` for the input law
`r(u, ·) / (r(u, 0) + r(u, 1))`, then `H(Y | U) = ∑ᵤ p(u) H(a_u ∗ p)` with
`a_u = r(u, 1) / (r(u, 0) + r(u, 1))`. -/
lemma bsbc_condEntropy_eq {Ω α : Type*} [Fintype Ω] [Fintype α] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (U : Ω → α) (Y : Ω → Bool) (r : α × Bool → ℝ) {p : ℝ}
    (hU : ∀ u, dist μ U u = r (u, false) + r (u, true))
    (hUY : ∀ u, dist μ (pair U Y) (u, true) = r (u, false) * p + r (u, true) * (1 - p)) :
    H[Y | U ; μ] = ∑ u, (r (u, false) + r (u, true)) *
      binEntropy (binConv (r (u, true) / (r (u, false) + r (u, true))) p) := by
  unfold condEntropy
  refine sum_congr rfl fun u _ => ?_
  rw [hU]
  by_cases hs : r (u, false) + r (u, true) = 0
  · rw [hs, zero_mul, zero_mul]
  · congr 1
    rw [condEntropyAt, entropy_bool (condDist_isPMF hμ Y U (by rw [hU]; exact hs)), condDist,
      hUY, hU]
    congr 1
    unfold binConv
    field_simp
    ring

section Info

variable {𝒰 : Type*} [Fintype 𝒰] {q : 𝒰 × Bool → ℝ} {W : Bool → Bool × Bool → ℝ}

lemma bsbc_dist_U (hW : IsChannel W) (u : 𝒰) :
    dist (bcJoint q W) (fun z : (𝒰 × Bool) × (Bool × Bool) => z.1.1) u =
      q (u, false) + q (u, true) := by
  classical
  have h : ∀ x, ∑ y, W x y = 1 := fun x => (hW x).sum_eq_one
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at h
  simp only [dist, bcJoint, jointOf, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq']
  linear_combination q (u, true) * h true + q (u, false) * h false

lemma bsbc_dist_U_Y₁ (u : 𝒰) (y : Bool) :
    dist (bcJoint q W) (pair (fun z : (𝒰 × Bool) × (Bool × Bool) => z.1.1) fun z => z.2.1) (u, y) =
      ∑ x, q (u, x) * bcMarg₁ W x y := by
  classical
  simp only [dist, pair, bcJoint, jointOf, bcMarg₁, Fintype.sum_prod_type, Prod.mk.injEq, mul_sum]
  simp [ite_and, Finset.sum_ite_eq']

lemma bsbc_dist_U_Y₂ (u : 𝒰) (y : Bool) :
    dist (bcJoint q W) (pair (fun z : (𝒰 × Bool) × (Bool × Bool) => z.1.1) fun z => z.2.2) (u, y) =
      ∑ x, q (u, x) * bcMarg₂ W x y := by
  classical
  simp only [dist, pair, bcJoint, jointOf, bcMarg₂, Fintype.sum_prod_type, Prod.mk.injEq, mul_sum]
  simp [ite_and, Finset.sum_ite_eq']

lemma bsbc_dist_XU (hW : IsChannel W) (x : Bool) (u : 𝒰) :
    dist (bcJoint q W) (pair (fun z : (𝒰 × Bool) × (Bool × Bool) => z.1.2) fun z => z.1.1) (x, u) =
      q (u, x) := by
  classical
  have h : ∀ x, ∑ y, W x y = 1 := fun x => (hW x).sum_eq_one
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at h
  simp only [dist, pair, bcJoint, jointOf, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, Finset.sum_ite_eq']
  linear_combination q (u, x) * h x

lemma bsbc_dist_XU_Y₁ (x : Bool) (u : 𝒰) (y : Bool) :
    dist (bcJoint q W) (pair (pair (fun z : (𝒰 × Bool) × (Bool × Bool) => z.1.2) fun z => z.1.1)
      fun z => z.2.1) ((x, u), y) = q (u, x) * bcMarg₁ W x y := by
  classical
  simp only [dist, pair, bcJoint, jointOf, bcMarg₁, Fintype.sum_prod_type, Prod.mk.injEq, mul_sum]
  simp [ite_and, Finset.sum_ite_eq']

lemma bsbc_dist_XU_Y₂ (x : Bool) (u : 𝒰) (y : Bool) :
    dist (bcJoint q W) (pair (pair (fun z : (𝒰 × Bool) × (Bool × Bool) => z.1.2) fun z => z.1.1)
      fun z => z.2.2) ((x, u), y) = q (u, x) * bcMarg₂ W x y := by
  classical
  simp only [dist, pair, bcJoint, jointOf, bcMarg₂, Fintype.sum_prod_type, Prod.mk.injEq, mul_sum]
  simp [ite_and, Finset.sum_ite_eq']

lemma bsbc_dist_Y₂ (y : Bool) :
    dist (bcJoint q W) (fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.2) y =
      ∑ u, ∑ x, q (u, x) * bcMarg₂ W x y := by
  classical
  simp only [dist, bcJoint, jointOf, bcMarg₂, Fintype.sum_prod_type, mul_sum]
  simp [Finset.sum_ite_eq']

/-- `a ∗ p ∈ [0, 1]` for `a, p ∈ [0, 1]`. -/
lemma bsbc_binConv_mem_Icc {a p : ℝ} (ha : a ∈ Set.Icc 0 1) (hp : p ∈ Set.Icc 0 1) :
    binConv a p ∈ Set.Icc 0 1 := by
  unfold binConv
  constructor <;> nlinarith [ha.1, ha.2, hp.1, hp.2]

lemma bsbc_cond_mem_Icc (hq : IsPMF q) (u : 𝒰) :
    q (u, true) / (q (u, false) + q (u, true)) ∈ Set.Icc 0 1 := by
  have h0 := hq.nonneg (u, false)
  have h1 := hq.nonneg (u, true)
  rcases (add_nonneg h0 h1).eq_or_lt with h | h
  · rw [← h, div_zero]; simp
  · exact ⟨div_nonneg h1 h.le, (div_le_one h).2 (by linarith)⟩

lemma bsbc_sum_weight (hq : IsPMF q) : ∑ u : 𝒰, (q (u, false) + q (u, true)) = 1 := by
  rw [← hq.sum_eq_one, Fintype.sum_prod_type]
  simp [add_comm]

/-- `H(Y₁ | U) = ∑ᵤ p(u) H(a_u ∗ p₁)`, where `a_u = P{X = 1 | U = u}`. -/
lemma bsbc_condEntropy_Y₁_U (hq : IsPMF q) (hW : IsChannel W) (h₁ : bcMarg₁ W = bsbcBSC p₁) :
    H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.1 | fun z => z.1.1 ; bcJoint q W] =
      ∑ u, (q (u, false) + q (u, true)) *
        binEntropy (binConv (q (u, true) / (q (u, false) + q (u, true))) p₁) :=
  bsbc_condEntropy_eq (bcJoint_isPMF hq hW) _ _ q (bsbc_dist_U hW) fun u => by
    rw [bsbc_dist_U_Y₁, h₁, Fintype.sum_bool, bsbcBSC_true, bsbcBSC_true]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    ring

/-- `H(Y₂ | U) = ∑ᵤ p(u) H(a_u ∗ p₂)`, where `a_u = P{X = 1 | U = u}`. -/
lemma bsbc_condEntropy_Y₂_U (hq : IsPMF q) (hW : IsChannel W) (h₂ : bcMarg₂ W = bsbcBSC p₂) :
    H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.2 | fun z => z.1.1 ; bcJoint q W] =
      ∑ u, (q (u, false) + q (u, true)) *
        binEntropy (binConv (q (u, true) / (q (u, false) + q (u, true))) p₂) :=
  bsbc_condEntropy_eq (bcJoint_isPMF hq hW) _ _ q (bsbc_dist_U hW) fun u => by
    rw [bsbc_dist_U_Y₂, h₂, Fintype.sum_bool, bsbcBSC_true, bsbcBSC_true]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    ring

/-- `H(Y₁ | X, U) = H(p₁)`. -/
lemma bsbc_condEntropy_Y₁_XU (hq : IsPMF q) (hW : IsChannel W) (h₁ : bcMarg₁ W = bsbcBSC p₁)
    (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) :
    H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.1 |
      pair (fun z => z.1.2) (fun z => z.1.1) ; bcJoint q W] = binEntropy p₁ := by
  have hμ := bcJoint_isPMF hq hW
  rw [condEntropy_of_channel (W := bsbcBSC p₁) Prod.fst fun z y => by
    rw [bsbc_dist_XU_Y₁, bsbc_dist_XU hW, h₁]]
  simp only [entropy_bsbcBSC hp₁ hp₁', ← sum_mul, (hμ.dist _).sum_eq_one, one_mul]

/-- `H(Y₂ | X, U) = H(p₂)`. -/
lemma bsbc_condEntropy_Y₂_XU (hq : IsPMF q) (hW : IsChannel W) (h₂ : bcMarg₂ W = bsbcBSC p₂)
    (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) :
    H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.2 |
      pair (fun z => z.1.2) (fun z => z.1.1) ; bcJoint q W] = binEntropy p₂ := by
  have hμ := bcJoint_isPMF hq hW
  rw [condEntropy_of_channel (W := bsbcBSC p₂) Prod.fst fun z y => by
    rw [bsbc_dist_XU_Y₂, bsbc_dist_XU hW, h₂]]
  simp only [entropy_bsbcBSC hp₂ hp₂', ← sum_mul, (hμ.dist _).sum_eq_one, one_mul]

/-- `I(X; Y₁ | U) = H(Y₁ | U) - H(p₁)`. -/
lemma bcInfoXY₁U_bsbc (hq : IsPMF q) (hW : IsChannel W) (h₁ : bcMarg₁ W = bsbcBSC p₁)
    (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1) :
    bcInfoXY₁U q W =
      H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.1 | fun z => z.1.1 ; bcJoint q W] -
        binEntropy p₁ := by
  rw [bcInfoXY₁U, condMutualInfo_comm (bcJoint_isPMF hq hW), condMutualInfo,
    bsbc_condEntropy_Y₁_XU hq hW h₁ hp₁ hp₁']

/-- `I(U; Y₂) = H(Y₂) - H(Y₂ | U)`. -/
lemma bsbc_bcInfoUY₂_eq (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoUY₂ q W = H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.2 ; bcJoint q W] -
      H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.2 | fun z => z.1.1 ; bcJoint q W] :=
  mutualInfo_eq_entropy_sub_condEntropy' (bcJoint_isPMF hq hW) _ _

/-- **Mrs. Gerber's lemma for the BS-BC.** `H(Y₂ | U) ≥ H(H⁻¹(H(Y₁ | U)) ∗ p̃₂)`. This is the
scalar Mrs. Gerber's lemma for the physically degraded channel `Y₂ = Y₁ ⊕ Z̃₂`; it is proved by
the same convexity argument, from `H(Y₂ | U = u) = H((a_u ∗ p₁) ∗ p̃₂)`. -/
theorem bsbc_mrsGerber_le (hq : IsPMF q) (hW : IsChannel W) (h₁ : bcMarg₁ W = bsbcBSC p₁)
    (h₂ : bcMarg₂ W = bsbcBSC p₂) (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    mrsGerber (bsbcNoise₂ p₁ p₂)
        H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.1 | fun z => z.1.1 ; bcJoint q W] ≤
      H[fun z : (𝒰 × Bool) × (Bool × Bool) => z.2.2 | fun z => z.1.1 ; bcJoint q W] := by
  have hn := bsbcNoise₂_mem hp₁₂ hp₂
  have hp₁I : p₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨hp₁, by linarith⟩
  rw [bsbc_condEntropy_Y₁_U hq hW h₁, bsbc_condEntropy_Y₂_U hq hW h₂]
  have hterm : ∀ u : 𝒰, binEntropy (binConv (q (u, true) / (q (u, false) + q (u, true))) p₂) =
      mrsGerber (bsbcNoise₂ p₁ p₂)
        (binEntropy (binConv (q (u, true) / (q (u, false) + q (u, true))) p₁)) := fun u => by
    rw [mrsGerber]
    rw [binEntropy_binConv_binEntropyInv (bsbc_binConv_mem_Icc
      (bsbc_cond_mem_Icc hq u) hp₁I)]
    rw [bsbc_binConv_assoc, binConv_bsbcNoise₂ hp₁₂ hp₂]
  simp only [hterm]
  have := (mrsGerber_convexOn (p := bsbcNoise₂ p₁ p₂) ⟨hn.1, hn.2.trans (by norm_num)⟩).map_sum_le
    (t := Finset.univ) (w := fun u : 𝒰 => q (u, false) + q (u, true))
    (p := fun u => binEntropy (binConv (q (u, true) / (q (u, false) + q (u, true))) p₁))
    (fun u _ => add_nonneg (hq.nonneg _) (hq.nonneg _)) (bsbc_sum_weight hq)
    (fun u _ => binEntropy_mem_Icc (bsbc_binConv_mem_Icc (bsbc_cond_mem_Icc hq u) hp₁I))
  simpa only [smul_eq_mul] using this

/-! ### The doubly symmetric binary source -/

/-- The doubly symmetric binary source `DSBS(a)`, as the law `p(u, x)` of `(U, X)` with
`U ∼ Bern(1/2)` (on `Fin 2`, `1` standing for the bit `1`), `X = U ⊕ V` and `V ∼ Bern(a)`
independent of `U`: `p(u, x) = BSC(a)(x | u) / 2`. -/
def bsbcDSBS (a : ℝ) : Fin 2 × Bool → ℝ := fun z => bsbcBSC a (decide (z.1 = 1)) z.2 / 2

lemma bsbcDSBS_isPMF {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsPMF (bsbcDSBS a) := by
  have hB := bsbcBSC_isChannel h0 h1
  refine ⟨fun z => div_nonneg ((hB _).nonneg _) zero_le_two, ?_⟩
  simp only [bsbcDSBS, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, bsbcBSC]
  norm_num
  ring

lemma bsbcDSBS_weight (a : ℝ) (u : Fin 2) :
    bsbcDSBS a (u, false) + bsbcDSBS a (u, true) = 1 / 2 := by
  fin_cases u <;> simp [bsbcDSBS, bsbcBSC] <;> ring

lemma binEntropy_binConv_bsbcDSBS (a p : ℝ) (u : Fin 2) :
    binEntropy (binConv (bsbcDSBS a (u, true) / (bsbcDSBS a (u, false) + bsbcDSBS a (u, true))) p) =
      binEntropy (binConv a p) := by
  rw [bsbcDSBS_weight, bsbcDSBS, show ∀ t : ℝ, t / 2 / (1 / 2) = t from fun t => by ring]
  simp only
  rw [bsbcBSC_true]
  split_ifs
  · exact binEntropy_binConv_one_sub_left a p
  · rfl

end Info

section DSBS

variable {W : Bool → Bool × Bool → ℝ} {a : ℝ}

/-- For `(U, X) ∼ DSBS(a)`, `H(Y₁ | U) = H(a ∗ p₁)`. -/
lemma bsbc_condEntropy_Y₁_U_DSBS (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hW : IsChannel W)
    (h₁ : bcMarg₁ W = bsbcBSC p₁) :
    H[fun z : (Fin 2 × Bool) × (Bool × Bool) => z.2.1 | fun z => z.1.1 ; bcJoint (bsbcDSBS a) W] =
      binEntropy (binConv a p₁) := by
  rw [bsbc_condEntropy_Y₁_U (bsbcDSBS_isPMF ha₀ ha₁) hW h₁]
  rw [Fin.sum_univ_two, binEntropy_binConv_bsbcDSBS, binEntropy_binConv_bsbcDSBS,
    bsbcDSBS_weight, bsbcDSBS_weight]
  ring

/-- For `(U, X) ∼ DSBS(a)`, `H(Y₂ | U) = H(a ∗ p₂)`. -/
lemma bsbc_condEntropy_Y₂_U_DSBS (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hW : IsChannel W)
    (h₂ : bcMarg₂ W = bsbcBSC p₂) :
    H[fun z : (Fin 2 × Bool) × (Bool × Bool) => z.2.2 | fun z => z.1.1 ; bcJoint (bsbcDSBS a) W] =
      binEntropy (binConv a p₂) := by
  rw [bsbc_condEntropy_Y₂_U (bsbcDSBS_isPMF ha₀ ha₁) hW h₂]
  rw [Fin.sum_univ_two, binEntropy_binConv_bsbcDSBS, binEntropy_binConv_bsbcDSBS,
    bsbcDSBS_weight, bsbcDSBS_weight]
  ring

/-- For `(U, X) ∼ DSBS(a)`, `Y₂ ∼ Bern(1/2)`, so `H(Y₂) = log 2`. -/
lemma bsbc_entropy_Y₂_DSBS (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hW : IsChannel W)
    (h₂ : bcMarg₂ W = bsbcBSC p₂) :
    H[fun z : (Fin 2 × Bool) × (Bool × Bool) => z.2.2 ; bcJoint (bsbcDSBS a) W] = log 2 := by
  have hμ := bcJoint_isPMF (bsbcDSBS_isPMF ha₀ ha₁) hW
  rw [entropyRV, entropy_bool (hμ.dist _), bsbc_dist_Y₂, h₂]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, bsbcDSBS, bsbcBSC]
  norm_num
  ring_nf
  rw [one_div, binEntropy_two_inv]

end DSBS

/-- For `p₁ < 1/2` and `v ∈ [H(p₁), log 2]`, there is `a ∈ [0, 1/2]` with `H(a ∗ p₁) = v`, and then
`H(a ∗ p₂) = H(H⁻¹(v) ∗ p̃₂)`. -/
lemma bsbc_exists_binConv (hp₁ : 0 ≤ p₁) (hhalf : p₁ < 2⁻¹) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2)
    {v : ℝ} (hv : v ∈ Set.Icc (binEntropy p₁) (log 2)) :
    ∃ a ∈ Set.Icc (0 : ℝ) (1 / 2), binEntropy (binConv a p₁) = v ∧
      binEntropy (binConv a p₂) = mrsGerber (bsbcNoise₂ p₁ p₂) v := by
  have hvI : v ∈ Set.Icc 0 (log 2) := ⟨(binEntropy_nonneg hp₁ (by linarith)).trans hv.1, hv.2⟩
  set b := binEntropyInv v
  have hbmem := binEntropyInv_mem hvI
  have hHb : binEntropy b = v := binEntropy_binEntropyInv hvI
  have hpb : p₁ ≤ b := by
    by_contra hlt
    push Not at hlt
    have := binEntropy_strictMonoOn hbmem ⟨hp₁, hhalf.le⟩ hlt
    linarith [hv.1]
  have hd : 0 < 1 - 2 * p₁ := by linarith
  have hab : binConv ((b - p₁) / (1 - 2 * p₁)) p₁ = b := by
    rw [binConv_eq, mul_div_cancel₀ _ hd.ne']; ring
  refine ⟨(b - p₁) / (1 - 2 * p₁), ⟨div_nonneg (by linarith) hd.le, (div_le_iff₀ hd).2 ?_⟩,
    by rw [hab, hHb], ?_⟩
  · linarith [hbmem.2]
  · conv_lhs => rw [← binConv_bsbcNoise₂ hp₁₂ hp₂, ← bsbc_binConv_assoc, hab]
    rfl

/-! ### The capacity region of the BS-BC -/

/-- **Proposition (Lecture 5 of [elgamal2010], pages 5-27, 5-28): capacity region of the binary
symmetric BC.** For a broadcast channel whose conditional marginals are `BSC(p₁)` and `BSC(p₂)`,
with `0 ≤ p₁ ≤ p₂ ≤ 1/2`, the region of the degraded DM-BC (`R₁ ≤ I(X; Y₁ | U)`,
`R₂ ≤ I(U; Y₂)` for some `p(u, x)`) is the set of rate pairs with
`R₁ ≤ H(a ∗ p₁) - H(p₁)` and `R₂ ≤ 1 - H(a ∗ p₂)` for some `a ∈ [0, 1/2]`, in bits.

`⊇`: `(U, X) ∼ DSBS(a)`. `⊆`: `I(U; Y₂) ≤ 1 - H(Y₂ | U)` and `I(X; Y₁ | U) = H(Y₁ | U) - H(p₁)`;
writing `H(Y₁ | U) = H(a ∗ p₁)` (possible as `H(Y₁ | U) ≥ H(p₁)`), Mrs. Gerber's lemma gives
`H(Y₂ | U) ≥ H(a ∗ p₁ ∗ p̃₂) = H(a ∗ p₂)`. (The notes choose `a` with `H(Y₂ | U) = H(a ∗ p₂)`
instead, and invert `v ↦ H(H⁻¹(v) ∗ p̃₂)`, which is only possible for `p₂ < 1/2`; this choice of
`a` also covers `p₂ = 1/2`.) -/
theorem degradedBCRegionBits_bsbc {W : Bool → Bool × Bool → ℝ} (hW : IsChannel W)
    (h₁ : bcMarg₁ W = bsbcBSC p₁) (h₂ : bcMarg₂ W = bsbcBSC p₂) (hp₁ : 0 ≤ p₁)
    (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    degradedBCRegionBits W = {R | ∃ a ∈ Set.Icc (0 : ℝ) (1 / 2),
      R.1 ≤ (binEntropy (binConv a p₁) - binEntropy p₁) / log 2 ∧
      R.2 ≤ 1 - binEntropy (binConv a p₂) / log 2} := by
  have hl : 0 < log 2 := log_pos one_lt_two
  have hp₁' : p₁ ≤ 1 := by linarith
  have hp₂₀ : 0 ≤ p₂ := by linarith
  have hp₂' : p₂ ≤ 1 := by linarith
  ext R
  constructor
  · rintro ⟨k, q, hq, hR₁, hR₂⟩
    have hμ := bcJoint_isPMF hq hW
    set h₁' := H[fun z : (Fin k × Bool) × (Bool × Bool) => z.2.1 | fun z => z.1.1 ; bcJoint q W]
      with hh₁'
    set h₂' := H[fun z : (Fin k × Bool) × (Bool × Bool) => z.2.2 | fun z => z.1.1 ; bcJoint q W]
      with hh₂'
    have hI₁ := bcInfoXY₁U_bsbc hq hW h₁ hp₁ hp₁'
    have hI₂ := bsbc_bcInfoUY₂_eq hq hW
    have hY₂ : H[fun z : (Fin k × Bool) × (Bool × Bool) => z.2.2 ; bcJoint q W] ≤ log 2 := by
      have := entropyRV_le_log_card hμ (fun z : (Fin k × Bool) × (Bool × Bool) => z.2.2)
      simpa using this
    have hlow₁ : binEntropy p₁ ≤ h₁' := by
      have := condEntropy_le_condEntropy hμ (fun z : (Fin k × Bool) × (Bool × Bool) => z.2.1)
        (fun z => z.1.2) (fun z => z.1.1)
      rwa [bsbc_condEntropy_Y₁_XU hq hW h₁ hp₁ hp₁'] at this
    have hlow₂ : binEntropy p₂ ≤ h₂' := by
      have := condEntropy_le_condEntropy hμ (fun z : (Fin k × Bool) × (Bool × Bool) => z.2.2)
        (fun z => z.1.2) (fun z => z.1.1)
      rwa [bsbc_condEntropy_Y₂_XU hq hW h₂ hp₂₀ hp₂'] at this
    have hmem₁ : h₁' ∈ Set.Icc 0 (log 2) := condEntropy_bool_mem_Icc hμ _ _
    have hmg := bsbc_mrsGerber_le hq hW h₁ h₂ hp₁ hp₁₂ hp₂
    rw [← hh₁', ← hh₂'] at hmg
    -- It suffices to find `a ∈ [0, 1/2]` with `H(Y₁ | U) ≤ H(a ∗ p₁)` and `H(a ∗ p₂) ≤ H(Y₂ | U)`.
    suffices h : ∃ a ∈ Set.Icc (0 : ℝ) (1 / 2), h₁' ≤ binEntropy (binConv a p₁) ∧
        binEntropy (binConv a p₂) ≤ h₂' by
      obtain ⟨a, ha, ha₁, ha₂⟩ := h
      refine ⟨a, ha, hR₁.trans ?_, hR₂.trans ?_⟩
      · rw [hI₁]
        exact div_le_div_of_nonneg_right (by linarith) hl.le
      · rw [hI₂, le_sub_iff_add_le, ← add_div, div_le_one hl]
        linarith
    rcases (show p₁ ≤ 2⁻¹ by linarith).eq_or_lt with hhalf | hhalf
    · -- `p₁ = p₂ = 1/2`: all the conditional entropies are `log 2`.
      have hp₂h : p₂ = 2⁻¹ := by linarith
      refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
      · rw [hhalf, binConv_half_right, binEntropy_two_inv]
        exact hmem₁.2
      · rwa [hp₂h, binConv_half_right, ← hp₂h]
    · -- `p₁ < 1/2`: take `a` with `H(a ∗ p₁) = H(Y₁ | U)`.
      obtain ⟨a, ha, ha₁, ha₂⟩ := bsbc_exists_binConv hp₁ hhalf hp₁₂ hp₂ ⟨hlow₁, hmem₁.2⟩
      exact ⟨a, ha, ha₁.ge, ha₂.trans_le hmg⟩
  · rintro ⟨a, ha, hR₁, hR₂⟩
    have ha₁ : a ≤ 1 := by linarith [ha.2]
    refine ⟨2, bsbcDSBS a, bsbcDSBS_isPMF ha.1 ha₁, ?_, ?_⟩
    · rwa [bcInfoXY₁U_bsbc (bsbcDSBS_isPMF ha.1 ha₁) hW h₁ hp₁ hp₁',
        bsbc_condEntropy_Y₁_U_DSBS ha.1 ha₁ hW h₁]
    · rw [bsbc_bcInfoUY₂_eq (bsbcDSBS_isPMF ha.1 ha₁) hW, bsbc_entropy_Y₂_DSBS ha.1 ha₁ hW h₂,
        bsbc_condEntropy_Y₂_U_DSBS ha.1 ha₁ hW h₂, sub_div, div_self hl.ne']
      exact hR₂

/-! ### Superposition coding versus time division -/

/-- **Lecture 5 of [elgamal2010], page 5-12.** The superposition coding inner bound of the BS-BC,
in bits: `R₁ ≤ H(a ∗ p₁) - H(p₁)`, `R₂ ≤ 1 - H(a ∗ p₂)` for some `a ∈ [0, 1/2]`. By
`degradedBCRegionBits_bsbc` it is `degradedBCRegionBits W`. -/
def bsbcSuperpositionRegion (p₁ p₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ a ∈ Set.Icc (0 : ℝ) (1 / 2), R.1 ≤ (binEntropy (binConv a p₁) - binEntropy p₁) / log 2 ∧
    R.2 ≤ 1 - binEntropy (binConv a p₂) / log 2}

/-- `degradedBCRegionBits_bsbc` in terms of `bsbcSuperpositionRegion`. -/
theorem degradedBCRegionBits_eq_bsbcSuperpositionRegion {W : Bool → Bool × Bool → ℝ}
    (hW : IsChannel W) (h₁ : bcMarg₁ W = bsbcBSC p₁) (h₂ : bcMarg₂ W = bsbcBSC p₂) (hp₁ : 0 ≤ p₁)
    (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    degradedBCRegionBits W = bsbcSuperpositionRegion p₁ p₂ :=
  degradedBCRegionBits_bsbc hW h₁ h₂ hp₁ hp₁₂ hp₂

/-- The region of the BS-BC is closed, as `a` ranges over the compact set `[0, 1/2]`. So its closure
is itself, and the capacity region of the Proposition of the notes needs no closure. -/
theorem isClosed_bsbcSuperpositionRegion (p₁ p₂ : ℝ) :
    IsClosed (bsbcSuperpositionRegion p₁ p₂) := by
  have hc : ∀ p : ℝ, Continuous fun a : Set.Icc (0 : ℝ) (1 / 2) =>
      binEntropy (binConv (a : ℝ) p) := fun p =>
    binEntropy_continuous.comp (by unfold binConv; fun_prop)
  have hT : IsClosed {z : (ℝ × ℝ) × Set.Icc (0 : ℝ) (1 / 2) |
      z.1.1 ≤ (binEntropy (binConv (z.2 : ℝ) p₁) - binEntropy p₁) / log 2 ∧
      z.1.2 ≤ 1 - binEntropy (binConv (z.2 : ℝ) p₂) / log 2} :=
    (isClosed_le (by fun_prop)
      (((hc p₁).comp continuous_snd).sub continuous_const |>.div_const _)).inter
    (isClosed_le (by fun_prop)
      (continuous_const.sub (((hc p₂).comp continuous_snd).div_const _)))
  have := isClosedMap_fst_of_compactSpace _ hT
  convert this using 1
  ext R
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨(R, ⟨a, ha⟩), h, rfl⟩
  · rintro ⟨⟨R', a⟩, h, rfl⟩
    exact ⟨a, a.2, h⟩

/-- **Lecture 5 of [elgamal2010], page 5-8.** The time-division inner bound of the BS-BC, in bits:
`R₁ ≤ λ C₁`, `R₂ ≤ (1 - λ) C₂` for some `λ ∈ [0, 1]`, with `Cⱼ = 1 - H(pⱼ)` the capacity of
`BSC(pⱼ)`. -/
def bsbcTimeDivisionRegion (p₁ p₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ t ∈ Set.Icc (0 : ℝ) 1, R.1 ≤ t * (1 - binEntropy p₁ / log 2) ∧
    R.2 ≤ (1 - t) * (1 - binEntropy p₂ / log 2)}

/-- **Lecture 5 of [elgamal2010], page 5-12.** Superposition coding does at least as well as time
division on the BS-BC. This follows from the convexity of `v ↦ H(H⁻¹(v) ∗ p̃₂)`. -/
theorem bsbcTimeDivisionRegion_subset (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    bsbcTimeDivisionRegion p₁ p₂ ⊆ bsbcSuperpositionRegion p₁ p₂ := by
  rintro R ⟨t, ht, hR₁, hR₂⟩
  have hl : 0 < log 2 := log_pos one_lt_two
  rcases (show p₁ ≤ 2⁻¹ by linarith).eq_or_lt with hhalf | hhalf
  · have hp₂h : p₂ = 2⁻¹ := by linarith
    refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
    · rw [hhalf, binConv_half_right, binEntropy_two_inv, sub_self, zero_div]
      rw [hhalf, binEntropy_two_inv, div_self hl.ne', sub_self, mul_zero] at hR₁
      exact hR₁
    · rw [hp₂h, binConv_half_right, binEntropy_two_inv, div_self hl.ne', sub_self]
      rw [hp₂h, binEntropy_two_inv, div_self hl.ne', sub_self, mul_zero] at hR₂
      exact hR₂
  · have hH₁ : binEntropy p₁ ≤ log 2 := binEntropy_le_log_two
    set v := t * log 2 + (1 - t) * binEntropy p₁
    have hv : v ∈ Set.Icc (binEntropy p₁) (log 2) := ⟨by nlinarith [ht.1, ht.2],
      by nlinarith [ht.1, ht.2]⟩
    obtain ⟨a, ha, ha₁, ha₂⟩ := bsbc_exists_binConv hp₁ hhalf hp₁₂ hp₂ hv
    have hn := bsbcNoise₂_mem hp₁₂ hp₂
    have hp₁m : p₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨hp₁, by linarith⟩
    -- `H(H⁻¹(v) ∗ p̃₂) ≤ λ log 2 + (1 - λ) H(p₂)` by convexity.
    have hconv := (mrsGerber_convexOn (p := bsbcNoise₂ p₁ p₂)
      ⟨hn.1, hn.2.trans (by norm_num)⟩).2 (x := log 2) (y := binEntropy p₁)
      ⟨log_nonneg one_le_two, le_rfl⟩ (binEntropy_mem_Icc hp₁m) ht.1 (sub_nonneg.2 ht.2)
      (by ring)
    have hm₁ : mrsGerber (bsbcNoise₂ p₁ p₂) (log 2) = log 2 := by
      rw [mrsGerber, ← binEntropy_two_inv, binEntropyInv_binEntropy ⟨by norm_num, le_rfl⟩,
        binConv_half_left]
    have hm₂ : mrsGerber (bsbcNoise₂ p₁ p₂) (binEntropy p₁) = binEntropy p₂ := by
      rw [mrsGerber, binEntropy_binConv_binEntropyInv hp₁m, binConv_bsbcNoise₂ hp₁₂ hp₂]
    simp only [smul_eq_mul, hm₁, hm₂] at hconv
    refine ⟨a, ha, ?_, ?_⟩
    · rw [ha₁]
      refine hR₁.trans (le_of_eq ?_)
      field_simp
      ring
    · rw [ha₂]
      refine hR₂.trans ?_
      rw [show (1 - t) * (1 - binEntropy p₂ / log 2) =
        1 - (t * log 2 + (1 - t) * binEntropy p₂) / log 2 by field_simp; ring]
      exact sub_le_sub_left (div_le_div_of_nonneg_right hconv hl.le) 1

lemma bsbc_binEntropy_quarter : binEntropy (1 / 4) = 2 * log 2 - 3 / 4 * log 3 := by
  rw [binEntropy_eq_mul_log_inv]
  have h1 : ((1 : ℝ) / 4)⁻¹ = 2 ^ 2 := by norm_num
  have h2 : (1 - (1 : ℝ) / 4)⁻¹ = 2 ^ 2 / 3 := by norm_num
  rw [h1, h2, log_div (by norm_num) (by norm_num), log_pow]
  push_cast
  ring

lemma bsbc_binEntropy_three_eighths :
    binEntropy (3 / 8) = 3 * log 2 - 3 / 8 * log 3 - 5 / 8 * log 5 := by
  rw [binEntropy_eq_mul_log_inv]
  have h1 : ((3 : ℝ) / 8)⁻¹ = 2 ^ 3 / 3 := by norm_num
  have h2 : (1 - (3 : ℝ) / 8)⁻¹ = 2 ^ 3 / 5 := by norm_num
  rw [h1, h2, log_div (by norm_num) (by norm_num), log_div (by norm_num) (by norm_num), log_pow]
  push_cast
  ring

/-- **Lecture 5 of [elgamal2010], page 5-12.** Superposition coding does strictly better than time
division on the BS-BC for some parameters: for `p₁ = 0` and `p₂ = 1/4`, the rate pair
`(H(1/4), 1 - H(3/8))` of the `DSBS(1/4)` is not achievable by time division. -/
theorem bsbcTimeDivisionRegion_ssubset :
    bsbcTimeDivisionRegion 0 (1 / 4) ⊂ bsbcSuperpositionRegion 0 (1 / 4) := by
  refine (Set.ssubset_iff_of_subset (bsbcTimeDivisionRegion_subset le_rfl (by norm_num)
    (by norm_num))).2 ⟨(binEntropy (1 / 4) / log 2, 1 - binEntropy (3 / 8) / log 2),
      ⟨1 / 4, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩, ?_⟩
  · simp [binConv]
  · norm_num [binConv]
  · rintro ⟨t, -, h₁, h₂⟩
    have hl : 0 < log 2 := log_pos one_lt_two
    simp only [binEntropy_zero, zero_div, sub_zero, mul_one] at h₁ h₂
    -- `1 - H(3/8) ≤ (1 - t)(1 - H(1/4)) ≤ (1 - H(1/4))²`.
    have hC : 0 ≤ 1 - binEntropy (1 / 4) / log 2 := by
      rw [sub_nonneg, div_le_one hl]
      exact binEntropy_le_log_two
    have h3 : 1 - binEntropy (3 / 8) / log 2 ≤ (1 - binEntropy (1 / 4) / log 2) ^ 2 := by
      nlinarith
    have key : (log 2 - binEntropy (1 / 4)) ^ 2 < log 2 * (log 2 - binEntropy (3 / 8)) := by
      rw [bsbc_binEntropy_quarter, bsbc_binEntropy_three_eighths]
      have := log_two_gt_d9
      have := log_two_lt_d9
      have := log_three_gt_d9
      have := log_three_lt_d9
      have := log_five_gt_d9
      have := log_five_lt_d9
      norm_num at *
      nlinarith
    have e₁ : 1 - binEntropy (3 / 8) / log 2 =
        log 2 * (log 2 - binEntropy (3 / 8)) / log 2 ^ 2 := by
      field_simp
    have e₂ : (1 - binEntropy (1 / 4) / log 2) ^ 2 =
        (log 2 - binEntropy (1 / 4)) ^ 2 / log 2 ^ 2 := by
      field_simp
    rw [e₁, e₂] at h3
    have := (div_le_div_iff_of_pos_right (by positivity)).1 h3
    linarith

end InfoTheory
