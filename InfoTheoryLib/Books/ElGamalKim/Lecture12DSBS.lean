/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture11
public import InfoTheoryLib.Network.BCClasses
public import InfoTheoryLib.RateDistortion.SideInfoCases

/-!
# El Gamal & Kim, Lecture 12: the doubly symmetric binary source

This file computes the rate–distortion functions of Lecture 12 for a `DSBS(p)` and the Hamming
distortion. Side information available causally and noncausally at the decoder are treated together,
as `min (I(X; U) - θ I(Y; U))` with `θ = 0` and `θ = 1`.

For each `u`, the function `x̂(u, ·)` is a constant, the identity or the negation. The rate is the
mean
under `p(u)` of `ψ(P{X = 1 | U = u})`, with

  `ψ(a) = (1 - θ) log 2 - H(a) + θ H(a ∗ p)`,

so `ψ(a) = 1 - H(a)` for `θ = 0` and `ψ(a) = g(a) = H(a ∗ p) - H(a)` for `θ = 1`, and `ψ` is convex.
A constant has distortion `a` or `1 - a`, and the others `p` or `1 - p`. Hence any line below `ψ`
that
vanishes at `p` is a lower bound on the rate, and the rate–distortion function is the lower convex
envelope of `ψ` and the point `(p, 0)`.

## Main statements

* `dsbsPsi_convexOn`, `dsbsPsi_tangent`: the convexity of `ψ`.
* `line_le_sideRate`: the converse, by supporting lines.
* `exists_isDsbsTangency`: the point of tangency exists.
* `causalRD_dsbs_of_le_tangency`, `causalRD_dsbs_of_tangency_le`: the formula for `R_CSI-D(D)`.
* `wzRD_dsbs_of_le_tangency`, `wzRD_dsbs_of_tangency_le`: the formula for `R_SI-D(D)`.
* `bothRD_dsbs`, `bothRD_dsbs_of_le`: `R_SI-ED(D) = H(p) - H(D)`.
* `bothRD_lt_wzRD_dsbs`: the cost of the lack of side information at the encoder.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 12
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ### The doubly symmetric binary source -/

section DSBS

variable {p θ a : ℝ}

/-- `(1 - θ) log 2 - H(a) + θ H(a ∗ p)`, in nats: `1 - H(a)` for `θ = 0` and `H(a ∗ p) - H(a)` for
`θ = 1`. -/
def dsbsPsi (θ p a : ℝ) : ℝ := (1 - θ) * log 2 - binEntropy a + θ * binEntropy (binConv a p)

/-- The derivative of `dsbsPsi` in `a`. -/
def dsbsDPsi (θ p a : ℝ) : ℝ :=
  -(log (1 - a) - log a) + θ * ((1 - 2 * p) * (log (1 - binConv a p) - log (binConv a p)))

lemma dsbsPsi_one_sub (θ p a : ℝ) : dsbsPsi θ p (1 - a) = dsbsPsi θ p a := by
  simp only [dsbsPsi, binEntropy_one_sub, binEntropy_binConv_one_sub_left]

/-- `H(a) ≤ H(a ∗ p)`: `a ∗ p` is a mixture of `a` and `1 - a`. -/
lemma binEntropy_le_binConv (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    binEntropy a ≤ binEntropy (binConv a p) := by
  have h := strictConcave_binEntropy.concaveOn.2 (show a ∈ Set.Icc (0 : ℝ) 1 from ⟨ha0, ha1⟩)
    (show 1 - a ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩) (sub_nonneg.2 hp1) hp0
    (by ring)
  simp only [smul_eq_mul, binEntropy_one_sub] at h
  have e : (1 - p) * a + p * (1 - a) = binConv a p := by
    unfold binConv
    ring
  rw [e] at h
  linarith

lemma dsbsPsi_nonneg (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) : 0 ≤ dsbsPsi θ p a := by
  have h1 := binEntropy_le_binConv hp0 hp1 ha0 ha1
  have h2 : binEntropy a ≤ log 2 := binEntropy_le_log_two
  have e : dsbsPsi θ p a = (1 - θ) * (log 2 - binEntropy a) +
      θ * (binEntropy (binConv a p) - binEntropy a) := by
    simp only [dsbsPsi]
    ring
  rw [e]
  exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hθ0 (by linarith))

/-- The channel from `X` to `Y` of a `DSBS(p)`. -/
lemma dsbsPMF_eq (p : ℝ) (x y : Bool) :
    dsbsPMF p (x, y) = margFst (dsbsPMF p) x * bscKernel p x y := by
  change _ = dist (dsbsPMF p) Prod.fst x * _
  rw [dist_fst_dsbsPMF]
  rfl

/-- A pmf on `Bool` is Bernoulli. -/
lemma isPMF_bool_eq {r : Bool → ℝ} (hr : IsPMF r) : r = bernoulliPMF (r true) := by
  funext b
  have h := hr.sum_eq_one
  rw [Fintype.sum_bool] at h
  cases b
  · simp only [bernoulliPMF, Bool.false_eq_true, ↓reduceIte]
    linarith
  · simp [bernoulliPMF]

/-- The output of `BSC(p)` for a Bernoulli(`a`) input is Bernoulli(`a ∗ p`). -/
lemma outDist_bernoulli_bsc (a p : ℝ) :
    outDist (bernoulliPMF a) (bscKernel p) = bernoulliPMF (binConv a p) := by
  funext b
  cases b
  · simp [outDist, bscKernel, bernoulliPMF, binConv]
    ring
  · simp [outDist, bscKernel, bernoulliPMF, binConv]

variable {υ : Type*} [Fintype υ] {q : Bool → υ → ℝ} {w : υ → ℝ} {r : υ → Bool → ℝ}

/-- **The rate for a `DSBS(p)`**, in terms of the posterior laws: `∑ᵤ w(u) ψ(P{X = 1 | U = u})`. -/
theorem sideRate_dsbs (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : IsChannel q) (hw : ∀ u, 0 ≤ w u)
    (hr : ∀ u, IsPMF (r u)) (hrep : ∀ x u, margFst (dsbsPMF p) x * q x u = w u * r u x) (θ : ℝ) :
    sideRate θ (dsbsPMF p) q = ∑ u, w u * dsbsPsi θ p (r u true) := by
  have hP := dsbsPMF_isPMF hp0 hp1
  have hwP := isPMF_of_rep hP hq hw hr hrep
  have hW := bscKernel_isPMF hp0 hp1
  rw [sideRate_eq_of_rep hP hq hW (dsbsPMF_eq p) hw hr hrep θ]
  have e1 : entropy (margFst (dsbsPMF p)) = log 2 := entropy_fst_dsbsPMF p
  have e2 : entropy (margSnd (dsbsPMF p)) = log 2 := entropy_snd_dsbsPMF p
  have e3 : ∀ u, sideF θ (bscKernel p) (r u) =
      binEntropy (r u true) - θ * binEntropy (binConv (r u true) p) := fun u => by
    simp only [sideF]
    conv_lhs => rw [isPMF_bool_eq (hr u)]
    rw [entropy_bernoulliPMF, outDist_bernoulli_bsc, entropy_bernoulliPMF]
  rw [e1, e2]
  simp only [e3, dsbsPsi]
  have e4 : ∑ u, w u * ((1 - θ) * log 2 - binEntropy (r u true) +
      θ * binEntropy (binConv (r u true) p)) = ∑ u, (w u * ((1 - θ) * log 2) -
        w u * (binEntropy (r u true) - θ * binEntropy (binConv (r u true) p))) :=
    sum_congr rfl fun u _ => by ring
  rw [e4, sum_sub_distrib, ← sum_mul, hwP.sum_eq_one, one_mul]
  ring

/-- The expected Hamming distortion of `x̂ = g(y)` for `X ∼ Bernoulli(a)` and `Y` from `BSC(p)`. -/
def dsbsLetter (p a : ℝ) (g : Bool → Bool) : ℝ :=
  sideG (bscKernel p) (fun x y => hammingDistortion x (g y)) (bernoulliPMF a)

/-- **The cost for a `DSBS(p)`**, in terms of the posterior laws. -/
theorem sideCost_dsbs (hr : ∀ u, IsPMF (r u))
    (hrep : ∀ x u, margFst (dsbsPMF p) x * q x u = w u * r u x) (f : υ → Bool → Bool) :
    sideCost (dsbsPMF p) q (fun u x y => hammingDistortion x (f u y)) =
      ∑ u, w u * dsbsLetter p (r u true) (f u) := by
  rw [sideCost_eq_of_rep (dsbsPMF_eq p) hrep]
  refine sum_congr rfl fun u _ => ?_
  simp only [dsbsLetter]
  conv_lhs => rw [isPMF_bool_eq (hr u)]

lemma dsbsLetter_const_false (p a : ℝ) : dsbsLetter p a (fun _ => false) = a := by
  simp [dsbsLetter, sideG, bscKernel, bernoulliPMF, hammingDistortion]

lemma dsbsLetter_const_true (p a : ℝ) : dsbsLetter p a (fun _ => true) = 1 - a := by
  simp [dsbsLetter, sideG, bscKernel, bernoulliPMF, hammingDistortion]

lemma dsbsLetter_id (p a : ℝ) : dsbsLetter p a id = p := by
  simp [dsbsLetter, sideG, bscKernel, bernoulliPMF, hammingDistortion]
  ring

lemma dsbsLetter_not (p a : ℝ) : dsbsLetter p a not = 1 - p := by
  simp [dsbsLetter, sideG, bscKernel, bernoulliPMF, hammingDistortion]
  ring

/-- Each of the four functions `x̂(y)` is on the same side of a line below `ψ` that vanishes at `p`.
-/
lemma line_le_dsbsPsi (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) {A s : ℝ}
    (hs : 0 ≤ s) (h1 : ∀ c ∈ Set.Icc (0 : ℝ) 1, A - s * c ≤ dsbsPsi θ p c) (h2 : A - s * p ≤ 0)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (g : Bool → Bool) :
    A - s * dsbsLetter p a g ≤ dsbsPsi θ p a := by
  have hψ := dsbsPsi_nonneg hθ0 hθ1 hp0 (by linarith) ha0 ha1
  have hg : g = (fun _ => false) ∨ g = (fun _ => true) ∨ g = id ∨ g = not := by
    cases hf : g false <;> cases ht : g true
    · left
      funext b
      cases b <;> simp [hf, ht]
    · right; right; left
      funext b
      cases b <;> simp [hf, ht]
    · right; right; right
      funext b
      cases b <;> simp [hf, ht]
    · right; left
      funext b
      cases b <;> simp [hf, ht]
  rcases hg with rfl | rfl | rfl | rfl
  · rw [dsbsLetter_const_false]
    exact h1 a ⟨ha0, ha1⟩
  · rw [dsbsLetter_const_true, ← dsbsPsi_one_sub]
    exact h1 _ ⟨by linarith, by linarith⟩
  · rw [dsbsLetter_id]
    linarith
  · rw [dsbsLetter_not]
    have : s * p ≤ s * (1 - p) := mul_le_mul_of_nonneg_left (by linarith) hs
    linarith

/-- **The supporting lines (the converse for a `DSBS(p)`).** For every `p(u | x)` and `x̂(u, y)` and
a
line `A - s c` with `s ≥ 0`, below `ψ` on `[0, 1]` and nonpositive at `p`, we have
`I(X; U) - θ I(Y; U) ≥ A - s E d(X, X̂)`. -/
theorem line_le_sideRate (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) {A s : ℝ}
    (hs : 0 ≤ s) (h1 : ∀ c ∈ Set.Icc (0 : ℝ) 1, A - s * c ≤ dsbsPsi θ p c) (h2 : A - s * p ≤ 0)
    (hq : IsChannel q) (f : υ → Bool → Bool) :
    A - s * sideCost (dsbsPMF p) q (fun u x y => hammingDistortion x (f u y)) ≤
      sideRate θ (dsbsPMF p) q := by
  have hp1 : p ≤ 1 := by linarith
  have hP := dsbsPMF_isPMF hp0 hp1
  obtain ⟨w, r, hw, hr, hrep⟩ := exists_side_rep hP hq
  have hwP := isPMF_of_rep hP hq hw hr hrep
  rw [sideRate_dsbs hp0 hp1 hq hw hr hrep, sideCost_dsbs hr hrep]
  have e : A - s * ∑ u, w u * dsbsLetter p (r u true) (f u) =
      ∑ u, w u * (A - s * dsbsLetter p (r u true) (f u)) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hwP.sum_eq_one, one_mul, mul_sum]
    congr 1
    exact sum_congr rfl fun u _ => by ring
  rw [e]
  refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hw u)
  have h0 := (hr u).nonneg true
  have h3 := (hr u).le_one true
  exact line_le_dsbsPsi hθ0 hθ1 hp0 hp hs h1 h2 h0 h3 _

/-- The auxiliary random variable `U = X ⊕ V`, with `V ∼ Bernoulli(a)`, has
`I(X; U) - θ I(Y; U) = ψ(a)` and `E d(X, U) = a`. -/
lemma sideRD_dsbs_le_psi (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (θ : ℝ) {D : ℝ}
    (hD : a ≤ D) : sideRD θ (dsbsPMF p) hammingDistortion D ≤ dsbsPsi θ p a := by
  have hP := dsbsPMF_isPMF hp0 hp1
  have hq : IsChannel (bscKernel a) := bscKernel_isPMF ha0 ha1
  have hrep : ∀ x u, margFst (dsbsPMF p) x * bscKernel a x u =
      (fun _ : Bool => (1 / 2 : ℝ)) u * bscKernel a u x := fun x u => by
    change dist (dsbsPMF p) Prod.fst x * _ = _
    rw [dist_fst_dsbsPMF]
    cases x <;> cases u <;> rfl
  have hr : ∀ u, IsPMF (bscKernel a u) := bscKernel_isPMF ha0 ha1
  have hw : ∀ u : Bool, 0 ≤ (fun _ : Bool => (1 / 2 : ℝ)) u := fun _ => by norm_num
  have hrate : sideRate θ (dsbsPMF p) (bscKernel a) = dsbsPsi θ p a := by
    rw [sideRate_dsbs hp0 hp1 hq hw hr hrep, Fintype.sum_bool]
    have e1 : bscKernel a true true = 1 - a := by simp [bscKernel, bernoulliPMF]
    have e2 : bscKernel a false true = a := by simp [bscKernel, bernoulliPMF]
    rw [e1, e2, dsbsPsi_one_sub]
    ring
  have hcost : sideCost (dsbsPMF p) (bscKernel a) (fun u x y => hammingDistortion x u) = a := by
    have := sideCost_dsbs (q := bscKernel a) hr hrep fun u _ => u
    rw [this, Fintype.sum_bool]
    have e1 : bscKernel a true true = 1 - a := by simp [bscKernel, bernoulliPMF]
    have e2 : bscKernel a false true = a := by simp [bscKernel, bernoulliPMF]
    simp only [e1, e2]
    rw [dsbsLetter_const_true, dsbsLetter_const_false]
    ring
  rw [← hrate]
  exact sideRD_le hP hq θ (fun u _ => u) (hcost.trans_le hD)

/-- **Zero-rate decoding.** With `U` constant and `x̂ = y`, the rate is `0` and the distortion is
`p`.
-/
lemma sideRD_dsbs_le_zero (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) {D : ℝ} (hD : p ≤ D) :
    sideRD θ (dsbsPMF p) hammingDistortion D ≤ 0 := by
  have hP := dsbsPMF_isPMF hp0 hp1
  have hq : IsChannel fun (_ : Bool) (_ : Unit) => (1 : ℝ) := fun _ =>
    ⟨fun _ => zero_le_one, by simp⟩
  have hrep : ∀ x u, margFst (dsbsPMF p) x * (fun (_ : Bool) (_ : Unit) => (1 : ℝ)) x u =
      (fun _ : Unit => (1 : ℝ)) u * (fun (_ : Unit) => bernoulliPMF (1 / 2)) u x := fun x u => by
    change dist (dsbsPMF p) Prod.fst x * _ = _
    rw [dist_fst_dsbsPMF]
    cases x <;> norm_num [bernoulliPMF]
  have hr : ∀ u : Unit, IsPMF ((fun (_ : Unit) => bernoulliPMF (1 / 2)) u) := fun _ =>
    bernoulliPMF_isPMF (by norm_num) (by norm_num)
  have hrate := sideRate_dsbs hp0 hp1 hq (w := fun _ => 1) (fun _ => zero_le_one) hr hrep θ
  have hcost := sideCost_dsbs (q := fun (_ : Bool) (_ : Unit) => (1 : ℝ)) hr hrep fun _ y => y
  have e0 : dsbsPsi θ p (bernoulliPMF (1 / 2) true) = 0 := by
    have e : bernoulliPMF (1 / 2) true = 2⁻¹ := by norm_num [bernoulliPMF]
    rw [e, dsbsPsi, binConv_half_left, binEntropy_two_inv]
    ring
  simp only [Fintype.sum_unique, one_mul, e0] at hrate hcost
  rw [show (fun (y : Bool) => y) = id from rfl, dsbsLetter_id] at hcost
  rw [← hrate]
  exact sideRD_le hP hq θ (fun _ y => y) (hcost.trans_le hD)

/-- `D_min = 0` for the Hamming distortion. -/
lemma minDistortion_dsbs (p D : ℝ) (hD : 0 ≤ D) :
    minDistortion (margFst (dsbsPMF p)) (hammingDistortion (α := Bool)) ≤ D := by
  rw [minDistortion_hammingDistortion]
  exact hD

/-! #### The convexity of `ψ` -/

lemma binConv_mem_Ioo (hp0 : 0 < p) (hp : p < 1 / 2) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    binConv a p ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := ha
  rw [binConv_eq]
  constructor <;> nlinarith

lemma hasDerivAt_binConv (a p : ℝ) : HasDerivAt (fun a => binConv a p) (1 - 2 * p) a := by
  have h := ((hasDerivAt_id a).const_mul (1 - 2 * p)).const_add p
  simp only [mul_one] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun x => binConv_eq x p)

/-- The derivative of `H'(x) = log (1 - x) - log x`. -/
lemma hasDerivAt_dH {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => log (1 - x) - log x) (-(1 / (x * (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hx
  have h2 := ((hasDerivAt_id x).const_sub 1).log (by simp only [id]; linarith)
  have h3 := hasDerivAt_log h0.ne'
  refine ((h2.sub h3).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [id, Pi.sub_apply]
  · simp only [id]
    have : 1 - x ≠ 0 := by linarith
    field_simp
    ring

lemma hasDerivAt_dsbsPsi (hp0 : 0 < p) (hp : p < 1 / 2) (ha : a ∈ Set.Ioo (0 : ℝ) 1) (θ : ℝ) :
    HasDerivAt (dsbsPsi θ p) (dsbsDPsi θ p a) a := by
  have hb := binConv_mem_Ioo hp0 hp ha
  have h1 := hasDerivAt_binEntropy ha.1.ne' ha.2.ne
  have h2 := (hasDerivAt_binEntropy hb.1.ne' hb.2.ne).comp a (hasDerivAt_binConv a p)
  have h3 := ((h1.neg).const_add ((1 - θ) * log 2)).add (h2.const_mul θ)
  refine (h3.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [dsbsPsi, Pi.add_apply, Pi.neg_apply, Function.comp]
    ring
  · simp only [dsbsDPsi]
    ring

lemma hasDerivAt_dsbsDPsi (hp0 : 0 < p) (hp : p < 1 / 2) (ha : a ∈ Set.Ioo (0 : ℝ) 1) (θ : ℝ) :
    HasDerivAt (dsbsDPsi θ p) (1 / (a * (1 - a)) -
      θ * (1 - 2 * p) ^ 2 / (binConv a p * (1 - binConv a p))) a := by
  have hb := binConv_mem_Ioo hp0 hp ha
  have h1 := hasDerivAt_dH ha
  have h2 := (hasDerivAt_dH hb).comp a (hasDerivAt_binConv a p)
  have h3 := (h1.neg).add ((h2.const_mul (1 - 2 * p)).const_mul θ)
  refine (h3.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [dsbsDPsi, Pi.add_apply, Pi.neg_apply, Function.comp]
  · ring

/-- `a ∗ p (1 - a ∗ p) = p (1 - p) + (1 - 2p)² a (1 - a)`. -/
lemma binConv_mul_one_sub (a p : ℝ) :
    binConv a p * (1 - binConv a p) = p * (1 - p) + (1 - 2 * p) ^ 2 * (a * (1 - a)) := by
  rw [binConv_eq]
  ring

/-- **Lecture 12, pages 12-7 and 12-19.** `ψ` is convex, in particular `D ↦ 1 - H(D)` and
`g(D) = H(p ∗ D) - H(D)`: its second derivative is `1 / (a (1 - a)) - θ t² / (b (1 - b))`, with
`t = 1 - 2p` and `b = a ∗ p`, and `b (1 - b) = p (1 - p) + t² a (1 - a)`. -/
theorem dsbsPsi_convexOn (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (dsbsPsi θ p) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) (f' := dsbsDPsi θ p)
    (f'' := fun a => 1 / (a * (1 - a)) -
      θ * (1 - 2 * p) ^ 2 / (binConv a p * (1 - binConv a p))) ?_ ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    unfold dsbsPsi binConv
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx ⊢
    exact (hasDerivAt_dsbsPsi hp0 hp hx θ).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx ⊢
    exact (hasDerivAt_dsbsDPsi hp0 hp hx θ).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hb := binConv_mem_Ioo hp0 hp hx
    have hx1 : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    have hb1 : 0 < binConv x p * (1 - binConv x p) := mul_pos hb.1 (by linarith [hb.2])
    rw [sub_nonneg, div_le_div_iff₀ hb1 hx1, binConv_mul_one_sub, one_mul]
    have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
    have ht : 0 ≤ (1 - 2 * p) ^ 2 * (x * (1 - x)) := by positivity
    nlinarith [mul_le_of_le_one_left ht hθ1]

/-- **The tangent lines of `ψ` are below `ψ`.** -/
theorem dsbsPsi_tangent (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    dsbsPsi θ p x + dsbsDPsi θ p x * (a - x) ≤ dsbsPsi θ p a := by
  have hc := dsbsPsi_convexOn hθ1 hp0 hp
  have hd := hasDerivAt_dsbsPsi hp0 hp hx θ
  have hxI : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  rcases lt_trichotomy a x with h | rfl | h
  · have h2 := hc.slope_le_of_hasDerivAt ha hxI h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h2
    nlinarith
  · simp
  · have h2 := hc.le_slope_of_hasDerivAt hxI ha h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h2
    nlinarith

/-- The slope of `ψ` is nondecreasing. -/
theorem dsbsDPsi_mono (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hxy : x ≤ y) :
    dsbsDPsi θ p x ≤ dsbsDPsi θ p y := by
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  have h1 := dsbsPsi_tangent hθ1 hp0 hp hx (Set.Ioo_subset_Icc_self hy)
  have h2 := dsbsPsi_tangent hθ1 hp0 hp hy (Set.Ioo_subset_Icc_self hx)
  have h3 : 0 < y - x := by linarith
  have h4 : (dsbsDPsi θ p x - dsbsDPsi θ p y) * (y - x) ≤ 0 := by nlinarith
  by_contra hne
  push Not at hne
  nlinarith [mul_pos (sub_pos.2 hne) h3]

/-! #### The rate–distortion functions -/

/-- **Lecture 12, pages 12-7 and 12-19.** The point of tangency `x` of the line through `(p, 0)`:
`ψ(x) / (p - x) = -ψ'(x)`. -/
def IsDsbsTangency (θ p x : ℝ) : Prop :=
  x ∈ Set.Ioo 0 p ∧ dsbsPsi θ p x = (p - x) * -dsbsDPsi θ p x

/-- For `D ≥ p`, the rate is `0`. -/
theorem sideRD_dsbs_of_le (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp : p ≤ 1) {D : ℝ} (hD : p ≤ D) :
    sideRD θ (dsbsPMF p) hammingDistortion D = 0 :=
  le_antisymm (sideRD_dsbs_le_zero hp0 hp θ hD)
    (sideRD_nonneg (dsbsPMF_isPMF hp0 hp) hθ1 _ D)

/-- A supporting line gives the lower bound on the rate at `D`. -/
private lemma le_sideRD_dsbs (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) {A s : ℝ}
    (hs : 0 ≤ s) (h1 : ∀ c ∈ Set.Icc (0 : ℝ) 1, A - s * c ≤ dsbsPsi θ p c) (h2 : A - s * p ≤ 0)
    {D : ℝ} (hD : 0 ≤ D) : A - s * D ≤ sideRD θ (dsbsPMF p) hammingDistortion D := by
  have hP := dsbsPMF_isPMF hp0 (by linarith : p ≤ 1)
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := θ) hP (minDistortion_dsbs p D hD)
  rw [← he]
  have := line_le_sideRate hθ0 hθ1 hp0 hp hs h1 h2 hq f
  nlinarith [mul_le_mul_of_nonneg_left hc hs]

/-- **Lecture 12, pages 12-7 and 12-19.** For `0 < D ≤ x`, the rate is `ψ(D)`: `1 - H(D)` for causal
side information and `g(D) = H(p ∗ D) - H(D)` for noncausal side information. -/
theorem sideRD_dsbs_eq_psi (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : IsDsbsTangency θ p x) {D : ℝ} (hD0 : 0 < D) (hD : D ≤ x) :
    sideRD θ (dsbsPMF p) hammingDistortion D = dsbsPsi θ p D := by
  obtain ⟨⟨hx0, hxp⟩, htan⟩ := hx
  have hx1 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, by linarith⟩
  have hD1 : D ∈ Set.Ioo (0 : ℝ) 1 := ⟨hD0, by linarith⟩
  refine le_antisymm (sideRD_dsbs_le_psi hp0.le (by linarith) hD0.le hD1.2.le θ le_rfl) ?_
  have hmono := dsbsDPsi_mono hθ1 hp0 hp hD1 hx1 hD
  have hψx := dsbsPsi_nonneg hθ0 hθ1 hp0.le (by linarith) hx0.le hx1.2.le
  have hneg : dsbsDPsi θ p x ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos (sub_pos.2 hxp) h]
  have hs : 0 ≤ -dsbsDPsi θ p D := by linarith
  have ht := dsbsPsi_tangent hθ1 hp0 hp hD1 (Set.Ioo_subset_Icc_self hx1)
  have hline := le_sideRD_dsbs (A := dsbsPsi θ p D + -dsbsDPsi θ p D * D) (D := D) hθ0 hθ1 hp0.le
    hp.le hs (fun c hc => ?_) ?_ hD0.le
  · linarith
  · have := dsbsPsi_tangent hθ1 hp0 hp hD1 hc
    nlinarith
  · have h5 : dsbsDPsi θ p D * (p - x) ≤ dsbsDPsi θ p x * (p - x) :=
      mul_le_mul_of_nonneg_right hmono (by linarith)
    nlinarith

/-- **Lecture 12, pages 12-7 and 12-19.** For `x ≤ D ≤ p`, the rate is `(p - D) (-ψ'(x))`, the
tangent
to `ψ` through `(p, 0)`: time sharing between `U = X ⊕ V` and zero-rate decoding. -/
theorem sideRD_dsbs_eq_line (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : IsDsbsTangency θ p x) {D : ℝ} (hD : x ≤ D) (hDp : D ≤ p) :
    sideRD θ (dsbsPMF p) hammingDistortion D = (p - D) * -dsbsDPsi θ p x := by
  obtain ⟨⟨hx0, hxp⟩, htan⟩ := hx
  have hx1 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, by linarith⟩
  have hP := dsbsPMF_isPMF hp0.le (by linarith : p ≤ 1)
  have hψx := dsbsPsi_nonneg hθ0 hθ1 hp0.le (by linarith) hx0.le hx1.2.le
  have hneg : 0 ≤ -dsbsDPsi θ p x := by
    by_contra h
    push Not at h
    nlinarith [mul_pos (sub_pos.2 hxp) (neg_pos.2 h)]
  have hgap : 0 < p - x := sub_pos.2 hxp
  refine le_antisymm ?_ ?_
  · -- Time sharing.
    have hconv := (sideRD_convexOn (P := dsbsPMF p) (d := hammingDistortion (α := Bool)) hP θ).2
      (show x ∈ Set.Ici _ from minDistortion_dsbs p x hx0.le)
      (show p ∈ Set.Ici _ from minDistortion_dsbs p p hp0.le)
      (show 0 ≤ (p - D) / (p - x) from div_nonneg (by linarith) hgap.le)
      (show 0 ≤ (D - x) / (p - x) from div_nonneg (by linarith) hgap.le)
      (by field_simp; ring)
    simp only [smul_eq_mul] at hconv
    have e : (p - D) / (p - x) * x + (D - x) / (p - x) * p = D := by
      field_simp
      ring
    rw [e] at hconv
    have h1 := sideRD_dsbs_le_psi hp0.le (by linarith : p ≤ 1) hx0.le hx1.2.le θ le_rfl
    have h2 := sideRD_dsbs_of_le hθ1 hp0.le (by linarith : p ≤ 1) (le_refl p)
    rw [h2, mul_zero, add_zero] at hconv
    refine hconv.trans ?_
    calc (p - D) / (p - x) * sideRD θ (dsbsPMF p) hammingDistortion x
        ≤ (p - D) / (p - x) * dsbsPsi θ p x :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (by linarith) hgap.le)
      _ = (p - D) * -dsbsDPsi θ p x := by
          rw [htan]
          field_simp
  · have hline := le_sideRD_dsbs (A := -dsbsDPsi θ p x * p) (D := D) hθ0 hθ1 hp0.le hp.le hneg
      (fun c hc => ?_) (by nlinarith) (hx0.le.trans hD)
    · nlinarith
    · have := dsbsPsi_tangent hθ1 hp0 hp hx1 hc
      nlinarith

/-- **Lecture 12, pages 12-7 and 12-19.** The rate at `D = 0` is `ψ(0)`: `1` for causal side
information
and `H(p)` for noncausal side information. -/
theorem sideRD_dsbs_zero (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : IsDsbsTangency θ p x) :
    sideRD θ (dsbsPMF p) hammingDistortion 0 = dsbsPsi θ p 0 := by
  have hP := dsbsPMF_isPMF hp0.le (by linarith : p ≤ 1)
  refine le_antisymm (sideRD_dsbs_le_psi hp0.le (by linarith) le_rfl zero_le_one θ le_rfl) ?_
  have hanti := sideRD_antitoneOn (P := dsbsPMF p) (d := hammingDistortion (α := Bool)) hP θ
  have hc : Continuous (dsbsPsi θ p) := by
    unfold dsbsPsi binConv
    fun_prop
  have hlim : Tendsto (dsbsPsi θ p) (𝓝[>] 0) (𝓝 (dsbsPsi θ p 0)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hx.1.1] with D hD
  rw [← sideRD_dsbs_eq_psi hθ0 hθ1 hp0 hp hx hD.1 hD.2.le]
  exact hanti (minDistortion_dsbs p 0 le_rfl) (minDistortion_dsbs p D hD.1.le) hD.1.le

/-- `ψ(p) > 0` for `0 < p < 1/2`. -/
lemma dsbsPsi_self_pos (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) :
    0 < dsbsPsi θ p p := by
  have h1 : binEntropy p < log 2 := binEntropy_lt_log_two.2 (by
    intro h
    rw [h] at hp
    norm_num at hp)
  have hb : binConv p p ≤ 2⁻¹ := by
    have := sq_nonneg (1 - 2 * p)
    unfold binConv
    nlinarith
  have h2 : binEntropy p < binEntropy (binConv p p) :=
    binEntropy_strictMonoOn ⟨hp0.le, by linarith⟩ ⟨by unfold binConv; nlinarith, hb⟩ (by
      unfold binConv
      nlinarith)
  have e : dsbsPsi θ p p = (1 - θ) * (log 2 - binEntropy p) +
      θ * (binEntropy (binConv p p) - binEntropy p) := by
    simp only [dsbsPsi]
    ring
  rw [e]
  rcases hθ0.eq_or_lt with rfl | hθ
  · linarith
  · have h3 : 0 ≤ (1 - θ) * (log 2 - binEntropy p) := mul_nonneg (by linarith) (by linarith)
    have h4 := mul_pos hθ (sub_pos.2 h2)
    linarith

/-- **Lecture 12, pages 12-7 and 12-19.** The point of tangency exists, by the intermediate value
theorem: `ψ(x) + (p - x) ψ'(x)` tends to `-∞` at `0` and is positive at `p`. -/
theorem exists_isDsbsTangency (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 < p) (hp : p < 1 / 2) :
    ∃ x, IsDsbsTangency θ p x := by
  set F : ℝ → ℝ := fun a => dsbsPsi θ p a + (p - a) * dsbsDPsi θ p a with hF
  have hFeq : ∀ a, IsDsbsTangency θ p a ↔ a ∈ Set.Ioo 0 p ∧ F a = 0 := fun a => by
    simp only [IsDsbsTangency, hF]
    constructor
    · rintro ⟨h, h2⟩
      exact ⟨h, by rw [h2]; ring⟩
    · rintro ⟨h, h2⟩
      exact ⟨h, by linarith⟩
  -- The behaviour at `0`.
  have hbound : ContinuousAt (fun a => dsbsPsi θ p a + (p - a) * (-log (1 - a) +
      θ * ((1 - 2 * p) * (log (1 - binConv a p) - log (binConv a p))))) 0 := by
    have hb0 : binConv 0 p = p := by unfold binConv; ring
    have hcb : Continuous fun a => binConv a p := by
      unfold binConv
      fun_prop
    have hψ : Continuous (dsbsPsi θ p) := by
      unfold dsbsPsi binConv
      fun_prop
    refine hψ.continuousAt.add (ContinuousAt.mul (by fun_prop) (ContinuousAt.add ?_ ?_))
    · exact (continuousAt_log (by norm_num)).comp (f := fun a => 1 - a) (by fun_prop) |>.neg
    · refine continuousAt_const.mul (continuousAt_const.mul (ContinuousAt.sub ?_ ?_))
      · exact ContinuousAt.log (by fun_prop) (by rw [hb0]; linarith)
      · exact ContinuousAt.log hcb.continuousAt (by rw [hb0]; exact hp0.ne')
  have hlogp : Tendsto (fun a => (p - a) * log a) (𝓝[>] 0) atBot := by
    have h1 : Tendsto (fun a : ℝ => p - a) (𝓝[>] 0) (𝓝 p) := by
      have : Tendsto (fun a : ℝ => p - a) (𝓝 0) (𝓝 (p - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact h1.pos_mul_atBot hp0 tendsto_log_nhdsGT_zero
  have hsum : Tendsto F (𝓝[>] 0) atBot := by
    have h2 := hlogp.atBot_add ((hbound.tendsto).mono_left nhdsWithin_le_nhds)
    refine h2.congr' ?_
    filter_upwards with a
    simp only [hF, dsbsDPsi]
    ring
  obtain ⟨a₀, hFa₀, ha₀⟩ := ((hsum.eventually (eventually_lt_atBot 0)).and
    (eventually_mem_set.2 (Ioo_mem_nhdsGT hp0))).exists
  -- The intermediate value theorem.
  have hF0 : F p = dsbsPsi θ p p := by simp [hF]
  have hcont : ContinuousOn F (Set.Icc a₀ p) := by
    intro a ha
    have ha' : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha₀.1.trans_le ha.1, by linarith [ha.2]⟩
    have h1 := (hasDerivAt_dsbsPsi hp0 hp ha' θ).continuousAt
    have h2 := (hasDerivAt_dsbsDPsi hp0 hp ha' θ).continuousAt
    exact (h1.add ((continuousAt_const.sub continuousAt_id).mul h2)).continuousWithinAt
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc ha₀.2.le hcont
    (show (0 : ℝ) ∈ Set.Icc (F a₀) (F p) from ⟨hFa₀.le, by
      rw [hF0]
      exact (dsbsPsi_self_pos hθ0 hθ1 hp0 hp).le⟩)
  have hxp : x ≠ p := by
    rintro rfl
    rw [hF0] at hFx
    exact (dsbsPsi_self_pos hθ0 hθ1 hp0 hp).ne' hFx
  exact ⟨x, (hFeq x).2 ⟨⟨ha₀.1.trans_le hx.1, lt_of_le_of_ne hx.2 hxp⟩, hFx⟩⟩

/-- **Lecture 12, page 12-7.** For a `DSBS(p)` and the Hamming distortion, with the point of
tangency
`D_c`, `R_CSI-D(D) = 1 - H(D)` for `0 ≤ D ≤ D_c`, in nats. By `rateCausalBits_eq`, the rate in bits
is
this value divided by `log 2`. -/
theorem causalRD_dsbs_of_le_tangency (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : IsDsbsTangency 0 p x) {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ x) :
    causalRD (dsbsPMF p) hammingDistortion D = log 2 - binEntropy D := by
  have e : dsbsPsi 0 p D = log 2 - binEntropy D := by
    simp only [dsbsPsi]
    ring
  rw [← e]
  rcases hD0.eq_or_lt with rfl | h
  · exact sideRD_dsbs_zero le_rfl zero_le_one hp0 hp hx
  · exact sideRD_dsbs_eq_psi le_rfl zero_le_one hp0 hp hx h hD

/-- **Lecture 12, page 12-7.** For a `DSBS(p)` and the Hamming distortion,
`R_CSI-D(D) = (p - D) H'(D_c)` for `D_c ≤ D ≤ p`, in nats. -/
theorem causalRD_dsbs_of_tangency_le (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : IsDsbsTangency 0 p x) {D : ℝ} (hD : x ≤ D) (hDp : D ≤ p) :
    causalRD (dsbsPMF p) hammingDistortion D = (p - D) * (log (1 - x) - log x) := by
  have e : -dsbsDPsi 0 p x = log (1 - x) - log x := by
    simp only [dsbsDPsi]
    ring
  rw [← e]
  exact sideRD_dsbs_eq_line le_rfl zero_le_one hp0 hp hx hD hDp

/-- The value of `ψ` for `θ = 1`: `g(D) = H(p ∗ D) - H(D)`. -/
lemma dsbsPsi_one (p D : ℝ) : dsbsPsi 1 p D = binEntropy (binConv D p) - binEntropy D := by
  simp only [dsbsPsi]
  ring

/-- **Lecture 12, page 12-19.** For a `DSBS(p)` and the Hamming distortion, with the point of
tangency
`D'_c`, `R_SI-D(D) = g(D) = H(p ∗ D) - H(D)` for `0 ≤ D ≤ D'_c`, in nats. By `rateWZBits_eq`, the
rate in
bits is this value divided by `log 2`. -/
theorem wzRD_dsbs_of_le_tangency (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : IsDsbsTangency 1 p x) {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ x) :
    wzRD (dsbsPMF p) hammingDistortion D = binEntropy (binConv D p) - binEntropy D := by
  rw [← dsbsPsi_one]
  rcases hD0.eq_or_lt with rfl | h
  · exact sideRD_dsbs_zero zero_le_one le_rfl hp0 hp hx
  · exact sideRD_dsbs_eq_psi zero_le_one le_rfl hp0 hp hx h hD

/-- **Lecture 12, page 12-19.** For a `DSBS(p)` and the Hamming distortion,
`R_SI-D(D) = (p - D) (-g'(D'_c))` for `D'_c ≤ D ≤ p`, in nats. The notes omit the sign. -/
theorem wzRD_dsbs_of_tangency_le (hp0 : 0 < p) (hp : p < 1 / 2) {x : ℝ}
    (hx : IsDsbsTangency 1 p x) {D : ℝ} (hD : x ≤ D) (hDp : D ≤ p) :
    wzRD (dsbsPMF p) hammingDistortion D = (p - D) * -dsbsDPsi 1 p x :=
  sideRD_dsbs_eq_line zero_le_one le_rfl hp0 hp hx hD hDp

/-! #### Side information at both ends -/

/-- The law of `((Z, Ẑ), Y)` with `Y` uniform and independent of `(Z, Ẑ)`, and the map to
`((X, Y), X̂) = ((Z ⊕ Y, Y), Ẑ ⊕ Y)`. -/
private def bothMap (ω : (Bool × Bool) × Bool) : (Bool × Bool) × Bool :=
  ((xor ω.1.1 ω.2, ω.2), xor ω.1.2 ω.2)

private lemma bothMap_bijective : Function.Bijective bothMap := by
  refine ⟨?_, fun t => ⟨((xor t.1.1 t.1.2, xor t.2 t.1.2), t.1.2), ?_⟩⟩
  · rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
    revert h
    cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> simp [bothMap]
  · obtain ⟨⟨a, b⟩, c⟩ := t
    cases a <;> cases b <;> cases c <;> simp [bothMap]

/-- The kernel `p(x̂ | x, y) = r(x̂ ⊕ y | x ⊕ y)`. -/
def bothKernel (r : Bool → Bool → ℝ) (a : Bool × Bool) (b : Bool) : ℝ :=
  r (xor a.1 a.2) (xor b a.2)

lemma bothKernel_isChannel {r : Bool → Bool → ℝ} (hr : IsChannel r) : IsChannel (bothKernel r) :=
  fun ⟨x, y⟩ => by
    refine ⟨fun b => (hr _).nonneg _, ?_⟩
    have h := (hr (xor x y)).sum_eq_one
    rw [Fintype.sum_bool] at h ⊢
    cases y
    · simpa [bothKernel] using h
    · simp only [bothKernel, Bool.xor_true, Bool.not_true, Bool.not_false] at h ⊢
      linarith

variable {r' : Bool → Bool → ℝ}

/-- `bothLaw` is the image of the law of `((Z, Ẑ), Y)`. -/
private lemma bothLaw_eq_dist :
    bothLaw (dsbsPMF p) (bothKernel r') =
      dist (mixLaw (jointOf (bernoulliPMF p) r') Bool) bothMap := by
  classical
  funext t
  obtain ⟨ω, rfl⟩ := bothMap_bijective.2 t
  have h := dist_comp_of_injective (mixLaw (jointOf (bernoulliPMF p) r') Bool) id
    bothMap_bijective.1 ω
  rw [dist_id] at h
  refine Eq.trans ?_ h.symm
  obtain ⟨⟨z, c⟩, y⟩ := ω
  simp only [bothMap, jointOf, mixLaw, prodDist, uniformPMF, bothKernel, dsbsPMF, Fintype.card_bool]
  cases y <;> simp <;> ring

/-- The entropy of `(Y, g_Y(F))` under the law of `((Z, Ẑ), Y)`. -/
private lemma entropyRV_mix_bool {μ : Bool × Bool → ℝ} (hμ : IsPMF μ) {τ σ : Type*} [Fintype τ]
    [Fintype σ] (F : Bool × Bool → τ) (g : Bool → τ → σ) (hg : ∀ y, Function.Injective (g y)) :
    H[fun ω : (Bool × Bool) × Bool => (ω.2, g ω.2 (F ω.1)) ; mixLaw μ Bool] =
      log 2 + H[F ; μ] := by
  have h := entropyRV_mix hμ (ι := Bool) (b := fun _ => τ) fun _ => F
  simp only [Fintype.sum_bool, Fintype.card_bool] at h
  have e : H[fun ω : (Bool × Bool) × Bool => (ω.2, g ω.2 (F ω.1)) ; mixLaw μ Bool] =
      H[fun z : (Bool × Bool) × Bool => (⟨z.2, F z.1⟩ : Σ _ : Bool, τ) ; mixLaw μ Bool] := by
    refine entropyRV_eq_of_injective _ (fun s : Σ _ : Bool, τ => (s.1, g s.1 s.2)) ?_ fun _ => rfl
    rintro ⟨y, a⟩ ⟨y', a'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [hg y h2]
  rw [e, h]
  push_cast
  norm_num
  ring

/-- **Lecture 12, page 12-7.** The rate of `p(x̂ | x, y) = r(x̂ ⊕ y | x ⊕ y)` is `I(Z; Ẑ)`, where
`Z = X ⊕ Y`, because `(Z, Ẑ)` is independent of `Y`. -/
theorem bothRate_bothKernel (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : IsChannel r') :
    bothRate (dsbsPMF p) (bothKernel r') = mutualInfoOf (bernoulliPMF p) r' := by
  classical
  have hP := dsbsPMF_isPMF hp0 hp1
  have hb := bernoulliPMF_isPMF hp0 hp1
  have hμ₂ : IsPMF (jointOf (bernoulliPMF p) r') := jointOf_isPMF hb hr
  have hμ : IsPMF (bothLaw (dsbsPMF p) (bothKernel r')) :=
    jointOf_isPMF hP (bothKernel_isChannel hr)
  have hxor : ∀ y : Bool, Function.Injective fun z : Bool => xor z y := fun y a b h => by
    revert h
    cases a <;> cases b <;> cases y <;> simp
  rw [bothRate, condMutualInfo_eq hμ]
  have key : ∀ {τ : Type _} [Fintype τ] (A : (Bool × Bool) × Bool → τ),
      H[A ; bothLaw (dsbsPMF p) (bothKernel r')] =
        H[A ∘ bothMap ; mixLaw (jointOf (bernoulliPMF p) r') Bool] := fun A => by
    rw [entropyRV, bothLaw_eq_dist, ← dist_comp_eq]
    rfl
  have e1 := entropyRV_mix_bool hμ₂ Prod.fst (fun y z => xor z y) hxor
  have e2 := entropyRV_mix_bool hμ₂ Prod.snd (fun y z => xor z y) hxor
  have e3 := entropyRV_mix_bool hμ₂ (id : Bool × Bool → Bool × Bool)
    (fun y z => (xor z.1 y, xor z.2 y)) fun y a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (hxor y h.1) (hxor y h.2)
  have e4 : H[fun ω : (Bool × Bool) × Bool => ω.2 ; mixLaw (jointOf (bernoulliPMF p) r') Bool] =
      log 2 := by
    have h := entropyRV_mix_bool hμ₂ (fun _ => ()) (fun _ _ => ()) fun _ _ _ _ => rfl
    have h2 : H[fun _ : Bool × Bool => () ; jointOf (bernoulliPMF p) r'] = 0 := by
      have h3 := entropyRV_le_log_card hμ₂ fun _ : Bool × Bool => ()
      have h4 := entropy_nonneg (hμ₂.dist fun _ : Bool × Bool => ())
      simp only [Fintype.card_unit, Nat.cast_one, log_one] at h3
      exact le_antisymm h3 h4
    rw [h2, add_zero] at h
    rw [← h]
    refine entropyRV_eq_of_injective _ (Prod.fst : Bool × Unit → Bool) ?_ fun _ => rfl
    rintro ⟨a, _⟩ ⟨b, _⟩ h
    exact Prod.ext h rfl
  have k1 : H[pair (fun z : (Bool × Bool) × Bool => z.1.2) (fun z => z.1.1) ;
      bothLaw (dsbsPMF p) (bothKernel r')] = log 2 + H[Prod.fst ; jointOf (bernoulliPMF p) r'] :=
    (key _).trans e1
  have k2 : H[pair (fun z : (Bool × Bool) × Bool => z.1.2) Prod.snd ;
      bothLaw (dsbsPMF p) (bothKernel r')] = log 2 + H[Prod.snd ; jointOf (bernoulliPMF p) r'] :=
    (key _).trans e2
  have k3 : H[fun z : (Bool × Bool) × Bool => z.1.2 ; bothLaw (dsbsPMF p) (bothKernel r')] =
      log 2 := (key _).trans e4
  have k4 : H[pair (fun z : (Bool × Bool) × Bool => z.1.2)
      (pair (fun z => z.1.1) Prod.snd) ; bothLaw (dsbsPMF p) (bothKernel r')] =
      log 2 + H[id ; jointOf (bernoulliPMF p) r'] := (key _).trans e3
  rw [k1, k2, k3, k4, mutualInfoOf, mutualInfo_eq_add_sub hμ₂]
  have e5 : H[pair Prod.fst Prod.snd ; jointOf (bernoulliPMF p) r'] =
      H[id ; jointOf (bernoulliPMF p) r'] := rfl
  rw [e5]
  ring

/-- The distortion of `p(x̂ | x, y) = r(x̂ ⊕ y | x ⊕ y)` is `E d(Z, Ẑ)`. -/
lemma sum_bothKernel_distortion :
    ∑ z, bothLaw (dsbsPMF p) (bothKernel r') z * hammingDistortion z.1.1 z.2 =
      expDistortion (bernoulliPMF p) r' hammingDistortion := by
  classical
  rw [bothLaw_eq_dist, sum_dist_mul (mixLaw (jointOf (bernoulliPMF p) r') Bool) bothMap
    fun z => hammingDistortion z.1.1 z.2, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, bothMap, mixLaw, prodDist, uniformPMF, Fintype.card_bool,
    expDistortion, jointOf, hammingDistortion_bool, Fintype.sum_prod_type]
  simp
  ring

/-- **Lecture 12, page 12-7.** The lower bound with side information at both ends:
`I(X; X̂ | Y) = H(X | Y) - H(X | X̂, Y) ≥ H(p) - H(X ⊕ X̂) ≥ H(p) - H(D)`. -/
theorem binEntropy_sub_le_bothRate (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : Bool × Bool → Bool → ℝ}
    (hq : IsChannel q) {D : ℝ}
    (hD : ∑ z, bothLaw (dsbsPMF p) q z * hammingDistortion z.1.1 z.2 ≤ D) (hD2 : D ≤ 1 / 2) :
    binEntropy p - binEntropy D ≤ bothRate (dsbsPMF p) q := by
  classical
  have hP := dsbsPMF_isPMF hp0 hp1
  have hμ : IsPMF (bothLaw (dsbsPMF p) q) := jointOf_isPMF hP hq
  set μ := bothLaw (dsbsPMF p) q with hμd
  set X : (Bool × Bool) × Bool → Bool := fun z => z.1.1
  set Y : (Bool × Bool) × Bool → Bool := fun z => z.1.2
  set Xh : (Bool × Bool) × Bool → Bool := Prod.snd
  set Z : (Bool × Bool) × Bool → Bool := fun z => xor z.1.1 z.2
  have hcond : H[X | Xh ; μ] = H[Z | Xh ; μ] := by
    rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
    congr 1
    refine (entropyRV_eq_of_injective μ (fun z : Bool × Bool => (z.1, xor z.2 z.1)) ?_
      fun ω => ?_).symm
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all
    · simp only [pair, X, Z, Xh]
  set t := dist μ Z true
  have ht : t = ∑ z, μ z * hammingDistortion z.1.1 z.2 := by
    have h := sum_dist_mul μ Z fun b => if b then (1 : ℝ) else 0
    rw [Fintype.sum_bool] at h
    simp only [↓reduceIte, mul_one, Bool.false_eq_true, mul_zero, add_zero] at h
    change dist μ Z true = _
    rw [h]
    exact sum_congr rfl fun z _ => by rw [hammingDistortion_bool]
  have ht0 : 0 ≤ t := dist_nonneg hμ Z true
  have htD : t ≤ D := ht ▸ hD
  have hZ : H[Z ; μ] = binEntropy t := by
    rw [entropyRV, dist_eq_bernoulliPMF hμ Z, entropy_bernoulliPMF]
  have hmono : binEntropy t ≤ binEntropy D :=
    binEntropy_strictMonoOn.monotoneOn ⟨ht0, by linarith⟩ ⟨ht0.trans htD, by linarith⟩ htD
  have hXY : H[X | Y ; μ] = binEntropy p := by
    rw [← condEntropy_dsbsPMF hp0 hp1]
    refine condEntropy_eq_of_dist_pair_eq hμ hP ?_
    rw [show pair Y X = (pair Prod.snd Prod.fst) ∘ (Prod.fst : (Bool × Bool) × Bool → _) from rfl,
      dist_comp_eq, dist_jointOf_fst hq]
  have hle1 : H[X | pair Xh Y ; μ] ≤ H[X | Xh ; μ] :=
    condEntropy_le_condEntropy_comp hμ X (pair Xh Y) Prod.fst
  have hle2 := condEntropy_le_entropy hμ Z Xh
  rw [bothRate, condMutualInfo, hXY]
  linarith

/-- **Lecture 12, page 12-7.** For a `DSBS(p)` and the Hamming distortion,
`R_SI-ED(D) = H(p) - H(D)` for `0 ≤ D ≤ p`, in nats. By `rateBothBits_eq`, the rate in bits is this
value
divided by `log 2`. -/
theorem bothRD_dsbs (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ p) :
    bothRD (dsbsPMF p) hammingDistortion D = binEntropy p - binEntropy D := by
  classical
  have hp1 : p ≤ 1 := by linarith
  have hP := dsbsPMF_isPMF hp0 hp1
  have hb := bernoulliPMF_isPMF hp0 hp1
  have hmin : D ≤ min p (1 - p) := le_min hD (by linarith)
  have hDm : minDistortion (bernoulliPMF p) (hammingDistortion (α := Bool)) ≤ D := by
    rw [minDistortion_hammingDistortion]
    exact hD0
  obtain ⟨r, hr, hc, he⟩ := exists_infoRD_eq hb hDm
  rw [infoRD_bernoulli hp0 hp1 hD0, ite_eq_left hmin] at he
  have hq := bothKernel_isChannel hr
  have hc' : ∑ z, bothLaw (dsbsPMF p) (bothKernel r) z * hammingDistortion z.1.1 z.2 ≤ D := by
    rw [sum_bothKernel_distortion]
    exact hc
  refine le_antisymm ?_ (le_csInf ⟨_, bothKernel r, hq, hc', rfl⟩ ?_)
  · refine (csInf_le (bothRD_set_bddBelow hP _ D) ⟨bothKernel r, hq, hc', rfl⟩).trans (le_of_eq ?_)
    rw [bothRate_bothKernel hp0 hp1 hr, he]
  · rintro _ ⟨q, hq', hc'', rfl⟩
    exact binEntropy_sub_le_bothRate hp0 hp1 hq' hc'' (by linarith)

/-- For `D ≥ p`, the rate with side information at both ends is `0`. -/
theorem bothRD_dsbs_of_le (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) {D : ℝ} (hD : p ≤ D) :
    bothRD (dsbsPMF p) hammingDistortion D = 0 := by
  have hp1 : p ≤ 1 := by linarith
  have hP := dsbsPMF_isPMF hp0 hp1
  refine le_antisymm ?_ (Real.sInf_nonneg ?_)
  · have h1 := bothRD_le_wzRD (d := hammingDistortion (α := Bool)) hP
      (minDistortion_dsbs p D (hp0.trans hD))
    have h2 := sideRD_dsbs_of_le (θ := 1) le_rfl hp0 hp1 hD
    exact h1.trans h2.le
  · rintro _ ⟨q, hq, -, rfl⟩
    exact condMutualInfo_nonneg (jointOf_isPMF hP hq) _ _ _

/-- **Lecture 12, page 12-19.** There is a nonzero cost for the lack of side information at the
encoder:
`R_SI-ED(D) < R_SI-D(D)` for `0 < D < p`. The notes write the inequality the other way round. -/
theorem bothRD_lt_wzRD_dsbs (hp0 : 0 < p) (hp : p < 1 / 2) {D : ℝ} (hD0 : 0 < D) (hD : D < p) :
    bothRD (dsbsPMF p) hammingDistortion D < wzRD (dsbsPMF p) hammingDistortion D := by
  have hphalf : p ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨hp0.le, by norm_num; linarith⟩
  have hgap : ∀ a, 0 < a → a < p → binEntropy p < binEntropy (binConv a p) := fun a h0 h1 => by
    have hm := binConv_mem_Icc_half (a := a) ⟨h0.le, by norm_num; linarith⟩ hphalf
    have hlt : p < binConv a p := by
      rw [binConv_eq]
      nlinarith
    exact binEntropy_strictMonoOn hphalf ⟨hp0.le.trans hlt.le, hm.2⟩ hlt
  obtain ⟨x, hx⟩ := exists_isDsbsTangency (θ := 1) zero_le_one le_rfl hp0 hp
  rw [bothRD_dsbs hp0.le hp.le hD0.le hD.le]
  rcases le_total D x with h | h
  · rw [wzRD_dsbs_of_le_tangency hp0 hp hx hD0.le h]
    linarith [hgap D hD0 hD]
  · rw [wzRD_dsbs_of_tangency_le hp0 hp hx h hD.le]
    obtain ⟨⟨hx0, hxp⟩, htan⟩ := hx
    have hgx := hgap x hx0 hxp
    rw [dsbsPsi_one] at htan
    have hpx : 0 < p - x := sub_pos.2 hxp
    have hpD : 0 < p - D := sub_pos.2 hD
    -- The concavity of `H`.
    have hconc := strictConcave_binEntropy.concaveOn.2
      (show x ∈ Set.Icc (0 : ℝ) 1 from ⟨hx0.le, by linarith⟩)
      (show p ∈ Set.Icc (0 : ℝ) 1 from ⟨hp0.le, by linarith⟩)
      (show 0 ≤ (p - D) / (p - x) from (div_pos hpD hpx).le)
      (show 0 ≤ (D - x) / (p - x) from div_nonneg (by linarith) hpx.le)
      (by field_simp; ring)
    simp only [smul_eq_mul] at hconc
    have e : (p - D) / (p - x) * x + (D - x) / (p - x) * p = D := by
      field_simp
      ring
    rw [e] at hconc
    have h1 : (p - D) * -dsbsDPsi 1 p x =
        (p - D) / (p - x) * (binEntropy (binConv x p) - binEntropy x) := by
      rw [htan]
      field_simp
    rw [h1]
    have h2 : (p - D) / (p - x) * (binEntropy p - binEntropy x) <
        (p - D) / (p - x) * (binEntropy (binConv x p) - binEntropy x) :=
      mul_lt_mul_of_pos_left (by linarith) (div_pos hpD hpx)
    have h3 : (p - D) / (p - x) + (D - x) / (p - x) = 1 := by
      field_simp
      ring
    have h4 : binEntropy p = ((p - D) / (p - x) + (D - x) / (p - x)) * binEntropy p := by
      rw [h3, one_mul]
    nlinarith

end DSBS

end InfoTheory.ElGamalKim
