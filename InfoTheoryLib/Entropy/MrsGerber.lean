/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.Probability.Independence
public import InfoTheoryLib.Probability.RandomVector
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Mrs. Gerber's lemma

Let `X` be a binary random variable, `U` an arbitrary random variable, and `Z ∼ Bern(p)`
independent of `(X, U)`. Mrs. Gerber's lemma (Wyner and Ziv) lower bounds the conditional entropy
of `Y = X ⊕ Z` in terms of that of `X`:
`H(Y|U) ≥ H(H⁻¹(H(X|U)) ∗ p)`, where `H` is the binary entropy function, `H⁻¹ : [0, 1] → [0, 1/2]`
its inverse and `a ∗ p = a(1 - p) + (1 - a)p` the binary convolution. The lemma follows from
Jensen's inequality and the convexity of `v ↦ H(H⁻¹(v) ∗ p)`.

The convexity is the analytic heart of the lemma. Writing `v = H(a)` with `a ∈ [0, 1/2]` and
`F(a) = H(a ∗ p)`, the slopes of `v ↦ F(H⁻¹(v))` are, by Cauchy's mean value theorem, values of
the ratio `F'(a)/H'(a) = (1 - 2p) ℓ(a ∗ p)/ℓ(a)`, where `ℓ(t) = log (1 - t) - log t`. This ratio
is nondecreasing in `a`: both `ℓ(a ∗ p)` and `ℓ(a)` vanish at `a = 1/2`, so by Cauchy's mean value
theorem again it suffices that the ratio of their derivatives,
`(1 - 2p) a(1 - a)/((a ∗ p)(1 - a ∗ p))`, is nondecreasing, which is an algebraic inequality.

## Main definitions

* `binConv a p`: the binary convolution `a ∗ p`.
* `binEntropyInv v`: the inverse `H⁻¹(v) ∈ [0, 1/2]` of the binary entropy function.
* `mrsGerber p v`: the function `H(H⁻¹(v) ∗ p)`.

## Main statements

* `mrsGerber_convexOn`, `mrsGerber_monotoneOn`: `v ↦ H(H⁻¹(v) ∗ p)` is convex and nondecreasing
  on `[0, log 2]` (Lecture 2 of [elgamal2010]).
* `mrsGerber_le_condEntropy_xor`: **Mrs. Gerber's lemma**, scalar form.
* `mrsGerber_le_condEntropy_xor_prefixRV`: **Mrs. Gerber's lemma**, vector form.
* `binConv_binEntropyInv_le`, `binConv_binEntropyInv_le_prefixRV`: the same in the form
  `H⁻¹(H(Y|U)) ≥ H⁻¹(H(X|U)) ∗ p` of the lecture notes, for `p ≤ 1/2`.
* `entropy_bool`: the entropy of a pmf on `Bool` is a binary entropy.

## Implementation notes

Entropies are in nats, so `H⁻¹` is defined on `[0, log 2]`. The statements are homogeneous in the
base of the logarithm, so they are the notes' statements in bits.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 2
* [A. D. Wyner and J. Ziv, *A theorem on the entropy of certain binary sequences and
  applications*][wyner1973]
-/

open Real Set Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Binary convolution -/

/-- The binary convolution `a ∗ p = a(1 - p) + (1 - a)p`: the probability that `X ⊕ Z = 1` for
independent `X ∼ Bern(a)` and `Z ∼ Bern(p)`. -/
def binConv (a p : ℝ) : ℝ := a * (1 - p) + (1 - a) * p

lemma binConv_eq (a p : ℝ) : binConv a p = p + (1 - 2 * p) * a := by unfold binConv; ring

lemma binConv_one_sub_left (a p : ℝ) : binConv (1 - a) p = 1 - binConv a p := by
  unfold binConv; ring

lemma binConv_one_sub_right (a p : ℝ) : binConv a (1 - p) = 1 - binConv a p := by
  unfold binConv; ring

lemma binEntropy_binConv_one_sub_left (a p : ℝ) :
    binEntropy (binConv (1 - a) p) = binEntropy (binConv a p) := by
  rw [binConv_one_sub_left, binEntropy_one_sub]

lemma binConv_half_right (a : ℝ) : binConv a 2⁻¹ = 2⁻¹ := by unfold binConv; ring

lemma binConv_half_left (p : ℝ) : binConv 2⁻¹ p = 2⁻¹ := by unfold binConv; ring

/-! ### The inverse of the binary entropy function -/

/-- The inverse `H⁻¹ : [0, log 2] → [0, 1/2]` of the binary entropy function restricted to
`[0, 1/2]`. -/
def binEntropyInv (v : ℝ) : ℝ := Function.invFunOn binEntropy (Icc 0 2⁻¹) v

lemma exists_binEntropy_eq {v : ℝ} (hv : v ∈ Icc 0 (log 2)) :
    ∃ a ∈ Icc (0 : ℝ) 2⁻¹, binEntropy a = v := by
  have h := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    binEntropy_continuous.continuousOn
  rw [binEntropy_zero, binEntropy_two_inv] at h
  exact h hv

lemma binEntropyInv_mem {v : ℝ} (hv : v ∈ Icc 0 (log 2)) : binEntropyInv v ∈ Icc 0 2⁻¹ :=
  (Function.invFunOn_pos (exists_binEntropy_eq hv)).1

lemma binEntropy_binEntropyInv {v : ℝ} (hv : v ∈ Icc 0 (log 2)) :
    binEntropy (binEntropyInv v) = v :=
  (Function.invFunOn_pos (exists_binEntropy_eq hv)).2

lemma binEntropy_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) : binEntropy a ∈ Icc 0 (log 2) :=
  ⟨binEntropy_nonneg ha.1 ha.2, binEntropy_le_log_two⟩

lemma binEntropyInv_binEntropy {a : ℝ} (ha : a ∈ Icc 0 2⁻¹) : binEntropyInv (binEntropy a) = a :=
  binEntropy_strictMonoOn.injOn
    (binEntropyInv_mem (binEntropy_mem_Icc ⟨ha.1, ha.2.trans (by norm_num)⟩)) ha
    (binEntropy_binEntropyInv (binEntropy_mem_Icc ⟨ha.1, ha.2.trans (by norm_num)⟩))

lemma binEntropyInv_strictMonoOn : StrictMonoOn binEntropyInv (Icc 0 (log 2)) := by
  intro v hv w hw hvw
  by_contra h
  push Not at h
  have := binEntropy_strictMonoOn.monotoneOn (binEntropyInv_mem hw) (binEntropyInv_mem hv) h
  rw [binEntropy_binEntropyInv hv, binEntropy_binEntropyInv hw] at this
  linarith

/-- `H(H⁻¹(H(a)) ∗ p) = H(a ∗ p)` for `a ∈ [0, 1]`, since `H⁻¹(H(a)) = min(a, 1 - a)`. -/
lemma binEntropy_binConv_binEntropyInv {a : ℝ} (ha : a ∈ Icc 0 1) (p : ℝ) :
    binEntropy (binConv (binEntropyInv (binEntropy a)) p) = binEntropy (binConv a p) := by
  rcases le_total a 2⁻¹ with h | h
  · rw [binEntropyInv_binEntropy ⟨ha.1, h⟩]
  · rw [← binEntropy_one_sub a, binEntropyInv_binEntropy ⟨by linarith [ha.2], by linarith⟩,
      binEntropy_binConv_one_sub_left]

/-! ### The function `H(H⁻¹(v) ∗ p)` -/

/-- The function `v ↦ H(H⁻¹(v) ∗ p)` of Mrs. Gerber's lemma. -/
def mrsGerber (p v : ℝ) : ℝ := binEntropy (binConv (binEntropyInv v) p)

lemma mrsGerber_one_sub (p : ℝ) : mrsGerber (1 - p) = mrsGerber p := by
  funext v
  rw [mrsGerber, mrsGerber, binConv_one_sub_right, binEntropy_one_sub]

/-- For `p ≤ 1/2`, `a ↦ a ∗ p` maps `[0, 1/2]` into `[0, 1/2]`, monotonically. -/
lemma binConv_mem_Icc_half {a p : ℝ} (ha : a ∈ Icc 0 2⁻¹) (hp : p ∈ Icc 0 2⁻¹) :
    binConv a p ∈ Icc 0 2⁻¹ := by
  rw [binConv_eq]
  constructor <;> nlinarith [ha.1, ha.2, hp.1, hp.2]

lemma mrsGerber_monotoneOn_of_le_half {p : ℝ} (hp : p ∈ Icc 0 2⁻¹) :
    MonotoneOn (mrsGerber p) (Icc 0 (log 2)) := by
  intro v hv w hw hvw
  have hab := binEntropyInv_strictMonoOn.monotoneOn hv hw hvw
  refine binEntropy_strictMonoOn.monotoneOn (binConv_mem_Icc_half (binEntropyInv_mem hv) hp)
    (binConv_mem_Icc_half (binEntropyInv_mem hw) hp) ?_
  rw [binConv_eq, binConv_eq]
  nlinarith [hp.2]

/-- `v ↦ H(H⁻¹(v) ∗ p)` is nondecreasing on `[0, log 2]` for `p ∈ [0, 1]`. -/
theorem mrsGerber_monotoneOn {p : ℝ} (hp : p ∈ Icc 0 1) :
    MonotoneOn (mrsGerber p) (Icc 0 (log 2)) := by
  rcases le_total p 2⁻¹ with h | h
  · exact mrsGerber_monotoneOn_of_le_half ⟨hp.1, h⟩
  · have := mrsGerber_monotoneOn_of_le_half (p := 1 - p) ⟨by linarith [hp.2], by linarith⟩
    rwa [mrsGerber_one_sub] at this

/-! ### Convexity -/

section Convexity

/-- `ℓ(t) = log (1 - t) - log t`, the derivative of the binary entropy function. -/
private def ell (t : ℝ) : ℝ := log (1 - t) - log t

private lemma hasDerivAt_ell {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt ell (-((1 - t)⁻¹ + t⁻¹)) t := by
  have hA := ((hasDerivAt_id t).const_sub 1).log (sub_ne_zero.2 h1.ne')
  have hB := (hasDerivAt_id t).log h0.ne'
  have hC := hA.sub hB
  simp only [id_eq] at hC
  rw [show ell = (fun y => log (1 - y)) - fun y => log y from funext fun y => rfl]
  exact hC.congr_deriv (by ring)

private lemma continuousOn_ell : ContinuousOn ell (Ioo 0 1) :=
  ((continuousOn_const.sub continuousOn_id).log
    fun t (ht : t ∈ Ioo (0 : ℝ) 1) => sub_ne_zero.2 ht.2.ne').sub
    (continuousOn_id.log fun t (ht : t ∈ Ioo (0 : ℝ) 1) => ht.1.ne')

private lemma ell_half : ell 2⁻¹ = 0 := by norm_num [ell]

private lemma ell_pos {t : ℝ} (h0 : 0 < t) (h : t < 2⁻¹) : 0 < ell t := by
  unfold ell
  have := log_lt_log h0 (show t < 1 - t by linarith)
  linarith

private lemma ell_antitoneOn : AntitoneOn ell (Ioo 0 1) := by
  intro s hs t ht hst
  unfold ell
  have := log_le_log (by linarith [ht.2]) (show 1 - t ≤ 1 - s by linarith)
  have := log_le_log hs.1 hst
  linarith

variable {p : ℝ}

/-- The ratio `F'(a)/H'(a) = (1 - 2p) ℓ(a ∗ p)/ℓ(a)`. -/
private def ratio (p a : ℝ) : ℝ := (1 - 2 * p) * ell (binConv a p) / ell a

/-- `(1 - 2p) a(1 - a)/((a ∗ p)(1 - a ∗ p))`, the ratio of the derivatives of `ℓ(a ∗ p)` and
`ℓ(a)`. -/
private def derivRatio (p a : ℝ) : ℝ :=
  (1 - 2 * p) * (a * (1 - a)) / (binConv a p * (1 - binConv a p))

private lemma binConv_pos_of_mem {a : ℝ} (hp : p ∈ Icc 0 2⁻¹) (ha : 0 < a) : 0 < binConv a p := by
  rw [binConv_eq]
  rcases hp.1.lt_or_eq with h | h
  · nlinarith [hp.2]
  · subst h; simpa using ha

private lemma binConv_mem_Ioo {a : ℝ} (hp : p ∈ Icc 0 2⁻¹) (ha : a ∈ Ioc 0 2⁻¹) :
    binConv a p ∈ Ioo 0 1 :=
  ⟨binConv_pos_of_mem hp ha.1,
    lt_of_le_of_lt (binConv_mem_Icc_half ⟨ha.1.le, ha.2⟩ hp).2 (by norm_num)⟩

private lemma continuous_binConv_left (p : ℝ) : Continuous fun a => binConv a p := by
  unfold binConv; fun_prop

private lemma hasDerivAt_binConv (a p : ℝ) : HasDerivAt (fun a => binConv a p) (1 - 2 * p) a := by
  simp_rw [binConv_eq]
  simpa using ((hasDerivAt_id a).const_mul (1 - 2 * p)).const_add p

/-- `derivRatio` is nondecreasing on `(0, 1/2]`. -/
private lemma derivRatio_le {s t : ℝ} (hp : p ∈ Icc 0 2⁻¹) (hs : 0 < s) (hst : s ≤ t)
    (ht : t ≤ 2⁻¹) : derivRatio p s ≤ derivRatio p t := by
  have hcs := binConv_mem_Ioo hp ⟨hs, hst.trans ht⟩
  have hct := binConv_mem_Ioo hp ⟨hs.trans_le hst, ht⟩
  have hρ : 0 ≤ 1 - 2 * p := by linarith [hp.2]
  have hρ1 : 1 - 2 * p ≤ 1 := by linarith [hp.1]
  have hcs1 : 0 < 1 - binConv s p := by linarith [hcs.2]
  have hct1 : 0 < 1 - binConv t p := by linarith [hct.2]
  unfold derivRatio
  rw [mul_div_assoc (1 - 2 * p) (s * (1 - s)), mul_div_assoc (1 - 2 * p) (t * (1 - t))]
  refine mul_le_mul_of_nonneg_left ?_ hρ
  rw [div_le_div_iff₀ (mul_pos hcs.1 hcs1) (mul_pos hct.1 hct1)]
  rw [binConv_eq, binConv_eq]
  -- In terms of `σ = 1 - 2s`, `τ = 1 - 2t` and `ρ = 1 - 2p`, this is
  -- `(1 - σ²)(1 - ρ²τ²) ≤ (1 - τ²)(1 - ρ²σ²)`, i.e. `(σ² - τ²)(1 - ρ²) ≥ 0`.
  nlinarith [mul_nonneg (mul_nonneg hρ (by linarith : (0 : ℝ) ≤ 1 - (1 - 2 * p)))
    (mul_nonneg (by linarith : (0 : ℝ) ≤ t - s) (by linarith : (0 : ℝ) ≤ 1 - s - t)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (1 - 2 * p))
    (mul_nonneg (by linarith : (0 : ℝ) ≤ t - s) (by linarith : (0 : ℝ) ≤ 1 - s - t))]

/-- `ℓ(a ∗ p) = derivRatio · ℓ(a)` at the level of derivatives. -/
private lemma hasDerivAt_ell_binConv {a : ℝ} (hp : p ∈ Icc 0 2⁻¹) (ha : a ∈ Ioo 0 2⁻¹) :
    HasDerivAt (fun a => ell (binConv a p)) (derivRatio p a * -((1 - a)⁻¹ + a⁻¹)) a := by
  have hc := binConv_mem_Ioo hp ⟨ha.1, ha.2.le⟩
  have h := (hasDerivAt_ell hc.1 hc.2).comp a (hasDerivAt_binConv a p)
  refine h.congr_deriv ?_
  have h1 : (1 - a) ≠ 0 := by linarith [ha.2]
  have h2 : (1 - binConv a p) ≠ 0 := by linarith [hc.2]
  have h3 : a ≠ 0 := ha.1.ne'
  have h4 : binConv a p ≠ 0 := hc.1.ne'
  unfold derivRatio
  field_simp
  ring

/-- The ratio `F'(a)/H'(a)` is nondecreasing on `(0, 1/2)`. -/
private lemma ratio_le {s t : ℝ} (hp : p ∈ Icc 0 2⁻¹) (hs : s ∈ Ioo 0 2⁻¹) (ht : t ∈ Ioo 0 2⁻¹)
    (hst : s < t) : ratio p s ≤ ratio p t := by
  set u : ℝ → ℝ := fun a => ell (binConv a p)
  have hcont : ∀ {a b : ℝ}, 0 < a → b ≤ 2⁻¹ → ContinuousOn u (Icc a b) ∧
      ContinuousOn ell (Icc a b) := fun ha hb => by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hc := binConv_mem_Ioo hp ⟨ha.trans_le hx.1, hx.2.trans hb⟩
      exact (ContinuousAt.comp (g := ell) (f := fun a => binConv a p)
        (continuousOn_ell.continuousAt (isOpen_Ioo.mem_nhds hc))
        (hasDerivAt_binConv x p).continuousAt).continuousWithinAt
    · exact (continuousOn_ell.continuousAt (isOpen_Ioo.mem_nhds
        ⟨ha.trans_le hx.1, by linarith [hx.2]⟩)).continuousWithinAt
  have hderiv : ∀ x ∈ Ioo s 2⁻¹, HasDerivAt u (derivRatio p x * -((1 - x)⁻¹ + x⁻¹)) x ∧
      HasDerivAt ell (-((1 - x)⁻¹ + x⁻¹)) x := fun x hx =>
    ⟨hasDerivAt_ell_binConv hp ⟨hs.1.trans hx.1, hx.2⟩,
      hasDerivAt_ell (hs.1.trans hx.1) (by linarith [hx.2])⟩
  have hne : ∀ x ∈ Ioo s 2⁻¹, -((1 - x)⁻¹ + x⁻¹) ≠ 0 := fun x hx => by
    have : 0 < (1 - x)⁻¹ := inv_pos.2 (by linarith [hx.2])
    have : 0 < x⁻¹ := inv_pos.2 (hs.1.trans hx.1)
    linarith
  -- Mean value theorem on `[s, t]`: `u(t) - u(s) = (ℓ(t) - ℓ(s)) k(ξ)`.
  obtain ⟨ξ, hξ, hξeq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope u _ hst
    (hcont hs.1 ht.2.le).1 (fun x hx => (hderiv x ⟨hx.1, hx.2.trans ht.2⟩).1) ell _
    (hcont hs.1 ht.2.le).2 (fun x hx => (hderiv x ⟨hx.1, hx.2.trans ht.2⟩).2)
  -- Mean value theorem on `[t, 1/2]`: `u(t) = ℓ(t) k(η)`.
  obtain ⟨η, hη, hηeq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope u _ ht.2
    (hcont ht.1 le_rfl).1 (fun x hx => (hderiv x ⟨hst.trans hx.1, hx.2⟩).1) ell _
    (hcont ht.1 le_rfl).2 (fun x hx => (hderiv x ⟨hst.trans hx.1, hx.2⟩).2)
  have hξ' : ξ ∈ Ioo s 2⁻¹ := ⟨hξ.1, hξ.2.trans ht.2⟩
  have hη' : η ∈ Ioo s 2⁻¹ := ⟨hst.trans hη.1, hη.2⟩
  have e1 : u t - u s = (ell t - ell s) * derivRatio p ξ := by
    have := hne ξ hξ'
    apply mul_right_cancel₀ this
    linarith [hξeq]
  have hu2 : u 2⁻¹ = 0 := by simp only [u, binConv_half_left, ell_half]
  have e2 : u t = ell t * derivRatio p η := by
    have := hne η hη'
    apply mul_right_cancel₀ this
    rw [hu2, ell_half] at hηeq
    linarith [hηeq]
  have hk : derivRatio p ξ ≤ derivRatio p η :=
    derivRatio_le hp (hs.1.trans hξ.1) (hξ.2.trans hη.1).le hη.2.le
  have hls : 0 < ell s := ell_pos hs.1 hs.2
  have hlt : 0 < ell t := ell_pos ht.1 ht.2
  have hdec : ell t ≤ ell s := ell_antitoneOn ⟨hs.1, by linarith [hs.2]⟩
    ⟨ht.1, by linarith [ht.2]⟩ hst.le
  unfold ratio
  rw [mul_div_assoc (1 - 2 * p) (ell (binConv s p)), mul_div_assoc (1 - 2 * p) (ell (binConv t p))]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [hp.2] : (0 : ℝ) ≤ 1 - 2 * p)
  rw [div_le_div_iff₀ hls hlt]
  have : u s ≤ ell s * derivRatio p η := by nlinarith
  change u s * ell t ≤ u t * ell s
  rw [e2]
  nlinarith

private lemma hasDerivAt_binEntropy_binConv {a : ℝ} (hp : p ∈ Icc 0 2⁻¹) (ha : a ∈ Ioo 0 2⁻¹) :
    HasDerivAt (fun a => binEntropy (binConv a p)) ((1 - 2 * p) * ell (binConv a p)) a := by
  have hc := binConv_mem_Ioo hp ⟨ha.1, ha.2.le⟩
  refine ((hasDerivAt_binEntropy hc.1.ne' hc.2.ne).comp a (hasDerivAt_binConv a p)).congr_deriv ?_
  simp only [ell]
  ring

private lemma slope_eq_ratio {a b : ℝ} (hp : p ∈ Icc 0 2⁻¹) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 2⁻¹) : ∃ ξ ∈ Ioo a b,
      (binEntropy (binConv b p) - binEntropy (binConv a p)) / (binEntropy b - binEntropy a) =
        ratio p ξ := by
  have hmem : ∀ x ∈ Ioo a b, x ∈ Ioo 0 2⁻¹ := fun x hx => ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
  obtain ⟨ξ, hξ, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    (fun a => binEntropy (binConv a p)) (fun x => (1 - 2 * p) * ell (binConv x p)) hab
    (binEntropy_continuous.comp (continuous_binConv_left p)).continuousOn
    (fun x hx => hasDerivAt_binEntropy_binConv hp (hmem x hx))
    binEntropy (fun x => log (1 - x) - log x) binEntropy_continuous.continuousOn
    (fun x hx => hasDerivAt_binEntropy (hmem x hx).1.ne' (by linarith [(hmem x hx).2]))
  refine ⟨ξ, hξ, ?_⟩
  have hpos := ell_pos (hmem ξ hξ).1 (hmem ξ hξ).2
  have hne : binEntropy b - binEntropy a ≠ 0 := by
    have := binEntropy_strictMonoOn ⟨ha, (hab.trans_le hb).le⟩ ⟨ha.trans hab.le, hb⟩ hab
    linarith
  unfold ratio
  rw [div_eq_div_iff hne hpos.ne']
  simp only [ell] at heq ⊢
  linear_combination -heq

lemma mrsGerber_convexOn_of_le_half {p : ℝ} (hp : p ∈ Icc 0 2⁻¹) :
    ConvexOn ℝ (Icc 0 (log 2)) (mrsGerber p) := by
  refine convexOn_of_slope_mono_adjacent (convex_Icc _ _) fun {x y z} hx hz hxy hyz => ?_
  have hy : y ∈ Icc 0 (log 2) := ⟨hx.1.trans hxy.le, hyz.le.trans hz.2⟩
  set a := binEntropyInv x
  set b := binEntropyInv y
  set c := binEntropyInv z
  have hab : a < b := binEntropyInv_strictMonoOn hx hy hxy
  have hbc : b < c := binEntropyInv_strictMonoOn hy hz hyz
  have ha := binEntropyInv_mem hx
  have hc := binEntropyInv_mem hz
  obtain ⟨ξ, hξ, e1⟩ := slope_eq_ratio hp ha.1 hab (hbc.le.trans hc.2)
  obtain ⟨η, hη, e2⟩ := slope_eq_ratio hp (ha.1.trans hab.le) hbc hc.2
  rw [binEntropy_binEntropyInv hx, binEntropy_binEntropyInv hy] at e1
  rw [binEntropy_binEntropyInv hy, binEntropy_binEntropyInv hz] at e2
  simp only [mrsGerber]
  rw [e1, e2]
  exact (ratio_le hp ⟨ha.1.trans_lt hξ.1, hξ.2.trans_le (hbc.le.trans hc.2)⟩
    ⟨(ha.1.trans hab.le).trans_lt hη.1, hη.2.trans_le hc.2⟩ (hξ.2.trans hη.1)).trans le_rfl

end Convexity

/-- **Lecture 2.** `v ↦ H(H⁻¹(v) ∗ p)` is convex on `[0, log 2]` for every `p ∈ [0, 1]`. -/
theorem mrsGerber_convexOn {p : ℝ} (hp : p ∈ Icc 0 1) :
    ConvexOn ℝ (Icc 0 (log 2)) (mrsGerber p) := by
  rcases le_total p 2⁻¹ with h | h
  · exact mrsGerber_convexOn_of_le_half ⟨hp.1, h⟩
  · have := mrsGerber_convexOn_of_le_half (p := 1 - p) ⟨by linarith [hp.2], by linarith⟩
    rwa [mrsGerber_one_sub] at this

/-! ### Mrs. Gerber's lemma -/

section Lemma

variable {Ω γ : Type*} [Fintype Ω] [Fintype γ]

/-- The entropy of a pmf on `Bool` is the binary entropy of the probability of `true`. -/
lemma entropy_bool {q : Bool → ℝ} (hq : IsPMF q) : entropy q = binEntropy (q true) := by
  have h1 : q false = 1 - q true := by
    have := hq.sum_eq_one
    rw [Fintype.sum_bool] at this
    linarith
  have : q = fun b => if b then q true else 1 - q true := by
    funext b
    cases b <;> simp [h1]
  rw [this, entropy_bernoulli]
  simp

omit [Fintype γ] in
/-- The law of `X ⊕ Z` given `U = u`, for `Z` independent of `(X, U)`:
`p(x ⊕ z = 1, u) = p · p(X = 0, u) + (1 - p) · p(X = 1, u)` with `p = P{Z = 1}`. -/
lemma dist_pair_xor {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → Bool) (U : Ω → γ) (Z : Ω → Bool)
    (hind : IndepRV μ Z (pair X U)) (u : γ) :
    dist μ (pair U fun ω => xor (X ω) (Z ω)) (u, true) =
      dist μ Z true * dist μ (pair U X) (u, false) +
        (1 - dist μ Z true) * dist μ (pair U X) (u, true) := by
  have hZf : dist μ Z false = 1 - dist μ Z true := by
    have := (hμ.dist Z).sum_eq_one
    rw [Fintype.sum_bool] at this
    linarith
  have h : dist μ (pair U fun ω => xor (X ω) (Z ω)) (u, true) =
      dist μ (pair Z (pair X U)) (true, (false, u)) +
        dist μ (pair Z (pair X U)) (false, (true, u)) := by
    simp only [dist, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hU : U ω = u <;> cases hX : X ω <;> cases hZ : Z ω <;> simp [pair, hU, hX, hZ]
  rw [h, hind, hind, hZf, dist_pair_swap μ X U, dist_pair_swap μ X U]

/-- **Mrs. Gerber's lemma (Lecture 2)**, scalar form. Let `X` be a binary random variable, `U` an
arbitrary random variable, and `Z ∼ Bern(p)` independent of `(X, U)`. Then
`H(X ⊕ Z|U) ≥ H(H⁻¹(H(X|U)) ∗ p)`. -/
theorem mrsGerber_le_condEntropy_xor {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → Bool) (U : Ω → γ)
    (Z : Ω → Bool) {p : ℝ} (hZ : dist μ Z true = p) (hind : IndepRV μ Z (pair X U)) :
    mrsGerber p H[X | U ; μ] ≤ H[fun ω => xor (X ω) (Z ω) | U ; μ] := by
  have hp : p ∈ Icc 0 1 := hZ ▸ ⟨dist_nonneg hμ Z true, (hμ.dist Z).le_one true⟩
  set Y : Ω → Bool := fun ω => xor (X ω) (Z ω)
  -- `H(X | U = u) ∈ [0, log 2]`.
  have hmem : ∀ u, condEntropyAt μ X U u ∈ Icc 0 (log 2) := fun u => by
    by_cases hu : dist μ U u = 0
    · have : condDist μ X U u = fun _ => 0 := funext fun x => by simp [condDist, hu]
      simp [condEntropyAt, this, entropy, log_nonneg one_le_two]
    · rw [condEntropyAt, entropy_bool (condDist_isPMF hμ X U hu)]
      exact binEntropy_mem_Icc ⟨condDist_nonneg hμ X U u true,
        (condDist_isPMF hμ X U hu).le_one true⟩
  -- `H(Y | U = u) = H(H⁻¹(H(X | U = u)) ∗ p)`.
  have hterm : ∀ u, dist μ U u * condEntropyAt μ Y U u =
      dist μ U u * mrsGerber p (condEntropyAt μ X U u) := fun u => by
    by_cases hu : dist μ U u = 0
    · rw [hu, zero_mul, zero_mul]
    · congr 1
      have ha : condDist μ X U u true ∈ Icc 0 1 :=
        ⟨condDist_nonneg hμ X U u true, (condDist_isPMF hμ X U hu).le_one true⟩
      rw [condEntropyAt, entropy_bool (condDist_isPMF hμ Y U hu), condEntropyAt,
        entropy_bool (condDist_isPMF hμ X U hu), mrsGerber, binEntropy_binConv_binEntropyInv ha]
      congr 1
      have hsum := sum_dist_pair_right μ U X u
      rw [Fintype.sum_bool] at hsum
      simp only [condDist]
      rw [dist_pair_xor hμ X U Z hind, hZ, binConv]
      field_simp
      rw [← hsum]
      ring
  have hY : H[Y | U ; μ] = ∑ u, dist μ U u * mrsGerber p (condEntropyAt μ X U u) := by
    rw [condEntropy]
    exact Finset.sum_congr rfl fun u _ => hterm u
  rw [hY, condEntropy]
  have := (mrsGerber_convexOn hp).map_sum_le (t := Finset.univ) (w := fun u => dist μ U u)
    (p := fun u => condEntropyAt μ X U u) (fun u _ => dist_nonneg hμ U u)
    (hμ.dist U).sum_eq_one (fun u _ => hmem u)
  simpa only [smul_eq_mul] using this

/-- A binary random variable has conditional entropy in `[0, log 2]`. -/
lemma condEntropy_bool_mem_Icc {β : Type*} [Fintype β] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → Bool)
    (W : Ω → β) : H[X | W ; μ] ∈ Icc 0 (log 2) :=
  ⟨condEntropy_nonneg hμ X W, (condEntropy_le_entropy hμ X W).trans
    ((entropyRV_le_log_card hμ X).trans (by simp))⟩

/-- **Mrs. Gerber's lemma (Lecture 2)**, vector form. Let `Xⁿ` be a binary random vector, `U`
an arbitrary random variable, and `Zⁿ` a vector of i.i.d. `Bern(p)` random variables independent
of `(Xⁿ, U)`. Then `H(Xⁿ ⊕ Zⁿ|U)/n ≥ H(H⁻¹(H(Xⁿ|U)/n) ∗ p)`. The hypotheses say that
`Z₀, …, Z_{n-1}` are mutually independent with `P{Zᵢ = 1} = p`, and that `Zⁿ` is independent of
`(Xⁿ, U)`. -/
theorem mrsGerber_le_condEntropy_xor_prefixRV {μ : Ω → ℝ} (hμ : IsPMF μ) (X Z : ℕ → Ω → Bool)
    (U : Ω → γ) {n : ℕ} (hn : 0 < n) {p : ℝ} (hZ : ∀ i < n, dist μ (Z i) true = p)
    (hfam : IndepFamily μ Z n) (hind : IndepRV μ (prefixRV Z n) (pair (prefixRV X n) U)) :
    mrsGerber p (H[prefixRV X n | U ; μ] / n) ≤
      H[prefixRV (fun i ω => xor (X i ω) (Z i ω)) n | U ; μ] / n := by
  set Y : ℕ → Ω → Bool := fun i ω => xor (X i ω) (Z i ω)
  set V := pair (prefixRV X n) U
  have hp : p ∈ Icc 0 1 := hZ 0 hn ▸ ⟨dist_nonneg hμ _ true, (hμ.dist _).le_one true⟩
  have hterm : ∀ i ∈ Finset.range n,
      mrsGerber p H[X i | pair U (prefixRV X i) ; μ] ≤ H[Y i | pair U (prefixRV Y i) ; μ] := by
    intro i hi
    have hi : i < n := Finset.mem_range.1 hi
    -- Independence of `Zᵢ` from `(Xⁿ, U, Z^i)`, and of `Z^i` from `(Xⁿ, U)`.
    have hZiV : IndepRV μ (prefixRV Z i) V :=
      hind.comp (fun z : Fin n → Bool => fun j : Fin i => z (Fin.castLE hi.le j)) id
    have hZpairV : IndepRV μ (pair (Z i) (prefixRV Z i)) V :=
      hind.comp (fun z : Fin n → Bool => (z ⟨i, hi⟩, fun j : Fin i => z (Fin.castLE hi.le j))) id
    have hZZ : IndepRV μ (Z i) (prefixRV Z i) :=
      ((indepFamily_iff hμ Z n).1 hfam i (Finset.mem_range.2 hi)).symm
    have hZW : IndepRV μ (Z i) (pair V (prefixRV Z i)) := by
      rintro c ⟨v, z⟩
      have e1 : dist μ (pair (Z i) (pair V (prefixRV Z i))) (c, (v, z)) =
          dist μ (pair (pair (Z i) (prefixRV Z i)) V) ((c, z), v) :=
        dist_comp_of_injective μ (pair (pair (Z i) (prefixRV Z i)) V)
          (f := fun t => (t.1.1, (t.2, t.1.2)))
          (Function.LeftInverse.injective (g := fun s => ((s.1, s.2.2), s.2.1)) fun _ => rfl)
          ((c, z), v)
      rw [e1, hZpairV, hZZ, hZiV.symm]
      ring
    -- The scalar lemma, given `(U, Y^i)`.
    have hind1 : IndepRV μ (Z i) (pair (X i) (pair U (prefixRV Y i))) :=
      hZW.comp id fun w : ((Fin n → Bool) × γ) × (Fin i → Bool) =>
        (w.1.1 ⟨i, hi⟩, (w.1.2, fun j => xor (w.1.1 (Fin.castLE hi.le j)) (w.2 j)))
    have h1 := mrsGerber_le_condEntropy_xor hμ (X i) (pair U (prefixRV Y i)) (Z i) (hZ i hi) hind1
    -- `H(Xᵢ | U, Y^i) ≥ H(Xᵢ | U, X^i, Z^i) = H(Xᵢ | U, X^i)`.
    have hind2 : IndepRV μ (prefixRV Z i) (pair (X i) (pair U (prefixRV X i))) :=
      hZiV.comp id fun v : (Fin n → Bool) × γ =>
        (v.1 ⟨i, hi⟩, (v.2, fun j : Fin i => v.1 (Fin.castLE hi.le j)))
    have hI : I[X i : prefixRV Z i | pair U (prefixRV X i) ; μ] = 0 := by
      have hc := chain_rule_mutualInfo₂ hμ (prefixRV Z i) (X i) (pair U (prefixRV X i))
      rw [(mutualInfo_eq_zero_iff hμ _ _).2 hind2] at hc
      have h0 := mutualInfo_nonneg hμ (prefixRV Z i) (pair U (prefixRV X i))
      have h0' := condMutualInfo_nonneg hμ (prefixRV Z i) (X i) (pair U (prefixRV X i))
      rw [condMutualInfo_comm hμ]
      linarith
    have h3 : H[X i | pair (prefixRV Z i) (pair U (prefixRV X i)) ; μ] ≤
        H[X i | pair U (prefixRV Y i) ; μ] :=
      condEntropy_le_condEntropy_comp hμ (X i) (pair (prefixRV Z i) (pair U (prefixRV X i)))
        fun w => (w.2.1, fun j => xor (w.2.2 j) (w.1 j))
    have h2 : H[X i | pair U (prefixRV X i) ; μ] ≤ H[X i | pair U (prefixRV Y i) ; μ] := by
      rw [condMutualInfo] at hI
      linarith
    exact (mrsGerber_monotoneOn hp (condEntropy_bool_mem_Icc hμ _ _)
      (condEntropy_bool_mem_Icc hμ _ _) h2).trans h1
  -- Jensen's inequality over `i`.
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ := (mrsGerber_convexOn hp).map_sum_le (t := Finset.range n) (w := fun _ => (1 / n : ℝ))
    (p := fun i => H[X i | pair U (prefixRV X i) ; μ]) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp)
    (fun i _ => condEntropy_bool_mem_Icc hμ _ _)
  simp only [smul_eq_mul] at hJ
  rw [chain_rule_entropy_cond hμ X U n, chain_rule_entropy_cond hμ Y U n, Finset.sum_div,
    Finset.sum_div]
  calc mrsGerber p (∑ i ∈ Finset.range n, H[X i | pair U (prefixRV X i) ; μ] / n)
      = mrsGerber p (∑ i ∈ Finset.range n, 1 / n * H[X i | pair U (prefixRV X i) ; μ]) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range n, 1 / n * mrsGerber p H[X i | pair U (prefixRV X i) ; μ] := hJ
    _ ≤ ∑ i ∈ Finset.range n, H[Y i | pair U (prefixRV Y i) ; μ] / n :=
        Finset.sum_le_sum fun i hi =>
          (mul_le_mul_of_nonneg_left (hterm i hi) (by positivity : (0 : ℝ) ≤ 1 / n)).trans_eq
            (by ring)

/-- `H⁻¹(H(Xⁿ|U)/n)` is defined: a binary random vector has `H(Xⁿ|U)/n ∈ [0, log 2]`. -/
lemma condEntropy_prefixRV_div_mem_Icc {β : Type*} [Fintype β] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (X : ℕ → Ω → Bool) (W : Ω → β) {n : ℕ} (hn : 0 < n) :
    H[prefixRV X n | W ; μ] / n ∈ Icc 0 (log 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨div_nonneg (condEntropy_nonneg hμ _ _) hn'.le, (div_le_iff₀ hn').2 ?_⟩
  have h := (condEntropy_le_entropy hμ (prefixRV X n) W).trans (entropyRV_le_log_card hμ _)
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, mul_comm] using h

/-- **Mrs. Gerber's lemma (Lecture 2)**, scalar form as stated in the lecture notes:
`H⁻¹(H(X ⊕ Z|U)) ≥ H⁻¹(H(X|U)) ∗ p` for `Z ∼ Bern(p)` independent of `(X, U)`. This form needs
`p ≤ 1/2`: for `p = 1` and a constant `X`, the left side is `0` and the right side is `1`. -/
theorem binConv_binEntropyInv_le {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → Bool) (U : Ω → γ)
    (Z : Ω → Bool) {p : ℝ} (hZ : dist μ Z true = p) (hp : p ≤ 2⁻¹)
    (hind : IndepRV μ Z (pair X U)) :
    binConv (binEntropyInv H[X | U ; μ]) p ≤ binEntropyInv H[fun ω => xor (X ω) (Z ω) | U ; μ] := by
  have hp0 : 0 ≤ p := hZ ▸ dist_nonneg hμ Z true
  have hc := binConv_mem_Icc_half (binEntropyInv_mem (condEntropy_bool_mem_Icc hμ X U)) ⟨hp0, hp⟩
  have h := mrsGerber_le_condEntropy_xor hμ X U Z hZ hind
  rw [← binEntropyInv_binEntropy hc]
  exact binEntropyInv_strictMonoOn.monotoneOn
    (binEntropy_mem_Icc ⟨hc.1, hc.2.trans (by norm_num)⟩) (condEntropy_bool_mem_Icc hμ _ U) h

/-- **Mrs. Gerber's lemma (Lecture 2)**, vector form as stated in the lecture notes:
`H⁻¹(H(Xⁿ ⊕ Zⁿ|U)/n) ≥ H⁻¹(H(Xⁿ|U)/n) ∗ p` for `Zⁿ` i.i.d. `Bern(p)` independent of `(Xⁿ, U)`,
with `p ≤ 1/2`. -/
theorem binConv_binEntropyInv_le_prefixRV {μ : Ω → ℝ} (hμ : IsPMF μ) (X Z : ℕ → Ω → Bool)
    (U : Ω → γ) {n : ℕ} (hn : 0 < n) {p : ℝ} (hZ : ∀ i < n, dist μ (Z i) true = p)
    (hp : p ≤ 2⁻¹) (hfam : IndepFamily μ Z n)
    (hind : IndepRV μ (prefixRV Z n) (pair (prefixRV X n) U)) :
    binConv (binEntropyInv (H[prefixRV X n | U ; μ] / n)) p ≤
      binEntropyInv (H[prefixRV (fun i ω => xor (X i ω) (Z i ω)) n | U ; μ] / n) := by
  have hp0 : 0 ≤ p := hZ 0 hn ▸ dist_nonneg hμ _ true
  have hc := binConv_mem_Icc_half (binEntropyInv_mem (condEntropy_prefixRV_div_mem_Icc hμ X U hn))
    ⟨hp0, hp⟩
  have h := mrsGerber_le_condEntropy_xor_prefixRV hμ X Z U hn hZ hfam hind
  rw [← binEntropyInv_binEntropy hc]
  exact binEntropyInv_strictMonoOn.monotoneOn
    (binEntropy_mem_Icc ⟨hc.1, hc.2.trans (by norm_num)⟩)
    (condEntropy_prefixRV_div_mem_Icc hμ _ U hn) h

end Lemma

end InfoTheory
