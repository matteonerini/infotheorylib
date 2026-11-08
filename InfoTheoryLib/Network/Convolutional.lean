/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.RatPowerSeries
public import InfoTheoryLib.Network.MaxFlowBound

/-!
# Linear network codes on cyclic networks

On a network `G` that may have directed cycles, an `ω`-dimensional linear network code with source
`s` is given by local encoding kernels: `ks i e` for the `i`-th imaginary channel into `s` and a
channel `e` out of `s`, and `k d e` for adjacent channels, `d` into the node that `e` leaves. The
global encoding kernels `fₑ` satisfy `fₑ = g (∑ᵢ ks i e uᵢ + ∑_{d → e} k d e f_d)`, where the
`uᵢ` are the standard basis vectors and `g` is the gain of a channel.

* With `g = 1`, this is (19.17) of Yeung for delay-free networks. On a cyclic network it can have
  one, none or many solutions (Examples 20.1–20.3).
* With power series coefficients and `g = X`, this is (20.39) of a convolutional network code on a
  unit-delay network (Definition 20.6), and it always has exactly one solution, which is rational
  when the local encoding kernels are (Theorem 20.9).

In matrix form the equations read `F (1 - g K) = g Hₛ` (20.80), where `F` has the global encoding
kernels as its columns, `K` is the `E × E` matrix of the local encoding kernels and `Hₛ` the
`ω × E` matrix of those at the source.

## Main definitions

* `PtpNetwork.IsGlobalKernel`: the equations (19.17) and (20.39) with gain `g`.
* `PtpNetwork.IsConvCode`: a convolutional network code (Definition 20.6).
* `PtpNetwork.unitMaxflow`: the max-flow when every channel has capacity `1`.
* `PtpNetwork.IsConvMulticast`: a convolutional multicast (Definition 20.10).

## Main statements

* `PtpNetwork.isGlobalKernel_iff`: the matrix form (20.80).
* `PtpNetwork.existsUnique_isGlobalKernel`: a unique solution when `det (1 - g K)` is a unit.
* `PtpNetwork.existsUnique_isConvCode`: Theorem 20.9.
* `PtpNetwork.vecMul_decode`: decoding the message pipeline, (20.88)–(20.90).
* `PtpNetwork.exists_decoder_of_det_ne_zero`: a node has a decoding kernel if the global encoding
  kernels of `ω` of its input channels have a nonzero determinant, the second half of the proof of
  Theorem 20.13.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 20
-/

open Finset PowerSeries
open scoped Matrix

@[expose] public noncomputable section

namespace InfoTheory

namespace PtpNetwork

variable {V E A : Type*} [DecidableEq V] [Fintype E] (G : PtpNetwork V E) (s : V) {ω : ℕ}

section Kernels

variable [CommRing A]

/-- The global encoding kernels `f` satisfy the local encoding kernels `ks` at the source `s` and
`k` at the other nodes, with gain `g` on every channel:
`fₑ = g (∑ᵢ ks i e uᵢ + ∑_{d ∈ In(tail e)} k d e f_d)`, where the first sum is only present when
`e` leaves `s`. With `g = 1` this is (19.17), and with `g = X` it is (20.39). -/
def IsGlobalKernel (g : A) (ks : Fin ω → E → A) (k : E → E → A) (f : E → Fin ω → A) : Prop :=
  ∀ e, f e = g • ((if G.tail e = s then fun i => ks i e else 0) +
    ∑ d with G.head d = G.tail e, k d e • f d)

/-- The `E × E` matrix of the local encoding kernels, zero off the adjacent pairs of channels. -/
def kernelMatrix (k : E → E → A) : Matrix E E A :=
  Matrix.of fun d e => if G.head d = G.tail e then k d e else 0

/-- The `ω × E` matrix `Hₛ` of the local encoding kernels at the source, zero off the channels
out of `s`. -/
def srcMatrix (ks : Fin ω → E → A) : Matrix (Fin ω) E A :=
  Matrix.of fun i e => if G.tail e = s then ks i e else 0

variable {G s}

/-- **(20.80).** The equations of the global encoding kernels in matrix form,
`F (1 - g K) = g Hₛ`, where `F` has columns `fₑ`. -/
theorem isGlobalKernel_iff [DecidableEq E] {g : A} {ks : Fin ω → E → A} {k : E → E → A}
    {f : E → Fin ω → A} :
    G.IsGlobalKernel s g ks k f ↔
      (Matrix.of f)ᵀ * (1 - g • G.kernelMatrix k) = g • G.srcMatrix s ks := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, sub_eq_iff_eq_add, ← smul_add,
    ← Matrix.ext_iff, IsGlobalKernel, forall_comm]
  refine forall_congr' fun e => ?_
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.add_apply, Matrix.add_apply, Finset.sum_apply, Matrix.mul_apply, srcMatrix,
    kernelMatrix, sum_filter, mul_ite, mul_zero, ite_apply, Pi.zero_apply]
  split_ifs <;> simp [mul_comm]

/-- The equations only involve the local encoding kernels at the source on the channels out of
`s`, and the other ones on adjacent pairs of channels. -/
theorem isGlobalKernel_congr {g : A} {ks ks' : Fin ω → E → A} {k k' : E → E → A}
    {f : E → Fin ω → A} (hks : ∀ i e, G.tail e = s → ks i e = ks' i e)
    (hk : ∀ d e, G.head d = G.tail e → k d e = k' d e) :
    G.IsGlobalKernel s g ks k f ↔ G.IsGlobalKernel s g ks' k' f := by
  refine forall_congr' fun e => ?_
  rw [sum_congr rfl fun d hd => by rw [hk d e (mem_filter.1 hd).2]]
  split_ifs with h
  · simp only [funext fun i => hks i e h]
  · rfl

/-- Solutions of the equations are preserved by ring homomorphisms. -/
theorem IsGlobalKernel.map {B : Type*} [CommRing B] (φ : A →+* B) {g : A}
    {ks : Fin ω → E → A} {k : E → E → A} {f : E → Fin ω → A} (h : G.IsGlobalKernel s g ks k f) :
    G.IsGlobalKernel s (φ g) (fun i e => φ (ks i e)) (fun d e => φ (k d e))
      (fun e i => φ (f e i)) := by
  intro e
  funext i
  have := congrFun (h e) i
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul] at this ⊢
  rw [this]
  split_ifs <;> simp [map_sum]

/-- The equations have a unique solution when `det (1 - g K)` is a unit, `F = g Hₛ (1 - g K)⁻¹`. -/
theorem existsUnique_isGlobalKernel [DecidableEq E] {g : A} (ks : Fin ω → E → A) (k : E → E → A)
    (h : IsUnit (1 - g • G.kernelMatrix k).det) : ∃! f, G.IsGlobalKernel s g ks k f := by
  set M := 1 - g • G.kernelMatrix k
  refine ⟨fun e i => (g • G.srcMatrix s ks * M⁻¹)ᵀ e i, ?_, fun f hf => ?_⟩
  · beta_reduce
    rw [isGlobalKernel_iff]
    exact Matrix.nonsing_inv_mul_cancel_right _ _ h
  · beta_reduce at hf
    rw [isGlobalKernel_iff] at hf
    have : (Matrix.of f)ᵀ = g • G.srcMatrix s ks * M⁻¹ := by
      rw [← hf, Matrix.mul_nonsing_inv_cancel_right _ _ h]
    rw [← this]
    rfl

end Kernels

/-! ### Convolutional network codes -/

section Convolutional

variable {F : Type*} [Field F]

/-- **Definition 20.6 (Convolutional Network Code).** An `ω`-dimensional convolutional network code
on the unit-delay network `G` with source `s`: the local encoding kernels at the source `ks i e`,
for the channels `e` out of `s`, and `k d e`, for the adjacent pairs of channels, and the global
encoding kernels `fₑ` are rational power series, and they satisfy (20.39) and (20.40),
`fₑ = X (∑ᵢ ks i e uᵢ + ∑_{d ∈ In(tail e)} k d e f_d)`. -/
def IsConvCode (ks : Fin ω → E → F⟦X⟧) (k : E → E → F⟦X⟧) (f : E → Fin ω → F⟦X⟧) : Prop :=
  (∀ i e, G.tail e = s → ks i e ∈ ratPowerSeries F) ∧
    (∀ d e, G.head d = G.tail e → k d e ∈ ratPowerSeries F) ∧
    (∀ e i, f e i ∈ ratPowerSeries F) ∧ G.IsGlobalKernel s (X : F⟦X⟧) ks k f

variable {G s}

/-- On a unit-delay network, the global encoding kernels are unique, for any power series local
encoding kernels: `det (1 - X K)` has constant coefficient `1`. -/
theorem existsUnique_isGlobalKernel_X {R : Type*} [CommRing R]
    (ks : Fin ω → E → R⟦X⟧) (k : E → E → R⟦X⟧) : ∃! f, G.IsGlobalKernel s (X : R⟦X⟧) ks k f := by
  classical
  exact existsUnique_isGlobalKernel ks k (isUnit_det_one_sub_X_smul _)

/-- **Theorem 20.9.** Rational power series local encoding kernels on a unit-delay network define a
unique convolutional network code: the global encoding kernels `F = X Hₛ (1 - X K)⁻¹` of (20.84)
are rational. -/
theorem existsUnique_isConvCode {ks : Fin ω → E → F⟦X⟧} {k : E → E → F⟦X⟧}
    (hks : ∀ i e, G.tail e = s → ks i e ∈ ratPowerSeries F)
    (hk : ∀ d e, G.head d = G.tail e → k d e ∈ ratPowerSeries F) :
    ∃! f, G.IsConvCode s ks k f := by
  classical
  obtain ⟨f₀, hf₀, huniq⟩ := existsUnique_isGlobalKernel_X (G := G) (s := s) ks k
  refine ⟨f₀, ⟨hks, hk, ?_, hf₀⟩, fun f hf => huniq f hf.2.2.2⟩
  -- solve the equations in the ring of rational power series
  let S := ratPowerSeries F
  let ks' : Fin ω → E → S := fun i e => if h : G.tail e = s then ⟨ks i e, hks i e h⟩ else 0
  let k' : E → E → S := fun d e => if h : G.head d = G.tail e then ⟨k d e, hk d e h⟩ else 0
  let X' : S := ⟨X, X_mem_ratPowerSeries⟩
  have hdet : IsUnit (1 - X' • G.kernelMatrix k').det := by
    refine isUnit_ratPowerSeries ?_
    have hmap : (S.subtype.mapMatrix (1 - X' • G.kernelMatrix k')) =
        1 - (X : F⟦X⟧) • G.kernelMatrix (fun d e => (k' d e : F⟦X⟧)) := by
      ext d e
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, kernelMatrix, Matrix.of_apply, map_sub, smul_eq_mul, map_mul]
      split_ifs <;> simp [X']
    rw [← Subring.coe_subtype, RingHom.map_det, hmap]
    exact (PowerSeries.isUnit_iff_constantCoeff.mp (isUnit_det_one_sub_X_smul _)).ne_zero
  obtain ⟨f', hf', -⟩ := existsUnique_isGlobalKernel (s := s) ks' k' hdet
  have hf'' := hf'.map S.subtype
  rw [isGlobalKernel_congr (ks' := ks) (k' := k) (fun i e h => by simp [ks', h])
    (fun d e h => by simp [k', h])] at hf''
  have : f₀ = fun e i => (f' e i : F⟦X⟧) := (huniq _ hf'').symm
  intro e i
  rw [this]
  exact (f' e i).2

/-! ### Decoding -/

/-- The `ω × E` matrix `F_t` of (20.85), whose columns are the global encoding kernels of the
channels into `t`, and zero for the other channels. -/
def inKernelMatrix (f : E → Fin ω → F⟦X⟧) (t : V) : Matrix (Fin ω) E F⟦X⟧ :=
  Matrix.of fun i e => if G.head e = t then f e i else 0

variable (G s)

/-- The max-flow from `s` to `t` in `G` when every channel has capacity `1`. -/
def unitMaxflow [Fintype V] (t : V) : ℝ :=
  (⟨G.tail, G.head, fun _ => 1⟩ : PtpNetwork V E).maxflow s t

/-- **Definition 20.10 (Convolutional Multicast).** A convolutional network code is an
`ω`-dimensional convolutional multicast if every node `t ≠ s` with `maxflow(t) ≥ ω` has a decoding
kernel `D_t`, an `E × ω` matrix of rational power series, and a decoding delay `τ > 0` with
`F_t D_t = X^τ I` (20.86). The rows of `D_t` off the channels into `t` play no role. -/
def IsConvMulticast [Fintype V] (ks : Fin ω → E → F⟦X⟧) (k : E → E → F⟦X⟧)
    (f : E → Fin ω → F⟦X⟧) : Prop :=
  G.IsConvCode s ks k f ∧ ∀ t ≠ s, (ω : ℝ) ≤ G.unitMaxflow s t →
    ∃ D : Matrix E (Fin ω) F⟦X⟧, (∀ e i, D e i ∈ ratPowerSeries F) ∧
      ∃ τ, 0 < τ ∧ G.inKernelMatrix f t * D = (X : F⟦X⟧) ^ τ • (1 : Matrix (Fin ω) (Fin ω) F⟦X⟧)

variable {G s}

/-- **(20.88)–(20.90).** A node with a decoding kernel recovers the message pipeline `x` with delay
`τ` from what it receives, `x F_t`. -/
theorem vecMul_decode {f : E → Fin ω → F⟦X⟧} {t : V} {D : Matrix E (Fin ω) F⟦X⟧} {τ : ℕ}
    (hD : G.inKernelMatrix f t * D = (X : F⟦X⟧) ^ τ • (1 : Matrix (Fin ω) (Fin ω) F⟦X⟧))
    (x : Fin ω → F⟦X⟧) :
    Matrix.vecMul (Matrix.vecMul x (G.inKernelMatrix f t)) D = (X : F⟦X⟧) ^ τ • x := by
  rw [Matrix.vecMul_vecMul, hD, Matrix.vecMul_smul, Matrix.vecMul_one]

/-- **Second half of the proof of Theorem 20.13.** If the global encoding kernels of channels
`ι 0, …, ι (ω - 1)` into `t` are rational and have a nonzero determinant, then `t` has a decoding
kernel: with `det L = X^n w`, take `X w⁻¹ adj L` on the rows `ι j`. -/
theorem exists_decoder_of_det_ne_zero {f : E → Fin ω → F⟦X⟧}
    (hf : ∀ e i, f e i ∈ ratPowerSeries F) {t : V} (ι : Fin ω → E) (hι : ∀ j, G.head (ι j) = t)
    (hdet : (Matrix.of fun i j => f (ι j) i).det ≠ 0) :
    ∃ D : Matrix E (Fin ω) F⟦X⟧, (∀ e i, D e i ∈ ratPowerSeries F) ∧
      ∃ τ, 0 < τ ∧
        G.inKernelMatrix f t * D = (X : F⟦X⟧) ^ τ • (1 : Matrix (Fin ω) (Fin ω) F⟦X⟧) := by
  classical
  set L : Matrix (Fin ω) (Fin ω) F⟦X⟧ := Matrix.of fun i j => f (ι j) i
  set n := L.det.order.toNat
  set w := divXPowOrder L.det
  have hLw : X ^ n * w = L.det := X_pow_order_mul_divXPowOrder
  have hw : constantCoeff w ≠ 0 := by
    rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]
    exact hdet
  -- `L` and its adjugate are rational
  let S := ratPowerSeries F
  let L' : Matrix (Fin ω) (Fin ω) S := Matrix.of fun i j => ⟨f (ι j) i, hf _ _⟩
  have hL : S.subtype.mapMatrix L' = L := rfl
  have hdetS : L.det ∈ S := by
    rw [← hL, ← RingHom.map_det]
    exact (L'.det).2
  have hadj : ∀ i j, L.adjugate i j ∈ S := by
    intro i j
    rw [← hL, ← RingHom.map_adjugate]
    exact (L'.adjugate i j).2
  have hwS : w ∈ S := mem_ratPowerSeries_of_X_pow_mul n (hLw ▸ hdetS)
  let D : Matrix E (Fin ω) F⟦X⟧ := Matrix.of fun e i =>
    ∑ j, if ι j = e then X * w⁻¹ * L.adjugate j i else 0
  refine ⟨D, fun e i => ?_, n + 1, n.succ_pos, ?_⟩
  · simp only [D, Matrix.of_apply]
    refine S.sum_mem fun j _ => ?_
    split_ifs
    · exact S.mul_mem (S.mul_mem X_mem_ratPowerSeries (inv_mem_ratPowerSeries hwS)) (hadj j i)
    · exact S.zero_mem
  · have hLD : G.inKernelMatrix f t * D = (X : F⟦X⟧) • w⁻¹ • (L * L.adjugate) := by
      refine Matrix.ext fun i i' => ?_
      simp only [Matrix.mul_apply, inKernelMatrix, D, Matrix.of_apply, mul_sum, mul_ite, mul_zero,
        Matrix.smul_apply, smul_eq_mul]
      rw [sum_comm]
      simp only [sum_ite_eq, mem_univ, ite_true, hι, L, Matrix.of_apply]
      exact sum_congr rfl fun j _ => by ring
    rw [hLD, Matrix.mul_adjugate, ← hLw, smul_smul, smul_smul, pow_succ]
    congr 1
    linear_combination (X ^ n * X : F⟦X⟧) * PowerSeries.inv_mul_cancel w hw

end Convolutional

end PtpNetwork

end InfoTheory
