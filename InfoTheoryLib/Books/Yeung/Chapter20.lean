/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.Yeung.Chapter19
public import InfoTheoryLib.Network.Convolutional

/-!
# Yeung, Chapter 20: Single-Source Linear Network Coding: Cyclic Networks

This file indexes the formalization of Chapter 20 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Networks.** A network is a `PtpNetwork V E` of `Network.MaxFlowBound`, which may have directed
  cycles; its capacities play no role, except in `PtpNetwork.unitMaxflow`, which sets them to `1`.
* **Local and global encoding kernels.** The local encoding kernels are `ks i e`, from the `i`-th
  imaginary channel into the source `s` to a channel `e` out of `s`, so that `Kₛ` is the matrix
  `(ks i e)`, and `k d e` for the other adjacent pairs of channels `(d, e)`. The global encoding
  kernel of `e` is a vector `f e : Fin ω → R`. `PtpNetwork.IsGlobalKernel s g ks k f` states the
  equations (19.17) and (19.18) with `g = 1`, and (20.39) and (20.40) with `g = X`
  (`Network.Convolutional`).
* **Power series.** The dummy variable `z` of the book is `PowerSeries.X`, and `F⟨z⟩` is
  `ratPowerSeries F` (`ForMathlib.RatPowerSeries`).
* **Decoding kernels.** The decoding kernel `D_t` of Definition 20.10 is an `E × ω` matrix, whose
  rows off the input channels of `t` play no role, and `F_t` is the `ω × E` matrix
  `PtpNetwork.inKernelMatrix f t`, with zero columns off the input channels of `t`.
* **Indexing.** In Figure 20.1 the nodes `s, t, t', u, v` are `0, …, 4` and the channels `(s, t)`,
  `(s, t')`, `(t, u)`, `(t', u)`, `(u, v)`, `(v, t)`, `(v, t')` are `0, …, 6`. In Figure 20.2 the
  nodes `s, x, y, w` are `0, …, 3` and the channels `(s, x)`, `(s, y)`, `(x, y)`, `(y, w)`, `(w, x)`
  are `0, …, 4`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 20.1 Delay-Free Cyclic Networks
* Example 20.1: `example_20_1` (here), the unique solution for the global encoding kernels.
* Example 20.2: `example_20_2` (here), no solution.
* Example 20.3: `example_20_3` (here), three solutions over a ring of characteristic `2`.
* A unique solution when `det (1 - K)` is a unit: `PtpNetwork.existsUnique_isGlobalKernel`, with
  the matrix form `PtpNetwork.isGlobalKernel_iff` (`Network.Convolutional`).

### 20.2 Convolutional Network Codes
* Example 20.4: the scalars (20.20) on the channel `(x, y)` are those of `example_20_8` (here).
* The ring `F⟨z⟩` of rational power series (20.23): `ratPowerSeries`, a subring of `F⟦X⟧`, with
  its property 2, `inv_mem_ratPowerSeries` (`ForMathlib.RatPowerSeries`).
* Example 20.5: `example_20_5`, `example_20_5_inv` and `example_20_5_not` (here).
* Definition 20.6 (Convolutional Network Code): `PtpNetwork.IsConvCode` (`Network.Convolutional`).
  The global encoding kernels are unique for any power series local encoding kernels,
  `PtpNetwork.existsUnique_isGlobalKernel_X` (`Network.Convolutional`).
* Example 20.7: `example_20_7` (here).
* Example 20.8: `example_20_8` (here), the scalars (20.77) on the channel `(x, y)`, from the
  recursions (20.73)–(20.75).
* Theorem 20.9: `theorem_20_9` (here), which is `PtpNetwork.existsUnique_isConvCode`
  (`Network.Convolutional`), with (20.80) in `PtpNetwork.isGlobalKernel_iff`
  (`Network.Convolutional`) and the invertibility of `I - z K` in `isUnit_det_one_sub_X_smul`
  (`ForMathlib.RatPowerSeries`).

### 20.3 Decoding of Convolutional Network Codes
* Definition 20.10 (Convolutional Multicast): `PtpNetwork.IsConvMulticast`, with (20.85) in
  `PtpNetwork.inKernelMatrix` and (20.88)–(20.90) in `PtpNetwork.vecMul_decode`
  (`Network.Convolutional`).
* Example 20.11: `example_20_11` (here), with the decoding kernels `oneCycleDecX` of (20.93) and
  `oneCycleDecY`, of decoding delays `3` and `2`.
* Lemma 20.12: `lemma_20_12` (here), which is `exists_eval_ne_zero_of_degreeOf_lt_card`
  (`ForMathlib.PolyFiniteField`), over any integral domain.
* Theorem 20.13, in part: `PtpNetwork.exists_decoder_of_det_ne_zero` (`Network.Convolutional`), the
  construction (20.106)–(20.111) of a decoding kernel from `ω` input channels whose global encoding
  kernels have a nonzero determinant.

## Not formalized

* The linear broadcast property claimed in Example 20.1, and the message interpretation (20.12)–
  (20.15) of Example 20.2.
* Figures 20.3 and 20.4, the trellis network.
* Theorem 20.13 and Example 20.14, the existence of a convolutional multicast. The proof needs `ω`
  edge-disjoint paths from the source to every node of max-flow at least `ω` in a network with
  cycles, which the library does not have; its routings (`exists_routes`) are for acyclic networks.
  The proof in the book also treats the determinant of `L_t(z)` as a polynomial in the local
  encoding kernels, while the entries of `(I - z K)⁻¹` in (20.98) are not polynomials in them; the
  argument goes through after multiplying by a power of `det (I - z K)`.

## References

Numbers without a source refer to [yeung2008].

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 20
-/

open Finset PowerSeries

@[expose] public noncomputable section

namespace InfoTheory.Yeung

open PtpNetwork

variable {R : Type*} [CommRing R]

/-- The local encoding kernel `Kₛ = I` at the source: the `i`-th imaginary channel goes to the
`i`-th channel. -/
def idSrc {n : ℕ} : Fin 2 → Fin n → R := fun i e => if (e : ℕ) = i then 1 else 0

/-! ### 20.1 Delay-Free Cyclic Networks -/

/-- **Figure 20.1.** The nodes `s, t, t', u, v` are `0, …, 4`, and the channels are `(s, t)`,
`(s, t')`, `(t, u)`, `(t', u)`, `(u, v)`, `(v, t)` and `(v, t')`. -/
def twoCycleNet : PtpNetwork (Fin 5) (Fin 7) :=
  ⟨![0, 0, 1, 2, 3, 4, 4], ![1, 2, 3, 3, 4, 1, 2], fun _ => 1⟩

/-- **(20.1).** The local encoding kernels `K_t = K_{t'} = [1 0]ᵀ`, `K_u = [1 1]ᵀ` and
`K_v = [1 1]`. -/
def twoCycleLocal : Fin 7 → Fin 7 → R := fun d e =>
  if ((d : ℕ), (e : ℕ)) ∈ ({(0, 2), (1, 3), (2, 4), (3, 4), (4, 5), (4, 6)} : Finset (ℕ × ℕ))
  then 1 else 0

/-- **(20.2)–(20.3).** The global encoding kernels of Example 20.1. -/
def twoCycleGlobal : Fin 7 → Fin 2 → R :=
  ![![1, 0], ![0, 1], ![1, 0], ![0, 1], ![1, 1], ![1, 1], ![1, 1]]

/-- **Example 20.1.** On the network of Figure 20.1, the local encoding kernels (20.1) determine the
global encoding kernels (20.2)–(20.3) uniquely. -/
theorem example_20_1 (f : Fin 7 → Fin 2 → R) :
    twoCycleNet.IsGlobalKernel 0 1 idSrc twoCycleLocal f ↔ f = twoCycleGlobal := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    simp only [sum_filter, Fin.sum_univ_seven] at h0 h1 h2 h3 h4 h5 h6
    simp [twoCycleNet, idSrc, twoCycleLocal] at h0 h1 h2 h3 h4 h5 h6
    funext e i
    fin_cases e <;> fin_cases i <;> simp [twoCycleGlobal, h0, h1, h2, h3, h4, h5, h6]
  · rintro rfl e
    fin_cases e <;> simp only [sum_filter, Fin.sum_univ_seven] <;> funext i <;> fin_cases i <;>
      simp [twoCycleNet, idSrc, twoCycleLocal, twoCycleGlobal]

/-- **Figure 20.2.** The nodes `s, x, y, w` are `0, …, 3`, and the channels are `(s, x)`, `(s, y)`,
`(x, y)`, `(y, w)` and `(w, x)`. -/
def oneCycleNet : PtpNetwork (Fin 4) (Fin 5) := ⟨![0, 0, 1, 2, 3], ![1, 2, 2, 3, 1], fun _ => 1⟩

/-- **Figure 20.2(a).** The local encoding kernels `K_x = K_y = [1 1]ᵀ` and `K_w = [1]`. -/
def oneCycleLocal : Fin 5 → Fin 5 → R := fun d e =>
  if ((d : ℕ), (e : ℕ)) ∈ ({(0, 2), (4, 2), (1, 3), (2, 3), (3, 4)} : Finset (ℕ × ℕ)) then 1 else 0

/-- The equations of the global encoding kernels of Figure 20.2 with gain `g` and `Kₛ = I`. -/
lemma oneCycle_eqs {g : R} {f : Fin 5 → Fin 2 → R}
    (h : oneCycleNet.IsGlobalKernel 0 g idSrc oneCycleLocal f) :
    f 0 = g • ![1, 0] ∧ f 1 = g • ![0, 1] ∧ f 2 = g • (f 0 + f 4) ∧ f 3 = g • (f 1 + f 2) ∧
      f 4 = g • f 3 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp only [sum_filter, Fin.sum_univ_five] at h0 h1 h2 h3 h4
  simp only [oneCycleNet, idSrc, oneCycleLocal] at h0 h1 h2 h3 h4
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_, h3.trans ?_, h4.trans ?_⟩ <;>
    congr 1 <;> (funext i; fin_cases i) <;> simp

/-- **Example 20.2.** On the network of Figure 20.2, the local encoding kernels of
Figure 20.2(a) admit no global encoding kernels: (20.8)–(20.10) sum up to (20.11). -/
theorem example_20_2 [Nontrivial R] :
    ¬ ∃ f : Fin 5 → Fin 2 → R, oneCycleNet.IsGlobalKernel 0 1 idSrc oneCycleLocal f := by
  rintro ⟨f, h⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := oneCycle_eqs h
  simp only [one_smul] at h0 h1 h2 h3 h4
  have : f 0 + f 1 = 0 := by linear_combination -h2 - h3 - h4
  have := congrFun this 0
  simp [h0, h1] at this

/-- **(20.16).** The local encoding kernel `Kₛ = [1 1; 0 0]`. -/
def oneCycleSrc' : Fin 2 → Fin 5 → R := fun i _ => if i = 0 then 1 else 0

/-- **(20.17)–(20.19).** The three solutions of Example 20.3, with `f_{(x,y)} = 0`, `[1 0]ᵀ` and
`[0 1]ᵀ`. -/
def oneCycleGlobal' : Fin 3 → Fin 5 → Fin 2 → R :=
  ![![![1, 0], ![1, 0], ![0, 0], ![1, 0], ![1, 0]],
    ![![1, 0], ![1, 0], ![1, 0], ![0, 0], ![0, 0]],
    ![![1, 0], ![1, 0], ![0, 1], ![1, 1], ![1, 1]]]

/-- **Example 20.3.** Over a ring of characteristic `2`, such as an extension field of `GF(2)`, the
local encoding kernels of Figure 20.2(a) with `Kₛ` of (20.16) have the three distinct solutions
(20.17)–(20.19). -/
theorem example_20_3 [CharP R 2] [Nontrivial R] :
    (∀ j, oneCycleNet.IsGlobalKernel 0 1 oneCycleSrc' oneCycleLocal (oneCycleGlobal' (R := R) j)) ∧
      Function.Injective (oneCycleGlobal' (R := R)) := by
  have h2 : (1 : R) + 1 = 0 := CharTwo.add_self_eq_zero 1
  refine ⟨fun j e => ?_, fun j j' hj => ?_⟩
  · fin_cases j <;> fin_cases e <;> simp only [sum_filter, Fin.sum_univ_five] <;> funext i <;>
      fin_cases i <;> simp [oneCycleNet, oneCycleSrc', oneCycleLocal, oneCycleGlobal', h2]
  · have h₀ := congrFun (congrFun hj 2) 0
    have h₁ := congrFun (congrFun hj 2) 1
    fin_cases j <;> fin_cases j' <;> simp [oneCycleGlobal'] at h₀ h₁ ⊢

/-! ### 20.2 Convolutional Network Codes -/

/-- **Example 20.5, (20.26)–(20.34).** In `R⟦X⟧`, `1 - X` times `a` is `1` exactly when `a` is
`1 + X + X² + ⋯`. -/
theorem example_20_5 (a : R⟦X⟧) : (1 - X) * a = 1 ↔ a = PowerSeries.mk 1 := by
  have h := mk_one_mul_one_sub_eq_one R
  constructor
  · intro ha
    linear_combination (PowerSeries.mk 1 : R⟦X⟧) * ha - a * h
  · rintro rfl
    rw [mul_comm, h]

/-- **Example 20.5, (20.28).** `1 / (1 - X) = 1 + X + X² + ⋯` over a field. -/
theorem example_20_5_inv {F : Type*} [Field F] : (1 - X : F⟦X⟧)⁻¹ = PowerSeries.mk 1 := by
  rw [← (example_20_5 _).1 (PowerSeries.mul_inv_cancel _ (by simp))]

/-- **Example 20.5, (20.35)–(20.38).** `1 / (X - X²)` is not a power series. -/
theorem example_20_5_not [Nontrivial R] : ¬ ∃ a : R⟦X⟧, (X - X ^ 2) * a = 1 := by
  rintro ⟨a, ha⟩
  have := congrArg constantCoeff ha
  simp at this

variable {F : Type*} [Field F]

/-- The power series `1 / (1 - X³)`. -/
def invOneSubXCube : F⟦X⟧ := (1 - X ^ 3)⁻¹

lemma invOneSubXCube_mul : (invOneSubXCube : F⟦X⟧) * (1 - X ^ 3) = 1 :=
  PowerSeries.inv_mul_cancel _ (by simp)

lemma invOneSubXCube_mem : (invOneSubXCube : F⟦X⟧) ∈ ratPowerSeries F :=
  inv_mem_ratPowerSeries (Subring.sub_mem _ (Subring.one_mem _)
    (Subring.pow_mem _ X_mem_ratPowerSeries 3))

/-- **(20.47)–(20.52).** The global encoding kernels of the convolutional network code of
Example 20.7. -/
def oneCycleConv : Fin 5 → Fin 2 → F⟦X⟧ :=
  ![![X, 0], ![0, X], ![X ^ 2 * invOneSubXCube, X ^ 4 * invOneSubXCube],
    ![X ^ 3 * invOneSubXCube, X ^ 2 * invOneSubXCube],
    ![X ^ 4 * invOneSubXCube, X ^ 3 * invOneSubXCube]]

/-- **Example 20.7.** On the unit-delay network of Figure 20.2, the local encoding kernels (20.46)
and the global encoding kernels (20.47)–(20.52) form a 2-dimensional convolutional network code:
they solve (20.53)–(20.55). -/
theorem example_20_7 : oneCycleNet.IsConvCode 0 idSrc oneCycleLocal (oneCycleConv (F := F)) := by
  have hu := invOneSubXCube_mul (F := F)
  have hX := X_mem_ratPowerSeries (R := F)
  refine ⟨fun i e _ => ?_, fun d e _ => ?_, fun e i => ?_, fun e => ?_⟩
  · simp only [idSrc]
    split_ifs
    exacts [Subring.one_mem _, Subring.zero_mem _]
  · simp only [oneCycleLocal]
    split_ifs
    exacts [Subring.one_mem _, Subring.zero_mem _]
  · have hXu : ∀ k, (X : F⟦X⟧) ^ k * invOneSubXCube ∈ ratPowerSeries F := fun k =>
      Subring.mul_mem _ (Subring.pow_mem _ hX _) invOneSubXCube_mem
    fin_cases e <;> fin_cases i <;> simp [oneCycleConv, hX, hXu]
  · fin_cases e <;> simp only [sum_filter, Fin.sum_univ_five] <;> funext i <;> fin_cases i <;>
      simp only [Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.reduceFinMk,
        Fin.zero_eta, Matrix.add_cons, Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_add_empty, Matrix.head_cons,
        Matrix.tail_cons, Nat.mod_succ, Nat.one_mod, Nat.reduceEqDiff, Nat.reduceMod,
        Nat.succ_ne_self, Nat.zero_mod, OfNat.ofNat_eq_ofNat, OfNat.ofNat_ne_one,
        OfNat.ofNat_ne_zero, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, Pi.smul_apply, Prod.mk.injEq,
        add_zero, and_self, and_true, idSrc, mem_insert, mem_singleton, mul_one, mul_zero,
        oneCycleConv, oneCycleLocal, oneCycleNet, one_ne_zero, one_smul, or_false, or_self, or_true,
        smul_eq_mul, zero_add, zero_ne_one, ↓reduceIte] <;>
      first
      | ring1
      | linear_combination (X ^ 2 : F⟦X⟧) * hu

/-- **Example 20.8.** When the source pipelines the message `x = (∑ aⱼ zʲ, ∑ bⱼ zʲ)`, the channel
`(x, y)` of Example 20.7 carries the scalars (20.77): `0, 0, a₀, a₁, a₂ + b₀, a₀ + a₃ + b₁` at
times `0, …, 5`, as computed by the recursions (20.73)–(20.75). These are also the scalars (20.20)
of Example 20.4. -/
theorem example_20_8 (x : Fin 2 → F⟦X⟧) :
    let m := x ⬝ᵥ oneCycleConv 2
    let a := fun j => coeff j (x 0)
    let b := fun j => coeff j (x 1)
    coeff 0 m = 0 ∧ coeff 1 m = 0 ∧ coeff 2 m = a 0 ∧ coeff 3 m = a 1 ∧
      coeff 4 m = a 2 + b 0 ∧ coeff 5 m = a 0 + a 3 + b 1 := by
  intro M a b
  obtain ⟨h0, h1, h2, h3, h4⟩ := oneCycle_eqs (example_20_7 (F := F)).2.2.2
  set m : Fin 5 → F⟦X⟧ := fun e => x ⬝ᵥ oneCycleConv e
  have q0 : m 0 = X * x 0 := by
    change x ⬝ᵥ _ = _
    rw [h0, dotProduct_smul]
    simp [dotProduct]
  have q1 : m 1 = X * x 1 := by
    change x ⬝ᵥ _ = _
    rw [h1, dotProduct_smul]
    simp [dotProduct]
  have q2 : m 2 = X * (m 0 + m 4) := by
    change x ⬝ᵥ _ = X * (x ⬝ᵥ _ + x ⬝ᵥ _)
    rw [h2, dotProduct_smul, dotProduct_add, smul_eq_mul]
  have q3 : m 3 = X * (m 1 + m 2) := by
    change x ⬝ᵥ _ = X * (x ⬝ᵥ _ + x ⬝ᵥ _)
    rw [h3, dotProduct_smul, dotProduct_add, smul_eq_mul]
  have q4 : m 4 = X * m 3 := by
    change x ⬝ᵥ _ = X * (x ⬝ᵥ _)
    rw [h4, dotProduct_smul, smul_eq_mul]
  -- the recursions (20.73)–(20.75)
  have r0 : ∀ n, coeff (n + 1) (m 0) = coeff n (x 0) := fun n => by rw [q0, coeff_succ_X_mul]
  have r1 : ∀ n, coeff (n + 1) (m 1) = coeff n (x 1) := fun n => by rw [q1, coeff_succ_X_mul]
  have r2 : ∀ n, coeff (n + 1) (m 2) = coeff n (m 0) + coeff n (m 4) := fun n => by
    rw [q2, coeff_succ_X_mul, map_add]
  have r3 : ∀ n, coeff (n + 1) (m 3) = coeff n (m 1) + coeff n (m 2) := fun n => by
    rw [q3, coeff_succ_X_mul, map_add]
  have r4 : ∀ n, coeff (n + 1) (m 4) = coeff n (m 3) := fun n => by rw [q4, coeff_succ_X_mul]
  have z0 : coeff 0 (m 0) = 0 := by rw [q0, coeff_zero_X_mul]
  have z1 : coeff 0 (m 1) = 0 := by rw [q1, coeff_zero_X_mul]
  have z2 : coeff 0 (m 2) = 0 := by rw [q2, coeff_zero_X_mul]
  have z3 : coeff 0 (m 3) = 0 := by rw [q3, coeff_zero_X_mul]
  have z4 : coeff 0 (m 4) = 0 := by rw [q4, coeff_zero_X_mul]
  change coeff 0 (m 2) = 0 ∧ coeff 1 (m 2) = 0 ∧ coeff 2 (m 2) = a 0 ∧ coeff 3 (m 2) = a 1 ∧
    coeff 4 (m 2) = a 2 + b 0 ∧ coeff 5 (m 2) = a 0 + a 3 + b 1
  simp only [r0, r1, r2, r3, r4, z0, z1, z2, z3, z4, a, b, add_zero, true_and]
  ring

/-- **Theorem 20.9.** -/
alias theorem_20_9 := existsUnique_isConvCode

/-! ### 20.3 Decoding of Convolutional Network Codes -/

/-- **(20.93).** The decoding kernel at node `x`, on the rows of the channels `(s, x)` and
`(w, x)`. -/
def oneCycleDecX : Matrix (Fin 5) (Fin 2) F⟦X⟧ :=
  ![![X ^ 2, -X ^ 3], 0, 0, 0, ![0, 1 - X ^ 3]]

/-- The decoding kernel at node `y`, on the rows of the channels `(s, y)` and `(x, y)`. -/
def oneCycleDecY : Matrix (Fin 5) (Fin 2) F⟦X⟧ :=
  ![0, ![-X ^ 3, X], ![1 - X ^ 3, 0], 0, 0]

/-- **Example 20.11.** The convolutional network code of Example 20.7 is a 2-dimensional
convolutional multicast: nodes `x` and `y` decode with delays `3` and `2`, and node `w` has
max-flow `1`. -/
theorem example_20_11 :
    oneCycleNet.IsConvMulticast 0 idSrc oneCycleLocal (oneCycleConv (F := F)) := by
  have hX := X_mem_ratPowerSeries (R := F)
  have hpoly : (1 - X ^ 3 : F⟦X⟧) ∈ ratPowerSeries F :=
    Subring.sub_mem _ (Subring.one_mem _) (Subring.pow_mem _ hX 3)
  have hXk : ∀ k, (X : F⟦X⟧) ^ k ∈ ratPowerSeries F := fun k => Subring.pow_mem _ hX k
  have hu := invOneSubXCube_mul (F := F)
  refine ⟨example_20_7, fun t ht hmax => ?_⟩
  fin_cases t
  · exact absurd rfl ht
  · -- (20.93)–(20.94): `F_x D_x = z³ I`
    refine ⟨oneCycleDecX, fun e i => ?_, 3, by norm_num, Matrix.ext fun i j => ?_⟩
    swap
    · rw [Matrix.mul_apply, Fin.sum_univ_five]
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.zero_eta, Matrix.cons_val,
          Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.of_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, Matrix.smul_apply,
          Nat.reduceAdd, Pi.zero_apply, add_zero, inKernelMatrix, mul_neg, mul_one, mul_zero, ne_eq,
          neg_zero, not_false_eq_true, oneCycleConv, oneCycleDecX, oneCycleNet, one_ne_zero,
          smul_eq_mul, zero_add, zero_mul, zero_ne_one, ↓reduceIte] <;>
        first
        | ring1
        | linear_combination (X ^ 2 : F⟦X⟧) * hu
        | linear_combination (X ^ 3 : F⟦X⟧) * hu
        | linear_combination (X ^ 4 : F⟦X⟧) * hu
    fin_cases e <;> fin_cases i <;> simp [oneCycleDecX, hXk, hpoly]
  · -- `F_y D_y = z² I`
    refine ⟨oneCycleDecY, fun e i => ?_, 2, by norm_num, Matrix.ext fun i j => ?_⟩
    swap
    · rw [Matrix.mul_apply, Fin.sum_univ_five]
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.isValue, Fin.mk_one, Fin.reduceEq, Fin.reduceFinMk, Fin.zero_eta,
          Matrix.cons_val, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.of_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
          Matrix.smul_apply, Nat.reduceAdd, Pi.zero_apply, add_zero, inKernelMatrix, mul_neg,
          mul_one, mul_zero, ne_eq, neg_zero, not_false_eq_true, oneCycleConv, oneCycleDecY,
          oneCycleNet, one_ne_zero, smul_eq_mul, zero_add, zero_mul, zero_ne_one, ↓reduceIte] <;>
        first
        | ring1
        | linear_combination (X ^ 2 : F⟦X⟧) * hu
        | linear_combination (X ^ 3 : F⟦X⟧) * hu
        | linear_combination (X ^ 4 : F⟦X⟧) * hu
    fin_cases e <;> fin_cases i <;> simp [oneCycleDecY, hX, hXk, hpoly]
  · have := (PtpNetwork.maxflow_le (⟨oneCycleNet.tail, oneCycleNet.head, fun _ => 1⟩ :
      PtpNetwork (Fin 4) (Fin 5)) (s := 0) (t := 3) (U := {0, 1, 2}) (by decide)
      (by decide)).trans_eq (sum_cutEdges_eq (m := 1) (by decide))
    have h := hmax.trans this
    norm_num at h

/-- **Lemma 20.12.** -/
alias lemma_20_12 := exists_eval_ne_zero_of_degreeOf_lt_card

end InfoTheory.Yeung
