/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.GuptaKumarCells
public import InfoTheoryLib.Network.GuptaKumarLemma2

/-!
# El Gamal & Kim, Lecture 20: Gaussian Networks

This file indexes the formalization of Lecture 20 of [elgamal2010]. Operationally, for networks in
which the nodes do not relay, we prove the cutset bound, the capacity of the `N`-sender MAC, the
bounds of the interference example, and the upper bound `D(N)` of the random network for a fixed
gain matrix. For the rest of the lecture, which needs relays with continuous alphabets, we prove the
results on the rates: the constant gap of noisy network coding, the order of the `N`-relay network,
and the two scaling bounds of the Gupta–Kumar network, with their probabilistic Lemmas 1 and 2.

## Conventions

* **Rates.** Rates are in bits with `2 ^ ⌈n R⌉` messages, and informations are in nats, so that a
  bound is written as `R * log 2 ≤ I`. The formulas `C(x)` are `gaussCap x = ½ log (1 + x)`, in
  nats.
* **Networks.** The gain matrix is rectangular, `G : Matrix r t ℝ`, from the senders `t` to the
  receivers `r`. A code is a `GNCode`: each sender encodes its message only, with no relaying.
* **Power.** `SatisfiesPower` is the constraint averaged over the messages, as in the notes.
* **Distances.** In the upper bound, `W = 2 |U|` is the variable with the uniform law `gkUnif` on
  `(0, N^{1/2}]`, and `gkLaw N` is the law of `2N` independent copies.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### The network and the cutset bound (pages 20-2 to 20-4)
* The code and the rates: `GNCode`, `GNCode.SatisfiesPower`, `GNCode.errProb`, `IsAchievableGN`
  (`Network.GaussianNetCode`).
* The cutset bound, with the covariance made diagonal by the independence of the messages:
  `IsAchievableGN.sum_le`.

### The constant gap (pages 20-5 to 20-7)
* `K ≼ tr(K) I`: `posSemidef_trace_smul_sub`; the relaxation of the cutset bound: `cutset_relax`,
  here `gaussian_cutset_relax` (`Network.GaussianNetBounds`).
* The rate of Theorem 1: `nncGaussRate` (`Network.GaussianNetBounds`).
  The two terms of its derivation: `gk_nnc_gap`,
  `gvRate_half` (`Network.GuptaKumar`).
* The gap: `nnc_gap_le`, `gvRate_le_nncGaussRate_add`, here `gaussian_constant_gap`.

### Capacity scaling, examples (pages 20-10 to 20-17)
* The `N`-sender MAC: `C(N) = (1 / N) C(N P)`, `gnSymCapacity_mac` (`Network.GaussianNetTDM`), here
  `mac_symmetric_capacity`; its order: `isTheta_gaussCap_div` (`Network.GuptaKumar`), here
  `mac_order`.
* The interference example: time division `isAchievableGN_ic`, the bounds
  `IsAchievableGN.ic_le_single` and `IsAchievableGN.ic_le_rate`; the determinant
  `det_interference`, `gvRate_interference`; the case `a = 1`: here `ic_one_rate`.
* The `N`-relay network, formulas only: the interference `relayInterference_le`, the multi-hop rate
  `relay_multihop_ge`, the broadcast bound `relay_upper_le`, `gvRate_rankOne`, the rate without
  relaying `tendsto_relay_direct`.

### The Gupta–Kumar network, lower bound (pages 20-21 to 20-28, 20-36 to 20-38)
* The distance and the received power: `gk_dist_sq_le`, `gk_received_ge`.
* The interference: `summable_gkOne`, `summable_gkTwo`, `gkInterference_eq` (`Network.GuptaKumar`).
* The rate: `gkRate`, `gkRate_ge`.
* The cells: `GKCell`, `gkRoute`, `gkS`, `gkL`, the Chernoff bound `gkProb_count_ge`, and
  `gkProb_empty_le`, `gkProb_gkS_ge`, `gkProb_gkL_ge` (`Network.GuptaKumarCells`).
* **Lemma 1:** `gk_lemma1`, here `lemma_20_1`.
* **The lower bound** on the rate, with probability tending to one: `gkRate_whp`, here
  `gupta_kumar_lower`.

### The Gupta–Kumar network, upper bound (pages 20-30 to 20-34, 20-39 to 20-42)
* The chain of inequalities of page 20-33: `gvRate_le_sum_log`; the operational form for a fixed
  network: `gvRate_submatrix_le`, `IsAchievableGN.sum_le_gain`, `IsAchievableGN.sum_le_sum_log`.
* The integrals: `integral_gkLog_le`, `integral_gkLog_ge`, `integral_gkLog_sq_le`
  (`Network.GuptaKumarLemma2`). Chebyshev's inequality: `pi_sum_ge_le`, `pi_gkLog_ge_le`.
* **Lemma 2:** `gkD_whp`, here `lemma_20_2`.
* **The upper bound**, with probability tending to one: `gk_upper_whp`, `gk_capacity_upper_whp`,
  here `gupta_kumar_upper`.

## Differences from the notes

* **Routes.** Lemma 1 is proved for routes along the row of the source and then the column of the
  destination, instead of straight lines. The probability that a route crosses a cell is at most
  `2 / m` by counting (`prob_route_le`), so the torus and the expected number of hops of pages 20-36
  and 20-37 are not needed. The order is the same. The node-blocks of the scheme are unchanged since
  these routes also use only neighboring cells.
* **Cell model.** Only the cells of the nodes matter, so a pair is a uniform pair of cells of an
  `m × m` grid, with `m = ⌊(N / log N)^{1/2}⌋`. The cells have an area between `log N` and
  `4 log N`. A cell is called empty if it has no source, which is stronger than having no node.
* **Chernoff.** We take `t = 1` in `gkProb_count_ge`, so that `δ` of the notes does not appear. This
  gives a better bound than the notes and avoids the issue on page 20-38 listed below.
* **Lemma 2.** The bounds on the integrals are simplified: `log (1 / u) ≤ 4 u^{-1/4}` replaces the
  exact integrals of `log (1 / u)` and of its square, and the same tail is used for `X` and `X²`.
* **Upper bound.** The sum rate is bounded directly: in `IsAchievableGN.sum_le_gain` the network is
  any submatrix of `G`, which replaces the reduction to `N'` pairs and to the augmented network at
  the level of the gains.

## Not formalized

* **Relays with continuous alphabets.** Theorem 1 of page 20-6 as a coding theorem (only the rate,
  the terms and the gap are proved), the coding theorem of the multi-hop scheme, the broadcast bound
  of the relay network as a converse, the block Markov scheme of the cellular network. The
  discrete noisy network coding theorem is `isAchievableMN_nnc` of Lecture 19, whose extension to
  Gaussian channels needs a discretization that is not in the library.
* **Treating interference as noise** as a coding theorem, on which `gkRate` depends. So `gkRate_whp`
  bounds the formula for the rate of the scheme. The bound of the interference by the series of page
  20-27 from the positions of the interferers is not formalized either: only the series is.
* **The geometry of the upper bound.** The mirror nodes and the claim that a constant fraction of
  the sources is on the left with a destination on the right. The fact that `G` is positive
  semidefinite is cited by the notes from Lévêque and Telatar, and it is a hypothesis of
  `gk_upper_whp`, for positive distances (it can hold: `gupta_kumar_upper_hypotheses`). Also, the
  law of the distances is taken to be `gkLaw`, without the conditioning due to the relabeling.
* The simple schemes of page 20-22, the time sharing bound of page 20-4, and absorption (page
  20-34).

## Issues in the notes

* **Page 20-6.** The entropies are printed as `(|S| / 2) log (2πe)` and `(|S| / 2) log (πe)`. The
  variances are `2` and `1`, so the entropies are `(|S| / 2) log (4πe)` and `(|S| / 2) log (2πe)`.
  Their difference is right (`gk_nnc_gap`). Confirmed against the PDF.
* **Page 20-12.** The exponent `k - 1` of the determinant should be `N - 1` (`det_interference`).
* **Page 20-15.** The rate without relaying is `C(P (N + 1)^{-ν})`, the distance being `N + 1`; this
  does not change the order.
* **Page 20-16.** The sum `∑_{j=1}^{k+1}` should end at `N + 1`.
* **Page 20-21.** A second "Theorem 1", and "sum-capacity" for the symmetric capacity.
* **Page 20-28.** The event `E₃` is not defined; it should be `E₂`.
* **Page 20-30.** The notes say that the probability of the case considered tends to `0`. It is the
  probability of the other case that tends to `0`: otherwise the bound would hold almost never.
* **Page 20-37.** The equation `(N² / log N) P{I_{jc} = 1} / log N = N E(H_j)` has an extra factor
  `1 / log N`: the claimed `P{I_{jc} = 1} = Θ((log N / N)^{1/2})` follows only without it. Confirmed
  against the PDF.
* **Page 20-38.** `L_c = ∑ I_{kc}` and `∑_{j=1}^n` should be `∑_{j=1}^N I_{jc}`. The choice
  `δ = 2 (log N / E(L_c))^{1/2}` gives the bound `1 / N` (`printed_delta_bound`), not `1 / (3 N²)`,
  and the union bound then gives only `1 / log N`, not `1 / (3 N)`. A larger `δ` is needed for the
  printed claim, and the conclusion of Lemma 1 is unaffected. Confirmed against the PDF.
* **Page 20-39.** `D(N)` has `2 N` terms, but `E(D(N)) = N E(X(N))` is printed. And `U` is
  `Unif[0, N^{1/2}]`, whereas `|U_j|` is on `[0, N^{1/2} / 2]`: it is `2 |U_j|` that has this law.
  This affects only constants.
* **Page 20-40.** `∫_1^{u₀} log (1 + a u^{-ν'} k) du ≥ ∫_1^{u₀} log (1 + a) du` fails for `a > 1`:
  at `u₀` the integrand is `log 2` (`printed_log_lower_fails`). With `log 2` the proof goes through
  (`gkLog_ge_log_two`).

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 20
-/

open Real Finset Matrix Filter Topology Asymptotics
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

section Printed

/-- **Page 20-38 of [elgamal2010].** The choice `δ = 2 (log N / E)^{1/2}` makes the Chernoff bound
`exp (-E δ² / 4)` equal to `1 / N`, and not `1 / (3 N²)` as printed. -/
theorem printed_delta_bound {E : ℝ} (hE : 0 < E) {N : ℝ} (hN : 1 ≤ N) :
    exp (-(E * (2 * √(log N / E)) ^ 2 / 4)) = 1 / N := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ log N := log_nonneg hN
  have e : E * (2 * √(log N / E)) ^ 2 / 4 = log N := by
    rw [mul_pow, sq_sqrt (by positivity)]
    field_simp
    ring
  rw [e, exp_neg, exp_log hN0, one_div]

/-- **Page 20-40 of [elgamal2010]: the printed lower bound fails.** For `a > 1`, the integrand at
`u₀` is `log 2`, which is smaller than `log (1 + a)`. -/
theorem printed_log_lower_fails {c ν a : ℝ} (hc : 0 < c) (hν : 0 < ν) (ha : 1 < a) :
    gkLog c ν (gkU c ν) < log (1 + a) := by
  have hu : 0 < gkU c ν := rpow_pos_of_pos hc _
  have e : c * gkU c ν ^ (-ν) = 1 := by
    rw [rpow_neg hu.le, gkU_pow hc hν]
    field_simp
  rw [gkLog, e]
  exact log_lt_log (by norm_num) (by linarith)

end Printed

section Aliases

/-- **Page 20-5.** The relaxation of the cutset bound. -/
theorem gaussian_cutset_relax {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
    [Nonempty t] (G : Matrix r t ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) {P : ℝ} (hP : 0 ≤ P)
    (hT : K.trace ≤ Fintype.card t * P) :
    gvRate G K ≤ gvRate G ((P / 2) • 1) + (Fintype.card r : ℝ) / 2 * log (2 * Fintype.card t) :=
  cutset_relax G hK hP hT

/-- **Page 20-7.** The cutset bound exceeds the rate of Theorem 1 by at most `(N / 2) log (4 N)`. -/
theorem gaussian_constant_gap {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
    [Nonempty t] (G : Matrix r t ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) {P : ℝ} (hP : 0 ≤ P)
    (hT : K.trace ≤ Fintype.card t * P) {N : ℕ} (hN : Fintype.card t + Fintype.card r = N) :
    gvRate G K ≤ nncGaussRate G P + (N : ℝ) / 2 * log (4 * N) :=
  gvRate_le_nncGaussRate_add G hK hP hT hN

/-- **Page 20-10.** The symmetric capacity of the `N`-sender AWGN MAC. -/
theorem mac_symmetric_capacity {N : ℕ} (hN : 0 < N) {P : ℝ≥0} (hP : 0 < P) :
    gnSymCapacity (macGain N) (fun _ => {()}) P * log 2 = gaussCap (N * P) / N :=
  gnSymCapacity_mac hN hP

/-- **Page 20-10.** The order of the symmetric capacity of the `N`-sender AWGN MAC. -/
theorem mac_order {P : ℝ} (hP : 0 < P) :
    (fun N : ℕ => gaussCap ((N : ℝ) * P) / N) =Θ[atTop] fun N : ℕ => log N / N := by
  simpa using isTheta_gaussCap_div (k := 1) one_pos hP

/-- **Page 20-13.** For `a = 1`, the cutset bound of the interference example is `(1 / N) C(N² P)`,
which has the order `log N / N` of time division. -/
theorem ic_one_rate {N : ℕ} (hN : 0 < N) {P : ℝ} (hP : 0 ≤ P) :
    gvRate (icGain N 1) (P • 1) / N = 1 / N * gaussCap ((N : ℝ) ^ 2 * P) := by
  rw [gvRate_interference hN 1 hP]
  have h₀ : gaussCap (((1 : ℝ) - 1) ^ 2 * P) = 0 := by simp [gaussCap]
  have e : ((1 : ℝ) * ((N : ℝ) - 1) + 1) = N := by ring
  rw [h₀, e]
  ring

/-- **Lemma 1, page 20-28**, for routes along the rows and the columns. -/
theorem lemma_20_1 :
    Tendsto (fun N : ℕ => gkProb (fun ω : Fin N → GKCell (gkSide N) × GKCell (gkSide N) =>
      (∃ c : GKCell (gkSide N), ∀ j, ¬(ω j).1 = c) ∨
        13 * ((N : ℝ) * log N) ^ (1 / 2 : ℝ) ≤ (gkS ω : ℝ) + gkL ω)) atTop (𝓝 0) :=
  gk_lemma1

/-- **Theorem 1 of page 20-21, the lower bound**, on the rate of the cellular scheme. -/
theorem gupta_kumar_lower {ν P : ℝ} (hν : 2 < ν) (hP : 0 < P) :
    ∃ c' > 0, Tendsto (fun N : ℕ =>
      gkProb (fun ω : Fin N → GKCell (gkSide N) × GKCell (gkSide N) =>
        gkRate ν P (gkArea N) ((gkS ω : ℝ) + gkL ω) <
          c' * ((N : ℝ) ^ (-(1 / 2) : ℝ) * (log N) ^ (-((ν + 1) / 2))))) atTop (𝓝 0) :=
  gkRate_whp hν hP

/-- **Lemma 2, page 20-34.** -/
theorem lemma_20_2 {ν P : ℝ} (hν : 2 < ν) (hP : 0 < P) :
    ∃ b > 0, Tendsto (fun N : ℕ =>
      gkLaw N {w | b * ((N : ℝ) ^ (1 / 2 + 1 / ν) * log N) ≤ gkD ν P N w}) atTop (𝓝 0) :=
  gkD_whp hν hP

/-- **Theorem 1 of page 20-21, the upper bound**, with the positive semidefinite gain matrix as a
hypothesis. -/
theorem gupta_kumar_upper {ν : ℝ} {P : ℝ≥0} (hν : 2 < ν) (hP : 0 < (P : ℝ))
    (G : ∀ N : ℕ, (Fin (2 * N) → ℝ) → Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ)
    (hG : ∀ N w, (∀ j, 0 < w j) → (G N w).PosSemidef)
    (hdiag : ∀ N w, (∀ j, 0 < w j) → ∀ j, G N w j j = w j ^ (-(ν / 2))) :
    ∃ b > 0, Tendsto (fun N : ℕ => gkLaw N {w | ∃ (n : ℕ) (d s : Fin n → Fin (2 * N))
      (D : Fin n → Finset (Fin n)) (R : Fin n → ℝ), Function.Injective d ∧ Function.Injective s ∧
        (∀ j, (D j).Nonempty) ∧ IsAchievableGN ((G N w).submatrix d s) D P R ∧
        b * ((N : ℝ) ^ (1 / 2 + 1 / ν) * log N) ≤ (∑ j, R j) * log 2}) atTop (𝓝 0) :=
  gk_capacity_upper_whp hν hP G hG hdiag

/-- The hypotheses of `gupta_kumar_upper` can be satisfied: for instance by a diagonal matrix. -/
theorem gupta_kumar_upper_hypotheses (ν : ℝ) :
    ∃ G : ∀ N : ℕ, (Fin (2 * N) → ℝ) → Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ,
      (∀ N w, (∀ j, 0 < w j) → (G N w).PosSemidef) ∧
        ∀ N w, (∀ j, 0 < w j) → ∀ j, G N w j j = w j ^ (-(ν / 2)) := by
  refine ⟨fun _ w => Matrix.diagonal fun j => w j ^ (-(ν / 2)), fun N w hw => ?_, fun N w _ j => ?_⟩
  · exact posSemidef_diagonal_iff.mpr fun j => rpow_nonneg (hw j).le _
  · simp

end Aliases

end InfoTheory.ElGamalKim
