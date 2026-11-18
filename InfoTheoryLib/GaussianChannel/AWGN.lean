/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.AverageError
public import InfoTheoryLib.GaussianChannel.Achievability
public import InfoTheoryLib.GaussianChannel.Converse

/-!
# The additive white Gaussian noise channel with a channel gain

El Gamal and Kim's lecture notes model the discrete-time additive white Gaussian noise (AWGN)
channel as `Yᵢ = g Xᵢ + Zᵢ`, with channel gain `g`, noise `Zᵢ` i.i.d. `N(0, 1)` and the average
power constraint `∑ᵢ xᵢ²(m) ≤ nP` on every codeword. The capacity depends only on the received
signal-to-noise ratio `S = g²P`: it is `C(S) = ½ log (1 + S)`, the Gaussian capacity function.

The channel `Y = gX + Z` with power `P` is the channel `Y = X' + Z` with power `g²P`, applied to the
scaled codewords `X' = gX`. We derive its capacity, defined with the average probability of error
and rates in bits, from Theorem 9.1.1 of Cover and Thomas (`gaussianOpCapacity_eq`).

## Main definitions

* `gaussianCapacityFun x`: the Gaussian capacity function `C(x) = ½ log (1 + x)`, in nats.
* `GaussianCode.scale g c`: the code `c` with its codewords multiplied by the gain `g`.
* `IsAchievableAWGNRate g P R`: the rate `R` (in bits) is achievable over `Y = gX + Z`.
* `opCapacityAWGN g P`: the capacity of the AWGN channel, in bits.

## Main statements

* `opCapacityAWGN_eq`: **Theorem 3 of Lecture 3**, the capacity of the AWGN channel is
  `C(g²P)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real MeasureTheory Filter Topology Finset
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-- **Notation (Lecture 1).** The Gaussian capacity function `C(x) = ½ log (1 + x)`, in nats. -/
def gaussianCapacityFun (x : ℝ) : ℝ := 1 / 2 * log (1 + x)

namespace GaussianCode

variable {M n : ℕ}

/-- The code `c` used over the channel `Y = gX + Z`: the code over `Y = X + Z` whose codewords are
`g xⁿ(m)`. -/
def scale (g : ℝ) (c : GaussianCode M n) : GaussianCode M n where
  enc w := g • c.enc w
  dec := c.dec
  measurable_dec := c.measurable_dec

lemma SatisfiesPower.scale {c : GaussianCode M n} {P : ℝ} (hc : c.SatisfiesPower P) (g : ℝ) :
    (c.scale g).SatisfiesPower (g ^ 2 * P) := fun w => by
  have h := hc w
  simp only [GaussianCode.scale, Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_sum]
  nlinarith [sq_nonneg g]

lemma scale_scale_inv {g : ℝ} (hg : g ≠ 0) (c : GaussianCode M n) :
    (c.scale g⁻¹).scale g = c := by
  cases c
  simp only [GaussianCode.scale, smul_smul, mul_inv_cancel₀ hg, one_smul]

end GaussianCode

/-- **Definition (Lecture 3).** A rate `R`, in bits per transmission, is achievable over the AWGN
channel `Y = gX + Z`, `Z ∼ N(0, 1)`, with power constraint `P`, if there is a sequence of
`(2^{nR}, n)` codes satisfying the power constraint whose average probability of error tends to
`0`. -/
def IsAchievableAWGNRate (g : ℝ) (P : ℝ≥0) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, GaussianCode (2 ^ ⌈n * R⌉₊) n, (∀ n, (c n).SatisfiesPower P) ∧
    Tendsto (fun n => ((c n).scale g).avgErrProb 1) atTop (𝓝 0)

/-- **Definition (Lecture 3).** The capacity of the AWGN channel, in bits per transmission. -/
def opCapacityAWGN (g : ℝ) (P : ℝ≥0) : ℝ := sSup {R | IsAchievableAWGNRate g P R}

/-- The received power `S = g²P` as a nonnegative real. -/
def receivedPower (g : ℝ) (P : ℝ≥0) : ℝ≥0 := ⟨g ^ 2 * P, mul_nonneg (sq_nonneg g) P.2⟩

lemma coe_receivedPower (g : ℝ) (P : ℝ≥0) : (receivedPower g P : ℝ) = g ^ 2 * P := rfl

/-- **Theorem 3 of Lecture 3 (converse).** Every achievable rate is at most `C(g²P)` bits. -/
theorem IsAchievableAWGNRate.le {g : ℝ} {P : ℝ≥0} {R : ℝ} (h : IsAchievableAWGNRate g P R) :
    R ≤ gaussianCapacityFun (g ^ 2 * P) / log 2 := by
  obtain ⟨c, hpow, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  have h1 : ∀ n, ((c n).scale g).avgErrProb 1 ≤ 1 := fun n =>
    ((c n).scale g).avgErrProb_le_maxErrProb 1 |>.trans (((c n).scale g).maxErrProb_le_one 1)
  have hpow' : ∀ n, ((c n).scale g).SatisfiesPower (receivedPower g P) := fun n =>
    (hpow n).scale g
  have key := le_of_converse_bound (R := R * log 2) (C := gaussianCapacityFun (g ^ 2 * P)) hc h1
    fun n _ => by
      have hb := ((c n).scale g).one_sub_avgErrProb_mul_log_le 1 one_ne_zero (hpow' n) (hpos n)
      rw [coe_receivedPower, NNReal.coe_one, div_one] at hb
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (by linarith [h1 n])) hb
      exact log_le_log (Nat.cast_pos.2 (Nat.ceil_pos.2 (exp_pos _)))
        (by exact_mod_cast ceil_exp_le_two_pow n R)
  rwa [le_div_iff₀ (log_pos one_lt_two)]

/-- **Theorem 3 of Lecture 3 (achievability).** For `g ≠ 0`, every rate below `C(g²P)` bits is
achievable. -/
theorem isAchievableAWGNRate_of_lt {g : ℝ} (hg : g ≠ 0) {P : ℝ≥0} {R : ℝ}
    (hR : R < gaussianCapacityFun (g ^ 2 * P) / log 2) : IsAchievableAWGNRate g P R := by
  have hl := log_pos one_lt_two
  rcases le_or_gt R 0 with hR0 | hR0
  · -- With `R ≤ 0` there is a single message, and the decoder never errs.
    have h1 : ∀ n : ℕ, 2 ^ ⌈n * R⌉₊ = 1 := fun n => by
      rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0), pow_zero]
    refine ⟨fun n => ⟨fun _ => 0, fun _ => ⟨0, by rw [h1 n]; norm_num⟩, measurable_const⟩,
      fun n w => by simpa using mul_nonneg (Nat.cast_nonneg n) P.2, ?_⟩
    refine tendsto_const_nhds.congr fun n => ?_
    symm
    refine le_antisymm ?_ (GaussianCode.avgErrProb_nonneg _ _)
    rw [GaussianCode.avgErrProb]
    refine div_nonpos_of_nonpos_of_nonneg (sum_nonpos fun w _ => ?_) (Nat.cast_nonneg _)
    have : Subsingleton (Fin (2 ^ ⌈n * R⌉₊)) := by rw [h1 n]; infer_instance
    simp [GaussianCode.condErrProb, GaussianCode.scale, Subsingleton.elim _ w]
  · -- Unscale Cover and Thomas's codes of a rate `R'` with `R log 2 < R' < C(g²P)` (in nats).
    have hRC : R * log 2 < gaussianCapacityFun (g ^ 2 * P) := (lt_div_iff₀ hl).1 hR
    obtain ⟨R', hR'1, hR'2⟩ : ∃ R', R * log 2 < R' ∧ R' < gaussianCapacityFun (g ^ 2 * P) :=
      ⟨(R * log 2 + gaussianCapacityFun (g ^ 2 * P)) / 2, by linarith, by linarith⟩
    obtain ⟨c', hpow', hc'⟩ := isAchievableGaussianRate_of_lt (P := receivedPower g P)
      (N := 1) one_ne_zero (by
        rw [coe_receivedPower, NNReal.coe_one, div_one]
        exact hR'2)
    have hgap : 0 < R' - R * log 2 := by linarith
    have hev : ∀ᶠ n : ℕ in atTop, 2 ^ ⌈n * R⌉₊ ≤ ⌈exp (n * R')⌉₊ := by
      filter_upwards [eventually_ge_atTop ⌈log 2 / (R' - R * log 2)⌉₊] with n hn
      have hn' : log 2 ≤ n * (R' - R * log 2) := (div_le_iff₀ hgap).1 (Nat.ceil_le.1 hn)
      have hreal : ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ exp (n * R') := by
        push_cast
        calc (2 : ℝ) ^ ⌈n * R⌉₊ = 2 ^ (⌈n * R⌉₊ : ℝ) := (rpow_natCast 2 _).symm
          _ ≤ 2 ^ (n * R + 1) := rpow_le_rpow_of_exponent_le one_le_two
              (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) hR0.le)).le
          _ = exp (n * R * log 2 + log 2) := by
              rw [rpow_def_of_pos two_pos]
              congr 1
              ring
          _ ≤ exp (n * R') := exp_le_exp.2 (by nlinarith [hn'])
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hsub : ∀ n : ℕ, ∃ c : GaussianCode (2 ^ ⌈n * R⌉₊) n, c.SatisfiesPower P ∧
        (2 ^ ⌈n * R⌉₊ ≤ ⌈exp (n * R')⌉₊ →
          (c.scale g).avgErrProb 1 ≤ (c' n).maxErrProb 1) := fun n => by
      have : NeZero (2 ^ ⌈n * R⌉₊) := ⟨by positivity⟩
      by_cases h : 2 ^ ⌈n * R⌉₊ ≤ ⌈exp (n * R')⌉₊
      · set c'' := (c' n).reindex (Fin.castLEEmb h)
        refine ⟨c''.scale g⁻¹, fun w => ?_, fun _ => ?_⟩
        · have h2 := (GaussianCode.SatisfiesPower.reindex (c' n) (hpow' n)
            (Fin.castLEEmb h)).scale g⁻¹ w
          rw [coe_receivedPower] at h2
          refine h2.trans_eq ?_
          field_simp
        · rw [GaussianCode.scale_scale_inv hg]
          refine (c''.avgErrProb_le_maxErrProb 1).trans (GaussianCode.maxErrProb_le _ _
            (by positivity) fun j => ?_)
          exact ((c' n).condErrProb_reindex_le 1 _ j).trans ((c' n).condErrProb_le_maxErrProb 1 _)
      · exact ⟨⟨fun _ => 0, fun _ => 0, measurable_const⟩,
          fun w => by simpa using mul_nonneg (Nat.cast_nonneg n) P.2, fun h' => absurd h' h⟩
    choose c hpow hc using hsub
    refine ⟨c, hpow, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc'
      (Eventually.of_forall fun n => GaussianCode.avgErrProb_nonneg _ _) ?_⟩
    filter_upwards [hev] with n hn
    exact hc n hn

/-- **Theorem 3 of Lecture 3 (Shannon).** The capacity of the AWGN channel `Y = gX + Z` with
`g ≠ 0`, `Z ∼ N(0, 1)` and power constraint `P` is `C(S) = ½ log (1 + S)` with `S = g²P`, in
bits per transmission. -/
theorem opCapacityAWGN_eq {g : ℝ} (hg : g ≠ 0) (P : ℝ≥0) :
    opCapacityAWGN g P = gaussianCapacityFun (g ^ 2 * P) / log 2 := by
  have hl := log_pos one_lt_two
  have hC : 0 ≤ gaussianCapacityFun (g ^ 2 * P) / log 2 :=
    div_nonneg (mul_nonneg (by norm_num) (log_nonneg (by nlinarith [sq_nonneg g, P.2])))
      hl.le
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨-1, isAchievableAWGNRate_of_lt hg (by linarith)⟩ (fun R hR => hR.le) fun w hw => ?_
  exact ⟨(w + gaussianCapacityFun (g ^ 2 * P) / log 2) / 2,
    isAchievableAWGNRate_of_lt hg (by linarith), by linarith⟩

end InfoTheory
