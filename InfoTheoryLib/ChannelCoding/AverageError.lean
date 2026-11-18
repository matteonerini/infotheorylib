/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse

/-!
# Channel capacity with the average probability of error

In their lecture notes, El Gamal and Kim define achievable rates in bits per transmission, with
`(2^{nR}, n)` codes whose message set is `[1 : 2^{nR}] = {1, …, 2^⌈nR⌉}`, and with the average
probability of error `P_e^(n) = P{M̂ ≠ M}` for a uniformly distributed message. Cover and Thomas use
rates in nats, `⌈e^{nR}⌉` messages and the maximal probability of error. Both definitions give the
same capacity: we derive the channel coding theorem for the average-error definition from the one of
`ChannelCoding.Achievability` and `ChannelCoding.Converse`. Achievability transfers because a code
can be restricted to fewer messages without increasing its maximal probability of error, which
bounds the average one; the converse of Cover and Thomas is already proved from the average
probability of error.

## Main definitions

* `IsAchievableRateAvg W R`: `R` (in bits) is achievable with the average probability of error.
* `opCapacityAvg W`: the supremum of these rates, the capacity in bits.

## Main statements

* `isAchievableRateAvg_of_lt`: every rate below `C / log 2` bits is achievable.
* `IsAchievableRateAvg.le_capacity_div`: the converse.
* `opCapacityAvg_eq`: **the channel coding theorem of [elgamal2010], Lecture 3**, the capacity is
  `max_{p(x)} I(X; Y)`, that is `capacity W / log 2` bits.

## Implementation notes

The decoder of a `ChannelCode` always outputs a message. The notes' decoder may also declare an
error `e`; mapping `e` to any message does not increase the probability of error, so the two
definitions have the same achievable rates.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β] {W : α → β → ℝ}

/-- **Definition (Lecture 3 of [elgamal2010]).** A rate `R`, in bits per transmission, is
achievable if there is a sequence of `(2^{nR}, n)` codes, with message set
`[1 : 2^{nR}] = {1, …, 2^⌈nR⌉}`, whose average probability of error tends to `0`. -/
def IsAchievableRateAvg (W : α → β → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, ChannelCode (2 ^ ⌈n * R⌉₊) n α β,
    Tendsto (fun n => (c n).avgErrProb W) atTop (𝓝 0)

/-- **Definition (Lecture 3 of [elgamal2010]).** The capacity, in bits per transmission, is the
supremum of the achievable rates. -/
def opCapacityAvg (W : α → β → ℝ) : ℝ := sSup {R | IsAchievableRateAvg W R}

/-- `⌈2^{nR}⌉ ≤ 2^⌈nR⌉`. -/
lemma ceil_exp_le_two_pow (n : ℕ) (R : ℝ) : ⌈exp (n * (R * log 2))⌉₊ ≤ 2 ^ ⌈n * R⌉₊ := by
  apply Nat.ceil_le.2
  push_cast
  calc exp (n * (R * log 2)) = 2 ^ (n * R) := by
        rw [rpow_def_of_pos two_pos]
        congr 1
        ring
    _ ≤ 2 ^ (⌈n * R⌉₊ : ℝ) := rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
    _ = 2 ^ ⌈n * R⌉₊ := rpow_natCast 2 _

/-- **Channel coding theorem (Lecture 3), weak converse.** A rate that is achievable with the
average probability of error is at most `C / log 2` bits. -/
theorem IsAchievableRateAvg.le_capacity_div [Nonempty α] (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRateAvg W R) : R ≤ capacity W / log 2 := by
  obtain ⟨c, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  have h1 : ∀ n, (c n).avgErrProb W ≤ 1 := fun n =>
    (c n).avgErrProb_le_maxErrProb.trans
      (ChannelCode.maxErrProb_le _ (hpos n) fun i => (c n).condErrProb_le_one hW i)
  have key := le_of_converse_bound (R := R * log 2) (C := capacity W) hc h1 fun n _ => by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by linarith [h1 n]))
      ((c n).one_sub_avgErrProb_mul_log_le hW (hpos n))
    exact log_le_log (Nat.cast_pos.2 (Nat.ceil_pos.2 (exp_pos _)))
      (by exact_mod_cast ceil_exp_le_two_pow n R)
  rwa [le_div_iff₀ (log_pos one_lt_two)]

/-- **Channel coding theorem (Lecture 3), achievability.** Every rate below `C / log 2` bits is
achievable with the average probability of error. -/
theorem isAchievableRateAvg_of_lt [Nonempty α] (hW : IsChannel W) {R : ℝ}
    (hR : R < capacity W / log 2) : IsAchievableRateAvg W R := by
  have hl := log_pos one_lt_two
  rcases le_or_gt R 0 with hR0 | hR0
  · -- With `R ≤ 0` there is a single message.
    have h1 : ∀ n : ℕ, 2 ^ ⌈n * R⌉₊ = 1 := fun n => by
      rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0), pow_zero]
    choose c hc using fun n : ℕ => exists_code_maxErrProb_eq_zero W (h1 n) n
    refine ⟨c, ?_⟩
    have : ∀ n, (c n).avgErrProb W = 0 := fun n =>
      le_antisymm ((c n).avgErrProb_le_maxErrProb.trans (hc n).le) ((c n).avgErrProb_nonneg hW)
    simp [this]
  · -- Restrict Cover and Thomas's codes of a rate `R'` with `R log 2 < R' < C` (in nats).
    have hRC : R * log 2 < capacity W := (lt_div_iff₀ hl).1 hR
    obtain ⟨R', hR'1, hR'2⟩ : ∃ R', R * log 2 < R' ∧ R' < capacity W :=
      ⟨(R * log 2 + capacity W) / 2, by linarith, by linarith⟩
    obtain ⟨c', hc'⟩ := isAchievableRate_of_lt_capacity hW hR'2
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
    have hsub : ∀ n : ℕ, ∃ c : ChannelCode (2 ^ ⌈n * R⌉₊) n α β,
        2 ^ ⌈n * R⌉₊ ≤ ⌈exp (n * R')⌉₊ → c.maxErrProb W ≤ (c' n).maxErrProb W := fun n => by
      by_cases h : 2 ^ ⌈n * R⌉₊ ≤ ⌈exp (n * R')⌉₊
      · obtain ⟨c, hc⟩ := ChannelCode.exists_maxErrProb_le (c := c' n) hW (by positivity) h
        exact ⟨c, fun _ => hc⟩
      · exact ⟨⟨fun _ _ => Classical.arbitrary α, fun _ => ⟨0, by positivity⟩⟩,
          fun h' => absurd h' h⟩
    choose c hc using hsub
    refine ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc'
      (Eventually.of_forall fun n => (c n).avgErrProb_nonneg hW) ?_⟩
    filter_upwards [hev] with n hn
    exact (c n).avgErrProb_le_maxErrProb.trans (hc n hn)

/-- **Shannon's channel coding theorem (Lecture 3 of [elgamal2010]).** The capacity of a discrete
memoryless channel, defined with the average probability of error and in bits, is given by the
information capacity formula `C = max_{p(x)} I(X; Y)`. -/
theorem opCapacityAvg_eq [Nonempty α] (hW : IsChannel W) :
    opCapacityAvg W = capacity W / log 2 := by
  have hl := log_pos one_lt_two
  have hC := div_nonneg (capacity_nonneg hW) hl.le
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨-1, isAchievableRateAvg_of_lt hW (by linarith)⟩ (fun R hR => hR.le_capacity_div hW) ?_
  intro w hw
  exact ⟨(w + capacity W / log 2) / 2, isAchievableRateAvg_of_lt hW (by linarith), by linarith⟩

end InfoTheory
