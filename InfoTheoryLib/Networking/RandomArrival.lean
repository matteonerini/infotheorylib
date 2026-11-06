/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.Networking.Queue
public import InfoTheoryLib.Secrecy.KeyedChannel

/-!
# Random data arrival at a discrete memoryless channel

Theorem 1 of Lecture 24 of El Gamal and Kim. An augmented `(2^{nR}, n)` code has the messages
`[1 : 2^{nR}]`, for the blocks in which `nR` bits are taken from the queue, and the message `0`,
for the other blocks. Here a block carries `⌈nR⌉` bits, the augmented message set is
`Fin (2^⌈nR⌉ + 1)`, and `0` is its first element.

The converse in the notes applies Fano's inequality conditionally on `M_j ≠ 0`, but the error
probability `P_ej` only controls the nonzero messages if `P{M_j ≠ 0}` is bounded away from `0`.
That is true, for a suitable `j`, because a stable queue has to serve the arrivals
(`exists_one_sub_queueLowProb_ge`).

The converse also claims `λ < R`, which is false for `p = 1`: Lemma 1 gives only `λ ≤ R`, and
`λ = R` can be reliable (`printed_theorem1_strict_false`).

## Main definitions

* `arrivalErr W p k c s j`: the probability of error `P_ej` in block `j`.
* `IsReliableArrival W p k R`: the arrivals can be reliably communicated at rate `R`.

## Main statements

* `isReliableArrival_of_lt`, `exists_isReliableArrival`, `IsReliableArrival.le_capacity`:
  **Theorem 1 of Lecture 24**.
* `printed_theorem1_strict_false`: the strict inequality in the printed converse fails.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24.
-/

@[expose] public noncomputable section

open Finset Filter Topology Real

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **`P_ej` of Lecture 24.** The probability of error in block `j` of an augmented code: with
probability `p_j` the message is `0`, and otherwise it is uniform on the `M` other messages. -/
def arrivalErr (W : α → β → ℝ) (p : ℝ) (k : ℕ) {M n : ℕ} (c : ChannelCode (M + 1) n α β) (s : ℝ)
    (j : ℕ) : ℝ :=
  queueLowProb p k n s j * c.condErrProb W 0 +
    (1 - queueLowProb p k n s j) / M * ∑ m : Fin M, c.condErrProb W m.succ

/-- **Definition (Lecture 24).** The arrivals can be reliably communicated at rate `R` (in bits): a
sequence of augmented `(2^{nR}, n)` codes has a stable queue and `sup_j P_ej → 0`. -/
def IsReliableArrival (W : α → β → ℝ) (p : ℝ) (k : ℕ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, ChannelCode (2 ^ ⌈n * R⌉₊ + 1) n α β,
    (∀ᶠ n : ℕ in atTop, QueueStable p k n ⌈n * R⌉₊) ∧
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j, arrivalErr W p k (c n) ⌈n * R⌉₊ j ≤ ε

variable {W : α → β → ℝ} {p : ℝ} {k : ℕ} {R : ℝ}

lemma queueLowProb_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) (s : ℝ) (j : ℕ) :
    0 ≤ queueLowProb p k n s j := by
  refine sum_nonneg fun a _ => mul_nonneg ((iidPMF_bernoulli_isPMF h0 h1 _).nonneg a) ?_
  dsimp only
  split_ifs <;> norm_num

lemma queueLowProb_le_one (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) (s : ℝ) (j : ℕ) :
    queueLowProb p k n s j ≤ 1 := by
  have hq := iidPMF_bernoulli_isPMF h0 h1 (j * n)
  calc queueLowProb p k n s j ≤ ∑ a, iidPMF (bernoulliPMF p) (j * n) a * 1 := by
        refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hq.nonneg a)
        dsimp only
        split_ifs <;> norm_num
    _ = 1 := by simp [hq.sum_eq_one]

omit [Fintype α] in
/-- `P_ej` is at most the maximal probability of error. -/
lemma arrivalErr_le_maxErrProb (h0 : 0 ≤ p) (h1 : p ≤ 1) {M n : ℕ} (hM : 0 < M)
    (c : ChannelCode (M + 1) n α β) (s : ℝ) (j : ℕ) :
    arrivalErr W p k c s j ≤ c.maxErrProb W := by
  have hl := queueLowProb_nonneg (k := k) h0 h1 n s j
  have hu := queueLowProb_le_one (k := k) h0 h1 n s j
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : ∑ m : Fin M, c.condErrProb W m.succ ≤ M * c.maxErrProb W := by
    calc ∑ m : Fin M, c.condErrProb W m.succ ≤ ∑ _m : Fin M, c.maxErrProb W :=
          sum_le_sum fun m _ => c.condErrProb_le_maxErrProb _
      _ = M * c.maxErrProb W := by simp
  have h3 : (1 - queueLowProb p k n s j) / M * ∑ m : Fin M, c.condErrProb W m.succ ≤
      (1 - queueLowProb p k n s j) * c.maxErrProb W := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hM']
    calc (1 - queueLowProb p k n s j) * ∑ m : Fin M, c.condErrProb W m.succ
        ≤ (1 - queueLowProb p k n s j) * (M * c.maxErrProb W) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = _ := by ring
  have h4 : queueLowProb p k n s j * c.condErrProb W 0 ≤
      queueLowProb p k n s j * c.maxErrProb W :=
    mul_le_mul_of_nonneg_left (c.condErrProb_le_maxErrProb _) hl
  unfold arrivalErr
  linarith

/-- `2^⌈nR⌉ + 1 ≤ ⌈e^{nR'}⌉` for large `n`, if `R log 2 < R'`. -/
lemma eventually_two_pow_succ_le {R R' : ℝ} (hR : 0 < R) (hR' : R * log 2 < R') :
    ∀ᶠ n : ℕ in atTop, 2 ^ ⌈n * R⌉₊ + 1 ≤ ⌈exp (n * R')⌉₊ := by
  have hl := log_pos one_lt_two
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (3 * log 2 / (R' - R * log 2))
  have hpos : 0 < R' - R * log 2 := by linarith
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hn' : 3 * log 2 < n * (R' - R * log 2) := by
    have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have h2 := (div_lt_iff₀ hpos).1 hn₀
    nlinarith
  have hc : (⌈n * R⌉₊ : ℝ) < n * R + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1 : ((2 ^ ⌈n * R⌉₊ + 1 : ℕ) : ℝ) ≤ exp (n * R') := by
    have h2 : ((2 : ℝ) ^ ⌈n * R⌉₊) = exp (⌈n * R⌉₊ * log 2) := by
      rw [← rpow_natCast, rpow_def_of_pos two_pos, mul_comm]
    have h3 : (1 : ℝ) ≤ 2 ^ ⌈n * R⌉₊ := one_le_pow₀ one_le_two
    have h4 : exp (log 2 + ⌈n * R⌉₊ * log 2) ≤ exp (n * R') := by
      refine exp_le_exp.2 ?_
      nlinarith
    rw [exp_add, exp_log two_pos, ← h2] at h4
    push_cast
    linarith
  exact_mod_cast h1.trans (Nat.le_ceil _)

/-- **Theorem 1 of Lecture 24, achievability.** If `λ < R` and `R < C`, the arrivals can be
reliably communicated at rate `R`. The capacity `C` is in nats. -/
theorem isReliableArrival_of_lt [Nonempty α] [Nonempty β] (hW : IsChannel W) (h0 : 0 ≤ p)
    (h1 : p ≤ 1) (hlr : p * k < R) (hRC : R * log 2 < capacity W) :
    IsReliableArrival W p k R := by
  have hl0 : 0 ≤ p * (k : ℝ) := by positivity
  have hR : 0 < R := by linarith
  obtain ⟨R', hR1, hR2⟩ := exists_between hRC
  obtain ⟨c₀, hc₀⟩ := isAchievableRate_of_lt_capacity hW hR2
  have hmsg := eventually_two_pow_succ_le hR hR1
  have hex : ∀ n : ℕ, ∃ c : ChannelCode (2 ^ ⌈n * R⌉₊ + 1) n α β,
      2 ^ ⌈n * R⌉₊ + 1 ≤ ⌈exp (n * R')⌉₊ → c.maxErrProb W ≤ (c₀ n).maxErrProb W := by
    intro n
    by_cases hn : 2 ^ ⌈n * R⌉₊ + 1 ≤ ⌈exp (n * R')⌉₊
    · obtain ⟨c, hc⟩ := (c₀ n).exists_maxErrProb_le hW (Nat.succ_pos _) hn
      exact ⟨c, fun _ => hc⟩
    · exact ⟨⟨fun _ _ => Classical.arbitrary α, fun _ => 0⟩, fun h => absurd h hn⟩
  choose c hc using hex
  refine ⟨c, ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    refine queueStable_of_lt h0 h1 hn ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (n : ℝ) * (p * k) < n * R := mul_lt_mul_of_pos_left hlr hn'
      _ ≤ _ := Nat.le_ceil _
  · have hlim := hc₀.eventually (gt_mem_nhds hε)
    filter_upwards [hlim, hmsg] with n hn1 hn2 j
    calc arrivalErr W p k (c n) ⌈n * R⌉₊ j ≤ (c n).maxErrProb W :=
          arrivalErr_le_maxErrProb h0 h1 (by positivity) _ _ _
      _ ≤ (c₀ n).maxErrProb W := hc n hn2
      _ ≤ ε := hn1.le

/-- **Theorem 1 of Lecture 24, achievability.** If `λ < C`, the arrivals can be reliably
communicated at some rate. The capacity `C` is in nats. -/
theorem exists_isReliableArrival [Nonempty α] [Nonempty β] (hW : IsChannel W) (h0 : 0 ≤ p)
    (h1 : p ≤ 1) (hlC : p * k * log 2 < capacity W) : ∃ R, IsReliableArrival W p k R := by
  have hl := log_pos one_lt_two
  obtain ⟨R, hR1, hR2⟩ := exists_between ((lt_div_iff₀ hl).2 hlC)
  exact ⟨R, isReliableArrival_of_lt hW h0 h1 hR1 ((lt_div_iff₀ hl).1 hR2)⟩

/-- The nonzero messages of an augmented code, as an ordinary code. A received `0` is sent to the
first message, which only counts against that message when it is decoded wrongly. -/
def augRestrict {M n : ℕ} [NeZero M] (c : ChannelCode (M + 1) n α β) : ChannelCode M n α β where
  enc m := c.enc m.succ
  dec y := (c.dec y).cases 0 id

omit [Fintype α] in
lemma augRestrict_condErrProb_le {M n : ℕ} [NeZero M] (hW : IsChannel W)
    (c : ChannelCode (M + 1) n α β) (m : Fin M) :
    (augRestrict c).condErrProb W m ≤ c.condErrProb W m.succ := by
  classical
  unfold ChannelCode.condErrProb
  refine sum_le_sum fun y _ => ?_
  by_cases h : c.dec y = m.succ
  · have : (augRestrict c).dec y = m := by
      simp [augRestrict, h]
    simp [this, h]
  · simp only [ne_eq, h, not_false_eq_true, ite_true]
    have he : (augRestrict c).enc m = c.enc m.succ := rfl
    rw [he]
    split_ifs <;> first | exact le_rfl | exact channelExt_nonneg hW _ _

/-- **Theorem 1 of Lecture 24, converse.** If the arrivals can be reliably communicated at rate `R`,
then `λ ≤ R ≤ C`, with the capacity `C` in nats. A packet has to have some bits and to arrive with
positive probability. -/
theorem IsReliableArrival.le_capacity [Nonempty α] (hW : IsChannel W) (h0 : 0 < p) (h1 : p ≤ 1)
    (hk : 0 < k) (h : IsReliableArrival W p k R) : p * k ≤ R ∧ R * log 2 ≤ capacity W := by
  obtain ⟨c, hst, herr⟩ := h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set lam : ℝ := p * k with hlam
  have hlam0 : 0 < lam := by positivity
  have hl := log_pos one_lt_two
  have hstable : ∀ᶠ n : ℕ in atTop, (n : ℝ) * lam ≤ ⌈n * R⌉₊ := by
    filter_upwards [hst, eventually_gt_atTop 0] with n hn hn0
    exact le_of_queueStable h0.le h1 hn0 (by positivity) hn
  -- The rate exceeds the arrival rate.
  have hle : lam ≤ R := by
    by_contra hcon
    push Not at hcon
    have hgap : 0 < lam - R := by linarith
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / (lam - R))
    obtain ⟨n, hn1, hn2, hn3⟩ := (hstable.and ((eventually_ge_atTop n₀).and
      (eventually_gt_atTop 0))).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn3
    have h2 : (1 : ℝ) < n₀ * (lam - R) := (div_lt_iff₀ hgap).1 hn₀
    have h3 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn2
    have h4 : (1 : ℝ) < n * (lam - R) := by nlinarith
    rcases le_or_gt (n * R) 0 with hneg | hpos
    · rw [Nat.ceil_eq_zero.2 hneg] at hn1
      simp only [Nat.cast_zero] at hn1
      nlinarith
    · have h5 : (⌈n * R⌉₊ : ℝ) < n * R + 1 := Nat.ceil_lt_add_one hpos.le
      nlinarith
  have hR : 0 < R := by linarith
  refine ⟨hle, ?_⟩
  have ha : 0 ≤ R * log 2 := by positivity
  set κ := lam / (2 * (R + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  refine le_of_forall_eventually_mul_le ha fun ε hε => ⟨log 2, ?_⟩
  filter_upwards [hst, herr (ε * κ) (by positivity), eventually_gt_atTop 0] with n hst' herr' hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : 0 < n * R := by positivity
  have hs0 : (0 : ℝ) < ⌈n * R⌉₊ := lt_of_lt_of_le hnR (Nat.le_ceil _)
  have hsu : (⌈n * R⌉₊ : ℝ) ≤ n * (R + 1) := by
    have h5 : (⌈n * R⌉₊ : ℝ) < n * R + 1 := Nat.ceil_lt_add_one hnR.le
    have h6 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith
  obtain ⟨j, hj⟩ := exists_one_sub_queueLowProb_ge h0.le h1 hn0 hs0
    (by rw [← hlam]; positivity) hst'
  rw [← hlam] at hj
  -- The served fraction is at least `κ`.
  have hκj : κ ≤ 1 - queueLowProb p k n ⌈n * R⌉₊ j := by
    refine le_trans ?_ hj
    rw [hκ, div_le_div_iff₀ (by positivity) (by positivity)]
    have : lam * (2 * ⌈n * R⌉₊) ≤ lam * (2 * (n * (R + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) hlam0.le
    nlinarith
  set M := 2 ^ ⌈n * R⌉₊ with hM
  have hMpos : 0 < M := by positivity
  have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
  have : NeZero M := ⟨hMpos.ne'⟩
  have hsumnn : 0 ≤ ∑ m : Fin M, (c n).condErrProb W m.succ :=
    sum_nonneg fun m _ => (c n).condErrProb_nonneg hW _
  -- So the nonzero messages have small average error.
  have havg : (∑ m : Fin M, (c n).condErrProb W m.succ) / M ≤ ε := by
    have h7 := herr' j
    unfold arrivalErr at h7
    have h8 : 0 ≤ queueLowProb p k n ⌈n * R⌉₊ j * (c n).condErrProb W 0 :=
      mul_nonneg (queueLowProb_nonneg h0.le h1 _ _ _) ((c n).condErrProb_nonneg hW _)
    have h9 : κ * ((∑ m : Fin M, (c n).condErrProb W m.succ) / M) ≤ ε * κ := by
      have h10 : κ * ((∑ m : Fin M, (c n).condErrProb W m.succ) / M) ≤
          (1 - queueLowProb p k n ⌈n * R⌉₊ j) * ((∑ m : Fin M, (c n).condErrProb W m.succ) / M) :=
        mul_le_mul_of_nonneg_right hκj (by positivity)
      have h11 : (1 - queueLowProb p k n ⌈n * R⌉₊ j) *
          ((∑ m : Fin M, (c n).condErrProb W m.succ) / M) =
          (1 - queueLowProb p k n ⌈n * R⌉₊ j) / M * ∑ m : Fin M, (c n).condErrProb W m.succ := by
        ring
      linarith
    nlinarith
  have hcode := ChannelCode.one_sub_avgErrProb_mul_log_le hW hMpos (augRestrict (c n))
  have hav2 : (augRestrict (c n)).avgErrProb W ≤ ε := by
    refine le_trans ?_ havg
    unfold ChannelCode.avgErrProb
    exact div_le_div_of_nonneg_right
      (sum_le_sum fun m _ => augRestrict_condErrProb_le hW _ m) hM'.le
  have hav0 : (augRestrict (c n)).avgErrProb W ≤ 1 :=
    (ChannelCode.avgErrProb_le_maxErrProb _).trans
      (ChannelCode.maxErrProb_le _ hMpos fun i => (augRestrict (c n)).condErrProb_le_one hW i)
  have hlogM : n * (R * log 2) ≤ log M := by
    rw [hM]
    push_cast
    rw [Real.log_pow]
    have : n * R ≤ ⌈n * R⌉₊ := Nat.le_ceil _
    nlinarith
  have hna : 0 ≤ n * (R * log 2) := by positivity
  have h12 : (1 - ε) * (n * (R * log 2)) ≤
      (1 - (augRestrict (c n)).avgErrProb W) * log M := by
    calc (1 - ε) * (n * (R * log 2)) ≤
          (1 - (augRestrict (c n)).avgErrProb W) * (n * (R * log 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hna
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogM (by linarith)
  have hC := capacity_nonneg (α := α) hW
  nlinarith

/-! ### The strict inequality in the printed converse -/

/-- The noiseless channel on three letters. -/
def ternaryNoiseless : Fin 3 → Fin 3 → ℝ := fun x y => if x = y then 1 else 0

lemma ternaryNoiseless_isChannel : IsChannel ternaryNoiseless := fun x =>
  ⟨fun y => by unfold ternaryNoiseless; split_ifs <;> norm_num, by simp [ternaryNoiseless]⟩

/-- The extension of the noiseless channel only reaches the input. -/
lemma channelExt_ternaryNoiseless_of_ne {n : ℕ} {x y : Fin n → Fin 3} (h : y ≠ x) :
    channelExt ternaryNoiseless n x y = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  refine prod_eq_zero (mem_univ i) ?_
  simp [ternaryNoiseless, hi.symm]

/-- Injective codewords for the noiseless channel give no error. -/
lemma exists_ternary_code {M n : ℕ} (hM : 0 < M) (hMn : M ≤ 3 ^ n) :
    ∃ c : ChannelCode M n (Fin 3) (Fin 3), ∀ i, c.condErrProb ternaryNoiseless i = 0 := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hcard : Fintype.card (Fin M) ≤ Fintype.card (Fin n → Fin 3) := by simpa using hMn
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨⟨e, Function.invFun e⟩, fun i => ?_⟩
  unfold ChannelCode.condErrProb
  refine sum_eq_zero fun y _ => ?_
  by_cases hy : y = e i
  · subst hy
    simp [Function.leftInverse_invFun e.injective i]
  · simp [channelExt_ternaryNoiseless_of_ne hy]

/-- With deterministic arrivals of exactly `n` bits per block, the queue holds `0` or `n` bits at
the beginning of each block. -/
lemma queueOf_det_cases {n : ℕ} (hn : 0 < n) (A : ℕ → ℝ) (hA : ∀ t, A t = 1) (j : ℕ) :
    queueOf n n A (j * n) = 0 ∨ queueOf n n A (j * n) = n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : ∀ m : ℕ, n ∣ m → (∑ i ∈ range n, A (m + i)) = n := fun m _ => by simp [hA]
  induction j with
  | zero => simp [queueOf]
  | succ j ih =>
    right
    rw [Nat.succ_mul, queueOf_block _ (Dvd.intro_left j rfl) hn le_rfl, hb _ (Dvd.intro_left j rfl)]
    rcases ih with h | h
    · rw [h]
      have : ¬ (n : ℝ) ≤ 0 := by linarith
      simp [queueServe, this]
    · rw [h]
      simp [queueServe]

/-- For `p = 1` and `λ = R`, the queue is stable: Lemma 1 cannot be improved at `p = 1`. -/
lemma queueStable_one_one {n : ℕ} (hn : 0 < n) : QueueStable 1 1 n n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨2 * n, fun N => ?_⟩
  have hN : N = (N / n) * n + N % n := (Nat.div_add_mod' N n).symm
  have h2 := queueMean_add_le (k := 1) (n := n) (p := 1) (s := n) zero_le_one le_rfl hn'.le
    ((N / n) * n) (N % n)
  rw [← hN] at h2
  have hmod : ((N % n : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.mod_lt N hn).le
  have h3 : queueMean 1 1 n n ((N / n) * n) ≤ n := by
    rw [queueMean_one]
    set A : ℕ → ℝ := fun t => if t < (N / n) * n then (1 : ℕ) else 0
    have hcong : queueOf n n A ((N / n) * n) = queueOf n n (fun _ => 1) ((N / n) * n) :=
      queueOf_congr fun t ht => by simp [A, ht]
    rw [hcong]
    rcases queueOf_det_cases hn (fun _ => 1) (fun _ => rfl) (N / n) with h | h <;> rw [h]
    exact hn'.le
  push_cast at h2
  linarith

lemma two_pow_succ_le_three_pow {n : ℕ} (hn : 0 < n) : 2 ^ n + 1 ≤ 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m _ ih =>
    have h4 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have h5 : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
    omega

/-- **The strict inequality `λ < R` in the printed converse of Theorem 1 fails.** For `p = 1` and
packets of one bit, the deterministic arrivals of rate `λ = 1` are reliably communicated at rate
`R = 1` over the noiseless ternary channel. The notes allow `p ∈ (0, 1]`. The converse holds with
`λ ≤ R`, as in `IsReliableArrival.le_capacity`. -/
theorem printed_theorem1_strict_false :
    IsReliableArrival ternaryNoiseless 1 1 1 ∧ ¬ ((1 : ℝ) * (1 : ℕ) < 1) := by
  refine ⟨?_, by norm_num⟩
  have hex : ∀ n : ℕ, ∃ c : ChannelCode (2 ^ ⌈(n : ℝ) * 1⌉₊ + 1) n (Fin 3) (Fin 3),
      0 < n → ∀ i, c.condErrProb ternaryNoiseless i = 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact ⟨⟨fun _ _ => 0, fun _ => 0⟩, fun h => absurd h (by omega)⟩
    · have hle : 2 ^ ⌈(n : ℝ) * 1⌉₊ + 1 ≤ 3 ^ n := by
        rw [mul_one, Nat.ceil_natCast]
        exact two_pow_succ_le_three_pow hn
      obtain ⟨c, hc⟩ := exists_ternary_code (Nat.succ_pos _) hle
      exact ⟨c, fun _ => hc⟩
  choose c hc using hex
  refine ⟨c, ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [mul_one, Nat.ceil_natCast]
    exact queueStable_one_one hn
  · filter_upwards [eventually_gt_atTop 0] with n hn j
    unfold arrivalErr
    simp [hc n hn, hε.le]

end InfoTheory
