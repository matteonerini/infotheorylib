/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.ChannelCoding.SourceChannel

/-!
# Asymptotically achievable rates

A rate `R` is asymptotically achievable if, for every `ε > 0` and `n` sufficiently large, some code
of block length `n` has rate `(1/n) log M > R - ε` and maximal probability of error `λ_max < ε`.
The rates may approach `R` from below, unlike `IsAchievableRate`, which asks for `⌈e^{nR}⌉`
messages. The channel coding theorem says that the achievable rates are exactly the rates
`R ≤ C`, with or without feedback.

## Main definitions

* `codeRate M n`: the rate `(1/n) log M` of a code with `M` messages and block length `n`.
* `IsAsymptoticallyAchievable W R`, `IsAsymptoticallyAchievableFB W R`: achievable rates without
  and with feedback.
* `FeedbackCode.condErrProb`, `FeedbackCode.maxErrProb`: the conditional and maximal probabilities
  of error of a feedback code.
* `fbCapacityMax W`: the supremum of the rates achievable with feedback.

## Main statements

* `isAsymptoticallyAchievable_iff`: the channel coding theorem, `R` is achievable iff `R ≤ C`.
* `isAsymptoticallyAchievableFB_iff`, `fbCapacityMax_eq_capacity`: feedback does not increase the
  capacity.
* `isAsymptoticallyAchievableFB_fbCapacityMax`: the supremum of the rates achievable with feedback
  is achieved.
* `entropyRate_le_capacity_of_fbLaw`: the converse of the separation theorem, for joint
  source-channel codes with feedback.

## Implementation notes

Rates are in nats per use: `codeRate M n = log M / n` with natural logarithms.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 7.2, 7.6 and 7.7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Definition 7.13.** The rate `(1/n) log M` of a code with `M` messages and block length `n`, in
nats per use. -/
def codeRate (M n : ℕ) : ℝ := log M / n

/-- **Definition 7.14.** A rate `R` is asymptotically achievable if, for every `ε > 0` and `n`
sufficiently large, there is a code with `(1/n) log M > R - ε` and `λ_max < ε`. -/
def IsAsymptoticallyAchievable (W : α → β → ℝ) (R : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 0 < M ∧ ∃ c : ChannelCode M n α β,
    R - ε < codeRate M n ∧ c.maxErrProb W < ε

/-- The common end of the converse proofs, (7.128)–(7.133): if for every `ε > 0` and `n` large there
are `M > 0` and `Pₑ < ε` with `(1/n) log M > R - ε` and `(1 - Pₑ) log M ≤ log 2 + nC`, then
`R ≤ C`. -/
theorem le_of_eventually_code_bound {R C : ℝ}
    (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 0 < M ∧ ∃ P : ℝ, P < ε ∧
      R - ε < codeRate M n ∧ (1 - P) * log M ≤ log 2 + n * C) : R ≤ C := by
  by_contra hRC
  rw [not_le] at hRC
  set d := (R - C) / 2 with hd_def
  have hd : 0 < d := by linarith
  set ε := min (1 / 2) (d / (1 + |R|)) with hε_def
  have hR₀ : 0 < 1 + |R| := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hd hR₀)
  have hε₁ : ε ≤ 1 / 2 := min_le_left _ _
  have hε₂ : ε * (1 + |R|) ≤ d := (le_div_iff₀ hR₀).1 (min_le_right _ _)
  have hkey : C + d ≤ (1 - ε) * (R - ε) := by
    have h₁ : ε * R ≤ ε * |R| := mul_le_mul_of_nonneg_left (le_abs_self R) hε.le
    have h₂ : (1 - ε) * (R - ε) = R - ε * (1 + |R|) + (ε * |R| - ε * R) + ε ^ 2 := by ring
    nlinarith [sq_nonneg ε]
  obtain ⟨n, ⟨M, hM, P, hP, hrate, hbound⟩, hn⟩ :=
    ((h ε hε).and (eventually_gt_atTop ⌈log 2 / d⌉₊)).exists
  have hn' : (0 : ℝ) < n := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
    exact_mod_cast this
  have hnd : log 2 < n * d := by
    have h₁ : log 2 / d < n := (Nat.lt_of_ceil_lt hn)
    rw [div_lt_iff₀ hd] at h₁
    linarith [mul_comm d (n : ℝ)]
  have hlogM : n * (R - ε) < log M := by
    rw [codeRate, lt_div_iff₀ hn'] at hrate
    linarith
  have hlogM₀ : 0 ≤ log (M : ℝ) := log_natCast_nonneg M
  have h₁ : (1 - ε) * log M ≤ (1 - P) * log M :=
    mul_le_mul_of_nonneg_right (by linarith) hlogM₀
  have h₂ : (1 - ε) * (n * (R - ε)) ≤ (1 - ε) * log M :=
    mul_le_mul_of_nonneg_left hlogM.le (by linarith)
  have h₃ : n * (C + d) ≤ n * ((1 - ε) * (R - ε)) := mul_le_mul_of_nonneg_left hkey hn'.le
  nlinarith

/-- `(1/n) log ⌈e^{nR}⌉ ≥ R`. -/
lemma le_codeRate_ceil_exp {n : ℕ} (hn : 0 < n) (R : ℝ) : R ≤ codeRate ⌈exp (n * R)⌉₊ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [codeRate, le_div_iff₀ hn', mul_comm]
  calc (n : ℝ) * R = log (exp (n * R)) := (log_exp _).symm
    _ ≤ log ⌈exp (n * R)⌉₊ := log_le_log (exp_pos _) (Nat.le_ceil _)

/-- **Theorem 7.15 (Channel Coding Theorem).** A rate `R` is achievable for a discrete memoryless
channel iff `R ≤ C`. -/
theorem isAsymptoticallyAchievable_iff [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) {R : ℝ} :
    IsAsymptoticallyAchievable W R ↔ R ≤ capacity W := by
  constructor
  · intro h
    refine le_of_eventually_code_bound fun ε hε => ?_
    filter_upwards [h ε hε] with n ⟨M, hM, c, hr, hlam⟩
    exact ⟨M, hM, c.avgErrProb W, c.avgErrProb_le_maxErrProb.trans_lt hlam, hr,
      c.one_sub_avgErrProb_mul_log_le hW hM⟩
  · intro hR ε hε
    obtain ⟨c, hc⟩ := isAchievableRate_of_lt_capacity hW (R := R - ε / 2) (by linarith)
    filter_upwards [hc.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with n h₁ hn
    exact ⟨_, one_le_ceil_exp _, c n, by linarith [le_codeRate_ceil_exp hn (R - ε / 2)], h₁⟩

/-! ### Feedback -/

namespace FeedbackCode

variable {M n : ℕ} (W : α → β → ℝ) (c : FeedbackCode M n α β)

open Classical in
/-- **(7.85) with feedback.** The conditional probability of error
`λ_w = Pr{Ŵ ≠ w | W = w}` of a feedback code, for a uniformly distributed message. -/
def condErrProb (w : Fin M) : ℝ :=
  ∑ y, if c.dec y ≠ w then M * fbLaw (uniformPMF (Fin M)) W c.enc n (w, y) else 0

/-- **(7.86) with feedback.** The maximal probability of error `λ_max = max_w λ_w`. -/
def maxErrProb : ℝ := ⨆ w, c.condErrProb W w

omit [Fintype α] in
/-- **(7.92) with feedback.** `Pₑ ≤ λ_max`. -/
theorem errProb_le_maxErrProb (hM : 0 < M) : c.errProb W ≤ c.maxErrProb W := by
  classical
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h₂ : ∀ w, c.condErrProb W w ≤ c.maxErrProb W := fun w =>
    le_ciSup (Set.finite_range _).bddAbove w
  rw [errProb, InfoTheory.errProb, Fintype.sum_prod_type]
  refine le_trans (le_of_eq (sum_congr (g := fun w => c.condErrProb W w / M) rfl
    fun w _ => ?_)) ?_
  · rw [condErrProb, eq_div_iff hM'.ne', sum_mul]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  calc ∑ w, c.condErrProb W w / M ≤ ∑ _w : Fin M, c.maxErrProb W / M :=
        sum_le_sum fun w _ => div_le_div_of_nonneg_right (h₂ w) hM'.le
    _ = c.maxErrProb W := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end FeedbackCode

/-- **Definition 7.19.** A rate `R` is achievable with complete feedback if, for every `ε > 0` and
`n` sufficiently large, there is a feedback code with `(1/n) log M > R - ε` and `λ_max < ε`. -/
def IsAsymptoticallyAchievableFB (W : α → β → ℝ) (R : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, 0 < M ∧ ∃ c : FeedbackCode M n α β,
    R - ε < codeRate M n ∧ c.maxErrProb W < ε

omit [Fintype α] in
/-- A code without feedback, used as a feedback code, has the same conditional probabilities of
error. -/
lemma FeedbackCode.condErrProb_nfEnc [Nonempty α] {M n : ℕ} (hM : 0 < M) (W : α → β → ℝ)
    (c : ChannelCode M n α β) (w : Fin M) :
    (⟨nfEnc c.enc, c.dec⟩ : FeedbackCode M n α β).condErrProb W w = c.condErrProb W w := by
  classical
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [FeedbackCode.condErrProb, ChannelCode.condErrProb, fbLaw_nfEnc, uniformPMF,
    Fintype.card_fin]
  refine sum_congr rfl fun y _ => ?_
  split_ifs <;> field_simp

omit [Fintype α] in
/-- **(7.208)** A rate achievable without feedback is achievable with feedback. -/
theorem IsAsymptoticallyAchievable.fb [Nonempty α] {W : α → β → ℝ} {R : ℝ}
    (h : IsAsymptoticallyAchievable W R) : IsAsymptoticallyAchievableFB W R := by
  intro ε hε
  filter_upwards [h ε hε] with n ⟨M, hM, c, hr, hlam⟩
  refine ⟨M, hM, ⟨nfEnc c.enc, c.dec⟩, hr, ?_⟩
  rw [FeedbackCode.maxErrProb]
  simp only [FeedbackCode.condErrProb_nfEnc hM W c]
  exact hlam

/-- **(7.217)–(7.229)** Feedback does not increase the capacity: a rate `R` is achievable with
complete feedback iff `R ≤ C`. -/
theorem isAsymptoticallyAchievableFB_iff [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) {R : ℝ} :
    IsAsymptoticallyAchievableFB W R ↔ R ≤ capacity W := by
  constructor
  · intro h
    refine le_of_eventually_code_bound fun ε hε => ?_
    filter_upwards [h ε hε] with n ⟨M, hM, c, hr, hlam⟩
    exact ⟨M, hM, c.errProb W, (c.errProb_le_maxErrProb W hM).trans_lt hlam, hr,
      c.one_sub_errProb_mul_log_le hW hM⟩
  · intro hR
    exact ((isAsymptoticallyAchievable_iff hW).2 hR).fb

/-- **Definition 7.20.** The feedback capacity `C_FB`, the supremum of the rates achievable with
complete feedback. -/
def fbCapacityMax (W : α → β → ℝ) : ℝ := sSup {R | IsAsymptoticallyAchievableFB W R}

/-- `C_FB = C`. -/
theorem fbCapacityMax_eq_capacity [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W) :
    fbCapacityMax W = capacity W := by
  have h : {R | IsAsymptoticallyAchievableFB W R} = Set.Iic (capacity W) := by
    ext R
    exact isAsymptoticallyAchievableFB_iff hW
  rw [fbCapacityMax, h, csSup_Iic]

omit [Fintype α] in
/-- **Proposition 7.21.** The supremum in the definition of `C_FB` is a maximum: `C_FB` is
achievable with complete feedback. -/
theorem isAsymptoticallyAchievableFB_fbCapacityMax [Finite α] [Nonempty α] {W : α → β → ℝ}
    (hW : IsChannel W) : IsAsymptoticallyAchievableFB W (fbCapacityMax W) :=
  have := Fintype.ofFinite α
  (isAsymptoticallyAchievableFB_iff hW).2 (fbCapacityMax_eq_capacity hW).le

/-! ### Separation of source and channel coding -/

variable {𝒱 : Type*} [Fintype 𝒱]

/-- **(7.244)–(7.254)** The converse of the separation theorem, with complete feedback: if a source
is sent over the channel by joint source-channel codes with feedback, with encoders
`Xᵢ = fᵢ(U, Yⁱ⁻¹)` and probability of error `Pₑ → 0`, then `H ≤ C`. -/
theorem entropyRate_le_capacity_of_fbLaw (P : StochasticProcess 𝒱) {W : α → β → ℝ}
    (hW : IsChannel W) (enc : ∀ n k, (Fin n → 𝒱) → (Fin k → β) → α)
    (dec : ∀ n, (Fin n → β) → Fin n → 𝒱)
    (hc : Tendsto (fun n => errProb (fbLaw (P.law n) W (enc n) n) Prod.fst Prod.snd (dec n)) atTop
      (𝓝 0)) :
    P.entropyRate ≤ capacity W := by
  have hbound : ∀ᶠ n : ℕ in atTop, P.entropyRate ≤ log 2 / n +
      errProb (fbLaw (P.law n) W (enc n) n) Prod.fst Prod.snd (dec n) * log (Fintype.card 𝒱) +
        capacity W := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h₁ := entropy_le_of_fbLaw (enc := enc n) (P.isPMF n) hW (dec n)
    rw [entropyRV, dist_fst_fbLaw hW, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
      log_pow] at h₁
    have h₂ := P.mul_entropyRate_le_jointEntropy n
    rw [StochasticProcess.jointEntropy] at h₂
    have key : n * P.entropyRate ≤ n * (log 2 / n +
        errProb (fbLaw (P.law n) W (enc n) n) Prod.fst Prod.snd (dec n) *
          log (Fintype.card 𝒱) + capacity W) := by
      rw [mul_add, mul_add, mul_div_cancel₀ _ hn'.ne']
      linarith
    exact le_of_mul_le_mul_left key hn'
  have hlim : Tendsto (fun n : ℕ => log 2 / n +
      errProb (fbLaw (P.law n) W (enc n) n) Prod.fst Prod.snd (dec n) * log (Fintype.card 𝒱) +
        capacity W) atTop (𝓝 (capacity W)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (log 2)).add
      (hc.mul_const (log (Fintype.card 𝒱)))).add_const (capacity W)
    simpa using this
  exact ge_of_tendsto hlim hbound

end InfoTheory
