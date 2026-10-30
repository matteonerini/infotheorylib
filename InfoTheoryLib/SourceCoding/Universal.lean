/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Statistics.LargeDeviations

/-!
# Universal source coding

A fixed-rate block code of rate `R` describes `xⁿ` by one of `e^{nR}` indices. The code that
enumerates the sequences whose type has entropy at most `Rₙ = R - |𝒳| log (n + 1)/n` has at most
`e^{nR}` codewords and does not depend on the source; for every i.i.d. source `Q` with
`H(Q) < R`, its probability of error tends to `0`.

## Main definitions

* `FixedRateCode M n α`: a fixed-rate block code with `M` indices, (11.72)–(11.73).
* `FixedRateCode.errProb`: its probability of error `Qⁿ(φₙ(fₙ(Xⁿ)) ≠ Xⁿ)`, (11.74).
* `universalSet R n`: the set `A = {x : H(Pₓ) ≤ Rₙ}` (11.75)–(11.76).
* `universalCode`: the universal code of Csiszár and Körner.

## Main statements

* `card_universalSet_le`: (11.77)–(11.82), `|A| ≤ e^{nR}`.
* `errProb_universalCode_le`: (11.84)–(11.87), `Pₑ ≤ (n + 1)^|𝒳| e^{-n min_{H(P) > Rₙ} D(P‖Q)}`.
* `tendsto_errProb_universalCode`: **Theorem 11.3.1**.

## Implementation notes

Rates are in nats and a code of rate `R ≥ 0` has `⌊e^{nR}⌋` indices.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 11.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- **Definition (11.72)–(11.73).** A fixed-rate block code with `M` indices for sequences of
length `n`: an encoder `fₙ : 𝒳ⁿ → {0, …, M - 1}` and a decoder `φₙ : {0, …, M - 1} → 𝒳ⁿ`. -/
structure FixedRateCode (M n : ℕ) (α : Type*) where
  /-- The encoder `fₙ`. -/
  enc : (Fin n → α) → Fin M
  /-- The decoder `φₙ`. -/
  dec : Fin M → Fin n → α

open Classical in
/-- **Definition (11.74).** The probability of error `Qⁿ(φₙ(fₙ(Xⁿ)) ≠ Xⁿ)` of a code for the
i.i.d. source `Q`. -/
def FixedRateCode.errProb {M n : ℕ} (Q : α → ℝ) (c : FixedRateCode M n α) : ℝ :=
  prob (iidPMF Q n) (univ.filter fun x => c.dec (c.enc x) ≠ x)

/-- **(11.75)** The adjusted rate `Rₙ = R - |𝒳| log (n + 1)/n`. -/
def adjustedRate (α : Type*) [Fintype α] (R : ℝ) (n : ℕ) : ℝ :=
  R - Fintype.card α * log (n + 1) / n

open Classical in
/-- **(11.76)** The set `A = {x ∈ 𝒳ⁿ : H(Pₓ) ≤ Rₙ}` of sequences described by the universal
code. -/
def universalSet (α : Type*) [Fintype α] (R : ℝ) (n : ℕ) : Finset (Fin n → α) :=
  typeEvent {P | entropy P ≤ adjustedRate α R n} n

/-- **(11.77)–(11.82)** The universal set has at most `e^{nR}` elements. -/
theorem card_universalSet_le (R : ℝ) (n : ℕ) :
    ((universalSet α R n).card : ℝ) ≤ exp (n * R) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, zero_mul, exp_zero]
    exact_mod_cast (card_le_univ _).trans (by simp)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set S := (types α n).filter (· ∈ {P | entropy P ≤ adjustedRate α R n})
  -- `|A| = ∑_{P : H(P) ≤ Rₙ} |T(P)| ≤ |𝒫ₙ| e^{nRₙ} ≤ (n + 1)^|𝒳| e^{nRₙ} = e^{nR}`.
  have hcard : ((universalSet α R n).card : ℝ) = ∑ P ∈ S, ((typeClass P n).card : ℝ) := by
    have h := prob_typeEvent_eq_sum (fun _ : α => (1 : ℝ)) {P | entropy P ≤ adjustedRate α R n} n
    have hone : ∀ T : Finset (Fin n → α), prob (iidPMF (fun _ : α => (1 : ℝ)) n) T = T.card :=
      fun T => by simp [prob, iidPMF]
    rw [hone] at h
    simp only [hone] at h
    exact h
  have hT : ∀ P ∈ S, ((typeClass P n).card : ℝ) ≤ exp (n * adjustedRate α R n) := by
    intro P hP
    obtain ⟨hPt, hPE⟩ := mem_filter.1 hP
    obtain ⟨x, rfl⟩ := mem_types.1 hPt
    exact (card_typeClass_le hn x).trans (exp_le_exp.2 (mul_le_mul_of_nonneg_left hPE hn'.le))
  rw [hcard]
  calc ∑ P ∈ S, ((typeClass P n).card : ℝ) ≤ ∑ _P ∈ S, exp (n * adjustedRate α R n) :=
        sum_le_sum hT
    _ = S.card * exp (n * adjustedRate α R n) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n + 1) ^ Fintype.card α * exp (n * adjustedRate α R n) :=
        mul_le_mul_of_nonneg_right ((by exact_mod_cast card_filter_le _ _ :
          (S.card : ℝ) ≤ (types α n).card).trans (card_types_le n)) (exp_pos _).le
    _ = exp (n * R) := by
        rw [adjustedRate, mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hn'.ne', exp_sub,
          mul_comm, ← log_pow, exp_log (by positivity), div_mul_cancel₀ _ (by positivity)]

lemma card_universalSet_le_floor (R : ℝ) (n : ℕ) :
    (universalSet α R n).card ≤ ⌊exp (n * R)⌋₊ :=
  Nat.le_floor (card_universalSet_le R n)

open Classical in
/-- **Theorem 11.3.1.** The universal code: the sequences of the universal set are sent by their
index in an enumeration of the set, and all the others by the index `0`. -/
def universalCode [Nonempty α] {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    FixedRateCode ⌊exp (n * R)⌋₊ n α where
  enc x := if h : x ∈ universalSet α R n then
      Fin.castLE (card_universalSet_le_floor R n) ((universalSet α R n).equivFin ⟨x, h⟩)
    else ⟨0, Nat.floor_pos.2 (one_le_exp (by positivity))⟩
  dec w := if h : (w : ℕ) < (universalSet α R n).card then
      ((universalSet α R n).equivFin.symm ⟨w, h⟩ : Fin n → α)
    else fun _ => Classical.arbitrary α

lemma universalCode_dec_enc [Nonempty α] {R : ℝ} (hR : 0 ≤ R) {n : ℕ} {x : Fin n → α}
    (hx : x ∈ universalSet α R n) : (universalCode hR n).dec ((universalCode hR n).enc x) = x := by
  classical
  simp only [universalCode, hx, ↓reduceDIte, Fin.val_castLE, Fin.is_lt, Fin.eta,
    Equiv.symm_apply_apply]

/-- **(11.84)–(11.87)** The probability of error of the universal code is at most
`Qⁿ(H(P_{Xⁿ}) > Rₙ) ≤ (n + 1)^|𝒳| e^{-nD*}`, with `D* = inf_{H(P) > Rₙ} D(P‖Q)`. -/
theorem errProb_universalCode_le [Nonempty α] {R : ℝ} (hR : 0 ≤ R) {Q : α → ℝ} (hQ : IsPMF Q)
    {n : ℕ} (hn : 0 < n) :
    (universalCode hR n).errProb Q ≤ (n + 1) ^ Fintype.card α *
      exp (-(n * sanovExponent Q {P | adjustedRate α R n < entropy P})) := by
  classical
  refine le_trans (prob_mono (iidPMF_nonneg hQ.nonneg) fun x hx => ?_)
    (prob_typeEvent_le_sanov hQ _ hn)
  rw [mem_filter] at hx
  rw [mem_typeEvent]
  by_contra h
  exact hx.2 (universalCode_dec_enc hR (mem_typeEvent.2
    (show entropy (typeOf x) ≤ adjustedRate α R n from not_lt.1 h)))

/-- **Theorem 11.3.1.** There is a sequence of universal codes of rate `R`: the same codes have
probability of error `Pₑ^(n) → 0` for every i.i.d. source `Q` with `H(Q) < R`. -/
theorem tendsto_errProb_universalCode [Nonempty α] {R : ℝ} (hR : 0 ≤ R) {Q : α → ℝ}
    (hQ : IsPMF Q) (hHR : entropy Q < R) :
    Tendsto (fun n => (universalCode hR n).errProb Q) atTop (𝓝 0) := by
  classical
  set δ := (R - entropy Q) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  -- The entropy is continuous at `Q`.
  have hcont : Continuous fun P : α → ℝ => entropy P := by
    simp only [entropy_eq_sum_negMulLog]
    exact continuous_finsetSum _ fun a _ => continuous_negMulLog.comp (continuous_apply a)
  obtain ⟨η, hη, hηH⟩ := Metric.continuousAt_iff.1 hcont.continuousAt δ hδ
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  -- Strongly typical sequences have types within `η` of `Q`.
  have htyp := tendsto_prob_strongTypicalSet hQ (show 0 < η * Fintype.card α by positivity)
  have hlog := tendsto_log_add_one_div.const_mul (Fintype.card α : ℝ)
  rw [mul_zero] at hlog
  have hle : ∀ᶠ n : ℕ in atTop, (universalCode hR n).errProb Q ≤
      1 - prob (iidPMF Q n) (strongTypicalSet Q n (η * Fintype.card α)) := by
    filter_upwards [hlog.eventually (gt_mem_nhds hδ), eventually_gt_atTop 0] with n hlogn hn
    rw [FixedRateCode.errProb, ← prob_compl (iidPMF_isPMF hQ n)]
    refine prob_mono (iidPMF_nonneg hQ.nonneg) fun x hx => ?_
    rw [mem_compl]
    intro hxs
    rw [mem_filter] at hx
    refine hx.2 (universalCode_dec_enc hR (mem_typeEvent.2 ?_))
    rw [mem_strongTypicalSet] at hxs
    have hclose : Dist.dist (typeOf x) Q < η := by
      refine (dist_pi_lt_iff hη).2 fun a => ?_
      rw [Real.dist_eq]
      rcases (hQ.nonneg a).eq_or_lt with h0 | h0
      · rw [← h0, typeOf, (hxs a).2 h0.symm]
        simpa using hη
      · have := (hxs a).1 h0
        rwa [mul_div_cancel_right₀ _ hcard.ne'] at this
    have hH := hηH hclose
    rw [Real.dist_eq] at hH
    change entropy (typeOf x) ≤ adjustedRate α R n
    rw [adjustedRate]
    have : (Fintype.card α : ℝ) * (log (n + 1) / n) = Fintype.card α * log (n + 1) / n := by ring
    have hδdef : R - entropy Q = 2 * δ := by simp only [δ]; ring
    linarith [(abs_lt.1 hH).2]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using htyp.const_sub 1)
    (Eventually.of_forall fun n => prob_nonneg (iidPMF_nonneg hQ.nonneg) _) hle

end InfoTheory
