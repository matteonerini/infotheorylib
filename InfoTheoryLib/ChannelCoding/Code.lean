/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Capacity
public import InfoTheoryLib.Probability.IID

/-!
# Channel codes

An `(M, n)` code for a discrete memoryless channel sends one of `M` messages by `n` uses of the
channel: an encoder maps each message to a codeword in `𝒳ⁿ`, and a decoder guesses the message
from the received sequence in `𝒴ⁿ`. A rate `R` is achievable if there are `(⌈e^{nR}⌉, n)` codes
whose maximal probability of error tends to `0`, and the operational capacity is the supremum of
the achievable rates.

The messages `1, …, M` are `0, …, M - 1 : Fin M`. Rates are in nats per channel use: the book's
`(⌈2^{nR}⌉, n)` codes with `R` in bits are our `(⌈e^{nR}⌉, n)` codes with `R` in nats.

## Main definitions

* `channelExt W n`: the `n`-th extension `p(yⁿ | xⁿ) = ∏ᵢ p(yᵢ | xᵢ)` of a memoryless channel used
  without feedback, (7.27).
* `ChannelCode M n α β`: an `(M, n)` code, with encoder `enc` and decoder `dec`.
* `ChannelCode.condErrProb`, `ChannelCode.maxErrProb`, `ChannelCode.avgErrProb`: the conditional,
  maximal and average probabilities of error, (7.29)–(7.31).
* `IsAchievableRate W R`, `opCapacity W`: achievable rates and the operational capacity.

## Main statements

* `ChannelCode.avgErrProb_le_maxErrProb`: (7.33).
* `ChannelCode.exists_maxErrProb_le_two_mul`: (7.80)–(7.81), throwing away the worse half of the
  codewords of a code with small average error gives a code with small maximal error.
* `ChannelCode.exists_maxErrProb_le`: a code can be restricted to fewer messages without
  increasing the maximal error.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 7.5
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **(7.27)** The `n`-th extension `p(yⁿ | xⁿ) = ∏ᵢ p(yᵢ | xᵢ)` of the discrete memoryless channel
`W`, used without feedback. -/
def channelExt (W : α → β → ℝ) (n : ℕ) (x : Fin n → α) (y : Fin n → β) : ℝ := ∏ i, W (x i) (y i)

omit [Fintype α] in
lemma channelExt_nonneg {W : α → β → ℝ} (hW : IsChannel W) {n : ℕ} (x : Fin n → α)
    (y : Fin n → β) : 0 ≤ channelExt W n x y :=
  prod_nonneg fun _ _ => (hW _).nonneg _

omit [Fintype α] in
/-- The `n`-th extension of a channel is a channel. -/
lemma IsChannel.ext {W : α → β → ℝ} (hW : IsChannel W) (n : ℕ) : IsChannel (channelExt W n) := by
  classical
  intro x
  refine ⟨channelExt_nonneg hW x, ?_⟩
  have h := Fintype.prod_sum fun (i : Fin n) (b : β) => W (x i) b
  simp only [(hW _).sum_eq_one, prod_const_one] at h
  exact h.symm

/-- **Definition (Section 7.5).** An `(M, n)` code: an encoding function `enc` mapping each of the
messages `0, …, M - 1` to a codeword in `𝒳ⁿ`, and a decoding function `dec` guessing the message
from the received sequence. -/
structure ChannelCode (M n : ℕ) (α β : Type*) where
  /-- The encoding function `w ↦ xⁿ(w)`. -/
  enc : Fin M → Fin n → α
  /-- The decoding function `g : 𝒴ⁿ → {0, …, M - 1}`. -/
  dec : (Fin n → β) → Fin M

namespace ChannelCode

variable {M n : ℕ} (W : α → β → ℝ) (c : ChannelCode M n α β)

open Classical in
/-- **Definition (7.29).** The probability of error `λᵢ = Pr{g(Yⁿ) ≠ i | Xⁿ = xⁿ(i)}` when the
message `i` is sent. -/
def condErrProb (i : Fin M) : ℝ := ∑ y, if c.dec y ≠ i then channelExt W n (c.enc i) y else 0

/-- **Definition (7.30).** The maximal probability of error `λ^(n) = maxᵢ λᵢ`. -/
def maxErrProb : ℝ := ⨆ i, c.condErrProb W i

/-- **Definition (7.31).** The average probability of error `Pₑ^(n) = (1/M) ∑ᵢ λᵢ`. -/
def avgErrProb : ℝ := (∑ i, c.condErrProb W i) / M

variable {W}

omit [Fintype α] in
lemma condErrProb_nonneg (hW : IsChannel W) (i : Fin M) : 0 ≤ c.condErrProb W i := by
  classical
  exact sum_nonneg fun y _ => by split_ifs <;> simp [channelExt_nonneg hW]

omit [Fintype α] in
lemma condErrProb_le_one (hW : IsChannel W) (i : Fin M) : c.condErrProb W i ≤ 1 := by
  classical
  calc c.condErrProb W i ≤ ∑ y, channelExt W n (c.enc i) y :=
        sum_le_sum fun y _ => by split_ifs <;> simp [channelExt_nonneg hW]
    _ = 1 := ((hW.ext n) (c.enc i)).sum_eq_one

omit [Fintype α] in
lemma condErrProb_le_maxErrProb (i : Fin M) : c.condErrProb W i ≤ c.maxErrProb W :=
  le_ciSup (Set.finite_range _).bddAbove i

omit [Fintype α] in
lemma maxErrProb_nonneg (hW : IsChannel W) : 0 ≤ c.maxErrProb W := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [maxErrProb]
  · exact (c.condErrProb_nonneg hW ⟨0, hM⟩).trans (c.condErrProb_le_maxErrProb ⟨0, hM⟩)

omit [Fintype α] in
lemma maxErrProb_le {t : ℝ} (hM : 0 < M) (h : ∀ i, c.condErrProb W i ≤ t) :
    c.maxErrProb W ≤ t :=
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  ciSup_le h

omit [Fintype α] in
/-- **(7.33)** `Pₑ^(n) ≤ λ^(n)`. -/
lemma avgErrProb_le_maxErrProb : c.avgErrProb W ≤ c.maxErrProb W := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [avgErrProb, maxErrProb]
  · have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    rw [avgErrProb, div_le_iff₀ hM']
    calc ∑ i, c.condErrProb W i ≤ ∑ _i : Fin M, c.maxErrProb W :=
          sum_le_sum fun i _ => c.condErrProb_le_maxErrProb i
      _ = c.maxErrProb W * M := by simp [mul_comm]

omit [Fintype α] in
lemma avgErrProb_nonneg (hW : IsChannel W) : 0 ≤ c.avgErrProb W :=
  div_nonneg (sum_nonneg fun i _ => c.condErrProb_nonneg hW i) (Nat.cast_nonneg _)

/-- Re-index the messages of a code along an injection `e : Fin M' ↪ Fin M`: the new code sends
`xⁿ(e j)` for the message `j` and decodes as the old code, mapping back to the new messages. -/
def reindex {M' : ℕ} [NeZero M'] (c : ChannelCode M n α β) (e : Fin M' ↪ Fin M) :
    ChannelCode M' n α β where
  enc j := c.enc (e j)
  dec y := Function.invFun e (c.dec y)

omit [Fintype α] in
lemma condErrProb_reindex_le {M' : ℕ} [NeZero M'] (hW : IsChannel W) (e : Fin M' ↪ Fin M)
    (j : Fin M') : (c.reindex e).condErrProb W j ≤ c.condErrProb W (e j) := by
  classical
  refine sum_le_sum fun y _ => ?_
  by_cases h : c.dec y = e j
  · have : (c.reindex e).dec y = j := by
      simp only [reindex, h]
      exact Function.leftInverse_invFun e.injective j
    simp [this, h]
  · simp only [reindex]
    split_ifs <;> simp_all [channelExt_nonneg hW]

omit [Fintype α] in
/-- A code can be restricted to `M' ≤ M` messages without increasing the maximal error. -/
theorem exists_maxErrProb_le (hW : IsChannel W) {M' : ℕ} (hM' : 0 < M') (hMM : M' ≤ M) :
    ∃ c' : ChannelCode M' n α β, c'.maxErrProb W ≤ c.maxErrProb W := by
  have : NeZero M' := ⟨hM'.ne'⟩
  refine ⟨c.reindex (Fin.castLEEmb hMM), maxErrProb_le _ hM' fun j => ?_⟩
  exact (c.condErrProb_reindex_le hW _ j).trans (c.condErrProb_le_maxErrProb _)

omit [Fintype α] in
/-- **(7.80)–(7.81)** Throwing away the worse half of the codewords: if a code with `2M` codewords
has average probability of error `Pₑ`, at least `M` codewords have `λᵢ ≤ 2Pₑ`, and these form a
code with `M` codewords and maximal probability of error at most `2Pₑ`. -/
theorem exists_maxErrProb_le_two_mul (hW : IsChannel W) (hM : 0 < M)
    (c : ChannelCode (2 * M) n α β) :
    ∃ c' : ChannelCode M n α β, c'.maxErrProb W ≤ 2 * c.avgErrProb W := by
  classical
  set P := c.avgErrProb W
  have hP : 0 ≤ P := c.avgErrProb_nonneg hW
  set S := univ.filter fun i => c.condErrProb W i ≤ 2 * P
  have hsum : ∑ i, c.condErrProb W i = 2 * M * P := by
    have h2M : (2 * M : ℝ) ≠ 0 := by positivity
    simp only [P, avgErrProb]
    push_cast
    field_simp
  have hS : M ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have hc : M < Sᶜ.card := by rw [card_compl, Fintype.card_fin]; omega
    have hne : Sᶜ.Nonempty := card_pos.1 (by omega)
    have h1 : ∑ i ∈ Sᶜ, 2 * P < ∑ i ∈ Sᶜ, c.condErrProb W i :=
      sum_lt_sum_of_nonempty hne fun i hi => by simpa [S] using hi
    have h2 : ∑ i ∈ Sᶜ, c.condErrProb W i ≤ ∑ i, c.condErrProb W i :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => c.condErrProb_nonneg hW i
    rw [sum_const, nsmul_eq_mul] at h1
    have h3 : (M : ℝ) * (2 * P) ≤ Sᶜ.card * (2 * P) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc.le) (by positivity)
    nlinarith
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hS
  have : NeZero M := ⟨hM.ne'⟩
  let e : Fin M ↪ Fin (2 * M) := (T.orderEmbOfFin hT).toEmbedding
  refine ⟨c.reindex e, maxErrProb_le _ hM fun j => ?_⟩
  refine (c.condErrProb_reindex_le hW e j).trans ?_
  have : e j ∈ S := hTS (T.orderEmbOfFin_mem hT j)
  simpa [S] using this

end ChannelCode

/-- **Definition (Section 7.5).** A rate `R` (in nats) is achievable if there is a sequence of
`(⌈e^{nR}⌉, n)` codes whose maximal probability of error tends to `0`. -/
def IsAchievableRate (W : α → β → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, ChannelCode ⌈exp (n * R)⌉₊ n α β,
    Filter.Tendsto (fun n => (c n).maxErrProb W) Filter.atTop (nhds 0)

/-- **Definition (Section 7.5).** The (operational) capacity of a channel is the supremum of the
achievable rates. -/
def opCapacity (W : α → β → ℝ) : ℝ := sSup {R | IsAchievableRate W R}

lemma one_le_ceil_exp (x : ℝ) : 1 ≤ ⌈exp x⌉₊ :=
  Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (exp_pos x)).ne'

end InfoTheory
