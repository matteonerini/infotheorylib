/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Capacity

/-!
# Codes for the Gaussian channel

An `(M, n)` code for the Gaussian channel with power constraint `P` has an encoder sending each
message `w ∈ {1, …, M}` to a codeword `xⁿ(w) ∈ ℝⁿ` with `∑ᵢ xᵢ(w)² ≤ nP`, and a (measurable)
decoder `g : ℝⁿ → {1, …, M}`. The channel adds i.i.d. noise `Zᵢ ∼ N(0, N)`, so message `w` is
decoded correctly when `g(xⁿ(w) + Zⁿ) = w`. Achievable rates and the (operational) capacity are
defined as for discrete channels.

## Main definitions

* `noiseLaw N n`: the law `N(0, N)ⁿ` of `n` noise samples.
* `GaussianCode M n`: an `(M, n)` code for the Gaussian channel, (9.18)–(9.19).
* `GaussianCode.SatisfiesPower`: the power constraint (9.18).
* `GaussianCode.condErrProb`, `GaussianCode.maxErrProb`, `GaussianCode.avgErrProb`: the
  probabilities of error `λᵢ`, `λ^(n)` and `Pₑ^(n)`, (9.20).
* `IsAchievableGaussianRate P N R`, `gaussianOpCapacity P N`: achievable rates and the capacity.

## Main statements

* `GaussianCode.exists_maxErrProb_le_two_mul`: throwing away the worse half of the codewords.

## Implementation notes

Messages `1, …, M` are `0, …, M - 1 : Fin M`. Rates are in nats: a rate `R` is achievable if
there are `(⌈e^{nR}⌉, n)` codes satisfying the power constraint with maximal probability of
error tending to `0`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 9.1
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-- The law `N(0, N)ⁿ` of `n` i.i.d. noise samples. -/
abbrev noiseLaw (N : ℝ≥0) (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 N

/-- **Definition (9.18)–(9.19).** An `(M, n)` code for the Gaussian channel: an encoder sending
each message to a codeword in `ℝⁿ` and a measurable decoder. -/
structure GaussianCode (M n : ℕ) where
  /-- The encoding function `w ↦ xⁿ(w)`. -/
  enc : Fin M → Fin n → ℝ
  /-- The decoding function `g : ℝⁿ → {0, …, M - 1}`. -/
  dec : (Fin n → ℝ) → Fin M
  measurable_dec : Measurable dec

namespace GaussianCode

variable {M n : ℕ} (N : ℝ≥0) (c : GaussianCode M n)

/-- **(9.18)** The power constraint: every codeword has `∑ᵢ xᵢ(w)² ≤ nP`. -/
def SatisfiesPower (P : ℝ) : Prop := ∀ w, ∑ i, c.enc w i ^ 2 ≤ n * P

/-- The conditional probability of error `λ_w = Pr{g(xⁿ(w) + Zⁿ) ≠ w}` when `w` is sent. -/
def condErrProb (w : Fin M) : ℝ := (noiseLaw N n).real {z | c.dec (c.enc w + z) ≠ w}

/-- The maximal probability of error `λ^(n) = max_w λ_w`. -/
def maxErrProb : ℝ := ⨆ w, c.condErrProb N w

/-- **(9.20)** The average probability of error `Pₑ^(n) = (1/M) ∑_w λ_w`. -/
def avgErrProb : ℝ := (∑ w, c.condErrProb N w) / M

lemma condErrProb_nonneg (w : Fin M) : 0 ≤ c.condErrProb N w := measureReal_nonneg

lemma condErrProb_le_one (w : Fin M) : c.condErrProb N w ≤ 1 := measureReal_le_one

lemma condErrProb_le_maxErrProb (w : Fin M) : c.condErrProb N w ≤ c.maxErrProb N :=
  le_ciSup (Set.finite_range _).bddAbove w

lemma maxErrProb_nonneg : 0 ≤ c.maxErrProb N := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [maxErrProb]
  · exact (c.condErrProb_nonneg N ⟨0, hM⟩).trans (c.condErrProb_le_maxErrProb N _)

lemma maxErrProb_le {t : ℝ} (hM : 0 < M) (h : ∀ w, c.condErrProb N w ≤ t) :
    c.maxErrProb N ≤ t :=
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  ciSup_le h

lemma maxErrProb_le_one : c.maxErrProb N ≤ 1 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [maxErrProb]
  · exact c.maxErrProb_le N hM fun w => c.condErrProb_le_one N w

lemma avgErrProb_nonneg : 0 ≤ c.avgErrProb N :=
  div_nonneg (sum_nonneg fun w _ => c.condErrProb_nonneg N w) (Nat.cast_nonneg _)

lemma avgErrProb_le_maxErrProb : c.avgErrProb N ≤ c.maxErrProb N := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [avgErrProb, maxErrProb]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [avgErrProb, div_le_iff₀ hM']
  calc ∑ w, c.condErrProb N w ≤ ∑ _w : Fin M, c.maxErrProb N :=
        sum_le_sum fun w _ => c.condErrProb_le_maxErrProb N w
    _ = c.maxErrProb N * M := by simp [mul_comm]

/-- Re-index the messages of a code along an injection `e : Fin M' ↪ Fin M`. -/
def reindex {M' : ℕ} [NeZero M'] (e : Fin M' ↪ Fin M) : GaussianCode M' n where
  enc j := c.enc (e j)
  dec y := Function.invFun e (c.dec y)
  measurable_dec := (Measurable.of_discrete (f := Function.invFun e)).comp c.measurable_dec

lemma condErrProb_reindex_le {M' : ℕ} [NeZero M'] (e : Fin M' ↪ Fin M) (j : Fin M') :
    (c.reindex e).condErrProb N j ≤ c.condErrProb N (e j) := by
  refine measureReal_mono fun z hz => ?_
  simp only [Set.mem_ofPred_eq] at hz ⊢
  intro h
  apply hz
  simp only [reindex, h]
  exact Function.leftInverse_invFun e.injective j

lemma SatisfiesPower.reindex {P : ℝ} (hc : c.SatisfiesPower P) {M' : ℕ} [NeZero M']
    (e : Fin M' ↪ Fin M) : (c.reindex e).SatisfiesPower P := fun j => hc (e j)

/-- **(7.80)–(7.81)** for the Gaussian channel. Throwing away the worse half of the codewords: if a
code with `2M` codewords has average probability of error `Pₑ`, at least `M` codewords have
`λ_w ≤ 2Pₑ`, and these form a code with `M` codewords, satisfying the same power constraint, with
maximal probability of error at most `2Pₑ`. -/
theorem exists_maxErrProb_le_two_mul (hM : 0 < M) (c : GaussianCode (2 * M) n) {P : ℝ}
    (hc : c.SatisfiesPower P) :
    ∃ c' : GaussianCode M n, c'.SatisfiesPower P ∧ c'.maxErrProb N ≤ 2 * c.avgErrProb N := by
  classical
  set Pe := c.avgErrProb N
  have hP : 0 ≤ Pe := c.avgErrProb_nonneg N
  set S := univ.filter fun i => c.condErrProb N i ≤ 2 * Pe
  have hsum : ∑ i, c.condErrProb N i = 2 * M * Pe := by
    have h2M : (2 * M : ℝ) ≠ 0 := by positivity
    simp only [Pe, avgErrProb]
    push_cast
    field_simp
  have hS : M ≤ S.card := by
    by_contra hlt
    push Not at hlt
    have hc' : M < Sᶜ.card := by rw [card_compl, Fintype.card_fin]; omega
    have hne : Sᶜ.Nonempty := card_pos.1 (by omega)
    have h1 : ∑ i ∈ Sᶜ, 2 * Pe < ∑ i ∈ Sᶜ, c.condErrProb N i :=
      sum_lt_sum_of_nonempty hne fun i hi => by simpa [S] using hi
    have h2 : ∑ i ∈ Sᶜ, c.condErrProb N i ≤ ∑ i, c.condErrProb N i :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => c.condErrProb_nonneg N i
    rw [sum_const, nsmul_eq_mul] at h1
    have h3 : (M : ℝ) * (2 * Pe) ≤ Sᶜ.card * (2 * Pe) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc'.le) (by positivity)
    nlinarith
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hS
  have : NeZero M := ⟨hM.ne'⟩
  let e : Fin M ↪ Fin (2 * M) := (T.orderEmbOfFin hT).toEmbedding
  refine ⟨c.reindex e, hc.reindex c e, maxErrProb_le _ _ hM fun j => ?_⟩
  refine (c.condErrProb_reindex_le N e j).trans ?_
  have : e j ∈ S := hTS (T.orderEmbOfFin_mem hT j)
  simpa [S] using this

end GaussianCode

/-- **Definition (Section 9.1).** A rate `R` (in nats) is achievable for the Gaussian channel with
power constraint `P` and noise variance `N` if there is a sequence of `(⌈e^{nR}⌉, n)` codes
satisfying the power constraint whose maximal probability of error tends to `0`. -/
def IsAchievableGaussianRate (P N : ℝ≥0) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, GaussianCode ⌈exp (n * R)⌉₊ n, (∀ n, (c n).SatisfiesPower P) ∧
    Tendsto (fun n => (c n).maxErrProb N) atTop (𝓝 0)

/-- **Definition (Section 9.1).** The capacity of the Gaussian channel is the supremum of the
achievable rates. -/
def gaussianOpCapacity (P N : ℝ≥0) : ℝ := sSup {R | IsAchievableGaussianRate P N R}

end InfoTheory
