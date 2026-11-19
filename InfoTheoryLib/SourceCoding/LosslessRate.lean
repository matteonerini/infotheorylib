/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.Basic
public import InfoTheoryLib.Entropy.Fano
public import InfoTheoryLib.RateDistortion.Basic
public import InfoTheoryLib.Typicality.Basic

/-!
# The lossless source coding theorem

A `(2^{nR}, n)` fixed-length source code for a discrete memoryless source `X ∼ p(x)` maps each
source sequence `xⁿ` to an index `m(xⁿ) ∈ [1 : 2^{nR}) = {1, …, 2^⌊nR⌋}` and each index to an
estimate `x̂ⁿ(m)`. A rate `R ≥ 0` is achievable if there are codes whose probability of error
`P{X̂ⁿ ≠ Xⁿ}` tends to `0`, and the optimal lossless compression rate `R*` is the infimum of the
achievable rates. Shannon's lossless source coding theorem says that `R* = H(X)`.

Achievability: there are at most `e^{n(H(X) + δ(ε))}` typical sequences; giving each an index
leaves only the atypical sequences in error. Converse: by Fano's inequality,
`nH(X) = H(Xⁿ) ≤ H(M) + H(Xⁿ|X̂ⁿ) ≤ nR log 2 + log 2 + P_e^(n) n log |𝒳|`.

## Main definitions

* `RDCode.blockErrProb p c`: the probability of error `P{X̂ⁿ ≠ Xⁿ}` of a source code.
* `IsAchievableLosslessRate p R`: the rate `R` (in bits) is achievable.
* `optLosslessRate p`: the optimal lossless compression rate `R*`, in bits.

## Main statements

* `isAchievableLosslessRate_of_lt`: achievability.
* `IsAchievableLosslessRate.le`: the converse.
* `optLosslessRate_eq`: **the lossless source coding theorem**, `R* = H(X)` bits.

## Implementation notes

A source code is an `RDCode M n α α`, with encoder `enc` and decoder `dec`, the same data as a
rate–distortion code with reproduction alphabet `𝒳`. Rates are in bits, so `R* = H(X) / log 2`
with `H(X)` in nats.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α] {p : α → ℝ}

/-- **Definition (Lecture 3).** The probability of error `P_e^(n) = P{X̂ⁿ ≠ Xⁿ}` of a source code
for the i.i.d. source `Xᵢ ∼ p`. -/
def RDCode.blockErrProb {M n : ℕ} (p : α → ℝ) (c : RDCode M n α α) : ℝ :=
  errProb (iidPMF p n) id (c.dec ∘ c.enc) id

/-- **Definition (Lecture 3).** A rate `R ≥ 0`, in bits per source symbol, is achievable if there
is a sequence of `(2^{nR}, n)` fixed-length source codes, with index set
`[1 : 2^{nR}) = {1, …, 2^⌊nR⌋}`, whose probability of error tends to `0`. -/
def IsAchievableLosslessRate (p : α → ℝ) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, RDCode (2 ^ ⌊n * R⌋₊) n α α,
    Tendsto (fun n => (c n).blockErrProb p) atTop (𝓝 0)

/-- **Definition (Lecture 3).** The optimal lossless compression rate `R*`, in bits per source
symbol: the infimum of the achievable rates. -/
def optLosslessRate (p : α → ℝ) : ℝ := sInf {R | IsAchievableLosslessRate p R}

lemma RDCode.blockErrProb_nonneg {M n : ℕ} (hp : IsPMF p) (c : RDCode M n α α) :
    0 ≤ c.blockErrProb p :=
  errProb_nonneg (iidPMF_isPMF hp n) _ _ _

/-! ### Achievability -/

omit [Fintype α] in
/-- A code that assigns an index to each sequence of a set `T` of at most `M` sequences, and
decodes it without error. -/
lemma exists_code_of_card_le [Nonempty α] {M n : ℕ} (hM : 0 < M) (T : Finset (Fin n → α))
    (hT : T.card ≤ M) : ∃ c : RDCode M n α α, ∀ x ∈ T, c.dec (c.enc x) = x := by
  classical
  let e := T.equivFin
  refine ⟨⟨fun x => if hx : x ∈ T then Fin.castLE hT (e ⟨x, hx⟩) else ⟨0, hM⟩,
    fun m => if h : (m : ℕ) < T.card then (e.symm ⟨m, h⟩).val else fun _ => Classical.arbitrary α⟩,
    fun x hx => ?_⟩
  simp [hx]

/-- **Lossless source coding theorem (Lecture 3), achievability.** Every rate `R > H(X)` bits is
achievable. -/
theorem isAchievableLosslessRate_of_lt (hp : IsPMF p) {R : ℝ} (hR : entropy p / log 2 < R) :
    IsAchievableLosslessRate p R := by
  classical
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  have hl := log_pos one_lt_two
  have hH := entropy_nonneg hp
  have hRl : entropy p < R * log 2 := (div_lt_iff₀ hl).1 hR
  have hR0 : 0 ≤ R := le_trans (div_nonneg hH hl.le) hR.le
  set ε := (R * log 2 - entropy p) / (2 * (entropy p + 1))
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  have hεH : entropy p + ε * entropy p < R * log 2 := by
    have : ε * entropy p ≤ (R * log 2 - entropy p) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  -- For `n` large there are at most `2^⌊nR⌋` typical sequences.
  have hev : ∀ᶠ n : ℕ in atTop, (robustTypicalSet p n ε).card ≤ 2 ^ ⌊n * R⌋₊ := by
    have hgap : 0 < R * log 2 - (entropy p + ε * entropy p) := by linarith
    filter_upwards [eventually_ge_atTop ⌈log 2 / (R * log 2 - (entropy p + ε * entropy p))⌉₊]
      with n hn
    have hn' : log 2 ≤ n * (R * log 2 - (entropy p + ε * entropy p)) :=
      (div_le_iff₀ hgap).1 (Nat.ceil_le.1 hn)
    have hcard := card_robustTypicalSet_le hp n ε
    have hfloor : (n * R - 1) * log 2 ≤ ⌊n * R⌋₊ * log 2 :=
      mul_le_mul_of_nonneg_right (by linarith [Nat.lt_floor_add_one (n * R)]) hl.le
    have h2 : exp (n * (entropy p + ε * entropy p)) ≤ ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) := by
      push_cast
      rw [← exp_log (by positivity : (0 : ℝ) < 2 ^ ⌊n * R⌋₊), log_pow]
      exact exp_le_exp.2 (by nlinarith)
    exact_mod_cast hcard.trans h2
  have hcode : ∀ n : ℕ, ∃ c : RDCode (2 ^ ⌊n * R⌋₊) n α α,
      (robustTypicalSet p n ε).card ≤ 2 ^ ⌊n * R⌋₊ →
        ∀ x ∈ robustTypicalSet p n ε, c.dec (c.enc x) = x := fun n => by
    by_cases h : (robustTypicalSet p n ε).card ≤ 2 ^ ⌊n * R⌋₊
    · obtain ⟨c, hc⟩ := exists_code_of_card_le (by positivity) _ h
      exact ⟨c, fun _ => hc⟩
    · obtain ⟨c, -⟩ := exists_code_of_card_le (α := α) (n := n)
        (by positivity : 0 < 2 ^ ⌊n * R⌋₊) ∅ (by simp)
      exact ⟨c, fun h' => absurd h' h⟩
  choose c hc using hcode
  refine ⟨hR0, c, ?_⟩
  -- Only the atypical sequences are decoded in error.
  have hlim : Tendsto (fun n => 1 - prob (iidPMF p n) (robustTypicalSet p n ε)) atTop (𝓝 0) := by
    simpa using (tendsto_prob_robustTypicalSet hp hε).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => (c n).blockErrProb_nonneg hp) ?_
  filter_upwards [hev] with n hn
  have e : (∑ x, if x ∈ (robustTypicalSet p n ε)ᶜ then iidPMF p n x else 0) =
      prob (iidPMF p n) (robustTypicalSet p n ε)ᶜ := by
    rw [sum_ite_mem, univ_inter]
    rfl
  rw [← prob_compl (iidPMF_isPMF hp n), RDCode.blockErrProb, errProb, ← e]
  refine sum_le_sum fun x _ => ?_
  by_cases hT : x ∈ robustTypicalSet p n ε
  · have : (c n).dec ((c n).enc x) = x := hc n hn x hT
    simp [this, hT]
  · have := iidPMF_nonneg hp.nonneg x
    simp only [mem_compl, hT, not_false_eq_true, ite_true]
    split_ifs <;> linarith

/-! ### The converse -/

/-- **Lossless source coding theorem (Lecture 3), converse for one code.** A source code with `M`
indices satisfies `nH(X) ≤ log M + log 2 + P_e^(n) n log |𝒳|`. -/
theorem RDCode.mul_entropy_le {M n : ℕ} (hp : IsPMF p) (c : RDCode M n α α) :
    n * entropy p ≤ log M + log 2 + c.blockErrProb p * (n * log (Fintype.card α)) := by
  have hμ := iidPMF_isPMF hp n
  set Xh : (Fin n → α) → Fin n → α := c.dec ∘ c.enc
  have h1 : H[(id : (Fin n → α) → Fin n → α) ; iidPMF p n] = n * entropy p := by
    rw [entropyRV, dist_id, entropy_iidPMF hp]
  -- `H(Xⁿ) ≤ H(X̂ⁿ, Xⁿ) = H(X̂ⁿ) + H(Xⁿ|X̂ⁿ)`.
  have h2 := chain_rule hμ Xh id
  have h3 : H[(id : (Fin n → α) → Fin n → α) ; iidPMF p n] ≤ H[pair Xh id ; iidPMF p n] :=
    entropyRV_comp_le hμ (pair Xh id) Prod.snd
  -- `H(X̂ⁿ) ≤ H(M) ≤ log M`.
  have h4 : H[Xh ; iidPMF p n] ≤ log M := by
    have := (entropyRV_comp_le hμ c.enc c.dec).trans (entropyRV_le_log_card hμ c.enc)
    simpa using this
  -- Fano's inequality.
  have h5 := fano_weak hμ id Xh id
  have hcard : log (Fintype.card (Fin n → α)) = n * log (Fintype.card α) := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, log_pow]
  rw [hcard] at h5
  change _ ≤ _ + c.blockErrProb p * _ at h5
  linarith

/-- **Lossless source coding theorem (Lecture 3), weak converse.** Every achievable rate is at
least `H(X)` bits. -/
theorem IsAchievableLosslessRate.le (hp : IsPMF p) {R : ℝ} (h : IsAchievableLosslessRate p R) :
    entropy p / log 2 ≤ R := by
  obtain ⟨hR0, c, hc⟩ := h
  have hl := log_pos one_lt_two
  set L := log (Fintype.card α)
  have hbound : ∀ᶠ n : ℕ in atTop,
      entropy p ≤ R * log 2 + log 2 / n + (c n).blockErrProb p * L := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (c n).mul_entropy_le hp
    have hM : log ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) ≤ n * R * log 2 := by
      push_cast
      rw [log_pow]
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hl.le
    have : n * entropy p ≤ n * (R * log 2 + log 2 / n + (c n).blockErrProb p * L) := by
      rw [mul_add, mul_add, mul_div_cancel₀ _ hn'.ne']
      nlinarith
    exact le_of_mul_le_mul_left this hn'
  have hlim : Tendsto (fun n : ℕ => R * log 2 + log 2 / n + (c n).blockErrProb p * L) atTop
      (𝓝 (R * log 2)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (log 2)).const_add (R * log 2)).add
      (hc.mul_const L)
    simpa using this
  rw [div_le_iff₀ hl]
  exact ge_of_tendsto hlim hbound

/-- **Shannon's lossless source coding theorem (Lecture 3).** The optimal lossless compression
rate of a discrete memoryless source is `R* = H(X)` bits per symbol. -/
theorem optLosslessRate_eq (hp : IsPMF p) : optLosslessRate p = entropy p / log 2 := by
  have hl := log_pos one_lt_two
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    ⟨entropy p / log 2 + 1, isAchievableLosslessRate_of_lt hp (by linarith)⟩
    (fun R hR => hR.le hp) fun w hw =>
      ⟨(entropy p / log 2 + w) / 2, isAchievableLosslessRate_of_lt hp (by linarith), by linarith⟩

end InfoTheory
