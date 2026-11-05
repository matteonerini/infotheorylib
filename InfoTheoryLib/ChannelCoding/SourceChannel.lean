/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.StochasticProcess.Independent
public import InfoTheoryLib.AEP.TypicalSet

/-!
# The joint source–channel coding theorem

A source `V₁, V₂, …` is sent over a discrete memoryless channel, one channel use per source
symbol: an encoder maps the block `Vⁿ` to a codeword `Xⁿ(Vⁿ)`, and a decoder estimates `Vⁿ` from
the output `Yⁿ`. If the source has typical sets of size about `e^{nH}` (as a source satisfying
the AEP does) and `H < C`, the two-stage scheme works. It indexes the typical sequences with
`n(H + ε)` nats and sends the index with a channel code, so the probability of error tends to
`0`. Conversely, a stationary source with entropy rate `H(𝒱) > C` cannot be sent reliably. So data
compression and data transmission can be designed separately.

Logarithms are natural.

## Main definitions

* `SourceChannelCode n 𝒱 α β`: a source–channel code of block length `n`.
* `SourceChannelCode.errProb`: its probability of error `Pr{V̂ⁿ ≠ Vⁿ}`, (7.136).
* `randomErrProb P W q g`: the probability of error of a code with a random encoder
  `q(xⁿ | vⁿ)` and the decoder `g`.
* `StochasticProcess.HasTypicalSets P H`: the source has, for every `ε > 0`, sets of size at most
  `e^{n(H+ε)}` and probability tending to `1`, the consequence of the AEP used in the theorem.

## Main statements

* `iidProcess_hasTypicalSets`: i.i.d. sources have typical sets, by the AEP (Chapter 3).
* `exists_sourceChannelCode`: Theorem 7.13.1 (achievability), (7.137)–(7.140).
* `entropyRate_le_capacity`: Theorem 7.13.1 (converse), (7.143)–(7.150).
* `entropyRate_le_capacity_of_random`: the converse for random encoders, by derandomization
  (`exists_errProb_le_randomErrProb`).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 7.13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒱 α β : Type*} [Fintype 𝒱] [Fintype α] [Fintype β]

/-- **Section 7.13.** A source–channel code of block length `n`: an encoder mapping source blocks
`vⁿ` to channel codewords `xⁿ(vⁿ)`, and a decoder `g : 𝒴ⁿ → 𝒱ⁿ`. -/
structure SourceChannelCode (n : ℕ) (𝒱 α β : Type*) where
  /-- The encoder `vⁿ ↦ xⁿ(vⁿ)`. -/
  enc : (Fin n → 𝒱) → Fin n → α
  /-- The decoder `g : 𝒴ⁿ → 𝒱ⁿ`. -/
  dec : (Fin n → β) → Fin n → 𝒱

open Classical in
/-- **(7.136)** The probability of error `Pr{V̂ⁿ ≠ Vⁿ} = ∑ p(vⁿ) p(yⁿ | xⁿ(vⁿ)) 1(g(yⁿ) ≠ vⁿ)` of a
source–channel code for the source `P`. -/
def SourceChannelCode.errProb {n : ℕ} (P : StochasticProcess 𝒱) (W : α → β → ℝ)
    (c : SourceChannelCode n 𝒱 α β) : ℝ :=
  ∑ v, ∑ y, if c.dec y ≠ v then P.law n v * channelExt W n (c.enc v) y else 0

omit [Fintype α] in
lemma SourceChannelCode.errProb_eq [Nonempty α] {n : ℕ} (P : StochasticProcess 𝒱)
    (W : α → β → ℝ) (c : SourceChannelCode n 𝒱 α β) :
    InfoTheory.errProb (fbLaw (P.law n) W (nfEnc c.enc) n) Prod.fst Prod.snd c.dec =
      c.errProb P W := by
  classical
  simp only [InfoTheory.errProb, SourceChannelCode.errProb, Fintype.sum_prod_type, fbLaw_nfEnc]

/-! ### The converse -/

/-- **Theorem 7.13.1 (converse), (7.143)–(7.150).** If a source can be sent over the channel with
probability of error `Pₑ^(n) → 0`, its entropy rate is at most the capacity: `H(𝒱) ≤ C`. -/
theorem entropyRate_le_capacity [Nonempty α] (P : StochasticProcess 𝒱) {W : α → β → ℝ}
    (hW : IsChannel W) (c : ∀ n, SourceChannelCode n 𝒱 α β)
    (hc : Tendsto (fun n => (c n).errProb P W) atTop (𝓝 0)) : P.entropyRate ≤ capacity W := by
  -- `n H(𝒱) ≤ H(Vⁿ) ≤ log 2 + Pₑ^(n) n log |𝒱| + nC`, by Fano's inequality and `I(Vⁿ; Yⁿ) ≤ nC`.
  have hbound : ∀ᶠ n : ℕ in atTop, P.entropyRate ≤
      log 2 / n + (c n).errProb P W * log (Fintype.card 𝒱) + capacity W := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := entropy_le_of_fbLaw (enc := nfEnc (β := β) (c n).enc) (P.isPMF n) hW (c n).dec
    rw [entropyRV, dist_fst_fbLaw hW, SourceChannelCode.errProb_eq, Fintype.card_fun,
      Fintype.card_fin, Nat.cast_pow, log_pow] at h1
    have h2 := P.mul_entropyRate_le_jointEntropy n
    rw [StochasticProcess.jointEntropy] at h2
    have key : n * P.entropyRate ≤
        n * (log 2 / n + (c n).errProb P W * log (Fintype.card 𝒱) + capacity W) := by
      rw [mul_add, mul_add, mul_div_cancel₀ _ hn'.ne']
      linarith
    exact le_of_mul_le_mul_left key hn'
  have hlim : Tendsto (fun n : ℕ => log 2 / n + (c n).errProb P W * log (Fintype.card 𝒱) +
      capacity W) atTop (𝓝 (capacity W)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (log 2)).add
      (hc.mul_const (log (Fintype.card 𝒱)))).add_const (capacity W)
    simpa using this
  exact ge_of_tendsto hlim hbound

/-! ### Random encoders -/

open Classical in
/-- The probability of error `Pr{V̂ⁿ ≠ Vⁿ}` of a source–channel code whose encoder is random: the
codeword of `vⁿ` is drawn from `q(xⁿ | vⁿ)`, and `g` is the decoder. -/
def randomErrProb {n : ℕ} (P : StochasticProcess 𝒱) (W : α → β → ℝ)
    (q : (Fin n → 𝒱) → (Fin n → α) → ℝ) (g : (Fin n → β) → Fin n → 𝒱) : ℝ :=
  ∑ v, ∑ x, ∑ y, if g y ≠ v then P.law n v * q v x * channelExt W n x y else 0

omit [Fintype α] in
lemma SourceChannelCode.errProb_nonneg {n : ℕ} (P : StochasticProcess 𝒱) {W : α → β → ℝ}
    (hW : IsChannel W) (c : SourceChannelCode n 𝒱 α β) : 0 ≤ c.errProb P W := by
  classical
  refine sum_nonneg fun v _ => sum_nonneg fun y _ => ?_
  split_ifs
  · exact mul_nonneg ((P.isPMF n).nonneg v) (channelExt_nonneg hW _ y)
  · exact le_rfl

open Classical in
/-- A random encoder can be derandomized: choosing for each `vⁿ` the codeword with the smallest
probability of error gives a deterministic encoder that is at least as good. -/
theorem exists_errProb_le_randomErrProb [Nonempty α] {n : ℕ} (P : StochasticProcess 𝒱)
    (W : α → β → ℝ) {q : (Fin n → 𝒱) → (Fin n → α) → ℝ} (hq : IsChannel q)
    (g : (Fin n → β) → Fin n → 𝒱) :
    ∃ c : SourceChannelCode n 𝒱 α β, c.dec = g ∧ c.errProb P W ≤ randomErrProb P W q g := by
  -- The probability of error of the codeword `xⁿ` for the source block `vⁿ`.
  set e : (Fin n → 𝒱) → (Fin n → α) → ℝ :=
    fun v x => ∑ y, if g y ≠ v then channelExt W n x y else 0
  have hmin := fun v => univ.exists_min_image (e v) univ_nonempty
  refine ⟨⟨fun v => (hmin v).choose, g⟩, rfl, ?_⟩
  have h1 : ∀ v, (∑ y, if g y ≠ v then P.law n v * channelExt W n (hmin v).choose y else 0) =
      P.law n v * e v (hmin v).choose := fun v => by
    simp only [e, mul_sum, mul_ite, mul_zero]
  have h2 : ∀ v, (∑ x, ∑ y, if g y ≠ v then P.law n v * q v x * channelExt W n x y else 0) =
      P.law n v * ∑ x, q v x * e v x := fun v => by
    simp only [e, mul_sum, mul_ite, mul_zero, mul_assoc]
  simp only [SourceChannelCode.errProb, randomErrProb, h1, h2]
  refine sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ ((P.isPMF n).nonneg v)
  calc e v (hmin v).choose = ∑ x, q v x * e v (hmin v).choose := by
        rw [← sum_mul, (hq v).sum_eq_one, one_mul]
    _ ≤ ∑ x, q v x * e v x := sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left ((hmin v).choose_spec.2 x (mem_univ x)) ((hq v).nonneg x)

/-- **Theorem 7.13.1 (converse) for random encoders.** If a source can be sent over the channel
with probability of error `Pₑ^(n) → 0` by codes whose encoders assign the codewords at random,
then `H(𝒱) ≤ C`. -/
theorem entropyRate_le_capacity_of_random [Nonempty α] (P : StochasticProcess 𝒱)
    {W : α → β → ℝ} (hW : IsChannel W) (q : ∀ n, (Fin n → 𝒱) → (Fin n → α) → ℝ)
    (hq : ∀ n, IsChannel (q n)) (g : ∀ n, (Fin n → β) → Fin n → 𝒱)
    (hc : Tendsto (fun n => randomErrProb P W (q n) (g n)) atTop (𝓝 0)) :
    P.entropyRate ≤ capacity W := by
  choose c _ hle using fun n => exists_errProb_le_randomErrProb P W (hq n) (g n)
  exact entropyRate_le_capacity P hW c (tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hc (fun n => (c n).errProb_nonneg P hW) hle)

/-! ### Achievability -/

/-- The consequence of the AEP used in the source–channel coding theorem: for every `ε > 0` there
are sets `A_ε^(n)` of source blocks with `|A_ε^(n)| ≤ e^{n(H+ε)}` for `n` large and
`Pr{A_ε^(n)} → 1`. -/
def StochasticProcess.HasTypicalSets (P : StochasticProcess 𝒱) (H : ℝ) : Prop :=
  ∀ ε > 0, ∃ A : ∀ n, Finset (Fin n → 𝒱),
    (∀ᶠ n : ℕ in atTop, ((A n).card : ℝ) ≤ exp (n * (H + ε))) ∧
      Tendsto (fun n => prob (P.law n) (A n)) atTop (𝓝 1)

/-- **Section 7.13.** An i.i.d. source satisfies the AEP: it has typical sets of size at most
`e^{n(H(X)+ε)}` and probability tending to `1` (Theorem 3.1.2). -/
theorem iidProcess_hasTypicalSets {p : 𝒱 → ℝ} (hp : IsPMF p) :
    (iidProcess p hp).HasTypicalSets (entropy p) := fun ε hε =>
  ⟨fun n => typicalSet p n ε, Eventually.of_forall fun n => card_typicalSet_le hp n ε,
    tendsto_prob_typicalSet hp hε⟩

open Classical in
/-- The two-stage source–channel code: index the typical set `A` into the messages of the channel
code `ch`, send the index, and decode the typical sequence with the received index. -/
def twoStageCode [Nonempty 𝒱] {n M : ℕ} (hM : 0 < M) (A : Finset (Fin n → 𝒱))
    (hA : A.card ≤ M) (ch : ChannelCode M n α β) : SourceChannelCode n 𝒱 α β :=
  let idx : (Fin n → 𝒱) → Fin M := fun v =>
    if hv : v ∈ A then Fin.castLE hA (A.equivFin ⟨v, hv⟩) else ⟨0, hM⟩
  { enc := fun v => ch.enc (idx v)
    dec := fun y => if h : ∃ v ∈ A, idx v = ch.dec y then h.choose else Classical.arbitrary _ }

omit [Fintype α] in
/-- **(7.138)–(7.139)** The two-stage code errs only if the source block is atypical or the channel
code errs: `Pₑ^(n) ≤ Pr{Vⁿ ∉ A} + λ^(n)`. -/
theorem errProb_twoStageCode_le [Nonempty 𝒱] {n M : ℕ} (P : StochasticProcess 𝒱)
    {W : α → β → ℝ} (hW : IsChannel W) (hM : 0 < M) (A : Finset (Fin n → 𝒱))
    (hA : A.card ≤ M) (ch : ChannelCode M n α β) :
    (twoStageCode hM A hA ch).errProb P W ≤ (1 - prob (P.law n) A) + ch.maxErrProb W := by
  classical
  have hP := P.isPMF n
  set c := twoStageCode hM A hA ch
  set idx : (Fin n → 𝒱) → Fin M := fun v =>
    if hv : v ∈ A then Fin.castLE hA (A.equivFin ⟨v, hv⟩) else ⟨0, hM⟩ with hidx
  have henc : ∀ v, c.enc v = ch.enc (idx v) := fun v => rfl
  -- On `A`, decoding the right index recovers the right source block.
  have hinj : ∀ v ∈ A, ∀ v' ∈ A, idx v = idx v' → v = v' := by
    intro v hv v' hv' h
    simp only [hidx, hv, hv', ↓reduceDIte] at h
    have := (A.equivFin).injective (Fin.castLE_injective hA h)
    exact congrArg Subtype.val this
  have hdec : ∀ v ∈ A, ∀ y, ch.dec y = idx v → c.dec y = v := by
    intro v hv y hy
    have h : ∃ v' ∈ A, idx v' = ch.dec y := ⟨v, hv, hy.symm⟩
    change (if h : ∃ v' ∈ A, idx v' = ch.dec y then h.choose else Classical.arbitrary _) = v
    split
    · next h' => exact hinj _ h'.choose_spec.1 _ hv (h'.choose_spec.2.trans hy)
    · next h' => exact absurd h h'
  -- Bound the error of each source block.
  have hterm : ∀ v, ∑ y, (if c.dec y ≠ v then P.law n v * channelExt W n (c.enc v) y else 0) ≤
      (if v ∈ A then 0 else P.law n v) + P.law n v * ch.maxErrProb W := by
    intro v
    by_cases hv : v ∈ A
    · simp only [hv, ↓reduceIte, zero_add]
      calc ∑ y, (if c.dec y ≠ v then P.law n v * channelExt W n (c.enc v) y else 0)
          ≤ ∑ y, P.law n v * (if ch.dec y ≠ idx v then channelExt W n (ch.enc (idx v)) y else 0) :=
            sum_le_sum fun y _ => by
              rw [henc]
              by_cases hy : ch.dec y = idx v
              · simp [hdec v hv y hy, hy]
              · simp only [hy, ne_eq, not_false_eq_true, ↓reduceIte]
                split_ifs <;> simp [mul_nonneg (hP.nonneg v) (channelExt_nonneg hW _ _)]
        _ = P.law n v * ch.condErrProb W (idx v) := by rw [← mul_sum]; rfl
        _ ≤ P.law n v * ch.maxErrProb W :=
            mul_le_mul_of_nonneg_left (ch.condErrProb_le_maxErrProb _) (hP.nonneg v)
    · simp only [hv, ↓reduceIte]
      have h1 : ∑ y, (if c.dec y ≠ v then P.law n v * channelExt W n (c.enc v) y else 0) ≤
          ∑ y, P.law n v * channelExt W n (c.enc v) y :=
        sum_le_sum fun y _ => by
          split_ifs <;> simp [mul_nonneg (hP.nonneg v) (channelExt_nonneg hW _ _)]
      rw [← mul_sum, ((hW.ext n) (c.enc v)).sum_eq_one, mul_one] at h1
      have h2 : 0 ≤ P.law n v * ch.maxErrProb W :=
        mul_nonneg (hP.nonneg v) (ch.maxErrProb_nonneg hW)
      linarith
  calc c.errProb P W ≤ ∑ v, ((if v ∈ A then 0 else P.law n v) + P.law n v * ch.maxErrProb W) :=
        sum_le_sum fun v _ => hterm v
    _ = (1 - prob (P.law n) A) + ch.maxErrProb W := by
        rw [sum_add_distrib, ← sum_mul, hP.sum_eq_one, one_mul]
        congr 1
        have h1 : ∑ v, (if v ∈ A then 0 else P.law n v) =
            ∑ v, P.law n v - ∑ v, (if v ∈ A then P.law n v else 0) := by
          rw [← sum_sub_distrib]
          exact sum_congr rfl fun v _ => by split_ifs <;> ring
        rw [h1, hP.sum_eq_one, ← sum_filter, filter_mem_eq_inter, univ_inter]
        rfl

/-- **Theorem 7.13.1 (achievability), (7.137)–(7.140).** If the source satisfies the AEP with
entropy rate `H` (it has typical sets of size about `e^{nH}`) and `H < C`, then there are
source–channel codes with probability of error `Pₑ^(n) → 0`. -/
theorem exists_sourceChannelCode [Nonempty α] [Nonempty 𝒱] {P : StochasticProcess 𝒱}
    {W : α → β → ℝ} (hW : IsChannel W) {H : ℝ} (hP : P.HasTypicalSets H)
    (hHC : H < capacity W) :
    ∃ c : ∀ n, SourceChannelCode n 𝒱 α β, Tendsto (fun n => (c n).errProb P W) atTop (𝓝 0) := by
  classical
  set ε := (capacity W - H) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set R := H + ε
  obtain ⟨ch, hch⟩ := isAchievableRate_of_lt_capacity hW (show R < capacity W by
    simp only [R, hε_def]; linarith)
  obtain ⟨A, hAcard, hAprob⟩ := hP ε hε
  -- For `n` large, `|A| ≤ e^{nR} ≤ ⌈e^{nR}⌉`, and the two-stage code is defined.
  have hM : ∀ n : ℕ, 0 < ⌈exp (n * R)⌉₊ := fun n => one_le_ceil_exp _
  let c : ∀ n, SourceChannelCode n 𝒱 α β := fun n =>
    if hA : (A n).card ≤ ⌈exp (n * R)⌉₊ then twoStageCode (hM n) (A n) hA (ch n)
    else ⟨fun _ _ => Classical.arbitrary α, fun _ _ => Classical.arbitrary 𝒱⟩
  refine ⟨c, ?_⟩
  have hle : ∀ᶠ n : ℕ in atTop,
      (c n).errProb P W ≤ (1 - prob (P.law n) (A n)) + (ch n).maxErrProb W := by
    filter_upwards [hAcard] with n hn
    have hA : (A n).card ≤ ⌈exp (n * R)⌉₊ := by
      have : ((A n).card : ℝ) ≤ ⌈exp (n * R)⌉₊ := hn.trans (Nat.le_ceil _)
      exact_mod_cast this
    simp only [c, hA, ↓reduceDIte]
    exact errProb_twoStageCode_le P hW (hM n) (A n) hA (ch n)
  have hnn : ∀ n, 0 ≤ (c n).errProb P W := fun n => by
    classical
    exact sum_nonneg fun v _ => sum_nonneg fun y _ => by
      split_ifs <;> simp [mul_nonneg ((P.isPMF n).nonneg v) (channelExt_nonneg hW _ _)]
  have hlim : Tendsto (fun n => (1 - prob (P.law n) (A n)) + (ch n).maxErrProb W) atTop (𝓝 0) := by
    simpa using (hAprob.const_sub 1).add hch
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall hnn) hle

end InfoTheory
