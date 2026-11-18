/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Converse
public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.Probability.WeakLaw

/-!
# The rate distortion theorem: achievability

Every pair `(R, D)` with `R > R^(I)(D)` is achievable. Fix a test channel `p(x̂|x)` with
`E d(X, X̂) ≤ D` and `I(X; X̂) < R`, and draw a codebook of `⌊e^{nR}⌋` codewords i.i.d. from the
induced law `p(x̂)`. The encoder sends the first codeword that is distortion typical with the
source sequence. A source sequence with no such codeword has probability at most
`Pr{(Xⁿ, X̂ⁿ) ∉ A_{d,ε}^(n)} + exp(-⌊e^{nR}⌋ e^{-n(I(X; X̂)+3ε)})` averaged over the codebooks,
which tends to `0`.

## Main definitions

* `distortionTypicalSet q d n ε`: the distortion typical set `A_{d,ε}^(n)`, (10.72)–(10.75).
* `typicalEncode`, `typicalRDCode`: encoding by distortion typicality.

## Main statements

* `tendsto_prob_distortionTypicalSet`: **Lemma 10.5.1**.
* `channelExt_mul_exp_le_iidPMF`: **Lemma 10.5.2**, `p(x̂ⁿ) ≥ p(x̂ⁿ | xⁿ) e^{-n(I(X; X̂)+3ε)}` on
  the distortion typical set.
* `one_sub_mul_pow_le`: **Lemma 10.5.3**, `(1 - xy)ⁿ ≤ 1 - x + e^{-yn}`.
* `sum_codebook_distortion_le`: (10.89)–(10.101), the distortion averaged over random codebooks.
* `isAchievableRD_of_infoRD_lt`: **Theorem 10.2.1 (achievability)**.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 10.5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### The distortion typical set -/

open Classical in
/-- **Definition (10.72)–(10.75).** The distortion typical set `A_{d,ε}^(n)`: the jointly typical
pairs `(xⁿ, x̂ⁿ)` whose distortion is within `ε` of `E d(X, X̂)`. As in `jointTypicalSet`, the
typicality bounds are non-strict. -/
def distortionTypicalSet (q : α × β → ℝ) (d : α → β → ℝ) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → α) × (Fin n → β)) :=
  (jointTypicalSet q n ε).filter fun z =>
    |seqDistortion d z.1 z.2 - expect q (fun w => d w.1 w.2)| < ε

lemma mem_distortionTypicalSet {q : α × β → ℝ} {d : α → β → ℝ} {n : ℕ} {ε : ℝ}
    {z : (Fin n → α) × (Fin n → β)} :
    z ∈ distortionTypicalSet q d n ε ↔ z ∈ jointTypicalSet q n ε ∧
      |seqDistortion d z.1 z.2 - expect q (fun w => d w.1 w.2)| < ε := by
  classical
  simp [distortionTypicalSet]

/-- **Lemma 10.5.1.** For i.i.d. pairs `(Xᵢ, X̂ᵢ) ∼ q`, `Pr{A_{d,ε}^(n)} → 1`: the pairs are
jointly typical with probability tending to `1`, and the distortion `d(Xⁿ, X̂ⁿ)` is close to its
mean by the weak law of large numbers. -/
theorem tendsto_prob_distortionTypicalSet {q : α × β → ℝ} (hq : IsPMF q) (d : α → β → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (jointIid q n) (distortionTypicalSet q d n ε)) atTop (𝓝 1) := by
  classical
  set E := expect q (fun w => d w.1 w.2)
  set bad := fun n : ℕ => univ.filter fun z : (Fin n → α) × (Fin n → β) =>
    ε ≤ |seqDistortion d z.1 z.2 - E|
  -- The distortion is atypical with probability tending to `0`.
  have hbad : Tendsto (fun n => prob (jointIid q n) (bad n)) atTop (𝓝 0) := by
    have hw := weak_law hq (fun w => d w.1 w.2) ε hε
    refine hw.congr fun n => ?_
    have h := sum_jointIid q n fun w => if ε ≤ |(sampleMean fun i => d (w i).1 (w i).2) - E|
      then 1 else 0
    simp only [mul_ite, mul_one, mul_zero] at h
    rw [prob, prob, sum_filter, sum_filter, ← h]
    refine sum_congr rfl fun z _ => ?_
    simp only [seqDistortion, sampleMean, zipSeq, Fintype.card_fin]
    exact if_congr Iff.rfl rfl rfl
  have hJ := tendsto_prob_jointTypicalSet hq hε
  have hle : ∀ n, prob (jointIid q n) (jointTypicalSet q n ε) - prob (jointIid q n) (bad n) ≤
      prob (jointIid q n) (distortionTypicalSet q d n ε) := by
    intro n
    have hsplit : prob (jointIid q n) (distortionTypicalSet q d n ε) +
        ∑ z ∈ (jointTypicalSet q n ε).filter
          (fun z => ¬|seqDistortion d z.1 z.2 - E| < ε), jointIid q n z =
        prob (jointIid q n) (jointTypicalSet q n ε) := by
      rw [prob, prob, distortionTypicalSet]
      exact sum_filter_add_sum_filter_not _ _ _
    have hsub : ∑ z ∈ (jointTypicalSet q n ε).filter
        (fun z => ¬|seqDistortion d z.1 z.2 - E| < ε), jointIid q n z ≤
        prob (jointIid q n) (bad n) := by
      refine sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
        fun z _ _ => jointIid_nonneg hq.nonneg n z
      simp only [mem_filter, not_lt] at hz
      simp [bad, hz.2]
    linarith
  have hle1 : ∀ n, prob (jointIid q n) (distortionTypicalSet q d n ε) ≤ 1 := fun n => by
    rw [← prob_univ (jointIid_isPMF hq n)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun z _ _ => jointIid_nonneg hq.nonneg n z
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hJ.sub hbad)
    tendsto_const_nhds hle hle1

/-! ### Lemmas 10.5.2 and 10.5.3 -/

variable {p : α → ℝ} {q : α → β → ℝ} {d : α → β → ℝ}

lemma expect_jointOf_distortion (p : α → ℝ) (q : α → β → ℝ) (d : α → β → ℝ) :
    expect (jointOf p q) (fun w => d w.1 w.2) = expDistortion p q d := by
  rw [expDistortion_eq_sum_jointOf, expect]
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- **Lemma 10.5.2.** For jointly typical `(xⁿ, x̂ⁿ)` with respect to `p(x) p(x̂|x)`,
`p(x̂ⁿ) ≥ p(x̂ⁿ | xⁿ) e^{-n(I(X; X̂)+3ε)}`. -/
theorem channelExt_mul_exp_le_iidPMF (hp : IsPMF p) (hq : IsChannel q) {n : ℕ} {ε : ℝ}
    {x : Fin n → α} {y : Fin n → β} (hxy : (x, y) ∈ jointTypicalSet (jointOf p q) n ε) :
    channelExt q n x y * exp (-(n * (mutualInfoOf p q + 3 * ε))) ≤
      iidPMF (outDist p q) n y := by
  obtain ⟨hx, hy, hz⟩ := mem_jointTypicalSet.1 hxy
  simp only [margFst, margSnd, dist_jointOf_fst hq, dist_jointOf_snd] at hx hy
  have hx1 := le_iidPMF_of_mem_typicalSet hx
  have hy1 := le_iidPMF_of_mem_typicalSet hy
  have hz2 := iidPMF_le_of_mem_typicalSet hz
  have hjoint : iidPMF (jointOf p q) n (zipSeq x y) = iidPMF p n x * channelExt q n x y :=
    jointIid_jointOf p q n (x, y)
  rw [hjoint] at hz2
  have hI : mutualInfoOf p q = entropy p + entropy (outDist p q) - entropy (jointOf p q) := by
    rw [mutualInfoOf, mutualInfo_fst_snd_eq (jointOf_isPMF hp hq), margFst, margSnd,
      dist_jointOf_fst hq, dist_jointOf_snd]
  have hA : 0 < iidPMF p n x := (exp_pos _).trans_le hx1
  have hC : 0 ≤ channelExt q n x y := channelExt_nonneg hq x y
  -- `p(x̂ⁿ | xⁿ) ≤ e^{-n(H(X,X̂)-ε)} / p(xⁿ) ≤ e^{-n(H(X,X̂)-ε)} e^{n(H(X)+ε)}`.
  have hC' : channelExt q n x y ≤
      exp (-(n * (entropy (jointOf p q) - ε))) * exp (n * (entropy p + ε)) := by
    have h1 : channelExt q n x y * exp (-(n * (entropy p + ε))) ≤
        exp (-(n * (entropy (jointOf p q) - ε))) :=
      (mul_le_mul_of_nonneg_left hx1 hC).trans (by rw [mul_comm]; exact hz2)
    calc channelExt q n x y = channelExt q n x y * exp (-(n * (entropy p + ε))) *
          exp (n * (entropy p + ε)) := by rw [mul_assoc, ← exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (exp_pos _).le
  calc channelExt q n x y * exp (-(n * (mutualInfoOf p q + 3 * ε)))
      ≤ exp (-(n * (entropy (jointOf p q) - ε))) * exp (n * (entropy p + ε)) *
          exp (-(n * (mutualInfoOf p q + 3 * ε))) :=
        mul_le_mul_of_nonneg_right hC' (exp_pos _).le
    _ = exp (-(n * (entropy (outDist p q) + ε))) := by
        rw [← exp_add, ← exp_add, hI]
        congr 1
        ring
    _ ≤ iidPMF (outDist p q) n y := hy1

/-- **Lemma 10.5.3.** For `0 ≤ x ≤ 1` and `y ≤ 1`, `(1 - xy)ⁿ ≤ 1 - x + e^{-yn}`: by convexity
of `t ↦ tⁿ`, `(1 - xy)ⁿ ≤ x (1 - y)ⁿ + (1 - x) ≤ x e^{-yn} + 1 - x`. -/
theorem one_sub_mul_pow_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (n : ℕ) : (1 - x * y) ^ n ≤ 1 - x + exp (-(y * n)) := by
  have hconv := (convexOn_pow n).2 (show 1 - y ∈ Set.Ici (0 : ℝ) from sub_nonneg.2 hy1)
    (Set.mem_Ici.2 zero_le_one) hx0 (sub_nonneg.2 hx1) (by ring)
  simp only [smul_eq_mul, one_pow, mul_one] at hconv
  have hexp : (1 - y) ^ n ≤ exp (-(y * n)) := by
    rw [show exp (-(y * n)) = exp (-y) ^ n by rw [← exp_nat_mul]; ring_nf]
    exact pow_le_pow_left₀ (sub_nonneg.2 hy1) (by linarith [add_one_le_exp (-y)]) n
  calc (1 - x * y) ^ n = (x * (1 - y) + (1 - x)) ^ n := by ring_nf
    _ ≤ x * (1 - y) ^ n + (1 - x) := hconv
    _ ≤ x * exp (-(y * n)) + (1 - x) := by gcongr
    _ ≤ 1 - x + exp (-(y * n)) := by nlinarith [exp_pos (-(y * n))]

/-! ### Random coding -/

open Classical in
/-- **Section 10.5, encoding.** Encode `xⁿ` by the least index `w` such that `(xⁿ, x̂ⁿ(w)) ∈ A`, or
by `w₀` if there is none. -/
def typicalEncode {n M : ℕ} (A : Finset ((Fin n → α) × (Fin n → β))) (C : Fin M → Fin n → β)
    (w₀ : Fin M) (x : Fin n → α) : Fin M :=
  if h : (univ.filter fun w => (x, C w) ∈ A).Nonempty then
    (univ.filter fun w => (x, C w) ∈ A).min' h
  else w₀

/-- The rate distortion code with codebook `C` (the decoder) and encoding by membership in `A`. -/
def typicalRDCode {n M : ℕ} (A : Finset ((Fin n → α) × (Fin n → β))) (C : Fin M → Fin n → β)
    (w₀ : Fin M) : RDCode M n α β :=
  ⟨typicalEncode A C w₀, C⟩

omit [Fintype α] [Fintype β] in
lemma typicalEncode_mem {n M : ℕ} {A : Finset ((Fin n → α) × (Fin n → β))}
    {C : Fin M → Fin n → β} (w₀ : Fin M) {x : Fin n → α} (h : ∃ w, (x, C w) ∈ A) :
    (x, C (typicalEncode A C w₀ x)) ∈ A := by
  classical
  have hne : (univ.filter fun w => (x, C w) ∈ A).Nonempty :=
    let ⟨w, hw⟩ := h
    ⟨w, by simp [hw]⟩
  simp only [typicalEncode, hne, ↓reduceDIte]
  simpa using min'_mem _ hne

open Classical in
omit [Fintype α] [Fintype β] in
/-- For a fixed codebook, the distortion of `xⁿ` is at most `D₀ + ε` if some codeword is in `A`
with `xⁿ`, and at most `d_max` otherwise. -/
lemma seqDistortion_typicalEncode_le [Finite α] [Finite β] {n M : ℕ} (hn : 0 < n)
    {A : Finset ((Fin n → α) × (Fin n → β))} {C : Fin M → Fin n → β} (w₀ : Fin M) {D₀ : ℝ}
    (hD₀ : 0 ≤ D₀) (hA : ∀ z ∈ A, seqDistortion d z.1 z.2 < D₀) (x : Fin n → α) :
    seqDistortion d x (C (typicalEncode A C w₀ x)) ≤
      D₀ + maxDistortion d * ∏ w, (if (x, C w) ∈ A then 0 else 1) := by
  classical
  by_cases h : ∃ w, (x, C w) ∈ A
  · obtain ⟨w, hw⟩ := h
    rw [prod_eq_zero (mem_univ w) (by simp [hw]), mul_zero, add_zero]
    exact (hA _ (typicalEncode_mem w₀ ⟨w, hw⟩)).le
  · push Not at h
    rw [prod_eq_one fun w _ => by simp [h w], mul_one]
    linarith [seqDistortion_le_maxDistortion d hn x (C (typicalEncode A C w₀ x))]

/-- **(10.89)–(10.101)** Averaged over random codebooks of `M` codewords drawn i.i.d. from the law
`p(x̂ⁿ)` induced by the test channel, the distortion of distortion typical encoding is at most
`E d(X, X̂) + ε + d_max (Pr{(Xⁿ, X̂ⁿ) ∉ A_{d,ε}^(n)} + exp(-M e^{-n(I(X; X̂)+3ε)}))`. -/
theorem sum_codebook_distortion_le [Nonempty β] (hp : IsPMF p) (hq : IsChannel q)
    (hd : ∀ x y, 0 ≤ d x y) {n M : ℕ} (hn : 0 < n) (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∑ C : Fin M → Fin n → β, iidPMF (iidPMF (outDist p q) n) M C *
        (typicalRDCode (distortionTypicalSet (jointOf p q) d n ε) C ⟨0, hM⟩).distortion p d ≤
      expDistortion p q d + ε + maxDistortion d *
        (1 - prob (jointIid (jointOf p q) n) (distortionTypicalSet (jointOf p q) d n ε) +
          exp (-(exp (-(n * (mutualInfoOf p q + 3 * ε))) * M))) := by
  classical
  have : Nonempty α := by
    obtain ⟨a, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hp)
    exact ⟨a⟩
  set A := distortionTypicalSet (jointOf p q) d n ε
  set r := outDist p q
  have hr : IsPMF r := outDist_isPMF hp hq
  have hrn : IsPMF (iidPMF r n) := iidPMF_isPMF hr n
  have hpn : IsPMF (iidPMF p n) := iidPMF_isPMF hp n
  set E := expDistortion p q d
  have hE : 0 ≤ E := sum_nonneg fun x _ => sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (hp.nonneg x) ((hq x).nonneg y)) (hd x y)
  set y := exp (-(n * (mutualInfoOf p q + 3 * ε)))
  have hy1 : y ≤ 1 := exp_le_one_iff.2 (by
    have := mutualInfoOf_nonneg hp hq
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith)
  have hdmax : 0 ≤ maxDistortion d := maxDistortion_nonneg hd
  set φ : (Fin n → α) → (Fin n → β) → ℝ := fun x z => if (x, z) ∈ A then 0 else 1
  -- The distortion of a fixed codebook.
  have hA : ∀ z ∈ A, seqDistortion d z.1 z.2 < E + ε := fun z hz => by
    have h := (mem_distortionTypicalSet.1 hz).2
    rw [expect_jointOf_distortion] at h
    linarith [(abs_lt.1 h).2]
  have hfix : ∀ C : Fin M → Fin n → β,
      (typicalRDCode A C ⟨0, hM⟩).distortion p d ≤
        E + ε + maxDistortion d * ∑ x, iidPMF p n x * ∏ w, φ x (C w) := fun C => by
    calc (typicalRDCode A C ⟨0, hM⟩).distortion p d
        ≤ ∑ x, iidPMF p n x * (E + ε + maxDistortion d * ∏ w, φ x (C w)) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (seqDistortion_typicalEncode_le hn _ (by linarith) hA x) (hpn.nonneg x)
      _ = E + ε + maxDistortion d * ∑ x, iidPMF p n x * ∏ w, φ x (C w) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hpn.sum_eq_one, one_mul, mul_sum]
          congr 1
          exact sum_congr rfl fun x _ => by ring
  -- Averaging over the codebooks: the codewords are independent.
  have havg : ∀ x, ∑ C : Fin M → Fin n → β, iidPMF (iidPMF r n) M C * ∏ w, φ x (C w) =
      (∑ z, iidPMF r n z * φ x z) ^ M := fun x => by
    rw [sum_iidPMF_mul_prod (iidPMF r n) fun _ z => φ x z, prod_const, card_univ,
      Fintype.card_fin]
  -- The probability that one codeword misses `xⁿ`, bounded with Lemmas 10.5.2 and 10.5.3.
  set K : (Fin n → α) → ℝ := fun x => ∑ z, channelExt q n x z * (if (x, z) ∈ A then 1 else 0)
  have hK0 : ∀ x, 0 ≤ K x := fun x => sum_nonneg fun z _ =>
    mul_nonneg (channelExt_nonneg hq x z) (by split_ifs <;> norm_num)
  have hK1 : ∀ x, K x ≤ 1 := fun x => by
    calc K x ≤ ∑ z, channelExt q n x z := sum_le_sum fun z _ => by
          split_ifs <;> simp [channelExt_nonneg hq x z]
      _ = 1 := ((hq.ext n) x).sum_eq_one
  have hmiss : ∀ x, (∑ z, iidPMF r n z * φ x z) ^ M ≤ 1 - K x + exp (-(y * M)) := by
    intro x
    have hsplit : ∑ z, iidPMF r n z * φ x z =
        1 - ∑ z, iidPMF r n z * (if (x, z) ∈ A then 1 else 0) := by
      rw [eq_sub_iff_add_eq, ← sum_add_distrib]
      refine (sum_congr rfl fun z _ => ?_).trans hrn.sum_eq_one
      simp only [φ]
      split_ifs <;> ring
    have hlow : y * K x ≤ ∑ z, iidPMF r n z * (if (x, z) ∈ A then 1 else 0) := by
      rw [mul_sum]
      refine sum_le_sum fun z _ => ?_
      split_ifs with hz
      · rw [mul_one, mul_one, mul_comm]
        exact channelExt_mul_exp_le_iidPMF hp hq (mem_distortionTypicalSet.1 hz).1
      · simp
    have h0 : 0 ≤ ∑ z, iidPMF r n z * φ x z :=
      sum_nonneg fun z _ => mul_nonneg (hrn.nonneg z) (by simp only [φ]; split_ifs <;> norm_num)
    calc (∑ z, iidPMF r n z * φ x z) ^ M ≤ (1 - K x * y) ^ M :=
          pow_le_pow_left₀ h0 (by linarith) M
      _ ≤ 1 - K x + exp (-(y * M)) := one_sub_mul_pow_le (hK0 x) (hK1 x) hy1 M
  have hprob : ∑ x, iidPMF p n x * K x = prob (jointIid (jointOf p q) n) A := by
    rw [prob, ← univ_inter A, ← sum_ite_mem, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    simp only [K, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [jointIid_jointOf]
    split_ifs <;> ring
  calc ∑ C : Fin M → Fin n → β, iidPMF (iidPMF r n) M C * (typicalRDCode A C ⟨0, hM⟩).distortion p d
      ≤ ∑ C : Fin M → Fin n → β, iidPMF (iidPMF r n) M C *
          (E + ε + maxDistortion d * ∑ x, iidPMF p n x * ∏ w, φ x (C w)) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hfix C)
          (iidPMF_nonneg hrn.nonneg C)
    _ = E + ε + maxDistortion d * ∑ x, iidPMF p n x *
          ∑ C : Fin M → Fin n → β, iidPMF (iidPMF r n) M C * ∏ w, φ x (C w) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, (iidPMF_isPMF hrn M).sum_eq_one,
          one_mul, mul_sum]
        congr 1
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_congr rfl fun C _ => by ring
    _ ≤ E + ε + maxDistortion d * ∑ x, iidPMF p n x * (1 - K x + exp (-(y * M))) := by
        gcongr with x
        · exact hpn.nonneg x
        · rw [havg x]; exact hmiss x
    _ = _ := by
        rw [← hprob]
        simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, ← sum_mul,
          hpn.sum_eq_one, one_mul]

/-! ### Theorem 10.2.1, achievability -/

omit [Fintype α] [Fintype β] in
lemma RDCode.ext_iff' {M n : ℕ} {c c' : RDCode M n α β} :
    c = c' ↔ c.enc = c'.enc ∧ c.dec = c'.dec := by
  cases c; cases c'; simp

omit [Fintype α] [Fintype β] in
instance RDCode.finite [Finite α] [Finite β] {M n : ℕ} : Finite (RDCode M n α β) :=
  Finite.of_injective (fun c : RDCode M n α β => (c.enc, c.dec)) fun c c' h => by
    simp only [Prod.mk.injEq] at h
    exact RDCode.ext_iff'.2 h

omit [Fintype β] in
/-- To show that `(R, D)` is achievable it is enough to find, for every `ε > 0` and all large `n`,
a `(⌊e^{nR}⌋, n)` code with distortion at most `D + ε`: the codes of least distortion then form a
sequence with `limsup E d(Xⁿ, X̂ⁿ) ≤ D`. -/
theorem isAchievableRD_of_eventually [Finite β] [Nonempty β] {R D : ℝ} (hR : 0 ≤ R)
    (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∃ c : RDCode ⌊exp (n * R)⌋₊ n α β, c.distortion p d ≤ D + ε) :
    IsAchievableRD p d R D := by
  have hM : ∀ n : ℕ, 0 < ⌊exp (n * R)⌋₊ := fun n =>
    Nat.floor_pos.2 (one_le_exp (by positivity))
  have hne : ∀ n : ℕ, Nonempty (RDCode ⌊exp (n * R)⌋₊ n α β) := fun n =>
    ⟨⟨fun _ => ⟨0, hM n⟩, fun _ _ => Classical.arbitrary β⟩⟩
  choose c hc using fun n => @Finite.exists_min _ _ _ (hne n) _
    fun c : RDCode ⌊exp (n * R)⌋₊ n α β => c.distortion p d
  exact ⟨c, fun ε hε => (h ε hε).mono fun n ⟨c', hc'⟩ => (hc n c').trans hc'⟩

/-- **Theorem 10.2.1 (achievability).** For a bounded distortion measure, every pair `(R, D)` with
`D ≥ D_min` and `R > R^(I)(D)` is achievable. -/
theorem isAchievableRD_of_infoRD_lt [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y)
    {R D : ℝ} (hD : minDistortion p d ≤ D) (hR : infoRD p d D < R) : IsAchievableRD p d R D := by
  obtain ⟨q, hq, hqD, hqI⟩ := exists_infoRD_eq hp hD
  set I := mutualInfoOf p q
  have hI0 : 0 ≤ I := mutualInfoOf_nonneg hp hq
  have hIR : I < R := hqI ▸ hR
  have hR0 : 0 < R := hI0.trans_lt hIR
  refine isAchievableRD_of_eventually hR0.le fun δ hδ => ?_
  set ε := min (δ / 2) ((R - I) / 4)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεR : 0 < R - (I + 3 * ε) := by
    have := min_le_right (δ / 2) ((R - I) / 4)
    linarith
  set M := fun n : ℕ => ⌊exp (n * R)⌋₊
  have hM : ∀ n, 0 < M n := fun n => Nat.floor_pos.2 (one_le_exp (by positivity))
  -- The excess distortion tends to `0`.
  have hexp : Tendsto (fun n : ℕ => exp (-(exp (-(n * (I + 3 * ε))) * M n))) atTop (𝓝 0) := by
    refine tendsto_exp_neg_atTop_nhds_zero.comp ?_
    have hlow : ∀ n : ℕ, exp (n * (R - (I + 3 * ε))) - 1 ≤ exp (-(n * (I + 3 * ε))) * M n := by
      intro n
      have hMn : exp (n * R) - 1 ≤ M n := (Nat.sub_one_lt_floor _).le
      have hy : exp (-(n * (I + 3 * ε))) ≤ 1 := exp_le_one_iff.2 (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith)
      calc exp (n * (R - (I + 3 * ε))) - 1
          ≤ exp (n * (R - (I + 3 * ε))) - exp (-(n * (I + 3 * ε))) := by linarith
        _ = exp (-(n * (I + 3 * ε))) * (exp (n * R) - 1) := by
            have : exp (n * (R - (I + 3 * ε))) = exp (-(n * (I + 3 * ε))) * exp (n * R) := by
              rw [← exp_add]; ring_nf
            rw [this]
            ring
        _ ≤ exp (-(n * (I + 3 * ε))) * M n := mul_le_mul_of_nonneg_left hMn (exp_pos _).le
    refine tendsto_atTop_mono hlow ?_
    have := (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hεR))
    exact tendsto_atTop_add_const_right _ (-1) this
  have hT := ((tendsto_prob_distortionTypicalSet (jointOf_isPMF hp hq) d hε).const_sub 1 |>.add
    hexp).const_mul (maxDistortion d)
  simp only [sub_self, add_zero, mul_zero] at hT
  filter_upwards [hT.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by linarith)),
    eventually_gt_atTop 0] with n hTn hn
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (iidPMF_isPMF (iidPMF_isPMF (outDist_isPMF hp hq) n) (M n))
    (sum_codebook_distortion_le hp hq hd hn (hM n) hε)
  exact ⟨_, hC.trans (by linarith)⟩

end InfoTheory
