/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.AsymptoticRate
public import InfoTheoryLib.RateDistortion.Normal
public import InfoTheoryLib.RateDistortion.Theorem

/-!
# Rate distortion theory with a probability of excess distortion

A pair `(R, D)` is achievable in probability if, for every `ε > 0` and `n` sufficiently large, some
code of block length `n` has rate at most `R + ε` and distortion larger than `D + ε` with
probability at most `ε`. This is the criterion of [yeung2008]; the library's `IsAchievableRD`
(Cover & Thomas) bounds the expected distortion instead. The achievable pairs are the same:
`(R, D)` is achievable iff `D ≥ D_min` and `R ≥ R^(I)(D)`.

## Main definitions

* `IsAchievableRDProb p d R D`: `(R, D)` is achievable in probability.
* `rdRegionProb p d`: the set of achievable pairs.
* `rateDistortionProb p d D`, `distortionRateProb p d R`: the rate-distortion and the
  distortion-rate functions.

## Main statements

* `sum_codebook_miss_distortionTypicalSet_le`: (8.156)–(8.182), the probability that no codeword of
  a random codebook is jointly typical with the source sequence.
* `isAchievableRDProb_of_expDistortion_le`: the achievability of `(I(X; X̂), D)`, (8.152)–(8.201).
* `IsAchievableRDProb.mem_epigraph`: the converse, (8.125)–(8.151).
* `isAchievableRDProb_iff`, `rdRegionProb_eq`: the rate-distortion region.
* `isClosed_rdRegionProb`, `convex_rdRegionProb`: Theorem 8.12.
* `rateDistortionProb_properties`: Theorem 8.15.
* `rateDistortionProb_eq_infoRD`: Theorem 8.17, `R(D) = R^(I)(D)`.
* `exists_eventually_prob_const_gt_le`: (8.18)–(8.19), a constant reproduction.

## Implementation notes

Rates are in nats. The achievability proof encodes by distortion typicality (`typicalRDCode`), as
the library's proof for the expected distortion, rather than by strong typicality as the book does.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 8.1 to 8.5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β] {p : α → ℝ} {d : α → β → ℝ}

/-! ### Achievability in probability -/

open Classical in
/-- **Definition 8.10.** `(R, D)` is asymptotically achievable if, for every `ε > 0` and `n`
sufficiently large, there is a code with `(1/n) log M ≤ R + ε` and
`Pr{d(X, X̂) > D + ε} ≤ ε`. -/
def IsAchievableRDProb (p : α → ℝ) (d : α → β → ℝ) (R D : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ M : ℕ, ∃ c : RDCode M n α β, codeRate M n ≤ R + ε ∧
    prob (iidPMF p n) (univ.filter fun x => D + ε < seqDistortion d x (c.dec (c.enc x))) ≤ ε

/-- **Definition 8.11.** The rate-distortion region, the set of achievable pairs `(R, D)`. -/
def rdRegionProb (p : α → ℝ) (d : α → β → ℝ) : Set (ℝ × ℝ) :=
  {z | IsAchievableRDProb p d z.1 z.2}

/-- **Definition 8.13.** The rate-distortion function `R(D)`, the least rate `R` with `(R, D)`
achievable. -/
def rateDistortionProb (p : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | IsAchievableRDProb p d R D}

/-- **Definition 8.14.** The distortion-rate function `D(R)`, the least distortion `D` with `(R, D)`
achievable. -/
def distortionRateProb (p : α → ℝ) (d : α → β → ℝ) (R : ℝ) : ℝ :=
  sInf {D | IsAchievableRDProb p d R D}

omit [Fintype β] in
/-- The remark after Definition 8.10: a larger rate or distortion is also achievable. -/
theorem IsAchievableRDProb.mono (hp : IsPMF p) {R D R' D' : ℝ} (h : IsAchievableRDProb p d R D)
    (hR : R ≤ R') (hD : D ≤ D') : IsAchievableRDProb p d R' D' := by
  classical
  intro ε hε
  filter_upwards [h ε hε] with n ⟨M, c, hr, hP⟩
  refine ⟨M, c, by linarith, le_trans (prob_mono (iidPMF_isPMF hp n).nonneg fun x hx => ?_) hP⟩
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  linarith

/-! ### Covering by a random codebook -/

open Classical in
/-- **(8.156)–(8.182)** Averaged over random codebooks of `M` codewords drawn i.i.d. from the law
`p(x̂ⁿ)` induced by the test channel, the probability that no codeword is distortion typical with
the source sequence is at most `Pr{(Xⁿ, X̂ⁿ) ∉ A} + exp(-M e^{-n(I(X; X̂) + 3ε)})`. -/
theorem sum_codebook_miss_distortionTypicalSet_le (hp : IsPMF p) {q : α → β → ℝ}
    (hq : IsChannel q) {n M : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∑ C : Fin M → Fin n → β, iidPMF (iidPMF (outDist p q) n) M C *
        ∑ x, iidPMF p n x *
          ∏ w, (if (x, C w) ∈ distortionTypicalSet (jointOf p q) d n ε then (0 : ℝ) else 1) ≤
      1 - prob (jointIid (jointOf p q) n) (distortionTypicalSet (jointOf p q) d n ε) +
        exp (-(exp (-(n * (mutualInfoOf p q + 3 * ε))) * M)) := by
  set A := distortionTypicalSet (jointOf p q) d n ε
  set r := outDist p q
  have hr : IsPMF r := outDist_isPMF hp hq
  have hrn : IsPMF (iidPMF r n) := iidPMF_isPMF hr n
  have hpn : IsPMF (iidPMF p n) := iidPMF_isPMF hp n
  set y := exp (-(n * (mutualInfoOf p q + 3 * ε)))
  have hy1 : y ≤ 1 := exp_le_one_iff.2 (by
    have := mutualInfoOf_nonneg hp hq
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith)
  set φ : (Fin n → α) → (Fin n → β) → ℝ := fun x z => if (x, z) ∈ A then 0 else 1
  have havg : ∀ x, ∑ C : Fin M → Fin n → β, iidPMF (iidPMF r n) M C * ∏ w, φ x (C w) =
      (∑ z, iidPMF r n z * φ x z) ^ M := fun x => by
    rw [sum_iidPMF_mul_prod (iidPMF r n) fun _ z => φ x z, prod_const, card_univ,
      Fintype.card_fin]
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
  calc ∑ C : Fin M → Fin n → β, iidPMF (iidPMF r n) M C * ∑ x, iidPMF p n x * ∏ w, φ x (C w)
      = ∑ x, iidPMF p n x * ∑ C : Fin M → Fin n → β, iidPMF (iidPMF r n) M C *
          ∏ w, φ x (C w) := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_congr rfl fun C _ => by ring
    _ ≤ ∑ x, iidPMF p n x * (1 - K x + exp (-(y * M))) := by
        gcongr with x
        · exact hpn.nonneg x
        · rw [havg x]; exact hmiss x
    _ = _ := by
        rw [← hprob]
        simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, ← sum_mul,
          hpn.sum_eq_one, one_mul]

open Classical in
omit [Fintype β] in
/-- With distortion typical encoding, a distortion of at least `D₀` only occurs when no codeword is
typical, if typical pairs have distortion below `D₀`. -/
lemma prob_ge_typicalRDCode_le (hp : IsPMF p) {n M : ℕ} {A : Finset ((Fin n → α) × (Fin n → β))}
    {C : Fin M → Fin n → β} (w₀ : Fin M) {D₀ : ℝ} (hA : ∀ z ∈ A, seqDistortion d z.1 z.2 < D₀) :
    prob (iidPMF p n) (univ.filter fun x =>
        D₀ ≤ seqDistortion d x ((typicalRDCode A C w₀).dec ((typicalRDCode A C w₀).enc x))) ≤
      ∑ x, iidPMF p n x * ∏ w, (if (x, C w) ∈ A then (0 : ℝ) else 1) := by
  rw [prob, sum_filter]
  refine sum_le_sum fun x _ => ?_
  split_ifs with h
  · by_cases hx : ∃ w, (x, C w) ∈ A
    · exact absurd h (not_le.2 (hA _ (typicalEncode_mem w₀ hx)))
    · push Not at hx
      rw [prod_eq_one fun w _ => by simp [hx w], mul_one]
  · exact mul_nonneg (iidPMF_nonneg hp.nonneg x) (prod_nonneg fun w _ => by
      split_ifs <;> norm_num)

/-- **(8.152)–(8.201)** For a test channel `p(x̂|x)` with `E d(X, X̂) ≤ D`, the pair `(I(X; X̂), D)`
is achievable. -/
theorem isAchievableRDProb_of_expDistortion_le (hp : IsPMF p)
    {q : α → β → ℝ} (hq : IsChannel q) {D : ℝ} (hqD : expDistortion p q d ≤ D) :
    IsAchievableRDProb p d (mutualInfoOf p q) D := by
  classical
  intro ε hε
  set I := mutualInfoOf p q
  have hI0 : 0 ≤ I := mutualInfoOf_nonneg hp hq
  set ε₁ := ε / 8 with hε₁_def
  have hε₁ : 0 < ε₁ := by positivity
  set R := I + ε / 2 with hR_def
  have hgap : 0 < R - (I + 3 * ε₁) := by rw [hR_def, hε₁_def]; linarith
  set M := fun n : ℕ => ⌊exp (n * R)⌋₊
  have hM : ∀ n, 0 < M n := fun n => Nat.floor_pos.2 (one_le_exp (by positivity))
  -- The probability of missing every codeword tends to `0`.
  have hexp : Tendsto (fun n : ℕ => exp (-(exp (-(n * (I + 3 * ε₁))) * M n))) atTop (𝓝 0) := by
    refine tendsto_exp_neg_atTop_nhds_zero.comp ?_
    have hlow : ∀ n : ℕ, exp (n * (R - (I + 3 * ε₁))) - 1 ≤ exp (-(n * (I + 3 * ε₁))) * M n := by
      intro n
      have hMn : exp (n * R) - 1 ≤ M n := (Nat.sub_one_lt_floor _).le
      have hy : exp (-(n * (I + 3 * ε₁))) ≤ 1 := exp_le_one_iff.2 (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith)
      calc exp (n * (R - (I + 3 * ε₁))) - 1
          ≤ exp (n * (R - (I + 3 * ε₁))) - exp (-(n * (I + 3 * ε₁))) := by linarith
        _ = exp (-(n * (I + 3 * ε₁))) * (exp (n * R) - 1) := by
            have : exp (n * (R - (I + 3 * ε₁))) = exp (-(n * (I + 3 * ε₁))) * exp (n * R) := by
              rw [← exp_add]; ring_nf
            rw [this]
            ring
        _ ≤ exp (-(n * (I + 3 * ε₁))) * M n := mul_le_mul_of_nonneg_left hMn (exp_pos _).le
    refine tendsto_atTop_mono hlow ?_
    have := (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hgap))
    exact tendsto_atTop_add_const_right _ (-1) this
  have hT : Tendsto (fun n : ℕ => 1 - prob (jointIid (jointOf p q) n)
      (distortionTypicalSet (jointOf p q) d n ε₁) + exp (-(exp (-(n * (I + 3 * ε₁))) * M n)))
      atTop (𝓝 0) := by
    have := ((tendsto_prob_distortionTypicalSet (jointOf_isPMF hp hq) d hε₁).const_sub 1).add hexp
    simpa using this
  filter_upwards [hT.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with n hTn hn
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le
    (iidPMF_isPMF (iidPMF_isPMF (outDist_isPMF hp hq) n) (M n))
    (sum_codebook_miss_distortionTypicalSet_le (d := d) hp hq (n := n) (M := M n) hε₁)
  set A := distortionTypicalSet (jointOf p q) d n ε₁
  have hA : ∀ z ∈ A, seqDistortion d z.1 z.2 < expDistortion p q d + ε₁ := fun z hz => by
    have h := (mem_distortionTypicalSet.1 hz).2
    rw [expect_jointOf_distortion] at h
    linarith [(abs_lt.1 h).2]
  refine ⟨M n, typicalRDCode A C ⟨0, hM n⟩, ?_, ?_⟩
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hMpos : (0 : ℝ) < M n := by exact_mod_cast hM n
    rw [codeRate, div_le_iff₀ hn']
    calc log (M n) ≤ log (exp (n * R)) := log_le_log hMpos (Nat.floor_le (exp_pos _).le)
      _ = n * R := log_exp _
      _ ≤ (I + ε) * n := by rw [hR_def]; nlinarith
  · refine le_trans (prob_mono (iidPMF_isPMF hp n).nonneg fun x hx => ?_)
      ((prob_ge_typicalRDCode_le hp ⟨0, hM n⟩ hA).trans (hC.trans hTn.le))
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    linarith

/-! ### The converse -/

/-- **(8.125)–(8.151)** If `(R, D)` is achievable, then `D ≥ D_min` and `R ≥ R^(I)(D)`. -/
theorem IsAchievableRDProb.mem_epigraph [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y)
    {R D : ℝ} (h : IsAchievableRDProb p d R D) : minDistortion p d ≤ D ∧ infoRD p d D ≤ R := by
  classical
  have : Nonempty α := by
    obtain ⟨a, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hp)
    exact ⟨a⟩
  set dm := maxDistortion d
  have hdm : 0 ≤ dm := maxDistortion_nonneg hd
  -- A negative distortion is never achieved.
  have hD0 : 0 ≤ D := by
    by_contra hneg
    push Not at hneg
    set ε := min (1 / 2) (-D / 2)
    have hε : 0 < ε := lt_min (by norm_num) (by linarith)
    have hε₁ : ε ≤ 1 / 2 := min_le_left _ _
    have hε₂ : ε ≤ -D / 2 := min_le_right _ _
    obtain ⟨n, M, c, -, hP⟩ := (h ε hε).exists
    have hall : (univ.filter fun x : Fin n → α =>
        D + ε < seqDistortion d x (c.dec (c.enc x))) = univ :=
      filter_true_of_mem fun x _ => by linarith [seqDistortion_nonneg hd x (c.dec (c.enc x))]
    rw [hall, prob_univ (iidPMF_isPMF hp n)] at hP
    linarith
  -- (8.141)–(8.147) for each `ε > 0`.
  have key : ∀ ε > 0, minDistortion p d ≤ D + (1 + dm) * ε ∧
      infoRD p d (D + (1 + dm) * ε) ≤ R + ε := by
    intro ε hε
    obtain ⟨n, ⟨M, c, hr, hP⟩, hn⟩ := ((h ε hε).and (eventually_gt_atTop 0)).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hμ := iidPMF_isPMF hp n
    -- (8.143)–(8.145): `E d(X, X̂) ≤ D + ε + d_max ε`.
    have hE : c.distortion p d ≤ D + (1 + dm) * ε := by
      have hpt : ∀ x, seqDistortion d x (c.dec (c.enc x)) ≤ (D + ε) +
          dm * (if D + ε < seqDistortion d x (c.dec (c.enc x)) then 1 else 0) := by
        intro x
        split_ifs with hx
        · linarith [seqDistortion_le_maxDistortion d hn x (c.dec (c.enc x))]
        · linarith
      calc c.distortion p d
          ≤ ∑ x, iidPMF p n x * ((D + ε) +
              dm * (if D + ε < seqDistortion d x (c.dec (c.enc x)) then 1 else 0)) :=
            sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hμ.nonneg x)
        _ = (D + ε) + dm * prob (iidPMF p n)
              (univ.filter fun x => D + ε < seqDistortion d x (c.dec (c.enc x))) := by
            rw [prob, sum_filter]
            simp only [mul_add, sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul, mul_sum]
            congr 1
            refine sum_congr rfl fun x _ => ?_
            split_ifs <;> ring
        _ ≤ D + (1 + dm) * ε := by nlinarith
    have hmin := RDCode.minDistortion_le_distortion hp hn c (d := d)
    have hlog := RDCode.mul_infoRD_le_log hp hn c (d := d)
    have hRI : infoRD p d (c.distortion p d) ≤ R + ε := by
      have : infoRD p d (c.distortion p d) ≤ codeRate M n := by
        rw [codeRate, le_div_iff₀ hn', mul_comm]
        exact hlog
      linarith
    exact ⟨hmin.trans hE, (infoRD_antitoneOn hp hmin (hmin.trans hE) hE).trans hRI⟩
  -- Let `ε → 0` in the closed epigraph of `R^(I)`.
  have hlim : Tendsto (fun k : ℕ => (R + 1 / ((k : ℝ) + 1), D + (1 + dm) * (1 / ((k : ℝ) + 1))))
      atTop (𝓝 (R, D)) := by
    have h₀ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h₁ := (tendsto_const_nhds (x := R)).add h₀
    have h₂ := (tendsto_const_nhds (x := D)).add (h₀.const_mul (1 + dm))
    simp only [add_zero, mul_zero] at h₁ h₂
    exact h₁.prodMk_nhds h₂
  have hmem := (isClosed_epigraph_infoRD (d := d) hp).mem_of_tendsto hlim
    (Eventually.of_forall fun k => key _ (by positivity))
  exact hmem

/-! ### The rate-distortion region and function -/

/-- **The rate-distortion region.** `(R, D)` is achievable iff `D ≥ D_min` and `R ≥ R^(I)(D)`. -/
theorem isAchievableRDProb_iff [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) {R D : ℝ} :
    IsAchievableRDProb p d R D ↔ minDistortion p d ≤ D ∧ infoRD p d D ≤ R := by
  refine ⟨IsAchievableRDProb.mem_epigraph hp hd, fun ⟨hD, hR⟩ => ?_⟩
  obtain ⟨q, hq, hqD, hqI⟩ := exists_infoRD_eq hp hD
  exact (isAchievableRDProb_of_expDistortion_le hp hq hqD).mono hp (by rw [hqI]; exact hR) le_rfl

lemma rdRegionProb_eq [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) :
    rdRegionProb p d = {z : ℝ × ℝ | minDistortion p d ≤ z.2 ∧ infoRD p d z.2 ≤ z.1} := by
  ext z
  exact isAchievableRDProb_iff hp hd

omit [Fintype β] in
/-- **Theorem 8.12 (closed).** The rate-distortion region is closed. -/
theorem isClosed_rdRegionProb [Finite β] [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) :
    IsClosed (rdRegionProb p d) := by
  have := Fintype.ofFinite β
  rw [rdRegionProb_eq hp hd]
  exact isClosed_epigraph_infoRD hp

omit [Fintype β] in
/-- **Theorem 8.12 (convex).** The rate-distortion region is convex. -/
theorem convex_rdRegionProb [Finite β] [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) :
    Convex ℝ (rdRegionProb p d) := by
  have := Fintype.ofFinite β
  rw [rdRegionProb_eq hp hd]
  have h := (infoRD_convexOn (d := d) hp).convex_epigraph
  convert h.linear_preimage ((LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.fst ℝ ℝ ℝ)) using 1
  ext z
  simp

/-- **Theorem 8.17 (The Rate-Distortion Theorem).** For `D ≥ D_min`, `R(D) = R^(I)(D)`, and the
minimum in Definition 8.13 is attained. -/
theorem rateDistortionProb_eq_infoRD [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y)
    {D : ℝ} (hD : minDistortion p d ≤ D) :
    rateDistortionProb p d D = infoRD p d D ∧ IsAchievableRDProb p d (infoRD p d D) D := by
  have h : {R | IsAchievableRDProb p d R D} = Set.Ici (infoRD p d D) := by
    ext R
    simp [isAchievableRDProb_iff hp hd, hD]
  refine ⟨?_, (isAchievableRDProb_iff hp hd).2 ⟨hD, le_rfl⟩⟩
  rw [rateDistortionProb, h, csInf_Ici]

omit [Fintype β] in
/-- **Theorem 8.15.** `R(D)` is nonincreasing and convex for `D ≥ D_min`, `R(D) = 0` for
`D ≥ D_max`, and `R(0) ≤ H(X)` for a normal distortion measure. -/
theorem rateDistortionProb_properties [Finite β] [Nonempty β] (hp : IsPMF p)
    (hd : ∀ x y, 0 ≤ d x y) :
    AntitoneOn (rateDistortionProb p d) (Set.Ici (minDistortion p d)) ∧
      ConvexOn ℝ (Set.Ici (minDistortion p d)) (rateDistortionProb p d) ∧
      (∀ D, dMax p d ≤ D → rateDistortionProb p d D = 0) ∧
      (IsNormalDistortion d → rateDistortionProb p d 0 ≤ entropy p) := by
  have := Fintype.ofFinite β
  have heq : Set.EqOn (infoRD p d) (rateDistortionProb p d) (Set.Ici (minDistortion p d)) :=
    fun D hD => (rateDistortionProb_eq_infoRD hp hd hD).1.symm
  refine ⟨fun a ha b hb hab => ?_, (infoRD_convexOn hp).congr heq, fun D hD => ?_, fun hn => ?_⟩
  · rw [← heq ha, ← heq hb]
    exact infoRD_antitoneOn hp ha hb hab
  · rw [← heq ((minDistortion_le_dMax hp).trans hD)]
    exact infoRD_eq_zero_of_dMax_le hp hD
  · have h0 : minDistortion p d = 0 := hn.minDistortion_eq_zero hd
    rw [← heq (show (0 : ℝ) ∈ Set.Ici (minDistortion p d) from h0.le)]
    exact infoRD_le_entropy hp hn

omit [Fintype β] in
/-- **(8.18)–(8.19)** The constant reproduction `(x̂*, …, x̂*)`, with `x̂*` the best constant
estimate, has `Pr{d(X, X̂) > D_max + ε} ≤ ε` for `n` sufficiently large, by the weak law of large
numbers. -/
theorem exists_eventually_prob_const_gt_le [Finite β] [Nonempty β] (hp : IsPMF p) :
    ∃ y₀ : β, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, prob (iidPMF p n)
      (univ.filter fun x => dMax p d + ε < seqDistortion d x fun _ => y₀) ≤ ε := by
  have := Fintype.ofFinite β
  classical
  obtain ⟨y₀, hy₀⟩ := exists_dMax_eq p d
  refine ⟨y₀, fun ε hε => ?_⟩
  have hlaw := weak_law hp (fun a => d a y₀) ε hε
  filter_upwards [hlaw.eventually (ge_mem_nhds hε)] with n hn
  refine le_trans (prob_mono (iidPMF_isPMF hp n).nonneg fun x hx => ?_) hn
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  have h₁ : seqDistortion d x (fun _ => y₀) = sampleMean fun i => d (x i) y₀ := by
    simp [seqDistortion, sampleMean]
  have h₂ : expect p (fun a => d a y₀) = dMax p d := by
    rw [← hy₀, expect]
    exact sum_congr rfl fun a _ => mul_comm _ _
  rw [h₁] at hx
  rw [h₂]
  exact le_abs.2 (Or.inl (by linarith))

end InfoTheory
