/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.AverageError
public import InfoTheoryLib.MutualInformation.Convexity
public import InfoTheoryLib.Typicality.Basic

/-!
# Channel coding with cost

A nonnegative cost `b(x)` is associated with each input symbol of a discrete memoryless channel,
with `b(x₀) = 0` for some `x₀`, and every codeword must satisfy the cost constraint
`∑ᵢ b(xᵢ(m)) ≤ nB`. The capacity of the channel with cost constraint `B` is the capacity–cost
function `C(B) = max_{p(x) : E b(X) ≤ B} I(X; Y)`, which is nondecreasing, concave and continuous
in `B`.

## Main definitions

* `capacityCost W b B`: the capacity–cost function `C(B)`.
* `ChannelCode.SatisfiesCost c b B`: every codeword of `c` satisfies `∑ᵢ b(xᵢ(m)) ≤ nB`.
* `IsAchievableRateCost W b B R`, `opCapacityCost W b B`: achievable rates in bits, with the
  average probability of error, and the capacity with cost constraint `B`.

## Main statements

* `exists_capacityCost_eq`: the supremum defining `C(B)` is a maximum.
* `monotoneOn_capacityCost`, `concaveOn_capacityCost`, `continuousOn_capacityCost`: `C(B)` is
  nondecreasing and concave for `B ≥ 0`, hence continuous for `B > 0`.
* `continuousWithinAt_capacityCost`, `continuousOn_capacityCost_Ici`: `C(B)` is also continuous at
  the smallest cost.
* `ChannelCode.one_sub_avgErrProb_mul_log_le_capacityCost`: Fano's inequality and concavity give
  `(1 - P_e^(n)) log M ≤ log 2 + n C(B)` for every code satisfying the cost constraint.
* `isAchievableRateCost_of_lt`: achievability, by random coding.
* `opCapacityCost_eq`: **Theorem 2 of [elgamal2010], Lecture 3**, the capacity of the channel with
  cost constraint `B` is `C(B) / log 2` bits.

## Implementation notes

The notes generate the codewords i.i.d. from a pmf with `E b(X) ≤ B / (1 + ε)`, conditioned on
being typical, and use the continuity of `C(B)`. We instead draw the codewords i.i.d. from
`p = t p₁ + (1 - t) δ_{x₀}`, where `p₁` achieves `C(B)` and `t < 1`, decode with the pairs that
are jointly typical and whose codeword is robustly typical for `p`, and replace every codeword that
is not robustly typical by `x₀ⁿ`. Robustly typical codewords satisfy the cost constraint by the
typical average lemma, since `(1 + ε) E_p b(X) ≤ B` for `1 + ε = 1/t`; the replacement can only
change the probability of error of the default message of the decoder. By concavity
`I(p) ≥ t C(B)`, so this does not need the continuity of `C(B)` at `B = 0`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β] {W : α → β → ℝ} {b : α → ℝ}

/-! ### The capacity–cost function -/

/-- **Theorem 2 (Lecture 3 of [elgamal2010]).** The capacity–cost function
`C(B) = max_{p(x) : E b(X) ≤ B} I(X; Y)`. -/
def capacityCost (W : α → β → ℝ) (b : α → ℝ) (B : ℝ) : ℝ :=
  sSup {c | ∃ p, IsPMF p ∧ expect p b ≤ B ∧ mutualInfoOf p W = c}

lemma bddAbove_capacityCost (hW : IsChannel W) (b : α → ℝ) (B : ℝ) :
    BddAbove {c | ∃ p, IsPMF p ∧ expect p b ≤ B ∧ mutualInfoOf p W = c} :=
  ⟨log (Fintype.card β), fun _ ⟨_, hp, _, hc⟩ => hc ▸ mutualInfoOf_le_log_card_output hp hW⟩

lemma mutualInfoOf_le_capacityCost (hW : IsChannel W) {p : α → ℝ} (hp : IsPMF p) {B : ℝ}
    (hpB : expect p b ≤ B) : mutualInfoOf p W ≤ capacityCost W b B :=
  le_csSup (bddAbove_capacityCost hW b B) ⟨p, hp, hpB, rfl⟩

omit [Fintype β] in
lemma isPMF_pi_single [DecidableEq α] (x₀ : α) : IsPMF (Pi.single x₀ (1 : ℝ) : α → ℝ) :=
  ⟨fun x => by by_cases h : x = x₀ <;> simp [h], by simp⟩

omit [Fintype β] in
lemma expect_pi_single [DecidableEq α] (x₀ : α) (g : α → ℝ) :
    expect (Pi.single x₀ (1 : ℝ) : α → ℝ) g = g x₀ := by
  simp [expect, Pi.single_apply]

omit [Fintype β] in
lemma expect_mix (p₁ p₂ : α → ℝ) (s t : ℝ) (g : α → ℝ) :
    expect (s • p₁ + t • p₂) g = s * expect p₁ g + t * expect p₂ g := by
  simp only [expect, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

lemma capacityCost_set_nonempty (W : α → β → ℝ) {x₀ : α} {B : ℝ} (hB : b x₀ ≤ B) :
    {c | ∃ p, IsPMF p ∧ expect p b ≤ B ∧ mutualInfoOf p W = c}.Nonempty := by
  classical
  exact ⟨_, Pi.single x₀ 1, isPMF_pi_single x₀, by rwa [expect_pi_single], rfl⟩

/-- `C(B) ≥ 0`. -/
theorem capacityCost_nonneg (hW : IsChannel W) {x₀ : α} {B : ℝ} (hB : b x₀ ≤ B) :
    0 ≤ capacityCost W b B := by
  classical
  have hp := isPMF_pi_single x₀
  exact (mutualInfoOf_nonneg hp hW).trans
    (mutualInfoOf_le_capacityCost hW hp (by rwa [expect_pi_single]))

/-- `C(B) ≤ C`: a cost constraint can only lower the capacity. -/
theorem capacityCost_le_capacity (hW : IsChannel W) {x₀ : α} {B : ℝ} (hB : b x₀ ≤ B) :
    capacityCost W b B ≤ capacity W :=
  csSup_le (capacityCost_set_nonempty W hB) fun _ ⟨_, hp, _, hc⟩ =>
    hc ▸ mutualInfoOf_le_capacity hp hW

/-- The supremum defining `C(B)` is attained, since the set of input distributions with
`E b(X) ≤ B` is compact and `I(X; Y)` is continuous. -/
theorem exists_capacityCost_eq (hW : IsChannel W) {x₀ : α} {B : ℝ} (hB : b x₀ ≤ B) :
    ∃ p, IsPMF p ∧ expect p b ≤ B ∧ mutualInfoOf p W = capacityCost W b B := by
  classical
  have hcont : Continuous fun p : α → ℝ => expect p b :=
    continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_apply x)
  have hK : IsCompact ({p : α → ℝ | IsPMF p} ∩ {p | expect p b ≤ B}) :=
    isCompact_setOf_isPMF.inter_right (isClosed_le hcont continuous_const)
  obtain ⟨p, ⟨hp, hpB⟩, hmax⟩ := hK.exists_isMaxOn
    ⟨Pi.single x₀ 1, isPMF_pi_single x₀, by rwa [Set.mem_ofPred_eq, expect_pi_single]⟩
    ((continuousOn_mutualInfoOf hW).mono Set.inter_subset_left)
  refine ⟨p, hp, hpB, le_antisymm (mutualInfoOf_le_capacityCost hW hp hpB) ?_⟩
  exact csSup_le (capacityCost_set_nonempty W hB) fun _ ⟨q, hq, hqB, hc⟩ => hc ▸ hmax ⟨hq, hqB⟩

/-- **Lecture 3 of [elgamal2010].** `C(B)` is nondecreasing in `B`. -/
theorem monotoneOn_capacityCost (hW : IsChannel W) (x₀ : α) :
    MonotoneOn (capacityCost W b) (Set.Ici (b x₀)) := fun _ hB _ _ hBB =>
  csSup_le_csSup (bddAbove_capacityCost hW b _) (capacityCost_set_nonempty W hB)
    fun _ ⟨p, hp, hpB, hc⟩ => ⟨p, hp, hpB.trans hBB, hc⟩

/-- **Lecture 3 of [elgamal2010].** `C(B)` is concave in `B`: mixing input distributions mixes
their costs, and `I(X; Y)` is concave in `p(x)`. -/
theorem concaveOn_capacityCost (hW : IsChannel W) (x₀ : α) :
    ConcaveOn ℝ (Set.Ici (b x₀)) (capacityCost W b) := by
  refine ⟨convex_Ici _, fun B₁ hB₁ B₂ hB₂ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨_, ⟨p₁, hp₁, hpB₁, rfl⟩, h₁⟩ :=
    exists_lt_of_lt_csSup (capacityCost_set_nonempty W hB₁)
      (sub_lt_self (capacityCost W b B₁) hε)
  obtain ⟨_, ⟨p₂, hp₂, hpB₂, rfl⟩, h₂⟩ :=
    exists_lt_of_lt_csSup (capacityCost_set_nonempty W hB₂)
      (sub_lt_self (capacityCost W b B₂) hε)
  change capacityCost W b B₁ - ε < mutualInfoOf p₁ W at h₁
  change capacityCost W b B₂ - ε < mutualInfoOf p₂ W at h₂
  have hmix := hp₁.mix hp₂ hs ht hst
  have hcon := (mutualInfoOf_concave_input hW).2 hp₁ hp₂ hs ht hst
  simp only [smul_eq_mul] at hcon
  have hle := mutualInfoOf_le_capacityCost hW hmix (b := b) (B := s * B₁ + t * B₂) (by
    rw [expect_mix]
    exact add_le_add (mul_le_mul_of_nonneg_left hpB₁ hs) (mul_le_mul_of_nonneg_left hpB₂ ht))
  have e₁ := mul_le_mul_of_nonneg_left (by linarith : capacityCost W b B₁ ≤
    mutualInfoOf p₁ W + ε) hs
  have e₂ := mul_le_mul_of_nonneg_left (by linarith : capacityCost W b B₂ ≤
    mutualInfoOf p₂ W + ε) ht
  nlinarith

/-- **Lecture 3 of [elgamal2010].** `C(B)` is continuous for `B > b(x₀)`, as a concave
function. -/
theorem continuousOn_capacityCost (hW : IsChannel W) (x₀ : α) :
    ContinuousOn (capacityCost W b) (Set.Ioi (b x₀)) := by
  simpa using (concaveOn_capacityCost hW x₀).continuousOn_interior

/-- **Lecture 3 of [elgamal2010].** `C(B)` is continuous from the right at `B = b(x₀)`, in
particular at the smallest cost. For `ε > 0`, the laws with `I(X; Y) ≥ C(b(x₀)) + ε` form a compact
set, on which the cost has a minimum, and this minimum is larger than `b(x₀)`. -/
theorem continuousWithinAt_capacityCost (hW : IsChannel W) (x₀ : α) :
    ContinuousWithinAt (capacityCost W b) (Set.Ici (b x₀)) (b x₀) := by
  classical
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set C₀ := capacityCost W b (b x₀) with hC₀
  set K : Set (α → ℝ) := {p | IsPMF p} ∩ (fun p => mutualInfoOf p W) ⁻¹' Set.Ici (C₀ + ε) with hK
  have hKcl : IsClosed K := (continuousOn_mutualInfoOf hW).preimage_isClosed_of_isClosed
    isCompact_setOf_isPMF.isClosed isClosed_Ici
  have hKc : IsCompact K := isCompact_setOf_isPMF.of_isClosed_subset hKcl Set.inter_subset_left
  have hcont : Continuous fun p : α → ℝ => expect p b :=
    continuous_finsetSum _ fun x _ => continuous_const.mul (continuous_apply x)
  -- A threshold below which the value `C₀ + ε` is not reached.
  obtain ⟨δ, hδ, hlt⟩ : ∃ δ > 0, ∀ p ∈ K, b x₀ + δ ≤ expect p b := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp => by simp [he] at hp⟩
    · obtain ⟨p, hp, hmin⟩ := hKc.exists_isMinOn hne hcont.continuousOn
      refine ⟨expect p b - b x₀, ?_, fun q hq => by
        have := hmin hq
        simp only [Set.mem_ofPred_eq] at this
        linarith⟩
      by_contra hn
      have hle : expect p b ≤ b x₀ := by linarith
      have h1 := mutualInfoOf_le_capacityCost hW hp.1 hle
      have h2 : C₀ + ε ≤ mutualInfoOf p W := hp.2
      linarith
  refine ⟨δ, hδ, fun B hB hd => ?_⟩
  have hB' : b x₀ ≤ B := hB
  rw [Real.dist_eq, abs_of_nonneg (by linarith)] at hd
  have hmono : C₀ ≤ capacityCost W b B :=
    monotoneOn_capacityCost hW x₀ Set.self_mem_Ici hB hB'
  obtain ⟨p, hp, hpB, heq⟩ := exists_capacityCost_eq hW hB'
  have hup : capacityCost W b B < C₀ + ε := by
    by_contra hn
    push Not at hn
    have hmem : p ∈ K := ⟨hp, by
      change C₀ + ε ≤ mutualInfoOf p W
      rwa [heq]⟩
    have := hlt p hmem
    linarith
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-- **Lecture 3 of [elgamal2010].** `C(B)` is continuous for `B ≥ b(x₀)`. -/
theorem continuousOn_capacityCost_Ici (hW : IsChannel W) (x₀ : α) :
    ContinuousOn (capacityCost W b) (Set.Ici (b x₀)) := fun B hB => by
  rcases (show b x₀ ≤ B from hB).eq_or_lt with rfl | hlt
  · exact continuousWithinAt_capacityCost hW x₀
  · exact ((continuousOn_capacityCost hW x₀).continuousAt (Ioi_mem_nhds hlt)).continuousWithinAt

/-! ### Codes satisfying the cost constraint -/

/-- **Lecture 3 of [elgamal2010].** The cost constraint: every codeword satisfies
`∑ᵢ b(xᵢ(m)) ≤ nB`. -/
def ChannelCode.SatisfiesCost {M n : ℕ} (c : ChannelCode M n α β) (b : α → ℝ) (B : ℝ) : Prop :=
  ∀ m, ∑ i, b (c.enc m i) ≤ n * B

/-- **Lecture 3 of [elgamal2010].** A rate `R`, in bits per transmission, is achievable with cost
constraint `B` if there is a sequence of `(2^{nR}, n)` codes satisfying the cost constraint whose
average probability of error tends to `0`. -/
def IsAchievableRateCost (W : α → β → ℝ) (b : α → ℝ) (B R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, ChannelCode (2 ^ ⌈n * R⌉₊) n α β, (∀ n, (c n).SatisfiesCost b B) ∧
    Tendsto (fun n => (c n).avgErrProb W) atTop (𝓝 0)

/-- The capacity of the channel with cost constraint `B`, in bits: the supremum of the achievable
rates. -/
def opCapacityCost (W : α → β → ℝ) (b : α → ℝ) (B : ℝ) : ℝ :=
  sSup {R | IsAchievableRateCost W b B R}

/-! ### The converse -/

section Converse

variable {𝒲 : Type*} [Fintype 𝒲] {ν : 𝒲 → ℝ}

/-- Without feedback, `I(W; Yᵏ) ≤ ∑_{i ≤ k} I(Xᵢ; Yᵢ)`, where `Xᵢ = xᵢ(W)`. -/
theorem mutualInfo_fbLaw_nfEnc_le [Nonempty α] (hν : IsPMF ν) (hW : IsChannel W) {n : ℕ}
    (x : 𝒲 → Fin n → α) (k : ℕ) (hk : k ≤ n) :
    I[Prod.fst : Prod.snd ; fbLaw ν W (nfEnc x) k] ≤
      ∑ i : Fin k, mutualInfoOf (dist ν fun w => x w (Fin.castLE hk i)) W := by
  induction k with
  | zero => simpa using mutualInfo_fbLaw_le (enc := nfEnc x) hν hW 0
  | succ k ih =>
    have hkn : k < n := by omega
    have h1 := mutualInfo_fbLaw_succ_le_mutualInfoOf (enc := nfEnc x) hν hW k
    have h2 : dist (fbLaw ν W (nfEnc x) (k + 1)) (fun z => nfEnc x k z.1 (Fin.init z.2)) =
        dist ν fun w => x w ⟨k, hkn⟩ := by
      have : (fun z : 𝒲 × (Fin (k + 1) → β) => nfEnc x k z.1 (Fin.init z.2)) =
          (fun w => x w ⟨k, hkn⟩) ∘ Prod.fst := by
        funext z
        simp [nfEnc, hkn]
      rw [this, dist_comp_eq, dist_fst_fbLaw hW]
    rw [h2] at h1
    rw [Fin.sum_univ_castSucc]
    exact h1.trans (add_le_add_left (ih (by omega)) _)

/-- By Fano's inequality, `(1 - P_e^(n)) log M ≤ log 2 + ∑ᵢ I(Xᵢ; Yᵢ)`, where `Xᵢ = xᵢ(M)` for a
uniformly distributed message `M`. -/
theorem ChannelCode.one_sub_avgErrProb_mul_log_le_sum [Nonempty α] (hW : IsChannel W) {M n : ℕ}
    (hM : 0 < M) (c : ChannelCode M n α β) :
    (1 - c.avgErrProb W) * log M ≤
      log 2 + ∑ i, mutualInfoOf (dist (uniformPMF (Fin M)) fun m => c.enc m i) W := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hμ : IsPMF (c.jointLaw W) := fbLaw_isPMF uniformPMF_isPMF hW n
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ
    (Prod.fst : Fin M × (Fin n → β) → Fin M) Prod.snd
  have h2 := fano_weak hμ (Prod.fst : Fin M × (Fin n → β) → Fin M) Prod.snd c.dec
  rw [errProb_jointLaw, Fintype.card_fin] at h2
  rw [entropy_fst_jointLaw hW hM] at h1
  have h3 := mutualInfo_fbLaw_nfEnc_le (uniformPMF_isPMF (α := Fin M)) hW c.enc n le_rfl
  rw [← jointLaw] at h3
  have h5 : ∑ i : Fin n, mutualInfoOf (dist (uniformPMF (Fin M)) fun w =>
      c.enc w (Fin.castLE le_rfl i)) W =
      ∑ i : Fin n, mutualInfoOf (dist (uniformPMF (Fin M)) fun m => c.enc m i) W := rfl
  linarith

/-- **Converse of Theorem 2 (Lecture 3 of [elgamal2010]).** By Fano's inequality,
`log M ≤ log 2 + P_e^(n) log M + ∑ᵢ I(Xᵢ; Yᵢ)`, and
`∑ᵢ I(Xᵢ; Yᵢ) ≤ ∑ᵢ C(E b(Xᵢ)) ≤ n C((1/n) ∑ᵢ E b(Xᵢ)) ≤ n C(B)` by the definition of `C(B)`, its
concavity and its monotonicity. -/
theorem ChannelCode.one_sub_avgErrProb_mul_log_le_capacityCost (hW : IsChannel W)
    (hb : ∀ x, 0 ≤ b x) {x₀ : α} (hb0 : b x₀ = 0) {B : ℝ} (hB : 0 ≤ B) {M n : ℕ} (hM : 0 < M)
    (c : ChannelCode M n α β) (hc : c.SatisfiesCost b B) :
    (1 - c.avgErrProb W) * log M ≤ log 2 + n * capacityCost W b B := by
  have : Nonempty α := ⟨x₀⟩
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have h0 := c.one_sub_avgErrProb_mul_log_le_sum hW hM
  -- The input distributions `pᵢ` of `Xᵢ` and their costs `Bᵢ = E b(Xᵢ)`.
  set p : Fin n → α → ℝ := fun i => dist (uniformPMF (Fin M)) fun m => c.enc m (Fin.castLE le_rfl i)
  have hp : ∀ i, IsPMF (p i) := fun i => uniformPMF_isPMF.dist _
  set Bi : Fin n → ℝ := fun i => expect (p i) b
  have hBi : ∀ i, Bi i = ∑ m, 1 / M * b (c.enc m i) := fun i => by
    simp only [Bi, p, expect]
    simp_rw [mul_comm (b _)]
    rw [sum_dist_mul]
    simp [uniformPMF]
  have hBi0 : ∀ i, b x₀ ≤ Bi i := fun i => hb0 ▸ expect_nonneg (hp i).nonneg hb
  have hsum : ∑ i, Bi i ≤ n * B := by
    simp only [hBi]
    rw [sum_comm]
    calc ∑ m, ∑ i, 1 / (M : ℝ) * b (c.enc m i) ≤ ∑ _m : Fin M, 1 / (M : ℝ) * (n * B) :=
          sum_le_sum fun m _ => by
            rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left (hc m) (by positivity)
      _ = n * B := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have h4 : ∑ i : Fin n, mutualInfoOf (p i) W ≤ n * capacityCost W b B := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hJ := (concaveOn_capacityCost hW x₀).le_map_sum (t := univ) (w := fun _ => 1 / (n : ℝ))
      (p := Bi) (fun _ _ => by positivity) (by simp [hn'.ne']) fun i _ => hBi0 i
    simp only [smul_eq_mul, ← mul_sum] at hJ
    have hmono := monotoneOn_capacityCost hW x₀ (b := b)
      (show b x₀ ≤ 1 / n * ∑ i, Bi i by
        rw [hb0]
        exact mul_nonneg (by positivity) (sum_nonneg fun i _ => hb0 ▸ hBi0 i))
      (show b x₀ ≤ B by rw [hb0]; exact hB) (show 1 / n * ∑ i, Bi i ≤ B by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn', mul_comm]
        exact hsum)
    calc ∑ i, mutualInfoOf (p i) W ≤ ∑ i, capacityCost W b (Bi i) :=
          sum_le_sum fun i _ => mutualInfoOf_le_capacityCost hW (hp i) le_rfl
      _ = n * (1 / n * ∑ i, capacityCost W b (Bi i)) := by field_simp
      _ ≤ n * capacityCost W b B := mul_le_mul_of_nonneg_left (hJ.trans hmono) hn'.le
  have h5 : ∑ i : Fin n, mutualInfoOf (dist (uniformPMF (Fin M)) fun m => c.enc m i) W =
      ∑ i : Fin n, mutualInfoOf (p i) W := rfl
  linarith

end Converse

/-! ### Achievability -/

omit [Fintype α] in
/-- A single message is sent with the codeword `x₀ⁿ`, of cost `0`, and never in error. -/
lemma exists_code_satisfiesCost_avgErrProb_eq_zero (W : α → β → ℝ) {x₀ : α} (hb0 : b x₀ = 0)
    {B : ℝ} (hB : 0 ≤ B) {M : ℕ} (hM : M = 1) (n : ℕ) :
    ∃ c : ChannelCode M n α β, c.SatisfiesCost b B ∧ c.avgErrProb W = 0 := by
  subst hM
  refine ⟨⟨fun _ _ => x₀, fun _ => 0⟩, fun m => ?_, ?_⟩
  · simp only [hb0, sum_const_zero]
    positivity
  · have : ∀ i : Fin 1,
        (⟨fun _ _ => x₀, fun _ => 0⟩ : ChannelCode 1 n α β).condErrProb W i = 0 := fun i => by
      simp [ChannelCode.condErrProb, Subsingleton.elim i 0]
    simp [ChannelCode.avgErrProb, this]

omit [Fintype α] [Fintype β] in
/-- Joint typicality decoding outputs `w` only if `(xⁿ(w), yⁿ) ∈ A` or `w` is the default. -/
lemma typicalDecode_eq_imp {n M : ℕ} {A : Finset ((Fin n → α) × (Fin n → β))}
    {C : Fin M → Fin n → α} {w₀ : Fin M} {y : Fin n → β} {w : Fin M}
    (h : typicalDecode A C w₀ y = w) : (C w, y) ∈ A ∨ w = w₀ := by
  unfold typicalDecode at h
  split at h
  · next h' =>
    left
    rw [← h]
    exact h'.choose_spec.1
  · exact Or.inr h.symm

omit [Fintype α] in
open Classical in
/-- Replacing the codewords outside `T` by `x₀ⁿ`, and keeping the decoder, which uses only pairs
whose codeword is in `T`, increases the average probability of error by at most `1/M`: only the
default message of the decoder can be affected. -/
lemma avgErrProb_replace_le (hW : IsChannel W) {n M : ℕ} (hM : 0 < M)
    {A : Finset ((Fin n → α) × (Fin n → β))} {T : Finset (Fin n → α)}
    (hAT : ∀ z ∈ A, z.1 ∈ T) (C : Fin M → Fin n → α) (x₀ : α) :
    (⟨fun m => if C m ∈ T then C m else fun _ => x₀, typicalDecode A C ⟨0, hM⟩⟩ :
        ChannelCode M n α β).avgErrProb W ≤
      (typicalCode A C ⟨0, hM⟩).avgErrProb W + 1 / M := by
  classical
  set c' : ChannelCode M n α β :=
    ⟨fun m => if C m ∈ T then C m else fun _ => x₀, typicalDecode A C ⟨0, hM⟩⟩
  set c := typicalCode A C ⟨0, hM⟩
  have key : ∀ w, c'.condErrProb W w ≤ c.condErrProb W w + if w = ⟨0, hM⟩ then 1 else 0 := by
    intro w
    have h0 := c.condErrProb_nonneg hW w
    have h1 := c'.condErrProb_le_one hW w
    by_cases hT : C w ∈ T
    · have : c'.condErrProb W w = c.condErrProb W w := by
        simp [c', c, ChannelCode.condErrProb, typicalCode, hT]
      rw [this]
      by_cases hw : w = ⟨0, hM⟩ <;> simp [hw]
    · by_cases hw : w = ⟨0, hM⟩
      · simp only [hw, ite_true]
        rw [hw] at h0 h1
        linarith
      · have hne : ∀ y, ¬typicalDecode A C ⟨0, hM⟩ y = w := fun y h =>
          (typicalDecode_eq_imp h).elim (fun h' => hT (hAT _ h')) hw
        have hc : c.condErrProb W w = 1 := by
          simp only [c, ChannelCode.condErrProb, typicalCode, ne_eq, hne, not_false_eq_true,
            ite_true]
          exact ((hW.ext n) (C w)).sum_eq_one
        simp only [hc, hw, ite_false]
        linarith
  have hsum : ∑ w, c'.condErrProb W w ≤ ∑ w, c.condErrProb W w + 1 := by
    refine (sum_le_sum fun w _ => key w).trans ?_
    rw [sum_add_distrib, sum_ite_eq']
    simp
  simp only [ChannelCode.avgErrProb]
  rw [← add_div]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg M)

open Classical in
/-- The codewords drawn i.i.d. from `p` are robustly typical with probability tending to `1`:
`Pr{(Xⁿ, Yⁿ) ∈ A, Xⁿ ∉ T} ≤ 1 - Pr{Xⁿ ∈ T}`. -/
lemma prob_jointIid_filter_ge {p : α → ℝ} (hp : IsPMF p) (hW : IsChannel W) {n : ℕ}
    (A : Finset ((Fin n → α) × (Fin n → β))) (T : Finset (Fin n → α)) :
    prob (jointIid (jointOf p W) n) A - (1 - prob (iidPMF p n) T) ≤
      prob (jointIid (jointOf p W) n) (A.filter fun z => z.1 ∈ T) := by
  classical
  have hnn : ∀ z, 0 ≤ jointIid (jointOf p W) n z := fun z => by
    rw [jointIid_jointOf]
    exact mul_nonneg (iidPMF_nonneg hp.nonneg _) (channelExt_nonneg hW _ _)
  have hsplit := sum_filter_add_sum_filter_not A (fun z => z.1 ∈ T) (jointIid (jointOf p W) n)
  have hnot : ∑ z ∈ A.filter (fun z => z.1 ∉ T), jointIid (jointOf p W) n z ≤
      1 - prob (iidPMF p n) T := by
    calc ∑ z ∈ A.filter (fun z => z.1 ∉ T), jointIid (jointOf p W) n z
        ≤ ∑ z, if z.1 ∉ T then jointIid (jointOf p W) n z else 0 := by
          rw [← sum_filter]
          exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset_univ _))
            fun z _ _ => hnn z
      _ = ∑ x, if x ∉ T then iidPMF p n x else 0 := by
          rw [Fintype.sum_prod_type]
          refine sum_congr rfl fun x _ => ?_
          by_cases hx : x ∈ T
          · simp [hx]
          · simp only [hx, not_false_eq_true, ite_true, jointIid_jointOf, ← mul_sum,
              ((hW.ext n) x).sum_eq_one, mul_one]
      _ = prob (iidPMF p n) Tᶜ := by
          rw [prob, ← sum_filter]
          congr 1
          ext x
          simp
      _ = 1 - prob (iidPMF p n) T := prob_compl (iidPMF_isPMF hp n) T
  simp only [prob] at hsplit hnot ⊢
  linarith

lemma two_pow_ceil_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ 2 * exp (n * (R * log 2)) := by
  push_cast
  calc (2 : ℝ) ^ ⌈n * R⌉₊ = 2 ^ (⌈n * R⌉₊ : ℝ) := (rpow_natCast 2 _).symm
    _ ≤ 2 ^ (n * R + 1) := rpow_le_rpow_of_exponent_le one_le_two
        (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) hR)).le
    _ = 2 * exp (n * (R * log 2)) := by
        rw [rpow_def_of_pos two_pos, ← exp_log two_pos, ← exp_add, exp_log two_pos]
        congr 1
        ring

lemma exp_le_two_pow_ceil (n : ℕ) (R : ℝ) :
    exp (n * (R * log 2)) ≤ ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := by
  push_cast
  calc exp (n * (R * log 2)) = 2 ^ (n * R) := by
        rw [rpow_def_of_pos two_pos]
        congr 1
        ring
    _ ≤ 2 ^ (⌈n * R⌉₊ : ℝ) := rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
    _ = (2 : ℝ) ^ ⌈n * R⌉₊ := rpow_natCast 2 _

/-- **Achievability of Theorem 2 (Lecture 3 of [elgamal2010]).** Every rate below `C(B) / log 2`
bits is achievable with cost constraint `B`. -/
theorem isAchievableRateCost_of_lt (hW : IsChannel W) (hb : ∀ x, 0 ≤ b x) {x₀ : α}
    (hb0 : b x₀ = 0) {B : ℝ} (hB : 0 ≤ B) {R : ℝ} (hR : R < capacityCost W b B / log 2) :
    IsAchievableRateCost W b B R := by
  classical
  have hl := log_pos one_lt_two
  rcases le_or_gt R 0 with hR0 | hR0
  · -- With `R ≤ 0` there is a single message.
    have h1 : ∀ n : ℕ, 2 ^ ⌈n * R⌉₊ = 1 := fun n => by
      rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0), pow_zero]
    choose c hc using fun n : ℕ =>
      exists_code_satisfiesCost_avgErrProb_eq_zero W hb0 hB (h1 n) n
    exact ⟨c, fun n => (hc n).1, by simp [fun n => (hc n).2]⟩
  -- `p₁` achieves `C(B)`; draw the codewords from `p = t p₁ + (1 - t) δ_{x₀}` with `t < 1`.
  have hRC : R * log 2 < capacityCost W b B := (lt_div_iff₀ hl).1 hR
  have hRl : 0 < R * log 2 := mul_pos hR0 hl
  obtain ⟨p₁, hp₁, hp₁B, hp₁C⟩ :=
    exists_capacityCost_eq hW (b := b) (x₀ := x₀) (B := B) (by rw [hb0]; exact hB)
  set I₁ := mutualInfoOf p₁ W
  have hI₁ : R * log 2 < I₁ := by rw [hp₁C]; exact hRC
  have hI₁pos : 0 < I₁ := by linarith
  set t := (I₁ + R * log 2) / (2 * I₁) with ht_def
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht_def, div_lt_one (by positivity)]; linarith
  have htI : t * I₁ = (I₁ + R * log 2) / 2 := by rw [ht_def]; field_simp
  have hδx := isPMF_pi_single (α := α) x₀
  set p := t • p₁ + (1 - t) • (Pi.single x₀ 1 : α → ℝ)
  have hp : IsPMF p := hp₁.mix hδx ht0.le (by linarith) (by ring)
  have hpb : expect p b = t * expect p₁ b := by
    rw [expect_mix, expect_pi_single, hb0]
    ring
  have hIp : (I₁ + R * log 2) / 2 ≤ mutualInfoOf p W := by
    have := (mutualInfoOf_concave_input hW).2 hp₁ hδx ht0.le (by linarith : (0 : ℝ) ≤ 1 - t)
      (by ring)
    simp only [smul_eq_mul] at this
    have h0 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (mutualInfoOf_nonneg hδx hW (W := W))
    linarith
  -- Robustly typical codewords for `p` satisfy the cost constraint, with `1 + ε = 1/t`.
  set ε := 1 / t - 1 with hε_def
  have hε : 0 < ε := by rw [hε_def, sub_pos, one_lt_div ht0]; exact ht1
  have hεb : (1 + ε) * expect p b ≤ B := by
    rw [hpb, show 1 + ε = 1 / t by rw [hε_def]; ring]
    field_simp
    exact hp₁B
  set I := mutualInfoOf p W
  set δ := (I - R * log 2) / 4 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  set T := fun n : ℕ => robustTypicalSet p n ε
  set A := fun n : ℕ => (jointTypicalSet (jointOf p W) n δ).filter fun z => z.1 ∈ T n
  have hM : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  have hcode : ∀ n : ℕ, ∃ c : ChannelCode (2 ^ ⌈n * R⌉₊) n α β, c.SatisfiesCost b B ∧
      c.avgErrProb W ≤ (1 - prob (jointIid (jointOf p W) n) (A n)) +
        ((2 ^ ⌈n * R⌉₊ : ℕ) - 1) * exp (-(n * (I - 3 * δ))) + 1 / (2 ^ ⌈n * R⌉₊ : ℕ) := by
    intro n
    obtain ⟨C, hC⟩ := exists_codebook_avgErrProb_le_of_subset hp hW (hM n)
      (filter_subset _ _ : A n ⊆ _)
    refine ⟨⟨fun m => if C m ∈ T n then C m else fun _ => x₀,
      typicalDecode (A n) C ⟨0, hM n⟩⟩, fun m => ?_, ?_⟩
    · by_cases hm : C m ∈ T n
      · simp only [hm, ite_true]
        exact (sum_le_card_mul_of_mem_robustTypicalSet hm hb).trans
          (mul_le_mul_of_nonneg_left hεb (Nat.cast_nonneg n))
      · simp only [hm, ite_false, hb0, sum_const_zero]
        positivity
    · refine (avgErrProb_replace_le hW (hM n) (fun z hz => (mem_filter.1 hz).2) C x₀).trans ?_
      linarith
  choose c hc using hcode
  refine ⟨c, fun n => (hc n).1, ?_⟩
  -- The bound tends to `0`.
  have hbound : ∀ n : ℕ, (c n).avgErrProb W ≤
      ((1 - prob (jointIid (jointOf p W) n) (jointTypicalSet (jointOf p W) n δ)) +
        (1 - prob (iidPMF p n) (T n))) + 2 * exp (-(n * δ)) + exp (-(n * (R * log 2))) := by
    intro n
    have h1 := prob_jointIid_filter_ge hp hW (W := W) (jointTypicalSet (jointOf p W) n δ) (T n)
    have hMle := two_pow_ceil_le n hR0.le
    have hMge := exp_le_two_pow_ceil n R
    have hpos := exp_pos (n * (R * log 2))
    have h2 : (((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (I - 3 * δ))) ≤
        2 * exp (-(n * δ)) := by
      have hI3 : I - 3 * δ = R * log 2 + δ := by rw [hδ_def]; ring
      have hexp : exp (n * (R * log 2)) * exp (-(n * (I - 3 * δ))) = exp (-(n * δ)) := by
        rw [← exp_add, hI3]
        ring_nf
      calc (((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (I - 3 * δ)))
          ≤ (2 * exp (n * (R * log 2))) * exp (-(n * (I - 3 * δ))) :=
            mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
        _ = 2 * exp (-(n * δ)) := by rw [mul_assoc, hexp]
    have h3 : 1 / ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ exp (-(n * (R * log 2))) := by
      rw [exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hpos hMge
    have := hc n
    simp only [A] at this
    linarith [this.2]
  have hlim : Tendsto (fun n : ℕ =>
      ((1 - prob (jointIid (jointOf p W) n) (jointTypicalSet (jointOf p W) n δ)) +
        (1 - prob (iidPMF p n) (T n))) + 2 * exp (-(n * δ)) + exp (-(n * (R * log 2))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n =>
        1 - prob (jointIid (jointOf p W) n) (jointTypicalSet (jointOf p W) n δ)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_jointTypicalSet (jointOf_isPMF hp hW) hδ).const_sub 1
    have h2 : Tendsto (fun n => 1 - prob (iidPMF p n) (T n)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet hp hε).const_sub 1
    have h3 := (tendsto_exp_neg_mul_nat hδ).const_mul 2
    have h4 := tendsto_exp_neg_mul_nat hRl
    simpa using ((h1.add h2).add h3).add h4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (c n).avgErrProb_nonneg hW) hbound

/-! ### Theorem 2 -/

/-- **Converse of Theorem 2 (Lecture 3 of [elgamal2010]).** A rate that is achievable with cost
constraint `B` is at most `C(B) / log 2` bits. -/
theorem IsAchievableRateCost.le (hW : IsChannel W) (hb : ∀ x, 0 ≤ b x) {x₀ : α}
    (hb0 : b x₀ = 0) {B : ℝ} (hB : 0 ≤ B) {R : ℝ} (h : IsAchievableRateCost W b B R) :
    R ≤ capacityCost W b B / log 2 := by
  have : Nonempty α := ⟨x₀⟩
  obtain ⟨c, hcost, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  have h1 : ∀ n, (c n).avgErrProb W ≤ 1 := fun n =>
    (c n).avgErrProb_le_maxErrProb.trans
      (ChannelCode.maxErrProb_le _ (hpos n) fun i => (c n).condErrProb_le_one hW i)
  have key := le_of_converse_bound (R := R * log 2) (C := capacityCost W b B) hc h1 fun n _ => by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by linarith [h1 n]))
      ((c n).one_sub_avgErrProb_mul_log_le_capacityCost hW hb hb0 hB (hpos n) (hcost n))
    exact log_le_log (Nat.cast_pos.2 (Nat.ceil_pos.2 (exp_pos _)))
      (by exact_mod_cast ceil_exp_le_two_pow n R)
  rwa [le_div_iff₀ (log_pos one_lt_two)]

/-- **Theorem 2 (Lecture 3 of [elgamal2010]).** The capacity of the discrete memoryless channel
with cost constraint `B` is `C(B) = max_{p(x) : E b(X) ≤ B} I(X; Y)`, that is `C(B) / log 2`
bits. -/
theorem opCapacityCost_eq (hW : IsChannel W) (hb : ∀ x, 0 ≤ b x) {x₀ : α} (hb0 : b x₀ = 0)
    {B : ℝ} (hB : 0 ≤ B) : opCapacityCost W b B = capacityCost W b B / log 2 := by
  have hl := log_pos one_lt_two
  have hC := div_nonneg
    (capacityCost_nonneg hW (b := b) (x₀ := x₀) (B := B) (by rw [hb0]; exact hB)) hl.le
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨-1, isAchievableRateCost_of_lt hW hb hb0 hB (by linarith)⟩
    (fun R hR => hR.le hW hb hb0 hB) ?_
  intro w hw
  exact ⟨(w + capacityCost W b B / log 2) / 2,
    isAchievableRateCost_of_lt hW hb hb0 hB (by linarith), by linarith⟩

end InfoTheory
