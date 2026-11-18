/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StateChannel.Multicoding

/-!
# The Gelfand–Pinsker coding scheme

With the state available noncausally at the encoder only, the Gelfand–Pinsker theorem says that the
capacity is `max_{p(u|s), x(u, s)} (I(U; Y) - I(U; S))`. This file defines the region and proves
achievability by multicoding: each message has a subcodebook of `2^{n(R̃ - R)}` sequences `uⁿ(l)`,
the encoder looks for one that is jointly typical with `sⁿ` and transmits `xᵢ = x(uᵢ(l), sᵢ)`, and
the decoder looks for a sequence that is jointly typical with `yⁿ`.

## Main definitions

* `gpSU p ρ`: the pmf `p(s) p(u | s)`; `gpChannel x W`: the channel
  `p(y | s, u) = p(y | x(u, s), s)`; `gpJoint p ρ x W`: the pmf of `((S, U), Y)`.
* `gpRate p ρ x W`: `I(U; Y) - I(U; S)`.
* `gpValue W p`: `max_{p(u|s), x(u, s)} (I(U; Y) - I(U; S))`, with `U` on `Fin k`.

## Main statements

* `exists_gp_code_le`: the random coding bound.
* `isAchievableStateRate_noncausal_false_of_lt`: **achievability in the Gelfand–Pinsker theorem**.
* `gpRate_le_stateKnownValue`: `I(U; Y) - I(U; S) ≤ max_{p(x|s)} I(X; Y | S)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {σ α β 𝒰 : Type*} [Fintype σ] [Fintype β] [Fintype 𝒰]

/-! ### The law of `(S, U, Y)` -/

/-- The pmf `p(s) p(u | s)` of `(S, U)`. -/
def gpSU (p : σ → ℝ) (ρ : σ → 𝒰 → ℝ) : σ × 𝒰 → ℝ := fun z => p z.1 * ρ z.1 z.2

/-- The channel `p(y | s, u) = p(y | x(u, s), s)`. -/
def gpChannel (x : 𝒰 → σ → α) (W : α × σ → β → ℝ) : σ × 𝒰 → β → ℝ := fun z => W (x z.2 z.1, z.1)

/-- The pmf of `((S, U), Y)`. -/
def gpJoint (p : σ → ℝ) (ρ : σ → 𝒰 → ℝ) (x : 𝒰 → σ → α) (W : α × σ → β → ℝ) :
    (σ × 𝒰) × β → ℝ :=
  jointOf (gpSU p ρ) (gpChannel x W)

/-- The pmf of `(Y, U)`. -/
def gpYU (p : σ → ℝ) (ρ : σ → 𝒰 → ℝ) (x : 𝒰 → σ → α) (W : α × σ → β → ℝ) : β × 𝒰 → ℝ :=
  dist (gpJoint p ρ x W) fun z => (z.2, z.1.2)

/-- `I(U; Y) - I(U; S)`. -/
def gpRate (p : σ → ℝ) (ρ : σ → 𝒰 → ℝ) (x : 𝒰 → σ → α) (W : α × σ → β → ℝ) : ℝ :=
  I[fun z : (σ × 𝒰) × β => z.1.2 : Prod.snd ; gpJoint p ρ x W] -
    I[fun z : (σ × 𝒰) × β => z.1.2 : fun z => z.1.1 ; gpJoint p ρ x W]

/-- **Gelfand–Pinsker theorem (Lecture 7 of [elgamal2010]).** The value
`max_{p(u|s), x(u, s)} (I(U; Y) - I(U; S))`, with `U` on `Fin k` for some `k`. -/
def gpValue (W : α × σ → β → ℝ) (p : σ → ℝ) : ℝ :=
  sSup {v | ∃ (k : ℕ) (ρ : σ → Fin k → ℝ) (x : Fin k → σ → α), (∀ s, IsPMF (ρ s)) ∧
    gpRate p ρ x W = v}

variable {p : σ → ℝ} {ρ : σ → 𝒰 → ℝ} {x : 𝒰 → σ → α} {W : α × σ → β → ℝ}

lemma gpSU_isPMF (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s)) : IsPMF (gpSU p ρ) := by
  refine ⟨fun z => mul_nonneg (hp.nonneg _) ((hρ _).nonneg _), ?_⟩
  simp only [gpSU, Fintype.sum_prod_type, ← mul_sum, (hρ _).sum_eq_one, mul_one, hp.sum_eq_one]

omit [Fintype σ] [Fintype 𝒰] in
lemma gpChannel_isChannel (hW : IsChannel W) (x : 𝒰 → σ → α) : IsChannel (gpChannel x W) :=
  fun _ => hW _

lemma gpJoint_isPMF (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s)) (hW : IsChannel W) :
    IsPMF (gpJoint p ρ x W) :=
  jointOf_isPMF (gpSU_isPMF hp hρ) (gpChannel_isChannel hW x)

lemma gpYU_isPMF (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s)) (hW : IsChannel W) :
    IsPMF (gpYU p ρ x W) :=
  (gpJoint_isPMF hp hρ hW).dist _

lemma margFst_gpJoint (hW : IsChannel W) : margFst (gpJoint p ρ x W) = gpSU p ρ :=
  dist_jointOf_fst (gpChannel_isChannel hW x)

lemma margFst_gpSU (hρ : ∀ s, IsPMF (ρ s)) : margFst (gpSU p ρ) = p := by
  funext s
  rw [margFst, dist_fst]
  simp [gpSU, ← mul_sum, (hρ _).sum_eq_one]

lemma margSnd_gpYU (hW : IsChannel W) : margSnd (gpYU p ρ x W) = margSnd (gpSU p ρ) := by
  rw [margSnd, gpYU, ← dist_comp_eq, margSnd, ← margFst_gpJoint hW (x := x), margFst,
    ← dist_comp_eq]
  rfl

/-- `I(U; Y)` in terms of the pmf of `(Y, U)`. -/
lemma mutualInfo_gpYU : I[Prod.snd : Prod.fst ; gpYU p ρ x W] =
    I[fun z : (σ × 𝒰) × β => z.1.2 : Prod.snd ; gpJoint p ρ x W] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [gpYU, ← dist_comp_eq]
  rfl

/-- `I(U; S)` in terms of the pmf of `(S, U)`. -/
lemma mutualInfo_gpSU (hW : IsChannel W) : I[Prod.snd : Prod.fst ; gpSU p ρ] =
    I[fun z : (σ × 𝒰) × β => z.1.2 : fun z => z.1.1 ; gpJoint p ρ x W] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [← margFst_gpJoint hW (x := x), margFst, ← dist_comp_eq]
  rfl

omit [Fintype σ] [Fintype β] [Fintype 𝒰] in
/-- The channel of a code is the channel from `(S, U)`. -/
lemma channelExt_gpChannel (x : 𝒰 → σ → α) (W : α × σ → β → ℝ) {n : ℕ} (s : Fin n → σ)
    (u : Fin n → 𝒰) (y : Fin n → β) :
    channelExt W n (zipSeq (fun i => x (u i) (s i)) s) y =
      channelExt (gpChannel x W) n (zipSeq s u) y := rfl

omit [Fintype σ] [Fintype 𝒰] in
/-- On the support of `(S, U)`, the conditional pmf of `Y` is the channel. -/
lemma condPMF_gpJoint [Finite σ] [Finite 𝒰] (hW : IsChannel W) {z : σ × 𝒰}
    (hz : gpSU p ρ z ≠ 0) (y : β) : condPMF (gpJoint p ρ x W) z y = gpChannel x W z y := by
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite 𝒰
  rw [condPMF, marg_eq_dist]
  have : dist (gpJoint p ρ x W) Prod.fst z = gpSU p ρ z := by
    have := margFst_gpJoint hW (p := p) (ρ := ρ) (x := x)
    exact congrFun this z
  rw [this]
  simp only [gpJoint, jointOf]
  field_simp

open Classical in
/-- For `(sⁿ, uⁿ)` typical, the output is jointly typical with `uⁿ` with probability at least
`1 - K/n`, by the conditional typicality lemma. -/
lemma sum_ite_not_mem_gpYU_le (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s)) (hW : IsChannel W) {n : ℕ}
    (hn : 0 < n) {ε' ε : ℝ} (hεε : ε' < ε) {s : Fin n → σ} {u : Fin n → 𝒰}
    (hsu : zipSeq s u ∈ robustTypicalSet (gpSU p ρ) n ε') :
    ∑ y, (if zipSeq y u ∉ robustTypicalSet (gpYU p ρ x W) n ε then
        channelExt (gpChannel x W) n (zipSeq s u) y else 0) ≤
      condTypicalityConst (gpJoint p ρ x W) ε' ε / n := by
  classical
  have hJ := gpJoint_isPMF (x := x) hp hρ hW
  have hsu' : zipSeq s u ∈ robustTypicalSet (margFst (gpJoint p ρ x W)) n ε' := by
    rwa [margFst_gpJoint hW]
  have h1 := one_sub_div_le_prob_condRobustTypicalSet hJ hεε hn hsu'
  have hext : ∀ y, channelExt (condPMF (gpJoint p ρ x W)) n (zipSeq s u) y =
      channelExt (gpChannel x W) n (zipSeq s u) y := fun y => by
    refine prod_congr rfl fun i _ => ?_
    exact condPMF_gpJoint hW
      (pos_of_mem_robustTypicalSet (gpSU_isPMF hp hρ).nonneg hsu i).ne' (y i)
  have h2 : prob (channelExt (condPMF (gpJoint p ρ x W)) n (zipSeq s u))
      (condRobustTypicalSet (gpJoint p ρ x W) ε (zipSeq s u)) ≤
      1 - ∑ y, (if zipSeq y u ∉ robustTypicalSet (gpYU p ρ x W) n ε then
        channelExt (gpChannel x W) n (zipSeq s u) y else 0) := by
    have hsum := ((gpChannel_isChannel hW x).ext n (zipSeq s u)).sum_eq_one
    have e : prob (channelExt (condPMF (gpJoint p ρ x W)) n (zipSeq s u))
        (condRobustTypicalSet (gpJoint p ρ x W) ε (zipSeq s u)) =
        ∑ y, if y ∈ condRobustTypicalSet (gpJoint p ρ x W) ε (zipSeq s u) then
          channelExt (gpChannel x W) n (zipSeq s u) y else 0 := by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, prob]
      exact sum_congr rfl fun y _ => hext y
    rw [e, ← hsum, le_sub_iff_add_le, ← sum_add_distrib]
    refine sum_le_sum fun y _ => ?_
    have hE := channelExt_nonneg (gpChannel_isChannel hW x) (zipSeq s u) y
    by_cases hy : y ∈ condRobustTypicalSet (gpJoint p ρ x W) ε (zipSeq s u)
    · have hT : zipSeq y u ∈ robustTypicalSet (gpYU p ρ x W) n ε :=
        comp_mem_robustTypicalSet (mem_condRobustTypicalSet.1 hy) fun z => (z.2, z.1.2)
      simp [hy, hT]
    · simp only [hy, ite_false, zero_add]
      split_ifs
      · exact hE
      · exact le_rfl
  linarith

/-! ### The random coding bound -/

open Classical in
/-- The encoder: the first sequence of the subcodebook that is jointly typical with `sⁿ`. -/
def gpEnc {n L : ℕ} (T : (Fin n → σ) → Finset (Fin n → 𝒰)) (hL : 0 < L) (D : Fin L → Fin n → 𝒰)
    (s : Fin n → σ) : Fin n → 𝒰 :=
  if h : ∃ l, D l ∈ T s then D h.choose else D ⟨0, hL⟩

open Classical in
/-- **Random coding for the Gelfand–Pinsker scheme.** With `L` sequences in each of the `M`
subcodebooks, there is a code with
`P_e^(n) ≤ K/n + e^{-La} + P{Sⁿ ∉ T_{ε''}} + M L e^{-n(I(U;Y)-δ)}`, where `a` bounds below the
probability that `Uⁿ` is typical with a typical `sⁿ`. -/
theorem exists_gp_code_le (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s)) (hW : IsChannel W) (x : 𝒰 → σ → α)
    {n M L : ℕ} (hn : 0 < n) (hM : 0 < M) (hL : 0 < L) {ε'' ε' ε a : ℝ} (hεε : ε' < ε)
    (ha : ∀ s ∈ robustTypicalSet p n ε'',
      a ≤ prob (iidPMF (margSnd (gpSU p ρ)) n) (condRobustTypicalSet (gpSU p ρ) ε' s)) :
    ∃ c : StateCode M n σ α β, c.Allowed .noncausal false ∧ c.errProb W p ≤
      condTypicalityConst (gpJoint p ρ x W) ε' ε / n + exp (-(L * a)) +
        (1 - prob (iidPMF p n) (robustTypicalSet p n ε'')) +
        M * (L * exp (-(n * (I[Prod.snd : Prod.fst ; gpYU p ρ x W] -
          ε * (H[Prod.snd ; gpYU p ρ x W] + H[Prod.snd | Prod.fst ; gpYU p ρ x W]))))) := by
  have hSU := gpSU_isPMF hp hρ
  have hU : IsPMF (margSnd (gpSU p ρ)) := hSU.dist _
  set μ := iidPMF (margSnd (gpSU p ρ)) n with hμ_def
  have hμ : IsPMF μ := iidPMF_isPMF hU n
  have hi := iidPMF_isPMF hp n
  have hYU : IsPMF (gpYU p ρ x W) := gpYU_isPMF hp hρ hW
  obtain ⟨A, hA⟩ : ∃ A : (Fin n → 𝒰) → (Fin n → β) → Prop, ∀ u y, A u y ↔
      zipSeq y u ∈ robustTypicalSet (gpYU p ρ x W) n ε := ⟨_, fun _ _ => Iff.rfl⟩
  set S : (Fin n → σ) → Finset (Fin n → 𝒰) := fun s => condRobustTypicalSet (gpSU p ρ) ε' s
  set η := exp (-(n * (I[Prod.snd : Prod.fst ; gpYU p ρ x W] -
    ε * (H[Prod.snd ; gpYU p ρ x W] + H[Prod.snd | Prod.fst ; gpYU p ρ x W]))))
  have hη : ∀ y, ∑ u, μ u * (if A u y then 1 else 0) ≤ η := fun y => by
    have := prob_iidPMF_condRobustTypicalSet_le hYU ε y
    rw [margSnd_gpYU hW] at this
    refine le_trans (le_of_eq ?_) this
    rw [prob]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    congr 1
    ext u
    simp [hA, mem_condRobustTypicalSet]
  set E : (Fin L → Fin n → 𝒰) → (Fin n → σ) → (Fin n → β) → ℝ := fun D s y =>
    channelExt (gpChannel x W) n (zipSeq s (gpEnc S hL D s)) y
  have hE0 : ∀ D s y, 0 ≤ E D s y := fun D s y => channelExt_nonneg (gpChannel_isChannel hW x) _ _
  have hE1 : ∀ D s, ∑ y, E D s y = 1 := fun D s =>
    ((gpChannel_isChannel hW x).ext n _).sum_eq_one
  set Q : (Fin L → Fin n → 𝒰) → (Fin n → β) → ℝ := fun D y => ∑ s, iidPMF p n s * E D s y
  have hQ0 : ∀ D y, 0 ≤ Q D y := fun D y =>
    sum_nonneg fun s _ => mul_nonneg (hi.nonneg s) (hE0 D s y)
  have hQ1 : ∀ D, ∑ y, Q D y ≤ 1 := fun D => le_of_eq (by
    simp only [Q]
    rw [sum_comm]
    simp only [← mul_sum, hE1, mul_one, hi.sum_eq_one])
  set m₀ : Fin M := ⟨0, hM⟩
  set code : (Fin M → Fin L → Fin n → 𝒰) → StateCode M n σ α β := fun C =>
    ⟨fun m s i => x (gpEnc S hL (C m) s i) (s i), fun _ y => subcodeDecode A C m₀ y⟩
  have hcond : ∀ C m, (code C).condErr W p m =
      ∑ y, if subcodeDecode A C m₀ y ≠ m then Q (C m) y else 0 := fun C m => by
    simp only [StateCode.condErr, code]
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    by_cases hy : subcodeDecode A C m₀ y ≠ m
    · simp only [hy, ne_eq, not_false_eq_true, ite_true]
      rfl
    · simp [hy]
  -- The probability that there is no typical sequence, or that the chosen one is not typical.
  have hinner : ∀ D s, ∑ y, (if ∀ l, ¬ A (D l) y then E D s y else 0) ≤
      condTypicalityConst (gpJoint p ρ x W) ε' ε / n +
        if ∀ l, D l ∉ S s then 1 else 0 := fun D s => by
    have hK : 0 ≤ condTypicalityConst (gpJoint p ρ x W) ε' ε / n := by
      refine div_nonneg (sum_nonneg fun z _ => ?_) (Nat.cast_nonneg n)
      positivity
    by_cases hs : ∀ l, D l ∉ S s
    · have e1 : (if ∀ l, D l ∉ S s then (1 : ℝ) else 0) = 1 := by
        split_ifs
        rfl
      rw [e1]
      have : ∑ y, (if ∀ l, ¬ A (D l) y then E D s y else 0) ≤ ∑ y, E D s y :=
        sum_le_sum fun y _ => by
          split_ifs
          · exact le_rfl
          · exact hE0 D s y
      rw [hE1] at this
      linarith
    · have hex : ∃ l, D l ∈ S s := by
        by_contra h
        exact hs fun l hl => h ⟨l, hl⟩
      have hu : gpEnc S hL D s = D hex.choose := by simp [gpEnc, hex]
      have hmem : zipSeq s (gpEnc S hL D s) ∈ robustTypicalSet (gpSU p ρ) n ε' := by
        rw [hu]
        exact mem_condRobustTypicalSet.1 hex.choose_spec
      have hb := sum_ite_not_mem_gpYU_le (x := x) hp hρ hW hn hεε hmem
      have e0 : (if ∀ l, D l ∉ S s then (1 : ℝ) else 0) = 0 := by
        split_ifs
        rfl
      rw [e0, add_zero]
      refine le_trans (sum_le_sum fun y _ => ?_) hb
      by_cases hAl : ∀ l, ¬ A (D l) y
      · have : zipSeq y (gpEnc S hL D s) ∉ robustTypicalSet (gpYU p ρ x W) n ε := by
          rw [hu, ← hA]
          exact hAl _
        simp only [hAl, implies_true, ite_true, this, not_false_eq_true]
        exact le_rfl
      · have e1 : (if ∀ l, ¬ A (D l) y then E D s y else 0) = 0 := by
          split_ifs
          rfl
        rw [e1]
        split_ifs
        · exact le_rfl
        · exact hE0 D s y
  have hfirst : ∑ D : Fin L → Fin n → 𝒰, iidPMF μ L D *
        ∑ y, (if ∀ l, ¬ A (D l) y then Q D y else 0) ≤
      condTypicalityConst (gpJoint p ρ x W) ε' ε / n + exp (-(L * a)) +
        (1 - prob (iidPMF p n) (robustTypicalSet p n ε'')) := by
    set K := condTypicalityConst (gpJoint p ρ x W) ε' ε / n
    have hν := iidPMF_isPMF hμ L
    have hswap : ∀ D : Fin L → Fin n → 𝒰, ∑ y, (if ∀ l, ¬ A (D l) y then Q D y else 0) =
        ∑ s, iidPMF p n s * ∑ y, (if ∀ l, ¬ A (D l) y then E D s y else 0) := fun D => by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      by_cases hAl : ∀ l, ¬ A (D l) y
      · have e1 : ∀ s, (if ∀ l, ¬ A (D l) y then E D s y else 0) = E D s y := fun s => by
          split_ifs
          rfl
        have e2 : (if ∀ l, ¬ A (D l) y then Q D y else 0) = Q D y := by
          split_ifs
          rfl
        simp only [e1, e2, Q]
      · have e1 : ∀ s, (if ∀ l, ¬ A (D l) y then E D s y else 0) = 0 := fun s => by
          split_ifs
          rfl
        have e2 : (if ∀ l, ¬ A (D l) y then Q D y else 0) = 0 := by
          split_ifs
          rfl
        simp [e1, e2]
    have hstep : ∀ D : Fin L → Fin n → 𝒰, ∑ y, (if ∀ l, ¬ A (D l) y then Q D y else 0) ≤
        K + ∑ s, iidPMF p n s * (if ∀ l, D l ∉ S s then 1 else 0) := fun D => by
      rw [hswap]
      refine (sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hinner D s) (hi.nonneg s)).trans ?_
      simp_rw [mul_add]
      rw [sum_add_distrib, ← sum_mul, hi.sum_eq_one, one_mul]
    have hmiss : ∀ s, ∑ D : Fin L → Fin n → 𝒰, iidPMF μ L D * (if ∀ l, D l ∉ S s then 1 else 0) ≤
        exp (-(L * a)) + if s ∉ robustTypicalSet p n ε'' then 1 else 0 := fun s => by
      refine (le_trans (le_of_eq (by congr!))
        (sum_iidPMF_ite_forall_not_mem_le hμ L (S s))).trans ?_
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      by_cases hs : s ∈ robustTypicalSet p n ε''
      · simp only [hs, not_true_eq_false, ite_false, add_zero]
        exact exp_le_exp.2 (by nlinarith [ha s hs])
      · simp only [hs, not_false_eq_true, ite_true]
        have h1 : exp (-(L * prob μ (S s))) ≤ 1 := by
          rw [exp_le_one_iff]
          have := mul_nonneg hL0 (prob_nonneg hμ.nonneg (S s))
          linarith
        linarith [exp_pos (-(L * a))]
    have hcompl : ∑ s, iidPMF p n s * (if s ∉ robustTypicalSet p n ε'' then 1 else 0) =
        1 - prob (iidPMF p n) (robustTypicalSet p n ε'') := by
      rw [← prob_compl hi, prob]
      simp only [mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      congr 1
      ext s
      simp
    calc ∑ D : Fin L → Fin n → 𝒰, iidPMF μ L D * ∑ y, (if ∀ l, ¬ A (D l) y then Q D y else 0)
        ≤ ∑ D : Fin L → Fin n → 𝒰, iidPMF μ L D *
            (K + ∑ s, iidPMF p n s * (if ∀ l, D l ∉ S s then 1 else 0)) :=
          sum_le_sum fun D _ => mul_le_mul_of_nonneg_left (hstep D) (hν.nonneg D)
      _ = K + ∑ s, iidPMF p n s * ∑ D : Fin L → Fin n → 𝒰, iidPMF μ L D *
            (if ∀ l, D l ∉ S s then 1 else 0) := by
          simp_rw [mul_add]
          rw [sum_add_distrib, ← sum_mul, hν.sum_eq_one, one_mul]
          congr 1
          simp_rw [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ ≤ K + ∑ s, iidPMF p n s * (exp (-(L * a)) +
            if s ∉ robustTypicalSet p n ε'' then 1 else 0) :=
          add_le_add le_rfl (sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left (hmiss s) (hi.nonneg s))
      _ = _ := by
          simp_rw [mul_add]
          rw [sum_add_distrib, ← sum_mul, hi.sum_eq_one, one_mul, hcompl]
          ring
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set F := condTypicalityConst (gpJoint p ρ x W) ε' ε / n + exp (-(L * a)) +
    (1 - prob (iidPMF p n) (robustTypicalSet p n ε''))
  have hν := iidPMF_isPMF hμ L
  have hC := iidPMF_isPMF hν M
  have hm : ∀ m : Fin M, ∑ C, iidPMF (iidPMF μ L) M C * (code C).condErr W p m ≤
      F + M * (L * η) := fun m => by
    simp_rw [hcond]
    exact (sum_codebook_subcode_le hμ m₀ A Q hQ0 hQ1 (exp_pos _).le hη m).trans
      (add_le_add hfirst le_rfl)
  have htotal : ∑ C, iidPMF (iidPMF μ L) M C * (code C).errProb W p ≤ F + M * (L * η) := by
    calc ∑ C, iidPMF (iidPMF μ L) M C * (code C).errProb W p
        = (∑ m, ∑ C, iidPMF (iidPMF μ L) M C * (code C).condErr W p m) / M := by
          simp only [StateCode.errProb]
          rw [sum_comm, sum_div]
          refine sum_congr rfl fun C _ => ?_
          rw [mul_div_assoc', mul_sum]
      _ ≤ (∑ _m : Fin M, (F + M * (L * η))) / M :=
          div_le_div_of_nonneg_right (sum_le_sum fun m _ => hm m) hM'.le
      _ = F + M * (L * η) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  obtain ⟨C, hCb⟩ := exists_le_of_sum_mul_le hC htotal
  exact ⟨code C, ⟨trivial, fun _ _ _ _ => rfl⟩, hCb⟩

/-! ### Achievability -/

omit [Fintype 𝒰] in
/-- A single message is never in error. -/
lemma StateCode.errProb_single {M n : ℕ} (hM : M = 1) (x₀ : α)
    (d : (Fin n → σ) → (Fin n → β) → Fin M) (W : α × σ → β → ℝ) (p : σ → ℝ) :
    (⟨fun _ _ _ => x₀, d⟩ : StateCode M n σ α β).errProb W p = 0 := by
  subst hM
  have : ∀ m : Fin 1, (⟨fun _ _ _ => x₀, d⟩ : StateCode 1 n σ α β).condErr W p m = 0 := fun m => by
    simp [StateCode.condErr, Subsingleton.elim (d _ _) m]
  simp [StateCode.errProb, this]

/-- **Achievability in the Gelfand–Pinsker theorem (Lecture 7 of [elgamal2010]).** For every
`p(u | s)` and `x(u, s)`, every rate below `I(U; Y) - I(U; S)` is achievable with the state
available noncausally at the encoder. -/
theorem isAchievableStateRate_noncausal_false_of_lt [Nonempty α] (hp : IsPMF p)
    (hρ : ∀ s, IsPMF (ρ s)) (hW : IsChannel W) (x : 𝒰 → σ → α) {R : ℝ}
    (hR : R < gpRate p ρ x W / log 2) : IsAchievableStateRate W p .noncausal false R := by
  classical
  have hl := log_pos one_lt_two
  obtain ⟨x₀⟩ := ‹Nonempty α›
  have hRp : R * log 2 < gpRate p ρ x W := (lt_div_iff₀ hl).1 hR
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  rcases le_or_gt R 0 with hR0 | hR0
  · have h1 : ∀ n : ℕ, 2 ^ ⌈n * R⌉₊ = 1 := fun n => by
      rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0), pow_zero]
    refine ⟨fun n => ⟨fun _ _ _ => x₀, fun _ _ => ⟨0, hpos n⟩⟩, fun n => ⟨trivial,
      fun _ _ _ _ => rfl⟩, ?_⟩
    exact tendsto_const_nhds.congr fun n => (StateCode.errProb_single (h1 n) x₀ _ W p).symm
  have hSU := gpSU_isPMF hp hρ
  have hYU : IsPMF (gpYU p ρ x W) := gpYU_isPMF hp hρ hW
  set IY := I[Prod.snd : Prod.fst ; gpYU p ρ x W] with hIY
  set IS := I[Prod.snd : Prod.fst ; gpSU p ρ] with hIS
  have hrate : gpRate p ρ x W = IY - IS := by
    rw [gpRate, hIY, hIS, mutualInfo_gpYU, mutualInfo_gpSU hW]
  rw [hrate] at hRp
  have hIS0 : 0 ≤ IS := mutualInfo_nonneg hSU _ _
  set δ := (IY - IS - R * log 2) / 4 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  set cY := H[Prod.snd ; gpYU p ρ x W] + H[Prod.snd | Prod.fst ; gpYU p ρ x W]
  set cS := H[Prod.snd ; gpSU p ρ] + H[Prod.snd | Prod.fst ; gpSU p ρ]
  have hcY : 0 ≤ cY := add_nonneg (entropyRV_nonneg hYU _) (condEntropy_nonneg hYU _ _)
  have hcS : 0 ≤ cS := add_nonneg (entropyRV_nonneg hSU _) (condEntropy_nonneg hSU _ _)
  set ε' := min (1 / 4) (δ / (1 + 2 * cY + cS)) with hε'_def
  have hden : 0 < 1 + 2 * cY + cS := by linarith
  have hε' : 0 < ε' := lt_min (by norm_num) (div_pos hδ hden)
  have hε'14 : ε' ≤ 1 / 4 := min_le_left _ _
  have hε'δ : ε' * (1 + 2 * cY + cS) ≤ δ := (le_div_iff₀ hden).1 (min_le_right _ _)
  have hεcY : (2 * ε') * cY ≤ δ := by nlinarith [mul_nonneg hε'.le hcS]
  have hεcS : ε' * cS ≤ δ := by nlinarith [mul_nonneg hε'.le hcY]
  have hev := eventually_le_prob_iidPMF_condRobustTypicalSet hSU (ε' := ε' / 2) (ε := ε')
    (by linarith) hε'
  rw [margFst_gpSU hρ] at hev
  set L : ℕ → ℕ := fun n => ⌈exp (n * (IS + 2 * δ))⌉₊
  have hL : ∀ n, 0 < L n := fun n => Nat.ceil_pos.2 (exp_pos _)
  set K := condTypicalityConst (gpJoint p ρ x W) ε' (2 * ε')
  set G : ℕ → ℝ := fun n => K / n + exp (-(n * (δ / 2))) +
    (1 - prob (iidPMF p n) (robustTypicalSet p n (ε' / 2))) + 4 * exp (-(n * δ))
  have hcode : ∀ n : ℕ, ∃ c : StateCode (2 ^ ⌈n * R⌉₊) n σ α β, c.Allowed .noncausal false ∧
      (0 < n → (∀ s ∈ robustTypicalSet p n (ε' / 2),
        (1 - ε') * exp (-(n * (IS + ε' * cS))) ≤
          prob (iidPMF (margSnd (gpSU p ρ)) n) (condRobustTypicalSet (gpSU p ρ) ε' s)) →
        c.errProb W p ≤ G n) := fun n => by
    by_cases hP : 0 < n ∧ ∀ s ∈ robustTypicalSet p n (ε' / 2),
        (1 - ε') * exp (-(n * (IS + ε' * cS))) ≤
          prob (iidPMF (margSnd (gpSU p ρ)) n) (condRobustTypicalSet (gpSU p ρ) ε' s)
    · obtain ⟨hn, ha⟩ := hP
      obtain ⟨c, hc, hb⟩ := exists_gp_code_le hp hρ hW x hn (hpos n) (hL n)
        (ε := 2 * ε') (by linarith) ha
      refine ⟨c, hc, fun _ _ => hb.trans ?_⟩
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      -- The covering term.
      have hLge : exp (n * (IS + 2 * δ)) ≤ (L n : ℝ) := Nat.le_ceil _
      have hcov : exp (-((L n : ℝ) * ((1 - ε') * exp (-(n * (IS + ε' * cS)))))) ≤
          exp (-(n * (δ / 2))) := by
        refine exp_le_exp.2 ?_
        have h1 : exp (n * (IS + 2 * δ)) * exp (-(n * (IS + ε' * cS))) =
            exp (n * (2 * δ - ε' * cS)) := by
          rw [← exp_add]
          congr 1
          ring
        have h2 : (n : ℝ) * δ + 1 ≤ exp (n * (2 * δ - ε' * cS)) := by
          have := add_one_le_exp ((n : ℝ) * (2 * δ - ε' * cS))
          nlinarith [mul_le_mul_of_nonneg_left (by linarith : δ ≤ 2 * δ - ε' * cS) hn0]
        have h3 : exp (n * (IS + 2 * δ)) * ((1 - ε') * exp (-(n * (IS + ε' * cS)))) ≤
            (L n : ℝ) * ((1 - ε') * exp (-(n * (IS + ε' * cS)))) :=
          mul_le_mul_of_nonneg_right hLge
            (mul_nonneg (by linarith) (exp_pos _).le)
        have h4 : (1 - ε') * exp (n * (2 * δ - ε' * cS)) ≤
            exp (n * (IS + 2 * δ)) * ((1 - ε') * exp (-(n * (IS + ε' * cS)))) := by
          rw [← h1]
          exact le_of_eq (by ring)
        have h5 : (n : ℝ) * (δ / 2) ≤ (1 - ε') * exp (n * (2 * δ - ε' * cS)) := by
          have : (0 : ℝ) ≤ (n : ℝ) * δ := mul_nonneg hn0 hδ.le
          nlinarith
        linarith
      -- The packing term.
      have hpack : ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) * ((L n : ℝ) * exp (-(n * (IY - 2 * ε' * cY)))) ≤
          4 * exp (-(n * δ)) := by
        have hMle := two_pow_ceil_le n hR0.le
        have hA0 : 0 ≤ n * (IS + 2 * δ) := mul_nonneg hn0 (by linarith)
        have h1le : (1 : ℝ) ≤ exp (n * (IS + 2 * δ)) := one_le_exp hA0
        have hLle : (L n : ℝ) ≤ 2 * exp (n * (IS + 2 * δ)) := by
          have := (Nat.ceil_lt_add_one (exp_pos (n * (IS + 2 * δ))).le).le
          simp only [L]
          linarith
        have hη : exp (-(n * (IY - 2 * ε' * cY))) ≤ exp (-(n * (IY - δ))) :=
          exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hεcY hn0])
        have hexp : exp (n * (R * log 2)) * (exp (n * (IS + 2 * δ)) * exp (-(n * (IY - δ)))) =
            exp (-(n * δ)) := by
          rw [← exp_add, ← exp_add]
          congr 1
          rw [hδ_def]
          ring
        calc ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) * ((L n : ℝ) * exp (-(n * (IY - 2 * ε' * cY))))
            ≤ (2 * exp (n * (R * log 2))) * ((2 * exp (n * (IS + 2 * δ))) *
                exp (-(n * (IY - δ)))) := by
              gcongr
          _ = 4 * exp (-(n * δ)) := by
              rw [← hexp]
              ring
      simp only [G, K]
      have e : IY - 2 * ε' * (H[Prod.snd ; gpYU p ρ x W] +
          H[Prod.snd | Prod.fst ; gpYU p ρ x W]) = IY - 2 * ε' * cY := rfl
      linarith
    · refine ⟨⟨fun _ _ _ => x₀, fun _ _ => ⟨0, hpos n⟩⟩, ⟨trivial, fun _ _ _ _ => rfl⟩,
        fun hn ha => absurd ⟨hn, ha⟩ hP⟩
  choose c hc hcb using hcode
  refine ⟨c, hc, ?_⟩
  have hGlim : Tendsto G atTop (𝓝 0) := by
    have h1 := tendsto_const_div_atTop_nhds_zero_nat K
    have h2 := tendsto_exp_neg_mul_nat (a := δ / 2) (by linarith)
    have h3 : Tendsto (fun n => 1 - prob (iidPMF p n) (robustTypicalSet p n (ε' / 2)))
        atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet hp (by linarith : 0 < ε' / 2)).const_sub 1
    have h4 := (tendsto_exp_neg_mul_nat hδ).const_mul 4
    simpa using ((h1.add h2).add h3).add h4
  have hnn : ∀ n, 0 ≤ (c n).errProb W p := fun n => by
    rw [(c n).errProb_eq_sum_atState]
    exact sum_nonneg fun s _ => mul_nonneg (iidPMF_isPMF hp n |>.nonneg s)
      ((c n |>.atState s).avgErrProb_nonneg hW)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hGlim
    (Eventually.of_forall hnn) ?_
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  exact hcb n hn0 hn

/-- `I(U; Y) - I(U; S) ≤ max_{p(x|s)} I(X; Y | S)`: knowing the state at the decoder can only
help. -/
theorem gpRate_le_stateKnownValue [Fintype α] [Nonempty α] (hp : IsPMF p) (hρ : ∀ s, IsPMF (ρ s))
    (hW : IsChannel W) (x : 𝒰 → σ → α) : gpRate p ρ x W ≤ stateKnownValue W p := by
  have hl := log_pos one_lt_two
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  have hR : r / log 2 < gpRate p ρ x W / log 2 := div_lt_div_of_pos_right hr hl
  have := (isAchievableStateRate_noncausal_false_of_lt hp hρ hW x hR).le_stateKnownValue hW hp
  exact (div_le_div_iff_of_pos_right hl).1 this

end InfoTheory
