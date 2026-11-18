/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StateChannel.Multicoding

/-!
# The compound channel

A compound channel is a finite set of DMCs `p(y_s | x)`, `s ∈ 𝒮`. The transmission is over one of
them, unknown to the encoder and to the decoder, and a code must work for all of them. This file
proves Theorem 1 of Lecture 7: the capacity is `max_{p(x)} min_{s} I(X; Y_s)`.

## Main definitions

* `compoundErr W c`: the probability of error `max_s P{M ≠ M̂ | s}`.
* `IsAchievableCompound W R`, `compoundCapacity W`: achievable rates in bits, and the capacity.
* `IsAchievableCompoundDec W R`, `compoundDecCapacity W`: the same when the decoder knows `s`.
* `compoundInfo W p`: `min_s I(X; Y_s)`, and `compoundValue W`: `max_{p(x)} min_s I(X; Y_s)`.

## Main statements

* `compoundCapacity_eq`: **Theorem 1 of Lecture 7**.
* `compoundDecCapacity_eq`: the capacity does not increase if the decoder knows the state.
* `compoundValue_le_capacity`: `C_CC ≤ min_s C_s`.

## Implementation notes

The notes prove the converse with a time-sharing random variable. We use the concavity of `I(X; Y)`
in `p(x)` for `p(x) = (1/n) ∑ᵢ p(xᵢ)`, which is the same argument.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {σ α β : Type*} [Fintype σ] [Nonempty σ] [Fintype β]

/-- **Lecture 7 of [elgamal2010].** The probability of error of a code for the compound channel,
`P_e^(n) = max_s P{M ≠ M̂ | s is the actual state}`. -/
def compoundErr {M n : ℕ} (W : σ → α → β → ℝ) (c : ChannelCode M n α β) : ℝ :=
  univ.sup' univ_nonempty fun s => c.avgErrProb (W s)

/-- **Lecture 7 of [elgamal2010].** A rate `R`, in bits, is achievable for the compound channel if
there are `(2^{nR}, n)` codes whose probability of error tends to `0`. -/
def IsAchievableCompound (W : σ → α → β → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, ChannelCode (2 ^ ⌈n * R⌉₊) n α β,
    Tendsto (fun n => compoundErr W (c n)) atTop (𝓝 0)

/-- **Lecture 7 of [elgamal2010].** The capacity of the compound channel, in bits. -/
def compoundCapacity (W : σ → α → β → ℝ) : ℝ := sSup {R | IsAchievableCompound W R}

/-- A rate `R` is achievable when the decoder knows the state: the codes for the different states
have the same encoder. -/
def IsAchievableCompoundDec (W : σ → α → β → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, σ → ChannelCode (2 ^ ⌈n * R⌉₊) n α β, (∀ n s s', (c n s).enc = (c n s').enc) ∧
    Tendsto (fun n => univ.sup' univ_nonempty fun s => (c n s).avgErrProb (W s)) atTop (𝓝 0)

/-- The capacity of the compound channel when the decoder knows the state, in bits. -/
def compoundDecCapacity (W : σ → α → β → ℝ) : ℝ := sSup {R | IsAchievableCompoundDec W R}

variable [Fintype α]

/-- `min_s I(X; Y_s)`. -/
def compoundInfo (W : σ → α → β → ℝ) (p : α → ℝ) : ℝ :=
  univ.inf' univ_nonempty fun s => mutualInfoOf p (W s)

/-- `max_{p(x)} min_s I(X; Y_s)`. -/
def compoundValue (W : σ → α → β → ℝ) : ℝ := sSup {v | ∃ p, IsPMF p ∧ compoundInfo W p = v}

variable {W : σ → α → β → ℝ}

omit [Fintype α] in
lemma compoundErr_ge {M n : ℕ} (W : σ → α → β → ℝ) (c : ChannelCode M n α β) (s : σ) :
    c.avgErrProb (W s) ≤ compoundErr W c :=
  le_sup' (fun s => c.avgErrProb (W s)) (mem_univ s)

lemma compoundInfo_le (W : σ → α → β → ℝ) (p : α → ℝ) (s : σ) :
    compoundInfo W p ≤ mutualInfoOf p (W s) :=
  inf'_le (fun s => mutualInfoOf p (W s)) (mem_univ s)

lemma bddAbove_compoundValue (hW : ∀ s, IsChannel (W s)) :
    BddAbove {v | ∃ p, IsPMF p ∧ compoundInfo W p = v} := by
  obtain ⟨s₀⟩ := ‹Nonempty σ›
  refine ⟨capacity (W s₀), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (compoundInfo_le W p s₀).trans (mutualInfoOf_le_capacity hp (hW s₀))

lemma compoundInfo_le_compoundValue (hW : ∀ s, IsChannel (W s)) {p : α → ℝ} (hp : IsPMF p) :
    compoundInfo W p ≤ compoundValue W :=
  le_csSup (bddAbove_compoundValue hW) ⟨p, hp, rfl⟩

/-- `C_CC ≤ min_s C_s`, where `C_s` is the capacity of the channel `p(y_s | x)`. -/
theorem compoundValue_le_capacity [Nonempty α] (hW : ∀ s, IsChannel (W s)) (s : σ) :
    compoundValue W ≤ capacity (W s) :=
  csSup_le ⟨_, uniformPMF α, uniformPMF_isPMF, rfl⟩ fun _ ⟨_, hp, hv⟩ => hv ▸
    (compoundInfo_le W _ s).trans (mutualInfoOf_le_capacity hp (hW s))

/-! ### The converse -/

omit [Fintype σ] [Nonempty σ] in
/-- The input law averaged over time. -/
lemma mutualInfoOf_sum_le (hW : ∀ s, IsChannel (W s)) {n : ℕ} (hn : 0 < n) {P : Fin n → α → ℝ}
    (hP : ∀ i, IsPMF (P i)) (s : σ) :
    IsPMF (fun x => ∑ i, (1 / (n : ℝ)) * P i x) ∧
      ∑ i, mutualInfoOf (P i) (W s) ≤
        n * mutualInfoOf (fun x => ∑ i, (1 / (n : ℝ)) * P i x) (W s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hPbar : IsPMF (fun x => ∑ i, (1 / (n : ℝ)) * P i x) := by
    refine ⟨fun x => sum_nonneg fun i _ => mul_nonneg (by positivity) ((hP i).nonneg x), ?_⟩
    rw [sum_comm]
    simp only [← mul_sum, (hP _).sum_eq_one, mul_one, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  refine ⟨hPbar, ?_⟩
  have hJ := (mutualInfoOf_concave_input (hW s)).le_map_sum (t := univ)
    (w := fun _ : Fin n => 1 / (n : ℝ)) (p := P) (fun _ _ => by positivity)
    (by simp [hn'.ne']) fun i _ => hP i
  simp only [smul_eq_mul, ← mul_sum] at hJ
  have e : (∑ i : Fin n, (1 / (n : ℝ)) • P i) = fun x => ∑ i, (1 / (n : ℝ)) * P i x := by
    funext x
    simp [Finset.sum_apply]
  rw [e] at hJ
  calc ∑ i, mutualInfoOf (P i) (W s) = n * (1 / n * ∑ i, mutualInfoOf (P i) (W s)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ hn'.le

/-- **Converse of Theorem 1 (Lecture 7 of [elgamal2010]).** By Fano's inequality, for each `s`,
`(1 - P_e^(n)) log M ≤ log 2 + ∑ᵢ I(Xᵢ; Y_{s,i}) ≤ log 2 + n I(X; Y_s)` with the same `p(x)`, and
the decoder may depend on `s`. -/
theorem one_sub_compoundErr_mul_log_le [Nonempty α] (hW : ∀ s, IsChannel (W s)) {M n : ℕ}
    (hM : 0 < M) (c : σ → ChannelCode M n α β) (hc : ∀ s s', (c s).enc = (c s').enc) :
    (1 - univ.sup' univ_nonempty fun s => (c s).avgErrProb (W s)) * log M ≤
      log 2 + n * compoundValue W := by
  obtain ⟨s₀⟩ := ‹Nonempty σ›
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hlog : 0 ≤ log (M : ℝ) := log_natCast_nonneg M
  set Pm := univ.sup' univ_nonempty fun s => (c s).avgErrProb (W s)
  have hPm : ∀ s, (1 - Pm) * log M ≤ (1 - (c s).avgErrProb (W s)) * log M := fun s =>
    mul_le_mul_of_nonneg_right (by
      have := le_sup' (fun s => (c s).avgErrProb (W s)) (mem_univ s)
      linarith) hlog
  set P : Fin n → α → ℝ := fun i => dist (uniformPMF (Fin M)) fun m => (c s₀).enc m i
  have hP : ∀ i, IsPMF (P i) := fun i => uniformPMF_isPMF.dist _
  have hF : ∀ s, (1 - (c s).avgErrProb (W s)) * log M ≤ log 2 + ∑ i, mutualInfoOf (P i) (W s) :=
    fun s => by
      have := (c s).one_sub_avgErrProb_mul_log_le_sum (hW s) hM
      rwa [hc s s₀] at this
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using (hPm s₀).trans (hF s₀)
  · have hbar := (mutualInfoOf_sum_le hW hn hP s₀).1
    obtain ⟨s, -, hs⟩ := exists_mem_eq_inf' (s := (univ : Finset σ)) univ_nonempty
      fun s => mutualInfoOf (fun x => ∑ i, (1 / (n : ℝ)) * P i x) (W s)
    have h1 := (mutualInfoOf_sum_le hW hn hP s).2
    have h2 : mutualInfoOf (fun x => ∑ i, (1 / (n : ℝ)) * P i x) (W s) ≤ compoundValue W := by
      rw [← hs]
      exact compoundInfo_le_compoundValue hW hbar
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [hPm s, hF s, mul_le_mul_of_nonneg_left h2 hn']

theorem compoundDecCapacity_le_aux [Nonempty α] (hW : ∀ s, IsChannel (W s)) {R : ℝ}
    (h : IsAchievableCompoundDec W R) : R ≤ compoundValue W / log 2 := by
  obtain ⟨c, hc, hlim⟩ := h
  obtain ⟨s₀⟩ := ‹Nonempty σ›
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  refine le_div_log_two_of_converse hlim (fun n => sup'_le _ _ fun s _ => ?_)
    fun n => one_sub_compoundErr_mul_log_le hW (hpos n) (c n) (hc n)
  exact (c n s).avgErrProb_le_maxErrProb.trans
    (ChannelCode.maxErrProb_le _ (hpos n) fun i => (c n s).condErrProb_le_one (hW s) i)

omit [Fintype α] in
/-- A code for the compound channel is a code when the decoder knows the state. -/
lemma IsAchievableCompound.isAchievableCompoundDec {R : ℝ} (h : IsAchievableCompound W R) :
    IsAchievableCompoundDec W R := by
  obtain ⟨c, hlim⟩ := h
  exact ⟨fun n _ => c n, fun _ _ _ => rfl, hlim⟩

/-! ### Achievability -/

omit [Fintype α] [Nonempty σ] in
/-- A single message is never in error. -/
lemma avgErrProb_single {M n : ℕ} (hM : M = 1) (x₀ : α) (d : (Fin n → β) → Fin M)
    (V : α → β → ℝ) : (⟨fun _ _ => x₀, d⟩ : ChannelCode M n α β).avgErrProb V = 0 := by
  subst hM
  have : ∀ i : Fin 1, (⟨fun _ _ => x₀, d⟩ : ChannelCode 1 n α β).condErrProb V i = 0 := fun i => by
    simp [ChannelCode.condErrProb, Subsingleton.elim (d _) i]
  simp [ChannelCode.avgErrProb, this]

omit [Nonempty σ] in
open Classical in
/-- The random coding bound for the compound channel: a code all of whose probabilities of error
add up to at most the sum of the atypicality probabilities plus `|𝒮| M e^{-n a}|𝒮|`. -/
theorem exists_compound_code_le (hW : ∀ s, IsChannel (W s)) {p : α → ℝ} (hp : IsPMF p) {n M : ℕ}
    (hM : 0 < M) {ε a : ℝ}
    (ha : ∀ s, a ≤ mutualInfoOf p (W s) - ε * (H[Prod.snd ; revJoint p (W s)] +
      H[Prod.snd | Prod.fst ; revJoint p (W s)])) :
    ∃ c : ChannelCode M n α β, ∑ s, c.avgErrProb (W s) ≤
      ∑ s, (1 - prob (iidPMF (revJoint p (W s)) n) (robustTypicalSet (revJoint p (W s)) n ε)) +
        Fintype.card σ * (M * (Fintype.card σ * exp (-(n * a)))) := by
  have hμ := iidPMF_isPMF hp n
  set q : σ → β × α → ℝ := fun s => revJoint p (W s)
  have hq : ∀ s, IsPMF (q s) := fun s => revJoint_isPMF hp (hW s)
  have hm : ∀ s, margSnd (q s) = p := fun s => margSnd_revJoint (hW s)
  obtain ⟨A, hA⟩ : ∃ A : (Fin n → α) → (Fin n → β) → Prop, ∀ x y, A x y ↔
      ∃ s, zipSeq y x ∈ robustTypicalSet (q s) n ε := ⟨_, fun _ _ => Iff.rfl⟩
  set m₀ : Fin M := ⟨0, hM⟩
  set η : ℝ := Fintype.card σ * exp (-(n * a))
  have hη₀ : 0 ≤ η := mul_nonneg (Nat.cast_nonneg _) (exp_pos _).le
  have hη : ∀ y, ∑ x, iidPMF p n x * (if A x y then 1 else 0) ≤ η := fun y => by
    have hstep : ∀ x, iidPMF p n x * (if A x y then 1 else 0) ≤ ∑ s, iidPMF p n x *
        (if x ∈ condRobustTypicalSet (q s) ε y then 1 else 0) := fun x => by
      by_cases hx : A x y
      · obtain ⟨s, hs⟩ := (hA x y).1 hx
        simp only [hx, ite_true, mul_one]
        refine le_trans ?_ (single_le_sum (fun s _ => mul_nonneg (hμ.nonneg x)
          (by split_ifs <;> norm_num)) (mem_univ s))
        simp [mem_condRobustTypicalSet.2 hs]
      · simp only [hx, ite_false, mul_zero]
        exact sum_nonneg fun s _ => mul_nonneg (hμ.nonneg x) (by split_ifs <;> norm_num)
    refine (sum_le_sum fun x _ => hstep x).trans ?_
    rw [sum_comm]
    calc ∑ s, ∑ x, iidPMF p n x * (if x ∈ condRobustTypicalSet (q s) ε y then 1 else 0)
        = ∑ s, prob (iidPMF (margSnd (q s)) n) (condRobustTypicalSet (q s) ε y) :=
          sum_congr rfl fun s _ => by
            rw [hm, prob]
            simp only [mul_ite, mul_one, mul_zero]
            rw [← sum_filter]
            congr 1
            ext x
            simp
      _ ≤ ∑ _s : σ, exp (-(n * a)) := sum_le_sum fun s _ =>
          (prob_iidPMF_condRobustTypicalSet_le (hq s) ε y).trans (exp_le_exp.2 (by
            have h1 := ha s
            have h2 : I[Prod.snd : Prod.fst ; q s] = mutualInfoOf p (W s) :=
              mutualInfo_revJoint p (W s)
            have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            rw [h2]
            nlinarith [mul_le_mul_of_nonneg_left h1 hn]))
      _ = η := by simp [η]
  -- The code for a codebook.
  set code : (Fin M → Fin 1 → Fin n → α) → ChannelCode M n α β := fun C =>
    ⟨fun m => C m 0, subcodeDecode A C m₀⟩
  set bound : σ → ℝ := fun s =>
    1 - prob (iidPMF (q s) n) (robustTypicalSet (q s) n ε)
  have hs : ∀ s (m : Fin M),
      ∑ C, iidPMF (iidPMF (iidPMF p n) 1) M C * (code C).condErrProb (W s) m ≤
      bound s + M * (1 * η) := fun s m => by
    have h := sum_codebook_subcode_le hμ m₀ A
      (fun (D : Fin 1 → Fin n → α) y => channelExt (W s) n (D 0) y)
      (fun D y => channelExt_nonneg (hW s) _ _)
      (fun D => le_of_eq ((hW s).ext n (D 0)).sum_eq_one) hη₀ hη m
    have hfirst : ∑ D : Fin 1 → Fin n → α, iidPMF (iidPMF p n) 1 D * ∑ y,
        (if ∀ l, ¬ A (D l) y then channelExt (W s) n (D 0) y else 0) ≤ bound s := by
      have e := sum_iidPMF_mul_sum_ite_not_mem hp (hW s) (n := n) ε
      rw [← sum_iidPMF_eval hμ (0 : Fin 1)] at e
      simp only [bound, q]
      rw [← e]
      refine sum_le_sum fun D _ => mul_le_mul_of_nonneg_left (sum_le_sum fun y _ => ?_)
        ((iidPMF_isPMF hμ 1).nonneg D)
      by_cases hAl : ∀ l, ¬ A (D l) y
      · have : zipSeq y (D 0) ∉ robustTypicalSet (revJoint p (W s)) n ε := fun h' =>
          hAl 0 ((hA _ _).2 ⟨s, h'⟩)
        simp [hAl, this]
      · simp only [hAl, ite_false]
        split_ifs
        · exact le_rfl
        · exact channelExt_nonneg (hW s) _ _
    have hcast : (((1 : ℕ) : ℝ)) = 1 := Nat.cast_one
    rw [hcast] at h
    exact h.trans (add_le_add hfirst le_rfl)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have htotal : ∑ C, iidPMF (iidPMF (iidPMF p n) 1) M C * ∑ s, (code C).avgErrProb (W s) ≤
      ∑ s, bound s + Fintype.card σ * (M * η) := by
    calc ∑ C, iidPMF (iidPMF (iidPMF p n) 1) M C * ∑ s, (code C).avgErrProb (W s)
        = ∑ s, (∑ m, ∑ C, iidPMF (iidPMF (iidPMF p n) 1) M C *
            (code C).condErrProb (W s) m) / M := by
          simp_rw [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun s _ => ?_
          simp only [ChannelCode.avgErrProb]
          rw [sum_comm, sum_div]
          refine sum_congr rfl fun C _ => ?_
          rw [mul_div_assoc', mul_sum]
      _ ≤ ∑ s, (∑ _m : Fin M, (bound s + M * (1 * η))) / M := sum_le_sum fun s _ =>
          div_le_div_of_nonneg_right (sum_le_sum fun m _ => hs s m) hM'.le
      _ = ∑ s, (bound s + M * η) := sum_congr rfl fun s _ => by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
          field_simp
      _ = ∑ s, bound s + Fintype.card σ * (M * η) := by
          rw [sum_add_distrib]
          simp
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le (iidPMF_isPMF (iidPMF_isPMF hμ 1) M) htotal
  exact ⟨code C, hC⟩

/-- **Achievability of Theorem 1 (Lecture 7 of [elgamal2010]).** Every rate below `C_CC` is
achievable, with one decoder for all the states: `(xⁿ(m̂), yⁿ) ∈ T_ε^(n)(X, Y_s)` for some `s`. -/
theorem isAchievableCompound_of_lt [Nonempty α] (hW : ∀ s, IsChannel (W s)) {R : ℝ}
    (hR : R < compoundValue W / log 2) : IsAchievableCompound W R := by
  classical
  have hl := log_pos one_lt_two
  obtain ⟨s₀⟩ := ‹Nonempty σ›
  obtain ⟨x₀⟩ := ‹Nonempty α›
  rcases le_or_gt R 0 with hR0 | hR0
  · -- With `R ≤ 0` there is a single message.
    have h1 : ∀ n : ℕ, 2 ^ ⌈n * R⌉₊ = 1 := fun n => by
      rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0), pow_zero]
    refine ⟨fun n => ⟨fun _ _ => x₀, fun _ => ⟨0, by positivity⟩⟩, ?_⟩
    have : ∀ n : ℕ, compoundErr W (⟨fun _ _ => x₀, fun _ => ⟨0, by positivity⟩⟩ :
        ChannelCode (2 ^ ⌈n * R⌉₊) n α β) = 0 := fun n => by
      simp [compoundErr, avgErrProb_single (h1 n)]
    exact tendsto_const_nhds.congr fun n => (this n).symm
  have hRC : R * log 2 < compoundValue W := (lt_div_iff₀ hl).1 hR
  obtain ⟨_, ⟨p, hp, rfl⟩, hpI⟩ := exists_lt_of_lt_csSup
    (⟨_, uniformPMF α, uniformPMF_isPMF, rfl⟩ :
      Set.Nonempty {v | ∃ p, IsPMF p ∧ compoundInfo W p = v}) hRC
  set I := compoundInfo W p
  set δ := (I - R * log 2) / 4 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  set c : σ → ℝ := fun s => H[Prod.snd ; revJoint p (W s)] +
    H[Prod.snd | Prod.fst ; revJoint p (W s)]
  have hc : ∀ s, 0 ≤ c s := fun s => add_nonneg (entropyRV_nonneg (revJoint_isPMF hp (hW s)) _)
    (condEntropy_nonneg (revJoint_isPMF hp (hW s)) _ _)
  set K := 1 + ∑ s, c s
  have hK : 0 < K := by
    have := sum_nonneg fun s (_ : s ∈ univ) => hc s
    linarith
  set ε := δ / K with hε_def
  have hε : 0 < ε := div_pos hδ hK
  have hεc : ∀ s, ε * c s ≤ δ := fun s => by
    have h1 : c s ≤ K := by
      have := single_le_sum (fun s _ => hc s) (mem_univ s)
      simp only [K]
      linarith
    calc ε * c s ≤ ε * K := mul_le_mul_of_nonneg_left h1 hε.le
      _ = δ := by rw [hε_def]; field_simp
  have ha : ∀ s, I - δ ≤ mutualInfoOf p (W s) - ε * c s := fun s => by
    have := compoundInfo_le W p s
    linarith [hεc s]
  have hM : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  choose code hcode using fun n : ℕ => exists_compound_code_le hW hp (n := n) (hM n) (ε := ε)
    (a := I - δ) ha
  refine ⟨code, ?_⟩
  set card := (Fintype.card σ : ℝ)
  have hbound : ∀ n : ℕ, compoundErr W (code n) ≤
      ∑ s, (1 - prob (iidPMF (revJoint p (W s)) n) (robustTypicalSet (revJoint p (W s)) n ε)) +
        card * (2 * (card * exp (-(n * (3 * δ))))) := fun n => by
    have hnn : ∀ s, 0 ≤ (code n).avgErrProb (W s) := fun s => (code n).avgErrProb_nonneg (hW s)
    have h1 : compoundErr W (code n) ≤ ∑ s, (code n).avgErrProb (W s) :=
      sup'_le _ _ fun s hs => single_le_sum (fun s _ => hnn s) hs
    refine h1.trans ((hcode n).trans (add_le_add le_rfl ?_))
    have hMle := two_pow_ceil_le n hR0.le
    have hexp : exp (n * (R * log 2)) * exp (-(n * (I - δ))) = exp (-(n * (3 * δ))) := by
      rw [← exp_add]
      congr 1
      rw [hδ_def]
      ring
    have hc0 : 0 ≤ card := Nat.cast_nonneg _
    calc card * (((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) * (card * exp (-(n * (I - δ)))))
        ≤ card * ((2 * exp (n * (R * log 2))) * (card * exp (-(n * (I - δ))))) := by
          gcongr
      _ = card * (2 * (card * (exp (n * (R * log 2)) * exp (-(n * (I - δ)))))) := by ring
      _ = _ := by rw [hexp]
  have hlim : Tendsto (fun n : ℕ =>
      ∑ s, (1 - prob (iidPMF (revJoint p (W s)) n) (robustTypicalSet (revJoint p (W s)) n ε)) +
        card * (2 * (card * exp (-(n * (3 * δ)))))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ∑ s, (1 - prob (iidPMF (revJoint p (W s)) n)
        (robustTypicalSet (revJoint p (W s)) n ε))) atTop (𝓝 0) := by
      have := tendsto_finsetSum (univ : Finset σ) fun s _ =>
        ((tendsto_prob_robustTypicalSet (revJoint_isPMF hp (hW s)) hε).const_sub 1)
      simpa using this
    have h2 := ((tendsto_exp_neg_mul_nat (a := 3 * δ) (by linarith)).const_mul card).const_mul 2
      |>.const_mul card
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => ?_) hbound
  exact ((code n).avgErrProb_nonneg (hW s₀)).trans (compoundErr_ge W _ s₀)

/-! ### Theorem 1 -/

/-- **Theorem 1 (Lecture 7 of [elgamal2010]).** The capacity of the compound channel is
`C_CC = max_{p(x)} min_s I(X; Y_s)`, in bits. -/
theorem compoundCapacity_eq [Nonempty α] (hW : ∀ s, IsChannel (W s)) :
    compoundCapacity W = compoundValue W / log 2 :=
  sSup_eq_of_forall_mem (fun _ h => compoundDecCapacity_le_aux hW h.isAchievableCompoundDec)
    fun _ hR => isAchievableCompound_of_lt hW hR

/-- **Lecture 7 of [elgamal2010], page 7-5.** The capacity does not increase if the decoder knows
the state. -/
theorem compoundDecCapacity_eq [Nonempty α] (hW : ∀ s, IsChannel (W s)) :
    compoundDecCapacity W = compoundValue W / log 2 :=
  sSup_eq_of_forall_mem (fun _ h => compoundDecCapacity_le_aux hW h)
    fun _ hR => (isAchievableCompound_of_lt hW hR).isAchievableCompoundDec

/-- The maximum in `C_CC` is attained: `max_{p(x)} min_s I(X; Y_s)`. -/
theorem exists_compoundInfo_eq [Nonempty α] (hW : ∀ s, IsChannel (W s)) :
    ∃ p, IsPMF p ∧ compoundInfo W p = compoundValue W := by
  have hcont : ContinuousOn (compoundInfo W) {p : α → ℝ | IsPMF p} := by
    have : compoundInfo W = univ.inf' univ_nonempty fun s p => mutualInfoOf p (W s) := by
      funext p
      simp [compoundInfo, Finset.inf'_apply]
    rw [this]
    exact ContinuousOn.finset_inf' _ fun s _ => continuousOn_mutualInfoOf (hW s)
  obtain ⟨p, hp, hmax⟩ := isCompact_setOf_isPMF.exists_isMaxOn
    ⟨uniformPMF α, uniformPMF_isPMF⟩ hcont
  refine ⟨p, hp, le_antisymm (compoundInfo_le_compoundValue hW hp) ?_⟩
  exact csSup_le ⟨_, uniformPMF α, uniformPMF_isPMF, rfl⟩ fun _ ⟨q, hq, hc⟩ => hc ▸ hmax hq

end InfoTheory
