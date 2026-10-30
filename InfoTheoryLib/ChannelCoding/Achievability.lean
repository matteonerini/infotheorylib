/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Code
public import InfoTheoryLib.ChannelCoding.JointTypicality

/-!
# The channel coding theorem: achievability

All rates below capacity are achievable. Following Shannon, we pick the codebook at random: the
`M` codewords are i.i.d. with i.i.d. symbols drawn from an input distribution `p`. The receiver
decodes by joint typicality, declaring `ŵ` if `(xⁿ(ŵ), yⁿ)` is the only jointly typical pair. The
average probability of error, averaged over the random codebooks, is at most
`Pr{(Xⁿ, Yⁿ) ∉ A_ε^(n)} + (M - 1) e^{-n(I(X;Y)-3ε)}`. So some codebook does at least this well,
and throwing away its worse half gives a code with small maximal probability of error.

The average over codebooks is an exact finite sum over all codebooks `Fin M → 𝒳ⁿ`, weighted by
their probability `∏_w ∏_i p(xᵢ(w))`, (7.62).

## Main definitions

* `typicalDecode A C w₀`: joint typicality decoding with the jointly typical set `A` and the
  codebook `C`, with `w₀` the guess when decoding fails.
* `typicalCode A C w₀`: the code with codebook `C` and joint typicality decoding.

## Main statements

* `sum_iidPMF_eval`, `sum_iidPMF_eval₂`: averaging a function of one or two codewords of a random
  codebook.
* `sum_codebook_condErrProb_le`: (7.65)–(7.78), the error probability of a message, averaged over
  the random codebooks.
* `exists_code_avgErrProb_le`: the random coding bound, some code has average probability of
  error at most `Pr{(Xⁿ, Yⁿ) ∉ A_ε^(n)} + (M - 1) e^{-n(I(X;Y)-3ε)}`.
* `isAchievableRate_of_lt_capacity`: Theorem 7.7.1 (achievability), every rate below capacity is
  achievable.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 7.7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Random codebooks -/

section Codebook

variable {X : Type*} [Fintype X]

open Classical in
/-- The probability that the `w`-th codeword of a random codebook is `a`. -/
lemma sum_iidPMF_indicator {μ : X → ℝ} (hμ : IsPMF μ) {M : ℕ} (w : Fin M) (a : X) :
    ∑ C : Fin M → X, iidPMF μ M C * (if C w = a then 1 else 0) = μ a := by
  classical
  have h := sum_iidPMF_mul_prod μ fun i b => if i = w then (if b = a then (1 : ℝ) else 0) else 1
  have h1 : ∀ C : Fin M → X,
      (∏ i, if i = w then (if C i = a then (1 : ℝ) else 0) else 1) = if C w = a then 1 else 0 :=
    fun C => by simp
  have h2 : ∀ i, ∑ b, μ b * (if i = w then (if b = a then (1 : ℝ) else 0) else 1) =
      if i = w then μ a else 1 := fun i => by
    split_ifs <;> simp [hμ.sum_eq_one]
  simp only [h1, h2] at h
  simpa using h

/-- Averaging a function of one codeword over a random codebook. -/
lemma sum_iidPMF_eval {μ : X → ℝ} (hμ : IsPMF μ) {M : ℕ} (w : Fin M) (f : X → ℝ) :
    ∑ C : Fin M → X, iidPMF μ M C * f (C w) = ∑ x, μ x * f x := by
  classical
  have : ∀ C : Fin M → X, f (C w) = ∑ a, f a * (if C w = a then 1 else 0) := fun C => by simp
  simp only [this, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_iidPMF_indicator hμ w a, sum_mul]
  exact sum_congr rfl fun C _ => by ring

open Classical in
/-- The probability that the `w`-th and `w'`-th codewords of a random codebook are `a` and `a'`. -/
lemma sum_iidPMF_indicator₂ {μ : X → ℝ} (hμ : IsPMF μ) {M : ℕ} {w w' : Fin M} (hww : w ≠ w')
    (a a' : X) :
    ∑ C : Fin M → X, iidPMF μ M C * ((if C w = a then 1 else 0) * (if C w' = a' then 1 else 0)) =
      μ a * μ a' := by
  classical
  set φ : Fin M → X → ℝ := fun i b =>
    if i = w then (if b = a then 1 else 0) else if i = w' then (if b = a' then 1 else 0) else 1
  have h := sum_iidPMF_mul_prod μ φ
  have hsplit : ∀ i b, φ i b = (if i = w then (if b = a then 1 else 0) else 1) *
      (if i = w' then (if b = a' then 1 else 0) else 1) := fun i b => by
    simp only [φ]
    by_cases h1 : i = w
    · subst h1; simp [hww]
    · simp [h1]
  have h1 : ∀ C : Fin M → X, (∏ i, φ i (C i)) =
      (if C w = a then 1 else 0) * (if C w' = a' then 1 else 0) := fun C => by
    simp only [hsplit, prod_mul_distrib]
    simp
  have h2 : ∀ i, ∑ b, μ b * φ i b = (if i = w then μ a else 1) * (if i = w' then μ a' else 1) :=
    fun i => by
      simp only [φ]
      by_cases hi1 : i = w
      · subst hi1; simp [hww]
      · by_cases hi2 : i = w'
        · simp [hi2, Ne.symm hww]
        · simp [hi1, hi2, hμ.sum_eq_one]
  simp only [h1, h2, prod_mul_distrib] at h
  simpa using h

/-- Averaging a function of two distinct codewords over a random codebook: they are independent. -/
lemma sum_iidPMF_eval₂ {μ : X → ℝ} (hμ : IsPMF μ) {M : ℕ} {w w' : Fin M} (hww : w ≠ w')
    (f : X → X → ℝ) :
    ∑ C : Fin M → X, iidPMF μ M C * f (C w) (C w') = ∑ x, ∑ x', μ x * μ x' * f x x' := by
  classical
  have : ∀ C : Fin M → X, f (C w) (C w') =
      ∑ a, ∑ a', f a a' * ((if C w = a then 1 else 0) * (if C w' = a' then 1 else 0)) :=
    fun C => by simp
  simp only [this, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun a' _ => ?_
  rw [← sum_iidPMF_indicator₂ hμ hww a a', sum_mul]
  exact sum_congr rfl fun C _ => by ring

/-- If the average of `g` under a pmf is at most `b`, some point has `g ≤ b`. -/
lemma exists_le_of_sum_mul_le {μ : X → ℝ} (hμ : IsPMF μ) {g : X → ℝ} {b : ℝ}
    (h : ∑ x, μ x * g x ≤ b) : ∃ x, g x ≤ b := by
  by_contra hne
  push Not at hne
  obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < μ x := by
    by_contra h0
    push Not at h0
    have : ∑ x, μ x ≤ 0 := sum_nonpos fun x _ => h0 x
    linarith [hμ.sum_eq_one]
  have : ∑ x, μ x * b < ∑ x, μ x * g x :=
    sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_left (hne x).le (hμ.nonneg x))
      ⟨x₀, mem_univ _, mul_lt_mul_of_pos_left (hne x₀) hx₀⟩
  rw [← sum_mul, hμ.sum_eq_one, one_mul] at this
  linarith

end Codebook

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Joint typicality decoding -/

open Classical in
/-- **Section 7.7, step 6.** Joint typicality decoding: declare `ŵ` if `(xⁿ(ŵ), yⁿ)` is jointly
typical and no other codeword is jointly typical with `yⁿ`; otherwise declare `w₀`. -/
def typicalDecode {n M : ℕ} (A : Finset ((Fin n → α) × (Fin n → β))) (C : Fin M → Fin n → α)
    (w₀ : Fin M) (y : Fin n → β) : Fin M :=
  if h : ∃ w, (C w, y) ∈ A ∧ ∀ w', (C w', y) ∈ A → w' = w then h.choose else w₀

omit [Fintype α] [Fintype β] in
lemma typicalDecode_eq {n M : ℕ} {A : Finset ((Fin n → α) × (Fin n → β))}
    {C : Fin M → Fin n → α} (w₀ : Fin M) {y : Fin n → β} {w : Fin M} (hw : (C w, y) ∈ A)
    (huniq : ∀ w', (C w', y) ∈ A → w' = w) : typicalDecode A C w₀ y = w := by
  have h : ∃ w, (C w, y) ∈ A ∧ ∀ w', (C w', y) ∈ A → w' = w := ⟨w, hw, huniq⟩
  unfold typicalDecode
  split
  · next h' => exact huniq _ h'.choose_spec.1
  · next h' => exact absurd h h' 

/-- The code with codebook `C` and joint typicality decoding. -/
def typicalCode {n M : ℕ} (A : Finset ((Fin n → α) × (Fin n → β))) (C : Fin M → Fin n → α)
    (w₀ : Fin M) : ChannelCode M n α β :=
  ⟨C, typicalDecode A C w₀⟩

omit [Fintype α] [Fintype β] in
open Classical in
/-- **(7.72)–(7.73)** A decoding error occurs only if the transmitted codeword is not jointly
typical with the output, or another codeword is. -/
lemma typicalDecode_ne_le {n M : ℕ} (A : Finset ((Fin n → α) × (Fin n → β)))
    (C : Fin M → Fin n → α) (w₀ : Fin M) (y : Fin n → β) (w : Fin M) :
    (if typicalDecode A C w₀ y ≠ w then (1 : ℝ) else 0) ≤
      (if (C w, y) ∈ A then 0 else 1) + ∑ w' ∈ univ.erase w, if (C w', y) ∈ A then 1 else 0 := by
  classical
  have hnn : 0 ≤ ∑ w' ∈ univ.erase w, if (C w', y) ∈ A then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hd : typicalDecode A C w₀ y = w
  · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte]
    split_ifs <;> linarith
  · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
    by_cases hw : (C w, y) ∈ A
    · obtain ⟨w', hw'A, hw'⟩ : ∃ w', (C w', y) ∈ A ∧ w' ≠ w := by
        by_contra hne
        push Not at hne
        exact hd (typicalDecode_eq w₀ hw hne)
      have : (1 : ℝ) ≤ ∑ w' ∈ univ.erase w, if (C w', y) ∈ A then 1 else 0 := by
        have := single_le_sum (f := fun w' => if (C w', y) ∈ A then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (mem_erase.2 ⟨hw', mem_univ w'⟩)
        simpa [hw'A] using this
      simp only [hw, ↓reduceIte, zero_add]
      exact this
    · simp only [hw, ↓reduceIte]
      linarith

/-! ### The random coding bound -/

omit [Fintype β] in
/-- `∑_{xⁿ} p(xⁿ) p(yⁿ | xⁿ) = p(yⁿ)`, the law of the output of the channel. -/
lemma sum_iidPMF_mul_channelExt (p : α → ℝ) (W : α → β → ℝ) (n : ℕ) (y : Fin n → β) :
    ∑ x, iidPMF p n x * channelExt W n x y = iidPMF (outDist p W) n y := by
  classical
  simp only [iidPMF, channelExt, ← prod_mul_distrib, outDist]
  exact (Fintype.prod_sum fun i a => p a * W a (y i)).symm

omit [Fintype α] [Fintype β] in
lemma jointIid_jointOf (p : α → ℝ) (W : α → β → ℝ) (n : ℕ) (z : (Fin n → α) × (Fin n → β)) :
    jointIid (jointOf p W) n z = iidPMF p n z.1 * channelExt W n z.1 z.2 := by
  simp only [jointIid, iidPMF, channelExt, jointOf, zipSeq, prod_mul_distrib]

/-- **(7.65)–(7.78)** Averaged over the random codebooks, the probability of error of joint
typicality decoding when the message `w` is sent is at most
`Pr{(Xⁿ, Yⁿ) ∉ A_ε^(n)} + (M - 1) e^{-n(I(X;Y)-3ε)}`. -/
theorem sum_codebook_condErrProb_le {p : α → ℝ} (hp : IsPMF p) {W : α → β → ℝ}
    (hW : IsChannel W) {n M : ℕ} (ε : ℝ) (w₀ w : Fin M) :
    ∑ C : Fin M → Fin n → α, iidPMF (iidPMF p n) M C *
        (typicalCode (jointTypicalSet (jointOf p W) n ε) C w₀).condErrProb W w ≤
      (1 - prob (jointIid (jointOf p W) n) (jointTypicalSet (jointOf p W) n ε)) +
        (M - 1) * exp (-(n * (mutualInfoOf p W - 3 * ε))) := by
  classical
  set q := jointOf p W
  set A := jointTypicalSet q n ε
  have hpn := iidPMF_isPMF hp n
  -- The two error events, (7.72).
  set T₁ : (Fin n → α) → ℝ := fun x => ∑ y, channelExt W n x y * if (x, y) ∈ A then 0 else 1
  set T₂ : (Fin n → α) → (Fin n → α) → ℝ :=
    fun x x' => ∑ y, channelExt W n x y * if (x', y) ∈ A then 1 else 0
  have hlam : ∀ C : Fin M → Fin n → α, (typicalCode A C w₀).condErrProb W w ≤
      T₁ (C w) + ∑ w' ∈ univ.erase w, T₂ (C w) (C w') := by
    intro C
    simp only [ChannelCode.condErrProb, typicalCode, T₁, T₂]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_le_sum fun y _ => ?_
    simp only [← mul_sum, ← mul_add]
    have h := mul_le_mul_of_nonneg_left (typicalDecode_ne_le A C w₀ y w)
      (channelExt_nonneg hW (C w) y)
    rw [mul_ite, mul_one, mul_zero] at h
    exact h
  -- The first error event has probability `Pr{(Xⁿ, Yⁿ) ∉ A}`, by the joint AEP.
  have hT₁ : ∑ x, iidPMF p n x * T₁ x = 1 - prob (jointIid q n) A := by
    have hjoint := (jointIid_isPMF (jointOf_isPMF hp hW) n).sum_eq_one
    have : ∑ x, iidPMF p n x * T₁ x = ∑ z, jointIid q n z * if z ∈ A then 0 else 1 := by
      simp only [T₁, mul_sum, Fintype.sum_prod_type, jointIid_jointOf, q]
      exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
    rw [this]
    have h2 : ∑ z, jointIid q n z * (if z ∈ A then 0 else 1) =
        ∑ z, jointIid q n z - ∑ z, if z ∈ A then jointIid q n z else 0 := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun z _ => by split_ifs <;> ring
    rw [h2, hjoint, ← sum_filter, filter_mem_eq_inter, univ_inter]
    rfl
  -- A wrong codeword is independent of the output, (7.75)–(7.76).
  have hT₂ : ∑ x, ∑ x', iidPMF p n x * iidPMF p n x' * T₂ x x' ≤
      exp (-(n * (mutualInfoOf p W - 3 * ε))) := by
    have h1 : ∑ x, ∑ x', iidPMF p n x * iidPMF p n x' * T₂ x x' =
        ∑ z ∈ A, iidPMF (margFst q) n z.1 * iidPMF (margSnd q) n z.2 := by
      have hm₁ : margFst q = p := dist_jointOf_fst hW
      have hm₂ : margSnd q = outDist p W := dist_jointOf_snd p W
      have hA : ∀ g : (Fin n → α) × (Fin n → β) → ℝ,
          ∑ z ∈ A, g z = ∑ z, if z ∈ A then g z else 0 := fun g => by
        rw [sum_ite_mem, univ_inter]
      rw [hm₁, hm₂, hA, Fintype.sum_prod_type]
      simp only [T₂, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun x' _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      rw [← sum_iidPMF_mul_channelExt]
      split_ifs with hxy
      · rw [mul_sum]
        exact sum_congr rfl fun x _ => by ring
      · simp
    rw [h1]
    exact prob_indep_jointTypicalSet_le (jointOf_isPMF hp hW) n ε
  calc ∑ C : Fin M → Fin n → α, iidPMF (iidPMF p n) M C * (typicalCode A C w₀).condErrProb W w
      ≤ ∑ C : Fin M → Fin n → α, iidPMF (iidPMF p n) M C *
          (T₁ (C w) + ∑ w' ∈ univ.erase w, T₂ (C w) (C w')) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hlam C) (iidPMF_nonneg hpn.nonneg C)
    _ = ∑ x, iidPMF p n x * T₁ x +
          ∑ w' ∈ univ.erase w, ∑ x, ∑ x', iidPMF p n x * iidPMF p n x' * T₂ x x' := by
        simp only [mul_add, sum_add_distrib, mul_sum]
        rw [sum_iidPMF_eval hpn w T₁, sum_comm]
        congr 1
        refine sum_congr rfl fun w' hw' => ?_
        exact sum_iidPMF_eval₂ hpn (Ne.symm (ne_of_mem_erase hw')) T₂
    _ ≤ (1 - prob (jointIid q n) A) +
          ∑ _w' ∈ univ.erase w, exp (-(n * (mutualInfoOf p W - 3 * ε))) := by
        rw [hT₁]
        exact add_le_add le_rfl (sum_le_sum fun _ _ => hT₂)
    _ = _ := by
        rw [sum_const, card_erase_of_mem (mem_univ w), card_univ, Fintype.card_fin, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos M with hM | hM
        · exact absurd w.isLt (by omega)
        · push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hM.ne')]
          ring

/-- **The random coding bound, (7.79).** For every `M ≥ 1` and `ε`, some `(M, n)` code has average
probability of error at most `Pr{(Xⁿ, Yⁿ) ∉ A_ε^(n)} + (M - 1) e^{-n(I(X;Y)-3ε)}`. -/
theorem exists_code_avgErrProb_le {p : α → ℝ} (hp : IsPMF p) {W : α → β → ℝ}
    (hW : IsChannel W) {M : ℕ} (hM : 0 < M) (n : ℕ) (ε : ℝ) :
    ∃ c : ChannelCode M n α β, c.avgErrProb W ≤
      (1 - prob (jointIid (jointOf p W) n) (jointTypicalSet (jointOf p W) n ε)) +
        (M - 1) * exp (-(n * (mutualInfoOf p W - 3 * ε))) := by
  set A := jointTypicalSet (jointOf p W) n ε
  set U := (1 - prob (jointIid (jointOf p W) n) A) +
    (M - 1) * exp (-(n * (mutualInfoOf p W - 3 * ε)))
  have hμ := iidPMF_isPMF (iidPMF_isPMF hp n) M
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h : ∑ C : Fin M → Fin n → α, iidPMF (iidPMF p n) M C *
      (typicalCode A C ⟨0, hM⟩).avgErrProb W ≤ U := by
    simp only [ChannelCode.avgErrProb, mul_div_assoc', ← sum_div, mul_sum]
    rw [sum_comm, div_le_iff₀ hM']
    calc ∑ w : Fin M, ∑ C : Fin M → Fin n → α,
          iidPMF (iidPMF p n) M C * (typicalCode A C ⟨0, hM⟩).condErrProb W w
        ≤ ∑ _w : Fin M, U := sum_le_sum fun w _ => sum_codebook_condErrProb_le hp hW ε _ w
      _ = U * M := by simp [mul_comm]
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hμ h
  exact ⟨_, hC⟩

/-! ### Theorem 7.7.1 -/

lemma tendsto_exp_neg_mul_nat {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => exp (-(n * a))) atTop (𝓝 0) :=
  tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.atTop_mul_const ha)

omit [Fintype α] in
/-- A code with a single message never errs. -/
lemma exists_code_maxErrProb_eq_zero [Nonempty α] (W : α → β → ℝ) {M : ℕ} (hM : M = 1)
    (n : ℕ) : ∃ c : ChannelCode M n α β, c.maxErrProb W = 0 := by
  subst hM
  refine ⟨⟨fun _ _ => Classical.arbitrary α, fun _ => 0⟩, ?_⟩
  have : ∀ i : Fin 1, (⟨fun _ _ => Classical.arbitrary α, fun _ => 0⟩ :
      ChannelCode 1 n α β).condErrProb W i = 0 := fun i => by
    simp [ChannelCode.condErrProb, Subsingleton.elim i 0]
  simp [ChannelCode.maxErrProb, this]

/-- **Theorem 7.7.1 (The channel coding theorem, achievability).** All rates below capacity are
achievable: for every `R < C` there is a sequence of `(⌈e^{nR}⌉, n)` codes with maximal
probability of error `λ^(n) → 0`. -/
theorem isAchievableRate_of_lt_capacity [Nonempty α] {W : α → β → ℝ} (hW : IsChannel W)
    {R : ℝ} (hR : R < capacity W) : IsAchievableRate W R := by
  rcases le_or_gt R 0 with hR0 | hR0
  · -- With `R ≤ 0` there is a single message.
    have h1 : ∀ n : ℕ, ⌈exp (n * R)⌉₊ = 1 := fun n => by
      rw [Nat.ceil_eq_iff one_ne_zero]
      refine ⟨by simp [exp_pos], ?_⟩
      have : (n : ℝ) * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0
      simpa using exp_le_one_iff.2 this
    choose c hc using fun n : ℕ => exists_code_maxErrProb_eq_zero W (h1 n) n
    exact ⟨c, by simp [hc]⟩
  -- Choose `p` achieving capacity and `ε = (C - R)/4`, so that `R = I(X;Y) - 4ε`.
  obtain ⟨p, hp, hpC⟩ := exists_capacity_eq hW
  set ε := (capacity W - R) / 4 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set A := fun n : ℕ => jointTypicalSet (jointOf p W) n ε
  set U : ℕ → ℝ := fun n => (1 - prob (jointIid (jointOf p W) n) (A n)) +
    (2 * ⌈exp (n * R)⌉₊ - 1) * exp (-(n * (mutualInfoOf p W - 3 * ε)))
  -- For each `n`, a random code with `2⌈e^{nR}⌉` codewords and its better half, (7.80)–(7.81).
  have hcode : ∀ n : ℕ, ∃ c : ChannelCode ⌈exp (n * R)⌉₊ n α β, c.maxErrProb W ≤ 2 * U n := by
    intro n
    have hM := one_le_ceil_exp (n * R)
    obtain ⟨c₀, hc₀⟩ := exists_code_avgErrProb_le (M := 2 * ⌈exp (n * R)⌉₊) hp hW
      (by omega) n ε
    obtain ⟨c, hc⟩ := ChannelCode.exists_maxErrProb_le_two_mul hW (by omega) c₀
    refine ⟨c, hc.trans ?_⟩
    push_cast at hc₀
    exact mul_le_mul_of_nonneg_left hc₀ (by norm_num)
  choose c hc using hcode
  refine ⟨c, ?_⟩
  -- `U n → 0`: the joint AEP and `(2⌈e^{nR}⌉ - 1) e^{-n(R+ε)} ≤ 2 e^{-nε} + 2 e^{-n(R+ε)}`.
  have hbound : ∀ n : ℕ, U n ≤ (1 - prob (jointIid (jointOf p W) n) (A n)) +
      (2 * exp (-(n * ε)) + 2 * exp (-(n * (R + ε)))) := by
    intro n
    have hceil : (⌈exp (n * R)⌉₊ : ℝ) ≤ exp (n * R) + 1 :=
      (Nat.ceil_lt_add_one (exp_pos _).le).le
    have hI : mutualInfoOf p W - 3 * ε = R + ε := by rw [hpC, hε_def]; ring
    have hpos : 0 ≤ exp (-(n * (R + ε))) := (exp_pos _).le
    have hexp : exp (n * R) * exp (-(n * (R + ε))) = exp (-(n * ε)) := by
      rw [← exp_add]; ring_nf
    have key : (2 * (⌈exp (n * R)⌉₊ : ℝ) - 1) * exp (-(n * (R + ε))) ≤
        2 * exp (-(n * ε)) + 2 * exp (-(n * (R + ε))) := by
      have h2 : 2 * (⌈exp (n * R)⌉₊ : ℝ) - 1 ≤ 2 * (exp (n * R) + 1) := by linarith
      calc (2 * (⌈exp (n * R)⌉₊ : ℝ) - 1) * exp (-(n * (R + ε)))
          ≤ 2 * (exp (n * R) + 1) * exp (-(n * (R + ε))) := mul_le_mul_of_nonneg_right h2 hpos
        _ = _ := by rw [← hexp]; ring
    simp only [U, hI]
    linarith
  have hlim : Tendsto (fun n : ℕ => (1 - prob (jointIid (jointOf p W) n) (A n)) +
      (2 * exp (-(n * ε)) + 2 * exp (-(n * (R + ε))))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 1 - prob (jointIid (jointOf p W) n) (A n)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_jointTypicalSet (jointOf_isPMF hp hW) hε).const_sub 1
    have h2 := ((tendsto_exp_neg_mul_nat hε).const_mul 2).add
      ((tendsto_exp_neg_mul_nat (by linarith : 0 < R + ε)).const_mul 2)
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim.const_mul 2) (fun n => (c n).maxErrProb_nonneg hW) fun n => ?_
  exact (hc n).trans (mul_le_mul_of_nonneg_left (hbound n) (by norm_num))

end InfoTheory
