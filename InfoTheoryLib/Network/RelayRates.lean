/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayMarkov

/-!
# The relay channel: from block codes to achievable rates

Codes for one block, for all large `n`, give achievable rates for the relay channel.

## Main statements

* `RCCode.errProb_eq`: the probability of error as an expectation.
* `RCCode.pad`, `RCCode.errProb_pad`: a code still works when the block length is increased.
* `RCCode.exists_sub`: a code still works with fewer messages.
* `exists_seq_tendsto`: a sequence of codes from codes for each `ε`.
* `isAchievableRC_of_codes`: **codes of many blocks give achievable rates**.
* `isAchievableRC_of_blocks`: **codes for one block give achievable rates**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X X₁ Y Y₁ : Type*} [Fintype Y] [Fintype Y₁] {M N : ℕ} {W : X × X₁ → Y × Y₁ → ℝ}

/-- The probability of error as an expectation. -/
lemma RCCode.errProb_eq (c : RCCode M N X X₁ Y Y₁) :
    c.errProb W = ∑ ω, c.law W N ω * ind (c.dec (rcY ω) ≠ ω.1) := by
  classical
  simp only [RCCode.errProb, InfoTheory.errProb]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : c.dec (rcY ω) = ω.1
  · have hne : ¬ c.dec (rcY ω) ≠ ω.1 := not_not.mpr h
    rw [ind_of_neg hne, mul_zero]
    exact ite_eq_right hne
  · rw [ind_of_pos h, mul_one]
    exact ite_eq_left h

/-! ### Padding -/

/-- A code for a longer block: the decoder ignores the last symbols. -/
def RCCode.pad (c : RCCode M N X X₁ Y Y₁) (m : ℕ) : RCCode M (N + m) X X₁ Y Y₁ where
  enc := c.enc
  relay := c.relay
  dec y := c.dec fun i => y (Fin.castAdd m i)

/-- Padding does not change the probability of error. -/
theorem RCCode.errProb_pad (c : RCCode M N X X₁ Y Y₁) (hW : IsChannel W) (m : ℕ) :
    (c.pad m).errProb W = c.errProb W := by
  classical
  have key : ∀ m : ℕ, ∑ ω : Fin M × (Fin (N + m) → Y × Y₁), c.law W (N + m) ω *
      ind (c.dec (fun i => (ω.2 (Fin.castAdd m i)).1) ≠ ω.1) =
      ∑ ω, c.law W N ω * ind (c.dec (rcY ω) ≠ ω.1) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have hm := sum_dist_mul (c.law W (N + m + 1)) (fun z => (z.1, Fin.init z.2))
        (fun ω : Fin M × (Fin (N + m) → Y × Y₁) =>
          ind (c.dec (fun i => (ω.2 (Fin.castAdd m i)).1) ≠ ω.1))
      have hd : dist (c.law W (N + m + 1)) (fun z => (z.1, Fin.init z.2)) = c.law W (N + m) :=
        dist_fbLaw_init hW (N + m)
      rw [hd] at hm
      exact hm.symm.trans ih
  rw [errProb_eq, errProb_eq]
  exact key m

/-! ### Fewer messages -/

/-- The window of `M'` messages starting at `s`. -/
lemma exists_window [NeZero M] {M' : ℕ} (h : M' ≤ M) (f : Fin M → ℝ) :
    ∃ s : Fin M, (∑ t : Fin M', f (s + Fin.castLE h t)) * M ≤ (∑ w, f w) * M' := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ s : Fin M, (∑ t : Fin M', f (s + Fin.castLE h t)) = M' * ∑ w, f w := by
    rw [sum_comm]
    have hin : ∀ t : Fin M', ∑ s : Fin M, f (s + Fin.castLE h t) = ∑ w, f w := fun t =>
      Equiv.sum_comp (Equiv.addRight (Fin.castLE h t)) f
    simp only [hin, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : (univ : Finset (Fin M)).Nonempty := univ_nonempty
  have hlt := sum_lt_sum_of_nonempty hne fun s _ => hcon s
  rw [← sum_mul, ← sum_mul, hsum] at hlt
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  have : (M : ℝ) * (∑ w, f w) * M' = M' * (∑ w, f w) * M := by ring
  linarith

/-- **Fewer messages.** A code still works with fewer messages: the best window of messages has at
most the average error. -/
theorem RCCode.exists_sub [NeZero M] (c : RCCode M N X X₁ Y Y₁) {M' : ℕ} (hM' : 0 < M')
    (h : M' ≤ M) (hW : IsChannel W) :
    ∃ c' : RCCode M' N X X₁ Y Y₁, c'.errProb W ≤ c.errProb W := by
  classical
  have : NeZero M' := ⟨hM'.ne'⟩
  have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hM'pos : (0 : ℝ) < M' := by exact_mod_cast hM'
  -- the error of a message
  let P : Fin M → (Fin N → Y × Y₁) → ℝ := fun w z =>
    ∏ i : Fin N, W (c.fbEnc i w fun t : Fin i => z ⟨t, t.2.trans i.2⟩) (z i)
  have hP0 : ∀ w z, 0 ≤ P w z := fun w z => prod_nonneg fun i _ => (hW _).nonneg _
  let f : Fin M → ℝ := fun w => ∑ z, P w z * ind (c.dec (fun i => (z i).1) ≠ w)
  have hc : c.errProb W = (∑ w, f w) / M := by
    rw [errProb_eq, Fintype.sum_prod_type, sum_div]
    refine sum_congr rfl fun w _ => ?_
    simp only [f, sum_div]
    refine sum_congr rfl fun z _ => ?_
    have hl := fbLaw_eq_prod (ν := uniformPMF (Fin M)) (W := W) (enc := c.fbEnc) N w z
    rw [RCCode.law, hl]
    simp only [uniformPMF, Fintype.card_fin]
    field_simp
    rfl
  obtain ⟨s, hs⟩ := exists_window h f
  let ι : Fin M' → Fin M := fun t => s + Fin.castLE h t
  have hι : Function.Injective ι := fun a b hab =>
    Fin.castLE_injective h (add_left_cancel hab)
  let c' : RCCode M' N X X₁ Y Y₁ :=
    ⟨fun k t => c.enc k (ι t), c.relay, fun y =>
      if hy : ∃ t, ι t = c.dec y then Classical.choose hy else 0⟩
  refine ⟨c', ?_⟩
  have hrow : ∀ t : Fin M', (∑ z : Fin N → Y × Y₁, (∏ i : Fin N, W (c'.fbEnc i t fun u : Fin i =>
      z ⟨u, u.2.trans i.2⟩) (z i)) * ind (c'.dec (fun i => (z i).1) ≠ t)) ≤ f (ι t) := by
    intro t
    refine sum_le_sum fun z _ => ?_
    refine mul_le_mul_of_nonneg_left (ind_mono ?_) (hP0 (ι t) z)
    intro hne heq
    refine hne ?_
    have hy : ∃ t', ι t' = c.dec (fun i => (z i).1) := ⟨t, heq.symm⟩
    change (if hy : ∃ t, ι t = c.dec fun i => (z i).1 then Classical.choose hy else 0) = t
    rw [dite_eq_left hy]
    exact hι ((Classical.choose_spec hy).trans heq)
  have hc' : c'.errProb W =
    (∑ t, ∑ z : Fin N → Y × Y₁, (∏ i : Fin N, W (c'.fbEnc i t fun u : Fin i =>
      z ⟨u, u.2.trans i.2⟩) (z i)) * ind (c'.dec (fun i => (z i).1) ≠ t)) / M' := by
    rw [errProb_eq, Fintype.sum_prod_type, sum_div]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun z _ => ?_
    have hl := fbLaw_eq_prod (ν := uniformPMF (Fin M')) (W := W) (enc := c'.fbEnc) N w z
    rw [RCCode.law, hl]
    simp only [uniformPMF, Fintype.card_fin]
    field_simp
    rfl
  rw [hc', hc, div_le_div_iff₀ hM'pos hMpos]
  calc _ ≤ (∑ t : Fin M', f (ι t)) * M :=
        mul_le_mul_of_nonneg_right (sum_le_sum fun t _ => hrow t) hMpos.le
    _ ≤ _ := hs

/-! ### Sequences of codes -/

/-- A sequence of codes whose errors tend to zero, from codes with small errors. -/
lemma exists_seq_tendsto {C : ℕ → Type*} [∀ n, Nonempty (C n)] (g : ∀ n, C n → ℝ)
    (h0 : ∀ n c, 0 ≤ g n c) (h : ∀ ε > 0, ∀ᶠ n in atTop, ∃ c, g n c ≤ ε) :
    ∃ c : ∀ n, C n, Tendsto (fun n => g n (c n)) atTop (𝓝 0) := by
  classical
  have hbdd : ∀ n, BddBelow (Set.range (g n)) := fun n => ⟨0, by
    rintro _ ⟨c, rfl⟩
    exact h0 n c⟩
  have hex : ∀ n : ℕ, ∃ c, g n c < sInf (Set.range (g n)) + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (Set.range_nonempty (g n))
      (lt_add_of_pos_right (sInf (Set.range (g n))) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    exact ⟨c, hc⟩
  choose c hc using hex
  refine ⟨c, tendsto_order.mpr ⟨fun a ha => Eventually.of_forall fun n =>
    lt_of_lt_of_le ha (h0 n _), fun a ha => ?_⟩⟩
  have h₁ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [h (a / 2) (by positivity), (tendsto_order.mp h₁).2 (a / 2) (by positivity)]
    with n ⟨c', hc'⟩ hn
  have hinf : sInf (Set.range (g n)) ≤ a / 2 := (csInf_le (hbdd n) ⟨c', rfl⟩).trans hc'
  have := hc n
  linarith

/-! ### From block codes to rates -/

section Rates

variable [Fintype X] [Fintype X₁] [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]

instance (M N : ℕ) [NeZero M] : Nonempty (RCCode M N X X₁ Y Y₁) :=
  ⟨⟨fun _ _ => Classical.arbitrary _, fun _ _ => Classical.arbitrary _, fun _ => 0⟩⟩

instance (a : ℕ) : NeZero (2 ^ a) := ⟨by positivity⟩

omit [Fintype X] [Fintype X₁] [Nonempty Y] [Nonempty Y₁] in
/-- **Codes of many blocks give achievable rates.** For every number of blocks `B₁ + 1` and for all
large `n`, let there be codes of `(B₁ + 1) n` uses of the channel, with error as small as we wish
and at least `exp (B₁ n ρ)` messages. Then every rate `R`, in bits, with `R log 2 < ρ` is
achievable. -/
theorem isAchievableRC_of_codes {ρ R : ℝ} (hρ0 : 0 ≤ ρ) (hR : R * log 2 < ρ) (hW : IsChannel W)
    (hcode : ∀ B₁ : ℕ, 0 < B₁ → ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (M₀ : ℕ)
      (c : RCCode M₀ ((B₁ + 1) * n) X X₁ Y Y₁), 0 < M₀ ∧
        exp ((B₁ : ℝ) * ((n : ℝ) * ρ)) ≤ (M₀ : ℝ) ∧ c.errProb W ≤ ε) :
    IsAchievableRC W R := by
  classical
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  set gap := ρ - R * log 2 with hgap
  have hgap0 : 0 < gap := sub_pos.mpr hR
  -- the number of blocks
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ρ / gap < B := exists_nat_gt _
  have hBpos : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  set B₁ := B + 1 with hB₁
  have hB₁pos : (0 : ℝ) < (B₁ : ℝ) + 1 := by positivity
  have hη : 0 < (B₁ : ℝ) / (B₁ + 1) * ρ - R * log 2 := by
    have h₁ : ρ / gap < (B₁ : ℝ) + 1 := by
      have : (B : ℝ) < (B₁ : ℝ) + 1 := by
        simp only [hB₁]
        push_cast
        linarith
      linarith
    rw [div_lt_iff₀ hgap0] at h₁
    have h₂ : (B₁ : ℝ) / (B₁ + 1) * ρ - R * log 2 = (((B₁ : ℝ) + 1) * gap - ρ) / (B₁ + 1) := by
      simp only [hgap]
      field_simp
      ring
    rw [h₂]
    exact div_pos (by linarith) hB₁pos
  set η := (B₁ : ℝ) / (B₁ + 1) * ρ - R * log 2 with hηdef
  have key : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∃ c : RCCode (2 ^ ⌈(N : ℝ) * R⌉₊) N X X₁ Y Y₁,
      c.errProb W ≤ ε := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hcode B₁ (by simp [hB₁]) ε hε)
    have hdiv : Tendsto (fun N : ℕ => N / (B₁ + 1)) atTop atTop :=
      Nat.tendsto_div_const_atTop (Nat.succ_ne_zero B₁)
    have hev : ∀ᶠ N : ℕ in atTop, (B₁ : ℝ) * ρ + log 2 ≤ (N : ℝ) * η :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hη |>.eventually_ge_atTop _
    filter_upwards [hdiv.eventually_ge_atTop (n₀ + 1), hev] with N hN₁ hN₂
    obtain ⟨n, hn⟩ : ∃ n, n = N / (B₁ + 1) := ⟨_, rfl⟩
    rw [← hn] at hN₁
    obtain ⟨M₀, c₀, hM₀pos, hexp, hc₀⟩ := hn₀ n (by omega)
    obtain ⟨m, hm⟩ : ∃ m, N = (B₁ + 1) * n + m :=
      Nat.exists_eq_add_of_le (by rw [hn]; exact Nat.mul_div_le N (B₁ + 1))
    have hNreal : (N : ℝ) / ((B₁ : ℝ) + 1) < (n : ℝ) + 1 := by
      have h₀ : N < (B₁ + 1) * (n + 1) := by
        rw [hn]
        exact Nat.lt_mul_div_succ N (Nat.succ_pos B₁)
      have h₀' : (N : ℝ) < ((B₁ : ℝ) + 1) * ((n : ℝ) + 1) := by exact_mod_cast h₀
      rw [div_lt_iff₀ hB₁pos]
      linarith
    have hne₀ : NeZero M₀ := ⟨hM₀pos.ne'⟩
    have hrate : 2 ^ ⌈(N : ℝ) * R⌉₊ ≤ M₀ := by
      by_cases hR0 : (N : ℝ) * R ≤ 0
      · rw [Nat.ceil_eq_zero.mpr hR0, pow_zero]
        exact hM₀pos
      · push Not at hR0
        have hceil : ((⌈(N : ℝ) * R⌉₊ : ℕ) : ℝ) < (N : ℝ) * R + 1 := Nat.ceil_lt_add_one hR0.le
        have h₂ : ((2 ^ ⌈(N : ℝ) * R⌉₊ : ℕ) : ℝ) ≤ (M₀ : ℝ) := by
          refine le_trans ?_ hexp
          push_cast
          rw [← exp_log (by norm_num : (0 : ℝ) < 2), ← exp_nat_mul]
          refine exp_le_exp.mpr ?_
          have h₃ : (B₁ : ℝ) * ((N : ℝ) / ((B₁ : ℝ) + 1) * ρ) = (N : ℝ) *
            ((B₁ : ℝ) / (B₁ + 1) * ρ) := by
            field_simp
          have h₄ : (N : ℝ) / ((B₁ : ℝ) + 1) * ρ ≤ ((n : ℝ) + 1) * ρ :=
            mul_le_mul_of_nonneg_right hNreal.le hρ0
          have h₅ : (B₁ : ℝ) * ((N : ℝ) / ((B₁ : ℝ) + 1) * ρ) ≤ (B₁ : ℝ) * (((n : ℝ) + 1) * ρ) :=
            mul_le_mul_of_nonneg_left h₄ (Nat.cast_nonneg _)
          have h₆ : ((⌈(N : ℝ) * R⌉₊ : ℕ) : ℝ) * log 2 ≤ ((N : ℝ) * R + 1) * log 2 :=
            mul_le_mul_of_nonneg_right hceil.le hlog2.le
          have h₇ : (N : ℝ) * η = (N : ℝ) * ((B₁ : ℝ) / (B₁ + 1) * ρ) - (N : ℝ) * R * log 2 := by
            simp only [hηdef]
            ring
          nlinarith
        exact_mod_cast h₂
    subst hm
    obtain ⟨c', hc'⟩ := (c₀.pad m).exists_sub (by positivity) hrate hW
    exact ⟨c', hc'.trans ((c₀.errProb_pad hW m).trans_le hc₀)⟩
  exact exists_seq_tendsto (C := fun N : ℕ => RCCode (2 ^ ⌈(N : ℝ) * R⌉₊) N X X₁ Y Y₁)
    (fun N c => c.errProb W) (fun N c => errProb_nonneg (c.law_isPMF (by positivity) hW N) _ _ _)
      key

omit [Fintype X] [Fintype X₁] in
/-- **Codes for one block give achievable rates.** Let the block codes have rates `R'` and `R''` in
nats. Then every rate `R`, in bits, with `R log 2 < R' + R''` is achievable. -/
theorem isAchievableRC_of_blocks {R' R'' R : ℝ} (hR' : 0 ≤ R') (hR'' : 0 ≤ R'')
    (hR : R * log 2 < R' + R'') (hW : IsChannel W)
    (hblock : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, ∃ C : RelayBlock ⌈exp (n * R')⌉₊ ⌈exp (n * R'')⌉₊
      (Fin n → X₁) (Fin n → X) (Fin n → Y) (Fin n → Y₁), C.avgErr (relaySeq W n) ≤ δ) :
    IsAchievableRC W R := by
  classical
  refine isAchievableRC_of_codes (add_nonneg hR' hR'') hR hW fun B₁ hB₁ ε hε => ?_
  have hB₁pos : (0 : ℝ) < (B₁ : ℝ) + 1 := by positivity
  have hδ : 0 < ε / ((B₁ : ℝ) + 1) := by positivity
  filter_upwards [hblock _ hδ, eventually_gt_atTop 0] with n ⟨C, hC⟩ hn0
  have hnpos : NeZero n := ⟨hn0.ne'⟩
  set M₀ := ⌈exp (n * R')⌉₊ ^ B₁ * ⌈exp (n * R'')⌉₊ ^ B₁ with hM₀
  have hM₀pos : 0 < M₀ := by positivity
  have hne₀ : NeZero M₀ := ⟨hM₀pos.ne'⟩
  have hexp : exp ((B₁ : ℝ) * ((n : ℝ) * (R' + R''))) ≤ (M₀ : ℝ) := by
    have h₁ : exp (n * R') ≤ ((⌈exp (n * R')⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h₂ : exp (n * R'') ≤ ((⌈exp (n * R'')⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h₃ : exp ((B₁ : ℝ) * ((n : ℝ) * (R' + R''))) =
        exp (n * R') ^ B₁ * exp (n * R'') ^ B₁ := by
      rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
      congr 1
      ring
    rw [h₃, hM₀]
    push_cast
    exact mul_le_mul (pow_le_pow_left₀ (exp_pos _).le h₁ _) (pow_le_pow_left₀ (exp_pos _).le h₂ _)
      (by positivity) (by positivity)
  let e : Fin M₀ ≃ MarkovMsg ⌈exp (n * R')⌉₊ ⌈exp (n * R'')⌉₊ B₁ :=
    (Fintype.equivFinOfCardEq (by simp [hM₀])).symm
  refine ⟨M₀, C.markov (X := X) (X₁ := X₁) e (Classical.arbitrary Y₁) (Classical.arbitrary Y),
    hM₀pos, hexp, ?_⟩
  refine (C.markov_errProb_le hB₁ hW e _ _).trans ?_
  calc _ ≤ ((B₁ : ℝ) + 1) * (ε / ((B₁ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hC hB₁pos.le
    _ = ε := by field_simp

end Rates

end InfoTheory
