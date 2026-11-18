/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.Shannon

/-!
# Secure communication over a DMC with a shared key

Theorem 2 of Lecture 23 of El Gamal and Kim. The sender and the receiver share a key of rate `R_K`,
and the eavesdropper observes the output of the channel. With the information leakage rate
`(1/n) I(M; Yⁿ) → 0`, the secrecy capacity is `min {R_K, max_{p(x)} I(X; Y)}`.

## Main definitions

* `KeyedSecrecyCode M K n α β`: a code, with a randomized encoder.
* `IsAchievableKeyed`, `keyedSecrecyCapacity`: the secrecy capacity, in bits.

## Main statements

* `KeyedSecrecyCode.one_sub_errProb_mul_log_le_key`, `.one_sub_errProb_mul_log_le_capacity`: the
  two bounds of the converse for one code.
* `padCode`, `padCode_leakage`, `padCode_errProb`: the one-time pad on the message of a channel
  code. Its leakage is `0`.
* `keyedSecrecyCapacity_eq`: **Theorem 2 of Lecture 23**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- The limit in the converse proofs of this folder: if, for all `ε` and all large `n`,
`(1 - ε) n a ≤ n (b + ε) + c`, then `a ≤ b`. -/
lemma le_of_forall_eventually_mul_le {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ ε > 0, ∃ c : ℝ, ∀ᶠ n : ℕ in atTop, (1 - ε) * (n * a) ≤ n * (b + ε) + c) : a ≤ b := by
  by_contra hab
  push Not at hab
  set δ := (a - b) / (2 * (a + 2)) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
  have hδa : δ * (a + 1) ≤ (a - b) / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨c, hc⟩ := h δ hδ0
  set g := (a - b) / 2 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  obtain ⟨n, hn, hn1⟩ := (hc.and (eventually_gt_atTop ⌈c / g⌉₊)).exists
  have h₁ : c / g < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
  rw [div_lt_iff₀ hg0] at h₁
  have h₂ : (n : ℝ) * g ≤ n * (a - b - δ * (a + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
  nlinarith

/-- The number of messages `2 ^ ⌈nR⌉` has `log ≥ n R log 2`. -/
lemma le_log_two_pow_ceil (n : ℕ) (R : ℝ) :
    n * (R * log 2) ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := by
  have hl := log_pos one_lt_two
  push_cast
  rw [log_pow]
  have := Nat.le_ceil ((n : ℝ) * R)
  nlinarith

/-- The number of messages `2 ^ ⌈nR⌉` has `log ≤ n R log 2 + log 2`. -/
lemma log_two_pow_ceil_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ n * (R * log 2) + log 2 := by
  have hl := log_pos one_lt_two
  push_cast
  rw [log_pow]
  have := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) hR)
  nlinarith

/-- The law of `(g(A), C)` when `C` is the output of the channel `κ` from `g(A)`. -/
lemma dist_jointOf_comp_pair {A B C : Type*} [Fintype A] [Fintype C] (q : A → ℝ) {κ : B → C → ℝ}
    {g : A → B} (b : B) (y : C) :
    dist (jointOf q fun a => κ (g a)) (pair (g ∘ Prod.fst) Prod.snd) (b, y) =
      dist q g b * κ b y := by
  classical
  simp only [dist, pair, jointOf, Function.comp, Prod.mk.injEq, Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single y (fun c _ hc => by simp [hc]) (by simp)]
  by_cases h : g a = b
  · simp [h]
  · simp [h]

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Lecture 23 of [elgamal2010], page 23-5.** A code for the DMC with a shared key: a randomized
encoder `p(xⁿ | m, k)` and a decoder `m̂(yⁿ, k)`. The notes also allow an error message, which does
not help. -/
structure KeyedSecrecyCode (M K n : ℕ) (α β : Type*) [Fintype α] where
  /-- The randomized encoder. -/
  enc : Fin M × Fin K → (Fin n → α) → ℝ
  /-- Each row of the encoder is a pmf. -/
  isChannel_enc : IsChannel enc
  /-- The decoder. -/
  dec : (Fin n → β) → Fin K → Fin M

namespace KeyedSecrecyCode

variable {M K n : ℕ} (W : α → β → ℝ) (c : KeyedSecrecyCode M K n α β)

/-- The law of `((M, K), Xⁿ)`, for a uniform message and an independent uniform key. -/
def inputLaw : (Fin M × Fin K) × (Fin n → α) → ℝ := jointOf (uniformPMF _) c.enc

/-- The law of `(((M, K), Xⁿ), Yⁿ)`. -/
def law : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) → ℝ :=
  jointOf c.inputLaw fun z => channelExt W n z.2

/-- The probability of error `P{M ≠ M̂(Yⁿ, K)}`. -/
def errProb : ℝ :=
  InfoTheory.errProb (c.law W) (fun z => z.1.1.1) (fun z => (z.2, z.1.1.2)) fun w => c.dec w.1 w.2

/-- The information leakage `I(M; Yⁿ)`, which is `n` times the leakage rate. -/
def leakage : ℝ := I[fun z => z.1.1.1 : Prod.snd ; c.law W]

variable {W c}

omit [Fintype β] in
lemma inputLaw_isPMF [NeZero M] [NeZero K] : IsPMF c.inputLaw := by
  have : Nonempty (Fin M × Fin K) := ⟨(0, 0)⟩
  exact jointOf_isPMF uniformPMF_isPMF c.isChannel_enc

lemma law_isPMF [NeZero M] [NeZero K] (hW : IsChannel W) : IsPMF (c.law W) :=
  jointOf_isPMF inputLaw_isPMF fun z => hW.ext n z.2

/-- The law of `(M, K)` is uniform. -/
lemma dist_pair_key [NeZero M] [NeZero K] (hW : IsChannel W) (z : Fin M × Fin K) :
    dist (c.law W) (fun z => z.1.1) z = 1 / (M * K) := by
  have : Nonempty (Fin M × Fin K) := ⟨(0, 0)⟩
  have h := dist_comp_eq (c.law W) Prod.fst (Prod.fst : (Fin M × Fin K) × (Fin n → α) → _)
  have h' : dist (c.law W) (fun z => z.1.1) = dist c.inputLaw Prod.fst := by
    have e : dist (c.law W) Prod.fst = c.inputLaw := dist_jointOf_fst fun z => hW.ext n z.2
    rw [e] at h
    exact h
  rw [h', inputLaw, dist_jointOf_fst c.isChannel_enc]
  simp [uniformPMF]

lemma entropy_message [NeZero M] [NeZero K] (hW : IsChannel W) :
    H[fun z => z.1.1.1 ; c.law W] = log M := by
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h := dist_comp_eq (c.law W) (fun z => z.1.1) (Prod.fst : Fin M × Fin K → _)
  have e : dist (c.law W) (fun z => z.1.1.1) = uniformPMF (Fin M) := by
    funext m
    have h₁ : dist (c.law W) (fun z => z.1.1.1) m =
        dist (dist (c.law W) fun z => z.1.1) Prod.fst m := by
      rw [← dist_comp_eq]
      rfl
    rw [h₁, dist_fst]
    simp only [dist_pair_key hW, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, uniformPMF]
    field_simp
  rw [entropyRV, e, entropy_uniformPMF, Fintype.card_fin]

/-- The message and the key are independent. -/
lemma mutualInfo_message_key [NeZero M] [NeZero K] (hW : IsChannel W) :
    I[fun z => z.1.1.1 : fun z => z.1.1.2 ; c.law W] = 0 := by
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [mutualInfo_eq_zero_iff (law_isPMF hW)]
  intro m k
  have hpair : dist (c.law W) (pair (fun z => z.1.1.1) fun z => z.1.1.2) (m, k) =
      1 / (M * K) := by
    have : (pair (fun z : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) => z.1.1.1)
        fun z => z.1.1.2) = fun z => z.1.1 := rfl
    rw [this, dist_pair_key hW]
  have hm : dist (c.law W) (fun z => z.1.1.1) m = 1 / M := by
    have h₁ : dist (c.law W) (fun z => z.1.1.1) m =
        dist (dist (c.law W) fun z => z.1.1) Prod.fst m := by
      rw [← dist_comp_eq]
      rfl
    rw [h₁, dist_fst]
    simp only [dist_pair_key hW, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hk : dist (c.law W) (fun z => z.1.1.2) k = 1 / K := by
    have h₁ : dist (c.law W) (fun z => z.1.1.2) k =
        dist (dist (c.law W) fun z => z.1.1) Prod.snd k := by
      rw [← dist_comp_eq]
      rfl
    rw [h₁, dist_snd]
    simp only [dist_pair_key hW, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hpair, hm, hk]
  field_simp

/-- **Page 23-3 of [elgamal2010], for a noisy channel: the bound by the key.**
`(1 - Pₑ) log M ≤ I(M; Yⁿ) + log K + log 2`. -/
theorem one_sub_errProb_mul_log_le_key [NeZero M] [NeZero K] (hW : IsChannel W) :
    (1 - c.errProb W) * log M ≤ c.leakage W + log K + log 2 := by
  have hμ := law_isPMF (c := c) hW
  set M' : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) → Fin M := fun z => z.1.1.1
  set K' : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) → Fin K := fun z => z.1.1.2
  have hF := fano_weak hμ M' (pair Prod.snd K') fun w => c.dec w.1 w.2
  rw [Fintype.card_fin] at hF
  have h₁ := mutualInfo_eq_entropy_sub_condEntropy hμ M' Prod.snd
  have h₂ := chain_rule_cond hμ K' M' Prod.snd
  have h₃ := chain_rule_cond hμ M' K' Prod.snd
  have h₄ : H[pair M' K' | Prod.snd ; c.law W] = H[pair K' M' | Prod.snd ; c.law W] :=
    condEntropy_congr_left hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have h₅ : H[M' | pair K' Prod.snd ; c.law W] = H[M' | pair Prod.snd K' ; c.law W] :=
    condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have h₆ := condEntropy_nonneg hμ K' (pair M' Prod.snd)
  have h₇ := (condEntropy_le_entropy hμ K' (Prod.snd)).trans (entropyRV_le_log_card hμ K')
  rw [Fintype.card_fin] at h₇
  have h₈ := entropy_message (c := c) hW
  have h₉ : c.leakage W = I[M' : Prod.snd ; c.law W] := rfl
  have h₁₀ : c.errProb W = InfoTheory.errProb (c.law W) M' (pair Prod.snd K')
    (fun w => c.dec w.1 w.2) := rfl
  rw [← h₁₀] at hF
  rw [h₉]
  nlinarith

/-- **Page 23-6 of [elgamal2010]: the bound by the capacity.**
`(1 - Pₑ) log M ≤ n C + log 2`. -/
theorem one_sub_errProb_mul_log_le_capacity [NeZero M] [NeZero K] [Nonempty α] (hW : IsChannel W) :
    (1 - c.errProb W) * log M ≤ n * capacity W + log 2 := by
  have hμ := law_isPMF (c := c) hW
  set M' : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) → Fin M := fun z => z.1.1.1
  set K' : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) → Fin K := fun z => z.1.1.2
  set A : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) → Fin M × Fin K := fun z => z.1.1
  set X : ((Fin M × Fin K) × (Fin n → α)) × (Fin n → β) → Fin n → α := fun z => z.1.2
  have hF := fano_weak hμ M' (pair Prod.snd K') fun w => c.dec w.1 w.2
  rw [Fintype.card_fin] at hF
  have h₁ := mutualInfo_eq_entropy_sub_condEntropy hμ M' (pair Prod.snd K')
  have h₂ := chain_rule_mutualInfo₂ hμ M' Prod.snd K'
  have h₃ := mutualInfo_message_key (c := c) hW
  have h₄ : I[M' : Prod.snd | K' ; c.law W] = H[Prod.snd | K' ; c.law W] -
      H[Prod.snd | pair M' K' ; c.law W] := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
  have h₅ := condEntropy_le_entropy hμ Prod.snd K'
  -- `H(Yⁿ | M, K) ≥ H(Yⁿ | Xⁿ)`.
  have h₆ : H[Prod.snd | X ; c.law W] ≤ H[Prod.snd | pair M' K' ; c.law W] := by
    have e₁ : H[Prod.snd | Prod.fst ; c.law W] = H[Prod.snd | X ; c.law W] :=
      condEntropy_jointOf_comp inputLaw_isPMF (hW.ext n) Prod.snd
    have e₂ : H[Prod.snd | pair X A ; c.law W] = H[Prod.snd | Prod.fst ; c.law W] :=
      condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
    have e₃ := condEntropy_le_condEntropy hμ (Prod.snd) X A
    have e₄ : H[Prod.snd | pair M' K' ; c.law W] = H[Prod.snd | A ; c.law W] := rfl
    linarith
  -- `I(Xⁿ; Yⁿ) ≤ n C`.
  have h₇ : H[Prod.snd ; c.law W] - H[Prod.snd | X ; c.law W] ≤ n * capacity W := by
    have hP : IsPMF (dist (c.law W) X) := hμ.dist X
    have hk := mutualInfo_channelExt_le (W := W) hP hW
    refine le_trans (le_of_eq ?_) hk
    rw [← mutualInfo_eq_entropy_sub_condEntropy' hμ]
    refine mutualInfo_eq_of_dist_pair_eq ?_
    funext ⟨x, y⟩
    rw [dist_pair_fst_snd]
    exact dist_jointOf_comp_pair (κ := channelExt W n) (g := Prod.snd) c.inputLaw x y |>.trans (by
      congr 1
      have e := dist_comp_eq (c.law W) Prod.fst (Prod.snd : (Fin M × Fin K) × (Fin n → α) → _)
      have e' : dist (c.law W) Prod.fst = c.inputLaw := dist_jointOf_fst fun z => hW.ext n z.2
      rw [e'] at e
      exact (congrFun e x).symm)
  have h₈ := entropy_message (c := c) hW
  have h₁₀ : c.errProb W = InfoTheory.errProb (c.law W) M' (pair Prod.snd K')
    (fun w => c.dec w.1 w.2) := rfl
  rw [← h₁₀] at hF
  nlinarith

end KeyedSecrecyCode

/-- **Page 23-6 of [elgamal2010].** A rate `R`, in bits, is achievable at the key rate `R_K` if for
every `ε` and all large `n` there is a code with `2 ^ ⌈nR⌉` messages and `2 ^ ⌈nR_K⌉` keys, with
probability of error at most `ε` and leakage rate at most `ε`. -/
def IsAchievableKeyed (W : α → β → ℝ) (R RK : ℝ) : Prop :=
  0 ≤ R ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    ∃ c : KeyedSecrecyCode (2 ^ ⌈n * R⌉₊) (2 ^ ⌈n * RK⌉₊) n α β,
      c.errProb W ≤ ε ∧ c.leakage W ≤ n * ε

/-- **Page 23-6 of [elgamal2010].** The secrecy capacity `C(R_K)`, in bits. -/
def keyedSecrecyCapacity (W : α → β → ℝ) (RK : ℝ) : ℝ := sSup {R | IsAchievableKeyed W R RK}

/-! ### The one-time pad on a channel code -/

section Pad

variable {M d n : ℕ} [NeZero M] {W : α → β → ℝ}

/-- The part of the key that the pad uses. With `M * d` keys, each index has `d` keys. -/
def padKey (M d : ℕ) (k : Fin (M * d)) : Fin M := (finProdFinEquiv.symm k).1

omit [NeZero M] in
/-- A sum over the keys of a function of the part of the key that the pad uses. -/
lemma sum_padKey (f : Fin M → ℝ) : ∑ k : Fin (M * d), f (padKey M d k) = d * ∑ a, f a := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [padKey, mul_sum, sum_const]

variable [NeZero d]

open Classical in
/-- The encoder: the codeword of `m + k`. -/
def padCode (c : ChannelCode M n α β) : KeyedSecrecyCode M (M * d) n α β where
  enc z x := if x = c.enc (z.1 + padKey M d z.2) then 1 else 0
  isChannel_enc z := by
    classical
    refine ⟨fun x => ?_, by simp⟩
    dsimp only
    split_ifs <;> norm_num
  dec y k := c.dec y - padKey M d k

omit [Fintype β] [NeZero M] [NeZero d] in
open Classical in
/-- The law of the pad code. -/
lemma padCode_law (c : ChannelCode M n α β) (z) : (padCode (d := d) c).law W z =
    1 / ((M * d : ℕ) * M : ℝ) * (if z.1.2 = c.enc (z.1.1.1 + padKey M d z.1.1.2) then 1 else 0) *
      channelExt W n z.1.2 z.2 := by
  simp only [KeyedSecrecyCode.law, KeyedSecrecyCode.inputLaw, jointOf, padCode, uniformPMF,
    Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring_nf

omit [Fintype β] [NeZero M] [NeZero d] in
/-- The sum over the codeword in the law of the pad code. -/
lemma sum_padCode_law (c : ChannelCode M n α β) (m : Fin M) (k : Fin (M * d)) (y : Fin n → β) :
    ∑ x, (padCode (d := d) c).law W (((m, k), x), y) =
      1 / ((M * d : ℕ) * M : ℝ) * channelExt W n (c.enc (m + padKey M d k)) y := by
  classical
  simp only [padCode_law]
  rw [sum_eq_single (c.enc (m + padKey M d k)) (fun x _ hx => by simp [hx]) (by simp)]
  simp

/-- **Page 23-4 of [elgamal2010], on a channel.** The leakage of the pad code is `0`. -/
theorem padCode_leakage (hW : IsChannel W) (c : ChannelCode M n α β) :
    (padCode (d := d) c).leakage W = 0 := by
  classical
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hμ := KeyedSecrecyCode.law_isPMF (c := padCode (d := d) c) hW
  rw [KeyedSecrecyCode.leakage, mutualInfo_eq_zero_iff hμ]
  intro m y
  set Y₀ := ∑ l, channelExt W n (c.enc l) y with hY₀
  have hj : ∀ m', dist ((padCode (d := d) c).law W)
      (pair (fun z => z.1.1.1) Prod.snd) (m', y) = 1 / (M * M) * Y₀ := fun m' => by
    have h₀ : dist ((padCode (d := d) c).law W) (pair (fun z => z.1.1.1) Prod.snd) (m', y) =
        ∑ k : Fin (M * d), ∑ x, (padCode (d := d) c).law W (((m', k), x), y) := by
      simp only [dist, pair, Prod.mk.injEq, Fintype.sum_prod_type]
      rw [sum_eq_single m' (fun b _ hb => by simp [hb]) (by simp)]
      refine sum_congr rfl fun k _ => sum_congr rfl fun x _ => ?_
      rw [sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
      simp
    rw [h₀]
    simp only [sum_padCode_law, ← mul_sum]
    have hs : ∑ a, channelExt W n (c.enc (m' + a)) y = Y₀ :=
      Equiv.sum_comp (Equiv.addLeft m') fun l => channelExt W n (c.enc l) y
    rw [sum_padKey fun a => channelExt W n (c.enc (m' + a)) y, hs]
    push_cast
    field_simp
  have hm : dist ((padCode (d := d) c).law W) (fun z => z.1.1.1) m = 1 / M := by
    have h₁ : dist ((padCode (d := d) c).law W) (fun z => z.1.1.1) m =
        dist (dist ((padCode (d := d) c).law W) fun z => z.1.1) Prod.fst m := by
      rw [← dist_comp_eq]
      rfl
    rw [h₁, dist_fst]
    simp only [KeyedSecrecyCode.dist_pair_key hW, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  have hy : dist ((padCode (d := d) c).law W) Prod.snd y = 1 / M * Y₀ := by
    have h₁ : dist ((padCode (d := d) c).law W) Prod.snd y =
        ∑ m', dist ((padCode (d := d) c).law W) (pair (fun z => z.1.1.1) Prod.snd) (m', y) := by
      rw [← dist_snd, ← dist_comp_eq]
      rfl
    rw [h₁]
    simp only [hj, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hj, hm, hy]
  field_simp

/-- **Page 23-6 of [elgamal2010].** The probability of error of the pad code is the average
probability of error of the channel code, since `m + k` is uniform. -/
theorem padCode_errProb (c : ChannelCode M n α β) :
    (padCode (d := d) c).errProb W = c.avgErrProb W := by
  classical
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [KeyedSecrecyCode.errProb, InfoTheory.errProb, ChannelCode.avgErrProb]
  have e₁ : ∀ m k, ∑ x, ∑ y, (if (padCode (d := d) c).dec y k ≠ m then
      (padCode (d := d) c).law W (((m, k), x), y) else 0) =
      1 / ((M * d : ℕ) * M : ℝ) * c.condErrProb W (m + padKey M d k) := fun m k => by
    rw [sum_comm]
    simp only [ChannelCode.condErrProb, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases h : c.dec y = m + padKey M d k
    · have : (padCode (d := d) c).dec y k = m := by
        simp [padCode, h]
      simp [this, h]
    · have : (padCode (d := d) c).dec y k ≠ m := by
        simp only [padCode, ne_eq, sub_eq_iff_eq_add]
        exact h
      simp only [this, ne_eq, not_false_eq_true, ite_true, h, sum_padCode_law]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have e₂ : ∀ m : Fin M, ∑ k : Fin (M * d), ∑ x, ∑ y, (if (padCode (d := d) c).dec y k ≠ m then
      (padCode (d := d) c).law W (((m, k), x), y) else 0) =
      1 / ((M * d : ℕ) * M : ℝ) * (d * ∑ l, c.condErrProb W l) := fun m => by
    simp only [e₁, ← mul_sum]
    rw [sum_padKey fun a => c.condErrProb W (m + a)]
    rw [show ∑ a, c.condErrProb W (m + a) = ∑ l, c.condErrProb W l from
      Equiv.sum_comp (Equiv.addLeft m) fun l => c.condErrProb W l]
  have e₃ : ∑ m : Fin M, ∑ k : Fin (M * d), ∑ x, ∑ y, (if (padCode (d := d) c).dec y k ≠ m then
      (padCode (d := d) c).law W (((m, k), x), y) else 0) =
      ∑ _m : Fin M, 1 / ((M * d : ℕ) * M : ℝ) * (d * ∑ l, c.condErrProb W l) :=
    sum_congr rfl fun m _ => e₂ m
  refine Eq.trans ?_ (e₃.trans ?_)
  · refine sum_congr rfl fun m _ => sum_congr rfl fun k _ => sum_congr rfl fun x _ =>
      sum_congr rfl fun y _ => ?_
    exact ite_congr rfl (fun _ => rfl) fun _ => rfl
  · rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

end Pad

/-! ### Theorem 2 -/

section Theorem

variable {W : α → β → ℝ}

/-- For `R < R_K`, eventually `2 ^ ⌈nR⌉` divides `2 ^ ⌈nR_K⌉`. -/
lemma eventually_two_pow_ceil_dvd {R RK : ℝ} (h : R < RK) :
    ∀ᶠ n : ℕ in atTop, 2 ^ ⌈n * R⌉₊ ∣ 2 ^ ⌈n * RK⌉₊ := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact pow_dvd_pow 2 (Nat.ceil_mono (mul_le_mul_of_nonneg_left h.le hn'.le))

/-- **Page 23-6 of [elgamal2010]: achievability.** Every `R < min {R_K, C}` is achievable. -/
theorem isAchievableKeyed_of_lt [Nonempty α] (hW : IsChannel W) {R RK : ℝ} (hR : 0 ≤ R)
    (h₁ : R < RK) (h₂ : R * log 2 < capacity W) : IsAchievableKeyed W R RK := by
  obtain ⟨p, hp, hpC⟩ := exists_capacity_eq hW
  set e := (capacity W - R * log 2) / 4 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hlim : Tendsto (fun n : ℕ => (1 - prob (jointIid (jointOf p W) n)
      (jointTypicalSet (jointOf p W) n e)) + 2 * exp (-(n * e))) atTop (𝓝 0) := by
    have t₁ : Tendsto (fun n => 1 - prob (jointIid (jointOf p W) n)
        (jointTypicalSet (jointOf p W) n e)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_jointTypicalSet (jointOf_isPMF hp hW) he0).const_sub 1
    simpa using t₁.add ((tendsto_exp_neg_mul_nat he0).const_mul 2)
  refine ⟨hR, fun ε hε => ?_⟩
  filter_upwards [(tendsto_order.1 hlim).2 ε hε, eventually_two_pow_ceil_dvd h₁,
    eventually_gt_atTop 0] with n hn hdvd hn0
  obtain ⟨d, hd⟩ := hdvd
  set M := 2 ^ ⌈n * R⌉₊ with hM
  have hMpos : 0 < M := by positivity
  have : NeZero M := ⟨hMpos.ne'⟩
  have hdpos : d ≠ 0 := by
    rintro rfl
    have : 0 < 2 ^ ⌈n * RK⌉₊ := by positivity
    simp [hd] at this
  have : NeZero d := ⟨hdpos⟩
  obtain ⟨c, hc⟩ := exists_code_avgErrProb_le (M := M) hp hW hMpos n e
  rw [hd]
  refine ⟨padCode (d := d) c, ?_, ?_⟩
  · rw [padCode_errProb]
    refine le_trans hc (le_trans (add_le_add le_rfl ?_) hn.le)
    have hbd : ((M : ℝ) - 1) ≤ 2 * exp (n * (R * log 2)) := by
      have h₃ := log_two_pow_ceil_le n hR
      have h₄ : (M : ℝ) ≤ exp (n * (R * log 2) + log 2) := by
        rw [← exp_log (show (0 : ℝ) < M by exact_mod_cast hMpos)]
        exact exp_le_exp.2 h₃
      rw [exp_add, exp_log two_pos] at h₄
      linarith
    calc ((M : ℝ) - 1) * exp (-(n * (mutualInfoOf p W - 3 * e)))
        ≤ 2 * exp (n * (R * log 2)) * exp (-(n * (mutualInfoOf p W - 3 * e))) :=
          mul_le_mul_of_nonneg_right hbd (exp_pos _).le
      _ = 2 * exp (-(n * e)) := by
          rw [mul_assoc, ← exp_add]
          congr 2
          rw [hpC, he]
          ring
  · rw [padCode_leakage hW]
    positivity

/-- **Page 23-6 of [elgamal2010]: the converse.** An achievable rate is at most `R_K` and at most
the capacity. -/
theorem IsAchievableKeyed.le [Nonempty α] (hW : IsChannel W) {R RK : ℝ} (hRK : 0 ≤ RK)
    (h : IsAchievableKeyed W R RK) : R ≤ RK ∧ R * log 2 ≤ capacity W := by
  have hl := log_pos one_lt_two
  have hne : ∀ (n : ℕ) (R : ℝ), NeZero (2 ^ ⌈n * R⌉₊) := fun n R => ⟨by positivity⟩
  constructor
  · have key : R * log 2 ≤ RK * log 2 := by
      refine le_of_forall_eventually_mul_le (mul_nonneg h.1 hl.le) fun ε hε => ?_
      refine ⟨2 * log 2, ?_⟩
      filter_upwards [h.2 (min ε (1 / 2)) (by positivity)] with n hn
      obtain ⟨c, hc₁, hc₂⟩ := hn
      have := hne n R
      have := hne n RK
      have h₁ := c.one_sub_errProb_mul_log_le_key hW
      have h₂ := le_log_two_pow_ceil n R
      have h₃ := log_two_pow_ceil_le n hRK
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hP : 0 ≤ 1 - c.errProb W := by
        have := hc₁.trans (min_le_right _ _)
        linarith
      have hmin : c.errProb W ≤ ε := hc₁.trans (min_le_left _ _)
      have hleak : c.leakage W ≤ n * ε :=
        hc₂.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hn0)
      have hb : (1 - ε) * (n * (R * log 2)) ≤ (1 - c.errProb W) * log (2 ^ ⌈n * R⌉₊ : ℕ) := by
        have ha : 0 ≤ n * (R * log 2) := mul_nonneg hn0 (mul_nonneg h.1 hl.le)
        calc (1 - ε) * (n * (R * log 2)) ≤ (1 - c.errProb W) * (n * (R * log 2)) :=
              mul_le_mul_of_nonneg_right (by linarith) ha
          _ ≤ _ := mul_le_mul_of_nonneg_left h₂ hP
      nlinarith
    exact le_of_mul_le_mul_right key hl
  · refine le_of_forall_eventually_mul_le (mul_nonneg h.1 hl.le) fun ε hε => ?_
    refine ⟨log 2, ?_⟩
    filter_upwards [h.2 (min ε (1 / 2)) (by positivity)] with n hn
    obtain ⟨c, hc₁, -⟩ := hn
    have := hne n R
    have := hne n RK
    have h₁ := c.one_sub_errProb_mul_log_le_capacity hW
    have h₂ := le_log_two_pow_ceil n R
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hP : 0 ≤ 1 - c.errProb W := by
      have := hc₁.trans (min_le_right _ _)
      linarith
    have hmin : c.errProb W ≤ ε := hc₁.trans (min_le_left _ _)
    have hb : (1 - ε) * (n * (R * log 2)) ≤ (1 - c.errProb W) * log (2 ^ ⌈n * R⌉₊ : ℕ) := by
      have ha : 0 ≤ n * (R * log 2) := mul_nonneg hn0 (mul_nonneg h.1 hl.le)
      calc (1 - ε) * (n * (R * log 2)) ≤ (1 - c.errProb W) * (n * (R * log 2)) :=
            mul_le_mul_of_nonneg_right (by linarith) ha
        _ ≤ _ := mul_le_mul_of_nonneg_left h₂ hP
    have : (n : ℝ) * capacity W ≤ n * (capacity W + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) hn0
    linarith

/-- **Theorem 2 of Lecture 23 of [elgamal2010], page 23-6.** The secrecy capacity of the DMC with a
key of rate `R_K` is `C(R_K) = min {R_K, max_{p(x)} I(X; Y)}`, in bits. -/
theorem keyedSecrecyCapacity_eq [Nonempty α] (hW : IsChannel W) {RK : ℝ} (hRK : 0 ≤ RK) :
    keyedSecrecyCapacity W RK = min RK (capacity W / log 2) := by
  have hl := log_pos one_lt_two
  have hC : 0 ≤ capacity W / log 2 := by
    obtain ⟨p, hp, hpC⟩ := exists_capacity_eq hW
    rw [← hpC]
    exact div_nonneg (mutualInfoOf_nonneg hp hW) hl.le
  have hup : ∀ R ∈ {R | IsAchievableKeyed W R RK}, R ≤ min RK (capacity W / log 2) := fun R hR => by
    obtain ⟨h₁, h₂⟩ := IsAchievableKeyed.le hW hRK hR
    exact le_min h₁ ((le_div_iff₀ hl).2 h₂)
  refine le_antisymm (Real.sSup_le hup (le_min hRK hC)) ?_
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  rcases lt_or_ge r 0 with h0 | h0
  · exact h0.le.trans (Real.sSup_nonneg fun R hR => hR.1)
  · have hmem : r ∈ {R | IsAchievableKeyed W R RK} :=
      isAchievableKeyed_of_lt hW h0 (hr.trans_le (min_le_left _ _))
        ((lt_div_iff₀ hl).1 (hr.trans_le (min_le_right _ _)))
    exact le_csSup ⟨_, hup⟩ hmem

end Theorem

end InfoTheory
