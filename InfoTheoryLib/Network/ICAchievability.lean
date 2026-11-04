/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.ICSuperLetter

/-!
# The simultaneous decoding inner bound and Theorem 1

If each receiver of a DM-IC decodes both messages, the rate pairs with
`R₁ ≤ min {I(X₁; Y₁ | X₂, Q), I(X₁; Y₂ | X₂, Q)}`, `R₂ ≤ min {I(X₂; Y₁ | X₁, Q), I(X₂; Y₂ | X₁, Q)}`
and `R₁ + R₂ ≤ min {I(X₁, X₂; Y₁ | Q), I(X₁, X₂; Y₂ | Q)}` are achievable. With strong interference
this inner bound meets the outer bound: Theorem 1 of Lecture 6 of El Gamal and Kim.

## Main definitions

* `superSplit`, `superJoin`, `ICCode.flatten`: a code on super-letters as a code on letters.
* `icSimultaneousRegionBits W`: the simultaneous decoding inner bound.

## Main statements

* `ICCode.err₁_flatten`, `ICCode.err₂_flatten`: a code on `t` super-letters of `m` letters works at
  every block length `t m + r`, with the same probabilities of error.
* `exists_timeSharing_pattern`: a pattern of values of `Q` with empirical averages close to the
  averages of `Q`.
* `isAchievableICBits_of_lt`: rate pairs strictly inside the inner bound are achievable.
* `icSimultaneousRegionBits_subset`: the **simultaneous decoding inner bound**.
* `icCapacityRegionBits_eq_closure_icStrongRegionBits`: **Theorem 1 of [elgamal2010], Lecture 6**.

## Implementation notes

The notes prove the inner bound with coded time sharing. We fix instead a deterministic pattern of
values of `Q` of length `m`, in the right proportions, and code over super-letters of `m` channel
uses with independent letters, which turns the time-sharing variable into a product input
distribution, so that `exists_icCode_err_le` applies. We do not bound `|Q|` (the notes have
`|Q| ≤ 4` in Theorem 1), so Theorem 1 is stated up to closure.

The notes also state a tighter inner bound, where a receiver need not decode the message of the
other pair correctly; it is not needed for Theorem 1 and is not formalized.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 6
-/

open Real Finset Filter Topology Set

@[expose] public noncomputable section

namespace InfoTheory

/-! ### From super-letters to letters -/

section Flatten

variable {t m r N : ℕ} (e : (Fin t × Fin m) ⊕ Fin r ≃ Fin N)

/-- The received sequence, read as `t` super-letters of `m` letters. -/
def superSplit {β : Type*} (y : Fin N → β) : Fin t → Fin m → β :=
  fun a b => y (e (Sum.inl (a, b)))

/-- A sequence of `t` super-letters of `m` letters, padded with the symbol `a₀`. -/
def superJoin {α : Type*} (x : Fin t → Fin m → α) (a₀ : α) : Fin N → α :=
  fun j => Sum.elim (fun ab => x ab.1 ab.2) (fun _ => a₀) (e.symm j)

/-- The outputs at the padding positions sum out. -/
lemma sum_superSplit {β : Type*} [Fintype β] {G : Fin N → β → ℝ} (hG : ∀ j, ∑ b, G j b = 1)
    (f : (Fin t → Fin m → β) → ℝ) :
    ∑ y, f (superSplit e y) * ∏ j, G j (y j) =
      ∑ Y, f Y * ∏ a, ∏ b, G (e (Sum.inl (a, b))) (Y a b) := by
  classical
  let Φ : (Fin t → Fin m → β) × (Fin r → β) ≃ (Fin N → β) :=
    { toFun := fun z j => Sum.elim (fun ab => z.1 ab.1 ab.2) z.2 (e.symm j)
      invFun := fun y => (superSplit e y, fun c => y (e (Sum.inr c)))
      left_inv := fun z => by
        ext <;> simp [superSplit]
      right_inv := fun y => by
        funext j
        rcases h : e.symm j with ⟨a, b⟩ | c
        · simp [superSplit, h, ← e.symm_apply_eq.1 h]
        · simp [h, ← e.symm_apply_eq.1 h] }
  have hsplit : ∀ z, superSplit e (Φ z) = z.1 := fun z => by
    funext a b
    simp [superSplit, Φ]
  have hprod : ∀ z : (Fin t → Fin m → β) × (Fin r → β), ∏ j, G j (Φ z j) =
      (∏ a, ∏ b, G (e (Sum.inl (a, b))) (z.1 a b)) * ∏ c, G (e (Sum.inr c)) (z.2 c) := fun z => by
    rw [← e.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
    simp [Φ]
  have hZ : ∑ Z : Fin r → β, ∏ c, G (e (Sum.inr c)) (Z c) = 1 := by
    have h := Fintype.prod_sum fun (c : Fin r) (b : β) => G (e (Sum.inr c)) b
    simp only [hG, prod_const_one] at h
    exact h.symm
  rw [← Φ.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun Y _ => ?_
  simp only [hsplit, hprod, ← mul_assoc, ← mul_sum, hZ, mul_one]

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] {M₁ M₂ : ℕ}

/-- A code on `t` super-letters of `m` letters, as a code of block length `N`, using the positions
in the padding for fixed symbols. -/
def ICCode.flatten (c : ICCode M₁ M₂ t (Fin m → α₁) (Fin m → α₂) (Fin m → β₁) (Fin m → β₂))
    (a₀ : α₁) (b₀ : α₂) : ICCode M₁ M₂ N α₁ α₂ β₁ β₂ :=
  ⟨fun i => superJoin e (c.enc₁ i) a₀, fun j => superJoin e (c.enc₂ j) b₀,
    fun y => c.dec₁ (superSplit e y), fun y => c.dec₂ (superSplit e y)⟩

omit [Fintype β₂] in
/-- The probability of error of a super-letter code at receiver 1 does not change on letters. -/
theorem ICCode.err₁_flatten (c : ICCode M₁ M₂ t (Fin m → α₁) (Fin m → α₂) (Fin m → β₁)
    (Fin m → β₂)) (a₀ : α₁) (b₀ : α₂) {V : α₁ × α₂ → β₁ → ℝ} (hV : IsChannel V) :
    (c.flatten e a₀ b₀).err₁ V = c.err₁ (macExt V m) := by
  classical
  simp only [ICCode.err₁, ICCode.flatten]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have h := sum_superSplit e (G := fun k b => V (zipSeq (superJoin e (c.enc₁ i) a₀)
    (superJoin e (c.enc₂ j) b₀) k) b) (fun k => (hV _).sum_eq_one)
    (fun Y => if c.dec₁ Y ≠ i then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  refine Eq.trans (sum_congr rfl fun y _ => ?_) (h.trans (sum_congr rfl fun Y _ => ?_))
  · by_cases hd : c.dec₁ (superSplit e y) = i <;> simp [hd, channelExt]
  · by_cases hd : c.dec₁ Y = i <;> simp [hd, macExt, channelExt, zipSeq, superJoin]

omit [Fintype β₁] in
/-- The probability of error of a super-letter code at receiver 2 does not change on letters. -/
theorem ICCode.err₂_flatten (c : ICCode M₁ M₂ t (Fin m → α₁) (Fin m → α₂) (Fin m → β₁)
    (Fin m → β₂)) (a₀ : α₁) (b₀ : α₂) {V : α₁ × α₂ → β₂ → ℝ} (hV : IsChannel V) :
    (c.flatten e a₀ b₀).err₂ V = c.err₂ (macExt V m) := by
  classical
  simp only [ICCode.err₂, ICCode.flatten]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have h := sum_superSplit e (G := fun k b => V (zipSeq (superJoin e (c.enc₁ i) a₀)
    (superJoin e (c.enc₂ j) b₀) k) b) (fun k => (hV _).sum_eq_one)
    (fun Y => if c.dec₂ Y ≠ j then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  refine Eq.trans (sum_congr rfl fun y _ => ?_) (h.trans (sum_congr rfl fun Y _ => ?_))
  · by_cases hd : c.dec₂ (superSplit e y) = j <;> simp [hd, channelExt]
  · by_cases hd : c.dec₂ Y = j <;> simp [hd, macExt, channelExt, zipSeq, superJoin]

end Flatten

/-! ### The time-sharing pattern -/

/-- A deterministic pattern `s` of values of the time-sharing variable `Q ∼ q`, of some length `m`,
whose empirical averages of bounded nonnegative functions are within `δ` of their means. -/
theorem exists_timeSharing_pattern {k : ℕ} {q : Fin k → ℝ} (hq : IsPMF q) {B δ : ℝ}
    (hδ : 0 < δ) : ∃ (m : ℕ) (s : Fin m → Fin k), 0 < m ∧ ∀ f : Fin k → ℝ,
      (∀ i, 0 ≤ f i ∧ f i ≤ B) → ∑ i, q i * f i - δ ≤ (∑ j, f (s j)) / m := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (k * B / δ) k)
  have hLk : (k : ℝ) < L := (le_max_right _ _).trans_lt hL
  have hLδ : k * B / δ < L := (le_max_left _ _).trans_lt hL
  have hL0 : (0 : ℝ) < L := lt_of_le_of_lt (Nat.cast_nonneg k) hLk
  set c : Fin k → ℕ := fun i => ⌊q i * L⌋₊
  have hc₁ : ∀ i, (c i : ℝ) ≤ q i * L := fun i =>
    Nat.floor_le (mul_nonneg (hq.nonneg i) hL0.le)
  have hc₂ : ∀ i, q i * L < c i + 1 := fun i => Nat.lt_floor_add_one _
  have hsum : ∑ i, q i * (L : ℝ) = L := by rw [← sum_mul, hq.sum_eq_one, one_mul]
  have hm₁ : ((∑ i, c i : ℕ) : ℝ) ≤ L := by
    push_cast
    exact (sum_le_sum fun i _ => hc₁ i).trans hsum.le
  have hm₂ : (L : ℝ) - k < ((∑ i, c i : ℕ) : ℝ) := by
    have hne : (univ : Finset (Fin k)).Nonempty :=
      ⟨(Classical.choice (Fintype.card_pos_iff.1 (card_pos_of_isPMF hq))), mem_univ _⟩
    have := sum_lt_sum_of_nonempty hne fun i _ => hc₂ i
    rw [hsum, sum_add_distrib] at this
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    push_cast
    linarith
  refine ⟨∑ i, c i, fun j => ((finSigmaFinEquiv (n := c)).symm j).1, ?_, fun f hf => ?_⟩
  · have : (0 : ℝ) < ((∑ i, c i : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  · have hm0 : (0 : ℝ) < ((∑ i, c i : ℕ) : ℝ) := by linarith
    have e : ∑ j, f ((finSigmaFinEquiv (n := c)).symm j).1 = ∑ i, (c i : ℝ) * f i := by
      rw [(finSigmaFinEquiv (n := c)).symm.sum_comp fun x => f x.1, Fintype.sum_sigma]
      simp
    rw [e]
    have hnn : 0 ≤ ∑ i, (c i : ℝ) * f i :=
      sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hf i).1
    have h1 : (∑ i, (c i : ℝ) * f i) / L ≤ (∑ i, (c i : ℝ) * f i) / ((∑ i, c i : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hnn hm0 hm₁
    refine le_trans ?_ h1
    have h2 : L * ∑ i, q i * f i - k * B ≤ ∑ i, (c i : ℝ) * f i := by
      have : ∑ i, (q i * L - 1) * f i ≤ ∑ i, (c i : ℝ) * f i :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by linarith [hc₂ i]) (hf i).1
      have h3 : ∑ i, (q i * L - 1) * f i = L * ∑ i, q i * f i - ∑ i, f i := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
      have h4 : ∑ i, f i ≤ k * B := by
        calc ∑ i, f i ≤ ∑ _i : Fin k, B := sum_le_sum fun i _ => (hf i).2
          _ = k * B := by simp
      linarith
    rw [le_div_iff₀ hL0]
    have h5 : k * B ≤ δ * L := by
      rw [div_lt_iff₀ hδ] at hLδ
      linarith
    nlinarith

/-! ### The rates -/

section Rates

/-- `e^{Nρ} e^{-t (I - 3γ)} ≤ e^{C} e^{-γ t}` when `N < (t + 1) m`, `I ≥ m (ρ + 5γ)`, `m ρ ≤ C`. -/
lemma icRate_exp_le {ρ γ I C : ℝ} {N t m : ℕ} (hρ : 0 < ρ) (hγ : 0 < γ) (hN : N < (t + 1) * m)
    (hm : 0 < m) (hI : m * (ρ + 5 * γ) ≤ I) (hC : m * ρ ≤ C) :
    exp (N * ρ) * exp (-(t * (I - 3 * γ))) ≤ exp C * exp (-(t * γ)) := by
  rw [← exp_add, ← exp_add, exp_le_exp]
  have hN' : (N : ℝ) ≤ (t + 1) * m := by exact_mod_cast hN.le
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have h1 : (N : ℝ) * ρ ≤ (t + 1) * m * ρ := mul_le_mul_of_nonneg_right hN' hρ.le
  have h2 : t * (m * (ρ + 5 * γ)) ≤ t * I := mul_le_mul_of_nonneg_left hI ht
  have h3 : 0 ≤ t * γ * (m - 1) := mul_nonneg (mul_nonneg ht hγ.le) (by linarith)
  nlinarith

/-- A single-message term vanishes, otherwise it is exponentially small. -/
lemma icRate_term_le {R γ I C : ℝ} {N t m : ℕ} (hγ : 0 < γ) (hN : N < (t + 1) * m) (hm : 0 < m)
    (hI : m * (R * log 2 + 5 * γ) ≤ I) (hC : m * (|R| * log 2) ≤ C) :
    (((2 ^ ⌈N * R⌉₊ : ℕ) : ℝ) - 1) * exp (-(t * (I - 3 * γ))) ≤ 2 * (exp C * exp (-(t * γ))) := by
  have hl := log_pos one_lt_two
  have hpos : 0 ≤ 2 * (exp C * exp (-(t * γ))) := by positivity
  rcases le_or_gt R 0 with hR | hR
  · rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hR)]
    simpa using hpos
  · have hρ : 0 < R * log 2 := mul_pos hR hl
    have hC' : m * (R * log 2) ≤ C := by rwa [abs_of_pos hR] at hC
    have h := icRate_exp_le hρ hγ hN hm hI hC'
    have hM := two_pow_ceil_le N hR.le
    have hE := exp_pos (-(t * (I - 3 * γ)))
    calc (((2 ^ ⌈N * R⌉₊ : ℕ) : ℝ) - 1) * exp (-(t * (I - 3 * γ)))
        ≤ (2 * exp (N * (R * log 2))) * exp (-(t * (I - 3 * γ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hE.le
      _ ≤ 2 * (exp C * exp (-(t * γ))) := by
          rw [mul_assoc]
          linarith

/-- The term with both messages wrong vanishes if one of them is a single message, otherwise it is
exponentially small. -/
lemma icRate_term₁₂_le {R₁ R₂ γ I C : ℝ} {N t m : ℕ} (hγ : 0 < γ) (hN : N < (t + 1) * m)
    (hm : 0 < m) (hI : m * (R₁ * log 2 + R₂ * log 2 + 5 * γ) ≤ I)
    (hC : m * (|R₁| * log 2 + |R₂| * log 2) ≤ C) :
    (((2 ^ ⌈N * R₁⌉₊ : ℕ) : ℝ) - 1) * (((2 ^ ⌈N * R₂⌉₊ : ℕ) : ℝ) - 1) *
      exp (-(t * (I - 3 * γ))) ≤ 4 * (exp C * exp (-(t * γ))) := by
  have hl := log_pos one_lt_two
  have hpos : 0 ≤ 4 * (exp C * exp (-(t * γ))) := by positivity
  rcases le_or_gt R₁ 0 with hR₁ | hR₁
  · rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hR₁)]
    simpa using hpos
  rcases le_or_gt R₂ 0 with hR₂ | hR₂
  · rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hR₂)]
    simpa using hpos
  have hρ : 0 < R₁ * log 2 + R₂ * log 2 := add_pos (mul_pos hR₁ hl) (mul_pos hR₂ hl)
  have hC' : m * (R₁ * log 2 + R₂ * log 2) ≤ C := by
    rwa [abs_of_pos hR₁, abs_of_pos hR₂] at hC
  have h := icRate_exp_le hρ hγ hN hm hI hC'
  have hM₁ := two_pow_ceil_le N hR₁.le
  have hM₂ := two_pow_ceil_le N hR₂.le
  have hM₁' : (1 : ℝ) ≤ ((2 ^ ⌈N * R₁⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hM₂' : (1 : ℝ) ≤ ((2 ^ ⌈N * R₂⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hE := exp_pos (-(t * (I - 3 * γ)))
  have hprod : (((2 ^ ⌈N * R₁⌉₊ : ℕ) : ℝ) - 1) * (((2 ^ ⌈N * R₂⌉₊ : ℕ) : ℝ) - 1) ≤
      4 * exp (N * (R₁ * log 2 + R₂ * log 2)) := by
    rw [mul_add, exp_add]
    calc _ ≤ (2 * exp (N * (R₁ * log 2))) * (2 * exp (N * (R₂ * log 2))) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  calc _ ≤ (4 * exp (N * (R₁ * log 2 + R₂ * log 2))) * exp (-(t * (I - 3 * γ))) :=
        mul_le_mul_of_nonneg_right hprod hE.le
    _ ≤ 4 * (exp C * exp (-(t * γ))) := by
        rw [mul_assoc]
        linarith

end Rates

/-! ### The inner bound -/

section InnerBound

variable {α₁ α₂ β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
  {W : α₁ × α₂ → β₁ × β₂ → ℝ}

/-- **Lecture 6 of [elgamal2010], page 6-7.** Rate pairs strictly inside the simultaneous decoding
inner bound are achievable: for a pattern of values of `Q` of length `m`, the super-letters of `m`
channel uses with independent letters have informations `m I(X₁; Y | X₂, Q)`, and so on, up to a
small loss, and compound random coding applies. -/
theorem isAchievableICBits_of_lt (hW : IsChannel W) {k : ℕ} {q : Fin k → ℝ} {p₁ : Fin k → α₁ → ℝ}
    {p₂ : Fin k → α₂ → ℝ} (hq : IsPMF q) (hp₁ : ∀ i, IsPMF (p₁ i)) (hp₂ : ∀ i, IsPMF (p₂ i))
    {R₁ R₂ : ℝ} (h₁₁ : R₁ < icAvg₁ q p₁ p₂ (bcMarg₁ W) / log 2)
    (h₁₂ : R₁ < icAvg₁ q p₁ p₂ (bcMarg₂ W) / log 2)
    (h₂₁ : R₂ < icAvg₂ q p₁ p₂ (bcMarg₁ W) / log 2)
    (h₂₂ : R₂ < icAvg₂ q p₁ p₂ (bcMarg₂ W) / log 2)
    (h₃₁ : R₁ + R₂ < icAvg₁₂ q p₁ p₂ (bcMarg₁ W) / log 2)
    (h₃₂ : R₁ + R₂ < icAvg₁₂ q p₁ p₂ (bcMarg₂ W) / log 2) :
    IsAchievableICBits W R₁ R₂ := by
  have hl := log_pos one_lt_two
  have hV₁ := hW.bcMarg₁
  have hV₂ := hW.bcMarg₂
  have i₀ : Fin k := Classical.choice (Fintype.card_pos_iff.1 (card_pos_of_isPMF hq))
  have a₀ : α₁ := Classical.choice (Fintype.card_pos_iff.1 (card_pos_of_isPMF (hp₁ i₀)))
  have b₀ : α₂ := Classical.choice (Fintype.card_pos_iff.1 (card_pos_of_isPMF (hp₂ i₀)))
  rw [lt_div_iff₀ hl] at h₁₁ h₁₂ h₂₁ h₂₂ h₃₁ h₃₂
  -- A common margin `6γ`.
  have key : ∀ a b : ℝ, 0 < a → 0 < b → ∃ c > 0, c ≤ a ∧ c ≤ b := fun a b ha hb =>
    ⟨min a b, lt_min ha hb, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨g₁, hg₁, g₁a, g₁b⟩ := key _ _ (sub_pos.2 h₁₁) (sub_pos.2 h₁₂)
  obtain ⟨g₂, hg₂, g₂a, g₂b⟩ := key _ _ hg₁ (sub_pos.2 h₂₁)
  obtain ⟨g₃, hg₃, g₃a, g₃b⟩ := key _ _ hg₂ (sub_pos.2 h₂₂)
  obtain ⟨g₄, hg₄, g₄a, g₄b⟩ := key _ _ hg₃ (sub_pos.2 h₃₁)
  obtain ⟨g₅, hg₅, g₅a, g₅b⟩ := key _ _ hg₄ (sub_pos.2 h₃₂)
  set γ := g₅ / 6 with hγ_def
  have hγ : 0 < γ := by positivity
  have hg : g₅ = 6 * γ := by rw [hγ_def]; ring
  -- The bound on the informations.
  set B := |log (Fintype.card β₁)| + |log (Fintype.card β₂)|
  have hB₁ : ∀ {p : α₁ → ℝ} {p' : α₂ → ℝ}, IsPMF p → IsPMF p' →
      0 ≤ macInfo₁₂ p p' (bcMarg₁ W) ∧ macInfo₁₂ p p' (bcMarg₁ W) ≤ B := fun hp hp' =>
    ⟨(macInfo₁_nonneg hp hp' hV₁).trans (macInfo₁_le_macInfo₁₂ hp hp' hV₁),
      (macInfo₁₂_le_log_card hp hp' hV₁).trans
        ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))⟩
  have hB₂ : ∀ {p : α₁ → ℝ} {p' : α₂ → ℝ}, IsPMF p → IsPMF p' →
      0 ≤ macInfo₁₂ p p' (bcMarg₂ W) ∧ macInfo₁₂ p p' (bcMarg₂ W) ≤ B := fun hp hp' =>
    ⟨(macInfo₁_nonneg hp hp' hV₂).trans (macInfo₁_le_macInfo₁₂ hp hp' hV₂),
      (macInfo₁₂_le_log_card hp hp' hV₂).trans
        ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))⟩
  obtain ⟨m, s, hm, hpat⟩ := exists_timeSharing_pattern hq (B := B) hγ
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpat' : ∀ (f : Fin k → ℝ) (ρ : ℝ), (∀ i, 0 ≤ f i ∧ f i ≤ B) → ρ + 6 * γ ≤ ∑ i, q i * f i →
      m * (ρ + 5 * γ) ≤ ∑ j, f (s j) := fun f ρ hf hρ => by
    have := hpat f hf
    rw [le_div_iff₀ hm'] at this
    nlinarith
  -- The super-letters.
  set r₁ : Fin m → α₁ → ℝ := fun j => p₁ (s j)
  set r₂ : Fin m → α₂ → ℝ := fun j => p₂ (s j)
  have hr₁ : ∀ j, IsPMF (r₁ j) := fun j => hp₁ _
  have hr₂ : ∀ j, IsPMF (r₂ j) := fun j => hp₂ _
  set P₁ := indexedPMF r₁
  set P₂ := indexedPMF r₂
  have hP₁ : IsPMF P₁ := indexedPMF_isPMF hr₁
  have hP₂ : IsPMF P₂ := indexedPMF_isPMF hr₂
  set E₁ := macExt (bcMarg₁ W) m
  set E₂ := macExt (bcMarg₂ W) m
  have hE₁ : IsChannel E₁ := macExt_isChannel hV₁ m
  have hE₂ : IsChannel E₂ := macExt_isChannel hV₂ m
  have hA₁ : m * (R₁ * log 2 + 5 * γ) ≤ macInfo₁ P₁ P₂ E₁ := by
    rw [macInfo₁_macExt_indexedPMF hr₁ hr₂ hV₁]
    exact hpat' (fun i => macInfo₁ (p₁ i) (p₂ i) (bcMarg₁ W)) _
      (fun i => ⟨macInfo₁_nonneg (hp₁ i) (hp₂ i) hV₁,
        (macInfo₁_le_macInfo₁₂ (hp₁ i) (hp₂ i) hV₁).trans (hB₁ (hp₁ i) (hp₂ i)).2⟩)
      (by simp only [icAvg₁] at g₁a; linarith)
  have hA₂ : m * (R₁ * log 2 + 5 * γ) ≤ macInfo₁ P₁ P₂ E₂ := by
    rw [macInfo₁_macExt_indexedPMF hr₁ hr₂ hV₂]
    exact hpat' (fun i => macInfo₁ (p₁ i) (p₂ i) (bcMarg₂ W)) _
      (fun i => ⟨macInfo₁_nonneg (hp₁ i) (hp₂ i) hV₂,
        (macInfo₁_le_macInfo₁₂ (hp₁ i) (hp₂ i) hV₂).trans (hB₂ (hp₁ i) (hp₂ i)).2⟩)
      (by simp only [icAvg₁] at g₁b; linarith)
  have hB₁' : m * (R₂ * log 2 + 5 * γ) ≤ macInfo₂ P₁ P₂ E₁ := by
    rw [macInfo₂_macExt_indexedPMF hr₁ hr₂ hV₁]
    exact hpat' (fun i => macInfo₂ (p₁ i) (p₂ i) (bcMarg₁ W)) _
      (fun i => ⟨macInfo₂_nonneg (hp₁ i) (hp₂ i) hV₁,
        (macInfo₂_le_macInfo₁₂ (hp₁ i) (hp₂ i) hV₁).trans (hB₁ (hp₁ i) (hp₂ i)).2⟩)
      (by simp only [icAvg₂] at g₂b; linarith)
  have hB₂' : m * (R₂ * log 2 + 5 * γ) ≤ macInfo₂ P₁ P₂ E₂ := by
    rw [macInfo₂_macExt_indexedPMF hr₁ hr₂ hV₂]
    exact hpat' (fun i => macInfo₂ (p₁ i) (p₂ i) (bcMarg₂ W)) _
      (fun i => ⟨macInfo₂_nonneg (hp₁ i) (hp₂ i) hV₂,
        (macInfo₂_le_macInfo₁₂ (hp₁ i) (hp₂ i) hV₂).trans (hB₂ (hp₁ i) (hp₂ i)).2⟩)
      (by simp only [icAvg₂] at g₃b; linarith)
  have hC₁ : m * (R₁ * log 2 + R₂ * log 2 + 5 * γ) ≤ macInfo₁₂ P₁ P₂ E₁ := by
    rw [macInfo₁₂_macExt_indexedPMF hr₁ hr₂ hV₁]
    exact hpat' (fun i => macInfo₁₂ (p₁ i) (p₂ i) (bcMarg₁ W)) _
      (fun i => hB₁ (hp₁ i) (hp₂ i)) (by simp only [icAvg₁₂] at g₄b; linarith)
  have hC₂ : m * (R₁ * log 2 + R₂ * log 2 + 5 * γ) ≤ macInfo₁₂ P₁ P₂ E₂ := by
    rw [macInfo₁₂_macExt_indexedPMF hr₁ hr₂ hV₂]
    exact hpat' (fun i => macInfo₁₂ (p₁ i) (p₂ i) (bcMarg₂ W)) _
      (fun i => hB₂ (hp₁ i) (hp₂ i)) (by simp only [icAvg₁₂] at g₅b; linarith)
  -- The bound on the probability of error, for every block length.
  set C := m * (|R₁| * log 2 + |R₂| * log 2)
  have hC_a : m * (|R₁| * log 2) ≤ C :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hm'.le
  have hC_b : m * (|R₂| * log 2) ≤ C :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hm'.le
  set G : ℕ → ℝ := fun t => macAtypProb P₁ P₂ E₁ t γ + macAtypProb P₁ P₂ E₂ t γ +
    16 * (exp C * exp (-(t * γ)))
  have hcode : ∀ N : ℕ, ∃ c : ICCode (2 ^ ⌈N * R₁⌉₊) (2 ^ ⌈N * R₂⌉₊) N α₁ α₂ β₁ β₂,
      c.errProb W ≤ G (N / m) := by
    intro N
    set t := N / m
    have ht : t * m + N % m = N := Nat.div_add_mod' N m
    have hN : N < (t + 1) * m := by
      have := Nat.mod_lt N hm
      nlinarith
    let e : (Fin t × Fin m) ⊕ Fin (N % m) ≃ Fin N :=
      (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans (finSumFinEquiv.trans (finCongr ht))
    obtain ⟨c', hc'⟩ := exists_icCode_err_le (β₁ := Fin m → β₁) (β₂ := Fin m → β₂) hP₁ hP₂ hE₁ hE₂
      (two_pow_ceil_pos N R₁) (two_pow_ceil_pos N R₂) t γ
    refine ⟨c'.flatten e a₀ b₀, ?_⟩
    have h1 := (c'.flatten e a₀ b₀).errProb_le_add hW
    rw [ICCode.errProb₁_eq_err₁, ICCode.errProb₂_eq_err₂, ICCode.err₁_flatten e c' a₀ b₀ hV₁,
      ICCode.err₂_flatten e c' a₀ b₀ hV₂] at h1
    refine h1.trans (hc'.trans ?_)
    have t₁ := icRate_term_le (t := t) (I := macInfo₁ P₁ P₂ E₁) hγ hN hm hA₁ hC_a
    have t₂ := icRate_term_le (t := t) (I := macInfo₁ P₁ P₂ E₂) hγ hN hm hA₂ hC_a
    have t₃ := icRate_term_le (t := t) (I := macInfo₂ P₁ P₂ E₁) hγ hN hm hB₁' hC_b
    have t₄ := icRate_term_le (t := t) (I := macInfo₂ P₁ P₂ E₂) hγ hN hm hB₂' hC_b
    have t₅ := icRate_term₁₂_le (t := t) (I := macInfo₁₂ P₁ P₂ E₁) hγ hN hm hC₁ le_rfl
    have t₆ := icRate_term₁₂_le (t := t) (I := macInfo₁₂ P₁ P₂ E₂) hγ hN hm hC₂ le_rfl
    simp only [icRandomBound, G]
    linarith
  choose c hc using hcode
  refine ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun N => (c N).errProb_nonneg hW) hc⟩
  have hdiv : Tendsto (fun N : ℕ => N / m) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * m, fun a ha => (Nat.le_div_iff_mul_le hm).2 ha⟩
  have hG : Tendsto G atTop (𝓝 0) := by
    have h₁ := tendsto_macAtypProb hP₁ hP₂ hE₁ hγ
    have h₂ := tendsto_macAtypProb hP₁ hP₂ hE₂ hγ
    have h₃ := ((tendsto_exp_neg_mul_nat hγ).const_mul (exp C)).const_mul 16
    simpa [G] using (h₁.add h₂).add h₃
  exact hG.comp hdiv

/-- **Lecture 6 of [elgamal2010], page 6-7.** The simultaneous decoding inner bound: the rate pairs
with `R₁ ≤ min {I(X₁; Y₁ | X₂, Q), I(X₁; Y₂ | X₂, Q)}`,
`R₂ ≤ min {I(X₂; Y₁ | X₁, Q), I(X₂; Y₂ | X₁, Q)}` and
`R₁ + R₂ ≤ min {I(X₁, X₂; Y₁ | Q), I(X₁, X₂; Y₂ | Q)}` for some `p(q) p(x₁ | q) p(x₂ | q)`. -/
def icSimultaneousRegionBits (W : α₁ × α₂ → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (q : Fin k → ℝ) (p₁ : Fin k → α₁ → ℝ) (p₂ : Fin k → α₂ → ℝ),
    IsPMF q ∧ (∀ i, IsPMF (p₁ i)) ∧ (∀ i, IsPMF (p₂ i)) ∧
    R.1 ≤ icAvg₁ q p₁ p₂ (bcMarg₁ W) / log 2 ∧ R.1 ≤ icAvg₁ q p₁ p₂ (bcMarg₂ W) / log 2 ∧
    R.2 ≤ icAvg₂ q p₁ p₂ (bcMarg₁ W) / log 2 ∧ R.2 ≤ icAvg₂ q p₁ p₂ (bcMarg₂ W) / log 2 ∧
    R.1 + R.2 ≤ icAvg₁₂ q p₁ p₂ (bcMarg₁ W) / log 2 ∧
    R.1 + R.2 ≤ icAvg₁₂ q p₁ p₂ (bcMarg₂ W) / log 2}

/-- **Lecture 6 of [elgamal2010], page 6-7.** The simultaneous decoding inner bound is in the
capacity region: its points are the limits of the points `R - (t, t)`, `t → 0⁺`. -/
theorem icSimultaneousRegionBits_subset (hW : IsChannel W) :
    icSimultaneousRegionBits W ⊆ icCapacityRegionBits W := by
  rintro ⟨R₁, R₂⟩ ⟨k, q, p₁, p₂, hq, hp₁, hp₂, a₁, a₂, b₁, b₂, c₁, c₂⟩
  simp only at a₁ a₂ b₁ b₂ c₁ c₂
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine mem_closure_of_sub_icEps (R₁ := R₁) (R₂ := R₂) ht fun n _ => ?_
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact isAchievableICBits_of_lt hW hq hp₁ hp₂ (by dsimp only; linarith) (by dsimp only; linarith)
    (by dsimp only; linarith) (by dsimp only; linarith) (by dsimp only; linarith)
    (by dsimp only; linarith)

/-! ### Theorem 1 -/

/-- With strong interference, the region of Theorem 1 is in the simultaneous decoding inner bound:
the receiver of the other pair can decode each message. -/
theorem IsStrongIC.icStrongRegionBits_subset (hs : IsStrongIC W) :
    icStrongRegionBits W ⊆ icSimultaneousRegionBits W := by
  have hl := log_pos one_lt_two
  rintro R ⟨k, q, p₁, p₂, hq, hp₁, hp₂, a, b, c₁, c₂⟩
  refine ⟨k, q, p₁, p₂, hq, hp₁, hp₂, a, a.trans ?_, b.trans ?_, b, c₁, c₂⟩
  · exact div_le_div_of_nonneg_right (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (hs _ _ (hp₁ i) (hp₂ i)).1 (hq.nonneg i)) hl.le
  · exact div_le_div_of_nonneg_right (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (hs _ _ (hp₁ i) (hp₂ i)).2 (hq.nonneg i)) hl.le

/-- **Theorem 1 of [elgamal2010], Lecture 6.** The capacity region of the DM-IC with strong
interference is the closure of the set of rate pairs with `R₁ ≤ I(X₁; Y₁ | X₂, Q)`,
`R₂ ≤ I(X₂; Y₂ | X₁, Q)` and `R₁ + R₂ ≤ min {I(X₁, X₂; Y₁ | Q), I(X₁, X₂; Y₂ | Q)}` for some
`p(q) p(x₁ | q) p(x₂ | q)`. -/
theorem icCapacityRegionBits_eq_closure_icStrongRegionBits (hW : IsChannel W) (hs : IsStrongIC W) :
    icCapacityRegionBits W = closure (icStrongRegionBits W) := by
  refine Subset.antisymm (closure_minimal (fun R hR => ?_) isClosed_closure) ?_
  · exact IsAchievableICBits.mem_closure_icStrongRegionBits hW hs hR
  · exact closure_minimal (hs.icStrongRegionBits_subset.trans (icSimultaneousRegionBits_subset hW))
      isClosed_closure

end InnerBound

end InfoTheory
