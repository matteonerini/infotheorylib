/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StateChannel.Multicoding

/-!
# The mutual covering lemma

Let `Uⁿ₁(l₁)`, `l₁ ∈ [1 : L₁]`, and `Uⁿ₂(l₂)`, `l₂ ∈ [1 : L₂]`, be independent random sequences, the
first ones i.i.d. from `∏ᵢ p(u₁ᵢ)` and the second ones i.i.d. from `∏ᵢ p(u₂ᵢ)`. The mutual covering
lemma of Lecture 9 of El Gamal and Kim says that some pair is jointly typical, with high
probability, if `L₁ L₂` is exponentially larger than `2^{n I(U₁; U₂)}`.

The proof is the second moment method for the number of jointly typical pairs. We first prove the
bound for a general relation `e` between two independent families, and then specialize it to joint
typicality.

## Main statements

* `sum_mutualCovering_le`: the second moment bound.
* `eventually_sum_mutualCovering_typical_le`: **the mutual covering lemma** in quantitative form.

## Implementation notes

The notes assume the sequences of each family to be pairwise independent only, which is what the
proof uses. We state the lemma for i.i.d. sequences, which is what Marton's coding scheme needs.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The second moment bound -/

section SecondMoment

variable {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂] {μ₁ : X₁ → ℝ} {μ₂ : X₂ → ℝ} {L₁ L₂ : ℕ}

open Classical in
/-- The probability `p₁` that independent `X₁ ∼ μ₁`, `X₂ ∼ μ₂` are related by `e`. -/
def coverProb (μ₁ : X₁ → ℝ) (μ₂ : X₂ → ℝ) (e : X₁ → X₂ → Prop) : ℝ :=
  ∑ x₁, ∑ x₂, μ₁ x₁ * μ₂ x₂ * (if e x₁ x₂ then 1 else 0)

open Classical in
/-- The number of related pairs. -/
def coverCount (e : X₁ → X₂ → Prop) (D₁ : Fin L₁ → X₁) (D₂ : Fin L₂ → X₂) : ℝ :=
  ∑ l₁, ∑ l₂, if e (D₁ l₁) (D₂ l₂) then 1 else 0

/-- The product of the laws of two families of sequences. -/
def coverLaw (μ₁ : X₁ → ℝ) (μ₂ : X₂ → ℝ) (L₁ L₂ : ℕ) (D : (Fin L₁ → X₁) × (Fin L₂ → X₂)) : ℝ :=
  iidPMF μ₁ L₁ D.1 * iidPMF μ₂ L₂ D.2

lemma coverLaw_isPMF (h₁ : IsPMF μ₁) (h₂ : IsPMF μ₂) : IsPMF (coverLaw μ₁ μ₂ L₁ L₂) :=
  ⟨fun D => mul_nonneg ((iidPMF_isPMF h₁ L₁).nonneg _) ((iidPMF_isPMF h₂ L₂).nonneg _), by
    simp only [coverLaw, Fintype.sum_prod_type, ← mul_sum, (iidPMF_isPMF h₂ L₂).sum_eq_one, mul_one,
      (iidPMF_isPMF h₁ L₁).sum_eq_one]⟩

open Classical in
/-- `E[e(D₁(l₁), D₂(l₂)) e(D₁(l₁'), D₂(l₂'))] ≤ p₁² + 1[l₁ = l₁', l₂ = l₂'] p₁ + 1[l₁ = l₁'] a₁ p₁ +
1[l₂ = l₂'] a₂ p₁`, where `a₁`, `a₂` bound the probabilities of being related to a given
sequence. -/
lemma sum_coverLaw_mul_le (h₁ : IsPMF μ₁) (h₂ : IsPMF μ₂) (e : X₁ → X₂ → Prop) {a₁ a₂ : ℝ}
    (ha₁ : ∀ x₁, ∑ x₂, μ₂ x₂ * (if e x₁ x₂ then 1 else 0) ≤ a₁)
    (ha₂ : ∀ x₂, ∑ x₁, μ₁ x₁ * (if e x₁ x₂ then 1 else 0) ≤ a₂) (l₁ l₁' : Fin L₁)
    (l₂ l₂' : Fin L₂) :
    ∑ D, coverLaw μ₁ μ₂ L₁ L₂ D * ((if e (D.1 l₁) (D.2 l₂) then 1 else 0) *
        (if e (D.1 l₁') (D.2 l₂') then 1 else 0)) ≤
      coverProb μ₁ μ₂ e ^ 2 + (if l₁ = l₁' then 1 else 0) * (if l₂ = l₂' then 1 else 0) *
          coverProb μ₁ μ₂ e + (if l₁ = l₁' then 1 else 0) * (a₁ * coverProb μ₁ μ₂ e) +
        (if l₂ = l₂' then 1 else 0) * (a₂ * coverProb μ₁ μ₂ e) := by
  set r : X₁ → X₂ → ℝ := fun x₁ x₂ => if e x₁ x₂ then 1 else 0 with hr
  have hr0 : ∀ x₁ x₂, 0 ≤ r x₁ x₂ := fun x₁ x₂ => by
    simp only [hr]
    split_ifs <;> norm_num
  have hrr : ∀ x₁ x₂, r x₁ x₂ * r x₁ x₂ = r x₁ x₂ := fun x₁ x₂ => by
    simp only [hr]
    split_ifs <;> norm_num
  set s : X₁ → ℝ := fun x₁ => ∑ x₂, μ₂ x₂ * r x₁ x₂
  set t : X₂ → ℝ := fun x₂ => ∑ x₁, μ₁ x₁ * r x₁ x₂
  have hs0 : ∀ x₁, 0 ≤ s x₁ := fun x₁ => sum_nonneg fun x₂ _ =>
    mul_nonneg (h₂.nonneg x₂) (hr0 _ _)
  have ht0 : ∀ x₂, 0 ≤ t x₂ := fun x₂ => sum_nonneg fun x₁ _ =>
    mul_nonneg (h₁.nonneg x₁) (hr0 _ _)
  have hps : coverProb μ₁ μ₂ e = ∑ x₁, μ₁ x₁ * s x₁ := by
    simp only [coverProb, s, mul_sum, mul_assoc]
    rfl
  have hpt : coverProb μ₁ μ₂ e = ∑ x₂, μ₂ x₂ * t x₂ := by
    simp only [coverProb, t, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x₂ _ => sum_congr rfl fun x₁ _ => ?_
    simp only [hr]
    ring
  set p₁ := coverProb μ₁ μ₂ e
  have hp0 : 0 ≤ p₁ := by
    rw [hps]
    exact sum_nonneg fun x₁ _ => mul_nonneg (h₁.nonneg x₁) (hs0 x₁)
  have hne₁ : Nonempty X₁ := by
    by_contra h
    rw [not_nonempty_iff] at h
    simpa using h₁.sum_eq_one
  have hne₂ : Nonempty X₂ := by
    by_contra h
    rw [not_nonempty_iff] at h
    simpa using h₂.sum_eq_one
  have ha₁0 : 0 ≤ a₁ := (hs0 hne₁.some).trans (ha₁ hne₁.some)
  have ha₂0 : 0 ≤ a₂ := (ht0 hne₂.some).trans (ha₂ hne₂.some)
  have hi₁ := iidPMF_isPMF h₁ L₁
  have hi₂ := iidPMF_isPMF h₂ L₂
  -- The expectation over the second family.
  have hΦ : ∀ u u' : X₁, ∑ D₂ : Fin L₂ → X₂, iidPMF μ₂ L₂ D₂ * (r u (D₂ l₂) * r u' (D₂ l₂')) =
      if l₂ = l₂' then ∑ x₂, μ₂ x₂ * (r u x₂ * r u' x₂) else s u * s u' := fun u u' => by
    split_ifs with hl
    · subst hl
      exact sum_iidPMF_eval h₂ l₂ fun x => r u x * r u' x
    · rw [sum_iidPMF_eval₂ h₂ hl fun x x' => r u x * r u' x']
      simp only [s, sum_mul_sum]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hsplit : ∑ D, coverLaw μ₁ μ₂ L₁ L₂ D * (r (D.1 l₁) (D.2 l₂) * r (D.1 l₁') (D.2 l₂')) =
      ∑ D₁ : Fin L₁ → X₁, iidPMF μ₁ L₁ D₁ *
        (if l₂ = l₂' then ∑ x₂, μ₂ x₂ * (r (D₁ l₁) x₂ * r (D₁ l₁') x₂)
          else s (D₁ l₁) * s (D₁ l₁')) := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun D₁ _ => ?_
    rw [← hΦ, mul_sum]
    exact sum_congr rfl fun D₂ _ => by simp only [coverLaw]; ring
  change ∑ D, coverLaw μ₁ μ₂ L₁ L₂ D * (r (D.1 l₁) (D.2 l₂) * r (D.1 l₁') (D.2 l₂')) ≤ _
  rw [hsplit]
  have hrhs0 : 0 ≤ a₁ * p₁ := mul_nonneg ha₁0 hp0
  have hrhs1 : 0 ≤ a₂ * p₁ := mul_nonneg ha₂0 hp0
  by_cases hl₁ : l₁ = l₁' <;> by_cases hl₂ : l₂ = l₂'
  · subst hl₁ hl₂
    simp only [ite_true, hrr, one_mul]
    rw [sum_iidPMF_eval h₁ l₁ fun x => ∑ x₂, μ₂ x₂ * r x x₂]
    have : ∑ x₁, μ₁ x₁ * ∑ x₂, μ₂ x₂ * r x₁ x₂ = p₁ := hps.symm
    rw [this]
    nlinarith [sq_nonneg p₁]
  · subst hl₁
    simp only [hl₂, ite_true, ite_false, one_mul, mul_zero, zero_mul, add_zero]
    rw [sum_iidPMF_eval h₁ l₁ fun x => s x * s x]
    have hle : ∑ x₁, μ₁ x₁ * (s x₁ * s x₁) ≤ ∑ x₁, μ₁ x₁ * (a₁ * s x₁) := sum_le_sum fun x₁ _ =>
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (ha₁ x₁) (hs0 x₁)) (h₁.nonneg x₁)
    have he : ∑ x₁, μ₁ x₁ * (a₁ * s x₁) = a₁ * p₁ := by
      rw [hps, mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    rw [he] at hle
    nlinarith [sq_nonneg p₁]
  · subst hl₂
    simp only [hl₁, ite_true, ite_false, one_mul, zero_mul, add_zero]
    rw [sum_iidPMF_eval₂ h₁ hl₁ fun x x' => ∑ x₂, μ₂ x₂ * (r x x₂ * r x' x₂)]
    have e1 : ∑ x, ∑ x', μ₁ x * μ₁ x' * ∑ x₂, μ₂ x₂ * (r x x₂ * r x' x₂) =
        ∑ x₂, μ₂ x₂ * (t x₂ * t x₂) := by
      have hx : ∀ x₂, μ₂ x₂ * (t x₂ * t x₂) =
          ∑ x, ∑ x', μ₁ x * μ₁ x' * (μ₂ x₂ * (r x x₂ * r x' x₂)) := fun x₂ => by
        simp only [t]
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun x' _ => by ring
      simp_rw [hx]
      calc _ = ∑ x, ∑ x', ∑ x₂, μ₁ x * μ₁ x' * (μ₂ x₂ * (r x x₂ * r x' x₂)) :=
            sum_congr rfl fun x _ => sum_congr rfl fun x' _ => mul_sum _ _ _
        _ = ∑ x, ∑ x₂, ∑ x', μ₁ x * μ₁ x' * (μ₂ x₂ * (r x x₂ * r x' x₂)) :=
            sum_congr rfl fun x _ => sum_comm
        _ = _ := sum_comm
    rw [e1]
    have hle : ∑ x₂, μ₂ x₂ * (t x₂ * t x₂) ≤ ∑ x₂, μ₂ x₂ * (a₂ * t x₂) := sum_le_sum fun x₂ _ =>
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (ha₂ x₂) (ht0 x₂)) (h₂.nonneg x₂)
    have he : ∑ x₂, μ₂ x₂ * (a₂ * t x₂) = a₂ * p₁ := by
      rw [hpt, mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    rw [he] at hle
    nlinarith [sq_nonneg p₁]
  · simp only [hl₁, hl₂, ite_false, mul_zero, zero_mul, add_zero]
    rw [sum_iidPMF_eval₂ h₁ hl₁ fun x x' => s x * s x']
    have e1 : ∑ x, ∑ x', μ₁ x * μ₁ x' * (s x * s x') = p₁ ^ 2 := by
      rw [hps, sq, sum_mul_sum]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [e1]

open Classical in
/-- **The second moment bound for covering.** If `p₁` is the probability that independent `X₁`, `X₂`
are related, and `a₁`, `a₂` bound the probabilities of being related to a given sequence, then the
probability that no pair of the two families is related is at most
`1/(L₁ L₂ p₁) + a₁/(L₁ p₁) + a₂/(L₂ p₁)`. -/
theorem sum_mutualCovering_le (h₁ : IsPMF μ₁) (h₂ : IsPMF μ₂) (e : X₁ → X₂ → Prop) {a₁ a₂ : ℝ}
    (ha₁ : ∀ x₁, ∑ x₂, μ₂ x₂ * (if e x₁ x₂ then 1 else 0) ≤ a₁)
    (ha₂ : ∀ x₂, ∑ x₁, μ₁ x₁ * (if e x₁ x₂ then 1 else 0) ≤ a₂) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hp : 0 < coverProb μ₁ μ₂ e) :
    ∑ D, coverLaw μ₁ μ₂ L₁ L₂ D * (if ∀ l₁ l₂, ¬ e (D.1 l₁) (D.2 l₂) then 1 else 0) ≤
      1 / (L₁ * L₂ * coverProb μ₁ μ₂ e) + a₁ / (L₁ * coverProb μ₁ μ₂ e) +
        a₂ / (L₂ * coverProb μ₁ μ₂ e) := by
  set P := coverLaw μ₁ μ₂ L₁ L₂
  have hP := coverLaw_isPMF h₁ h₂ (L₁ := L₁) (L₂ := L₂)
  set p₁ := coverProb μ₁ μ₂ e with hp₁
  set N : (Fin L₁ → X₁) × (Fin L₂ → X₂) → ℝ := fun D => coverCount e D.1 D.2
  have hL₁' : (0 : ℝ) < L₁ := by exact_mod_cast hL₁
  have hL₂' : (0 : ℝ) < L₂ := by exact_mod_cast hL₂
  -- The first moment.
  have hE1 : ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
      ∑ D, P D * (if e (D.1 l₁) (D.2 l₂) then 1 else 0) = p₁ := fun l₁ l₂ => by
    simp only [P, coverLaw]
    rw [Fintype.sum_prod_type]
    have hin : ∀ D₁ : Fin L₁ → X₁, ∑ D₂ : Fin L₂ → X₂, iidPMF μ₁ L₁ D₁ * iidPMF μ₂ L₂ D₂ *
        (if e (D₁ l₁) (D₂ l₂) then 1 else 0) =
        iidPMF μ₁ L₁ D₁ * ∑ x₂, μ₂ x₂ * (if e (D₁ l₁) x₂ then 1 else 0) := fun D₁ => by
      rw [← sum_iidPMF_eval h₂ l₂ fun x₂ => if e (D₁ l₁) x₂ then 1 else 0, mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    simp only [hin]
    rw [sum_iidPMF_eval h₁ l₁ fun x₁ => ∑ x₂, μ₂ x₂ * if e x₁ x₂ then 1 else 0, hp₁, coverProb]
    refine sum_congr rfl fun x₁ _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun x₂ _ => by ring
  have hNp : ∀ D, N D = ∑ ℓ : Fin L₁ × Fin L₂, if e (D.1 ℓ.1) (D.2 ℓ.2) then 1 else 0 := fun D => by
    simp only [N, coverCount]
    rw [Fintype.sum_prod_type]
  have hEN : ∑ D, P D * N D = L₁ * L₂ * p₁ := by
    simp_rw [hNp, mul_sum]
    rw [sum_comm]
    simp_rw [hE1 _ _]
    simp [card_univ, mul_assoc]
  -- The second moment.
  have hEN2 : ∑ D, P D * (N D * N D) ≤ L₁ * L₁ * L₂ * L₂ * p₁ ^ 2 + L₁ * L₂ * p₁ +
      L₁ * L₂ * L₂ * (a₁ * p₁) + L₁ * L₁ * L₂ * (a₂ * p₁) := by
    have hexp : ∀ D, P D * (N D * N D) = ∑ ℓ : Fin L₁ × Fin L₂, ∑ ℓ' : Fin L₁ × Fin L₂,
        P D * ((if e (D.1 ℓ.1) (D.2 ℓ.2) then 1 else 0) *
          (if e (D.1 ℓ'.1) (D.2 ℓ'.2) then 1 else 0)) := fun D => by
      rw [hNp, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun ℓ _ => ?_
      rw [mul_sum]
    simp_rw [hexp]
    rw [sum_comm]
    have hb : ∀ ℓ : Fin L₁ × Fin L₂, ∑ D, ∑ ℓ' : Fin L₁ × Fin L₂,
        P D * ((if e (D.1 ℓ.1) (D.2 ℓ.2) then 1 else 0) *
          (if e (D.1 ℓ'.1) (D.2 ℓ'.2) then 1 else 0)) ≤
        ∑ ℓ' : Fin L₁ × Fin L₂, (p₁ ^ 2 + (if ℓ.1 = ℓ'.1 then 1 else 0) *
          (if ℓ.2 = ℓ'.2 then 1 else 0) * p₁ + (if ℓ.1 = ℓ'.1 then 1 else 0) * (a₁ * p₁) +
          (if ℓ.2 = ℓ'.2 then 1 else 0) * (a₂ * p₁)) := fun ℓ => by
      rw [sum_comm]
      exact sum_le_sum fun ℓ' _ => sum_coverLaw_mul_le h₁ h₂ e ha₁ ha₂ ℓ.1 ℓ'.1 ℓ.2 ℓ'.2
    refine (sum_le_sum fun ℓ _ => hb ℓ).trans (le_of_eq ?_)
    have hin : ∀ ℓ : Fin L₁ × Fin L₂, ∑ ℓ' : Fin L₁ × Fin L₂, (p₁ ^ 2 +
        (if ℓ.1 = ℓ'.1 then 1 else 0) * (if ℓ.2 = ℓ'.2 then 1 else 0) * p₁ +
        (if ℓ.1 = ℓ'.1 then 1 else 0) * (a₁ * p₁) + (if ℓ.2 = ℓ'.2 then 1 else 0) * (a₂ * p₁)) =
        L₁ * L₂ * p₁ ^ 2 + p₁ + L₂ * (a₁ * p₁) + L₁ * (a₂ * p₁) := fun ℓ => by
      rw [Fintype.sum_prod_type]
      simp [sum_add_distrib, Finset.sum_ite_eq, card_univ, mul_assoc]
    simp_rw [hin]
    simp [card_univ]
    ring
  -- Chebyshev's inequality.
  set EN := ∑ D, P D * N D with hENdef
  have hC : ∀ D, (if ∀ l₁ l₂, ¬ e (D.1 l₁) (D.2 l₂) then 1 else 0) * EN ^ 2 ≤ (N D - EN) ^ 2 :=
    fun D => by
      split_ifs with h
      · have hN : N D = 0 := by
          simp [N, coverCount, h]
        rw [hN]
        nlinarith [sq_nonneg EN]
      · rw [zero_mul]
        exact sq_nonneg _
  have hsum := sum_le_sum fun D (_ : D ∈ univ) => mul_le_mul_of_nonneg_left (hC D) (hP.nonneg D)
  have hvar : ∑ D, P D * (N D - EN) ^ 2 = ∑ D, P D * (N D * N D) - EN ^ 2 := by
    have : ∀ D, P D * (N D - EN) ^ 2 = P D * (N D * N D) - 2 * EN * (P D * N D) + EN ^ 2 * P D :=
      fun D => by ring
    simp_rw [this]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← hENdef, hP.sum_eq_one]
    ring
  rw [hvar] at hsum
  have hpull : ∑ D, P D * ((if ∀ l₁ l₂, ¬ e (D.1 l₁) (D.2 l₂) then 1 else 0) * EN ^ 2) =
      (∑ D, P D * (if ∀ l₁ l₂, ¬ e (D.1 l₁) (D.2 l₂) then 1 else 0)) * EN ^ 2 := by
    rw [sum_mul]
    exact sum_congr rfl fun _ _ => by ring
  rw [hpull] at hsum
  set P0 := ∑ D, P D * (if ∀ l₁ l₂, ¬ e (D.1 l₁) (D.2 l₂) then 1 else 0)
  have hENv : EN = L₁ * L₂ * p₁ := hEN
  have hmain : P0 * (L₁ * L₂ * p₁) ^ 2 ≤ L₁ * L₂ * p₁ + L₁ * L₂ * L₂ * (a₁ * p₁) +
      L₁ * L₁ * L₂ * (a₂ * p₁) := by
    rw [hENv] at hsum
    nlinarith
  have hpos : 0 < (L₁ : ℝ) * L₂ * p₁ := by positivity
  have hfin : 1 / (L₁ * L₂ * p₁) + a₁ / (L₁ * p₁) + a₂ / (L₂ * p₁) =
      (L₁ * L₂ * p₁ + L₁ * L₂ * L₂ * (a₁ * p₁) + L₁ * L₁ * L₂ * (a₂ * p₁)) /
        (L₁ * L₂ * p₁) ^ 2 := by
    field_simp
  rw [hfin, le_div_iff₀ (by positivity)]
  exact hmain

end SecondMoment

/-! ### Joint typicality -/

section Typical

variable {𝒰₁ 𝒰₂ : Type*} [Fintype 𝒰₁] [Fintype 𝒰₂] {q : 𝒰₁ × 𝒰₂ → ℝ} {n : ℕ} {ε : ℝ}

/-- The two entropy terms of the error `δ(ε)` for the pmf `q`, for both orders of the variables. -/
def mutualCoveringConst (q : 𝒰₁ × 𝒰₂ → ℝ) : ℝ :=
  (H[Prod.snd ; q] + H[Prod.snd | Prod.fst ; q]) +
    (H[Prod.snd ; dist q Prod.swap] + H[Prod.snd | Prod.fst ; dist q Prod.swap])

lemma mutualCoveringConst_nonneg (hq : IsPMF q) : 0 ≤ mutualCoveringConst q := by
  have hs : IsPMF (dist q Prod.swap) := hq.dist _
  exact add_nonneg (add_nonneg (entropyRV_nonneg hq _) (condEntropy_nonneg hq _ _))
    (add_nonneg (entropyRV_nonneg hs _) (condEntropy_nonneg hs _ _))

/-- `I(U₂; U₁)` for the swapped pmf is `I(U₂; U₁)`. -/
lemma mutualInfo_swap (hq : IsPMF q) :
    I[Prod.snd : Prod.fst ; dist q Prod.swap] = I[Prod.snd : Prod.fst ; q] := by
  have hs : IsPMF (dist q Prod.swap) := hq.dist _
  have h1 : I[Prod.snd : Prod.fst ; dist q Prod.swap] = I[Prod.fst : Prod.snd ; q] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    have e : pair (Prod.snd : 𝒰₂ × 𝒰₁ → 𝒰₁) Prod.fst ∘ Prod.swap = pair Prod.fst Prod.snd := rfl
    rw [← dist_comp_eq, e]
  rw [h1, mutualInfo_comm hq]

open Classical in
/-- The probability that `U₂ⁿ` is typical with a given `u₁ⁿ` is at most `e^{-n(I - δ)}`. -/
lemma sum_iidPMF_typical_snd_le (hq : IsPMF q) (hε : 0 ≤ ε) (u₁ : Fin n → 𝒰₁) :
    ∑ u₂, iidPMF (margSnd q) n u₂ * (if zipSeq u₁ u₂ ∈ robustTypicalSet q n ε then 1 else 0) ≤
      exp (-(n * (I[Prod.snd : Prod.fst ; q] - ε * mutualCoveringConst q))) := by
  have hs : IsPMF (dist q Prod.swap) := hq.dist _
  have hb := prob_iidPMF_condRobustTypicalSet_le hq ε u₁
  refine le_trans (le_of_eq ?_) (hb.trans (exp_le_exp.2 ?_))
  · rw [prob]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    rfl
  · have h0 : 0 ≤ H[Prod.snd ; dist q Prod.swap] + H[Prod.snd | Prod.fst ; dist q Prod.swap] :=
      add_nonneg (entropyRV_nonneg hs _) (condEntropy_nonneg hs _ _)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : ε * (H[Prod.snd ; q] + H[Prod.snd | Prod.fst ; q]) ≤ ε * mutualCoveringConst q :=
      mul_le_mul_of_nonneg_left (by simp only [mutualCoveringConst]; linarith) hε
    nlinarith [mul_le_mul_of_nonneg_left h1 hn]

open Classical in
/-- The probability that `U₁ⁿ` is typical with a given `u₂ⁿ` is at most `e^{-n(I - δ)}`. -/
lemma sum_iidPMF_typical_fst_le (hq : IsPMF q) (hε : 0 ≤ ε) (u₂ : Fin n → 𝒰₂) :
    ∑ u₁, iidPMF (margFst q) n u₁ * (if zipSeq u₁ u₂ ∈ robustTypicalSet q n ε then 1 else 0) ≤
      exp (-(n * (I[Prod.snd : Prod.fst ; q] - ε * mutualCoveringConst q))) := by
  have hs : IsPMF (dist q Prod.swap) := hq.dist _
  have hm : margSnd (dist q Prod.swap) = margFst q := by
    rw [margSnd, ← dist_comp_eq]
    rfl
  have hb := prob_iidPMF_condRobustTypicalSet_le hs ε u₂
  rw [hm, mutualInfo_swap hq] at hb
  have hμ := iidPMF_isPMF (hq.dist Prod.fst) n
  refine le_trans ?_ (hb.trans (exp_le_exp.2 ?_))
  · rw [prob]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg (fun u₁ hu₁ => ?_) fun _ _ _ => hμ.nonneg _
    rw [mem_filter] at hu₁
    exact mem_condRobustTypicalSet.2 (zipSeq_swap_mem_robustTypicalSet hu₁.2)
  · have h0 : 0 ≤ H[Prod.snd ; q] + H[Prod.snd | Prod.fst ; q] :=
      add_nonneg (entropyRV_nonneg hq _) (condEntropy_nonneg hq _ _)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : ε * (H[Prod.snd ; dist q Prod.swap] + H[Prod.snd | Prod.fst ; dist q Prod.swap]) ≤
        ε * mutualCoveringConst q :=
      mul_le_mul_of_nonneg_left (by simp only [mutualCoveringConst]; linarith) hε
    nlinarith [mul_le_mul_of_nonneg_left h1 hn]

open Classical in
/-- **The mutual covering lemma (Lecture 9 of [elgamal2010])**, quantitative form. For `n` large,
the probability that no pair of the sequences is jointly typical is at most
`4 (e^{n(I(U₁; U₂) + δ)}/(L₁ L₂) + e^{2nδ}/L₁ + e^{2nδ}/L₂)`. This tends to `0` if `L₁ L₂` grows
exponentially faster than `e^{n(I(U₁; U₂) + δ)}` and `L₁`, `L₂` faster than `e^{2nδ}`. -/
theorem eventually_sum_mutualCovering_typical_le (hq : IsPMF q) (hε : 0 < ε) (hε₂ : ε ≤ 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ {L₁ L₂ : ℕ}, 0 < L₁ → 0 < L₂ →
      ∑ D, coverLaw (iidPMF (margFst q) n) (iidPMF (margSnd q) n) L₁ L₂ D *
          (if ∀ l₁ l₂, zipSeq (D.1 l₁) (D.2 l₂) ∉ robustTypicalSet q n ε then 1 else 0) ≤
        4 * (exp (n * (I[Prod.snd : Prod.fst ; q] + ε * mutualCoveringConst q)) / (L₁ * L₂) +
          exp (n * (2 * (ε * mutualCoveringConst q))) / L₁ +
          exp (n * (2 * (ε * mutualCoveringConst q))) / L₂) := by
  have hC := mutualCoveringConst_nonneg hq
  set C := mutualCoveringConst q
  set I₀ := I[Prod.snd : Prod.fst ; q]
  have hμ₁ := hq.dist (Prod.fst : 𝒰₁ × 𝒰₂ → 𝒰₁)
  have hμ₂ := hq.dist (Prod.snd : 𝒰₁ × 𝒰₂ → 𝒰₂)
  have hlow := eventually_le_prob_iidPMF_condRobustTypicalSet hq (ε' := ε / 2) (ε := ε)
    (by linarith) hε
  have htyp : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤
      prob (iidPMF (margFst q) n) (robustTypicalSet (margFst q) n (ε / 2)) :=
    (tendsto_prob_robustTypicalSet hμ₁ (by linarith : 0 < ε / 2)).eventually_const_le
      (by norm_num)
  filter_upwards [hlow, htyp] with n hn hn2 L₁ L₂ hL₁ hL₂
  obtain ⟨e, he⟩ : ∃ e : (Fin n → 𝒰₁) → (Fin n → 𝒰₂) → Prop, ∀ u₁ u₂, e u₁ u₂ ↔
      zipSeq u₁ u₂ ∈ robustTypicalSet q n ε := ⟨_, fun _ _ => Iff.rfl⟩
  have hi₁ := iidPMF_isPMF hμ₁ n
  have hi₂ := iidPMF_isPMF hμ₂ n
  set a := exp (-(n * (I₀ - ε * C))) with ha
  set low := exp (-(n * (I₀ + ε * C)))
  have hlowpos : 0 < low := exp_pos _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- The lower bound on `p₁`.
  have hp : low / 4 ≤ coverProb (iidPMF (margFst q) n) (iidPMF (margSnd q) n) e := by
    have hs : ∀ u₁, iidPMF (margFst q) n u₁ *
        (if u₁ ∈ robustTypicalSet (margFst q) n (ε / 2) then (1 / 2 : ℝ) * low else 0) ≤
        ∑ u₂, iidPMF (margFst q) n u₁ * iidPMF (margSnd q) n u₂ * (if e u₁ u₂ then 1 else 0) :=
      fun u₁ => by
        have hsum : ∑ u₂, iidPMF (margFst q) n u₁ * iidPMF (margSnd q) n u₂ *
            (if e u₁ u₂ then 1 else 0) = iidPMF (margFst q) n u₁ *
              prob (iidPMF (margSnd q) n) (condRobustTypicalSet q ε u₁) := by
          have hf : condRobustTypicalSet q ε u₁ = univ.filter (e u₁) := by
            ext u₂
            simp [he, mem_condRobustTypicalSet]
          rw [prob, hf, sum_filter, mul_sum]
          refine sum_congr rfl fun u₂ _ => ?_
          split_ifs <;> ring
        rw [hsum]
        refine mul_le_mul_of_nonneg_left ?_ (hi₁.nonneg u₁)
        split_ifs with hu
        · refine le_trans ?_ (hn u₁ hu)
          have hc : ε * (H[Prod.snd ; q] + H[Prod.snd | Prod.fst ; q]) ≤ ε * C := by
            refine mul_le_mul_of_nonneg_left ?_ hε.le
            have hs : IsPMF (dist q Prod.swap) := hq.dist _
            have h0 : 0 ≤ H[Prod.snd ; dist q Prod.swap] +
                H[Prod.snd | Prod.fst ; dist q Prod.swap] :=
              add_nonneg (entropyRV_nonneg hs _) (condEntropy_nonneg hs _ _)
            simp only [C, mutualCoveringConst]
            linarith
          have hexp : low ≤ exp (-(n * (I₀ + ε * (H[Prod.snd ; q] +
              H[Prod.snd | Prod.fst ; q])))) :=
            exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hc hn0])
          have h1e : (1 / 2 : ℝ) ≤ 1 - ε := by linarith
          exact mul_le_mul h1e hexp hlowpos.le (by linarith)
        · exact prob_nonneg hi₂.nonneg _
    have hsum := sum_le_sum fun u₁ (_ : u₁ ∈ univ) => hs u₁
    have hl : ∑ u₁, iidPMF (margFst q) n u₁ *
        (if u₁ ∈ robustTypicalSet (margFst q) n (ε / 2) then (1 / 2 : ℝ) * low else 0) =
        prob (iidPMF (margFst q) n) (robustTypicalSet (margFst q) n (ε / 2)) * (1 / 2 * low) := by
      simp_rw [mul_ite, mul_zero]
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, prob, sum_mul]
    rw [hl] at hsum
    have : (1 / 2 : ℝ) * (1 / 2 * low) ≤
        coverProb (iidPMF (margFst q) n) (iidPMF (margSnd q) n) e :=
      (mul_le_mul_of_nonneg_right hn2 (by positivity)).trans hsum
    linarith
  have hppos : 0 < coverProb (iidPMF (margFst q) n) (iidPMF (margSnd q) n) e :=
    lt_of_lt_of_le (by positivity) hp
  have ha₁ : ∀ u₁, ∑ u₂, iidPMF (margSnd q) n u₂ * (if e u₁ u₂ then 1 else 0) ≤ a := fun u₁ => by
    refine le_trans (le_of_eq (sum_congr rfl fun u₂ _ => ?_))
      (sum_iidPMF_typical_snd_le hq hε.le u₁)
    rw [if_congr (he u₁ u₂) rfl rfl]
  have ha₂ : ∀ u₂, ∑ u₁, iidPMF (margFst q) n u₁ * (if e u₁ u₂ then 1 else 0) ≤ a := fun u₂ => by
    refine le_trans (le_of_eq (sum_congr rfl fun u₁ _ => ?_))
      (sum_iidPMF_typical_fst_le hq hε.le u₂)
    rw [if_congr (he u₁ u₂) rfl rfl]
  have hb := sum_mutualCovering_le hi₁ hi₂ e ha₁ ha₂ hL₁ hL₂ hppos
  set p₁ := coverProb (iidPMF (margFst q) n) (iidPMF (margSnd q) n) e
  have hL₁' : (0 : ℝ) < L₁ := by exact_mod_cast hL₁
  have hL₂' : (0 : ℝ) < L₂ := by exact_mod_cast hL₂
  have hinv : 1 / p₁ ≤ 4 * exp (n * (I₀ + ε * C)) := by
    rw [div_le_iff₀ hppos]
    have e1 : exp (n * (I₀ + ε * C)) * low = 1 := by
      rw [← exp_add]
      simp
    nlinarith [exp_pos (n * (I₀ + ε * C))]
  have ha0 : 0 ≤ a := (exp_pos _).le
  have haexp : a * exp (n * (I₀ + ε * C)) = exp (n * (2 * (ε * C))) := by
    rw [ha, ← exp_add]
    congr 1
    ring
  have t1 : 1 / (L₁ * L₂ * p₁) ≤ 4 * (exp (n * (I₀ + ε * C)) / (L₁ * L₂)) := by
    have : 1 / ((L₁ : ℝ) * L₂ * p₁) = 1 / p₁ / (L₁ * L₂) := by
      field_simp
    rw [this, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hinv (by positivity)
  have hmid : a * (1 / p₁) ≤ 4 * exp (n * (2 * (ε * C))) := by
    calc a * (1 / p₁) ≤ a * (4 * exp (n * (I₀ + ε * C))) := mul_le_mul_of_nonneg_left hinv ha0
      _ = 4 * exp (n * (2 * (ε * C))) := by rw [← haexp]; ring
  have t2 : a / (L₁ * p₁) ≤ 4 * (exp (n * (2 * (ε * C))) / L₁) := by
    calc a / (L₁ * p₁) = a * (1 / p₁) / L₁ := by field_simp
      _ ≤ 4 * exp (n * (2 * (ε * C))) / L₁ := div_le_div_of_nonneg_right hmid hL₁'.le
      _ = _ := by ring
  have t3 : a / (L₂ * p₁) ≤ 4 * (exp (n * (2 * (ε * C))) / L₂) := by
    calc a / (L₂ * p₁) = a * (1 / p₁) / L₂ := by field_simp
      _ ≤ 4 * exp (n * (2 * (ε * C))) / L₂ := div_le_div_of_nonneg_right hmid hL₂'.le
      _ = _ := by ring
  refine le_trans (le_of_eq (sum_congr rfl fun D _ => ?_)) (hb.trans ?_)
  · congr 1
    exact if_congr (by simp [he]) rfl rfl
  · linarith

end Typical

end InfoTheory
