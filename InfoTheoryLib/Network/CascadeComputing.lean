/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.GraphEntropy
public import InfoTheoryLib.SourceCoding.LosslessRate
public import InfoTheoryLib.Network.SlepianWolfMany

/-!
# Cascade coding for lossless computing

This file proves the optimal rate region for computing `Z = g(X₁, X₂)` losslessly over a cascade:
the first encoder sees `X₁` and sends an index to the second encoder, which sees `X₂` and sends an
index to the decoder. By Lecture 22 of [elgamal2010], the region is `R₁ ≥ H_G(X₁ | X₂)`,
`R₂ ≥ H(Z)`: this is where the local computing inner bound and the cutset outer bound coincide.

## Main definitions

* `CascadeCode`, `CascadeCode.errProb`: the codes.
* `IsLosslessCascade`, `cascadeRegion`: the achievable rates, and the optimal rate region.

## Main statements

* `isLosslessCascade_of_lt`: achievability, by local computing.
* `IsLosslessCascade.isLosslessFunBits`, `IsLosslessCascade.entropy_le`: the converse.
* `cascadeRegion_eq`: **the optimal rate region**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ}

/-- **Lecture 22 of [elgamal2010], page 22-24.** A code for computing over a cascade. -/
structure CascadeCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*) where
  /-- The first encoder. -/
  enc₁ : (Fin n → α₁) → Fin M₁
  /-- The second encoder. -/
  enc₂ : Fin M₁ → (Fin n → α₂) → Fin M₂
  /-- The decoder. -/
  dec : Fin M₂ → Fin n → β

open Classical in
/-- The probability of error `P{Ẑⁿ ≠ Zⁿ}`. -/
def CascadeCode.errProb {M₁ M₂ n : ℕ} (c : CascadeCode M₁ M₂ n α₁ α₂ β) (P : α₁ × α₂ → ℝ)
    (g : α₁ × α₂ → β) : ℝ :=
  ∑ ω, if c.dec (c.enc₂ (c.enc₁ (fstSeq ω)) (sndSeq ω)) ≠ fun i => g (ω i) then iidPMF P n ω else 0

/-- **Lecture 22 of [elgamal2010], page 22-25.** A rate pair, in bits, is achievable for computing
`Z = g(X₁, X₂)` losslessly over the cascade. -/
def IsLosslessCascade (P : α₁ × α₂ → ℝ) (g : α₁ × α₂ → β) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ ∃ c : ∀ n : ℕ, CascadeCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂ β,
    Tendsto (fun n => (c n).errProb P g) atTop (𝓝 0)

/-- **Lecture 22 of [elgamal2010], page 22-25.** The optimal rate region. -/
def cascadeRegion (P : α₁ × α₂ → ℝ) (g : α₁ × α₂ → β) : Set (ℝ × ℝ) :=
  closure {R | IsLosslessCascade P g R.1 R.2}

/-- The errors of the two stages add up: first compute `Zⁿ` at the second encoder, with the code of
side information, and then compress `Zⁿ`. -/
theorem isLosslessCascade_of_isLossless [Fintype β] (hP : IsPMF P) {g : α₁ × α₂ → β} {R₁ R₂ : ℝ}
    (h₁ : IsLosslessFunBits P g R₁) (h₂ : IsAchievableLosslessRate (dist P g) R₂) :
    IsLosslessCascade P g R₁ R₂ := by
  classical
  obtain ⟨h₁0, c₁, hc₁⟩ := h₁
  obtain ⟨h₂0, c₂, hc₂⟩ := h₂
  refine ⟨h₁0, h₂0, fun n => ⟨(c₁ n).enc, fun m y => (c₂ n).enc ((c₁ n).dec m y),
    (c₂ n).dec⟩, ?_⟩
  have hnn : ∀ n : ℕ, 0 ≤ CascadeCode.errProb (⟨(c₁ n).enc, fun m y => (c₂ n).enc ((c₁ n).dec m y),
      (c₂ n).dec⟩ : CascadeCode _ _ n α₁ α₂ β) P g := fun n => sum_nonneg fun ω _ => by
    split_ifs
    · exact iidPMF_nonneg hP.nonneg ω
    · exact le_rfl
  refine squeeze_zero hnn (fun n => ?_) (by simpa using hc₁.add hc₂)
  have hb : (c₂ n).blockErrProb (dist P g) = ∑ ω, if (c₂ n).dec ((c₂ n).enc fun i => g (ω i)) ≠
      (fun i => g (ω i)) then iidPMF P n ω else 0 := by
    rw [RDCode.blockErrProb, InfoTheory.errProb, ← dist_iidPMF_comp]
    have h := sum_dist_mul (iidPMF P n) (fun ω i => g (ω i)) fun z =>
      if (c₂ n).dec ((c₂ n).enc z) ≠ z then (1 : ℝ) else 0
    simp only [mul_ite, mul_one, mul_zero] at h
    refine Eq.trans (sum_congr rfl fun z _ => ?_) h
    simp only [id, Function.comp]
    congr!
  rw [hb, WZCode.funErrProb, ← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  have h0 := iidPMF_nonneg hP.nonneg ω
  by_cases he : (c₁ n).dec ((c₁ n).enc (fstSeq ω)) (sndSeq ω) = fun i => g (ω i)
  · simp only [he, ne_eq, not_true_eq_false, ite_false, zero_add]
    exact le_rfl
  · simp only [ne_eq, he, not_false_eq_true, ite_true]
    have h1 : 0 ≤ if (c₂ n).dec ((c₂ n).enc fun i => g (ω i)) = (fun i => g (ω i)) then 0 else
        iidPMF P n ω := by
      split_ifs
      · exact le_rfl
      · exact h0
    split_ifs <;> linarith

/-- **Lecture 22, page 22-25: achievability, by local computing.** -/
theorem isLosslessCascade_of_lt [Fintype β] (hP : IsPMF P) {g : α₁ × α₂ → β} {R₁ R₂ : ℝ}
    (h₁ : funLosslessRate P g / log 2 < R₁) (h₂ : entropy (dist P g) / log 2 < R₂) :
    IsLosslessCascade P g R₁ R₂ := by
  obtain ⟨q, f, hq, hf, hr⟩ := exists_funLosslessRate_eq hP g
  exact isLosslessCascade_of_isLossless hP (isLosslessFunBits_of_lt hP hq hf (by rwa [hr]))
    (isAchievableLosslessRate_of_lt (hP.dist _) h₂)

/-- A cascade code gives a code with side information `X₂`: the second encoder can decode. -/
theorem IsLosslessCascade.isLosslessFunBits {g : α₁ × α₂ → β} {R₁ R₂ : ℝ}
    (h : IsLosslessCascade P g R₁ R₂) : IsLosslessFunBits P g R₁ := by
  obtain ⟨h₁, -, c, hc⟩ := h
  exact ⟨h₁, fun n => ⟨(c n).enc₁, fun m y => (c n).dec ((c n).enc₂ m y)⟩, hc⟩

/-- **Lecture 22, page 22-25.** Fano's inequality for one code: the index of the second encoder must
describe `Zⁿ`. -/
theorem CascadeCode.mul_entropy_le [Fintype β] {M₁ M₂ n : ℕ} (hM₂ : 0 < M₂) (hP : IsPMF P)
    (c : CascadeCode M₁ M₂ n α₁ α₂ β) (g : α₁ × α₂ → β) :
    n * H[g ; P] ≤ log M₂ + log 2 + c.errProb P g * (n * log (Fintype.card β)) := by
  classical
  have hμ := iidPMF_isPMF hP n
  set Z : (Fin n → α₁ × α₂) → Fin n → β := fun ω i => g (ω i) with hZ
  set Me : (Fin n → α₁ × α₂) → Fin M₂ := fun ω => c.enc₂ (c.enc₁ (fstSeq ω)) (sndSeq ω) with hMe
  have hH : H[Z ; iidPMF P n] = n * H[g ; P] := entropyRV_iidPMF_comp hP n g
  have hne : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  have hI : I[Z : Me ; iidPMF P n] ≤ log M₂ := by
    have h₂ := entropyRV_le_log_card hμ Me
    rw [Fintype.card_fin] at h₂
    have h₃ := condEntropy_nonneg hμ Me Z
    rw [mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
    linarith
  have hsum := mutualInfo_eq_entropy_sub_condEntropy hμ (X := Z) (Y := Me)
  have hdec : H[Z | Me ; iidPMF P n] ≤ H[Z | c.dec ∘ Me ; iidPMF P n] :=
    condEntropy_le_condEntropy_comp hμ Z Me c.dec
  have hF := condEntropy_le_estErrProb hμ Z (c.dec ∘ Me) (ι := id) Function.injective_id
  have hb : binEntropy (estErrProb (iidPMF P n) Z (c.dec ∘ Me) id) ≤ log 2 := binEntropy_le_log_two
  have herr : estErrProb (iidPMF P n) Z (c.dec ∘ Me) id = c.errProb P g := by
    refine sum_congr rfl fun ω _ => ?_
    simp only [hZ, hMe, id, Function.comp]
  have hcard : log (Fintype.card (Fin n → β)) = n * log (Fintype.card β) := by
    simp [Nat.cast_pow, log_pow]
  rw [herr, hcard] at hF
  rw [herr] at hb
  linarith

/-- **Lecture 22, page 22-25: the converse.** `R₂ ≥ H(Z)`, in bits. -/
theorem IsLosslessCascade.entropy_le [Fintype β] (hP : IsPMF P) {g : α₁ × α₂ → β} {R₁ R₂ : ℝ}
    (h : IsLosslessCascade P g R₁ R₂) : H[g ; P] ≤ R₂ * log 2 := by
  obtain ⟨-, h₂, c, hc⟩ := h
  have hl := log_pos one_lt_two
  have hbound : ∀ n : ℕ, 0 < n → H[g ; P] ≤ R₂ * log 2 + log 2 / n +
      (c n).errProb P g * log (Fintype.card β) := fun n hn => by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hF := (c n).mul_entropy_le (by positivity) hP g
    have hlog : log ((2 ^ ⌊(n : ℝ) * R₂⌋₊ : ℕ) : ℝ) ≤ n * (R₂ * log 2) := by
      exact log_two_pow_floor_le n h₂
    have hmain : n * H[g ; P] ≤ n * (R₂ * log 2 + log 2 / n +
        (c n).errProb P g * log (Fintype.card β)) := by
      have e : (n : ℝ) * (log 2 / n) = log 2 := by field_simp
      rw [mul_add, mul_add, e]
      nlinarith
    exact le_of_mul_le_mul_left hmain hn'
  have ht : Tendsto (fun n : ℕ => R₂ * log 2 + log 2 / n +
      (c n).errProb P g * log (Fintype.card β)) atTop (𝓝 (R₂ * log 2)) := by
    have h₁ : Tendsto (fun n : ℕ => log 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h₂' := hc.mul_const (log (Fintype.card β))
    simpa using (tendsto_const_nhds.add h₁).add h₂'
  exact ge_of_tendsto ht ((eventually_gt_atTop 0).mono hbound)

/-- **Lecture 22 of [elgamal2010], page 22-25.** The optimal rate region for computing `Z`
losslessly over a cascade is `R₁ ≥ H_G(X₁ | X₂)`, `R₂ ≥ H(Z)`, in bits: the local computing inner
bound and the cutset outer bound coincide. -/
theorem cascadeRegion_eq [Fintype β] (hP : IsPMF P) (g : α₁ × α₂ → β) :
    cascadeRegion P g = {R | condGraphEntropy (charGraph P g) P / log 2 ≤ R.1 ∧
      H[g ; P] / log 2 ≤ R.2} := by
  have hl := log_pos one_lt_two
  rw [← funLosslessRate_eq_condGraphEntropy hP]
  refine subset_antisymm (closure_minimal (fun R hR => ⟨?_, ?_⟩) ?_) ?_
  · rw [div_le_iff₀ hl]
    exact IsLosslessCascade.isLosslessFunBits hR |>.le hP
  · rw [div_le_iff₀ hl]
    exact hR.entropy_le hP
  · exact (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  · rintro R ⟨hr₁, hr₂⟩
    have hδ : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun m : ℕ => ((R.1 + 1 / ((m : ℝ) + 1), R.2 + 1 / ((m : ℝ) + 1)) : ℝ × ℝ))
        atTop (𝓝 R) := by
      have e₁ := (tendsto_const_nhds (x := R.1)).add hδ
      have e₂ := (tendsto_const_nhds (x := R.2)).add hδ
      simp only [add_zero] at e₁ e₂
      exact e₁.prodMk_nhds e₂
    refine mem_closure_of_tendsto ht (Eventually.of_forall fun m => ?_)
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    exact isLosslessCascade_of_lt hP (by dsimp only; linarith)
      (by rw [show entropy (dist P g) = H[g ; P] from rfl]; dsimp only; linarith)

end InfoTheory
