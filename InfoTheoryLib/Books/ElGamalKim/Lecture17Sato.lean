/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayClasses
public import InfoTheoryLib.Network.RelayLookahead
public import InfoTheoryLib.SourceCoding.Minimax

/-!
# Lecture 17: the Sato relay channel

The degraded relay channel of pages 17-19, 17-71 and 17-74 of El Gamal and Kim, with `Y₁ = X`.

## Main statements

* `sato_le_log`: the capacity of the channel from `(X, X₁)` to `Y` is at most `log (9/4)`.
* `sato_lookCapacity`: with unlimited lookahead the capacity is `log₂ (9/4)` bits.
* `sato_rwdCapacity`: without delay the capacity is also `log₂ (9/4)` bits, by instantaneous
  relaying.
* `sato_isDegradedRC`: the channel is degraded, so its capacity is given by decode–forward.
* `sato_rcCapacity_le`: the capacity of the relay channel is at most `log₂ (9/4)` bits.
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-- **Page 17-19 of [elgamal2010].** The channel from `(X, X₁)` to `Y`. -/
def satoW₂ (a : Fin 3 × Fin 2) : Fin 3 → ℝ :=
  match a with
  | (0, 0) => ![1, 0, 0]
  | (1, 0) => ![0, 1 / 2, 1 / 2]
  | (2, 0) => ![0, 1 / 2, 1 / 2]
  | (0, 1) => ![1 / 2, 1 / 2, 0]
  | (1, 1) => ![1 / 2, 1 / 2, 0]
  | (2, 1) => ![0, 0, 1]

/-- The law of `Y` of the optimal input. -/
def satoQ : Fin 3 → ℝ := ![4 / 9, 1 / 9, 4 / 9]

lemma satoQ_isPMF : IsPMF satoQ := by
  refine ⟨fun x => ?_, ?_⟩
  · fin_cases x <;> norm_num [satoQ]
  · simp only [Fin.sum_univ_three, satoQ]
    norm_num

lemma satoW₂_isChannel : IsChannel satoW₂ := by
  rintro ⟨x, x₁⟩
  refine ⟨fun y => ?_, ?_⟩
  · fin_cases x <;> fin_cases x₁ <;> fin_cases y <;> simp [satoW₂]
  · fin_cases x <;> fin_cases x₁ <;> simp [satoW₂, Fin.sum_univ_three] <;> norm_num

/-- All the inputs are at the same divergence from the optimal output. -/
lemma relEntropy_satoW₂ (a : Fin 3 × Fin 2) : relEntropyReal (satoW₂ a) satoQ = log (9 / 4) := by
  have h₁ : log (9 / 2) + log (9 / 8) = 2 * log (9 / 4) := by
    rw [← log_mul (by norm_num) (by norm_num), two_mul, ← log_mul (by norm_num) (by norm_num)]
    norm_num
  have h₂ : log (1 / (4 / 9 : ℝ)) = log (9 / 4) := by norm_num
  obtain ⟨x, x₁⟩ := a
  fin_cases x <;> fin_cases x₁ <;>
    simp only [relEntropyReal, Fin.sum_univ_three, satoW₂, satoQ] <;> norm_num <;> linarith

/-- **Page 17-71 of [elgamal2010].** The capacity of the channel from `(X, X₁)` to `Y`, an upper
  bound
for all the relay models. -/
lemma sato_le_log {α : Type*} [Fintype α] [Nonempty α] {V : α → Fin 3 → ℝ} (hV : IsChannel V)
    (g : α → Fin 3 × Fin 2) (hg : ∀ a, V a = satoW₂ (g a)) : capacity V ≤ log (9 / 4) := by
  obtain ⟨a, ha⟩ := exists_capacity_le_relEntropy hV satoQ_isPMF (q := satoQ) fun a y hy => by
    fin_cases y <;> simp [satoQ] at hy
  rw [hg a, relEntropy_satoW₂] at ha
  exact ha

/-- The law of `Y₁` given `X`: the relay receives `X`. -/
def satoW₁ (x y₁ : Fin 3) : ℝ := if y₁ = x then 1 else 0

lemma satoW₁_isChannel : IsChannel satoW₁ := fun x => by
  refine ⟨fun y₁ => ?_, ?_⟩
  · simp only [satoW₁]
    split_ifs <;> norm_num
  · simp [satoW₁]

/-- The law of `Y` given `(X, X₁, Y₁)`, which does not depend on `Y₁`. -/
def satoW₂' (a : Fin 3 × Fin 2 × Fin 3) : Fin 3 → ℝ := satoW₂ (a.1, a.2.1)

lemma satoW₂'_isChannel : IsChannel satoW₂' := fun _ => satoW₂_isChannel _

/-- The optimal input of noncausal decode–forward, page 17-71. -/
def satoP (a : Fin 3 × Fin 2) : ℝ :=
  match a with
  | (0, 0) => 7 / 18
  | (1, 0) => 1 / 18
  | (2, 0) => 1 / 18
  | (0, 1) => 1 / 18
  | (1, 1) => 1 / 18
  | (2, 1) => 7 / 18

lemma satoP_isPMF : IsPMF satoP := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, x₁⟩
    fin_cases x <;> fin_cases x₁ <;> norm_num [satoP]
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, satoP]
    norm_num

/-- `I(X, X₁; Y) = log (9/4)` for the optimal input. -/
lemma sato_info : mutualInfoOf satoP satoW₂ = log (9 / 4) := by
  have hout : outDist satoP satoW₂ = satoQ := by
    funext y
    simp only [outDist, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, satoP, satoW₂]
    fin_cases y <;> simp [satoQ] <;> norm_num
  rw [mutualInfoOf_eq_sum_relEntropy satoP_isPMF satoW₂_isChannel, hout]
  simp_rw [relEntropy_satoW₂]
  rw [← sum_mul, satoP_isPMF.sum_eq_one, one_mul]

/-- `lookY` of the Sato channel is the channel from `(X, X₁)` to `Y`. -/
lemma sato_lookY : lookY satoW₁ satoW₂' = satoW₂ := by
  funext a y
  simp [lookY, satoW₁, satoW₂']

/-- The law of `X` of the optimal input is the optimal output. -/
lemma sato_dist_fst : dist satoP Prod.fst = satoQ := by
  funext x
  simp only [dist, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, satoP]
  fin_cases x <;> simp [satoQ] <;> norm_num

/-- `I(X; Y₁) = H(X) ≥ log (9/4)` for the optimal input. -/
lemma sato_info₁ : log (9 / 4) ≤ mutualInfoOf (dist satoP Prod.fst) satoW₁ := by
  have hout : outDist satoQ satoW₁ = satoQ := by
    funext y
    simp [outDist, satoW₁]
  rw [sato_dist_fst, mutualInfoOf_eq_sum_relEntropy satoQ_isPMF satoW₁_isChannel, hout]
  have hd : ∀ x, relEntropyReal (satoW₁ x) satoQ = log (1 / satoQ x) := by
    intro x
    fin_cases x <;> simp [relEntropyReal, satoW₁, satoQ]
  simp_rw [hd]
  simp only [Fin.sum_univ_three, satoQ]
  have h₁ : log (1 / (4 / 9 : ℝ)) = log (9 / 4) := by norm_num
  have h₂ : log (9 / 4 : ℝ) ≤ log (1 / (1 / 9 : ℝ)) := log_le_log (by norm_num) (by norm_num)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [h₁]
  nlinarith

/-- **Page 17-71 of [elgamal2010].** The capacity of the Sato relay channel with unlimited lookahead
is `log₂ (9/4) = 1.169925` bits, by noncausal decode–forward. -/
theorem sato_lookCapacity : lookCapacity (X₁ := Fin 2) satoW₁ satoW₂' = log (9 / 4) / log 2 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨log (9 / 4) / log 2 - 1, ?_⟩
    (fun R hR => ?_) fun a ha => ?_
  · refine isAchievableLook_noncausal satoW₁_isChannel satoW₂'_isChannel satoP_isPMF ?_ ?_
    · refine lt_of_lt_of_le ?_ sato_info₁
      rw [sub_mul, div_mul_cancel₀ _ hlog2.ne']
      linarith
    · rw [sato_lookY, sato_info, sub_mul, div_mul_cancel₀ _ hlog2.ne']
      linarith
  · rw [le_div_iff₀ hlog2]
    refine (IsAchievableLook.le_capacity satoW₁_isChannel satoW₂'_isChannel hR).trans ?_
    exact sato_le_log satoW₂'_isChannel (fun a => (a.1, a.2.1)) fun _ => rfl
  · obtain ⟨b, hab, hb⟩ := exists_between ha
    refine ⟨b, ?_, hab⟩
    have hb' := (lt_div_iff₀ hlog2).mp hb
    refine isAchievableLook_noncausal satoW₁_isChannel satoW₂'_isChannel satoP_isPMF
      (hb'.trans_le sato_info₁) ?_
    rw [sato_lookY, sato_info]
    exact hb'

/-- The map from the received symbol to the relay input of instantaneous relaying, page 17-74. -/
def satoφ : Fin 3 → Fin 2 := ![0, 1, 1]

/-- The input of instantaneous relaying, page 17-74. -/
def satoQ₀ : Fin 3 → ℝ := ![3 / 9, 2 / 9, 4 / 9]

lemma satoQ₀_isPMF : IsPMF satoQ₀ := by
  refine ⟨fun x => ?_, ?_⟩
  · fin_cases x <;> norm_num [satoQ₀]
  · simp only [Fin.sum_univ_three, satoQ₀]
    norm_num

/-- For the Sato channel the receiver sees `X` through the channel with `X₁ = φ(X)`. -/
lemma sato_rwd_marg (x : Fin 3) (φ : Fin 3 → Fin 2) :
    bcMarg₁ (rwdChannel satoW₁ satoW₂') (x, φ) = satoW₂ (x, φ x) := by
  funext y
  simp [bcMarg₁, rwdChannel, satoW₁, satoW₂']

/-- `I(X; Y) = log (9/4)` for instantaneous relaying. -/
lemma sato_info_rwd :
    mutualInfoOf satoQ₀ (fun x => bcMarg₁ (rwdChannel satoW₁ satoW₂') (x, satoφ)) = log (9 / 4) :=
      by
  have hV : IsChannel fun x : Fin 3 => bcMarg₁ (rwdChannel satoW₁ satoW₂') (x, satoφ) := fun x =>
    (rwdChannel_isChannel satoW₁_isChannel satoW₂'_isChannel).bcMarg₁ _
  have hout : outDist satoQ₀ (fun x => bcMarg₁ (rwdChannel satoW₁ satoW₂') (x, satoφ)) = satoQ := by
    funext y
    simp only [sato_rwd_marg, outDist, Fin.sum_univ_three, satoQ₀, satoφ, satoW₂]
    fin_cases y <;> simp [satoQ] <;> norm_num
  rw [mutualInfoOf_eq_sum_relEntropy satoQ₀_isPMF hV, hout]
  simp_rw [sato_rwd_marg, relEntropy_satoW₂]
  rw [← sum_mul, satoQ₀_isPMF.sum_eq_one, one_mul]

/-- **Page 17-74 of [elgamal2010].** The capacity of the Sato relay channel without delay is
`log₂ (9/4) = 1.169925` bits, by instantaneous relaying. -/
theorem sato_rwdCapacity : rwdCapacity (X₁ := Fin 2) satoW₁ satoW₂' = log (9 / 4) / log 2 := by
  have hc := rwdChannel_isChannel (X₁ := Fin 2) satoW₁_isChannel satoW₂'_isChannel
  refine rcCapacity_eq (fun R hR => ?_) fun R hR => ?_
  · refine isAchievableRWD_instantaneous satoW₁_isChannel satoW₂'_isChannel satoQ₀_isPMF satoφ ?_
    rw [sato_info_rwd]
    exact hR
  · refine (IsAchievableRWD.le_rcCutsetBound satoW₁_isChannel satoW₂'_isChannel hR).trans ?_
    refine csSup_le ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    refine (min_le_left _ _).trans ((mutualInfoOf_le_capacity hq hc.bcMarg₁).trans ?_)
    exact sato_le_log hc.bcMarg₁ (fun a => (a.1, a.2 a.1)) fun a => sato_rwd_marg a.1 a.2

/-- **Page 17-19 of [elgamal2010].** The Sato relay channel. -/
def satoW (a : Fin 3 × Fin 2) (o : Fin 3 × Fin 3) : ℝ := satoW₁ a.1 o.2 * satoW₂ a o.1

lemma satoW_isChannel : IsChannel satoW := fun a => by
  refine ⟨fun o => mul_nonneg ((satoW₁_isChannel _).nonneg _) ((satoW₂_isChannel _).nonneg _), ?_⟩
  simp only [satoW]
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [← mul_sum, (satoW₂_isChannel _).sum_eq_one, mul_one]
  exact (satoW₁_isChannel _).sum_eq_one

/-- **Page 17-19 of [elgamal2010].** The Sato relay channel is degraded, so its capacity is given by
decode–forward. -/
theorem sato_isDegradedRC : IsDegradedRC satoW := by
  have hm : ∀ a y₁, bcMarg₂ satoW a y₁ = satoW₁ a.1 y₁ := fun a y₁ => by
    simp only [bcMarg₂, satoW, ← mul_sum, (satoW₂_isChannel a).sum_eq_one, mul_one]
  refine ⟨fun t => satoW₂ (t.2, t.1), fun t => satoW₂_isChannel _, fun a y y₁ => ?_⟩
  rw [hm]
  simp only [satoW, satoW₁]
  by_cases h : y₁ = a.1
  · simp [h]
  · simp [h]

/-- The capacity of the Sato relay channel is at most `log₂ (9/4)`. The notes cite its value
`1.161878` bits, which is not proved here. -/
theorem sato_rcCapacity_le : rcCapacity satoW ≤ log (9 / 4) / log 2 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  refine csSup_le ⟨0, isAchievableRC_of_nonpos le_rfl⟩ fun R hR => ?_
  rw [le_div_iff₀ hlog2]
  refine (hR.le_rcCutsetBound satoW_isChannel).trans ?_
  refine csSup_le ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩ ?_
  rintro _ ⟨q, hq, rfl⟩
  refine (min_le_left _ _).trans ((mutualInfoOf_le_capacity hq satoW_isChannel.bcMarg₁).trans ?_)
  refine sato_le_log satoW_isChannel.bcMarg₁ id fun a => ?_
  funext y
  simp only [bcMarg₁, satoW, ← sum_mul, (satoW₁_isChannel _).sum_eq_one, one_mul, id]

end InfoTheory.ElGamalKim
