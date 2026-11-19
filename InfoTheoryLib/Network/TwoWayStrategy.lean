/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DependenceBalance

/-!
# Strategies for the two-way channel with a common output

A strategy of length `k` chooses each input from the past outputs. Two strategies drive the channel:
the result is a super-channel from pairs of strategies to `k` outputs.

## Main definitions

* `Strat`: the strategies of length `k`.
* `stratW`: the super-channel.
* `TWCCode.strat₁`, `TWCCode.strat₂`: the strategies of a message.
* `twcMultiRegion`: the rate pairs of strategies of length `k`.

## Main statements

* `condInfo_le_cInfo_of_law`: the information of the messages is at most the one of their functions.
* `TWCCode.exists_strat`: the outer bound for one code.
* `IsAchievableTWC.mem_closure_iUnion_twcMultiRegion`: **the outer bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- **A strategy of length `k`.** It chooses the input at time `i` from the outputs before time `i`.
-/
def Strat (k : ℕ) (α γ : Type*) : Type _ := ∀ i : Fin k, (Fin i → γ) → α

instance {k : ℕ} {α γ : Type*} [Fintype α] [Fintype γ] : Fintype (Strat k α γ) := by
  classical
  unfold Strat
  infer_instance

instance {k : ℕ} {α γ : Type*} [Nonempty α] : Nonempty (Strat k α γ) :=
  ⟨fun _ _ => Classical.arbitrary α⟩

/-- The information of the messages is at most the one of the functions of the messages that
determine the law of the output. -/
theorem condInfo_le_cInfo_of_law {Ω Ma Mb A B Z : Type*} [Fintype Ω] [Fintype Ma] [Fintype Mb]
    [Fintype A] [Fintype B] [Fintype Z] {μ : Ω → ℝ} (hμ : IsPMF μ) (ma : Ω → Ma) (mb : Ω → Mb)
    (O : Ω → Z) (ta : Ma → A) (tb : Mb → B) {q : A × B → ℝ} {T : A × B → Z → ℝ} (hq : IsPMF q)
    (hT : IsChannel T)
    (hd : dist μ (fun ω => ((ta (ma ω), tb (mb ω)), O ω)) = jointOf q T)
    (hrow : ∀ x o, dist μ (pair (pair ma mb) O) (x, o) =
      dist μ (pair ma mb) x * T (ta x.1, tb x.2) o) :
    I[ma : O | mb ; μ] ≤ cInfo q T := by
  classical
  have hJ := jointOf_isPMF hq hT
  have hI : I[ma : O | mb ; μ] = H[O | mb ; μ] - H[O | pair ma mb ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    congr 1
    exact condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have h₁ : H[O | pair ma mb ; μ] = ∑ t, q t * entropy (T t) := by
    have hch := condEntropy_of_channel (W := T) (μ := μ) (Z := pair ma mb) (Y := O)
      (fun x : Ma × Mb => (ta x.1, tb x.2)) hrow
    have hdq : dist μ ((fun x : Ma × Mb => (ta x.1, tb x.2)) ∘ pair ma mb) = q := by
      have h := dist_jointOf_fst (p := q) (W := T) hT
      rw [← hd, ← dist_comp_eq] at h
      exact h
    rw [hch, hdq]
  have h₂ : H[O | mb ; μ] ≤ H[O | tb ∘ mb ; μ] := condEntropy_le_condEntropy_comp hμ O mb tb
  have h₃ : H[O | tb ∘ mb ; μ] = H[Prod.snd | fun z : (A × B) × Z => z.1.2 ; jointOf q T] := by
    refine condEntropy_eq_of_dist_pair_eq hμ hJ ?_
    rw [← hd, ← dist_comp_eq]
    rfl
  rw [hI, h₁, cInfo_eq hq hT, ← h₃]
  linarith

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y] {V : X₁ × X₂ → Y → ℝ} {k : ℕ}

/-- **The super-channel.** The law of `k` outputs when two strategies drive the channel. -/
def stratW (V : X₁ × X₂ → Y → ℝ) (k : ℕ) (s : Strat k X₁ Y × Strat k X₂ Y) (y : Fin k → Y) : ℝ :=
  ∏ i, V (s.1 i (fbPre i y), s.2 i (fbPre i y)) (y i)

section Enc

variable [Nonempty X₁] [Nonempty X₂]

/-- The encoder of a pair of strategies, as an encoder with feedback. -/
def stratEnc (k : ℕ) : ∀ i, Strat k X₁ Y × Strat k X₂ Y → (Fin i → Y) → X₁ × X₂ :=
  fun i s u => if h : i < k then (s.1 ⟨i, h⟩ u, s.2 ⟨i, h⟩ u) else
    (Classical.arbitrary X₁, Classical.arbitrary X₂)

omit [Fintype X₁] [Fintype X₂] [Fintype Y] in
lemma stratW_eq_prod (s : Strat k X₁ Y × Strat k X₂ Y) (y : Fin k → Y) :
    stratW V k s y =
      ∏ i : Fin k, V (stratEnc k i s fun t : Fin i => y ⟨t, t.isLt.trans i.isLt⟩) (y i) := by
  refine prod_congr rfl fun i _ => ?_
  simp [stratEnc, i.isLt]
  rfl

omit [Fintype X₁] [Fintype X₂] in
/-- **The super-channel is a channel.** -/
theorem stratW_isChannel [Finite X₁] [Finite X₂] (hV : IsChannel V) :
    IsChannel (stratW V k) := fun s => by
  classical
  have : Fintype X₁ := Fintype.ofFinite X₁
  have : Fintype X₂ := Fintype.ofFinite X₂
  refine ⟨fun y => prod_nonneg fun i _ => (hV _).nonneg _, ?_⟩
  have h := congrFun (dist_fst_fbLaw (ν := uniformPMF (Strat k X₁ Y × Strat k X₂ Y)) (W := V)
    (enc := stratEnc k) hV k) s
  simp only [dist, Fintype.sum_prod_type] at h
  rw [Finset.sum_eq_single s.1, Finset.sum_eq_single s.2] at h
  · simp only [ite_true] at h
    have hl : ∀ y, fbLaw (uniformPMF (Strat k X₁ Y × Strat k X₂ Y)) V (stratEnc k) k
      ((s.1, s.2), y) =
        uniformPMF (Strat k X₁ Y × Strat k X₂ Y) s * stratW V k s y := fun y => by
      rw [fbLaw_eq_prod, stratW_eq_prod]
    simp_rw [hl, ← mul_sum] at h
    have hu : uniformPMF (Strat k X₁ Y × Strat k X₂ Y) s ≠ 0 := by
      have := Fintype.card_pos (α := Strat k X₁ Y × Strat k X₂ Y)
      simp [uniformPMF]
    exact mul_left_cancel₀ hu (h.trans (mul_one _).symm)
  · intro b _ hb
    refine sum_eq_zero fun y _ => ite_eq_right fun h' => absurd ?_ hb
    exact (Prod.ext_iff.mp h').2
  · simp
  · intro a _ ha
    refine sum_eq_zero fun b _ => sum_eq_zero fun y _ => ite_eq_right fun h' => absurd ?_ ha
    exact (Prod.ext_iff.mp h').1
  · simp

end Enc

/-- **Page 18-55 of [elgamal2010], with strategies.** The rate pairs, in bits, of independent random
strategies of length `k`: `k R₁ ≤ I(T₁; Yᵏ | T₂)` and `k R₂ ≤ I(T₂; Yᵏ | T₁)`. -/
def twcMultiRegion (V : X₁ × X₂ → Y → ℝ) (k : ℕ) : Set (ℝ × ℝ) :=
  {R | ∃ (p₁ : Strat k X₁ Y → ℝ) (p₂ : Strat k X₂ Y → ℝ), IsPMF p₁ ∧ IsPMF p₂ ∧
    k * (R.1 * log 2) ≤ cInfo (prodDist p₁ p₂) (stratW V k) ∧
    k * (R.2 * log 2) ≤ cInfo (prodDist p₂ p₁) fun t => stratW V k t.swap}

namespace TWCCode

variable {M₁ M₂ n : ℕ} (c : TWCCode M₁ M₂ n X₁ X₂ Y Y)

/-- The strategy of a message of node 1. -/
def strat₁ (w : Fin M₁) : Strat n X₁ Y := fun i u => c.enc₁ i w u

/-- The strategy of a message of node 2. -/
def strat₂ (w : Fin M₂) : Strat n X₂ Y := fun i u => c.enc₂ i w u

omit [Fintype X₁] [Fintype X₂] [Fintype Y] in
/-- The law of the code as a law of the super-channel. -/
lemma law_eq_stratW (w : Fin M₁ × Fin M₂) (y : Fin n → Y) :
    c.law V id id (w, y) =
      uniformPMF (Fin M₁ × Fin M₂) w * stratW V n (c.strat₁ w.1, c.strat₂ w.2) y := by
  rw [TWCCode.law, fbLaw_eq_prod]
  rfl

omit [Fintype X₁] [Fintype X₂] [Fintype Y] in
/-- The law of a pair of independent uniform messages. -/
lemma dist_uniform_strat :
    dist (uniformPMF (Fin M₁ × Fin M₂)) (fun w => (c.strat₁ w.1, c.strat₂ w.2)) =
      prodDist (dist (uniformPMF (Fin M₁)) c.strat₁) (dist (uniformPMF (Fin M₂)) c.strat₂) := by
  classical
  funext ⟨s₁, s₂⟩
  simp only [dist, prodDist, Fintype.sum_prod_type, Prod.mk.injEq, uniformPMF, Fintype.card_prod,
    Fintype.card_fin]
  rw [sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases h₁ : c.strat₁ a = s₁ <;> by_cases h₂ : c.strat₂ b = s₂ <;> simp [h₁, h₂]
  ring

variable [Nonempty X₁] [Nonempty X₂]

/-- **The outer bound for one code.** -/
theorem exists_strat (hV : IsChannel V) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    ∃ (p₁ : Strat n X₁ Y → ℝ) (p₂ : Strat n X₂ Y → ℝ), IsPMF p₁ ∧ IsPMF p₂ ∧
      log M₁ ≤ cInfo (prodDist p₁ p₂) (stratW V n) + log 2 + c.err₂ V id id * log M₁ ∧
      log M₂ ≤ cInfo (prodDist p₂ p₁) (fun t => stratW V n t.swap) + log 2 +
        c.err₁ V id id * log M₂ := by
  classical
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hμ := c.law_isPMF (W := V) (v₁ := id) (v₂ := id) hV h₁ h₂
  set μ := c.law V id id with hμd
  set p₁ := dist (uniformPMF (Fin M₁)) c.strat₁ with hp₁d
  set p₂ := dist (uniformPMF (Fin M₂)) c.strat₂ with hp₂d
  have hp₁ : IsPMF p₁ := uniformPMF_isPMF.dist _
  have hp₂ : IsPMF p₂ := uniformPMF_isPMF.dist _
  have hS := stratW_isChannel (k := n) hV
  have hSs : IsChannel fun t : Strat n X₂ Y × Strat n X₁ Y => stratW V n t.swap := fun t => hS _
  -- the law of the messages and of the outputs
  have hJ : μ = jointOf (uniformPMF (Fin M₁ × Fin M₂))
      fun w => stratW V n (c.strat₁ w.1, c.strat₂ w.2) := by
    funext ⟨w, y⟩
    exact c.law_eq_stratW w y
  have hd₁ : dist μ (fun z => ((c.strat₁ z.1.1, c.strat₂ z.1.2), z.2)) =
      jointOf (prodDist p₁ p₂) (stratW V n) := by
    rw [hJ, ← c.dist_uniform_strat]
    exact dist_jointOf_map (fun w : Fin M₁ × Fin M₂ => (c.strat₁ w.1, c.strat₂ w.2)) (stratW V n)
  have hrow₁ : ∀ (x : Fin M₁ × Fin M₂) (o : Fin n → Y),
      dist μ (pair (pair (fun z => z.1.1) fun z => z.1.2) Prod.snd) (x, o) =
        dist μ (pair (fun z => z.1.1) fun z => z.1.2) x *
          stratW V n (c.strat₁ x.1, c.strat₂ x.2) o := by
    intro x o
    have e₁ : (pair (pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1) fun z => z.1.2)
        Prod.snd) = id := rfl
    have e₂ : (pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1) fun z => z.1.2) =
        Prod.fst := rfl
    have e₃ : dist μ Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hV n
    rw [e₁, e₂, dist_id, e₃, hμd]
    exact c.law_eq_stratW x o
  have hrow₂ : ∀ (x : Fin M₂ × Fin M₁) (o : Fin n → Y),
      dist μ (pair (pair (fun z => z.1.2) fun z => z.1.1) Prod.snd) (x, o) =
        dist μ (pair (fun z => z.1.2) fun z => z.1.1) x *
          stratW V n (c.strat₂ x.1, c.strat₁ x.2).swap o := by
    intro x o
    have hinj : Function.Injective fun t : (Fin M₁ × Fin M₂) × (Fin n → Y) =>
        (t.1.swap, t.2) := fun s t h => by
      have h' := Prod.ext_iff.mp h
      exact Prod.ext (Prod.swap_injective h'.1) h'.2
    have e₁ := dist_comp_of_injective μ id hinj (x.swap, o)
    rw [dist_id] at e₁
    have e₂ := dist_comp_of_injective (dist μ Prod.fst) id Prod.swap_injective x.swap
    rw [dist_id, ← dist_comp_eq] at e₂
    have e₃ : dist μ Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hV n
    rw [e₃] at e₂
    have ee₁ : dist μ (pair (pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.2)
        fun z => z.1.1) Prod.snd) (x, o) = μ (x.swap, o) := e₁
    have ee₂ : dist μ (pair (fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.2)
        fun z => z.1.1) x = uniformPMF (Fin M₁ × Fin M₂) x.swap := by
      rw [← e₂]
      rfl
    rw [ee₁, ee₂, hμd]
    exact c.law_eq_stratW x.swap o
  have hP₂₁ : IsPMF (prodDist p₂ p₁) := hp₂.prodDist hp₁
  have hd₂ : dist μ (fun z => ((c.strat₂ z.1.2, c.strat₁ z.1.1), z.2)) =
      jointOf (prodDist p₂ p₁) fun t => stratW V n t.swap := by
    have hinj : Function.Injective fun t : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) =>
        (t.1.swap, t.2) := fun s t h => by
      have h' := Prod.ext_iff.mp h
      exact Prod.ext (Prod.swap_injective h'.1) h'.2
    have e₀ : dist μ (fun z => ((c.strat₂ z.1.2, c.strat₁ z.1.1), z.2)) =
        dist (dist μ fun z => ((c.strat₁ z.1.1, c.strat₂ z.1.2), z.2))
          fun t : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => (t.1.swap, t.2) :=
      dist_comp_eq μ (fun z => ((c.strat₁ z.1.1, c.strat₂ z.1.2), z.2))
        fun t : (Strat n X₁ Y × Strat n X₂ Y) × (Fin n → Y) => (t.1.swap, t.2)
    rw [e₀, hd₁]
    funext ⟨t, o⟩
    have e₁ := dist_comp_of_injective (jointOf (prodDist p₁ p₂) (stratW V n)) id hinj (t.swap, o)
    rw [dist_id] at e₁
    refine e₁.trans ?_
    simp [jointOf, prodDist, mul_comm]
  have hf₂ := c.log_le_of_fano₂ (W := V) (v₁ := id) (v₂ := id) hV h₁ h₂
  have hf₁ := c.log_le_of_fano₁ (W := V) (v₁ := id) (v₂ := id) hV h₁ h₂
  have hb₂ := condInfo_le_cInfo_of_law hμ (fun z => z.1.1) (fun z => z.1.2) Prod.snd c.strat₁
    c.strat₂ (hp₁.prodDist hp₂) hS hd₁ hrow₁
  have hb₁ := condInfo_le_cInfo_of_law hμ (fun z => z.1.2) (fun z => z.1.1) Prod.snd c.strat₂
    c.strat₁ hP₂₁ hSs hd₂ hrow₂
  refine ⟨p₁, p₂, hp₁, hp₂, ?_, ?_⟩
  · have e : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : fun z i => id (z.2 i) |
        fun z => z.1.2 ; c.law V id id] = I[fun z => z.1.1 : Prod.snd | fun z => z.1.2 ; μ] := rfl
    rw [e] at hf₂
    linarith
  · have e : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.2 : fun z i => id (z.2 i) |
        fun z => z.1.1 ; c.law V id id] = I[fun z => z.1.2 : Prod.snd | fun z => z.1.1 ; μ] := rfl
    rw [e] at hf₁
    linarith

end TWCCode

/-- **Theorem 7, the converse, page 18-57 of [elgamal2010], with strategies.** -/
theorem IsAchievableTWC.mem_closure_iUnion_twcMultiRegion [Nonempty X₁] [Nonempty X₂]
    (hV : IsChannel V) {R₁ R₂ : ℝ} (h : IsAchievableTWC (commonTW V) R₁ R₂) :
    (R₁, R₂) ∈ closure (⋃ k : ℕ, ⋃ _ : 0 < k, twcMultiRegion V k) := by
  obtain ⟨c, hc⟩ := h
  set a₁ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₁⌉₊ with ha₁
  set a₂ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₂⌉₊ with ha₂
  set P : ℕ → ℝ := fun n => (c n).errProb (commonTW V) with hPdef
  set ε : ℕ → ℝ := fun n => (1 + P n * ((a₁ n : ℝ) + a₂ n)) / n with hεdef
  have hpos₁ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := fun n => by positivity
  have hpos₂ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := fun n => by positivity
  have he₁ : ∀ n, 0 ≤ (c n).err₁ V id id := fun n =>
    errProb_nonneg ((c n).law_isPMF hV (hpos₁ n) (hpos₂ n)) _ _ _
  have he₂ : ∀ n, 0 ≤ (c n).err₂ V id id := fun n =>
    errProb_nonneg ((c n).law_isPMF hV (hpos₁ n) (hpos₂ n)) _ _ _
  have hPe : ∀ n, P n = (c n).err₁ V id id + (c n).err₂ V id id := fun n => by
    simp only [hPdef, TWCCode.errProb, TWCCode.err₁_commonTW, TWCCode.err₂_commonTW]
  have hP₁ : ∀ n, (c n).err₁ V id id ≤ P n := fun n => by
    rw [hPe]
    linarith [he₂ n]
  have hP₂ : ∀ n, (c n).err₂ V id id ≤ P n := fun n => by
    rw [hPe]
    linarith [he₁ n]
  have hP0 : ∀ n, 0 ≤ P n := fun n => (he₁ n).trans (hP₁ n)
  have hL := log_two_pos'
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈
      ⋃ k : ℕ, ⋃ _ : 0 < k, twcMultiRegion V k := by
    intro n hn
    obtain ⟨p₁, p₂, hp₁, hp₂, b₁, b₂⟩ := (c n).exists_strat hV (hpos₁ n) (hpos₂ n)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn, p₁, p₂, hp₁, hp₂, ?_, ?_⟩⟩
    · have h₃ := degradedBC_rate_le (b := a₂ n) (R := R₁) hn (hP0 n) (hP₂ n)
        (by exact_mod_cast b₁)
      have h₄ := (le_div_iff₀ hL).mp h₃
      have h₅ := mul_le_mul_of_nonneg_left h₄ hn'.le
      refine h₅.trans (le_of_eq ?_)
      field_simp
    · have h₃ := degradedBC_rate_le (b := a₁ n) (R := R₂) hn (hP0 n) (hP₁ n)
        (by exact_mod_cast b₂)
      have e : ε n = (1 + P n * ((a₂ n : ℝ) + a₁ n)) / n := by
        simp only [hεdef, add_comm]
      rw [e]
      have h₄ := (le_div_iff₀ hL).mp h₃
      have h₅ := mul_le_mul_of_nonneg_left h₄ hn'.le
      refine h₅.trans (le_of_eq ?_)
      field_simp
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_rate_eps hc hP0
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

end InfoTheory
