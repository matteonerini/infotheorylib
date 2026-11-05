/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayCode

/-!
# The multiple access channel with feedback

Pages 18-19 to 18-21 of the notes: the code, the capacity region and the cooperative outer bound.

## Main definitions

* `MACFBCode`: a code for the multiple access channel with noiseless causal feedback to both
  senders.
* `IsAchievableMACFB`, `macfbCapacityRegion`: achievable rates and the capacity region.
* `macCoopRegion`: the cooperative outer bound.

## Main statements

* `MACFBCode.exists_input_law`: the outer bound for one code.
* `IsAchievableMACFB.mem_closure_macCoopRegion`: **the cooperative outer bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- **Page 18-19 of [elgamal2010].** A code for the multiple access channel with noiseless causal
feedback to both senders. -/
structure MACFBCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*) where
  /-- The encoder of sender 1. -/
  enc₁ : ∀ k, Fin M₁ → (Fin k → β) → α₁
  /-- The encoder of sender 2. -/
  enc₂ : ∀ k, Fin M₂ → (Fin k → β) → α₂
  /-- The decoder. -/
  dec : (Fin n → β) → Fin M₁ × Fin M₂

namespace MACFBCode

variable {M₁ M₂ n : ℕ} {α₁ α₂ β : Type*} (c : MACFBCode M₁ M₂ n α₁ α₂ β)

/-- The two encoders, as an encoder with feedback. -/
def fbEnc : ∀ k, Fin M₁ × Fin M₂ → (Fin k → β) → α₁ × α₂ :=
  fun k w z => (c.enc₁ k w.1 z, c.enc₂ k w.2 z)

/-- The code as a code for a two-way channel with the same output at the two nodes, where the
decoders ignore the messages of their nodes. -/
def toTW : TWCCode M₁ M₂ n α₁ α₂ β β where
  enc₁ := c.enc₁
  enc₂ := c.enc₂
  dec₁ _ y := (c.dec y).2
  dec₂ _ y := (c.dec y).1

variable [Fintype β]

/-- The joint law of the uniform messages and of the outputs. -/
def law (W : α₁ × α₂ → β → ℝ) : (Fin M₁ × Fin M₂) × (Fin n → β) → ℝ :=
  fbLaw (uniformPMF (Fin M₁ × Fin M₂)) W c.fbEnc n

/-- **Page 18-19 of [elgamal2010].** The average probability of error. -/
def errProb (W : α₁ × α₂ → β → ℝ) : ℝ :=
  InfoTheory.errProb (c.law W) Prod.fst Prod.snd c.dec

variable {W : α₁ × α₂ → β → ℝ}

lemma law_isPMF (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) : IsPMF (c.law W) :=
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  fbLaw_isPMF uniformPMF_isPMF hW n

omit [Fintype β] in
lemma toTW_law : c.toTW.law W id id = c.law W := rfl

/-- The error of decoder 2 of the two-way code is at most the error of the code. -/
lemma toTW_err₂_le (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    c.toTW.err₂ W id id ≤ c.errProb W := by
  classical
  have hμ := c.law_isPMF hW h₁ h₂
  refine sum_le_sum fun ω _ => ?_
  by_cases h : c.dec ω.2 = ω.1
  · have h' : (c.dec ω.2).1 = ω.1.1 := by rw [h]
    refine le_trans (le_of_eq (ite_eq_right (not_not.mpr h'))) ?_
    exact (le_of_eq (ite_eq_right (not_not.mpr h)).symm)
  · refine le_trans ?_ (le_of_eq (ite_eq_left h).symm)
    split_ifs
    · exact le_rfl
    · exact hμ.nonneg ω

/-- The error of decoder 1 of the two-way code is at most the error of the code. -/
lemma toTW_err₁_le (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    c.toTW.err₁ W id id ≤ c.errProb W := by
  classical
  have hμ := c.law_isPMF hW h₁ h₂
  refine sum_le_sum fun ω _ => ?_
  by_cases h : c.dec ω.2 = ω.1
  · have h' : (c.dec ω.2).2 = ω.1.2 := by rw [h]
    refine le_trans (le_of_eq (ite_eq_right (not_not.mpr h'))) ?_
    exact (le_of_eq (ite_eq_right (not_not.mpr h)).symm)
  · refine le_trans ?_ (le_of_eq (ite_eq_left h).symm)
    split_ifs
    · exact le_rfl
    · exact hμ.nonneg ω

/-- **Fano's inequality for the pair of messages.** -/
lemma log_le_of_fano (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    log ((M₁ : ℝ) * M₂) ≤ I[Prod.fst : Prod.snd ; c.law W] + log 2 +
      c.errProb W * log ((M₁ : ℝ) * M₂) := by
  classical
  have hμ := c.law_isPMF hW h₁ h₂
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  have hd : dist (c.law W) Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hW n
  have hH : H[Prod.fst ; c.law W] = log ((M₁ : ℝ) * M₂) := by
    rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  have hF := fano_weak hμ (Prod.fst : (Fin M₁ × Fin M₂) × (Fin n → β) → _) Prod.snd c.dec
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hF
  push_cast at hF
  have hI : I[Prod.fst : Prod.snd ; c.law W] = H[Prod.fst ; c.law W] -
      H[Prod.fst | Prod.snd ; c.law W] := mutualInfo_eq_entropy_sub_condEntropy hμ _ _
  have he : InfoTheory.errProb (c.law W) Prod.fst Prod.snd c.dec = c.errProb W := rfl
  rw [he] at hF
  rw [hI, hH]
  linarith

/-- The law of the inputs at time `i`. -/
def letter [Fintype α₁] [Fintype α₂] (W : α₁ × α₂ → β → ℝ) (i : Fin n) : α₁ × α₂ → ℝ :=
  dist (c.law W) fun z => c.fbEnc i z.1 (fbPre i z.2)

end MACFBCode

/-- The bound `I(M; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`, with or without feedback. -/
theorem mutualInfo_fbLaw_le_sum {𝒲 α β : Type*} [Fintype 𝒲] [Fintype α] [Fintype β] {ν : 𝒲 → ℝ}
    {W : α → β → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β) → α} (hν : IsPMF ν) (hW : IsChannel W) (n : ℕ) :
    I[Prod.fst : Prod.snd ; fbLaw ν W enc n] ≤
      ∑ i : Fin n, mutualInfoOf (dist (fbLaw ν W enc n) fun z => enc i z.1 (fbPre i z.2)) W := by
  classical
  have hl : ∀ k (i : Fin k), dist (fbLaw ν W enc k) (fun z => enc i z.1 (fbPre i z.2)) =
      dist (fbLaw ν W enc (i + 1)) fun z => enc i z.1 (Fin.init z.2) := by
    intro k i
    have h := dist_fbLaw_prefix (ν := ν) (W := W) (enc := enc) hW (i + 1) k i.2
    rw [← h, ← dist_comp_eq]
    rfl
  induction n with
  | zero =>
    have hμ := fbLaw_isPMF (enc := enc) hν hW 0
    rw [mutualInfo_eq_entropy_sub_condEntropy' hμ]
    have h₀ : H[Prod.snd ; fbLaw ν W enc 0] = 0 := by
      have := entropy_le_log_card (hμ.dist (Prod.snd : 𝒲 × (Fin 0 → β) → Fin 0 → β))
      have h0 := entropyRV_nonneg hμ (Prod.snd : 𝒲 × (Fin 0 → β) → Fin 0 → β)
      simp only [Fintype.card_pi, Finset.univ_eq_empty, prod_empty, Nat.cast_one, log_one] at this
      exact le_antisymm this h0
    have h₁ := condEntropy_nonneg hμ (Prod.snd : 𝒲 × (Fin 0 → β) → Fin 0 → β) Prod.fst
    simp only [Fin.sum_univ_zero]
    linarith
  | succ k ih =>
    refine (mutualInfo_fbLaw_succ_le_mutualInfoOf hν hW k).trans ?_
    rw [Fin.sum_univ_castSucc]
    refine add_le_add (ih.trans (le_of_eq (sum_congr rfl fun i _ => ?_))) (le_of_eq ?_)
    · rw [hl k i, hl (k + 1) (Fin.castSucc i)]
      rfl
    · rw [hl (k + 1) (Fin.last k)]
      rfl

section Coop

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}

/-- **The cooperative outer bound, page 18-20 of [elgamal2010]**, in bits. -/
def macCoopRegion (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ p : α₁ × α₂ → ℝ, IsPMF p ∧ R.1 ≤ cInfo p W / log 2 ∧
    R.2 ≤ cInfo (fun a : α₂ × α₁ => p a.swap) (fun t => W t.swap) / log 2 ∧
    R.1 + R.2 ≤ mutualInfoOf p W / log 2}

/-- **The outer bound for one code.** -/
theorem MACFBCode.exists_input_law {M₁ M₂ n : ℕ} (c : MACFBCode M₁ M₂ n α₁ α₂ β) (hW : IsChannel W)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (hn : 0 < n) :
    ∃ p : α₁ × α₂ → ℝ, IsPMF p ∧
      log M₁ ≤ n * cInfo p W + log 2 + c.errProb W * log M₁ ∧
      log M₂ ≤ n * cInfo (fun a : α₂ × α₁ => p a.swap) (fun t => W t.swap) + log 2 +
        c.errProb W * log M₂ ∧
      log ((M₁ : ℝ) * M₂) ≤ n * mutualInfoOf p W + log 2 +
        c.errProb W * log ((M₁ : ℝ) * M₂) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  have hμ := c.law_isPMF hW h₁ h₂
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : IsPMF (uniformPMF (Fin n)) := uniformPMF_isPMF
  have hwv : ∀ i : Fin n, uniformPMF (Fin n) i = 1 / n := fun i => by simp [uniformPMF]
  have hq : ∀ i : Fin n, IsPMF (c.letter W i) := fun i => hμ.dist _
  have hswap : ∀ i : Fin n, IsPMF fun a : α₂ × α₁ => c.letter W i a.swap := fun i =>
    ⟨fun a => (hq i).nonneg _, (Equiv.sum_comp (Equiv.prodComm α₂ α₁) (c.letter W i)).trans
      (hq i).sum_eq_one⟩
  let p : α₁ × α₂ → ℝ := fun a => ∑ i, uniformPMF (Fin n) i * c.letter W i a
  have hp : IsPMF p := by
    refine ⟨fun a => sum_nonneg fun i _ => mul_nonneg (hw.nonneg i) ((hq i).nonneg a), ?_⟩
    simp only [p]
    rw [sum_comm]
    simp_rw [← mul_sum, (hq _).sum_eq_one, mul_one, hw.sum_eq_one]
  have hsum : ∀ g : Fin n → ℝ, ∑ i, g i = n * ∑ i, uniformPMF (Fin n) i * g i := by
    intro g
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hwv]
    field_simp
  have hid : ∀ t, dist (W t) id = W t := fun t => dist_id _
  have hidk : (fun t => dist (W t) id) = W := funext hid
  have herr₂ := c.toTW_err₂_le hW h₁ h₂
  have herr₁ := c.toTW_err₁_le hW h₁ h₂
  have hlog₁ : 0 ≤ log (M₁ : ℝ) := log_natCast_nonneg M₁
  have hlog₂ : 0 ≤ log (M₂ : ℝ) := log_natCast_nonneg M₂
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · have hb := c.toTW.log_le_sum₂ (W := W) (v₁ := id) (v₂ := id) hW h₁ h₂
    rw [hidk] at hb
    have hc := sum_cInfo_le hw hq hW
    have hlet : ∀ i, c.toTW.letter W id id i = c.letter W i := fun _ => rfl
    simp only [hlet] at hb
    rw [hsum] at hb
    have := mul_le_mul_of_nonneg_left hc hn'.le
    have h3 := mul_le_mul_of_nonneg_right herr₂ hlog₁
    linarith
  · have hb := c.toTW.log_le_sum₁ (W := W) (v₁ := id) (v₂ := id) hW h₁ h₂
    have hidk' : (fun t : α₂ × α₁ => dist (W t.swap) id) = fun t => W t.swap :=
      funext fun t => hid _
    have hK : IsChannel fun t : α₂ × α₁ => W t.swap := fun t => hW _
    rw [hidk'] at hb
    have hc := sum_cInfo_le hw hswap hK
    have hlet : ∀ i, c.toTW.letterSwap W id id i = fun a : α₂ × α₁ => c.letter W i a.swap :=
      fun _ => rfl
    simp only [hlet] at hb
    rw [hsum] at hb
    have := mul_le_mul_of_nonneg_left hc hn'.le
    have h3 := mul_le_mul_of_nonneg_right herr₁ hlog₂
    linarith
  · have hf := c.log_le_of_fano hW h₁ h₂
    have hI := mutualInfo_fbLaw_le_sum (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := W)
      (enc := c.fbEnc) uniformPMF_isPMF hW n
    have hI' : I[Prod.fst : Prod.snd ; c.law W] ≤ ∑ i : Fin n, mutualInfoOf (c.letter W i) W := hI
    have hcon := (mutualInfoOf_concave_input hW).le_map_sum (t := univ)
      (w := uniformPMF (Fin n)) (p := fun i : Fin n => c.letter W i)
      (fun i _ => hw.nonneg i) hw.sum_eq_one (fun i _ => hq i)
    have hmix : (∑ i : Fin n, uniformPMF (Fin n) i • c.letter W i) = p := by
      funext a
      simp [p, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hmix] at hcon
    simp only [smul_eq_mul] at hcon
    rw [hsum] at hI'
    have := mul_le_mul_of_nonneg_left hcon hn'.le
    linarith

/-- A rate pair, in bits, is achievable for the multiple access channel with feedback. -/
def IsAchievableMACFB (W : α₁ × α₂ → β → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, MACFBCode (2 ^ ⌈(n : ℝ) * R₁⌉₊) (2 ^ ⌈(n : ℝ) * R₂⌉₊) n α₁ α₂ β,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Page 18-19 of [elgamal2010].** The capacity region with feedback. -/
def macfbCapacityRegion (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableMACFB W R.1 R.2}

/-- **The cooperative outer bound, page 18-20 of [elgamal2010].** -/
theorem IsAchievableMACFB.mem_closure_macCoopRegion (hW : IsChannel W)
    {R₁ R₂ : ℝ} (h : IsAchievableMACFB W R₁ R₂) : (R₁, R₂) ∈ closure (macCoopRegion W) := by
  obtain ⟨c, hc⟩ := h
  set a₁ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₁⌉₊ with ha₁
  set a₂ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₂⌉₊ with ha₂
  set P : ℕ → ℝ := fun n => (c n).errProb W with hPdef
  set ε : ℕ → ℝ := fun n => (1 + P n * ((a₁ n : ℝ) + a₂ n)) / n with hεdef
  have hpos₁ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := fun n => by positivity
  have hpos₂ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := fun n => by positivity
  have hP0 : ∀ n, 0 ≤ P n := fun n => errProb_nonneg ((c n).law_isPMF hW (hpos₁ n) (hpos₂ n)) _ _ _
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg zero_le_one
    (mul_nonneg (hP0 n) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))) (Nat.cast_nonneg n)
  have hL := log_two_pos'
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ macCoopRegion W := by
    intro n hn
    obtain ⟨p, hp, b₁, b₂, b₃⟩ := (c n).exists_input_law hW (hpos₁ n) (hpos₂ n) hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨p, hp, ?_, ?_, ?_⟩
    · have h₃ := degradedBC_rate_le (b := a₂ n) (S := n * cInfo p W) (R := R₁) hn (hP0 n) le_rfl
        (by exact_mod_cast b₁)
      refine h₃.trans (le_of_eq ?_)
      field_simp
    · have h₃ := degradedBC_rate_le (b := a₁ n)
        (S := n * cInfo (fun a : α₂ × α₁ => p a.swap) (fun t => W t.swap)) (R := R₂) hn (hP0 n)
          le_rfl
        (by exact_mod_cast b₂)
      have e : ε n = (1 + P n * ((a₂ n : ℝ) + a₁ n)) / n := by
        simp only [hεdef, add_comm]
      rw [e]
      refine h₃.trans (le_of_eq ?_)
      field_simp
    · have hlogM : log (((2 ^ a₁ n : ℕ) : ℝ) * ((2 ^ a₂ n : ℕ) : ℝ)) =
          ((a₁ n : ℝ) + a₂ n) * log 2 := by
        push_cast
        rw [log_mul (by positivity) (by positivity), log_pow, log_pow]
        ring
      have b₃' : ((a₁ n : ℝ) + a₂ n) * log 2 ≤ n * mutualInfoOf p W + log 2 +
          P n * (((a₁ n : ℝ) + a₂ n) * log 2) := by
        rw [← hlogM]
        exact_mod_cast b₃
      have hR₁ : (n : ℝ) * R₁ ≤ a₁ n := Nat.le_ceil _
      have hR₂ : (n : ℝ) * R₂ ≤ a₂ n := Nat.le_ceil _
      rw [le_div_iff₀ hL]
      have key : (n : ℝ) * (R₁ + R₂) ≤ n * mutualInfoOf p W / log 2 + 1 +
          P n * ((a₁ n : ℝ) + a₂ n) := by
        have h₄ : ((a₁ n : ℝ) + a₂ n) ≤ n * mutualInfoOf p W / log 2 + 1 +
            P n * ((a₁ n : ℝ) + a₂ n) := by
          rw [← sub_nonneg]
          have : n * mutualInfoOf p W / log 2 + 1 + P n * ((a₁ n : ℝ) + a₂ n) -
              ((a₁ n : ℝ) + a₂ n) = (n * mutualInfoOf p W + log 2 +
                P n * (((a₁ n : ℝ) + a₂ n) * log 2) - ((a₁ n : ℝ) + a₂ n) * log 2) / log 2 := by
            field_simp
          rw [this]
          exact div_nonneg (by linarith) hL.le
        linarith
      have hεn : ε n * n = 1 + P n * ((a₁ n : ℝ) + a₂ n) := by
        simp only [hεdef]
        field_simp
      have key' : (R₁ - ε n + (R₂ - ε n)) * n ≤ n * mutualInfoOf p W / log 2 := by
        have h5 := hε0 n
        have h6 : 0 ≤ ε n * n := mul_nonneg h5 hn'.le
        nlinarith
      have h7 : (R₁ - ε n + (R₂ - ε n)) ≤ mutualInfoOf p W / log 2 := by
        have : n * mutualInfoOf p W / log 2 = (mutualInfoOf p W / log 2) * n := by ring
        rw [this] at key'
        exact le_of_mul_le_mul_right key' hn'
      rw [le_div_iff₀ hL] at h7
      exact h7
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_rate_eps hc hP0
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

end Coop

end InfoTheory
