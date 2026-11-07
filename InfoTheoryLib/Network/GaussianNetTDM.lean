/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.GaussianNetCode
public import InfoTheoryLib.Network.RelayRates

/-!
# Gaussian networks without relaying: time division

Each sender transmits for a fraction `1 / T` of the time, with power `T P`, and the other senders
are silent. This gives a rate `(1 / T) C(g² T P)` to each sender, and the symmetric capacity of the
`N`-sender AWGN MAC.

## Main definitions

* `gnSlot`: the times at which a sender transmits.
* `gnTdmCode`: the time division code.
* `gnSymCapacity`: the symmetric capacity.

## Main statements

* `exists_single_code`: codes for the AWGN channel with small maximal error.
* `isAchievableGN_tdm`: **time division achieves `(1 / T) C(g² T P)`**.
* `gnSymCapacity_mac`: **the symmetric capacity of the `N`-sender AWGN MAC, page 20-10**.
* `isAchievableGN_ic`, `IsAchievableGN.ic_le_rate`, `IsAchievableGN.ic_le_single`: **the bounds of
  the interference example, pages 20-12 and 20-13**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 20
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Codes with small maximal error -/

section Single

/-- Removing the worse half of the codewords, and then some more. -/
lemma GaussianCode.exists_max_le {K M M' n : ℕ} [NeZero M] (hK : K = 2 * M') (hM : M ≤ M')
    (N : ℝ≥0) (c : GaussianCode K n) {P : ℝ} (hc : c.SatisfiesPower P) :
    ∃ c' : GaussianCode M n, c'.SatisfiesPower P ∧ c'.maxErrProb N ≤ 2 * c.avgErrProb N := by
  subst hK
  have hM₀ := NeZero.pos M
  have hM'₀ : 0 < M' := by omega
  obtain ⟨c₁, hp₁, hm₁⟩ := GaussianCode.exists_maxErrProb_le_two_mul N hM'₀ c hc
  refine ⟨c₁.reindex (Fin.castLEEmb hM), GaussianCode.SatisfiesPower.reindex c₁ hp₁ _, le_trans ?_
    hm₁⟩
  refine GaussianCode.maxErrProb_le _ _ hM₀ fun w => ?_
  exact (c₁.condErrProb_reindex_le N _ w).trans (c₁.condErrProb_le_maxErrProb N _)

/-- **Codes for the AWGN channel with small maximal error.** For a gain `g ≠ 0` and a rate below the
capacity, all large block lengths have codes of all sizes `M` with `2 M ≤ 2 ^ ⌈m R⌉`, with maximal
probability of error at most `ε`. -/
theorem exists_single_code {g : ℝ} (hg : g ≠ 0) {P : ℝ≥0} {R : ℝ}
    (hR : R < gaussianCapacityFun (g ^ 2 * P) / log 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ M : ℕ, 0 < M → 2 * M ≤ 2 ^ ⌈(m : ℝ) * R⌉₊ →
      ∃ c : GaussianCode M m, c.SatisfiesPower P ∧
        ∀ w, (noiseLaw 1 m).real {z | c.dec (g • c.enc w + z) ≠ w} ≤ ε := by
  obtain ⟨c, hpow, hlim⟩ := isAchievableAWGNRate_of_lt hg hR
  filter_upwards [(tendsto_order.1 hlim).2 (ε / 2) (by positivity)] with m hm M hM hle
  have : NeZero M := ⟨hM.ne'⟩
  -- the number of messages is a power of two
  set a := ⌈(m : ℝ) * R⌉₊ with ha
  have ha1 : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    rw [this, pow_zero] at hle
    omega
  have hK : 2 ^ a = 2 * 2 ^ (a - 1) := by
    obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [hb, Nat.add_sub_cancel, pow_succ, mul_comm]
  have hM' : M ≤ 2 ^ (a - 1) := by
    rw [hK] at hle
    omega
  have hs : ((c m).scale g).SatisfiesPower (g ^ 2 * P) := (hpow m).scale g
  obtain ⟨c₁, hp₁, hm₁⟩ := GaussianCode.exists_max_le hK hM' 1 ((c m).scale g) hs
  refine ⟨c₁.scale g⁻¹, ?_, fun w => ?_⟩
  · have := hp₁.scale g⁻¹
    have e : g⁻¹ ^ 2 * (g ^ 2 * (P : ℝ)) = P := by
      field_simp
    rwa [e] at this
  · have e : g • (c₁.scale g⁻¹).enc w = c₁.enc w := by
      funext i
      simp [GaussianCode.scale, hg]
    rw [e]
    have h₁ := c₁.condErrProb_le_maxErrProb 1 w
    have h₂ : (noiseLaw 1 m).real {z | (c₁.scale g⁻¹).dec (c₁.enc w + z) ≠ w} =
        c₁.condErrProb 1 w := rfl
    rw [h₂]
    linarith

end Single

/-! ### The slots -/

section Slots

variable {t : Type*} [Fintype t] [DecidableEq t] {n m : ℕ}

/-- The times at which sender `j` transmits. -/
def gnSlot (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) (j : t) (i : Fin m) : Fin
    n :=
  Fin.castLE hm (finProdFinEquiv (e j, i))

omit [DecidableEq t] in
lemma gnSlot_inj (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) {j l : t}
    {i i' : Fin m} (h : gnSlot e hm j i = gnSlot e hm l i') : j = l ∧ i = i' := by
  have h₁ := finProdFinEquiv.injective (Fin.castLE_injective hm h)
  simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h₁
  exact h₁

omit [DecidableEq t] in
lemma gnSlot_injective (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) (j : t) :
    Function.Injective (gnSlot e hm j) := fun _ _ h => (gnSlot_inj e hm h).2

/-- A sequence on the slots of a sender, and `0` at the other times. -/
def gnExtend (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) (j : t)
    (x : Fin m → ℝ) : Fin n → ℝ :=
  Function.extend (gnSlot e hm j) x 0

omit [DecidableEq t] in
lemma gnExtend_slot (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) (j : t)
    (x : Fin m → ℝ) (i : Fin m) : gnExtend e hm j x (gnSlot e hm j i) = x i :=
  (gnSlot_injective e hm j).extend_apply x 0 i

omit [DecidableEq t] in
lemma gnExtend_slot_ne (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) {j l : t}
    (hjl : j ≠ l) (x : Fin m → ℝ) (i : Fin m) : gnExtend e hm j x (gnSlot e hm l i) = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨i', hi'⟩
  exact hjl (gnSlot_inj e hm hi').1

omit [DecidableEq t] in
/-- The power of a sequence on the slots of a sender. -/
lemma sum_gnExtend_sq (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) (j : t)
    (x : Fin m → ℝ) : ∑ i, gnExtend e hm j x i ^ 2 = ∑ i, x i ^ 2 := by
  classical
  have h₁ : ∑ i ∈ univ.image (gnSlot e hm j), gnExtend e hm j x i ^ 2 = ∑ i, x i ^ 2 := by
    rw [sum_image fun a _ b _ h => gnSlot_injective e hm j h]
    exact sum_congr rfl fun i _ => by rw [gnExtend_slot]
  rw [← h₁]
  refine (sum_subset (subset_univ _) fun i _ hi => ?_).symm
  have : gnExtend e hm j x i = 0 := by
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨a, ha⟩
    exact hi (ha ▸ mem_image_of_mem _ (mem_univ a))
  rw [this]
  norm_num

end Slots

/-! ### The code -/

section TDM

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t] {M : t → ℕ} {n m : ℕ}

/-- **Page 20-12 of [elgamal2010].** The time division code: sender `j` uses the code `cs j` in its
slots. The destination of sender `j` is the receiver `dest j`. -/
def gnTdmCode (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) (dest : t → r)
    (hM : ∀ j, 0 < M j) (cs : ∀ j, GaussianCode (M j) m) : GNCode M n r where
  enc j a := gnExtend e hm j ((cs j).enc a)
  dec k y j := if dest j = k then (cs j).dec fun i => y (gnSlot e hm j i) else ⟨0, hM j⟩
  measurable_dec k := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases h : dest j = k
    · simp only [h, ite_true]
      exact (cs j).measurable_dec.comp (measurable_pi_iff.mpr fun i => measurable_pi_apply _)
    · simp only [h, ite_false]
      exact measurable_const

variable (G : Matrix r t ℝ)

omit [Fintype r] [DecidableEq t] in
/-- In the slot of sender `j`, the output is the output of the channel from sender `j`. -/
lemma gnTdm_out (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n) (dest : t → r)
    (hM : ∀ j, 0 < M j) (cs : ∀ j, GaussianCode (M j) m) (a : ∀ j, Fin (M j)) (j : t) (i : Fin m)
    (k : r) :
    (gnTdmCode e hm dest hM cs).out G a (gnSlot e hm j i) k = G k j * (cs j).enc (a j) i := by
  simp only [GNCode.out, gnTdmCode]
  rw [sum_eq_single j]
  · rw [gnExtend_slot]
  · intro l _ hl
    rw [gnExtend_slot_ne e hm hl, mul_zero]
  · simp

/-- **The error of the time division code** is at most the sum of the errors of the codes. -/
theorem gnTdm_errProb_le (e : t ≃ Fin (Fintype.card t)) (hm : Fintype.card t * m ≤ n)
    (dest : t → r) (hM : ∀ j, 0 < M j) (cs : ∀ j, GaussianCode (M j) m) {ε : ℝ}
    (hε : ∀ j w, (noiseLaw 1 m).real
      {z | (cs j).dec (G (dest j) j • (cs j).enc w + z) ≠ w} ≤ ε) :
    (gnTdmCode e hm dest hM cs).errProb G (fun j => {dest j}) ≤ Fintype.card t * ε := by
  classical
  set c := gnTdmCode e hm dest hM cs with hc
  have : Nonempty (∀ j, Fin (M j)) := ⟨fun j => ⟨0, hM j⟩⟩
  have hpos : (0 : ℝ) < Fintype.card (∀ j, Fin (M j)) := by exact_mod_cast Fintype.card_pos
  have hone : ∀ a : ∀ j, Fin (M j), (stdNoise (Fin n × r)).real (c.errSet G (fun j => {dest j}) a) ≤
      Fintype.card t * ε := by
    intro a
    let f : ∀ j, Fin m → Fin n × r := fun j i => (gnSlot e hm j i, dest j)
    have hf : ∀ j, Function.Injective (f j) := fun j a b h => by
      simp only [f, Prod.mk.injEq] at h
      exact gnSlot_injective e hm j h.1
    let S : t → Set (Fin n × r → ℝ) := fun j => (fun (z : Fin n × r → ℝ) (i : Fin m) => z (f j i))
      ⁻¹'
      {z | (cs j).dec (G (dest j) j • (cs j).enc (a j) + z) ≠ a j}
    have hsub : c.errSet G (fun j => {dest j}) a ⊆ ⋃ j ∈ (univ : Finset t), S j := by
      rintro z ⟨j, k, hk, hne⟩
      have hk' : k = dest j := mem_singleton.mp hk
      subst hk'
      refine Set.mem_biUnion (mem_coe.mpr (mem_univ j)) ?_
      simp only [S, Set.mem_preimage, Set.mem_ofPred_eq]
      intro he
      apply hne
      have hd : c.dec (dest j) (fun i => c.out G a i (dest j) + z (i, dest j)) j =
          (cs j).dec fun i => c.out G a (gnSlot e hm j i) (dest j) +
            z (gnSlot e hm j i, dest j) := by
        simp only [hc, gnTdmCode, ite_true]
      rw [hd, ← he]
      congr 1
      funext i
      rw [hc, gnTdm_out]
      rfl
    have hreal : ∀ j, (stdNoise (Fin n × r)).real (S j) ≤ ε := by
      intro j
      have hmap := map_stdNoise_comp_injective (hf j)
      have hρ : Measurable fun (z : Fin n × r → ℝ) (b : Fin m) => z (f j b) :=
        measurable_pi_iff.mpr fun b => measurable_pi_apply (f j b)
      have hE : MeasurableSet {z : Fin m → ℝ | (cs j).dec (G (dest j) j • (cs j).enc (a j) + z) ≠
          a j} := by
        have hm' : Measurable fun z : Fin m → ℝ =>
          (cs j).dec (G (dest j) j • (cs j).enc (a j) + z) :=
          (cs j).measurable_dec.comp (measurable_const.add measurable_id)
        exact hm' (measurableSet_singleton _).compl
      have h₁ := map_measureReal_apply (μ := stdNoise (Fin n × r)) hρ hE
      rw [hmap] at h₁
      simp only [S]
      rw [← h₁]
      exact hε j (a j)
    calc _ ≤ (stdNoise (Fin n × r)).real (⋃ j ∈ (univ : Finset t), S j) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ j, (stdNoise (Fin n × r)).real (S j) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _j : t, ε := sum_le_sum fun j _ => hreal j
      _ = _ := by simp
  rw [GNCode.errProb, div_le_iff₀ hpos]
  calc _ ≤ ∑ _a : ∀ j, Fin (M j), (Fintype.card t * ε) := sum_le_sum fun a _ => hone a
    _ = _ := by
      simp
      ring

/-- The symmetric capacity, in bits. -/
def gnSymCapacity (G : Matrix r t ℝ) (D : t → Finset r) (P : ℝ≥0) : ℝ :=
  sSup {R : ℝ | IsAchievableGN G D P fun _ => R}

omit [DecidableEq r] in
/-- **Page 20-12 of [elgamal2010]: time division.** With `T` senders, each sender `j` can send at a
rate `R_j < (1 / T) C(g² T P)`, where `g` is the gain to its destination. -/
theorem isAchievableGN_tdm [Nonempty t] {dest : t → r} (hg : ∀ j, G (dest j) j ≠ 0) {P : ℝ≥0}
    (hP : 0 < P) {R : t → ℝ}
    (hR : ∀ j, (Fintype.card t : ℝ) * R j * log 2 <
      gaussianCapacityFun (G (dest j) j ^ 2 * (Fintype.card t * (P : ℝ)))) :
    IsAchievableGN G (fun j => {dest j}) P R := by
  classical
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  set T := Fintype.card t with hT
  have hT0 : 0 < T := Fintype.card_pos
  have hT0' : (0 : ℝ) < T := by exact_mod_cast hT0
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  set e := Fintype.equivFin t with he
  set P₁ : ℝ≥0 := (T : ℝ≥0) * P with hP₁
  have hP₁c : (P₁ : ℝ) = T * P := by simp [hP₁]
  -- the rates of the codes
  have hex : ∀ j, ∃ R' : ℝ, (T : ℝ) * max (R j) 0 < R' ∧
      R' < gaussianCapacityFun (G (dest j) j ^ 2 * P₁) / log 2 := by
    intro j
    rw [hP₁c]
    have hcap0 : 0 < gaussianCapacityFun (G (dest j) j ^ 2 * (T * (P : ℝ))) := by
      have hg2 : 0 < G (dest j) j ^ 2 := by
        have := hg j
        positivity
      simp only [gaussianCapacityFun]
      have : 0 < log (1 + G (dest j) j ^ 2 * (T * (P : ℝ))) :=
        log_pos (by
          have : 0 < G (dest j) j ^ 2 * (T * (P : ℝ)) := by positivity
          linarith)
      positivity
    refine exists_between ?_
    rw [lt_div_iff₀ hlog]
    rcases le_total (R j) 0 with h | h
    · rw [max_eq_right h]
      simpa using hcap0
    · rw [max_eq_left h]
      exact hR j
  choose R' hR'₁ hR'₂ using hex
  have hsmall : ∀ η > 0, ∀ᶠ n : ℕ in atTop,
      ∃ c : {c : GNCode (fun j => 2 ^ ⌈(n : ℝ) * R j⌉₊) n r // c.SatisfiesPower P},
        c.1.errProb G (fun j => {dest j}) ≤ η := by
    intro η hη
    have hε : 0 < η / T := by positivity
    have hcodes : ∀ᶠ m : ℕ in atTop, ∀ j, ∀ M : ℕ, 0 < M → 2 * M ≤ 2 ^ ⌈(m : ℝ) * R' j⌉₊ →
        ∃ c : GaussianCode M m, c.SatisfiesPower P₁ ∧
          ∀ w, (noiseLaw 1 m).real {z | c.dec (G (dest j) j • c.enc w + z) ≠ w} ≤ η / T :=
      eventually_all.mpr fun j => exists_single_code (hg j) (hR'₂ j) hε
    have hsize : ∀ᶠ m : ℕ in atTop, ∀ j, (T : ℝ) * ((m : ℝ) + 1) * max (R j) 0 + 2 ≤ m * R' j := by
      refine eventually_all.mpr fun j => ?_
      have hd : 0 < R' j - T * max (R j) 0 := sub_pos.mpr (hR'₁ j)
      filter_upwards [eventually_ge_atTop ⌈(T * max (R j) 0 + 2) / (R' j - T * max (R j) 0)⌉₊]
        with m hm
      have h₁ := Nat.ceil_le.mp hm
      rw [div_le_iff₀ hd] at h₁
      nlinarith
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hcodes.and hsize)
    refine eventually_atTop.mpr ⟨T * m₀, fun n hn => ?_⟩
    set m := n / T with hmd
    have hmge : m₀ ≤ m := by
      rw [hmd, Nat.le_div_iff_mul_le hT0, mul_comm]
      exact hn
    obtain ⟨hc, hs⟩ := hm₀ m hmge
    have hTm : T * m ≤ n := Nat.mul_div_le n T
    have hnlt : (n : ℝ) < T * ((m : ℝ) + 1) := by
      have : n < T * (m + 1) := Nat.lt_mul_div_succ n hT0
      exact_mod_cast this
    have hMpos : ∀ (j : t), 0 < 2 ^ ⌈(n : ℝ) * R j⌉₊ := fun j => by positivity
    -- the sizes of the codes
    have hfit : ∀ j, 2 * 2 ^ ⌈(n : ℝ) * R j⌉₊ ≤ 2 ^ ⌈(m : ℝ) * R' j⌉₊ := by
      intro j
      rw [← pow_succ']
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have hmax : 0 ≤ max (R j) 0 := le_max_right _ _
      have h₁ : (n : ℝ) * R j ≤ T * ((m : ℝ) + 1) * max (R j) 0 :=
        calc (n : ℝ) * R j ≤ n * max (R j) 0 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg n)
          _ ≤ _ := mul_le_mul_of_nonneg_right hnlt.le hmax
      have h₂ : (⌈(n : ℝ) * R j⌉₊ : ℝ) < T * ((m : ℝ) + 1) * max (R j) 0 + 1 := by
        have h₃ : ⌈(n : ℝ) * R j⌉₊ ≤ ⌈(T : ℝ) * ((m : ℝ) + 1) * max (R j) 0⌉₊ := Nat.ceil_mono h₁
        have h₄ := Nat.ceil_lt_add_one (a := (T : ℝ) * ((m : ℝ) + 1) * max (R j) 0) (by positivity)
        have h₅ : (⌈(n : ℝ) * R j⌉₊ : ℝ) ≤ ⌈(T : ℝ) * ((m : ℝ) + 1) * max (R j) 0⌉₊ := by
          exact_mod_cast h₃
        linarith
      have h₃ : ((⌈(n : ℝ) * R j⌉₊ + 1 : ℕ) : ℝ) ≤ (⌈(m : ℝ) * R' j⌉₊ : ℝ) := by
        push_cast
        have := hs j
        have h₄ := Nat.le_ceil ((m : ℝ) * R' j)
        linarith
      exact_mod_cast h₃
    have hcs : ∀ j, ∃ c : GaussianCode (2 ^ ⌈(n : ℝ) * R j⌉₊) m, c.SatisfiesPower P₁ ∧
        ∀ w, (noiseLaw 1 m).real {z | c.dec (G (dest j) j • c.enc w + z) ≠ w} ≤ η / T :=
      fun j => hc j _ (hMpos j) (hfit j)
    choose cs hpow herr using hcs
    refine ⟨⟨gnTdmCode e hTm dest hMpos cs, fun j => ?_⟩, ?_⟩
    · -- the power
      simp only [gnTdmCode]
      simp_rw [sum_gnExtend_sq]
      calc _ ≤ ∑ _a : Fin (2 ^ ⌈(n : ℝ) * R j⌉₊), ((n : ℝ) * P) := by
            refine sum_le_sum fun a _ => (hpow j a).trans ?_
            rw [hP₁c]
            have : (T : ℝ) * m ≤ n := by exact_mod_cast hTm
            nlinarith
        _ = _ := by simp
    · refine (gnTdm_errProb_le G e hTm dest hMpos cs herr).trans (le_of_eq ?_)
      rw [← hT]
      field_simp
  have hdef : ∀ n : ℕ, Nonempty {c : GNCode (fun j => 2 ^ ⌈(n : ℝ) * R j⌉₊) n r //
      c.SatisfiesPower P} := fun n =>
    ⟨⟨⟨fun _ _ _ => 0, fun _ _ j => ⟨0, by positivity⟩, fun _ => measurable_const⟩, fun j => by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
      positivity⟩⟩
  obtain ⟨c, hc⟩ := exists_seq_tendsto
    (C := fun n : ℕ => {c : GNCode (fun j => 2 ^ ⌈(n : ℝ) * R j⌉₊) n r // c.SatisfiesPower P})
    (fun n c => c.1.errProb G fun j => {dest j})
    (fun n c => div_nonneg (sum_nonneg fun _ _ => measureReal_nonneg) (Nat.cast_nonneg _)) hsmall
  exact ⟨fun n => (c n).1, fun n => (c n).2, hc⟩

end TDM

/-! ### The `N`-sender MAC and the interference example -/

section Examples

variable {N : ℕ}

/-- The determinant over the type of the elements of `univ`. -/
lemma gvRate_submatrix_univ {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
    (G : Matrix r t ℝ) (P : ℝ) :
    gvRate (G.submatrix (Subtype.val : ↥(univ : Finset r) → r)
      (Subtype.val : ↥(univ : Finset t) → t)) (P • 1) = gvRate G (P • 1) := by
  simp only [gvRate]
  congr 2
  let er : ↥(univ : Finset r) ≃ r := Equiv.subtypeUnivEquiv fun _ => mem_univ _
  have e : G.submatrix (Subtype.val : ↥(univ : Finset r) → r)
        (Subtype.val : ↥(univ : Finset t) → t) *
      (P • (1 : Matrix ↥(univ : Finset t) ↥(univ : Finset t) ℝ)) *
      (G.submatrix (Subtype.val : ↥(univ : Finset r) → r)
        (Subtype.val : ↥(univ : Finset t) → t))ᵀ + 1 =
      (G * (P • (1 : Matrix t t ℝ)) * Gᵀ + 1).submatrix er er := by
    ext a b
    have hsum : ∀ F : t → ℝ, ∑ x : ↥(univ : Finset t), F x = ∑ x, F x := fun F =>
      Finset.sum_coe_sort univ F
    simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.smul_apply, Matrix.mul_apply, transpose_apply]
    rw [hsum fun x => G a x * G b x]
    by_cases h : a = b
    · subst h
      simp [er]
    · have h' : (a : r) ≠ b := fun e => h (Subtype.ext e)
      simp [er, h, h']
  rw [e, det_submatrix_equiv_self]

/-- **Page 20-10 of [elgamal2010].** The channel of the `N`-sender AWGN MAC. -/
def macGain (N : ℕ) : Matrix Unit (Fin N) ℝ := Matrix.of fun _ _ => 1

/-- `½ log |1 + N P|` for the `N`-sender AWGN MAC. -/
lemma gvRate_macGain (P : ℝ) : gvRate (macGain N) (P • 1) = gaussCap (N * P) := by
  simp only [gvRate, gaussCap]
  congr 2
  rw [det_unique]
  simp [macGain, Matrix.mul_apply, add_comm]

/-- **Page 20-10 of [elgamal2010]: the symmetric capacity of the `N`-sender AWGN MAC** is
`C(N) = (1 / N) C(N P)`. It is achieved by time division. -/
theorem gnSymCapacity_mac (hN : 0 < N) {P : ℝ≥0} (hP : 0 < P) :
    gnSymCapacity (macGain N) (fun _ => {()}) P * log 2 = gaussCap (N * P) / N := by
  classical
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hcap0 : 0 ≤ gaussCap (N * P) := by
    simp only [gaussCap]
    have : 0 ≤ log (1 + (N : ℝ) * P) := log_nonneg (by
      have : 0 ≤ (N : ℝ) * P := by positivity
      linarith)
    positivity
  have hup : ∀ R : ℝ, IsAchievableGN (macGain N) (fun _ => {()}) P (fun _ => R) →
      R * log 2 ≤ gaussCap (N * P) / N := by
    intro R hR
    have h := hR.sum_le univ univ fun j _ => ⟨(), mem_univ _, mem_singleton_self _⟩
    rw [gvRate_submatrix_univ, gvRate_macGain, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    rw [le_div_iff₀ hN']
    linarith
  have hlow : ∀ R : ℝ, R * log 2 < gaussCap (N * P) / N →
      IsAchievableGN (macGain N) (fun _ => {()}) P (fun _ => R) := by
    intro R hR
    refine isAchievableGN_tdm (macGain N) (dest := fun _ => ()) (fun j => by simp [macGain]) hP
      fun j => ?_
    rw [lt_div_iff₀ hN'] at hR
    simp only [Fintype.card_fin, macGain, Matrix.of_apply, one_pow, one_mul]
    simp only [gaussCap] at hR
    simp only [gaussianCapacityFun]
    nlinarith
  have hbdd : BddAbove {R : ℝ | IsAchievableGN (macGain N) (fun _ => {()}) P fun _ => R} :=
    ⟨gaussCap (N * P) / N / log 2, fun R hR => by
      rw [le_div_iff₀ hlog]
      exact hup R hR⟩
  have hC0 : 0 ≤ gnSymCapacity (macGain N) (fun _ => {()}) P := by
    refine le_csSup hbdd (hlow 0 ?_)
    rw [zero_mul]
    have : 0 < gaussCap (N * P) := by
      simp only [gaussCap]
      have : 0 < log (1 + (N : ℝ) * P) := log_pos (by
        have : 0 < (N : ℝ) * P := by positivity
        linarith)
      positivity
    positivity
  refine le_antisymm ?_ ?_
  · rw [← le_div_iff₀ hlog]
    refine Real.sSup_le (fun R hR => ?_) (by positivity)
    rw [le_div_iff₀ hlog]
    exact hup R hR
  · rw [← div_le_iff₀ hlog]
    refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
    exact le_csSup hbdd (hlow R ((lt_div_iff₀ hlog).mp hR))

variable {a : ℝ} {P : ℝ≥0}

/-- Receiver `j` is the destination of sender `j`. -/
abbrev icDest (N : ℕ) : Fin N → Finset (Fin N) := fun j => {j}

/-- **Page 20-12 of [elgamal2010].** In the interference example, time division achieves a symmetric
rate of `(1 / N) C(N P)`. -/
theorem isAchievableGN_ic (hN : 0 < N) (hP : 0 < P) {R : ℝ}
    (hR : R * log 2 < gaussCap (N * P) / N) :
    IsAchievableGN (icGain N a) (icDest N) P fun _ => R := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine isAchievableGN_tdm (icGain N a) (dest := id) (fun j => by simp [icGain]) hP fun j => ?_
  rw [lt_div_iff₀ hN'] at hR
  simp only [Fintype.card_fin, icGain, id, Matrix.of_apply, ite_true, one_pow, one_mul]
  simp only [gaussCap] at hR
  simp only [gaussianCapacityFun]
  nlinarith

/-- **Page 20-12 of [elgamal2010].** In the interference example, a symmetric rate is at most
`C(P)`: for any `a`, `C(N) = O(1)`. -/
theorem IsAchievableGN.ic_le_single (hN : 0 < N) {R : ℝ}
    (h : IsAchievableGN (icGain N a) (icDest N) P fun _ => R) : R * log 2 ≤ gaussCap P := by
  classical
  let j : Fin N := ⟨0, hN⟩
  have hb := h.sum_le {j} {j} fun l hl => ⟨j, mem_singleton_self j, by
    rw [mem_singleton.mp hl]
    exact mem_singleton_self j⟩
  have e : gvRate ((icGain N a).submatrix (Subtype.val : ({j} : Finset (Fin N)) → Fin N)
      (Subtype.val : ({j} : Finset (Fin N)) → Fin N)) ((P : ℝ) • 1) = gaussCap P := by
    simp only [gvRate, gaussCap]
    congr 2
    rw [det_unique]
    have hd : (default : ({j} : Finset (Fin N))) = ⟨j, mem_singleton_self j⟩ := Subsingleton.elim _
      _
    simp [Matrix.mul_apply, icGain, add_comm, hd]
  rw [e] at hb
  simpa using hb

/-- **Page 20-12 of [elgamal2010].** In the interference example, a symmetric rate is at most
`(1 / 2N) log |I + G Gᵀ P|`. -/
theorem IsAchievableGN.ic_le_rate (hN : 0 < N) {R : ℝ}
    (h : IsAchievableGN (icGain N a) (icDest N) P fun _ => R) :
    R * log 2 ≤ gvRate (icGain N a) ((P : ℝ) • 1) / N := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := h.sum_le univ univ fun l _ => ⟨l, mem_univ _, mem_singleton_self l⟩
  rw [gvRate_submatrix_univ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  rw [le_div_iff₀ hN']
  linarith

end Examples

end InfoTheory
