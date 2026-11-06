/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DistFun
public import InfoTheoryLib.Network.MACBits
public import InfoTheoryLib.Network.MACBounds

/-!
# Computing over a multiple access channel

This file proves the example of Nazer and Gastpar in Lecture 22 of [elgamal2010]: two independent
uniform binary sources are to be added over a modulo-2 sum channel with additive noise. The optimal
computing rate is `1 - H(N)`, by linear codes, while separate source–channel coding only achieves
`(1 - H(N)) / 2`. So separation is suboptimal for computing, even for independent sources.

## Main definitions

* `ComputeCode`, `ComputeCode.errProb`, `IsComputable`: the codes, and the computable rates.
* `macSumChannel`: the channel `Y = X₁ ⊕ X₂ ⊕ N`.

## Main statements

* `isComputable_of_lt`, `IsComputable.le`: **the computing capacity** is `1 - H(N)` bits.
* `mem_macCapacityRegionBits_diag_iff`: separation achieves a rate `r` iff `2 r ≤ 1 - H(N)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {k n : ℕ} {ν : ZMod 2 → ℝ}

/-- **Lecture 22 of [elgamal2010], page 22-33.** A code for computing `U₁ᵏ ⊕ U₂ᵏ` with `n` uses of
the channel. -/
structure ComputeCode (k n : ℕ) where
  /-- The first encoder. -/
  enc₁ : (Fin k → ZMod 2) → Fin n → ZMod 2
  /-- The second encoder. -/
  enc₂ : (Fin k → ZMod 2) → Fin n → ZMod 2
  /-- The decoder. -/
  dec : (Fin n → ZMod 2) → Fin k → ZMod 2

/-- The law of `Yⁿ = X₁ⁿ ⊕ X₂ⁿ ⊕ Nⁿ` given the sources, with an i.i.d. noise of law `ν`. -/
def ComputeCode.kernel (c : ComputeCode k n) (ν : ZMod 2 → ℝ)
    (u : (Fin k → ZMod 2) × (Fin k → ZMod 2)) (y : Fin n → ZMod 2) : ℝ :=
  iidPMF ν n (y - (c.enc₁ u.1 + c.enc₂ u.2))

/-- **Lecture 22 of [elgamal2010], page 22-33.** The probability of error `P{Ẑᵏ ≠ U₁ᵏ ⊕ U₂ᵏ}`, for
uniform independent sources. -/
def ComputeCode.errProb (c : ComputeCode k n) (ν : ZMod 2 → ℝ) : ℝ :=
  ∑ z, jointOf (uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2))) (c.kernel ν) z *
    if c.dec z.2 ≠ z.1.1 + z.1.2 then 1 else 0

/-- **Lecture 22 of [elgamal2010], page 22-33.** A rate `r = k / n` is computable if there are codes
with `k = ⌊n r⌋` and a vanishing probability of error. -/
def IsComputable (ν : ZMod 2 → ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ c : ∀ n : ℕ, ComputeCode ⌊n * r⌋₊ n, Tendsto (fun n => (c n).errProb ν) atTop (𝓝 0)

lemma ComputeCode.kernel_isChannel (c : ComputeCode k n) (hν : IsPMF ν) : IsChannel (c.kernel ν) :=
  fun u => ⟨fun y => iidPMF_nonneg hν.nonneg _, by
    rw [← (iidPMF_isPMF hν n).sum_eq_one]
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl⟩

lemma ComputeCode.entropy_kernel (c : ComputeCode k n) (hν : IsPMF ν)
    (u : (Fin k → ZMod 2) × (Fin k → ZMod 2)) :
    entropy (c.kernel ν u) = n * entropy ν := by
  rw [← entropy_iidPMF hν n, entropy, entropy]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl

/-! ### The converse -/

section Converse

/-- **Lecture 22, page 22-34.** The cutset bound at the input of the noise, with Fano's inequality:
`k log 2 ≤ n (log 2 - H(N)) + log 2 + P_e k log 2`. -/
theorem ComputeCode.fano (c : ComputeCode k n) (hν : IsPMF ν) :
    k * log 2 ≤ n * (log 2 - entropy ν) + log 2 + c.errProb ν * (k * log 2) := by
  classical
  have hU : IsPMF (uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2))) := uniformPMF_isPMF
  have hK := c.kernel_isChannel hν
  have hμ := jointOf_isPMF hU hK
  set μ := jointOf (uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2))) (c.kernel ν) with hμd
  set Z : ((Fin k → ZMod 2) × (Fin k → ZMod 2)) × (Fin n → ZMod 2) → Fin k → ZMod 2 :=
    fun z => z.1.1 + z.1.2 with hZ
  -- `Z` is uniform.
  have hZu : H[Z ; μ] = k * log 2 := by
    have hd : dist μ Z = uniformPMF (Fin k → ZMod 2) := by
      rw [show Z = (fun w : (Fin k → ZMod 2) × (Fin k → ZMod 2) => w.1 + w.2) ∘ Prod.fst from rfl,
        dist_comp_eq, dist_jointOf_fst hK]
      funext a
      have hin : ∀ u₁ : Fin k → ZMod 2, ∑ u₂ : Fin k → ZMod 2, (if u₁ + u₂ = a then
          uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2)) (u₁, u₂) else 0) =
          uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2)) (u₁, a - u₁) := fun u₁ => by
        rw [sum_eq_single (a - u₁)]
        · simp
        · intro u₂ _ hu
          rw [ite_eq_right]
          intro h
          exact absurd (eq_sub_of_add_eq' h) hu
        · simp
      rw [dist, Fintype.sum_prod_type]
      refine (sum_congr rfl fun u₁ _ => by convert hin u₁).trans ?_
      simp only [uniformPMF, sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
      have hc : ((Fintype.card (Fin k → ZMod 2) : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp
    rw [entropyRV, hd, entropy_uniformPMF]
    simp [ZMod.card, Nat.cast_pow]
  have hcard : log (Fintype.card (Fin k → ZMod 2)) = k * log 2 := by
    simp [ZMod.card, Nat.cast_pow]
  -- Fano.
  have hF := condEntropy_le_estErrProb hμ Z (fun z => c.dec z.2) (ι := id) Function.injective_id
  have hb : binEntropy (estErrProb μ Z (fun z => c.dec z.2) id) ≤ log 2 := binEntropy_le_log_two
  have herr : estErrProb μ Z (fun z => c.dec z.2) id = c.errProb ν := by
    simp only [estErrProb, ComputeCode.errProb, mul_ite, mul_one, mul_zero]
    refine sum_congr rfl fun x _ => ?_
    by_cases h : c.dec x.2 = x.1.1 + x.1.2 <;> simp [h, hZ, id]
    rfl
  rw [herr, hcard] at hF
  rw [herr] at hb
  have hdec : H[Z | Prod.snd ; μ] ≤ H[Z | fun z => c.dec z.2 ; μ] :=
    condEntropy_le_condEntropy_comp hμ Z Prod.snd c.dec
  -- The information.
  have hI : I[Z : Prod.snd ; μ] ≤ n * (log 2 - entropy ν) := by
    have h₁ : I[Z : Prod.snd ; μ] ≤ I[Prod.fst : Prod.snd ; μ] := by
      have := mutualInfo_comp_le hμ Prod.snd Prod.fst (fun w : (Fin k → ZMod 2) × (Fin k → ZMod 2)
        => w.1 + w.2)
      rw [mutualInfo_comm hμ, mutualInfo_comm hμ Prod.fst]
      exact this
    refine h₁.trans ?_
    have h₂ := mutualInfoOf_eq hU hK
    rw [mutualInfoOf] at h₂
    rw [h₂]
    have h₃ : ∑ x, uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2)) x * entropy (c.kernel ν x) =
        n * entropy ν := by
      simp only [c.entropy_kernel hν, ← sum_mul, hU.sum_eq_one, one_mul]
    rw [h₃]
    have h₄ : entropy (outDist (uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2))) (c.kernel ν)) ≤
        n * log 2 := by
      have := entropy_le_log_card (outDist_isPMF hU hK)
      simpa [ZMod.card, Nat.cast_pow] using this
    linarith
  have hsum := mutualInfo_eq_entropy_sub_condEntropy hμ (X := Z) (Y := Prod.snd)
  linarith

/-- **Lecture 22, page 22-34.** A computable rate is at most `1 - H(N)` bits. -/
theorem IsComputable.le (hν : IsPMF ν) {r : ℝ} (h : IsComputable ν r) :
    r * log 2 ≤ log 2 - entropy ν := by
  obtain ⟨hr, c, hc⟩ := h
  have hl := log_pos one_lt_two
  refine le_of_forall_pos_le_add fun δ' hδ' => ?_
  -- Choose a small error, and then a large length.
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = δ' / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδd]; positivity
  set η := δ / (r * log 2 + 1) with hη
  have hη0 : 0 < η := by positivity
  have hrl : 0 ≤ r * log 2 := mul_nonneg hr hl.le
  obtain ⟨n, hn1, hn2⟩ := ((hc.eventually (gt_mem_nhds hη0)).and (eventually_gt_atTop
    ⌈(2 * log 2 + r * log 2) / δ + 1⌉₊)).exists
  have hn0 : (0 : ℝ) < n := by
    have : (⌈(2 * log 2 + r * log 2) / δ + 1⌉₊ : ℝ) < n := by exact_mod_cast hn2
    have h' : (0 : ℝ) ≤ ⌈(2 * log 2 + r * log 2) / δ + 1⌉₊ := Nat.cast_nonneg _
    linarith
  have hnb : (2 * log 2 + r * log 2) / δ < n := by
    have h₁ := Nat.le_ceil ((2 * log 2 + r * log 2) / δ + 1)
    have h₂ : (⌈(2 * log 2 + r * log 2) / δ + 1⌉₊ : ℝ) < n := by exact_mod_cast hn2
    linarith
  have hF := (c n).fano hν
  set k := ⌊(n : ℝ) * r⌋₊ with hk
  have hk1 : (n : ℝ) * r - 1 ≤ k := by
    have := Nat.lt_floor_add_one ((n : ℝ) * r)
    linarith
  have hk2 : (k : ℝ) ≤ n * r := Nat.floor_le (by positivity)
  have hP0 : 0 ≤ (c n).errProb ν := sum_nonneg fun z _ => by
    refine mul_nonneg ((jointOf_isPMF uniformPMF_isPMF ((c n).kernel_isChannel hν)).nonneg z) ?_
    split_ifs <;> norm_num
  have herr : (c n).errProb ν * ((k : ℝ) * log 2) ≤ η * (n * (r * log 2)) := by
    have h₁ : (k : ℝ) * log 2 ≤ n * (r * log 2) := by
      calc (k : ℝ) * log 2 ≤ (n * r) * log 2 := mul_le_mul_of_nonneg_right hk2 hl.le
        _ = _ := by ring
    exact mul_le_mul hn1.le h₁ (by positivity) hη0.le
  have hηb : η * (r * log 2) ≤ δ := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hηn : η * (n * (r * log 2)) ≤ n * δ := by
    calc η * (n * (r * log 2)) = n * (η * (r * log 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hηb hn0.le
  have hk3 : ((n : ℝ) * r - 1) * log 2 ≤ (k : ℝ) * log 2 := mul_le_mul_of_nonneg_right hk1 hl.le
  have hmain : n * (r * log 2) ≤ n * (log 2 - entropy ν) + n * δ + 2 * log 2 := by nlinarith
  have hsmall : 2 * log 2 ≤ n * δ := by
    have h₁ : (2 * log 2 + r * log 2) ≤ n * δ := by
      rw [div_lt_iff₀ hδ] at hnb
      exact hnb.le
    linarith
  have h₂ : n * (r * log 2) ≤ n * (log 2 - entropy ν + (δ + δ)) := by
    calc _ ≤ _ := hmain
      _ ≤ n * (log 2 - entropy ν) + n * δ + n * δ := by linarith
      _ = _ := by ring
  have h₃ := le_of_mul_le_mul_left h₂ hn0
  linarith

end Converse

/-! ### Achievability -/

section Achievability

/-- **Lecture 22, page 22-34.** The linear code of a matrix `B`: both encoders send `B Uᵏ`, and the
decoder looks for a sequence `z'` such that `Yⁿ ⊖ B z'` is typical. -/
def linearCompute (B : Fin n → Fin k → ZMod 2) (T : Finset (Fin n → ZMod 2)) : ComputeCode k n where
  enc₁ := binMul B
  enc₂ := binMul B
  dec y :=
    open Classical in
    if h : ∃ z', y - binMul B z' ∈ T then h.choose else 0

/-- The events of an error of a linear code, for `Z = z` and the noise `N`. -/
def computeBad (B : Fin n → Fin k → ZMod 2) (T : Finset (Fin n → ZMod 2)) (z : Fin k → ZMod 2)
    (N : Fin n → ZMod 2) : ℝ :=
  (if N ∈ T then 0 else 1) +
    ∑ z' : Fin k → ZMod 2, ∑ t ∈ T, if z' ≠ z ∧ binMul B (z - z') = t - N then (1 : ℝ) else 0

lemma computeBad_nonneg (B : Fin n → Fin k → ZMod 2) (T : Finset (Fin n → ZMod 2))
    (z : Fin k → ZMod 2) (N : Fin n → ZMod 2) : 0 ≤ computeBad B T z N := by
  refine add_nonneg (by split_ifs <;> norm_num) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => ?_)
  split_ifs <;> norm_num

/-- The code of a matrix errs only on these events. -/
lemma linearCompute_err_le (B : Fin n → Fin k → ZMod 2) (T : Finset (Fin n → ZMod 2))
    (z : Fin k → ZMod 2) (N : Fin n → ZMod 2) :
    (if (linearCompute B T).dec (N + binMul B z) ≠ z then (1 : ℝ) else 0) ≤
      computeBad B T z N := by
  classical
  by_cases hdec : (linearCompute B T).dec (N + binMul B z) = z
  · simpa [hdec] using computeBad_nonneg B T z N
  simp only [ne_eq, hdec, not_false_eq_true, ite_true]
  by_cases hN : N ∈ T
  · have hex : ∃ z', (N + binMul B z) - binMul B z' ∈ T := ⟨z, by simpa using hN⟩
    have hd : (linearCompute B T).dec (N + binMul B z) = hex.choose := by
      simp only [linearCompute]
      rw [dite_eq_left_of_eq_true (eq_true hex)]
    have hne : hex.choose ≠ z := fun h => hdec (hd.trans h)
    have hmem := hex.choose_spec
    have hrhs : (1 : ℝ) ≤ ∑ z' : Fin k → ZMod 2, ∑ t ∈ T,
        if z' ≠ z ∧ binMul B (z - z') = t - N then (1 : ℝ) else 0 := by
      calc (1 : ℝ) = if hex.choose ≠ z ∧ binMul B (z - hex.choose) =
              ((N + binMul B z) - binMul B hex.choose) - N then (1 : ℝ) else 0 := by
            rw [ite_eq_left]
            refine ⟨hne, ?_⟩
            rw [binMul_sub]
            abel
        _ ≤ ∑ t ∈ T, if hex.choose ≠ z ∧ binMul B (z - hex.choose) = t - N then (1 : ℝ) else 0 :=
            single_le_sum (f := fun t => if hex.choose ≠ z ∧ binMul B (z - hex.choose) = t - N then
              (1 : ℝ) else 0) (fun _ _ => by split_ifs <;> norm_num) hmem
        _ ≤ _ := single_le_sum (f := fun z' : Fin k → ZMod 2 => ∑ t ∈ T,
              if z' ≠ z ∧ binMul B (z - z') = t - N then (1 : ℝ) else 0)
              (fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num) (mem_univ _)
    simp only [computeBad, hN, ite_true, zero_add]
    exact hrhs
  · have h0 : 0 ≤ ∑ z' : Fin k → ZMod 2, ∑ t ∈ T,
        if z' ≠ z ∧ binMul B (z - z') = t - N then (1 : ℝ) else 0 :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num
    simp only [computeBad, hN, ite_false]
    linarith

/-- **Lecture 22, page 22-35.** The fraction of the matrices with an error event of each kind. -/
lemma sum_computeBad_le (T : Finset (Fin n → ZMod 2)) (z : Fin k → ZMod 2) (N : Fin n → ZMod 2) :
    ∑ B : Fin n → Fin k → ZMod 2, computeBad B T z N ≤ (2 : ℝ) ^ (k * n) *
      ((if N ∈ T then 0 else 1) + (2 : ℝ) ^ k * ((T.card : ℝ) / 2 ^ n)) := by
  classical
  have hc : ((Fintype.card (Fin n → Fin k → ZMod 2) : ℕ) : ℝ) = (2 : ℝ) ^ (k * n) := by
    rw [← card_univ]
    exact card_binMatrix
  simp only [computeBad]
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hc, mul_add]
  refine add_le_add le_rfl ?_
  rw [sum_comm]
  have hz' : ∀ z' : Fin k → ZMod 2, ∑ B : Fin n → Fin k → ZMod 2, ∑ t ∈ T,
      (if z' ≠ z ∧ binMul B (z - z') = t - N then (1 : ℝ) else 0) ≤
      (T.card : ℝ) * ((2 : ℝ) ^ (k * n) / 2 ^ n) := fun z' => by
    rw [sum_comm]
    calc _ ≤ ∑ _t ∈ T, (2 : ℝ) ^ (k * n) / 2 ^ n := sum_le_sum fun t _ => ?_
      _ = _ := by rw [sum_const, nsmul_eq_mul]
    by_cases hne : z' = z
    · simp only [hne, ne_eq, not_true_eq_false, false_and, ite_false, sum_const_zero]
      positivity
    · simp only [hne, ne_eq, not_false_eq_true, true_and]
      have hv : z - z' ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      rw [← card_mulVec_eq hv (t - N), sum_boole]
      refine le_of_eq ?_
      congr 2
      ext B
      simp only [mem_filter, mem_univ, true_and]
      exact funext_iff
  calc _ ≤ ∑ _z' : Fin k → ZMod 2, (T.card : ℝ) * ((2 : ℝ) ^ (k * n) / 2 ^ n) :=
        sum_le_sum fun z' _ => hz' z'
    _ = _ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- **Lecture 22, page 22-35.** There is a linear code with an error of at most
`P{Nⁿ ∉ T} + 2^k |T| 2^{-n}`. -/
theorem exists_computeCode_le (hν : IsPMF ν) (T : Finset (Fin n → ZMod 2)) :
    ∃ c : ComputeCode k n, c.errProb ν ≤ (∑ N, iidPMF ν n N * (if N ∈ T then (0 : ℝ) else 1)) +
      (2 : ℝ) ^ k * ((T.card : ℝ) / 2 ^ n) := by
  classical
  set Bd : (Fin k → ZMod 2) × (Fin k → ZMod 2) → (Fin n → ZMod 2) → (Fin n → Fin k → ZMod 2) → ℝ :=
    fun u N B => uniformPMF _ u * iidPMF ν n N * computeBad B T (u.1 + u.2) N with hBd
  have hU : IsPMF (uniformPMF ((Fin k → ZMod 2) × (Fin k → ZMod 2))) := uniformPMF_isPMF
  have hle : ∀ B : Fin n → Fin k → ZMod 2, (linearCompute B T).errProb ν ≤ ∑ u, ∑ N, Bd u N B := by
    intro B
    rw [ComputeCode.errProb, Fintype.sum_prod_type]
    refine sum_le_sum fun u _ => ?_
    have hw : binMul B u.1 + binMul B u.2 = binMul B (u.1 + u.2) := (binMul_add B _ _).symm
    refine le_of_eq_of_le (Fintype.sum_equiv (Equiv.subRight (binMul B (u.1 + u.2)))
      _ (fun N => uniformPMF _ u * iidPMF ν n N *
        if (linearCompute B T).dec (N + binMul B (u.1 + u.2)) ≠ u.1 + u.2 then 1 else 0)
        fun y => ?_) (sum_le_sum fun N _ => ?_)
    · have hk : (linearCompute B T).enc₁ u.1 + (linearCompute B T).enc₂ u.2 =
          binMul B (u.1 + u.2) := hw
      simp only [jointOf, ComputeCode.kernel, hk, Equiv.subRight_apply, sub_add_cancel]
    · exact mul_le_mul_of_nonneg_left (linearCompute_err_le B T _ N)
        (mul_nonneg (hU.nonneg u) (iidPMF_nonneg hν.nonneg N))
  have hsum : ∑ B : Fin n → Fin k → ZMod 2, ∑ u, ∑ N, Bd u N B ≤
      ∑ _B : Fin n → Fin k → ZMod 2, ((∑ N, iidPMF ν n N * (if N ∈ T then (0 : ℝ) else 1)) +
        (2 : ℝ) ^ k * ((T.card : ℝ) / 2 ^ n)) := by
    have hc : ((Fintype.card (Fin n → Fin k → ZMod 2) : ℕ) : ℝ) = (2 : ℝ) ^ (k * n) := by
      rw [← card_univ]
      exact card_binMatrix
    rw [sum_const, card_univ, nsmul_eq_mul, hc, sum_comm]
    have hu : ∀ u, ∑ B : Fin n → Fin k → ZMod 2, ∑ N, Bd u N B ≤ uniformPMF _ u *
        ((2 : ℝ) ^ (k * n) * ((∑ N, iidPMF ν n N * (if N ∈ T then (0 : ℝ) else 1)) +
          (2 : ℝ) ^ k * ((T.card : ℝ) / 2 ^ n))) := fun u => by
      rw [sum_comm]
      have hN : ∀ N, ∑ B : Fin n → Fin k → ZMod 2, Bd u N B ≤ uniformPMF _ u * iidPMF ν n N *
          ((2 : ℝ) ^ (k * n) * ((if N ∈ T then 0 else 1) +
            (2 : ℝ) ^ k * ((T.card : ℝ) / 2 ^ n))) := fun N => by
        simp only [hBd]
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_computeBad_le T _ N)
          (mul_nonneg (hU.nonneg u) (iidPMF_nonneg hν.nonneg N))
      refine (sum_le_sum fun N _ => hN N).trans (le_of_eq ?_)
      have e : ∑ N, iidPMF ν n N * ((if N ∈ T then (0 : ℝ) else 1) +
          (2 : ℝ) ^ k * ((T.card : ℝ) / 2 ^ n)) =
          (∑ N, iidPMF ν n N * (if N ∈ T then (0 : ℝ) else 1)) +
            (2 : ℝ) ^ k * ((T.card : ℝ) / 2 ^ n) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, (iidPMF_isPMF hν n).sum_eq_one, one_mul]
      rw [← e, mul_sum, mul_sum]
      exact sum_congr rfl fun N _ => by ring
    refine (sum_le_sum fun u _ => hu u).trans (le_of_eq ?_)
    rw [← sum_mul, hU.sum_eq_one, one_mul]
  obtain ⟨B, -, hB⟩ := exists_le_of_sum_le (s := univ) univ_nonempty hsum
  exact ⟨linearCompute B T, (hle B).trans hB⟩

/-- **Lecture 22, pages 22-34 and 22-35.** Every rate `r < 1 - H(N)` bits is computable, by linear
codes. -/
theorem isComputable_of_lt (hν : IsPMF ν) {r : ℝ} (h0 : 0 ≤ r)
    (hr : r * log 2 < log 2 - entropy ν) : IsComputable ν r := by
  classical
  have hl := log_pos one_lt_two
  set ε := (log 2 - entropy ν - r * log 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  choose c hc using fun n : ℕ => exists_computeCode_le (k := ⌊(n : ℝ) * r⌋₊) (n := n) hν
    (typicalSet ν n ε)
  refine ⟨h0, c, ?_⟩
  have hnn : ∀ n, 0 ≤ (c n).errProb ν := fun n => sum_nonneg fun z _ => by
    refine mul_nonneg ((jointOf_isPMF uniformPMF_isPMF ((c n).kernel_isChannel hν)).nonneg z) ?_
    split_ifs <;> norm_num
  have ha := tendsto_sum_not_mem_typicalSet hν hε0
  have hb : Tendsto (fun n : ℕ => exp (-(n * ε))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const hε0))
  have hle : ∀ n : ℕ, (2 : ℝ) ^ ⌊(n : ℝ) * r⌋₊ * (((typicalSet ν n ε).card : ℝ) / 2 ^ n) ≤
      exp (-(n * ε)) := fun n => by
    have hcard := card_typicalSet_le hν n ε
    have hk : (⌊(n : ℝ) * r⌋₊ : ℝ) ≤ n * r := Nat.floor_le (by positivity)
    have h2 : (2 : ℝ) ^ ⌊(n : ℝ) * r⌋₊ ≤ exp ((n * r) * log 2) := by
      rw [← rpow_natCast, rpow_def_of_pos (by norm_num), mul_comm]
      exact exp_le_exp.2 (mul_le_mul_of_nonneg_right hk hl.le)
    have h3 : (2 : ℝ) ^ n = exp (n * log 2) := by
      rw [← rpow_natCast, rpow_def_of_pos (by norm_num), mul_comm]
    calc _ ≤ exp ((n * r) * log 2) * (exp (n * (entropy ν + ε)) / exp (n * log 2)) := by
          rw [h3]
          gcongr
      _ = _ := by
          rw [← exp_sub, ← exp_add]
          congr 1
          rw [hε]
          ring
  refine squeeze_zero hnn (fun n => (hc n).trans (add_le_add le_rfl (hle n))) ?_
  simpa using ha.add hb

end Achievability

/-! ### Separate source–channel coding -/

section Separation

/-- **Lecture 22 of [elgamal2010], page 22-33.** The modulo-2 sum channel `Y = X₁ ⊕ X₂ ⊕ N`. -/
def macSumChannel (ν : ZMod 2 → ℝ) (x : ZMod 2 × ZMod 2) (y : ZMod 2) : ℝ := ν (y - (x.1 + x.2))

lemma macSumChannel_isChannel (hν : IsPMF ν) : IsChannel (macSumChannel ν) :=
  fun x => ⟨fun y => hν.nonneg _, by
    rw [← hν.sum_eq_one]
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl⟩

lemma entropy_macSumChannel (ν : ZMod 2 → ℝ) (x : ZMod 2 × ZMod 2) :
    entropy (macSumChannel ν x) = entropy ν := by
  rw [entropy, entropy]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl

/-- `I(X₁, X₂; Y) ≤ log 2 - H(N)`. -/
lemma macInfo₁₂_macSumChannel_le (hν : IsPMF ν) {p₁ p₂ : ZMod 2 → ℝ} (h₁ : IsPMF p₁)
    (h₂ : IsPMF p₂) : macInfo₁₂ p₁ p₂ (macSumChannel ν) ≤ log 2 - entropy ν := by
  have hp := h₁.prodDist h₂
  have hW := macSumChannel_isChannel hν
  have e : macInfo₁₂ p₁ p₂ (macSumChannel ν) = mutualInfoOf (prodDist p₁ p₂) (macSumChannel ν) :=
    rfl
  rw [e, mutualInfoOf_eq hp hW]
  simp only [entropy_macSumChannel, ← sum_mul, hp.sum_eq_one, one_mul]
  have := entropy_le_log_card (outDist_isPMF hp hW)
  simp only [ZMod.card, Nat.cast_ofNat] at this
  linarith

/-- **Lecture 22, page 22-34.** Separate source–channel coding: a rate pair in the capacity region
of the channel has `R₁ + R₂ ≤ 1 - H(N)`, in bits. -/
theorem sum_le_of_mem_macCapacityRegionBits (hν : IsPMF ν) {R : ℝ × ℝ}
    (hR : R ∈ macCapacityRegionBits (macSumChannel ν)) :
    R.1 + R.2 ≤ (log 2 - entropy ν) / log 2 := by
  have hl := log_pos one_lt_two
  rw [macCapacityRegionBits_eq (macSumChannel_isChannel hν)] at hR
  have hconv : Convex ℝ {R : ℝ × ℝ | R.1 + R.2 ≤ (log 2 - entropy ν) / log 2} := by
    intro a ha b hb s t hs ht hst
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at ha hb ⊢
    have h₁ := mul_le_mul_of_nonneg_left ha hs
    have h₂ := mul_le_mul_of_nonneg_left hb ht
    have e : s * ((log 2 - entropy ν) / log 2) + t * ((log 2 - entropy ν) / log 2) =
        (log 2 - entropy ν) / log 2 := by rw [← add_mul, hst, one_mul]
    linarith
  have hcl : IsClosed {R : ℝ × ℝ | R.1 + R.2 ≤ (log 2 - entropy ν) / log 2} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  refine closure_minimal (convexHull_min (fun R hR => ?_) hconv) hcl hR
  obtain ⟨p₁, p₂, h₁, h₂, -, -, h₃⟩ := hR
  exact h₃.trans (div_le_div_of_nonneg_right (macInfo₁₂_macSumChannel_le hν h₁ h₂) hl.le)

/-- With uniform inputs, `I(X₁; Y | X₂) = log 2 - H(N)`, and the same for the others. -/
lemma macInfo_uniform (hν : IsPMF ν) :
    macInfo₁ (uniformPMF (ZMod 2)) (uniformPMF (ZMod 2)) (macSumChannel ν) = log 2 - entropy ν ∧
      macInfo₂ (uniformPMF (ZMod 2)) (uniformPMF (ZMod 2)) (macSumChannel ν) =
        log 2 - entropy ν := by
  have hU : IsPMF (uniformPMF (ZMod 2)) := uniformPMF_isPMF
  have hW := macSumChannel_isChannel hν
  have key : ∀ V : ZMod 2 → ZMod 2 → ℝ, (∀ a, entropy (V a) = entropy ν) → IsChannel V →
      (∀ y, ∑ a, V a y = 1) → mutualInfoOf (uniformPMF (ZMod 2)) V = log 2 - entropy ν := by
    intro V hV hCh hs
    have hout : outDist (uniformPMF (ZMod 2)) V = uniformPMF (ZMod 2) := by
      funext y
      simp only [outDist, uniformPMF, ← mul_sum, hs, mul_one]
    rw [mutualInfoOf_eq hU hCh, hout, entropy_uniformPMF]
    simp only [hV, ← sum_mul, hU.sum_eq_one, one_mul, ZMod.card, Nat.cast_ofNat]
  have hshift : ∀ (c y : ZMod 2), ∑ a, ν (y - (a + c)) = 1 := fun c y => by
    rw [← hν.sum_eq_one]
    exact Fintype.sum_equiv ⟨fun a => y - (a + c), fun b => y - b - c, fun a => by ring,
      fun b => by ring⟩ _ _ fun _ => rfl
  have hshift' : ∀ (c y : ZMod 2), ∑ a, ν (y - (c + a)) = 1 := fun c y => by
    simpa only [add_comm c] using hshift c y
  constructor
  · rw [macInfo₁_eq_sum hU hU hW]
    have h : ∀ b, mutualInfoOf (uniformPMF (ZMod 2)) (fun a => macSumChannel ν (a, b)) =
        log 2 - entropy ν := fun b =>
      key _ (fun a => entropy_macSumChannel ν (a, b))
        (fun a => hW (a, b)) fun y => hshift b y
    simp only [h, ← sum_mul, hU.sum_eq_one, one_mul]
  · rw [macInfo₂_eq_sum hU hU hW]
    have h : ∀ a, mutualInfoOf (uniformPMF (ZMod 2)) (fun b => macSumChannel ν (a, b)) =
        log 2 - entropy ν := fun a =>
      key _ (fun b => entropy_macSumChannel ν (a, b))
        (fun b => hW (a, b)) fun y => hshift' a y
    simp only [h, ← sum_mul, hU.sum_eq_one, one_mul]

/-- **Lecture 22 of [elgamal2010], page 22-34.** Separate source–channel coding achieves a rate `r`
if and only if `2 r ≤ 1 - H(N)`, in bits: `(r, r)` must lie in the capacity region of the channel,
as `H(U₁) = H(U₂) = 1` bit. -/
theorem mem_macCapacityRegionBits_diag_iff (hν : IsPMF ν) {r : ℝ} (h0 : 0 ≤ r) :
    (r, r) ∈ macCapacityRegionBits (macSumChannel ν) ↔
      2 * r ≤ (log 2 - entropy ν) / log 2 := by
  have hl := log_pos one_lt_two
  have hW := macSumChannel_isChannel hν
  constructor
  · intro h
    have := sum_le_of_mem_macCapacityRegionBits hν h
    dsimp only at this
    linarith
  · intro h
    rw [macCapacityRegionBits_eq hW]
    refine subset_closure (subset_convexHull ℝ _ ?_)
    have hU : IsPMF (uniformPMF (ZMod 2)) := uniformPMF_isPMF
    obtain ⟨e₁, e₂⟩ := macInfo_uniform hν
    have hr : r ≤ (log 2 - entropy ν) / log 2 := by linarith
    refine ⟨uniformPMF _, uniformPMF _, hU, hU, ?_, ?_, ?_⟩
    · rw [e₁]
      exact hr
    · rw [e₂]
      exact hr
    · have e₃ : macInfo₁₂ (uniformPMF (ZMod 2)) (uniformPMF (ZMod 2)) (macSumChannel ν) =
          log 2 - entropy ν := by
        refine le_antisymm (macInfo₁₂_macSumChannel_le hν hU hU) ?_
        rw [← e₁]
        exact macInfo₁_le_macInfo₁₂ hU hU hW
      rw [e₃]
      dsimp only
      linarith

/-- **Lecture 22, pages 22-34 and 22-35.** Separation is suboptimal for computing: if the noise is
not uniform, the rate `(1 - H(N)) / 2` of separate coding is below the computing capacity
`1 - H(N)`, so some computable rate cannot be achieved by separate source–channel coding. -/
theorem exists_isComputable_not_separate (hν : IsPMF ν) (hH : entropy ν < log 2) :
    ∃ r, IsComputable ν r ∧ (r, r) ∉ macCapacityRegionBits (macSumChannel ν) := by
  have hl := log_pos one_lt_two
  have hC : 0 < (log 2 - entropy ν) / log 2 := div_pos (by linarith) hl
  set C := (log 2 - entropy ν) / log 2 with hCd
  refine ⟨3 / 4 * C, isComputable_of_lt hν (by positivity) ?_, fun h => ?_⟩
  · have e : C * log 2 = log 2 - entropy ν := div_mul_cancel₀ _ hl.ne'
    have : 3 / 4 * C * log 2 < C * log 2 := by
      have := mul_pos hC hl
      nlinarith
    rw [e] at this
    exact this
  · have := (mem_macCapacityRegionBits_diag_iff hν (by positivity)).1 h
    rw [← hCd] at this
    linarith

end Separation

end InfoTheory
