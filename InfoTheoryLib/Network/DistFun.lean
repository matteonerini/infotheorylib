/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.BinaryMatrix
public import InfoTheoryLib.Network.SlepianWolfBits
public import InfoTheoryLib.Network.SlepianWolfMany
public import InfoTheoryLib.RateDistortion.GraphEntropy

/-!
# Distributed coding for lossless computing

This file proves the bounds of Lecture 22 of [elgamal2010] on the rates for computing a function
`Z = g(X₁, X₂)` of two separately encoded sources: the Slepian–Wolf inner bound and the outer bound
from the Orlitsky–Roche theorem, and the example of Körner and Marton, where random linear codes
compute `X₁ ⊕ X₂` at rates below the Slepian–Wolf region.

## Main definitions

* `DistFunCode`, `IsAchievableDistFun`, `distFunRegion`: the codes and the optimal rate region.
* `distFunOuter`: the outer bound `R₁ ≥ H_{G₁}(X₁ | X₂)`, `R₂ ≥ H_{G₂}(X₂ | X₁)`.

## Main statements

* `swRegionBits_subset_distFunRegion`: the inner bound.
* `distFunRegion_subset_distFunOuter`: the outer bound, and `condEntropy_le_of_mem_distFunRegion`,
  the simpler form `R₁ ≥ H(Z | X₂)`, `R₂ ≥ H(Z | X₁)`.
* `isAchievableDistFun_add`: **Körner and Marton**: for any law of binary `(X₁, X₂)`, the rates
  `R₁, R₂ > H(X₁ ⊕ X₂)` are achievable for computing `X₁ ⊕ X₂`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 22
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂]

/-! ### The problem -/

/-- **Lecture 22 of [elgamal2010], page 22-10.** A code for computing a function of two sources. -/
structure DistFunCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*) where
  /-- The first encoder. -/
  enc₁ : (Fin n → α₁) → Fin M₁
  /-- The second encoder. -/
  enc₂ : (Fin n → α₂) → Fin M₂
  /-- The decoder. -/
  dec : Fin M₁ → Fin M₂ → Fin n → β

open Classical in
/-- The probability of error `P{Ẑⁿ ≠ Zⁿ}`. -/
def DistFunCode.errProb {M₁ M₂ n : ℕ} (c : DistFunCode M₁ M₂ n α₁ α₂ β) (P : α₁ × α₂ → ℝ)
    (g : α₁ × α₂ → β) : ℝ :=
  ∑ ω, if c.dec (c.enc₁ (fstSeq ω)) (c.enc₂ (sndSeq ω)) ≠ fun i => g (ω i) then iidPMF P n ω else 0

/-- **Lecture 22 of [elgamal2010], page 22-10.** A rate pair, in bits, is achievable for computing
`Z = g(X₁, X₂)` if there are `(2^{nR₁}, 2^{nR₂}, n)` codes with `P{Ẑⁿ ≠ Zⁿ} → 0`. -/
def IsAchievableDistFun (P : α₁ × α₂ → ℝ) (g : α₁ × α₂ → β) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ ∃ c : ∀ n : ℕ, DistFunCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂ β,
    Tendsto (fun n => (c n).errProb P g) atTop (𝓝 0)

/-- **Lecture 22 of [elgamal2010], page 22-10.** The optimal rate region for computing `Z`. -/
def distFunRegion (P : α₁ × α₂ → ℝ) (g : α₁ × α₂ → β) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableDistFun P g R.1 R.2}

/-- **Lecture 22 of [elgamal2010], page 22-13.** The outer bound from the Orlitsky–Roche theorem:
`R₁ ≥ H_{G₁}(X₁ | X₂)` and `R₂ ≥ H_{G₂}(X₂ | X₁)`, in bits. -/
def distFunOuter (P : α₁ × α₂ → ℝ) (g : α₁ × α₂ → β) : Set (ℝ × ℝ) :=
  {R | condGraphEntropy (charGraph P g) P / log 2 ≤ R.1 ∧
    condGraphEntropy (charGraph (P ∘ Prod.swap) (g ∘ Prod.swap)) (P ∘ Prod.swap) / log 2 ≤ R.2}

/-! ### The bounds -/

section Bounds

variable {P : α₁ × α₂ → ℝ} {g : α₁ × α₂ → β}

/-- **Lecture 22, page 22-11.** Even when the receiver knows `X₂`, the first encoder must send at
the optimal rate of computing with side information. -/
theorem IsAchievableDistFun.lossless₁ {R₁ R₂ : ℝ} (h : IsAchievableDistFun P g R₁ R₂) :
    IsLosslessFunBits P g R₁ := by
  obtain ⟨h₁, -, c, hc⟩ := h
  exact ⟨h₁, fun n => ⟨(c n).enc₁, fun m y => (c n).dec m ((c n).enc₂ y)⟩, hc⟩

/-- `(fstSeq, sndSeq)` after a swap of the sources. -/
private lemma sum_iid_swap {n : ℕ} (F : (Fin n → α₁ × α₂) → ℝ) :
    ∑ ω, iidPMF (P ∘ Prod.swap) n ω * F (fun i => (ω i).swap) = ∑ ω, iidPMF P n ω * F ω := by
  let e : (Fin n → α₂ × α₁) ≃ (Fin n → α₁ × α₂) := Equiv.piCongrRight fun _ => Equiv.prodComm _ _
  refine Fintype.sum_equiv e _ _ fun ω => ?_
  congr 1

/-- The same for the second encoder. -/
theorem IsAchievableDistFun.lossless₂ {R₁ R₂ : ℝ}
    (h : IsAchievableDistFun P g R₁ R₂) : IsLosslessFunBits (P ∘ Prod.swap) (g ∘ Prod.swap) R₂ := by
  classical
  obtain ⟨-, h₂, c, hc⟩ := h
  refine ⟨h₂, fun n => ⟨(c n).enc₂, fun m y => (c n).dec ((c n).enc₁ y) m⟩, ?_⟩
  refine hc.congr fun n => ?_
  have h := sum_iid_swap (P := P) (n := n) fun ω =>
    if (c n).dec ((c n).enc₁ (fstSeq ω)) ((c n).enc₂ (sndSeq ω)) ≠ (fun i => g (ω i)) then
      (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  exact h.symm.trans (by rfl)

/-- **Lecture 22, page 22-13.** The outer bound from the Orlitsky–Roche theorem. -/
theorem distFunRegion_subset_distFunOuter [Finite β] (hP : IsPMF P) (g : α₁ × α₂ → β) :
    distFunRegion P g ⊆ distFunOuter P g := by
  have hl := log_pos one_lt_two
  have hP' : IsPMF (P ∘ Prod.swap) := by
    refine ⟨fun z => hP.nonneg _, ?_⟩
    rw [← hP.sum_eq_one]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl
  refine closure_minimal (fun R hR => ⟨?_, ?_⟩) ?_
  · rw [div_le_iff₀ hl, ← funLosslessRate_eq_condGraphEntropy hP]
    exact hR.lossless₁.le hP
  · rw [div_le_iff₀ hl, ← funLosslessRate_eq_condGraphEntropy hP']
    exact hR.lossless₂.le hP'
  · exact (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)

/-- **Lecture 22, page 22-11.** The simple outer bound `R₁ ≥ H(Z | X₂)` and `R₂ ≥ H(Z | X₁)`. -/
theorem condEntropy_le_of_mem_distFunRegion [Fintype β] (hP : IsPMF P) {g : α₁ × α₂ → β}
    {R : ℝ × ℝ} (hR : R ∈ distFunRegion P g) :
    H[g | Prod.snd ; P] / log 2 ≤ R.1 ∧ H[g | Prod.fst ; P] / log 2 ≤ R.2 := by
  have hl := log_pos one_lt_two
  have hP' : IsPMF (P ∘ Prod.swap) := by
    refine ⟨fun z => hP.nonneg _, ?_⟩
    rw [← hP.sum_eq_one]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl
  obtain ⟨h₁, h₂⟩ := distFunRegion_subset_distFunOuter hP g hR
  rw [← funLosslessRate_eq_condGraphEntropy hP] at h₁
  rw [← funLosslessRate_eq_condGraphEntropy hP'] at h₂
  refine ⟨le_trans ?_ h₁, le_trans ?_ h₂⟩
  · exact div_le_div_of_nonneg_right (condEntropy_le_funLosslessRate hP g) hl.le
  · refine div_le_div_of_nonneg_right (le_trans (le_of_eq ?_)
      (condEntropy_le_funLosslessRate hP' (g ∘ Prod.swap))) hl.le
    refine condEntropy_eq_of_dist_pair_eq hP hP' ?_
    funext ⟨a, b⟩
    simp only [dist, pair, Function.comp]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl

/-- A Slepian–Wolf code computes any function. -/
theorem IsAchievableSWBits.isAchievableDistFun {R₁ R₂ : ℝ} (hP : IsPMF P) (g : α₁ × α₂ → β)
    (h : IsAchievableSWBits P R₁ R₂) : IsAchievableDistFun P g R₁ R₂ := by
  classical
  obtain ⟨h₁, h₂, c, hc⟩ := h
  refine ⟨h₁, h₂, fun n => ⟨(c n).enc₁, (c n).enc₂, fun m₁ m₂ i =>
    g (((c n).dec (m₁, m₂)).1 i, ((c n).dec (m₁, m₂)).2 i)⟩, ?_⟩
  have hnn : ∀ n : ℕ, 0 ≤ DistFunCode.errProb (⟨(c n).enc₁, (c n).enc₂, fun m₁ m₂ i =>
      g (((c n).dec (m₁, m₂)).1 i, ((c n).dec (m₁, m₂)).2 i)⟩ : DistFunCode _ _ n α₁ α₂ β) P g :=
    fun n => sum_nonneg fun ω _ => by
      split_ifs
      · exact iidPMF_nonneg hP.nonneg ω
      · exact le_rfl
  refine squeeze_zero hnn (fun n => ?_) hc
  · rw [SWCode.errProb]
    refine le_trans (sum_le_sum fun ω _ => ?_) (le_of_eq (Fintype.sum_equiv
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => α₁) (fun _ => α₂)) (fun ω =>
        if (c n).dec ((c n).index (fstSeq ω, sndSeq ω)) ≠ (fstSeq ω, sndSeq ω) then
          iidPMF P n ω else 0) _ fun ω => rfl))
    by_cases he : (c n).dec ((c n).index (fstSeq ω, sndSeq ω)) = (fstSeq ω, sndSeq ω)
    · have hd : (fun i => g (((c n).dec ((c n).enc₁ (fstSeq ω), (c n).enc₂ (sndSeq ω))).1 i,
          ((c n).dec ((c n).enc₁ (fstSeq ω), (c n).enc₂ (sndSeq ω))).2 i)) =
          fun i => g (ω i) := by
        have he' : (c n).dec ((c n).enc₁ (fstSeq ω), (c n).enc₂ (sndSeq ω)) =
            (fstSeq ω, sndSeq ω) := he
        simp only [he']
        rfl
      simp [hd, he]
    · simp only [ne_eq, he, not_false_eq_true, ite_true]
      split_ifs
      · exact iidPMF_nonneg hP.nonneg ω
      · exact le_rfl

/-- **Lecture 22, page 22-11.** The Slepian–Wolf region is an inner bound on the rate region for any
function. -/
theorem swRegionBits_subset_distFunRegion (hP : IsPMF P) (g : α₁ × α₂ → β) :
    swRegionBits P ⊆ distFunRegion P g := by
  rw [← swOptimalRegionBits_eq hP]
  exact closure_mono fun R hR => IsAchievableSWBits.isAchievableDistFun hP g hR

end Bounds

/-! ### Random linear codes -/

section Linear

variable {k n : ℕ}

/-- The product `A x` of a binary matrix and a vector. -/
def binMul (A : Fin k → Fin n → ZMod 2) (x : Fin n → ZMod 2) : Fin k → ZMod 2 :=
  fun j => A j ⬝ᵥ x

lemma binMul_add (A : Fin k → Fin n → ZMod 2) (x y : Fin n → ZMod 2) :
    binMul A (x + y) = binMul A x + binMul A y := by
  funext j
  simp [binMul, dotProduct_add]

/-- **Lecture 22, page 22-12.** The fraction of the binary matrices with `A z' = A z` is `2^{-k}`,
for `z' ≠ z`. -/
lemma sum_binMul_eq {z z' : Fin n → ZMod 2} (hne : z' ≠ z) :
    ∑ A : Fin k → Fin n → ZMod 2, (if binMul A z' = binMul A z then (1 : ℝ) else 0) =
      (2 : ℝ) ^ (n * k) / 2 ^ k := by
  have hv : z' - z ≠ 0 := sub_ne_zero.2 hne
  rw [← card_mulVec_eq hv 0, Finset.sum_boole]
  congr 2
  ext A
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h j
    have := congrFun h j
    simp only [binMul] at this
    rw [dotProduct_sub, this, sub_self]
    rfl
  · intro h
    funext j
    have := h j
    rw [dotProduct_sub, Pi.zero_apply, sub_eq_zero] at this
    exact this

/-- The number of binary matrices. -/
lemma card_binMatrix : ((univ : Finset (Fin k → Fin n → ZMod 2)).card : ℝ) = (2 : ℝ) ^ (n * k) := by
  rw [card_univ]
  simp [ZMod.card, ← pow_mul, mul_comm]

/-- The probability that an i.i.d. sequence is not typical tends to `0`. -/
lemma tendsto_sum_not_mem_typicalSet {γ : Type*} [Fintype γ] [DecidableEq γ] {p : γ → ℝ}
  (hp : IsPMF p) {ε : ℝ}
    (hε : 0 < ε) : Tendsto (fun n : ℕ => ∑ z, iidPMF p n z *
      (if z ∈ typicalSet p n ε then (0 : ℝ) else 1)) atTop (𝓝 0) := by
  classical
  have ht := tendsto_prob_typicalSet hp hε
  have he : ∀ n : ℕ, ∑ z, iidPMF p n z * (if z ∈ typicalSet p n ε then (0 : ℝ) else 1) =
      1 - prob (iidPMF p n) (typicalSet p n ε) := fun n => by
    have h : ∀ z, iidPMF p n z * (if z ∈ typicalSet p n ε then (0 : ℝ) else 1) = iidPMF p n z -
        if z ∈ typicalSet p n ε then iidPMF p n z else 0 := fun z => by
      split_ifs <;> simp
    simp only [h]
    rw [sum_sub_distrib, (iidPMF_isPMF hp n).sum_eq_one, sum_ite_mem, univ_inter, prob]
  simp only [he]
  simpa using ht.const_sub 1

/-- `A (x - y) = A x - A y`. -/
lemma binMul_sub (A : Fin k → Fin n → ZMod 2) (x y : Fin n → ZMod 2) :
    binMul A (x - y) = binMul A x - binMul A y := by
  funext j
  simp [binMul, dotProduct_sub]

/-- **Lecture 22, page 22-12.** The error of the decoder of a random linear code: there is a binary
matrix for which, except with the probability that `Zⁿ ∉ T`, no other sequence of `T` has the same
image as `Zⁿ`, up to `|T| 2^{-k}`. -/
theorem exists_binMatrix_le {μ : (Fin n → ZMod 2) → ℝ} (hμ : IsPMF μ)
    (T : Finset (Fin n → ZMod 2)) :
    ∃ A : Fin k → Fin n → ZMod 2,
      ∑ z, μ z * ((if z ∈ T then (0 : ℝ) else 1) +
        ∑ z' ∈ T, if z' ≠ z ∧ binMul A z' = binMul A z then (1 : ℝ) else 0) ≤
      (∑ z, μ z * (if z ∈ T then (0 : ℝ) else 1)) + (T.card : ℝ) / 2 ^ k := by
  classical
  have hN : (0 : ℝ) < (2 : ℝ) ^ (n * k) := by positivity
  have hkey : ∑ A : Fin k → Fin n → ZMod 2, ∑ z, μ z * ((if z ∈ T then (0 : ℝ) else 1) +
      ∑ z' ∈ T, if z' ≠ z ∧ binMul A z' = binMul A z then (1 : ℝ) else 0) ≤
      ∑ _A : Fin k → Fin n → ZMod 2,
        ((∑ z, μ z * (if z ∈ T then (0 : ℝ) else 1)) + (T.card : ℝ) / 2 ^ k) := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    have hc : ((Fintype.card (Fin k → Fin n → ZMod 2) : ℕ) : ℝ) = (2 : ℝ) ^ (n * k) := by
      rw [← card_univ]; exact card_binMatrix
    rw [hc, sum_comm]
    have hz : ∀ z, ∑ A : Fin k → Fin n → ZMod 2, μ z * ((if z ∈ T then (0 : ℝ) else 1) +
        ∑ z' ∈ T, if z' ≠ z ∧ binMul A z' = binMul A z then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (n * k) * (μ z * (if z ∈ T then (0 : ℝ) else 1) + μ z * ((T.card : ℝ) / 2 ^ k)) :=
          by
      intro z
      rw [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hc, sum_comm]
      have hin : ∑ z' ∈ T, ∑ A : Fin k → Fin n → ZMod 2,
          (if z' ≠ z ∧ binMul A z' = binMul A z then (1 : ℝ) else 0) ≤
          ∑ _z' ∈ T, (2 : ℝ) ^ (n * k) / 2 ^ k := by
        refine sum_le_sum fun z' _ => ?_
        by_cases hne : z' = z
        · simp only [hne, ne_eq, not_true_eq_false, false_and, ite_false, sum_const_zero]
          positivity
        · simp only [hne, ne_eq, not_false_eq_true, true_and]
          exact (sum_binMul_eq hne).le
      rw [sum_const, nsmul_eq_mul] at hin
      have := mul_le_mul_of_nonneg_left hin (hμ.nonneg z)
      have e : μ z * ((T.card : ℝ) * ((2 : ℝ) ^ (n * k) / 2 ^ k)) =
          (2 : ℝ) ^ (n * k) * (μ z * ((T.card : ℝ) / 2 ^ k)) := by ring
      nlinarith [this, e]
    refine (sum_le_sum fun z _ => hz z).trans (le_of_eq ?_)
    rw [← mul_sum, sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul]
  obtain ⟨A, -, hA⟩ := exists_le_of_sum_le (s := univ) univ_nonempty hkey
  exact ⟨A, hA⟩

/-- The sequence `Z = X₁ ⊕ X₂`. -/
def addSeq (ω : Fin n → ZMod 2 × ZMod 2) : Fin n → ZMod 2 := fun i => (ω i).1 + (ω i).2

/-- The code with a matrix `A`: the encoders send `A X₁ⁿ` and `A X₂ⁿ`; the decoder adds them, and
looks for the unique sequence of `T` with this image. -/
def linearCode {M₁ M₂ : ℕ} (A : Fin k → Fin n → ZMod 2) (T : Finset (Fin n → ZMod 2))
    (e₁ : (Fin k → ZMod 2) ↪ Fin M₁) (e₂ : (Fin k → ZMod 2) ↪ Fin M₂) :
    DistFunCode M₁ M₂ n (ZMod 2) (ZMod 2) (ZMod 2) where
  enc₁ x := e₁ (binMul A x)
  enc₂ x := e₂ (binMul A x)
  dec m₁ m₂ :=
    open Classical in
    let s := Function.invFun e₁ m₁ + Function.invFun e₂ m₂
    if h : ∃ z ∈ T, binMul A z = s then h.choose else 0

/-- **Lecture 22, page 22-12.** The code of a matrix errs only if `Zⁿ ∉ T`, or if another sequence
of `T` has the same image as `Zⁿ`. -/
lemma linearCode_err_le {M₁ M₂ : ℕ} (A : Fin k → Fin n → ZMod 2) (T : Finset (Fin n → ZMod 2))
    (e₁ : (Fin k → ZMod 2) ↪ Fin M₁) (e₂ : (Fin k → ZMod 2) ↪ Fin M₂)
    (ω : Fin n → ZMod 2 × ZMod 2) :
    (open Classical in if (linearCode A T e₁ e₂).dec ((linearCode A T e₁ e₂).enc₁ (fstSeq ω))
        ((linearCode A T e₁ e₂).enc₂ (sndSeq ω)) ≠ addSeq ω then (1 : ℝ) else 0) ≤
      (if addSeq ω ∈ T then (0 : ℝ) else 1) +
        ∑ z' ∈ T, if z' ≠ addSeq ω ∧ binMul A z' = binMul A (addSeq ω) then (1 : ℝ) else 0 := by
  classical
  have h0 : 0 ≤ ∑ z' ∈ T, if z' ≠ addSeq ω ∧ binMul A z' =
    binMul A (addSeq ω) then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hT : addSeq ω ∈ T
  · simp only [hT, ite_true, zero_add]
    by_cases hdec : (linearCode A T e₁ e₂).dec ((linearCode A T e₁ e₂).enc₁ (fstSeq ω))
        ((linearCode A T e₁ e₂).enc₂ (sndSeq ω)) = addSeq ω
    · simp [hdec]
    · simp only [ne_eq, hdec, not_false_eq_true, ite_true]
      have hs : Function.invFun e₁ (e₁ (binMul A (fstSeq ω))) +
          Function.invFun e₂ (e₂ (binMul A (sndSeq ω))) = binMul A (addSeq ω) := by
        rw [Function.leftInverse_invFun e₁.injective, Function.leftInverse_invFun e₂.injective,
          ← binMul_add]
        rfl
      have hex : ∃ z ∈ T, binMul A z = binMul A (addSeq ω) := ⟨_, hT, rfl⟩
      have hd : (linearCode A T e₁ e₂).dec ((linearCode A T e₁ e₂).enc₁ (fstSeq ω))
          ((linearCode A T e₁ e₂).enc₂ (sndSeq ω)) = hex.choose := by
        simp only [linearCode, hs]
        rw [dite_eq_left_of_eq_true (eq_true hex)]
      obtain ⟨hc₁, hc₂⟩ := hex.choose_spec
      have hne : hex.choose ≠ addSeq ω := fun h => hdec (hd.trans h)
      calc (1 : ℝ) = if hex.choose ≠ addSeq ω ∧ binMul A hex.choose = binMul A (addSeq ω) then
            (1 : ℝ) else 0 := by simp [hne, hc₂]
        _ ≤ _ := single_le_sum (f := fun z' => if z' ≠ addSeq ω ∧
            binMul A z' = binMul A (addSeq ω) then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) hc₁
  · simp only [hT, ite_false]
    split_ifs <;> linarith

end Linear

/-! ### The theorem of Körner and Marton -/

section KornerMarton

variable {P : ZMod 2 × ZMod 2 → ℝ}

/-- `Z = X₁ ⊕ X₂` as a function of the pair. -/
def addZ (z : ZMod 2 × ZMod 2) : ZMod 2 := z.1 + z.2

/-- **Lecture 22, page 22-12.** For each length, there is a linear code with an error of at most
`P{Zⁿ ∉ T} + |T| 2^{-k}`, with `k ≤ log₂ Mⱼ`. -/
theorem exists_linearCode_le (hP : IsPMF P) {n k M₁ M₂ : ℕ} (h₁ : 2 ^ k ≤ M₁) (h₂ : 2 ^ k ≤ M₂)
    (T : Finset (Fin n → ZMod 2)) :
    ∃ c : DistFunCode M₁ M₂ n (ZMod 2) (ZMod 2) (ZMod 2), c.errProb P addZ ≤
      (∑ z, iidPMF (dist P addZ) n z * (if z ∈ T then (0 : ℝ) else 1)) + (T.card : ℝ) / 2 ^ k := by
  classical
  have hcard : ∀ {M : ℕ}, 2 ^ k ≤ M → Nonempty ((Fin k → ZMod 2) ↪ Fin M) := fun {M} h =>
    Function.Embedding.nonempty_of_card_le (by simpa [ZMod.card] using h)
  obtain ⟨e₁⟩ := hcard h₁
  obtain ⟨e₂⟩ := hcard h₂
  have hμ : IsPMF (iidPMF (dist P addZ) n) := iidPMF_isPMF (hP.dist _) n
  obtain ⟨A, hA⟩ := exists_binMatrix_le (k := k) hμ T
  refine ⟨linearCode A T e₁ e₂, le_trans ?_ hA⟩
  have hdist : iidPMF (dist P addZ) n = dist (iidPMF P n) addSeq :=
    (dist_iidPMF_comp P n addZ).symm
  rw [hdist]
  rw [sum_dist_mul]
  refine sum_le_sum fun ω _ => ?_
  have h0 := iidPMF_nonneg hP.nonneg ω
  have hle := linearCode_err_le A T e₁ e₂ ω
  have hg : (fun i => addZ (ω i)) = addSeq ω := rfl
  simp only [hg]
  calc _ = iidPMF P n ω * (if (linearCode A T e₁ e₂).dec
        ((linearCode A T e₁ e₂).enc₁ (fstSeq ω)) ((linearCode A T e₁ e₂).enc₂ (sndSeq ω)) ≠
          addSeq ω then (1 : ℝ) else 0) := by split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hle h0

/-- **The theorem of Körner and Marton (Lecture 22 of [elgamal2010], page 22-12).** For any law of
binary `(X₁, X₂)`, the rates `R₁, R₂ > H(X₁ ⊕ X₂)` bits are achievable for computing `X₁ ⊕ X₂`, by
random linear codes. -/
theorem isAchievableDistFun_add (hP : IsPMF P) {R₁ R₂ : ℝ} (h₁ : entropy (dist P addZ) / log 2 < R₁)
    (h₂ : entropy (dist P addZ) / log 2 < R₂) : IsAchievableDistFun P addZ R₁ R₂ := by
  classical
  have hl := log_pos one_lt_two
  have hz : IsPMF (dist P addZ) := hP.dist _
  have hH : 0 ≤ entropy (dist P addZ) := entropy_nonneg hz
  set H := entropy (dist P addZ) with hHd
  have hH0 : 0 ≤ H / log 2 := div_nonneg hH hl.le
  set R := min R₁ R₂ with hR
  have hRH : H / log 2 < R := lt_min h₁ h₂
  have hR0 : 0 < R := hH0.trans_lt hRH
  have hgap : H < R * log 2 := (div_lt_iff₀ hl).1 hRH
  set ε := (R * log 2 - H) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hfl : ∀ (n : ℕ) {S : ℝ}, R ≤ S → 2 ^ ⌊(n : ℝ) * R⌋₊ ≤ 2 ^ ⌊(n : ℝ) * S⌋₊ := fun n S hS =>
    Nat.pow_le_pow_right (by norm_num) (Nat.floor_mono (mul_le_mul_of_nonneg_left hS n.cast_nonneg))
  choose c hc using fun n : ℕ => exists_linearCode_le hP (hfl n (min_le_left R₁ R₂))
    (hfl n (min_le_right R₁ R₂)) (typicalSet (dist P addZ) n ε)
  refine ⟨h₁.le.trans' hH0, h₂.le.trans' hH0, c, ?_⟩
  have hnn : ∀ n, 0 ≤ (c n).errProb P addZ := fun n => sum_nonneg fun ω _ => by
    split_ifs
    · exact iidPMF_nonneg hP.nonneg ω
    · exact le_rfl
  have ha := tendsto_sum_not_mem_typicalSet hz hε0
  have hb : Tendsto (fun n : ℕ => exp (log 2 - n * ε)) atTop (𝓝 0) := by
    refine tendsto_exp_atBot.comp ?_
    have h' : Tendsto (fun n : ℕ => -((n : ℝ) * ε)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hε0)
    exact (tendsto_atBot_add_const_left atTop (log 2) h').congr fun n => by ring
  have hle : ∀ n : ℕ, ((typicalSet (dist P addZ) n ε).card : ℝ) / 2 ^ ⌊(n : ℝ) * R⌋₊ ≤
      exp (log 2 - n * ε) := fun n => by
    have hcard := card_typicalSet_le hz n ε
    have hk : (n : ℝ) * R - 1 ≤ (⌊(n : ℝ) * R⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one ((n : ℝ) * R)
      linarith
    have h2 : exp (((n : ℝ) * R - 1) * log 2) ≤ (2 : ℝ) ^ ⌊(n : ℝ) * R⌋₊ := by
      rw [← rpow_natCast, rpow_def_of_pos (by norm_num), mul_comm]
      exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hk hl.le)
    refine (div_le_div₀ (exp_pos _).le hcard (exp_pos _) h2).trans (le_of_eq ?_)
    rw [← exp_sub]
    congr 1
    rw [← hHd, hε]
    ring
  refine squeeze_zero hnn (fun n => (hc n).trans (add_le_add le_rfl (hle n))) ?_
  simpa using ha.add hb

/-- **Lecture 22 of [elgamal2010], page 22-12.** If `Z = X₁ ⊕ X₂` is independent of `X₁` and of
`X₂`, as for a doubly symmetric binary source, then the outer bound is tight: the optimal rate
region for computing `Z` is `R₁ ≥ H(Z)`, `R₂ ≥ H(Z)`, in bits. -/
theorem distFunRegion_add_eq (hP : IsPMF P) (h₁ : H[addZ | Prod.snd ; P] = entropy (dist P addZ))
    (h₂ : H[addZ | Prod.fst ; P] = entropy (dist P addZ)) :
    distFunRegion P addZ = {R | entropy (dist P addZ) / log 2 ≤ R.1 ∧
      entropy (dist P addZ) / log 2 ≤ R.2} := by
  ext R
  constructor
  · intro hR
    have := condEntropy_le_of_mem_distFunRegion hP hR
    rwa [h₁, h₂] at this
  · rintro ⟨hr₁, hr₂⟩
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
    exact isAchievableDistFun_add hP (by dsimp only; linarith) (by dsimp only; linarith)

end KornerMarton

end InfoTheory
