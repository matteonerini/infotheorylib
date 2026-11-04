/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCBits
public import InfoTheoryLib.ChannelCoding.Cost
public import InfoTheoryLib.Network.Typicality

/-!
# The laws and typical triples of superposition coding

The first part of the proof of Theorem 1 of Lecture 5 of El Gamal and Kim. The random codebook has
independent cloud centers `uⁿ(m₂)`, drawn i.i.d. from `p(u)`, and for each of them conditionally
independent satellite codewords `xⁿ(m₁, m₂)`, drawn from `∏ᵢ p(xᵢ | uᵢ(m₂))`. This file gives their
laws and the typical triples `(uⁿ, xⁿ, yⁿ)`, in the weak typicality of Chapter 7 of Cover and
Thomas.

## Main definitions

* `superpositionKernel q`, `superpositionSeqKernel q`: the conditional pmfs `p(x | u)` and
  `∏ᵢ p(xᵢ | uᵢ)`.
* `superpositionColumnLaw q n L`: the law of a cloud center with its `L` satellite codewords.
* `superpositionOut q V`, `superpositionTriple q V`: the laws of `(U, Y)` and `((U, X), Y)`.
* `superpositionTypicalSet q V n ε`: the typical triples `(uⁿ, xⁿ, yⁿ)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒰 α β : Type*} [Fintype 𝒰] [Fintype α] [Fintype β]

/-! ### The conditional law of the satellite codewords -/

/-- The conditional pmf `p(x | u) = p(u, x) / p(u)` of a joint pmf `q = p(u, x)`, set to the
marginal `p(x)` when `p(u) = 0`, so that it is a pmf for every `u`. -/
def superpositionKernel (q : 𝒰 × α → ℝ) (u : 𝒰) (x : α) : ℝ :=
  if margFst q u = 0 then margSnd q x else q (u, x) / margFst q u

variable {q : 𝒰 × α → ℝ}

lemma superpositionKernel_mul (hq : IsPMF q) (u : 𝒰) (x : α) :
    margFst q u * superpositionKernel q u x = q (u, x) := by
  unfold superpositionKernel
  split_ifs with h
  · have hle : q (u, x) ≤ margFst q u := by
      change q (u, x) ≤ dist q Prod.fst u
      rw [dist_fst]
      exact single_le_sum (f := fun b => q (u, b)) (fun b _ => hq.nonneg _) (mem_univ x)
    rw [h, zero_mul]
    exact le_antisymm (h ▸ hle) (hq.nonneg _) |>.symm
  · field_simp

lemma superpositionKernel_isPMF (hq : IsPMF q) (u : 𝒰) : IsPMF (superpositionKernel q u) := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold superpositionKernel
    split_ifs
    · exact (hq.dist _).nonneg x
    · exact div_nonneg (hq.nonneg _) ((hq.dist _).nonneg _)
  · unfold superpositionKernel
    split_ifs with h
    · exact (hq.dist _).sum_eq_one
    · rw [← sum_div, ← dist_fst, div_self h]

/-- The conditional pmf `∏ᵢ p(xᵢ | uᵢ)` of a satellite codeword given its cloud center. -/
def superpositionSeqKernel (q : 𝒰 × α → ℝ) {n : ℕ} (u : Fin n → 𝒰) (x : Fin n → α) : ℝ :=
  ∏ i, superpositionKernel q (u i) (x i)

lemma superpositionSeqKernel_isPMF (hq : IsPMF q) {n : ℕ} (u : Fin n → 𝒰) :
    IsPMF (superpositionSeqKernel q u) := by
  refine ⟨fun x => prod_nonneg fun i _ => (superpositionKernel_isPMF hq _).nonneg _, ?_⟩
  unfold superpositionSeqKernel
  rw [← Fintype.prod_sum fun i a => superpositionKernel q (u i) a]
  simp [(superpositionKernel_isPMF hq _).sum_eq_one]

lemma iidPMF_mul_superpositionSeqKernel (hq : IsPMF q) {n : ℕ} (u : Fin n → 𝒰)
    (x : Fin n → α) :
    iidPMF (margFst q) n u * superpositionSeqKernel q u x = jointIid q n (u, x) := by
  simp only [iidPMF, superpositionSeqKernel, jointIid, zipSeq, ← prod_mul_distrib,
    superpositionKernel_mul hq]

/-- The law of a column of the superposition codebook: a cloud center `uⁿ` drawn i.i.d. from
`p(u)`, and `L` satellite codewords drawn conditionally i.i.d. from `p(x | u)` given `uⁿ`. -/
def superpositionColumnLaw (q : 𝒰 × α → ℝ) (n L : ℕ) (c : (Fin n → 𝒰) × (Fin L → Fin n → α)) :
    ℝ :=
  iidPMF (margFst q) n c.1 * iidPMF (superpositionSeqKernel q c.1) L c.2

lemma superpositionColumnLaw_isPMF (hq : IsPMF q) (n L : ℕ) :
    IsPMF (superpositionColumnLaw q n L) := by
  refine ⟨fun c => mul_nonneg (iidPMF_nonneg (hq.dist _).nonneg _)
    (iidPMF_nonneg (superpositionSeqKernel_isPMF hq _).nonneg _), ?_⟩
  simp only [superpositionColumnLaw, Fintype.sum_prod_type, ← mul_sum,
    (iidPMF_isPMF (superpositionSeqKernel_isPMF hq _) L).sum_eq_one, mul_one,
    (iidPMF_isPMF (hq.dist _) n).sum_eq_one]

/-- Averaging a function of the cloud center and one satellite codeword of a column. -/
lemma sum_superpositionColumnLaw_eval (hq : IsPMF q) {n L : ℕ} (l : Fin L)
    (f : (Fin n → 𝒰) → (Fin n → α) → ℝ) :
    ∑ c, superpositionColumnLaw q n L c * f c.1 (c.2 l) =
      ∑ u, ∑ x, jointIid q n (u, x) * f u x := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  simp only [superpositionColumnLaw, mul_assoc, ← mul_sum]
  rw [sum_iidPMF_eval (superpositionSeqKernel_isPMF hq u) l (f u), mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, iidPMF_mul_superpositionSeqKernel hq]

/-- Averaging a function of the cloud center and two distinct satellite codewords of a column:
given the cloud center, they are independent. -/
lemma sum_superpositionColumnLaw_eval₂ (hq : IsPMF q) {n L : ℕ} {l l' : Fin L} (hl : l ≠ l')
    (f : (Fin n → 𝒰) → (Fin n → α) → (Fin n → α) → ℝ) :
    ∑ c, superpositionColumnLaw q n L c * f c.1 (c.2 l) (c.2 l') =
      ∑ u, ∑ x, ∑ x', jointIid q n (u, x) * superpositionSeqKernel q u x' * f u x x' := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  simp only [superpositionColumnLaw, mul_assoc, ← mul_sum]
  rw [sum_iidPMF_eval₂ (superpositionSeqKernel_isPMF hq u) hl (f u), mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← iidPMF_mul_superpositionSeqKernel hq u x, mul_sum, mul_sum]
  exact sum_congr rfl fun x' _ => by ring

/-! ### The laws of `(U, Y)` and `((U, X), Y)` -/

/-- The law `p(u, y) = ∑ₓ p(u, x) V(y | x)` of `(U, Y)`, for a channel `V` from `X` to `Y`. -/
def superpositionOut (q : 𝒰 × α → ℝ) (V : α → β → ℝ) : 𝒰 × β → ℝ :=
  fun z => ∑ x, q (z.1, x) * V x z.2

/-- The law `p(u, x) V(y | x)` of `((U, X), Y)`. -/
def superpositionTriple (q : 𝒰 × α → ℝ) (V : α → β → ℝ) : (𝒰 × α) × β → ℝ :=
  jointOf q fun z => V z.2

variable {V : α → β → ℝ}

lemma superpositionTriple_isPMF (hq : IsPMF q) (hV : IsChannel V) :
    IsPMF (superpositionTriple q V) :=
  jointOf_isPMF hq fun z => hV z.2

lemma margFst_superpositionTriple (hV : IsChannel V) : margFst (superpositionTriple q V) = q :=
  dist_jointOf_fst fun z => hV z.2

lemma superpositionOut_isPMF (hq : IsPMF q) (hV : IsChannel V) :
    IsPMF (superpositionOut q V) := by
  refine ⟨fun z => sum_nonneg fun x _ => mul_nonneg (hq.nonneg _) ((hV x).nonneg _), ?_⟩
  simp only [superpositionOut, Fintype.sum_prod_type]
  rw [← hq.sum_eq_one, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  simp only [← mul_sum, (hV _).sum_eq_one, mul_one]

lemma margFst_superpositionOut (hV : IsChannel V) :
    margFst (superpositionOut q V) = margFst q := by
  funext u
  change dist (superpositionOut q V) Prod.fst u = dist q Prod.fst u
  rw [dist_fst, dist_fst]
  simp only [superpositionOut]
  rw [sum_comm]
  simp only [← mul_sum, (hV _).sum_eq_one, mul_one]

omit [Fintype 𝒰] [Fintype β] in
/-- `∑_{xⁿ} p(uⁿ, xⁿ) V(yⁿ | xⁿ) = p(uⁿ, yⁿ)`. -/
lemma sum_jointIid_mul_channelExt (q : 𝒰 × α → ℝ) (V : α → β → ℝ) {n : ℕ} (u : Fin n → 𝒰)
    (y : Fin n → β) :
    ∑ x, jointIid q n (u, x) * channelExt V n x y = jointIid (superpositionOut q V) n (u, y) := by
  simp only [jointIid, iidPMF, channelExt, zipSeq, superpositionOut, ← prod_mul_distrib]
  exact (Fintype.prod_sum fun i a => q (u i, a) * V a (y i)).symm

omit [Fintype 𝒰] [Fintype α] [Fintype β] in
lemma jointIid_mul_channelExt_eq_triple (q : 𝒰 × α → ℝ) (V : α → β → ℝ) {n : ℕ}
    (u : Fin n → 𝒰) (x : Fin n → α) (y : Fin n → β) :
    jointIid q n (u, x) * channelExt V n x y =
      jointIid (superpositionTriple q V) n (zipSeq u x, y) := by
  simp only [jointIid, iidPMF, channelExt, zipSeq, superpositionTriple, jointOf,
    ← prod_mul_distrib]

/-! ### Typical triples -/

variable (q V) in
open Classical in
/-- The typical triples `(uⁿ, xⁿ, yⁿ)`: `((uⁿ, xⁿ), yⁿ)` is jointly typical for
`p(u, x) V(y | x)` and `(uⁿ, yⁿ)` is jointly typical for `p(u, y)`. -/
def superpositionTypicalSet (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → 𝒰) × (Fin n → α) × (Fin n → β)) :=
  univ.filter fun z => (zipSeq z.1 z.2.1, z.2.2) ∈ jointTypicalSet (superpositionTriple q V) n ε ∧
    (z.1, z.2.2) ∈ jointTypicalSet (superpositionOut q V) n ε

variable (q V) in
/-- A bound on the probability that the triple sent is not typical. -/
def superpositionAtypProb (n : ℕ) (ε : ℝ) : ℝ :=
  (1 - prob (jointIid (superpositionTriple q V) n)
      (jointTypicalSet (superpositionTriple q V) n ε)) +
    (1 - prob (jointIid (superpositionOut q V) n) (jointTypicalSet (superpositionOut q V) n ε))

lemma tendsto_superpositionAtypProb (hq : IsPMF q) (hV : IsChannel V) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => superpositionAtypProb q V n ε) atTop (𝓝 0) := by
  have c : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h₁ := c.sub (tendsto_prob_jointTypicalSet (superpositionTriple_isPMF hq hV) hε)
  have h₂ := c.sub (tendsto_prob_jointTypicalSet (superpositionOut_isPMF hq hV) hε)
  have h := h₁.add h₂
  rw [show (1 : ℝ) - 1 + (1 - 1) = 0 by norm_num] at h
  exact h

open Classical in
/-- **Event `E₁₁` of Lecture 5.** The triple sent is not typical with probability at most
`superpositionAtypProb`, which tends to `0` by the LLN. -/
lemma sum_superposition_atyp_le (hq : IsPMF q) (hV : IsChannel V) (n : ℕ) (ε : ℝ) :
    ∑ u, ∑ x, jointIid q n (u, x) *
        ∑ y, channelExt V n x y * (if (u, x, y) ∈ superpositionTypicalSet q V n ε then 0 else 1) ≤
      superpositionAtypProb q V n ε := by
  set J₁ := jointTypicalSet (superpositionTriple q V) n ε
  set J₂ := jointTypicalSet (superpositionOut q V) n ε
  have hpt : ∀ u x y, (if (u, x, y) ∈ superpositionTypicalSet q V n ε then (0 : ℝ) else 1) ≤
      (if (zipSeq u x, y) ∈ J₁ then 0 else 1) + (if (u, y) ∈ J₂ then 0 else 1) := by
    intro u x y
    simp only [superpositionTypicalSet, mem_filter, mem_univ, true_and]
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e₁ : ∑ u, ∑ x, ∑ y, jointIid q n (u, x) * channelExt V n x y *
      (if (zipSeq u x, y) ∈ J₁ then 0 else 1) =
      1 - prob (jointIid (superpositionTriple q V) n) J₁ := by
    rw [← sum_mul_ite_not_mem (jointIid_isPMF (superpositionTriple_isPMF hq hV) n),
      Fintype.sum_prod_type]
    simp_rw [jointIid_mul_channelExt_eq_triple]
    exact sum_zipSeq fun w => ∑ y, jointIid (superpositionTriple q V) n (w, y) *
      if (w, y) ∈ J₁ then 0 else 1
  have e₂ : ∑ u, ∑ x, ∑ y, jointIid q n (u, x) * channelExt V n x y *
      (if (u, y) ∈ J₂ then 0 else 1) = 1 - prob (jointIid (superpositionOut q V) n) J₂ := by
    rw [← sum_mul_ite_not_mem (jointIid_isPMF (superpositionOut_isPMF hq hV) n),
      Fintype.sum_prod_type]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_mul, sum_jointIid_mul_channelExt]
  calc _ ≤ ∑ u, ∑ x, ∑ y, (jointIid q n (u, x) * channelExt V n x y *
          (if (zipSeq u x, y) ∈ J₁ then 0 else 1) + jointIid q n (u, x) * channelExt V n x y *
          (if (u, y) ∈ J₂ then 0 else 1)) := by
        refine sum_le_sum fun u _ => sum_le_sum fun x _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun y _ => ?_
        rw [← mul_add, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (hpt u x y)
          (mul_nonneg (jointIid_nonneg hq.nonneg n _) (channelExt_nonneg hV _ _))
    _ = _ := by simp only [sum_add_distrib, e₁, e₂, superpositionAtypProb, J₁, J₂]

variable (q V) in
/-- `H(U, X) + H(U, Y) - H(U) - H(U, X, Y)`, which is `I(X; Y | U)`. -/
def superpositionInfoCond : ℝ :=
  entropy q + entropy (superpositionOut q V) - entropy (margFst q) -
    entropy (superpositionTriple q V)

open Classical in
/-- **Event `E₁₂` of Lecture 5.** A wrong satellite codeword of the right cloud center, which is
conditionally independent of the output given the cloud center, is typical with the output with
probability at most `e^{-n(I(X; Y | U) - 4ε)}`. -/
lemma sum_superposition_satellite_le (hq : IsPMF q) (hV : IsChannel V) (n : ℕ) (ε : ℝ) :
    ∑ u, ∑ x, ∑ x', jointIid q n (u, x) * superpositionSeqKernel q u x' *
        ∑ y, channelExt V n x y * (if (u, x', y) ∈ superpositionTypicalSet q V n ε then 1 else 0)
      ≤ exp (-(n * (superpositionInfoCond q V - 4 * ε))) := by
  set T := superpositionTypicalSet q V n ε
  set r := superpositionOut q V
  set t := superpositionTriple q V
  set B : ℝ := exp (-(n * (entropy r - ε))) *
    (exp (-(n * (entropy q - ε))) * exp (n * (entropy (margFst q) + ε)))
  have hT : ∀ g : (Fin n → 𝒰) × (Fin n → α) × (Fin n → β) → ℝ,
      ∑ z ∈ T, g z = ∑ u, ∑ x', ∑ y, if (u, x', y) ∈ T then g (u, x', y) else 0 := fun g => by
    have e : ∑ z ∈ T, g z = ∑ z, if z ∈ T then g z else 0 := by rw [sum_ite_mem, univ_inter]
    rw [e, Fintype.sum_prod_type]
    exact sum_congr rfl fun u _ => Fintype.sum_prod_type _
  have h1 : ∑ u, ∑ x, ∑ x', jointIid q n (u, x) * superpositionSeqKernel q u x' *
        ∑ y, channelExt V n x y * (if (u, x', y) ∈ T then 1 else 0) =
      ∑ z ∈ T, jointIid r n (z.1, z.2.2) * superpositionSeqKernel q z.1 z.2.1 := by
    rw [hT]
    refine sum_congr rfl fun u _ => ?_
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun x' _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_jointIid_mul_channelExt, sum_mul]
    split_ifs <;> simp only [mul_one, mul_zero, sum_const_zero]
    exact sum_congr rfl fun x _ => by ring
  -- The bound on each typical triple.
  have hpt : ∀ z ∈ T, jointIid r n (z.1, z.2.2) * superpositionSeqKernel q z.1 z.2.1 ≤ B := by
    intro z hz
    simp only [T, superpositionTypicalSet, mem_filter, mem_univ, true_and,
      mem_jointTypicalSet] at hz
    obtain ⟨⟨hux, -, -⟩, hu, -, huy⟩ := hz
    rw [margFst_superpositionTriple hV] at hux
    rw [margFst_superpositionOut hV] at hu
    have hr : jointIid r n (z.1, z.2.2) ≤ exp (-(n * (entropy r - ε))) :=
      iidPMF_le_of_mem_typicalSet huy
    have hlow := le_iidPMF_of_mem_typicalSet hu
    have hup := iidPMF_le_of_mem_typicalSet hux
    have hκ0 := (superpositionSeqKernel_isPMF hq z.1).nonneg z.2.1
    have hκ : superpositionSeqKernel q z.1 z.2.1 ≤
        exp (-(n * (entropy q - ε))) * exp (n * (entropy (margFst q) + ε)) := by
      have e : exp (-(n * (entropy (margFst q) + ε))) *
          exp (n * (entropy (margFst q) + ε)) = 1 := by
        rw [← exp_add, neg_add_cancel, exp_zero]
      have h2 : superpositionSeqKernel q z.1 z.2.1 * exp (-(n * (entropy (margFst q) + ε))) ≤
          exp (-(n * (entropy q - ε))) := by
        calc _ ≤ superpositionSeqKernel q z.1 z.2.1 * iidPMF (margFst q) n z.1 :=
              mul_le_mul_of_nonneg_left hlow hκ0
          _ = jointIid q n (z.1, z.2.1) := by
              rw [mul_comm, iidPMF_mul_superpositionSeqKernel hq]
          _ ≤ _ := hup
      calc superpositionSeqKernel q z.1 z.2.1
          = superpositionSeqKernel q z.1 z.2.1 * exp (-(n * (entropy (margFst q) + ε))) *
              exp (n * (entropy (margFst q) + ε)) := by rw [mul_assoc, e, mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 (exp_pos _).le
    exact mul_le_mul hr hκ hκ0 (exp_pos _).le
  -- The number of typical triples.
  have hcard : (#T : ℝ) ≤ exp (n * (entropy t + ε)) := by
    refine le_trans ?_ (card_jointTypicalSet_le (superpositionTriple_isPMF hq hV) n ε)
    have : #T ≤ #(jointTypicalSet t n ε) := by
      refine card_le_card_of_injOn (fun z => (zipSeq z.1 z.2.1, z.2.2)) (fun z hz => ?_) ?_
      · simp only [T, superpositionTypicalSet, coe_filter, mem_univ, true_and,
          Set.mem_ofPred_eq] at hz
        exact hz.1
      · intro a _ b _ h
        simp only [Prod.mk.injEq] at h
        have h' := @zipSeq_injective _ _ n (a.1, a.2.1) (b.1, b.2.1) h.1
        simp only [Prod.mk.injEq] at h'
        exact Prod.ext h'.1 (Prod.ext h'.2 h.2)
    exact_mod_cast this
  rw [h1]
  calc _ ≤ ∑ _z ∈ T, B := sum_le_sum hpt
    _ = #T * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ exp (n * (entropy t + ε)) * B := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
        simp only [B, superpositionInfoCond, ← exp_add]
        congr 1
        ring

open Classical in
/-- **Event `E₁₃` of Lecture 5.** A satellite codeword of a wrong cloud center, which together
with its cloud center is independent of the output, is typical with the output with probability
at most `e^{-n(I(U, X; Y) - 3ε)}`. -/
lemma sum_superposition_wrongCloud_le (hq : IsPMF q) (hV : IsChannel V) (n : ℕ) (ε : ℝ) :
    ∑ u, ∑ x, ∑ u', ∑ x', jointIid q n (u, x) * jointIid q n (u', x') *
        ∑ y, channelExt V n x y * (if (u', x', y) ∈ superpositionTypicalSet q V n ε then 1 else 0)
      ≤ exp (-(n * (I[Prod.fst : Prod.snd ; superpositionTriple q V] - 3 * ε))) := by
  set t := superpositionTriple q V
  set J := jointTypicalSet t n ε
  have hmt : margFst t = q := margFst_superpositionTriple hV
  calc _ ≤ ∑ u, ∑ x, ∑ u', ∑ x', ∑ y, jointIid t n (zipSeq u x, y) *
        iidPMF (margFst t) n (zipSeq u' x') * (if (zipSeq u' x', y) ∈ J then 1 else 0) := by
        refine sum_le_sum fun u _ => sum_le_sum fun x _ => sum_le_sum fun u' _ =>
          sum_le_sum fun x' _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun y _ => ?_
        rw [hmt]
        have hle : (if (u', x', y) ∈ superpositionTypicalSet q V n ε then (1 : ℝ) else 0) ≤
            if (zipSeq u' x', y) ∈ J then 1 else 0 := by
          by_cases h : (u', x', y) ∈ superpositionTypicalSet q V n ε
          · have hJ : (zipSeq u' x', y) ∈ J := by
              simp only [superpositionTypicalSet, mem_filter, mem_univ, true_and] at h
              exact h.1
            simp only [h, hJ, ↓reduceIte, le_refl]
          · simp only [h, ↓reduceIte]
            split_ifs <;> norm_num
        rw [← jointIid_mul_channelExt_eq_triple]
        have h0 : 0 ≤ jointIid q n (u, x) * channelExt V n x y * iidPMF q n (zipSeq u' x') :=
          mul_nonneg (mul_nonneg (jointIid_nonneg hq.nonneg n _) (channelExt_nonneg hV _ _))
            (iidPMF_nonneg hq.nonneg _)
        calc jointIid q n (u, x) * jointIid q n (u', x') *
              (channelExt V n x y * if (u', x', y) ∈ superpositionTypicalSet q V n ε then 1 else 0)
            = jointIid q n (u, x) * channelExt V n x y * iidPMF q n (zipSeq u' x') *
                (if (u', x', y) ∈ superpositionTypicalSet q V n ε then 1 else 0) := by
              simp only [jointIid]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hle h0
    _ = ∑ w, ∑ w', ∑ y, jointIid t n (w, y) * iidPMF (margFst t) n w' *
          (if (w', y) ∈ J then 1 else 0) := by
        rw [← sum_zipSeq (fun w => ∑ w', ∑ y, jointIid t n (w, y) * iidPMF (margFst t) n w' *
          (if (w', y) ∈ J then 1 else 0))]
        refine sum_congr rfl fun u _ => sum_congr rfl fun x _ => ?_
        exact sum_zipSeq fun w' => ∑ y, jointIid t n (zipSeq u x, y) *
          iidPMF (margFst t) n w' * (if (w', y) ∈ J then 1 else 0)
    _ ≤ _ := sum_indep_typical_le (superpositionTriple_isPMF hq hV) n ε

open Classical in
/-- **Event `E₂₁` of Lecture 5.** The cloud center sent is not jointly typical with the output
with probability `1 - P{(Uⁿ, Yⁿ) ∈ A_ε^(n)}`, which tends to `0`. -/
lemma sum_superposition_cloudAtyp_eq (hq : IsPMF q) (hV : IsChannel V) (n : ℕ) (ε : ℝ) :
    ∑ u, ∑ x, jointIid q n (u, x) * ∑ y, channelExt V n x y *
        (if (u, y) ∈ jointTypicalSet (superpositionOut q V) n ε then 0 else 1) =
      1 - prob (jointIid (superpositionOut q V) n)
        (jointTypicalSet (superpositionOut q V) n ε) := by
  rw [← sum_mul_ite_not_mem (jointIid_isPMF (superpositionOut_isPMF hq hV) n),
    Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_jointIid_mul_channelExt, sum_mul]
  exact sum_congr rfl fun x _ => by ring

open Classical in
/-- **Event `E₂₂` of Lecture 5.** A wrong cloud center, which is independent of the output, is
jointly typical with the output with probability at most `e^{-n(I(U; Y) - 3ε)}`. -/
lemma sum_superposition_cloudWrong_le (hq : IsPMF q) (hV : IsChannel V) (n : ℕ) (ε : ℝ) :
    ∑ u, ∑ x, ∑ u', ∑ x', jointIid q n (u, x) * jointIid q n (u', x') *
        ∑ y, channelExt V n x y *
          (if (u', y) ∈ jointTypicalSet (superpositionOut q V) n ε then 1 else 0) ≤
      exp (-(n * (I[Prod.fst : Prod.snd ; superpositionOut q V] - 3 * ε))) := by
  set r := superpositionOut q V
  set J := jointTypicalSet r n ε
  have hmr : margFst r = margFst q := margFst_superpositionOut hV
  have hx' : ∀ u' : Fin n → 𝒰, ∑ x', jointIid q n (u', x') = iidPMF (margFst q) n u' :=
    sum_jointIid_fiber_snd q n
  calc _ = ∑ u, ∑ u', ∑ y, jointIid r n (u, y) * iidPMF (margFst r) n u' *
        (if (u', y) ∈ J then 1 else 0) := by
        refine sum_congr rfl fun u _ => ?_
        calc _ = ∑ x, ∑ u', jointIid q n (u, x) * iidPMF (margFst q) n u' *
              ∑ y, channelExt V n x y * (if (u', y) ∈ J then 1 else 0) := by
              refine sum_congr rfl fun x _ => sum_congr rfl fun u' _ => ?_
              rw [← sum_mul, ← mul_sum, hx']
          _ = _ := by
              rw [sum_comm, hmr]
              refine sum_congr rfl fun u' _ => ?_
              simp only [mul_sum]
              rw [sum_comm]
              refine sum_congr rfl fun y _ => ?_
              rw [← sum_jointIid_mul_channelExt, sum_mul, sum_mul]
              exact sum_congr rfl fun x _ => by ring
    _ ≤ _ := sum_indep_typical_le (superpositionOut_isPMF hq hV) n ε

end InfoTheory
