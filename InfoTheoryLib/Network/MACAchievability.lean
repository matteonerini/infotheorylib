/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.Network.MACCode
public import InfoTheoryLib.Network.MACRegion

/-!
# The multiple-access channel: achievability

Every rate pair in the pentagon `R₁ < I(X₁; Y | X₂)`, `R₂ < I(X₂; Y | X₁)`, `R₁ + R₂ < I(X₁, X₂; Y)`
of a product input distribution `p₁(x₁) p₂(x₂)` is achievable (Section 15.3.1). The two codebooks
are drawn independently, with i.i.d. symbols from `p₁` and `p₂`, and the receiver looks for the
unique pair of codewords jointly typical with the output. Given that `(1, 1)` was sent, an error
occurs if `(x₁(1), x₂(1), yⁿ)` is not typical, or if a pair `(i, j) ≠ (1, 1)` is typical: for
`i ≠ 1, j = 1` the codeword `x₁(i)` is independent of `(x₂(1), yⁿ)`, which gives the probability
`e^{-n(I(X₁; X₂, Y) - 3ε)} = e^{-n(I(X₁; Y | X₂) - 3ε)}`, (15.64)–(15.69), and similarly for the
two other cases.

The typical set of triples `(x₁ⁿ, x₂ⁿ, yⁿ)` is the intersection of the jointly typical sets of
Chapter 7 for the three groupings `((x₁, x₂), y)`, `(x₁, (x₂, y))` and `(x₂, (x₁, y))`, so that the
bounds of Theorem 7.6.1 apply directly to each error event.

## Main definitions

* `macJointA`, `macJointB`: the joint law of `(X₁, (X₂, Y))` and `(X₂, (X₁, Y))`.
* `macTypicalSet p₁ p₂ W n ε`: the typical triples.
* `macTypicalDecode`, `macTypicalCode`: joint typicality decoding.

## Main statements

* `mutualInfo_macJointA`, `mutualInfo_macJointB`: (15.68)–(15.69), `I(X₁; X₂, Y) = I(X₁; Y | X₂)`
  for independent inputs.
* `sum_codebook_macCondErrProb_le`: (15.62)–(15.72), the probability of error for a message pair,
  averaged over the random codebooks.
* `isAchievableMAC_of_mem_macRateRegion`: **Theorem 15.3.1 (achievability)** for a fixed product
  input distribution.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 15.3.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]

/-! ### Regrouping the triple -/

section Regroup

variable {Ω T : Type*} [Fintype Ω] [Finite T]

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma dist_equiv (μ : Ω → ℝ) (e : Ω ≃ T) (v : T) : dist μ e v = μ (e.symm v) := by
  classical
  have := Fintype.ofFinite T
  rw [dist, ← e.symm.sum_comp]
  simp

end Regroup

variable (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ)

/-- The joint law of `(X₁, (X₂, Y))`. -/
def macJointA : α₁ × (α₂ × β) → ℝ := fun z => macJoint p₁ p₂ W ((z.1, z.2.1), z.2.2)

/-- The joint law of `(X₂, (X₁, Y))`. -/
def macJointB : α₂ × (α₁ × β) → ℝ := fun z => macJoint p₁ p₂ W ((z.2.1, z.1), z.2.2)

/-- `((x₁, x₂), y) ↦ (x₁, (x₂, y))`. -/
def macEquivA : (α₁ × α₂) × β ≃ α₁ × (α₂ × β) := Equiv.prodAssoc _ _ _

/-- `((x₁, x₂), y) ↦ (x₂, (x₁, y))`. -/
def macEquivB : (α₁ × α₂) × β ≃ α₂ × (α₁ × β) :=
  (Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

lemma macJointA_eq : macJointA p₁ p₂ W = dist (macJoint p₁ p₂ W) (macEquivA (β := β)) := by
  funext z
  rw [dist_equiv]
  rfl

lemma macJointB_eq : macJointB p₁ p₂ W = dist (macJoint p₁ p₂ W) (macEquivB (β := β)) := by
  funext z
  rw [dist_equiv]
  rfl

variable {p₁ p₂ W}

lemma macJointA_isPMF (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    IsPMF (macJointA p₁ p₂ W) := by
  rw [macJointA_eq]
  exact (macJoint_isPMF hp₁ hp₂ hW).dist _

lemma macJointB_isPMF (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    IsPMF (macJointB p₁ p₂ W) := by
  rw [macJointB_eq]
  exact (macJoint_isPMF hp₁ hp₂ hW).dist _

lemma margFst_macJointA (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    margFst (macJointA p₁ p₂ W) = p₁ := by
  rw [margFst, macJointA_eq, ← dist_comp_eq]
  exact dist_macJoint_fst hp₂ hW

lemma margFst_macJointB (hp₁ : IsPMF p₁) (hW : IsChannel W) :
    margFst (macJointB p₁ p₂ W) = p₂ := by
  rw [margFst, macJointB_eq, ← dist_comp_eq]
  exact dist_macJoint_snd hp₁ hW

lemma margFst_macJoint (hW : IsChannel W) : margFst (macJoint p₁ p₂ W) = prodDist p₁ p₂ :=
  dist_macJoint_inputs hW

/-- **(15.68)–(15.69)** For independent inputs, `I(X₁; X₂, Y) = I(X₁; Y | X₂)`. -/
theorem mutualInfo_macJointA (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    I[Prod.fst : Prod.snd ; macJointA p₁ p₂ W] = macInfo₁ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  have h1 : I[Prod.fst : Prod.snd ; macJointA p₁ p₂ W] =
      I[fun z : (α₁ × α₂) × β => z.1.1 : fun z => (z.1.2, z.2) ; macJoint p₁ p₂ W] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd, macJointA_eq]
    rfl
  have h2 : I[fun z : (α₁ × α₂) × β => z.1.1 : fun z => (z.1.2, z.2) ; macJoint p₁ p₂ W] =
      I[fun z : (α₁ × α₂) × β => z.1.1 : pair Prod.snd (fun z => z.1.2) ; macJoint p₁ p₂ W] :=
    mutualInfo_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have h3 := chain_rule_mutualInfo₂ hμ (fun z : (α₁ × α₂) × β => z.1.1) Prod.snd
    (fun z => z.1.2)
  have h4 := mutualInfo_inputs_eq_zero hp₁ hp₂ hW
  rw [mutualInfo_comm hμ] at h4
  rw [h1, h2, h3, h4, zero_add]
  rfl

/-- `I(X₂; X₁, Y) = I(X₂; Y | X₁)` for independent inputs. -/
theorem mutualInfo_macJointB (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    I[Prod.fst : Prod.snd ; macJointB p₁ p₂ W] = macInfo₂ p₁ p₂ W := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  have h1 : I[Prod.fst : Prod.snd ; macJointB p₁ p₂ W] =
      I[fun z : (α₁ × α₂) × β => z.1.2 : fun z => (z.1.1, z.2) ; macJoint p₁ p₂ W] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd, macJointB_eq]
    rfl
  have h2 : I[fun z : (α₁ × α₂) × β => z.1.2 : fun z => (z.1.1, z.2) ; macJoint p₁ p₂ W] =
      I[fun z : (α₁ × α₂) × β => z.1.2 : pair Prod.snd (fun z => z.1.1) ; macJoint p₁ p₂ W] :=
    mutualInfo_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have h3 := chain_rule_mutualInfo₂ hμ (fun z : (α₁ × α₂) × β => z.1.2) Prod.snd
    (fun z => z.1.1)
  have h4 := mutualInfo_inputs_eq_zero hp₁ hp₂ hW
  rw [h1, h2, h3, h4, zero_add]
  rfl

/-! ### The law of the triple of sequences -/

variable (p₁ p₂ W) in
/-- The law `p₁(x₁ⁿ) p₂(x₂ⁿ) p(yⁿ | x₁ⁿ, x₂ⁿ)` of the codewords sent and the output. -/
def macLaw (n : ℕ) (z : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) : ℝ :=
  iidPMF p₁ n z.1 * iidPMF p₂ n z.2.1 * channelExt W n (zipSeq z.1 z.2.1) z.2.2

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma jointIid_macJoint {n : ℕ} (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (y : Fin n → β) :
    jointIid (macJoint p₁ p₂ W) n (zipSeq x₁ x₂, y) = macLaw p₁ p₂ W n (x₁, x₂, y) := by
  simp only [jointIid, macLaw, iidPMF, channelExt, macJoint, jointOf, prodDist, zipSeq,
    prod_mul_distrib]

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma jointIid_macJointA {n : ℕ} (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (y : Fin n → β) :
    jointIid (macJointA p₁ p₂ W) n (x₁, zipSeq x₂ y) = macLaw p₁ p₂ W n (x₁, x₂, y) := by
  simp only [jointIid, macLaw, iidPMF, channelExt, macJointA, macJoint, jointOf, prodDist,
    zipSeq, prod_mul_distrib]

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma jointIid_macJointB {n : ℕ} (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (y : Fin n → β) :
    jointIid (macJointB p₁ p₂ W) n (x₂, zipSeq x₁ y) = macLaw p₁ p₂ W n (x₁, x₂, y) := by
  simp only [jointIid, macLaw, iidPMF, channelExt, macJointB, macJoint, jointOf, prodDist,
    zipSeq, prod_mul_distrib]

omit [Fintype α₁] [Fintype α₂] in
lemma iidPMF_prodDist {n : ℕ} (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) :
    iidPMF (prodDist p₁ p₂) n (zipSeq x₁ x₂) = iidPMF p₁ n x₁ * iidPMF p₂ n x₂ := by
  simp only [iidPMF, prodDist, zipSeq, prod_mul_distrib]

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma sum_zipSeq {γ δ : Type*} [Fintype γ] [Fintype δ] {n : ℕ} (f : (Fin n → γ × δ) → ℝ) :
    ∑ x : Fin n → γ, ∑ y : Fin n → δ, f (zipSeq x y) = ∑ w, f w := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => γ) (fun _ => δ)).symm.sum_comp f

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma sum_mul_ite_not_mem {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (A : Finset Ω) :
    ∑ z, μ z * (if z ∈ A then 0 else 1) = 1 - prob μ A := by
  have h2 : ∑ z, μ z * (if z ∈ A then 0 else 1) = ∑ z, μ z - ∑ z, if z ∈ A then μ z else 0 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun z _ => by split_ifs <;> ring
  rw [h2, hμ.sum_eq_one, ← sum_filter, filter_mem_eq_inter, univ_inter]
  rfl

/-! ### Jointly typical triples -/

variable (p₁ p₂ W) in
open Classical in
/-- **(15.60)** The typical triples `(x₁ⁿ, x₂ⁿ, yⁿ)`: jointly typical for the three groupings
`((x₁, x₂), y)`, `(x₁, (x₂, y))` and `(x₂, (x₁, y))`. -/
def macTypicalSet (n : ℕ) (ε : ℝ) : Finset ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
  univ.filter fun z => (zipSeq z.1 z.2.1, z.2.2) ∈ jointTypicalSet (macJoint p₁ p₂ W) n ε ∧
    (z.1, zipSeq z.2.1 z.2.2) ∈ jointTypicalSet (macJointA p₁ p₂ W) n ε ∧
    (z.2.1, zipSeq z.1 z.2.2) ∈ jointTypicalSet (macJointB p₁ p₂ W) n ε

variable (p₁ p₂ W) in
/-- The probability that the triple sent is not typical is at most the sum of the probabilities
that its three groupings are not jointly typical. -/
def macAtypProb (n : ℕ) (ε : ℝ) : ℝ :=
  (1 - prob (jointIid (macJoint p₁ p₂ W) n) (jointTypicalSet (macJoint p₁ p₂ W) n ε)) +
    (1 - prob (jointIid (macJointA p₁ p₂ W) n) (jointTypicalSet (macJointA p₁ p₂ W) n ε)) +
    (1 - prob (jointIid (macJointB p₁ p₂ W) n) (jointTypicalSet (macJointB p₁ p₂ W) n ε))

/-- **(15.62)–(15.63)** `P(E₁₁ᶜ) → 0`: the triple sent is typical with probability tending to
`1`. -/
lemma tendsto_macAtypProb (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) {ε : ℝ}
    (hε : 0 < ε) : Tendsto (fun n => macAtypProb p₁ p₂ W n ε) atTop (𝓝 0) := by
  have c : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h₁ := c.sub (tendsto_prob_jointTypicalSet (macJoint_isPMF hp₁ hp₂ hW) hε)
  have h₂ := c.sub (tendsto_prob_jointTypicalSet (macJointA_isPMF hp₁ hp₂ hW) hε)
  have h₃ := c.sub (tendsto_prob_jointTypicalSet (macJointB_isPMF hp₁ hp₂ hW) hε)
  have h := (h₁.add h₂).add h₃
  rw [show (1 : ℝ) - 1 + (1 - 1) + (1 - 1) = 0 by norm_num] at h
  exact h

open Classical in
lemma ite_not_mem_macTypicalSet_le {n : ℕ} {ε : ℝ}
    (z : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :
    (if z ∈ macTypicalSet p₁ p₂ W n ε then (0 : ℝ) else 1) ≤
      (if (zipSeq z.1 z.2.1, z.2.2) ∈ jointTypicalSet (macJoint p₁ p₂ W) n ε then 0 else 1) +
        (if (z.1, zipSeq z.2.1 z.2.2) ∈ jointTypicalSet (macJointA p₁ p₂ W) n ε then 0 else 1) +
          (if (z.2.1, zipSeq z.1 z.2.2) ∈ jointTypicalSet (macJointB p₁ p₂ W) n ε then 0
            else 1) := by
  simp only [macTypicalSet, mem_filter, mem_univ, true_and]
  split_ifs <;> first | (exfalso; tauto) | norm_num

open Classical in
lemma sum_macLaw_not_mem_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (n : ℕ)
    (ε : ℝ) :
    ∑ z, macLaw p₁ p₂ W n z * (if z ∈ macTypicalSet p₁ p₂ W n ε then 0 else 1) ≤
      macAtypProb p₁ p₂ W n ε := by
  set q₃ := macJoint p₁ p₂ W
  set qA := macJointA p₁ p₂ W
  set qB := macJointB p₁ p₂ W
  set A₃ := jointTypicalSet q₃ n ε
  set AA := jointTypicalSet qA n ε
  set AB := jointTypicalSet qB n ε
  have hL : ∀ z, 0 ≤ macLaw p₁ p₂ W n z := fun z =>
    mul_nonneg (mul_nonneg (iidPMF_nonneg hp₁.nonneg _) (iidPMF_nonneg hp₂.nonneg _))
      (channelExt_nonneg hW _ _)
  have hpt : ∀ z : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β),
      (if z ∈ macTypicalSet p₁ p₂ W n ε then (0 : ℝ) else 1) ≤
        (if (zipSeq z.1 z.2.1, z.2.2) ∈ A₃ then 0 else 1) +
          (if (z.1, zipSeq z.2.1 z.2.2) ∈ AA then 0 else 1) +
            (if (z.2.1, zipSeq z.1 z.2.2) ∈ AB then 0 else 1) := by
    intro z
    exact ite_not_mem_macTypicalSet_le z
  have e₃ : ∑ z, macLaw p₁ p₂ W n z * (if (zipSeq z.1 z.2.1, z.2.2) ∈ A₃ then 0 else 1) =
      1 - prob (jointIid q₃ n) A₃ := by
    rw [← sum_mul_ite_not_mem (jointIid_isPMF (macJoint_isPMF hp₁ hp₂ hW) n), Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    simp_rw [← jointIid_macJoint]
    exact sum_zipSeq (fun u => ∑ y, jointIid q₃ n (u, y) * if (u, y) ∈ A₃ then 0 else 1)
  have eA : ∑ z, macLaw p₁ p₂ W n z * (if (z.1, zipSeq z.2.1 z.2.2) ∈ AA then 0 else 1) =
      1 - prob (jointIid qA n) AA := by
    rw [← sum_mul_ite_not_mem (jointIid_isPMF (macJointA_isPMF hp₁ hp₂ hW) n),
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine sum_congr rfl fun x₁ _ => ?_
    simp only [Fintype.sum_prod_type]
    simp_rw [← jointIid_macJointA]
    exact sum_zipSeq (fun v => jointIid qA n (x₁, v) * if (x₁, v) ∈ AA then 0 else 1)
  have eB : ∑ z, macLaw p₁ p₂ W n z * (if (z.2.1, zipSeq z.1 z.2.2) ∈ AB then 0 else 1) =
      1 - prob (jointIid qB n) AB := by
    rw [← sum_mul_ite_not_mem (jointIid_isPMF (macJointB_isPMF hp₁ hp₂ hW) n),
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    simp_rw [← jointIid_macJointB]
    rw [sum_comm]
    refine sum_congr rfl fun x₂ _ => ?_
    exact sum_zipSeq (fun v => jointIid qB n (x₂, v) * if (x₂, v) ∈ AB then 0 else 1)
  calc ∑ z, macLaw p₁ p₂ W n z * (if z ∈ macTypicalSet p₁ p₂ W n ε then 0 else 1)
      ≤ ∑ z, (macLaw p₁ p₂ W n z * (if (zipSeq z.1 z.2.1, z.2.2) ∈ A₃ then 0 else 1) +
          macLaw p₁ p₂ W n z * (if (z.1, zipSeq z.2.1 z.2.2) ∈ AA then 0 else 1) +
          macLaw p₁ p₂ W n z * (if (z.2.1, zipSeq z.1 z.2.2) ∈ AB then 0 else 1)) :=
        sum_le_sum fun z _ => by
          rw [← mul_add, ← mul_add]
          exact mul_le_mul_of_nonneg_left (hpt z) (hL z)
    _ = macAtypProb p₁ p₂ W n ε := by
        rw [sum_add_distrib, sum_add_distrib, e₃, eA, eB]
        rfl

/-- **Theorem 7.6.1 (3), rearranged.** If `X'ⁿ` is independent of `(Xⁿ, Vⁿ)`, with the law of `Xⁿ`,
then `Pr{(X'ⁿ, Vⁿ) ∈ A_ε^(n)} ≤ e^{-n(I(X; V) - 3ε)}`. -/
lemma sum_indep_typical_le {γ δ : Type*} [Fintype γ] [Fintype δ] {q : γ × δ → ℝ} (hq : IsPMF q)
    (n : ℕ) (ε : ℝ) [DecidableEq ((Fin n → γ) × (Fin n → δ))] :
    ∑ x, ∑ x', ∑ v, jointIid q n (x, v) * iidPMF (margFst q) n x' *
        (if (x', v) ∈ jointTypicalSet q n ε then 1 else 0) ≤
      exp (-(n * (I[Prod.fst : Prod.snd ; q] - 3 * ε))) := by
  set A := jointTypicalSet q n ε
  have h1 : ∑ x, ∑ x', ∑ v, jointIid q n (x, v) * iidPMF (margFst q) n x' *
      (if (x', v) ∈ A then 1 else 0) =
      ∑ z ∈ A, iidPMF (margFst q) n z.1 * iidPMF (margSnd q) n z.2 := by
    rw [sum_comm]
    have : ∀ g : (Fin n → γ) × (Fin n → δ) → ℝ, ∑ z ∈ A, g z = ∑ z, if z ∈ A then g z else 0 :=
      fun g => by rw [sum_ite_mem, univ_inter]
    rw [this, Fintype.sum_prod_type]
    refine sum_congr rfl fun x' _ => ?_
    have h := sum_jointIid_snd q n fun v =>
      iidPMF (margFst q) n x' * if (x', v) ∈ A then 1 else 0
    rw [Fintype.sum_prod_type] at h
    calc ∑ x, ∑ v, jointIid q n (x, v) * iidPMF (margFst q) n x' * (if (x', v) ∈ A then 1 else 0)
        = ∑ x, ∑ v, jointIid q n (x, v) *
            (iidPMF (margFst q) n x' * if (x', v) ∈ A then 1 else 0) := by simp only [mul_assoc]
      _ = ∑ v, iidPMF (margSnd q) n v * (iidPMF (margFst q) n x' * if (x', v) ∈ A then 1 else 0) :=
          h
      _ = _ := sum_congr rfl fun v _ => by split_ifs <;> ring
  rw [h1]
  exact prob_indep_jointTypicalSet_le hq n ε

/-! ### Two independent random codebooks -/

section Codebook

variable {X Y : Type*} [Fintype X] [Fintype Y] {μ₁ : X → ℝ} {μ₂ : Y → ℝ} {M₁ M₂ : ℕ}

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma sum_codebook_eval (hμ₁ : IsPMF μ₁) (hμ₂ : IsPMF μ₂) (i : Fin M₁) (j : Fin M₂)
    (f : X → Y → ℝ) :
    ∑ C₁ : Fin M₁ → X, ∑ C₂ : Fin M₂ → Y, iidPMF μ₁ M₁ C₁ * iidPMF μ₂ M₂ C₂ * f (C₁ i) (C₂ j) =
      ∑ x, ∑ y, μ₁ x * μ₂ y * f x y := by
  calc _ = ∑ C₁ : Fin M₁ → X, iidPMF μ₁ M₁ C₁ * ∑ y, μ₂ y * f (C₁ i) y :=
        sum_congr rfl fun C₁ _ => by
          rw [← sum_iidPMF_eval hμ₂ j (f (C₁ i)), mul_sum]
          exact sum_congr rfl fun _ _ => by ring
    _ = ∑ x, μ₁ x * ∑ y, μ₂ y * f x y := sum_iidPMF_eval hμ₁ i (fun x => ∑ y, μ₂ y * f x y)
    _ = _ := sum_congr rfl fun x _ => by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma sum_codebook_eval₂₁ (hμ₁ : IsPMF μ₁) (hμ₂ : IsPMF μ₂) {i i' : Fin M₁} (hi : i ≠ i')
    (j : Fin M₂) (f : X → X → Y → ℝ) :
    ∑ C₁ : Fin M₁ → X, ∑ C₂ : Fin M₂ → Y,
        iidPMF μ₁ M₁ C₁ * iidPMF μ₂ M₂ C₂ * f (C₁ i) (C₁ i') (C₂ j) =
      ∑ x, ∑ x', ∑ y, μ₁ x * μ₁ x' * μ₂ y * f x x' y := by
  calc _ = ∑ C₁ : Fin M₁ → X, iidPMF μ₁ M₁ C₁ * ∑ y, μ₂ y * f (C₁ i) (C₁ i') y :=
        sum_congr rfl fun C₁ _ => by
          rw [← sum_iidPMF_eval hμ₂ j (f (C₁ i) (C₁ i')), mul_sum]
          exact sum_congr rfl fun _ _ => by ring
    _ = ∑ x, ∑ x', μ₁ x * μ₁ x' * ∑ y, μ₂ y * f x x' y :=
        sum_iidPMF_eval₂ hμ₁ hi (fun x x' => ∑ y, μ₂ y * f x x' y)
    _ = _ := sum_congr rfl fun x _ => sum_congr rfl fun x' _ => by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma sum_codebook_eval₁₂ (hμ₁ : IsPMF μ₁) (hμ₂ : IsPMF μ₂) (i : Fin M₁) {j j' : Fin M₂}
    (hj : j ≠ j') (f : X → Y → Y → ℝ) :
    ∑ C₁ : Fin M₁ → X, ∑ C₂ : Fin M₂ → Y,
        iidPMF μ₁ M₁ C₁ * iidPMF μ₂ M₂ C₂ * f (C₁ i) (C₂ j) (C₂ j') =
      ∑ x, ∑ y, ∑ y', μ₁ x * μ₂ y * μ₂ y' * f x y y' := by
  calc _ = ∑ C₁ : Fin M₁ → X, iidPMF μ₁ M₁ C₁ * ∑ y, ∑ y', μ₂ y * μ₂ y' * f (C₁ i) y y' :=
        sum_congr rfl fun C₁ _ => by
          rw [← sum_iidPMF_eval₂ hμ₂ hj (f (C₁ i)), mul_sum]
          exact sum_congr rfl fun _ _ => by ring
    _ = ∑ x, μ₁ x * ∑ y, ∑ y', μ₂ y * μ₂ y' * f x y y' :=
        sum_iidPMF_eval hμ₁ i (fun x => ∑ y, ∑ y', μ₂ y * μ₂ y' * f x y y')
    _ = _ := sum_congr rfl fun x _ => by
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma sum_codebook_eval₂₂ (hμ₁ : IsPMF μ₁) (hμ₂ : IsPMF μ₂) {i i' : Fin M₁} (hi : i ≠ i')
    {j j' : Fin M₂} (hj : j ≠ j') (f : X → X → Y → Y → ℝ) :
    ∑ C₁ : Fin M₁ → X, ∑ C₂ : Fin M₂ → Y,
        iidPMF μ₁ M₁ C₁ * iidPMF μ₂ M₂ C₂ * f (C₁ i) (C₁ i') (C₂ j) (C₂ j') =
      ∑ x, ∑ x', ∑ y, ∑ y', μ₁ x * μ₁ x' * μ₂ y * μ₂ y' * f x x' y y' := by
  calc _ = ∑ C₁ : Fin M₁ → X, iidPMF μ₁ M₁ C₁ *
          ∑ y, ∑ y', μ₂ y * μ₂ y' * f (C₁ i) (C₁ i') y y' :=
        sum_congr rfl fun C₁ _ => by
          rw [← sum_iidPMF_eval₂ hμ₂ hj (f (C₁ i) (C₁ i')), mul_sum]
          exact sum_congr rfl fun _ _ => by ring
    _ = ∑ x, ∑ x', μ₁ x * μ₁ x' * ∑ y, ∑ y', μ₂ y * μ₂ y' * f x x' y y' :=
        sum_iidPMF_eval₂ hμ₁ hi (fun x x' => ∑ y, ∑ y', μ₂ y * μ₂ y' * f x x' y y')
    _ = _ := sum_congr rfl fun x _ => sum_congr rfl fun x' _ => by
        rw [mul_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring

end Codebook

/-! ### The three error events -/

open Classical in
/-- **(15.64)–(15.69)** A wrong codeword of sender 1 is typical with the right codeword of sender 2
and the output with probability at most `e^{-n(I(X₁; Y | X₂) - 3ε)}`. -/
lemma sum_error₁_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (n : ℕ) (ε : ℝ) :
    ∑ x₁, ∑ x₁', ∑ x₂, iidPMF p₁ n x₁ * iidPMF p₁ n x₁' * iidPMF p₂ n x₂ *
        ∑ y, channelExt W n (zipSeq x₁ x₂) y *
          (if (x₁', x₂, y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0) ≤
      exp (-(n * (macInfo₁ p₁ p₂ W - 3 * ε))) := by
  set qA := macJointA p₁ p₂ W
  set AA := jointTypicalSet qA n ε
  calc _ ≤ ∑ x₁, ∑ x₁', ∑ x₂, ∑ y, jointIid qA n (x₁, zipSeq x₂ y) * iidPMF (margFst qA) n x₁' *
        (if (x₁', zipSeq x₂ y) ∈ AA then 1 else 0) := by
        refine sum_le_sum fun x₁ _ => sum_le_sum fun x₁' _ => sum_le_sum fun x₂ _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun y _ => ?_
        rw [jointIid_macJointA, margFst_macJointA hp₂ hW]
        have hle : (if (x₁', x₂, y) ∈ macTypicalSet p₁ p₂ W n ε then (1 : ℝ) else 0) ≤
            if (x₁', zipSeq x₂ y) ∈ AA then 1 else 0 := by
          by_cases h : (x₁', x₂, y) ∈ macTypicalSet p₁ p₂ W n ε
          · have hA : (x₁', zipSeq x₂ y) ∈ AA := by
              simp only [macTypicalSet, mem_filter, mem_univ, true_and] at h
              exact h.2.1
            simp only [h, hA, ↓reduceIte, le_refl]
          · simp only [h, ↓reduceIte]
            split_ifs <;> norm_num
        have h0 : 0 ≤ iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * channelExt W n (zipSeq x₁ x₂) y *
            iidPMF p₁ n x₁' :=
          mul_nonneg (mul_nonneg (mul_nonneg (iidPMF_nonneg hp₁.nonneg _)
            (iidPMF_nonneg hp₂.nonneg _)) (channelExt_nonneg hW _ _)) (iidPMF_nonneg hp₁.nonneg _)
        calc iidPMF p₁ n x₁ * iidPMF p₁ n x₁' * iidPMF p₂ n x₂ *
              (channelExt W n (zipSeq x₁ x₂) y *
                if (x₁', x₂, y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0)
            = iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * channelExt W n (zipSeq x₁ x₂) y *
                iidPMF p₁ n x₁' * (if (x₁', x₂, y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hle h0
    _ = ∑ x₁, ∑ x₁', ∑ v, jointIid qA n (x₁, v) * iidPMF (margFst qA) n x₁' *
          (if (x₁', v) ∈ AA then 1 else 0) :=
        sum_congr rfl fun x₁ _ => sum_congr rfl fun x₁' _ =>
          sum_zipSeq fun v => jointIid qA n (x₁, v) * iidPMF (margFst qA) n x₁' *
            (if (x₁', v) ∈ AA then 1 else 0)
    _ ≤ _ := sum_indep_typical_le (macJointA_isPMF hp₁ hp₂ hW) n ε
    _ = _ := by rw [mutualInfo_macJointA hp₁ hp₂ hW]

open Classical in
/-- **(15.70)** A wrong codeword of sender 2 is typical with the right codeword of sender 1 and the
output with probability at most `e^{-n(I(X₂; Y | X₁) - 3ε)}`. -/
lemma sum_error₂_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (n : ℕ) (ε : ℝ) :
    ∑ x₁, ∑ x₂, ∑ x₂', iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * iidPMF p₂ n x₂' *
        ∑ y, channelExt W n (zipSeq x₁ x₂) y *
          (if (x₁, x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0) ≤
      exp (-(n * (macInfo₂ p₁ p₂ W - 3 * ε))) := by
  set qB := macJointB p₁ p₂ W
  set AB := jointTypicalSet qB n ε
  calc _ ≤ ∑ x₁, ∑ x₂, ∑ x₂', ∑ y, jointIid qB n (x₂, zipSeq x₁ y) * iidPMF (margFst qB) n x₂' *
        (if (x₂', zipSeq x₁ y) ∈ AB then 1 else 0) := by
        refine sum_le_sum fun x₁ _ => sum_le_sum fun x₂ _ => sum_le_sum fun x₂' _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun y _ => ?_
        rw [jointIid_macJointB, margFst_macJointB hp₁ hW]
        have hle : (if (x₁, x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then (1 : ℝ) else 0) ≤
            if (x₂', zipSeq x₁ y) ∈ AB then 1 else 0 := by
          by_cases h : (x₁, x₂', y) ∈ macTypicalSet p₁ p₂ W n ε
          · have hA : (x₂', zipSeq x₁ y) ∈ AB := by
              simp only [macTypicalSet, mem_filter, mem_univ, true_and] at h
              exact h.2.2
            simp only [h, hA, ↓reduceIte, le_refl]
          · simp only [h, ↓reduceIte]
            split_ifs <;> norm_num
        have h0 : 0 ≤ iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * channelExt W n (zipSeq x₁ x₂) y *
            iidPMF p₂ n x₂' :=
          mul_nonneg (mul_nonneg (mul_nonneg (iidPMF_nonneg hp₁.nonneg _)
            (iidPMF_nonneg hp₂.nonneg _)) (channelExt_nonneg hW _ _)) (iidPMF_nonneg hp₂.nonneg _)
        calc iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * iidPMF p₂ n x₂' *
              (channelExt W n (zipSeq x₁ x₂) y *
                if (x₁, x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0)
            = iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * channelExt W n (zipSeq x₁ x₂) y *
                iidPMF p₂ n x₂' * (if (x₁, x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hle h0
    _ = ∑ x₂, ∑ x₂', ∑ x₁, ∑ y, jointIid qB n (x₂, zipSeq x₁ y) * iidPMF (margFst qB) n x₂' *
          (if (x₂', zipSeq x₁ y) ∈ AB then 1 else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun x₂ _ => sum_comm
    _ = ∑ x₂, ∑ x₂', ∑ v, jointIid qB n (x₂, v) * iidPMF (margFst qB) n x₂' *
          (if (x₂', v) ∈ AB then 1 else 0) :=
        sum_congr rfl fun x₂ _ => sum_congr rfl fun x₂' _ =>
          sum_zipSeq fun v => jointIid qB n (x₂, v) * iidPMF (margFst qB) n x₂' *
            (if (x₂', v) ∈ AB then 1 else 0)
    _ ≤ _ := sum_indep_typical_le (macJointB_isPMF hp₁ hp₂ hW) n ε
    _ = _ := by rw [mutualInfo_macJointB hp₁ hp₂ hW]

open Classical in
/-- **(15.71)** A pair of wrong codewords is typical with the output with probability at most
`e^{-n(I(X₁, X₂; Y) - 3ε)}`. -/
lemma sum_error₁₂_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (n : ℕ) (ε : ℝ) :
    ∑ x₁, ∑ x₁', ∑ x₂, ∑ x₂', iidPMF p₁ n x₁ * iidPMF p₁ n x₁' * iidPMF p₂ n x₂ *
        iidPMF p₂ n x₂' * ∑ y, channelExt W n (zipSeq x₁ x₂) y *
          (if (x₁', x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0) ≤
      exp (-(n * (macInfo₁₂ p₁ p₂ W - 3 * ε))) := by
  set q₃ := macJoint p₁ p₂ W
  set A₃ := jointTypicalSet q₃ n ε
  calc _ ≤ ∑ x₁, ∑ x₁', ∑ x₂, ∑ x₂', ∑ y, jointIid q₃ n (zipSeq x₁ x₂, y) *
        iidPMF (margFst q₃) n (zipSeq x₁' x₂') *
        (if (zipSeq x₁' x₂', y) ∈ A₃ then 1 else 0) := by
        refine sum_le_sum fun x₁ _ => sum_le_sum fun x₁' _ => sum_le_sum fun x₂ _ =>
          sum_le_sum fun x₂' _ => ?_
        rw [mul_sum]
        refine sum_le_sum fun y _ => ?_
        rw [jointIid_macJoint, margFst_macJoint hW, iidPMF_prodDist]
        have hle : (if (x₁', x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then (1 : ℝ) else 0) ≤
            if (zipSeq x₁' x₂', y) ∈ A₃ then 1 else 0 := by
          by_cases h : (x₁', x₂', y) ∈ macTypicalSet p₁ p₂ W n ε
          · have hA : (zipSeq x₁' x₂', y) ∈ A₃ := by
              simp only [macTypicalSet, mem_filter, mem_univ, true_and] at h
              exact h.1
            simp only [h, hA, ↓reduceIte, le_refl]
          · simp only [h, ↓reduceIte]
            split_ifs <;> norm_num
        have h0 : 0 ≤ iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * channelExt W n (zipSeq x₁ x₂) y *
            (iidPMF p₁ n x₁' * iidPMF p₂ n x₂') :=
          mul_nonneg (mul_nonneg (mul_nonneg (iidPMF_nonneg hp₁.nonneg _)
            (iidPMF_nonneg hp₂.nonneg _)) (channelExt_nonneg hW _ _))
            (mul_nonneg (iidPMF_nonneg hp₁.nonneg _) (iidPMF_nonneg hp₂.nonneg _))
        calc iidPMF p₁ n x₁ * iidPMF p₁ n x₁' * iidPMF p₂ n x₂ * iidPMF p₂ n x₂' *
              (channelExt W n (zipSeq x₁ x₂) y *
                if (x₁', x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0)
            = iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * channelExt W n (zipSeq x₁ x₂) y *
                (iidPMF p₁ n x₁' * iidPMF p₂ n x₂') *
                (if (x₁', x₂', y) ∈ macTypicalSet p₁ p₂ W n ε then 1 else 0) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hle h0
    _ = ∑ x₁, ∑ x₂, ∑ x₁', ∑ x₂', ∑ y, jointIid q₃ n (zipSeq x₁ x₂, y) *
          iidPMF (margFst q₃) n (zipSeq x₁' x₂') *
          (if (zipSeq x₁' x₂', y) ∈ A₃ then 1 else 0) :=
        sum_congr rfl fun x₁ _ => sum_comm
    _ = ∑ u, ∑ u', ∑ y, jointIid q₃ n (u, y) * iidPMF (margFst q₃) n u' *
          (if (u', y) ∈ A₃ then 1 else 0) := by
        rw [← sum_zipSeq (fun u => ∑ u', ∑ y, jointIid q₃ n (u, y) * iidPMF (margFst q₃) n u' *
          (if (u', y) ∈ A₃ then 1 else 0))]
        refine sum_congr rfl fun x₁ _ => sum_congr rfl fun x₂ _ => ?_
        exact sum_zipSeq fun u' => ∑ y, jointIid q₃ n (zipSeq x₁ x₂, y) *
          iidPMF (margFst q₃) n u' * (if (u', y) ∈ A₃ then 1 else 0)
    _ ≤ _ := sum_indep_typical_le (macJoint_isPMF hp₁ hp₂ hW) n ε
    _ = _ := rfl

/-! ### Joint typicality decoding -/

open Classical in
/-- **(15.60)** Joint typicality decoding: declare `(i, j)` if `(x₁(i), x₂(j), yⁿ)` is the only
typical triple, and `d` otherwise. -/
def macTypicalDecode {n M₁ M₂ : ℕ} (T : Finset ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)))
    (C₁ : Fin M₁ → Fin n → α₁) (C₂ : Fin M₂ → Fin n → α₂) (d : Fin M₁ × Fin M₂)
    (y : Fin n → β) : Fin M₁ × Fin M₂ :=
  if h : ∃ w : Fin M₁ × Fin M₂, (C₁ w.1, C₂ w.2, y) ∈ T ∧
      ∀ w' : Fin M₁ × Fin M₂, (C₁ w'.1, C₂ w'.2, y) ∈ T → w' = w then h.choose else d

/-- The code with codebooks `C₁`, `C₂` and joint typicality decoding. -/
def macTypicalCode {n M₁ M₂ : ℕ} (T : Finset ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)))
    (C₁ : Fin M₁ → Fin n → α₁) (C₂ : Fin M₂ → Fin n → α₂) (d : Fin M₁ × Fin M₂) :
    MACCode M₁ M₂ n α₁ α₂ β :=
  ⟨C₁, C₂, macTypicalDecode T C₁ C₂ d⟩

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma macTypicalDecode_eq {n M₁ M₂ : ℕ} {T : Finset ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β))}
    {C₁ : Fin M₁ → Fin n → α₁} {C₂ : Fin M₂ → Fin n → α₂} (d : Fin M₁ × Fin M₂)
    {y : Fin n → β} {w : Fin M₁ × Fin M₂} (hw : (C₁ w.1, C₂ w.2, y) ∈ T)
    (huniq : ∀ w' : Fin M₁ × Fin M₂, (C₁ w'.1, C₂ w'.2, y) ∈ T → w' = w) :
    macTypicalDecode T C₁ C₂ d y = w := by
  have h : ∃ w : Fin M₁ × Fin M₂, (C₁ w.1, C₂ w.2, y) ∈ T ∧
      ∀ w' : Fin M₁ × Fin M₂, (C₁ w'.1, C₂ w'.2, y) ∈ T → w' = w := ⟨w, hw, huniq⟩
  unfold macTypicalDecode
  split
  · next h' => exact huniq _ h'.choose_spec.1
  · next h' => exact absurd h h'

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
open Classical in
/-- **(15.61)–(15.63)** A decoding error occurs only if the triple sent is not typical, or another
pair of codewords is typical with the output: with the first, the second or both codewords
wrong. -/
lemma macTypicalDecode_ne_le {n M₁ M₂ : ℕ}
    (T : Finset ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β))) (C₁ : Fin M₁ → Fin n → α₁)
    (C₂ : Fin M₂ → Fin n → α₂) (d : Fin M₁ × Fin M₂) (y : Fin n → β) (i : Fin M₁) (j : Fin M₂) :
    (if macTypicalDecode T C₁ C₂ d y ≠ (i, j) then (1 : ℝ) else 0) ≤
      (if (C₁ i, C₂ j, y) ∈ T then 0 else 1) +
        ∑ i' ∈ univ.erase i, (if (C₁ i', C₂ j, y) ∈ T then 1 else 0) +
        ∑ j' ∈ univ.erase j, (if (C₁ i, C₂ j', y) ∈ T then 1 else 0) +
        ∑ i' ∈ univ.erase i, ∑ j' ∈ univ.erase j, (if (C₁ i', C₂ j', y) ∈ T then 1 else 0) := by
  have hind : ∀ t : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β),
      0 ≤ (if t ∈ T then (1 : ℝ) else 0) := fun t => by split_ifs <;> norm_num
  have hS₁ := sum_nonneg fun i' (_ : i' ∈ univ.erase i) => hind (C₁ i', C₂ j, y)
  have hS₂ := sum_nonneg fun j' (_ : j' ∈ univ.erase j) => hind (C₁ i, C₂ j', y)
  have hS₃ := sum_nonneg fun i' (_ : i' ∈ univ.erase i) =>
    sum_nonneg fun j' (_ : j' ∈ univ.erase j) => hind (C₁ i', C₂ j', y)
  have h0 : 0 ≤ (if (C₁ i, C₂ j, y) ∈ T then (0 : ℝ) else 1) := by split_ifs <;> norm_num
  by_cases hd : macTypicalDecode T C₁ C₂ d y = (i, j)
  · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte]
    linarith
  simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases hw : (C₁ i, C₂ j, y) ∈ T
  swap
  · simp only [hw, ↓reduceIte]
    linarith
  obtain ⟨⟨i', j'⟩, hw', hne⟩ : ∃ w' : Fin M₁ × Fin M₂, (C₁ w'.1, C₂ w'.2, y) ∈ T ∧
      w' ≠ (i, j) := by
    by_contra hne
    push Not at hne
    exact hd (macTypicalDecode_eq (w := (i, j)) d hw hne)
  have hone : (1 : ℝ) ≤ if (C₁ i', C₂ j', y) ∈ T then 1 else 0 := by simp [hw']
  by_cases hi : i' = i
  · subst hi
    have hj : j' ≠ j := fun h => hne (by rw [h])
    have := single_le_sum (f := fun j' => if (C₁ i', C₂ j', y) ∈ T then (1 : ℝ) else 0)
      (fun j' _ => hind _) (mem_erase.2 ⟨hj, mem_univ j'⟩)
    simp only [hw, ↓reduceIte] at this ⊢
    linarith
  by_cases hj : j' = j
  · subst hj
    have := single_le_sum (f := fun i' => if (C₁ i', C₂ j', y) ∈ T then (1 : ℝ) else 0)
      (fun i' _ => hind _) (mem_erase.2 ⟨hi, mem_univ i'⟩)
    simp only [hw, ↓reduceIte] at this ⊢
    linarith
  have h1 := single_le_sum (f := fun j' => if (C₁ i', C₂ j', y) ∈ T then (1 : ℝ) else 0)
    (fun j' _ => hind _) (mem_erase.2 ⟨hj, mem_univ j'⟩)
  have h2 := single_le_sum (f := fun i' => ∑ j' ∈ univ.erase j,
      if (C₁ i', C₂ j', y) ∈ T then (1 : ℝ) else 0)
    (fun i' _ => sum_nonneg fun j' _ => hind _) (mem_erase.2 ⟨hi, mem_univ i'⟩)
  simp only [hw, ↓reduceIte] at h1 h2 ⊢
  linarith

/-! ### The random coding bound -/

open Classical in
/-- **(15.62)–(15.72)** Averaged over the random codebooks, the probability of error of joint
typicality decoding for the message pair `(i, j)` is at most
`P(E₁₁ᶜ) + (M₁ - 1) e^{-n(I₁ - 3ε)} + (M₂ - 1) e^{-n(I₂ - 3ε)} + (M₁ - 1)(M₂ - 1) e^{-n(I₃ - 3ε)}`.
-/
theorem sum_codebook_macCondErrProb_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W)
    {n M₁ M₂ : ℕ} (ε : ℝ) (d : Fin M₁ × Fin M₂) (i : Fin M₁) (j : Fin M₂) :
    ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
        iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ *
          (macTypicalCode (macTypicalSet p₁ p₂ W n ε) C₁ C₂ d).condErrProb W i j ≤
      macAtypProb p₁ p₂ W n ε + (M₁ - 1) * exp (-(n * (macInfo₁ p₁ p₂ W - 3 * ε))) +
        (M₂ - 1) * exp (-(n * (macInfo₂ p₁ p₂ W - 3 * ε))) +
        (M₁ - 1) * (M₂ - 1) * exp (-(n * (macInfo₁₂ p₁ p₂ W - 3 * ε))) := by
  set T := macTypicalSet p₁ p₂ W n ε
  set K : (Fin n → α₁) → (Fin n → α₂) → (Fin n → β) → ℝ :=
    fun x₁ x₂ y => channelExt W n (zipSeq x₁ x₂) y
  set T₁ : (Fin n → α₁) → (Fin n → α₂) → ℝ :=
    fun x₁ x₂ => ∑ y, K x₁ x₂ y * (if (x₁, x₂, y) ∈ T then 0 else 1)
  set T₂ : (Fin n → α₁) → (Fin n → α₁) → (Fin n → α₂) → ℝ :=
    fun x₁ x₁' x₂ => ∑ y, K x₁ x₂ y * (if (x₁', x₂, y) ∈ T then 1 else 0)
  set T₃ : (Fin n → α₁) → (Fin n → α₂) → (Fin n → α₂) → ℝ :=
    fun x₁ x₂ x₂' => ∑ y, K x₁ x₂ y * (if (x₁, x₂', y) ∈ T then 1 else 0)
  set T₄ : (Fin n → α₁) → (Fin n → α₁) → (Fin n → α₂) → (Fin n → α₂) → ℝ :=
    fun x₁ x₁' x₂ x₂' => ∑ y, K x₁ x₂ y * (if (x₁', x₂', y) ∈ T then 1 else 0)
  have hpn₁ := iidPMF_isPMF hp₁ n
  have hpn₂ := iidPMF_isPMF hp₂ n
  -- The error events, (15.62)–(15.63).
  have hlam : ∀ (C₁ : Fin M₁ → Fin n → α₁) (C₂ : Fin M₂ → Fin n → α₂),
      (macTypicalCode T C₁ C₂ d).condErrProb W i j ≤ T₁ (C₁ i) (C₂ j) +
        ∑ i' ∈ univ.erase i, T₂ (C₁ i) (C₁ i') (C₂ j) +
        ∑ j' ∈ univ.erase j, T₃ (C₁ i) (C₂ j) (C₂ j') +
        ∑ i' ∈ univ.erase i, ∑ j' ∈ univ.erase j, T₄ (C₁ i) (C₁ i') (C₂ j) (C₂ j') := by
    intro C₁ C₂
    have h2 : ∑ i' ∈ univ.erase i, T₂ (C₁ i) (C₁ i') (C₂ j) =
        ∑ y, K (C₁ i) (C₂ j) y * ∑ i' ∈ univ.erase i, (if (C₁ i', C₂ j, y) ∈ T then 1 else 0) := by
      simp only [T₂, mul_sum]
      exact sum_comm
    have h3 : ∑ j' ∈ univ.erase j, T₃ (C₁ i) (C₂ j) (C₂ j') =
        ∑ y, K (C₁ i) (C₂ j) y * ∑ j' ∈ univ.erase j, (if (C₁ i, C₂ j', y) ∈ T then 1 else 0) := by
      simp only [T₃, mul_sum]
      exact sum_comm
    have h4 : ∑ i' ∈ univ.erase i, ∑ j' ∈ univ.erase j, T₄ (C₁ i) (C₁ i') (C₂ j) (C₂ j') =
        ∑ y, K (C₁ i) (C₂ j) y * ∑ i' ∈ univ.erase i, ∑ j' ∈ univ.erase j,
          (if (C₁ i', C₂ j', y) ∈ T then 1 else 0) := by
      simp only [T₄, mul_sum]
      calc _ = ∑ i' ∈ univ.erase i, ∑ y, ∑ j' ∈ univ.erase j,
            K (C₁ i) (C₂ j) y * (if (C₁ i', C₂ j', y) ∈ T then (1 : ℝ) else 0) :=
            sum_congr rfl fun i' _ => sum_comm
        _ = _ := sum_comm
    rw [h2, h3, h4]
    simp only [T₁, ← sum_add_distrib, ← mul_add]
    refine sum_le_sum fun y _ => ?_
    have hK : 0 ≤ K (C₁ i) (C₂ j) y := channelExt_nonneg hW _ _
    have := mul_le_mul_of_nonneg_left (macTypicalDecode_ne_le T C₁ C₂ d y i j) hK
    rw [mul_ite, mul_one, mul_zero] at this
    exact this
  -- The four averages.
  have hT₁ : ∑ x₁, ∑ x₂, iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * T₁ x₁ x₂ ≤
      macAtypProb p₁ p₂ W n ε := by
    refine le_trans (le_of_eq ?_) (sum_macLaw_not_mem_le hp₁ hp₂ hW n ε)
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun x₁ _ => ?_
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun x₂ _ => ?_
    simp only [T₁, K, mul_sum, macLaw]
    exact sum_congr rfl fun y _ => by ring
  have hT₂ : ∀ i' ∈ univ.erase i, ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
      iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ * T₂ (C₁ i) (C₁ i') (C₂ j) ≤
        exp (-(n * (macInfo₁ p₁ p₂ W - 3 * ε))) := by
    intro i' hi'
    rw [sum_codebook_eval₂₁ hpn₁ hpn₂ (Ne.symm (ne_of_mem_erase hi')) j]
    exact sum_error₁_le hp₁ hp₂ hW n ε
  have hT₃ : ∀ j' ∈ univ.erase j, ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
      iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ * T₃ (C₁ i) (C₂ j) (C₂ j') ≤
        exp (-(n * (macInfo₂ p₁ p₂ W - 3 * ε))) := by
    intro j' hj'
    rw [sum_codebook_eval₁₂ hpn₁ hpn₂ i (Ne.symm (ne_of_mem_erase hj'))]
    exact sum_error₂_le hp₁ hp₂ hW n ε
  have hT₄ : ∀ i' ∈ univ.erase i, ∀ j' ∈ univ.erase j,
      ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
        iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ *
          T₄ (C₁ i) (C₁ i') (C₂ j) (C₂ j') ≤ exp (-(n * (macInfo₁₂ p₁ p₂ W - 3 * ε))) := by
    intro i' hi' j' hj'
    rw [sum_codebook_eval₂₂ hpn₁ hpn₂ (Ne.symm (ne_of_mem_erase hi'))
      (Ne.symm (ne_of_mem_erase hj'))]
    exact sum_error₁₂_le hp₁ hp₂ hW n ε
  have hw : ∀ (C₁ : Fin M₁ → Fin n → α₁) (C₂ : Fin M₂ → Fin n → α₂),
      0 ≤ iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ := fun C₁ C₂ =>
    mul_nonneg (iidPMF_nonneg hpn₁.nonneg _) (iidPMF_nonneg hpn₂.nonneg _)
  have hcard₁ : (#((univ : Finset (Fin M₁)).erase i) : ℝ) = M₁ - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos i).ne'), Nat.cast_one]
  have hcard₂ : (#((univ : Finset (Fin M₂)).erase j) : ℝ) = M₂ - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos j).ne'), Nat.cast_one]
  calc ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
        iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ *
          (macTypicalCode T C₁ C₂ d).condErrProb W i j
      ≤ ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
          iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ *
          (T₁ (C₁ i) (C₂ j) + ∑ i' ∈ univ.erase i, T₂ (C₁ i) (C₁ i') (C₂ j) +
            ∑ j' ∈ univ.erase j, T₃ (C₁ i) (C₂ j) (C₂ j') +
            ∑ i' ∈ univ.erase i, ∑ j' ∈ univ.erase j, T₄ (C₁ i) (C₁ i') (C₂ j) (C₂ j')) :=
        sum_le_sum fun C₁ _ => sum_le_sum fun C₂ _ =>
          mul_le_mul_of_nonneg_left (hlam C₁ C₂) (hw C₁ C₂)
    _ = ∑ x₁, ∑ x₂, iidPMF p₁ n x₁ * iidPMF p₂ n x₂ * T₁ x₁ x₂ +
          ∑ i' ∈ univ.erase i, (∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
            iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ *
              T₂ (C₁ i) (C₁ i') (C₂ j)) +
          ∑ j' ∈ univ.erase j, (∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
            iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ *
              T₃ (C₁ i) (C₂ j) (C₂ j')) +
          ∑ i' ∈ univ.erase i, ∑ j' ∈ univ.erase j, (∑ C₁ : Fin M₁ → Fin n → α₁,
            ∑ C₂ : Fin M₂ → Fin n → α₂, iidPMF (iidPMF p₁ n) M₁ C₁ *
              iidPMF (iidPMF p₂ n) M₂ C₂ * T₄ (C₁ i) (C₁ i') (C₂ j) (C₂ j')) := by
        have hpull : ∀ {ι : Type} (s : Finset ι)
            (f : (Fin M₁ → Fin n → α₁) → (Fin M₂ → Fin n → α₂) → ι → ℝ),
            ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
              iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ * ∑ k ∈ s, f C₁ C₂ k =
            ∑ k ∈ s, ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ C₂ : Fin M₂ → Fin n → α₂,
              iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ * f C₁ C₂ k := by
          intro ι s f
          simp only [mul_sum]
          calc _ = ∑ C₁ : Fin M₁ → Fin n → α₁, ∑ k ∈ s, ∑ C₂ : Fin M₂ → Fin n → α₂,
                iidPMF (iidPMF p₁ n) M₁ C₁ * iidPMF (iidPMF p₂ n) M₂ C₂ * f C₁ C₂ k :=
                sum_congr rfl fun C₁ _ => sum_comm
            _ = _ := sum_comm
        simp only [mul_add, sum_add_distrib]
        rw [sum_codebook_eval hpn₁ hpn₂ i j T₁, hpull, hpull, hpull]
        congr 1
        exact sum_congr rfl fun i' _ => hpull _ _
    _ ≤ macAtypProb p₁ p₂ W n ε +
          ∑ _i' ∈ univ.erase i, exp (-(n * (macInfo₁ p₁ p₂ W - 3 * ε))) +
          ∑ _j' ∈ univ.erase j, exp (-(n * (macInfo₂ p₁ p₂ W - 3 * ε))) +
          ∑ _i' ∈ univ.erase i, ∑ _j' ∈ univ.erase j,
            exp (-(n * (macInfo₁₂ p₁ p₂ W - 3 * ε))) :=
        add_le_add (add_le_add (add_le_add hT₁ (sum_le_sum hT₂)) (sum_le_sum hT₃))
          (sum_le_sum fun i' hi' => sum_le_sum (hT₄ i' hi'))
    _ = _ := by
        simp only [sum_const, nsmul_eq_mul, hcard₁, hcard₂]
        ring

/-- **(15.72)** For all `M₁, M₂ ≥ 1` and `ε`, some `((M₁, M₂), n)` code has average probability of
error at most `P(E₁₁ᶜ) + (M₁ - 1) e^{-n(I₁ - 3ε)} + (M₂ - 1) e^{-n(I₂ - 3ε)} +
(M₁ - 1)(M₂ - 1) e^{-n(I₃ - 3ε)}`. -/
theorem exists_macCode_avgErrProb_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W)
    {M₁ M₂ : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (n : ℕ) (ε : ℝ) :
    ∃ c : MACCode M₁ M₂ n α₁ α₂ β, c.avgErrProb W ≤
      macAtypProb p₁ p₂ W n ε + (M₁ - 1) * exp (-(n * (macInfo₁ p₁ p₂ W - 3 * ε))) +
        (M₂ - 1) * exp (-(n * (macInfo₂ p₁ p₂ W - 3 * ε))) +
        (M₁ - 1) * (M₂ - 1) * exp (-(n * (macInfo₁₂ p₁ p₂ W - 3 * ε))) := by
  set U := macAtypProb p₁ p₂ W n ε + (M₁ - 1) * exp (-(n * (macInfo₁ p₁ p₂ W - 3 * ε))) +
    (M₂ - 1) * exp (-(n * (macInfo₂ p₁ p₂ W - 3 * ε))) +
    (M₁ - 1) * (M₂ - 1) * exp (-(n * (macInfo₁₂ p₁ p₂ W - 3 * ε)))
  set μ := prodDist (iidPMF (iidPMF p₁ n) M₁) (iidPMF (iidPMF p₂ n) M₂)
  have hμ : IsPMF μ := (iidPMF_isPMF (iidPMF_isPMF hp₁ n) M₁).prodDist
    (iidPMF_isPMF (iidPMF_isPMF hp₂ n) M₂)
  set d : Fin M₁ × Fin M₂ := (⟨0, h₁⟩, ⟨0, h₂⟩)
  set code : (Fin M₁ → Fin n → α₁) × (Fin M₂ → Fin n → α₂) → MACCode M₁ M₂ n α₁ α₂ β :=
    fun C => macTypicalCode (macTypicalSet p₁ p₂ W n ε) C.1 C.2 d
  have hM : (0 : ℝ) < M₁ * M₂ := by positivity
  have hb : ∀ i j, ∑ C, μ C * (code C).condErrProb W i j ≤ U := fun i j => by
    rw [Fintype.sum_prod_type]
    exact sum_codebook_macCondErrProb_le hp₁ hp₂ hW ε d i j
  have h : ∑ C, μ C * (code C).avgErrProb W ≤ U := by
    have e : ∑ C, μ C * (code C).avgErrProb W =
        (∑ i, ∑ j, ∑ C, μ C * (code C).condErrProb W i j) / (M₁ * M₂) := by
      simp only [MACCode.avgErrProb, mul_div_assoc', ← sum_div, mul_sum]
      congr 1
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_comm
    rw [e, div_le_iff₀ hM]
    calc ∑ i, ∑ j, ∑ C, μ C * (code C).condErrProb W i j ≤ ∑ _i : Fin M₁, ∑ _j : Fin M₂, U :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => hb i j
      _ = U * (M₁ * M₂) := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hμ h
  exact ⟨code C, hC⟩

lemma mul_exp_neg_le {a r I ε : ℝ} {n : ℕ} (ha : a ≤ exp (n * r)) (h : r + 4 * ε ≤ I) :
    a * exp (-(n * (I - 3 * ε))) ≤ exp (-(n * ε)) := by
  calc a * exp (-(n * (I - 3 * ε))) ≤ exp (n * r) * exp (-(n * (I - 3 * ε))) :=
        mul_le_mul_of_nonneg_right ha (exp_pos _).le
    _ = exp (n * r + -(n * (I - 3 * ε))) := (exp_add _ _).symm
    _ ≤ exp (-(n * ε)) := exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

lemma ceil_exp_sub_one_le (x : ℝ) : ((⌈exp x⌉₊ : ℝ) - 1) ≤ exp x := by
  linarith [Nat.ceil_lt_add_one (exp_pos x).le]

/-- **Theorem 15.3.1 (achievability), Section 15.3.1.** For a product input distribution
`p₁(x₁) p₂(x₂)`, every rate pair with `R₁ < I(X₁; Y | X₂)`, `R₂ < I(X₂; Y | X₁)` and
`R₁ + R₂ < I(X₁, X₂; Y)` is achievable. -/
theorem isAchievableMAC_of_mem_macRateRegion [Nonempty α₁] [Nonempty α₂] (hp₁ : IsPMF p₁)
    (hp₂ : IsPMF p₂) (hW : IsChannel W) {R : ℝ × ℝ} (hR : R ∈ macRateRegion W p₁ p₂) :
    IsAchievableMAC W R.1 R.2 := by
  obtain ⟨hR₁, hR₂, hR₃⟩ := hR
  set A := macInfo₁ p₁ p₂ W - R.1
  set B := macInfo₂ p₁ p₂ W - R.2
  set C := macInfo₁₂ p₁ p₂ W - (R.1 + R.2)
  set ε := min (min A B) C / 4 with hε_def
  have hε : 0 < ε := by
    have := lt_min (lt_min (sub_pos.2 hR₁) (sub_pos.2 hR₂)) (sub_pos.2 hR₃)
    positivity
  have hε₁ : R.1 + 4 * ε ≤ macInfo₁ p₁ p₂ W := by
    have := (min_le_left (min A B) C).trans (min_le_left A B)
    linarith
  have hε₂ : R.2 + 4 * ε ≤ macInfo₂ p₁ p₂ W := by
    have := (min_le_left (min A B) C).trans (min_le_right A B)
    linarith
  have hε₃ : R.1 + R.2 + 4 * ε ≤ macInfo₁₂ p₁ p₂ W := by
    have := min_le_right (min A B) C
    linarith
  set P : ℕ → ℝ := fun n => macAtypProb p₁ p₂ W n ε + 3 * exp (-(n * ε))
  have hP : Tendsto P atTop (𝓝 0) := by
    have := (tendsto_macAtypProb hp₁ hp₂ hW hε).add ((tendsto_exp_neg_mul_nat hε).const_mul 3)
    simpa using this
  refine isAchievableMAC_of_forall_ge hW hP 0 fun n _ => ?_
  obtain ⟨c, hc⟩ := exists_macCode_avgErrProb_le hp₁ hp₂ hW (one_le_ceil_exp (n * R.1))
    (one_le_ceil_exp (n * R.2)) n ε
  refine ⟨c, hc.trans ?_⟩
  have h₁ := ceil_exp_sub_one_le (n * R.1)
  have h₂ := ceil_exp_sub_one_le (n * R.2)
  have h₁0 : (0 : ℝ) ≤ (⌈exp (n * R.1)⌉₊ : ℝ) - 1 := by
    have := one_le_ceil_exp (n * R.1)
    have : (1 : ℝ) ≤ ⌈exp (n * R.1)⌉₊ := by exact_mod_cast this
    linarith
  have h₂0 : (0 : ℝ) ≤ (⌈exp (n * R.2)⌉₊ : ℝ) - 1 := by
    have := one_le_ceil_exp (n * R.2)
    have : (1 : ℝ) ≤ ⌈exp (n * R.2)⌉₊ := by exact_mod_cast this
    linarith
  have h₁₂ : ((⌈exp (n * R.1)⌉₊ : ℝ) - 1) * ((⌈exp (n * R.2)⌉₊ : ℝ) - 1) ≤
      exp (n * (R.1 + R.2)) := by
    rw [mul_add, exp_add]
    exact mul_le_mul h₁ h₂ h₂0 (exp_pos _).le
  have e1 := mul_exp_neg_le h₁ hε₁
  have e2 := mul_exp_neg_le h₂ hε₂
  have e3 := mul_exp_neg_le h₁₂ hε₃
  simp only [P]
  linarith

end InfoTheory
