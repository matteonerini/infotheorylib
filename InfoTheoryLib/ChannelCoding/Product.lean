/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Capacity

/-!
# Product channels

The product of two discrete memoryless channels `p(y₁|x₁)` and `p(y₂|x₂)` sends `x₁` and `x₂`
in parallel: `p(y₁, y₂|x₁, x₂) = p(y₁|x₁) p(y₂|x₂)`. Its capacity is the sum of the capacities.
For every input pmf `I(X₁, X₂; Y₁, Y₂) ≤ I(X₁; Y₁) + I(X₂; Y₂)`, because the output entropy is
subadditive and the conditional output entropy is additive; independent inputs achieve equality.

## Main definitions

* `prodChannel W₁ W₂`: the product channel.
* `piChannel W`: the product of `d` channels.

## Main statements

* `entropy_prodDist`: `H(p × q) = H(p) + H(q)`.
* `mutualInfoOf_prodChannel_le`: `I(X₁, X₂; Y₁, Y₂) ≤ I(X₁; Y₁) + I(X₂; Y₂)`.
* `mutualInfoOf_prodDist_prodChannel`: equality for independent inputs.
* `capacity_prodChannel`: **the product DMC (Lecture 3 of [elgamal2010])**, `C = C₁ + C₂`.
* `capacity_piChannel`: the same for `d` channels, `C = ∑ⱼ Cⱼ`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β α₁ α₂ β₁ β₂ : Type*} [Fintype α] [Fintype β] [Fintype α₁] [Fintype α₂]
  [Fintype β₁] [Fintype β₂]

/-- The entropy of a product pmf is the sum of the entropies: `H(p × q) = H(p) + H(q)`. -/
theorem entropy_prodDist {p : α → ℝ} {q : β → ℝ} (hp : IsPMF p) (hq : IsPMF q) :
    entropy (prodDist p q) = entropy p + entropy q := by
  simp only [entropy_eq_sum_negMulLog, prodDist, Fintype.sum_prod_type, negMulLog_mul,
    sum_add_distrib, ← mul_sum, ← sum_mul, hp.sum_eq_one, hq.sum_eq_one, one_mul]

/-- **Lecture 3 (product DMC).** The product `p(y₁, y₂|x₁, x₂) = p(y₁|x₁) p(y₂|x₂)` of two
channels. -/
def prodChannel (W₁ : α₁ → β₁ → ℝ) (W₂ : α₂ → β₂ → ℝ) : α₁ × α₂ → β₁ × β₂ → ℝ :=
  fun x y => W₁ x.1 y.1 * W₂ x.2 y.2

variable {W₁ : α₁ → β₁ → ℝ} {W₂ : α₂ → β₂ → ℝ}

omit [Fintype α₁] [Fintype α₂] in
lemma IsChannel.prod (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) :
    IsChannel (prodChannel W₁ W₂) := fun x => (h₁ x.1).prodDist (h₂ x.2)

/-- The first output of the product channel has the law of the output of `W₁` with the first
input. -/
lemma dist_outDist_prodChannel_fst (h₂ : IsChannel W₂) (p : α₁ × α₂ → ℝ) :
    dist (outDist p (prodChannel W₁ W₂)) Prod.fst = outDist (dist p Prod.fst) W₁ := by
  funext b₁
  rw [dist_fst]
  simp only [outDist, prodChannel]
  rw [sum_comm]
  simp_rw [← mul_sum, (h₂ _).sum_eq_one, mul_one]
  exact (sum_dist_mul p Prod.fst fun a => W₁ a b₁).symm

/-- The second output of the product channel has the law of the output of `W₂` with the second
input. -/
lemma dist_outDist_prodChannel_snd (h₁ : IsChannel W₁) (p : α₁ × α₂ → ℝ) :
    dist (outDist p (prodChannel W₁ W₂)) Prod.snd = outDist (dist p Prod.snd) W₂ := by
  funext b₂
  rw [dist_snd]
  simp only [outDist, prodChannel]
  rw [sum_comm]
  have key : ∀ x : α₁ × α₂, ∑ b₁, p x * (W₁ x.1 b₁ * W₂ x.2 b₂) = p x * W₂ x.2 b₂ := fun x => by
    simp_rw [show ∀ b₁, p x * (W₁ x.1 b₁ * W₂ x.2 b₂) = p x * W₂ x.2 b₂ * W₁ x.1 b₁ from
      fun _ => by ring]
    rw [← mul_sum, (h₁ _).sum_eq_one, mul_one]
  rw [sum_congr rfl fun x _ => key x]
  exact (sum_dist_mul p Prod.snd fun a => W₂ a b₂).symm

/-- **Lecture 3 (product DMC).** For every input pmf,
`I(X₁, X₂; Y₁, Y₂) ≤ I(X₁; Y₁) + I(X₂; Y₂)`. -/
theorem mutualInfoOf_prodChannel_le {p : α₁ × α₂ → ℝ} (hp : IsPMF p) (h₁ : IsChannel W₁)
    (h₂ : IsChannel W₂) :
    mutualInfoOf p (prodChannel W₁ W₂) ≤
      mutualInfoOf (dist p Prod.fst) W₁ + mutualInfoOf (dist p Prod.snd) W₂ := by
  have hW := h₁.prod h₂
  rw [mutualInfoOf_eq hp hW, mutualInfoOf_eq (hp.dist _) h₁, mutualInfoOf_eq (hp.dist _) h₂]
  -- The output entropy is subadditive.
  have hq := outDist_isPMF hp hW
  have hsub := entropyRV_pair_le_add hq (Prod.fst : β₁ × β₂ → β₁) Prod.snd
  rw [entropyRV, entropyRV, entropyRV, dist_pair_fst_snd, dist_outDist_prodChannel_fst h₂,
    dist_outDist_prodChannel_snd h₁] at hsub
  -- The conditional output entropy is additive.
  have hcond : ∑ x, p x * entropy (prodChannel W₁ W₂ x) =
      ∑ a, dist p Prod.fst a * entropy (W₁ a) + ∑ a, dist p Prod.snd a * entropy (W₂ a) := by
    rw [sum_dist_mul, sum_dist_mul, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [show prodChannel W₁ W₂ x = prodDist (W₁ x.1) (W₂ x.2) from rfl,
      entropy_prodDist (h₁ _) (h₂ _)]
    ring
  linarith

/-- **Lecture 3 (product DMC).** Independent inputs achieve
`I(X₁, X₂; Y₁, Y₂) = I(X₁; Y₁) + I(X₂; Y₂)`. -/
theorem mutualInfoOf_prodDist_prodChannel {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} (hp₁ : IsPMF p₁)
    (hp₂ : IsPMF p₂) (h₁ : IsChannel W₁) (h₂ : IsChannel W₂) :
    mutualInfoOf (prodDist p₁ p₂) (prodChannel W₁ W₂) =
      mutualInfoOf p₁ W₁ + mutualInfoOf p₂ W₂ := by
  have hW := h₁.prod h₂
  rw [mutualInfoOf_eq (hp₁.prodDist hp₂) hW, mutualInfoOf_eq hp₁ h₁, mutualInfoOf_eq hp₂ h₂]
  have hout : outDist (prodDist p₁ p₂) (prodChannel W₁ W₂) =
      prodDist (outDist p₁ W₁) (outDist p₂ W₂) := by
    funext y
    simp only [outDist, prodDist, prodChannel, Fintype.sum_prod_type, sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [hout, entropy_prodDist (outDist_isPMF hp₁ h₁) (outDist_isPMF hp₂ h₂)]
  have hcond : ∑ x, prodDist p₁ p₂ x * entropy (prodChannel W₁ W₂ x) =
      ∑ a, p₁ a * entropy (W₁ a) + ∑ a, p₂ a * entropy (W₂ a) := by
    have hrow : ∀ a b, entropy (prodChannel W₁ W₂ (a, b)) = entropy (W₁ a) + entropy (W₂ b) :=
      fun a b => entropy_prodDist (h₁ a) (h₂ b)
    simp only [prodDist, Fintype.sum_prod_type, hrow]
    have hinner : ∀ a, ∑ b, p₁ a * p₂ b * (entropy (W₁ a) + entropy (W₂ b)) =
        p₁ a * entropy (W₁ a) + p₁ a * ∑ b, p₂ b * entropy (W₂ b) := fun a => by
      calc ∑ b, p₁ a * p₂ b * (entropy (W₁ a) + entropy (W₂ b))
          = ∑ b, (p₁ a * entropy (W₁ a) * p₂ b + p₁ a * (p₂ b * entropy (W₂ b))) :=
            sum_congr rfl fun b _ => by ring
        _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hp₂.sum_eq_one, mul_one]
    rw [sum_congr rfl fun a _ => hinner a, sum_add_distrib, ← sum_mul, hp₁.sum_eq_one, one_mul]
  rw [hcond]
  ring

/-- **Lecture 3 (product DMC).** The capacity of the product of two discrete memoryless channels
is the sum of their capacities, `C = C₁ + C₂`. -/
theorem capacity_prodChannel [Nonempty α₁] [Nonempty α₂] (h₁ : IsChannel W₁)
    (h₂ : IsChannel W₂) : capacity (prodChannel W₁ W₂) = capacity W₁ + capacity W₂ := by
  refine le_antisymm (csSup_le (capacity_set_nonempty _) ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact (mutualInfoOf_prodChannel_le hp h₁ h₂).trans (add_le_add
      (mutualInfoOf_le_capacity (hp.dist _) h₁) (mutualInfoOf_le_capacity (hp.dist _) h₂))
  · obtain ⟨p₁, hp₁, e₁⟩ := exists_capacity_eq h₁
    obtain ⟨p₂, hp₂, e₂⟩ := exists_capacity_eq h₂
    rw [← e₁, ← e₂, ← mutualInfoOf_prodDist_prodChannel hp₁ hp₂ h₁ h₂]
    exact mutualInfoOf_le_capacity (hp₁.prodDist hp₂) (h₁.prod h₂)

section Relabel

variable {α α' β β' : Type*} [Fintype α] [Fintype α'] [Fintype β] [Fintype β']

/-- The capacity does not depend on the names of the inputs and of the outputs. -/
theorem capacity_comp_equiv (e : α' ≃ α) (e' : β' ≃ β) {W : α → β → ℝ} (hW : IsChannel W) :
    capacity (fun x y => W (e x) (e' y)) = capacity W := by
  have hW' : IsChannel fun x y => W (e x) (e' y) := fun x =>
    ⟨fun y => (hW _).nonneg _, by rw [e'.sum_comp (W (e x)), (hW _).sum_eq_one]⟩
  have key : ∀ {p : α → ℝ}, IsPMF p →
      mutualInfoOf (fun x => p (e x)) (fun x y => W (e x) (e' y)) = mutualInfoOf p W :=
      fun {p} hp => by
    have hp' : IsPMF fun x => p (e x) :=
      ⟨fun _ => hp.nonneg _, by rw [e.sum_comp p, hp.sum_eq_one]⟩
    rw [mutualInfoOf_eq hp' hW', mutualInfoOf_eq hp hW]
    congr 1
    · have ho : outDist (fun x => p (e x)) (fun x y => W (e x) (e' y)) = outDist p W ∘ e' := by
        funext y
        exact e.sum_comp fun a => p a * W a (e' y)
      rw [ho]
      exact entropy_comp_equiv e' _
    · refine (e.sum_comp fun a => p a * entropy (W a ∘ e')).trans ?_
      exact sum_congr rfl fun a _ => by rw [entropy_comp_equiv]
  unfold capacity
  congr 1
  ext c
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun a => p (e.symm a), ⟨fun _ => hp.nonneg _, by
      rw [e.symm.sum_comp p, hp.sum_eq_one]⟩, ?_⟩
    have h := key (p := fun a => p (e.symm a)) ⟨fun _ => hp.nonneg _, by
      rw [e.symm.sum_comp p, hp.sum_eq_one]⟩
    simp only [Equiv.symm_apply_apply] at h
    exact h.symm
  · rintro ⟨p, hp, rfl⟩
    exact ⟨fun x => p (e x), ⟨fun _ => hp.nonneg _, by rw [e.sum_comp p, hp.sum_eq_one]⟩, key hp⟩

end Relabel

section Pi

universe u v

/-- **Lecture 3 of [elgamal2010] (product DMC).** The product `∏ⱼ p(yⱼ | xⱼ)` of `d` channels. -/
def piChannel {d : ℕ} {α : Fin d → Type u} {β : Fin d → Type v} (W : ∀ i, α i → β i → ℝ) :
    (∀ i, α i) → (∀ i, β i) → ℝ :=
  fun x y => ∏ i, W i (x i) (y i)

/-- **Lecture 3 of [elgamal2010] (product DMC).** The capacity of the product of `d` discrete
memoryless channels is the sum of their capacities. -/
theorem capacity_piChannel : ∀ {d : ℕ} {α : Fin d → Type u} {β : Fin d → Type v}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Nonempty (α i)] {W : ∀ i, α i → β i → ℝ},
    (∀ i, IsChannel (W i)) → IsChannel (piChannel W) ∧
      capacity (piChannel W) = ∑ i, capacity (W i)
  | 0, α, β, _, _, _, W, _ => by
    have hC : IsChannel (piChannel W) := fun x => by
      refine ⟨fun y => by simp [piChannel], ?_⟩
      simp [piChannel]
    refine ⟨hC, le_antisymm ?_ (by simpa using capacity_nonneg hC)⟩
    simpa using capacity_le_log_card_input hC
  | d + 1, α, β, _, _, _, W, hW => by
    obtain ⟨hC, hc⟩ := capacity_piChannel (α := fun i => α i.succ) (β := fun i => β i.succ)
      (W := fun i => W i.succ) fun i => hW i.succ
    have hP := (hW 0).prod hC
    have heq : ∀ x y, piChannel W (Fin.consEquiv α x) (Fin.consEquiv β y) =
        prodChannel (W 0) (piChannel fun i => W i.succ) x y := fun x y => by
      simp [piChannel, prodChannel, Fin.prod_univ_succ, Fin.consEquiv]
    have hA : IsChannel (piChannel W) := fun x => by
      have hx : x = Fin.consEquiv α ((Fin.consEquiv α).symm x) := by simp
      rw [hx]
      refine ⟨fun y => ?_, ?_⟩
      · have hy : y = Fin.consEquiv β ((Fin.consEquiv β).symm y) := by simp
        rw [hy, heq]
        exact (hP _).nonneg _
      · rw [← (Fin.consEquiv β).sum_comp]
        simp only [heq]
        exact (hP _).sum_eq_one
    refine ⟨hA, ?_⟩
    rw [Fin.sum_univ_succ, ← hc, ← capacity_prodChannel (hW 0) hC,
      ← capacity_comp_equiv (Fin.consEquiv α) (Fin.consEquiv β) hA]
    congr 1
    funext x y
    exact heq x y

end Pi

end InfoTheory
