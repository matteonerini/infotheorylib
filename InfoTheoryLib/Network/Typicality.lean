/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.Basic
public import InfoTheoryLib.ChannelCoding.JointTypicality

/-!
# Jointly typical sequences: conditional bounds

Section 15.2 extends joint typicality to collections of random variables. For a pair `(X, Y)`,
the jointly typical set of Chapter 7 already has the properties of Theorem 15.2.1 (its
probability tends to `1`, `tendsto_prob_jointTypicalSet`, and `|A_ε^(n)| ≤ e^{n(H(X,Y)+ε)}`,
`card_jointTypicalSet_le`). This file adds the conditional statements: for a jointly typical pair,
`p(xⁿ | yⁿ) ≐ e^{-nH(X|Y)}`, and for a fixed `yⁿ`, at most `e^{n(H(X|Y)+2ε)}` sequences `xⁿ` are
jointly typical with it (Theorem 15.2.2). It also records the entropies of `n` i.i.d. pairs.

## Main statements

* `entropy_jointIid`, `condEntropy_jointIid_fst`, `condEntropy_jointIid_snd`:
  `H(Xⁿ, Yⁿ) = n H(X, Y)` and `H(Xⁿ | Yⁿ) = n H(X | Y)` for i.i.d. pairs.
* `jointTypicalSet_condProb_bounds`: **Theorem 15.2.1 (4)**, (15.30).
* `card_fiber_jointTypicalSet_le`, `card_fiber_jointTypicalSet_le'`: **Theorem 15.2.2**,
  (15.38), (15.40)–(15.42), `|A_ε^(n)(X | yⁿ)| ≤ e^{n(H(X|Y)+2ε)}`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 15.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Entropies of i.i.d. pairs -/

omit [Fintype α] [Fintype β] in
lemma jointIid_eq_comp (q : α × β → ℝ) (n : ℕ) :
    jointIid q n =
      iidPMF q n ∘ (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => α) (fun _ => β)).symm :=
  rfl

/-- `H(Xⁿ, Yⁿ) = n H(X, Y)`. -/
theorem entropy_jointIid {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) :
    entropy (jointIid q n) = n * entropy q := by
  rw [jointIid_eq_comp, entropy_comp_equiv, entropy_iidPMF hq]

lemma dist_jointIid_fst (q : α × β → ℝ) (n : ℕ) :
    dist (jointIid q n) Prod.fst = iidPMF (margFst q) n := by
  classical
  funext x
  have h := sum_jointIid_fst q n fun x' => if x' = x then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [← h, dist]
  exact sum_congr rfl fun ω _ => by congr

lemma dist_jointIid_snd (q : α × β → ℝ) (n : ℕ) :
    dist (jointIid q n) Prod.snd = iidPMF (margSnd q) n := by
  classical
  funext y
  have h := sum_jointIid_snd q n fun y' => if y' = y then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [← h, dist]
  exact sum_congr rfl fun ω _ => by congr

/-- `∑_{xⁿ} p(xⁿ, yⁿ) = p(yⁿ)`. -/
lemma sum_jointIid_fiber_fst (q : α × β → ℝ) (n : ℕ) (y : Fin n → β) :
    ∑ x, jointIid q n (x, y) = iidPMF (margSnd q) n y := by
  rw [← dist_jointIid_snd, dist_snd]

/-- `H(X | Y) = H(X, Y) - H(Y)` for a joint pmf `q`. -/
lemma condEntropy_fst_snd_eq {q : α × β → ℝ} (hq : IsPMF q) :
    H[Prod.fst | Prod.snd ; q] = entropy q - entropy (margSnd q) := by
  rw [condEntropy_eq_sub hq]
  have e : H[pair (Prod.snd : α × β → β) Prod.fst ; q] = H[id ; q] :=
    entropyRV_eq_of_injective q Prod.swap Prod.swap_injective fun _ => rfl
  rw [e, entropyRV, entropyRV, dist_id]

/-- `H(Xⁿ | Yⁿ) = n H(X | Y)` for i.i.d. pairs. -/
theorem condEntropy_jointIid_fst {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) :
    H[Prod.fst | Prod.snd ; jointIid q n] = n * H[Prod.fst | Prod.snd ; q] := by
  rw [condEntropy_fst_snd_eq (jointIid_isPMF hq n), condEntropy_fst_snd_eq hq, margSnd,
    dist_jointIid_snd, entropy_jointIid hq, entropy_iidPMF (hq.dist _)]
  ring

/-- `H(Yⁿ | Xⁿ) = n H(Y | X)` for i.i.d. pairs. -/
theorem condEntropy_jointIid_snd {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) :
    H[Prod.snd | Prod.fst ; jointIid q n] = n * H[Prod.snd | Prod.fst ; q] := by
  rw [condEntropy_snd_fst_eq (jointIid_isPMF hq n), condEntropy_snd_fst_eq hq, margFst,
    dist_jointIid_fst, entropy_jointIid hq, entropy_iidPMF (hq.dist _)]
  ring

/-! ### Conditional typicality -/

/-- **Theorem 15.2.1 (4), (15.30).** For a jointly typical pair,
`e^{-n(H(X|Y)+2ε)} ≤ p(xⁿ | yⁿ) ≤ e^{-n(H(X|Y)-2ε)}`. -/
theorem jointTypicalSet_condProb_bounds {q : α × β → ℝ} (hq : IsPMF q) {n : ℕ} {ε : ℝ}
    {z : (Fin n → α) × (Fin n → β)} (hz : z ∈ jointTypicalSet q n ε) :
    exp (-(n * (H[Prod.fst | Prod.snd ; q] + 2 * ε))) * iidPMF (margSnd q) n z.2 ≤
        jointIid q n z ∧
      jointIid q n z ≤ exp (-(n * (H[Prod.fst | Prod.snd ; q] - 2 * ε))) *
        iidPMF (margSnd q) n z.2 := by
  obtain ⟨-, hy, hxy⟩ := mem_jointTypicalSet.1 hz
  obtain ⟨hy₁, hy₂⟩ := mem_typicalSet.1 hy
  obtain ⟨hxy₁, hxy₂⟩ := mem_typicalSet.1 hxy
  rw [condEntropy_fst_snd_eq hq]
  constructor
  · calc exp (-(n * (entropy q - entropy (margSnd q) + 2 * ε))) * iidPMF (margSnd q) n z.2
        ≤ exp (-(n * (entropy q - entropy (margSnd q) + 2 * ε))) *
            exp (-(n * (entropy (margSnd q) - ε))) :=
          mul_le_mul_of_nonneg_left hy₂ (exp_pos _).le
      _ = exp (-(n * (entropy q + ε))) := by rw [← exp_add]; congr 1; ring
      _ ≤ jointIid q n z := hxy₁
  · calc jointIid q n z ≤ exp (-(n * (entropy q - ε))) := hxy₂
      _ = exp (-(n * (entropy q - entropy (margSnd q) - 2 * ε))) *
            exp (-(n * (entropy (margSnd q) + ε))) := by rw [← exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hy₁ (exp_pos _).le

open Classical in
/-- **Theorem 15.2.2, (15.38), (15.40)–(15.42).** For a fixed `yⁿ`, the set `A_ε^(n)(X | yⁿ)` of
sequences `xⁿ` jointly typical with `yⁿ` has at most `e^{n(H(X|Y)+2ε)}` elements. -/
theorem card_fiber_jointTypicalSet_le {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) (ε : ℝ)
    (y : Fin n → β) :
    (#(univ.filter fun x => (x, y) ∈ jointTypicalSet q n ε) : ℝ) ≤
      exp (n * (H[Prod.fst | Prod.snd ; q] + 2 * ε)) := by
  set S := univ.filter fun x => (x, y) ∈ jointTypicalSet q n ε
  rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
  · rw [hS, card_empty, Nat.cast_zero]
    exact (exp_pos _).le
  have hy : y ∈ typicalSet (margSnd q) n ε :=
    (mem_jointTypicalSet.1 (mem_filter.1 hx₀).2).2.1
  have h1 : (#S : ℝ) * exp (-(n * (entropy q + ε))) ≤ ∑ x ∈ S, jointIid q n (x, y) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun x hx =>
      (mem_typicalSet.1 (mem_jointTypicalSet.1 (mem_filter.1 hx).2).2.2).1
  have h2 : ∑ x ∈ S, jointIid q n (x, y) ≤ iidPMF (margSnd q) n y := by
    rw [← sum_jointIid_fiber_fst]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
      jointIid_nonneg hq.nonneg n _
  have h3 := (mem_typicalSet.1 hy).2
  have h4 : exp (-(n * (entropy q + ε))) * exp (n * (H[Prod.fst | Prod.snd ; q] + 2 * ε)) =
      exp (-(n * (entropy (margSnd q) - ε))) := by
    rw [← exp_add, condEntropy_fst_snd_eq hq]
    congr 1
    ring
  have h5 := mul_le_mul_of_nonneg_right ((h1.trans h2).trans h3)
    (exp_pos (n * (H[Prod.fst | Prod.snd ; q] + 2 * ε))).le
  rw [mul_assoc, h4] at h5
  have := exp_pos (-(n * (entropy (margSnd q) - ε)))
  nlinarith

open Classical in
/-- **Theorem 15.2.2** with the roles exchanged: `|A_ε^(n)(Y | xⁿ)| ≤ e^{n(H(Y|X)+2ε)}`. -/
theorem card_fiber_jointTypicalSet_le' {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) (ε : ℝ)
    (x : Fin n → α) :
    (#(univ.filter fun y => (x, y) ∈ jointTypicalSet q n ε) : ℝ) ≤
      exp (n * (H[Prod.snd | Prod.fst ; q] + 2 * ε)) := by
  set S := univ.filter fun y => (x, y) ∈ jointTypicalSet q n ε
  rcases S.eq_empty_or_nonempty with hS | ⟨y₀, hy₀⟩
  · rw [hS, card_empty, Nat.cast_zero]
    exact (exp_pos _).le
  have hx : x ∈ typicalSet (margFst q) n ε :=
    (mem_jointTypicalSet.1 (mem_filter.1 hy₀).2).1
  have h1 : (#S : ℝ) * exp (-(n * (entropy q + ε))) ≤ ∑ y ∈ S, jointIid q n (x, y) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun y hy =>
      (mem_typicalSet.1 (mem_jointTypicalSet.1 (mem_filter.1 hy).2).2.2).1
  have h2 : ∑ y ∈ S, jointIid q n (x, y) ≤ iidPMF (margFst q) n x := by
    rw [← sum_jointIid_fiber_snd]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ =>
      jointIid_nonneg hq.nonneg n _
  have h3 := (mem_typicalSet.1 hx).2
  have h4 : exp (-(n * (entropy q + ε))) * exp (n * (H[Prod.snd | Prod.fst ; q] + 2 * ε)) =
      exp (-(n * (entropy (margFst q) - ε))) := by
    rw [← exp_add, condEntropy_snd_fst_eq hq]
    congr 1
    ring
  have h5 := mul_le_mul_of_nonneg_right ((h1.trans h2).trans h3)
    (exp_pos (n * (H[Prod.snd | Prod.fst ; q] + 2 * ε))).le
  rw [mul_assoc, h4] at h5
  have := exp_pos (-(n * (entropy (margFst q) - ε)))
  nlinarith

end InfoTheory
