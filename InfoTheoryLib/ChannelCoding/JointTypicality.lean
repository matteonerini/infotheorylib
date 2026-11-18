/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.TypicalSet
public import InfoTheoryLib.MutualInformation.Basic

/-!
# Jointly typical sequences

Let `q` be a joint pmf on `α × β` with marginals `p₁` and `p₂`. A pair of sequences
`(xⁿ, yⁿ)` is jointly typical if `xⁿ`, `yⁿ` and the sequence of pairs `((x₁, y₁), …, (xₙ, yₙ))`
are typical for `p₁`, `p₂` and `q`. For i.i.d. pairs the jointly typical set has probability
close to `1` and about `e^{nH(X,Y)}` elements. Two independent sequences with the right marginals
are jointly typical with probability about `e^{-nI(X;Y)}`. This is the joint AEP, the key to the
channel coding theorem.

Pairs of sequences are elements of `(Fin n → α) × (Fin n → β)`. Logarithms are natural.

## Main definitions

* `zipSeq x y`: the sequence of pairs `((x₁, y₁), …, (xₙ, yₙ))`.
* `jointIid q n`: the law `p(xⁿ, yⁿ) = ∏ᵢ q(xᵢ, yᵢ)` of `n` i.i.d. pairs, (7.38).
* `jointTypicalSet q n ε`: the jointly typical set `A_ε^(n)`, (7.35)–(7.37).

## Main statements

* `tendsto_prob_jointTypicalSet`: Theorem 7.6.1 (1), `Pr{A_ε^(n)} → 1`.
* `card_jointTypicalSet_le`: Theorem 7.6.1 (2), `|A_ε^(n)| ≤ e^{n(H(X,Y)+ε)}`.
* `prob_indep_jointTypicalSet_le`: Theorem 7.6.1 (3), (7.51)–(7.53), independent sequences are
  jointly typical with probability at most `e^{-n(I(X;Y)-3ε)}`.
* `eventually_prob_indep_jointTypicalSet_ge`: (7.57)–(7.59), and with probability at least
  `(1 - ε) e^{-n(I(X;Y)+3ε)}` for `n` large.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 7.6
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The sequence of pairs `((x₁, y₁), …, (xₙ, yₙ))`. -/
def zipSeq {n : ℕ} (x : Fin n → α) (y : Fin n → β) : Fin n → α × β := fun i => (x i, y i)

omit [Fintype α] [Fintype β] in
lemma zipSeq_injective (n : ℕ) :
    Function.Injective fun z : (Fin n → α) × (Fin n → β) => zipSeq z.1 z.2 := by
  intro z w h
  have h' := fun i => Prod.ext_iff.1 (congrFun h i)
  exact Prod.ext (funext fun i => (h' i).1) (funext fun i => (h' i).2)

/-- The first marginal `p₁(x) = ∑_y q(x, y)` of a joint pmf. -/
abbrev margFst (q : α × β → ℝ) : α → ℝ := dist q Prod.fst

/-- The second marginal `p₂(y) = ∑_x q(x, y)` of a joint pmf. -/
abbrev margSnd (q : α × β → ℝ) : β → ℝ := dist q Prod.snd

/-- **(7.38)** The law `p(xⁿ, yⁿ) = ∏ᵢ q(xᵢ, yᵢ)` of `n` i.i.d. pairs. -/
def jointIid (q : α × β → ℝ) (n : ℕ) (z : (Fin n → α) × (Fin n → β)) : ℝ :=
  iidPMF q n (zipSeq z.1 z.2)

omit [Fintype α] [Fintype β] in
lemma jointIid_nonneg {q : α × β → ℝ} (hq : ∀ z, 0 ≤ q z) (n : ℕ) (z) : 0 ≤ jointIid q n z :=
  iidPMF_nonneg hq _

/-- `∑_{yⁿ} p(xⁿ, yⁿ) = p(xⁿ)`. -/
lemma sum_jointIid_fiber_snd (q : α × β → ℝ) (n : ℕ) (x : Fin n → α) :
    ∑ y, jointIid q n (x, y) = iidPMF (margFst q) n x := by
  classical
  simp only [jointIid, iidPMF, zipSeq]
  rw [← Fintype.prod_sum fun i b => q (x i, b)]
  exact prod_congr rfl fun i _ => (dist_fst q (x i)).symm

/-- `H(Y | X) = H(X, Y) - H(X)` for a joint pmf `q`. -/
lemma condEntropy_snd_fst_eq {q : α × β → ℝ} (hq : IsPMF q) :
    H[Prod.snd | Prod.fst ; q] = entropy q - entropy (margFst q) := by
  rw [condEntropy_eq_sub hq, entropyRV, dist_pair_fst_snd, entropyRV]

/-- Sums against `jointIid` are sums against `iidPMF` on sequences of pairs. -/
lemma sum_jointIid (q : α × β → ℝ) (n : ℕ) (f : (Fin n → α × β) → ℝ) :
    ∑ z, jointIid q n z * f (zipSeq z.1 z.2) = ∑ w, iidPMF q n w * f w := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => α) (fun _ => β)).symm.sum_comp]
  rfl

/-- The first marginal of `n` i.i.d. pairs is `n` i.i.d. copies of the first marginal. -/
lemma sum_jointIid_fst (q : α × β → ℝ) (n : ℕ) (f : (Fin n → α) → ℝ) :
    ∑ z, jointIid q n z * f z.1 = ∑ x, iidPMF (margFst q) n x * f x := by
  classical
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  change ∑ y, jointIid q n (x, y) * f x = _
  rw [← sum_mul]
  congr 1
  simp only [jointIid, iidPMF, zipSeq]
  rw [← Fintype.prod_sum fun i b => q (x i, b)]
  exact prod_congr rfl fun i _ => (dist_fst q (x i)).symm

/-- The second marginal of `n` i.i.d. pairs is `n` i.i.d. copies of the second marginal. -/
lemma sum_jointIid_snd (q : α × β → ℝ) (n : ℕ) (f : (Fin n → β) → ℝ) :
    ∑ z, jointIid q n z * f z.2 = ∑ y, iidPMF (margSnd q) n y * f y := by
  classical
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  change ∑ x, jointIid q n (x, y) * f y = _
  rw [← sum_mul]
  congr 1
  simp only [jointIid, iidPMF, zipSeq]
  rw [← Fintype.prod_sum fun i a => q (a, y i)]
  refine prod_congr rfl fun i _ => ?_
  change _ = dist q Prod.snd (y i)
  rw [← sum_dist_pair_left q Prod.fst Prod.snd (y i)]
  simp [dist_pair_fst_snd]

lemma jointIid_isPMF {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) : IsPMF (jointIid q n) := by
  refine ⟨jointIid_nonneg hq.nonneg n, ?_⟩
  have h := sum_jointIid_fst q n fun _ => 1
  simp only [mul_one] at h
  rw [h]
  exact (iidPMF_isPMF (hq.dist Prod.fst) n).sum_eq_one

open Classical in
/-- **Definition (7.35)–(7.37).** The jointly typical set `A_ε^(n)`: the pairs `(xⁿ, yⁿ)` such that
`xⁿ`, `yⁿ` and `(xⁿ, yⁿ)` are typical for the marginals `p₁`, `p₂` and the joint pmf `q`. The
bounds are non-strict, `≤ ε` where the book has `< ε`; the theorems of Section 7.6 are proved for
this set. -/
def jointTypicalSet (q : α × β → ℝ) (n : ℕ) (ε : ℝ) : Finset ((Fin n → α) × (Fin n → β)) :=
  univ.filter fun z => z.1 ∈ typicalSet (margFst q) n ε ∧
    z.2 ∈ typicalSet (margSnd q) n ε ∧ zipSeq z.1 z.2 ∈ typicalSet q n ε

lemma mem_jointTypicalSet {q : α × β → ℝ} {n : ℕ} {ε : ℝ} {z : (Fin n → α) × (Fin n → β)} :
    z ∈ jointTypicalSet q n ε ↔ z.1 ∈ typicalSet (margFst q) n ε ∧
      z.2 ∈ typicalSet (margSnd q) n ε ∧ zipSeq z.1 z.2 ∈ typicalSet q n ε := by
  classical
  simp [jointTypicalSet]

/-- **Theorem 7.6.1 (1), (7.41)–(7.46).** For i.i.d. pairs, `Pr{(Xⁿ, Yⁿ) ∈ A_ε^(n)} → 1`. -/
theorem tendsto_prob_jointTypicalSet {q : α × β → ℝ} (hq : IsPMF q) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (jointIid q n) (jointTypicalSet q n ε)) atTop (𝓝 1) := by
  classical
  -- The probabilities of the three atypical events tend to `0`.
  have h₁ := tendsto_prob_typicalSet (hq.dist Prod.fst) hε
  have h₂ := tendsto_prob_typicalSet (hq.dist Prod.snd) hε
  have h₃ := tendsto_prob_typicalSet hq hε
  have hb : ∀ n, 1 - (1 - prob (iidPMF (margFst q) n) (typicalSet (margFst q) n ε)) -
      (1 - prob (iidPMF (margSnd q) n) (typicalSet (margSnd q) n ε)) -
        (1 - prob (iidPMF q n) (typicalSet q n ε)) ≤
        prob (jointIid q n) (jointTypicalSet q n ε) := by
    intro n
    have hpmf := jointIid_isPMF hq n
    -- The indicator of `A` is at least `1 - 1[x ∉ T₁] - 1[y ∉ T₂] - 1[(x, y) ∉ T]`.
    have key : ∀ z : (Fin n → α) × (Fin n → β),
        jointIid q n z * (1 - (if z.1 ∈ typicalSet (margFst q) n ε then 0 else 1) -
          (if z.2 ∈ typicalSet (margSnd q) n ε then 0 else 1) -
          (if zipSeq z.1 z.2 ∈ typicalSet q n ε then 0 else 1)) ≤
        if z ∈ jointTypicalSet q n ε then jointIid q n z else 0 := by
      intro z
      have h0 := hpmf.nonneg z
      simp only [mem_jointTypicalSet]
      by_cases a : z.1 ∈ typicalSet (margFst q) n ε <;>
        by_cases b : z.2 ∈ typicalSet (margSnd q) n ε <;>
        by_cases c : zipSeq z.1 z.2 ∈ typicalSet q n ε <;> simp [a, b, c] <;> linarith
    have e₁ : ∑ z, jointIid q n z * (if z.1 ∈ typicalSet (margFst q) n ε then 0 else 1) =
        1 - prob (iidPMF (margFst q) n) (typicalSet (margFst q) n ε) := by
      rw [sum_jointIid_fst q n fun x => if x ∈ typicalSet (margFst q) n ε then 0 else 1]
      have := prob_add_prob_compl (iidPMF_isPMF (hq.dist Prod.fst) n) (typicalSet (margFst q) n ε)
      simp only [prob, mul_ite, mul_zero, mul_one, sum_ite, sum_const_zero, zero_add] at this ⊢
      rw [filter_not, ← compl_eq_univ_sdiff, filter_mem_eq_inter, univ_inter]
      linarith
    have e₂ : ∑ z, jointIid q n z * (if z.2 ∈ typicalSet (margSnd q) n ε then 0 else 1) =
        1 - prob (iidPMF (margSnd q) n) (typicalSet (margSnd q) n ε) := by
      rw [sum_jointIid_snd q n fun y => if y ∈ typicalSet (margSnd q) n ε then 0 else 1]
      have := prob_add_prob_compl (iidPMF_isPMF (hq.dist Prod.snd) n) (typicalSet (margSnd q) n ε)
      simp only [prob, mul_ite, mul_zero, mul_one, sum_ite, sum_const_zero, zero_add] at this ⊢
      rw [filter_not, ← compl_eq_univ_sdiff, filter_mem_eq_inter, univ_inter]
      linarith
    have e₃ : ∑ z, jointIid q n z * (if zipSeq z.1 z.2 ∈ typicalSet q n ε then 0 else 1) =
        1 - prob (iidPMF q n) (typicalSet q n ε) := by
      rw [sum_jointIid q n fun w => if w ∈ typicalSet q n ε then 0 else 1]
      have := prob_add_prob_compl (iidPMF_isPMF hq n) (typicalSet q n ε)
      simp only [prob, mul_ite, mul_zero, mul_one, sum_ite, sum_const_zero, zero_add] at this ⊢
      rw [filter_not, ← compl_eq_univ_sdiff, filter_mem_eq_inter, univ_inter]
      linarith
    have hsum := sum_le_sum fun z (_ : z ∈ univ) => key z
    simp only [mul_sub, mul_one, sum_sub_distrib, hpmf.sum_eq_one, e₁, e₂, e₃] at hsum
    have hA : ∑ z, (if z ∈ jointTypicalSet q n ε then jointIid q n z else 0) =
        prob (jointIid q n) (jointTypicalSet q n ε) := by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter]
      rfl
    linarith
  have hlow : Tendsto (fun n => 1 - (1 - prob (iidPMF (margFst q) n) (typicalSet (margFst q) n ε)) -
      (1 - prob (iidPMF (margSnd q) n) (typicalSet (margSnd q) n ε)) -
      (1 - prob (iidPMF q n) (typicalSet q n ε))) atTop (𝓝 1) := by
    have c : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have := ((c.sub (c.sub h₁)).sub (c.sub h₂)).sub (c.sub h₃)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hb
    fun n => prob_le_one (jointIid_isPMF hq n) _

/-- **Theorem 7.6.1 (2), (7.47)–(7.50).** `|A_ε^(n)| ≤ e^{n(H(X,Y)+ε)}`. -/
theorem card_jointTypicalSet_le {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) (ε : ℝ) :
    ((jointTypicalSet q n ε).card : ℝ) ≤ exp (n * (entropy q + ε)) := by
  refine le_trans ?_ (card_typicalSet_le hq n ε)
  have : (jointTypicalSet q n ε).card ≤ (typicalSet q n ε).card :=
    card_le_card_of_injOn (fun z => zipSeq z.1 z.2)
      (fun z hz => (mem_jointTypicalSet.1 hz).2.2) (zipSeq_injective n).injOn
  exact_mod_cast this

lemma iidPMF_le_of_mem_typicalSet {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α}
    (hx : x ∈ typicalSet p n ε) : iidPMF p n x ≤ exp (-(n * (entropy p - ε))) :=
  (mem_typicalSet.1 hx).2

lemma le_iidPMF_of_mem_typicalSet {p : α → ℝ} {n : ℕ} {ε : ℝ} {x : Fin n → α}
    (hx : x ∈ typicalSet p n ε) : exp (-(n * (entropy p + ε))) ≤ iidPMF p n x :=
  (mem_typicalSet.1 hx).1

/-- `I(X; Y) = H(X) + H(Y) - H(X, Y)` for a joint pmf `q`. -/
lemma mutualInfo_fst_snd_eq {q : α × β → ℝ} (hq : IsPMF q) :
    I[Prod.fst : Prod.snd ; q] =
      entropy (margFst q) + entropy (margSnd q) - entropy q := by
  rw [mutualInfo_eq_add_sub hq, entropyRV, entropyRV, entropyRV, dist_pair_fst_snd]

/-- **Theorem 7.6.1 (3), (7.51)–(7.53).** If `X̃ⁿ` and `Ỹⁿ` are independent, with the same marginals
as `Xⁿ` and `Yⁿ`, then `Pr{(X̃ⁿ, Ỹⁿ) ∈ A_ε^(n)} ≤ e^{-n(I(X;Y)-3ε)}`. -/
theorem prob_indep_jointTypicalSet_le {q : α × β → ℝ} (hq : IsPMF q) (n : ℕ) (ε : ℝ) :
    ∑ z ∈ jointTypicalSet q n ε,
        iidPMF (margFst q) n z.1 * iidPMF (margSnd q) n z.2 ≤
      exp (-(n * (I[Prod.fst : Prod.snd ; q] - 3 * ε))) := by
  calc ∑ z ∈ jointTypicalSet q n ε,
        iidPMF (margFst q) n z.1 * iidPMF (margSnd q) n z.2
      ≤ ∑ _z ∈ jointTypicalSet q n ε,
          exp (-(n * (entropy (margFst q) - ε))) * exp (-(n * (entropy (margSnd q) - ε))) := by
        refine sum_le_sum fun z hz => ?_
        have hz := mem_jointTypicalSet.1 hz
        exact mul_le_mul (iidPMF_le_of_mem_typicalSet hz.1) (iidPMF_le_of_mem_typicalSet hz.2.1)
          (iidPMF_nonneg ((hq.dist _).nonneg) _) (exp_pos _).le
    _ = (jointTypicalSet q n ε).card *
          (exp (-(n * (entropy (margFst q) - ε))) * exp (-(n * (entropy (margSnd q) - ε)))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ exp (n * (entropy q + ε)) *
          (exp (-(n * (entropy (margFst q) - ε))) * exp (-(n * (entropy (margSnd q) - ε)))) :=
        mul_le_mul_of_nonneg_right (card_jointTypicalSet_le hq n ε) (by positivity)
    _ = exp (-(n * (I[Prod.fst : Prod.snd ; q] - 3 * ε))) := by
        rw [mutualInfo_fst_snd_eq hq, ← exp_add, ← exp_add]
        congr 1
        ring

/-- **(7.54)–(7.56), (7.57)–(7.59).** For `n` sufficiently large, independent `X̃ⁿ` and `Ỹⁿ` with
the same marginals as `Xⁿ` and `Yⁿ` are jointly typical with probability at least
`(1 - ε) e^{-n(I(X;Y)+3ε)}`. -/
theorem eventually_prob_indep_jointTypicalSet_ge {q : α × β → ℝ} (hq : IsPMF q) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 - ε) * exp (-(n * (I[Prod.fst : Prod.snd ; q] + 3 * ε))) ≤
      ∑ z ∈ jointTypicalSet q n ε,
        iidPMF (margFst q) n z.1 * iidPMF (margSnd q) n z.2 := by
  have hev := (tendsto_prob_jointTypicalSet hq hε).eventually
    (lt_mem_nhds (by linarith : 1 - ε < 1))
  filter_upwards [hev] with n hn
  -- `|A| ≥ (1 - ε) e^{n(H(X,Y)-ε)}`.
  have hcard : (1 - ε) * exp (n * (entropy q - ε)) ≤ (jointTypicalSet q n ε).card := by
    have h1 : prob (jointIid q n) (jointTypicalSet q n ε) ≤
        (jointTypicalSet q n ε).card * exp (-(n * (entropy q - ε))) :=
      prob_le_card_mul fun z hz => iidPMF_le_of_mem_typicalSet (mem_jointTypicalSet.1 hz).2.2
    have h2 : exp (-(n * (entropy q - ε))) * exp (n * (entropy q - ε)) = 1 := by
      rw [← exp_add, neg_add_cancel, exp_zero]
    calc (1 - ε) * exp (n * (entropy q - ε))
        ≤ (jointTypicalSet q n ε).card * exp (-(n * (entropy q - ε))) *
            exp (n * (entropy q - ε)) :=
          mul_le_mul_of_nonneg_right (hn.le.trans h1) (exp_pos _).le
      _ = (jointTypicalSet q n ε).card := by rw [mul_assoc, h2, mul_one]
  calc (1 - ε) * exp (-(n * (I[Prod.fst : Prod.snd ; q] + 3 * ε)))
      = (1 - ε) * exp (n * (entropy q - ε)) *
          (exp (-(n * (entropy (margFst q) + ε))) * exp (-(n * (entropy (margSnd q) + ε)))) := by
        rw [mutualInfo_fst_snd_eq hq, mul_assoc, ← exp_add, ← exp_add]
        congr 2
        ring
    _ ≤ (jointTypicalSet q n ε).card *
          (exp (-(n * (entropy (margFst q) + ε))) * exp (-(n * (entropy (margSnd q) + ε)))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ _z ∈ jointTypicalSet q n ε,
          exp (-(n * (entropy (margFst q) + ε))) * exp (-(n * (entropy (margSnd q) + ε))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine sum_le_sum fun z hz => ?_
        have hz := mem_jointTypicalSet.1 hz
        exact mul_le_mul (le_iidPMF_of_mem_typicalSet hz.1) (le_iidPMF_of_mem_typicalSet hz.2.1)
          (exp_pos _).le (iidPMF_nonneg ((hq.dist _).nonneg) _)

end InfoTheory
