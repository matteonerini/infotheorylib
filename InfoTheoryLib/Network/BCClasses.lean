/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCBits
public import InfoTheoryLib.MarkovChain.DataProcessing
public import InfoTheoryLib.StochasticProcess.HiddenMarkov
public import InfoTheoryLib.Entropy.MrsGerber
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# Less noisy and more capable broadcast channels

Two classes of DM-BC `p(y₁, y₂ | x)` that are more general than the degraded ones, and for which
superposition coding is optimal. Receiver `Y₁` is less noisy than `Y₂` if `I(U; Y₁) ≥ I(U; Y₂)`
for every `p(u, x)`, and more capable than `Y₂` if `I(X; Y₁) ≥ I(X; Y₂)` for every `p(x)`.
A degraded DM-BC is less noisy, by the data processing inequality, and a less noisy DM-BC is more
capable, by taking `U = X`.

The converses fail, as shown by the example of Nair: `X ∈ {0, 1}`, `Y₁` the output of a BSC(`p`)
with `p ∈ [0, 1/2]` and `Y₂` the output of a BEC(`ε`). For `X ∼ Bern(a)`, we have
`I(X; Y₁) = H(a ∗ p) - H(p)` and `I(X; Y₂) = (1 - ε) H(a)`. Whether `Y₂` is less noisy than `Y₁` is
decided by `G(a) = H(a ∗ p) - (1 - ε) H(a)`: `I(U; Y₁) - I(U; Y₂)` is a Jensen gap of `G`, and
`G''(a)` has the sign of `(4p(1 - p) - ε) / 4 + ε (1 - 2p)² (a - 1/2)²`.

## Main definitions

* `IsLessNoisy W`, `IsMoreCapable W`: receiver `Y₁` is less noisy, more capable, than `Y₂`.
* `bcReceiverSwap W`: the DM-BC with the receivers exchanged, for statements about `Y₂` being the
  stronger receiver.
* `bscBecMarg₁ p`, `bscBecMarg₂ ε`, `bscBecBC p ε`: the BSC(`p`), the BEC(`ε`) and the DM-BC with
  these conditional marginals.

## Main statements

* `bcInfoUY₁_eq`, `bcInfoUY₂_eq`, `bcInfoXY₁_eq`, `bcInfoXY₂_eq`: the mutual informations only
  depend on `p(u, x)` and the conditional marginals.
* `IsPhysicallyDegraded.isLessNoisy`, `IsStochasticallyDegraded.isLessNoisy`,
  `IsLessNoisy.isMoreCapable`, `IsStochasticallyDegraded.isMoreCapable`: the implications between
  the classes.
* `mutualInfo_bernoulli_mixture`: for a binary input, `I(U; Y)` is a Jensen gap of the output
  entropy.
* `isStochasticallyDegraded_bcReceiverSwap_bscBecBC_iff`: `Y₁` is a degraded version of `Y₂` iff
  `ε ≤ 2p`.
* `isLessNoisy_bcReceiverSwap_bscBecBC_iff`: `Y₂` is less noisy than `Y₁` iff `ε ≤ 4p(1 - p)`.
* `isMoreCapable_bcReceiverSwap_bscBecBC_iff`: `Y₂` is more capable than `Y₁` iff `ε ≤ H(p)` in
  bits.
* `not_isMoreCapable_bscBecBC`: for `p > 0` and `ε < 1`, `Y₁` is not more capable than `Y₂`.
* `bscBecBC_case₁`, `bscBecBC_case₂`, `bscBecBC_case₃`, `bscBecBC_case₄`: the four cases of the
  example.

## Implementation notes

Entropies are in nats, so that `ε ≤ H(p)` in bits reads `ε * log 2 ≤ binEntropy p`.

Case 4 of the example in the notes, `H(p) < ε ≤ 1`, needs `ε < 1` and `p > 0`: if `ε = 1` or
`p = 0`, then `Y₂` is a degraded version of `Y₁`, see
`isStochasticallyDegraded_bscBecBC_of_eps_eq_one` and
`isStochasticallyDegraded_bscBecBC_of_p_eq_zero`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
* [C. Nair, *Capacity regions of two new classes of 2-receiver broadcast channels*][nair2009]
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂]

/-! ### The classes -/

/-- **Definition (Lecture 5 of [elgamal2010]).** A DM-BC is less noisy, or receiver `Y₁` is less
noisy than receiver `Y₂`, if `I(U; Y₁) ≥ I(U; Y₂)` for every `p(u, x)`. The auxiliary `U` takes
values in `Fin k` for some `k`. -/
def IsLessNoisy (W : α → β₁ × β₂ → ℝ) : Prop :=
  ∀ (k : ℕ) (q : Fin k × α → ℝ), IsPMF q → bcInfoUY₂ q W ≤ bcInfoUY₁ q W

/-- **Definition (Lecture 5 of [elgamal2010]).** A DM-BC is more capable, or receiver `Y₁` is more
capable than receiver `Y₂`, if `I(X; Y₁) ≥ I(X; Y₂)` for every `p(x)`. -/
def IsMoreCapable (W : α → β₁ × β₂ → ℝ) : Prop :=
  ∀ p : α → ℝ, IsPMF p → mutualInfoOf p (bcMarg₂ W) ≤ mutualInfoOf p (bcMarg₁ W)

/-- The DM-BC with the two receivers exchanged: `p'(y₂, y₁ | x) = p(y₁, y₂ | x)`. -/
def bcReceiverSwap (W : α → β₁ × β₂ → ℝ) : α → β₂ × β₁ → ℝ := fun x y => W x y.swap

omit [Fintype α] in
lemma IsChannel.bcReceiverSwap {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W) :
    IsChannel (bcReceiverSwap W) := fun x =>
  ⟨fun y => (hW x).nonneg _, by
    rw [← (hW x).sum_eq_one]
    exact Fintype.sum_equiv (Equiv.prodComm β₂ β₁) _ _ fun _ => rfl⟩

omit [Fintype α] [Fintype β₂] in
@[simp] lemma bcMarg₁_bcReceiverSwap (W : α → β₁ × β₂ → ℝ) :
    bcMarg₁ (bcReceiverSwap W) = bcMarg₂ W := rfl

omit [Fintype α] [Fintype β₁] in
@[simp] lemma bcMarg₂_bcReceiverSwap (W : α → β₁ × β₂ → ℝ) :
    bcMarg₂ (bcReceiverSwap W) = bcMarg₁ W := rfl

/-! ### Information quantities depend only on the conditional marginals -/

variable {𝒰 : Type*} [Fintype 𝒰]

lemma dist_bcJoint_UY₁ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) (u : 𝒰) (y : β₁) :
    dist (bcJoint q W) (pair (fun z => z.1.1) (fun z => z.2.1)) (u, y) =
      ∑ x, q (u, x) * bcMarg₁ W x y := by
  classical
  simp only [dist, bcJoint, jointOf, pair_apply, Prod.mk.injEq, Fintype.sum_prod_type, bcMarg₁,
    mul_sum, ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]

lemma dist_bcJoint_UY₂ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) (u : 𝒰) (y : β₂) :
    dist (bcJoint q W) (pair (fun z => z.1.1) (fun z => z.2.2)) (u, y) =
      ∑ x, q (u, x) * bcMarg₂ W x y := by
  classical
  simp only [dist, bcJoint, jointOf, pair_apply, Prod.mk.injEq, Fintype.sum_prod_type, bcMarg₂,
    mul_sum, ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]

lemma dist_bcJoint_XY₁ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) (x : α) (y : β₁) :
    dist (bcJoint q W) (pair (fun z => z.1.2) (fun z => z.2.1)) (x, y) =
      (∑ u, q (u, x)) * bcMarg₁ W x y := by
  classical
  simp only [dist, bcJoint, jointOf, pair_apply, Prod.mk.injEq, Fintype.sum_prod_type, bcMarg₁,
    mul_sum, sum_mul, ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  exact sum_comm

lemma dist_bcJoint_XY₂ (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) (x : α) (y : β₂) :
    dist (bcJoint q W) (pair (fun z => z.1.2) (fun z => z.2.2)) (x, y) =
      (∑ u, q (u, x)) * bcMarg₂ W x y := by
  classical
  simp only [dist, bcJoint, jointOf, pair_apply, Prod.mk.injEq, Fintype.sum_prod_type, bcMarg₂,
    mul_sum, sum_mul, ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  exact sum_comm

/-- `I(U; Y₁)` only depends on `p(u, x)` and the conditional marginal `p(y₁ | x)`: it is the mutual
information of the law `p(u, y₁) = ∑ₓ p(u, x) p(y₁ | x)`. -/
theorem bcInfoUY₁_eq (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) :
    bcInfoUY₁ q W = I[Prod.fst : Prod.snd ; fun z : 𝒰 × β₁ => ∑ x, q (z.1, x) * bcMarg₁ W x z.2] :=
  mutualInfo_eq_of_dist_pair_eq (by
    rw [dist_pair_fst_snd]
    funext ⟨u, y⟩
    exact dist_bcJoint_UY₁ q W u y)

/-- `I(U; Y₂)` only depends on `p(u, x)` and the conditional marginal `p(y₂ | x)`: it is the mutual
information of the law `p(u, y₂) = ∑ₓ p(u, x) p(y₂ | x)`. -/
theorem bcInfoUY₂_eq (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) :
    bcInfoUY₂ q W = I[Prod.fst : Prod.snd ; fun z : 𝒰 × β₂ => ∑ x, q (z.1, x) * bcMarg₂ W x z.2] :=
  mutualInfo_eq_of_dist_pair_eq (by
    rw [dist_pair_fst_snd]
    funext ⟨u, y⟩
    exact dist_bcJoint_UY₂ q W u y)

/-- `I(X; Y₁)` is the mutual information of the marginal `p(x)` and the channel `p(y₁ | x)`. -/
theorem bcInfoXY₁_eq (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) :
    bcInfoXY₁ q W = mutualInfoOf (fun x => ∑ u, q (u, x)) (bcMarg₁ W) :=
  mutualInfo_eq_of_dist_pair_eq (by
    rw [dist_pair_fst_snd]
    funext ⟨x, y⟩
    exact dist_bcJoint_XY₁ q W x y)

/-- `I(X; Y₂)` is the mutual information of the marginal `p(x)` and the channel `p(y₂ | x)`. -/
theorem bcInfoXY₂_eq (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) :
    bcInfoXY₂ q W = mutualInfoOf (fun x => ∑ u, q (u, x)) (bcMarg₂ W) :=
  mutualInfo_eq_of_dist_pair_eq (by
    rw [dist_pair_fst_snd]
    funext ⟨x, y⟩
    exact dist_bcJoint_XY₂ q W x y)

lemma bcInfoUY₁_congr (q : 𝒰 × α → ℝ) {W W' : α → β₁ × β₂ → ℝ} (h : bcMarg₁ W = bcMarg₁ W') :
    bcInfoUY₁ q W = bcInfoUY₁ q W' := by
  rw [bcInfoUY₁_eq, bcInfoUY₁_eq, h]

lemma bcInfoUY₂_congr (q : 𝒰 × α → ℝ) {W W' : α → β₁ × β₂ → ℝ} (h : bcMarg₂ W = bcMarg₂ W') :
    bcInfoUY₂ q W = bcInfoUY₂ q W' := by
  rw [bcInfoUY₂_eq, bcInfoUY₂_eq, h]

@[simp] lemma bcInfoUY₁_bcReceiverSwap (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) :
    bcInfoUY₁ q (bcReceiverSwap W) = bcInfoUY₂ q W := by
  rw [bcInfoUY₁_eq, bcInfoUY₂_eq, bcMarg₁_bcReceiverSwap]

@[simp] lemma bcInfoUY₂_bcReceiverSwap (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) :
    bcInfoUY₂ q (bcReceiverSwap W) = bcInfoUY₁ q W := by
  rw [bcInfoUY₁_eq, bcInfoUY₂_eq, bcMarg₂_bcReceiverSwap]

/-- Being less noisy only depends on the conditional marginals. -/
lemma IsLessNoisy.congr {W W' : α → β₁ × β₂ → ℝ} (h : IsLessNoisy W) (h₁ : bcMarg₁ W = bcMarg₁ W')
    (h₂ : bcMarg₂ W = bcMarg₂ W') : IsLessNoisy W' := fun k q hq => by
  rw [← bcInfoUY₁_congr q h₁, ← bcInfoUY₂_congr q h₂]
  exact h k q hq

/-! ### Degraded implies less noisy implies more capable -/

/-- **Lecture 5 of [elgamal2010].** A physically degraded DM-BC is less noisy: `U → Y₁ → Y₂`, so
`I(U; Y₂) ≤ I(U; Y₁)` by the data processing inequality. -/
theorem IsPhysicallyDegraded.isLessNoisy {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W)
    (h : IsPhysicallyDegraded W) : IsLessNoisy W := by
  obtain ⟨W₁, V, -, -, hWV⟩ := h
  intro k q hq
  have hμ := bcJoint_isPMF hq hW
  have h1 : MarkovChain (bcJoint q W) Prod.fst (Prod.fst ∘ Prod.snd) Prod.snd :=
    markovChain_of_factorization hμ (a := fun z y₁ => q z * W₁ z.2 y₁) (b := fun y => V y.1 y.2)
      fun z y => by simp only [bcJoint, jointOf, hWV]; ring
  have h2 := (((h1.comp_right hμ Prod.snd).symm hμ).comp_right hμ Prod.fst).symm hμ
  exact data_processing hμ h2

/-- **Lecture 5 of [elgamal2010].** A stochastically degraded DM-BC is less noisy: the mutual
informations only depend on the conditional marginals, which are those of a physically degraded
DM-BC. -/
theorem IsStochasticallyDegraded.isLessNoisy {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W)
    (h : IsStochasticallyDegraded W) : IsLessNoisy W := by
  obtain ⟨V, hV, hWV⟩ := h
  set W' : α → β₁ × β₂ → ℝ := fun x y => bcMarg₁ W x y.1 * V y.1 y.2
  have hW' : IsChannel W' := fun x =>
    ⟨fun y => mul_nonneg ((hW.bcMarg₁ x).nonneg _) ((hV _).nonneg _), by
      rw [Fintype.sum_prod_type]
      simp only [W', ← mul_sum, (hV _).sum_eq_one, mul_one]
      exact (hW.bcMarg₁ x).sum_eq_one⟩
  have h₁ : bcMarg₁ W' = bcMarg₁ W := by
    funext x y₁
    simp only [W', bcMarg₁, ← mul_sum, (hV y₁).sum_eq_one, mul_one]
  have h₂ : bcMarg₂ W' = bcMarg₂ W := by
    funext x y₂
    rw [hWV]
    rfl
  exact (IsPhysicallyDegraded.isLessNoisy hW' ⟨bcMarg₁ W, V, hW.bcMarg₁, hV, fun _ _ _ => rfl⟩)
    |>.congr h₁ h₂

omit [Fintype β₁] [Fintype β₂] in
/-- With `U = X`, encoded in `Fin k` by an equivalence `e`, the law `p(u, y) = ∑ₓ p(u, x) p(y | x)`
has the mutual information `I(X; Y)`. -/
private lemma mutualInfo_relabel_input {β : Type*} [Fintype β] {k : ℕ} (e : α ≃ Fin k)
    {p : α → ℝ} (hp : IsPMF p) {T : α → β → ℝ} (hT : IsChannel T) :
    I[Prod.fst : Prod.snd ; fun z : Fin k × β =>
      ∑ x, (if z.1 = e x then p x else 0) * T x z.2] = mutualInfoOf p T := by
  classical
  have hr : (fun z : Fin k × β => ∑ x, (if z.1 = e x then p x else 0) * T x z.2) =
      jointOf (p ∘ e.symm) fun u => T (e.symm u) := by
    funext ⟨u, y⟩
    rw [sum_eq_single (e.symm u) (fun x _ hx => by
      rw [ite_eq_right_iff.2 fun h => absurd (by rw [show u = e x from h, Equiv.symm_apply_apply])
        hx, zero_mul])
      (by simp)]
    simp [jointOf]
  have hp' : IsPMF (p ∘ e.symm) :=
    ⟨fun _ => hp.nonneg _, by rw [← hp.sum_eq_one]; exact e.symm.sum_comp p⟩
  have h := mutualInfoOf_eq hp' fun u => hT (e.symm u)
  rw [mutualInfoOf] at h
  rw [hr, h, mutualInfoOf_eq hp hT]
  congr 1
  · congr 1
    funext y
    exact e.symm.sum_comp fun x => p x * T x y
  · exact e.symm.sum_comp fun x => p x * entropy (T x)

/-- **Lecture 5 of [elgamal2010].** A less noisy DM-BC is more capable: take `U = X`. -/
theorem IsLessNoisy.isMoreCapable {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W) (h : IsLessNoisy W) :
    IsMoreCapable W := by
  classical
  intro p hp
  set e := Fintype.equivFin α
  set q : Fin (Fintype.card α) × α → ℝ := fun z => if z.1 = e z.2 then p z.2 else 0
  have hq : IsPMF q := by
    refine ⟨fun z => ?_, ?_⟩
    · simp only [q]; split_ifs
      exacts [hp.nonneg _, le_rfl]
    · rw [← hp.sum_eq_one, Fintype.sum_prod_type_right]
      refine sum_congr rfl fun x _ => ?_
      simp [q]
  have h := h _ q hq
  rwa [bcInfoUY₁_eq, bcInfoUY₂_eq, mutualInfo_relabel_input e hp hW.bcMarg₁,
    mutualInfo_relabel_input e hp hW.bcMarg₂] at h

/-- **Lecture 5 of [elgamal2010].** A degraded DM-BC is more capable. -/
theorem IsStochasticallyDegraded.isMoreCapable {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W)
    (h : IsStochasticallyDegraded W) : IsMoreCapable W :=
  (h.isLessNoisy hW).isMoreCapable hW

/-! ### Binary inputs: `I(U; Y)` as a Jensen gap -/

section Binary

variable {β : Type*} [Fintype β]

omit [Fintype 𝒰] in
/-- Every pmf `p(u, x)` with `x ∈ {0, 1}` is `p(u) Bern(aᵤ)(x)`. -/
lemma exists_bernoulli_decomp {q : 𝒰 × Bool → ℝ} (hq : ∀ z, 0 ≤ q z) :
    ∃ (w a : 𝒰 → ℝ), (∀ u, 0 ≤ w u) ∧ (∀ u, a u ∈ Set.Icc 0 1) ∧
      (∀ u, w u = q (u, false) + q (u, true)) ∧ ∀ u x, q (u, x) = w u * bernoulliPMF (a u) x := by
  refine ⟨fun u => q (u, false) + q (u, true), fun u => q (u, true) / (q (u, false) + q (u, true)),
    fun u => add_nonneg (hq _) (hq _), fun u => ⟨div_nonneg (hq _) (add_nonneg (hq _) (hq _)),
      div_le_one_of_le₀ (le_add_of_nonneg_left (hq _)) (add_nonneg (hq _) (hq _))⟩,
    fun _ => rfl, fun u x => ?_⟩
  have h0 := hq (u, false)
  have h1 := hq (u, true)
  rcases (add_nonneg h0 h1).eq_or_lt with h | h
  · have e0 : q (u, false) = 0 := by linarith
    have e1 : q (u, true) = 0 := by linarith
    cases x <;> simp [e0, e1]
  · cases x <;> simp only [bernoulliPMF, Bool.false_eq_true, ↓reduceIte] <;> field_simp
    ring

omit [Fintype 𝒰] in
lemma outDist_isChannel {a : 𝒰 → ℝ} (ha : ∀ u, a u ∈ Set.Icc 0 1) {T : Bool → β → ℝ}
    (hT : IsChannel T) : IsChannel fun u => outDist (bernoulliPMF (a u)) T := fun u =>
  outDist_isPMF (bernoulliPMF_isPMF (ha u).1 (ha u).2) hT

/-- For a binary input `X` with `p(u, x) = p(u) Bern(aᵤ)(x)` and a channel `T`, the mutual
information `I(U; Y)` is the Jensen gap `F(∑ᵤ p(u) aᵤ) - ∑ᵤ p(u) F(aᵤ)` of the output entropy
`F(a) = H(Y)` for `X ∼ Bern(a)`. -/
theorem mutualInfo_bernoulli_mixture {w a : 𝒰 → ℝ} (hw : IsPMF w)
    (ha : ∀ u, a u ∈ Set.Icc 0 1) {T : Bool → β → ℝ} (hT : IsChannel T) :
    I[Prod.fst : Prod.snd ; fun z : 𝒰 × β => ∑ x, w z.1 * bernoulliPMF (a z.1) x * T x z.2] =
      entropy (outDist (bernoulliPMF (∑ u, w u * a u)) T) -
        ∑ u, w u * entropy (outDist (bernoulliPMF (a u)) T) := by
  have hr : (fun z : 𝒰 × β => ∑ x, w z.1 * bernoulliPMF (a z.1) x * T x z.2) =
      jointOf w fun u => outDist (bernoulliPMF (a u)) T := by
    funext z
    simp only [jointOf, outDist, mul_sum, mul_assoc]
  have hout : outDist w (fun u => outDist (bernoulliPMF (a u)) T) =
      outDist (bernoulliPMF (∑ u, w u * a u)) T := by
    funext y
    simp only [outDist, Fintype.sum_bool, bernoulliPMF, Bool.false_eq_true,
      ↓reduceIte, mul_add, sum_add_distrib, ← mul_assoc, ← sum_mul]
    rw [show ∑ u, w u * (1 - a u) = 1 - ∑ u, w u * a u by
      simp only [mul_sub, mul_one, sum_sub_distrib, hw.sum_eq_one]]
  rw [hr]
  have := mutualInfoOf_eq hw (outDist_isChannel ha hT)
  rw [mutualInfoOf, hout] at this
  exact this

end Binary

/-! ### A BSC and a BEC -/

/-- The channel `X → Y₁` of the example of Nair: the binary symmetric channel BSC(`p`). -/
def bscBecMarg₁ (p : ℝ) : Bool → Bool → ℝ := fun x y => if x = y then 1 - p else p

/-- The channel `X → Y₂` of the example of Nair: the binary erasure channel BEC(`ε`), with the
erasure `e` represented by `none`. -/
def bscBecMarg₂ (ε : ℝ) : Bool → Option Bool → ℝ := fun x y =>
  match y with
  | none => ε
  | some y => if x = y then 1 - ε else 0

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** The DM-BC with `X ∈ {0, 1}`,
`Y₁ ∈ {0, 1}` the output of a BSC(`p`) and `Y₂ ∈ {0, 1, e}` the output of a BEC(`ε`), with the two
outputs conditionally independent given `X` (only the conditional marginals matter). -/
def bscBecBC (p ε : ℝ) : Bool → Bool × Option Bool → ℝ := fun x y =>
  bscBecMarg₁ p x y.1 * bscBecMarg₂ ε x y.2

lemma sum_bscBecMarg₁ (p : ℝ) (x : Bool) : ∑ y, bscBecMarg₁ p x y = 1 := by
  cases x <;> simp [bscBecMarg₁]

lemma sum_bscBecMarg₂ (ε : ℝ) (x : Bool) : ∑ y, bscBecMarg₂ ε x y = 1 := by
  cases x <;> simp [bscBecMarg₂, Fintype.sum_option]

lemma bscBecMarg₁_isChannel {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsChannel (bscBecMarg₁ p) :=
  fun x => ⟨fun y => by unfold bscBecMarg₁; split_ifs <;> linarith, sum_bscBecMarg₁ p x⟩

lemma bscBecMarg₂_isChannel {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : IsChannel (bscBecMarg₂ ε) :=
  fun x => ⟨fun y => by
    cases y with
    | none => exact h0
    | some y => simp only [bscBecMarg₂]; split_ifs <;> linarith, sum_bscBecMarg₂ ε x⟩

lemma bscBecBC_isChannel {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsChannel (bscBecBC p ε) := fun x =>
  ⟨fun y => mul_nonneg ((bscBecMarg₁_isChannel hp0 hp1 x).nonneg _)
    ((bscBecMarg₂_isChannel hε0 hε1 x).nonneg _), by
    rw [Fintype.sum_prod_type]
    simp only [bscBecBC, ← mul_sum, sum_bscBecMarg₂, mul_one, sum_bscBecMarg₁]⟩

@[simp] lemma bcMarg₁_bscBecBC (p ε : ℝ) : bcMarg₁ (bscBecBC p ε) = bscBecMarg₁ p := by
  funext x y
  simp only [bcMarg₁, bscBecBC, ← mul_sum, sum_bscBecMarg₂, mul_one]

@[simp] lemma bcMarg₂_bscBecBC (p ε : ℝ) : bcMarg₂ (bscBecBC p ε) = bscBecMarg₂ ε := by
  funext x y
  simp only [bcMarg₂, bscBecBC, ← sum_mul, sum_bscBecMarg₁, one_mul]

/-- The output of the BSC(`p`) for the input `Bern(a)` is `Bern(a ∗ p)`. -/
lemma outDist_bscBecMarg₁ (a p : ℝ) :
    outDist (bernoulliPMF a) (bscBecMarg₁ p) = bernoulliPMF (binConv a p) := by
  funext y
  cases y <;> simp [outDist, bernoulliPMF, bscBecMarg₁, binConv]
  ring

/-- `H(Y₁) = H(a ∗ p)` for `X ∼ Bern(a)`. -/
lemma entropy_outDist_bscBecMarg₁ (a p : ℝ) :
    entropy (outDist (bernoulliPMF a) (bscBecMarg₁ p)) = binEntropy (binConv a p) := by
  rw [outDist_bscBecMarg₁, entropy_bernoulliPMF]

/-- `H(Y₂) = H(ε) + (1 - ε) H(a)` for `X ∼ Bern(a)` (7.12). -/
lemma entropy_outDist_bscBecMarg₂ (a ε : ℝ) :
    entropy (outDist (bernoulliPMF a) (bscBecMarg₂ ε)) =
      binEntropy ε + (1 - ε) * binEntropy a := by
  rw [entropy_eq_sum_negMulLog, Fintype.sum_option, Fintype.sum_bool]
  simp only [outDist, Fintype.sum_bool, bscBecMarg₂, bernoulliPMF, Bool.false_eq_true,
    ↓reduceIte, mul_zero, add_zero, Bool.true_eq_false, zero_add]
  rw [show a * ε + (1 - a) * ε = ε by ring, negMulLog_mul, negMulLog_mul,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

lemma eq_bernoulliPMF_of_isPMF {r : Bool → ℝ} (hr : IsPMF r) : r = bernoulliPMF (r true) := by
  have h := hr.sum_eq_one
  rw [Fintype.sum_bool] at h
  funext b
  cases b <;> simp [bernoulliPMF]
  linarith

/-- `I(X; Y₁) = H(a ∗ p) - H(p)` for the BSC(`p`) with input `Bern(a)`. -/
theorem mutualInfoOf_bscBecMarg₁ {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {r : Bool → ℝ}
    (hr : IsPMF r) :
    mutualInfoOf r (bscBecMarg₁ p) = binEntropy (binConv (r true) p) - binEntropy p := by
  have hrow : ∀ x, entropy (bscBecMarg₁ p x) = binEntropy p := fun x => by
    rw [entropy_bool (bscBecMarg₁_isChannel h0 h1 x)]
    cases x <;> simp [bscBecMarg₁]
  rw [mutualInfoOf_eq hr (bscBecMarg₁_isChannel h0 h1)]
  simp only [hrow, ← sum_mul, hr.sum_eq_one, one_mul]
  rw [eq_bernoulliPMF_of_isPMF hr, entropy_outDist_bscBecMarg₁]
  simp [bernoulliPMF]

/-- `I(X; Y₂) = (1 - ε) H(a)` for the BEC(`ε`) with input `Bern(a)` (7.14). -/
theorem mutualInfoOf_bscBecMarg₂ {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {r : Bool → ℝ}
    (hr : IsPMF r) : mutualInfoOf r (bscBecMarg₂ ε) = (1 - ε) * binEntropy (r true) := by
  have hrow : ∀ x, entropy (bscBecMarg₂ ε x) = binEntropy ε := fun x => by
    rw [entropy_eq_sum_negMulLog, binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Fintype.sum_option]
    cases x <;> simp [bscBecMarg₂]
  rw [mutualInfoOf_eq hr (bscBecMarg₂_isChannel h0 h1)]
  simp only [hrow, ← sum_mul, hr.sum_eq_one, one_mul]
  rw [eq_bernoulliPMF_of_isPMF hr, entropy_outDist_bscBecMarg₂]
  simp [bernoulliPMF]

/-- A consequence of the convexity of `v ↦ H(H⁻¹(v) ∗ p)` (Mrs. Gerber's lemma), evaluated
between `v = 0` and `v = log 2`: `H(a ∗ p) ≤ H(p) + H(a) (1 - H(p) / log 2)`, that is
`H(a ∗ p) - H(p) ≤ H(a) (1 - H(p))` in bits. -/
theorem binEntropy_binConv_le {a p : ℝ} (ha : a ∈ Set.Icc 0 1) (hp : p ∈ Set.Icc 0 1) :
    binEntropy (binConv a p) ≤ binEntropy p + binEntropy a * (1 - binEntropy p / log 2) := by
  have hl : 0 < log 2 := log_pos one_lt_two
  have hm : ∀ b ∈ Set.Icc (0 : ℝ) 1, mrsGerber p (binEntropy b) = binEntropy (binConv b p) :=
    fun b hb => binEntropy_binConv_binEntropyInv hb p
  have h0 : mrsGerber p 0 = binEntropy p := by
    rw [← binEntropy_zero, hm 0 ⟨le_rfl, zero_le_one⟩]
    congr 1
    unfold binConv
    ring
  have h1 : mrsGerber p (log 2) = log 2 := by
    rw [← binEntropy_two_inv, hm 2⁻¹ ⟨by norm_num, by norm_num⟩, binConv_half_left]
  set t := binEntropy a / log 2
  have ht0 : 0 ≤ t := div_nonneg (binEntropy_nonneg ha.1 ha.2) hl.le
  have ht1 : t ≤ 1 := div_le_one_of_le₀ binEntropy_le_log_two hl.le
  have hc := (mrsGerber_convexOn hp).2 (x := 0) (y := log 2) ⟨le_rfl, hl.le⟩ ⟨hl.le, le_rfl⟩
    (sub_nonneg.2 ht1) ht0 (by ring)
  have harg : (1 - t) • (0 : ℝ) + t • log 2 = binEntropy a := by
    simp only [smul_eq_mul, mul_zero, zero_add, t]
    field_simp
  rw [harg, hm a ha, h0, h1, smul_eq_mul, smul_eq_mul] at hc
  have : t * log 2 = binEntropy a := by simp only [t]; field_simp
  have e : binEntropy a * (1 - binEntropy p / log 2) = t * log 2 - t * binEntropy p := by
    rw [← this]; field_simp
  rw [e]
  linarith

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** The BEC receiver `Y₂` is more
capable than the BSC receiver `Y₁` iff `ε ≤ H(p)` in bits, i.e. `ε log 2 ≤ H(p)` in nats: for
`X ∼ Bern(a)`, `I(X; Y₁) = H(a ∗ p) - H(p)` and `I(X; Y₂) = (1 - ε) H(a)`. -/
theorem isMoreCapable_bcReceiverSwap_bscBecBC_iff {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsMoreCapable (bcReceiverSwap (bscBecBC p ε)) ↔ ε * log 2 ≤ binEntropy p := by
  simp only [IsMoreCapable, bcMarg₁_bcReceiverSwap, bcMarg₂_bcReceiverSwap, bcMarg₁_bscBecBC,
    bcMarg₂_bscBecBC]
  constructor
  · intro h
    have h' := h _ (bernoulliPMF_isPMF (θ := 2⁻¹) (by norm_num) (by norm_num))
    rw [mutualInfoOf_bscBecMarg₁ hp0 hp1 (bernoulliPMF_isPMF (by norm_num) (by norm_num)),
      mutualInfoOf_bscBecMarg₂ hε0 hε1 (bernoulliPMF_isPMF (by norm_num) (by norm_num))] at h'
    simp only [bernoulliPMF, ite_true, binConv_half_left, binEntropy_two_inv] at h'
    linarith
  · intro h r hr
    rw [mutualInfoOf_bscBecMarg₁ hp0 hp1 hr, mutualInfoOf_bscBecMarg₂ hε0 hε1 hr]
    have ha : r true ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.nonneg _, hr.le_one _⟩
    have hb := binEntropy_binConv_le ha ⟨hp0, hp1⟩
    have hH := binEntropy_nonneg ha.1 ha.2
    have hl : 0 < log 2 := log_pos one_lt_two
    have : ε ≤ binEntropy p / log 2 := by rw [le_div_iff₀ hl]; exact h
    nlinarith

/-! ### Less noisy: the convexity of `H(a ∗ p) - (1 - ε) H(a)` -/

/-- `G(a) = H(a ∗ p) - (1 - ε) H(a)`: for `X ∼ Bern(a)`, `H(Y₁) - H(Y₂) = G(a) - H(ε)`. The
receiver `Y₂` is less noisy than `Y₁` iff the Jensen gaps of `G` are nonpositive. -/
private def bscBecGap (p ε a : ℝ) : ℝ := binEntropy (binConv a p) - (1 - ε) * binEntropy a

/-- `G'(a)`. -/
private def bscBecGap' (p ε a : ℝ) : ℝ :=
  (1 - 2 * p) * (log (1 - binConv a p) - log (binConv a p)) - (1 - ε) * (log (1 - a) - log a)

/-- `G''(a) = (1 - ε) / (a (1 - a)) - (1 - 2p)² / ((a ∗ p) (1 - a ∗ p))`. -/
private def bscBecGap'' (p ε a : ℝ) : ℝ :=
  (1 - ε) / (a * (1 - a)) - (1 - 2 * p) ^ 2 / (binConv a p * (1 - binConv a p))

private lemma binConv_mem_Ioo_of_le_half {a p : ℝ} (ha : a ∈ Set.Ioo 0 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 2⁻¹) : binConv a p ∈ Set.Ioo 0 1 := by
  have := ha.1; have := ha.2
  constructor <;> unfold binConv <;> nlinarith

private lemma hasDerivAt_binConv_left (a p : ℝ) :
    HasDerivAt (fun a => binConv a p) (1 - 2 * p) a := by
  have : (fun a => binConv a p) = fun a => p + (1 - 2 * p) * a := funext fun a => binConv_eq a p
  rw [this]
  simpa using ((hasDerivAt_id a).const_mul (1 - 2 * p)).const_add p

private lemma hasDerivAt_bscBecGap {p ε a : ℝ} (ha : a ∈ Set.Ioo 0 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 2⁻¹) : HasDerivAt (bscBecGap p ε) (bscBecGap' p ε a) a := by
  have hb := binConv_mem_Ioo_of_le_half ha hp0 hp1
  have h1 := (hasDerivAt_binEntropy hb.1.ne' hb.2.ne).comp a (hasDerivAt_binConv_left a p)
  have h2 := (hasDerivAt_binEntropy ha.1.ne' ha.2.ne).const_mul (1 - ε)
  exact (h1.sub h2).congr_deriv (by unfold bscBecGap'; ring)

private lemma hasDerivAt_bscBecGap' {p ε a : ℝ} (ha : a ∈ Set.Ioo 0 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 2⁻¹) : HasDerivAt (bscBecGap' p ε) (bscBecGap'' p ε a) a := by
  have hb := binConv_mem_Ioo_of_le_half ha hp0 hp1
  have hb1 : 1 - binConv a p ≠ 0 := by linarith [hb.2]
  have ha1 : 1 - a ≠ 0 := by linarith [ha.2]
  have hc := hasDerivAt_binConv_left a p
  have h1 := ((hc.const_sub 1).log hb1).sub (hc.log hb.1.ne')
  have h2 := (((hasDerivAt_id a).const_sub 1).log ha1).sub ((hasDerivAt_id a).log ha.1.ne')
  have hb0 := hb.1.ne'
  have ha0 := ha.1.ne'
  refine ((h1.const_mul (1 - 2 * p)).sub (h2.const_mul (1 - ε))).congr_deriv ?_
  unfold bscBecGap''
  simp only [id]
  field_simp
  ring

/-- `G''(a) = ((1 - ε) B - (1 - 2p)² A) / (A B)` with `A = a (1 - a)`, `B = (a ∗ p) (1 - a ∗ p)`,
and the numerator is `(4p(1 - p) - ε) / 4 + ε (1 - 2p)² (a - 1/2)²`. -/
private lemma bscBecGap''_eq {p ε a : ℝ} (ha : a ∈ Set.Ioo 0 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹) :
    bscBecGap'' p ε a = ((4 * p * (1 - p) - ε) / 4 + ε * (1 - 2 * p) ^ 2 * (a - 2⁻¹) ^ 2) /
      ((a * (1 - a)) * (binConv a p * (1 - binConv a p))) := by
  have hb := binConv_mem_Ioo_of_le_half ha hp0 hp1
  have : 1 - binConv a p ≠ 0 := by linarith [hb.2]
  have : 1 - a ≠ 0 := by linarith [ha.2]
  have := hb.1.ne'
  have := ha.1.ne'
  unfold bscBecGap''
  field_simp
  unfold binConv
  ring

private lemma continuous_bscBecGap (p ε : ℝ) : Continuous (bscBecGap p ε) := by
  unfold bscBecGap binConv
  fun_prop

/-- For `ε ≤ 4p(1 - p)`, `G` is convex on `[0, 1]`. -/
private lemma bscBecGap_convexOn {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 4 * p * (1 - p)) : ConvexOn ℝ (Set.Icc 0 1) (bscBecGap p ε) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    (continuous_bscBecGap p ε).continuousOn (f' := bscBecGap' p ε) (f'' := bscBecGap'' p ε)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Icc] at hx
  · exact (hasDerivAt_bscBecGap hx hp0 hp1).hasDerivWithinAt
  · exact (hasDerivAt_bscBecGap' hx hp0 hp1).hasDerivWithinAt
  · rw [bscBecGap''_eq hx hp0 hp1]
    have hb := binConv_mem_Ioo_of_le_half hx hp0 hp1
    have := hx.1; have := hx.2; have := hb.1; have := hb.2
    refine div_nonneg ?_ (by positivity)
    have : 0 ≤ ε * (1 - 2 * p) ^ 2 * (x - 2⁻¹) ^ 2 := by positivity
    linarith

/-- `I(U; Y₁) - I(U; Y₂)` is the Jensen gap of `G` for the decomposition `p(u) Bern(aᵤ)(x)`. -/
private lemma bscBec_info_sub {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {q : 𝒰 × Bool → ℝ} {w a : 𝒰 → ℝ} (hw : IsPMF w) (ha : ∀ u, a u ∈ Set.Icc 0 1)
    (hdec : ∀ u x, q (u, x) = w u * bernoulliPMF (a u) x) :
    bcInfoUY₁ q (bscBecBC p ε) - bcInfoUY₂ q (bscBecBC p ε) =
      bscBecGap p ε (∑ u, w u * a u) - ∑ u, w u * bscBecGap p ε (a u) := by
  rw [bcInfoUY₁_eq, bcInfoUY₂_eq, bcMarg₁_bscBecBC, bcMarg₂_bscBecBC]
  simp only [hdec]
  rw [mutualInfo_bernoulli_mixture hw ha (bscBecMarg₁_isChannel hp0 hp1),
    mutualInfo_bernoulli_mixture hw ha (bscBecMarg₂_isChannel hε0 hε1)]
  simp only [entropy_outDist_bscBecMarg₁, entropy_outDist_bscBecMarg₂, bscBecGap]
  have e1 : ∑ u, w u * (binEntropy ε + (1 - ε) * binEntropy (a u)) =
      binEntropy ε + (1 - ε) * ∑ u, w u * binEntropy (a u) := by
    simp only [mul_add, sum_add_distrib, ← sum_mul, hw.sum_eq_one, one_mul, mul_sum]
    congr 1
    exact sum_congr rfl fun u _ => by ring
  have e2 : ∑ u, w u * (binEntropy (binConv (a u) p) - (1 - ε) * binEntropy (a u)) =
      ∑ u, w u * binEntropy (binConv (a u) p) - (1 - ε) * ∑ u, w u * binEntropy (a u) := by
    simp only [mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    exact sum_congr rfl fun u _ => by ring
  rw [e1, e2]
  ring

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** For `ε ≤ 4p(1 - p)`, the BEC
receiver `Y₂` is less noisy than the BSC receiver `Y₁`: `I(U; Y₁) - I(U; Y₂)` is a Jensen gap of
the function `H(a ∗ p) - (1 - ε) H(a)`, which is convex. -/
theorem isLessNoisy_bcReceiverSwap_bscBecBC {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 4 * p * (1 - p)) : IsLessNoisy (bcReceiverSwap (bscBecBC p ε)) := by
  intro k q hq
  rw [bcInfoUY₁_bcReceiverSwap, bcInfoUY₂_bcReceiverSwap]
  obtain ⟨w, a, hw0, ha, hwq, hdec⟩ := exists_bernoulli_decomp hq.nonneg
  have hw : IsPMF w := ⟨hw0, by
    rw [← hq.sum_eq_one, Fintype.sum_prod_type]
    exact sum_congr rfl fun u _ => by rw [hwq, Fintype.sum_bool, add_comm]⟩
  have hε1 : ε ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  have h := bscBec_info_sub hp0 (by linarith) hε0 hε1 hw ha hdec
  have hJ := (bscBecGap_convexOn hp0 hp1 hε0 hε).map_sum_le (t := univ) (w := w) (p := a)
    (fun u _ => hw0 u) hw.sum_eq_one (fun u _ => ha u)
  simp only [smul_eq_mul] at hJ
  linarith

/-- For `4p(1 - p) < ε`, with `κ = ε - 4p(1 - p)` and `η = κ / 4`, the function `G` lies strictly
above its chord at the midpoint of `[1/2 - η, 1/2 + η]`: `G''` is negative there. -/
private lemma bscBecGap_midpoint {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹) (hε1 : ε ≤ 1)
    (hε : 4 * p * (1 - p) < ε) :
    2⁻¹ * bscBecGap p ε (2⁻¹ - (ε - 4 * p * (1 - p)) / 4) +
      2⁻¹ * bscBecGap p ε (2⁻¹ + (ε - 4 * p * (1 - p)) / 4) < bscBecGap p ε 2⁻¹ := by
  set κ := ε - 4 * p * (1 - p) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hpp : 0 ≤ 4 * p * (1 - p) := by nlinarith
  have hκ1 : κ ≤ 1 := by rw [hκ]; linarith
  have hε0 : 0 ≤ ε := by linarith
  set η := κ / 4 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 4⁻¹ := by rw [hη]; linarith
  set f : ℝ → ℝ := fun a => bscBecGap p ε a + κ * (a - 2⁻¹) ^ 2 with hf
  have hs : ∀ x, HasDerivAt (fun a : ℝ => κ * (a - 2⁻¹) ^ 2) (κ * (2 * (x - 2⁻¹))) x := fun x => by
    have := (((hasDerivAt_id x).sub_const 2⁻¹).pow 2).const_mul κ
    exact this.congr_deriv (by simp)
  have hs' : ∀ x, HasDerivAt (fun a : ℝ => κ * (2 * (a - 2⁻¹))) (2 * κ) x := fun x => by
    have := (((hasDerivAt_id x).sub_const 2⁻¹).const_mul 2).const_mul κ
    exact this.congr_deriv (by ring)
  have hsub : ∀ x ∈ Set.Ioo (2⁻¹ - η) (2⁻¹ + η), x ∈ Set.Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hconc : ConcaveOn ℝ (Set.Icc (2⁻¹ - η) (2⁻¹ + η)) f := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (((continuous_bscBecGap p ε).add (by fun_prop)).continuousOn)
      (f' := fun a => bscBecGap' p ε a + κ * (2 * (a - 2⁻¹)))
      (f'' := fun a => bscBecGap'' p ε a + 2 * κ)
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Icc] at hx
    · exact ((hasDerivAt_bscBecGap (hsub x hx) hp0 hp1).add (hs x)).hasDerivWithinAt
    · exact ((hasDerivAt_bscBecGap' (hsub x hx) hp0 hp1).add (hs' x)).hasDerivWithinAt
    · have hx01 := hsub x hx
      have hb := binConv_mem_Ioo_of_le_half hx01 hp0 hp1
      have hA : 0 < x * (1 - x) := mul_pos hx01.1 (by linarith [hx01.2])
      have hB : 0 < binConv x p * (1 - binConv x p) := mul_pos hb.1 (by linarith [hb.2])
      have hA' : x * (1 - x) ≤ 4⁻¹ := by nlinarith [sq_nonneg (x - 2⁻¹)]
      have hB' : binConv x p * (1 - binConv x p) ≤ 4⁻¹ := by
        nlinarith [sq_nonneg (binConv x p - 2⁻¹)]
      have hAB : (x * (1 - x)) * (binConv x p * (1 - binConv x p)) ≤ 16⁻¹ := by
        calc _ ≤ (4⁻¹ : ℝ) * 4⁻¹ := mul_le_mul hA' hB' hB.le (by norm_num)
          _ = 16⁻¹ := by norm_num
      have hc : (1 - 2 * p) ^ 2 ≤ 1 := by nlinarith
      have hc0 : 0 ≤ (1 - 2 * p) ^ 2 := sq_nonneg _
      have hec : ε * (1 - 2 * p) ^ 2 ≤ 1 := by nlinarith
      have hs2 : (x - 2⁻¹) ^ 2 ≤ κ / 16 := by
        have h1 : (x - 2⁻¹) ^ 2 ≤ η ^ 2 := sq_le_sq' (by linarith [hx.1]) (by linarith [hx.2])
        have h2 : η ^ 2 = κ * κ / 16 := by rw [hη]; ring
        nlinarith
      have hN : (4 * p * (1 - p) - ε) / 4 + ε * (1 - 2 * p) ^ 2 * (x - 2⁻¹) ^ 2 ≤
          -(3 * κ / 16) := by
        have h1 : ε * (1 - 2 * p) ^ 2 * (x - 2⁻¹) ^ 2 ≤ κ / 16 := by
          nlinarith [sq_nonneg (x - 2⁻¹)]
        have h2 : (4 * p * (1 - p) - ε) / 4 = -(κ / 4) := by rw [hκ]; ring
        linarith
      have hle : bscBecGap'' p ε x ≤ -(3 * κ) := by
        rw [bscBecGap''_eq hx01 hp0 hp1, div_le_iff₀ (mul_pos hA hB)]
        nlinarith
      linarith
  have hmem₁ : 2⁻¹ - η ∈ Set.Icc (2⁻¹ - η) (2⁻¹ + η) := ⟨le_rfl, by linarith⟩
  have hmem₂ : 2⁻¹ + η ∈ Set.Icc (2⁻¹ - η) (2⁻¹ + η) := ⟨by linarith, le_rfl⟩
  have h := hconc.2 hmem₁ hmem₂ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num)
  simp only [smul_eq_mul, hf] at h
  rw [show (2⁻¹ : ℝ) * (2⁻¹ - η) + 2⁻¹ * (2⁻¹ + η) = 2⁻¹ by ring] at h
  have hη2 : 0 < κ * η ^ 2 := by positivity
  ring_nf at h ⊢
  nlinarith

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** For `4p(1 - p) < ε`, the BEC
receiver `Y₂` is not less noisy than the BSC receiver `Y₁`: take `U` uniform on `{0, 1}` and
`X ∼ Bern(1/2 ∓ η)` given `U` for a small `η`. -/
theorem not_isLessNoisy_bcReceiverSwap_bscBecBC {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹)
    (hε1 : ε ≤ 1) (hε : 4 * p * (1 - p) < ε) :
    ¬ IsLessNoisy (bcReceiverSwap (bscBecBC p ε)) := by
  intro hL
  have hm := bscBecGap_midpoint hp0 hp1 hε1 hε
  have hpp : 0 ≤ 4 * p * (1 - p) := by nlinarith
  have hε0 : 0 ≤ ε := by linarith
  set η := (ε - 4 * p * (1 - p)) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η ≤ 4⁻¹ := by rw [hη]; linarith
  set a : Fin 2 → ℝ := fun u => if u = 0 then 2⁻¹ - η else 2⁻¹ + η with ha_def
  have ha : ∀ u, a u ∈ Set.Icc (0 : ℝ) 1 := fun u => by
    simp only [ha_def]
    split_ifs <;> constructor <;> linarith
  set w : Fin 2 → ℝ := fun _ => 2⁻¹ with hw_def
  have hw : IsPMF w := ⟨fun _ => by norm_num [hw_def], by simp [hw_def]⟩
  set q : Fin 2 × Bool → ℝ := fun z => w z.1 * bernoulliPMF (a z.1) z.2 with hq_def
  have hq : IsPMF q := by
    have hb : ∀ u, IsPMF (bernoulliPMF (a u)) := fun u => bernoulliPMF_isPMF (ha u).1 (ha u).2
    refine ⟨fun z => mul_nonneg (hw.nonneg z.1) ((hb z.1).nonneg z.2), ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [hq_def, ← mul_sum, (hb _).sum_eq_one, mul_one]
    exact hw.sum_eq_one
  have h := bscBec_info_sub hp0 (by linarith) hε0 hε1 hw ha (q := q) fun _ _ => rfl
  have hL' := hL 2 q hq
  rw [bcInfoUY₁_bcReceiverSwap, bcInfoUY₂_bcReceiverSwap] at hL'
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [hw_def, ha_def, Fin.isValue, ↓reduceIte, one_ne_zero] at h
  rw [show (2⁻¹ : ℝ) * (2⁻¹ - η) + 2⁻¹ * (2⁻¹ + η) = 2⁻¹ by ring] at h
  linarith

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** The BEC receiver `Y₂` is less noisy
than the BSC receiver `Y₁` iff `ε ≤ 4p(1 - p)`. -/
theorem isLessNoisy_bcReceiverSwap_bscBecBC_iff {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsLessNoisy (bcReceiverSwap (bscBecBC p ε)) ↔ ε ≤ 4 * p * (1 - p) :=
  ⟨fun h => not_lt.1 fun hlt => not_isLessNoisy_bcReceiverSwap_bscBecBC hp0 hp1 hε1 hlt h,
    isLessNoisy_bcReceiverSwap_bscBecBC hp0 hp1 hε0⟩

/-! ### Degradedness -/

/-- The channel from `{0, 1, e}` to `{0, 1}` that degrades the BEC(`ε`) to the BSC(`p`): an erasure
is replaced by a fair coin flip, and the other outputs go through a BSC(`θ`). -/
private def bscBecDegrading (θ : ℝ) : Option Bool → Bool → ℝ := fun y z =>
  match y with
  | none => 2⁻¹
  | some b => bscBecMarg₁ θ b z

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** For `ε ≤ 2p`, the BSC receiver `Y₁`
is a degraded version of the BEC receiver `Y₂`: the BSC(`p`) is the BEC(`ε`) followed by the channel
that replaces an erasure by a fair coin flip and otherwise is a BSC(`(p - ε/2) / (1 - ε)`). -/
theorem isStochasticallyDegraded_bcReceiverSwap_bscBecBC {p ε : ℝ} (hp1 : p ≤ 2⁻¹)
    (hε : ε ≤ 2 * p) : IsStochasticallyDegraded (bcReceiverSwap (bscBecBC p ε)) := by
  have hε1 : ε ≤ 1 := by linarith
  set θ := (p - ε / 2) / (1 - ε) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  have hmul : (1 - ε) * θ = p - ε / 2 := by
    rcases eq_or_ne ε 1 with h | h
    · have : p = 2⁻¹ := by linarith
      rw [h, this]; norm_num
    · have : 1 - ε ≠ 0 := sub_ne_zero.2 h.symm
      rw [hθ]; field_simp
  have hV : IsChannel (bscBecDegrading θ) := fun y => by
    cases y with
    | none => exact ⟨fun _ => by norm_num [bscBecDegrading], by simp [bscBecDegrading]⟩
    | some b => exact bscBecMarg₁_isChannel hθ0 hθ1 b
  refine ⟨bscBecDegrading θ, hV, fun x y => ?_⟩
  rw [bcMarg₁_bcReceiverSwap, bcMarg₂_bcReceiverSwap, bcMarg₁_bscBecBC, bcMarg₂_bscBecBC,
    Fintype.sum_option, Fintype.sum_bool]
  cases x <;> cases y <;> simp [bscBecMarg₁, bscBecMarg₂, bscBecDegrading] <;> linarith

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** For `2p < ε`, the BSC receiver `Y₁`
is not a degraded version of the BEC receiver `Y₂`. -/
theorem not_isStochasticallyDegraded_bcReceiverSwap_bscBecBC {p ε : ℝ} (hε1 : ε ≤ 1)
    (hε : 2 * p < ε) : ¬ IsStochasticallyDegraded (bcReceiverSwap (bscBecBC p ε)) := by
  rintro ⟨V, hV, h⟩
  have h₁ := h false true
  have h₂ := h true false
  rw [bcMarg₁_bcReceiverSwap, bcMarg₂_bcReceiverSwap, bcMarg₁_bscBecBC, bcMarg₂_bscBecBC,
    Fintype.sum_option, Fintype.sum_bool] at h₁ h₂
  have e₁ : p = ε * V none true + (1 - ε) * V (some false) true := by
    simpa [bscBecMarg₁, bscBecMarg₂] using h₁
  have e₂ : p = ε * V none false + (1 - ε) * V (some true) false := by
    simpa [bscBecMarg₁, bscBecMarg₂] using h₂
  have hs := (hV none).sum_eq_one
  rw [Fintype.sum_bool] at hs
  have hn₁ := mul_nonneg (sub_nonneg.2 hε1) ((hV (some false)).nonneg true)
  have hn₂ := mul_nonneg (sub_nonneg.2 hε1) ((hV (some true)).nonneg false)
  have hsum : ε * V none true + ε * V none false = ε := by rw [← mul_add, hs, mul_one]
  linarith

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** The BSC receiver `Y₁` is a degraded
version of the BEC receiver `Y₂` iff `ε ≤ 2p`. -/
theorem isStochasticallyDegraded_bcReceiverSwap_bscBecBC_iff {p ε : ℝ} (hp1 : p ≤ 2⁻¹)
    (hε1 : ε ≤ 1) :
    IsStochasticallyDegraded (bcReceiverSwap (bscBecBC p ε)) ↔ ε ≤ 2 * p :=
  ⟨fun h => not_lt.1 fun hlt => not_isStochasticallyDegraded_bcReceiverSwap_bscBecBC hε1 hlt h,
    isStochasticallyDegraded_bcReceiverSwap_bscBecBC hp1⟩

/-! ### The BSC receiver is not more capable -/

/-- The tangent line bound for the binary entropy: `H(b) ≤ H(p) + (b - p) H'(p)`, which is the
nonnegativity of the relative entropy `D(Bern(b) ‖ Bern(p))`. -/
private lemma binEntropy_le_tangent {b p : ℝ} (hb : b ∈ Set.Ioo 0 1) (hp : p ∈ Set.Ioo 0 1) :
    binEntropy b ≤ binEntropy p + (log (1 - p) - log p) * (b - p) := by
  have hb0 := hb.1
  have hp0 := hp.1
  have hb1 : 0 < 1 - b := by linarith [hb.2]
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have h1 : b * (log p - log b) ≤ p - b := by
    have := log_le_sub_one_of_pos (div_pos hp0 hb0)
    rw [log_div hp0.ne' hb0.ne'] at this
    calc b * (log p - log b) ≤ b * (p / b - 1) := mul_le_mul_of_nonneg_left this hb0.le
      _ = p - b := by field_simp
  have h2 : (1 - b) * (log (1 - p) - log (1 - b)) ≤ (1 - p) - (1 - b) := by
    have := log_le_sub_one_of_pos (div_pos hp1 hb1)
    rw [log_div hp1.ne' hb1.ne'] at this
    calc (1 - b) * (log (1 - p) - log (1 - b)) ≤ (1 - b) * ((1 - p) / (1 - b) - 1) :=
          mul_le_mul_of_nonneg_left this hb1.le
      _ = (1 - p) - (1 - b) := by field_simp
  simp only [binEntropy_eq_mul_log_inv, log_inv]
  nlinarith

/-- **Example (a BSC and a BEC), Lecture 5 of [elgamal2010].** For `0 < p ≤ 1/2` and `ε < 1`, the
BSC receiver `Y₁` is never more capable than the BEC receiver `Y₂`: at a small `a`,
`I(X; Y₂) = (1 - ε) H(a)` is of order `a log (1 / a)` while `I(X; Y₁) = H(a ∗ p) - H(p)` is of
order `a`. -/
theorem not_isMoreCapable_bscBecBC {p ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 2⁻¹) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) : ¬ IsMoreCapable (bscBecBC p ε) := by
  intro h
  have hL : 0 ≤ log (1 - p) - log p :=
    sub_nonneg.2 (log_le_log hp0 (by linarith))
  have hc : 0 ≤ 1 - 2 * p := by linarith
  have hε' : 0 < 1 - ε := by linarith
  set L := log (1 - p) - log p with hLdef
  set M := L * (1 - 2 * p) / (1 - ε) + 1 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hMe : (1 - ε) * M = L * (1 - 2 * p) + (1 - ε) := by rw [hM]; field_simp
  set a := exp (-M) with ha_def
  have ha0 : 0 < a := exp_pos _
  have ha1 : a < 1 := exp_lt_one_iff.2 (by linarith)
  have hmem : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha0, ha1⟩
  have hb := binConv_mem_Ioo_of_le_half hmem hp0.le hp1
  have hpm : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, by linarith⟩
  have h' := h _ (bernoulliPMF_isPMF ha0.le ha1.le)
  rw [bcMarg₁_bscBecBC, bcMarg₂_bscBecBC, mutualInfoOf_bscBecMarg₁ hp0.le (by linarith)
    (bernoulliPMF_isPMF ha0.le ha1.le), mutualInfoOf_bscBecMarg₂ hε0 hε1.le
    (bernoulliPMF_isPMF ha0.le ha1.le)] at h'
  simp only [bernoulliPMF, ↓reduceIte] at h'
  have ht := binEntropy_le_tangent hb hpm
  rw [← hLdef, show binConv a p - p = (1 - 2 * p) * a by rw [binConv_eq]; ring] at ht
  have hH : M * a ≤ binEntropy a := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have h1 := negMulLog_nonneg (x := 1 - a) (by linarith) (by linarith)
    have h2 : negMulLog a = M * a := by
      simp only [negMulLog_def, ha_def, log_exp]
      ring
    linarith
  have h3 : (1 - ε) * (M * a) ≤ (1 - ε) * binEntropy a := mul_le_mul_of_nonneg_left hH hε'.le
  have h4 : (1 - ε) * (M * a) = (L * (1 - 2 * p) + (1 - ε)) * a := by rw [← hMe]; ring
  have h5 : 0 < (1 - ε) * a := mul_pos hε' ha0
  nlinarith

/-- If `p = 0`, the BEC receiver `Y₂` is a degraded version of the noiseless receiver `Y₁`, for
every `ε`: in the notes' case 4, `p > 0` is needed. -/
theorem isStochasticallyDegraded_bscBecBC_of_p_eq_zero {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsStochasticallyDegraded (bscBecBC 0 ε) := by
  refine ⟨bscBecMarg₂ ε, bscBecMarg₂_isChannel hε0 hε1, fun x y => ?_⟩
  rw [bcMarg₁_bscBecBC, bcMarg₂_bscBecBC, Fintype.sum_bool]
  cases x <;> simp [bscBecMarg₁]

/-- If `ε = 1`, the output of the BEC is always an erasure, so that the BEC receiver `Y₂` is a
degraded version of `Y₁`, for every `p`: in the notes' case 4, `ε < 1` is needed. -/
theorem isStochasticallyDegraded_bscBecBC_of_eps_eq_one (p : ℝ) :
    IsStochasticallyDegraded (bscBecBC p 1) := by
  refine ⟨bscBecMarg₂ 1, bscBecMarg₂_isChannel zero_le_one le_rfl, fun x y => ?_⟩
  rw [bcMarg₁_bscBecBC, bcMarg₂_bscBecBC, Fintype.sum_bool]
  cases x <;> cases y <;> simp [bscBecMarg₁, bscBecMarg₂]

/-! ### The four cases of the example -/

/-- **Example (a BSC and a BEC), case 1, Lecture 5 of [elgamal2010].** For `0 ≤ ε ≤ 2p`, `Y₁` is a
degraded version of `Y₂`. -/
theorem bscBecBC_case₁ {p ε : ℝ} (hp1 : p ≤ 2⁻¹) (hε : ε ≤ 2 * p) :
    IsStochasticallyDegraded (bcReceiverSwap (bscBecBC p ε)) :=
  isStochasticallyDegraded_bcReceiverSwap_bscBecBC hp1 hε

/-- **Example (a BSC and a BEC), case 2, Lecture 5 of [elgamal2010].** For `2p < ε ≤ 4p(1 - p)`,
`Y₂` is less noisy than `Y₁`, but `Y₁` is not a degraded version of `Y₂`. -/
theorem bscBecBC_case₂ {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹) (h₁ : 2 * p < ε)
    (h₂ : ε ≤ 4 * p * (1 - p)) :
    IsLessNoisy (bcReceiverSwap (bscBecBC p ε)) ∧
      ¬ IsStochasticallyDegraded (bcReceiverSwap (bscBecBC p ε)) :=
  ⟨isLessNoisy_bcReceiverSwap_bscBecBC hp0 hp1 (by linarith) h₂,
    not_isStochasticallyDegraded_bcReceiverSwap_bscBecBC
      (by nlinarith [sq_nonneg (1 - 2 * p)]) h₁⟩

/-- **Example (a BSC and a BEC), case 3, Lecture 5 of [elgamal2010].** For `4p(1 - p) < ε ≤ H(p)`,
with `H(p)` in bits, `Y₂` is more capable than `Y₁`, but not less noisy. -/
theorem bscBecBC_case₃ {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹) (h₁ : 4 * p * (1 - p) < ε)
    (h₂ : ε * log 2 ≤ binEntropy p) :
    IsMoreCapable (bcReceiverSwap (bscBecBC p ε)) ∧
      ¬ IsLessNoisy (bcReceiverSwap (bscBecBC p ε)) := by
  have hl : 0 < log 2 := log_pos one_lt_two
  have hε0 : 0 ≤ ε := by nlinarith
  have hε1 : ε ≤ 1 := by
    have := (binEntropy_le_log_two (p := p))
    by_contra hc
    nlinarith [not_le.1 hc]
  exact ⟨(isMoreCapable_bcReceiverSwap_bscBecBC_iff hp0 (by linarith) hε0 hε1).2 h₂,
    not_isLessNoisy_bcReceiverSwap_bscBecBC hp0 hp1 hε1 h₁⟩

/-- **Example (a BSC and a BEC), case 4, Lecture 5 of [elgamal2010].** For `H(p) < ε < 1`, with
`H(p)` in bits, and `p > 0`, the DM-BC belongs to none of the three classes, with either receiver
as the stronger one. The notes state this for `H(p) < ε ≤ 1` and `p ∈ [0, 1/2]`, but it fails for
`ε = 1` and for `p = 0`, see `isStochasticallyDegraded_bscBecBC_of_eps_eq_one` and
`isStochasticallyDegraded_bscBecBC_of_p_eq_zero`. -/
theorem bscBecBC_case₄ {p ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 2⁻¹)
    (h₁ : binEntropy p < ε * log 2) (h₂ : ε < 1) :
    (¬ IsStochasticallyDegraded (bcReceiverSwap (bscBecBC p ε)) ∧
        ¬ IsLessNoisy (bcReceiverSwap (bscBecBC p ε)) ∧
        ¬ IsMoreCapable (bcReceiverSwap (bscBecBC p ε))) ∧
      ¬ IsStochasticallyDegraded (bscBecBC p ε) ∧ ¬ IsLessNoisy (bscBecBC p ε) ∧
        ¬ IsMoreCapable (bscBecBC p ε) := by
  have hl : 0 < log 2 := log_pos one_lt_two
  have hH : 0 ≤ binEntropy p := binEntropy_nonneg hp0.le (by linarith)
  have hε0 : 0 ≤ ε := by
    by_contra hc
    nlinarith [not_le.1 hc]
  have hW : IsChannel (bscBecBC p ε) := bscBecBC_isChannel hp0.le (by linarith) hε0 h₂.le
  have hM₁ : ¬ IsMoreCapable (bcReceiverSwap (bscBecBC p ε)) := fun h =>
    absurd ((isMoreCapable_bcReceiverSwap_bscBecBC_iff hp0.le (by linarith) hε0 h₂.le).1 h)
      (not_le.2 h₁)
  have hM₂ := not_isMoreCapable_bscBecBC hp0 hp1 hε0 h₂
  exact ⟨⟨fun h => hM₁ (h.isMoreCapable hW.bcReceiverSwap),
      fun h => hM₁ (h.isMoreCapable hW.bcReceiverSwap), hM₁⟩,
    fun h => hM₂ (h.isMoreCapable hW), fun h => hM₂ (h.isMoreCapable hW), hM₂⟩

/-- The thresholds of the example are ordered: `4p(1 - p) ≤ H(p)`, with `H(p)` in bits, since a less
noisy DM-BC is more capable. -/
theorem four_mul_mul_one_sub_mul_log_two_le_binEntropy {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2⁻¹) :
    4 * p * (1 - p) * log 2 ≤ binEntropy p := by
  have hε0 : 0 ≤ 4 * p * (1 - p) := by nlinarith
  have hε1 : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  have hW := bscBecBC_isChannel (p := p) (ε := 4 * p * (1 - p)) hp0 (by linarith) hε0 hε1
  exact (isMoreCapable_bcReceiverSwap_bscBecBC_iff hp0 (by linarith) hε0 hε1).1
    ((isLessNoisy_bcReceiverSwap_bscBecBC hp0 hp1 hε0 le_rfl).isMoreCapable hW.bcReceiverSwap)

end InfoTheory
