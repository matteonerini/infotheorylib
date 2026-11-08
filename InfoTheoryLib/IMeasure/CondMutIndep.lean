/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.IMeasure.Realization
public import InfoTheoryLib.InfoInequalities.Polymatroid
public import InfoTheoryLib.MutualInformation.CondMutIndep

/-!
# Conditional mutual independence and the I-Measure

Let `X_{Qᵢ}`, `i ∈ κ`, be blocks of random variables `Xₗ`, `l ∈ ι`, with disjoint index sets
`Qᵢ`. They are mutually independent conditioning on a block `X_T` if and only if `μ*` vanishes on
the sets `⋂_{l ∈ ⋃ Wᵢ} X̃ₗ - X̃_{T ∪ ⋃ (Qᵢ - Wᵢ)}` for all `Wᵢ ⊆ Qᵢ` of which at least two are
nonempty (Theorem 12.9). For a *full* conditional mutual independency (FCMI), in which every
variable is involved, these sets are atoms, and they form the *image* of the FCMI. A set of FCMIs
holds if and only if `μ*` vanishes on the union of their images, so a set of FCMIs implies another
if and only if its image contains the other's (Theorem 12.20): the implication problem for FCMIs
is solved by the basic inequalities.

## Main definitions

* `FCMI ι`: a conditional mutual independency `(T, Qᵢ)`, with `FCMI.IsFull`, `FCMI.Holds` and
  `FCMI.image`.
* `fcmiImage P`: the image of a set `P` of FCMIs.
* `FCMI.Implies P₁ P₂`: the FCMIs in `P₁` imply those in `P₂`.

## Main statements

* `condMutIndep_blocks_sdiff`: **Theorem 12.5**.
* `iMeasure_inf_sdiff_eq_zero_of_condMutIndep`: **Lemma 12.7**.
* `IsSignedMeasure.inf_inter_inf_sdiff_eq_sum`: **Lemma 12.8**.
* `condMutIndep_blocks_iff_iMeasure`: **Theorem 12.9**.
* `FCMI.mem_image_iff`, `FCMI.mem_image_iff_of_parts_eq_pair`: **Propositions 12.15 and 12.14**.
* `FCMI.holds_iff`, `FCMI.holds_set_iff`: **Theorems 12.17 and 12.19**.
* `FCMI.implies_iff`, `FCMI.equiv_iff`: **Theorem 12.20 and Corollary 12.21**.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 12.1 and 12.2
-/

open Real Finset Function

@[expose] public noncomputable section

namespace InfoTheory

universe u

/-! ### Lemma 12.8 -/

/-- A sum over the subsets of a disjoint union is a double sum. -/
lemma sum_powerset_union_of_disjoint {κ : Type*} [DecidableEq κ] {S T : Finset κ}
    (hST : Disjoint S T) (G : Finset κ → ℝ) :
    ∑ U ∈ (S ∪ T).powerset, G U = ∑ S' ∈ S.powerset, ∑ T' ∈ T.powerset, G (S' ∪ T') := by
  induction T using Finset.induction_on generalizing G with
  | empty => simp
  | insert b T hb ih =>
    have hbS : b ∉ S := fun h => disjoint_left.1 hST h (mem_insert_self b T)
    have hST' : Disjoint S T := disjoint_of_subset_right (subset_insert b T) hST
    rw [union_insert, sum_powerset_insert (fun h => (mem_union.1 h).elim hbS hb), ih hST',
      ih hST' (fun U => G (insert b U)), ← sum_add_distrib]
    refine sum_congr rfl fun S' _ => ?_
    rw [sum_powerset_insert hb]
    simp only [union_insert]

/-- `∑_{T' ⊆ T} (-1)^{|T'|} = 0` for a nonempty `T`, (12.44). -/
lemma sum_powerset_neg_one_pow_eq_zero {κ : Type*} {T : Finset κ} (hT : T.Nonempty) :
    ∑ T' ∈ T.powerset, (-1 : ℝ) ^ #T' = 0 := by
  have := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card_of_nonempty hT)
  push_cast at this
  exact this

/-- **Lemma 12.8.** For a set-additive function `m`, disjoint nonempty index sets `S` and `T`, and
sets `Aᵢ` and `B`,
`m((⋂_{i ∈ S} Aᵢ) ∩ (⋂_{j ∈ T} Aⱼ) - B) = ∑_{S' ⊆ S} ∑_{T' ⊆ T} (-1)^{|S'| + |T'|}
(m(A_{S'} - B) + m(A_{T'} - B) - m(A_{S' ∪ T'} - B))` (12.41), where `A_{S'} = ⋃_{i ∈ S'} Aᵢ`.
-/
theorem IsSignedMeasure.inf_inter_inf_sdiff_eq_sum {α κ : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq κ] {m : Finset α → ℝ} (hm : IsSignedMeasure m) {S T : Finset κ}
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T) (A : κ → Finset α)
    (B : Finset α) :
    m ((S.inf A ∩ T.inf A) \ B) = ∑ S' ∈ S.powerset, ∑ T' ∈ T.powerset,
      (-1 : ℝ) ^ (#S' + #T') *
        (m (S'.biUnion A \ B) + m (T'.biUnion A \ B) - m ((S' ∪ T').biUnion A \ B)) := by
  -- (12.43)–(12.46)
  have h₁ : ∑ S' ∈ S.powerset, ∑ T' ∈ T.powerset,
      (-1 : ℝ) ^ (#S' + #T') * m (S'.biUnion A \ B) = 0 := by
    refine sum_eq_zero fun S' _ => ?_
    have e : ∀ T' : Finset κ, (-1 : ℝ) ^ (#S' + #T') * m (S'.biUnion A \ B) =
        (-1 : ℝ) ^ #S' * m (S'.biUnion A \ B) * (-1 : ℝ) ^ #T' := fun T' => by ring
    rw [sum_congr rfl fun T' _ => e T', ← mul_sum, sum_powerset_neg_one_pow_eq_zero hT, mul_zero]
  have h₂ : ∑ S' ∈ S.powerset, ∑ T' ∈ T.powerset,
      (-1 : ℝ) ^ (#S' + #T') * m (T'.biUnion A \ B) = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun T' _ => ?_
    have e : ∀ S' : Finset κ, (-1 : ℝ) ^ (#S' + #T') * m (T'.biUnion A \ B) =
        (-1 : ℝ) ^ #T' * m (T'.biUnion A \ B) * (-1 : ℝ) ^ #S' := fun S' => by ring
    rw [sum_congr rfl fun S' _ => e S', ← mul_sum, sum_powerset_neg_one_pow_eq_zero hS, mul_zero]
  have h₃ : ∑ S' ∈ S.powerset, ∑ T' ∈ T.powerset,
      (-1 : ℝ) ^ (#S' + #T') * m ((S' ∪ T').biUnion A \ B) =
        ∑ U ∈ (S ∪ T).powerset, (-1 : ℝ) ^ #U * m (U.biUnion A \ B) := by
    rw [sum_powerset_union_of_disjoint hST]
    refine sum_congr rfl fun S' hS' => sum_congr rfl fun T' hT' => ?_
    rw [card_union_of_disjoint (disjoint_of_subset_left (mem_powerset.1 hS')
      (disjoint_of_subset_right (mem_powerset.1 hT') hST))]
  -- (12.47), from Theorem 3.19
  have hne : (S ∪ T).Nonempty := hS.mono subset_union_left
  have h₄ := hm.inf_sdiff_eq_sum hne A B
  rw [inf'_eq_inf, inf_union, inf_eq_inter] at h₄
  have h₅ : ∑ U ∈ (S ∪ T).powerset, (-1 : ℝ) ^ #U * m (U.biUnion A \ B) =
      -∑ U ∈ (S ∪ T).powerset with U.Nonempty, (-1 : ℝ) ^ (#U + 1) * m (U.biUnion A \ B) := by
    rw [← sum_filter_add_sum_filter_not (S ∪ T).powerset (fun U => U.Nonempty)]
    have h0 : ∑ U ∈ (S ∪ T).powerset with ¬U.Nonempty, (-1 : ℝ) ^ #U * m (U.biUnion A \ B) =
        0 := by
      refine sum_eq_zero fun U hU => ?_
      rw [not_nonempty_iff_eq_empty.1 (mem_filter.1 hU).2, biUnion_empty, empty_sdiff,
        hm.map_empty, mul_zero]
    rw [h0, add_zero, ← sum_neg_distrib]
    exact sum_congr rfl fun U _ => by ring
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  rw [h₁, h₂, h₃, h₅, h₄]
  ring

section IMeasure

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, Fintype (A i)] {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

/-- `μ*(X̃_G - X̃_B) = H(X_{B ∪ G}) - H(X_B)`. -/
lemma iMeasure_tilde_sdiff (hμ : IsPMF μ) (G B : Finset ι) :
    iMeasure μ X (tilde G \ tilde B) = blockEntropy μ X (B ∪ G) - blockEntropy μ X B := by
  rw [(isSignedMeasure_iMeasure μ X).sdiff_eq, ← tilde_union, iMeasure_tilde hμ,
    iMeasure_tilde hμ, union_comm]
  rfl

/-- `condInfo` of the entropy function is the value of `μ*` on `X̃_S ∩ X̃_T - X̃_K`. -/
lemma condInfo_blockEntropy_eq_iMeasure (hμ : IsPMF μ) (S T K : Finset ι) :
    condInfo (blockEntropy μ X) S T K = iMeasure μ X ((tilde S ∩ tilde T) \ tilde K) := by
  rw [iMeasure_inter_sdiff_eq_blockEntropy hμ (union_comm S K) (union_comm T K)
    (by rw [union_comm, ← union_assoc])]
  rfl

omit [Fintype ι] in
/-- The atoms in `⋂_{l ∈ U} X̃ₗ - X̃_V` are those containing `U` and disjoint from `V`. -/
lemma mem_inf_tilde_sdiff [Fintype ι] {U V : Finset ι} {a : NAtom ι} :
    a ∈ U.inf (fun l => tilde {l}) \ tilde V ↔ U ⊆ a.1 ∧ Disjoint a.1 V := by
  simp only [mem_sdiff, mem_inf, mem_tilde, mem_singleton, exists_eq_left, subset_iff,
    disjoint_right, not_exists, not_and]

/-- **Lemma 12.7**, for two collections. If `I(X_{G₁}; X_{G₂} | X_B) = 0` for disjoint nonempty
`G₁` and `G₂`, then `μ*(⋂_{l ∈ G₁ ∪ G₂} X̃ₗ - X̃_B) = 0` (12.48)–(12.49). -/
theorem iMeasure_inf_sdiff_eq_zero_of_condInfo (hμ : IsPMF μ) {G₁ G₂ B : Finset ι}
    (hd : Disjoint G₁ G₂) (h₁ : G₁.Nonempty) (h₂ : G₂.Nonempty)
    (hI : condInfo (blockEntropy μ X) G₁ G₂ B = 0) :
    iMeasure μ X ((G₁ ∪ G₂).inf (fun l => tilde {l}) \ tilde B) = 0 := by
  have hf := isPolymatroid_blockEntropy (X := X) hμ
  rw [inf_union, inf_eq_inter,
    (isSignedMeasure_iMeasure μ X).inf_inter_inf_sdiff_eq_sum h₁ h₂ hd]
  refine sum_eq_zero fun S' hS' => sum_eq_zero fun T' hT' => ?_
  rw [biUnion_tilde_singleton, biUnion_tilde_singleton, biUnion_tilde_singleton,
    iMeasure_tilde_sdiff hμ, iMeasure_tilde_sdiff hμ, iMeasure_tilde_sdiff hμ]
  have h0 := hf.condInfo_nonneg S' T' B
  have hle := hf.condInfo_mono (mem_powerset.1 hS') (mem_powerset.1 hT') B
  have h : condInfo (blockEntropy μ X) S' T' B = 0 := by linarith
  simp only [condInfo] at h
  rw [← union_assoc]
  linear_combination (-1 : ℝ) ^ (#S' + #T') * h

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
/-- `H(X_{⋃_{j ∈ s} Qⱼ} | X_T) = H(X_{T ∪ ⋃_{j ∈ s} Qⱼ}) - H(X_T)`. -/
lemma condEntropy_blockRV_blocks (hμ : IsPMF μ) (Q : κ → Finset ι) (T : Finset ι)
    (s : Finset κ) :
    H[blockRV (fun j => blockRV X (Q j)) s | blockRV X T ; μ] =
      blockEntropy μ X (T ∪ s.biUnion Q) - blockEntropy μ X T := by
  rw [condEntropy_eq_sub hμ, (((RVEquiv.refl _).pair (rvEquiv_blockRV_biUnion X Q s)).trans
    (rvEquiv_blockRV_union X T _)).entropy_eq hμ]
  rfl

omit [Fintype ι] in
/-- `H(X_G | X_T) = H(X_{T ∪ G}) - H(X_T)`. -/
lemma condEntropy_blockRV (hμ : IsPMF μ) (G T : Finset ι) :
    H[blockRV X G | blockRV X T ; μ] = blockEntropy μ X (T ∪ G) - blockEntropy μ X T := by
  rw [condEntropy_eq_sub hμ, (rvEquiv_blockRV_union X T G).entropy_eq hμ]
  rfl

omit [Fintype ι] [DecidableEq κ] in
/-- **Theorem 12.2** for blocks: `X_{Qⱼ}`, `j ∈ κ`, are mutually independent conditioning on
`X_T` if and only if `H(X_{T ∪ ⋃ Qⱼ}) - H(X_T) = ∑ⱼ (H(X_{T ∪ Qⱼ}) - H(X_T))`. -/
theorem condMutIndep_blocks_iff_sum (hμ : IsPMF μ) (Q : κ → Finset ι) (T : Finset ι) :
    CondMutIndep μ (fun j => blockRV X (Q j)) (blockRV X T) ↔
      blockEntropy μ X (T ∪ univ.biUnion Q) - blockEntropy μ X T =
        ∑ j, (blockEntropy μ X (T ∪ Q j) - blockEntropy μ X T) := by
  classical
  rw [condMutIndep_iff_condEntropy_eq_sum hμ, condEntropy_eq_condEntropy_blockRV_univ hμ,
    condEntropy_blockRV_blocks hμ]
  simp only [condEntropy_blockRV hμ]

omit [Fintype ι] in
/-- **Theorem 12.3** for blocks: `X_{Qⱼ}`, `j ∈ κ`, are mutually independent conditioning on
`X_T` if and only if `I(X_{Qᵢ}; X_{⋃_{j ≠ i} Qⱼ} | X_T) = 0` for all `i`. -/
theorem condMutIndep_blocks_iff_condInfo (hμ : IsPMF μ) (Q : κ → Finset ι) (T : Finset ι) :
    CondMutIndep μ (fun j => blockRV X (Q j)) (blockRV X T) ↔
      ∀ i, condInfo (blockEntropy μ X) (Q i) ((univ.erase i).biUnion Q) T = 0 := by
  rw [condMutIndep_iff_condMutualInfo_eq_zero hμ]
  refine forall_congr' fun i => ?_
  rw [condMutualInfo_eq_blockEntropy hμ (RVEquiv.refl _) (rvEquiv_blockRV_biUnion X Q _)
    (RVEquiv.refl _), condInfo, ← union_assoc]
  constructor <;> intro h <;> linarith

omit [Fintype ι] [∀ i, Fintype (A i)] [DecidableEq κ] in
/-- **Theorem 12.5.** If `X_{Qⱼ}`, `j ∈ κ`, are mutually independent conditioning on `X_C`, and
`Wⱼ ⊆ Qⱼ`, then `X_{Wⱼ}`, `j ∈ κ`, are mutually independent conditioning on
`(X_C, X_{Qⱼ - Wⱼ}, j ∈ κ)`. The book keeps only the `Wⱼ` that are nonempty; the others are
constant and do not affect the mutual independence. -/
theorem condMutIndep_blocks_sdiff [∀ i, Finite (A i)] (hμ : IsPMF μ) {C : Finset ι}
    {Q W : κ → Finset ι} (hW : ∀ j, W j ⊆ Q j)
    (h : CondMutIndep μ (fun j => blockRV X (Q j)) (blockRV X C)) :
    CondMutIndep μ (fun j => blockRV X (W j))
      (blockRV X (C ∪ univ.biUnion fun j => Q j \ W j)) := by
  classical
  have : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite _
  set f := blockEntropy μ X with hfdef
  have hf : IsPolymatroid f := isPolymatroid_blockEntropy hμ
  set R : Finset κ → Finset ι := fun s => s.biUnion fun j => Q j \ W j with hR
  rw [condMutIndep_blocks_iff_sum hμ] at h ⊢
  have hU : C ∪ R univ ∪ univ.biUnion W = C ∪ univ.biUnion Q := by
    ext l
    simp only [hR, mem_union, mem_biUnion, mem_univ, true_and, mem_sdiff]
    constructor
    · rintro ((h | ⟨j, hj, -⟩) | ⟨j, hj⟩)
      exacts [Or.inl h, Or.inr ⟨j, hj⟩, Or.inr ⟨j, hW j hj⟩]
    · rintro (h | ⟨j, hj⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hl : l ∈ W j
        · exact Or.inr ⟨j, hl⟩
        · exact Or.inl (Or.inr ⟨j, hj, hl⟩)
  -- (12.29)–(12.33), by induction on the set of indices
  have key : ∀ s : Finset κ, ∑ j ∈ s, (f (C ∪ R univ ∪ W j) - f (C ∪ R univ)) +
      f (C ∪ R s) - f C ≤ ∑ j ∈ s, (f (C ∪ Q j) - f C) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hR]
    | insert a s ha ih =>
      rw [sum_insert ha, sum_insert ha]
      have hRs : R (insert a s) = (Q a \ W a) ∪ R s := biUnion_insert
      have h₁ := hf.sub_le_sub (subset_union_left : C ⊆ C ∪ R s) (Q a)
      have hsub : C ∪ R (insert a s) ⊆ C ∪ R univ :=
        union_subset_union_right (biUnion_subset_biUnion_of_subset_left _ (subset_univ _))
      have h₂ := hf.sub_le_sub hsub (W a)
      have e : C ∪ R (insert a s) ∪ W a = C ∪ R s ∪ Q a := by
        rw [hRs]
        ext l
        have := @hW a l
        simp only [mem_union, mem_sdiff]
        tauto
      rw [e] at h₂
      linarith
  have h₃ := key univ
  have h₄ := hf.sub_le_sum (C ∪ R univ) W univ
  rw [hU] at h₄ ⊢
  linarith

omit [DecidableEq κ] in
/-- **Lemma 12.7.** If `X_{Wⱼ}`, `j ∈ κ`, with disjoint `Wⱼ`, are mutually independent conditioning
on `X_B`, and at least two of the `Wⱼ` are nonempty, then `μ*(⋂_{l ∈ ⋃ Wⱼ} X̃ₗ - X̃_B) = 0`
(12.40). -/
theorem iMeasure_inf_sdiff_eq_zero_of_condMutIndep (hμ : IsPMF μ) {W : κ → Finset ι}
    (hW : Pairwise (Disjoint on W)) {B : Finset ι}
    (h : CondMutIndep μ (fun j => blockRV X (W j)) (blockRV X B)) {j₀ j₁ : κ} (hj : j₀ ≠ j₁)
    (h₀ : (W j₀).Nonempty) (h₁ : (W j₁).Nonempty) :
    iMeasure μ X ((univ.biUnion W).inf (fun l => tilde {l}) \ tilde B) = 0 := by
  classical
  have hI := (condMutIndep_blocks_iff_condInfo hμ W B).1 h j₀
  have hU : univ.biUnion W = W j₀ ∪ (univ.erase j₀).biUnion W := by
    rw [← biUnion_insert, insert_erase (mem_univ _)]
  rw [hU]
  refine iMeasure_inf_sdiff_eq_zero_of_condInfo hμ ?_ h₀ ?_ hI
  · rw [disjoint_biUnion_right]
    exact fun j hj => hW (ne_of_mem_erase hj).symm
  · exact h₁.mono (subset_biUnion_of_mem W (mem_erase.2 ⟨hj.symm, mem_univ _⟩))

omit [DecidableEq κ] in
/-- **Theorem 12.9.** For disjoint index sets `Qⱼ`, `j ∈ κ`, the blocks `X_{Qⱼ}` are mutually
independent conditioning on `X_T` if and only if `μ*(⋂_{l ∈ ⋃ Wⱼ} X̃ₗ - X̃_{T ∪ ⋃ (Qⱼ - Wⱼ)}) = 0`
for all `Wⱼ ⊆ Qⱼ` such that at least two of the `Wⱼ` are nonempty (12.52). -/
theorem condMutIndep_blocks_iff_iMeasure (hμ : IsPMF μ) {T : Finset ι} {Q : κ → Finset ι}
    (hQ : Pairwise (Disjoint on Q)) :
    CondMutIndep μ (fun j => blockRV X (Q j)) (blockRV X T) ↔
      ∀ W : κ → Finset ι, (∀ j, W j ⊆ Q j) →
        (∃ j j', j ≠ j' ∧ (W j).Nonempty ∧ (W j').Nonempty) →
          iMeasure μ X ((univ.biUnion W).inf (fun l => tilde {l}) \
            tilde (T ∪ univ.biUnion fun j => Q j \ W j)) = 0 := by
  classical
  constructor
  · rintro h W hW ⟨j, j', hjj, hj, hj'⟩
    exact iMeasure_inf_sdiff_eq_zero_of_condMutIndep hμ
      (fun a b hab => disjoint_of_subset_left (hW a) (disjoint_of_subset_right (hW b) (hQ hab)))
      (condMutIndep_blocks_sdiff hμ hW h) hjj hj hj'
  · -- (12.55)–(12.65), through the conditional independencies of Theorem 12.3
    intro h
    rw [condMutIndep_blocks_iff_condInfo hμ]
    intro i
    rw [condInfo_blockEntropy_eq_iMeasure hμ, (isSignedMeasure_iMeasure μ X).eq_sum_singleton]
    set F := (tilde (Q i) ∩ tilde ((univ.erase i).biUnion Q)) \ tilde T with hF
    have hmaps : ∀ a ∈ F, (fun j => a.1 ∩ Q j) ∈ (Fintype.piFinset fun j => (Q j).powerset).filter
        fun W => (W i).Nonempty ∧ ∃ j ≠ i, (W j).Nonempty := by
      intro a ha
      simp only [hF, mem_sdiff, mem_inter, mem_tilde] at ha
      obtain ⟨⟨⟨l, hlQ, hla⟩, ⟨l', hl'R, hl'a⟩⟩, -⟩ := ha
      rw [mem_filter, Fintype.mem_piFinset]
      refine ⟨fun j => mem_powerset.2 inter_subset_right, ⟨l, mem_inter.2 ⟨hla, hlQ⟩⟩, ?_⟩
      obtain ⟨j, hj, hl'j⟩ := mem_biUnion.1 hl'R
      exact ⟨j, ne_of_mem_erase hj, l', mem_inter.2 ⟨hl'a, hl'j⟩⟩
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_eq_zero fun W hW => ?_
    rw [mem_filter, Fintype.mem_piFinset] at hW
    obtain ⟨hWQ', hWi, j, hji, hWj⟩ := hW
    have hWQ : ∀ j, W j ⊆ Q j := fun j => mem_powerset.1 (hWQ' j)
    have e : F.filter (fun a => (fun j => a.1 ∩ Q j) = W) = (univ.biUnion W).inf
        (fun l => tilde {l}) \ tilde (T ∪ univ.biUnion fun j => Q j \ W j) := by
      ext a
      rw [mem_filter, mem_inf_tilde_sdiff]
      constructor
      · rintro ⟨haF, hkey⟩
        have hk : ∀ j, a.1 ∩ Q j = W j := fun j => congrFun hkey j
        simp only [hF, mem_sdiff, mem_tilde, not_exists, not_and] at haF
        refine ⟨fun l hl => ?_, ?_⟩
        · obtain ⟨j, -, hlj⟩ := mem_biUnion.1 hl
          rw [← hk j] at hlj
          exact (mem_inter.1 hlj).1
        · rw [disjoint_union_right, disjoint_biUnion_right]
          refine ⟨disjoint_right.2 fun l hl hla => haF.2 l hl hla, fun j _ => ?_⟩
          rw [← hk j, disjoint_left]
          intro l hla hl
          exact (mem_sdiff.1 hl).2 (mem_inter.2 ⟨hla, (mem_sdiff.1 hl).1⟩)
      · rintro ⟨hsub, hdisj⟩
        rw [disjoint_union_right, disjoint_biUnion_right] at hdisj
        have hk : ∀ j, a.1 ∩ Q j = W j := fun j => by
          ext l
          constructor
          · intro hl
            rw [mem_inter] at hl
            by_contra hlW
            exact disjoint_left.1 (hdisj.2 j (mem_univ j)) hl.1 (mem_sdiff.2 ⟨hl.2, hlW⟩)
          · intro hl
            exact mem_inter.2 ⟨hsub (mem_biUnion.2 ⟨j, mem_univ j, hl⟩), hWQ j hl⟩
        refine ⟨?_, funext hk⟩
        simp only [hF, mem_sdiff, mem_inter, mem_tilde]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · obtain ⟨l, hl⟩ := hWi
          exact ⟨l, hWQ i hl, hsub (mem_biUnion.2 ⟨i, mem_univ _, hl⟩)⟩
        · obtain ⟨l, hl⟩ := hWj
          exact ⟨l, mem_biUnion.2 ⟨j, mem_erase.2 ⟨hji, mem_univ _⟩, hWQ j hl⟩,
            hsub (mem_biUnion.2 ⟨j, mem_univ _, hl⟩)⟩
        · rintro ⟨l, hlT, hla⟩
          exact disjoint_left.1 hdisj.1 hla hlT
    rw [e, ← (isSignedMeasure_iMeasure μ X).eq_sum_singleton]
    exact h W hWQ ⟨i, j, hji.symm, hWi, hWj⟩

end IMeasure

/-! ### Full conditional mutual independencies -/

/-- A conditional mutual independency `K = (T, Qᵢ, 1 ≤ i ≤ k)` on random variables `Xₗ`, `l ∈ ι`:
the blocks `X_{Qᵢ}` are mutually independent conditioning on `X_T`. -/
structure FCMI (ι : Type*) where
  /-- The index set `T` of the conditioning variables. -/
  cond : Finset ι
  /-- The index sets `Qᵢ` of the mutually independent blocks. -/
  parts : Finset (Finset ι)

namespace FCMI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Definition 12.11.** A conditional mutual independency is *full* (an FCMI) if all the
variables are involved: `T` and the `Qᵢ` are disjoint and their union is everything (12.67). -/
def IsFull (K : FCMI ι) : Prop :=
  (∀ q ∈ K.parts, Disjoint K.cond q) ∧ (K.parts : Set (Finset ι)).PairwiseDisjoint id ∧
    K.cond ∪ K.parts.biUnion id = univ

/-- The conditional mutual independency `K` holds for the random variables `X`. -/
def Holds {Ω : Type*} [Fintype Ω] {A : ι → Type*} (μ : Ω → ℝ) (X : ∀ i, Ω → A i)
    (K : FCMI ι) : Prop :=
  CondMutIndep μ (fun q : K.parts => blockRV X q.1) (blockRV X K.cond)

open Classical in
/-- **Definition 12.13.** The image `Im(K)` of `K`: the atoms of the form
`⋂_{l ∈ ⋃ Wᵢ} X̃ₗ - X̃_{T ∪ ⋃ (Qᵢ - Wᵢ)}` (12.57), with `Wᵢ ⊆ Qᵢ` and at least two `Wᵢ` nonempty.
-/
def image (K : FCMI ι) : Finset (NAtom ι) :=
  univ.filter fun a => ∃ W : K.parts → Finset ι, (∀ q, W q ⊆ q.1) ∧
    (∃ q q', q ≠ q' ∧ (W q).Nonempty ∧ (W q').Nonempty) ∧
      ({a} : Finset (NAtom ι)) = (univ.biUnion W).inf (fun l => tilde {l}) \
        tilde (K.cond ∪ univ.biUnion fun q => q.1 \ W q)

lemma mem_image {K : FCMI ι} {a : NAtom ι} : a ∈ K.image ↔ ∃ W : K.parts → Finset ι,
    (∀ q, W q ⊆ q.1) ∧ (∃ q q', q ≠ q' ∧ (W q).Nonempty ∧ (W q').Nonempty) ∧
      ({a} : Finset (NAtom ι)) = (univ.biUnion W).inf (fun l => tilde {l}) \
        tilde (K.cond ∪ univ.biUnion fun q => q.1 \ W q) := by
  rw [image, mem_filter]
  exact and_iff_right (mem_univ a)

/-- `IsFull` in a decidable form. -/
lemma isFull_iff {K : FCMI ι} : K.IsFull ↔ (∀ q ∈ K.parts, Disjoint K.cond q) ∧
    (∀ q ∈ K.parts, ∀ q' ∈ K.parts, q ≠ q' → Disjoint q q') ∧
      K.cond ∪ K.parts.biUnion id = univ := Iff.rfl

lemma pairwise_disjoint {K : FCMI ι} (hK : K.IsFull) :
    Pairwise (Disjoint on fun q : K.parts => q.1) :=
  fun q q' hqq' => hK.2.1 q.2 q'.2 fun h => hqq' (Subtype.ext h)

/-- For an FCMI, the set (12.57) is the atom `⋂_{l ∈ ⋃ Wᵢ} X̃ₗ - X̃_{(⋃ Wᵢ)ᶜ}`, (12.72). -/
lemma inf_tilde_sdiff_eq_singleton {K : FCMI ι} (hK : K.IsFull) {W : K.parts → Finset ι}
    (hW : ∀ q, W q ⊆ q.1) (hne : (univ.biUnion W).Nonempty) :
    (univ.biUnion W).inf (fun l => tilde {l}) \ tilde (K.cond ∪ univ.biUnion fun q => q.1 \ W q) =
      {⟨univ.biUnion W, hne⟩} := by
  ext b
  rw [mem_inf_tilde_sdiff, mem_singleton]
  constructor
  · rintro ⟨hsub, hdisj⟩
    refine Subtype.ext (Finset.ext fun l => ⟨fun hl => ?_, fun hl => hsub hl⟩)
    have hcov : l ∈ K.cond ∪ K.parts.biUnion id := hK.2.2 ▸ mem_univ l
    rw [disjoint_union_right, disjoint_biUnion_right] at hdisj
    rcases mem_union.1 hcov with hT | hQ
    · exact absurd hT (disjoint_left.1 hdisj.1 hl)
    · obtain ⟨q, hq, hlq⟩ := mem_biUnion.1 hQ
      by_contra hlW
      refine disjoint_left.1 (hdisj.2 ⟨q, hq⟩ (mem_univ _)) hl (mem_sdiff.2 ⟨hlq, ?_⟩)
      exact fun h => hlW (mem_biUnion.2 ⟨⟨q, hq⟩, mem_univ _, h⟩)
  · rintro rfl
    refine ⟨subset_rfl, ?_⟩
    rw [disjoint_union_right, disjoint_biUnion_right]
    refine ⟨(disjoint_biUnion_left _ _ _).2 fun q _ =>
      disjoint_of_subset_left (hW q) (hK.1 q.1 q.2).symm, fun q' _ => ?_⟩
    rw [disjoint_biUnion_left]
    intro q _
    by_cases hqq : q = q'
    · subst hqq
      exact disjoint_sdiff
    · exact disjoint_of_subset_left (hW q) (disjoint_of_subset_right sdiff_subset
        (pairwise_disjoint hK hqq))

/-- **Proposition 12.15.** For an FCMI `K = (T, Qᵢ)`, `Im(K)` is the set of atoms in
`⋃_{i < j} (X̃_{Qᵢ} ∩ X̃_{Qⱼ} - X̃_T)` (12.69). -/
theorem mem_image_iff {K : FCMI ι} (hK : K.IsFull) {a : NAtom ι} :
    a ∈ K.image ↔
      ∃ q ∈ K.parts, ∃ q' ∈ K.parts, q ≠ q' ∧ a ∈ (tilde q ∩ tilde q') \ tilde K.cond := by
  rw [mem_image]
  constructor
  · rintro ⟨W, hW, ⟨q, q', hqq', ⟨l, hl⟩, ⟨l', hl'⟩⟩, ha⟩
    have hmem : a ∈ (univ.biUnion W).inf (fun l => tilde {l}) \
        tilde (K.cond ∪ univ.biUnion fun q => q.1 \ W q) := ha ▸ mem_singleton_self a
    rw [mem_inf_tilde_sdiff, disjoint_union_right] at hmem
    refine ⟨q.1, q.2, q'.1, q'.2, fun h => hqq' (Subtype.ext h), ?_⟩
    simp only [mem_sdiff, mem_inter, mem_tilde, not_exists, not_and]
    refine ⟨⟨⟨l, hW q hl, hmem.1 (mem_biUnion.2 ⟨q, mem_univ _, hl⟩)⟩,
      ⟨l', hW q' hl', hmem.1 (mem_biUnion.2 ⟨q', mem_univ _, hl'⟩)⟩⟩, fun l hl hla => ?_⟩
    exact disjoint_left.1 hmem.2.1 hla hl
  · rintro ⟨q, hq, q', hq', hqq', ha⟩
    simp only [mem_sdiff, mem_inter, mem_tilde, not_exists, not_and] at ha
    obtain ⟨⟨⟨l, hlq, hla⟩, ⟨l', hlq', hla'⟩⟩, haT⟩ := ha
    set W : K.parts → Finset ι := fun p => a.1 ∩ p.1 with hWdef
    have hW : ∀ p, W p ⊆ p.1 := fun p => inter_subset_right
    have hUa : univ.biUnion W = a.1 := by
      ext m
      simp only [hWdef, mem_biUnion, mem_univ, true_and, mem_inter]
      constructor
      · rintro ⟨_, hm, -⟩
        exact hm
      · intro hm
        have hcov : m ∈ K.cond ∪ K.parts.biUnion id := hK.2.2 ▸ mem_univ m
        rcases mem_union.1 hcov with hT | hQ
        · exact absurd hm (haT m hT)
        · obtain ⟨p, hp, hmp⟩ := mem_biUnion.1 hQ
          exact ⟨⟨p, hp⟩, hm, hmp⟩
    have hne : (univ.biUnion W).Nonempty := hUa ▸ a.2
    refine ⟨W, hW, ⟨⟨q, hq⟩, ⟨q', hq'⟩, fun h => hqq' (congrArg Subtype.val h),
      ⟨l, mem_inter.2 ⟨hla, hlq⟩⟩, ⟨l', mem_inter.2 ⟨hla', hlq'⟩⟩⟩, ?_⟩
    rw [inf_tilde_sdiff_eq_singleton hK hW hne]
    congr 1
    exact Subtype.ext hUa.symm

/-- **Proposition 12.14.** For a full conditional independency `K = (T, Q₁, Q₂)`, `Im(K)` is the
set of atoms in `X̃_{Q₁} ∩ X̃_{Q₂} - X̃_T` (12.68). -/
theorem mem_image_iff_of_parts_eq_pair {K : FCMI ι} (hK : K.IsFull) {Q₁ Q₂ : Finset ι}
    (hQ : Q₁ ≠ Q₂) (hp : K.parts = {Q₁, Q₂}) {a : NAtom ι} :
    a ∈ K.image ↔ a ∈ (tilde Q₁ ∩ tilde Q₂) \ tilde K.cond := by
  rw [mem_image_iff hK, hp]
  constructor
  · rintro ⟨q, hq, q', hq', hqq', ha⟩
    simp only [mem_insert, mem_singleton] at hq hq'
    rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl
    · exact absurd rfl hqq'
    · exact ha
    · rwa [inter_comm]
    · exact absurd rfl hqq'
  · intro ha
    exact ⟨Q₁, by simp, Q₂, by simp, hQ, ha⟩

variable {Ω : Type*} [Fintype Ω] {A : ι → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}
  {X : ∀ i, Ω → A i}

/-- **Theorem 12.17.** An FCMI `K` holds if and only if `μ*` vanishes on `Im(K)`. -/
theorem holds_iff (hμ : IsPMF μ) {K : FCMI ι} (hK : K.IsFull) :
    K.Holds μ X ↔ ∀ a ∈ K.image, iMeasure μ X {a} = 0 := by
  rw [Holds, condMutIndep_blocks_iff_iMeasure hμ (pairwise_disjoint hK)]
  constructor
  · intro h a ha
    obtain ⟨W, hW, h2, ha⟩ := mem_image.1 ha
    rw [ha]
    exact h W hW h2
  · rintro h W hW ⟨q, q', hqq', hq, hq'⟩
    have hne : (univ.biUnion W).Nonempty := hq.mono (subset_biUnion_of_mem W (mem_univ q))
    rw [inf_tilde_sdiff_eq_singleton hK hW hne]
    refine h _ (mem_image.2 ⟨W, hW, ⟨q, q', hqq', hq, hq'⟩, ?_⟩)
    rw [inf_tilde_sdiff_eq_singleton hK hW hne]

end FCMI

/-- **Definition 12.18.** The image `Im(P) = ⋃_{K ∈ P} Im(K)` of a set `P` of FCMIs (12.78). -/
def fcmiImage {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Set (FCMI ι)) : Set (NAtom ι) :=
  ⋃ K ∈ P, (K.image : Set (NAtom ι))

namespace FCMI

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **Theorem 12.19.** A set `P` of FCMIs holds if and only if `μ*` vanishes on `Im(P)`. -/
theorem holds_set_iff {Ω : Type*} [Fintype Ω] {A : ι → Type*} [∀ i, Fintype (A i)]
    {μ : Ω → ℝ} {X : ∀ i, Ω → A i} (hμ : IsPMF μ) {P : Set (FCMI ι)}
    (hP : ∀ K ∈ P, K.IsFull) :
    (∀ K ∈ P, K.Holds μ X) ↔ ∀ a ∈ fcmiImage P, iMeasure μ X {a} = 0 := by
  simp only [fcmiImage, Set.mem_iUnion, mem_coe]
  constructor
  · rintro h a ⟨K, hK, ha⟩
    exact (holds_iff hμ (hP K hK)).1 (h K hK) a ha
  · exact fun h K hK => (holds_iff hμ (hP K hK)).2 fun a ha => h a ⟨K, hK, ha⟩

/-- A set `P₁` of conditional mutual independencies implies another set `P₂` if `P₂` holds for
all random variables `Xₗ`, `l ∈ ι`, for which `P₁` holds. -/
def Implies (P₁ P₂ : Set (FCMI ι)) : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (A : ι → Type u) [∀ i, Fintype (A i)] (μ : Ω → ℝ)
    (X : ∀ i, Ω → A i), IsPMF μ → (∀ K ∈ P₁, K.Holds μ X) → ∀ K ∈ P₂, K.Holds μ X

/-- **Theorem 12.20.** A set `P₁` of FCMIs implies a set `P₂` of FCMIs if and only if
`Im(P₂) ⊆ Im(P₁)`. -/
theorem implies_iff {P₁ P₂ : Set (FCMI ι)} (h₁ : ∀ K ∈ P₁, K.IsFull)
    (h₂ : ∀ K ∈ P₂, K.IsFull) : Implies P₁ P₂ ↔ fcmiImage P₂ ⊆ fcmiImage P₁ := by
  classical
  constructor
  · intro himp a ha
    by_contra ha₁
    -- Theorem 3.11: `μ*` vanishes on all atoms except `a`
    obtain ⟨Ω, _, A, _, μ, X, hμ, hv⟩ :=
      exists_iMeasure_eq (fun b : NAtom ι => if b = a then (1 : ℝ) else 0)
        fun b => by split_ifs <;> norm_num
    have hP₁ : ∀ K ∈ P₁, K.Holds μ X := (holds_set_iff hμ h₁).2 fun b hb => by
      rw [hv, ite_eq_right_iff]
      rintro rfl
      exact absurd hb ha₁
    have := (holds_set_iff hμ h₂).1 (himp Ω A μ X hμ hP₁) a ha
    simp [hv] at this
  · intro hsub Ω _ A _ μ X hμ hP₁
    exact (holds_set_iff hμ h₂).2 fun a ha => (holds_set_iff hμ h₁).1 hP₁ a (hsub ha)

/-- **Corollary 12.21.** Two sets of FCMIs are equivalent if and only if their images are equal. -/
theorem equiv_iff {P₁ P₂ : Set (FCMI ι)} (h₁ : ∀ K ∈ P₁, K.IsFull) (h₂ : ∀ K ∈ P₂, K.IsFull) :
    Implies P₁ P₂ ∧ Implies P₂ P₁ ↔ fcmiImage P₁ = fcmiImage P₂ := by
  rw [implies_iff h₁ h₂, implies_iff h₂ h₁, Set.Subset.antisymm_iff, and_comm]

end FCMI

end InfoTheory
