/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.InfoInequalities.EntropicRegion

/-!
# The Zhang–Yeung inequalities

For random variables `X₁, X₂, X₃, X₄`, let `(X̃₁, X̃₂)` be a copy of `(X₁, X₂)` over
`(X₃, X₄)`: the joint distribution of `(X₁, X₂, X₃, X₄, X̃₁, X̃₂)` is
`p(x₁x₂x₃x₄) p(x̃₁x̃₂x₃x₄) / p(x₃x₄)` (15.63), so that `(X̃₁, X̃₂, X₃, X₄)` has the same
distribution as `(X₁, X₂, X₃, X₄)` and `(X₁, X₂) → (X₃, X₄) → (X̃₁, X̃₂)` is a Markov chain
(Lemma 15.8). The basic inequalities for the six random variables then give the unconstrained
non-Shannon-type inequality (Theorem 15.7)
`2 I(X₃; X₄) ≤ I(X₁; X₂) + I(X₁; X₃, X₄) + 3 I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂)`.

The copy is realized on the sample space `Ω × Ω`, and its entropy function on the six indices
`0, …, 5` (for `X₁, X₂, X₃, X₄, X̃₁, X̃₂`) is a polymatroid `f` with three properties: it extends
the entropy function `h` of `X₁, …, X₄` (`copy_fst`), its restriction to `X̃₁, X̃₂, X₃, X₄` is `h`
again (`copy_snd`), and it satisfies the Markov condition (`copy_markov`). The inequality is a
linear consequence of these (`zhangYeung_of_copy`).

## Main statements

* `copyMeasure`, `isPMF_copyMeasure`, `copyEntropy`: the copy (15.63) and its entropy function.
* `copy_markov`, `copy_snd`, `dist_copyMeasure_copyVec`: **Lemma 15.8**; `copy_fst`.
* `condInfo_sub_sub_le_of_markov`, `condInfo_sub_two_mul_le_of_markov`: **Lemmas 15.9 and 15.10**,
  for a polymatroid on six indices.
* `zhangYeung_of_copy`: (15.77)–(15.84).
* `zhangYeung`: **Theorem 15.7**.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 15.2
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Shannon's information measures of blocks -/

section Blocks

variable {Ω ι β γ δ : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, Fintype (A i)] [Fintype β] [Fintype γ] [Fintype δ] {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

omit [Fintype ι] in
/-- `I(U; V | W) = condInfo h G G' K` for `U`, `V`, `W` equivalent to `X_G`, `X_G'`, `X_K`. -/
lemma condMutualInfo_eq_condInfo [Finite ι] (hμ : IsPMF μ) {U : Ω → β} {V : Ω → γ} {W : Ω → δ}
    {G G' K : Finset ι} (hU : RVEquiv U (blockRV X G)) (hV : RVEquiv V (blockRV X G'))
    (hW : RVEquiv W (blockRV X K)) :
    I[U : V | W ; μ] = condInfo (blockEntropy μ X) G G' K := by
  have := Fintype.ofFinite ι
  rw [← iMeasure_inter_sdiff hμ hU hV hW, condInfo_blockEntropy_eq_iMeasure hμ]

omit [Fintype ι] in
/-- `I(U; V) = condInfo h G G' ∅` for `U`, `V` equivalent to `X_G`, `X_G'`. -/
lemma mutualInfo_eq_condInfo [Finite ι] (hμ : IsPMF μ) {U : Ω → β} {V : Ω → γ} {G G' : Finset ι}
    (hU : RVEquiv U (blockRV X G)) (hV : RVEquiv V (blockRV X G')) :
    I[U : V ; μ] = condInfo (blockEntropy μ X) G G' ∅ := by
  have := Fintype.ofFinite ι
  rw [← iMeasure_inter hμ hU hV, condInfo_blockEntropy_eq_iMeasure hμ, tilde_empty, sdiff_empty]

omit [Fintype Ω] [Fintype ι] [∀ i, Fintype (A i)] in
lemma rvEquiv_pair_blockRV (X : ∀ i, Ω → A i) {i j : ι} :
    RVEquiv (pair (X i) (X j)) (blockRV X {i, j}) := by
  have := ((rvEquiv_blockRV_singleton X i).pair (rvEquiv_blockRV_singleton X j)).trans
    (rvEquiv_blockRV_union X {i} {j})
  rwa [singleton_union] at this

end Blocks

/-- `condInfo f S T K` through literal sets. -/
lemma condInfo_eq_of {ι : Type*} [DecidableEq ι] (f : Finset ι → ℝ) {S T K U₁ U₂ U₃ : Finset ι}
    (h₁ : K ∪ S = U₁) (h₂ : K ∪ T = U₂) (h₃ : K ∪ S ∪ T = U₃) :
    condInfo f S T K = f U₁ + f U₂ - f U₃ - f K := by
  subst h₁ h₂ h₃
  rfl

/-! ### The copy -/

section Copy

variable {Ω : Type*} [Fintype Ω] {A : Fin 4 → Type*} {μ : Ω → ℝ}

/-- The pair `(X₃, X₄)` over which the copy is made. -/
def copyBase (X : ∀ i, Ω → A i) : Ω → A 2 × A 3 := pair (X 2) (X 3)

open Classical in
/-- The distribution (15.63) on `Ω × Ω`: `μ(ω) μ(ω̃) / p(x₃x₄)` if `(X₃, X₄)` agree at `ω` and
`ω̃`, and `0` otherwise. -/
def copyMeasure (μ : Ω → ℝ) (X : ∀ i, Ω → A i) (q : Ω × Ω) : ℝ :=
  if copyBase X q.1 = copyBase X q.2 then
    μ q.1 * μ q.2 / dist μ (copyBase X) (copyBase X q.1) else 0

variable {X : ∀ i, Ω → A i}

lemma copyMeasure_symm (q : Ω × Ω) : copyMeasure μ X q.swap = copyMeasure μ X q := by
  simp only [copyMeasure, Prod.fst_swap, Prod.snd_swap]
  split_ifs with h₁ h₂ h₂
  · rw [h₁, mul_comm]
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · rfl

lemma copyMeasure_ne_zero {q : Ω × Ω} (h : copyMeasure μ X q ≠ 0) :
    copyBase X q.1 = copyBase X q.2 := by
  by_contra hne
  exact h (by simp [copyMeasure, hne])

variable [∀ i, Finite (A i)]

/-- The rows of the copy measure sum to `μ`. -/
lemma sum_copyMeasure (hμ : IsPMF μ) (ω : Ω) : ∑ ω', copyMeasure μ X (ω, ω') = μ ω := by
  classical
  have : ∀ i, Fintype (A i) := fun i => Fintype.ofFinite _
  have hd : dist μ (copyBase X) (copyBase X ω) =
      ∑ ω', μ ω' * (if copyBase X ω' = copyBase X ω then 1 else 0) := by
    have := sum_dist_mul μ (copyBase X) (fun a => if a = copyBase X ω then (1 : ℝ) else 0)
    simpa [mul_ite, mul_one, mul_zero, sum_ite_eq'] using this
  by_cases hk : dist μ (copyBase X) (copyBase X ω) = 0
  · have hω : μ ω = 0 := by
      have := dist_le_dist_comp hμ id (copyBase X) ω
      rw [dist_id] at this
      exact le_antisymm (by simpa [hk] using this) (hμ.nonneg ω)
    simp [copyMeasure, hω]
  · calc ∑ ω', copyMeasure μ X (ω, ω')
        = ∑ ω', μ ω / dist μ (copyBase X) (copyBase X ω) *
            (μ ω' * (if copyBase X ω' = copyBase X ω then 1 else 0)) :=
          sum_congr rfl fun ω' _ => by
            unfold copyMeasure
            split_ifs with h₁ h₂ h₂
            · ring
            · exact absurd h₁.symm h₂
            · exact absurd h₂.symm h₁
            · simp
      _ = μ ω := by rw [← mul_sum, ← hd, div_mul_cancel₀ _ hk]

lemma isPMF_copyMeasure (hμ : IsPMF μ) : IsPMF (copyMeasure μ X) := by
  refine ⟨fun q => ?_, ?_⟩
  · simp only [copyMeasure]
    split_ifs
    · exact div_nonneg (mul_nonneg (hμ.nonneg _) (hμ.nonneg _)) (dist_nonneg hμ _ _)
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    simp only [sum_copyMeasure hμ, hμ.sum_eq_one]

/-- The first coordinate of the copy has the distribution `μ`. -/
lemma dist_copyMeasure_fst (hμ : IsPMF μ) {γ : Type*} (F : Ω → γ) (c : γ) :
    dist (copyMeasure μ X) (fun q => F q.1) c = dist μ F c := by
  classical
  simp only [dist, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : F ω = c
  · simp [h, sum_copyMeasure hμ]
  · simp [h]

/-- The second coordinate of the copy has the distribution `μ`. -/
lemma dist_copyMeasure_snd (hμ : IsPMF μ) {γ : Type*} (F : Ω → γ) (c : γ) :
    dist (copyMeasure μ X) (fun q => F q.2) c = dist μ F c := by
  classical
  rw [← dist_copyMeasure_fst (X := X) hμ F c]
  simp only [dist]
  rw [← Equiv.sum_comp (Equiv.prodComm Ω Ω)]
  refine sum_congr rfl fun q _ => ?_
  simp only [Equiv.prodComm_apply, Prod.snd_swap, copyMeasure_symm]

omit [∀ i, Finite (A i)] in
/-- Two random variables that agree on the support of the copy measure have the same
distribution. -/
lemma dist_copyMeasure_congr {γ : Type*} {V W : Ω × Ω → γ}
    (h : ∀ q, copyMeasure μ X q ≠ 0 → V q = W q) (c : γ) :
    dist (copyMeasure μ X) V c = dist (copyMeasure μ X) W c := by
  refine sum_congr rfl fun q _ => ?_
  by_cases hq : copyMeasure μ X q = 0
  · simp [hq]
  · rw [h q hq]

/-- The vector `(X̃₁, X̃₂, X₃, X₄)` of the copy, as a full vector of values. -/
def copyVec (X : ∀ i, Ω → A i) (q : Ω × Ω) : ∀ i, A i :=
  fun i => X i (if i.val < 2 then q.2 else q.1)

/-- **Lemma 15.8**, the marginal: `(X̃₁, X̃₂, X₃, X₄)` has the distribution of
`(X₁, X₂, X₃, X₄)`. -/
lemma dist_copyMeasure_copyVec (hμ : IsPMF μ) {γ : Type*} (R : (∀ i, A i) → γ) (c : γ) :
    dist (copyMeasure μ X) (fun q => R (copyVec X q)) c = dist μ (fun ω => R fun i => X i ω) c := by
  rw [← dist_copyMeasure_snd (X := X) hμ]
  refine dist_copyMeasure_congr (fun q hq => ?_) c
  have hK := copyMeasure_ne_zero hq
  simp only [copyBase, pair, Prod.mk.injEq] at hK
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact hK.1
  · exact hK.2

end Copy

/-- `I(f U; g V | k W) = I(U; V | W)` for injective `f`, `g`, `k`. -/
lemma condMutualInfo_comp_injective {Ω α β γ α' β' γ' : Type*} [Fintype Ω] [Fintype α]
    [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ'] {μ : Ω → ℝ} (hμ : IsPMF μ)
    {U : Ω → α} {V : Ω → β} {W : Ω → γ} {f : α → α'} {g : β → β'} {k : γ → γ'}
    (hf : Function.Injective f) (hg : Function.Injective g) (hk : Function.Injective k) :
    I[f ∘ U : g ∘ V | k ∘ W ; μ] = I[U : V | W ; μ] := by
  rw [condMutualInfo, condMutualInfo,
    condEntropy_congr_left hμ (k ∘ W) f hf (Y := U) (Y' := f ∘ U) fun _ => rfl,
    condEntropy_congr_left hμ (pair (g ∘ V) (k ∘ W)) f hf (Y := U) (Y' := f ∘ U) fun _ => rfl,
    condEntropy_congr_right hμ U k hk (X := W) (X' := k ∘ W) fun _ => rfl,
    condEntropy_congr_right hμ U (Prod.map g k) (hg.prodMap hk) (X := pair V W)
      (X' := pair (g ∘ V) (k ∘ W)) fun _ => rfl]

section Six

variable {Ω : Type*} [Fintype Ω] {A : Fin 4 → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}
  {X : ∀ i, Ω → A i}

/-- The index among `X₁, …, X₄` of each of the six variables `X₁, X₂, X₃, X₄, X̃₁, X̃₂`. -/
def copyIdx : Fin 6 → Fin 4 := ![0, 1, 2, 3, 0, 1]

/-- Whether each of the six variables is read on the copy. -/
def copySide : Fin 6 → Bool := ![false, false, false, false, true, true]

/-- The six random variables `X₁, X₂, X₃, X₄, X̃₁, X̃₂` on `Ω × Ω`, with values tagged by their
index. -/
def copyFamily (X : ∀ i, Ω → A i) (j : Fin 6) (q : Ω × Ω) : Σ i, A i :=
  ⟨copyIdx j, X (copyIdx j) (if copySide j then q.2 else q.1)⟩

/-- `X₁, X₂, X₃, X₄` among the six variables. -/
def copyEmb₁ : Fin 4 ↪ Fin 6 := ⟨![0, 1, 2, 3], by decide⟩

/-- `X̃₁, X̃₂, X₃, X₄` among the six variables. -/
def copyEmb₂ : Fin 4 ↪ Fin 6 := ⟨![4, 5, 2, 3], by decide⟩

/-- The entropy function of the six variables `X₁, X₂, X₃, X₄, X̃₁, X̃₂`. -/
def copyEntropy (μ : Ω → ℝ) (X : ∀ i, Ω → A i) : Finset (Fin 6) → ℝ :=
  blockEntropy (copyMeasure μ X) (copyFamily X)

/-- The block of the six variables on `e(S)` is an injective function of a vector on `S`. -/
lemma entropyRV_copy_map (S : Finset (Fin 4)) (e : Fin 4 ↪ Fin 6)
    (he : ∀ i, copyIdx (e i) = i) (V : Ω × Ω → ∀ i, A i)
    (hV : ∀ q i, copyFamily X (e i) q = ⟨i, V q i⟩) :
    H[blockRV (copyFamily X) (S.map e) ; copyMeasure μ X] =
      H[fun q (i : S) => V q i ; copyMeasure μ X] := by
  have hmem : ∀ j : S.map e, copyIdx j.1 ∈ S := fun j => by
    obtain ⟨i, hi, hj⟩ := mem_map.1 j.2
    rw [← hj, he]
    exact hi
  refine entropyRV_eq_of_injective _ (fun v (j : S.map e) => ⟨copyIdx j.1, v ⟨_, hmem j⟩⟩)
    (fun v w hvw => funext fun k => ?_) fun q => funext fun ⟨j, hj⟩ => ?_
  · have h₁ := congrFun hvw ⟨e k, mem_map_of_mem e k.2⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h₁
    have h₂ : (⟨copyIdx (e k), hmem ⟨e k, mem_map_of_mem e k.2⟩⟩ : S) = k := Subtype.ext (he k)
    have key : ∀ z : S, z = k → v z = w z → v k = w k := by
      rintro z rfl h
      exact h
    exact key _ h₂ h₁
  · obtain ⟨i, -, rfl⟩ := mem_map.1 hj
    change copyFamily X (e i) q = _
    rw [hV]
    have key : ∀ j, j = i → (⟨i, V q i⟩ : Σ i, A i) = ⟨j, V q j⟩ := by
      rintro j rfl
      rfl
    exact key _ (he i)

/-- **Lemma 15.8**: the entropy function of the six variables extends the entropy function of
`X₁, …, X₄`. -/
theorem copy_fst (hμ : IsPMF μ) (S : Finset (Fin 4)) :
    copyEntropy μ X (S.map copyEmb₁) = blockEntropy μ X S := by
  change H[blockRV (copyFamily X) (S.map copyEmb₁) ; copyMeasure μ X] = H[blockRV X S ; μ]
  rw [entropyRV_copy_map S copyEmb₁ (fun i => by fin_cases i <;> rfl)
    (fun q i => X i q.1) (fun q i => by fin_cases i <;> rfl)]
  change entropy (dist _ _) = entropy (dist _ _)
  congr 1
  funext v
  exact dist_copyMeasure_fst hμ (blockRV X S) v

/-- **Lemma 15.8**: `(X̃₁, X̃₂, X₃, X₄)` has the same distribution as `(X₁, X₂, X₃, X₄)`. -/
theorem copy_snd (hμ : IsPMF μ) (S : Finset (Fin 4)) :
    copyEntropy μ X (S.map copyEmb₂) = blockEntropy μ X S := by
  change H[blockRV (copyFamily X) (S.map copyEmb₂) ; copyMeasure μ X] = H[blockRV X S ; μ]
  rw [entropyRV_copy_map S copyEmb₂ (fun i => by fin_cases i <;> rfl)
    (copyVec X) (fun q i => by fin_cases i <;> rfl)]
  change entropy (dist _ _) = entropy (dist _ _)
  congr 1
  funext v
  exact dist_copyMeasure_copyVec hμ (fun w (i : S) => w i) v

omit [∀ i, Fintype (A i)] in
/-- The joint distribution of `(F, X₃X₄)` on the first copy and `G` on the second. -/
lemma dist_copyMeasure_triple {β γ : Type*} (F : Ω → β) (G : Ω → γ) (a : β)
    (k : A 2 × A 3) (b : γ) :
    dist (copyMeasure μ X) (fun q => (F q.1, copyBase X q.1, G q.2)) (a, k, b) =
      dist μ (pair F (copyBase X)) (a, k) * dist μ (pair G (copyBase X)) (b, k) /
        dist μ (copyBase X) k := by
  classical
  simp only [copyMeasure, dist, Fintype.sum_prod_type, sum_mul_sum, sum_div]
  refine sum_congr rfl fun ω _ => sum_congr rfl fun ω' _ => ?_
  simp only [pair, Prod.mk.injEq]
  split_ifs <;> simp_all only [mem_univ, Fin.isValue, true_and, and_true, and_self, false_and,
    not_true_eq_false, not_false_eq_true, not_and, mul_zero, zero_mul, zero_div]
  congr 1
  exact sum_congr rfl fun x _ => by congr

/-- **Lemma 15.8**: `(X₁, X₂) → (X₃, X₄) → (X̃₁, X̃₂)` is a Markov chain. -/
theorem copy_markov (hμ : IsPMF μ) : condInfo (copyEntropy μ X) {0, 1} {4, 5} {2, 3} = 0 := by
  classical
  set P : Ω → A 0 × A 1 := pair (X 0) (X 1)
  set K := copyBase X
  have hμ' := isPMF_copyMeasure (X := X) hμ
  -- the blocks are injective functions of `P ∘ fst`, `P ∘ snd` and `K ∘ fst`
  have hpair : ∀ (a b : Fin 6), a ≠ b → ∀ (i₁ i₂ : Fin 4), (∀ x y : A i₁ × A i₂,
      (⟨i₁, x.1⟩ : Σ i, A i) = ⟨i₁, y.1⟩ → (⟨i₂, x.2⟩ : Σ i, A i) = ⟨i₂, y.2⟩ → x = y) →
      True := fun _ _ _ _ _ _ => trivial
  have e₁ : blockRV (copyFamily X) {0, 1} =
      (fun x (j : ({0, 1} : Finset (Fin 6))) =>
        if j.1 = 0 then (⟨0, x.1⟩ : Σ i, A i) else ⟨1, x.2⟩) ∘ fun q => P q.1 := by
    funext q ⟨j, hj⟩
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> rfl
  have e₂ : blockRV (copyFamily X) {4, 5} =
      (fun x (j : ({4, 5} : Finset (Fin 6))) =>
        if j.1 = 4 then (⟨0, x.1⟩ : Σ i, A i) else ⟨1, x.2⟩) ∘ fun q => P q.2 := by
    funext q ⟨j, hj⟩
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> rfl
  have e₃ : blockRV (copyFamily X) {2, 3} =
      (fun x (j : ({2, 3} : Finset (Fin 6))) =>
        if j.1 = 2 then (⟨2, x.1⟩ : Σ i, A i) else ⟨3, x.2⟩) ∘ fun q => K q.1 := by
    funext q ⟨j, hj⟩
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> rfl
  have inj : ∀ (a b : Fin 6) (i₁ i₂ : Fin 4), a ≠ b → ∀ {x y : A i₁ × A i₂},
      (fun (j : ({a, b} : Finset (Fin 6))) =>
        if j.1 = a then (⟨i₁, x.1⟩ : Σ i, A i) else ⟨i₂, x.2⟩) =
      (fun (j : ({a, b} : Finset (Fin 6))) =>
        if j.1 = a then (⟨i₁, y.1⟩ : Σ i, A i) else ⟨i₂, y.2⟩) → x = y := by
    intro a b i₁ i₂ hab x y h
    have h₁ := congrFun h ⟨a, by simp⟩
    have h₂ := congrFun h ⟨b, by simp⟩
    simp only [↓reduceIte, Ne.symm hab, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h₁ h₂
    exact Prod.ext h₁ h₂
  rw [copyEntropy, condInfo_blockEntropy hμ', e₁, e₂, e₃,
    condMutualInfo_comp_injective hμ' (fun x y h => inj 0 1 0 1 (by decide) h)
      (fun x y h => inj 4 5 0 1 (by decide) h) (fun x y h => inj 2 3 2 3 (by decide) h),
    condMutualInfo_eq_zero_iff hμ', condIndep_iff_mul hμ']
  intro a k b
  have h₁ : dist (copyMeasure μ X) (pair (fun q => P q.1) (pair (fun q => K q.1) fun q => P q.2))
      (a, k, b) = dist μ (pair P K) (a, k) * dist μ (pair P K) (b, k) / dist μ K k :=
    dist_copyMeasure_triple P P a k b
  have h₂ : dist (copyMeasure μ X) (fun q => K q.1) k = dist μ K k :=
    dist_copyMeasure_fst hμ K k
  have h₃ : dist (copyMeasure μ X) (pair (fun q => P q.1) fun q => K q.1) (a, k) =
      dist μ (pair P K) (a, k) := dist_copyMeasure_fst hμ (pair P K) (a, k)
  have h₄ : dist (copyMeasure μ X) (pair (fun q => K q.1) fun q => P q.2) (k, b) =
      dist μ (pair P K) (b, k) := by
    rw [← dist_pair_swap μ, ← dist_copyMeasure_snd (X := X) hμ (pair K P) (k, b)]
    exact dist_copyMeasure_congr (fun q hq => by
      simp only [pair, copyMeasure_ne_zero hq, K]) (k, b)
  rw [h₁, h₂, h₃, h₄]
  by_cases hk : dist μ K k = 0
  · rw [hk, mul_zero, dist_pair_eq_zero_of_right hμ P K hk, zero_mul]
  · rw [div_mul_cancel₀ _ hk]

end Six

/-! ### The inequality -/

section Linear

variable {f : Finset (Fin 6) → ℝ}

/-- **Lemma 15.9**, for the entropy function `f` of `X₁, X₂, X₃, X₄, X̃₁, X̃₂` (indices `0, …, 5`):
`I(X₃; X₄) - I(X₃; X₄ | X₁) - I(X₃; X₄ | X₂) ≤ I(X₁; X̃₂)`, (15.66)–(15.74). The hypotheses are
`I(X₃; X₄ | X₂) = I(X₃; X₄ | X̃₂)` and `I(X₁; X̃₂ | X₃, X₄) = 0`. -/
theorem condInfo_sub_sub_le_of_markov (hf : IsPolymatroid f)
    (hc : condInfo f {2} {3} {5} = condInfo f {2} {3} {1}) (hM : condInfo f {0} {5} {2, 3} = 0) :
    condInfo f {2} {3} ∅ - condInfo f {2} {3} {0} - condInfo f {2} {3} {1} ≤
      condInfo f {0} {5} ∅ := by
  have n₁ := hf.condInfo_nonneg {0} {5} {3}
  have n₂ := hf.condInfo_nonneg {0} {5} {2}
  have n₃ := hf.condInfo_nonneg {2} {3} {0, 5}
  rw [condInfo_eq_of f (U₁ := {0, 3}) (U₂ := {3, 5}) (U₃ := {0, 3, 5}) (by decide) (by decide)
    (by decide)] at n₁
  rw [condInfo_eq_of f (U₁ := {0, 2}) (U₂ := {2, 5}) (U₃ := {0, 2, 5}) (by decide) (by decide)
    (by decide)] at n₂
  rw [condInfo_eq_of f (U₁ := {0, 2, 5}) (U₂ := {0, 3, 5}) (U₃ := {0, 2, 3, 5}) (by decide)
    (by decide) (by decide)] at n₃
  rw [condInfo_eq_of f (U₁ := {0, 2, 3}) (U₂ := {2, 3, 5}) (U₃ := {0, 2, 3, 5}) (by decide)
    (by decide) (by decide)] at hM
  rw [← hc]
  rw [condInfo_eq_of f (U₁ := {2}) (U₂ := {3}) (U₃ := {2, 3}) (by decide) (by decide)
      (by decide), condInfo_eq_of f (U₁ := {0, 2}) (U₂ := {0, 3}) (U₃ := {0, 2, 3}) (by decide)
      (by decide) (by decide), condInfo_eq_of f (U₁ := {2, 5}) (U₂ := {3, 5}) (U₃ := {2, 3, 5})
      (by decide) (by decide) (by decide), condInfo_eq_of f (U₁ := {0}) (U₂ := {5})
      (U₃ := {0, 5}) (by decide) (by decide) (by decide)]
  linarith

/-- **Lemma 15.10**, for the entropy function `f` of the six variables:
`I(X₃; X₄) - 2 I(X₃; X₄ | X₁) ≤ I(X₁; X̃₁)`, (15.76). The hypotheses are
`I(X₃; X₄ | X₁) = I(X₃; X₄ | X̃₁)` and `I(X₁; X̃₁ | X₃, X₄) = 0`. -/
theorem condInfo_sub_two_mul_le_of_markov (hf : IsPolymatroid f)
    (hc : condInfo f {2} {3} {4} = condInfo f {2} {3} {0}) (hM : condInfo f {0} {4} {2, 3} = 0) :
    condInfo f {2} {3} ∅ - 2 * condInfo f {2} {3} {0} ≤ condInfo f {0} {4} ∅ := by
  have n₁ := hf.condInfo_nonneg {0} {4} {3}
  have n₂ := hf.condInfo_nonneg {0} {4} {2}
  have n₃ := hf.condInfo_nonneg {2} {3} {0, 4}
  rw [condInfo_eq_of f (U₁ := {0, 3}) (U₂ := {3, 4}) (U₃ := {0, 3, 4}) (by decide) (by decide)
    (by decide)] at n₁
  rw [condInfo_eq_of f (U₁ := {0, 2}) (U₂ := {2, 4}) (U₃ := {0, 2, 4}) (by decide) (by decide)
    (by decide)] at n₂
  rw [condInfo_eq_of f (U₁ := {0, 2, 4}) (U₂ := {0, 3, 4}) (U₃ := {0, 2, 3, 4}) (by decide)
    (by decide) (by decide)] at n₃
  rw [condInfo_eq_of f (U₁ := {0, 2, 3}) (U₂ := {2, 3, 4}) (U₃ := {0, 2, 3, 4}) (by decide)
    (by decide) (by decide)] at hM
  rw [two_mul]
  nth_rewrite 2 [← hc]
  rw [condInfo_eq_of f (U₁ := {2}) (U₂ := {3}) (U₃ := {2, 3}) (by decide) (by decide)
      (by decide), condInfo_eq_of f (U₁ := {0, 2}) (U₂ := {0, 3}) (U₃ := {0, 2, 3}) (by decide)
      (by decide) (by decide), condInfo_eq_of f (U₁ := {2, 4}) (U₂ := {3, 4}) (U₃ := {2, 3, 4})
      (by decide) (by decide) (by decide), condInfo_eq_of f (U₁ := {0}) (U₂ := {4})
      (U₃ := {0, 4}) (by decide) (by decide) (by decide)]
  linarith

/-- **Theorem 15.7**, from a copy: if `f` is a polymatroid on six indices whose restrictions to
`{0, 1, 2, 3}` and `{4, 5, 2, 3}` are `h`, and `I(X₁, X₂; X̃₁, X̃₂ | X₃, X₄) = 0`, then
`2 I(X₃; X₄) ≤ I(X₁; X₂) + I(X₁; X₃, X₄) + 3 I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂)` for `h`,
(15.77)–(15.84). -/
theorem zhangYeung_of_copy {h : Finset (Fin 4) → ℝ} (hf : IsPolymatroid f)
    (h₁ : ∀ S, f (S.map copyEmb₁) = h S) (h₂ : ∀ S, f (S.map copyEmb₂) = h S)
    (hM : condInfo f {0, 1} {4, 5} {2, 3} = 0) :
    2 * condInfo h {2} {3} ∅ ≤ condInfo h {0} {1} ∅ + condInfo h {0} {2, 3} ∅ +
      3 * condInfo h {2} {3} {0} + condInfo h {2} {3} {1} := by
  -- the Markov chain gives the three conditional independencies used
  have hM₅ : condInfo f {0} {5} {2, 3} = 0 := le_antisymm
    (hM ▸ hf.condInfo_mono (by decide) (by decide) _) (hf.condInfo_nonneg _ _ _)
  have hM₄ : condInfo f {0} {4} {2, 3} = 0 := le_antisymm
    (hM ▸ hf.condInfo_mono (by decide) (by decide) _) (hf.condInfo_nonneg _ _ _)
  have hM₄₅ : condInfo f {0} {4, 5} {2, 3} = 0 := le_antisymm
    (hM ▸ hf.condInfo_mono (by decide) (by decide) _) (hf.condInfo_nonneg _ _ _)
  -- the values of `h` and their copies
  have v : ∀ (S : Finset (Fin 4)) (T : Finset (Fin 6)), S.map copyEmb₁ = T → h S = f T :=
    fun S T e => (h₁ S).symm.trans (congrArg f e)
  have w : ∀ (S : Finset (Fin 4)) (T : Finset (Fin 6)), S.map copyEmb₂ = T → h S = f T :=
    fun S T e => (h₂ S).symm.trans (congrArg f e)
  have c₁ : condInfo f {2} {3} {5} = condInfo f {2} {3} {1} := by
    simp only [condInfo]
    rw [← w {1, 2} ({5} ∪ {2}) (by decide), ← w {1, 3} ({5} ∪ {3}) (by decide),
      ← w {1, 2, 3} ({5} ∪ {2} ∪ {3}) (by decide), ← w {1} {5} (by decide),
      ← v {1, 2} ({1} ∪ {2}) (by decide), ← v {1, 3} ({1} ∪ {3}) (by decide),
      ← v {1, 2, 3} ({1} ∪ {2} ∪ {3}) (by decide), ← v {1} {1} (by decide)]
  have c₂ : condInfo f {2} {3} {4} = condInfo f {2} {3} {0} := by
    simp only [condInfo]
    rw [← w {0, 2} ({4} ∪ {2}) (by decide), ← w {0, 3} ({4} ∪ {3}) (by decide),
      ← w {0, 2, 3} ({4} ∪ {2} ∪ {3}) (by decide), ← w {0} {4} (by decide),
      ← v {0, 2} ({0} ∪ {2}) (by decide), ← v {0, 3} ({0} ∪ {3}) (by decide),
      ← v {0, 2, 3} ({0} ∪ {2} ∪ {3}) (by decide), ← v {0} {0} (by decide)]
  have l₁ := condInfo_sub_sub_le_of_markov hf c₁ hM₅
  have l₂ := condInfo_sub_two_mul_le_of_markov hf c₂ hM₄
  have n₇ := hf.condInfo_nonneg {4} {5} {0}
  have o₁ := hf.condInfo_mono (S := {0}) (S' := {0}) (T := {4, 5}) (T' := {2, 3, 4, 5}) subset_rfl
    (by decide) ∅
  -- the goal in terms of `f`
  have hmap : ∀ S T K : Finset (Fin 4),
      condInfo h S T K = condInfo f (S.map copyEmb₁) (T.map copyEmb₁) (K.map copyEmb₁) := by
    intro S T K
    simp only [condInfo, ← h₁, map_union]
  rw [hmap, hmap, hmap, hmap, hmap]
  have m₁ : ({2} : Finset (Fin 4)).map copyEmb₁ = {2} := by decide
  have m₂ : ({3} : Finset (Fin 4)).map copyEmb₁ = {3} := by decide
  have m₃ : ({0} : Finset (Fin 4)).map copyEmb₁ = {0} := by decide
  have m₄ : ({1} : Finset (Fin 4)).map copyEmb₁ = {1} := by decide
  have m₅ : ({2, 3} : Finset (Fin 4)).map copyEmb₁ = {2, 3} := by decide
  rw [m₁, m₂, m₃, m₄, m₅, map_empty]
  -- every conditional mutual information through the entropies of literal sets
  have q₁ := condInfo_eq_of f (S := {2}) (T := {3}) (K := ∅) (U₁ := {2}) (U₂ := {3})
    (U₃ := {2, 3}) (by decide) (by decide) (by decide)
  have q₂ := condInfo_eq_of f (S := {0}) (T := {1}) (K := ∅) (U₁ := {0}) (U₂ := {1})
    (U₃ := {0, 1}) (by decide) (by decide) (by decide)
  have q₃ := condInfo_eq_of f (S := {0}) (T := {2, 3}) (K := ∅) (U₁ := {0}) (U₂ := {2, 3})
    (U₃ := {0, 2, 3}) (by decide) (by decide) (by decide)
  have q₄ := condInfo_eq_of f (S := {2}) (T := {3}) (K := {0}) (U₁ := {0, 2}) (U₂ := {0, 3})
    (U₃ := {0, 2, 3}) (by decide) (by decide) (by decide)
  have q₅ := condInfo_eq_of f (S := {2}) (T := {3}) (K := {1}) (U₁ := {1, 2}) (U₂ := {1, 3})
    (U₃ := {1, 2, 3}) (by decide) (by decide) (by decide)
  have q₆ := condInfo_eq_of f (S := {0}) (T := {5}) (K := ∅) (U₁ := {0}) (U₂ := {5})
    (U₃ := {0, 5}) (by decide) (by decide) (by decide)
  have q₇ := condInfo_eq_of f (S := {0}) (T := {4}) (K := ∅) (U₁ := {0}) (U₂ := {4})
    (U₃ := {0, 4}) (by decide) (by decide) (by decide)
  have q₈ := condInfo_eq_of f (S := {4}) (T := {5}) (K := {0}) (U₁ := {0, 4}) (U₂ := {0, 5})
    (U₃ := {0, 4, 5}) (by decide) (by decide) (by decide)
  have q₉ := condInfo_eq_of f (S := {0}) (T := {4, 5}) (K := ∅) (U₁ := {0}) (U₂ := {4, 5})
    (U₃ := {0, 4, 5}) (by decide) (by decide) (by decide)
  have q₁₀ := condInfo_eq_of f (S := {0}) (T := {2, 3, 4, 5}) (K := ∅) (U₁ := {0})
    (U₂ := {2, 3, 4, 5}) (U₃ := {0, 2, 3, 4, 5}) (by decide) (by decide) (by decide)
  have q₁₁ := condInfo_eq_of f (S := {0}) (T := {4, 5}) (K := {2, 3}) (U₁ := {0, 2, 3})
    (U₂ := {2, 3, 4, 5}) (U₃ := {0, 2, 3, 4, 5}) (by decide) (by decide) (by decide)
  -- the copies
  have e₄₅ : f {4, 5} = f {0, 1} := (w {0, 1} {4, 5} (by decide)).symm.trans
    (v {0, 1} {0, 1} (by decide))
  have e₄ : f {4} = f {0} := (w {0} {4} (by decide)).symm.trans (v {0} {0} (by decide))
  have e₅ : f {5} = f {1} := (w {1} {5} (by decide)).symm.trans (v {1} {1} (by decide))
  have h₀ := hf.empty
  linarith

end Linear

/-- **Theorem 15.7 (Zhang–Yeung).** For any four random variables,
`2 I(X₃; X₄) ≤ I(X₁; X₂) + I(X₁; X₃, X₄) + 3 I(X₃; X₄ | X₁) + I(X₃; X₄ | X₂)` (15.62). The variables
are `X 0, …, X 3`. -/
theorem zhangYeung {Ω : Type*} [Fintype Ω] {A : Fin 4 → Type*} [∀ i, Fintype (A i)]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    2 * I[X 2 : X 3 ; μ] ≤ I[X 0 : X 1 ; μ] + I[X 0 : pair (X 2) (X 3) ; μ] +
      3 * I[X 2 : X 3 | X 0 ; μ] + I[X 2 : X 3 | X 1 ; μ] := by
  have s := rvEquiv_blockRV_singleton X
  rw [mutualInfo_eq_condInfo hμ (s 2) (s 3), mutualInfo_eq_condInfo hμ (s 0) (s 1),
    mutualInfo_eq_condInfo hμ (s 0) (rvEquiv_pair_blockRV X), condMutualInfo_eq_condInfo hμ (s 2)
    (s 3) (s 0), condMutualInfo_eq_condInfo hμ (s 2) (s 3) (s 1)]
  exact zhangYeung_of_copy (isPolymatroid_blockEntropy (isPMF_copyMeasure hμ))
    (copy_fst hμ) (copy_snd hμ) (copy_markov hμ)

end InfoTheory
