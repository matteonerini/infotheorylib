/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.FourierMotzkin
public import InfoTheoryLib.InfoInequalities.EntropySpace
public import InfoTheoryLib.MutualInformation.CsiszarSum

/-!
# Shannon-type inequalities

Every Shannon information measure of random variables `Xᵢ`, `i ∈ ι`, is a sum of measures of two
*elemental forms*: `H(Xᵢ | X_{N - i})` and `I(Xᵢ; Xⱼ | X_K)` with `i ≠ j` and `K ⊆ N - {i, j}`.
Their nonnegativity, the *elemental inequalities* `G h ≥ 0`, is equivalent to the basic
inequalities and to the polymatroidal axioms, and defines the region `Γₙ ⊇ Γ*ₙ`. An information
inequality `b ⬝ h ≥ 0` is *Shannon-type* if it holds on `Γₙ`; it then always holds. This is a
linear programming question: `b ⬝ h ≥ 0` is Shannon-type if and only if the minimum of `b ⬝ h` on
`Γₙ` is `0` (Theorem 14.3), and, by Farkas's lemma, if and only if `b` is a nonnegative
combination of the rows of `G` (Theorem 14.5).

## Main definitions

* `ElemForm ι`: the elemental forms, with `elemValue e f` the value of the form `e` on a set
  function `f`.
* `elemMatrix ι`: the matrix `G` of the elemental inequalities.
* `shannonRegion ι`: the region `Γₙ = {h : G h ≥ 0}`.
* `IsShannonType b Φ`: `b ⬝ h ≥ 0` is a Shannon-type inequality under the constraint `Φ`.

## Main statements

* `card_elemForm`: (14.12), the number `n + C(n, 2) 2^{n-2}` of elemental forms.
* `isPolymatroid_iff_elemValue_nonneg`: the elemental inequalities are equivalent to the
  polymatroidal axioms.
* `isPolymatroid_iff_condInfo_nonneg`: **Appendix 14.A**, the polymatroidal axioms are equivalent
  to the basic inequalities.
* `mem_shannonRegion_iff`, `entropicRegion_subset_shannonRegion`: (14.25)–(14.26).
* `isShannonType_iff_isLeast`: **Theorems 14.3 and 14.4**.
* `isShannonType_univ_iff`: **Theorem 14.5**.
* `exists_elemental_nonredundant`: **Section 14.6**, the elemental inequalities are minimal.
* `condIndep_pair_iff`: (14.71), the semi-graphoid axioms.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 14
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

universe u

/-! ### Elemental forms -/

section Elemental

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **elemental forms** of Shannon's information measures, Section 14.1: `H(Xᵢ | X_{N - i})`
for `i ∈ ι`, and `I(Xᵢ; Xⱼ | X_K)` for a pair `p = {i, j}` and a set `K` disjoint from `p`. -/
abbrev ElemForm (ι : Type*) :=
  ι ⊕ {pK : Finset ι × Finset ι // #pK.1 = 2 ∧ Disjoint pK.1 pK.2}

/-- The value of an elemental form on a set function `f`, in canonical form: `f N - f (N - i)`, and
`f (K ∪ {i}) + f (K ∪ {j}) - f (K ∪ {i, j}) - f K` for `p = {i, j}`. -/
def elemValue : ElemForm ι → (Finset ι → ℝ) → ℝ
  | .inl i, f => f univ - f (univ.erase i)
  | .inr pK, f => ∑ x ∈ pK.1.1, f (pK.1.2 ∪ {x}) - f (pK.1.2 ∪ pK.1.1) - f pK.1.2

omit [Fintype ι] in
lemma condInfo_singleton_eq (f : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) (K : Finset ι) :
    condInfo f {i} {j} K = ∑ x ∈ ({i, j} : Finset ι), f (K ∪ {x}) - f (K ∪ {i, j}) - f K := by
  rw [condInfo, sum_pair hij, union_assoc, singleton_union, ← pair_comm]

lemma elemValue_inr (f : Finset ι → ℝ) {i j : ι} (hij : i ≠ j) {K : Finset ι}
    (h : #({i, j} : Finset ι) = 2 ∧ Disjoint {i, j} K) :
    elemValue (.inr ⟨({i, j}, K), h⟩) f = condInfo f {i} {j} K := by
  rw [condInfo_singleton_eq f hij]
  rfl

/-- **(14.12)** The number of elemental forms of Shannon's information measures for `n` random
variables is `n + C(n, 2) 2^{n-2}`. -/
theorem card_elemForm :
    Fintype.card (ElemForm ι) =
      Fintype.card ι + (Fintype.card ι).choose 2 * 2 ^ (Fintype.card ι - 2) := by
  rw [Fintype.card_sum, Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun (p K : Finset ι) => #p = 2 ∧ Disjoint p K), Fintype.card_sigma]
  congr 1
  have hK : ∀ p : Finset ι, Fintype.card {K : Finset ι // #p = 2 ∧ Disjoint p K} =
      if #p = 2 then 2 ^ (Fintype.card ι - 2) else 0 := by
    intro p
    split_ifs with hp
    · rw [Fintype.card_subtype]
      have e : (univ.filter fun K : Finset ι => #p = 2 ∧ Disjoint p K) = (univ \ p).powerset := by
        ext K
        rw [mem_filter, mem_powerset]
        constructor
        · rintro ⟨-, -, hd⟩ x hx
          exact mem_sdiff.2 ⟨mem_univ x, disjoint_right.1 hd hx⟩
        · intro hK
          exact ⟨mem_univ K, hp, disjoint_right.2 fun x hx => (mem_sdiff.1 (hK hx)).2⟩
      rw [e, card_powerset, card_sdiff_of_subset (subset_univ p), card_univ, hp]
    · rw [Fintype.card_eq_zero_iff]
      exact ⟨fun K => hp K.2.1⟩
  rw [Fintype.sum_congr _ _ hK, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
  congr 1
  rw [← powerset_univ, ← powersetCard_eq_filter, card_powersetCard, card_univ]

omit [Fintype ι] in
/-- The chain rule `I(X_{S ∪ {a}}; X_T | X_K) = I(X_S; X_T | X_K) + I(Xₐ; X_T | X_{K ∪ S})` for
set functions. -/
lemma condInfo_insert_left (f : Finset ι → ℝ) (a : ι) (S T K : Finset ι) :
    condInfo f (insert a S) T K = condInfo f S T K + condInfo f {a} T (K ∪ S) := by
  have e₁ : K ∪ insert a S = K ∪ S ∪ {a} := by
    ext x
    simp only [mem_union, mem_insert, mem_singleton]
    tauto
  simp only [condInfo]
  rw [e₁]
  ring

omit [Fintype ι] in
/-- If all the elemental conditional mutual informations of `f` are nonnegative, then so is
`I(X_S; X_T | X_K)` for disjoint `S`, `T` and `K`. -/
lemma condInfo_nonneg_of_elem {f : Finset ι → ℝ}
    (hβ : ∀ i j K, i ≠ j → i ∉ K → j ∉ K → 0 ≤ condInfo f {i} {j} K) :
    ∀ S T K : Finset ι, Disjoint S T → Disjoint S K → Disjoint T K → 0 ≤ condInfo f S T K := by
  -- the case `S = {a}`, by induction on `T`
  have hsingle : ∀ a (T K : Finset ι), a ∉ T → a ∉ K → Disjoint T K →
      0 ≤ condInfo f {a} T K := by
    intro a T
    induction T using Finset.induction_on with
    | empty =>
      intro K _ _ _
      simp [condInfo]
    | insert b T hb ih =>
      intro K haT haK hTK
      rw [condInfo_comm, condInfo_insert_left, condInfo_comm f T, condInfo_comm f {b}]
      have hab : a ≠ b := fun h => haT (h ▸ mem_insert_self b T)
      refine add_nonneg (ih K (fun h => haT (mem_insert_of_mem h)) haK
        (disjoint_of_subset_left (subset_insert b T) hTK)) (hβ a b (K ∪ T) hab ?_ ?_)
      · rw [mem_union, not_or]
        exact ⟨haK, fun h => haT (mem_insert_of_mem h)⟩
      · rw [mem_union, not_or]
        exact ⟨disjoint_left.1 hTK (mem_insert_self b T), hb⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro T K _ _ _
    simp [condInfo]
  | insert a S ha ih =>
    intro T K hST hSK hTK
    rw [condInfo_insert_left]
    refine add_nonneg (ih T K (disjoint_of_subset_left (subset_insert a S) hST)
      (disjoint_of_subset_left (subset_insert a S) hSK) hTK) (hsingle a T (K ∪ S)
      (disjoint_left.1 hST (mem_insert_self a S)) ?_ ?_)
    · rw [mem_union, not_or]
      exact ⟨disjoint_left.1 hSK (mem_insert_self a S), ha⟩
    · exact disjoint_union_right.2 ⟨hTK, (disjoint_of_subset_left (subset_insert a S) hST).symm⟩

/-- **Section 14.1.** The elemental inequalities are equivalent to the polymatroidal axioms, so to
the basic inequalities. -/
theorem isPolymatroid_iff_elemValue_nonneg {f : Finset ι → ℝ} (h0 : f ∅ = 0) :
    IsPolymatroid f ↔ ∀ e : ElemForm ι, 0 ≤ elemValue e f := by
  constructor
  · rintro hf (i | ⟨⟨p, K⟩, hp, hd⟩)
    · exact sub_nonneg.2 (hf.mono (erase_subset i univ))
    · obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hp
      rw [elemValue_inr f hij]
      exact hf.condInfo_nonneg _ _ _
  · intro H
    have hβ : ∀ i j K, i ≠ j → i ∉ K → j ∉ K → 0 ≤ condInfo f {i} {j} K := by
      intro i j K hij hi hj
      have hp : #({i, j} : Finset ι) = 2 ∧ Disjoint {i, j} K :=
        ⟨card_pair hij, by
          rw [disjoint_insert_left, disjoint_singleton_left]
          exact ⟨hi, hj⟩⟩
      rw [← elemValue_inr f hij hp]
      exact H _
    -- one step of monotonicity: `f S ≤ f (S ∪ {j})`
    have hstep : ∀ j (S : Finset ι), j ∉ S → f S ≤ f (insert j S) := by
      intro j S hj
      have hc := condInfo_nonneg_of_elem hβ {j} (univ \ insert j S) S
        (disjoint_singleton_left.2 fun h => (mem_sdiff.1 h).2 (mem_insert_self j S))
        (disjoint_singleton_left.2 hj) (disjoint_left.2 fun x hx hxS =>
          (mem_sdiff.1 hx).2 (mem_insert_of_mem hxS))
      have hα := H (.inl j)
      simp only [elemValue] at hα
      have e₁ : S ∪ {j} = insert j S := by rw [union_comm, singleton_union]
      have e₂ : S ∪ (univ \ insert j S) = univ.erase j := by
        ext x
        by_cases hxj : x = j
        · subst hxj
          simp [hj]
        · by_cases hxS : x ∈ S <;> simp [hxj, hxS]
      have e₃ : S ∪ {j} ∪ (univ \ insert j S) = univ := by
        rw [e₁, union_sdiff_of_subset (subset_univ _)]
      simp only [condInfo] at hc
      rw [e₃, e₁, e₂] at hc
      linarith
    have hmono : ∀ (u S : Finset ι), Disjoint S u → f S ≤ f (S ∪ u) := by
      intro u
      induction u using Finset.induction_on with
      | empty => intro S _; rw [union_empty]
      | insert b u hb ih =>
        intro S hSu
        have hbS : b ∉ S ∪ u := by
          rw [mem_union, not_or]
          exact ⟨disjoint_right.1 hSu (mem_insert_self b u), hb⟩
        rw [union_insert]
        exact (ih S (disjoint_of_subset_right (subset_insert b u) hSu)).trans
          (hstep b (S ∪ u) hbS)
    refine ⟨h0, fun s t hst => ?_, fun s t => ?_⟩
    · have := hmono (t \ s) s disjoint_sdiff
      rwa [union_sdiff_of_subset hst] at this
    · have hc := condInfo_nonneg_of_elem hβ (s \ t) (t \ s) (s ∩ t) disjoint_sdiff_sdiff
        (disjoint_of_subset_right inter_subset_right sdiff_disjoint)
        (disjoint_of_subset_right inter_subset_left sdiff_disjoint)
      have e₁ : s ∩ t ∪ s \ t = s := by rw [union_comm, sdiff_union_inter]
      have e₂ : s ∩ t ∪ t \ s = t := by rw [inter_comm, union_comm, sdiff_union_inter]
      have e₃ : s ∩ t ∪ s \ t ∪ t \ s = s ∪ t := by rw [e₁, union_sdiff_self_eq_union]
      simp only [condInfo] at hc
      rw [e₃, e₁, e₂] at hc
      linarith

omit [Fintype ι] in
/-- **Appendix 14.A.** For a set function with `f ∅ = 0`, the polymatroidal axioms are equivalent
to the basic inequalities `I(X_α; X_β | X_γ) ≥ 0` for all `α`, `β`, `γ`, which include
`H(X_α) = I(X_α; X_α)` and `H(X_α | X_γ) = I(X_α; X_α | X_γ)`. -/
theorem isPolymatroid_iff_condInfo_nonneg {f : Finset ι → ℝ} (h0 : f ∅ = 0) :
    IsPolymatroid f ↔ ∀ α β γ, 0 ≤ condInfo f α β γ := by
  refine ⟨fun hf => hf.condInfo_nonneg, fun H => ⟨h0, fun s t hst => ?_, fun s t => ?_⟩⟩
  · have := H t t s
    simp only [condInfo, union_self, union_eq_right.2 hst] at this
    linarith
  · have := H s t (s ∩ t)
    simp only [condInfo] at this
    rw [union_eq_right.2 inter_subset_left, union_eq_right.2 inter_subset_right] at this
    linarith

end Elemental

/-! ### The region `Γₙ` -/

section Region

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma EntropySpace.extend_empty (h : EntropySpace ι) : h.extend ∅ = 0 := by
  simp [EntropySpace.extend]

omit [Fintype ι] [DecidableEq ι] in
lemma EntropySpace.extend_add (h g : EntropySpace ι) : (h + g).extend = h.extend + g.extend := by
  funext s
  simp only [EntropySpace.extend, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
lemma EntropySpace.extend_smul (c : ℝ) (h : EntropySpace ι) : (c • h).extend = c • h.extend := by
  funext s
  simp only [EntropySpace.extend, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The elemental form `e` as a linear functional on the entropy space. -/
def elemFunctional (e : ElemForm ι) : EntropySpace ι →ₗ[ℝ] ℝ where
  toFun h := elemValue e h.extend
  map_add' h g := by
    rw [EntropySpace.extend_add]
    rcases e with i | ⟨⟨p, K⟩, _⟩
    · simp only [elemValue, Pi.add_apply]
      ring
    · simp only [elemValue, Pi.add_apply, sum_add_distrib]
      ring
  map_smul' c h := by
    rw [EntropySpace.extend_smul]
    rcases e with i | ⟨⟨p, K⟩, _⟩
    · simp only [elemValue, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp only [elemValue, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← mul_sum]
      ring

/-- **The matrix `G`** of the elemental inequalities in canonical form, (14.23). -/
def elemMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix (ElemForm ι) {α : Finset ι // α.Nonempty} ℝ :=
  Matrix.of fun e α => elemFunctional e (Pi.single α 1)

lemma elemMatrix_mulVec (h : EntropySpace ι) (e : ElemForm ι) :
    (elemMatrix ι *ᵥ h) e = elemValue e h.extend := by
  change _ = elemFunctional e h
  rw [LinearMap.pi_apply_eq_sum_univ (elemFunctional e) h, mulVec, dotProduct]
  refine sum_congr rfl fun α _ => ?_
  rw [smul_eq_mul, mul_comm, elemMatrix, of_apply]
  congr 2
  funext β
  simp [Pi.single_apply, eq_comm]

/-- **The region `Γₙ = {h : G h ≥ 0}`**, (14.23), of the vectors satisfying the elemental
inequalities. -/
def shannonRegion (ι : Type*) [Fintype ι] [DecidableEq ι] : Set (EntropySpace ι) :=
  {h | 0 ≤ elemMatrix ι *ᵥ h}

/-- `Γₙ` is the set of polymatroids. -/
theorem mem_shannonRegion_iff {h : EntropySpace ι} :
    h ∈ shannonRegion ι ↔ IsPolymatroid h.extend := by
  rw [isPolymatroid_iff_elemValue_nonneg (EntropySpace.extend_empty h), shannonRegion,
    Set.mem_ofPred_eq, Pi.le_def]
  simp only [Pi.zero_apply, elemMatrix_mulVec]

/-- The origin is in `Γₙ`. -/
theorem zero_mem_shannonRegion : (0 : EntropySpace ι) ∈ shannonRegion ι := by
  rw [shannonRegion, Set.mem_ofPred_eq, mulVec_zero]

/-- **(14.25)** `Γₙ` lies in the nonnegative orthant. -/
theorem nonneg_of_mem_shannonRegion {h : EntropySpace ι} (hh : h ∈ shannonRegion ι)
    (α : {α : Finset ι // α.Nonempty}) : 0 ≤ h α := by
  have := (mem_shannonRegion_iff.1 hh).nonneg α.1
  simpa [EntropySpace.extend, α.2] using this

end Region

section Universe

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **(14.26)** `Γ*ₙ ⊆ Γₙ`: entropy functions satisfy the elemental inequalities. -/
theorem entropicRegion_subset_shannonRegion : entropicRegion ι ⊆ shannonRegion ι := by
  rintro h ⟨Ω, _, A, _, μ, X, hμ, rfl⟩
  rw [mem_shannonRegion_iff, extend_entropyVector hμ]
  exact isPolymatroid_blockEntropy hμ

/-- The inequality `b ⬝ h ≥ 0` is **Shannon-type** under the constraint `Φ` if it holds on
`Γₙ ∩ Φ`, (14.27) and (14.31). -/
def IsShannonType (b : EntropySpace ι) (Φ : Set (EntropySpace ι)) : Prop :=
  ∀ h ∈ shannonRegion ι ∩ Φ, 0 ≤ infoExpr b h

/-- **(14.27)–(14.32)** A Shannon-type inequality always holds. -/
theorem IsShannonType.ineqAlwaysHolds {b : EntropySpace ι} {Φ : Set (EntropySpace ι)}
    (h : IsShannonType b Φ) : IneqAlwaysHolds b Φ :=
  fun x hx => h x ⟨entropicRegion_subset_shannonRegion hx.1, hx.2⟩

/-- **Theorems 14.3 and 14.4.** If `0 ∈ Φ`, `b ⬝ h ≥ 0` is a Shannon-type inequality under the
constraint `Φ` if and only if the minimum of `b ⬝ h` subject to `G h ≥ 0` and `h ∈ Φ` is zero; it
is attained at the origin. -/
theorem isShannonType_iff_isLeast (b : EntropySpace ι) {Φ : Set (EntropySpace ι)}
    (h0 : (0 : EntropySpace ι) ∈ Φ) :
    IsShannonType b Φ ↔ IsLeast (infoExpr b '' (shannonRegion ι ∩ Φ)) 0 := by
  constructor
  · intro h
    refine ⟨⟨0, ⟨zero_mem_shannonRegion, h0⟩, by simp [infoExpr]⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rintro ⟨-, h⟩ x hx
    exact h ⟨x, hx, rfl⟩

/-- **Theorem 14.5.** `b ⬝ h ≥ 0` is a Shannon-type inequality if and only if `b = Gᵀ x` for some
`x ≥ 0`: `b` is a nonnegative combination of the rows of `G`. -/
theorem isShannonType_univ_iff (b : EntropySpace ι) :
    IsShannonType b Set.univ ↔ ∃ x : ElemForm ι → ℝ, 0 ≤ x ∧ b = (elemMatrix ι)ᵀ *ᵥ x := by
  classical
  set G := elemMatrix ι with hG
  constructor
  · intro H
    by_contra hno
    -- the system `x ≥ 0`, `Gᵀ x ≤ b`, `-Gᵀ x ≤ -b`, as `A x ≤ c`
    let A : Matrix (ElemForm ι ⊕ ({α : Finset ι // α.Nonempty} ⊕ {α : Finset ι // α.Nonempty}))
        (ElemForm ι) ℝ := Matrix.of fun j e => match j with
      | .inl e' => if e' = e then -1 else 0
      | .inr (.inl α) => G e α
      | .inr (.inr α) => -G e α
    let c : ElemForm ι ⊕ ({α : Finset ι // α.Nonempty} ⊕ {α : Finset ι // α.Nonempty}) → ℝ :=
      fun j => match j with
      | .inl _ => 0
      | .inr (.inl α) => b α
      | .inr (.inr α) => -b α
    have hA₁ : ∀ x e', (A *ᵥ x) (.inl e') = -x e' := fun x e' => by
      simp [A, mulVec, dotProduct, ite_mul, neg_mul, one_mul, zero_mul]
    have hA₂ : ∀ x α, (A *ᵥ x) (.inr (.inl α)) = (Gᵀ *ᵥ x) α := fun x α => by
      simp [A, mulVec, dotProduct, transpose_apply]
    have hA₃ : ∀ x α, (A *ᵥ x) (.inr (.inr α)) = -(Gᵀ *ᵥ x) α := fun x α => by
      simp [A, mulVec, dotProduct, transpose_apply, sum_neg_distrib]
    have hinf : ¬∃ x, A *ᵥ x ≤ c := by
      rintro ⟨x, hx⟩
      refine hno ⟨x, fun e => ?_, funext fun α => ?_⟩
      · have := hx (.inl e)
        rw [hA₁] at this
        simpa [c] using this
      · have h₁ := hx (.inr (.inl α))
        have h₂ := hx (.inr (.inr α))
        rw [hA₂] at h₁
        rw [hA₃] at h₂
        simp only [c] at h₁ h₂
        linarith
    obtain ⟨y, hy, hyA, hyc⟩ := FourierMotzkin.exists_nonneg_comb_of_infeasible hinf
    set h : EntropySpace ι := fun α => y (.inr (.inl α)) - y (.inr (.inr α)) with hh
    have hGh : ∀ e, (G *ᵥ h) e = y (.inl e) := by
      intro e
      have h₁ := congrFun hyA e
      rw [vecMul, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_sum_type (α₁ := {α : Finset ι // α.Nonempty})
          (α₂ := {α : Finset ι // α.Nonempty})] at h₁
      simp only [A, of_apply, Pi.zero_apply, mul_ite, mul_neg, mul_one, mul_zero, sum_ite_eq',
        mem_univ, ite_true, sum_neg_distrib] at h₁
      rw [mulVec, dotProduct]
      simp only [hh, mul_sub, sum_sub_distrib]
      have e₁ : ∑ α, G e α * y (.inr (.inl α)) = ∑ α, y (.inr (.inl α)) * G e α :=
        sum_congr rfl fun α _ => mul_comm _ _
      have e₂ : ∑ α, G e α * y (.inr (.inr α)) = ∑ α, y (.inr (.inr α)) * G e α :=
        sum_congr rfl fun α _ => mul_comm _ _
      rw [e₁, e₂]
      linarith
    have hmem : h ∈ shannonRegion ι := fun e => by
      rw [Pi.zero_apply, ← hG, hGh e]
      exact hy (.inl e)
    have hbh := H h ⟨hmem, Set.mem_univ h⟩
    have hyc' : y ⬝ᵥ c = infoExpr b h := by
      rw [dotProduct, Fintype.sum_sum_type,
        Fintype.sum_sum_type (α₁ := {α : Finset ι // α.Nonempty})
          (α₂ := {α : Finset ι // α.Nonempty})]
      simp only [c, mul_zero, sum_const_zero, zero_add, infoExpr, hh, mul_neg,
        ← sum_add_distrib]
      exact sum_congr rfl fun α _ => by ring
    linarith
  · rintro ⟨x, hx, rfl⟩ h ⟨hh, -⟩
    change 0 ≤ (Gᵀ *ᵥ x) ⬝ᵥ h
    rw [mulVec_transpose, ← dotProduct_mulVec]
    exact dotProduct_nonneg_of_nonneg hx hh

end Universe

/-! ### Minimality of the elemental inequalities -/

section Minimality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The atoms of the set of `ℱₙ` measured by an elemental form: `X̃ᵢ - X̃_{N - i}` and
`X̃ᵢ ∩ X̃ⱼ - X̃_K`. -/
def elemAtoms : ElemForm ι → Finset (NAtom ι)
  | .inl i => {⟨{i}, singleton_nonempty i⟩}
  | .inr pK => univ.filter fun a => pK.1.1 ⊆ a.1 ∧ Disjoint a.1 pK.1.2

/-- In terms of the values `u` of a signed measure on the atoms, an elemental form is the measure
of its set of atoms. -/
theorem elemValue_atomsToEntropy (u : NAtom ι → ℝ) (e : ElemForm ι) :
    elemValue e (atomsToEntropy u).extend = ∑ a ∈ elemAtoms e, u a := by
  set m : Finset (NAtom ι) → ℝ := fun F => ∑ a ∈ F, u a with hm
  have hms : IsSignedMeasure m := isSignedMeasure_sum u
  have hf : (atomsToEntropy u).extend = fun G => m (tilde G) := by
    funext G
    rw [EntropySpace.extend]
    split_ifs with hG
    · rfl
    · rw [not_nonempty_iff_eq_empty.1 hG, tilde_empty]
      simp [hm]
  rw [hf]
  rcases e with i | ⟨⟨p, K⟩, hp, hd⟩
  · change m (tilde univ) - m (tilde (univ.erase i)) = m {⟨{i}, singleton_nonempty i⟩}
    have hsub : tilde (univ.erase i) ⊆ tilde (univ : Finset ι) := fun a ha => by
      obtain ⟨x, -, hx⟩ := mem_tilde.1 ha
      exact mem_tilde.2 ⟨x, mem_univ x, hx⟩
    rw [← union_eq_left.2 hsub, ← hms.sdiff_eq]
    congr 1
    ext a
    rw [mem_sdiff, mem_tilde, mem_tilde, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      have h' : ∀ x ∈ a.1, x = i := fun x hx => by
        by_contra hxi
        exact h ⟨x, mem_erase.2 ⟨hxi, mem_univ x⟩, hx⟩
      refine Subtype.ext (Finset.ext fun x => ⟨fun hx => mem_singleton.2 (h' x hx), fun hx => ?_⟩)
      rw [mem_singleton] at hx
      subst hx
      obtain ⟨y, hy⟩ := a.2
      rwa [← h' y hy]
    · rintro rfl
      refine ⟨⟨i, mem_univ i, mem_singleton_self i⟩, ?_⟩
      rintro ⟨x, hx, hxi⟩
      exact (mem_erase.1 hx).1 (mem_singleton.1 hxi)
  · obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hp
    rw [elemValue_inr _ hxy ⟨hp, hd⟩]
    have hset : elemAtoms (.inr ⟨({x, y}, K), hp, hd⟩ : ElemForm ι) =
        (tilde {x} ∩ tilde {y}) \ tilde K := by
      ext a
      simp only [elemAtoms, mem_sdiff, mem_inter, mem_tilde, mem_singleton, exists_eq_left,
        mem_filter, mem_univ, true_and, insert_subset_iff, singleton_subset_iff, disjoint_right,
        not_exists, not_and]
    have e₁ : K ∪ {x} ∪ {y} = {x} ∪ {y} ∪ K := by
      ext z
      simp only [mem_union, mem_singleton]
      tauto
    change m (tilde (K ∪ {x})) + m (tilde (K ∪ {y})) - m (tilde (K ∪ {x} ∪ {y})) - m (tilde K) =
      m _
    rw [hset, hms.inter_sdiff_eq_union, e₁, ← tilde_union, ← tilde_union, ← tilde_union,
      ← tilde_union, union_comm K, union_comm K]

/-- **Section 14.6.** The elemental inequalities are minimal: for each elemental inequality there
is a vector `h` that satisfies all the other elemental inequalities but not this one. The book's
measure (14.87) for a `β`-inequality can violate another `β`-inequality, for instance
`I(X₁; X₃ | X₄) ≥ 0` when `n = 4` and the inequality is `I(X₁; X₂ | X₄) ≥ 0`; the measure used here
is `-1` on the atom `X̃_{N - K}`, `0` on the other atoms of `X̃ᵢ ∩ X̃ⱼ - X̃_K` and `1` elsewhere. -/
theorem exists_elemental_nonredundant (e : ElemForm ι) :
    ∃ h : EntropySpace ι, (elemMatrix ι *ᵥ h) e < 0 ∧ ∀ e' ≠ e, 0 ≤ (elemMatrix ι *ᵥ h) e' := by
  simp only [elemMatrix_mulVec]
  rcases e with i | ⟨⟨p, K⟩, hp, hd⟩
  · -- an `α`-inequality: `-1` on the atom `X̃ᵢ - X̃_{N - i}`
    refine ⟨atomsToEntropy fun a => if a.1 = {i} then -1 else 1, ?_, ?_⟩ <;>
      simp only [elemValue_atomsToEntropy]
    · simp [elemAtoms]
    · rintro (i' | ⟨⟨p', K'⟩, hp', hd'⟩) hne
      · simp only [elemAtoms, sum_singleton]
        have : ({i'} : Finset ι) ≠ {i} := fun h => hne (by rw [singleton_inj.1 h])
        simp [this]
      · refine sum_nonneg fun a ha => ?_
        have hpa := (mem_filter.1 ha).2.1
        have : a.1 ≠ {i} := fun h => by
          have := card_le_card hpa
          rw [h, hp', card_singleton] at this
          omega
        simp [this]
  · -- a `β`-inequality: `-1` on the atom `X̃_{N - K}`, `0` on the other atoms of `X̃ᵢ ∩ X̃ⱼ - X̃_K`
    have hpK : p ⊆ univ \ K := fun x hx => mem_sdiff.2 ⟨mem_univ x, disjoint_left.1 hd hx⟩
    have hne₀ : (univ \ K).Nonempty := by
      obtain ⟨x, hx⟩ := card_pos.1 (hp ▸ two_pos : 0 < #p)
      exact ⟨x, hpK hx⟩
    set a₀ : NAtom ι := ⟨univ \ K, hne₀⟩ with ha₀
    set u : NAtom ι → ℝ := fun a =>
      if a = a₀ then -1 else if p ⊆ a.1 ∧ Disjoint a.1 K then 0 else 1 with hu
    have hu_ge : ∀ a, a ≠ a₀ → 0 ≤ u a := fun a ha => by
      simp only [hu, ha, ite_false]
      split_ifs <;> norm_num
    have ha₀mem : a₀ ∈ elemAtoms (.inr ⟨(p, K), hp, hd⟩ : ElemForm ι) :=
      mem_filter.2 ⟨mem_univ _, hpK, disjoint_sdiff_self_left⟩
    refine ⟨atomsToEntropy u, ?_, ?_⟩ <;> simp only [elemValue_atomsToEntropy]
    · rw [sum_eq_single_of_mem a₀ ha₀mem]
      · simp [hu]
      · intro b hb hba
        have hb' : p ⊆ b.1 ∧ Disjoint b.1 K := (mem_filter.1 hb).2
        simp only [hu, hba, ite_false, hb', and_self, ite_true]
    · rintro (i' | ⟨⟨p', K'⟩, hp', hd'⟩) hne
      · -- `α`-inequalities: the atom `{i'}` is not in `X̃ᵢ ∩ X̃ⱼ - X̃_K`
        simp only [elemAtoms, sum_singleton]
        refine hu_ge _ fun h => ?_
        have h₁ := card_le_card hpK
        have h₂ : ({i'} : Finset ι) = univ \ K := congrArg Subtype.val h
        rw [← h₂, card_singleton] at h₁
        have : #p = 2 := hp
        omega
      · by_cases h₀ : a₀ ∈ elemAtoms (.inr ⟨(p', K'), hp', hd'⟩ : ElemForm ι)
        · -- another atom of the set, outside `X̃ᵢ ∩ X̃ⱼ - X̃_K`, has measure `1`
          have h₀' := (mem_filter.1 h₀).2
          have hK' : K' ⊆ K := fun x hx => by
            by_contra hxK
            exact disjoint_right.1 h₀'.2 hx (mem_sdiff.2 ⟨mem_univ x, hxK⟩)
          obtain ⟨a₁, ha₁, ha₁u⟩ : ∃ a₁ ∈ elemAtoms (.inr ⟨(p', K'), hp', hd'⟩ : ElemForm ι),
              u a₁ = 1 := by
            by_cases hpp : p' = p
            · subst hpp
              have hKK : K' ≠ K := fun h => hne (by subst h; rfl)
              obtain ⟨k, hkK, hkK'⟩ : ∃ k ∈ K, k ∉ K' := by
                by_contra h
                push Not at h
                exact hKK (subset_antisymm hK' h)
              refine ⟨⟨insert k p', insert_nonempty k p'⟩, mem_filter.2 ⟨mem_univ _,
                subset_insert k p', disjoint_insert_left.2 ⟨hkK', hd'⟩⟩, ?_⟩
              have hna : (⟨insert k p', insert_nonempty k p'⟩ : NAtom ι) ≠ a₀ := fun h => by
                have := congrArg (fun a : NAtom ι => k ∈ a.1) h
                simp only [ha₀, mem_insert_self, mem_sdiff, mem_univ, true_and] at this
                exact this.mp trivial hkK
              simp only [hu, hna, ite_false, ite_eq_right_iff]
              rintro ⟨-, hdis⟩
              exact absurd hkK (disjoint_left.1 hdis (mem_insert_self k p'))
            · have hp'ne : p'.Nonempty := card_pos.1 (hp' ▸ two_pos)
              refine ⟨⟨p', hp'ne⟩, mem_filter.2 ⟨mem_univ _, subset_rfl, hd'⟩, ?_⟩
              have hsub : ¬p ⊆ p' := fun h => hpp (eq_of_subset_of_card_le h
                (by rw [hp, hp'])).symm
              have hna : (⟨p', hp'ne⟩ : NAtom ι) ≠ a₀ := fun h => by
                apply hsub
                rw [show p' = univ \ K from congrArg Subtype.val h]
                exact hpK
              simp only [hu, hna, ite_false, ite_eq_right_iff]
              exact fun h => absurd h.1 hsub
          have ha₁₀ : a₁ ≠ a₀ := fun h => by
            rw [h] at ha₁u
            simp only [hu, ite_true] at ha₁u
            norm_num at ha₁u
          calc (0 : ℝ) = ∑ a ∈ elemAtoms (.inr ⟨(p', K'), hp', hd'⟩ : ElemForm ι),
                ((if a = a₁ then 1 else 0) - if a = a₀ then 1 else 0) := by
                rw [sum_sub_distrib, sum_ite_eq', sum_ite_eq']
                simp [ha₁, h₀]
            _ ≤ _ := sum_le_sum fun a _ => by
                by_cases haa₀ : a = a₀
                · subst haa₀
                  simp [ha₁₀.symm, hu]
                · by_cases haa₁ : a = a₁
                  · subst haa₁
                    simp [haa₀, ha₁u]
                  · simpa [haa₀, haa₁] using hu_ge a haa₀
        · exact sum_nonneg fun a ha => hu_ge a fun h => h₀ (h ▸ ha)

end Minimality

/-! ### The implication problem -/

section SemiGraphoid

variable {Ω α β γ δ : Type*} [Fintype Ω] {μ : Ω → ℝ}

/-- `I(X; Y, T | Z) = I(X; T, Y | Z)`. -/
lemma condMutualInfo_pair_swap [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (hμ : IsPMF μ)
    (X : Ω → α) (Y : Ω → β) (T : Ω → γ) (Z : Ω → δ) :
    I[X : pair Y T | Z ; μ] = I[X : pair T Y | Z ; μ] := by
  rw [condMutualInfo, condMutualInfo, condEntropy_congr_right hμ X (X := pair (pair T Y) Z)
    (X' := pair (pair Y T) Z) (fun p => ((p.1.2, p.1.1), p.2))
    (fun a b h => by
      obtain ⟨⟨a1, a2⟩, a3⟩ := a
      obtain ⟨⟨b1, b2⟩, b3⟩ := b
      simp only [Prod.mk.injEq] at h ⊢
      tauto) fun _ => rfl]

/-- **(14.71)** `X ⊥ (Y, T) | Z` if and only if `X ⊥ Y | Z` and `X ⊥ T | (Y, Z)`; this gives the
axioms of decomposition, weak union and contraction. -/
theorem condIndep_pair_iff [Finite α] [Finite β] [Finite γ] [Finite δ] (hμ : IsPMF μ)
    (X : Ω → α) (Y : Ω → β) (T : Ω → γ) (Z : Ω → δ) :
    CondIndep μ X (pair Y T) Z ↔ CondIndep μ X Y Z ∧ CondIndep μ X T (pair Y Z) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  have := Fintype.ofFinite δ
  rw [← condMutualInfo_eq_zero_iff hμ, ← condMutualInfo_eq_zero_iff hμ,
    ← condMutualInfo_eq_zero_iff hμ, condMutualInfo_pair_swap hμ,
    chain_rule_condMutualInfo hμ]
  have h₁ := condMutualInfo_nonneg hμ X Y Z
  have h₂ := condMutualInfo_nonneg hμ X T (pair Y Z)
  constructor
  · intro h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₃, h₄⟩
    rw [h₃, h₄, add_zero]

/-- **(14.67)** The axiom of symmetry. -/
theorem condIndep_comm [Finite α] [Finite β] [Finite γ] (hμ : IsPMF μ) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) : CondIndep μ X Y Z ↔ CondIndep μ Y X Z := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  rw [← condMutualInfo_eq_zero_iff hμ, ← condMutualInfo_eq_zero_iff hμ,
    condMutualInfo_comm hμ]

/-- **(14.68)** The axiom of decomposition. -/
theorem CondIndep.decomposition [Finite α] [Finite β] [Finite γ] [Finite δ] (hμ : IsPMF μ)
    {X : Ω → α} {Y : Ω → β} {T : Ω → γ} {Z : Ω → δ} (h : CondIndep μ X (pair Y T) Z) :
    CondIndep μ X Y Z ∧ CondIndep μ X T Z := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  have := Fintype.ofFinite δ
  refine ⟨((condIndep_pair_iff hμ X Y T Z).1 h).1, ?_⟩
  rw [← condMutualInfo_eq_zero_iff hμ, ← condMutualInfo_pair_swap hμ,
    condMutualInfo_eq_zero_iff hμ] at *
  exact ((condIndep_pair_iff hμ X T Y Z).1 h).1

/-- **(14.69)** The axiom of weak union. -/
theorem CondIndep.weak_union [Finite α] [Finite β] [Finite γ] [Finite δ] (hμ : IsPMF μ)
    {X : Ω → α} {Y : Ω → β} {T : Ω → γ} {Z : Ω → δ} (h : CondIndep μ X (pair Y T) Z) :
    CondIndep μ X Y (pair T Z) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  have := Fintype.ofFinite δ
  rw [← condMutualInfo_eq_zero_iff hμ, condMutualInfo_pair_swap hμ,
    condMutualInfo_eq_zero_iff hμ] at h
  exact ((condIndep_pair_iff hμ X T Y Z).1 h).2

/-- **(14.70)** The axiom of contraction. -/
theorem CondIndep.contraction [Finite α] [Finite β] [Finite γ] [Finite δ] (hμ : IsPMF μ)
    {X : Ω → α} {Y : Ω → β} {T : Ω → γ} {Z : Ω → δ} (h₁ : CondIndep μ X Y Z)
    (h₂ : CondIndep μ X T (pair Y Z)) : CondIndep μ X (pair Y T) Z :=
  (condIndep_pair_iff hμ X Y T Z).2 ⟨h₁, h₂⟩

end SemiGraphoid

end InfoTheory
