/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Inequalities.Han
public import InfoTheoryLib.Inequalities.Schur
public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian

/-!
# Inequalities for determinants

For a positive definite matrix `K` and a set `S` of indices, let `K(S)` be the principal
submatrix on `S`. For `X ∼ N(0, K)`, `h(X(S)) = ½ log ((2πe)^{|S|} |K(S)|)`, so the
inequalities for entropies of subsets (Section 17.6) become inequalities for principal minors.
We prove the matrix fact behind them directly: `S ↦ log |K(S)|` is submodular (Koteljanskii's
inequality `|K(A ∪ B)| |K(A ∩ B)| ≤ |K(A)| |K(B)|`, from Schur complements and Fischer's
inequality), and apply Han's inequalities (`Inequalities.Han`).

## Main definitions

* `principalMinor K S`: the principal minor `|K(S)|`.
* `minorProd K k`: the product `Pₖ` of the `k × k` principal minors, (17.117).
* `minorRootAvg K k`: the average `Sₖ` of the `k`-th roots of the `k × k` principal minors,
  (17.119).
* `condMinorMean K k`: the geometric mean `Qₖ` of `(|K|/|K(Sᶜ)|)^{1/k}` over `|S| = k`, (17.121).
* `condVar K i`: `σᵢ² = |K|/|K({i}ᶜ)|`, (17.125).

## Main statements

* `det_mul_det_le_of_block`, `principalMinor_union_mul_inter_le`: **Koteljanskii's inequality**.
* `isSubmodular_logMinor`: `S ↦ log |K(S)|` is submodular.
* `minorProd_rpow_succ_le`: **Theorem 17.9.3 (Szász)**, `P_{k+1}^{1/C(n-1,k)} ≤ Pₖ^{1/C(n-1,k-1)}`.
* `minorRootAvg_succ_le`, `minorRootAvg_one`, `minorRootAvg_card`: **Theorem 17.9.4**.
* `condMinorMean_le_succ`, `condMinorMean_one`, `condMinorMean_card`: **Theorem 17.9.5**.
* `prod_condVar_le_det`, `prod_condVar_le_det_le_prod_diag`: (17.124) and **Corollary (17.126)**,
  `∏ σᵢ² ≤ |K| ≤ ∏ Kᵢᵢ`.
* `det_rpow_add_det_rpow_le`: **Theorem 17.9.7 (Minkowski)**,
  `|K₁|^{1/n} + |K₂|^{1/n} ≤ |K₁ + K₂|^{1/n}`.

## Implementation notes

The book derives these results from the entropy inequalities for Gaussian vectors; the
submodularity of `log |K(S)|` is the Gaussian case of `isSubmodular_subsetEntropy`, and we prove
it with matrix algebra. Minkowski's inequality is proved by simultaneous diagonalization and the
AM–GM inequality instead of the entropy power inequality.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 17.9
-/

open Matrix Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Koteljanskii's inequality -/

section Block

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
  [DecidableEq γ]

/-- **Koteljanskii's inequality**, block form: for `K ≻ 0` indexed by `γ ⊕ (α ⊕ β)`,
`|K| |K_γ| ≤ |K_{γ ∪ α}| |K_{γ ∪ β}|`. -/
theorem det_mul_det_le_of_block {K : Matrix (γ ⊕ (α ⊕ β)) (γ ⊕ (α ⊕ β)) ℝ} (hK : K.PosDef) :
    K.det * K.toBlocks₁₁.det ≤
      (K.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det *
        (K.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det := by
  set Ka := K.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)
  set Kb := K.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)
  have hKa : Ka.PosDef :=
    hK.submatrix (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)
  have hKb : Kb.PosDef :=
    hK.submatrix (Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩)
  have ha : schurCompl Ka = (schurCompl K).toBlocks₁₁ := by ext i j; rfl
  have hb : schurCompl Kb = (schurCompl K).toBlocks₂₂ := by ext i j; rfl
  have h1 : Ka.toBlocks₁₁ = K.toBlocks₁₁ := by ext i j; rfl
  have h2 : Kb.toBlocks₁₁ = K.toBlocks₁₁ := by ext i j; rfl
  rw [det_eq_mul_det_schurCompl hK, det_eq_mul_det_schurCompl hKa,
    det_eq_mul_det_schurCompl hKb, h1, h2, ha, hb]
  have hA := (toBlocks₁₁_posDef hK).det_pos
  have hF := det_le_det_mul_det (schurCompl_posDef hK)
  calc K.toBlocks₁₁.det * (schurCompl K).det * K.toBlocks₁₁.det
      ≤ K.toBlocks₁₁.det * ((schurCompl K).toBlocks₁₁.det * (schurCompl K).toBlocks₂₂.det) *
          K.toBlocks₁₁.det := by gcongr
    _ = _ := by ring

end Block

variable {ι : Type*} [DecidableEq ι]

/-- The principal minor `|K(S)|` of `K` on the indices in `S`. -/
def principalMinor (K : Matrix ι ι ℝ) (S : Finset ι) : ℝ :=
  (K.submatrix (fun i : S => (i : ι)) (fun i : S => (i : ι))).det

variable {K : Matrix ι ι ℝ}

/-- The determinant of `K` restricted along an injective map with range `S` is `|K(S)|`. -/
lemma det_submatrix_eq_principalMinor {τ : Type*} [Fintype τ] [DecidableEq τ] (K : Matrix ι ι ℝ)
    {f : τ → ι} (hf : Function.Injective f) {S : Finset ι} (hS : ∀ x, x ∈ S ↔ ∃ t, f t = x) :
    (K.submatrix f f).det = principalMinor K S := by
  let e : τ ≃ S := Equiv.ofBijective (fun t => ⟨f t, (hS _).2 ⟨t, rfl⟩⟩)
    ⟨fun a b h => hf (congrArg Subtype.val h), fun x => by
      obtain ⟨t, ht⟩ := (hS x).1 x.property
      exact ⟨t, Subtype.ext ht⟩⟩
  have : K.submatrix f f =
      (K.submatrix (fun i : S => (i : ι)) (fun i : S => (i : ι))).submatrix e e := rfl
  rw [this, det_submatrix_equiv_self]
  rfl

lemma principalMinor_pos (hK : K.PosDef) (S : Finset ι) : 0 < principalMinor K S :=
  (hK.submatrix Subtype.val_injective).det_pos

lemma principalMinor_empty (K : Matrix ι ι ℝ) : principalMinor K ∅ = 1 := det_isEmpty

lemma principalMinor_univ [Fintype ι] (K : Matrix ι ι ℝ) : principalMinor K univ = K.det := by
  rw [← det_submatrix_eq_principalMinor K Function.injective_id (fun x => by simp)]
  rfl

lemma principalMinor_singleton (K : Matrix ι ι ℝ) (i : ι) : principalMinor K {i} = K i i := by
  rw [← det_submatrix_eq_principalMinor K (f := fun _ : Unit => i) (fun _ _ _ => rfl)
    (fun x => by simp [eq_comm]), det_unique]
  rfl

/-- **Koteljanskii's inequality.** For `K ≻ 0`, `|K(A ∪ B)| |K(A ∩ B)| ≤ |K(A)| |K(B)|`. -/
theorem principalMinor_union_mul_inter_le (hK : K.PosDef) (A B : Finset ι) :
    principalMinor K (A ∪ B) * principalMinor K (A ∩ B) ≤
      principalMinor K A * principalMinor K B := by
  let F : ↥(A ∩ B) ⊕ (↥(A \ B) ⊕ ↥(B \ A)) → ι :=
    Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  have hF : Function.Injective F := by
    refine Subtype.val_injective.sumElim (Subtype.val_injective.sumElim Subtype.val_injective
      fun a b h => ?_) fun a b h => ?_
    · have ha := a.property; have hb := b.property
      simp only [mem_sdiff] at ha hb
      exact ha.2 (h ▸ hb.1)
    · have ha := a.property
      simp only [mem_inter] at ha
      rcases b with b | b <;> have hb := b.property <;> simp only [mem_sdiff] at hb <;>
        simp only [Sum.elim_inl, Sum.elim_inr] at h
      · exact hb.2 (h ▸ ha.2)
      · exact hb.2 (h ▸ ha.1)
  have hM : (K.submatrix F F).PosDef := hK.submatrix hF
  have h := det_mul_det_le_of_block hM
  have e1 : (K.submatrix F F).det = principalMinor K (A ∪ B) := by
    refine det_submatrix_eq_principalMinor K hF fun x => ⟨fun hx => ?_, ?_⟩
    · by_cases hA : x ∈ A
      · by_cases hB : x ∈ B
        · exact ⟨Sum.inl ⟨x, mem_inter.2 ⟨hA, hB⟩⟩, rfl⟩
        · exact ⟨Sum.inr (Sum.inl ⟨x, mem_sdiff.2 ⟨hA, hB⟩⟩), rfl⟩
      · have hB : x ∈ B := by rcases mem_union.1 hx with h | h; exacts [absurd h hA, h]
        exact ⟨Sum.inr (Sum.inr ⟨x, mem_sdiff.2 ⟨hB, hA⟩⟩), rfl⟩
    · rintro ⟨t | t | t, rfl⟩
      · exact mem_union_left _ (mem_inter.1 t.property).1
      · exact mem_union_left _ (mem_sdiff.1 t.property).1
      · exact mem_union_right _ (mem_sdiff.1 t.property).1
  have e2 : (K.submatrix F F).toBlocks₁₁.det = principalMinor K (A ∩ B) :=
    det_submatrix_eq_principalMinor K Subtype.val_injective fun x =>
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨t, rfl⟩; exact t.property⟩
  have e3 : ((K.submatrix F F).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det =
      principalMinor K A := by
    rw [submatrix_submatrix]
    refine det_submatrix_eq_principalMinor K
      (hF.comp (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)) fun x =>
        ⟨fun hx => ?_, ?_⟩
    · by_cases hB : x ∈ B
      · exact ⟨Sum.inl ⟨x, mem_inter.2 ⟨hx, hB⟩⟩, rfl⟩
      · exact ⟨Sum.inr ⟨x, mem_sdiff.2 ⟨hx, hB⟩⟩, rfl⟩
    · rintro ⟨t | t, rfl⟩
      · exact (mem_inter.1 t.property).1
      · exact (mem_sdiff.1 t.property).1
  have e4 : ((K.submatrix F F).submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det =
      principalMinor K B := by
    rw [submatrix_submatrix]
    refine det_submatrix_eq_principalMinor K
      (hF.comp (Sum.map_injective.2 ⟨Function.injective_id, Sum.inr_injective⟩)) fun x =>
        ⟨fun hx => ?_, ?_⟩
    · by_cases hA : x ∈ A
      · exact ⟨Sum.inl ⟨x, mem_inter.2 ⟨hA, hx⟩⟩, rfl⟩
      · exact ⟨Sum.inr ⟨x, mem_sdiff.2 ⟨hx, hA⟩⟩, rfl⟩
    · rintro ⟨t | t, rfl⟩
      · exact (mem_inter.1 t.property).2
      · exact (mem_sdiff.1 t.property).1
  rwa [e1, e2, e3, e4] at h

/-! ### Han's inequalities for principal minors -/

variable {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}

/-- `S ↦ log |K(S)|`, the entropy `h(X(S))` of `X ∼ N(0, K)` up to the term `½ |S| log 2πe`
and the factor `½`. -/
def logMinor (K : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ := log (principalMinor K S)

lemma logMinor_empty (K : Matrix (Fin n) (Fin n) ℝ) : logMinor K ∅ = 0 := by
  rw [logMinor, principalMinor_empty, log_one]

/-- `S ↦ log |K(S)|` is submodular. -/
theorem isSubmodular_logMinor (hK : K.PosDef) : IsSubmodular (logMinor K) := by
  intro A B
  simp only [logMinor]
  rw [← log_mul (principalMinor_pos hK _).ne' (principalMinor_pos hK _).ne',
    ← log_mul (principalMinor_pos hK _).ne' (principalMinor_pos hK _).ne']
  exact log_le_log (mul_pos (principalMinor_pos hK _) (principalMinor_pos hK _))
    (principalMinor_union_mul_inter_le hK A B)

/-- **(17.117)** The product `Pₖ` of the `k × k` principal minors. -/
def minorProd (K : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∏ S ∈ powersetCard k univ, principalMinor K S

lemma minorProd_pos (hK : K.PosDef) (k : ℕ) : 0 < minorProd K k :=
  prod_pos fun S _ => principalMinor_pos hK S

lemma log_minorProd (hK : K.PosDef) (k : ℕ) :
    log (minorProd K k) = ∑ S ∈ powersetCard k univ, logMinor K S :=
  log_prod fun S _ => (principalMinor_pos hK S).ne'

/-- **Theorem 17.9.3 (Szász), (17.118).** `P_{k+1}^{1/C(n-1,k)} ≤ Pₖ^{1/C(n-1,k-1)}`. -/
theorem minorProd_rpow_succ_le (hK : K.PosDef) {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    minorProd K (k + 1) ^ (1 / ((n - 1).choose k : ℝ)) ≤
      minorProd K k ^ (1 / ((n - 1).choose (k - 1) : ℝ)) := by
  have hH := subsetAvg_succ_le (isSubmodular_logMinor hK) (logMinor_empty K) hk hkn
  rw [subsetAvg_eq, subsetAvg_eq] at hH
  rw [rpow_def_of_pos (minorProd_pos hK _), rpow_def_of_pos (minorProd_pos hK _), exp_le_exp,
    log_minorProd hK, log_minorProd hK]
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hH ⊢
  set A := ∑ S ∈ powersetCard (k + 1 + 1) univ, logMinor K S
  set B := ∑ S ∈ powersetCard (k + 1) univ, logMinor K S
  have c1 : ((n : ℝ) + 1) * n.choose k = (n + 1).choose (k + 1) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  have c2 : ((n : ℝ) + 1) * n.choose (k + 1) =
      (n + 1).choose (k + 1 + 1) * ((k : ℝ) + 1 + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n (k + 1)
  have hc1 : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega)
  have hc2 : (0 : ℝ) < n.choose (k + 1) := by exact_mod_cast Nat.choose_pos (by omega)
  push_cast at hH
  have e1 : A * (1 / (n.choose (k + 1) : ℝ)) =
      ((n : ℝ) + 1) * (A / (((k : ℝ) + 1 + 1) * (n + 1).choose (k + 1 + 1))) := by
    rw [mul_comm ((k : ℝ) + 1 + 1), ← c2]
    field_simp
  have e2 : B * (1 / (n.choose k : ℝ)) =
      ((n : ℝ) + 1) * (B / (((k : ℝ) + 1) * (n + 1).choose (k + 1))) := by
    rw [mul_comm ((k : ℝ) + 1), ← c1]
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hH (by positivity)

/-- **(17.119)** The average `Sₖ = (1/C(n, k)) ∑_{|S| = k} |K(S)|^{1/k}`. -/
def minorRootAvg (K : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  (∑ S ∈ powersetCard k univ, principalMinor K S ^ (1 / (k : ℝ))) / n.choose k

lemma minorRootAvg_eq (hK : K.PosDef) (k : ℕ) :
    minorRootAvg K k = subsetExpAvg (logMinor K) 1 k := by
  simp only [minorRootAvg, subsetExpAvg, one_mul, logMinor]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [rpow_def_of_pos (principalMinor_pos hK S), mul_one_div]

/-- **Theorem 17.9.4, (17.120).** `S_{k+1} ≤ Sₖ`. -/
theorem minorRootAvg_succ_le (hK : K.PosDef) {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    minorRootAvg K (k + 1) ≤ minorRootAvg K k := by
  rw [minorRootAvg_eq hK, minorRootAvg_eq hK]
  exact subsetExpAvg_succ_le (isSubmodular_logMinor hK) (logMinor_empty K) zero_le_one hk hkn

/-- **Theorem 17.9.4, (17.120).** `S₁ = tr(K)/n`. -/
theorem minorRootAvg_one (K : Matrix (Fin n) (Fin n) ℝ) : minorRootAvg K 1 = K.trace / n := by
  rw [minorRootAvg, powersetCard_one, sum_map, Nat.choose_one_right]
  simp only [Function.Embedding.coeFn_mk, principalMinor_singleton, Nat.cast_one, div_one,
    rpow_one]
  rfl

/-- **Theorem 17.9.4, (17.120).** `Sₙ = |K|^{1/n}`. -/
theorem minorRootAvg_card (K : Matrix (Fin n) (Fin n) ℝ) :
    minorRootAvg K n = K.det ^ (1 / (n : ℝ)) := by
  have h : powersetCard n (univ : Finset (Fin n)) = {univ} := by
    simpa using powersetCard_self (univ : Finset (Fin n))
  rw [minorRootAvg, h, sum_singleton, Nat.choose_self, Nat.cast_one, div_one,
    principalMinor_univ]

/-- **(17.121)** `Qₖ = (∏_{|S| = k} |K|/|K(Sᶜ)|)^{1/(k C(n, k))}`. -/
def condMinorMean (K : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  (∏ S ∈ powersetCard k univ, K.det / principalMinor K Sᶜ) ^ (1 / (k * n.choose k : ℝ))

lemma condMinorMean_eq (hK : K.PosDef) (k : ℕ) :
    condMinorMean K k = exp (subsetCondAvg (logMinor K) k) := by
  have hpos : ∀ S, 0 < K.det / principalMinor K Sᶜ := fun S =>
    div_pos hK.det_pos (principalMinor_pos hK _)
  rw [condMinorMean, rpow_def_of_pos (prod_pos fun S _ => hpos S), subsetCondAvg_eq,
    log_prod fun S _ => (hpos S).ne']
  congr 1
  rw [mul_one_div]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [log_div hK.det_pos.ne' (principalMinor_pos hK _).ne', logMinor, logMinor,
    principalMinor_univ]

/-- **Theorem 17.9.5, (17.122).** `Qₖ ≤ Q_{k+1}`. -/
theorem condMinorMean_le_succ (hK : K.PosDef) {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    condMinorMean K k ≤ condMinorMean K (k + 1) := by
  rw [condMinorMean_eq hK, condMinorMean_eq hK, exp_le_exp]
  exact subsetCondAvg_le_succ (isSubmodular_logMinor hK) hk hkn

/-- **(17.125)** `σᵢ² = |K|/|K({i}ᶜ)|`, the conditional variance of `Xᵢ` given the other
coordinates of `X ∼ N(0, K)`. -/
def condVar (K : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := K.det / principalMinor K {i}ᶜ

/-- **Theorem 17.9.5, (17.122).** `Q₁ = (∏ᵢ σᵢ²)^{1/n}`. -/
theorem condMinorMean_one (K : Matrix (Fin n) (Fin n) ℝ) :
    condMinorMean K 1 = (∏ i, condVar K i) ^ (1 / (n : ℝ)) := by
  rw [condMinorMean, powersetCard_one, prod_map, Nat.choose_one_right, Nat.cast_one, one_mul]
  rfl

/-- **Theorem 17.9.5, (17.122).** `Qₙ = |K|^{1/n}`. -/
theorem condMinorMean_card (K : Matrix (Fin n) (Fin n) ℝ) :
    condMinorMean K n = K.det ^ (1 / (n : ℝ)) := by
  have h : powersetCard n (univ : Finset (Fin n)) = {univ} := by
    simpa using powersetCard_self (univ : Finset (Fin n))
  rw [condMinorMean, h, prod_singleton, compl_univ, principalMinor_empty, div_one,
    Nat.choose_self, Nat.cast_one, mul_one]

/-- **(17.124)** `∏ᵢ σᵢ² ≤ |K|`. -/
theorem prod_condVar_le_det (hK : K.PosDef) : ∏ i, condVar K i ≤ K.det := by
  have hpos : ∀ i, 0 < condVar K i := fun i => div_pos hK.det_pos (principalMinor_pos hK _)
  have h := sum_sub_erase_le (isSubmodular_logMinor hK) univ
  rw [logMinor_empty, sub_zero] at h
  rw [← log_le_log_iff (prod_pos fun i _ => hpos i) hK.det_pos,
    log_prod fun i _ => (hpos i).ne']
  calc ∑ i, log (condVar K i) = ∑ i, (logMinor K univ - logMinor K (univ.erase i)) := by
        refine sum_congr rfl fun i _ => ?_
        rw [condVar, log_div hK.det_pos.ne' (principalMinor_pos hK _).ne', logMinor, logMinor,
          principalMinor_univ, compl_singleton]
    _ ≤ logMinor K univ := h
    _ = log K.det := by rw [logMinor, principalMinor_univ]

/-- **Corollary (17.126).** `∏ᵢ σᵢ² ≤ |K| ≤ ∏ᵢ Kᵢᵢ`: the determinant of a covariance matrix lies
between the product of the conditional variances and the product of the variances. -/
theorem prod_condVar_le_det_le_prod_diag (hK : K.PosDef) :
    ∏ i, condVar K i ≤ K.det ∧ K.det ≤ ∏ i, K i i :=
  ⟨prod_condVar_le_det hK, det_le_prod_diag hK⟩

/-! ### Minkowski's inequality -/

omit [DecidableEq ι] in
/-- The geometric mean is superadditive: `(∏ aᵢ)^{1/N} + (∏ bᵢ)^{1/N} ≤ (∏ (aᵢ + bᵢ))^{1/N}` for
`a, b ≥ 0`, where `N` is the number of factors. -/
theorem prod_rpow_add_prod_rpow_le [Fintype ι] [Nonempty ι] {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) :
    (∏ i, a i) ^ (1 / (Fintype.card ι : ℝ)) + (∏ i, b i) ^ (1 / (Fintype.card ι : ℝ)) ≤
      (∏ i, (a i + b i)) ^ (1 / (Fintype.card ι : ℝ)) := by
  set w : ℝ := 1 / (Fintype.card ι : ℝ)
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : 0 < w := by positivity
  have hRHS : 0 ≤ (∏ i, (a i + b i)) ^ w :=
    rpow_nonneg (prod_nonneg fun i _ => add_nonneg (ha i) (hb i)) _
  by_cases h0 : ∃ i, a i + b i = 0
  · obtain ⟨i, hi⟩ := h0
    have hai : a i = 0 := by linarith [ha i, hb i]
    have hbi : b i = 0 := by linarith [ha i, hb i]
    rw [prod_eq_zero (mem_univ i) hai, prod_eq_zero (mem_univ i) hbi, zero_rpow hw.ne', add_zero]
    exact hRHS
  push Not at h0
  have hc : ∀ i, 0 < a i + b i := fun i => lt_of_le_of_ne (add_nonneg (ha i) (hb i)) (h0 i).symm
  have hwsum : ∑ _i : ι, w = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    simp only [w]
    field_simp
  have hamgm : ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) →
      (∏ i, z i) ^ w / (∏ i, (a i + b i)) ^ w ≤ ∑ i, w * (z i / (a i + b i)) := by
    intro z hz
    rw [← div_rpow (prod_nonneg fun i _ => hz i) (prod_pos fun i _ => hc i).le, ← prod_div_distrib,
      ← finsetProd_rpow _ _ fun i _ => div_nonneg (hz i) (hc i).le]
    exact geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => hw.le) hwsum
      fun i _ => div_nonneg (hz i) (hc i).le
  have hP : 0 < (∏ i, (a i + b i)) ^ w := rpow_pos_of_pos (prod_pos fun i _ => hc i) _
  have h := add_le_add (hamgm a ha) (hamgm b hb)
  rw [← sum_add_distrib] at h
  have hsum : ∑ i, (w * (a i / (a i + b i)) + w * (b i / (a i + b i))) = 1 := by
    rw [← hwsum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_add, ← add_div, div_self (hc i).ne', mul_one]
  rw [hsum, ← add_div, div_le_one hP] at h
  exact h

lemma det_eq_prod_eigenvalues_real [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.det = ∏ i, hA.eigenvalues i := by
  simpa using hA.det_eq_prod_eigenvalues

/-- **Theorem 17.9.7 (Minkowski), (17.136).** For positive semidefinite `n × n` matrices with
`n ≥ 1`, `|K₁|^{1/n} + |K₂|^{1/n} ≤ |K₁ + K₂|^{1/n}`. -/
theorem det_rpow_add_det_rpow_le [Fintype ι] [Nonempty ι] {K₁ K₂ : Matrix ι ι ℝ}
    (h₁ : K₁.PosSemidef) (h₂ : K₂.PosSemidef) :
    K₁.det ^ (1 / (Fintype.card ι : ℝ)) + K₂.det ^ (1 / (Fintype.card ι : ℝ)) ≤
      (K₁ + K₂).det ^ (1 / (Fintype.card ι : ℝ)) := by
  set w : ℝ := 1 / (Fintype.card ι : ℝ)
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : 0 < w := by positivity
  by_cases hd : K₁.det = 0
  · rw [hd, zero_rpow hw.ne', zero_add]
    refine rpow_le_rpow h₂.det_nonneg (det_le_det_of_posSemidef_sub h₂ ?_) hw.le
    simpa using h₁
  have hpd : K₁.PosDef := h₁.posDef_iff_det_ne_zero.2 hd
  obtain ⟨S, hS⟩ := exists_mul_mul_transpose_eq_one hpd
  set M := S * K₂ * Sᵀ
  have hM : M.PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using h₂.mul_mul_conjTranspose_same S
  have hd1 := congrArg det hS
  rw [det_mul_mul_transpose, det_one] at hd1
  have hsum : S * (K₁ + K₂) * Sᵀ = 1 + M := by
    rw [Matrix.mul_add, Matrix.add_mul, hS]
  have hd2 := det_mul_mul_transpose S K₂
  have hd3 := det_mul_mul_transpose S (K₁ + K₂)
  rw [hsum] at hd3
  set d := S.det ^ 2
  have hdpos : 0 < d := by
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, zero_mul] at hd1
      exact zero_ne_one hd1
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hd0)
  -- `|K₁| = 1/d`, `|K₂| = |M|/d`, `|K₁ + K₂| = |1 + M|/d`.
  have e1 : K₁.det = 1 / d := by field_simp; linarith
  have e2 : K₂.det = M.det / d := by field_simp; linarith
  have e3 : (K₁ + K₂).det = (1 + M).det / d := by field_simp; linarith
  have hl := hM.eigenvalues_nonneg
  have hdetM : M.det = ∏ i, hM.1.eigenvalues i := det_eq_prod_eigenvalues_real hM.1
  have hdet1M : (1 + M).det = ∏ i, (1 + hM.1.eigenvalues i) := by
    have := det_smul_one_add_smul hM.1 1 1
    simpa using this
  have key := prod_rpow_add_prod_rpow_le (a := fun _ => (1 : ℝ)) (b := hM.1.eigenvalues)
    (fun _ => zero_le_one) hl
  simp only [prod_const_one, one_rpow] at key
  rw [← hdetM, ← hdet1M] at key
  rw [e1, e2, e3, div_rpow hM.det_nonneg hdpos.le, div_rpow zero_le_one hdpos.le,
    div_rpow (by rw [hdet1M]; exact prod_nonneg fun i _ => by linarith [hl i]) hdpos.le,
    one_rpow, ← add_div]
  exact div_le_div_of_nonneg_right key (rpow_pos_of_pos hdpos _).le

end InfoTheory
