/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.ConvexOptimization
public import InfoTheoryLib.GaussianChannel.Vector

/-!
# Determinant maximization

The problem `maximize log |X + K| subject to X ≽ 0, tr X ≤ P` for a positive definite `K`, as in
Appendix E of El Gamal and Kim. The KKT conditions `(X + K)⁻¹ + Υ - λ I = 0`, `tr(Υ X) = 0` and
`λ (tr X - P) = 0` characterize its solution, which is unique and given by water-filling on the
eigenvalues of `K`.

## Main definitions

* `IsDetMaxKKT K P X Υ l`: the KKT conditions.
* `IsDetMaxOptimal K P X`: `X` is optimal.
* `detMaxProgram K P`: the problem as a `ConvexOpt.Program`, with `X ≽ 0` as the domain.
* `burgProgram`: differential entropy maximization under correlation constraints.

## Main statements

* `isDetMaxOptimal_of_kkt`: the KKT conditions are sufficient.
* `exists_detMaxKKT`: **water-filling** gives a solution of the KKT conditions.
* `isDetMaxOptimal_iff_kkt`: **the KKT conditions characterize the optimal `X`**.
* `eq_of_isDetMaxOptimal`: the optimal `X` is unique.
* `posSemidef_iff_forall_trace_mul_nonneg`: `X ≽ 0` iff `tr(Υ X) ≥ 0` for every `Υ ≽ 0`.
* `detMaxProgram_isConvex`, `detMaxProgram_isSlaterPoint`, `detMaxProgram_strong_duality`: Slater's
  condition and strong duality.
* `burgProgram_isConvex`: the problem of Burg is convex.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  E
* [S. Boyd and L. Vandenberghe, *Convex Optimization*][boyd2004]
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The strict tangent bound -/

/-- `log |M| < tr M - dim` for a positive definite `M ≠ I`. -/
lemma log_det_lt_trace_sub_card' {M : Matrix n n ℝ} (hM : M.PosDef) (hne : M ≠ 1) :
    log M.det < M.trace - Fintype.card n := by
  have hex : ∃ i, PosDef.eigval hM i ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [PosDef.eq_eigU hM]
    have : PosDef.eigval hM = fun _ => 1 := funext hcon
    rw [this, diagonal_one, Matrix.mul_one, PosDef.eigU_mul_transpose]
  obtain ⟨i, hi⟩ := hex
  rw [hM.1.det_eq_prod_eigenvalues, hM.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [log_prod fun i _ => (hM.eigenvalues_pos i).ne']
  have h : ∑ i, log (hM.1.eigenvalues i) < ∑ i, (hM.1.eigenvalues i - 1) :=
    sum_lt_sum (fun j _ => log_le_sub_one_of_pos (hM.eigenvalues_pos j))
      ⟨i, mem_univ i, log_lt_sub_one_of_pos (hM.eigenvalues_pos i) hi⟩
  simpa [sum_sub_distrib] using h

/-- `log |A + Δ| - log |A| < tr(A⁻¹ Δ)` for `Δ ≠ 0`. -/
lemma log_det_add_sub_lt {A Δ : Matrix n n ℝ} (hA : A.PosDef) (hB : (A + Δ).PosDef) (hΔ : Δ ≠ 0) :
    log (A + Δ).det - log A.det < (A⁻¹ * Δ).trace := by
  obtain ⟨M, hM, h₁, h₂, h₃⟩ := exists_whitened hA hB
  have hne : M ≠ 1 := fun h => hΔ (by simpa using h₃ h)
  have h := log_det_lt_trace_sub_card' hM hne
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA.det_pos.ne'
  rw [Matrix.mul_add, nonsing_inv_mul A hu, trace_add, trace_one] at h₂
  rw [h₁]
  linarith

/-! ### The KKT conditions -/

/-- **Pages E-6 and E-7 of [elgamal2010].** The KKT conditions of the problem: feasibility, the
stationarity of the Lagrangian and complementary slackness. -/
structure IsDetMaxKKT (K : Matrix n n ℝ) (P : ℝ) (X Υ : Matrix n n ℝ) (l : ℝ) : Prop where
  feasible : X.PosSemidef
  trace_le : X.trace ≤ P
  dual : Υ.PosSemidef
  nonneg : 0 ≤ l
  stationary : (X + K)⁻¹ + Υ - l • 1 = 0
  slack_dual : (Υ * X).trace = 0
  slack_trace : l * (X.trace - P) = 0

/-- `X` solves `maximize log |X + K| subject to X ≽ 0, tr X ≤ P`. -/
def IsDetMaxOptimal (K : Matrix n n ℝ) (P : ℝ) (X : Matrix n n ℝ) : Prop :=
  X.PosSemidef ∧ X.trace ≤ P ∧
    ∀ Y : Matrix n n ℝ, Y.PosSemidef → Y.trace ≤ P → log (Y + K).det ≤ log (X + K).det

variable {K X Y Υ : Matrix n n ℝ} {P l : ℝ}

/-- The trace of `A⁻¹ (Y - X)` at a KKT point. -/
lemma IsDetMaxKKT.trace_eq (h : IsDetMaxKKT K P X Υ l) (Y : Matrix n n ℝ) :
    ((X + K)⁻¹ * (Y - X)).trace = l * (Y.trace - P) - (Υ * Y).trace := by
  have hinv : (X + K)⁻¹ = l • 1 - Υ := by
    have := h.stationary
    rw [eq_sub_iff_add_eq]
    rwa [sub_eq_zero] at this
  have h₂ := h.slack_trace
  rw [hinv, Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, trace_sub,
    Matrix.mul_sub, trace_sub, h.slack_dual, smul_eq_mul]
  linarith

/-- **Page E-6 of [elgamal2010].** The KKT conditions are sufficient for optimality. -/
theorem isDetMaxOptimal_of_kkt (hK : K.PosDef) (h : IsDetMaxKKT K P X Υ l) :
    IsDetMaxOptimal K P X := by
  refine ⟨h.feasible, h.trace_le, fun Y hY hYP => ?_⟩
  have hA : (X + K).PosDef := Matrix.PosDef.posSemidef_add h.feasible hK
  have e : Y + K = (X + K) + (Y - X) := by abel
  have hB : ((X + K) + (Y - X)).PosDef := e ▸ Matrix.PosDef.posSemidef_add hY hK
  rw [e]
  have h₁ := log_det_add_sub_le hA hB
  rw [h.trace_eq] at h₁
  have h₂ := trace_mul_nonneg_of_posSemidef h.dual hY
  have h₃ : l * (Y.trace - P) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h.nonneg (by linarith)
  linarith

/-- The solution of the KKT conditions is the only optimal `X`. -/
theorem eq_of_isDetMaxOptimal (hK : K.PosDef) (h : IsDetMaxKKT K P X Υ l)
    (hY : IsDetMaxOptimal K P Y) : Y = X := by
  by_contra hne
  have hA : (X + K).PosDef := Matrix.PosDef.posSemidef_add h.feasible hK
  have e : Y + K = (X + K) + (Y - X) := by abel
  have hB : ((X + K) + (Y - X)).PosDef := e ▸ Matrix.PosDef.posSemidef_add hY.1 hK
  have h₁ := log_det_add_sub_lt hA hB (sub_ne_zero.2 hne)
  rw [h.trace_eq, ← e] at h₁
  have h₂ := trace_mul_nonneg_of_posSemidef h.dual hY.1
  have h₃ : l * (Y.trace - P) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h.nonneg (by linarith [hY.2.1])
  have h₄ := hY.2.2 X h.feasible h.trace_le
  linarith

/-! ### Water-filling -/

/-- **Water-filling.** For `K ≻ 0` and `P ≥ 0`, the matrix `X = U diag((ν - dᵢ)⁺) Uᵀ` for the
eigendecomposition `K = U diag(dᵢ) Uᵀ` and the water level `ν`, with `λ = 1 / ν` and
`Υ = U diag(1 / ν - 1 / max(ν, dᵢ)) Uᵀ`, solves the KKT conditions. -/
theorem exists_detMaxKKT [Nonempty n] (hK : K.PosDef) (hP : 0 ≤ P) :
    ∃ (X Υ : Matrix n n ℝ) (l : ℝ), IsDetMaxKKT K P X Υ l := by
  set U := PosDef.eigU hK with hUd
  set N := PosDef.eigval hK with hN
  have hU : Uᵀ * U = 1 := PosDef.eigU_transpose_mul hK
  have hU' : U * Uᵀ = 1 := PosDef.eigU_mul_transpose hK
  have hNpos : ∀ i, 0 < N i := PosDef.eigval_pos hK
  obtain ⟨ν, -, ⟨i₀, hi₀⟩, hsum⟩ := exists_waterLevel N hP
  have hν : 0 < ν := (hNpos i₀).trans_le hi₀
  set p := waterFill N ν with hp
  set q : n → ℝ := fun i => max ν (N i) with hq
  have hqν : ∀ i, ν ≤ q i := fun i => le_max_left _ _
  have hqpos : ∀ i, 0 < q i := fun i => hν.trans_le (hqν i)
  set r : n → ℝ := fun i => ν⁻¹ - (q i)⁻¹ with hr
  have hmul : ∀ a b : n → ℝ, (U * diagonal a * Uᵀ) * (U * diagonal b * Uᵀ) =
      U * diagonal (fun i => a i * b i) * Uᵀ := fun a b => by
    calc (U * diagonal a * Uᵀ) * (U * diagonal b * Uᵀ)
        = U * diagonal a * (Uᵀ * U) * diagonal b * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
  have htr : ∀ a : n → ℝ, (U * diagonal a * Uᵀ).trace = ∑ i, a i := fun a => by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one, trace_diagonal]
  have hXK : U * diagonal p * Uᵀ + K = U * diagonal q * Uᵀ := by
    conv_lhs => rw [PosDef.eq_eigU hK]
    rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3
    funext i
    rw [add_comm]
    exact add_waterFill N ν i
  have hinv : (U * diagonal p * Uᵀ + K)⁻¹ = U * diagonal (fun i => (q i)⁻¹) * Uᵀ := by
    rw [hXK]
    refine inv_eq_right_inv ?_
    rw [hmul]
    have : (fun i => q i * (q i)⁻¹) = fun _ => (1 : ℝ) :=
      funext fun i => mul_inv_cancel₀ (hqpos i).ne'
    rw [this, diagonal_one, Matrix.mul_one, hU']
  refine ⟨U * diagonal p * Uᵀ, U * diagonal r * Uᵀ, ν⁻¹,
    posSemidef_mul_diagonal_mul U (waterFill_nonneg N ν), ?_,
    posSemidef_mul_diagonal_mul U fun i => ?_, inv_nonneg.2 hν.le, ?_, ?_, ?_⟩
  · rw [htr]
    exact hsum.le
  · exact sub_nonneg.2 (inv_anti₀ hν (hqν i))
  · rw [hinv]
    have e : (ν⁻¹ • 1 : Matrix n n ℝ) = U * diagonal (fun _ => ν⁻¹) * Uᵀ := by
      have : (fun _ : n => ν⁻¹) = fun i => (q i)⁻¹ + r i := funext fun i => by simp [hr]
      rw [show diagonal (fun _ : n => ν⁻¹) = ν⁻¹ • (1 : Matrix n n ℝ) by
        ext i j
        by_cases h : i = j <;> simp [h]]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']
    rw [e, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add, ← Matrix.sub_mul, ← Matrix.mul_sub]
    have : diagonal (fun i => (q i)⁻¹ + r i) - diagonal (fun _ => ν⁻¹) = (0 : Matrix n n ℝ) := by
      ext i j
      by_cases h : i = j <;> simp [h, hr]
    rw [this]
    simp
  · rw [hmul, htr]
    refine sum_eq_zero fun i _ => ?_
    by_cases hi : ν ≤ N i
    · have : p i = 0 := max_eq_right (by linarith)
      rw [this, mul_zero]
    · have hqi : q i = ν := max_eq_left (not_le.1 hi).le
      simp [hr, hqi]
  · rw [htr, hsum]
    ring

/-- **Pages E-6 and E-7 of [elgamal2010].** The KKT conditions characterize the optimal `X`: the
matrix `X` is optimal if and only if there are `Υ ≽ 0` and `λ ≥ 0` that satisfy them. -/
theorem isDetMaxOptimal_iff_kkt [Nonempty n] (hK : K.PosDef) (hP : 0 ≤ P) :
    IsDetMaxOptimal K P X ↔ ∃ (Υ : Matrix n n ℝ) (l : ℝ), IsDetMaxKKT K P X Υ l := by
  constructor
  · intro hX
    obtain ⟨X₀, Υ, l, h⟩ := exists_detMaxKKT hK hP
    obtain rfl := eq_of_isDetMaxOptimal hK h hX
    exact ⟨Υ, l, h⟩
  · rintro ⟨Υ, l, h⟩
    exact isDetMaxOptimal_of_kkt hK h

omit [DecidableEq n] in
/-- **Page E-6 of [elgamal2010].** `X ≽ 0` if and only if `tr(Υ X) ≥ 0` for every `Υ ≽ 0`, for a
symmetric `X`. -/
theorem posSemidef_iff_forall_trace_mul_nonneg (hX : X.IsHermitian) :
    X.PosSemidef ↔ ∀ Υ : Matrix n n ℝ, Υ.PosSemidef → 0 ≤ (Υ * X).trace := by
  constructor
  · exact fun h Υ hΥ => trace_mul_nonneg_of_posSemidef hΥ h
  · intro h
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hX, fun v => ?_⟩
    have hv : (vecMulVec v v).PosSemidef := by
      simpa using posSemidef_vecMulVec_self_star v
    have := h _ hv
    have e : (vecMulVec v v * X).trace = star v ⬝ᵥ (X *ᵥ v) := by
      simp only [trace, diag_apply, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, mul_sum,
        Pi.star_apply, star_trivial]
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rwa [e] at this

/-! ### The problem as a convex program -/

/-- **Page E-6 of [elgamal2010].** The problem as `minimize -log |X + K|` on the domain `X ≽ 0`
subject to `tr X - P ≤ 0`, with no equality constraint. -/
def detMaxProgram (K : Matrix n n ℝ) (P : ℝ) : ConvexOpt.Program (Matrix n n ℝ) Unit (Fin 0) where
  dom := {X | X.PosSemidef}
  obj X := -log (X + K).det
  ineq _ X := X.trace - P
  A := 0
  b := 0

/-- The feasible set of the program. -/
lemma mem_feasible_detMaxProgram :
    X ∈ (detMaxProgram K P).feasible ↔ X.PosSemidef ∧ X.trace ≤ P := by
  simp [ConvexOpt.Program.feasible, detMaxProgram]

/-- The problem is convex. -/
theorem detMaxProgram_isConvex (hK : K.PosDef) : (detMaxProgram K P).IsConvex := by
  have hdom : Convex ℝ {X : Matrix n n ℝ | X.PosSemidef} := fun X hX Y hY a b ha hb _ =>
    (PosSemidef.smul hX ha).add (PosSemidef.smul hY hb)
  refine ⟨hdom, ⟨hdom, fun X hX Y hY a b ha hb hab => ?_⟩, fun _ => ⟨hdom, ?_⟩⟩
  · have hc := concaveOn_log_det.2 (x := X + K) (y := Y + K)
      (Matrix.PosDef.posSemidef_add hX hK) (Matrix.PosDef.posSemidef_add hY hK) ha hb hab
    have e : a • (X + K) + b • (Y + K) = a • X + b • Y + K := by
      have : K = a • K + b • K := by rw [← add_smul, hab, one_smul]
      nth_rw 3 [this]
      simp only [smul_add]
      abel
    rw [e] at hc
    simp only [detMaxProgram, smul_eq_mul] at hc ⊢
    linarith
  · intro X _ Y _ a b _ _ hab
    simp only [detMaxProgram, trace_add, trace_smul, smul_eq_mul]
    apply le_of_eq
    linear_combination P * hab

/-- **Page E-6 of [elgamal2010].** The problem satisfies Slater's condition, at the point
`X = (P / (2 n)) I`. -/
theorem detMaxProgram_isSlaterPoint [Nonempty n] (hP : 0 < P) :
    (detMaxProgram K P).IsSlaterPoint ((P / (2 * Fintype.card n)) • (1 : Matrix n n ℝ)) := by
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hd : ((P / (2 * Fintype.card n)) • (1 : Matrix n n ℝ)).PosSemidef :=
    PosSemidef.smul PosSemidef.one (by positivity)
  refine ⟨hd, fun _ => ?_, Subsingleton.elim _ _, fun _ => ⟨_, hd, 1, one_pos,
    Subsingleton.elim _ _⟩⟩
  · simp only [detMaxProgram, trace_smul, trace_one, smul_eq_mul]
    have : P / (2 * Fintype.card n) * (Fintype.card n : ℝ) = P / 2 := by field_simp
    linarith

/-- **Page E-6 of [elgamal2010].** Strong duality holds for the problem. -/
theorem detMaxProgram_strong_duality [Nonempty n] (hK : K.PosDef) (hP : 0 < P) :
    (detMaxProgram K P).dualValue = (detMaxProgram K P).primalValue :=
  (ConvexOpt.Program.strong_duality (detMaxProgram_isConvex hK) (detMaxProgram_isSlaterPoint hP)).1

/-- **The point on page E-6 of [elgamal2010] is not feasible in general.** With more than two
dimensions and `P > 0`, the matrix `X = (P / 2) I` has a trace larger than `P`. -/
theorem printed_detMax_point_infeasible (hn : 2 < Fintype.card n) (hP : 0 < P) :
    P < ((P / 2) • (1 : Matrix n n ℝ)).trace := by
  have : (2 : ℝ) < Fintype.card n := by exact_mod_cast hn
  simp only [trace_smul, trace_one, smul_eq_mul]
  nlinarith

/-! ### The problem of Burg -/

section Burg

variable {d : ℕ}

/-- **Page E-2 of [elgamal2010].** Differential entropy maximization under correlation constraints:
`maximize log |K| subject to K_{j, j+k} = a_k` for `k ∈ [0 : l]`, on positive definite `K`. The
constraints are indexed by the pairs `(j, j + k)`. -/
def burgProgram (l : ℕ) (a : ℕ → ℝ) :
    ConvexOpt.Program (Matrix (Fin d) (Fin d) ℝ) Empty
      {s : Fin d × Fin d // s.1 ≤ s.2 ∧ (s.2 : ℕ) - s.1 ≤ l} where
  dom := {K | K.PosDef}
  obj K := -log K.det
  ineq j _ := nomatch j
  A := { toFun := fun K s => K s.val.1 s.val.2
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }
  b s := a ((s.val.2 : ℕ) - s.val.1)

/-- **Page E-2 of [elgamal2010].** The problem of Burg is convex. -/
theorem burgProgram_isConvex (l : ℕ) (a : ℕ → ℝ) : (burgProgram (d := d) l a).IsConvex :=
  ⟨concaveOn_log_det.1, concaveOn_log_det.neg, fun j => nomatch j⟩

end Burg

end InfoTheory
