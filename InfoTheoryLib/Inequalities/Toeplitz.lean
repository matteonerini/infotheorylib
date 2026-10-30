/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Inequalities.Determinant

/-!
# Determinants of Toeplitz matrices

A Toeplitz matrix has `Kᵢⱼ = K_{i+1, j+1}`; it is the covariance matrix of a stationary process.
Let `Kₖ` be its leading `k × k` section. Then `|Kₖ|/|Kₖ₋₁|` and `|Kₖ|^{1/k}` decrease with `k`,
and they have the same limit (Theorem 17.9.6). For a Gaussian process these are
`h(Xₖ | Xₖ₋₁, …, X₁)` and `h(X₁, …, Xₖ)/k`, and the theorem is the matrix form of Theorem 4.2.1.

The ratio inequality `|Kₖ₊₂| |Kₖ| ≤ |Kₖ₊₁|²` is Koteljanskii's inequality for the index sets
`{0, …, k}` and `{1, …, k + 1}`, whose principal minors are both `|Kₖ₊₁|` by the Toeplitz
property; this is the matrix form of (17.131)–(17.132).

## Main definitions

* `leadingSection K k`: the leading `k × k` section `Kₖ` of an infinite matrix `K`.
* `IsToeplitz K`: `K (i + 1) (j + 1) = K i j`.

## Main statements

* `det_leadingSection_mul_le_sq`: `|Kₖ₊₂| |Kₖ| ≤ |Kₖ₊₁|²`.
* `det_ratio_succ_le`: **Theorem 17.9.6**, `|Kₖ₊₂|/|Kₖ₊₁| ≤ |Kₖ₊₁|/|Kₖ|`.
* `det_rpow_succ_le`: **Theorem 17.9.6, (17.127)**, `|Kₖ₊₁|^{1/(k+1)} ≤ |Kₖ|^{1/k}`.
* `tendsto_det_rpow_and_ratio`: **Theorem 17.9.6, (17.128)**,
  `lim |Kₙ|^{1/n} = lim |Kₙ|/|Kₙ₋₁|`.

## Implementation notes

An `n × n` Toeplitz matrix is the leading section `Kₙ` of an infinite Toeplitz matrix (extend
its diagonals arbitrarily), so the finite statements assume only that `Kₙ` is positive definite.
The limit is stated for an infinite matrix whose sections are all positive definite, as for the
covariance of a stationary process. We prove it directly, without the Cesàro mean, since the
limit of the ratios may be `0`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 17.9
-/

open Matrix Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- The leading `k × k` section `Kₖ = (Kᵢⱼ)_{i, j < k}` of an infinite matrix. -/
def leadingSection (K : ℕ → ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => K i j

/-- An infinite Toeplitz matrix: `Kᵢⱼ` depends only on `i - j`. -/
def IsToeplitz (K : ℕ → ℕ → ℝ) : Prop := ∀ i j, K (i + 1) (j + 1) = K i j

variable {K : ℕ → ℕ → ℝ}

lemma leadingSection_submatrix_castLE {k n : ℕ} (h : k ≤ n) :
    (leadingSection K n).submatrix (Fin.castLE h) (Fin.castLE h) = leadingSection K k := by
  ext i j
  simp [leadingSection]

lemma leadingSection_submatrix_succ (hT : IsToeplitz K) (k : ℕ) :
    (leadingSection K (k + 1)).submatrix Fin.succ Fin.succ = leadingSection K k := by
  ext i j
  simp only [leadingSection, submatrix_apply, of_apply, Fin.val_succ]
  exact hT _ _

lemma posDef_leadingSection_of_le {k n : ℕ} (hK : (leadingSection K n).PosDef) (h : k ≤ n) :
    (leadingSection K k).PosDef := by
  rw [← leadingSection_submatrix_castLE h]
  exact hK.submatrix (Fin.castLE_injective h)

lemma det_leadingSection_pos {k n : ℕ} (hK : (leadingSection K n).PosDef) (h : k ≤ n) :
    0 < (leadingSection K k).det :=
  (posDef_leadingSection_of_le hK h).det_pos

/-- `|Kₖ₊₂| |Kₖ| ≤ |Kₖ₊₁|²` for a Toeplitz matrix with `Kₖ₊₂ ≻ 0`. -/
theorem det_leadingSection_mul_le_sq (hT : IsToeplitz K) {k : ℕ}
    (hK : (leadingSection K (k + 2)).PosDef) :
    (leadingSection K (k + 2)).det * (leadingSection K k).det ≤
      (leadingSection K (k + 1)).det ^ 2 := by
  set M := leadingSection K (k + 2)
  set A : Finset (Fin (k + 2)) := univ.filter fun x => x ≠ Fin.last (k + 1)
  set B : Finset (Fin (k + 2)) := univ.filter fun x => x ≠ 0
  have hA : principalMinor M A = (leadingSection K (k + 1)).det := by
    rw [← det_submatrix_eq_principalMinor M (Fin.castSucc_injective _) (S := A)]
    · rw [show Fin.castSucc = Fin.castLE (Nat.le_succ (k + 1)) by rfl,
        leadingSection_submatrix_castLE]
    · intro x
      simp only [A, mem_filter, mem_univ, true_and]
      exact Fin.exists_castSucc_eq.symm
  have hB : principalMinor M B = (leadingSection K (k + 1)).det := by
    rw [← det_submatrix_eq_principalMinor M (Fin.succ_injective _) (S := B),
      leadingSection_submatrix_succ hT]
    intro x
    simp only [B, mem_filter, mem_univ, true_and]
    exact Fin.exists_succ_eq.symm
  have hAB : A ∪ B = univ := by
    ext x
    simp only [A, B, mem_union, mem_filter, mem_univ, true_and, iff_true]
    by_contra h
    push Not at h
    exact Fin.last_pos.ne' (h.1.symm.trans h.2)
  have hC : principalMinor M (A ∩ B) = (leadingSection K k).det := by
    have hf : Function.Injective fun t : Fin k => (Fin.castSucc t).succ :=
      (Fin.succ_injective _).comp (Fin.castSucc_injective _)
    rw [← det_submatrix_eq_principalMinor M hf (S := A ∩ B)]
    · have : M.submatrix (fun t : Fin k => (Fin.castSucc t).succ) (fun t => (Fin.castSucc t).succ)
          = ((M.submatrix Fin.succ Fin.succ).submatrix Fin.castSucc Fin.castSucc) := rfl
      rw [this, leadingSection_submatrix_succ hT,
        show (Fin.castSucc : Fin k → Fin (k + 1)) = Fin.castLE (Nat.le_succ k) by rfl,
        leadingSection_submatrix_castLE]
    · intro x
      simp only [A, B, mem_inter, mem_filter, mem_univ, true_and, Fin.ne_iff_vne, Fin.val_last,
        Fin.val_zero]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨x.val - 1, by omega⟩, Fin.ext ?_⟩
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      · rintro ⟨t, rfl⟩
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
  have h := principalMinor_union_mul_inter_le hK A B
  rwa [hAB, principalMinor_univ, hC, hA, hB, ← sq] at h

/-- **Theorem 17.9.6.** For a Toeplitz matrix, `|Kₖ₊₂|/|Kₖ₊₁| ≤ |Kₖ₊₁|/|Kₖ|`: the conditional
variances `σₖ² = |Kₖ|/|Kₖ₋₁|` decrease. -/
theorem det_ratio_succ_le (hT : IsToeplitz K) {n k : ℕ} (hK : (leadingSection K n).PosDef)
    (hk : k + 2 ≤ n) :
    (leadingSection K (k + 2)).det / (leadingSection K (k + 1)).det ≤
      (leadingSection K (k + 1)).det / (leadingSection K k).det := by
  have h := det_leadingSection_mul_le_sq hT (posDef_leadingSection_of_le hK hk)
  have h0 := det_leadingSection_pos hK (show k ≤ n by omega)
  have h1 := det_leadingSection_pos hK (show k + 1 ≤ n by omega)
  rw [div_le_div_iff₀ h1 h0]
  linarith

/-- `log |Kⱼ| = ∑_{i < j} log (|Kᵢ₊₁|/|Kᵢ|)`. -/
lemma log_det_leadingSection_eq_sum {n : ℕ} (hK : (leadingSection K n).PosDef) {j : ℕ}
    (hj : j ≤ n) :
    log (leadingSection K j).det =
      ∑ i ∈ range j, log ((leadingSection K (i + 1)).det / (leadingSection K i).det) := by
  induction j with
  | zero => simp [leadingSection]
  | succ j ih =>
    rw [sum_range_succ, ← ih (by omega), ← log_mul (det_leadingSection_pos hK (by omega)).ne'
      (div_pos (det_leadingSection_pos hK hj) (det_leadingSection_pos hK (by omega))).ne',
      mul_div_cancel₀ _ (det_leadingSection_pos hK (by omega)).ne']

/-- **Theorem 17.9.6, (17.127).** For a Toeplitz matrix, `|Kₖ₊₁|^{1/(k+1)} ≤ |Kₖ|^{1/k}`. -/
theorem det_rpow_succ_le (hT : IsToeplitz K) {n k : ℕ} (hK : (leadingSection K n).PosDef)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ n) :
    (leadingSection K (k + 1)).det ^ (1 / ((k : ℝ) + 1)) ≤
      (leadingSection K k).det ^ (1 / (k : ℝ)) := by
  set a : ℕ → ℝ := fun i => log ((leadingSection K (i + 1)).det / (leadingSection K i).det)
  -- `a` is decreasing on `[0, n - 1)`.
  have hanti' : ∀ i j, i ≤ j → j + 1 ≤ n → a j ≤ a i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      refine le_trans ?_ (ih (by omega))
      exact log_le_log (div_pos (det_leadingSection_pos hK (by omega))
        (det_leadingSection_pos hK (by omega))) (det_ratio_succ_le hT hK (k := j) (by omega))
  have hanti : ∀ i, i ≤ k → a k ≤ a i := fun i hi => hanti' i k hi hk
  have hlogk := log_det_leadingSection_eq_sum hK (j := k) (by omega)
  have hlogk1 := log_det_leadingSection_eq_sum hK (j := k + 1) hk
  rw [sum_range_succ] at hlogk1
  have hsum : (k : ℝ) * a k ≤ ∑ i ∈ range k, a i := by
    calc (k : ℝ) * a k = ∑ _i ∈ range k, a k := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ range k, a i := sum_le_sum fun i hi => hanti i (mem_range.1 hi).le
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk1
  rw [rpow_def_of_pos (det_leadingSection_pos hK hk),
    rpow_def_of_pos (det_leadingSection_pos hK (by omega)), exp_le_exp, hlogk1, hlogk,
    mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) hk']
  change (∑ i ∈ range k, a i + a k) * k ≤ (∑ i ∈ range k, a i) * (k + 1)
  nlinarith

/-- The ratios `rₖ = |Kₖ₊₁|/|Kₖ|` of an infinite Toeplitz matrix decrease. -/
lemma antitone_det_ratio (hT : IsToeplitz K) (hK : ∀ k, (leadingSection K k).PosDef) :
    Antitone fun k => (leadingSection K (k + 1)).det / (leadingSection K k).det :=
  antitone_nat_of_succ_le fun k => det_ratio_succ_le hT (hK (k + 2)) le_rfl

/-- `|Kₖ| ≤ |Kₘ| rₘ^{k-m}` for `m ≤ k`, where `rₘ = |Kₘ₊₁|/|Kₘ|`. -/
lemma det_le_mul_ratio_pow (hT : IsToeplitz K) (hK : ∀ k, (leadingSection K k).PosDef) {m k : ℕ}
    (hmk : m ≤ k) :
    (leadingSection K k).det ≤ (leadingSection K m).det *
      ((leadingSection K (m + 1)).det / (leadingSection K m).det) ^ (k - m) := by
  have hpos : ∀ j, 0 < (leadingSection K j).det := fun j => (hK j).det_pos
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    have hr := antitone_det_ratio hT hK hmk
    have e : (leadingSection K (k + 1)).det =
        (leadingSection K k).det * ((leadingSection K (k + 1)).det / (leadingSection K k).det) :=
      (mul_div_cancel₀ _ (hpos k).ne').symm
    rw [e, Nat.succ_sub hmk, pow_succ, ← mul_assoc]
    exact mul_le_mul ih hr (div_pos (hpos _) (hpos _)).le
      (mul_pos (hpos m) (pow_pos (div_pos (hpos _) (hpos _)) _)).le

/-- **Theorem 17.9.6, (17.128), (17.134)–(17.135).** For an infinite Toeplitz matrix whose leading
sections are positive definite, the ratios `|Kₙ|/|Kₙ₋₁|` and the roots `|Kₙ|^{1/n}` have the same
limit. -/
theorem tendsto_det_rpow_and_ratio (hT : IsToeplitz K) (hK : ∀ k, (leadingSection K k).PosDef) :
    ∃ L, Tendsto (fun k => (leadingSection K (k + 1)).det / (leadingSection K k).det) atTop (𝓝 L) ∧
      Tendsto (fun k => (leadingSection K k).det ^ (1 / (k : ℝ))) atTop (𝓝 L) := by
  set r : ℕ → ℝ := fun k => (leadingSection K (k + 1)).det / (leadingSection K k).det
  set D : ℕ → ℝ := fun k => (leadingSection K k).det
  have hpos : ∀ j, 0 < D j := fun j => (hK j).det_pos
  have hrpos : ∀ j, 0 < r j := fun j => div_pos (hpos _) (hpos _)
  have hanti : Antitone r := antitone_det_ratio hT hK
  have hbdd : BddBelow (Set.range r) := ⟨0, by rintro _ ⟨j, rfl⟩; exact (hrpos j).le⟩
  set L := ⨅ j, r j
  have hr : Tendsto r atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  have hL : 0 ≤ L := le_ciInf fun j => (hrpos j).le
  have hLr : ∀ j, L ≤ r j := fun j => ciInf_le hbdd j
  refine ⟨L, hr, tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩⟩
  · -- `|Kₖ| ≥ L^k`, so `|Kₖ|^{1/k} ≥ L > a`.
    have hDL : ∀ k, L ^ k ≤ D k := by
      intro k
      induction k with
      | zero => simp [D, leadingSection]
      | succ k ih =>
        have e : D (k + 1) = D k * r k := (mul_div_cancel₀ _ (hpos k).ne').symm
        rw [e, pow_succ]
        exact mul_le_mul ih (hLr k) hL (hpos k).le
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (k : ℝ) ≠ 0 := by positivity
    calc a < L := ha
      _ = (L ^ k) ^ (1 / (k : ℝ)) := by
          rw [one_div, pow_rpow_inv_natCast hL (by omega)]
      _ ≤ D k ^ (1 / (k : ℝ)) := rpow_le_rpow (pow_nonneg hL k) (hDL k) (by positivity)
  · -- For `rₘ < b' < b`, `|Kₖ|^{1/k} ≤ c^{1/k} rₘ` with `c = |Kₘ|/rₘ^m`, and `c^{1/k} → 1`.
    set b' := (L + b) / 2
    have hb' : L < b' := by simp only [b']; linarith
    have hb'b : b' < b := by simp only [b']; linarith
    have hb'0 : 0 < b' := by linarith
    obtain ⟨m, hm⟩ := (hr.eventually (gt_mem_nhds hb')).exists
    set c := D m / r m ^ m
    have hc : 0 < c := div_pos (hpos m) (pow_pos (hrpos m) m)
    have hc1 : Tendsto (fun k : ℕ => c ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
      have := tendsto_const_nhds (x := c).rpow tendsto_one_div_atTop_nhds_zero_nat
        (Or.inl hc.ne')
      simpa using this
    have hlt : 1 < b / b' := (one_lt_div hb'0).2 hb'b
    filter_upwards [hc1.eventually (gt_mem_nhds hlt), eventually_ge_atTop (max m 1)] with k hk hkm
    have hmk : m ≤ k := le_of_max_le_left hkm
    have hk1 : 1 ≤ k := le_of_max_le_right hkm
    have hbound : D k ≤ c * r m ^ k := by
      have h := det_le_mul_ratio_pow hT hK hmk
      calc D k ≤ D m * r m ^ (k - m) := h
        _ = c * r m ^ k := by
            have e : r m ^ k = r m ^ m * r m ^ (k - m) := by
              rw [← pow_add, Nat.add_sub_cancel' hmk]
            rw [e, ← mul_assoc, div_mul_cancel₀ _ (pow_pos (hrpos m) m).ne']
    calc D k ^ (1 / (k : ℝ)) ≤ (c * r m ^ k) ^ (1 / (k : ℝ)) :=
          rpow_le_rpow (hpos k).le hbound (by positivity)
      _ = c ^ (1 / (k : ℝ)) * r m := by
          rw [mul_rpow hc.le (pow_nonneg (hrpos m).le k), one_div,
            pow_rpow_inv_natCast (hrpos m).le (by omega)]
      _ < b / b' * b' := mul_lt_mul hk hm.le (hrpos m) (by positivity)
      _ = b := div_mul_cancel₀ _ hb'0.ne'

end InfoTheory
