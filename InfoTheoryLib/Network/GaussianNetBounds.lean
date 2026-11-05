/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.VectorCode
public import InfoTheoryLib.Network.Gaussian

/-!
# Gaussian networks: the bounds

The closed forms of Lecture 20 of El Gamal and Kim: the relaxation of the cutset bound, the gap to
the noisy network coding bound, the determinant of the interference example, and the bounds for the
`N`-relay network.

## Main statements

* `posSemidef_trace_smul_sub`: `K ≼ tr(K) I`.
* `gvRate_le_of_trace_le`, `gvRate_scale_le`, `cutset_relax`: **the relaxation of page 20-5**.
* `nnc_gap_le`: the gap of page 20-7.
* `det_interference`, `gvRate_interference`: the determinant of page 20-12.
* `det_rankOne`: the rank one matrix of page 20-16.
* `relay_upper_le`, `relay_interference_le`, `relay_multihop_ge`: the bounds of pages 20-15 and
  20-17.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 20
-/

open Real Finset Matrix

@[expose] public noncomputable section

namespace InfoTheory

section Relax

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]

/-- `K ≼ tr(K) I` for a positive semidefinite matrix `K`. -/
lemma posSemidef_trace_smul_sub {K : Matrix t t ℝ} (hK : K.PosSemidef) :
    (K.trace • (1 : Matrix t t ℝ) - K).PosSemidef := by
  set U := eigvecs hK.1 with hU
  have hUU' : U * Uᵀ = 1 := eigvecs_mul_transpose hK.1
  have hspec : K = U * diagonal hK.1.eigenvalues * Uᵀ := eq_eigvecs hK.1
  have hsum : K.trace = ∑ i, hK.1.eigenvalues i := by
    simpa using hK.1.trace_eq_sum_eigenvalues
  have e : K.trace • (1 : Matrix t t ℝ) - K =
      U * diagonal (fun i => K.trace - hK.1.eigenvalues i) * Uᵀ := by
    have h₁ : diagonal (fun i => K.trace - hK.1.eigenvalues i) =
        K.trace • (1 : Matrix t t ℝ) - diagonal hK.1.eigenvalues := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [h₁, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU',
      ← hspec]
  rw [e]
  refine posSemidef_mul_mul_transpose (posSemidef_diagonal_iff.mpr fun i => ?_) U
  rw [hsum]
  have := single_le_sum (f := hK.1.eigenvalues) (fun j _ => hK.eigenvalues_nonneg j) (mem_univ i)
  simpa using this

omit [DecidableEq t] in
/-- The rate of the Gaussian vector channel is monotone in the covariance. -/
lemma gvRate_mono (G : Matrix r t ℝ) {K L : Matrix t t ℝ} (hK : K.PosSemidef)
    (hKL : (L - K).PosSemidef) : gvRate G K ≤ gvRate G L := by
  have h₁ := posDef_add_one (posSemidef_mul_mul_transpose hK G)
  have e : G * L * Gᵀ + 1 - (G * K * Gᵀ + 1) = G * (L - K) * Gᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have h₂ : (G * K * Gᵀ + 1).det ≤ (G * L * Gᵀ + 1).det :=
    det_le_det_of_posSemidef_sub h₁.posSemidef (e ▸ posSemidef_mul_mul_transpose hKL G)
  simp only [gvRate]
  exact mul_le_mul_of_nonneg_left (log_le_log h₁.det_pos h₂) (by norm_num)

/-- **Page 20-5 of [elgamal2010], step (a).** If `tr(K) ≤ T` then
`½ log |I + G K Gᵀ| ≤ ½ log |I + T G Gᵀ|`. -/
theorem gvRate_le_of_trace_le (G : Matrix r t ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) {T : ℝ}
    (hT : K.trace ≤ T) : gvRate G K ≤ gvRate G (T • 1) := by
  refine gvRate_mono G hK ?_
  have e : T • (1 : Matrix t t ℝ) - K =
      (T - K.trace) • (1 : Matrix t t ℝ) + (K.trace • (1 : Matrix t t ℝ) - K) := by
    rw [sub_smul]
    abel
  rw [e]
  exact (PosSemidef.one.smul (sub_nonneg.mpr hT)).add (posSemidef_trace_smul_sub hK)

/-- **Page 20-5 of [elgamal2010].** For `s ≥ 1`,
`½ log |I + s T G Gᵀ| ≤ ½ log |I + T G Gᵀ| + (|r| / 2) log s`, where `r` indexes the outputs. -/
theorem gvRate_scale_le (G : Matrix r t ℝ) {T s : ℝ} (hT : 0 ≤ T) (hs : 1 ≤ s) :
    gvRate G ((s * T) • 1) ≤ gvRate G (T • 1) + (Fintype.card r : ℝ) / 2 * log s := by
  have hs0 : 0 < s := by linarith
  have hA : (G * (T • (1 : Matrix t t ℝ)) * Gᵀ).PosSemidef :=
    posSemidef_mul_mul_transpose (PosSemidef.one.smul hT) G
  have hB := posDef_add_one hA
  set B := G * (T • (1 : Matrix t t ℝ)) * Gᵀ + 1 with hBd
  have hC := posDef_add_one (posSemidef_mul_mul_transpose
    (PosSemidef.one.smul (mul_nonneg hs0.le hT)) G (r := r) (t := t))
  have e₁ : G * ((s * T) • (1 : Matrix t t ℝ)) * Gᵀ = s • (G * (T • (1 : Matrix t t ℝ)) * Gᵀ) := by
    rw [mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have e₂ : s • B - (G * ((s * T) • (1 : Matrix t t ℝ)) * Gᵀ + 1) = (s - 1) • (1 : Matrix r r ℝ) :=
    by
    rw [hBd, e₁, smul_add, sub_smul]
    simp only [one_smul]
    abel
  have hdet : (G * ((s * T) • (1 : Matrix t t ℝ)) * Gᵀ + 1).det ≤ (s • B).det :=
    det_le_det_of_posSemidef_sub hC.posSemidef
      (e₂ ▸ PosSemidef.one.smul (sub_nonneg.mpr hs))
  rw [det_smul] at hdet
  have hlog := log_le_log hC.det_pos hdet
  rw [log_mul (by positivity) hB.det_pos.ne', log_pow] at hlog
  simp only [gvRate]
  rw [← hBd]
  linarith

/-- **Page 20-5 of [elgamal2010]: the relaxation of the cutset bound.** Here `t` indexes the nodes
of the cut and `r` the other nodes. If `tr(K) ≤ |t| P`, then
`½ log |I + G K Gᵀ| ≤ ½ log |I + (P / 2) G Gᵀ| + (|r| / 2) log (2 |t|)`. -/
theorem cutset_relax [Nonempty t] (G : Matrix r t ℝ) {K : Matrix t t ℝ} (hK : K.PosSemidef) {P : ℝ}
    (hP : 0 ≤ P) (hT : K.trace ≤ Fintype.card t * P) :
    gvRate G K ≤ gvRate G ((P / 2) • 1) +
      (Fintype.card r : ℝ) / 2 * log (2 * Fintype.card t) := by
  have hc : (1 : ℝ) ≤ Fintype.card t := by exact_mod_cast Fintype.card_pos
  have h₁ := gvRate_le_of_trace_le G hK hT
  have h₂ := gvRate_scale_le (r := r) G (T := P / 2) (s := 2 * Fintype.card t) (by positivity)
    (by linarith)
  have e : (2 * (Fintype.card t : ℝ) * (P / 2)) = Fintype.card t * P := by ring
  rw [e] at h₂
  exact h₁.trans h₂

/-- **Page 20-7 of [elgamal2010]: the gap.** In nats,
`|S| (log 2) / 2 + (|Sᶜ| / 2) log (2 |S|) ≤ (N / 2) log (4 N)`, for `|S| + |Sᶜ| = N` and
`|S| ≥ 1`. -/
theorem nnc_gap_le {a b N : ℕ} (ha : 1 ≤ a) (hab : a + b = N) :
    (a : ℝ) * (log 2 / 2) + (b : ℝ) / 2 * log (2 * a) ≤ (N : ℝ) / 2 * log (4 * N) := by
  have hN : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have haN : (a : ℝ) ≤ N := by
    have : a ≤ N := by omega
    exact_mod_cast this
  have h₁ : log 2 ≤ log (4 * N) := log_le_log (by norm_num) (by linarith)
  have h₂ : log (2 * a) ≤ log (4 * N) := log_le_log (by linarith) (by linarith)
  have hsum : (a : ℝ) + b = N := by exact_mod_cast hab
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have h₃ := mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ (a : ℝ) / 2)
  have h₄ := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ (b : ℝ) / 2)
  rw [← hsum]
  have e₁ : (a : ℝ) * (log 2 / 2) = (a : ℝ) / 2 * log 2 := by ring
  rw [e₁]
  have e₂ : ((a : ℝ) + b) / 2 * log (4 * ((a : ℝ) + b)) =
      (a : ℝ) / 2 * log (4 * ((a : ℝ) + b)) + (b : ℝ) / 2 * log (4 * ((a : ℝ) + b)) := by ring
  rw [e₂, hsum]
  linarith

/-- **Page 20-6 of [elgamal2010]: the rate of Theorem 1**, in nats:
`½ log |I + (P / 2) G Gᵀ| - |S| (log 2) / 2`, for `t` the nodes of the cut. -/
def nncGaussRate (G : Matrix r t ℝ) (P : ℝ) : ℝ :=
  gvRate G ((P / 2) • 1) - (Fintype.card t : ℝ) * (log 2 / 2)

/-- **Page 20-7 of [elgamal2010].** The cutset bound exceeds the rate of Theorem 1 by at most
`(N / 2) log (4 N)`. -/
theorem gvRate_le_nncGaussRate_add [Nonempty t] (G : Matrix r t ℝ) {K : Matrix t t ℝ}
    (hK : K.PosSemidef) {P : ℝ} (hP : 0 ≤ P) (hT : K.trace ≤ Fintype.card t * P) {N : ℕ}
    (hN : Fintype.card t + Fintype.card r = N) :
    gvRate G K ≤ nncGaussRate G P + (N : ℝ) / 2 * log (4 * N) := by
  have h₁ := cutset_relax G hK hP hT
  have h₂ := nnc_gap_le (a := Fintype.card t) (b := Fintype.card r) Fintype.card_pos hN
  simp only [nncGaussRate]
  linarith

end Relax

/-! ### The interference example -/

section Interference

variable {N : ℕ}

/-- **Page 20-11 of [elgamal2010].** The gain matrix with `1` on the diagonal and `a` elsewhere. -/
def icGain (N : ℕ) (a : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => if i = j then 1 else a

/-- The matrix with all the entries equal to `1`. -/
def allOnes (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun _ _ => 1

lemma icGain_eq (a : ℝ) : icGain N a = (1 - a) • (1 : Matrix (Fin N) (Fin N) ℝ) + a • allOnes N :=
  by
  ext i j
  by_cases h : i = j
  · subst h
    simp [icGain, allOnes]
  · simp [icGain, allOnes, h]

lemma allOnes_mul_allOnes : allOnes N * allOnes N = (N : ℝ) • allOnes N := by
  ext i j
  simp [allOnes, Matrix.mul_apply]

lemma allOnes_transpose : (allOnes N)ᵀ = allOnes N := by
  ext i j
  simp [allOnes]

/-- `det (α I + β J) = α ^ (N - 1) (α + N β)`. -/
lemma det_smul_one_add_allOnes (hN : 0 < N) {α : ℝ} (hα : α ≠ 0) (β : ℝ) :
    (α • (1 : Matrix (Fin N) (Fin N) ℝ) + β • allOnes N).det = α ^ (N - 1) * (α + N * β) := by
  have e : α • (1 : Matrix (Fin N) (Fin N) ℝ) + β • allOnes N =
      α • (1 + replicateCol Unit (fun _ : Fin N => β / α) *
        replicateRow Unit (fun _ : Fin N => (1 : ℝ))) := by
    ext i j
    by_cases h : i = j
    · simp [allOnes, Matrix.mul_apply, h]
      field_simp
    · simp [allOnes, Matrix.mul_apply, h]
      field_simp
  rw [e, det_smul, det_one_add_replicateCol_mul_replicateRow]
  simp only [Fintype.card_fin]
  have h₁ : (fun _ : Fin N => (1 : ℝ)) ⬝ᵥ (fun _ : Fin N => β / α) = N * (β / α) := by
    simp [dotProduct]
  rw [h₁]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_succ]
  field_simp

/-- **Page 20-12 of [elgamal2010].**
`|I + G Gᵀ P| = (1 + (a - 1)² P) ^ (N - 1) (1 + (a (N - 1) + 1)² P)`. -/
theorem det_interference (hN : 0 < N) (a : ℝ) {P : ℝ} (hP : 0 ≤ P) :
    (icGain N a * (P • (1 : Matrix (Fin N) (Fin N) ℝ)) * (icGain N a)ᵀ + 1).det =
      (1 + (a - 1) ^ 2 * P) ^ (N - 1) * (1 + (a * ((N : ℝ) - 1) + 1) ^ 2 * P) := by
  set α := 1 + (a - 1) ^ 2 * P with hα
  have hα0 : α ≠ 0 := by
    have : 0 ≤ (a - 1) ^ 2 * P := by positivity
    rw [hα]
    linarith
  set β := P * (2 * a * (1 - a) + a ^ 2 * N) with hβ
  have hT : (icGain N a)ᵀ = icGain N a := by
    rw [icGain_eq, transpose_add, transpose_smul, transpose_smul, transpose_one, allOnes_transpose]
  have e : icGain N a * (P • (1 : Matrix (Fin N) (Fin N) ℝ)) * (icGain N a)ᵀ + 1 =
      α • (1 : Matrix (Fin N) (Fin N) ℝ) + β • allOnes N := by
    rw [hT, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, icGain_eq, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      allOnes_mul_allOnes, smul_add, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hα, hβ]
    ring
  rw [e, det_smul_one_add_allOnes hN hα0]
  congr 1
  rw [hα, hβ]
  ring

/-- **Page 20-13 of [elgamal2010].** The cutset bound for the interference example:
`(1 / 2N) log |I + G Gᵀ P| = ((N - 1) / N) C((a - 1)² P) + (1 / N) C((a (N - 1) + 1)² P)`. -/
theorem gvRate_interference (hN : 0 < N) (a : ℝ) {P : ℝ} (hP : 0 ≤ P) :
    gvRate (icGain N a) (P • 1) / N =
      ((N : ℝ) - 1) / N * gaussCap ((a - 1) ^ 2 * P) +
        1 / N * gaussCap ((a * ((N : ℝ) - 1) + 1) ^ 2 * P) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h₁ : (0 : ℝ) < 1 + (a - 1) ^ 2 * P := by positivity
  have h₂ : (0 : ℝ) < 1 + (a * ((N : ℝ) - 1) + 1) ^ 2 * P := by positivity
  rw [gvRate, det_interference hN a hP, log_mul (by positivity) h₂.ne', log_pow]
  simp only [gaussCap]
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hc]
  field_simp

end Interference

/-! ### The `N`-relay network -/

section Relay

variable {ν : ℝ}

/-- **Page 20-16 of [elgamal2010].** `|I + a aᵀ P| = 1 + P ∑ⱼ aⱼ²`: the matrix `a aᵀ` has rank one,
with the eigenvalue `∑ⱼ aⱼ²`. -/
theorem gvRate_rankOne {r : Type*} [Fintype r] [DecidableEq r] (a : r → ℝ) (P : ℝ) :
    gvRate (replicateCol Unit a) (P • 1) = gaussCap ((∑ j, a j ^ 2) * P) := by
  have e : replicateCol Unit a * (P • (1 : Matrix Unit Unit ℝ)) * (replicateCol Unit a)ᵀ + 1 =
      1 + replicateCol Unit (fun j => P * a j) * replicateRow Unit a := by
    rw [add_comm]
    congr 1
    ext i j
    simp [Matrix.mul_apply, mul_comm, mul_left_comm]
  simp only [gvRate, gaussCap]
  rw [e, det_one_add_replicateCol_mul_replicateRow]
  congr 2
  simp only [dotProduct]
  rw [sum_mul, add_right_inj]
  exact sum_congr rfl fun j _ => by ring

/-- The sum `∑_{j ≥ 1} 1 / j ^ ν`. -/
def zetaSum (ν : ℝ) : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ ν

lemma summable_zetaTerm (hν : 1 < ν) : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ ν := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hν)
  simpa using h

lemma zetaTerm_nonneg (m : ℕ) : 0 ≤ 1 / ((m : ℝ) + 1) ^ ν := by positivity

lemma zetaSum_nonneg : 0 ≤ zetaSum ν := tsum_nonneg zetaTerm_nonneg

/-- **Page 20-17 of [elgamal2010].** The broadcast bound of the `N`-relay network is at most a
constant, for `ν > 1`: `C((∑_{j=1}^{N+1} 1 / j^ν) P) ≤ C(ζ(ν) P)`. -/
theorem relay_upper_le (hν : 1 < ν) (N : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    gvRate (replicateCol Unit fun j : Fin (N + 1) => ((j : ℝ) + 1) ^ (-(ν / 2))) (P • 1) ≤
      gaussCap (zetaSum ν * P) := by
  rw [gvRate_rankOne]
  have hsum : ∑ j : Fin (N + 1), (((j : ℝ) + 1) ^ (-(ν / 2))) ^ 2 =
      ∑ m ∈ range (N + 1), 1 / ((m : ℝ) + 1) ^ ν := by
    rw [← Fin.sum_univ_eq_sum_range fun m : ℕ => 1 / ((m : ℝ) + 1) ^ ν]
    refine sum_congr rfl fun j _ => ?_
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [← rpow_natCast, ← rpow_mul hj.le, one_div, ← rpow_neg hj.le]
    congr 1
    push_cast
    ring
  have hle : ∑ j : Fin (N + 1), (((j : ℝ) + 1) ^ (-(ν / 2))) ^ 2 ≤ zetaSum ν := by
    rw [hsum]
    exact (summable_zetaTerm hν).sum_le_tsum _ fun m _ => zetaTerm_nonneg m
  simp only [gaussCap]
  refine mul_le_mul_of_nonneg_left (log_le_log ?_ ?_) (by norm_num)
  · have : 0 ≤ (∑ j : Fin (N + 1), (((j : ℝ) + 1) ^ (-(ν / 2))) ^ 2) * P := by positivity
    linarith
  · have := mul_le_mul_of_nonneg_right hle hP
    linarith

/-- **Page 20-15 of [elgamal2010].** The interference at the receiver `j` of the multi-hop scheme,
over the transmitters `k ∈ [0 : N]`, `k ≠ j - 1, j`. -/
def relayInterference (N j : ℕ) (ν P : ℝ) : ℝ :=
  ∑ k ∈ (range (N + 1)).filter (fun k => k + 1 ≠ j ∧ k ≠ j), P / (|(k : ℝ) - j|) ^ ν

/-- **Page 20-15 of [elgamal2010].** The interference is bounded: `I_j ≤ 2 ζ(ν) P`, for `ν > 1`. -/
theorem relayInterference_le (hν : 1 < ν) (N j : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    relayInterference N j ν P ≤ 2 * zetaSum ν * P := by
  classical
  have hsum := summable_zetaTerm hν
  set A := (range (N + 1)).filter (fun k => k + 1 ≠ j ∧ k ≠ j) with hA
  -- the transmitters after and before the receiver
  have hval₁ : ∀ k, j < k → P / (|(k : ℝ) - j|) ^ ν = P * (1 / (((k - j - 1 : ℕ) : ℝ) + 1) ^ ν) :=
    by
    intro k hk
    have h₁ : (((k - j - 1 : ℕ) : ℝ) + 1) = (k : ℝ) - j := by
      have : k - j - 1 + 1 = k - j := by omega
      have h₂ : ((k - j - 1 + 1 : ℕ) : ℝ) = ((k - j : ℕ) : ℝ) := by rw [this]
      push_cast at h₂
      rw [h₂, Nat.cast_sub hk.le]
    have hnn : (0 : ℝ) ≤ (k : ℝ) - j := by
      have : (j : ℝ) ≤ k := by exact_mod_cast hk.le
      linarith
    rw [h₁, abs_of_nonneg hnn, mul_one_div]
  have hval₂ : ∀ k, k < j → P / (|(k : ℝ) - j|) ^ ν = P * (1 / (((j - k - 1 : ℕ) : ℝ) + 1) ^ ν) :=
    by
    intro k hk
    have h₁ : (((j - k - 1 : ℕ) : ℝ) + 1) = (j : ℝ) - k := by
      have : j - k - 1 + 1 = j - k := by omega
      have h₂ : ((j - k - 1 + 1 : ℕ) : ℝ) = ((j - k : ℕ) : ℝ) := by rw [this]
      push_cast at h₂
      rw [h₂, Nat.cast_sub hk.le]
    have hnn : (k : ℝ) - j ≤ 0 := by
      have : (k : ℝ) ≤ j := by exact_mod_cast hk.le
      linarith
    rw [h₁, abs_of_nonpos hnn, neg_sub, mul_one_div]
  have hbound : ∀ (B : Finset ℕ) (φ : ℕ → ℕ), Set.InjOn φ B →
      ∑ k ∈ B, 1 / (((φ k : ℕ) : ℝ) + 1) ^ ν ≤ zetaSum ν := by
    intro B φ hφ
    have e := sum_image (f := fun m : ℕ => 1 / ((m : ℝ) + 1) ^ ν) (s := B) (g := φ) hφ
    rw [← e]
    exact hsum.sum_le_tsum _ fun m _ => zetaTerm_nonneg m
  have hsplit : relayInterference N j ν P ≤
      ∑ k ∈ A.filter (fun k => j < k), P / (|(k : ℝ) - j|) ^ ν +
        ∑ k ∈ A.filter (fun k => ¬ j < k), P / (|(k : ℝ) - j|) ^ ν :=
    le_of_eq (sum_filter_add_sum_filter_not A _ _).symm
  have h₁ : ∑ k ∈ A.filter (fun k => j < k), P / (|(k : ℝ) - j|) ^ ν ≤ P * zetaSum ν := by
    rw [sum_congr rfl fun k hk => hval₁ k (mem_filter.mp hk).2, ← mul_sum]
    refine mul_le_mul_of_nonneg_left (hbound _ (fun k => k - j - 1) fun a ha b hb hab => ?_) hP
    have h₃ := (mem_filter.mp (mem_coe.mp ha)).2
    have h₄ := (mem_filter.mp (mem_coe.mp hb)).2
    simp only at hab
    omega
  have h₂ : ∑ k ∈ A.filter (fun k => ¬ j < k), P / (|(k : ℝ) - j|) ^ ν ≤ P * zetaSum ν := by
    have hlt : ∀ k ∈ A.filter (fun k => ¬ j < k), k < j := fun k hk => by
      have h₃ := (mem_filter.mp hk).2
      have h₄ := (mem_filter.mp (mem_filter.mp hk).1).2.2
      omega
    rw [sum_congr rfl fun k hk => hval₂ k (hlt k hk), ← mul_sum]
    refine mul_le_mul_of_nonneg_left (hbound _ (fun k => j - k - 1) fun a ha b hb hab => ?_) hP
    have h₃ := hlt a (mem_coe.mp ha)
    have h₄ := hlt b (mem_coe.mp hb)
    simp only at hab
    omega
  have e : 2 * zetaSum ν * P = P * zetaSum ν + P * zetaSum ν := by ring
  rw [e]
  linarith

/-- **Page 20-15 of [elgamal2010].** The rate of the multi-hop scheme is bounded below by a
constant: `min_j C(P / (I_j + 1)) ≥ C(P / (2 ζ(ν) P + 1))`, whatever the number of relays. -/
theorem relay_multihop_ge (hν : 1 < ν) (N j : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    gaussCap (P / (2 * zetaSum ν * P + 1)) ≤ gaussCap (P / (relayInterference N j ν P + 1)) := by
  have hI : 0 ≤ relayInterference N j ν P := sum_nonneg fun k _ => by positivity
  have hz := zetaSum_nonneg (ν := ν)
  have hle := relayInterference_le hν N j hP
  simp only [gaussCap]
  refine mul_le_mul_of_nonneg_left (log_le_log (by positivity) ?_) (by norm_num)
  have : P / (2 * zetaSum ν * P + 1) ≤ P / (relayInterference N j ν P + 1) :=
    div_le_div_of_nonneg_left hP (by positivity) (by linarith)
  linarith

/-- **Page 20-15 of [elgamal2010].** Without relaying the rate `C(P / N ^ ν)` tends to `0`. -/
theorem tendsto_relay_direct (hν : 0 < ν) (P : ℝ) :
    Filter.Tendsto (fun N : ℕ => gaussCap (P / (N : ℝ) ^ ν)) Filter.atTop (nhds 0) := by
  have h₁ : Filter.Tendsto (fun N : ℕ => P / (N : ℝ) ^ ν) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      ((tendsto_rpow_atTop hν).comp tendsto_natCast_atTop_atTop)
  have h₂ : Filter.Tendsto (fun x : ℝ => 1 / 2 * log (1 + x)) (nhds 0) (nhds (1 / 2 * log (1 + 0)))
    :=
    ((continuousAt_const.add continuousAt_id).log (by norm_num)).const_mul _
  simp only [add_zero, log_one, mul_zero] at h₂
  exact h₂.comp h₁

end Relay

end InfoTheory
