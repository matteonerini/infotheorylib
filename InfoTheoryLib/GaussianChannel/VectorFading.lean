/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Vector

/-!
# The Gaussian vector fading channel: the formulas

With the gain matrix `G` known at the decoder and a covariance matrix `K` at the encoder, the rate
is
`E[½ log |I + G K Gᵀ|]`. This file studies its maximum for finitely many fading states. If the law
of
`G` does not change under sign flips and permutations of the transmit antennas, the maximum is
attained
by `K* = (P/t) I`. The operational meaning of the rate is not formalized.

## Main definitions

* `gvFadingRate q G K`: the rate `E[½ log |I + G K Gᵀ|]`.
* `gvFadingCapacity q G P`: its supremum under `tr K ≤ P`.
* `IsIsotropicFading q G`: the invariance of the law of `G`.

## Main statements

* `gvFadingCapacity_eq`: **Theorem 2 of Lecture 10**, `C = E[½ log |I + (P/t) G Gᵀ|]`.
* `gvRate_isotropic_eq_sum`: the form with the eigenvalues of `G Gᵀ`.
* `tendsto_gvFadingRate_div`: the low SNR behaviour.
* `tendsto_gvFadingRate_sub_log`: the high SNR behaviour.

## Implementation notes

A finitely supported law cannot be invariant under all orthogonal matrices unless `G = 0`. We ask
for
the invariance under the flips of a sign and the transpositions of two columns only, which every
orthogonally invariant law has. The proof does not average over a group: the invariance makes the
matrix `E[Gᵀ (I + (P/t) G Gᵀ)⁻¹ G]` a multiple of the identity, which is the KKT condition for
`K* = (P/t) I`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 10
-/

open Real Finset Matrix Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {σ r t : Type*} [Fintype σ] [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]

/-- **Lecture 10 of [elgamal2010], page 10-14.** The rate `E[½ log |I + G K Gᵀ|]` of the input
covariance matrix `K`, for a gain matrix `G` with the law `q` on finitely many states, in nats. -/
def gvFadingRate (q : σ → ℝ) (G : σ → Matrix r t ℝ) (K : Matrix t t ℝ) : ℝ :=
  ∑ s, q s * gvRate (G s) K

/-- **Lecture 10 of [elgamal2010], page 10-14.** The formula
`max_{K ≽ 0, tr K ≤ P} E[½ log |I + G K Gᵀ|]`. -/
def gvFadingCapacity (q : σ → ℝ) (G : σ → Matrix r t ℝ) (P : ℝ) : ℝ :=
  sSup {v | ∃ K : Matrix t t ℝ, K.PosSemidef ∧ K.trace ≤ P ∧ gvFadingRate q G K = v}

/-- The matrix that flips the sign of the transmit antenna `i`. -/
def flipMatrix (i : t) : Matrix t t ℝ := diagonal fun k => if k = i then -1 else 1

/-- The gain matrix with the sign of the transmit antenna `i` flipped. -/
def flipColumn (G : Matrix r t ℝ) (i : t) : Matrix r t ℝ :=
  Matrix.of fun a b => G a b * if b = i then -1 else 1

omit [Fintype r] [DecidableEq r] in
lemma flipColumn_eq (G : Matrix r t ℝ) (i : t) : flipColumn G i = G * flipMatrix i := by
  ext a b
  rw [flipMatrix, Matrix.mul_diagonal]
  rfl

/-- **Lecture 10 of [elgamal2010], page 10-14.** The law of the gain matrix is invariant under flips
of the sign and transpositions of the transmit antennas. This holds if the law of `G` is invariant
under orthogonal transformations, the isotropy of the notes. -/
def IsIsotropicFading (q : σ → ℝ) (G : σ → Matrix r t ℝ) : Prop :=
  ∀ f : Matrix r t ℝ → ℝ, (∀ i, ∑ s, q s * f (flipColumn (G s) i) = ∑ s, q s * f (G s)) ∧
    ∀ i j, ∑ s, q s * f ((G s).submatrix id (Equiv.swap i j)) = ∑ s, q s * f (G s)

/-- The matrix `Gᵀ (x G Gᵀ + I)⁻¹ G`. -/
def isoKernel (x : ℝ) (G : Matrix r t ℝ) : Matrix t t ℝ := Gᵀ * (x • (G * Gᵀ) + 1)⁻¹ * G

omit [DecidableEq t] in
private lemma flipMatrix_mul_self [DecidableEq t] (i : t) :
    flipMatrix i * flipMatrix i = (1 : Matrix t t ℝ) := by
  rw [flipMatrix, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  split_ifs <;> norm_num

private lemma isoKernel_flip (x : ℝ) (G : Matrix r t ℝ) (i a b : t) :
    isoKernel x (flipColumn G i) a b =
      (if a = i then -1 else 1) * isoKernel x G a b * (if b = i then -1 else 1) := by
  rw [flipColumn_eq]
  have h1 : (G * flipMatrix i) * (G * flipMatrix i)ᵀ = G * Gᵀ := by
    have ht : (flipMatrix i)ᵀ = (flipMatrix i : Matrix t t ℝ) := diagonal_transpose _
    rw [transpose_mul, ht]
    calc G * flipMatrix i * (flipMatrix i * Gᵀ) = G * (flipMatrix i * flipMatrix i) * Gᵀ := by
          simp only [Matrix.mul_assoc]
      _ = G * Gᵀ := by rw [flipMatrix_mul_self, Matrix.mul_one]
  have h2 : isoKernel x (G * flipMatrix i) = flipMatrix i * isoKernel x G * flipMatrix i := by
    have ht : (flipMatrix i)ᵀ = (flipMatrix i : Matrix t t ℝ) := diagonal_transpose _
    rw [isoKernel, h1, transpose_mul, ht, isoKernel]
    simp only [Matrix.mul_assoc]
  rw [h2, flipMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]

omit [DecidableEq t] in
private lemma isoKernel_swap (x : ℝ) (G : Matrix r t ℝ) (e : t ≃ t) (a b : t) :
    isoKernel x (G.submatrix id e) a b = isoKernel x G (e a) (e b) := by
  have h1 : G.submatrix id e * (G.submatrix id e)ᵀ = G * Gᵀ := by
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_id_id]
  simp only [isoKernel, h1]
  rw [transpose_submatrix]
  have h2 : Gᵀ.submatrix e id * (x • (G * Gᵀ) + 1)⁻¹ =
      (Gᵀ * (x • (G * Gᵀ) + 1)⁻¹).submatrix e id := by
    ext p q
    simp [Matrix.mul_apply]
  rw [h2, ← submatrix_mul _ _ e id e Function.bijective_id]
  rfl

/-- **Lecture 10, page 10-14.** For an isotropic law, the matrix `E[Gᵀ (x G Gᵀ + I)⁻¹ G]` is a
multiple
of the identity. -/
theorem exists_sum_isoKernel_eq {q : σ → ℝ} {G : σ → Matrix r t ℝ} (hiso : IsIsotropicFading q G)
    (x : ℝ) : ∃ c : t → ℝ, (∀ i j, c i = c j) ∧ ∑ s, q s • isoKernel x (G s) = diagonal c := by
  set M := ∑ s, q s • isoKernel x (G s) with hM
  have hent : ∀ a b, M a b = ∑ s, q s * isoKernel x (G s) a b := fun a b => by
    simp [hM, Matrix.sum_apply, Matrix.smul_apply]
  refine ⟨fun i => M i i, fun i j => ?_, ?_⟩
  · have h := (hiso fun H => isoKernel x H i i).2 i j
    beta_reduce at h
    simp only [isoKernel_swap, Equiv.swap_apply_left] at h
    change M i i = M j j
    rw [hent, hent]
    exact h.symm
  · ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [diagonal_apply_ne _ hab, hent]
      have h := (hiso fun H => isoKernel x H a b).1 a
      beta_reduce at h
      have e : ∀ s, q s * isoKernel x (flipColumn (G s) a) a b =
          - (q s * isoKernel x (G s) a b) := fun s => by
        rw [isoKernel_flip]
        simp [Ne.symm hab]
      rw [sum_congr rfl fun s _ => e s, sum_neg_distrib] at h
      linarith

/-- **Theorem 2 of Lecture 10, the bound.** For an isotropic law, `K* = (P/t) I` is the best input
covariance matrix. -/
theorem gvFadingRate_le_isotropic {q : σ → ℝ} (hq : ∀ s, 0 ≤ q s) {G : σ → Matrix r t ℝ}
    (hiso : IsIsotropicFading q G) {P : ℝ} (hP : 0 ≤ P) (ht : 0 < Fintype.card t)
    {K : Matrix t t ℝ} (hK : K.PosSemidef) (htr : K.trace ≤ P) :
    gvFadingRate q G K ≤ gvFadingRate q G ((P / Fintype.card t) • 1) := by
  have hn : (Fintype.card t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hn' : (0 : ℝ) < Fintype.card t := by exact_mod_cast ht
  set x := P / (Fintype.card t : ℝ) with hx
  have hx0 : 0 ≤ x := div_nonneg hP hn'.le
  set Ks : Matrix t t ℝ := x • 1 with hKs
  have hKsp : Ks.PosSemidef := PosSemidef.one.smul hx0
  have htrs : Ks.trace = P := by
    rw [hKs, trace_smul, trace_one, smul_eq_mul, hx, div_mul_cancel₀ _ hn]
  have hA : ∀ H : Matrix r t ℝ, H * Ks * Hᵀ + 1 = x • (H * Hᵀ) + 1 := fun H => by
    rw [hKs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  -- The tangent bound in each state.
  have hterm : ∀ s, gvRate (G s) K - gvRate (G s) Ks ≤
      1 / 2 * (isoKernel x (G s) * (K - Ks)).trace := fun s => by
    have hP1 := posDef_add_one (posSemidef_mul_mul_transpose hKsp (G s))
    have hP2 := posDef_add_one (posSemidef_mul_mul_transpose hK (G s))
    have e : G s * K * (G s)ᵀ + 1 = (G s * Ks * (G s)ᵀ + 1) + G s * (K - Ks) * (G s)ᵀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e] at hP2
    have h := log_det_add_sub_le hP1 hP2
    rw [← e, hA] at h
    have htrc : ((x • (G s * (G s)ᵀ) + 1)⁻¹ * (G s * (K - Ks) * (G s)ᵀ)).trace =
        (isoKernel x (G s) * (K - Ks)).trace := by
      rw [isoKernel, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [htrc] at h
    rw [gvRate, gvRate, hA]
    linarith
  obtain ⟨c, hc, hM⟩ := exists_sum_isoKernel_eq hiso x
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.1 ht
  have hcc : ∑ s, q s • isoKernel x (G s) = c i₀ • (1 : Matrix t t ℝ) := by
    rw [hM, ← diagonal_one, ← Matrix.diagonal_smul]
    congr 1
    funext k
    simp [hc k i₀]
  -- `c ≥ 0`.
  have hc0 : 0 ≤ c i₀ := by
    have h1 : (∑ s, q s • isoKernel x (G s)) i₀ i₀ = c i₀ := by
      rw [hM, diagonal_apply_eq]
    rw [← h1, Matrix.sum_apply]
    refine sum_nonneg fun s _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    refine mul_nonneg (hq s) ?_
    have hPD : (x • ((G s) * (G s)ᵀ) + 1).PosDef := by
      have := posDef_add_one (posSemidef_mul_mul_transpose hKsp (G s))
      rwa [hA] at this
    exact (posSemidef_transpose_mul_mul hPD.inv.posSemidef (G s)).diag_nonneg
  have hsum : ∑ s, q s * (1 / 2 * (isoKernel x (G s) * (K - Ks)).trace) =
      1 / 2 * (c i₀ * (K.trace - P)) := by
    have e1 : ∑ s, q s * (1 / 2 * (isoKernel x (G s) * (K - Ks)).trace) =
        1 / 2 * ((∑ s, q s • isoKernel x (G s)) * (K - Ks)).trace := by
      rw [Matrix.sum_mul, trace_sum, mul_sum]
      refine sum_congr rfl fun s _ => ?_
      rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
      ring
    rw [e1, hcc, Matrix.smul_mul, Matrix.one_mul, trace_smul, trace_sub, htrs, smul_eq_mul]
  have hfin : gvFadingRate q G K - gvFadingRate q G Ks ≤ 1 / 2 * (c i₀ * (K.trace - P)) := by
    rw [gvFadingRate, gvFadingRate, ← sum_sub_distrib, ← hsum]
    refine sum_le_sum fun s _ => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (hterm s) (hq s)
  have hneg : c i₀ * (K.trace - P) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
  linarith

/-- **Theorem 2 of Lecture 10 of [elgamal2010], page 10-14.** For an isotropic law of the gain
matrix,
`max_{K ≽ 0, tr K ≤ P} E[½ log |I + G K Gᵀ|] = E[½ log |I + (P/t) G Gᵀ|]`, attained by `(P/t) I`. -/
theorem gvFadingCapacity_eq {q : σ → ℝ} (hq : ∀ s, 0 ≤ q s) {G : σ → Matrix r t ℝ}
    (hiso : IsIsotropicFading q G) {P : ℝ} (hP : 0 ≤ P) (ht : 0 < Fintype.card t) :
    gvFadingCapacity q G P = gvFadingRate q G ((P / Fintype.card t) • 1) := by
  have hn : (Fintype.card t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hn' : (0 : ℝ) < Fintype.card t := by exact_mod_cast ht
  refine IsGreatest.csSup_eq ⟨⟨_, PosSemidef.one.smul (div_nonneg hP hn'.le), ?_, rfl⟩, ?_⟩
  · rw [trace_smul, trace_one, smul_eq_mul, div_mul_cancel₀ _ hn]
  · rintro _ ⟨K, hK, htr, rfl⟩
    exact gvFadingRate_le_isotropic hq hiso hP ht hK htr

/-! ### Eigenvalues and limits -/

omit [DecidableEq t] in
/-- **Lecture 10, page 10-14.** `½ log |I + x G Gᵀ| = ∑ⱼ ½ log (1 + x Λⱼ)`, where `Λⱼ` are the
eigenvalues of `G Gᵀ`. -/
theorem gvRate_isotropic_eq_sum [DecidableEq t] (G : Matrix r t ℝ) {x : ℝ} (hx : 0 ≤ x) :
    gvRate G (x • 1) =
      ∑ j, 1 / 2 * log (1 + x * (posSemidef_self_mul_transpose G).1.eigenvalues j) := by
  have hA := posSemidef_self_mul_transpose G
  have e : G * (x • (1 : Matrix t t ℝ)) * Gᵀ + 1 = (1 : ℝ) • (1 : Matrix r r ℝ) + x • (G * Gᵀ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, one_smul, add_comm]
  rw [gvRate, e, det_smul_one_add_smul hA.1, log_prod fun j _ => ?_, mul_sum]
  have := mul_nonneg hx (hA.eigenvalues_nonneg j)
  linarith

omit [DecidableEq t] in
/-- The rate of `(x) I` at low SNR: `½ log |I + x G Gᵀ| / x → ½ tr(G Gᵀ)`. -/
theorem tendsto_gvRate_div [DecidableEq t] (G : Matrix r t ℝ) :
    Tendsto (fun x : ℝ => gvRate G (x • 1) / x) (𝓝[>] 0) (𝓝 (1 / 2 * (G * Gᵀ).trace)) := by
  have hA := posSemidef_self_mul_transpose G
  have hlog : ∀ a : ℝ, Tendsto (fun x : ℝ => log (1 + x * a) / x) (𝓝[>] 0) (𝓝 a) := fun a => by
    have hd : HasDerivAt (fun x : ℝ => log (1 + x * a)) a 0 := by
      have h1 : HasDerivAt (fun x : ℝ => 1 + x * a) a 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add 1
      have h2 := h1.log (by simp)
      simpa using h2
    have h3 := hd.tendsto_slope_zero_right
    refine h3.congr fun x => ?_
    simp [div_eq_inv_mul]
  have htr : (G * Gᵀ).trace = ∑ j, hA.1.eigenvalues j := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp
  have hsum := tendsto_finsetSum (univ : Finset r)
    fun j _ => (hlog (hA.1.eigenvalues j)).const_mul (1 / 2 : ℝ)
  rw [htr, mul_sum]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [gvRate_isotropic_eq_sum G (le_of_lt hx), sum_div]
  exact sum_congr rfl fun j _ => by ring

omit [DecidableEq t] in
/-- The rate of `x I` at high SNR, with `m` the number of nonzero eigenvalues of `G Gᵀ`:
`½ log |I + x G Gᵀ| - (m/2) log x → ½ ∑ⱼ log Λⱼ`, the sum being over the nonzero eigenvalues as
`log 0 = 0`. -/
theorem tendsto_gvRate_sub_log [DecidableEq t] (G : Matrix r t ℝ) :
    Tendsto (fun x : ℝ => gvRate G (x • 1) -
        ((univ.filter fun j => (posSemidef_self_mul_transpose G).1.eigenvalues j ≠ 0).card : ℝ) /
          2 * log x) atTop
      (𝓝 (∑ j, 1 / 2 * log ((posSemidef_self_mul_transpose G).1.eigenvalues j))) := by
  have hA := posSemidef_self_mul_transpose G
  set lam := hA.1.eigenvalues with hlam
  have hlam0 : ∀ j, 0 ≤ lam j := hA.eigenvalues_nonneg
  have hterm : ∀ j, Tendsto (fun x : ℝ => 1 / 2 * log (1 + x * lam j) -
      (if lam j ≠ 0 then (1 : ℝ) else 0) / 2 * log x) atTop (𝓝 (1 / 2 * log (lam j))) := fun j => by
    by_cases h : lam j = 0
    · simp [h]
    · have hpos : 0 < lam j := lt_of_le_of_ne (hlam0 j) (Ne.symm h)
      simp only [h, ne_eq, not_false_eq_true, ite_true]
      have hinv : Tendsto (fun x : ℝ => x⁻¹ + lam j) atTop (𝓝 (0 + lam j)) :=
        tendsto_inv_atTop_zero.add_const _
      rw [zero_add] at hinv
      have hlog := ((continuousAt_log hpos.ne').tendsto.comp hinv).const_mul (1 / 2 : ℝ)
      refine hlog.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [Function.comp_apply]
      have e : x⁻¹ + lam j = (1 + x * lam j) / x := by
        field_simp
      rw [e, log_div (by positivity) hx.ne']
      ring
  have hsum := tendsto_finsetSum (univ : Finset r) fun j _ => hterm j
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [gvRate_isotropic_eq_sum G hx, sum_sub_distrib]
  congr 1
  rw [← sum_mul, ← sum_div, card_filter]
  push_cast
  rfl

/-- **Lecture 10, page 10-15.** The low SNR behaviour of the fading channel:
`C/P → E[tr(G Gᵀ)]/(2t)`, for the rate of `(P/t) I`. For Rayleigh fading this is `r/2`, an `r`-fold
gain over a single receive antenna. -/
theorem tendsto_gvFadingRate_div (q : σ → ℝ) (G : σ → Matrix r t ℝ) (ht : 0 < Fintype.card t) :
    Tendsto (fun P : ℝ => gvFadingRate q G ((P / Fintype.card t) • 1) / P) (𝓝[>] 0)
      (𝓝 (∑ s, q s * (G s * (G s)ᵀ).trace / (2 * Fintype.card t))) := by
  have hn' : (0 : ℝ) < Fintype.card t := by exact_mod_cast ht
  have hscale : Tendsto (fun P : ℝ => P / (Fintype.card t : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun P : ℝ => P / (Fintype.card t : ℝ)) (𝓝 0) (𝓝 (0 / (Fintype.card t : ℝ))) :=
        (continuous_id.div_const _).tendsto 0
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with P hP
      exact div_pos hP hn'
  have hterm : ∀ s, Tendsto (fun P : ℝ => q s * (gvRate (G s) ((P / Fintype.card t) • 1) /
      (P / Fintype.card t)) / Fintype.card t) (𝓝[>] 0)
      (𝓝 (q s * (1 / 2 * (G s * (G s)ᵀ).trace) / Fintype.card t)) := fun s =>
    (((tendsto_gvRate_div (G s)).comp hscale).const_mul (q s)).div_const _
  have hsum := tendsto_finsetSum (univ : Finset σ) fun s _ => hterm s
  have elim : ∑ s, q s * (G s * (G s)ᵀ).trace / (2 * Fintype.card t) =
      ∑ s, q s * (1 / 2 * (G s * (G s)ᵀ).trace) / Fintype.card t :=
    sum_congr rfl fun s _ => by field_simp
  rw [elim]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with P hP
  have hP' : P ≠ 0 := (show 0 < P from hP).ne'
  rw [gvFadingRate, sum_div]
  refine sum_congr rfl fun s _ => ?_
  field_simp

/-- **Lecture 10, page 10-15.** The high SNR behaviour of the fading channel when the rank of `G Gᵀ`
is
`m` in each state: `C - (m/2) log(P/t) → E[½ ∑ⱼ log Λⱼ]`, for the rate of `(P/t) I`. This is an
`m`-fold
increase of the capacity, with `m = min(t, r)` for full rank. -/
theorem tendsto_gvFadingRate_sub_log {q : σ → ℝ} (hq : ∑ s, q s = 1) (G : σ → Matrix r t ℝ)
    (ht : 0 < Fintype.card t) {m : ℕ}
    (hm : ∀ s,
      (univ.filter fun j => (posSemidef_self_mul_transpose (G s)).1.eigenvalues j ≠ 0).card = m) :
    Tendsto (fun P : ℝ => gvFadingRate q G ((P / Fintype.card t) • 1) -
        (m : ℝ) / 2 * log (P / Fintype.card t)) atTop
      (𝓝 (∑ s, q s *
        ∑ j, 1 / 2 * log ((posSemidef_self_mul_transpose (G s)).1.eigenvalues j))) := by
  have hn' : (0 : ℝ) < Fintype.card t := by exact_mod_cast ht
  have hscale : Tendsto (fun P : ℝ => P / (Fintype.card t : ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const hn'
  have hterm : ∀ s, Tendsto (fun P : ℝ => q s * (gvRate (G s) ((P / Fintype.card t) • 1) -
      (m : ℝ) / 2 * log (P / Fintype.card t))) atTop
      (𝓝 (q s * ∑ j, 1 / 2 * log ((posSemidef_self_mul_transpose (G s)).1.eigenvalues j))) :=
    fun s => by
      have h := (tendsto_gvRate_sub_log (G s)).comp hscale
      rw [hm s] at h
      exact h.const_mul (q s)
  have hsum := tendsto_finsetSum (univ : Finset σ) fun s _ => hterm s
  refine hsum.congr fun P => ?_
  simp only [mul_sub, sum_sub_distrib, gvFadingRate]
  rw [← sum_mul, hq, one_mul]

end InfoTheory
