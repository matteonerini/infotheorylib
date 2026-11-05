/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.DifferentialEntropy.MultivariateGaussian
public import InfoTheoryLib.Network.GaussianNetTDM

/-!
# The Gupta–Kumar random network: the bounds for a fixed network

The analytic parts of the scaling law of Lecture 20 of El Gamal and Kim that do not involve the
random positions of the nodes.

## Main definitions

* `gkInterf ν P`: the constant `a₁` of the interference, page 20-27.
* `gkRate`: the rate of the cellular time division scheme, page 20-28.

## Main statements

* `summable_gkOne`, `summable_gkTwo`: the two series of the interference converge for `ν > 2`.
* `gkInterference_eq`: the interference is `a₁ (log N) ^ (-ν / 2)`.
* `gkRate_ge`: **the rate of the cellular scheme is `Ω(N^{-1/2} (log N)^{-(ν+1)/2})`**, if
  `L(N) + S(N) = O((N log N)^{1/2})`.
* `gvRate_le_sum_log`: **the chain of inequalities of page 20-33**.
* `gvRate_submatrix_le`: removing rows and columns of a gain matrix decreases the rate.
* `IsAchievableGN.sum_le_sum_log`: **the upper bound for a fixed network**, operational.
* `gk_dist_sq_le`, `gk_received_ge`: the distance and the received power in a neighboring cell.
* `gk_nnc_gap`, `gvRate_half`: the evaluation of the noisy network coding terms of page 20-6.
* `isTheta_gaussCap_div`: `C(N^k P) / N = Θ(log N / N)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 20
-/

open Real Finset Matrix Filter Topology Asymptotics
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The order of the rates -/

section Order

/-- **Pages 20-10 and 20-13 of [elgamal2010].** `C(N ^ k P) / N = Θ(log N / N)`, for `k ≥ 1`. -/
theorem isTheta_gaussCap_div {k : ℕ} (hk : 0 < k) {P : ℝ} (hP : 0 < P) :
    (fun N : ℕ => gaussCap ((N : ℝ) ^ k * P) / N) =Θ[atTop] fun N : ℕ => log N / N := by
  have hlim : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : ∀ᶠ N : ℕ in atTop, gaussCap ((N : ℝ) ^ k * P) ≤ ((k : ℝ) + 1) * log N := by
    filter_upwards [hlim.eventually_ge_atTop (log (1 + P)), eventually_ge_atTop 1] with N hN hN1
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h₁ : 1 + (N : ℝ) ^ k * P ≤ (1 + P) * (N : ℝ) ^ k := by
      have : (1 : ℝ) ≤ (N : ℝ) ^ k := one_le_pow₀ hN'
      nlinarith
    have h₂ : log (1 + (N : ℝ) ^ k * P) ≤ log (1 + P) + k * log N := by
      refine (log_le_log (by positivity) h₁).trans (le_of_eq ?_)
      rw [log_mul (by positivity) (by positivity), log_pow]
    have h₃ : 0 ≤ log (N : ℝ) := log_nonneg hN'
    simp only [gaussCap]
    nlinarith
  have hlower : ∀ᶠ N : ℕ in atTop, 1 / 4 * log (N : ℝ) ≤ gaussCap ((N : ℝ) ^ k * P) := by
    filter_upwards [hlim.eventually_ge_atTop (2 * log (1 / P)), eventually_ge_atTop 1] with N hN hN1
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h₁ : (N : ℝ) * P ≤ 1 + (N : ℝ) ^ k * P := by
      have : (N : ℝ) ≤ (N : ℝ) ^ k := le_self_pow₀ hN' hk.ne'
      nlinarith
    have h₂ : log N + log P ≤ log (1 + (N : ℝ) ^ k * P) := by
      rw [← log_mul (by positivity) hP.ne']
      exact log_le_log (by positivity) h₁
    have h₃ : log (1 / P) = -log P := by
      rw [one_div, log_inv]
    rw [h₃] at hN
    simp only [gaussCap]
    linarith
  refine ⟨IsBigO.of_bound ((k : ℝ) + 1) ?_, IsBigO.of_bound 4 ?_⟩
  · filter_upwards [hupper, hlower, eventually_ge_atTop 1] with N h₁ h₂ hN1
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
    have hl : 0 ≤ log (N : ℝ) := log_natCast_nonneg N
    have h₀ : 0 ≤ gaussCap ((N : ℝ) ^ k * P) := by linarith
    rw [norm_div, norm_div, Real.norm_of_nonneg h₀, Real.norm_of_nonneg hl,
      Real.norm_of_nonneg hN'.le, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h₁ hN'.le
  · filter_upwards [hlower, eventually_ge_atTop 1] with N h₂ hN1
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
    have hl : 0 ≤ log (N : ℝ) := log_natCast_nonneg N
    have h₀ : 0 ≤ gaussCap ((N : ℝ) ^ k * P) := by linarith
    rw [norm_div, norm_div, Real.norm_of_nonneg h₀, Real.norm_of_nonneg hl,
      Real.norm_of_nonneg hN'.le, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hN'.le
    linarith

end Order

/-! ### The interference -/

section Interference

variable {ν : ℝ}

/-- A term of the first series of page 20-27, with `j` replaced by `j + 1`. -/
def gkOne (ν : ℝ) (j : ℕ) : ℝ := 2 / (((3 * (j : ℝ) + 1) ^ 2) ^ (ν / 2))

/-- A term of the second series of page 20-27, with `j, k` replaced by `j + 1, k + 1`. -/
def gkTwo (ν : ℝ) (p : ℕ × ℕ) : ℝ :=
  4 / (((3 * (p.1 : ℝ) + 1) ^ 2 + (3 * (p.2 : ℝ) + 2) ^ 2) ^ (ν / 2))

lemma summable_half (hν : 2 < ν) : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ (ν / 2) :=
  summable_zetaTerm (by linarith)

/-- **Page 20-27 of [elgamal2010].** The first series converges for `ν > 2`. -/
theorem summable_gkOne (hν : 2 < ν) : Summable (gkOne ν) := by
  have hν0 : 0 < ν / 2 := by linarith
  refine Summable.of_nonneg_of_le (fun j => by unfold gkOne; positivity) (fun j => ?_)
    ((summable_half hν).mul_left 2)
  simp only [gkOne]
  rw [← mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine one_div_le_one_div_of_le (by positivity) (rpow_le_rpow (by positivity) ?_ hν0.le)
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- **Page 20-27 of [elgamal2010].** The second series converges for `ν > 2`. -/
theorem summable_gkTwo (hν : 2 < ν) : Summable (gkTwo ν) := by
  have hν0 : 0 < ν / 2 := by linarith
  have hprod := ((summable_half hν).mul_of_nonneg (summable_half hν)
    (fun m => by positivity) (fun m => by positivity)).mul_left 4
  refine Summable.of_nonneg_of_le (fun p => by unfold gkTwo; positivity) (fun p => ?_) hprod
  obtain ⟨j, k⟩ := p
  simp only [gkTwo]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h₁ : ((j : ℝ) + 1) * ((k : ℝ) + 1) ≤ (3 * (j : ℝ) + 1) ^ 2 + (3 * (k : ℝ) + 2) ^ 2 := by
    nlinarith
  have h₂ : (((j : ℝ) + 1) * ((k : ℝ) + 1)) ^ (ν / 2) ≤
      ((3 * (j : ℝ) + 1) ^ 2 + (3 * (k : ℝ) + 2) ^ 2) ^ (ν / 2) :=
    rpow_le_rpow (by positivity) h₁ hν0.le
  rw [mul_rpow (by positivity) (by positivity)] at h₂
  have h₃ : 0 < ((j : ℝ) + 1) ^ (ν / 2) * ((k : ℝ) + 1) ^ (ν / 2) := by positivity
  calc 4 / ((3 * (j : ℝ) + 1) ^ 2 + (3 * (k : ℝ) + 2) ^ 2) ^ (ν / 2)
      ≤ 4 / (((j : ℝ) + 1) ^ (ν / 2) * ((k : ℝ) + 1) ^ (ν / 2)) :=
        div_le_div_of_nonneg_left (by norm_num) h₃ h₂
    _ = _ := by
        field_simp

/-- **Page 20-27 of [elgamal2010].** The constant `a₁` of the interference. -/
def gkInterf (ν P : ℝ) : ℝ := P * (∑' j, gkOne ν j + ∑' p, gkTwo ν p)

/-- **Page 20-27 of [elgamal2010].** The two series of the interference at a cell size `L`, summed:
this is `a₁ L ^ (-ν / 2)`. -/
theorem gkInterference_eq (P : ℝ) {L : ℝ} (hL : 0 < L) :
    (∑' j : ℕ, 2 * P / (((3 * (j : ℝ) + 1) ^ 2 * L) ^ (ν / 2))) +
      (∑' p : ℕ × ℕ, 4 * P / ((((3 * (p.1 : ℝ) + 1) ^ 2 + (3 * (p.2 : ℝ) + 2) ^ 2) * L) ^ (ν / 2)))
        =
    gkInterf ν P * L ^ (-(ν / 2)) := by
  have hpow : L ^ (-(ν / 2)) = (L ^ (ν / 2))⁻¹ := rpow_neg hL.le _
  have h₁ : ∀ j : ℕ, 2 * P / (((3 * (j : ℝ) + 1) ^ 2 * L) ^ (ν / 2)) =
      gkOne ν j * (P * L ^ (-(ν / 2))) := by
    intro j
    rw [mul_rpow (by positivity) hL.le, hpow, gkOne]
    have : 0 < L ^ (ν / 2) := rpow_pos_of_pos hL _
    have h₃ : 0 < ((3 * (j : ℝ) + 1) ^ 2) ^ (ν / 2) := by positivity
    field_simp
  have h₂ : ∀ p : ℕ × ℕ, 4 * P / (((3 * (p.1 : ℝ) + 1) ^ 2 + (3 * (p.2 : ℝ) + 2) ^ 2) * L) ^ (ν / 2)
    =
      gkTwo ν p * (P * L ^ (-(ν / 2))) := by
    intro p
    rw [mul_rpow (by positivity) hL.le, hpow, gkTwo]
    have : 0 < L ^ (ν / 2) := rpow_pos_of_pos hL _
    have h₃ : 0 < ((3 * (p.1 : ℝ) + 1) ^ 2 + (3 * (p.2 : ℝ) + 2) ^ 2) ^ (ν / 2) := by positivity
    field_simp
  simp_rw [h₁, h₂]
  rw [tsum_mul_right, tsum_mul_right, gkInterf]
  ring

lemma gkInterf_nonneg (ν : ℝ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ gkInterf ν P :=
  mul_nonneg hP (add_nonneg (tsum_nonneg fun j => by unfold gkOne; positivity)
    (tsum_nonneg fun p => by unfold gkTwo; positivity))

/-- **Page 20-28 of [elgamal2010].** The rate of the cellular time division scheme, when there are
`s = L(N) + S(N)` node-blocks in a cell-block, for a cell size `L`. -/
def gkRate (ν P L s : ℝ) : ℝ :=
  1 / (9 * s) * gaussCap ((5 * L) ^ (-(ν / 2)) * P / (1 + gkInterf ν P * L ^ (-(ν / 2))))

/-- **Page 20-28 of [elgamal2010]: the order of the rate of the cellular scheme.** If the cells have
area `L` between `log N` and `4 log N`, and `L(N) + S(N) ≤ c (N log N)^{1/2}`, the rate of the
scheme is at least `c' N^{-1/2} (log N)^{-(ν+1)/2}`, for all large `N`. -/
theorem gkRate_ge (hν : 2 < ν) {P c : ℝ} (hP : 0 < P) (hc : 0 < c) :
    ∃ c' > 0, ∀ᶠ N : ℕ in atTop, ∀ L s : ℝ, log N ≤ L → L ≤ 4 * log N → 0 < s →
      s ≤ c * ((N : ℝ) * log N) ^ (1 / 2 : ℝ) →
      c' * ((N : ℝ) ^ (-(1 / 2) : ℝ) * (log N) ^ (-((ν + 1) / 2))) ≤ gkRate ν P L s := by
  have hν0 : 0 < ν / 2 := by linarith
  set a₁ := gkInterf ν P with ha₁
  have ha₁0 : 0 ≤ a₁ := gkInterf_nonneg ν hP.le
  set κ := (5 : ℝ) ^ (-(ν / 2)) * P / (1 + a₁) with hκ
  have hκ0 : 0 < κ := by positivity
  set κ₄ := κ * (4 : ℝ) ^ (-(ν / 2)) with hκ₄
  refine ⟨1 / (9 * c) * (κ₄ / 4), by positivity, ?_⟩
  have hlim : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => (log (N : ℝ)) ^ (-(ν / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hν0).comp hlim
  filter_upwards [hlim.eventually_ge_atTop 1, eventually_ge_atTop 1,
    (tendsto_order.1 hsmall).2 (1 / ((5 : ℝ) ^ (-(ν / 2)) * P + 1)) (by positivity)]
    with N hℓ hN1 hx L s hL hL₄ hs hsle
  set ℓ := log (N : ℝ) with hℓd
  have hℓ0 : 0 < ℓ := by linarith
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpow : L ^ (-(ν / 2)) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hpow0 : 0 < L ^ (-(ν / 2)) := rpow_pos_of_pos hL0 _
  have hpowℓ : L ^ (-(ν / 2)) ≤ ℓ ^ (-(ν / 2)) := rpow_le_rpow_of_nonpos hℓ0 hL (by linarith)
  have hpow₄ : (4 : ℝ) ^ (-(ν / 2)) * ℓ ^ (-(ν / 2)) ≤ L ^ (-(ν / 2)) := by
    rw [← mul_rpow (by norm_num) hℓ0.le]
    exact rpow_le_rpow_of_nonpos hL0 hL₄ (by linarith)
  set x := (5 * L) ^ (-(ν / 2)) * P / (1 + a₁ * L ^ (-(ν / 2))) with hx'
  have h5 : (5 * L) ^ (-(ν / 2)) = (5 : ℝ) ^ (-(ν / 2)) * L ^ (-(ν / 2)) :=
    mul_rpow (by norm_num) hL0.le
  have hxlow : κ * L ^ (-(ν / 2)) ≤ x := by
    rw [hx', h5, hκ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h₁ : a₁ * L ^ (-(ν / 2)) ≤ a₁ := by nlinarith
    have h₂ : 0 ≤ (5 : ℝ) ^ (-(ν / 2)) * P * L ^ (-(ν / 2)) := by positivity
    nlinarith
  have hxlow₄ : κ₄ * ℓ ^ (-(ν / 2)) ≤ x := by
    refine le_trans ?_ hxlow
    rw [hκ₄, mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow₄ hκ0.le
  have hxup : x ≤ 1 := by
    rw [hx', h5, div_le_one (by positivity)]
    have h₁ : 0 ≤ a₁ * L ^ (-(ν / 2)) := by positivity
    have hA : 0 < (5 : ℝ) ^ (-(ν / 2)) * P + 1 := by positivity
    rw [lt_div_iff₀ hA] at hx
    have h₂ : L ^ (-(ν / 2)) * ((5 : ℝ) ^ (-(ν / 2)) * P + 1) < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpowℓ hA.le) hx
    nlinarith [rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5) (-(ν / 2))]
  have hx0 : 0 ≤ x := le_trans (by positivity) hxlow
  -- the capacity function
  have hcap : x / 4 ≤ gaussCap x := by
    simp only [gaussCap]
    have h₁ : x / (1 + x) ≤ log (1 + x) := by
      have h₂ := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + x)
      have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by
        field_simp
        ring
      rwa [e] at h₂
    have h₃ : x / 2 ≤ x / (1 + x) :=
      div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
    linarith
  have hsprod : 0 < ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ) := rpow_pos_of_pos (by positivity) _
  have hexp : (N : ℝ) ^ (-(1 / 2) : ℝ) * ℓ ^ (-((ν + 1) / 2)) =
      ((N : ℝ) * ℓ) ^ (-(1 / 2 : ℝ)) * ℓ ^ (-(ν / 2)) := by
    rw [mul_rpow hN0.le hℓ0.le, mul_assoc, ← rpow_add hℓ0]
    congr 2
    ring
  have hinv : ((N : ℝ) * ℓ) ^ (-(1 / 2 : ℝ)) = 1 / ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ) := by
    rw [rpow_neg (by positivity), inv_eq_one_div]
  rw [hexp, hinv]
  simp only [gkRate]
  rw [← ha₁, ← hx']
  have hstep₁ : 1 / (9 * (c * ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ))) ≤ 1 / (9 * s) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hcap₀ : 0 ≤ gaussCap x := by linarith
  calc _ = 1 / (9 * (c * ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ))) * ((κ₄ * ℓ ^ (-(ν / 2))) / 4) := by
        field_simp
    _ ≤ 1 / (9 * (c * ((N : ℝ) * ℓ) ^ (1 / 2 : ℝ))) * gaussCap x := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hstep₁ hcap₀

end Interference

/-! ### The upper bound -/

section Upper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Page 20-33 of [elgamal2010]: the chain of inequalities.** If the gain matrix `G` is symmetric
and positive semidefinite, and `tr(K) ≤ T`, then
`½ log |I + G K Gᵀ| ≤ log |I + T^{1/2} G| ≤ ∑ⱼ log (1 + T^{1/2} G_{jj})`. -/
theorem gvRate_le_sum_log {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {K : Matrix ι ι ℝ}
    (hK : K.PosSemidef) {T : ℝ} (hT : K.trace ≤ T) (hT0 : 0 ≤ T) :
    gvRate G K ≤ ∑ j, log (1 + √T * G j j) := by
  have hGT : Gᵀ = G := by
    have := hG.1
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using this
  have hs : 0 ≤ √T := sqrt_nonneg T
  have h₁ := gvRate_le_of_trace_le G hK hT
  -- the matrix `I + T^{1/2} G`
  set A := (1 : Matrix ι ι ℝ) + √T • G with hA
  have hApos : A.PosDef := PosDef.one.add_posSemidef (hG.smul hs)
  have hdet0 := hApos.det_pos
  have e₁ : G * (T • (1 : Matrix ι ι ℝ)) * Gᵀ + 1 = T • (G * G) + 1 := by
    rw [hGT, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hAA : A * A - (T • (G * G) + 1) = (2 * √T) • G := by
    rw [hA]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    have : √T • √T • (G * G) = T • (G * G) := by
      rw [smul_smul, mul_self_sqrt hT0]
    rw [smul_add, this, two_mul, add_smul]
    abel
  have hB : (T • (G * G) + 1).PosSemidef := by
    have h₂ : (G * G).PosSemidef := by
      have := posSemidef_self_mul_transpose G
      rwa [hGT] at this
    exact (h₂.smul hT0).add PosSemidef.one
  have hle : (T • (G * G) + 1).det ≤ (A * A).det :=
    det_le_det_of_posSemidef_sub hB (hAA ▸ hG.smul (by positivity))
  have hBpos : 0 < (T • (G * G) + 1).det := by
    have h₂ : (G * G).PosSemidef := by
      have := posSemidef_self_mul_transpose G
      rwa [hGT] at this
    exact (posDef_add_one (h₂.smul hT0)).det_pos
  have h₂ : gvRate G (T • 1) ≤ log A.det := by
    simp only [gvRate]
    rw [e₁]
    have h₃ := log_le_log hBpos hle
    rw [det_mul, log_mul hdet0.ne' hdet0.ne'] at h₃
    linarith
  have h₃ : log A.det ≤ ∑ j, log (1 + √T * G j j) := by
    have hd := det_le_prod_diag hApos
    have hentry : ∀ j, A j j = 1 + √T * G j j := fun j => by simp [hA]
    have hentry0 : ∀ j, 0 < A j j := fun j => hApos.diag_pos
    refine (log_le_log hdet0 hd).trans (le_of_eq ?_)
    rw [log_prod fun j _ => (hentry0 j).ne']
    exact sum_congr rfl fun j _ => by rw [hentry]
  exact h₁.trans (h₂.trans h₃)

omit [Fintype ι] [DecidableEq ι] in
/-- The two forms of the rate at a scalar covariance: the rate of a gain matrix and of its
transpose are equal. -/
lemma gvRate_transpose {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
    (H : Matrix r t ℝ) (P : ℝ) : gvRate Hᵀ (P • 1) = gvRate H (P • 1) := by
  simp only [gvRate, transpose_transpose, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have e := det_mul_add_one_comm (P • Hᵀ) H
  rw [Matrix.smul_mul, Matrix.mul_smul] at e
  rw [e]

omit [Fintype ι] [DecidableEq ι] in
/-- A gain matrix followed by a contraction has a smaller rate. -/
lemma gvRate_mul_le {r s t : Type*} [Fintype r] [Fintype s] [Fintype t] [DecidableEq r]
    [DecidableEq s] [DecidableEq t] (C : Matrix r s ℝ) (E : Matrix s t ℝ)
    (hE : (1 - E * Eᵀ).PosSemidef) {P : ℝ} (hP : 0 ≤ P) :
    gvRate (C * E) (P • 1) ≤ gvRate C (P • 1) := by
  have e : gvRate (C * E) (P • 1) = gvRate C (P • (E * Eᵀ)) := by
    simp only [gvRate, transpose_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_assoc]
  rw [e]
  refine gvRate_mono C ((posSemidef_self_mul_transpose E).smul hP) ?_
  rw [← smul_sub]
  exact hE.smul hP

omit [Fintype ι] in
/-- A selection of coordinates is a contraction. -/
lemma posSemidef_one_sub_select {t : Type*} [Finite ι] [Fintype t] {s : t → ι}
    (hs : Function.Injective s) :
    (1 - ((1 : Matrix ι ι ℝ).submatrix id s) *
      ((1 : Matrix ι ι ℝ).submatrix id s)ᵀ).PosSemidef := by
  classical
  cases nonempty_fintype ι
  set E := (1 : Matrix ι ι ℝ).submatrix id s with hEd
  have hEE : Eᵀ * E = 1 := by
    ext a b
    simp [hEd, Matrix.mul_apply, Matrix.one_apply, hs.eq_iff]
  have h := posSemidef_self_mul_transpose (1 - E * Eᵀ)
  have e : (1 - E * Eᵀ) * (1 - E * Eᵀ)ᵀ = 1 - E * Eᵀ := by
    have e₁ : (1 - E * Eᵀ)ᵀ = 1 - E * Eᵀ := by
      simp [transpose_sub, transpose_mul]
    have e₂ : E * Eᵀ * (E * Eᵀ) = E * Eᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, hEE, Matrix.one_mul]
    rw [e₁, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, e₂]
    abel
  rwa [e] at h

/-- Removing rows and columns of a gain matrix decreases the rate. This is the step from the
network to the augmented network on page 20-32 of [elgamal2010]. -/
theorem gvRate_submatrix_le {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
    (G : Matrix ι ι ℝ) {d : r → ι} {s : t → ι} (hd : Function.Injective d)
    (hs : Function.Injective s) {P : ℝ} (hP : 0 ≤ P) :
    gvRate (G.submatrix d s) (P • 1) ≤ gvRate G (P • 1) := by
  set Es := (1 : Matrix ι ι ℝ).submatrix id s with hEs
  set Ed := (1 : Matrix ι ι ℝ).submatrix id d with hEd
  have e : G.submatrix d s = (Edᵀ * G) * Es := by
    ext a b
    simp [hEs, hEd, Matrix.mul_apply, Matrix.one_apply]
  rw [e]
  refine (gvRate_mul_le _ _ (posSemidef_one_sub_select hs) hP).trans ?_
  rw [← gvRate_transpose (Edᵀ * G), transpose_mul, transpose_transpose,
    ← gvRate_transpose G]
  exact gvRate_mul_le _ _ (posSemidef_one_sub_select hd) hP

/-- **The first step of page 20-33 of [elgamal2010].** A rate tuple achievable in a part of a
network with gain matrix `G` has a sum rate at most `½ log |I + P G Gᵀ|`. -/
theorem IsAchievableGN.sum_le_gain {r t : Type*} [Fintype r] [Fintype t]
    [DecidableEq t] {G : Matrix ι ι ℝ} {d : r → ι} {s : t → ι} (hd : Function.Injective d)
    (hs : Function.Injective s) {D : t → Finset r} {P : ℝ≥0} {R : t → ℝ}
    (h : IsAchievableGN (G.submatrix d s) D P R) (hD : ∀ j, (D j).Nonempty) :
    (∑ j, R j) * log 2 ≤ gvRate G ((P : ℝ) • 1) := by
  classical
  have h₁ := h.sum_le univ univ fun j _ => by
    obtain ⟨k, hk⟩ := hD j
    exact ⟨k, mem_univ k, hk⟩
  rw [gvRate_submatrix_univ] at h₁
  exact h₁.trans (gvRate_submatrix_le G hd hs P.2)

omit [DecidableEq ι] in
/-- **The upper bound of page 20-33 of [elgamal2010], for a fixed network.** If the gain matrix `G`
of the augmented network is positive semidefinite, the sum rate of the original network is at most
`D = ∑ⱼ log (1 + (|ι| P)^{1/2} G_{jj})`. -/
theorem IsAchievableGN.sum_le_sum_log {r t : Type*} [Fintype r] [Fintype t]
    [DecidableEq t] {G : Matrix ι ι ℝ} (hG : G.PosSemidef) {d : r → ι} {s : t → ι}
    (hd : Function.Injective d) (hs : Function.Injective s) {D : t → Finset r} {P : ℝ≥0}
    {R : t → ℝ} (h : IsAchievableGN (G.submatrix d s) D P R) (hD : ∀ j, (D j).Nonempty) :
    (∑ j, R j) * log 2 ≤ ∑ j, log (1 + √((Fintype.card ι : ℝ) * P) * G j j) := by
  classical
  refine (h.sum_le_gain hd hs hD).trans (gvRate_le_sum_log hG (PosSemidef.one.smul P.2) ?_
    (by positivity))
  simp [trace_smul, mul_comm]

end Upper

/-! ### The received power -/

section Power

variable {ν L P : ℝ}

/-- **Page 20-26 of [elgamal2010].** Two nodes in neighboring cells of area `L` are at a squared
distance at most `5 L`. -/
theorem gk_dist_sq_le {x y : ℝ} (hL : 0 ≤ L) (hx : |x| ≤ 2 * √L) (hy : |y| ≤ √L) :
    x ^ 2 + y ^ 2 ≤ 5 * L := by
  have h₁ : x ^ 2 ≤ (2 * √L) ^ 2 := sq_le_sq' (by linarith [(abs_le.1 hx).1]) (abs_le.1 hx).2
  have h₂ : y ^ 2 ≤ (√L) ^ 2 := sq_le_sq' (by linarith [(abs_le.1 hy).1]) (abs_le.1 hy).2
  rw [mul_pow, sq_sqrt hL] at h₁
  rw [sq_sqrt hL] at h₂
  linarith

/-- **Page 20-26 of [elgamal2010].** The power received in a neighboring cell is at least
`(5 L)^{-ν/2} P`. -/
theorem gk_received_ge (hν : 0 ≤ ν) (hP : 0 ≤ P) {r : ℝ} (hr : 0 < r) (hrL : r ≤ 5 * L) :
    (5 * L) ^ (-(ν / 2)) * P ≤ r ^ (-(ν / 2)) * P :=
  mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos hr hrL (by linarith)) hP

end Power

/-! ### The noisy network coding rate -/

section NNC

/-- **Page 20-6 of [elgamal2010].** The conditional entropies of the quantized outputs are those of
Gaussians of variances `2` and `1`, and they differ by `½ log 2` per node. -/
theorem gk_nnc_gap (s : ℝ) :
    s * (1 / 2 * log (2 * π * exp 1 * 2)) - s * (1 / 2 * log (2 * π * exp 1)) =
      s * (log 2 / 2) := by
  have h : (2 * π * exp 1 * 2) = (2 * π * exp 1) * 2 := rfl
  rw [h, log_mul (by positivity) (by norm_num)]
  ring

/-- **Page 20-6 of [elgamal2010].** The information term of noisy network coding: since the
quantized outputs have noise variance `2`, it is `½ log |2 I + P G Gᵀ| - ½ log |2 I|`, which is the
rate at the power `P / 2`. -/
theorem gvRate_half {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
    (G : Matrix r t ℝ) {P : ℝ} (hP : 0 ≤ P) :
    1 / 2 * log (P • (G * Gᵀ) + (2 : ℝ) • (1 : Matrix r r ℝ)).det -
        1 / 2 * log ((2 : ℝ) • (1 : Matrix r r ℝ)).det =
      gvRate G ((P / 2) • 1) := by
  have e : P • (G * Gᵀ) + (2 : ℝ) • (1 : Matrix r r ℝ) =
      (2 : ℝ) • (G * ((P / 2) • (1 : Matrix t t ℝ)) * Gᵀ + 1) := by
    rw [smul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_smul]
    congr 2
    ring
  have hpos : 0 < (G * ((P / 2) • (1 : Matrix t t ℝ)) * Gᵀ + 1).det :=
    (posDef_add_one (posSemidef_mul_mul_transpose (PosSemidef.one.smul (by positivity)) G)).det_pos
  have e₂ : ((2 : ℝ) • (1 : Matrix r r ℝ)).det = 2 ^ Fintype.card r := by
    simp
  rw [e, det_smul, gvRate, e₂, log_mul (by positivity) hpos.ne']
  ring

end NNC

end InfoTheory
