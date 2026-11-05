/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Books.ElGamalKim.Lecture12DSBS
public import InfoTheoryLib.ChannelCoding.Product

/-!
# El Gamal & Kim, Lecture 12: Source Coding with Side Information

This file indexes the formalization of Lecture 12 of [elgamal2010] and contains the lossless
examples and the quadratic Gaussian computation. We prove Theorems 1 and 2, the Wyner–Ziv theorem,
and the special cases of side information at the encoder or at both ends, as coding theorems. The
examples for the doubly symmetric binary source are in `Books.ElGamalKim.Lecture12DSBS`.

## Conventions

* **Rates.** The operational rates are in bits, with the index sets `[1 : 2^{nR})` of the notes. The
  single-letter functions `sideRD`, `causalRD`, `wzRD`, `bothRD` and `infoRD` are in nats, and the
  theorems divide them by `log 2`.
* **Auxiliary random variables.** `U` takes values in `Fin k` for some `k`; the minimum is attained
  with `|𝒰| ≤ |𝒳| + 3`, against `|𝒰| ≤ |𝒳| + 1` in the notes.
* **Causal and noncausal together.** `sideRD θ` is `min (I(X; U) - θ I(Y; U))`, so that `causalRD`
  is `θ = 0` and `wzRD` is `θ = 1`, and all the properties have one proof.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Simple special cases (pages 12-3 and 12-4)
* Side information at the encoder only: `EncSideCode`, `IsAchievableEncSideBits`, `rateEncSideBits`,
  `rateEncSideBits_eq`, `EncSideCode.exists_rdCode_le` (`RateDistortion.SideInfoCases`), and the
  lossless case at `D = 0`: `rateEncSideBits_hamming_zero` (here).
* Side information at both ends: `BothSideCode`, `IsAchievableBothBits`, `rateBothBits`, `bothLaw`,
  `bothRate`, `bothRD`, `rateBothBits_eq`, by the reduction to the source `(X, Y)`: `bothSource`,
  `bothDist`, `isAchievableBothBits_iff`, `sideRate_bothSource`, `bothRD_eq_wzRD`.
* The lossless case at `D = 0`: `bothRD_hamming_zero`, `rateBothBits_hamming_zero` (here).

### The single-letter functions (pages 12-6 and 12-17)
* `siLaw`, `sideRate`, `sideCost`, `sideRD`, `causalRD`, `wzRD`; `I(X; U) - I(Y; U) = I(X; U | Y)`:
  `sideRate_one` (`RateDistortion.SideInfo`).
* The cardinality bound: `exists_fin_mean_eq` (`ForMathlib.SupportLemma`), `sideRate_eq_of_rep`,
  `sideCost_eq_of_rep`, `exists_side_reduce`, `exists_side_reduce₁`.
* The minimum and the closedness: `exists_sideRD_eq`, `exists_le_of_forall_side`, `sideRD_le`,
  `sideRD_nonneg`.
* Nonincreasing and convex: `sideRD_antitoneOn`, `sideRD_convexOn`, with `sideMix`,
  `sideRate_sideMix`, `sideCost_sideMix`.
* `R_SI-ED(D) ≤ R_SI-D(D) ≤ R_CSI-D(D) ≤ R(D)` (page 12-17): `bothRD_le_wzRD`, `wzRD_le_causalRD`,
  `causalRD_le_infoRD` (`RateDistortion.SideInfoCases`).

### Causal side information (pages 12-5 to 12-15)
* The codes: `CausalCode`, `IsAchievableCausalBits`, `rateCausalBits`
  (`RateDistortion.SideInfoAchievability`).
* **Theorem 1**: `rateCausalBits_eq` (`RateDistortion.SideInfoConverse`), `theorem_12_1` (here).
* Achievability: `sum_codebook_miss_le`, `sum_codebook_triple_le`, `eventually_causal_code`
  (`RateDistortion.SideInfoCovering`), `isAchievableCausalBits_of_lt`.
* The converse: `exists_mix_kernel`, `sum_mutualInfo_prefix_le`, `CausalCode.exists_kernel_le`,
  `IsAchievableCausalBits.exists_kernel`.
* **Theorem 2**: `IsLosslessCausalBits`, `losslessCausalRate`, `losslessCausalBits_eq`,
  `theorem_12_2` (here), with `isLosslessCausalBits_of_lt`, `losslessCausalRate_eq`,
  `condEntropy_XUY_eq_zero_iff`, `sideCost_hamming_le_zero_iff`.
* `H(X | Y) ≤ R*_CSI-D ≤ H(X)`: `condEntropy_le_losslessCausalRate`,
  `losslessCausalRate_le_entropy`.
* The three examples: `losslessCausalRate_diag`, `losslessCausalRate_prod`,
  `losslessCausalRate_pair` (here).
* `p(x, y) > 0` gives `R*_CSI-D = H(X)`: `losslessCausalRate_of_pos`.

### Noncausal side information (pages 12-16 to 12-27)
* The codes: `WZCode`, `IsAchievableWZBits`, `rateWZBits`.
* **The Wyner–Ziv theorem**: `rateWZBits_eq`, `wyner_ziv_theorem` (here).
* Achievability, with random binning: `wzIndex`, `wzIndex_not_mem_le`, `sum_bins_erase_le`,
  `sum_codebook_count_eq`, `exists_wz_code_le`, `eventually_wz_code`, `isAchievableWZBits_of_lt`.
* The converse: `WZCode.exists_kernel_le`, `IsAchievableWZBits.exists_kernel`,
  `condEntropy_iid_seq`.
* Slepian–Wolf as a special case (pages 12-16 and 12-25): `IsLosslessWZBits`,
  `isLosslessWZBits_of_lt`, `losslessWZBits_eq`.

### The doubly symmetric binary source (pages 12-7, 12-8, 12-19 and 12-20)
All in `Books.ElGamalKim.Lecture12DSBS`.
* `ψ` and its convexity: `dsbsPsi`, `dsbsDPsi`, `dsbsPsi_convexOn`, `dsbsPsi_tangent`,
  `dsbsDPsi_mono`.
* The converse by supporting lines: `sideRate_dsbs`, `sideCost_dsbs`, `dsbsLetter`,
  `line_le_sideRate`.
* Achievability: `sideRD_dsbs_le_psi`, `sideRD_dsbs_le_zero`.
* The point of tangency: `IsDsbsTangency`, `exists_isDsbsTangency`.
* `R_CSI-D`: `causalRD_dsbs_of_le_tangency`, `causalRD_dsbs_of_tangency_le`. `R_SI-D`:
  `wzRD_dsbs_of_le_tangency`, `wzRD_dsbs_of_tangency_le`. Both vanish for `D ≥ p`:
  `sideRD_dsbs_of_le`.
* `R_SI-ED`: `bothKernel`, `bothRate_bothKernel`, `sum_bothKernel_distortion`,
  `binEntropy_sub_le_bothRate`, `bothRD_dsbs`, `bothRD_dsbs_of_le`.
* The cost of the lack of side information at the encoder: `bothRD_lt_wzRD_dsbs`.
* Without side information, `R(D) = 1 - H(D)`: `infoRD_bernoulli` (`RateDistortion.Binary`).

### The quadratic Gaussian case (pages 12-18 and 12-19)
* The computations of the notes: `gaussian_condVar`, `gaussian_condVar_U`, `gaussian_estimate`,
  `gaussian_rate` (here).

## Not formalized

* The bound `|𝒰| ≤ |𝒳| + 1`, which needs the Fenchel–Eggleston strengthening of Carathéodory's
  theorem: we prove `|𝒰| ≤ |𝒳| + 3`, which is enough for all the theorems.
* Source coding when side information may be absent (pages 12-30 to 12-33), that is the results of
  Heegard and Berger and of Kaspi with two decoders.
* The coding theorems of the quadratic Gaussian case, including `R_SI-D(D) = R_SI-ED(D)`: the source
  is not discrete, and we only check the formulas of the notes.
* Deterministic binning and Lemma 1 of the Appendix, replaced by random binning (see the issues).
* The lossless cases `R*_SI-E = H(X)` and `R*_SI-ED = H(X | Y)` for the block probability of error;
  we have them for the distortion at `D = 0`.
* The tangent formulas for `p = 0` and `p = 1/2`, where no point of tangency exists in `(0, p)`.
* The discussion of the duality between Wyner–Ziv and Gelfand–Pinsker on pages 12-28 and 12-29.

## Issues in the notes

* **Page 12-19.** `g` is decreasing, so `g'(D'_c) < 0`, and the formulas `(p - D) g'(D'_c)` and
  `g(D'_c) / (p - D'_c) = g'(D'_c)` lack a sign: they should have `-g'(D'_c)`, as in
  `IsDsbsTangency` and `wzRD_dsbs_of_tangency_le`.
* **Page 12-19.** "`R_SI-D(D) < R_SI-ED(D)`" is the wrong way round, as page 12-17 says: the
  statement is `R_SI-ED(D) < R_SI-D(D)` for `0 < D < p`, which is `bothRD_lt_wzRD_dsbs`.
* **Pages 12-36 and 12-37, Lemma 1.** Step (b) says that, given `L = l`, any collection of the other
  codewords has the same distribution. With the encoder of page 12-22, which selects the smallest
  index, this is not so: the codewords with an index below `l` are known not to be typical with
  `Xⁿ`, and the others are not. The step holds for an encoder that picks a typical index uniformly
  at random. We avoid the lemma by binning at random, independently of the codebook
  (`sum_bins_erase_le`).
* **Page 12-28.** The second capacity is written `R_SI-E`; it should be `C_SI-E`.
* **Page 12-31.** The minimum is written over `x̂₂(u, y)` and then described over `x̂₂(u, x̂₁, y)`.
* **The converse on page 12-12.** Step (a) uses a Markov chain, which `CausalCode.exists_kernel_le`
  avoids with `Uᵢ = (M, Zⁱ⁻¹)` and `Zᵢ = (Xᵢ, Yᵢ)`: the chain rule for `Zⁿ` bounds `∑ᵢ I(Xᵢ; Uᵢ)`.
  This is not an error in the notes.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 12
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory.ElGamalKim

/-! ## Aliases -/

section Aliases

variable {α γ β : Type*} [Fintype α] [Fintype γ] {P : α × γ → ℝ} {d : α → β → ℝ}

/-- **Theorem 1 of Lecture 12, page 12-6.** -/
theorem theorem_12_1 [Finite β] [Nonempty β] (hP : IsPMF P) (hd : ∀ x y, 0 ≤ d x y) {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) : rateCausalBits P d D = causalRD P d D / log 2 :=
  rateCausalBits_eq hP hd hD

/-- **Theorem 2 of Lecture 12, page 12-13.** -/
theorem theorem_12_2 (hP : IsPMF P) :
    sInf {R | IsLosslessCausalBits P R} = losslessCausalRate P / log 2 :=
  losslessCausalBits_eq hP

/-- **The Wyner–Ziv theorem of Lecture 12, page 12-17.** -/
theorem wyner_ziv_theorem [Finite β] [Nonempty β] (hP : IsPMF P) (hd : ∀ x y, 0 ≤ d x y) {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) : rateWZBits P d D = wzRD P d D / log 2 :=
  rateWZBits_eq hP hd hD

end Aliases

/-! ## The lossless cases at `D = 0` -/

section ZeroDistortion

variable {α γ : Type*} [Fintype α] [Fintype γ] {P : α × γ → ℝ}

/-- **Lecture 12, page 12-3.** With side information at the encoder only, the rate–distortion
function at `D = 0` for the Hamming distortion is `H(X)`, in bits. -/
theorem rateEncSideBits_hamming_zero (hP : IsPMF P) :
    rateEncSideBits P (hammingDistortion (α := α)) 0 = entropy (margFst P) / log 2 := by
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α := ⟨z.1⟩
  rw [rateEncSideBits_eq hP hammingDistortion_nonneg (minDistortion_hammingDistortion _).le,
    infoRD_hammingDistortion_zero (hP.dist _)]

/-- **Lecture 12, page 12-3.** With side information at both ends, the rate–distortion function at
`D = 0` for the Hamming distortion is `H(X | Y)`, in bits. -/
theorem rateBothBits_hamming_zero (hP : IsPMF P) :
    rateBothBits P (hammingDistortion (α := α)) 0 = H[Prod.fst | Prod.snd ; P] / log 2 := by
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α := ⟨z.1⟩
  rw [rateBothBits_eq hP hammingDistortion_nonneg (minDistortion_hammingDistortion _).le,
    bothRD_hamming_zero hP]

end ZeroDistortion

/-! ## The lossless examples of page 12-13 -/

section Lossless

variable {α γ : Type*} [Fintype α] [Fintype γ]

/-- **Example 1, page 12-13.** If `X = Y`, then `R*_CSI-D = H(X | Y) = 0`. -/
theorem losslessCausalRate_diag {p : α → ℝ} (hp : IsPMF p) :
    losslessCausalRate (dist p fun a => (a, a)) = 0 := by
  classical
  set P := dist p fun a => (a, a) with hPd
  have hP : IsPMF P := hp.dist _
  refine le_antisymm ?_ ?_
  · rw [losslessCausalRate_eq hP]
    have hq : IsChannel fun (_ : α) (_ : Unit) => (1 : ℝ) := fun _ =>
      ⟨fun _ => zero_le_one, by simp⟩
    have hc := (sideCost_hamming_le_zero_iff hP hq fun _ y => y).2 fun z hz => by
      have h1 : P z.1 ≠ 0 := fun h => hz (by simp [siLaw, jointOf, h])
      by_contra hne
      refine h1 (dist_eq_zero_of_forall_ne _ fun a ha => ?_)
      have h2 := Prod.mk.inj ha
      exact hne (by rw [← h2.1, ← h2.2])
    refine (sideRD_le hP hq 0 _ hc).trans (le_of_eq ?_)
    have hμ := siLaw_isPMF hP hq
    rw [sideRate, zero_mul, sub_zero, mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
    have h1 := entropyRV_le_log_card hμ (Prod.snd : (α × α) × Unit → Unit)
    simp only [Fintype.card_unit, Nat.cast_one, log_one] at h1
    have h2 := condEntropy_nonneg hμ (Prod.snd : (α × α) × Unit → Unit) fun z => z.1.1
    have h3 := condEntropy_le_entropy hμ (Prod.snd : (α × α) × Unit → Unit) fun z => z.1.1
    linarith
  · rw [losslessCausalRate_eq hP]
    exact sideRD_nonneg hP zero_le_one _ _

/-- **Example 2, page 12-13.** If `X` and `Y` are independent, then `R*_CSI-D = H(X | Y) = H(X)`. -/
theorem losslessCausalRate_prod {p : α → ℝ} {r : γ → ℝ} (hp : IsPMF p) (hr : IsPMF r) :
    losslessCausalRate (prodDist p r) = entropy p := by
  have hP := hp.prodDist hr
  have hX : dist (prodDist p r) Prod.fst = p := dist_prodDist_fst hr p
  have hY : dist (prodDist p r) Prod.snd = r := dist_prodDist_snd hp r
  have hle := losslessCausalRate_le_entropy hP
  have hge := condEntropy_le_losslessCausalRate hP
  have hind : IndepRV (prodDist p r) Prod.fst Prod.snd := fun a b => by
    rw [dist_pair_fst_snd, hX, hY]
    rfl
  rw [(condEntropy_eq_entropy_iff hP _ _).2 hind, entropyRV, hX] at hge
  have hle' : losslessCausalRate (prodDist p r) ≤ entropy p := by
    have e : entropy (margFst (prodDist p r)) = entropy p := congrArg entropy hX
    rwa [e] at hle
  exact le_antisymm hle' hge

/-- **Example 3, page 12-13.** If `X = (Y, Z)` with `Y` and `Z` independent, then
`R*_CSI-D = H(X | Y) = H(Z)`: the encoder describes `Z`. -/
theorem losslessCausalRate_pair {ζ : Type*} [Fintype ζ] {r : γ → ℝ} {s : ζ → ℝ} (hr : IsPMF r)
    (hs : IsPMF s) :
    losslessCausalRate (dist (prodDist r s) fun w => (w, w.1)) = entropy s := by
  classical
  have hμ := hr.prodDist hs
  set μ := prodDist r s with hμd
  set P := dist μ fun w : γ × ζ => (w, w.1) with hPd
  have hP : IsPMF P := hμ.dist _
  have hmarg : margFst P = μ := by
    have h := dist_comp_eq μ (fun w : γ × ζ => (w, w.1)) Prod.fst
    rw [show (Prod.fst ∘ fun w : γ × ζ => (w, w.1)) = id from rfl, dist_id] at h
    exact h.symm
  refine le_antisymm ?_ ?_
  · -- The auxiliary random variable `U = Z`.
    set q : γ × ζ → ζ → ℝ := fun w u => if u = w.2 then 1 else 0 with hq'
    have hq : IsChannel q := fun w => by
      refine ⟨fun u => by simp only [hq']; split_ifs <;> norm_num, ?_⟩
      simp [hq']
    have hf : ∀ z : ((γ × ζ) × γ) × ζ, siLaw P q z ≠ 0 →
        (fun (u : ζ) (y : γ) => (y, u)) z.2 z.1.2 = z.1.1 := fun z hz => by
      have h1 : P z.1 ≠ 0 := fun h => hz (by simp [siLaw, jointOf, h])
      have h2 : q z.1.1 z.2 ≠ 0 := fun h => hz (by simp [siLaw, jointOf, h])
      have h3 : z.2 = z.1.1.2 := by
        by_contra hne
        exact h2 (by simp [hq', hne])
      have h4 : z.1.2 = z.1.1.1 := by
        by_contra hne
        refine h1 (dist_eq_zero_of_forall_ne _ fun w hw => hne ?_)
        have := Prod.mk.inj hw
        rw [← this.2, ← this.1]
      exact Prod.ext h4 h3
    rw [losslessCausalRate_eq hP]
    refine (sideRD_le hP hq 0 (fun u y => (y, u))
      ((sideCost_hamming_le_zero_iff hP hq fun u y => (y, u)).2 hf)).trans ?_
    have hL := siLaw_isPMF hP hq
    have hU : dist (siLaw P q) Prod.snd = s := by
      funext u
      rw [← sum_dist_pair_right (siLaw P q) Prod.snd (fun z : ((γ × ζ) × γ) × ζ => z.1.1) u]
      simp only [dist_siLaw_UX, hmarg, hμd, hq', Fintype.sum_prod_type, prodDist, mul_ite, mul_one,
        mul_zero]
      rw [sum_congr rfl fun y _ => sum_ite_eq univ u fun z => r y * s z]
      simp only [mem_univ, ite_true, ← sum_mul, hr.sum_eq_one, one_mul]
    rw [sideRate, zero_mul, sub_zero, mutualInfo_comm hL, mutualInfo_eq_entropy_sub_condEntropy hL,
      entropyRV, hU]
    linarith [condEntropy_nonneg hL (Prod.snd : ((γ × ζ) × γ) × ζ → ζ) fun z => z.1.1]
  · refine le_trans (le_of_eq ?_) (condEntropy_le_losslessCausalRate hP)
    have e1 : H[pair Prod.snd Prod.fst ; P] = entropy μ := by
      rw [entropyRV, ← dist_comp_eq]
      have e : H[(pair Prod.snd Prod.fst) ∘ fun w : γ × ζ => (w, w.1) ; μ] = H[id ; μ] := by
        refine entropyRV_eq_of_injective μ (fun w : γ × ζ => (w.1, w)) ?_ fun _ => rfl
        intro a b h
        exact (Prod.mk.inj h).2
      have e3 : H[id ; μ] = entropy μ := by rw [entropyRV, dist_id]
      exact e.trans e3
    have e2 : H[Prod.snd ; P] = entropy r := by
      rw [entropyRV, ← dist_comp_eq]
      exact congrArg entropy (dist_prodDist_fst hs r)
    rw [condEntropy_eq_sub hP, e1, e2, hμd, entropy_prodDist hr hs]
    ring

end Lossless

/-! ## The quadratic Gaussian case -/

section Gaussian

variable {P N D : ℝ}

/-- **Lecture 12, page 12-18.** `P' = Var(X | Y) = P N / (P + N)`, the inverse of the sum of the
precisions of `X` and of `Y` given `X`, for `Y = X + Z`. -/
theorem gaussian_condVar (hP : 0 < P) (hN : 0 < N) : (P⁻¹ + N⁻¹)⁻¹ = P * N / (P + N) := by
  field_simp
  ring

/-- **Lecture 12, pages 12-18 and 12-19.** With `Q = P' D / (P' - D)` and `U = X + V`, for
`V ∼ N(0, Q)`, we have `Var(X | U, Y) = (1 / P' + 1 / Q)⁻¹ = D`. -/
theorem gaussian_condVar_U {P' : ℝ} (hD0 : 0 < D) (hD : D < P') :
    (P'⁻¹ + (P' * D / (P' - D))⁻¹)⁻¹ = D := by
  have hP' : 0 < P' := hD0.trans hD
  have h : P' - D ≠ 0 := (sub_pos.2 hD).ne'
  have h2 : P'⁻¹ + (P' * D / (P' - D))⁻¹ = D⁻¹ := by
    field_simp
    ring
  rw [h2, inv_inv]

/-- **Lecture 12, page 12-19.** The estimate `X̂ = a Y + b U`, with `a = D / N` and `b = D / Q`, of
`X` from `Y = X + Z` and `U = X + V` has `E (X - X̂)² = D`, for `1 / P + 1 / N + 1 / Q = 1 / D`. -/
theorem gaussian_estimate {Q : ℝ} (hP : 0 < P) (hN : 0 < N) (hQ : 0 < Q) (hD0 : 0 < D)
    (h : P⁻¹ + N⁻¹ + Q⁻¹ = D⁻¹) :
    (1 - D / N - D / Q) ^ 2 * P + (D / N) ^ 2 * N + (D / Q) ^ 2 * Q = D := by
  have h1 : 1 - D / N - D / Q = D / P := by
    have : D * (P⁻¹ + N⁻¹ + Q⁻¹) = 1 := by
      rw [h]
      field_simp
    field_simp at this ⊢
    linarith
  rw [h1]
  have : D * (P⁻¹ + N⁻¹ + Q⁻¹) = 1 := by
    rw [h]
    field_simp
  field_simp at this ⊢
  nlinarith

/-- **Lecture 12, page 12-18.** The rate of the quadratic Gaussian case: `h(X | Y) - h(X | U, Y)`
with `Var(X | Y) = P'` and `Var(X | U, Y) = D` is `R(P' / D) = (1 / 2) log (P' / D)`. -/
theorem gaussian_rate {P' : ℝ} (hP' : 0 < P') (hD0 : 0 < D) :
    1 / 2 * log (2 * π * rexp 1 * P') - 1 / 2 * log (2 * π * rexp 1 * D) =
      1 / 2 * log (P' / D) := by
  have hc : (0 : ℝ) < 2 * π * rexp 1 := by positivity
  rw [log_mul hc.ne' hP'.ne', log_mul hc.ne' hD0.ne', log_div hP'.ne' hD0.ne']
  ring

end Gaussian

end InfoTheory.ElGamalKim
