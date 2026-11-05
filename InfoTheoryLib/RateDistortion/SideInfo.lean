/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.SupportLemma
public import InfoTheoryLib.MutualInformation.Conditional
public import InfoTheoryLib.RateDistortion.BitRate
public import InfoTheoryLib.StateChannel.GPDerandomize

/-!
# Rate distortion functions with side information at the decoder

Let `(X, Y) ∼ p(x, y)` and let `d(x, x̂)` be a distortion measure. Lecture 12 of the notes of El
Gamal and Kim has two single-letter formulas, over `p(u | x)` and `x̂(u, y)` with `E d(X, X̂) ≤ D`:

  `R_CSI-D(D) = min I(X; U)`,  `R_SI-D(D) = min (I(X; U) - I(Y; U)) = min I(X; U | Y)`,

for side information available causally and noncausally at the decoder. We treat them together as
`min (I(X; U) - θ I(Y; U))`, with `θ = 0` and `θ = 1` respectively: all the properties below hold
for both of them with the same proof.

## Main definitions

* `siLaw P q`: the law `p(x, y) p(u | x)` of `((X, Y), U)`.
* `sideRate θ P q`: `I(X; U) - θ I(Y; U)`, in nats.
* `sideCost P q c`: `E c(U, X, Y)`, and in particular the distortion with `c = d(x, x̂(u, y))`.
* `sideRD θ P d D`: `min (I(X; U) - θ I(Y; U))`, with `U` on `Fin k` for some `k`.
* `causalRD P d D`, `wzRD P d D`: the rate–distortion functions for `θ = 0` and `θ = 1`.

## Main statements

* `sideRate_one`: `I(X; U) - I(Y; U) = I(X; U | Y)`.
* `exists_side_reduce`: **the cardinality bound**, from the support lemma.
* `exists_sideRD_eq`: the minimum is attained, with `|𝒰| ≤ |𝒳| + 3`.
* `exists_le_of_forall_side`: the closedness of the set of the rates and distortions.
* `sideRD_antitoneOn`, `sideRD_convexOn`: the function is nonincreasing and convex in `D`.

## Implementation notes

The notes state the bound `|𝒰| ≤ |𝒳| + 1`, which uses the Fenchel–Eggleston strengthening of
Carathéodory's theorem. We prove `|𝒰| ≤ |𝒳| + 3` from Carathéodory's theorem: any finite bound gives
the compactness needed to attain the minimum and to pass to the limit in the converse, without the
continuity of the function that the notes use.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 12
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α γ β υ : Type*} [Fintype α] [Fintype γ] [Fintype υ]

/-! ### The law of `((X, Y), U)` -/

/-- **Lecture 12 of [elgamal2010], page 12-6.** The law `p(x, y) p(u | x)` of `((X, Y), U)`. -/
def siLaw (P : α × γ → ℝ) (q : α → υ → ℝ) : (α × γ) × υ → ℝ := jointOf P fun z => q z.1

/-- `I(X; U) - θ I(Y; U)` under the law `p(x, y) p(u | x)`, in nats. -/
def sideRate (θ : ℝ) (P : α × γ → ℝ) (q : α → υ → ℝ) : ℝ :=
  I[fun z : (α × γ) × υ => z.1.1 : Prod.snd ; siLaw P q] -
    θ * I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q]

/-- `E c(U, X, Y)` under the law `p(x, y) p(u | x)`. -/
def sideCost (P : α × γ → ℝ) (q : α → υ → ℝ) (c : υ → α → γ → ℝ) : ℝ :=
  ∑ z, siLaw P q z * c z.2 z.1.1 z.1.2

/-- **Lecture 12 of [elgamal2010], pages 12-6 and 12-17.** `min (I(X; U) - θ I(Y; U))` over
`p(u | x)` and `x̂(u, y)` with `E d(X, X̂) ≤ D`, with `U` on `Fin k` for some `k`, in nats. -/
def sideRD (θ : ℝ) (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
    sideCost P q (fun u x y => d x (f u y)) ≤ D ∧ sideRate θ P q = I}

/-- **Theorem 1 of Lecture 12 of [elgamal2010], page 12-6.** `R_CSI-D(D) = min I(X; U)`, in nats. -/
def causalRD (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ := sideRD 0 P d D

/-- **The Wyner–Ziv theorem (Lecture 12 of [elgamal2010], page 12-17).**
`R_SI-D(D) = min (I(X; U) - I(Y; U))`, in nats. -/
def wzRD (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ := sideRD 1 P d D

variable {P : α × γ → ℝ} {q : α → υ → ℝ}

lemma siLaw_isPMF (hP : IsPMF P) (hq : IsChannel q) : IsPMF (siLaw P q) :=
  jointOf_isPMF hP fun z => hq z.1

omit [Fintype υ] in
/-- `p(x) = ∑_y p(x, y)`. -/
lemma margFst_apply (P : α × γ → ℝ) (x : α) : margFst P x = ∑ y, P (x, y) := dist_fst P x

/-- The law of `(U, X)`. -/
lemma dist_siLaw_UX (P : α × γ → ℝ) (q : α → υ → ℝ) (u : υ) (x : α) :
    dist (siLaw P q) (pair Prod.snd fun z : (α × γ) × υ => z.1.1) (u, x) =
      margFst P x * q x u := by
  classical
  rw [margFst_apply]
  simp only [dist, siLaw, jointOf, pair, Prod.mk.injEq]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_mul, sum_eq_single x]
  · refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single u]
    · simp
    · intro u' _ hu
      simp [hu]
    · simp
  · intro x' _ hx
    refine sum_eq_zero fun y _ => sum_eq_zero fun u' _ => ?_
    simp [hx]
  · simp

/-- The law of `(U, Y)`. -/
lemma dist_siLaw_UY (P : α × γ → ℝ) (q : α → υ → ℝ) (u : υ) (y : γ) :
    dist (siLaw P q) (pair Prod.snd fun z : (α × γ) × υ => z.1.2) (u, y) =
      ∑ x, P (x, y) * q x u := by
  classical
  simp only [dist, siLaw, jointOf, pair, Prod.mk.injEq]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single y]
  · rw [sum_eq_single u]
    · simp
    · intro u' _ hu
      simp [hu]
    · simp
  · intro y' _ hy
    refine sum_eq_zero fun u' _ => ?_
    simp [hy]
  · simp

/-- The law of `X`. -/
lemma dist_siLaw_X (hq : IsChannel q) :
    dist (siLaw P q) (fun z : (α × γ) × υ => z.1.1) = margFst P := by
  classical
  funext x
  rw [← sum_dist_pair_left (siLaw P q) Prod.snd (fun z : (α × γ) × υ => z.1.1) x]
  simp only [dist_siLaw_UX, ← mul_sum, (hq x).sum_eq_one, mul_one]

/-- The law of `Y`. -/
lemma dist_siLaw_Y (hq : IsChannel q) :
    dist (siLaw P q) (fun z : (α × γ) × υ => z.1.2) = margSnd P := by
  classical
  funext y
  rw [← sum_dist_pair_left (siLaw P q) Prod.snd (fun z : (α × γ) × υ => z.1.2) y]
  simp only [dist_siLaw_UY]
  rw [sum_comm, show margSnd P y = ∑ x, P (x, y) from dist_snd P y]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_sum, (hq x).sum_eq_one, mul_one]

/-- The law of `(X, Y)`. -/
lemma dist_siLaw_fst (hq : IsChannel q) : dist (siLaw P q) Prod.fst = P :=
  dist_jointOf_fst fun z => hq z.1

/-- `H(U | X, Y) = H(U | X)`: the Markov chain `U → X → Y`. -/
lemma condEntropy_U_XY (hP : IsPMF P) (hq : IsChannel q) :
    H[Prod.snd | Prod.fst ; siLaw P q] =
      H[Prod.snd | fun z : (α × γ) × υ => z.1.1 ; siLaw P q] := by
  classical
  have hp : IsPMF (margFst P) := hP.dist _
  have hμ := siLaw_isPMF hP hq
  have h1 : H[Prod.snd | Prod.fst ; siLaw P q] = ∑ z, P z * entropy (q z.1) :=
    condEntropy_jointOf hP fun z => hq z.1
  have h2 : H[Prod.snd | fun z : (α × γ) × υ => z.1.1 ; siLaw P q] =
      ∑ x, margFst P x * entropy (q x) := by
    rw [← condEntropy_jointOf hp hq]
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hp hq) ?_
    rw [dist_pair_fst_snd]
    funext ⟨x, u⟩
    rw [dist_pair_swap, dist_siLaw_UX]
    rfl
  rw [h1, h2, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [margFst_apply, sum_mul]

/-- **Lecture 12 of [elgamal2010], page 12-17.** `I(X; U) - I(Y; U) = I(X; U | Y)`. -/
theorem sideRate_one (hP : IsPMF P) (hq : IsChannel q) :
    sideRate 1 P q = I[fun z : (α × γ) × υ => z.1.1 : Prod.snd | fun z => z.1.2 ; siLaw P q] := by
  classical
  have hμ := siLaw_isPMF hP hq
  rw [sideRate, one_mul, condMutualInfo_comm hμ, condMutualInfo_eq' hμ,
    mutualInfo_comm hμ (fun z : (α × γ) × υ => z.1.1),
    mutualInfo_comm hμ (fun z : (α × γ) × υ => z.1.2),
    mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
  have e : H[Prod.snd | pair (fun z : (α × γ) × υ => z.1.2) fun z => z.1.1 ; siLaw P q] =
      H[Prod.snd | Prod.fst ; siLaw P q] := by
    refine condEntropy_congr_right hμ Prod.snd Prod.swap Prod.swap_injective fun _ => rfl
  rw [e, condEntropy_U_XY hP hq]
  ring

/-- `I(Y; U) ≤ I(X; U)`, by the Markov chain `U → X → Y`. -/
lemma mutualInfo_Y_U_le (hP : IsPMF P) (hq : IsChannel q) :
    I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q] ≤
      I[fun z : (α × γ) × υ => z.1.1 : Prod.snd ; siLaw P q] := by
  have h := sideRate_one hP hq
  have h0 : 0 ≤ I[fun z : (α × γ) × υ => z.1.1 : Prod.snd | fun z => z.1.2 ; siLaw P q] :=
    condMutualInfo_nonneg (siLaw_isPMF hP hq) _ _ _
  rw [← h, sideRate] at h0
  linarith

/-- `I(X; U) - θ I(Y; U) ≥ 0` for `θ ≤ 1`. -/
lemma sideRate_nonneg (hP : IsPMF P) (hq : IsChannel q) {θ : ℝ} (hθ1 : θ ≤ 1) :
    0 ≤ sideRate θ P q := by
  have h1 := mutualInfo_Y_U_le hP hq
  have h2 : 0 ≤ I[fun z : (α × γ) × υ => z.1.2 : Prod.snd ; siLaw P q] :=
    mutualInfo_nonneg (siLaw_isPMF hP hq) _ _
  rw [sideRate]
  nlinarith [mul_nonneg (sub_nonneg.2 hθ1) h2]

/-! ### The representation by the posterior laws -/

section Rep

variable {W : α → γ → ℝ} {w : υ → ℝ} {r : υ → α → ℝ}

/-- `H(r) - θ H(Y)`, for `X ∼ r` and `Y` the output of `W`. -/
def sideF (θ : ℝ) (W : α → γ → ℝ) (r : α → ℝ) : ℝ := entropy r - θ * entropy (outDist r W)

/-- `E c(X, Y)`, for `X ∼ r` and `Y` the output of `W`. -/
def sideG (W : α → γ → ℝ) (c : α → γ → ℝ) (r : α → ℝ) : ℝ := ∑ x, r x * ∑ y, W x y * c x y

/-- If `p(x) p(u | x) = w(u) r(x | u)`, then `w` is a pmf. -/
lemma isPMF_of_rep (hP : IsPMF P) (hq : IsChannel q) (hw : ∀ u, 0 ≤ w u) (hr : ∀ u, IsPMF (r u))
    (hrep : ∀ x u, margFst P x * q x u = w u * r u x) : IsPMF w := by
  refine ⟨hw, ?_⟩
  have h : ∑ u, w u = ∑ u, ∑ x, w u * r u x := sum_congr rfl fun u _ => by
    rw [← mul_sum, (hr u).sum_eq_one, mul_one]
  rw [h, sum_comm]
  simp only [← hrep, ← mul_sum, (hq _).sum_eq_one, mul_one]
  exact (hP.dist _).sum_eq_one

/-- **The rates in terms of the posterior laws.** If `p(x, y) = p(x) W(y | x)` and
`p(x) p(u | x) = w(u) r(x | u)`, then `I(X; U) - θ I(Y; U)` is
`H(X) - θ H(Y) - ∑ᵤ w(u) (H(X | U = u) - θ H(Y | U = u))`. -/
theorem sideRate_eq_of_rep (hP : IsPMF P) (hq : IsChannel q) (hW : IsChannel W)
    (hPW : ∀ x y, P (x, y) = margFst P x * W x y) (hw : ∀ u, 0 ≤ w u) (hr : ∀ u, IsPMF (r u))
    (hrep : ∀ x u, margFst P x * q x u = w u * r u x) (θ : ℝ) :
    sideRate θ P q = entropy (margFst P) - θ * entropy (margSnd P) -
      ∑ u, w u * sideF θ W (r u) := by
  classical
  have hμ := siLaw_isPMF hP hq
  have hwP := isPMF_of_rep hP hq hw hr hrep
  -- `H(X | U)`.
  have hX : H[fun z : (α × γ) × υ => z.1.1 | Prod.snd ; siLaw P q] = ∑ u, w u * entropy (r u) := by
    rw [← condEntropy_jointOf hwP hr]
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hwP hr) ?_
    rw [dist_pair_fst_snd]
    funext ⟨u, x⟩
    rw [dist_siLaw_UX, hrep]
    rfl
  -- `H(Y | U)`.
  have hC : ∀ u, IsPMF (outDist (r u) W) := fun u => outDist_isPMF (hr u) hW
  have hY : H[fun z : (α × γ) × υ => z.1.2 | Prod.snd ; siLaw P q] =
      ∑ u, w u * entropy (outDist (r u) W) := by
    rw [← condEntropy_jointOf hwP hC]
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hwP hC) ?_
    rw [dist_pair_fst_snd]
    funext ⟨u, y⟩
    rw [dist_siLaw_UY]
    simp only [jointOf, outDist, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [hPW]
    have := hrep x u
    linear_combination W x y * this
  rw [sideRate, mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_eq_entropy_sub_condEntropy hμ,
    hX, hY, entropyRV, entropyRV, dist_siLaw_X hq, dist_siLaw_Y hq]
  simp only [sideF, mul_sub, sum_sub_distrib]
  rw [show ∑ u, w u * (θ * entropy (outDist (r u) W)) =
    θ * ∑ u, w u * entropy (outDist (r u) W) from by
      rw [mul_sum]
      exact sum_congr rfl fun u _ => by ring]
  ring

/-- **The cost in terms of the posterior laws.** -/
theorem sideCost_eq_of_rep (hPW : ∀ x y, P (x, y) = margFst P x * W x y)
    (hrep : ∀ x u, margFst P x * q x u = w u * r u x) (c : υ → α → γ → ℝ) :
    sideCost P q c = ∑ u, w u * sideG W (c u) (r u) := by
  have e : sideCost P q c = ∑ x, ∑ y, ∑ u, P (x, y) * q x u * c u x y := by
    simp only [sideCost, Fintype.sum_prod_type, siLaw, jointOf]
  simp only [sideG, mul_sum]
  rw [e, sum_comm (s := univ (α := υ)) (t := univ (α := α))]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun u _ => sum_congr rfl fun y _ => ?_
  rw [hPW]
  linear_combination (W x y * c u x y) * hrep x u

/-- Every `p(x, y)` is `p(x) W(y | x)`. -/
lemma exists_side_channel (hP : IsPMF P) :
    ∃ W : α → γ → ℝ, IsChannel W ∧ ∀ x y, P (x, y) = margFst P x * W x y := by
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty γ := ⟨z.2⟩
  exact exists_kernel hP

/-- Every `p(x) p(u | x)` is `w(u) r(x | u)`. -/
lemma exists_side_rep (hP : IsPMF P) (hq : IsChannel q) :
    ∃ (w : υ → ℝ) (r : υ → α → ℝ), (∀ u, 0 ≤ w u) ∧ (∀ u, IsPMF (r u)) ∧
      ∀ x u, margFst P x * q x u = w u * r u x := by
  classical
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α := ⟨z.1⟩
  have hJ : IsPMF (fun z : υ × α => margFst P z.2 * q z.2 z.1) := by
    have h := (siLaw_isPMF hP hq).dist (pair Prod.snd fun z : (α × γ) × υ => z.1.1)
    convert h using 1
    funext ⟨u, x⟩
    exact (dist_siLaw_UX P q u x).symm
  obtain ⟨r, hr, hk⟩ := exists_kernel hJ
  exact ⟨_, r, (hJ.dist _).nonneg, hr, fun x u => hk u x⟩

end Rep

/-! ### The cardinality bound -/

section Reduce

variable {κ : Type*} [Fintype κ]

/-- **The cardinality bound (Lecture 12, pages 12-6 and 12-17, and Appendix C).** The rate and any
finite family of costs of `p(u | x)` are those of a `p(u' | x)` with `|𝒰'| = |𝒳| + |κ| + 2`, by the
support lemma: they are the mean under `p(u)` of functions of the posterior law `p(x | u)`, together
with `p(x)` itself. -/
theorem exists_side_reduce (hP : IsPMF P) (hq : IsChannel q) (θ : ℝ) (c : κ → υ → α → γ → ℝ) {N : ℕ}
    (hN : N = Fintype.card α + Fintype.card κ + 2) :
    ∃ (q' : α → Fin N → ℝ) (g : Fin N → υ), IsChannel q' ∧ sideRate θ P q' = sideRate θ P q ∧
      ∀ i, sideCost P q' (fun j => c i (g j)) = sideCost P q (c i) := by
  classical
  obtain ⟨W, hW, hPW⟩ := exists_side_channel hP
  obtain ⟨w, r, hw, hr, hrep⟩ := exists_side_rep hP hq
  have hwP := isPMF_of_rep hP hq hw hr hrep
  set v : υ → (α → ℝ) × ℝ × (κ → ℝ) := fun u =>
    (r u, sideF θ W (r u), fun i => sideG W (c i u) (r u))
  have hdim : N = Module.finrank ℝ ((α → ℝ) × ℝ × (κ → ℝ)) + 1 := by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_self, hN]
    omega
  subst hdim
  obtain ⟨g, w', hw0, hw1, hsum⟩ := exists_fin_mean_eq hw hwP.sum_eq_one v
  have key : ∀ L : ((α → ℝ) × ℝ × (κ → ℝ)) →ₗ[ℝ] ℝ,
      ∑ j, w' j * L (v (g j)) = ∑ u, w u * L (v u) := fun L => by
    have e := congrArg L hsum
    simpa only [map_sum, map_smul, smul_eq_mul] using e
  have h1 : ∀ x, ∑ j, w' j * r (g j) x = margFst P x := fun x => by
    have e : ∑ j, w' j * r (g j) x = ∑ u, w u * r u x :=
      key ((LinearMap.proj x).comp (LinearMap.fst ℝ (α → ℝ) (ℝ × (κ → ℝ))))
    rw [e, ← mul_one (margFst P x), ← (hq x).sum_eq_one, mul_sum]
    exact (sum_congr rfl fun u _ => hrep x u).symm
  have h2 : ∑ j, w' j * sideF θ W (r (g j)) = ∑ u, w u * sideF θ W (r u) :=
    key ((LinearMap.fst ℝ ℝ (κ → ℝ)).comp (LinearMap.snd ℝ (α → ℝ) (ℝ × (κ → ℝ))))
  have h3 : ∀ i, ∑ j, w' j * sideG W (c i (g j)) (r (g j)) = ∑ u, w u * sideG W (c i u) (r u) :=
    fun i => key ((LinearMap.proj i).comp ((LinearMap.snd ℝ ℝ (κ → ℝ)).comp
      (LinearMap.snd ℝ (α → ℝ) (ℝ × (κ → ℝ)))))
  -- The new kernel.
  set q' : α → Fin _ → ℝ := fun x j =>
    if margFst P x = 0 then w' j else w' j * r (g j) x / margFst P x with hq'
  have hp0 : ∀ x, 0 ≤ margFst P x := (hP.dist _).nonneg
  have hq'P : IsChannel q' := fun x => by
    by_cases hx : margFst P x = 0
    · simp only [hq', hx, ite_true]
      exact ⟨hw0, hw1⟩
    · simp only [hq', hx, ite_false]
      refine ⟨fun j => div_nonneg (mul_nonneg (hw0 j) ((hr _).nonneg x)) (hp0 x), ?_⟩
      rw [← sum_div, h1, div_self hx]
  have hrep' : ∀ x j, margFst P x * q' x j = w' j * r (g j) x := fun x j => by
    by_cases hx : margFst P x = 0
    · have h0 : ∀ j ∈ univ, 0 ≤ w' j * r (g j) x := fun j _ =>
        mul_nonneg (hw0 j) ((hr _).nonneg x)
      have := (sum_eq_zero_iff_of_nonneg h0).1 ((h1 x).trans hx) j (mem_univ j)
      rw [this, hx, zero_mul]
    · simp only [hq', hx, ite_false]
      field_simp
  refine ⟨q', g, hq'P, ?_, fun i => ?_⟩
  · rw [sideRate_eq_of_rep hP hq'P hW hPW hw0 (fun j => hr (g j)) hrep' θ,
      sideRate_eq_of_rep hP hq hW hPW hw hr hrep θ, h2]
  · rw [sideCost_eq_of_rep hPW hrep', sideCost_eq_of_rep hPW hrep, h3]

/-- The cardinality bound for a distortion measure: `|𝒰'| = |𝒳| + 3`. -/
theorem exists_side_reduce₁ (hP : IsPMF P) (hq : IsChannel q) (θ : ℝ) (d : α → β → ℝ)
    (f : υ → γ → β) :
    ∃ (q' : α → Fin (Fintype.card α + 3) → ℝ) (f' : Fin (Fintype.card α + 3) → γ → β),
      IsChannel q' ∧ sideRate θ P q' = sideRate θ P q ∧
        sideCost P q' (fun u x y => d x (f' u y)) = sideCost P q (fun u x y => d x (f u y)) := by
  obtain ⟨q', g, hq', h1, h2⟩ := exists_side_reduce (κ := Unit) hP hq θ
    (fun _ u x y => d x (f u y)) (N := Fintype.card α + 3) (by simp only [Fintype.card_unit])
  exact ⟨q', fun j => f (g j), hq', h1, h2 ()⟩

end Reduce

/-! ### Compactness -/

section Compact

omit [Fintype υ] in
lemma continuous_sideCost [Fintype υ] (P : α × γ → ℝ) (c : υ → α → γ → ℝ) :
    Continuous fun q : α → υ → ℝ => sideCost P q c := by
  unfold sideCost siLaw jointOf
  fun_prop

/-- The entropies are continuous in `p(u | x)`. -/
lemma continuous_entropyRV_siLaw {a : Type*} [Fintype a] (P : α × γ → ℝ)
    (A : (α × γ) × υ → a) : Continuous fun q : α → υ → ℝ => H[A ; siLaw P q] := by
  classical
  simp only [entropyRV, entropy_eq_sum_negMulLog]
  refine continuous_finsetSum _ fun v _ => continuous_negMulLog.comp ?_
  simp only [dist]
  refine continuous_finsetSum _ fun z _ => ?_
  split_ifs
  · simp only [siLaw, jointOf]
    fun_prop
  · exact continuous_const

/-- `I(X; U) - θ I(Y; U)` is continuous in `p(u | x)`. -/
lemma continuousOn_sideRate (hP : IsPMF P) (θ : ℝ) :
    ContinuousOn (fun q : α → υ → ℝ => sideRate θ P q) {q | IsChannel q} := by
  have hc : Continuous fun q : α → υ → ℝ =>
      (H[fun z : (α × γ) × υ => z.1.1 ; siLaw P q] + H[Prod.snd ; siLaw P q] -
        H[pair (fun z : (α × γ) × υ => z.1.1) Prod.snd ; siLaw P q]) -
      θ * (H[fun z : (α × γ) × υ => z.1.2 ; siLaw P q] + H[Prod.snd ; siLaw P q] -
        H[pair (fun z : (α × γ) × υ => z.1.2) Prod.snd ; siLaw P q]) := by
    refine ((((continuous_entropyRV_siLaw P _).add (continuous_entropyRV_siLaw P _)).sub
      (continuous_entropyRV_siLaw P _))).sub (continuous_const.mul
      (((continuous_entropyRV_siLaw P _).add (continuous_entropyRV_siLaw P _)).sub
      (continuous_entropyRV_siLaw P _)))
  refine hc.continuousOn.congr fun q hq => ?_
  have hμ := siLaw_isPMF hP (show IsChannel q from hq)
  simp only [sideRate]
  rw [mutualInfo_eq_add_sub hμ, mutualInfo_eq_add_sub hμ]

variable {N : ℕ}

/-- The set of the rates of `(q, f)` with `E d(X, X̂) ≤ D` is compact, for a fixed `f`. -/
lemma isCompact_side_rates (hP : IsPMF P) (θ : ℝ) (c : Fin N → α → γ → ℝ) (D : ℝ) :
    IsCompact ((fun q : α → Fin N → ℝ => sideRate θ P q) ''
      {q | IsChannel q ∧ sideCost P q c ≤ D}) := by
  have hS : IsCompact {q : α → Fin N → ℝ | IsChannel q ∧ sideCost P q c ≤ D} :=
    isCompact_setOf_isChannel.inter_right (isClosed_le (continuous_sideCost P c) continuous_const)
  exact hS.image_of_continuousOn ((continuousOn_sideRate hP θ).mono fun q hq => hq.1)

/-- The set of all the rates of `(q, f)` with `E d(X, X̂) ≤ D` is that for `|𝒰| = |𝒳| + 3`, which is
compact. -/
lemma sideRD_set_eq (hP : IsPMF P) (θ : ℝ) (d : α → β → ℝ) (D : ℝ) :
    {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ D ∧ sideRate θ P q = I} =
    ⋃ f : Fin (Fintype.card α + 3) → γ → β, (fun q : α → Fin (Fintype.card α + 3) → ℝ =>
      sideRate θ P q) '' {q | IsChannel q ∧ sideCost P q (fun u x y => d x (f u y)) ≤ D} := by
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨k, q, f, hq, hD, rfl⟩
    obtain ⟨q', f', hq', h1, h2⟩ := exists_side_reduce₁ hP hq θ d f
    exact ⟨f', q', ⟨hq', h2.le.trans hD⟩, h1⟩
  · rintro ⟨f, q, ⟨hq, hD⟩, rfl⟩
    exact ⟨_, q, f, hq, hD, rfl⟩

lemma isCompact_sideRD_set [Finite β] (hP : IsPMF P) (θ : ℝ) (d : α → β → ℝ) (D : ℝ) :
    IsCompact {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ D ∧ sideRate θ P q = I} := by
  rw [sideRD_set_eq hP]
  exact isCompact_iUnion fun f => isCompact_side_rates hP θ _ D

/-- `min (I(X; U) - θ I(Y; U)) ≤ I(X; U) - θ I(Y; U)` for every `p(u | x)` and `x̂(u, y)` with
`E d(X, X̂) ≤ D`, with `U` on any finite set. -/
theorem sideRD_le [Finite β] (hP : IsPMF P) (hq : IsChannel q) (θ : ℝ) {d : α → β → ℝ}
    (f : υ → γ → β) {D : ℝ}
    (hD : sideCost P q (fun u x y => d x (f u y)) ≤ D) : sideRD θ P d D ≤ sideRate θ P q := by
  obtain ⟨q', f', hq', h1, h2⟩ := exists_side_reduce₁ hP hq θ d f
  exact csInf_le (isCompact_sideRD_set hP θ d D).bddBelow ⟨_, q', f', hq', h2.le.trans hD, h1⟩

/-- A test channel `p(x̂ | x)` with `U = X̂` and `x̂(u, y) = u` has the distortion `E d(X, X̂)`. -/
lemma sideCost_test [Fintype β] (P : α × γ → ℝ) (q : α → β → ℝ) (d : α → β → ℝ) :
    sideCost P q (fun u x _ => d x u) = expDistortion (margFst P) q d := by
  rw [sideCost, Fintype.sum_prod_type, Fintype.sum_prod_type, expDistortion]
  refine sum_congr rfl fun x _ => ?_
  simp only [margFst_apply, siLaw, jointOf, sum_mul]
  rw [sum_comm]

/-- **(Lecture 12, pages 12-6 and 12-17.)** The minimum is attained, with `|𝒰| ≤ |𝒳| + 3`, for
`D ≥ D_min`. -/
theorem exists_sideRD_eq [Finite β] [Nonempty β] (hP : IsPMF P) (θ : ℝ) {d : α → β → ℝ} {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) :
    ∃ (q : α → Fin (Fintype.card α + 3) → ℝ) (f : Fin (Fintype.card α + 3) → γ → β),
      IsChannel q ∧ sideCost P q (fun u x y => d x (f u y)) ≤ D ∧
        sideRate θ P q = sideRD θ P d D := by
  have := Fintype.ofFinite β
  have hne : {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ D ∧ sideRate θ P q = I}.Nonempty := by
    obtain ⟨q₀, hq₀, he₀⟩ := exists_expDistortion_eq_minDistortion (margFst P) d
    obtain ⟨q', f', hq', -, h2⟩ := exists_side_reduce₁ hP hq₀ θ d fun u _ => u
    refine ⟨_, _, q', f', hq', ?_, rfl⟩
    rw [h2, sideCost_test, he₀]
    exact hD
  have hmem := (isCompact_sideRD_set hP θ d D).sInf_mem hne
  rw [sideRD_set_eq hP] at hmem
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨f, q, ⟨hq, hc⟩, he⟩ := hmem
  refine ⟨q, f, hq, hc, he.trans ?_⟩
  rw [sideRD, sideRD_set_eq hP]

/-- `min (I(X; U) - θ I(Y; U)) ≥ 0` for `θ ≤ 1`. -/
lemma sideRD_nonneg (hP : IsPMF P) {θ : ℝ} (hθ : θ ≤ 1) (d : α → β → ℝ) (D : ℝ) :
    0 ≤ sideRD θ P d D := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨k, q, f, hq, -, rfl⟩
  exact sideRate_nonneg hP hq hθ

/-- **The closedness of the rates and distortions.** If there are, for every `ε > 0`, `p(u | x)` and
`x̂(u, y)` on `Fin N` with `E d(X, X̂) ≤ D + ε` and `I(X; U) - θ I(Y; U) ≤ R`, then there are such
laws with `E d(X, X̂) ≤ D`. -/
theorem exists_le_of_forall_side [Finite β] (hP : IsPMF P) (θ : ℝ) {d : α → β → ℝ} {R D : ℝ}
    (h : ∀ ε > 0, ∃ (q : α → Fin N → ℝ) (f : Fin N → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ D + ε ∧ sideRate θ P q ≤ R) :
    ∃ (q : α → Fin N → ℝ) (f : Fin N → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ D ∧ sideRate θ P q ≤ R := by
  have hK : IsCompact {q : α → Fin N → ℝ | IsChannel q ∧ sideRate θ P q ≤ R} := by
    have hcl : IsClosed ({q : α → Fin N → ℝ | IsChannel q} ∩
        (fun q => sideRate θ P q) ⁻¹' Set.Iic R) :=
      (continuousOn_sideRate hP θ).preimage_isClosed_of_isClosed
        isCompact_setOf_isChannel.isClosed isClosed_Iic
    exact isCompact_setOf_isChannel.of_isClosed_subset hcl fun q hq => hq.1
  set C : Set ℝ := ⋃ f : Fin N → γ → β,
    (fun q : α → Fin N → ℝ => sideCost P q fun u x y => d x (f u y)) ''
      {q | IsChannel q ∧ sideRate θ P q ≤ R} with hC
  have hCc : IsCompact C := isCompact_iUnion fun f =>
    hK.image (continuous_sideCost P _)
  have hmemC : ∀ ε > 0, ∃ c ∈ C, c ≤ D + ε := fun ε hε => by
    obtain ⟨q, f, hq, hc, hr⟩ := h ε hε
    exact ⟨_, Set.mem_iUnion.2 ⟨f, q, ⟨hq, hr⟩, rfl⟩, hc⟩
  have hne : C.Nonempty :=
    let ⟨c, hc, _⟩ := hmemC 1 one_pos
    ⟨c, hc⟩
  have hmin := hCc.sInf_mem hne
  simp only [hC, Set.mem_iUnion, Set.mem_image] at hmin
  obtain ⟨f, q, ⟨hq, hr⟩, he⟩ := hmin
  refine ⟨q, f, hq, ?_, hr⟩
  rw [he]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨c, hc, hle⟩ := hmemC ε hε
  exact (csInf_le hCc.bddBelow hc).trans hle

end Compact

/-! ### Monotonicity and convexity -/

section Convex

variable {d : α → β → ℝ}

/-- **Lecture 12, pages 12-6 and 12-17.** The function is nonincreasing in `D ≥ D_min`. -/
theorem sideRD_antitoneOn [Finite β] [Nonempty β] (hP : IsPMF P) (θ : ℝ) :
    AntitoneOn (sideRD θ P d) (Set.Ici (minDistortion (margFst P) d)) := by
  intro D₁ hD₁ D₂ _ h
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq hP θ hD₁
  rw [← he]
  exact sideRD_le hP hq θ f (hc.trans h)

/-- **Time sharing.** The `p(u | x)` on the disjoint union of two alphabets that uses the kernels
`q₁` and `q₂` with probabilities `s` and `t`. -/
def sideMix {υ₁ υ₂ : Type*} (s t : ℝ) (q₁ : α → υ₁ → ℝ) (q₂ : α → υ₂ → ℝ) (x : α) :
    υ₁ ⊕ υ₂ → ℝ :=
  Sum.elim (fun u => s * q₁ x u) fun u => t * q₂ x u

variable {υ₁ υ₂ : Type*} [Fintype υ₁] [Fintype υ₂] {q₁ : α → υ₁ → ℝ} {q₂ : α → υ₂ → ℝ} {s t : ℝ}

omit [Fintype α] in
lemma sideMix_isChannel (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) : IsChannel (sideMix s t q₁ q₂) := fun x => by
  refine ⟨?_, ?_⟩
  · rintro (u | u)
    · exact mul_nonneg hs ((h₁ x).nonneg u)
    · exact mul_nonneg ht ((h₂ x).nonneg u)
  · simp only [Fintype.sum_sum_type, sideMix, Sum.elim_inl, Sum.elim_inr, ← mul_sum,
      (h₁ x).sum_eq_one, (h₂ x).sum_eq_one, mul_one, hst]

/-- **Time sharing.** The rate of the mixture of two kernels is the mixture of the rates. -/
theorem sideRate_sideMix (hP : IsPMF P) (h₁ : IsChannel q₁) (h₂ : IsChannel q₂) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : s + t = 1) (θ : ℝ) :
    sideRate θ P (sideMix s t q₁ q₂) = s * sideRate θ P q₁ + t * sideRate θ P q₂ := by
  obtain ⟨W, hW, hPW⟩ := exists_side_channel hP
  obtain ⟨w₁, r₁, hw₁, hr₁, hrep₁⟩ := exists_side_rep hP h₁
  obtain ⟨w₂, r₂, hw₂, hr₂, hrep₂⟩ := exists_side_rep hP h₂
  have hrep : ∀ x u, margFst P x * sideMix s t q₁ q₂ x u =
      Sum.elim (fun u => s * w₁ u) (fun u => t * w₂ u) u * Sum.elim r₁ r₂ u x := by
    rintro x (u | u)
    · simp only [sideMix, Sum.elim_inl]
      linear_combination s * hrep₁ x u
    · simp only [sideMix, Sum.elim_inr]
      linear_combination t * hrep₂ x u
  have hw : ∀ u, 0 ≤ Sum.elim (fun u => s * w₁ u) (fun u => t * w₂ u) u := by
    rintro (u | u)
    · exact mul_nonneg hs (hw₁ u)
    · exact mul_nonneg ht (hw₂ u)
  have hr : ∀ u, IsPMF (Sum.elim r₁ r₂ u) := by
    rintro (u | u)
    · exact hr₁ u
    · exact hr₂ u
  rw [sideRate_eq_of_rep hP (sideMix_isChannel h₁ h₂ hs ht hst) hW hPW hw hr hrep θ,
    sideRate_eq_of_rep hP h₁ hW hPW hw₁ hr₁ hrep₁ θ,
    sideRate_eq_of_rep hP h₂ hW hPW hw₂ hr₂ hrep₂ θ,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_assoc, ← mul_sum]
  have : t = 1 - s := by linarith
  subst this
  ring

/-- **Time sharing.** The cost of the mixture of two kernels is the mixture of the costs. -/
theorem sideCost_sideMix (P : α × γ → ℝ) (q₁ : α → υ₁ → ℝ) (q₂ : α → υ₂ → ℝ)
    (c₁ : υ₁ → α → γ → ℝ) (c₂ : υ₂ → α → γ → ℝ) :
    sideCost P (sideMix s t q₁ q₂) (Sum.elim c₁ c₂) =
      s * sideCost P q₁ c₁ + t * sideCost P q₂ c₂ := by
  simp only [sideCost, Fintype.sum_prod_type (f := fun z : (α × γ) × _ => _), siLaw, jointOf,
    Fintype.sum_sum_type, sideMix, Sum.elim_inl, Sum.elim_inr, mul_sum, sum_add_distrib]
  congr 1 <;>
  · refine sum_congr rfl fun z _ => sum_congr rfl fun u _ => ?_
    ring

/-- **Lecture 12, pages 12-6 and 12-17.** The function is convex in `D ≥ D_min`. -/
theorem sideRD_convexOn [Finite β] [Nonempty β] (hP : IsPMF P) (θ : ℝ) :
    ConvexOn ℝ (Set.Ici (minDistortion (margFst P) d)) (sideRD θ P d) := by
  refine ⟨convex_Ici _, fun D₁ hD₁ D₂ hD₂ s t hs ht hst => ?_⟩
  obtain ⟨q₁, f₁, hq₁, hc₁, he₁⟩ := exists_sideRD_eq hP θ hD₁
  obtain ⟨q₂, f₂, hq₂, hc₂, he₂⟩ := exists_sideRD_eq hP θ hD₂
  have hmix := sideMix_isChannel hq₁ hq₂ hs ht hst
  have hcost := sideCost_sideMix (s := s) (t := t) P q₁ q₂ (fun u x y => d x (f₁ u y))
    fun u x y => d x (f₂ u y)
  have hel : (Sum.elim (fun u x y => d x (f₁ u y)) fun u x y => d x (f₂ u y)) =
      fun u x y => d x (Sum.elim f₁ f₂ u y) := by
    funext u x y
    cases u <;> rfl
  rw [hel] at hcost
  have hle := sideRD_le hP hmix θ (d := d) (Sum.elim f₁ f₂) (D := s * D₁ + t * D₂) (by
    rw [hcost]
    gcongr)
  rw [sideRate_sideMix hP hq₁ hq₂ hs ht hst, he₁, he₂] at hle
  simpa only [smul_eq_mul] using hle

end Convex

end InfoTheory
