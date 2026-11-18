/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.SourceHelperConverse
public import InfoTheoryLib.RateDistortion.SideInfoAchievability

/-!
# Source coding with side information at the decoder: the converses

This file proves the converses of Theorems 1 and 2 of Lecture 12 and of the Wyner–Ziv theorem, and
so these theorems. A code gives an auxiliary random variable `Uᵢ` for each coordinate. With a
uniform time sharing variable `Q`, the pair `(Q, U_Q)` is a single auxiliary random variable, with
`U → X → Y` because `Uᵢ` does not depend on `Yᵢ` given `Xᵢ`. The notes use the convexity of the
rate–distortion function instead of `Q`.

* For causal side information, we take `Uᵢ = (M, Zⁱ⁻¹)`, with `Zᵢ = (Xᵢ, Yᵢ)`, instead of the
  `Uᵢ = (M, Yⁱ⁻¹)` of the notes, and bound `∑ᵢ I(Xᵢ; Uᵢ)` by the chain rule for `Zⁿ`. This avoids
  the Markov chain `Xᵢ → (M, Xⁱ⁻¹) → Yⁱ⁻¹` of step (a) on page 12-12.
* For noncausal side information, we take `Uᵢ = (M, Yⁿ \ Yᵢ)` as in the notes.

## Main statements

* `exists_mix_kernel`: the auxiliary random variable given by a family `Vᵢ`.
* `CausalCode.exists_kernel_le`, `WZCode.exists_kernel_le`: the single-letter bounds for one code.
* `rateCausalBits_eq`: **Theorem 1 of Lecture 12**.
* `rateWZBits_eq`: **the Wyner–Ziv theorem**.
* `losslessCausalBits_eq`: **Theorem 2 of Lecture 12**.
* `losslessWZBits_eq`: the optimal lossless rate `H(X | Y)` from the Wyner–Ziv theorem.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 12
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α γ β υ : Type*} [Fintype α] [Fintype γ] [Fintype υ] {P : α × γ → ℝ} {n : ℕ}

/-! ### The auxiliary random variable -/

section Kernel

open Classical in
omit [Fintype υ] in
/-- **The Markov chain `Uᵢ → g(Zᵢ) → Zᵢ` (Lecture 12, pages 12-11 and 12-26).** If `Vᵢ` does not
depend on `Zᵢ` given `g(Zᵢ)`, then `p(a) p(z, v) = p(z) p(a, v)`, with `a = g(z)`. -/
private lemma markov_coordinate {a : Type*} (g : α × γ → a) (i : Fin n)
    (V : (Fin n → α × γ) → υ)
    (hV : ∀ ω (c : α × γ), g c = g (ω i) → V (Function.update ω i c) = V ω) (z : α × γ) (u : υ) :
    dist P g (g z) * dist (iidPMF P n) (pair (fun ω => ω i) V) (z, u) =
      P z * dist (iidPMF P n) (pair (fun ω => g (ω i)) V) (g z, u) := by
  obtain ⟨T, hT⟩ := sum_iidPMF_mul_phi P i z fun ω => if V ω = u then (1 : ℝ) else 0
  have hinv : ∀ (ω : Fin n → α × γ) (c' : α × γ), g c' = g z →
      (if V (Function.update ω i c') = u then (1 : ℝ) else 0) =
        if V (Function.update ω i z) = u then 1 else 0 := fun ω c' hc' => by
    have e : V (Function.update ω i c') = V (Function.update ω i z) := by
      have h := hV (Function.update ω i z) c' (by simp [hc'])
      rwa [Function.update_idem] at h
    rw [e]
  have h1 := hT (fun c' => if c' = z then 1 else 0) fun ω c' hne => by
    have : c' = z := by
      by_contra h
      exact hne (by simp [h])
    rw [this]
  have h2 := hT (fun c' => if g c' = g z then 1 else 0) fun ω c' hne => by
    refine hinv ω c' ?_
    by_contra h
    exact hne (by simp [h])
  have e1 : dist (iidPMF P n) (pair (fun ω => ω i) V) (z, u) =
      ∑ ω, iidPMF P n ω * ((if ω i = z then 1 else 0) * if V ω = u then (1 : ℝ) else 0) := by
    simp only [dist, pair, Prod.mk.injEq]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₁ : ω i = z <;> by_cases h₂ : V ω = u <;> simp [h₁, h₂]
  have e2 : dist (iidPMF P n) (pair (fun ω => g (ω i)) V) (g z, u) =
      ∑ ω, iidPMF P n ω * ((if g (ω i) = g z then 1 else 0) * if V ω = u then (1 : ℝ) else 0) := by
    simp only [dist, pair, Prod.mk.injEq]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₁ : g (ω i) = g z <;> by_cases h₂ : V ω = u <;> simp [h₁, h₂]
  rw [e1, e2, h1, h2]
  have s1 : ∑ c' : α × γ, P c' * (if c' = z then 1 else 0) = P z := by simp
  have s2 : ∑ c' : α × γ, P c' * (if g c' = g z then 1 else 0) = dist P g (g z) := by
    simp only [dist, mul_ite, mul_one, mul_zero]
  rw [s1, s2]
  ring

/-- **The auxiliary random variable.** Let `Vᵢ` be a function of `Zⁿ` that does not depend on `Zᵢ`
given `g(Zᵢ)`. There is `p(u | a)` such that `p(z) p(u | g(z))` is the law of `(Z_Q, V_Q)`, for a
uniform time sharing variable `Q`. -/
theorem exists_mix_kernel_comp {a : Type*} [Finite a] (hP : IsPMF P) (hn : 0 < n) (g : α × γ → a)
    (V : Fin n → (Fin n → α × γ) → υ)
    (hV : ∀ i ω (c : α × γ), g c = g (ω i) → V i (Function.update ω i c) = V i ω) :
    ∃ q : a → υ → ℝ, IsChannel q ∧
      jointOf P (fun z => q (g z)) =
        dist (mixLaw (iidPMF P n) (Fin n)) fun z => (z.1 z.2, V z.2 z.1) := by
  classical
  have := Fintype.ofFinite a
  have hμ := iidPMF_isPMF hP n
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set ν := mixLaw (iidPMF P n) (Fin n) with hν
  have hνP : IsPMF ν := mixLaw_isPMF hμ
  obtain ⟨z₀⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hυ : Nonempty υ := ⟨V ⟨0, hn⟩ fun _ => z₀⟩
  set Gq : (Fin n → α × γ) × Fin n → a := fun z => g (z.1 z.2) with hGq
  set Uq : (Fin n → α × γ) × Fin n → υ := fun z => V z.2 z.1 with hUq
  set r := dist ν (pair Gq Uq) with hr
  have hrP : IsPMF r := hνP.dist _
  obtain ⟨q, hq, hker⟩ := exists_kernel hrP
  have hGmarg : ∀ i : Fin n, dist (iidPMF P n) (fun ω : Fin n → α × γ => g (ω i)) = dist P g :=
    fun i => by
      have h := dist_comp_eq (iidPMF P n) (fun ω : Fin n → α × γ => ω i) g
      rwa [dist_iid_coordinate hP i] at h
  have hG : dist ν Gq = dist P g := by
    funext x
    rw [dist_mixLaw]
    simp only [hGq, hGmarg, Finset.sum_const, card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by simp [hn'.ne']), one_mul]
  have hrfst : dist r Prod.fst = dist P g := by
    rw [hr, ← dist_comp_eq]
    exact hG
  have hker' : ∀ x u, r (x, u) = dist P g x * q x u := fun x u => by
    rw [hker, hrfst]
  have hmark : ∀ z u, dist P g (g z) * dist ν (pair (fun w => w.1 w.2) Uq) (z, u) =
      P z * r (g z, u) := fun z u => by
    rw [hr, dist_mixLaw, dist_mixLaw, mul_left_comm, mul_left_comm (P z)]
    congr 1
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun i _ => markov_coordinate g i (V i) (hV i) z u
  refine ⟨q, hq, ?_⟩
  funext ⟨z, u⟩
  simp only [jointOf]
  change P z * q (g z) u = dist ν (pair (fun w => w.1 w.2) Uq) (z, u)
  by_cases hpx : dist P g (g z) = 0
  · have hP0 : P z = 0 := by
      have h1 : P z ≤ dist P g (g z) := le_dist hP g z
      exact le_antisymm (hpx ▸ h1) (hP.nonneg z)
    have hle : dist ν (pair (fun w => w.1 w.2) Uq) (z, u) ≤ dist ν Gq (g z) := by
      simp only [dist]
      refine sum_le_sum fun w _ => ?_
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (congrArg (fun t => g t.1) h1) h2
      · exact hνP.nonneg w
      · exact le_rfl
    rw [hG, hpx] at hle
    have h0 := (hνP.dist (pair (fun w : (Fin n → α × γ) × Fin n => w.1 w.2) Uq)).nonneg (z, u)
    rw [hP0, zero_mul]
    exact (le_antisymm hle h0).symm
  · have h1 := hmark z u
    rw [hker' (g z) u] at h1
    have h2 : dist P g (g z) * dist ν (pair (fun w => w.1 w.2) Uq) (z, u) =
        dist P g (g z) * (P z * q (g z) u) := by
      rw [h1]
      ring
    exact (mul_left_cancel₀ hpx h2).symm

/-- **The auxiliary random variable (Lecture 12, pages 12-11 and 12-26).** Let `Vᵢ` be a function of
`Zⁿ` that does not depend on `Yᵢ` given `Xᵢ`. There is `p(u | x)` such that `p(x, y) p(u | x)` is
the law of `((X_Q, Y_Q), V_Q)`, for a uniform time sharing variable `Q`. -/
theorem exists_mix_kernel (hP : IsPMF P) (hn : 0 < n) (V : Fin n → (Fin n → α × γ) → υ)
    (hV : ∀ i ω (c : α × γ), c.1 = (ω i).1 → V i (Function.update ω i c) = V i ω) :
    ∃ q : α → υ → ℝ, IsChannel q ∧
      siLaw P q = dist (mixLaw (iidPMF P n) (Fin n)) fun z => (z.1 z.2, V z.2 z.1) :=
  exists_mix_kernel_comp hP hn Prod.fst V hV

/-- The cost under time sharing is the average over the coordinates. -/
lemma sideCost_mix {q : α → υ → ℝ} (hn : 0 < n) {V : Fin n → (Fin n → α × γ) → υ}
    (hlaw : siLaw P q = dist (mixLaw (iidPMF P n) (Fin n)) fun z => (z.1 z.2, V z.2 z.1))
    (c : υ → α → γ → ℝ) :
    sideCost P q c = ∑ ω, iidPMF P n ω * ((∑ i, c (V i ω) (ω i).1 (ω i).2) / n) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have e := sum_dist_mul (mixLaw (iidPMF P n) (Fin n)) (fun z => (z.1 z.2, V z.2 z.1))
    fun z => c z.2 z.1.1 z.1.2
  rw [sideCost, hlaw, e, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  rw [sum_div, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [mixLaw, prodDist, uniformPMF, Fintype.card_fin]
  ring

end Kernel

/-! ### Causal side information -/

section Causal

variable {M : ℕ} (hP : IsPMF P) (c : CausalCode M n α γ β)

/-- The auxiliary random variable `(i, M, Zⁱ⁻¹)`. -/
def causalAux (z₀ : α × γ) (enc : (Fin n → α) → Fin M) (i : Fin n) (ω : Fin n → α × γ) :
    Σ i : Fin n, Fin M × (Fin i → α × γ) :=
  ⟨i, enc (fstSeq ω), prefixRV (seqZ z₀) i ω⟩

/-- The reconstruction `x̂(u, y) = x̂ᵢ(m, yⁱ⁻¹, y)` from the auxiliary random variable. -/
def causalRecon (c : CausalCode M n α γ β) (u : Σ i : Fin n, Fin M × (Fin i → α × γ)) (y : γ) : β :=
  c.dec u.2.1 u.1 (Fin.snoc (α := fun _ => γ) (fun j => (u.2.2 j).2) y)

omit [Fintype α] [Fintype γ] in
lemma causalRecon_aux (z₀ : α × γ) (i : Fin n) (ω : Fin n → α × γ) :
    causalRecon c (causalAux z₀ c.enc i ω) (ω i).2 =
      c.output (c.enc (fstSeq ω)) (sndSeq ω) i := by
  simp only [causalRecon, causalAux, CausalCode.output]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [Fin.snoc_last, prefixSeq, sndSeq]
    congr 2
  · simp only [Fin.snoc_castSucc, prefixSeq, sndSeq, prefixRV]
    have hk : (k : ℕ) < n := k.2.trans i.2
    simp only [seqZ, hk, ↓reduceDIte]
    congr 2

include hP in
/-- **Lecture 12, pages 12-11 and 12-12.** The single-letter bounds: every code gives `p(u | x)` and
`x̂(u, y)` with `E d(X, X̂) ≤ E d(Xⁿ, X̂ⁿ)` and `n I(X; U) ≤ log M`, with `|𝒰| ≤ |𝒳| + 1`. -/
theorem CausalCode.exists_kernel_le (hn : 0 < n) (d : α → β → ℝ) :
    ∃ (q : α → Fin (Fintype.card α + 1) → ℝ) (f : Fin (Fintype.card α + 1) → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ c.distortion P d ∧ n * sideRate 0 P q ≤ log M := by
  classical
  obtain ⟨z₀⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcardn : ((Fintype.card (Fin n) : ℕ) : ℝ) = n := by simp
  set V : Fin n → (Fin n → α × γ) → Σ i : Fin n, Fin M × (Fin i → α × γ) :=
    fun i ω => causalAux z₀ c.enc i ω with hVd
  have hV : ∀ i ω (c' : α × γ), c'.1 = (ω i).1 → V i (Function.update ω i c') = V i ω :=
    fun i ω c' hc' => by
      have hf : fstSeq (Function.update ω i c') = fstSeq ω := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [fstSeq, hc']
        · simp [fstSeq, hj]
      simp only [hVd, causalAux, hf, prefixRV_update]
  obtain ⟨q, hq, hlaw⟩ := exists_mix_kernel hP hn V hV
  have hcost : sideCost P q (fun u x y => d x (causalRecon c u y)) = c.distortion P d := by
    rw [sideCost_mix hn hlaw]
    refine sum_congr rfl fun ω _ => ?_
    congr 1
    simp only [seqDistortion, hVd, causalRecon_aux]
    rfl
  -- The rate.
  set ν := mixLaw (iidPMF P n) (Fin n) with hν
  have hνP : IsPMF ν := mixLaw_isPMF hμ
  have hLaw := siLaw_isPMF hP hq
  have hsig : ∀ i : Fin n, H[fun ω : Fin n → α × γ => (ω i).1 | V i ; iidPMF P n] =
      H[fun ω : Fin n → α × γ => (ω i).1 |
        pair (fun ω => c.enc (fstSeq ω)) (prefixRV (seqZ z₀) i) ; iidPMF P n] := fun i =>
    condEntropy_comp_right_injective hμ _ _ (f := fun w => (⟨i, w⟩ :
      Σ i : Fin n, Fin M × (Fin i → α × γ))) fun a b h => by simpa using h
  have hrate : sideRate 0 P q = entropy (margFst P) -
      (n : ℝ)⁻¹ * ∑ i : Fin n, H[fun ω : Fin n → α × γ => (ω i).1 | V i ; iidPMF P n] := by
    have e1 : I[fun z : (α × γ) × _ => z.1.1 : Prod.snd ; siLaw P q] =
        I[fun z : (Fin n → α × γ) × Fin n => (z.1 z.2).1 : fun z => V z.2 z.1 ; ν] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [hlaw, ← dist_comp_eq]
      rfl
    have e3 := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α × γ) => (ω i).1)
      fun i ω => (c.enc (fstSeq ω), prefixRV (seqZ z₀) i ω)
    rw [hcardn] at e3
    have e2 : H[fun z : (Fin n → α × γ) × Fin n => (z.1 z.2).1 ; ν] = entropy (margFst P) := by
      rw [entropyRV]
      congr 1
      have hd := dist_siLaw_X (P := P) hq
      rw [hlaw] at hd
      rw [← dist_comp_eq] at hd
      exact hd
    rw [sideRate, zero_mul, sub_zero, e1, mutualInfo_eq_entropy_sub_condEntropy hνP, e2]
    congr 1
    refine e3.trans ?_
    congr 1
    exact sum_congr rfl fun i _ => (hsig i).symm
  have hb := sum_mutualInfo_prefix_le hP z₀ Prod.fst fun ω => c.enc (fstSeq ω)
  have hXmarg : ∀ i : Fin n, H[fun ω : Fin n → α × γ => (ω i).1 ; iidPMF P n] =
      entropy (margFst P) := fun i => by
    have h := dist_comp_eq (iidPMF P n) (fun ω : Fin n → α × γ => ω i) Prod.fst
    rw [dist_iid_coordinate hP i] at h
    rw [entropyRV]
    exact congrArg entropy h
  have hexp : ∑ i : Fin n, I[fun ω : Fin n → α × γ => (ω i).1 :
      pair (fun ω => c.enc (fstSeq ω)) (prefixRV (seqZ z₀) i) ; iidPMF P n] =
      n * entropy (margFst P) - ∑ i : Fin n,
        H[fun ω : Fin n → α × γ => (ω i).1 | V i ; iidPMF P n] := by
    have hs : ∑ i : Fin n, H[fun ω : Fin n → α × γ => (ω i).1 ; iidPMF P n] =
        n * entropy (margFst P) := by
      simp only [hXmarg, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hs, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mutualInfo_eq_entropy_sub_condEntropy hμ, hsig]
  rw [hexp] at hb
  obtain ⟨q', f', hq', h1, h2⟩ := exists_side_reduce₁ hP hq 0 d (causalRecon c)
  refine ⟨q', f', hq', h2.trans hcost.le, ?_⟩
  rw [h1, hrate, mul_sub, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
  exact hb

/-- **The converse of Theorem 1 of Lecture 12.** If `(R, D)` is achievable, there are `p(u | x)` and
`x̂(u, y)` with `E d(X, X̂) ≤ D` and `I(X; U) ≤ R`, in bits. -/
theorem IsAchievableCausalBits.exists_kernel [Finite β] (hP : IsPMF P) {d : α → β → ℝ} {R D : ℝ}
    (h : IsAchievableCausalBits P d R D) :
    ∃ (q : α → Fin (Fintype.card α + 1) → ℝ) (f : Fin (Fintype.card α + 1) → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ D ∧ sideRate 0 P q ≤ R * log 2 := by
  obtain ⟨hR, c, hc⟩ := h
  refine exists_le_of_forall_side hP 0 fun ε hε => ?_
  obtain ⟨n, hn1, hn2⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
  obtain ⟨q, f, hq, h1, h2⟩ := (c n).exists_kernel_le hP hn2 d
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn2
  exact ⟨q, f, hq, h1.trans hn1, le_of_mul_le_mul_left (h2.trans
    (by simpa using log_two_pow_floor_le n hR)) hn'⟩

/-- **Theorem 1 of Lecture 12 of [elgamal2010], page 12-6.** The rate–distortion function with side
information available causally at the decoder is `R_CSI-D(D) = min I(X; U)`, over `p(u | x)` and
`x̂(u, y)` with `E d(X, X̂) ≤ D`, for `D ≥ D_min`, in bits. By `exists_sideRD_eq`, the minimum is
attained with `|𝒰| ≤ |𝒳| + 1`. -/
theorem rateCausalBits_eq [Finite β] [Nonempty β] (hP : IsPMF P) {d : α → β → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) {D : ℝ} (hD : minDistortion (margFst P) d ≤ D) :
    rateCausalBits P d D = causalRD P d D / log 2 := by
  have hl := log_pos one_lt_two
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 0) hP hD
  have hach : ∀ R, causalRD P d D / log 2 < R → IsAchievableCausalBits P d R D := fun R hR =>
    isAchievableCausalBits_of_lt hP hd hq f hc (by rwa [he])
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, hach _ (lt_add_one _)⟩ (fun R hR => ?_)
    fun w hw => ⟨(causalRD P d D / log 2 + w) / 2, hach _ (by linarith), by linarith⟩
  obtain ⟨q', f', hq', hc', hr'⟩ := hR.exists_kernel hP
  rw [div_le_iff₀ hl]
  exact (sideRD_le hP hq' 0 f' hc').trans hr'

end Causal

/-! ### Noncausal side information -/

section WZ

variable {M : ℕ} (hP : IsPMF P) (c : WZCode M n α γ β)

/-- The auxiliary random variable `(i, M, Yⁿ \ Yᵢ)`, with `y₀` in the place of `Yᵢ`. -/
def wzAux (y₀ : γ) (enc : (Fin n → α) → Fin M) (i : Fin n) (ω : Fin n → α × γ) :
    Σ _ : Fin n, Fin M × (Fin n → γ) :=
  ⟨i, enc (fstSeq ω), Function.update (sndSeq ω) i y₀⟩

/-- The reconstruction `x̂(u, y) = x̂ᵢ(m, yⁿ)` from the auxiliary random variable. -/
def wzRecon (c : WZCode M n α γ β) (u : Σ _ : Fin n, Fin M × (Fin n → γ)) (y : γ) : β :=
  c.dec u.2.1 (Function.update u.2.2 u.1 y) u.1

omit [Fintype α] [Fintype γ] in
lemma wzRecon_aux (y₀ : γ) (i : Fin n) (ω : Fin n → α × γ) :
    wzRecon c (wzAux y₀ c.enc i ω) (ω i).2 = c.dec (c.enc (fstSeq ω)) (sndSeq ω) i := by
  simp only [wzRecon, wzAux, Function.update_idem]
  have : Function.update (sndSeq ω) i (ω i).2 = sndSeq ω := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [sndSeq]
    · simp [hj]
  rw [this]

/-- `H(Xⁿ | Yⁿ) = n H(X | Y)`. -/
lemma condEntropy_iid_seq (hP : IsPMF P) (n : ℕ) :
    H[fstSeq | sndSeq ; iidPMF P n] = n * H[Prod.fst | Prod.snd ; P] := by
  classical
  have hμ := iidPMF_isPMF hP n
  have e1 : H[pair (sndSeq : (Fin n → α × γ) → Fin n → γ) fstSeq ; iidPMF P n] =
      H[fun (ω : Fin n → α × γ) i => ((ω i).2, (ω i).1) ; iidPMF P n] := by
    refine entropyRV_eq_of_injective _ (fun w => (fun i => (w i).1, fun i => (w i).2)) ?_
      fun _ => rfl
    intro w w' h
    funext i
    exact Prod.ext (congrFun (Prod.mk.inj h).1 i) (congrFun (Prod.mk.inj h).2 i)
  have e2 : H[(sndSeq : (Fin n → α × γ) → Fin n → γ) ; iidPMF P n] = n * H[Prod.snd ; P] :=
    entropyRV_iidPMF_comp hP n Prod.snd
  rw [condEntropy_eq_sub hμ, e1, entropyRV_iidPMF_comp hP n (fun z => (z.2, z.1)), e2,
    condEntropy_eq_sub hP]
  have e3 : H[pair Prod.snd Prod.fst ; P] = H[fun z : α × γ => (z.2, z.1) ; P] := rfl
  rw [e3]
  ring

/-- **Lecture 12, page 12-26.** `∑ᵢ H(Xᵢ | M, Yⁿ) ≥ H(Xⁿ | Yⁿ) - log M`. -/
private lemma sum_condEntropy_ge (hP : IsPMF P) (hM : 0 < M) (z₀ : α × γ)
    (enc : (Fin n → α) → Fin M) :
    n * H[Prod.fst | Prod.snd ; P] - log M ≤ ∑ i : Fin n,
      H[fun ω : Fin n → α × γ => (ω i).1 | pair (fun ω => enc (fstSeq ω)) sndSeq ; iidPMF P n] := by
  classical
  have hμ := iidPMF_isPMF hP n
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set Me : (Fin n → α × γ) → Fin M := fun ω => enc (fstSeq ω) with hMe
  set Yq : (Fin n → α × γ) → Fin n → γ := sndSeq with hYq
  set Xk : ℕ → (Fin n → α × γ) → α := fun k ω => (seqZ z₀ k ω).1 with hXk
  have hchain := chain_rule_entropy_cond hμ Xk (pair Me Yq) n
  have hprefix : prefixRV Xk n = (fstSeq : (Fin n → α × γ) → Fin n → α) := by
    funext ω j
    simp only [prefixRV, hXk, fstSeq, seqZ_coe]
  rw [hprefix, sum_range] at hchain
  have hle : H[fstSeq | pair Me Yq ; iidPMF P n] ≤ ∑ i : Fin n,
      H[fun ω : Fin n → α × γ => (ω i).1 | pair Me Yq ; iidPMF P n] := by
    rw [hchain]
    refine sum_le_sum fun i _ => ?_
    have hX : Xk i = fun ω : Fin n → α × γ => (ω i).1 := funext fun ω => by
      simp only [hXk, seqZ_coe]
    rw [hX]
    exact condEntropy_le_condEntropy_comp hμ _ (pair (pair Me Yq) (prefixRV Xk i)) Prod.fst
  have hc1 := chain_rule_cond hμ fstSeq Me Yq
  have hc2 := chain_rule_cond hμ Me fstSeq Yq
  have hswap : H[pair fstSeq Me | Yq ; iidPMF P n] = H[pair Me fstSeq | Yq ; iidPMF P n] :=
    condEntropy_congr_left hμ Yq Prod.swap Prod.swap_injective fun _ => rfl
  have h0 := condEntropy_nonneg hμ Me (pair fstSeq Yq)
  have h1 : H[Me | Yq ; iidPMF P n] ≤ log M := by
    have h2 := condEntropy_le_entropy hμ Me Yq
    have h3 := entropyRV_le_log_card hμ Me
    rw [Fintype.card_fin] at h3
    linarith
  have h4 := condEntropy_iid_seq hP n
  linarith

include hP in
/-- **Lecture 12, pages 12-26 and 12-27.** The auxiliary random variable `(Q, M, Yⁿ \ Y_Q)` of a
code: its costs are the averages over the coordinates, and `n I(X; U | Y) ≤ log M`. -/
theorem WZCode.exists_aux_law (hn : 0 < n) (hM : 0 < M) (enc : (Fin n → α) → Fin M) :
    ∃ (y₀ : γ) (q : α → (Σ _ : Fin n, Fin M × (Fin n → γ)) → ℝ), IsChannel q ∧
      (∀ e : (Σ _ : Fin n, Fin M × (Fin n → γ)) → α → γ → ℝ, sideCost P q e =
        ∑ ω, iidPMF P n ω * ((∑ i, e (wzAux y₀ enc i ω) (ω i).1 (ω i).2) / n)) ∧
      n * sideRate 1 P q ≤ log M := by
  classical
  obtain ⟨z₀⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcardn : ((Fintype.card (Fin n) : ℕ) : ℝ) = n := by simp
  set V : Fin n → (Fin n → α × γ) → Σ _ : Fin n, Fin M × (Fin n → γ) :=
    fun i ω => wzAux z₀.2 enc i ω with hVd
  have hV : ∀ i ω (c' : α × γ), c'.1 = (ω i).1 → V i (Function.update ω i c') = V i ω :=
    fun i ω c' hc' => by
      have hf : fstSeq (Function.update ω i c') = fstSeq ω := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [fstSeq, hc']
        · simp [fstSeq, hj]
      have hg : Function.update (sndSeq (Function.update ω i c')) i z₀.2 =
          Function.update (sndSeq ω) i z₀.2 := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [sndSeq, hj]
      simp only [hVd, wzAux, hf, hg]
  obtain ⟨q, hq, hlaw⟩ := exists_mix_kernel hP hn V hV
  -- The rate.
  set ν := mixLaw (iidPMF P n) (Fin n) with hν
  have hνP : IsPMF ν := mixLaw_isPMF hμ
  have hLaw := siLaw_isPMF hP hq
  set Me : (Fin n → α × γ) → Fin M := fun ω => enc (fstSeq ω) with hMe
  have hsig : ∀ i : Fin n, H[fun ω : Fin n → α × γ => (ω i).1 |
      pair (fun ω => ((Me ω, Function.update (sndSeq ω) i z₀.2) : Fin M × (Fin n → γ)))
        (fun ω => (ω i).2) ; iidPMF P n] =
      H[fun ω : Fin n → α × γ => (ω i).1 | pair Me sndSeq ; iidPMF P n] := fun i => by
    refine condEntropy_congr_right hμ (fun ω : Fin n → α × γ => (ω i).1)
      (X := pair Me sndSeq)
      (fun w : Fin M × (Fin n → γ) => ((w.1, Function.update w.2 i z₀.2), w.2 i)) ?_
        fun ω => rfl
    rintro ⟨m, y⟩ ⟨m', y'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, h2⟩, h3⟩ := h
    refine Prod.ext rfl ?_
    funext j
    by_cases hj : j = i
    · subst hj
      exact h3
    · have := congrFun h2 j
      simpa [hj] using this
  have hrate : sideRate 1 P q = H[Prod.fst | Prod.snd ; P] -
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        H[fun ω : Fin n → α × γ => (ω i).1 | pair Me sndSeq ; iidPMF P n] := by
    rw [sideRate_one hP hq, condMutualInfo]
    congr 1
    · refine condEntropy_eq_of_dist_pair_eq hLaw hP ?_
      rw [show pair (fun z : (α × γ) × (Σ _ : Fin n, Fin M × (Fin n → γ)) => z.1.2)
        (fun z => z.1.1) = (pair Prod.snd Prod.fst) ∘ Prod.fst from rfl, dist_comp_eq,
        dist_siLaw_fst hq]
    · have e1 : H[fun z : (α × γ) × (Σ _ : Fin n, Fin M × (Fin n → γ)) => z.1.1 |
          pair Prod.snd fun z => z.1.2 ; siLaw P q] =
          H[fun z : (Fin n → α × γ) × Fin n => (z.1 z.2).1 |
            pair (fun z => V z.2 z.1) (fun z => (z.1 z.2).2) ; ν] := by
        refine condEntropy_eq_of_dist_pair_eq hLaw hνP ?_
        rw [hlaw, ← dist_comp_eq]
        rfl
      have e2 : H[fun z : (Fin n → α × γ) × Fin n => (z.1 z.2).1 |
          pair (fun z => V z.2 z.1) (fun z => (z.1 z.2).2) ; ν] =
          H[fun z : (Fin n → α × γ) × Fin n => (z.1 z.2).1 | fun z =>
            (⟨z.2, pair (fun ω => ((Me ω, Function.update (sndSeq ω) z.2 z₀.2) :
              Fin M × (Fin n → γ))) (fun ω => (ω z.2).2) z.1⟩ :
                Σ _ : Fin n, (Fin M × (Fin n → γ)) × γ) ; ν] := by
        refine (condEntropy_congr_right hνP _
          (fun w : (Σ _ : Fin n, Fin M × (Fin n → γ)) × γ =>
            (⟨w.1.1, (w.1.2, w.2)⟩ : Σ _ : Fin n, (Fin M × (Fin n → γ)) × γ)) ?_
              fun _ => rfl).symm
        rintro ⟨⟨i, a⟩, y⟩ ⟨⟨i', a'⟩, y'⟩ h
        simp only [Sigma.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h2
        rw [h2.1, h2.2]
      have e3 := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α × γ) => (ω i).1)
        (b := fun _ => (Fin M × (Fin n → γ)) × γ)
        fun i => pair (fun ω => ((Me ω, Function.update (sndSeq ω) i z₀.2) :
          Fin M × (Fin n → γ))) (fun ω => (ω i).2)
      rw [hcardn] at e3
      rw [e1, e2]
      refine e3.trans ?_
      congr 1
      exact sum_congr rfl fun i _ => hsig i
  have hb := sum_condEntropy_ge hP hM z₀ enc (n := n)
  refine ⟨z₀.2, q, hq, fun e => sideCost_mix hn hlaw e, ?_⟩
  rw [hrate, mul_sub, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
  linarith

include hP in
/-- **Lecture 12, pages 12-26 and 12-27.** The single-letter bounds: every code gives `p(u | x)` and
`x̂(u, y)` with `E d(X, X̂) ≤ E d(Xⁿ, X̂ⁿ)` and `n I(X; U | Y) ≤ log M`, with `|𝒰| ≤ |𝒳| + 1`. -/
theorem WZCode.exists_kernel_le (hn : 0 < n) (hM : 0 < M) (d : α → β → ℝ) :
    ∃ (q : α → Fin (Fintype.card α + 1) → ℝ) (f : Fin (Fintype.card α + 1) → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ c.distortion P d ∧ n * sideRate 1 P q ≤ log M := by
  obtain ⟨y₀, q, hq, he, hr⟩ := WZCode.exists_aux_law hP hn hM c.enc
  have hcost : sideCost P q (fun u x y => d x (wzRecon c u y)) = c.distortion P d := by
    rw [he]
    refine sum_congr rfl fun ω _ => ?_
    congr 1
    simp only [seqDistortion, wzRecon_aux]
    rfl
  obtain ⟨q', f', hq', h1, h2⟩ := exists_side_reduce₁ hP hq 1 d (wzRecon c)
  exact ⟨q', f', hq', h2.trans hcost.le, by rwa [h1]⟩

/-- **The converse of the Wyner–Ziv theorem.** If `(R, D)` is achievable, there are `p(u | x)` and
`x̂(u, y)` with `E d(X, X̂) ≤ D` and `I(X; U | Y) ≤ R`, in bits. -/
theorem IsAchievableWZBits.exists_kernel [Finite β] (hP : IsPMF P) {d : α → β → ℝ} {R D : ℝ}
    (h : IsAchievableWZBits P d R D) :
    ∃ (q : α → Fin (Fintype.card α + 1) → ℝ) (f : Fin (Fintype.card α + 1) → γ → β), IsChannel q ∧
      sideCost P q (fun u x y => d x (f u y)) ≤ D ∧ sideRate 1 P q ≤ R * log 2 := by
  obtain ⟨hR, c, hc⟩ := h
  refine exists_le_of_forall_side hP 1 fun ε hε => ?_
  obtain ⟨n, hn1, hn2⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
  obtain ⟨q, f, hq, h1, h2⟩ := (c n).exists_kernel_le hP hn2 (by positivity) d
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn2
  exact ⟨q, f, hq, h1.trans hn1, le_of_mul_le_mul_left (h2.trans
    (by simpa using log_two_pow_floor_le n hR)) hn'⟩

/-- **The Wyner–Ziv theorem (Lecture 12 of [elgamal2010], page 12-17).** The rate–distortion
function with side information available only at the decoder is
`R_SI-D(D) = min (I(X; U) - I(Y; U)) = min I(X; U | Y)`, over `p(u | x)` and `x̂(u, y)` with
`E d(X, X̂) ≤ D`, for `D ≥ D_min`, in bits. By `exists_sideRD_eq`, the minimum is attained with
`|𝒰| ≤ |𝒳| + 1`. -/
theorem rateWZBits_eq [Finite β] [Nonempty β] (hP : IsPMF P) {d : α → β → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) {D : ℝ} (hD : minDistortion (margFst P) d ≤ D) :
    rateWZBits P d D = wzRD P d D / log 2 := by
  have hl := log_pos one_lt_two
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 1) hP hD
  have hach : ∀ R, wzRD P d D / log 2 < R → IsAchievableWZBits P d R D := fun R hR =>
    isAchievableWZBits_of_lt hP hd hq f hc (by rwa [he])
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, hach _ (lt_add_one _)⟩ (fun R hR => ?_)
    fun w hw => ⟨(wzRD P d D / log 2 + w) / 2, hach _ (by linarith), by linarith⟩
  obtain ⟨q', f', hq', hc', hr'⟩ := hR.exists_kernel hP
  rw [div_le_iff₀ hl]
  exact (sideRD_le hP hq' 1 f' hc').trans hr'

end WZ

/-! ### Lossless source coding -/

section Lossless

variable {q : α → υ → ℝ}

/-- **Lecture 12, page 12-13.** `min I(X; U)` over `p(u | x)` with `H(X | U, Y) = 0`, with `U` on
`Fin k` for some `k`, in nats. -/
def losslessCausalRate (P : α × γ → ℝ) : ℝ :=
  sInf {I | ∃ (k : ℕ) (q : α → Fin k → ℝ), IsChannel q ∧
    H[fun z : (α × γ) × Fin k => z.1.1 | pair Prod.snd (fun z => z.1.2) ; siLaw P q] = 0 ∧
    sideRate 0 P q = I}

open Classical in
/-- **Lecture 12, page 12-14.** `E d(X, x̂(U, Y)) ≤ 0` for the Hamming distortion if and only if
`X = x̂(U, Y)` with probability `1`. -/
lemma sideCost_hamming_le_zero_iff (hP : IsPMF P) (hq : IsChannel q) (f : υ → γ → α) :
    sideCost P q (fun u x y => hammingDistortion x (f u y)) ≤ 0 ↔
      ∀ z, siLaw P q z ≠ 0 → f z.2 z.1.2 = z.1.1 := by
  have hμ := siLaw_isPMF hP hq
  have hnn : ∀ z ∈ univ, 0 ≤ siLaw P q z * hammingDistortion z.1.1 (f z.2 z.1.2) := fun z _ =>
    mul_nonneg (hμ.nonneg z) (hammingDistortion_nonneg _ _)
  constructor
  · intro h z hz
    have h0 : sideCost P q (fun u x y => hammingDistortion x (f u y)) = 0 :=
      le_antisymm h (sum_nonneg hnn)
    have ht := (sum_eq_zero_iff_of_nonneg hnn).1 h0 z (mem_univ z)
    have hd := (mul_eq_zero.1 ht).resolve_left hz
    by_contra hne
    simp [hammingDistortion, Ne.symm hne] at hd
  · intro h
    refine le_of_eq (sum_eq_zero fun z _ => ?_)
    by_cases hz : siLaw P q z = 0
    · rw [hz, zero_mul]
    · change siLaw P q z * hammingDistortion z.1.1 (f z.2 z.1.2) = 0
      rw [h z hz]
      simp [hammingDistortion]

/-- **Lecture 12, pages 12-14 and 12-15.** `H(X | U, Y) = 0` if and only if `X = x̂(U, Y)` with
probability `1` for some `x̂(u, y)`. -/
lemma condEntropy_XUY_eq_zero_iff (hP : IsPMF P) (hq : IsChannel q) :
    H[fun z : (α × γ) × υ => z.1.1 | pair Prod.snd (fun z => z.1.2) ; siLaw P q] = 0 ↔
      ∃ f : υ → γ → α, ∀ z, siLaw P q z ≠ 0 → f z.2 z.1.2 = z.1.1 := by
  rw [condEntropy_eq_zero_iff (siLaw_isPMF hP hq)]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨fun u y => g (u, y), fun z hz => (hg z hz).symm⟩
  · rintro ⟨f, hf⟩
    exact ⟨fun w => f w.1 w.2, fun z hz => (hf z hz).symm⟩

/-- The minimum over `H(X | U, Y) = 0` is `R_CSI-D(0)` for the Hamming distortion. -/
theorem losslessCausalRate_eq (hP : IsPMF P) :
    losslessCausalRate P = causalRD P (hammingDistortion (α := α)) 0 := by
  classical
  have hset : {I | ∃ (k : ℕ) (q : α → Fin k → ℝ), IsChannel q ∧
      H[fun z : (α × γ) × Fin k => z.1.1 | pair Prod.snd (fun z => z.1.2) ; siLaw P q] = 0 ∧
      sideRate 0 P q = I} =
      {I | ∃ (k : ℕ) (q : α → Fin k → ℝ) (f : Fin k → γ → α), IsChannel q ∧
        sideCost P q (fun u x y => hammingDistortion x (f u y)) ≤ 0 ∧ sideRate 0 P q = I} := by
    ext I
    constructor
    · rintro ⟨k, q, hq, h0, rfl⟩
      obtain ⟨f, hf⟩ := (condEntropy_XUY_eq_zero_iff hP hq).1 h0
      exact ⟨k, q, f, hq, (sideCost_hamming_le_zero_iff hP hq f).2 hf, rfl⟩
    · rintro ⟨k, q, f, hq, hc, rfl⟩
      exact ⟨k, q, hq, (condEntropy_XUY_eq_zero_iff hP hq).2
        ⟨f, (sideCost_hamming_le_zero_iff hP hq f).1 hc⟩, rfl⟩
  rw [losslessCausalRate, hset]
  rfl

open Classical in
omit [Fintype α] [Fintype γ] in
/-- The Hamming distortion is at most the indicator of a block error. -/
lemma seqDistortion_hamming_le {x y : Fin n → α} :
    seqDistortion hammingDistortion x y ≤ if y ≠ x then 1 else 0 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases h : y = x
  · subst h
    simp [seqDistortion, hammingDistortion]
  · simp only [h, ne_eq, not_false_eq_true, ite_true]
    rcases eq_or_lt_of_le hn0 with h0 | h0
    · simp [seqDistortion, ← h0]
    · rw [seqDistortion, div_le_one h0]
      calc ∑ i, hammingDistortion (x i) (y i) ≤ ∑ _i : Fin n, (1 : ℝ) := sum_le_sum fun i _ => by
            unfold hammingDistortion
            split_ifs <;> norm_num
        _ = n := by simp

/-- A lossless code is a code of distortion `0` for the Hamming distortion. -/
theorem IsLosslessCausalBits.isAchievable {R : ℝ} (hP : IsPMF P) (h : IsLosslessCausalBits P R) :
    IsAchievableCausalBits P (hammingDistortion (α := α)) R 0 := by
  classical
  obtain ⟨hR, c, hc⟩ := h
  refine ⟨hR, c, fun ε hε => ?_⟩
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
  rw [zero_add]
  refine le_trans (sum_le_sum fun ω _ => ?_) hn.le
  have h0 := (iidPMF_isPMF hP n).nonneg ω
  have := seqDistortion_hamming_le (x := fstSeq ω)
    (y := (c n).output ((c n).enc (fstSeq ω)) (sndSeq ω))
  split_ifs at this ⊢ with h1
  · exact mul_le_of_le_one_right h0 this
  · exact mul_nonpos_of_nonneg_of_nonpos h0 this

/-- A lossless code is a code of distortion `0` for the Hamming distortion. -/
theorem IsLosslessWZBits.isAchievable {R : ℝ} (hP : IsPMF P) (h : IsLosslessWZBits P R) :
    IsAchievableWZBits P (hammingDistortion (α := α)) R 0 := by
  classical
  obtain ⟨hR, c, hc⟩ := h
  refine ⟨hR, c, fun ε hε => ?_⟩
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
  rw [zero_add]
  refine le_trans (sum_le_sum fun ω _ => ?_) hn.le
  have h0 := (iidPMF_isPMF hP n).nonneg ω
  have := seqDistortion_hamming_le (x := fstSeq ω)
    (y := (c n).dec ((c n).enc (fstSeq ω)) (sndSeq ω))
  split_ifs at this ⊢ with h1
  · exact mul_le_of_le_one_right h0 this
  · exact mul_nonpos_of_nonneg_of_nonpos h0 this

/-- **Theorem 2 of Lecture 12 of [elgamal2010], page 12-13.** The optimal rate of lossless source
coding with causal side information is `R*_CSI-D = min I(X; U)` over `p(u | x)` with
`H(X | U, Y) = 0`, in bits. -/
theorem losslessCausalBits_eq (hP : IsPMF P) :
    sInf {R | IsLosslessCausalBits P R} = losslessCausalRate P / log 2 := by
  classical
  have hl := log_pos one_lt_two
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α := ⟨z.1⟩
  rw [losslessCausalRate_eq hP]
  have hD : minDistortion (margFst P) (hammingDistortion (α := α)) ≤ 0 :=
    (minDistortion_hammingDistortion _).le
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 0) hP hD
  have hach : ∀ R, causalRD P (hammingDistortion (α := α)) 0 / log 2 < R →
      IsLosslessCausalBits P R := fun R hR =>
    isLosslessCausalBits_of_lt hP hq f ((sideCost_hamming_le_zero_iff hP hq f).1 hc)
      (by rw [he]; exact hR)
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, hach _ (lt_add_one _)⟩ (fun R hR => ?_)
    fun w hw => ⟨(causalRD P (hammingDistortion (α := α)) 0 / log 2 + w) / 2,
      hach _ (by linarith), by linarith⟩
  obtain ⟨q', f', hq', hc', hr'⟩ := (hR.isAchievable hP).exists_kernel hP
  rw [div_le_iff₀ hl]
  exact (sideRD_le hP hq' 0 f' hc').trans hr'

/-- `X = x̂(U, Y)` with probability `1` gives `I(X; U | Y) = H(X | Y)`. -/
lemma sideRate_one_eq_of_support (hP : IsPMF P) (hq : IsChannel q)
    (h0 : H[fun z : (α × γ) × υ => z.1.1 | pair Prod.snd (fun z => z.1.2) ; siLaw P q] = 0) :
    sideRate 1 P q = H[Prod.fst | Prod.snd ; P] := by
  rw [sideRate_one hP hq, condMutualInfo, h0, sub_zero]
  refine condEntropy_eq_of_dist_pair_eq (siLaw_isPMF hP hq) hP ?_
  rw [show pair (fun z : (α × γ) × υ => z.1.2) (fun z => z.1.1) =
    (pair Prod.snd Prod.fst) ∘ Prod.fst from rfl, dist_comp_eq, dist_siLaw_fst hq]

/-- The test channel with `U = X`. -/
def identityKernel [DecidableEq α] (x u : α) : ℝ := if u = x then 1 else 0

omit [Fintype γ] [Fintype υ] in
lemma identityKernel_isChannel [DecidableEq α] : IsChannel (identityKernel (α := α)) := fun x => by
  refine ⟨fun u => by unfold identityKernel; split_ifs <;> norm_num, ?_⟩
  simp [identityKernel]

/-- Any rate above `H(X | Y)` is achievable for lossless source coding with side information at the
decoder. -/
theorem isLosslessWZBits_of_condEntropy_lt (hP : IsPMF P) {R : ℝ}
    (hR : H[Prod.fst | Prod.snd ; P] / log 2 < R) : IsLosslessWZBits P R := by
  classical
  have hid : IsChannel (identityKernel (α := α)) := identityKernel_isChannel
  have hf : ∀ z : (α × γ) × α, siLaw P identityKernel z ≠ 0 →
      (fun (u : α) (_ : γ) => u) z.2 z.1.2 = z.1.1 := fun z hz => by
    by_contra hne
    apply hz
    simp [siLaw, jointOf, identityKernel, hne]
  have hrate : sideRate 1 P (identityKernel (α := α)) = H[Prod.fst | Prod.snd ; P] :=
    sideRate_one_eq_of_support hP hid
      ((condEntropy_XUY_eq_zero_iff hP hid).2 ⟨fun u _ => u, hf⟩)
  exact isLosslessWZBits_of_lt hP hid (fun u _ => u) hf (by rw [hrate]; exact hR)

/-- **The lossless case of the Wyner–Ziv theorem (Lecture 12, pages 12-16 and 12-25).** The optimal
rate of lossless source coding with noncausal side information is `R*_SI-D = H(X | Y)`, in bits: the
corner point of the Slepian–Wolf theorem is a special case of the Wyner–Ziv theorem. -/
theorem losslessWZBits_eq (hP : IsPMF P) :
    sInf {R | IsLosslessWZBits P R} = H[Prod.fst | Prod.snd ; P] / log 2 := by
  have hl := log_pos one_lt_two
  have hach : ∀ R, H[Prod.fst | Prod.snd ; P] / log 2 < R → IsLosslessWZBits P R := fun R hR =>
    isLosslessWZBits_of_condEntropy_lt hP hR
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, hach _ (lt_add_one _)⟩ (fun R hR => ?_)
    fun w hw => ⟨(H[Prod.fst | Prod.snd ; P] / log 2 + w) / 2, hach _ (by linarith), by linarith⟩
  obtain ⟨q, f, hq, hc, hr⟩ := (hR.isAchievable hP).exists_kernel hP
  have h0 := (condEntropy_XUY_eq_zero_iff hP hq).2
    ⟨f, (sideCost_hamming_le_zero_iff hP hq f).1 hc⟩
  rw [sideRate_one_eq_of_support hP hq h0] at hr
  rwa [div_le_iff₀ hl]

/-- `I(X; U) = H(X)` if `H(X | U) = 0`. -/
private lemma sideRate_zero_of_condEntropy {q : α → υ → ℝ} (hP : IsPMF P) (hq : IsChannel q)
    (h : H[fun z : (α × γ) × υ => z.1.1 | Prod.snd ; siLaw P q] = 0) :
    sideRate 0 P q = entropy (margFst P) := by
  have hμ := siLaw_isPMF hP hq
  rw [sideRate, zero_mul, sub_zero, mutualInfo_eq_entropy_sub_condEntropy hμ, h, sub_zero,
    entropyRV,
    dist_siLaw_X hq]

/-- **Lecture 12, page 12-13.** `R*_CSI-D ≤ H(X)`: the auxiliary random variable `U = X`. -/
theorem losslessCausalRate_le_entropy (hP : IsPMF P) :
    losslessCausalRate P ≤ entropy (margFst P) := by
  classical
  have hid : IsChannel (identityKernel (α := α)) := identityKernel_isChannel
  have hf : ∀ z : (α × γ) × α, siLaw P identityKernel z ≠ 0 →
      (fun (u : α) (_ : γ) => u) z.2 z.1.2 = z.1.1 := fun z hz => by
    by_contra hne
    apply hz
    simp [siLaw, jointOf, identityKernel, hne]
  rw [losslessCausalRate_eq hP]
  refine (sideRD_le hP hid 0 (fun u _ => u)
    ((sideCost_hamming_le_zero_iff hP hid fun u _ => u).2 hf)).trans (le_of_eq ?_)
  refine sideRate_zero_of_condEntropy hP hid ?_
  exact (condEntropy_eq_zero_iff (siLaw_isPMF hP hid) _ _).2
    ⟨id, fun z hz => (hf z hz).symm⟩

/-- **Lecture 12, page 12-13.** `H(X | Y) ≤ R*_CSI-D`. -/
theorem condEntropy_le_losslessCausalRate (hP : IsPMF P) :
    H[Prod.fst | Prod.snd ; P] ≤ losslessCausalRate P := by
  classical
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α := ⟨z.1⟩
  rw [losslessCausalRate_eq hP]
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 0) hP
    (minDistortion_hammingDistortion (margFst P)).le
  have h0 := (condEntropy_XUY_eq_zero_iff hP hq).2
    ⟨f, (sideCost_hamming_le_zero_iff hP hq f).1 hc⟩
  have h1 := sideRate_one_eq_of_support hP hq h0
  have h2 := mutualInfo_nonneg (siLaw_isPMF hP hq) (fun z : (α × γ) × _ => z.1.2) Prod.snd
  rw [causalRD, ← he, ← h1]
  simp only [sideRate]
  linarith

/-- **Lecture 12, pages 12-14 and 12-15.** If `p(x, y) > 0` for all `(x, y)`, then
`R*_CSI-D = H(X)`: causal side information does not help at all. -/
theorem losslessCausalRate_of_pos (hP : IsPMF P) (hpos : ∀ z, P z ≠ 0) :
    losslessCausalRate P = entropy (margFst P) := by
  classical
  obtain ⟨z₀⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α := ⟨z₀.1⟩
  refine le_antisymm (losslessCausalRate_le_entropy hP) ?_
  rw [losslessCausalRate_eq hP]
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 0) hP
    (minDistortion_hammingDistortion (margFst P)).le
  have hf := (sideCost_hamming_le_zero_iff hP hq f).1 hc
  have h0 : H[fun z : (α × γ) × _ => z.1.1 | Prod.snd ; siLaw P q] = 0 := by
    refine (condEntropy_eq_zero_iff (siLaw_isPMF hP hq) _ _).2 ⟨fun u => f u z₀.2, fun z hz => ?_⟩
    have hqz : q z.1.1 z.2 ≠ 0 := fun h => hz (by simp [siLaw, jointOf, h])
    have := hf ((z.1.1, z₀.2), z.2) (by simp [siLaw, jointOf, hpos, hqz])
    exact this.symm
  rw [causalRD, ← he, sideRate_zero_of_condEntropy hP hq h0]

end Lossless

end InfoTheory
