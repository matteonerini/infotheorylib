/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayRates

/-!
# The relay channel: partial decode–forward

Theorem 3 of Lecture 17 of El Gamal and Kim and its special cases.

## Main definitions

* `rcFunInfo p f W`: `I(U; Y₁ | X₁) + I(X; Y | X₁, U)` for `U = f(X, X₁)`.
* `rcDfInfo p W`: `I(X; Y₁ | X₁)`.
* `rcDfBound W`: the decode–forward lower bound.

## Main statements

* `rGapA_eq`, `rGapC_eq`, `rGapL_eq`: the gaps of the block code are the informations of the
  theorem.
* `isAchievableRC_of_nonpos`: rates `R ≤ 0` are achievable.
* `isAchievableRC_partialDF`: partial decode–forward for layered codebooks.
* `isAchievableRC_of_pmf`: **Theorem 3 of Lecture 17**.
* `isAchievableRC_of_fun`: the case where `U` is a function of `(X, X₁)`.
* `isAchievableRC_decodeForward`: **Theorem 2, decode–forward**.
* `isAchievableRC_multihop`: the coherent multi-hop lower bound.

## Implementation notes

The notes prove Theorem 2 by backward decoding, and outline Theorem 3 with binning and forward
decoding. Here backward decoding gives Theorem 3: the rates are limited by `R' < I(U; Y₁ | X₁)`,
`R'' < I(X; Y | X₁, U)` and `R' + R'' < I(X, X₁; Y)`, and no bins are needed. Theorem 2, the
multi-hop bounds and direct transmission are special cases, with `U = X` or with a constant `U`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X₁ U X Y Y₁ : Type*} [Fintype X₁] [Fintype U] [Fintype X] [Fintype Y] [Fintype Y₁]

/-! ### The informations -/

section Gaps

variable {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]

/-- A conditional mutual information in terms of entropies. -/
lemma condMutualInfo_eq_entropies {μ : Ω → ℝ} (hμ : IsPMF μ) (A : Ω → a) (B : Ω → b) (C : Ω → c) :
    I[A : B | C ; μ] = H[pair C A ; μ] - H[C ; μ] - H[pair (pair C B) A ; μ] + H[pair C B ; μ] := by
  have h₀ := condMutualInfo_eq' hμ A B C
  have h₁ := chain_rule hμ C A
  have h₂ := chain_rule hμ (pair C B) A
  rw [h₀]
  linarith

end Gaps

variable {L : ((X₁ × U) × X) × (Y × Y₁) → ℝ}

/-- The gap of a wrong `a'` is `I(U; Y₁ | X₁)`. -/
lemma rGapA_eq (hL : IsPMF L) :
    rGapA L = I[fun z => z.1.1.2 : fun z => z.2.2 | fun z => z.1.1.1 ; L] := by
  rw [condMutualInfo_eq_entropies hL, rGapA]
  have h₃ : H[pair (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1.1) (fun z => z.1.1.2) ; L] =
      H[fun z => z.1.1 ; L] := rfl
  have h₁ : H[pair (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1.1) (fun z => z.2.2) ; L] =
      H[fun z => (z.1.1.1, z.2.2) ; L] := rfl
  have h₂ : H[pair (pair (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1.1) (fun z => z.2.2))
      (fun z => z.1.1.2) ; L] = H[relayR₁ ; L] := rfl
  rw [h₁, h₂, h₃]
  ring

/-- The gap of a wrong `c'` is `I(X; Y | X₁, U)`. -/
lemma rGapC_eq (hL : IsPMF L) :
    rGapC L = I[fun z => z.1.2 : fun z => z.2.1 | fun z => z.1.1 ; L] := by
  rw [condMutualInfo_eq_entropies hL, rGapC]
  have h₃ : H[pair (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1) (fun z => z.1.2) ; L] =
      H[Prod.fst ; L] := rfl
  have h₁ : H[pair (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1) (fun z => z.2.1) ; L] =
      H[fun z => (z.1.1, z.2.1) ; L] := rfl
  have h₂ : H[pair (pair (fun z : ((X₁ × U) × X) × (Y × Y₁) => z.1.1) (fun z => z.2.1))
      (fun z => z.1.2) ; L] = H[relayRc ; L] := rfl
  rw [h₁, h₂, h₃]
  ring

/-- The gap of a wrong `l'` is `I(X₁, U, X; Y)`. -/
lemma rGapL_eq (hL : IsPMF L) : rGapL L = I[Prod.fst : fun z => z.2.1 ; L] := by
  rw [mutualInfo_eq_add_sub hL, rGapL]
  have h₁ : H[relayRl ; L] = H[pair (Prod.fst : ((X₁ × U) × X) × (Y × Y₁) → (X₁ × U) × X)
      (fun z => z.2.1) ; L] :=
    (entropyRV_eq_of_injective L (fun t : Y × ((X₁ × U) × X) => (t.2, t.1))
      (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl).symm
  rw [h₁]
  ring

variable {τ : X₁ → ℝ} {A : X₁ → U → ℝ} {B : X₁ × U → X → ℝ} {W : X × X₁ → Y × Y₁ → ℝ}

/-- `I(X₁, U, X; Y) = I(X, X₁; Y)`, since the channel depends only on `(X, X₁)`. -/
lemma rGapL_relayLaw (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    rGapL (relayLaw τ A B W) =
      rcMacInfo (dist (jointOf (jointOf τ A) B) fun t => (t.2, t.1.1)) W := by
  classical
  have hL := relayLaw_isPMF hτ hA hB hW
  rw [rGapL_eq hL, mutualInfo_eq_entropy_sub_condEntropy' hL]
  have hchan : ∀ (t : (X₁ × U) × X) (y : Y), dist (relayLaw τ A B W)
      (pair Prod.fst fun z => z.2.1) (t, y) =
      dist (relayLaw τ A B W) Prod.fst t *
        bcMarg₁ W ((fun t : (X₁ × U) × X => (t.2, t.1.1)) t) y := by
    intro t y
    rw [show (pair Prod.fst fun z : ((X₁ × U) × X) × (Y × Y₁) => z.2.1) =
      pair Prod.fst fun z => (Prod.snd z).1 from rfl, dist_pair_marg_fst, dist_pair_fst_snd]
    simp only [bcMarg₁, mul_sum, relayLaw, jointOf]
    have hm := (relayLaw_marg (τ := τ) hA hB hW).1
    rw [relayLaw] at hm
    rw [hm]
    rfl
  have h := entropy_sub_condEntropy_eq_mutualInfoOf (fun t : (X₁ × U) × X => (t.2, t.1.1)) hL
    hW.bcMarg₁ hchan
  rw [h, dist_comp_eq, (relayLaw_marg (τ := τ) hA hB hW).1]
  rfl

/-! ### Theorem 3 -/

section Theorem3

variable [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]

omit [Fintype X₁] [Fintype X] [Nonempty Y] [Nonempty Y₁] in
/-- Rates `R ≤ 0` are achievable, with one message. -/
lemma isAchievableRC_of_nonpos {W : X × X₁ → Y × Y₁ → ℝ} {R : ℝ} (hR : R ≤ 0) :
    IsAchievableRC W R := by
  classical
  refine ⟨fun N => Classical.arbitrary _, tendsto_const_nhds.congr fun N => ?_⟩
  have hc : ⌈(N : ℝ) * R⌉₊ = 0 :=
    Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hR)
  have hs : Subsingleton (Fin (2 ^ ⌈(N : ℝ) * R⌉₊)) := by
    rw [hc, pow_zero]
    infer_instance
  symm
  rw [RCCode.errProb_eq]
  exact sum_eq_zero fun ω _ => by rw [ind_of_neg (not_not.mpr (Subsingleton.elim _ _)), mul_zero]

/-- **Partial decode–forward** for layered codebooks. -/
theorem isAchievableRC_partialDF (hτ : IsPMF τ) (hA : IsChannel A) (hB : IsChannel B)
    (hW : IsChannel W) {R : ℝ}
    (h₁ : R * log 2 < rcMacInfo (dist (jointOf (jointOf τ A) B) fun t => (t.2, t.1.1)) W)
    (h₂ : R * log 2 < I[fun z => z.1.1.2 : fun z => z.2.2 | fun z => z.1.1.1 ; relayLaw τ A B W] +
      I[fun z => z.1.2 : fun z => z.2.1 | fun z => z.1.1 ; relayLaw τ A B W]) :
    IsAchievableRC W R := by
  by_cases hR : R ≤ 0
  · exact isAchievableRC_of_nonpos hR
  push Not at hR
  have hL := relayLaw_isPMF hτ hA hB hW
  rw [← rGapL_relayLaw hτ hA hB hW] at h₁
  rw [← rGapA_eq hL, ← rGapC_eq hL] at h₂
  set gA := rGapA (relayLaw τ A B W) with hgA
  set gC := rGapC (relayLaw τ A B W) with hgC
  set gL := rGapL (relayLaw τ A B W) with hgL
  have hgA0 : 0 ≤ gA := by
    rw [hgA, rGapA_eq hL]
    exact condMutualInfo_nonneg hL _ _ _
  have hgC0 : 0 ≤ gC := by
    rw [hgC, rGapC_eq hL]
    exact condMutualInfo_nonneg hL _ _ _
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hρ : 0 < R * log 2 := mul_pos hR hlog2
  set σ := gA + gC with hσ
  have hσpos : 0 < σ := hρ.trans h₂
  obtain ⟨t, ht₁, ht₂⟩ := exists_between (lt_min h₁ h₂)
  have htL : t < gL := ht₂.trans_le (min_le_left _ _)
  have htσ : t < σ := ht₂.trans_le (min_le_right _ _)
  have htpos : 0 < t := hρ.trans ht₁
  set θ := t / σ with hθ
  have hθ0 : 0 < θ := div_pos htpos hσpos
  have hθ1 : θ < 1 := (div_lt_one hσpos).mpr htσ
  have hsum : θ * gA + θ * gC = t := by
    rw [← mul_add, hθ]
    exact div_mul_cancel₀ _ hσpos.ne'
  refine isAchievableRC_of_blocks (R' := θ * gA) (R'' := θ * gC) (mul_nonneg hθ0.le hgA0)
    (mul_nonneg hθ0.le hgC0) (by rw [hsum]; exact ht₁) hW fun δ hδ =>
      eventually_relayBlock hτ hA hB hW (mul_nonneg hθ0.le hgA0) (mul_nonneg hθ0.le hgC0) ?_ ?_
        (by rw [hsum]; exact htL) hδ
  · rcases hgA0.eq_or_lt with h | h
    · exact Or.inl (by rw [← h, mul_zero])
    · refine Or.inr ?_
      nlinarith
  · rcases hgC0.eq_or_lt with h | h
    · exact Or.inl (by rw [← h, mul_zero])
    · refine Or.inr ?_
      nlinarith

/-- The law of `(X₁, U, X, Y, Y₁)` for a law `p(x₁, u, x)`. -/
def rcPdfLaw (q₃ : (X₁ × U) × X → ℝ) (W : X × X₁ → Y × Y₁ → ℝ) : ((X₁ × U) × X) × (Y × Y₁) → ℝ :=
  jointOf q₃ fun t => W (t.2, t.1.1)

/-- **Theorem 3 of Lecture 17 of [elgamal2010], page 17-33: the partial decode–forward lower
bound.** For any law `p(x₁, u, x)`, every rate `R`, in bits, with `R log 2 < I(X, X₁; Y)` and
`R log 2 < I(U; Y₁ | X₁) + I(X; Y | X₁, U)` is achievable. -/
theorem isAchievableRC_of_pmf [Nonempty U] {q₃ : (X₁ × U) × X → ℝ} (hq₃ : IsPMF q₃)
    (hW : IsChannel W) {R : ℝ} (h₁ : R * log 2 < rcMacInfo (dist q₃ fun t => (t.2, t.1.1)) W)
    (h₂ : R * log 2 < I[fun z => z.1.1.2 : fun z => z.2.2 | fun z => z.1.1.1 ; rcPdfLaw q₃ W] +
      I[fun z => z.1.2 : fun z => z.2.1 | fun z => z.1.1 ; rcPdfLaw q₃ W]) :
    IsAchievableRC W R := by
  obtain ⟨B', hB', hfB⟩ := exists_kernel hq₃
  have hq₃₂ : IsPMF (dist q₃ Prod.fst) := hq₃.dist _
  obtain ⟨A', hA', hfA⟩ := exists_kernel hq₃₂
  have hτ : IsPMF (dist (dist q₃ Prod.fst) Prod.fst) := hq₃₂.dist _
  have hfac : jointOf (jointOf (dist (dist q₃ Prod.fst) Prod.fst) A') B' = q₃ := by
    funext ⟨⟨s, u⟩, x⟩
    simp only [jointOf]
    rw [hfB (s, u) x, hfA s u]
  have hlaw : relayLaw (dist (dist q₃ Prod.fst) Prod.fst) A' B' W = rcPdfLaw q₃ W := by
    rw [relayLaw, hfac, rcPdfLaw]
  refine isAchievableRC_partialDF hτ hA' hB' hW ?_ ?_
  · rw [hfac]
    exact h₁
  · rw [hlaw]
    exact h₂

end Theorem3

/-! ### `U` is a function of `(X, X₁)` -/

section Fun

variable {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]

/-- A conditional mutual information under a pushforward. -/
lemma condMutualInfo_dist {Ω' : Type*} [Fintype Ω'] {μ : Ω → ℝ} (hμ : IsPMF μ) (T : Ω → Ω')
    (A : Ω' → a) (B : Ω' → b) (C : Ω' → c) :
    I[A : B | C ; dist μ T] = I[A ∘ T : B ∘ T | C ∘ T ; μ] := by
  rw [condMutualInfo_eq_entropies (hμ.dist T), condMutualInfo_eq_entropies hμ]
  simp only [entropyRV_dist]
  rfl

end Fun

variable [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁] {p : X × X₁ → ℝ}

/-- `I(U; Y₁ | X₁) + I(X; Y | X₁, U)` for `U = f(X, X₁)`, in nats. -/
def rcFunInfo (p : X × X₁ → ℝ) (f : X × X₁ → U) (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  I[fun z : (X × X₁) × (Y × Y₁) => f z.1 : fun z => z.2.2 | fun z => z.1.2 ; jointOf p W] +
    I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 | fun z => (z.1.2, f z.1) ; jointOf p W]

/-- **Theorem 3 for `U = f(X, X₁)`.** -/
theorem isAchievableRC_of_fun [Nonempty U] (hp : IsPMF p) (hW : IsChannel W) (f : X × X₁ → U)
    {R : ℝ} (h₁ : R * log 2 < rcMacInfo p W) (h₂ : R * log 2 < rcFunInfo p f W) :
    IsAchievableRC W R := by
  classical
  have hJ := jointOf_isPMF hp hW
  let g : X × X₁ → (X₁ × U) × X := fun a => ((a.2, f a), a.1)
  let T : (X × X₁) × (Y × Y₁) → ((X₁ × U) × X) × (Y × Y₁) := fun z => (g z.1, z.2)
  have hg : dist (dist p g) (fun t => (t.2, t.1.1)) = p := by
    rw [← dist_comp_eq]
    exact dist_id p
  have hginj : Function.Injective g := fun a b h => by
    have h₁ := congrArg Prod.snd h
    have h₂ := congrArg (fun t => t.1.1) h
    exact Prod.ext h₁ h₂
  have hTinj : Function.Injective T := fun a b h => by
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (hginj h₁) h₂
  have hlaw : rcPdfLaw (dist p g) W = dist (jointOf p W) T := by
    funext ⟨t, o⟩
    by_cases ht : ∃ a, g a = t
    · obtain ⟨a, rfl⟩ := ht
      have h₁ := dist_comp_of_injective (jointOf p W) id hTinj (a, o)
      have h₂ := dist_comp_of_injective p id hginj a
      rw [dist_id] at h₁ h₂
      simp only [rcPdfLaw, jointOf]
      have e₁ : dist p g (g a) = p a := h₂
      have e₂ : dist (jointOf p W) T (g a, o) = jointOf p W (a, o) := h₁
      rw [e₁, e₂]
      rfl
    · have h₁ : dist p g t = 0 := by
        simp only [dist]
        refine sum_eq_zero fun a _ => ite_eq_right fun h => ht ⟨a, h⟩
      have h₂ : dist (jointOf p W) T (t, o) = 0 := by
        simp only [dist]
        refine sum_eq_zero fun z _ => ite_eq_right fun h => ht ⟨z.1, congrArg Prod.fst h⟩
      simp only [rcPdfLaw, jointOf, h₁, h₂, zero_mul]
  refine isAchievableRC_of_pmf (hp.dist g) hW (by rw [hg]; exact h₁) ?_
  rw [hlaw, condMutualInfo_dist hJ, condMutualInfo_dist hJ]
  exact h₂

/-! ### Decode–forward -/

/-- `I(X; Y₁ | X₁)`, in nats. -/
def rcDfInfo (p : X × X₁ → ℝ) (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.2 | fun z => z.1.2 ; jointOf p W]

omit [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁] in
/-- `I(X; Y | X₁, X) = 0`. -/
lemma rcFunInfo_fst (hp : IsPMF p) (hW : IsChannel W) : rcFunInfo p Prod.fst W = rcDfInfo p W := by
  have hJ := jointOf_isPMF hp hW
  simp only [rcFunInfo, rcDfInfo]
  have hzero : I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 |
      fun z => (z.1.2, z.1.1) ; jointOf p W] = 0 := by
    rw [condMutualInfo_eq' hJ]
    have h₁ := condEntropy_comp_self hJ (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.1.1))
      (Prod.snd : X₁ × X → X)
    have h₂ := condEntropy_comp_self hJ (pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.1.1))
      fun z => z.2.1) (fun t : (X₁ × X) × Y => t.1.2)
    have e₁ : H[fun z : (X × X₁) × (Y × Y₁) => z.1.1 | fun z => (z.1.2, z.1.1) ; jointOf p W] = 0 :=
      h₁
    have e₂ : H[fun z : (X × X₁) × (Y × Y₁) => z.1.1 | pair (fun z => (z.1.2, z.1.1))
        (fun z => z.2.1) ; jointOf p W] = 0 := h₂
    rw [e₁, e₂, sub_zero]
  rw [hzero, add_zero]

/-- **Theorem 2 of Lecture 17 of [elgamal2010], page 17-18: decode–forward.** For any input law,
every rate `R`, in bits, with `R log 2 < I(X, X₁; Y)` and `R log 2 < I(X; Y₁ | X₁)` is
achievable. -/
theorem isAchievableRC_decodeForward (hp : IsPMF p) (hW : IsChannel W) {R : ℝ}
    (h₁ : R * log 2 < rcMacInfo p W) (h₂ : R * log 2 < rcDfInfo p W) : IsAchievableRC W R :=
  isAchievableRC_of_fun hp hW Prod.fst h₁ (by rw [rcFunInfo_fst hp hW]; exact h₂)

/-- **Theorem 2 of Lecture 17 of [elgamal2010], page 17-18.** The decode–forward lower bound
`max_{p(x, x₁)} min {I(X, X₁; Y), I(X; Y₁ | X₁)}`, in nats. -/
def rcDfBound (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  sSup {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧ v = min (rcMacInfo p W) (rcDfInfo p W)}

/-- **Theorem 2**, with the maximum over the input laws. -/
theorem isAchievableRC_of_lt_rcDfBound (hW : IsChannel W) {R : ℝ} (h : R * log 2 < rcDfBound W) :
    IsAchievableRC W R := by
  have hne : {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧ v = min (rcMacInfo p W) (rcDfInfo p W)}.Nonempty :=
    ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩
  obtain ⟨_, ⟨p, hp, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne h
  exact isAchievableRC_decodeForward hp hW (hv.trans_le (min_le_left _ _))
    (hv.trans_le (min_le_right _ _))

omit [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁] in
/-- `I(X, X₁; Y)` as a mutual information under the joint law. -/
lemma rcMacInfo_eq (p : X × X₁ → ℝ) :
    rcMacInfo p W = I[Prod.fst : fun z : (X × X₁) × (Y × Y₁) => z.2.1 ; jointOf p W] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  funext ⟨a, y⟩
  rw [dist_pair_fst_snd, show (pair Prod.fst fun z : (X × X₁) × (Y × Y₁) => z.2.1) =
    pair Prod.fst fun z => (Prod.snd z).1 from rfl, dist_pair_marg_fst, dist_pair_fst_snd]
  simp only [jointOf, bcMarg₁, mul_sum]

/-- **The coherent multi-hop lower bound, page 17-14 of [elgamal2010].** For any input law, every
rate `R`, in bits, with `R log 2 < I(X₁; Y)` and `R log 2 < I(X; Y₁ | X₁)` is achievable. The simple
multi-hop lower bound of page 17-10 is the case of a product law. -/
theorem isAchievableRC_multihop (hp : IsPMF p) (hW : IsChannel W) {R : ℝ}
    (h₁ : R * log 2 < I[fun z : (X × X₁) × (Y × Y₁) => z.1.2 : fun z => z.2.1 ; jointOf p W])
    (h₂ : R * log 2 < rcDfInfo p W) : IsAchievableRC W R := by
  have hJ := jointOf_isPMF hp hW
  refine isAchievableRC_decodeForward hp hW (lt_of_lt_of_le h₁ ?_) h₂
  have h := mutualInfo_comp_le hJ (fun z : (X × X₁) × (Y × Y₁) => z.2.1) Prod.fst
    (Prod.snd : X × X₁ → X₁)
  rw [rcMacInfo_eq, mutualInfo_comm hJ Prod.fst, mutualInfo_comm hJ (fun z => z.1.2)]
  exact h

end InfoTheory
