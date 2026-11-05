/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayCFRate

/-!
# The compress–forward lower bound

## Main statements

* `isAchievableRC_of_cfBlocks`: codes for one block give achievable rates.
* `isAchievableRC_compressForward`: **Theorem 4, the compress–forward lower bound**.
* `isAchievableRC_compressForward_original`: the original characterization of the bound.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X U Y S V : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype S] [Fintype V]
  {p : X → ℝ} {p₁ : U → ℝ} {W : X × U → Y × S → ℝ} {τ : U × S → V → ℝ}

omit [Fintype X] [Fintype U] in
/-- **Codes for one block of compress–forward give achievable rates.** -/
theorem isAchievableRC_of_cfBlocks [Nonempty X] [Nonempty U] [Nonempty Y] [Nonempty S]
    {R₀ R₁ R : ℝ} (hR₀ : 0 ≤ R₀) (hR : R * log 2 < R₀) (hW : IsChannel W)
    (hblock : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, ∃ C : CFBlock ⌈exp (n * R₀)⌉₊ ⌈exp (n * R₁)⌉₊ n X U Y S,
    C.avgErr (relaySeq W n) ≤ δ) : IsAchievableRC W R := by
  classical
  refine isAchievableRC_of_codes hR₀ hR hW fun B₁ _ ε hε => ?_
  have hB₁pos : (0 : ℝ) < (B₁ : ℝ) + 1 := by positivity
  have hδ : 0 < ε / ((B₁ : ℝ) + 1) := by positivity
  filter_upwards [hblock _ hδ, eventually_gt_atTop 0] with n ⟨C, hC⟩ hn0
  have hnpos : NeZero n := ⟨hn0.ne'⟩
  set M₀ := ⌈exp (n * R₀)⌉₊ ^ B₁ with hM₀
  have hM₀pos : 0 < M₀ := by
    have : 0 < ⌈exp (n * R₀)⌉₊ := NeZero.pos _
    positivity
  have hexp : exp ((B₁ : ℝ) * ((n : ℝ) * R₀)) ≤ (M₀ : ℝ) := by
    have h₁ : exp (n * R₀) ≤ ((⌈exp (n * R₀)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    rw [exp_nat_mul, hM₀]
    push_cast
    exact pow_le_pow_left₀ (exp_pos _).le h₁ _
  let e : Fin M₀ ≃ (Fin B₁ → Fin ⌈exp (n * R₀)⌉₊) := (Fintype.equivFinOfCardEq (by simp [hM₀])).symm
  obtain ⟨m₀, d, hc⟩ := C.exists_code_le (W := W) hW e (Classical.arbitrary S) (Classical.arbitrary
    Y)
  refine ⟨M₀, C.code e m₀ d (Classical.arbitrary S) (Classical.arbitrary Y), hM₀pos, hexp,
    hc.trans ?_⟩
  calc _ ≤ ((B₁ : ℝ) + 1) * (ε / ((B₁ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hC hB₁pos.le
    _ = ε := by field_simp

section Gaps

/-- The two inputs are independent. -/
lemma cfLaw_entropy_inputs (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) :
    H[fun z => z.1.1 ; cfLaw p p₁ W τ] =
      H[fun z => z.1.1.1 ; cfLaw p p₁ W τ] + H[fun z => z.1.1.2 ; cfLaw p p₁ W τ] := by
  obtain ⟨hmx, hmu⟩ := cfLaw_marg (p := p) (p₁ := p₁) (W := W) (τ := τ) hp hp₁ hW hτ
  have h₁ : dist (cfLaw p p₁ W τ) (fun z => z.1.1) = prodDist p p₁ := by
    have := cfLaw_dist_inputs (p := p) (p₁ := p₁) (W := W) (τ := τ) hW hτ (id : X × U → X × U)
    rw [show dist (prodDist p p₁) (id : X × U → X × U) = prodDist p p₁ from dist_id _] at this
    exact this
  simp only [entropyRV, h₁, hmx, hmu]
  exact entropy_prodDist hp hp₁

/-- The gap of a wrong message is `I(X; Y, Ŷ₁ | X₁)`. -/
lemma cfGapX_eq (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) :
    cfGapX (cfLaw p p₁ W τ) =
      I[fun z => z.1.1.1 : fun z => (z.1.2.1, z.2) | fun z => z.1.1.2 ; cfLaw p p₁ W τ] := by
  have hμ := cfLaw_isPMF hp hp₁ hW hτ
  have hin := cfLaw_entropy_inputs hp hp₁ hW hτ
  set μ := cfLaw p p₁ W τ
  rw [condMutualInfo_eq_entropies hμ, cfGapX]
  have h₁ : H[pair (fun z : ((X × U) × (Y × S)) × V => z.1.1.2) (fun z => z.1.1.1) ; μ] =
      H[fun z => z.1.1 ; μ] :=
    entropyRV_eq_of_injective μ (fun t : X × U => (t.2, t.1))
      (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl
  have h₂ : H[pair (pair (fun z : ((X × U) × (Y × S)) × V => z.1.1.2) fun z => (z.1.2.1, z.2))
      (fun z => z.1.1.1) ; μ] = H[cfF₂ ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (U × V × Y) × X => ((t.1.1, (t.1.2.2, t.1.2.1)), t.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 (Prod.ext h.1.2.2 h.1.2.1)) h.2) fun _ => rfl
  have h₃ : H[pair (fun z : ((X × U) × (Y × S)) × V => z.1.1.2) (fun z => (z.1.2.1, z.2)) ; μ] =
      H[fun z => (z.1.1.2, z.2, z.1.2.1) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : U × V × Y => (t.1, (t.2.2, t.2.1)))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)) fun _ => rfl
  rw [h₁, h₂, h₃, hin]
  ring

/-- `H(Ŷ₁ | X, X₁, Y, Y₁) = H(Ŷ₁ | X₁, Y₁)`. -/
lemma cfLaw_markov (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) :
    entropy (cfLaw p p₁ W τ) - H[Prod.fst ; cfLaw p p₁ W τ] =
      H[cfFJ ; cfLaw p p₁ W τ] - H[fun z => (z.1.1.2, z.1.2.2) ; cfLaw p p₁ W τ] := by
  have hμ := cfLaw_isPMF hp hp₁ hW hτ
  set μ := cfLaw p p₁ W τ with hμd
  have h₁ := chain_rule hμ (Prod.fst : ((X × U) × (Y × S)) × V → _) Prod.snd
  have h₂ := chain_rule hμ (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2)) Prod.snd
  have hd : dist μ (pair Prod.fst Prod.snd) = jointOf (dist μ Prod.fst)
      fun v : (X × U) × (Y × S) => τ ((fun t : (X × U) × (Y × S) => (t.1.2, t.2.2)) v) := by
    have hf : dist μ Prod.fst = jointOf (prodDist p p₁) W := dist_jointOf_fst fun _ => hτ _
    have : (pair Prod.fst Prod.snd : ((X × U) × (Y × S)) × V → _) = id := rfl
    rw [hf, this, dist_id]
    rfl
  have h₃ := condEntropy_eq_comp_of_channel hμ Prod.fst Prod.snd
    (fun t : (X × U) × (Y × S) => (t.1.2, t.2.2)) hτ hd
  have e₁ : H[pair (Prod.fst : ((X × U) × (Y × S)) × V → _) Prod.snd ; μ] = entropy μ := by
    have : (pair Prod.fst Prod.snd : ((X × U) × (Y × S)) × V → _) = id := rfl
    simp only [entropyRV, this, dist_id]
  have e₂ : H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2)) Prod.snd ; μ] =
      H[cfFJ ; μ] := rfl
  rw [e₁] at h₁
  rw [e₂] at h₂
  have e₃ : H[Prod.snd | (fun t : (X × U) × (Y × S) => (t.1.2, t.2.2)) ∘ Prod.fst ; μ] =
      H[Prod.snd | fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2) ; μ] := rfl
  rw [e₃] at h₃
  linarith

/-- The sum of the gaps is the first term of the compress–forward lower bound. -/
lemma cfGap_sum (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) :
    cfGapW (cfLaw p p₁ W τ) + cfGapV (cfLaw p p₁ W τ) + cfGapU (cfLaw p p₁ W τ) -
        cfGapC (cfLaw p p₁ W τ) =
      I[fun z => z.1.1 : fun z => z.1.2.1 ; cfLaw p p₁ W τ] -
        I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ; cfLaw p p₁ W τ] := by
  have hμ := cfLaw_isPMF hp hp₁ hW hτ
  have hin := cfLaw_entropy_inputs hp hp₁ hW hτ
  have hmk := cfLaw_markov hp hp₁ hW hτ
  set μ := cfLaw p p₁ W τ
  rw [mutualInfo_eq_add_sub hμ, condMutualInfo_eq_entropies hμ]
  simp only [cfGapW, cfGapV, cfGapU, cfGapC]
  have h₁ : H[cfF₁ ; μ] = H[fun z => (z.1.1.2, z.1.2.1) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : U × Y => (t.2, t.1))
      (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl
  have h₂ : H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1, z.1.2.1)) (fun z => z.1.2.2) ; μ] =
      H[Prod.fst ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (X × U) × (Y × S) => ((t.1, t.2.1), t.2.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) fun _ => rfl
  have h₃ : H[pair (pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1, z.1.2.1)) fun z => z.2)
      (fun z => z.1.2.2) ; μ] = entropy μ := by
    have := entropyRV_eq_of_injective (Y := pair (pair (fun z : ((X × U) × (Y × S)) × V =>
      (z.1.1, z.1.2.1)) fun z => z.2) (fun z => z.1.2.2)) μ (X := id)
      (fun t : ((X × U) × (Y × S)) × V => (((t.1.1, t.1.2.1), t.2), t.1.2.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1.1 (Prod.ext h.1.1.2 h.2)) h.1.2) fun _ => rfl
    rw [this]
    simp only [entropyRV, dist_id]
  have h₄ : H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1, z.1.2.1)) (fun z => z.2) ; μ] =
      H[cfF₃ ; μ] :=
    entropyRV_eq_of_injective μ (fun t : ((U × Y) × X) × V => (((t.1.2, t.1.1.1), t.1.1.2), t.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext (Prod.ext h.1.1.2 h.1.2) h.1.1.1) h.2) fun _ => rfl
  have h₅ : H[pair (fun z : ((X × U) × (Y × S)) × V => z.1.1) (fun z => z.1.2.1) ; μ] =
      H[fun z => (z.1.1, z.1.2.1) ; μ] := rfl
  rw [h₁, h₂, h₃, h₄, h₅, hin]
  linarith

/-- The gap of a wrong state is nonnegative. -/
lemma cfGapU_nonneg {μ : ((X × U) × (Y × S)) × V → ℝ} (hμ : IsPMF μ) : 0 ≤ cfGapU μ := by
  have h := mutualInfo_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.1.2.1) (fun z => z.1.1.2)
  rw [mutualInfo_eq_add_sub hμ] at h
  exact h

end Gaps

/-- **Theorem 4 (compress–forward lower bound), page 17-39 of [elgamal2010].** For
`p(x) p(x₁) p(ŷ₁ | y₁, x₁)`, every rate with
`R < min {I(X, X₁; Y) - I(Y₁; Ŷ₁ | X, X₁, Y), I(X; Y, Ŷ₁ | X₁)}` is achievable. -/
theorem isAchievableRC_compressForward [Nonempty X] [Nonempty U] [Nonempty Y] [Nonempty S]
    [Nonempty V] (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) {R : ℝ}
    (hR₁ : R * log 2 < I[fun z => z.1.1 : fun z => z.1.2.1 ; cfLaw p p₁ W τ] -
      I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ; cfLaw p p₁ W τ])
    (hR₂ : R * log 2 <
      I[fun z => z.1.1.1 : fun z => (z.1.2.1, z.2) | fun z => z.1.1.2 ; cfLaw p p₁ W τ]) :
    IsAchievableRC W R := by
  classical
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  rcases le_or_gt R 0 with hR0 | hR0
  · exact isAchievableRC_of_nonpos hR0
  have hμ := cfLaw_isPMF hp hp₁ hW hτ
  rw [← cfGap_sum hp hp₁ hW hτ] at hR₁
  rw [← cfGapX_eq hp hp₁ hW hτ] at hR₂
  have hC0 := cfGapC_nonneg hμ
  have hU0 := cfGapU_nonneg hμ
  set μ := cfLaw p p₁ W τ with hμd
  set A := cfGapW μ + cfGapV μ + cfGapU μ - cfGapC μ with hA
  -- the rates
  obtain ⟨R₀, hR₀l, hR₀r⟩ := exists_between (lt_min hR₁ hR₂)
  have hR₀A : R₀ < A := hR₀r.trans_le (min_le_left _ _)
  have hR₀X : R₀ < cfGapX μ := hR₀r.trans_le (min_le_right _ _)
  have hR₀0 : 0 ≤ R₀ := (mul_pos hR0 hlog2).le.trans hR₀l.le
  set θ := A - R₀ with hθ
  have hθ0 : 0 < θ := sub_pos.mpr hR₀A
  set R₁ := max (cfGapU μ - θ / 3) 0 with hR₁d
  set R₂ := cfGapC μ + θ / 3 with hR₂d
  refine isAchievableRC_of_cfBlocks (R₁ := R₁) hR₀0 hR₀l hW fun δ hδ => ?_
  refine eventually_cfBlock (R₂ := R₂) hp hp₁ hW hτ (by positivity) ?_ hR₀X
    (by rw [hR₂d]; linarith) ?_ hδ
  · by_cases h : cfGapU μ - θ / 3 ≤ 0
    · exact Or.inl (max_eq_right h)
    · push Not at h
      right
      rw [hR₁d, max_eq_left h.le]
      linarith
  · have h₁ : cfGapU μ - θ / 3 ≤ R₁ := le_max_left _ _
    rw [hR₂d]
    have : A = R₀ + θ := by rw [hθ]; ring
    rw [hA] at this
    linarith

/-- The difference of the two terms of the compress–forward lower bound, page 17-90 of
[elgamal2010]. -/
lemma cf_terms_sub (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) :
    (I[fun z => z.1.1 : fun z => z.1.2.1 ; cfLaw p p₁ W τ] -
        I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ; cfLaw p p₁ W τ]) -
      I[fun z => z.1.1.1 : fun z => (z.1.2.1, z.2) | fun z => z.1.1.2 ; cfLaw p p₁ W τ] =
    I[fun z => z.1.1.2 : fun z => z.1.2.1 ; cfLaw p p₁ W τ] -
      I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1.2, z.1.2.1) ; cfLaw p p₁ W τ] := by
  have hμ := cfLaw_isPMF hp hp₁ hW hτ
  rw [← cfGap_sum hp hp₁ hW hτ, ← cfGapX_eq hp hp₁ hW hτ]
  have hmk := cfLaw_markov hp hp₁ hW hτ
  set μ := cfLaw p p₁ W τ
  rw [mutualInfo_eq_add_sub hμ, condMutualInfo_eq_entropies hμ]
  simp only [cfGapW, cfGapV, cfGapU, cfGapC, cfGapX]
  -- the conditional independence
  have hc₁ := condMutualInfo_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.2) (fun z => z.1.2.1)
    (fun z => (z.1.1.2, z.1.2.2))
  have hc₂ := condMutualInfo_nonneg hμ (fun z : ((X × U) × (Y × S)) × V => z.2) (fun z => z.1.1.1)
    (fun z => ((z.1.1.2, z.1.2.2), z.1.2.1))
  rw [condMutualInfo_eq_entropies hμ] at hc₁ hc₂
  have e₀ : H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2)) (fun z => z.2) ; μ] =
      H[cfFJ ; μ] := rfl
  have e₁ : H[pair (pair (fun z : ((X × U) × (Y × S)) × V => ((z.1.1.2, z.1.2.2), z.1.2.1))
      (fun z => z.1.1.1)) (fun z => z.2) ; μ] = entropy μ := by
    have := entropyRV_eq_of_injective (Y := pair (pair (fun z : ((X × U) × (Y × S)) × V =>
      ((z.1.1.2, z.1.2.2), z.1.2.1)) (fun z => z.1.1.1)) (fun z => z.2)) μ (X := id)
      (fun t : ((X × U) × (Y × S)) × V => ((((t.1.1.2, t.1.2.2), t.1.2.1), t.1.1.1), t.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext (Prod.ext h.1.2 h.1.1.1.1) (Prod.ext h.1.1.2 h.1.1.1.2)) h.2)
      fun _ => rfl
    rw [this]
    simp only [entropyRV, dist_id]
  have e₂ : H[pair (fun z : ((X × U) × (Y × S)) × V => ((z.1.1.2, z.1.2.2), z.1.2.1))
      (fun z => z.1.1.1) ; μ] = H[Prod.fst ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (X × U) × (Y × S) => (((t.1.2, t.2.2), t.2.1), t.1.1))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.2 h.1.1.1) (Prod.ext h.1.2 h.1.1.2)) fun _ => rfl
  have e₃ : H[pair (pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2)) fun z => z.1.2.1)
      (fun z => z.2) ; μ] = H[pair (fun z : ((X × U) × (Y × S)) × V => ((z.1.1.2, z.1.2.2),
        z.1.2.1))
        (fun z => z.2) ; μ] := rfl
  have e₄ : H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.1)) (fun z => z.1.2.2) ; μ] =
      H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2)) (fun z => z.1.2.1) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (U × S) × Y => ((t.1.1, t.2), t.1.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1 h.2) h.1.2) fun _ => rfl
  have e₅ : H[pair (pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.1)) fun z => z.2)
      (fun z => z.1.2.2) ; μ] = H[pair (fun z : ((X × U) × (Y × S)) × V =>
        ((z.1.1.2, z.1.2.2), z.1.2.1)) (fun z => z.2) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : ((U × S) × Y) × V => (((t.1.1.1, t.1.2), t.2), t.1.1.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext (Prod.ext h.1.1.1 h.2) h.1.1.2) h.1.2) fun _ => rfl
  have e₆ : H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.1)) (fun z => z.2) ; μ] =
      H[fun z => (z.1.1.2, z.2, z.1.2.1) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : U × V × Y => ((t.1, t.2.2), t.2.1))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.1 (Prod.ext h.2 h.1.2)) fun _ => rfl
  have e₇ : H[cfF₃ ; μ] = H[cfF₂ ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (U × V × Y) × X => (((t.1.1, t.1.2.2), t.2), t.1.2.1))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Prod.ext h.1.1.1 (Prod.ext h.2 h.1.1.2)) h.1.2) fun _ => rfl
  have e₈ : H[cfF₁ ; μ] = H[fun z => (z.1.1.2, z.1.2.1) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : U × Y => (t.2, t.1))
      (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl
  have e₉ : H[pair (fun z : ((X × U) × (Y × S)) × V => z.1.1.2) (fun z => z.1.2.1) ; μ] =
      H[fun z => (z.1.1.2, z.1.2.1) ; μ] := rfl
  rw [e₀] at hc₁
  rw [e₁, e₂] at hc₂
  rw [e₃] at hc₁
  have e₁₀ : H[fun z : ((X × U) × (Y × S)) × V => ((z.1.1.2, z.1.2.2), z.1.2.1) ; μ] =
      H[pair (fun z : ((X × U) × (Y × S)) × V => (z.1.1.2, z.1.2.2)) (fun z => z.1.2.1) ; μ] := rfl
  rw [e₁₀] at hc₂
  rw [e₄, e₅, e₆, e₇, e₈, e₉]
  linarith

/-- **The original characterization of the compress–forward lower bound, page 17-46 of
[elgamal2010].** Every rate `R < I(X; Y, Ŷ₁ | X₁)` is achievable, if
`I(X₁; Y) ≥ I(Y₁; Ŷ₁ | X₁, Y)`. -/
theorem isAchievableRC_compressForward_original [Nonempty X] [Nonempty U] [Nonempty Y] [Nonempty S]
    [Nonempty V] (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) {R : ℝ}
    (hc : I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1.2, z.1.2.1) ; cfLaw p p₁ W τ] ≤
      I[fun z => z.1.1.2 : fun z => z.1.2.1 ; cfLaw p p₁ W τ])
    (hR : R * log 2 <
      I[fun z => z.1.1.1 : fun z => (z.1.2.1, z.2) | fun z => z.1.1.2 ; cfLaw p p₁ W τ]) :
    IsAchievableRC W R := by
  have h := cf_terms_sub (p := p) (p₁ := p₁) (W := W) (τ := τ) hp hp₁ hW hτ
  exact isAchievableRC_compressForward hp hp₁ hW hτ (by linarith) hR

end InfoTheory
