/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MDOuter
public import InfoTheoryLib.Network.ZhangBerger

/-!
# The El Gamal–Cover inner bound and the tight cases of multiple descriptions

The Zhang–Berger inner bound gives the El Gamal–Cover inner bound, Theorem 1 of Lecture 14 of
El Gamal and Kim, when the common description `U` is the time sharing variable `Q`, which is
independent of `X`. Together with the simple outer bound, this gives the rate–distortion regions of
the special cases of the notes.

A decoder is removed by giving it the reproduction alphabet `Unit` and the distortion measure `0`,
which is what `Dⱼ = ∞` means in the notes.

## Main definitions

* `margCh κ g`: the channel `p(g(y)|x)` of a function of the output of `κ`.
* `srRegion P d₀ d₁ D₀ D₁`: the successive refinement region `R(D₀, D₁)`.
* `IsSuccessivelyRefinable P d`: a source that is successively refinable.

## Main statements

* `isAchievableMD_elGamalCover`: **the El Gamal–Cover inner bound**, Theorem 1 of the notes.
* `mem_mdRegion_of_le`: the inner bound for the closure, with `Q` constant.
* `infoRD_le_of_mem_mdRegion₀`, `₁`, `₂`: `R₁ + R₂ ≥ R(D₀)`, `R₁ ≥ R(D₁)` and `R₂ ≥ R(D₂)`.
* `mem_mdRegion_no_combined_iff`, `mem_mdRegion_combined_only_iff`: special cases 1 and 3.
* `mem_srRegion_iff`: **successive refinement**, Theorem 3 of the notes.
* `mem_srRegion_zero_iff`: special case 2.
* `isSuccessivelyRefinable_iff`: **Proposition 1 of the notes**.
* `isAchievableMD_of_auxiliary`: the alternative form of the Zhang–Berger inner bound.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 14
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α υ β₀ β₁ β₂ : Type*} [Fintype Ω] [Fintype α] [Fintype υ] [Fintype β₀] [Fintype β₁]
  [Fintype β₂] {μ : Ω → ℝ} {X : Ω → α} {Y₀ : Ω → β₀} {Y₁ : Ω → β₁} {Y₂ : Ω → β₂}
  {d₀ : α → β₀ → ℝ} {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ}

/-! ### The El Gamal–Cover inner bound -/

section Inner

omit [Fintype α] in
/-- `I(X; c) = 0` for a constant `c`. -/
lemma mutualInfo_const_right' {σ : Type*} [Fintype σ] (hμ : IsPMF μ) (A : Ω → σ) (c : υ) :
    I[A : fun _ => c ; μ] = 0 := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, condEntropy_const hμ, sub_self]

/-- **Theorem 1 of Lecture 14 of [elgamal2010], page 14-7: the El Gamal–Cover inner bound.** Let `Q`
be independent of `X`. A rate pair `(R₁, R₂)`, in bits, is achievable with `(D₀, D₁, D₂)` if
`R₁ > I(X; X̂₁|Q)`, `R₂ > I(X; X̂₂|Q)`, `R₁ + R₂ > I(X; X̂₀, X̂₁, X̂₂|Q) + I(X̂₁; X̂₂|Q)` and
`E dⱼ(X, X̂ⱼ) ≤ Dⱼ`. This is the Zhang–Berger inner bound for `U = Q`, so no separate time sharing
argument is needed. -/
theorem isAchievableMD_elGamalCover (hμ : IsPMF μ) (hd₀ : ∀ a b, 0 ≤ d₀ a b)
    (hd₁ : ∀ a b, 0 ≤ d₁ a b) (hd₂ : ∀ a b, 0 ≤ d₂ a b) {Q : Ω → υ} (hQ : I[Q : X ; μ] = 0)
    {R₁ R₂ D₀ D₁ D₂ : ℝ} (h₁ : I[X : Y₁ | Q ; μ] < R₁ * log 2) (h₂ : I[X : Y₂ | Q ; μ] < R₂ * log 2)
    (h₁₂ : I[X : pair Y₀ (pair Y₁ Y₂) | Q ; μ] + I[Y₁ : Y₂ | Q ; μ] < (R₁ + R₂) * log 2)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂) :
    IsAchievableMD (dist μ X) d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  have hQ' : I[X : Q ; μ] = 0 := by rw [mutualInfo_comm hμ, hQ]
  refine isAchievableMD_zhangBerger (U := Q) hμ hd₀ hd₁ hd₂ ?_ ?_ ?_ hc₀ hc₁ hc₂
  · rw [chain_rule_mutualInfo₂ hμ, hQ', zero_add]
    exact h₁
  · rw [chain_rule_mutualInfo₂ hμ, hQ', zero_add]
    exact h₂
  · rw [hQ]
    linarith

/-- The El Gamal–Cover inner bound for a constant `Q`, on page 14-12 of the notes. -/
theorem isAchievableMD_of_lt (hμ : IsPMF μ) (hd₀ : ∀ a b, 0 ≤ d₀ a b)
    (hd₁ : ∀ a b, 0 ≤ d₁ a b) (hd₂ : ∀ a b, 0 ≤ d₂ a b) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h₁ : I[X : Y₁ ; μ] < R₁ * log 2) (h₂ : I[X : Y₂ ; μ] < R₂ * log 2)
    (h₁₂ : I[X : pair Y₀ (pair Y₁ Y₂) ; μ] + I[Y₁ : Y₂ ; μ] < (R₁ + R₂) * log 2)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂) :
    IsAchievableMD (dist μ X) d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  refine isAchievableMD_elGamalCover (Q := fun _ => ()) hμ hd₀ hd₁ hd₂ ?_ ?_ ?_ ?_ hc₀ hc₁ hc₂
  · rw [mutualInfo_comm hμ]
    exact mutualInfo_const_right' hμ X ()
  · rwa [condMutualInfo_const hμ]
  · rwa [condMutualInfo_const hμ]
  · rwa [condMutualInfo_const hμ, condMutualInfo_const hμ]

/-- **Lecture 14, page 14-7.** The inner bound with a constant `Q` for the closure: rate pairs on
the boundary of the bound are in the region. -/
theorem mem_mdRegion_of_le (hμ : IsPMF μ) (hd₀ : ∀ a b, 0 ≤ d₀ a b)
    (hd₁ : ∀ a b, 0 ≤ d₁ a b) (hd₂ : ∀ a b, 0 ≤ d₂ a b) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h₁ : I[X : Y₁ ; μ] ≤ R₁ * log 2) (h₂ : I[X : Y₂ ; μ] ≤ R₂ * log 2)
    (h₁₂ : I[X : pair Y₀ (pair Y₁ Y₂) ; μ] + I[Y₁ : Y₂ ; μ] ≤ (R₁ + R₂) * log 2)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂) :
    (R₁, R₂) ∈ mdRegion (dist μ X) d₀ d₁ d₂ D₀ D₁ D₂ := by
  have hl := log_pos one_lt_two
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hj : ∀ R : ℝ, Tendsto (fun k : ℕ => R + 1 / ((k : ℝ) + 1)) atTop (𝓝 R) := fun R => by
    simpa using tendsto_const_nhds.add h0
  refine mem_closure_of_tendsto ((hj R₁).prodMk_nhds (hj R₂)) (Eventually.of_forall fun k => ?_)
  have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hpl := mul_pos hp hl
  refine isAchievableMD_of_lt hμ hd₀ hd₁ hd₂ ?_ ?_ ?_ hc₀ hc₁ hc₂
  · simp only [add_mul]
    linarith
  · simp only [add_mul]
    linarith
  · simp only [add_mul] at h₁₂ ⊢
    linarith

omit [Fintype β₀] [Fintype β₁] [Fintype β₂] in
/-- The rates of the region are nonnegative. -/
lemma mdRegion_nonneg {P : α → ℝ} {D₀ D₁ D₂ : ℝ} {R : ℝ × ℝ}
    (h : R ∈ mdRegion P d₀ d₁ d₂ D₀ D₁ D₂) : 0 ≤ R.1 ∧ 0 ≤ R.2 := by
  have hc : IsClosed {R : ℝ × ℝ | 0 ≤ R.1 ∧ 0 ≤ R.2} :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  have hsub : {R : ℝ × ℝ | IsAchievableMD P d₀ d₁ d₂ R.1 R.2 D₀ D₁ D₂} ⊆
      {R : ℝ × ℝ | 0 ≤ R.1 ∧ 0 ≤ R.2} := fun R' hR' => ⟨hR'.1, hR'.2.1⟩
  exact closure_minimal hsub hc h

end Inner

/-! ### Channels of functions of the output -/

section Marg

variable {B B' : Type*} [Fintype B] [Fintype B'] {P : α → ℝ}

/-- The channel `p(g(y)|x)` of a function of the output of `κ`. -/
def margCh (κ : α → B → ℝ) (g : B → B') : α → B' → ℝ := fun a => dist (κ a) g

omit [Fintype α] in
lemma margCh_isChannel {κ : α → B → ℝ} (h : IsChannel κ) (g : B → B') : IsChannel (margCh κ g) :=
  fun a => (h a).dist g

omit [Fintype B'] in
lemma jointOf_margCh [Finite B'] (κ : α → B → ℝ) (g : B → B') :
    jointOf P (margCh κ g) = dist (jointOf P κ) (fun z => (z.1, g z.2)) := by
  classical
  funext ⟨a, b'⟩
  simp only [jointOf, margCh, dist, Fintype.sum_prod_type]
  rw [sum_eq_single a]
  · rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    by_cases h : g b = b'
    · simp [h]
    · simp [h]
  · intro a' _ ha'
    refine sum_eq_zero fun b _ => ?_
    simp [ha']
  · simp

/-- The expected costs of `margCh κ g`. -/
lemma sum_jointOf_margCh (κ : α → B → ℝ) (g : B → B') (f : α × B' → ℝ) :
    ∑ z, jointOf P (margCh κ g) z * f z = ∑ z, jointOf P κ z * f (z.1, g z.2) := by
  rw [jointOf_margCh]
  exact sum_dist_mul _ _ f

/-- `I(X; g(Y))` for `margCh κ g`. -/
lemma mutualInfoOf_margCh (κ : α → B → ℝ) (g : B → B') :
    mutualInfoOf P (margCh κ g) = I[Prod.fst : fun z : α × B => g z.2 ; jointOf P κ] := by
  rw [mutualInfoOf, jointOf_margCh, ← mutualInfo_comp]
  rfl

end Marg

/-! ### The lower bounds on the rates -/

section Lower

variable {P : α → ℝ} {D₀ D₁ D₂ : ℝ} {R : ℝ × ℝ}

omit [Fintype β₁] [Fintype β₂] in
/-- **Lecture 14, page 14-7.** `R₁ + R₂ ≥ R(D₀)`, the rate–distortion function for `d₀`. -/
theorem infoRD_le_of_mem_mdRegion₀ [Finite β₁] [Finite β₂] (hP : IsPMF P)
    (h : R ∈ mdRegion P d₀ d₁ d₂ D₀ D₁ D₂) : infoRD P d₀ D₀ ≤ (R.1 + R.2) * log 2 := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  obtain ⟨κ, hκ, a0, -, -, -, -, a3⟩ := mdRegion_subset_mdOuter hP h
  have hg : IsChannel (margCh κ fun b : β₀ × β₁ × β₂ => b.1) := margCh_isChannel hκ _
  have hμ := jointOf_isPMF hP hκ
  refine (infoRD_le hP hg (D := D₀) ?_).trans ?_
  · rw [expDistortion_eq_sum_jointOf, sum_jointOf_margCh]
    exact a0
  · rw [mutualInfoOf_margCh]
    exact (mutualInfo_comp_le hμ Prod.fst Prod.snd (fun b : β₀ × β₁ × β₂ => b.1)).trans a3

omit [Fintype β₀] [Fintype β₂] in
/-- **Lecture 14, page 14-6.** `R₁ ≥ R(D₁)`. -/
theorem infoRD_le_of_mem_mdRegion₁ [Finite β₀] [Finite β₂] (hP : IsPMF P)
    (h : R ∈ mdRegion P d₀ d₁ d₂ D₀ D₁ D₂) : infoRD P d₁ D₁ ≤ R.1 * log 2 := by
  have := Fintype.ofFinite β₀
  have := Fintype.ofFinite β₂
  obtain ⟨κ, hκ, -, a0, -, a3, -, -⟩ := mdRegion_subset_mdOuter hP h
  have hg : IsChannel (margCh κ fun b : β₀ × β₁ × β₂ => b.2.1) := margCh_isChannel hκ _
  refine (infoRD_le hP hg (D := D₁) ?_).trans ?_
  · rw [expDistortion_eq_sum_jointOf, sum_jointOf_margCh]
    exact a0
  · rw [mutualInfoOf_margCh]
    exact a3

omit [Fintype β₀] [Fintype β₁] in
/-- **Lecture 14, page 14-6.** `R₂ ≥ R(D₂)`. -/
theorem infoRD_le_of_mem_mdRegion₂ [Finite β₀] [Finite β₁] (hP : IsPMF P)
    (h : R ∈ mdRegion P d₀ d₁ d₂ D₀ D₁ D₂) : infoRD P d₂ D₂ ≤ R.2 * log 2 := by
  have := Fintype.ofFinite β₀
  have := Fintype.ofFinite β₁
  obtain ⟨κ, hκ, -, -, a0, -, a3, -⟩ := mdRegion_subset_mdOuter hP h
  have hg : IsChannel (margCh κ fun b : β₀ × β₁ × β₂ => b.2.2) := margCh_isChannel hκ _
  refine (infoRD_le hP hg (D := D₂) ?_).trans ?_
  · rw [expDistortion_eq_sum_jointOf, sum_jointOf_margCh]
    exact a0
  · rw [mutualInfoOf_margCh]
    exact a3

end Lower

/-! ### Successive refinement -/

section Refinement

variable {P : α → ℝ}

/-- **Lecture 14 of [elgamal2010], page 14-22.** The successive refinement region `R(D₀, D₁)`: the
multiple description region without decoder 2. -/
def srRegion (P : α → ℝ) (d₀ : α → β₀ → ℝ) (d₁ : α → β₁ → ℝ) (D₀ D₁ : ℝ) : Set (ℝ × ℝ) :=
  mdRegion P d₀ d₁ (fun _ (_ : Unit) => (0 : ℝ)) D₀ D₁ 0

/-- **Theorem 3 of Lecture 14 of [elgamal2010], page 14-23: successive refinement.** The region
`R(D₀, D₁)` is the set of the rate pairs with `R₁ ≥ I(X; X̂₁)`, `R₁ + R₂ ≥ I(X; X̂₀, X̂₁)` and
`R₂ ≥ 0`, for some `p(x̂₀, x̂₁|x)` with `E dⱼ(X, X̂ⱼ) ≤ Dⱼ`. -/
theorem mem_srRegion_iff (hP : IsPMF P) (hd₀ : ∀ a b, 0 ≤ d₀ a b) (hd₁ : ∀ a b, 0 ≤ d₁ a b)
    {D₀ D₁ R₁ R₂ : ℝ} :
    (R₁, R₂) ∈ srRegion P d₀ d₁ D₀ D₁ ↔ 0 ≤ R₂ ∧ ∃ κ : α → β₀ × β₁ → ℝ, IsChannel κ ∧
      ∑ z, jointOf P κ z * d₀ z.1 z.2.1 ≤ D₀ ∧ ∑ z, jointOf P κ z * d₁ z.1 z.2.2 ≤ D₁ ∧
      I[Prod.fst : fun z : α × β₀ × β₁ => z.2.2 ; jointOf P κ] ≤ R₁ * log 2 ∧
      I[Prod.fst : Prod.snd ; jointOf P κ] ≤ (R₁ + R₂) * log 2 := by
  have hl := log_pos one_lt_two
  constructor
  · intro h
    refine ⟨(mdRegion_nonneg h).2, ?_⟩
    obtain ⟨κ, hκ, a0, a1, -, a3, -, a5⟩ := mdRegion_subset_mdOuter hP h
    have hμ := jointOf_isPMF hP hκ
    set g : β₀ × β₁ × Unit → β₀ × β₁ := fun b => (b.1, b.2.1) with hg
    have hm : IsChannel (margCh κ g) := margCh_isChannel hκ g
    refine ⟨margCh κ g, hm, ?_, ?_, ?_, ?_⟩
    · rw [sum_jointOf_margCh]
      exact a0
    · rw [sum_jointOf_margCh]
      exact a1
    · rw [jointOf_margCh, ← mutualInfo_comp]
      exact a3
    · have := mutualInfoOf_margCh (P := P) κ g
      rw [mutualInfoOf] at this
      rw [this]
      exact (mutualInfo_comp_le hμ Prod.fst Prod.snd g).trans a5
  · rintro ⟨hR₂, κ, hκ, a0, a1, a3, a5⟩
    have hμ := jointOf_isPMF hP hκ
    have hX : dist (jointOf P κ) Prod.fst = P := dist_jointOf_fst hκ
    have h := mem_mdRegion_of_le (X := Prod.fst) (Y₀ := fun z : α × β₀ × β₁ => z.2.1)
      (Y₁ := fun z : α × β₀ × β₁ => z.2.2) (Y₂ := fun _ => ()) (d₀ := d₀) (d₁ := d₁)
      (d₂ := fun _ (_ : Unit) => (0 : ℝ)) hμ hd₀ hd₁ (fun _ _ => le_rfl) (R₁ := R₁) (R₂ := R₂)
      (D₀ := D₀) (D₁ := D₁) (D₂ := 0) a3
      (by
        rw [mutualInfo_const_right' hμ]
        positivity)
      (by
        rw [mutualInfo_const_right' hμ, add_zero]
        refine le_trans (le_of_eq ?_) a5
        refine mutualInfo_congr_right hμ _ (fun b : β₀ × β₁ => (b.1, b.2, ())) ?_ fun _ => rfl
        rintro ⟨a, b⟩ ⟨a', b'⟩ h
        simpa using h)
      (by
        refine le_trans (le_of_eq ?_) a0
        exact sum_congr rfl fun _ _ => rfl)
      (by
        refine le_trans (le_of_eq ?_) a1
        exact sum_congr rfl fun _ _ => rfl)
      (by simp)
    rwa [hX] at h

/-- **Special case 2 of Lecture 14, page 14-5: a single description with two reproductions.** The
slice `R₂ = 0` of the region: `R₁ ≥ I(X; X̂₀, X̂₁)` for some `p(x̂₀, x̂₁|x)` with
`E dⱼ(X, X̂ⱼ) ≤ Dⱼ`. -/
theorem mem_srRegion_zero_iff (hP : IsPMF P) (hd₀ : ∀ a b, 0 ≤ d₀ a b) (hd₁ : ∀ a b, 0 ≤ d₁ a b)
    {D₀ D₁ R₁ : ℝ} :
    (R₁, (0 : ℝ)) ∈ srRegion P d₀ d₁ D₀ D₁ ↔ ∃ κ : α → β₀ × β₁ → ℝ, IsChannel κ ∧
      ∑ z, jointOf P κ z * d₀ z.1 z.2.1 ≤ D₀ ∧ ∑ z, jointOf P κ z * d₁ z.1 z.2.2 ≤ D₁ ∧
      I[Prod.fst : Prod.snd ; jointOf P κ] ≤ R₁ * log 2 := by
  rw [mem_srRegion_iff hP hd₀ hd₁]
  constructor
  · rintro ⟨-, κ, hκ, a0, a1, -, a5⟩
    rw [add_zero] at a5
    exact ⟨κ, hκ, a0, a1, a5⟩
  · rintro ⟨κ, hκ, a0, a1, a5⟩
    have hμ := jointOf_isPMF hP hκ
    refine ⟨le_rfl, κ, hκ, a0, a1, ?_, by rwa [add_zero]⟩
    exact (mutualInfo_comp_le hμ Prod.fst Prod.snd (fun b : β₀ × β₁ => b.2)).trans a5

/-- **Lecture 14 of [elgamal2010], page 14-24.** A source is successively refinable for the
  distortion
measure `d` if, for all `D₀ ≤ D₁`, the rate pair `(R(D₁), R(D₀) - R(D₁))`, in bits, has the
  distortion
pair `(D₀, D₁)`. -/
def IsSuccessivelyRefinable (P : α → ℝ) (d : α → β₀ → ℝ) : Prop :=
  ∀ D₀ D₁, minDistortion P d ≤ D₀ → D₀ ≤ D₁ →
    (infoRD P d D₁ / log 2, (infoRD P d D₀ - infoRD P d D₁) / log 2) ∈ srRegion P d d D₀ D₁

/-- A channel with a Markov chain `X → X̂₀ → X̂₁` from random variables on a finite probability
space. -/
theorem exists_markov_channel_of_rv [Nonempty β₀] {Ω' : Type*} [Fintype Ω'] {ν : Ω' → ℝ}
    (hν : IsPMF ν) {A : Ω' → α} {B₀ B₁ : Ω' → β₀} (hA : dist ν A = P)
    (hM : I[A : B₁ | B₀ ; ν] = 0) :
    ∃ κ : α → β₀ × β₀ → ℝ, IsChannel κ ∧
      MarkovChain (jointOf P κ) Prod.fst (fun z => z.2.1) (fun z => z.2.2) ∧
      (∀ d : α → β₀ → ℝ, ∑ z, jointOf P κ z * d z.1 z.2.1 = ∑ ω, ν ω * d (A ω) (B₀ ω)) ∧
      (∀ d : α → β₀ → ℝ, ∑ z, jointOf P κ z * d z.1 z.2.2 = ∑ ω, ν ω * d (A ω) (B₁ ω)) ∧
      I[Prod.fst : fun z : α × β₀ × β₀ => z.2.1 ; jointOf P κ] = I[A : B₀ ; ν] ∧
      I[Prod.fst : fun z : α × β₀ × β₀ => z.2.2 ; jointOf P κ] = I[A : B₁ ; ν] := by
  set W : Ω' → α × β₀ × β₀ := fun ω => (A ω, B₀ ω, B₁ ω) with hW
  have hr : IsPMF (dist ν W) := hν.dist W
  obtain ⟨κ, hκ, hker⟩ := exists_kernel hr
  have hfst : dist (dist ν W) Prod.fst = P := by
    rw [← dist_comp_eq]
    exact hA
  have hL : jointOf P κ = dist ν W := by
    funext ⟨a, b⟩
    rw [hker a b, hfst]
    rfl
  have hμ : IsPMF (jointOf P κ) := by
    rw [hL]
    exact hr
  refine ⟨κ, hκ, ?_, fun d => ?_, fun d => ?_, ?_, ?_⟩
  · refine (markovChain_iff_condIndep hμ _ _ _).2 ((condMutualInfo_eq_zero_iff hμ _ _ _).1 ?_)
    rw [hL, ← condMutualInfo_comp hν W]
    exact hM
  · rw [hL]
    exact sum_dist_mul ν W fun z => d z.1 z.2.1
  · rw [hL]
    exact sum_dist_mul ν W fun z => d z.1 z.2.2
  · rw [hL, ← mutualInfo_comp W]
    rfl
  · rw [hL, ← mutualInfo_comp W]
    rfl

/-- **Proposition 1 of Lecture 14 of [elgamal2010], page 14-26.** A source is successively refinable
if and only if, for all `D₀ ≤ D₁`, there is a `p(x̂₀, x̂₁|x)` with `X → X̂₀ → X̂₁`,
  `E d(X, X̂ⱼ) ≤ Dⱼ`,
`I(X; X̂₀) = R(D₀)` and `I(X; X̂₁) = R(D₁)`. -/
theorem isSuccessivelyRefinable_iff [Nonempty β₀] (hP : IsPMF P) (hd : ∀ a b, 0 ≤ d₀ a b) :
    IsSuccessivelyRefinable P d₀ ↔ ∀ D₀ D₁, minDistortion P d₀ ≤ D₀ → D₀ ≤ D₁ →
      ∃ κ : α → β₀ × β₀ → ℝ, IsChannel κ ∧
        MarkovChain (jointOf P κ) Prod.fst (fun z => z.2.1) (fun z => z.2.2) ∧
        ∑ z, jointOf P κ z * d₀ z.1 z.2.1 ≤ D₀ ∧ ∑ z, jointOf P κ z * d₀ z.1 z.2.2 ≤ D₁ ∧
        I[Prod.fst : fun z : α × β₀ × β₀ => z.2.1 ; jointOf P κ] = infoRD P d₀ D₀ ∧
        I[Prod.fst : fun z : α × β₀ × β₀ => z.2.2 ; jointOf P κ] = infoRD P d₀ D₁ := by
  have hl := log_pos one_lt_two
  have hswap : ∀ κ : α → β₀ × β₀ → ℝ, IsChannel κ →
      I[Prod.fst : Prod.snd ; jointOf P κ] =
        I[Prod.fst : pair (fun z : α × β₀ × β₀ => z.2.2) (fun z => z.2.1) ; jointOf P κ] := fun κ hκ
          =>
    mutualInfo_congr_right (jointOf_isPMF hP hκ) _ Prod.swap Prod.swap_injective fun _ => rfl
  have hlow₀ : ∀ {D : ℝ} {κ : α → β₀ × β₀ → ℝ}, IsChannel κ →
      ∑ z, jointOf P κ z * d₀ z.1 z.2.1 ≤ D → infoRD P d₀ D ≤
        I[Prod.fst : fun z : α × β₀ × β₀ => z.2.1 ; jointOf P κ] := fun {D κ} hκ hc => by
    have hg : IsChannel (margCh κ fun b : β₀ × β₀ => b.1) := margCh_isChannel hκ _
    refine (infoRD_le hP hg (D := D) ?_).trans (le_of_eq (mutualInfoOf_margCh κ _))
    rw [expDistortion_eq_sum_jointOf, sum_jointOf_margCh]
    exact hc
  have hlow₁ : ∀ {D : ℝ} {κ : α → β₀ × β₀ → ℝ}, IsChannel κ →
      ∑ z, jointOf P κ z * d₀ z.1 z.2.2 ≤ D → infoRD P d₀ D ≤
        I[Prod.fst : fun z : α × β₀ × β₀ => z.2.2 ; jointOf P κ] := fun {D κ} hκ hc => by
    have hg : IsChannel (margCh κ fun b : β₀ × β₀ => b.2) := margCh_isChannel hκ _
    refine (infoRD_le hP hg (D := D) ?_).trans (le_of_eq (mutualInfoOf_margCh κ _))
    rw [expDistortion_eq_sum_jointOf, sum_jointOf_margCh]
    exact hc
  constructor
  · intro h D₀ D₁ hD₀ hD
    obtain ⟨-, κ, hκ, a0, a1, a3, a5⟩ := (mem_srRegion_iff hP hd hd).1 (h D₀ D₁ hD₀ hD)
    have hμ := jointOf_isPMF hP hκ
    rw [div_mul_cancel₀ _ hl.ne'] at a3
    have e : (infoRD P d₀ D₁ / log 2 + (infoRD P d₀ D₀ - infoRD P d₀ D₁) / log 2) * log 2 =
        infoRD P d₀ D₀ := by
      field_simp
      ring
    rw [e, hswap κ hκ, chain_rule_mutualInfo₂ hμ] at a5
    have hz := condMutualInfo_nonneg hμ (Prod.fst : α × β₀ × β₀ → α)
      (fun z : α × β₀ × β₀ => z.2.2) (fun z => z.2.1)
    have l0 := hlow₀ hκ a0
    have l1 := hlow₁ hκ a1
    have hzero : I[Prod.fst : fun z : α × β₀ × β₀ => z.2.2 | fun z => z.2.1 ; jointOf P κ] = 0 := by
      linarith
    refine ⟨κ, hκ, ?_, a0, a1, by linarith, by linarith⟩
    exact (markovChain_iff_condIndep hμ _ _ _).2 ((condMutualInfo_eq_zero_iff hμ _ _ _).1 hzero)
  · intro h D₀ D₁ hD₀ hD
    obtain ⟨κ, hκ, hM, a0, a1, e0, e1⟩ := h D₀ D₁ hD₀ hD
    have hμ := jointOf_isPMF hP hκ
    refine (mem_srRegion_iff hP hd hd).2 ⟨?_, κ, hκ, a0, a1, ?_, ?_⟩
    · exact div_nonneg (sub_nonneg.2 (infoRD_antitoneOn hP hD₀ (hD₀.trans hD) hD)) hl.le
    · rw [div_mul_cancel₀ _ hl.ne']
      exact e1.le
    · have e : (infoRD P d₀ D₁ / log 2 + (infoRD P d₀ D₀ - infoRD P d₀ D₁) / log 2) * log 2 =
          infoRD P d₀ D₀ := by
        field_simp
        ring
      have hzero := (condMutualInfo_eq_zero_iff hμ _ _ _).2
        ((markovChain_iff_condIndep hμ _ _ _).1 hM)
      rw [e, hswap κ hκ, chain_rule_mutualInfo₂ hμ, hzero, add_zero]
      exact e0.le

end Refinement

/-! ### Special cases 1 and 3 -/

section Cases

variable {P : α → ℝ}

/-- **Special case 3 of Lecture 14, page 14-5: combined description only.** The region for
`D₁ = D₂ = ∞` is the set of the rate pairs with `R₁ + R₂ ≥ R(D₀)`. -/
theorem mem_mdRegion_combined_only_iff [Nonempty β₀] (hP : IsPMF P) (hd₀ : ∀ a b, 0 ≤ d₀ a b)
    {D₀ R₁ R₂ : ℝ} (hD₀ : minDistortion P d₀ ≤ D₀) :
    (R₁, R₂) ∈ mdRegion P d₀ (fun _ (_ : Unit) => (0 : ℝ)) (fun _ (_ : Unit) => (0 : ℝ)) D₀ 0 0 ↔
      0 ≤ R₁ ∧ 0 ≤ R₂ ∧ infoRD P d₀ D₀ ≤ (R₁ + R₂) * log 2 := by
  constructor
  · intro h
    exact ⟨(mdRegion_nonneg h).1, (mdRegion_nonneg h).2, infoRD_le_of_mem_mdRegion₀ hP h⟩
  · rintro ⟨hR₁, hR₂, hR⟩
    obtain ⟨κ, hκ, hc, he⟩ := exists_infoRD_eq hP hD₀
    have hμ := jointOf_isPMF hP hκ
    have hX : dist (jointOf P κ) Prod.fst = P := dist_jointOf_fst hκ
    have hl := log_pos one_lt_two
    have h := mem_mdRegion_of_le (X := Prod.fst) (Y₀ := Prod.snd) (Y₁ := fun _ => ())
      (Y₂ := fun _ => ()) (d₀ := d₀) (d₁ := fun _ (_ : Unit) => (0 : ℝ))
      (d₂ := fun _ (_ : Unit) => (0 : ℝ)) hμ hd₀ (fun _ _ => le_rfl) (fun _ _ => le_rfl)
      (R₁ := R₁) (R₂ := R₂) (D₀ := D₀) (D₁ := 0) (D₂ := 0)
      (by
        rw [mutualInfo_const_right' hμ]
        positivity)
      (by
        rw [mutualInfo_const_right' hμ]
        positivity)
      (by
        rw [mutualInfo_const_right' hμ, add_zero]
        refine le_trans (le_of_eq ?_) (he.le.trans hR)
        exact mutualInfo_congr_right hμ _ (fun b : β₀ => (b, (), ()))
          (fun a b h => (Prod.mk.inj h).1) fun _ => rfl)
      (by
        rw [expDistortion_eq_sum_jointOf] at hc
        exact hc)
      (by simp) (by simp)
    rwa [hX] at h

/-- `I(X; Y₁, Y₂) + I(Y₁; Y₂) = I(X; Y₁) + I(X; Y₂) + I(Y₁; Y₂|X)`. -/
lemma mutualInfo_pair_add_eq (hμ : IsPMF μ) :
    I[X : pair Y₁ Y₂ ; μ] + I[Y₁ : Y₂ ; μ] =
      I[X : Y₁ ; μ] + I[X : Y₂ ; μ] + I[Y₁ : Y₂ | X ; μ] := by
  have e1 := chain_rule_mutualInfo₂ hμ X Y₁ Y₂
  have e2 : I[X : Y₁ | Y₂ ; μ] = I[Y₁ : X | Y₂ ; μ] := condMutualInfo_comm hμ _ _ _
  have e3 := chain_rule_mutualInfo₂ hμ Y₁ X Y₂
  have e4 := chain_rule_mutualInfo₂ hμ Y₁ Y₂ X
  have e5 : I[Y₁ : pair Y₂ X ; μ] = I[Y₁ : pair X Y₂ ; μ] :=
    mutualInfo_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have e6 : I[Y₁ : X ; μ] = I[X : Y₁ ; μ] := mutualInfo_comm hμ _ _
  linarith

/-- **Special case 1 of Lecture 14, page 14-4: no combined description.** The region for `D₀ = ∞`
is the set of the rate pairs with `R₁ ≥ I(X; X̂₁)` and `R₂ ≥ I(X; X̂₂)`, for some
  `p(x̂₁|x) p(x̂₂|x)`
with `E dⱼ(X, X̂ⱼ) ≤ Dⱼ`. -/
theorem mem_mdRegion_no_combined_iff (hP : IsPMF P) (hd₁ : ∀ a b, 0 ≤ d₁ a b)
    (hd₂ : ∀ a b, 0 ≤ d₂ a b) {D₁ D₂ R₁ R₂ : ℝ} :
    (R₁, R₂) ∈ mdRegion P (fun _ (_ : Unit) => (0 : ℝ)) d₁ d₂ 0 D₁ D₂ ↔
      ∃ (κ₁ : α → β₁ → ℝ) (κ₂ : α → β₂ → ℝ), IsChannel κ₁ ∧ IsChannel κ₂ ∧
        expDistortion P κ₁ d₁ ≤ D₁ ∧ expDistortion P κ₂ d₂ ≤ D₂ ∧
        mutualInfoOf P κ₁ ≤ R₁ * log 2 ∧ mutualInfoOf P κ₂ ≤ R₂ * log 2 := by
  constructor
  · intro h
    obtain ⟨κ, hκ, -, a1, a2, a3, a4, -⟩ := mdRegion_subset_mdOuter hP h
    refine ⟨margCh κ fun b => b.2.1, margCh κ fun b => b.2.2, margCh_isChannel hκ _,
      margCh_isChannel hκ _, ?_, ?_, ?_, ?_⟩
    · rw [expDistortion_eq_sum_jointOf, sum_jointOf_margCh]
      exact a1
    · rw [expDistortion_eq_sum_jointOf, sum_jointOf_margCh]
      exact a2
    · rw [mutualInfoOf_margCh]
      exact a3
    · rw [mutualInfoOf_margCh]
      exact a4
  · rintro ⟨κ₁, κ₂, h₁, h₂, c₁, c₂, a₁, a₂⟩
    classical
    set κ : α → β₁ × β₂ → ℝ := fun a b => κ₁ a b.1 * κ₂ a b.2 with hκd
    have hκ : IsChannel κ := fun a => ⟨fun b => mul_nonneg ((h₁ a).nonneg _) ((h₂ a).nonneg _), by
      simp only [hκd, Fintype.sum_prod_type, ← mul_sum, (h₂ a).sum_eq_one, mul_one,
        (h₁ a).sum_eq_one]⟩
    have hμ := jointOf_isPMF hP hκ
    have hX : dist (jointOf P κ) Prod.fst = P := dist_jointOf_fst hκ
    -- The marginal channels.
    have hm₁ : margCh κ (fun b : β₁ × β₂ => b.1) = κ₁ := by
      funext a b₁
      simp only [margCh, dist, hκd, Fintype.sum_prod_type]
      rw [sum_eq_single b₁]
      · simp only [ite_true]
        rw [← mul_sum, (h₂ a).sum_eq_one, mul_one]
      · intro b _ hb
        simp [hb]
      · simp
    have hm₂ : margCh κ (fun b : β₁ × β₂ => b.2) = κ₂ := by
      funext a b₂
      simp only [margCh, dist, hκd, Fintype.sum_prod_type_right]
      rw [sum_eq_single b₂]
      · simp only [ite_true]
        rw [← sum_mul, (h₁ a).sum_eq_one, one_mul]
      · intro b _ hb
        simp [hb]
      · simp
    have eI₁ : I[Prod.fst : fun z : α × β₁ × β₂ => z.2.1 ; jointOf P κ] = mutualInfoOf P κ₁ := by
      rw [← hm₁, mutualInfoOf_margCh]
    have eI₂ : I[Prod.fst : fun z : α × β₁ × β₂ => z.2.2 ; jointOf P κ] = mutualInfoOf P κ₂ := by
      rw [← hm₂, mutualInfoOf_margCh]
    -- The conditional independence.
    have hci : I[(fun z : α × β₁ × β₂ => z.2.1) : (fun z => z.2.2) | Prod.fst ; jointOf P κ] = 0 :=
      by
      rw [condMutualInfo_comm hμ, condMutualInfo]
      have hA : IsPMF (dist (jointOf P κ) (fun z : α × β₁ × β₂ => (z.2.1, z.1))) := hμ.dist _
      have hch := condEntropy_eq_comp_of_channel hμ (fun z : α × β₁ × β₂ => (z.2.1, z.1))
        (fun z => z.2.2) (fun v => v.2) h₂ (by
          funext ⟨⟨b₁, a⟩, b₂⟩
          have e1 : dist (jointOf P κ) (pair (fun z : α × β₁ × β₂ => (z.2.1, z.1)) fun z => z.2.2)
              ((b₁, a), b₂) = P a * (κ₁ a b₁ * κ₂ a b₂) := by
            have hinj : Function.Injective (fun z : α × β₁ × β₂ => ((z.2.1, z.1), z.2.2)) := by
              rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
              simp only [Prod.mk.injEq] at h ⊢
              tauto
            have := dist_comp_of_injective (jointOf P κ) id hinj (a, b₁, b₂)
            rw [dist_id] at this
            exact this
          have e2 : dist (jointOf P κ) (fun z : α × β₁ × β₂ => (z.2.1, z.1)) (b₁, a) =
              P a * κ₁ a b₁ := by
            have h3 : jointOf P κ₁ = dist (jointOf P κ) (fun z : α × β₁ × β₂ => (z.1, z.2.1)) := by
              rw [← hm₁, jointOf_margCh]
            have h4 : dist (jointOf P κ) (fun z : α × β₁ × β₂ => (z.2.1, z.1)) =
                dist (jointOf P κ₁) Prod.swap := by
              rw [h3, ← dist_comp_eq]
              rfl
            rw [h4]
            have := dist_comp_of_injective (jointOf P κ₁) id Prod.swap_injective (a, b₁)
            rw [dist_id] at this
            exact this
          simp only [jointOf]
          rw [e1, e2]
          ring)
      have e3 : H[(fun z : α × β₁ × β₂ => z.2.2) | pair (fun z => z.2.1) Prod.fst ; jointOf P κ] =
          H[(fun z : α × β₁ × β₂ => z.2.2) | (fun v : β₁ × α => v.2) ∘
            (fun z : α × β₁ × β₂ => (z.2.1, z.1)) ; jointOf P κ] := hch
      rw [e3]
      exact sub_self _
    have hl := log_pos one_lt_two
    have hsum := mutualInfo_pair_add_eq (X := (Prod.fst : α × β₁ × β₂ → α))
      (Y₁ := fun z : α × β₁ × β₂ => z.2.1) (Y₂ := fun z => z.2.2) hμ
    rw [hci, add_zero, eI₁, eI₂] at hsum
    have h := mem_mdRegion_of_le (X := Prod.fst) (Y₀ := fun _ => ())
      (Y₁ := fun z : α × β₁ × β₂ => z.2.1) (Y₂ := fun z => z.2.2)
      (d₀ := fun _ (_ : Unit) => (0 : ℝ)) (d₁ := d₁) (d₂ := d₂) hμ (fun _ _ => le_rfl) hd₁ hd₂
      (R₁ := R₁) (R₂ := R₂) (D₀ := 0) (D₁ := D₁) (D₂ := D₂)
      (by rwa [eI₁]) (by rwa [eI₂])
      (by
        have e : I[Prod.fst : pair (fun _ : α × β₁ × β₂ => ()) (pair (fun z => z.2.1)
            (fun z => z.2.2)) ; jointOf P κ] =
            I[Prod.fst : pair (fun z : α × β₁ × β₂ => z.2.1) (fun z => z.2.2) ; jointOf P κ] :=
          mutualInfo_congr_right hμ _ (fun b : β₁ × β₂ => ((), b))
            (fun a b h => (Prod.mk.inj h).2) fun _ => rfl
        rw [e, hsum, add_mul]
        exact add_le_add a₁ a₂)
      (by simp)
      (by
        have hm := sum_jointOf_margCh (P := P) κ (fun b : β₁ × β₂ => b.1) fun z => d₁ z.1 z.2
        rw [hm₁] at hm
        rw [expDistortion_eq_sum_jointOf, hm] at c₁
        exact c₁)
      (by
        have hm := sum_jointOf_margCh (P := P) κ (fun b : β₁ × β₂ => b.2) fun z => d₂ z.1 z.2
        rw [hm₂] at hm
        rw [expDistortion_eq_sum_jointOf, hm] at c₂
        exact c₂)
    rwa [hX] at h

end Cases

/-! ### The alternative form of the Zhang–Berger inner bound -/

section Auxiliary

variable {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]

omit [Fintype α] [Fintype υ] in
/-- Processing `Y` given `Z` cannot increase the conditional information:
`I(X; g(Z, Y) | Z) ≤ I(X; Y | Z)`. -/
lemma condMutualInfo_comp_cond_le {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]
    {ξ : Type*} [Fintype ξ] (hμ : IsPMF μ) (A : Ω → ξ) (B : Ω → σ) (Z : Ω → τ) (g : τ → σ → ρ) :
    I[A : (fun ω => g (Z ω) (B ω)) | Z ; μ] ≤ I[A : B | Z ; μ] := by
  have h := condEntropy_le_condEntropy_comp hμ A (pair B Z) (fun p : σ × τ => (g p.2 p.1, p.2))
  rw [condMutualInfo, condMutualInfo]
  have e : H[A | (fun p : σ × τ => (g p.2 p.1, p.2)) ∘ pair B Z ; μ] =
      H[A | pair (fun ω => g (Z ω) (B ω)) Z ; μ] := rfl
  rw [e] at h
  linarith

omit [Fintype β₀] [Fintype β₁] [Fintype β₂] in
/-- **Lecture 14, pages 14-30 and 14-31: the alternative form of the Zhang–Berger inner bound.** A
rate pair is achievable if `R₁ > I(X; U₀, U₁)`, `R₂ > I(X; U₀, U₂)`,
`R₁ + R₂ > I(X; U₁, U₂|U₀) + 2 I(U₀; X) + I(U₁; U₂|U₀)` and
`E d₀(X, x̂₀(U₀, U₁, U₂)) ≤ D₀`, `E d₁(X, x̂₁(U₀, U₁)) ≤ D₁`, `E d₂(X, x̂₂(U₀, U₂)) ≤ D₂`. This is
  the
inclusion of the alternative region in the inner bound of Theorem 4. -/
theorem isAchievableMD_of_auxiliary [Finite β₀] [Finite β₁] [Finite β₂] (hμ : IsPMF μ) (hd₀ : ∀ a b,
  0 ≤ d₀ a b)
    (hd₁ : ∀ a b, 0 ≤ d₁ a b) (hd₂ : ∀ a b, 0 ≤ d₂ a b) {U₀ : Ω → υ} {U₁ : Ω → κ₁} {U₂ : Ω → κ₂}
    (f₀ : υ → κ₁ × κ₂ → β₀) (f₁ : υ → κ₁ → β₁) (f₂ : υ → κ₂ → β₂) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h₁ : I[X : pair U₀ U₁ ; μ] < R₁ * log 2) (h₂ : I[X : pair U₀ U₂ ; μ] < R₂ * log 2)
    (h₁₂ : I[X : pair U₁ U₂ | U₀ ; μ] + 2 * I[U₀ : X ; μ] + I[U₁ : U₂ | U₀ ; μ] <
      (R₁ + R₂) * log 2)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (f₀ (U₀ ω) (U₁ ω, U₂ ω)) ≤ D₀)
    (hc₁ : ∑ ω, μ ω * d₁ (X ω) (f₁ (U₀ ω) (U₁ ω)) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (f₂ (U₀ ω) (U₂ ω)) ≤ D₂) :
    IsAchievableMD (dist μ X) d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  have := Fintype.ofFinite β₀
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  refine isAchievableMD_zhangBerger (U := U₀) (Y₀ := fun ω => f₀ (U₀ ω) (U₁ ω, U₂ ω))
    (Y₁ := fun ω => f₁ (U₀ ω) (U₁ ω)) (Y₂ := fun ω => f₂ (U₀ ω) (U₂ ω)) hμ hd₀ hd₁ hd₂ ?_ ?_ ?_
    hc₀ hc₁ hc₂
  · refine lt_of_le_of_lt ?_ h₁
    exact mutualInfo_comp_le hμ X (pair U₀ U₁) (fun p : υ × κ₁ => (f₁ p.1 p.2, p.1))
  · refine lt_of_le_of_lt ?_ h₂
    exact mutualInfo_comp_le hμ X (pair U₀ U₂) (fun p : υ × κ₂ => (f₂ p.1 p.2, p.1))
  · have e₁ : I[X : pair (fun ω => f₀ (U₀ ω) (U₁ ω, U₂ ω)) (pair (fun ω => f₁ (U₀ ω) (U₁ ω))
        (fun ω => f₂ (U₀ ω) (U₂ ω))) | U₀ ; μ] ≤ I[X : pair U₁ U₂ | U₀ ; μ] :=
      condMutualInfo_comp_cond_le hμ X (pair U₁ U₂) U₀
        (fun u v => (f₀ u v, f₁ u v.1, f₂ u v.2))
    have e₂ : I[(fun ω => f₁ (U₀ ω) (U₁ ω)) : (fun ω => f₂ (U₀ ω) (U₂ ω)) | U₀ ; μ] ≤
        I[U₁ : U₂ | U₀ ; μ] := by
      have a₁ := condMutualInfo_comp_cond_le hμ (fun ω => f₁ (U₀ ω) (U₁ ω)) U₂ U₀ f₂
      have a₂ := condMutualInfo_comp_cond_le hμ U₂ U₁ U₀ f₁
      rw [condMutualInfo_comm hμ U₂] at a₂
      exact a₁.trans (a₂.trans (condMutualInfo_comm hμ U₂ U₁ U₀).le)
    linarith

end Auxiliary

end InfoTheory
