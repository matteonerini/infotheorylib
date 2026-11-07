/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Connected.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Supporting hyperplanes

Supporting hyperplanes of convex sets in a finite-dimensional real vector space, and two criteria
for the equality of two convex sets, which are Lemmas A.1 and A.2 of El Gamal and Kim.

A supporting hyperplane at a boundary point `x₀` of `S` is `{y | f y = f x₀}` for a nonzero linear
functional `f` with `f x ≤ f x₀` on `S`. We work with the functional, since it also records the side
of `S`.

## Main definitions

* `IsSupportingAt S f x₀`: the functional `f` supports `S` at the boundary point `x₀`.
* `HasUniqueSupport S x₀`: the functional is unique up to a positive factor.
* `HasUniqueSupportingHyperplane S x₀`: the hyperplane is unique as a set.

## Main statements

* `exists_isSupportingAt`: **the supporting hyperplane theorem**.
* `eq_sInter_halfSpaces`: a nonempty closed bounded convex set is the intersection of its supporting
  half spaces.
* `eq_of_forall_isSupportingAt`: **Lemma A.1** of El Gamal and Kim.
* `eq_of_hasUniqueSupport`: **Lemma A.2**, with supporting half spaces.
* `eq_of_hasUniqueSupportingHyperplane`: **Lemma A.2**, with hyperplanes, for a smaller set with
  nonempty interior.

## References

* [R. T. Rockafellar, *Convex Analysis*][rockafellar1970]
-/

@[expose] public section

open Set Topology Filter Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonzero functional `f` supports `S` at the boundary point `x₀`. -/
def IsSupportingAt (S : Set E) (f : StrongDual ℝ E) (x₀ : E) : Prop :=
  x₀ ∈ frontier S ∧ f ≠ 0 ∧ ∀ x ∈ S, f x ≤ f x₀

/-- The supporting functional at `x₀` is unique up to a positive factor. -/
def HasUniqueSupport (S : Set E) (x₀ : E) : Prop :=
  ∀ f g, IsSupportingAt S f x₀ → IsSupportingAt S g x₀ → ∃ c : ℝ, 0 < c ∧ g = c • f

/-- The supporting hyperplane at `x₀` is unique as a set. -/
def HasUniqueSupportingHyperplane (S : Set E) (x₀ : E) : Prop :=
  ∀ f g, IsSupportingAt S f x₀ → IsSupportingAt S g x₀ → {y | f y = f x₀} = {y | g y = g x₀}

/-- A nonzero functional takes a positive value. -/
lemma exists_pos_of_ne_zero {f : StrongDual ℝ E} (hf : f ≠ 0) : ∃ v, 0 < f v := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (ContinuousLinearMap.ext hcon)
  rcases lt_or_gt_of_ne hv with h | h
  · exact ⟨-v, by simpa using h⟩
  · exact ⟨v, h⟩

/-- A nonzero functional does not attain its maximum on `S` in the interior of `S`. -/
lemma lt_of_mem_interior {S : Set E} {f : StrongDual ℝ E} {M : ℝ} (hf : f ≠ 0)
    (hS : ∀ x ∈ S, f x ≤ M) {c : E} (hc : c ∈ interior S) : f c < M := by
  obtain ⟨v, hv⟩ := exists_pos_of_ne_zero hf
  have hcont : Tendsto (fun t : ℝ => c + t • v) (𝓝 0) (𝓝 c) := by
    have : Continuous fun t : ℝ => c + t • v := by fun_prop
    simpa using this.tendsto 0
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), c + t • v ∈ S :=
    (hcont.mono_left nhdsWithin_le_nhds).eventually (mem_interior_iff_mem_nhds.1 hc)
  obtain ⟨t, ht, ht0⟩ := (h1.and self_mem_nhdsWithin).exists
  have h2 := hS _ ht
  rw [map_add, map_smul, smul_eq_mul] at h2
  have h3 : 0 < t * f v := mul_pos ht0 hv
  linarith

/-- A bound on `S` extends to the closure of `S`. -/
lemma le_of_mem_closure {S : Set E} {f : StrongDual ℝ E} {M : ℝ} (hS : ∀ x ∈ S, f x ≤ M) {x : E}
    (hx : x ∈ closure S) : f x ≤ M := by
  have hc : IsClosed {y | f y ≤ M} := isClosed_le f.continuous continuous_const
  exact closure_minimal (fun y hy => hS y hy) hc hx

/-- A point of the closure at which a nonzero functional is maximal is a boundary point. -/
lemma isSupportingAt_of_max {S : Set E} {f : StrongDual ℝ E} {x₀ : E} (hf : f ≠ 0)
    (hx₀ : x₀ ∈ closure S) (h : ∀ x ∈ S, f x ≤ f x₀) : IsSupportingAt S f x₀ :=
  ⟨⟨hx₀, fun hi => lt_irrefl _ (lt_of_mem_interior hf h hi)⟩, hf, h⟩

omit [NormedSpace ℝ E] in
/-- A connected set from the interior of `S` to the outside of its closure meets the boundary. -/
lemma exists_mem_frontier_of_isPreconnected {T S : Set E} (hT : IsPreconnected T) {c y : E}
    (hc : c ∈ T) (hy : y ∈ T) (hci : c ∈ interior S) (hyc : y ∉ closure S) :
    ∃ b ∈ T, b ∈ frontier S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z, -, hz1, hz2⟩ := hT (interior S) (closure S)ᶜ isOpen_interior
    isClosed_closure.isOpen_compl
    (fun z hz => by
      by_cases h : z ∈ closure S
      · exact Or.inl (by_contra fun hi => hcon z hz ⟨h, hi⟩)
      · exact Or.inr h)
    ⟨c, hc, hci⟩ ⟨y, hy, hyc⟩
  exact hz2 (interior_subset_closure hz1)

variable [FiniteDimensional ℝ E]

/-- A convex set with empty interior lies in a hyperplane: a nonzero functional is constant on its
closure. -/
lemma exists_const_of_interior_eq_empty {S : Set E} (hS : Convex ℝ S) (hne : S.Nonempty)
    (hint : interior S = ∅) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ x ∈ closure S, ∀ y ∈ closure S, f x = f y := by
  set A := affineSpan ℝ S with hA
  have hAne : (A : Set E).Nonempty := (affineSpan_nonempty ℝ).2 hne
  have hAtop : A ≠ ⊤ := fun h => by
    have := hS.interior_nonempty_iff_affineSpan_eq_top.2 h
    rw [hint] at this
    exact Set.not_nonempty_empty this
  have hdir : A.direction < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hAtop ?_
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty hAne).1 h
  obtain ⟨φ, hφ, hle⟩ := A.direction.exists_le_ker_of_lt_top hdir
  have hcl : closure S ⊆ A :=
    closure_minimal (subset_affineSpan ℝ S) A.closed_of_finiteDimensional
  refine ⟨LinearMap.toContinuousLinearMap φ, fun h => hφ ?_, fun x hx y hy => ?_⟩
  · ext v
    have := congrArg (fun F : StrongDual ℝ E => F v) h
    simpa using this
  · have h1 : x -ᵥ y ∈ A.direction := AffineSubspace.vsub_mem_direction (hcl hx) (hcl hy)
    have h2 : φ (x - y) = 0 := hle h1
    rw [map_sub, sub_eq_zero] at h2
    simpa using h2

/-- **The supporting hyperplane theorem.** A convex set has a supporting hyperplane at each of its
boundary points. -/
theorem exists_isSupportingAt {S : Set E} (hS : Convex ℝ S) {x₀ : E} (hx₀ : x₀ ∈ frontier S) :
    ∃ f, IsSupportingAt S f x₀ := by
  rcases (interior S).eq_empty_or_nonempty with hint | hint
  · have hne : S.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp [h] at hx₀
    obtain ⟨f, hf, hc⟩ := exists_const_of_interior_eq_empty hS hne hint
    exact ⟨f, hx₀, hf, fun x hx => (hc x (subset_closure hx) x₀ hx₀.1).le⟩
  · obtain ⟨f, hf, h⟩ := geometric_hahn_banach_of_nonempty_interior_point hS hx₀.2 hint
    exact ⟨f, hx₀, hf, h⟩

/-- **A nonempty closed bounded convex set is the intersection of its supporting half spaces.** -/
theorem eq_sInter_halfSpaces {S : Set E} (hS : Convex ℝ S) (hcl : IsClosed S)
    (hb : Bornology.IsBounded S) (hne : S.Nonempty) :
    S = ⋂₀ {H | ∃ f x₀, IsSupportingAt S f x₀ ∧ H = {y | f y ≤ f x₀}} := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have hK : IsCompact S := Metric.isCompact_of_isClosed_isBounded hcl hb
  refine Subset.antisymm (fun x hx H hH => ?_) fun y hy => ?_
  · obtain ⟨f, x₀, hf, rfl⟩ := hH
    exact hf.2.2 x hx
  · by_contra hyS
    obtain ⟨f, u, v, h1, huv, h2⟩ := geometric_hahn_banach_compact_closed hS hK
      (convex_singleton y) isClosed_singleton (disjoint_singleton_right.2 hyS)
    have hfy : v < f y := h2 y (mem_singleton y)
    obtain ⟨a, ha⟩ := hne
    have hf : f ≠ 0 := fun h0 => by
      have h3 := h1 a ha
      simp only [h0, zero_apply] at h3 hfy
      linarith
    obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn ⟨a, ha⟩ f.continuous.continuousOn
    have hsup := isSupportingAt_of_max hf (subset_closure hx₀) fun x hx => hmax hx
    have h3 : f y ≤ f x₀ := hy _ ⟨f, x₀, hsup, rfl⟩
    have h4 := h1 x₀ hx₀
    linarith

/-- **Lemma A.1 of El Gamal and Kim.** Let `R₁ ⊆ R₂` be bounded subsets of `R`, with `R₁` convex and
closed relative to `R`. If every supporting hyperplane of `R₂` meets `R₁`, then `R₁ = R₂`. The
convexity of `R` and `R₂` is not needed. -/
theorem eq_of_forall_isSupportingAt [Nontrivial E] {R R₁ R₂ : Set E} (hR₁ : Convex ℝ R₁)
    (hb₁ : Bornology.IsBounded R₁) (hb₂ : Bornology.IsBounded R₂) (hsub : R₁ ⊆ R₂) (hR₂ : R₂ ⊆ R)
    (hrel : closure R₁ ∩ R ⊆ R₁)
    (h : ∀ f x₀, IsSupportingAt R₂ f x₀ → ∃ y ∈ R₁, f y = f x₀) : R₁ = R₂ := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  refine Subset.antisymm hsub fun x hx => ?_
  by_contra hx₁
  have hxc : x ∉ closure R₁ := fun hc => hx₁ (hrel ⟨hc, hR₂ hx⟩)
  -- A functional separating `x` from `R₁`.
  obtain ⟨f, hf, hsep⟩ : ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ a ∈ R₁, f a < f x := by
    rcases R₁.eq_empty_or_nonempty with hemp | ⟨a₀, ha₀⟩
    · obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hv' : (‖v‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hv
      obtain ⟨f, -, hf⟩ := exists_dual_vector ℝ v hv'
      refine ⟨f, fun h0 => hv' ?_, fun a ha => ?_⟩
      · simpa [h0] using hf.symm
      rw [hemp] at ha
      exact absurd ha (Set.notMem_empty a)
    · obtain ⟨f, u, v, h1, huv, h2⟩ := geometric_hahn_banach_compact_closed hR₁.closure
        hb₁.isCompact_closure (convex_singleton x) isClosed_singleton
        (disjoint_singleton_right.2 hxc)
      have hfx : v < f x := h2 x (mem_singleton x)
      have hlt : ∀ a ∈ R₁, f a < f x := fun a ha => by
        have := h1 a (subset_closure ha)
        linarith
      refine ⟨f, fun h0 => ?_, hlt⟩
      have := hlt a₀ ha₀
      simp [h0] at this
  -- The supporting hyperplane of `R₂` in the direction `f`.
  obtain ⟨x₀, hx₀, hmax⟩ := hb₂.isCompact_closure.exists_isMaxOn
    ⟨x, subset_closure hx⟩ f.continuous.continuousOn
  have hsup := isSupportingAt_of_max hf hx₀ fun z hz => hmax (subset_closure hz)
  obtain ⟨y, hy, hyeq⟩ := h f x₀ hsup
  have h1 := hsep y hy
  have h2 : f x ≤ f x₀ := hmax (subset_closure hx)
  linarith

/-- **Lemma A.2 of El Gamal and Kim, with supporting half spaces.** Let `R₁ ⊆ R₂` be convex subsets
of `R`, with `R₁` nonempty and closed relative to `R`. Let `A` be a set of boundary points of `R₁`
whose convex hull contains the boundary of `R₁`. If each point of `A` has a unique supporting half
space of `R₁` and lies on the boundary of `R₂`, then `R₁ = R₂`. Boundedness is not needed. -/
theorem eq_of_hasUniqueSupport {R R₁ R₂ A : Set E} (hR₁ : Convex ℝ R₁)
    (hR₂c : Convex ℝ R₂) (hne : R₁.Nonempty) (hsub : R₁ ⊆ R₂) (hR₂ : R₂ ⊆ R)
    (hrel : closure R₁ ∩ R ⊆ R₁) (hA : A ⊆ frontier R₁) (hcov : frontier R₁ ⊆ convexHull ℝ A)
    (huniq : ∀ x₀ ∈ A, HasUniqueSupport R₁ x₀) (hbd : ∀ x₀ ∈ A, x₀ ∈ frontier R₂) : R₁ = R₂ := by
  -- The set `R₁` has interior points.
  have hint : (interior R₁).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    obtain ⟨r, hr⟩ := hne
    have hrf : r ∈ frontier R₁ := ⟨subset_closure hr, by simp [hemp]⟩
    obtain ⟨a, ha⟩ : A.Nonempty := convexHull_nonempty_iff.1 ⟨r, hcov hrf⟩
    obtain ⟨f, hf, hc⟩ := exists_const_of_interior_eq_empty hR₁ ⟨r, hr⟩ hemp
    have haf := hA ha
    have h1 : IsSupportingAt R₁ f a :=
      ⟨haf, hf, fun x hx => (hc x (subset_closure hx) a haf.1).le⟩
    have h2 : IsSupportingAt R₁ (-f) a := ⟨haf, neg_ne_zero.2 hf, fun x hx => by
      simpa using (hc x (subset_closure hx) a haf.1).ge⟩
    obtain ⟨c, hc0, hcf⟩ := huniq a ha f (-f) h1 h2
    apply hf
    have h3 : (1 + c) • f = 0 := by
      rw [add_smul, one_smul, ← hcf]
      simp
    exact (smul_eq_zero.1 h3).resolve_left (by positivity)
  obtain ⟨c, hc⟩ := hint
  refine Subset.antisymm hsub fun y hy => ?_
  by_contra hy₁
  have hyc : y ∉ closure R₁ := fun hc' => hy₁ (hrel ⟨hc', hR₂ hy⟩)
  -- The segment from `c` to `y` leaves `R₁` at a boundary point `b`.
  obtain ⟨b, hbs, hbf⟩ := exists_mem_frontier_of_isPreconnected (convex_segment c y).isPreconnected
    (left_mem_segment ℝ c y) (right_mem_segment ℝ c y) hc hyc
  obtain ⟨a₁, a₂, ha₁, ha₂, ha, rfl⟩ := hbs
  set b := a₁ • c + a₂ • y with hb
  obtain ⟨f, -, hf, hfle⟩ := exists_isSupportingAt hR₁ hbf
  have hfc : f c < f b := lt_of_mem_interior hf hfle hc
  -- A point of `A` on the same supporting hyperplane.
  obtain ⟨a, ha', hfa⟩ : ∃ a ∈ A, f a = f b := by
    by_contra hcon
    push Not at hcon
    have hlt : ∀ a ∈ A, f a < f b := fun a ha' =>
      lt_of_le_of_ne (le_of_mem_closure hfle (hA ha').1) (hcon a ha')
    have hhull : convexHull ℝ A ⊆ {x | f x < f b} :=
      convexHull_min (fun a ha' => hlt a ha') (convex_halfSpace_lt f.isLinear _)
    exact lt_irrefl (f b) (hhull (hcov hbf))
  have hfs : IsSupportingAt R₁ f a := ⟨hA ha', hf, fun x hx => by rw [hfa]; exact hfle x hx⟩
  obtain ⟨g, -, hg, hgle⟩ := exists_isSupportingAt hR₂c (hbd a ha')
  have hgs : IsSupportingAt R₁ g a := ⟨hA ha', hg, fun x hx => hgle x (hsub hx)⟩
  obtain ⟨t, ht, hfg⟩ := huniq a ha' g f hgs hfs
  -- So `f` supports `R₂` at `a`, while the segment shows that `f y > f b`.
  have hfy : f y ≤ f b := by
    rw [← hfa, hfg]
    simpa using mul_le_mul_of_nonneg_left (hgle y hy) ht.le
  have ha₁0 : 0 < a₁ := by
    refine lt_of_le_of_ne ha₁ fun h => hyc ?_
    have h2 : a₂ = 1 := by linarith
    have h3 : b = y := by simp [hb, ← h, h2]
    exact h3 ▸ hbf.1
  have hval : f b = a₁ * f c + a₂ * f y := by
    simp [hb, map_add, map_smul]
  have h4 : a₁ * f c < a₁ * f b := mul_lt_mul_of_pos_left hfc ha₁0
  have h5 : a₂ * f y ≤ a₂ * f b := mul_le_mul_of_nonneg_left hfy ha₂
  have h6 : a₁ * f b + a₂ * f b = f b := by rw [← add_mul, ha, one_mul]
  linarith

omit [FiniteDimensional ℝ E] in
/-- For a set with nonempty interior, a unique supporting hyperplane is a unique supporting half
space. -/
lemma HasUniqueSupportingHyperplane.hasUniqueSupport {S : Set E} {x₀ : E}
    (h : HasUniqueSupportingHyperplane S x₀) (hint : (interior S).Nonempty) :
    HasUniqueSupport S x₀ := by
  intro f g hf hg
  obtain ⟨v₀, hv₀⟩ := exists_pos_of_ne_zero hf.2.1
  set v := (f v₀)⁻¹ • v₀ with hv
  have hfv : f v = 1 := by
    rw [hv, map_smul, smul_eq_mul, inv_mul_cancel₀ hv₀.ne']
  have hset := h f g hf hg
  have hgw : ∀ w, g w = f w * g v := by
    intro w
    have h1 : x₀ + (w - f w • v) ∈ {y | f y = f x₀} := by
      simp [hfv]
    rw [hset] at h1
    have h2 : g (x₀ + (w - f w • v)) = g x₀ := h1
    simp only [map_add, map_sub, map_smul, smul_eq_mul] at h2
    linarith
  obtain ⟨e, he⟩ := hint
  have h1 := lt_of_mem_interior hf.2.1 hf.2.2 he
  have h2 := lt_of_mem_interior hg.2.1 hg.2.2 he
  have h3 : g e - g x₀ = (f e - f x₀) * g v := by
    rw [hgw e, hgw x₀]
    ring
  refine ⟨g v, ?_, ContinuousLinearMap.ext fun w => ?_⟩
  · by_contra hc
    push Not at hc
    nlinarith
  · simp [hgw w, mul_comm]

/-- **Lemma A.2 of El Gamal and Kim, with hyperplanes**, for a smaller set with nonempty interior.
The assumption on the interior cannot be dropped: see `printed_lemma_A_2_false`. -/
theorem eq_of_hasUniqueSupportingHyperplane {R R₁ R₂ A : Set E} (hR₁ : Convex ℝ R₁)
    (hR₂c : Convex ℝ R₂) (hint : (interior R₁).Nonempty) (hsub : R₁ ⊆ R₂) (hR₂ : R₂ ⊆ R)
    (hrel : closure R₁ ∩ R ⊆ R₁) (hA : A ⊆ frontier R₁) (hcov : frontier R₁ ⊆ convexHull ℝ A)
    (huniq : ∀ x₀ ∈ A, HasUniqueSupportingHyperplane R₁ x₀) (hbd : ∀ x₀ ∈ A, x₀ ∈ frontier R₂) :
    R₁ = R₂ :=
  eq_of_hasUniqueSupport hR₁ hR₂c (hint.mono interior_subset) hsub hR₂ hrel hA hcov
    (fun x₀ hx₀ => (huniq x₀ hx₀).hasUniqueSupport hint) hbd
