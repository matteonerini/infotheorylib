/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Sequences
public import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Alternating maximization

To maximize `f(u₁, u₂)` over `u₁ ∈ A₁` and `u₂ ∈ A₂`, alternately maximize over one variable with
the other fixed: `u₁⁽ᵏ⁾ = c₁(u₂⁽ᵏ⁻¹⁾)` and `u₂⁽ᵏ⁾ = c₂(u₁⁽ᵏ⁾)`, where `c₁(u₂)` maximizes
`f(·, u₂)` and `c₂(u₁)` maximizes `f(u₁, ·)`. The values `f(u⁽ᵏ⁾)` increase. If `f` is concave and
differentiable, a point that cannot be improved in either variable is a global maximum, so the
iteration only stops at the maximum; with compactness and continuity, `f(u⁽ᵏ⁾)` converges to the
maximum.

## Main definitions

* `altStep c₁ c₂ u`: one round `(c₁(u₂), c₂(c₁(u₂)))` of the iteration.
* `altSeq c₁ c₂ u₁`: the iteration started at `(u₁, c₂(u₁))`.

## Main statements

* `le_altSeq_succ`: the values increase, (9.10)–(9.13).
* `le_of_isMax_coordinatewise`: for a concave differentiable function, a coordinatewise maximum is
  a global maximum.
* `lt_altStep`: Lemma 9.4, the iteration is not trapped below the maximum.
* `tendsto_altSeq`: Theorem 9.5, for compact sets and continuous maximizers.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 9.1 and 9.3.1
-/

open Set Filter Topology

public section

namespace InfoTheory

variable {E₁ E₂ : Type*}

/-- One round of alternating maximization, (9.80): `(c₁(u₂), c₂(c₁(u₂)))`. -/
def altStep (c₁ : E₂ → E₁) (c₂ : E₁ → E₂) (u : E₁ × E₂) : E₁ × E₂ := (c₁ u.2, c₂ (c₁ u.2))

/-- **(9.7)–(9.8)** The alternating maximization sequence started at `(u₁, c₂(u₁))`. -/
def altSeq (c₁ : E₂ → E₁) (c₂ : E₁ → E₂) (u₁ : E₁) : ℕ → E₁ × E₂
  | 0 => (u₁, c₂ u₁)
  | k + 1 => altStep c₁ c₂ (altSeq c₁ c₂ u₁ k)

variable {f : E₁ × E₂ → ℝ} {A₁ : Set E₁} {A₂ : Set E₂} {c₁ : E₂ → E₁} {c₂ : E₁ → E₂}

/-- `c₁(u₂)` maximizes `f(·, u₂)` over `A₁`, (9.4). -/
def IsBestFst (f : E₁ × E₂ → ℝ) (A₁ : Set E₁) (A₂ : Set E₂) (c₁ : E₂ → E₁) : Prop :=
  ∀ u₂ ∈ A₂, c₁ u₂ ∈ A₁ ∧ ∀ u₁ ∈ A₁, f (u₁, u₂) ≤ f (c₁ u₂, u₂)

/-- `c₂(u₁)` maximizes `f(u₁, ·)` over `A₂`, (9.5). -/
def IsBestSnd (f : E₁ × E₂ → ℝ) (A₁ : Set E₁) (A₂ : Set E₂) (c₂ : E₁ → E₂) : Prop :=
  ∀ u₁ ∈ A₁, c₂ u₁ ∈ A₂ ∧ ∀ u₂ ∈ A₂, f (u₁, u₂) ≤ f (u₁, c₂ u₁)

lemma altStep_mem (h₁ : IsBestFst f A₁ A₂ c₁) (h₂ : IsBestSnd f A₁ A₂ c₂) {u : E₁ × E₂}
    (hu : u ∈ A₁ ×ˢ A₂) : altStep c₁ c₂ u ∈ A₁ ×ˢ A₂ :=
  ⟨(h₁ u.2 hu.2).1, (h₂ _ (h₁ u.2 hu.2).1).1⟩

lemma altSeq_mem (h₁ : IsBestFst f A₁ A₂ c₁) (h₂ : IsBestSnd f A₁ A₂ c₂) {u₁ : E₁}
    (hu₁ : u₁ ∈ A₁) (k : ℕ) : altSeq c₁ c₂ u₁ k ∈ A₁ ×ˢ A₂ := by
  induction k with
  | zero => exact ⟨hu₁, (h₂ u₁ hu₁).1⟩
  | succ k ih => exact altStep_mem h₁ h₂ ih

/-- **(9.10)–(9.13)** One round does not decrease `f`. -/
lemma le_altStep (h₁ : IsBestFst f A₁ A₂ c₁) (h₂ : IsBestSnd f A₁ A₂ c₂) {u : E₁ × E₂}
    (hu : u ∈ A₁ ×ˢ A₂) : f u ≤ f (altStep c₁ c₂ u) :=
  ((h₁ u.2 hu.2).2 u.1 hu.1).trans ((h₂ _ (h₁ u.2 hu.2).1).2 u.2 hu.2)

/-- **(9.10)–(9.13)** The values `f(u⁽ᵏ⁾)` are nondecreasing. -/
theorem le_altSeq_succ (h₁ : IsBestFst f A₁ A₂ c₁) (h₂ : IsBestSnd f A₁ A₂ c₂) {u₁ : E₁}
    (hu₁ : u₁ ∈ A₁) (k : ℕ) : f (altSeq c₁ c₂ u₁ k) ≤ f (altSeq c₁ c₂ u₁ (k + 1)) :=
  le_altStep h₁ h₂ (altSeq_mem h₁ h₂ hu₁ k)

/-! ### A coordinatewise maximum of a concave function -/

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- If the slopes of `g` at `0` from the right are at most `c`, so is its derivative. -/
lemma deriv_le_of_slope_le {g : ℝ → ℝ} {D c : ℝ} (hg : HasDerivAt g D 0)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, (g t - g 0) / t ≤ c) : D ≤ c := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  rw [slope_def_field, sub_zero]
  exact h t ht

/-- If the slopes of `g` at `0` from the right are at least `c`, so is its derivative. -/
lemma le_deriv_of_le_slope {g : ℝ → ℝ} {D c : ℝ} (hg : HasDerivAt g D 0)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, c ≤ (g t - g 0) / t) : c ≤ D := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  refine ge_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  rw [slope_def_field, sub_zero]
  exact h t ht

/-- The derivative of `f` along the line `u + t w` at `t = 0`. -/
lemma hasDerivAt_line {u w : E₁ × E₂} (hd : DifferentiableAt ℝ f u) :
    HasDerivAt (fun t : ℝ => f (u + t • w)) (fderiv ℝ f u w) 0 := by
  have h₁ : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id' 0
  have hl : HasDerivAt (fun t : ℝ => u + t • w) w 0 := by
    simpa using (h₁.smul_const w).const_add u
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

/-- **(9.93)–(9.101)** For a concave function differentiable at `u`, a point that maximizes `f` in
each variable separately maximizes `f`. -/
theorem le_of_isMax_coordinatewise (hA₁ : Convex ℝ A₁) (hA₂ : Convex ℝ A₂)
    (hf : ConcaveOn ℝ (A₁ ×ˢ A₂) f) {u : E₁ × E₂} (hu : u ∈ A₁ ×ˢ A₂)
    (hd : DifferentiableAt ℝ f u) (h₁ : ∀ v₁ ∈ A₁, f (v₁, u.2) ≤ f u)
    (h₂ : ∀ v₂ ∈ A₂, f (u.1, v₂) ≤ f u) {v : E₁ × E₂} (hv : v ∈ A₁ ×ˢ A₂) : f v ≤ f u := by
  set L := fderiv ℝ f u
  -- The derivative in the first and in the second variable is at most `0`.
  have hL₁ : L (v.1 - u.1, 0) ≤ 0 := by
    refine deriv_le_of_slope_le (hasDerivAt_line hd) fun t ht => ?_
    have hmem : u.1 + t • (v.1 - u.1) ∈ A₁ := hA₁.add_smul_sub_mem hu.1 hv.1 ⟨ht.1.le, ht.2.le⟩
    have : u + t • (v.1 - u.1, (0 : E₂)) = (u.1 + t • (v.1 - u.1), u.2) := by ext <;> simp
    simp only [this, zero_smul, add_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (h₁ _ hmem)) ht.1.le
  have hL₂ : L (0, v.2 - u.2) ≤ 0 := by
    refine deriv_le_of_slope_le (hasDerivAt_line hd) fun t ht => ?_
    have hmem : u.2 + t • (v.2 - u.2) ∈ A₂ := hA₂.add_smul_sub_mem hu.2 hv.2 ⟨ht.1.le, ht.2.le⟩
    have : u + t • ((0 : E₁), v.2 - u.2) = (u.1, u.2 + t • (v.2 - u.2)) := by ext <;> simp
    simp only [this, zero_smul, add_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (h₂ _ hmem)) ht.1.le
  -- Concavity: `f(v) - f(u) ≤ L (v - u)`.
  have hL : f v - f u ≤ L (v - u) := by
    refine le_deriv_of_le_slope (hasDerivAt_line hd) fun t ht => ?_
    have hc := hf.2 hu hv (show 0 ≤ 1 - t by linarith [ht.2]) ht.1.le (show 1 - t + t = 1 by ring)
    have e : (1 - t) • u + t • v = u + t • (v - u) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e, smul_eq_mul, smul_eq_mul] at hc
    simp only [zero_smul, add_zero]
    rw [le_div_iff₀ ht.1]
    linarith
  have hsplit : v - u = (v.1 - u.1, (0 : E₂)) + ((0 : E₁), v.2 - u.2) := by ext <;> simp
  rw [hsplit, map_add] at hL
  linarith

/-! ### Lemma 9.4 and Theorem 9.5 -/

/-- The maximizer `c₁(u₂)` is unique. -/
def IsUniqueBestFst (f : E₁ × E₂ → ℝ) (A₁ : Set E₁) (A₂ : Set E₂) (c₁ : E₂ → E₁) : Prop :=
  ∀ u₂ ∈ A₂, ∀ u₁ ∈ A₁, f (c₁ u₂, u₂) ≤ f (u₁, u₂) → u₁ = c₁ u₂

/-- The maximizer `c₂(u₁)` is unique. -/
def IsUniqueBestSnd (f : E₁ × E₂ → ℝ) (A₁ : Set E₁) (A₂ : Set E₂) (c₂ : E₁ → E₂) : Prop :=
  ∀ u₁ ∈ A₁, ∀ u₂ ∈ A₂, f (u₁, c₂ u₁) ≤ f (u₁, u₂) → u₂ = c₂ u₁

/-- **Lemma 9.4.** For a concave function, differentiable on `A₁ × A₂`, with unique maximizers in
each variable: if `f(u) < f*`, one round strictly increases `f`. -/
theorem lt_altStep (hA₁ : Convex ℝ A₁) (hA₂ : Convex ℝ A₂) (hf : ConcaveOn ℝ (A₁ ×ˢ A₂) f)
    (hd : ∀ u ∈ A₁ ×ˢ A₂, DifferentiableAt ℝ f u) (h₁ : IsBestFst f A₁ A₂ c₁)
    (h₂ : IsBestSnd f A₁ A₂ c₂) (hu₁ : IsUniqueBestFst f A₁ A₂ c₁)
    (hu₂ : IsUniqueBestSnd f A₁ A₂ c₂) {u : E₁ × E₂} (hu : u ∈ A₁ ×ˢ A₂)
    (hlt : ∃ v ∈ A₁ ×ˢ A₂, f u < f v) : f u < f (altStep c₁ c₂ u) := by
  by_contra hle
  push Not at hle
  set a := c₁ u.2
  have ha : a ∈ A₁ := (h₁ u.2 hu.2).1
  have e₁ : f u ≤ f (a, u.2) := (h₁ u.2 hu.2).2 u.1 hu.1
  have e₂ : f (a, u.2) ≤ f (a, c₂ a) := (h₂ a ha).2 u.2 hu.2
  -- `u₁ = c₁(u₂)` and `u₂ = c₂(u₁)` by uniqueness, (9.86)–(9.92).
  have hfa : u.1 = a := hu₁ u.2 hu.2 u.1 hu.1 (by
    have : f (altStep c₁ c₂ u) = f (a, c₂ a) := rfl
    linarith)
  have hfu : f (a, c₂ a) ≤ f u := hle
  have hfb : u.2 = c₂ u.1 := hu₂ u.1 hu.1 u.2 hu.2 (by
    rw [hfa]
    have : f u = f (a, u.2) := by rw [← hfa]
    linarith)
  obtain ⟨v, hv, hfv⟩ := hlt
  refine absurd (le_of_isMax_coordinatewise hA₁ hA₂ hf hu (hd u hu) (fun v₁ hv₁ => ?_)
    (fun v₂ hv₂ => ?_) hv) (not_le.2 hfv)
  · calc f (v₁, u.2) ≤ f (a, u.2) := (h₁ u.2 hu.2).2 v₁ hv₁
      _ = f u := by rw [← hfa]
  · calc f (u.1, v₂) ≤ f (u.1, c₂ u.1) := (h₂ u.1 hu.1).2 v₂ hv₂
      _ = f u := by rw [← hfb]

/-- **Theorem 9.5.** For a concave function on a product of compact convex sets, continuous and
differentiable there, with unique and continuous maximizers in each variable, alternating
maximization converges to the maximum: `f(u⁽ᵏ⁾) → f*`. -/
theorem tendsto_altSeq (hA₁ : Convex ℝ A₁) (hA₂ : Convex ℝ A₂) (hK₁ : IsCompact A₁)
    (hK₂ : IsCompact A₂) (hf : ConcaveOn ℝ (A₁ ×ˢ A₂) f) (hfc : ContinuousOn f (A₁ ×ˢ A₂))
    (hd : ∀ u ∈ A₁ ×ˢ A₂, DifferentiableAt ℝ f u) (h₁ : IsBestFst f A₁ A₂ c₁)
    (h₂ : IsBestSnd f A₁ A₂ c₂) (hu₁ : IsUniqueBestFst f A₁ A₂ c₁)
    (hu₂ : IsUniqueBestSnd f A₁ A₂ c₂) (hc₁ : ContinuousOn c₁ A₂) (hc₂ : ContinuousOn c₂ A₁)
    {u₁ : E₁} (hu : u₁ ∈ A₁) :
    Tendsto (fun k => f (altSeq c₁ c₂ u₁ k)) atTop (𝓝 (sSup (f '' (A₁ ×ˢ A₂)))) := by
  set A := A₁ ×ˢ A₂
  set u := altSeq c₁ c₂ u₁
  have hK : IsCompact A := hK₁.prod hK₂
  have huA : ∀ k, u k ∈ A := altSeq_mem h₁ h₂ hu
  have hbdd : BddAbove (f '' A) := hK.bddAbove_image hfc
  have hmono : Monotone fun k => f (u k) := monotone_nat_of_le_succ (le_altSeq_succ h₁ h₂ hu)
  have hbdd' : BddAbove (Set.range fun k => f (u k)) :=
    hbdd.mono (by rintro _ ⟨k, rfl⟩; exact ⟨u k, huA k, rfl⟩)
  set L := ⨆ k, f (u k)
  have hL : Tendsto (fun k => f (u k)) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd'
  -- A limit point `ū` of the iteration has `f(ū) = L` and `f(step ū) = f(ū)`.
  obtain ⟨ū, hū, φ, hφ, hlim⟩ := hK.tendsto_subseq huA
  have hlimA : Tendsto (fun k => u (φ k)) atTop (𝓝[A] ū) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => huA _⟩
  have hfū : f ū = L :=
    tendsto_nhds_unique ((hfc ū hū).tendsto.comp hlimA) (hL.comp hφ.tendsto_atTop)
  have hstepc : ContinuousOn (altStep c₁ c₂) A := by
    have hs : ContinuousOn (fun z : E₁ × E₂ => c₁ z.2) A :=
      hc₁.comp continuous_snd.continuousOn fun z hz => hz.2
    refine hs.prodMk (hc₂.comp hs fun z hz => (h₁ z.2 hz.2).1)
  have hstep : Tendsto (fun k => f (altStep c₁ c₂ (u (φ k)))) atTop
      (𝓝 (f (altStep c₁ c₂ ū))) := by
    refine (hfc _ (altStep_mem h₁ h₂ hū)).tendsto.comp ?_
    exact tendsto_nhdsWithin_iff.2 ⟨(hstepc ū hū).tendsto.comp hlimA,
      Eventually.of_forall fun k => altStep_mem h₁ h₂ (huA _)⟩
  have hstep' : Tendsto (fun k => f (altStep c₁ c₂ (u (φ k)))) atTop (𝓝 L) :=
    hL.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
  have hfix : f (altStep c₁ c₂ ū) = f ū := by
    rw [tendsto_nhds_unique hstep hstep', hfū]
  -- `L` is the supremum, by Lemma 9.4.
  have hle : L ≤ sSup (f '' A) :=
    ciSup_le fun k => le_csSup hbdd ⟨u k, huA k, rfl⟩
  have hge : sSup (f '' A) ≤ L := by
    by_contra hlt
    push Not at hlt
    obtain ⟨_, ⟨v, hv, rfl⟩, hv'⟩ := exists_lt_of_lt_csSup (s := f '' A) ⟨f ū, ⟨ū, hū, rfl⟩⟩
      (show f ū < sSup (f '' A) by rw [hfū]; exact hlt)
    exact absurd hfix (lt_altStep hA₁ hA₂ hf hd h₁ h₂ hu₁ hu₂ hū ⟨v, hv, hv'⟩).ne'
  rwa [le_antisymm hle hge] at hL

end InfoTheory
