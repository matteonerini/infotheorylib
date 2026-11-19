/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.InfoInequalities.NonShannon
public import InfoTheoryLib.Probability.SupportMixture
public import InfoTheoryLib.Statistics.LargeDeviations
public import InfoTheoryLib.Typicality.Basic

/-!
# Entropy and groups

Subgroups `G₁, …, Gₙ` of a finite group `G` give the entropy function `h_α = log (|G| / |G_α|)`,
where `G_α = ⋂_{i ∈ α} Gᵢ` (Theorem 16.16): take `Λ` uniform on `G` and `Xᵢ = Λ Gᵢ`, its left
coset. Such vectors form the region `Υₙ` of group-characterizable entropy functions, and every
entropy function is a limit of `f(r) / r` with `f(r) ∈ Υₙ` (Theorem 16.22): for the stabilizers
`Gᵢ` in the symmetric group on `r` letters of the `i`-th coordinates of a sequence of length `r`,
`|G| / |G_α|` is the multinomial coefficient of the type of the `α`-coordinates. So the closure of
the convex hull of `Υₙ` is the closure of `Γ*ₙ` (Corollary 16.24), and an unconstrained
information inequality holds if and only if the corresponding group inequality holds for all
finite groups.

## Main definitions

* `subgroupInter H s`: the intersection `G_s = ⋂_{i ∈ s} Gᵢ`.
* `groupEntropy H`: the vector `h_α = log (|G| / |G_α|)` of (16.45).
* `groupCharRegion ι`: the region `Υₙ` of (16.65).
* `permStab y`: the permutations `σ` of the positions of a sequence `y` with `y ∘ σ = y`.

## Main statements

* `ncard_iInter_smul_subgroup`: **Lemma 16.15**.
* `groupEntropy_mem_entropicRegion`: **Theorem 16.16**.
* `exists_tendsto_smul_groupEntropy`: **Theorem 16.22**.
* `tendsto_log_multinomial`: **Lemma 16.23**.
* `closure_convexHull_groupCharRegion`: **Corollary 16.24**.
* `ineqAlwaysHolds_iff_groupEntropy`: (16.84)–(16.89).
* `card_mul_mul_card_inf`: **Proposition 16.26**.
* `card_inf_mul_card_inf_le`: **Theorem 16.27**.
* `card_inf_pow_mul_le_of_zhangYeung`: the group inequality (16.5) from Theorem 15.7.

## Implementation notes

The book approximates a general distribution by rational ones and then takes `r` along multiples
of the common denominator. Here, for every `r`, a sequence of length `r` whose type is within
`|Ω| / r` of the distribution is used directly, so `f(r)` is defined for every `r`. The bounds on
the size of a type class (Theorem 11.1.3 of [cover2006]) replace Lemma 16.23 in the proof.

The region `Υₙ` takes groups in the universe of the index type, as `Γ*ₙ` does. Theorem 16.22,
which uses symmetric groups on `Fin r`, is stated for index types in `Type`.

## References

Numbers without a source refer to [yeung2008].

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 16
* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 11.1
-/

open Real Finset Filter Topology
open scoped Pointwise

@[expose] public noncomputable section

namespace InfoTheory

universe u

/-! ### Intersections of subgroups and their cosets -/

section Subgroups

variable {G : Type*} [Group G] {ι : Type*}

/-- The intersection `G_s = ⋂_{i ∈ s} Gᵢ` of the subgroups `Gᵢ`, a subgroup by Corollary 16.14. -/
def subgroupInter (H : ι → Subgroup G) (s : Finset ι) : Subgroup G := ⨅ i ∈ s, H i

lemma mem_subgroupInter {H : ι → Subgroup G} {s : Finset ι} {x : G} :
    x ∈ subgroupInter H s ↔ ∀ i ∈ s, x ∈ H i := by
  simp [subgroupInter, Subgroup.mem_iInf]

lemma coe_subgroupInter (H : ι → Subgroup G) (s : Finset ι) :
    (subgroupInter H s : Set G) = ⋂ i ∈ s, (H i : Set G) := by
  ext x
  simp [mem_subgroupInter]

@[simp] lemma subgroupInter_empty (H : ι → Subgroup G) : subgroupInter H ∅ = ⊤ := by
  simp [subgroupInter]

lemma subgroupInter_insert [DecidableEq ι] (H : ι → Subgroup G) (i : ι) (s : Finset ι) :
    subgroupInter H (insert i s) = H i ⊓ subgroupInter H s := by
  rw [subgroupInter, Finset.iInf_insert]
  rfl

@[simp] lemma subgroupInter_singleton (H : ι → Subgroup G) (i : ι) :
    subgroupInter H {i} = H i := by
  simp [subgroupInter]

open Classical in
/-- **Lemma 16.15.** An intersection `⋂_{i ∈ s} aᵢ Gᵢ` of left cosets is empty or has `|G_s|`
elements, (16.40). -/
theorem ncard_iInter_smul_subgroup (H : ι → Subgroup G) (s : Finset ι) (a : ι → G) :
    (⋂ i ∈ s, a i • (H i : Set G)).ncard =
      if (⋂ i ∈ s, a i • (H i : Set G)).Nonempty then Nat.card (subgroupInter H s) else 0 := by
  split_ifs with hne
  · obtain ⟨x, hx⟩ := hne
    simp only [Set.mem_iInter, mem_leftCoset_iff] at hx
    have he : ⋂ i ∈ s, a i • (H i : Set G) = x • (subgroupInter H s : Set G) := by
      ext y
      simp only [Set.mem_iInter, mem_leftCoset_iff, SetLike.mem_coe, mem_subgroupInter]
      refine forall₂_congr fun i hi => ?_
      rw [show (a i)⁻¹ * y = (a i)⁻¹ * x * (x⁻¹ * y) by group,
        Subgroup.mul_mem_cancel_left _ (hx i hi)]
    rw [he, Set.ncard_smul_set]
    exact (Nat.card_coe_set_eq _).symm
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.ncard_empty]

end Subgroups

/-! ### Group-characterizable entropy functions -/

section Characterization

variable {ι : Type*} {G : Type*} [Group G]

/-- The vector `h_α = log (|G| / |G_α|)` of (16.45) given by subgroups `Gᵢ` of `G`;
`(G, G₁, …, Gₙ)` is a group characterization of `h` (Definition 16.17) when
`h = groupEntropy H`. -/
def groupEntropy (H : ι → Subgroup G) : EntropySpace ι :=
  fun α => log (Nat.card G / Nat.card (subgroupInter H α.val))

lemma extend_groupEntropy [Finite G] (H : ι → Subgroup G) (s : Finset ι) :
    (groupEntropy H).extend s = log (Nat.card G) - log (Nat.card (subgroupInter H s)) := by
  rw [EntropySpace.extend]
  split_ifs with hs
  · rw [groupEntropy, log_div (by exact_mod_cast Nat.card_pos.ne') (by exact_mod_cast
      Nat.card_pos.ne')]
  · rw [not_nonempty_iff_eq_empty.1 hs, subgroupInter_empty, Subgroup.card_top, sub_self]

/-- The trivial characterization `Gᵢ = G` gives the origin. -/
lemma groupEntropy_top [Finite G] : groupEntropy (fun _ : ι => (⊤ : Subgroup G)) = 0 := by
  funext α
  have : subgroupInter (fun _ : ι => (⊤ : Subgroup G)) α.val = ⊤ := by simp [subgroupInter]
  rw [groupEntropy, this, Subgroup.card_top,
    div_self (by exact_mod_cast Nat.card_pos.ne'), log_one, Pi.zero_apply]

/-- A uniform `ω` whose image under `V` determines `ω` up to `k` choices: `H(V) = log (|Ω| / k)`. -/
lemma entropyRV_uniformPMF_of_card_fiber {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [Fintype β]
    (V : Ω → β) (k : ℕ) (hk : ∀ ω, Nat.card {ω' // V ω' = V ω} = k) :
    H[V ; uniformPMF Ω] = log (Fintype.card Ω / k) := by
  classical
  have hd : ∀ ω, dist (uniformPMF Ω) V (V ω) = k / Fintype.card Ω := fun ω => by
    rw [dist, ← sum_filter]
    simp only [uniformPMF, sum_const, nsmul_eq_mul]
    rw [← hk ω, Nat.card_eq_fintype_card, Fintype.card_subtype]
    ring
  rw [entropyRV, entropy, sum_dist_mul (uniformPMF Ω) V fun b => log (dist (uniformPMF Ω) V b)]
  simp only [hd, uniformPMF, sum_const, card_univ, nsmul_eq_mul]
  have : (Fintype.card Ω : ℝ) * (1 / Fintype.card Ω * log (k / Fintype.card Ω)) =
      log (k / Fintype.card Ω) := by field_simp
  rw [this, ← log_inv, inv_div]

/-- **Theorem 16.16.** For subgroups `Gᵢ` of a finite group `G`, `h_α = log (|G| / |G_α|)` is
entropic: it is the entropy function of the cosets `Xᵢ = Λ Gᵢ` of a uniform `Λ` on `G`. -/
theorem groupEntropy_mem_entropicRegion {ι G : Type u} [Fintype ι] [DecidableEq ι] [Group G]
    [Finite G] (H : ι → Subgroup G) : groupEntropy H ∈ entropicRegion ι := by
  classical
  have := Fintype.ofFinite G
  refine ⟨G, inferInstance, fun i => G ⧸ H i, fun _ => inferInstance, uniformPMF G,
    fun i g => (g : G ⧸ H i), uniformPMF_isPMF, funext fun α => ?_⟩
  -- the fiber of `ω` is the coset `ω G_α`
  have hfib : ∀ ω ω', blockRV (fun i (g : G) => (g : G ⧸ H i)) α.val ω' =
      blockRV (fun i (g : G) => (g : G ⧸ H i)) α.val ω ↔ ω⁻¹ * ω' ∈ subgroupInter H α.val := by
    intro ω ω'
    simp only [blockRV, funext_iff, Subtype.forall, mem_subgroupInter]
    refine forall₂_congr fun i _ => ?_
    rw [eq_comm, QuotientGroup.eq]
  have hk : ∀ ω, Nat.card {ω' // blockRV (fun i (g : G) => (g : G ⧸ H i)) α.val ω' =
      blockRV (fun i (g : G) => (g : G ⧸ H i)) α.val ω} = Nat.card (subgroupInter H α.val) :=
    fun ω => Nat.card_congr
      { toFun := fun ω' => ⟨ω⁻¹ * ω'.val, (hfib ω ω'.val).1 ω'.property⟩
        invFun := fun x => ⟨ω * x.val, (hfib ω _).2 (by simp)⟩
        left_inv := fun ω' => by ext; simp
        right_inv := fun x => by ext; simp }
  rw [entropyVector, blockEntropy, entropyRV_uniformPMF_of_card_fiber _ _ hk, groupEntropy,
    Nat.card_eq_fintype_card (α := G)]

/-- **Definition 16.21.** The region `Υₙ` of the vectors that have a group characterization,
(16.65). -/
def groupCharRegion (ι : Type u) [Fintype ι] [DecidableEq ι] : Set (EntropySpace ι) :=
  {h | ∃ (G : Type u) (_ : Group G) (_ : Finite G) (H : ι → Subgroup G), h = groupEntropy H}

lemma groupEntropy_mem_groupCharRegion {ι G : Type u} [Fintype ι] [DecidableEq ι] [Group G]
    [Finite G] (H : ι → Subgroup G) : groupEntropy H ∈ groupCharRegion ι :=
  ⟨G, inferInstance, inferInstance, H, rfl⟩

/-- `Υₙ ⊂ Γ*ₙ`, by Theorem 16.16. -/
lemma groupCharRegion_subset_entropicRegion {ι : Type u} [Fintype ι] [DecidableEq ι] :
    groupCharRegion ι ⊆ entropicRegion ι := by
  rintro _ ⟨G, _, _, H, rfl⟩
  exact groupEntropy_mem_entropicRegion H

/-- The origin is in `Υₙ` (Example 16.19 with `β = ∅`). -/
lemma zero_mem_groupCharRegion {ι : Type u} [Fintype ι] [DecidableEq ι] :
    (0 : EntropySpace ι) ∈ groupCharRegion ι :=
  ⟨PUnit, inferInstance, inferInstance, fun _ => ⊤, groupEntropy_top.symm⟩

end Characterization

/-! ### Stabilizers in the symmetric group -/

section Stabilizer

variable {T β : Type*}

/-- The permutations `σ` of the positions of a sequence `y` with `y ∘ σ = y`: the subgroup `Gᵢ` of
the proof of Theorem 16.22. -/
def permStab (y : T → β) : Subgroup (Equiv.Perm T) where
  carrier := {σ | y ∘ σ = y}
  mul_mem' {σ τ} hσ hτ := by
    have hσ : y ∘ σ = y := hσ
    have hτ : y ∘ τ = y := hτ
    change y ∘ ⇑(σ * τ) = y
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ, hτ]
  one_mem' := rfl
  inv_mem' {σ} hσ := by
    have hσ : y ∘ σ = y := hσ
    change y ∘ ⇑σ⁻¹ = y
    calc y ∘ ⇑σ⁻¹ = (y ∘ σ) ∘ ⇑σ⁻¹ := by rw [hσ]
      _ = y := by
        rw [Function.comp_assoc, ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one,
          Function.comp_id]

lemma mem_permStab {y : T → β} {σ : Equiv.Perm T} : σ ∈ permStab y ↔ y ∘ σ = y := Iff.rfl

/-- The stabilizers of the coordinates of a sequence meet in the stabilizer of the sequence of
the `s`-blocks, (16.72)–(16.75). -/
lemma subgroupInter_permStab {ι Ω : Type*} {A : ι → Type*} (X : ∀ i, Ω → A i) (x : T → Ω)
    (s : Finset ι) :
    subgroupInter (fun i => permStab (X i ∘ x)) s = permStab (blockRV X s ∘ x) := by
  ext σ
  simp only [mem_subgroupInter, mem_permStab, funext_iff, Function.comp_apply, blockRV,
    Subtype.forall]
  exact ⟨fun h j i hi => h i hi j, fun h i hi j => h j i hi⟩

/-- (16.79)–(16.80): `|T(P_y)| |G_y| = r!` for the stabilizer `G_y` of a sequence `y`. -/
lemma card_typeClass_mul_card_permStab [Fintype β] {r : ℕ} (y : Fin r → β) :
    #(typeClass (typeOf y) r) * Nat.card (permStab y) = r.factorial := by
  classical
  rw [← card_typeClass_mul_prod_factorial y]
  congr 1
  change Nat.card {σ : Equiv.Perm (Fin r) // y ∘ σ = y} = _
  rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
  refine prod_congr rfl fun b _ => ?_
  rw [Fintype.card_subtype, symbolCount]

/-- The group characterization by the stabilizers of the coordinates of a sequence `x` has
`h_α = log |T(P)|` for the type `P` of the `α`-coordinates of `x`. -/
lemma groupEntropy_permStab {ι Ω : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (X : ∀ i, Ω → A i) {r : ℕ} (x : Fin r → Ω)
    (α : {s : Finset ι // s.Nonempty}) :
    groupEntropy (fun i => permStab (X i ∘ x)) α =
      log #(typeClass (typeOf (blockRV X α.val ∘ x)) r) := by
  have h := card_typeClass_mul_card_permStab (blockRV X α.val ∘ x)
  have hpos : (0 : ℝ) < Nat.card (permStab (blockRV X α.val ∘ x)) := by
    exact_mod_cast Nat.card_pos
  rw [groupEntropy, subgroupInter_permStab, Nat.card_perm, Nat.card_fin, ← h]
  push_cast
  rw [mul_div_cancel_right₀ _ hpos.ne']

end Stabilizer

/-! ### Bounds on the size of a type class -/

section TypeBounds

variable {α : Type*} [Fintype α]

/-- `log |T(P)| ≤ r H(P)`. -/
lemma log_card_typeClass_le {r : ℕ} (hr : 0 < r) (x : Fin r → α) :
    log #(typeClass (typeOf x) r) ≤ r * entropy (typeOf x) := by
  have hpos : (0 : ℝ) < #(typeClass (typeOf x) r) := by
    exact_mod_cast card_pos.2 ⟨x, mem_typeClass.2 rfl⟩
  rw [← log_exp (r * entropy (typeOf x))]
  exact log_le_log hpos (card_typeClass_le hr x)

/-- `r H(P) - |𝒳| log (r + 1) ≤ log |T(P)|`. -/
lemma sub_le_log_card_typeClass {r : ℕ} (hr : 0 < r) (x : Fin r → α) :
    r * entropy (typeOf x) - Fintype.card α * log (r + 1) ≤ log #(typeClass (typeOf x) r) := by
  have hpos : (0 : ℝ) < exp (r * entropy (typeOf x)) / (r + 1) ^ Fintype.card α := by positivity
  have := log_le_log hpos (exp_div_le_card_typeClass hr x)
  rwa [log_div (exp_pos _).ne' (by positivity), log_exp, log_pow] at this

/-- **Lemma 16.23.** For a distribution `p(a) = kₐ / q` with denominator `q`,
`(1 / r) log (r! / ∏ₐ (r p(a))!) → H(p)` as `r = q m → ∞`, (16.66). -/
theorem tendsto_log_multinomial {q : ℕ} (hq : 0 < q) (k : α → ℕ) (hk : ∑ a, k a = q) :
    Tendsto (fun m : ℕ => ((q * m : ℕ) : ℝ)⁻¹ *
      log ((q * m).factorial / ∏ a, ((m * k a).factorial : ℝ))) atTop
        (𝓝 (entropy fun a => (k a : ℝ) / q)) := by
  classical
  -- a sequence of length `q m` with `m kₐ` occurrences of `a`
  have hx : ∀ m, ∃ x : Fin (q * m) → α, ∀ a, symbolCount x a = m * k a := fun m =>
    exists_symbolCount_eq _ (by rw [← mul_sum, hk, mul_comm])
  choose x hx using hx
  have htype : ∀ m, 0 < m → typeOf (x m) = fun a => (k a : ℝ) / q := fun m hm => by
    funext a
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [typeOf, hx]
    push_cast
    field_simp
  have hcard : ∀ m, ((q * m).factorial : ℝ) / ∏ a, ((m * k a).factorial : ℝ) =
      #(typeClass (typeOf (x m)) (q * m)) := fun m => by
    have := card_typeClass_mul_prod_factorial (x m)
    simp only [hx] at this
    rw [← this]
    push_cast
    rw [mul_div_cancel_right₀ _ (by positivity)]
  have hr : Tendsto (fun m : ℕ => q * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hq) tendsto_id
  have hlog : Tendsto (fun m : ℕ => (Fintype.card α : ℝ) *
      (log (((q * m : ℕ) : ℝ) + 1) / ((q * m : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_log_add_one_div.comp hr).const_mul (Fintype.card α : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds.sub hlog)
    tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hqm : 0 < q * m := Nat.mul_pos hq hm
    have hqm' : (0 : ℝ) < (q * m : ℕ) := by exact_mod_cast hqm
    have := sub_le_log_card_typeClass hqm (x m)
    rw [hcard, ← htype m hm]
    calc _ = ((q * m : ℕ) : ℝ)⁻¹ * ((q * m : ℕ) * entropy (typeOf (x m)) -
          Fintype.card α * log (((q * m : ℕ) : ℝ) + 1)) := by
          push_cast at hqm' ⊢
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hqm'.le)
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hqm : 0 < q * m := Nat.mul_pos hq hm
    have hqm' : (0 : ℝ) < (q * m : ℕ) := by exact_mod_cast hqm
    rw [hcard, ← htype m hm]
    calc ((q * m : ℕ) : ℝ)⁻¹ * log #(typeClass (typeOf (x m)) (q * m))
        ≤ ((q * m : ℕ) : ℝ)⁻¹ * ((q * m : ℕ) * entropy (typeOf (x m))) :=
          mul_le_mul_of_nonneg_left (log_card_typeClass_le hqm (x m)) (inv_nonneg.2 hqm'.le)
      _ = entropy (typeOf (x m)) := by field_simp

end TypeBounds

/-! ### A group characterization of `Γ̄*ₙ` -/

section Closure

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Theorem 16.22.** For every `h ∈ Γ*ₙ` there are `f(r) ∈ Υₙ` with `f(r) / r → h`. -/
theorem exists_tendsto_smul_groupEntropy {h : EntropySpace ι} (hh : h ∈ entropicRegion ι) :
    ∃ f : ℕ → EntropySpace ι, (∀ r, f r ∈ groupCharRegion ι) ∧
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹ • f r) atTop (𝓝 h) := by
  classical
  obtain ⟨Ω, _, A, _, μ, X, hμ, rfl⟩ := hh
  -- for each `r`, a sequence of length `r` whose type is close to `μ`
  have hx : ∀ r : ℕ, ∃ x : Fin r → Ω, 0 < r → ∀ ω, |typeOf x ω - μ ω| ≤ Fintype.card Ω / r := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact ⟨Fin.elim0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨x, hx, -⟩ := exists_typeOf_near hμ hr
      exact ⟨x, fun _ => hx⟩
  choose x hx using hx
  refine ⟨fun r => groupEntropy fun i => permStab (X i ∘ x r),
    fun r => groupEntropy_mem_groupCharRegion _, ?_⟩
  have hP : Tendsto (fun r => typeOf (x r)) atTop (𝓝 μ) := by
    refine tendsto_pi_nhds.2 fun ω => ?_
    have : Tendsto (fun r => typeOf (x r) ω - μ ω) atTop (𝓝 0) :=
      squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun r hr => by
        rw [Real.norm_eq_abs]
        exact hx r hr ω) (tendsto_const_div_atTop_nhds_zero_nat _)
    simpa using this.add_const (μ ω)
  refine tendsto_pi_nhds.2 fun α => ?_
  -- the entropy of the type of the `α`-coordinates converges to `H(X_α)`, (16.81)
  have hH : Tendsto (fun r => entropy (typeOf (blockRV X α.val ∘ x r))) atTop
      (𝓝 (entropyVector μ X α)) := by
    refine (((continuous_entropy_dist (blockRV X α.val)).tendsto μ).comp hP).congr fun r => ?_
    simp only [Function.comp_apply]
    congr 1
    funext b
    rw [typeOf_comp]
  have hlog := tendsto_log_add_one_div.const_mul (Fintype.card (∀ i : α.val, A i) : ℝ)
  rw [mul_zero] at hlog
  have hlow := hH.sub hlog
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hH ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have := sub_le_log_card_typeClass hr (blockRV X α.val ∘ x r)
    rw [Pi.smul_apply, smul_eq_mul, groupEntropy_permStab]
    calc entropy (typeOf (blockRV X α.val ∘ x r)) -
          Fintype.card (∀ i : α.val, A i) * (log ((r : ℝ) + 1) / r)
        = (r : ℝ)⁻¹ * (r * entropy (typeOf (blockRV X α.val ∘ x r)) -
          Fintype.card (∀ i : α.val, A i) * log ((r : ℝ) + 1)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hr'.le)
  · filter_upwards [eventually_gt_atTop 0] with r hr
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    rw [Pi.smul_apply, smul_eq_mul, groupEntropy_permStab]
    calc (r : ℝ)⁻¹ * log #(typeClass (typeOf (blockRV X α.val ∘ x r)) r)
        ≤ (r : ℝ)⁻¹ * (r * entropy (typeOf (blockRV X α.val ∘ x r))) :=
          mul_le_mul_of_nonneg_left (log_card_typeClass_le hr _) (inv_nonneg.2 hr'.le)
      _ = entropy (typeOf (blockRV X α.val ∘ x r)) := by field_simp

/-- **Corollary 16.24.** The closure of the convex hull of `Υₙ` is the closure of `Γ*ₙ`. -/
theorem closure_convexHull_groupCharRegion :
    closure (convexHull ℝ (groupCharRegion ι)) = closure (entropicRegion ι) := by
  refine subset_antisymm (closure_minimal (convexHull_min
    (groupCharRegion_subset_entropicRegion.trans subset_closure) convex_closure_entropicRegion)
      isClosed_closure) (closure_minimal (fun h hh => ?_) isClosed_closure)
  obtain ⟨f, hf, ht⟩ := exists_tendsto_smul_groupEntropy hh
  refine mem_closure_of_tendsto ht ((eventually_ge_atTop 1).mono fun r hr => ?_)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have := convex_convexHull ℝ (groupCharRegion ι) (subset_convexHull ℝ _ (hf r))
    (subset_convexHull ℝ _ zero_mem_groupCharRegion) (inv_nonneg.2 (by linarith))
    (sub_nonneg.2 (inv_le_one_of_one_le₀ hr')) (add_sub_cancel _ _)
  rw [smul_zero, add_zero] at this
  exact this

/-- **(16.84)–(16.89)** An unconstrained information inequality `b ⬝ h ≥ 0` always holds if and
only if the group inequality obtained by replacing each `h_α` by `log (|G| / |G_α|)` holds for
all finite groups `G` and subgroups `G₁, …, Gₙ`. -/
theorem ineqAlwaysHolds_iff_groupEntropy (b : EntropySpace ι) :
    IneqAlwaysHolds b Set.univ ↔ ∀ (G : Type) [Group G] [Finite G] (H : ι → Subgroup G),
      0 ≤ infoExpr b (groupEntropy H) := by
  rw [ineqAlwaysHolds_iff_closure_subset]
  refine ⟨fun hs G _ _ H => hs (subset_closure (groupEntropy_mem_entropicRegion H)), fun hg => ?_⟩
  have hc : IsClosed {h : EntropySpace ι | 0 ≤ infoExpr b h} :=
    isClosed_le continuous_const
      (continuous_finsetSum _ fun α _ => continuous_const.mul (continuous_apply α))
  have hcv : Convex ℝ {h : EntropySpace ι | 0 ≤ infoExpr b h} := by
    intro x hx y hy a c ha hc _
    have e : infoExpr b (a • x + c • y) = a * infoExpr b x + c * infoExpr b y := by
      simp only [infoExpr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun α _ => by ring
    change 0 ≤ infoExpr b (a • x + c • y)
    rw [e]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hc hy)
  rw [← closure_convexHull_groupCharRegion]
  refine closure_minimal (convexHull_min ?_ hcv) hc
  rintro _ ⟨G, _, _, H, rfl⟩
  exact hg G H

end Closure

/-! ### Group inequalities -/

section GroupInequalities

variable {G : Type*} [Group G]

/-- **Proposition 16.26.** `|G₁ ∘ G₂| |G₁ ∩ G₂| = |G₁| |G₂|` for the product set
`G₁ ∘ G₂ = {a b : a ∈ G₁, b ∈ G₂}` of Definition 16.25, (16.91). -/
theorem card_mul_mul_card_inf [Finite G] (H K : Subgroup G) :
    Nat.card ((H : Set G) * (K : Set G)) * Nat.card (H ⊓ K : Subgroup G) =
      Nat.card H * Nat.card K := by
  classical
  have := Fintype.ofFinite G
  set m : H × K → G := fun p => (p.1 : G) * p.2 with hm
  have hrange : Set.range m = (H : Set G) * (K : Set G) := by
    ext y
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact Set.mul_mem_mul a.property b.property
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  -- each fiber of the multiplication has `|G₁ ∩ G₂|` elements, (16.92)–(16.102)
  have hfib : ∀ p : H × K,
      #(univ.filter fun p' => m p' = m p) = Fintype.card (H ⊓ K : Subgroup G) := by
    intro p
    rw [← card_univ]
    refine card_bij (fun p' hp' => ⟨(p.1 : G)⁻¹ * p'.1,
        H.mul_mem (H.inv_mem p.1.property) p'.1.property, ?_⟩)
      (fun _ _ => mem_univ _) (fun p' hp' q' hq' h => ?_) (fun k _ => ?_)
    · have e : (p'.1 : G) * p'.2 = p.1 * p.2 := (mem_filter.1 hp').2
      rw [show (p.1 : G)⁻¹ * p'.1 = p.2 * (p'.2 : G)⁻¹ by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
        exact e]
      exact K.mul_mem p.2.property (K.inv_mem p'.2.property)
    · have e₁ : (p'.1 : G) * p'.2 = p.1 * p.2 := (mem_filter.1 hp').2
      have e₂ : (q'.1 : G) * q'.2 = p.1 * p.2 := (mem_filter.1 hq').2
      have h₁ : (p'.1 : G) = q'.1 := mul_left_cancel (congrArg Subtype.val h)
      have h₂ : (p'.2 : G) = q'.2 := by
        rw [← e₂, h₁] at e₁
        exact mul_left_cancel e₁
      exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
    · refine ⟨(⟨p.1 * k, H.mul_mem p.1.property (Subgroup.mem_inf.1 k.property).1⟩,
        ⟨(k : G)⁻¹ * p.2,
            K.mul_mem (K.inv_mem (Subgroup.mem_inf.1 k.property).2) p.2.property⟩), ?_, ?_⟩
      · simp [hm, mul_assoc]
      · ext
        simp
  have hsum := card_eq_sum_card_image m (univ : Finset (H × K))
  have hc : ∀ y ∈ univ.image m, #(univ.filter fun a => m a = y) =
      Fintype.card (H ⊓ K : Subgroup G) := by
    intro y hy
    obtain ⟨p, -, hp⟩ := mem_image.1 hy
    rw [← hp]
    convert hfib p
  rw [sum_congr rfl hc, sum_const, smul_eq_mul, card_univ, Fintype.card_prod] at hsum
  rw [← hrange, Nat.card_eq_card_toFinset, Set.toFinset_range, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hsum]

/-- **Theorem 16.27.** `|G₁₃| |G₂₃| ≤ |G₃| |G₁₂₃|`, (16.104). -/
theorem card_inf_mul_card_inf_le [Finite G] (G₁ G₂ G₃ : Subgroup G) :
    Nat.card (G₁ ⊓ G₃ : Subgroup G) * Nat.card (G₂ ⊓ G₃ : Subgroup G) ≤
      Nat.card G₃ * Nat.card (G₁ ⊓ G₂ ⊓ G₃ : Subgroup G) := by
  have e := card_mul_mul_card_inf (G₁ ⊓ G₃) (G₂ ⊓ G₃)
  have hi : G₁ ⊓ G₃ ⊓ (G₂ ⊓ G₃) = G₁ ⊓ G₂ ⊓ G₃ := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hsub : ((G₁ ⊓ G₃ : Subgroup G) : Set G) * (G₂ ⊓ G₃ : Subgroup G) ⊆ G₃ := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy
    exact G₃.mul_mem (Subgroup.mem_inf.1 ha).2 (Subgroup.mem_inf.1 hb).2
  rw [hi] at e
  rw [← e]
  exact Nat.mul_le_mul_right _ (Nat.card_mono (Set.toFinite _) hsub)

/-- (16.3): `|G₁| |G₂| ≤ |G| |G₁ ∩ G₂|`, the case `G₃ = G` of Theorem 16.27. -/
theorem card_mul_card_le_card_mul_card_inf [Finite G] (G₁ G₂ : Subgroup G) :
    Nat.card G₁ * Nat.card G₂ ≤ Nat.card G * Nat.card (G₁ ⊓ G₂ : Subgroup G) := by
  simpa using card_inf_mul_card_inf_le G₁ G₂ ⊤

/-- The group inequality (16.5), (16.116), which corresponds to the Zhang–Yeung inequality
(15.62) by (16.114)–(16.115). The subgroups `G₁, …, G₄` of the book are `H 0, …, H 3`. -/
theorem card_inf_pow_mul_le_of_zhangYeung {G : Type} [Group G] [Finite G]
    (H : Fin 4 → Subgroup G) :
    Nat.card (H 0 ⊓ H 2 : Subgroup G) ^ 3 * Nat.card (H 0 ⊓ H 3 : Subgroup G) ^ 3 *
        Nat.card (H 2 ⊓ H 3 : Subgroup G) ^ 3 * Nat.card (H 1 ⊓ H 2 : Subgroup G) *
          Nat.card (H 1 ⊓ H 3 : Subgroup G) ≤
      Nat.card (H 0) * Nat.card (H 0 ⊓ H 1 : Subgroup G) * Nat.card (H 2) ^ 2 *
        Nat.card (H 3) ^ 2 * Nat.card (H 0 ⊓ H 2 ⊓ H 3 : Subgroup G) ^ 4 *
          Nat.card (H 1 ⊓ H 2 ⊓ H 3 : Subgroup G) := by
  have hz := infoExpr_zyCoeff_nonneg (groupEntropy_mem_entropicRegion H)
  rw [zyCoeff, infoExpr_canonicalForm] at hz
  simp only [zyFunctional, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    condInfoFunctional_apply, smul_eq_mul] at hz
  rw [condInfo_eq_of _ (S := {0}) (T := {1}) (K := ∅) (U₁ := {0}) (U₂ := {1}) (U₃ := {0, 1})
      (by decide) (by decide) (by decide),
    condInfo_eq_of _ (S := {0}) (T := {2, 3}) (K := ∅) (U₁ := {0}) (U₂ := {2, 3})
      (U₃ := {0, 2, 3}) (by decide) (by decide) (by decide),
    condInfo_eq_of _ (S := {2}) (T := {3}) (K := {0}) (U₁ := {0, 2}) (U₂ := {0, 3})
      (U₃ := {0, 2, 3}) (by decide) (by decide) (by decide),
    condInfo_eq_of _ (S := {2}) (T := {3}) (K := {1}) (U₁ := {1, 2}) (U₂ := {1, 3})
      (U₃ := {1, 2, 3}) (by decide) (by decide) (by decide),
    condInfo_eq_of _ (S := {2}) (T := {3}) (K := ∅) (U₁ := {2}) (U₂ := {3}) (U₃ := {2, 3})
      (by decide) (by decide) (by decide)] at hz
  simp only [EntropySpace.extend_empty, extend_groupEntropy, subgroupInter_insert,
    subgroupInter_singleton, ← inf_assoc] at hz
  have hx : ∀ K : Subgroup G, (Nat.card K : ℝ) = exp (log (Nat.card K)) := fun K =>
    (exp_log (by exact_mod_cast Nat.card_pos)).symm
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  rw [hx (H 0 ⊓ H 2), hx (H 0 ⊓ H 3), hx (H 2 ⊓ H 3), hx (H 1 ⊓ H 2), hx (H 1 ⊓ H 3), hx (H 0),
    hx (H 0 ⊓ H 1), hx (H 2), hx (H 3), hx (H 0 ⊓ H 2 ⊓ H 3), hx (H 1 ⊓ H 2 ⊓ H 3)]
  simp only [← exp_natCast_mul, ← exp_add, exp_le_exp]
  push_cast
  linarith

end GroupInequalities

end InfoTheory
