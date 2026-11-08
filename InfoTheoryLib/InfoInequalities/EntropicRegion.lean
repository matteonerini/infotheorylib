/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Capacity
public import InfoTheoryLib.ChannelCoding.Product
public import InfoTheoryLib.Entropy.Fano
public import InfoTheoryLib.Entropy.MrsGerber
public import InfoTheoryLib.IMeasure.CondMutIndep
public import InfoTheoryLib.InfoInequalities.ShannonType

/-!
# The structure of the region `Γ*ₙ`

The sum of two entropic vectors is entropic: take independent copies of the two collections of
random variables and pair them (Lemma 15.3). Mixing a collection with a constant one by an
independent coin of bias `δ` scales its entropy function by `δ`, up to the entropy `h(δ)` of the
coin. Together these show that the closure of `Γ*ₙ` is a convex cone (Theorem 15.5).

For two random variables `Γ*₂ = Γ₂` (Theorem 15.1), but `Γ*₃ ≠ Γ₃` (Theorem 15.2): the vector
`(a, a, a, 2a, 2a, 2a, 2a)` satisfies the elemental inequalities, but it is entropic only if
`a = log M` for an integer `M`, since three pairwise independent random variables each of which is
a function of the other two are uniform on their supports. The closure of `Γ*₃` is `Γ₃`
(Theorem 15.6).

## Main statements

* `add_mem_entropicRegion`, `nsmul_mem_entropicRegion`: **Lemma 15.3** and **Corollary 15.4**.
* `exists_mem_entropicRegion_eq_binEntropy_add`: the mixture with a constant collection.
* `convex_closure_entropicRegion`, `smul_mem_closure_entropicRegion`: **Theorem 15.5**.
* `ineqAlwaysHolds_iff_closure_subset`: (15.34)–(15.36).
* `entropicRegion_fin_two`: **Theorem 15.1**.
* `exists_eq_log_of_smul_rankTwo_mem`, `entropicRegion_fin_three_ne`: **Theorem 15.2**.
* `closure_entropicRegion_fin_three`: **Theorem 15.6**.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 15.1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

/-! ### Products of sample spaces -/

section Product

variable {Ω₀ Ω₁ Ω₂ α β γ : Type*} [Fintype Ω₀] [Fintype Ω₁] [Fintype Ω₂]

omit [Fintype Ω₀] in
/-- The entropy of a pair of random variables on the two factors of a product space. -/
lemma entropyRV_prodDist_pair [Fintype α] [Fintype β] {μ₁ : Ω₁ → ℝ} {μ₂ : Ω₂ → ℝ}
    (hμ₁ : IsPMF μ₁) (hμ₂ : IsPMF μ₂) (F : Ω₁ → α) (G : Ω₂ → β) :
    H[fun ω => (F ω.1, G ω.2) ; prodDist μ₁ μ₂] = H[F ; μ₁] + H[G ; μ₂] := by
  rw [entropyRV, show dist (prodDist μ₁ μ₂) (fun ω => (F ω.1, G ω.2)) =
    prodDist (dist μ₁ F) (dist μ₂ G) from funext fun z => dist_prodDist_pair μ₁ μ₂ F G z.1 z.2,
    entropy_prodDist (hμ₁.dist F) (hμ₂.dist G)]
  rfl

/-- The conditional entropy given the first coordinate of a product space. -/
lemma condEntropy_fst_prodDist [Fintype γ] {ν : Ω₀ → ℝ} {μ : Ω₁ → ℝ} (hμ : IsPMF μ)
    (V : Ω₀ × Ω₁ → γ) :
    H[V | Prod.fst ; prodDist ν μ] = ∑ b, ν b * H[fun ω => V (b, ω) ; μ] := by
  classical
  rw [condEntropy]
  refine sum_congr rfl fun b _ => ?_
  have hb : dist (prodDist ν μ) Prod.fst b = ν b := by
    have := dist_prodDist_comp_fst ν hμ (id : Ω₀ → Ω₀) b
    rwa [dist_id] at this
  rw [hb]
  by_cases hν0 : ν b = 0
  · rw [hν0, zero_mul, zero_mul]
  · congr 1
    rw [condEntropyAt, entropyRV]
    congr 1
    funext v
    rw [condDist, hb]
    have : dist (prodDist ν μ) (pair Prod.fst V) (b, v) =
        ν b * dist μ (fun ω => V (b, ω)) v := by
      simp only [dist, prodDist, pair, Fintype.sum_prod_type, Prod.mk.injEq, mul_sum]
      rw [sum_eq_single b]
      · exact sum_congr rfl fun ω _ => by split_ifs <;> simp_all
      · intro b' _ hb'
        exact sum_eq_zero fun ω _ => by simp [hb']
      · simp
    rw [this, mul_div_cancel_left₀ _ hν0]

end Product

/-- A random variable that is a function of `W` has zero conditional entropy given `W`. -/
lemma condEntropy_eq_zero_of_eq_comp {Ω σ α : Type*} [Fintype Ω] [Fintype σ] [Fintype α]
    {μ : Ω → ℝ} (hμ : IsPMF μ) {S : Ω → σ} {W : Ω → α} (g : α → σ) (h : ∀ ω, S ω = g (W ω)) :
    H[S | W ; μ] = 0 :=
  (condEntropy_eq_zero_iff hμ S W).2 ⟨g, fun ω _ => h ω⟩

/-- If `ω ↦ (U ω, V ω)` is a bijection and `ω` is uniform, then `U` and `V` are independent and
uniform. -/
lemma mutualInfo_eq_zero_and_entropyRV_of_equiv {Ω α β : Type*} [Fintype Ω] [Fintype α]
    [Fintype β] [Nonempty Ω] [Nonempty α] [Nonempty β] (e : Ω ≃ α × β) :
    I[fun ω => (e ω).1 : fun ω => (e ω).2 ; uniformPMF Ω] = 0 ∧
      H[fun ω => (e ω).1 ; uniformPMF Ω] = log (Fintype.card α) ∧
        H[fun ω => (e ω).2 ; uniformPMF Ω] = log (Fintype.card β) := by
  have hμ : IsPMF (uniformPMF Ω) := uniformPMF_isPMF
  have hcard : (Fintype.card Ω : ℝ) = Fintype.card α * Fintype.card β := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  have hpair : pair (fun ω => (e ω).1) (fun ω => (e ω).2) = e := rfl
  have hd : ∀ z, dist (uniformPMF Ω) (pair (fun ω => (e ω).1) (fun ω => (e ω).2)) z =
      1 / Fintype.card Ω := fun z => by
    rw [hpair, ← e.apply_symm_apply z]
    have := dist_comp_of_injective (uniformPMF Ω) id e.injective (e.symm z)
    rw [Function.comp_id] at this
    rw [show (e : Ω → α × β) = ⇑e from rfl, this, dist_id]
    rfl
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h₁ : dist (uniformPMF Ω) (fun ω => (e ω).1) = uniformPMF α := funext fun a => by
    rw [← sum_dist_pair_right _ _ (fun ω => (e ω).2) a]
    simp only [hd, sum_const, card_univ, nsmul_eq_mul, uniformPMF, hcard]
    field_simp
  have h₂ : dist (uniformPMF Ω) (fun ω => (e ω).2) = uniformPMF β := funext fun b => by
    rw [← sum_dist_pair_left _ (fun ω => (e ω).1) _ b]
    simp only [hd, sum_const, card_univ, nsmul_eq_mul, uniformPMF, hcard]
    field_simp
  refine ⟨(mutualInfo_eq_zero_iff hμ _ _).2 fun a b => ?_, ?_, ?_⟩
  · rw [hd, h₁, h₂, hcard]
    simp only [uniformPMF]
    field_simp
  · rw [entropyRV, h₁, entropy_uniformPMF]
  · rw [entropyRV, h₂, entropy_uniformPMF]

/-! ### Lemma 15.3, Corollary 15.4 and Theorem 15.5 -/

section Cone

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **Lemma 15.3.** If `h` and `h'` are entropic, so is `h + h'`: pair independent collections of
random variables realizing them, (15.37)–(15.38). -/
theorem add_mem_entropicRegion {h h' : EntropySpace ι} (hh : h ∈ entropicRegion ι)
    (hh' : h' ∈ entropicRegion ι) : h + h' ∈ entropicRegion ι := by
  obtain ⟨Ω₁, _, A₁, _, μ₁, X₁, hμ₁, rfl⟩ := hh
  obtain ⟨Ω₂, _, A₂, _, μ₂, X₂, hμ₂, rfl⟩ := hh'
  refine ⟨Ω₁ × Ω₂, inferInstance, fun i => A₁ i × A₂ i, inferInstance, prodDist μ₁ μ₂,
    fun i ω => (X₁ i ω.1, X₂ i ω.2), hμ₁.prodDist hμ₂, funext fun α => ?_⟩
  change H[blockRV (fun i (ω : Ω₁ × Ω₂) => (X₁ i ω.1, X₂ i ω.2)) α.1 ; prodDist μ₁ μ₂] =
    H[blockRV X₁ α.1 ; μ₁] + H[blockRV X₂ α.1 ; μ₂]
  rw [← entropyRV_prodDist_pair hμ₁ hμ₂]
  exact entropyRV_eq_of_injective _ (fun p (i : α.1) => (p.1 i, p.2 i))
    (fun p q e => Prod.ext (funext fun i => (Prod.mk.inj (congrFun e i)).1)
      (funext fun i => (Prod.mk.inj (congrFun e i)).2)) fun _ => rfl

/-- **Corollary 15.4.** If `h` is entropic, so is `k h` for every natural number `k`. -/
theorem nsmul_mem_entropicRegion {h : EntropySpace ι} (hh : h ∈ entropicRegion ι) (k : ℕ) :
    k • h ∈ entropicRegion ι := by
  induction k with
  | zero => rw [zero_smul]; exact zero_mem_entropicRegion
  | succ k ih => rw [succ_nsmul]; exact add_mem_entropicRegion ih hh

/-- Mixing a collection of random variables with a constant one by an independent coin of bias `δ`
gives the entropy function `h(δ) + δ h`, (15.41)–(15.45). -/
theorem exists_mem_entropicRegion_eq_binEntropy_add {h : EntropySpace ι}
    (hh : h ∈ entropicRegion ι) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    (fun _ => binEntropy δ) + δ • h ∈ entropicRegion ι := by
  classical
  obtain ⟨Ω₁, _, A₁, _, μ₁, X₁, hμ₁, rfl⟩ := hh
  set ν : Bool → ℝ := fun b => if b then δ else 1 - δ with hν
  have hνp : IsPMF ν := ⟨fun b => by cases b <;> simp [hν] <;> linarith, by simp [hν]⟩
  set X : ∀ i, Bool × Ω₁ → Option (A₁ i) := fun i ω => bif ω.1 then some (X₁ i ω.2) else none
  have hμ : IsPMF (prodDist ν μ₁) := hνp.prodDist hμ₁
  refine ⟨Bool × Ω₁, inferInstance, fun i => Option (A₁ i), inferInstance, prodDist ν μ₁, X, hμ,
    funext fun α => ?_⟩
  obtain ⟨i₀, hi₀⟩ := α.2
  change H[blockRV X α.1 ; prodDist ν μ₁] = binEntropy δ + δ * H[blockRV X₁ α.1 ; μ₁]
  set V := blockRV X α.1 with hV
  -- the coin is a function of `V`
  have hUV : H[Prod.fst | V ; prodDist ν μ₁] = 0 :=
    condEntropy_eq_zero_of_eq_comp hμ (fun v => (v ⟨i₀, hi₀⟩).isSome) fun ω => by
      rcases ω with ⟨b, ω⟩
      cases b <;> rfl
  have hVU : H[V | Prod.fst ; prodDist ν μ₁] = δ * H[blockRV X₁ α.1 ; μ₁] := by
    rw [condEntropy_fst_prodDist hμ₁, Fintype.sum_bool]
    have hc : (fun ω => V (false, ω)) = fun _ => (fun _ => none : ∀ i : α.1, Option (A₁ i)) := by
      funext ω i
      rfl
    have hf : H[fun ω => V (false, ω) ; μ₁] = 0 := by
      rw [hc]
      exact entropyRV_const hμ₁ _
    have ht : H[fun ω => V (true, ω) ; μ₁] = H[blockRV X₁ α.1 ; μ₁] :=
      entropyRV_eq_of_injective μ₁ (fun v (i : α.1) => some (v i))
        (fun v w e => funext fun i => Option.some_injective _ (congrFun e i)) fun _ => rfl
    rw [hf, ht]
    simp [hν]
  have hU : H[Prod.fst ; prodDist ν μ₁] = binEntropy δ := by
    rw [entropyRV, show dist (prodDist ν μ₁) Prod.fst = ν from funext fun b => by
      have := dist_prodDist_comp_fst ν hμ₁ (id : Bool → Bool) b
      rwa [dist_id] at this, entropy_bool hνp]
    simp [hν]
  have e₁ := condEntropy_eq_sub hμ V Prod.fst
  have e₂ := condEntropy_eq_sub hμ Prod.fst V
  rw [entropyRV_pair_comm] at e₂
  linarith

lemma tendsto_binEntropy_div (t : ℝ) :
    Tendsto (fun k : ℕ => binEntropy (t / (k + 1))) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => t / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
  have := (binEntropy_continuous.tendsto 0).comp h
  simpa [Function.comp_def] using this

/-- `t h` is in the closure of `Γ*ₙ` for an entropic `h` and `0 ≤ t ≤ 1`: mix `k h` with a
constant collection by a coin of bias `t / k`, (15.46)–(15.48). -/
lemma smul_mem_closure_of_mem {h : EntropySpace ι} (hh : h ∈ entropicRegion ι) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • h ∈ closure (entropicRegion ι) := by
  have hsmul : ∀ k : ℕ, (t / (k + 1)) • ((k + 1 : ℕ) • h) = t • h := fun k => by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    push_cast
    field_simp
  refine mem_closure_of_tendsto (b := (atTop : Filter ℕ))
    (f := fun k : ℕ => (fun _ => binEntropy (t / (k + 1))) + (t / (k + 1)) • ((k + 1 : ℕ) • h))
    ?_ (Eventually.of_forall fun k => ?_)
  · simp only [hsmul]
    have h2 : Tendsto (fun k : ℕ => (fun _ : {α : Finset ι // α.Nonempty} =>
        binEntropy (t / (k + 1)))) atTop (𝓝 0) :=
      tendsto_pi_nhds.2 fun _ => tendsto_binEntropy_div t
    simpa using h2.add_const (t • h)
  · refine exists_mem_entropicRegion_eq_binEntropy_add (nsmul_mem_entropicRegion hh (k + 1))
      (div_nonneg ht0 (by positivity)) ?_
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- The closure of `Γ*ₙ` is closed under addition. -/
theorem add_mem_closure_entropicRegion {h h' : EntropySpace ι}
    (hh : h ∈ closure (entropicRegion ι)) (hh' : h' ∈ closure (entropicRegion ι)) :
    h + h' ∈ closure (entropicRegion ι) :=
  map_mem_closure₂ continuous_add hh hh' fun _ ha _ hb => add_mem_entropicRegion ha hb

lemma smul_mem_closure_of_le_one {h : EntropySpace ι} (hh : h ∈ closure (entropicRegion ι))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • h ∈ closure (entropicRegion ι) := by
  rw [← closure_closure (s := entropicRegion ι)]
  exact map_mem_closure (continuous_const_smul t) hh fun _ ha => smul_mem_closure_of_mem ha ht0 ht1

/-- **Theorem 15.5**, the cone: the closure of `Γ*ₙ` is closed under multiplication by `t ≥ 0`. -/
theorem smul_mem_closure_entropicRegion {h : EntropySpace ι}
    (hh : h ∈ closure (entropicRegion ι)) {t : ℝ} (ht : 0 ≤ t) :
    t • h ∈ closure (entropicRegion ι) := by
  have hnat : ∀ n : ℕ, (n : ℝ) • h ∈ closure (entropicRegion ι) := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul]; exact subset_closure zero_mem_entropicRegion
    | succ n ih =>
      rw [Nat.cast_succ, add_smul, one_smul]
      exact add_mem_closure_entropicRegion ih hh
  have e : t = (⌊t⌋₊ : ℝ) + (t - ⌊t⌋₊) := by ring
  rw [e, add_smul]
  exact add_mem_closure_entropicRegion (hnat _) (smul_mem_closure_of_le_one hh
    (sub_nonneg.2 (Nat.floor_le ht)) (by linarith [Nat.lt_floor_add_one t]))

/-- **Theorem 15.5.** The closure of `Γ*ₙ` is a convex cone. -/
theorem convex_closure_entropicRegion : Convex ℝ (closure (entropicRegion ι)) :=
  fun _ hx _ hy _ _ ha hb _ => add_mem_closure_entropicRegion
    (smul_mem_closure_entropicRegion hx ha) (smul_mem_closure_entropicRegion hy hb)

/-- **(15.34)–(15.36)** An unconstrained inequality `b ⬝ h ≥ 0` always holds if and only if it
holds on the closure of `Γ*ₙ`. -/
theorem ineqAlwaysHolds_iff_closure_subset (b : EntropySpace ι) :
    IneqAlwaysHolds b Set.univ ↔ closure (entropicRegion ι) ⊆ {h | 0 ≤ infoExpr b h} := by
  have hc : IsClosed {h : EntropySpace ι | 0 ≤ infoExpr b h} :=
    isClosed_le continuous_const
      (continuous_finsetSum _ fun α _ => continuous_const.mul (continuous_apply α))
  constructor
  · exact fun H => closure_minimal (fun h hh => H h ⟨hh, Set.mem_univ h⟩) hc
  · exact fun H h hh => H (subset_closure hh.1)

end Cone

/-! ### Two and three random variables -/

/-- An I-Measure that is nonnegative on every atom of the sets of `ℱₙ` of the elemental forms. -/
lemma atom_nonneg_of_mem_shannonRegion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : NAtom ι → ℝ} (hh : atomsToEntropy u ∈ shannonRegion ι) (e : ElemForm ι) :
    0 ≤ ∑ a ∈ elemAtoms e, u a := by
  have := hh e
  rwa [Pi.zero_apply, elemMatrix_mulVec, elemValue_atomsToEntropy] at this

/-- **Theorem 15.1.** `Γ*₂ = Γ₂`: for two random variables, the values of `μ*` on the atoms are
the elemental forms, so `Ψ₂` is the nonnegative orthant, (15.4)–(15.7). -/
theorem entropicRegion_fin_two : entropicRegion (Fin 2) = shannonRegion (Fin 2) := by
  refine subset_antisymm entropicRegion_subset_shannonRegion fun h hh => ?_
  obtain ⟨u, rfl⟩ := exists_atomsToEntropy_eq h
  refine atomsToEntropy_mem_entropicRegion fun a => ?_
  obtain ⟨s, hs⟩ := a
  have hcases : ∀ s : Finset (Fin 2), s.Nonempty → s = {0} ∨ s = {1} ∨ s = {0, 1} := by decide
  rcases hcases s hs with rfl | rfl | rfl
  · simpa [elemAtoms] using atom_nonneg_of_mem_shannonRegion hh (.inl 0)
  · simpa [elemAtoms] using atom_nonneg_of_mem_shannonRegion hh (.inl 1)
  · have h₀ := atom_nonneg_of_mem_shannonRegion hh (.inr ⟨({0, 1}, ∅), by decide⟩)
    have he : ∀ hs' : ({0, 1} : Finset (Fin 2)).Nonempty,
        elemAtoms (.inr ⟨({0, 1}, ∅), by decide⟩ : ElemForm (Fin 2)) = {⟨{0, 1}, hs'⟩} := by
      decide
    rwa [he hs, sum_singleton] at h₀

/-! #### Theorem 15.2 -/

section Three

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] {μ : Ω → ℝ}

omit [Fintype α] in
lemma exists_of_dist_ne_zero {V : Ω → α} {v : α} (h : dist μ V v ≠ 0) :
    ∃ ω, V ω = v ∧ μ ω ≠ 0 := by
  classical
  by_contra hno
  push Not at hno
  exact h (sum_eq_zero fun ω _ => by by_cases hω : V ω = v <;> simp [hω, hno ω])

/-- If `Z` is a function of `(X, Y)`, then `p(x, y) = p(x, y, z)` at every outcome of positive
probability. -/
lemma dist_pair_eq_triple (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (h : H[Z | pair X Y ; μ] = 0) {ω : Ω} (hω : μ ω ≠ 0) :
    dist μ (pair X Y) (X ω, Y ω) = dist μ (fun ω' => (X ω', Y ω', Z ω')) (X ω, Y ω, Z ω) := by
  classical
  obtain ⟨g, hg⟩ := (condEntropy_eq_zero_iff hμ Z (pair X Y)).1 h
  refine sum_congr rfl fun ω' _ => ?_
  by_cases hω' : μ ω' = 0
  · simp [hω']
  · have hZ : X ω' = X ω → Y ω' = Y ω → Z ω' = Z ω := fun h₁ h₂ => by
      rw [hg ω' hω', hg ω hω]
      simp [pair, h₁, h₂]
    by_cases h₁ : X ω' = X ω
    · by_cases h₂ : Y ω' = Y ω
      · simp [pair, h₁, h₂, hZ h₁ h₂]
      · simp [pair, h₂]
    · simp [pair, h₁]

/-- Three pairwise independent random variables, each a function of the other two: at an outcome
of positive probability the three have the same probability, (15.18)–(15.21). -/
lemma dist_eq_of_three (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hXY : IndepRV μ X Y) (hXZ : IndepRV μ X Z) (hYZ : IndepRV μ Y Z)
    (hZ : H[Z | pair X Y ; μ] = 0) (hY : H[Y | pair X Z ; μ] = 0) (hX : H[X | pair Y Z ; μ] = 0)
    {ω : Ω} (hω : μ ω ≠ 0) :
    dist μ X (X ω) = dist μ Y (Y ω) ∧ dist μ Y (Y ω) = dist μ Z (Z ω) := by
  classical
  set T := dist μ (fun ω' => (X ω', Y ω', Z ω')) (X ω, Y ω, Z ω) with hT
  have h₁ : dist μ X (X ω) * dist μ Y (Y ω) = T := by
    rw [← hXY, dist_pair_eq_triple hμ hZ hω]
  have h₂ : dist μ X (X ω) * dist μ Z (Z ω) = T := by
    rw [← hXZ, dist_pair_eq_triple hμ hY hω, hT]
    exact dist_congr_of_iff μ fun ω' => by simp only [Prod.mk.injEq]; tauto
  have h₃ : dist μ Y (Y ω) * dist μ Z (Z ω) = T := by
    rw [← hYZ, dist_pair_eq_triple hμ hX hω, hT]
    exact dist_congr_of_iff μ fun ω' => by simp only [Prod.mk.injEq]; tauto
  have pX := dist_pos hμ X ((hμ.nonneg _).lt_of_ne' hω)
  have pY := dist_pos hμ Y ((hμ.nonneg _).lt_of_ne' hω)
  have pZ := dist_pos hμ Z ((hμ.nonneg _).lt_of_ne' hω)
  constructor
  · exact mul_right_cancel₀ pZ.ne' (h₂.trans h₃.symm)
  · exact mul_left_cancel₀ pX.ne' (h₁.trans h₂.symm)

/-- Under the hypotheses of `dist_eq_of_three`, `Y` is uniform on its support, (15.22)–(15.27). -/
lemma dist_const_of_three (hμ : IsPMF μ) {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hXY : IndepRV μ X Y) (hXZ : IndepRV μ X Z) (hYZ : IndepRV μ Y Z)
    (hZ : H[Z | pair X Y ; μ] = 0) (hY : H[Y | pair X Z ; μ] = 0) (hX : H[X | pair Y Z ; μ] = 0)
    {ω ω' : Ω} (hω : μ ω ≠ 0) (hω' : μ ω' ≠ 0) : dist μ Y (Y ω') = dist μ Y (Y ω) := by
  have hpos : dist μ (pair Y Z) (Y ω', Z ω) ≠ 0 := by
    rw [hYZ]
    exact (mul_pos (dist_pos hμ Y ((hμ.nonneg _).lt_of_ne' hω'))
      (dist_pos hμ Z ((hμ.nonneg _).lt_of_ne' hω))).ne'
  obtain ⟨ω'', he, hω''⟩ := exists_of_dist_ne_zero hpos
  simp only [pair, Prod.mk.injEq] at he
  have h₁ := (dist_eq_of_three hμ hXY hXZ hYZ hZ hY hX hω'').2
  rw [he.1, he.2] at h₁
  rw [h₁, (dist_eq_of_three hμ hXY hXZ hYZ hZ hY hX hω).2]

omit [Fintype α] [Fintype γ] in
/-- A random variable uniform on its support has entropy `log M`, for the size `M` of the
support. -/
lemma exists_entropyRV_eq_log (hμ : IsPMF μ) {Y : Ω → β}
    (h : ∀ ω ω', μ ω ≠ 0 → μ ω' ≠ 0 → dist μ Y (Y ω') = dist μ Y (Y ω)) :
    ∃ M : ℕ, 0 < M ∧ H[Y ; μ] = log M := by
  classical
  obtain ⟨ω₀, hω₀⟩ : ∃ ω, μ ω ≠ 0 := by
    by_contra hno
    push Not at hno
    have := hμ.sum_eq_one
    simp [hno] at this
  set c := dist μ Y (Y ω₀) with hc
  have hc0 : 0 < c := dist_pos hμ Y ((hμ.nonneg _).lt_of_ne' hω₀)
  have hp : ∀ y, dist μ Y y ≠ 0 → dist μ Y y = c := fun y hy => by
    obtain ⟨ω, rfl, hω⟩ := exists_of_dist_ne_zero hy
    exact h ω₀ ω hω₀ hω
  set S := univ.filter fun y => dist μ Y y ≠ 0 with hS
  have hsum : (#S : ℝ) * c = 1 := by
    have := (hμ.dist Y).sum_eq_one
    rw [← sum_filter_ne_zero, ← hS] at this
    rw [← this, sum_congr rfl fun y hy => hp y (mem_filter.1 hy).2, sum_const, nsmul_eq_mul]
  have hSpos : 0 < #S := by
    by_contra h0
    rw [Nat.eq_zero_of_not_pos h0, Nat.cast_zero, zero_mul] at hsum
    exact zero_ne_one hsum
  refine ⟨#S, hSpos, ?_⟩
  rw [entropyRV, entropy_eq_sum_negMulLog, ← sum_filter_ne_zero]
  have e : (univ.filter fun y => negMulLog (dist μ Y y) ≠ 0) ⊆ S := fun y hy => by
    rw [mem_filter] at hy ⊢
    exact ⟨mem_univ y, fun h0 => hy.2 (by rw [h0, negMulLog_zero])⟩
  rw [sum_subset e (fun y hy hy' => by simpa using hy'), sum_congr rfl fun y hy =>
    by rw [hp y (mem_filter.1 hy).2], sum_const, nsmul_eq_mul, negMulLog]
  have hc' : c = (#S : ℝ)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)
  rw [hc', log_inv]
  field_simp

end Three

/-- The rank function `min(|α|, r)` of the uniform matroid, as a vector of the entropy space. -/
def rankVector (ι : Type*) (r : ℕ) : EntropySpace ι := fun α => (min #α.1 r : ℕ)

lemma extend_rankVector {ι : Type*} (r : ℕ) :
    (rankVector ι r).extend = fun s => ((min #s r : ℕ) : ℝ) := by
  funext s
  rw [EntropySpace.extend]
  split_ifs with hs
  · rfl
  · simp [not_nonempty_iff_eq_empty.1 hs]

lemma isPolymatroid_min_card {ι : Type*} [DecidableEq ι] (r : ℕ) :
    IsPolymatroid fun s : Finset ι => ((min #s r : ℕ) : ℝ) := by
  refine ⟨by simp, fun s t hst => ?_, fun s t => ?_⟩
  · exact_mod_cast min_le_min_right r (card_le_card hst)
  · have h₁ := card_union_add_card_inter s t
    have h₂ := card_le_card (inter_subset_left (s₁ := s) (s₂ := t))
    have h₃ := card_le_card (inter_subset_right (s₁ := s) (s₂ := t))
    have h₄ := card_le_card (subset_union_left (s₁ := s) (s₂ := t))
    have h₅ := card_le_card (subset_union_right (s₁ := s) (s₂ := t))
    exact_mod_cast (show min #(s ∪ t) r + min #(s ∩ t) r ≤ min #s r + min #t r by omega)

lemma IsPolymatroid.const_smul {ι : Type*} [DecidableEq ι] {f : Finset ι → ℝ}
    (hf : IsPolymatroid f) {c : ℝ} (hc : 0 ≤ c) : IsPolymatroid (c • f) :=
  ⟨by simp [hf.empty], fun s t hst => by
    simpa using mul_le_mul_of_nonneg_left (hf.mono hst) hc, fun s t => by
    have := mul_le_mul_of_nonneg_left (hf.submod s t) hc
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith⟩

lemma smul_rankVector_mem_shannonRegion {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) {a : ℝ}
    (ha : 0 ≤ a) : a • rankVector ι r ∈ shannonRegion ι := by
  rw [mem_shannonRegion_iff, EntropySpace.extend_smul, extend_rankVector]
  exact (isPolymatroid_min_card r).const_smul ha

/-- **Theorem 15.2**, the main step: if `(a, a, a, 2a, 2a, 2a, 2a)` is entropic, then each variable
is uniform on its support, so `a = log M` for a positive integer `M`, (15.16)–(15.31). -/
theorem exists_eq_log_of_smul_rankTwo_mem {a : ℝ}
    (h : a • rankVector (Fin 3) 2 ∈ entropicRegion (Fin 3)) : ∃ M : ℕ, 0 < M ∧ a = log M := by
  obtain ⟨Ω, _, A, _, μ, X, hμ, hX⟩ := h
  set f := blockEntropy μ X with hfdef
  have hf : ∀ s : Finset (Fin 3), f s = a * (min #s 2 : ℕ) := fun s => by
    have := congrFun (congrArg EntropySpace.extend hX) s
    rw [extend_entropyVector hμ, EntropySpace.extend_smul, extend_rankVector] at this
    exact this
  -- the pairwise independencies
  have hind : ∀ i j : Fin 3, i ≠ j → IndepRV μ (X i) (X j) := fun i j hij => by
    rw [← mutualInfo_eq_zero_iff hμ, ← iMeasure_inter hμ (rvEquiv_blockRV_singleton X i)
      (rvEquiv_blockRV_singleton X j), ← sdiff_empty (s := tilde {i} ∩ tilde {j}),
      ← tilde_empty, ← condInfo_blockEntropy_eq_iMeasure hμ, condInfo]
    simp only [empty_union, ← hfdef, hf, card_empty, card_singleton]
    rw [singleton_union, card_pair hij]
    norm_num
    ring
  -- each variable is a function of the other two
  have hfun : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      H[X k | pair (X i) (X j) ; μ] = 0 := fun i j k hij hki hkj => by
    have hW : RVEquiv (pair (X i) (X j)) (blockRV X {i, j}) := by
      have := ((rvEquiv_blockRV_singleton X i).pair (rvEquiv_blockRV_singleton X j)).trans
        (rvEquiv_blockRV_union X {i} {j})
      rwa [singleton_union] at this
    rw [← iMeasure_sdiff hμ (rvEquiv_blockRV_singleton X k) hW, iMeasure_tilde_sdiff hμ,
      ← hfdef, hf, hf, card_pair hij]
    have : #({i, j} ∪ {k} : Finset (Fin 3)) = 3 := by
      rw [union_singleton, card_insert_of_notMem (by simp [hki, hkj]), card_pair hij]
    rw [this]
    norm_num
  obtain ⟨M, hM, he⟩ := exists_entropyRV_eq_log hμ fun ω ω' hω hω' =>
    dist_const_of_three hμ (hind 0 1 (by decide)) (hind 0 2 (by decide)) (hind 1 2 (by decide))
      (hfun 0 1 2 (by decide) (by decide) (by decide))
      (hfun 0 2 1 (by decide) (by decide) (by decide))
      (hfun 1 2 0 (by decide) (by decide) (by decide)) hω hω'
  refine ⟨M, hM, ?_⟩
  rw [← he, (rvEquiv_blockRV_singleton X 1).entropy_eq hμ]
  change a = f {1}
  rw [hf, card_singleton]
  norm_num

/-- **Theorem 15.2.** `Γ*₃ ≠ Γ₃`: `(a, a, a, 2a, 2a, 2a, 2a)` with `a = log (3/2)` satisfies the
elemental inequalities but is not entropic. -/
theorem entropicRegion_fin_three_ne : entropicRegion (Fin 3) ≠ shannonRegion (Fin 3) := by
  intro h
  have hmem := smul_rankVector_mem_shannonRegion (ι := Fin 3) 2
    (log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2))
  rw [← h] at hmem
  obtain ⟨M, hM, he⟩ := exists_eq_log_of_smul_rankTwo_mem hmem
  have h32 : (3 / 2 : ℝ) = M :=
    log_injOn_pos (Set.mem_Ioi.2 (by norm_num)) (Set.mem_Ioi.2 (by exact_mod_cast hM)) he
  have : (2 * M : ℝ) = 3 := by rw [← h32]; norm_num
  have : 2 * M = 3 := by exact_mod_cast this
  omega

/-! #### Theorem 15.6 -/

/-- The random variables `X₁`, `X₂` independent and uniform on `{0, 1}` and `X₃ = X₁ + X₂ mod 2`
of Example 3.10. -/
def xorRV : Fin 3 → Bool × Bool → Bool := ![fun ω => ω.1, fun ω => ω.2, fun ω => xor ω.1 ω.2]

/-- The entropy function of `xorRV` is `log 2 · min(|α|, 2)`. -/
theorem smul_rankVector_mem_entropicRegion :
    log 2 • rankVector (Fin 3) 2 ∈ entropicRegion (Fin 3) := by
  have hμ : IsPMF (uniformPMF (Bool × Bool)) := uniformPMF_isPMF
  refine ⟨Bool × Bool, inferInstance, fun _ => Bool, inferInstance, uniformPMF (Bool × Bool),
    xorRV, hμ, funext fun α => ?_⟩
  obtain ⟨s, hs⟩ := α
  change H[blockRV xorRV s ; uniformPMF (Bool × Bool)] = log 2 * ((min #s 2 : ℕ) : ℝ)
  by_cases h2 : 2 ≤ #s
  · -- the block determines the outcome
    have hinj : ∀ s : Finset (Fin 3), 2 ≤ #s → Function.Injective (blockRV xorRV s) := by
      decide
    have e := entropyRV_eq_of_injective (uniformPMF (Bool × Bool)) (blockRV xorRV s) (hinj s h2)
      (X := id) (Y := blockRV xorRV s) fun _ => rfl
    rw [e, entropyRV, dist_id, entropy_uniformPMF]
    simp only [Fintype.card_prod, Fintype.card_bool, min_eq_right h2]
    rw [show ((2 * 2 : ℕ) : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
    ring
  · have h1 : #s = 1 := by
      have := card_pos.2 hs
      omega
    obtain ⟨i, rfl⟩ := card_eq_one.1 h1
    rw [← (rvEquiv_blockRV_singleton xorRV i).entropy_eq hμ, entropyRV,
      entropy_bool (hμ.dist _), card_singleton]
    have hd : dist (uniformPMF (Bool × Bool)) (xorRV i) true = 2⁻¹ := by
      fin_cases i <;>
        simp [dist, uniformPMF, xorRV, Fintype.sum_prod_type] <;> norm_num
    rw [hd, binEntropy_two_inv]
    norm_num

lemma atomsToEntropy_add {ι : Type*} [Fintype ι] [DecidableEq ι] (u v : NAtom ι → ℝ) :
    atomsToEntropy (u + v) = atomsToEntropy u + atomsToEntropy v := by
  funext α
  simp [atomsToEntropy, sum_add_distrib]

lemma atomsToEntropy_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) (u : NAtom ι → ℝ) :
    atomsToEntropy (c • u) = c • atomsToEntropy u := by
  funext α
  simp [atomsToEntropy, mul_sum]

/-- The values `(0, 0, 0, 1, 1, 1, -1)` of `μ*` on the atoms of `ℱ₃`, (15.53). -/
def xorAtoms (a : NAtom (Fin 3)) : ℤ := if #a.1 = 2 then 1 else if #a.1 = 3 then -1 else 0

lemma atomsToEntropy_xorAtoms :
    atomsToEntropy (fun a => (xorAtoms a : ℝ)) = rankVector (Fin 3) 2 := by
  have h : ∀ s : Finset (Fin 3), s.Nonempty → ∑ a ∈ tilde s, xorAtoms a = (min #s 2 : ℕ) := by
    decide
  funext α
  have := h α.1 α.2
  simp only [atomsToEntropy, rankVector]
  exact_mod_cast this

/-- **Theorem 15.6.** The closure of `Γ*₃` is `Γ₃`: a vector of `Γ₃` is the sum of a vector with
a nonnegative I-Measure and a multiple of the entropy function of `xorRV`, (15.54)–(15.61). -/
theorem closure_entropicRegion_fin_three :
    closure (entropicRegion (Fin 3)) = shannonRegion (Fin 3) := by
  refine subset_antisymm (closure_minimal entropicRegion_subset_shannonRegion
    (isClosed_le continuous_const (continuous_const.matrix_mulVec continuous_id)))
    fun h hh => ?_
  obtain ⟨u, rfl⟩ := exists_atomsToEntropy_eq h
  have hn := atom_nonneg_of_mem_shannonRegion hh
  set top : NAtom (Fin 3) := ⟨univ, univ_nonempty⟩ with htop
  -- (15.15): the elemental inequalities in terms of the atoms
  have key₁ : ∀ a : NAtom (Fin 3), #a.1 = 1 → ∃ e : ElemForm (Fin 3), elemAtoms e = {a} := by
    decide
  have key₂ : ∀ a : NAtom (Fin 3), #a.1 = 2 → ∃ e : ElemForm (Fin 3), elemAtoms e = {a} := by
    decide
  have key₃ : ∀ a : NAtom (Fin 3), #a.1 = 2 →
      ∃ e : ElemForm (Fin 3), elemAtoms e = {a, ⟨univ, univ_nonempty⟩} := by
    decide
  have key₄ : ∀ a : NAtom (Fin 3), #a.1 = 1 ∨ #a.1 = 2 ∨ a = ⟨univ, univ_nonempty⟩ := by decide
  have hsing : ∀ a : NAtom (Fin 3), #a.1 = 1 → 0 ≤ u a := fun a ha => by
    obtain ⟨e, he⟩ := key₁ a ha
    simpa [he] using hn e
  have hpair : ∀ a : NAtom (Fin 3), #a.1 = 2 → 0 ≤ u a := fun a ha => by
    obtain ⟨e, he⟩ := key₂ a ha
    simpa [he] using hn e
  have hpair' : ∀ a : NAtom (Fin 3), #a.1 = 2 → 0 ≤ u a + u top := fun a ha => by
    obtain ⟨e, he⟩ := key₃ a ha
    have hne : a ≠ top := fun h' => by
      rw [h', htop, card_univ, Fintype.card_fin] at ha
      omega
    have := hn e
    rwa [he, sum_pair hne] at this
  by_cases hc : 0 ≤ u top
  · refine subset_closure (atomsToEntropy_mem_entropicRegion fun a => ?_)
    rcases key₄ a with ha | ha | rfl
    exacts [hsing a ha, hpair a ha, hc]
  · -- `u = w + (-u₇) t`, (15.55)–(15.57)
    set v : NAtom (Fin 3) → ℝ := fun a => (xorAtoms a : ℝ) with hv
    have hw : ∀ a, 0 ≤ (u + u top • v) a := fun a => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, xorAtoms]
      rcases key₄ a with ha | ha | rfl
      · simp [ha, hsing a ha]
      · simp [ha, hpair' a ha]
      · simp [htop]
    have he : atomsToEntropy u =
        atomsToEntropy (u + u top • v) + (-u top) • rankVector (Fin 3) 2 := by
      rw [atomsToEntropy_add, atomsToEntropy_smul, hv, atomsToEntropy_xorAtoms]
      module
    rw [he]
    refine add_mem_closure_entropicRegion (subset_closure (atomsToEntropy_mem_entropicRegion hw)) ?_
    have hl : (0 : ℝ) < log 2 := log_pos (by norm_num)
    have e : (-u top) • rankVector (Fin 3) 2 =
        (-u top / log 2) • (log 2 • rankVector (Fin 3) 2) := by
      rw [smul_smul, div_mul_cancel₀ _ hl.ne']
    rw [e]
    exact smul_mem_closure_entropicRegion (subset_closure smul_rankVector_mem_entropicRegion)
      (div_nonneg (by linarith) hl.le)

end InfoTheory
