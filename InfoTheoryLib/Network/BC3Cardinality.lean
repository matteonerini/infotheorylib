/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCCardinality

/-!
# The cardinality bound of the 3-receiver degraded broadcast channel

The capacity region of the 3-receiver degraded DM-BC is the set of `(R₁, R₂, R₃)` with
`R₁ ≤ I(X; Y₁ | V)`, `R₂ ≤ I(V; Y₂ | U)`, `R₃ ≤ I(U; Y₃)` for some `p(u) p(v | u) p(x | v)`. As in
Appendix C of El Gamal and Kim, it suffices to take `|𝒰| ≤ |𝒳| + 2` and
`|𝒱| ≤ (|𝒳| + 1) (|𝒳| + 2)`.

The three informations only depend on the marginals `p(yⱼ | x)` of the channel, so we state them for
one channel `T : α → β` at a time. The bound does not use degradedness.

## Main definitions

* `triLaw r c T`: the law of `((U, V), X), Y` with `p(u, v) p(x | v) T(y | x)`.
* `triInfoXV`, `triInfoVU`, `triInfoU`: `I(X; Y | V)`, `I(V; Y | U)` and `I(U; Y)`.

## Main statements

* `exists_bc3_card`: **the bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Channel

variable {Ξ δ β : Type*} [Fintype Ξ] [Fintype β]

/-- If given `G(ξ) = d` the output of `T` has law `K d`, then `H(Y | G) = ∑_d p(d) H(K d)`. -/
lemma condEntropy_comp_of_channel [Fintype δ] {ρ : Ξ → ℝ} {T : Ξ → β → ℝ} (hT : IsChannel T)
    (G : Ξ → δ) (K : δ → β → ℝ)
    (h : ∀ d y, dist (fun ξ => ρ ξ * T ξ y) G d = dist ρ G d * K d y) :
    H[Prod.snd | fun ω : Ξ × β => G ω.1 ; jointOf ρ T] = ∑ d, dist ρ G d * entropy (K d) := by
  classical
  have dZ : dist (jointOf ρ T) (fun ω : Ξ × β => G ω.1) = dist ρ G := by
    have e : (fun ω : Ξ × β => G ω.1) = G ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, dist_jointOf_fst hT]
  have hpair : ∀ d y, dist (jointOf ρ T) (pair (fun ω : Ξ × β => G ω.1) Prod.snd) (d, y) =
      dist (jointOf ρ T) (fun ω : Ξ × β => G ω.1) d * K d y := fun d y => by
    rw [dZ, ← h d y]
    simp only [dist, jointOf, pair_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and,
      sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  have e := condEntropy_of_channel (μ := jointOf ρ T) (Z := fun ω : Ξ × β => G ω.1)
    (Y := Prod.snd) (W := K) id hpair
  rw [e, Function.id_comp, dZ]

end Channel

variable {𝒰 𝒱 α β : Type*} [Fintype 𝒰] [Fintype 𝒱] [Fintype α] [Fintype β]

/-- The law `p(u, v) p(x | v) T(y | x)` of `(((U, V), X), Y)`, with `U → V → X → Y`. -/
def bc3Law (r : 𝒰 × 𝒱 → ℝ) (c : 𝒱 → α → ℝ) (T : α → β → ℝ) : ((𝒰 × 𝒱) × α) × β → ℝ :=
  jointOf (jointOf r fun z => c z.2) fun z => T z.2

/-- `I(X; Y | V)`. -/
def bc3InfoXV (r : 𝒰 × 𝒱 → ℝ) (c : 𝒱 → α → ℝ) (T : α → β → ℝ) : ℝ :=
  I[fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.2 : Prod.snd | fun ω => ω.1.1.2 ; bc3Law r c T]

/-- `I(V; Y | U)`. -/
def bc3InfoVU (r : 𝒰 × 𝒱 → ℝ) (c : 𝒱 → α → ℝ) (T : α → β → ℝ) : ℝ :=
  I[fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.1.2 : Prod.snd | fun ω => ω.1.1.1 ; bc3Law r c T]

/-- `I(U; Y)`. -/
def bc3InfoU (r : 𝒰 × 𝒱 → ℝ) (c : 𝒱 → α → ℝ) (T : α → β → ℝ) : ℝ :=
  I[fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.1.1 : Prod.snd ; bc3Law r c T]

section Marginals

variable (f : (𝒰 × 𝒱) × α → ℝ)

lemma dist_tree_U (u : 𝒰) : dist f (fun ξ => ξ.1.1) u = ∑ v, ∑ x, f ((u, v), x) := by
  classical
  simp only [dist, Fintype.sum_prod_type]
  rw [sum_eq_single u (fun u' _ hu => by simp [hu]) (by simp)]
  simp

lemma dist_tree_V (v : 𝒱) : dist f (fun ξ => ξ.1.2) v = ∑ u, ∑ x, f ((u, v), x) := by
  classical
  simp only [dist, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_eq_single v (fun v' _ hv => by simp [hv]) (by simp)]
  simp

lemma dist_tree_VU (v : 𝒱) (u : 𝒰) :
    dist f (fun ξ => (ξ.1.2, ξ.1.1)) (v, u) = ∑ x, f ((u, v), x) := by
  classical
  simp only [dist, Fintype.sum_prod_type, Prod.mk.injEq]
  rw [sum_eq_single u (fun u' _ hu => by simp [hu]) (by simp),
    sum_eq_single v (fun v' _ hv => by simp [hv]) (by simp)]
  simp

lemma dist_tree_XV (x : α) (v : 𝒱) :
    dist f (fun ξ => (ξ.2, ξ.1.2)) (x, v) = ∑ u, f ((u, v), x) := by
  classical
  simp only [dist, Fintype.sum_prod_type, Prod.mk.injEq]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_eq_single v (fun v' _ hv => by simp [hv]) (by simp),
    sum_eq_single x (fun x' _ hx => by simp [hx]) (by simp)]
  simp

end Marginals

variable {a : 𝒰 → ℝ} {b : 𝒰 → 𝒱 → ℝ} {c : 𝒱 → α → ℝ} {T : α → β → ℝ}

/-- The first level of the tree, as a law. -/
lemma tree_isPMF (ha : IsPMF a) (hb : IsChannel b) :
    IsPMF fun z : 𝒰 × 𝒱 => a z.1 * b z.1 z.2 := by
  refine ⟨fun z => mul_nonneg (ha.nonneg _) ((hb _).nonneg _), ?_⟩
  simp only [Fintype.sum_prod_type, ← mul_sum, (hb _).sum_eq_one, mul_one, ha.sum_eq_one]

lemma bc3Law_isPMF {r : 𝒰 × 𝒱 → ℝ} (hr : IsPMF r) (hc : IsChannel c) (hT : IsChannel T) :
    IsPMF (bc3Law r c T) :=
  jointOf_isPMF (jointOf_isPMF hr fun z => hc z.2) fun z => hT z.2

/-- The tree law of `((U, V), X)`. -/
private abbrev treeρ (a : 𝒰 → ℝ) (b : 𝒰 → 𝒱 → ℝ) (c : 𝒱 → α → ℝ) : (𝒰 × 𝒱) × α → ℝ :=
  jointOf (fun z => a z.1 * b z.1 z.2) fun z => c z.2

/-- `H(Y | U) = ∑_u p(u) H(Y | U = u)`. -/
lemma condEntropy_tree_U (hb : IsChannel b) (hc : IsChannel c) (hT : IsChannel T) :
    H[Prod.snd | fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.1.1 ; bc3Law (fun z => a z.1 * b z.1 z.2) c T] =
      ∑ u, a u * entropy (outDist (outDist (b u) c) T) := by
  have hmass : ∀ u, dist (treeρ a b c) (fun ξ => ξ.1.1) u = a u := fun u => by
    rw [dist_tree_U]
    simp only [treeρ, jointOf, ← mul_sum, (hc _).sum_eq_one, mul_one, (hb u).sum_eq_one]
  have h := condEntropy_comp_of_channel (ρ := treeρ a b c) (T := fun ξ => T ξ.2)
    (fun ξ => hT ξ.2) (fun ξ => ξ.1.1) (fun u => outDist (outDist (b u) c) T) (fun u y => by
      rw [hmass, dist_tree_U]
      simp only [treeρ, jointOf, outDist, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun x _ => sum_congr rfl fun v _ => by ring)
  simp only [hmass] at h
  exact h

/-- `H(Y | V, U) = ∑_u p(u) ∑_v p(v | u) H(Y | V = v)`. -/
lemma condEntropy_tree_VU (hc : IsChannel c) (hT : IsChannel T) :
    H[Prod.snd | pair (fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.1.2) (fun ω => ω.1.1.1) ;
      bc3Law (fun z => a z.1 * b z.1 z.2) c T] =
      ∑ u, a u * ∑ v, b u v * entropy (outDist (c v) T) := by
  have hmass : ∀ v u, dist (treeρ a b c) (fun ξ => (ξ.1.2, ξ.1.1)) (v, u) = a u * b u v :=
    fun v u => by
    rw [dist_tree_VU]
    simp only [treeρ, jointOf, ← mul_sum, (hc _).sum_eq_one, mul_one]
  have h := condEntropy_comp_of_channel (ρ := treeρ a b c) (T := fun ξ => T ξ.2)
    (fun ξ => hT ξ.2) (fun ξ => (ξ.1.2, ξ.1.1)) (fun d => outDist (c d.1) T) (fun d y => by
      obtain ⟨v, u⟩ := d
      rw [hmass, dist_tree_VU]
      simp only [treeρ, jointOf, outDist, mul_sum]
      exact sum_congr rfl fun x _ => by ring)
  have e : H[Prod.snd | pair (fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.1.2) (fun ω => ω.1.1.1) ;
      bc3Law (fun z => a z.1 * b z.1 z.2) c T] = _ := h
  rw [e, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun v _ => by rw [hmass]; ring

/-- `H(Y | V) = ∑_u p(u) ∑_v p(v | u) H(Y | V = v)`. -/
lemma condEntropy_tree_V (hc : IsChannel c) (hT : IsChannel T) :
    H[Prod.snd | fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.1.2 ; bc3Law (fun z => a z.1 * b z.1 z.2) c T] =
      ∑ u, a u * ∑ v, b u v * entropy (outDist (c v) T) := by
  have hmass : ∀ v, dist (treeρ a b c) (fun ξ => ξ.1.2) v = ∑ u, a u * b u v := fun v => by
    rw [dist_tree_V]
    simp only [treeρ, jointOf, ← mul_sum, (hc _).sum_eq_one, mul_one]
  have h := condEntropy_comp_of_channel (ρ := treeρ a b c) (T := fun ξ => T ξ.2)
    (fun ξ => hT ξ.2) (fun ξ => ξ.1.2) (fun v => outDist (c v) T) (fun v y => by
      rw [hmass, dist_tree_V]
      simp only [treeρ, jointOf, outDist, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun x _ => sum_congr rfl fun u _ => by ring)
  have e : H[Prod.snd | fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.1.2 ;
      bc3Law (fun z => a z.1 * b z.1 z.2) c T] = _ := h
  rw [e]
  simp only [hmass, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring

/-- `H(Y | X, V) = ∑_u p(u) ∑_v p(v | u) ∑_x p(x | v) H(Y | X = x)`. -/
lemma condEntropy_tree_XV (hT : IsChannel T) :
    H[Prod.snd | pair (fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.2) (fun ω => ω.1.1.2) ;
      bc3Law (fun z => a z.1 * b z.1 z.2) c T] =
      ∑ u, a u * ∑ v, b u v * ∑ x, c v x * entropy (T x) := by
  have hmass : ∀ x v, dist (treeρ a b c) (fun ξ => (ξ.2, ξ.1.2)) (x, v) =
      ∑ u, a u * b u v * c v x := fun x v => dist_tree_XV _ x v
  have h := condEntropy_comp_of_channel (ρ := treeρ a b c) (T := fun ξ => T ξ.2)
    (fun ξ => hT ξ.2) (fun ξ => (ξ.2, ξ.1.2)) (fun d => T d.1) (fun d y => by
      obtain ⟨x, v⟩ := d
      rw [hmass, dist_tree_XV]
      simp only [treeρ, jointOf, sum_mul])
  have e : H[Prod.snd | pair (fun ω : ((𝒰 × 𝒱) × α) × β => ω.1.2) (fun ω => ω.1.1.2) ;
      bc3Law (fun z => a z.1 * b z.1 z.2) c T] = _ := h
  rw [e, Fintype.sum_prod_type]
  simp only [hmass, mul_sum, sum_mul]
  rw [sum_comm]
  refine (sum_congr rfl fun v _ => sum_comm).trans ?_
  rw [sum_comm]
  exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => sum_congr rfl fun x _ => by ring

/-- `I(X; Y | V) = ∑_u p(u) ∑_v p(v | u) I(X; Y | V = v)`. -/
theorem bc3InfoXV_tree (ha : IsPMF a) (hb : IsChannel b) (hc : IsChannel c) (hT : IsChannel T) :
    bc3InfoXV (fun z => a z.1 * b z.1 z.2) c T = ∑ u, a u * ∑ v, b u v * mutualInfoOf (c v) T := by
  have hμ := bc3Law_isPMF (tree_isPMF ha hb) hc hT
  rw [bc3InfoXV, condMutualInfo_comm hμ, condMutualInfo, condEntropy_tree_V hc hT,
    condEntropy_tree_XV hT, ← sum_sub_distrib]
  refine sum_congr rfl fun u _ => ?_
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun v _ => ?_
  rw [mutualInfoOf_eq (hc v) hT, mul_sub]

/-- `I(V; Y | U) = ∑_u p(u) (H(Y | U = u) - ∑_v p(v | u) H(Y | V = v))`. -/
theorem bc3InfoVU_tree (ha : IsPMF a) (hb : IsChannel b) (hc : IsChannel c) (hT : IsChannel T) :
    bc3InfoVU (fun z => a z.1 * b z.1 z.2) c T =
      ∑ u, a u * (entropy (outDist (outDist (b u) c) T) -
        ∑ v, b u v * entropy (outDist (c v) T)) := by
  have hμ := bc3Law_isPMF (tree_isPMF ha hb) hc hT
  rw [bc3InfoVU, condMutualInfo_comm hμ, condMutualInfo, condEntropy_tree_U hb hc hT,
    condEntropy_tree_VU hc hT, ← sum_sub_distrib]
  exact sum_congr rfl fun u _ => (mul_sub _ _ _).symm

/-- `I(U; Y) = H(Y) - ∑_u p(u) H(Y | U = u)`. -/
theorem bc3InfoU_tree (ha : IsPMF a) (hb : IsChannel b) (hc : IsChannel c) (hT : IsChannel T) :
    bc3InfoU (fun z => a z.1 * b z.1 z.2) c T =
      entropy (outDist (∑ u, a u • outDist (b u) c) T) -
        ∑ u, a u * entropy (outDist (outDist (b u) c) T) := by
  have hμ := bc3Law_isPMF (tree_isPMF ha hb) hc hT
  rw [bc3InfoU, mutualInfo_eq_entropy_sub_condEntropy' hμ, condEntropy_tree_U hb hc hT, entropyRV]
  congr 2
  funext y
  rw [bc3Law, dist_jointOf_snd]
  simp only [outDist, jointOf, Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_sum, sum_mul]
  refine (sum_congr rfl fun u _ => sum_comm).trans ?_
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring

/-! ### The bound -/

/-- The entropy of the output of a mixture is continuous in the mixture. -/
private lemma continuous_outDist_entropy (c : 𝒱 → α → ℝ) (T : α → β → ℝ) :
    Continuous fun t : 𝒱 → ℝ => entropy (outDist (outDist t c) T) :=
  (continuous_entropy_outDist T).comp (continuous_pi fun x => by simp only [outDist]; fun_prop)

/-- **The cardinality bound of the 3-receiver DM-BC on pages C-5 to C-7 of [elgamal2010].** For
every `p(u) p(v | u) p(x | v)` there is `p(u') p(v' | u') p(x' | v')` with `|𝒰'| = |𝒳| + 2` and
`𝒱' = 𝒰' × [1 : |𝒳| + 1]`, so that `|𝒱'| = (|𝒳| + 1) (|𝒳| + 2)`, and the same `I(X; Y₁ | V)`,
`I(V; Y₂ | U)` and `I(U; Y₃)`. -/
theorem exists_bc3_card {β₁ β₂ β₃ : Type*} [Fintype β₁] [Fintype β₂] [Fintype β₃]
    {T₁ : α → β₁ → ℝ} {T₂ : α → β₂ → ℝ} {T₃ : α → β₃ → ℝ} {r : 𝒰 × 𝒱 → ℝ} (hr : IsPMF r)
    (hc : IsChannel c) (hT₁ : IsChannel T₁) (hT₂ : IsChannel T₂) (hT₃ : IsChannel T₃) :
    ∃ (r' : Fin (Fintype.card α + 2) × (Fin (Fintype.card α + 2) × Fin (Fintype.card α + 1)) → ℝ)
      (c' : Fin (Fintype.card α + 2) × Fin (Fintype.card α + 1) → α → ℝ),
      IsPMF r' ∧ IsChannel c' ∧ bc3InfoXV r' c' T₁ = bc3InfoXV r c T₁ ∧
        bc3InfoVU r' c' T₂ = bc3InfoVU r c T₂ ∧ bc3InfoU r' c' T₃ = bc3InfoU r c T₃ := by
  classical
  obtain ⟨z₀⟩ : Nonempty (𝒰 × 𝒱) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hr)
  have h𝒱 : Nonempty 𝒱 := ⟨z₀.2⟩
  have hαpos : 0 < Fintype.card α := card_pos_of_isPMF (hc z₀.2)
  have hα : Nonempty α := Fintype.card_pos_iff.1 hαpos
  -- The tree form of the law.
  set a : 𝒰 → ℝ := fun u => ∑ v, r (u, v) with ha
  set b := wtPosterior r with hbd
  have haP : IsPMF a := wiretapMarg_isPMF hr
  have hb : IsChannel b := wtPosterior_isChannel hr
  have hre : r = fun z : 𝒰 × 𝒱 => a z.1 * b z.1 z.2 := funext fun z =>
    (marg_mul_wtPosterior hr z).symm
  -- The first step: a mixture of `|𝒳| + 2` laws of `V`.
  set f : Fin 3 → (𝒱 → ℝ) → ℝ := ![fun t => ∑ v, t v * mutualInfoOf (c v) T₁,
    fun t => entropy (outDist (outDist t c) T₂) - ∑ v, t v * entropy (outDist (c v) T₂),
    fun t => entropy (outDist (outDist t c) T₃)] with hf
  have hfc : ∀ k, ContinuousOn (f k) {p | IsPMF p} := by
    intro k
    fin_cases k
    · change ContinuousOn (fun t : 𝒱 → ℝ => ∑ v, t v * mutualInfoOf (c v) T₁) _
      exact Continuous.continuousOn (by fun_prop)
    · change ContinuousOn (fun t : 𝒱 → ℝ => entropy (outDist (outDist t c) T₂) -
        ∑ v, t v * entropy (outDist (c v) T₂)) _
      exact Continuous.continuousOn ((continuous_outDist_entropy c T₂).sub (by fun_prop))
    · exact (continuous_outDist_entropy c T₃).continuousOn
  obtain ⟨a', b', ha', hb', hmean, hmix⟩ := exists_mixture_preserving (κ := Fin 3) (L := c) hc hfc
    haP hb (n := Fintype.card α + 2) (by rw [Fintype.card_fin]; omega)
  have hm₁ := hmix 0
  have hm₂ := hmix 1
  have hm₃ := hmix 2
  simp only [hf, Matrix.cons_val] at hm₁ hm₂ hm₃
  -- The second step: for each `u'`, a mixture of `|𝒳| + 1` laws of `X`.
  set d : α → α → ℝ := fun x y => if x = y then 1 else 0 with hd
  have hdC : IsChannel d := fun x =>
    ⟨fun y => by simp only [hd]; split_ifs <;> norm_num, by simp [hd]⟩
  have hdO : ∀ t : α → ℝ, outDist t d = t := fun t => by
    funext y
    simp [outDist, hd]
  set e : Bool → (α → ℝ) → ℝ := fun k t =>
    if k then mutualInfoOf t T₁ else entropy (outDist t T₂) with he
  have hec : ∀ k, ContinuousOn (e k) {p | IsPMF p} := by
    rintro (_ | _)
    · simpa [he] using (continuous_entropy_outDist T₂).continuousOn
    · simpa [he] using continuousOn_mutualInfoOf hT₁
  have hstep := fun i => exists_mixture_preserving (κ := Bool) (L := d) (a := b' i) (b := c)
    hdC hec (hb' i) hc (n := Fintype.card α + 1) (by rw [Fintype.card_bool]; omega)
  choose b₂ c₂ hb₂ hc₂ hmean' hmix' using hstep
  simp only [hdO] at hmean'
  have hX : ∀ i, outDist (b' i) c = ∑ j, b₂ i j • c₂ i j := fun i => by
    rw [hmean' i]
    funext x
    simp [outDist, Finset.sum_apply]
  have hI : ∀ i, ∑ j, b₂ i j * mutualInfoOf (c₂ i j) T₁ = ∑ v, b' i v * mutualInfoOf (c v) T₁ :=
    fun i => by simpa [he] using hmix' i true
  have hH : ∀ i, ∑ j, b₂ i j * entropy (outDist (c₂ i j) T₂) =
      ∑ v, b' i v * entropy (outDist (c v) T₂) := fun i => by simpa [he] using hmix' i false
  -- The new tree, with `V₃ = (U', V₂)`.
  set B : Fin (Fintype.card α + 2) → Fin (Fintype.card α + 2) × Fin (Fintype.card α + 1) → ℝ :=
    fun u z => if u = z.1 then b₂ u z.2 else 0 with hB
  set C : Fin (Fintype.card α + 2) × Fin (Fintype.card α + 1) → α → ℝ := fun z => c₂ z.1 z.2 with hC
  have hsum : ∀ (u : Fin (Fintype.card α + 2)) (g : Fin (Fintype.card α + 2) ×
      Fin (Fintype.card α + 1) → ℝ), ∑ z, B u z * g z = ∑ j, b₂ u j * g (u, j) := fun u g => by
    rw [Fintype.sum_prod_type, sum_eq_single u (fun u' _ hu => by simp [hB, hu.symm]) (by simp)]
    simp [hB]
  have hBC : IsChannel B := fun u => by
    refine ⟨fun z => ?_, ?_⟩
    · simp only [hB]
      split_ifs
      exacts [(hb₂ u).nonneg _, le_rfl]
    · have := hsum u fun _ => 1
      simpa [(hb₂ u).sum_eq_one] using this
  have hCC : IsChannel C := fun z => hc₂ z.1 z.2
  have hBX : ∀ u, outDist (B u) C = outDist (b' u) c := fun u => by
    rw [hX u]
    funext x
    simp only [outDist, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hsum u fun z => C z x
  refine ⟨fun z => a' z.1 * B z.1 z.2, C, tree_isPMF ha' hBC, hCC, ?_, ?_, ?_⟩
  · rw [hre, bc3InfoXV_tree ha' hBC hCC hT₁, bc3InfoXV_tree haP hb hc hT₁, ← hm₁]
    refine sum_congr rfl fun u _ => ?_
    rw [hsum u fun z => mutualInfoOf (C z) T₁, hI u]
  · rw [hre, bc3InfoVU_tree ha' hBC hCC hT₂, bc3InfoVU_tree haP hb hc hT₂, ← hm₂]
    refine sum_congr rfl fun u _ => ?_
    rw [hBX u, hsum u fun z => entropy (outDist (C z) T₂), hH u]
  · rw [hre, bc3InfoU_tree ha' hBC hCC hT₃, bc3InfoU_tree haP hb hc hT₃, ← hm₃]
    simp only [hBX]
    rw [hmean]

end InfoTheory
