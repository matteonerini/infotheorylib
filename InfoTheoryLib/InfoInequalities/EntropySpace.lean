/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.IMeasure.Realization
public import InfoTheoryLib.InfoInequalities.Polymatroid

/-!
# The entropy space and the region `Γ*ₙ`

The joint entropies `H(X_α)` of random variables `Xᵢ`, `i ∈ ι`, indexed by the nonempty subsets
`α`, form a vector of the *entropy space* `ℋₙ`, the *entropy function* of the variables. The set of
all such vectors is the region `Γ*ₙ` of entropic vectors. An information expression in canonical
form is a linear function `b ⬝ h` of the entropies, and an information inequality `b ⬝ h ≥ 0`
always holds if and only if `Γ*ₙ` lies in the half-space `b ⬝ h ≥ 0`.

Theorem 3.11 shows that the vectors `h` whose I-Measure is nonnegative on every atom are entropic
(Lemma 13.1). These span the entropy space, so an information identity `b ⬝ h = 0` holds for all
random variables only if `b = 0` (Theorem 13.2), and the canonical form of an information
expression is unique (Corollary 13.3).

## Main definitions

* `EntropySpace ι`: the entropy space `ℋₙ`.
* `entropyVector μ X`: the entropy function of the random variables `X`.
* `entropicRegion ι`: the region `Γ*ₙ`.
* `infoExpr b h`: the information expression `b ⬝ h` in canonical form.
* `atomsToEntropy u`: the entropies `h = Cₙ u` of the I-Measure with values `u` on the atoms.
* `IneqAlwaysHolds b Φ`: the inequality `b ⬝ h ≥ 0` always holds under the constraint `Φ`.

## Main statements

* `zero_mem_entropicRegion`, `nonneg_of_mem_entropicRegion`: properties 1 and 3 of `Γ*ₙ`.
* `atomsToEntropy_mem_entropicRegion`: **Lemma 13.1**.
* `infoExpr_eq_zero_iff`: **Theorem 13.2**.
* `infoExpr_eq_iff`: **Corollary 13.3**, the uniqueness of the canonical form.
* `condIndep_blockRV_iff`: (13.77), a conditional independency is a hyperplane.
* `ciImplies_iff`: the implication problem in terms of `Γ*ₙ`.

## Implementation notes

The book proves Theorem 13.2 by showing that `Γ*ₙ` has positive Lebesgue measure. Here the proof
is linear algebra: every vector of `ℋₙ` is a difference of two entropic vectors `Cₙ u` and
`Cₙ v` with `u, v ≥ 0`, by Lemma 13.1 and Theorem 3.6, so `b ⬝ h = 0` on `Γ*ₙ` gives `b ⬝ b = 0`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 13
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

universe u

/-- **The entropy space** `ℋₙ`: vectors `h` with a coordinate `h_α` for each nonempty subset `α`
of the indices. -/
abbrev EntropySpace (ι : Type*) := {α : Finset ι // α.Nonempty} → ℝ

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The entropy function** `H_Θ` of random variables, (13.23): `h_α = H(X_α)`. -/
def entropyVector {Ω : Type*} [Fintype Ω] {A : ι → Type*} [∀ i, Fintype (A i)] (μ : Ω → ℝ)
    (X : ∀ i, Ω → A i) : EntropySpace ι :=
  fun α => blockEntropy μ X α.1

/-- An information expression in canonical form, `b ⬝ h = ∑_α b_α h_α`, (13.29). -/
def infoExpr (b h : EntropySpace ι) : ℝ := ∑ α, b α * h α

omit [DecidableEq ι] in
lemma infoExpr_sub_right (b h₁ h₂ : EntropySpace ι) :
    infoExpr b (h₁ - h₂) = infoExpr b h₁ - infoExpr b h₂ := by
  simp only [infoExpr, Pi.sub_apply, mul_sub, sum_sub_distrib]

omit [DecidableEq ι] in
lemma infoExpr_sub_left (b₁ b₂ h : EntropySpace ι) :
    infoExpr (b₁ - b₂) h = infoExpr b₁ h - infoExpr b₂ h := by
  simp only [infoExpr, Pi.sub_apply, sub_mul, sum_sub_distrib]

/-- The entropies `h = Cₙ u` of the signed measure with the values `u` on the nonempty atoms,
(13.35): `h_α = ∑_{A ⊆ X̃_α} u(A)`. -/
def atomsToEntropy (u : NAtom ι → ℝ) : EntropySpace ι :=
  fun α => ∑ a ∈ tilde α.1, u a

lemma atomsToEntropy_sub (u v : NAtom ι → ℝ) :
    atomsToEntropy (u - v) = atomsToEntropy u - atomsToEntropy v := by
  funext α
  simp only [atomsToEntropy, Pi.sub_apply, sum_sub_distrib]

/-- Every vector of the entropy space is `Cₙ u` for some `u`, by Theorem 3.6. -/
lemma exists_atomsToEntropy_eq (h : EntropySpace ι) : ∃ u, atomsToEntropy u = h := by
  classical
  set g : Finset ι → ℝ := fun G => if hG : G.Nonempty then h ⟨G, hG⟩ else 0 with hg
  have h0 : g ∅ = 0 := by simp [hg]
  refine ⟨fun a => atomValue g a.1, funext fun α => ?_⟩
  change signedMeasureOf g (tilde α.1) = h α
  rw [signedMeasureOf_tilde h0]
  simp [hg, α.2]

/-- The extension `h_∅ = 0` of a vector of the entropy space to all subsets. -/
def EntropySpace.extend (h : EntropySpace ι) (s : Finset ι) : ℝ :=
  if hs : s.Nonempty then h ⟨s, hs⟩ else 0

omit [Fintype ι] in
lemma extend_entropyVector {Ω : Type*} [Fintype Ω] {A : ι → Type*} [∀ i, Fintype (A i)]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    (entropyVector μ X).extend = blockEntropy μ X := by
  funext s
  rw [EntropySpace.extend]
  split_ifs with hs
  · rfl
  · rw [not_nonempty_iff_eq_empty.1 hs, blockEntropy_empty hμ]

end

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **The region `Γ*ₙ`** of entropic vectors, (13.24): the entropy functions of random variables
`Xᵢ`, `i ∈ ι`. -/
def entropicRegion (ι : Type u) [Fintype ι] [DecidableEq ι] : Set (EntropySpace ι) :=
  {h | ∃ (Ω : Type u) (_ : Fintype Ω) (A : ι → Type u) (_ : ∀ i, Fintype (A i)) (μ : Ω → ℝ)
    (X : ∀ i, Ω → A i), IsPMF μ ∧ entropyVector μ X = h}

lemma entropyVector_mem_entropicRegion {Ω : Type u} [Fintype Ω] {A : ι → Type u}
    [∀ i, Fintype (A i)] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    entropyVector μ X ∈ entropicRegion ι :=
  ⟨Ω, inferInstance, A, inferInstance, μ, X, hμ, rfl⟩

/-- Property 1 of `Γ*ₙ`: it contains the origin, the entropy function of constant random
variables. -/
theorem zero_mem_entropicRegion : (0 : EntropySpace ι) ∈ entropicRegion ι := by
  have hμ : IsPMF (fun _ : PUnit.{u + 1} => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩
  refine ⟨PUnit, inferInstance, fun _ => PUnit, inferInstance, _, fun _ _ => PUnit.unit, hμ, ?_⟩
  funext α
  have h₁ := entropyRV_le_log_card hμ (blockRV (fun (_ : ι) (_ : PUnit.{u + 1}) =>
    PUnit.unit) α.1)
  have h₂ := entropyRV_nonneg hμ (blockRV (fun (_ : ι) (_ : PUnit.{u + 1}) => PUnit.unit) α.1)
  rw [Fintype.card_unique, Nat.cast_one, log_one] at h₁
  exact le_antisymm h₁ h₂

/-- Property 3 of `Γ*ₙ`: it lies in the nonnegative orthant of the entropy space. -/
theorem nonneg_of_mem_entropicRegion {h : EntropySpace ι} (hh : h ∈ entropicRegion ι)
    (α : {α : Finset ι // α.Nonempty}) : 0 ≤ h α := by
  obtain ⟨Ω, _, A, _, μ, X, hμ, rfl⟩ := hh
  exact entropyRV_nonneg hμ _

/-- The region `Ψ*ₙ = {u : Cₙ u ∈ Γ*ₙ}` of the values of the I-Measure on the atoms, (13.36). -/
def entropicAtomRegion (ι : Type u) [Fintype ι] [DecidableEq ι] : Set (NAtom ι → ℝ) :=
  {u | atomsToEntropy u ∈ entropicRegion ι}

/-- **Lemma 13.1.** The nonnegative orthant is contained in `Ψ*ₙ`: if `u ≥ 0`, then `Cₙ u` is
entropic. This is Theorem 3.11. -/
theorem atomsToEntropy_mem_entropicRegion {u : NAtom ι → ℝ} (hu : ∀ a, 0 ≤ u a) :
    u ∈ entropicAtomRegion ι := by
  obtain ⟨Ω, _, A, _, μ, X, hμ, hv⟩ := exists_iMeasure_eq u hu
  refine ⟨Ω, inferInstance, A, inferInstance, μ, X, hμ, funext fun α => ?_⟩
  change blockEntropy μ X α.1 = ∑ a ∈ tilde α.1, u a
  rw [blockEntropy, ← iMeasure_tilde hμ, (isSignedMeasure_iMeasure μ X).eq_sum_singleton]
  exact sum_congr rfl fun a _ => hv a

/-- Every vector of the entropy space is the difference of two entropic vectors. -/
lemma exists_sub_eq (h : EntropySpace ι) :
    ∃ h₁ ∈ entropicRegion ι, ∃ h₂ ∈ entropicRegion ι, h = h₁ - h₂ := by
  obtain ⟨u, rfl⟩ := exists_atomsToEntropy_eq h
  refine ⟨atomsToEntropy fun a => max (u a) 0, atomsToEntropy_mem_entropicRegion fun a =>
    le_max_right _ _, atomsToEntropy fun a => max (-u a) 0,
    atomsToEntropy_mem_entropicRegion fun a => le_max_right _ _, ?_⟩
  rw [← atomsToEntropy_sub]
  congr 1
  funext a
  simp only [Pi.sub_apply]
  rcases le_total 0 (u a) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

/-- **Theorem 13.2.** The unconstrained information identity `b ⬝ h = 0` always holds if and only
if `b` is the zero function. -/
theorem infoExpr_eq_zero_iff (b : EntropySpace ι) :
    (∀ h ∈ entropicRegion ι, infoExpr b h = 0) ↔ b = 0 := by
  constructor
  · intro H
    obtain ⟨h₁, hh₁, h₂, hh₂, he⟩ := exists_sub_eq b
    have hbb : infoExpr b (h₁ - h₂) = 0 := by
      rw [infoExpr_sub_right, H h₁ hh₁, H h₂ hh₂, sub_self]
    rw [← he] at hbb
    have hsq := (sum_eq_zero_iff_of_nonneg fun α _ => mul_self_nonneg (b α)).1 hbb
    exact funext fun α => mul_self_eq_zero.1 (hsq α (mem_univ α))
  · rintro rfl h _
    simp [infoExpr]

/-- **Corollary 13.3.** The canonical form of an information expression is unique. -/
theorem infoExpr_eq_iff (b₁ b₂ : EntropySpace ι) :
    (∀ h ∈ entropicRegion ι, infoExpr b₁ h = infoExpr b₂ h) ↔ b₁ = b₂ := by
  rw [← sub_eq_zero, ← infoExpr_eq_zero_iff]
  simp only [infoExpr_sub_left, sub_eq_zero]

/-! ### A geometrical framework -/

/-- The information inequality `b ⬝ h ≥ 0` **always holds under the constraint** `Φ`: it holds
for the entropy function of all random variables in `Φ`. The unconstrained case is
`Φ = Set.univ`. -/
def IneqAlwaysHolds (b : EntropySpace ι) (Φ : Set (EntropySpace ι)) : Prop :=
  ∀ h ∈ entropicRegion ι ∩ Φ, 0 ≤ infoExpr b h

/-- **Sections 13.3.1–13.3.2.** `b ⬝ h ≥ 0` always holds under `Φ` if and only if
`Γ*ₙ ∩ Φ ⊆ {h : b ⬝ h ≥ 0}`. -/
theorem ineqAlwaysHolds_iff (b : EntropySpace ι) (Φ : Set (EntropySpace ι)) :
    IneqAlwaysHolds b Φ ↔ ∀ (Ω : Type u) [Fintype Ω] (A : ι → Type u) [∀ i, Fintype (A i)]
      (μ : Ω → ℝ) (X : ∀ i, Ω → A i), IsPMF μ → entropyVector μ X ∈ Φ →
        0 ≤ infoExpr b (entropyVector μ X) := by
  constructor
  · intro H Ω _ A _ μ X hμ hΦ
    exact H _ ⟨entropyVector_mem_entropicRegion hμ X, hΦ⟩
  · rintro H h ⟨⟨Ω, _, A, _, μ, X, hμ, rfl⟩, hΦ⟩
    exact H Ω A μ X hμ hΦ

/-- (13.49)–(13.50): an inequality that always holds without constraint always holds under any
constraint. -/
theorem IneqAlwaysHolds.mono {b : EntropySpace ι} {Φ Φ' : Set (EntropySpace ι)}
    (h : IneqAlwaysHolds b Φ') (hΦ : Φ ⊆ Φ') : IneqAlwaysHolds b Φ :=
  fun x hx => h x ⟨hx.1, hΦ hx.2⟩

/-- **Section 13.3.3.** Under the constraint `Φ`, the identity `b ⬝ h = 0` always holds if and only
if both `b ⬝ h ≥ 0` and `b ⬝ h ≤ 0` always hold. -/
theorem forall_infoExpr_eq_zero_iff (b : EntropySpace ι) (Φ : Set (EntropySpace ι)) :
    (∀ h ∈ entropicRegion ι ∩ Φ, infoExpr b h = 0) ↔
      IneqAlwaysHolds b Φ ∧ IneqAlwaysHolds (-b) Φ := by
  have hneg : ∀ h, infoExpr (-b) h = -infoExpr b h := fun h => by
    simp [infoExpr, sum_neg_distrib]
  constructor
  · intro H
    exact ⟨fun h hh => (H h hh).ge, fun h hh => by rw [hneg, H h hh, neg_zero]⟩
  · rintro ⟨H₁, H₂⟩ h hh
    have := H₂ h hh
    rw [hneg] at this
    linarith [H₁ h hh]

/-! ### The implication problem of conditional independence -/

section CI

variable {Ω : Type*} [Fintype Ω] {A : ι → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}
  {X : ∀ i, Ω → A i}

omit [Fintype ι] in
/-- (13.77): `X_α ⊥ X_β | X_γ` if and only if
`H(X_{α ∪ γ}) + H(X_{β ∪ γ}) - H(X_{α ∪ β ∪ γ}) - H(X_γ) = 0`. -/
theorem condIndep_blockRV_iff (hμ : IsPMF μ) (α β γ : Finset ι) :
    CondIndep μ (blockRV X α) (blockRV X β) (blockRV X γ) ↔
      condInfo (blockEntropy μ X) α β γ = 0 := by
  rw [condInfo_blockEntropy hμ, condMutualInfo_eq_zero_iff hμ]

end CI

/-- The hyperplane `E(K)` of the conditional independency `K = (α, β, γ)`, `X_α ⊥ X_β | X_γ`,
(13.78). -/
def ciHyperplane (K : Finset ι × Finset ι × Finset ι) : Set (EntropySpace ι) :=
  {h | condInfo h.extend K.1 K.2.1 K.2.2 = 0}

/-- **Section 13.5.** A collection `Π = {K_l}` of conditional independencies implies a conditional
independency `K` if and only if `(⋂_l E(K_l)) ∩ Γ*ₙ ⊆ E(K)`. -/
theorem ciImplies_iff {κ : Type*} (P : κ → Finset ι × Finset ι × Finset ι)
    (K : Finset ι × Finset ι × Finset ι) :
    (∀ (Ω : Type u) [Fintype Ω] (A : ι → Type u) [∀ i, Fintype (A i)] (μ : Ω → ℝ)
      (X : ∀ i, Ω → A i), IsPMF μ →
        (∀ l, CondIndep μ (blockRV X (P l).1) (blockRV X (P l).2.1) (blockRV X (P l).2.2)) →
          CondIndep μ (blockRV X K.1) (blockRV X K.2.1) (blockRV X K.2.2)) ↔
      (⋂ l, ciHyperplane (P l)) ∩ entropicRegion ι ⊆ ciHyperplane K := by
  constructor
  · rintro H h ⟨hP, Ω, _, A, _, μ, X, hμ, rfl⟩
    simp only [Set.mem_iInter, ciHyperplane, Set.mem_ofPred_eq,
      extend_entropyVector hμ] at hP ⊢
    rw [← condIndep_blockRV_iff hμ]
    exact H Ω A μ X hμ fun l => (condIndep_blockRV_iff hμ _ _ _).2 (hP l)
  · intro H Ω _ A _ μ X hμ hP
    have := H ⟨Set.mem_iInter.2 fun l => ?_, entropyVector_mem_entropicRegion hμ X⟩
    · simp only [ciHyperplane, Set.mem_ofPred_eq, extend_entropyVector hμ] at this
      exact (condIndep_blockRV_iff hμ _ _ _).2 this
    · simp only [ciHyperplane, Set.mem_ofPred_eq, extend_entropyVector hμ]
      exact (condIndep_blockRV_iff hμ _ _ _).1 (hP l)

end InfoTheory
