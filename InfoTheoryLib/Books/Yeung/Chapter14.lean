/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Capacity
public import InfoTheoryLib.IMeasure.CondMutIndep
public import InfoTheoryLib.InfoInequalities.ShannonType
public import InfoTheoryLib.MarkovChain.Sequence

/-!
# Yeung, Chapter 14: Shannon-Type Inequalities

This file indexes the formalization of Chapter 14 of [yeung2008], and contains its worked examples
and aliases named after the numbers of the results, so the index is checked by Lean. It cites the
draft of 15 November 2007, which numbers definitions, theorems and examples with one counter per
chapter. The end-of-chapter problems and the historical notes are not included.

## Conventions

* **Entropy space.** As in Chapter 13, `h : EntropySpace ι` has coordinates on the nonempty
  subsets, and `h.extend` adds `h_∅ = 0`.
* **Elemental forms.** An elemental form `I(Xᵢ; Xⱼ | X_K)` is indexed by the unordered pair
  `{i, j}` and `K`, so that each form occurs once. The matrix `G` has a row for each form.
* **Indexing.** The variables are `X i` for `i : Fin n`, starting at `0`: the book's `X₁` is
  `X 0`. In Examples 14.6–14.9 the book's `X, Y, Z, T` are `X 0, X 1, X 2, X 3`.
* **ITIP.** Section 14.4 describes a program. The examples that it proves are proved here with
  the basic inequalities and `linarith`.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### 14.1 The Elemental Inequalities
* (14.1)–(14.11): `chain_rule_condMutualInfo` (`MutualInformation.Conditional`), and for set
  functions `condInfo_insert_left` (`InfoInequalities.ShannonType`).
* The elemental forms and (14.12): `ElemForm`, `elemValue`, `card_elemForm`
  (`InfoInequalities.ShannonType`).
* Example 14.1: `example_14_1` (here).
* The equivalence of the elemental and the basic inequalities: `isPolymatroid_iff_elemValue_nonneg`
  (`InfoInequalities.ShannonType`), through the polymatroidal axioms.
* Example 14.2: `example_14_2` (here).

### 14.2 A Linear Programming Approach
* (14.23): `elemMatrix`, `elemMatrix_mulVec`, `shannonRegion`, with `mem_shannonRegion_iff`
  (`InfoInequalities.ShannonType`): `Γₙ` is the set of polymatroids.
* (14.25): `nonneg_of_mem_shannonRegion`, `zero_mem_shannonRegion`
  (`InfoInequalities.ShannonType`).
* (14.26): `entropicRegion_subset_shannonRegion` (`InfoInequalities.ShannonType`).
* (14.27)–(14.32): `IsShannonType`, `IsShannonType.ineqAlwaysHolds`
  (`InfoInequalities.ShannonType`).
* Theorem 14.3: `theorem_14_3` (here), from `isShannonType_iff_isLeast`
  (`InfoInequalities.ShannonType`).
* Theorem 14.4: `theorem_14_4` (here), from `isShannonType_iff_isLeast`
  (`InfoInequalities.ShannonType`).

### 14.3 A Duality
* Theorem 14.5: `theorem_14_5` (here), which is `isShannonType_univ_iff`
  (`InfoInequalities.ShannonType`). The proof uses the Farkas lemma
  `FourierMotzkin.exists_nonneg_comb_of_infeasible` (`ForMathlib.FourierMotzkin`) instead of the
  duality theorem of linear programming.

### 14.4 Machine Proving – ITIP
* Examples 14.6 and 14.7: `example_14_6`, `example_14_7` (here).
* Example 14.8: `example_14_8` (here), the bound `H(X) + H(Y) + H(Z) ≥ 3 H(S)`, and
  `example_14_8_tight` (here), the construction that shows that `3` is the best constant.
* Example 14.9: `example_14_9` (here).

### 14.5 Tackling the Implication Problem
* (14.67)–(14.70), the semi-graphoid axioms: `condIndep_comm`, `CondIndep.decomposition`,
  `CondIndep.weak_union`, `CondIndep.contraction` (`InfoInequalities.ShannonType`).
* (14.71): `condIndep_pair_iff` (`InfoInequalities.ShannonType`).

### 14.6 Minimality of the Elemental Inequalities
* (14.80)–(14.82): `elemAtoms`, `elemValue_atomsToEntropy` (`InfoInequalities.ShannonType`).
* The minimality: `exists_elemental_nonredundant` (`InfoInequalities.ShannonType`). The measure
  (14.87) of the book does not work in general: for `n = 4` and the inequality
  `I(X₁; X₂ | X₄) ≥ 0`, it is `-2` on `X̃₁ ∩ X̃₂ ∩ X̃₃ ∩ X̃₄ᶜ`, so it violates
  `I(X₁; X₃ | X₄) ≥ 0` too (the argument after (14.100) misses that the one atom can be
  `C_{ij|K}(L(i, j, K))`). The library uses the measure `-1` on `X̃_{N - K}`, `0` on the other atoms
  of `X̃ᵢ ∩ X̃ⱼ - X̃_K`, and `1` elsewhere.

### Appendix 14.A
* The polymatroidal axioms P1–P3: `IsPolymatroid` (`InfoInequalities.Polymatroid`).
* The entropy function is a polymatroid: `isPolymatroid_blockEntropy`
  (`InfoInequalities.Polymatroid`).
* The polymatroidal axioms are equivalent to the basic inequalities:
  `isPolymatroid_iff_condInfo_nonneg` (`InfoInequalities.ShannonType`).
* Submodularity for `n` variables indexed by `Fin n`: `IsSubmodular` (`Inequalities.Han`), with
  `subsetEntropy` (`Inequalities.SubsetEntropy`).

## Not formalized

* The software ITIP of Section 14.4, and the reformulation (14.38)–(14.41) of the linear program
  for a computer, which concern the computation rather than the mathematics.
* The three ITIP sessions at the start of Section 14.4.
* Figures 14.1 to 14.5.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 14
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory.Yeung

/-- **Theorem 14.3.** `b ⬝ h ≥ 0` is a Shannon-type inequality if and only if the minimum of
`b ⬝ h` subject to `G h ≥ 0` is zero, (14.33). -/
theorem theorem_14_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (b : EntropySpace ι) :
    IsShannonType b Set.univ ↔ IsLeast (infoExpr b '' (shannonRegion ι ∩ Set.univ)) 0 :=
  isShannonType_iff_isLeast b (Set.mem_univ 0)

/-- **Theorem 14.4.** `b ⬝ h ≥ 0` is a Shannon-type inequality under the constraint `Q h = 0` if
and only if the minimum of `b ⬝ h` subject to `G h ≥ 0` and `Q h = 0` is zero, (14.37). -/
theorem theorem_14_4 {ι : Type*} [Fintype ι] [DecidableEq ι] {q : Type*}
    (Q : Matrix q {α : Finset ι // α.Nonempty} ℝ) (b : EntropySpace ι) :
    IsShannonType b {h | Q.mulVec h = 0} ↔
      IsLeast (infoExpr b '' (shannonRegion ι ∩ {h | Q.mulVec h = 0})) 0 :=
  isShannonType_iff_isLeast b (by simp)

/-- **Theorem 14.5.** -/
alias theorem_14_5 := isShannonType_univ_iff

/-! ### Examples 14.1 and 14.2 -/

section Elemental

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, Fintype (A i)] {μ : Ω → ℝ} {X : ∀ i, Ω → A i}

omit [Fintype ι] in
/-- `I(Xₐ; X_b | X_c)` in terms of joint entropies of literal index sets. -/
lemma condMutualInfo_eq_blockEntropy_of_eq [Finite ι] (hμ : IsPMF μ) {a b c : ι}
    {U₁ U₂ U₃ : Finset ι} (h₁ : {a} ∪ {c} = U₁) (h₂ : {b} ∪ {c} = U₂)
    (h₃ : {a} ∪ {b} ∪ {c} = U₃) :
    I[X a : X b | X c ; μ] =
      blockEntropy μ X U₁ + blockEntropy μ X U₂ - blockEntropy μ X U₃ - blockEntropy μ X {c} := by
  have := Fintype.ofFinite ι
  rw [← iMeasure_inter_sdiff hμ (rvEquiv_blockRV_singleton X a) (rvEquiv_blockRV_singleton X b)
    (rvEquiv_blockRV_singleton X c), iMeasure_inter_sdiff_eq_blockEntropy hμ h₁ h₂ h₃]

end Elemental

section Three

variable {Ω : Type*} [Fintype Ω] {A : Fin 3 → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}

/-- **Example 14.1.** For `n = 3`,
`H(X₁, X₂) = H(X₁ | X₂, X₃) + I(X₁; X₂) + I(X₁; X₃ | X₂) + H(X₂ | X₁, X₃) + I(X₂; X₃ | X₁)`, a sum
of elemental forms (14.13)–(14.15). -/
theorem example_14_1 (hμ : IsPMF μ) (X : ∀ i, Ω → A i) :
    H[blockRV X {0, 1} ; μ] = H[X 0 | blockRV X {1, 2} ; μ] + I[X 0 : X 1 ; μ] +
      I[X 0 : X 2 | X 1 ; μ] + H[X 1 | blockRV X {0, 2} ; μ] + I[X 1 : X 2 | X 0 ; μ] := by
  set f := blockEntropy μ X with hf
  have hH₁ : H[X 0 | blockRV X {1, 2} ; μ] = f {0, 1, 2} - f {1, 2} := by
    rw [← iMeasure_sdiff hμ (rvEquiv_blockRV_singleton X 0) (RVEquiv.refl _),
      iMeasure_tilde_sdiff hμ, show ({1, 2} ∪ {0} : Finset (Fin 3)) = {0, 1, 2} by decide]
  have hH₂ : H[X 1 | blockRV X {0, 2} ; μ] = f {0, 1, 2} - f {0, 2} := by
    rw [← iMeasure_sdiff hμ (rvEquiv_blockRV_singleton X 1) (RVEquiv.refl _),
      iMeasure_tilde_sdiff hμ, show ({0, 2} ∪ {1} : Finset (Fin 3)) = {0, 1, 2} by decide]
  have hI : I[X 0 : X 1 ; μ] = f {0} + f {1} - f {0, 1} := by
    rw [← iMeasure_inter hμ (rvEquiv_blockRV_singleton X 0) (rvEquiv_blockRV_singleton X 1),
      ← sdiff_empty (s := tilde {0} ∩ tilde {1}), ← tilde_empty,
      iMeasure_inter_sdiff_eq_blockEntropy hμ (U₁ := {0}) (U₂ := {1}) (U₃ := {0, 1})
        (union_empty _) (union_empty _) (by decide), blockEntropy_empty hμ, sub_zero]
  have hI₁ := condMutualInfo_eq_blockEntropy_of_eq (X := X) hμ (a := 0) (b := 2) (c := 1)
    (U₁ := {0, 1}) (U₂ := {1, 2}) (U₃ := {0, 1, 2}) (by decide) (by decide) (by decide)
  have hI₂ := condMutualInfo_eq_blockEntropy_of_eq (X := X) hμ (a := 1) (b := 2) (c := 0)
    (U₁ := {0, 1}) (U₂ := {0, 2}) (U₃ := {0, 1, 2}) (by decide) (by decide) (by decide)
  rw [hH₁, hH₂, hI, hI₁, hI₂]
  change f {0, 1} = _
  ring

/-- **Example 14.2.** The basic inequality `H(X₁, X₂) ≥ 0` is the sum of the elemental
inequalities (14.18)–(14.22). -/
theorem example_14_2 (hμ : IsPMF μ) (X : ∀ i, Ω → A i) : 0 ≤ H[blockRV X {0, 1} ; μ] := by
  rw [example_14_1 hμ X]
  have := condEntropy_nonneg hμ (X 0) (blockRV X {1, 2})
  have := mutualInfo_nonneg hμ (X 0) (X 1)
  have := condMutualInfo_nonneg hμ (X 0) (X 2) (X 1)
  have := condEntropy_nonneg hμ (X 1) (blockRV X {0, 2})
  have := condMutualInfo_nonneg hμ (X 1) (X 2) (X 0)
  linarith

end Three

/-! ### Examples 14.6 and 14.7 -/

/-- The random variables of Examples 14.6 and 14.7 on `Bool` with the uniform distribution:
`X = T = U` with `H(U) > 0`, and `Y`, `Z` constant. -/
def example146Z : ℕ → Bool → Bool
  | 0 => id
  | 3 => id
  | _ => fun _ => false

lemma example146_mutualInfo :
    I[example146Z 1 : example146Z 2 ; uniformPMF Bool] = 0 ∧
      I[example146Z 0 : example146Z 3 ; uniformPMF Bool] = log 2 := by
  have hμ : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  constructor
  · change I[(fun _ : Bool => false) : (fun _ : Bool => false) ; uniformPMF Bool] = 0
    rw [mutualInfo_self hμ, entropyRV_const hμ]
  · change I[(id : Bool → Bool) : (id : Bool → Bool) ; uniformPMF Bool] = log 2
    rw [mutualInfo_self hμ, entropyRV, dist_id, entropy_uniformPMF, Fintype.card_bool,
      Nat.cast_ofNat]

lemma example146_markov :
    MarkovChain (uniformPMF Bool) (example146Z 0) (example146Z 1) (example146Z 2) ∧
      MarkovChain (uniformPMF Bool) (example146Z 1) (example146Z 2) (example146Z 3) := by
  have hμ : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  rw [markovChain_iff_condIndep hμ, markovChain_iff_condIndep hμ,
    ← condMutualInfo_eq_zero_iff hμ, ← condMutualInfo_eq_zero_iff hμ]
  exact ⟨condMutualInfo_const_mid hμ _ false _, condMutualInfo_const_left hμ false _ _⟩

/-- **Example 14.6.** The two short Markov chains `X → Y → Z` and `Y → Z → T` do not imply the
long Markov chain `X → Y → Z → T`. -/
theorem example_14_6 :
    MarkovChain (uniformPMF Bool) (example146Z 0) (example146Z 1) (example146Z 2) ∧
      MarkovChain (uniformPMF Bool) (example146Z 1) (example146Z 2) (example146Z 3) ∧
        ¬IsMarkovChain (uniformPMF Bool) example146Z 4 := by
  refine ⟨example146_markov.1, example146_markov.2, fun h => ?_⟩
  have := h.data_processing uniformPMF_isPMF (by norm_num) (i := 0) (j := 1) (k := 2) (l := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [example146_mutualInfo.1, example146_mutualInfo.2] at this
  linarith [log_pos (by norm_num : (1 : ℝ) < 2)]

/-- **Example 14.7.** Under the two short Markov chains `X → Y → Z` and `Y → Z → T`, the
inequality `I(Y; Z) ≥ I(X; T)` (14.53) of the data processing theorem does not always hold. -/
theorem example_14_7 :
    MarkovChain (uniformPMF Bool) (example146Z 0) (example146Z 1) (example146Z 2) ∧
      MarkovChain (uniformPMF Bool) (example146Z 1) (example146Z 2) (example146Z 3) ∧
        I[example146Z 1 : example146Z 2 ; uniformPMF Bool] <
          I[example146Z 0 : example146Z 3 ; uniformPMF Bool] := by
  refine ⟨example146_markov.1, example146_markov.2, ?_⟩
  rw [example146_mutualInfo.1, example146_mutualInfo.2]
  exact log_pos (by norm_num)

/-! ### Examples 14.8 and 14.9 -/

section Secret

variable {Ω σ α β γ : Type*} [Fintype Ω] [Fintype σ] [Fintype α] [Fintype β] [Fintype γ]
  {μ : Ω → ℝ}

/-- One share of a secret sharing scheme: if `S` is recovered from `(A, B)` and `B` alone tells
nothing about `S`, then `H(A) ≥ H(S)`. -/
lemma entropyRV_ge_of_secret (hμ : IsPMF μ) {S : Ω → σ} {A : Ω → α} {B : Ω → β}
    (h₁ : H[S | pair A B ; μ] = 0) (h₂ : I[S : B ; μ] = 0) : H[S ; μ] ≤ H[A ; μ] := by
  -- `H(S) = H(S | B) = I(S; A | B) ≤ H(A | B) ≤ H(A)`
  have e₁ : H[S | B ; μ] = H[S ; μ] := by
    rw [mutualInfo_eq_entropy_sub_condEntropy hμ] at h₂
    linarith
  have e₂ : I[S : A | B ; μ] = H[S | B ; μ] := by
    rw [condMutualInfo, h₁, sub_zero]
  have e₃ : I[S : A | B ; μ] ≤ H[A | B ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
    linarith [condEntropy_nonneg hμ A (pair S B)]
  linarith [condEntropy_le_entropy hμ A B]

/-- **Example 14.8 (Secret Sharing).** If the secret `S` can be recovered from any two of the
pieces `X`, `Y`, `Z` (14.56), and no information about `S` can be obtained from any one of them
(14.57), then `H(X) + H(Y) + H(Z) ≥ 3 H(S)` (14.59) with `c = 3`. -/
theorem example_14_8 (hμ : IsPMF μ) {S : Ω → σ} {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hXY : H[S | pair X Y ; μ] = 0) (hYZ : H[S | pair Y Z ; μ] = 0)
    (hXZ : H[S | pair X Z ; μ] = 0) (hX : I[S : X ; μ] = 0) (hY : I[S : Y ; μ] = 0)
    (hZ : I[S : Z ; μ] = 0) : 3 * H[S ; μ] ≤ H[X ; μ] + H[Y ; μ] + H[Z ; μ] := by
  have hZX : H[S | pair Z X ; μ] = 0 := by
    rw [condEntropy_congr_right hμ S (X := pair X Z) (X' := pair Z X) Prod.swap
      Prod.swap_injective fun _ => rfl, hXZ]
  linarith [entropyRV_ge_of_secret hμ hXY hY, entropyRV_ge_of_secret hμ hYZ hZ,
    entropyRV_ge_of_secret hμ hZX hX]

/-- A random variable that is a function of `W` has zero conditional entropy given `W`. -/
lemma condEntropy_eq_zero_of_eq_comp (hμ : IsPMF μ) {S : Ω → σ} {W : Ω → α} (g : α → σ)
    (h : ∀ ω, S ω = g (W ω)) : H[S | W ; μ] = 0 := by
  rw [condEntropy_eq_sub hμ, sub_eq_zero]
  exact entropyRV_eq_of_injective μ (fun w => (w, g w)) (fun _ _ e => (Prod.mk.inj e).1)
    fun ω => by simp [pair, h ω]

/-- If `ω ↦ (U ω, V ω)` is a bijection and `ω` is uniform, then `U` and `V` are independent and
uniform. -/
lemma uniform_of_equiv [Nonempty Ω] [Nonempty α] [Nonempty β] (e : Ω ≃ α × β) :
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

end Secret

/-- The bijection `(s, n) ↦ (s, s + n)` of `(ZMod 3)²`. -/
def example148e₂ : ZMod 3 × ZMod 3 ≃ ZMod 3 × ZMod 3 where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.2 - p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- The bijection `(s, n) ↦ (s, s + 2n)` of `(ZMod 3)²`. -/
def example148e₃ : ZMod 3 × ZMod 3 ≃ ZMod 3 × ZMod 3 where
  toFun p := (p.1, p.1 + 2 * p.2)
  invFun p := (p.1, 2 * (p.2 - p.1))
  left_inv p := by
    have : ∀ s n : ZMod 3, 2 * (s + 2 * n - s) = n := by decide
    exact Prod.ext rfl (this p.1 p.2)
  right_inv p := by
    have : ∀ s z : ZMod 3, s + 2 * (2 * (z - s)) = z := by decide
    exact Prod.ext rfl (this p.1 p.2)

/-- **Example 14.8**, the construction (14.60)–(14.66): with `S` and `N` independent and uniform on
`{0, 1, 2}`, the pieces `X = N`, `Y = S + N` and `Z = S + 2N` satisfy (14.56)–(14.57), and
`H(X) + H(Y) + H(Z) = 3 H(S) > 0`, so the constant `3` in (14.59) cannot be improved. -/
theorem example_14_8_tight :
    let μ := uniformPMF (ZMod 3 × ZMod 3)
    let S : ZMod 3 × ZMod 3 → ZMod 3 := fun p => p.1
    let X : ZMod 3 × ZMod 3 → ZMod 3 := fun p => p.2
    let Y : ZMod 3 × ZMod 3 → ZMod 3 := fun p => p.1 + p.2
    let Z : ZMod 3 × ZMod 3 → ZMod 3 := fun p => p.1 + 2 * p.2
    H[S | pair X Y ; μ] = 0 ∧ H[S | pair Y Z ; μ] = 0 ∧ H[S | pair X Z ; μ] = 0 ∧
      I[S : X ; μ] = 0 ∧ I[S : Y ; μ] = 0 ∧ I[S : Z ; μ] = 0 ∧
        H[X ; μ] + H[Y ; μ] + H[Z ; μ] = 3 * H[S ; μ] ∧ 0 < H[S ; μ] := by
  intro μ S X Y Z
  have hμ : IsPMF μ := uniformPMF_isPMF
  obtain ⟨h₁, hS, hX⟩ := uniform_of_equiv (Equiv.refl (ZMod 3 × ZMod 3))
  obtain ⟨h₂, -, hY⟩ := uniform_of_equiv example148e₂
  obtain ⟨h₃, -, hZ⟩ := uniform_of_equiv example148e₃
  have hcard : Fintype.card (ZMod 3) = 3 := ZMod.card 3
  refine ⟨condEntropy_eq_zero_of_eq_comp hμ (fun w => w.2 - w.1) fun p => by simp [S, X, Y],
    condEntropy_eq_zero_of_eq_comp hμ (fun w => 2 * w.1 - w.2) fun p => by simp [S, Y, Z]; ring,
    condEntropy_eq_zero_of_eq_comp hμ (fun w => w.2 - 2 * w.1) fun p => by simp [S, X, Z],
    h₁, h₂, h₃, ?_, ?_⟩
  · change H[fun p => (Equiv.refl _ p).2 ; μ] + H[fun p => (example148e₂ p).2 ; μ] +
      H[fun p => (example148e₃ p).2 ; μ] = 3 * H[fun p => (Equiv.refl _ p).1 ; μ]
    rw [hX, hY, hZ, hS]
    ring
  · change 0 < H[fun p => (Equiv.refl _ p).1 ; μ]
    rw [hS, hcard]
    exact log_pos (by norm_num)


section Four

variable {Ω : Type*} [Fintype Ω] {A : Fin 4 → Type*} [∀ i, Fintype (A i)] {μ : Ω → ℝ}

/-- **Example 14.9.** `I(X; Y | Z) = I(X; T | Z) = I(X; T | Y) = I(X; Z | Y) = I(X; Z | T) = 0`
imply `I(X; Y | T) = 0`, (14.73), by the basic inequalities; in fact the conclusion is a linear
combination of the hypotheses. -/
theorem example_14_9 (hμ : IsPMF μ) (X : ∀ i, Ω → A i) (h₁ : I[X 0 : X 1 | X 2 ; μ] = 0)
    (h₂ : I[X 0 : X 3 | X 2 ; μ] = 0) (h₃ : I[X 0 : X 3 | X 1 ; μ] = 0)
    (h₄ : I[X 0 : X 2 | X 1 ; μ] = 0) (h₅ : I[X 0 : X 2 | X 3 ; μ] = 0) :
    I[X 0 : X 1 | X 3 ; μ] = 0 := by
  rw [condMutualInfo_eq_blockEntropy_of_eq hμ (U₁ := {0, 2}) (U₂ := {1, 2}) (U₃ := {0, 1, 2})
    (by decide) (by decide) (by decide)] at h₁
  rw [condMutualInfo_eq_blockEntropy_of_eq hμ (U₁ := {0, 2}) (U₂ := {2, 3}) (U₃ := {0, 2, 3})
    (by decide) (by decide) (by decide)] at h₂
  rw [condMutualInfo_eq_blockEntropy_of_eq hμ (U₁ := {0, 1}) (U₂ := {1, 3}) (U₃ := {0, 1, 3})
    (by decide) (by decide) (by decide)] at h₃
  rw [condMutualInfo_eq_blockEntropy_of_eq hμ (U₁ := {0, 1}) (U₂ := {1, 2}) (U₃ := {0, 1, 2})
    (by decide) (by decide) (by decide)] at h₄
  rw [condMutualInfo_eq_blockEntropy_of_eq hμ (U₁ := {0, 3}) (U₂ := {2, 3}) (U₃ := {0, 2, 3})
    (by decide) (by decide) (by decide)] at h₅
  rw [condMutualInfo_eq_blockEntropy_of_eq hμ (U₁ := {0, 3}) (U₂ := {1, 3}) (U₃ := {0, 1, 3})
    (by decide) (by decide) (by decide)]
  linear_combination h₁ + h₃ + h₅ - h₂ - h₄

end Four

end InfoTheory.Yeung
