/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.MarkovChain.CondIndep
public import InfoTheoryLib.MutualInformation.Block

/-!
# Conditional mutual independence

Random variables `Zⱼ`, `j ∈ κ`, are mutually independent conditioning on `Y` if
`p(z | y) = ∏ⱼ p(zⱼ | y)` whenever `p(y) > 0`. As for mutual independence (Theorem 2.39), this is
characterized by entropies: `H(Z | Y) = ∑ⱼ H(Zⱼ | Y)`. Two other characterizations replace the
mutual independence by the conditional independencies `Zᵢ ⊥ (Zⱼ, j ≠ i) | Y`, or by
`H(Z | Y) = ∑ᵢ H(Zᵢ | Y, Zⱼ, j ≠ i)`.

The proofs go through the subfamilies `Z_s = (Zⱼ, j ∈ s)`: adding `Zₐ` to `Z_s` keeps the
mutual independence if and only if `Zₐ ⊥ Z_s | Y` (`condMutIndepOn_insert_iff`).

## Main definitions

* `CondMutIndep μ Z Y`: the `Zⱼ` are mutually independent conditioning on `Y`.

## Main statements

* `condMutIndep_iff_condEntropy_eq_sum`: **Theorem 12.2**.
* `condMutIndep_iff_condMutualInfo_eq_zero`, `condMutIndep_iff_condIndep`: **Theorem 12.3**.
* `condMutIndep_iff_condEntropy_eq_sum_condEntropy`: **Theorem 12.4**.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 12.1
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω κ γ : Type*} [Fintype Ω] {B : κ → Type*} {μ : Ω → ℝ}

/-- Random variables `Zⱼ`, `j ∈ κ`, are **mutually independent conditioning on** `Y` if
`p(z | y) = ∏ⱼ p(zⱼ | y)` for all `z` and all `y` with `p(y) > 0`. -/
def CondMutIndep [Fintype κ] (μ : Ω → ℝ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) : Prop :=
  ∀ y, dist μ Y y ≠ 0 → ∀ z : ∀ j, B j,
    condDist μ (fun ω j => Z j ω) Y y z = ∏ j, condDist μ (Z j) Y y (z j)

/-- The product form `p(y, z_s) p(y)^{|s|} = p(y) ∏_{j ∈ s} p(y, zⱼ)` of the conditional mutual
independence of the subfamily `Z_s`, written with values `z` of the whole family. -/
def CondMutIndepOn (μ : Ω → ℝ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) (s : Finset κ) : Prop :=
  ∀ y (z : ∀ j, B j), dist μ (pair Y (blockRV Z s)) (y, fun j : s => z j) * dist μ Y y ^ #s =
    dist μ Y y * ∏ j ∈ s, dist μ (pair Y (Z j)) (y, z j)

lemma condMutIndepOn_empty (Z : ∀ j, Ω → B j) (Y : Ω → γ) : CondMutIndepOn μ Z Y ∅ := by
  intro y z
  rw [card_empty, pow_zero, mul_one, prod_empty, mul_one]
  refine dist_congr_of_iff μ fun ω => ?_
  have hw : blockRV Z ∅ ω = fun j : (∅ : Finset κ) => z j :=
    funext fun j => absurd j.property (notMem_empty _)
  simp [hw]

/-- Conditional mutual independence is the product form for the whole family. -/
theorem condMutIndep_iff_condMutIndepOn_univ [Fintype κ] (hμ : IsPMF μ) (Z : ∀ j, Ω → B j)
    (Y : Ω → γ) : CondMutIndep μ Z Y ↔ CondMutIndepOn μ Z Y univ := by
  have key : ∀ y (z : ∀ j, B j), dist μ (pair Y (fun ω j => Z j ω)) (y, z) =
      dist μ (pair Y (blockRV Z univ)) (y, fun j : (univ : Finset κ) => z j) := by
    intro y z
    have hr : Function.Injective fun p : γ × (∀ j, B j) =>
        (p.1, fun j : (univ : Finset κ) => p.2 j) := by
      rintro ⟨y₁, w₁⟩ ⟨y₂, w₂⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (funext fun j => congrFun h.2 ⟨j, mem_univ j⟩)
    exact (dist_eq_of_injective μ _ hr (fun _ => rfl) (y, z)).symm
  simp only [CondMutIndep, CondMutIndepOn, condDist, card_univ]
  constructor
  · intro h y z
    by_cases hy : dist μ Y y = 0
    · rw [hy, zero_mul, dist_pair_eq_zero_of_left hμ _ _ hy, zero_mul]
    · have hz := h y hy z
      rw [prod_div_distrib, prod_const, card_univ,
        div_eq_div_iff hy (pow_ne_zero _ hy), key] at hz
      linear_combination hz
  · intro h y hy z
    rw [prod_div_distrib, prod_const, card_univ, div_eq_div_iff hy (pow_ne_zero _ hy), key]
    linear_combination h y z

variable [DecidableEq κ]

/-- Two vectors on `insert a s` that agree at `a` and on `s` are equal. -/
lemma eq_of_insert_restrict {a : κ} {s : Finset κ} {w w' : ∀ j : ↥(insert a s), B j}
    (h₁ : w ⟨a, mem_insert_self a s⟩ = w' ⟨a, mem_insert_self a s⟩)
    (h₂ : ∀ j : s, w ⟨j, mem_insert_of_mem j.property⟩ =
      w' ⟨j, mem_insert_of_mem j.property⟩) : w = w' := by
  funext ⟨j, hj⟩
  rcases mem_insert.1 hj with rfl | hj'
  · exact h₁
  · exact h₂ ⟨j, hj'⟩

/-- `p(y, z_{insert a s}) = p(zₐ, y, z_s)`. -/
lemma dist_pair_blockRV_insert (μ : Ω → ℝ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) (a : κ) (s : Finset κ)
    (y : γ) (z : ∀ j, B j) :
    dist μ (pair Y (blockRV Z (insert a s))) (y, fun j => z j) =
      dist μ (pair (Z a) (pair Y (blockRV Z s))) (z a, (y, fun j : s => z j)) := by
  have hr : Function.Injective fun p : γ × (∀ j : ↥(insert a s), B j) =>
      (p.2 ⟨a, mem_insert_self a s⟩,
        (p.1, fun j : s => p.2 ⟨j, mem_insert_of_mem j.property⟩)) := by
    rintro ⟨y₁, w₁⟩ ⟨y₂, w₂⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    exact Prod.ext h₂ (eq_of_insert_restrict h₁ fun j => congrFun h₃ j)
  exact (dist_eq_of_injective μ _ hr (fun _ => rfl) (y, fun j => z j)).symm

/-- **The induction step.** If `a ∉ s`, the subfamily on `insert a s` is mutually independent
conditioning on `Y` if and only if the subfamily on `s` is, and `Zₐ ⊥ Z_s | Y`. -/
theorem condMutIndepOn_insert_iff [∀ j, Finite (B j)] (hμ : IsPMF μ) (Z : ∀ j, Ω → B j)
    (Y : Ω → γ) {a : κ} {s : Finset κ} (ha : a ∉ s) :
    CondMutIndepOn μ Z Y (insert a s) ↔
      CondMutIndepOn μ Z Y s ∧ CondIndep μ (Z a) (blockRV Z s) Y := by
  have : ∀ j, Fintype (B j) := fun j => Fintype.ofFinite _
  have hne : ∀ j ∈ s, j ≠ a := fun j hj h => ha (h ▸ hj)
  rw [condIndep_iff_mul hμ]
  constructor
  · intro h
    have hs : CondMutIndepOn μ Z Y s := by
      intro y z
      have hsum : ∑ x : B a, dist μ (pair (Z a) (pair Y (blockRV Z s))) (x, (y, fun j : s => z j)) *
          dist μ Y y ^ (#s + 1) = ∑ x : B a, dist μ Y y * (dist μ (pair Y (Z a)) (y, x) *
            ∏ j ∈ s, dist μ (pair Y (Z j)) (y, z j)) := by
        refine sum_congr rfl fun x _ => ?_
        have hx := h y (Function.update z a x)
        rw [dist_pair_blockRV_insert, card_insert_of_notMem ha, prod_insert ha,
          Function.update_self] at hx
        have e₁ : (fun j : s => Function.update z a x j) = fun j : s => z j :=
          funext fun j => Function.update_of_ne (hne j j.property) _ _
        have e₂ : ∏ j ∈ s, dist μ (pair Y (Z j)) (y, Function.update z a x j) =
            ∏ j ∈ s, dist μ (pair Y (Z j)) (y, z j) :=
          prod_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
        rw [e₁, e₂] at hx
        exact hx
      rw [← sum_mul, ← mul_sum, ← sum_mul, sum_dist_pair_left, sum_dist_pair_right] at hsum
      by_cases hp : dist μ Y y = 0
      · rw [hp, dist_pair_eq_zero_of_left hμ _ _ hp, zero_mul, zero_mul]
      · exact mul_left_cancel₀ hp (by linear_combination hsum)
    refine ⟨hs, fun x y w => ?_⟩
    obtain ⟨ω₀⟩ : Nonempty Ω := by
      by_contra h0
      rw [not_nonempty_iff] at h0
      have := hμ.sum_eq_one
      simp at this
    set z : ∀ j, B j := Function.update (fun j => if hj : j ∈ s then w ⟨j, hj⟩ else Z j ω₀) a x
      with hz
    have hza : z a = x := Function.update_self _ _ _
    have hzs : (fun j : s => z j) = w := funext fun j => by
      simp [hz, Function.update_of_ne (hne j j.property), j.property]
    have h₁ := h y z
    rw [dist_pair_blockRV_insert, card_insert_of_notMem ha, prod_insert ha, hza, hzs] at h₁
    have h₂ := hs y z
    rw [hzs] at h₂
    rw [← dist_pair_swap μ (Z a) Y]
    by_cases hp : dist μ Y y = 0
    · rw [hp, mul_zero, dist_pair_eq_zero_of_left hμ _ _ hp, zero_mul]
    · refine mul_right_cancel₀ (pow_ne_zero #s hp) ?_
      linear_combination h₁ - dist μ (pair Y (Z a)) (y, x) * h₂
  · rintro ⟨hs, hci⟩ y z
    rw [dist_pair_blockRV_insert, card_insert_of_notMem ha, prod_insert ha]
    have h₁ := hci (z a) y (fun j => z j)
    have h₂ := hs y z
    rw [← dist_pair_swap μ (Z a) Y] at h₁
    linear_combination dist μ Y y ^ #s * h₁ + dist μ (pair Y (Z a)) (y, z a) * h₂

variable [Fintype γ] [∀ j, Fintype (B j)]

/-- The chain rule `H(Z_{insert a s} | Y) = H(Z_s | Y) + H(Zₐ | Z_s, Y)`. -/
theorem condEntropy_blockRV_insert (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) (a : κ)
    (s : Finset κ) :
    H[blockRV Z (insert a s) | Y ; μ] =
      H[blockRV Z s | Y ; μ] + H[Z a | pair (blockRV Z s) Y ; μ] := by
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ,
    entropyRV_pair_comm μ (blockRV Z s) Y]
  have hf : Function.Injective fun p : γ × (∀ j : ↥(insert a s), B j) =>
      ((fun j : s => p.2 ⟨j, mem_insert_of_mem j.property⟩, p.1),
        p.2 ⟨a, mem_insert_self a s⟩) := by
    rintro ⟨y₁, w₁⟩ ⟨y₂, w₂⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
    exact Prod.ext h₂ (eq_of_insert_restrict h₃ fun j => congrFun h₁ j)
  have e := entropyRV_eq_of_injective μ _ hf (X := pair Y (blockRV Z (insert a s)))
    (Y := pair (pair (blockRV Z s) Y) (Z a)) fun _ => rfl
  rw [← e]
  ring

lemma condEntropy_blockRV_empty (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) :
    H[blockRV Z ∅ | Y ; μ] = 0 := by
  rw [condEntropy_eq_sub hμ, sub_eq_zero]
  exact entropyRV_eq_of_injective μ (fun y => (y, fun j : (∅ : Finset κ) => isEmptyElim j))
    (fun _ _ h => (Prod.mk.inj h).1) fun ω => Prod.ext rfl (funext fun j => isEmptyElim j)

lemma condEntropy_blockRV_singleton (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) (a : κ) :
    H[blockRV Z {a} | Y ; μ] = H[Z a | Y ; μ] := by
  rw [← insert_empty, condEntropy_blockRV_insert hμ, condEntropy_blockRV_empty hμ, zero_add]
  exact condEntropy_congr_right hμ (Z a) (fun y => (fun j : (∅ : Finset κ) => isEmptyElim j, y))
    (fun _ _ h => (Prod.mk.inj h).2) fun ω => Prod.ext (funext fun j => isEmptyElim j) rfl

/-- Conditioning on more of the family reduces the conditional entropy. -/
lemma condEntropy_pair_blockRV_anti (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) {β : Type*}
    [Fintype β] (X : Ω → β) {s t : Finset κ} (hst : s ⊆ t) :
    H[X | pair (blockRV Z t) Y ; μ] ≤ H[X | pair (blockRV Z s) Y ; μ] :=
  condEntropy_le_condEntropy_comp hμ X (pair (blockRV Z t) Y)
    (fun p => (fun j : s => p.1 ⟨j, hst j.property⟩, p.2))

/-- `I(Zₐ; Z_s | Y)` grows with `s`. -/
lemma condMutualInfo_blockRV_mono (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) {β : Type*}
    [Fintype β] (X : Ω → β) {s t : Finset κ} (hst : s ⊆ t) :
    I[X : blockRV Z s | Y ; μ] ≤ I[X : blockRV Z t | Y ; μ] := by
  simp only [condMutualInfo]
  linarith [condEntropy_pair_blockRV_anti hμ Z Y X hst]

/-- `H(Z_s | Y) ≤ ∑_{j ∈ s} H(Zⱼ | Y)`, with equality if and only if the `Zⱼ`, `j ∈ s`, are
mutually independent conditioning on `Y`. -/
theorem condEntropy_blockRV_le_sum (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ)
    (s : Finset κ) :
    H[blockRV Z s | Y ; μ] ≤ ∑ j ∈ s, H[Z j | Y ; μ] ∧
      (CondMutIndepOn μ Z Y s ↔ H[blockRV Z s | Y ; μ] = ∑ j ∈ s, H[Z j | Y ; μ]) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [condEntropy_blockRV_empty hμ, sum_empty]
    exact ⟨le_rfl, iff_of_true (condMutIndepOn_empty Z Y) rfl⟩
  | insert a s ha ih =>
    have e := condEntropy_blockRV_insert hμ Z Y a s
    have hI : I[Z a : blockRV Z s | Y ; μ] =
        H[Z a | Y ; μ] - H[Z a | pair (blockRV Z s) Y ; μ] := rfl
    have hI0 := condMutualInfo_nonneg hμ (Z a) (blockRV Z s) Y
    rw [sum_insert ha, condMutIndepOn_insert_iff hμ Z Y ha, ih.2, e,
      ← condMutualInfo_eq_zero_iff hμ]
    refine ⟨by linarith [ih.1], ⟨fun h => by linarith [h.1, h.2], fun h => ?_⟩⟩
    constructor <;> linarith [ih.1]

variable [Fintype κ]

lemma condEntropy_eq_condEntropy_blockRV_univ (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) :
    H[fun ω j => Z j ω | Y ; μ] = H[blockRV Z univ | Y ; μ] :=
  (condEntropy_congr_left hμ (Y := fun ω j => Z j ω) (Y' := blockRV Z univ) Y
    (fun (v : ∀ j, B j) (j : (univ : Finset κ)) => v j)
    (fun _ _ h => funext fun j => congrFun h ⟨j, mem_univ j⟩) fun _ => rfl).symm

/-- **Theorem 12.2.** `Z₁, …, Zₙ` are mutually independent conditioning on `Y` if and only if
`H(Z₁, …, Zₙ | Y) = ∑ᵢ H(Zᵢ | Y)` (12.15). -/
theorem condMutIndep_iff_condEntropy_eq_sum (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) :
    CondMutIndep μ Z Y ↔ H[fun ω j => Z j ω | Y ; μ] = ∑ j, H[Z j | Y ; μ] := by
  rw [condMutIndep_iff_condMutIndepOn_univ hμ, condEntropy_eq_condEntropy_blockRV_univ hμ]
  exact (condEntropy_blockRV_le_sum hμ Z Y univ).2

/-- **Theorem 12.3.** `Z₁, …, Zₙ` are mutually independent conditioning on `Y` if and only if
`I(Zᵢ; Zⱼ, j ≠ i | Y) = 0` for all `i` (12.16). -/
theorem condMutIndep_iff_condMutualInfo_eq_zero (hμ : IsPMF μ) (Z : ∀ j, Ω → B j) (Y : Ω → γ) :
    CondMutIndep μ Z Y ↔ ∀ i, I[Z i : blockRV Z (univ.erase i) | Y ; μ] = 0 := by
  constructor
  · intro h i
    have h₁ := (condMutIndep_iff_condEntropy_eq_sum hμ Z Y).1 h
    rw [condEntropy_eq_condEntropy_blockRV_univ hμ, ← insert_erase (mem_univ i),
      condEntropy_blockRV_insert hμ, insert_erase (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
      at h₁
    have h₂ := (condEntropy_blockRV_le_sum hμ Z Y (univ.erase i)).1
    have hI : I[Z i : blockRV Z (univ.erase i) | Y ; μ] =
        H[Z i | Y ; μ] - H[Z i | pair (blockRV Z (univ.erase i)) Y ; μ] := rfl
    linarith [condMutualInfo_nonneg hμ (Z i) (blockRV Z (univ.erase i)) Y]
  · intro h
    rw [condMutIndep_iff_condMutIndepOn_univ hμ]
    suffices ∀ s : Finset κ, CondMutIndepOn μ Z Y s from this univ
    intro s
    induction s using Finset.induction_on with
    | empty => exact condMutIndepOn_empty Z Y
    | insert a s ha ih =>
      refine (condMutIndepOn_insert_iff hμ Z Y ha).2 ⟨ih, ?_⟩
      rw [← condMutualInfo_eq_zero_iff hμ]
      have hle := condMutualInfo_blockRV_mono hμ Z Y (Z a)
        (fun j hj => mem_erase.2 ⟨fun h' => ha (h' ▸ hj), mem_univ j⟩ : s ⊆ univ.erase a)
      linarith [h a, condMutualInfo_nonneg hμ (Z a) (blockRV Z s) Y]

omit [Fintype γ] [∀ j, Fintype (B j)] in
/-- **Theorem 12.3**, with conditional independencies: `Zᵢ ⊥ (Zⱼ, j ≠ i) | Y` for all `i`. -/
theorem condMutIndep_iff_condIndep [Finite γ] [∀ j, Finite (B j)] (hμ : IsPMF μ)
    (Z : ∀ j, Ω → B j) (Y : Ω → γ) :
    CondMutIndep μ Z Y ↔ ∀ i, CondIndep μ (Z i) (blockRV Z (univ.erase i)) Y := by
  have := Fintype.ofFinite γ
  have : ∀ j, Fintype (B j) := fun j => Fintype.ofFinite _
  rw [condMutIndep_iff_condMutualInfo_eq_zero hμ]
  exact forall_congr' fun i => condMutualInfo_eq_zero_iff hμ _ _ _

/-- **Theorem 12.4.** `Z₁, …, Zₙ` are mutually independent conditioning on `Y` if and only if
`H(Z₁, …, Zₙ | Y) = ∑ᵢ H(Zᵢ | Y, Zⱼ, j ≠ i)` (12.20). -/
theorem condMutIndep_iff_condEntropy_eq_sum_condEntropy (hμ : IsPMF μ) (Z : ∀ j, Ω → B j)
    (Y : Ω → γ) : CondMutIndep μ Z Y ↔
      H[fun ω j => Z j ω | Y ; μ] = ∑ i, H[Z i | pair (blockRV Z (univ.erase i)) Y ; μ] := by
  set d : κ → ℝ := fun i => H[Z i | pair (blockRV Z (univ.erase i)) Y ; μ] with hd
  rw [condEntropy_eq_condEntropy_blockRV_univ hμ]
  constructor
  · intro h
    have h₁ := (condMutIndep_iff_condEntropy_eq_sum hμ Z Y).1 h
    rw [condEntropy_eq_condEntropy_blockRV_univ hμ] at h₁
    rw [h₁]
    refine sum_congr rfl fun i _ => ?_
    have h₂ := (condMutIndep_iff_condMutualInfo_eq_zero hμ Z Y).1 h i
    simp only [condMutualInfo] at h₂
    linarith
  · intro h
    -- (12.22)–(12.25): each step of the chain rule is at least the corresponding `d i`
    have key : ∀ u s : Finset κ, Disjoint s u →
        H[blockRV Z s | Y ; μ] + ∑ j ∈ u, d j ≤ H[blockRV Z (s ∪ u) | Y ; μ] := by
      intro u
      induction u using Finset.induction_on with
      | empty => intro s _; rw [sum_empty, union_empty, add_zero]
      | insert a u ha ih =>
        intro s hsu
        have has : a ∉ s ∪ u := by
          rw [mem_union, not_or]
          exact ⟨fun h' => disjoint_left.1 hsu h' (mem_insert_self a u), ha⟩
        have h₁ := ih s (disjoint_of_subset_right (subset_insert a u) hsu)
        rw [sum_insert ha, union_insert, condEntropy_blockRV_insert hμ]
        have h₂ : d a ≤ H[Z a | pair (blockRV Z (s ∪ u)) Y ; μ] :=
          condEntropy_pair_blockRV_anti hμ Z Y (Z a)
            (fun j hj => mem_erase.2 ⟨fun h' => has (h' ▸ hj), mem_univ j⟩)
        linarith
    rw [condMutIndep_iff_condMutualInfo_eq_zero hμ]
    intro i
    have h₁ := key {i} ∅ (disjoint_empty_left _)
    have h₂ := key (univ.erase i) {i} (disjoint_singleton_left.2 (notMem_erase i univ))
    rw [empty_union, condEntropy_blockRV_empty hμ, sum_singleton, zero_add,
      condEntropy_blockRV_singleton hμ] at h₁
    rw [singleton_union, insert_erase (mem_univ i), h, ← add_sum_erase _ _ (mem_univ i),
      condEntropy_blockRV_singleton hμ] at h₂
    have hI : I[Z i : blockRV Z (univ.erase i) | Y ; μ] = H[Z i | Y ; μ] - d i := rfl
    linarith

end InfoTheory
