/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeySpecialCases

/-!
# Secret key agreement with many nodes: definitions

Theorem 9 of Lecture 23 of El Gamal and Kim. There are `N ≥ 2` nodes, node `j` observes `(Xⱼⁿ, Zⁿ)`,
and the eavesdropper observes `Zⁿ`. The secret key capacity is `H(X^N | Z) - R_CFO([1 : N] | Z)`,
where `R_CFO` is the minimum sum rate of communication for omniscience when all the nodes know `Z`.

## Main definitions

* `zCondH p S`: `H(X(S) | X(Sᶜ), Z)`.
* `zRegion p`, `rCFOZ p`: the region and the minimum sum rate of communication for omniscience.
* `MultiKeyCode`, `IsAchievableMultiKey`, `multiKeyCapacity`: the secret key capacity, in bits.

## Main statements

* `swCondH_zTuple`: the conditional entropies are those of Lecture 21 for the sources `(Xⱼ, Z)`.
* `condEntropy_runTo`, `condEntropy_viewB_eq_sum`: the chain rules along the rounds and the nodes.
* `condEntropy_viewB_compl`: `H(A(S) | A(Sᶜ), Zⁿ) = n H(X(S) | X(Sᶜ), Z) + ∑_{j ∈ S} H(Wⱼ)`.

## Implementation notes

The notes give the proof without randomization, and say that the same steps apply with `(Xⱼⁿ, Wⱼ)`
as the observation of node `j`. The entropy of the private random variables then has to be
subtracted from the rates `R'ⱼ`, which we do.

With `N = 1` and private randomness the theorem fails, since node `1` can draw any key: the theorem
needs two nodes. So we assume `N ≥ 2`.

We keep a part of a tuple as a tuple of `Option`s, which is `maskL`, so that all the parts have the
same type.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Random variables that determine each other -/

section Mutual

variable {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]

/-- Two random variables that are functions of each other have the same entropy. -/
lemma entropyRV_eq_of_mutual {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → a} {Y : Ω → b} (f : a → b)
    (g : b → a) (hf : Y = f ∘ X) (hg : X = g ∘ Y) : H[Y ; μ] = H[X ; μ] := by
  refine le_antisymm ?_ ?_
  · have := entropyRV_comp_le hμ X f
    rwa [← hf] at this
  · have := entropyRV_comp_le hμ Y g
    rwa [← hg] at this

/-- Two random variables that are functions of each other have the same conditional entropy. -/
lemma condEntropy_eq_of_mutual {μ : Ω → ℝ} (hμ : IsPMF μ) {X : Ω → a} {Y : Ω → b} (C : Ω → c)
    (f : a → b) (g : b → a) (hf : Y = f ∘ X) (hg : X = g ∘ Y) : H[Y | C ; μ] = H[X | C ; μ] := by
  refine le_antisymm ?_ ?_
  · have := condEntropy_comp_le hμ X C f
    rwa [← hf] at this
  · have := condEntropy_comp_le hμ Y C g
    rwa [← hg] at this

end Mutual

/-! ### Parts of tuples -/

section Mask

variable {N : ℕ} {β : Fin N → Type*}

/-- The part of a tuple on the set `S`. -/
def maskL (S : Finset (Fin N)) (x : ∀ j, β j) : ∀ j, Option (β j) :=
  fun j => if j ∈ S then some (x j) else none

/-- The tuple from its part on the set `S`, with default values. -/
def unmaskL (d : ∀ j, β j) (v : ∀ j, Option (β j)) : ∀ j, β j := fun j => (v j).getD (d j)

lemma unmaskL_maskL (d x : ∀ j, β j) (j : Fin N) {S : Finset (Fin N)} (h : j ∈ S) :
    unmaskL d (maskL S x) j = x j := by
  simp [unmaskL, maskL, h]

lemma maskL_insert [DecidableEq (Fin N)] (S : Finset (Fin N)) (j : Fin N) (x : ∀ j, β j) :
    maskL (insert j S) x = Function.update (maskL S x) j (some (x j)) := by
  funext i
  by_cases h : i = j
  · subst h
    simp [maskL]
  · simp [maskL, h]

lemma maskL_empty (x : ∀ j, β j) : maskL ∅ x = fun _ => none := by
  funext j
  simp [maskL]

/-- The part on a set from the part on a larger set. -/
def restrictMask (S : Finset (Fin N)) (v : ∀ j, Option (β j)) : ∀ j, Option (β j) :=
  fun j => if j ∈ S then v j else none

lemma restrictMask_maskL {S D : Finset (Fin N)} (h : S ⊆ D) (x : ∀ j, β j) :
    restrictMask S (maskL D x) = maskL S x := by
  funext j
  by_cases hj : j ∈ S
  · simp [restrictMask, maskL, hj, h hj]
  · simp [restrictMask, maskL, hj]

/-- The part on `S ∪ D` from the parts on `S` and `D`. -/
def unionMask (S : Finset (Fin N)) (v w : ∀ j, Option (β j)) : ∀ j, Option (β j) :=
  fun j => if j ∈ S then v j else w j

lemma unionMask_maskL (S D : Finset (Fin N)) (x : ∀ j, β j) :
    unionMask S (maskL S x) (maskL D x) = maskL (S ∪ D) x := by
  funext j
  by_cases hj : j ∈ S
  · simp [unionMask, maskL, hj]
  · by_cases hd : j ∈ D <;> simp [unionMask, maskL, hj, hd]

end Mask

/-! ### Independent private random variables -/

section Seeds

variable {N : ℕ} {κ : Fin N → Type*} [∀ j, Fintype (κ j)]

/-- The law of independent random variables, one for each node. -/
def seedsLaw (θ : ∀ j, κ j → ℝ) (w : ∀ j, κ j) : ℝ := ∏ j, θ j (w j)

variable {θ : ∀ j, κ j → ℝ}

lemma seedsLaw_isPMF (hθ : ∀ j, IsPMF (θ j)) : IsPMF (seedsLaw θ) := by
  refine ⟨fun w => prod_nonneg fun j _ => (hθ j).nonneg _, ?_⟩
  simp only [seedsLaw]
  rw [← Fintype.prod_sum fun j a => θ j a]
  simp [(hθ _).sum_eq_one]

/-- **Independent coordinates.** If `F` does not depend on the coordinate `j`, then
`E F(W) g(Wⱼ) = E F(W) · E g(Wⱼ)`. -/
lemma sum_seedsLaw_mul_coord (hθ : ∀ j, IsPMF (θ j)) (j : Fin N) {F : (∀ j, κ j) → ℝ}
    (hF : ∀ w a, F (Function.update w j a) = F w) (g : κ j → ℝ) :
    ∑ w, seedsLaw θ w * (F w * g (w j)) = (∑ w, seedsLaw θ w * F w) * ∑ a, θ j a * g a := by
  classical
  set Φ : (∀ j, κ j) × κ j → (∀ j, κ j) × κ j := fun z => (Function.update z.1 j z.2, z.1 j)
  have hΦ : Function.Involutive Φ := fun z => by
    simp [Φ]
  have hext : ∀ w a, seedsLaw θ (Function.update w j a) * θ j (w j) = seedsLaw θ w * θ j a := by
    intro w a
    simp only [seedsLaw]
    rw [← mul_prod_erase univ _ (mem_univ j),
      ← mul_prod_erase univ (fun i => θ i (w i)) (mem_univ j)]
    have e : ∏ i ∈ univ.erase j, θ i (Function.update w j a i) =
        ∏ i ∈ univ.erase j, θ i (w i) :=
      prod_congr rfl fun i hi => by rw [Function.update_of_ne (mem_erase.1 hi).1]
    rw [e, Function.update_self]
    ring
  have h := Equiv.sum_comp (hΦ.toPerm)
    (fun z : (∀ j, κ j) × κ j => seedsLaw θ z.1 * (F z.1 * g (z.1 j)) * θ j z.2)
  have hL : ∑ z : (∀ j, κ j) × κ j, seedsLaw θ z.1 * (F z.1 * g (z.1 j)) * θ j z.2 =
      ∑ w, seedsLaw θ w * (F w * g (w j)) := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, (hθ j).sum_eq_one, mul_one]
  have hR : ∑ z : (∀ j, κ j) × κ j, seedsLaw θ (Φ z).1 * (F (Φ z).1 * g ((Φ z).1 j)) *
      θ j (Φ z).2 = (∑ w, seedsLaw θ w * F w) * ∑ a, θ j a * g a := by
    rw [Fintype.sum_prod_type, sum_mul]
    refine sum_congr rfl fun w _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [Φ, hF, Function.update_self]
    have := hext w a
    linear_combination (F w * g a) * this
  rw [← hL, ← hR]
  exact h.symm

/-- The entropy of the part of the private random variables on `S` is the sum of the entropies. -/
theorem entropy_maskL_seedsLaw (hθ : ∀ j, IsPMF (θ j)) (S : Finset (Fin N)) :
    H[maskL S ; seedsLaw θ] = ∑ j ∈ S, entropy (θ j) := by
  classical
  have hμ := seedsLaw_isPMF hθ
  have hone : ∀ j, dist (seedsLaw θ) (fun w => w j) = θ j := fun j => by
    funext a
    have h₁ := sum_seedsLaw_mul_coord hθ j (F := fun _ => 1) (fun _ _ => rfl)
      (fun b => if b = a then (1 : ℝ) else 0)
    simp only [one_mul, mul_one, hμ.sum_eq_one] at h₁
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h₁
    exact h₁
  induction S using Finset.induction_on with
  | empty =>
    have hc : maskL (∅ : Finset (Fin N)) = fun _ : (∀ j, κ j) => fun _ => none := by
      funext w
      exact maskL_empty w
    rw [hc, entropyRV_const hμ]
    simp
  | insert j S hj ih =>
    rw [sum_insert hj, ← ih]
    have e₁ : H[maskL (insert j S) ; seedsLaw θ] = H[pair (fun w => w j) (maskL S) ; seedsLaw θ] :=
      by
      obtain ⟨d⟩ : Nonempty (∀ j, κ j) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)
      exact entropyRV_eq_of_mutual hμ (fun v => Function.update v.2 j (some v.1))
        (fun v => ((v j).getD (d j), restrictMask S v))
        (funext fun w => maskL_insert S j w)
        (funext fun w => Prod.ext (by simp [maskL]) (restrictMask_maskL (subset_insert j S) w).symm)
    have hI : I[(fun w : ∀ j, κ j => w j) : maskL S ; seedsLaw θ] = 0 := by
      rw [mutualInfo_eq_zero_iff hμ]
      intro a v
      have hF := sum_seedsLaw_mul_coord hθ j (F := fun w => if maskL S w = v then (1 : ℝ) else 0)
        (fun w b => by
          have : maskL S (Function.update w j b) = maskL S w := by
            funext i
            by_cases hi : i ∈ S
            · have hne : i ≠ j := fun h => hj (h ▸ hi)
              simp [maskL, hi, Function.update_of_ne hne]
            · simp [maskL, hi]
          rw [this]) (fun b => if b = a then (1 : ℝ) else 0)
      have hg : ∑ b, θ j b * (if b = a then (1 : ℝ) else 0) = θ j a := by simp
      rw [hg] at hF
      have h₁ : dist (seedsLaw θ) (pair (fun w => w j) (maskL S)) (a, v) =
          ∑ w, seedsLaw θ w * ((if maskL S w = v then (1 : ℝ) else 0) *
            if w j = a then (1 : ℝ) else 0) := by
        simp only [dist, pair, Prod.mk.injEq]
        refine sum_congr rfl fun w _ => ?_
        by_cases h₂ : w j = a <;> by_cases h₃ : maskL S w = v <;> simp [h₂, h₃]
      have h₂ : dist (seedsLaw θ) (maskL S) v =
          ∑ w, seedsLaw θ w * if maskL S w = v then (1 : ℝ) else 0 := by
        simp only [dist]
        refine sum_congr rfl fun w _ => ?_
        by_cases h₃ : maskL S w = v <;> simp [h₃]
      rw [h₁, h₂, hF, hone j]
      ring
    have hsum := mutualInfo_eq_add_sub hμ (fun w : ∀ j, κ j => w j) (maskL S)
    rw [hI] at hsum
    have e₂ : H[(fun w : ∀ j, κ j => w j) ; seedsLaw θ] = entropy (θ j) := by
      rw [entropyRV, hone j]
    linarith

end Seeds

/-! ### The chain rule along a protocol -/

section Rounds

variable {Ω 𝒟 : Type*} [Fintype Ω] [Fintype 𝒟] {r : ℕ} {M : Fin r → ℕ} [∀ l, NeZero (M l)]
  {μ : Ω → ℝ}

instance instNonemptyFinNeZero : ∀ l, Nonempty (Fin (M l)) := fun _ => ⟨0⟩

/-- **The chain rule for the indices.** `H(Mᵐ | D) = ∑_{l < m} H(M_l | M^{l-1}, D)`. -/
theorem condEntropy_runTo (hμ : IsPMF μ) (g : Ω → ∀ l, (∀ l', Fin (M l')) → Fin (M l))
    (D : Ω → 𝒟) (m : ℕ) (hm : m ≤ r) :
    H[fun ω => runTo (g ω) m | D ; μ] = ∑ l : Fin r, if (l : ℕ) < m then
      H[fun ω => g ω l (runTo (g ω) l) | pair (fun ω => runTo (g ω) l) D ; μ] else 0 := by
  classical
  induction m with
  | zero =>
    have h₀ : H[fun ω => runTo (g ω) 0 | D ; μ] = 0 :=
      (condEntropy_eq_zero_iff hμ _ _).2 ⟨fun _ => fun _ => Classical.arbitrary _, fun _ _ => rfl⟩
    rw [h₀]
    simp
  | succ m ih =>
    have hlt : m < r := hm
    set l : Fin r := ⟨m, hlt⟩ with hl
    set Hist := fun ω => runTo (g ω) m with hHist
    set Mn : Ω → Fin (M l) := fun ω => g ω l (Hist ω) with hMn
    have h₁ : H[fun ω => runTo (g ω) (m + 1) | D ; μ] = H[pair Hist Mn | D ; μ] := by
      refine condEntropy_eq_of_mutual hμ D (fun w => Function.update w.1 l w.2)
        (fun w => (Function.update w l (Classical.arbitrary _), w l)) ?_ ?_
      · funext ω
        exact runTo_succ_comm g m hlt ω
      · funext ω
        have e := runTo_succ_comm g m hlt ω
        refine Prod.ext ?_ ?_
        · change Hist ω = Function.update (runTo (g ω) (m + 1)) l (Classical.arbitrary _)
          rw [e]
          funext l'
          by_cases hl' : l' = l
          · subst hl'
            rw [Function.update_self]
            exact runTo_of_le (g ω) (le_refl m)
          · rw [Function.update_of_ne hl', Function.update_of_ne hl']
        · change Mn ω = runTo (g ω) (m + 1) l
          rw [e, Function.update_self]
    rw [h₁, chain_rule_cond hμ, ih (by omega)]
    have h₂ : ∀ l' : Fin r, (if (l' : ℕ) < m + 1 then
        H[fun ω => g ω l' (runTo (g ω) l') | pair (fun ω => runTo (g ω) l') D ; μ] else 0) =
        (if (l' : ℕ) < m then
          H[fun ω => g ω l' (runTo (g ω) l') | pair (fun ω => runTo (g ω) l') D ; μ] else 0) +
        (if l' = l then
          H[fun ω => g ω l' (runTo (g ω) l') | pair (fun ω => runTo (g ω) l') D ; μ] else 0) := by
      intro l'
      by_cases h₃ : (l' : ℕ) < m
      · have h₄ : l' ≠ l := fun he => by
          rw [he] at h₃
          exact lt_irrefl _ h₃
        simp [h₃, h₄, Nat.lt_succ_of_lt h₃]
      · by_cases h₄ : l' = l
        · subst h₄
          simp [hl]
        · have h₅ : ¬ (l' : ℕ) < m + 1 := fun h₆ => h₄ (Fin.ext (by
            simp only [hl]
            omega))
          simp [h₃, h₄, h₅]
    simp only [h₂, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    rfl

end Rounds

/-! ### The region -/

section Region

variable {N : ℕ} {α : Fin N → Type*} [∀ j, Fintype (α j)] {γ : Type*} [Fintype γ]

/-- A letter of the sources `X^N` and of `Z`. -/
abbrev mLetter (α : Fin N → Type*) (γ : Type*) := (∀ j, α j) × γ

/-- **Theorem 9 of Lecture 23 of [elgamal2010].** `H(X(S) | X(Sᶜ), Z)`. -/
def zCondH (p : mLetter α γ → ℝ) (S : Finset (Fin N)) : ℝ :=
  H[fun a => maskL S a.1 | fun a => (maskL Sᶜ a.1, a.2) ; p]

/-- **Lecture 21 and page 23-54 of [elgamal2010].** The region of communication for omniscience when
all the nodes know `Z`, in bits: `∑_{j ∈ S} Rⱼ ≥ H(X(S) | X(Sᶜ), Z)` for every proper subset `S`. -/
def zRegion (p : mLetter α γ → ℝ) : Set (Fin N → ℝ) :=
  {R | (∀ j, 0 ≤ R j) ∧ ∀ S : Finset (Fin N), S ≠ univ → zCondH p S / log 2 ≤ ∑ j ∈ S, R j}

/-- **Page 23-54 of [elgamal2010].** The rate `R_CFO([1 : N] | Z)`, in bits. -/
def rCFOZ (p : mLetter α γ → ℝ) : ℝ := sInf ((fun R : Fin N → ℝ => ∑ j, R j) '' zRegion p)

/-- The sources `(Xⱼ, Z)` of communication for omniscience, in which all the nodes know `Z`. -/
def zTuple (p : mLetter α γ → ℝ) : (∀ j, α j × γ) → ℝ := dist p fun a j => (a.1 j, a.2)

/-- For a proper subset `S`, `H(X(S), Z | X(Sᶜ), Z) = H(X(S) | X(Sᶜ), Z)`: the conditional entropy
of Lecture 21 for the sources `(Xⱼ, Z)` is `zCondH`. -/
theorem swCondH_zTuple {p : mLetter α γ → ℝ} (hp : IsPMF p) {S : Finset (Fin N)} (hS : S ≠ univ) :
    swCondH (zTuple p) S = zCondH p S := by
  classical
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (univ : Finset (Fin N)), k ∉ S := by
    by_contra h
    push Not at h
    exact hS (eq_univ_of_forall fun j => h j (mem_univ j))
  obtain ⟨a₀⟩ : Nonempty (mLetter α γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  set Γ : mLetter α γ → ∀ j, α j × γ := fun a j => (a.1 j, a.2) with hΓ
  have h₁ : swCondH (zTuple p) S = H[swPart S ∘ Γ | swRest S ∘ Γ ; p] :=
    (condEntropy_comp_of_dist hp Γ (swPart S) (swRest S)).symm
  rw [h₁, zCondH]
  set Dz : mLetter α γ → (∀ j, Option (α j)) × γ := fun a => (maskL Sᶜ a.1, a.2) with hDz
  -- The conditioning random variables determine each other.
  have hC : H[swPart S ∘ Γ | swRest S ∘ Γ ; p] = H[swPart S ∘ Γ | Dz ; p] := by
    refine condEntropy_eq_of_comp hp _
      (fun w => (fun j => if h : j ∈ Sᶜ then some (w ⟨j, by simpa using h⟩).1 else none,
        (w ⟨k, hk⟩).2))
      (fun w j => ((w.1 j).getD (a₀.1 j), w.2)) ?_ ?_
    · funext a
      refine Prod.ext (funext fun j => ?_) rfl
      by_cases hj : j ∈ S
      · have hj' : j ∉ Sᶜ := by simpa using hj
        simp [hDz, maskL, hj', hj]
      · have hj' : j ∈ Sᶜ := by simpa using hj
        simp [hDz, maskL, hj', hj, swRest, hΓ]
    · funext a
      funext j
      have hj : (j : Fin N) ∈ Sᶜ := by simpa using j.2
      simp [hDz, maskL, hj, swRest, hΓ]
  rw [hC]
  -- `Z` is known from the condition.
  set B : mLetter α γ → ∀ j, Option (α j) := fun a => maskL S a.1 with hB
  have hle₁ : H[swPart S ∘ Γ | Dz ; p] ≤ H[pair B Prod.snd | Dz ; p] := by
    have h := condEntropy_comp_le hp (pair B Prod.snd) Dz
      (fun w (j : S) => ((w.1 j).getD (a₀.1 j), w.2))
    refine le_trans (le_of_eq ?_) h
    congr 1
    funext a
    funext j
    simp [hB, maskL, hΓ, swPart]
  have hle₂ : H[B | Dz ; p] ≤ H[swPart S ∘ Γ | Dz ; p] := by
    have h := condEntropy_comp_le hp (swPart S ∘ Γ) Dz
      (fun w j => if h : j ∈ S then some (w ⟨j, h⟩).1 else none)
    refine le_trans (le_of_eq ?_) h
    congr 1
  have h₀ : H[Prod.snd | pair B Dz ; p] = 0 :=
    (condEntropy_eq_zero_iff hp _ _).2 ⟨fun w => w.2.2, fun _ _ => rfl⟩
  have h₂ := chain_rule_cond hp B Prod.snd Dz
  rw [h₀, add_zero] at h₂
  exact le_antisymm (hle₁.trans (le_of_eq h₂)) hle₂

end Region

/-! ### Codes -/

section Code

variable {N : ℕ} {α : Fin N → Type*} [∀ j, Fintype (α j)] {γ : Type*} [Fintype γ]

/-- **Lecture 23 of [elgamal2010], page 23-52.** A protocol for secret key agreement between `N`
nodes with the observations `a j`. In the round `l` the node `spk l` broadcasts one of `M l`
indices, a function of its observation and of the previous indices. Each node generates a key from
its observation and the indices. -/
structure MultiKeyCode {r : ℕ} (spk : Fin r → Fin N) (M : Fin r → ℕ) (K : ℕ)
    (a : Fin N → Type*) where
  /-- The index of the round `l`. -/
  enc : ∀ l, a (spk l) → (∀ l', Fin (M l')) → Fin (M l)
  /-- The key of the node `j`. -/
  key : ∀ j, a j → (∀ l', Fin (M l')) → Fin K

variable {r : ℕ} {spk : Fin r → Fin N} {M : Fin r → ℕ} [∀ l, NeZero (M l)] {K n : ℕ}
  {κ : Fin N → Type*} [∀ j, Fintype (κ j)]

/-- The observation of the node `j`: `(Xⱼⁿ, Zⁿ, Wⱼ)`. -/
abbrev mObs (α : Fin N → Type*) (γ : Type*) (κ : Fin N → Type*) (n : ℕ) (j : Fin N) :=
  (Fin n → α j) × (Fin n → γ) × κ j

/-- The block of the source and of the private random variables. -/
abbrev mBlock (α : Fin N → Type*) (γ : Type*) (κ : Fin N → Type*) (n : ℕ) :=
  (Fin n → mLetter α γ) × ∀ j, κ j

/-- The observation of the node `j`, on the block. -/
def nodeObs (j : Fin N) (w : mBlock α γ κ n) : mObs α γ κ n j :=
  (fun i => (w.1 i).1 j, fun i => (w.1 i).2, w.2 j)

/-- The sequence `Zⁿ`, on the block. -/
def eveM (w : mBlock α γ κ n) : Fin n → γ := fun i => (w.1 i).2

namespace MultiKeyCode

variable (c : MultiKeyCode spk M K (mObs α γ κ n))

/-- The protocol on the block. -/
def protocolB (w : mBlock α γ κ n) (l : Fin r) (h : ∀ l', Fin (M l')) : Fin (M l) :=
  c.enc l (nodeObs (spk l) w) h

/-- The transcript `Mᵠ`, on the block. -/
def transB (w : mBlock α γ κ n) : ∀ l, Fin (M l) := run (c.protocolB w)

/-- The key of the node `j`, on the block. -/
def keyB (j : Fin N) (w : mBlock α γ κ n) : Fin K := c.key j (nodeObs j w) (c.transB w)

open Classical in
/-- **Page 23-52 of [elgamal2010].** The probability of error `1 - P{K₁ = ⋯ = K_N}`, for the law of
the block. -/
def errProbB (μ : mBlock α γ κ n → ℝ) : ℝ :=
  ∑ w, μ w * if ∃ j j', c.keyB j w ≠ c.keyB j' w then 1 else 0

end MultiKeyCode

/-- **Pages 23-52 and 23-53 of [elgamal2010].** A secret key rate `R`, in bits, is achievable if for
every `ε` and all large `n` there is a protocol with keys in `[1 : 2 ^ ⌈nR⌉]`, with probability of
error at most `ε`, leakage rates `(1/n) I(Kⱼ; Zⁿ, Mᵠ)` at most `ε`, and `H(Kⱼ) ≥ n (R - ε)`. -/
def IsAchievableMultiKey (p : mLetter α γ → ℝ) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (r : ℕ) (spk : Fin r → Fin N) (M : Fin r → ℕ)
    (_ : ∀ l, NeZero (M l)) (κ : Fin N → Type) (_ : ∀ j, Fintype (κ j)) (θ : ∀ j, κ j → ℝ)
    (c : MultiKeyCode spk M (2 ^ ⌈n * R⌉₊) (mObs α γ κ n)), (∀ j, IsPMF (θ j)) ∧
      c.errProbB (secBlockLaw p (seedsLaw θ) n) ≤ ε ∧
      (∀ j, I[c.keyB j : pair eveM c.transB ; secBlockLaw p (seedsLaw θ) n] ≤ n * ε) ∧
      ∀ j, n * (R * log 2 - ε) ≤ H[c.keyB j ; secBlockLaw p (seedsLaw θ) n]

/-- **Page 23-53 of [elgamal2010].** The secret key capacity `C_K(X₁; …; X_N ‖ Z)`, in bits. -/
def multiKeyCapacity (p : mLetter α γ → ℝ) : ℝ := sSup {R | IsAchievableMultiKey p R}

/-! ### The parts of the block -/

variable {p : mLetter α γ → ℝ} {θ : ∀ j, κ j → ℝ}

/-- The part of the sources and of the private random variables on `D`. -/
def viewB (D : Finset (Fin N)) (w : mBlock α γ κ n) :
    (Fin n → ∀ j, Option (α j)) × ∀ j, Option (κ j) :=
  (fun i => maskL D (w.1 i).1, maskL D w.2)

/-- The observation `(Xⱼⁿ, Wⱼ)` without `Zⁿ`. -/
def partB (j : Fin N) (w : mBlock α γ κ n) : (Fin n → α j) × κ j :=
  (fun i => (w.1 i).1 j, w.2 j)

/-- The union of two parts of the block. -/
def unionMaskB (S : Finset (Fin N)) (v w : (Fin n → ∀ j, Option (α j)) × ∀ j, Option (κ j)) :
    (Fin n → ∀ j, Option (α j)) × ∀ j, Option (κ j) :=
  (fun i => unionMask S (v.1 i) (w.1 i), unionMask S v.2 w.2)

/-- The chain rule for one more node. -/
lemma condEntropy_viewB_insert {Ω' : Type*} [Fintype Ω'] {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ)
    (d : ∀ j, α j) (d' : ∀ j, κ j) (j : Fin N) (D : Finset (Fin N))
    (C : mBlock α γ κ n → Ω') :
    H[viewB (insert j D) | C ; μ] = H[viewB D | C ; μ] + H[partB j | pair (viewB D) C ; μ] := by
  rw [← chain_rule_cond hμ]
  refine condEntropy_eq_of_mutual hμ C
    (fun v => (fun i => Function.update (v.1.1 i) j (some (v.2.1 i)),
      Function.update v.1.2 j (some v.2.2)))
    (fun v => ((fun i => restrictMask D (v.1 i), restrictMask D v.2),
      (fun i => (v.1 i j).getD (d j), (v.2 j).getD (d' j)))) ?_ ?_
  · funext w
    refine Prod.ext (funext fun i => maskL_insert D j _) (maskL_insert D j _)
  · funext w
    refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) (Prod.ext (funext fun i => ?_) ?_)
    · exact (restrictMask_maskL (subset_insert j D) _).symm
    · exact (restrictMask_maskL (subset_insert j D) _).symm
    · simp [viewB, partB, maskL]
    · simp [viewB, partB, maskL]

/-- **The chain rule along the nodes.**
`H(A(S) | A(D), C) = ∑_{j ∈ S} H(Aⱼ | A(S ∩ [1 : j - 1]), A(D), C)`. -/
theorem condEntropy_viewB_eq_sum {Ω' : Type*} [Fintype Ω'] {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ)
    (d : ∀ j, α j) (d' : ∀ j, κ j) (D : Finset (Fin N)) (C : mBlock α γ κ n → Ω')
    (S : Finset (Fin N)) :
    H[viewB S | pair (viewB D) C ; μ] =
      ∑ j ∈ S, H[partB j | pair (viewB ((S.filter (· < j)) ∪ D)) C ; μ] := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    have h₀ : H[viewB (∅ : Finset (Fin N)) | pair (viewB D) C ; μ] = 0 :=
      (condEntropy_eq_zero_iff hμ _ _).2 ⟨fun _ => (fun _ _ => none, fun _ => none), fun w _ => by
        refine Prod.ext (funext fun i => funext fun j => ?_) (funext fun j => ?_) <;>
          simp [viewB, maskL]⟩
    rw [h₀]
    simp
  | insert a S hS ih =>
    have ha : a ∉ S := fun h => lt_irrefl _ (hS a h)
    rw [condEntropy_viewB_insert hμ d d', ih, sum_insert ha, add_comm]
    congr 1
    · have hf : (insert a S).filter (· < a) = S := by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | h, hx⟩
          · exact absurd hx (lt_irrefl _)
          · exact h
        · exact fun h => ⟨Or.inr h, hS x h⟩
      rw [hf]
      refine condEntropy_eq_of_comp hμ _
        (fun v => ((fun i => unionMask S (v.1.1 i) (v.2.1.1 i), unionMask S v.1.2 v.2.1.2), v.2.2))
        (fun v => ((fun i => restrictMask S (v.1.1 i), restrictMask S v.1.2),
          ((fun i => restrictMask D (v.1.1 i), restrictMask D v.1.2), v.2))) ?_ ?_
      · funext w
        refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) rfl
        · exact (unionMask_maskL S D _).symm
        · exact (unionMask_maskL S D _).symm
      · funext w
        refine Prod.ext (Prod.ext (funext fun i => ?_) ?_)
          (Prod.ext (Prod.ext (funext fun i => ?_) ?_) rfl)
        · exact (restrictMask_maskL subset_union_left _).symm
        · exact (restrictMask_maskL subset_union_left _).symm
        · exact (restrictMask_maskL subset_union_right _).symm
        · exact (restrictMask_maskL subset_union_right _).symm
    · refine sum_congr rfl fun j hj => ?_
      have hf : (insert a S).filter (· < j) = S.filter (· < j) := by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | h, hx⟩
          · exact absurd (hS j hj) (not_lt.2 hx.le)
          · exact ⟨h, hx⟩
        · exact fun h => ⟨Or.inr h.1, h.2⟩
      rw [hf]

/-- **The entropy of a part of the block.**
`H(A(S) | A(Sᶜ), Zⁿ) = n H(X(S) | X(Sᶜ), Z) + ∑_{j ∈ S} H(Wⱼ)`. -/
theorem condEntropy_viewB_compl (hp : IsPMF p) (hθ : ∀ j, IsPMF (θ j)) (S : Finset (Fin N)) :
    H[viewB S | pair (viewB Sᶜ) eveM ; secBlockLaw p (seedsLaw θ) n] =
      n * zCondH p S + ∑ j ∈ S, entropy (θ j) := by
  classical
  have hρ := seedsLaw_isPMF hθ
  have hμ : IsPMF (secBlockLaw p (seedsLaw θ) n) := secBlockLaw_isPMF hp hρ n
  set fD : mLetter α γ → (∀ j, Option (α j)) × γ := fun a => (maskL Sᶜ a.1, a.2) with hfD
  set fS : mLetter α γ → ∀ j, Option (α j) := fun a => maskL S a.1 with hfS
  have h₁ := entropy_blockLaw_of (n := n) hp hρ fD (maskL Sᶜ) (pair (viewB Sᶜ) eveM)
    (fun v => ((fun i => (v.1 i).1, v.2), fun i => (v.1 i).2))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (congrFun h.1.1 i) (congrFun h.2 i)) h.1.2)
    fun w => rfl
  have h₂ := entropy_blockLaw_of (n := n) hp hρ (pair fD fS)
    (pair (maskL Sᶜ) (maskL S)) (pair (pair (viewB Sᶜ) eveM) (viewB S))
    (fun v => (((fun i => (v.1 i).1.1, v.2.1), fun i => (v.1 i).1.2),
      (fun i => (v.1 i).2, v.2.2)))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (Prod.ext (congrFun h.1.1.1 i) (congrFun h.1.2 i))
        (congrFun h.2.1 i)) (Prod.ext h.1.1.2 h.2.2))
    fun w => rfl
  have hunion : (Sᶜ ∪ S) = univ := by
    ext x
    by_cases hx : x ∈ S <;> simp
  have hseed : H[pair (maskL Sᶜ) (maskL S) ; seedsLaw θ] = H[maskL univ ; seedsLaw θ] :=
    (entropyRV_eq_of_mutual hρ (fun v => (restrictMask Sᶜ v, restrictMask S v))
      (fun v => unionMask Sᶜ v.1 v.2)
      (funext fun w => Prod.ext (restrictMask_maskL (subset_univ _) w).symm
        (restrictMask_maskL (subset_univ _) w).symm)
      (funext fun w => by
        simp only [Function.comp, pair]
        rw [unionMask_maskL, hunion]))
  have hs₁ := entropy_maskL_seedsLaw hθ Sᶜ
  have hs₂ := entropy_maskL_seedsLaw hθ univ
  have hsum : ∑ j ∈ (univ : Finset (Fin N)), entropy (θ j) =
      ∑ j ∈ Sᶜ, entropy (θ j) + ∑ j ∈ S, entropy (θ j) := by
    rw [add_comm, sum_add_sum_compl]
  have hz : zCondH p S = H[pair fD fS ; p] - H[fD ; p] := condEntropy_eq_sub hp _ _
  rw [condEntropy_eq_sub hμ, h₁, h₂, hseed, hs₁, hs₂, hsum, hz]
  ring

end Code

end InfoTheory
