/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.DoubleBinning

/-!
# Secret key agreement with one-way communication: achievability

The achievability of Theorem 6 of Lecture 23 of El Gamal and Kim: for sources `(X₁, X₂, Z)` and
`p(v | x₁) p(u | v)`, node `1` generates `(Uⁿ, Vⁿ)`, sends `Uⁿ` and a bin of `Vⁿ`, and takes another
bin of `Vⁿ` as the key. The key rate `I(V; X₂ | U) - I(V; Z | U)` is achievable.

## Main definitions

* `oneWayLaw`, `oneWayGap`: the law of `(X₁, X₂, Z, V, U)` and `I(V; X₂ | U) - I(V; Z | U)`.
* `keySeedLaw`: the law of a function `x₁ ↦ (v, u)`, as the private randomness of node `1`.

## Main statements

* `isAchievableKey_of_lt_oneWayGap`: the achievability of Theorem 6.

## Implementation notes

The randomness of `p(v | x₁) p(u | v)` is a private random function of the letter. The law of a
letter and of this function is i.i.d., so the proof works with a deterministic code on a larger
i.i.d. source.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Laws that are images of each other -/

section Image

variable {Ω J a b : Type*} [Fintype Ω] [Fintype J] [Fintype a] [Fintype b] {μ : Ω → ℝ}

/-- A conditional entropy for the image of a law. -/
lemma condEntropy_comp_of_dist (hμ : IsPMF μ) (Γ : Ω → J) (f : J → a) (g : J → b) :
    H[f ∘ Γ | g ∘ Γ ; μ] = H[f | g ; dist μ Γ] := by
  refine condEntropy_eq_of_dist_pair_eq hμ (hμ.dist Γ) ?_
  rw [← dist_comp_eq]
  rfl

/-- A mutual information for the image of a law. -/
lemma mutualInfo_comp_of_dist (Γ : Ω → J) (f : J → a) (g : J → b) :
    I[f ∘ Γ : g ∘ Γ ; μ] = I[f : g ; dist μ Γ] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [← dist_comp_eq]
  rfl

/-- An entropy for the image of a law. -/
lemma entropyRV_comp_of_dist (Γ : Ω → J) (f : J → a) : H[f ∘ Γ ; μ] = H[f ; dist μ Γ] := by
  rw [entropyRV, entropyRV, dist_comp_eq]

end Image

/-! ### A random function -/

section Seed

variable {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq α]

omit [Fintype τ] [DecidableEq α] in
/-- The law of a random function `f`, with `f(a) ∼ κ(a, ·)` independent for all `a`. -/
def keySeedLaw (κ : α → τ → ℝ) (f : α → τ) : ℝ := ∏ a, κ a (f a)

lemma keySeedLaw_isPMF {κ : α → τ → ℝ} (hκ : IsChannel κ) : IsPMF (keySeedLaw κ) := by
  refine ⟨fun f => prod_nonneg fun a _ => (hκ a).nonneg _, ?_⟩
  simp only [keySeedLaw]
  rw [← Fintype.prod_sum fun a t => κ a t]
  simp [(hκ _).sum_eq_one]

/-- The value of the random function at `a` has the law `κ(a, ·)`. -/
lemma sum_keySeedLaw {κ : α → τ → ℝ} (hκ : IsChannel κ) (a₀ : α) (g : τ → ℝ) :
    ∑ f, keySeedLaw κ f * g (f a₀) = ∑ t, κ a₀ t * g t := by
  have h₁ : ∀ f : α → τ, keySeedLaw κ f * g (f a₀) =
      ∏ a, (κ a (f a) * if a = a₀ then g (f a) else 1) := fun f => by
    rw [prod_mul_distrib, keySeedLaw, prod_ite_eq' univ a₀]
    simp
  simp only [h₁]
  rw [← Fintype.prod_sum fun a t => κ a t * if a = a₀ then g t else 1, prod_eq_single a₀
    (fun a _ ha => by simp [ha, (hκ a).sum_eq_one]) (by simp)]
  simp

end Seed

/-! ### The objective -/

section Objective

variable {α₁ α₂ γ 𝒱 𝒰 : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype 𝒱] [Fintype 𝒰]

/-- **Theorem 6 of Lecture 23 of [elgamal2010].** The law `p(x₁, x₂, z) p(v | x₁) p(u | v)`. -/
def oneWayLaw (P : srcLetter α₁ α₂ γ → ℝ) (q : α₁ → 𝒱 → ℝ) (r : 𝒱 → 𝒰 → ℝ) :
    (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 → ℝ :=
  jointOf (jointOf P fun l => q l.1) fun w => r w.2

/-- **Theorem 6 of Lecture 23 of [elgamal2010].** `I(V; X₂ | U) - I(V; Z | U)`. -/
def oneWayGap (P : srcLetter α₁ α₂ γ → ℝ) (q : α₁ → 𝒱 → ℝ) (r : 𝒱 → 𝒰 → ℝ) : ℝ :=
  I[(fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2) : (fun w => w.1.1.2.1) | Prod.snd ;
      oneWayLaw P q r] -
    I[(fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2) : (fun w => w.1.1.2.2) | Prod.snd ;
      oneWayLaw P q r]

/-- The kernel `p(v, u | x₁) = p(v | x₁) p(u | v)`. -/
def oneWayKernel (q : α₁ → 𝒱 → ℝ) (r : 𝒱 → 𝒰 → ℝ) (a : α₁) (t : 𝒱 × 𝒰) : ℝ := q a t.1 * r t.1 t.2

omit [Fintype α₁] [Fintype α₂] [Fintype γ] in
lemma oneWayKernel_isChannel {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ} (hq : IsChannel q)
    (hr : IsChannel r) : IsChannel (oneWayKernel q r) := fun a => by
  refine ⟨fun t => mul_nonneg ((hq a).nonneg _) ((hr _).nonneg _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [oneWayKernel, ← mul_sum, (hr _).sum_eq_one, mul_one, (hq a).sum_eq_one]

/-- The law of the source and of `(V, U)`. -/
def oneWayJoint (P : srcLetter α₁ α₂ γ → ℝ) (q : α₁ → 𝒱 → ℝ) (r : 𝒱 → 𝒰 → ℝ) :
    srcLetter α₁ α₂ γ × 𝒱 × 𝒰 → ℝ :=
  jointOf P fun l => oneWayKernel q r l.1

/-- **Page 23-36 of [elgamal2010].** The objective is `H(V | Z, U) - H(V | X₂, U)`. -/
lemma oneWayGap_eq {P : srcLetter α₁ α₂ γ → ℝ} (hP : IsPMF P) {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ}
    (hq : IsChannel q) (hr : IsChannel r) :
    oneWayGap P q r =
      H[(fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1) | (fun w => (w.1.2.2, w.2.2)) ;
        oneWayJoint P q r] -
      H[(fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1) | (fun w => (w.1.2.1, w.2.2)) ;
        oneWayJoint P q r] := by
  classical
  have hP₁ : IsPMF (jointOf P fun l : srcLetter α₁ α₂ γ => q l.1) := jointOf_isPMF hP fun l => hq _
  have hμ : IsPMF (oneWayLaw P q r) := jointOf_isPMF hP₁ fun w => hr _
  set Γ : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 → srcLetter α₁ α₂ γ × 𝒱 × 𝒰 :=
    fun w => (w.1.1, w.1.2, w.2) with hΓ
  have hd : dist (oneWayLaw P q r) Γ = oneWayJoint P q r := by
    funext x
    have h := dist_equiv (oneWayLaw P q r) (Equiv.prodAssoc (srcLetter α₁ α₂ γ) 𝒱 𝒰) x
    refine h.trans ?_
    obtain ⟨l, v, u⟩ := x
    simp [oneWayLaw, oneWayJoint, jointOf, oneWayKernel, mul_assoc]
  rw [oneWayGap, condMutualInfo, condMutualInfo]
  have e₁ := condEntropy_comp_of_dist hμ Γ (fun w => w.2.1) (fun w => w.2.2)
  have e₂ := condEntropy_comp_of_dist hμ Γ (fun w => w.2.1) (fun w => (w.1.2.1, w.2.2))
  have e₃ := condEntropy_comp_of_dist hμ Γ (fun w => w.2.1) (fun w => (w.1.2.2, w.2.2))
  rw [hd] at e₁ e₂ e₃
  change _ = H[(fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1) | (fun w => (w.1.2.2, w.2.2)) ;
    oneWayJoint P q r] - H[(fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1) |
    (fun w => (w.1.2.1, w.2.2)) ; oneWayJoint P q r]
  rw [← e₂, ← e₃]
  have e₄ : H[(fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2) | Prod.snd ; oneWayLaw P q r] =
      H[(fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2) | Prod.snd ; oneWayLaw P q r] := rfl
  have e₅ : H[(fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2) |
      pair (fun w => w.1.1.2.1) Prod.snd ; oneWayLaw P q r] =
      H[(fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1) ∘ Γ |
        (fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => (w.1.2.1, w.2.2)) ∘ Γ ; oneWayLaw P q r] := rfl
  have e₆ : H[(fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2) |
      pair (fun w => w.1.1.2.2) Prod.snd ; oneWayLaw P q r] =
      H[(fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1) ∘ Γ |
        (fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => (w.1.2.2, w.2.2)) ∘ Γ ; oneWayLaw P q r] := rfl
  rw [e₅, e₆]
  ring

/-- The letter of the i.i.d. source with the private function of node `1`. -/
abbrev seedLetter (α₁ α₂ γ : Type*) (N : ℕ) := srcLetter α₁ α₂ γ × Fin N

variable [DecidableEq α₁]

/-- The number of functions `x₁ ↦ (v, u)`. -/
abbrev seedCard (α₁ 𝒱 𝒰 : Type*) [Fintype α₁] [Fintype 𝒱] [Fintype 𝒰] [DecidableEq α₁] : ℕ :=
  Fintype.card (α₁ → 𝒱 × 𝒰)

/-- The function with a given number. -/
def seedFun (j : Fin (seedCard α₁ 𝒱 𝒰)) : α₁ → 𝒱 × 𝒰 := (Fintype.equivFin _).symm j

/-- The law of the number of the private function. -/
def seedLaw (q : α₁ → 𝒱 → ℝ) (r : 𝒱 → 𝒰 → ℝ) (j : Fin (seedCard α₁ 𝒱 𝒰)) : ℝ :=
  keySeedLaw (oneWayKernel q r) (seedFun j)

omit [Fintype α₂] [Fintype γ] in
lemma seedLaw_isPMF {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ} (hq : IsChannel q) (hr : IsChannel r) :
    IsPMF (seedLaw q r) := by
  have hs := keySeedLaw_isPMF (oneWayKernel_isChannel hq hr)
  refine ⟨fun j => hs.nonneg _, ?_⟩
  rw [← hs.sum_eq_one]
  exact Equiv.sum_comp (Fintype.equivFin (α₁ → 𝒱 × 𝒰)).symm _

/-- The letter `(v, u)` of a letter of the source with a private function. -/
def seedVal (z : seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰)) : 𝒱 × 𝒰 := seedFun z.2 z.1.1

/-- The law of `(X₁, X₂, Z, V, U)` is the image of the law of the letter and the function. -/
lemma dist_seedVal {P : srcLetter α₁ α₂ γ → ℝ} {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ}
    (hq : IsChannel q) (hr : IsChannel r) :
    dist (prodDist P (seedLaw q r)) (fun z => (z.1, seedVal z)) = oneWayJoint P q r := by
  classical
  have hκ := oneWayKernel_isChannel hq hr
  funext ⟨l, t⟩
  have h₁ : ∑ f : α₁ → 𝒱 × 𝒰, keySeedLaw (oneWayKernel q r) f * (if f l.1 = t then 1 else 0) =
      oneWayKernel q r l.1 t := by
    rw [sum_keySeedLaw hκ l.1 fun t' => if t' = t then (1 : ℝ) else 0]
    simp
  have h₂ : ∑ j : Fin (seedCard α₁ 𝒱 𝒰), seedLaw q r j * (if seedFun j l.1 = t then 1 else 0) =
      oneWayKernel q r l.1 t := by
    rw [← h₁]
    exact Equiv.sum_comp (Fintype.equivFin (α₁ → 𝒱 × 𝒰)).symm
      fun f => keySeedLaw (oneWayKernel q r) f * (if f l.1 = t then 1 else 0)
  simp only [dist, Prod.mk.injEq, prodDist, seedVal]
  rw [Fintype.sum_prod_type, sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
  simp only [oneWayJoint, jointOf, true_and]
  rw [← h₂, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : seedFun j l.1 = t <;> simp [h]

end Objective

/-! ### The code -/

section Code

variable {α₁ α₂ γ 𝒱 𝒰 : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype 𝒱] [Fintype 𝒰]
  [DecidableEq α₁] {n Mb Kb : ℕ}

/-- `vⁿ` for the observation of node `1`. -/
def vSeq (a : (Fin n → α₁) × (Fin n → Fin (seedCard α₁ 𝒱 𝒰))) : Fin n → 𝒱 :=
  fun i => (seedFun (a.2 i) (a.1 i)).1

/-- `uⁿ` for the observation of node `1`. -/
def uSeq (a : (Fin n → α₁) × (Fin n → Fin (seedCard α₁ 𝒱 𝒰))) : Fin n → 𝒰 :=
  fun i => (seedFun (a.2 i) (a.1 i)).2

/-- The number of public indices. -/
abbrev pubCard (𝒰 : Type*) [Fintype 𝒰] (n Mb : ℕ) : ℕ := Fintype.card ((Fin n → 𝒰) × Fin Mb)

/-- **Pages 23-32, 23-33 and 23-36 of [elgamal2010].** The code: node `1` sends `uⁿ` and the bin of
`vⁿ`. The key of node `1` is the other bin of `vⁿ`. Node `2` decodes `vⁿ` from `(x₂ⁿ, uⁿ)` and the
bin. -/
def oneWayCode (b₁ : (Fin n → 𝒱) → Fin Mb) (b₂ : (Fin n → 𝒱) → Fin Kb)
    (d₁ : (Fin n → α₂ × 𝒰) → Fin Mb → Fin n → 𝒱) (m₀ : Fin (pubCard 𝒰 n Mb)) :
    KeyCode (q := 1) (fun _ => true) (fun _ => pubCard 𝒰 n Mb) Kb
      ((Fin n → α₁) × (Fin n → Fin (seedCard α₁ 𝒱 𝒰))) ((Fin n → α₂) × Unit) where
  enc₁ _ a _ := Fintype.equivFin _ (uSeq a, b₁ (vSeq a))
  enc₂ _ _ _ := m₀
  key₁ a _ := b₂ (vSeq a)
  key₂ a h := b₂ (d₁ (fun i => (a.1 i, ((Fintype.equivFin _).symm (h 0)).1 i))
    ((Fintype.equivFin _).symm (h 0)).2)

/-- The map from the block to the i.i.d. sequence of letters with private functions. -/
def seedMap (w : (Fin n → srcLetter α₁ α₂ γ) × (Fin n → Fin (seedCard α₁ 𝒱 𝒰)) × Unit) :
    Fin n → seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰) := fun i => (w.1 i, w.2.1 i)

/-- The map as a bijection. -/
def seedEquiv : (Fin n → srcLetter α₁ α₂ γ) × (Fin n → Fin (seedCard α₁ 𝒱 𝒰)) × Unit ≃
    (Fin n → seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰)) where
  toFun := seedMap
  invFun x := (fun i => (x i).1, fun i => (x i).2, ())
  left_inv _ := rfl
  right_inv _ := rfl

/-- The law of the block is the i.i.d. law of letters with private functions. -/
lemma dist_seedMap (P : srcLetter α₁ α₂ γ → ℝ) (q : α₁ → 𝒱 → ℝ) (r : 𝒱 → 𝒰 → ℝ) :
    dist (keyLaw P (iidPMF (seedLaw q r) n) (fun _ : Unit => 1) n) (seedMap (𝒱 := 𝒱) (𝒰 := 𝒰)) =
      iidPMF (prodDist P (seedLaw q r)) n := by
  funext x
  have h := dist_equiv (keyLaw P (iidPMF (seedLaw q r) n) (fun _ : Unit => 1) n)
    (seedEquiv (α₂ := α₂) (γ := γ) (𝒱 := 𝒱) (𝒰 := 𝒰) (n := n)) x
  refine h.trans ?_
  change iidPMF P n (fun i => (x i).1) * (iidPMF (seedLaw q r) n (fun i => (x i).2) * 1) = _
  rw [mul_one]
  simp only [iidPMF, prodDist, prod_mul_distrib]

variable [NeZero (pubCard 𝒰 n Mb)]

omit [Fintype α₂] in
/-- The transcript of the code. -/
lemma trans_oneWayCode (b₁ : (Fin n → 𝒱) → Fin Mb) (b₂ : (Fin n → 𝒱) → Fin Kb)
    (d₁ : (Fin n → α₂ × 𝒰) → Fin Mb → Fin n → 𝒱) (m₀ : Fin (pubCard 𝒰 n Mb))
    (a₁ : (Fin n → α₁) × (Fin n → Fin (seedCard α₁ 𝒱 𝒰))) (a₂ : (Fin n → α₂) × Unit) (l : Fin 1) :
    (oneWayCode b₁ b₂ d₁ m₀).trans a₁ a₂ l = Fintype.equivFin _ (uSeq a₁, b₁ (vSeq a₁)) := by
  simp only [KeyCode.trans]
  rw [run_apply]
  rfl

end Code

/-- **The final arithmetic for the second key.** -/
lemma oneWay_second_key {n : ℕ} {A ε ε₀ l₂ logK P₁ I₁ H₁ I₂ H₂ h₁₂ h₂₁ : ℝ}
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ ≤ 1) (hε₂ : ε₀ * (A + 2) ≤ ε / 2) (hl : 0 ≤ l₂)
    (hn : 4 * l₂ ≤ n * (ε / 2))
    (hlogK : logK ≤ n * A + l₂) (hlogK0 : 0 ≤ logK) (hP : P₁ ≤ ε₀) (hI₁ : I₁ ≤ n * ε₀)
    (hH₁ : n * (A - ε₀) ≤ H₁) (h₁ : I₂ ≤ I₁ + h₂₁) (h₂ : H₁ - h₁₂ ≤ H₂) (h₃ : h₂₁ ≤ l₂ + P₁ * logK)
    (h₄ : h₁₂ ≤ l₂ + P₁ * logK) : I₂ ≤ n * ε ∧ n * (A - ε) ≤ H₂ := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₅ : P₁ * logK ≤ ε₀ * (n * A + l₂) :=
    (mul_le_mul_of_nonneg_right hP hlogK0).trans (mul_le_mul_of_nonneg_left hlogK hε₀.le)
  have h₆ : ε₀ * l₂ ≤ l₂ := by nlinarith
  have h₇ : n * (ε₀ * (A + 2)) ≤ n * (ε / 2) := mul_le_mul_of_nonneg_left hε₂ hn0
  have e₁ : n * (ε₀ * (A + 2)) = ε₀ * (n * A) + n * ε₀ + n * ε₀ := by ring
  have h₈ : 0 ≤ n * ε₀ := by positivity
  have e₂ : (n : ℝ) * ε = n * (ε / 2) + n * (ε / 2) := by ring
  have e₃ : (n : ℝ) * (A - ε) = n * A - n * ε := by ring
  have e₄ : (n : ℝ) * (A - ε₀) = n * A - n * ε₀ := by ring
  have e₅ : ε₀ * (n * A + l₂) = ε₀ * (n * A) + ε₀ * l₂ := by ring
  constructor <;> linarith

variable {α₁ α₂ γ 𝒱 𝒰 : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype 𝒱] [Fintype 𝒰]
  {P : srcLetter α₁ α₂ γ → ℝ} {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ}

/-- **Pages 23-32 to 23-36 of [elgamal2010]: the achievability of Theorem 6.** With one-way
communication from node `1`, every rate below `I(V; X₂ | U) - I(V; Z | U)` is achievable. -/
theorem isAchievableKey_of_lt_oneWayGap (hP : IsPMF P) (hq : IsChannel q) (hr : IsChannel r) {R : ℝ}
    (hR : 0 ≤ R) (hlt : R * log 2 < oneWayGap P q r) :
    IsAchievableKey (fun _ s => ∀ l, s l = true) P R := by
  classical
  have hl := log_pos one_lt_two
  have hA : 0 ≤ R * log 2 := mul_nonneg hR hl.le
  set s := seedLaw q r with hs
  have hsP : IsPMF s := seedLaw_isPMF hq hr
  set P₀ := prodDist P s with hP₀
  have hP₀P : IsPMF P₀ := hP.prodDist hsP
  set Γ : seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰) → srcLetter α₁ α₂ γ × 𝒱 × 𝒰 :=
    fun z => (z.1, seedVal z) with hΓ
  have hd : dist P₀ Γ = oneWayJoint P q r := dist_seedVal hq hr
  set v : seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰) → 𝒱 := fun z => (seedVal z).1 with hv
  set y : seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰) → α₂ × 𝒰 :=
    fun z => (z.1.2.1, (seedVal z).2) with hy
  set e : seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰) → γ × 𝒰 :=
    fun z => (z.1.2.2, (seedVal z).2) with he
  have hgap : H[v | e ; P₀] - H[v | y ; P₀] = oneWayGap P q r := by
    rw [oneWayGap_eq hP hq hr, ← hd]
    congr 1
    · exact condEntropy_comp_of_dist hP₀P Γ (fun w => w.2.1) fun w => (w.1.2.2, w.2.2)
    · exact condEntropy_comp_of_dist hP₀P Γ (fun w => w.2.1) fun w => (w.1.2.1, w.2.2)
  rw [← hgap] at hlt
  refine ⟨hR, fun ε hε => ?_⟩
  set ε₀ := min 1 (ε / (2 * (R * log 2 + 2))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₁ : ε₀ ≤ 1 := min_le_left _ _
  have hε₂ : ε₀ * (R * log 2 + 2) ≤ ε / 2 := by
    have h₁ : ε₀ ≤ ε / (2 * (R * log 2 + 2)) := min_le_right _ _
    have h₂ := (le_div_iff₀ (by positivity)).1 h₁
    linarith
  filter_upwards [eventually_doubleBin hP₀P v y e hR hlt hε₀0,
    eventually_gt_atTop ⌈8 * log 2 / ε⌉₊] with n hn hn1
  obtain ⟨Mb, hMb, b₁, b₂, d₁, herr, hleak, hkey⟩ := hn
  have hnε : 4 * log 2 ≤ n * (ε / 2) := by
    have h₁ : 8 * log 2 / ε < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
    rw [div_lt_iff₀ hε] at h₁
    linarith
  -- The alphabets are not empty.
  obtain ⟨z₀⟩ : Nonempty (seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰)) :=
    Fintype.card_pos_iff.1 (card_pos_of_isPMF hP₀P)
  have hpub : 0 < pubCard 𝒰 n Mb := Fintype.card_pos_iff.2 ⟨(fun _ => (seedVal z₀).2, 0)⟩
  have hne : NeZero (pubCard 𝒰 n Mb) := ⟨hpub.ne'⟩
  set c := oneWayCode (α₁ := α₁) (α₂ := α₂) (Kb := 2 ^ ⌈n * R⌉₊) b₁ b₂ d₁ ⟨0, hpub⟩ with hc
  set π₁ := iidPMF s n with hπ₁
  have hπ₁P : IsPMF π₁ := iidPMF_isPMF hsP n
  have hπ₂P : IsPMF fun _ : Unit => (1 : ℝ) := ⟨fun _ => zero_le_one, by simp⟩
  have hμ : IsPMF (keyLaw P π₁ (fun _ : Unit => 1) n) := secBlockLaw_isPMF hP (hπ₁P.prodDist hπ₂P) n
  have hdist : dist (keyLaw P π₁ (fun _ : Unit => 1) n) (seedMap (𝒱 := 𝒱) (𝒰 := 𝒰)) =
      iidPMF P₀ n := dist_seedMap P q r
  set Ψ := seedMap (α₁ := α₁) (α₂ := α₂) (γ := γ) (𝒱 := 𝒱) (𝒰 := 𝒰) (n := n) with hΨ
  set T : (Fin n → seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰)) → Fin n → 𝒱 := fun ω i => v (ω i) with hT
  set U : (Fin n → seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰)) → Fin n → 𝒰 :=
    fun ω i => (seedVal (ω i)).2 with hU
  -- The keys and the transcript on the block.
  have hK₁ : c.keyB₁ (Prod.fst : srcLetter α₁ α₂ γ → α₁) (fun a => a.2.1) = (b₂ ∘ T) ∘ Ψ := rfl
  have htr : ∀ w l, c.transB (Prod.fst : srcLetter α₁ α₂ γ → α₁) (fun a => a.2.1) w l =
      Fintype.equivFin _ (U (Ψ w), b₁ (T (Ψ w))) := fun w l =>
    trans_oneWayCode b₁ b₂ d₁ ⟨0, hpub⟩ _ _ l
  have hK₂ : c.keyB₂ (Prod.fst : srcLetter α₁ α₂ γ → α₁) (fun a => a.2.1) =
      (fun ω => b₂ (d₁ (fun i => y (ω i)) (b₁ (T ω)))) ∘ Ψ := by
    funext w
    change b₂ (d₁ (fun i => ((w.1 i).2.1, ((Fintype.equivFin _).symm
      (c.transB Prod.fst (fun a => a.2.1) w 0)).1 i)) ((Fintype.equivFin _).symm
      (c.transB Prod.fst (fun a => a.2.1) w 0)).2) = _
    rw [htr, Equiv.symm_apply_apply]
    rfl
  set Ind : (Fin n → seedLetter α₁ α₂ γ (seedCard α₁ 𝒱 𝒰)) → ℝ := fun ω =>
    if d₁ (fun i => y (ω i)) (b₁ (T ω)) ≠ T ω then 1 else 0 with hInd
  have hP₁ : c.errProbB P π₁ (fun _ : Unit => 1) ≤ ε₀ := by
    refine le_trans ?_ herr
    have h₂ := sum_dist_mul (keyLaw P π₁ (fun _ : Unit => 1) n) Ψ Ind
    rw [hdist] at h₂
    refine le_trans ?_ (le_of_eq h₂.symm)
    simp only [KeyCode.errProbB, InfoTheory.errProb, id, hK₁, hK₂, Function.comp]
    refine sum_le_sum fun w _ => ?_
    have h₀ := hμ.nonneg w
    by_cases hd₁ : d₁ (fun i => y (Ψ w i)) (b₁ (T (Ψ w))) = T (Ψ w)
    · rw [hd₁]
      simp [hInd, hd₁]
    · have : Ind (Ψ w) = 1 := by simp [hInd, hd₁]
      rw [this, mul_one]
      split_ifs <;> simp [h₀]
  -- The public information on the block.
  have hpair : pair (KeyCode.eveB (κ₁ := Fin n → Fin (seedCard α₁ 𝒱 𝒰)) (κ₂ := Unit))
      (c.transB (Prod.fst : srcLetter α₁ α₂ γ → α₁) fun a => a.2.1) =
      (fun ω => (fun i => (ω i).1.2.2, fun _ : Fin 1 =>
        Fintype.equivFin _ (U ω, b₁ (T ω)))) ∘ Ψ := by
    funext w
    refine Prod.ext rfl (funext fun l => ?_)
    exact htr w l
  have hleak₁ : c.leak₁ P π₁ (fun _ : Unit => 1) ≤ n * ε₀ := by
    refine le_trans (le_of_eq ?_) hleak
    rw [KeyCode.leak₁, hK₁, hpair, mutualInfo_comp_of_dist, hdist]
    refine mutualInfo_congr_right (iidPMF_isPMF hP₀P n) _
      (fun w => (fun i => (w.1 i).1, fun _ : Fin 1 => Fintype.equivFin _
        ((fun i => (w.1 i).2), w.2))) (fun a b h => ?_) fun ω => rfl
    simp only [Prod.mk.injEq] at h
    have h₂ := (Fintype.equivFin _).injective (congrFun h.2 0)
    simp only [Prod.mk.injEq] at h₂
    exact Prod.ext (funext fun i => Prod.ext (congrFun h.1 i) (congrFun h₂.1 i)) h₂.2
  have hH₁ : n * (R * log 2 - ε₀) ≤ c.entropyKey₁ P π₁ (fun _ : Unit => 1) := by
    refine hkey.trans (le_of_eq ?_)
    have h₂ := entropyRV_comp_of_dist (μ := keyLaw P π₁ (fun _ : Unit => 1) n) Ψ (b₂ ∘ T)
    rw [hdist] at h₂
    exact h₂.symm
  -- The key of node `2`.
  have hlogK := log_two_pow_ceil_le n hR
  have hlogK0 : 0 ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := log_natCast_nonneg _
  set K₁ := c.keyB₁ (Prod.fst : srcLetter α₁ α₂ γ → α₁) fun a => a.2.1 with hK₁d
  set K₂ := c.keyB₂ (Prod.fst : srcLetter α₁ α₂ γ → α₁) fun a => a.2.1 with hK₂d
  set V := pair (KeyCode.eveB (κ₁ := Fin n → Fin (seedCard α₁ 𝒱 𝒰)) (κ₂ := Unit))
      (c.transB (Prod.fst : srcLetter α₁ α₂ γ → α₁) fun a => a.2.1) with hV
  obtain ⟨ht₁, ht₂⟩ := key_transfer hμ K₁ K₂ V
  have hF₁ := fano_weak hμ K₁ K₂ id
  have hF₂ := fano_weak hμ K₂ K₁ id
  rw [Fintype.card_fin] at hF₁ hF₂
  have herrsymm : InfoTheory.errProb (keyLaw P π₁ (fun _ : Unit => 1) n) K₂ K₁ id =
      InfoTheory.errProb (keyLaw P π₁ (fun _ : Unit => 1) n) K₁ K₂ id := by
    simp only [InfoTheory.errProb, id]
    refine sum_congr rfl fun w _ => ?_
    by_cases h : K₁ w = K₂ w
    · simp [h]
    · simp [h, Ne.symm h]
  rw [herrsymm] at hF₂
  obtain ⟨hfin₁, hfin₂⟩ := oneWay_second_key hε₀0 hε₁ hε₂ hl.le hnε hlogK hlogK0 hP₁ hleak₁ hH₁
    ht₁ ht₂ hF₂ hF₁
  refine ⟨1, fun _ => true, fun _ => pubCard 𝒰 n Mb, fun _ => hne, _, Unit, inferInstance,
    inferInstance, π₁, fun _ => 1, c, fun _ => rfl, hπ₁P, hπ₂P, hP₁.trans ?_, ?_, hfin₁, ?_, hfin₂⟩
  · have h₁ : ε₀ ≤ ε / 2 := by
      have : ε₀ * 1 ≤ ε₀ * (R * log 2 + 2) := mul_le_mul_of_nonneg_left (by linarith) hε₀0.le
      linarith
    linarith
  · refine hleak₁.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
    have : ε₀ * 1 ≤ ε₀ * (R * log 2 + 2) := mul_le_mul_of_nonneg_left (by linarith) hε₀0.le
    linarith
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)) hH₁
    have : ε₀ * 1 ≤ ε₀ * (R * log 2 + 2) := mul_le_mul_of_nonneg_left (by linarith) hε₀0.le
    linarith

end InfoTheory
