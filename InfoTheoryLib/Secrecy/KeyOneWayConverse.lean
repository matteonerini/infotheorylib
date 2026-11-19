/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyOneWay

/-!
# Secret key agreement with one-way communication: the converse and the capacity

Theorem 6 of Lecture 23 of El Gamal and Kim. With communication from node `1` to node `2` only, the
secret key capacity is `max_{p(v | x₁) p(u | v)} (I(V; X₂ | U) - I(V; Z | U))`.

## Main definitions

* `oneWayValue`: the value of Theorem 6, in nats.
* `keyCapacity₁₂`, `keyCapacity₂₁`, `keyCapacityOneWay`: the one-way secret key capacities.

## Main statements

* `condMutualInfo_sub_eq_sum`: the Csiszár sum identity given a random variable `T`.
* `exists_channel_coord`: the memoryless step: the key and the other letters depend on the letter
  at time `i` only through `X₁ᵢ`.
* `keyCapacity₁₂_eq`, `keyCapacity₂₁_eq`, `keyCapacityOneWay_eq`: **Theorem 6 of Lecture 23**.

## Implementation notes

The notes state a maximum, with no bound on the alphabets of `U` and `V`. We take the supremum over
finite alphabets.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The Csiszár sum identity given a random variable -/

section Identity

variable {Ω 𝓚 𝓣 β γ : Type*} [Fintype Ω] [Fintype 𝓚] [Fintype 𝓣] [Fintype β] [Fintype γ] {μ : Ω → ℝ}

/-- `I(K, T; W) = I(T; W) + I(K; W | T)`. -/
lemma mutualInfo_pair_left {τ : Type*} [Fintype τ] (hμ : IsPMF μ) (K : Ω → 𝓚) (T : Ω → 𝓣)
    (W : Ω → τ) : I[pair K T : W ; μ] = I[T : W ; μ] + I[K : W | T ; μ] := by
  have a₁ := chain_rule_mutualInfo₂ hμ W K T
  rw [mutualInfo_comm hμ W, mutualInfo_comm hμ W, condMutualInfo_comm hμ W] at a₁
  exact a₁

/-- `I(K, T; W | C) = I(T; W | C) + I(K; W | T, C)`. -/
lemma condMutualInfo_pair_left {τ σ : Type*} [Fintype τ] [Fintype σ] (hμ : IsPMF μ) (K : Ω → 𝓚)
    (T : Ω → 𝓣) (W : Ω → τ) (C : Ω → σ) :
    I[pair K T : W | C ; μ] = I[T : W | C ; μ] + I[K : W | pair T C ; μ] := by
  have a₁ := chain_rule_condMutualInfo hμ W K T C
  rw [condMutualInfo_comm hμ W, condMutualInfo_comm hμ W, condMutualInfo_comm hμ W] at a₁
  exact a₁

/-- **Page 23-37 of [elgamal2010], (c).** With `Vᵢ = (Y^{i-1}, Z_{i+1}ⁿ)`,
`I(K; Yⁿ | T) - I(K; Zⁿ | T) = ∑ᵢ (I(K; Yᵢ | T, Vᵢ) - I(K; Zᵢ | T, Vᵢ))`. -/
theorem condMutualInfo_sub_eq_sum (hμ : IsPMF μ) (K : Ω → 𝓚) (T : Ω → 𝓣) (Y : ℕ → Ω → β)
    (Z : ℕ → Ω → γ) (n : ℕ) :
    I[K : prefixRV Y n | T ; μ] - I[K : suffixRV Z 0 n | T ; μ] =
      ∑ i ∈ range n, (I[K : Y i | pair T (pair (prefixRV Y i) (suffixRV Z (i + 1) n)) ; μ] -
        I[K : Z i | pair T (pair (prefixRV Y i) (suffixRV Z (i + 1) n)) ; μ]) := by
  have h₁ := mutualInfo_sub_mutualInfo_eq_sum hμ (pair K T) Y Z n
  have h₂ := mutualInfo_sub_mutualInfo_eq_sum hμ T Y Z n
  have hsum : ∑ i ∈ range n, (I[K : Y i | pair T (pair (prefixRV Y i) (suffixRV Z (i + 1) n)) ; μ] -
      I[K : Z i | pair T (pair (prefixRV Y i) (suffixRV Z (i + 1) n)) ; μ]) =
      ∑ i ∈ range n, (I[pair K T : Y i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ] -
        I[pair K T : Z i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ]) -
      ∑ i ∈ range n, (I[T : Y i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ] -
        I[T : Z i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ]) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [condMutualInfo_pair_left hμ K T, condMutualInfo_pair_left hμ K T]
    ring
  rw [hsum, ← h₁, ← h₂, mutualInfo_pair_left hμ K T, mutualInfo_pair_left hμ K T]
  ring

end Identity

/-! ### The memoryless step -/

section Coord

variable {α₁ α₂ γ κ g : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype κ] [Fintype g]
  {P : srcLetter α₁ α₂ γ → ℝ} {ρ : κ → ℝ} {n : ℕ}

/-- **Page 23-38 of [elgamal2010]: the Markov chain `(U, V) → X₁ → (X₂, Z)`.** Let `G` be a function
of the block that does not depend on the letter at time `i`, except through its first coordinate.
Then `(Xᵢ, G)` has the law `p(x₁, x₂, z) q(g | x₁)` for a channel `q`. -/
theorem exists_channel_coord (hP : IsPMF P) (hρ : IsPMF ρ) (i : Fin n)
    (G : (Fin n → srcLetter α₁ α₂ γ) × κ → g)
    (hG : ∀ ω u (l l' : srcLetter α₁ α₂ γ), l.1 = l'.1 →
      G (Function.update ω i l, u) = G (Function.update ω i l', u)) :
    ∃ q : α₁ → g → ℝ, IsChannel q ∧
      dist (secBlockLaw P ρ n) (pair (fun w => w.1 i) G) = jointOf P fun l => q l.1 := by
  classical
  obtain ⟨l₀⟩ : Nonempty (srcLetter α₁ α₂ γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  set F : α₁ → g → (Fin n → srcLetter α₁ α₂ γ) × κ → ℝ := fun a v w =>
    if G (Function.update w.1 i (a, l₀.2), w.2) = v then 1 else 0 with hF
  set q : α₁ → g → ℝ := fun a v => ∑ w, secBlockLaw P ρ n w * F a v w with hq
  have hν := secBlockLaw_isPMF hP hρ n
  refine ⟨q, fun a => ⟨fun v => sum_nonneg fun w _ => mul_nonneg (hν.nonneg w) ?_, ?_⟩, ?_⟩
  · simp only [hF]
    split_ifs <;> norm_num
  · simp only [hq]
    rw [sum_comm]
    simp only [← mul_sum, hF]
    have : ∀ w : (Fin n → srcLetter α₁ α₂ γ) × κ,
        ∑ v, (if G (Function.update w.1 i (a, l₀.2), w.2) = v then (1 : ℝ) else 0) = 1 :=
      fun w => by simp
    simp only [this, mul_one, hν.sum_eq_one]
  · funext ⟨l, v⟩
    simp only [dist, pair, Prod.mk.injEq, jointOf, hq, mul_sum]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type (f := fun w : (Fin n → srcLetter α₁ α₂ γ) × κ => _)]
    simp only [secBlockLaw, prodDist]
    rw [sum_comm]
    rw [sum_comm (s := (univ : Finset (Fin n → srcLetter α₁ α₂ γ)))]
    refine sum_congr rfl fun u _ => ?_
    have hc := sum_iidPMF_mul_coord hP i
      (F := fun s => if G (Function.update s i (l.1, l₀.2), u) = v then (1 : ℝ) else 0)
      (fun s a => by rw [Function.update_idem]) (fun a => if a = l then (1 : ℝ) else 0)
    have hg : ∑ a, P a * (if a = l then (1 : ℝ) else 0) = P l := by simp
    rw [hg] at hc
    have hL : ∀ s : Fin n → srcLetter α₁ α₂ γ,
        (if s i = l ∧ G (s, u) = v then iidPMF P n s * ρ u else 0) =
        ρ u * (iidPMF P n s * ((if G (Function.update s i (l.1, l₀.2), u) = v then (1 : ℝ) else 0) *
          if s i = l then 1 else 0)) := fun s => by
      by_cases hs : s i = l
      · have e₁ : G (Function.update s i (l.1, l₀.2), u) = G (s, u) := by
          have := hG s u (l.1, l₀.2) (s i) (by rw [hs])
          rw [this, Function.update_eq_self]
        simp [hs, e₁]
        by_cases hv : G (s, u) = v <;> simp [hv]
        ring
      · simp [hs]
    simp only [hL]
    rw [← mul_sum, hc]
    simp only [hF]
    have hR : ∀ s : Fin n → srcLetter α₁ α₂ γ,
        P l * (iidPMF P n s * ρ u *
          (if G (Function.update s i (l.1, l₀.2), u) = v then (1 : ℝ) else 0)) =
        ρ u * (iidPMF P n s * (if G (Function.update s i (l.1, l₀.2), u) = v then (1 : ℝ) else 0)) *
          P l := fun s => by ring
    simp only [hR]
    rw [← sum_mul, ← mul_sum]
    ring

end Coord

/-! ### The value -/

section Value

variable {α₁ α₂ γ : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] {P : srcLetter α₁ α₂ γ → ℝ}
  {𝒱 𝒰 𝒱' 𝒰' : Type*} [Fintype 𝒱] [Fintype 𝒰] [Fintype 𝒱'] [Fintype 𝒰']

/-- **Theorem 6 of Lecture 23 of [elgamal2010], the value.** The supremum of
`I(V; X₂ | U) - I(V; Z | U)` over `p(v | x₁) p(u | v)` with finite alphabets, in nats. -/
def oneWayValue (P : srcLetter α₁ α₂ γ → ℝ) : ℝ :=
  sSup {g | ∃ (k l : ℕ) (q : α₁ → Fin k → ℝ) (r : Fin k → Fin l → ℝ),
    IsChannel q ∧ IsChannel r ∧ oneWayGap P q r = g}

/-- The objective is bounded by `log |𝒳₂|`. -/
lemma oneWayGap_le_log (hP : IsPMF P) {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ} (hq : IsChannel q)
    (hr : IsChannel r) : oneWayGap P q r ≤ log (Fintype.card α₂) := by
  have hP₁ : IsPMF (jointOf P fun l : srcLetter α₁ α₂ γ => q l.1) := jointOf_isPMF hP fun l => hq _
  have hμ : IsPMF (oneWayLaw P q r) := jointOf_isPMF hP₁ fun w => hr _
  rw [oneWayGap]
  have h₁ := condMutualInfo_nonneg hμ (fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2)
    (fun w => w.1.1.2.2) Prod.snd
  have h₂ : I[(fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.2) : (fun w => w.1.1.2.1) | Prod.snd ;
      oneWayLaw P q r] ≤ log (Fintype.card α₂) := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
    have h₃ := condEntropy_nonneg hμ (fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.1.2.1)
      (pair (fun w => w.1.2) Prod.snd)
    have h₄ := condEntropy_le_entropy hμ (fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.1.2.1) Prod.snd
    have h₅ := entropyRV_le_log_card hμ (fun w : (srcLetter α₁ α₂ γ × 𝒱) × 𝒰 => w.1.1.2.1)
    linarith
  linarith

omit [Fintype α₁] in
lemma isChannel_relabel_q {q : α₁ → 𝒱 → ℝ} (hq : IsChannel q) (e𝒱 : 𝒱 ≃ 𝒱') :
    IsChannel fun a v => q a (e𝒱.symm v) := fun a =>
  ⟨fun v => (hq a).nonneg _, by rw [Equiv.sum_comp e𝒱.symm (q a)]; exact (hq a).sum_eq_one⟩

omit [Fintype 𝒱] [Fintype 𝒱'] in
lemma isChannel_relabel_r {r : 𝒱 → 𝒰 → ℝ} (hr : IsChannel r) (e𝒱 : 𝒱 ≃ 𝒱') (e𝒰 : 𝒰 ≃ 𝒰') :
    IsChannel fun v u => r (e𝒱.symm v) (e𝒰.symm u) := fun v =>
  ⟨fun u => (hr _).nonneg _, by
    rw [Equiv.sum_comp e𝒰.symm (r (e𝒱.symm v))]; exact (hr _).sum_eq_one⟩

/-- A conditional entropy of the law does not depend on the names of the auxiliary letters. -/
lemma condEntropy_oneWayJoint_relabel {b : Type*} [Fintype b] (hP : IsPMF P) {q : α₁ → 𝒱 → ℝ}
    {r : 𝒱 → 𝒰 → ℝ} (hq : IsChannel q) (hr : IsChannel r) (e𝒱 : 𝒱 ≃ 𝒱') (e𝒰 : 𝒰 ≃ 𝒰')
    (g : srcLetter α₁ α₂ γ → b) :
    H[(fun w : srcLetter α₁ α₂ γ × 𝒱' × 𝒰' => w.2.1) | (fun w => (g w.1, w.2.2)) ;
      oneWayJoint P (fun a v => q a (e𝒱.symm v)) (fun v u => r (e𝒱.symm v) (e𝒰.symm u))] =
    H[(fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1) | (fun w => (g w.1, w.2.2)) ;
      oneWayJoint P q r] := by
  classical
  have hJ : IsPMF (oneWayJoint P q r) :=
    jointOf_isPMF hP fun l => oneWayKernel_isChannel hq hr _
  set E : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 ≃ srcLetter α₁ α₂ γ × 𝒱' × 𝒰' :=
    (Equiv.refl _).prodCongr (e𝒱.prodCongr e𝒰) with hE
  have hd : dist (oneWayJoint P q r) E = oneWayJoint P (fun a v => q a (e𝒱.symm v))
      (fun v u => r (e𝒱.symm v) (e𝒰.symm u)) := by
    funext x
    refine (dist_equiv _ E x).trans ?_
    obtain ⟨l, v, u⟩ := x
    simp [oneWayJoint, jointOf, oneWayKernel, hE]
  rw [← hd, ← condEntropy_comp_of_dist hJ E]
  have e₁ := condEntropy_comp_left_injective hJ (fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1)
    (fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => (g w.1, e𝒰 w.2.2)) e𝒱.injective
  have e₂ := condEntropy_comp_right_injective hJ (fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => w.2.1)
    (fun w : srcLetter α₁ α₂ γ × 𝒱 × 𝒰 => (g w.1, w.2.2))
    (f := fun w : b × 𝒰 => (w.1, e𝒰 w.2)) (fun a c h => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
      exact Prod.ext h.1 h.2)
  exact e₁.trans e₂

/-- The objective does not depend on the names of the auxiliary letters. -/
lemma oneWayGap_relabel (hP : IsPMF P) {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ} (hq : IsChannel q)
    (hr : IsChannel r) (e𝒱 : 𝒱 ≃ 𝒱') (e𝒰 : 𝒰 ≃ 𝒰') :
    oneWayGap P (fun a v => q a (e𝒱.symm v)) (fun v u => r (e𝒱.symm v) (e𝒰.symm u)) =
      oneWayGap P q r := by
  rw [oneWayGap_eq hP (isChannel_relabel_q hq e𝒱) (isChannel_relabel_r hr e𝒱 e𝒰),
    oneWayGap_eq hP hq hr, condEntropy_oneWayJoint_relabel hP hq hr e𝒱 e𝒰 fun l => l.2.2,
    condEntropy_oneWayJoint_relabel hP hq hr e𝒱 e𝒰 fun l => l.2.1]

/-- Every law, with any alphabets, has an objective at most the value. -/
theorem oneWayGap_le_value (hP : IsPMF P) {q : α₁ → 𝒱 → ℝ} {r : 𝒱 → 𝒰 → ℝ} (hq : IsChannel q)
    (hr : IsChannel r) : oneWayGap P q r ≤ oneWayValue P := by
  classical
  have hbdd : BddAbove {g | ∃ (k l : ℕ) (q : α₁ → Fin k → ℝ) (r : Fin k → Fin l → ℝ),
      IsChannel q ∧ IsChannel r ∧ oneWayGap P q r = g} := by
    refine ⟨log (Fintype.card α₂), ?_⟩
    rintro _ ⟨k, l, q', r', hq', hr', rfl⟩
    exact oneWayGap_le_log hP hq' hr'
  exact le_csSup hbdd ⟨_, _, _, _, isChannel_relabel_q hq (Fintype.equivFin 𝒱),
    isChannel_relabel_r hr (Fintype.equivFin 𝒱) (Fintype.equivFin 𝒰),
    oneWayGap_relabel hP hq hr (Fintype.equivFin 𝒱) (Fintype.equivFin 𝒰)⟩

/-- `H(K, U | C, U) = H(K | C, U)`. -/
lemma condEntropy_pair_of_cond {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (K : Ω → a) (U : Ω → b) (C : Ω → c) :
    H[pair K U | pair C U ; μ] = H[K | pair C U ; μ] := by
  have h₁ := chain_rule_cond hμ K U (pair C U)
  have h₂ : H[U | pair K (pair C U) ; μ] = 0 :=
    (condEntropy_eq_zero_iff hμ _ _).2 ⟨fun w => w.2.2, fun _ _ => rfl⟩
  rw [h₁, h₂, add_zero]

/-- **The step `(d)` and `(e)` of pages 23-37 and 23-38 of [elgamal2010].** If `(K, U)` does not
depend on the letter at time `i`, except through `X₁ᵢ`, then `I(K; X₂ᵢ | U) - I(K; Zᵢ | U)` is at
most the value. -/
theorem letterGap_le_value {κ 𝓚 : Type*} [Fintype κ] [Fintype 𝓚] {ρ : κ → ℝ} {n : ℕ}
    (hP : IsPMF P) (hρ : IsPMF ρ) (i : Fin n) (K : (Fin n → srcLetter α₁ α₂ γ) × κ → 𝓚)
    (U : (Fin n → srcLetter α₁ α₂ γ) × κ → 𝒰)
    (hG : ∀ ω u (l l' : srcLetter α₁ α₂ γ), l.1 = l'.1 →
      pair K U (Function.update ω i l, u) = pair K U (Function.update ω i l', u)) :
    I[K : (fun w => (w.1 i).2.1) | U ; secBlockLaw P ρ n] -
      I[K : (fun w => (w.1 i).2.2) | U ; secBlockLaw P ρ n] ≤ oneWayValue P := by
  classical
  have hμ := secBlockLaw_isPMF hP hρ n
  obtain ⟨q, hq, hd⟩ := exists_channel_coord hP hρ i (pair K U) hG
  set r : 𝓚 × 𝒰 → 𝒰 → ℝ := fun g u => if u = g.2 then 1 else 0 with hr
  have hrC : IsChannel r := fun g => ⟨fun u => by simp only [hr]; split_ifs <;> norm_num, by simp
    [hr]⟩
  refine le_trans (le_of_eq ?_) (oneWayGap_le_value hP hq hrC)
  set Γ : (Fin n → srcLetter α₁ α₂ γ) × κ → srcLetter α₁ α₂ γ × (𝓚 × 𝒰) × 𝒰 :=
    fun w => (w.1 i, pair K U w, U w) with hΓ
  have hdΓ : dist (secBlockLaw P ρ n) Γ = oneWayJoint P q r := by
    have h₁ : Γ = (fun z : srcLetter α₁ α₂ γ × 𝓚 × 𝒰 => (z.1, z.2, z.2.2)) ∘
        pair (fun w => w.1 i) (pair K U) := rfl
    rw [h₁, dist_comp_eq, hd]
    funext ⟨l, g, u⟩
    simp only [dist, Prod.mk.injEq, oneWayJoint, jointOf, oneWayKernel, hr]
    rw [Fintype.sum_prod_type, sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
    rw [sum_eq_single g (fun b _ hb => by simp [hb]) (by simp)]
    by_cases hu : u = g.2
    · simp [hu]
    · simp [hu, Ne.symm hu]
  rw [oneWayGap_eq hP hq hrC, ← hdΓ]
  have e₁ := condEntropy_comp_of_dist hμ Γ (fun w => w.2.1) (fun w => (w.1.2.2, w.2.2))
  have e₂ := condEntropy_comp_of_dist hμ Γ (fun w => w.2.1) (fun w => (w.1.2.1, w.2.2))
  rw [← e₁, ← e₂]
  have e₃ := condEntropy_pair_of_cond hμ K U fun w => (w.1 i).2.2
  have e₄ := condEntropy_pair_of_cond hμ K U fun w => (w.1 i).2.1
  rw [condMutualInfo, condMutualInfo]
  change _ = H[pair K U | pair (fun w => (w.1 i).2.2) U ; secBlockLaw P ρ n] -
    H[pair K U | pair (fun w => (w.1 i).2.1) U ; secBlockLaw P ρ n]
  rw [e₃, e₄]
  ring

end Value

/-! ### The converse for one code -/

section Code

variable {α₁ α₂ γ κ₁ κ₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype κ₁] [Fintype κ₂]
  {P : srcLetter α₁ α₂ γ → ℝ} {π₁ : κ₁ → ℝ} {π₂ : κ₂ → ℝ} {q n : ℕ} {spk : Fin q → Bool}
  {M : Fin q → ℕ} [∀ l, NeZero (M l)] {K : ℕ}

/-- If only node `1` speaks, the transcript does not depend on the observation of node `2`. -/
lemma KeyCode.trans_indep {a₁ a₂ : Type*} (c : KeyCode spk M K a₁ a₂) (hs : ∀ l, spk l = true)
    (x₁ : a₁) (x₂ x₂' : a₂) : c.trans x₁ x₂ = c.trans x₁ x₂' := by
  have h : c.protocol x₁ x₂ = c.protocol x₁ x₂' := by
    funext l h
    simp [KeyCode.protocol, hs]
  simp only [KeyCode.trans, h]

/-- The private random variable of node `2` is independent of the rest. -/
lemma mutualInfo_seed₂_eq_zero (hP : IsPMF P) (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) :
    I[(fun w : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ => w.2.2) : (fun w => (w.1, w.2.1)) ;
      keyLaw P π₁ π₂ n] = 0 := by
  have hρ := hπ₁.prodDist hπ₂
  have hμ : IsPMF (keyLaw P π₁ π₂ n) := secBlockLaw_isPMF hP hρ n
  rw [mutualInfo_eq_add_sub hμ]
  have h₁ := entropy_keyLaw_of hP hπ₁ hπ₂ n (fun _ => ()) Prod.snd
    (fun w : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ => w.2.2) (fun v => v.2)
    (fun a b h => Prod.ext (funext fun _ => rfl) h) fun _ => rfl
  have h₂ := entropy_keyLaw_of hP hπ₁ hπ₂ n id Prod.fst
    (fun w : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ => (w.1, w.2.1)) (fun v => v)
    (fun a b h => h) fun _ => rfl
  have h₃ := entropy_keyLaw_of hP hπ₁ hπ₂ n id id
    (pair (fun w : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ => w.2.2) fun w => (w.1, w.2.1))
    (fun v => (v.2.2, v.1, v.2.1))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2.1 (Prod.ext h.2.2 h.1)) fun _ => rfl
  have h₄ := entropy_seeds hπ₁ hπ₂
  have h₅ : H[(fun _ : srcLetter α₁ α₂ γ => ()) ; P] = 0 := entropyRV_const hP ()
  rw [h₁, h₂, h₃, h₄, h₅]
  ring

/-- **Pages 23-37 and 23-38 of [elgamal2010]: the converse of Theorem 6 for one code.**
`H(K₁) ≤ n C_{K-1} + I(K₁; Zⁿ, M) + log 2 + Pₑ log K`. -/
theorem KeyCode.entropyKey₁_le_oneWay (c : KeyCode spk M K ((Fin n → α₁) × κ₁) ((Fin n → α₂) × κ₂))
    (hs : ∀ l, spk l = true) (hP : IsPMF P) (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) :
    c.entropyKey₁ P π₁ π₂ ≤ n * oneWayValue P + c.leak₁ P π₁ π₂ + log 2 +
      c.errProbB P π₁ π₂ * log K := by
  classical
  have hρ := hπ₁.prodDist hπ₂
  have hμ : IsPMF (keyLaw P π₁ π₂ n) := secBlockLaw_isPMF hP hρ n
  obtain ⟨l₀⟩ : Nonempty (srcLetter α₁ α₂ γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  obtain ⟨w₂₀⟩ : Nonempty κ₂ := Fintype.card_pos_iff.1 (card_pos_of_isPMF hπ₂)
  set f₁ : srcLetter α₁ α₂ γ → α₁ := Prod.fst
  set f₂ : srcLetter α₁ α₂ γ → α₂ := fun a => a.2.1
  set K₁ := c.keyB₁ f₁ f₂ with hK₁
  set K₂ := c.keyB₂ f₁ f₂ with hK₂
  set T := c.transB f₁ f₂ with hT
  set Xs : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ → Fin n → α₂ := fun w i => (w.1 i).2.1 with hXs
  set Zs := KeyCode.eveB (α₁ := α₁) (α₂ := α₂) (γ := γ) (κ₁ := κ₁) (κ₂ := κ₂) (n := n) with hZs
  -- `H(K₁ | X₂ⁿ, M) ≤ H(K₁ | K₂)`.
  have hcond : H[K₁ | pair Xs T ; keyLaw P π₁ π₂ n] ≤ H[K₁ | K₂ ; keyLaw P π₁ π₂ n] := by
    set W₂ : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ → κ₂ := fun w => w.2.2 with hW₂
    set D : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ → (Fin n → srcLetter α₁ α₂ γ) × κ₁ :=
      fun w => (w.1, w.2.1) with hD
    set φ : (Fin n → srcLetter α₁ α₂ γ) × κ₁ → Fin K × (Fin n → α₂) × ∀ l, Fin (M l) := fun d =>
      (c.key₁ (fun i => (d.1 i).1, d.2) (c.trans (fun i => (d.1 i).1, d.2)
          (fun i => (d.1 i).2.1, w₂₀)), (fun i => (d.1 i).2.1),
        c.trans (fun i => (d.1 i).1, d.2) (fun i => (d.1 i).2.1, w₂₀)) with hφ
    have hφD : pair K₁ (pair Xs T) = φ ∘ D := by
      funext w
      have e : T w = c.trans (fun i => (w.1 i).1, w.2.1) (fun i => (w.1 i).2.1, w₂₀) :=
        c.trans_indep hs _ _ _
      simp only [pair, Function.comp, hφ, hD]
      refine Prod.ext ?_ (Prod.ext rfl e)
      change c.key₁ _ (T w) = _
      rw [e]
      rfl
    have h₁ : I[W₂ : pair K₁ (pair Xs T) ; keyLaw P π₁ π₂ n] ≤ 0 := by
      rw [hφD]
      exact (mutualInfo_comp_le hμ W₂ D φ).trans (le_of_eq (mutualInfo_seed₂_eq_zero hP hπ₁ hπ₂))
    have h₂ := chain_rule_mutualInfo₂ hμ W₂ K₁ (pair Xs T)
    have h₃ := mutualInfo_nonneg hμ W₂ (pair Xs T)
    have h₄ := condMutualInfo_nonneg hμ W₂ K₁ (pair Xs T)
    have h₅ : I[K₁ : W₂ | pair Xs T ; keyLaw P π₁ π₂ n] = 0 := by
      rw [condMutualInfo_comm hμ]
      linarith
    have h₆ : H[K₁ | pair Xs T ; keyLaw P π₁ π₂ n] =
        H[K₁ | pair W₂ (pair Xs T) ; keyLaw P π₁ π₂ n] := by
      rw [condMutualInfo] at h₅
      linarith
    rw [h₆]
    exact condEntropy_le_condEntropy_comp hμ K₁ (pair W₂ (pair Xs T))
      fun v => c.key₂ (v.2.1, v.1) v.2.2
  -- The sequences.
  set Y : ℕ → (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ → α₂ :=
    fun j w => if h : j < n then (w.1 ⟨j, h⟩).2.1 else l₀.2.1 with hY
  set Z : ℕ → (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ → γ :=
    fun j w => if h : j < n then (w.1 ⟨j, h⟩).2.2 else l₀.2.2 with hZ
  have hYn : prefixRV Y n = Xs := by
    funext w j
    simp [prefixRV, hY, hXs, j.isLt]
  have hZn : H[K₁ | pair (suffixRV Z 0 n) T ; keyLaw P π₁ π₂ n] =
      H[K₁ | pair Zs T ; keyLaw P π₁ π₂ n] := by
    refine condEntropy_congr_right hμ _ (fun w => (fun j => w.1 ⟨j, by have := j.isLt; omega⟩, w.2))
      (fun a b h => ?_) fun w => ?_
    · simp only [Prod.mk.injEq] at h
      refine Prod.ext (funext fun j => ?_) h.2
      have := congrFun h.1 ⟨j, by have := j.isLt; omega⟩
      simpa using this
    · refine Prod.ext (funext fun j => ?_) rfl
      have hj : (0 + (j : ℕ)) < n := by have := j.isLt; omega
      simp [suffixRV, hZ, hZs, KeyCode.eveB]
  -- The single-letterization.
  have hsum : I[K₁ : prefixRV Y n | T ; keyLaw P π₁ π₂ n] -
      I[K₁ : suffixRV Z 0 n | T ; keyLaw P π₁ π₂ n] ≤ n * oneWayValue P := by
    rw [condMutualInfo_sub_eq_sum hμ]
    have hterm : ∀ i ∈ range n,
        I[K₁ : Y i | pair T (pair (prefixRV Y i) (suffixRV Z (i + 1) n)) ; keyLaw P π₁ π₂ n] -
        I[K₁ : Z i | pair T (pair (prefixRV Y i) (suffixRV Z (i + 1) n)) ; keyLaw P π₁ π₂ n] ≤
          oneWayValue P := by
      intro i hi
      have hin : i < n := mem_range.1 hi
      have e₁ : Y i = fun w => (w.1 ⟨i, hin⟩).2.1 := by
        funext w
        simp [hY, hin]
      have e₂ : Z i = fun w => (w.1 ⟨i, hin⟩).2.2 := by
        funext w
        simp [hZ, hin]
      rw [e₁, e₂]
      refine letterGap_le_value hP hρ ⟨i, hin⟩ K₁ _ fun ω u l l' hll' => ?_
      have hx₁ : ∀ j, (Function.update ω ⟨i, hin⟩ l j).1 = (Function.update ω ⟨i, hin⟩ l' j).1 := by
        intro j
        by_cases hj : j = ⟨i, hin⟩
        · subst hj
          simpa using hll'
        · simp [Function.update_of_ne hj]
      have hne : ∀ j : ℕ, j ≠ i → ∀ h : j < n, Function.update ω ⟨i, hin⟩ l ⟨j, h⟩ =
          Function.update ω ⟨i, hin⟩ l' ⟨j, h⟩ := fun j hj h => by
        have hj' : (⟨j, h⟩ : Fin n) ≠ ⟨i, hin⟩ := fun he => hj (congrArg Fin.val he)
        rw [Function.update_of_ne hj', Function.update_of_ne hj']
      have hobs : obs₁ f₁ (Function.update ω ⟨i, hin⟩ l, u) =
          obs₁ f₁ (Function.update ω ⟨i, hin⟩ l', u) :=
        Prod.ext (funext hx₁) rfl
      have htr : T (Function.update ω ⟨i, hin⟩ l, u) = T (Function.update ω ⟨i, hin⟩ l', u) := by
        simp only [hT, KeyCode.transB]
        rw [hobs]
        exact c.trans_indep hs _ _ _
      refine Prod.ext ?_ (Prod.ext htr (Prod.ext ?_ ?_))
      · change c.key₁ _ (T _) = c.key₁ _ (T _)
        rw [htr, hobs]
      · funext j
        have hj : (j : ℕ) < i := j.isLt
        have hjn : (j : ℕ) < n := by omega
        simp only [pair, prefixRV, hY, hjn, ↓reduceDIte]
        rw [hne j (by omega) hjn]
      · funext j
        simp only [pair, suffixRV, hZ]
        split_ifs with hjn
        · rw [hne _ (by omega) hjn]
        · rfl
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    simp
  -- The chain of inequalities.
  have h₁ := mutualInfo_eq_entropy_sub_condEntropy hμ K₁ (pair Xs T)
  have h₂ := chain_rule_mutualInfo₂ hμ K₁ Xs T
  have h₃ := chain_rule_mutualInfo₂ hμ K₁ Zs T
  have h₄ := mutualInfo_nonneg hμ K₁ T
  have h₅ : I[K₁ : suffixRV Z 0 n | T ; keyLaw P π₁ π₂ n] = I[K₁ : Zs | T ; keyLaw P π₁ π₂ n] := by
    rw [condMutualInfo, condMutualInfo, hZn]
  rw [hYn, h₅] at hsum
  have hF := fano_weak hμ K₁ K₂ id
  rw [Fintype.card_fin] at hF
  have e₅ : c.entropyKey₁ P π₁ π₂ = H[K₁ ; keyLaw P π₁ π₂ n] := rfl
  have e₆ : c.leak₁ P π₁ π₂ = I[K₁ : pair Zs T ; keyLaw P π₁ π₂ n] := rfl
  have e₇ : c.errProbB P π₁ π₂ = InfoTheory.errProb (keyLaw P π₁ π₂ n) K₁ K₂ id := rfl
  rw [e₅, e₆, e₇]
  linarith

end Code

/-! ### Theorem 6 -/

section Theorem

variable {α₁ α₂ γ : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] {P : srcLetter α₁ α₂ γ → ℝ}

/-- **Page 23-31 of [elgamal2010].** The secret key capacity with communication from node `1` to
node `2` only, `C_{K-1}(X₁; X₂^(s) ‖ Z)`, in bits. -/
def keyCapacity₁₂ (P : srcLetter α₁ α₂ γ → ℝ) : ℝ := keyCapacityOf (fun _ s => ∀ l, s l = true) P

/-- **Page 23-31 of [elgamal2010].** The secret key capacity with communication from node `2` to
node `1` only, `C_{K-1}(X₁^(s); X₂ ‖ Z)`, in bits. -/
def keyCapacity₂₁ (P : srcLetter α₁ α₂ γ → ℝ) : ℝ := keyCapacityOf (fun _ s => ∀ l, s l = false) P

/-- **Page 23-31 of [elgamal2010].** The one-way secret key capacity `C_{K-1}`, in bits. -/
def keyCapacityOneWay (P : srcLetter α₁ α₂ γ → ℝ) : ℝ := max (keyCapacity₁₂ P) (keyCapacity₂₁ P)

/-- **The converse of Theorem 6.** -/
theorem IsAchievableKey.le_oneWayValue {R : ℝ}
  (h : IsAchievableKey (fun _ s => ∀ l, s l = true) P R)
    (hP : IsPMF P) : R * log 2 ≤ oneWayValue P := by
  have hl := log_pos one_lt_two
  have ha : 0 ≤ R * log 2 := mul_nonneg h.1 hl.le
  refine le_of_forall_eventually_mul_le ha fun ε' hε' => ?_
  refine ⟨2 * log 2, ?_⟩
  set ε := min (ε' / 2) 1 with hε
  have hε0 : 0 < ε := lt_min (by linarith) one_pos
  have hε₁ : ε ≤ ε' / 2 := min_le_left _ _
  have hε₂ : ε ≤ 1 := min_le_right _ _
  filter_upwards [h.2 ε hε0] with n hn
  obtain ⟨q, spk, M, hM, κ₁, κ₂, _, _, π₁, π₂, c, hs, hπ₁, hπ₂, herr, hl₁, -, hk₁, -⟩ := hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb := c.entropyKey₁_le_oneWay hs hP hπ₁ hπ₂
  have hlogK := log_two_pow_ceil_le n h.1
  have hlogK0 : 0 ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := log_natCast_nonneg _
  have h₁ : c.errProbB P π₁ π₂ * log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ ε * (n * (R * log 2) + log 2) :=
    (mul_le_mul_of_nonneg_right herr hlogK0).trans (mul_le_mul_of_nonneg_left hlogK hε0.le)
  have hA : 0 ≤ (n : ℝ) * (R * log 2) := mul_nonneg hn0 ha
  have h₂ : ε * (n * (R * log 2)) ≤ ε' * (n * (R * log 2)) := by
    refine mul_le_mul_of_nonneg_right ?_ hA
    linarith
  have h₃ : ε * log 2 ≤ log 2 := by nlinarith
  have h₄ : (n : ℝ) * (ε + ε) ≤ n * ε' := mul_le_mul_of_nonneg_left (by linarith) hn0
  have e₁ : (n : ℝ) * (R * log 2 - ε) = n * (R * log 2) - n * ε := by ring
  have e₂ : (n : ℝ) * (oneWayValue P + ε') = n * oneWayValue P + n * ε' := by ring
  have e₃ : (1 - ε') * ((n : ℝ) * (R * log 2)) = n * (R * log 2) - ε' * (n * (R * log 2)) := by ring
  have e₄ : ε * (n * (R * log 2) + log 2) = ε * (n * (R * log 2)) + ε * log 2 := by ring
  have e₅ : (n : ℝ) * (ε + ε) = n * ε + n * ε := by ring
  rw [e₂, e₃]
  linarith

/-- A random variable with one value has conditional entropy `0`. -/
lemma condEntropy_unit_eq_zero {Ω b : Type*} [Fintype Ω] [Fintype b] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (V : Ω → Unit) (C : Ω → b) : H[V | C ; μ] = 0 := by
  refine le_antisymm ?_ (condEntropy_nonneg hμ _ _)
  have h₁ := condEntropy_le_entropy hμ V C
  have h₂ := entropyRV_le_log_card hμ V
  simp only [Fintype.card_unique, Nat.cast_one, log_one] at h₂
  linarith

/-- The objective is `0` for constant auxiliary random variables, so the value is nonnegative. -/
lemma oneWayValue_nonneg (hP : IsPMF P) : 0 ≤ oneWayValue P := by
  have hq : IsChannel fun (_ : α₁) (_ : Unit) => (1 : ℝ) := fun _ => ⟨fun _ => zero_le_one, by simp⟩
  have hr : IsChannel fun (_ : Unit) (_ : Unit) => (1 : ℝ) := fun _ =>
    ⟨fun _ => zero_le_one, by simp⟩
  have hJ : IsPMF (oneWayJoint P (fun (_ : α₁) (_ : Unit) => (1 : ℝ))
      (fun (_ : Unit) (_ : Unit) => (1 : ℝ))) :=
    jointOf_isPMF hP fun l => oneWayKernel_isChannel hq hr _
  refine le_trans (le_of_eq ?_) (oneWayGap_le_value hP hq hr)
  rw [oneWayGap_eq hP hq hr, condEntropy_unit_eq_zero hJ, condEntropy_unit_eq_zero hJ, sub_zero]

/-- **Theorem 6 of Lecture 23 of [elgamal2010], page 23-31.** With communication from node `1` to
node `2` only, the secret key capacity is `sup_{p(v | x₁) p(u | v)} (I(V; X₂ | U) - I(V; Z | U))`,
in bits. -/
theorem keyCapacity₁₂_eq (hP : IsPMF P) : keyCapacity₁₂ P = oneWayValue P / log 2 := by
  have hl := log_pos one_lt_two
  have hV := oneWayValue_nonneg hP
  have hup : ∀ R ∈ {R | IsAchievableKey (fun _ s => ∀ l, s l = true) P R},
      R ≤ oneWayValue P / log 2 := fun R hR => (le_div_iff₀ hl).2 (hR.le_oneWayValue hP)
  refine le_antisymm (Real.sSup_le hup (div_nonneg hV hl.le)) ?_
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  rcases lt_or_ge r 0 with h0 | h0
  · exact h0.le.trans (Real.sSup_nonneg fun R hR => hR.1)
  · have hne : {g | ∃ (k l : ℕ) (q : α₁ → Fin k → ℝ) (r : Fin k → Fin l → ℝ),
        IsChannel q ∧ IsChannel r ∧ oneWayGap P q r = g}.Nonempty :=
      ⟨_, 1, 1, fun _ _ => 1, fun _ _ => 1, fun _ => ⟨fun _ => zero_le_one, by simp⟩,
        fun _ => ⟨fun _ => zero_le_one, by simp⟩, rfl⟩
    obtain ⟨_, ⟨k, l, q, r', hq, hr', rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne
      ((lt_div_iff₀ hl).1 hr)
    exact le_csSup ⟨_, hup⟩ (isAchievableKey_of_lt_oneWayGap hP hq hr' h0 hlt)

end Theorem

end InfoTheory
