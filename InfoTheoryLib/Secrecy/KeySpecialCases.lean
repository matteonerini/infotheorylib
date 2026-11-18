/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyOneWayConverse

/-!
# Secret key agreement: the other direction and the cases where the capacity is known

The rest of Theorem 6 of Lecture 23 of El Gamal and Kim, by the symmetry of the two nodes, and the
cases in which the upper bound of Theorem 8 is tight.

## Main definitions

* `srcSwap P`: the source with the two nodes exchanged.
* `KeyCode.swap`: the protocol with the two nodes exchanged.

## Main statements

* `keyCapacity₂₁_eq`, `keyCapacityOneWay_eq`: **Theorem 6 of Lecture 23**.
* `keyCapacity_of_markov₁`, `keyCapacity_of_markov₂`: `C_K = I(X₁; X₂ | Z)` if `X₁ → X₂ → Z` or
  `X₂ → X₁ → Z`.
* `keyCapacity_of_nodes_know`: `C_K = I(X₁; X₂ | Z)` if the nodes know `Z`.
* `keyCapacity_of_indep`: `C_K = I(X₁; X₂)` if `Z` is independent of `(X₁, X₂)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The two nodes exchanged -/

section Err

variable {Ω J a : Type*} [Fintype Ω] [Fintype J] [Fintype a]

omit [Fintype a] in
/-- The probability that two random variables differ, for the image of a law. -/
lemma errProb_image (μ : Ω → ℝ) (Γ : Ω → J) (X Y : J → a) :
    InfoTheory.errProb (dist μ Γ) X Y id = InfoTheory.errProb μ (X ∘ Γ) (Y ∘ Γ) id := by
  classical
  simp only [InfoTheory.errProb, id, Function.comp]
  have h₁ := sum_dist_mul μ Γ fun w => if Y w ≠ X w then (1 : ℝ) else 0
  have h₂ : ∀ w, (if Y w ≠ X w then dist μ Γ w else 0) =
      dist μ Γ w * (if Y w ≠ X w then (1 : ℝ) else 0) := fun w => by split_ifs <;> simp
  simp only [h₂]
  rw [h₁]
  refine sum_congr rfl fun w _ => ?_
  split_ifs <;> simp

omit [Fintype a] in
/-- The probability that two random variables differ is symmetric. -/
lemma errProb_symm (μ : Ω → ℝ) (X Y : Ω → a) :
    InfoTheory.errProb μ X Y id = InfoTheory.errProb μ Y X id := by
  classical
  simp only [InfoTheory.errProb, id]
  refine sum_congr rfl fun w _ => ?_
  by_cases h : X w = Y w
  · simp [h]
  · simp [h, Ne.symm h]

end Err

section Swap

variable {α₁ α₂ γ κ₁ κ₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype κ₁] [Fintype κ₂]

/-- The source with the two nodes exchanged. -/
def srcSwap (P : srcLetter α₁ α₂ γ → ℝ) : srcLetter α₂ α₁ γ → ℝ := fun a => P (a.2.1, a.1, a.2.2)

omit [Fintype κ₁] [Fintype κ₂] in
lemma srcSwap_isPMF {P : srcLetter α₁ α₂ γ → ℝ} (hP : IsPMF P) : IsPMF (srcSwap P) := by
  refine ⟨fun a => hP.nonneg _, ?_⟩
  rw [← hP.sum_eq_one]
  refine Fintype.sum_equiv ⟨fun a : srcLetter α₂ α₁ γ => (a.2.1, a.1, a.2.2),
    fun a => (a.2.1, a.1, a.2.2), fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

omit [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype κ₁] [Fintype κ₂] in
@[simp] lemma srcSwap_srcSwap (P : srcLetter α₁ α₂ γ → ℝ) : srcSwap (srcSwap P) = P := rfl

variable {q n : ℕ} {spk : Fin q → Bool} {M : Fin q → ℕ} [∀ l, NeZero (M l)] {K : ℕ}

/-- The protocol with the two nodes exchanged. -/
def KeyCode.swap {a₁ a₂ : Type*} (c : KeyCode spk M K a₁ a₂) :
    KeyCode (fun l => !spk l) M K a₂ a₁ := ⟨c.enc₂, c.enc₁, c.key₂, c.key₁⟩

/-- The transcript of the protocol with the two nodes exchanged. -/
lemma KeyCode.trans_swap {a₁ a₂ : Type*} (c : KeyCode spk M K a₁ a₂) (x₁ : a₁) (x₂ : a₂) :
    c.swap.trans x₂ x₁ = c.trans x₁ x₂ := by
  have h : c.swap.protocol x₂ x₁ = c.protocol x₁ x₂ := by
    funext l h
    simp only [KeyCode.protocol, KeyCode.swap]
    by_cases hs : spk l = true
    · simp [hs]
    · have hs' : spk l = false := by simpa using hs
      simp [hs']
  simp only [KeyCode.trans, h]

/-- The block with the two nodes exchanged. -/
def blockSwap : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ ≃ (Fin n → srcLetter α₂ α₁ γ) × κ₂ × κ₁ where
  toFun w := (fun i => ((w.1 i).2.1, (w.1 i).1, (w.1 i).2.2), w.2.2, w.2.1)
  invFun w := (fun i => ((w.1 i).2.1, (w.1 i).1, (w.1 i).2.2), w.2.2, w.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The law of the block with the two nodes exchanged. -/
lemma dist_blockSwap (P : srcLetter α₁ α₂ γ → ℝ) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) :
    dist (keyLaw P π₁ π₂ n) blockSwap = keyLaw (srcSwap P) π₂ π₁ n := by
  funext x
  refine (dist_equiv _ _ x).trans ?_
  change iidPMF P n _ * (π₁ _ * π₂ _) = iidPMF (srcSwap P) n _ * (π₂ _ * π₁ _)
  rw [mul_comm (π₁ _)]
  rfl

variable {P : srcLetter α₁ α₂ γ → ℝ} {π₁ : κ₁ → ℝ} {π₂ : κ₂ → ℝ}

/-- **The symmetry of the two nodes.** An achievable rate is achievable for the source with the
nodes exchanged and the protocols with the speakers exchanged. -/
theorem IsAchievableKey.swap {allowed allowed' : ∀ q, (Fin q → Bool) → Prop} {R : ℝ}
    (h : IsAchievableKey allowed P R) (hP : IsPMF P)
    (hallowed : ∀ q (s : Fin q → Bool), allowed q s → allowed' q fun l => !s l) :
    IsAchievableKey allowed' (srcSwap P) R := by
  refine ⟨h.1, fun ε hε => ?_⟩
  filter_upwards [h.2 ε hε] with n hn
  obtain ⟨q, spk, M, hM, κ₁, κ₂, _, _, π₁, π₂, c, hs, hπ₁, hπ₂, herr, hl₁, hl₂, hk₁, hk₂⟩ := hn
  have hd := dist_blockSwap (α₁ := α₁) (α₂ := α₂) (γ := γ) (n := n) P π₁ π₂
  set Sw := blockSwap (α₁ := α₁) (α₂ := α₂) (γ := γ) (κ₁ := κ₁) (κ₂ := κ₂) (n := n) with hSw
  set c' := c.swap with hc'
  have hμ : IsPMF (keyLaw P π₁ π₂ n) := secBlockLaw_isPMF hP (hπ₁.prodDist hπ₂) n
  have htr : c'.transB Prod.fst (fun a => a.2.1) ∘ Sw = c.transB Prod.fst fun a => a.2.1 := by
    funext w
    exact c.trans_swap _ _
  have hK₁ : c'.keyB₁ Prod.fst (fun a => a.2.1) ∘ Sw = c.keyB₂ Prod.fst fun a => a.2.1 := by
    funext w
    change c.key₂ _ (c'.transB Prod.fst (fun a => a.2.1) (Sw w)) = _
    have := congrFun htr w
    simp only [Function.comp] at this
    rw [this]
    rfl
  have hK₂ : c'.keyB₂ Prod.fst (fun a => a.2.1) ∘ Sw = c.keyB₁ Prod.fst fun a => a.2.1 := by
    funext w
    change c.key₁ _ (c'.transB Prod.fst (fun a => a.2.1) (Sw w)) = _
    have := congrFun htr w
    simp only [Function.comp] at this
    rw [this]
    rfl
  have hE : KeyCode.eveB (α₁ := α₂) (α₂ := α₁) (γ := γ) (κ₁ := κ₂) (κ₂ := κ₁) (n := n) ∘ Sw =
      KeyCode.eveB := rfl
  have hV : pair (KeyCode.eveB (α₁ := α₂) (α₂ := α₁) (γ := γ) (κ₁ := κ₂) (κ₂ := κ₁) (n := n))
      (c'.transB Prod.fst fun a => a.2.1) ∘ Sw =
      pair KeyCode.eveB (c.transB Prod.fst fun a => a.2.1) := by
    funext w
    exact Prod.ext rfl (congrFun htr w)
  refine ⟨q, fun l => !spk l, M, hM, κ₂, κ₁, inferInstance, inferInstance, π₂, π₁, c',
    hallowed _ _ hs, hπ₂, hπ₁, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) herr
    rw [KeyCode.errProbB, ← hd, errProb_image, hK₁, hK₂]
    exact errProb_symm _ _ _
  · refine le_trans (le_of_eq ?_) hl₂
    rw [KeyCode.leak₁, ← hd, ← mutualInfo_comp, hK₁, hV]
    rfl
  · refine le_trans (le_of_eq ?_) hl₁
    rw [KeyCode.leak₂, ← hd, ← mutualInfo_comp, hK₂, hV]
    rfl
  · refine hk₂.trans (le_of_eq ?_)
    rw [KeyCode.entropyKey₁, ← hd, ← entropyRV_comp_of_dist, hK₁]
    rfl
  · refine hk₁.trans (le_of_eq ?_)
    rw [KeyCode.entropyKey₂, ← hd, ← entropyRV_comp_of_dist, hK₂]
    rfl

/-- **Theorem 6 of Lecture 23 of [elgamal2010], page 23-31, for communication from node `2` to node
`1`.** The capacity is `sup_{p(v | x₂) p(u | v)} (I(V; X₁ | U) - I(V; Z | U))`, in bits. -/
theorem keyCapacity₂₁_eq (hP : IsPMF P) : keyCapacity₂₁ P = oneWayValue (srcSwap P) / log 2 := by
  rw [← keyCapacity₁₂_eq (srcSwap_isPMF hP)]
  refine congrArg sSup (Set.ext fun R => ⟨fun h => ?_, fun h => ?_⟩)
  · exact h.swap hP fun q s hs l => by simp [hs l]
  · have := h.swap (srcSwap_isPMF hP) (allowed' := fun _ s => ∀ l, s l = false)
      fun q s hs l => by simp [hs l]
    simpa using this

/-- **Theorem 6 of Lecture 23 of [elgamal2010], page 23-31.** The one-way secret key capacity. -/
theorem keyCapacityOneWay_eq (hP : IsPMF P) :
    keyCapacityOneWay P = max (oneWayValue P / log 2) (oneWayValue (srcSwap P) / log 2) := by
  rw [keyCapacityOneWay, keyCapacity₁₂_eq hP, keyCapacity₂₁_eq hP]

end Swap

/-! ### When the upper bound is tight -/

section Tight

variable {α₁ α₂ γ : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] {P : srcLetter α₁ α₂ γ → ℝ}

/-- A set of protocols with more protocols has at least the same achievable rates. -/
lemma IsAchievableKey.mono {allowed allowed' : ∀ q, (Fin q → Bool) → Prop} {R : ℝ}
    (h : IsAchievableKey allowed P R) (hm : ∀ q s, allowed q s → allowed' q s) :
    IsAchievableKey allowed' P R := by
  refine ⟨h.1, fun ε hε => ?_⟩
  filter_upwards [h.2 ε hε] with n hn
  obtain ⟨q, spk, M, hM, κ₁, κ₂, i₁, i₂, π₁, π₂, c, hs, rest⟩ := hn
  exact ⟨q, spk, M, hM, κ₁, κ₂, i₁, i₂, π₁, π₂, c, hm _ _ hs, rest⟩

/-- A set of protocols with more protocols has at least the same capacity. -/
lemma keyCapacityOf_mono {allowed allowed' : ∀ q, (Fin q → Bool) → Prop}
    (hm : ∀ q s, allowed q s → allowed' q s) (hP : IsPMF P) :
    keyCapacityOf allowed P ≤ keyCapacityOf allowed' P := by
  have hl := log_pos one_lt_two
  have hQ : IsChannel fun (_ : γ) (_ : Unit) => (1 : ℝ) := fun _ => ⟨fun _ => zero_le_one, by simp⟩
  have hbdd : BddAbove {R | IsAchievableKey allowed' P R} :=
    ⟨intrinsicInfoOf P (fun (_ : γ) (_ : Unit) => (1 : ℝ)) / log 2, fun R hR =>
      (le_div_iff₀ hl).2 (hR.le hP hQ)⟩
  exact Real.sSup_le (fun R hR => le_csSup hbdd (hR.mono hm)) (Real.sSup_nonneg fun R hR => hR.1)

omit [Fintype γ] in
/-- The identity channel. -/
lemma idChannel_isChannel {τ : Type*} [Fintype τ] [DecidableEq τ] :
    IsChannel fun z z' : τ => if z = z' then (1 : ℝ) else 0 := fun z =>
  ⟨fun z' => by
    dsimp only
    split_ifs <;> norm_num, by simp⟩

/-- With the identity channel, `I(X₁; X₂ | Z̄)` is `I(X₁; X₂ | Z)`. -/
lemma intrinsicInfoOf_id [DecidableEq γ] (hP : IsPMF P) :
    intrinsicInfoOf P (fun z z' : γ => if z = z' then (1 : ℝ) else 0) =
      I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) | (fun a => a.2.2) ; P] := by
  classical
  have hQ : IsChannel fun z z' : γ => if z = z' then (1 : ℝ) else 0 := idChannel_isChannel
  set Γ : srcLetter α₁ α₂ γ → srcLetter α₁ α₂ γ × γ := fun l => (l, l.2.2) with hΓ
  have hd : dist P Γ = jointOf P fun a z' => if a.2.2 = z' then (1 : ℝ) else 0 := by
    funext ⟨l, z'⟩
    simp only [dist, Prod.mk.injEq, jointOf, hΓ]
    rw [sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
    by_cases h : l.2.2 = z' <;> simp [h]
  rw [intrinsicInfoOf, ← hd, condMutualInfo, condMutualInfo,
    ← condEntropy_comp_of_dist hP Γ (fun a => a.1.1) Prod.snd,
    ← condEntropy_comp_of_dist hP Γ (fun a => a.1.1) (pair (fun a => a.1.2.1) Prod.snd)]
  rfl

/-- **Page 23-32 of [elgamal2010]: the rate `I(X₁; X₂) - I(X₁; Z)`.** -/
theorem le_oneWayValue (hP : IsPMF P) :
    H[(Prod.fst : srcLetter α₁ α₂ γ → α₁) | (fun a => a.2.2) ; P] -
      H[(Prod.fst : srcLetter α₁ α₂ γ → α₁) | (fun a => a.2.1) ; P] ≤ oneWayValue P := by
  classical
  set q : α₁ → α₁ → ℝ := fun a v => if a = v then 1 else 0 with hq
  set r : α₁ → Unit → ℝ := fun _ _ => 1 with hr
  have hqC : IsChannel q := fun a => ⟨fun v => by simp only [hq]; split_ifs <;> norm_num, by simp
    [hq]⟩
  have hrC : IsChannel r := fun _ => ⟨fun _ => zero_le_one, by simp [hr]⟩
  refine le_trans (le_of_eq ?_) (oneWayGap_le_value hP hqC hrC)
  set Γ : srcLetter α₁ α₂ γ → srcLetter α₁ α₂ γ × α₁ × Unit := fun l => (l, l.1, ()) with hΓ
  have hd : dist P Γ = oneWayJoint P q r := by
    funext ⟨l, v, u⟩
    simp only [dist, Prod.mk.injEq, oneWayJoint, jointOf, oneWayKernel, hq, hr, hΓ]
    rw [sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
    by_cases h : l.1 = v <;> simp [h]
  rw [oneWayGap_eq hP hqC hrC, ← hd, ← condEntropy_comp_of_dist hP Γ (fun w => w.2.1)
    (fun w => (w.1.2.2, w.2.2)), ← condEntropy_comp_of_dist hP Γ (fun w => w.2.1)
    (fun w => (w.1.2.1, w.2.2))]
  have e₁ := condEntropy_congr_right hP (Prod.fst : srcLetter α₁ α₂ γ → α₁)
    (X := fun a => a.2.2) (X' := (fun w => (w.1.2.2, w.2.2)) ∘ Γ) (fun a => (a, ()))
    (fun a b h => (Prod.mk.inj h).1) fun _ => rfl
  have e₂ := condEntropy_congr_right hP (Prod.fst : srcLetter α₁ α₂ γ → α₁)
    (X := fun a => a.2.1) (X' := (fun w => (w.1.2.1, w.2.2)) ∘ Γ) (fun a => (a, ()))
    (fun a b h => (Prod.mk.inj h).1) fun _ => rfl
  exact congrArg₂ (· - ·) e₁.symm e₂.symm

/-- **Page 23-45 of [elgamal2010].** If `X₁ → X₂ → Z`, then the secret key capacity is
`I(X₁; X₂ | Z)`, in bits, and it is achieved with communication from node `1` to node `2`. -/
theorem keyCapacity_of_markov₁ (hP : IsPMF P)
    (hm : I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.2) | (fun a => a.2.1) ; P] = 0) :
    keyCapacity₁₂ P = I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) |
      (fun a => a.2.2) ; P] /
        log 2 ∧
      keyCapacity P = I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) |
        (fun a => a.2.2) ; P] /
        log 2 := by
  classical
  have hl := log_pos one_lt_two
  have hQ : IsChannel fun z z' : γ => if z = z' then (1 : ℝ) else 0 := idChannel_isChannel
  have hup := keyCapacity_le_of_channel (fun _ _ => True) hP hQ
  rw [intrinsicInfoOf_id hP] at hup
  have hmono : keyCapacity₁₂ P ≤ keyCapacity P := keyCapacityOf_mono (fun _ _ _ => trivial) hP
  have hlow : I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) | (fun a => a.2.2) ; P] /
      log 2 ≤ keyCapacity₁₂ P := by
    rw [keyCapacity₁₂_eq hP]
    refine div_le_div_of_nonneg_right (le_trans (le_of_eq ?_) (le_oneWayValue hP)) hl.le
    rw [condMutualInfo] at hm ⊢
    have e : H[(Prod.fst : srcLetter α₁ α₂ γ → α₁) | pair (fun a => a.2.1) (fun a => a.2.2) ; P] =
        H[(Prod.fst : srcLetter α₁ α₂ γ → α₁) | pair (fun a => a.2.2) (fun a => a.2.1) ; P] :=
      condEntropy_congr_right hP _ Prod.swap Prod.swap_injective fun _ => rfl
    rw [e]
    linarith
  exact ⟨le_antisymm (hmono.trans hup) hlow, le_antisymm hup (hlow.trans hmono)⟩

/-- The law of the source with the two nodes exchanged, as an image. -/
lemma dist_srcSwap : dist P (fun a : srcLetter α₁ α₂ γ => ((a.2.1, a.1, a.2.2) : srcLetter α₂ α₁
  γ)) =
    srcSwap P := by
  funext x
  have e : srcLetter α₁ α₂ γ ≃ srcLetter α₂ α₁ γ := ⟨fun a => (a.2.1, a.1, a.2.2),
    fun a => (a.2.1, a.1, a.2.2), fun _ => rfl, fun _ => rfl⟩
  exact dist_equiv P ⟨fun a => (a.2.1, a.1, a.2.2), fun a => (a.2.1, a.1, a.2.2), fun _ => rfl,
    fun _ => rfl⟩ x

/-- **Page 23-45 of [elgamal2010].** If `X₂ → X₁ → Z`, then the secret key capacity is
`I(X₁; X₂ | Z)`, in bits, and it is achieved with communication from node `2` to node `1`. -/
theorem keyCapacity_of_markov₂ (hP : IsPMF P)
    (hm : I[(fun a : srcLetter α₁ α₂ γ => a.2.1) : (fun a => a.2.2) | Prod.fst ; P] = 0) :
    keyCapacity₂₁ P = I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) |
      (fun a => a.2.2) ; P] /
        log 2 ∧
      keyCapacity P = I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) |
        (fun a => a.2.2) ; P] /
        log 2 := by
  classical
  have hl := log_pos one_lt_two
  have hS := srcSwap_isPMF hP
  set Γ := fun a : srcLetter α₁ α₂ γ => ((a.2.1, a.1, a.2.2) : srcLetter α₂ α₁ γ) with hΓ
  have hd : dist P Γ = srcSwap P := dist_srcSwap
  -- The conditional entropies of the exchanged source.
  have e₁ : H[(Prod.fst : srcLetter α₂ α₁ γ → α₂) | (fun a => a.2.2) ; srcSwap P] =
      H[(fun a : srcLetter α₁ α₂ γ => a.2.1) | (fun a => a.2.2) ; P] := by
    rw [← hd, ← condEntropy_comp_of_dist hP Γ]
    rfl
  have e₂ : H[(Prod.fst : srcLetter α₂ α₁ γ → α₂) | (fun a => a.2.1) ; srcSwap P] =
      H[(fun a : srcLetter α₁ α₂ γ => a.2.1) | Prod.fst ; P] := by
    rw [← hd, ← condEntropy_comp_of_dist hP Γ]
    rfl
  have hval : I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) | (fun a => a.2.2) ; P] =
      H[(fun a : srcLetter α₁ α₂ γ => a.2.1) | (fun a => a.2.2) ; P] -
        H[(fun a : srcLetter α₁ α₂ γ => a.2.1) | Prod.fst ; P] := by
    rw [condMutualInfo_comm hP, condMutualInfo]
    rw [condMutualInfo] at hm
    have e : H[(fun a : srcLetter α₁ α₂ γ => a.2.1) | pair Prod.fst (fun a => a.2.2) ; P] =
        H[(fun a : srcLetter α₁ α₂ γ => a.2.1) | pair (fun a => a.2.2) Prod.fst ; P] :=
      condEntropy_congr_right hP _ Prod.swap Prod.swap_injective fun _ => rfl
    rw [e]
    linarith
  have hQ : IsChannel fun z z' : γ => if z = z' then (1 : ℝ) else 0 := idChannel_isChannel
  have hup := keyCapacity_le_of_channel (fun _ _ => True) hP hQ
  rw [intrinsicInfoOf_id hP] at hup
  have hmono : keyCapacity₂₁ P ≤ keyCapacity P := keyCapacityOf_mono (fun _ _ _ => trivial) hP
  have hlow : I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) | (fun a => a.2.2) ; P] /
      log 2 ≤ keyCapacity₂₁ P := by
    rw [keyCapacity₂₁_eq hP, hval]
    refine div_le_div_of_nonneg_right ?_ hl.le
    have := le_oneWayValue hS
    rwa [e₁, e₂] at this
  exact ⟨le_antisymm (hmono.trans hup) hlow, le_antisymm hup (hlow.trans hmono)⟩

/-- **Page 23-51 of [elgamal2010].** If `Z` is independent of `(X₁, X₂)`, in particular if the
eavesdropper only listens to the public communication, the secret key capacity is `I(X₁; X₂)`. -/
theorem keyCapacity_of_indep (hP : IsPMF P)
    (hi : I[(fun a : srcLetter α₁ α₂ γ => a.2.2) : (fun a => (a.1, a.2.1)) ; P] = 0) :
    keyCapacity P = I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) ; P] / log 2 := by
  set x₁ : srcLetter α₁ α₂ γ → α₁ := Prod.fst
  set x₂ : srcLetter α₁ α₂ γ → α₂ := fun a => a.2.1
  set z : srcLetter α₁ α₂ γ → γ := fun a => a.2.2
  have h₁ : I[z : pair x₁ x₂ ; P] = 0 := hi
  have hc₁ := chain_rule_mutualInfo₂ hP z x₁ x₂
  have h₂ := mutualInfo_nonneg hP z x₂
  have h₃ := condMutualInfo_nonneg hP z x₁ x₂
  have hzx₁ : I[z : x₁ ; P] = 0 := by
    have hc₂ := chain_rule_mutualInfo₂ hP z x₂ x₁
    have e : I[z : pair x₂ x₁ ; P] = I[z : pair x₁ x₂ ; P] :=
      mutualInfo_congr_right hP z Prod.swap Prod.swap_injective fun _ => rfl
    have h₄ := mutualInfo_nonneg hP z x₁
    have h₅ := condMutualInfo_nonneg hP z x₂ x₁
    linarith
  have hm : I[x₁ : z | x₂ ; P] = 0 := by
    rw [condMutualInfo_comm hP]
    linarith
  have hval : I[x₁ : x₂ | z ; P] = I[x₁ : x₂ ; P] := by
    have c₁ := chain_rule_mutualInfo₂ hP x₁ x₂ z
    have c₂ := chain_rule_mutualInfo₂ hP x₁ z x₂
    have e : I[x₁ : pair z x₂ ; P] = I[x₁ : pair x₂ z ; P] :=
      mutualInfo_congr_right hP x₁ Prod.swap Prod.swap_injective fun _ => rfl
    have e₂ : I[x₁ : z ; P] = 0 := by rw [mutualInfo_comm hP]; exact hzx₁
    linarith
  rw [(keyCapacity_of_markov₁ hP hm).2, hval]

/-- The source with `Z` known to both nodes. -/
def nodesKnow (P : srcLetter α₁ α₂ γ → ℝ) : srcLetter (α₁ × γ) (α₂ × γ) γ → ℝ :=
  dist P fun l => ((l.1, l.2.2), (l.2.1, l.2.2), l.2.2)

/-- **Page 23-51 of [elgamal2010].** If both nodes know `Z`, the secret key capacity is
`I(X₁; X₂ | Z)`, in bits. -/
theorem keyCapacity_of_nodes_know (hP : IsPMF P) :
    keyCapacity (nodesKnow P) =
      I[(Prod.fst : srcLetter α₁ α₂ γ → α₁) : (fun a => a.2.1) | (fun a => a.2.2) ; P] / log 2 := by
  have hS : IsPMF (nodesKnow P) := hP.dist _
  set Γ : srcLetter α₁ α₂ γ → srcLetter (α₁ × γ) (α₂ × γ) γ :=
    fun l => ((l.1, l.2.2), (l.2.1, l.2.2), l.2.2) with hΓ
  have hm : I[(Prod.fst : srcLetter (α₁ × γ) (α₂ × γ) γ → α₁ × γ) : (fun a => a.2.2) |
      (fun a => a.2.1) ; nodesKnow P] = 0 := by
    rw [condMutualInfo_comm hS, condMutualInfo]
    have h₁ : H[(fun a : srcLetter (α₁ × γ) (α₂ × γ) γ => a.2.2) | (fun a => a.2.1) ;
        nodesKnow P] = H[(fun a : srcLetter α₁ α₂ γ => a.2.2) ∘ id |
        (fun a => (a.2.1, a.2.2)) ; P] := by
      rw [nodesKnow, ← condEntropy_comp_of_dist hP Γ]
      rfl
    have h₂ : H[(fun a : srcLetter (α₁ × γ) (α₂ × γ) γ => a.2.2) |
        pair Prod.fst (fun a => a.2.1) ; nodesKnow P] =
        H[(fun a : srcLetter α₁ α₂ γ => a.2.2) ∘ id |
          (fun a => ((a.1, a.2.2), (a.2.1, a.2.2))) ; P] := by
      rw [nodesKnow, ← condEntropy_comp_of_dist hP Γ]
      rfl
    have h₃ : H[(fun a : srcLetter α₁ α₂ γ => a.2.2) ∘ id | (fun a => (a.2.1, a.2.2)) ; P] = 0 :=
      (condEntropy_eq_zero_iff hP _ _).2 ⟨fun w => w.2, fun _ _ => rfl⟩
    have h₄ : H[(fun a : srcLetter α₁ α₂ γ => a.2.2) ∘ id |
        (fun a => ((a.1, a.2.2), (a.2.1, a.2.2))) ; P] = 0 :=
      (condEntropy_eq_zero_iff hP _ _).2 ⟨fun w => w.2.2, fun _ _ => rfl⟩
    rw [h₁, h₂, h₃, h₄, sub_zero]
  rw [(keyCapacity_of_markov₁ hS hm).2]
  congr 1
  rw [condMutualInfo, condMutualInfo, nodesKnow, ← condEntropy_comp_of_dist hP Γ,
    ← condEntropy_comp_of_dist hP Γ]
  have e₁ : H[(Prod.fst : srcLetter (α₁ × γ) (α₂ × γ) γ → α₁ × γ) ∘ Γ |
      (fun a : srcLetter (α₁ × γ) (α₂ × γ) γ => a.2.2) ∘ Γ ; P] =
      H[(Prod.fst : srcLetter α₁ α₂ γ → α₁) | (fun a => a.2.2) ; P] := by
    have h₁ := chain_rule_cond hP (Prod.fst : srcLetter α₁ α₂ γ → α₁) (fun a => a.2.2)
      (fun a => a.2.2)
    have h₂ : H[(fun a : srcLetter α₁ α₂ γ => a.2.2) |
        pair Prod.fst (fun a => a.2.2) ; P] = 0 :=
      (condEntropy_eq_zero_iff hP _ _).2 ⟨fun w => w.2, fun _ _ => rfl⟩
    rw [h₂, add_zero] at h₁
    exact h₁
  have e₂ : H[(Prod.fst : srcLetter (α₁ × γ) (α₂ × γ) γ → α₁ × γ) ∘ Γ |
      pair (fun a : srcLetter (α₁ × γ) (α₂ × γ) γ => a.2.1) (fun a => a.2.2) ∘ Γ ; P] =
      H[(Prod.fst : srcLetter α₁ α₂ γ → α₁) | pair (fun a => a.2.1) (fun a => a.2.2) ; P] := by
    have h₁ := chain_rule_cond hP (Prod.fst : srcLetter α₁ α₂ γ → α₁) (fun a => a.2.2)
      (pair (fun a => a.2.1) (fun a => a.2.2))
    have h₂ : H[(fun a : srcLetter α₁ α₂ γ => a.2.2) |
        pair Prod.fst (pair (fun a => a.2.1) (fun a => a.2.2)) ; P] = 0 :=
      (condEntropy_eq_zero_iff hP _ _).2 ⟨fun w => w.2.2, fun _ _ => rfl⟩
    rw [h₂, add_zero] at h₁
    have h₃ : H[(Prod.fst : srcLetter (α₁ × γ) (α₂ × γ) γ → α₁ × γ) ∘ Γ |
        pair (fun a : srcLetter (α₁ × γ) (α₂ × γ) γ => a.2.1) (fun a => a.2.2) ∘ Γ ; P] =
        H[pair (Prod.fst : srcLetter α₁ α₂ γ → α₁) (fun a => a.2.2) |
          pair (fun a => a.2.1) (fun a => a.2.2) ; P] :=
      condEntropy_congr_right hP (pair (Prod.fst : srcLetter α₁ α₂ γ → α₁) (fun a => a.2.2))
        (fun w : α₂ × γ => ((w.1, w.2), w.2))
        (fun a b h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1.1 h.2) fun _ => rfl
    rw [h₃, h₁]
  exact congrArg₂ (· - ·) e₁ e₂

end Tight

end InfoTheory
