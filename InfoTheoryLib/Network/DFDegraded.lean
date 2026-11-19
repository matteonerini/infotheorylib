/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DFTheorem

/-!
# Physically degraded networks

The decode–forward lower bound is tight for physically degraded networks.

## Main definitions

* `IsDegradedNet W`: the Markov chains `X^{d-1} → (Y_d, X_d^N) → Y_{d+1}^N` of page 19-8.
* `dfBound W`: `max_{p(xᴺ)} min_d I(X^{d-1}; Y_d | X_d^N)`.

## Main statements

* `cutInfo_dfLt_eq`: on a degraded network, the information across the cut before `d` is
  `I(X^{d-1}; Y_d | X_d^N)`.
* `mnCapacity_of_degraded`: **the capacity of a physically degraded network**.
* `mnCapacity_relay_both`: the capacity of the relay channel when the relay also decodes.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section Degraded

variable {N : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

/-- The nodes after node `d`. -/
def dfGt (d : Fin N) : Finset (Fin N) := univ.filter fun k => (d : ℕ) < k

/-- **Page 19-8 of [elgamal2010].** A network is physically degraded if, for all the input laws,
`X^{d-1} → (Y_d, X_d^N) → Y_{d+1}^N` is a Markov chain for all the nodes `d`. -/
def IsDegradedNet (W : (∀ k, X k) → (∀ k, Y k) → ℝ) : Prop :=
  ∀ (p : (∀ k, X k) → ℝ), IsPMF p → ∀ d : Fin N,
    I[fun ω : (∀ l, X l) × (∀ l, Y l) => restr (dfLt d) ω.1 : fun ω => restr (dfGt d) ω.2 |
      fun ω => (ω.2 d, restr (dfLt d)ᶜ ω.1) ; jointOf p W] = 0

/-- **Page 19-8 of [elgamal2010].** On a degraded network, the information across the cut before `d`
is `I(X^{d-1}; Y_d | X_d^N)`. -/
theorem cutInfo_dfLt_eq (hW : IsChannel W) (hdeg : IsDegradedNet W) {p : (∀ k, X k) → ℝ}
    (hp : IsPMF p) (d : Fin N) : cutInfo p W (dfLt d) = dfInfo p W d := by
  classical
  have hL := jointOf_isPMF hp hW
  set L₀ := jointOf p W with hL₀
  let A : (∀ l, X l) × (∀ l, Y l) → ∀ l : dfLt d, X l := fun ω => restr (dfLt d) ω.1
  let Xc : (∀ l, X l) × (∀ l, Y l) → ∀ l : ((dfLt d)ᶜ : Finset (Fin N)), X l :=
    fun ω => restr (dfLt d)ᶜ ω.1
  let Yd : (∀ l, X l) × (∀ l, Y l) → Y d := fun ω => ω.2 d
  let Yg : (∀ l, X l) × (∀ l, Y l) → ∀ l : dfGt d, Y l := fun ω => restr (dfGt d) ω.2
  let Yc : (∀ l, X l) × (∀ l, Y l) → ∀ l : ((dfLt d)ᶜ : Finset (Fin N)), Y l :=
    fun ω => restr (dfLt d)ᶜ ω.2
  -- the outputs after the cut are the output of `d` and the outputs after `d`
  have hmem : ∀ l : Fin N, l ∈ (dfLt d)ᶜ ↔ l = d ∨ l ∈ dfGt d := by
    intro l
    simp only [dfLt, dfGt, mem_compl, mem_filter, mem_univ, true_and, not_lt, Fin.ext_iff]
    constructor
    · intro h
      have : (d : ℕ) ≤ l := h
      omega
    · intro h
      have : (d : ℕ) ≤ l := by omega
      exact this
  have hdc : d ∈ (dfLt d)ᶜ := (hmem d).2 (Or.inl rfl)
  let g : (∀ l : ((dfLt d)ᶜ : Finset (Fin N)), Y l) → Y d × ∀ l : dfGt d, Y l := fun c =>
    (c ⟨d, hdc⟩, fun l => c ⟨l, (hmem l).2 (Or.inr l.property)⟩)
  have hg : Function.Injective g := by
    intro a b h
    funext l
    rcases (hmem l).1 l.property with hl | hl
    · have e : l = ⟨d, hdc⟩ := Subtype.ext hl
      rw [e]
      exact (Prod.ext_iff.mp h).1
    · exact congrFun (Prod.ext_iff.mp h).2 ⟨l, hl⟩
  -- the chain rule
  have h₁ : I[A : Yc | Xc ; L₀] = I[A : pair Yd Yg | Xc ; L₀] := by
    simp only [condMutualInfo]
    congr 1
    refine (condEntropy_congr_right hL A (fun t : (∀ l : ((dfLt d)ᶜ : Finset (Fin N)), Y l) ×
      (∀ l : ((dfLt d)ᶜ : Finset (Fin N)), X l) => (g t.1, t.2)) (fun a b h => ?_) fun _ =>
        rfl).symm
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hg h.1) h.2
  have h₂ : I[A : pair Yd Yg | Xc ; L₀] = I[A : Yd | Xc ; L₀] +
      I[A : Yg | pair Yd Xc ; L₀] := by
    simp only [condMutualInfo]
    have e : H[A | pair (pair Yd Yg) Xc ; L₀] = H[A | pair Yg (pair Yd Xc) ; L₀] :=
      condEntropy_congr_right hL A (fun t => ((t.2.1, t.1), t.2.2)) (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 (Prod.ext h.1.1 h.2)) fun _ => rfl
    rw [e]
    ring
  have h₃ : I[A : Yg | pair Yd Xc ; L₀] = 0 := hdeg p hp d
  have h₄ : cutInfo p W (dfLt d) = I[A : Yc | Xc ; L₀] := rfl
  have h₅ : dfInfo p W d = I[A : Yd | Xc ; L₀] := rfl
  rw [h₄, h₅, h₁, h₂, h₃, add_zero]

/-- **Page 19-8 of [elgamal2010].** The bound `max_{p(xᴺ)} min_d I(X^{d-1}; Y_d | X_d^N)`, in nats,
where `d` runs over the nodes other than the source. -/
def dfBound (W : (∀ k, X k) → (∀ k, Y k) → ℝ) : ℝ :=
  sSup {v | ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ d : Fin N, (d : ℕ) ≠ 0 → v ≤ dfInfo p W d}

omit [∀ k, Fintype (X k)] in
/-- The rate `0` is achievable, by the code with one message. -/
lemma isAchievableMN_zero [∀ k, Nonempty (X k)] (s : Fin N)
    (D : Finset (Fin N)) : IsAchievableMN W s D 0 := by
  classical
  have h1 : ∀ n k, (2 ^ ⌈(n : ℝ) * mcRate s 0 k⌉₊ : ℕ) = 1 := by
    intro n k
    simp [mcRate]
  refine ⟨fun n => ⟨fun k _ _ _ => Classical.arbitrary _, fun _ _ _ j => ⟨0, by positivity⟩⟩, ?_⟩
  refine tendsto_const_nhds.congr fun n => ?_
  refine (sum_eq_zero fun z _ => ?_).symm
  rw [ind_of_neg, mul_zero]
  rintro ⟨j, k, _, hne⟩
  apply hne
  exact Fin.ext (by
    have h₁ := (z.1 j).isLt
    have h₂ := h1 n j
    simp only at h₁
    omega)

/-- The decode–forward bound is tight when, for each node `d` other than the source, some cut has at
most the information `I(X^{d-1}; Y_d | X_d^N)`. -/
theorem mnCapacity_eq_dfBound [∀ k, Nonempty (X k)] (hW : IsChannel W) {s₀ d₁ k₁ : Fin N}
    (hs : (s₀ : ℕ) = 0) (hd₁ : (d₁ : ℕ) ≠ 0) {D : Finset (Fin N)} (hD : ∀ k ∈ D, (k : ℕ) ≠ 0)
    (hk₁ : k₁ ∈ D)
    (hcut : ∀ p : (∀ k, X k) → ℝ, IsPMF p → ∀ d : Fin N, (d : ℕ) ≠ 0 → ∃ k ∈ D,
      ∃ S : Finset (Fin N), s₀ ∈ S ∧ k ∉ S ∧ cutInfo p W S ≤ dfInfo p W d) :
    mnCapacity W s₀ D * log 2 = dfBound W := by
  classical
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hsk : s₀ ≠ k₁ := fun h => hD k₁ hk₁ (by rw [← h, hs])
  have hbddR := bddAbove_isAchievableMN hW hk₁ hsk
  have hbddV : BddAbove {v | ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ d : Fin N, (d : ℕ) ≠ 0 →
      v ≤ dfInfo p W d} := by
    refine ⟨log (Fintype.card (Y d₁)), ?_⟩
    rintro v ⟨p, hp, h⟩
    refine (h d₁ hd₁).trans ?_
    have hL := jointOf_isPMF hp hW
    have h₁ : dfInfo p W d₁ = _ := condMutualInfo_comm hL _ _ _
    rw [h₁, condMutualInfo_eq' hL]
    have h₂ := condEntropy_nonneg hL (fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d₁)
      (pair (fun ω => restr (dfLt d₁)ᶜ ω.1) fun ω => restr (dfLt d₁) ω.1)
    have h₃ := condEntropy_le_entropy hL (fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d₁)
      fun ω => restr (dfLt d₁)ᶜ ω.1
    have h₄ := entropyRV_le_log_card hL fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d₁
    linarith
  have hC0 : 0 ≤ mnCapacity W s₀ D := le_csSup hbddR (isAchievableMN_zero s₀ D)
  refine le_antisymm ?_ ?_
  · -- the cutset bound
    rw [← le_div_iff₀ hlog]
    have hval0 : 0 ≤ dfBound W := by
      refine le_csSup hbddV ⟨uniformPMF _, uniformPMF_isPMF, fun d _ => ?_⟩
      exact condMutualInfo_nonneg (jointOf_isPMF uniformPMF_isPMF hW) _ _ _
    refine Real.sSup_le (fun R hR => ?_) (div_nonneg hval0 hlog.le)
    rw [le_div_iff₀ hlog]
    obtain ⟨p, hp, hle⟩ := IsAchievableMN.exists_cutset hW hR
    refine le_csSup hbddV ⟨p, hp, fun d hd => ?_⟩
    obtain ⟨k, hk, S, hsS, hkS, hS⟩ := hcut p hp d hd
    exact (hle k hk S hsS hkS).trans hS
  · -- the decode–forward lower bound
    refine Real.sSup_le (fun v hv => ?_) (mul_nonneg hC0 hlog.le)
    obtain ⟨p, hp, hle⟩ := hv
    by_cases hv0 : v ≤ 0
    · exact hv0.trans (mul_nonneg hC0 hlog.le)
    push Not at hv0
    rw [← div_le_iff₀ hlog]
    refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
    by_cases hR0 : 0 ≤ R
    · refine le_csSup hbddR (isAchievableMN_df hp hW hs hD hR0 fun d hd => ?_)
      have := (lt_div_iff₀ hlog).mp hR
      exact this.trans_le (hle d hd)
    · exact (not_le.mp hR0).le.trans hC0

/-- **Page 19-8 of [elgamal2010]: the capacity of a physically degraded network.** The
decode–forward lower bound is tight, when the last node is a destination. -/
theorem mnCapacity_of_degraded [∀ k, Nonempty (X k)] (hW : IsChannel W) (hdeg : IsDegradedNet W)
    {s₀ last : Fin N} (hs : (s₀ : ℕ) = 0) (hlast : ∀ l : Fin N, (l : ℕ) ≤ last)
    (hne : (last : ℕ) ≠ 0) {D : Finset (Fin N)} (hD : ∀ k ∈ D, (k : ℕ) ≠ 0) (hlD : last ∈ D) :
    mnCapacity W s₀ D * log 2 = dfBound W := by
  refine mnCapacity_eq_dfBound hW hs hne hD hlD fun p hp d hd => ⟨last, hlD, dfLt d, ?_, ?_, ?_⟩
  · exact mem_filter.mpr ⟨mem_univ _, by omega⟩
  · have := hlast d
    simp only [dfLt, mem_filter, mem_univ, true_and, not_lt]
    exact this
  · exact (cutInfo_dfLt_eq hW hdeg hp d).le

/-- If the nodes after `d` have one input, and `d` is the only node outside the cut, then the
information across the cut is `I(X^{d-1}; Y_d | X_d^N)`. -/
theorem cutInfo_eq_dfInfo (hW : IsChannel W) {p : (∀ k, X k) → ℝ} (hp : IsPMF p) {d : Fin N}
    (hgt : ∀ k : Fin N, (d : ℕ) < k → Subsingleton (X k)) {S : Finset (Fin N)}
    (hS : (Sᶜ : Finset (Fin N)) = {d}) : cutInfo p W S = dfInfo p W d := by
  classical
  have hL := jointOf_isPMF hp hW
  set L₀ := jointOf p W with hL₀
  have hd : d ∈ Sᶜ := by simp [hS]
  have hmem : ∀ l : (Sᶜ : Finset (Fin N)), (l : Fin N) = d := fun l => by
    have h : (l : Fin N) ∈ ({d} : Finset (Fin N)) := by
      rw [← hS]
      exact l.property
    exact mem_singleton.mp h
  have hdl : d ∈ (dfLt d)ᶜ := by simp [dfLt]
  have hsub : ∀ l : (Sᶜ : Finset (Fin N)), (l : Fin N) ∈ (dfLt d)ᶜ := fun l => by
    rw [hmem l]
    exact hdl
  -- the conditional entropies
  have h₁ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => restr Sᶜ ω.2 | fun ω => restr Sᶜ ω.1 ; L₀] =
      H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | fun ω => restr (dfLt d)ᶜ ω.1 ; L₀] := by
    have e₁ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | fun ω => restr Sᶜ ω.1 ; L₀] =
        H[fun ω : (∀ l, X l) × (∀ l, Y l) => restr Sᶜ ω.2 | fun ω => restr Sᶜ ω.1 ; L₀] :=
      condEntropy_congr_left hL _ (fun z : ∀ l : (Sᶜ : Finset (Fin N)), Y l => z ⟨d, hd⟩)
        (fun a b h => by
          funext l
          have e : l = ⟨d, hd⟩ := Subtype.ext (hmem l)
          rw [e]
          exact h) fun _ => rfl
    rw [← e₁]
    refine condEntropy_congr_right hL _
      (fun b : ∀ l : ((dfLt d)ᶜ : Finset (Fin N)), X l =>
        (fun l => b ⟨l, hsub l⟩ : ∀ l : (Sᶜ : Finset (Fin N)), X l))
      (fun a b h => ?_) fun _ => rfl
    funext l
    by_cases hl : (l : Fin N) = d
    · have := congrFun h ⟨d, hd⟩
      have e : l = ⟨d, hdl⟩ := Subtype.ext hl
      rw [e]
      exact this
    · have hlt : (d : ℕ) < (l : Fin N) := by
        have := l.property
        simp only [dfLt, mem_compl, mem_filter, mem_univ, true_and, not_lt] at this
        have h' : (d : ℕ) ≤ (l : Fin N) := this
        have hne : (d : ℕ) ≠ (l : Fin N) := fun e => hl (Fin.ext e.symm)
        omega
      have := hgt l hlt
      exact Subsingleton.elim _ _
  have h₂ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => restr Sᶜ ω.2 | pair (fun ω => restr Sᶜ ω.1)
      (fun ω => restr S ω.1) ; L₀] =
      H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | pair (fun ω => restr (dfLt d)ᶜ ω.1)
        (fun ω => restr (dfLt d) ω.1) ; L₀] := by
    have e₁ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | pair (fun ω => restr Sᶜ ω.1)
        (fun ω => restr S ω.1) ; L₀] =
        H[fun ω : (∀ l, X l) × (∀ l, Y l) => restr Sᶜ ω.2 | pair (fun ω => restr Sᶜ ω.1)
        (fun ω => restr S ω.1) ; L₀] :=
      condEntropy_congr_left hL _ (fun z : ∀ l : (Sᶜ : Finset (Fin N)), Y l => z ⟨d, hd⟩)
        (fun a b h => by
          funext l
          have e : l = ⟨d, hd⟩ := Subtype.ext (hmem l)
          rw [e]
          exact h) fun _ => rfl
    rw [← e₁]
    have e₂ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | pair (fun ω => restr Sᶜ ω.1)
        (fun ω => restr S ω.1) ; L₀] =
          H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | Prod.fst ; L₀] :=
      condEntropy_congr_right hL _ (fun x : ∀ l, X l => (restr Sᶜ x, restr S x))
        (restr_compl_restr_injective S) fun _ => rfl
    have e₃ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | pair (fun ω => restr (dfLt d)ᶜ ω.1)
        (fun ω => restr (dfLt d) ω.1) ; L₀] =
        H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | Prod.fst ; L₀] :=
      condEntropy_congr_right hL _ (fun x : ∀ l, X l => (restr (dfLt d)ᶜ x, restr (dfLt d) x))
        (restr_compl_restr_injective _) fun _ => rfl
    rw [e₂, e₃]
  rw [cutInfo, dfInfo, condMutualInfo_comm hL, condMutualInfo_eq' hL, condMutualInfo_comm hL,
    condMutualInfo_eq' hL, h₁, h₂]

/-- **Page 19-9 of [elgamal2010]: the relay channel with two destinations.** Both the relay and the
receiver decode the message: the capacity is `max_{p(x₁, x₂)} min {I(X₁; Y₂ | X₂), I(X₁, X₂; Y₃)}`.
The nodes are numbered from `0`, and the last node has one input. -/
theorem mnCapacity_relay_both {X Y : Fin 3 → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
    [∀ k, Nonempty (X k)] [Subsingleton (X 2)] {W : (∀ k, X k) → (∀ k, Y k) → ℝ}
    (hW : IsChannel W) : mnCapacity W 0 {1, 2} * log 2 = dfBound W := by
  classical
  have hS₁ : (({0, 2} : Finset (Fin 3))ᶜ : Finset (Fin 3)) = {1} := by decide
  have hS₂ : (({0, 1} : Finset (Fin 3))ᶜ : Finset (Fin 3)) = {2} := by decide
  refine mnCapacity_eq_dfBound (s₀ := 0) (d₁ := 1) (k₁ := 1) hW rfl (by decide) ?_ (by decide)
    fun p hp d hd => ?_
  · intro k hk
    fin_cases hk <;> decide
  · have hd' : d = 1 ∨ d = 2 := by
      fin_cases d
      · exact absurd rfl hd
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hd' with rfl | rfl
    · refine ⟨1, by decide, {0, 2}, by decide, by decide, ?_⟩
      refine (cutInfo_eq_dfInfo hW hp (fun k hk => ?_) hS₁).le
      have hk2 : k = 2 := by
        fin_cases k
        · exact absurd hk (by decide)
        · exact absurd hk (by decide)
        · rfl
      rw [hk2]
      infer_instance
    · refine ⟨2, by decide, {0, 1}, by decide, by decide, ?_⟩
      refine (cutInfo_eq_dfInfo hW hp (fun k hk => ?_) hS₂).le
      exact absurd hk (by
        have := k.isLt
        change ¬ (2 : ℕ) < k
        omega)

end Degraded

end InfoTheory
