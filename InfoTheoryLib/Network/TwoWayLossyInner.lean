/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayLossyBook

/-!
# Two-way lossy source coding: the achievability of Kaspi's theorem

The achievability of Theorem 4 of Lecture 21 of El Gamal and Kim, on pages 21-22 and 21-23.

## Main statements

* `kaspi_sum_rate₁`, `kaspi_sum_rate₂`: the rate of a node is the sum over its rounds of
  `I(X_s; U_l | U^{l-1}) - I(X_o; U_l | U^{l-1})`.
* `exists_eps_chain`: the parameters of the typicality of the rounds.
* `isAchievableKaspi_of_lt`: **achievability**.
* `kaspiInner_subset_kaspiRegion`: **the inner bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

/-! ### The rates of the rounds -/

section Rates

variable {Ω a b d e : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype d] [Fintype e]
  {μ : Ω → ℝ}

/-- With the Markov chain `B → (A, V) → U`, `I(A; U | B, V) = I(A; U | V) - I(B; U | V)`. -/
lemma condInfo_markov (hμ : IsPMF μ) (A : Ω → a) (B : Ω → b) (U : Ω → d) (V : Ω → e)
    (h : I[B : U | pair A V ; μ] = 0) :
    I[A : U | pair B V ; μ] = I[A : U | V ; μ] - I[B : U | V ; μ] := by
  have h₁ := chain_rule_condMutualInfo hμ U A B V
  have h₂ := chain_rule_condMutualInfo hμ U B A V
  have e₁ : I[U : pair A B | V ; μ] = I[U : pair B A | V ; μ] := by
    rw [condMutualInfo, condMutualInfo]
    congr 1
    exact condEntropy_congr_right hμ U (X := pair (pair B A) V) (X' := pair (pair A B) V)
      (Prod.map Prod.swap id) (Prod.swap_injective.prodMap Function.injective_id) fun _ => rfl
  rw [condMutualInfo_comm hμ U (pair A B), condMutualInfo_comm hμ U (pair B A)] at e₁
  rw [condMutualInfo_comm hμ U (pair A B)] at h₁
  rw [condMutualInfo_comm hμ U (pair B A)] at h₂
  rw [condMutualInfo_comm hμ U B V, condMutualInfo_comm hμ U A (pair B V)] at h₁
  rw [condMutualInfo_comm hμ U A V, condMutualInfo_comm hμ U B (pair A V), h] at h₂
  linarith

variable {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {υ : Type*} [Fintype υ] [Nonempty υ] {q : ℕ}
  {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ} {μ' : α₁ × α₂ × (Fin q → υ) → ℝ}

omit [Fintype υ] [Nonempty υ] in
lemma truncU_top [Nonempty υ] (u : Fin q → υ) : truncU q u = u := by
  funext l
  simp [truncU]

/-- One step of the chain rule for the auxiliary letters. -/
lemma condInfo_truncU_succ {a b : Type*} [Fintype a] [Fintype b] (hμ : IsPMF μ')
    (A : α₁ × α₂ × (Fin q → υ) → a) (B : α₁ × α₂ × (Fin q → υ) → b) (l : Fin q) :
    I[A : fun z => truncU (l + 1 : ℕ) z.2.2 | B ; μ'] =
      I[A : fun z => truncU l z.2.2 | B ; μ'] + I[A : fun z => z.2.2 l |
        pair B (fun z => truncU l z.2.2) ; μ'] := by
  classical
  have h₁ := chain_rule_condMutualInfo hμ A (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l)
    (fun z => truncU l z.2.2) B
  have e₁ : I[A : fun z => truncU (l + 1 : ℕ) z.2.2 | B ; μ'] =
      I[A : pair (fun z => z.2.2 l) (fun z => truncU l z.2.2) | B ; μ'] := by
    rw [condMutualInfo, condMutualInfo]
    congr 1
    refine condEntropy_eq_of_comp hμ _
      (fun w : (Fin q → υ) × b => ((w.1 l, Function.update w.1 l (Classical.arbitrary υ)), w.2))
      (fun w : (υ × (Fin q → υ)) × b => (Function.update w.1.2 l w.1.1, w.2)) ?_ ?_
    · funext z
      simp only [Function.comp, pair]
      refine Prod.ext (Prod.ext ?_ ?_) rfl
      · simp [truncU]
      · funext j
        by_cases hj : j = l
        · subst hj
          simp [truncU]
        · have hne : (j : ℕ) ≠ l := fun h => hj (Fin.ext h)
          have : ((j : ℕ) < l + 1) ↔ ((j : ℕ) < l) := by omega
          simp [truncU, Function.update_of_ne hj, this]
    · funext z
      simp only [Function.comp, pair]
      refine Prod.ext ?_ rfl
      exact (truncU_succ l z.2.2).symm
  have e₂ : I[A : fun z => z.2.2 l | pair (fun z => truncU l z.2.2) B ; μ'] =
      I[A : fun z => z.2.2 l | pair B (fun z => truncU l z.2.2) ; μ'] :=
    condMutualInfo_congr_comp hμ _ _ Prod.swap Prod.swap rfl rfl
  rw [e₁, h₁, e₂]

/-- The information of a round of the speaker. -/
def kInfoS (μ' : α₁ × α₂ × (Fin q → υ) → ℝ) (spk : Fin q → Bool) (l : Fin q) : ℝ :=
  if spk l = true then
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 l | fun z => truncU l z.2.2 ; μ']
  else
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 l | fun z => truncU l z.2.2 ; μ']

/-- The information of a round of the other node. -/
def kInfoO (μ' : α₁ × α₂ × (Fin q → υ) → ℝ) (spk : Fin q → Bool) (l : Fin q) : ℝ :=
  if spk l = true then
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 l | fun z => truncU l z.2.2 ; μ']
  else
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 l | fun z => truncU l z.2.2 ; μ']

/-- The difference of the two informations of a round is an information. -/
lemma kInfo_sub_nonneg (hμ : IsKaspiLaw P spk μ') (l : Fin q) :
    0 ≤ kInfoS μ' spk l - kInfoO μ' spk l := by
  simp only [kInfoS, kInfoO]
  split_ifs with hs
  · rw [← condInfo_markov hμ.isPMF _ _ _ _ (hμ.markov₁ l hs)]
    exact condMutualInfo_nonneg hμ.isPMF _ _ _
  · rw [← condInfo_markov hμ.isPMF _ _ _ _ (hμ.markov₂ l (by simpa using hs))]
    exact condMutualInfo_nonneg hμ.isPMF _ _ _

/-- **The rate of node 1 is the sum over its rounds.** -/
theorem kaspi_sum_rate₁ (hμ : IsKaspiLaw P spk μ') :
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 | fun z => z.2.1 ; μ'] =
      ∑ l with spk l = true, (kInfoS μ' spk l - kInfoO μ' spk l) := by
  classical
  have hp := hμ.isPMF
  have key : ∀ r : ℕ, r ≤ q →
      I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => truncU r z.2.2 | fun z => z.2.1 ; μ'] =
      ∑ l ∈ univ.filter fun l : Fin q => spk l = true ∧ (l : ℕ) < r,
        (kInfoS μ' spk l - kInfoO μ' spk l) := by
    intro r
    induction r with
    | zero =>
      intro _
      have : (univ.filter fun l : Fin q => spk l = true ∧ (l : ℕ) < 0) = ∅ := by
        ext l
        simp
      rw [this, sum_empty, condMutualInfo, sub_eq_zero]
      refine condEntropy_eq_of_comp hp _ (fun w => ((fun _ => Classical.arbitrary υ), w))
        (fun w => w.2) ?_ rfl
      funext z
      simp only [Function.comp, pair]
      refine Prod.ext ?_ rfl
      funext l
      simp [truncU]
    | succ r ih =>
      intro hr
      have hrq : r < q := hr
      have h₁ := condInfo_truncU_succ hp (fun z : α₁ × α₂ × (Fin q → υ) => z.1)
        (fun z => z.2.1) ⟨r, hrq⟩
      have e₀ : ((⟨r, hrq⟩ : Fin q) : ℕ) = r := rfl
      rw [e₀] at h₁
      rw [h₁, ih (by omega)]
      by_cases hs : spk ⟨r, hrq⟩ = true
      · have e : (univ.filter fun l : Fin q => spk l = true ∧ (l : ℕ) < r + 1) =
            insert ⟨r, hrq⟩ (univ.filter fun l : Fin q => spk l = true ∧ (l : ℕ) < r) := by
          ext l
          simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          constructor
          · rintro ⟨h₂, h₃⟩
            by_cases h₄ : (l : ℕ) = r
            · exact Or.inl h₄
            · exact Or.inr ⟨h₂, by omega⟩
          · rintro (h₄ | ⟨h₂, h₃⟩)
            · have : l = ⟨r, hrq⟩ := Fin.ext h₄
              subst this
              exact ⟨hs, by simp⟩
            · exact ⟨h₂, by omega⟩
        rw [e, sum_insert (by simp), add_comm]
        congr 1
        have hmk := hμ.markov₁ ⟨r, hrq⟩ hs
        rw [e₀] at hmk
        have := condInfo_markov hp _ _ _ _ hmk
        simp only [kInfoS, kInfoO, hs, ite_true]
        exact this
      · have e : (univ.filter fun l : Fin q => spk l = true ∧ (l : ℕ) < r + 1) =
            (univ.filter fun l : Fin q => spk l = true ∧ (l : ℕ) < r) := by
          ext l
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨h₂, h₃⟩
            refine ⟨h₂, ?_⟩
            by_contra h₄
            have : l = ⟨r, hrq⟩ := Fin.ext (by omega)
            subst this
            exact hs h₂
          · rintro ⟨h₂, h₃⟩
            exact ⟨h₂, by omega⟩
        rw [e]
        have hmk := hμ.markov₂ ⟨r, hrq⟩ (by simpa using hs)
        rw [e₀] at hmk
        rw [hmk, add_zero]
  have h := key q le_rfl
  have e₁ : (fun z : α₁ × α₂ × (Fin q → υ) => truncU q z.2.2) = fun z => z.2.2 := by
    funext z
    exact truncU_top z.2.2
  rw [e₁] at h
  rw [h]
  refine sum_congr ?_ fun _ _ => rfl
  ext l
  simp

/-- **The rate of node 2 is the sum over its rounds.** -/
theorem kaspi_sum_rate₂ (hμ : IsKaspiLaw P spk μ') :
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 | fun z => z.1 ; μ'] =
      ∑ l with spk l = false, (kInfoS μ' spk l - kInfoO μ' spk l) := by
  classical
  have hp := hμ.isPMF
  have key : ∀ r : ℕ, r ≤ q →
      I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => truncU r z.2.2 | fun z => z.1 ; μ'] =
      ∑ l ∈ univ.filter fun l : Fin q => spk l = false ∧ (l : ℕ) < r,
        (kInfoS μ' spk l - kInfoO μ' spk l) := by
    intro r
    induction r with
    | zero =>
      intro _
      have : (univ.filter fun l : Fin q => spk l = false ∧ (l : ℕ) < 0) = ∅ := by
        ext l
        simp
      rw [this, sum_empty, condMutualInfo, sub_eq_zero]
      refine condEntropy_eq_of_comp hp _ (fun w => ((fun _ => Classical.arbitrary υ), w))
        (fun w => w.2) ?_ rfl
      funext z
      simp only [Function.comp, pair]
      refine Prod.ext ?_ rfl
      funext l
      simp [truncU]
    | succ r ih =>
      intro hr
      have hrq : r < q := hr
      have h₁ := condInfo_truncU_succ hp (fun z : α₁ × α₂ × (Fin q → υ) => z.2.1)
        (fun z => z.1) ⟨r, hrq⟩
      have e₀ : ((⟨r, hrq⟩ : Fin q) : ℕ) = r := rfl
      rw [e₀] at h₁
      rw [h₁, ih (by omega)]
      by_cases hs : spk ⟨r, hrq⟩ = false
      · have e : (univ.filter fun l : Fin q => spk l = false ∧ (l : ℕ) < r + 1) =
            insert ⟨r, hrq⟩ (univ.filter fun l : Fin q => spk l = false ∧ (l : ℕ) < r) := by
          ext l
          simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          constructor
          · rintro ⟨h₂, h₃⟩
            by_cases h₄ : (l : ℕ) = r
            · exact Or.inl h₄
            · exact Or.inr ⟨h₂, by omega⟩
          · rintro (h₄ | ⟨h₂, h₃⟩)
            · have : l = ⟨r, hrq⟩ := Fin.ext h₄
              subst this
              exact ⟨hs, by simp⟩
            · exact ⟨h₂, by omega⟩
        rw [e, sum_insert (by simp), add_comm]
        congr 1
        have hmk := hμ.markov₂ ⟨r, hrq⟩ hs
        rw [e₀] at hmk
        have := condInfo_markov hp _ _ _ _ hmk
        simp only [kInfoS, kInfoO, hs]
        simp only [Bool.false_eq_true, ite_false]
        exact this
      · have hs' : spk ⟨r, hrq⟩ = true := by simpa using hs
        have e : (univ.filter fun l : Fin q => spk l = false ∧ (l : ℕ) < r + 1) =
            (univ.filter fun l : Fin q => spk l = false ∧ (l : ℕ) < r) := by
          ext l
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨h₂, h₃⟩
            refine ⟨h₂, ?_⟩
            by_contra h₄
            have : l = ⟨r, hrq⟩ := Fin.ext (by omega)
            subst this
            exact hs h₂
          · rintro ⟨h₂, h₃⟩
            exact ⟨h₂, by omega⟩
        rw [e]
        have hmk := hμ.markov₁ ⟨r, hrq⟩ hs'
        rw [e₀] at hmk
        rw [hmk, add_zero]
  have h := key q le_rfl
  have e₁ : (fun z : α₁ × α₂ × (Fin q → υ) => truncU q z.2.2) = fun z => z.2.2 := by
    funext z
    exact truncU_top z.2.2
  rw [e₁] at h
  rw [h]
  refine sum_congr ?_ fun _ _ => rfl
  ext l
  simp

end Rates

/-! ### The chain of the typicality parameters -/

section Chain

variable {q : ℕ}

/-- **The chain of the typicality parameters**, from the last round to the first one. -/
theorem exists_eps_chain (Φ : Fin q → ℝ → ℝ → Prop) {εb εt : ℝ} (ht : 0 < εt) (htb : εt ≤ εb)
    (h : ∀ l ε, 0 < ε → ε ≤ εb → ∃ ε', 0 < ε' ∧ ε' ≤ ε ∧ Φ l ε ε') :
    ∃ εs : ℕ → ℝ, (∀ r, 0 < εs r) ∧ (∀ r, εs r ≤ εb) ∧ (∀ r, εs r ≤ εs (r + 1)) ∧ εs q = εt ∧
      ∀ l : Fin q, Φ l (εs (l + 1)) (εs l) := by
  classical
  choose! next hn₀ hn₁ hn₂ using h
  let g : ℕ → ℝ := fun d => Nat.rec εt (fun d y => if hd : d < q then
    next ⟨q - 1 - d, by omega⟩ y else y) d
  have hg0 : g 0 = εt := rfl
  have hgs : ∀ d, g (d + 1) = if hd : d < q then next ⟨q - 1 - d, by omega⟩ (g d) else g d :=
    fun _ => rfl
  have hgp : ∀ d, 0 < g d ∧ g d ≤ εb := by
    intro d
    induction d with
    | zero => exact ⟨ht, htb⟩
    | succ d ih =>
      rw [hgs]
      split_ifs with hd
      · exact ⟨hn₀ _ _ ih.1 ih.2, (hn₁ _ _ ih.1 ih.2).trans ih.2⟩
      · exact ih
  refine ⟨fun r => g (q - r), fun r => (hgp _).1, fun r => (hgp _).2, fun r => ?_, ?_, fun l => ?_⟩
  · by_cases hr : r < q
    · have e : q - r = (q - (r + 1)) + 1 := by omega
      simp only [e]
      rw [hgs, dite_eq_left (by omega)]
      exact hn₁ _ _ (hgp _).1 (hgp _).2
    · have e₁ : q - r = 0 := by omega
      have e₂ : q - (r + 1) = 0 := by omega
      simp only [e₁, e₂, le_refl]
  · simp [hg0]
  · have e : q - (l : ℕ) = (q - ((l : ℕ) + 1)) + 1 := by omega
    have hl := l.2
    simp only [e]
    rw [hgs, dite_eq_left (by omega)]
    have e₂ : (⟨q - 1 - (q - ((l : ℕ) + 1)), by omega⟩ : Fin q) = l := Fin.ext (by
      simp only
      omega)
    rw [e₂]
    exact hn₂ _ _ (hgp _).1 (hgp _).2

end Chain

/-! ### The rounds of a law -/

section Rounds

variable {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {υ : Type*} [Fintype υ] [Nonempty υ] {q : ℕ}
  {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ} {μ : α₁ × α₂ × (Fin q → υ) → ℝ}

/-- The statement of one round for all large `n`, in the form used for the books. -/
def KRound₁ (μ : α₁ × α₂ × (Fin q → υ) → ℝ) (l : Fin q) (rc rm ε ε' e₂ η : ℝ) (n : ℕ) : Prop :=
  open Classical in
  ∀ (M : ℕ) (_ : exp (n * rm) ≤ M) (l₀ : Fin ⌈exp ((n : ℝ) * rc)⌉₊)
    (v : Fin n → Fin q → υ) (xs : Fin n → α₁) (xo : Fin n → α₂),
    zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ
      (pair (fun z : α₁ × α₂ × (Fin q → υ) => z.2.1)
        (pair (fun z => truncU l z.2.2) (fun z => z.1)))) n ε' →
    IsPMF (iidPMF (channelExt (condDist μ (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l)
      (fun z => truncU l z.2.2)) n v) ⌈exp ((n : ℝ) * rc)⌉₊) ∧
    ∑ C : Fin ⌈exp ((n : ℝ) * rc)⌉₊ → Fin n → υ, iidPMF (channelExt (condDist μ
      (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l) (fun z => truncU l z.2.2)) n v)
        ⌈exp ((n : ℝ) * rc)⌉₊ C *
      ∑ Bn : Fin ⌈exp ((n : ℝ) * rc)⌉₊ → Fin M, iidPMF (uniformPMF (Fin M))
          ⌈exp ((n : ℝ) * rc)⌉₊ Bn *
        kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => z.1) (fun z => z.2.2 l)) e₂ (zipSeq v xs))
          (condRobustTypicalSet (dist μ (pair (pair (fun z => z.2.1)
            (pair (fun z => truncU l z.2.2) (fun z => z.1))) (fun z => z.2.2 l))) ε
            (zipSeq xo (zipSeq v xs)))
          (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => z.2.1) (fun z => z.2.2 l)) ε (zipSeq v xo)) l₀ C Bn ≤ η

/-- The statement of one round of node 2. -/
def KRound₂ (μ : α₁ × α₂ × (Fin q → υ) → ℝ) (l : Fin q) (rc rm ε ε' e₂ η : ℝ) (n : ℕ) : Prop :=
  open Classical in
  ∀ (M : ℕ) (_ : exp (n * rm) ≤ M) (l₀ : Fin ⌈exp ((n : ℝ) * rc)⌉₊)
    (v : Fin n → Fin q → υ) (xs : Fin n → α₂) (xo : Fin n → α₁),
    zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ
      (pair (fun z : α₁ × α₂ × (Fin q → υ) => z.1)
        (pair (fun z => truncU l z.2.2) (fun z => z.2.1)))) n ε' →
    IsPMF (iidPMF (channelExt (condDist μ (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l)
      (fun z => truncU l z.2.2)) n v) ⌈exp ((n : ℝ) * rc)⌉₊) ∧
    ∑ C : Fin ⌈exp ((n : ℝ) * rc)⌉₊ → Fin n → υ, iidPMF (channelExt (condDist μ
      (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l) (fun z => truncU l z.2.2)) n v)
        ⌈exp ((n : ℝ) * rc)⌉₊ C *
      ∑ Bn : Fin ⌈exp ((n : ℝ) * rc)⌉₊ → Fin M, iidPMF (uniformPMF (Fin M))
          ⌈exp ((n : ℝ) * rc)⌉₊ Bn *
        kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => z.2.1) (fun z => z.2.2 l)) e₂ (zipSeq v xs))
          (condRobustTypicalSet (dist μ (pair (pair (fun z => z.1)
            (pair (fun z => truncU l z.2.2) (fun z => z.2.1))) (fun z => z.2.2 l))) ε
            (zipSeq xo (zipSeq v xs)))
          (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => z.1) (fun z => z.2.2 l)) ε (zipSeq v xo)) l₀ C Bn ≤ η

/-- The round of a law, for node 1. -/
lemma exists_kaspi_round₁ (hμ : IsKaspiLaw P spk μ) (l : Fin q) (hs : spk l = true) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεc : ε * (2 * log (Fintype.card υ)) ≤ δ) :
    ∃ ε', 0 < ε' ∧ ε' ≤ ε ∧ ∃ e₂ > 0, e₂ ≤ 1 / 2 ∧ ∀ η > 0, ∀ᶠ n : ℕ in atTop,
      KRound₁ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ) ε ε' e₂ η n := by
  have hM : I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 l |
      pair (fun z => truncU l z.2.2) (fun z => z.1) ; μ] = 0 := by
    rw [← hμ.markov₁ l hs]
    exact condMutualInfo_congr_comp hμ.isPMF _ _ Prod.swap Prod.swap rfl rfl
  simp only [kInfoS, kInfoO, hs, ite_true]
  obtain ⟨ε', hε'0, hε'le, e₂, he₂, he₂2, h⟩ := exists_kaspi_round hμ.isPMF hM
    (rm := I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 l |
      fun z => truncU l z.2.2 ; μ] - I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 l |
      fun z => truncU l z.2.2 ; μ] + 3 * δ)
    (rc := I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 l |
      fun z => truncU l z.2.2 ; μ] + δ) (by linarith) hε hε1 (by linarith)
  exact ⟨ε', hε'0, hε'le, e₂, he₂, he₂2, h⟩

/-- The round of a law, for node 2. -/
lemma exists_kaspi_round₂ (hμ : IsKaspiLaw P spk μ) (l : Fin q) (hs : spk l = false) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεc : ε * (2 * log (Fintype.card υ)) ≤ δ) :
    ∃ ε', 0 < ε' ∧ ε' ≤ ε ∧ ∃ e₂ > 0, e₂ ≤ 1 / 2 ∧ ∀ η > 0, ∀ᶠ n : ℕ in atTop,
      KRound₂ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ) ε ε' e₂ η n := by
  have hM : I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 l |
      pair (fun z => truncU l z.2.2) (fun z => z.2.1) ; μ] = 0 := by
    rw [← hμ.markov₂ l hs]
    exact condMutualInfo_congr_comp hμ.isPMF _ _ Prod.swap Prod.swap rfl rfl
  simp only [kInfoS, kInfoO, hs, Bool.false_eq_true, ite_false]
  obtain ⟨ε', hε'0, hε'le, e₂, he₂, he₂2, h⟩ := exists_kaspi_round hμ.isPMF hM
    (rm := I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 l |
      fun z => truncU l z.2.2 ; μ] - I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 l |
      fun z => truncU l z.2.2 ; μ] + 3 * δ)
    (rc := I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 l |
      fun z => truncU l z.2.2 ; μ] + δ) (by linarith) hε hε1 (by linarith)
  exact ⟨ε', hε'0, hε'le, e₂, he₂, he₂2, h⟩

variable {rc rm : Fin q → ℝ} {ε₂ εd : Fin q → ℝ} {n : ℕ}

/-- The law of the state before the first round. -/
lemma dist_state_zero (hm : dist μ (fun z => (z.1, z.2.1)) = P) :
    dist μ (kState 0) = dist P fun w => (w, fun _ : Fin q => Classical.arbitrary υ) := by
  rw [← hm, ← dist_comp_eq]
  rfl

open Classical in
/-- **The codebooks and the bins of all the rounds**, chosen one round at a time. -/
theorem exists_book (hμ : IsKaspiLaw P spk μ) (hP : IsPMF P) {εs : ℕ → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hd : ∀ l : Fin q, εd l = εs (l + 1)) {M : Fin q → ℕ} [∀ l, NeZero (M l)]
    (hM : ∀ l, exp (n * rm l) ≤ M l) (hc : ∀ l, NeZero ⌈exp ((n : ℝ) * rc l)⌉₊)
    (h₁ : ∀ l, spk l = true →
      KRound₁ μ l (rc l) (rm l) (εs (l + 1)) (εs l) (ε₂ l) η n)
    (h₂ : ∀ l, spk l = false →
      KRound₂ μ l (rc l) (rm l) (εs (l + 1)) (εs l) (ε₂ l) η n)
    (h₀ : ∑ ω, iidPMF P n ω * (if ω ∈ robustTypicalSet P n (εs 0) then (0 : ℝ) else 1) ≤ η) :
    ∃ B : KBook (fun l => ⌈exp ((n : ℝ) * rc l)⌉₊) M n υ, ∑ ω, iidPMF P n ω *
      (if B.Good spk μ ε₂ εd q (εs q) ω then 0 else 1) ≤ ((q : ℝ) + 1) * η := by
  have hw := iidPMF_isPMF hP n
  have key : ∀ r : ℕ, r ≤ q → ∃ B : KBook (fun l => ⌈exp ((n : ℝ) * rc l)⌉₊) M n υ,
      ∑ ω, iidPMF P n ω * (if B.Good spk μ ε₂ εd r (εs r) ω then 0 else 1) ≤ ((r : ℝ) + 1) * η := by
    intro r
    induction r with
    | zero =>
      intro _
      set B₀ : KBook (fun l => ⌈exp ((n : ℝ) * rc l)⌉₊) M n υ :=
        fun _ _ => (fun _ _ => Classical.arbitrary υ, fun _ => 0) with hB₀
      have hpt : ∀ ω, (if B₀.Good spk μ ε₂ εd 0 (εs 0) ω then (0 : ℝ) else 1) ≤
          if ω ∈ robustTypicalSet P n (εs 0) then (0 : ℝ) else 1 := fun ω => by
        by_cases hω : ω ∈ robustTypicalSet P n (εs 0)
        · rw [ite_eq_left hω, ite_eq_left]
          refine ⟨?_, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
          have h₃ := comp_mem_robustTypicalSet hω fun w =>
            (w, fun _ : Fin q => Classical.arbitrary υ)
          rw [dist_state_zero hμ.marg]
          exact h₃
        · rw [ite_eq_right hω]
          split_ifs <;> norm_num
      refine ⟨B₀, (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw.nonneg ω)).trans ?_⟩
      simpa using h₀
    | succ r ih =>
      intro hr
      have hrq : r < q := hr
      obtain ⟨B, hB⟩ := ih (by omega)
      set l : Fin q := ⟨r, hrq⟩ with hl
      have e₁ : (l : ℕ) = r := rfl
      by_cases hs : spk l = true
      · obtain ⟨B', hB'⟩ := KBook.good_step₁ (l := l) (ε₂ := ε₂) (εd := εd) (μ := μ) hs B hP
          (ε := εs (l + 1)) (ε' := εs l) hη (hd l)
          fun v xs xo ht => h₁ l hs (M l) (hM l) 0 v xs xo ht
        refine ⟨B', hB'.trans ?_⟩
        rw [e₁]
        push_cast
        linarith
      · have hs' : spk l = false := by simpa using hs
        obtain ⟨B', hB'⟩ := KBook.good_step₂ (l := l) (ε₂ := ε₂) (εd := εd) (μ := μ) hs' B hP
          (ε := εs (l + 1)) (ε' := εs l) hη (hd l)
          fun v xs xo ht => h₂ l hs' (M l) (hM l) 0 v xs xo ht
        refine ⟨B', hB'.trans ?_⟩
        rw [e₁]
        push_cast
        linarith
  exact key q le_rfl

end Rounds

/-! ### The code -/

section Code

variable {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂]
  {υ : Type*} [Fintype υ] [Nonempty υ] {q n : ℕ} {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ}
  {μ : α₁ × α₂ × (Fin q → υ) → ℝ} {ε₂ εd : Fin q → ℝ} {L M : Fin q → ℕ} [∀ l, NeZero (L l)]
  [∀ l, NeZero (M l)]

omit [Fintype β₂] [Fintype β₁] in
open Classical in
/-- **The distortion of `X₁`**, from the probability that a round is not good. -/
theorem KBook.distortion₁_le [Finite β₁] (B : KBook L M n υ) (hP : IsPMF P) (hn : 0 < n)
    [Nonempty β₁] {d₁ : α₁ × α₂ → β₁ → ℝ} (hd : ∀ x y, 0 ≤ d₁ x y) (hμ : IsPMF μ)
    (f₁ : (Fin q → υ) → α₂ → β₁) (f₂ : (Fin q → υ) → α₁ → β₂) {ε : ℝ} (hε : 0 ≤ ε) :
    ((B.proto spk μ ε₂ εd).code f₁ f₂).distortion₁ P d₁ ≤ (1 + ε) * ∑ z, μ z * d₁ (z.1, z.2.1)
    (f₁ z.2.2 z.2.1) + maxDistortion d₁ * ∑ ω, iidPMF P n ω *
    (if B.Good spk μ ε₂ εd q ε ω then 0 else 1) := by
  have := Fintype.ofFinite β₁
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty (α₁ × α₂) := ⟨z₀⟩
  have hw := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := maxDistortion_nonneg hd
  set E := ∑ z, μ z * d₁ (z.1, z.2.1) (f₁ z.2.2 z.2.1) with hE
  have hE0 : 0 ≤ E := sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (hd _ _)
  have hpt : ∀ ω : Fin n → α₁ × α₂, seqDistortion d₁ ω
      (((B.proto spk μ ε₂ εd).code f₁ f₂).dec₁ (fun i => (ω i).2)
        (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2)) ≤
      (1 + ε) * E + maxDistortion d₁ * (if B.Good spk μ ε₂ εd q ε ω then 0 else 1) := fun ω => by
    by_cases hg : B.Good spk μ ε₂ εd q ε ω
    · rw [ite_eq_left hg, mul_zero, add_zero, seqDistortion, div_le_iff₀ hn']
      obtain ⟨h₁, h₂⟩ := (B.proto spk μ ε₂ εd).view_code (f₁ := f₁) (f₂ := f₂)
        (x₁ := fstSeq ω) (x₂ := sndSeq ω) fun l => hg.2 l l.2
      have hs := sum_le_card_mul_of_mem_robustTypicalSet hg.1
        (g := fun w : (α₁ × α₂) × (Fin q → υ) => d₁ w.1 (f₁ w.2 w.1.2)) fun w => hd _ _
      have e₁ : expect (dist μ (kState q)) (fun w : (α₁ × α₂) × (Fin q → υ) =>
          d₁ w.1 (f₁ w.2 w.1.2)) = E := by
        rw [expect]
        simp only [mul_comm (d₁ _ _)]
        rw [sum_dist_mul]
        refine sum_congr rfl fun z _ => ?_
        simp only [kState, truncU_top]
      rw [e₁] at hs
      have e₂ : ∑ i, d₁ (ω i) (((B.proto spk μ ε₂ εd).code f₁ f₂).dec₁ (fun i => (ω i).2)
          (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2) i) =
          ∑ i, (fun w : (α₁ × α₂) × (Fin q → υ) => d₁ w.1 (f₁ w.2 w.1.2))
            (zipSeq ω ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) q) i) := by
        refine sum_congr rfl fun i _ => ?_
        change d₁ (ω i) (f₁ ((B.proto spk μ ε₂ εd).view₂ (sndSeq ω)
          (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fstSeq ω) (sndSeq ω)) q i) (ω i).2) = _
        rw [h₂]
        rfl
      rw [e₂]
      linarith
    · rw [ite_eq_right hg, mul_one]
      have h₁ := seqDistortion_le_maxDistortion d₁ hn ω
        (((B.proto spk μ ε₂ εd).code f₁ f₂).dec₁ (fun i => (ω i).2)
          (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2))
      have h₂ : 0 ≤ (1 + ε) * E := by positivity
      linarith
  simp only [KaspiCode.distortion₁]
  calc _ ≤ ∑ ω, iidPMF P n ω * ((1 + ε) * E + maxDistortion d₁ *
        (if B.Good spk μ ε₂ εd q ε ω then 0 else 1)) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw.nonneg ω)
    _ = _ := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        · rw [← sum_mul, hw.sum_eq_one, one_mul]
        · rw [mul_sum]
          exact sum_congr rfl fun ω _ => by ring

omit [Fintype β₁] [Fintype β₂] in
open Classical in
/-- **The distortion of `X₂`**, from the probability that a round is not good. -/
theorem KBook.distortion₂_le [Finite β₂] (B : KBook L M n υ) (hP : IsPMF P) (hn : 0 < n)
    [Nonempty β₂] {d₂ : α₁ × α₂ → β₂ → ℝ} (hd : ∀ x y, 0 ≤ d₂ x y) (hμ : IsPMF μ)
    (f₁ : (Fin q → υ) → α₂ → β₁) (f₂ : (Fin q → υ) → α₁ → β₂) {ε : ℝ} (hε : 0 ≤ ε) :
    ((B.proto spk μ ε₂ εd).code f₁ f₂).distortion₂ P d₂ ≤ (1 + ε) * ∑ z, μ z * d₂ (z.1, z.2.1)
    (f₂ z.2.2 z.1) + maxDistortion d₂ * ∑ ω, iidPMF P n ω *
    (if B.Good spk μ ε₂ εd q ε ω then 0 else 1) := by
  have := Fintype.ofFinite β₂
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty (α₁ × α₂) := ⟨z₀⟩
  have hw := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := maxDistortion_nonneg hd
  set E := ∑ z, μ z * d₂ (z.1, z.2.1) (f₂ z.2.2 z.1) with hE
  have hE0 : 0 ≤ E := sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (hd _ _)
  have hpt : ∀ ω : Fin n → α₁ × α₂, seqDistortion d₂ ω
      (((B.proto spk μ ε₂ εd).code f₁ f₂).dec₂ (fun i => (ω i).1)
        (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2)) ≤
      (1 + ε) * E + maxDistortion d₂ * (if B.Good spk μ ε₂ εd q ε ω then 0 else 1) := fun ω => by
    by_cases hg : B.Good spk μ ε₂ εd q ε ω
    · rw [ite_eq_left hg, mul_zero, add_zero, seqDistortion, div_le_iff₀ hn']
      obtain ⟨h₁, h₂⟩ := (B.proto spk μ ε₂ εd).view_code (f₁ := f₁) (f₂ := f₂)
        (x₁ := fstSeq ω) (x₂ := sndSeq ω) fun l => hg.2 l l.2
      have hs := sum_le_card_mul_of_mem_robustTypicalSet hg.1
        (g := fun w : (α₁ × α₂) × (Fin q → υ) => d₂ w.1 (f₂ w.2 w.1.1)) fun w => hd _ _
      have e₁ : expect (dist μ (kState q)) (fun w : (α₁ × α₂) × (Fin q → υ) =>
          d₂ w.1 (f₂ w.2 w.1.1)) = E := by
        rw [expect]
        simp only [mul_comm (d₂ _ _)]
        rw [sum_dist_mul]
        refine sum_congr rfl fun z _ => ?_
        simp only [kState, truncU_top]
      rw [e₁] at hs
      have e₂ : ∑ i, d₂ (ω i) (((B.proto spk μ ε₂ εd).code f₁ f₂).dec₂ (fun i => (ω i).1)
          (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2) i) =
          ∑ i, (fun w : (α₁ × α₂) × (Fin q → υ) => d₂ w.1 (f₂ w.2 w.1.1))
            (zipSeq ω ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) q) i) := by
        refine sum_congr rfl fun i _ => ?_
        change d₂ (ω i) (f₂ ((B.proto spk μ ε₂ εd).view₁ (fstSeq ω)
          (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fstSeq ω) (sndSeq ω)) q i) (ω i).1) = _
        rw [h₁]
        rfl
      rw [e₂]
      linarith
    · rw [ite_eq_right hg, mul_one]
      have h₁ := seqDistortion_le_maxDistortion d₂ hn ω
        (((B.proto spk μ ε₂ εd).code f₁ f₂).dec₂ (fun i => (ω i).1)
          (((B.proto spk μ ε₂ εd).code f₁ f₂).trans (fun i => (ω i).1) fun i => (ω i).2))
      have h₂ : 0 ≤ (1 + ε) * E := by positivity
      linarith
  simp only [KaspiCode.distortion₂]
  calc _ ≤ ∑ ω, iidPMF P n ω * ((1 + ε) * E + maxDistortion d₂ *
        (if B.Good spk μ ε₂ εd q ε ω then 0 else 1)) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw.nonneg ω)
    _ = _ := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        · rw [← sum_mul, hw.sum_eq_one, one_mul]
        · rw [mul_sum]
          exact sum_congr rfl fun ω _ => by ring

/-- The product of the sizes of the bins of a node. -/
lemma prod_ceil_exp_le {ι : Type*} (A : Finset ι) (r : ι → ℝ) (hr : ∀ l ∈ A, 0 ≤ r l) {R : ℝ}
    {K : ℝ} (hK : (A.card : ℝ) ≤ K) (hn : ((K + 1) * log 2) + n * ∑ l ∈ A, r l ≤ n * (R * log 2)) :
    ∏ l ∈ A, ⌈exp ((n : ℝ) * r l)⌉₊ ≤ 2 ^ ⌊(n : ℝ) * R⌋₊ := by
  have hl2 := log_pos one_lt_two
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₁ : ((∏ l ∈ A, ⌈exp ((n : ℝ) * r l)⌉₊ : ℕ) : ℝ) ≤
      exp ((n : ℝ) * (R * log 2) - log 2) := by
    push_cast
    refine (prod_le_prod₀ (fun l _ => Nat.cast_nonneg _) fun l hl =>
      ceil_exp_le (mul_nonneg hn0 (hr l hl))).trans ?_
    rw [← exp_sum]
    refine exp_le_exp.2 ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    have := mul_le_mul_of_nonneg_right hK hl2.le
    linarith
  have h₂ := h₁.trans (exp_le_two_pow_floor n R)
  exact_mod_cast h₂

/-- The sizes of the bins of one node, from the sum of its rates. -/
lemma prod_size_le {A : Finset (Fin q)} (sub : Fin q → ℝ) (hsub : ∀ l, 0 ≤ sub l) {I₀ δ R : ℝ}
    (hδ0 : 0 < δ) (hsum : I₀ = ∑ l ∈ A, sub l) (hR : I₀ + (3 * (q : ℝ) + 2) * δ ≤ R * log 2)
    (hns : ((q : ℝ) + 1) * log 2 ≤ n * δ) :
    ∏ l ∈ A, ⌈exp ((n : ℝ) * (sub l + 3 * δ))⌉₊ ≤ 2 ^ ⌊(n : ℝ) * R⌋₊ := by
  have hA : (A.card : ℝ) ≤ q := by
    have := card_le_univ A
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  refine prod_ceil_exp_le A _ (fun l _ => add_nonneg (hsub l) (by positivity)) hA ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e₁ : ∑ l ∈ A, (sub l + 3 * δ) ≤ I₀ + 3 * (q : ℝ) * δ := by
    rw [sum_add_distrib, ← hsum, sum_const, nsmul_eq_mul]
    have : (A.card : ℝ) * (3 * δ) ≤ q * (3 * δ) := mul_le_mul_of_nonneg_right hA (by positivity)
    linarith
  have h₃ := mul_le_mul_of_nonneg_left e₁ hn0
  have h₄ := mul_le_mul_of_nonneg_left hR hn0
  have e₂ : (n : ℝ) * (I₀ + (3 * (q : ℝ) + 2) * δ) =
      n * (I₀ + 3 * (q : ℝ) * δ) + 2 * (n * δ) := by ring
  have h₅ : 0 ≤ (n : ℝ) * δ := mul_nonneg hn0 hδ0.le
  linarith

/-- The arithmetic of the distortions. -/
lemma distortion_arith {E m G Bd εt η Dv ε Q : ℝ} (hm : 0 ≤ m) (hEB : E ≤ Bd)
    (hmB : m ≤ Bd) (hEv : E ≤ Dv) (hεt : 0 ≤ εt) (hη : 0 ≤ Q * η) (hG : G ≤ Q * η)
    (h₁ : εt * Bd ≤ ε / 6) (h₂ : Q * η * Bd = ε / 8) (hε : 0 < ε) :
    (1 + εt) * E + m * G ≤ Dv + ε := by
  have h₃ : εt * E ≤ εt * Bd := mul_le_mul_of_nonneg_left hEB hεt
  have h₄ : m * G ≤ m * (Q * η) := mul_le_mul_of_nonneg_left hG hm
  have h₅ : m * (Q * η) ≤ Bd * (Q * η) := mul_le_mul_of_nonneg_right hmB hη
  have e : Bd * (Q * η) = Q * η * Bd := by ring
  have e₂ : (1 + εt) * E = E + εt * E := by ring
  rw [e₂]
  linarith

/-- The parameters of the rounds. -/
lemma exists_kaspi_params (hμ : IsKaspiLaw P spk μ) {δ εt : ℝ} (hδ : 0 < δ) (hεt0 : 0 < εt)
    (hεt1 : εt ≤ 1) (hεtc : εt * (2 * log (Fintype.card υ)) ≤ δ) :
    ∃ (εs : ℕ → ℝ) (ε₂ : Fin q → ℝ), (∀ r, 0 < εs r) ∧ εs q = εt ∧ ∀ l : Fin q, ∀ η > 0,
      ∀ᶠ n : ℕ in atTop,
      (spk l = true → KRound₁ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
        (εs (l + 1)) (εs l) (ε₂ l) η n) ∧
      (spk l = false → KRound₂ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
        (εs (l + 1)) (εs l) (ε₂ l) η n) := by
  obtain ⟨εs, hεs0, -, -, hεsq, hchain⟩ := exists_eps_chain
    (fun (l : Fin q) e e' => ∃ e₂ > 0, e₂ ≤ 1 / 2 ∧ ∀ η > 0, ∀ᶠ n : ℕ in atTop,
      (spk l = true → KRound₁ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
        e e' e₂ η n) ∧
      (spk l = false → KRound₂ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
        e e' e₂ η n)) hεt0 (le_refl εt) (fun l e he heb => by
      have hec : e * (2 * log (Fintype.card υ)) ≤ δ :=
        (mul_le_mul_of_nonneg_right heb (mul_nonneg (by norm_num)
          (log_natCast_nonneg _))).trans hεtc
      by_cases hs : spk l = true
      · obtain ⟨e', h₁, h₂, e₂, h₃, h₄, h₅⟩ := exists_kaspi_round₁ hμ l hs hδ he (heb.trans hεt1)
          hec
        refine ⟨e', h₁, h₂, e₂, h₃, h₄, fun η hη => ?_⟩
        filter_upwards [h₅ η hη] with n hn
        exact ⟨fun _ => hn, fun hf => by simp [hs] at hf⟩
      · have hs' : spk l = false := by simpa using hs
        obtain ⟨e', h₁, h₂, e₂, h₃, h₄, h₅⟩ := exists_kaspi_round₂ hμ l hs' hδ he (heb.trans hεt1)
          hec
        refine ⟨e', h₁, h₂, e₂, h₃, h₄, fun η hη => ?_⟩
        filter_upwards [h₅ η hη] with n hn
        exact ⟨fun hf => by simp [hs'] at hf, fun _ => hn⟩)
  choose ε₂ _ _ hround using hchain
  exact ⟨εs, ε₂, hεs0, hεsq, hround⟩

omit [Fintype β₁] [Fintype β₂] in
open Classical in
/-- The code for one length. -/
lemma exists_kaspi_code [Finite β₁]
    [Finite β₂] [Nonempty β₁] [Nonempty β₂] (hP : IsPMF P) {d₁ : α₁ × α₂ → β₁ → ℝ}
    {d₂ : α₁ × α₂ → β₂ → ℝ} (hd₁ : ∀ x y, 0 ≤ d₁ x y) (hd₂ : ∀ x y, 0 ≤ d₂ x y)
    (hμ : IsKaspiLaw P spk μ) (f₁ : (Fin q → υ) → α₂ → β₁) (f₂ : (Fin q → υ) → α₁ → β₂)
    {δ η εt : ℝ} (hη : 0 ≤ η) (hεt : 0 ≤ εt) {εs : ℕ → ℝ} (hεsq : εs q = εt)
    {ε₂ : Fin q → ℝ} (hn0 : 0 < n)
    (hrn : ∀ l : Fin q,
      (spk l = true → KRound₁ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
        (εs (l + 1)) (εs l) (ε₂ l) η n) ∧
      (spk l = false → KRound₂ μ l (kInfoS μ spk l + δ) (kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
        (εs (l + 1)) (εs l) (ε₂ l) η n))
    (h₀ : ∑ ω, iidPMF P n ω * (if ω ∈ robustTypicalSet P n (εs 0) then (0 : ℝ) else 1) ≤ η) :
    ∃ (_ : ∀ l : Fin q, NeZero ⌈exp ((n : ℝ) * (kInfoS μ spk l - kInfoO μ spk l + 3 * δ))⌉₊)
      (c : KaspiCode spk (fun l => ⌈exp ((n : ℝ) * (kInfoS μ spk l - kInfoO μ spk l + 3 * δ))⌉₊)
        n α₁ α₂ β₁ β₂),
      c.distortion₁ P d₁ ≤ (1 + εt) * ∑ z, μ z * d₁ (z.1, z.2.1) (f₁ z.2.2 z.2.1) +
        maxDistortion d₁ *
        (((q : ℝ) + 1) * η) ∧
      c.distortion₂ P d₂ ≤ (1 + εt) * ∑ z, μ z * d₂ (z.1, z.2.1) (f₂ z.2.2 z.1) + maxDistortion d₂ *
        (((q : ℝ) + 1) * η) := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty (α₁ × α₂) := ⟨z₀⟩
  have hLne : ∀ l : Fin q, NeZero ⌈exp ((n : ℝ) * (kInfoS μ spk l + δ))⌉₊ := fun l =>
    ⟨(Nat.ceil_pos.2 (exp_pos _)).ne'⟩
  have hMne : ∀ l : Fin q, NeZero ⌈exp ((n : ℝ) * (kInfoS μ spk l - kInfoO μ spk l + 3 * δ))⌉₊ :=
    fun l => ⟨(Nat.ceil_pos.2 (exp_pos _)).ne'⟩
  obtain ⟨B, hB⟩ := exists_book (spk := spk) (μ := μ) (ε₂ := ε₂) (εd := fun l => εs (l + 1))
    (rc := fun l => kInfoS μ spk l + δ) (rm := fun l => kInfoS μ spk l - kInfoO μ spk l + 3 * δ)
    (εs := εs) (M := fun l => ⌈exp ((n : ℝ) * (kInfoS μ spk l - kInfoO μ spk l + 3 * δ))⌉₊)
    hμ hP hη (fun _ => rfl) (fun l => Nat.le_ceil _) hLne (fun l hs => (hrn l).1 hs)
    (fun l hs => (hrn l).2 hs) h₀
  rw [hεsq] at hB
  refine ⟨hMne, (B.proto spk μ ε₂ fun l => εs (l + 1)).code f₁ f₂, ?_, ?_⟩
  · refine (B.distortion₁_le hP hn0 hd₁ hμ.isPMF f₁ f₂ hεt).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (maxDistortion_nonneg hd₁)))
    convert hB
  · refine (B.distortion₂_le hP hn0 hd₂ hμ.isPMF f₁ f₂ hεt).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (maxDistortion_nonneg hd₂)))
    convert hB

omit [Fintype β₁] [Fintype β₂] in
/-- **Theorem 4 of Lecture 21 of [elgamal2010], pages 21-22 and 21-23: achievability.** A rate pair
strictly above the bounds of a law is achievable, by Wyner–Ziv coding in each round. -/
theorem isAchievableKaspi_of_lt [Finite β₁]
    [Finite β₂] [Nonempty β₁] [Nonempty β₂] (hP : IsPMF P) {d₁ : α₁ × α₂ → β₁ → ℝ}
    {d₂ : α₁ × α₂ → β₂ → ℝ} (hd₁ : ∀ x y, 0 ≤ d₁ x y) (hd₂ : ∀ x y, 0 ≤ d₂ x y)
    (hμ : IsKaspiLaw P spk μ) {f₁ : (Fin q → υ) → α₂ → β₁} {f₂ : (Fin q → υ) → α₁ → β₂} {D₁ D₂ : ℝ}
    {R : ℝ × ℝ}
    (hR₁ : I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 | fun z => z.2.1 ; μ] <
      R.1 * log 2)
    (hR₂ : I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 | fun z => z.1 ; μ] <
      R.2 * log 2)
    (hE₁ : ∑ z, μ z * d₁ (z.1, z.2.1) (f₁ z.2.2 z.2.1) ≤ D₁)
      (hE₂ : ∑ z, μ z * d₂ (z.1, z.2.1) (f₂ z.2.2 z.1) ≤ D₂) :
    IsAchievableKaspi P spk d₁ d₂ D₁ D₂ R := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  classical
  have hp := hμ.isPMF
  have hl2 := log_pos one_lt_two
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty (α₁ × α₂) := ⟨z₀⟩
  obtain ⟨I₁, hI₁⟩ : ∃ I₁, I₁ = I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 |
    fun z => z.2.1 ; μ] := ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ I₂, I₂ = I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 |
    fun z => z.1 ; μ] := ⟨_, rfl⟩
  rw [← hI₁] at hR₁
  rw [← hI₂] at hR₂
  have hI₁0 : 0 ≤ I₁ := hI₁ ▸ condMutualInfo_nonneg hp _ _ _
  have hI₂0 : 0 ≤ I₂ := hI₂ ▸ condMutualInfo_nonneg hp _ _ _
  have hR₁0 : 0 ≤ R.1 := by
    by_contra h
    nlinarith [not_le.1 h]
  have hR₂0 : 0 ≤ R.2 := by
    by_contra h
    nlinarith [not_le.1 h]
  refine ⟨hR₁0, hR₂0, fun ε hε => ?_⟩
  -- the margin
  obtain ⟨δ, hδ0, hδ₁, hδ₂⟩ : ∃ δ > 0, I₁ + (3 * (q : ℝ) + 2) * δ ≤ R.1 * log 2 ∧
      I₂ + (3 * (q : ℝ) + 2) * δ ≤ R.2 * log 2 := by
    have hQ0 : 0 < 3 * (q : ℝ) + 2 := by positivity
    refine ⟨min (R.1 * log 2 - I₁) (R.2 * log 2 - I₂) / (3 * (q : ℝ) + 2),
      div_pos (lt_min (by linarith) (by linarith)) hQ0, ?_, ?_⟩
    · have := min_le_left (R.1 * log 2 - I₁) (R.2 * log 2 - I₂)
      rw [mul_div_cancel₀ _ hQ0.ne']
      linarith
    · have := min_le_right (R.1 * log 2 - I₁) (R.2 * log 2 - I₂)
      rw [mul_div_cancel₀ _ hQ0.ne']
      linarith
  -- the parameters
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = (∑ z, μ z * d₁ (z.1, z.2.1) (f₁ z.2.2 z.2.1)) +
      (∑ z, μ z * d₂ (z.1, z.2.1) (f₂ z.2.2 z.1)) + maxDistortion d₁ + maxDistortion d₂ + 1 :=
        ⟨_, rfl⟩
  have hE₁0 : 0 ≤ ∑ z, μ z * d₁ (z.1, z.2.1) (f₁ z.2.2 z.2.1) := sum_nonneg fun z _ =>
    mul_nonneg (hp.nonneg z) (hd₁ _ _)
  have hE₂0 : 0 ≤ ∑ z, μ z * d₂ (z.1, z.2.1) (f₂ z.2.2 z.1) := sum_nonneg fun z _ =>
    mul_nonneg (hp.nonneg z) (hd₂ _ _)
  have hm₁0 := maxDistortion_nonneg hd₁
  have hm₂0 := maxDistortion_nonneg hd₂
  have hBd0 : 0 < Bd := by linarith
  obtain ⟨c, hc⟩ : ∃ c, c = log (Fintype.card υ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ log_natCast_nonneg _
  obtain ⟨εt, hεt⟩ : ∃ εt, εt = min (min 1 (δ / (2 * c + 1))) (ε / (6 * Bd)) := ⟨_, rfl⟩
  have hεt0 : 0 < εt := by
    rw [hεt]
    exact lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hεt1 : εt ≤ 1 := by
    rw [hεt]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hεtc : εt * (2 * log (Fintype.card υ)) ≤ δ := by
    have h₁ : εt ≤ δ / (2 * c + 1) := by
      rw [hεt]
      exact (min_le_left _ _).trans (min_le_right _ _)
    rw [← hc]
    calc εt * (2 * c) ≤ δ / (2 * c + 1) * (2 * c) := mul_le_mul_of_nonneg_right h₁ (by positivity)
      _ ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have hscale : εt * Bd ≤ ε / 6 := by
    have h₁ : εt ≤ ε / (6 * Bd) := by
      rw [hεt]
      exact min_le_right _ _
    calc εt * Bd ≤ ε / (6 * Bd) * Bd := mul_le_mul_of_nonneg_right h₁ hBd0.le
      _ = ε / 6 := by field_simp
  obtain ⟨εs, ε₂, hεs0, hεsq, hround⟩ := exists_kaspi_params (spk := spk) hμ hδ0 hεt0 hεt1 hεtc
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (8 * Bd * ((q : ℝ) + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    positivity
  have hgood : ((q : ℝ) + 1) * η * Bd = ε / 8 := by
    rw [hη]
    field_simp
  have htyp := tendsto_prob_robustTypicalSet hP (hεs0 0)
  have ht : Tendsto (fun n => 1 - prob (iidPMF P n) (robustTypicalSet P n (εs 0))) atTop (𝓝 0) := by
    simpa using htyp.const_sub 1
  have hsize : ∀ᶠ n : ℕ in atTop, ((q : ℝ) + 1) * log 2 ≤ n * δ :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hδ0).eventually_ge_atTop _
  filter_upwards [eventually_all.2 fun l => hround l η hη0, (tendsto_order.1 ht).2 η hη0, hsize,
    eventually_gt_atTop 0] with n hrn hst hns hn0
  have hw := iidPMF_isPMF hP n
  have h₀ : ∑ ω, iidPMF P n ω * (if ω ∈ robustTypicalSet P n (εs 0) then (0 : ℝ) else 1) ≤ η := by
    refine le_trans (le_of_eq ?_) hst.le
    have h2 : prob (iidPMF P n) (robustTypicalSet P n (εs 0)) =
        ∑ x, if x ∈ robustTypicalSet P n (εs 0) then iidPMF P n x else 0 := by
      rw [sum_ite_mem, univ_inter]
      rfl
    rw [h2]
    calc ∑ x, iidPMF P n x * (if x ∈ robustTypicalSet P n (εs 0) then (0 : ℝ) else 1)
        = ∑ x, (iidPMF P n x - if x ∈ robustTypicalSet P n (εs 0) then iidPMF P n x else 0) :=
          sum_congr rfl fun x _ => by split_ifs <;> simp
      _ = _ := by rw [sum_sub_distrib, hw.sum_eq_one]
  obtain ⟨hMne, c', hc₁, hc₂⟩ := exists_kaspi_code hP hd₁ hd₂ hμ f₁ f₂ hη0.le hεt0.le hεsq hn0
    hrn h₀
  have hsub := kInfo_sub_nonneg hμ
  have hQη : 0 ≤ ((q : ℝ) + 1) * η := by positivity
  refine ⟨_, hMne, c', ?_, ?_, ?_, ?_⟩
  · exact prod_size_le _ hsub hδ0 (hI₁.trans (kaspi_sum_rate₁ hμ)) hδ₁ hns
  · exact prod_size_le _ hsub hδ0 (hI₂.trans (kaspi_sum_rate₂ hμ)) hδ₂ hns
  · exact hc₁.trans (distortion_arith hm₁0 (by linarith) (by linarith) hE₁ hεt0.le hQη le_rfl
      hscale hgood hε)
  · exact hc₂.trans (distortion_arith hm₂0 (by linarith) (by linarith) hE₂ hεt0.le hQη le_rfl
      hscale hgood hε)

omit [Fintype β₁] [Fintype β₂] in
/-- **Theorem 4 of Lecture 21 of [elgamal2010], page 21-22: the inner bound.** The region of a law
is contained in the `q`-round rate–distortion region. -/
theorem kaspiInner_subset_kaspiRegion [Finite β₁]
    [Finite β₂] [Nonempty β₁] [Nonempty β₂] (hP : IsPMF P) {d₁ : α₁ × α₂ → β₁ → ℝ}
    {d₂ : α₁ × α₂ → β₂ → ℝ} (hd₁ : ∀ x y, 0 ≤ d₁ x y) (hd₂ : ∀ x y, 0 ≤ d₂ x y) (D₁ D₂ : ℝ) :
    kaspiInner P spk d₁ d₂ D₁ D₂ ⊆ kaspiRegion P spk d₁ d₂ D₁ D₂ := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  rintro ⟨R₁, R₂⟩ ⟨υ', hF, hN, μ', f₁, f₂, hμ, h₁, h₂, hE₁, hE₂⟩
  have hl2 := log_pos one_lt_two
  have hj : ∀ D : ℝ, Tendsto (fun k : ℕ => D + 1 / ((k : ℝ) + 1)) atTop (𝓝 D) := fun D => by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine mem_closure_of_tendsto ((hj R₁).prodMk_nhds (hj R₂)) (Eventually.of_forall fun k => ?_)
  have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  refine isAchievableKaspi_of_lt hP hd₁ hd₂ hμ ?_ ?_ hE₁ hE₂
  · simp only at h₁ ⊢
    nlinarith [mul_pos hp hl2]
  · simp only at h₂ ⊢
    nlinarith [mul_pos hp hl2]

end Code

end InfoTheory
