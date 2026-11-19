/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayLossyProtocol

/-!
# Two-way lossy source coding: the choice of the codebooks

For the scheme of Theorem 4 of Lecture 21 of El Gamal and Kim, the codebook and the bins of each
round are chosen one round at a time, for each value of the past, given the choices of the earlier
rounds.

## Main definitions

* `KBook`: the codebooks and the bins.
* `KBook.proto`: the protocol of a book.
* `KBook.Good`: the sources and the past are typical and the earlier rounds are correct.

## Main statements

* `exists_keyed_choice`: the choice of a codebook for each value of a key.
* `KBook.past_update`: changing a later round does not change the past.
* `KBook.good_step₁`, `KBook.good_step₂`: one round.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The choice of a codebook for each key -/

section Choice

variable {A I 𝒟 : Type*} [Fintype A] [Finite I] [Fintype 𝒟] [Nonempty 𝒟]

open Classical in
/-- **The choice of a codebook for each value of a key.** If the expected failure of a random
codebook is at most `η` for the good elements, one can fix a codebook for each key so that
the failure has an expectation of at most `η` on the good elements. -/
theorem exists_keyed_choice {w : A → ℝ} (hw : IsPMF w) (e : A → I) (G : A → Prop)
    (ν : I → 𝒟 → ℝ) (fail : I → 𝒟 → A → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x, G x → IsPMF (ν (e x)) ∧ ∑ D, ν (e x) D * fail (e x) D x ≤ η) :
    ∃ D : I → 𝒟, ∑ x, w x * (if G x then fail (e x) (D (e x)) x else 0) ≤ η := by
  have := Fintype.ofFinite I
  set S : I → Finset A := fun i => univ.filter fun x => G x ∧ e x = i with hS
  have hchoice : ∀ i, ∃ D, ∑ x ∈ S i, w x * fail i D x ≤ η * ∑ x ∈ S i, w x := fun i => by
    by_cases hne : (S i).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hx₀' := (mem_filter.1 hx₀).2
      have hν : IsPMF (ν i) := by
        have := (h x₀ hx₀'.1).1
        rwa [hx₀'.2] at this
      refine exists_le_of_sum_mul_le hν ?_
      calc ∑ D, ν i D * ∑ x ∈ S i, w x * fail i D x
          = ∑ x ∈ S i, w x * ∑ D, ν i D * fail i D x := by
            simp only [mul_sum]
            rw [sum_comm]
            exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
        _ ≤ ∑ x ∈ S i, w x * η := sum_le_sum fun x hx => by
            have hx' := (mem_filter.1 hx).2
            have := (h x hx'.1).2
            rw [hx'.2] at this
            exact mul_le_mul_of_nonneg_left this (hw.nonneg x)
        _ = η * ∑ x ∈ S i, w x := by
            rw [mul_sum]
            exact sum_congr rfl fun _ _ => mul_comm _ _
    · rw [not_nonempty_iff_eq_empty] at hne
      exact ⟨Classical.arbitrary 𝒟, by simp [hne]⟩
  choose D hD using hchoice
  refine ⟨D, ?_⟩
  have hsum : ∑ x, w x * (if G x then fail (e x) (D (e x)) x else 0) =
      ∑ i, ∑ x ∈ S i, w x * fail i (D i) x := by
    have h1 := sum_fiberwise (univ.filter G) e fun x => w x * fail (e x) (D (e x)) x
    have e₁ : ∑ x, w x * (if G x then fail (e x) (D (e x)) x else 0) =
        ∑ x ∈ univ.filter G, w x * fail (e x) (D (e x)) x := by
      rw [sum_filter]
      refine sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [e₁, ← h1]
    refine sum_congr rfl fun i _ => ?_
    rw [filter_filter]
    refine sum_congr rfl fun x hx => ?_
    rw [(mem_filter.1 hx).2.2]
  have hmass : ∑ i, ∑ x ∈ S i, w x ≤ 1 := by
    have h1 := sum_fiberwise (univ.filter G) e w
    have h2 : ∑ x ∈ univ.filter G, w x ≤ ∑ x, w x :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => hw.nonneg x
    rw [hw.sum_eq_one] at h2
    rw [← h1] at h2
    refine le_trans (le_of_eq ?_) h2
    refine sum_congr rfl fun i _ => ?_
    rw [filter_filter]
  rw [hsum]
  calc ∑ i, ∑ x ∈ S i, w x * fail i (D i) x ≤ ∑ i, η * ∑ x ∈ S i, w x :=
        sum_le_sum fun i _ => hD i
    _ = η * ∑ i, ∑ x ∈ S i, w x := (mul_sum _ _ _).symm
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left hmass hη
    _ = η := mul_one η

end Choice

/-! ### Books -/

section Book

universe u

variable {α₁ α₂ : Type u} [Fintype α₁] [Fintype α₂] {υ : Type*} [Fintype υ] [Nonempty υ] {q n : ℕ}

/-- The state letter: the sources and the past before the round `r`. -/
def kState (r : ℕ) (z : α₁ × α₂ × (Fin q → υ)) : (α₁ × α₂) × (Fin q → υ) :=
  ((z.1, z.2.1), truncU r z.2.2)

/-- The codebooks and the bins of the rounds, for each past. -/
abbrev KBook (L M : Fin q → ℕ) (n : ℕ) (υ : Type*) :=
  ∀ l, KPast n q υ → (Fin (L l) → Fin n → υ) × (Fin (L l) → Fin (M l))

variable {L M : Fin q → ℕ} [∀ l, NeZero (L l)]

open Classical in
/-- The protocol of a book: the speaker selects the first codeword typical with the past and its
source, and the other node looks in the bin for a codeword typical with the past and its source. -/
def KBook.proto (B : KBook L M n υ) (spk : Fin q → Bool) (μ : α₁ × α₂ × (Fin q → υ) → ℝ)
    (ε₂ εd : Fin q → ℝ) : KProto spk L M n α₁ α₂ υ where
  word l v := (B l v).1
  bin l v := (B l v).2
  sel₁ l v x₁ := firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2) (fun z => z.1)
    (fun z => z.2.2 l)) (ε₂ l) (zipSeq v x₁)) (B l v).1 0
  sel₂ l v x₂ := firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2) (fun z => z.2.1)
    (fun z => z.2.2 l)) (ε₂ l) (zipSeq v x₂)) (B l v).1 0
  dec₁ l v x₁ := kDec (B l v).2 (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
    (fun z => z.1) (fun z => z.2.2 l)) (εd l) (zipSeq v x₁)) (B l v).1 0
  dec₂ l v x₂ := kDec (B l v).2 (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
    (fun z => z.2.1) (fun z => z.2.2 l)) (εd l) (zipSeq v x₂)) (B l v).1 0

variable {spk : Fin q → Bool} {μ : α₁ × α₂ × (Fin q → υ) → ℝ} {ε₂ εd : Fin q → ℝ}

/-- Changing a later round of a book does not change the past. -/
lemma KBook.past_update (B : KBook L M n υ) (l : Fin q)
    (D : KPast n q υ → (Fin (L l) → Fin n → υ) × (Fin (L l) → Fin (M l)))
    (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) {r : ℕ} (hr : r ≤ l) :
    (KBook.proto (Function.update B l D) spk μ ε₂ εd).past x₁ x₂ r =
      (KBook.proto B spk μ ε₂ εd).past x₁ x₂ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have ih' := ih (by omega)
    simp only [KProto.past]
    split_ifs with h
    · have hne : (⟨r, h⟩ : Fin q) ≠ l := fun e => by
        have : r = l := congrArg Fin.val e
        omega
      rw [ih']
      simp only [KBook.proto, KProto.idx, Function.update_of_ne hne]
    · exact ih'

omit [Fintype υ] in
/-- The past before the next round. -/
lemma truncU_succ (l : Fin q) (u : Fin q → υ) :
    Function.update (truncU l u) l (u l) = truncU (l + 1 : ℕ) u := by
  classical
  funext j
  by_cases hj : j = l
  · subst hj
    simp [truncU]
  · have hne : (j : ℕ) ≠ l := fun h => hj (Fin.ext h)
    have : ((j : ℕ) < l + 1) ↔ ((j : ℕ) < l) := by omega
    simp [truncU, Function.update_of_ne hj, this]

/-- The sources and the past are typical and the rounds before `r` are correct. -/
def KBook.Good (B : KBook L M n υ) (spk : Fin q → Bool) (μ : α₁ × α₂ × (Fin q → υ) → ℝ)
    (ε₂ εd : Fin q → ℝ) (r : ℕ) (ε : ℝ) (ω : Fin n → α₁ × α₂) : Prop :=
  zipSeq ω ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) r) ∈
      robustTypicalSet (dist μ (kState r)) n ε ∧
    ∀ l : Fin q, (l : ℕ) < r → (B.proto spk μ ε₂ εd).Ok (fstSeq ω) (sndSeq ω) l

variable {a b : Type*} [Fintype a] [Fintype b]

omit [Fintype a] [Fintype b] in
/-- The law of the variables of a round, from the state. -/
lemma dist_state_round (l : ℕ) (ξs : α₁ × α₂ → a) (ξo : α₁ × α₂ → b) :
    dist μ (pair (fun z : α₁ × α₂ × (Fin q → υ) => ξo (z.1, z.2.1))
      (pair (fun z => truncU l z.2.2) (fun z => ξs (z.1, z.2.1)))) =
    dist (dist μ (kState l)) fun w => (ξo w.1, w.2, ξs w.1) := by
  rw [← dist_comp_eq]
  rfl

open Classical in
/-- **The choice of the codebook and the bins of one round**, for each past. -/
theorem exists_round_choice {l : Fin q} [NeZero (M l)] (ξs : α₁ × α₂ → a) (ξo : α₁ × α₂ → b)
    {P : α₁ × α₂ → ℝ} (hP : IsPMF P) {ε ε' e₂ η : ℝ} (hη : 0 ≤ η) (key : (Fin n → α₁ × α₂) →
      KPast n q υ) (G : (Fin n → α₁ × α₂) → Prop)
    (hG : ∀ ω, G ω → zipSeq ω (key ω) ∈ robustTypicalSet (dist μ (kState l)) n ε')
    (hR : ∀ (v : Fin n → Fin q → υ) (xs : Fin n → a) (xo : Fin n → b),
      zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ
        (pair (fun z : α₁ × α₂ × (Fin q → υ) => ξo (z.1, z.2.1))
          (pair (fun z => truncU l z.2.2) (fun z => ξs (z.1, z.2.1))))) n ε' →
      IsPMF (iidPMF (channelExt (condDist μ (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l)
        (fun z => truncU l z.2.2)) n v) (L l)) ∧
      ∑ C : Fin (L l) → Fin n → υ, iidPMF (channelExt (condDist μ
        (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l) (fun z => truncU l z.2.2)) n v) (L l) C *
        ∑ Bn : Fin (L l) → Fin (M l), iidPMF (uniformPMF (Fin (M l))) (L l) Bn *
          kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => ξs (z.1, z.2.1)) (fun z => z.2.2 l)) e₂ (zipSeq v xs))
            (condRobustTypicalSet (dist μ (pair (pair (fun z => ξo (z.1, z.2.1))
              (pair (fun z => truncU l z.2.2) (fun z => ξs (z.1, z.2.1)))) (fun z => z.2.2 l))) ε
              (zipSeq xo (zipSeq v xs)))
            (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => ξo (z.1, z.2.1)) (fun z => z.2.2 l)) ε (zipSeq v xo)) 0 C Bn ≤ η) :
    ∃ D : KPast n q υ → (Fin (L l) → Fin n → υ) × (Fin (L l) → Fin (M l)),
      ∑ ω, iidPMF P n ω * (if G ω then
        kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => ξs (z.1, z.2.1)) (fun z => z.2.2 l)) e₂
              (zipSeq (key ω) fun i => ξs (ω i)))
          (condRobustTypicalSet (dist μ (pair (pair (fun z => ξo (z.1, z.2.1))
            (pair (fun z => truncU l z.2.2) (fun z => ξs (z.1, z.2.1)))) (fun z => z.2.2 l))) ε
            (zipSeq (fun i => ξo (ω i)) (zipSeq (key ω) fun i => ξs (ω i))))
          (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => ξo (z.1, z.2.1)) (fun z => z.2.2 l)) ε (zipSeq (key ω) fun i => ξo (ω i))) 0
          (D (key ω)).1 (D (key ω)).2 else 0) ≤ η := by
  have hw := iidPMF_isPMF hP n
  have hneM : Nonempty (Fin (M l)) := ⟨0⟩
  have hne𝒟 : Nonempty ((Fin (L l) → Fin n → υ) × (Fin (L l) → Fin (M l))) :=
    ⟨(fun _ _ => Classical.arbitrary υ, fun _ => 0)⟩
  have ht : ∀ ω, G ω → zipSeq (fun i => ξo (ω i)) (zipSeq (key ω) fun i => ξs (ω i)) ∈
      robustTypicalSet (dist μ (pair (fun z : α₁ × α₂ × (Fin q → υ) => ξo (z.1, z.2.1))
        (pair (fun z => truncU l z.2.2) (fun z => ξs (z.1, z.2.1))))) n ε' := fun ω hω => by
    rw [dist_state_round]
    exact comp_mem_robustTypicalSet (hG ω hω) fun w => (ξo w.1, w.2, ξs w.1)
  exact exists_keyed_choice hw key G
    (fun v => prodDist (iidPMF (channelExt (condDist μ (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l)
      (fun z => truncU l z.2.2)) n v) (L l)) (iidPMF (uniformPMF (Fin (M l))) (L l)))
    (fun v D ω => kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
        (fun z => ξs (z.1, z.2.1)) (fun z => z.2.2 l)) e₂ (zipSeq v fun i => ξs (ω i)))
      (condRobustTypicalSet (dist μ (pair (pair (fun z => ξo (z.1, z.2.1))
        (pair (fun z => truncU l z.2.2) (fun z => ξs (z.1, z.2.1)))) (fun z => z.2.2 l))) ε
        (zipSeq (fun i => ξo (ω i)) (zipSeq v fun i => ξs (ω i))))
      (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
        (fun z => ξo (z.1, z.2.1)) (fun z => z.2.2 l)) ε (zipSeq v fun i => ξo (ω i))) 0 D.1 D.2)
    hη fun ω hω => by
      obtain ⟨h₁, h₂⟩ := hR _ _ _ (ht ω hω)
      refine ⟨h₁.prodDist (iidPMF_isPMF uniformPMF_isPMF _), ?_⟩
      rw [Fintype.sum_prod_type]
      refine le_trans (le_of_eq ?_) h₂
      refine sum_congr rfl fun C _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun Bn _ => ?_
      simp only [prodDist]
      ring

omit [Fintype α₁] [Fintype α₂] [Fintype υ] [∀ l, NeZero (L l)] [Fintype a] [Fintype b] in
lemma kFail_eq_zero_iff {X : Type*} [Finite X] {Lk Mk : ℕ} {A T S : Finset X}
    {C : Fin Lk → X} {Bn : Fin Lk → Fin Mk} {l₀ : Fin Lk} (h : kFail A T S l₀ C Bn = 0) :
    C (firstIn A C l₀) ∈ T ∧ ∀ l' ∈ univ.erase (firstIn A C l₀),
      ¬ (Bn l' = Bn (firstIn A C l₀) ∧ C l' ∈ S) := by
  have := Fintype.ofFinite X
  classical
  by_contra hc
  simp only [kFail] at h
  rw [ite_eq_right hc] at h
  exact one_ne_zero h

/-- Changing a later round of a book does not change whether a round is correct. -/
lemma KBook.ok_update (B : KBook L M n υ) (l : Fin q)
    (D : KPast n q υ → (Fin (L l) → Fin n → υ) × (Fin (L l) → Fin (M l)))
    (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) {l' : Fin q} (hl : (l' : ℕ) < l) :
    (KBook.proto (Function.update B l D) spk μ ε₂ εd).Ok x₁ x₂ l' ↔
      (KBook.proto B spk μ ε₂ εd).Ok x₁ x₂ l' := by
  have hne : l' ≠ l := fun e => by
    rw [e] at hl
    exact lt_irrefl _ hl
  have hp := KBook.past_update (spk := spk) (μ := μ) (ε₂ := ε₂) (εd := εd) B l D x₁ x₂ hl.le
  simp only [KProto.Ok, KProto.msg, KProto.idx, hp]
  simp only [KBook.proto, Function.update_of_ne hne]

/-- The law of the state after a round. -/
lemma dist_round_state (l : Fin q) {a b : Type*} [Fintype a] [Fintype b] (ξs : α₁ × α₂ → a)
    (ξo : α₁ × α₂ → b) (pack : a × b → α₁ × α₂) (hpack : ∀ w, pack (ξs w, ξo w) = w) :
    dist μ (kState (l + 1 : ℕ)) = dist (dist μ (pair (pair (fun z : α₁ × α₂ × (Fin q → υ) =>
        ξo (z.1, z.2.1)) (pair (fun z => truncU l z.2.2) (fun z => ξs (z.1, z.2.1))))
        (fun z => z.2.2 l)))
      (fun w => (pack (w.1.2.2, w.1.1), Function.update w.1.2.1 l w.2)) := by
  rw [← dist_comp_eq]
  congr 1
  funext z
  simp only [Function.comp, pair, kState, hpack, truncU_succ]

open Classical in
/-- **A round of node 1 that does not fail.** -/
lemma KBook.good_succ₁ {l : Fin q} (hs : spk l = true) (B : KBook L M n υ)
    (D : KPast n q υ → (Fin (L l) → Fin n → υ) × (Fin (L l) → Fin (M l))) {ε ε' : ℝ}
    (hd : εd l = ε) {ω : Fin n → α₁ × α₂} (hG : B.Good spk μ ε₂ εd l ε' ω)
    (hT : (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1
        (firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2) (fun z => z.1)
          (fun z => z.2.2 l)) (ε₂ l) (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)
            (fstSeq ω)))
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 0) ∈
      condRobustTypicalSet (dist μ (pair (pair (fun z => z.2.1)
        (pair (fun z => truncU l z.2.2) (fun z => z.1))) (fun z => z.2.2 l))) ε
        (zipSeq (sndSeq ω) (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)
          (fstSeq ω))))
    (hU : ∀ l' ∈ univ.erase (firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
          (fun z => z.1) (fun z => z.2.2 l)) (ε₂ l)
            (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l) (fstSeq ω)))
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 0),
        ¬ ((D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).2 l' =
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).2
            (firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.1) (fun z => z.2.2 l)) (ε₂ l)
                (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l) (fstSeq ω)))
              (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 0) ∧
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 l' ∈
            condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.2.1) (fun z => z.2.2 l)) ε
                (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l) (sndSeq ω)))) :
    KBook.Good (Function.update B l D) spk μ ε₂ εd (l + 1 : ℕ) ε ω := by
  set v := (B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l with hv
  set C := (D v).1 with hC
  set Bn := (D v).2 with hBn
  set lstar := firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2) (fun z => z.1)
    (fun z => z.2.2 l)) (ε₂ l) (zipSeq v (fstSeq ω))) C 0 with hlstar
  have hp' : (KBook.proto (Function.update B l D) spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l = v :=
    KBook.past_update B l D _ _ le_rfl
  have hnext : (KBook.proto (Function.update B l D) spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω)
      (l + 1 : ℕ) = kUpd l v (C lstar) := by
    simp only [KProto.past, dite_eq_left l.isLt, Fin.eta, hp']
    simp only [KBook.proto, KProto.idx, hs, ite_true, Function.update_self]
    rfl
  have hT' := mem_condRobustTypicalSet.1 hT
  constructor
  · rw [hnext, dist_round_state l (Prod.fst : α₁ × α₂ → α₁) (Prod.snd : α₁ × α₂ → α₂) id fun _ =>
    rfl]
    have h₁ := comp_mem_robustTypicalSet hT' fun w => (id (w.1.2.2, w.1.1),
      Function.update w.1.2.1 l w.2)
    have e : zipSeq ω (kUpd l v (C lstar)) = (fun w => (id (w.1.2.2, w.1.1),
        Function.update w.1.2.1 l w.2)) ∘
          zipSeq (zipSeq (sndSeq ω) (zipSeq v (fstSeq ω))) (C lstar) := by
      funext i
      rfl
    rw [e]
    exact h₁
  · intro l' hl'
    by_cases hlt : (l' : ℕ) < l
    · exact (KBook.ok_update B l D _ _ hlt).2 (hG.2 l' hlt)
    · have hl'' : l' = l := Fin.ext (by omega)
      subst hl''
      have hS : C lstar ∈ condRobustTypicalSet (triLaw μ (fun z => truncU l' z.2.2)
          (fun z => z.2.1) (fun z => z.2.2 l')) ε (zipSeq v (sndSeq ω)) := by
        refine mem_condRobustTypicalSet.2 ?_
        have h₁ := comp_mem_robustTypicalSet hT' fun w => ((w.1.2.1, w.1.1), w.2)
        rw [← dist_comp_eq] at h₁
        exact h₁
      have hk := kDec_eq (B := Bn) 0 lstar hS hU
      simp only [KProto.Ok, KProto.msg, KProto.idx, hs, ite_true, hp']
      simp only [KBook.proto, Function.update_self, hd]
      exact hk

/-- **One round of node 1.** -/
theorem KBook.good_step₁ {l : Fin q} [NeZero (M l)] (hs : spk l = true) (B : KBook L M n υ)
    {P : α₁ × α₂ → ℝ} (hP : IsPMF P) {ε ε' η : ℝ} (hη : 0 ≤ η) (hd : εd l = ε)
    (hR : ∀ (v : Fin n → Fin q → υ) (xs : Fin n → α₁) (xo : Fin n → α₂),
      zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ
        (pair (fun z : α₁ × α₂ × (Fin q → υ) => z.2.1)
          (pair (fun z => truncU l z.2.2) (fun z => z.1)))) n ε' →
      IsPMF (iidPMF (channelExt (condDist μ (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l)
        (fun z => truncU l z.2.2)) n v) (L l)) ∧
      ∑ C : Fin (L l) → Fin n → υ, iidPMF (channelExt (condDist μ
        (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l) (fun z => truncU l z.2.2)) n v) (L l) C *
        ∑ Bn : Fin (L l) → Fin (M l), iidPMF (uniformPMF (Fin (M l))) (L l) Bn *
          kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.1) (fun z => z.2.2 l)) (ε₂ l) (zipSeq v xs))
            (condRobustTypicalSet (dist μ (pair (pair (fun z => z.2.1)
              (pair (fun z => truncU l z.2.2) (fun z => z.1))) (fun z => z.2.2 l))) ε
              (zipSeq xo (zipSeq v xs)))
            (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.2.1) (fun z => z.2.2 l)) ε (zipSeq v xo)) 0 C Bn ≤ η) :
    ∃ B' : KBook L M n υ, ∑ ω, iidPMF P n ω *
      (open Classical in if KBook.Good B' spk μ ε₂ εd (l + 1 : ℕ) ε ω then 0 else 1) ≤
      ∑ ω, iidPMF P n ω * (open Classical in if B.Good spk μ ε₂ εd l ε' ω then 0 else 1) + η := by
  classical
  have hw := iidPMF_isPMF hP n
  obtain ⟨key, hkey⟩ : ∃ key : (Fin n → α₁ × α₂) → KPast n q υ,
      key = fun ω => (B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ := exists_round_choice (l := l) (μ := μ) (L := L) (M := M)
    (Prod.fst : α₁ × α₂ → α₁) (Prod.snd : α₁ × α₂ → α₂) hP (ε := ε) (ε' := ε') (e₂ := ε₂ l) hη key
    (B.Good (α₁ := α₁) (α₂ := α₂) spk μ ε₂ εd l ε') (fun ω hω => by
      rw [hkey]
      exact hω.1) hR
  refine ⟨Function.update B l D, ?_⟩
  have hpt : ∀ ω, (if KBook.Good (Function.update B l D) spk μ ε₂ εd (l + 1 : ℕ) ε ω then (0 : ℝ)
      else 1) ≤ (if B.Good spk μ ε₂ εd l ε' ω then (0 : ℝ) else 1) +
      (if B.Good spk μ ε₂ εd l ε' ω then
        kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z : α₁ × α₂ × (Fin q → υ) => z.1) (fun z => z.2.2 l)) (ε₂ l)
              (zipSeq (key ω) (fstSeq ω)))
          (condRobustTypicalSet (dist μ (pair (pair (fun z => z.2.1)
            (pair (fun z => truncU l z.2.2) (fun z => z.1))) (fun z => z.2.2 l))) ε
            (zipSeq (sndSeq ω) (zipSeq (key ω) (fstSeq ω))))
          (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => z.2.1) (fun z => z.2.2 l)) ε (zipSeq (key ω) (sndSeq ω))) 0
          (D (key ω)).1 (D (key ω)).2 else 0) := fun ω => by
    by_cases hGω : B.Good spk μ ε₂ εd l ε' ω
    · rw [ite_eq_left hGω, ite_eq_left hGω, zero_add]
      simp only [kFail]
      split_ifs with h₁ h₂ h₂
      · exact le_rfl
      · exact zero_le_one
      · exfalso
        apply h₁
        subst hkey
        exact KBook.good_succ₁ hs B D hd hGω h₂.1 h₂.2
      · exact le_rfl
    · rw [ite_eq_right hGω, ite_eq_right hGω, add_zero]
      split_ifs <;> norm_num
  refine (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw.nonneg ω)).trans ?_
  simp only [mul_add, sum_add_distrib]
  refine add_le_add le_rfl (le_trans (le_of_eq ?_) hD)
  refine sum_congr rfl fun ω _ => ?_
  congr!

open Classical in
/-- **A round of node 2 that does not fail.** -/
lemma KBook.good_succ₂ {l : Fin q} (hs : spk l = false) (B : KBook L M n υ)
    (D : KPast n q υ → (Fin (L l) → Fin n → υ) × (Fin (L l) → Fin (M l))) {ε ε' : ℝ}
    (hd : εd l = ε) {ω : Fin n → α₁ × α₂} (hG : B.Good spk μ ε₂ εd l ε' ω)
    (hT : (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1
        (firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2) (fun z => z.2.1)
          (fun z => z.2.2 l)) (ε₂ l) (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)
            (sndSeq ω)))
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 0) ∈
      condRobustTypicalSet (dist μ (pair (pair (fun z => z.1)
        (pair (fun z => truncU l z.2.2) (fun z => z.2.1))) (fun z => z.2.2 l))) ε
        (zipSeq (fstSeq ω) (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)
          (sndSeq ω))))
    (hU : ∀ l' ∈ univ.erase (firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
          (fun z => z.2.1) (fun z => z.2.2 l)) (ε₂ l)
            (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l) (sndSeq ω)))
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 0),
        ¬ ((D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).2 l' =
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).2
            (firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.2.1) (fun z => z.2.2 l)) (ε₂ l)
                (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l) (sndSeq ω)))
              (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 0) ∧
          (D ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l)).1 l' ∈
            condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.1) (fun z => z.2.2 l)) ε
                (zipSeq ((B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l) (fstSeq ω)))) :
    KBook.Good (Function.update B l D) spk μ ε₂ εd (l + 1 : ℕ) ε ω := by
  set v := (B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l with hv
  set C := (D v).1 with hC
  set Bn := (D v).2 with hBn
  set lstar := firstIn (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2) (fun z => z.2.1)
    (fun z => z.2.2 l)) (ε₂ l) (zipSeq v (sndSeq ω))) C 0 with hlstar
  have hp' : (KBook.proto (Function.update B l D) spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l = v :=
    KBook.past_update B l D _ _ le_rfl
  have hnext : (KBook.proto (Function.update B l D) spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω)
      (l + 1 : ℕ) = kUpd l v (C lstar) := by
    simp only [KProto.past, dite_eq_left l.isLt, Fin.eta, hp']
    simp only [KBook.proto, KProto.idx, hs, Function.update_self]
    rfl
  have hT' := mem_condRobustTypicalSet.1 hT
  constructor
  · rw [hnext, dist_round_state l (Prod.snd : α₁ × α₂ → α₂) (Prod.fst : α₁ × α₂ → α₁) Prod.swap fun
    _ => rfl]
    have h₁ := comp_mem_robustTypicalSet hT' fun w => (Prod.swap (w.1.2.2, w.1.1),
      Function.update w.1.2.1 l w.2)
    have e : zipSeq ω (kUpd l v (C lstar)) = (fun w => (Prod.swap (w.1.2.2, w.1.1),
        Function.update w.1.2.1 l w.2)) ∘
          zipSeq (zipSeq (fstSeq ω) (zipSeq v (sndSeq ω))) (C lstar) := by
      funext i
      rfl
    rw [e]
    exact h₁
  · intro l' hl'
    by_cases hlt : (l' : ℕ) < l
    · exact (KBook.ok_update B l D _ _ hlt).2 (hG.2 l' hlt)
    · have hl'' : l' = l := Fin.ext (by omega)
      subst hl''
      have hS : C lstar ∈ condRobustTypicalSet (triLaw μ (fun z => truncU l' z.2.2)
          (fun z => z.1) (fun z => z.2.2 l')) ε (zipSeq v (fstSeq ω)) := by
        refine mem_condRobustTypicalSet.2 ?_
        have h₁ := comp_mem_robustTypicalSet hT' fun w => ((w.1.2.1, w.1.1), w.2)
        rw [← dist_comp_eq] at h₁
        exact h₁
      have hk := kDec_eq (B := Bn) 0 lstar hS hU
      simp only [KProto.Ok, KProto.msg, KProto.idx, hs, hp']
      simp only [KBook.proto, Function.update_self, hd]
      exact hk

/-- **One round of node 2.** -/
theorem KBook.good_step₂ {l : Fin q} [NeZero (M l)] (hs : spk l = false) (B : KBook L M n υ)
    {P : α₁ × α₂ → ℝ} (hP : IsPMF P) {ε ε' η : ℝ} (hη : 0 ≤ η) (hd : εd l = ε)
    (hR : ∀ (v : Fin n → Fin q → υ) (xs : Fin n → α₂) (xo : Fin n → α₁),
      zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ
        (pair (fun z : α₁ × α₂ × (Fin q → υ) => z.1)
          (pair (fun z => truncU l z.2.2) (fun z => z.2.1)))) n ε' →
      IsPMF (iidPMF (channelExt (condDist μ (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l)
        (fun z => truncU l z.2.2)) n v) (L l)) ∧
      ∑ C : Fin (L l) → Fin n → υ, iidPMF (channelExt (condDist μ
        (fun z : α₁ × α₂ × (Fin q → υ) => z.2.2 l) (fun z => truncU l z.2.2)) n v) (L l) C *
        ∑ Bn : Fin (L l) → Fin (M l), iidPMF (uniformPMF (Fin (M l))) (L l) Bn *
          kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.2.1) (fun z => z.2.2 l)) (ε₂ l) (zipSeq v xs))
            (condRobustTypicalSet (dist μ (pair (pair (fun z => z.1)
              (pair (fun z => truncU l z.2.2) (fun z => z.2.1))) (fun z => z.2.2 l))) ε
              (zipSeq xo (zipSeq v xs)))
            (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
              (fun z => z.1) (fun z => z.2.2 l)) ε (zipSeq v xo)) 0 C Bn ≤ η) :
    ∃ B' : KBook L M n υ, ∑ ω, iidPMF P n ω *
      (open Classical in if KBook.Good B' spk μ ε₂ εd (l + 1 : ℕ) ε ω then 0 else 1) ≤
      ∑ ω, iidPMF P n ω * (open Classical in if B.Good spk μ ε₂ εd l ε' ω then 0 else 1) + η := by
  classical
  have hw := iidPMF_isPMF hP n
  obtain ⟨key, hkey⟩ : ∃ key : (Fin n → α₁ × α₂) → KPast n q υ,
      key = fun ω => (B.proto spk μ ε₂ εd).past (fstSeq ω) (sndSeq ω) l := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ := exists_round_choice (l := l) (μ := μ) (L := L) (M := M)
    (Prod.snd : α₁ × α₂ → α₂) (Prod.fst : α₁ × α₂ → α₁) hP (ε := ε) (ε' := ε') (e₂ := ε₂ l) hη key
    (B.Good (α₁ := α₁) (α₂ := α₂) spk μ ε₂ εd l ε') (fun ω hω => by
      rw [hkey]
      exact hω.1) hR
  refine ⟨Function.update B l D, ?_⟩
  have hpt : ∀ ω, (if KBook.Good (Function.update B l D) spk μ ε₂ εd (l + 1 : ℕ) ε ω then (0 : ℝ)
      else 1) ≤ (if B.Good spk μ ε₂ εd l ε' ω then (0 : ℝ) else 1) +
      (if B.Good spk μ ε₂ εd l ε' ω then
        kFail (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z : α₁ × α₂ × (Fin q → υ) => z.2.1) (fun z => z.2.2 l)) (ε₂ l)
              (zipSeq (key ω) (sndSeq ω)))
          (condRobustTypicalSet (dist μ (pair (pair (fun z => z.1)
            (pair (fun z => truncU l z.2.2) (fun z => z.2.1))) (fun z => z.2.2 l))) ε
            (zipSeq (fstSeq ω) (zipSeq (key ω) (sndSeq ω))))
          (condRobustTypicalSet (triLaw μ (fun z => truncU l z.2.2)
            (fun z => z.1) (fun z => z.2.2 l)) ε (zipSeq (key ω) (fstSeq ω))) 0
          (D (key ω)).1 (D (key ω)).2 else 0) := fun ω => by
    by_cases hGω : B.Good spk μ ε₂ εd l ε' ω
    · rw [ite_eq_left hGω, ite_eq_left hGω, zero_add]
      simp only [kFail]
      split_ifs with h₁ h₂ h₂
      · exact le_rfl
      · exact zero_le_one
      · exfalso
        apply h₁
        subst hkey
        exact KBook.good_succ₂ hs B D hd hGω h₂.1 h₂.2
      · exact le_rfl
    · rw [ite_eq_right hGω, ite_eq_right hGω, add_zero]
      split_ifs <;> norm_num
  refine (sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw.nonneg ω)).trans ?_
  simp only [mul_add, sum_add_distrib]
  refine add_le_add le_rfl (le_trans (le_of_eq ?_) hD)
  refine sum_congr rfl fun ω _ => ?_
  congr!

end Book

end InfoTheory
