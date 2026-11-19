/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayLossyRound

/-!
# Two-way lossy source coding: the protocol of the achievability

In each round of the scheme for Theorem 4 of Lecture 21 of El Gamal and Kim, the speaker selects a
codeword given the past and sends its bin, and the other node recovers the codeword. Each node
computes the past from its source and the indices. This file shows that if all the rounds succeed
for the ideal past, computed with the true selections, then the two nodes follow this ideal past.

## Main definitions

* `KProto`: the codewords, bins, selections and decoders of the rounds.
* `KProto.past`: the ideal past.
* `KProto.view₁`, `KProto.view₂`: the past computed by each node.
* `KProto.Ok`: the round is correctly decoded.
* `KProto.code`: the code.

## Main statements

* `KProto.trans_code`, `KProto.view_code`: if all the rounds are correct, the code follows the ideal
  past.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

variable {α₁ α₂ : Type u} {β₁ β₂ : Type*} {υ : Type*} {q : ℕ} {n : ℕ}

/-- The sequences of the letters of the auxiliary variables. -/
abbrev KPast (n q : ℕ) (υ : Type*) := Fin n → Fin q → υ

/-- A letter of the round `l` for each time. -/
def kUpd (l : Fin q) (v : KPast n q υ) (y : Fin n → υ) : KPast n q υ :=
  fun i => Function.update (v i) l (y i)

/-- The data of the rounds of the scheme. -/
structure KProto (spk : Fin q → Bool) (L M : Fin q → ℕ) (n : ℕ) (α₁ α₂ υ : Type*) where
  /-- The codeword of an index, given the past. -/
  word : ∀ l, KPast n q υ → Fin (L l) → Fin n → υ
  /-- The bin of an index, given the past. -/
  bin : ∀ l, KPast n q υ → Fin (L l) → Fin (M l)
  /-- The selection of node 1. -/
  sel₁ : ∀ l, KPast n q υ → (Fin n → α₁) → Fin (L l)
  /-- The selection of node 2. -/
  sel₂ : ∀ l, KPast n q υ → (Fin n → α₂) → Fin (L l)
  /-- The decoder of node 1. -/
  dec₁ : ∀ l, KPast n q υ → (Fin n → α₁) → Fin (M l) → Fin (L l)
  /-- The decoder of node 2. -/
  dec₂ : ∀ l, KPast n q υ → (Fin n → α₂) → Fin (M l) → Fin (L l)

namespace KProto

variable [Nonempty υ] {spk : Fin q → Bool} {L M : Fin q → ℕ} (p : KProto spk L M n α₁ α₂ υ)

/-- The default past. -/
def past₀ : KPast n q υ := fun _ _ => Classical.arbitrary υ

/-- The index of the speaker of the round `l`. -/
def idx (l : Fin q) (v : KPast n q υ) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) : Fin (L l) :=
  if spk l = true then p.sel₁ l v x₁ else p.sel₂ l v x₂

/-- The ideal past before the round `r`. -/
def past (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) : ℕ → KPast n q υ
  | 0 => past₀
  | r + 1 => if hr : r < q then
      kUpd ⟨r, hr⟩ (past x₁ x₂ r) (p.word ⟨r, hr⟩ (past x₁ x₂ r) (p.idx ⟨r, hr⟩ (past x₁ x₂ r) x₁
        x₂))
    else past x₁ x₂ r

/-- The ideal index of the round `l`. -/
def msg (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (l : Fin q) : Fin (M l) :=
  p.bin l (p.past x₁ x₂ l) (p.idx l (p.past x₁ x₂ l) x₁ x₂)

/-- The round `l` is correct: the other node recovers the index of the speaker. -/
def Ok (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (l : Fin q) : Prop :=
  if spk l = true then
    p.dec₂ l (p.past x₁ x₂ l) x₂ (p.msg x₁ x₂ l) = p.sel₁ l (p.past x₁ x₂ l) x₁
  else
    p.dec₁ l (p.past x₁ x₂ l) x₁ (p.msg x₁ x₂ l) = p.sel₂ l (p.past x₁ x₂ l) x₂

/-- The past computed by node 1, from its source and the indices. -/
def view₁ (x₁ : Fin n → α₁) (h : ∀ l, Fin (M l)) : ℕ → KPast n q υ
  | 0 => past₀
  | r + 1 => if hr : r < q then
      kUpd ⟨r, hr⟩ (view₁ x₁ h r) (p.word ⟨r, hr⟩ (view₁ x₁ h r)
        (if spk ⟨r, hr⟩ = true then p.sel₁ ⟨r, hr⟩ (view₁ x₁ h r) x₁
          else p.dec₁ ⟨r, hr⟩ (view₁ x₁ h r) x₁ (h ⟨r, hr⟩)))
    else view₁ x₁ h r

/-- The past computed by node 2, from its source and the indices. -/
def view₂ (x₂ : Fin n → α₂) (h : ∀ l, Fin (M l)) : ℕ → KPast n q υ
  | 0 => past₀
  | r + 1 => if hr : r < q then
      kUpd ⟨r, hr⟩ (view₂ x₂ h r) (p.word ⟨r, hr⟩ (view₂ x₂ h r)
        (if spk ⟨r, hr⟩ = true then p.dec₂ ⟨r, hr⟩ (view₂ x₂ h r) x₂ (h ⟨r, hr⟩)
          else p.sel₂ ⟨r, hr⟩ (view₂ x₂ h r) x₂))
    else view₂ x₂ h r

/-- **The two nodes follow the ideal past** if the rounds are correct and the indices are ideal. -/
lemma view_eq_past {x₁ : Fin n → α₁} {x₂ : Fin n → α₂} {h : ∀ l, Fin (M l)} (r : ℕ)
    (hok : ∀ l : Fin q, (l : ℕ) < r → p.Ok x₁ x₂ l)
    (hh : ∀ l : Fin q, (l : ℕ) < r → h l = p.msg x₁ x₂ l) :
    p.view₁ x₁ h r = p.past x₁ x₂ r ∧ p.view₂ x₂ h r = p.past x₁ x₂ r := by
  induction r with
  | zero => exact ⟨rfl, rfl⟩
  | succ r ih =>
    obtain ⟨h₁, h₂⟩ := ih (fun l hl => hok l (by omega)) fun l hl => hh l (by omega)
    by_cases hr : r < q
    · have hhl : h ⟨r, hr⟩ = p.msg x₁ x₂ ⟨r, hr⟩ := hh ⟨r, hr⟩ (by simp)
      have hokl' : if spk ⟨r, hr⟩ = true then
          p.dec₂ ⟨r, hr⟩ (p.past x₁ x₂ r) x₂ (p.msg x₁ x₂ ⟨r, hr⟩) =
            p.sel₁ ⟨r, hr⟩ (p.past x₁ x₂ r) x₁
        else p.dec₁ ⟨r, hr⟩ (p.past x₁ x₂ r) x₁ (p.msg x₁ x₂ ⟨r, hr⟩) =
            p.sel₂ ⟨r, hr⟩ (p.past x₁ x₂ r) x₂ := hok ⟨r, hr⟩ (by simp)
      constructor
      · simp only [view₁, past, hr, ↓reduceDIte, h₁, hhl, idx]
        by_cases hs : spk ⟨r, hr⟩ = true
        · simp [hs]
        · simp only [hs] at hokl' ⊢
          rw [hokl']
      · simp only [view₂, past, hr, ↓reduceDIte, h₂, hhl, idx]
        by_cases hs : spk ⟨r, hr⟩ = true
        · simp only [hs, ite_true] at hokl' ⊢
          rw [hokl']
        · simp [hs]
    · simp only [view₁, view₂, past, hr, ↓reduceDIte]
      exact ⟨h₁, h₂⟩

variable [∀ l, NeZero (M l)]

/-- The code of the scheme, with the reconstructions `f₁` and `f₂` of the letters. -/
def code (f₁ : (Fin q → υ) → α₂ → β₁) (f₂ : (Fin q → υ) → α₁ → β₂) :
    KaspiCode spk M n α₁ α₂ β₁ β₂ where
  enc₁ l x₁ h := p.bin l (p.view₁ x₁ h l) (p.sel₁ l (p.view₁ x₁ h l) x₁)
  enc₂ l x₂ h := p.bin l (p.view₂ x₂ h l) (p.sel₂ l (p.view₂ x₂ h l) x₂)
  dec₁ x₂ h i := f₁ (p.view₂ x₂ h q i) (x₂ i)
  dec₂ x₁ h i := f₂ (p.view₁ x₁ h q i) (x₁ i)

variable {f₁ : (Fin q → υ) → α₂ → β₁} {f₂ : (Fin q → υ) → α₁ → β₂}

/-- The history of the code is the ideal one, if the rounds are correct. -/
lemma runTo_code {x₁ : Fin n → α₁} {x₂ : Fin n → α₂} (r : ℕ)
    (hok : ∀ l : Fin q, (l : ℕ) < r → p.Ok x₁ x₂ l) :
    ∀ l : Fin q, (l : ℕ) < r →
      runTo ((p.code f₁ f₂).step x₁ x₂) r l = p.msg x₁ x₂ l := by
  induction r with
  | zero => exact fun l hl => absurd hl (Nat.not_lt_zero _)
  | succ r ih =>
    intro l hl
    have ih' := ih fun l hl => hok l (by omega)
    rw [runTo_of_lt _ hl]
    have hprev : ∀ l' : Fin q, (l' : ℕ) < l →
        runTo ((p.code f₁ f₂).step x₁ x₂) l l' = p.msg x₁ x₂ l' := by
      intro l' hl'
      rw [runTo_of_lt _ hl']
      by_cases hle : (l' : ℕ) < r
      · have := ih' l' hle
        rwa [runTo_of_lt _ hle] at this
      · omega
    obtain ⟨h₁, h₂⟩ := p.view_eq_past (h := runTo ((p.code f₁ f₂).step x₁ x₂) l) (l : ℕ)
      (fun l' hl' => hok l' (by omega)) hprev
    set H := runTo ((p.code f₁ f₂).step x₁ x₂) (l : ℕ) with hH
    by_cases hs : spk l = true
    · simp only [KaspiCode.step, hs, ite_true]
      change p.bin l (p.view₁ x₁ H l) (p.sel₁ l (p.view₁ x₁ H l) x₁) = _
      rw [h₁]
      simp [msg, idx, hs]
    · simp only [KaspiCode.step, hs]
      change p.bin l (p.view₂ x₂ H l) (p.sel₂ l (p.view₂ x₂ H l) x₂) = _
      rw [h₂]
      simp [msg, idx, hs]

/-- **The code follows the ideal past**, if all the rounds are correct. -/
theorem trans_code {x₁ : Fin n → α₁} {x₂ : Fin n → α₂} (hok : ∀ l, p.Ok x₁ x₂ l) (l : Fin q) :
    (p.code f₁ f₂).trans x₁ x₂ l = p.msg x₁ x₂ l :=
  p.runTo_code q (fun l _ => hok l) l l.isLt

/-- **The nodes end with the ideal past**, if all the rounds are correct. -/
theorem view_code {x₁ : Fin n → α₁} {x₂ : Fin n → α₂} (hok : ∀ l, p.Ok x₁ x₂ l) :
    p.view₁ x₁ ((p.code f₁ f₂).trans x₁ x₂) q = p.past x₁ x₂ q ∧
      p.view₂ x₂ ((p.code f₁ f₂).trans x₁ x₂) q = p.past x₁ x₂ q :=
  p.view_eq_past q (fun l _ => hok l) fun l _ => p.trans_code hok l

end KProto

end InfoTheory
