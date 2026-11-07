/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MultiWay
public import InfoTheoryLib.RateDistortion.SideInfoConverse

/-!
# Two-way lossless source coding through a relay

Two nodes observe `X₁` and `X₂` and exchange them through a relay, which broadcasts to both.
In each round, each node sends an index to the relay, a function of its source and of the past
broadcasts, and the relay broadcasts a function of all the indices it has received.

We show that the rates of the links must satisfy the cutset bounds, and that any rates above these
bounds are achieved in one round: each node sends its Slepian–Wolf index and the relay broadcasts
the sum of the two indices. The minimum sum rate is
`H(X₁ | X₂) + H(X₂ | X₁) + max {H(X₁ | X₂), H(X₂ | X₁)}`.

## Main definitions

* `TWRCode M₁ M₂ M₃ n α₁ α₂`: a code.
* `IsAchievableTWR`, `twrOptimalRegion`, `twrRegion`: the rate region, and `twrSumRate`.

## Main statements

* `TWRCode.condEntropy_bounds`: the cutset bounds for one code.
* `twrOptimalRegion_eq`: the rate region.
* `twrSumRate_eq`: **the minimum sum rate, page 21-31**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂]

/-- **Lecture 21 of [elgamal2010], page 21-30.** A code for two-way source coding through a relay,
with `r` rounds. -/
structure TWRCode {r : ℕ} (M₁ M₂ M₃ : Fin r → ℕ) (n : ℕ) (α₁ α₂ : Type*) where
  /-- The encoder of node 1, from its source and the past broadcasts. -/
  enc₁ : ∀ l, (Fin n → α₁) → (∀ l', Fin (M₃ l')) → Fin (M₁ l)
  /-- The encoder of node 2. -/
  enc₂ : ∀ l, (Fin n → α₂) → (∀ l', Fin (M₃ l')) → Fin (M₂ l)
  /-- The relay, from the indices it has received. -/
  rel : ∀ l, (∀ l', Fin (M₁ l')) → (∀ l', Fin (M₂ l')) → Fin (M₃ l)
  /-- The decoder of node 1. -/
  dec₁ : (Fin n → α₁) → (∀ l', Fin (M₃ l')) → Fin n → α₂
  /-- The decoder of node 2. -/
  dec₂ : (Fin n → α₂) → (∀ l', Fin (M₃ l')) → Fin n → α₁

namespace TWRCode

variable {r : ℕ} {M₁ M₂ M₃ : Fin r → ℕ} [∀ l, NeZero (M₁ l)] [∀ l, NeZero (M₂ l)]
  [∀ l, NeZero (M₃ l)] {n : ℕ}

/-- The indices of a round. -/
abbrev Round (M₁ M₂ M₃ : Fin r → ℕ) (l : Fin r) := Fin (M₁ l) × Fin (M₂ l) × Fin (M₃ l)

instance : ∀ l, Nonempty (Round M₁ M₂ M₃ l) := fun _ => ⟨(0, 0, 0)⟩

/-- The relay of the round `l`, from the indices of this round and the history. -/
def relStep (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (l : Fin r) (m₁ : Fin (M₁ l)) (m₂ : Fin (M₂ l))
    (h : ∀ l', Round M₁ M₂ M₃ l') : Round M₁ M₂ M₃ l :=
  (m₁, m₂, c.rel l (Function.update (fun l' => (h l').1) l m₁)
    (Function.update (fun l' => (h l').2.1) l m₂))

/-- One round of the protocol. -/
def step (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (l : Fin r)
    (h : ∀ l', Round M₁ M₂ M₃ l') : Round M₁ M₂ M₃ l :=
  c.relStep l (c.enc₁ l x₁ fun l' => (h l').2.2) (c.enc₂ l x₂ fun l' => (h l').2.2) h

/-- The transcript. -/
def trans (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) :
    ∀ l, Round M₁ M₂ M₃ l :=
  run (c.step x₁ x₂)

/-- The broadcasts. -/
def bcast (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) :
    ∀ l, Fin (M₃ l) :=
  fun l => (c.trans x₁ x₂ l).2.2

open Classical in
/-- The probability of error. -/
def errProb (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (P : α₁ × α₂ → ℝ) : ℝ :=
  ∑ ω : Fin n → α₁ × α₂, iidPMF P n ω *
    if c.dec₁ (fun i => (ω i).1) (c.bcast (fun i => (ω i).1) fun i => (ω i).2) ≠
        (fun i => (ω i).2) ∨
      c.dec₂ (fun i => (ω i).2) (c.bcast (fun i => (ω i).1) fun i => (ω i).2) ≠
        (fun i => (ω i).1) then 1 else 0

end TWRCode

/-- **Lecture 21 of [elgamal2010], page 21-30.** A rate triple, in bits, for the links from node 1,
from node 2 and from the relay, is achievable if for every `ε` and all large `n` there is a code
with error at most `ε`, in any number of rounds. -/
def IsAchievableTWR (P : α₁ × α₂ → ℝ) (R : ℝ × ℝ × ℝ) : Prop :=
  0 ≤ R.1 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2 ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (r : ℕ) (M₁ M₂ M₃ : Fin r → ℕ)
    (_ : ∀ l, NeZero (M₁ l)) (_ : ∀ l, NeZero (M₂ l)) (_ : ∀ l, NeZero (M₃ l))
    (c : TWRCode M₁ M₂ M₃ n α₁ α₂), ∏ l, M₁ l ≤ 2 ^ ⌊n * R.1⌋₊ ∧ ∏ l, M₂ l ≤ 2 ^ ⌊n * R.2.1⌋₊ ∧
      ∏ l, M₃ l ≤ 2 ^ ⌊n * R.2.2⌋₊ ∧ c.errProb P ≤ ε

/-- The optimal rate region. -/
def twrOptimalRegion (P : α₁ × α₂ → ℝ) : Set (ℝ × ℝ × ℝ) := closure {R | IsAchievableTWR P R}

/-- The region given by the cutset bounds, in bits. -/
def twrRegion (P : α₁ × α₂ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  {R | H[Prod.fst | Prod.snd ; P] / log 2 ≤ R.1 ∧ H[Prod.snd | Prod.fst ; P] / log 2 ≤ R.2.1 ∧
    H[Prod.fst | Prod.snd ; P] / log 2 ≤ R.2.2 ∧ H[Prod.snd | Prod.fst ; P] / log 2 ≤ R.2.2}

/-- **Page 21-30 of [elgamal2010].** The minimum sum rate, in bits. -/
def twrSumRate (P : α₁ × α₂ → ℝ) : ℝ :=
  sInf ((fun R : ℝ × ℝ × ℝ => R.1 + R.2.1 + R.2.2) '' twrOptimalRegion P)

lemma isClosed_twrRegion (P : α₁ × α₂ → ℝ) : IsClosed (twrRegion P) := by
  have c₁ : Continuous fun R : ℝ × ℝ × ℝ => R.1 := continuous_fst
  have c₂ : Continuous fun R : ℝ × ℝ × ℝ => R.2.1 := continuous_fst.comp continuous_snd
  have c₃ : Continuous fun R : ℝ × ℝ × ℝ => R.2.2 := continuous_snd.comp continuous_snd
  exact (isClosed_le continuous_const c₁).inter ((isClosed_le continuous_const c₂).inter
    ((isClosed_le continuous_const c₃).inter (isClosed_le continuous_const c₃)))

/-! ### The converse -/

section Converse

variable {P : α₁ × α₂ → ℝ} {n : ℕ}

/-- If `X` is decoded from `Z` and `Y`, then `H(X | Y) ≤ log |𝒵| + log 2 + Pₑ log |𝒳|`. -/
lemma condEntropy_le_of_decode {Ω a b z : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype z]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → a) (Y : Ω → b) (Z : Ω → z) (g : z × b → a) :
    H[X | Y ; μ] ≤ log (Fintype.card z) + log 2 +
      InfoTheory.errProb μ X (pair Z Y) g * log (Fintype.card a) := by
  have hc1 := chain_rule_cond hμ X Z Y
  have hc2 := chain_rule_cond hμ Z X Y
  have hswap : H[pair X Z | Y ; μ] = H[pair Z X | Y ; μ] :=
    condEntropy_congr_left hμ Y Prod.swap Prod.swap_injective fun _ => rfl
  have h0 := condEntropy_nonneg hμ Z (pair X Y)
  have h1 := (condEntropy_le_entropy hμ Z Y).trans (entropyRV_le_log_card hμ Z)
  have h2 := fano_weak hμ X (pair Z Y) g
  linarith

/-- `H(X₁ⁿ | X₂ⁿ) = n H(X₁ | X₂)`. -/
lemma condEntropy_iid_fst (hP : IsPMF P) (n : ℕ) :
    H[fun (ω : Fin n → α₁ × α₂) i => (ω i).1 | fun ω i => (ω i).2 ; iidPMF P n] =
      n * H[Prod.fst | Prod.snd ; P] := by
  have hμ := iidPMF_isPMF hP n
  have e1 : H[pair (fun (ω : Fin n → α₁ × α₂) i => (ω i).2) (fun ω i => (ω i).1) ; iidPMF P n] =
      H[fun (ω : Fin n → α₁ × α₂) i => ((ω i).2, (ω i).1) ; iidPMF P n] := by
    refine entropyRV_eq_of_injective _ (fun w => (fun i => (w i).1, fun i => (w i).2)) ?_
      fun _ => rfl
    intro w w' h
    funext i
    exact Prod.ext (congrFun (Prod.mk.inj h).1 i) (congrFun (Prod.mk.inj h).2 i)
  have e2 : H[fun (ω : Fin n → α₁ × α₂) i => (ω i).2 ; iidPMF P n] = n * H[Prod.snd ; P] :=
    entropyRV_iidPMF_comp hP n Prod.snd
  rw [condEntropy_eq_sub hμ, e1, entropyRV_iidPMF_comp hP n (fun z => (z.2, z.1)), e2,
    condEntropy_eq_sub hP]
  have e3 : H[pair Prod.snd Prod.fst ; P] = H[fun z : α₁ × α₂ => (z.2, z.1) ; P] := rfl
  rw [e3]
  ring

/-- `H(X₂ⁿ | X₁ⁿ) = n H(X₂ | X₁)`. -/
lemma condEntropy_iid_snd (hP : IsPMF P) (n : ℕ) :
    H[fun (ω : Fin n → α₁ × α₂) i => (ω i).2 | fun ω i => (ω i).1 ; iidPMF P n] =
      n * H[Prod.snd | Prod.fst ; P] := by
  have hμ := iidPMF_isPMF hP n
  have e1 : H[pair (fun (ω : Fin n → α₁ × α₂) i => (ω i).1) (fun ω i => (ω i).2) ; iidPMF P n] =
      H[fun (ω : Fin n → α₁ × α₂) i => ((ω i).1, (ω i).2) ; iidPMF P n] := by
    refine entropyRV_eq_of_injective _ (fun w => (fun i => (w i).1, fun i => (w i).2)) ?_
      fun _ => rfl
    intro w w' h
    funext i
    exact Prod.ext (congrFun (Prod.mk.inj h).1 i) (congrFun (Prod.mk.inj h).2 i)
  have e2 : H[fun (ω : Fin n → α₁ × α₂) i => (ω i).1 ; iidPMF P n] = n * H[Prod.fst ; P] :=
    entropyRV_iidPMF_comp hP n Prod.fst
  rw [condEntropy_eq_sub hμ, e1, entropyRV_iidPMF_comp hP n (fun z => (z.1, z.2)), e2,
    condEntropy_eq_sub hP]
  have e3 : H[pair Prod.fst Prod.snd ; P] = H[fun z : α₁ × α₂ => (z.1, z.2) ; P] := rfl
  rw [e3]
  ring

variable {r : ℕ} {M₁ M₂ M₃ : Fin r → ℕ} [∀ l, NeZero (M₁ l)] [∀ l, NeZero (M₂ l)]
  [∀ l, NeZero (M₃ l)]

lemma log_card_pi (M : Fin r → ℕ) :
    log (Fintype.card (∀ l, Fin (M l))) = log ((∏ l, M l : ℕ) : ℝ) := by
  rw [Fintype.card_pi]
  simp

namespace TWRCode

omit [Fintype α₁] [Fintype α₂] in
/-- The transcript is determined by the indices of node 1 and the source of node 2. -/
lemma trans_eq_of_fst (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) :
    c.trans x₁ x₂ = run fun l h =>
      c.relStep l ((c.trans x₁ x₂ l).1) (c.enc₂ l x₂ fun l' => (h l').2.2) h := by
  refine run_congr fun l => ?_
  have h := run_apply (c.step x₁ x₂) l
  have h₁ : (c.step x₁ x₂ l (runTo (c.step x₁ x₂) l)).1 = (c.trans x₁ x₂ l).1 :=
    congrArg Prod.fst h.symm
  simp only [step] at h₁ ⊢
  simp only [relStep] at h₁ ⊢
  rw [h₁]

omit [Fintype α₁] [Fintype α₂] in
/-- The transcript is determined by the indices of node 2 and the source of node 1. -/
lemma trans_eq_of_snd (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) :
    c.trans x₁ x₂ = run fun l h =>
      c.relStep l (c.enc₁ l x₁ fun l' => (h l').2.2) ((c.trans x₁ x₂ l).2.1) h := by
  refine run_congr fun l => ?_
  have h := run_apply (c.step x₁ x₂) l
  have h₁ : (c.step x₁ x₂ l (runTo (c.step x₁ x₂) l)).2.1 = (c.trans x₁ x₂ l).2.1 :=
    congrArg (fun z => z.2.1) h.symm
  simp only [step] at h₁ ⊢
  simp only [relStep] at h₁ ⊢
  rw [h₁]

open Classical in
/-- **Page 21-31 of [elgamal2010]: the cutset bounds for one code.** -/
theorem condEntropy_bounds (c : TWRCode M₁ M₂ M₃ n α₁ α₂) (hP : IsPMF P) :
    n * H[Prod.fst | Prod.snd ; P] ≤ log ((∏ l, M₁ l : ℕ) : ℝ) + log 2 +
        c.errProb P * (n * log (Fintype.card α₁)) ∧
    n * H[Prod.snd | Prod.fst ; P] ≤ log ((∏ l, M₂ l : ℕ) : ℝ) + log 2 +
        c.errProb P * (n * log (Fintype.card α₂)) ∧
    n * H[Prod.fst | Prod.snd ; P] ≤ log ((∏ l, M₃ l : ℕ) : ℝ) + log 2 +
        c.errProb P * (n * log (Fintype.card α₁)) ∧
    n * H[Prod.snd | Prod.fst ; P] ≤ log ((∏ l, M₃ l : ℕ) : ℝ) + log 2 +
        c.errProb P * (n * log (Fintype.card α₂)) := by
  have hμ := iidPMF_isPMF hP n
  set X₁ : (Fin n → α₁ × α₂) → Fin n → α₁ := fun ω i => (ω i).1 with hX₁
  set X₂ : (Fin n → α₁ × α₂) → Fin n → α₂ := fun ω i => (ω i).2 with hX₂
  set Er := c.errProb P with hEr
  have hEr0 : 0 ≤ Er := sum_nonneg fun ω _ => mul_nonneg (hμ.nonneg ω) (by split_ifs <;> norm_num)
  have hc₁ : log (Fintype.card (Fin n → α₁)) = n * log (Fintype.card α₁) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  have hc₂ : log (Fintype.card (Fin n → α₂)) = n * log (Fintype.card α₂) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  have hL₁ : 0 ≤ (n : ℝ) * log (Fintype.card α₁) :=
    mul_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg _)
  have hL₂ : 0 ≤ (n : ℝ) * log (Fintype.card α₂) :=
    mul_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg _)
  -- the two errors
  have herr₁ : ∀ {z : Type _} [Fintype z] (Z : (Fin n → α₁ × α₂) → z)
      (g : z × (Fin n → α₂) → Fin n → α₁),
      (∀ ω, g (Z ω, X₂ ω) = c.dec₂ (X₂ ω) (c.bcast (X₁ ω) (X₂ ω))) →
      InfoTheory.errProb (iidPMF P n) X₁ (pair Z X₂) g ≤ Er := by
    intro z _ Z g hg
    refine sum_le_sum fun ω _ => ?_
    have h₀ := hμ.nonneg ω
    have e : g (pair Z X₂ ω) = c.dec₂ (X₂ ω) (c.bcast (X₁ ω) (X₂ ω)) := hg ω
    rw [e]
    by_cases he : c.dec₂ (X₂ ω) (c.bcast (X₁ ω) (X₂ ω)) = X₁ ω
    · simp only [he, ne_eq, not_true_eq_false, ite_false]
      exact mul_nonneg h₀ (by split_ifs <;> norm_num)
    · have h₂ : (c.dec₁ (fun i => (ω i).1) (c.bcast (fun i => (ω i).1) fun i => (ω i).2) ≠
          (fun i => (ω i).2) ∨
        c.dec₂ (fun i => (ω i).2) (c.bcast (fun i => (ω i).1) fun i => (ω i).2) ≠
          (fun i => (ω i).1)) := Or.inr he
      rw [ite_eq_left he, ite_eq_left h₂, mul_one]
  have herr₂ : ∀ {z : Type _} [Fintype z] (Z : (Fin n → α₁ × α₂) → z)
      (g : z × (Fin n → α₁) → Fin n → α₂),
      (∀ ω, g (Z ω, X₁ ω) = c.dec₁ (X₁ ω) (c.bcast (X₁ ω) (X₂ ω))) →
      InfoTheory.errProb (iidPMF P n) X₂ (pair Z X₁) g ≤ Er := by
    intro z _ Z g hg
    refine sum_le_sum fun ω _ => ?_
    have h₀ := hμ.nonneg ω
    have e : g (pair Z X₁ ω) = c.dec₁ (X₁ ω) (c.bcast (X₁ ω) (X₂ ω)) := hg ω
    rw [e]
    by_cases he : c.dec₁ (X₁ ω) (c.bcast (X₁ ω) (X₂ ω)) = X₂ ω
    · simp only [he, ne_eq, not_true_eq_false, ite_false]
      exact mul_nonneg h₀ (by split_ifs <;> norm_num)
    · have h₂ : (c.dec₁ (fun i => (ω i).1) (c.bcast (fun i => (ω i).1) fun i => (ω i).2) ≠
          (fun i => (ω i).2) ∨
        c.dec₂ (fun i => (ω i).2) (c.bcast (fun i => (ω i).1) fun i => (ω i).2) ≠
          (fun i => (ω i).1)) := Or.inl he
      rw [ite_eq_left he, ite_eq_left h₂, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the link from node 1
    set Z : (Fin n → α₁ × α₂) → ∀ l, Fin (M₁ l) := fun ω l => (c.trans (X₁ ω) (X₂ ω) l).1 with hZ
    set g : (∀ l, Fin (M₁ l)) × (Fin n → α₂) → Fin n → α₁ := fun w =>
      c.dec₂ w.2 fun l => (run (fun l h => c.relStep l (w.1 l)
        (c.enc₂ l w.2 fun l' => (h l').2.2) h) l).2.2 with hg
    have h₁ := condEntropy_le_of_decode hμ X₁ X₂ Z g
    rw [condEntropy_iid_fst hP n, hc₁, log_card_pi] at h₁
    have h₂ := herr₁ Z g fun ω => by
      have hrun := c.trans_eq_of_fst (X₁ ω) (X₂ ω)
      simp only [hg, hZ]
      rw [← hrun]
      rfl
    have := mul_le_mul_of_nonneg_right h₂ hL₁
    linarith
  · -- the link from node 2
    set Z : (Fin n → α₁ × α₂) → ∀ l, Fin (M₂ l) := fun ω l => (c.trans (X₁ ω) (X₂ ω) l).2.1 with hZ
    set g : (∀ l, Fin (M₂ l)) × (Fin n → α₁) → Fin n → α₂ := fun w =>
      c.dec₁ w.2 fun l => (run (fun l h => c.relStep l (c.enc₁ l w.2 fun l' => (h l').2.2)
        (w.1 l) h) l).2.2 with hg
    have h₁ := condEntropy_le_of_decode hμ X₂ X₁ Z g
    rw [condEntropy_iid_snd hP n, hc₂, log_card_pi] at h₁
    have h₂ := herr₂ Z g fun ω => by
      have hrun := c.trans_eq_of_snd (X₁ ω) (X₂ ω)
      simp only [hg, hZ]
      rw [← hrun]
      rfl
    have := mul_le_mul_of_nonneg_right h₂ hL₂
    linarith
  · -- the broadcast, for node 2
    set Z : (Fin n → α₁ × α₂) → ∀ l, Fin (M₃ l) := fun ω => c.bcast (X₁ ω) (X₂ ω) with hZ
    have h₁ := condEntropy_le_of_decode hμ X₁ X₂ Z fun w => c.dec₂ w.2 w.1
    rw [condEntropy_iid_fst hP n, hc₁, log_card_pi] at h₁
    have h₂ := herr₁ Z (fun w => c.dec₂ w.2 w.1) fun _ => rfl
    have := mul_le_mul_of_nonneg_right h₂ hL₁
    linarith
  · -- the broadcast, for node 1
    set Z : (Fin n → α₁ × α₂) → ∀ l, Fin (M₃ l) := fun ω => c.bcast (X₁ ω) (X₂ ω) with hZ
    have h₁ := condEntropy_le_of_decode hμ X₂ X₁ Z fun w => c.dec₁ w.2 w.1
    rw [condEntropy_iid_snd hP n, hc₂, log_card_pi] at h₁
    have h₂ := herr₂ Z (fun w => c.dec₁ w.2 w.1) fun _ => rfl
    have := mul_le_mul_of_nonneg_right h₂ hL₂
    linarith

end TWRCode

/-- A bound that holds for small error and all large `n` holds in the limit. -/
lemma le_of_forall_eventually {a b L : ℝ} (hL : 0 ≤ L)
    (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, n * a ≤ n * b + log 2 + ε * (n * L)) : a ≤ b := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (2 * (L + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨n, hn, hn1⟩ := ((h ε hε0).and (eventually_gt_atTop ⌈2 * log 2 / δ⌉₊)).exists
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn2 : log 2 ≤ n * (δ / 2) := by
    have : 2 * log 2 / δ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
    rw [div_lt_iff₀ hδ] at this
    linarith
  have h₃ : ε * L ≤ δ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have key : (n : ℝ) * a ≤ n * (b + δ) := by
    have h₄ : (n : ℝ) * (ε * L) ≤ n * (δ / 2) := mul_le_mul_of_nonneg_left h₃ hn0.le
    nlinarith
  exact le_of_mul_le_mul_left key hn0

/-- **Page 21-31 of [elgamal2010]: the converse.** -/
theorem IsAchievableTWR.mem_twrRegion (hP : IsPMF P) {R : ℝ × ℝ × ℝ} (h : IsAchievableTWR P R) :
    R ∈ twrRegion P := by
  obtain ⟨h₁, h₂, h₃, hc⟩ := h
  have hl := log_pos one_lt_two
  have hsize : ∀ {r : ℕ} (M : Fin r → ℕ) [∀ l, NeZero (M l)] {R' : ℝ} (n : ℕ), 0 ≤ R' →
      ∏ l, M l ≤ 2 ^ ⌊n * R'⌋₊ → log ((∏ l, M l : ℕ) : ℝ) ≤ n * (R' * log 2) := by
    intro r M _ R' n hR' hle
    have hpos : (0 : ℝ) < ((∏ l, M l : ℕ) : ℝ) := by
      have : 0 < ∏ l, M l := prod_pos fun l _ => Nat.pos_of_ne_zero (NeZero.ne _)
      exact_mod_cast this
    refine le_trans (log_le_log hpos ?_) (log_two_pow_floor_le n hR')
    exact_mod_cast hle
  have key : ∀ (a R' L : ℝ), 0 ≤ L → (∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      n * a ≤ n * (R' * log 2) + log 2 + ε * (n * L)) → a / log 2 ≤ R' := by
    intro a R' L hL h'
    rw [div_le_iff₀ hl]
    exact le_of_forall_eventually hL h'
  have hmono : ∀ {ε e L' : ℝ}, e ≤ ε → 0 ≤ L' → e * L' ≤ ε * L' := fun he hL =>
    mul_le_mul_of_nonneg_right he hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine key _ _ (log (Fintype.card α₁)) (log_natCast_nonneg _) fun ε hε => ?_
    filter_upwards [hc ε hε] with n hn
    obtain ⟨r, M₁, M₂, M₃, _, _, _, c, s₁, -, -, he⟩ := hn
    have hb := (c.condEntropy_bounds hP).1
    have := hsize M₁ n h₁ s₁
    have := hmono (L' := (n : ℝ) * log (Fintype.card α₁)) he
      (mul_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg _))
    linarith
  · refine key _ _ (log (Fintype.card α₂)) (log_natCast_nonneg _) fun ε hε => ?_
    filter_upwards [hc ε hε] with n hn
    obtain ⟨r, M₁, M₂, M₃, _, _, _, c, -, s₂, -, he⟩ := hn
    have hb := (c.condEntropy_bounds hP).2.1
    have := hsize M₂ n h₂ s₂
    have := hmono (L' := (n : ℝ) * log (Fintype.card α₂)) he
      (mul_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg _))
    linarith
  · refine key _ _ (log (Fintype.card α₁)) (log_natCast_nonneg _) fun ε hε => ?_
    filter_upwards [hc ε hε] with n hn
    obtain ⟨r, M₁, M₂, M₃, _, _, _, c, -, -, s₃, he⟩ := hn
    have hb := (c.condEntropy_bounds hP).2.2.1
    have := hsize M₃ n h₃ s₃
    have := hmono (L' := (n : ℝ) * log (Fintype.card α₁)) he
      (mul_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg _))
    linarith
  · refine key _ _ (log (Fintype.card α₂)) (log_natCast_nonneg _) fun ε hε => ?_
    filter_upwards [hc ε hε] with n hn
    obtain ⟨r, M₁, M₂, M₃, _, _, _, c, -, -, s₃, he⟩ := hn
    have hb := (c.condEntropy_bounds hP).2.2.2
    have := hsize M₃ n h₃ s₃
    have := hmono (L' := (n : ℝ) * log (Fintype.card α₂)) he
      (mul_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg _))
    linarith

end Converse

/-! ### Achievability -/

section Achievability

variable {P : α₁ × α₂ → ℝ}

/-- The sum of two indices, in the broadcast alphabet. -/
def addFin {A B K : ℕ} [NeZero K] (a : Fin A) (b : Fin B) : Fin K :=
  ⟨((a : ℕ) + b) % K, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne K))⟩

/-- The index of the other node, from the broadcast and the own index. -/
def subFin {A B K : ℕ} [NeZero B] (t : Fin K) (a : Fin A) : Fin B :=
  if h : ((t : ℕ) + K - a) % K < B then ⟨_, h⟩ else 0

lemma add_mod_sub_mod {a b K : ℕ} (ha : a < K) (hb : b < K) : ((a + b) % K + K - a) % K = b := by
  by_cases h : a + b < K
  · rw [Nat.mod_eq_of_lt h]
    have e : a + b + K - a = b + K := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · have e₁ : (a + b) % K = a + b - K := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e₁]
    have e : a + b - K + K - a = b := by omega
    rw [e, Nat.mod_eq_of_lt hb]

lemma subFin_addFin_left {A B K : ℕ} [NeZero B] [NeZero K] (hA : A ≤ K) (hB : B ≤ K) (a : Fin A)
    (b : Fin B) : subFin (addFin a b : Fin K) a = b := by
  have e : (((addFin a b : Fin K) : ℕ) + K - a) % K = b :=
    add_mod_sub_mod (a.2.trans_le hA) (b.2.trans_le hB)
  simp only [subFin, e, b.2, ↓reduceDIte]

lemma subFin_addFin_right {A B K : ℕ} [NeZero A] [NeZero K] (hA : A ≤ K) (hB : B ≤ K) (a : Fin A)
    (b : Fin B) : subFin (addFin a b : Fin K) b = a := by
  have e : (((addFin a b : Fin K) : ℕ) + K - b) % K = a := by
    have := add_mod_sub_mod (b.2.trans_le hB) (a.2.trans_le hA)
    rwa [Nat.add_comm (b : ℕ)] at this
  simp only [subFin, e, a.2, ↓reduceDIte]

lemma dist_swap_apply (P : α₁ × α₂ → ℝ) (z : α₂ × α₁) : dist P Prod.swap z = P z.swap := by
  classical
  simp only [dist]
  rw [sum_eq_single z.swap]
  · simp
  · intro w _ hw
    rw [ite_eq_right]
    intro h
    exact hw (by rw [← h, Prod.swap_swap])
  · simp

/-- **Page 21-31 of [elgamal2010]: Slepian–Wolf coding and network coding.** -/
theorem isAchievableTWR_of_lt (hP : IsPMF P) {R : ℝ × ℝ × ℝ}
    (h₁ : H[Prod.fst | Prod.snd ; P] / log 2 < R.1)
    (h₂ : H[Prod.snd | Prod.fst ; P] / log 2 < R.2.1)
    (h₃ : H[Prod.fst | Prod.snd ; P] / log 2 < R.2.2)
    (h₄ : H[Prod.snd | Prod.fst ; P] / log 2 < R.2.2) : IsAchievableTWR P R := by
  classical
  have hl := log_pos one_lt_two
  have hH₁ : 0 ≤ H[Prod.fst | Prod.snd ; P] / log 2 :=
    div_nonneg (condEntropy_nonneg hP _ _) hl.le
  have hH₂ : 0 ≤ H[Prod.snd | Prod.fst ; P] / log 2 :=
    div_nonneg (condEntropy_nonneg hP _ _) hl.le
  set P' : α₂ × α₁ → ℝ := dist P Prod.swap with hP'
  have hP'p : IsPMF P' := hP.dist _
  have eH : H[Prod.fst | Prod.snd ; P'] = H[Prod.snd | Prod.fst ; P] := by
    refine condEntropy_eq_of_dist_pair_eq hP'p hP ?_
    rw [hP', ← dist_comp_eq]
    rfl
  set r₁ := min R.1 R.2.2 with hr₁
  set r₂ := min R.2.1 R.2.2 with hr₂
  obtain ⟨hr₁0, c₁, hc₁⟩ := isLosslessWZBits_of_condEntropy_lt hP (R := r₁) (lt_min h₁ h₃)
  obtain ⟨hr₂0, c₂, hc₂⟩ := isLosslessWZBits_of_condEntropy_lt hP'p (R := r₂)
    (by rw [eH]; exact lt_min h₂ h₄)
  have hR₁ : 0 ≤ R.1 := hH₁.trans h₁.le
  have hR₂ : 0 ≤ R.2.1 := hH₂.trans h₂.le
  have hR₃ : 0 ≤ R.2.2 := hH₁.trans h₃.le
  refine ⟨hR₁, hR₂, hR₃, fun ε hε => ?_⟩
  filter_upwards [(tendsto_order.1 hc₁).2 (ε / 2) (by positivity),
    (tendsto_order.1 hc₂).2 (ε / 2) (by positivity)] with n he₁ he₂
  set A := 2 ^ ⌊(n : ℝ) * r₁⌋₊ with hA
  set B := 2 ^ ⌊(n : ℝ) * r₂⌋₊ with hB
  set K := 2 ^ ⌊(n : ℝ) * R.2.2⌋₊ with hK
  have hAne : NeZero A := ⟨by positivity⟩
  have hBne : NeZero B := ⟨by positivity⟩
  have hKne : NeZero K := ⟨by positivity⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfloor : ∀ {a b : ℝ}, a ≤ b → 2 ^ ⌊(n : ℝ) * a⌋₊ ≤ 2 ^ ⌊(n : ℝ) * b⌋₊ := fun hab =>
    Nat.pow_le_pow_right (by norm_num) (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hab hn0))
  have hAK : A ≤ K := hfloor (min_le_right _ _)
  have hBK : B ≤ K := hfloor (min_le_right _ _)
  let c : TWRCode (fun _ : Fin 1 => A) (fun _ : Fin 1 => B) (fun _ : Fin 1 => K) n α₁ α₂ :=
    { enc₁ := fun _ x _ => (c₁ n).enc x
      enc₂ := fun _ x _ => (c₂ n).enc x
      rel := fun _ h₁ h₂ => addFin (h₁ 0) (h₂ 0)
      dec₁ := fun x h => (c₂ n).dec (subFin (h 0) ((c₁ n).enc x)) x
      dec₂ := fun x h => (c₁ n).dec (subFin (h 0) ((c₂ n).enc x)) x }
  have hb : ∀ x₁ x₂, c.bcast x₁ x₂ 0 = addFin ((c₁ n).enc x₁) ((c₂ n).enc x₂) := fun x₁ x₂ => by
    have := run_apply (c.step x₁ x₂) 0
    simp only [TWRCode.bcast, TWRCode.trans]
    rw [this]
    simp [TWRCode.step, TWRCode.relStep, c]
  refine ⟨1, _, _, _, fun _ => hAne, fun _ => hBne, fun _ => hKne, c, ?_, ?_, ?_, ?_⟩
  · simpa using hfloor (min_le_left _ _)
  · simpa using hfloor (min_le_left _ _)
  · simp [hK]
  · -- the error
    have hμ := iidPMF_isPMF hP n
    let e : (Fin n → α₁ × α₂) ≃ (Fin n → α₂ × α₁) :=
      Equiv.arrowCongr (Equiv.refl _) (Equiv.prodComm _ _)
    have hiid : ∀ ω, iidPMF P' n (e ω) = iidPMF P n ω := fun ω => by
      simp only [iidPMF]
      refine prod_congr rfl fun i _ => ?_
      rw [hP', dist_swap_apply]
      rfl
    have herr₂ : ∑ ω : Fin n → α₁ × α₂, (if (c₂ n).dec ((c₂ n).enc fun i => (ω i).2)
        (fun i => (ω i).1) ≠ (fun i => (ω i).2) then iidPMF P n ω else 0) =
        (c₂ n).errProb P' := by
      rw [WZCode.errProb, ← e.sum_comp]
      refine sum_congr rfl fun ω _ => ?_
      rw [hiid]
      rfl
    have hsum : c.errProb P ≤ (c₁ n).errProb P + (c₂ n).errProb P' := by
      rw [← herr₂, WZCode.errProb, ← sum_add_distrib]
      refine sum_le_sum fun ω _ => ?_
      have h₀ := hμ.nonneg ω
      set x₁ : Fin n → α₁ := fun i => (ω i).1 with hx₁
      set x₂ : Fin n → α₂ := fun i => (ω i).2 with hx₂
      have d₁ : c.dec₁ x₁ (c.bcast x₁ x₂) = (c₂ n).dec ((c₂ n).enc x₂) x₁ := by
        simp only [c]
        rw [hb, subFin_addFin_left hAK hBK]
      have d₂ : c.dec₂ x₂ (c.bcast x₁ x₂) = (c₁ n).dec ((c₁ n).enc x₁) x₂ := by
        simp only [c]
        rw [hb, subFin_addFin_right hAK hBK]
      have ef₁ : (fstSeq ω) = x₁ := rfl
      have ef₂ : (sndSeq ω) = x₂ := rfl
      rw [ef₁, ef₂, d₁, d₂]
      by_cases a₁ : (c₂ n).dec ((c₂ n).enc x₂) x₁ = x₂ <;>
        by_cases a₂ : (c₁ n).dec ((c₁ n).enc x₁) x₂ = x₁ <;> simp [a₁, a₂, h₀]
    have hn₁ : (c₁ n).errProb P < ε / 2 := he₁
    have hn₂ : (c₂ n).errProb P' < ε / 2 := he₂
    linarith

/-- **The rate region.** The closure of the achievable rates is given by the cutset bounds. -/
theorem twrOptimalRegion_eq (hP : IsPMF P) : twrOptimalRegion P = twrRegion P := by
  refine subset_antisymm (closure_minimal (fun R hR => ?_) (isClosed_twrRegion P)) ?_
  · exact IsAchievableTWR.mem_twrRegion hP hR
  · rintro ⟨R₁, R₂, R₃⟩ ⟨h₁, h₂, h₃, h₄⟩
    simp only at h₁ h₂ h₃ h₄
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hj : ∀ D : ℝ, Tendsto (fun k : ℕ => D + 1 / ((k : ℝ) + 1)) atTop (𝓝 D) := fun D => by
      simpa using tendsto_const_nhds.add ht
    have hlim := (hj R₁).prodMk_nhds ((hj R₂).prodMk_nhds (hj R₃))
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact isAchievableTWR_of_lt hP (by simp only; linarith) (by simp only; linarith)
      (by simp only; linarith) (by simp only; linarith)

/-- **Page 21-31 of [elgamal2010]: the minimum sum rate of two-way lossless source coding through a
relay** is `H(X₁ | X₂) + H(X₂ | X₁) + max {H(X₁ | X₂), H(X₂ | X₁)}`. -/
theorem twrSumRate_eq (hP : IsPMF P) :
    twrSumRate P = H[Prod.fst | Prod.snd ; P] / log 2 + H[Prod.snd | Prod.fst ; P] / log 2 +
      max (H[Prod.fst | Prod.snd ; P] / log 2) (H[Prod.snd | Prod.fst ; P] / log 2) := by
  rw [twrSumRate, twrOptimalRegion_eq hP]
  set a := H[Prod.fst | Prod.snd ; P] / log 2
  set b := H[Prod.snd | Prod.fst ; P] / log 2
  refine IsLeast.csInf_eq ⟨⟨(a, b, max a b), ⟨le_rfl, le_rfl, le_max_left _ _, le_max_right _ _⟩,
    rfl⟩, ?_⟩
  rintro _ ⟨⟨R₁, R₂, R₃⟩, ⟨h₁, h₂, h₃, h₄⟩, rfl⟩
  simp only at h₁ h₂ h₃ h₄ ⊢
  have : max a b ≤ R₃ := max_le h₃ h₄
  linarith

end Achievability

end InfoTheory
