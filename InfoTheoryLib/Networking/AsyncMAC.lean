/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACBounds
public import InfoTheoryLib.Network.MACConverse

/-!
# The totally asynchronous multiple-access channel: the model and the region

Theorem 2 of Lecture 24 of El Gamal and Kim. The two senders use a block code of length `n` in each
transmission block, with i.i.d. uniform messages, and their blocks incur unknown delays
`d₁, d₂ ∈ [0 : n - 1]`. To decode block `l`, the receiver uses the `2 n - 1` outputs starting at the
beginning of the block with delay `0`. These outputs depend on three consecutive messages of each
sender. By stationarity the error probability does not depend on `l`, as the notes observe, so one
window with three messages per sender defines it.

## Main definitions

* `asyncInput enc m d t`: the input of a sender at slot `t` of the window, for the three messages
  `m` and the delay `d`.
* `AsyncCode`, `AsyncCode.asyncErr`: a code and its probability of error `P_e(d₁, d₂)`.
* `IsAchievableAsync`, `asyncCapacityRegionBits`: achievability and the capacity region.
* `asyncRegionBits W`: the region of Theorem 2, with no time sharing.

## Main statements

* `mem_asyncRegionBits_of_forall`: the region is reached through approximations, by compactness.
* `isClosed_asyncRegionBits`: it is closed.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset Filter Topology Real

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]

/-- The block offset of slot `t` of the window, for a sender with delay `d`, is at most `2`. -/
lemma async_div_lt {n : ℕ} (d : Fin n) (t : Fin (2 * n - 1)) : ((t : ℕ) + n - d) / n < 3 := by
  have hn : 0 < n := d.pos
  refine Nat.div_lt_of_lt_mul ?_
  have := t.isLt
  omega

/-- **The input of a sender in the window.** Slot `t` of the window lies in the block before the
current one (offset `0`), the current one (offset `1`) or the next one (offset `2`). -/
def asyncInput {M n : ℕ} {α : Type*} (enc : Fin M → Fin n → α) (m : Fin 3 → Fin M) (d : Fin n)
    (t : Fin (2 * n - 1)) : α :=
  enc (m ⟨((t : ℕ) + n - d) / n, async_div_lt d t⟩) ⟨((t : ℕ) + n - d) % n, Nat.mod_lt _ d.pos⟩

/-- **Definition (Lecture 24).** A `(2^{nR₁}, 2^{nR₂}, n, n - 1)` code for the asynchronous DM-MAC:
two encoders, and a decoder of the message pair of a block from the window of `2 n - 1` outputs. The
error message of the notes is dropped, as sending it to any message pair can only help. -/
structure AsyncCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*) where
  /-- The codewords of sender 1, the same in each block. -/
  enc₁ : Fin M₁ → Fin n → α₁
  /-- The codewords of sender 2, the same in each block. -/
  enc₂ : Fin M₂ → Fin n → α₂
  /-- The decoder of the messages of a block. -/
  dec : (Fin (2 * n - 1) → β) → Fin M₁ × Fin M₂

namespace AsyncCode

variable {M₁ M₂ n : ℕ}

/-- The law of the window for the three messages of each sender and the delays. -/
def windowLaw (c : AsyncCode M₁ M₂ n α₁ α₂ β) (W : α₁ × α₂ → β → ℝ) (d₁ d₂ : Fin n)
    (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂) (y : Fin (2 * n - 1) → β) : ℝ :=
  channelExt W (2 * n - 1)
    (fun t => (asyncInput c.enc₁ m₁ d₁ t, asyncInput c.enc₂ m₂ d₂ t)) y

/-- **The probability of error `P_e(d₁, d₂)` of Lecture 24**, for uniform messages. The current
messages are `m₁ 1` and `m₂ 1`. -/
def asyncErr (c : AsyncCode M₁ M₂ n α₁ α₂ β) (W : α₁ × α₂ → β → ℝ) (d₁ d₂ : Fin n) : ℝ :=
  (∑ m₁ : Fin 3 → Fin M₁, ∑ m₂ : Fin 3 → Fin M₂, ∑ y,
    if c.dec y ≠ (m₁ 1, m₂ 1) then c.windowLaw W d₁ d₂ m₁ m₂ y else 0) /
      ((M₁ : ℝ) ^ 3 * (M₂ : ℝ) ^ 3)

end AsyncCode

/-- **Definition (Lecture 24).** A rate pair (in bits) is achievable for the totally asynchronous
DM-MAC if a sequence of codes has `P_e = max_{d₁, d₂} P_e(d₁, d₂) → 0`. -/
def IsAchievableAsync (W : α₁ × α₂ → β → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, AsyncCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α₁ α₂ β,
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ d₁ d₂ : Fin n, (c n).asyncErr W d₁ d₂ ≤ ε

/-- The capacity region of the totally asynchronous DM-MAC, in bits. -/
def asyncCapacityRegionBits (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableAsync W R.1 R.2}

/-- **The region of Theorem 2 of Lecture 24.** The rate pairs (in bits) with
`R₁ ≤ I(X₁; Y | X₂)`, `R₂ ≤ I(X₂; Y | X₁)` and `R₁ + R₂ ≤ I(X₁, X₂; Y)` for some `p(x₁) p(x₂)`, with
no time sharing. -/
def asyncRegionBits (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ R.1 * log 2 ≤ macInfo₁ p₁ p₂ W ∧
    R.2 * log 2 ≤ macInfo₂ p₁ p₂ W ∧ (R.1 + R.2) * log 2 ≤ macInfo₁₂ p₁ p₂ W}

variable {W : α₁ × α₂ → β → ℝ}

/-! ### Continuity of the three mutual informations -/

lemma continuousOn_macInfo₁ (hW : IsChannel W) :
    ContinuousOn (fun p : (α₁ → ℝ) × (α₂ → ℝ) => macInfo₁ p.1 p.2 W)
      {p | IsPMF p.1 ∧ IsPMF p.2} := by
  have h : ContinuousOn (fun p : (α₁ → ℝ) × (α₂ → ℝ) =>
      ∑ b, p.2 b * mutualInfoOf p.1 (fun a => W (a, b))) {p | IsPMF p.1 ∧ IsPMF p.2} := by
    refine continuousOn_finsetSum _ fun b _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact ((continuous_apply b).comp continuous_snd).continuousOn
    · exact (continuousOn_mutualInfoOf fun a => hW (a, b)).comp continuous_fst.continuousOn
        fun p hp => hp.1
  exact h.congr fun p hp => macInfo₁_eq_sum hp.1 hp.2 hW

lemma continuousOn_macInfo₂ (hW : IsChannel W) :
    ContinuousOn (fun p : (α₁ → ℝ) × (α₂ → ℝ) => macInfo₂ p.1 p.2 W)
      {p | IsPMF p.1 ∧ IsPMF p.2} := by
  have h : ContinuousOn (fun p : (α₁ → ℝ) × (α₂ → ℝ) =>
      ∑ a, p.1 a * mutualInfoOf p.2 (fun b => W (a, b))) {p | IsPMF p.1 ∧ IsPMF p.2} := by
    refine continuousOn_finsetSum _ fun a _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact ((continuous_apply a).comp continuous_fst).continuousOn
    · exact (continuousOn_mutualInfoOf fun b => hW (a, b)).comp continuous_snd.continuousOn
        fun p hp => hp.2
  exact h.congr fun p hp => macInfo₂_eq_sum hp.1 hp.2 hW

lemma continuousOn_macInfo₁₂ (hW : IsChannel W) :
    ContinuousOn (fun p : (α₁ → ℝ) × (α₂ → ℝ) => macInfo₁₂ p.1 p.2 W)
      {p | IsPMF p.1 ∧ IsPMF p.2} := by
  have hc : Continuous fun p : (α₁ → ℝ) × (α₂ → ℝ) => prodDist p.1 p.2 := by
    refine continuous_pi fun z => ?_
    exact ((continuous_apply z.1).comp continuous_fst).mul
      ((continuous_apply z.2).comp continuous_snd)
  exact (continuousOn_mutualInfoOf hW).comp hc.continuousOn fun p hp => hp.1.prodDist hp.2

/-- **The region is reached through approximations.** If for each `η > 0` some product input
distribution satisfies the three bounds up to `η`, then one satisfies them exactly: the worst of
the three deficits is continuous, so it attains its minimum on the compact set of input
distributions. -/
theorem mem_asyncRegionBits_of_forall [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) {R : ℝ × ℝ}
    (h : ∀ η > 0, ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧ R.1 * log 2 ≤ macInfo₁ p₁ p₂ W + η ∧
      R.2 * log 2 ≤ macInfo₂ p₁ p₂ W + η ∧ (R.1 + R.2) * log 2 ≤ macInfo₁₂ p₁ p₂ W + η) :
    R ∈ asyncRegionBits W := by
  set K : Set ((α₁ → ℝ) × (α₂ → ℝ)) := {p | IsPMF p.1 ∧ IsPMF p.2} with hK
  have hKc : IsCompact K := by
    have : K = {p : α₁ → ℝ | IsPMF p} ×ˢ {p : α₂ → ℝ | IsPMF p} := rfl
    rw [this]
    exact isCompact_setOf_isPMF.prod isCompact_setOf_isPMF
  set g : (α₁ → ℝ) × (α₂ → ℝ) → ℝ := fun p =>
    max (R.1 * log 2 - macInfo₁ p.1 p.2 W) (max (R.2 * log 2 - macInfo₂ p.1 p.2 W)
      ((R.1 + R.2) * log 2 - macInfo₁₂ p.1 p.2 W)) with hg
  have hgc : ContinuousOn g K :=
    (continuousOn_const.sub (continuousOn_macInfo₁ hW)).sup
      ((continuousOn_const.sub (continuousOn_macInfo₂ hW)).sup
        (continuousOn_const.sub (continuousOn_macInfo₁₂ hW)))
  have hne : K.Nonempty :=
    ⟨(uniformPMF α₁, uniformPMF α₂), uniformPMF_isPMF, uniformPMF_isPMF⟩
  obtain ⟨p, hp, hmin⟩ := hKc.exists_isMinOn hne hgc
  have hle : g p ≤ 0 := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨p₁, p₂, h₁, h₂, h3, h4, h5⟩ := h η hη
    have hq : (p₁, p₂) ∈ K := ⟨h₁, h₂⟩
    refine (hmin hq).trans ?_
    refine max_le ?_ (max_le ?_ ?_) <;> simp only [zero_add] <;> linarith
  refine ⟨p.1, p.2, hp.1, hp.2, ?_, ?_, ?_⟩
  · have := (le_max_left _ _).trans hle
    linarith
  · have := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
    linarith
  · have := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
    linarith

/-- The region of Theorem 2 is closed. -/
theorem isClosed_asyncRegionBits [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    IsClosed (asyncRegionBits W) := by
  refine isClosed_of_closure_subset fun R hR => ?_
  have hl := log_pos one_lt_two
  refine mem_asyncRegionBits_of_forall hW fun η hη => ?_
  set δ := η / (2 * log 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have hball : Metric.ball R δ ∩ asyncRegionBits W |>.Nonempty :=
    Metric.mem_closure_iff.1 hR δ hδ0 |>.imp fun x hx => ⟨by
      rw [Metric.mem_ball, dist_comm]; exact hx.2, hx.1⟩
  obtain ⟨R', hball', p₁, p₂, h₁, h₂, h3, h4, h5⟩ := hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hball'
  have e1 := abs_lt.1 hball'.1
  have e2 := abs_lt.1 hball'.2
  have hη : δ * log 2 = η / 2 := by
    rw [hδ]
    field_simp
  refine ⟨p₁, p₂, h₁, h₂, ?_, ?_, ?_⟩ <;> nlinarith

end InfoTheory
