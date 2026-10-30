/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACAchievability

/-!
# The broadcast channel

A broadcast channel has one input alphabet `𝒳`, two output alphabets `𝒴₁`, `𝒴₂` and a transition
matrix `p(y₁, y₂ | x)`, which we write as a channel `W : 𝒳 → 𝒴₁ × 𝒴₂ → ℝ`. A code sends a pair
of independent messages, `W₁` to receiver 1 and `W₂` to receiver 2 (Section 15.6.1).

An error for receiver 1 only involves the law of `(Xⁿ, Y₁ⁿ)`, and the probability of error
`P(g₁(Y₁ⁿ) ≠ W₁ or g₂(Y₂ⁿ) ≠ W₂)` is between the larger and the sum of the two individual
probabilities of error. So whether a rate pair is achievable only depends on the conditional
marginals `p(y₁ | x)` and `p(y₂ | x)` (Theorem 15.6.1). In particular a stochastically degraded
channel has the same capacity region as the physically degraded channel with the same marginals.

## Main definitions

* `bcMarg₁ W`, `bcMarg₂ W`: the conditional marginals `p(y₁ | x)` and `p(y₂ | x)`.
* `BCCode M₁ M₂ n α β₁ β₂`: **(15.201)–(15.203)** a `((M₁, M₂), n)` code for the broadcast
  channel with independent information.
* `BCCode.errProb`: **(15.204)** the probability of error; `BCCode.errProb₁`, `BCCode.errProb₂`:
  the probabilities of error at each receiver.
* `IsAchievableBC W R₁ R₂`, `bcCapacityRegion W`: achievable rate pairs and the capacity region.
* `IsPhysicallyDegraded W`, `IsStochasticallyDegraded W`: **Section 15.6.2, (15.209)**.

## Main statements

* `BCCode.errProb₁_eq`: the probability of error at receiver 1 is computed from `p(y₁ | x)`.
* `BCCode.max_errProb_le`, `BCCode.errProb_le_add`: `max (P₁, P₂) ≤ Pₑ ≤ P₁ + P₂`.
* `isAchievableBC_iff`: a rate pair is achievable iff there are codes whose individual
  probabilities of error tend to `0`.
* `bcCapacityRegion_eq_of_marg_eq`: **Theorem 15.6.1**, the capacity region only depends on the
  conditional marginals.
* `IsPhysicallyDegraded.isStochasticallyDegraded`, `IsStochasticallyDegraded.capacityRegion_eq`:
  a stochastically degraded channel has the capacity region of a physically degraded one.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 15.6.1
  and 15.6.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂]

/-- The conditional marginal `p(y₁ | x) = ∑_{y₂} p(y₁, y₂ | x)`. -/
def bcMarg₁ (W : α → β₁ × β₂ → ℝ) (x : α) (y₁ : β₁) : ℝ := ∑ y₂, W x (y₁, y₂)

/-- The conditional marginal `p(y₂ | x) = ∑_{y₁} p(y₁, y₂ | x)`. -/
def bcMarg₂ (W : α → β₁ × β₂ → ℝ) (x : α) (y₂ : β₂) : ℝ := ∑ y₁, W x (y₁, y₂)

omit [Fintype α] in
lemma IsChannel.bcMarg₁ {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W) : IsChannel (bcMarg₁ W) :=
  fun x => ⟨fun _ => sum_nonneg fun _ _ => (hW x).nonneg _, by
    change ∑ y₁, ∑ y₂, W x (y₁, y₂) = 1
    rw [← Fintype.sum_prod_type' (f := fun a b => W x (a, b))]
    exact (hW x).sum_eq_one⟩

omit [Fintype α] in
lemma IsChannel.bcMarg₂ {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W) : IsChannel (bcMarg₂ W) :=
  fun x => ⟨fun _ => sum_nonneg fun _ _ => (hW x).nonneg _, by
    change ∑ y₂, ∑ y₁, W x (y₁, y₂) = 1
    rw [sum_comm, ← Fintype.sum_prod_type' (f := fun a b => W x (a, b))]
    exact (hW x).sum_eq_one⟩

omit [Fintype α] in
/-- The output `Y₁ⁿ` of `n` uses of the broadcast channel is the output of `n` uses of the
marginal channel `p(y₁ | x)`. -/
lemma sum_channelExt_fst (W : α → β₁ × β₂ → ℝ) {n : ℕ} (x : Fin n → α)
    (f : (Fin n → β₁) → ℝ) :
    ∑ y : Fin n → β₁ × β₂, channelExt W n x y * f (fun i => (y i).1) =
      ∑ y₁, channelExt (bcMarg₁ W) n x y₁ * f y₁ := by
  classical
  rw [← sum_zipSeq]
  refine sum_congr rfl fun y₁ _ => ?_
  have e : ∀ y₂ : Fin n → β₂, (fun i => (zipSeq y₁ y₂ i).1) = y₁ := fun _ => rfl
  simp only [e]
  rw [← sum_mul]
  congr 1
  simp only [channelExt, bcMarg₁, zipSeq]
  exact (Fintype.prod_sum fun i b => W (x i) (y₁ i, b)).symm

omit [Fintype α] in
/-- The output `Y₂ⁿ` of `n` uses of the broadcast channel is the output of `n` uses of the
marginal channel `p(y₂ | x)`. -/
lemma sum_channelExt_snd (W : α → β₁ × β₂ → ℝ) {n : ℕ} (x : Fin n → α)
    (f : (Fin n → β₂) → ℝ) :
    ∑ y : Fin n → β₁ × β₂, channelExt W n x y * f (fun i => (y i).2) =
      ∑ y₂, channelExt (bcMarg₂ W) n x y₂ * f y₂ := by
  classical
  rw [← sum_zipSeq, sum_comm]
  refine sum_congr rfl fun y₂ _ => ?_
  have e : ∀ y₁ : Fin n → β₁, (fun i => (zipSeq y₁ y₂ i).2) = y₂ := fun _ => rfl
  simp only [e]
  rw [← sum_mul]
  congr 1
  simp only [channelExt, bcMarg₂, zipSeq]
  exact (Fintype.prod_sum fun i a => W (x i) (a, y₂ i)).symm

/-- **Definition (15.201)–(15.203).** A `((M₁, M₂), n)` code for the broadcast channel with
independent information: an encoder of the message pair and a decoder at each receiver. -/
structure BCCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*) where
  /-- The encoder `X : {0, …, M₁ - 1} × {0, …, M₂ - 1} → 𝒳ⁿ`. -/
  enc : Fin M₁ × Fin M₂ → Fin n → α
  /-- The decoder `g₁ : 𝒴₁ⁿ → {0, …, M₁ - 1}` of receiver 1. -/
  dec₁ : (Fin n → β₁) → Fin M₁
  /-- The decoder `g₂ : 𝒴₂ⁿ → {0, …, M₂ - 1}` of receiver 2. -/
  dec₂ : (Fin n → β₂) → Fin M₂

namespace BCCode

variable {M₁ M₂ n : ℕ} (W : α → β₁ × β₂ → ℝ) (c : BCCode M₁ M₂ n α β₁ β₂)

open Classical in
/-- **Definition (15.204).** The probability `P(g₁(Y₁ⁿ) ≠ W₁ or g₂(Y₂ⁿ) ≠ W₂)` of error, for
independent uniform messages. -/
def errProb : ℝ :=
  (∑ w, ∑ y : Fin n → β₁ × β₂, if c.dec₁ (fun i => (y i).1) ≠ w.1 ∨
    c.dec₂ (fun i => (y i).2) ≠ w.2 then channelExt W n (c.enc w) y else 0) / (M₁ * M₂)

open Classical in
/-- The probability `P(g₁(Y₁ⁿ) ≠ W₁)` of error at receiver 1, computed from `p(y₁ | x)`. -/
def errProb₁ : ℝ :=
  (∑ w, ∑ y₁, if c.dec₁ y₁ ≠ w.1 then channelExt (bcMarg₁ W) n (c.enc w) y₁ else 0) / (M₁ * M₂)

open Classical in
/-- The probability `P(g₂(Y₂ⁿ) ≠ W₂)` of error at receiver 2, computed from `p(y₂ | x)`. -/
def errProb₂ : ℝ :=
  (∑ w, ∑ y₂, if c.dec₂ y₂ ≠ w.2 then channelExt (bcMarg₂ W) n (c.enc w) y₂ else 0) / (M₁ * M₂)

variable {W}

open Classical in
omit [Fintype α] in
/-- The probability of error at receiver 1 only depends on `p(y₁ | x)`. -/
lemma errProb₁_eq :
    c.errProb₁ W = (∑ w, ∑ y : Fin n → β₁ × β₂,
      if c.dec₁ (fun i => (y i).1) ≠ w.1 then channelExt W n (c.enc w) y else 0) / (M₁ * M₂) := by
  unfold errProb₁
  congr 1
  refine sum_congr rfl fun w _ => ?_
  have h := sum_channelExt_fst W (c.enc w) fun y₁ => if c.dec₁ y₁ ≠ w.1 then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  exact h.symm

open Classical in
omit [Fintype α] in
/-- The probability of error at receiver 2 only depends on `p(y₂ | x)`. -/
lemma errProb₂_eq :
    c.errProb₂ W = (∑ w, ∑ y : Fin n → β₁ × β₂,
      if c.dec₂ (fun i => (y i).2) ≠ w.2 then channelExt W n (c.enc w) y else 0) / (M₁ * M₂) := by
  unfold errProb₂
  congr 1
  refine sum_congr rfl fun w _ => ?_
  have h := sum_channelExt_snd W (c.enc w) fun y₂ => if c.dec₂ y₂ ≠ w.2 then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  exact h.symm

omit [Fintype α] in
lemma errProb₁_congr {W' : α → β₁ × β₂ → ℝ} (h : bcMarg₁ W = bcMarg₁ W') :
    c.errProb₁ W = c.errProb₁ W' := by
  unfold errProb₁
  rw [h]

omit [Fintype α] in
lemma errProb₂_congr {W' : α → β₁ × β₂ → ℝ} (h : bcMarg₂ W = bcMarg₂ W') :
    c.errProb₂ W = c.errProb₂ W' := by
  unfold errProb₂
  rw [h]

omit [Fintype α] in
lemma errProb₁_nonneg (hW : IsChannel W) : 0 ≤ c.errProb₁ W := by
  classical
  refine div_nonneg (sum_nonneg fun w _ => sum_nonneg fun y _ => ?_) (by positivity)
  split_ifs <;> simp [channelExt_nonneg hW.bcMarg₁]

omit [Fintype α] in
lemma errProb₂_nonneg (hW : IsChannel W) : 0 ≤ c.errProb₂ W := by
  classical
  refine div_nonneg (sum_nonneg fun w _ => sum_nonneg fun y _ => ?_) (by positivity)
  split_ifs <;> simp [channelExt_nonneg hW.bcMarg₂]

omit [Fintype α] in
/-- `P₁ ≤ Pₑ` and `P₂ ≤ Pₑ`. -/
theorem max_errProb_le (hW : IsChannel W) :
    max (c.errProb₁ W) (c.errProb₂ W) ≤ c.errProb W := by
  classical
  rw [c.errProb₁_eq, c.errProb₂_eq]
  refine max_le (div_le_div_of_nonneg_right ?_ (by positivity))
    (div_le_div_of_nonneg_right ?_ (by positivity)) <;>
  refine sum_le_sum fun w _ => sum_le_sum fun y _ => ?_ <;>
  split_ifs <;> simp_all [channelExt_nonneg hW]

omit [Fintype α] in
/-- `Pₑ ≤ P₁ + P₂`. -/
theorem errProb_le_add (hW : IsChannel W) : c.errProb W ≤ c.errProb₁ W + c.errProb₂ W := by
  classical
  rw [c.errProb₁_eq, c.errProb₂_eq, ← add_div, ← sum_add_distrib]
  refine div_le_div_of_nonneg_right (sum_le_sum fun w _ => ?_) (by positivity)
  rw [← sum_add_distrib]
  refine sum_le_sum fun y _ => ?_
  have := channelExt_nonneg hW (c.enc w) y
  split_ifs <;> simp_all

end BCCode

/-- **Definition (Section 15.6.1).** A rate pair `(R₁, R₂)` (in nats) is achievable for the
broadcast channel if there are `((⌈e^{nR₁}⌉, ⌈e^{nR₂}⌉), n)` codes whose probability of error
tends to `0`. -/
def IsAchievableBC (W : α → β₁ × β₂ → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, BCCode ⌈exp (n * R₁)⌉₊ ⌈exp (n * R₂)⌉₊ n α β₁ β₂,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Definition (Section 15.6.1).** The capacity region of the broadcast channel is the closure of
the set of achievable rate pairs. -/
def bcCapacityRegion (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableBC W R.1 R.2}

variable {W W' : α → β₁ × β₂ → ℝ}

omit [Fintype α] in
/-- A rate pair is achievable iff there are codes whose probabilities of error at both receivers
tend to `0`. -/
theorem isAchievableBC_iff (hW : IsChannel W) {R₁ R₂ : ℝ} :
    IsAchievableBC W R₁ R₂ ↔ ∃ c : ∀ n : ℕ, BCCode ⌈exp (n * R₁)⌉₊ ⌈exp (n * R₂)⌉₊ n α β₁ β₂,
      Tendsto (fun n => (c n).errProb₁ W) atTop (𝓝 0) ∧
        Tendsto (fun n => (c n).errProb₂ W) atTop (𝓝 0) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun n => (c n).errProb₁_nonneg hW)
        fun n => (le_max_left _ _).trans ((c n).max_errProb_le hW)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun n => (c n).errProb₂_nonneg hW)
        fun n => (le_max_right _ _).trans ((c n).max_errProb_le hW)
  · rintro ⟨c, h₁, h₂⟩
    refine ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using h₁.add h₂) (fun n => ?_) fun n => (c n).errProb_le_add hW⟩
    exact ((c n).errProb₁_nonneg hW).trans ((le_max_left _ _).trans ((c n).max_errProb_le hW))

omit [Fintype α] in
/-- **Theorem 15.6.1.** The capacity region of a broadcast channel only depends on the conditional
marginal distributions `p(y₁ | x)` and `p(y₂ | x)`. -/
theorem bcCapacityRegion_eq_of_marg_eq (hW : IsChannel W) (hW' : IsChannel W')
    (h₁ : bcMarg₁ W = bcMarg₁ W') (h₂ : bcMarg₂ W = bcMarg₂ W') :
    bcCapacityRegion W = bcCapacityRegion W' := by
  have : ∀ R₁ R₂, IsAchievableBC W R₁ R₂ ↔ IsAchievableBC W' R₁ R₂ := fun R₁ R₂ => by
    rw [isAchievableBC_iff hW, isAchievableBC_iff hW']
    refine exists_congr fun c => ?_
    simp only [fun n => (c n).errProb₁_congr h₁, fun n => (c n).errProb₂_congr h₂]
  unfold bcCapacityRegion
  congr 1
  ext R
  exact this R.1 R.2

/-! ### Degraded broadcast channels -/

/-- **Definition (Section 15.6.2).** A broadcast channel is physically degraded if
`p(y₁, y₂ | x) = p(y₁ | x) p(y₂ | y₁)`. -/
def IsPhysicallyDegraded (W : α → β₁ × β₂ → ℝ) : Prop :=
  ∃ W₁ : α → β₁ → ℝ, ∃ V : β₁ → β₂ → ℝ, IsChannel W₁ ∧ IsChannel V ∧
    ∀ x y₁ y₂, W x (y₁, y₂) = W₁ x y₁ * V y₁ y₂

/-- **Definition (15.209).** A broadcast channel is stochastically degraded if its conditional
marginals are those of a physically degraded channel:
`p(y₂ | x) = ∑_{y₁} p(y₁ | x) p'(y₂ | y₁)`. -/
def IsStochasticallyDegraded (W : α → β₁ × β₂ → ℝ) : Prop :=
  ∃ V : β₁ → β₂ → ℝ, IsChannel V ∧ ∀ x y₂, bcMarg₂ W x y₂ = ∑ y₁, bcMarg₁ W x y₁ * V y₁ y₂

omit [Fintype α] in
/-- A physically degraded broadcast channel is stochastically degraded. -/
theorem IsPhysicallyDegraded.isStochasticallyDegraded (h : IsPhysicallyDegraded W) :
    IsStochasticallyDegraded W := by
  obtain ⟨W₁, V, -, hV, hW⟩ := h
  refine ⟨V, hV, fun x y₂ => ?_⟩
  have hm : ∀ y₁, bcMarg₁ W x y₁ = W₁ x y₁ := fun y₁ => by
    simp only [bcMarg₁, hW, ← mul_sum, (hV y₁).sum_eq_one, mul_one]
  simp only [bcMarg₂, hW, hm]

omit [Fintype α] in
/-- **Section 15.6.2** A stochastically degraded broadcast channel has the same capacity region as
the physically degraded channel `p(y₁ | x) p'(y₂ | y₁)`. -/
theorem IsStochasticallyDegraded.capacityRegion_eq (hW : IsChannel W) {V : β₁ → β₂ → ℝ}
    (hV : IsChannel V) (h : ∀ x y₂, bcMarg₂ W x y₂ = ∑ y₁, bcMarg₁ W x y₁ * V y₁ y₂) :
    bcCapacityRegion W = bcCapacityRegion fun x y => bcMarg₁ W x y.1 * V y.1 y.2 := by
  have hW' : IsChannel fun x (y : β₁ × β₂) => bcMarg₁ W x y.1 * V y.1 y.2 := fun x =>
    ⟨fun y => mul_nonneg ((hW.bcMarg₁ x).nonneg _) ((hV _).nonneg _), by
      rw [Fintype.sum_prod_type]
      simp only [← mul_sum, (hV _).sum_eq_one, mul_one]
      exact (hW.bcMarg₁ x).sum_eq_one⟩
  refine bcCapacityRegion_eq_of_marg_eq hW hW' ?_ ?_
  · funext x y₁
    simp only [bcMarg₁, ← mul_sum, (hV y₁).sum_eq_one, mul_one]
  · funext x y₂
    rw [h]
    rfl

end InfoTheory
