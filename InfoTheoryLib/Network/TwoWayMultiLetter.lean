/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayRates
public import InfoTheoryLib.Network.TwoWayStrategy

/-!
# The multi-letter capacity region of the two-way channel

Theorem 7 on page 18-55 of the notes, with strategies: the capacity region of the two-way channel
with a common output is the closure of the union of the regions of strategies of length `k`.

## Main definitions

* `stratAt`: the encoder that runs a strategy in each block of `k` symbols.
* `blockCode`: the code on the channel of a code on the super-channel.

## Main statements

* `sum_blockLaw`: the law of the code on the channel, in terms of the code on the super-channel.
* `isAchievableTWC_of_multi`: **the strategies give achievable rates**.
* `twcCapacityRegion_eq_closure_iUnion`: **Theorem 7**.

## Implementation notes

The notes prove achievability by interleaving `k` blocks and by multiplexing over the states
`(x₁ʲ⁻¹, yʲ⁻¹)`. We use instead Shannon's inner bound on the super-channel, which is the same as the
coding on strategies of Shannon's original paper, and run a strategy in each block of `k` symbols.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X₁ X₂ Y : Type*} {k m M₁ M₂ : ℕ}

/-! ### Blocks -/

section Block

variable [NeZero k]

/-- The input of a strategy at time `(j, i)`, from the outputs of all the blocks. -/
def stratAt {X : Type*} (e : ∀ j, (Fin j → Fin k → Y) → Strat k X Y) (j : ℕ) (i : Fin k)
    (Z : ℕ → Fin k → Y) : X :=
  e j (fun j' => Z j') i fun t => Z j ⟨t, t.isLt.trans i.isLt⟩

omit [NeZero k] in
lemma stratAt_congr {X : Type*} (e : ∀ j, (Fin j → Fin k → Y) → Strat k X Y) (j : ℕ) (i : Fin k)
    {Z Z' : ℕ → Fin k → Y} (h₁ : ∀ j' < j, Z j' = Z' j')
    (h₂ : ∀ t (ht : t < (i : ℕ)), Z j ⟨t, ht.trans i.isLt⟩ = Z' j ⟨t, ht.trans i.isLt⟩) :
    stratAt e j i Z = stratAt e j i Z' := by
  have e₁ : (fun j' : Fin j => Z j') = fun j' : Fin j => Z' j' := funext fun j' => h₁ j' j'.isLt
  have e₂ : (fun t : Fin i => Z j ⟨t, t.isLt.trans i.isLt⟩) =
      fun t : Fin i => Z' j ⟨t, t.isLt.trans i.isLt⟩ :=
    funext fun t => h₂ t t.isLt
  simp only [stratAt, e₁, e₂]

variable [Nonempty Y]

/-- The blocks of a sequence, for `m` blocks. -/
def blocksOf {N : ℕ} (y : Fin N → Y) : Fin m → Fin k → Y :=
  fun j => getBlock (Classical.arbitrary Y) y j

/-- **The code on the channel of a code on the super-channel.** -/
def blockCode (c : TWCCode M₁ M₂ m (Strat k X₁ Y) (Strat k X₂ Y) (Fin k → Y) (Fin k → Y)) (N : ℕ) :
    TWCCode M₁ M₂ N X₁ X₂ Y Y where
  enc₁ K w ys := stratAt (fun j z => c.enc₁ j w z) (K / k) ⟨K % k, Nat.mod_lt _ (NeZero.pos k)⟩
    (getBlock (Classical.arbitrary Y) ys)
  enc₂ K w ys := stratAt (fun j z => c.enc₂ j w z) (K / k) ⟨K % k, Nat.mod_lt _ (NeZero.pos k)⟩
    (getBlock (Classical.arbitrary Y) ys)
  dec₁ w y := c.dec₁ w (blocksOf y)
  dec₂ w y := c.dec₂ w (blocksOf y)

omit [NeZero k] [Nonempty Y] in
lemma finProd_val (j : Fin m) (i : Fin k) :
    ((finProdFinEquiv (j, i) : Fin (m * k)) : ℕ) = i + k * j := rfl

omit [NeZero k] in
/-- The blocks of a sequence of `m k` symbols. -/
lemma blocksOf_eq (y : Fin (m * k) → Y) (j : Fin m) (i : Fin k) :
    blocksOf y j i = y (finProdFinEquiv (j, i)) := by
  have hlt : (i : ℕ) + k * j < m * k := by
    rw [← finProd_val j i]
    exact (finProdFinEquiv (j, i)).isLt
  simp only [blocksOf, getBlock, dite_eq_left hlt]
  rfl

omit [NeZero k] in
/-- The first blocks depend only on the first symbols. -/
lemma blocksOf_prefix {N : ℕ} (h : m * k ≤ N) (y : Fin N → Y) :
    (blocksOf y : Fin m → Fin k → Y) =
      blocksOf (fun t : Fin (m * k) => y ⟨t, lt_of_lt_of_le t.isLt h⟩) := by
  funext j i
  have hlt : (i : ℕ) + k * j < m * k := by
    rw [← finProd_val j i]
    exact (finProdFinEquiv (j, i)).isLt
  simp only [blocksOf, getBlock, dite_eq_left hlt, dite_eq_left (lt_of_lt_of_le hlt h)]

/-- The input at the time `(j, i)` depends only on the outputs before it. -/
lemma stratAt_block {X : Type*} (e : ∀ j, (Fin j → Fin k → Y) → Strat k X Y) (y : Fin (m * k) → Y)
    (j : Fin m) (i : Fin k) :
    stratAt e ((finProdFinEquiv (j, i) : Fin (m * k)) / k)
        ⟨((finProdFinEquiv (j, i) : Fin (m * k)) : ℕ) % k, Nat.mod_lt _ (NeZero.pos k)⟩
        (getBlock (Classical.arbitrary Y)
          fun t : Fin (finProdFinEquiv (j, i) : Fin (m * k)) => y ⟨t, t.isLt.trans (Fin.is_lt _)⟩) =
      stratAt e j i (getBlock (Classical.arbitrary Y) y) := by
  set K : Fin (m * k) := finProdFinEquiv (j, i) with hK
  have hval : (K : ℕ) = i + k * j := rfl
  have hpos := NeZero.pos k
  have hdiv : (K : ℕ) / k = j := by
    rw [hval, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt i.isLt, zero_add]
  have hmod : (⟨(K : ℕ) % k, Nat.mod_lt _ hpos⟩ : Fin k) = i := by
    apply Fin.ext
    change (K : ℕ) % k = i
    rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  rw [hdiv, hmod]
  refine stratAt_congr e j i (fun j' hj' => ?_) fun t ht => ?_
  · funext i'
    have hlt : (i' : ℕ) + k * j' < K := by
      rw [hval]
      have h₁ : k * (j' + 1) ≤ k * j := Nat.mul_le_mul_left _ hj'
      have h₂ := i'.isLt
      rw [Nat.mul_add, Nat.mul_one] at h₁
      omega
    simp only [getBlock, dite_eq_left hlt, dite_eq_left (hlt.trans K.isLt)]
  · have hlt : t + k * j < K := by
      rw [hval]
      omega
    simp only [getBlock, dite_eq_left hlt, dite_eq_left (hlt.trans K.isLt)]

/-- **The law of the code on the channel.** -/
lemma prod_blockCode (c : TWCCode M₁ M₂ m (Strat k X₁ Y) (Strat k X₂ Y) (Fin k → Y) (Fin k → Y))
    {V : X₁ × X₂ → Y → ℝ} (N : ℕ) (w : Fin M₁ × Fin M₂) (y : Fin (m * k) → Y) :
    ∏ K : Fin (m * k),
      V ((blockCode c N).fbEnc id id K w fun t : Fin K => y ⟨t, t.isLt.trans K.isLt⟩)
        (y K) =
      ∏ j : Fin m, stratW V k (c.fbEnc id id j w fun t : Fin j =>
        blocksOf y ⟨t, t.isLt.trans j.isLt⟩) (blocksOf y j) := by
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  refine prod_congr rfl fun j _ => ?_
  simp only [stratW]
  refine prod_congr rfl fun i _ => ?_
  have hy : y (finProdFinEquiv (j, i)) = blocksOf y j i := (blocksOf_eq y j i).symm
  simp only [TWCCode.fbEnc, blockCode, id]
  rw [stratAt_block, stratAt_block, hy]
  rfl

variable [Fintype Y]

omit [NeZero k] [Fintype Y] in
/-- The sum over the sequences of `m k` symbols is a sum over the blocks. -/
lemma sum_blocksOf [Fintype Y] (F : (Fin m → Fin k → Y) → ℝ) :
    ∑ y : Fin (m * k) → Y, F (blocksOf y) = ∑ z, F z := by
  classical
  let e : (Fin (m * k) → Y) ≃ (Fin m → Fin k → Y) :=
    (finProdFinEquiv.arrowCongr (Equiv.refl Y)).symm.trans (Equiv.curry _ _ _)
  have he : ∀ y : Fin (m * k) → Y, (blocksOf y : Fin m → Fin k → Y) = e y := fun y => by
    funext j i
    rw [blocksOf_eq]
    rfl
  simp only [he]
  exact e.sum_comp F

variable [Fintype X₁] [Fintype X₂] {V : X₁ × X₂ → Y → ℝ}

omit [Fintype X₁] [Fintype X₂] in
/-- **The law of the code on the channel, in terms of the code on the super-channel.** -/
theorem sum_blockLaw (c : TWCCode M₁ M₂ m (Strat k X₁ Y) (Strat k X₂ Y) (Fin k → Y) (Fin k → Y))
    (hV : IsChannel V) {N : ℕ} (h : m * k ≤ N)
    (F : (Fin M₁ × Fin M₂) → (Fin m → Fin k → Y) → ℝ) :
    ∑ ω, (blockCode c N).law V id id ω * F ω.1 (blocksOf ω.2) =
      ∑ ω, c.law (stratW V k) id id ω * F ω.1 ω.2 := by
  classical
  -- the first `m k` symbols
  have hd := dist_fbLaw_prefix (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := V)
    (enc := (blockCode c N).fbEnc id id) hV (m * k) N h
  have hm := sum_dist_mul (fbLaw (uniformPMF (Fin M₁ × Fin M₂)) V ((blockCode c N).fbEnc id id) N)
    (fun z => (z.1, fun t : Fin (m * k) => z.2 ⟨t, lt_of_lt_of_le t.isLt h⟩))
    (fun ω : (Fin M₁ × Fin M₂) × (Fin (m * k) → Y) => F ω.1 (blocksOf ω.2))
  rw [hd] at hm
  have e₁ : ∑ ω, (blockCode c N).law V id id ω * F ω.1 (blocksOf ω.2) =
      ∑ ω : (Fin M₁ × Fin M₂) × (Fin (m * k) → Y),
        fbLaw (uniformPMF (Fin M₁ × Fin M₂)) V ((blockCode c N).fbEnc id id) (m * k) ω *
          F ω.1 (blocksOf ω.2) := by
    rw [hm]
    refine sum_congr rfl fun ω _ => ?_
    rw [blocksOf_prefix h]
    rfl
  rw [e₁, Fintype.sum_prod_type]
  refine Eq.trans ?_ (Fintype.sum_prod_type _).symm
  refine sum_congr rfl fun w _ => ?_
  have e₂ : ∀ y : Fin (m * k) → Y,
      fbLaw (uniformPMF (Fin M₁ × Fin M₂)) V ((blockCode c N).fbEnc id id) (m * k) (w, y) =
        c.law (stratW V k) id id (w, blocksOf y) := by
    intro y
    rw [fbLaw_eq_prod, prod_blockCode, TWCCode.law, fbLaw_eq_prod]
  simp only [e₂]
  exact sum_blocksOf fun z => c.law (stratW V k) id id (w, z) * F w z

end Block

/-! ### The errors -/

/-- The probability of error as an expectation. -/
lemma errProb_eq_ind {Ω α β : Type*} [Fintype Ω] (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (g : β → α) :
    InfoTheory.errProb μ X Y g = ∑ ω, μ ω * ind (g (Y ω) ≠ X ω) := by
  classical
  simp only [InfoTheory.errProb]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : g (Y ω) = X ω
  · have hne : ¬ g (Y ω) ≠ X ω := not_not.mpr h
    rw [ind_of_neg hne, mul_zero]
    exact ite_eq_right hne
  · rw [ind_of_pos h, mul_one]
    exact ite_eq_left h

section Errors

variable [NeZero k] [Nonempty Y] [Fintype Y] [Fintype X₁] [Fintype X₂] {V : X₁ × X₂ → Y → ℝ}

omit [Fintype X₁] [Fintype X₂] in
/-- The error of node 2 is the same on the channel and on the super-channel. -/
lemma err₂_blockCode (c : TWCCode M₁ M₂ m (Strat k X₁ Y) (Strat k X₂ Y) (Fin k → Y) (Fin k → Y))
    (hV : IsChannel V) {N : ℕ} (h : m * k ≤ N) :
    (blockCode c N).err₂ V id id = c.err₂ (stratW V k) id id := by
  simp only [TWCCode.err₂, errProb_eq_ind]
  exact sum_blockLaw c hV h fun w z => ind (c.dec₂ w.2 z ≠ w.1)

omit [Fintype X₁] [Fintype X₂] in
/-- The error of node 1 is the same on the channel and on the super-channel. -/
lemma err₁_blockCode (c : TWCCode M₁ M₂ m (Strat k X₁ Y) (Strat k X₂ Y) (Fin k → Y) (Fin k → Y))
    (hV : IsChannel V) {N : ℕ} (h : m * k ≤ N) :
    (blockCode c N).err₁ V id id = c.err₁ (stratW V k) id id := by
  simp only [TWCCode.err₁, errProb_eq_ind]
  exact sum_blockLaw c hV h fun w z => ind (c.dec₁ w.1 z ≠ w.2)

end Errors

/-! ### The rates -/

section Rates

variable [Nonempty Y] [Fintype Y] [Fintype X₁] [Fintype X₂] [Nonempty X₁] [Nonempty X₂]
  {V : X₁ × X₂ → Y → ℝ}

/-- A term of the bound on the error. -/
lemma blockTerm_le {R G E ε : ℝ} {N : ℕ} (hN : N < k * (m + 1))
    (hg : 0 < R → k * (R * log 2) + E * ε + ε ≤ G) :
    (((2 ^ ⌈(N : ℝ) * R⌉₊ : ℕ) : ℝ) - 1) * exp (-(m * (G - E * ε))) ≤
      (2 * exp (k * (|R| * log 2))) * exp (-(m * ε)) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  rcases le_or_gt R 0 with hR | hR
  · rw [Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hR)]
    simp only [pow_zero, Nat.cast_one, sub_self, zero_mul]
    positivity
  · have hgap := hg hR
    have hN' : (N : ℝ) ≤ k * ((m : ℝ) + 1) := by exact_mod_cast hN.le
    have hRl : 0 < R * log 2 := mul_pos hR hlog2
    have h₁ := superposition_two_pow_ceil_sub_one_le N R
    have h₂ : exp ((N : ℝ) * (R * log 2)) ≤ exp ((k : ℝ) * (R * log 2)) *
        exp ((m : ℝ) * (k * (R * log 2))) := by
      rw [← exp_add]
      refine exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_right hN' hRl.le
      nlinarith
    have habs : |R| = R := abs_of_pos hR
    rw [habs]
    calc _ ≤ (2 * (exp ((k : ℝ) * (R * log 2)) * exp ((m : ℝ) * (k * (R * log 2))))) *
          exp (-(m * (G - E * ε))) :=
          mul_le_mul_of_nonneg_right (h₁.trans (mul_le_mul_of_nonneg_left h₂ (by norm_num)))
            (exp_pos _).le
      _ = (2 * exp ((k : ℝ) * (R * log 2))) *
          exp ((m : ℝ) * (k * (R * log 2)) + -(m * (G - E * ε))) := by
          rw [exp_add]
          ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by positivity)
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          nlinarith

/-- **Strategies give achievable rates.** -/
theorem isAchievableTWC_of_multi (hk : 0 < k) {p₁ : Strat k X₁ Y → ℝ} {p₂ : Strat k X₂ Y → ℝ}
    (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hV : IsChannel V) {R₁ R₂ : ℝ}
    (h₁ : k * (R₁ * log 2) < cInfo (prodDist p₁ p₂) (stratW V k))
    (h₂ : k * (R₂ * log 2) < cInfo (prodDist p₂ p₁) fun t => stratW V k t.swap) :
    IsAchievableTWC (commonTW V) R₁ R₂ := by
  classical
  have : NeZero k := ⟨hk.ne'⟩
  have hS : IsChannel (stratW V k) := stratW_isChannel hV
  have hW' := commonTW_isChannel hS
  have hq : IsPMF fun _ : Unit => (1 : ℝ) := ⟨fun _ => zero_le_one, by simp⟩
  have hμ := twLaw_isPMF hq (fun _ => hp₁) (fun _ => hp₂) hW'
  set μ := twLaw (fun _ : Unit => (1 : ℝ)) (fun _ => p₁) (fun _ => p₂) (commonTW (stratW V k)) with
    hμd
  -- the gaps are the informations of the super-channel
  have hG₂ : twGap₂ μ = cInfo (prodDist p₁ p₂) (stratW V k) := by
    rw [hμd, twGap₂_eq hq (fun _ => hp₁) (fun _ => hp₂) hW', twLaw_unit_info₁ hp₁ hp₂ hW',
      twcInfo₁, show bcMarg₂ (commonTW (stratW V k)) = stratW V k from funext bcMarg₂_commonTW]
  have hG₁ : twGap₁ μ = cInfo (prodDist p₂ p₁) fun t => stratW V k t.swap := by
    rw [hμd, twGap₁_eq hq (fun _ => hp₁) (fun _ => hp₂) hW', twLaw_unit_info₂ hp₁ hp₂ hW', twcInfo₂]
    have e₁ : (fun a : Strat k X₂ Y × Strat k X₁ Y => prodDist p₁ p₂ a.swap) = prodDist p₂ p₁ := by
      funext a
      simp [prodDist, mul_comm]
    have e₂ : (fun t : Strat k X₂ Y × Strat k X₁ Y => bcMarg₁ (commonTW (stratW V k)) t.swap) =
        fun t => stratW V k t.swap := funext fun t => bcMarg₁_commonTW _
    rw [e₁, e₂]
  rw [← hG₂] at h₁
  rw [← hG₁] at h₂
  have hE₁ : 0 ≤ twErr₁ μ := twErr_nonneg hμ _ _ _
  have hE₂ : 0 ≤ twErr₂ μ := twErr_nonneg hμ _ _ _
  -- a small `ε`
  set g := min (twGap₂ μ - k * (R₁ * log 2)) (twGap₁ μ - k * (R₂ * log 2)) with hg
  have hg0 : 0 < g := lt_min (by linarith) (by linarith)
  set E := twErr₁ μ + twErr₂ μ + 1 with hE
  have hEpos : 0 < E := by linarith
  set ε := g / E with hε
  have hεpos : 0 < ε := by positivity
  have hεE : E * ε = g := by
    rw [hε]
    field_simp
  have hg₂ : k * (R₁ * log 2) + twErr₂ μ * ε + ε ≤ twGap₂ μ := by
    have : g ≤ twGap₂ μ - k * (R₁ * log 2) := min_le_left _ _
    have h3 : (twErr₂ μ + 1) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
    linarith
  have hg₁ : k * (R₂ * log 2) + twErr₁ μ * ε + ε ≤ twGap₁ μ := by
    have : g ≤ twGap₁ μ - k * (R₂ * log 2) := min_le_right _ _
    have h3 : (twErr₁ μ + 1) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
    linarith
  set K₁ := 2 * exp (k * (|R₁| * log 2)) with hK₁
  set K₂ := 2 * exp (k * (|R₂| * log 2)) with hK₂
  have hprob := tendsto_prob_robustTypicalSet hμ hεpos
  have hexp : Tendsto (fun m : ℕ => exp (-(m * ε))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_nat hεpos
  have hlim : Tendsto (fun m : ℕ => 2 * (1 - prob (iidPMF μ m) (robustTypicalSet μ m ε)) +
      K₂ * exp (-(m * ε)) + K₁ * exp (-(m * ε))) atTop (𝓝 (2 * (1 - 1) + K₂ * 0 + K₁ * 0)) :=
    (((tendsto_const_nhds.sub hprob).const_mul _).add (hexp.const_mul _)).add (hexp.const_mul _)
  have hdiv : Tendsto (fun N : ℕ => N / k) atTop atTop :=
    Nat.tendsto_div_const_atTop hk.ne'
  have key : ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      ∃ c : TWCCode (2 ^ ⌈(N : ℝ) * R₁⌉₊) (2 ^ ⌈(N : ℝ) * R₂⌉₊) N X₁ X₂ Y Y,
        c.errProb (commonTW V) ≤ δ := by
    intro δ hδ
    have hev := (tendsto_order.mp hlim).2 δ (by simpa using hδ)
    filter_upwards [hdiv.eventually hev] with N hn
    set m := N / k with hm
    obtain ⟨c', hc'⟩ := exists_twCode_gaps (M₁ := 2 ^ ⌈(N : ℝ) * R₁⌉₊) (M₂ := 2 ^ ⌈(N : ℝ) * R₂⌉₊)
      (n := m) hq (fun _ => hp₁) (fun _ => hp₂) hW' (W := commonTW (stratW V k)) ε
    have hle : m * k ≤ N := Nat.div_mul_le_self N k
    have hlt : N < k * (m + 1) := Nat.lt_mul_div_succ N hk
    refine ⟨blockCode c' N, ?_⟩
    have e : (blockCode c' N).errProb (commonTW V) = c'.errProb (commonTW (stratW V k)) := by
      simp only [TWCCode.errProb, TWCCode.err₁_commonTW, TWCCode.err₂_commonTW]
      rw [err₁_blockCode c' hV hle, err₂_blockCode c' hV hle]
    rw [e]
    rw [← hμd] at hc'
    have t₁ := blockTerm_le (k := k) (m := m) (N := N) (R := R₂) (G := twGap₁ μ) (E := twErr₁ μ)
      (ε := ε) hlt fun _ => hg₁
    have t₂ := blockTerm_le (k := k) (m := m) (N := N) (R := R₁) (G := twGap₂ μ) (E := twErr₂ μ)
      (ε := ε) hlt fun _ => hg₂
    rw [← hK₂] at t₁
    rw [← hK₁] at t₂
    linarith
  obtain ⟨c, hc⟩ := exists_seq_tendsto
    (C := fun N : ℕ => TWCCode (2 ^ ⌈(N : ℝ) * R₁⌉₊) (2 ^ ⌈(N : ℝ) * R₂⌉₊) N X₁ X₂ Y Y)
    (fun N c => c.errProb (commonTW V))
    (fun N c => add_nonneg
      (errProb_nonneg (c.law_isPMF (commonTW_isChannel hV) (by positivity) (by positivity)) _ _ _)
      (errProb_nonneg (c.law_isPMF (commonTW_isChannel hV) (by positivity) (by positivity)) _ _ _))
    key
  exact ⟨c, hc⟩

/-- **Theorem 7, page 18-55 of [elgamal2010], with strategies.** The capacity region of the two-way
channel with a common output is the closure of the union of the regions of the strategies of length
`k`. -/
theorem twcCapacityRegion_eq_closure_iUnion (hV : IsChannel V) :
    twcCapacityRegion (commonTW V) = closure (⋃ k : ℕ, ⋃ _ : 0 < k, twcMultiRegion V k) := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  refine Set.Subset.antisymm ?_ ?_
  · exact closure_minimal (fun R hR => IsAchievableTWC.mem_closure_iUnion_twcMultiRegion hV hR)
      isClosed_closure
  · refine closure_minimal ?_ isClosed_closure
    intro R hR
    obtain ⟨k, hk, p₁, p₂, hp₁, hp₂, h₁, h₂⟩ := Set.mem_iUnion₂.mp hR
    have hmem : ∀ j : ℕ, (R.1 - 1 / ((j : ℝ) + 1), R.2 - 1 / ((j : ℝ) + 1)) ∈
        {R | IsAchievableTWC (commonTW V) R.1 R.2} := by
      intro j
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      have hs : ∀ r : ℝ, k * ((r - 1 / ((j : ℝ) + 1)) * log 2) < k * (r * log 2) := fun r => by
        refine mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (by linarith) hlog2) hk'
      exact isAchievableTWC_of_multi hk hp₁ hp₂ hV ((hs _).trans_le h₁) ((hs _).trans_le h₂)
    have hlim : Tendsto (fun j : ℕ => (R.1 - 1 / ((j : ℝ) + 1), R.2 - 1 / ((j : ℝ) + 1))) atTop
        (𝓝 R) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h1 : Tendsto (fun j : ℕ => R.1 - 1 / ((j : ℝ) + 1)) atTop (𝓝 (R.1 - 0)) :=
        tendsto_const_nhds.sub h0
      have h2 : Tendsto (fun j : ℕ => R.2 - 1 / ((j : ℝ) + 1)) atTop (𝓝 (R.2 - 0)) :=
        tendsto_const_nhds.sub h0
      rw [sub_zero] at h1 h2
      exact h1.prodMk_nhds h2
    exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

end Rates

end InfoTheory
