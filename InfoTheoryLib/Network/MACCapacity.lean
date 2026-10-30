/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACAchievability
public import InfoTheoryLib.Network.MACConverse
public import Mathlib.Analysis.Convex.Caratheodory

/-!
# The capacity region of the multiple-access channel

The achievability of the pentagons (Section 15.3.1), time sharing (Theorem 15.3.2), Lemma 15.3.1
and the converse (Section 15.3.4) together determine the capacity region of the discrete
memoryless multiple-access channel: it is the closure of the convex hull of the pentagons
`R₁ < I(X₁; Y | X₂)`, `R₂ < I(X₂; Y | X₁)`, `R₁ + R₂ < I(X₁, X₂; Y)` over the product input
distributions (Theorem 15.3.1), and equivalently the closure of the region (15.89) defined with a
time-sharing variable (Theorem 15.3.4).

## Main statements

* `macRateRegions_subset_macSlackSet`: every rate pair in a pentagon is achievable up to an
  arbitrarily small loss.
* `macCapacityRegion_eq`: **Theorem 15.3.1 (Multiple-access channel capacity).**
* `convex_macCapacityRegion`: **Theorem 15.3.2**, the capacity region is convex.
* `macCapacityRegion_eq_closure_macRegion`: **Theorem 15.3.4.**
* `exists_convex_combination_le_three`: **Theorem 15.3.5 (Carathéodory)** in the plane, a point
  of the convex hull of a set is a convex combination of at most three points of the set.
* `isAchievableMAC_of_isAchievableRate`: **Section 15.3.2**, if sender 2 sends a fixed symbol,
  sender 1 can use any rate achievable over the resulting single-user channel (point `A` of
  Figure 15.14).
* `sum_le_log_card_of_mem_macCapacityRegion`: the sum rate is at most `log |𝒴|`
  (Example 15.3.2).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 15.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}

section Capacity

variable [Nonempty α₁] [Nonempty α₂]

/-- Every rate pair in a pentagon is achievable up to an arbitrarily small loss. -/
theorem macRateRegions_subset_macSlackSet (hW : IsChannel W) :
    macRateRegions W ⊆ macSlackSet W := by
  rintro R ⟨p₁, p₂, hp₁, hp₂, h1, h2, h3⟩ δ hδ
  exact isAchievableMAC_of_mem_macRateRegion hp₁ hp₂ hW (R := (R.1 - δ, R.2 - δ))
    ⟨by dsimp only; linarith, by dsimp only; linarith, by dsimp only; linarith⟩

/-- **Section 15.3.3** Time sharing achieves the convex hull of the pentagons. -/
theorem closure_convexHull_subset_macCapacityRegion (hW : IsChannel W) :
    closure (convexHull ℝ (macRateRegions W)) ⊆ macCapacityRegion W :=
  closure_minimal ((convexHull_min (macRateRegions_subset_macSlackSet hW)
    (convex_macSlackSet hW)).trans macSlackSet_subset_macCapacityRegion) isClosed_closure

omit [Nonempty α₁] [Nonempty α₂] in
/-- **Section 15.3.4 (converse)** The capacity region is in the closure of the region (15.89). -/
theorem macCapacityRegion_subset_closure_macRegion (hW : IsChannel W) :
    macCapacityRegion W ⊆ closure (macRegion W) :=
  closure_minimal (fun _ hR => hR.mem_closure_macRegion hW) isClosed_closure

/-- **Theorem 15.3.1 (Multiple-access channel capacity).** The capacity region of a discrete
memoryless multiple-access channel is the closure of the convex hull of the rate pairs with
`R₁ < I(X₁; Y | X₂)`, `R₂ < I(X₂; Y | X₁)` and `R₁ + R₂ < I(X₁, X₂; Y)` for some product
distribution `p₁(x₁) p₂(x₂)`. -/
theorem macCapacityRegion_eq (hW : IsChannel W) :
    macCapacityRegion W = closure (convexHull ℝ (macRateRegions W)) :=
  le_antisymm ((macCapacityRegion_subset_closure_macRegion hW).trans
    (closure_minimal (macRegion_subset_closure_convexHull hW) isClosed_closure))
    (closure_convexHull_subset_macCapacityRegion hW)

/-- **Theorem 15.3.4.** The capacity region is the closure of the rate pairs with
`R₁ ≤ I(X₁; Y | X₂, Q)`, `R₂ ≤ I(X₂; Y | X₁, Q)`, `R₁ + R₂ ≤ I(X₁, X₂; Y | Q)` for a
time-sharing variable `Q` and inputs independent given `Q`. -/
theorem macCapacityRegion_eq_closure_macRegion (hW : IsChannel W) :
    macCapacityRegion W = closure (macRegion W) :=
  le_antisymm (macCapacityRegion_subset_closure_macRegion hW)
    ((closure_minimal (macRegion_subset_closure_convexHull hW) isClosed_closure).trans
      (closure_convexHull_subset_macCapacityRegion hW))

omit [Fintype α₁] [Fintype α₂] in
/-- **Theorem 15.3.2.** The capacity region of a multiple-access channel is convex. -/
theorem convex_macCapacityRegion [Finite α₁] [Finite α₂] (hW : IsChannel W) :
    Convex ℝ (macCapacityRegion W) := by
  have := Fintype.ofFinite α₁
  have := Fintype.ofFinite α₂
  rw [macCapacityRegion_eq hW]
  exact (convex_convexHull ℝ _).closure

end Capacity

/-- **Theorem 15.3.5 (Carathéodory), in the plane.** Any point of the convex hull of a set in
`ℝ²` is a convex combination of at most three points of the set. -/
theorem exists_convex_combination_le_three {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ s) :
    ∃ k ≤ 3, ∃ (w : Fin k → ℝ) (z : Fin k → ℝ × ℝ), (∀ i, z i ∈ s) ∧ (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  obtain ⟨ι, _, z, w, hzs, hz, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ 3 := by
    have h1 := hz.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ (ℝ × ℝ) :=
      Submodule.finrank_le _
    rw [Module.finrank_prod, Module.finrank_self] at h2
    omega
  set e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, hcard, fun i => w (e.symm i), fun i => z (e.symm i),
    fun i => hzs ⟨_, rfl⟩, fun i => (hw _).le, ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm w]
    exact hw1
  · rw [Equiv.sum_comp e.symm (fun i => w i • z i)]
    exact hwz

/-! ### Corner points and simple bounds -/

/-- A code for the single-user channel `p(y | x₁, b)`, as a multiple-access code in which
sender 2 has a single message and always sends `b`. -/
def MACCode.ofChannelCode {M M₂ n : ℕ} (c : ChannelCode M n α₁ β) (b : α₂) (hM₂ : M₂ = 1) :
    MACCode M M₂ n α₁ α₂ β :=
  ⟨c.enc, fun _ _ => b, fun y => (c.dec y, ⟨0, by omega⟩)⟩

omit [Fintype α₁] [Fintype α₂] in
lemma MACCode.avgErrProb_ofChannelCode {M M₂ n : ℕ} (c : ChannelCode M n α₁ β) (b : α₂)
    (hM₂ : M₂ = 1) :
    (MACCode.ofChannelCode c b hM₂).avgErrProb W = c.avgErrProb (fun a => W (a, b)) := by
  subst hM₂
  classical
  simp only [MACCode.avgErrProb, ChannelCode.avgErrProb, MACCode.condErrProb,
    ChannelCode.condErrProb, Fin.sum_univ_one, Nat.cast_one, mul_one]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun y _ => ?_
  have e : (MACCode.ofChannelCode c b rfl).dec y = (c.dec y, 0) := rfl
  simp only [e, ne_eq, Prod.mk.injEq, and_true]
  rfl

omit [Fintype α₁] [Fintype α₂] in
/-- **Section 15.3.2 (point `A` of Figure 15.14).** If sender 2 always sends the symbol `b`,
sender 1 sees the single-user channel `p(y | x₁, b)`, and every rate achievable over it is
achievable for sender 1, with `R₂ = 0`. -/
theorem isAchievableMAC_of_isAchievableRate (hW : IsChannel W) (b : α₂) {R : ℝ}
    (h : IsAchievableRate (fun a => W (a, b)) R) : IsAchievableMAC W R 0 := by
  obtain ⟨c, hc⟩ := h
  have h1 : ∀ n : ℕ, ⌈exp (n * (0 : ℝ))⌉₊ = 1 := fun n => by simp
  refine ⟨fun n => MACCode.ofChannelCode (c n) b (h1 n), ?_⟩
  simp only [MACCode.avgErrProb_ofChannelCode]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => (c n).avgErrProb_nonneg fun a => hW (a, b))
    fun n => (c n).avgErrProb_le_maxErrProb

/-- `I(X₁, X₂; Y) ≤ log |𝒴|`. -/
lemma macInfo₁₂_le_log_card {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hW : IsChannel W) : macInfo₁₂ p₁ p₂ W ≤ log (Fintype.card β) := by
  have hμ := macJoint_isPMF hp₁ hp₂ hW
  rw [macInfo₁₂, mutualInfo_eq_entropy_sub_condEntropy' hμ]
  linarith [entropyRV_le_log_card hμ (Prod.snd : (α₁ × α₂) × β → β),
    condEntropy_nonneg hμ (Prod.snd : (α₁ × α₂) × β → β) Prod.fst]

omit [Fintype α₁] [Fintype α₂] in
/-- **Example 15.3.2** In the capacity region of any multiple-access channel, the sum rate is at
most `log |𝒴|`: for the binary multiplier channel `Y = X₁X₂`, `R₁ + R₂ ≤ log 2`. -/
theorem sum_le_log_card_of_mem_macCapacityRegion [Finite α₁] [Finite α₂] (hW : IsChannel W)
    {R : ℝ × ℝ} (hR : R ∈ macCapacityRegion W) : R.1 + R.2 ≤ log (Fintype.card β) := by
  have := Fintype.ofFinite α₁
  have := Fintype.ofFinite α₂
  have hc : IsClosed {R : ℝ × ℝ | R.1 + R.2 ≤ log (Fintype.card β)} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hsub : macRegion W ⊆ {R : ℝ × ℝ | R.1 + R.2 ≤ log (Fintype.card β)} := by
    rintro R ⟨k, q, p₁, p₂, hq, hp₁, hp₂, -, -, h3⟩
    refine h3.trans ?_
    calc ∑ i, q i * macInfo₁₂ (p₁ i) (p₂ i) W ≤ ∑ i, q i * log (Fintype.card β) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (macInfo₁₂_le_log_card (hp₁ i) (hp₂ i) hW) (hq.nonneg i)
      _ = log (Fintype.card β) := by rw [← sum_mul, hq.sum_eq_one, one_mul]
  exact closure_minimal hsub hc (macCapacityRegion_subset_closure_macRegion hW hR)

/-- A code for the single-user channel `p(y | a, x₂)`, as a multiple-access code in which
sender 1 has a single message and always sends `a`. -/
def MACCode.ofChannelCode₂ {M M₁ n : ℕ} (c : ChannelCode M n α₂ β) (a : α₁) (hM₁ : M₁ = 1) :
    MACCode M₁ M n α₁ α₂ β :=
  ⟨fun _ _ => a, c.enc, fun y => (⟨0, by omega⟩, c.dec y)⟩

omit [Fintype α₁] [Fintype α₂] in
lemma MACCode.avgErrProb_ofChannelCode₂ {M M₁ n : ℕ} (c : ChannelCode M n α₂ β) (a : α₁)
    (hM₁ : M₁ = 1) :
    (MACCode.ofChannelCode₂ c a hM₁).avgErrProb W = c.avgErrProb (fun b => W (a, b)) := by
  subst hM₁
  classical
  simp only [MACCode.avgErrProb, ChannelCode.avgErrProb, MACCode.condErrProb,
    ChannelCode.condErrProb, Fin.sum_univ_one, Nat.cast_one, one_mul]
  congr 1
  refine sum_congr rfl fun j _ => sum_congr rfl fun y _ => ?_
  have e : (MACCode.ofChannelCode₂ c a rfl).dec y = (0, c.dec y) := rfl
  simp only [e, ne_eq, Prod.mk.injEq, true_and]
  rfl

omit [Fintype α₁] [Fintype α₂] in
/-- **Section 15.3.2 (point `D` of Figure 15.14).** If sender 1 always sends the symbol `a`,
sender 2 can use any rate achievable over the single-user channel `p(y | a, x₂)`, with
`R₁ = 0`. -/
theorem isAchievableMAC_of_isAchievableRate₂ (hW : IsChannel W) (a : α₁) {R : ℝ}
    (h : IsAchievableRate (fun b => W (a, b)) R) : IsAchievableMAC W 0 R := by
  obtain ⟨c, hc⟩ := h
  have h1 : ∀ n : ℕ, ⌈exp (n * (0 : ℝ))⌉₊ = 1 := fun n => by simp
  refine ⟨fun n => MACCode.ofChannelCode₂ (c n) a (h1 n), ?_⟩
  simp only [MACCode.avgErrProb_ofChannelCode₂]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => (c n).avgErrProb_nonneg fun b => hW (a, b))
    fun n => (c n).avgErrProb_le_maxErrProb

omit [Fintype α₁] [Fintype α₂] in
/-- In the capacity region of any multiple-access channel, `R₁ ≤ log |𝒴|`, `R₂ ≤ log |𝒴|` and
`R₁ + R₂ ≤ log |𝒴|`. -/
theorem le_log_card_of_mem_macCapacityRegion [Finite α₁] [Finite α₂] (hW : IsChannel W)
    {R : ℝ × ℝ} (hR : R ∈ macCapacityRegion W) :
    R.1 ≤ log (Fintype.card β) ∧ R.2 ≤ log (Fintype.card β) ∧
      R.1 + R.2 ≤ log (Fintype.card β) := by
  have := Fintype.ofFinite α₁
  have := Fintype.ofFinite α₂
  set L := log (Fintype.card β)
  have hc : IsClosed {R : ℝ × ℝ | R.1 ≤ L ∧ R.2 ≤ L ∧ R.1 + R.2 ≤ L} :=
    (isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_snd continuous_const).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hsub : macRegion W ⊆ {R : ℝ × ℝ | R.1 ≤ L ∧ R.2 ≤ L ∧ R.1 + R.2 ≤ L} := by
    rintro R ⟨k, q, p₁, p₂, hq, hp₁, hp₂, h1, h2, h3⟩
    have hb : ∀ f : Fin k → ℝ, (∀ i, f i ≤ L) → ∑ i, q i * f i ≤ L := fun f hf => by
      calc ∑ i, q i * f i ≤ ∑ i, q i * L :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (hq.nonneg i)
        _ = L := by rw [← sum_mul, hq.sum_eq_one, one_mul]
    have hI₃ := fun i => macInfo₁₂_le_log_card (hp₁ i) (hp₂ i) hW
    refine ⟨h1.trans (hb _ fun i => (macInfo₁_le_macInfo₁₂ (hp₁ i) (hp₂ i) hW).trans (hI₃ i)),
      h2.trans (hb _ fun i => (macInfo₂_le_macInfo₁₂ (hp₁ i) (hp₂ i) hW).trans (hI₃ i)),
      h3.trans (hb _ hI₃)⟩
  exact closure_minimal hsub hc (macCapacityRegion_subset_closure_macRegion hW hR)

omit [Fintype α₁] [Fintype α₂] in
/-- The capacity region is closed under lowering the rates. -/
theorem mem_macCapacityRegion_of_le [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W)
    {R R' : ℝ × ℝ} (hR : R ∈ macCapacityRegion W) (h₁ : R'.1 ≤ R.1) (h₂ : R'.2 ≤ R.2) :
    R' ∈ macCapacityRegion W := by
  set φ : ℝ × ℝ → ℝ × ℝ := fun x => x - (R - R')
  have hφ : Continuous φ := continuous_id.sub continuous_const
  have himage : φ '' {R | IsAchievableMAC W R.1 R.2} ⊆ {R | IsAchievableMAC W R.1 R.2} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.mono hW (by simp only [φ, Prod.fst_sub]; linarith)
      (by simp only [φ, Prod.snd_sub]; linarith)
  have := image_closure_subset_closure_image hφ ⟨R, hR, rfl⟩
  simp only [φ, sub_sub_cancel] at this
  exact closure_mono himage this

end InfoTheory
