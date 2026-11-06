/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Networking.AsyncError
public import InfoTheoryLib.Networking.AsyncMACConverse

/-!
# The totally asynchronous multiple-access channel: achievability

The achievability of Theorem 2 of Lecture 24 of El Gamal and Kim, and the theorem itself.

The proof differs from the one in the notes, which has several gaps:

* The notes detect the delays from preambles, using Lemma 2, which assumes `p(x, y) ≠ p(x) p(y)`,
  an assumption Theorem 2 does not have. It fails on the binary adder `Y = X₁ ⊕ X₂` for the input
  distributions with sum rate `1`, where one input is uniform and the other input is independent of
  the output. Here there is no separate synchronization: the decoder searches over the delays and
  the messages jointly.
* The notes test joint typicality of the whole block and then use the joint typicality lemma for
  each of the groups of slots with a given pattern of errors, but typicality of the whole block does
  not imply typicality of each group. Here each group has its own information-density test, and the
  decoder tests all the groups.
* The notes bound the error averaged over the codebooks for each pair of delays, which does not give
  one code that is good for all of them, since the bounds from the law of large numbers are not
  summable over the `n²` pairs. Here all the bounds are exponential.
* The notes take the same codebook for all the subblocks, and they discard the error patterns with
  a repeated wrong message without justification. Here each position of a block has its own
  independent letters, so the only dependent hypotheses are those using sub-messages actually sent,
  and they are handled by the conflict bound.

## Main definitions

* `asyncTableCode`: the code defined by the two tables of letters.

## Main statements

* `asyncE_decA_le`: the error of the decoder of one sender, averaged over the tables.
* `exists_asyncCode`: for suitable parameters, one code is good for all the delays.
* `isAchievableAsync_of_lt`: **Theorem 2 of Lecture 24, achievability**.
* `asyncCapacityRegionBits_eq`: **Theorem 2 of Lecture 24**: the capacity region is the union of the
  pentagons over `p(x₁) p(x₂)`, with no time sharing.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset Filter Topology Real

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]
  {p₁ : α₁ → ℝ} {p₂ : α₂ → ℝ} {W : α₁ × α₂ → β → ℝ} {n k b V₁ V₂ M₁ M₂ : ℕ}

section Decoder

variable [NeZero V₁] [NeZero V₂] [NeZero M₁]

/-- The failure event of the true hypothesis, for a pair of sets of segments. -/
def AsyncFail (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (k b : ℕ) (D : ℝ)
    (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂)
    (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂) (d₁ d₂ : Fin n)
    (τ₁ : Fin n × Fin V₁ → α₁) (τ₂ : Fin n × Fin V₂ → α₂) (y : Fin (2 * n - 1) → β)
    (JA JB : Finset (Fin (b + 3))) (i : Fin 3) : Prop :=
  match i with
  | 0 => ∏ t ∈ asyncG₂ k b d₁ d₂ JA JB, macRatio₁ p₁ W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t))
      (τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t) <
        exp ((asyncG₂ k b d₁ d₂ JA JB).card * macInfo₁ p₁ p₂ W - D)
  | 1 => ∏ t ∈ asyncG₃ k b d₁ d₂ JA JB, macRatio₂ p₂ W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t))
      (τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t) <
        exp ((asyncG₃ k b d₁ d₂ JA JB).card * macInfo₂ p₁ p₂ W - D)
  | 2 => ∏ t ∈ asyncG₄ k b d₁ d₂ JA JB, macRatio₁₂ p₁ p₂ W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t))
      (τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t) <
        exp ((asyncG₄ k b d₁ d₂ JA JB).card * macInfo₁₂ p₁ p₂ W - D)

/-- The hypotheses with a wrong message of sender `A`. -/
def asyncWrong {M V : ℕ} [NeZero V] (sub : Fin M → Fin (b + 3) → Fin V) (m : Fin 3 → Fin M) :
    Finset (Fin (b + 3) → Fin V) :=
  (asyncHyp (asyncMsg b)).filter fun v => ∃ j ∈ asyncMsg b, v j ≠ sub (m 1) j

/-- **The union bound for the decoder.** The decoder errs only if the true hypothesis fails one of
its tests, or a hypothesis with a wrong message passes all of them. -/
theorem ite_decA_le {D : ℝ} (hk : 0 < k) (hu : n < (b + 3) * k)
    {sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁} {sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂}
    (hsub₁ : IsAsyncSub sub₁) (hsub₂ : IsAsyncSub sub₂) (m₁ : Fin 3 → Fin M₁)
    (m₂ : Fin 3 → Fin M₂) (d₁ d₂ : Fin n) (τ₁ : Fin n × Fin V₁ → α₁) (τ₂ : Fin n × Fin V₂ → α₂)
    (y : Fin (2 * n - 1) → β) :
    (if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) ≤
      (∑ JA, ∑ JB, ∑ i : Fin 3, (open Classical in
        if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then (1 : ℝ) else 0)) +
      ∑ dA : Fin n, ∑ dB : Fin n, ∑ vA ∈ asyncWrong sub₁ m₁,
        ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB), (open Classical in
        if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then (1 : ℝ) else 0) := by
  classical
  set F := ∑ JA, ∑ JB, ∑ i : Fin 3,
    if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then (1 : ℝ) else 0 with hF
  set H := ∑ dA : Fin n, ∑ dB : Fin n, ∑ vA ∈ asyncWrong sub₁ m₁,
    ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
    if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then (1 : ℝ) else 0 with hH
  have hite : ∀ P : Prop, 0 ≤ (if P then (1 : ℝ) else 0) := fun P => by
    split_ifs <;> norm_num
  have hF0 : 0 ≤ F := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hite _
  have hH0 : 0 ≤ H := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    sum_nonneg fun _ _ => hite _
  split_ifs with hne
  · rcases asyncDecA_ne hne with hrej | ⟨m', hm', hacc⟩
    · -- The true hypothesis fails a test.
      have hfail : ∃ JA JB i, AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i := by
        by_contra hcon
        push Not at hcon
        apply hrej
        refine ⟨d₁, d₂, asyncTrueV k sub₂ m₂ d₁ d₂, asyncTrueV_mem sub₂ m₂ d₁ d₂, ?_⟩
        refine asyncPasses_true hk hu hsub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y fun JA JB => ?_
        refine ⟨?_, ?_, ?_⟩
        · exact not_lt.1 (hcon JA JB 0)
        · exact not_lt.1 (hcon JA JB 1)
        · exact not_lt.1 (hcon JA JB 2)
      obtain ⟨JA, JB, i, hi⟩ := hfail
      have h1 : (1 : ℝ) ≤ F := by
        calc (1 : ℝ) = if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then
              (1 : ℝ) else 0 := by simp [hi]
          _ ≤ ∑ i : Fin 3, if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then
              (1 : ℝ) else 0 := single_le_sum (f := fun i : Fin 3 =>
                if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then
              (1 : ℝ) else 0) (fun _ _ => hite _) (mem_univ i)
          _ ≤ ∑ JB, ∑ i : Fin 3, if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i
            then
              (1 : ℝ) else 0 := single_le_sum (f := fun JB => ∑ i : Fin 3,
                if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then
              (1 : ℝ) else 0) (fun _ _ => sum_nonneg fun _ _ => hite _) (mem_univ JB)
          _ ≤ F := single_le_sum (f := fun JA => ∑ JB, ∑ i : Fin 3,
                if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then
              (1 : ℝ) else 0) (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hite _)
                (mem_univ JA)
      linarith
    · -- A wrong message passes.
      obtain ⟨dA, dB, vB, hvB, hpass⟩ := hacc
      have hw : sub₁ m' ∈ asyncWrong sub₁ m₁ := by
        refine mem_filter.2 ⟨?_, ?_⟩
        · simp only [asyncHyp, mem_filter, mem_univ, true_and]
          exact hsub₁.pilot m'
        · by_contra hcon
          push Not at hcon
          exact hm' (hsub₁.inj _ _ hcon)
      have h1 : (1 : ℝ) ≤ H := by
        have e0 : (1 : ℝ) = if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB (sub₁ m') vB y then
            (1 : ℝ) else 0 := by simp [hpass]
        rw [e0]
        refine le_trans ?_ (single_le_sum (f := fun dA : Fin n => ∑ dB : Fin n,
          ∑ vA ∈ asyncWrong sub₁ m₁, ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
          if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then (1 : ℝ) else 0)
          (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hite _)
          (mem_univ dA))
        refine le_trans ?_ (single_le_sum (f := fun dB : Fin n =>
          ∑ vA ∈ asyncWrong sub₁ m₁, ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
          if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then (1 : ℝ) else 0)
          (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hite _) (mem_univ dB))
        refine le_trans ?_ (single_le_sum (f := fun vA =>
          ∑ vB ∈ asyncHyp (V := V₂) (asyncSegsB k b dA dB),
          if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB vA vB y then (1 : ℝ) else 0)
          (fun _ _ => sum_nonneg fun _ _ => hite _) hw)
        exact single_le_sum (f := fun vB =>
          if AsyncPasses p₁ p₂ W k b D τ₁ τ₂ dA dB (sub₁ m') vB y then (1 : ℝ) else 0)
          (fun _ _ => hite _) hvB
      linarith
  · linarith

/-- The Chernoff constants of the three densities. -/
structure AsyncChernoff (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ) (W : α₁ × α₂ → β → ℝ) (l₁ l₂ l₃ c : ℝ) :
    Prop where
  pos₁ : 0 < l₁
  pos₂ : 0 < l₂
  pos₃ : 0 < l₃
  mgf₁ : asyncMGF p₁ p₂ W (macRatio₁ p₁ W) l₁ ≤ exp (-(l₁ * (macInfo₁ p₁ p₂ W - c)))
  mgf₂ : asyncMGF p₁ p₂ W (macRatio₂ p₂ W) l₂ ≤ exp (-(l₂ * (macInfo₂ p₁ p₂ W - c)))
  mgf₃ : asyncMGF p₁ p₂ W (macRatio₁₂ p₁ p₂ W) l₃ ≤ exp (-(l₃ * (macInfo₁₂ p₁ p₂ W - c)))

lemma exists_asyncChernoff (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) {c : ℝ}
    (hc : 0 < c) : ∃ l₁ l₂ l₃, AsyncChernoff p₁ p₂ W l₁ l₂ l₃ c := by
  obtain ⟨l₁, h1, h1'⟩ := exists_asyncMGF_le hp₁ hp₂ hW (macRatio₁ p₁ W)
    (macInfo₁_eq_sum_log hp₁ hp₂ hW) hc
  obtain ⟨l₂, h2, h2'⟩ := exists_asyncMGF_le hp₁ hp₂ hW (macRatio₂ p₂ W)
    (macInfo₂_eq_sum_log hp₁ hp₂ hW) hc
  obtain ⟨l₃, h3, h3'⟩ := exists_asyncMGF_le hp₁ hp₂ hW (macRatio₁₂ p₁ p₂ W)
    (macInfo₁₂_eq_sum_log hp₁ hp₂ hW) hc
  exact ⟨l₁, l₂, l₃, h1, h2, h3, h1', h2', h3'⟩

omit [NeZero V₁] [NeZero V₂] [NeZero M₁] in
/-- **The bound for the true hypothesis**, over all its tests. -/
theorem asyncE_fails_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (hk : 0 < k) {D : ℝ}
    (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂)
    (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂) (d₁ d₂ : Fin n) {l₁ l₂ l₃ c : ℝ}
    (hC : AsyncChernoff p₁ p₂ W l₁ l₂ l₃ c) (hc : 0 ≤ c) (hcD : n * c ≤ D / 2)
    (JA JB : Finset (Fin (b + 3))) :
    ∑ i : Fin 3, asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂)
      (fun τ₁ τ₂ y => open Classical in
        if AsyncFail p₁ p₂ W k b D sub₁ sub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y JA JB i then (1 : ℝ) else 0) ≤
      exp (-(l₁ * D / 2)) + exp (-(l₂ * D / 2)) + exp (-(l₃ * D / 2)) := by
  classical
  rw [Fin.sum_univ_three]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact asyncE_fail_le hp₁ hp₂ hW hk sub₁ sub₂ m₁ m₂ d₁ d₂ (filter_subset _ _) _
      (fun x₁ x₂ y h1 _ h3 => infoRatio_pos hp₁ (fun a => hW (a, x₂)) h1 h3) hC.pos₁ hC.mgf₁ hc hcD
        _
      (fun τ₁ τ₂ y => le_of_eq (by simp only [AsyncFail]; congr))
  · exact asyncE_fail_le hp₁ hp₂ hW hk sub₁ sub₂ m₁ m₂ d₁ d₂ (filter_subset _ _) _
      (fun x₁ x₂ y _ h2 h3 => infoRatio_pos hp₂ (fun b => hW (x₁, b)) h2 h3) hC.pos₂ hC.mgf₂ hc hcD
        _
      (fun τ₁ τ₂ y => le_of_eq (by simp only [AsyncFail]; congr))
  · exact asyncE_fail_le hp₁ hp₂ hW hk sub₁ sub₂ m₁ m₂ d₁ d₂ (filter_subset _ _) _
      (fun x₁ x₂ y h1 h2 h3 => infoRatio_pos (hp₁.prodDist hp₂) hW (mul_pos h1 h2) h3) hC.pos₃
      hC.mgf₃ hc hcD _ (fun τ₁ τ₂ y => le_of_eq (by simp only [AsyncFail]; congr))

/-- **The error of the decoder of sender `A`, averaged over the tables.** -/
theorem asyncE_decA_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) (hk : 0 < k)
    (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) {D : ℝ} {sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁}
    {sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂} (hsub₁ : IsAsyncSub sub₁) (hsub₂ : IsAsyncSub sub₂)
    (m₁ : Fin 3 → Fin M₁) (m₂ : Fin 3 → Fin M₂) (d₁ d₂ : Fin n) {r₁ r₂ γ : ℝ} (hr₁ : 0 ≤ r₁)
    (hr₂ : 0 ≤ r₂) (hγ : 0 < γ) (hV₁ : (V₁ : ℝ) ≤ 2 * exp (k * r₁))
    (hV₂ : (V₂ : ℝ) ≤ 2 * exp (k * r₂)) (hA : 2 ≤ V₁ → r₁ + γ ≤ macInfo₁ p₁ p₂ W)
    (hB : 2 ≤ V₂ → r₂ + γ ≤ macInfo₂ p₁ p₂ W)
    (hAB : 2 ≤ V₁ → 2 ≤ V₂ → r₁ + r₂ + γ ≤ macInfo₁₂ p₁ p₂ W) {l₁ l₂ l₃ c : ℝ}
    (hC : AsyncChernoff p₁ p₂ W l₁ l₂ l₃ c) (hc : 0 ≤ c) (hcD : n * c ≤ D / 2) :
    asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂)
      (fun τ₁ τ₂ y => if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) ≤
    4 ^ (b + 3) * (exp (-(l₁ * D / 2)) + exp (-(l₂ * D / 2)) + exp (-(l₃ * D / 2))) +
      n ^ 2 * (4 ^ (b + 3) * (64 ^ (b + 3) * exp (-(γ * k - 3 * D)) +
        16 ^ (b + 3) * exp (-((γ * k - D) / 2)))) := by
  classical
  set a := asyncTrue k b sub₁ m₁ d₁ with ha
  set e := asyncTrue k b sub₂ m₂ d₂ with he
  refine (asyncE_mono hp₁ hp₂ hW a e fun τ₁ τ₂ y =>
    ite_decA_le hk hu hsub₁ hsub₂ m₁ m₂ d₁ d₂ τ₁ τ₂ y).trans ?_
  rw [asyncE_add]
  refine add_le_add ?_ ?_
  · rw [asyncE_sum]
    calc _ ≤ ∑ _JA : Finset (Fin (b + 3)), ∑ _JB : Finset (Fin (b + 3)),
          (exp (-(l₁ * D / 2)) + exp (-(l₂ * D / 2)) + exp (-(l₃ * D / 2))) := by
          refine sum_le_sum fun JA _ => ?_
          rw [asyncE_sum]
          refine sum_le_sum fun JB _ => ?_
          rw [asyncE_sum]
          exact asyncE_fails_le hp₁ hp₂ hW hk sub₁ sub₂ m₁ m₂ d₁ d₂ hC hc hcD JA JB
      _ = _ := by
          simp only [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          have : (4 : ℝ) ^ (b + 3) = 2 ^ (b + 3) * 2 ^ (b + 3) := by
            rw [← mul_pow]
            norm_num
          rw [this]
          ring
  · rw [asyncE_sum]
    calc _ ≤ ∑ _dA : Fin n, ∑ _dB : Fin n, (4 ^ (b + 3) *
          (64 ^ (b + 3) * exp (-(γ * k - 3 * D)) + 16 ^ (b + 3) * exp (-((γ * k - D) / 2)))) := by
          refine sum_le_sum fun dA _ => ?_
          rw [asyncE_sum]
          refine sum_le_sum fun dB _ => ?_
          rw [asyncE_sum]
          have h := sum_asyncE_passes_le (D := D) hp₁ hp₂ hW hk hl hu sub₁ sub₂ m₁ m₂ d₁ d₂ dA dB
            hr₁ hr₂ hγ hV₁ hV₂ hA hB hAB
          refine le_trans (le_of_eq ?_) h
          refine sum_congr rfl fun vA _ => ?_
          rw [asyncE_sum]
      _ = _ := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

end Decoder

/-! ### The two senders -/

/-- The channel with the two inputs exchanged. -/
def asyncSwap (W : α₁ × α₂ → β → ℝ) : α₂ × α₁ → β → ℝ := fun x => W (x.2, x.1)

omit [Fintype α₁] [Fintype α₂] in
lemma asyncSwap_isChannel (hW : IsChannel W) : IsChannel (asyncSwap W) := fun _ => hW _

lemma macInfo₁_asyncSwap (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁ p₂ p₁ (asyncSwap W) = macInfo₂ p₁ p₂ W := by
  rw [macInfo₁_eq_sum hp₂ hp₁ (asyncSwap_isChannel hW), macInfo₂_eq_sum hp₁ hp₂ hW]
  rfl

lemma macInfo₂_asyncSwap (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₂ p₂ p₁ (asyncSwap W) = macInfo₁ p₁ p₂ W := by
  rw [macInfo₂_eq_sum hp₂ hp₁ (asyncSwap_isChannel hW), macInfo₁_eq_sum hp₁ hp₂ hW]
  rfl

lemma macInfo₁₂_asyncSwap (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) :
    macInfo₁₂ p₂ p₁ (asyncSwap W) = macInfo₁₂ p₁ p₂ W := by
  have h1 : macInfo₁₂ p₂ p₁ (asyncSwap W) = mutualInfoOf (prodDist p₂ p₁) (asyncSwap W) := rfl
  have h2 : macInfo₁₂ p₁ p₂ W = mutualInfoOf (prodDist p₁ p₂) W := rfl
  rw [h1, h2, mutualInfoOf_eq_sum (hp₂.prodDist hp₁) (asyncSwap_isChannel hW),
    mutualInfoOf_eq_sum (hp₁.prodDist hp₂) hW]
  have e : ∀ F : α₁ × α₂ → ℝ, ∑ x : α₂ × α₁, F (x.2, x.1) = ∑ x, F x := fun F =>
    (Equiv.prodComm α₂ α₁).sum_comp F
  have e1 : ∀ y, ∑ x : α₂ × α₁, prodDist p₂ p₁ x * asyncSwap W x y =
      ∑ x : α₁ × α₂, prodDist p₁ p₂ x * W x y := fun y => by
    rw [← e fun x => prodDist p₁ p₂ x * W x y]
    refine sum_congr rfl fun x _ => ?_
    simp [prodDist, asyncSwap, mul_comm (p₂ x.1)]
  have e2 : ∑ x : α₂ × α₁, prodDist p₂ p₁ x * entropy (asyncSwap W x) =
      ∑ x : α₁ × α₂, prodDist p₁ p₂ x * entropy (W x) := by
    rw [← e fun x => prodDist p₁ p₂ x * entropy (W x)]
    refine sum_congr rfl fun x _ => ?_
    simp [prodDist, asyncSwap, mul_comm (p₂ x.1)]
  simp only [e1, e2]

/-- **The code defined by the two tables of letters.** -/
def asyncTableCode [NeZero V₁] [NeZero V₂] [NeZero M₁] [NeZero M₂] (p₁ : α₁ → ℝ) (p₂ : α₂ → ℝ)
    (W : α₁ × α₂ → β → ℝ) (k b : ℕ) (D : ℝ) (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁)
    (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂) (τ₁ : Fin n × Fin V₁ → α₁) (τ₂ : Fin n × Fin V₂ → α₂) :
    AsyncCode M₁ M₂ n α₁ α₂ β where
  enc₁ m p := τ₁ (asyncLetter k b (sub₁ m) p)
  enc₂ m p := τ₂ (asyncLetter k b (sub₂ m) p)
  dec y := (asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y,
    asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y)

omit [Fintype α₁] [Fintype α₂] in
lemma AsyncCode.asyncErr_nonneg (c : AsyncCode M₁ M₂ n α₁ α₂ β) (hW : IsChannel W)
    (d₁ d₂ : Fin n) : 0 ≤ c.asyncErr W d₁ d₂ := by
  refine div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun y _ => ?_)
    (by positivity)
  split_ifs
  · exact channelExt_nonneg hW _ _
  · exact le_rfl

section Code

variable [NeZero V₁] [NeZero V₂] [NeZero M₁] [NeZero M₂]

/-- **The tables average.** If the error of each decoder, averaged over the tables, is small for all
the true messages, the same holds for the code. -/
theorem sum_tables_asyncErr_le (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) {D : ℝ}
    (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂) (d₁ d₂ : Fin n)
    {ε₁ ε₂ : ℝ}
    (h₁ : ∀ m₁ m₂, asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂)
      (fun τ₁ τ₂ y => if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) ≤ ε₁)
    (h₂ : ∀ m₁ m₂, asyncE p₂ p₁ (asyncSwap W) (asyncTrue k b sub₂ m₂ d₂) (asyncTrue k b sub₁ m₁ d₁)
      (fun τ₂ τ₁ y => if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠
        m₂ 1 then (1 : ℝ) else 0)
        ≤ ε₂) :
    ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ *
      (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂ ≤ ε₁ + ε₂ := by
  classical
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M₁
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M₂
  set C := (M₁ : ℝ) ^ 3 * (M₂ : ℝ) ^ 3 with hC
  have hC0 : 0 < C := by positivity
  -- The bound for fixed tables.
  have hpt : ∀ τ₁ τ₂, (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂ ≤
      (∑ m₁ : Fin 3 → Fin M₁, ∑ m₂ : Fin 3 → Fin M₂, ∑ y : Fin (2 * n - 1) → β,
        (∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) *
        ((if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) +
          if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then (1 : ℝ) else 0)) / C := by
    intro τ₁ τ₂
    refine div_le_div_of_nonneg_right (sum_le_sum fun m₁ _ => sum_le_sum fun m₂ _ =>
      sum_le_sum fun y _ => ?_) hC0.le
    have hlaw : (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).windowLaw W d₁ d₂ m₁ m₂ y =
        ∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t) := rfl
    rw [hlaw]
    have hW0 : 0 ≤ ∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t))
        (y t) := prod_nonneg fun t _ => (hW _).nonneg _
    by_cases hne : (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).dec y ≠ (m₁ 1, m₂ 1)
    · rw [ite_eq_left hne]
      have h3 : asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 ∨
          asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 := by
        by_contra hcon
        push Not at hcon
        exact hne (Prod.ext hcon.1 hcon.2)
      have h4 : (1 : ℝ) ≤ (if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) +
          if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then (1 : ℝ) else 0 := by
        rcases h3 with h | h
        · simp only [ne_eq, h, not_false_eq_true, ite_true]
          split_ifs <;> norm_num
        · simp only [ne_eq, h, not_false_eq_true, ite_true]
          split_ifs <;> norm_num
      nlinarith
    · rw [ite_eq_right hne]
      refine mul_nonneg hW0 (add_nonneg ?_ ?_) <;> split_ifs <;> norm_num
  -- The average over the tables, for fixed messages.
  have hmsg : ∀ m₁ m₂, ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ *
      ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ * ∑ y : Fin (2 * n - 1) → β,
      (∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) *
      ((if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) +
        if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then (1 : ℝ) else 0) ≤
      ε₁ + ε₂ := by
    intro m₁ m₂
    have e := asyncE_add (p₁ := p₁) (p₂ := p₂) (W := W) (asyncTrue k b sub₁ m₁ d₁)
      (asyncTrue k b sub₂ m₂ d₂)
      (fun τ₁ τ₂ y => if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0)
      (fun τ₁ τ₂ y => if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then
        (1 : ℝ) else 0)
    have e2 : asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂)
        (fun τ₁ τ₂ y => if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then
          (1 : ℝ) else 0) =
        asyncE p₂ p₁ (asyncSwap W) (asyncTrue k b sub₂ m₂ d₂) (asyncTrue k b sub₁ m₁ d₁)
        (fun τ₂ τ₁ y => if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then
          (1 : ℝ) else 0) := by
      unfold asyncE
      simp only [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun τ₂ _ => sum_congr rfl fun τ₁ _ => sum_congr rfl fun y _ => ?_
      simp only [asyncSwap]
      ring
    have e3 := h₁ m₁ m₂
    have e4 := h₂ m₁ m₂
    rw [← e2] at e4
    have e5 : ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ *
        ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ * ∑ y : Fin (2 * n - 1) → β,
        (∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) *
        ((if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) +
          if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then (1 : ℝ) else 0) =
        asyncE p₁ p₂ W (asyncTrue k b sub₁ m₁ d₁) (asyncTrue k b sub₂ m₂ d₂) (fun τ₁ τ₂ y =>
        (if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) +
          if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then (1 : ℝ) else 0) := rfl
    rw [e5, e]
    exact add_le_add e3 e4
  have hcard : ∑ _m₁ : Fin 3 → Fin M₁, ∑ _m₂ : Fin 3 → Fin M₂, (1 : ℝ) = C := by
    simp [hC]
  calc _ ≤ ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ * ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ *
        ((∑ m₁ : Fin 3 → Fin M₁, ∑ m₂ : Fin 3 → Fin M₂, ∑ y : Fin (2 * n - 1) → β,
        (∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) *
        ((if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) +
          if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then (1 : ℝ) else 0)) / C) :=
        sum_le_sum fun τ₁ _ => mul_le_mul_of_nonneg_left
          (sum_le_sum fun τ₂ _ => mul_le_mul_of_nonneg_left (hpt τ₁ τ₂) (tableLaw_nonneg hp₂ τ₂))
          (tableLaw_nonneg hp₁ τ₁)
    _ = (∑ m₁ : Fin 3 → Fin M₁, ∑ m₂ : Fin 3 → Fin M₂,
        ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ *
        ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ * ∑ y : Fin (2 * n - 1) → β,
        (∏ t, W (τ₁ (asyncTrue k b sub₁ m₁ d₁ t), τ₂ (asyncTrue k b sub₂ m₂ d₂ t)) (y t)) *
        ((if asyncDecA p₁ p₂ W k b D sub₁ τ₁ τ₂ y ≠ m₁ 1 then (1 : ℝ) else 0) +
          if asyncDecA p₂ p₁ (asyncSwap W) k b D sub₂ τ₂ τ₁ y ≠ m₂ 1 then (1 : ℝ) else 0)) / C := by
        simp only [mul_sum, sum_div, mul_div_assoc']
        have : ∀ (F : (Fin n × Fin V₁ → α₁) → (Fin n × Fin V₂ → α₂) → (Fin 3 → Fin M₁) →
            (Fin 3 → Fin M₂) → ℝ), ∑ τ₁, ∑ τ₂, ∑ m₁, ∑ m₂, F τ₁ τ₂ m₁ m₂ =
            ∑ m₁, ∑ m₂, ∑ τ₁, ∑ τ₂, F τ₁ τ₂ m₁ m₂ := fun F => by
          calc ∑ τ₁, ∑ τ₂, ∑ m₁, ∑ m₂, F τ₁ τ₂ m₁ m₂
              = ∑ τ₁, ∑ m₁, ∑ τ₂, ∑ m₂, F τ₁ τ₂ m₁ m₂ := sum_congr rfl fun _ _ => sum_comm
            _ = ∑ m₁, ∑ τ₁, ∑ τ₂, ∑ m₂, F τ₁ τ₂ m₁ m₂ := sum_comm
            _ = ∑ m₁, ∑ τ₁, ∑ m₂, ∑ τ₂, F τ₁ τ₂ m₁ m₂ :=
                sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
            _ = ∑ m₁, ∑ m₂, ∑ τ₁, ∑ τ₂, F τ₁ τ₂ m₁ m₂ := sum_congr rfl fun _ _ => sum_comm
        exact this _
    _ ≤ (∑ _m₁ : Fin 3 → Fin M₁, ∑ _m₂ : Fin 3 → Fin M₂, (ε₁ + ε₂)) / C :=
        div_le_div_of_nonneg_right (sum_le_sum fun m₁ _ => sum_le_sum fun m₂ _ => hmsg m₁ m₂)
          hC0.le
    _ = ε₁ + ε₂ := by
        have : ∑ _m₁ : Fin 3 → Fin M₁, ∑ _m₂ : Fin 3 → Fin M₂, (ε₁ + ε₂) = C * (ε₁ + ε₂) := by
          rw [← hcard, sum_mul]
          refine sum_congr rfl fun _ _ => ?_
          rw [sum_mul]
          simp
        rw [this]
        field_simp

/-- **One code is good for all the delays**, as the sum of the errors over the delays is small on
average over the tables. -/
theorem exists_asyncTableCode (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂) (hW : IsChannel W) {D : ℝ}
    (sub₁ : Fin M₁ → Fin (b + 3) → Fin V₁) (sub₂ : Fin M₂ → Fin (b + 3) → Fin V₂) {ε : ℝ}
    (h : ∀ d₁ d₂ : Fin n, ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ *
      ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ *
      (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂ ≤ ε) :
    ∃ c : AsyncCode M₁ M₂ n α₁ α₂ β, ∀ d₁ d₂ : Fin n, c.asyncErr W d₁ d₂ ≤ n ^ 2 * ε := by
  classical
  have hsum : ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ *
      ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ * (∑ d₁ : Fin n, ∑ d₂ : Fin n,
      (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂) ≤ n ^ 2 * ε := by
    calc _ = ∑ d₁ : Fin n, ∑ d₂ : Fin n, ∑ τ₁ : Fin n × Fin V₁ → α₁, tableLaw p₁ τ₁ *
          ∑ τ₂ : Fin n × Fin V₂ → α₂, tableLaw p₂ τ₂ *
          (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂ := by
          simp only [mul_sum]
          have : ∀ (F : (Fin n × Fin V₁ → α₁) → (Fin n × Fin V₂ → α₂) → Fin n → Fin n → ℝ),
              ∑ τ₁, ∑ τ₂, ∑ d₁, ∑ d₂, F τ₁ τ₂ d₁ d₂ = ∑ d₁, ∑ d₂, ∑ τ₁, ∑ τ₂, F τ₁ τ₂ d₁ d₂ :=
            fun F => by
            calc ∑ τ₁, ∑ τ₂, ∑ d₁, ∑ d₂, F τ₁ τ₂ d₁ d₂
                = ∑ τ₁, ∑ d₁, ∑ τ₂, ∑ d₂, F τ₁ τ₂ d₁ d₂ := sum_congr rfl fun _ _ => sum_comm
              _ = ∑ d₁, ∑ τ₁, ∑ τ₂, ∑ d₂, F τ₁ τ₂ d₁ d₂ := sum_comm
              _ = ∑ d₁, ∑ τ₁, ∑ d₂, ∑ τ₂, F τ₁ τ₂ d₁ d₂ :=
                  sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
              _ = ∑ d₁, ∑ d₂, ∑ τ₁, ∑ τ₂, F τ₁ τ₂ d₁ d₂ := sum_congr rfl fun _ _ => sum_comm
          exact this _
      _ ≤ ∑ _d₁ : Fin n, ∑ _d₂ : Fin n, ε := sum_le_sum fun d₁ _ => sum_le_sum fun d₂ _ => h d₁ d₂
      _ = n ^ 2 * ε := by
          simp
          ring
  obtain ⟨τ₁, h1⟩ := exists_le_of_sum_tableLaw_le hp₁ hsum
  obtain ⟨τ₂, h2⟩ := exists_le_of_sum_tableLaw_le hp₂ h1
  refine ⟨asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂, fun d₁ d₂ => ?_⟩
  refine le_trans ?_ h2
  have hnn : ∀ d₁ d₂ : Fin n, 0 ≤ (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂ :=
    fun d₁ d₂ => AsyncCode.asyncErr_nonneg _ hW d₁ d₂
  calc _ ≤ ∑ d₂ : Fin n, (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂ :=
        single_le_sum (f := fun d₂ : Fin n =>
          (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂)
          (fun d₂ _ => hnn d₁ d₂) (mem_univ d₂)
    _ ≤ _ := single_le_sum (f := fun d₁ : Fin n => ∑ d₂ : Fin n,
          (asyncTableCode p₁ p₂ W k b D sub₁ sub₂ τ₁ τ₂).asyncErr W d₁ d₂)
          (fun d₁ _ => sum_nonneg fun d₂ _ => hnn d₁ d₂) (mem_univ d₁)

end Code

/-- A map from messages to sub-messages exists if there are enough sub-messages. -/
lemma exists_isAsyncSub {M V : ℕ} [NeZero V] (hM : M ≤ V ^ b) :
    ∃ sub : Fin M → Fin (b + 3) → Fin V, IsAsyncSub sub := by
  classical
  have hcard : Fintype.card (Fin M) ≤ Fintype.card (Fin b → Fin V) := by simpa using hM
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hlt : ∀ j : Fin (b + 3), 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ b → (j : ℕ) - 1 < b := fun j h => by omega
  refine ⟨fun m j => if h : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ b then e m ⟨(j : ℕ) - 1, hlt j h⟩ else 0,
    ⟨fun m j hj => ?_, fun m m' h => ?_⟩⟩
  · have : ¬ (1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ b) := fun h' => hj (by simp [asyncMsg, h'])
    simp [this]
  · refine e.injective (funext fun i => ?_)
    have hi := i.isLt
    set j : Fin (b + 3) := ⟨(i : ℕ) + 1, by omega⟩ with hj
    have hjm : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ b := ⟨by simp [hj], by simp only [hj]; omega⟩
    have h1 := h j (by simp [asyncMsg, hjm])
    simp only [hjm, and_self, dite_true] at h1
    have h2 : (⟨(j : ℕ) - 1, hlt j hjm⟩ : Fin b) = i := Fin.ext (by simp [hj])
    rwa [h2] at h1

/-! ### One code for all the delays -/

/-- The bound for the error of one decoder. -/
def asyncEps (S n k : ℕ) (D γ l₁ l₂ l₃ : ℝ) : ℝ :=
  4 ^ S * (exp (-(l₁ * D / 2)) + exp (-(l₂ * D / 2)) + exp (-(l₃ * D / 2))) +
    n ^ 2 * (4 ^ S * (64 ^ S * exp (-(γ * k - 3 * D)) + 16 ^ S * exp (-((γ * k - D) / 2))))

/-- **A code good for all the delays**, for given sizes of the message and sub-message sets. -/
theorem exists_asyncCode [NeZero V₁] [NeZero V₂] [NeZero M₁] [NeZero M₂] (hp₁ : IsPMF p₁)
    (hp₂ : IsPMF p₂) (hW : IsChannel W) (hk : 0 < k) (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k)
    {D : ℝ} (hM₁ : M₁ ≤ V₁ ^ b) (hM₂ : M₂ ≤ V₂ ^ b) {r₁ r₂ γ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hγ : 0 < γ) (hV₁ : (V₁ : ℝ) ≤ 2 * exp (k * r₁)) (hV₂ : (V₂ : ℝ) ≤ 2 * exp (k * r₂))
    (hA : 2 ≤ V₁ → r₁ + γ ≤ macInfo₁ p₁ p₂ W) (hB : 2 ≤ V₂ → r₂ + γ ≤ macInfo₂ p₁ p₂ W)
    (hAB : 2 ≤ V₁ → 2 ≤ V₂ → r₁ + r₂ + γ ≤ macInfo₁₂ p₁ p₂ W) {l₁ l₂ l₃ l₄ l₅ l₆ c : ℝ}
    (hC : AsyncChernoff p₁ p₂ W l₁ l₂ l₃ c) (hC' : AsyncChernoff p₂ p₁ (asyncSwap W) l₄ l₅ l₆ c)
    (hc : 0 ≤ c) (hcD : n * c ≤ D / 2) :
    ∃ c' : AsyncCode M₁ M₂ n α₁ α₂ β, ∀ d₁ d₂ : Fin n, c'.asyncErr W d₁ d₂ ≤
      n ^ 2 * (asyncEps (b + 3) n k D γ l₁ l₂ l₃ + asyncEps (b + 3) n k D γ l₄ l₅ l₆) := by
  obtain ⟨sub₁, hsub₁⟩ := exists_isAsyncSub hM₁
  obtain ⟨sub₂, hsub₂⟩ := exists_isAsyncSub hM₂
  have hW' := asyncSwap_isChannel hW
  refine exists_asyncTableCode hp₁ hp₂ hW (D := D) (k := k) sub₁ sub₂ fun d₁ d₂ => ?_
  refine sum_tables_asyncErr_le hp₁ hp₂ hW sub₁ sub₂ d₁ d₂ (fun m₁ m₂ => ?_) (fun m₁ m₂ => ?_)
  · exact asyncE_decA_le hp₁ hp₂ hW hk hl hu hsub₁ hsub₂ m₁ m₂ d₁ d₂ hr₁ hr₂ hγ hV₁ hV₂ hA hB hAB
      hC hc hcD
  · refine asyncE_decA_le hp₂ hp₁ hW' hk hl hu hsub₂ hsub₁ m₂ m₁ d₂ d₁ hr₂ hr₁ hγ hV₂ hV₁
      (fun h => ?_) (fun h => ?_) (fun h h' => ?_) hC' hc hcD
    · rw [macInfo₁_asyncSwap hp₁ hp₂ hW]
      exact hB h
    · rw [macInfo₂_asyncSwap hp₁ hp₂ hW]
      exact hA h
    · rw [macInfo₁₂_asyncSwap hp₁ hp₂ hW]
      have := hAB h' h
      linarith

/-- The bound for one decoder, in terms of the smallest exponent. -/
lemma asyncEps_le {S n k : ℕ} {δ γ l₁ l₂ l₃ ν : ℝ} (hk0 : (0 : ℝ) ≤ k) (hn : 1 ≤ n)
    (hδ : δ = γ / 6) (hγ : 0 < γ) (h₁ : ν ≤ l₁ * δ / 2) (h₂ : ν ≤ l₂ * δ / 2) (h₃ : ν ≤ l₃ * δ / 2)
    (h₄ : ν ≤ 5 * γ / 12) :
    asyncEps S n k (δ * k) γ l₁ l₂ l₃ ≤
      n ^ 2 * (4 ^ S * (3 + 64 ^ S + 16 ^ S)) * exp (-(ν * k)) := by
  set e := exp (-(ν * k)) with he
  have he0 : 0 < e := exp_pos _
  have hexp : ∀ x : ℝ, ν ≤ x → exp (-(x * k)) ≤ e := fun x hx =>
    exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hx hk0))
  have e1 : exp (-(l₁ * (δ * k) / 2)) ≤ e := by
    have := hexp _ h₁
    rwa [show l₁ * δ / 2 * k = l₁ * (δ * k) / 2 by ring] at this
  have e2 : exp (-(l₂ * (δ * k) / 2)) ≤ e := by
    have := hexp _ h₂
    rwa [show l₂ * δ / 2 * k = l₂ * (δ * k) / 2 by ring] at this
  have e3 : exp (-(l₃ * (δ * k) / 2)) ≤ e := by
    have := hexp _ h₃
    rwa [show l₃ * δ / 2 * k = l₃ * (δ * k) / 2 by ring] at this
  have e4 : exp (-(γ * k - 3 * (δ * k))) ≤ e := by
    have := hexp (γ / 2) (by linarith)
    rwa [show γ / 2 * k = γ * k - 3 * (δ * k) by rw [hδ]; ring] at this
  have e5 : exp (-((γ * k - δ * k) / 2)) ≤ e := by
    have := hexp (5 * γ / 12) h₄
    rwa [show 5 * γ / 12 * k = (γ * k - δ * k) / 2 by rw [hδ]; ring] at this
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  have h4 : (0 : ℝ) < 4 ^ S := by positivity
  unfold asyncEps
  have h6 : (4 : ℝ) ^ S * (exp (-(l₁ * (δ * k) / 2)) + exp (-(l₂ * (δ * k) / 2)) +
      exp (-(l₃ * (δ * k) / 2))) ≤ 4 ^ S * (3 * e) :=
    mul_le_mul_of_nonneg_left (by linarith) h4.le
  have h7 : (n : ℝ) ^ 2 * (4 ^ S * (64 ^ S * exp (-(γ * k - 3 * (δ * k))) +
      16 ^ S * exp (-((γ * k - δ * k) / 2)))) ≤ n ^ 2 * (4 ^ S * (64 ^ S * e + 16 ^ S * e)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ h4.le) (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left e4 (by positivity))
      (mul_le_mul_of_nonneg_left e5 (by positivity))
  have h8 : (4 : ℝ) ^ S * (3 * e) ≤ n ^ 2 * (4 ^ S * (3 * e)) := by
    have : 0 ≤ (4 : ℝ) ^ S * (3 * e) := by positivity
    nlinarith
  calc _ ≤ (n : ℝ) ^ 2 * (4 ^ S * (3 * e)) + n ^ 2 * (4 ^ S * (64 ^ S * e + 16 ^ S * e)) := by
        linarith
    _ = _ := by ring

/-! ### The rates -/

/-- The rate per letter of the sub-messages, for a target rate `R`. -/
def asyncRho (b : ℕ) (R : ℝ) : ℝ := max R 0 * (1 + 4 / b)

lemma asyncRho_nonneg (b : ℕ) (R : ℝ) : 0 ≤ asyncRho b R :=
  mul_nonneg (le_max_right _ _) (by positivity)

lemma pos_of_asyncRho_pos {b : ℕ} {R : ℝ} (h : 0 < asyncRho b R) : 0 < R := by
  by_contra hR
  push Not at hR
  have : asyncRho b R = 0 := by simp [asyncRho, max_eq_right hR]
  linarith

/-- If there are at least two sub-messages, the rate is positive. -/
lemma pos_of_two_le {b k : ℕ} {R : ℝ} (h : 2 ≤ 2 ^ ⌈(k : ℝ) * asyncRho b R⌉₊) : 0 < R := by
  refine pos_of_asyncRho_pos (b := b) ?_
  by_contra hR
  have h0 : asyncRho b R = 0 := le_antisymm (not_lt.1 hR) (asyncRho_nonneg b R)
  simp [h0] at h

/-- `2^⌈k ρ⌉ ≤ 2 e^{k ρ log 2}`. -/
lemma two_pow_ceil_le_two_mul_exp {k : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((2 ^ ⌈(k : ℝ) * ρ⌉₊ : ℕ) : ℝ) ≤ 2 * exp (k * (ρ * log 2)) := by
  have hl := log_pos one_lt_two
  have h1 : (⌈(k : ℝ) * ρ⌉₊ : ℝ) < k * ρ + 1 := Nat.ceil_lt_add_one (by positivity)
  push_cast
  calc (2 : ℝ) ^ ⌈(k : ℝ) * ρ⌉₊ = exp (⌈(k : ℝ) * ρ⌉₊ * log 2) := by
        rw [← rpow_natCast, rpow_def_of_pos two_pos, mul_comm]
    _ ≤ exp ((k * ρ + 1) * log 2) := exp_le_exp.2 (mul_le_mul_of_nonneg_right h1.le hl.le)
    _ = 2 * exp (k * (ρ * log 2)) := by
        rw [add_mul, one_mul, exp_add, exp_log two_pos, mul_comm]
        ring_nf

/-- **There are enough sub-messages for the messages.** -/
lemma two_pow_ceil_le_pow {b k n : ℕ} {R : ℝ} (hb : 1 ≤ b) (hu : n < (b + 3) * k)
    (hkR : 0 < R → 1 ≤ (k : ℝ) * R) :
    2 ^ ⌈(n : ℝ) * R⌉₊ ≤ (2 ^ ⌈(k : ℝ) * asyncRho b R⌉₊) ^ b := by
  rw [← pow_mul]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rcases le_or_gt R 0 with hR | hR
  · have : ⌈(n : ℝ) * R⌉₊ = 0 :=
      Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) hR)
    omega
  · have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hn : (n : ℝ) ≤ (b + 3) * k := by exact_mod_cast hu.le
    have h1 : (⌈(n : ℝ) * R⌉₊ : ℝ) < n * R + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (k : ℝ) * asyncRho b R ≤ ⌈(k : ℝ) * asyncRho b R⌉₊ := Nat.le_ceil _
    have h3 : (b : ℝ) * ((k : ℝ) * asyncRho b R) = k * R * (b + 4) := by
      rw [asyncRho, max_eq_left hR.le]
      field_simp
    have h4 : (n : ℝ) * R + 1 ≤ k * R * (b + 4) := by
      have h5 := hkR hR
      nlinarith
    have h6 : (⌈(n : ℝ) * R⌉₊ : ℝ) ≤ ⌈(k : ℝ) * asyncRho b R⌉₊ * b := by
      have h7 : (b : ℝ) * ((k : ℝ) * asyncRho b R) ≤ b * ⌈(k : ℝ) * asyncRho b R⌉₊ :=
        mul_le_mul_of_nonneg_left h2 hb'.le
      linarith
    exact_mod_cast h6

/-- **The parameters.** A large number of segments makes the overhead of the pilots small. -/
lemma exists_async_params {R₁ R₂ I₁ I₂ I₁₂ : ℝ} (h₁ : R₁ * log 2 < I₁) (h₂ : R₂ * log 2 < I₂)
    (h₁₂ : (R₁ + R₂) * log 2 < I₁₂) :
    ∃ (b : ℕ) (γ : ℝ), 1 ≤ b ∧ 0 < γ ∧ (0 < R₁ → asyncRho b R₁ * log 2 + γ ≤ I₁) ∧
      (0 < R₂ → asyncRho b R₂ * log 2 + γ ≤ I₂) ∧
      (0 < R₁ → 0 < R₂ → asyncRho b R₁ * log 2 + asyncRho b R₂ * log 2 + γ ≤ I₁₂) := by
  have hl := log_pos one_lt_two
  set g := min (I₁ - R₁ * log 2) (min (I₂ - R₂ * log 2) (I₁₂ - (R₁ + R₂) * log 2)) with hg
  have hg0 : 0 < g := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hg1 : g ≤ I₁ - R₁ * log 2 := min_le_left _ _
  have hg2 : g ≤ I₂ - R₂ * log 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hg3 : g ≤ I₁₂ - (R₁ + R₂) * log 2 := (min_le_right _ _).trans (min_le_right _ _)
  set T := (|R₁| + |R₂|) * log 2 with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨b₀, hb₀⟩ := exists_nat_gt (8 * T / g)
  set b := b₀ + 1 with hb
  have hb' : (0 : ℝ) < b := by positivity
  have hbT : 8 * T ≤ g * b := by
    have h3 := (div_lt_iff₀ hg0).1 hb₀
    have h4 : (b₀ : ℝ) ≤ b := by simp [hb]
    nlinarith
  have hover : ∀ R : ℝ, 0 < R → |R| * log 2 ≤ T → asyncRho b R * log 2 ≤ R * log 2 + 4 * T / b := by
    intro R hR hRT
    have h5 : asyncRho b R * log 2 = R * log 2 + 4 * (R * log 2) / b := by
      rw [asyncRho, max_eq_left hR.le]
      field_simp
    rw [h5]
    have h6 : R * log 2 ≤ T := by rwa [abs_of_pos hR] at hRT
    have h7 : 4 * (R * log 2) / b ≤ 4 * T / b :=
      div_le_div_of_nonneg_right (by linarith) hb'.le
    linarith
  have h4T : 4 * T / b ≤ g / 2 := by
    rw [div_le_iff₀ hb']
    linarith
  have hR₁T : |R₁| * log 2 ≤ T := by
    rw [hT]
    nlinarith [abs_nonneg R₂]
  have hR₂T : |R₂| * log 2 ≤ T := by
    rw [hT]
    nlinarith [abs_nonneg R₁]
  refine ⟨b, g / 2, by omega, by positivity, fun h => ?_, fun h => ?_, fun h h' => ?_⟩
  · have := hover R₁ h hR₁T
    linarith
  · have := hover R₂ h hR₂T
    linarith
  · -- The overhead of the two senders together.
    have h5 : asyncRho b R₁ * log 2 = R₁ * log 2 + 4 * (R₁ * log 2) / b := by
      rw [asyncRho, max_eq_left h.le]
      field_simp
    have h6 : asyncRho b R₂ * log 2 = R₂ * log 2 + 4 * (R₂ * log 2) / b := by
      rw [asyncRho, max_eq_left h'.le]
      field_simp
    have h7 : 4 * (R₁ * log 2) / b + 4 * (R₂ * log 2) / b = 4 * ((R₁ + R₂) * log 2) / b := by
      ring
    have h8 : (R₁ + R₂) * log 2 ≤ T := by
      rw [hT, abs_of_pos h, abs_of_pos h']
    have h9 : 4 * ((R₁ + R₂) * log 2) / b ≤ 4 * T / b :=
      div_le_div_of_nonneg_right (by linarith) hb'.le
    linarith

/-- **Theorem 2 of Lecture 24, achievability.** For a product input distribution, the rate pairs
strictly inside the pentagon are achievable. -/
theorem isAchievableAsync_of_lt [Nonempty α₁] [Nonempty α₂] (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (hW : IsChannel W) {R₁ R₂ : ℝ} (h₁ : R₁ * log 2 < macInfo₁ p₁ p₂ W)
    (h₂ : R₂ * log 2 < macInfo₂ p₁ p₂ W) (h₁₂ : (R₁ + R₂) * log 2 < macInfo₁₂ p₁ p₂ W) :
    IsAchievableAsync W R₁ R₂ := by
  have hl := log_pos one_lt_two
  obtain ⟨b, γ, hb, hγ, hA, hB, hAB⟩ := exists_async_params h₁ h₂ h₁₂
  set δ := γ / 6 with hδ
  have hδ0 : 0 < δ := by positivity
  have hb3 : (0 : ℝ) < (b : ℝ) + 3 := by positivity
  set c := δ / (2 * ((b : ℝ) + 3)) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨l₁, l₂, l₃, hC⟩ := exists_asyncChernoff hp₁ hp₂ hW hc0
  obtain ⟨l₄, l₅, l₆, hC'⟩ := exists_asyncChernoff hp₂ hp₁ (asyncSwap_isChannel hW) hc0
  -- The smallest exponent.
  set ν := min (l₁ * δ / 2) (min (l₂ * δ / 2) (min (l₃ * δ / 2) (min (l₄ * δ / 2)
    (min (l₅ * δ / 2) (min (l₆ * δ / 2) (5 * γ / 12)))))) with hν
  have hν0 : 0 < ν := by
    have := hC.pos₁
    have := hC.pos₂
    have := hC.pos₃
    have := hC'.pos₁
    have := hC'.pos₂
    have := hC'.pos₃
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  have hν₁ : ν ≤ l₁ * δ / 2 := min_le_left _ _
  have hν₂ : ν ≤ l₂ * δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hν₃ : ν ≤ l₃ * δ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄ : ν ≤ l₄ * δ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hν₅ : ν ≤ l₅ * δ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hν₆ : ν ≤ l₆ * δ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))))
  have hν₇ : ν ≤ 5 * γ / 12 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))))
  set K₀ : ℝ := 4 ^ (b + 3) * (3 + 64 ^ (b + 3) + 16 ^ (b + 3)) with hK₀
  have hK₀0 : 0 < K₀ := by positivity
  -- The sizes, for large `n`.
  have hsize : ∀ n : ℕ, (b + 2) ≤ n / (b + 2) → (∀ R : ℝ, R = R₁ ∨ R = R₂ → 0 < R →
      1 ≤ ((n / (b + 2) : ℕ) : ℝ) * R) →
      ∃ c' : AsyncCode (2 ^ ⌈(n : ℝ) * R₁⌉₊) (2 ^ ⌈(n : ℝ) * R₂⌉₊) n α₁ α₂ β,
        ∀ d₁ d₂ : Fin n, c'.asyncErr W d₁ d₂ ≤
          (n : ℝ) ^ 4 * (2 * K₀) * exp (-(ν * ((n / (b + 2) : ℕ) : ℝ))) := by
    intro n hn hR
    set k := n / (b + 2) with hk
    have hk0 : 0 < k := by omega
    have hl' : (b + 2) * k ≤ n := by
      rw [hk]
      exact Nat.mul_div_le _ _
    have hu' : n < (b + 3) * k := by
      have h3 := Nat.lt_mul_div_succ n (show 0 < b + 2 by omega)
      rw [← hk] at h3
      nlinarith
    have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
    have hn1 : 1 ≤ n := by
      have : 0 < (b + 2) * k := by positivity
      omega
    have hu'' : (n : ℝ) ≤ ((b : ℝ) + 3) * k := by exact_mod_cast hu'.le
    set V₁ := 2 ^ ⌈(k : ℝ) * asyncRho b R₁⌉₊ with hV₁
    set V₂ := 2 ^ ⌈(k : ℝ) * asyncRho b R₂⌉₊ with hV₂
    have : NeZero V₁ := ⟨by positivity⟩
    have : NeZero V₂ := ⟨by positivity⟩
    have : NeZero (2 ^ ⌈(n : ℝ) * R₁⌉₊) := ⟨by positivity⟩
    have : NeZero (2 ^ ⌈(n : ℝ) * R₂⌉₊) := ⟨by positivity⟩
    have hcD : (n : ℝ) * c ≤ δ * k / 2 := by
      have h3 : (n : ℝ) * c ≤ ((b : ℝ) + 3) * k * c := mul_le_mul_of_nonneg_right hu'' hc0.le
      have h4 : ((b : ℝ) + 3) * k * c = δ * k / 2 := by
        rw [hc]
        field_simp
      linarith
    obtain ⟨c', hc'⟩ := exists_asyncCode (n := n) (k := k) (b := b) (V₁ := V₁) (V₂ := V₂)
      (M₁ := 2 ^ ⌈(n : ℝ) * R₁⌉₊) (M₂ := 2 ^ ⌈(n : ℝ) * R₂⌉₊) (D := δ * k)
      (r₁ := asyncRho b R₁ * log 2) (r₂ := asyncRho b R₂ * log 2) (γ := γ) hp₁ hp₂ hW hk0 hl' hu'
      (two_pow_ceil_le_pow hb hu' (hR R₁ (Or.inl rfl)))
      (two_pow_ceil_le_pow hb hu' (hR R₂ (Or.inr rfl)))
      (mul_nonneg (asyncRho_nonneg _ _) hl.le) (mul_nonneg (asyncRho_nonneg _ _) hl.le) hγ
      (two_pow_ceil_le_two_mul_exp (asyncRho_nonneg _ _))
      (two_pow_ceil_le_two_mul_exp (asyncRho_nonneg _ _))
      (fun h => hA (pos_of_two_le h)) (fun h => hB (pos_of_two_le h))
      (fun h h' => hAB (pos_of_two_le h) (pos_of_two_le h')) hC hC' hc0.le hcD
    refine ⟨c', fun d₁ d₂ => (hc' d₁ d₂).trans ?_⟩
    have e1 := asyncEps_le (S := b + 3) (n := n) (k := k) (ν := ν) hk0'.le hn1 hδ hγ hν₁ hν₂ hν₃ hν₇
    have e2 := asyncEps_le (S := b + 3) (n := n) (k := k) (ν := ν) hk0'.le hn1 hδ hγ hν₄ hν₅ hν₆ hν₇
    have e3 : (n : ℝ) ^ 2 * (asyncEps (b + 3) n k (δ * k) γ l₁ l₂ l₃ +
        asyncEps (b + 3) n k (δ * k) γ l₄ l₅ l₆) ≤ n ^ 2 * (2 * (n ^ 2 * K₀ *
          exp (-(ν * k)))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine e3.trans (le_of_eq ?_)
    ring
  -- The choice of the codes.
  have hex : ∀ n : ℕ, ∃ c' : AsyncCode (2 ^ ⌈(n : ℝ) * R₁⌉₊) (2 ^ ⌈(n : ℝ) * R₂⌉₊) n α₁ α₂ β,
      (b + 2) ≤ n / (b + 2) → (∀ R : ℝ, R = R₁ ∨ R = R₂ → 0 < R →
        1 ≤ ((n / (b + 2) : ℕ) : ℝ) * R) → ∀ d₁ d₂ : Fin n, c'.asyncErr W d₁ d₂ ≤
          (n : ℝ) ^ 4 * (2 * K₀) * exp (-(ν * ((n / (b + 2) : ℕ) : ℝ))) := by
    intro n
    by_cases hn : (b + 2) ≤ n / (b + 2) ∧ (∀ R : ℝ, R = R₁ ∨ R = R₂ → 0 < R →
        1 ≤ ((n / (b + 2) : ℕ) : ℝ) * R)
    · obtain ⟨c', hc'⟩ := hsize n hn.1 hn.2
      exact ⟨c', fun _ _ => hc'⟩
    · exact ⟨⟨fun _ _ => Classical.arbitrary _, fun _ _ => Classical.arbitrary _,
        fun _ => (⟨0, by positivity⟩, ⟨0, by positivity⟩)⟩, fun h h' => absurd ⟨h, h'⟩ hn⟩
  choose c' hc' using hex
  refine ⟨c', fun ε hε => ?_⟩
  -- The bound tends to zero.
  have hkn : Tendsto (fun n : ℕ => n / (b + 2)) atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    filter_upwards [eventually_ge_atTop (N * (b + 2))] with n hn
    exact (Nat.le_div_iff_mul_le (by omega)).2 hn
  have hr : |exp (-ν)| < 1 := by
    rw [abs_of_pos (exp_pos _)]
    rw [← exp_zero]
    exact exp_lt_exp.2 (by linarith)
  have hlim := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 hr
  set K : ℝ := ((b : ℝ) + 3) ^ 4 * (2 * K₀) with hK
  have hK0 : 0 < K := by positivity
  have hsmall := (hlim.comp hkn).eventually (gt_mem_nhds (div_pos hε hK0))
  have hk_large := hkn.eventually (eventually_ge_atTop (b + 2))
  have hR_large : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, 0 < R → 1 ≤ ((n / (b + 2) : ℕ) : ℝ) * R := by
    intro R
    by_cases hR : 0 < R
    · obtain ⟨N, hN⟩ := exists_nat_gt (1 / R)
      filter_upwards [hkn.eventually (eventually_ge_atTop N)] with n hn _
      have h3 : (N : ℝ) ≤ ((n / (b + 2) : ℕ) : ℝ) := by exact_mod_cast hn
      have h4 := (div_lt_iff₀ hR).1 hN
      nlinarith
    · exact Eventually.of_forall fun _ h => absurd h hR
  filter_upwards [hsmall, hk_large, hR_large R₁, hR_large R₂] with n h3 h4 h5 h6 d₁ d₂
  refine (hc' n h4 (fun R hR h7 => ?_) d₁ d₂).trans ?_
  · rcases hR with rfl | rfl
    · exact h5 h7
    · exact h6 h7
  · -- `n ≤ (b + 3) k`.
    set k := n / (b + 2) with hk
    have hu' : n < (b + 3) * k := by
      have h7 := Nat.lt_mul_div_succ n (show 0 < b + 2 by omega)
      rw [← hk] at h7
      nlinarith
    have hu'' : (n : ℝ) ≤ ((b : ℝ) + 3) * k := by exact_mod_cast hu'.le
    have hpow : (n : ℝ) ^ 4 ≤ ((b : ℝ) + 3) ^ 4 * (k : ℝ) ^ 4 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hu'' _
    have hexp : exp (-(ν * (k : ℝ))) = exp (-ν) ^ k := by
      rw [← exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    simp only [Function.comp_apply] at h3
    rw [← hk] at h3
    have h7 : (k : ℝ) ^ 4 * exp (-ν) ^ k < ε / K := h3
    have h8 : K * ((k : ℝ) ^ 4 * exp (-ν) ^ k) ≤ ε := by
      have := (lt_div_iff₀' hK0).1 h7
      exact this.le
    have h9 : 0 ≤ exp (-ν) ^ k := by positivity
    calc (n : ℝ) ^ 4 * (2 * K₀) * exp (-ν) ^ k
        ≤ ((b : ℝ) + 3) ^ 4 * (k : ℝ) ^ 4 * (2 * K₀) * exp (-ν) ^ k := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpow (by positivity)) h9
      _ = K * ((k : ℝ) ^ 4 * exp (-ν) ^ k) := by
          rw [hK]
          ring
      _ ≤ ε := h8

/-! ### Theorem 2 -/

/-- **Theorem 2 of Lecture 24 (Hui and Humblet).** The capacity region of the totally asynchronous
DM-MAC is the set of rate pairs with `R₁ ≤ I(X₁; Y | X₂)`, `R₂ ≤ I(X₂; Y | X₁)` and
`R₁ + R₂ ≤ I(X₁, X₂; Y)` for some `p(x₁) p(x₂)`. Rates are in bits and informations in nats. -/
theorem asyncCapacityRegionBits_eq [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    asyncCapacityRegionBits W = asyncRegionBits W := by
  refine Set.Subset.antisymm (asyncCapacityRegionBits_subset hW) fun R hR => ?_
  obtain ⟨p₁, p₂, hp₁, hp₂, h₁, h₂, h₁₂⟩ := hR
  have hl := log_pos one_lt_two
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  refine ⟨(R.1 - ε / 2, R.2 - ε / 2), ?_, ?_⟩
  · refine isAchievableAsync_of_lt hp₁ hp₂ hW ?_ ?_ ?_ <;> simp only <;> nlinarith
  · rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    simp only
    constructor <;> rw [abs_lt] <;> constructor <;> linarith

end InfoTheory
