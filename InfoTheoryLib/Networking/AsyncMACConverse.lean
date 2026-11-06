/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.Networking.AsyncMAC

/-!
# The totally asynchronous multiple-access channel: the converse

The converse of Theorem 2 of Lecture 24 of El Gamal and Kim. The notes decode `κ` blocks from a long
output sequence, with sender 1 aligned and a uniform delay `D₂` for sender 2, assume the
communication started in the remote past to ignore the edges, and let `κ → ∞` at the end.

Here the edges are removed by running a code cyclically on three blocks. Each window of `2 n - 1`
outputs of the cyclic system then has the same law as a window of the real system, since it sees
three distinct messages of each sender. So the whole cyclic system is an ordinary code for the
synchronous DM-MAC of length `3 n`, with `3` messages per sender and error at most `3 ε`, and the
converse bounds of the DM-MAC apply directly with `κ = 3`.

The letters of the cyclic system have laws `P₁(i mod n)` and `P₂((i - d) mod n)`. Averaging over the
delay `d` of sender 2 makes the position of its letter independent of the position of the letter of
sender 1. This is why time sharing is lost: the average of `p₁(x₁) p₂(x₂)` over a product of
independent positions is again a product (`sum_macInfo₁₂_le` and its companions).

## Main definitions

* `cycInput enc d w i`: the input of a sender in the cyclic system.
* `AsyncCode.cycCode c d`: the cyclic system as a code for the DM-MAC.
* `letterAvg enc`: the law of a letter of a uniform codeword at a uniform position.

## Main statements

* `sum_pi_prod_comp`: marginalizing a product law over the coordinates outside an injection.
* `AsyncCode.avgErrProb_cycCode_le`: the error of the cyclic system.
* `AsyncCode.log_le_of_asyncErr_le`: the single-letter bounds for one code.
* `IsAchievableAsync.mem_asyncRegionBits`, `asyncCapacityRegionBits_subset`: **Theorem 2 of
  Lecture 24, converse**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset Filter Topology Real

namespace InfoTheory

/-! ### Marginalizing a product law -/

/-- Summing out the coordinates of a product law outside the range of an injection. -/
lemma sum_pi_prod_comp {ι κ b : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype b] (g : ι → b → ℝ) (hg : ∀ i, ∑ x, g i x = 1) {ρ : κ → ι}
    (hρ : Function.Injective ρ) (F : (κ → b) → ℝ) :
    ∑ y : ι → b, (∏ i, g i (y i)) * F (fun k => y (ρ k)) =
      ∑ v : κ → b, (∏ k, g (ρ k) (v k)) * F v := by
  classical
  -- For fixed `v`, the mass of the event `y ∘ ρ = v`.
  have hmass : ∀ v : κ → b,
      ∑ y : ι → b, (∏ i, g i (y i)) * (if (fun k => y (ρ k)) = v then 1 else 0) =
        ∏ k, g (ρ k) (v k) := by
    intro v
    set h : ι → b → ℝ := fun i x =>
      if hi : ∃ k, ρ k = i then (if x = v hi.choose then g i x else 0) else g i x with hh
    have hpt : ∀ y : ι → b, (∏ i, g i (y i)) * (if (fun k => y (ρ k)) = v then (1 : ℝ) else 0) =
        ∏ i, h i (y i) := by
      intro y
      by_cases hyv : (fun k => y (ρ k)) = v
      · rw [ite_eq_left hyv, mul_one]
        refine prod_congr rfl fun i _ => ?_
        simp only [hh]
        split_ifs with hi hx
        · rfl
        · exfalso
          apply hx
          have := congrFun hyv hi.choose
          rw [← this, hi.choose_spec]
        · rfl
      · rw [ite_eq_right hyv, mul_zero]
        obtain ⟨k, hk⟩ := Function.ne_iff.1 hyv
        refine (prod_eq_zero (mem_univ (ρ k)) ?_).symm
        have hi : ∃ k', ρ k' = ρ k := ⟨k, rfl⟩
        have hch : hi.choose = k := hρ hi.choose_spec
        simp only [hh, hi, dite_true]
        rw [ite_eq_right]
        rw [hch]
        exact hk
    simp only [hpt]
    rw [← Fintype.prod_sum h]
    have hsum : ∀ i, ∑ x, h i x = if hi : ∃ k, ρ k = i then g i (v hi.choose) else 1 := by
      intro i
      by_cases hi : ∃ k, ρ k = i
      · simp [hh, hi]
      · simp [hh, hi, hg]
    simp only [hsum]
    symm
    refine Fintype.prod_of_injective ρ hρ _ _ (fun i hi => ?_) (fun k => ?_)
    · have : ¬ ∃ k, ρ k = i := fun ⟨k, hk⟩ => hi ⟨k, hk⟩
      simp [this]
    · have hi : ∃ k', ρ k' = ρ k := ⟨k, rfl⟩
      have hch : hi.choose = k := hρ hi.choose_spec
      simp [hi, hch]
  have hF : ∀ y : ι → b, F (fun k => y (ρ k)) =
      ∑ v : κ → b, F v * (if (fun k => y (ρ k)) = v then 1 else 0) := by
    intro y
    simp
  simp only [hF, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← hmass v, sum_mul]
  exact sum_congr rfl fun y _ => by ring

/-! ### The cyclic system -/

section Cyclic

variable {n : ℕ}

/-- The block of a slot of the cyclic system of three blocks is at most `2`. -/
lemma cyc_mod_lt (x : ℕ) : x / n % 3 < 3 := Nat.mod_lt _ (by norm_num)

/-- **The cyclic system.** A sender with the three messages `w`, sending them in turn over the
`3 n` slots of a cycle, with delay `d`. -/
def cycInput {M : ℕ} {α : Type*} (enc : Fin M → Fin n → α) (d : Fin n) (w : Fin 3 → Fin M)
    (i : Fin (3 * n)) : α :=
  enc (w ⟨((i : ℕ) + 3 * n - d) / n % 3, cyc_mod_lt _⟩)
    ⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ d.pos⟩

/-- The window `l` of the cyclic system: the `2 n - 1` slots starting at the beginning of block
`l`, around the cycle. -/
def cycWindow (l : Fin 3) (t : Fin (2 * n - 1)) : Fin (3 * n) :=
  ⟨if (l : ℕ) * n + t < 3 * n then (l : ℕ) * n + t else (l : ℕ) * n + t - 3 * n, by
    have ht := t.isLt
    have hl := l.isLt
    have hb : (l : ℕ) * n ≤ 2 * n := Nat.mul_le_mul_right _ (by omega)
    split_ifs <;> omega⟩

lemma cycWindow_injective (l : Fin 3) : Function.Injective (cycWindow (n := n) l) := by
  intro t t' h
  have h' := congrArg Fin.val h
  have ht := t.isLt
  have ht' := t'.isLt
  simp only [cycWindow] at h'
  ext
  fin_cases l <;> simp only [zero_mul, one_mul] at h' <;> split_ifs at h' <;> omega

/-- The slot `cycWindow l t` is at block offset `A` from the slot `t` of the real window. -/
lemma exists_cycWindow_eq (l : Fin 3) (d : Fin n) (t : Fin (2 * n - 1)) :
    ∃ A : ℕ, ((cycWindow l t : Fin (3 * n)) : ℕ) + 3 * n - d = A * n + ((t : ℕ) + n - d) ∧
      A % 3 = ((l : ℕ) + 2) % 3 := by
  have ht := t.isLt
  have hd := d.isLt
  fin_cases l
  · refine ⟨2, ?_, rfl⟩
    simp only [cycWindow, zero_mul, zero_add]
    rw [ite_eq_left (by omega)]
    omega
  · refine ⟨3, ?_, rfl⟩
    simp only [cycWindow, one_mul]
    rw [ite_eq_left (by omega)]
    omega
  · by_cases h : (t : ℕ) < n
    · refine ⟨4, ?_, rfl⟩
      simp only [cycWindow]
      rw [ite_eq_left (by omega)]
      omega
    · refine ⟨1, ?_, rfl⟩
      simp only [cycWindow]
      rw [ite_eq_right (by omega)]
      omega

/-- **A window of the cyclic system looks like a window of the real system.** -/
lemma cycInput_cycWindow {M : ℕ} {α : Type*} (enc : Fin M → Fin n → α) (d : Fin n)
    (w : Fin 3 → Fin M) (l : Fin 3) (t : Fin (2 * n - 1)) :
    cycInput enc d w (cycWindow l t) = asyncInput enc (fun r => w (r + l + 2)) d t := by
  obtain ⟨A, hA, hA3⟩ := exists_cycWindow_eq l d t
  have hn : 0 < n := d.pos
  unfold cycInput asyncInput
  have h1 : (((cycWindow l t : Fin (3 * n)) : ℕ) + 3 * n - d) % n = ((t : ℕ) + n - d) % n := by
    rw [hA, Nat.mul_comm A n, Nat.mul_add_mod]
  have h2 : (((cycWindow l t : Fin (3 * n)) : ℕ) + 3 * n - d) / n % 3 =
      (((⟨((t : ℕ) + n - d) / n, async_div_lt d t⟩ : Fin 3) + l + 2 : Fin 3) : ℕ) := by
    rw [hA, Nat.add_comm (A * n), Nat.add_mul_div_right _ _ hn]
    simp only [Fin.val_add]
    have h3 := async_div_lt d t
    have hl := l.isLt
    have h22 : ((2 : Fin 3) : ℕ) = 2 := rfl
    rw [h22]
    omega
  have e1 : (⟨(((cycWindow l t : Fin (3 * n)) : ℕ) + 3 * n - d) / n % 3, cyc_mod_lt _⟩ : Fin 3) =
      (⟨((t : ℕ) + n - d) / n, async_div_lt d t⟩ : Fin 3) + l + 2 := Fin.ext h2
  have e2 : (⟨(((cycWindow l t : Fin (3 * n)) : ℕ) + 3 * n - d) % n, Nat.mod_lt _ d.pos⟩ : Fin n) =
      ⟨((t : ℕ) + n - d) % n, Nat.mod_lt _ d.pos⟩ := Fin.ext h1
  rw [e1, e2]

end Cyclic

/-- The law of letter `q` of a uniformly chosen codeword. -/
def letterLaw {M n : ℕ} {α : Type*} [Fintype α] (enc : Fin M → Fin n → α) (q : Fin n) : α → ℝ :=
  dist (uniformPMF (Fin M)) fun m => enc m q

lemma letterLaw_isPMF {M n : ℕ} {α : Type*} [Fintype α] (hM : 0 < M) (enc : Fin M → Fin n → α)
    (q : Fin n) : IsPMF (letterLaw enc q) :=
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  uniformPMF_isPMF.dist _

/-- The letter of a coordinate of three uniform messages has the law of one message. -/
lemma dist_uniform_finFunction_coord {M : ℕ} (hM : 0 < M) {γ : Type*} [Finite γ] (b : Fin 3)
    (f : Fin M → γ) :
    dist (uniformPMF (Fin (M ^ 3))) (fun e => f (finFunctionFinEquiv.symm e b)) =
      dist (uniformPMF (Fin M)) f := by
  have := Fintype.ofFinite γ
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hu : IsPMF (uniformPMF (Fin M)) := uniformPMF_isPMF
  funext a
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 := sum_iidPMF_eval hu (M := 3) b (fun m => if f m = a then (1 : ℝ) else 0)
  have h2 : ∀ w : Fin 3 → Fin M, iidPMF (uniformPMF (Fin M)) 3 w = ((M : ℝ) ^ 3)⁻¹ := by
    intro w
    simp [iidPMF, uniformPMF]
  simp only [dist, uniformPMF, Fintype.card_fin] at h1 h2 ⊢
  rw [← (finFunctionFinEquiv (m := M) (n := 3)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  push_cast
  simp only [h2] at h1
  simpa [mul_ite] using h1

section Cycle

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}
  {M₁ M₂ n : ℕ}

namespace AsyncCode

/-- **The cyclic system as a code for the DM-MAC of length `3 n`.** Sender 1 has delay `0` and
sender 2 has delay `d`. The block messages of each sender form one big message, and each block is
decoded from its own window. -/
def cycCode (c : AsyncCode M₁ M₂ n α₁ α₂ β) (d : Fin n) :
    MACCode (M₁ ^ 3) (M₂ ^ 3) (3 * n) α₁ α₂ β where
  enc₁ e := cycInput c.enc₁ ⟨0, d.pos⟩ (finFunctionFinEquiv.symm e)
  enc₂ e := cycInput c.enc₂ d (finFunctionFinEquiv.symm e)
  dec y := (finFunctionFinEquiv fun l => (c.dec fun t => y (cycWindow l t)).1,
    finFunctionFinEquiv fun l => (c.dec fun t => y (cycWindow l t)).2)

omit [Fintype α₁] [Fintype α₂] in
/-- The error of window `l` of the cyclic system is the error of the real system. -/
lemma sum_window_eq (c : AsyncCode M₁ M₂ n α₁ α₂ β) (d : Fin n) (hW : IsChannel W) (l : Fin 3)
    (e₁ : Fin (M₁ ^ 3)) (e₂ : Fin (M₂ ^ 3)) :
    (∑ y, if (c.dec fun t => y (cycWindow l t)) ≠
        (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) then
        channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0) =
      ∑ y, if c.dec y ≠ ((fun r => finFunctionFinEquiv.symm e₁ (r + l + 2)) 1,
          (fun r => finFunctionFinEquiv.symm e₂ (r + l + 2)) 1) then
        c.windowLaw W ⟨0, d.pos⟩ d (fun r => finFunctionFinEquiv.symm e₁ (r + l + 2))
          (fun r => finFunctionFinEquiv.symm e₂ (r + l + 2)) y else 0 := by
  classical
  have hl : (1 + l + 2 : Fin 3) = l := by
    fin_cases l <;> rfl
  simp only [hl]
  set w₁ := finFunctionFinEquiv.symm e₁
  set w₂ := finFunctionFinEquiv.symm e₂
  have h := sum_pi_prod_comp (fun (i : Fin (3 * n)) b => W ((c.cycCode d).input e₁ e₂ i) b)
    (fun i => (hW _).sum_eq_one) (cycWindow_injective (n := n) l)
    (fun v => if c.dec v ≠ (w₁ l, w₂ l) then (1 : ℝ) else 0)
  have e1 : ∀ y : Fin (3 * n) → β, (if (c.dec fun t => y (cycWindow l t)) ≠ (w₁ l, w₂ l) then
      channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0) =
      (∏ i, W ((c.cycCode d).input e₁ e₂ i) (y i)) *
        (if (c.dec fun t => y (cycWindow l t)) ≠ (w₁ l, w₂ l) then (1 : ℝ) else 0) := by
    intro y
    split_ifs <;> simp [channelExt]
  have e2 : ∀ y : Fin (2 * n - 1) → β, (if c.dec y ≠ (w₁ l, w₂ l) then
      c.windowLaw W ⟨0, d.pos⟩ d (fun r => w₁ (r + l + 2)) (fun r => w₂ (r + l + 2)) y else 0) =
      (∏ t, W ((c.cycCode d).input e₁ e₂ (cycWindow l t)) (y t)) *
        (if c.dec y ≠ (w₁ l, w₂ l) then (1 : ℝ) else 0) := by
    intro y
    have hin : ∀ t, (c.cycCode d).input e₁ e₂ (cycWindow l t) =
        (asyncInput c.enc₁ (fun r => w₁ (r + l + 2)) ⟨0, d.pos⟩ t,
          asyncInput c.enc₂ (fun r => w₂ (r + l + 2)) d t) := fun t => by
      rw [← cycInput_cycWindow, ← cycInput_cycWindow]
      rfl
    simp only [hin]
    split_ifs <;> simp [windowLaw, channelExt]
  simp only [e1, e2]
  exact h

omit [Fintype α₁] [Fintype α₂] in
/-- **The error of the cyclic system is at most the sum of the errors of its windows.** -/
theorem avgErrProb_cycCode_le [Finite α₁] [Finite α₂] (c : AsyncCode M₁ M₂ n α₁ α₂ β) (d : Fin n)
  (hW : IsChannel W)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    (c.cycCode d).avgErrProb W ≤ 3 * c.asyncErr W ⟨0, d.pos⟩ d := by
  have := Fintype.ofFinite α₁
  have := Fintype.ofFinite α₂
  classical
  have hM₁ : (0 : ℝ) < M₁ := by exact_mod_cast h₁
  have hM₂ : (0 : ℝ) < M₂ := by exact_mod_cast h₂
  have hpt : ∀ (e₁ : Fin (M₁ ^ 3)) (e₂ : Fin (M₂ ^ 3)), (c.cycCode d).condErrProb W e₁ e₂ ≤
      ∑ l : Fin 3, ∑ y, if (c.dec fun t => y (cycWindow l t)) ≠
        (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) then
        channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0 := by
    intro e₁ e₂
    unfold MACCode.condErrProb
    rw [sum_comm]
    refine sum_le_sum fun y _ => ?_
    have hnn : ∀ l : Fin 3, 0 ≤ (if (c.dec fun t => y (cycWindow l t)) ≠
        (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) then
        channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0) := fun l => by
      split_ifs
      · exact channelExt_nonneg hW _ _
      · exact le_rfl
    split_ifs with hne
    · by_contra hcon
      push Not at hcon
      apply hne
      have hall : ∀ l : Fin 3, (c.dec fun t => y (cycWindow l t)) =
          (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) := by
        intro l
        by_contra hl
        have h3 := single_le_sum (f := fun l : Fin 3 =>
          (if (c.dec fun t => y (cycWindow l t)) ≠
          (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) then
          channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0)) (fun l _ => hnn l)
          (mem_univ l)
        simp only [ne_eq, hl, not_false_eq_true, ite_true] at h3
        exact absurd h3 (not_le.2 hcon)
      have h1 : (fun l => (c.dec fun t => y (cycWindow l t)).1) = finFunctionFinEquiv.symm e₁ :=
        funext fun l => by rw [hall l]
      have h2 : (fun l => (c.dec fun t => y (cycWindow l t)).2) = finFunctionFinEquiv.symm e₂ :=
        funext fun l => by rw [hall l]
      simp only [cycCode, h1, h2, Equiv.apply_symm_apply]
    · exact sum_nonneg fun l _ => hnn l
  unfold MACCode.avgErrProb
  have hcast : ((M₁ ^ 3 : ℕ) : ℝ) * ((M₂ ^ 3 : ℕ) : ℝ) = (M₁ : ℝ) ^ 3 * (M₂ : ℝ) ^ 3 := by
    push_cast
    ring
  rw [hcast, div_le_iff₀ (by positivity)]
  -- Each window contributes the same amount, by reindexing the messages.
  have hwin : ∀ l : Fin 3, (∑ e₁ : Fin (M₁ ^ 3), ∑ e₂ : Fin (M₂ ^ 3), ∑ y,
      if (c.dec fun t => y (cycWindow l t)) ≠
        (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) then
        channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0) =
      c.asyncErr W ⟨0, d.pos⟩ d * ((M₁ : ℝ) ^ 3 * (M₂ : ℝ) ^ 3) := by
    intro l
    have hne : (M₁ : ℝ) ^ 3 * (M₂ : ℝ) ^ 3 ≠ 0 := by positivity
    rw [asyncErr, div_mul_cancel₀ _ hne]
    simp only [c.sum_window_eq d hW l]
    set G : (Fin 3 → Fin M₁) → (Fin 3 → Fin M₂) → ℝ := fun m₁ m₂ => ∑ y,
      if c.dec y ≠ (m₁ 1, m₂ 1) then c.windowLaw W ⟨0, d.pos⟩ d m₁ m₂ y else 0 with hG
    have hrot₁ : ∀ F : (Fin 3 → Fin M₁) → ℝ, ∑ e : Fin (M₁ ^ 3),
        F (fun r => finFunctionFinEquiv.symm e (r + l + 2)) = ∑ m, F m := by
      intro F
      rw [← (finFunctionFinEquiv (m := M₁) (n := 3)).sum_comp]
      simp only [Equiv.symm_apply_apply]
      exact ((Equiv.addRight (l + 2 : Fin 3)).arrowCongr (Equiv.refl _)).symm.sum_comp F |>.trans
        rfl |> fun h => by
          convert h using 3 with w
          funext r
          simp [add_assoc]
    have hrot₂ : ∀ F : (Fin 3 → Fin M₂) → ℝ, ∑ e : Fin (M₂ ^ 3),
        F (fun r => finFunctionFinEquiv.symm e (r + l + 2)) = ∑ m, F m := by
      intro F
      rw [← (finFunctionFinEquiv (m := M₂) (n := 3)).sum_comp]
      simp only [Equiv.symm_apply_apply]
      exact ((Equiv.addRight (l + 2 : Fin 3)).arrowCongr (Equiv.refl _)).symm.sum_comp F |>.trans
        rfl |> fun h => by
          convert h using 3 with w
          funext r
          simp [add_assoc]
    calc _ = ∑ e₁ : Fin (M₁ ^ 3), ∑ e₂ : Fin (M₂ ^ 3),
          G (fun r => finFunctionFinEquiv.symm e₁ (r + l + 2))
            (fun r => finFunctionFinEquiv.symm e₂ (r + l + 2)) := rfl
      _ = ∑ e₁ : Fin (M₁ ^ 3), ∑ m₂, G (fun r => finFunctionFinEquiv.symm e₁ (r + l + 2)) m₂ :=
          sum_congr rfl fun e₁ _ => hrot₂ _
      _ = ∑ m₁, ∑ m₂, G m₁ m₂ := hrot₁ fun m₁ => ∑ m₂, G m₁ m₂
  calc ∑ e₁ : Fin (M₁ ^ 3), ∑ e₂ : Fin (M₂ ^ 3), (c.cycCode d).condErrProb W e₁ e₂
      ≤ ∑ e₁ : Fin (M₁ ^ 3), ∑ e₂ : Fin (M₂ ^ 3), ∑ l : Fin 3, ∑ y,
        if (c.dec fun t => y (cycWindow l t)) ≠
          (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) then
          channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0 :=
        sum_le_sum fun e₁ _ => sum_le_sum fun e₂ _ => hpt e₁ e₂
    _ = ∑ l : Fin 3, ∑ e₁ : Fin (M₁ ^ 3), ∑ e₂ : Fin (M₂ ^ 3), ∑ y,
        if (c.dec fun t => y (cycWindow l t)) ≠
          (finFunctionFinEquiv.symm e₁ l, finFunctionFinEquiv.symm e₂ l) then
          channelExt W (3 * n) ((c.cycCode d).input e₁ e₂) y else 0 := by
        exact (sum_congr rfl fun e₁ _ => sum_comm).trans sum_comm
    _ = 3 * c.asyncErr W ⟨0, d.pos⟩ d * ((M₁ : ℝ) ^ 3 * (M₂ : ℝ) ^ 3) := by
        simp only [hwin]
        simp [mul_assoc]

omit [Fintype α₂] [Fintype β] in
lemma letterDist₁_cycCode (c : AsyncCode M₁ M₂ n α₁ α₂ β) (d : Fin n) (h₁ : 0 < M₁)
    (i : Fin (3 * n)) :
    (c.cycCode d).letterDist₁ i = letterLaw c.enc₁ ⟨(i : ℕ) % n, Nat.mod_lt _ d.pos⟩ := by
  have h := dist_uniform_finFunction_coord h₁
    (⟨((i : ℕ) + 3 * n - 0) / n % 3, cyc_mod_lt _⟩ : Fin 3)
    (fun m => c.enc₁ m ⟨(i : ℕ) % n, Nat.mod_lt _ d.pos⟩)
  unfold MACCode.letterDist₁ letterLaw
  rw [← h]
  congr 1
  funext e
  simp only [cycCode, cycInput]
  congr 2
  rw [Nat.sub_zero, Nat.add_mul_mod_self_right]

omit [Fintype α₁] [Fintype β] in
lemma letterDist₂_cycCode (c : AsyncCode M₁ M₂ n α₁ α₂ β) (d : Fin n) (h₂ : 0 < M₂)
    (i : Fin (3 * n)) :
    (c.cycCode d).letterDist₂ i =
      letterLaw c.enc₂ ⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ d.pos⟩ := by
  have h := dist_uniform_finFunction_coord h₂
    (⟨((i : ℕ) + 3 * n - d) / n % 3, cyc_mod_lt _⟩ : Fin 3)
    (fun m => c.enc₂ m ⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ d.pos⟩)
  unfold MACCode.letterDist₂ letterLaw
  rw [← h]
  rfl

end AsyncCode

end Cycle

/-! ### Averaging over the delay -/

section Average

variable {n : ℕ}

/-- **Averaging over the delay.** Over a uniform delay, the positions of the letters of the two
senders range independently over all pairs of positions. -/
lemma sum_cyc_eq (hn : 0 < n) (J : Fin n → Fin n → ℝ) :
    ∑ d : Fin n, ∑ i : Fin (3 * n), J ⟨(i : ℕ) % n, Nat.mod_lt _ hn⟩
      ⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ hn⟩ = 3 * ∑ q, ∑ u, J q u := by
  rw [sum_comm]
  have hd : ∀ i : Fin (3 * n), ∑ d : Fin n, J ⟨(i : ℕ) % n, Nat.mod_lt _ hn⟩
      ⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ hn⟩ = ∑ u, J ⟨(i : ℕ) % n, Nat.mod_lt _ hn⟩ u := by
    intro i
    have hinj : Function.Injective fun d : Fin n =>
        (⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ hn⟩ : Fin n) := by
      intro d d' h
      have h' : ((i : ℕ) + 3 * n - d) % n = ((i : ℕ) + 3 * n - d') % n := congrArg Fin.val h
      have hdn := d.isLt
      have hdn' := d'.isLt
      rcases le_total (d : ℕ) d' with hle | hle
      · have h1 : (i : ℕ) + 3 * n - d' ≤ (i : ℕ) + 3 * n - d := by omega
        have h2 := (Nat.modEq_iff_dvd' h1).1 h'.symm
        have h3 : (i : ℕ) + 3 * n - d - ((i : ℕ) + 3 * n - d') = (d' : ℕ) - d := by omega
        rw [h3] at h2
        have h4 : (d' : ℕ) - d = 0 := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
        exact Fin.ext (by omega)
      · have h1 : (i : ℕ) + 3 * n - d ≤ (i : ℕ) + 3 * n - d' := by omega
        have h2 := (Nat.modEq_iff_dvd' h1).1 h'
        have h3 : (i : ℕ) + 3 * n - d' - ((i : ℕ) + 3 * n - d) = (d : ℕ) - d' := by omega
        rw [h3] at h2
        have h4 : (d : ℕ) - d' = 0 := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
        exact Fin.ext (by omega)
    exact (Finite.injective_iff_bijective.1 hinj).sum_comp
      (fun u => J ⟨(i : ℕ) % n, Nat.mod_lt _ hn⟩ u)
  simp only [hd]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have hval : ∀ (a : Fin 3) (b : Fin n), (⟨((finProdFinEquiv (a, b) : Fin (3 * n)) : ℕ) % n,
      Nat.mod_lt _ hn⟩ : Fin n) = b := by
    intro a b
    refine Fin.ext ?_
    simp only [finProdFinEquiv_apply_val]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
  simp only [hval]
  simp

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The average of a family of laws. -/
def avgLaw {ι : Type*} [Fintype ι] (P : ι → α → ℝ) (a : α) : ℝ :=
  (∑ i, P i a) / Fintype.card ι

omit [Fintype β] in
lemma avgLaw_isPMF {ι : Type*} [Fintype ι] [Nonempty ι] {P : ι → α → ℝ} (hP : ∀ i, IsPMF (P i)) :
    IsPMF (avgLaw P) := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨fun a => div_nonneg (sum_nonneg fun i _ => (hP i).nonneg a) hc.le, ?_⟩
  unfold avgLaw
  rw [← sum_div, sum_comm]
  simp [(hP _).sum_eq_one, hc.ne']

/-- By concavity, the average of `I(X; Y)` is at most `I(X; Y)` at the average input. -/
lemma sum_mutualInfoOf_le_avg {ι : Type*} [Fintype ι] [Nonempty ι] {P : ι → α → ℝ}
    (hP : ∀ i, IsPMF (P i)) {W : α → β → ℝ} (hW : IsChannel W) :
    ∑ i, mutualInfoOf (P i) W ≤ Fintype.card ι * mutualInfoOf (avgLaw P) W := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hconc := (mutualInfoOf_concave_input hW).le_map_sum (t := univ)
    (w := fun _ : ι => (Fintype.card ι : ℝ)⁻¹) (p := P)
    (fun _ _ => by positivity) (by simp [hc.ne']) (fun i _ => hP i)
  have he : ∑ i, (Fintype.card ι : ℝ)⁻¹ • P i = avgLaw P := by
    funext a
    simp only [avgLaw, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_sum, div_eq_inv_mul]
  rw [he] at hconc
  simp only [smul_eq_mul, ← mul_sum] at hconc
  rw [inv_mul_le_iff₀ hc] at hconc
  exact hconc

end Average

section Letters

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}
  {ι ι' : Type*} [Fintype ι] [Fintype ι'] [Nonempty ι] [Nonempty ι']
  {P₁ : ι → α₁ → ℝ} {P₂ : ι' → α₂ → ℝ}

/-- **Lecture 24: no time sharing.** The average of `I(X₁; Y | X₂)` over independent positions is at
most its value at the average laws. -/
theorem sum_macInfo₁_le (hP₁ : ∀ i, IsPMF (P₁ i)) (hP₂ : ∀ i, IsPMF (P₂ i)) (hW : IsChannel W) :
    ∑ q, ∑ u, macInfo₁ (P₁ q) (P₂ u) W ≤
      Fintype.card ι * (Fintype.card ι' * macInfo₁ (avgLaw P₁) (avgLaw P₂) W) := by
  have hc : (Fintype.card ι' : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [macInfo₁_eq_sum (avgLaw_isPMF hP₁) (avgLaw_isPMF hP₂) hW]
  have h1 : ∀ q u, macInfo₁ (P₁ q) (P₂ u) W =
      ∑ b, P₂ u b * mutualInfoOf (P₁ q) (fun a => W (a, b)) :=
    fun q u => macInfo₁_eq_sum (hP₁ q) (hP₂ u) hW
  simp only [h1]
  calc ∑ q, ∑ u, ∑ b, P₂ u b * mutualInfoOf (P₁ q) (fun a => W (a, b))
      = ∑ b, (∑ u, P₂ u b) * ∑ q, mutualInfoOf (P₁ q) (fun a => W (a, b)) := by
        simp only [sum_mul, mul_sum]
        symm
        rw [sum_comm]
        refine sum_congr rfl fun q _ => ?_
        exact sum_comm
    _ ≤ ∑ b, (∑ u, P₂ u b) * (Fintype.card ι * mutualInfoOf (avgLaw P₁) (fun a => W (a, b))) :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
          (sum_mutualInfoOf_le_avg hP₁ fun a => hW (a, b))
          (sum_nonneg fun u _ => (hP₂ u).nonneg b)
    _ = _ := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun b _ => ?_
        simp only [avgLaw]
        field_simp

/-- The analogue of `sum_macInfo₁_le` for `I(X₂; Y | X₁)`. -/
theorem sum_macInfo₂_le (hP₁ : ∀ i, IsPMF (P₁ i)) (hP₂ : ∀ i, IsPMF (P₂ i)) (hW : IsChannel W) :
    ∑ q, ∑ u, macInfo₂ (P₁ q) (P₂ u) W ≤
      Fintype.card ι * (Fintype.card ι' * macInfo₂ (avgLaw P₁) (avgLaw P₂) W) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [macInfo₂_eq_sum (avgLaw_isPMF hP₁) (avgLaw_isPMF hP₂) hW]
  have h1 : ∀ q u, macInfo₂ (P₁ q) (P₂ u) W =
      ∑ a, P₁ q a * mutualInfoOf (P₂ u) (fun b => W (a, b)) :=
    fun q u => macInfo₂_eq_sum (hP₁ q) (hP₂ u) hW
  simp only [h1]
  calc ∑ q, ∑ u, ∑ a, P₁ q a * mutualInfoOf (P₂ u) (fun b => W (a, b))
      = ∑ a, (∑ q, P₁ q a) * ∑ u, mutualInfoOf (P₂ u) (fun b => W (a, b)) := by
        simp only [sum_mul, mul_sum]
        symm
        rw [sum_comm]
        exact Eq.trans (sum_congr rfl fun u _ => sum_comm) sum_comm
    _ ≤ ∑ a, (∑ q, P₁ q a) * (Fintype.card ι' * mutualInfoOf (avgLaw P₂) (fun b => W (a, b))) :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (sum_mutualInfoOf_le_avg hP₂ fun b => hW (a, b))
          (sum_nonneg fun q _ => (hP₁ q).nonneg a)
    _ = _ := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        simp only [avgLaw]
        field_simp

/-- **The heart of Lecture 24's converse.** The average of `p₁(x₁) p₂(x₂)` over independent
positions is the product of the averages, so `I(X₁, X₂; Y)` needs no time sharing. -/
theorem sum_macInfo₁₂_le (hP₁ : ∀ i, IsPMF (P₁ i)) (hP₂ : ∀ i, IsPMF (P₂ i)) (hW : IsChannel W) :
    ∑ q, ∑ u, macInfo₁₂ (P₁ q) (P₂ u) W ≤
      Fintype.card ι * (Fintype.card ι' * macInfo₁₂ (avgLaw P₁) (avgLaw P₂) W) := by
  have hc₁ : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc₂ : (Fintype.card ι' : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := sum_mutualInfoOf_le_avg (ι := ι × ι') (P := fun z => prodDist (P₁ z.1) (P₂ z.2))
    (fun z => (hP₁ z.1).prodDist (hP₂ z.2)) hW
  have he : avgLaw (fun z : ι × ι' => prodDist (P₁ z.1) (P₂ z.2)) =
      prodDist (avgLaw P₁) (avgLaw P₂) := by
    funext x
    simp only [avgLaw, prodDist, Fintype.card_prod, Fintype.sum_prod_type]
    rw [div_mul_div_comm, sum_mul]
    push_cast
    congr 1
    refine sum_congr rfl fun q _ => ?_
    rw [mul_sum]
  rw [he, Fintype.card_prod, Fintype.sum_prod_type] at h
  push_cast at h
  rw [← mul_assoc]
  exact h

end Letters

/-! ### The bounds for one code -/

section Bounds

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β] {W : α₁ × α₂ → β → ℝ}
  {M₁ M₂ n : ℕ}

/-- Dividing the bound of the cyclic system, averaged over the delay, by the number of delays. -/
lemma le_of_sum_cyc (hn : 0 < n) {B K I : ℝ} {J : Fin n → Fin n → ℝ}
    (hd : ∀ d : Fin n, B ≤ ∑ i : Fin (3 * n), J ⟨(i : ℕ) % n, Nat.mod_lt _ hn⟩
      ⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ hn⟩ + K)
    (hJ : ∑ q, ∑ u, J q u ≤ (n : ℝ) * (n * I)) : B ≤ 3 * n * I + K := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∑ _d : Fin n, B ≤ ∑ d : Fin n, (∑ i : Fin (3 * n), J ⟨(i : ℕ) % n, Nat.mod_lt _ hn⟩
      ⟨((i : ℕ) + 3 * n - d) % n, Nat.mod_lt _ hn⟩ + K) := sum_le_sum fun d _ => hd d
  rw [sum_add_distrib, sum_cyc_eq hn] at h1
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 : (n : ℝ) * B ≤ (n : ℝ) * (3 * n * I + K) := by nlinarith
  exact le_of_mul_le_mul_left h2 hn'

/-- **The single-letter bounds for one code.** If `P_e(0, d) ≤ ε` for each delay `d` of sender 2,
then `log M₁`, `log M₂` and `log (M₁ M₂)` are at most `n` times the three mutual informations of a
product input distribution, up to the terms of Fano's inequality. -/
theorem AsyncCode.log_le_of_asyncErr_le (c : AsyncCode M₁ M₂ n α₁ α₂ β) (hW : IsChannel W)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (hn : 0 < n) {ε : ℝ}
    (hε : ∀ d : Fin n, c.asyncErr W ⟨0, hn⟩ d ≤ ε) :
    ∃ p₁ p₂, IsPMF p₁ ∧ IsPMF p₂ ∧
      3 * log M₁ ≤ 3 * n * macInfo₁ p₁ p₂ W + (log 2 + 9 * ε * log (M₁ * M₂)) ∧
      3 * log M₂ ≤ 3 * n * macInfo₂ p₁ p₂ W + (log 2 + 9 * ε * log (M₁ * M₂)) ∧
      3 * log (M₁ * M₂) ≤ 3 * n * macInfo₁₂ p₁ p₂ W + (log 2 + 9 * ε * log (M₁ * M₂)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hM₁ : (1 : ℝ) ≤ M₁ := by exact_mod_cast h₁
  have hM₂ : (1 : ℝ) ≤ M₂ := by exact_mod_cast h₂
  have hL : 0 ≤ log ((M₁ : ℝ) * M₂) := log_nonneg (by nlinarith)
  have hM₁0 : (M₁ : ℝ) ≠ 0 := by linarith
  have hM₂0 : (M₂ : ℝ) ≠ 0 := by linarith
  have hb₁ : 0 < M₁ ^ 3 := by positivity
  have hb₂ : 0 < M₂ ^ 3 := by positivity
  set P₁ := letterLaw c.enc₁ with hP₁
  set P₂ := letterLaw c.enc₂ with hP₂
  have hp₁ : ∀ q, IsPMF (P₁ q) := letterLaw_isPMF h₁ _
  have hp₂ : ∀ q, IsPMF (P₂ q) := letterLaw_isPMF h₂ _
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
  have hlog₁ : log ((M₁ ^ 3 : ℕ) : ℝ) = 3 * log M₁ := by
    push_cast
    rw [Real.log_pow]
    norm_num
  have hlog₂ : log ((M₂ ^ 3 : ℕ) : ℝ) = 3 * log M₂ := by
    push_cast
    rw [Real.log_pow]
    norm_num
  have hlogm : log (((M₁ ^ 3 : ℕ) : ℝ) * ((M₂ ^ 3 : ℕ) : ℝ)) = 3 * log ((M₁ : ℝ) * M₂) := by
    push_cast
    rw [← mul_pow, Real.log_pow]
    norm_num
  -- The Fano term of the cyclic system.
  have hfano : ∀ d : Fin n, (c.cycCode d).avgErrProb W *
      log (((M₁ ^ 3 : ℕ) : ℝ) * ((M₂ ^ 3 : ℕ) : ℝ)) ≤ 9 * ε * log ((M₁ : ℝ) * M₂) := by
    intro d
    rw [hlogm]
    have h3 := c.avgErrProb_cycCode_le d hW h₁ h₂
    have h4 : (c.cycCode d).avgErrProb W ≤ 3 * ε := h3.trans (by linarith [hε d])
    nlinarith
  refine ⟨avgLaw P₁, avgLaw P₂, avgLaw_isPMF hp₁, avgLaw_isPMF hp₂, ?_, ?_, ?_⟩
  · refine le_of_sum_cyc hn (J := fun q u => macInfo₁ (P₁ q) (P₂ u) W) (fun d => ?_) ?_
    · have h3 := (c.cycCode d).log_le_macInfo₁ hW hb₁ hb₂
      rw [hlog₁] at h3
      simp only [c.letterDist₁_cycCode d h₁, c.letterDist₂_cycCode d h₂] at h3
      have h4 := hfano d
      linarith
    · simpa only [hcard] using sum_macInfo₁_le hp₁ hp₂ hW
  · refine le_of_sum_cyc hn (J := fun q u => macInfo₂ (P₁ q) (P₂ u) W) (fun d => ?_) ?_
    · have h3 := (c.cycCode d).log_le_macInfo₂ hW hb₁ hb₂
      rw [hlog₂] at h3
      simp only [c.letterDist₁_cycCode d h₁, c.letterDist₂_cycCode d h₂] at h3
      have h4 := hfano d
      linarith
    · simpa only [hcard] using sum_macInfo₂_le hp₁ hp₂ hW
  · refine le_of_sum_cyc hn (J := fun q u => macInfo₁₂ (P₁ q) (P₂ u) W) (fun d => ?_) ?_
    · have h3 := (c.cycCode d).log_mul_le_macInfo₁₂ hW hb₁ hb₂
      have h4 := hfano d
      rw [hlogm] at h3 h4
      simp only [c.letterDist₁_cycCode d h₁, c.letterDist₂_cycCode d h₂] at h3
      linarith
    · simpa only [hcard] using sum_macInfo₁₂_le hp₁ hp₂ hW

/-- The arithmetic of the converse: a bound of the form `3 ⌈n R⌉ log 2 ≤ 3 n I + …` gives
`R log 2 ≤ I + η`. -/
lemma async_arith {R C I η : ℝ} {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : n * R ≤ x)
    (h : 3 * (x * log 2) ≤ 3 * n * I + C) (hC : C ≤ 3 * n * η) : R * log 2 ≤ I + η := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := log_pos one_lt_two
  have h1 : (n : ℝ) * R * log 2 ≤ x * log 2 := mul_le_mul_of_nonneg_right hx hl.le
  have h2 : (n : ℝ) * (R * log 2) ≤ n * (I + η) := by nlinarith
  exact le_of_mul_le_mul_left h2 hn'

/-- **Theorem 2 of Lecture 24, converse.** An achievable rate pair lies in the region. -/
theorem IsAchievableAsync.mem_asyncRegionBits [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W)
    {R₁ R₂ : ℝ} (h : IsAchievableAsync W R₁ R₂) : (R₁, R₂) ∈ asyncRegionBits W := by
  obtain ⟨c, hc⟩ := h
  have hl := log_pos one_lt_two
  refine mem_asyncRegionBits_of_forall hW fun η hη => ?_
  simp only
  set T := |R₁| + |R₂| + 2 with hT
  have hT0 : 0 < T := by positivity
  set ε := η / (9 * T * log 2 + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hεT : 9 * ε * (T * log 2) ≤ η := by
    have hD : 0 < 9 * T * log 2 + 1 := by positivity
    calc 9 * ε * (T * log 2) = η * ((9 * T * log 2) / (9 * T * log 2 + 1)) := by
          rw [hε]
          ring
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left ((div_le_one hD).2 (by linarith)) hη.le
      _ = η := mul_one η
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (log 2 / η)
  obtain ⟨n, hn1, hn2, hn3⟩ := ((hc ε hε0).and ((eventually_ge_atTop n₀).and
    (eventually_gt_atTop 0))).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn3
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn3
  have hbig : log 2 ≤ n * η := by
    have h2 := (div_lt_iff₀ hη).1 hn₀
    have h3 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn2
    nlinarith
  obtain ⟨p₁, p₂, h₁, h₂, h3, h4, h5⟩ := (c n).log_le_of_asyncErr_le hW (by positivity)
    (by positivity) hn3 (ε := ε) (fun d => hn1 _ d)
  -- The sizes of the message sets.
  have hceil : ∀ R : ℝ, (⌈n * R⌉₊ : ℝ) ≤ n * |R| + 1 := by
    intro R
    have h6 : (⌈n * R⌉₊ : ℝ) ≤ ⌈n * |R|⌉₊ := by
      exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left (le_abs_self R) hn'.le)
    have h7 : (⌈n * |R|⌉₊ : ℝ) < n * |R| + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hlog : ∀ m : ℕ, log ((2 ^ m : ℕ) : ℝ) = m * log 2 := by
    intro m
    push_cast
    rw [Real.log_pow]
  have hlogp : log (((2 ^ ⌈n * R₁⌉₊ : ℕ) : ℝ) * ((2 ^ ⌈n * R₂⌉₊ : ℕ) : ℝ)) =
      (⌈n * R₁⌉₊ + ⌈n * R₂⌉₊ : ℝ) * log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), hlog, hlog]
    ring
  rw [hlog] at h3 h4
  rw [hlogp] at h3 h4 h5
  have hbig2 : (⌈n * R₁⌉₊ + ⌈n * R₂⌉₊ : ℝ) ≤ n * T := by
    have h6 := hceil R₁
    have h7 := hceil R₂
    rw [hT]
    nlinarith
  have hC : log 2 + 9 * ε * ((⌈n * R₁⌉₊ + ⌈n * R₂⌉₊ : ℝ) * log 2) ≤ 3 * n * η := by
    have h6 : (⌈n * R₁⌉₊ + ⌈n * R₂⌉₊ : ℝ) * log 2 ≤ n * T * log 2 :=
      mul_le_mul_of_nonneg_right hbig2 hl.le
    have h7 : 9 * ε * ((⌈n * R₁⌉₊ + ⌈n * R₂⌉₊ : ℝ) * log 2) ≤ 9 * ε * (n * T * log 2) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    have h8 : 9 * ε * (n * T * log 2) = n * (9 * ε * (T * log 2)) := by ring
    have h9 : n * (9 * ε * (T * log 2)) ≤ n * η := mul_le_mul_of_nonneg_left hεT hn'.le
    nlinarith
  refine ⟨p₁, p₂, h₁, h₂, ?_, ?_, ?_⟩
  · exact async_arith hn3 (Nat.le_ceil _) h3 hC
  · exact async_arith hn3 (Nat.le_ceil _) h4 hC
  · refine async_arith hn3 (x := (⌈n * R₁⌉₊ + ⌈n * R₂⌉₊ : ℝ)) ?_ (by linarith) hC
    have h6 := Nat.le_ceil ((n : ℝ) * R₁)
    have h7 := Nat.le_ceil ((n : ℝ) * R₂)
    nlinarith

/-- **Theorem 2 of Lecture 24, converse.** The capacity region lies in the region. -/
theorem asyncCapacityRegionBits_subset [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    asyncCapacityRegionBits W ⊆ asyncRegionBits W :=
  closure_minimal (fun _ hR => IsAchievableAsync.mem_asyncRegionBits hW hR)
    (isClosed_asyncRegionBits hW)

end Bounds

end InfoTheory
