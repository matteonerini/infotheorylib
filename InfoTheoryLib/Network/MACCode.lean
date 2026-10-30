/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Code
public import InfoTheoryLib.ChannelCoding.JointTypicality

/-!
# Codes for the multiple-access channel

A discrete memoryless multiple-access channel has two input alphabets `𝒳₁`, `𝒳₂`, an output
alphabet `𝒴` and a transition matrix `p(y | x₁, x₂)`, which we write as a channel
`W : 𝒳₁ × 𝒳₂ → 𝒴 → ℝ` with a product input. A `((M₁, M₂), n)` code has one encoder per sender and
a decoder recovering both messages. A rate pair `(R₁, R₂)` is achievable if there are
`((⌈e^{nR₁}⌉, ⌈e^{nR₂}⌉), n)` codes whose average probability of error tends to `0`, and the
capacity region is the closure of the set of achievable rate pairs.

The capacity region is convex (Theorem 15.3.2): using one code for the first `⌊λn⌋` symbols and
another for the rest achieves the convex combination of the rates, up to an arbitrarily small
loss. We prove this for the set `macSlackSet W` of the rate pairs `R` such that `R - (δ, δ)` is
achievable for every `δ > 0`, which lies between the achievable rates and their closure.

## Main definitions

* `MACCode M₁ M₂ n α₁ α₂ β`: **(15.52)–(15.54)** a `((M₁, M₂), n)` code.
* `MACCode.condErrProb`, `MACCode.avgErrProb`: the probability of error for a message pair, and
  **(15.55)** the average probability of error.
* `IsAchievableMAC W R₁ R₂`, `macCapacityRegion W`: achievable rate pairs and the capacity region.
* `macSlackSet W`: the rate pairs `R` with `R - (δ, δ)` achievable for every `δ > 0`.
* `MACCode.append`: the code using two codes one after the other.

## Main statements

* `MACCode.exists_avgErrProb_le_of_le`: a code can be restricted to fewer messages without
  increasing its average probability of error.
* `MACCode.avgErrProb_append_le`: the probability of error of two codes used one after the other
  is at most the sum of their probabilities of error.
* `IsAchievableMAC.mono`: lower rates are achievable.
* `convex_macSlackSet`: **Theorem 15.3.2 (time sharing)**, the rate pairs achievable up to an
  arbitrarily small loss form a convex set.
* `macSlackSet_subset_macCapacityRegion`.

## Implementation notes

As in Chapter 7, the messages `1, …, M` are `0, …, M - 1 : Fin M`, and rates are in nats. The
input sequence of the message pair `(i, j)` is `zipSeq (x₁(i)) (x₂(j))`, so the probability of
receiving `yⁿ` is `channelExt W n (zipSeq (x₁(i)) (x₂(j))) yⁿ`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 15.3 and
  15.3.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β : Type*} [Fintype β]

/-- **Definition (15.52)–(15.54).** A `((M₁, M₂), n)` code for the multiple-access channel: an
encoder for each sender and a decoder guessing both messages from the received sequence. -/
structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*) where
  /-- The encoder `X₁ : {0, …, M₁ - 1} → 𝒳₁ⁿ` of sender 1. -/
  enc₁ : Fin M₁ → Fin n → α₁
  /-- The encoder `X₂ : {0, …, M₂ - 1} → 𝒳₂ⁿ` of sender 2. -/
  enc₂ : Fin M₂ → Fin n → α₂
  /-- The decoder `g : 𝒴ⁿ → {0, …, M₁ - 1} × {0, …, M₂ - 1}`. -/
  dec : (Fin n → β) → Fin M₁ × Fin M₂

namespace MACCode

variable {M₁ M₂ n : ℕ} (W : α₁ × α₂ → β → ℝ) (c : MACCode M₁ M₂ n α₁ α₂ β)

/-- The channel input `(x₁(i), x₂(j))` when the message pair `(i, j)` is sent. -/
def input (i : Fin M₁) (j : Fin M₂) : Fin n → α₁ × α₂ := zipSeq (c.enc₁ i) (c.enc₂ j)

open Classical in
/-- The probability `Pr{g(Yⁿ) ≠ (i, j) | (i, j) sent}` of a decoding error for the message pair
`(i, j)`. -/
def condErrProb (i : Fin M₁) (j : Fin M₂) : ℝ :=
  ∑ y, if c.dec y ≠ (i, j) then channelExt W n (c.input i j) y else 0

/-- **Definition (15.55).** The average probability of error, for independent and uniformly
distributed messages. -/
def avgErrProb : ℝ := (∑ i, ∑ j, c.condErrProb W i j) / (M₁ * M₂)

variable {W}

lemma condErrProb_nonneg (hW : IsChannel W) (i : Fin M₁) (j : Fin M₂) :
    0 ≤ c.condErrProb W i j := by
  classical
  exact sum_nonneg fun y _ => by split_ifs <;> simp [channelExt_nonneg hW]

lemma condErrProb_le_one (hW : IsChannel W) (i : Fin M₁) (j : Fin M₂) :
    c.condErrProb W i j ≤ 1 := by
  classical
  calc c.condErrProb W i j ≤ ∑ y, channelExt W n (c.input i j) y :=
        sum_le_sum fun y _ => by split_ifs <;> simp [channelExt_nonneg hW]
    _ = 1 := ((hW.ext n) (c.input i j)).sum_eq_one

lemma avgErrProb_nonneg (hW : IsChannel W) : 0 ≤ c.avgErrProb W :=
  div_nonneg (sum_nonneg fun i _ => sum_nonneg fun j _ => c.condErrProb_nonneg hW i j)
    (by positivity)

/-! ### Fewer messages -/

/-- Re-index the messages along injections `e₁`, `e₂`: send `(x₁(e₁ k), x₂(e₂ l))` for the pair
`(k, l)`, and decode as the old code, mapping back to the new messages. -/
def restrict {M₁' M₂' : ℕ} [NeZero M₁'] [NeZero M₂'] (e₁ : Fin M₁' ↪ Fin M₁)
    (e₂ : Fin M₂' ↪ Fin M₂) : MACCode M₁' M₂' n α₁ α₂ β where
  enc₁ k := c.enc₁ (e₁ k)
  enc₂ l := c.enc₂ (e₂ l)
  dec y := (Function.invFun e₁ (c.dec y).1, Function.invFun e₂ (c.dec y).2)

lemma condErrProb_restrict_le {M₁' M₂' : ℕ} [NeZero M₁'] [NeZero M₂'] (hW : IsChannel W)
    (e₁ : Fin M₁' ↪ Fin M₁) (e₂ : Fin M₂' ↪ Fin M₂) (k : Fin M₁') (l : Fin M₂') :
    (c.restrict e₁ e₂).condErrProb W k l ≤ c.condErrProb W (e₁ k) (e₂ l) := by
  classical
  refine sum_le_sum fun y _ => ?_
  have hin : (c.restrict e₁ e₂).input k l = c.input (e₁ k) (e₂ l) := rfl
  rw [hin]
  by_cases h : c.dec y = (e₁ k, e₂ l)
  · have : (c.restrict e₁ e₂).dec y = (k, l) := by
      simp only [restrict, h]
      rw [Function.leftInverse_invFun e₁.injective k, Function.leftInverse_invFun e₂.injective l]
    simp [this, h]
  · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte]
    split_ifs <;> simp [channelExt_nonneg hW]

/-- Among the elements of `s`, some `k` of them have an average of `f` at most the average over
`s`. -/
lemma exists_subset_sum_mul_le {ι : Type*} (f : ι → ℝ) (s : Finset ι) {k : ℕ}
    (hk : k ≤ #s) : ∃ t ⊆ s, #t = k ∧ (∑ i ∈ t, f i) * #s ≤ (∑ i ∈ s, f i) * k := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, #s = m := ⟨_, rfl⟩
  induction m generalizing s with
  | zero =>
    have hk0 : k = 0 := by omega
    exact ⟨∅, empty_subset _, by simp [hk0], by simp [hk0, hm]⟩
  | succ m ih =>
    by_cases hkm : k = m + 1
    · exact ⟨s, subset_refl _, by omega, by rw [hm, hkm]⟩
    have hne : s.Nonempty := card_pos.1 (by omega)
    obtain ⟨a, ha, hmax⟩ := exists_max_image s f hne
    obtain ⟨t, hts, htk, ht⟩ := ih (s.erase a) (by rw [card_erase_of_mem ha]; omega)
      (by rw [card_erase_of_mem ha]; omega)
    refine ⟨t, hts.trans (erase_subset _ _), htk, ?_⟩
    have hsum := sum_erase_add s f ha
    have hmax' : ∑ i ∈ t, f i ≤ k * f a := by
      have := sum_le_card_nsmul t f (f a) fun i hi => hmax i (mem_of_mem_erase (hts hi))
      rwa [htk, nsmul_eq_mul] at this
    rw [card_erase_of_mem ha, hm] at ht
    rw [hm]
    push_cast at ht ⊢
    nlinarith

omit [Fintype β] in
lemma sum_prod_sum_prod_fst {A A' B B' : Type*} [Fintype A] [Fintype A'] [Fintype B]
    [Fintype B'] (f : A → B → ℝ) :
    ∑ p : A × A', ∑ q : B × B', f p.1 q.1 =
      Fintype.card A' * Fintype.card B' * ∑ a, ∑ b, f a b := by
  simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

omit [Fintype β] in
lemma sum_orderEmbOfFin {ι : Type*} [LinearOrder ι] (t : Finset ι) {k : ℕ} (h : #t = k)
    (g : ι → ℝ) : ∑ x : Fin k, g (t.orderEmbOfFin h x) = ∑ i ∈ t, g i := by
  conv_rhs => rw [← map_orderEmbOfFin_univ t h, sum_map]
  rfl

/-- A code can be restricted to `M₁' ≤ M₁` and `M₂' ≤ M₂` messages without increasing its average
probability of error. -/
theorem exists_avgErrProb_le_of_le (hW : IsChannel W) {M₁' M₂' : ℕ} (h₁ : 0 < M₁')
    (h₂ : 0 < M₂') (hM₁ : M₁' ≤ M₁) (hM₂ : M₂' ≤ M₂) :
    ∃ c' : MACCode M₁' M₂' n α₁ α₂ β, c'.avgErrProb W ≤ c.avgErrProb W := by
  classical
  have : NeZero M₁' := ⟨h₁.ne'⟩
  have : NeZero M₂' := ⟨h₂.ne'⟩
  set L := c.condErrProb W
  obtain ⟨t₁, -, ht₁, hs₁⟩ := exists_subset_sum_mul_le (fun i => ∑ j, L i j) univ (k := M₁')
    (by simpa using hM₁)
  obtain ⟨t₂, -, ht₂, hs₂⟩ := exists_subset_sum_mul_le (fun j => ∑ i ∈ t₁, L i j) univ
    (k := M₂') (by simpa using hM₂)
  set e₁ := (t₁.orderEmbOfFin ht₁).toEmbedding
  set e₂ := (t₂.orderEmbOfFin ht₂).toEmbedding
  refine ⟨c.restrict e₁ e₂, ?_⟩
  simp only [card_univ, Fintype.card_fin] at hs₁ hs₂
  have hle : ∑ k, ∑ l, (c.restrict e₁ e₂).condErrProb W k l ≤ ∑ i ∈ t₁, ∑ j ∈ t₂, L i j := by
    calc ∑ k, ∑ l, (c.restrict e₁ e₂).condErrProb W k l ≤ ∑ k, ∑ l, L (e₁ k) (e₂ l) :=
          sum_le_sum fun k _ => sum_le_sum fun l _ => c.condErrProb_restrict_le hW e₁ e₂ k l
      _ = ∑ i ∈ t₁, ∑ j ∈ t₂, L i j := by
          rw [← sum_orderEmbOfFin t₁ ht₁ (fun i => ∑ j ∈ t₂, L i j)]
          refine sum_congr rfl fun k _ => ?_
          exact sum_orderEmbOfFin t₂ ht₂ (fun j => L (e₁ k) j)
  have hswap : ∑ i ∈ t₁, ∑ j ∈ t₂, L i j = ∑ j ∈ t₂, ∑ i ∈ t₁, L i j := sum_comm
  have hswap' : ∑ j, ∑ i ∈ t₁, L i j = ∑ i ∈ t₁, ∑ j, L i j := sum_comm
  rw [hswap'] at hs₂
  have hM₁' : (0 : ℝ) < M₁' := by exact_mod_cast h₁
  have hM₂' : (0 : ℝ) < M₂' := by exact_mod_cast h₂
  have hM₁r : (M₁' : ℝ) ≤ M₁ := by exact_mod_cast hM₁
  have hM₂r : (M₂' : ℝ) ≤ M₂ := by exact_mod_cast hM₂
  have hM₁0 : (0 : ℝ) < M₁ := hM₁'.trans_le hM₁r
  have hM₂0 : (0 : ℝ) < M₂ := hM₂'.trans_le hM₂r
  unfold avgErrProb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [hswap] at hle
  set X := ∑ j ∈ t₂, ∑ i ∈ t₁, L i j
  set Y := ∑ i ∈ t₁, ∑ j, L i j
  set Z := ∑ i, ∑ j, L i j
  calc (∑ k, ∑ l, (c.restrict e₁ e₂).condErrProb W k l) * (M₁ * M₂) ≤ X * (M₁ * M₂) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (X * M₂) * M₁ := by ring
    _ ≤ (Y * M₂') * M₁ := mul_le_mul_of_nonneg_right hs₂ (by positivity)
    _ = (Y * M₁) * M₂' := by ring
    _ ≤ (Z * M₁') * M₂' := mul_le_mul_of_nonneg_right hs₁ hM₂'.le
    _ = Z * (M₁' * M₂') := by ring

/-! ### Two codes one after the other -/

/-- The code sending the first components of the messages with `c` during the first `n` symbols
and the second components with `c'` during the last `n'` symbols. The messages of the new code
are pairs, numbered by `finProdFinEquiv`. -/
def append {M₁' M₂' n' : ℕ} (c' : MACCode M₁' M₂' n' α₁ α₂ β) :
    MACCode (M₁ * M₁') (M₂ * M₂') (n + n') α₁ α₂ β where
  enc₁ i := Fin.append (c.enc₁ (finProdFinEquiv.symm i).1) (c'.enc₁ (finProdFinEquiv.symm i).2)
  enc₂ j := Fin.append (c.enc₂ (finProdFinEquiv.symm j).1) (c'.enc₂ (finProdFinEquiv.symm j).2)
  dec y :=
    (finProdFinEquiv ((c.dec fun k => y (Fin.castAdd n' k)).1,
        (c'.dec fun k => y (Fin.natAdd n k)).1),
      finProdFinEquiv ((c.dec fun k => y (Fin.castAdd n' k)).2,
        (c'.dec fun k => y (Fin.natAdd n k)).2))

omit [Fintype β] in
lemma channelExt_append {n' : ℕ} (x : Fin n → α₁ × α₂) (x' : Fin n' → α₁ × α₂)
    (u : Fin n → β) (v : Fin n' → β) :
    channelExt W (n + n') (Fin.append x x') (Fin.append u v) =
      channelExt W n x u * channelExt W n' x' v := by
  simp only [channelExt, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

omit [Fintype β] in
lemma input_append {M₁' M₂' n' : ℕ} (c' : MACCode M₁' M₂' n' α₁ α₂ β) (i : Fin (M₁ * M₁'))
    (j : Fin (M₂ * M₂')) :
    (c.append c').input i j = Fin.append (c.input (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm j).1) (c'.input (finProdFinEquiv.symm i).2
      (finProdFinEquiv.symm j).2) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;>
    simp [input, append, zipSeq, Fin.append_left, Fin.append_right]

/-- The probability of error of two codes used one after the other is at most the sum of their
probabilities of error. -/
lemma condErrProb_append_le (hW : IsChannel W) {M₁' M₂' n' : ℕ}
    (c' : MACCode M₁' M₂' n' α₁ α₂ β) (i : Fin (M₁ * M₁')) (j : Fin (M₂ * M₂')) :
    (c.append c').condErrProb W i j ≤
      c.condErrProb W (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 +
        c'.condErrProb W (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  classical
  set i₁ := (finProdFinEquiv.symm i).1
  set i₂ := (finProdFinEquiv.symm i).2
  set j₁ := (finProdFinEquiv.symm j).1
  set j₂ := (finProdFinEquiv.symm j).2
  set P := channelExt W n (c.input i₁ j₁)
  set P' := channelExt W n' (c'.input i₂ j₂)
  have hP := (hW.ext n) (c.input i₁ j₁)
  have hP' := (hW.ext n') (c'.input i₂ j₂)
  have key : ∀ u v, (if (c.append c').dec (Fin.append u v) ≠ (i, j) then
      channelExt W (n + n') ((c.append c').input i j) (Fin.append u v) else 0) ≤
      P' v * (if c.dec u ≠ (i₁, j₁) then P u else 0) +
        P u * (if c'.dec v ≠ (i₂, j₂) then P' v else 0) := by
    intro u v
    rw [input_append, channelExt_append]
    have hu : (fun k => Fin.append u v (Fin.castAdd n' k)) = u :=
      funext fun k => Fin.append_left u v k
    have hv : (fun k => Fin.append u v (Fin.natAdd n k)) = v :=
      funext fun k => Fin.append_right u v k
    have h0 : 0 ≤ P u * P' v := mul_nonneg (hP.nonneg u) (hP'.nonneg v)
    by_cases h1 : c.dec u = (i₁, j₁)
    · by_cases h2 : c'.dec v = (i₂, j₂)
      · have : (c.append c').dec (Fin.append u v) = (i, j) := by
          simp only [append, hu, hv, h1, h2, i₁, i₂, j₁, j₂, Prod.mk.eta,
            Equiv.apply_symm_apply]
        simp only [this, h1, h2, ne_eq, not_true_eq_false, ↓reduceIte, mul_zero, add_zero,
          le_refl]
      · simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, mul_zero,
          zero_add]
        split_ifs <;> linarith
    · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte]
      have : 0 ≤ P u * (if c'.dec v = (i₂, j₂) then 0 else P' v) := by
        split_ifs
        · simp
        · exact h0
      split_ifs <;> nlinarith
  calc (c.append c').condErrProb W i j
      = ∑ uv : (Fin n → β) × (Fin n' → β), (if (c.append c').dec (Fin.appendEquiv n n' uv) ≠
          (i, j) then channelExt W (n + n') ((c.append c').input i j) (Fin.appendEquiv n n' uv)
          else 0) := (Equiv.sum_comp (Fin.appendEquiv n n') _).symm
    _ ≤ ∑ uv : (Fin n → β) × (Fin n' → β), (P' uv.2 * (if c.dec uv.1 ≠ (i₁, j₁) then P uv.1
          else 0) + P uv.1 * (if c'.dec uv.2 ≠ (i₂, j₂) then P' uv.2 else 0)) :=
        sum_le_sum fun uv _ => key uv.1 uv.2
    _ = c.condErrProb W i₁ j₁ + c'.condErrProb W i₂ j₂ := by
        rw [Fintype.sum_prod_type]
        simp only [sum_add_distrib]
        have e1 : ∀ u, ∑ v, P' v * (if c.dec u ≠ (i₁, j₁) then P u else 0) =
            if c.dec u ≠ (i₁, j₁) then P u else 0 := fun u => by
          rw [← sum_mul, hP'.sum_eq_one, one_mul]
        have e2 : ∑ u, ∑ v, P u * (if c'.dec v ≠ (i₂, j₂) then P' v else 0) =
            ∑ v, if c'.dec v ≠ (i₂, j₂) then P' v else 0 := by
          simp_rw [← mul_sum]
          rw [← sum_mul, hP.sum_eq_one, one_mul]
        rw [e2]
        simp only [e1]
        rfl

/-- **(Theorem 15.3.2)** The average probability of error of two codes used one after the other is
at most the sum of their average probabilities of error. -/
theorem avgErrProb_append_le (hW : IsChannel W) {M₁' M₂' n' : ℕ}
    (c' : MACCode M₁' M₂' n' α₁ α₂ β) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₁' : 0 < M₁')
    (h₂' : 0 < M₂') : (c.append c').avgErrProb W ≤ c.avgErrProb W + c'.avgErrProb W := by
  set L := c.condErrProb W
  set L' := c'.condErrProb W
  have hsum : ∑ i, ∑ j, (c.append c').condErrProb W i j ≤
      M₁' * M₂' * ∑ i, ∑ j, L i j + M₁ * M₂ * ∑ i, ∑ j, L' i j := by
    calc ∑ i, ∑ j, (c.append c').condErrProb W i j
        ≤ ∑ i : Fin (M₁ * M₁'), ∑ j : Fin (M₂ * M₂'),
            (L (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 +
              L' (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2) :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => c.condErrProb_append_le hW c' i j
      _ = ∑ p : Fin M₁ × Fin M₁', ∑ q : Fin M₂ × Fin M₂', (L p.1 q.1 + L' p.2 q.2) := by
          rw [← Equiv.sum_comp finProdFinEquiv]
          refine sum_congr rfl fun p _ => ?_
          rw [← Equiv.sum_comp finProdFinEquiv]
          simp
      _ = M₁' * M₂' * ∑ i, ∑ j, L i j + M₁ * M₂ * ∑ i, ∑ j, L' i j := by
          simp only [sum_add_distrib]
          have h' : ∑ p : Fin M₁ × Fin M₁', ∑ q : Fin M₂ × Fin M₂', L' p.2 q.2 =
              ∑ p : Fin M₁' × Fin M₁, ∑ q : Fin M₂' × Fin M₂, L' p.1 q.1 := by
            rw [← Equiv.sum_comp (Equiv.prodComm _ _)]
            refine sum_congr rfl fun p _ => ?_
            rw [← Equiv.sum_comp (Equiv.prodComm _ _)]
            rfl
          rw [h', sum_prod_sum_prod_fst, sum_prod_sum_prod_fst]
          simp
  have hM₁ : (0 : ℝ) < M₁ := by exact_mod_cast h₁
  have hM₂ : (0 : ℝ) < M₂ := by exact_mod_cast h₂
  have hM₁' : (0 : ℝ) < M₁' := by exact_mod_cast h₁'
  have hM₂' : (0 : ℝ) < M₂' := by exact_mod_cast h₂'
  unfold avgErrProb
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by push_cast; positivity)
    (by positivity)]
  push_cast
  calc (∑ i, ∑ j, (c.append c').condErrProb W i j) * (M₁ * M₂ * (M₁' * M₂'))
      ≤ (M₁' * M₂' * ∑ i, ∑ j, L i j + M₁ * M₂ * ∑ i, ∑ j, L' i j) * (M₁ * M₂ * (M₁' * M₂')) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = ((∑ i, ∑ j, L i j) * (M₁' * M₂') + M₁ * M₂ * ∑ i, ∑ j, L' i j) *
          (M₁ * M₁' * (M₂ * M₂')) := by ring

/-- Transport a code along an equality of block lengths. -/
def cast {n' : ℕ} (h : n = n') : MACCode M₁ M₂ n' α₁ α₂ β := h ▸ c

lemma avgErrProb_cast {n' : ℕ} (h : n = n') : (c.cast h).avgErrProb W = c.avgErrProb W := by
  subst h
  rfl

/-- A code always making the same guess. -/
def const [Nonempty α₁] [Nonempty α₂] (M₁ M₂ n : ℕ) [NeZero M₁] [NeZero M₂] :
    MACCode M₁ M₂ n α₁ α₂ β :=
  ⟨fun _ _ => Classical.arbitrary α₁, fun _ _ => Classical.arbitrary α₂, fun _ => (0, 0)⟩

end MACCode

/-! ### Achievable rates and the capacity region -/

/-- **Definition (Section 15.3).** A rate pair `(R₁, R₂)` (in nats) is achievable if there are
`((⌈e^{nR₁}⌉, ⌈e^{nR₂}⌉), n)` codes whose average probability of error tends to `0`. -/
def IsAchievableMAC (W : α₁ × α₂ → β → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, MACCode ⌈exp (n * R₁)⌉₊ ⌈exp (n * R₂)⌉₊ n α₁ α₂ β,
    Tendsto (fun n => (c n).avgErrProb W) atTop (𝓝 0)

/-- **Definition (Section 15.3).** The capacity region of the multiple-access channel is the
closure of the set of achievable rate pairs. -/
def macCapacityRegion (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableMAC W R.1 R.2}

/-- The rate pairs `R` such that `R - (δ, δ)` is achievable for every `δ > 0`. -/
def macSlackSet (W : α₁ × α₂ → β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∀ δ > 0, IsAchievableMAC W (R.1 - δ) (R.2 - δ)}

variable {W : α₁ × α₂ → β → ℝ}

/-- To prove that a rate pair is achievable, it suffices to find codes for all large `n`, with
error probabilities bounded by a sequence tending to `0`. -/
lemma isAchievableMAC_of_forall_ge [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W)
    {R₁ R₂ : ℝ} {P : ℕ → ℝ} (hP : Tendsto P atTop (𝓝 0)) (N : ℕ)
    (h : ∀ n ≥ N, ∃ c : MACCode ⌈exp (n * R₁)⌉₊ ⌈exp (n * R₂)⌉₊ n α₁ α₂ β,
      c.avgErrProb W ≤ P n) : IsAchievableMAC W R₁ R₂ := by
  have hz : ∀ n : ℕ, NeZero ⌈exp (n * R₁)⌉₊ ∧ NeZero ⌈exp (n * R₂)⌉₊ := fun n =>
    ⟨⟨Nat.one_le_iff_ne_zero.1 (one_le_ceil_exp _)⟩, ⟨Nat.one_le_iff_ne_zero.1 (one_le_ceil_exp _)⟩⟩
  let c : ∀ n : ℕ, MACCode ⌈exp (n * R₁)⌉₊ ⌈exp (n * R₂)⌉₊ n α₁ α₂ β := fun n =>
    if hn : N ≤ n then (h n hn).choose else
      have := (hz n).1
      have := (hz n).2
      MACCode.const _ _ n
  refine ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hP
    (Eventually.of_forall fun n => (c n).avgErrProb_nonneg hW) ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [c, hn, ↓reduceDIte]
  exact (h n hn).choose_spec

/-- Lower rates are achievable. -/
theorem IsAchievableMAC.mono [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) {R₁ R₂ R₁' R₂' : ℝ}
    (h : IsAchievableMAC W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) :
    IsAchievableMAC W R₁' R₂' := by
  obtain ⟨c, hc⟩ := h
  refine isAchievableMAC_of_forall_ge hW hc 0 fun n _ => ?_
  have hle : ∀ {a b : ℝ}, a ≤ b → ⌈exp (n * a)⌉₊ ≤ ⌈exp (n * b)⌉₊ := fun hab =>
    Nat.ceil_mono (exp_le_exp.2 (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)))
  exact (c n).exists_avgErrProb_le_of_le hW (one_le_ceil_exp _) (one_le_ceil_exp _) (hle h₁)
    (hle h₂)

lemma IsAchievableMAC.mem_macSlackSet [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W)
    {R : ℝ × ℝ} (h : IsAchievableMAC W R.1 R.2) : R ∈ macSlackSet W :=
  fun δ hδ => h.mono hW (by linarith) (by linarith)

theorem macSlackSet_subset_macCapacityRegion : macSlackSet W ⊆ macCapacityRegion W := by
  intro R hR
  have hlim : Tendsto (fun k : ℕ => (R.1 - 1 / ((k : ℝ) + 1), R.2 - 1 / ((k : ℝ) + 1))) atTop
      (𝓝 R) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Tendsto (fun k : ℕ => R.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.1 - 0)) :=
      tendsto_const_nhds.sub h
    have h2 : Tendsto (fun k : ℕ => R.2 - 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.2 - 0)) :=
      tendsto_const_nhds.sub h
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k => hR _ (by positivity))

lemma ceil_exp_le_mul {x y z : ℝ} (h : x ≤ y + z) : ⌈exp x⌉₊ ≤ ⌈exp y⌉₊ * ⌈exp z⌉₊ := by
  refine Nat.ceil_le.2 ?_
  push_cast
  calc exp x ≤ exp y * exp z := by rw [← exp_add]; exact exp_le_exp.2 h
    _ ≤ _ := mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (exp_pos _).le (Nat.cast_nonneg _)

/-- The rounding of time sharing: with `x = ⌊t y⌋`, the rate `t r + (1 - t) r' - δ` fits in
`x (r - δ/2) + (y - x) (r' - δ/2)` once `y δ ≥ 2 |r - r'|`. -/
lemma time_sharing_bound {t r r' δ x y : ℝ} (hx : x ≤ t * y) (hx' : t * y < x + 1)
    (hy : 2 * |r - r'| ≤ y * δ) :
    y * (t * r + (1 - t) * r' - δ) ≤ x * (r - δ / 2) + (y - x) * (r' - δ / 2) := by
  have h1 : -|r - r'| ≤ (x - t * y) * (r - r') := by
    have : |(x - t * y) * (r - r')| ≤ |r - r'| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨by linarith, by linarith⟩)
    linarith [neg_abs_le ((x - t * y) * (r - r'))]
  linear_combination h1 + hy / 2

/-- **Theorem 15.3.2 (Convexity of the capacity region, time sharing).** If `R` and `R'` are
achievable up to an arbitrarily small loss, so is every convex combination `λR + (1 - λ)R'`: use
a code of rate `R` for the first `⌊λn⌋` symbols and a code of rate `R'` for the others. -/
theorem convex_macSlackSet [Nonempty α₁] [Nonempty α₂] (hW : IsChannel W) :
    Convex ℝ (macSlackSet W) := by
  rw [convex_iff_forall_pos]
  intro R hR R' hR' a b ha hb hab δ hδ
  obtain ⟨ca, hca⟩ := hR (δ / 2) (by positivity)
  obtain ⟨cb, hcb⟩ := hR' (δ / 2) (by positivity)
  have hb' : b = 1 - a := by linarith
  subst hb'
  set n₁ : ℕ → ℕ := fun n => ⌊a * n⌋₊
  have hn₁ : ∀ n : ℕ, (n₁ n : ℝ) ≤ a * n := fun n => Nat.floor_le (by positivity)
  have hn₁' : ∀ n : ℕ, a * n < n₁ n + 1 := fun n => Nat.lt_floor_add_one _
  have hn₁n : ∀ n : ℕ, n₁ n ≤ n := fun n => by
    have : (n₁ n : ℝ) ≤ n := (hn₁ n).trans (mul_le_of_le_one_left (Nat.cast_nonneg n) (by linarith))
    exact_mod_cast this
  set P : ℕ → ℝ := fun n => (ca (n₁ n)).avgErrProb W + (cb (n - n₁ n)).avgErrProb W
  have hP : Tendsto P atTop (𝓝 0) := by
    have h1 : Tendsto n₁ atTop atTop :=
      tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
    have h2 : Tendsto (fun n => n - n₁ n) atTop atTop := by
      rw [← tendsto_natCast_atTop_iff (R := ℝ)]
      refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop.const_mul_atTop hb)
      rw [Nat.cast_sub (hn₁n n)]
      linarith [hn₁ n]
    simpa using (hca.comp h1).add (hcb.comp h2)
  set N := ⌈2 * (|R.1 - R'.1| + |R.2 - R'.2|) / δ⌉₊
  refine isAchievableMAC_of_forall_ge hW hP N fun n hn => ?_
  have hnδ : 2 * (|R.1 - R'.1| + |R.2 - R'.2|) ≤ n * δ := by
    have : 2 * (|R.1 - R'.1| + |R.2 - R'.2|) / δ ≤ n := (Nat.ceil_le.1 hn)
    rwa [div_le_iff₀ hδ] at this
  have habs₁ := abs_nonneg (R.1 - R'.1)
  have habs₂ := abs_nonneg (R.2 - R'.2)
  have hcast : ((n - n₁ n : ℕ) : ℝ) = n - n₁ n := Nat.cast_sub (hn₁n n)
  have hmsg : ∀ r r' : ℝ, 2 * |r - r'| ≤ n * δ →
      ⌈exp (n * (a * r + (1 - a) * r' - δ))⌉₊ ≤
        ⌈exp (n₁ n * (r - δ / 2))⌉₊ * ⌈exp ((n - n₁ n : ℕ) * (r' - δ / 2))⌉₊ := by
    intro r r' hrr
    refine ceil_exp_le_mul ?_
    rw [hcast]
    exact time_sharing_bound (hn₁ n) (hn₁' n) hrr
  let c₀ := ((ca (n₁ n)).append (cb (n - n₁ n))).cast (Nat.add_sub_cancel' (hn₁n n))
  have hm₁ := hmsg R.1 R'.1 (by linarith)
  have hm₂ := hmsg R.2 R'.2 (by linarith)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  obtain ⟨c', hc'⟩ := c₀.exists_avgErrProb_le_of_le hW (one_le_ceil_exp _) (one_le_ceil_exp _)
    hm₁ hm₂
  refine ⟨c', hc'.trans ?_⟩
  rw [MACCode.avgErrProb_cast]
  exact (ca (n₁ n)).avgErrProb_append_le hW _ (one_le_ceil_exp _) (one_le_ceil_exp _)
    (one_le_ceil_exp _) (one_le_ceil_exp _)

end InfoTheory
