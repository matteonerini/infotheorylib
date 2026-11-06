/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.Statistics.Bernoulli

/-!
# The sender's queue under random data arrival

The queue of Lecture 24 of El Gamal and Kim. In each slot a packet of `k` bits arrives with
probability `p`, independently of the other slots, so that the arrival rate is `λ = p k`. At the
beginning of each transmission block of `n` slots the sender removes `s = nR` bits, if the queue
holds that many.

Slots are numbered from `0`, so block `j` starts at slot `j n`.

The notes prove the sufficiency in Lemma 1 by a Foster–Lyapunov drift bound on the Cesàro means,
followed by the convergence of the positive recurrent aperiodic chain. That last step fails for
`p = 1`, where the chain can be periodic (`queueMean_not_tendsto`). Here the drift is applied to a
monotone chain dominating the queue. The mean of a monotone chain started at `0` is nondecreasing,
so the bound on the Cesàro means bounds the means themselves, for every `p`, without any ergodic
theory.

## Main definitions

* `queueOf n s A t`: the backlog at slot `t` for the arrival amounts `A`.
* `queueExp p k n s N g`: the expectation of `g (Q(N))`.
* `queueMean p k n s N`: the mean backlog `E Q(N)`.
* `QueueStable p k n s`: the backlog has bounded mean.
* `queueLowProb p k n s j`: the probability that the queue holds fewer than `s` bits at the
  beginning of block `j`, which is `p_j` in the notes.

## Main statements

* `queueStable_of_lt`, `le_of_queueStable`: **Lemma 1 of Lecture 24**, for a block of `s` bits.
* `queueMean_iterate_le`: the bound `E Q(j n) ≤ C / (s - n λ)` with `C = 4 s² + (n k + s)²`.
* `queue_tail_le`: a stable queue rarely exceeds a large buffer.
* `exists_one_sub_queueLowProb_ge`: a stable queue is served in some block with probability at
  least `n λ / (2 s)`. The converse of Theorem 1 needs this.
* `queueMean_not_tendsto`: for `p = 1` the mean backlog of a stable queue need not converge.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24.
-/

@[expose] public noncomputable section

open Finset Filter Topology

namespace InfoTheory

/-! ### The transition law -/

/-- The backlog after the sender asks for `s` bits: they are removed if the queue holds them. -/
def queueServe (s q : ℝ) : ℝ := if s ≤ q then q - s else q

/-- **The transition law of Lecture 24.** The backlog `Q(t)` at slot `t`: at the beginning of a
block the sender asks for `s` bits, and at the end of each slot the arrival `A t` joins the
queue. -/
def queueOf (n : ℕ) (s : ℝ) (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (if n ∣ t then queueServe s (queueOf n s A t) else queueOf n s A t) + A t

lemma queueServe_nonneg {s q : ℝ} (hq : 0 ≤ q) : 0 ≤ queueServe s q := by
  unfold queueServe
  split_ifs with h <;> linarith

lemma queueServe_le {s q : ℝ} (hs : 0 ≤ s) : queueServe s q ≤ q := by
  unfold queueServe
  split_ifs <;> linarith

lemma sub_le_queueServe {s q : ℝ} (hs : 0 ≤ s) : q - s ≤ queueServe s q := by
  unfold queueServe
  split_ifs <;> linarith

lemma queueOf_congr {n : ℕ} {s : ℝ} {A A' : ℕ → ℝ} {N : ℕ} (h : ∀ t < N, A t = A' t) :
    queueOf n s A N = queueOf n s A' N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [queueOf]
    rw [ih fun t ht => h t (by omega), h N (by omega)]

lemma queueOf_nonneg {n : ℕ} {s : ℝ} {A : ℕ → ℝ} (hA : ∀ t, 0 ≤ A t) (t : ℕ) :
    0 ≤ queueOf n s A t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    simp only [queueOf]
    split_ifs
    · exact add_nonneg (queueServe_nonneg ih) (hA t)
    · exact add_nonneg ih (hA t)

/-- During a block the backlog only grows by the arrivals, of at most `K` bits per slot. -/
lemma queueOf_add_le {n : ℕ} {s K : ℝ} {A : ℕ → ℝ} (hs : 0 ≤ s) (hA : ∀ t, A t ≤ K) (m r : ℕ) :
    queueOf n s A (m + r) ≤ queueOf n s A m + r * K := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← add_assoc]
    simp only [queueOf]
    have h1 : (if n ∣ m + r then queueServe s (queueOf n s A (m + r)) else
        queueOf n s A (m + r)) ≤ queueOf n s A (m + r) := by
      split_ifs
      · exact queueServe_le hs
      · exact le_rfl
    have := hA (m + r)
    push_cast
    linarith

/-- The backlog over a block: the sender is served once, at its first slot. -/
lemma queueOf_block {n : ℕ} {s : ℝ} (A : ℕ → ℝ) {m : ℕ} (hm : n ∣ m) {r : ℕ} (hr : 1 ≤ r)
    (hrn : r ≤ n) :
    queueOf n s A (m + r) = queueServe s (queueOf n s A m) + ∑ i ∈ range r, A (m + i) := by
  induction r, hr using Nat.le_induction with
  | base =>
    simp [queueOf, hm]
  | succ r hr ih =>
    rw [← add_assoc]
    simp only [queueOf]
    have hnd : ¬ n ∣ m + r := by
      intro h
      have h' : n ∣ r := (Nat.dvd_add_right hm).1 h
      have := Nat.le_of_dvd (by omega) h'
      omega
    simp only [hnd, ite_false]
    rw [ih (by omega), sum_range_succ]
    ring

/-! ### The drift argument for an abstract block arrival -/

section Drift

variable {X : Type*} [Fintype X]

/-- The Markov operator of the queue at the block level: `g` is sent to
`q ↦ E g(serve(q) + Ã)`. -/
def serveOp (μ : X → ℝ) (a : X → ℝ) (s : ℝ) (g : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∑ x, μ x * g (queueServe s q + a x)

/-- The Markov operator of the monotone chain `W ↦ max(W - 2s, 0) + Ã + s`, which dominates the
queue. -/
def domOp (μ : X → ℝ) (a : X → ℝ) (s : ℝ) (g : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∑ x, μ x * g (max (q - 2 * s) 0 + a x + s)

variable {μ : X → ℝ} {a : X → ℝ} {s : ℝ}

lemma domOp_mono (hμ : IsPMF μ) {g h : ℝ → ℝ} (ha : ∀ x, 0 ≤ a x) (hs : 0 ≤ s)
    (hgh : ∀ q, 0 ≤ q → g q ≤ h q) (q : ℝ) :
    domOp μ a s g q ≤ domOp μ a s h q := by
  refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hgh _ ?_) (hμ.nonneg x)
  have := le_max_right (q - 2 * s) 0
  have := ha x
  linarith

lemma domOp_iterate_mono (hμ : IsPMF μ) {g h : ℝ → ℝ} (ha : ∀ x, 0 ≤ a x) (hs : 0 ≤ s)
    (hgh : ∀ q, 0 ≤ q → g q ≤ h q) (j : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (domOp μ a s)^[j] g q ≤ (domOp μ a s)^[j] h q := by
  induction j generalizing q with
  | zero => exact hgh q hq
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    exact domOp_mono hμ ha hs (fun q' hq' => ih hq') q

/-- The iterates of the operator send functions monotone on `[0, ∞)` to such functions. -/
lemma domOp_iterate_monotoneOn (hμ : IsPMF μ) {g : ℝ → ℝ} (ha : ∀ x, 0 ≤ a x) (hs : 0 ≤ s)
    (hg : ∀ q q', 0 ≤ q → q ≤ q' → g q ≤ g q') (j : ℕ) :
    ∀ q q', 0 ≤ q → q ≤ q' → (domOp μ a s)^[j] g q ≤ (domOp μ a s)^[j] g q' := by
  induction j with
  | zero => exact hg
  | succ j ih =>
    intro q q' hq hqq'
    simp only [Function.iterate_succ_apply']
    refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ih _ _ ?_ ?_) (hμ.nonneg x)
    · have := le_max_right (q - 2 * s) 0
      have := ha x
      linarith
    · have : max (q - 2 * s) 0 ≤ max (q' - 2 * s) 0 := max_le_max (by linarith) le_rfl
      linarith

/-- The operator is affine. -/
lemma domOp_affine (hμ : IsPMF μ) (g h : ℝ → ℝ) (c e q : ℝ) :
    domOp μ a s (fun q => g q + c - e * h q) q =
      domOp μ a s g q + c - e * domOp μ a s h q := by
  unfold domOp
  have h1 : ∑ x, μ x * (g (max (q - 2 * s) 0 + a x + s) + c - e * h (max (q - 2 * s) 0 + a x + s)) =
      ∑ x, (μ x * g (max (q - 2 * s) 0 + a x + s) + μ x * c -
        e * (μ x * h (max (q - 2 * s) 0 + a x + s))) :=
    sum_congr rfl fun x _ => by ring
  rw [h1, sum_sub_distrib, sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul, mul_sum]

lemma domOp_iterate_affine (hμ : IsPMF μ) (g h : ℝ → ℝ) (c e : ℝ) (j : ℕ) (q : ℝ) :
    (domOp μ a s)^[j] (fun q => g q + c - e * h q) q =
      (domOp μ a s)^[j] g q + c - e * (domOp μ a s)^[j] h q := by
  induction j generalizing q with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    have : (domOp μ a s)^[j] (fun q => g q + c - e * h q) =
        fun q => (domOp μ a s)^[j] g q + c - e * (domOp μ a s)^[j] h q := funext ih
    rw [this, domOp_affine hμ]

/-- **The one-step drift**, as on p. 24-32 of the notes. -/
lemma domOp_sq_le (hμ : IsPMF μ) (ha : ∀ x, 0 ≤ a x) {A : ℝ} (hA : ∀ x, a x ≤ A) (hs : 0 ≤ s)
    {q : ℝ} (hq : 0 ≤ q) :
    domOp μ a s (fun q => q ^ 2) q ≤
      q ^ 2 + (4 * s ^ 2 + (A + s) ^ 2) - 2 * (s - ∑ x, μ x * a x) * q := by
  have hpt : ∀ x, (max (q - 2 * s) 0 + a x + s) ^ 2 ≤
      q ^ 2 + (4 * s ^ 2 + (A + s) ^ 2) - 2 * s * q + 2 * q * a x := by
    intro x
    have hax := ha x
    have hAx := hA x
    have hsq : (a x + s) ^ 2 ≤ (A + s) ^ 2 := by nlinarith
    rcases le_total (q - 2 * s) 0 with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg hq hax, mul_nonneg hq hs]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg hq hax, mul_nonneg hs hax]
  calc domOp μ a s (fun q => q ^ 2) q
      ≤ ∑ x, μ x * (q ^ 2 + (4 * s ^ 2 + (A + s) ^ 2) - 2 * s * q + 2 * q * a x) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hμ.nonneg x)
    _ = q ^ 2 + (4 * s ^ 2 + (A + s) ^ 2) - 2 * (s - ∑ x, μ x * a x) * q := by
        have h1 : ∑ x, μ x * (q ^ 2 + (4 * s ^ 2 + (A + s) ^ 2) - 2 * s * q + 2 * q * a x) =
            (q ^ 2 + (4 * s ^ 2 + (A + s) ^ 2) - 2 * s * q) * ∑ x, μ x +
              2 * q * ∑ x, μ x * a x := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun x _ => by ring
        rw [h1, hμ.sum_eq_one]
        ring

/-- The drift inequality for the iterates, which are expectations of functions of the chain. -/
lemma domOp_iterate_drift (hμ : IsPMF μ) (ha : ∀ x, 0 ≤ a x) {A : ℝ} (hA : ∀ x, a x ≤ A)
    (hs : 0 ≤ s) (j : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (domOp μ a s)^[j + 1] (fun q => q ^ 2) q ≤
      (domOp μ a s)^[j] (fun q => q ^ 2) q + (4 * s ^ 2 + (A + s) ^ 2) -
        (2 * (s - ∑ x, μ x * a x)) * (domOp μ a s)^[j] (fun q => q) q := by
  rw [Function.iterate_succ_apply, ← domOp_iterate_affine hμ]
  refine domOp_iterate_mono hμ ha hs (fun q' hq' => ?_) j hq
  exact domOp_sq_le hμ ha hA hs hq'

lemma domOp_iterate_nonneg (hμ : IsPMF μ) {g : ℝ → ℝ} (ha : ∀ x, 0 ≤ a x) (hs : 0 ≤ s)
    (hg : ∀ q, 0 ≤ q → 0 ≤ g q) (j : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ (domOp μ a s)^[j] g q := by
  induction j generalizing q with
  | zero => exact hg q hq
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    refine sum_nonneg fun x _ => mul_nonneg (hμ.nonneg x) (ih ?_)
    have := le_max_right (q - 2 * s) 0
    have := ha x
    linarith

/-- The mean of the monotone chain started at `0` is nondecreasing. -/
lemma domOp_iterate_le_succ (hμ : IsPMF μ) (ha : ∀ x, 0 ≤ a x) (hs : 0 ≤ s) (j : ℕ) :
    (domOp μ a s)^[j] (fun q => q) 0 ≤ (domOp μ a s)^[j + 1] (fun q => q) 0 := by
  rw [Function.iterate_succ_apply']
  have hmono := domOp_iterate_monotoneOn hμ ha hs (g := fun q => q) (fun _ _ _ h => h) j
  calc (domOp μ a s)^[j] (fun q => q) 0
      = ∑ x, μ x * (domOp μ a s)^[j] (fun q => q) 0 := by
        rw [← sum_mul, hμ.sum_eq_one, one_mul]
    _ ≤ _ := sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hmono _ _ le_rfl (by
        have := le_max_right ((0 : ℝ) - 2 * s) 0
        have := ha x
        linarith)) (hμ.nonneg x)

/-- **The Foster–Lyapunov bound.** The mean of the monotone chain is at most
`(4 s² + (A + s)²) / δ`, for the negative drift `δ = s - E Ã`. -/
lemma domOp_iterate_mean_le (hμ : IsPMF μ) (ha : ∀ x, 0 ≤ a x) {A : ℝ} (hA : ∀ x, a x ≤ A)
    (hs : 0 ≤ s) (hδ : 0 < s - ∑ x, μ x * a x) (j : ℕ) :
    (s - ∑ x, μ x * a x) * (domOp μ a s)^[j] (fun q => q) 0 ≤ 4 * s ^ 2 + (A + s) ^ 2 := by
  set δ := s - ∑ x, μ x * a x
  set C := 4 * s ^ 2 + (A + s) ^ 2
  set v : ℕ → ℝ := fun i => (domOp μ a s)^[i] (fun q => q) 0 with hv
  set u : ℕ → ℝ := fun i => (domOp μ a s)^[i] (fun q => q ^ 2) 0 with hu
  have hC : 0 ≤ C := by positivity
  -- Telescoping the drift.
  have hsum : ∀ b : ℕ, 2 * δ * ∑ i ∈ range b, v i ≤ b * C - u b := by
    intro b
    induction b with
    | zero => simp [hu]
    | succ b ih =>
      have h := domOp_iterate_drift hμ ha hA hs b (q := 0) le_rfl
      rw [sum_range_succ, mul_add]
      push_cast
      have h' : u (b + 1) ≤ u b + C - 2 * δ * v b := h
      nlinarith
  have hun : ∀ b, 0 ≤ u b := fun b =>
    domOp_iterate_nonneg hμ ha hs (fun q _ => sq_nonneg q) b le_rfl
  have hvn : ∀ b, 0 ≤ v b := fun b =>
    domOp_iterate_nonneg hμ ha hs (fun q hq => hq) b le_rfl
  have hmono : Monotone v := monotone_nat_of_le_succ fun i => domOp_iterate_le_succ hμ ha hs i
  -- The mean at `j` is at most the average over `j, …, 2j`.
  have hlow : ((j : ℝ) + 1) * v j ≤ ∑ i ∈ range (2 * j + 1), v i := by
    calc ((j : ℝ) + 1) * v j = ∑ _i ∈ Ico j (2 * j + 1), v j := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
          congr 1
          have : 2 * j + 1 - j = j + 1 := by omega
          rw [this]
          push_cast
          ring
      _ ≤ ∑ i ∈ Ico j (2 * j + 1), v i := sum_le_sum fun i hi => hmono (mem_Ico.1 hi).1
      _ ≤ ∑ i ∈ range (2 * j + 1), v i :=
          sum_le_sum_of_subset_of_nonneg (fun i hi => mem_range.2 (mem_Ico.1 hi).2)
            fun i _ _ => hvn i
  have h2 := hsum (2 * j + 1)
  have h3 := hun (2 * j + 1)
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h4 : 2 * δ * (((j : ℝ) + 1) * v j) ≤ (2 * (j : ℝ) + 1) * C := by
    calc 2 * δ * (((j : ℝ) + 1) * v j) ≤ 2 * δ * ∑ i ∈ range (2 * j + 1), v i :=
          mul_le_mul_of_nonneg_left hlow (by linarith)
      _ ≤ ((2 * j + 1 : ℕ) : ℝ) * C - u (2 * j + 1) := h2
      _ ≤ (2 * (j : ℝ) + 1) * C := by push_cast; linarith
  have h5 : ((j : ℝ) + 1) * (δ * v j) ≤ ((j : ℝ) + 1) * C := by nlinarith
  exact le_of_mul_le_mul_left h5 hj

/-- The queue is dominated by the monotone chain. -/
lemma serveOp_iterate_le_domOp (hμ : IsPMF μ) (ha : ∀ x, 0 ≤ a x) (hs : 0 ≤ s) (j : ℕ) {q : ℝ}
    (hq : 0 ≤ q) :
    (serveOp μ a s)^[j] (fun q => q) q ≤ (domOp μ a s)^[j] (fun q => q) q := by
  induction j generalizing q with
  | zero => exact le_rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hμ.nonneg x)
    have hax := ha x
    have h0 : 0 ≤ queueServe s q + a x := add_nonneg (queueServe_nonneg hq) hax
    refine (ih h0).trans (domOp_iterate_monotoneOn hμ ha hs (g := fun q => q)
      (fun _ _ _ h => h) j _ _ h0 ?_)
    have : queueServe s q ≤ max (q - 2 * s) 0 + s := by
      unfold queueServe
      split_ifs with h
      · have := le_max_left (q - 2 * s) 0
        linarith
      · have := le_max_right (q - 2 * s) 0
        linarith
    linarith

end Drift

/-! ### The expectation under i.i.d. arrivals -/

section Append

variable {α : Type*} [Fintype α]

/-- Splitting a block of an i.i.d. sequence. -/
lemma sum_iidPMF_finAppend (q : α → ℝ) (m n : ℕ) (F : (Fin (m + n) → α) → ℝ) :
    ∑ a, iidPMF q (m + n) a * F a =
      ∑ a : Fin m → α, iidPMF q m a * ∑ b : Fin n → α, iidPMF q n b * F (Fin.append a b) := by
  rw [← (Fin.appendEquiv m n).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  have : iidPMF q (m + n) ((Fin.appendEquiv m n) (a, b)) = iidPMF q m a * iidPMF q n b := by
    simp [iidPMF, Fin.prod_univ_add, Fin.appendEquiv]
  rw [this]
  simp [Fin.appendEquiv, mul_assoc]

end Append

/-- The number of bits arriving in a slot: `k` if a packet arrives. -/
def arrivalAmt (k : ℕ) (b : Bool) : ℝ := if b then k else 0

lemma arrivalAmt_nonneg (k : ℕ) (b : Bool) : 0 ≤ arrivalAmt k b := by
  unfold arrivalAmt
  split_ifs <;> simp

lemma arrivalAmt_le (k : ℕ) (b : Bool) : arrivalAmt k b ≤ k := by
  unfold arrivalAmt
  split_ifs <;> simp

/-- The arrival amounts of the slots `0, …, N - 1`, for the packet indicators `a`. -/
def arrivalSeq (k : ℕ) {N : ℕ} (a : Fin N → Bool) (t : ℕ) : ℝ :=
  if h : t < N then arrivalAmt k (a ⟨t, h⟩) else 0

lemma arrivalSeq_nonneg (k : ℕ) {N : ℕ} (a : Fin N → Bool) (t : ℕ) : 0 ≤ arrivalSeq k a t := by
  unfold arrivalSeq
  split_ifs
  · exact arrivalAmt_nonneg _ _
  · exact le_rfl

lemma arrivalSeq_le (k : ℕ) {N : ℕ} (a : Fin N → Bool) (t : ℕ) : arrivalSeq k a t ≤ k := by
  unfold arrivalSeq
  split_ifs
  · exact arrivalAmt_le _ _
  · positivity

/-- The expectation `E g(Q(N))`, for i.i.d. packet arrivals of `k` bits with probability `p`. -/
def queueExp (p : ℝ) (k n : ℕ) (s : ℝ) (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑ a : Fin N → Bool, iidPMF (bernoulliPMF p) N a * g (queueOf n s (arrivalSeq k a) N)

/-- The mean backlog `E Q(N)`. -/
def queueMean (p : ℝ) (k n : ℕ) (s : ℝ) (N : ℕ) : ℝ := queueExp p k n s N fun q => q

/-- **Definition (Lecture 24).** The queue is stable if `sup_i E Q(i) ≤ B` for some `B < ∞`. -/
def QueueStable (p : ℝ) (k n : ℕ) (s : ℝ) : Prop := ∃ B : ℝ, ∀ N, queueMean p k n s N ≤ B

/-- The total arrival in a block. -/
def blockArrival (k : ℕ) {n : ℕ} (b : Fin n → Bool) : ℝ := ∑ i, arrivalAmt k (b i)

/-- **`p_j` of Lecture 24.** The probability that the queue holds fewer than `s` bits at the
beginning of block `j`, numbered from `0`. -/
def queueLowProb (p : ℝ) (k n : ℕ) (s : ℝ) (j : ℕ) : ℝ :=
  queueExp p k n s (j * n) fun q => if q < s then 1 else 0

variable {p : ℝ} {k n : ℕ} {s : ℝ}

lemma iidPMF_bernoulli_isPMF (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) :
    IsPMF (iidPMF (bernoulliPMF p) n) :=
  iidPMF_isPMF (bernoulliPMF_isPMF h0 h1) n

lemma blockArrival_nonneg (b : Fin n → Bool) : 0 ≤ blockArrival k b :=
  sum_nonneg fun _ _ => arrivalAmt_nonneg _ _

lemma blockArrival_le (b : Fin n → Bool) : blockArrival k b ≤ n * k := by
  calc blockArrival k b ≤ ∑ _i : Fin n, (k : ℝ) := sum_le_sum fun _ _ => arrivalAmt_le _ _
    _ = n * k := by simp

/-- `E Ã = n λ`. -/
lemma sum_blockArrival (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∑ b : Fin n → Bool, iidPMF (bernoulliPMF p) n b * blockArrival k b = n * (p * k) := by
  have hq := bernoulliPMF_isPMF h0 h1
  unfold blockArrival
  simp only [mul_sum]
  rw [sum_comm]
  have : ∀ i : Fin n, ∑ b : Fin n → Bool, iidPMF (bernoulliPMF p) n b * arrivalAmt k (b i) =
      p * k := by
    intro i
    rw [sum_iidPMF_eval hq i]
    simp [bernoulliPMF, arrivalAmt]
  simp [this]

lemma arrivalSeq_append_left {m : ℕ} (a : Fin m → Bool) (b : Fin n → Bool) {t : ℕ} (ht : t < m) :
    arrivalSeq k (Fin.append a b) t = arrivalSeq k a t := by
  unfold arrivalSeq
  have h2 : t < m + n := by omega
  simp only [ht, h2, ↓reduceDIte]
  congr 1
  exact Fin.append_left a b ⟨t, ht⟩

lemma arrivalSeq_append_right {m : ℕ} (a : Fin m → Bool) (b : Fin n → Bool) (i : Fin n) :
    arrivalSeq k (Fin.append a b) (m + i) = arrivalAmt k (b i) := by
  unfold arrivalSeq
  have h2 : m + (i : ℕ) < m + n := by omega
  simp only [h2, ↓reduceDIte]
  congr 1
  exact Fin.append_right a b i

lemma queueOf_append_left {m : ℕ} (a : Fin m → Bool) (b : Fin n → Bool) :
    queueOf n s (arrivalSeq k (Fin.append a b)) m = queueOf n s (arrivalSeq k a) m :=
  queueOf_congr fun _ ht => arrivalSeq_append_left a b ht

/-- **The block transition.** Conditioning on the arrivals before a block. -/
lemma queueExp_add (hn : 0 < n) {m : ℕ} (hm : n ∣ m) (g : ℝ → ℝ) :
    queueExp p k n s (m + n) g =
      queueExp p k n s m (serveOp (iidPMF (bernoulliPMF p) n) (blockArrival k) s g) := by
  unfold queueExp
  rw [sum_iidPMF_finAppend]
  refine sum_congr rfl fun a _ => ?_
  congr 1
  refine sum_congr rfl fun b _ => ?_
  congr 2
  rw [queueOf_block _ hm hn le_rfl, queueOf_append_left]
  congr 1
  unfold blockArrival
  rw [← Fin.sum_univ_eq_sum_range (fun i => arrivalSeq k (Fin.append a b) (m + i))]
  exact sum_congr rfl fun i _ => arrivalSeq_append_right a b i

/-- The law of the queue at the beginning of block `j`, by iterating the block transition. -/
lemma queueExp_mul (hn : 0 < n) (j : ℕ) (g : ℝ → ℝ) :
    queueExp p k n s (j * n) g =
      (serveOp (iidPMF (bernoulliPMF p) n) (blockArrival k) s)^[j] g 0 := by
  induction j generalizing g with
  | zero =>
    simp [queueExp, iidPMF, queueOf]
  | succ j ih =>
    rw [Nat.succ_mul, queueExp_add hn (Dvd.intro_left j rfl), ih,
      Function.iterate_succ_apply]

/-- The mean backlog at slot `m + r` exceeds the one at slot `m` by at most `r k`. -/
lemma queueMean_add_le (h0 : 0 ≤ p) (h1 : p ≤ 1) (hs : 0 ≤ s) (m r : ℕ) :
    queueMean p k n s (m + r) ≤ queueMean p k n s m + r * k := by
  have hq := iidPMF_bernoulli_isPMF h0 h1
  unfold queueMean queueExp
  rw [sum_iidPMF_finAppend]
  have hsum : (∑ a : Fin m → Bool, iidPMF (bernoulliPMF p) m a *
      queueOf n s (arrivalSeq k a) m) + r * k = ∑ a : Fin m → Bool, iidPMF (bernoulliPMF p) m a *
      (queueOf n s (arrivalSeq k a) m + r * k) := by
    simp only [mul_add, sum_add_distrib]
    rw [← sum_mul, (hq m).sum_eq_one, one_mul]
  rw [hsum]
  refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((hq m).nonneg a)
  calc ∑ b : Fin r → Bool, iidPMF (bernoulliPMF p) r b *
        queueOf n s (arrivalSeq k (Fin.append a b)) (m + r)
      ≤ ∑ b : Fin r → Bool, iidPMF (bernoulliPMF p) r b *
          (queueOf n s (arrivalSeq k a) m + r * k) := by
        refine sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ ((hq r).nonneg b)
        have := queueOf_add_le (n := n) hs (arrivalSeq_le k (Fin.append a b)) m r
        rwa [queueOf_congr (A' := arrivalSeq k a) fun _ ht => arrivalSeq_append_left a b ht] at this
    _ = _ := by rw [← sum_mul, (hq r).sum_eq_one, one_mul]

/-! ### Lemma 1 -/

/-- **The bound of Lemma 1 at the beginning of the blocks.** If `n λ < s`, then
`E Q(j n) ≤ (4 s² + (n k + s)²) / (s - n λ)`. -/
theorem queueMean_iterate_le (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n) (hs : 0 ≤ s)
    (hl : n * (p * k) < s) (j : ℕ) :
    (s - n * (p * k)) * queueMean p k n s (j * n) ≤ 4 * s ^ 2 + (n * k + s) ^ 2 := by
  have hμ := iidPMF_bernoulli_isPMF h0 h1 n
  have hm := sum_blockArrival (k := k) (n := n) h0 h1
  have hδ : 0 < s - n * (p * k) := by linarith
  have h := domOp_iterate_mean_le hμ (a := blockArrival k) (s := s)
    (fun b => blockArrival_nonneg b) (fun b => blockArrival_le b) hs (by rw [hm]; exact hδ) j
  rw [hm] at h
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hδ.le) h
  unfold queueMean
  rw [queueExp_mul hn]
  exact serveOp_iterate_le_domOp hμ (fun b => blockArrival_nonneg b) hs j le_rfl

/-- **Lemma 1 of Lecture 24, sufficiency.** If `n λ < s`, the queue is stable. -/
theorem queueStable_of_lt (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n) (hl : n * (p * k) < s) :
    QueueStable p k n s := by
  have hl0 : 0 ≤ n * (p * (k : ℝ)) := by positivity
  have hs : 0 ≤ s := by linarith
  have hδ : 0 < s - n * (p * k) := by linarith
  refine ⟨(4 * s ^ 2 + (n * k + s) ^ 2) / (s - n * (p * k)) + n * k, fun N => ?_⟩
  have hN : N = (N / n) * n + N % n := (Nat.div_add_mod' N n).symm
  have hmod : ((N % n : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.mod_lt N hn).le
  have h2 := queueMean_add_le (k := k) (n := n) h0 h1 hs ((N / n) * n) (N % n)
  rw [← hN] at h2
  have h3 := queueMean_iterate_le (k := k) h0 h1 hn hs hl (N / n)
  have h4 : queueMean p k n s ((N / n) * n) ≤ (4 * s ^ 2 + (n * k + s) ^ 2) / (s - n * (p * k)) :=
    (le_div_iff₀' hδ).2 h3
  have h5 : ((N % n : ℕ) : ℝ) * k ≤ n * k := mul_le_mul_of_nonneg_right hmod (by positivity)
  linarith

/-- The exact balance of a block: `E Q̃_{j+1} = E Q̃_j - s (1 - p_j) + n λ`. -/
lemma queueMean_succ (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n) (j : ℕ) :
    queueMean p k n s ((j + 1) * n) =
      queueMean p k n s (j * n) - s * (1 - queueLowProb p k n s j) + n * (p * k) := by
  have hμ := iidPMF_bernoulli_isPMF h0 h1 n
  have hq := iidPMF_bernoulli_isPMF h0 h1 (j * n)
  have hm := sum_blockArrival (k := k) (n := n) h0 h1
  unfold queueMean queueLowProb
  rw [Nat.succ_mul, queueExp_add hn (Dvd.intro_left j rfl)]
  unfold queueExp
  have hone : (1 : ℝ) = ∑ a : Fin (j * n) → Bool, iidPMF (bernoulliPMF p) (j * n) a :=
    hq.sum_eq_one.symm
  have hc : n * (p * (k : ℝ)) = ∑ a : Fin (j * n) → Bool, iidPMF (bernoulliPMF p) (j * n) a *
      (n * (p * (k : ℝ))) := by
    rw [← sum_mul, hq.sum_eq_one, one_mul]
  rw [hc]
  nth_rw 1 [hone]
  rw [← sum_sub_distrib, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  set q := queueOf n s (arrivalSeq k a) (j * n)
  have hop : serveOp (iidPMF (bernoulliPMF p) n) (blockArrival k) s (fun q => q) q =
      queueServe s q + n * (p * k) := by
    unfold serveOp
    rw [← hm]
    simp only [mul_add, sum_add_distrib]
    rw [← sum_mul, hμ.sum_eq_one, one_mul]
  rw [hop]
  by_cases hsq : s ≤ q
  · simp only [queueServe, hsq, ite_true, not_lt.2 hsq, ite_false]
    ring
  · simp only [queueServe, hsq, ite_false, not_le.1 hsq, ite_true]
    ring

/-- **Lemma 1 of Lecture 24, necessity.** If the queue is stable, then `n λ ≤ s`. -/
theorem le_of_queueStable (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n) (hs : 0 ≤ s)
    (h : QueueStable p k n s) : n * (p * k) ≤ s := by
  obtain ⟨B, hB⟩ := h
  have hlow : ∀ j : ℕ, j * (n * (p * k) - s) ≤ queueMean p k n s (j * n) := by
    intro j
    induction j with
    | zero =>
      simp [queueMean, queueExp, queueOf, iidPMF]
    | succ j ih =>
      have hb : 0 ≤ queueLowProb p k n s j := by
        refine sum_nonneg fun a _ => mul_nonneg ((iidPMF_bernoulli_isPMF h0 h1 _).nonneg a) ?_
        dsimp only
        split_ifs <;> norm_num
      rw [queueMean_succ h0 h1 hn]
      push_cast
      nlinarith
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ := exists_nat_gt (B / (n * (p * k) - s))
  have hpos : 0 < n * (p * k) - s := by linarith
  have h3 := hlow j
  have h4 := hB (j * n)
  have h5 : B < j * (n * (p * k) - s) := (div_lt_iff₀ hpos).1 hj
  linarith

/-- **For the converse of Theorem 1.** If the queue is stable and `n λ > 0`, some block is served
with probability at least `n λ / (2 s)`. The fraction of served blocks balances the arrivals. -/
theorem exists_one_sub_queueLowProb_ge (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n) (hs : 0 < s)
    (hl : 0 < n * (p * (k : ℝ))) (h : QueueStable p k n s) :
    ∃ j, n * (p * k) / (2 * s) ≤ 1 - queueLowProb p k n s j := by
  obtain ⟨B, hB⟩ := h
  by_contra hcon
  push Not at hcon
  have hsum : ∀ b : ℕ, queueMean p k n s (b * n) ≥ b * (n * (p * k) / 2) := by
    intro b
    induction b with
    | zero =>
      simp [queueMean, queueExp, queueOf, iidPMF]
    | succ b ih =>
      rw [queueMean_succ h0 h1 hn]
      have h2 := hcon b
      have h3 : s * (1 - queueLowProb p k n s b) ≤ n * (p * k) / 2 := by
        have : s * (1 - queueLowProb p k n s b) ≤ s * (n * (p * k) / (2 * s)) :=
          mul_le_mul_of_nonneg_left h2.le hs.le
        have he : s * (n * (p * k) / (2 * s)) = n * (p * k) / 2 := by
          field_simp
        linarith
      push_cast
      nlinarith
  obtain ⟨b, hb⟩ := exists_nat_gt (B / (n * (p * k) / 2))
  have h5 : B < b * (n * (p * k) / 2) := (div_lt_iff₀ (by positivity)).1 hb
  have h6 := hsum b
  have h7 := hB (b * n)
  linarith

/-- **Lecture 24: finite buffers.** By Markov's inequality, a stable queue exceeds a buffer of size
`x` with probability at most `B / x`, so a finite buffer makes the probability of data loss as small
as desired, as the notes ask the reader to check. -/
theorem queue_tail_le (h0 : 0 ≤ p) (h1 : p ≤ 1) {B x : ℝ} (hx : 0 < x)
    (hB : ∀ N, queueMean p k n s N ≤ B) (N : ℕ) :
    queueExp p k n s N (fun q => if x ≤ q then 1 else 0) ≤ B / x := by
  rw [le_div_iff₀ hx]
  refine le_trans ?_ (hB N)
  unfold queueExp queueMean
  rw [sum_mul]
  refine sum_le_sum fun a _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ ((iidPMF_bernoulli_isPMF h0 h1 N).nonneg a)
  have hq : 0 ≤ queueOf n s (arrivalSeq k a) N := queueOf_nonneg (arrivalSeq_nonneg k a) N
  dsimp only
  split_ifs with h
  · linarith
  · linarith

/-! ### A periodic queue -/

/-- The deterministic queue with `n = 1`, `k = 1` and `s = 2` alternates between `1` and `2`. -/
lemma queueOf_periodic (t : ℕ) :
    queueOf 1 2 (fun _ => 1) (2 * t + 1) = 1 ∧ queueOf 1 2 (fun _ => 1) (2 * t + 2) = 2 := by
  have hstep : ∀ i, queueOf 1 2 (fun _ => 1) (i + 1) =
      queueServe 2 (queueOf 1 2 (fun _ => 1) i) + 1 := fun i => by simp [queueOf]
  have h1 : ∀ i, queueOf 1 2 (fun _ => 1) i = 1 → queueOf 1 2 (fun _ => 1) (i + 1) = 2 := by
    intro i hi
    rw [hstep, hi]
    norm_num [queueServe]
  have h2 : ∀ i, queueOf 1 2 (fun _ => 1) i = 2 → queueOf 1 2 (fun _ => 1) (i + 1) = 1 := by
    intro i hi
    rw [hstep, hi]
    norm_num [queueServe]
  induction t with
  | zero =>
    have h : queueOf 1 2 (fun _ => 1) 1 = 1 := by norm_num [queueOf, queueServe]
    exact ⟨h, h1 1 h⟩
  | succ t ih =>
    have h : queueOf 1 2 (fun _ => 1) (2 * (t + 1) + 1) = 1 := h2 _ ih.2
    exact ⟨h, h1 _ h⟩

/-- For `p = 1` the arrival sequence is deterministic. -/
lemma queueMean_one (k n : ℕ) (s : ℝ) (N : ℕ) :
    queueMean 1 k n s N = queueOf n s (fun t => if t < N then (k : ℝ) else 0) N := by
  classical
  unfold queueMean queueExp
  rw [sum_eq_single (fun _ => true)]
  · have : iidPMF (bernoulliPMF 1) N (fun _ => true) = 1 := by
      simp [iidPMF, bernoulliPMF]
    rw [this, one_mul]
    refine queueOf_congr fun t ht => ?_
    simp [arrivalSeq, ht, arrivalAmt]
  · intro a _ ha
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ true := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    have : iidPMF (bernoulliPMF 1) N a = 0 := by
      refine prod_eq_zero (mem_univ i) ?_
      simp [bernoulliPMF, hi]
    rw [this, zero_mul]
  · simp

/-- **The chain of the appendix of Lecture 24 can be periodic.** For `p = 1`, `k = 1`, `n = 1` and
`s = 2` we have `λ = 1 < 2`, so the queue is stable, but the mean backlog alternates between `1`
and `2` and has no limit. So the step "the chain is aperiodic and `E(Q̃_j)` converges" on p. 24-33
of the notes fails for `p = 1`, although `p ∈ (0, 1]` is allowed there. -/
theorem queueMean_not_tendsto :
    QueueStable 1 1 1 2 ∧ ¬ ∃ L, Tendsto (queueMean 1 1 1 2) atTop (𝓝 L) := by
  refine ⟨queueStable_of_lt (by norm_num) le_rfl (by norm_num) (by norm_num), ?_⟩
  rintro ⟨L, hL⟩
  have hval : ∀ N, queueMean 1 1 1 2 N = queueOf 1 2 (fun _ => 1) N := by
    intro N
    rw [queueMean_one]
    refine queueOf_congr fun t ht => ?_
    simp [ht]
  have h1 : Tendsto (fun t : ℕ => queueMean 1 1 1 2 (2 * t + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_mono (fun t => by change t ≤ 2 * t + 1; omega) tendsto_id)
  have h2 : Tendsto (fun t : ℕ => queueMean 1 1 1 2 (2 * t + 2)) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_mono (fun t => by change t ≤ 2 * t + 2; omega) tendsto_id)
  have e1 : (fun t : ℕ => queueMean 1 1 1 2 (2 * t + 1)) = fun _ => 1 :=
    funext fun t => by rw [hval, (queueOf_periodic t).1]
  have e2 : (fun t : ℕ => queueMean 1 1 1 2 (2 * t + 2)) = fun _ => 2 :=
    funext fun t => by rw [hval, (queueOf_periodic t).2]
  rw [e1] at h1
  rw [e2] at h2
  have h3 : (1 : ℝ) = 2 := (tendsto_const_nhds_iff.1 h1).trans (tendsto_const_nhds_iff.1 h2).symm
  norm_num at h3

end InfoTheory
