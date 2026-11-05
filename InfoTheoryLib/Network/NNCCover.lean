/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NNCLaw
public import InfoTheoryLib.Network.RelayCFCover

/-!
# Noisy network coding: covering at all the nodes

Each node `k` describes its received sequence by a sequence of a codebook drawn from `p(v_k | x_k)`.
We have to show that the sequences of all the nodes and the descriptions are jointly typical with
high probability. The notes use the Markov lemma, node by node.

## Main definitions

* `nncHyb σ Bad`: the probability of `Bad`, when each node `k` draws its sequence from the kernel
  `σ k`, given its input and output sequences. Only the kernels of the nodes change, so these are
  hybrids between the true conditional law and the codebooks.
* `nncB σ k Bad a b c`: the mass of `Bad` given the sequences of node `k`.
* `nncPick`: the index of a good sequence in a codebook.

## Main statements

* `nncHyb_update_le`: **one step of the hybrid argument**.

## Implementation notes

As in compress–forward, instead of the Markov lemma we use Markov's inequality. Fix the kernels of
the other nodes. The conditional mass of `Bad` given the sequences of node `k` is at most `δ` with
high probability, and node `k` looks for a sequence with that property in its codebook. Then the
next node does the same, for the new kernels. This avoids the conditional typicality lemma.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Hybrid

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {px : ∀ k, X k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

/-- The inputs at each time, from the sequences of the nodes. -/
def xAt (x : ∀ k, Fin n → X k) : Fin n → ∀ k, X k := fun i k => x k i

/-- The sequence received by a node. -/
def yOf (k : Fin N) (y : Fin n → ∀ k, Y k) : Fin n → Y k := fun i => y i k

/-- A kernel for each node, from its input and output sequences to its description sequence. -/
abbrev NNCKernels (n : ℕ) (X Y V : Fin N → Type*) :=
  ∀ k, (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → ℝ

/-- The joint law of the input and output sequences. -/
def nncXY (px : ∀ k, X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (x : ∀ k, Fin n → X k)
    (y : Fin n → ∀ k, Y k) : ℝ :=
  (∏ k, iidPMF (px k) n (x k)) * seqChan W n (xAt x) y

/-- The probability of `Bad`, when each node draws its sequence from its kernel. -/
def nncHyb (px : ∀ k, X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (σ : NNCKernels n X Y V)
    (Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop) : ℝ :=
  ∑ x, ∑ y, nncXY px W x y * ∑ v, (∏ k, σ k (x k) (yOf k y) (v k)) * ind (Bad x y v)

/-- The law of the input and output sequences of a node. -/
def nncR (px : ∀ k, X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (k : Fin N) (a : Fin n → X k)
    (b : Fin n → Y k) : ℝ :=
  ∑ x, ∑ y, ind (x k = a ∧ yOf k y = b) * nncXY px W x y

/-- The mass of `Bad`, given the sequences of node `k`. -/
def nncB (px : ∀ k, X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (σ : NNCKernels n X Y V) (k : Fin N)
    (Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop) (a : Fin n → X k)
    (b : Fin n → Y k) (c : Fin n → V k) : ℝ :=
  ∑ x, ∑ y, ind (x k = a ∧ yOf k y = b) * (nncXY px W x y * ∑ v, ind (v k = c) *
    ((∏ j ∈ univ.erase k, σ j (x j) (yOf j y) (v j)) * ind (Bad x y v)))

lemma nncXY_nonneg (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (x : ∀ k, Fin n → X k)
    (y : Fin n → ∀ k, Y k) : 0 ≤ nncXY px W x y :=
  mul_nonneg (prod_nonneg fun k _ => (iidPMF_isPMF (hpx k) n).nonneg _)
    ((seqChan_isChannel hW n _).nonneg _)

/-- The input and output sequences have total mass one. -/
lemma sum_nncXY (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) :
    ∑ x : ∀ k, Fin n → X k, ∑ y : Fin n → ∀ k, Y k, nncXY px W x y = 1 := by
  simp only [nncXY]
  simp_rw [← mul_sum, (seqChan_isChannel hW n _).sum_eq_one, mul_one]
  rw [sum_prod_pi]
  exact prod_eq_one fun k _ => (iidPMF_isPMF (hpx k) n).sum_eq_one

/-- Summing over the values of two functions. -/
lemma sum_match {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (p : c → a) (f : e → b) (G : a → b → c → e → ℝ) :
    ∑ u, ∑ w, ∑ x, ∑ y, ind (p x = u ∧ f y = w) * G u w x y = ∑ x, ∑ y, G (p x) (f y) x y := by
  classical
  calc _ = ∑ u, ∑ x, ∑ w, ∑ y, ind (p x = u ∧ f y = w) * G u w x y :=
        sum_congr rfl fun u _ => sum_comm
    _ = ∑ x, ∑ u, ∑ w, ∑ y, ind (p x = u ∧ f y = w) * G u w x y := sum_comm
    _ = ∑ x, ∑ u, ∑ y, ∑ w, ind (p x = u ∧ f y = w) * G u w x y :=
        sum_congr rfl fun x _ => sum_congr rfl fun u _ => sum_comm
    _ = ∑ x, ∑ y, ∑ u, ∑ w, ind (p x = u ∧ f y = w) * G u w x y :=
        sum_congr rfl fun x _ => sum_comm
    _ = _ := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        rw [Finset.sum_eq_single (p x), Finset.sum_eq_single (f y)]
        · rw [ind_of_pos ⟨rfl, rfl⟩, one_mul]
        · exact fun w _ hw => by rw [ind_of_neg fun h => hw h.2.symm, zero_mul]
        · simp
        · exact fun u _ hu => sum_eq_zero fun w _ => by
            rw [ind_of_neg fun h => hu h.1.symm, zero_mul]
        · simp

/-- The law of the sequences of a node has total mass one. -/
lemma sum_nncR (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (k : Fin N) :
    ∑ a : Fin n → X k, ∑ b : Fin n → Y k, nncR px W k a b = 1 := by
  have h := sum_match (fun x : ∀ k, Fin n → X k => x k) (yOf (n := n) (Y := Y) k)
    fun _ _ x y => nncXY px W x y
  simp only [nncR]
  rw [h]
  exact sum_nncXY hpx hW

lemma nncR_nonneg (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (k : Fin N) (a : Fin n → X k)
    (b : Fin n → Y k) : 0 ≤ nncR px W k a b :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (ind_nonneg _) (nncXY_nonneg hpx hW _ _)

variable {σ : NNCKernels n X Y V} {Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) →
  (∀ k, Fin n → V k) → Prop}

lemma nncB_nonneg (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W)
    (hσ : ∀ k a b, IsPMF (σ k a b)) (k : Fin N) (a : Fin n → X k) (b : Fin n → Y k)
    (c : Fin n → V k) : 0 ≤ nncB px W σ k Bad a b c :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (ind_nonneg _)
    (mul_nonneg (nncXY_nonneg hpx hW _ _) (sum_nonneg fun _ _ => mul_nonneg (ind_nonneg _)
      (mul_nonneg (prod_nonneg fun j _ => (hσ j _ _).nonneg _) (ind_nonneg _))))

/-- The mass of `Bad` is at most the mass of the sequences. -/
lemma nncB_le_nncR (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W)
    (hσ : ∀ k a b, IsPMF (σ k a b)) (k : Fin N) (a : Fin n → X k) (b : Fin n → Y k)
    (c : Fin n → V k) : nncB px W σ k Bad a b c ≤ nncR px W k a b := by
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (ind_nonneg _)
  have h := sum_ind_prod_erase (A := fun j => Fin n → V j)
    (ν := fun j => σ j (x j) (yOf j y)) (fun j => hσ j _ _) k c
  calc _ ≤ nncXY px W x y * ∑ v : ∀ j, Fin n → V j, ind (v k = c) *
        ∏ j ∈ univ.erase k, σ j (x j) (yOf j y) (v j) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => ?_) (nncXY_nonneg hpx hW _ _)
        refine mul_le_mul_of_nonneg_left ?_ (ind_nonneg _)
        have h0 : 0 ≤ ∏ j ∈ univ.erase k, σ j (x j) (yOf j y) (v j) :=
          prod_nonneg fun j _ => (hσ j _ _).nonneg _
        have := mul_le_mul_of_nonneg_left (ind_le_one (Bad x y v)) h0
        linarith
    _ = _ := by rw [h, mul_one]

/-- Moving a weighted sum inside a double sum. -/
lemma sum_mul_sum_sum {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] (s : c → ℝ)
    (u w : a → b → ℝ) (T : a → b → c → ℝ) :
    ∑ e, s e * ∑ x, ∑ y, u x y * (w x y * T x y e) =
      ∑ x, ∑ y, u x y * (w x y * ∑ e, s e * T x y e) := by
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun e _ => ?_
  ring

/-- **The probability of `Bad` as a function of the kernel of node `k`.** -/
theorem nncHyb_update_eq (σ : NNCKernels n X Y V) (k : Fin N)
    (s : (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → ℝ) :
    nncHyb px W (Function.update σ k s) Bad =
      ∑ a, ∑ b, ∑ c, s a b c * nncB px W σ k Bad a b c := by
  classical
  have hprod : ∀ (x : ∀ k, Fin n → X k) (y : Fin n → ∀ k, Y k) (v : ∀ k, Fin n → V k),
      ∏ j, Function.update σ k s j (x j) (yOf j y) (v j) =
        s (x k) (yOf k y) (v k) * ∏ j ∈ univ.erase k, σ j (x j) (yOf j y) (v j) := by
    intro x y v
    rw [← mul_prod_erase univ _ (mem_univ k), Function.update_self]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  -- the inner sum
  have hin : ∀ (x : ∀ k, Fin n → X k) (y : Fin n → ∀ k, Y k),
      ∑ v, (∏ j, Function.update σ k s j (x j) (yOf j y) (v j)) * ind (Bad x y v) =
      ∑ c, s (x k) (yOf k y) c * ∑ v, ind (v k = c) *
        ((∏ j ∈ univ.erase k, σ j (x j) (yOf j y) (v j)) * ind (Bad x y v)) := by
    intro x y
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [Finset.sum_eq_single (v k)]
    · rw [hprod, ind_of_pos rfl, one_mul]
      ring
    · intro c _ hc
      rw [ind_of_neg (Ne.symm hc)]
      ring
    · simp
  have hR := sum_match (fun x : ∀ k, Fin n → X k => x k) (yOf (n := n) (Y := Y) k)
    fun a b x y => nncXY px W x y * ∑ c, s a b c * ∑ v, ind (v k = c) *
      ((∏ j ∈ univ.erase k, σ j (x j) (yOf j y) (v j)) * ind (Bad x y v))
  simp only [nncHyb]
  simp_rw [hin]
  rw [← hR]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  simp only [nncB]
  exact (sum_mul_sum_sum (s a b) (fun x y => ind (x k = a ∧ yOf k y = b))
    (fun x y => nncXY px W x y) fun x y c => ∑ v, ind (v k = c) *
      ((∏ j ∈ univ.erase k, σ j (x j) (yOf j y) (v j)) * ind (Bad x y v))).symm

end Hybrid

/-! ### One step of the hybrid argument -/

section Step

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {px : ∀ k, X k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}
  {σ : NNCKernels n X Y V} {Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) →
    Prop}

/-- The kernel of a node that picks a sequence of a random codebook of `K` sequences, each drawn
from `P a`, when its input sequence is `a` and its output sequence is `b`. -/
def nncSel {α β γ : Type*} [Fintype γ] (P : α → γ → ℝ) (K : ℕ)
    (pick : α → (Fin K → γ) → β → Fin K) (a : α) (b : β) (c : γ) : ℝ :=
  ∑ C : Fin K → γ, iidPMF (P a) K C * ind (C (pick a C b) = c)

lemma nncSel_isPMF {α β γ : Type*} [Fintype γ] {P : α → γ → ℝ} (hP : ∀ a, IsPMF (P a)) (K : ℕ)
    (pick : α → (Fin K → γ) → β → Fin K) (a : α) (b : β) : IsPMF (nncSel P K pick a b) := by
  classical
  have hI := iidPMF_isPMF (hP a) K
  refine ⟨fun c => sum_nonneg fun C _ => mul_nonneg (hI.nonneg C) (ind_nonneg _), ?_⟩
  simp only [nncSel]
  rw [sum_comm]
  have h : ∀ C : Fin K → γ, ∑ c, iidPMF (P a) K C * ind (C (pick a C b) = c) =
    iidPMF (P a) K C := by
    intro C
    rw [Finset.sum_eq_single (C (pick a C b))]
    · rw [ind_of_pos rfl, mul_one]
    · exact fun c _ hc => by rw [ind_of_neg (Ne.symm hc), mul_zero]
    · simp
  simp_rw [h]
  exact hI.sum_eq_one

/-- The sequences that node `k` looks for in its codebook. -/
def nncGood (px : ∀ k, X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (σ : NNCKernels n X Y V)
    (k : Fin N) (Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop)
    (Tj : (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → Prop) (δ : ℝ) (a : Fin n → X k)
    (b : Fin n → Y k) (c : Fin n → V k) : Prop :=
  nncB px W σ k Bad a b c ≤ δ * nncR px W k a b ∧ Tj a b c

/-- The index of a good sequence in the codebook. -/
def nncPick (px : ∀ k, X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (σ : NNCKernels n X Y V)
    (k : Fin N) (Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop)
    (Tj : (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → Prop) (δ : ℝ) {K : ℕ} [NeZero K]
    (a : Fin n → X k) (C : Fin K → Fin n → V k) (b : Fin n → Y k) : Fin K :=
  cfPick (nncGood px W σ k Bad Tj δ a b) C

/-- **One step of the hybrid argument.** Replacing the kernel `τn` of node `k` by the kernel of a
codebook of `K` sequences adds at most `δ + exp(-y K)` and the probability that the sequences of the
node are not typical, and divides the rest by `δ`. -/
theorem nncHyb_update_le {K : ℕ} [NeZero K] (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W)
    (hσ : ∀ k a b, IsPMF (σ k a b)) (k : Fin N) {P : (Fin n → X k) → (Fin n → V k) → ℝ}
    (hP : ∀ a, IsPMF (P a)) {τn : (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → ℝ}
    (hτn : ∀ a b, IsPMF (τn a b)) (Tj : (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → Prop)
    {δ y : ℝ} (hδ : 0 < δ) (hy1 : y ≤ 1) (hy : ∀ a b c, Tj a b c → τn a b c * y ≤ P a c) :
    nncHyb px W (Function.update σ k (nncSel P K (nncPick px W σ k Bad Tj δ))) Bad ≤
      δ + exp (-(y * K)) + ∑ a, ∑ b, nncR px W k a b * ∑ c, τn a b c * ind (¬ Tj a b c) +
        nncHyb px W (Function.update σ k τn) Bad / δ := by
  classical
  set R := nncR px W (n := n) k with hR
  set B := nncB px W σ k Bad with hB
  set Good := nncGood px W σ k Bad Tj δ with hGood
  have hR0 : ∀ a b, 0 ≤ R a b := nncR_nonneg hpx hW k
  have hB0 := nncB_nonneg (Bad := Bad) hpx hW hσ k
  have hBR := nncB_le_nncR (Bad := Bad) hpx hW hσ k
  have hRs : ∑ a, ∑ b, R a b = 1 := sum_nncR hpx hW k
  -- the kernel of the codebook
  have h₁ : ∀ a b, ∑ c, nncSel P K (nncPick px W σ k Bad Tj δ) a b c * B a b c =
      ∑ C : Fin K → Fin n → V k, iidPMF (P a) K C *
        B a b (C (nncPick px W σ k Bad Tj δ a C b)) := by
    intro a b
    simp only [nncSel, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun C _ => ?_
    rw [Finset.sum_eq_single (C (nncPick px W σ k Bad Tj δ a C b))]
    · rw [ind_of_pos rfl, mul_one]
    · exact fun c _ hc => by rw [ind_of_neg (Ne.symm hc), mul_zero, zero_mul]
    · simp
  -- a good sequence, or none
  have h₂ : ∀ a b (C : Fin K → Fin n → V k), B a b (C (nncPick px W σ k Bad Tj δ a C b)) ≤
      R a b * (δ + ∏ l, ind (¬ Good a b (C l))) := by
    intro a b C
    by_cases h : ∃ l, Good a b (C l)
    · have hg : Good a b (C (nncPick px W σ k Bad Tj δ a C b)) := cfPick_spec h
      have h0 : 0 ≤ ∏ l, ind (¬ Good a b (C l)) := prod_nonneg fun l _ => ind_nonneg _
      have := hg.1
      nlinarith [hR0 a b]
    · have h1 : ∏ l, ind (¬ Good a b (C l)) = 1 := prod_eq_one fun l _ =>
        ind_of_pos fun hl => h ⟨l, hl⟩
      rw [h1]
      have := hBR a b (C (nncPick px W σ k Bad Tj δ a C b))
      nlinarith [hR0 a b]
  -- the probability of missing
  have h₃ : ∀ a b, ∑ c, nncSel P K (nncPick px W σ k Bad Tj δ) a b c * B a b c ≤
      R a b * (δ + (1 - ∑ c, τn a b c * ind (Good a b c) + exp (-(y * K)))) := by
    intro a b
    have hI := iidPMF_isPMF (hP a) K
    have hm := sum_miss_le (hP a) (hτn a b) (G := Good a b) hy1
      (fun c hc => hy a b c hc.2) K
    rw [h₁]
    calc _ ≤ ∑ C : Fin K → Fin n → V k, iidPMF (P a) K C *
          (R a b * (δ + ∏ l, ind (¬ Good a b (C l)))) :=
          sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (h₂ a b C) (hI.nonneg C)
      _ = R a b * (δ + ∑ C : Fin K → Fin n → V k, iidPMF (P a) K C *
            ∏ l, ind (¬ Good a b (C l))) := by
          have e : ∀ C : Fin K → Fin n → V k, iidPMF (P a) K C *
              (R a b * (δ + ∏ l, ind (¬ Good a b (C l)))) = R a b * (δ * iidPMF (P a) K C +
                iidPMF (P a) K C * ∏ l, ind (¬ Good a b (C l))) := fun C => by ring
          simp_rw [e]
          rw [← mul_sum, sum_add_distrib, ← mul_sum, hI.sum_eq_one, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (hR0 a b)
  -- not good: not typical, or too much mass of `Bad`
  have h₄ : ∀ a b, R a b * (1 - ∑ c, τn a b c * ind (Good a b c)) ≤
      R a b * ∑ c, τn a b c * ind (¬ Tj a b c) + (∑ c, τn a b c * B a b c) / δ := by
    intro a b
    have e : 1 - ∑ c, τn a b c * ind (Good a b c) = ∑ c, τn a b c * ind (¬ Good a b c) := by
      rw [← (hτn a b).sum_eq_one, ← sum_sub_distrib]
      refine sum_congr rfl fun c _ => ?_
      by_cases h : Good a b c
      · rw [ind_of_pos h, ind_of_neg (not_not.mpr h)]
        ring
      · rw [ind_of_neg h, ind_of_pos h]
        ring
    rw [e, mul_sum, mul_sum, sum_div, ← sum_add_distrib]
    refine sum_le_sum fun c _ => ?_
    have hτ0 := (hτn a b).nonneg c
    by_cases hT : Tj a b c
    · by_cases hg : Good a b c
      · rw [ind_of_neg (not_not.mpr hg), mul_zero, mul_zero]
        exact add_nonneg (mul_nonneg (hR0 a b) (mul_nonneg hτ0 (ind_nonneg _)))
          (div_nonneg (mul_nonneg hτ0 (hB0 a b c)) hδ.le)
      · have hgt : δ * R a b < B a b c := by
          by_contra hle
          exact hg ⟨not_lt.mp hle, hT⟩
        rw [ind_of_pos hg, mul_one, ind_of_neg (not_not.mpr hT), mul_zero, mul_zero, zero_add,
          le_div_iff₀ hδ]
        nlinarith
    · rw [ind_of_pos hT, mul_one]
      have h' : ind (¬ Good a b c) ≤ 1 := ind_le_one _
      have h'' : 0 ≤ τn a b c * B a b c / δ := div_nonneg (mul_nonneg hτ0 (hB0 a b c)) hδ.le
      nlinarith [hR0 a b, mul_nonneg (hR0 a b) hτ0]
  have hτ := nncHyb_update_eq (px := px) (W := W) (Bad := Bad) σ k τn
  rw [nncHyb_update_eq σ k, hτ]
  have hsum : ∑ a, ∑ b, (∑ c, τn a b c * B a b c) / δ =
      (∑ a, ∑ b, ∑ c, τn a b c * nncB px W σ k Bad a b c) / δ := by
    rw [sum_div]
    exact sum_congr rfl fun a _ => (sum_div _ _ _).symm
  calc _ ≤ ∑ a, ∑ b, R a b * (δ + (1 - ∑ c, τn a b c * ind (Good a b c) + exp (-(y * K)))) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => h₃ a b
    _ = ∑ a, ∑ b, ((δ + exp (-(y * K))) * R a b +
          R a b * (1 - ∑ c, τn a b c * ind (Good a b c))) :=
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    _ ≤ ∑ a, ∑ b, ((δ + exp (-(y * K))) * R a b + (R a b * ∑ c, τn a b c * ind (¬ Tj a b c) +
          (∑ c, τn a b c * B a b c) / δ)) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => add_le_add le_rfl (h₄ a b)
    _ = _ := by
        simp_rw [sum_add_distrib, ← mul_sum]
        rw [hRs, mul_one, hsum]
        ring

end Step

/-! ### The i.i.d. law -/

section IID

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {px : ∀ k, X k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}
  {τ : ∀ k, X k × Y k → V k → ℝ}

/-- The tuple of the sequences of all the nodes, at each time. -/
def nncFull (x : ∀ k, Fin n → X k) (y : Fin n → ∀ k, Y k) (v : ∀ k, Fin n → V k) :
    Fin n → NNCΩ X Y V :=
  fun i => (fun k => x k i, y i, fun k => v k i)

/-- The sequences of the nodes are the sequences of the tuples. -/
def nncSeqEquiv : ((∀ k, Fin n → X k) × (Fin n → ∀ k, Y k) × (∀ k, Fin n → V k)) ≃
    (Fin n → NNCΩ X Y V) where
  toFun t := nncFull t.1 t.2.1 t.2.2
  invFun ω := (fun k i => (ω i).1 k, fun i => (ω i).2.1, fun k i => (ω i).2.2 k)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The kernels of the true conditional law. -/
def nncTauN (τ : ∀ k, X k × Y k → V k → ℝ) (n : ℕ) : NNCKernels n X Y V :=
  fun k a b c => seqChan (τ k) n (fun i => (a i, b i)) c

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] in
/-- The law of the tuple of sequences is i.i.d. -/
lemma iidPMF_nncFull (x : ∀ k, Fin n → X k) (y : Fin n → ∀ k, Y k) (v : ∀ k, Fin n → V k) :
    iidPMF (nncLaw px W τ) n (nncFull x y v) =
      nncXY px W x y * ∏ k, nncTauN τ n k (x k) (yOf k y) (v k) := by
  simp only [iidPMF, nncLaw, nncFull, nncXY, nncTauN, seqChan, prod_mul_distrib]
  congr 1
  · congr 1
    exact prod_comm
  · exact prod_comm

/-- **The probability of `Bad` for the true conditional law.** -/
lemma nncHyb_tauN
    (Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop) :
    nncHyb px W (nncTauN τ n) Bad = ∑ t : (∀ k, Fin n → X k) × (Fin n → ∀ k, Y k) ×
      (∀ k, Fin n → V k), iidPMF (nncLaw px W τ) n (nncFull t.1 t.2.1 t.2.2) *
        ind (Bad t.1 t.2.1 t.2.2) := by
  simp only [nncHyb, Fintype.sum_prod_type, iidPMF_nncFull, mul_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun v _ => ?_
  ring

/-- The event that the tuple of sequences is not typical. -/
def nncBad (L : NNCΩ X Y V → ℝ) (ε : ℝ) (x : ∀ k, Fin n → X k) (y : Fin n → ∀ k, Y k)
    (v : ∀ k, Fin n → V k) : Prop :=
  nncFull x y v ∉ robustTypicalSet L n ε

/-- The probability that the i.i.d. tuple is not typical. -/
lemma nncHyb_tauN_bad (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    (ε : ℝ) : nncHyb px W (nncTauN τ n) (nncBad (nncLaw px W τ) ε) =
      1 - prob (iidPMF (nncLaw px W τ) n) (robustTypicalSet (nncLaw px W τ) n ε) := by
  classical
  have hL := iidPMF_isPMF (nncLaw_isPMF hpx hW hτ) n
  rw [nncHyb_tauN]
  have e := Fintype.sum_equiv (nncSeqEquiv (n := n) (X := X) (Y := Y) (V := V))
    (fun t => iidPMF (nncLaw px W τ) n (nncFull t.1 t.2.1 t.2.2) *
      ind (nncBad (nncLaw px W τ) ε t.1 t.2.1 t.2.2))
    (fun ω => iidPMF (nncLaw px W τ) n ω * ind (ω ∉ robustTypicalSet (nncLaw px W τ) n ε))
    fun _ => rfl
  have e₂ : prob (iidPMF (nncLaw px W τ) n) (robustTypicalSet (nncLaw px W τ) n ε) =
      ∑ ω, if ω ∈ robustTypicalSet (nncLaw px W τ) n ε then iidPMF (nncLaw px W τ) n ω else 0 := by
    rw [prob, sum_ite_mem, univ_inter]
  rw [e, eq_sub_iff_add_eq, ← hL.sum_eq_one, e₂, ← sum_add_distrib]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : ω ∈ robustTypicalSet (nncLaw px W τ) n ε
  · simp [ind, h]
  · simp [ind, h]

/-- The event of a function of the sequences of node `k` under the true conditional law. -/
theorem sum_nncR_not_le (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    (k : Fin N) (Tj : (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → Prop)
    (Bad : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop)
    (hT : ∀ x y v, ¬ Bad x y v → Tj (x k) (yOf k y) (v k)) :
    ∑ a, ∑ b, nncR px W k a b * ∑ c, nncTauN τ n k a b c * ind (¬ Tj a b c) ≤
      nncHyb px W (nncTauN τ n) Bad := by
  classical
  have hσ : ∀ j a b, IsPMF (nncTauN τ n j a b) := fun j a b => seqChan_isChannel (hτ j) n _
  let Bad' : (∀ k, Fin n → X k) → (Fin n → ∀ k, Y k) → (∀ k, Fin n → V k) → Prop :=
    fun x y v => ¬ Tj (x k) (yOf k y) (v k)
  have hmono : nncHyb px W (nncTauN τ n) Bad' ≤ nncHyb px W (nncTauN τ n) Bad := by
    refine sum_le_sum fun x _ => sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
      (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (ind_mono fun h => by
        by_contra hB
        exact h (hT x y v hB))
        (prod_nonneg fun j _ => (hσ j _ _).nonneg _)) (nncXY_nonneg hpx hW x y)
  refine le_trans (le_of_eq ?_) hmono
  have hu := nncHyb_update_eq (px := px) (W := W) (Bad := Bad') (nncTauN τ n) k (nncTauN τ n k)
  rw [Function.update_eq_self] at hu
  rw [hu]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  have hB : nncB px W (nncTauN τ n) k Bad' a b c = nncR px W k a b * ind (¬ Tj a b c) := by
    simp only [nncB, nncR, sum_mul]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    by_cases hm : x k = a ∧ yOf k y = b
    · rw [ind_of_pos hm, one_mul, one_mul]
      congr 1
      have h₁ := sum_ind_prod_erase (A := fun j => Fin n → V j)
        (ν := fun j => nncTauN τ n j (x j) (yOf j y)) (fun j => hσ j _ _) k c
      rw [← mul_one (ind (¬ Tj a b c)), ← h₁, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      by_cases hv : v k = c
      · have : Bad' x y v ↔ ¬ Tj a b c := by
          simp only [Bad', hm.1, hm.2, hv]
        simp only [ind, this]
        split_ifs <;> simp
      · rw [ind_of_neg hv]
        ring
    · rw [ind_of_neg hm, zero_mul, zero_mul]
      simp
  rw [hB]
  ring

end IID

/-! ### Typical sequences -/

section Typical

variable {α β : Type*} [Fintype α] [Fintype β]

/-- On a typical sequence, a channel that gives the joint law is the conditional law. -/
lemma seqChan_eq_of_typical {J : α × β → ℝ} (hJ : IsPMF J) {K : α → β → ℝ}
    (hK : ∀ a b, J (a, b) = marg J a * K a b) {n : ℕ} {x : Fin n → α} {y : Fin n → β} {ε : ℝ}
    (h : zipSeq x y ∈ robustTypicalSet J n ε) :
    seqChan K n x y = channelExt (condPMF J) n x y := by
  simp only [seqChan, channelExt]
  refine prod_congr rfl fun i _ => ?_
  have hpos := pos_of_mem_robustTypicalSet hJ.nonneg h i
  have hzip : zipSeq x y i = (x i, y i) := rfl
  rw [hzip, hK] at hpos
  have hne : marg J (x i) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [condPMF, hK]
  field_simp

end Typical

/-! ### The law of the sequences of a node -/

section Node

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {px : ∀ k, X k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}
  {τ : ∀ k, X k × Y k → V k → ℝ}

/-- The law of `((X_k, Y_k), V_k)`. -/
def nncRho3 (L : NNCΩ X Y V → ℝ) (k : Fin N) : (X k × Y k) × V k → ℝ :=
  dist L fun ω => ((ω.1 k, ω.2.1 k), ω.2.2 k)

/-- `I(V_k; Y_k | X_k)`, the rate that the compression needs. -/
def nncI (L : NNCΩ X Y V → ℝ) (k : Fin N) : ℝ :=
  H[Prod.snd | Prod.fst ; nncRho L k] - H[Prod.snd | Prod.fst ; nncRho3 L k]

/-- The entropies of the compression of a node. -/
def nncH₂₃ (L : NNCΩ X Y V → ℝ) (k : Fin N) : ℝ :=
  H[Prod.snd | Prod.fst ; nncRho L k] + H[Prod.snd | Prod.fst ; nncRho3 L k]

/-- The compression of a node depends only on its input and its output. -/
lemma nncRho3_eq (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    (k : Fin N) (a : X k × Y k) (c : V k) :
    nncRho3 (nncLaw px W τ) k (a, c) =
      marg (nncRho3 (nncLaw px W τ) k) a * τ k a c := by
  classical
  have hL := nncLaw_isPMF hpx hW hτ (V := V)
  have hm : marg (nncRho3 (nncLaw px W τ) k) a =
      ∑ ω, nncLaw px W τ ω * ind ((ω.1 k, ω.2.1 k) = a) := by
    rw [marg_eq_dist, nncRho3, ← dist_comp_eq]
    simp only [dist, ind]
    refine sum_congr rfl fun ω _ => ?_
    split_ifs with h₁ h₂ h₂
    · simp
    · exact absurd h₁ h₂
    · exact absurd h₂ h₁
    · simp
  have hsum := sum_nncLaw_mul (px := px) (W := W) (V := V) hτ
    fun x y => ind ((x k, y k) = a)
  rw [hm, hsum, nncRho3]
  have hd : dist (nncLaw px W τ) (fun ω => ((ω.1 k, ω.2.1 k), ω.2.2 k)) (a, c) =
      ∑ ω, nncLaw px W τ ω * (ind ((ω.1 k, ω.2.1 k) = a) * ind (ω.2.2 k = c)) := by
    simp only [dist, ind]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₁ : (ω.1 k, ω.2.1 k) = a
    · by_cases h₂ : ω.2.2 k = c
      · simp [h₁, h₂]
      · have : ¬ ((ω.1 k, ω.2.1 k), ω.2.2 k) = (a, c) := fun h => h₂ (Prod.ext_iff.mp h).2
        simp [this, h₂]
    · have : ¬ ((ω.1 k, ω.2.1 k), ω.2.2 k) = (a, c) := fun h => h₁ (Prod.ext_iff.mp h).1
      simp [this, h₁]
  rw [hd]
  simp only [Fintype.sum_prod_type, nncLaw, sum_mul]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases h₁ : (x k, y k) = a
  · have h₂ := sum_ind_prod_erase (A := V) (ν := fun j => τ j (x j, y j)) (fun j => hτ j _) k c
    have h₃ : ∀ v : ∀ k, V k, ind (v k = c) * ∏ j, τ j (x j, y j) (v j) =
        τ k a c * (ind (v k = c) * ∏ j ∈ univ.erase k, τ j (x j, y j) (v j)) := by
      intro v
      by_cases hv : v k = c
      · rw [← mul_prod_erase univ _ (mem_univ k), hv, h₁, ind_of_pos rfl]
        ring
      · rw [ind_of_neg hv]
        ring
    simp only [h₁, ind_of_pos]
    calc _ = (∏ j, px j (x j)) * W x y * ∑ v : ∀ k, V k, ind (v k = c) *
          ∏ j, τ j (x j, y j) (v j) := by
          rw [mul_sum]
          refine sum_congr rfl fun v _ => ?_
          ring_nf
      _ = _ := by
          simp_rw [h₃]
          rw [← mul_sum, h₂]
          ring
  · simp [ind_of_neg h₁]

/-- A typical tuple of the sequences of a node: the probability of a sequence of the codebook is at
least `y` times its probability under the true conditional law. -/
lemma nnc_chan_mul_le (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    {q : ∀ k, X k → V k → ℝ}
    (hq : ∀ k a b, nncRho (nncLaw px W τ) k (a, b) =
      dist (nncLaw px W τ) (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b) (k : Fin N)
    {a : Fin n → X k} {b : Fin n → Y k} {c : Fin n → V k} {ε : ℝ}
    (h : zipSeq (zipSeq a b) c ∈ robustTypicalSet (nncRho3 (nncLaw px W τ) k) n ε) :
    seqChan (τ k) n (fun i => (a i, b i)) c *
        exp (-(n * (nncI (nncLaw px W τ) k + ε * nncH₂₃ (nncLaw px W τ) k))) ≤
      seqChan (q k) n a c := by
  have hL := nncLaw_isPMF hpx hW hτ (V := V)
  set L := nncLaw px W τ with hLd
  have h3P : IsPMF (nncRho3 L k) := hL.dist _
  have h2P : IsPMF (nncRho L k) := hL.dist _
  have hmarg2 : marg (nncRho L k) = dist L (fun ω : NNCΩ X Y V => ω.1 k) := by
    funext x
    rw [marg_eq_dist, nncRho, ← dist_comp_eq]
    rfl
  have e₃ : seqChan (τ k) n (fun i => (a i, b i)) c =
      channelExt (condPMF (nncRho3 L k)) n (zipSeq a b) c :=
    seqChan_eq_of_typical h3P (fun t v => nncRho3_eq hpx hW hτ k t v) h
  have hac : zipSeq a c ∈ robustTypicalSet (nncRho L k) n ε := by
    have hm := comp_mem_robustTypicalSet h fun t : (X k × Y k) × V k => (t.1.1, t.2)
    have e : dist (nncRho3 L k) (fun t : (X k × Y k) × V k => (t.1.1, t.2)) = nncRho L k := by
      rw [nncRho3, ← dist_comp_eq]
      rfl
    rw [e] at hm
    exact hm
  have e₂ : seqChan (q k) n a c = channelExt (condPMF (nncRho L k)) n a c :=
    seqChan_eq_of_typical h2P (fun x v => by rw [hq, hmarg2]) hac
  have h₁ := channelExt_condPMF_le_of_mem h3P h
  have h₂ := le_channelExt_condPMF_of_mem h2P hac
  rw [e₃, e₂]
  refine le_trans ?_ h₂
  calc _ ≤ exp (-(n * (H[Prod.snd | Prod.fst ; nncRho3 L k] -
        ε * H[Prod.snd | Prod.fst ; nncRho3 L k]))) *
        exp (-(n * (nncI L k + ε * nncH₂₃ L k))) :=
        mul_le_mul_of_nonneg_right h₁ (exp_pos _).le
    _ = _ := by
        rw [← exp_add]
        congr 1
        simp only [nncI, nncH₂₃]
        ring

/-- `I(V_k; Y_k | X_k)` is nonnegative. -/
lemma nncI_nonneg (hL : IsPMF (nncLaw px W τ)) (k : Fin N) : 0 ≤ nncI (nncLaw px W τ) k := by
  set L := nncLaw px W τ
  have h3 : H[Prod.snd | Prod.fst ; nncRho3 L k] =
      H[fun ω : NNCΩ X Y V => ω.2.2 k | fun ω => (ω.1 k, ω.2.1 k) ; L] := by
    refine condEntropy_eq_of_dist_pair_eq (hL.dist _) hL ?_
    rw [pair_fst_snd, dist_id]
    rfl
  have h2 : H[Prod.snd | Prod.fst ; nncRho L k] =
      H[fun ω : NNCΩ X Y V => ω.2.2 k | fun ω => ω.1 k ; L] := by
    refine condEntropy_eq_of_dist_pair_eq (hL.dist _) hL ?_
    rw [pair_fst_snd, dist_id]
    rfl
  have h := condEntropy_le_condEntropy_comp hL (fun ω : NNCΩ X Y V => ω.2.2 k)
    (fun ω => (ω.1 k, ω.2.1 k)) Prod.fst
  have e : (Prod.fst ∘ fun ω : NNCΩ X Y V => (ω.1 k, ω.2.1 k)) = fun ω => ω.1 k := rfl
  rw [e] at h
  rw [nncI, h2, h3]
  linarith

lemma nncH₂₃_nonneg (hL : IsPMF (nncLaw px W τ)) (k : Fin N) : 0 ≤ nncH₂₃ (nncLaw px W τ) k :=
  add_nonneg (condEntropy_nonneg (hL.dist _) _ _) (condEntropy_nonneg (hL.dist _) _ _)

end Node

/-! ### Covering at all the nodes -/

section Cover

open Filter Topology

variable {N : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {px : ∀ k, X k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}
  {τ : ∀ k, X k × Y k → V k → ℝ}

/-- The kernels of the nodes of `Done`, which use their codebooks, and of the other nodes, which use
the true conditional law. -/
def nncMix (τ : ∀ k, X k × Y k → V k → ℝ) (q : ∀ k, X k → V k → ℝ) (n : ℕ) (K : Fin N → ℕ)
    (Done : Finset (Fin N))
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k)) :
    NNCKernels n X Y V :=
  fun k => if k ∈ Done then nncSel (seqChan (q k) n) (K k) (pk k) else nncTauN τ n k

/-- **Covering at all the nodes.** If each node has a codebook of more than
`exp(n I(V_k; Y_k | X_k))` sequences, then there are encoders of the nodes such that the tuple of
all the sequences is typical with high probability. -/
theorem nnc_cover_aux (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    {q : ∀ k, X k → V k → ℝ}
    (hq : ∀ k a b, nncRho (nncLaw px W τ) k (a, b) =
      dist (nncLaw px W τ) (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    (hqc : ∀ k, IsChannel (q k)) {ε : ℝ} (hε : 0 < ε) {K : ℕ → Fin N → ℕ}
    [hK0 : ∀ n k, NeZero (K n k)] {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hK : ∀ᶠ n : ℕ in atTop, ∀ k,
      exp (n * (nncI (nncLaw px W τ) k + ϑ)) ≤ K n k) (Done : Finset (Fin N)) :
    ∀ η > 0, ∀ᶠ n : ℕ in atTop, ∃ pk : ∀ k, (Fin n → X k) → (Fin (K n k) → Fin n → V k) →
      (Fin n → Y k) → Fin (K n k),
      nncHyb px W (nncMix τ q n (K n) Done pk) (nncBad (nncLaw px W τ) ε) ≤ η := by
  classical
  have hL := nncLaw_isPMF hpx hW hτ (V := V)
  set L := nncLaw px W τ with hLd
  induction Done using Finset.induction_on with
  | empty =>
    intro η hη
    have hlim := tendsto_prob_robustTypicalSet hL hε
    filter_upwards [(tendsto_order.1 hlim).1 (1 - η) (by linarith)] with n hn
    refine ⟨fun k _ _ _ => 0, ?_⟩
    have e : nncMix τ q n (K n) ∅ (fun k _ _ _ => 0) = nncTauN τ n := by
      funext k
      simp [nncMix]
    rw [e, nncHyb_tauN_bad hpx hW hτ]
    linarith
  | insert k Done hk ih =>
    intro η hη
    set δ := η / 4 with hδd
    have hδ : 0 < δ := by positivity
    -- the typicality parameter of the sequences of the node
    set H := nncH₂₃ L k with hH
    have hH0 : 0 ≤ H := nncH₂₃_nonneg hL k
    set ε' := ϑ / (2 * (H + 1)) with hε'd
    have hε' : 0 < ε' := by positivity
    have hε'H : ε' * H ≤ ϑ / 2 := by
      rw [hε'd, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hlim' := tendsto_prob_robustTypicalSet hL hε'
    have hexp : Tendsto (fun n : ℕ => exp (-(n * (ϑ / 2)))) atTop (𝓝 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity : 0 < ϑ / 2))
      exact this
    filter_upwards [ih (δ * (η / 4)) (by positivity), hK,
      (tendsto_order.1 hlim').1 (1 - η / 4) (by linarith),
      (tendsto_order.1 hexp).2 (η / 4) (by positivity)] with n hn hKn hprob hexpn
    obtain ⟨pk, hpk⟩ := hn
    set σ := nncMix τ q n (K n) Done pk with hσd
    have hσ : ∀ j a b, IsPMF (σ j a b) := by
      intro j a b
      simp only [hσd, nncMix]
      split_ifs
      · exact nncSel_isPMF (seqChan_isChannel (hqc j) n) _ _ _ _
      · exact seqChan_isChannel (hτ j) n _
    let Tj : (Fin n → X k) → (Fin n → Y k) → (Fin n → V k) → Prop := fun a b c =>
      zipSeq (zipSeq a b) c ∈ robustTypicalSet (nncRho3 L k) n ε'
    set y := exp (-(n * (nncI L k + ε' * H))) with hy
    have hy1 : y ≤ 1 := by
      refine exp_le_one_iff.mpr ?_
      have := nncI_nonneg hL k
      have : 0 ≤ ε' * H := by positivity
      have : 0 ≤ (n : ℝ) * (nncI L k + ε' * H) := by positivity
      linarith
    have hyT : ∀ a b c, Tj a b c → nncTauN τ n k a b c * y ≤ seqChan (q k) n a c :=
      fun a b c h => nnc_chan_mul_le hpx hW hτ hq k h
    have hstep := nncHyb_update_le (σ := σ) (K := K n k) (Bad := nncBad L ε) hpx hW hσ k
      (P := seqChan (q k) n) (seqChan_isChannel (hqc k) n)
      (τn := nncTauN τ n k) (fun a b => seqChan_isChannel (hτ k) n _) Tj hδ hy1 hyT
    let pk' : ∀ j, (Fin n → X j) → (Fin (K n j) → Fin n → V j) → (Fin n → Y j) → Fin (K n j) :=
      Function.update pk k (nncPick px W σ k (nncBad L ε) Tj δ)
    refine ⟨pk', ?_⟩
    have e₁ : nncMix τ q n (K n) (insert k Done) pk' =
        Function.update σ k (nncSel (seqChan (q k) n) (K n k)
          (nncPick px W σ k (nncBad L ε) Tj δ)) := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [nncMix, pk']
      · rw [Function.update_of_ne hj]
        have : pk' j = pk j := Function.update_of_ne hj _ _
        simp [nncMix, hσd, hj, this]
    have e₂ : Function.update σ k (nncTauN τ n k) = σ := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [hσd, nncMix, hk]
      · rw [Function.update_of_ne hj]
    rw [e₁]
    rw [e₂] at hstep
    -- the sequences of the node are typical
    have hatyp : ∑ a, ∑ b, nncR px W k a b * ∑ c, nncTauN τ n k a b c * ind (¬ Tj a b c) ≤ η /
      4 := by
      have h₁ := sum_nncR_not_le hpx hW hτ k Tj (nncBad L ε') (fun x y v hB => by
        have hB' : nncFull x y v ∈ robustTypicalSet L n ε' := not_not.mp hB
        have hm := comp_mem_robustTypicalSet hB' fun ω : NNCΩ X Y V =>
          ((ω.1 k, ω.2.1 k), ω.2.2 k)
        exact hm)
      rw [nncHyb_tauN_bad hpx hW hτ] at h₁
      linarith
    -- the number of sequences of the codebook
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hyK : (n : ℝ) * (ϑ / 2) ≤ y * K n k := by
      have h₁ := hKn k
      have hprod : exp (n * (ϑ / 2)) ≤ y * K n k := by
        calc exp (n * (ϑ / 2)) ≤ y * exp (n * (nncI L k + ϑ)) := by
              rw [hy, ← exp_add]
              refine exp_le_exp.mpr ?_
              nlinarith
          _ ≤ _ := mul_le_mul_of_nonneg_left h₁ (exp_pos _).le
      have := add_one_le_exp ((n : ℝ) * (ϑ / 2))
      linarith
    have hexpK : exp (-(y * K n k)) ≤ η / 4 :=
      (exp_le_exp.mpr (by linarith)).trans hexpn.le
    have hdiv : nncHyb px W σ (nncBad L ε) / δ ≤ η / 4 := by
      rw [div_le_iff₀ hδ]
      linarith
    linarith

/-- **Covering at all the nodes.** -/
theorem nnc_cover (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    {q : ∀ k, X k → V k → ℝ}
    (hq : ∀ k a b, nncRho (nncLaw px W τ) k (a, b) =
      dist (nncLaw px W τ) (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    (hqc : ∀ k, IsChannel (q k)) {ε : ℝ} (hε : 0 < ε) {K : ℕ → Fin N → ℕ}
    [hK0 : ∀ n k, NeZero (K n k)] {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hK : ∀ᶠ n : ℕ in atTop, ∀ k,
      exp (n * (nncI (nncLaw px W τ) k + ϑ)) ≤ K n k) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∃ pk : ∀ k, (Fin n → X k) → (Fin (K n k) → Fin n → V k) →
      (Fin n → Y k) → Fin (K n k),
      nncHyb px W (fun k => nncSel (seqChan (q k) n) (K n k) (pk k))
        (nncBad (nncLaw px W τ) ε) ≤ η := by
  filter_upwards [nnc_cover_aux hpx hW hτ hq hqc hε hϑ hK univ η hη] with n hn
  obtain ⟨pk, hpk⟩ := hn
  refine ⟨pk, ?_⟩
  have e : nncMix τ q n (K n) univ pk = fun k => nncSel (seqChan (q k) n) (K n k) (pk k) := by
    funext k
    simp [nncMix]
  rwa [e] at hpk

end Cover

end InfoTheory
