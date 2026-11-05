/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayMarkov

/-!
# The relay channel: block Markov coding for compress–forward

A code for one block is repeated `B + 1` times. In block `j` the sender sends `x(m_j)` and the relay
sends `s(l_j)`. The next state of the relay is `l_{j+1} = r(l_j, y₁(j)) + d_{j+1}`, where `r` is the
bin index of the description of `y₁(j)` and `d_{j+1}` is an offset known to the receiver. The
receiver decodes `l_{j+1}` from `y(j+1)`, and then `m_j` from `y(j)`, `l_j` and the bin index.

## Main definitions

* `CFBlock`: a code for one block.
* `CFBlock.code`: the code of `B + 1` blocks.

## Main statements

* `CFBlock.exists_code_le`: some choice of the offsets and of the message of the last block gives a
  code with error at most `(B + 1)` times the average error of a block.

## Implementation notes

The state of the relay is not a function of the messages and its law is not uniform, so the genie
run of the decode–forward code does not apply, and neither does the argument of the notes, which
draws a new codebook for every block. Instead we use one fixed code for all the blocks, together
with the offsets, which are chosen at random and then fixed. For an offset drawn uniformly at
random, the state `l_j` is uniform and independent of the past. Thus the error of block `j`,
averaged over the offsets, is the error of the block code averaged over its states.

The message of the last block, which carries no information, is drawn in the same way.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

/-- **Resampling an entry of a table.** -/
lemma sum_resample {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (j : ι)
    (Φ : (ι → α) → ℝ) :
    ∑ θ, ∑ a, Φ (Function.update θ j a) = (Fintype.card α : ℝ) * ∑ θ, Φ θ := by
  let f := Equiv.piSplitAt j fun _ => α
  have hu : ∀ (b a : α) (t : ∀ i : {i // i ≠ j}, α),
      Function.update (f.symm (b, t)) j a = f.symm (a, t) := by
    intro b a t
    funext i
    by_cases hi : i = j
    · subst hi
      simp [f, Equiv.piSplitAt]
    · simp [f, Equiv.piSplitAt, hi]
  rw [← f.symm.sum_comp, ← f.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [hu]
  have h₁ : ∑ t : ∀ i : {i // i ≠ j}, α, ∑ a, Φ (f.symm (a, t)) =
      ∑ a, ∑ t : ∀ i : {i // i ≠ j}, α, Φ (f.symm (a, t)) := sum_comm
  simp_rw [h₁]
  simp [Finset.card_univ]

/-- A code for one block of compress–forward. -/
structure CFBlock (M L n : ℕ) (X U Y S : Type*) where
  /-- The codewords of the sender. -/
  x : Fin M → Fin n → X
  /-- The codewords of the relay, indexed by its state. -/
  s : Fin L → Fin n → U
  /-- The bin index of the description of the received sequence, given the state of the relay. -/
  r : Fin L → (Fin n → S) → Fin L
  /-- The decoder of the state of the relay. -/
  dL : (Fin n → Y) → Fin L
  /-- The decoder of the message, given the state of the relay and the bin index. -/
  dM : Fin L → Fin L → (Fin n → Y) → Fin M

/-- An entry of a table indexed by the blocks, at a natural number. -/
def tabAt {α : Type*} {B : ℕ} (t : Fin (B + 1) → α) (j : ℕ) : α :=
  if h : j < B + 1 then t ⟨j, h⟩ else t 0

lemma tabAt_val {α : Type*} {B : ℕ} (t : Fin (B + 1) → α) (j : Fin (B + 1)) :
    tabAt t j = t j := by
  simp [tabAt, j.2]

lemma tabAt_update {α : Type*} {B : ℕ} (t : Fin (B + 1) → α) (j : Fin (B + 1)) (a : α) :
    tabAt (Function.update t j a) j = a := by
  rw [tabAt_val, Function.update_self]

lemma tabAt_update_ne {α : Type*} {B : ℕ} (t : Fin (B + 1) → α) (j : Fin (B + 1)) (a : α) {i : ℕ}
    (hi : i < j) : tabAt (Function.update t j a) i = tabAt t i := by
  have hlt : i < B + 1 := hi.trans j.2
  simp only [tabAt, hlt, dite_true]
  refine Function.update_of_ne (fun h => ?_) _ _
  have := congrArg Fin.val h
  simp only at this
  omega

namespace CFBlock

variable {M L n B : ℕ} {X U Y S : Type*} (C : CFBlock M L n X U Y S)

section Err

variable [Fintype Y] [Fintype S]

/-- The loss of a block, for the state `l` of the relay, the message `m` and the received pair. -/
def loss (l : Fin L) (m : Fin M) (ζ : (Fin n → Y) × (Fin n → S)) : ℝ :=
  ind (C.dL ζ.1 ≠ l) + ind (C.dM l (C.r l ζ.2) ζ.1 ≠ m)

omit [Fintype Y] [Fintype S] in
lemma loss_nonneg (l : Fin L) (m : Fin M) (ζ : (Fin n → Y) × (Fin n → S)) : 0 ≤ C.loss l m ζ :=
  add_nonneg (ind_nonneg _) (ind_nonneg _)

/-- The error of a block, for a state of the relay and a message. -/
def rowErr (V : (Fin n → X) × (Fin n → U) → (Fin n → Y) × (Fin n → S) → ℝ) (l : Fin L)
    (m : Fin M) : ℝ :=
  ∑ ζ, V (C.x m, C.s l) ζ * C.loss l m ζ

/-- The error of a block, averaged over the states of the relay and over the messages. -/
def avgErr (V : (Fin n → X) × (Fin n → U) → (Fin n → Y) × (Fin n → S) → ℝ) : ℝ :=
  (∑ l, ∑ m, C.rowErr V l m) / (L * M)

end Err

variable [NeZero L] [NeZero n]

/-- The state of the relay in block `j`, when it has received `Z 0, Z 1, …`. -/
def st (d : Fin (B + 1) → Fin L) (Z : ℕ → Fin n → S) : ℕ → Fin L
  | 0 => tabAt d 0
  | j + 1 => C.r (st d Z j) (Z j) + tabAt d (j + 1)

omit [NeZero L] [NeZero n] in
lemma st_congr (d : Fin (B + 1) → Fin L) {Z Z' : ℕ → Fin n → S} :
    ∀ j, (∀ j', j' < j → Z j' = Z' j') → C.st d Z j = C.st d Z' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [st]
    rw [st_congr d j fun j' hj' => h j' (hj'.trans (Nat.lt_succ_self j)), h j (Nat.lt_succ_self j)]

omit [NeZero L] [NeZero n] in
/-- The state in a block does not depend on the offsets of the later blocks. -/
lemma st_update_lt (d : Fin (B + 1) → Fin L) (Z : ℕ → Fin n → S) (j : Fin (B + 1)) (a : Fin L) :
    ∀ i : ℕ, i < j → C.st (Function.update d j a) Z i = C.st d Z i
  | 0, h => by
    simp only [st]
    exact tabAt_update_ne d j a h
  | i + 1, h => by
    simp only [st]
    rw [st_update_lt d Z j a i (by omega), tabAt_update_ne d j a h]

omit [NeZero n] in
/-- The offset of a block is added to a state that does not depend on it. -/
lemma st_update_self (d : Fin (B + 1) → Fin L) (Z : ℕ → Fin n → S) (j : Fin (B + 1)) (a : Fin L) :
    C.st (Function.update d j a) Z j = (C.st d Z j - tabAt d j) + a := by
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero =>
    simp only [st]
    rw [sub_self, zero_add]
    exact tabAt_update d _ a
  | succ i =>
    simp only [st]
    rw [add_sub_cancel_right, st_update_lt C d Z ⟨i + 1, hj⟩ a i (by simp)]
    congr 1
    exact tabAt_update d ⟨i + 1, hj⟩ a

/-- The estimates of the receiver of the states of the relay. -/
def hatS (d : Fin (B + 1) → Fin L) (Yb : ℕ → Fin n → Y) : ℕ → Fin L
  | 0 => tabAt d 0
  | j + 1 => C.dL (Yb (j + 1))

variable [NeZero M]

/-- **The code of `B + 1` blocks.** It depends on the message `m₀` of the last block, and on the
offsets. -/
def code {M₀ : ℕ} (e : Fin M₀ ≃ (Fin B → Fin M)) (m₀ : Fin M) (d : Fin (B + 1) → Fin L) (d₁ : S)
    (dy : Y) : RCCode M₀ ((B + 1) * n) X U Y S where
  enc k w := C.x (tabAt (Fin.snoc (α := fun _ => Fin M) (e w) m₀) (k / n))
    ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩
  relay k y₁ := C.s (C.st d (getBlock d₁ y₁) (k / n)) ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩
  dec y := e.symm fun j => C.dM (C.hatS d (getBlock dy y) j)
    (C.hatS d (getBlock dy y) (j + 1) - tabAt d (j + 1)) (getBlock dy y j)

omit [NeZero L] [NeZero n] [NeZero M] in
/-- On a good run the receiver finds the states of the relay. -/
lemma hatS_eq {d : Fin (B + 1) → Fin L} {Yb : ℕ → Fin n → Y} {Z : ℕ → Fin n → S}
    (h : ∀ j, j ≤ B → C.dL (Yb j) = C.st d Z j) (j : ℕ) (hj : j ≤ B) :
    C.hatS d Yb j = C.st d Z j := by
  cases j with
  | zero => rfl
  | succ i => exact h _ hj

omit [NeZero M] in
/-- On a good run the receiver finds the message. -/
lemma code_dec_eq {M₀ : ℕ} (e : Fin M₀ ≃ (Fin B → Fin M)) (m₀ : Fin M) (d : Fin (B + 1) → Fin L)
    (d₁ : S) (dy : Y) (w : Fin M₀) {y : Fin ((B + 1) * n) → Y} {Z : ℕ → Fin n → S}
    (hL : ∀ j, j ≤ B → C.dL (getBlock dy y j) = C.st d Z j)
    (hM : ∀ j : Fin B, C.dM (C.st d Z j) (C.r (C.st d Z j) (Z j)) (getBlock dy y j) = e w j) :
    (C.code (X := X) e m₀ d d₁ dy).dec y = w := by
  simp only [code]
  rw [Equiv.symm_apply_eq]
  funext j
  have h₁ := C.hatS_eq hL j (by have := j.2; omega)
  have h₂ := C.hatS_eq hL (j + 1) (by have := j.2; omega)
  rw [h₁, h₂]
  simp only [st, add_sub_cancel_right]
  exact hM j

section Law

variable [Fintype Y] [Fintype S] {W : X × U → Y × S → ℝ}

/-- The sequences received by the relay, from a prefix of the blocks. -/
def arrS {k : ℕ} (d₁ : S) (z : Fin k → (Fin n → Y) × (Fin n → S)) (j : ℕ) : Fin n → S :=
  if h : j < k then (z ⟨j, h⟩).2 else fun _ => d₁

omit [Fintype Y] [Fintype S] [NeZero L] [NeZero n] [NeZero M] in
lemma arrS_snoc {k : ℕ} (d₁ : S) (z : Fin k → (Fin n → Y) × (Fin n → S))
    (c : (Fin n → Y) × (Fin n → S)) {j : ℕ} (hj : j < k) :
    arrS d₁ (Fin.snoc (α := fun _ => (Fin n → Y) × (Fin n → S)) z c) j = arrS d₁ z j := by
  have h₁ : j < k + 1 := by omega
  simp only [arrS, hj, h₁, dite_true]
  have : (⟨j, h₁⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hj⟩ := rfl
  rw [this, Fin.snoc_castSucc]

/-- The inputs in block `j`, for a table of the messages and of the offsets. -/
def blockEnc (d₁ : S) (j : ℕ) (θ : Fin (B + 1) → Fin M × Fin L)
    (z : Fin j → (Fin n → Y) × (Fin n → S)) : (Fin n → X) × (Fin n → U) :=
  (C.x (tabAt (fun i => (θ i).1) j), C.s (C.st (fun i => (θ i).2) (arrS d₁ z) j))

/-- The law of the output of all the blocks, for a table of the messages and of the offsets. -/
def blockLaw (V : (Fin n → X) × (Fin n → U) → (Fin n → Y) × (Fin n → S) → ℝ) (d₁ : S) (k : ℕ)
    (t : (Fin (B + 1) → Fin M × Fin L) × (Fin k → (Fin n → Y) × (Fin n → S))) : ℝ :=
  fbLaw (fun _ => 1) V (C.blockEnc d₁) k t

variable {V : (Fin n → X) × (Fin n → U) → (Fin n → Y) × (Fin n → S) → ℝ}

omit [NeZero L] [NeZero n] [NeZero M] in
lemma blockLaw_nonneg (hV : IsChannel V) (d₁ : S) (k : ℕ)
    (t : (Fin (B + 1) → Fin M × Fin L) × (Fin k → (Fin n → Y) × (Fin n → S))) :
    0 ≤ C.blockLaw V d₁ k t := by
  rw [blockLaw, fbLaw_eq_prod, one_mul]
  exact prod_nonneg fun i _ => (hV _).nonneg _

omit [NeZero L] [NeZero n] [NeZero M] in
lemma sum_blockLaw (hV : IsChannel V) (d₁ : S) (θ : Fin (B + 1) → Fin M × Fin L) (k : ℕ) :
    ∑ z, C.blockLaw V d₁ k (θ, z) = 1 := by
  induction k with
  | zero => simp [blockLaw, fbLaw]
  | succ k ih =>
    simp only [blockLaw] at ih ⊢
    simp_rw [sum_snoc k, fbLaw_snoc, ← mul_sum, (hV _).sum_eq_one, mul_one]
    exact ih

/-- The loss in block `j`. -/
def blockLoss (d₁ : S) (j : ℕ) (θ : Fin (B + 1) → Fin M × Fin L) {k : ℕ}
    (z : Fin k → (Fin n → Y) × (Fin n → S)) : ℝ :=
  if h : j < k then
    C.loss (C.st (fun i => (θ i).2) (arrS d₁ z) j) (tabAt (fun i => (θ i).1) j) (z ⟨j, h⟩)
  else 0

omit [NeZero L] [NeZero n] [NeZero M] in
/-- The later blocks do not change the expectation of the loss of a block. -/
lemma sum_blockLoss_later (hV : IsChannel V) (d₁ : S) (j : ℕ) (θ : Fin (B + 1) → Fin M × Fin L)
    (k : ℕ) (hk : j + 1 ≤ k) :
    ∑ z, C.blockLaw V d₁ k (θ, z) * C.blockLoss d₁ j θ z =
      ∑ z, C.blockLaw V d₁ (j + 1) (θ, z) * C.blockLoss d₁ j θ z := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih]
    simp only [blockLaw] at ih ⊢
    simp_rw [sum_snoc k, fbLaw_snoc]
    refine sum_congr rfl fun u _ => ?_
    have hjk : j < k := hk
    have hval : ∀ c, C.blockLoss d₁ j θ
        (Fin.snoc (α := fun _ => (Fin n → Y) × (Fin n → S)) u c) = C.blockLoss d₁ j θ u := by
      intro c
      have hj₁ : j < k + 1 := by omega
      simp only [blockLoss, hjk, hj₁, dite_true]
      have hcast : (⟨j, hj₁⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hjk⟩ := rfl
      rw [hcast, Fin.snoc_castSucc]
      congr 1
      exact C.st_congr _ _ fun j' hj' => arrS_snoc d₁ u c (hj'.trans hjk)
    simp_rw [hval, mul_assoc, ← mul_sum, ← sum_mul, (hV _).sum_eq_one, one_mul]

omit [NeZero L] [NeZero n] [NeZero M] in
/-- The expectation of the loss of a block, given the previous blocks. -/
lemma sum_blockLoss_self (d₁ : S) (j : ℕ) (θ : Fin (B + 1) → Fin M × Fin L) :
    ∑ z, C.blockLaw V d₁ (j + 1) (θ, z) * C.blockLoss d₁ j θ z =
      ∑ u, C.blockLaw V d₁ j (θ, u) *
        C.rowErr V (C.st (fun i => (θ i).2) (arrS d₁ u) j) (tabAt (fun i => (θ i).1) j) := by
  simp only [blockLaw]
  simp_rw [sum_snoc j, fbLaw_snoc, rowErr, mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun c _ => ?_
  have hj₁ : j < j + 1 := by omega
  have hl : C.blockLoss d₁ j θ (Fin.snoc (α := fun _ => (Fin n → Y) × (Fin n → S)) u c) =
      C.loss (C.st (fun i => (θ i).2) (arrS d₁ u) j) (tabAt (fun i => (θ i).1) j) c := by
    simp only [blockLoss, hj₁, dite_true]
    have hcast : (⟨j, hj₁⟩ : Fin (j + 1)) = Fin.last j := rfl
    rw [hcast, Fin.snoc_last]
    congr 1
    exact C.st_congr _ _ fun j' hj' => arrS_snoc d₁ u c hj'
  rw [hl, mul_assoc]
  rfl

omit [Fintype Y] [Fintype S] [NeZero L] [NeZero n] [NeZero M] in
/-- The law of the blocks before block `j` does not depend on the table at `j`. -/
lemma blockLaw_update (d₁ : S) (j : Fin (B + 1)) (θ : Fin (B + 1) → Fin M × Fin L)
    (a : Fin M × Fin L) (u : Fin j → (Fin n → Y) × (Fin n → S)) :
    C.blockLaw V d₁ j (Function.update θ j a, u) = C.blockLaw V d₁ j (θ, u) := by
  simp only [blockLaw]
  rw [fbLaw_eq_prod, fbLaw_eq_prod]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  congr 1
  simp only [blockEnc]
  have hi : (i : ℕ) < j := i.2
  have hfst : (fun t => (Function.update θ j a t).1) =
      Function.update (fun t => (θ t).1) j a.1 := by
    funext t
    by_cases ht : t = j
    · subst ht
      simp
    · simp [Function.update_of_ne ht]
  have hsnd : (fun t => (Function.update θ j a t).2) =
      Function.update (fun t => (θ t).2) j a.2 := by
    funext t
    by_cases ht : t = j
    · subst ht
      simp
    · simp [Function.update_of_ne ht]
  rw [hfst, hsnd, tabAt_update_ne _ j _ hi, C.st_update_lt _ _ j _ _ hi]

omit [NeZero n] in
/-- The sum over the offset and the message of a block is the average over the block code. -/
lemma sum_rowErr_shift (pre : Fin L) :
    ∑ a : Fin M × Fin L, C.rowErr V (pre + a.2) a.1 = (L * M : ℝ) * C.avgErr V := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [avgErr, mul_div_cancel₀ _ (mul_ne_zero hL hM), Fintype.sum_prod_type, sum_comm]
  exact Equiv.sum_comp (Equiv.addLeft pre) fun l => ∑ m, C.rowErr V l m

omit [NeZero n] in
/-- **The expectation of the loss of a block.** For a uniform table of the messages and of the
offsets, the expected loss of each block is the average error of the block code. -/
theorem sum_blockLoss (hV : IsChannel V) (d₁ : S) (j : Fin (B + 1)) :
    ∑ θ : Fin (B + 1) → Fin M × Fin L, ∑ z, C.blockLaw V d₁ (B + 1) (θ, z) *
        C.blockLoss d₁ j θ z =
      (Fintype.card (Fin (B + 1) → Fin M × Fin L) : ℝ) * C.avgErr V := by
  classical
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h₁ : ∀ θ : Fin (B + 1) → Fin M × Fin L, ∑ z, C.blockLaw V d₁ (B + 1) (θ, z) *
      C.blockLoss d₁ j θ z = ∑ u, C.blockLaw V d₁ j (θ, u) *
        C.rowErr V (C.st (fun i => (θ i).2) (arrS d₁ u) j) (tabAt (fun i => (θ i).1) j) := by
    intro θ
    rw [C.sum_blockLoss_later hV d₁ j θ (B + 1) j.2, C.sum_blockLoss_self]
  simp_rw [h₁]
  rw [sum_comm]
  have h₂ : ∀ u : Fin j → (Fin n → Y) × (Fin n → S),
      ∑ θ : Fin (B + 1) → Fin M × Fin L, C.blockLaw V d₁ j (θ, u) *
        C.rowErr V (C.st (fun i => (θ i).2) (arrS d₁ u) j) (tabAt (fun i => (θ i).1) j) =
      ∑ θ : Fin (B + 1) → Fin M × Fin L, C.blockLaw V d₁ j (θ, u) * C.avgErr V := by
    intro u
    have hr := sum_resample j fun θ : Fin (B + 1) → Fin M × Fin L => C.blockLaw V d₁ j (θ, u) *
      C.rowErr V (C.st (fun i => (θ i).2) (arrS d₁ u) j) (tabAt (fun i => (θ i).1) j)
    have hcard : (Fintype.card (Fin M × Fin L) : ℝ) = L * M := by
      simp [mul_comm]
    rw [hcard] at hr
    refine mul_left_cancel₀ (mul_ne_zero hL hM) (hr.symm.trans ?_)
    rw [mul_sum]
    refine sum_congr rfl fun θ _ => ?_
    have hfst : ∀ a : Fin M × Fin L, (fun t => (Function.update θ j a t).1) =
        Function.update (fun t => (θ t).1) j a.1 := by
      intro a
      funext t
      by_cases ht : t = j
      · subst ht
        simp
      · simp [Function.update_of_ne ht]
    have hsnd : ∀ a : Fin M × Fin L, (fun t => (Function.update θ j a t).2) =
        Function.update (fun t => (θ t).2) j a.2 := by
      intro a
      funext t
      by_cases ht : t = j
      · subst ht
        simp
      · simp [Function.update_of_ne ht]
    have h₃ : ∀ a : Fin M × Fin L, C.blockLaw V d₁ j (Function.update θ j a, u) *
        C.rowErr V (C.st (fun i => (Function.update θ j a i).2) (arrS d₁ u) j)
          (tabAt (fun i => (Function.update θ j a i).1) j) =
        C.blockLaw V d₁ j (θ, u) * C.rowErr V
          ((C.st (fun i => (θ i).2) (arrS d₁ u) j - tabAt (fun i => (θ i).2) j) + a.2) a.1 := by
      intro a
      rw [C.blockLaw_update, hfst, hsnd, tabAt_update, C.st_update_self]
    simp_rw [h₃, ← mul_sum, C.sum_rowErr_shift]
    ring
  simp_rw [h₂, ← sum_mul]
  rw [sum_comm]
  simp_rw [C.sum_blockLaw hV d₁]
  simp [card_univ]

/-- The total loss of the blocks. -/
def totalLoss (V : (Fin n → X) × (Fin n → U) → (Fin n → Y) × (Fin n → S) → ℝ) (d₁ : S)
    (θ : Fin (B + 1) → Fin M × Fin L) : ℝ :=
  ∑ z, C.blockLaw V d₁ (B + 1) (θ, z) * ∑ j : Fin (B + 1), C.blockLoss d₁ j θ z

omit [NeZero n] in
/-- **The expectation of the total loss.** -/
theorem sum_totalLoss (hV : IsChannel V) (d₁ : S) :
    ∑ θ : Fin (B + 1) → Fin M × Fin L, C.totalLoss V d₁ θ =
      (Fintype.card (Fin (B + 1) → Fin M × Fin L) : ℝ) * (((B : ℝ) + 1) * C.avgErr V) := by
  simp only [totalLoss, mul_sum]
  rw [sum_congr rfl fun θ _ => sum_comm, sum_comm]
  simp_rw [C.sum_blockLoss hV d₁]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Law

/-! ### The code of all the blocks -/

section Code

variable [Fintype Y] [Fintype S] {W : X × U → Y × S → ℝ}

/-- The table of the messages and of the offsets. -/
def tableOf {M₀ : ℕ} (e : Fin M₀ ≃ (Fin B → Fin M)) (m₀ : Fin M) (d : Fin (B + 1) → Fin L)
    (w : Fin M₀) : Fin (B + 1) → Fin M × Fin L :=
  fun j => (Fin.snoc (α := fun _ => Fin M) (e w) m₀ j, d j)

omit [NeZero L] [NeZero M] [Fintype Y] [Fintype S] in
/-- The law of the code of all the blocks. -/
lemma code_law {M₀ : ℕ} (e : Fin M₀ ≃ (Fin B → Fin M)) (m₀ : Fin M) (d : Fin (B + 1) → Fin L)
    (d₁ : S) (dy : Y) (w : Fin M₀) (z : Fin ((B + 1) * n) → Y × S) :
    (C.code (X := X) e m₀ d d₁ dy).law W ((B + 1) * n) (w, z) =
      uniformPMF (Fin M₀) w *
        C.blockLaw (relaySeq W n) d₁ (B + 1) (tableOf e m₀ d w, blockEquiv z) := by
  rw [RCCode.law, fbLaw_eq_prod, blockLaw, fbLaw_eq_prod, one_mul]
  congr 1
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  refine prod_congr rfl fun j _ => ?_
  simp only [relaySeq]
  refine prod_congr rfl fun i _ => ?_
  obtain ⟨hdiv, hmod⟩ := finProd_div_mod (B := B) j i
  have hin : (⟨((finProdFinEquiv (j, i) : Fin ((B + 1) * n)) : ℕ) % n,
      Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = i := Fin.ext hmod
  have hst : C.st d (getBlock d₁ fun t : Fin (finProdFinEquiv (j, i) : Fin ((B + 1) * n)) =>
      (z ⟨t, t.2.trans (finProdFinEquiv (j, i)).2⟩).2) j =
      C.st d (arrS d₁ fun t : Fin j => blockEquiv z ⟨t, t.2.trans j.2⟩) j := by
    refine C.st_congr d j fun j' hj' => ?_
    funext i'
    have hj'B : j' < B + 1 := hj'.trans j.2
    have hlt : i'.val + n * j' <
        ((finProdFinEquiv (j, i) : Fin ((B + 1) * n)) : ℕ) := by
      have hval : ((finProdFinEquiv (j, i) : Fin ((B + 1) * n)) : ℕ) = i + n * j := rfl
      rw [hval]
      have h₁ : n * (j' + 1) ≤ n * j := Nat.mul_le_mul_left _ hj'
      have h₂ := i'.2
      rw [Nat.mul_add, Nat.mul_one] at h₁
      omega
    simp only [getBlock, dite_eq_left hlt, arrS, dite_eq_left hj']
    rfl
  simp only [RCCode.fbEnc, code, blockEnc, tableOf]
  rw [hdiv, hin, hst]
  rfl

omit [NeZero M] [Fintype Y] [Fintype S] in
/-- On a good run the decoder finds the message. -/
lemma ind_dec_le {M₀ : ℕ} (e : Fin M₀ ≃ (Fin B → Fin M)) (m₀ : Fin M) (d : Fin (B + 1) → Fin L)
    (d₁ : S) (dy : Y) (w : Fin M₀) (z : Fin ((B + 1) * n) → Y × S) :
    ind ((C.code (X := X) e m₀ d d₁ dy).dec (fun i => (z i).1) ≠ w) ≤
      ∑ j : Fin (B + 1), C.blockLoss d₁ j (tableOf e m₀ d w) (blockEquiv z) := by
  classical
  have hnn : ∀ j : Fin (B + 1), 0 ≤ C.blockLoss d₁ j (tableOf e m₀ d w) (blockEquiv z) := by
    intro j
    simp only [blockLoss, j.2, dite_true]
    exact C.loss_nonneg _ _ _
  by_cases h : (C.code (X := X) e m₀ d d₁ dy).dec (fun i => (z i).1) = w
  · rw [ind_of_neg (not_not.mpr h)]
    exact sum_nonneg fun j _ => hnn j
  rw [ind_of_pos h]
  by_contra hc
  push Not at hc
  have hlt : ∀ j : Fin (B + 1), C.blockLoss d₁ j (tableOf e m₀ d w) (blockEquiv z) < 1 := fun j =>
    lt_of_le_of_lt (single_le_sum (f := fun j : Fin (B + 1) => C.blockLoss d₁ j (tableOf e m₀ d w)
      (blockEquiv z)) (fun j _ => hnn j) (mem_univ j)) hc
  have hval : ∀ j : Fin (B + 1), C.blockLoss d₁ j (tableOf e m₀ d w) (blockEquiv z) =
      C.loss (C.st d (arrS d₁ (blockEquiv z)) j) (Fin.snoc (α := fun _ => Fin M) (e w) m₀ j)
        (blockEquiv z j) := by
    intro j
    simp only [blockLoss, j.2, dite_true, tableOf, tabAt_val]
  have hind : ∀ {P Q : Prop}, ind P + ind Q < 1 → ¬ P ∧ ¬ Q := by
    intro P Q hPQ
    refine ⟨fun hP => ?_, fun hQ => ?_⟩
    · rw [ind_of_pos hP] at hPQ
      linarith [ind_nonneg Q]
    · rw [ind_of_pos hQ] at hPQ
      linarith [ind_nonneg P]
  have hgood : ∀ j : Fin (B + 1), C.dL (blockEquiv z j).1 = C.st d (arrS d₁ (blockEquiv z)) j ∧
      C.dM (C.st d (arrS d₁ (blockEquiv z)) j)
        (C.r (C.st d (arrS d₁ (blockEquiv z)) j) (blockEquiv z j).2) (blockEquiv z j).1 =
        Fin.snoc (α := fun _ => Fin M) (e w) m₀ j := by
    intro j
    have := hlt j
    rw [hval, loss] at this
    obtain ⟨h₁, h₂⟩ := hind this
    exact ⟨not_not.mp h₁, not_not.mp h₂⟩
  have hb : ∀ (j : ℕ) (hj : j < B + 1), getBlock dy (fun i => (z i).1) j =
      (blockEquiv z ⟨j, hj⟩).1 := by
    intro j hj
    funext i
    have hi : i.val + n * j < (B + 1) * n := by
      have h₁ : n * (j + 1) ≤ n * (B + 1) := Nat.mul_le_mul_left _ hj
      have h₂ := i.2
      rw [Nat.mul_add, Nat.mul_one] at h₁
      rw [Nat.mul_comm (B + 1) n]
      omega
    simp only [getBlock, dite_eq_left hi]
    rfl
  refine h (C.code_dec_eq e m₀ d d₁ dy w (Z := arrS d₁ (blockEquiv z)) (fun j hj => ?_) fun j => ?_)
  · have hj' : j < B + 1 := by omega
    rw [hb j hj']
    exact (hgood ⟨j, hj'⟩).1
  · have hj' : (j : ℕ) < B + 1 := by have := j.2; omega
    have hg := (hgood ⟨j, hj'⟩).2
    have hc : (⟨j, hj'⟩ : Fin (B + 1)) = Fin.castSucc j := rfl
    rw [hc, Fin.snoc_castSucc] at hg
    rw [hb j hj']
    have hs : arrS d₁ (blockEquiv z) j = (blockEquiv z ⟨j, hj'⟩).2 := by
      simp only [arrS, hj', dite_true]
    rw [hs]
    exact hg

omit [NeZero L] [NeZero M] in
/-- The map from a message and the choices of the code to the table is bijective. -/
lemma tableOf_bijective {M₀ : ℕ} (e : Fin M₀ ≃ (Fin B → Fin M)) :
    Function.Bijective fun t : Fin M₀ × Fin M × (Fin (B + 1) → Fin L) =>
      tableOf e t.2.1 t.2.2 t.1 := by
  refine ⟨fun a b hab => ?_, fun θ => ?_⟩
  · have hd : a.2.2 = b.2.2 := by
      funext j
      exact (Prod.ext_iff.mp (congrFun hab j)).2
    have hl := (Prod.ext_iff.mp (congrFun hab (Fin.last B))).1
    simp only [tableOf, Fin.snoc_last] at hl
    have hw : a.1 = b.1 := by
      refine e.injective (funext fun j => ?_)
      have := (Prod.ext_iff.mp (congrFun hab (Fin.castSucc j))).1
      simpa only [tableOf, Fin.snoc_castSucc] using this
    exact Prod.ext hw (Prod.ext hl hd)
  · refine ⟨(e.symm fun j => (θ (Fin.castSucc j)).1, (θ (Fin.last B)).1, fun j => (θ j).2), ?_⟩
    funext j
    refine Prod.ext ?_ rfl
    simp only [tableOf]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · simp

/-- **The error of the code of all the blocks.** Some choice of the message of the last block and of
the offsets gives a code with error at most `B + 1` times the average error of the block code. -/
theorem exists_code_le {M₀ : ℕ} (hW : IsChannel W) (e : Fin M₀ ≃ (Fin B → Fin M)) (d₁ : S)
    (dy : Y) : ∃ (m₀ : Fin M) (d : Fin (B + 1) → Fin L), (C.code (X := X) e m₀ d d₁ dy).errProb W ≤
      ((B : ℝ) + 1) * C.avgErr (relaySeq W n) := by
  classical
  have hV := relaySeq_isChannel hW n
  have hcard : (M₀ : ℝ) = (M : ℝ) ^ B := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_fun] at h
    rw [h]
    push_cast
    rfl
  have hMr : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hLr : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hM₀ : (0 : ℝ) < M₀ := by rw [hcard]; positivity
  -- the error of a code
  have h₁ : ∀ (m₀ : Fin M) (d : Fin (B + 1) → Fin L), (C.code (X := X) e m₀ d d₁ dy).errProb W ≤
      (∑ w, C.totalLoss (relaySeq W n) d₁ (tableOf e m₀ d w)) / M₀ := by
    intro m₀ d
    have hu : ∀ w : Fin M₀, uniformPMF (Fin M₀) w = 1 / (M₀ : ℝ) := fun w => by simp [uniformPMF]
    rw [sum_div]
    simp only [RCCode.errProb, InfoTheory.errProb, Fintype.sum_prod_type]
    refine sum_le_sum fun w _ => ?_
    simp only [totalLoss]
    rw [← (blockEquiv (B := B) (n := n) (Y := Y) (Y₁ := S)).sum_comp, sum_div]
    refine sum_le_sum fun z _ => ?_
    have hl := C.code_law (W := W) e m₀ d d₁ dy w z
    have h0 := C.blockLaw_nonneg hV d₁ (B + 1) (tableOf e m₀ d w, blockEquiv z)
    have hnd := C.ind_dec_le (X := X) e m₀ d d₁ dy w z
    rw [hl, hu]
    have hle : 1 / (M₀ : ℝ) *
      C.blockLaw (relaySeq W n) d₁ (B + 1) (tableOf e m₀ d w, blockEquiv z) *
        ind ((C.code (X := X) e m₀ d d₁ dy).dec (fun i => (z i).1) ≠ w) ≤
        C.blockLaw (relaySeq W n) d₁ (B + 1) (tableOf e m₀ d w, blockEquiv z) *
          (∑ j : Fin (B + 1), C.blockLoss d₁ j (tableOf e m₀ d w) (blockEquiv z)) / M₀ := by
      calc _ ≤ 1 / (M₀ : ℝ) * C.blockLaw (relaySeq W n) d₁ (B + 1)
            (tableOf e m₀ d w, blockEquiv z) *
              ∑ j : Fin (B + 1), C.blockLoss d₁ j (tableOf e m₀ d w) (blockEquiv z) :=
            mul_le_mul_of_nonneg_left hnd (by positivity)
        _ = _ := by ring
    refine le_trans (le_of_eq ?_) hle
    by_cases hd : (C.code (X := X) e m₀ d d₁ dy).dec (fun i => (z i).1) ≠ w
    · rw [ind_of_pos hd, mul_one]
      exact ite_eq_left hd
    · rw [ind_of_neg hd, mul_zero]
      exact ite_eq_right hd
  -- the sum over the choices of the code
  have h₂ : ∑ t : Fin M × (Fin (B + 1) → Fin L),
      (C.code (X := X) e t.1 t.2 d₁ dy).errProb W ≤
      ∑ _t : Fin M × (Fin (B + 1) → Fin L), ((B : ℝ) + 1) * C.avgErr (relaySeq W n) := by
    calc _ ≤ ∑ t : Fin M × (Fin (B + 1) → Fin L),
          (∑ w, C.totalLoss (relaySeq W n) d₁ (tableOf e t.1 t.2 w)) / M₀ :=
          sum_le_sum fun t _ => h₁ t.1 t.2
      _ = (∑ θ : Fin (B + 1) → Fin M × Fin L, C.totalLoss (relaySeq W n) d₁ θ) / M₀ := by
          rw [← sum_div, ← (tableOf_bijective (L := L) e).sum_comp]
          congr 1
          rw [sum_comm, Fintype.sum_prod_type
            (f := fun i : Fin M₀ × Fin M × (Fin (B + 1) → Fin L) =>
            C.totalLoss (relaySeq W n) d₁ (tableOf e i.2.1 i.2.2 i.1))]
      _ = _ := by
          rw [C.sum_totalLoss hV d₁]
          simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          rw [hcard]
          field_simp
          ring
  obtain ⟨t, -, ht⟩ := exists_le_of_sum_le (s := univ) ⟨(0, 0), mem_univ _⟩ h₂
  exact ⟨t.1, t.2, ht⟩

end Code

end CFBlock

end InfoTheory
