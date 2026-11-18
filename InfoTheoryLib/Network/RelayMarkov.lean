/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayBlockIID

/-!
# The relay channel: block Markov coding and backward decoding

A code for one block is repeated `B + 1` times. In block `j` the sender sends `x(a_{j-1}, a_j, c_j)`
and the relay sends `s(ã_{j-1})`, where `ã_{j-1}` is what it has decoded in block `j - 1`. The
receiver decodes backward.

## Main definitions

* `RelayBlock.markov`: the code of `B + 1` blocks.

## Main statements

* `RelayBlock.markov_errProb_le`: the error of the code of all blocks is at most the sum of the
  errors of the blocks.

## Implementation notes

The notes use a new independent codebook in each block, and induction over the blocks for the error
of the relay and of the receiver. Here one fixed code is used in all the blocks. Let the genie run
be the one in which the relay always decodes correctly. Its blocks are independent, and the actual
run coincides with it as long as nothing goes wrong. So the probability of error is at most the sum
of the probabilities that a decoder fails in a block of the genie run, and these are averages of
`RelayBlock.err` because the messages are uniform.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The code of all the blocks -/

section Markov

variable {Ma Mc n B M : ℕ} {X X₁ Y Y₁ : Type*}

/-- The messages of `B` blocks. -/
abbrev MarkovMsg (Ma Mc B : ℕ) : Type := (Fin B → Fin Ma) × (Fin B → Fin Mc)

section Msg

variable [NeZero Ma] [NeZero Mc]

/-- The index `a_j`, which is `0` after the last message. -/
def msgA (m : MarkovMsg Ma Mc B) (j : ℕ) : Fin Ma := if h : j < B then m.1 ⟨j, h⟩ else 0

/-- The index `c_j`, which is `0` after the last message. -/
def msgC (m : MarkovMsg Ma Mc B) (j : ℕ) : Fin Mc := if h : j < B then m.2 ⟨j, h⟩ else 0

/-- The index `l_j = a_{j-1}`, which is `0` in the first block. -/
def msgL (m : MarkovMsg Ma Mc B) : ℕ → Fin Ma
  | 0 => 0
  | j + 1 => msgA m j

end Msg

variable [NeZero Ma] [NeZero Mc] [NeZero n]
  (C : RelayBlock Ma Mc (Fin n → X₁) (Fin n → X) (Fin n → Y) (Fin n → Y₁))

/-- The state of the relay after `j` blocks, when it has received `Z 0, Z 1, …`. -/
def stZ (Z : ℕ → Fin n → Y₁) : ℕ → Fin Ma
  | 0 => 0
  | j + 1 => C.rDec (stZ Z j) (Z j)

omit [NeZero Mc] [NeZero n] in
lemma stZ_congr {Z Z' : ℕ → Fin n → Y₁} : ∀ j, (∀ j', j' < j → Z j' = Z' j') →
    stZ C Z j = stZ C Z' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [stZ]
    rw [stZ_congr j fun j' hj' => h j' (hj'.trans (Nat.lt_succ_self j)), h j (Nat.lt_succ_self j)]

/-- The received block `j`, from a prefix of the received symbols. -/
def getBlock {α : Type*} (d : α) {k : ℕ} (s : Fin k → α) (j : ℕ) : Fin n → α :=
  fun i => if h : i.val + n * j < k then s ⟨i.val + n * j, h⟩ else d

/-- The estimates of the `a_j` of the receiver, going backward: `hatA t` is the estimate of
`a_{B - t}`. -/
def hatA (Yb : ℕ → Fin n → Y) (B : ℕ) : ℕ → Fin Ma
  | 0 => 0
  | t + 1 => (C.dDec (hatA Yb B t) (Yb (B - t))).1

/-- **The code of `B + 1` blocks**, with block Markov encoding and backward decoding. -/
def RelayBlock.markov (e : Fin M ≃ MarkovMsg Ma Mc B) (d₁ : Y₁) (d : Y) :
    RCCode M ((B + 1) * n) X X₁ Y Y₁ where
  enc k w := C.x (msgL (e w) (k / n)) (msgA (e w) (k / n)) (msgC (e w) (k / n))
    ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩
  relay k s := C.s (stZ C (getBlock d₁ s) (k / n)) ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩
  dec y := e.symm (fun j => hatA C (getBlock d y) B (B - j),
    fun j => (C.dDec (hatA C (getBlock d y) B (B - j)) (getBlock d y j)).2)

omit [NeZero Mc] [NeZero n] in
/-- On a good run the relay always decodes the right index. -/
lemma stZ_eq_msgL (m : MarkovMsg Ma Mc B) {Z : ℕ → Fin n → Y₁}
    (hr : ∀ j, j ≤ B → C.rDec (msgL m j) (Z j) = msgA m j) :
    ∀ j, j ≤ B + 1 → stZ C Z j = msgL m j
  | 0, _ => rfl
  | j + 1, hj => by
    simp only [stZ, msgL]
    rw [stZ_eq_msgL m hr j (by omega), hr j (by omega)]

omit [NeZero n] in
/-- On a good run the receiver always decodes the right indices. -/
lemma hatA_eq_msgA (m : MarkovMsg Ma Mc B) {Yb : ℕ → Fin n → Y}
    (hd : ∀ j, j ≤ B → C.dDec (msgA m j) (Yb j) = (msgL m j, msgC m j)) :
    ∀ t, t ≤ B → hatA C Yb B t = msgA m (B - t)
  | 0, _ => by
    simp [hatA, msgA]
  | t + 1, ht => by
    simp only [hatA]
    rw [hatA_eq_msgA m hd t (by omega), hd (B - t) (by omega)]
    obtain ⟨u, hu⟩ : ∃ u, B - t = u + 1 := ⟨B - t - 1, by omega⟩
    rw [hu]
    simp only [msgL]
    congr 1
    omega

/-- On a good run the decoder finds the message. -/
lemma markov_dec_eq (e : Fin M ≃ MarkovMsg Ma Mc B) (d₁ : Y₁) (d : Y) (w : Fin M)
    {y : Fin ((B + 1) * n) → Y}
    (hd : ∀ j, j ≤ B → C.dDec (msgA (e w) j) (getBlock d y j) =
      (msgL (e w) j, msgC (e w) j)) :
    (C.markov (X := X) (X₁ := X₁) e d₁ d).dec y = w := by
  have hA := hatA_eq_msgA C (e w) hd
  simp only [RelayBlock.markov]
  rw [Equiv.symm_apply_eq]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · dsimp only
    rw [hA (B - j) (by omega)]
    have : B - (B - (j : ℕ)) = j := by omega
    simp only [this, msgA, j.2, dite_true]
  · dsimp only
    rw [hA (B - j) (by omega)]
    have : B - (B - (j : ℕ)) = j := by omega
    simp only [this]
    rw [hd j (by have := j.2; omega)]
    simp only [msgC, j.2, dite_true]

section Law

variable [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁] {W : X × X₁ → Y × Y₁ → ℝ}

/-- The received sequences, block by block. -/
def blockEquiv : (Fin ((B + 1) * n) → Y × Y₁) ≃ (Fin (B + 1) → (Fin n → Y) × (Fin n → Y₁)) where
  toFun z j := (fun i => (z (finProdFinEquiv (j, i))).1, fun i => (z (finProdFinEquiv (j, i))).2)
  invFun Z k := ((Z (finProdFinEquiv.symm k).1).1 (finProdFinEquiv.symm k).2,
    (Z (finProdFinEquiv.symm k).1).2 (finProdFinEquiv.symm k).2)
  left_inv z := by
    funext k
    have h : finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2) = k :=
      finProdFinEquiv.apply_symm_apply k
    simp only [h]
  right_inv Z := by
    funext j
    simp

/-- The sequences received by the relay, block by block, indexed by natural numbers. -/
def y₁Arr (d₁ : Y₁) (Z : Fin (B + 1) → (Fin n → Y) × (Fin n → Y₁)) (j : ℕ) : Fin n → Y₁ :=
  if h : j < B + 1 then (Z ⟨j, h⟩).2 else fun _ => d₁

/-- The law of the output of all the blocks, for a message. -/
def markovReal (W : X × X₁ → Y × Y₁ → ℝ) (m : MarkovMsg Ma Mc B) (d₁ : Y₁)
    (Z : Fin (B + 1) → (Fin n → Y) × (Fin n → Y₁)) : ℝ :=
  ∏ j : Fin (B + 1), relaySeq W n (C.x (msgL m j) (msgA m j) (msgC m j),
    C.s (stZ C (y₁Arr d₁ Z) j)) (Z j)

omit [Fintype X] [Fintype X₁] [NeZero Ma] in
lemma finProd_div_mod (j : Fin (B + 1)) (i : Fin n) :
    ((finProdFinEquiv (j, i) : Fin ((B + 1) * n)) : ℕ) / n = j ∧
      ((finProdFinEquiv (j, i) : Fin ((B + 1) * n)) : ℕ) % n = i := by
  have hval : ((finProdFinEquiv (j, i) : Fin ((B + 1) * n)) : ℕ) = i + n * j := rfl
  have hn := NeZero.pos n
  rw [hval]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt i.2, zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]

omit [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁] in
/-- The law of the code of all the blocks. -/
lemma markov_law (e : Fin M ≃ MarkovMsg Ma Mc B) (d₁ : Y₁) (d : Y) (w : Fin M)
    (z : Fin ((B + 1) * n) → Y × Y₁) :
    (C.markov (X := X) (X₁ := X₁) e d₁ d).law W ((B + 1) * n) (w, z) =
      uniformPMF (Fin M) w * markovReal C W (e w) d₁ (blockEquiv z) := by
  rw [RCCode.law, fbLaw_eq_prod]
  congr 1
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  refine prod_congr rfl fun j _ => ?_
  simp only [relaySeq]
  refine prod_congr rfl fun i _ => ?_
  obtain ⟨hdiv, hmod⟩ := finProd_div_mod (B := B) j i
  have hin : (⟨((finProdFinEquiv (j, i) : Fin ((B + 1) * n)) : ℕ) % n,
      Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = i := Fin.ext hmod
  have hst : stZ C (getBlock d₁ fun t : Fin (finProdFinEquiv (j, i) : Fin ((B + 1) * n)) =>
      (z ⟨t, t.2.trans (finProdFinEquiv (j, i)).2⟩).2) j = stZ C (y₁Arr d₁ (blockEquiv z)) j := by
    refine stZ_congr C j fun j' hj' => ?_
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
    simp only [getBlock, dite_eq_left hlt, y₁Arr, dite_eq_left hj'B]
    rfl
  simp only [RCCode.fbEnc, RelayBlock.markov]
  rw [hdiv, hin, hst]
  rfl

omit [Fintype X] [Fintype X₁] in
/-- The total law of a row. -/
lemma sum_markovReal (e : Fin M ≃ MarkovMsg Ma Mc B) (d₁ : Y₁) (d : Y) (hW : IsChannel W)
    (w : Fin M) : ∑ Z, markovReal C W (e w) d₁ Z = 1 := by
  classical
  have hM : (0 : ℝ) < M := by
    have : 0 < M := Fin.pos w
    exact_mod_cast this
  have hne : Nonempty (Fin M) := ⟨w⟩
  have h := congrFun (dist_fst_fbLaw (ν := uniformPMF (Fin M)) (W := W)
    (enc := (C.markov (X := X) (X₁ := X₁) e d₁ d).fbEnc) hW ((B + 1) * n)) w
  simp only [dist, Fintype.sum_prod_type] at h
  rw [Finset.sum_eq_single w (fun w' _ hw' => sum_eq_zero fun z _ => by simp [hw']) (by simp)] at h
  simp only [ite_true] at h
  have hl : ∀ z, fbLaw (uniformPMF (Fin M)) W (C.markov (X := X) (X₁ := X₁) e d₁ d).fbEnc
      ((B + 1) * n) (w, z) = uniformPMF (Fin M) w * markovReal C W (e w) d₁ (blockEquiv z) :=
    fun z => markov_law C e d₁ d w z
  simp_rw [hl, ← mul_sum] at h
  have hu : uniformPMF (Fin M) w ≠ 0 := by
    simp [uniformPMF, hM.ne']
  have h' : ∑ z, markovReal C W (e w) d₁ (blockEquiv z) = 1 :=
    mul_left_cancel₀ hu (h.trans (mul_one _).symm)
  rw [← h']
  exact (Fintype.sum_equiv blockEquiv _ _ fun _ => rfl).symm

omit [Fintype X] [Fintype X₁] in
/-- **The union bound over the blocks of the genie run.** For one message, the probability of error
of the code of all the blocks is at most the sum of the errors of its blocks. -/
theorem markov_row_le (e : Fin M ≃ MarkovMsg Ma Mc B) (d₁ : Y₁) (d : Y) (hW : IsChannel W)
    (w : Fin M) :
    ∑ z, markovReal C W (e w) d₁ (blockEquiv z) *
        ind ((C.markov (X := X) (X₁ := X₁) e d₁ d).dec (fun i => (z i).1) ≠ w) ≤
      ∑ j : Fin (B + 1), C.err (relaySeq W n) (msgL (e w) j) (msgA (e w) j) (msgC (e w) j) := by
  classical
  set m := e w with hm
  -- the genie run
  let ν : Fin (B + 1) → (Fin n → Y) × (Fin n → Y₁) → ℝ := fun j =>
    relaySeq W n (C.x (msgL m j) (msgA m j) (msgC m j), C.s (msgL m j))
  have hν : ∀ j, IsPMF (ν j) := fun j => relaySeq_isChannel hW n _
  have hgen := piLaw_isPMF hν
  let Good : (Fin (B + 1) → (Fin n → Y) × (Fin n → Y₁)) → Prop := fun Z =>
    ∀ j : Fin (B + 1), C.rDec (msgL m j) (Z j).2 = msgA m j ∧
      C.dDec (msgA m j) (Z j).1 = (msgL m j, msgC m j)
  -- on a good run the actual run is the genie run
  have hreal : ∀ Z, Good Z → markovReal C W m d₁ Z = piLaw ν Z := by
    intro Z hZ
    have hst : ∀ j : Fin (B + 1), stZ C (y₁Arr d₁ Z) j = msgL m j := fun j =>
      stZ_eq_msgL C m (fun j' hj' => by
        have hlt : j' < B + 1 := by omega
        have := (hZ ⟨j', hlt⟩).1
        simpa only [y₁Arr, dite_eq_left hlt] using this) j (by have := j.2; omega)
    simp only [markovReal, piLaw, ν]
    exact prod_congr rfl fun j _ => by rw [hst j]
  -- a good run decodes correctly
  have hdec : ∀ z, Good (blockEquiv z) →
      (C.markov (X := X) (X₁ := X₁) e d₁ d).dec (fun i => (z i).1) = w := by
    intro z hZ
    refine markov_dec_eq C e d₁ d w fun j hj => ?_
    have hlt : j < B + 1 := by omega
    have hb : getBlock d (fun i => (z i).1) j = (blockEquiv z ⟨j, hlt⟩).1 := by
      funext i
      have hi : i.val + n * j < (B + 1) * n := by
        have h₁ : n * (j + 1) ≤ n * (B + 1) := Nat.mul_le_mul_left _ hlt
        have h₂ := i.2
        rw [Nat.mul_add, Nat.mul_one] at h₁
        rw [Nat.mul_comm (B + 1) n]
        omega
      simp only [getBlock, dite_eq_left hi]
      rfl
    rw [hb]
    exact (hZ ⟨j, hlt⟩).2
  have hR0 : ∀ Z, 0 ≤ markovReal C W m d₁ Z := fun Z =>
    prod_nonneg fun j _ => (relaySeq_isChannel hW n _).nonneg _
  have hsumR : ∑ Z, markovReal C W m d₁ Z = 1 := sum_markovReal C e d₁ d hW w
  -- the chain of inequalities
  have h₁ : ∑ z, markovReal C W m d₁ (blockEquiv z) *
      ind ((C.markov (X := X) (X₁ := X₁) e d₁ d).dec (fun i => (z i).1) ≠ w) ≤
      ∑ Z, markovReal C W m d₁ Z * ind (¬ Good Z) := by
    rw [← Fintype.sum_equiv blockEquiv (fun z => markovReal C W m d₁ (blockEquiv z) *
      ind (¬ Good (blockEquiv z))) (fun Z => markovReal C W m d₁ Z * ind (¬ Good Z))
      fun _ => rfl]
    refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (ind_mono fun h hG => h (hdec z hG))
      (hR0 _)
  have hsplit : ∀ F : (Fin (B + 1) → (Fin n → Y) × (Fin n → Y₁)) → ℝ,
      ∑ Z, F Z * ind (¬ Good Z) = ∑ Z, F Z - ∑ Z, F Z * ind (Good Z) := by
    intro F
    rw [eq_sub_iff_add_eq, ← sum_add_distrib]
    refine sum_congr rfl fun Z _ => ?_
    by_cases hZ : Good Z
    · rw [ind_of_neg (not_not.mpr hZ), ind_of_pos hZ]
      ring
    · rw [ind_of_pos hZ, ind_of_neg hZ]
      ring
  have h₂ : ∑ Z, markovReal C W m d₁ Z * ind (¬ Good Z) = ∑ Z, piLaw ν Z * ind (¬ Good Z) := by
    rw [hsplit, hsplit, hsumR, hgen.sum_eq_one]
    congr 1
    refine sum_congr rfl fun Z _ => ?_
    by_cases hZ : Good Z
    · rw [hreal Z hZ]
    · rw [ind_of_neg hZ, mul_zero, mul_zero]
  let Fj : Fin (B + 1) → (Fin n → Y) × (Fin n → Y₁) → ℝ := fun j ζ =>
    ind (C.rDec (msgL m j) ζ.2 ≠ msgA m j) + ind (C.dDec (msgA m j) ζ.1 ≠ (msgL m j, msgC m j))
  have hFj : ∀ j ζ, 0 ≤ Fj j ζ := fun j ζ => add_nonneg (ind_nonneg _) (ind_nonneg _)
  have h₃ : ∑ Z, piLaw ν Z * ind (¬ Good Z) ≤ ∑ Z, piLaw ν Z * ∑ j, Fj j (Z j) := by
    refine sum_le_sum fun Z _ => mul_le_mul_of_nonneg_left ?_ (hgen.nonneg Z)
    by_cases hZ : Good Z
    · rw [ind_of_neg (not_not.mpr hZ)]
      exact sum_nonneg fun j _ => hFj j _
    · rw [ind_of_pos hZ]
      simp only [Good, not_forall] at hZ
      obtain ⟨j, hj⟩ := hZ
      refine le_trans ?_ (single_le_sum (f := fun j => Fj j (Z j)) (fun j _ => hFj j _)
        (mem_univ j))
      simp only [Fj]
      by_cases hr : C.rDec (msgL m j) (Z j).2 = msgA m j
      · have hd : C.dDec (msgA m j) (Z j).1 ≠ (msgL m j, msgC m j) := fun h => hj ⟨hr, h⟩
        rw [ind_of_pos hd]
        linarith [ind_nonneg (C.rDec (msgL m j) (Z j).2 ≠ msgA m j)]
      · rw [ind_of_pos hr]
        linarith [ind_nonneg (C.dDec (msgA m j) (Z j).1 ≠ (msgL m j, msgC m j))]
  have h₄ : ∑ Z, piLaw ν Z * ∑ j, Fj j (Z j) = ∑ j : Fin (B + 1), C.err (relaySeq W n)
      (msgL m j) (msgA m j) (msgC m j) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    exact sum_piLaw_mul_eval hν j (Fj j)
  rw [h₂] at h₁
  exact h₁.trans (h₃.trans (le_of_eq h₄))

end Law

/-! ### The average over the messages -/

section Avg

variable [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁] {V : (Fin n → X) × (Fin n → X₁) →
  (Fin n → Y) × (Fin n → Y₁) → ℝ}

omit [Fintype X] [Fintype X₁] [NeZero Ma] [NeZero Mc] [NeZero n] in
lemma RelayBlock.err_nonneg (hV : IsChannel V) (l a : Fin Ma) (c : Fin Mc) :
    0 ≤ C.err V l a c :=
  sum_nonneg fun z _ => mul_nonneg ((hV _).nonneg z) (add_nonneg (ind_nonneg _) (ind_nonneg _))

/-- The uniform law of a table of messages. -/
lemma uniform_table (K : ℕ) (f : Fin B → Fin K) :
    piLaw (fun _ : Fin B => uniformPMF (Fin K)) f = 1 / (K : ℝ) ^ B := by
  simp [piLaw, uniformPMF]

/-- The average over the messages of a function, as an iterated expectation over tables. -/
lemma avg_msg_eq (G : MarkovMsg Ma Mc B → ℝ) :
    (∑ m, G m) / ((Ma : ℝ) ^ B * (Mc : ℝ) ^ B) =
      ∑ f : Fin B → Fin Ma, piLaw (fun _ => uniformPMF (Fin Ma)) f *
        ∑ g : Fin B → Fin Mc, piLaw (fun _ => uniformPMF (Fin Mc)) g * G (f, g) := by
  have hMa : (Ma : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Ma
  have hMc : (Mc : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Mc
  simp only [uniform_table, Fintype.sum_prod_type, sum_div, mul_sum]
  refine sum_congr rfl fun f _ => sum_congr rfl fun g _ => ?_
  field_simp

omit [NeZero n] [Fintype X] [Fintype X₁] in
/-- Every block has an average error at most the average error of the three kinds of blocks. -/
lemma avg_block_le (hB : 0 < B) (hV : IsChannel V) {j : ℕ} (hj : j ≤ B) :
    (∑ m : MarkovMsg Ma Mc B, C.err V (msgL m j) (msgA m j) (msgC m j)) /
      ((Ma : ℝ) ^ B * (Mc : ℝ) ^ B) ≤ C.avgErr V := by
  classical
  have hMa : (0 : ℝ) < Ma := by exact_mod_cast NeZero.pos Ma
  have hMc : (0 : ℝ) < Mc := by exact_mod_cast NeZero.pos Mc
  have hu₁ : ∀ a : Fin Ma, uniformPMF (Fin Ma) a = 1 / (Ma : ℝ) := fun a => by simp [uniformPMF]
  have hu₂ : ∀ c : Fin Mc, uniformPMF (Fin Mc) c = 1 / (Mc : ℝ) := fun c => by simp [uniformPMF]
  have hP₁ : IsPMF (uniformPMF (Fin Ma)) := uniformPMF_isPMF
  have hP₂ : IsPMF (uniformPMF (Fin Mc)) := uniformPMF_isPMF
  have hT₁ : 0 ≤ (∑ a, ∑ c, C.err V 0 a c) / (Ma * Mc) :=
    div_nonneg (sum_nonneg fun a _ => sum_nonneg fun c _ => C.err_nonneg hV _ _ _) (by positivity)
  have hT₂ : 0 ≤ (∑ l, ∑ a, ∑ c, C.err V l a c) / (Ma * Ma * Mc) :=
    div_nonneg (sum_nonneg fun l _ => sum_nonneg fun a _ => sum_nonneg fun c _ =>
      C.err_nonneg hV _ _ _) (by positivity)
  have hT₃ : 0 ≤ (∑ l, C.err V l 0 0) / Ma :=
    div_nonneg (sum_nonneg fun l _ => C.err_nonneg hV _ _ _) hMa.le
  rw [avg_msg_eq]
  have hEg : ∀ (K : ℝ) (_ : True), ∑ g : Fin B → Fin Mc,
      piLaw (fun _ => uniformPMF (Fin Mc)) g * K = K := fun K _ => by
    rw [← sum_mul, (piLaw_isPMF fun _ => hP₂).sum_eq_one, one_mul]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- the first block
    let i : Fin B := ⟨0, hB⟩
    have hval : ∀ (f : Fin B → Fin Ma) (g : Fin B → Fin Mc),
        C.err V (msgL (f, g) 0) (msgA (f, g) 0) (msgC (f, g) 0) = C.err V 0 (f i) (g i) := by
      intro f g
      simp [msgL, msgA, msgC, hB, i]
    simp_rw [hval]
    have hin : ∀ a : Fin Ma, ∑ g : Fin B → Fin Mc, piLaw (fun _ => uniformPMF (Fin Mc)) g *
        C.err V 0 a (g i) = (∑ c, C.err V 0 a c) / Mc := fun a => by
      rw [sum_piLaw_mul_eval (ν := fun _ : Fin B => uniformPMF (Fin Mc)) (fun _ => hP₂) i
        (fun c => C.err V 0 a c), sum_div]
      exact sum_congr rfl fun c _ => by rw [hu₂]; ring
    simp_rw [hin]
    rw [sum_piLaw_mul_eval (ν := fun _ : Fin B => uniformPMF (Fin Ma)) (fun _ => hP₁) i
      (fun a => (∑ c, C.err V 0 a c) / Mc)]
    have : ∑ a : Fin Ma, uniformPMF (Fin Ma) a * ((∑ c, C.err V 0 a c) / Mc) =
        (∑ a, ∑ c, C.err V 0 a c) / (Ma * Mc) := by
      rw [sum_div]
      refine sum_congr rfl fun a _ => ?_
      rw [hu₁]
      field_simp
    rw [this, RelayBlock.avgErr]
    linarith
  · obtain ⟨u, rfl⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    let i₀ : Fin B := ⟨u, by omega⟩
    by_cases hlast : u + 1 < B
    · -- a block in the middle
      let i₁ : Fin B := ⟨u + 1, hlast⟩
      have hne : i₀ ≠ i₁ := fun h => by
        have := congrArg Fin.val h
        simp [i₀, i₁] at this
      have hval : ∀ (f : Fin B → Fin Ma) (g : Fin B → Fin Mc),
          C.err V (msgL (f, g) (u + 1)) (msgA (f, g) (u + 1)) (msgC (f, g) (u + 1)) =
            C.err V (f i₀) (f i₁) (g i₁) := by
        intro f g
        have hu : u < B := by omega
        simp [msgL, msgA, msgC, hlast, hu, i₀, i₁]
      simp_rw [hval]
      have hin : ∀ l a : Fin Ma, ∑ g : Fin B → Fin Mc, piLaw (fun _ => uniformPMF (Fin Mc)) g *
          C.err V l a (g i₁) = (∑ c, C.err V l a c) / Mc := fun l a => by
        rw [sum_piLaw_mul_eval (ν := fun _ : Fin B => uniformPMF (Fin Mc)) (fun _ => hP₂) i₁
          (fun c => C.err V l a c), sum_div]
        exact sum_congr rfl fun c _ => by rw [hu₂]; ring
      simp_rw [hin]
      rw [sum_piLaw_mul_eval₂ (ν := fun _ : Fin B => uniformPMF (Fin Ma)) (fun _ => hP₁) hne
        (fun l a => (∑ c, C.err V l a c) / Mc)]
      have : ∑ l : Fin Ma, ∑ a : Fin Ma, uniformPMF (Fin Ma) l * uniformPMF (Fin Ma) a *
          ((∑ c, C.err V l a c) / Mc) = (∑ l, ∑ a, ∑ c, C.err V l a c) / (Ma * Ma * Mc) := by
        rw [sum_div]
        refine sum_congr rfl fun l _ => ?_
        rw [sum_div]
        refine sum_congr rfl fun a _ => ?_
        rw [hu₁, hu₁]
        field_simp
      rw [this, RelayBlock.avgErr]
      linarith
    · -- the last block
      have hub : u + 1 = B := by omega
      have hval : ∀ (f : Fin B → Fin Ma) (g : Fin B → Fin Mc),
          C.err V (msgL (f, g) (u + 1)) (msgA (f, g) (u + 1)) (msgC (f, g) (u + 1)) =
            C.err V (f i₀) 0 0 := by
        intro f g
        have hu : u < B := by omega
        simp [msgL, msgA, msgC, hlast, hu, i₀]
      simp_rw [hval]
      have hconst : ∀ f : Fin B → Fin Ma, ∑ g : Fin B → Fin Mc,
          piLaw (fun _ => uniformPMF (Fin Mc)) g * C.err V (f i₀) 0 0 = C.err V (f i₀) 0 0 :=
        fun f => hEg _ trivial
      have hstep : ∑ f : Fin B → Fin Ma, piLaw (fun _ => uniformPMF (Fin Ma)) f *
          ∑ g : Fin B → Fin Mc, piLaw (fun _ => uniformPMF (Fin Mc)) g * C.err V (f i₀) 0 0 =
          ∑ f : Fin B → Fin Ma, piLaw (fun _ => uniformPMF (Fin Ma)) f * C.err V (f i₀) 0 0 :=
        sum_congr rfl fun f _ => congrArg _ (hconst f)
      refine (le_of_eq hstep).trans ?_
      rw [sum_piLaw_mul_eval (ν := fun _ : Fin B => uniformPMF (Fin Ma)) (fun _ => hP₁) i₀
        (fun l => C.err V l 0 0)]
      have : ∑ l : Fin Ma, uniformPMF (Fin Ma) l * C.err V l 0 0 = (∑ l, C.err V l 0 0) / Ma := by
        rw [sum_div]
        refine sum_congr rfl fun l _ => ?_
        rw [hu₁]
        ring
      rw [this, RelayBlock.avgErr]
      linarith

omit [Fintype X] [Fintype X₁] in
/-- **The error of the code of all the blocks.** -/
theorem RelayBlock.markov_errProb_le {W : X × X₁ → Y × Y₁ → ℝ} (hB : 0 < B) (hW : IsChannel W)
    (e : Fin M ≃ MarkovMsg Ma Mc B) (d₁ : Y₁) (d : Y) :
    (C.markov (X := X) (X₁ := X₁) e d₁ d).errProb W ≤
      ((B : ℝ) + 1) * C.avgErr (relaySeq W n) := by
  classical
  have hcard : (M : ℝ) = (Ma : ℝ) ^ B * (Mc : ℝ) ^ B := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_fun] at h
    rw [h]
    push_cast
    rfl
  have hMa : (0 : ℝ) < Ma := by exact_mod_cast NeZero.pos Ma
  have hMc : (0 : ℝ) < Mc := by exact_mod_cast NeZero.pos Mc
  have hMpos : (0 : ℝ) < M := by rw [hcard]; positivity
  have hu : ∀ w : Fin M, uniformPMF (Fin M) w = 1 / (M : ℝ) := fun w => by simp [uniformPMF]
  -- the error as a sum over the messages
  have h₁ : (C.markov (X := X) (X₁ := X₁) e d₁ d).errProb W = ∑ w : Fin M, (1 / (M : ℝ)) *
      ∑ z, markovReal C W (e w) d₁ (blockEquiv z) *
        ind ((C.markov (X := X) (X₁ := X₁) e d₁ d).dec (fun i => (z i).1) ≠ w) := by
    simp only [RCCode.errProb, InfoTheory.errProb, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun w _ => sum_congr rfl fun z _ => ?_
    rw [markov_law, hu]
    by_cases h : (C.markov (X := X) (X₁ := X₁) e d₁ d).dec (fun i => (z i).1) = w
    · have hne : ¬ (C.markov (X := X) (X₁ := X₁) e d₁ d).dec (fun i => (z i).1) ≠ w := not_not.mpr h
      rw [ind_of_neg hne, mul_zero, mul_zero]
      exact ite_eq_right hne
    · rw [ind_of_pos h, mul_one]
      exact ite_eq_left h
  have hV := relaySeq_isChannel hW n
  rw [h₁, ← mul_sum, one_div, inv_mul_le_iff₀ hMpos]
  calc _ ≤ ∑ w : Fin M, ∑ j : Fin (B + 1), C.err (relaySeq W n) (msgL (e w) j) (msgA (e w) j)
        (msgC (e w) j) := sum_le_sum fun w _ => markov_row_le C e d₁ d hW w
    _ = ∑ j : Fin (B + 1), ∑ m : MarkovMsg Ma Mc B, C.err (relaySeq W n) (msgL m j) (msgA m j)
        (msgC m j) := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        exact Fintype.sum_equiv e _ _ fun _ => rfl
    _ ≤ ∑ _j : Fin (B + 1), (M : ℝ) * C.avgErr (relaySeq W n) := by
        refine sum_le_sum fun j _ => ?_
        have := avg_block_le C (Ma := Ma) (Mc := Mc) (V := relaySeq W n) hB hV
          (j := j) (by have := j.2; omega)
        rwa [div_le_iff₀ (by positivity), ← hcard, mul_comm] at this
    _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Avg

end Markov

end InfoTheory
