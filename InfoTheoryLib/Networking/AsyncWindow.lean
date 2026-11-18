/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Networking.AsyncMAC

/-!
# The slots of a window of the asynchronous multiple-access channel

The time structure of the code of Theorem 2 of Lecture 24 of El Gamal and Kim. A block of `n` slots
is divided into segments of `k` slots, and `n` is between `(b + 2) k` and `(b + 3) k`. Segment `0`
and the segments after segment `b` are pilots, and segments `1, …, b` carry the sub-messages. The
pilots of one sender are long enough that some segment boundary of the other sender falls in them,
so the test set `asyncTest dA dB` contains all the sub-message slots of sender `A`, and it contains
only whole segments of sender `B`.

## Main definitions

* `asyncPos d t`, `asyncOff d t`: the position in its block and the block offset of slot `t` of the
  window, for a sender with delay `d`.
* `asyncSeg k b p`: the segment of a position.
* `asyncMsg b j`: segment `j` carries a sub-message.
* `asyncTest k dA dB`: the slots read by the decoder of sender `A`.

## Main statements

* `asyncPos_inj`: slots closer than `n` have different positions.
* `le_card_filter_segA`: the test set contains a whole message segment of sender `A`.
* `le_card_filter_segB`: it contains a whole message segment of sender `B` or none of it.
* `asyncOff_eq_of_seg_eq`: a segment of sender `B` lies in one block within the test set.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 24
-/

@[expose] public noncomputable section

open Finset

namespace InfoTheory

variable {n : ℕ}

/-- The position of slot `t` of the window in its block, for a sender with delay `d`. -/
def asyncPos (d : Fin n) (t : Fin (2 * n - 1)) : Fin n :=
  ⟨((t : ℕ) + n - d) % n, Nat.mod_lt _ d.pos⟩

/-- The block offset of slot `t` of the window, for a sender with delay `d`. -/
def asyncOff (d : Fin n) (t : Fin (2 * n - 1)) : Fin 3 :=
  ⟨((t : ℕ) + n - d) / n, async_div_lt d t⟩

lemma asyncInput_eq {M : ℕ} {α : Type*} (enc : Fin M → Fin n → α) (m : Fin 3 → Fin M) (d : Fin n)
    (t : Fin (2 * n - 1)) : asyncInput enc m d t = enc (m (asyncOff d t)) (asyncPos d t) := rfl

lemma asyncPos_spec (d : Fin n) (t : Fin (2 * n - 1)) :
    (t : ℕ) + n - d = (asyncOff d t : ℕ) * n + asyncPos d t := by
  simp only [asyncOff, asyncPos]
  exact (Nat.div_add_mod' _ _).symm

/-- The position and the offset are determined by a division with remainder. -/
lemma asyncPos_eq_of (d : Fin n) (t : Fin (2 * n - 1)) {o r : ℕ}
    (h : (t : ℕ) + n - d = o * n + r) (hr : r < n) :
    (asyncPos d t : ℕ) = r ∧ (asyncOff d t : ℕ) = o := by
  have hn : 0 < n := d.pos
  have h1 := (Nat.div_mod_unique hn).2 (⟨by rw [h, Nat.mul_comm o n, Nat.add_comm], hr⟩ :
    r + n * o = (t : ℕ) + n - d ∧ r < n)
  exact ⟨h1.2, h1.1⟩

/-- **Slots closer than `n` have different positions.** -/
lemma asyncPos_inj (d : Fin n) {t t' : Fin (2 * n - 1)} (h : asyncPos d t = asyncPos d t')
    (hc : (t : ℕ) < t' + n) (hc' : (t' : ℕ) < t + n) : t = t' := by
  have h1 := asyncPos_spec d t
  have h2 := asyncPos_spec d t'
  have h3 : (asyncPos d t : ℕ) = asyncPos d t' := congrArg Fin.val h
  have ho := (asyncOff d t).isLt
  have ho' := (asyncOff d t').isLt
  have hd := d.isLt
  have hp := (asyncPos d t).isLt
  refine Fin.ext ?_
  generalize (asyncOff d t : ℕ) = o at *
  generalize (asyncOff d t' : ℕ) = o' at *
  interval_cases o <;> interval_cases o' <;> omega

/-- In the block of a sender, the position is the time since the start of the block. -/
lemma asyncPos_of_mem (d : Fin n) {t : Fin (2 * n - 1)} (h1 : (d : ℕ) ≤ t) (h2 : (t : ℕ) < d + n) :
    (asyncPos d t : ℕ) = (t : ℕ) - d ∧ (asyncOff d t : ℕ) = 1 := by
  refine asyncPos_eq_of d t ?_ (by omega)
  omega

/-- The segment of a position. -/
def asyncSeg (k b p : ℕ) : Fin (b + 3) := ⟨min (p / k) (b + 2), by omega⟩

/-- Segments `1, …, b` carry the sub-messages. -/
def asyncMsg (b : ℕ) : Finset (Fin (b + 3)) := univ.filter fun j => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ b

variable {k b : ℕ}

lemma asyncSeg_val (hu : n < (b + 3) * k) {p : ℕ} (hp : p < n) :
    (asyncSeg k b p : ℕ) = p / k := by
  have h : p / k < b + 3 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  simp only [asyncSeg]
  omega

/-- The slot `t` of the test set of sender `A`: the whole segment of sender `B` containing `t` lies
in the current block of sender `A`. -/
def asyncTest (k : ℕ) (dA dB : Fin n) : Finset (Fin (2 * n - 1)) :=
  univ.filter fun t => (dA : ℕ) + (asyncPos dB t : ℕ) % k ≤ t ∧
    (t : ℕ) + k ≤ dA + n + (asyncPos dB t : ℕ) % k

lemma mem_asyncTest {dA dB : Fin n} {t : Fin (2 * n - 1)} :
    t ∈ asyncTest k dA dB ↔ (dA : ℕ) + (asyncPos dB t : ℕ) % k ≤ t ∧
      (t : ℕ) + k ≤ dA + n + (asyncPos dB t : ℕ) % k := by
  simp [asyncTest]

/-- The test set lies in the current block of sender `A`. -/
lemma asyncTest_bounds (hk : 0 < k) {dA dB : Fin n} {t : Fin (2 * n - 1)}
    (h : t ∈ asyncTest k dA dB) : (dA : ℕ) ≤ t ∧ (t : ℕ) < dA + n := by
  rw [mem_asyncTest] at h
  have := Nat.mod_lt (asyncPos dB t : ℕ) hk
  omega

/-- Two slots of the test set are closer than `n`. -/
lemma asyncTest_close (hk : 0 < k) {dA dB : Fin n} {t t' : Fin (2 * n - 1)}
    (h : t ∈ asyncTest k dA dB) (h' : t' ∈ asyncTest k dA dB) : (t : ℕ) < t' + n := by
  have h1 := asyncTest_bounds hk h
  have h2 := asyncTest_bounds hk h'
  omega

/-- All the positions of a sender are different in the test set. -/
lemma asyncPos_injOn_test (hk : 0 < k) (d : Fin n) {dA dB : Fin n} {t t' : Fin (2 * n - 1)}
    (h : t ∈ asyncTest k dA dB) (h' : t' ∈ asyncTest k dA dB) (he : asyncPos d t = asyncPos d t') :
    t = t' :=
  asyncPos_inj d he (asyncTest_close hk h h') (asyncTest_close hk h' h)

/-- **The test set contains a whole message segment of sender `A`.** -/
lemma le_card_filter_segA (hk : 0 < k) (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k) (dA dB : Fin n)
    {j : Fin (b + 3)} (hj : j ∈ asyncMsg b) :
    k ≤ ((asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dA t) = j).card := by
  simp only [asyncMsg, mem_filter, mem_univ, true_and] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hdA := dA.isLt
  have hkj : k ≤ (j : ℕ) * k := by nlinarith
  have hsucc : ((j : ℕ) + 1) * k = (j : ℕ) * k + k := by ring
  have hb1 : ((j : ℕ) + 1) * k ≤ (b + 1) * k := Nat.mul_le_mul_right _ (by omega)
  have hb2 : (b + 2) * k = (b + 1) * k + k := by ring
  -- The slots of the segment.
  have hT : ∀ i : Fin k, (dA : ℕ) + (j : ℕ) * k + i < 2 * n - 1 := by
    intro i
    have := i.isLt
    omega
  set f : Fin k → Fin (2 * n - 1) := fun i => ⟨(dA : ℕ) + (j : ℕ) * k + i, hT i⟩ with hf
  have hinj : Function.Injective f := by
    intro i i' h
    have := congrArg Fin.val h
    simp only [hf] at this
    exact Fin.ext (by omega)
  have hmem : ∀ i : Fin k, f i ∈ (asyncTest k dA dB).filter
      fun t => asyncSeg k b (asyncPos dA t) = j := by
    intro i
    have hi := i.isLt
    have hq := Nat.mod_lt (asyncPos dB (f i) : ℕ) hk
    have hft : ((f i : Fin (2 * n - 1)) : ℕ) = (dA : ℕ) + (j : ℕ) * k + i := rfl
    rw [mem_filter, mem_asyncTest, hft]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hp := (asyncPos_of_mem dA (t := f i) (by omega) (by omega)).1
    rw [hft] at hp
    refine Fin.ext ?_
    rw [asyncSeg_val hu (asyncPos dA (f i)).isLt, hp]
    have h1 : (dA : ℕ) + (j : ℕ) * k + i - dA = i + k * (j : ℕ) := by
      rw [Nat.mul_comm k]
      omega
    rw [h1, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hi, zero_add]
  calc k = (univ : Finset (Fin k)).card := by simp
    _ ≤ _ := card_le_card_of_injOn f (fun i _ => hmem i) hinj.injOn

/-- **The test set contains a whole message segment of sender `B` or none of it.** -/
lemma le_card_filter_segB (hk : 0 < k) (hl : (b + 2) * k ≤ n) (hu : n < (b + 3) * k)
    (dA dB : Fin n) {j : Fin (b + 3)} (hj : j ∈ asyncMsg b)
    (hne : ∃ t ∈ asyncTest k dA dB, asyncSeg k b (asyncPos dB t) = j) :
    k ≤ ((asyncTest k dA dB).filter fun t => asyncSeg k b (asyncPos dB t) = j).card := by
  simp only [asyncMsg, mem_filter, mem_univ, true_and] at hj
  obtain ⟨hj1, hj2⟩ := hj
  obtain ⟨t, ht, hts⟩ := hne
  have hdA := dA.isLt
  have hdB := dB.isLt
  have htl := t.isLt
  have hval : (asyncPos dB t : ℕ) / k = j := by
    rw [← asyncSeg_val hu (asyncPos dB t).isLt, hts]
  set q := (asyncPos dB t : ℕ) % k with hq
  have hqk : q < k := Nat.mod_lt _ hk
  have hpos : (asyncPos dB t : ℕ) = (j : ℕ) * k + q := by
    rw [← hval, hq]
    exact (Nat.div_add_mod' _ _).symm
  have ht' := mem_asyncTest.1 ht
  rw [← hq] at ht'
  have hsucc : ((j : ℕ) + 1) * k = (j : ℕ) * k + k := by ring
  have hb1 : ((j : ℕ) + 1) * k ≤ (b + 1) * k := Nat.mul_le_mul_right _ (by omega)
  have hb2 : (b + 2) * k = (b + 1) * k + k := by ring
  have hT : ∀ i : Fin k, (t : ℕ) - q + i < 2 * n - 1 := by
    intro i
    have := i.isLt
    omega
  set f : Fin k → Fin (2 * n - 1) := fun i => ⟨(t : ℕ) - q + i, hT i⟩ with hf
  have hinj : Function.Injective f := by
    intro i i' h
    have := congrArg Fin.val h
    simp only [hf] at this
    exact Fin.ext (by omega)
  have hspec := asyncPos_spec dB t
  have hoff := (asyncOff dB t).isLt
  have hmem : ∀ i : Fin k, f i ∈ (asyncTest k dA dB).filter
      fun t => asyncSeg k b (asyncPos dB t) = j := by
    intro i
    have hi := i.isLt
    have hft : ((f i : Fin (2 * n - 1)) : ℕ) = (t : ℕ) - q + i := rfl
    have hp : (asyncPos dB (f i) : ℕ) = (j : ℕ) * k + i := by
      refine (asyncPos_eq_of dB (f i) (o := (asyncOff dB t : ℕ)) ?_ (by omega)).1
      rw [hft]
      rw [hpos] at hspec
      generalize (asyncOff dB t : ℕ) = o at *
      interval_cases o <;> omega
    have hdm : ((j : ℕ) * k + i) % k = i ∧ ((j : ℕ) * k + i) / k = j := by
      have h1 := (Nat.div_mod_unique hk).2 (⟨by rw [Nat.mul_comm k, Nat.add_comm], hi⟩ :
        (i : ℕ) + k * (j : ℕ) = (j : ℕ) * k + i ∧ (i : ℕ) < k)
      exact ⟨h1.2, h1.1⟩
    rw [mem_filter, mem_asyncTest, hft, hp, hdm.1]
    refine ⟨⟨by omega, by omega⟩, Fin.ext ?_⟩
    rw [asyncSeg_val hu (by omega), hdm.2]
  calc k = (univ : Finset (Fin k)).card := by simp
    _ ≤ _ := card_le_card_of_injOn f (fun i _ => hmem i) hinj.injOn

/-- **A segment of sender `B` lies in one block within the test set.** -/
lemma asyncOff_eq_of_seg_eq (hk : 0 < k) (hu : n < (b + 3) * k) {dA dB : Fin n}
    {t t' : Fin (2 * n - 1)} (ht : t ∈ asyncTest k dA dB) (ht' : t' ∈ asyncTest k dA dB)
    (hs : asyncSeg k b (asyncPos dB t) = asyncSeg k b (asyncPos dB t')) :
    asyncOff dB t = asyncOff dB t' := by
  have hval : (asyncPos dB t : ℕ) / k = (asyncPos dB t' : ℕ) / k := by
    rw [← asyncSeg_val hu (asyncPos dB t).isLt, ← asyncSeg_val hu (asyncPos dB t').isLt, hs]
  have h1 := (Nat.div_add_mod' (asyncPos dB t : ℕ) k)
  have h2 := (Nat.div_add_mod' (asyncPos dB t' : ℕ) k)
  rw [← hval] at h2
  have hm1 := mem_asyncTest.1 ht
  have hm2 := mem_asyncTest.1 ht'
  have hs1 := asyncPos_spec dB t
  have hs2 := asyncPos_spec dB t'
  have ho1 := (asyncOff dB t).isLt
  have ho2 := (asyncOff dB t').isLt
  have hdB := dB.isLt
  have hq1 := Nat.mod_lt (asyncPos dB t : ℕ) hk
  have hq2 := Nat.mod_lt (asyncPos dB t' : ℕ) hk
  have hd1 := (asyncPos dB t).isLt
  have hd2 := (asyncPos dB t').isLt
  refine Fin.ext ?_
  generalize (asyncOff dB t : ℕ) = o at *
  generalize (asyncOff dB t' : ℕ) = o' at *
  generalize (asyncPos dB t : ℕ) / k * k = c at *
  interval_cases o <;> interval_cases o' <;> omega

/-- **The shift between a hypothesized delay and the true one is well defined within a short
segment.** If the position of `t₁` for delay `d` equals the position of `t₁'` for delay `d'`, and
likewise for `t₂`, and the two time differences are small, then they are equal. -/
lemma asyncPos_shift_unique {d d' : Fin n} {t₁ t₁' t₂ t₂' : Fin (2 * n - 1)}
    (h₁ : asyncPos d t₁ = asyncPos d' t₁') (h₂ : asyncPos d t₂ = asyncPos d' t₂')
    (hc : ∀ x y : ℕ, x = t₁ ∨ x = t₁' ∨ x = t₂ ∨ x = t₂' → y = t₁ ∨ y = t₁' ∨ y = t₂ ∨ y = t₂' →
      2 * x < 2 * y + n) :
    (t₁' : ℕ) + t₂ = t₂' + t₁ := by
  have e1 : (asyncPos d t₁ : ℕ) = asyncPos d' t₁' := congrArg Fin.val h₁
  have e2 : (asyncPos d t₂ : ℕ) = asyncPos d' t₂' := congrArg Fin.val h₂
  have s1 := asyncPos_spec d t₁
  have s2 := asyncPos_spec d' t₁'
  have s3 := asyncPos_spec d t₂
  have s4 := asyncPos_spec d' t₂'
  have o1 := (asyncOff d t₁).isLt
  have o2 := (asyncOff d' t₁').isLt
  have o3 := (asyncOff d t₂).isLt
  have o4 := (asyncOff d' t₂').isLt
  have hd := d.isLt
  have hd' := d'.isLt
  have c1 := hc t₁ t₁' (by simp) (by simp)
  have c2 := hc t₁' t₁ (by simp) (by simp)
  have c3 := hc t₂ t₂' (by simp) (by simp)
  have c4 := hc t₂' t₂ (by simp) (by simp)
  generalize (asyncOff d t₁ : ℕ) = a at *
  generalize (asyncOff d' t₁' : ℕ) = a' at *
  generalize (asyncOff d t₂ : ℕ) = c at *
  generalize (asyncOff d' t₂' : ℕ) = c' at *
  interval_cases a <;> interval_cases a' <;> interval_cases c <;> interval_cases c' <;> omega

end InfoTheory
