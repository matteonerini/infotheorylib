/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyMultiNodeConverse

/-!
# Secret key agreement with many nodes: random binning

The random binning of pages 23-54 and 23-55 of Lecture 23 of El Gamal and Kim. Each node sends a bin
of its sequence, and the key is a random bin of all the sequences. Each node recovers all the
sequences from its own sequence, `Zⁿ` and the public indices. As for two nodes, the key is analyzed
through a decoder that knows `Zⁿ`, the public indices and the key.

## Main definitions

* `colNode`, `colKey`: the bounds on the collisions of the decoders.

## Main statements

* `card_rivals_le`: the number of typical sequences with the same `Zⁿ` that differ exactly on `S`.
* `exists_multiBin`: the random binning bound.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {N n : ℕ} {α : Fin N → Type*} [∀ j, Fintype (α j)] {γ : Type*} [Fintype γ]
  {p : mLetter α γ → ℝ} {M : Fin N → ℕ} {Kb : ℕ}

open Classical in
/-- The sequences on which `x'` differs from `x`. -/
def diffSet (x' x : Fin n → ∀ j, α j) : Finset (Fin N) :=
  univ.filter fun j => (fun i => x' i j) ≠ fun i => x i j

open Classical in
/-- The typical sequences with the same `Zⁿ`, except `x`. -/
def rivalSet (t : ℝ) (p : mLetter α γ → ℝ) (x : Fin n → ∀ j, α j) (z : Fin n → γ) :
    Finset (Fin n → ∀ j, α j) :=
  (univ.filter fun x' => zipSeq x' z ∈ robustTypicalSet p n t).erase x

open Classical in
/-- **Page 23-55 of [elgamal2010].** The number of typical sequences with the same `Zⁿ` that differ
from `x` exactly on `S` is at most `e^{n(H(X(S) | X(Sᶜ), Z) + δ)}`. -/
lemma card_rivals_le (hp : IsPMF p) (t : ℝ) (x : Fin n → ∀ j, α j) (z : Fin n → γ)
    (S : Finset (Fin N)) :
    (((rivalSet t p x z).filter fun x' => diffSet x' x = S).card : ℝ) ≤
      exp (n * (zCondH p S + t * zCondH p S)) := by
  set fD : mLetter α γ → (∀ j, Option (α j)) × γ := fun a => (maskL Sᶜ a.1, a.2) with hfD
  set fS : mLetter α γ → ∀ j, Option (α j) := fun a => maskL S a.1 with hfS
  have hJ : IsPMF (dist p (pair fD fS)) := hp.dist _
  have hz : zCondH p S = H[Prod.snd | Prod.fst ; dist p (pair fD fS)] := by
    refine condEntropy_eq_of_dist_pair_eq hp hJ ?_
    rw [dist_pair_fst_snd]
  have hb := card_condRobustTypicalSet_le hJ t (fun i => fD (x i, z i))
  rw [← hz] at hb
  refine le_trans ?_ hb
  norm_cast
  refine card_le_card_of_injOn (fun x' i => fS (x' i, z i)) ?_ ?_
  · intro x' hx'
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 hx')
    have hT : zipSeq x' z ∈ robustTypicalSet p n t := (mem_filter.1 (mem_erase.1 hm.1).2).2
    have key : ∀ a : Fin N, a ∉ S → (fun i => x' i a) = fun i => x i a := fun a ha => by
      by_contra hne
      exact ha (by
        rw [← hm.2]
        exact Finset.mem_filter.2 ⟨mem_univ _, hne⟩)
    have hrest : (fun i => fD (x' i, z i)) = fun i => fD (x i, z i) := by
      funext i
      refine Prod.ext (funext fun j => ?_) rfl
      by_cases hj : j ∈ S
      · have hj' : j ∉ Sᶜ := by simpa using hj
        simp [hfD, maskL, hj']
      · have hj' : j ∈ Sᶜ := by simpa using hj
        have := congrFun (key j hj) i
        simp [hfD, maskL, hj', this]
    refine Finset.mem_coe.2 (mem_condRobustTypicalSet.2 ?_)
    have h := comp_mem_robustTypicalSet hT (pair fD fS)
    have e : zipSeq (fun i => fD (x i, z i)) (fun i => fS (x' i, z i)) =
        (pair fD fS) ∘ zipSeq x' z := by
      funext i
      exact Prod.ext (congrFun hrest i).symm rfl
    rw [e]
    exact h
  · intro x₁ hx₁ x₂ hx₂ he
    have hm₁ := Finset.mem_filter.1 (Finset.mem_coe.1 hx₁)
    have hm₂ := Finset.mem_filter.1 (Finset.mem_coe.1 hx₂)
    funext i
    funext j
    by_cases hj : j ∈ S
    · have := congrFun (congrFun he i) j
      simpa [hfS, maskL, hj] using this
    · have h1 : (fun i => x₁ i j) = fun i => x i j := by
        by_contra hne
        exact hj (by
          rw [← hm₁.2]
          exact Finset.mem_filter.2 ⟨mem_univ _, hne⟩)
      have h2 : (fun i => x₂ i j) = fun i => x i j := by
        by_contra hne
        exact hj (by
          rw [← hm₂.2]
          exact Finset.mem_filter.2 ⟨mem_univ _, hne⟩)
      exact (congrFun h1 i).trans (congrFun h2 i).symm

open Classical in
/-- **Page 23-55 of [elgamal2010].** The bound on the collisions of the decoder of the node `k`. -/
def colNode (p : mLetter α γ → ℝ) (M : Fin N → ℕ) (n : ℕ) (t : ℝ) (k : Fin N) : ℝ :=
  ∑ S ∈ univ.filter fun S : Finset (Fin N) => S.Nonempty ∧ k ∉ S,
    exp (n * (zCondH p S + t * zCondH p S)) * ∏ j ∈ S, (1 / (M j : ℝ))

open Classical in
/-- **Page 23-55 of [elgamal2010].** The bound on the collisions of the decoder that knows the
key. -/
def colKey (p : mLetter α γ → ℝ) (M : Fin N → ℕ) (Kb n : ℕ) (t : ℝ) : ℝ :=
  ∑ S ∈ univ.filter fun S : Finset (Fin N) => S.Nonempty,
    exp (n * (zCondH p S + t * zCondH p S)) * (∏ j ∈ S, (1 / (M j : ℝ))) * (1 / (Kb : ℝ))

open Classical in
/-- The collisions over the rivals of the decoder of the node `k`. -/
lemma sum_rivals_node_le (hp : IsPMF p) (t : ℝ) (k : Fin N) (x : Fin n → ∀ j, α j)
    (z : Fin n → γ) :
    ∑ x' ∈ (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k),
      ∏ j ∈ diffSet x' x, (1 / (M j : ℝ)) ≤ colNode p M n t k := by
  set R := (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k) with hR
  have hmaps : ∀ x' ∈ R, diffSet x' x ∈ univ.filter fun S : Finset (Fin N) => S.Nonempty ∧ k ∉ S :=
    fun x' hx' => by
      have h₁ := mem_filter.1 hx'
      refine Finset.mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
      · by_contra hne
        refine (mem_erase.1 h₁.1).1 ?_
        funext i
        funext j
        have hj : (fun i => x' i j) = fun i => x i j := by
          by_contra h
          exact hne ⟨j, Finset.mem_filter.2 ⟨mem_univ _, h⟩⟩
        exact congrFun hj i
      · intro hk
        exact (mem_filter.1 hk).2 (funext h₁.2)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun S _ => ?_
  have hprod0 : (0 : ℝ) ≤ ∏ j ∈ S, (1 / (M j : ℝ)) := prod_nonneg fun _ _ => by positivity
  calc ∑ x' ∈ R.filter (fun x' => diffSet x' x = S), ∏ j ∈ diffSet x' x, (1 / (M j : ℝ))
      = ∑ _x' ∈ R.filter (fun x' => diffSet x' x = S), ∏ j ∈ S, (1 / (M j : ℝ)) :=
        sum_congr rfl fun x' hx' => by rw [(Finset.mem_filter.1 hx').2]
    _ = ((R.filter (fun x' => diffSet x' x = S)).card : ℝ) * ∏ j ∈ S, (1 / (M j : ℝ)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (((rivalSet t p x z).filter (fun x' => diffSet x' x = S)).card : ℝ) *
          ∏ j ∈ S, (1 / (M j : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hprod0
        exact_mod_cast card_le_card fun x' hx' => by
          have h₁ := mem_filter.1 hx'
          exact mem_filter.2 ⟨(mem_filter.1 h₁.1).1, h₁.2⟩
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_rivals_le hp t x z S) hprod0

open Classical in
/-- The collisions over the rivals of the decoder that knows the key. -/
lemma sum_rivals_key_le (hp : IsPMF p) (t : ℝ) (x : Fin n → ∀ j, α j) (z : Fin n → γ) :
    ∑ x' ∈ rivalSet t p x z, (∏ j ∈ diffSet x' x, (1 / (M j : ℝ))) * (1 / (Kb : ℝ)) ≤
      colKey p M Kb n t := by
  have hmaps : ∀ x' ∈ rivalSet t p x z, diffSet x' x ∈ univ.filter fun S : Finset (Fin N) =>
      S.Nonempty := fun x' hx' => by
    refine Finset.mem_filter.2 ⟨mem_univ _, ?_⟩
    by_contra hne
    refine (mem_erase.1 hx').1 ?_
    funext i
    funext j
    have hj : (fun i => x' i j) = fun i => x i j := by
      by_contra h
      exact hne ⟨j, Finset.mem_filter.2 ⟨mem_univ _, h⟩⟩
    exact congrFun hj i
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun S _ => ?_
  have hprod0 : (0 : ℝ) ≤ (∏ j ∈ S, (1 / (M j : ℝ))) * (1 / (Kb : ℝ)) :=
    mul_nonneg (prod_nonneg fun _ _ => by positivity) (by positivity)
  calc ∑ x' ∈ (rivalSet t p x z).filter (fun x' => diffSet x' x = S),
        (∏ j ∈ diffSet x' x, (1 / (M j : ℝ))) * (1 / (Kb : ℝ))
      = ∑ _x' ∈ (rivalSet t p x z).filter (fun x' => diffSet x' x = S),
          (∏ j ∈ S, (1 / (M j : ℝ))) * (1 / (Kb : ℝ)) :=
        sum_congr rfl fun x' hx' => by rw [(Finset.mem_filter.1 hx').2]
    _ = (((rivalSet t p x z).filter (fun x' => diffSet x' x = S)).card : ℝ) *
          ((∏ j ∈ S, (1 / (M j : ℝ))) * (1 / (Kb : ℝ))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ exp (n * (zCondH p S + t * zCondH p S)) * ((∏ j ∈ S, (1 / (M j : ℝ))) * (1 / (Kb : ℝ))) :=
        mul_le_mul_of_nonneg_right (card_rivals_le hp t x z S) hprod0
    _ = _ := by ring

/-! ### The decoders -/

open Classical in
/-- The decoder of the node `k`: the unique typical sequence with the source of `k`, with `Zⁿ` and
with the public indices. -/
def decNode (T : Finset (Fin n → mLetter α γ)) (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (d : Fin n → ∀ j, α j) (k : Fin N) (xk : Fin n → α k) (z : Fin n → γ)
    (m : ∀ j, Fin (M j)) : Fin n → ∀ j, α j :=
  uniqueOr (univ.filter fun x' => zipSeq x' z ∈ T ∧ (∀ i, x' i k = xk i) ∧ ∀ j, manyBin B x' j =
    m j) d

open Classical in
/-- The decoder that knows the key: the unique typical sequence with `Zⁿ`, with the public indices
and with the key. -/
def decKey (T : Finset (Fin n → mLetter α γ)) (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (C : Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb) (d : Fin n → ∀ j, α j) (z : Fin n → γ)
    (m : ∀ j, Fin (M j)) (κ : Fin Kb) : Fin n → ∀ j, α j :=
  uniqueOr (univ.filter fun x' => zipSeq x' z ∈ T ∧ (∀ j, manyBin B x' j = m j) ∧
    C (Fintype.equivFin _ x') = κ) d

open Classical in
/-- A decoding error of the node `k` needs an atypical sequence or a rival in the same bins. -/
lemma decNode_ne_le (t : ℝ) (B : ∀ j, Fin (seqN α n j) → Fin (M j)) (d : Fin n → ∀ j, α j)
    (k : Fin N) (x : Fin n → ∀ j, α j) (z : Fin n → γ) :
    (if decNode (robustTypicalSet p n t) B d k (fun i => x i k) z (manyBin B x) ≠ x then (1 : ℝ)
      else 0) ≤ (if zipSeq x z ∉ robustTypicalSet p n t then 1 else 0) +
        ∑ x' ∈ (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k),
          if ∀ j, manyBin B x' j = manyBin B x j then 1 else 0 := by
  have hn0 : (0 : ℝ) ≤ ∑ x' ∈ (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k),
      if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hs : zipSeq x z ∈ robustTypicalSet p n t
  · by_cases hu : ∀ x' ∈ (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k),
        ¬ ∀ j, manyBin B x' j = manyBin B x j
    · have hd : decNode (robustTypicalSet p n t) B d k (fun i => x i k) z (manyBin B x) = x := by
        refine uniqueOr_eq d (mem_filter.2 ⟨mem_univ _, hs, fun _ => rfl, fun _ => rfl⟩)
          fun x' hx' => ?_
        by_contra hne
        obtain ⟨-, h₁, h₂, h₃⟩ := mem_filter.1 hx'
        exact hu x' (mem_filter.2 ⟨mem_erase.2 ⟨hne, mem_filter.2 ⟨mem_univ _, h₁⟩⟩, h₂⟩) h₃
      simp only [hd, ne_eq, not_true_eq_false, ite_false, hs, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨x', hx', hb⟩ := hu
      have h₁ : (1 : ℝ) ≤ ∑ x' ∈ (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k),
          if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0 := by
        have := single_le_sum (f := fun x' => if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ)
          else 0) (fun _ _ => by split_ifs <;> norm_num) hx'
        simpa [hb] using this
      split_ifs <;> linarith
  · simp only [hs, not_false_eq_true, ite_true]
    split_ifs <;> linarith

open Classical in
/-- A decoding error with the key needs an atypical sequence or a rival in the same bins. -/
lemma decKey_ne_le (t : ℝ) (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (C : Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb) (d : Fin n → ∀ j, α j)
    (x : Fin n → ∀ j, α j) (z : Fin n → γ) :
    (if decKey (robustTypicalSet p n t) B C d z (manyBin B x) (C (Fintype.equivFin _ x)) ≠ x then
      (1 : ℝ) else 0) ≤ (if zipSeq x z ∉ robustTypicalSet p n t then 1 else 0) +
        ∑ x' ∈ rivalSet t p x z, (if ∀ j, manyBin B x' j = manyBin B x j then 1 else 0) *
          (if C (Fintype.equivFin _ x') = C (Fintype.equivFin _ x) then 1 else 0) := by
  have hn0 : (0 : ℝ) ≤ ∑ x' ∈ rivalSet t p x z,
      (if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0) *
        (if C (Fintype.equivFin _ x') = C (Fintype.equivFin _ x) then 1 else 0) :=
    sum_nonneg fun _ _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
  by_cases hs : zipSeq x z ∈ robustTypicalSet p n t
  · by_cases hu : ∀ x' ∈ rivalSet t p x z, ¬ ((∀ j, manyBin B x' j = manyBin B x j) ∧
        C (Fintype.equivFin _ x') = C (Fintype.equivFin _ x))
    · have hd : decKey (robustTypicalSet p n t) B C d z (manyBin B x) (C (Fintype.equivFin _ x)) =
          x := by
        refine uniqueOr_eq d (mem_filter.2 ⟨mem_univ _, hs, fun _ => rfl, rfl⟩) fun x' hx' => ?_
        by_contra hne
        obtain ⟨-, h₁, h₂, h₃⟩ := mem_filter.1 hx'
        exact hu x' (mem_erase.2 ⟨hne, mem_filter.2 ⟨mem_univ _, h₁⟩⟩) ⟨h₂, h₃⟩
      simp only [hd, ne_eq, not_true_eq_false, ite_false, hs, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨x', hx', hb, hc⟩ := hu
      have h₁ : (1 : ℝ) ≤ ∑ x' ∈ rivalSet t p x z,
          (if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0) *
            (if C (Fintype.equivFin _ x') = C (Fintype.equivFin _ x) then 1 else 0) := by
        have := single_le_sum (f := fun x' =>
          (if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0) *
            (if C (Fintype.equivFin _ x') = C (Fintype.equivFin _ x) then 1 else 0))
          (fun _ _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)) hx'
        simpa [hb, hc] using this
      split_ifs <;> linarith
  · simp only [hs, not_false_eq_true, ite_true]
    split_ifs <;> linarith

/-- The law of a random hash with values in `[1 : K]`. -/
def keyHashLaw (N' Kb : ℕ) : (Fin N' → Fin Kb) → ℝ := iidPMF (uniformPMF (Fin Kb)) N'

lemma keyHashLaw_isPMF {N' : ℕ} [NeZero Kb] : IsPMF (keyHashLaw N' Kb) := by
  have : Nonempty (Fin Kb) := ⟨0⟩
  exact iidPMF_isPMF uniformPMF_isPMF N'

/-- Two arguments of a random hash collide with probability `1 / K`. -/
lemma sum_keyHashLaw_eq {N' : ℕ} [NeZero Kb] {w w' : Fin N'} (h : w ≠ w') :
    ∑ C, keyHashLaw N' Kb C * (if C w = C w' then 1 else 0) = 1 / Kb := by
  classical
  have : Nonempty (Fin Kb) := ⟨0⟩
  have hK : (Kb : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Kb
  have h₁ := sum_iidPMF_eval₂ (uniformPMF_isPMF (α := Fin Kb)) h
    fun x y => if x = y then (1 : ℝ) else 0
  refine h₁.trans ?_
  have inner : ∀ x : Fin Kb, ∑ x' : Fin Kb, uniformPMF (Fin Kb) x * uniformPMF (Fin Kb) x' *
      (if x = x' then (1 : ℝ) else 0) = 1 / Kb * (1 / Kb) := fun x => by
    rw [sum_eq_single x (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [uniformPMF]
  simp only [inner, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

variable [∀ j, NeZero (M j)] [NeZero Kb]

omit [∀ (j : Fin N), NeZero (M j)] in
open Classical in
/-- The probability that the bins agree. -/
lemma sum_manyBinLaw_diffSet (hMpos : ∀ j, 0 < M j) (x' x : Fin n → ∀ j, α j) :
    ∑ B, manyBinLaw M n α B * (if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0) =
      ∏ j ∈ diffSet x' x, (1 / (M j : ℝ)) := by
  have h := sum_manyBinLaw_collision hMpos x x'
  refine (sum_congr rfl fun B _ => ?_).trans (h.trans ?_)
  · by_cases hc : ∀ j, manyBin B x' j = manyBin B x j <;> simp [hc]
  · refine prod_congr ?_ fun _ _ => rfl
    ext j
    simp [diffSet]

open Classical in
/-- The decoders, on average over the hashes, for one sequence. -/
lemma sum_multiHash_le (hp : IsPMF p) (t : ℝ) (d x : Fin n → ∀ j, α j) (z : Fin n → γ) :
    ∑ H : (∀ j, Fin (seqN α n j) → Fin (M j)) × (Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb),
      prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H *
        ((∑ k, if decNode (robustTypicalSet p n t) H.1 d k (fun i => x i k) z (manyBin H.1 x) ≠ x
            then 1 else 0) +
          if decKey (robustTypicalSet p n t) H.1 H.2 d z (manyBin H.1 x)
            (H.2 (Fintype.equivFin _ x)) ≠ x then 1 else 0) ≤
      (N + 1) * (if zipSeq x z ∉ robustTypicalSet p n t then 1 else 0) +
        ∑ k, colNode p M n t k + colKey p M Kb n t := by
  have hMpos : ∀ j, 0 < M j := fun j => Nat.pos_of_ne_zero (NeZero.ne _)
  have hlaw₁ := manyBinLaw_isPMF (M := M) (n := n) (α := α) hMpos
  have hlaw₂ := keyHashLaw_isPMF (N' := Fintype.card (Fin n → ∀ j, α j)) (Kb := Kb)
  have hlaw := hlaw₁.prodDist hlaw₂
  set a : ℝ := if zipSeq x z ∉ robustTypicalSet p n t then 1 else 0 with ha
  -- The rivals of the nodes.
  have hN₀ : ∀ k, ∑ B, manyBinLaw M n α B *
      (∑ x' ∈ (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k),
        if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0) ≤ colNode p M n t k := fun k =>
          by
    simp only [mul_sum]
    rw [sum_comm]
    simp only [sum_manyBinLaw_diffSet hMpos]
    exact sum_rivals_node_le hp t k x z
  -- The rivals of the decoder with the key.
  have hK₀ : ∑ H : (∀ j, Fin (seqN α n j) → Fin (M j)) ×
        (Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb),
      prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H * (∑ x' ∈ rivalSet t p x z,
        (if ∀ j, manyBin H.1 x' j = manyBin H.1 x j then (1 : ℝ) else 0) *
          (if H.2 (Fintype.equivFin _ x') = H.2 (Fintype.equivFin _ x) then 1 else 0)) ≤
      colKey p M Kb n t := by
    simp only [mul_sum]
    rw [sum_comm]
    refine le_trans (le_of_eq (sum_congr rfl fun x' hx' => ?_))
      (sum_rivals_key_le (Kb := Kb) hp t x z)
    have hne : (Fintype.equivFin (Fin n → ∀ j, α j)) x' ≠ Fintype.equivFin _ x := fun h =>
      (mem_erase.1 hx').1 ((Fintype.equivFin _).injective h)
    rw [Fintype.sum_prod_type]
    simp only [prodDist]
    have e₁ : ∀ B C, manyBinLaw M n α B * keyHashLaw _ Kb C *
        ((if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0) *
          (if C (Fintype.equivFin _ x') = C (Fintype.equivFin _ x) then 1 else 0)) =
        (manyBinLaw M n α B * (if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0)) *
          (keyHashLaw _ Kb C * (if C (Fintype.equivFin _ x') = C (Fintype.equivFin _ x) then 1
            else 0)) := fun B C => by ring
    simp only [e₁, ← mul_sum, sum_keyHashLaw_eq hne, ← sum_mul, sum_manyBinLaw_diffSet hMpos]
  -- The pointwise bound.
  set RN : (∀ j, Fin (seqN α n j) → Fin (M j)) → Fin N → ℝ := fun B k =>
    ∑ x' ∈ (rivalSet t p x z).filter (fun x' => ∀ i, x' i k = x i k),
      if ∀ j, manyBin B x' j = manyBin B x j then (1 : ℝ) else 0 with hRN
  set RK : (∀ j, Fin (seqN α n j) → Fin (M j)) × (Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb) →
      ℝ := fun H => ∑ x' ∈ rivalSet t p x z,
      (if ∀ j, manyBin H.1 x' j = manyBin H.1 x j then (1 : ℝ) else 0) *
        (if H.2 (Fintype.equivFin _ x') = H.2 (Fintype.equivFin _ x) then 1 else 0) with hRK
  have hpt : ∀ H : (∀ j, Fin (seqN α n j) → Fin (M j)) ×
      (Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb),
      ((∑ k, if decNode (robustTypicalSet p n t) H.1 d k (fun i => x i k) z (manyBin H.1 x) ≠ x
          then (1 : ℝ) else 0) +
        if decKey (robustTypicalSet p n t) H.1 H.2 d z (manyBin H.1 x)
          (H.2 (Fintype.equivFin _ x)) ≠ x then 1 else 0) ≤
      (N + 1) * a + ∑ k, RN H.1 k + RK H := fun H => by
    have h₁ := sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin N))) =>
      decNode_ne_le (p := p) t H.1 d k x z
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h₁
    have h₂ := decKey_ne_le (p := p) t H.1 H.2 d x z
    nlinarith
  refine (sum_le_sum fun H _ => mul_le_mul_of_nonneg_left (hpt H) (hlaw.nonneg H)).trans ?_
  have hsplit : ∑ H : (∀ j, Fin (seqN α n j) → Fin (M j)) ×
      (Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb),
      prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H * ((N + 1) * a + ∑ k, RN H.1 k + RK H) =
      (N + 1) * a + ∑ k, ∑ B, manyBinLaw M n α B * RN B k +
        ∑ H, prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H * RK H := by
    have e₁ : ∀ H : (∀ j, Fin (seqN α n j) → Fin (M j)) ×
        (Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb),
        prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H * ((N + 1) * a + ∑ k, RN H.1 k + RK H) =
        prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H * ((N + 1) * a) +
        prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H * ∑ k, RN H.1 k +
        prodDist (manyBinLaw M n α) (keyHashLaw _ Kb) H * RK H := fun H => by ring
    simp only [e₁, sum_add_distrib, ← sum_mul, hlaw.sum_eq_one, one_mul]
    congr 2
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [prodDist]
    refine sum_congr rfl fun B _ => ?_
    have e₂ : ∀ C, manyBinLaw M n α B * keyHashLaw (Fintype.card (Fin n → ∀ j, α j)) Kb C *
        RN B k = manyBinLaw M n α B * RN B k *
          keyHashLaw (Fintype.card (Fin n → ∀ j, α j)) Kb C := fun C => by ring
    simp only [e₂, ← mul_sum, hlaw₂.sum_eq_one, mul_one]
  rw [hsplit]
  have h₃ := sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin N))) => hN₀ k
  linarith

open Classical in
/-- **Pages 23-54 and 23-55 of [elgamal2010]: random binning.** There are bins and a key, and the
decoders of the nodes and a decoder with the key, such that the sum of the probabilities of error is
at most `(N + 1) P{(Xⁿ, Zⁿ) ∉ T} + ∑ₖ colₖ + col`. -/
theorem exists_multiBin (hp : IsPMF p) (t : ℝ) :
    ∃ (B : ∀ j, Fin (seqN α n j) → Fin (M j))
      (C : Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb) (d : Fin n → ∀ j, α j),
      ∑ ω : Fin n → mLetter α γ, iidPMF p n ω *
        ((∑ k, if decNode (robustTypicalSet p n t) B d k (fun i => (ω i).1 k) (fun i => (ω i).2)
            (manyBin B fun i => (ω i).1) ≠ (fun i => (ω i).1) then 1 else 0) +
          if decKey (robustTypicalSet p n t) B C d (fun i => (ω i).2) (manyBin B fun i => (ω i).1)
            (C (Fintype.equivFin _ fun i => (ω i).1)) ≠ (fun i => (ω i).1) then 1 else 0) ≤
      (N + 1) * (1 - prob (iidPMF p n) (robustTypicalSet p n t)) +
        ∑ k, colNode p M n t k + colKey p M Kb n t := by
  have hMpos : ∀ j, 0 < M j := fun j => Nat.pos_of_ne_zero (NeZero.ne _)
  have hlaw := (manyBinLaw_isPMF (M := M) (n := n) (α := α) hMpos).prodDist
    (keyHashLaw_isPMF (N' := Fintype.card (Fin n → ∀ j, α j)) (Kb := Kb))
  have hμ := iidPMF_isPMF hp n
  obtain ⟨a₀⟩ : Nonempty (mLetter α γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  set d : Fin n → ∀ j, α j := fun _ => a₀.1
  obtain ⟨H, hH⟩ := exists_of_pointwise_avg hlaw hμ
    (F := fun H ω => (∑ k, if decNode (robustTypicalSet p n t) H.1 d k (fun i => (ω i).1 k)
        (fun i => (ω i).2) (manyBin H.1 fun i => (ω i).1) ≠ (fun i => (ω i).1) then 1 else 0) +
      if decKey (robustTypicalSet p n t) H.1 H.2 d (fun i => (ω i).2)
        (manyBin H.1 fun i => (ω i).1) (H.2 (Fintype.equivFin _ fun i => (ω i).1)) ≠
        (fun i => (ω i).1) then 1 else 0)
    (G := fun ω => (N + 1) * (if zipSeq (fun i => (ω i).1) (fun i => (ω i).2) ∉
        robustTypicalSet p n t then 1 else 0) + ∑ k, colNode p M n t k + colKey p M Kb n t)
    fun ω => sum_multiHash_le hp t d _ _
  refine ⟨H.1, H.2, d, hH.trans (le_of_eq ?_)⟩
  have hs := sum_iidPMF_not_mem hp (id : mLetter α γ → mLetter α γ) n (robustTypicalSet p n t)
  rw [dist_id] at hs
  have e₁ : ∑ ω : Fin n → mLetter α γ, iidPMF p n ω *
      (if zipSeq (fun i => (ω i).1) (fun i => (ω i).2) ∉ robustTypicalSet p n t then (1 : ℝ)
        else 0) = 1 - prob (iidPMF p n) (robustTypicalSet p n t) := hs
  have e₂ : ∀ ω : Fin n → mLetter α γ, iidPMF p n ω * ((N + 1) *
      (if zipSeq (fun i => (ω i).1) (fun i => (ω i).2) ∉ robustTypicalSet p n t then (1 : ℝ)
        else 0) + ∑ k, colNode p M n t k + colKey p M Kb n t) = (N + 1) * (iidPMF p n ω *
      (if zipSeq (fun i => (ω i).1) (fun i => (ω i).2) ∉ robustTypicalSet p n t then (1 : ℝ)
        else 0)) + iidPMF p n ω * (∑ k, colNode p M n t k + colKey p M Kb n t) := fun ω => by ring
  simp only [e₂, sum_add_distrib, ← mul_sum, e₁, ← sum_mul, hμ.sum_eq_one, one_mul]
  ring

end InfoTheory
