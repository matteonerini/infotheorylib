/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.GaussianNetBounds

/-!
# Gaussian networks without relaying: codes and the cutset bound

The senders do not cooperate: each sender `j` encodes its message only, and each receiver `k`
decodes from its own output `Y_k = ∑_j G_{kj} X_j + Z_k`. Since the messages are independent, the
covariance of the inputs is diagonal once the means are removed.

## Main definitions

* `GNCode M n r t`: the codes, with `M j` messages at sender `j`.
* `GNCode.errProb`, `GNCode.SatisfiesPower`: the probability of error and the power constraint.
* `IsAchievableGN G D P R`: achievable rates, in bits, when sender `j` sends to the receivers `D j`.

## Main statements

* `GNCode.one_sub_errProb_mul_le`: the bound for each code.
* `IsAchievableGN.sum_le`: **the cutset bound with no cooperation, page 20-4**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 20
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Tools -/

section Tools

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]

/-- If the sum of `g` vanishes, so does the sum over a family of `g` of one member times a function
of another member. -/
lemma sum_pi_mul_apply_eq_zero {j l : ι} (hjl : j ≠ l) {g : A j → ℝ} (hg : ∑ a, g a = 0)
    (h : A l → ℝ) : ∑ m : ∀ i, A i, g (m j) * h (m l) = 0 := by
  classical
  let e := Equiv.piSplitAt j A
  have h₁ : ∑ m : ∀ i, A i, g (m j) * h (m l) =
      ∑ p : A j × ∀ i : {i // i ≠ j}, A i, g p.1 * h (p.2 ⟨l, hjl.symm⟩) :=
    Fintype.sum_equiv e _ _ fun m => rfl
  rw [h₁, Fintype.sum_prod_type]
  simp_rw [← mul_sum]
  rw [← sum_mul, hg, zero_mul]

/-- The average over a family of a function of one member. -/
lemma sum_pi_apply (j : ι) (g : A j → ℝ) :
    ∑ m : ∀ i, A i, g (m j) = (Fintype.card (∀ i : {i // i ≠ j}, A i) : ℝ) * ∑ a, g a := by
  classical
  let e := Equiv.piSplitAt j A
  have h₁ : ∑ m : ∀ i, A i, g (m j) = ∑ p : A j × ∀ i : {i // i ≠ j}, A i, g p.1 :=
    Fintype.sum_equiv e _ _ fun m => rfl
  rw [h₁, Fintype.sum_prod_type]
  simp [mul_sum]

/-- A sum over the members of a set, as a sum over all the indices. -/
lemma sum_coe_eq_sum_dite (S : Finset ι) (f : S → ℝ) :
    ∑ j : S, f j = ∑ j, if h : j ∈ S then f ⟨j, h⟩ else 0 := by
  rw [← sum_subset (subset_univ S) fun j _ hj => dite_eq_right hj, ← sum_attach S, univ_eq_attach]
  exact sum_congr rfl fun j _ => by simp

/-- The number of elements of a family is the product of the numbers of the elements. -/
lemma card_pi_split (j : ι) :
    (Fintype.card (∀ i, A i) : ℝ) =
      (Fintype.card (A j) : ℝ) * Fintype.card (∀ i : {i // i ≠ j}, A i) := by
  classical
  rw [Fintype.card_congr (Equiv.piSplitAt j A), Fintype.card_prod]
  push_cast
  rfl

end Tools

section Noise

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **A marginal of the noise is noise.** -/
lemma map_stdNoise_comp_injective {f : β → α}
    (hf : Function.Injective f) :
    (stdNoise α).map (fun z b => z (f b)) = stdNoise β := by
  classical
  have hmeas : Measurable fun (z : α → ℝ) (b : β) => z (f b) :=
    measurable_pi_iff.mpr fun b => measurable_pi_apply (f b)
  symm
  refine Measure.pi_eq fun S hS => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hS)]
  have hset : (fun (z : α → ℝ) (b : β) => z (f b)) ⁻¹' Set.univ.pi S =
      Set.univ.pi fun a : α => if h : ∃ b, f b = a then S (Classical.choose h) else Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h a
      split_ifs with ha
      · have := h (Classical.choose ha)
        rwa [Classical.choose_spec ha] at this
      · exact Set.mem_univ _
    · intro h b
      have ha : ∃ b', f b' = f b := ⟨b, rfl⟩
      have := h (f b)
      rw [dite_eq_left ha] at this
      have e := hf (Classical.choose_spec ha)
      rwa [e] at this
  rw [hset, Measure.pi_pi]
  have e : ∀ a : α, gaussianReal 0 (1 : ℝ≥0)
      (if h : ∃ b, f b = a then S (Classical.choose h) else Set.univ) =
      if h : ∃ b, f b = a then gaussianReal 0 (1 : ℝ≥0) (S (Classical.choose h)) else 1 := by
    intro a
    split_ifs <;> simp
  simp_rw [e]
  have h₂ : ∏ a : α, (if h : ∃ b, f b = a then gaussianReal 0 (1 : ℝ≥0) (S (Classical.choose h))
      else 1) = ∏ a ∈ univ.image f, (if h : ∃ b, f b = a then
        gaussianReal 0 (1 : ℝ≥0) (S (Classical.choose h)) else 1) := by
    refine (prod_subset (subset_univ _) fun a _ ha => ?_).symm
    rw [dite_eq_right]
    rintro ⟨b, rfl⟩
    exact ha (mem_image_of_mem _ (mem_univ b))
  rw [h₂, prod_image fun a _ b _ h => hf h]
  refine prod_congr rfl fun b _ => ?_
  have ha : ∃ b', f b' = f b := ⟨b, rfl⟩
  rw [dite_eq_left ha, hf (Classical.choose_spec ha)]

end Noise

/-! ### The model -/

/-- **Page 20-2 of [elgamal2010], with no relaying.** A code: sender `j` sends `enc j m_j`, and
receiver `k` estimates the messages from its output. -/
structure GNCode {t : Type*} (M : t → ℕ) (n : ℕ) (r : Type*) where
  /-- The encoders. -/
  enc : ∀ j, Fin (M j) → Fin n → ℝ
  /-- The decoders. -/
  dec : r → (Fin n → ℝ) → ∀ j, Fin (M j)
  measurable_dec : ∀ k, Measurable (dec k)

namespace GNCode

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq t] {M : t → ℕ} {n : ℕ}
  (c : GNCode M n r)

/-- **Page 20-2 of [elgamal2010].** The average power constraint, for each sender. -/
def SatisfiesPower (P : ℝ) : Prop :=
  ∀ j, ∑ m, ∑ i, c.enc j m i ^ 2 ≤ (M j : ℝ) * (n * P)

variable (G : Matrix r t ℝ)

/-- The noiseless output at time `i` of receiver `k`. -/
def out (m : ∀ j, Fin (M j)) (i : Fin n) (k : r) : ℝ := ∑ j, G k j * c.enc j (m j) i

/-- The event of an error for a tuple of messages, when sender `j` sends to the receivers `D j`. -/
def errSet (D : t → Finset r) (m : ∀ j, Fin (M j)) : Set (Fin n × r → ℝ) :=
  {z | ∃ j, ∃ k ∈ D j, c.dec k (fun i => c.out G m i k + z (i, k)) j ≠ m j}

/-- The probability of error, for uniform messages. -/
def errProb (D : t → Finset r) : ℝ :=
  (∑ m : ∀ j, Fin (M j), (stdNoise (Fin n × r)).real (c.errSet G D m)) /
    (Fintype.card (∀ j, Fin (M j)) : ℝ)

end GNCode

/-- **Page 20-2 of [elgamal2010], with no relaying.** A rate tuple, in bits, is achievable. -/
def IsAchievableGN {r t : Type*} [Fintype r] [Fintype t] [DecidableEq t] (G : Matrix r t ℝ)
    (D : t → Finset r) (P : ℝ≥0) (R : t → ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, GNCode (fun j => 2 ^ ⌈(n : ℝ) * R j⌉₊) n r,
    (∀ n, (c n).SatisfiesPower P) ∧ Tendsto (fun n => (c n).errProb G D) atTop (𝓝 0)

/-! ### The bound for one code -/

section Converse

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t] {M : t → ℕ} {n : ℕ}

namespace GNCode

variable (c : GNCode M n r) (G : Matrix r t ℝ)

/-- The mean of the input of a sender at a time. -/
def mean (j : t) (i : Fin n) : ℝ := (M j : ℝ)⁻¹ * ∑ m, c.enc j m i

omit [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t] in
lemma sum_sub_mean {j : t} (hM : 0 < M j) (i : Fin n) : ∑ m, (c.enc j m i - c.mean j i) = 0 := by
  have hM' : (M j : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mean]
  field_simp
  ring

omit [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t] in
/-- The variance is at most the second moment. -/
lemma sum_sub_mean_sq_le {j : t} (hM : 0 < M j) (i : Fin n) :
    ∑ m, (c.enc j m i - c.mean j i) ^ 2 ≤ ∑ m, c.enc j m i ^ 2 := by
  have h₁ := c.sum_sub_mean hM i
  have h₂ : ∑ m, c.enc j m i ^ 2 = ∑ m, (c.enc j m i - c.mean j i) ^ 2 +
      (M j : ℝ) * c.mean j i ^ 2 := by
    have e : ∀ m, c.enc j m i ^ 2 = (c.enc j m i - c.mean j i) ^ 2 +
        2 * c.mean j i * (c.enc j m i - c.mean j i) + c.mean j i ^ 2 := fun m => by ring
    simp_rw [e]
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, h₁]
    simp
  have h₃ : 0 ≤ (M j : ℝ) * c.mean j i ^ 2 := by positivity
  linarith

/-- The tuple of messages from the messages of the senders of `A` and of the others. -/
def merge (A : Finset t) (mA : ∀ j : A, Fin (M j)) (m₀ : ∀ j : {j // j ∉ A}, Fin (M j)) (j : t) :
    Fin (M j) :=
  if h : j ∈ A then mA ⟨j, h⟩ else m₀ ⟨j, h⟩

/-- The shift of the output of a receiver: what it does not depend on the messages of `A`. -/
def shift (A : Finset t) (m₀ : ∀ j : {j // j ∉ A}, Fin (M j)) (k : r) (i : Fin n) : ℝ :=
  ∑ j, G k j * if h : j ∈ A then c.mean j i else c.enc j (m₀ ⟨j, h⟩) i

/-- The code of the senders of `A` for the receivers of `B`, for fixed messages of the other
senders. -/
def cutCode (A : Finset t) (B : Finset r) (m₀ : ∀ j : {j // j ∉ A}, Fin (M j))
    {kj : A → r} (hkj : ∀ j, kj j ∈ B) :
    GVCode (Fintype.card (∀ j : A, Fin (M j))) n B A where
  enc w i j := c.enc j ((Fintype.equivFin _).symm w j) i - c.mean j i
  dec y := Fintype.equivFin _ fun j : A =>
    c.dec (kj j) (fun i => y (i, ⟨kj j, hkj j⟩) + c.shift G A m₀ (kj j) i) j
  measurable_dec := by
    refine (measurable_of_finite (Fintype.equivFin (∀ j : A, Fin (M j)))).comp ?_
    refine measurable_pi_iff.mpr fun j => ?_
    refine (measurable_pi_apply (j : t)).comp ((c.measurable_dec (kj j)).comp ?_)
    refine measurable_pi_iff.mpr fun i => ?_
    exact (measurable_pi_apply _).add_const _

variable (A : Finset t) (B : Finset r) (m₀ : ∀ j : {j // j ∉ A}, Fin (M j)) {kj : A → r}
  (hkj : ∀ j, kj j ∈ B)

omit [Fintype r] [DecidableEq r] in
/-- The output of the code of a cut, plus the shift, is the output of the network. -/
lemma cut_out_add_shift (w : Fin (Fintype.card (∀ j : A, Fin (M j)))) (i : Fin n) (k : B) :
    (c.cutCode G A B m₀ hkj).out (G.submatrix Subtype.val Subtype.val) w (i, k) +
      c.shift G A m₀ k i = c.out G (merge A ((Fintype.equivFin _).symm w) m₀) i k := by
  simp only [GVCode.out, cutCode, mulVec, dotProduct, submatrix_apply, shift, out]
  rw [sum_coe_eq_sum_dite A fun j : A => G k j *
    (c.enc j ((Fintype.equivFin (∀ j : A, Fin (M j))).symm w j) i - c.mean j i), ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : j ∈ A
  · simp only [h, dite_true, merge]
    ring
  · simp only [h, dite_false, merge, zero_add]

omit [DecidableEq r] in
/-- The event of an error of the code of a cut is contained in the event of an error of the code. -/
lemma cut_condErr_le {D : t → Finset r} (hkD : ∀ j : A, kj j ∈ D j)
    (w : Fin (Fintype.card (∀ j : A, Fin (M j)))) :
    (c.cutCode G A B m₀ hkj).condErrProb (G.submatrix Subtype.val Subtype.val) w ≤
      (stdNoise (Fin n × r)).real (c.errSet G D (merge A ((Fintype.equivFin _).symm w) m₀)) := by
  classical
  set c' := c.cutCode G A B m₀ hkj with hc'
  set G' := G.submatrix (Subtype.val : B → r) (Subtype.val : A → t) with hG'
  set m := merge A ((Fintype.equivFin (∀ j : A, Fin (M j))).symm w) m₀ with hm
  let f : Fin n × B → Fin n × r := fun p => (p.1, p.2)
  have hf : Function.Injective f := fun a b h => by
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Subtype.ext h.2)
  have hmap := map_stdNoise_comp_injective hf
  have hE : MeasurableSet {z : Fin n × B → ℝ | c'.dec (c'.out G' w + z) ≠ w} := by
    have hm' : Measurable fun z : Fin n × B → ℝ => c'.dec (c'.out G' w + z) :=
      c'.measurable_dec.comp (measurable_const.add measurable_id)
    exact hm' (measurableSet_singleton w).compl
  have hρ : Measurable fun (z : Fin n × r → ℝ) (b : Fin n × B) => z (f b) :=
    measurable_pi_iff.mpr fun b => measurable_pi_apply (f b)
  have hreal : (c'.condErrProb G' w) = (stdNoise (Fin n × r)).real
      ((fun (z : Fin n × r → ℝ) (b : Fin n × B) => z (f b)) ⁻¹'
        {z | c'.dec (c'.out G' w + z) ≠ w}) := by
    simp only [GVCode.condErrProb]
    rw [← hmap, map_measureReal_apply hρ hE]
  rw [hreal]
  refine measureReal_mono (fun z hz => ?_) (measure_ne_top _ _)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz
  by_contra hno
  apply hz
  have hn := hno
  simp only [errSet, Set.mem_ofPred_eq, not_exists, not_and, not_not] at hn
  have hdecEq : (fun j : A => c.dec (kj j) (fun i => (c'.out G' w + fun b => z (f b))
      (i, ⟨kj j, hkj j⟩) + c.shift G A m₀ (kj j) i) j) =
      (Fintype.equivFin (∀ j : A, Fin (M j))).symm w := by
    funext j
    have h₁ := hn j (kj j) (hkD j)
    have hmj : m j = (Fintype.equivFin (∀ j : A, Fin (M j))).symm w j := by
      simp [hm, merge, j.2]
    rw [hmj] at h₁
    rw [← h₁]
    congr 1
    funext i
    have h₂ := c.cut_out_add_shift G A B m₀ hkj w i ⟨kj j, hkj j⟩
    simp only [Pi.add_apply, f]
    rw [← hm, ← hc', ← hG'] at h₂
    simp only at h₂
    rw [← h₂]
    ring
  change (Fintype.equivFin (∀ j : A, Fin (M j))) (fun j : A => c.dec (kj j)
    (fun i => (c'.out G' w + fun b => z (f b)) (i, ⟨kj j, hkj j⟩) + c.shift G A m₀ (kj j) i) j) = w
  rw [hdecEq]
  simp

omit [Fintype r] [DecidableEq r] in
/-- The entries of the average covariance of the code of a cut. -/
lemma cut_avgCov_apply (j l : A) :
    (c.cutCode G A B m₀ hkj).avgCov j l =
      (((Fintype.card (∀ j : A, Fin (M j)) : ℕ) : ℝ) * n)⁻¹ * ∑ mA : ∀ j : A, Fin (M j), ∑ i,
        (c.enc j (mA j) i - c.mean j i) * (c.enc l (mA l) i - c.mean l i) := by
  simp only [GVCode.avgCov, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, transpose_apply,
    GVCode.codeMatrix, Matrix.of_apply, Fintype.sum_prod_type, cutCode]
  congr 1
  exact Fintype.sum_equiv (Fintype.equivFin _).symm _ _ fun w => rfl

omit [Fintype r] [DecidableEq r] in
/-- **The inputs of different senders are uncorrelated**, since the messages are independent. -/
lemma cut_avgCov_off (hM : ∀ j, 0 < M j) {j l : A} (hjl : j ≠ l) :
    (c.cutCode G A B m₀ hkj).avgCov j l = 0 := by
  rw [cut_avgCov_apply, sum_comm]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun i _ => ?_)
  exact sum_pi_mul_apply_eq_zero (A := fun j : A => Fin (M j)) hjl (g := fun a =>
    c.enc j a i - c.mean j i) (c.sum_sub_mean (hM j) i) fun b => c.enc l b i - c.mean l i

omit [Fintype r] [DecidableEq r] in
/-- The variance of the input of a sender is at most the power. -/
lemma cut_avgCov_diag_le (hM : ∀ j, 0 < M j) (hn : 0 < n) {P : ℝ} (hpow : c.SatisfiesPower P)
    (j : A) : (c.cutCode G A B m₀ hkj).avgCov j j ≤ P := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hMj : (0 : ℝ) < M j := by exact_mod_cast hM j
  have : Nonempty (∀ j : A, Fin (M j)) := ⟨fun j => ⟨0, hM j⟩⟩
  have hR : (0 : ℝ) < Fintype.card (∀ i : {i // i ≠ j}, Fin (M i)) := by
    have : Nonempty (∀ i : {i // i ≠ j}, Fin (M i)) := ⟨fun i => ⟨0, hM i⟩⟩
    exact_mod_cast Fintype.card_pos
  have hsplit := card_pi_split (A := fun j : A => Fin (M j)) j
  simp only [Fintype.card_fin] at hsplit
  rw [cut_avgCov_apply, hsplit, sum_comm]
  have h₁ : ∀ i, ∑ mA : ∀ j : A, Fin (M j),
      (c.enc j (mA j) i - c.mean j i) * (c.enc j (mA j) i - c.mean j i) =
      (Fintype.card (∀ i : {i // i ≠ j}, Fin (M i)) : ℝ) * ∑ a, (c.enc j a i - c.mean j i) ^ 2 := by
    intro i
    have := sum_pi_apply (A := fun j : A => Fin (M j)) j fun a => (c.enc j a i - c.mean j i) ^ 2
    simp only [sq] at this ⊢
    exact this
  simp_rw [h₁]
  rw [← mul_sum]
  have h₂ : ∑ i, ∑ a, (c.enc j a i - c.mean j i) ^ 2 ≤ (M j : ℝ) * (n * P) := by
    refine (sum_le_sum fun i _ => c.sum_sub_mean_sq_le (hM j) i).trans ?_
    rw [sum_comm]
    exact hpow j
  rw [inv_mul_le_iff₀ (by positivity)]
  calc _ ≤ (Fintype.card (∀ i : {i // i ≠ j}, Fin (M i)) : ℝ) * ((M j : ℝ) * (n * P)) :=
        mul_le_mul_of_nonneg_left h₂ hR.le
    _ = _ := by ring

/-- **The bound for each code, page 20-4 of [elgamal2010].** For a set `A` of senders and a set `B`
of receivers, such that each sender of `A` has a destination in `B`,
`(1 - P_e) ∑_{j ∈ A} log M_j ≤ log 2 + n ½ log |I + P G(B, A) G(B, A)ᵀ|`. -/
theorem one_sub_errProb_mul_le (hM : ∀ j, 0 < M j) (hn : 0 < n) {P : ℝ}
    (hpow : c.SatisfiesPower P) (D : t → Finset r) (A : Finset t) (B : Finset r)
    (hAB : ∀ j ∈ A, ∃ k ∈ B, k ∈ D j) :
    (1 - c.errProb G D) * ∑ j ∈ A, log (M j) ≤
      log 2 + n * gvRate (G.submatrix (Subtype.val : B → r) (Subtype.val : A → t)) (P • 1) := by
  classical
  have : Nonempty (∀ j, Fin (M j)) := ⟨fun j => ⟨0, hM j⟩⟩
  have hA' : Nonempty (∀ j : A, Fin (M j)) := ⟨fun j => ⟨0, hM j⟩⟩
  have hC' : Nonempty (∀ j : {j // j ∉ A}, Fin (M j)) := ⟨fun j => ⟨0, hM j⟩⟩
  have hdest : ∀ j : A, ∃ k, k ∈ B ∧ k ∈ D j := fun j => hAB j j.2
  choose kj hkjB hkjD using hdest
  -- the choice of the messages of the other senders
  set e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ A) (fun j => Fin (M j)) with he
  set cA := (Fintype.card (∀ j : A, Fin (M j)) : ℝ) with hcA
  set cC := (Fintype.card (∀ j : {j // j ∉ A}, Fin (M j)) : ℝ) with hcC
  have hcA0 : 0 < cA := by
    rw [hcA]
    exact_mod_cast Fintype.card_pos
  have hcC0 : 0 < cC := by
    rw [hcC]
    exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (∀ j, Fin (M j)) : ℝ) = cA * cC := by
    rw [Fintype.card_congr e, Fintype.card_prod]
    push_cast
    rfl
  set Err := fun m : ∀ j, Fin (M j) => (stdNoise (Fin n × r)).real (c.errSet G D m) with hErr
  have hsum : ∑ m₀ : ∀ j : {j // j ∉ A}, Fin (M j), ∑ mA : ∀ j : A, Fin (M j),
      Err (merge A mA m₀) = (cA * cC) * c.errProb G D := by
    have hE : c.errProb G D = (∑ m, Err m) / (cA * cC) := by
      rw [errProb, hcard]
    rw [hE, mul_div_cancel₀ _ (by positivity), sum_comm, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv e.symm _ _ fun p => rfl
  obtain ⟨m₀, -, hm₀⟩ : ∃ m₀ ∈ (univ : Finset (∀ j : {j // j ∉ A}, Fin (M j))),
      ∑ mA : ∀ j : A, Fin (M j), Err (merge A mA m₀) ≤ cA * c.errProb G D := by
    refine exists_le_of_sum_le univ_nonempty ?_
    rw [hsum, sum_const, card_univ, nsmul_eq_mul]
    exact le_of_eq (by ring)
  -- the code of the cut
  set c' := c.cutCode G A B m₀ hkjB with hc'
  set G' := G.submatrix (Subtype.val : B → r) (Subtype.val : A → t) with hG'
  have hM' : 0 < Fintype.card (∀ j : A, Fin (M j)) := Fintype.card_pos
  have hb := c'.one_sub_avgErrProb_mul_log_le G' hM' hn
  have hErrle : c'.avgErrProb G' ≤ c.errProb G D := by
    rw [GVCode.avgErrProb, div_le_iff₀ (by exact_mod_cast hM')]
    have h₁ : ∑ w, c'.condErrProb G' w ≤ ∑ mA : ∀ j : A, Fin (M j), Err (merge A mA m₀) := by
      calc _ ≤ ∑ w, Err (merge A ((Fintype.equivFin _).symm w) m₀) :=
            sum_le_sum fun w _ => c.cut_condErr_le G A B m₀ hkjB hkjD w
        _ = _ := Fintype.sum_equiv (Fintype.equivFin _).symm _ _ fun w => rfl
    refine h₁.trans (hm₀.trans (le_of_eq ?_))
    rw [hcA, mul_comm]
  have hlogcard : log (Fintype.card (∀ j : A, Fin (M j))) = ∑ j ∈ A, log (M j) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_coe_sort A fun k => M k, Nat.cast_prod, log_prod]
    exact fun k _ => by exact_mod_cast (hM k).ne'
  rw [hlogcard] at hb
  have hlog0 : 0 ≤ ∑ j ∈ A, log (M j : ℝ) := sum_nonneg fun k _ => log_natCast_nonneg _
  -- the covariance
  have hK := c'.avgCov_posSemidef
  have hdiag : c'.avgCov = diagonal fun j => c'.avgCov j j := by
    ext j l
    by_cases hjl : j = l
    · subst hjl
      simp
    · rw [diagonal_apply_ne _ hjl]
      exact c.cut_avgCov_off G A B m₀ hkjB hM hjl
  have hrate : gvRate G' c'.avgCov ≤ gvRate G' (P • 1) := by
    refine gvRate_mono G' hK ?_
    have e₂ : P • (1 : Matrix A A ℝ) - c'.avgCov = diagonal fun j => P - c'.avgCov j j := by
      conv_lhs => rw [hdiag]
      ext j l
      by_cases hjl : j = l
      · subst hjl
        simp
      · simp [hjl]
    rw [e₂]
    exact posSemidef_diagonal_iff.mpr fun j => sub_nonneg.mpr
      (c.cut_avgCov_diag_le G A B m₀ hkjB hM hn hpow j)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc _ ≤ (1 - c'.avgErrProb G') * ∑ j ∈ A, log (M j : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hlog0
    _ ≤ _ := hb
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hrate hn')

end GNCode

end Converse

/-! ### The cutset bound -/

section Cutset

variable {r t : Type*} [Fintype r] [Fintype t] [DecidableEq r] [DecidableEq t]
  {G : Matrix r t ℝ} {D : t → Finset r} {P : ℝ≥0} {R : t → ℝ}

/-- **Page 20-4 of [elgamal2010]: the cutset bound with no cooperation.** For a set `A` of senders
and a set `B` of receivers, such that each sender of `A` has a destination in `B`,
`∑_{j ∈ A} R_j ≤ ½ log |I + P G(B, A) G(B, A)ᵀ|`, where the rates are converted to nats. -/
theorem IsAchievableGN.sum_le (h : IsAchievableGN G D P R) (A : Finset t) (B : Finset r)
    (hAB : ∀ j ∈ A, ∃ k ∈ B, k ∈ D j) :
    (∑ j ∈ A, R j) * log 2 ≤
      gvRate (G.submatrix (Subtype.val : B → r) (Subtype.val : A → t)) ((P : ℝ) • 1) := by
  classical
  obtain ⟨c, hpow, hc⟩ := h
  have hpos : ∀ (n : ℕ) (j : t), 0 < 2 ^ ⌈(n : ℝ) * R j⌉₊ := fun n j => by positivity
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have h1 : ∀ n, (c n).errProb G D ≤ 1 := fun n => by
    have : Nonempty (∀ j, Fin (2 ^ ⌈(n : ℝ) * R j⌉₊)) := ⟨fun j => ⟨0, hpos n j⟩⟩
    have hc0 : (0 : ℝ) < Fintype.card (∀ j, Fin (2 ^ ⌈(n : ℝ) * R j⌉₊)) := by
      exact_mod_cast Fintype.card_pos
    rw [GNCode.errProb, div_le_one hc0]
    calc _ ≤ ∑ _m : ∀ j, Fin (2 ^ ⌈(n : ℝ) * R j⌉₊), (1 : ℝ) :=
          sum_le_sum fun _ _ => measureReal_le_one
      _ = _ := by simp
  refine le_of_converse_bound hc h1 fun n hn => ?_
  have hb := (c n).one_sub_errProb_mul_le G (hpos n) hn (hpow n) D A B hAB
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by linarith [h1 n])) hb
  -- the number of messages
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : (0 : ℝ) < ⌈exp (n * ((∑ j ∈ A, R j) * log 2))⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr (exp_pos _)
  have hce : exp (n * ((∑ j ∈ A, R j) * log 2)) ≤ ∏ j ∈ A, ((2 ^ ⌈(n : ℝ) * R j⌉₊ : ℕ) : ℝ) := by
    have h₂ : (n : ℝ) * ((∑ j ∈ A, R j) * log 2) = ∑ j ∈ A, (n : ℝ) * R j * log 2 := by
      rw [sum_mul, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [h₂, exp_sum]
    refine prod_le_prod₀ (fun j _ => (exp_pos _).le) fun j _ => ?_
    push_cast
    rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (log 2)]
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog.le)
  have hceil : (⌈exp (n * ((∑ j ∈ A, R j) * log 2))⌉₊ : ℝ) ≤
      ∏ j ∈ A, ((2 ^ ⌈(n : ℝ) * R j⌉₊ : ℕ) : ℝ) := by
    have h₃ : ⌈exp (n * ((∑ j ∈ A, R j) * log 2))⌉₊ ≤ ∏ j ∈ A, (2 ^ ⌈(n : ℝ) * R j⌉₊ : ℕ) :=
      Nat.ceil_le.mpr (by exact_mod_cast hce)
    exact_mod_cast h₃
  refine (log_le_log hexp hceil).trans (le_of_eq ?_)
  rw [log_prod]
  exact fun j _ => by
    have := hpos n j
    exact_mod_cast this.ne'

end Cutset

end InfoTheory
