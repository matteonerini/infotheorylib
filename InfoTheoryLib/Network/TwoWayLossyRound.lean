/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayLossyConverse

/-!
# Two-way lossy source coding: one round of Wyner–Ziv coding

The achievability of Theorem 4 of Lecture 21 of El Gamal and Kim uses one Wyner–Ziv code in each
round. This file bounds the error of one round, for a fixed past `vⁿ` known to the two nodes and
fixed source sequences, over a random codebook and random bins. The codewords are drawn from
`∏ᵢ p(uᵢ | vᵢ)`, and the speaker selects the first codeword jointly typical with `(vⁿ, xⁿ)`.

The law of the sources given the past is not a product law, so the first codeword is handled by the
Markov lemma of Lecture 13, and only the typicality of `(vⁿ, x_sⁿ, x_oⁿ)` is used.

## Main statements

* `sum_codebook_kaspi_le`: the selected codeword is typical with the sources.
* `sum_codebooks_bins_le`: adding the codewords that fall in the same bin.
* `exists_kaspi_round`: **the bound for one round**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω υ a b δ : Type*} [Fintype Ω] [Fintype υ] [Fintype a] [Fintype b] [Fintype δ]
  {μ : Ω → ℝ} {V : Ω → υ} {Xs : Ω → a} {Xo : Ω → b} {U : Ω → δ} {n L : ℕ}

/-! ### The kernel given the past and the speaker -/

section Kernel

/-- The Markov chain `Xₒ → (V, Xₛ) → U`, in the form of the Markov lemma. -/
lemma exists_markov_kernel [Nonempty δ] (hμ : IsPMF μ)
    (hM : I[Xo : U | pair V Xs ; μ] = 0) :
    ∃ κ : υ × a → δ → ℝ, IsChannel κ ∧
      (∀ y, dist μ (pair V Xs) y ≠ 0 → κ y = condDist μ U (pair V Xs) y) ∧
      ∀ x y u, dist μ (pair (pair Xo (pair V Xs)) U) ((x, y), u) =
        marg (dist μ (pair (pair Xo (pair V Xs)) U)) (x, y) * κ y u := by
  classical
  set Y := pair V Xs with hY
  have hr : IsPMF (dist μ (pair Y U)) := hμ.dist _
  obtain ⟨κ₀, hκ₀, hker⟩ := exists_kernel hr
  have hfst : dist (dist μ (pair Y U)) Prod.fst = dist μ Y := by
    rw [← dist_comp_eq]
    rfl
  have hκeq : ∀ y, dist μ Y y ≠ 0 → κ₀ y = condDist μ U Y y := fun y hy => by
    funext u
    have h₁ := hker y u
    rw [hfst] at h₁
    simp only [condDist]
    rw [h₁]
    field_simp
  refine ⟨κ₀, hκ₀, hκeq, fun x y u => ?_⟩
  have hlaw := (condIndep_iff_dist_eq hμ Xo U Y).1 ((condMutualInfo_eq_zero_iff hμ Xo U Y).1 hM)
  have hmarg : marg (dist μ (pair (pair Xo Y) U)) (x, y) = dist μ (pair Xo Y) (x, y) := by
    rw [marg_eq_dist, ← dist_comp_eq]
    rfl
  have e₁ : dist μ (pair (pair Xo Y) U) ((x, y), u) = dist μ (pair Y (pair Xo U)) (y, x, u) := by
    refine (dist_eq_of_injective μ (U := pair (pair Xo Y) U) (V := pair Y (pair Xo U))
      (fun t : (b × (υ × a)) × δ => (t.1.2, t.1.1, t.2)) ?_ (fun _ => rfl) ((x, y), u)).symm
    rintro ⟨⟨a₁, a₂⟩, a₃⟩ ⟨⟨b₁, b₂⟩, b₃⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    tauto
  have e₂ : dist μ (pair Xo Y) (x, y) = dist μ (pair Y Xo) (y, x) := by
    exact (dist_eq_of_injective μ (U := pair Xo Y) (V := pair Y Xo) Prod.swap Prod.swap_injective
      (fun _ => rfl) (x, y)).symm
  rw [e₁, hlaw, hmarg, e₂]
  simp only [condProdDist]
  by_cases hy : dist μ Y y = 0
  · have h₃ := dist_pair_le_left hμ Y Xo y x
    have h₄ := (hμ.dist (pair Y Xo)).nonneg (y, x)
    rw [hy] at h₃
    rw [le_antisymm h₃ h₄]
    simp
  · have h₁ := hker y u
    rw [hfst] at h₁
    rw [h₁]
    field_simp

omit [Fintype υ] in
/-- The entropy of a letter given the past is that of the joint law. -/
lemma condDist_pair [Finite υ] (μ : Ω → ℝ) (V : Ω → υ) (U : Ω → δ) :
    condPMF (dist μ (pair V U)) = condDist μ U V := by
  have := Fintype.ofFinite υ
  funext v u
  simp only [condPMF, condDist]
  rw [marg_eq_dist, ← dist_comp_eq]
  rfl

end Kernel

/-! ### The selected codeword -/

section Selected

variable [Nonempty δ]

open Classical in
/-- **The selected codeword is typical with the sources**, by the Markov lemma. -/
theorem sum_codebook_kaspi_le (hμ : IsPMF μ) (hM : I[Xo : U | pair V Xs ; μ] = 0)
    {ε ε₁ ε₂ : ℝ} (hε : ε₁ < ε) (hε1 : ε - ε₁ ≤ 1) (hε₂ : ε₂ ≤ 1 / 2) (hε₂0 : 0 ≤ ε₂) (hn : 0 < n)
    (l₀ : Fin L) {v : Fin n → υ} {xs : Fin n → a} {xo : Fin n → b}
    (ht : zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ (pair Xo (pair V Xs))) n ε₁)
    (hρ : IsPMF (channelExt (condDist μ U V) n v))
    (hlow : (1 - ε₂) * exp (-(n * (I[Xs : U | V ; μ] + ε₂ * (2 * log (Fintype.card δ))))) ≤
      prob (channelExt (condDist μ U V) n v) (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v
        xs))) :
    ∑ C : Fin L → Fin n → δ, iidPMF (channelExt (condDist μ U V) n v) L C *
      (if zipSeq (zipSeq xo (zipSeq v xs)) (C (firstIn
        (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v xs)) C l₀)) ∈
          robustTypicalSet (dist μ (pair (pair Xo (pair V Xs)) U)) n ε then 0 else 1) ≤
    exp (-(L * ((1 - ε₂) * exp (-(n * (I[Xs : U | V ; μ] + ε₂ * (2 * log (Fintype.card δ)))))))) +
      2 * (exp (n * (4 * (ε₂ * log (Fintype.card δ)))) *
        condExpBound (dist μ (pair (pair Xo (pair V Xs)) U)) ε₁ ε n) := by
  obtain ⟨κ, hκ, hκeq, hmk⟩ := exists_markov_kernel (Xo := Xo) (V := V) (Xs := Xs) (U := U) hμ hM
  set J := triLaw μ V Xs U with hJd
  have hJ : IsPMF J := hμ.dist _
  set ρ := channelExt (condDist μ U V) n v with hρd
  have hlaw := iidPMF_isPMF hρ L
  set A := condRobustTypicalSet J ε₂ (zipSeq v xs) with hA
  set q := dist μ (pair (pair Xo (pair V Xs)) U) with hq
  have hqp : IsPMF q := hμ.dist _
  set T := condRobustTypicalSet q ε (zipSeq xo (zipSeq v xs)) with hT
  set c := log (Fintype.card δ) with hc
  have hc0 : 0 ≤ c := log_natCast_nonneg _
  set Iv := I[Xs : U | V ; μ] with hIv
  set low := (1 - ε₂) * exp (-(n * (Iv + ε₂ * (2 * c)))) with hlowd
  have hε₂1 : 0 < 1 - ε₂ := by linarith
  have hlow0 : 0 < low := mul_pos hε₂1 (exp_pos _)
  have ha0 : 0 < prob ρ A := hlow0.trans_le hlow
  set Hu := H[U | V ; μ] with hHu
  set Hc := H[U | pair V Xs ; μ] with hHc
  have hHu0 : 0 ≤ Hu := condEntropy_nonneg hμ _ _
  have hHc0 : 0 ≤ Hc := condEntropy_nonneg hμ _ _
  have hHul : Hu ≤ c := condEntropy_le_log_card' hμ U V
  have hHcl : Hc ≤ c := condEntropy_le_log_card' hμ U (pair V Xs)
  have hI : Iv = Hu - Hc := by
    have e₁ : I[Xs : U | V ; μ] = I[U : Xs | V ; μ] := condMutualInfo_comm hμ _ _ _
    rw [hIv, e₁, condMutualInfo]
    congr 1
    exact (condEntropy_congr_right hμ U (X := pair Xs V) (X' := pair V Xs) Prod.swap
      Prod.swap_injective fun _ => rfl).symm
  set f : (Fin n → δ) → ℝ := fun z => if z ∉ T then 1 else 0 with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by simp only [hf]; split_ifs <;> norm_num
  have hmem : ∀ z, (if zipSeq (zipSeq xo (zipSeq v xs)) z ∈ robustTypicalSet q n ε then
      (0 : ℝ) else 1) = f z := fun z => by
    simp only [hf, hT, mem_condRobustTypicalSet]
    split_ifs <;> simp_all
  have hsplit : ∀ C : Fin L → Fin n → δ, f (C (firstIn A C l₀)) ≤
      (if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) +
        (if ∀ l, C l ∉ A then 1 else 0) := fun C => by
    by_cases h : ∃ l, C l ∈ A
    · have h' : ¬ ∀ l, C l ∉ A := by
        push Not
        exact h
      simp [h, h']
    · have h' : ∀ l, C l ∉ A := fun l hl => h ⟨l, hl⟩
      rw [ite_eq_right h, ite_eq_left h', zero_add]
      simp only [hf]
      split_ifs <;> norm_num
  have h1 := sum_codebook_firstIn_le hρ ha0 hf0 l₀ (L := L)
  have h2 := sum_iidPMF_ite_forall_not_mem_le hρ L A
  -- the Markov lemma
  set φ : (Fin n → δ) → ℝ := fun z => if z ∈ A then ρ z / prob ρ A / 2 else 0 with hφ
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    simp only [hφ]
    split_ifs
    · exact div_nonneg (div_nonneg (hρ.nonneg z) ha0.le) (by norm_num)
    · exact le_rfl
  have hJA : ∀ z ∈ A, zipSeq (zipSeq v xs) z ∈ robustTypicalSet J n ε₂ :=
    fun z hz => mem_condRobustTypicalSet.1 hz
  have hne : ∀ z ∈ A, ∀ i, dist μ (pair V Xs) (zipSeq v xs i) ≠ 0 := fun z hz i h => by
    have h₃ := pos_of_mem_robustTypicalSet hJ.nonneg (hJA z hz) i
    have h₄ : J (zipSeq (zipSeq v xs) z i) ≤ dist μ (pair V Xs) (zipSeq v xs i) := by
      exact dist_pair_le_left hμ (pair V Xs) U _ _
    rw [h] at h₄
    exact absurd h₃ (not_lt.2 h₄)
  have hAk : ∀ z ∈ A, exp (-(n * (Hc + ε₂ * Hc))) ≤ channelExt κ n (zipSeq v xs) z := fun z hz => by
    have h₃ := le_channelExt_condPMF_of_mem hJ (hJA z hz)
    have e₁ : H[Prod.snd | Prod.fst ; J] = Hc := by
      rw [hJd, triLaw]
      exact (condEntropy_dist hμ _ _ _).trans rfl
    rw [e₁] at h₃
    refine h₃.trans (le_of_eq (prod_congr rfl fun i _ => ?_))
    have e₂ : condPMF J (zipSeq v xs i) = κ (zipSeq v xs i) := by
      rw [hκeq _ (hne z hz i), hJd, triLaw]
      exact congrFun (condDist_pair μ (pair V Xs) U) _
    exact congrFun e₂ (z i)
  have hφA : ∀ z ∈ A, φ z ≤ exp (-(n * (Hu - ε₂ * Hu - (Iv + ε₂ * (2 * c))))) := fun z hz => by
    have h₃ := comp_mem_robustTypicalSet (hJA z hz) fun w : (υ × a) × δ => (w.1.1, w.2)
    have e₁ : dist J (fun w : (υ × a) × δ => (w.1.1, w.2)) = dist μ (pair V U) := by
      rw [hJd, triLaw, ← dist_comp_eq]
      rfl
    rw [e₁] at h₃
    have e₂ : (fun w : (υ × a) × δ => (w.1.1, w.2)) ∘ zipSeq (zipSeq v xs) z = zipSeq v z := rfl
    rw [e₂] at h₃
    have hb := channelExt_condPMF_le_of_mem (hμ.dist (pair V U)) h₃
    have e₃ : H[Prod.snd | Prod.fst ; dist μ (pair V U)] = Hu :=
      (condEntropy_dist hμ _ _ _).trans rfl
    rw [e₃, condDist_pair] at hb
    simp only [hφ, hz, ite_true]
    have h4 : ρ z / prob ρ A / 2 ≤ exp (-(n * (Hu - ε₂ * Hu))) / low / 2 := by
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      exact div_le_div₀ (exp_pos _).le hb hlow0 hlow
    refine h4.trans (le_of_le_of_eq (b := exp (-(n * (Hu - ε₂ * Hu))) *
      exp (n * (Iv + ε₂ * (2 * c)))) ?_ ?_)
    · simp only [hlowd]
      rw [div_div, div_le_iff₀ (by positivity)]
      have h5 : 1 ≤ (1 - ε₂) * 2 := by linarith
      have hE := mul_pos (exp_pos (-(n * (Hu - ε₂ * Hu)))) (exp_pos (n * (Iv + ε₂ * (2 * c))))
      have hrw : exp (n * (Iv + ε₂ * (2 * c))) * exp (-(n * (Iv + ε₂ * (2 * c)))) = 1 := by
        rw [← exp_add]
        simp
      calc exp (-(n * (Hu - ε₂ * Hu))) = exp (-(n * (Hu - ε₂ * Hu))) *
            (exp (n * (Iv + ε₂ * (2 * c))) * exp (-(n * (Iv + ε₂ * (2 * c))))) := by
            rw [hrw, mul_one]
        _ ≤ exp (-(n * (Hu - ε₂ * Hu))) * exp (n * (Iv + ε₂ * (2 * c))) *
            ((1 - ε₂) * exp (-(n * (Iv + ε₂ * (2 * c)))) * 2) := by
            have := exp_pos (-(n * (Iv + ε₂ * (2 * c))))
            nlinarith [mul_le_mul_of_nonneg_left h5 (mul_pos hE this).le]
    · rw [← exp_add]
      congr 1
      ring
  have hmarg : margFst q = dist μ (pair Xo (pair V Xs)) := by
    rw [hq, margFst, ← dist_comp_eq]
    rfl
  have hm := sum_not_mem_condRobust_le (q := q) (κ := κ) hqp hκ
    (fun x y u => hmk x y u) hε hε1 hn (by rw [hmarg]; exact ht) hφ0 A hAk hφA
  have hoff : ∑ z, (if z ∉ A then φ z else 0) = 0 := sum_eq_zero fun z _ => by
    simp only [hφ]
    split_ifs <;> simp_all
  rw [hoff, zero_add] at hm
  have hGle : (n : ℝ) * (Hc + ε₂ * Hc - (Hu - ε₂ * Hu - (Iv + ε₂ * (2 * c)))) ≤
      n * (4 * (ε₂ * c)) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    rw [hI]
    nlinarith
  have hcond := condExpBound_nonneg q ε₁ ε n
  have hm' : ∑ z, (if z ∉ T then φ z else 0) ≤ exp (n * (4 * (ε₂ * c))) *
      condExpBound q ε₁ ε n :=
    hm.trans (mul_le_mul_of_nonneg_right (exp_le_exp.2 hGle) hcond)
  have hsum : (∑ z ∈ A, ρ z * f z) / prob ρ A = 2 * ∑ z, (if z ∉ T then φ z else 0) := by
    have hA' : ∑ z ∈ A, ρ z * f z = ∑ z, if z ∈ A then ρ z * f z else 0 := by
      rw [sum_ite_mem, univ_inter]
    rw [hA', sum_div, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    simp only [hφ, hf]
    by_cases h3 : z ∈ A <;> by_cases h4 : z ∈ T <;> simp [h3, h4]
    field_simp
  have hmiss : exp (-(L * prob ρ A)) ≤ exp (-(L * low)) :=
    exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg L)))
  calc ∑ C : Fin L → Fin n → δ, iidPMF ρ L C *
        (if zipSeq (zipSeq xo (zipSeq v xs)) (C (firstIn A C l₀)) ∈ robustTypicalSet q n ε
          then 0 else 1)
      = ∑ C : Fin L → Fin n → δ, iidPMF ρ L C * f (C (firstIn A C l₀)) :=
        sum_congr rfl fun C _ => by rw [hmem]
    _ ≤ ∑ C : Fin L → Fin n → δ, iidPMF ρ L C *
          ((if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) +
            (if ∀ l, C l ∉ A then 1 else 0)) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hsplit C) (hlaw.nonneg C)
    _ = ∑ C : Fin L → Fin n → δ, iidPMF ρ L C *
          (if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) +
        ∑ C : Fin L → Fin n → δ, iidPMF ρ L C * (if ∀ l, C l ∉ A then 1 else 0) := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun C _ => mul_add _ _ _
    _ ≤ _ := by
        have h3 : (∑ z ∈ A, ρ z * f z) / prob ρ A ≤
            2 * (exp (n * (4 * (ε₂ * c))) * condExpBound q ε₁ ε n) := by
          rw [hsum]
          exact mul_le_mul_of_nonneg_left hm' (by norm_num)
        have h4 : ∑ C : Fin L → Fin n → δ, iidPMF ρ L C * (if ∀ l, C l ∉ A then 1 else 0) ≤
            exp (-(L * low)) := by
          refine le_trans (le_of_eq ?_) (h2.trans hmiss)
          exact sum_congr rfl fun C _ => by congr
        have h5 : ∑ C : Fin L → Fin n → δ, iidPMF ρ L C *
            (if ∃ l, C l ∈ A then f (C (firstIn A C l₀)) else 0) ≤
            2 * (exp (n * (4 * (ε₂ * c))) * condExpBound q ε₁ ε n) := by
          refine le_trans (le_of_eq ?_) (h1.trans h3)
          exact sum_congr rfl fun C _ => by congr
        rw [add_comm]
        exact add_le_add h4 h5

end Selected

/-! ### The bins -/

section Bins

variable {M : ℕ} {X : Type*} [Fintype X]

open Classical in
/-- The decoder of a round: the first index of the bin `m` whose codeword is in `S`. -/
def kDec (B : Fin L → Fin M) (S : Finset X) (C : Fin L → X) (l₀ : Fin L) (m : Fin M) : Fin L :=
  if h : ∃ l, B l = m ∧ C l ∈ S then h.choose else l₀

omit [Fintype X] in
open Classical in
/-- The decoder recovers the index `l` if no other codeword of its bin is in `S`. -/
lemma kDec_eq {B : Fin L → Fin M} {S : Finset X} {C : Fin L → X} (l₀ l : Fin L) (hl : C l ∈ S)
    (hu : ∀ l' ∈ univ.erase l, ¬ (B l' = B l ∧ C l' ∈ S)) : kDec B S C l₀ (B l) = l := by
  have hex : ∃ l', B l' = B l ∧ C l' ∈ S := ⟨l, rfl, hl⟩
  simp only [kDec, hex, ↓reduceDIte]
  by_contra hne
  exact hu _ (mem_erase.2 ⟨hne, mem_univ _⟩) hex.choose_spec

open Classical in
/-- The bound on the codewords of the bin of `l`, over the bins and the codebook. -/
lemma sum_codebooks_bins_le {ρ : X → ℝ} (hρ : IsPMF ρ) (hM : 0 < M) (sel : (Fin L → X) → Fin L)
    (T S : Finset X) :
    ∑ C : Fin L → X, iidPMF ρ L C * ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
      (if C (sel C) ∈ T ∧ ∀ l' ∈ univ.erase (sel C), ¬ (B l' = B (sel C) ∧ C l' ∈ S)
        then 0 else 1) ≤
      ∑ C : Fin L → X, iidPMF ρ L C * (if C (sel C) ∈ T then 0 else 1) +
        L * prob ρ S / M := by
  have hneM : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hlawC := iidPMF_isPMF hρ L
  have hlawB := iidPMF_isPMF (uniformPMF_isPMF (α := Fin M)) L
  have hpt : ∀ (C : Fin L → X) (B : Fin L → Fin M),
      (if C (sel C) ∈ T ∧ ∀ l' ∈ univ.erase (sel C), ¬ (B l' = B (sel C) ∧ C l' ∈ S)
        then (0 : ℝ) else 1) ≤ (if C (sel C) ∈ T then 0 else 1) +
        ∑ l' ∈ univ.erase (sel C), (if B l' = B (sel C) then 1 else 0) *
          (if C l' ∈ S then 1 else 0) := fun C B => by
    have h₀ : (0 : ℝ) ≤ ∑ l' ∈ univ.erase (sel C), (if B l' = B (sel C) then 1 else 0) *
        (if C l' ∈ S then 1 else 0) :=
      sum_nonneg fun _ _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
    by_cases hg : C (sel C) ∈ T ∧ ∀ l' ∈ univ.erase (sel C), ¬ (B l' = B (sel C) ∧ C l' ∈ S)
    · rw [ite_eq_left hg]
      split_ifs <;> linarith
    · rw [ite_eq_right hg]
      by_cases hT : C (sel C) ∈ T
      · simp only [hT, ite_true, zero_add]
        have hu : ¬ ∀ l' ∈ univ.erase (sel C), ¬ (B l' = B (sel C) ∧ C l' ∈ S) := fun h => hg ⟨hT,
          h⟩
        push Not at hu
        obtain ⟨l', hl', hb, hs⟩ := hu
        have := single_le_sum (f := fun l' => (if B l' = B (sel C) then (1 : ℝ) else 0) *
          (if C l' ∈ S then 1 else 0))
          (fun _ _ => mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)) hl'
        simpa [hb, hs] using this
      · simp only [hT, ite_false]
        linarith
  have hC : ∀ C : Fin L → X, ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
      (if C (sel C) ∈ T ∧ ∀ l' ∈ univ.erase (sel C), ¬ (B l' = B (sel C) ∧ C l' ∈ S)
        then 0 else 1) ≤ (if C (sel C) ∈ T then 0 else 1) +
        (∑ l', if C l' ∈ S then (1 : ℝ) else 0) / M := fun C => by
    calc _ ≤ ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
          ((if C (sel C) ∈ T then 0 else 1) + ∑ l' ∈ univ.erase (sel C),
            (if B l' = B (sel C) then 1 else 0) * (if C l' ∈ S then 1 else 0)) :=
          sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (hpt C B) (hlawB.nonneg B)
      _ = (if C (sel C) ∈ T then 0 else 1) + ∑ B : Fin L → Fin M,
            iidPMF (uniformPMF (Fin M)) L B * ∑ l' ∈ univ.erase (sel C),
            (if B l' = B (sel C) then 1 else 0) * (if C l' ∈ S then 1 else 0) := by
          simp only [mul_add, sum_add_distrib]
          rw [← sum_mul, hlawB.sum_eq_one, one_mul]
      _ ≤ _ := add_le_add le_rfl (sum_bins_erase_le hM (sel C)
          fun l' => by split_ifs <;> norm_num)
  have hcount : ∑ C : Fin L → X, iidPMF ρ L C * (∑ l', if C l' ∈ S then (1 : ℝ) else 0) =
      L * prob ρ S := by
    simp only [mul_sum]
    rw [sum_comm]
    have e : ∀ l' : Fin L, ∑ C : Fin L → X, iidPMF ρ L C * (if C l' ∈ S then (1 : ℝ) else 0) =
        prob ρ S := fun l' => by
      rw [sum_iidPMF_eval hρ l' fun x => if x ∈ S then (1 : ℝ) else 0]
      simp only [prob, mul_ite, mul_one, mul_zero]
      rw [sum_ite_mem, univ_inter]
    simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc _ ≤ ∑ C : Fin L → X, iidPMF ρ L C * ((if C (sel C) ∈ T then 0 else 1) +
        (∑ l', if C l' ∈ S then (1 : ℝ) else 0) / M) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hC C) (hlawC.nonneg C)
    _ = _ := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        rw [← hcount, sum_div]
        exact sum_congr rfl fun C _ => by ring

end Bins

/-! ### One round -/

section Round

variable [Nonempty δ]

open Classical in
/-- The failure of one round: the selected codeword is not typical with the sources, or another
codeword of its bin is typical with what the other node knows. -/
def kFail {X : Type*} {L M : ℕ} (A T S : Finset X) (l₀ : Fin L) (C : Fin L → X)
    (B : Fin L → Fin M) : ℝ :=
  if C (firstIn A C l₀) ∈ T ∧ ∀ l' ∈ univ.erase (firstIn A C l₀),
    ¬ (B l' = B (firstIn A C l₀) ∧ C l' ∈ S) then 0 else 1

open Classical in
/-- The bound for one round, for a fixed length. -/
lemma sum_kFail_le (hμ : IsPMF μ) (hM : I[Xo : U | pair V Xs ; μ] = 0) {ε ε₁ ε₂ : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε₁ < ε) (hε1 : ε - ε₁ ≤ 1) (hε₂ : ε₂ ≤ 1 / 2) (hε₂0 : 0 ≤ ε₂) (hn : 0 < n) {M : ℕ}
    (hM0 : 0 < M) (l₀ : Fin L) {v : Fin n → υ} {xs : Fin n → a} {xo : Fin n → b}
    (ht : zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ (pair Xo (pair V Xs))) n ε₁)
    (hρ : IsPMF (channelExt (condDist μ U V) n v))
    (hlow : (1 - ε₂) * exp (-(n * (I[Xs : U | V ; μ] + ε₂ * (2 * log (Fintype.card δ))))) ≤
      prob (channelExt (condDist μ U V) n v) (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v
        xs))) :
    ∑ C : Fin L → Fin n → δ, iidPMF (channelExt (condDist μ U V) n v) L C *
      ∑ B : Fin L → Fin M, iidPMF (uniformPMF (Fin M)) L B *
        kFail (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v xs))
          (condRobustTypicalSet (dist μ (pair (pair Xo (pair V Xs)) U)) ε (zipSeq xo (zipSeq v xs)))
          (condRobustTypicalSet (triLaw μ V Xo U) ε (zipSeq v xo)) l₀ C B ≤
    exp (-(L * ((1 - ε₂) * exp (-(n * (I[Xs : U | V ; μ] + ε₂ * (2 * log (Fintype.card δ)))))))) +
      2 * (exp (n * (4 * (ε₂ * log (Fintype.card δ)))) *
        condExpBound (dist μ (pair (pair Xo (pair V Xs)) U)) ε₁ ε n) +
      L * exp (-(n * (I[Xo : U | V ; μ] - ε * (2 * log (Fintype.card δ))))) / M := by
  have hsel := sum_codebook_kaspi_le (Xo := Xo) hμ hM hε hε1 hε₂ hε₂0 hn l₀ ht hρ hlow
  have hbin := sum_codebooks_bins_le hρ hM0
    (fun C => firstIn (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v xs)) C l₀)
    (condRobustTypicalSet (dist μ (pair (pair Xo (pair V Xs)) U)) ε (zipSeq xo (zipSeq v xs)))
    (condRobustTypicalSet (triLaw μ V Xo U) ε (zipSeq v xo))
  have hprob := prob_triLaw_le (U := V) (W := Xo) (Y := U) hμ hε₀ v xo
  have hconv : ∑ C : Fin L → Fin n → δ, iidPMF (channelExt (condDist μ U V) n v) L C *
      (if C (firstIn (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v xs)) C l₀) ∈
        condRobustTypicalSet (dist μ (pair (pair Xo (pair V Xs)) U)) ε (zipSeq xo (zipSeq v xs))
        then 0 else 1) = ∑ C : Fin L → Fin n → δ, iidPMF (channelExt (condDist μ U V) n v) L C *
      (if zipSeq (zipSeq xo (zipSeq v xs)) (C (firstIn
        (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v xs)) C l₀)) ∈
          robustTypicalSet (dist μ (pair (pair Xo (pair V Xs)) U)) n ε then 0 else 1) := by
    refine sum_congr rfl fun C _ => ?_
    simp only [mem_condRobustTypicalSet]
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have h₃ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprob hL)
    (Nat.cast_nonneg (α := ℝ) M)
  refine le_trans hbin (add_le_add (le_trans (le_of_eq ?_) (hconv.le.trans hsel)) h₃)
  congr!

omit [Nonempty δ] in
/-- The choice of the parameters of one round. -/
lemma exists_round_params {rc rm : ℝ} (hc : I[Xs : U | V ; μ] < rc) {ε : ℝ}
    (hε : 0 < ε) (hεm : ε * (2 * log (Fintype.card δ)) + rc - I[Xo : U | V ; μ] < rm) :
    ∃ ε₂ > 0, ε₂ ≤ 1 / 2 ∧ ∀ η > 0, ∀ᶠ n : ℕ in atTop,
      exp (-(exp ((n : ℝ) * rc) * ((1 - ε₂) *
        exp (-(n * (I[Xs : U | V ; μ] + ε₂ * (2 * log (Fintype.card δ)))))))) ≤ η ∧
      2 * (exp (n * (4 * (ε₂ * log (Fintype.card δ)))) *
        condExpBound (dist μ (pair (pair Xo (pair V Xs)) U)) (ε / 2) ε n) ≤ η ∧
      exp (log 2 + n * rc) * exp (-(n * (I[Xo : U | V ; μ] - ε * (2 * log (Fintype.card δ))))) ≤
        η * exp (n * rm) := by
  obtain ⟨c, hcd⟩ : ∃ c, c = log (Fintype.card δ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hcd ▸ log_natCast_nonneg _
  rw [← hcd] at hεm ⊢
  obtain ⟨Is, hIs⟩ : ∃ Is, Is = I[Xs : U | V ; μ] := ⟨_, rfl⟩
  obtain ⟨Io, hIo⟩ : ∃ Io, Io = I[Xo : U | V ; μ] := ⟨_, rfl⟩
  rw [← hIs] at hc ⊢
  rw [← hIo] at hεm ⊢
  have hg0 : 0 < rc - Is := sub_pos.2 hc
  obtain ⟨c₀, hc₀, hlimM⟩ := exists_mul_condExpBound_tendsto
    (dist μ (pair (pair Xo (pair V Xs)) U)) (half_lt_self hε)
  obtain ⟨ε₂, hε₂d⟩ : ∃ ε₂, ε₂ =
    min (min (1 / 2) ((rc - Is) / (4 * (c + 1)))) (c₀ / (8 * (c + 1))) :=
    ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by
    rw [hε₂d]
    exact lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  have hε₂2 : ε₂ ≤ 1 / 2 := by
    rw [hε₂d]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₂g : ε₂ * (2 * c) ≤ (rc - Is) / 2 := by
    have h₁ : ε₂ ≤ (rc - Is) / (4 * (c + 1)) := by
      rw [hε₂d]
      exact (min_le_left _ _).trans (min_le_right _ _)
    calc ε₂ * (2 * c) ≤ (rc - Is) / (4 * (c + 1)) * (2 * c) :=
          mul_le_mul_of_nonneg_right h₁ (by positivity)
      _ ≤ (rc - Is) / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hε₂c : 4 * (ε₂ * c) < c₀ := by
    have h₁ : ε₂ ≤ c₀ / (8 * (c + 1)) := by
      rw [hε₂d]
      exact min_le_right _ _
    have h₂ : ε₂ * c ≤ c₀ / (8 * (c + 1)) * c := mul_le_mul_of_nonneg_right h₁ hc0
    have h₃ : c₀ / (8 * (c + 1)) * c ≤ c₀ / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  refine ⟨ε₂, hε₂0, hε₂2, fun η hη => ?_⟩
  have hl₁ := tendsto_exp_neg_layer (a := Is + (rc - Is) / 2) (b := rc) (c := 1 / 2)
    (by linarith) (by norm_num)
  have hl₂ := (hlimM (4 * (ε₂ * c)) hε₂c).const_mul 2
  rw [mul_zero] at hl₂
  have hg₂0 : 0 < rm - (ε * (2 * c) + rc - Io) := sub_pos.2 hεm
  have hl₃ : Tendsto (fun n : ℕ => exp (log 2) * exp (-(n * (rm - (ε * (2 * c) + rc - Io)))))
      atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_mul_nat hg₂0).const_mul (exp (log 2))
  filter_upwards [(tendsto_order.1 hl₁).2 η hη, (tendsto_order.1 hl₂).2 η hη,
    (tendsto_order.1 hl₃).2 η hη] with n s₁ s₂ s₃
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨le_trans (exp_le_exp.2 (neg_le_neg ?_)) s₁.le, s₂.le, ?_⟩
  · have h₁ : (1 / 2 : ℝ) * exp (-(n * (Is + (rc - Is) / 2))) ≤
        (1 - ε₂) * exp (-(n * (Is + ε₂ * (2 * c)))) := by
      refine mul_le_mul (by linarith) (exp_le_exp.2 ?_) (exp_pos _).le (by linarith)
      have : (n : ℝ) * (ε₂ * (2 * c)) ≤ n * ((rc - Is) / 2) :=
        mul_le_mul_of_nonneg_left hε₂g hn'
      nlinarith
    exact mul_le_mul_of_nonneg_left h₁ (exp_pos _).le
  · have e : exp (log 2 + n * rc) * exp (-(n * (Io - ε * (2 * c)))) =
        exp (log 2) * exp (-(n * (rm - (ε * (2 * c) + rc - Io)))) * exp (n * rm) := by
      rw [← exp_add, ← exp_add, ← exp_add]
      congr 1
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right s₃.le (exp_pos _).le

open Classical in
/-- **The bound for one round of Wyner–Ziv coding**, on page 21-22 of [elgamal2010]. If the covering
rate `rc` exceeds `I(Xₛ; U | V)` and the rate `rm` of the bins exceeds `rc - I(Xₒ; U | V)`, then for
all large `n` and all typical `(vⁿ, xₛⁿ, xₒⁿ)`, the selected codeword is typical with the sources
and no other codeword of its bin is typical with `(vⁿ, xₒⁿ)`, except with probability `η` over the
codebook and the bins. -/
theorem exists_kaspi_round (hμ : IsPMF μ) (hM : I[Xo : U | pair V Xs ; μ] = 0) {rc rm : ℝ}
    (hc : I[Xs : U | V ; μ] < rc) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεm : ε * (2 * log (Fintype.card δ)) + rc - I[Xo : U | V ; μ] < rm) :
    ∃ ε' > 0, ε' ≤ ε ∧ ∃ ε₂ > 0, ε₂ ≤ 1 / 2 ∧ ∀ η > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (M : ℕ) (_ : exp (n * rm) ≤ M) (l₀ : Fin ⌈exp ((n : ℝ) * rc)⌉₊)
        (v : Fin n → υ) (xs : Fin n → a) (xo : Fin n → b),
        zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ (pair Xo (pair V Xs))) n ε' →
        IsPMF (iidPMF (channelExt (condDist μ U V) n v) ⌈exp ((n : ℝ) * rc)⌉₊) ∧
        ∑ C : Fin ⌈exp ((n : ℝ) * rc)⌉₊ → Fin n → δ,
          iidPMF (channelExt (condDist μ U V) n v) ⌈exp ((n : ℝ) * rc)⌉₊ C *
          ∑ B : Fin ⌈exp ((n : ℝ) * rc)⌉₊ → Fin M,
            iidPMF (uniformPMF (Fin M)) ⌈exp ((n : ℝ) * rc)⌉₊ B *
            kFail (condRobustTypicalSet (triLaw μ V Xs U) ε₂ (zipSeq v xs))
              (condRobustTypicalSet (dist μ (pair (pair Xo (pair V Xs)) U)) ε
                (zipSeq xo (zipSeq v xs)))
              (condRobustTypicalSet (triLaw μ V Xo U) ε (zipSeq v xo)) l₀ C B ≤ η := by
  obtain ⟨ε₂, hε₂0, hε₂2, hpar⟩ := exists_round_params (Xo := Xo) hc hε hεm
  have hε₁ε : ε / 2 < ε := half_lt_self hε
  have hε₁0 : 0 < ε / 2 := half_pos hε
  refine ⟨min (ε / 2) (ε₂ / 2), lt_min hε₁0 (half_pos hε₂0), (min_le_left _ _).trans hε₁ε.le, ε₂,
    hε₂0, hε₂2, fun η hη => ?_⟩
  have hb := eventually_triLaw_ge (U := V) (W := Xs) (Y := U) hμ (ε := ε₂) (half_lt_self hε₂0)
    hε₂0 (by linarith)
  have hIs0 : 0 ≤ I[Xs : U | V ; μ] := condMutualInfo_nonneg hμ _ _ _
  filter_upwards [hb, hpar (η / 3) (by positivity), eventually_gt_atTop 0] with n hb' hpn hn0
    M hMge l₀ v xs xo ht
  obtain ⟨s₁, s₂, s₃⟩ := hpn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hM0 : 0 < M := by
    have : (0 : ℝ) < M := (exp_pos _).trans_le hMge
    exact_mod_cast this
  have hty₁ : zipSeq xo (zipSeq v xs) ∈ robustTypicalSet (dist μ (pair Xo (pair V Xs))) n (ε / 2) :=
    robustTypicalSet_mono (hμ.dist _).nonneg (min_le_left _ _) ht
  have hty₂ : zipSeq v xs ∈ robustTypicalSet (dist μ (pair V Xs)) n (ε₂ / 2) := by
    have h₁ := comp_mem_robustTypicalSet (robustTypicalSet_mono (hμ.dist _).nonneg
      (min_le_right _ _) ht) Prod.snd
    rwa [← dist_comp_eq] at h₁
  have hρ := channelExt_condDist_isPMF hμ U V (u := v) fun i => dist_ne_zero_of_mem hμ hty₂ i
  refine ⟨iidPMF_isPMF hρ _, ?_⟩
  refine (sum_kFail_le (Xo := Xo) hμ hM hε.le hε₁ε (by linarith) hε₂2 hε₂0.le hn0 hM0 l₀ hty₁ hρ
    (hb' v xs hty₂)).trans ?_
  have h₁ : exp (-((⌈exp ((n : ℝ) * rc)⌉₊ : ℝ) * ((1 - ε₂) *
      exp (-(n * (I[Xs : U | V ; μ] + ε₂ * (2 * log (Fintype.card δ)))))))) ≤ η / 3 := by
    refine le_trans (exp_le_exp.2 (neg_le_neg ?_)) s₁
    refine mul_le_mul_of_nonneg_right (Nat.le_ceil _) (mul_nonneg (by linarith) (exp_pos _).le)
  have h₃ : (⌈exp ((n : ℝ) * rc)⌉₊ : ℝ) *
      exp (-(n * (I[Xo : U | V ; μ] - ε * (2 * log (Fintype.card δ))))) / M ≤ η / 3 := by
    have hrc0 : 0 ≤ (n : ℝ) * rc := mul_nonneg hn'.le (hIs0.trans hc.le)
    rw [div_le_iff₀ (by exact_mod_cast hM0)]
    refine (mul_le_mul_of_nonneg_right (ceil_exp_le hrc0) (exp_pos _).le).trans (s₃.trans ?_)
    exact mul_le_mul_of_nonneg_left hMge (by positivity)
  linarith

end Round

end InfoTheory
