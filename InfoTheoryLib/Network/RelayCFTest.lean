/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayBlockIID

/-!
# Bounds on the tests of compress–forward

The bounds of the fresh sequences of `sum_fresh_le`, for each sequence of the context, and the bound
on the probability that a random codebook misses a set of typical sequences.

## Main statements

* `sum_fresh_point`: the probability that a fresh sequence is jointly typical with a fixed sequence.
* `sum_fresh_const`: the same for a fresh sequence that is i.i.d. from a fixed law.
* `sum_miss_le`: the probability that a random codebook misses a set.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Fresh

variable {A N K : Type*} [Fintype A] [Fintype N] [Fintype K]

/-- A sum over a fresh sequence of the law of a pair is the law of the first sequence. -/
lemma sum_iidPMF_pair (L : A × N → ℝ) {n : ℕ} (r : Fin n → A) :
    ∑ t : Fin n → N, iidPMF L n (fun i => (r i, t i)) = iidPMF (dist L Prod.fst) n r := by
  classical
  have h := sum_iidPMF_mul_prod (fun _ : N => (1 : ℝ)) (n := n) fun i b => L (r i, b)
  simp only [iidPMF, one_mul, prod_const_one, dist_fst] at h ⊢
  exact h

/-- **The bound for a fresh sequence, for a fixed sequence of the context.** Let `(V, T) ∼ L`. Let a
sequence `tⁿ` be generated, given `vⁿ`, by `n` uses of the conditional law of `T` given `K = g(V)`.
Then for every `vⁿ` the probability that `(vⁿ, tⁿ)` is jointly typical is about
  `exp(-n I(T; V | K))`.
-/
theorem sum_fresh_point {L : A × N → ℝ} (hL : IsPMF L) (g : A → K) {κ : K → N → ℝ}
    (hκ : ∀ k t, dist L (fun z => (g z.1, z.2)) (k, t) = dist L (fun z => g z.1) k * κ k t)
    (hκc : IsChannel κ) {n : ℕ} {ε : ℝ} (Test : (Fin n → A) → (Fin n → N) → Prop)
    (hT : ∀ r t, Test r t → (fun i => (r i, t i)) ∈ robustTypicalSet L n ε) (r : Fin n → A) :
    ∑ t, seqChan κ n (fun i => g (r i)) t * ind (Test r t) ≤
      exp (-(n * (H[Prod.fst ; L] + H[fun z => (g z.1, z.2) ; L] - H[fun z => g z.1 ; L] -
        entropy L - ε * (entropy L + H[Prod.fst ; L] + H[fun z => (g z.1, z.2) ; L] +
          H[fun z => g z.1 ; L])))) := by
  classical
  set q := dist L Prod.fst with hq
  have hqP : IsPMF q := hL.dist _
  set LK := dist L fun z : A × N => (g z.1, z.2) with hLK
  have hLKP : IsPMF LK := hL.dist _
  set qK := dist L fun z : A × N => g z.1 with hqK
  have hqKP : IsPMF qK := hL.dist _
  set HV := H[Prod.fst ; L] with hHV
  set HKN := H[fun z => (g z.1, z.2) ; L] with hHKN
  set HK := H[fun z => g z.1 ; L] with hHK
  set HL := entropy L with hHL
  have hHV' : entropy q = HV := rfl
  have hHKN' : entropy LK = HKN := rfl
  have hHK' : entropy qK = HK := rfl
  set F := univ.filter fun t => Test r t with hF
  have hsum : ∑ t, seqChan κ n (fun i => g (r i)) t * ind (Test r t) =
      ∑ t ∈ F, seqChan κ n (fun i => g (r i)) t := by
    rw [hF, sum_filter]
    refine sum_congr rfl fun t _ => ?_
    by_cases h : Test r t
    · rw [ind_of_pos h, mul_one, ite_eq_left h]
    · rw [ind_of_neg h, mul_zero, ite_eq_right h]
  rw [hsum]
  rcases F.eq_empty_or_nonempty with hE | ⟨t₀, ht₀⟩
  · rw [hE, sum_empty]
    positivity
  have ht₀' : Test r t₀ := (mem_filter.mp ht₀).2
  -- `rⁿ` is typical
  have hr : r ∈ robustTypicalSet q n ε := comp_mem_robustTypicalSet (hT r t₀ ht₀') Prod.fst
  have e₁ := iidPMF_le_of_mem_robustTypicalSet hqP hr
  rw [hHV'] at e₁
  -- the bound of a sequence
  set Mt := exp (-(n * (HKN - ε * HKN))) * exp (n * (HK + ε * HK)) with hMt
  have hs : ∀ t ∈ F, seqChan κ n (fun i => g (r i)) t ≤ Mt := by
    intro t ht
    have hx := hT r t (mem_filter.mp ht).2
    have h₂ : (fun i => g (r i)) ∈ robustTypicalSet qK n ε :=
      comp_mem_robustTypicalSet hx fun z : A × N => g z.1
    have h₃ : (fun i => (g (r i), t i)) ∈ robustTypicalSet LK n ε :=
      comp_mem_robustTypicalSet hx fun z : A × N => (g z.1, z.2)
    have e₂ := le_iidPMF_of_mem_robustTypicalSet hqKP h₂
    have e₃ := iidPMF_le_of_mem_robustTypicalSet hLKP h₃
    rw [hHK'] at e₂
    rw [hHKN'] at e₃
    have hfac : iidPMF LK n (fun i => (g (r i), t i)) =
        iidPMF qK n (fun i => g (r i)) * seqChan κ n (fun i => g (r i)) t := by
      simp only [iidPMF, seqChan, ← prod_mul_distrib]
      exact prod_congr rfl fun i _ => hκ _ _
    have hc0 := (seqChan_isChannel hκc n (fun i => g (r i))).nonneg t
    have hexp : exp (n * (HK + ε * HK)) * exp (-(n * (HK + ε * HK))) = 1 := by
      rw [← exp_add]
      simp
    calc seqChan κ n (fun i => g (r i)) t
        = (exp (n * (HK + ε * HK)) * exp (-(n * (HK + ε * HK)))) *
            seqChan κ n (fun i => g (r i)) t := by rw [hexp, one_mul]
      _ ≤ exp (n * (HK + ε * HK)) * (iidPMF qK n (fun i => g (r i)) *
            seqChan κ n (fun i => g (r i)) t) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          exact mul_le_mul_of_nonneg_right e₂ hc0
      _ ≤ exp (n * (HK + ε * HK)) * exp (-(n * (HKN - ε * HKN))) :=
          mul_le_mul_of_nonneg_left (hfac ▸ e₃) (exp_pos _).le
      _ = Mt := mul_comm _ _
  -- the number of sequences
  have hcard : (F.card : ℝ) * exp (-(n * (HL + ε * HL))) ≤ exp (-(n * (HV - ε * HV))) := by
    calc (F.card : ℝ) * exp (-(n * (HL + ε * HL)))
        = ∑ _t ∈ F, exp (-(n * (HL + ε * HL))) := by simp
      _ ≤ ∑ t ∈ F, iidPMF L n (fun i => (r i, t i)) := sum_le_sum fun t ht =>
          le_iidPMF_of_mem_robustTypicalSet hL (hT r t (mem_filter.mp ht).2)
      _ ≤ ∑ t : Fin n → N, iidPMF L n (fun i => (r i, t i)) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun t _ _ => (iidPMF_isPMF hL n).nonneg _
      _ = iidPMF q n r := sum_iidPMF_pair L r
      _ ≤ _ := e₁
  have hcard' : (F.card : ℝ) ≤ exp (-(n * (HV - ε * HV))) * exp (n * (HL + ε * HL)) := by
    have hexp : exp (-(n * (HL + ε * HL))) * exp (n * (HL + ε * HL)) = 1 := by
      rw [← exp_add]
      simp
    calc (F.card : ℝ) = (F.card : ℝ) * exp (-(n * (HL + ε * HL))) * exp (n * (HL + ε * HL)) := by
          rw [mul_assoc, hexp, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (exp_pos _).le
  calc ∑ t ∈ F, seqChan κ n (fun i => g (r i)) t ≤ ∑ _t ∈ F, Mt := sum_le_sum hs
    _ = (F.card : ℝ) * Mt := by simp
    _ ≤ (exp (-(n * (HV - ε * HV))) * exp (n * (HL + ε * HL))) * Mt :=
        mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = _ := by
        simp only [hMt]
        rw [← exp_add, ← exp_add, ← exp_add]
        congr 1
        ring

/-- **The bound for a fresh i.i.d. sequence, for a fixed sequence of the context.** -/
theorem sum_fresh_const {L : A × N → ℝ} (hL : IsPMF L) {n : ℕ} {ε : ℝ}
    (Test : (Fin n → A) → (Fin n → N) → Prop)
    (hT : ∀ r t, Test r t → (fun i => (r i, t i)) ∈ robustTypicalSet L n ε) (r : Fin n → A) :
    ∑ t, iidPMF (dist L Prod.snd) n t * ind (Test r t) ≤
      exp (-(n * (H[Prod.fst ; L] + H[Prod.snd ; L] - entropy L -
        ε * (entropy L + H[Prod.fst ; L] + H[Prod.snd ; L])))) := by
  classical
  have hm : IsPMF (dist L Prod.snd) := hL.dist _
  have hu : ∀ k : Unit, dist L (fun _ : A × N => ()) k = 1 := by
    intro k
    simp only [dist]
    simpa using hL.sum_eq_one
  have hp : ∀ (k : Unit) t, dist L (fun z : A × N => ((), z.2)) (k, t) = dist L Prod.snd t := by
    intro k t
    simp [dist]
  have h := sum_fresh_point (K := Unit) hL (fun _ => ()) (κ := fun _ => dist L Prod.snd)
    (fun k t => by rw [hp, hu, one_mul]) (fun _ => hm) Test hT r
  have h₁ : H[fun z : A × N => ((), z.2) ; L] = H[Prod.snd ; L] :=
    entropyRV_comp_injective L Prod.snd (f := fun t => ((), t)) fun _ _ h => (Prod.ext_iff.mp h).2
  have h₂ : H[fun _ : A × N => () ; L] = 0 := by
    have : dist L (fun _ : A × N => ()) = fun _ => 1 := funext hu
    simp [entropyRV, this, entropy]
  rw [h₁, h₂] at h
  refine le_trans (le_of_eq rfl) (h.trans (le_of_eq ?_))
  congr 3
  ring

end Fresh

section Miss

variable {T : Type*} [Fintype T]

/-- **The probability that a random codebook misses a set.** If every sequence of a set `G` has
probability at least `y` times its probability under `Q`, then a codebook of `K` sequences misses
`G` with probability at most `1 - Q(G) + exp(-y K)`. -/
theorem sum_miss_le {P Q : T → ℝ} (hP : IsPMF P) (hQ : IsPMF Q) {G : T → Prop} {y : ℝ}
    (hy1 : y ≤ 1) (hy : ∀ v, G v → Q v * y ≤ P v) (K : ℕ) : ∑ C : Fin K → T, iidPMF P K C * ∏ k,
    ind (¬ G (C k)) ≤ 1 - ∑ v, Q v * ind (G v) + exp (-(y * K)) := by
  classical
  set a := ∑ v, Q v * ind (G v) with ha
  have ha0 : 0 ≤ a := sum_nonneg fun v _ => mul_nonneg (hQ.nonneg v) (ind_nonneg _)
  have ha1 : a ≤ 1 := by
    calc a ≤ ∑ v, Q v := sum_le_sum fun v _ => by
          have := mul_le_mul_of_nonneg_left (ind_le_one (G v)) (hQ.nonneg v)
          linarith
      _ = 1 := hQ.sum_eq_one
  have hsp : ∀ v, ind (¬ G v) = 1 - ind (G v) := by
    intro v
    by_cases h : G v
    · rw [ind_of_neg (not_not.mpr h), ind_of_pos h]
      ring
    · rw [ind_of_pos h, ind_of_neg h]
      ring
  have hs := sum_iidPMF_mul_prod P (n := K) fun _ v => ind (¬ G v)
  rw [hs, prod_const, card_univ, Fintype.card_fin]
  have hb : ∑ v, P v * ind (¬ G v) ≤ 1 - a * y := by
    have h₁ : ∑ v, P v * ind (¬ G v) = 1 - ∑ v, P v * ind (G v) := by
      rw [eq_sub_iff_add_eq, ← sum_add_distrib, ← hP.sum_eq_one]
      refine sum_congr rfl fun v _ => ?_
      rw [hsp]
      ring
    have h₂ : a * y ≤ ∑ v, P v * ind (G v) := by
      rw [ha, sum_mul]
      refine sum_le_sum fun v _ => ?_
      by_cases h : G v
      · rw [ind_of_pos h, mul_one, mul_one]
        exact hy v h
      · rw [ind_of_neg h, mul_zero, mul_zero, zero_mul]
    linarith
  have h0 : 0 ≤ ∑ v, P v * ind (¬ G v) := sum_nonneg fun v _ =>
    mul_nonneg (hP.nonneg v) (ind_nonneg _)
  calc (∑ v, P v * ind (¬ G v)) ^ K ≤ (1 - a * y) ^ K := pow_le_pow_left₀ h0 hb K
    _ ≤ 1 - a + exp (-(y * K)) := one_sub_mul_pow_le ha0 ha1 hy1 K

end Miss

section Tilt

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- **A change of the law of a sequence**, on the typical sequences: the law of `cⁿ` given
`(aⁿ, bⁿ)` is at most `exp(n I(B; C | A))` times the law of `cⁿ` given `aⁿ`. -/
theorem tilt_le {J : (A × B) × C → ℝ} (hJ : IsPMF J) {τ : A × B → C → ℝ} {q : A → C → ℝ}
    (hτ : ∀ a c, J (a, c) = dist J Prod.fst a * τ a c)
    (hq : ∀ a c, dist J (fun z => (z.1.1, z.2)) (a, c) = dist J (fun z => z.1.1) a * q a c)
    {n : ℕ} {ε : ℝ} {a : Fin n → A} {b : Fin n → B} {c : Fin n → C}
    (h : (fun i => ((a i, b i), c i)) ∈ robustTypicalSet J n ε) :
    seqChan τ n (fun i => (a i, b i)) c * exp (-(n * (H[Prod.fst ; J] +
        H[fun z => (z.1.1, z.2) ; J] - H[fun z => z.1.1 ; J] - entropy J +
        ε * (H[Prod.fst ; J] + H[fun z => (z.1.1, z.2) ; J] + H[fun z => z.1.1 ; J] +
          entropy J)))) ≤ seqChan q n a c := by
  have hUS : IsPMF (dist J Prod.fst) := hJ.dist _
  have hUV : IsPMF (dist J fun z => (z.1.1, z.2)) := hJ.dist _
  have hU : IsPMF (dist J fun z => z.1.1) := hJ.dist _
  have h₁ := comp_mem_robustTypicalSet h Prod.fst
  have h₂ := comp_mem_robustTypicalSet h fun z : (A × B) × C => (z.1.1, z.2)
  have h₃ := comp_mem_robustTypicalSet h fun z : (A × B) × C => z.1.1
  have e₁ := iidPMF_le_of_mem_robustTypicalSet hJ h
  have e₂ := le_iidPMF_of_mem_robustTypicalSet hUS h₁
  have e₃ := le_iidPMF_of_mem_robustTypicalSet hUV h₂
  have e₄ := iidPMF_le_of_mem_robustTypicalSet hU h₃
  set HUS := H[Prod.fst ; J] with hHUS
  set HUV := H[fun z => (z.1.1, z.2) ; J] with hHUV
  set HU := H[fun z => z.1.1 ; J] with hHU
  set HJ := entropy J with hHJ
  have hfac₁ : iidPMF J n (fun i => ((a i, b i), c i)) =
      iidPMF (dist J Prod.fst) n (fun i => (a i, b i)) * seqChan τ n (fun i => (a i, b i)) c := by
    simp only [iidPMF, seqChan, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hτ _ _
  have hfac₂ : iidPMF (dist J fun z => (z.1.1, z.2)) n (fun i => (a i, c i)) =
      iidPMF (dist J fun z => z.1.1) n a * seqChan q n a c := by
    simp only [iidPMF, seqChan, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hq _ _
  rw [hfac₁] at e₁
  have e₃' : exp (-(n * (HUV + ε * HUV))) ≤ iidPMF (dist J fun z => z.1.1) n a * seqChan q n a c :=
    hfac₂ ▸ e₃
  have hpos₁ : 0 < iidPMF (dist J Prod.fst) n fun i => (a i, b i) := lt_of_lt_of_le (exp_pos _) e₂
  have hpos₂ := lt_of_lt_of_le (exp_pos _) e₃'
  have hU0 := (iidPMF_isPMF hU n).nonneg a
  have hpos₃ : 0 < iidPMF (dist J fun z => z.1.1) n a := by
    rcases hU0.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at hpos₂
      exact absurd hpos₂ (lt_irrefl _)
  have hq0 : 0 < seqChan q n a c := by
    rcases (le_or_gt (seqChan q n a c) 0) with h' | h'
    · nlinarith
    · exact h'
  -- the bound of the law given `(aⁿ, bⁿ)`
  have hτle : seqChan τ n (fun i => (a i, b i)) c ≤
      exp (-(n * (HJ - ε * HJ))) * exp (n * (HUS + ε * HUS)) := by
    have hexp : exp (n * (HUS + ε * HUS)) * exp (-(n * (HUS + ε * HUS))) = 1 := by
      rw [← exp_add]
      simp
    have hc0 : 0 ≤ seqChan τ n (fun i => (a i, b i)) c ∨ seqChan τ n (fun i => (a i, b i)) c < 0 :=
      le_or_gt _ _
    rcases hc0 with hc0 | hc0
    · calc seqChan τ n (fun i => (a i, b i)) c
          = (exp (n * (HUS + ε * HUS)) * exp (-(n * (HUS + ε * HUS)))) *
              seqChan τ n (fun i => (a i, b i)) c := by rw [hexp, one_mul]
        _ ≤ exp (n * (HUS + ε * HUS)) * (iidPMF (dist J Prod.fst) n (fun i => (a i, b i)) *
              seqChan τ n (fun i => (a i, b i)) c) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e₂ hc0) (exp_pos _).le
        _ ≤ exp (n * (HUS + ε * HUS)) * exp (-(n * (HJ - ε * HJ))) :=
            mul_le_mul_of_nonneg_left e₁ (exp_pos _).le
        _ = _ := mul_comm _ _
    · exact hc0.le.trans (by positivity)
  -- the bound of the law given `aⁿ`
  have hqge : exp (-(n * (HUV + ε * HUV))) * exp (n * (HU - ε * HU)) ≤ seqChan q n a c := by
    have hexp : exp (-(n * (HU - ε * HU))) * exp (n * (HU - ε * HU)) = 1 := by
      rw [← exp_add]
      simp
    calc _ ≤ iidPMF (dist J fun z => z.1.1) n a * seqChan q n a c * exp (n * (HU - ε * HU)) :=
          mul_le_mul_of_nonneg_right e₃' (exp_pos _).le
      _ ≤ exp (-(n * (HU - ε * HU))) * seqChan q n a c * exp (n * (HU - ε * HU)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e₄ hq0.le) (exp_pos _).le
      _ = _ := by
          rw [mul_comm (exp _) (seqChan q n a c), mul_assoc, hexp, mul_one]
  refine le_trans ?_ hqge
  calc _ ≤ exp (-(n * (HJ - ε * HJ))) * exp (n * (HUS + ε * HUS)) *
    exp (-(n * (HUS + HUV - HU - HJ +
        ε * (HUS + HUV + HU + HJ)))) := mul_le_mul_of_nonneg_right hτle (exp_pos _).le
    _ = _ := by
        rw [← exp_add, ← exp_add, ← exp_add]
        congr 1
        ring

end Tilt

end InfoTheory
