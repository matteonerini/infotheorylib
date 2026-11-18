/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Jensen

/-!
# Han's inequalities for submodular set functions

The entropy rates of subsets of random variables (Section 17.6) only use two properties of the
entropy `h(S) = h(X(S))` of a subset `S` of the variables: `h(∅) = 0` and submodularity,
`h(S ∪ T) + h(S ∩ T) ≤ h(S) + h(T)`, which is the fact that conditioning reduces entropy. We prove
Han's inequalities for any such set function on the subsets of `{0, …, n - 1}`, so that they apply
to discrete entropies (`Inequalities.SubsetEntropy`) and to the logarithms of the principal minors
of a positive definite matrix (`Inequalities.Determinant`).

For the average per element over the `k`-element subsets,
`h_k = (1/C(n, k)) ∑_{|S| = k} h(S)/k`, Theorem 17.6.1 says that `h₁ ≥ h₂ ≥ ⋯ ≥ hₙ`. The same
holds for the averages of `e^{r h(S)/k}` (Theorem 17.6.2); for the conditional quantities
`g(S) = h(S | Sᶜ) = h(univ) - h(Sᶜ)` the averages per element increase (Theorem 17.6.3), and for
`h(S) - h(S | Sᶜ)`, the mutual information `I(X(S); X(Sᶜ))`, they decrease (Theorem 17.6.4).

## Main definitions

* `IsSubmodular f`: `f (A ∪ B) + f (A ∩ B) ≤ f A + f B`.
* `subsetAvg f k`: **(17.51)** `(1/C(n, k)) ∑_{|S| = k} f(S)/k`.
* `subsetExpAvg f r k`: **(17.55)** `(1/C(n, k)) ∑_{|S| = k} e^{r f(S)/k}`.
* `subsetCondAvg f k`: **(17.59)** `(1/C(n, k)) ∑_{|S| = k} (f(univ) - f(Sᶜ))/k`.
* `subsetMutAvg f k`: **(17.65)** `(1/C(n, k)) ∑_{|S| = k} (f(S) + f(Sᶜ) - f(univ))/k`.

## Main statements

* `card_sub_one_mul_le_sum_erase`: **(17.53)** `(|S| - 1) f(S) ≤ ∑_{i ∈ S} f(S \ {i})`.
* `subsetAvg_succ_le`: **Theorem 17.6.1 (Han).**
* `subsetExpAvg_succ_le`: **Theorem 17.6.2.**
* `subsetCondAvg_le_succ`: **Theorem 17.6.3 (Han).**
* `subsetMutAvg_succ_le`: **Theorem 17.6.4.**

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 17.6
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {n : ℕ} (f : Finset (Fin n) → ℝ)

/-- A set function is submodular if `f (A ∪ B) + f (A ∩ B) ≤ f A + f B`. -/
def IsSubmodular : Prop := ∀ A B : Finset (Fin n), f (A ∪ B) + f (A ∩ B) ≤ f A + f B

/-- **(17.51)** The average per element `(1/C(n, k)) ∑_{|S| = k} f(S)/k` over the `k`-element
subsets. -/
def subsetAvg (k : ℕ) : ℝ := (∑ S ∈ powersetCard k univ, f S / k) / n.choose k

/-- **(17.55)** The average `(1/C(n, k)) ∑_{|S| = k} e^{r f(S)/k}`. -/
def subsetExpAvg (r : ℝ) (k : ℕ) : ℝ := (∑ S ∈ powersetCard k univ, exp (r * f S / k)) / n.choose k

/-- **(17.59)** The average per element `(1/C(n, k)) ∑_{|S| = k} (f(univ) - f(Sᶜ))/k` of the
conditional quantities. -/
def subsetCondAvg (k : ℕ) : ℝ := (∑ S ∈ powersetCard k univ, (f univ - f Sᶜ) / k) / n.choose k

/-- **(17.65)** The average per element `(1/C(n, k)) ∑_{|S| = k} (f(S) + f(Sᶜ) - f(univ))/k`. -/
def subsetMutAvg (k : ℕ) : ℝ :=
  (∑ S ∈ powersetCard k univ, (f S + f Sᶜ - f univ) / k) / n.choose k

variable {f}

/-- Removing one element at a time: `∑_{i ∈ S} (f(S) - f(S \ {i})) ≤ f(S) - f(∅)`. -/
theorem sum_sub_erase_le (hf : IsSubmodular f) (S : Finset (Fin n)) :
    ∑ i ∈ S, (f S - f (S.erase i)) ≤ f S - f ∅ := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [sum_insert ha, erase_insert ha]
    have hle : ∀ i ∈ S, f (insert a S) - f ((insert a S).erase i) ≤ f S - f (S.erase i) := by
      intro i hi
      have h := hf ((insert a S).erase i) S
      have e1 : (insert a S).erase i ∪ S = insert a S := by
        ext j
        simp only [mem_union, mem_erase, mem_insert]
        constructor
        · rintro (⟨-, h⟩ | h)
          · exact h
          · exact Or.inr h
        · intro h
          by_cases hj : j = i
          · exact Or.inr (hj ▸ hi)
          · exact Or.inl ⟨hj, h⟩
      have e2 : (insert a S).erase i ∩ S = S.erase i := by
        ext j
        simp only [mem_inter, mem_erase, mem_insert]
        constructor
        · rintro ⟨⟨hj, -⟩, h⟩
          exact ⟨hj, h⟩
        · rintro ⟨hj, h⟩
          exact ⟨⟨hj, Or.inr h⟩, h⟩
      rw [e1, e2] at h
      linarith
    have := sum_le_sum hle
    linarith

/-- **(17.53)** For `f(∅) = 0`, `(|S| - 1) f(S) ≤ ∑_{i ∈ S} f(S \ {i})`. -/
theorem card_sub_one_mul_le_sum_erase (hf : IsSubmodular f) (h0 : f ∅ = 0)
    (S : Finset (Fin n)) : ((#S : ℝ) - 1) * f S ≤ ∑ i ∈ S, f (S.erase i) := by
  have h := sum_sub_erase_le hf S
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, h0, sub_zero] at h
  linarith

/-- Adding the elements of `A` to `B` one at a time:
`f(B ∪ A) - f(B) ≤ ∑_{i ∈ A} (f(B ∪ {i}) - f(B))` for `A` disjoint from `B`. -/
theorem sub_le_sum_insert (hf : IsSubmodular f) (B : Finset (Fin n)) :
    ∀ A : Finset (Fin n), Disjoint A B →
      f (B ∪ A) - f B ≤ ∑ i ∈ A, (f (insert i B) - f B) := by
  intro A
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    intro hd
    rw [sum_insert ha]
    have hd' : Disjoint A B := disjoint_of_subset_left (subset_insert a A) hd
    have haB : a ∉ B := fun h => disjoint_left.1 hd (mem_insert_self a A) h
    have h := hf (insert a B) (B ∪ A)
    have e1 : insert a B ∪ (B ∪ A) = B ∪ insert a A := by
      ext j; simp only [mem_union, mem_insert]; tauto
    have e2 : insert a B ∩ (B ∪ A) = B := by
      ext j
      simp only [mem_inter, mem_insert, mem_union]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact h1 ▸ h2
        · exact absurd (h1 ▸ h2) ha
        · exact h1
        · exact h1
      · intro h
        exact ⟨Or.inr h, Or.inl h⟩
    rw [e1, e2] at h
    have := ih hd'
    linarith

/-- The double counting `∑_{|S| = k+1} ∑_{i ∈ S} φ(S \ {i}) = (n - k) ∑_{|T| = k} φ(T)`. -/
theorem sum_powersetCard_sum_erase (k : ℕ) (φ : Finset (Fin n) → ℝ) :
    ∑ S ∈ powersetCard (k + 1) univ, ∑ i ∈ S, φ (S.erase i) =
      ((n : ℝ) - k) * ∑ T ∈ powersetCard k univ, φ T := by
  classical
  have h1 : ∑ S ∈ powersetCard (k + 1) univ, ∑ i ∈ S, φ (S.erase i) =
      ∑ i, ∑ S ∈ (powersetCard (k + 1) univ).filter (fun S => i ∈ S), φ (S.erase i) := by
    rw [sum_comm' (t' := univ) (s' := fun i => (powersetCard (k + 1) univ).filter (fun S => i ∈ S))]
    intro S i
    simp
  have h2 : ∀ i, ∑ S ∈ (powersetCard (k + 1) univ).filter (fun S => i ∈ S), φ (S.erase i) =
      ∑ T ∈ (powersetCard k univ).filter (fun T => i ∉ T), φ T := fun i => by
    refine sum_nbij' (fun S => S.erase i) (fun T => insert i T) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powersetCard] at hS ⊢
      exact ⟨⟨subset_univ _, by rw [card_erase_of_mem hS.2, hS.1.2]; rfl⟩, notMem_erase i S⟩
    · intro T hT
      simp only [mem_filter, mem_powersetCard] at hT ⊢
      exact ⟨⟨subset_univ _, by rw [card_insert_of_notMem hT.2, hT.1.2]⟩, mem_insert_self i T⟩
    · intro S hS
      simp only [mem_filter] at hS
      exact insert_erase hS.2
    · intro T hT
      simp only [mem_filter] at hT
      exact erase_insert hT.2
    · intro S _
      rfl
  rw [h1, sum_congr rfl fun i _ => h2 i]
  rw [sum_comm' (t' := powersetCard k univ) (s' := fun T => univ.filter fun i => i ∉ T)]
  · rw [mul_sum]
    refine sum_congr rfl fun T hT => ?_
    rw [sum_const, nsmul_eq_mul]
    congr 1
    have hc : #(univ.filter fun i => i ∉ T) = n - k := by
      rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ T),
        card_univ, Fintype.card_fin, (mem_powersetCard.1 hT).2]
    rw [hc, Nat.cast_sub]
    have := card_le_univ T
    rw [Fintype.card_fin, (mem_powersetCard.1 hT).2] at this
    exact this
  · intro i T
    simp only [mem_filter, mem_univ, true_and]
    tauto

lemma choose_mul_eq {k : ℕ} (hk : k + 1 ≤ n) :
    (n.choose (k + 1) : ℝ) * (k + 1) = n.choose k * ((n : ℝ) - k) := by
  have h := Nat.choose_succ_right_eq n k
  have h' : ((n.choose (k + 1) * (k + 1) : ℕ) : ℝ) = ((n.choose k * (n - k) : ℕ) : ℝ) := by
    rw [h]
  push_cast [Nat.cast_sub (show k ≤ n by omega)] at h'
  exact h'

lemma subsetAvg_eq (k : ℕ) :
    subsetAvg f k = (∑ S ∈ powersetCard k univ, f S) / (k * n.choose k) := by
  rw [subsetAvg, ← Finset.sum_div, div_div]

lemma subsetCondAvg_eq (k : ℕ) :
    subsetCondAvg f k = (∑ S ∈ powersetCard k univ, (f univ - f Sᶜ)) / (k * n.choose k) := by
  rw [subsetCondAvg, ← Finset.sum_div, div_div]

/-- **Theorem 17.6.1 (Han), (17.52)–(17.54).** For a submodular set function with `f(∅) = 0`, the
average per element over the subsets of size `k` decreases with `k`: `h_{k+1} ≤ h_k`. -/
theorem subsetAvg_succ_le (hf : IsSubmodular f) (h0 : f ∅ = 0) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k + 1 ≤ n) : subsetAvg f (k + 1) ≤ subsetAvg f k := by
  have hbase : (k : ℝ) * ∑ S ∈ powersetCard (k + 1) univ, f S ≤
      ((n : ℝ) - k) * ∑ T ∈ powersetCard k univ, f T := by
    rw [← sum_powersetCard_sum_erase, mul_sum]
    refine sum_le_sum fun S hS => ?_
    have := card_sub_one_mul_le_sum_erase hf h0 S
    rw [(mem_powersetCard.1 hS).2] at this
    push_cast at this
    linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hnk : (0 : ℝ) < n - k := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    linarith
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega)
  have hc1 : (0 : ℝ) < n.choose (k + 1) := by exact_mod_cast Nat.choose_pos hkn
  have hid := choose_mul_eq (n := n) hkn
  rw [subsetAvg_eq, subsetAvg_eq]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∑ S ∈ powersetCard (k + 1) univ, f S) * (k * n.choose k)
      = (k * ∑ S ∈ powersetCard (k + 1) univ, f S) * n.choose k := by ring
    _ ≤ (((n : ℝ) - k) * ∑ T ∈ powersetCard k univ, f T) * n.choose k :=
        mul_le_mul_of_nonneg_right hbase hc.le
    _ = (∑ T ∈ powersetCard k univ, f T) * ((k + 1) * n.choose (k + 1)) := by
        rw [mul_comm ((k : ℝ) + 1), hid]; ring

/-- **Theorem 17.6.2, (17.55)–(17.58).** For `r ≥ 0`, the averages of `e^{r f(S)/k}` over the
subsets of size `k` decrease with `k`. -/
theorem subsetExpAvg_succ_le (hf : IsSubmodular f) (h0 : f ∅ = 0) {r : ℝ} (hr : 0 ≤ r) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k + 1 ≤ n) : subsetExpAvg f r (k + 1) ≤ subsetExpAvg f r k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  -- For each `(k+1)`-set, `e^{r f(S)/(k+1)} ≤ (1/(k+1)) ∑_{i ∈ S} e^{r f(S \ {i})/k}`.
  have hS : ∀ S ∈ powersetCard (k + 1) univ, exp (r * f S / (k + 1 : ℕ)) ≤
      (1 / ((k : ℝ) + 1)) * ∑ i ∈ S, exp (r * f (S.erase i) / k) := by
    intro S hS
    have hcard := (mem_powersetCard.1 hS).2
    have hbase := card_sub_one_mul_le_sum_erase hf h0 S
    rw [hcard] at hbase
    push_cast at hbase ⊢
    have hkS : (k : ℝ) * f S ≤ ∑ i ∈ S, f (S.erase i) := by simpa using hbase
    have hmean : r * f S / (k + 1) ≤
        ∑ i ∈ S, (1 / ((k : ℝ) + 1)) • (r * f (S.erase i) / k) := by
      have e : ∑ i ∈ S, (1 / ((k : ℝ) + 1)) • (r * f (S.erase i) / k) =
          r * (∑ i ∈ S, f (S.erase i)) / (k * (k + 1)) := by
        simp only [smul_eq_mul]
        rw [← mul_sum, ← Finset.sum_div, ← mul_sum]
        field_simp
      have e2 : r * f S / (k + 1) = r * (k * f S) / (k * (k + 1)) := by field_simp
      rw [e, e2]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkS hr) (by positivity)
    have hw : ∑ i ∈ S, (1 / ((k : ℝ) + 1)) = 1 := by
      rw [sum_const, hcard, nsmul_eq_mul]; push_cast; field_simp
    have hjensen := ConvexOn.map_sum_le convexOn_exp (t := S) (w := fun _ => 1 / ((k : ℝ) + 1))
      (p := fun i => r * f (S.erase i) / k) (fun i _ => by positivity) hw (fun i _ => trivial)
    simp only [smul_eq_mul] at hjensen hmean
    rw [mul_sum]
    exact (exp_le_exp.2 hmean).trans hjensen
  have hsum := sum_le_sum hS
  rw [← mul_sum, sum_powersetCard_sum_erase k (fun T => exp (r * f T / k))] at hsum
  have hnk : (0 : ℝ) < n - k := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    linarith
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega)
  have hc1 : (0 : ℝ) < n.choose (k + 1) := by exact_mod_cast Nat.choose_pos hkn
  have hid := choose_mul_eq (n := n) hkn
  unfold subsetExpAvg
  rw [div_le_div_iff₀ hc1 hc]
  calc (∑ S ∈ powersetCard (k + 1) univ, exp (r * f S / (k + 1 : ℕ))) * n.choose k
      ≤ (1 / ((k : ℝ) + 1) * (((n : ℝ) - k) *
          ∑ T ∈ powersetCard k univ, exp (r * f T / k))) * n.choose k :=
        mul_le_mul_of_nonneg_right hsum hc.le
    _ = (∑ T ∈ powersetCard k univ, exp (r * f T / k)) * n.choose (k + 1) := by
        set X := ∑ T ∈ powersetCard k univ, exp (r * f T / k)
        have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
        rw [show 1 / ((k : ℝ) + 1) * (((n : ℝ) - k) * X) * n.choose k =
          X * (n.choose k * ((n : ℝ) - k)) / (k + 1) by ring, ← hid]
        field_simp

/-- **Theorem 17.6.3 (Han), (17.60)–(17.64).** For a submodular set function, the average per
element of the conditional quantities `f(univ) - f(Sᶜ)` increases with `k`. -/
theorem subsetCondAvg_le_succ (hf : IsSubmodular f) {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    subsetCondAvg f k ≤ subsetCondAvg f (k + 1) := by
  classical
  -- For each `(k+1)`-set, `∑_{i ∈ S} g(S \ {i}) ≤ k g(S)`.
  have hS : ∀ S ∈ powersetCard (k + 1) univ,
      ∑ i ∈ S, (f univ - f (S.erase i)ᶜ) ≤ (k : ℝ) * (f univ - f Sᶜ) := by
    intro S hS
    have hcard := (mem_powersetCard.1 hS).2
    have h := sub_le_sum_insert hf Sᶜ S (disjoint_compl_right)
    have e : Sᶜ ∪ S = univ := by rw [union_comm, union_compl]
    rw [e] at h
    have e2 : ∀ i ∈ S, (S.erase i)ᶜ = insert i Sᶜ := fun i hi => by
      ext j; simp only [mem_compl, mem_erase, mem_insert]; tauto
    rw [sum_congr rfl fun i hi => by rw [e2 i hi]]
    have e3 : ∑ i ∈ S, (f univ - f (insert i Sᶜ)) =
        ((k : ℝ) + 1) * f univ - ∑ i ∈ S, f (insert i Sᶜ) := by
      rw [sum_sub_distrib, sum_const, hcard, nsmul_eq_mul]; push_cast; ring
    have e4 : ∑ i ∈ S, (f (insert i Sᶜ) - f Sᶜ) =
        ∑ i ∈ S, f (insert i Sᶜ) - ((k : ℝ) + 1) * f Sᶜ := by
      rw [sum_sub_distrib, sum_const, hcard, nsmul_eq_mul]; push_cast; ring
    rw [e3]
    rw [e4] at h
    linarith
  have hsum := sum_le_sum hS
  rw [sum_powersetCard_sum_erase (φ := fun T => f univ - f Tᶜ), ← mul_sum] at hsum
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hnk : (0 : ℝ) < n - k := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    linarith
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (by omega)
  have hc1 : (0 : ℝ) < n.choose (k + 1) := by exact_mod_cast Nat.choose_pos hkn
  have hid := choose_mul_eq (n := n) hkn
  rw [subsetCondAvg_eq, subsetCondAvg_eq]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set A := ∑ T ∈ powersetCard k univ, (f univ - f Tᶜ)
  set B := ∑ S ∈ powersetCard (k + 1) univ, (f univ - f Sᶜ)
  calc A * ((k + 1) * n.choose (k + 1)) = A * (((n : ℝ) - k) * n.choose k) := by
        rw [mul_comm ((k : ℝ) + 1), hid]; ring
    _ = (((n : ℝ) - k) * A) * n.choose k := by ring
    _ ≤ (k * B) * n.choose k := mul_le_mul_of_nonneg_right hsum hc.le
    _ = B * (k * n.choose k) := by ring

/-- `subsetMutAvg f k = subsetAvg f k - subsetCondAvg f k`. -/
lemma subsetMutAvg_eq (k : ℕ) : subsetMutAvg f k = subsetAvg f k - subsetCondAvg f k := by
  simp only [subsetMutAvg, subsetAvg, subsetCondAvg, ← sub_div, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun S _ => by ring

/-- **Theorem 17.6.4, (17.65)–(17.66).** The average per element of `f(S) + f(Sᶜ) - f(univ)`, the
mutual information `I(X(S); X(Sᶜ))` for entropies, decreases with `k`. -/
theorem subsetMutAvg_succ_le (hf : IsSubmodular f) (h0 : f ∅ = 0) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k + 1 ≤ n) : subsetMutAvg f (k + 1) ≤ subsetMutAvg f k := by
  rw [subsetMutAvg_eq, subsetMutAvg_eq]
  linarith [subsetAvg_succ_le hf h0 hk hkn, subsetCondAvg_le_succ hf hk hkn]

end InfoTheory
