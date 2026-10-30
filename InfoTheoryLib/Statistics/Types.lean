/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.StrongTypicality
public import InfoTheoryLib.RelativeEntropy.InformationInequality
public import InfoTheoryLib.Entropy.Collision

/-!
# The method of types

The type `Pₓ` of a sequence `x ∈ 𝒳ⁿ` is its empirical distribution `Pₓ(a) = N(a|x)/n`. There are
at most `(n + 1)^|𝒳|` types with denominator `n`, the probability of a sequence under an i.i.d.
law `Qⁿ` depends only on its type, `Qⁿ(x) = e^{-n(H(Pₓ) + D(Pₓ‖Q))}`, and the type class `T(P)`
has about `e^{nH(P)}` elements and probability about `e^{-nD(P‖Q)}`.

## Main definitions

* `typeOf x`: the type `Pₓ` of a sequence.
* `types α n`: the set `𝒫ₙ` of types with denominator `n`.
* `typeClass P n`: the type class `T(P)`.

## Main statements

* `card_types_le`: **Theorem 11.1.1**, `|𝒫ₙ| ≤ (n + 1)^|𝒳|`.
* `iidPMF_eq_exp_type`: **Theorem 11.1.2**, `Qⁿ(x) = e^{-n(H(Pₓ) + D(Pₓ‖Q))}`.
* `card_typeClass_mul_prod_factorial`: (11.17), `|T(P)| ∏ₐ (nP(a))! = n!`.
* `card_typeClass_le`, `exp_div_le_card_typeClass`: **Theorem 11.1.3**.
* `prob_typeClass_le`, `exp_div_le_prob_typeClass`: **Theorem 11.1.4**.
* `exists_typeOf_near`: every pmf is approximated by types within `|𝒳|/n`.

## Implementation notes

Logarithms are natural, so the book's `2^{-nH}` are our `e^{-nH}`. The type of the empty
sequence is `0` by convention; for `n > 0` types are pmfs. Statements involving `D(P‖Q)` assume
`P ≪ Q`, so that the relative entropy is finite.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 11.1
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### Types -/

omit [Fintype α] in
/-- **Definition (Section 11.1).** The type (empirical distribution) `Pₓ(a) = N(a|x)/n` of a
sequence `x ∈ 𝒳ⁿ`. -/
def typeOf {n : ℕ} (x : Fin n → α) (a : α) : ℝ := symbolCount x a / n

open Classical in
/-- **Definition (Section 11.1).** The set `𝒫ₙ` of types with denominator `n`. -/
def types (β : Type*) [Fintype β] (n : ℕ) : Finset (β → ℝ) := univ.image (typeOf (n := n))

open Classical in
/-- **Definition (11.2).** The type class `T(P) = {x ∈ 𝒳ⁿ : Pₓ = P}`. -/
def typeClass (P : α → ℝ) (n : ℕ) : Finset (Fin n → α) := univ.filter fun x => typeOf x = P

lemma mem_typeClass {P : α → ℝ} {n : ℕ} {x : Fin n → α} : x ∈ typeClass P n ↔ typeOf x = P := by
  classical
  simp [typeClass]

lemma typeOf_mem_types {n : ℕ} (x : Fin n → α) : typeOf x ∈ types α n := by
  classical
  simp [types]

lemma mem_types {P : α → ℝ} {n : ℕ} : P ∈ types α n ↔ ∃ x : Fin n → α, typeOf x = P := by
  classical
  simp [types]

lemma sum_symbolCount {n : ℕ} (x : Fin n → α) : ∑ a, (symbolCount x a : ℝ) = n := by
  classical
  simp only [symbolCount_eq_sum]
  rw [sum_comm]
  simp

omit [Fintype α] in
lemma typeOf_nonneg {n : ℕ} (x : Fin n → α) (a : α) : 0 ≤ typeOf x a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- For `n > 0` the type of a sequence is a pmf. -/
lemma typeOf_isPMF {n : ℕ} (hn : 0 < n) (x : Fin n → α) : IsPMF (typeOf x) := by
  refine ⟨typeOf_nonneg x, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [typeOf]
  rw [← sum_div, sum_symbolCount, div_self hn']

omit [Fintype α] in
lemma symbolCount_le {n : ℕ} (x : Fin n → α) (a : α) : symbolCount x a ≤ n := by
  classical
  unfold symbolCount
  exact (card_filter_le _ _).trans (by simp)

omit [Fintype α] in
/-- `nPₓ(a) = N(a|x)`. -/
lemma mul_typeOf {n : ℕ} (hn : 0 < n) (x : Fin n → α) (a : α) :
    n * typeOf x a = symbolCount x a := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [typeOf]
  field_simp

/-- **Theorem 11.1.1.** There are at most `(n + 1)^|𝒳|` types with denominator `n`. -/
theorem card_types_le (n : ℕ) : ((types α n).card : ℝ) ≤ (n + 1) ^ Fintype.card α := by
  classical
  set cnt : (Fin n → α) → α → Fin (n + 1) := fun x a => ⟨symbolCount x a,
    Nat.lt_succ_of_le (symbolCount_le x a)⟩
  set g : (α → Fin (n + 1)) → α → ℝ := fun c a => (c a : ℕ) / n
  have h : types α n ⊆ (univ : Finset (α → Fin (n + 1))).image g := by
    intro P hP
    obtain ⟨x, rfl⟩ := mem_types.1 hP
    exact mem_image.2 ⟨cnt x, mem_univ _, rfl⟩
  have := (card_le_card h).trans card_image_le
  rw [card_univ, Fintype.card_fun, Fintype.card_fin] at this
  exact_mod_cast this

/-! ### The probability of a sequence -/

/-- `Qⁿ(x) = ∏ₐ Q(a)^{N(a|x)}` (11.9). -/
lemma iidPMF_eq_prod_pow (Q : α → ℝ) {n : ℕ} (x : Fin n → α) :
    iidPMF Q n x = ∏ a, Q a ^ symbolCount x a := by
  classical
  rw [iidPMF, ← prod_fiberwise univ x fun i => Q (x i)]
  refine prod_congr rfl fun a _ => ?_
  rw [prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], prod_const, symbolCount]

/-- `Qⁿ(x) = e^{∑ₐ N(a|x) log Q(a)}` when every symbol of `x` has positive probability. -/
lemma iidPMF_eq_exp_sum {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {n : ℕ} {x : Fin n → α}
    (hx : ∀ a, symbolCount x a ≠ 0 → Q a ≠ 0) :
    iidPMF Q n x = exp (∑ a, symbolCount x a * log (Q a)) := by
  rw [iidPMF_eq_prod_pow, exp_sum]
  refine prod_congr rfl fun a _ => ?_
  by_cases h0 : symbolCount x a = 0
  · simp [h0]
  · rw [exp_nat_mul, exp_log (lt_of_le_of_ne (hQ a) (hx a h0).symm)]

/-- **Theorem 11.1.2.** The probability of a sequence under the i.i.d. law `Qⁿ` depends only on
its type: `Qⁿ(x) = e^{-n(H(Pₓ) + D(Pₓ‖Q))}`, for `Pₓ ≪ Q`. -/
theorem iidPMF_eq_exp_type {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {n : ℕ} (x : Fin n → α)
    (hxQ : AbsCont (typeOf x) Q) :
    iidPMF Q n x = exp (-(n * (entropy (typeOf x) + relEntropyReal (typeOf x) Q))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [iidPMF]
  have hx : ∀ a, symbolCount x a ≠ 0 → Q a ≠ 0 := fun a h hQa => by
    have := hxQ a hQa
    rw [typeOf, div_eq_zero_iff] at this
    rcases this with h1 | h1
    · exact h (by exact_mod_cast h1)
    · exact (Nat.cast_ne_zero.2 hn.ne') h1
  rw [iidPMF_eq_exp_sum hQ hx, ← mul_neg, neg_add', neg_entropy_sub_relEntropyReal hxQ, mul_sum]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [← mul_assoc, mul_typeOf hn]

/-- **(11.15)** If `x` is in the type class of `Q`, then `Qⁿ(x) = e^{-nH(Q)}`. -/
theorem iidPMF_eq_exp_entropy {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {n : ℕ} {x : Fin n → α}
    (hx : typeOf x = Q) : iidPMF Q n x = exp (-(n * entropy Q)) := by
  have h := iidPMF_eq_exp_type hQ x (by rw [hx]; exact fun _ h => h)
  rwa [hx, relEntropyReal, sum_eq_zero fun a _ => ?_, add_zero] at h
  rcases eq_or_ne (Q a) 0 with h0 | h0
  · simp [h0]
  · rw [div_self h0, log_one, mul_zero]

/-! ### The size of a type class -/

omit [Fintype α] in
/-- Two sequences with the same counts are rearrangements of each other. -/
lemma exists_perm_of_symbolCount_eq {n : ℕ} {x y : Fin n → α}
    (h : ∀ a, symbolCount x a = symbolCount y a) : ∃ σ : Equiv.Perm (Fin n), y = x ∘ σ := by
  classical
  have e : ∀ a, {i // y i = a} ≃ {i // x i = a} := fun a =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact (h a).symm)
  exact ⟨Equiv.ofFiberEquiv e, funext fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

omit [Fintype α] in
/-- Rearranging a sequence does not change its type. -/
lemma typeOf_comp_perm {n : ℕ} (x : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    typeOf (x ∘ σ) = typeOf x := by
  classical
  funext a
  simp only [typeOf, symbolCount]
  congr 2
  exact card_bij' (fun i _ => σ i) (fun i _ => σ.symm i) (by simp) (by simp) (by simp) (by simp)

/-- **(11.17)** The size of a type class is a multinomial coefficient:
`|T(Pₓ)| ∏ₐ N(a|x)! = n!`. -/
theorem card_typeClass_mul_prod_factorial {n : ℕ} (x : Fin n → α) :
    (typeClass (typeOf x) n).card * ∏ a, (symbolCount x a).factorial = n.factorial := by
  classical
  -- The rearrangements `x ∘ σ` cover the type class, each `|stab x|` times.
  have hstab : Fintype.card {σ : Equiv.Perm (Fin n) // x ∘ σ = x} =
      ∏ a, (symbolCount x a).factorial := by
    rw [DomMulAct.stabilizer_card x]
    refine prod_congr rfl fun a _ => ?_
    rw [Fintype.card_subtype, symbolCount]
  have hcount : ∀ y : Fin n → α, typeOf y = typeOf x → ∀ a, symbolCount y a = symbolCount x a := by
    intro y hy a
    have h := congrFun hy a
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 := symbolCount_le y a
      have h2 := symbolCount_le x a
      omega
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [typeOf] at h
      exact_mod_cast (div_left_inj' hn').1 h
  have hfib : ∀ y ∈ typeClass (typeOf x) n,
      (univ.filter fun σ : Equiv.Perm (Fin n) => x ∘ σ = y).card =
        Fintype.card {σ : Equiv.Perm (Fin n) // x ∘ σ = x} := by
    intro y hy
    obtain ⟨τ, hτ⟩ := exists_perm_of_symbolCount_eq fun a => (hcount y (mem_typeClass.1 hy) a).symm
    rw [Fintype.card_subtype]
    refine card_nbij' (fun σ => σ * τ⁻¹) (fun σ => σ * τ) (fun σ hσ => ?_) (fun σ hσ => ?_)
      (fun σ _ => by simp) (fun σ _ => by simp)
    · rw [mem_coe, mem_filter] at hσ ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ.2, hτ, Function.comp_assoc,
        ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one, Function.comp_id]
    · rw [mem_coe, mem_filter] at hσ ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ.2, hτ]
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin n))), x ∘ σ ∈ typeClass (typeOf x) n := by
    intro σ _
    rw [mem_typeClass]
    exact typeOf_comp_perm x σ
  have h := card_eq_sum_card_fiberwise hmaps
  rw [card_univ, Fintype.card_perm, Fintype.card_fin, sum_congr rfl hfib, sum_const, smul_eq_mul,
    hstab] at h
  exact h.symm

/-- **Theorem 11.1.3 (upper bound), (11.18)–(11.22).** `|T(P)| ≤ e^{nH(P)}`. -/
theorem card_typeClass_le {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    ((typeClass (typeOf x) n).card : ℝ) ≤ exp (n * entropy (typeOf x)) := by
  have hP := typeOf_isPMF hn x
  have h1 := prob_le_one (iidPMF_isPMF hP n) (typeClass (typeOf x) n)
  have h2 : prob (iidPMF (typeOf x) n) (typeClass (typeOf x) n) =
      (typeClass (typeOf x) n).card * exp (-(n * entropy (typeOf x))) := by
    rw [prob, sum_congr rfl fun y hy => iidPMF_eq_exp_entropy hP.nonneg (mem_typeClass.1 hy),
      sum_const, nsmul_eq_mul]
  rw [h2, ← le_div_iff₀ (exp_pos _), one_div, ← exp_neg, neg_neg] at h1
  exact h1

/-- The bound behind (11.27): `k^{k'} k! ≤ k^k k'!`. -/
lemma pow_mul_factorial_le (k k' : ℕ) : k ^ k' * k.factorial ≤ k ^ k * k'.factorial := by
  rcases le_total k k' with h | h
  · calc k ^ k' * k.factorial = k ^ k * (k.factorial * k ^ (k' - k)) := by
          rw [← Nat.add_sub_cancel' h, pow_add]
          simp only [Nat.add_sub_cancel_left]
          ring
      _ ≤ k ^ k * k'.factorial :=
          Nat.mul_le_mul_left _ (Nat.factorial_mul_pow_sub_le_factorial h)
  · calc k ^ k' * k.factorial = k ^ k' * ((k - (k - k')).factorial * k.descFactorial (k - k')) := by
          rw [Nat.factorial_mul_descFactorial (Nat.sub_le k k')]
      _ ≤ k ^ k' * (k'.factorial * k ^ (k - k')) := by
          rw [Nat.sub_sub_self h]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _))
      _ = k ^ k * k'.factorial := by
          rw [mul_comm k'.factorial, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

/-- **(11.23)–(11.32)** Under `Pⁿ`, the type class `T(P)` is the most likely one:
`Pⁿ(T(P)) ≥ Pⁿ(T(P̂))` for every type `P̂`. -/
theorem prob_typeClass_le_self {n : ℕ} (hn : 0 < n) (x y : Fin n → α) :
    prob (iidPMF (typeOf x) n) (typeClass (typeOf y) n) ≤
      prob (iidPMF (typeOf x) n) (typeClass (typeOf x) n) := by
  classical
  set P := typeOf x
  -- `Pⁿ(T(Pᵧ)) = |T(Pᵧ)| ∏ₐ P(a)^{N(a|y)}`.
  have hprob : ∀ z : Fin n → α, prob (iidPMF P n) (typeClass (typeOf z) n) =
      (typeClass (typeOf z) n).card * ∏ a, P a ^ symbolCount z a := by
    intro z
    rw [prob, sum_congr rfl fun w hw => ?_, sum_const, nsmul_eq_mul]
    rw [iidPMF_eq_prod_pow]
    refine prod_congr rfl fun a _ => ?_
    have h := congrFun (mem_typeClass.1 hw) a
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [typeOf] at h
    rw [show symbolCount w a = symbolCount z a by exact_mod_cast (div_left_inj' hn').1 h]
  have hT : ∀ z : Fin n → α, ((typeClass (typeOf z) n).card : ℝ) =
      n.factorial / ∏ a, ((symbolCount z a).factorial : ℝ) := fun z => by
    rw [eq_div_iff (prod_ne_zero_iff.2 fun a _ => by positivity)]
    exact_mod_cast card_typeClass_mul_prod_factorial z
  rw [hprob, hprob, hT, hT, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff₀ (prod_pos fun a _ => by positivity) (prod_pos fun a _ => by positivity),
    mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- With `P(a) = kₐ/n`, compare `∏ kₐ^{k'ₐ}/k'ₐ!` and `∏ kₐ^{kₐ}/kₐ!`; the powers of `n` cancel.
  set k := fun a => symbolCount x a
  set k' := fun a => symbolCount y a
  have hPk : ∀ a, P a = k a / n := fun a => rfl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ a, (k a : ℝ) = ∑ a, (k' a : ℝ) := by
    rw [sum_symbolCount, sum_symbolCount]
  simp only [hPk, div_pow, prod_div_distrib, prod_pow_eq_pow_sum]
  have hsum' : ∑ a, k a = ∑ a, k' a := by exact_mod_cast hsum
  rw [hsum', div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right (pow_pos hn' _)]
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_le_prod₀ (fun a _ => by positivity) fun a _ => ?_
  exact_mod_cast pow_mul_factorial_le (k a) (k' a)

/-- **Theorem 11.1.3 (lower bound), (11.33)–(11.39).** `|T(P)| ≥ e^{nH(P)}/|𝒫ₙ|`, and hence
`|T(P)| ≥ e^{nH(P)}/(n + 1)^|𝒳|`. -/
theorem exp_div_card_types_le_card_typeClass {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    exp (n * entropy (typeOf x)) / (types α n).card ≤ (typeClass (typeOf x) n).card := by
  classical
  set P := typeOf x
  have hP := typeOf_isPMF hn x
  have hμ := iidPMF_isPMF hP n
  -- `1 = ∑_{types} Pⁿ(T(P̂)) ≤ |𝒫ₙ| Pⁿ(T(P))`.
  have h1 : (1 : ℝ) ≤ (types α n).card * prob (iidPMF P n) (typeClass P n) := by
    have hsplit : (1 : ℝ) = ∑ Q ∈ types α n, prob (iidPMF P n) (typeClass Q n) := by
      rw [← hμ.sum_eq_one, ← sum_fiberwise_of_maps_to (g := typeOf) (t := types α n)
        (fun z _ => typeOf_mem_types z)]
      refine sum_congr rfl fun Q _ => ?_
      rw [prob, typeClass]
    rw [hsplit, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun Q hQ => ?_
    obtain ⟨y, rfl⟩ := mem_types.1 hQ
    exact prob_typeClass_le_self hn x y
  have h2 : prob (iidPMF P n) (typeClass P n) =
      (typeClass P n).card * exp (-(n * entropy P)) := by
    rw [prob, sum_congr rfl fun y hy => iidPMF_eq_exp_entropy hP.nonneg (mem_typeClass.1 hy),
      sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) < (types α n).card := by
    exact_mod_cast card_pos.2 ⟨_, typeOf_mem_types x⟩
  rw [h2, exp_neg] at h1
  rw [div_le_iff₀ hcard]
  have := mul_le_mul_of_nonneg_left h1 (exp_pos (n * entropy P)).le
  rw [mul_one] at this
  calc exp (n * entropy P) ≤ exp (n * entropy P) *
        ((types α n).card * ((typeClass P n).card * (exp (n * entropy P))⁻¹)) := this
    _ = (typeClass P n).card * (types α n).card := by
        field_simp

/-- **Theorem 11.1.3 (lower bound).** `|T(P)| ≥ e^{nH(P)}/(n + 1)^|𝒳|`. -/
theorem exp_div_le_card_typeClass {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    exp (n * entropy (typeOf x)) / (n + 1) ^ Fintype.card α ≤ (typeClass (typeOf x) n).card := by
  refine le_trans ?_ (exp_div_card_types_le_card_typeClass hn x)
  have hcard : (0 : ℝ) < (types α n).card := by
    exact_mod_cast card_pos.2 ⟨_, typeOf_mem_types x⟩
  exact div_le_div_of_nonneg_left (exp_pos _).le hcard (card_types_le n)

/-! ### The probability of a type class -/

/-- `Qⁿ(T(P)) = |T(P)| e^{-n(H(P) + D(P‖Q))}` (11.55)–(11.57). -/
lemma prob_typeClass_eq {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {n : ℕ} (x : Fin n → α)
    (hxQ : AbsCont (typeOf x) Q) :
    prob (iidPMF Q n) (typeClass (typeOf x) n) = (typeClass (typeOf x) n).card *
      exp (-(n * (entropy (typeOf x) + relEntropyReal (typeOf x) Q))) := by
  rw [prob, sum_congr rfl fun y hy => ?_, sum_const, nsmul_eq_mul]
  rw [mem_typeClass] at hy
  rw [iidPMF_eq_exp_type hQ y (hy ▸ hxQ), hy]

/-- **Theorem 11.1.4 (upper bound).** `Qⁿ(T(P)) ≤ e^{-nD(P‖Q)}` for `P ≪ Q`. -/
theorem prob_typeClass_le {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {n : ℕ} (hn : 0 < n) (x : Fin n → α)
    (hxQ : AbsCont (typeOf x) Q) :
    prob (iidPMF Q n) (typeClass (typeOf x) n) ≤ exp (-(n * relEntropyReal (typeOf x) Q)) := by
  rw [prob_typeClass_eq hQ x hxQ, mul_add, neg_add, exp_add, ← mul_assoc]
  refine mul_le_of_le_one_left (exp_pos _).le ?_
  calc ((typeClass (typeOf x) n).card : ℝ) * exp (-(n * entropy (typeOf x)))
      ≤ exp (n * entropy (typeOf x)) * exp (-(n * entropy (typeOf x))) :=
        mul_le_mul_of_nonneg_right (card_typeClass_le hn x) (exp_pos _).le
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

/-- **Theorem 11.1.4 (lower bound).** `Qⁿ(T(P)) ≥ e^{-nD(P‖Q)}/(n + 1)^|𝒳|` for `P ≪ Q`. -/
theorem exp_div_le_prob_typeClass {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {n : ℕ} (hn : 0 < n)
    (x : Fin n → α) (hxQ : AbsCont (typeOf x) Q) :
    exp (-(n * relEntropyReal (typeOf x) Q)) / (n + 1) ^ Fintype.card α ≤
      prob (iidPMF Q n) (typeClass (typeOf x) n) := by
  rw [prob_typeClass_eq hQ x hxQ, mul_add, neg_add, exp_add]
  have h := exp_div_le_card_typeClass hn x
  calc exp (-(n * relEntropyReal (typeOf x) Q)) / (n + 1) ^ Fintype.card α
      = exp (n * entropy (typeOf x)) / (n + 1) ^ Fintype.card α *
          (exp (-(n * entropy (typeOf x))) * exp (-(n * relEntropyReal (typeOf x) Q))) := by
        rw [div_mul_eq_mul_div, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-! ### Approximating a distribution by types -/

/-- For every `k : 𝒳 → ℕ` with `∑ₐ kₐ = n` there is a sequence with `N(a|x) = kₐ`. -/
lemma exists_symbolCount_eq {n : ℕ} (k : α → ℕ) (hk : ∑ a, k a = n) :
    ∃ x : Fin n → α, ∀ a, symbolCount x a = k a := by
  classical
  have hcard : Fintype.card (Σ a, Fin (k a)) = n := by simp [hk]
  set e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i).1, fun a => ?_⟩
  rw [symbolCount]
  have : (univ.filter fun i => (e i).1 = a).card =
      (univ.filter fun s : Σ a, Fin (k a) => s.1 = a).card :=
    card_bij' (fun i _ => e i) (fun s _ => e.symm s) (by simp) (by simp) (by simp) (by simp)
  rw [this]
  have h2 : (univ.filter fun s : Σ a, Fin (k a) => s.1 = a) =
      (univ : Finset (Fin (k a))).map ⟨fun j => ⟨a, j⟩, fun j j' h => by simpa using h⟩ := by
    ext ⟨b, j⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro rfl
      exact ⟨j, rfl⟩
    · rintro ⟨j', h⟩
      exact (Sigma.mk.inj_iff.1 h).1.symm
  rw [h2, card_map, card_univ, Fintype.card_fin]

/-- Every pmf `P` is within `|𝒳|/n` of a type with denominator `n`, which vanishes wherever `P`
does. -/
theorem exists_typeOf_near {P : α → ℝ} (hP : IsPMF P) {n : ℕ} (hn : 0 < n) :
    ∃ x : Fin n → α, (∀ a, |typeOf x a - P a| ≤ Fintype.card α / n) ∧ AbsCont (typeOf x) P := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < P a := by
    by_contra h
    push Not at h
    have : ∑ a, P a ≤ 0 := sum_nonpos fun a _ => h a
    linarith [hP.sum_eq_one]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : α → ℕ := fun a => ⌊n * P a⌋₊
  have hf : ∀ a, (f a : ℝ) ≤ n * P a := fun a =>
    Nat.floor_le (mul_nonneg hn'.le (hP.nonneg a))
  have hf' : ∀ a, n * P a - 1 < f a := fun a => Nat.sub_one_lt_floor _
  set s := ∑ a ∈ univ.erase a₀, f a
  have hs : (s : ℝ) ≤ n * (1 - P a₀) := by
    have h1 : (s : ℝ) ≤ ∑ a ∈ univ.erase a₀, n * P a := by
      push_cast [s]
      exact sum_le_sum fun a _ => hf a
    have h2 : ∑ a ∈ univ.erase a₀, P a = 1 - P a₀ := by
      rw [← hP.sum_eq_one, ← add_sum_erase _ _ (mem_univ a₀)]
      ring
    rw [← mul_sum, h2] at h1
    exact h1
  have hsn : s ≤ n := by
    have : (s : ℝ) ≤ n := hs.trans (by nlinarith [hP.le_one a₀])
    exact_mod_cast this
  set k : α → ℕ := fun a => if a = a₀ then n - s else f a
  have hk : ∑ a, k a = n := by
    rw [← add_sum_erase _ _ (mem_univ a₀)]
    have h1 : k a₀ = n - s := by simp [k]
    have h2 : ∑ a ∈ univ.erase a₀, k a = s :=
      sum_congr rfl fun a ha => by simp [k, ne_of_mem_erase ha]
    rw [h1, h2]
    exact Nat.sub_add_cancel hsn
  obtain ⟨x, hx⟩ := exists_symbolCount_eq k hk
  have hcard : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.2 ⟨a₀⟩
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [typeOf, hx, le_div_iff₀ hn', ← abs_of_pos hn', ← abs_mul, abs_of_pos hn', sub_mul,
      div_mul_cancel₀ _ hn'.ne', mul_comm (P a)]
    by_cases ha : a = a₀
    · subst ha
      simp only [k, ↓reduceIte]
      rw [Nat.cast_sub hsn]
      -- `n - s ≥ nP(a₀)` and `n - s ≤ nP(a₀) + |𝒳| - 1`.
      have hs2 : (n : ℝ) * (1 - P a) - (Fintype.card α - 1) ≤ s := by
        have h1 : ∑ b ∈ univ.erase a, (n * P b - 1) ≤ (s : ℝ) := by
          push_cast [s]
          exact sum_le_sum fun b _ => (hf' b).le
        rw [sum_sub_distrib, ← mul_sum, sum_const, card_erase_of_mem (mem_univ a), card_univ,
          nsmul_eq_mul, mul_one] at h1
        have h2 : ∑ b ∈ univ.erase a, P b = 1 - P a := by
          rw [← hP.sum_eq_one, ← add_sum_erase _ _ (mem_univ a)]
          ring
        rw [h2, Nat.cast_sub (Fintype.card_pos_iff.2 ⟨a⟩), Nat.cast_one] at h1
        linarith
      rw [abs_le]
      constructor <;> nlinarith
    · simp only [k, ha, ↓reduceIte]
      rw [abs_le]
      constructor <;> nlinarith [hf a, hf' a]
  · -- `P(a) = 0` forces `kₐ = 0`.
    have hne : a ≠ a₀ := fun h => by rw [h] at ha; linarith
    rw [typeOf, hx]
    simp only [k, hne, ↓reduceIte, f, ha, mul_zero, Nat.floor_zero, Nat.cast_zero, zero_div]

end InfoTheory
