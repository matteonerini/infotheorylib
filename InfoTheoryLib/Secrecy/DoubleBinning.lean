/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyAgreement
public import InfoTheoryLib.Network.MultiWay

/-!
# Secret keys from decodable bins

Two tools for the proofs of achievability of the secret key capacities of Lecture 23 of El Gamal and
Kim. The first one is a pair of entropy inequalities: if a public index `M` and a key `K` are
functions of `T`, and if `T` can be recovered from `(M, K, O)`, then the key is nearly uniform and
nearly independent of `(M, O)` as soon as `log M + log K` is close to `H(T | O)`. The second one is
the random binning of a sequence with a public index and a key.

## Main statements

* `entropy_key_ge_of_decodable`, `mutualInfo_key_le_of_decodable`: the two inequalities.
* `key_transfer`: the same bounds for the key of the other node, from Fano's inequality.
* `exists_doubleBin`: **double binning**: a public index and a key, and the two decoders.

## Implementation notes

The notes analyze double binning on pages 23-32 to 23-36 and in Lemmas 2 and 3, with Chebyshev's
inequality on the number of sequences in a bin. With the rates above, a decoder that knows the key
and sees what the eavesdropper sees recovers the sequence, by the packing argument of Slepian–Wolf
coding. The entropy inequalities then give what Lemmas 2 and 3 give.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The entropy inequalities -/

section Decodable

variable {Ω τ o m k : Type*} [Fintype Ω] [Fintype τ] [Fintype o] [Fintype m] [Fintype k]
  {μ : Ω → ℝ}

/-- `H(M, K, O) ≥ H(T, O) - H(T | M, K, O)`, for functions `M` and `K` of `T`. -/
lemma entropy_triple_ge (hμ : IsPMF μ) (T : Ω → τ) (O : Ω → o) (f : τ → m) (g : τ → k) :
    H[pair T O ; μ] - H[T | pair (pair (f ∘ T) (g ∘ T)) O ; μ] ≤
      H[pair (pair (f ∘ T) (g ∘ T)) O ; μ] := by
  set D := pair (pair (f ∘ T) (g ∘ T)) O with hD
  have h₁ := chain_rule hμ D T
  have h₂ : H[pair D T ; μ] = H[pair T O ; μ] := by
    refine entropyRV_eq_of_injective _ (fun w => (((f w.1, g w.1), w.2), w.1))
      (fun a b h => ?_) fun _ => rfl
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1.2
  linarith

/-- **Lemma 2 of page 23-34 of [elgamal2010], by decoding.** For functions `M` and `K` of `T`,
`H(K) ≥ H(T | O) - H(M) - H(T | M, K, O)`. -/
theorem entropy_key_ge_of_decodable (hμ : IsPMF μ) (T : Ω → τ) (O : Ω → o) (f : τ → m) (g : τ → k) :
    H[T | O ; μ] - H[f ∘ T ; μ] - H[T | pair (pair (f ∘ T) (g ∘ T)) O ; μ] ≤ H[g ∘ T ; μ] := by
  have h₁ := entropy_triple_ge hμ T O f g
  have h₂ := chain_rule hμ O T
  have h₃ : H[pair O T ; μ] = H[pair T O ; μ] := entropyRV_pair_comm μ O T
  have h₄ := chain_rule hμ (pair (f ∘ T) (g ∘ T)) O
  have h₅ := condEntropy_le_entropy hμ O (pair (f ∘ T) (g ∘ T))
  have h₆ := chain_rule hμ (f ∘ T) (g ∘ T)
  have h₇ := condEntropy_le_entropy hμ (g ∘ T) (f ∘ T)
  linarith

/-- **Lemma 3 of page 23-36 of [elgamal2010], by decoding.** For functions `M` and `K` of `T`,
`I(K; O, M) ≤ H(K) + H(M) - H(T | O) + H(T | M, K, O)`. -/
theorem mutualInfo_key_le_of_decodable (hμ : IsPMF μ) (T : Ω → τ) (O : Ω → o) (f : τ → m)
    (g : τ → k) :
    I[g ∘ T : pair O (f ∘ T) ; μ] ≤ H[g ∘ T ; μ] + H[f ∘ T ; μ] - H[T | O ; μ] +
      H[T | pair (pair (f ∘ T) (g ∘ T)) O ; μ] := by
  have h₁ := entropy_triple_ge hμ T O f g
  have h₂ := chain_rule hμ O T
  have h₃ : H[pair O T ; μ] = H[pair T O ; μ] := entropyRV_pair_comm μ O T
  have h₄ := mutualInfo_eq_add_sub hμ (g ∘ T) (pair O (f ∘ T))
  have h₅ : H[pair (g ∘ T) (pair O (f ∘ T)) ; μ] = H[pair (pair (f ∘ T) (g ∘ T)) O ; μ] := by
    refine entropyRV_eq_of_injective _ (fun w => (w.1.2, w.2, w.1.1))
      (fun a b h => ?_) fun _ => rfl
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.2.2 h.1) h.2.1
  have h₆ := chain_rule hμ O (f ∘ T)
  have h₇ := condEntropy_le_entropy hμ (f ∘ T) O
  linarith

/-- **Page 23-34 of [elgamal2010].** The key of the other node has the same bounds, up to
`H(K₂ | K₁)` and `H(K₁ | K₂)`. -/
theorem key_transfer (hμ : IsPMF μ) (K₁ K₂ : Ω → k) (V : Ω → o) :
    I[K₂ : V ; μ] ≤ I[K₁ : V ; μ] + H[K₂ | K₁ ; μ] ∧ H[K₁ ; μ] - H[K₁ | K₂ ; μ] ≤ H[K₂ ; μ] := by
  constructor
  · have h₁ := mutualInfo_eq_entropy_sub_condEntropy' hμ K₂ V
    have h₂ := mutualInfo_eq_entropy_sub_condEntropy' hμ K₁ V
    have h₃ : H[V | pair K₁ K₂ ; μ] ≤ H[V | K₂ ; μ] := by
      have e := condEntropy_le_condEntropy hμ V K₁ K₂
      exact e
    have h₄ := chain_rule_cond hμ K₂ V K₁
    have h₅ := chain_rule_cond hμ V K₂ K₁
    have h₆ : H[pair K₂ V | K₁ ; μ] = H[pair V K₂ | K₁ ; μ] :=
      condEntropy_congr_left hμ _ Prod.swap Prod.swap_injective fun _ => rfl
    have h₇ := condEntropy_nonneg hμ K₂ (pair V K₁)
    have h₈ := condEntropy_nonneg hμ V (pair K₂ K₁)
    have h₉ : H[V | pair K₂ K₁ ; μ] = H[V | pair K₁ K₂ ; μ] :=
      condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
    linarith
  · have h₁ := entropy_sub_condEntropy_symm hμ K₁ K₂
    have h₂ := condEntropy_nonneg hμ K₂ K₁
    linarith

end Decodable

/-! ### A random hash -/

section Hash

variable {N Mb Kb : ℕ} [NeZero Mb] [NeZero Kb]

/-- The law of a random hash with values in `[1 : M] × [1 : K]`. -/
def hashLaw (N Mb Kb : ℕ) : (Fin N → Fin Mb × Fin Kb) → ℝ :=
  iidPMF (uniformPMF (Fin Mb × Fin Kb)) N

lemma hashLaw_isPMF : IsPMF (hashLaw N Mb Kb) := by
  have : Nonempty (Fin Mb × Fin Kb) := ⟨(0, 0)⟩
  exact iidPMF_isPMF uniformPMF_isPMF N

/-- The probability that two arguments have the same public index is `1 / M`. -/
lemma sum_hashLaw_fst {w w' : Fin N} (h : w ≠ w') :
    ∑ C, hashLaw N Mb Kb C * (if (C w).1 = (C w').1 then 1 else 0) = 1 / Mb := by
  classical
  have : Nonempty (Fin Mb × Fin Kb) := ⟨(0, 0)⟩
  have hM : (Mb : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Mb
  have hK : (Kb : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Kb
  have h₁ := sum_iidPMF_eval₂ (uniformPMF_isPMF (α := Fin Mb × Fin Kb)) h
    fun x y => if x.1 = y.1 then (1 : ℝ) else 0
  refine h₁.trans ?_
  have hu : ∀ x : Fin Mb × Fin Kb, uniformPMF (Fin Mb × Fin Kb) x = 1 / (Mb * Kb) := fun x => by
    simp [uniformPMF]
  have inner : ∀ x : Fin Mb × Fin Kb, ∑ x' : Fin Mb × Fin Kb,
      uniformPMF (Fin Mb × Fin Kb) x * uniformPMF (Fin Mb × Fin Kb) x' *
        (if x.1 = x'.1 then (1 : ℝ) else 0) = 1 / (Mb * Kb) * (1 / Mb) := fun x => by
    rw [Fintype.sum_prod_type, sum_eq_single x.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [hu, ite_true, mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp only [inner, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- The probability that two arguments have the same public index and key is `1 / (M K)`. -/
lemma sum_hashLaw_eq {w w' : Fin N} (h : w ≠ w') :
    ∑ C, hashLaw N Mb Kb C * (if C w = C w' then 1 else 0) = 1 / (Mb * Kb) := by
  classical
  have : Nonempty (Fin Mb × Fin Kb) := ⟨(0, 0)⟩
  have hM : (Mb : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Mb
  have hK : (Kb : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Kb
  have h₁ := sum_iidPMF_eval₂ (uniformPMF_isPMF (α := Fin Mb × Fin Kb)) h
    fun x y => if x = y then (1 : ℝ) else 0
  refine h₁.trans ?_
  have hu : ∀ x : Fin Mb × Fin Kb, uniformPMF (Fin Mb × Fin Kb) x = 1 / (Mb * Kb) := fun x => by
    simp [uniformPMF]
  have inner : ∀ x : Fin Mb × Fin Kb, ∑ x' : Fin Mb × Fin Kb,
      uniformPMF (Fin Mb × Fin Kb) x * uniformPMF (Fin Mb × Fin Kb) x' *
        (if x = x' then (1 : ℝ) else 0) = 1 / (Mb * Kb) * (1 / (Mb * Kb)) := fun x => by
    rw [sum_eq_single x (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [hu]
  simp only [inner, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

end Hash

/-! ### Decoding a unique candidate -/

section Unique

variable {X : Type*}

open Classical in
/-- The element of `S` if `S` has a single element, and `d` if not. -/
def uniqueOr (S : Finset X) (d : X) : X :=
  if h : ∃ x, S = {x} then h.choose else d

/-- If `x ∈ S` and every element of `S` is `x`, the decoder finds `x`. -/
lemma uniqueOr_eq {S : Finset X} (d : X) {x : X} (hx : x ∈ S) (h : ∀ y ∈ S, y = x) :
    uniqueOr S d = x := by
  classical
  have hS : S = {x} := by
    ext y
    simp only [mem_singleton]
    exact ⟨h y, fun e => e ▸ hx⟩
  have hex : ∃ x, S = {x} := ⟨x, hS⟩
  simp only [uniqueOr]
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have h₂ : ({hex.choose} : Finset X) = {x} := hex.choose_spec.symm.trans hS
  exact singleton_injective h₂

end Unique

/-! ### Double binning -/

section Double

variable {ξ ν β ε' : Type*} [Fintype ξ] [Fintype ν] [Fintype β] [Fintype ε'] {P₀ : ξ → ℝ}

/-- The probability that a letterwise function of an i.i.d. sequence is not in a set. -/
lemma sum_iidPMF_not_mem {τ : Type*} [Finite τ] (hP : IsPMF P₀) (f : ξ → τ) (n : ℕ)
    (T : Finset (Fin n → τ)) [DecidablePred fun ω : Fin n → ξ => (fun i => f (ω i)) ∉ T] :
    ∑ ω : Fin n → ξ, iidPMF P₀ n ω * (if (fun i => f (ω i)) ∉ T then 1 else 0) =
      1 - prob (iidPMF (dist P₀ f) n) T := by
  have := Fintype.ofFinite τ
  classical
  have h₁ := (iidPMF_isPMF hP n).sum_eq_one
  have h₂ : prob (iidPMF (dist P₀ f) n) T =
      ∑ ω : Fin n → ξ, iidPMF P₀ n ω * (if (fun i => f (ω i)) ∈ T then 1 else 0) := by
    rw [← dist_iidPMF_comp, prob,
      ← sum_dist_mul (iidPMF P₀ n) (fun ω i => f (ω i)) fun a => if a ∈ T then (1 : ℝ) else 0]
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, univ_inter]
  have h₃ : ∀ ω : Fin n → ξ, iidPMF P₀ n ω * (if (fun i => f (ω i)) ∉ T then 1 else 0) =
      iidPMF P₀ n ω - iidPMF P₀ n ω * (if (fun i => f (ω i)) ∈ T then 1 else 0) := fun ω => by
    by_cases h : (fun i => f (ω i)) ∈ T <;> simp [h]
  rw [h₂, sum_congr rfl fun ω _ => h₃ ω, sum_sub_distrib, h₁]

variable {Mb Kb n : ℕ} [NeZero Mb] [NeZero Kb]

open Classical in
/-- The decoder from `(yⁿ, m)` for a hash `C`. -/
def binDec₁ (T : Finset (Fin n → β × ν)) (C : Fin (Fintype.card (Fin n → ν)) → Fin Mb × Fin Kb)
    (d : Fin n → ν) (y : Fin n → β) (m : Fin Mb) : Fin n → ν :=
  uniqueOr (univ.filter fun s => zipSeq y s ∈ T ∧ (C (Fintype.equivFin _ s)).1 = m) d

open Classical in
/-- The decoder from `(eⁿ, m, k)` for a hash `C`. -/
def binDec₂ (T : Finset (Fin n → ε' × ν)) (C : Fin (Fintype.card (Fin n → ν)) → Fin Mb × Fin Kb)
    (d : Fin n → ν) (y : Fin n → ε') (m : Fin Mb) (k : Fin Kb) : Fin n → ν :=
  uniqueOr (univ.filter fun s => zipSeq y s ∈ T ∧ C (Fintype.equivFin _ s) = (m, k)) d

omit [Fintype β] [NeZero Mb] [NeZero Kb] in
open Classical in
/-- A decoding error needs an atypical pair or a rival with the same public index. -/
lemma binDec₁_ne_le (T : Finset (Fin n → β × ν))
    (C : Fin (Fintype.card (Fin n → ν)) → Fin Mb × Fin Kb) (d s : Fin n → ν) (y : Fin n → β) :
    (if binDec₁ T C d y (C (Fintype.equivFin _ s)).1 ≠ s then (1 : ℝ) else 0) ≤
      (if zipSeq y s ∉ T then 1 else 0) +
        ∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
          if (C (Fintype.equivFin _ s')).1 = (C (Fintype.equivFin _ s)).1 then 1 else 0 := by
  have hn0 : (0 : ℝ) ≤ ∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
      if (C (Fintype.equivFin _ s')).1 = (C (Fintype.equivFin _ s)).1 then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hs : zipSeq y s ∈ T
  · by_cases hu : ∀ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
        (C (Fintype.equivFin _ s')).1 ≠ (C (Fintype.equivFin _ s)).1
    · have hd : binDec₁ T C d y (C (Fintype.equivFin _ s)).1 = s := by
        refine uniqueOr_eq d (mem_filter.2 ⟨mem_univ _, hs, rfl⟩) fun s' hs' => ?_
        by_contra hne
        obtain ⟨-, h₁, h₂⟩ := mem_filter.1 hs'
        exact hu s' (mem_erase.2 ⟨hne, mem_filter.2 ⟨mem_univ _, h₁⟩⟩) h₂
      simp only [hd, ne_eq, not_true_eq_false, ite_false, hs, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨s', hs', hb⟩ := hu
      have h₁ : (1 : ℝ) ≤ ∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
          if (C (Fintype.equivFin _ s')).1 = (C (Fintype.equivFin _ s)).1 then (1 : ℝ) else 0 := by
        have := single_le_sum (f := fun s' => if (C (Fintype.equivFin _ s')).1 =
          (C (Fintype.equivFin _ s)).1 then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) hs'
        simpa [hb] using this
      split_ifs <;> linarith
  · simp only [hs, not_false_eq_true, ite_true]
    split_ifs <;> linarith

omit [Fintype ε'] [NeZero Mb] [NeZero Kb] in
open Classical in
/-- A decoding error needs an atypical pair or a rival with the same public index and key. -/
lemma binDec₂_ne_le (T : Finset (Fin n → ε' × ν))
    (C : Fin (Fintype.card (Fin n → ν)) → Fin Mb × Fin Kb) (d s : Fin n → ν) (y : Fin n → ε') :
    (if binDec₂ T C d y (C (Fintype.equivFin _ s)).1 (C (Fintype.equivFin _ s)).2 ≠ s then (1 : ℝ)
      else 0) ≤ (if zipSeq y s ∉ T then 1 else 0) +
        ∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
          if C (Fintype.equivFin _ s') = C (Fintype.equivFin _ s) then 1 else 0 := by
  have hn0 : (0 : ℝ) ≤ ∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
      if C (Fintype.equivFin _ s') = C (Fintype.equivFin _ s) then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hs : zipSeq y s ∈ T
  · by_cases hu : ∀ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
        C (Fintype.equivFin _ s') ≠ C (Fintype.equivFin _ s)
    · have hd : binDec₂ T C d y (C (Fintype.equivFin _ s)).1 (C (Fintype.equivFin _ s)).2 = s := by
        refine uniqueOr_eq d (mem_filter.2 ⟨mem_univ _, hs, rfl⟩) fun s' hs' => ?_
        by_contra hne
        obtain ⟨-, h₁, h₂⟩ := mem_filter.1 hs'
        exact hu s' (mem_erase.2 ⟨hne, mem_filter.2 ⟨mem_univ _, h₁⟩⟩) h₂
      simp only [hd, ne_eq, not_true_eq_false, ite_false, hs, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨s', hs', hb⟩ := hu
      have h₁ : (1 : ℝ) ≤ ∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
          if C (Fintype.equivFin _ s') = C (Fintype.equivFin _ s) then (1 : ℝ) else 0 := by
        have := single_le_sum (f := fun s' => if C (Fintype.equivFin _ s') =
          C (Fintype.equivFin _ s) then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) hs'
        simpa [hb] using this
      split_ifs <;> linarith
  · simp only [hs, not_false_eq_true, ite_true]
    split_ifs <;> linarith

/-- The law of `(Y, V)`. -/
abbrev binJoint (P₀ : ξ → ℝ) (y : ξ → β) (v : ξ → ν) : β × ν → ℝ := dist P₀ (pair y v)

omit [Fintype β] in
open Classical in
/-- The rivals with the same public index, on average over the hash. -/
lemma sum_hash_rival_fst (T : Finset (Fin n → β × ν)) {B : ℝ}
    (hB : ∀ y : Fin n → β, ((univ.filter fun s' => zipSeq y s' ∈ T).card : ℝ) ≤ B)
    (y : Fin n → β) (s : Fin n → ν) :
    ∑ C, hashLaw _ Mb Kb C * (∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
      if (C (Fintype.equivFin _ s')).1 = (C (Fintype.equivFin _ s)).1 then (1 : ℝ) else 0) ≤
      B * (1 / Mb) := by
  simp only [mul_sum]
  rw [sum_comm]
  have hone : ∀ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
      ∑ C, hashLaw _ Mb Kb C * (if (C (Fintype.equivFin _ s')).1 =
        (C (Fintype.equivFin _ s)).1 then (1 : ℝ) else 0) = 1 / Mb := fun s' hs' =>
    sum_hashLaw_fst fun h => (mem_erase.1 hs').1 ((Fintype.equivFin _).injective h)
  rw [sum_congr rfl hone, sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine le_trans ?_ (hB y)
  exact_mod_cast card_le_card (erase_subset _ _)

omit [Fintype β] in
open Classical in
/-- The rivals with the same public index and key, on average over the hash. -/
lemma sum_hash_rival_eq (T : Finset (Fin n → β × ν)) {B : ℝ}
    (hB : ∀ y : Fin n → β, ((univ.filter fun s' => zipSeq y s' ∈ T).card : ℝ) ≤ B)
    (y : Fin n → β) (s : Fin n → ν) :
    ∑ C, hashLaw _ Mb Kb C * (∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
      if C (Fintype.equivFin _ s') = C (Fintype.equivFin _ s) then (1 : ℝ) else 0) ≤
      B * (1 / (Mb * Kb)) := by
  simp only [mul_sum]
  rw [sum_comm]
  have hone : ∀ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T).erase s),
      ∑ C, hashLaw _ Mb Kb C * (if C (Fintype.equivFin _ s') =
        C (Fintype.equivFin _ s) then (1 : ℝ) else 0) = 1 / (Mb * Kb) := fun s' hs' =>
    sum_hashLaw_eq fun h => (mem_erase.1 hs').1 ((Fintype.equivFin _).injective h)
  rw [sum_congr rfl hone, sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine le_trans ?_ (hB y)
  exact_mod_cast card_le_card (erase_subset _ _)

omit [Fintype β] [Fintype ε'] in
open Classical in
/-- The two decoders, on average over the hash, for one sequence. -/
lemma sum_hash_err_le [Finite β] [Finite ε'] (T₁ : Finset (Fin n → β × ν))
  (T₂ : Finset (Fin n → ε' × ν)) {B₁ B₂ : ℝ}
    (h₁ : ∀ y : Fin n → β, ((univ.filter fun s' => zipSeq y s' ∈ T₁).card : ℝ) ≤ B₁)
    (h₂ : ∀ y : Fin n → ε', ((univ.filter fun s' => zipSeq y s' ∈ T₂).card : ℝ) ≤ B₂)
    (d s : Fin n → ν) (y : Fin n → β) (e : Fin n → ε') :
    ∑ C, hashLaw _ Mb Kb C * ((if binDec₁ T₁ C d y (C (Fintype.equivFin _ s)).1 ≠ s then 1 else 0) +
        (if binDec₂ T₂ C d e (C (Fintype.equivFin _ s)).1 (C (Fintype.equivFin _ s)).2 ≠ s
          then 1 else 0)) ≤
      (if zipSeq y s ∉ T₁ then 1 else 0) + (if zipSeq e s ∉ T₂ then 1 else 0) +
        B₁ * (1 / Mb) + B₂ * (1 / (Mb * Kb)) := by
  have := Fintype.ofFinite β
  have := Fintype.ofFinite ε'
  have hlaw := hashLaw_isPMF (N := Fintype.card (Fin n → ν)) (Mb := Mb) (Kb := Kb)
  set R₁ : (Fin (Fintype.card (Fin n → ν)) → Fin Mb × Fin Kb) → ℝ := fun C =>
    ∑ s' ∈ ((univ.filter fun s' => zipSeq y s' ∈ T₁).erase s),
      if (C (Fintype.equivFin _ s')).1 = (C (Fintype.equivFin _ s)).1 then 1 else 0 with hR₁
  set R₂ : (Fin (Fintype.card (Fin n → ν)) → Fin Mb × Fin Kb) → ℝ := fun C =>
    ∑ s' ∈ ((univ.filter fun s' => zipSeq e s' ∈ T₂).erase s),
      if C (Fintype.equivFin _ s') = C (Fintype.equivFin _ s) then 1 else 0 with hR₂
  set a : ℝ := if zipSeq y s ∉ T₁ then 1 else 0
  set b : ℝ := if zipSeq e s ∉ T₂ then 1 else 0
  have hpt : ∀ C, ((if binDec₁ T₁ C d y (C (Fintype.equivFin _ s)).1 ≠ s then (1 : ℝ) else 0) +
      (if binDec₂ T₂ C d e (C (Fintype.equivFin _ s)).1 (C (Fintype.equivFin _ s)).2 ≠ s
        then 1 else 0)) ≤ (a + R₁ C) + (b + R₂ C) := fun C =>
    add_le_add (binDec₁_ne_le T₁ C d s y) (binDec₂_ne_le T₂ C d s e)
  have hs : ∑ C, hashLaw _ Mb Kb C * ((a + R₁ C) + (b + R₂ C)) =
      a + b + ∑ C, hashLaw _ Mb Kb C * R₁ C + ∑ C, hashLaw _ Mb Kb C * R₂ C := by
    have e₁ : ∀ C, hashLaw _ Mb Kb C * ((a + R₁ C) + (b + R₂ C)) =
        hashLaw _ Mb Kb C * a + hashLaw _ Mb Kb C * b + hashLaw _ Mb Kb C * R₁ C +
          hashLaw _ Mb Kb C * R₂ C := fun C => by ring
    simp only [e₁, sum_add_distrib, ← sum_mul, hlaw.sum_eq_one, one_mul]
  refine (sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hpt C) (hlaw.nonneg C)).trans ?_
  rw [hs]
  exact add_le_add (add_le_add le_rfl (sum_hash_rival_fst T₁ h₁ y s)) (sum_hash_rival_eq T₂ h₂ e s)

/-- Choose a point from a bound for each sequence. -/
lemma exists_of_pointwise_avg {𝒞 Ω : Type*} [Fintype 𝒞] [Fintype Ω] {ν₀ : 𝒞 → ℝ} (hν : IsPMF ν₀)
    {μ : Ω → ℝ} (hμ : IsPMF μ) {F : 𝒞 → Ω → ℝ} {G : Ω → ℝ}
    (h : ∀ ω, ∑ C, ν₀ C * F C ω ≤ G ω) : ∃ C, ∑ ω, μ ω * F C ω ≤ ∑ ω, μ ω * G ω := by
  refine exists_le_of_sum_mul_le hν ?_
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_le_sum fun ω _ => ?_
  have := mul_le_mul_of_nonneg_left (h ω) (hμ.nonneg ω)
  rw [mul_sum] at this
  refine le_trans (le_of_eq (sum_congr rfl fun C _ => ?_)) this
  ring

open Classical in
/-- **Pages 23-32 to 23-36 of [elgamal2010]: double binning.** There are a public index and a key,
functions of `Vⁿ`, and a decoder from `(Yⁿ, M)` and a decoder from `(Eⁿ, M, K)`, such that the sum
of the probabilities of error is at most
`P{(Yⁿ, Vⁿ) ∉ T} + P{(Eⁿ, Vⁿ) ∉ T'} + e^{n(H(V | Y) + δ)} / M + e^{n(H(V | E) + δ')} / (M K)`. -/
theorem exists_doubleBin (hP : IsPMF P₀) (v : ξ → ν) (y : ξ → β) (e : ξ → ε') (t : ℝ) :
    ∃ (b₁ : (Fin n → ν) → Fin Mb) (b₂ : (Fin n → ν) → Fin Kb)
      (d₁ : (Fin n → β) → Fin Mb → Fin n → ν) (d₂ : (Fin n → ε') → Fin Mb → Fin Kb → Fin n → ν),
      ∑ ω : Fin n → ξ, iidPMF P₀ n ω *
        ((if d₁ (fun i => y (ω i)) (b₁ fun i => v (ω i)) ≠ (fun i => v (ω i)) then 1 else 0) +
          (if d₂ (fun i => e (ω i)) (b₁ fun i => v (ω i)) (b₂ fun i => v (ω i)) ≠
            (fun i => v (ω i)) then 1 else 0)) ≤
        (1 - prob (iidPMF (binJoint P₀ y v) n) (robustTypicalSet (binJoint P₀ y v) n t)) +
        (1 - prob (iidPMF (binJoint P₀ e v) n) (robustTypicalSet (binJoint P₀ e v) n t)) +
        exp (n * (H[Prod.snd | Prod.fst ; binJoint P₀ y v] +
          t * H[Prod.snd | Prod.fst ; binJoint P₀ y v])) * (1 / Mb) +
        exp (n * (H[Prod.snd | Prod.fst ; binJoint P₀ e v] +
          t * H[Prod.snd | Prod.fst ; binJoint P₀ e v])) * (1 / (Mb * Kb)) := by
  have hq₁ : IsPMF (binJoint P₀ y v) := hP.dist _
  have hq₂ : IsPMF (binJoint P₀ e v) := hP.dist _
  obtain ⟨z₀⟩ : Nonempty ξ := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  set d : Fin n → ν := fun _ => v z₀
  set T₁ := robustTypicalSet (binJoint P₀ y v) n t
  set T₂ := robustTypicalSet (binJoint P₀ e v) n t
  set B₁ := exp (n * (H[Prod.snd | Prod.fst ; binJoint P₀ y v] +
    t * H[Prod.snd | Prod.fst ; binJoint P₀ y v]))
  set B₂ := exp (n * (H[Prod.snd | Prod.fst ; binJoint P₀ e v] +
    t * H[Prod.snd | Prod.fst ; binJoint P₀ e v]))
  have hlaw := hashLaw_isPMF (N := Fintype.card (Fin n → ν)) (Mb := Mb) (Kb := Kb)
  have hμ := iidPMF_isPMF hP n
  have hc₁ : ∀ yn : Fin n → β, ((univ.filter fun s' => zipSeq yn s' ∈ T₁).card : ℝ) ≤ B₁ :=
    fun yn =>
    card_condRobustTypicalSet_le hq₁ t yn
  have hc₂ : ∀ yn : Fin n → ε', ((univ.filter fun s' => zipSeq yn s' ∈ T₂).card : ℝ) ≤ B₂ :=
    fun yn =>
    card_condRobustTypicalSet_le hq₂ t yn
  obtain ⟨C, hC⟩ := exists_of_pointwise_avg hlaw hμ
    (F := fun C ω => (if binDec₁ T₁ C d (fun i => y (ω i))
        (C (Fintype.equivFin _ fun i => v (ω i))).1 ≠ (fun i => v (ω i)) then 1 else 0) +
      (if binDec₂ T₂ C d (fun i => e (ω i)) (C (Fintype.equivFin _ fun i => v (ω i))).1
        (C (Fintype.equivFin _ fun i => v (ω i))).2 ≠ (fun i => v (ω i)) then 1 else 0))
    (G := fun ω => (if zipSeq (fun i => y (ω i)) (fun i => v (ω i)) ∉ T₁ then 1 else 0) +
      (if zipSeq (fun i => e (ω i)) (fun i => v (ω i)) ∉ T₂ then 1 else 0) +
        B₁ * (1 / Mb) + B₂ * (1 / (Mb * Kb)))
    fun ω => sum_hash_err_le T₁ T₂ hc₁ hc₂ d _ _ _
  refine ⟨fun s => (C (Fintype.equivFin _ s)).1, fun s => (C (Fintype.equivFin _ s)).2,
    binDec₁ T₁ C d, binDec₂ T₂ C d, hC.trans (le_of_eq ?_)⟩
  have hsum₁ := sum_iidPMF_not_mem hP (pair y v) n T₁
  have hsum₂ := sum_iidPMF_not_mem hP (pair e v) n T₂
  have e₁ : ∑ ω : Fin n → ξ, iidPMF P₀ n ω *
      (if zipSeq (fun i => y (ω i)) (fun i => v (ω i)) ∉ T₁ then (1 : ℝ) else 0) =
      1 - prob (iidPMF (binJoint P₀ y v) n) T₁ := hsum₁
  have e₂ : ∑ ω : Fin n → ξ, iidPMF P₀ n ω *
      (if zipSeq (fun i => e (ω i)) (fun i => v (ω i)) ∉ T₂ then (1 : ℝ) else 0) =
      1 - prob (iidPMF (binJoint P₀ e v) n) T₂ := hsum₂
  simp only [mul_add, sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul, e₁, e₂]

/-- `H(Vⁿ | Eⁿ) = n H(V | E)`, for letterwise functions of an i.i.d. sequence. -/
lemma condEntropy_iid_comp (hP : IsPMF P₀) (n : ℕ) (v : ξ → ν) (e : ξ → ε') :
    H[(fun (ω : Fin n → ξ) i => v (ω i)) | (fun ω i => e (ω i)) ; iidPMF P₀ n] =
      n * H[v | e ; P₀] := by
  have hμ := iidPMF_isPMF hP n
  have e₁ : H[pair (fun (ω : Fin n → ξ) i => e (ω i)) (fun ω i => v (ω i)) ; iidPMF P₀ n] =
      H[fun (ω : Fin n → ξ) i => (e (ω i), v (ω i)) ; iidPMF P₀ n] := by
    refine entropyRV_eq_of_injective _ (fun w => (fun i => (w i).1, fun i => (w i).2)) ?_
      fun _ => rfl
    intro w w' h
    funext i
    exact Prod.ext (congrFun (Prod.mk.inj h).1 i) (congrFun (Prod.mk.inj h).2 i)
  rw [condEntropy_eq_sub hμ, e₁, entropyRV_iidPMF_comp hP n (fun x => (e x, v x)),
    entropyRV_iidPMF_comp hP n e, condEntropy_eq_sub hP]
  have e₂ : H[pair e v ; P₀] = H[fun x => (e x, v x) ; P₀] := rfl
  rw [e₂]
  ring

/-- `H(snd | fst)` for the law of a pair. -/
lemma condEntropy_binJoint (hP : IsPMF P₀) (v : ξ → ν) (y : ξ → β) :
    H[Prod.snd | Prod.fst ; binJoint P₀ y v] = H[v | y ; P₀] := by
  refine condEntropy_eq_of_dist_pair_eq (hP.dist _) hP ?_
  rw [dist_pair_fst_snd]

/-- The arithmetic of the bounds of double binning. -/
lemma doubleBin_rates {a b R δ t r : ℝ} {n : ℕ} (hδ0 : 0 < δ) (h : 4 * δ ≤ b - a - R)
    (hta : t * a ≤ δ / 2) (htb : t * b ≤ δ / 2) (hr : r = b - R + δ)
    {logM logK : ℝ} (hM : n * r ≤ logM) (hK : n * R ≤ logK) {Mb Kb : ℝ} (hMb : 0 < Mb)
    (hKb : 0 < Kb) (hMe : logM = log Mb) (hKe : logK = log Kb) :
    exp (n * (a + t * a)) * (1 / Mb) ≤ exp (-(n * δ)) ∧
      exp (n * (b + t * b)) * (1 / (Mb * Kb)) ≤ exp (-(n * (δ / 2))) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hMe' : Mb = exp logM := by rw [hMe, exp_log hMb]
  have hKe' : Kb = exp logK := by rw [hKe, exp_log hKb]
  constructor
  · rw [hMe', one_div, ← exp_neg, ← exp_add]
    refine exp_le_exp.2 ?_
    have h₁ : (n : ℝ) * (a + t * a) ≤ n * (a + δ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hn0
    have h₂ : (n : ℝ) * (a + δ / 2) + n * δ ≤ n * r := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by rw [hr]; linarith) hn0
    linarith
  · rw [hMe', hKe', ← exp_add, one_div, ← exp_neg, ← exp_add]
    refine exp_le_exp.2 ?_
    have h₁ : (n : ℝ) * (b + t * b) ≤ n * (b + δ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hn0
    have h₂ : (n : ℝ) * (b + δ / 2) + n * (δ / 2) = n * r + n * R := by
      rw [hr]
      ring
    linarith

open Classical in
/-- **Pages 23-32 to 23-36 of [elgamal2010]: the key from double binning, on an i.i.d. sequence.**
If `R` is below `H(V | E) - H(V | Y)`, in bits, then for every `ε` and all large `n` there are a
public index `M = b₁(Vⁿ)` and a key `K = b₂(Vⁿ) ∈ [1 : 2 ^ ⌈nR⌉]`, such that a decoder from
`(Yⁿ, M)` recovers `Vⁿ` with probability of error at most `ε`, with `I(K; Eⁿ, M) ≤ n ε` and
`H(K) ≥ n (R - ε)`. -/
theorem eventually_doubleBin (hP : IsPMF P₀) (v : ξ → ν) (y : ξ → β) (e : ξ → ε') {R : ℝ}
    (hR : 0 ≤ R) (hlt : R * log 2 < H[v | e ; P₀] - H[v | y ; P₀]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ (Mb : ℕ) (_ : NeZero Mb) (b₁ : (Fin n → ν) → Fin Mb)
      (b₂ : (Fin n → ν) → Fin (2 ^ ⌈n * R⌉₊)) (d₁ : (Fin n → β) → Fin Mb → Fin n → ν),
      (∑ ω : Fin n → ξ, iidPMF P₀ n ω *
        (if d₁ (fun i => y (ω i)) (b₁ fun i => v (ω i)) ≠ (fun i => v (ω i)) then 1 else 0)) ≤ ε ∧
      I[b₂ ∘ (fun (ω : Fin n → ξ) i => v (ω i)) :
        pair (fun ω i => e (ω i)) (b₁ ∘ fun ω i => v (ω i)) ; iidPMF P₀ n] ≤ n * ε ∧
      n * (R * log 2 - ε) ≤ H[b₂ ∘ (fun (ω : Fin n → ξ) i => v (ω i)) ; iidPMF P₀ n] := by
  classical
  have hl := log_pos one_lt_two
  set a := H[v | y ; P₀] with ha
  set b := H[v | e ; P₀] with hb
  have ha0 : 0 ≤ a := condEntropy_nonneg hP _ _
  have hb0 : 0 ≤ b := condEntropy_nonneg hP _ _
  set A := R * log 2 with hA
  have hA0 : 0 ≤ A := mul_nonneg hR hl.le
  set Lν := log (Fintype.card ν) with hLν
  have hLν0 : 0 ≤ Lν := log_natCast_nonneg _
  set δ := min ((b - a - A) / 4) (ε / 8) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ₁ : 4 * δ ≤ b - a - A := by
    have := min_le_left ((b - a - A) / 4) (ε / 8)
    linarith
  have hδ₂ : 8 * δ ≤ ε := by
    have := min_le_right ((b - a - A) / 4) (ε / 8)
    linarith
  set t := δ / (2 * (a + b + 1)) with ht
  have ht0 : 0 < t := by positivity
  have hta : t * a ≤ δ / 2 := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have htb : t * b ≤ δ / 2 := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  set ρ := b - A + δ with hρ
  have hρ0 : 0 ≤ ρ := by linarith
  set s := ρ / log 2 with hs
  have hs0 : 0 ≤ s := div_nonneg hρ0 hl.le
  have hsρ : s * log 2 = ρ := div_mul_cancel₀ ρ hl.ne'
  set η := min (ε / 2) (ε / (8 * (Lν + 1))) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  have hη₁ : η ≤ ε := (min_le_left _ _).trans (by linarith)
  have hη₂ : η * Lν ≤ ε / 8 := by
    have h₁ : η ≤ ε / (8 * (Lν + 1)) := min_le_right _ _
    have h₂ : η * (8 * (Lν + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 h₁
    nlinarith
  -- The bounds tend to `0`.
  set Bd : ℕ → ℝ := fun n =>
    (1 - prob (iidPMF (binJoint P₀ y v) n) (robustTypicalSet (binJoint P₀ y v) n t)) +
    (1 - prob (iidPMF (binJoint P₀ e v) n) (robustTypicalSet (binJoint P₀ e v) n t)) +
    exp (-(n * δ)) + exp (-(n * (δ / 2))) with hBd
  have hBdlim : Tendsto Bd atTop (𝓝 0) := by
    have t₁ : Tendsto (fun n => 1 - prob (iidPMF (binJoint P₀ y v) n)
        (robustTypicalSet (binJoint P₀ y v) n t)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet (hP.dist _) ht0).const_sub 1
    have t₂ : Tendsto (fun n => 1 - prob (iidPMF (binJoint P₀ e v) n)
        (robustTypicalSet (binJoint P₀ e v) n t)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet (hP.dist _) ht0).const_sub 1
    simpa [hBd] using ((t₁.add t₂).add (tendsto_exp_neg_mul_nat hδ0)).add
      (tendsto_exp_neg_mul_nat (half_pos hδ0))
  filter_upwards [(tendsto_order.1 hBdlim).2 _ hη0,
    eventually_gt_atTop ⌈32 * log 2 / ε⌉₊] with n hn hn1
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hnε : 8 * log 2 ≤ n * (ε / 4) := by
    have h₁ : 32 * log 2 / ε < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
    rw [div_lt_iff₀ hε] at h₁
    linarith
  have hMne : NeZero (2 ^ ⌈n * s⌉₊) := ⟨by positivity⟩
  have hKne : NeZero (2 ^ ⌈n * R⌉₊) := ⟨by positivity⟩
  obtain ⟨b₁, b₂, d₁, d₂, hbin⟩ := exists_doubleBin (Mb := 2 ^ ⌈n * s⌉₊) (Kb := 2 ^ ⌈n * R⌉₊)
    (n := n)
    hP v y e t
  rw [condEntropy_binJoint hP, condEntropy_binJoint hP] at hbin
  have hMpos : (0 : ℝ) < ((2 ^ ⌈n * s⌉₊ : ℕ) : ℝ) := by positivity
  have hKpos : (0 : ℝ) < ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := by positivity
  have hlM₁ := le_log_two_pow_ceil n s
  have hlM₂ := log_two_pow_ceil_le n hs0
  have hlK₁ := le_log_two_pow_ceil n R
  have hlK₂ := log_two_pow_ceil_le n hR
  rw [hsρ] at hlM₁ hlM₂
  obtain ⟨hE₁, hE₂⟩ := doubleBin_rates (a := a) (b := b) (R := A) (δ := δ) (t := t) (r := ρ)
    (n := n)
    hδ0 hδ₁ hta htb rfl hlM₁ hlK₁ hMpos hKpos rfl rfl
  have hμ := iidPMF_isPMF hP n
  -- The two errors.
  set Ind₁ : (Fin n → ξ) → ℝ := fun ω => if d₁ (fun i => y (ω i)) (b₁ fun i => v (ω i)) ≠
    (fun i => v (ω i)) then 1 else 0 with hInd₁
  set Ind₂ : (Fin n → ξ) → ℝ := fun ω => if d₂ (fun i => e (ω i)) (b₁ fun i => v (ω i))
    (b₂ fun i => v (ω i)) ≠ (fun i => v (ω i)) then 1 else 0 with hInd₂
  have hI₁ : ∀ ω, 0 ≤ Ind₁ ω := fun ω => by simp only [hInd₁]; split_ifs <;> norm_num
  have hI₂ : ∀ ω, 0 ≤ Ind₂ ω := fun ω => by simp only [hInd₂]; split_ifs <;> norm_num
  have htot : ∑ ω, iidPMF P₀ n ω * (Ind₁ ω + Ind₂ ω) ≤ η := by
    push_cast at hE₁ hE₂
    refine le_trans hbin (le_trans ?_ hn.le)
    simp only [hBd]
    push_cast
    linarith
  have hsplit : ∑ ω, iidPMF P₀ n ω * (Ind₁ ω + Ind₂ ω) =
      ∑ ω, iidPMF P₀ n ω * Ind₁ ω + ∑ ω, iidPMF P₀ n ω * Ind₂ ω := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by ring
  have hs₁ : 0 ≤ ∑ ω, iidPMF P₀ n ω * Ind₁ ω :=
    sum_nonneg fun ω _ => mul_nonneg (hμ.nonneg ω) (hI₁ ω)
  have hs₂ : 0 ≤ ∑ ω, iidPMF P₀ n ω * Ind₂ ω :=
    sum_nonneg fun ω _ => mul_nonneg (hμ.nonneg ω) (hI₂ ω)
  -- Fano's inequality for the second decoder.
  set T : (Fin n → ξ) → Fin n → ν := fun ω i => v (ω i) with hT
  set O : (Fin n → ξ) → Fin n → ε' := fun ω i => e (ω i) with hO
  have hF := fano_weak hμ T (pair (pair (b₁ ∘ T) (b₂ ∘ T)) O) (fun w => d₂ w.2 w.1.1 w.1.2)
  have hcard : log (Fintype.card (Fin n → ν)) = n * Lν := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  rw [hcard] at hF
  have herr : InfoTheory.errProb (iidPMF P₀ n) T (pair (pair (b₁ ∘ T) (b₂ ∘ T)) O)
      (fun w => d₂ w.2 w.1.1 w.1.2) = ∑ ω, iidPMF P₀ n ω * Ind₂ ω := by
    simp only [InfoTheory.errProb, hInd₂]
    refine sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp_all [pair]
  rw [herr] at hF
  have hP₂ : ∑ ω, iidPMF P₀ n ω * Ind₂ ω ≤ η := by linarith
  have hF₂ : H[T | pair (pair (b₁ ∘ T) (b₂ ∘ T)) O ; iidPMF P₀ n] ≤ log 2 + n * (ε / 8) := by
    have h₁ : (∑ ω, iidPMF P₀ n ω * Ind₂ ω) * (n * Lν) ≤ η * (n * Lν) :=
      mul_le_mul_of_nonneg_right hP₂ (by positivity)
    have h₂ : η * (n * Lν) ≤ n * (ε / 8) := by
      have := mul_le_mul_of_nonneg_left hη₂ hn0.le
      linarith
    linarith
  have hHTO : H[T | O ; iidPMF P₀ n] = n * b := condEntropy_iid_comp hP n v e
  have hHM : H[b₁ ∘ T ; iidPMF P₀ n] ≤ log ((2 ^ ⌈n * s⌉₊ : ℕ) : ℝ) := by
    have := entropyRV_le_log_card hμ (b₁ ∘ T)
    rwa [Fintype.card_fin] at this
  have hHK : H[b₂ ∘ T ; iidPMF P₀ n] ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := by
    have := entropyRV_le_log_card hμ (b₂ ∘ T)
    rwa [Fintype.card_fin] at this
  have hkey := entropy_key_ge_of_decodable hμ T O b₁ b₂
  have hleak := mutualInfo_key_le_of_decodable hμ T O b₁ b₂
  refine ⟨_, hMne, b₁, b₂, d₁, ?_, ?_, ?_⟩
  · have : ∑ ω, iidPMF P₀ n ω * Ind₁ ω ≤ η := by linarith
    exact this.trans hη₁
  · have e₁ : (n : ℝ) * A + n * ρ = n * b + n * δ := by
      rw [hρ]
      ring
    have e₂ : (n : ℝ) * δ ≤ n * (ε / 8) := mul_le_mul_of_nonneg_left (by linarith) hn0.le
    have e₃ : n * (ε / 8) + n * (ε / 8) + n * (ε / 4) ≤ n * ε := by
      have : (0 : ℝ) ≤ n * ε := by positivity
      linarith [show n * (ε / 8) + n * (ε / 8) + n * (ε / 4) = n * ε / 2 by ring]
    linarith
  · have e₁ : (n : ℝ) * ρ = n * b - n * A + n * δ := by
      rw [hρ]
      ring
    have e₂ : (n : ℝ) * δ ≤ n * (ε / 8) := mul_le_mul_of_nonneg_left (by linarith) hn0.le
    have e₃ : (n : ℝ) * (A - ε) = n * A - n * ε := by ring
    have e₄ : n * (ε / 8) + n * (ε / 8) + n * (ε / 4) ≤ n * ε := by
      have : (0 : ℝ) ≤ n * ε := by positivity
      linarith [show n * (ε / 8) + n * (ε / 8) + n * (ε / 4) = n * ε / 2 by ring]
    linarith

end Double

end InfoTheory
