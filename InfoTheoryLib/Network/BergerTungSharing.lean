/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungInner

/-!
# The Berger–Tung inner bound: time sharing

This file proves Theorem 1 of Lecture 13 with the time sharing random variable `Q`. Two codes used
one after the other share the rates and the distortions, so that the set of the achievable tuples,
up to an arbitrarily small increase of the rates, is convex. For each value of `Q`, the rate region
of
`p(u₁ | x₁, q) p(u₂ | x₂, q)` is a contra-polymatroid, since `I(X₁; U₁ | U₂) + I(X₂; U₂ | U₁) ≤
I(X₁, X₂; U₁, U₂)`, and so a rate pair of the region for `Q` splits into rate pairs for each `q`.

## Main definitions

* `DistLossyCode.append`, `DistLossyCode.castLE`: two codes one after the other, and more indices.
* `dlAchievableSet`: the achievable tuples up to an arbitrarily small increase of the rates.

## Main statements

* `convex_dlAchievableSet`: the convexity of the set.
* `exists_rate_split`: the rate pair splits among the values of `Q`.
* `isAchievableDL_of_lt_sharing`: **the Berger–Tung inner bound (Theorem 1 of Lecture 13)**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ β₁ β₂ υ₁ υ₂ : Type*} [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ}
  {d₁ : α₁ → β₁ → ℝ} {d₂ : α₂ → β₂ → ℝ}

/-! ### Codes one after the other -/

section Append

variable {M₁ M₂ M₁' M₂' n n' : ℕ}

/-- Two distributed lossy source codes one after the other. -/
def DistLossyCode.append (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂)
    (c' : DistLossyCode M₁' M₂' n' α₁ α₂ β₁ β₂) :
    DistLossyCode (M₁ * M₁') (M₂ * M₂') (n + n') α₁ α₂ β₁ β₂ where
  enc₁ x := finProdFinEquiv (c.enc₁ fun k => x (Fin.castAdd n' k), c'.enc₁ fun k => x (Fin.natAdd n
    k))
  enc₂ x := finProdFinEquiv (c.enc₂ fun k => x (Fin.castAdd n' k), c'.enc₂ fun k => x (Fin.natAdd n
    k))
  dec m :=
    (Fin.append (c.dec ((finProdFinEquiv.symm m.1).1, (finProdFinEquiv.symm m.2).1)).1
        (c'.dec ((finProdFinEquiv.symm m.1).2, (finProdFinEquiv.symm m.2).2)).1,
      Fin.append (c.dec ((finProdFinEquiv.symm m.1).1, (finProdFinEquiv.symm m.2).1)).2
        (c'.dec ((finProdFinEquiv.symm m.1).2, (finProdFinEquiv.symm m.2).2)).2)

omit [Fintype α₁] [Fintype α₂] in
lemma DistLossyCode.output_append (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂)
    (c' : DistLossyCode M₁' M₂' n' α₁ α₂ β₁ β₂) (ω : Fin n → α₁ × α₂) (ω' : Fin n' → α₁ × α₂) :
    (c.append c').output (Fin.append ω ω') =
      (Fin.append (c.output ω).1 (c'.output ω').1, Fin.append (c.output ω).2 (c'.output ω').2) := by
  have e₁ : (fun k => fstSeq (Fin.append ω ω') (Fin.castAdd n' k)) = fstSeq ω :=
    funext fun k => by simp [fstSeq]
  have e₂ : (fun k => fstSeq (Fin.append ω ω') (Fin.natAdd n k)) = fstSeq ω' :=
    funext fun k => by simp [fstSeq]
  have e₃ : (fun k => sndSeq (Fin.append ω ω') (Fin.castAdd n' k)) = sndSeq ω :=
    funext fun k => by simp [sndSeq]
  have e₄ : (fun k => sndSeq (Fin.append ω ω') (Fin.natAdd n k)) = sndSeq ω' :=
    funext fun k => by simp [sndSeq]
  simp only [DistLossyCode.output, DistLossyCode.append, e₁, e₂, e₃, e₄, Equiv.symm_apply_apply]

omit [Fintype α₁] [Fintype α₂] in
/-- `n d(xⁿ, yⁿ) = ∑ᵢ d(xᵢ, yᵢ)`. -/
lemma cast_mul_seqDistortion {a b : Type*} (d : a → b → ℝ) {n : ℕ} (x : Fin n → a) (y : Fin n → b) :
    n * seqDistortion d x y = ∑ i, d (x i) (y i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [seqDistortion]
    field_simp

/-- The sum over two blocks. -/
lemma sum_iidPMF_append (P : α₁ × α₂ → ℝ) (F : (Fin (n + n') → α₁ × α₂) → ℝ) :
    ∑ ω, iidPMF P (n + n') ω * F ω =
      ∑ ω, ∑ ω', iidPMF P n ω * iidPMF P n' ω' * F (Fin.append ω ω') := by
  rw [← (Fin.appendEquiv n n').sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => sum_congr rfl fun ω' _ => ?_
  have e : (Fin.appendEquiv n n') (ω, ω') = Fin.append ω ω' := rfl
  rw [e]
  congr 1
  simp only [iidPMF, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

omit [Fintype α₁] [Fintype α₂] in
lemma seqDistortion_append {a b : Type*} (d : a → b → ℝ) (x : Fin n → a) (x' : Fin n' → a)
    (y : Fin n → b) (y' : Fin n' → b) :
    ((n + n' : ℕ) : ℝ) * seqDistortion d (Fin.append x x') (Fin.append y y') =
      n * seqDistortion d x y + n' * seqDistortion d x' y' := by
  rw [cast_mul_seqDistortion, cast_mul_seqDistortion, cast_mul_seqDistortion, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

omit [Fintype α₁] [Fintype α₂] in
lemma fstSeq_append (ω : Fin n → α₁ × α₂) (ω' : Fin n' → α₁ × α₂) :
    fstSeq (Fin.append ω ω') = Fin.append (fstSeq ω) (fstSeq ω') := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp [fstSeq]

omit [Fintype α₁] [Fintype α₂] in
lemma sndSeq_append (ω : Fin n → α₁ × α₂) (ω' : Fin n' → α₁ × α₂) :
    sndSeq (Fin.append ω ω') = Fin.append (sndSeq ω) (sndSeq ω') := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp [sndSeq]

/-- The average over two independent blocks of a sum of a function of each. -/
lemma sum_sum_mul_add (hP : IsPMF P) (A : (Fin n → α₁ × α₂) → ℝ) (B : (Fin n' → α₁ × α₂) → ℝ) :
    ∑ ω, ∑ ω', iidPMF P n ω * iidPMF P n' ω' * (A ω + B ω') =
      ∑ ω, iidPMF P n ω * A ω + ∑ ω', iidPMF P n' ω' * B ω' := by
  have hμ := iidPMF_isPMF hP n
  have hμ' := iidPMF_isPMF hP n'
  have e : ∀ ω, ∑ ω', iidPMF P n ω * iidPMF P n' ω' * (A ω + B ω') =
      iidPMF P n ω * A ω + iidPMF P n ω * ∑ ω', iidPMF P n' ω' * B ω' := fun ω => by
    rw [show (∑ ω', iidPMF P n ω * iidPMF P n' ω' * (A ω + B ω')) =
      ∑ ω', (iidPMF P n' ω' * (iidPMF P n ω * A ω) + iidPMF P n ω * (iidPMF P n' ω' * B ω')) from
      sum_congr rfl fun ω' _ => by ring, sum_add_distrib, ← sum_mul, hμ'.sum_eq_one, one_mul,
      mul_sum]
  simp only [e]
  rw [sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul]

/-- **Time sharing.** The distortion of two codes one after the other is the weighted mean. -/
theorem DistLossyCode.distortion₁_append (hP : IsPMF P) (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂)
    (c' : DistLossyCode M₁' M₂' n' α₁ α₂ β₁ β₂) :
    ((n + n' : ℕ) : ℝ) * (c.append c').distortion₁ P d₁ =
      n * c.distortion₁ P d₁ + n' * c'.distortion₁ P d₁ := by
  simp only [DistLossyCode.distortion₁]
  rw [mul_sum, show (∑ ω, ((n + n' : ℕ) : ℝ) * (iidPMF P (n + n') ω *
      seqDistortion d₁ (fstSeq ω) ((c.append c').output ω).1)) =
      ∑ ω, iidPMF P (n + n') ω * (((n + n' : ℕ) : ℝ) *
        seqDistortion d₁ (fstSeq ω) ((c.append c').output ω).1) from
    sum_congr rfl fun ω _ => by ring, sum_iidPMF_append]
  have e : ∀ ω ω', ((n + n' : ℕ) : ℝ) * seqDistortion d₁ (fstSeq (Fin.append ω ω'))
      ((c.append c').output (Fin.append ω ω')).1 =
      n * seqDistortion d₁ (fstSeq ω) (c.output ω).1 +
        n' * seqDistortion d₁ (fstSeq ω') (c'.output ω').1 := fun ω ω' => by
    rw [DistLossyCode.output_append, fstSeq_append, seqDistortion_append]
  simp only [e]
  rw [sum_sum_mul_add hP, mul_sum, mul_sum]
  congr 1 <;> exact sum_congr rfl fun ω _ => by ring

/-- **Time sharing.** The distortion of two codes one after the other is the weighted mean. -/
theorem DistLossyCode.distortion₂_append (hP : IsPMF P) (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂)
    (c' : DistLossyCode M₁' M₂' n' α₁ α₂ β₁ β₂) :
    ((n + n' : ℕ) : ℝ) * (c.append c').distortion₂ P d₂ =
      n * c.distortion₂ P d₂ + n' * c'.distortion₂ P d₂ := by
  simp only [DistLossyCode.distortion₂]
  rw [mul_sum, show (∑ ω, ((n + n' : ℕ) : ℝ) * (iidPMF P (n + n') ω *
      seqDistortion d₂ (sndSeq ω) ((c.append c').output ω).2)) =
      ∑ ω, iidPMF P (n + n') ω * (((n + n' : ℕ) : ℝ) *
        seqDistortion d₂ (sndSeq ω) ((c.append c').output ω).2) from
    sum_congr rfl fun ω _ => by ring, sum_iidPMF_append]
  have e : ∀ ω ω', ((n + n' : ℕ) : ℝ) * seqDistortion d₂ (sndSeq (Fin.append ω ω'))
      ((c.append c').output (Fin.append ω ω')).2 =
      n * seqDistortion d₂ (sndSeq ω) (c.output ω).2 +
        n' * seqDistortion d₂ (sndSeq ω') (c'.output ω').2 := fun ω ω' => by
    rw [DistLossyCode.output_append, sndSeq_append, seqDistortion_append]
  simp only [e]
  rw [sum_sum_mul_add hP, mul_sum, mul_sum]
  congr 1 <;> exact sum_congr rfl fun ω _ => by ring

/-- A code with more indices. -/
def DistLossyCode.castLE {M₁' M₂' : ℕ} (h₁ : M₁ ≤ M₁') (h₂ : M₂ ≤ M₂') (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂) : DistLossyCode M₁' M₂' n α₁ α₂ β₁ β₂ where
  enc₁ x := Fin.castLE h₁ (c.enc₁ x)
  enc₂ x := Fin.castLE h₂ (c.enc₂ x)
  dec m := c.dec (if hm : (m.1 : ℕ) < M₁ then ⟨m.1, hm⟩ else ⟨0, hM₁⟩,
    if hm : (m.2 : ℕ) < M₂ then ⟨m.2, hm⟩ else ⟨0, hM₂⟩)

omit [Fintype α₁] [Fintype α₂] in
lemma DistLossyCode.output_castLE {M₁' M₂' : ℕ} (h₁ : M₁ ≤ M₁') (h₂ : M₂ ≤ M₂') (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (c : DistLossyCode M₁ M₂ n α₁ α₂ β₁ β₂) (ω : Fin n → α₁ × α₂) :
    (c.castLE h₁ h₂ hM₁ hM₂).output ω = c.output ω := by
  simp [DistLossyCode.output, DistLossyCode.castLE]

end Append

/-! ### The convexity of the achievable set -/

section Convex

variable [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂]

/-- The tuples `(R₁, R₂, D₁, D₂)` such that `(R₁ + η, R₂ + η)` is achievable with `(D₁, D₂)`, for
every
`η > 0`. -/
def dlAchievableSet (P : α₁ × α₂ → ℝ) (d₁ : α₁ → β₁ → ℝ) (d₂ : α₂ → β₂ → ℝ) :
    Set (ℝ × ℝ × ℝ × ℝ) :=
  {z | ∀ η > 0, IsAchievableDL P d₁ d₂ (z.1 + η) (z.2.1 + η) z.2.2.1 z.2.2.2}

omit [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂] in
/-- Two codes one after the other, with more indices and with the length `n`. -/
lemma exists_code_append (hP : IsPMF P) {M₁ M₂ M₁' M₂' M M' m₁ m₂ n : ℕ}
    (c : DistLossyCode M₁ M₂ m₁ α₁ α₂ β₁ β₂) (c' : DistLossyCode M₁' M₂' m₂ α₁ α₂ β₁ β₂)
    (hn : m₁ + m₂ = n) (h₁ : M₁ * M₁' ≤ M) (h₂ : M₂ * M₂' ≤ M') (hM₁ : 0 < M₁ * M₁')
    (hM₂ : 0 < M₂ * M₂') :
    ∃ C : DistLossyCode M M' n α₁ α₂ β₁ β₂,
      (n : ℝ) * C.distortion₁ P d₁ = m₁ * c.distortion₁ P d₁ + m₂ * c'.distortion₁ P d₁ ∧
      (n : ℝ) * C.distortion₂ P d₂ = m₁ * c.distortion₂ P d₂ + m₂ * c'.distortion₂ P d₂ := by
  subst hn
  refine ⟨(c.append c').castLE h₁ h₂ hM₁ hM₂, ?_, ?_⟩
  · rw [← DistLossyCode.distortion₁_append hP]
    simp only [DistLossyCode.distortion₁, DistLossyCode.output_castLE]
  · rw [← DistLossyCode.distortion₂_append hP]
    simp only [DistLossyCode.distortion₂, DistLossyCode.output_castLE]

omit [Fintype α₁] [Fintype α₂] [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂] in
/-- The weighted mean of two distortions. -/
private lemma weighted_le {m₁ m₂ n : ℕ} {s t x x' D D' ε : ℝ} (hn : (0 : ℝ) < n)
    (hadd : (m₁ : ℝ) + m₂ = n) (hst : s + t = 1) (h₁ : (m₁ : ℝ) ≤ s * n)
    (h₁' : s * n - 1 ≤ (m₁ : ℝ)) (hx : x ≤ D + ε / 2) (hx' : x' ≤ D' + ε / 2)
    (hsmall : |D - D'| / n ≤ ε / 2) {y : ℝ} (hy : (n : ℝ) * y = m₁ * x + m₂ * x') :
    y ≤ s * D + t * D' + ε := by
  have hA : |D - D'| ≤ ε / 2 * n := (div_le_iff₀ hn).1 hsmall
  have hm₁ : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg m₁
  have hm₂ : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg m₂
  have h1 := mul_le_mul_of_nonneg_left hx hm₁
  have h2 := mul_le_mul_of_nonneg_left hx' hm₂
  have ht : t = 1 - s := by linarith
  have hm2 : (m₂ : ℝ) = n - m₁ := by linarith
  refine le_of_mul_le_mul_left ?_ hn
  rw [hy]
  have hkey : (m₁ : ℝ) * D + m₂ * D' ≤ n * (s * D + t * D') + |D - D'| := by
    rw [hm2, ht]
    have h3 : ((m₁ : ℝ) - s * n) * (D - D') ≤ |D - D'| := by
      have h4 : |(m₁ : ℝ) - s * n| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      calc ((m₁ : ℝ) - s * n) * (D - D') ≤ |((m₁ : ℝ) - s * n) * (D - D')| := le_abs_self _
        _ = |(m₁ : ℝ) - s * n| * |D - D'| := abs_mul _ _
        _ ≤ 1 * |D - D'| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
        _ = |D - D'| := one_mul _
    linarith
  have hsum : (m₁ : ℝ) * (D + ε / 2) + m₂ * (D' + ε / 2) =
      m₁ * D + m₂ * D' + ((m₁ : ℝ) + m₂) * (ε / 2) := by ring
  rw [hadd] at hsum
  have hε : (n : ℝ) * (s * D + t * D' + ε) = n * (s * D + t * D') + n * ε := by ring
  rw [hε]
  linarith

/-- The floors of the rates of two blocks. -/
private lemma floor_add_floor_le {s t r r' T : ℝ} {n₁ n₂ n : ℕ} (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hs : (n₁ : ℝ) ≤ s * n) (ht : (n₂ : ℝ) ≤ t * n + 1) (hT : s * r + t * r' + r' / n ≤ T)
    (hn : (0 : ℝ) < n) : ⌊n₁ * r⌋₊ + ⌊n₂ * r'⌋₊ ≤ ⌊n * T⌋₊ := by
  refine Nat.le_floor ?_
  push_cast
  have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n₁) hr)
  have h2 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n₂) hr')
  have h3 : (n₁ : ℝ) * r ≤ s * n * r := mul_le_mul_of_nonneg_right hs hr
  have h4 : (n₂ : ℝ) * r' ≤ (t * n + 1) * r' := mul_le_mul_of_nonneg_right ht hr'
  have h5 : n * (s * r + t * r' + r' / n) ≤ n * T := mul_le_mul_of_nonneg_left hT hn.le
  have h6 : n * (s * r + t * r' + r' / n) = s * n * r + (t * n + 1) * r' := by
    field_simp
    ring
  linarith

/-- **Time sharing (Lecture 13, page 13-9).** The set of the achievable tuples is convex. -/
theorem convex_dlAchievableSet (hP : IsPMF P) : Convex ℝ (dlAchievableSet P d₁ d₂) := by
  rintro ⟨R₁, R₂, D₁, D₂⟩ hz ⟨R₁', R₂', D₁', D₂'⟩ hz' s t hs ht hst
  intro η hη
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  -- The cases of a trivial mixture.
  rcases hs.eq_or_lt with rfl | hs0
  · have ht1 : t = 1 := by linarith
    subst ht1
    simpa using hz' η hη
  rcases ht.eq_or_lt with rfl | ht0
  · have hs1 : s = 1 := by linarith
    subst hs1
    simpa using hz η hη
  obtain ⟨hr₁, hr₂, c, hc⟩ := hz (η / 2) (half_pos hη)
  obtain ⟨hr₁', hr₂', c', hc'⟩ := hz' (η / 2) (half_pos hη)
  simp only at hr₁ hr₂ hc hr₁' hr₂' hc'
  have hT₁ : 0 ≤ s * R₁ + t * R₁' + η := by
    have : s * (R₁ + η / 2) + t * (R₁' + η / 2) = s * R₁ + t * R₁' + η / 2 := by
      have : t = 1 - s := by linarith
      subst this
      ring
    have h0 : 0 ≤ s * (R₁ + η / 2) + t * (R₁' + η / 2) := by positivity
    linarith
  have hT₂ : 0 ≤ s * R₂ + t * R₂' + η := by
    have : s * (R₂ + η / 2) + t * (R₂' + η / 2) = s * R₂ + t * R₂' + η / 2 := by
      have : t = 1 - s := by linarith
      subst this
      ring
    have h0 : 0 ≤ s * (R₂ + η / 2) + t * (R₂' + η / 2) := by positivity
    linarith
  refine isAchievableDL_of_eventually hT₁ hT₂ fun ε hε => ?_
  -- The lengths of the two blocks.
  set n₁ : ℕ → ℕ := fun n => ⌊s * n⌋₊ with hn₁
  set n₂ : ℕ → ℕ := fun n => n - ⌊s * n⌋₊ with hn₂
  have hs1 : s ≤ 1 := by linarith
  have hle : ∀ n : ℕ, n₁ n ≤ n := fun n => by
    refine Nat.floor_le_of_le ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hadd : ∀ n : ℕ, n₁ n + n₂ n = n := fun n => Nat.add_sub_cancel' (hle n)
  have hlim₁ : Tendsto n₁ atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hs0)
  have hn₁le : ∀ n : ℕ, (n₁ n : ℝ) ≤ s * n := fun n =>
    Nat.floor_le (by positivity)
  have hn₁ge : ∀ n : ℕ, s * n - 1 ≤ (n₁ n : ℝ) := fun n => by
    have := Nat.lt_floor_add_one (s * n)
    simp only [hn₁]
    linarith
  have hcast₂ : ∀ n : ℕ, (n₂ n : ℝ) = n - n₁ n := fun n => by
    have : ((n₁ n + n₂ n : ℕ) : ℝ) = n := by rw [hadd]
    push_cast at this
    linarith
  have hn₂le : ∀ n : ℕ, (n₂ n : ℝ) ≤ t * n + 1 := fun n => by
    rw [hcast₂]
    have := hn₁ge n
    have ht' : t = 1 - s := by linarith
    rw [ht']
    linarith
  have hn₂ge : ∀ n : ℕ, t * n ≤ (n₂ n : ℝ) := fun n => by
    rw [hcast₂]
    have := hn₁le n
    have ht' : t = 1 - s := by linarith
    rw [ht']
    linarith
  have hlim₂ : Tendsto n₂ atTop atTop := by
    refine tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono hn₂ge ?_)
    exact tendsto_natCast_atTop_atTop.const_mul_atTop ht0
  have hε' : 0 < ε / 2 := half_pos hε
  have hsmall : ∀ A : ℝ, ∀ {B : ℝ}, 0 < B → ∀ᶠ n : ℕ in atTop, A / n ≤ B := fun A B hB =>
    ((tendsto_const_div_atTop_nhds_zero_nat A).eventually (gt_mem_nhds hB)).mono fun _ h => h.le
  filter_upwards [hlim₁.eventually (hc (ε / 2) hε'), hlim₂.eventually (hc' (ε / 2) hε'),
    hsmall (R₁' + η / 2) (half_pos hη), hsmall (R₂' + η / 2) (half_pos hη), hsmall |D₁ - D₁'| hε',
    hsmall |D₂ - D₂'| hε', eventually_gt_atTop 0] with n hn₁c hn₂c hA₁ hA₂ hD₁ hD₂ hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcast : (n₁ n : ℝ) + n₂ n = n := by
    have : ((n₁ n + n₂ n : ℕ) : ℝ) = n := by rw [hadd]
    exact_mod_cast this
  have hb₁ : ⌊(n₁ n : ℝ) * (R₁ + η / 2)⌋₊ + ⌊(n₂ n : ℝ) * (R₁' + η / 2)⌋₊ ≤ ⌊n * (s * R₁ + t * R₁' +
    η)⌋₊ := by
    refine floor_add_floor_le hr₁ hr₁' (hn₁le n) (hn₂le n) ?_ hn'
    have e : s * (R₁ + η / 2) + t * (R₁' + η / 2) = s * R₁ + t * R₁' + η / 2 := by
      have : t = 1 - s := by linarith
      subst this
      ring
    linarith
  have hb₂ : ⌊(n₁ n : ℝ) * (R₂ + η / 2)⌋₊ + ⌊(n₂ n : ℝ) * (R₂' + η / 2)⌋₊ ≤ ⌊n * (s * R₂ + t * R₂' +
    η)⌋₊ := by
    refine floor_add_floor_le hr₂ hr₂' (hn₁le n) (hn₂le n) ?_ hn'
    have e : s * (R₂ + η / 2) + t * (R₂' + η / 2) = s * R₂ + t * R₂' + η / 2 := by
      have : t = 1 - s := by linarith
      subst this
      ring
    linarith
  obtain ⟨C, hC₁, hC₂⟩ := exists_code_append hP (d₁ := d₁) (d₂ := d₂) (c (n₁ n)) (c' (n₂ n))
    (hadd n) (M := 2 ^ ⌊n * (s * R₁ + t * R₁' + η)⌋₊) (M' := 2 ^ ⌊n * (s * R₂ + t * R₂' + η)⌋₊)
    (by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) hb₁)
    (by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) hb₂)
    (by positivity) (by positivity)
  exact ⟨C, weighted_le hn' hcast (by linarith) (hn₁le n) (hn₁ge n) hn₁c.1 hn₂c.1 hD₁ hC₁,
    weighted_le hn' hcast (by linarith) (hn₁le n) (hn₁ge n) hn₁c.2 hn₂c.2 hD₂ hC₂⟩

end Convex

/-! ### Theorem 1 -/

section Theorem

omit [Fintype α₁] [Fintype α₂] in
/-- A rate pair above an achievable rate pair is achievable, also with larger distortions. -/
theorem IsAchievableDL.mono [Fintype α₁] [Fintype α₂] {R₁ R₂ D₁ D₂ R₁' R₂' D₁' D₂' : ℝ}
    (h : IsAchievableDL P d₁ d₂ R₁ R₂ D₁ D₂) (h₁ : R₁ ≤ R₁') (h₂ : R₂ ≤ R₂') (h₃ : D₁ ≤ D₁')
    (h₄ : D₂ ≤ D₂') : IsAchievableDL P d₁ d₂ R₁' R₂' D₁' D₂' := by
  obtain ⟨hr₁, hr₂, c, hc⟩ := h
  have hle : ∀ {a b : ℝ}, a ≤ b → 0 ≤ a → ∀ n : ℕ, 2 ^ ⌊n * a⌋₊ ≤ 2 ^ ⌊n * b⌋₊ := fun hab ha n =>
    Nat.pow_le_pow_right (by norm_num) (Nat.floor_le_floor
      (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n)))
  refine ⟨hr₁.trans h₁, hr₂.trans h₂, fun n =>
    (c n).castLE (hle h₁ hr₁ n) (hle h₂ hr₂ n) (by positivity) (by positivity),
    fun ε hε => ?_⟩
  filter_upwards [hc ε hε] with n hn
  refine ⟨?_, ?_⟩
  · have e : ((c n).castLE (hle h₁ hr₁ n) (hle h₂ hr₂ n) (by positivity)
        (by positivity)).distortion₁ P d₁ = (c n).distortion₁ P d₁ := by
      simp only [DistLossyCode.distortion₁, DistLossyCode.output_castLE]
    rw [e]
    linarith [hn.1]
  · have e : ((c n).castLE (hle h₁ hr₁ n) (hle h₂ hr₂ n) (by positivity)
        (by positivity)).distortion₂ P d₂ = (c n).distortion₂ P d₂ := by
      simp only [DistLossyCode.distortion₂, DistLossyCode.output_castLE]
    rw [e]
    linarith [hn.2]

omit [Fintype α₁] [Fintype α₂] in
/-- **The splitting of the rates among the values of `Q`.** A rate pair in the interior of the sum
of
contra-polymatroids is a sum of rate pairs in the interior of each of them. -/
theorem exists_rate_split {Q : Type*} [Fintype Q] {τ : Q → ℝ} (hτ : IsPMF τ) {a b c : Q → ℝ}
    (habc : ∀ q, a q + b q ≤ c q) {R₁ R₂ : ℝ} (h₁ : ∑ q, τ q * a q < R₁)
    (h₂ : ∑ q, τ q * b q < R₂) (h₁₂ : ∑ q, τ q * c q < R₁ + R₂) :
    ∃ r₁ r₂ : Q → ℝ, (∀ q, a q < r₁ q ∧ b q < r₂ q ∧ c q < r₁ q + r₂ q) ∧
      ∑ q, τ q * r₁ q < R₁ ∧ ∑ q, τ q * r₂ q < R₂ := by
  set A := ∑ q, τ q * a q with hA
  set B := ∑ q, τ q * b q with hB
  set C := ∑ q, τ q * c q with hC
  have hABC : A + B ≤ C := by
    rw [hA, hB, hC, ← sum_add_distrib]
    exact sum_le_sum fun q _ => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (habc q) (hτ.nonneg q)
  set S := min (R₁ - A) (min (R₂ - B) (R₁ + R₂ - C)) with hS
  have hS0 : 0 < S := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hS₁ : S ≤ R₁ - A := min_le_left _ _
  have hS₂ : S ≤ R₂ - B := (min_le_right _ _).trans (min_le_left _ _)
  have hS₃ : S ≤ R₁ + R₂ - C := (min_le_right _ _).trans (min_le_right _ _)
  set η := S / 5 with hη
  have hη0 : 0 < η := by positivity
  set r := min (R₁ - 2 * η) (C - B) with hr
  have hrA : A ≤ r := le_min (by rw [hη]; linarith) (by linarith)
  have hrC : r ≤ C - B := min_le_right _ _
  have hrR : r ≤ R₁ - 2 * η := min_le_left _ _
  have hCr : C - r ≤ R₂ - 2 * η := by
    rcases min_choice (R₁ - 2 * η) (C - B) with h | h
    · rw [hr, h, hη]
      linarith
    · rw [hr, h, hη]
      linarith
  -- The mixture of the two corner points.
  obtain ⟨t, ht0, ht1, htr⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ t * A + (1 - t) * (C - B) = r := by
    rcases eq_or_lt_of_le (show A ≤ C - B by linarith) with h | h
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      have : r = A := le_antisymm (by rw [h]; exact hrC) hrA
      rw [this, h]
      ring
    · have hd : 0 < C - B - A := by linarith
      refine ⟨(C - B - r) / (C - B - A), div_nonneg (by linarith) hd.le,
        (div_le_one hd).2 (by linarith), ?_⟩
      field_simp
      ring
  set v : Q → ℝ := fun q => t * a q + (1 - t) * (c q - b q) with hv
  have hsum : ∑ q, τ q * v q = r := by
    rw [← htr, hA, hB, hC, mul_sum]
    have e : ∑ q, τ q * v q = t * ∑ q, τ q * a q +
        (1 - t) * (∑ q, τ q * c q - ∑ q, τ q * b q) := by
      rw [← sum_sub_distrib, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun q _ => ?_
      simp only [hv]
      ring
    rw [e, mul_sum]
  have hv1 : ∀ q, a q ≤ v q := fun q => by
    have h3 : a q ≤ c q - b q := by linarith [habc q]
    have h4 : (1 - t) * a q ≤ (1 - t) * (c q - b q) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    simp only [hv]
    linarith
  have hv2 : ∀ q, v q ≤ c q - b q := fun q => by
    have h3 : a q ≤ c q - b q := by linarith [habc q]
    have h4 : t * a q ≤ t * (c q - b q) := mul_le_mul_of_nonneg_left h3 ht0
    simp only [hv]
    linarith
  refine ⟨fun q => v q + η, fun q => c q - v q + η, fun q => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · linarith [hv1 q]
  · linarith [hv2 q]
  · linarith
  · have e : ∑ q, τ q * (v q + η) = r + η := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hτ.sum_eq_one, one_mul, hsum]
    rw [e]
    linarith
  · have e : ∑ q, τ q * (c q - v q + η) = C - r + η := by
      simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul, hτ.sum_eq_one,
        one_mul, hsum]
      rfl
    rw [e]
    linarith

variable {Q : Type*} [Fintype Q] [Fintype υ₁] [Fintype υ₂]

/-- **Theorem 1 of Lecture 13 of [elgamal2010], page 13-4: the Berger–Tung inner bound.** A rate
pair is
achievable with the distortion pair `(D₁, D₂)` if `R₁ > I(X₁; U₁ | U₂, Q)`, `R₂ > I(X₂; U₂ | U₁, Q)`
and
`R₁ + R₂ > I(X₁, X₂; U₁, U₂ | Q)`, in bits, for some `p(q) p(u₁ | x₁, q) p(u₂ | x₂, q)` and
`x̂ⱼ(u₁, u₂, q)` with `E dⱼ(Xⱼ, X̂ⱼ) ≤ Dⱼ`. The informations given `Q` are the means over `q`. -/
theorem isAchievableDL_of_lt_sharing [Finite β₁] [Finite β₂] (hP : IsPMF P)
    (hd₁ : ∀ x y, 0 ≤ d₁ x y) (hd₂ : ∀ x y, 0 ≤ d₂ x y) {τ : Q → ℝ} (hτ : IsPMF τ)
    {κ₁ : Q → α₁ → υ₁ → ℝ} {κ₂ : Q → α₂ → υ₂ → ℝ} (h₁ : ∀ q, IsChannel (κ₁ q))
    (h₂ : ∀ q, IsChannel (κ₂ q)) (f₁ : Q → υ₁ → υ₂ → β₁) (f₂ : Q → υ₁ → υ₂ → β₂) {R₁ R₂ D₁ D₂ : ℝ}
    (hc₁ : ∑ q, τ q * btCost₁ P (κ₁ q) (κ₂ q) d₁ (f₁ q) ≤ D₁)
    (hc₂ : ∑ q, τ q * btCost₂ P (κ₁ q) (κ₂ q) d₂ (f₂ q) ≤ D₂)
    (hR₁ : (∑ q, τ q * btRate₁ P (κ₁ q) (κ₂ q)) / log 2 < R₁)
    (hR₂ : (∑ q, τ q * btRate₂ P (κ₁ q) (κ₂ q)) / log 2 < R₂)
    (hR₁₂ : (∑ q, τ q * btRate₁₂ P (κ₁ q) (κ₂ q)) / log 2 < R₁ + R₂) :
    IsAchievableDL P d₁ d₂ R₁ R₂ D₁ D₂ := by
  have hl := log_pos one_lt_two
  obtain ⟨q₀, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hτ)
  obtain ⟨⟨x₁, x₂⟩⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  obtain ⟨u₁, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF (h₁ q₀ x₁))
  obtain ⟨u₂, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF (h₂ q₀ x₂))
  have hβ₁ : Nonempty β₁ := ⟨f₁ q₀ u₁ u₂⟩
  have hβ₂ : Nonempty β₂ := ⟨f₂ q₀ u₁ u₂⟩
  -- The rates of each `q`, in bits.
  set a := fun q => btRate₁ P (κ₁ q) (κ₂ q) / log 2 with ha
  set b := fun q => btRate₂ P (κ₁ q) (κ₂ q) / log 2 with hb
  set c := fun q => btRate₁₂ P (κ₁ q) (κ₂ q) / log 2 with hc
  have habc : ∀ q, a q + b q ≤ c q := fun q => by
    have hI : 0 ≤ I[fun z : ((α₁ × υ₁) × α₂) × υ₂ => z.1.1.2 : Prod.snd ;
        btLaw P (κ₁ q) (κ₂ q)] := mutualInfo_nonneg (btLaw_isPMF hP (h₁ q) (h₂ q)) _ _
    simp only [ha, hb, hc]
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ hl.le
    rw [btRate₁_eq hP (h₁ q) (h₂ q), btRate₂_eq hP (h₁ q) (h₂ q), btRate₁₂_eq hP (h₁ q) (h₂ q)]
    linarith
  have hsum : ∀ g : Q → ℝ, ∑ q, τ q * (g q / log 2) = (∑ q, τ q * g q) / log 2 := fun g => by
    rw [sum_div]
    exact sum_congr rfl fun q _ => by ring
  obtain ⟨r₁, r₂, hr, hs₁, hs₂⟩ := exists_rate_split hτ habc
    (by simpa only [ha, hsum] using hR₁) (by simpa only [hb, hsum] using hR₂)
    (by simpa only [hc, hsum] using hR₁₂)
  -- The tuples of the values of `Q`.
  set z : Q → ℝ × ℝ × ℝ × ℝ := fun q => (r₁ q, r₂ q, btCost₁ P (κ₁ q) (κ₂ q) d₁ (f₁ q),
    btCost₂ P (κ₁ q) (κ₂ q) d₂ (f₂ q)) with hz
  have hmem : ∀ q ∈ (univ : Finset Q), z q ∈ dlAchievableSet P d₁ d₂ := fun q _ η hη => by
    obtain ⟨h3, h4, h5⟩ := hr q
    exact isAchievableDL_of_lt hP hd₁ hd₂ (h₁ q) (h₂ q) (f₁ q) (f₂ q) le_rfl le_rfl
      (by simp only [hz]; linarith) (by simp only [hz]; linarith) (by simp only [hz]; linarith)
  have hconv := (convex_dlAchievableSet (d₁ := d₁) (d₂ := d₂) hP).sum_mem
    (fun q _ => hτ.nonneg q) hτ.sum_eq_one hmem
  -- The mixture.
  set η := min (R₁ - ∑ q, τ q * r₁ q) (R₂ - ∑ q, τ q * r₂ q) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hach := hconv η hη0
  have e₁ : (∑ q, τ q • z q).1 = ∑ q, τ q * r₁ q := by
    simp only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul, hz]
  have e₂ : (∑ q, τ q • z q).2.1 = ∑ q, τ q * r₂ q := by
    simp only [Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, smul_eq_mul, hz]
  have e₃ : (∑ q, τ q • z q).2.2.1 = ∑ q, τ q * btCost₁ P (κ₁ q) (κ₂ q) d₁ (f₁ q) := by
    simp only [Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, smul_eq_mul, hz]
  have e₄ : (∑ q, τ q • z q).2.2.2 = ∑ q, τ q * btCost₂ P (κ₁ q) (κ₂ q) d₂ (f₂ q) := by
    simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, hz]
  rw [e₁, e₂, e₃, e₄] at hach
  have h5 : η ≤ R₁ - ∑ q, τ q * r₁ q := min_le_left _ _
  have h6 : η ≤ R₂ - ∑ q, τ q * r₂ q := min_le_right _ _
  exact hach.mono (by linarith) (by linarith) hc₁ hc₂

end Theorem

end InfoTheory
