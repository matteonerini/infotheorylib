/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayCFTest

/-!
# The covering step of compress–forward

The relay of compress–forward describes its received sequence `y₁ⁿ` by a sequence `ŷ₁ⁿ` of a
codebook drawn from `p(ŷ₁ | x₁)`. We bound the probability that `(xⁿ, x₁ⁿ, ŷ₁ⁿ, yⁿ)` is not jointly
typical.

## Main definitions

* `cfLaw`: the law of `((X, X₁), (Y, Y₁), Ŷ₁)`, for `p(x) p(x₁) p(y, y₁ | x, x₁) p(ŷ₁ | y₁, x₁)`.
* `cfGood`: the triples `(x₁ⁿ, y₁ⁿ, ŷ₁ⁿ)` that are typical, and such that `(xⁿ, x₁ⁿ, ŷ₁ⁿ, yⁿ)` is
  typical with high probability given `(x₁ⁿ, y₁ⁿ)`.
* `cfPick`: the index of a good sequence of the codebook.

## Main statements

* `sum_cf_all`: the sum over all the sequences of a block is an i.i.d. expectation.
* `sum_cover_le`: **the covering bound**.

## Implementation notes

As in Lecture 12, a typical sequence is not good enough: `ŷ₁ⁿ` must be typical with `(xⁿ, yⁿ)`,
which the relay does not know. Instead of the conditional typicality lemma, we use Markov's
inequality: a typical triple is good with high probability, and we look for a good sequence in the
codebook.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {X U Y S V : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype S] [Fintype V]
  {p : X → ℝ} {p₁ : U → ℝ} {W : X × U → Y × S → ℝ} {τ : U × S → V → ℝ} {n : ℕ}

/-- The law of `((X, X₁), (Y, Y₁), Ŷ₁)`. -/
def cfLaw (p : X → ℝ) (p₁ : U → ℝ) (W : X × U → Y × S → ℝ) (τ : U × S → V → ℝ) :
    ((X × U) × (Y × S)) × V → ℝ :=
  jointOf (jointOf (prodDist p p₁) W) fun t => τ (t.1.2, t.2.2)

omit [Fintype V] in
lemma cfLaw_isPMF [Fintype V] (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W)
    (hτ : IsChannel τ) : IsPMF (cfLaw p p₁ W τ) :=
  jointOf_isPMF (jointOf_isPMF (hp.prodDist hp₁) hW) fun _ => hτ _

/-- A sum over sequences of tuples is a sum over the sequences of the components. -/
lemma sum_cf_split (F : (Fin n → ((X × U) × (Y × S)) × V) → ℝ) :
    ∑ ω, F ω = ∑ u : Fin n → U, ∑ x : Fin n → X, ∑ ζ : (Fin n → Y) × (Fin n → S),
      ∑ v : Fin n → V, F fun i => (((x i, u i), (ζ.1 i, ζ.2 i)), v i) := by
  calc ∑ ω, F ω = ∑ t, ∑ v, F (zipSeq t v) := sum_zip F
    _ = ∑ a, ∑ o, ∑ v, F (zipSeq (zipSeq a o) v) := sum_zip fun t => ∑ v, F (zipSeq t v)
    _ = ∑ x, ∑ u, ∑ o, ∑ v, F (zipSeq (zipSeq (zipSeq x u) o) v) :=
        sum_zip fun a => ∑ o, ∑ v, F (zipSeq (zipSeq a o) v)
    _ = ∑ u, ∑ x, ∑ o, ∑ v, F (zipSeq (zipSeq (zipSeq x u) o) v) := sum_comm
    _ = _ := by
        refine sum_congr rfl fun u _ => sum_congr rfl fun x _ => ?_
        rw [sum_zip, Fintype.sum_prod_type]
        rfl

/-- **The sum over all the sequences of a block is an i.i.d. expectation.** -/
theorem sum_cf_all (G : (Fin n → X) → (Fin n → U) → (Fin n → Y) × (Fin n → S) → (Fin n → V) → ℝ) :
    ∑ u, iidPMF p₁ n u * ∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
      ∑ v, seqChan τ n (fun i => (u i, ζ.2 i)) v * G x u ζ v =
    ∑ ω, iidPMF (cfLaw p p₁ W τ) n ω * G (fun i => (ω i).1.1.1) (fun i => (ω i).1.1.2)
      (fun i => (ω i).1.2.1, fun i => (ω i).1.2.2) (fun i => (ω i).2) := by
  rw [sum_cf_split]
  simp only [mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun x _ => sum_congr rfl fun ζ _ =>
    sum_congr rfl fun v _ => ?_
  have h : iidPMF (cfLaw p p₁ W τ) n (fun i => (((x i, u i), (ζ.1 i, ζ.2 i)), v i)) =
      iidPMF p₁ n u * (iidPMF p n x * (relaySeq W n (x, u) ζ *
        seqChan τ n (fun i => (u i, ζ.2 i)) v)) := by
    simp only [iidPMF, seqChan, relaySeq, cfLaw, jointOf, prodDist, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by ring
  rw [h]
  ring

/-- The i.i.d. expectation of an indicator of an event that does not happen on typical sequences. -/
theorem sum_cf_le (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ) {ε : ℝ}
    (A : (Fin n → X) → (Fin n → U) → (Fin n → Y) × (Fin n → S) → (Fin n → V) → Prop)
    (hA : ∀ ω ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε, ¬ A (fun i => (ω i).1.1.1)
      (fun i => (ω i).1.1.2) (fun i => (ω i).1.2.1, fun i => (ω i).1.2.2) (fun i => (ω i).2)) :
    ∑ u, iidPMF p₁ n u * ∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
      ∑ v, seqChan τ n (fun i => (u i, ζ.2 i)) v * ind (A x u ζ v) ≤
    1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε) := by
  classical
  have hL := cfLaw_isPMF hp hp₁ hW hτ
  rw [sum_cf_all fun x u ζ v => ind (A x u ζ v), ← prob_compl (iidPMF_isPMF hL n), prob]
  rw [← sum_filter_add_sum_filter_not univ (· ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε)]
  have h₁ : ∑ ω ∈ univ.filter (· ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε),
      iidPMF (cfLaw p p₁ W τ) n ω * ind (A (fun i => (ω i).1.1.1) (fun i => (ω i).1.1.2)
        (fun i => (ω i).1.2.1, fun i => (ω i).1.2.2) (fun i => (ω i).2)) = 0 :=
    sum_eq_zero fun ω hω => by
      rw [ind_of_neg (hA ω (mem_filter.mp hω).2), mul_zero]
  rw [h₁, zero_add]
  have h₂ : ∑ ω ∈ univ.filter (fun ω => ¬ ω ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε),
      iidPMF (cfLaw p p₁ W τ) n ω * ind (A (fun i => (ω i).1.1.1) (fun i => (ω i).1.1.2)
        (fun i => (ω i).1.2.1, fun i => (ω i).1.2.2) (fun i => (ω i).2)) ≤
      ∑ ω ∈ univ.filter (fun ω => ¬ ω ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε),
        iidPMF (cfLaw p p₁ W τ) n ω := sum_le_sum fun ω _ => by
    have := mul_le_mul_of_nonneg_left (ind_le_one (A (fun i => (ω i).1.1.1) (fun i => (ω i).1.1.2)
        (fun i => (ω i).1.2.1, fun i => (ω i).1.2.2) (fun i => (ω i).2)))
      ((iidPMF_isPMF hL n).nonneg ω)
    linarith
  refine h₂.trans (le_of_eq ?_)
  refine sum_congr ?_ fun _ _ => rfl
  ext ω
  simp

/-! ### Good sequences -/

section Good

/-- The law of `y₁ⁿ`, given `x₁ⁿ`. -/
def cfRho (p : X → ℝ) (W : X × U → Y × S → ℝ) (u : Fin n → U) (s : Fin n → S) : ℝ :=
  ∑ x, iidPMF p n x * ∑ y, relaySeq W n (x, u) (y, s)

/-- The probability of `y₁ⁿ` and of the failure of the test `T`, given `x₁ⁿ`. -/
def cfBad (p : X → ℝ) (W : X × U → Y × S → ℝ)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop) (u : Fin n → U)
    (s : Fin n → S) (v : Fin n → V) : ℝ :=
  ∑ x, iidPMF p n x * ∑ y, relaySeq W n (x, u) (y, s) * ind (¬ T x u v y)

/-- **The good triples:** those that pass the test `Tj`, and such that the failure of the test `T`
has probability at most `δ`, given `(x₁ⁿ, y₁ⁿ)`. -/
def cfGood (p : X → ℝ) (W : X × U → Y × S → ℝ)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop)
    (Tj : (Fin n → U) → (Fin n → S) → (Fin n → V) → Prop) (δ : ℝ) (u : Fin n → U) (s : Fin n → S)
    (v : Fin n → V) : Prop :=
  Tj u s v ∧ cfBad p W T u s v ≤ δ * cfRho p W u s

omit [Fintype U] [Fintype S] [Fintype V] in
lemma cfRho_nonneg [Fintype S] (hp : IsPMF p) (hW : IsChannel W) (u : Fin n → U) (s : Fin n → S) :
    0 ≤ cfRho p W u s :=
  sum_nonneg fun x _ => mul_nonneg ((iidPMF_isPMF hp n).nonneg x) (sum_nonneg fun _ _ =>
    (relaySeq_isChannel hW n _).nonneg _)

omit [Fintype U] [Fintype V] in
/-- A sum against the law of `y₁ⁿ`. -/
lemma sum_cfRho (u : Fin n → U) (H : (Fin n → S) → ℝ) :
    ∑ s, cfRho p W u s * H s = ∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ * H ζ.2 := by
  simp only [cfRho, sum_mul, mul_sum, Fintype.sum_prod_type]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun s _ => ?_
  ring

omit [Fintype U] [Fintype V] in
lemma sum_cfRho_one (hp : IsPMF p) (hW : IsChannel W) (u : Fin n → U) :
    ∑ s, cfRho p W u s = 1 := by
  have h := sum_cfRho (p := p) (W := W) u fun _ => 1
  simp only [mul_one] at h
  rw [h]
  simp_rw [(relaySeq_isChannel hW n _).sum_eq_one, mul_one]
  exact (iidPMF_isPMF hp n).sum_eq_one

omit [Fintype U] [Fintype V] in
lemma cfBad_nonneg (hp : IsPMF p) (hW : IsChannel W)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop) (u : Fin n → U)
    (s : Fin n → S) (v : Fin n → V) : 0 ≤ cfBad p W T u s v :=
  sum_nonneg fun x _ => mul_nonneg ((iidPMF_isPMF hp n).nonneg x) (sum_nonneg fun _ _ =>
    mul_nonneg ((relaySeq_isChannel hW n _).nonneg _) (ind_nonneg _))

omit [Fintype U] [Fintype V] in
lemma cfBad_le_rho (hp : IsPMF p) (hW : IsChannel W)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop) (u : Fin n → U)
    (s : Fin n → S) (v : Fin n → V) : cfBad p W T u s v ≤ cfRho p W u s := by
  simp only [cfBad, cfRho]
  refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ((iidPMF_isPMF hp n).nonneg x)
  refine sum_le_sum fun y _ => ?_
  have := mul_le_mul_of_nonneg_left (ind_le_one (¬ T x u v y))
    ((relaySeq_isChannel hW n (x, u)).nonneg (y, s))
  linarith

open Classical in
/-- The index of a good sequence of a codebook. -/
def cfPick {K : ℕ} [NeZero K] {T : Type*} (G : T → Prop) (C : Fin K → T) : Fin K :=
  if h : ∃ k, G (C k) then Classical.choose h else 0

lemma cfPick_spec {K : ℕ} [NeZero K] {T : Type*} {G : T → Prop} {C : Fin K → T}
    (h : ∃ k, G (C k)) : G (C (cfPick G C)) := by
  simp only [cfPick, h, dite_true]
  exact Classical.choose_spec h

omit [Fintype U] in
/-- **The covering bound, for a fixed `x₁ⁿ`.** -/
theorem sum_cover_row {K : ℕ} [NeZero K] (hp : IsPMF p) (hW : IsChannel W) {q : U → V → ℝ}
    (hq : IsChannel q) (hτ : IsChannel τ)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop)
    (Tj : (Fin n → U) → (Fin n → S) → (Fin n → V) → Prop) {δ y : ℝ} (hδ : 0 ≤ δ) (hy1 : y ≤ 1)
    (u : Fin n → U)
    (hy : ∀ s v, cfGood p W T Tj δ u s v →
      seqChan τ n (fun i => (u i, s i)) v * y ≤ seqChan q n u v) :
    ∑ C : Fin K → Fin n → V, iidPMF (seqChan q n u) K C * (∑ x, iidPMF p n x *
      ∑ ζ, relaySeq W n (x, u) ζ *
        ind (¬ T x u (C (cfPick (cfGood p W T Tj δ u ζ.2) C)) ζ.1)) ≤
    δ + exp (-(y * K)) + ∑ s, cfRho p W u s *
      (1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (cfGood p W T Tj δ u s v)) := by
  classical
  set Good := cfGood p W T Tj δ u with hGood
  set P := seqChan q n u with hP
  have hPP : IsPMF P := seqChan_isChannel hq n u
  have hPK : IsPMF (iidPMF P K) := iidPMF_isPMF hPP K
  have hρ := cfRho_nonneg (n := n) hp hW u
  -- for a fixed codebook
  have h₁ : ∀ C : Fin K → Fin n → V, ∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
      ind (¬ T x u (C (cfPick (Good ζ.2) C)) ζ.1) =
      ∑ s, cfBad p W T u s (C (cfPick (Good s) C)) := by
    intro C
    simp only [cfBad, Fintype.sum_prod_type, mul_sum]
    symm
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    exact sum_comm
  have h₂ : ∀ (C : Fin K → Fin n → V) (s : Fin n → S), cfBad p W T u s (C (cfPick (Good s) C)) ≤
      cfRho p W u s * (δ + ∏ k, ind (¬ Good s (C k))) := by
    intro C s
    by_cases h : ∃ k, Good s (C k)
    · have hg := (cfPick_spec h).2
      have h0 : 0 ≤ ∏ k, ind (¬ Good s (C k)) := prod_nonneg fun k _ => ind_nonneg _
      nlinarith [hρ s]
    · have h1 : ∏ k, ind (¬ Good s (C k)) = 1 := prod_eq_one fun k _ =>
        ind_of_pos fun hk => h ⟨k, hk⟩
      rw [h1]
      have := cfBad_le_rho (V := V) hp hW T u s (C (cfPick (Good s) C))
      nlinarith [hρ s]
  have hm : ∀ s, ∑ C : Fin K → Fin n → V, iidPMF P K C * ∏ k, ind (¬ Good s (C k)) ≤
      1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (Good s v) + exp (-(y * K)) := fun s =>
    sum_miss_le hPP (seqChan_isChannel hτ n _) hy1 (fun v hv => hy s v hv) K
  calc _ ≤ ∑ C : Fin K → Fin n → V, iidPMF P K C *
        ∑ s, cfRho p W u s * (δ + ∏ k, ind (¬ Good s (C k))) := by
        refine sum_le_sum fun C _ => mul_le_mul_of_nonneg_left ?_ (hPK.nonneg C)
        rw [h₁]
        exact sum_le_sum fun s _ => h₂ C s
    _ = ∑ s, cfRho p W u s * (δ + ∑ C : Fin K → Fin n → V, iidPMF P K C *
        ∏ k, ind (¬ Good s (C k))) := by
        rw [sum_congr rfl fun C _ => mul_sum _ _ _, sum_comm]
        refine sum_congr rfl fun s _ => ?_
        have hc : ∀ C : Fin K → Fin n → V, iidPMF P K C * (cfRho p W u s *
            (δ + ∏ k, ind (¬ Good s (C k)))) = cfRho p W u s * (δ * iidPMF P K C +
              iidPMF P K C * ∏ k, ind (¬ Good s (C k))) := fun C => by ring
        simp_rw [hc, ← mul_sum, sum_add_distrib, ← mul_sum, hPK.sum_eq_one, mul_one]
    _ ≤ ∑ s, cfRho p W u s * (δ + (1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (Good s v) +
        exp (-(y * K)))) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (by linarith [hm s]) (hρ s)
    _ = _ := by
        have hs := sum_cfRho_one (p := p) (W := W) hp hW (n := n) u
        simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul, hs, mul_one]
        ring

omit [Fintype U] in
/-- A sum over the description of the probability of failure of the test. -/
lemma sum_cfBad (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop) (u : Fin n → U) :
    ∑ s, ∑ v, seqChan τ n (fun i => (u i, s i)) v * cfBad p W T u s v =
      ∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
        ∑ v, seqChan τ n (fun i => (u i, ζ.2 i)) v * ind (¬ T x u v ζ.1) := by
  simp only [cfBad, Fintype.sum_prod_type, mul_sum]
  have h₁ : ∀ s : Fin n → S, ∑ v, ∑ x, ∑ y, seqChan τ n (fun i => (u i, s i)) v *
      (iidPMF p n x * (relaySeq W n (x, u) (y, s) * ind (¬ T x u v y))) =
      ∑ x, ∑ y, ∑ v, iidPMF p n x * (relaySeq W n (x, u) (y, s) *
        (seqChan τ n (fun i => (u i, s i)) v * ind (¬ T x u v y))) := by
    intro s
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y _ => sum_congr rfl fun v _ => ?_
    ring
  simp_rw [h₁]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]

/-- **The probability that a sequence of the true law is not good.** -/
theorem sum_cover_outer (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W) (hτ : IsChannel τ)
    {ε δ : ℝ} (hδ : 0 < δ) (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop)
    (Tj : (Fin n → U) → (Fin n → S) → (Fin n → V) → Prop)
    (hT : ∀ ω ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε, T (fun i => (ω i).1.1.1)
      (fun i => (ω i).1.1.2) (fun i => (ω i).2) (fun i => (ω i).1.2.1))
    (hTj : ∀ ω ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε, Tj (fun i => (ω i).1.1.2)
      (fun i => (ω i).1.2.2) (fun i => (ω i).2)) :
    ∑ u, iidPMF p₁ n u * ∑ s, cfRho p W u s *
      (1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (cfGood p W T Tj δ u s v)) ≤
    (1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε)) +
      (1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε)) / δ := by
  classical
  have hρ := cfRho_nonneg (n := n) hp hW
  have hup := iidPMF_isPMF hp₁ n
  have hτs : ∀ (u : Fin n → U) (s : Fin n → S), IsPMF (seqChan τ n fun i => (u i, s i)) :=
    fun u s =>
    seqChan_isChannel hτ n (fun i => ((u i, s i) : U × S))
  -- for a fixed pair
  have h₁ : ∀ (u : Fin n → U) (s : Fin n → S), cfRho p W u s *
      (1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (cfGood p W T Tj δ u s v)) ≤
      cfRho p W u s * (∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (¬ Tj u s v)) +
        (∑ v, seqChan τ n (fun i => (u i, s i)) v * cfBad p W T u s v) / δ := by
    intro u s
    have hsum := (hτs u s).sum_eq_one
    have hE : 1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (cfGood p W T Tj δ u s v) =
        ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (¬ cfGood p W T Tj δ u s v) := by
      rw [sub_eq_iff_eq_add, ← sum_add_distrib, ← hsum]
      refine sum_congr rfl fun v _ => ?_
      by_cases h : cfGood p W T Tj δ u s v
      · rw [ind_of_neg (not_not.mpr h), ind_of_pos h]
        ring
      · rw [ind_of_pos h, ind_of_neg h]
        ring
    rw [hE, mul_sum, mul_sum, sum_div, ← sum_add_distrib]
    refine sum_le_sum fun v _ => ?_
    have hc0 := (hτs u s).nonneg v
    have hpt : cfRho p W u s * ind (¬ cfGood p W T Tj δ u s v) ≤
        cfRho p W u s * ind (¬ Tj u s v) + cfBad p W T u s v / δ := by
      have hb0 := cfBad_nonneg hp hW T u s v
      have hb1 : 0 ≤ cfBad p W T u s v / δ := div_nonneg hb0 hδ.le
      by_cases h : cfGood p W T Tj δ u s v
      · rw [ind_of_neg (not_not.mpr h), mul_zero]
        have := mul_nonneg (hρ u s) (ind_nonneg (¬ Tj u s v))
        linarith
      · rw [ind_of_pos h, mul_one]
        by_cases hj : Tj u s v
        · have hlt : δ * cfRho p W u s < cfBad p W T u s v := by
            by_contra hc
            exact h ⟨hj, not_lt.mp hc⟩
          rw [ind_of_neg (not_not.mpr hj), mul_zero, zero_add, le_div_iff₀ hδ]
          linarith
        · rw [ind_of_pos hj, mul_one]
          linarith
    calc _ ≤ seqChan τ n (fun i => (u i, s i)) v * (cfRho p W u s * ind (¬ Tj u s v) +
          cfBad p W T u s v / δ) := by
          rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left hpt hc0
      _ = _ := by ring
  have h₂ := sum_cf_le (V := V) (S := S) (Y := Y) hp hp₁ hW hτ (ε := ε) (n := n)
    (fun x u ζ v => ¬ Tj u ζ.2 v) (fun ω hω => not_not.mpr (hTj ω hω))
  have h₃ := sum_cf_le (V := V) (S := S) (Y := Y) hp hp₁ hW hτ (ε := ε) (n := n)
    (fun x u ζ v => ¬ T x u v ζ.1) (fun ω hω => not_not.mpr (hT ω hω))
  calc _ ≤ ∑ u, iidPMF p₁ n u * (∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
        ∑ v, seqChan τ n (fun i => (u i, ζ.2 i)) v * ind (¬ Tj u ζ.2 v) +
        (∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
          ∑ v, seqChan τ n (fun i => (u i, ζ.2 i)) v * ind (¬ T x u v ζ.1)) / δ) := by
        refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hup.nonneg u)
        refine (sum_le_sum fun s _ => h₁ u s).trans (le_of_eq ?_)
        rw [sum_add_distrib, sum_cfRho, ← sum_div, sum_cfBad]
    _ = (∑ u, iidPMF p₁ n u * ∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
          ∑ v, seqChan τ n (fun i => (u i, ζ.2 i)) v * ind (¬ Tj u ζ.2 v)) +
        (∑ u, iidPMF p₁ n u * ∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
          ∑ v, seqChan τ n (fun i => (u i, ζ.2 i)) v * ind (¬ T x u v ζ.1)) / δ := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        rw [sum_div]
        exact sum_congr rfl fun u _ => mul_div_assoc _ _ _ |>.symm
    _ ≤ _ := add_le_add h₂ (div_le_div_of_nonneg_right h₃ hδ.le)

/-- **The covering bound.** Let `(x₁ⁿ, ŷ₁ⁿ(·))` be drawn at random and let `(xⁿ, yⁿ, y₁ⁿ)` be
generated from `x₁ⁿ`. Let `ŷ₁ⁿ(K)` be a good sequence of the codebook for `(x₁ⁿ, y₁ⁿ)`. Then the
test `T` fails with probability at most `δ`, plus the probability of the atypical i.i.d. sequences,
plus the probability that no sequence of the codebook is good. -/
theorem sum_cover_le {K : ℕ} [NeZero K] (hp : IsPMF p) (hp₁ : IsPMF p₁) (hW : IsChannel W)
    {q : U → V → ℝ} (hq : IsChannel q) (hτ : IsChannel τ) {ε δ y : ℝ} (hδ : 0 < δ) (hy1 : y ≤ 1)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop)
    (Tj : (Fin n → U) → (Fin n → S) → (Fin n → V) → Prop)
    (hT : ∀ ω ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε, T (fun i => (ω i).1.1.1)
      (fun i => (ω i).1.1.2) (fun i => (ω i).2) (fun i => (ω i).1.2.1))
    (hTj : ∀ ω ∈ robustTypicalSet (cfLaw p p₁ W τ) n ε, Tj (fun i => (ω i).1.1.2)
      (fun i => (ω i).1.2.2) (fun i => (ω i).2))
    (hy : ∀ u s v, Tj u s v → seqChan τ n (fun i => (u i, s i)) v * y ≤ seqChan q n u v) :
    ∑ u, iidPMF p₁ n u * ∑ C : Fin K → Fin n → V, iidPMF (seqChan q n u) K C *
      (∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
        ind (¬ T x u (C (cfPick (cfGood p W T Tj δ u ζ.2) C)) ζ.1)) ≤
    δ + exp (-(y * K)) +
      ((1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε)) +
      (1 - prob (iidPMF (cfLaw p p₁ W τ) n) (robustTypicalSet (cfLaw p p₁ W τ) n ε)) / δ) := by
  have hup := iidPMF_isPMF hp₁ n
  have hout := sum_cover_outer (V := V) (S := S) (Y := Y) hp hp₁ hW hτ (ε := ε) hδ T Tj hT hTj
  calc _ ≤ ∑ u, iidPMF p₁ n u * (δ + exp (-(y * K)) + ∑ s, cfRho p W u s *
        (1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (cfGood p W T Tj δ u s v))) :=
        sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (sum_cover_row hp hW hq hτ T Tj hδ.le hy1 u
          fun s v hv => hy u s v hv.1) (hup.nonneg u)
    _ = δ + exp (-(y * K)) + ∑ u, iidPMF p₁ n u * ∑ s, cfRho p W u s *
        (1 - ∑ v, seqChan τ n (fun i => (u i, s i)) v * ind (cfGood p W T Tj δ u s v)) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hup.sum_eq_one, one_mul]
    _ ≤ _ := add_le_add le_rfl hout

end Good

end InfoTheory
