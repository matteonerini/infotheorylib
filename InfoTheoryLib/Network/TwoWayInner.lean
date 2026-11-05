/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCSuperposition
public import InfoTheoryLib.Network.RelayCFRandom
public import InfoTheoryLib.Network.RelayCFRate
public import InfoTheoryLib.Network.TwoWayCode

/-!
# Shannon's inner bound for the two-way channel

Page 18-48 of the notes: the rate pairs with `R₁ < I(X₁; Y₂ | X₂, Q)` and `R₂ < I(X₂; Y₁ | X₁, Q)`
for some `p(q) p(x₁ | q) p(x₂ | q)` are achievable, by encoders that ignore the received outputs.

## Main definitions

* `twLaw`: the law of `((Q, X₁, X₂), (Y₁, Y₂))`.

## Main statements

* `sum_row_le`: the random coding bound for one decoder.
* `isAchievableTWC_of_lt`: **Shannon's inner bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The random coding bound for one decoder -/

section Row

variable {Qs A B Z : Type*} [Fintype Qs] [Fintype A] [Fintype B] [Fintype Z] {pq : Qs → ℝ}
  {Pa : Qs → A → ℝ} {Pb : Qs → B → ℝ} {V : A × B → Z → ℝ} {T : Qs → A → B → Z → Prop}

/-- **The random coding bound for one decoder.** The tables `(ta, tb)` are drawn given the sequence
`q`, and the decoder finds the unique index `i` that passes the test. -/
theorem sum_row_le {Ma Mb : ℕ} (hq : IsPMF pq) (hPa : IsChannel Pa) (hPb : IsChannel Pb)
    (hV : IsChannel V) {c e : ℝ}
    (hc : ∑ q, pq q * ∑ a, Pa q a * ∑ b, Pb q b * ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ) ≤ c)
    (he : ∀ q b ζ, ∑ a, Pa q a * ind (T q a b ζ) ≤ e) (i : Fin Ma) (j : Fin Mb) (d : Fin Ma) :
    ∑ q, pq q * ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta * ∑ tb : Fin Mb → B,
      piLaw (fun _ => Pb q) tb * ∑ ζ, V (ta i, tb j) ζ *
        ind (cfUniq (fun i' => T q (ta i') (tb j) ζ) d ≠ i) ≤ c + ((Ma : ℝ) - 1) * e := by
  classical
  have hνa : ∀ q, ∀ _ : Fin Ma, IsPMF (Pa q) := fun q _ => hPa q
  have hνb : ∀ q, ∀ _ : Fin Mb, IsPMF (Pb q) := fun q _ => hPb q
  have hta : ∀ q, IsPMF (piLaw fun _ : Fin Ma => Pa q) := fun q => piLaw_isPMF (hνa q)
  have htb : ∀ q, IsPMF (piLaw fun _ : Fin Mb => Pb q) := fun q => piLaw_isPMF (hνb q)
  -- for a fixed sequence `q` and a fixed entry of the second table
  have hfix : ∀ (q : Qs) (b : B), ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta *
      ∑ ζ, V (ta i, b) ζ * ind (cfUniq (fun i' => T q (ta i') b ζ) d ≠ i) ≤
      ∑ a, Pa q a * ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ) + ((Ma : ℝ) - 1) * e := by
    intro q b
    have hpt : ∀ ta : Fin Ma → A, ∑ ζ, V (ta i, b) ζ * ind (cfUniq (fun i' => T q (ta i') b ζ) d ≠
      i) ≤
        ∑ ζ, V (ta i, b) ζ * ind (¬ T q (ta i) b ζ) +
          ∑ i' ∈ univ.filter (· ≠ i), ∑ ζ, V (ta i, b) ζ * ind (T q (ta i') b ζ) := by
      intro ta
      rw [sum_comm, ← sum_add_distrib]
      refine sum_le_sum fun ζ _ => ?_
      rw [← mul_sum, ← mul_add]
      exact mul_le_mul_of_nonneg_left (ind_cfUniq_ne_le _ _ _) ((hV _).nonneg _)
    have hwrong : ∀ i' ∈ univ.filter (· ≠ i), ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta *
        ∑ ζ, V (ta i, b) ζ * ind (T q (ta i') b ζ) ≤ e := by
      intro i' hi'
      have hne : i ≠ i' := fun h => (mem_filter.mp hi').2 h.symm
      rw [sum_piLaw_mul_eval₂ (ν := fun _ : Fin Ma => Pa q) (hνa q) hne
        fun a a' => ∑ ζ, V (a, b) ζ * ind (T q a' b ζ)]
      have hin : ∀ a, ∑ a', Pa q a * Pa q a' * ∑ ζ, V (a, b) ζ * ind (T q a' b ζ) ≤ Pa q a * e := by
        intro a
        have hf : ∑ a', Pa q a * Pa q a' * ∑ ζ, V (a, b) ζ * ind (T q a' b ζ) =
            Pa q a * ∑ ζ, V (a, b) ζ * ∑ a', Pa q a' * ind (T q a' b ζ) := by
          simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun ζ _ => sum_congr rfl fun a' _ => ?_
          ring
        rw [hf]
        refine mul_le_mul_of_nonneg_left ?_ ((hPa q).nonneg a)
        calc _ ≤ ∑ ζ, V (a, b) ζ * e := sum_le_sum fun ζ _ =>
              mul_le_mul_of_nonneg_left (he q b ζ) ((hV _).nonneg _)
          _ = e := by rw [← sum_mul, (hV _).sum_eq_one, one_mul]
      calc _ ≤ ∑ a, Pa q a * e := sum_le_sum fun a _ => hin a
        _ = e := by rw [← sum_mul, (hPa q).sum_eq_one, one_mul]
    have hcard : ((univ.filter (· ≠ i) : Finset (Fin Ma)).card : ℝ) = (Ma : ℝ) - 1 := by
      have : 0 < Ma := Fin.pos i
      rw [filter_ne', card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
        Nat.cast_sub this]
      simp
    calc _ ≤ ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta *
          (∑ ζ, V (ta i, b) ζ * ind (¬ T q (ta i) b ζ) + ∑ i' ∈ univ.filter (· ≠ i),
            ∑ ζ, V (ta i, b) ζ * ind (T q (ta i') b ζ)) :=
          sum_le_sum fun ta _ => mul_le_mul_of_nonneg_left (hpt ta) ((hta q).nonneg ta)
      _ = ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta * ∑ ζ, V (ta i, b) ζ * ind (¬ T q (ta i) b ζ)
        +
          ∑ i' ∈ univ.filter (· ≠ i), ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta *
            ∑ ζ, V (ta i, b) ζ * ind (T q (ta i') b ζ) := by
          simp only [mul_add, sum_add_distrib]
          congr 1
          simp only [mul_sum]
          rw [sum_comm]
      _ ≤ _ := by
          refine add_le_add (le_of_eq ?_) ?_
          · exact sum_piLaw_mul_eval (ν := fun _ : Fin Ma => Pa q) (hνa q) i
              fun a => ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ)
          · refine (sum_le_sum hwrong).trans (le_of_eq ?_)
            rw [sum_const, nsmul_eq_mul, hcard]
  -- the average over the second table
  have hb : ∀ q, ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta * ∑ tb : Fin Mb → B,
      piLaw (fun _ => Pb q) tb * ∑ ζ, V (ta i, tb j) ζ *
        ind (cfUniq (fun i' => T q (ta i') (tb j) ζ) d ≠ i) ≤
      ∑ a, Pa q a * ∑ b, Pb q b * ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ) + ((Ma : ℝ) - 1) * e := by
    intro q
    have hswap : ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta * ∑ tb : Fin Mb → B,
        piLaw (fun _ => Pb q) tb * ∑ ζ, V (ta i, tb j) ζ *
          ind (cfUniq (fun i' => T q (ta i') (tb j) ζ) d ≠ i) =
        ∑ tb : Fin Mb → B, piLaw (fun _ => Pb q) tb * ∑ ta : Fin Ma → A,
          piLaw (fun _ => Pa q) ta * ∑ ζ, V (ta i, tb j) ζ *
            ind (cfUniq (fun i' => T q (ta i') (tb j) ζ) d ≠ i) := sum_inner_swap _ _ _
    rw [hswap]
    rw [sum_piLaw_mul_eval (ν := fun _ : Fin Mb => Pb q) (hνb q) j fun b =>
      ∑ ta : Fin Ma → A, piLaw (fun _ => Pa q) ta * ∑ ζ, V (ta i, b) ζ *
        ind (cfUniq (fun i' => T q (ta i') b ζ) d ≠ i)]
    calc _ ≤ ∑ b, Pb q b * (∑ a, Pa q a * ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ) +
          ((Ma : ℝ) - 1) * e) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hfix q b) ((hPb q).nonneg b)
      _ = ∑ b, Pb q b * ∑ a, Pa q a * ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ) +
          ((Ma : ℝ) - 1) * e := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, (hPb q).sum_eq_one, one_mul]
      _ = _ := by
          rw [sum_inner_swap]
  calc _ ≤ ∑ q, pq q * (∑ a, Pa q a * ∑ b, Pb q b * ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ) +
        ((Ma : ℝ) - 1) * e) := sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hb q) (hq.nonneg q)
    _ = ∑ q, pq q * ∑ a, Pa q a * ∑ b, Pb q b * ∑ ζ, V (a, b) ζ * ind (¬ T q a b ζ) +
        ((Ma : ℝ) - 1) * e := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hq.sum_eq_one, one_mul]
    _ ≤ _ := add_le_add hc le_rfl

end Row

/-! ### The code of two tables -/

section Tables

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
  [Nonempty X₁] [Nonempty X₂] {W : X₁ × X₂ → Y₁ × Y₂ → ℝ} {M₁ M₂ n : ℕ}

/-- The code of two tables. The encoders ignore the outputs. -/
def twCode [NeZero M₁] [NeZero M₂] (T₁ : (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₁) → Prop)
    (T₂ : (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₂) → Prop) (t₁ : Fin M₁ → Fin n → X₁)
    (t₂ : Fin M₂ → Fin n → X₂) : TWCCode M₁ M₂ n X₁ X₂ Y₁ Y₂ where
  enc₁ k m _ := if h : k < n then t₁ m ⟨k, h⟩ else Classical.arbitrary X₁
  enc₂ k m _ := if h : k < n then t₂ m ⟨k, h⟩ else Classical.arbitrary X₂
  dec₁ m y := cfUniq (fun m' => T₁ (t₁ m) (t₂ m') y) 0
  dec₂ m y := cfUniq (fun m' => T₂ (t₁ m') (t₂ m) y) 0

variable [NeZero M₁] [NeZero M₂] {T₁ : (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₁) → Prop}
  {T₂ : (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₂) → Prop} {t₁ : Fin M₁ → Fin n → X₁}
  {t₂ : Fin M₂ → Fin n → X₂}

/-- A sum over the outputs of all the times is a sum over the outputs of each node. -/
lemma sum_pair_seq (F : (Fin n → Y₁) × (Fin n → Y₂) → ℝ) :
    ∑ z : Fin n → Y₁ × Y₂, F (fun i => (z i).1, fun i => (z i).2) = ∑ ζ, F ζ :=
  (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Y₁) (fun _ => Y₂)).sum_comp F

omit [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂] in
lemma twCode_fbLaw (w : Fin M₁ × Fin M₂) (z : Fin n → Y₁ × Y₂) :
    (twCode T₁ T₂ t₁ t₂).law W Prod.fst Prod.snd (w, z) =
      1 / ((M₁ : ℝ) * M₂) * relaySeq W n (t₁ w.1, t₂ w.2) (fun i => (z i).1, fun i => (z i).2) := by
  rw [TWCCode.law, fbLaw_eq_prod]
  congr 1
  · simp [uniformPMF]
  · simp only [relaySeq]
    refine prod_congr rfl fun i _ => ?_
    simp [TWCCode.fbEnc, twCode]

omit [Fintype X₁] [Fintype X₂] in
/-- The probability of error of node 2. -/
lemma twCode_err₂ :
    (twCode T₁ T₂ t₁ t₂).err₂ W Prod.fst Prod.snd = (1 / ((M₁ : ℝ) * M₂)) *
      ∑ i : Fin M₁ × Fin M₂, ∑ ζ, relaySeq W n (t₁ i.1, t₂ i.2) ζ *
        ind (cfUniq (fun m' => T₂ (t₁ m') (t₂ i.2) ζ.2) 0 ≠ i.1) := by
  classical
  simp only [TWCCode.err₂, InfoTheory.errProb]
  rw [Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [← sum_pair_seq, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [twCode_fbLaw]
  by_cases h : cfUniq (fun m' => T₂ (t₁ m') (t₂ w.2) fun i => (z i).2) 0 ≠ w.1
  · rw [ind_of_pos h]
    simp only [twCode]
    exact (ite_eq_left h).trans (by ring)
  · rw [ind_of_neg h]
    simp only [twCode]
    exact (ite_eq_right h).trans (by ring)

omit [Fintype X₁] [Fintype X₂] in
/-- The probability of error of node 1. -/
lemma twCode_err₁ :
    (twCode T₁ T₂ t₁ t₂).err₁ W Prod.fst Prod.snd = (1 / ((M₁ : ℝ) * M₂)) *
      ∑ i : Fin M₁ × Fin M₂, ∑ ζ, relaySeq W n (t₁ i.1, t₂ i.2) ζ *
        ind (cfUniq (fun m' => T₁ (t₁ i.1) (t₂ m') ζ.1) 0 ≠ i.2) := by
  classical
  simp only [TWCCode.err₁, InfoTheory.errProb]
  rw [Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [← sum_pair_seq, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [twCode_fbLaw]
  by_cases h : cfUniq (fun m' => T₁ (t₁ w.1) (t₂ m') fun i => (z i).1) 0 ≠ w.2
  · rw [ind_of_pos h]
    simp only [twCode]
    exact (ite_eq_left h).trans (by ring)
  · rw [ind_of_neg h]
    simp only [twCode]
    exact (ite_eq_right h).trans (by ring)

end Tables

section Exists

variable {Q X₁ X₂ Y₁ Y₂ : Type*} [Fintype Q] [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
  [Nonempty X₁] [Nonempty X₂] {W : X₁ × X₂ → Y₁ × Y₂ → ℝ} {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂]
  {pq : Q → ℝ} {A : Q → X₁ → ℝ} {B : Q → X₂ → ℝ}
  {T₁ : (Fin n → Q) → (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₁) → Prop}
  {T₂ : (Fin n → Q) → (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₂) → Prop}

/-- **The random coding bound for the two-way channel.** -/
theorem exists_twCode_le (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W)
    {c₁ c₂ e₁ e₂ : ℝ}
    (hc₂ : ∑ q, iidPMF pq n q * ∑ a, seqChan A n q a * ∑ b, seqChan B n q b *
      ∑ ζ, relaySeq W n (a, b) ζ * ind (¬ T₂ q a b ζ.2) ≤ c₂)
    (he₂ : ∀ q b y, ∑ a, seqChan A n q a * ind (T₂ q a b y) ≤ e₂)
    (hc₁ : ∑ q, iidPMF pq n q * ∑ a, seqChan A n q a * ∑ b, seqChan B n q b *
      ∑ ζ, relaySeq W n (a, b) ζ * ind (¬ T₁ q a b ζ.1) ≤ c₁)
    (he₁ : ∀ q a y, ∑ b, seqChan B n q b * ind (T₁ q a b y) ≤ e₁) :
    ∃ c : TWCCode M₁ M₂ n X₁ X₂ Y₁ Y₂, c.errProb W ≤
      c₁ + ((M₂ : ℝ) - 1) * e₁ + (c₂ + ((M₁ : ℝ) - 1) * e₂) := by
  classical
  have hqn := iidPMF_isPMF hq n
  have hAs := seqChan_isChannel hA n
  have hBs := seqChan_isChannel hB n
  have hV := relaySeq_isChannel hW n
  have h₁ : (0 : ℝ) < M₁ := by exact_mod_cast NeZero.pos M₁
  have h₂ : (0 : ℝ) < M₂ := by exact_mod_cast NeZero.pos M₂
  have hM : (0 : ℝ) < (M₁ : ℝ) * M₂ := by positivity
  have hνa : ∀ q, IsPMF (piLaw fun _ : Fin M₁ => seqChan A n q) := fun q =>
    piLaw_isPMF fun _ => hAs q
  have hνb : ∀ q, IsPMF (piLaw fun _ : Fin M₂ => seqChan B n q) := fun q =>
    piLaw_isPMF fun _ => hBs q
  let err : (Fin n → Q) → (Fin M₁ → Fin n → X₁) → (Fin M₂ → Fin n → X₂) → ℝ := fun q t₁ t₂ =>
    (twCode (T₁ q) (T₂ q) t₁ t₂ : TWCCode M₁ M₂ n X₁ X₂ Y₁ Y₂).errProb W
  -- node 2
  have hbound₂ : ∑ q, iidPMF pq n q * ∑ t₁ : Fin M₁ → Fin n → X₁,
      piLaw (fun _ => seqChan A n q) t₁ * ∑ t₂ : Fin M₂ → Fin n → X₂,
        piLaw (fun _ => seqChan B n q) t₂ *
          (twCode (T₁ q) (T₂ q) t₁ t₂ : TWCCode M₁ M₂ n X₁ X₂ Y₁ Y₂).err₂ W Prod.fst Prod.snd ≤
      c₂ + ((M₁ : ℝ) - 1) * e₂ := by
    simp_rw [twCode_err₂, sum_mul_const_sum]
    refine (mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => sum_row_le (pq := iidPMF pq n)
      (Pa := seqChan A n) (Pb := seqChan B n) (V := relaySeq W n)
      (T := fun q a b ζ => T₂ q a b ζ.2) hqn hAs hBs hV hc₂ (fun q b ζ => he₂ q b ζ.2) i.1 i.2 0)
      (by positivity)).trans (le_of_eq ?_)
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  -- node 1
  have hbound₁ : ∑ q, iidPMF pq n q * ∑ t₁ : Fin M₁ → Fin n → X₁,
      piLaw (fun _ => seqChan A n q) t₁ * ∑ t₂ : Fin M₂ → Fin n → X₂,
        piLaw (fun _ => seqChan B n q) t₂ *
          (twCode (T₁ q) (T₂ q) t₁ t₂ : TWCCode M₁ M₂ n X₁ X₂ Y₁ Y₂).err₁ W Prod.fst Prod.snd ≤
      c₁ + ((M₂ : ℝ) - 1) * e₁ := by
    simp_rw [twCode_err₁, sum_mul_const_sum]
    have hV' : IsChannel fun t : (Fin n → X₂) × (Fin n → X₁) => relaySeq W n (t.2, t.1) :=
      fun t => hV _
    have hrow := fun i : Fin M₁ × Fin M₂ => sum_row_le (pq := iidPMF pq n)
      (Pa := seqChan B n) (Pb := seqChan A n) (V := fun t => relaySeq W n (t.2, t.1))
      (T := fun q b a ζ => T₁ q a b ζ.1) hqn hBs hAs hV'
      (by
        refine le_trans (le_of_eq ?_) hc₁
        refine sum_congr rfl fun q _ => congrArg _ ?_
        exact sum_inner_swap _ _ _)
      (fun q a ζ => he₁ q a ζ.1) i.2 i.1 0
    refine (mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => le_trans (le_of_eq ?_) (hrow i))
      (by positivity)).trans (le_of_eq ?_)
    · refine sum_congr rfl fun q _ => congrArg _ ?_
      exact sum_inner_swap _ _ _
    · simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
  have htot : ∑ q, iidPMF pq n q * ∑ t₁ : Fin M₁ → Fin n → X₁,
      piLaw (fun _ => seqChan A n q) t₁ * ∑ t₂ : Fin M₂ → Fin n → X₂,
        piLaw (fun _ => seqChan B n q) t₂ * err q t₁ t₂ ≤
      c₁ + ((M₂ : ℝ) - 1) * e₁ + (c₂ + ((M₁ : ℝ) - 1) * e₂) := by
    simp only [err, TWCCode.errProb, mul_add, sum_add_distrib]
    exact add_le_add hbound₁ hbound₂
  obtain ⟨q, h₁⟩ := exists_le_of_sum_mul_le hqn htot
  obtain ⟨t₁, h₂⟩ := exists_le_of_sum_mul_le (hνa q) h₁
  obtain ⟨t₂, h₃⟩ := exists_le_of_sum_mul_le (hνb q) h₂
  exact ⟨_, h₃⟩

end Exists

/-! ### The gap of a fresh sequence -/

section Gap

variable {Ω R Q F C Y : Type*} [Fintype Ω] [Fintype R] [Fintype Q] [Fintype F] [Fintype C]
  [Fintype Y] {μ : Ω → ℝ}

/-- `I(X; R | Q)` for a function `Q` of `R`, in terms of entropies. -/
def twGap (μ : Ω → ℝ) (r : Ω → R) (q : Ω → Q) (x : Ω → F) : ℝ :=
  H[r ; μ] + H[pair q x ; μ] - H[q ; μ] - H[pair r x ; μ]

/-- The correction to `twGap`. -/
def twErr (μ : Ω → ℝ) (r : Ω → R) (q : Ω → Q) (x : Ω → F) : ℝ :=
  H[pair r x ; μ] + H[r ; μ] + H[pair q x ; μ] + H[q ; μ]

lemma twErr_nonneg (hμ : IsPMF μ) (r : Ω → R) (q : Ω → Q) (x : Ω → F) : 0 ≤ twErr μ r q x := by
  have h₁ := entropyRV_nonneg hμ (pair r x)
  have h₂ := entropyRV_nonneg hμ r
  have h₃ := entropyRV_nonneg hμ (pair q x)
  have h₄ := entropyRV_nonneg hμ q
  simp only [twErr]
  linarith

/-- The probability that a fresh sequence is jointly typical with a fixed sequence. -/
theorem sum_fresh_tw (hμ : IsPMF μ) {r : Ω → R} {q : Ω → Q} {x : Ω → F} (k : R → Q)
    (hk : ∀ ω, k (r ω) = q ω) {κ : Q → F → ℝ}
    (hκ : ∀ a t, dist μ (pair q x) (a, t) = dist μ q a * κ a t) (hκc : IsChannel κ) {n : ℕ} {ε : ℝ}
    (s : Fin n → R) :
    ∑ a, seqChan κ n (fun i => k (s i)) a *
        ind ((fun i => (s i, a i)) ∈ robustTypicalSet (dist μ (pair r x)) n ε) ≤
      exp (-(n * (twGap μ r q x - twErr μ r q x * ε))) := by
  classical
  have e₁ : (fun z : R × F => (k z.1, z.2)) ∘ pair r x = pair q x := by
    funext ω
    simp [pair, hk]
  have e₂ : (fun z : R × F => k z.1) ∘ pair r x = q := funext hk
  have e₃ : dist (dist μ (pair r x)) (fun z : R × F => (k z.1, z.2)) = dist μ (pair q x) := by
    rw [← dist_dist_comp, e₁]
  have e₄ : dist (dist μ (pair r x)) (fun z : R × F => k z.1) = dist μ q := by
    rw [← dist_dist_comp, e₂]
  have h := sum_fresh_point (hμ.dist (pair r x)) k (κ := κ)
    (fun a t => by rw [e₃, e₄]; exact hκ a t) hκc (n := n) (ε := ε)
    (fun s t => (fun i => (s i, t i)) ∈ robustTypicalSet (dist μ (pair r x)) n ε)
    (fun _ _ h => h) s
  refine h.trans (le_of_eq ?_)
  have h₁ : H[Prod.fst ; dist μ (pair r x)] = H[r ; μ] := entropyRV_dist _ _ _
  have h₂ : H[fun z : R × F => (k z.1, z.2) ; dist μ (pair r x)] = H[pair q x ; μ] := by
    rw [entropyRV_dist, e₁]
  have h₃ : H[fun z : R × F => k z.1 ; dist μ (pair r x)] = H[q ; μ] := by
    rw [entropyRV_dist, e₂]
  have h₄ : entropy (dist μ (pair r x)) = H[pair r x ; μ] := rfl
  rw [h₁, h₂, h₃, h₄, twGap, twErr]
  congr 2
  ring

/-- The product form of the law of the inputs: the fresh input is independent of the other one
given the time sharing. -/
lemma tw_cond (hμ : IsPMF μ) {q : Ω → Q} {c : Ω → C} {x : Ω → F} {pq : Q → ℝ} {B : Q → C → ℝ}
    {A : Q → F → ℝ} (hA : IsChannel A) (hB : IsChannel B)
    (H : dist μ (pair (pair q c) x) = jointOf (jointOf pq B) fun v => A v.1) :
    (∀ k t, dist μ (pair q x) (k, t) = dist μ q k * A k t) ∧
      H[x | pair q c ; μ] = H[x | q ; μ] := by
  have hc : dist μ (pair q c) = jointOf pq B := by
    have h := dist_jointOf_fst (p := jointOf pq B) (W := fun v : Q × C => A v.1) fun _ => hA _
    rw [← H, ← dist_dist_comp] at h
    exact h
  have hqd : dist μ q = pq := by
    have h := dist_jointOf_fst (p := pq) (W := B) hB
    rw [← hc, ← dist_dist_comp] at h
    exact h
  have hx : dist μ (pair q x) = jointOf pq A := by
    have h := dist_jointOf_map (Q := jointOf pq B) (Prod.fst : Q × C → Q) A
    rw [← H, ← dist_dist_comp, dist_jointOf_fst hB] at h
    exact h
  refine ⟨fun k t => ?_, ?_⟩
  · rw [hx, hqd]
    rfl
  · refine condEntropy_eq_comp_of_channel hμ (pair q c) x Prod.fst hA ?_
    rw [H, hc]

/-- The conditional entropy of the fresh input given the time sharing. -/
lemma tw_condEntropy (hμ : IsPMF μ) {q : Ω → Q} {c : Ω → C} {x : Ω → F} {pq : Q → ℝ}
    {B : Q → C → ℝ} {A : Q → F → ℝ} (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B)
    (H : dist μ (pair (pair q c) x) = jointOf (jointOf pq B) fun v => A v.1) :
    H[x | q ; μ] = ∑ k, pq k * entropy (A k) := by
  have hc : dist μ (pair q c) = jointOf pq B := by
    have h := dist_jointOf_fst (p := jointOf pq B) (W := fun v : Q × C => A v.1) fun _ => hA _
    rw [← H, ← dist_dist_comp] at h
    exact h
  have hx : dist μ (pair q x) = jointOf pq A := by
    have h := dist_jointOf_map (Q := jointOf pq B) (Prod.fst : Q × C → Q) A
    rw [← H, ← dist_dist_comp, dist_jointOf_fst hB] at h
    exact h
  rw [← condEntropy_jointOf hq hA]
  refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hq hA) (hx.trans ?_)
  rw [show pair (Prod.fst : Q × F → Q) Prod.snd = id from rfl, dist_id]

/-- The gap is a conditional mutual information. -/
lemma twGap_eq (hμ : IsPMF μ) {q : Ω → Q} {c : Ω → C} {y : Ω → Y} {x : Ω → F}
    (h : H[x | c ; μ] = H[x | q ; μ]) : twGap μ (pair c y) q x = I[x : y | c ; μ] := by
  have h₁ := condEntropy_eq_sub hμ x c
  have h₂ := condEntropy_eq_sub hμ x q
  rw [condMutualInfo_eq_entropies hμ x y c, twGap]
  linarith

end Gap

/-! ### The law of the random code -/

section Law

variable {Q X₁ X₂ Y₁ Y₂ : Type*} [Fintype Q] [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
  {pq : Q → ℝ} {A : Q → X₁ → ℝ} {B : Q → X₂ → ℝ} {W : X₁ × X₂ → Y₁ × Y₂ → ℝ} {n : ℕ}

/-- The law of `(Q, X₁, X₂)`, for `p(q) p(x₁ | q) p(x₂ | q)`. -/
def twIn (pq : Q → ℝ) (A : Q → X₁ → ℝ) (B : Q → X₂ → ℝ) : Q × (X₁ × X₂) → ℝ :=
  jointOf pq fun k => prodDist (A k) (B k)

/-- The law of `((Q, X₁, X₂), (Y₁, Y₂))`. -/
def twLaw (pq : Q → ℝ) (A : Q → X₁ → ℝ) (B : Q → X₂ → ℝ) (W : X₁ × X₂ → Y₁ × Y₂ → ℝ) :
    (Q × (X₁ × X₂)) × (Y₁ × Y₂) → ℝ :=
  jointOf (twIn pq A B) fun t => W t.2

lemma twLaw_isPMF (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    IsPMF (twLaw pq A B W) :=
  jointOf_isPMF (jointOf_isPMF hq fun k => (hA k).prodDist (hB k)) fun _ => hW _

omit [Fintype Y₁] [Fintype Y₂] in
/-- The law of `((Q, X₂), X₁)` under the law of the inputs. -/
lemma dist_twIn₂ :
    dist (twIn pq A B) (fun t => ((t.1, t.2.2), t.2.1)) =
      jointOf (jointOf pq B) fun v => A v.1 := by
  classical
  set G : Q × (X₁ × X₂) → (Q × X₂) × X₁ := fun t => ((t.1, t.2.2), t.2.1) with hG
  have hGi : Function.Injective G := fun a b h => by
    simp only [hG, Prod.mk.injEq] at h
    exact Prod.ext h.1.1 (Prod.ext h.2 h.1.2)
  funext ⟨⟨k, b⟩, a⟩
  have h := dist_comp_of_injective (twIn pq A B) id hGi (k, (a, b))
  rw [dist_id] at h
  have h' : G ∘ id = G := rfl
  rw [h'] at h
  refine h.trans ?_
  simp only [twIn, jointOf, prodDist]
  ring

omit [Fintype Y₁] [Fintype Y₂] in
/-- The law of `((Q, X₁), X₂)` under the law of the inputs. -/
lemma dist_twIn₁ :
    dist (twIn pq A B) (fun t => ((t.1, t.2.1), t.2.2)) =
      jointOf (jointOf pq A) fun v => B v.1 := by
  classical
  set G : Q × (X₁ × X₂) → (Q × X₁) × X₂ := fun t => ((t.1, t.2.1), t.2.2) with hG
  have hGi : Function.Injective G := fun a b h => by
    simp only [hG, Prod.mk.injEq] at h
    exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)
  funext ⟨⟨k, a⟩, b⟩
  have h := dist_comp_of_injective (twIn pq A B) id hGi (k, (a, b))
  rw [dist_id] at h
  have h' : G ∘ id = G := rfl
  rw [h'] at h
  refine h.trans ?_
  simp only [twIn, jointOf, prodDist]
  ring

/-- The law of `((Q, X₂), X₁)`. -/
lemma twLaw_dist₂ (hW : IsChannel W) :
    dist (twLaw pq A B W) (pair (pair (fun z => z.1.1) fun z => z.1.2.2) fun z => z.1.2.1) =
      jointOf (jointOf pq B) fun v => A v.1 := by
  have e : dist (twLaw pq A B W) Prod.fst = twIn pq A B := dist_jointOf_fst fun _ => hW _
  have e' : pair (pair (fun z : (Q × (X₁ × X₂)) × (Y₁ × Y₂) => z.1.1) fun z => z.1.2.2)
      (fun z => z.1.2.1) = (fun t : Q × (X₁ × X₂) => ((t.1, t.2.2), t.2.1)) ∘ Prod.fst := rfl
  rw [e', dist_dist_comp, e, dist_twIn₂]

/-- The law of `((Q, X₁), X₂)`. -/
lemma twLaw_dist₁ (hW : IsChannel W) :
    dist (twLaw pq A B W) (pair (pair (fun z => z.1.1) fun z => z.1.2.1) fun z => z.1.2.2) =
      jointOf (jointOf pq A) fun v => B v.1 := by
  have e : dist (twLaw pq A B W) Prod.fst = twIn pq A B := dist_jointOf_fst fun _ => hW _
  have e' : pair (pair (fun z : (Q × (X₁ × X₂)) × (Y₁ × Y₂) => z.1.1) fun z => z.1.2.1)
      (fun z => z.1.2.2) = (fun t : Q × (X₁ × X₂) => ((t.1, t.2.1), t.2.2)) ∘ Prod.fst := rfl
  rw [e', dist_dist_comp, e, dist_twIn₁]

/-- A sum over sequences of tuples is a sum over the sequences of the components. -/
lemma sum_tw_split (F : (Fin n → (Q × (X₁ × X₂)) × (Y₁ × Y₂)) → ℝ) :
    ∑ ω, F ω = ∑ q : Fin n → Q, ∑ a : Fin n → X₁, ∑ b : Fin n → X₂,
      ∑ ζ : (Fin n → Y₁) × (Fin n → Y₂), F fun i => ((q i, (a i, b i)), (ζ.1 i, ζ.2 i)) := by
  calc ∑ ω, F ω = ∑ t, ∑ z, F (zipSeq t z) := sum_zip F
    _ = ∑ q, ∑ s, ∑ z, F (zipSeq (zipSeq q s) z) := sum_zip fun t => ∑ z, F (zipSeq t z)
    _ = ∑ q, ∑ a, ∑ b, ∑ z, F (zipSeq (zipSeq q (zipSeq a b)) z) :=
        sum_congr rfl fun q _ => sum_zip fun s => ∑ z, F (zipSeq (zipSeq q s) z)
    _ = _ := by
        refine sum_congr rfl fun q _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        rw [sum_zip, Fintype.sum_prod_type]
        rfl

/-- **The sum over all the sequences of a block is an i.i.d. expectation.** -/
theorem sum_tw_all (G : (Fin n → Q) → (Fin n → X₁) → (Fin n → X₂) →
      (Fin n → Y₁) × (Fin n → Y₂) → ℝ) :
    ∑ q, iidPMF pq n q * ∑ a, seqChan A n q a * ∑ b, seqChan B n q b *
      ∑ ζ, relaySeq W n (a, b) ζ * G q a b ζ =
    ∑ ω, iidPMF (twLaw pq A B W) n ω * G (fun i => (ω i).1.1) (fun i => (ω i).1.2.1)
      (fun i => (ω i).1.2.2) (fun i => (ω i).2.1, fun i => (ω i).2.2) := by
  rw [sum_tw_split]
  simp only [mul_sum]
  refine sum_congr rfl fun q _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
    sum_congr rfl fun ζ _ => ?_
  have h : iidPMF (twLaw pq A B W) n (fun i => ((q i, (a i, b i)), (ζ.1 i, ζ.2 i))) =
      iidPMF pq n q * (seqChan A n q a * (seqChan B n q b * relaySeq W n (a, b) ζ)) := by
    simp only [iidPMF, seqChan, relaySeq, twLaw, twIn, jointOf, prodDist, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by ring
  rw [h]
  ring

/-- The i.i.d. expectation of an indicator of an event that does not happen on typical sequences. -/
theorem sum_tw_le (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) {ε : ℝ}
    (P : (Fin n → Q) → (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₁) × (Fin n → Y₂) → Prop)
    (hP : ∀ ω ∈ robustTypicalSet (twLaw pq A B W) n ε, ¬ P (fun i => (ω i).1.1)
      (fun i => (ω i).1.2.1) (fun i => (ω i).1.2.2) (fun i => (ω i).2.1, fun i => (ω i).2.2)) :
    ∑ q, iidPMF pq n q * ∑ a, seqChan A n q a * ∑ b, seqChan B n q b *
      ∑ ζ, relaySeq W n (a, b) ζ * ind (P q a b ζ) ≤
    1 - prob (iidPMF (twLaw pq A B W) n) (robustTypicalSet (twLaw pq A B W) n ε) := by
  classical
  have hL := twLaw_isPMF hq hA hB hW
  rw [sum_tw_all fun q a b ζ => ind (P q a b ζ), ← prob_compl (iidPMF_isPMF hL n), prob]
  rw [← sum_filter_add_sum_filter_not univ (· ∈ robustTypicalSet (twLaw pq A B W) n ε)]
  have h₁ : ∑ ω ∈ univ.filter (· ∈ robustTypicalSet (twLaw pq A B W) n ε),
      iidPMF (twLaw pq A B W) n ω * ind (P (fun i => (ω i).1.1) (fun i => (ω i).1.2.1)
        (fun i => (ω i).1.2.2) (fun i => (ω i).2.1, fun i => (ω i).2.2)) = 0 :=
    sum_eq_zero fun ω hω => by
      rw [ind_of_neg (hP ω (mem_filter.mp hω).2), mul_zero]
  rw [h₁, zero_add]
  refine (sum_le_sum fun ω _ => mul_le_of_le_one_right ((iidPMF_isPMF hL n).nonneg ω)
    (ind_le_one _)).trans (le_of_eq ?_)
  refine sum_congr ?_ fun _ _ => rfl
  ext ω
  simp

end Law

/-! ### Shannon's inner bound -/

section Inner

variable {Q X₁ X₂ Y₁ Y₂ : Type*} [Fintype Q] [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
  [Nonempty X₁] [Nonempty X₂] {pq : Q → ℝ} {A : Q → X₁ → ℝ} {B : Q → X₂ → ℝ}
  {W : X₁ × X₂ → Y₁ × Y₂ → ℝ}

/-- The random variables of the test of node 2: `(Q, X₂, Y₂)`. -/
def twR₂ (z : (Q × (X₁ × X₂)) × (Y₁ × Y₂)) : (Q × X₂) × Y₂ := ((z.1.1, z.1.2.2), z.2.2)

/-- The random variables of the test of node 1: `(Q, X₁, Y₁)`. -/
def twR₁ (z : (Q × (X₁ × X₂)) × (Y₁ × Y₂)) : (Q × X₁) × Y₁ := ((z.1.1, z.1.2.1), z.2.1)

/-- `I(X₁; Y₂ | X₂, Q)`, in terms of entropies. -/
def twGap₂ (μ : (Q × (X₁ × X₂)) × (Y₁ × Y₂) → ℝ) : ℝ :=
  twGap μ twR₂ (fun z => z.1.1) fun z => z.1.2.1

/-- `I(X₂; Y₁ | X₁, Q)`, in terms of entropies. -/
def twGap₁ (μ : (Q × (X₁ × X₂)) × (Y₁ × Y₂) → ℝ) : ℝ :=
  twGap μ twR₁ (fun z => z.1.1) fun z => z.1.2.2

/-- The correction to `twGap₂`. -/
def twErr₂ (μ : (Q × (X₁ × X₂)) × (Y₁ × Y₂) → ℝ) : ℝ :=
  twErr μ twR₂ (fun z => z.1.1) fun z => z.1.2.1

/-- The correction to `twGap₁`. -/
def twErr₁ (μ : (Q × (X₁ × X₂)) × (Y₁ × Y₂) → ℝ) : ℝ :=
  twErr μ twR₁ (fun z => z.1.1) fun z => z.1.2.2

/-- The random coding bound in terms of the gaps. -/
theorem exists_twCode_gaps (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B)
    (hW : IsChannel W) {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ) :
    ∃ c : TWCCode M₁ M₂ n X₁ X₂ Y₁ Y₂, c.errProb W ≤
      2 * (1 - prob (iidPMF (twLaw pq A B W) n) (robustTypicalSet (twLaw pq A B W) n ε)) +
        ((M₂ : ℝ) - 1) * exp (-(n * (twGap₁ (twLaw pq A B W) - twErr₁ (twLaw pq A B W) * ε))) +
        ((M₁ : ℝ) - 1) * exp (-(n * (twGap₂ (twLaw pq A B W) - twErr₂ (twLaw pq A B W) * ε))) := by
  classical
  have hμ := twLaw_isPMF hq hA hB hW (W := W)
  set μ := twLaw pq A B W with hμd
  have c₂ := (tw_cond hμ hA hB (twLaw_dist₂ hW)).1
  have c₁ := (tw_cond hμ hB hA (twLaw_dist₁ hW)).1
  let T₂ : (Fin n → Q) → (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₂) → Prop := fun q a b y =>
    (fun i => (((q i, b i), y i), a i)) ∈
      robustTypicalSet (dist μ (pair twR₂ fun z => z.1.2.1)) n ε
  let T₁ : (Fin n → Q) → (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y₁) → Prop := fun q a b y =>
    (fun i => (((q i, a i), y i), b i)) ∈
      robustTypicalSet (dist μ (pair twR₁ fun z => z.1.2.2)) n ε
  obtain ⟨c, hc⟩ := exists_twCode_le (M₁ := M₁) (M₂ := M₂) (T₁ := T₁) (T₂ := T₂) hq hA hB hW
    (sum_tw_le hq hA hB hW (ε := ε) (fun q a b ζ => ¬ T₂ q a b ζ.2)
      fun ω hω => not_not.mpr (comp_mem_robustTypicalSet hω (pair twR₂ fun z => z.1.2.1)))
    (fun q b y => sum_fresh_tw hμ (r := twR₂) (x := fun z => z.1.2.1) (fun t => t.1.1)
      (fun _ => rfl) c₂ hA (n := n) (ε := ε) fun i => ((q i, b i), y i))
    (sum_tw_le hq hA hB hW (ε := ε) (fun q a b ζ => ¬ T₁ q a b ζ.1)
      fun ω hω => not_not.mpr (comp_mem_robustTypicalSet hω (pair twR₁ fun z => z.1.2.2)))
    (fun q a y => sum_fresh_tw hμ (r := twR₁) (x := fun z => z.1.2.2) (fun t => t.1.1)
      (fun _ => rfl) c₁ hB (n := n) (ε := ε) fun i => ((q i, a i), y i))
  rw [← hμd] at hc
  have e₁ : twGap μ twR₁ (fun x => (twR₁ x).1.1) (fun z => z.1.2.2) = twGap₁ μ := rfl
  have e₂ : twGap μ twR₂ (fun x => (twR₂ x).1.1) (fun z => z.1.2.1) = twGap₂ μ := rfl
  have e₃ : twErr μ twR₁ (fun x => (twR₁ x).1.1) (fun z => z.1.2.2) = twErr₁ μ := rfl
  have e₄ : twErr μ twR₂ (fun x => (twR₂ x).1.1) (fun z => z.1.2.1) = twErr₂ μ := rfl
  rw [e₁, e₂, e₃, e₄] at hc
  refine ⟨c, hc.trans (le_of_eq ?_)⟩
  ring

omit [Nonempty X₁] [Nonempty X₂] in
lemma twGap₂_eq (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    twGap₂ (twLaw pq A B W) =
      I[fun z => z.1.2.1 : fun z => z.2.2 | fun z => (z.1.1, z.1.2.2) ; twLaw pq A B W] :=
  twGap_eq (twLaw_isPMF hq hA hB hW) (tw_cond (twLaw_isPMF hq hA hB hW) hA hB (twLaw_dist₂ hW)).2

omit [Nonempty X₁] [Nonempty X₂] in
lemma twGap₁_eq (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    twGap₁ (twLaw pq A B W) =
      I[fun z => z.1.2.2 : fun z => z.2.1 | fun z => (z.1.1, z.1.2.1) ; twLaw pq A B W] :=
  twGap_eq (twLaw_isPMF hq hA hB hW) (tw_cond (twLaw_isPMF hq hA hB hW) hB hA (twLaw_dist₁ hW)).2

omit [Fintype Y₁] [Fintype Y₂] in
instance (M₁ M₂ n : ℕ) [NeZero M₁] [NeZero M₂] : Nonempty (TWCCode M₁ M₂ n X₁ X₂ Y₁ Y₂) :=
  ⟨⟨fun _ _ _ => Classical.arbitrary X₁, fun _ _ _ => Classical.arbitrary X₂, fun _ _ => 0,
    fun _ _ => 0⟩⟩

/-- **Shannon's inner bound, page 18-48 of [elgamal2010].** For `p(q) p(x₁ | q) p(x₂ | q)`, every
pair of rates, in bits, with `R₁ < I(X₁; Y₂ | X₂, Q)` and `R₂ < I(X₂; Y₁ | X₁, Q)` is achievable. -/
theorem isAchievableTWC_of_lt (hq : IsPMF pq) (hA : IsChannel A) (hB : IsChannel B)
    (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h₁ : R₁ * log 2 <
      I[fun z => z.1.2.1 : fun z => z.2.2 | fun z => (z.1.1, z.1.2.2) ; twLaw pq A B W])
    (h₂ : R₂ * log 2 <
      I[fun z => z.1.2.2 : fun z => z.2.1 | fun z => (z.1.1, z.1.2.1) ; twLaw pq A B W]) :
    IsAchievableTWC W R₁ R₂ := by
  classical
  rw [← twGap₂_eq hq hA hB hW] at h₁
  rw [← twGap₁_eq hq hA hB hW] at h₂
  have hμ := twLaw_isPMF hq hA hB hW (W := W)
  set μ := twLaw pq A B W with hμd
  have hE₁ : 0 ≤ twErr₁ μ := twErr_nonneg hμ _ _ _
  have hE₂ : 0 ≤ twErr₂ μ := twErr_nonneg hμ _ _ _
  set g := min (twGap₂ μ - R₁ * log 2) (twGap₁ μ - R₂ * log 2) with hg
  have hg0 : 0 < g := lt_min (by linarith) (by linarith)
  set E := twErr₁ μ + twErr₂ μ + 1 with hE
  have hEpos : 0 < E := by linarith
  set ε := g / E with hε
  have hεpos : 0 < ε := by positivity
  have hεE : E * ε = g := by
    rw [hε]
    field_simp
  have hg₂ : R₁ * log 2 + twErr₂ μ * ε + ε ≤ twGap₂ μ := by
    have : g ≤ twGap₂ μ - R₁ * log 2 := min_le_left _ _
    have h3 : (twErr₂ μ + 1) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
    linarith
  have hg₁ : R₂ * log 2 + twErr₁ μ * ε + ε ≤ twGap₁ μ := by
    have : g ≤ twGap₁ μ - R₂ * log 2 := min_le_right _ _
    have h3 : (twErr₁ μ + 1) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
    linarith
  have hprob := tendsto_prob_robustTypicalSet hμ hεpos
  have hexp : Tendsto (fun n : ℕ => exp (-(n * ε))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_natCast hεpos
  have hlim : Tendsto (fun n : ℕ => 2 * (1 - prob (iidPMF μ n) (robustTypicalSet μ n ε)) +
      2 * exp (-(n * ε)) + 2 * exp (-(n * ε))) atTop (𝓝 (2 * (1 - 1) + 2 * 0 + 2 * 0)) :=
    (((tendsto_const_nhds.sub hprob).const_mul _).add (hexp.const_mul _)).add (hexp.const_mul _)
  have key : ∀ δ > 0, ∀ᶠ n : ℕ in atTop,
      ∃ c : TWCCode (2 ^ ⌈(n : ℝ) * R₁⌉₊) (2 ^ ⌈(n : ℝ) * R₂⌉₊) n X₁ X₂ Y₁ Y₂, c.errProb W ≤ δ := by
    intro δ hδ
    have hev := (tendsto_order.mp hlim).2 δ (by simpa using hδ)
    filter_upwards [hev] with n hn
    obtain ⟨c, hc⟩ := exists_twCode_gaps (M₁ := 2 ^ ⌈(n : ℝ) * R₁⌉₊) (M₂ := 2 ^ ⌈(n : ℝ) * R₂⌉₊)
      (n := n) hq hA hB hW (W := W) ε
    refine ⟨c, hc.trans ?_⟩
    have t₁ := superposition_mul_exp_le (superposition_two_pow_ceil_sub_one_le n R₂)
      (by norm_num) hg₁
    have t₂ := superposition_mul_exp_le (superposition_two_pow_ceil_sub_one_le n R₁)
      (by norm_num) hg₂
    linarith
  obtain ⟨c, hc⟩ := exists_seq_tendsto
    (C := fun n : ℕ => TWCCode (2 ^ ⌈(n : ℝ) * R₁⌉₊) (2 ^ ⌈(n : ℝ) * R₂⌉₊) n X₁ X₂ Y₁ Y₂)
    (fun n c => c.errProb W)
    (fun n c => add_nonneg
      (errProb_nonneg (c.law_isPMF hW (by positivity) (by positivity)) _ _ _)
      (errProb_nonneg (c.law_isPMF hW (by positivity) (by positivity)) _ _ _)) key
  exact ⟨c, hc⟩

end Inner

end InfoTheory
