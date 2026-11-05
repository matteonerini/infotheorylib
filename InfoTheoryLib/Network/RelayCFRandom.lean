/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayCFBlock
public import InfoTheoryLib.Network.RelayCFCover

/-!
# The random code of compress–forward

The codewords `xⁿ(m)` and `x₁ⁿ(l)` are drawn i.i.d., and the descriptions `ŷ₁ⁿ(k | l)` given
`x₁ⁿ(l)`. The bin of each `k` is drawn uniformly at random. We bound the average error of the code.

## Main definitions

* `cfLam`: the law of `x₁ⁿ(l)` and of its codebook of descriptions.
* `cfUniq`: the decoder: the unique index that passes a test.
* `cfBlockOf`: the code of a table.

## Main statements

* `exists_cfBlock_le`: **the random coding bound**.

## Implementation notes

Since the bins are independent of the codebook, for `k' ≠ K` the description `ŷ₁ⁿ(k' | l)` is in the
bin of the chosen description with probability `1 / L`, whatever `K` is. Hence the sum over the
wrong descriptions of the bin needs no conditioning on `K`, unlike the notes, which follow Lemma 1
of the Wyner–Ziv proof.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

open Classical in
/-- The unique index that passes a test, if any. -/
def cfUniq {ι : Type*} (P : ι → Prop) (d : ι) : ι :=
  if h : ∃! i, P i then Classical.choose h else d

lemma ind_cfUniq_ne_le {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) (d i : ι) :
    ind (cfUniq P d ≠ i) ≤ ind (¬ P i) + ∑ j ∈ univ.filter (· ≠ i), ind (P j) := by
  have h0 : 0 ≤ ∑ j ∈ univ.filter (· ≠ i), ind (P j) := sum_nonneg fun j _ => ind_nonneg _
  by_cases h : P i ∧ ∀ j, j ≠ i → ¬ P j
  · have hu : ∃! j, P j := ⟨i, h.1, fun j hj => by
      by_contra hne
      exact h.2 j hne hj⟩
    have he : cfUniq P d = i := by
      simp only [cfUniq, hu, dite_true]
      exact (Classical.choose_spec hu).2 i h.1 |>.symm
    rw [ind_of_neg (not_not.mpr he)]
    exact add_nonneg (ind_nonneg _) h0
  · refine (ind_le_one _).trans ?_
    by_cases hi : P i
    · have : ∃ j, j ≠ i ∧ P j := by
        by_contra hc
        push Not at hc
        exact h ⟨hi, hc⟩
      obtain ⟨j, hj, hPj⟩ := this
      have hs := single_le_sum (f := fun j => ind (P j)) (fun j _ => ind_nonneg _)
        (mem_filter.mpr ⟨mem_univ j, hj⟩ : j ∈ univ.filter (· ≠ i))
      simp only [ind_of_pos hPj] at hs
      linarith [ind_nonneg (¬ P i)]
    · rw [ind_of_pos hi]
      linarith

variable {X U Y S V : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype S] [Fintype V]
  {p : X → ℝ} {p₁ : U → ℝ} {W : X × U → Y × S → ℝ} {q : U → V → ℝ} {n M L K : ℕ}

/-- The law of `x₁ⁿ(l)` and of its codebook of descriptions. -/
def cfLam (p₁ : U → ℝ) (q : U → V → ℝ) (n K : ℕ) : (Fin n → U) × (Fin K → Fin n → V) → ℝ :=
  fun a => iidPMF p₁ n a.1 * iidPMF (seqChan q n a.1) K a.2

omit [Fintype X] [Fintype Y] [Fintype S] in
lemma sum_cfLam (hq : IsChannel q) (G : (Fin n → U) → ℝ) :
    ∑ a, cfLam p₁ q n K a * G a.1 = ∑ u, iidPMF p₁ n u * G u := by
  simp only [cfLam, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  have h := (iidPMF_isPMF (seqChan_isChannel hq n u) K).sum_eq_one
  calc _ = iidPMF p₁ n u * G u * ∑ C, iidPMF (seqChan q n u) K C := by
        rw [mul_sum]
        exact sum_congr rfl fun C _ => by ring
    _ = _ := by rw [h, mul_one]

omit [Fintype X] [Fintype Y] [Fintype S] in
lemma cfLam_isPMF (hp₁ : IsPMF p₁) (hq : IsChannel q) : IsPMF (cfLam p₁ q n K) := by
  refine ⟨fun a => mul_nonneg ((iidPMF_isPMF hp₁ n).nonneg _)
    ((iidPMF_isPMF (seqChan_isChannel hq n a.1) K).nonneg _), ?_⟩
  have h := sum_cfLam (p₁ := p₁) (n := n) (K := K) hq fun _ => 1
  simp only [mul_one] at h
  rw [h]
  exact (iidPMF_isPMF hp₁ n).sum_eq_one

/-- The law of the table of the sender. -/
abbrev cfPX (p : X → ℝ) (n M : ℕ) : (Fin M → Fin n → X) → ℝ := piLaw fun _ => iidPMF p n

/-- The law of the table of the relay. -/
abbrev cfPU (p₁ : U → ℝ) (q : U → V → ℝ) (n L K : ℕ) :
    (Fin L → (Fin n → U) × (Fin K → Fin n → V)) → ℝ :=
  piLaw fun _ => cfLam p₁ q n K

/-- The law of the bins. -/
abbrev cfPB (L K : ℕ) : (Fin K → Fin L) → ℝ := piLaw fun _ => uniformPMF (Fin L)

variable [NeZero M] [NeZero L] [NeZero K]

/-- The block code of a table. -/
def cfBlockOf (T₁ : (Fin n → U) → (Fin n → Y) → Prop)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop)
    (Good : (Fin n → U) → (Fin n → S) → (Fin n → V) → Prop) (tx : Fin M → Fin n → X)
    (tu : Fin L → (Fin n → U) × (Fin K → Fin n → V)) (b : Fin K → Fin L) :
    CFBlock M L n X U Y S where
  x := tx
  s l := (tu l).1
  r l y₁ := b (cfPick (Good (tu l).1 y₁) (tu l).2)
  dL y := cfUniq (fun l => T₁ (tu l).1 y) 0
  dM l l' y := cfUniq (fun m => ∃ k, b k = l' ∧ T (tx m) (tu l).1 ((tu l).2 k) y) 0

omit [Fintype X] [Fintype U] [Fintype Y] [Fintype S] [Fintype V] [NeZero M] [NeZero K] in
/-- Two different indices are in the same bin with probability `1 / L`. -/
lemma sum_bin_eq {k k' : Fin K} (hk : k' ≠ k) :
    ∑ b, cfPB L K b * ind (b k' = b k) = 1 / (L : ℝ) := by
  classical
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hu : ∀ a : Fin L, uniformPMF (Fin L) a = 1 / (L : ℝ) := fun a => by simp [uniformPMF]
  rw [sum_piLaw_mul_eval₂ (ν := fun _ : Fin K => uniformPMF (Fin L)) (fun _ => uniformPMF_isPMF) hk
    fun a a' => ind (a = a')]
  have h₁ : ∀ a : Fin L, ∑ a' : Fin L, uniformPMF (Fin L) a * uniformPMF (Fin L) a' * ind (a = a') =
      1 / (L : ℝ) * (1 / (L : ℝ)) := by
    intro a
    rw [sum_eq_single a]
    · rw [ind_of_pos rfl, hu, mul_one]
    · intro a' _ ha'
      rw [ind_of_neg (Ne.symm ha'), mul_zero]
    · simp
  simp_rw [h₁]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

section Row

variable {T₁ : (Fin n → U) → (Fin n → Y) → Prop}
  {T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop}
  {Good : (Fin n → U) → (Fin n → S) → (Fin n → V) → Prop}

omit [Fintype X] [NeZero M] [NeZero K] in
/-- **The decoder of the state of the relay**, for one input of the sender. -/
theorem sum_rowA_le (hp₁ : IsPMF p₁) (hq : IsChannel q) (hW : IsChannel W) {e₁ : ℝ}
    (h₁ : ∀ y, ∑ u, iidPMF p₁ n u * ind (T₁ u y) ≤ e₁) (l : Fin L) (x : Fin n → X) :
    ∑ tu, cfPU p₁ q n L K tu * ∑ ζ, relaySeq W n (x, (tu l).1) ζ *
        ind (cfUniq (fun l' => T₁ (tu l').1 ζ.1) 0 ≠ l) ≤
      ∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ * ind (¬ T₁ u ζ.1) +
        ((L : ℝ) - 1) * e₁ := by
  classical
  have hΛ : IsPMF (cfLam p₁ q n K) := cfLam_isPMF hp₁ hq
  have hν : ∀ _ : Fin L, IsPMF (cfLam p₁ q n K) := fun _ => hΛ
  have hPU : IsPMF (cfPU p₁ q n L K) := piLaw_isPMF hν
  have hV := relaySeq_isChannel hW n
  have hup := iidPMF_isPMF hp₁ n
  -- the bound of a table
  have hpt : ∀ tu : Fin L → (Fin n → U) × (Fin K → Fin n → V),
      ∑ ζ, relaySeq W n (x, (tu l).1) ζ * ind (cfUniq (fun l' => T₁ (tu l').1 ζ.1) 0 ≠ l) ≤
      ∑ ζ, relaySeq W n (x, (tu l).1) ζ * ind (¬ T₁ (tu l).1 ζ.1) +
        ∑ l' ∈ univ.filter (· ≠ l), ∑ ζ, relaySeq W n (x, (tu l).1) ζ * ind (T₁ (tu l').1 ζ.1) := by
    intro tu
    rw [sum_comm, ← sum_add_distrib]
    refine sum_le_sum fun ζ _ => ?_
    rw [← mul_sum, ← mul_add]
    exact mul_le_mul_of_nonneg_left (ind_cfUniq_ne_le _ _ _) ((hV _).nonneg _)
  have h₂ : ∀ l' ∈ univ.filter (· ≠ l), ∑ tu, cfPU p₁ q n L K tu *
      ∑ ζ, relaySeq W n (x, (tu l).1) ζ * ind (T₁ (tu l').1 ζ.1) ≤ e₁ := by
    intro l' hl'
    have hne : l ≠ l' := fun h => (mem_filter.mp hl').2 h.symm
    rw [sum_piLaw_mul_eval₂ (ν := fun _ : Fin L => cfLam p₁ q n K) hν hne
      fun a a' => ∑ ζ, relaySeq W n (x, a.1) ζ * ind (T₁ a'.1 ζ.1)]
    have hinner : ∀ a : (Fin n → U) × (Fin K → Fin n → V), ∑ a', cfLam p₁ q n K a * cfLam p₁ q n K
      a' *
        ∑ ζ, relaySeq W n (x, a.1) ζ * ind (T₁ a'.1 ζ.1) ≤ cfLam p₁ q n K a * e₁ := by
      intro a
      have he : ∑ a', cfLam p₁ q n K a * cfLam p₁ q n K a' *
          ∑ ζ, relaySeq W n (x, a.1) ζ * ind (T₁ a'.1 ζ.1) = cfLam p₁ q n K a *
            ∑ ζ, relaySeq W n (x, a.1) ζ * ∑ u, iidPMF p₁ n u * ind (T₁ u ζ.1) := by
        simp_rw [← sum_cfLam (K := K) hq (fun u => ind (T₁ u _))]
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun ζ _ => sum_congr rfl fun a' _ => ?_
        ring
      rw [he]
      refine mul_le_mul_of_nonneg_left ?_ (hΛ.nonneg a)
      calc _ ≤ ∑ ζ, relaySeq W n (x, a.1) ζ * e₁ := sum_le_sum fun ζ _ =>
            mul_le_mul_of_nonneg_left (h₁ ζ.1) ((hV _).nonneg _)
        _ = e₁ := by rw [← sum_mul, (hV _).sum_eq_one, one_mul]
    calc _ ≤ ∑ a, cfLam p₁ q n K a * e₁ := sum_le_sum fun a _ => hinner a
      _ = e₁ := by rw [← sum_mul, hΛ.sum_eq_one, one_mul]
  have hcard : ((univ.filter (· ≠ l) : Finset (Fin L)).card : ℝ) = (L : ℝ) - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin,
      Nat.cast_sub (NeZero.one_le)]
    simp
  calc _ ≤ ∑ tu, cfPU p₁ q n L K tu * (∑ ζ, relaySeq W n (x, (tu l).1) ζ *
        ind (¬ T₁ (tu l).1 ζ.1) + ∑ l' ∈ univ.filter (· ≠ l),
          ∑ ζ, relaySeq W n (x, (tu l).1) ζ * ind (T₁ (tu l').1 ζ.1)) :=
        sum_le_sum fun tu _ => mul_le_mul_of_nonneg_left (hpt tu) (hPU.nonneg tu)
    _ = ∑ tu, cfPU p₁ q n L K tu * ∑ ζ, relaySeq W n (x, (tu l).1) ζ * ind (¬ T₁ (tu l).1 ζ.1) +
        ∑ l' ∈ univ.filter (· ≠ l), ∑ tu, cfPU p₁ q n L K tu *
          ∑ ζ, relaySeq W n (x, (tu l).1) ζ * ind (T₁ (tu l').1 ζ.1) := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        simp only [mul_sum]
        rw [sum_comm]
    _ ≤ _ := by
        refine add_le_add (le_of_eq ?_) ?_
        · rw [sum_piLaw_mul_eval (ν := fun _ : Fin L => cfLam p₁ q n K) hν l
            fun a => ∑ ζ, relaySeq W n (x, a.1) ζ * ind (¬ T₁ a.1 ζ.1)]
          exact sum_cfLam hq fun u => ∑ ζ, relaySeq W n (x, u) ζ * ind (¬ T₁ u ζ.1)
        · refine (sum_le_sum h₂).trans (le_of_eq ?_)
          rw [sum_const, nsmul_eq_mul, hcard]

omit [Fintype X] [Fintype U] [Fintype Y] [Fintype V] [NeZero M] [NeZero L] [NeZero K] in
/-- **The decoder of the message, for fixed tables of the sender and of the relay.** The average
  over
the bins of the error. -/
lemma sum_bin_le (tx : Fin M → Fin n → X) (u : Fin n → U) (C : Fin K → Fin n → V) (y : Fin n → Y)
    (k : Fin K) (m d : Fin M) [NeZero L] :
    ∑ b, cfPB L K b * ind (cfUniq (fun m' => ∃ k', b k' = b k ∧ T (tx m') u (C k') y) d ≠ m) ≤
      ind (¬ T (tx m) u (C k) y) + ∑ m' ∈ univ.filter (· ≠ m),
        (ind (T (tx m') u (C k) y) + (1 / (L : ℝ)) * ∑ k', ind (T (tx m') u (C k') y)) := by
  classical
  have hPB : IsPMF (cfPB L K) := piLaw_isPMF fun _ => uniformPMF_isPMF
  have hLinv : (0 : ℝ) ≤ 1 / (L : ℝ) := by positivity
  -- for fixed bins
  have hpt : ∀ b : Fin K → Fin L,
      ind (cfUniq (fun m' => ∃ k', b k' = b k ∧ T (tx m') u (C k') y) d ≠ m) ≤
      ind (¬ T (tx m) u (C k) y) + ∑ m' ∈ univ.filter (· ≠ m),
        (ind (T (tx m') u (C k) y) + ∑ k' ∈ univ.filter (· ≠ k),
          ind (b k' = b k) * ind (T (tx m') u (C k') y)) := by
    intro b
    refine (ind_cfUniq_ne_le _ _ _).trans (add_le_add ?_ (sum_le_sum fun m' _ => ?_))
    · exact ind_mono fun h hc => h ⟨k, rfl, hc⟩
    · by_cases hk : T (tx m') u (C k) y
      · rw [ind_of_pos hk]
        have : 0 ≤ ∑ k' ∈ univ.filter (· ≠ k), ind (b k' = b k) * ind (T (tx m') u (C k') y) :=
          sum_nonneg fun k' _ => mul_nonneg (ind_nonneg _) (ind_nonneg _)
        linarith [ind_le_one (∃ k', b k' = b k ∧ T (tx m') u (C k') y)]
      · rw [ind_of_neg hk, zero_add]
        by_cases hE : ∃ k', b k' = b k ∧ T (tx m') u (C k') y
        · obtain ⟨k', hb, hT⟩ := hE
          have hne : k' ≠ k := fun h => hk (h ▸ hT)
          rw [ind_of_pos ⟨k', hb, hT⟩]
          have hs := single_le_sum (f := fun k' => ind (b k' = b k) * ind (T (tx m') u (C k') y))
            (fun k' _ => mul_nonneg (ind_nonneg _) (ind_nonneg _))
            (mem_filter.mpr ⟨mem_univ k', hne⟩ : k' ∈ univ.filter (· ≠ k))
          simp only [ind_of_pos hb, ind_of_pos hT, mul_one] at hs
          exact hs
        · rw [ind_of_neg hE]
          exact sum_nonneg fun k' _ => mul_nonneg (ind_nonneg _) (ind_nonneg _)
  have hE : ∀ k' ∈ univ.filter (· ≠ k), ∑ b, cfPB L K b * ind (b k' = b k) = 1 / (L : ℝ) :=
    fun k' hk' => sum_bin_eq (mem_filter.mp hk').2
  calc _ ≤ ∑ b, cfPB L K b * (ind (¬ T (tx m) u (C k) y) + ∑ m' ∈ univ.filter (· ≠ m),
        (ind (T (tx m') u (C k) y) + ∑ k' ∈ univ.filter (· ≠ k),
          ind (b k' = b k) * ind (T (tx m') u (C k') y))) :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hpt b) (hPB.nonneg b)
    _ = ind (¬ T (tx m) u (C k) y) + ∑ m' ∈ univ.filter (· ≠ m),
        (ind (T (tx m') u (C k) y) + ∑ k' ∈ univ.filter (· ≠ k),
          (∑ b, cfPB L K b * ind (b k' = b k)) * ind (T (tx m') u (C k') y)) := by
        rw [sum_congr rfl fun b _ => mul_add _ _ _, sum_add_distrib, ← sum_mul, hPB.sum_eq_one,
          one_mul]
        congr 1
        rw [sum_congr rfl fun b _ => mul_sum _ _ _, sum_comm]
        refine sum_congr rfl fun m' _ => ?_
        rw [sum_congr rfl fun b _ => mul_add _ _ _, sum_add_distrib, ← sum_mul, hPB.sum_eq_one,
          one_mul]
        congr 1
        rw [sum_congr rfl fun b _ => mul_sum _ _ _, sum_comm]
        refine sum_congr rfl fun k' _ => ?_
        rw [sum_mul]
        exact sum_congr rfl fun b _ => by ring
    _ ≤ _ := by
        refine add_le_add le_rfl (sum_le_sum fun m' _ => add_le_add le_rfl ?_)
        rw [mul_sum]
        refine (sum_congr rfl fun k' hk' => by rw [hE k' hk']).le.trans ?_
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k' _ _ =>
          mul_nonneg hLinv (ind_nonneg _)

omit [Fintype U] [Fintype Y] [Fintype S] [Fintype X] [Fintype V] [NeZero M] [NeZero L] [NeZero K] in
lemma sum_iid_eval [Fintype V] {P : (Fin n → V) → ℝ} (hP : IsPMF P) (k : Fin K)
    (G : (Fin n → V) → ℝ) : ∑ C : Fin K → Fin n → V, iidPMF P K C * G (C k) = ∑ v, P v * G v :=
  sum_piLaw_mul_eval (ν := fun _ : Fin K => P) (fun _ => hP) k G

/-- The covering term of the bound. -/
def cfCov (p : X → ℝ) (p₁ : U → ℝ) (W : X × U → Y × S → ℝ) (q : U → V → ℝ)
    (T : (Fin n → X) → (Fin n → U) → (Fin n → V) → (Fin n → Y) → Prop)
    (Good : (Fin n → U) → (Fin n → S) → (Fin n → V) → Prop) (K : ℕ) [NeZero K] : ℝ :=
  ∑ u, iidPMF p₁ n u * ∑ C : Fin K → Fin n → V, iidPMF (seqChan q n u) K C *
    (∑ x, iidPMF p n x * ∑ ζ, relaySeq W n (x, u) ζ *
      ind (¬ T x u (C (cfPick (Good u ζ.2) C)) ζ.1))

omit [NeZero M] [NeZero L] in
/-- A wrong message, for the chosen description. -/
lemma sum_wrong_chosen (hp₁ : IsPMF p₁) (hq : IsChannel q) (hW : IsChannel W)
    {e₂ : ℝ} (h₂ : ∀ u v y, ∑ x, iidPMF p n x * ind (T x u v y) ≤ e₂) (x : Fin n → X) :
    ∑ x', iidPMF p n x' * ∑ a, cfLam p₁ q n K a * ∑ ζ, relaySeq W n (x, a.1) ζ *
      ind (T x' a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1) ≤ e₂ := by
  have hΛ : IsPMF (cfLam p₁ q n K) := cfLam_isPMF hp₁ hq
  have hV := relaySeq_isChannel hW n
  calc _ = ∑ a, cfLam p₁ q n K a * ∑ ζ, relaySeq W n (x, a.1) ζ * ∑ x', iidPMF p n x' *
        ind (T x' a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1) := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun ζ _ => sum_congr rfl fun x' _ => ?_
        ring
    _ ≤ ∑ a, cfLam p₁ q n K a * ∑ ζ, relaySeq W n (x, a.1) ζ * e₂ := by
        refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hΛ.nonneg a)
        exact sum_le_sum fun ζ _ => mul_le_mul_of_nonneg_left (h₂ _ _ _) ((hV _).nonneg _)
    _ = e₂ := by
        simp_rw [← sum_mul, (hV _).sum_eq_one, one_mul]
        rw [← sum_mul, hΛ.sum_eq_one, one_mul]

omit [NeZero M] [NeZero L] [NeZero K] in
/-- A wrong message, and a wrong description. -/
lemma sum_wrong_other (hp₁ : IsPMF p₁) (hq : IsChannel q) (hW : IsChannel W)
    {e₃ : ℝ} (h₃ : ∀ u y, ∑ x, iidPMF p n x * ∑ v, seqChan q n u v * ind (T x u v y) ≤ e₃)
    (x : Fin n → X) (k : Fin K) :
    ∑ x', iidPMF p n x' * ∑ a, cfLam p₁ q n K a * ∑ ζ, relaySeq W n (x, a.1) ζ *
      ind (T x' a.1 (a.2 k) ζ.1) ≤ e₃ := by
  have hup := iidPMF_isPMF hp₁ n
  have hV := relaySeq_isChannel hW n
  calc _ = ∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ * ∑ x', iidPMF p n x' *
        ∑ v, seqChan q n u v * ind (T x' u v ζ.1) := by
        have hin : ∀ (x' : Fin n → X) (u : Fin n → U), ∑ C : Fin K → Fin n → V,
            iidPMF (seqChan q n u) K C * ∑ ζ, relaySeq W n (x, u) ζ * ind (T x' u (C k) ζ.1) =
            ∑ ζ, relaySeq W n (x, u) ζ * ∑ v, seqChan q n u v * ind (T x' u v ζ.1) := by
          intro x' u
          simp_rw [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun ζ _ => ?_
          have he := sum_iid_eval (seqChan_isChannel hq n u) (K := K) k
            fun v => ind (T x' u v ζ.1)
          rw [← mul_sum, ← he, mul_sum]
          exact sum_congr rfl fun C _ => by ring
        have hstep : ∀ x', ∑ a, cfLam p₁ q n K a * ∑ ζ, relaySeq W n (x, a.1) ζ *
            ind (T x' a.1 (a.2 k) ζ.1) = ∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ *
              ∑ v, seqChan q n u v * ind (T x' u v ζ.1) := by
          intro x'
          simp only [cfLam, Fintype.sum_prod_type (f := fun a : (Fin n → U) × (Fin K → Fin n → V) =>
            _)]
          refine sum_congr rfl fun u _ => ?_
          rw [← hin, mul_sum]
          exact sum_congr rfl fun C _ => by ring
        simp_rw [hstep, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun u _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun ζ _ => sum_congr rfl fun x' _ => sum_congr rfl fun v _ => ?_
        ring
    _ ≤ ∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ * e₃ := by
        refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hup.nonneg u)
        exact sum_le_sum fun ζ _ => mul_le_mul_of_nonneg_left (h₃ _ _) ((hV _).nonneg _)
    _ = e₃ := by
        simp_rw [← sum_mul, (hV _).sum_eq_one, one_mul]
        rw [← sum_mul, hup.sum_eq_one, one_mul]

/-- A weighted sum of the error terms. -/
lemma sum_weight_expand {I J K' : Type*} [Fintype I] [Fintype K'] (s : Finset J) (w A : I → ℝ)
    (B : I → J → ℝ) (c : ℝ) (D : I → J → K' → ℝ) :
    ∑ i, w i * (A i + ∑ m ∈ s, (B i m + c * ∑ k, D i m k)) =
      ∑ i, w i * A i + ∑ m ∈ s, (∑ i, w i * B i m + c * ∑ k, ∑ i, w i * D i m k) := by
  have h : ∀ i, w i * (A i + ∑ m ∈ s, (B i m + c * ∑ k, D i m k)) =
      w i * A i + ∑ m ∈ s, (w i * B i m + c * ∑ k, w i * D i m k) := by
    intro i
    rw [mul_add, mul_sum]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [mul_add, mul_left_comm, mul_sum]
  have h₂ : ∑ i, ∑ m ∈ s, (w i * B i m + c * ∑ k, w i * D i m k) =
      ∑ m ∈ s, (∑ i, w i * B i m + c * ∑ k, ∑ i, w i * D i m k) := by
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_add_distrib, ← mul_sum]
    congr 2
    exact sum_comm
  simp_rw [h]
  rw [sum_add_distrib, h₂]

omit [NeZero M] [NeZero L] in
/-- **The decoder of the message.** -/
theorem sum_rowB_le (hp : IsPMF p) (hp₁ : IsPMF p₁) (hq : IsChannel q) (hW : IsChannel W) {e₂ e₃ :
  ℝ}
    (h₂ : ∀ u v y, ∑ x, iidPMF p n x * ind (T x u v y) ≤ e₂)
    (h₃ : ∀ u y, ∑ x, iidPMF p n x * ∑ v, seqChan q n u v * ind (T x u v y) ≤ e₃)
    [NeZero M] [NeZero L] (l : Fin L) (m : Fin M) :
    ∑ tx, cfPX p n M tx * ∑ tu, cfPU p₁ q n L K tu * ∑ b, cfPB L K b *
      ∑ ζ, relaySeq W n (tx m, (tu l).1) ζ * ind (cfUniq (fun m' => ∃ k, b k =
        b (cfPick (Good (tu l).1 ζ.2) (tu l).2) ∧ T (tx m') (tu l).1 ((tu l).2 k) ζ.1) 0 ≠ m) ≤
    cfCov p p₁ W q T Good K + ((M : ℝ) - 1) * (e₂ + (K : ℝ) / L * e₃) := by
  classical
  have hΛ : IsPMF (cfLam p₁ q n K) := cfLam_isPMF hp₁ hq
  have hνu : ∀ _ : Fin L, IsPMF (cfLam p₁ q n K) := fun _ => hΛ
  have hPU : IsPMF (cfPU p₁ q n L K) := piLaw_isPMF hνu
  have hpn := iidPMF_isPMF hp n
  have hνx : ∀ _ : Fin M, IsPMF (iidPMF p n) := fun _ => hpn
  have hPX : IsPMF (cfPX p n M) := piLaw_isPMF hνx
  have hV := relaySeq_isChannel hW n
  have hLinv : (0 : ℝ) ≤ 1 / (L : ℝ) := by positivity
  -- the three terms, for a pair of codewords
  let g₁ : (Fin n → X) → ℝ := fun x => ∑ a, cfLam p₁ q n K a * ∑ ζ, relaySeq W n (x, a.1) ζ *
    ind (¬ T x a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1)
  let g₂ : (Fin n → X) → (Fin n → X) → ℝ := fun x x' => ∑ a, cfLam p₁ q n K a *
    ∑ ζ, relaySeq W n (x, a.1) ζ * ind (T x' a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1)
  let g₃ : (Fin n → X) → (Fin n → X) → Fin K → ℝ := fun x x' k => ∑ a, cfLam p₁ q n K a *
    ∑ ζ, relaySeq W n (x, a.1) ζ * ind (T x' a.1 (a.2 k) ζ.1)
  -- for a fixed table of the sender
  have hbin : ∀ (tx : Fin M → Fin n → X) (a : (Fin n → U) × (Fin K → Fin n → V)),
      ∑ b, cfPB L K b * ∑ ζ, relaySeq W n (tx m, a.1) ζ * ind (cfUniq (fun m' => ∃ k, b k =
        b (cfPick (Good a.1 ζ.2) a.2) ∧ T (tx m') a.1 (a.2 k) ζ.1) 0 ≠ m) ≤
      ∑ ζ, relaySeq W n (tx m, a.1) ζ * (ind (¬ T (tx m) a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1)
        +
        ∑ m' ∈ univ.filter (· ≠ m), (ind (T (tx m') a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1) +
          (1 / (L : ℝ)) * ∑ k', ind (T (tx m') a.1 (a.2 k') ζ.1))) := by
    intro tx a
    calc _ = ∑ ζ, relaySeq W n (tx m, a.1) ζ * ∑ b, cfPB L K b * ind (cfUniq (fun m' => ∃ k, b k =
          b (cfPick (Good a.1 ζ.2) a.2) ∧ T (tx m') a.1 (a.2 k) ζ.1) 0 ≠ m) := by
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun ζ _ => sum_congr rfl fun b _ => by ring
      _ ≤ _ := sum_le_sum fun ζ _ => mul_le_mul_of_nonneg_left
          (sum_bin_le (L := L) (T := T) tx a.1 a.2 ζ.1 (cfPick (Good a.1 ζ.2) a.2) m 0)
          ((hV _).nonneg _)
  -- the average over the table of the relay
  have hrelay : ∀ tx : Fin M → Fin n → X, ∑ tu, cfPU p₁ q n L K tu * ∑ b, cfPB L K b *
      ∑ ζ, relaySeq W n (tx m, (tu l).1) ζ * ind (cfUniq (fun m' => ∃ k, b k =
        b (cfPick (Good (tu l).1 ζ.2) (tu l).2) ∧ T (tx m') (tu l).1 ((tu l).2 k) ζ.1) 0 ≠ m) ≤
      g₁ (tx m) + ∑ m' ∈ univ.filter (· ≠ m), (g₂ (tx m) (tx m') +
        (1 / (L : ℝ)) * ∑ k', g₃ (tx m) (tx m') k') := by
    intro tx
    have h₁ := sum_piLaw_mul_eval (ν := fun _ : Fin L => cfLam p₁ q n K) hνu l fun a =>
      ∑ b, cfPB L K b * ∑ ζ, relaySeq W n (tx m, a.1) ζ * ind (cfUniq (fun m' => ∃ k, b k =
        b (cfPick (Good a.1 ζ.2) a.2) ∧ T (tx m') a.1 (a.2 k) ζ.1) 0 ≠ m)
    refine (le_of_eq h₁).trans ?_
    refine (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hbin tx a) (hΛ.nonneg a)).trans
      (le_of_eq ?_)
    have hζ : ∀ a : (Fin n → U) × (Fin K → Fin n → V),
        ∑ ζ, relaySeq W n (tx m, a.1) ζ * (ind (¬ T (tx m) a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2))
          ζ.1) +
          ∑ m' ∈ univ.filter (· ≠ m), (ind (T (tx m') a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1) +
            (1 / (L : ℝ)) * ∑ k', ind (T (tx m') a.1 (a.2 k') ζ.1))) =
        ∑ ζ, relaySeq W n (tx m, a.1) ζ *
            ind (¬ T (tx m) a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1) +
          ∑ m' ∈ univ.filter (· ≠ m), (∑ ζ, relaySeq W n (tx m, a.1) ζ *
              ind (T (tx m') a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1) +
            (1 / (L : ℝ)) * ∑ k', ∑ ζ, relaySeq W n (tx m, a.1) ζ *
              ind (T (tx m') a.1 (a.2 k') ζ.1)) := fun a =>
      sum_weight_expand (univ.filter (· ≠ m)) (fun ζ => relaySeq W n (tx m, a.1) ζ)
        (fun ζ => ind (¬ T (tx m) a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1))
        (fun ζ m' => ind (T (tx m') a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1)) (1 / (L : ℝ))
        (fun ζ m' k' => ind (T (tx m') a.1 (a.2 k') ζ.1))
    simp_rw [hζ]
    exact sum_weight_expand (univ.filter (· ≠ m)) (cfLam p₁ q n K)
      (fun a => ∑ ζ, relaySeq W n (tx m, a.1) ζ *
        ind (¬ T (tx m) a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1))
      (fun a m' => ∑ ζ, relaySeq W n (tx m, a.1) ζ *
        ind (T (tx m') a.1 (a.2 (cfPick (Good a.1 ζ.2) a.2)) ζ.1)) (1 / (L : ℝ))
      (fun a m' k' => ∑ ζ, relaySeq W n (tx m, a.1) ζ * ind (T (tx m') a.1 (a.2 k') ζ.1))
  have hpair : ∀ m' ∈ univ.filter (· ≠ m), ∀ (G : (Fin n → X) → (Fin n → X) → ℝ) (e : ℝ),
      (∀ x, ∑ x', iidPMF p n x' * G x x' ≤ e) → ∑ tx, cfPX p n M tx * G (tx m) (tx m') ≤ e := by
    intro m' hm' G e hG
    have hne : m ≠ m' := fun h => (mem_filter.mp hm').2 h.symm
    rw [sum_piLaw_mul_eval₂ (ν := fun _ : Fin M => iidPMF p n) hνx hne G]
    calc _ = ∑ x, iidPMF p n x * ∑ x', iidPMF p n x' * G x x' := by
          simp only [mul_sum]
          exact sum_congr rfl fun x _ => sum_congr rfl fun x' _ => by ring
      _ ≤ ∑ x, iidPMF p n x * e :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hG x) (hpn.nonneg x)
      _ = e := by rw [← sum_mul, hpn.sum_eq_one, one_mul]
  have hsum₂ : ∀ m' ∈ univ.filter (· ≠ m), ∑ tx, cfPX p n M tx * g₂ (tx m) (tx m') ≤ e₂ :=
    fun m' hm' => hpair m' hm' g₂ e₂ fun x => sum_wrong_chosen hp₁ hq hW h₂ x
  have hsum₃ : ∀ m' ∈ univ.filter (· ≠ m), ∀ k' : Fin K,
      ∑ tx, cfPX p n M tx * g₃ (tx m) (tx m') k' ≤ e₃ :=
    fun m' hm' k' => hpair m' hm' (fun x x' => g₃ x x' k') e₃ fun x =>
      sum_wrong_other hp₁ hq hW h₃ x k'
  have hsum₁ : ∑ tx, cfPX p n M tx * g₁ (tx m) = cfCov p p₁ W q T Good K := by
    rw [sum_piLaw_mul_eval (ν := fun _ : Fin M => iidPMF p n) hνx m g₁]
    simp only [g₁, cfCov, cfLam, Fintype.sum_prod_type (f := fun a : (Fin n → U) × (Fin K → Fin n →
      V) => _),
      mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun C _ => sum_congr rfl fun x _ => sum_congr rfl fun ζ _ => ?_
    ring
  have hcard : ((univ.filter (· ≠ m) : Finset (Fin M)).card : ℝ) = (M : ℝ) - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_univ m), card_univ, Fintype.card_fin,
      Nat.cast_sub (NeZero.one_le)]
    simp
  calc _ ≤ ∑ tx, cfPX p n M tx * (g₁ (tx m) + ∑ m' ∈ univ.filter (· ≠ m), (g₂ (tx m) (tx m') +
        (1 / (L : ℝ)) * ∑ k', g₃ (tx m) (tx m') k')) :=
        sum_le_sum fun tx _ => mul_le_mul_of_nonneg_left (hrelay tx) (hPX.nonneg tx)
    _ = ∑ tx, cfPX p n M tx * g₁ (tx m) + ∑ m' ∈ univ.filter (· ≠ m),
        (∑ tx, cfPX p n M tx * g₂ (tx m) (tx m') + (1 / (L : ℝ)) * ∑ k',
          ∑ tx, cfPX p n M tx * g₃ (tx m) (tx m') k') := sum_weight_expand _ _ _ _ _ _
    _ ≤ cfCov p p₁ W q T Good K + ∑ _m' ∈ univ.filter (· ≠ m), (e₂ + (K : ℝ) / L * e₃) := by
        rw [hsum₁]
        refine add_le_add le_rfl (sum_le_sum fun m' hm' => add_le_add (hsum₂ m' hm') ?_)
        have h3 : ∑ k' : Fin K, ∑ tx, cfPX p n M tx * g₃ (tx m) (tx m') k' ≤ (K : ℝ) * e₃ := by
          refine (sum_le_sum fun k' _ => hsum₃ m' hm' k').trans (le_of_eq ?_)
          simp
        calc _ ≤ 1 / (L : ℝ) * ((K : ℝ) * e₃) := mul_le_mul_of_nonneg_left h3 hLinv
          _ = _ := by ring
    _ = _ := by
        rw [sum_const, nsmul_eq_mul, hcard]

/-- The linearity of an expectation. -/
lemma sum_mul_const_sum {I T' : Type*} [Fintype I] [Fintype T'] (P : T' → ℝ) (c : ℝ)
    (g : I → T' → ℝ) : ∑ t, P t * (c * ∑ i, g i t) = c * ∑ i, ∑ t, P t * g i t := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun t _ => by ring

/-- **The random coding bound of compress–forward.** -/
theorem exists_cfBlock_le (hp : IsPMF p) (hp₁ : IsPMF p₁) (hq : IsChannel q) (hW : IsChannel W)
    {e₁ e₂ e₃ c₁ : ℝ} (h₁ : ∀ y, ∑ u, iidPMF p₁ n u * ind (T₁ u y) ≤ e₁)
    (h₂ : ∀ u v y, ∑ x, iidPMF p n x * ind (T x u v y) ≤ e₂)
    (h₃ : ∀ u y, ∑ x, iidPMF p n x * ∑ v, seqChan q n u v * ind (T x u v y) ≤ e₃)
    (hA : ∑ x, iidPMF p n x * ∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ * ind (¬ T₁ u ζ.1) ≤
      c₁) :
    ∃ C : CFBlock M L n X U Y S, C.avgErr (relaySeq W n) ≤
      c₁ + ((L : ℝ) - 1) * e₁ + (cfCov p p₁ W q T Good K +
        ((M : ℝ) - 1) * (e₂ + (K : ℝ) / L * e₃)) := by
  classical
  have hΛ : IsPMF (cfLam p₁ q n K) := cfLam_isPMF hp₁ hq
  have hνu : ∀ _ : Fin L, IsPMF (cfLam p₁ q n K) := fun _ => hΛ
  have hPU : IsPMF (cfPU p₁ q n L K) := piLaw_isPMF hνu
  have hpn := iidPMF_isPMF hp n
  have hνx : ∀ _ : Fin M, IsPMF (iidPMF p n) := fun _ => hpn
  have hPX : IsPMF (cfPX p n M) := piLaw_isPMF hνx
  have hPB : IsPMF (cfPB L K) := piLaw_isPMF fun _ => uniformPMF_isPMF
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  set Bd := c₁ + ((L : ℝ) - 1) * e₁ + (cfCov p p₁ W q T Good K +
    ((M : ℝ) - 1) * (e₂ + (K : ℝ) / L * e₃)) with hBd
  let blk := fun tx tu b => cfBlockOf (M := M) (L := L) (K := K) T₁ T Good tx tu b
  -- the error of a state and of a message
  have hrow : ∀ (l : Fin L) (m : Fin M), ∑ tx, cfPX p n M tx * ∑ tu, cfPU p₁ q n L K tu *
      ∑ b, cfPB L K b * (blk tx tu b).rowErr (relaySeq W n) l m ≤ Bd := by
    intro l m
    have hsplit : ∀ tx tu b, (blk tx tu b).rowErr (relaySeq W n) l m =
        ∑ ζ, relaySeq W n (tx m, (tu l).1) ζ *
          ind (cfUniq (fun l' => T₁ (tu l').1 ζ.1) 0 ≠ l) +
        ∑ ζ, relaySeq W n (tx m, (tu l).1) ζ * ind (cfUniq (fun m' => ∃ k, b k =
          b (cfPick (Good (tu l).1 ζ.2) (tu l).2) ∧ T (tx m') (tu l).1 ((tu l).2 k) ζ.1) 0 ≠ m) :=
            by
      intro tx tu b
      simp only [CFBlock.rowErr, CFBlock.loss, mul_add, sum_add_distrib]
      rfl
    simp_rw [hsplit, mul_add, sum_add_distrib, ← sum_mul, hPB.sum_eq_one, one_mul, mul_add,
      sum_add_distrib, mul_add, sum_add_distrib]
    have hB := sum_rowB_le (T := T) (Good := Good) (K := K) hp hp₁ hq hW h₂ h₃ l m
    rw [hBd]
    refine add_le_add ?_ hB
    rw [sum_piLaw_mul_eval (ν := fun _ : Fin M => iidPMF p n) hνx m fun x =>
      ∑ tu, cfPU p₁ q n L K tu * ∑ ζ, relaySeq W n (x, (tu l).1) ζ *
        ind (cfUniq (fun l' => T₁ (tu l').1 ζ.1) 0 ≠ l)]
    calc _ ≤ ∑ x, iidPMF p n x * (∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ *
          ind (¬ T₁ u ζ.1) + ((L : ℝ) - 1) * e₁) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (sum_rowA_le hp₁ hq hW h₁ l x)
            (hpn.nonneg x)
      _ = ∑ x, iidPMF p n x * ∑ u, iidPMF p₁ n u * ∑ ζ, relaySeq W n (x, u) ζ * ind (¬ T₁ u ζ.1) +
          ((L : ℝ) - 1) * e₁ := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hpn.sum_eq_one, one_mul]
      _ ≤ _ := add_le_add hA le_rfl
  -- the average over the states and the messages
  have havg : ∀ tx tu b, (blk tx tu b).avgErr (relaySeq W n) = (1 / ((L : ℝ) * M)) *
      ∑ i : Fin L × Fin M, (blk tx tu b).rowErr (relaySeq W n) i.1 i.2 := by
    intro tx tu b
    rw [CFBlock.avgErr, Fintype.sum_prod_type]
    ring
  have htot : ∑ tx, cfPX p n M tx * ∑ tu, cfPU p₁ q n L K tu * ∑ b, cfPB L K b *
      (blk tx tu b).avgErr (relaySeq W n) ≤ Bd := by
    simp_rw [havg, sum_mul_const_sum]
    have hc : (0 : ℝ) ≤ 1 / ((L : ℝ) * M) := by positivity
    refine (mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hrow i.1 i.2) hc).trans (le_of_eq ?_)
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  obtain ⟨tx, h₁'⟩ := exists_le_of_sum_mul_le hPX htot
  obtain ⟨tu, h₂'⟩ := exists_le_of_sum_mul_le hPU h₁'
  obtain ⟨b, h₃'⟩ := exists_le_of_sum_mul_le hPB h₂'
  exact ⟨blk tx tu b, h₃'⟩

end Row

end InfoTheory
