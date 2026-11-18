/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACFeedback
public import InfoTheoryLib.Network.TwoWayInner

/-!
# The Cover–Leung inner bound: codes for one block

In one block with state `l`, sender 1 sends `x₁(l, m)` and sender 2 sends `x₂(l, c)`. Sender 1,
knowing `(l, m)`, decodes `c` from the output, and the receiver, knowing `c`, decodes `(l, m)`.

## Main definitions

* `CLBlock`: a code for one block.
* `rowLaw`: the law of the codewords of one state: `uⁿ` and, given `uⁿ`, independent `x₁ⁿ` and
  `x₂ⁿ`.
* `clLaw`: the law of `((U, X₁, X₂), Y)`.
* `macSeq`: `n` uses of the channel.

## Main statements

* `sum_clCode_err_le`: the random coding bound for one triple of indices.
* `exists_clBlock_le`: the random coding bound for the code of one block.
* `eventually_clBlock`: **codes for one block**, for rates that satisfy the conditions of the notes.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Codes for one block -/

/-- **A code for one block.** Sender 1 sends `x₁ l m` and sender 2 sends `x₂ l c`. Sender 1 decodes
`c` knowing `(l, m)`, and the receiver decodes `(l, m)` knowing `c`. -/
structure CLBlock (Mb Mm : ℕ) (S₁ S₂ Y : Type*) where
  /-- The codewords of sender 1. -/
  x₁ : Fin Mb → Fin Mm → S₁
  /-- The codewords of sender 2. -/
  x₂ : Fin Mb → Fin Mb → S₂
  /-- The decoder of sender 1. -/
  d₁ : Fin Mb → Fin Mm → Y → Fin Mb
  /-- The decoder of the receiver. -/
  d : Fin Mb → Y → Fin Mb × Fin Mm

section Block

variable {Mb Mm : ℕ} {S₁ S₂ Y : Type*} [Fintype Y]

/-- The probability that one of the two decoders is wrong, for the indices `(l, c, m)`. -/
def CLBlock.err (C : CLBlock Mb Mm S₁ S₂ Y) (V : S₁ × S₂ → Y → ℝ) (l c : Fin Mb) (m : Fin Mm) : ℝ :=
  ∑ y, V (C.x₁ l m, C.x₂ l c) y * (ind (C.d₁ l m y ≠ c) + ind (C.d c y ≠ (l, m)))

/-- The errors that matter: for the first block, where `l` is fixed, for the blocks in the middle,
and for the last block, where `c` and `m` are fixed. -/
def CLBlock.avgErr [NeZero Mb] [NeZero Mm] (C : CLBlock Mb Mm S₁ S₂ Y) (V : S₁ × S₂ → Y → ℝ) : ℝ :=
  (∑ c, ∑ m, C.err V 0 c m) / (Mb * Mm) + (∑ l, ∑ c, ∑ m, C.err V l c m) / (Mb * Mb * Mm) +
    (∑ l, C.err V l 0 0) / Mb

end Block

/-! ### The law of the codewords of one state -/

section Row

variable {U' A' B' Y' : Type*} [Fintype U'] [Fintype A'] [Fintype B'] [Fintype Y'] {Mb Mm : ℕ}
  {pu : U' → ℝ} {Pa : U' → A' → ℝ} {Pb : U' → B' → ℝ}

/-- The codewords of one state. -/
abbrev CLRow (Mb Mm : ℕ) (U' A' B' : Type*) : Type _ := U' × (Fin Mm → A') × (Fin Mb → B')

/-- The law of the codewords of one state. -/
def rowLaw (pu : U' → ℝ) (Pa : U' → A' → ℝ) (Pb : U' → B' → ℝ) (R : CLRow Mb Mm U' A' B') : ℝ :=
  pu R.1 * (piLaw (fun _ => Pa R.1) R.2.1 * piLaw (fun _ => Pb R.1) R.2.2)

lemma sum_rowLaw (G : CLRow Mb Mm U' A' B' → ℝ) :
    ∑ R, rowLaw pu Pa Pb R * G R = ∑ u, pu u * ∑ ta : Fin Mm → A', piLaw (fun _ => Pa u) ta *
      ∑ tb : Fin Mb → B', piLaw (fun _ => Pb u) tb * G (u, ta, tb) := by
  simp only [Fintype.sum_prod_type, rowLaw, mul_sum]
  exact sum_congr rfl fun u _ => sum_congr rfl fun ta _ => sum_congr rfl fun tb _ => by ring

lemma rowLaw_isPMF (hu : IsPMF pu) (hPa : IsChannel Pa) (hPb : IsChannel Pb) :
    IsPMF (rowLaw (Mb := Mb) (Mm := Mm) pu Pa Pb) := by
  have hta : ∀ u, IsPMF (piLaw fun _ : Fin Mm => Pa u) := fun u => piLaw_isPMF fun _ => hPa u
  have htb : ∀ u, IsPMF (piLaw fun _ : Fin Mb => Pb u) := fun u => piLaw_isPMF fun _ => hPb u
  refine ⟨fun R => mul_nonneg (hu.nonneg _) (mul_nonneg ((hta _).nonneg _) ((htb _).nonneg _)), ?_⟩
  have h := sum_rowLaw (Mb := Mb) (Mm := Mm) (pu := pu) (Pa := Pa) (Pb := Pb) fun _ => 1
  simp only [mul_one, (htb _).sum_eq_one, (hta _).sum_eq_one, hu.sum_eq_one] at h
  exact h

/-- The expectation of a function of the true codewords. -/
lemma rowLaw_eval (hPa : IsChannel Pa) (hPb : IsChannel Pb) (m : Fin Mm) (c : Fin Mb)
    (G : U' → A' → B' → ℝ) :
    ∑ R, rowLaw pu Pa Pb R * G R.1 (R.2.1 m) (R.2.2 c) =
      ∑ u, pu u * ∑ a, Pa u a * ∑ b, Pb u b * G u a b := by
  rw [sum_rowLaw]
  refine sum_congr rfl fun u _ => congrArg _ ?_
  have h : ∀ ta : Fin Mm → A', ∑ tb : Fin Mb → B', piLaw (fun _ => Pb u) tb * G u (ta m) (tb c) =
      ∑ b, Pb u b * G u (ta m) b := fun ta =>
    sum_piLaw_mul_eval (ν := fun _ : Fin Mb => Pb u) (fun _ => hPb u) c fun b => G u (ta m) b
  simp only [h]
  exact sum_piLaw_mul_eval (ν := fun _ : Fin Mm => Pa u) (fun _ => hPa u) m
    fun a => ∑ b, Pb u b * G u a b

/-- The expectation of a function of the true codewords and of a wrong codeword of sender 2. -/
lemma rowLaw_eval_b (hPa : IsChannel Pa) (hPb : IsChannel Pb) (m : Fin Mm)
    {c c' : Fin Mb} (hc : c ≠ c') (G : U' → A' → B' → B' → ℝ) :
    ∑ R, rowLaw pu Pa Pb R * G R.1 (R.2.1 m) (R.2.2 c) (R.2.2 c') =
      ∑ u, pu u * ∑ a, Pa u a * ∑ b, Pb u b * ∑ b', Pb u b' * G u a b b' := by
  rw [sum_rowLaw]
  refine sum_congr rfl fun u _ => congrArg _ ?_
  have h : ∀ ta : Fin Mm → A', ∑ tb : Fin Mb → B', piLaw (fun _ => Pb u) tb *
      G u (ta m) (tb c) (tb c') = ∑ b, Pb u b * ∑ b', Pb u b' * G u (ta m) b b' := fun ta =>
    sum_piLaw_mul_eval₂' (ν := fun _ : Fin Mb => Pb u) (fun _ => hPb u) hc fun b b' =>
      G u (ta m) b b'
  simp only [h]
  exact sum_piLaw_mul_eval (ν := fun _ : Fin Mm => Pa u) (fun _ => hPa u) m
    fun a => ∑ b, Pb u b * ∑ b', Pb u b' * G u a b b'

/-- The expectation of a function of the true codewords and of a wrong codeword of sender 1. -/
lemma rowLaw_eval_a (hPa : IsChannel Pa) (hPb : IsChannel Pb)
    {m m' : Fin Mm} (hm : m ≠ m') (c : Fin Mb) (G : U' → A' → A' → B' → ℝ) :
    ∑ R, rowLaw pu Pa Pb R * G R.1 (R.2.1 m) (R.2.1 m') (R.2.2 c) =
      ∑ u, pu u * ∑ a, Pa u a * ∑ a', Pa u a' * ∑ b, Pb u b * G u a a' b := by
  rw [sum_rowLaw]
  refine sum_congr rfl fun u _ => congrArg _ ?_
  have h : ∀ ta : Fin Mm → A', ∑ tb : Fin Mb → B', piLaw (fun _ => Pb u) tb *
      G u (ta m) (ta m') (tb c) = ∑ b, Pb u b * G u (ta m) (ta m') b := fun ta =>
    sum_piLaw_mul_eval (ν := fun _ : Fin Mb => Pb u) (fun _ => hPb u) c fun b =>
      G u (ta m) (ta m') b
  simp only [h]
  exact sum_piLaw_mul_eval₂' (ν := fun _ : Fin Mm => Pa u) (fun _ => hPa u) hm fun a a' =>
    ∑ b, Pb u b * G u a a' b

/-- A sum over the pairs different from `(l, m)`. -/
lemma sum_filter_prod_ne {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (f : K × L → ℝ) (l : K) (m : L) :
    ∑ p ∈ univ.filter (· ≠ (l, m)), f p =
      ∑ m' ∈ univ.filter (· ≠ m), f (l, m') + ∑ l' ∈ univ.filter (· ≠ l), ∑ m', f (l', m') := by
  rw [sum_filter, Fintype.sum_prod_type, ← Finset.add_sum_erase univ _ (mem_univ l)]
  congr 1
  · rw [sum_filter]
    refine sum_congr rfl fun m' _ => ?_
    simp
  · rw [filter_ne']
    refine sum_congr rfl fun l' hl' => sum_congr rfl fun m' _ => ?_
    have : (l', m') ≠ (l, m) := fun h => (mem_erase.mp hl').1 (Prod.ext_iff.mp h).1
    simp [this]

variable [NeZero Mb] [NeZero Mm]

/-- The code of a table of rows, with the decoders that look for the unique index that passes the
test. -/
def clCode (T : U' → A' → B' → Y' → Prop) (t : Fin Mb → CLRow Mb Mm U' A' B') :
    CLBlock Mb Mm A' B' Y' where
  x₁ l m := (t l).2.1 m
  x₂ l c := (t l).2.2 c
  d₁ l m y := cfUniq (fun c' => T (t l).1 ((t l).2.1 m) ((t l).2.2 c') y) 0
  d c y := cfUniq (fun p : Fin Mb × Fin Mm => T (t p.1).1 ((t p.1).2.1 p.2) ((t p.1).2.2 c) y) (0,
    0)

/-- **The random coding bound for one triple of indices.** -/
theorem sum_clCode_err_le {V : A' × B' → Y' → ℝ} {T : U' → A' → B' → Y' → Prop} (hu : IsPMF pu)
    (hPa : IsChannel Pa) (hPb : IsChannel Pb) (hV : IsChannel V) {c₀ e₁ e₂ e₃ : ℝ}
    (hc₀ : ∑ u, pu u * ∑ a, Pa u a * ∑ b, Pb u b * ∑ y, V (a, b) y * ind (¬ T u a b y) ≤ c₀)
    (he₂ : ∀ u a y, ∑ b, Pb u b * ind (T u a b y) ≤ e₂)
    (he₁ : ∀ u b y, ∑ a, Pa u a * ind (T u a b y) ≤ e₁)
    (he₃ : ∀ y, ∑ u, pu u * ∑ a, Pa u a * ∑ b, Pb u b * ind (T u a b y) ≤ e₃)
    (l c : Fin Mb) (m : Fin Mm) :
    ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => rowLaw pu Pa Pb) t *
      (clCode T t).err V l c m ≤
    2 * c₀ + ((Mb : ℝ) - 1) * e₂ + ((Mm : ℝ) - 1) * e₁ + ((Mb : ℝ) - 1) * Mm * e₃ := by
  classical
  set ρ : CLRow Mb Mm U' A' B' → ℝ := rowLaw pu Pa Pb with hρ
  have hρP : IsPMF ρ := rowLaw_isPMF hu hPa hPb
  have hνr : ∀ _ : Fin Mb, IsPMF ρ := fun _ => hρP
  have hν : IsPMF (piLaw fun _ : Fin Mb => ρ) := piLaw_isPMF hνr
  have hsumV : ∀ (a : A') (b : B') (e : ℝ) (g : Y' → ℝ), (∀ y, g y ≤ e) →
      ∑ y, V (a, b) y * g y ≤ e := fun a b e g hg =>
    (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hg y) ((hV _).nonneg y)).trans
      (le_of_eq (by rw [← sum_mul, (hV _).sum_eq_one, one_mul]))
  -- the four terms
  let A₀ : CLRow Mb Mm U' A' B' → ℝ := fun R =>
    ∑ y, V (R.2.1 m, R.2.2 c) y * ind (¬ T R.1 (R.2.1 m) (R.2.2 c) y)
  let A₁ : Fin Mb → CLRow Mb Mm U' A' B' → ℝ := fun c' R =>
    ∑ y, V (R.2.1 m, R.2.2 c) y * ind (T R.1 (R.2.1 m) (R.2.2 c') y)
  let A₂ : Fin Mm → CLRow Mb Mm U' A' B' → ℝ := fun m' R =>
    ∑ y, V (R.2.1 m, R.2.2 c) y * ind (T R.1 (R.2.1 m') (R.2.2 c) y)
  let A₃ : Fin Mm → CLRow Mb Mm U' A' B' → CLRow Mb Mm U' A' B' → ℝ := fun m' R R' =>
    ∑ y, V (R.2.1 m, R.2.2 c) y * ind (T R'.1 (R'.2.1 m') (R'.2.2 c) y)
  -- the union bound
  have hpt : ∀ t : Fin Mb → CLRow Mb Mm U' A' B', (clCode T t).err V l c m ≤
      2 * A₀ (t l) + ∑ c' ∈ univ.filter (· ≠ c), A₁ c' (t l) +
        ∑ m' ∈ univ.filter (· ≠ m), A₂ m' (t l) +
        ∑ l' ∈ univ.filter (· ≠ l), ∑ m', A₃ m' (t l) (t l') := by
    intro t
    have hy : ∀ y, ind ((clCode T t).d₁ l m y ≠ c) + ind ((clCode T t).d c y ≠ (l, m)) ≤
        2 * ind (¬ T (t l).1 ((t l).2.1 m) ((t l).2.2 c) y) +
        ∑ c' ∈ univ.filter (· ≠ c), ind (T (t l).1 ((t l).2.1 m) ((t l).2.2 c') y) +
        ∑ m' ∈ univ.filter (· ≠ m), ind (T (t l).1 ((t l).2.1 m') ((t l).2.2 c) y) +
        ∑ l' ∈ univ.filter (· ≠ l), ∑ m', ind (T (t l').1 ((t l').2.1 m') ((t l').2.2 c) y) := by
      intro y
      have h₁ := ind_cfUniq_ne_le (fun c' => T (t l).1 ((t l).2.1 m) ((t l).2.2 c') y) 0 c
      have h₂ := ind_cfUniq_ne_le
        (fun p : Fin Mb × Fin Mm => T (t p.1).1 ((t p.1).2.1 p.2) ((t p.1).2.2 c) y) (0, 0) (l, m)
      rw [sum_filter_prod_ne (fun p : Fin Mb × Fin Mm =>
        ind (T (t p.1).1 ((t p.1).2.1 p.2) ((t p.1).2.2 c) y)) l m] at h₂
      have e₁ : (clCode T t).d₁ l m y =
          cfUniq (fun c' => T (t l).1 ((t l).2.1 m) ((t l).2.2 c') y) 0 := rfl
      have e₂ : (clCode T t).d c y = cfUniq (fun p : Fin Mb × Fin Mm =>
          T (t p.1).1 ((t p.1).2.1 p.2) ((t p.1).2.2 c) y) (0, 0) := rfl
      rw [e₁, e₂]
      linarith
    calc (clCode T t).err V l c m ≤ ∑ y, V ((t l).2.1 m, (t l).2.2 c) y *
          (2 * ind (¬ T (t l).1 ((t l).2.1 m) ((t l).2.2 c) y) +
          ∑ c' ∈ univ.filter (· ≠ c), ind (T (t l).1 ((t l).2.1 m) ((t l).2.2 c') y) +
          ∑ m' ∈ univ.filter (· ≠ m), ind (T (t l).1 ((t l).2.1 m') ((t l).2.2 c) y) +
          ∑ l' ∈ univ.filter (· ≠ l), ∑ m', ind (T (t l').1 ((t l').2.1 m') ((t l').2.2 c) y)) :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hy y) ((hV _).nonneg y)
      _ = _ := by
          simp only [mul_add, sum_add_distrib, A₀, A₁, A₂, A₃, mul_sum]
          congr 1
          · congr 1
            · congr 1
              · refine sum_congr rfl fun y _ => by ring
              · rw [sum_comm]
            · rw [sum_comm]
          · rw [sum_comm]
            refine sum_congr rfl fun l' _ => ?_
            rw [sum_comm]
  -- the expectations
  have hE₀ : ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => ρ) t * A₀ (t l) ≤ c₀ := by
    rw [sum_piLaw_mul_eval hνr l A₀]
    refine le_trans (le_of_eq ?_) hc₀
    exact rowLaw_eval hPa hPb m c fun u a b => ∑ y, V (a, b) y * ind (¬ T u a b y)
  have hE₁ : ∀ c' ∈ univ.filter (· ≠ c), ∑ t : Fin Mb → CLRow Mb Mm U' A' B',
      piLaw (fun _ => ρ) t * A₁ c' (t l) ≤ e₂ := by
    intro c' hc'
    have hne : c ≠ c' := fun h => (mem_filter.mp hc').2 h.symm
    rw [sum_piLaw_mul_eval hνr l (A₁ c')]
    have h := rowLaw_eval_b (pu := pu) hPa hPb m hne fun u a b b' =>
      ∑ y, V (a, b) y * ind (T u a b' y)
    refine le_trans (le_of_eq h) ?_
    refine (sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hu.nonneg u)).trans
      (le_of_eq (by rw [← sum_mul, hu.sum_eq_one, one_mul]))
    refine (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((hPa u).nonneg a)).trans
      (le_of_eq (by rw [← sum_mul, (hPa u).sum_eq_one, one_mul]))
    refine (sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ ((hPb u).nonneg b)).trans
      (le_of_eq (by rw [← sum_mul, (hPb u).sum_eq_one, one_mul]))
    have hsw : ∑ b', Pb u b' * ∑ y, V (a, b) y * ind (T u a b' y) =
        ∑ y, V (a, b) y * ∑ b', Pb u b' * ind (T u a b' y) := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun y _ => sum_congr rfl fun b' _ => by ring
    rw [hsw]
    exact hsumV a b e₂ _ (he₂ u a)
  have hE₂ : ∀ m' ∈ univ.filter (· ≠ m), ∑ t : Fin Mb → CLRow Mb Mm U' A' B',
      piLaw (fun _ => ρ) t * A₂ m' (t l) ≤ e₁ := by
    intro m' hm'
    have hne : m ≠ m' := fun h => (mem_filter.mp hm').2 h.symm
    rw [sum_piLaw_mul_eval hνr l (A₂ m')]
    have h := rowLaw_eval_a (pu := pu) hPa hPb hne c fun u a a' b =>
      ∑ y, V (a, b) y * ind (T u a' b y)
    refine le_trans (le_of_eq h) ?_
    refine (sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hu.nonneg u)).trans
      (le_of_eq (by rw [← sum_mul, hu.sum_eq_one, one_mul]))
    refine (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((hPa u).nonneg a)).trans
      (le_of_eq (by rw [← sum_mul, (hPa u).sum_eq_one, one_mul]))
    have hsw : ∑ a', Pa u a' * ∑ b, Pb u b * ∑ y, V (a, b) y * ind (T u a' b y) =
        ∑ b, Pb u b * ∑ y, V (a, b) y * ∑ a', Pa u a' * ind (T u a' b y) := by
      simp only [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun b _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun y _ => sum_congr rfl fun a' _ => by ring
    rw [hsw]
    refine (sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ ((hPb u).nonneg b)).trans
      (le_of_eq (by rw [← sum_mul, (hPb u).sum_eq_one, one_mul]))
    exact hsumV a b e₁ _ fun y => he₁ u b y
  have hE₃ : ∀ l' ∈ univ.filter (· ≠ l), ∀ m' : Fin Mm, ∑ t : Fin Mb → CLRow Mb Mm U' A' B',
      piLaw (fun _ => ρ) t * A₃ m' (t l) (t l') ≤ e₃ := by
    intro l' hl' m'
    have hne : l ≠ l' := fun h => (mem_filter.mp hl').2 h.symm
    rw [sum_piLaw_mul_eval₂' hνr hne (A₃ m')]
    refine (sum_le_sum fun R _ => mul_le_mul_of_nonneg_left ?_ (hρP.nonneg R)).trans
      (le_of_eq (by rw [← sum_mul, hρP.sum_eq_one, one_mul]))
    have hsw : ∑ R', ρ R' * A₃ m' R R' = ∑ y, V (R.2.1 m, R.2.2 c) y *
        ∑ R', ρ R' * ind (T R'.1 (R'.2.1 m') (R'.2.2 c) y) := by
      simp only [A₃, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun y _ => sum_congr rfl fun R' _ => by ring
    rw [hsw]
    refine hsumV _ _ e₃ _ fun y => ?_
    refine le_trans (le_of_eq ?_) (he₃ y)
    exact rowLaw_eval hPa hPb m' c fun u a b => ind (T u a b y)
  -- the cardinalities
  have hcb : ((univ.filter (· ≠ c) : Finset (Fin Mb)).card : ℝ) = (Mb : ℝ) - 1 := by
    have : 0 < Mb := Fin.pos c
    rw [filter_ne', card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin, Nat.cast_sub this]
    simp
  have hcl : ((univ.filter (· ≠ l) : Finset (Fin Mb)).card : ℝ) = (Mb : ℝ) - 1 := by
    have : 0 < Mb := Fin.pos l
    rw [filter_ne', card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin, Nat.cast_sub this]
    simp
  have hcm : ((univ.filter (· ≠ m) : Finset (Fin Mm)).card : ℝ) = (Mm : ℝ) - 1 := by
    have : 0 < Mm := Fin.pos m
    rw [filter_ne', card_erase_of_mem (mem_univ m), card_univ, Fintype.card_fin, Nat.cast_sub this]
    simp
  calc _ ≤ ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => ρ) t *
        (2 * A₀ (t l) + ∑ c' ∈ univ.filter (· ≠ c), A₁ c' (t l) +
          ∑ m' ∈ univ.filter (· ≠ m), A₂ m' (t l) +
          ∑ l' ∈ univ.filter (· ≠ l), ∑ m', A₃ m' (t l) (t l')) :=
        sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hpt t) (hν.nonneg t)
    _ = 2 * ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => ρ) t * A₀ (t l) +
        ∑ c' ∈ univ.filter (· ≠ c), ∑ t : Fin Mb → CLRow Mb Mm U' A' B',
          piLaw (fun _ => ρ) t * A₁ c' (t l) +
        ∑ m' ∈ univ.filter (· ≠ m), ∑ t : Fin Mb → CLRow Mb Mm U' A' B',
          piLaw (fun _ => ρ) t * A₂ m' (t l) +
        ∑ l' ∈ univ.filter (· ≠ l), ∑ m', ∑ t : Fin Mb → CLRow Mb Mm U' A' B',
          piLaw (fun _ => ρ) t * A₃ m' (t l) (t l') := by
        simp only [mul_add, sum_add_distrib, mul_sum]
        congr 1
        · congr 1
          · congr 1
            · refine sum_congr rfl fun t _ => by ring
            · rw [sum_comm]
          · rw [sum_comm]
        · rw [sum_comm]
          refine sum_congr rfl fun l' _ => ?_
          rw [sum_comm]
    _ ≤ 2 * c₀ + ∑ _c' ∈ univ.filter (· ≠ c), e₂ + ∑ _m' ∈ univ.filter (· ≠ m), e₁ +
        ∑ _l' ∈ univ.filter (· ≠ l), ∑ _m' : Fin Mm, e₃ := by
        refine add_le_add (add_le_add (add_le_add (by linarith) (sum_le_sum hE₁))
          (sum_le_sum hE₂)) (sum_le_sum fun l' hl' => sum_le_sum fun m' _ => hE₃ l' hl' m')
    _ = _ := by
        simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin, hcb, hcm, hcl]
        ring

/-- An average of bounded terms is bounded. -/
lemma sum_mul_avg_le {I T' : Type*} [Fintype I] [Fintype T'] {ν : T' → ℝ} (g : I → T' → ℝ) {K b : ℝ}
    (hK : (Fintype.card I : ℝ) = K) (hK0 : 0 < K) (h : ∀ i, ∑ t, ν t * g i t ≤ b) :
    ∑ t, ν t * ((∑ i, g i t) / K) ≤ b := by
  have e : ∑ t, ν t * ((∑ i, g i t) / K) = (∑ i, ∑ t, ν t * g i t) / K := by
    simp only [mul_div_assoc', sum_div, mul_sum]
    rw [sum_comm]
  rw [e, div_le_iff₀ hK0]
  calc _ ≤ ∑ _i : I, b := sum_le_sum fun i _ => h i
    _ = b * K := by
      rw [sum_const, card_univ, nsmul_eq_mul, hK]
      ring

/-- **The random coding bound for the code of one block.** -/
theorem exists_clBlock_le {V : A' × B' → Y' → ℝ} {T : U' → A' → B' → Y' → Prop} (hu : IsPMF pu)
    (hPa : IsChannel Pa) (hPb : IsChannel Pb) (hV : IsChannel V) {c₀ e₁ e₂ e₃ : ℝ}
    (hc₀ : ∑ u, pu u * ∑ a, Pa u a * ∑ b, Pb u b * ∑ y, V (a, b) y * ind (¬ T u a b y) ≤ c₀)
    (he₂ : ∀ u a y, ∑ b, Pb u b * ind (T u a b y) ≤ e₂)
    (he₁ : ∀ u b y, ∑ a, Pa u a * ind (T u a b y) ≤ e₁)
    (he₃ : ∀ y, ∑ u, pu u * ∑ a, Pa u a * ∑ b, Pb u b * ind (T u a b y) ≤ e₃) :
    ∃ C : CLBlock Mb Mm A' B' Y', C.avgErr V ≤
      3 * (2 * c₀ + ((Mb : ℝ) - 1) * e₂ + ((Mm : ℝ) - 1) * e₁ + ((Mb : ℝ) - 1) * Mm * e₃) := by
  classical
  have hρP : IsPMF (rowLaw (Mb := Mb) (Mm := Mm) pu Pa Pb) := rowLaw_isPMF hu hPa hPb
  have hν : IsPMF (piLaw fun _ : Fin Mb => rowLaw (Mb := Mb) (Mm := Mm) pu Pa Pb) :=
    piLaw_isPMF fun _ => hρP
  have hb : (0 : ℝ) < Mb := by exact_mod_cast NeZero.pos Mb
  have hm : (0 : ℝ) < Mm := by exact_mod_cast NeZero.pos Mm
  set β := 2 * c₀ + ((Mb : ℝ) - 1) * e₂ + ((Mm : ℝ) - 1) * e₁ + ((Mb : ℝ) - 1) * Mm * e₃ with hβ
  have hE := sum_clCode_err_le (Mb := Mb) (Mm := Mm) hu hPa hPb hV hc₀ he₂ he₁ he₃
  have h₁ : ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => rowLaw pu Pa Pb) t *
      ((∑ c, ∑ m, (clCode T t).err V 0 c m) / ((Mb : ℝ) * Mm)) ≤ β := by
    have h := sum_mul_avg_le (I := Fin Mb × Fin Mm) (ν := piLaw fun _ => rowLaw pu Pa Pb)
      (K := (Mb : ℝ) * Mm) (b := β) (fun p t => (clCode T t).err V 0 p.1 p.2)
      (by simp) (by positivity) fun p => hE 0 p.1 p.2
    simpa only [Fintype.sum_prod_type] using h
  have h₂ : ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => rowLaw pu Pa Pb) t *
      ((∑ l, ∑ c, ∑ m, (clCode T t).err V l c m) / ((Mb : ℝ) * Mb * Mm)) ≤ β := by
    have h := sum_mul_avg_le (I := Fin Mb × Fin Mb × Fin Mm) (ν := piLaw fun _ => rowLaw pu Pa Pb)
      (K := (Mb : ℝ) * Mb * Mm) (b := β) (fun p t => (clCode T t).err V p.1 p.2.1 p.2.2)
      (by simp; ring) (by positivity) fun p => hE p.1 p.2.1 p.2.2
    simpa only [Fintype.sum_prod_type] using h
  have h₃ : ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => rowLaw pu Pa Pb) t *
      ((∑ l, (clCode T t).err V l 0 0) / (Mb : ℝ)) ≤ β :=
    sum_mul_avg_le (I := Fin Mb) (ν := piLaw fun _ => rowLaw pu Pa Pb)
      (K := (Mb : ℝ)) (b := β) (fun l t => (clCode T t).err V l 0 0)
      (by simp) hb fun l => hE l 0 0
  have htot : ∑ t : Fin Mb → CLRow Mb Mm U' A' B', piLaw (fun _ => rowLaw pu Pa Pb) t *
      (clCode T t).avgErr V ≤ 3 * β := by
    simp only [CLBlock.avgErr, mul_add, sum_add_distrib]
    linarith
  obtain ⟨t, ht⟩ := exists_le_of_sum_mul_le hν htot
  exact ⟨clCode T t, ht⟩

end Row

/-! ### The tests and the rates -/

section Gaps

variable {U X₁ X₂ Y : Type*} [Fintype U] [Fintype X₁] [Fintype X₂] [Fintype Y] {pu : U → ℝ}
  {A : U → X₁ → ℝ} {B : U → X₂ → ℝ} {W : X₁ × X₂ → Y → ℝ} {n : ℕ}

/-- `n` uses of the channel. -/
def macSeq (W : X₁ × X₂ → Y → ℝ) (n : ℕ) : (Fin n → X₁) × (Fin n → X₂) → (Fin n → Y) → ℝ :=
  fun x y => ∏ i, W (x.1 i, x.2 i) (y i)

omit [Fintype X₁] [Fintype X₂] in
lemma macSeq_isChannel (hW : IsChannel W) (n : ℕ) : IsChannel (macSeq W n) := fun x =>
  seqChan_isChannel hW n fun i => (x.1 i, x.2 i)

/-- The law of `((U, X₁, X₂), Y)`. -/
def clLaw (pu : U → ℝ) (A : U → X₁ → ℝ) (B : U → X₂ → ℝ) (W : X₁ × X₂ → Y → ℝ) :
    (U × (X₁ × X₂)) × Y → ℝ :=
  jointOf (twIn pu A B) fun t => W t.2

lemma clLaw_isPMF (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    IsPMF (clLaw pu A B W) :=
  jointOf_isPMF (jointOf_isPMF hu fun k => (hA k).prodDist (hB k)) fun _ => hW _

/-- A sum over sequences of inputs is a sum over the sequences of the components. -/
lemma sum_cl_inputs (F : (Fin n → U × (X₁ × X₂)) → ℝ) :
    ∑ t, F t = ∑ u : Fin n → U, ∑ a : Fin n → X₁, ∑ b : Fin n → X₂,
      F fun i => (u i, (a i, b i)) := by
  calc ∑ t, F t = ∑ u, ∑ s, F (zipSeq u s) := sum_zip F
    _ = _ := sum_congr rfl fun u _ => sum_zip fun s => F (zipSeq u s)

omit [Fintype U] [Fintype X₁] [Fintype X₂] in
/-- The i.i.d. law of the inputs. -/
lemma iidPMF_twIn (u : Fin n → U) (a : Fin n → X₁) (b : Fin n → X₂) :
    iidPMF (twIn pu A B) n (fun i => (u i, (a i, b i))) =
      iidPMF pu n u * (seqChan A n u a * seqChan B n u b) := by
  simp only [iidPMF, seqChan, twIn, jointOf, prodDist, ← prod_mul_distrib]

/-- **The sum over all the sequences of a block is an i.i.d. expectation.** -/
theorem sum_cl_all (G : (Fin n → U) → (Fin n → X₁) → (Fin n → X₂) → (Fin n → Y) → ℝ) :
    ∑ u, iidPMF pu n u * ∑ a, seqChan A n u a * ∑ b, seqChan B n u b *
      ∑ y, macSeq W n (a, b) y * G u a b y =
    ∑ ω, iidPMF (clLaw pu A B W) n ω * G (fun i => (ω i).1.1) (fun i => (ω i).1.2.1)
      (fun i => (ω i).1.2.2) (fun i => (ω i).2) := by
  rw [sum_zip, sum_cl_inputs]
  simp only [mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
    sum_congr rfl fun y _ => ?_
  have h : iidPMF (clLaw pu A B W) n (zipSeq (fun i => (u i, (a i, b i))) y) =
      iidPMF pu n u * (seqChan A n u a * (seqChan B n u b * macSeq W n (a, b) y)) := by
    simp only [iidPMF, seqChan, macSeq, clLaw, twIn, jointOf, prodDist, zipSeq,
      ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by ring
  rw [h]
  simp only [zipSeq]
  ring

/-- The test of the block. -/
def clT (μ : (U × (X₁ × X₂)) × Y → ℝ) (n : ℕ) (ε : ℝ) (u : Fin n → U) (a : Fin n → X₁)
    (b : Fin n → X₂) (y : Fin n → Y) : Prop :=
  (fun i => ((u i, (a i, b i)), y i)) ∈ robustTypicalSet μ n ε

/-- The time sharing variable. -/
abbrev clU (z : (U × (X₁ × X₂)) × Y) : U := z.1.1

/-- The first input. -/
abbrev clX₁ (z : (U × (X₁ × X₂)) × Y) : X₁ := z.1.2.1

/-- The second input. -/
abbrev clX₂ (z : (U × (X₁ × X₂)) × Y) : X₂ := z.1.2.2

/-- The gap of a wrong codeword of sender 2: `I(X₂; Y | X₁, U)`. -/
def clGap₂ (μ : (U × (X₁ × X₂)) × Y → ℝ) : ℝ :=
  twGap μ (pair (pair clU clX₁) Prod.snd) clU clX₂

/-- The correction to `clGap₂`. -/
def clErr₂ (μ : (U × (X₁ × X₂)) × Y → ℝ) : ℝ :=
  twErr μ (pair (pair clU clX₁) Prod.snd) clU clX₂

/-- The gap of a wrong codeword of sender 1: `I(X₁; Y | X₂, U)`. -/
def clGap₁ (μ : (U × (X₁ × X₂)) × Y → ℝ) : ℝ :=
  twGap μ (pair (pair clU clX₂) Prod.snd) clU clX₁

/-- The correction to `clGap₁`. -/
def clErr₁ (μ : (U × (X₁ × X₂)) × Y → ℝ) : ℝ :=
  twErr μ (pair (pair clU clX₂) Prod.snd) clU clX₁

/-- The gap of a wrong state: `I(U, X₁, X₂; Y)`. -/
def clGap₃ (μ : (U × (X₁ × X₂)) × Y → ℝ) : ℝ :=
  H[Prod.snd ; μ] + H[Prod.fst ; μ] - H[fun z => (z.2, z.1) ; μ]

/-- The correction to `clGap₃`. -/
def clErr₃ (μ : (U × (X₁ × X₂)) × Y → ℝ) : ℝ :=
  H[fun z => (z.2, z.1) ; μ] + H[Prod.snd ; μ] + H[Prod.fst ; μ]

lemma clErr₃_nonneg {μ : (U × (X₁ × X₂)) × Y → ℝ} (hμ : IsPMF μ) : 0 ≤ clErr₃ μ := by
  have h₁ := entropyRV_nonneg hμ (fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1))
  have h₂ := entropyRV_nonneg hμ (Prod.snd : (U × (X₁ × X₂)) × Y → Y)
  have h₃ := entropyRV_nonneg hμ (Prod.fst : (U × (X₁ × X₂)) × Y → U × (X₁ × X₂))
  simp only [clErr₃]
  linarith

lemma clLaw_dist_fst (hW : IsChannel W) : dist (clLaw pu A B W) Prod.fst = twIn pu A B :=
  dist_jointOf_fst fun _ => hW _

lemma clLaw_dist₂ (hW : IsChannel W) :
    dist (clLaw pu A B W) (pair (pair clU clX₂) clX₁) = jointOf (jointOf pu B) fun v => A v.1 := by
  have e' : pair (pair (clU : (U × (X₁ × X₂)) × Y → U) clX₂) clX₁ =
      (fun t : U × (X₁ × X₂) => ((t.1, t.2.2), t.2.1)) ∘ Prod.fst := rfl
  rw [e', dist_comp_eq, clLaw_dist_fst hW]
  exact dist_twIn₂

lemma clLaw_dist₁ (hW : IsChannel W) :
    dist (clLaw pu A B W) (pair (pair clU clX₁) clX₂) = jointOf (jointOf pu A) fun v => B v.1 := by
  have e' : pair (pair (clU : (U × (X₁ × X₂)) × Y → U) clX₁) clX₂ =
      (fun t : U × (X₁ × X₂) => ((t.1, t.2.1), t.2.2)) ∘ Prod.fst := rfl
  rw [e', dist_comp_eq, clLaw_dist_fst hW]
  exact dist_twIn₁

/-- `clGap₂` is `I(X₂; Y | X₁, U)`. -/
lemma clGap₂_eq (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    clGap₂ (clLaw pu A B W) =
      I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ; clLaw pu A B W] :=
  twGap_eq (clLaw_isPMF hu hA hB hW)
    (tw_cond (clLaw_isPMF hu hA hB hW) hB hA (clLaw_dist₁ hW)).2

/-- `clGap₁` is `I(X₁; Y | X₂, U)`. -/
lemma clGap₁_eq (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    clGap₁ (clLaw pu A B W) =
      I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ; clLaw pu A B W] :=
  twGap_eq (clLaw_isPMF hu hA hB hW)
    (tw_cond (clLaw_isPMF hu hA hB hW) hA hB (clLaw_dist₂ hW)).2

/-- `clGap₃` is `I(X₁, X₂; Y)`, since `U → (X₁, X₂) → Y` is a Markov chain. -/
lemma clGap₃_eq (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    clGap₃ (clLaw pu A B W) = I[fun z => z.1.2 : Prod.snd ; clLaw pu A B W] := by
  have hμ := clLaw_isPMF hu hA hB hW
  set μ := clLaw pu A B W with hμd
  have hc : H[Prod.snd | Prod.fst ; μ] = H[Prod.snd | fun z => z.1.2 ; μ] := by
    refine condEntropy_eq_comp_of_channel hμ Prod.fst Prod.snd Prod.snd (κ := W) hW ?_
    rw [show pair (Prod.fst : (U × (X₁ × X₂)) × Y → _) Prod.snd = id from rfl, dist_id]
    rw [hμd, clLaw_dist_fst hW]
    rfl
  have h₁ := condEntropy_eq_sub hμ (Prod.snd : (U × (X₁ × X₂)) × Y → Y) Prod.fst
  have h₂ := condEntropy_eq_sub hμ (Prod.snd : (U × (X₁ × X₂)) × Y → Y) fun z => z.1.2
  have h₃ : H[fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1) ; μ] = H[pair Prod.fst Prod.snd ; μ] :=
    entropyRV_eq_of_injective μ Prod.swap Prod.swap_injective fun _ => rfl
  have h₄ := mutualInfo_eq_entropy_sub_condEntropy' hμ (X := fun z : (U × (X₁ × X₂)) × Y => z.1.2)
    (Y := Prod.snd)
  rw [clGap₃, h₃, h₄]
  linarith

/-- `I(X₁, X₂; Y)` is the mutual information of the channel for the law of the inputs. -/
lemma cl_info₃ (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W) :
    I[fun z => z.1.2 : Prod.snd ; clLaw pu A B W] =
      mutualInfoOf (dist (twIn pu A B) Prod.snd) W := by
  have hμ := clLaw_isPMF hu hA hB hW
  have hin : IsPMF (twIn pu A B) := jointOf_isPMF hu fun k => (hA k).prodDist (hB k)
  have hd : dist (clLaw pu A B W) (pair (fun z : (U × (X₁ × X₂)) × Y => z.1.2) Prod.snd) =
      jointOf (dist (twIn pu A B) Prod.snd) W :=
    dist_jointOf_map (Q := twIn pu A B) Prod.snd W
  have hJ := jointOf_isPMF (hin.dist (Prod.snd : U × (X₁ × X₂) → X₁ × X₂)) hW
  have e : (Prod.snd : (U × (X₁ × X₂)) × Y → Y) =
      (Prod.snd : (X₁ × X₂) × Y → Y) ∘ pair (fun z : (U × (X₁ × X₂)) × Y => z.1.2) Prod.snd := rfl
  rw [mutualInfo_eq_entropy_sub_condEntropy' hμ, mutualInfoOf,
    mutualInfo_eq_entropy_sub_condEntropy' hJ]
  congr 1
  · rw [e, entropyRV, dist_comp_eq, hd]
    rfl
  · refine condEntropy_eq_of_dist_pair_eq hμ hJ (hd.trans ?_)
    rw [show pair (Prod.fst : (X₁ × X₂) × Y → _) Prod.snd = id from rfl, dist_id]

/-- The i.i.d. expectation of the failure of the test of the true sequences. -/
theorem sum_cl_miss_le (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W)
    {ε : ℝ} :
    ∑ u, iidPMF pu n u * ∑ a, seqChan A n u a * ∑ b, seqChan B n u b *
      ∑ y, macSeq W n (a, b) y * ind (¬ clT (clLaw pu A B W) n ε u a b y) ≤
    1 - prob (iidPMF (clLaw pu A B W) n) (robustTypicalSet (clLaw pu A B W) n ε) := by
  classical
  have hL := clLaw_isPMF hu hA hB hW
  rw [sum_cl_all fun u a b y => ind (¬ clT (clLaw pu A B W) n ε u a b y),
    ← prob_compl (iidPMF_isPMF hL n), prob]
  rw [← sum_filter_add_sum_filter_not univ (· ∈ robustTypicalSet (clLaw pu A B W) n ε)]
  have h₁ : ∑ ω ∈ univ.filter (· ∈ robustTypicalSet (clLaw pu A B W) n ε),
      iidPMF (clLaw pu A B W) n ω * ind (¬ clT (clLaw pu A B W) n ε (fun i => (ω i).1.1)
        (fun i => (ω i).1.2.1) (fun i => (ω i).1.2.2) (fun i => (ω i).2)) = 0 :=
    sum_eq_zero fun ω hω =>
      mul_eq_zero_of_right _ (ind_of_neg (not_not.mpr (mem_filter.mp hω).2))
  rw [h₁, zero_add]
  refine (sum_le_sum fun ω _ => mul_le_of_le_one_right ((iidPMF_isPMF hL n).nonneg ω)
    (ind_le_one _)).trans (le_of_eq ?_)
  refine sum_congr ?_ fun _ _ => rfl
  ext ω
  simp

/-- **The random coding bound in terms of the gaps.** -/
theorem exists_clBlock_gaps {Mb Mm : ℕ} [NeZero Mb] [NeZero Mm] (hu : IsPMF pu) (hA : IsChannel A)
    (hB : IsChannel B) (hW : IsChannel W) (ε : ℝ) :
    ∃ C : CLBlock Mb Mm (Fin n → X₁) (Fin n → X₂) (Fin n → Y), C.avgErr (macSeq W n) ≤
      3 * (2 * (1 - prob (iidPMF (clLaw pu A B W) n) (robustTypicalSet (clLaw pu A B W) n ε)) +
        ((Mb : ℝ) - 1) * exp (-(n * (clGap₂ (clLaw pu A B W) - clErr₂ (clLaw pu A B W) * ε))) +
        ((Mm : ℝ) - 1) * exp (-(n * (clGap₁ (clLaw pu A B W) - clErr₁ (clLaw pu A B W) * ε))) +
        ((Mb : ℝ) - 1) * Mm * exp (-(n * (clGap₃ (clLaw pu A B W) -
          clErr₃ (clLaw pu A B W) * ε)))) := by
  classical
  have hμ := clLaw_isPMF hu hA hB hW
  set μ := clLaw pu A B W with hμd
  have hAs := seqChan_isChannel hA n
  have hBs := seqChan_isChannel hB n
  have c₂ := (tw_cond hμ hB hA (clLaw_dist₁ hW)).1
  have c₁ := (tw_cond hμ hA hB (clLaw_dist₂ hW)).1
  refine exists_clBlock_le (T := clT μ n ε) (iidPMF_isPMF hu n) hAs hBs (macSeq_isChannel hW n)
    (sum_cl_miss_le hu hA hB hW) ?_ ?_ ?_
  · intro u a y
    have h := sum_fresh_tw hμ (r := pair (pair clU clX₁) Prod.snd) (q := clU) (x := clX₂)
      (fun t : (U × X₁) × Y => t.1.1) (fun _ => rfl) c₂ hB (n := n) (ε := ε)
      fun i => ((u i, a i), y i)
    refine le_trans (sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (ind_mono fun ht => ?_)
      ((hBs u).nonneg b)) h
    exact comp_mem_robustTypicalSet ht (pair (pair (pair clU clX₁) Prod.snd) clX₂)
  · intro u b y
    have h := sum_fresh_tw hμ (r := pair (pair clU clX₂) Prod.snd) (q := clU) (x := clX₁)
      (fun t : (U × X₂) × Y => t.1.1) (fun _ => rfl) c₁ hA (n := n) (ε := ε)
      fun i => ((u i, b i), y i)
    refine le_trans (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ind_mono fun ht => ?_)
      ((hAs u).nonneg a)) h
    exact comp_mem_robustTypicalSet ht (pair (pair (pair clU clX₂) Prod.snd) clX₁)
  · intro y
    have hL := hμ.dist fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1)
    have h := sum_fresh_const hL (n := n) (ε := ε)
      (fun y t => (fun i => (y i, t i)) ∈
        robustTypicalSet (dist μ fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1)) n ε)
      (fun _ _ h => h) y
    have e₁ : dist (dist μ fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1)) Prod.snd = twIn pu A B := by
      rw [← dist_comp_eq]
      exact clLaw_dist_fst hW
    rw [e₁] at h
    have e₂ : H[Prod.fst ; dist μ fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1)] = H[Prod.snd ; μ] :=
      entropyRV_dist _ _ _
    have e₃ : H[Prod.snd ; dist μ fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1)] = H[Prod.fst ; μ] :=
      entropyRV_dist _ _ _
    have e₄ : entropy (dist μ fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1)) =
        H[fun z => (z.2, z.1) ; μ] := rfl
    rw [e₂, e₃, e₄] at h
    have hsum : ∑ u, iidPMF pu n u * ∑ a, seqChan A n u a * ∑ b, seqChan B n u b *
        ind (clT μ n ε u a b y) = ∑ t, iidPMF (twIn pu A B) n t *
          ind (clT μ n ε (fun i => (t i).1) (fun i => (t i).2.1) (fun i => (t i).2.2) y) := by
      rw [sum_cl_inputs]
      simp only [mul_sum, iidPMF_twIn]
      refine sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    rw [hsum]
    refine (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ind_mono fun ht => ?_)
      ((iidPMF_isPMF (jointOf_isPMF hu fun k => (hA k).prodDist (hB k)) n).nonneg t)).trans
        (h.trans (le_of_eq ?_))
    · exact comp_mem_robustTypicalSet ht fun z : (U × (X₁ × X₂)) × Y => (z.2, z.1)
    · rw [clGap₃, clErr₃]
      congr 2
      ring

lemma clErr₁_nonneg {μ : (U × (X₁ × X₂)) × Y → ℝ} (hμ : IsPMF μ) : 0 ≤ clErr₁ μ :=
  twErr_nonneg hμ _ _ _

lemma clErr₂_nonneg {μ : (U × (X₁ × X₂)) × Y → ℝ} (hμ : IsPMF μ) : 0 ≤ clErr₂ μ :=
  twErr_nonneg hμ _ _ _

/-- **Codes for one block**, for rates, in nats, that satisfy the conditions of the notes. -/
theorem eventually_clBlock (hu : IsPMF pu) (hA : IsChannel A) (hB : IsChannel B) (hW : IsChannel W)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁)
    (h₁ : r₁ < I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ; clLaw pu A B W])
    (h₂ : r₂ < I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ; clLaw pu A B W])
    (h₃ : r₁ + r₂ < I[fun z => z.1.2 : Prod.snd ; clLaw pu A B W]) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ C : CLBlock ⌈exp (n * r₂)⌉₊ ⌈exp (n * r₁)⌉₊ (Fin n → X₁) (Fin n → X₂)
      (Fin n → Y), C.avgErr (macSeq W n) ≤ δ := by
  classical
  rw [← clGap₁_eq hu hA hB hW] at h₁
  rw [← clGap₂_eq hu hA hB hW] at h₂
  rw [← clGap₃_eq hu hA hB hW] at h₃
  have hμ := clLaw_isPMF hu hA hB hW
  set μ := clLaw pu A B W with hμd
  have hE₁ := clErr₁_nonneg hμ
  have hE₂ := clErr₂_nonneg hμ
  have hE₃ := clErr₃_nonneg hμ
  set g := min (min (clGap₁ μ - r₁) (clGap₂ μ - r₂)) (clGap₃ μ - (r₁ + r₂)) with hg
  have hg0 : 0 < g := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  set E := clErr₁ μ + clErr₂ μ + clErr₃ μ + 1 with hE
  have hEpos : 0 < E := by linarith
  set ε := g / E with hε
  have hεpos : 0 < ε := by positivity
  have hεE : E * ε = g := by
    rw [hε]
    field_simp
  have hg₁ : r₁ + clErr₁ μ * ε + ε ≤ clGap₁ μ := by
    have : g ≤ clGap₁ μ - r₁ := (min_le_left _ _).trans (min_le_left _ _)
    have h3 : (clErr₁ μ + 1) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
    linarith
  have hg₂ : r₂ + clErr₂ μ * ε + ε ≤ clGap₂ μ := by
    have : g ≤ clGap₂ μ - r₂ := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : (clErr₂ μ + 1) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
    linarith
  have hg₃ : (r₁ + r₂) + clErr₃ μ * ε + ε ≤ clGap₃ μ := by
    have : g ≤ clGap₃ μ - (r₁ + r₂) := min_le_right _ _
    have h3 : (clErr₃ μ + 1) * ε ≤ E * ε := mul_le_mul_of_nonneg_right (by linarith) hεpos.le
    linarith
  have hprob := tendsto_prob_robustTypicalSet hμ hεpos
  have hexp : Tendsto (fun n : ℕ => exp (-(n * ε))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_nat hεpos
  have hlim : Tendsto (fun n : ℕ => 3 * (2 * (1 - prob (iidPMF μ n) (robustTypicalSet μ n ε)) +
      exp (-(n * ε)) + exp (-(n * ε)) + 2 * exp (-(n * ε)))) atTop
      (𝓝 (3 * (2 * (1 - 1) + 0 + 0 + 2 * 0))) :=
    ((((tendsto_const_nhds.sub hprob).const_mul _).add hexp).add hexp |>.add
      (hexp.const_mul _)).const_mul _
  have hev := (tendsto_order.mp hlim).2 δ (by simpa using hδ)
  filter_upwards [hev] with n hn
  obtain ⟨C, hC⟩ := exists_clBlock_gaps (Mb := ⌈exp (n * r₂)⌉₊) (Mm := ⌈exp (n * r₁)⌉₊) (n := n)
    hu hA hB hW (W := W) ε
  refine ⟨C, hC.trans ?_⟩
  have hsub : ∀ r : ℝ, ((⌈exp (n * r)⌉₊ : ℕ) : ℝ) - 1 ≤ 1 * exp (n * r) := fun r => by
    have := Nat.ceil_lt_add_one (exp_pos (n * r)).le
    linarith
  have hone : ∀ r : ℝ, 0 ≤ r → (1 : ℝ) ≤ exp (n * r) := fun r hr =>
    one_le_exp (mul_nonneg (Nat.cast_nonneg n) hr)
  have hM : ((⌈exp (n * r₁)⌉₊ : ℕ) : ℝ) ≤ 2 * exp (n * r₁) := by
    have h := hsub r₁
    have h' := hone r₁ hr₁
    linarith
  have hb0 : (0 : ℝ) ≤ ((⌈exp (n * r₂)⌉₊ : ℕ) : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ((⌈exp (n * r₂)⌉₊ : ℕ) : ℝ) := by exact_mod_cast NeZero.one_le
    linarith
  have t₁ := superposition_mul_exp_le (hsub r₂) (by norm_num) hg₂
  have t₂ := superposition_mul_exp_le (hsub r₁) (by norm_num) hg₁
  have ha₃ : (((⌈exp (n * r₂)⌉₊ : ℕ) : ℝ) - 1) * ((⌈exp (n * r₁)⌉₊ : ℕ) : ℝ) ≤
      2 * exp (n * (r₁ + r₂)) := by
    calc _ ≤ (1 * exp (n * r₂)) * (2 * exp (n * r₁)) :=
          mul_le_mul (hsub r₂) hM (by positivity) (by positivity)
      _ = 2 * exp (n * (r₁ + r₂)) := by
          rw [mul_add, exp_add]
          ring
  have t₃ := superposition_mul_exp_le ha₃ (by norm_num) hg₃
  simp only [one_mul] at t₁ t₂
  linarith

end Gaps

end InfoTheory
