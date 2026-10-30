/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MutualInformation.Conditional

/-!
# Stochastic processes and their entropy rates

A discrete-time stochastic process `X₁, X₂, …` with values in a finite alphabet `α` is described
by its finite-dimensional laws: for each `n`, a pmf `p(x₁, …, xₙ)` on `Fin n → α`, and these laws
are consistent (summing out the last coordinate of `p(x₁, …, xₙ₊₁)` gives `p(x₁, …, xₙ)`). As in
the rest of the library, the coordinates are indexed from `0`.

## Main definitions

* `StochasticProcess α`: a consistent family of finite-dimensional laws.
* `StochasticProcess.jointEntropy P n`: `H(X₁, …, Xₙ)`.
* `StochasticProcess.condEntropyLast P n`: `H(Xₙ₊₁ | Xₙ, …, X₁)`.
* `StochasticProcess.IsStationary`: the laws are invariant under time shifts (4.1).
* `StochasticProcess.HasEntropyRate P h`: `(1/n) H(X₁, …, Xₙ) → h` (4.10).
* `StochasticProcess.HasCondEntropyRate P h`: `H(Xₙ | Xₙ₋₁, …, X₁) → h` (4.14).
* `StochasticProcess.entropyRate P`: the entropy rate of a stationary process.
* `StochasticProcess.map P φ`: the process `φ(X₁), φ(X₂), …`.

## Main statements

* `StochasticProcess.jointEntropy_eq_sum`: the chain rule
  `H(X₁, …, Xₙ) = ∑ᵢ H(Xᵢ | Xᵢ₋₁, …, X₁)`.
* `StochasticProcess.IsStationary.dist_shift`: for a stationary process, every window
  `(X_{l+1}, …, X_{l+n})` has the law of `(X₁, …, Xₙ)`.
* `StochasticProcess.IsStationary.condEntropyLast_antitone`,
  `StochasticProcess.IsStationary.hasCondEntropyRate`: Theorem 4.2.2.
* `cesaro_mean`: Theorem 4.2.3, the Cesàro mean of a convergent sequence converges.
* `StochasticProcess.IsStationary.hasEntropyRate`: Theorem 4.2.1, for a stationary process the
  limits (4.10) and (4.14) exist and are equal.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 4.1 and
  4.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Sums over sequences -/

lemma sum_snoc {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → α) → M) :
    ∑ x, f x = ∑ y : Fin n → α, ∑ a, f (Fin.snoc y a) := by
  rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma sum_cons {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → α) → M) :
    ∑ x, f x = ∑ a, ∑ y : Fin n → α, f (Fin.cons a y) := by
  rw [← (Fin.consEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_append {M : Type*} [AddCommMonoid M] (m n : ℕ) (f : (Fin (m + n) → α) → M) :
    ∑ x, f x = ∑ q : Fin m → α, ∑ w : Fin n → α, f (Fin.append q w) := by
  rw [← (Fin.appendEquiv m n).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The law of `(X₁, …, Xₙ)` under a law of `(X₁, …, Xₙ₊₁)`: sum out the last coordinate. -/
lemma dist_init_apply {n : ℕ} (ν : (Fin (n + 1) → α) → ℝ) (y : Fin n → α) :
    dist ν Fin.init y = ∑ a, ν (Fin.snoc y a) := by
  classical
  rw [dist, sum_snoc]
  simp only [Fin.init_snoc]
  rw [sum_eq_single y]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- The law of `(X₂, …, Xₙ₊₁)` under a law of `(X₁, …, Xₙ₊₁)`: sum out the first coordinate. -/
lemma dist_tail_apply {n : ℕ} (ν : (Fin (n + 1) → α) → ℝ) (y : Fin n → α) :
    dist ν Fin.tail y = ∑ a, ν (Fin.cons a y) := by
  classical
  rw [dist, sum_cons, sum_comm]
  simp only [Fin.tail_cons]
  rw [sum_eq_single y]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- **Theorem 4.2.3 (Cesàro mean).** If `aₙ → a`, then `(1/n) ∑_{i<n} aᵢ → a`. -/
theorem cesaro_mean {a : ℕ → ℝ} {l : ℝ} (h : Tendsto a atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (∑ i ∈ range n, a i) / n) atTop (𝓝 l) := by
  have := h.cesaro
  refine this.congr fun n => ?_
  rw [div_eq_inv_mul]

/-- **Definition (Section 4.1).** A stochastic process with values in a finite alphabet `α`,
described by its finite-dimensional laws `p(x₁, …, xₙ)`, which must be consistent. -/
structure StochasticProcess (α : Type*) [Fintype α] where
  /-- The law `p(x₁, …, xₙ) = Pr{(X₁, …, Xₙ) = (x₁, …, xₙ)}`. -/
  law : (n : ℕ) → (Fin n → α) → ℝ
  isPMF : ∀ n, IsPMF (law n)
  consistent : ∀ n (x : Fin n → α), ∑ a, law (n + 1) (Fin.snoc x a) = law n x

namespace StochasticProcess

variable (P : StochasticProcess α)

lemma law_cast {m n : ℕ} (h : m = n) (v : Fin n → α) : P.law m (v ∘ Fin.cast h) = P.law n v := by
  subst h; rfl

/-- The first `n` coordinates of `(X₁, …, Xₙ₊₁)` have law `p(x₁, …, xₙ)`. -/
lemma dist_init (n : ℕ) : dist (P.law (n + 1)) Fin.init = P.law n := by
  funext y; rw [dist_init_apply, P.consistent]

/-- The joint entropy `H(X₁, …, Xₙ)`. -/
def jointEntropy (n : ℕ) : ℝ := entropy (P.law n)

/-- The conditional entropy `H(Xₙ₊₁ | Xₙ, …, X₁)` of the next value given the past. -/
def condEntropyLast (n : ℕ) : ℝ :=
  H[fun x : Fin (n + 1) → α => x (Fin.last n) | Fin.init ; P.law (n + 1)]

lemma jointEntropy_nonneg (n : ℕ) : 0 ≤ P.jointEntropy n := entropy_nonneg (P.isPMF n)

lemma entropyRV_id {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) : H[id ; μ] = entropy μ := by
  rw [entropyRV, dist_id]

lemma condEntropyLast_eq (n : ℕ) :
    P.condEntropyLast n = P.jointEntropy (n + 1) - P.jointEntropy n := by
  rw [condEntropyLast, condEntropy_eq_sub (P.isPMF (n + 1))]
  have h1 : H[pair Fin.init (fun x : Fin (n + 1) → α => x (Fin.last n)) ; P.law (n + 1)] =
      H[id ; P.law (n + 1)] :=
    entropyRV_eq_of_injective _ (fun x : Fin (n + 1) → α => (Fin.init x, x (Fin.last n)))
      (fun x y h => by
        rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y]
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2]) (fun _ => rfl)
  rw [h1, entropyRV_id, entropyRV, P.dist_init]
  rfl

lemma condEntropyLast_nonneg (n : ℕ) : 0 ≤ P.condEntropyLast n :=
  condEntropy_nonneg (P.isPMF (n + 1)) _ _

lemma jointEntropy_zero : P.jointEntropy 0 = 0 := by
  have h := (P.isPMF 0).sum_eq_one
  rw [jointEntropy, entropy_eq_sum_negMulLog]
  rw [Fintype.sum_unique] at h ⊢
  rw [h, negMulLog_one]

/-- **The chain rule** `H(X₁, …, Xₙ) = ∑ᵢ H(Xᵢ | Xᵢ₋₁, …, X₁)`, (4.22). -/
theorem jointEntropy_eq_sum (n : ℕ) : P.jointEntropy n = ∑ i ∈ range n, P.condEntropyLast i := by
  induction n with
  | zero => simp [jointEntropy_zero]
  | succ n ih => rw [sum_range_succ, ← ih, condEntropyLast_eq]; ring

/-! ### Stationary processes -/

/-- **Definition (4.1).** A process is stationary if its laws are invariant under time shifts.
It suffices to require this for a shift by one: summing out the first coordinate of
`p(x₁, …, xₙ₊₁)` gives `p(x₁, …, xₙ)`. See `IsStationary.dist_shift` for arbitrary shifts. -/
def IsStationary : Prop := ∀ n (x : Fin n → α), ∑ a, P.law (n + 1) (Fin.cons a x) = P.law n x

variable {P}

/-- For a stationary process, `(X₂, …, Xₙ₊₁)` has the law of `(X₁, …, Xₙ)`. -/
lemma IsStationary.dist_tail (hP : P.IsStationary) (n : ℕ) :
    dist (P.law (n + 1)) Fin.tail = P.law n := by
  funext y; rw [dist_tail_apply, hP]

/-- Summing out the first `k` coordinates of a stationary process. -/
lemma IsStationary.sum_law_append (hP : P.IsStationary) (k n : ℕ) (w : Fin n → α) :
    ∑ q : Fin k → α, P.law (k + n) (Fin.append q w) = P.law n w := by
  induction k with
  | zero =>
    rw [Fintype.sum_unique, Subsingleton.elim (default : Fin 0 → α) Fin.elim0, Fin.elim0_append,
      law_cast]
  | succ k ih =>
    rw [sum_cons]
    simp only [Fin.append_cons, law_cast]
    rw [sum_comm]
    simp only [hP (k + n)]
    exact ih

/-- **(4.1)** For a stationary process, every window `(X_{k+1}, …, X_{k+n})` has the law of
`(X₁, …, Xₙ)`. -/
theorem IsStationary.dist_shift (hP : P.IsStationary) (k n : ℕ) :
    dist (P.law (k + n)) (fun x i => x (Fin.natAdd k i)) = P.law n := by
  classical
  funext w
  have hS : ∀ (q : Fin k → α) (w' : Fin n → α),
      (fun i => Fin.append q w' (Fin.natAdd k i)) = w' := fun q w' =>
    funext fun i => Fin.append_right q w' i
  rw [dist, sum_append]
  simp only [hS, sum_ite_eq', mem_univ, ite_true]
  exact hP.sum_law_append k n w

/-! ### Entropy rates -/

variable (P)

/-- **Definition (4.10).** The process has entropy rate `h` if `(1/n) H(X₁, …, Xₙ) → h`. -/
def HasEntropyRate (h : ℝ) : Prop :=
  Tendsto (fun n : ℕ => P.jointEntropy n / n) atTop (𝓝 h)

/-- **Definition (4.14).** `H(Xₙ | Xₙ₋₁, …, X₁) → h`. -/
def HasCondEntropyRate (h : ℝ) : Prop := Tendsto P.condEntropyLast atTop (𝓝 h)

lemma HasEntropyRate.unique {h₁ h₂ : ℝ} (h₁' : P.HasEntropyRate h₁) (h₂' : P.HasEntropyRate h₂) :
    h₁ = h₂ :=
  tendsto_nhds_unique h₁' h₂'

/-- The entropy rate of a stationary process, `lim H(Xₙ | Xₙ₋₁, …, X₁)`. -/
def entropyRate : ℝ := ⨅ n, P.condEntropyLast n

variable {P}

/-- **Theorem 4.2.2 (first part).** For a stationary process, `H(Xₙ | Xₙ₋₁, …, X₁)` is
decreasing in `n`, (4.16)–(4.17). -/
theorem IsStationary.condEntropyLast_antitone (hP : P.IsStationary) :
    Antitone P.condEntropyLast := by
  refine antitone_nat_of_succ_le fun n => ?_
  -- Work with `(X₁, …, Xₙ₊₂)`: `X₁`, the last value and the middle `(X₂, …, Xₙ₊₁)`.
  set μ := P.law (n + 2)
  have hμ : IsPMF μ := P.isPMF (n + 2)
  let A : (Fin (n + 2) → α) → α := fun x => x 0
  let B : (Fin (n + 2) → α) → α := fun x => x (Fin.last (n + 1))
  let C : (Fin (n + 2) → α) → (Fin n → α) := fun x => Fin.init (Fin.tail x)
  have hC : ∀ x, C x = Fin.tail (Fin.init x) := fun x => by
    funext i
    change x (Fin.castSucc i).succ = x (Fin.succ i).castSucc
    rw [Fin.succ_castSucc]
  have h1 : H[pair C A ; μ] = P.jointEntropy (n + 1) := by
    rw [entropyRV_eq_of_injective μ (X := Fin.init) (fun y : Fin (n + 1) → α => (Fin.tail y, y 0))
      (fun y z h => by
        rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail z]
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2])
      (fun x => by simp only [pair_apply, hC]; rfl), entropyRV, P.dist_init]
    rfl
  have h2 : H[pair C B ; μ] = P.jointEntropy (n + 1) := by
    rw [entropyRV_eq_of_injective μ (X := Fin.tail)
      (fun y : Fin (n + 1) → α => (Fin.init y, y (Fin.last n)))
      (fun y z h => by
        rw [← Fin.snoc_init_self y, ← Fin.snoc_init_self z]
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2])
      (fun x => by
        change (C x, B x) = (Fin.init (Fin.tail x), Fin.tail x (Fin.last n))
        simp only [C, B, Fin.tail, Fin.succ_last]), entropyRV, hP.dist_tail]
    rfl
  have h3 : H[C ; μ] = P.jointEntropy n := by
    have : C = Fin.init ∘ Fin.tail := rfl
    rw [entropyRV, this, dist_comp_eq, hP.dist_tail, P.dist_init]
    rfl
  have h4 : H[pair C (pair A B) ; μ] = P.jointEntropy (n + 2) := by
    rw [entropyRV_eq_of_injective μ (X := id) (Y := pair C (pair A B))
      (fun x : Fin (n + 2) → α => (Fin.init (Fin.tail x), (x 0, x (Fin.last (n + 1)))))
      (fun x y h => by
        simp only [Prod.mk.injEq] at h
        obtain ⟨hm, h0, hl⟩ := h
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simpa [Fin.succ_last] using hl
        · have := congrFun hm k
          simpa [Fin.init, Fin.tail] using this)
      (fun _ => rfl), entropyRV_id]
    rfl
  have hI := condMutualInfo_nonneg hμ A B C
  rw [condMutualInfo_eq hμ, h1, h2, h3, h4] at hI
  rw [condEntropyLast_eq, condEntropyLast_eq]
  linarith

/-- **Theorem 4.2.2.** For a stationary process, `H(Xₙ | Xₙ₋₁, …, X₁)` has a limit `H'(𝒳)`,
namely `entropyRate P`. -/
theorem IsStationary.hasCondEntropyRate (hP : P.IsStationary) :
    P.HasCondEntropyRate P.entropyRate :=
  tendsto_atTop_ciInf hP.condEntropyLast_antitone
    ⟨0, by rintro _ ⟨n, rfl⟩; exact P.condEntropyLast_nonneg n⟩

/-- **Theorem 4.2.1.** For a stationary process the limits (4.10) and (4.14) exist and are equal:
`H(𝒳) = H'(𝒳)`. -/
theorem IsStationary.hasEntropyRate (hP : P.IsStationary) : P.HasEntropyRate P.entropyRate := by
  have h := cesaro_mean hP.hasCondEntropyRate
  refine h.congr fun n => ?_
  rw [jointEntropy_eq_sum]

/-- The joint entropy is at least `n` times the entropy rate `inf H(Xₖ₊₁ | Xₖ, …, X₁)`. -/
lemma mul_entropyRate_le_jointEntropy (n : ℕ) : n * P.entropyRate ≤ P.jointEntropy n := by
  have hbdd : BddBelow (Set.range P.condEntropyLast) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact P.condEntropyLast_nonneg k⟩
  rw [P.jointEntropy_eq_sum]
  calc (n : ℝ) * P.entropyRate = ∑ _i ∈ range n, P.entropyRate := by simp
    _ ≤ _ := sum_le_sum fun k _ => ciInf_le hbdd k

/-! ### Functions of a process -/

variable (P)

/-- The process `Yᵢ = φ(Xᵢ)`. -/
def map (φ : α → β) : StochasticProcess β where
  law n := dist (P.law n) fun x => φ ∘ x
  isPMF n := (P.isPMF n).dist _
  consistent n y := by
    show ∑ b, dist (P.law (n + 1)) (fun x => φ ∘ x) (Fin.snoc y b) =
      dist (P.law n) (fun x => φ ∘ x) y
    rw [← dist_init_apply, ← dist_comp_eq]
    conv_rhs => rw [← P.dist_init n, ← dist_comp_eq]
    rfl

@[simp] lemma map_law (φ : α → β) (n : ℕ) : (P.map φ).law n = dist (P.law n) fun x => φ ∘ x :=
  rfl

variable {P}

/-- A function of a stationary process is stationary. -/
lemma IsStationary.map (hP : P.IsStationary) (φ : α → β) : (P.map φ).IsStationary := by
  intro n y
  rw [map_law, map_law, ← dist_tail_apply, ← dist_comp_eq]
  conv_rhs => rw [← hP.dist_tail n, ← dist_comp_eq]
  rfl

end StochasticProcess

end InfoTheory
