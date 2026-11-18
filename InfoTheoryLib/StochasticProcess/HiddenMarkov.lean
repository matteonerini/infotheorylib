/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StochasticProcess.Markov
public import InfoTheoryLib.MarkovChain.Basic
public import InfoTheoryLib.Entropy.Bounds

/-!
# Functions of Markov chains and hidden Markov models

Let `X₁, X₂, …` be a stationary Markov chain and `Yᵢ = φ(Xᵢ)`. The process `Y` is stationary, but
in general not Markov, and its entropy rate `H(𝒴)` is the limit of `H(Yₙ | Yₙ₋₁, …, Y₁)` from
above. Conditioning also on the first state `X₁` gives lower bounds converging to the same limit.

In a hidden Markov model, `Yᵢ` is instead drawn from `e(yᵢ | xᵢ)`, independently of everything
else given `Xᵢ`. The pairs `(Xᵢ, Yᵢ)` then form a stationary Markov chain and `Yᵢ` is a function of
it, so the same bounds hold.

## Main definitions

* `hmmUpper hμ hr φ n`: the upper bound `H(Yₙ₊₁ | Yₙ, …, Y₁)`.
* `hmmLower μ r φ n`: the lower bound `H(Yₙ₊₁ | Yₙ, …, Y₁, X₁)`.
* `hmmTrans r e`: the transition matrix `r(x'|x) e(y'|x')` of the pairs `(Xᵢ, Yᵢ)` of a hidden
  Markov model with emission probabilities `e(y|x)`.

## Main statements

* `markovChain_of_factorization`: if `p(q, w) = a(q, g(w)) b(w)`, then `q → g(w) → w` is a
  Markov chain.
* `markovLaw_append`: the law of a Markov chain splits at any time into a factor depending on the
  past and the present, and a factor depending on the present and the future.
* `hmmLower_le_entropyRate`: Lemma 4.5.1, `H(Yₙ | Yₙ₋₁, …, Y₂, X₁) ≤ H(𝒴)`.
* `tendsto_hmmUpper_sub_hmmLower`: Lemma 4.5.2, the gap between the bounds tends to `0`.
* `hmm_bounds`, `tendsto_hmmLower`: Theorem 4.5.1.
* `markovLaw_hmmTrans`: (4.75), the law of a hidden Markov model is the law of the Markov chain of
  the pairs `(Xᵢ, Yᵢ)`.
* `hiddenMarkov_bounds`, `tendsto_hiddenMarkov_lower`, `hmmLower_hmmTrans_eq`: the bounds of
  Theorem 4.5.1 for hidden Markov models, conditioning on the underlying state `X₁`.

## Implementation notes

The lower bound conditions on `(X₁, Y₁, …, Yₙ)`. Since `Y₁ = φ(X₁)`, this is the book's
`H(Yₙ₊₁ | Yₙ, …, Y₂, X₁)`, step (a) of (4.58).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 4.5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Conditional independence from a factorization -/

/-- If a law on a product factorizes as `ν(q, w) = a(q, g(w)) b(w)`, then `q → g(w) → w` is a
Markov chain: the first coordinate and the second are conditionally independent given `g(w)`. -/
theorem markovChain_of_factorization {δ γ : Type*} [Fintype δ] [Finite γ]
    {ν : β × δ → ℝ} (hν : IsPMF ν) {g : δ → γ} {a : β → γ → ℝ} {b : δ → ℝ}
    (h : ∀ q w, ν (q, w) = a q (g w) * b w) :
    MarkovChain ν Prod.fst (g ∘ Prod.snd) Prod.snd := by
  classical
  have := Fintype.ofFinite γ
  rw [markovChain_iff_mul hν]
  intro p z f
  set A := ∑ q, a q z
  set B := ∑ w, if g w = z then b w else 0
  have h3 : dist ν (pair Prod.fst (pair (g ∘ Prod.snd) Prod.snd)) (p, z, f) =
      if g f = z then a p z * b f else 0 := by
    rw [dist, Fintype.sum_prod_type]
    simp only [pair_apply, Function.comp_apply, Prod.mk.injEq]
    rw [sum_eq_single p (fun q _ hq => by simp [hq]) (by simp)]
    rw [sum_eq_single f (fun w _ hw => by simp [hw]) (by simp)]
    split_ifs with h1 h2 h2 <;> simp_all
  have hz : dist ν (g ∘ Prod.snd) z = A * B := by
    rw [dist, Fintype.sum_prod_type, sum_mul]
    refine sum_congr rfl fun q _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun w _ => ?_
    simp only [Function.comp_apply, h]
    split_ifs with hw <;> simp [hw]
  have hpz : dist ν (pair Prod.fst (g ∘ Prod.snd)) (p, z) = a p z * B := by
    rw [dist, Fintype.sum_prod_type, sum_eq_single p (fun q _ hq => by simp [hq]) (by simp)]
    rw [mul_sum]
    refine sum_congr rfl fun w _ => ?_
    simp only [pair_apply, Function.comp_apply, Prod.mk.injEq, true_and, h]
    split_ifs with hw <;> simp [hw]
  have hzf : dist ν (pair (g ∘ Prod.snd) Prod.snd) (z, f) =
      if g f = z then A * b f else 0 := by
    rw [dist, Fintype.sum_prod_type]
    simp only [pair_apply, Function.comp_apply, Prod.mk.injEq]
    split_ifs with hf
    · rw [sum_mul]
      refine sum_congr rfl fun q _ => ?_
      rw [sum_eq_single f (fun w _ hw => by simp [hw]) (by simp)]
      simp [hf, h]
    · refine sum_eq_zero fun q _ => sum_eq_zero fun w _ => ?_
      split_ifs with hw
      · exact absurd (hw.2 ▸ hw.1) hf
      · rfl
  rw [h3, hz, hpz, hzf]
  split_ifs <;> ring

/-- The law `μ ∘ e` pushed forward by the equivalence `e` is `μ`. -/
lemma dist_comp_equiv {Ω Ω' : Type*} [Fintype Ω] [Finite Ω'] (μ : Ω' → ℝ) (e : Ω ≃ Ω') :
    dist (fun ω => μ (e ω)) e = μ := by
  classical
  have := Fintype.ofFinite Ω'
  funext x
  rw [dist, ← e.symm.sum_comp]
  simp

/-! ### The Markov property across a split in time -/

variable {μ : α → ℝ} {r : α → α → ℝ}

omit [Fintype α] [Fintype β] in
/-- Splitting the law of a Markov chain at time `k`: with `q` the first `k` states and `w` the
following `s + 1` states, `p(q, w) = p(q, w₀) r(w₀, w₁) ⋯ r(wₛ₋₁, wₛ)`. -/
theorem markovLaw_append (k s : ℕ) (q : Fin k → α) (w : Fin (s + 1) → α) :
    markovLaw μ r (k + (s + 1)) (Fin.append q w) =
      markovLaw μ r (k + 1) (Fin.snoc q (w 0)) * pathProb r s w := by
  induction s with
  | zero =>
    have : (Fin.append q w : Fin (k + 1) → α) = Fin.snoc q (w 0) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, show Fin.last k = Fin.natAdd k (0 : Fin 1) from Fin.ext (by simp),
          Fin.append_right]
      · rw [Fin.snoc_castSucc]
        exact Fin.append_left q w j
    rw [this]
    simp [pathProb]
  | succ s ih =>
    obtain ⟨w', b, rfl⟩ : ∃ w' b, w = Fin.snoc w' b :=
      ⟨Fin.init w, w (Fin.last _), (Fin.snoc_init_self w).symm⟩
    have hl : Fin.append q w' (Fin.last (k + s)) = w' (Fin.last s) := by
      rw [show Fin.last (k + s) = Fin.natAdd k (Fin.last s) from Fin.ext (by simp),
        Fin.append_right]
    have h0 : (Fin.snoc w' b : Fin (s + 2) → α) 0 = w' 0 :=
      Fin.snoc_castSucc (α := fun _ => α) b w' 0
    have ih' := ih w'
    rw [Fin.append_snoc]
    change markovLaw μ r (k + s + 2) (Fin.snoc (Fin.append q w' : Fin (k + (s + 1)) → α) b) = _
    erw [markovLaw_snoc, hl, ih', pathProb_snoc, h0]
    ring

/-! ### Upper and lower bounds -/

lemma dist_markovLaw_init (hμ : IsPMF μ) (hr : IsStochastic r) (n : ℕ) :
    dist (markovLaw μ r (n + 1)) Fin.init = markovLaw μ r n :=
  (markovProcess μ r hμ hr).dist_init n

/-- The upper bound `H(Yₙ₊₁ | Yₙ, …, Y₁)` for the entropy rate of `Yᵢ = φ(Xᵢ)`. -/
def hmmUpper (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β) (n : ℕ) : ℝ :=
  ((markovProcess μ r hμ hr).map φ).condEntropyLast n

variable (μ r) in
/-- The lower bound `H(Yₙ₊₁ | Yₙ, …, Y₁, X₁)` for the entropy rate of `Yᵢ = φ(Xᵢ)`. -/
def hmmLower (φ : α → β) (n : ℕ) : ℝ :=
  H[fun w : Fin (n + 1) → α => φ (w (Fin.last n)) |
    fun w => (w 0, φ ∘ Fin.init w) ; markovLaw μ r (n + 1)]

/-- The upper bound computed from the law of `X₁, …, Xₙ₊₁`. -/
lemma hmmUpper_eq (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β) (n : ℕ) :
    hmmUpper hμ hr φ n = H[fun x : Fin (n + 1) → α => φ (x (Fin.last n)) |
      fun x => φ ∘ Fin.init x ; markovLaw μ r (n + 1)] := by
  refine condEntropy_eq_of_dist_pair_eq (((markovProcess μ r hμ hr).map φ).isPMF _)
    ((markovProcess μ r hμ hr).isPMF _) ?_
  rw [StochasticProcess.map_law, ← dist_comp_eq]
  rfl

variable (μ r) in
/-- The law on `(Fin k → α) × (Fin (n + 1) → α)` of the first `k` states and the next `n + 1`. -/
def windowLaw (k n : ℕ) : (Fin k → α) × (Fin (n + 1) → α) → ℝ :=
  fun qw => markovLaw μ r (k + (n + 1)) (Fin.append qw.1 qw.2)

omit [Fintype α] in
lemma windowLaw_eq (k n : ℕ) :
    windowLaw μ r k n = fun qw => markovLaw μ r (k + (n + 1)) (Fin.appendEquiv k (n + 1) qw) :=
  rfl

lemma windowLaw_isPMF (hμ : IsPMF μ) (hr : IsStochastic r) (k n : ℕ) :
    IsPMF (windowLaw μ r k n) := by
  refine ⟨fun qw => markovLaw_nonneg hμ hr _ _, ?_⟩
  rw [Fintype.sum_prod_type, ← sum_markovLaw hμ hr (k + (n + 1))]
  exact (sum_append k (n + 1) (markovLaw μ r (k + (n + 1)))).symm

lemma dist_windowLaw_append (k n : ℕ) :
    dist (windowLaw μ r k n) (Fin.appendEquiv k (n + 1)) = markovLaw μ r (k + (n + 1)) := by
  rw [windowLaw_eq]
  exact dist_comp_equiv (markovLaw μ r (k + (n + 1))) (Fin.appendEquiv k (n + 1))

lemma dist_windowLaw_snd (hμ : IsPMF μ) (hr : IsStochastic r) (hstat : IsStationaryDist r μ)
    (k n : ℕ) : dist (windowLaw μ r k n) Prod.snd = markovLaw μ r (n + 1) := by
  classical
  funext w
  rw [dist, Fintype.sum_prod_type, sum_comm]
  rw [sum_eq_single w (fun w' _ hw => by simp [hw]) (by simp)]
  simp only [ite_true]
  exact (markovProcess_isStationary hμ hr hstat).sum_law_append k (n + 1) w

lemma windowLaw_markovChain (hμ : IsPMF μ) (hr : IsStochastic r) (k n : ℕ) :
    MarkovChain (windowLaw μ r k n) Prod.fst ((fun w : Fin (n + 1) → α => w 0) ∘ Prod.snd)
      Prod.snd :=
  markovChain_of_factorization (windowLaw_isPMF hμ hr k n)
    (a := fun q z => markovLaw μ r (k + 1) (Fin.snoc q z)) (b := pathProb r n)
    fun q w => markovLaw_append k n q w

omit [Fintype α] [Fintype β] in
lemma init_append {k n : ℕ} (q : Fin k → α) (w : Fin (n + 1) → α) :
    Fin.init (Fin.append q w : Fin (k + (n + 1)) → α) = Fin.append q (Fin.init w) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    exact Fin.append_left q w j
  · rw [Fin.append_right]
    exact Fin.append_right q w j.castSucc

/-- The key step of Lemma 4.5.1: `H(Yₙ₊₁ | Yₙ, …, Y₁, X₁) ≤ H(Yₖ₊ₙ₊₁ | Yₖ₊ₙ, …, Y₁)` for
every `k`, (4.58)–(4.62). -/
theorem hmmLower_le_hmmUpper (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β)
    (hstat : IsStationaryDist r μ) (n k : ℕ) :
    hmmLower μ r φ n ≤ hmmUpper hμ hr φ (k + n) := by
  set ν := windowLaw μ r k n
  have hν : IsPMF ν := windowLaw_isPMF hμ hr k n
  let A' : (Fin k → α) × (Fin (n + 1) → α) → β := fun qw => φ (qw.2 (Fin.last n))
  let B' : (Fin k → α) × (Fin (n + 1) → α) → α × (Fin n → β) :=
    fun qw => (qw.2 0, φ ∘ Fin.init qw.2)
  let Z : (Fin k → α) × (Fin (n + 1) → α) → α := (fun w : Fin (n + 1) → α => w 0) ∘ Prod.snd
  -- (e) Stationarity: the lower bound is computed on the window `(Xₖ₊₁, …, Xₖ₊ₙ₊₁)`.
  have h1 : hmmLower μ r φ n = H[A' | B' ; ν] := by
    refine condEntropy_eq_of_dist_pair_eq ((markovProcess μ r hμ hr).isPMF _) hν ?_
    have : pair B' A' = (pair (fun w : Fin (n + 1) → α => (w 0, φ ∘ Fin.init w))
        (fun w => φ (w (Fin.last n)))) ∘ Prod.snd := rfl
    rw [this, dist_comp_eq, dist_windowLaw_snd hμ hr hstat]
    rfl
  -- (b) The Markov property: the earlier states `X₁, …, Xₖ` do not change the conditional
  -- entropy once `Xₖ₊₁` is known.
  have h2 : H[A' | B' ; ν] = H[A' | pair Prod.fst B' ; ν] := by
    have hci : I[Prod.fst : Prod.snd | Z ; ν] = 0 :=
      (condMutualInfo_eq_zero_iff hν _ _ _).2
        ((markovChain_iff_condIndep hν _ _ _).1 (windowLaw_markovChain hμ hr k n))
    have hle : I[Prod.fst : pair A' B' | Z ; ν] ≤ 0 := by
      have := condMutualInfo_comp_le hν Prod.fst Prod.snd Z
        (fun w : Fin (n + 1) → α => (φ (w (Fin.last n)), (w 0, φ ∘ Fin.init w)))
      rw [hci] at this
      exact this
    have hchain := chain_rule_condMutualInfo hν Prod.fst A' B' Z
    have hnn1 := condMutualInfo_nonneg hν Prod.fst B' Z
    have hnn2 := condMutualInfo_nonneg hν Prod.fst A' (pair B' Z)
    have h0 : I[A' : Prod.fst | pair B' Z ; ν] = 0 := by
      rw [condMutualInfo_comm hν]; linarith
    have e1 : H[A' | pair B' Z ; ν] = H[A' | B' ; ν] :=
      condEntropy_congr_right hν A' (fun b => (b, b.1)) (fun a b hab => (Prod.mk.inj hab).1)
        (fun _ => rfl)
    have e2 : H[A' | pair Prod.fst (pair B' Z) ; ν] = H[A' | pair Prod.fst B' ; ν] :=
      condEntropy_congr_right hν A' (fun qb => (qb.1, (qb.2, qb.2.1)))
        (fun a b hab => by
          simp only [Prod.mk.injEq] at hab
          exact Prod.ext hab.1 hab.2.1) (fun _ => rfl)
    rw [condMutualInfo, e1, e2] at h0
    linarith
  -- (c), (d) The states `X₁, …, Xₖ₊₁` determine `Y₁, …, Yₖ₊₁`, and conditioning reduces entropy.
  let G : (Fin k → α) × (α × (Fin n → β)) → Fin (k + n) → β :=
    fun qb => Fin.append (φ ∘ qb.1) qb.2.2
  have h3 : H[A' | pair Prod.fst B' ; ν] ≤ H[A' | G ∘ pair Prod.fst B' ; ν] :=
    condEntropy_le_condEntropy_comp hν A' _ G
  -- The right-hand side is `H(Yₖ₊ₙ₊₁ | Yₖ₊ₙ, …, Y₁)`.
  have h4 : H[A' | G ∘ pair Prod.fst B' ; ν] = hmmUpper hμ hr φ (k + n) := by
    rw [hmmUpper_eq]
    refine condEntropy_eq_of_dist_pair_eq hν ((markovProcess μ r hμ hr).isPMF _) ?_
    have : pair (G ∘ pair Prod.fst B') A' =
        (pair (fun x : Fin (k + n + 1) → α => φ ∘ Fin.init x)
          (fun x => φ (x (Fin.last (k + n))))) ∘ Fin.appendEquiv k (n + 1) := by
      funext qw
      refine Prod.ext ?_ ?_
      · change Fin.append (φ ∘ qw.1) (φ ∘ Fin.init qw.2) =
          φ ∘ Fin.init (Fin.append qw.1 qw.2 : Fin (k + (n + 1)) → α)
        rw [init_append]
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      · change φ (qw.2 (Fin.last n)) = φ (Fin.append qw.1 qw.2 (Fin.last (k + n)))
        rw [show Fin.last (k + n) = Fin.natAdd k (Fin.last n) from Fin.ext (by simp),
          Fin.append_right]
    rw [this, dist_comp_eq, dist_windowLaw_append]
    rfl
  rw [h1, h2]
  exact h3.trans h4.le

/-- The upper bounds decrease to the entropy rate of `Y`. -/
lemma hmmUpper_tendsto (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β)
    (hstat : IsStationaryDist r μ) :
    Tendsto (hmmUpper hμ hr φ) atTop
      (𝓝 ((markovProcess μ r hμ hr).map φ).entropyRate) :=
  ((markovProcess_isStationary hμ hr hstat).map φ).hasCondEntropyRate

/-- **Lemma 4.5.1.** `H(Yₙ | Yₙ₋₁, …, Y₂, X₁) ≤ H(𝒴)`, (4.57). -/
theorem hmmLower_le_entropyRate (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β)
    (hstat : IsStationaryDist r μ) (n : ℕ) :
    hmmLower μ r φ n ≤ ((markovProcess μ r hμ hr).map φ).entropyRate :=
  ge_of_tendsto ((hmmUpper_tendsto hμ hr φ hstat).comp (tendsto_add_atTop_nat n))
    (Eventually.of_forall fun k => hmmLower_le_hmmUpper hμ hr φ hstat n k)

/-- The entropy rate of `Y` is at most each upper bound `H(Yₙ | Yₙ₋₁, …, Y₁)`. -/
theorem entropyRate_le_hmmUpper (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β) (n : ℕ) :
    ((markovProcess μ r hμ hr).map φ).entropyRate ≤ hmmUpper hμ hr φ n :=
  ciInf_le ⟨0, by rintro _ ⟨m, rfl⟩; exact StochasticProcess.condEntropyLast_nonneg _ m⟩ n

/-- **(4.66)** The gap between the bounds is `I(X₁; Yₙ | Yₙ₋₁, …, Y₁)`. -/
lemma hmmUpper_sub_hmmLower (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β) (n : ℕ) :
    hmmUpper hμ hr φ n - hmmLower μ r φ n =
      I[fun x : Fin (n + 1) → α => φ (x (Fin.last n)) : fun x => x 0 |
        fun x => φ ∘ Fin.init x ; markovLaw μ r (n + 1)] := by
  rw [hmmUpper_eq, condMutualInfo]
  rfl

variable (μ r) in
/-- `H(X₁, Y₁, …, Yₙ₊₁)`. -/
private def hmmK (φ : α → β) (n : ℕ) : ℝ :=
  H[fun x : Fin (n + 1) → α => (x 0, φ ∘ x) ; markovLaw μ r (n + 1)]

private lemma hmmLower_eq_sub (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β) (n : ℕ) :
    hmmLower μ r φ n = hmmK μ r φ n -
      H[fun w : Fin (n + 1) → α => (w 0, φ ∘ Fin.init w) ; markovLaw μ r (n + 1)] := by
  rw [hmmLower, condEntropy_eq_sub (markovLaw_isPMF hμ hr (n + 1)), hmmK]
  congr 1
  refine entropyRV_eq_of_injective _ (fun p : α × (Fin (n + 1) → β) => ((p.1, Fin.init p.2),
    p.2 (Fin.last n))) (fun a b hab => ?_) (fun x => rfl)
  simp only [Prod.mk.injEq] at hab
  refine Prod.ext hab.1.1 ?_
  rw [← Fin.snoc_init_self a.2, ← Fin.snoc_init_self b.2, hab.1.2, hab.2]

private lemma hmmK_init (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β) (n : ℕ) :
    H[fun w : Fin (n + 2) → α => (w 0, φ ∘ Fin.init w) ; markovLaw μ r (n + 2)] =
      hmmK μ r φ n := by
  have : (fun w : Fin (n + 2) → α => (w 0, φ ∘ Fin.init w)) =
      (fun x : Fin (n + 1) → α => (x 0, φ ∘ x)) ∘ Fin.init := rfl
  rw [hmmK, entropyRV, this, dist_comp_eq, dist_markovLaw_init hμ hr]
  rfl

private lemma hmmK_zero (φ : α → β) :
    H[fun w : Fin (0 + 1) → α => (w 0, φ ∘ Fin.init w) ; markovLaw μ r (0 + 1)] =
      hmmK μ r φ 0 := by
  have h1 : H[fun w : Fin 1 → α => (w 0, φ ∘ Fin.init w) ; markovLaw μ r 1] =
      H[fun w : Fin 1 → α => w 0 ; markovLaw μ r 1] :=
    entropyRV_eq_of_injective _ (fun a => (a, (Fin.elim0 : Fin 0 → β)))
      (fun a b hab => (Prod.mk.inj hab).1)
      (fun w => Prod.ext rfl (Subsingleton.elim _ _))
  have h2 : hmmK μ r φ 0 = H[fun w : Fin 1 → α => w 0 ; markovLaw μ r 1] :=
    entropyRV_eq_of_injective _ (fun a => (a, (fun _ => φ a : Fin 1 → β)))
      (fun a b hab => (Prod.mk.inj hab).1)
      (fun w => Prod.ext rfl (by funext i; fin_cases i; rfl))
  rw [h1, h2]

/-- **Lemma 4.5.2.** `H(Yₙ | Yₙ₋₁, …, Y₁) - H(Yₙ | Yₙ₋₁, …, Y₁, X₁) → 0`, (4.65). -/
theorem tendsto_hmmUpper_sub_hmmLower (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β) :
    Tendsto (fun n => hmmUpper hμ hr φ n - hmmLower μ r φ n) atTop (𝓝 0) := by
  set P := markovProcess μ r hμ hr
  set d := fun n => hmmUpper hμ hr φ n - hmmLower μ r φ n
  have hd : ∀ n, 0 ≤ d n := fun n => by
    simp only [d]
    rw [hmmUpper_sub_hmmLower]
    exact condMutualInfo_nonneg (P.isPMF (n + 1)) _ _ _
  -- The partial sums telescope to `I(X₁; Y₁, …, Yₙ) = H(Y₁, …, Yₙ) - H(X₁, Y₁, …, Yₙ) + H(X₁)`.
  have hsum : ∀ N, ∑ i ∈ range (N + 1), d i =
      (P.map φ).jointEntropy (N + 1) - hmmK μ r φ N + hmmK μ r φ 0 := by
    intro N
    induction N with
    | zero =>
      simp only [zero_add, range_one, sum_singleton, d, hmmUpper,
        StochasticProcess.condEntropyLast_eq, StochasticProcess.jointEntropy_zero,
        hmmLower_eq_sub hμ hr, hmmK_zero]
      ring
    | succ N ih =>
      rw [sum_range_succ, ih]
      simp only [d, hmmUpper, StochasticProcess.condEntropyLast_eq, hmmLower_eq_sub hμ hr,
        hmmK_init hμ hr]
      ring
  -- `H(Y₁, …, Yₙ) ≤ H(X₁, Y₁, …, Yₙ)`, so the partial sums are bounded by `H(X₁)`.
  have hJ : ∀ N, (P.map φ).jointEntropy (N + 1) ≤ hmmK μ r φ N := by
    intro N
    have := entropyRV_comp_le (P.isPMF (N + 1)) (fun x : Fin (N + 1) → α => (x 0, φ ∘ x))
      Prod.snd
    exact this
  have hbound : ∀ N, ∑ i ∈ range N, d i ≤ hmmK μ r φ 0 := by
    intro N
    cases N with
    | zero =>
      simp only [range_zero, sum_empty]
      exact entropy_nonneg ((markovLaw_isPMF hμ hr 1).dist _)
    | succ N => rw [hsum]; linarith [hJ N]
  exact (summable_of_sum_range_le hd hbound).tendsto_atTop_zero

/-- **Theorem 4.5.1.** If `X₁, X₂, …` is a stationary Markov chain and `Yᵢ = φ(Xᵢ)`, then
`H(Yₙ | Yₙ₋₁, …, Y₁, X₁) ≤ H(𝒴) ≤ H(Yₙ | Yₙ₋₁, …, Y₁)`, (4.73). -/
theorem hmm_bounds (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β)
    (hstat : IsStationaryDist r μ) (n : ℕ) :
    hmmLower μ r φ n ≤ ((markovProcess μ r hμ hr).map φ).entropyRate ∧
      ((markovProcess μ r hμ hr).map φ).entropyRate ≤ hmmUpper hμ hr φ n :=
  ⟨hmmLower_le_entropyRate hμ hr φ hstat n, entropyRate_le_hmmUpper hμ hr φ n⟩

/-- **Theorem 4.5.1.** Both bounds converge to the entropy rate `H(𝒴)`, (4.74). -/
theorem tendsto_hmmLower (hμ : IsPMF μ) (hr : IsStochastic r) (φ : α → β)
    (hstat : IsStationaryDist r μ) :
    Tendsto (hmmLower μ r φ) atTop (𝓝 ((markovProcess μ r hμ hr).map φ).entropyRate) := by
  have h := (hmmUpper_tendsto hμ hr φ hstat).sub (tendsto_hmmUpper_sub_hmmLower hμ hr φ)
  simp only [sub_sub_cancel, sub_zero] at h
  exact h

/-! ### Hidden Markov models -/

section HiddenMarkov

variable {e : α → β → ℝ}

/-- The transitions `r(x'|x) e(y'|x')` of the pairs `(Xᵢ, Yᵢ)` of a hidden Markov model with state
transitions `r` and emission probabilities `e(y|x)`. The initial pair has law `μ(x) e(y|x)`,
which is `jointOf μ e`. -/
def hmmTrans (r : α → α → ℝ) (e : α → β → ℝ) : α × β → α × β → ℝ := fun z => jointOf (r z.1) e

lemma hmmTrans_isStochastic (hr : IsStochastic r) (he : IsChannel e) :
    IsStochastic (hmmTrans r e) :=
  fun z => jointOf_isPMF (hr z.1) he

/-- If `μ` is a stationary distribution of the states, then `μ(x) e(y|x)` is a stationary
distribution of the pairs. -/
lemma isStationaryDist_hmmTrans (he : IsChannel e) (hstat : IsStationaryDist r μ) :
    IsStationaryDist (hmmTrans r e) (jointOf μ e) := by
  funext z'
  have h := congrFun hstat z'.1
  simp only [step, outDist] at h ⊢
  simp only [hmmTrans, jointOf, Fintype.sum_prod_type]
  calc ∑ x, ∑ y, μ x * e x y * (r x z'.1 * e z'.1 z'.2)
      = ∑ x, μ x * r x z'.1 * e z'.1 z'.2 * ∑ y, e x y := by
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun y _ => by ring
    _ = μ z'.1 * e z'.1 z'.2 := by
        simp only [(he _).sum_eq_one, mul_one, ← sum_mul, h]

omit [Fintype α] [Fintype β] in
/-- **(4.75)** The Markov chain of the pairs `(Xᵢ, Yᵢ)` has the law of a hidden Markov model:
`p(xⁿ, yⁿ) = p(x₁) ∏ p(xᵢ₊₁ | xᵢ) ∏ p(yᵢ | xᵢ)`. -/
theorem markovLaw_hmmTrans (n : ℕ) (z : Fin n → α × β) :
    markovLaw (jointOf μ e) (hmmTrans r e) n z =
      markovLaw μ r n (Prod.fst ∘ z) * ∏ i, e (z i).1 (z i).2 := by
  induction n with
  | zero => simp [markovLaw]
  | succ n ih =>
    cases n with
    | zero => simp [markovLaw, pathProb, jointOf]
    | succ n =>
      obtain ⟨z, b, rfl⟩ : ∃ (z₀ : Fin (n + 1) → α × β) (b : α × β), Fin.snoc z₀ b = z :=
        ⟨Fin.init z, z (Fin.last _), Fin.snoc_init_self z⟩
      have hc : Prod.fst ∘ (Fin.snoc z b : Fin (n + 2) → α × β) = Fin.snoc (Prod.fst ∘ z) b.1 := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      have hp : ∏ i, e ((Fin.snoc z b : Fin (n + 2) → α × β) i).1
          ((Fin.snoc z b : Fin (n + 2) → α × β) i).2 = (∏ i, e (z i).1 (z i).2) * e b.1 b.2 := by
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [markovLaw_snoc, ih, hc, markovLaw_snoc, hp]
      simp only [Function.comp_apply, hmmTrans, jointOf]
      ring

/-- The observations `Y₁, Y₂, …` of the hidden Markov model with initial distribution `μ`, state
transitions `r` and emission probabilities `e`, as the function `Yᵢ = snd (Xᵢ, Yᵢ)` of the
Markov chain of pairs. -/
def hiddenMarkovProcess (hμ : IsPMF μ) (hr : IsStochastic r) (he : IsChannel e) :
    StochasticProcess β :=
  (markovProcess (jointOf μ e) (hmmTrans r e) (jointOf_isPMF hμ he)
    (hmmTrans_isStochastic hr he)).map Prod.snd

/-- **Hidden Markov models (Section 4.5).** If the hidden state is a stationary Markov chain,
the entropy rate of the observations satisfies `H(Yₙ | Yₙ₋₁, …, Y₁, X₁) ≤ H(𝒴) ≤
H(Yₙ | Yₙ₋₁, …, Y₁)`: Theorem 4.5.1 for the chain of the pairs `(Xᵢ, Yᵢ)`. The lower bound
conditions on `(X₁, Y₁)` and `Y₁, …, Yₙ`, which is `X₁` and `Y₁, …, Yₙ`
(`hmmLower_hmmTrans_eq`). -/
theorem hiddenMarkov_bounds (hμ : IsPMF μ) (hr : IsStochastic r) (he : IsChannel e)
    (hstat : IsStationaryDist r μ) (n : ℕ) :
    hmmLower (jointOf μ e) (hmmTrans r e) Prod.snd n ≤
        (hiddenMarkovProcess hμ hr he).entropyRate ∧
      (hiddenMarkovProcess hμ hr he).entropyRate ≤
        hmmUpper (jointOf_isPMF hμ he) (hmmTrans_isStochastic hr he) Prod.snd n :=
  hmm_bounds _ _ Prod.snd (isStationaryDist_hmmTrans he hstat) n

/-- **Hidden Markov models (Section 4.5).** The lower bounds, conditioned on the underlying state
`X₁`, converge to the entropy rate of the observations. -/
theorem tendsto_hiddenMarkov_lower (hμ : IsPMF μ) (hr : IsStochastic r) (he : IsChannel e)
    (hstat : IsStationaryDist r μ) :
    Tendsto (hmmLower (jointOf μ e) (hmmTrans r e) Prod.snd) atTop
      (𝓝 (hiddenMarkovProcess hμ hr he).entropyRate) :=
  tendsto_hmmLower _ _ Prod.snd (isStationaryDist_hmmTrans he hstat)

/-- For `n ≥ 1` observations in the past, the lower bound for the hidden Markov model is
`H(Yₙ₊₁ | X₁, Y₁, …, Yₙ)`, conditioned on the state `X₁` and the observations. -/
lemma hmmLower_hmmTrans_eq (hμ : IsPMF μ) (hr : IsStochastic r) (he : IsChannel e) (n : ℕ) :
    hmmLower (jointOf μ e) (hmmTrans r e) Prod.snd (n + 1) =
      H[fun z : Fin (n + 2) → α × β => (z (Fin.last (n + 1))).2 |
        fun z => ((z 0).1, Prod.snd ∘ Fin.init z) ;
        markovLaw (jointOf μ e) (hmmTrans r e) (n + 2)] :=
  condEntropy_congr_right
    (markovLaw_isPMF (jointOf_isPMF hμ he) (hmmTrans_isStochastic hr he) (n + 2)) _
    (fun p : α × (Fin (n + 1) → β) => ((p.1, p.2 0), p.2))
    (fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.1 h.2) (fun z => rfl)

end HiddenMarkov

end InfoTheory
