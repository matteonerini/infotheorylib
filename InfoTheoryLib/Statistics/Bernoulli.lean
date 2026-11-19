/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.IID
public import InfoTheoryLib.Statistics.SufficientStatistic

/-!
# Sufficient statistics for Bernoulli trials

For i.i.d. tosses of a coin with `Pr{Xᵢ = 1} = θ`, the number of ones is a minimal sufficient
statistic for `θ`.

## Main definitions

* `bernoulliPMF θ`: the Bernoulli(`θ`) pmf on `Bool`.
* `numOnes x`: the number of ones in a binary sequence.
* `bernSeq n θ`: the law of `n` i.i.d. Bernoulli(`θ`) trials.

## Main statements

* `condDist_numOnes`: given `∑ Xᵢ = k`, all sequences with `k` ones are equally likely.
* `numOnes_sufficient`, `numOnes_minimal`: the number of ones is a (minimal) sufficient statistic.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006],
  Section 2.9, Example 1
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable {Θ : Type*} [Fintype Θ]

/-- The Bernoulli(`θ`) pmf on `Bool`: `p(1) = θ` and `p(0) = 1 - θ`. -/
def bernoulliPMF (θ : ℝ) (b : Bool) : ℝ := if b then θ else 1 - θ

lemma bernoulliPMF_isPMF {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : IsPMF (bernoulliPMF θ) :=
  ⟨fun b => by cases b <;> simp [bernoulliPMF] <;> linarith, by simp [bernoulliPMF]⟩

/-- The entropy of a Bernoulli(`θ`) random variable is the binary entropy `H(θ)`. -/
lemma entropy_bernoulliPMF (θ : ℝ) : entropy (bernoulliPMF θ) = binEntropy θ :=
  entropy_bernoulli θ

/-- The number of `1`s in a binary sequence, `T(X₁, …, Xₙ) = ∑ Xᵢ ∈ {0, …, n}`. -/
def numOnes {n : ℕ} (x : Fin n → Bool) : Fin (n + 1) :=
  ⟨#(univ.filter fun i => x i = true),
    Nat.lt_succ_of_le (by simpa using card_le_univ (univ.filter fun i => x i = true))⟩

/-- `Pr_θ{(X₁, …, Xₙ) = x}` for i.i.d. tosses of a coin with `Pr{Xᵢ = 1} = θ`. -/
def bernSeq (n : ℕ) (θ : ℝ) (x : Fin n → Bool) : ℝ := ∏ i, if x i then θ else 1 - θ

lemma bernSeq_eq (n : ℕ) (θ : ℝ) (x : Fin n → Bool) :
    bernSeq n θ x = θ ^ (numOnes x : ℕ) * (1 - θ) ^ (n - numOnes x) := by
  rw [bernSeq, prod_ite, prod_const, prod_const, numOnes]
  congr 2
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => x i = true)
  rw [card_univ, Fintype.card_fin] at this
  simp only
  omega

/-- `bernSeq n θ` is the law of `n` i.i.d. Bernoulli(`θ`) random variables. -/
lemma bernSeq_eq_iidPMF (n : ℕ) (θ : ℝ) : bernSeq n θ = iidPMF (bernoulliPMF θ) n := rfl

lemma bernSeq_isPMF {n : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : IsPMF (bernSeq n θ) := by
  refine ⟨fun x => prod_nonneg fun i _ => by split_ifs <;> linarith, ?_⟩
  have := Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then θ else 1 - θ)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, add_sub_cancel,
    prod_const_one] at this
  exact this.symm

/-- There are `C(n, k)` binary sequences of length `n` with `k` ones. -/
lemma card_numOnes_eq (n : ℕ) (k : Fin (n + 1)) :
    #(univ.filter fun x : Fin n → Bool => numOnes x = k) = n.choose k := by
  have h := card_powersetCard (k : ℕ) (univ : Finset (Fin n))
  rw [card_univ, Fintype.card_fin] at h
  rw [← h]
  refine card_bij' (fun x _ => univ.filter fun i => x i = true) (fun s _ i => decide (i ∈ s))
    ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_filter] at hx
    rw [mem_powersetCard]
    exact ⟨subset_univ _, congrArg Fin.val hx.2⟩
  · intro s hs
    rw [mem_powersetCard] at hs
    rw [mem_filter]
    refine ⟨mem_univ _, Fin.ext ?_⟩
    simp [numOnes, hs.2]
  · intro x _; funext i; simp
  · intro s _; ext i; simp

/-- `Pr_θ{∑ Xᵢ = k} = C(n, k) θᵏ (1 - θ)ⁿ⁻ᵏ`. -/
lemma dist_numOnes {n : ℕ} (θ : ℝ) (k : Fin (n + 1)) :
    dist (bernSeq n θ) numOnes k = n.choose k * (θ ^ (k : ℕ) * (1 - θ) ^ (n - k)) := by
  calc dist (bernSeq n θ) numOnes k
      = ∑ ω ∈ univ.filter (fun ω : Fin n → Bool => numOnes ω = k),
          θ ^ (k : ℕ) * (1 - θ) ^ (n - k) := by
        rw [dist, sum_filter]
        refine sum_congr rfl fun ω _ => ?_
        split_ifs with h1
        · rw [bernSeq_eq, h1]
        · rfl
    _ = _ := by rw [sum_const, card_numOnes_eq, nsmul_eq_mul]

open Classical in
/-- **Example 1 (2.125).** For i.i.d. Bernoulli(`θ`) trials, given the number `k` of ones, all
sequences with that many ones are equally likely, independently of `θ`:
`Pr{X = x | ∑ Xᵢ = k} = 1/C(n, k)` if `∑ xᵢ = k`, and `0` otherwise. -/
theorem condDist_numOnes {n : ℕ} {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (k : Fin (n + 1))
    (x : Fin n → Bool) :
    condDist (bernSeq n θ) id numOnes k x = if numOnes x = k then 1 / (n.choose k : ℝ) else 0 := by
  rw [condDist, dist_numOnes θ k]
  have hpair : dist (bernSeq n θ) (pair numOnes id) (k, x) =
      if numOnes x = k then bernSeq n θ x else 0 := by
    have := dist_pair_comp_self (bernSeq n θ) id numOnes x k
    rw [dist_id] at this
    rw [dist_pair_swap (bernSeq n θ) id numOnes x k]
    convert this using 3
    rfl
  rw [hpair]
  split_ifs with h
  · rw [bernSeq_eq, h]
    have hc : (n.choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.1 k.isLt)).ne'
    have hθ1 : θ ^ (k : ℕ) ≠ 0 := pow_ne_zero _ h0.ne'
    have hθ2 : (1 - θ) ^ (n - k) ≠ 0 := pow_ne_zero _ (by linarith)
    field_simp
  · simp

/-- **Example 1.** The number of ones is a sufficient statistic for `θ`, for any (finite) family
of parameters `θ(ϑ) ∈ [0, 1]`. -/
theorem numOnes_sufficient {n : ℕ} (θ : Θ → ℝ) (hθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
    IsSufficient (fun t => bernSeq n (θ t)) numOnes :=
  isSufficient_of_factorization (fun t => bernSeq_isPMF (hθ t).1 (hθ t).2)
    (fun t k => θ t ^ (k : ℕ) * (1 - θ t) ^ (n - k)) (fun _ => 1)
    (fun t x => by rw [bernSeq_eq, mul_one])

lemma bernSeq_pos {n : ℕ} {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (x : Fin n → Bool) :
    0 < bernSeq n θ x :=
  prod_pos fun i _ => by split_ifs <;> linarith

open Classical in
/-- **Section 2.9.** "In the preceding examples, the sufficient statistics are also minimal."
For Bernoulli trials the number of ones is a minimal sufficient statistic, as soon as the
family contains two distinct parameters in `(0, 1)`. -/
theorem numOnes_minimal {n : ℕ} (θ : Θ → ℝ) (hθ : ∀ t, 0 < θ t ∧ θ t < 1) {t₁ t₂ : Θ}
    (hne : θ t₁ ≠ θ t₂) : IsMinimalSufficient (fun t => bernSeq n (θ t)) numOnes := by
  set f : Θ → (Fin n → Bool) → ℝ := fun t => bernSeq n (θ t)
  have hf : IsChannel f := fun t => bernSeq_isPMF (hθ t).1.le (hθ t).2.le
  have hfpos : ∀ t z, 0 < f t z := fun t z => bernSeq_pos (hθ t).1 (hθ t).2 z
  refine ⟨numOnes_sufficient θ (fun t => ⟨(hθ t).1.le, (hθ t).2.le⟩), fun γ' _ U hU => ?_⟩
  have key : ∀ x x', U x = U x' → numOnes x = numOnes x' := by
    intro x x' hxx'
    have : Nonempty Θ := ⟨t₁⟩
    set w := uniformPMF Θ
    have hw : IsPMF w := uniformPMF_isPMF
    have hwpos : ∀ t, 0 < w t := fun t => by simp [w, uniformPMF, Fintype.card_pos]
    have hm := (markovChain_iff_mul (jointOf_isPMF hw hf) _ _ _).1 (hU w hw)
    set u := U x
    set F : Θ → ℝ := fun t => ∑ y, if U y = u then f t y else 0
    have hFpos : ∀ t, 0 < F t := fun t => by
      refine lt_of_lt_of_le (hfpos t x) ?_
      have := single_le_sum (f := fun y => if U y = u then f t y else 0)
        (fun y _ => by split_ifs <;> simp [(hfpos t y).le]) (mem_univ x)
      simpa [u] using this
    -- For every sample `z` with `U z = u` and every `t`: `f_t(z) P(u) = F_t(u) M(z)`.
    have hid : ∀ t z, U z = u →
        f t z * (∑ t', ∑ y, if U y = u then w t' * f t' y else 0) =
          F t * ∑ t', w t' * f t' z := by
      intro t z hz
      have h := hm t u z
      rw [dist_param_stat_sample, dist_stat, dist_param_stat, dist_stat_sample] at h
      simp only [hz, ↓reduceIte, jointOf] at h
      have e : (∑ y, if U y = u then w t * f t y else 0) = w t * F t := by
        simp only [F, mul_sum]
        exact sum_congr rfl fun y _ => by split_ifs <;> simp
      rw [e] at h
      apply mul_left_cancel₀ (hwpos t).ne'
      linear_combination h
    -- Hence `f_{t₁}(z) F_{t₂} = f_{t₂}(z) F_{t₁}` for `z ∈ {x, x'}`.
    have hcross : ∀ z, U z = u → f t₁ z * F t₂ = f t₂ z * F t₁ := by
      intro z hz
      have h1 := hid t₁ z hz
      have h2 := hid t₂ z hz
      have hM : 0 < ∑ t', w t' * f t' z :=
        sum_pos (fun t _ => mul_pos (hwpos t) (hfpos t z)) univ_nonempty
      apply mul_right_cancel₀ hM.ne'
      linear_combination f t₂ z * h1 - f t₁ z * h2
    have hx := hcross x rfl
    have hx' := hcross x' hxx'.symm
    have hprod : f t₁ x * f t₂ x' = f t₂ x * f t₁ x' := by
      apply mul_right_cancel₀ (hFpos t₂).ne'
      calc f t₁ x * f t₂ x' * F t₂ = (f t₁ x * F t₂) * f t₂ x' := by ring
        _ = f t₂ x * (f t₁ x' * F t₂) := by rw [hx, hx']; ring
        _ = f t₂ x * f t₁ x' * F t₂ := by ring
    -- Take logarithms: `(k - k') (logit θ₁ - logit θ₂) = 0`.
    have hlog := congrArg log hprod
    have hθ1 := hθ t₁
    have hθ2 := hθ t₂
    simp only [f, bernSeq_eq] at hlog
    have hk : (numOnes x : ℕ) ≤ n := Nat.lt_succ_iff.1 (numOnes x).isLt
    have hk' : (numOnes x' : ℕ) ≤ n := Nat.lt_succ_iff.1 (numOnes x').isLt
    have p1 : 0 < θ t₁ := hθ1.1
    have p2 : 0 < θ t₂ := hθ2.1
    have q1 : 0 < 1 - θ t₁ := by linarith [hθ1.2]
    have q2 : 0 < 1 - θ t₂ := by linarith [hθ2.2]
    rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity)] at hlog
    simp only [log_pow, Nat.cast_sub hk, Nat.cast_sub hk'] at hlog
    have hfac : ((numOnes x : ℕ) - (numOnes x' : ℕ) : ℝ) *
        ((log (θ t₁) - log (1 - θ t₁)) - (log (θ t₂) - log (1 - θ t₂))) = 0 := by
      linarith
    rcases mul_eq_zero.1 hfac with h | h
    · exact Fin.ext (by exact_mod_cast sub_eq_zero.1 h)
    · exact absurd (log_odds_injective hθ1.1 hθ1.2 hθ2.1 hθ2.2 (sub_eq_zero.1 h)) hne
  classical
  refine ⟨fun v => if h : ∃ x, U x = v then numOnes h.choose else 0, fun x => ?_⟩
  have h : ∃ y, U y = U x := ⟨x, rfl⟩
  simp only [h, ↓reduceDIte]
  exact key x h.choose h.choose_spec.symm

end InfoTheory
