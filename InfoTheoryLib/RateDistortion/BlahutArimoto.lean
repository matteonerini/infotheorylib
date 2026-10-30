/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Basic
public import InfoTheoryLib.RelativeEntropy.Gibbs

/-!
# Computing the rate distortion function: the Blahut–Arimoto algorithm

The rate distortion function is a double minimization of a relative entropy,

  `R(D) = min_{r(x̂)} min_{q(x̂|x) : E d ≤ D} D(p(x) q(x̂|x) ‖ p(x) r(x̂))` (10.140),

because for a fixed test channel the best `r` is the output distribution (Lemma 10.8.1). The
Blahut–Arimoto algorithm alternates the two minimizations of the Lagrangian
`F(q, r) = D(p(x) q(x̂|x) ‖ p(x) r(x̂)) + λ E d(X, X̂)`. For fixed `r` the best test channel is
`q(x̂|x) = r(x̂) e^{-λ d(x, x̂)} / ∑_x̂' r(x̂') e^{-λ d(x, x̂')}` (10.124), (10.142), and for fixed
`q` the best `r` is `∑ₓ p(x) q(x̂|x)` (10.143). Each step decreases `F`.

## Main definitions

* `baChannel r d λ`: the test channel (10.142).
* `baObjective p d λ q r`: the Lagrangian `F(q, r)`.
* `baIter p d λ r₀ k`: the output distributions of the Blahut–Arimoto iteration.

## Main statements

* `relEntropy_jointOf_prodDist_eq`: (10.134)–(10.138),
  `D(p(x) q(y|x) ‖ p(x) r(y)) = I(X; Y) + D(r* ‖ r)`.
* `mutualInfoOf_le_relEntropy_jointOf_prodDist`: **Lemma 10.8.1**, (10.131).
* `sum_mul_log_div_le_mutualInfoOf`, `sum_mul_log_posterior_eq`: **Lemma 10.8.1**, (10.132).
* `infoRD_eq_sInf_relEntropy`: (10.140), the double minimization.
* `neg_log_sum_le_relEntropyReal_add`, `relEntropyReal_gibbs_add`
  (`RelativeEntropy.Gibbs`): the Gibbs variational principle, which gives (10.124) and (10.147).
* `baObjective_baChannel_le`, `baObjective_outDist_le`: the two steps of the algorithm.
* `baObjective_iter_antitone`: the Lagrangian decreases along the iteration.

## Implementation notes

The book writes `∑ p(x) q(x̂|x) log (q(x̂|x)/r(x̂))` for `D(p(x) q(x̂|x) ‖ p(x) r(x̂))`. The
convergence of the iteration to `R(D)` (Csiszár) is not formalized.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 10.7
  and 10.8
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Lemma 10.8.1 -/

variable {p : α → ℝ} {W : α → β → ℝ}

lemma jointOf_le_outDist (hp : IsPMF p) (hW : IsChannel W) (x : α) (y : β) :
    jointOf p W (x, y) ≤ outDist p W y :=
  single_le_sum (f := fun x => p x * W x y) (fun x _ => mul_nonneg (hp.nonneg x) ((hW x).nonneg y))
    (mem_univ x)

/-- **(10.134)–(10.138)** `D(p(x) p(y|x) ‖ p(x) r(y)) = I(X; Y) + D(r* ‖ r)`, where `r*` is the
law of the output, for every `r` with `r* ≪ r`. -/
theorem relEntropy_jointOf_prodDist_eq (hp : IsPMF p) (hW : IsChannel W) {r : β → ℝ}
    (hr : AbsCont (outDist p W) r) :
    relEntropyReal (jointOf p W) (prodDist p r) =
      mutualInfoOf p W + relEntropyReal (outDist p W) r := by
  set r' := outDist p W
  rw [mutualInfoOf_eq_relEntropy hW]
  have hterm : ∀ z : α × β, jointOf p W z * log (jointOf p W z / prodDist p r z) =
      jointOf p W z * log (jointOf p W z / prodDist p r' z) +
        jointOf p W z * log (r' z.2 / r z.2) := by
    rintro ⟨x, y⟩
    rcases eq_or_ne (jointOf p W (x, y)) 0 with h0 | h0
    · simp [h0]
    have hJ : 0 < jointOf p W (x, y) :=
      lt_of_le_of_ne (mul_nonneg (hp.nonneg x) ((hW x).nonneg y)) (Ne.symm h0)
    have hpx : p x ≠ 0 := fun h => h0 (by simp [jointOf, h])
    have hr' : r' y ≠ 0 := (hJ.trans_le (jointOf_le_outDist hp hW x y)).ne'
    have hry : r y ≠ 0 := fun h => hr' (hr y h)
    simp only [prodDist]
    rw [← mul_add, log_div h0 (mul_ne_zero hpx hry), log_div h0 (mul_ne_zero hpx hr'),
      log_div hr' hry, log_mul hpx hry, log_mul hpx hr']
    ring
  have hsum : ∑ z : α × β, jointOf p W z * log (r' z.2 / r z.2) = relEntropyReal r' r := by
    rw [Fintype.sum_prod_type, sum_comm, relEntropyReal]
    refine sum_congr rfl fun y _ => ?_
    change ∑ x, jointOf p W (x, y) * log (r' y / r y) = _
    rw [← sum_mul]
    rfl
  rw [relEntropyReal, relEntropyReal, sum_congr rfl fun z _ => hterm z, sum_add_distrib, hsum]

/-- **Lemma 10.8.1, (10.131).** The output distribution `r*(y) = ∑ₓ p(x) p(y|x)` minimizes
`D(p(x) p(y|x) ‖ p(x) r(y))` over the distributions `r`, and the minimum is `I(X; Y)`. -/
theorem mutualInfoOf_le_relEntropy_jointOf_prodDist (hp : IsPMF p) (hW : IsChannel W)
    {r : β → ℝ} (hr : IsPMF r) (hrW : AbsCont (outDist p W) r) :
    mutualInfoOf p W ≤ relEntropyReal (jointOf p W) (prodDist p r) := by
  rw [relEntropy_jointOf_prodDist_eq hp hW hrW]
  linarith [relEntropyReal_nonneg (outDist_isPMF hp hW) hr hrW]

/-- The posterior `r*(x|y) = p(x) p(y|x) / ∑ₓ' p(x') p(y|x')` (10.133), taken to be `p` when the
output `y` has probability `0`. -/
def posterior (p : α → ℝ) (W : α → β → ℝ) (y : β) (x : α) : ℝ :=
  if outDist p W y = 0 then p x else p x * W x y / outDist p W y

lemma posterior_isChannel (hp : IsPMF p) (hW : IsChannel W) : IsChannel (posterior p W) := by
  intro y
  by_cases hy : outDist p W y = 0
  · have : posterior p W y = p := funext fun x => by simp [posterior, hy]
    rw [this]
    exact hp
  · refine ⟨fun x => ?_, ?_⟩
    · simp only [posterior, hy, ↓reduceIte]
      exact div_nonneg (mul_nonneg (hp.nonneg x) ((hW x).nonneg y))
        (sum_nonneg fun x _ => mul_nonneg (hp.nonneg x) ((hW x).nonneg y))
    · simp only [posterior, hy, ↓reduceIte, ← sum_div]
      exact div_self hy

/-- **Lemma 10.8.1, (10.132).** For every backward channel `r(x|y)` with
`p(x) p(y|x) ≪ r(x|y)`, `∑ p(x) p(y|x) log (r(x|y)/p(x)) ≤ I(X; Y)`. The difference is the
relative entropy between `p(x, y)` and `r*(y) r(x|y)`. -/
theorem sum_mul_log_div_le_mutualInfoOf (hp : IsPMF p) (hW : IsChannel W) {V : β → α → ℝ}
    (hV : IsChannel V) (hVW : ∀ x y, V y x = 0 → p x * W x y = 0) :
    ∑ x, ∑ y, p x * W x y * log (V y x / p x) ≤ mutualInfoOf p W := by
  set r' := outDist p W
  set J := jointOf p W
  set Q : α × β → ℝ := fun z => r' z.2 * V z.2 z.1
  have hQ : IsPMF Q := by
    refine ⟨fun z => mul_nonneg ((outDist_isPMF hp hW).nonneg _) ((hV _).nonneg _), ?_⟩
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [Q, ← mul_sum, (hV _).sum_eq_one, mul_one]
    exact (outDist_isPMF hp hW).sum_eq_one
  have hJQ : AbsCont J Q := by
    rintro ⟨x, y⟩ h
    rcases mul_eq_zero.1 h with h | h
    · exact le_antisymm (h ▸ jointOf_le_outDist hp hW x y) (mul_nonneg (hp.nonneg x)
        ((hW x).nonneg y))
    · exact hVW x y h
  have hD : 0 ≤ relEntropyReal J Q := relEntropyReal_nonneg (jointOf_isPMF hp hW) hQ hJQ
  have hterm : ∀ z : α × β, J z * log (J z / prodDist p r' z) =
      J z * log (V z.2 z.1 / p z.1) + J z * log (J z / Q z) := by
    rintro ⟨x, y⟩
    rcases eq_or_ne (J (x, y)) 0 with h0 | h0
    · simp [h0]
    have hJ : 0 < J (x, y) :=
      lt_of_le_of_ne (mul_nonneg (hp.nonneg x) ((hW x).nonneg y)) (Ne.symm h0)
    have hpx : p x ≠ 0 := fun h => h0 (by simp [J, jointOf, h])
    have hr' : r' y ≠ 0 := (hJ.trans_le (jointOf_le_outDist hp hW x y)).ne'
    have hVx : V y x ≠ 0 := fun h => h0 (hVW x y h)
    simp only [prodDist, Q]
    rw [← mul_add, log_div h0 (mul_ne_zero hpx hr'), log_div hVx hpx, log_div h0
      (mul_ne_zero hr' hVx), log_mul hpx hr', log_mul hr' hVx]
    ring
  rw [mutualInfoOf_eq_relEntropy hW, relEntropyReal, sum_congr rfl fun z _ => hterm z,
    sum_add_distrib]
  have e : ∑ z : α × β, J z * log (V z.2 z.1 / p z.1) =
      ∑ x, ∑ y, p x * W x y * log (V y x / p x) := by
    rw [Fintype.sum_prod_type]
    rfl
  have : relEntropyReal J Q = ∑ z, J z * log (J z / Q z) := rfl
  linarith

/-- **Lemma 10.8.1, (10.132)–(10.133), equality.** The posterior attains the maximum:
`∑ p(x) p(y|x) log (r*(x|y)/p(x)) = I(X; Y)`. -/
theorem sum_mul_log_posterior_eq (hp : IsPMF p) (hW : IsChannel W) :
    ∑ x, ∑ y, p x * W x y * log (posterior p W y x / p x) = mutualInfoOf p W := by
  rw [mutualInfoOf_eq_relEntropy hW, relEntropyReal, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simp only [jointOf, prodDist]
  rcases eq_or_ne (p x * W x y) 0 with h0 | h0
  · simp [h0]
  have hpx : p x ≠ 0 := fun h => h0 (by simp [h])
  have hy : outDist p W y ≠ 0 :=
    ((lt_of_le_of_ne (mul_nonneg (hp.nonneg x) ((hW x).nonneg y)) (Ne.symm h0)).trans_le
      (jointOf_le_outDist hp hW x y)).ne'
  simp only [posterior, hy, ↓reduceIte]
  congr 2
  field_simp

/-! ### The double minimization (10.140) -/

variable {d : α → β → ℝ}

/-- **(10.140)** `R(D)` is the minimum over the test channels `q` with `E d ≤ D` and the output
distributions `r` of `D(p(x) q(x̂|x) ‖ p(x) r(x̂))`. -/
theorem infoRD_eq_sInf_relEntropy [Nonempty β] (hp : IsPMF p) {D : ℝ}
    (hD : minDistortion p d ≤ D) :
    infoRD p d D = sInf {v | ∃ q r, IsChannel q ∧ IsPMF r ∧ AbsCont (outDist p q) r ∧
      expDistortion p q d ≤ D ∧ relEntropyReal (jointOf p q) (prodDist p r) = v} := by
  obtain ⟨q₀, hq₀, hqD₀, he₀⟩ := exists_infoRD_eq hp hD
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨q₀, outDist p q₀, hq₀, outDist_isPMF hp hq₀, fun _ h => h, hqD₀, ?_⟩, ?_⟩
  · rw [← he₀, mutualInfoOf_eq_relEntropy hq₀]
  · rintro _ ⟨q, r, hq, hr, hqr, hqD, rfl⟩
    exact (infoRD_le hp hq hqD).trans (mutualInfoOf_le_relEntropy_jointOf_prodDist hp hq hr hqr)

/-! ### The Blahut–Arimoto algorithm -/

/-- **(10.142)** For an output distribution `r` and a multiplier `λ ≥ 0`, the test channel
`q(x̂|x) = r(x̂) e^{-λ d(x, x̂)} / ∑_x̂' r(x̂') e^{-λ d(x, x̂')}` minimizing
`D(p(x) q(x̂|x) ‖ p(x) r(x̂)) + λ E d(X, X̂)`. -/
def baChannel (r : β → ℝ) (d : α → β → ℝ) (lam : ℝ) (x : α) (y : β) : ℝ :=
  r y * exp (-(lam * d x y)) / ∑ y', r y' * exp (-(lam * d x y'))

/-- **(10.140)** The Lagrangian `F(q, r) = D(p(x) q(x̂|x) ‖ p(x) r(x̂)) + λ E d(X, X̂)` of the
double minimization. -/
def baObjective (p : α → ℝ) (d : α → β → ℝ) (lam : ℝ) (q : α → β → ℝ) (r : β → ℝ) : ℝ :=
  relEntropyReal (jointOf p q) (prodDist p r) + lam * expDistortion p q d

omit [Fintype α] in
lemma sum_baChannel_pos {r : β → ℝ} (hr : IsPMF r) (lam : ℝ) (x : α) :
    0 < ∑ y', r y' * exp (-(lam * d x y')) := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, 0 < r y := by
    by_contra h
    push Not at h
    have : ∑ y, r y ≤ 0 := sum_nonpos fun y _ => h y
    linarith [hr.sum_eq_one]
  exact lt_of_lt_of_le (mul_pos hy₀ (exp_pos _)) (single_le_sum
    (f := fun y => r y * exp (-(lam * d x y))) (fun y _ => mul_nonneg (hr.nonneg y)
      (exp_pos _).le) (mem_univ y₀))

omit [Fintype α] in
lemma baChannel_isChannel {r : β → ℝ} (hr : IsPMF r) (lam : ℝ) :
    IsChannel (baChannel r d lam) := fun x =>
  ⟨fun y => div_nonneg (mul_nonneg (hr.nonneg y) (exp_pos _).le)
    (sum_baChannel_pos hr lam x).le, by
    simp only [baChannel, ← sum_div]; exact div_self (sum_baChannel_pos hr lam x).ne'⟩

/-- `D(p(x) q(y|x) ‖ p(x) r(y)) = ∑ₓ p(x) D(q(·|x) ‖ r)`. -/
lemma relEntropyReal_jointOf_prodDist (p : α → ℝ) (q : α → β → ℝ) (r : β → ℝ) :
    relEntropyReal (jointOf p q) (prodDist p r) = ∑ x, p x * relEntropyReal (q x) r := by
  rw [relEntropyReal, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [relEntropyReal, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [jointOf, prodDist]
  rcases eq_or_ne (p x) 0 with h0 | h0
  · simp [h0]
  rw [mul_div_mul_left _ _ h0, mul_assoc]

/-- The Lagrangian as a sum over the source letters. -/
lemma baObjective_eq (p : α → ℝ) (d : α → β → ℝ) (lam : ℝ) (q : α → β → ℝ) (r : β → ℝ) :
    baObjective p d lam q r =
      ∑ x, p x * (relEntropyReal (q x) r + ∑ y, q x y * (lam * d x y)) := by
  rw [baObjective, relEntropyReal_jointOf_prodDist, expDistortion, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_add]
  congr 1
  simp only [mul_sum]
  exact sum_congr rfl fun y _ => by ring

/-- **(10.124), (10.142)** For a fixed output distribution `r`, the test channel `baChannel`
minimizes the Lagrangian `F(·, r)`, with minimum `-∑ₓ p(x) log ∑_x̂ r(x̂) e^{-λ d(x, x̂)}`. -/
theorem baObjective_baChannel_le (hp : IsPMF p) {q : α → β → ℝ} (hq : IsChannel q)
    {r : β → ℝ} (hr : IsPMF r) (hqr : AbsCont (jointOf p q) (prodDist p r)) (lam : ℝ) :
    baObjective p d lam (baChannel r d lam) r ≤ baObjective p d lam q r := by
  rw [baObjective_eq, baObjective_eq]
  refine sum_le_sum fun x _ => ?_
  rcases (hp.nonneg x).eq_or_lt with h0 | h0
  · simp [← h0]
  refine mul_le_mul_of_nonneg_left ?_ h0.le
  have hgibbs := relEntropyReal_gibbs_add (fun y => lam * d x y)
    (sum_baChannel_pos hr lam x)
  have hle := neg_log_sum_le_relEntropyReal_add (hq x) hr.nonneg (fun y hy => by
    have := hqr (x, y) (by simp [prodDist, hy])
    exact (mul_eq_zero.1 this).resolve_left h0.ne') fun y => lam * d x y
  exact hgibbs.trans_le hle

/-- **(10.143)** For a fixed test channel, the output distribution minimizes the Lagrangian
(Lemma 10.8.1). -/
theorem baObjective_outDist_le (hp : IsPMF p) {q : α → β → ℝ} (hq : IsChannel q) {r : β → ℝ}
    (hr : IsPMF r) (hqr : AbsCont (outDist p q) r) (lam : ℝ) :
    baObjective p d lam q (outDist p q) ≤ baObjective p d lam q r := by
  rw [baObjective, baObjective, ← mutualInfoOf_eq_relEntropy hq]
  linarith [mutualInfoOf_le_relEntropy_jointOf_prodDist hp hq hr hqr]

/-- **The Blahut–Arimoto iteration.** Starting from `r₀`, the output distributions
`r_{k+1} = ∑ₓ p(x) q_k(x̂|x)` of the test channels `q_k = baChannel r_k`. -/
def baIter (p : α → ℝ) (d : α → β → ℝ) (lam : ℝ) (r₀ : β → ℝ) : ℕ → β → ℝ
  | 0 => r₀
  | k + 1 => outDist p (baChannel (baIter p d lam r₀ k) d lam)

lemma baIter_isPMF (hp : IsPMF p) (lam : ℝ) {r₀ : β → ℝ} (hr₀ : IsPMF r₀) (k : ℕ) :
    IsPMF (baIter p d lam r₀ k) := by
  induction k with
  | zero => exact hr₀
  | succ k ih => exact outDist_isPMF hp (baChannel_isChannel ih lam)

/-- **Section 10.8.** Each step of the Blahut–Arimoto algorithm decreases the Lagrangian:
`F(q_{k+1}, r_{k+1}) ≤ F(q_k, r_{k+1}) ≤ F(q_k, r_k)`. -/
theorem baObjective_iter_antitone (hp : IsPMF p) (lam : ℝ) {r₀ : β → ℝ} (hr₀ : IsPMF r₀) :
    Antitone fun k => baObjective p d lam (baChannel (baIter p d lam r₀ k) d lam)
      (baIter p d lam r₀ k) := by
  refine antitone_nat_of_succ_le fun k => ?_
  set r := baIter p d lam r₀ k
  have hr := baIter_isPMF (d := d) hp lam hr₀ k
  have hq := baChannel_isChannel (d := d) hr lam
  set r' := outDist p (baChannel r d lam)
  have hr' : IsPMF r' := outDist_isPMF hp hq
  change baObjective p d lam (baChannel r' d lam) r' ≤ baObjective p d lam (baChannel r d lam) r
  refine (baObjective_baChannel_le hp hq hr' ?_ lam).trans
    (baObjective_outDist_le hp hq hr ?_ lam)
  · -- `r'(x̂) = 0` forces `p(x) q(x̂|x) = 0`.
    rintro ⟨x, y⟩ h
    rcases mul_eq_zero.1 h with h | h
    · simp [jointOf, h]
    · exact le_antisymm (h ▸ jointOf_le_outDist hp hq x y)
        (mul_nonneg (hp.nonneg x) ((hq x).nonneg y))
  · -- `r(x̂) = 0` forces `q(x̂|x) = 0`.
    intro y hy
    refine sum_eq_zero fun x _ => ?_
    simp [baChannel, hy]

end InfoTheory
