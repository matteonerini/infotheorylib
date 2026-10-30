/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.FinitePMF

/-!
# Entropy

## Main definitions

* `entropy p`: the entropy `H(p) = -∑ₓ p(x) log p(x)` of a pmf, in nats.
* `entropyRV μ X`: the entropy `H(X)` of a random variable, with notation `H[X ; μ]`.
* `entropyBase b p`: the entropy in base `b`; `entropyBits p` is the entropy in bits.

## Main statements

* `entropy_nonneg`: `H(X) ≥ 0`.
* `entropyBase_eq`: change of base, `H_b(X) = (log_b a) H_a(X)`.
* `entropy_eq_expect`: `H(X) = E log (1 / p(X))`.
* `entropy_bernoulli`: the entropy of a two-point distribution is `Real.binEntropy`.
* `entropy_eq_zero_iff`: `H(p) = 0` iff `p` is deterministic.

## Notation

* `H[X ; μ]`: the entropy of `X` (scoped in `InfoTheory`).

## Implementation notes

The convention `0 log 0 = 0` is automatic, since `Real.log 0 = 0`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 2.1 and 2.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Definition (2.1).** The entropy of a pmf `p`: `H(p) = - ∑ₓ p(x) log p(x)`.
The convention `0 log 0 = 0` is built in, since `Real.log 0 = 0`. -/
def entropy (p : α → ℝ) : ℝ := -∑ x, p x * log (p x)

lemma entropy_eq_sum_negMulLog (p : α → ℝ) : entropy p = ∑ x, negMulLog (p x) := by
  simp [entropy, negMulLog, sum_neg_distrib]

/-- The entropy `H(X)` of a random variable `X` is the entropy of its law. -/
def entropyRV (μ : Ω → ℝ) (X : Ω → α) : ℝ := entropy (dist μ X)

/-- `H[X ; μ]` is the entropy `H(X)` of `X` on `(Ω, μ)`. -/
scoped notation3:max "H[" X " ; " μ "]" => entropyRV μ X

/-- The convention `0 log 0 = 0` agrees with the value of `Real.log`. -/
lemma zero_mul_log_zero : (0 : ℝ) * log 0 = 0 := by simp

/-- The convention `0 log 0 = 0` is "justified by continuity": `x log x → 0` as `x → 0`. -/
lemma tendsto_mul_log_zero : Tendsto (fun x : ℝ => x * log x) (𝓝 0) (𝓝 0) := by
  have := Real.continuous_mul_log.tendsto 0
  simpa using this

/-- "Adding terms of zero probability does not change the entropy." If `p` lives on `α` and
`e : α → β` is injective, then extending `p` by zero along `e` does not change the entropy. -/
lemma entropy_extend_zero {e : α → β} (he : Function.Injective e) (p : α → ℝ) :
    entropy (Function.extend e p 0) = entropy p := by
  classical
  rw [entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog]
  have h : ∀ b, b ∉ Set.range e → negMulLog (Function.extend e p 0 b) = 0 := by
    intro b hb
    rw [Function.extend_apply' _ _ _ (by simpa using hb)]; simp
  rw [← Finset.sum_subset (subset_univ (univ.image e)) (fun b _ hb => h b (by simpa using hb)),
    sum_image (fun x _ y _ hxy => he hxy)]
  simp [he.extend_apply]

/-- "Entropy is a functional of the distribution of `X`; it does not depend on the actual values
taken by `X`": relabelling the alphabet does not change the entropy. -/
lemma entropy_comp_equiv (e : β ≃ α) (p : α → ℝ) : entropy (p ∘ e) = entropy p := by
  simp only [entropy, Function.comp_apply]
  rw [e.sum_comp (fun a => p a * log (p a))]

/-- **Remark.** `H(X) = E_p log (1 / p(X))`. -/
lemma entropy_eq_expect (p : α → ℝ) : entropy p = expect p (fun x => log (1 / p x)) := by
  simp [entropy, expect, log_inv, mul_comm, sum_neg_distrib]

/-- `H(X) = - ∑_ω μ(ω) log p(X(ω))`, i.e. `H(X) = E log (1 / p(X))` as an expectation on the
underlying probability space. -/
lemma entropyRV_eq (μ : Ω → ℝ) (X : Ω → α) :
    H[X ; μ] = -∑ ω, μ ω * log (dist μ X (X ω)) := by
  rw [entropyRV, entropy, sum_dist_mul μ X (fun a => log (dist μ X a))]

/-- **Lemma 2.1.1.** `H(X) ≥ 0`. -/
lemma entropy_nonneg {p : α → ℝ} (hp : IsPMF p) : 0 ≤ entropy p := by
  rw [entropy_eq_sum_negMulLog]
  exact sum_nonneg fun x _ => negMulLog_nonneg (hp.nonneg x) (hp.le_one x)

lemma entropyRV_nonneg {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → α) : 0 ≤ H[X ; μ] :=
  entropy_nonneg (hμ.dist X)

/-- The entropy with logarithms to base `b`: `H_b(X) = - ∑ p(x) log_b p(x)`. -/
def entropyBase (b : ℝ) (p : α → ℝ) : ℝ := -∑ x, p x * logb b (p x)

/-- Entropy in bits, `H(X) = H₂(X)`, the book's default unit. -/
abbrev entropyBits (p : α → ℝ) : ℝ := entropyBase 2 p

/-- The natural-log entropy is the entropy in base `e` (in nats). -/
lemma entropyBase_exp_one (p : α → ℝ) : entropyBase (exp 1) p = entropy p := by
  simp [entropyBase, entropy, logb]

lemma entropyBase_eq_div (b : ℝ) (p : α → ℝ) : entropyBase b p = entropy p / log b := by
  simp [entropyBase, entropy, logb, mul_div_assoc, neg_div, sum_div]

lemma entropyBits_eq (p : α → ℝ) : entropyBits p = entropy p / log 2 :=
  entropyBase_eq_div 2 p

/-- **Lemma 2.1.2.** `H_b(X) = (log_b a) H_a(X)` (change of base). -/
lemma entropyBase_eq {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a ≠ 1) (p : α → ℝ) :
    entropyBase b p = logb b a * entropyBase a p := by
  have hla : log a ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.1 h with h | h | h <;> [linarith; exact ha₁ h; linarith]
  rw [entropyBase_eq_div, entropyBase_eq_div, logb]
  field_simp

/-- **Lemma 2.1.1** in an arbitrary base `b > 1`. -/
lemma entropyBase_nonneg {b : ℝ} (hb : 1 < b) {p : α → ℝ} (hp : IsPMF p) :
    0 ≤ entropyBase b p := by
  rw [entropyBase_eq_div]; exact div_nonneg (entropy_nonneg hp) (log_pos hb).le

/-- The entropy of a two-point distribution `(1 - p, p)` is the binary entropy function
`H(p) = -p log p - (1 - p) log (1 - p)` (Mathlib's `Real.binEntropy`). -/
lemma entropy_bernoulli (p : ℝ) :
    entropy (fun b : Bool => if b then p else 1 - p) = binEntropy p := by
  rw [entropy_eq_sum_negMulLog, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp

/-- The defining formula `H(p) = p log p⁻¹ + (1 - p) log (1 - p)⁻¹` of Mathlib's
`Real.binEntropy`, whose body is not exposed to other modules. -/
lemma binEntropy_eq_mul_log_inv (p : ℝ) :
    binEntropy p = p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹ := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog, log_inv, log_inv]
  ring

/-- The entropy of `f ∘ X` for an injective `f` equals the entropy of `X`. -/
lemma entropyRV_comp_injective (μ : Ω → ℝ) (X : Ω → α) {f : α → β}
    (hf : Function.Injective f) : H[f ∘ X ; μ] = H[X ; μ] := by
  rw [entropyRV_eq, entropyRV_eq]
  congr 1
  refine sum_congr rfl fun ω _ => ?_
  simp only [Function.comp_apply]
  rw [dist_comp_of_injective μ X hf]

/-- If `Y = f(X)` with `f` injective, then `H(Y) = H(X)`. -/
lemma entropyRV_eq_of_injective (μ : Ω → ℝ) {X : Ω → α} {Y : Ω → β} (f : α → β)
    (hf : Function.Injective f) (h : ∀ ω, Y ω = f (X ω)) : H[Y ; μ] = H[X ; μ] := by
  rw [show Y = f ∘ X from funext h]
  exact entropyRV_comp_injective μ X hf

lemma entropyRV_pair_comm (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) :
    H[pair X Y ; μ] = H[pair Y X ; μ] :=
  entropyRV_eq_of_injective μ Prod.swap Prod.swap_injective fun _ => rfl

open Classical in
/-- The entropy of a constant random variable is `0`. -/
lemma entropyRV_const {μ : Ω → ℝ} (hμ : IsPMF μ) (c : α) : H[(fun _ => c) ; μ] = 0 := by
  rw [entropyRV, entropy_eq_sum_negMulLog]
  simp [dist_const hμ, apply_ite negMulLog]

/-- **Definition (2.8).** The joint entropy of `(X, Y)`, `H(X, Y) = -∑ₓ ∑ᵧ p(x, y) log p(x, y)`,
is the entropy of the pair `pair X Y`. -/
lemma jointEntropy_def (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) :
    H[pair X Y ; μ] =
      -∑ x, ∑ y, dist μ (pair X Y) (x, y) * log (dist μ (pair X Y) (x, y)) := by
  rw [entropyRV, entropy, Fintype.sum_prod_type]

/-- (2.9) `H(X, Y) = -E log p(X, Y)`. -/
lemma jointEntropy_eq_expect (μ : Ω → ℝ) (X : Ω → α) (Y : Ω → β) :
    H[pair X Y ; μ] = -∑ ω, μ ω * log (dist μ (pair X Y) (X ω, Y ω)) :=
  entropyRV_eq μ (pair X Y)

open Classical in
/-- The entropy of a pmf vanishes iff the distribution is deterministic. -/
lemma entropy_eq_zero_iff {p : α → ℝ} (hp : IsPMF p) :
    entropy p = 0 ↔ ∃ a, ∀ x, p x = if x = a then 1 else 0 := by
  constructor
  · intro h
    rw [entropy_eq_sum_negMulLog] at h
    have h0 := (sum_eq_zero_iff_of_nonneg fun x _ =>
      negMulLog_nonneg (hp.nonneg x) (hp.le_one x)).1 h
    have h01 : ∀ x, p x = 0 ∨ p x = 1 := by
      intro x
      have := h0 x (mem_univ x)
      rw [negMulLog, mul_eq_zero, neg_eq_zero] at this
      rcases this with h | h
      · exact Or.inl h
      · rcases log_eq_zero.1 h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · linarith [hp.nonneg x]
    obtain ⟨a, ha⟩ : ∃ a, p a ≠ 0 := by
      by_contra! h'
      have := hp.sum_eq_one
      simp [h'] at this
    have ha1 : p a = 1 := (h01 a).resolve_left ha
    refine ⟨a, fun x => ?_⟩
    split_ifs with hx
    · rw [hx, ha1]
    · have := hp.sum_eq_one
      rw [← sum_erase_add _ _ (mem_univ a), ha1, add_eq_right] at this
      exact (sum_eq_zero_iff_of_nonneg fun y _ => hp.nonneg y).1 this x (by simp [hx])
  · rintro ⟨a, ha⟩
    rw [entropy_eq_sum_negMulLog]
    exact sum_eq_zero fun x _ => by rw [ha x]; split_ifs <;> simp

end InfoTheory
