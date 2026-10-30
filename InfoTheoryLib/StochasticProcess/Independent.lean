/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StochasticProcess.Basic
public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.Probability.IID

/-!
# Independent processes

## Main definitions

* `indepProcess ps`: the process of independent random variables `Xᵢ ∼ psᵢ`.
* `iidProcess p`: the process of i.i.d. random variables `Xᵢ ∼ p`.

## Main statements

* `entropy_snoc_mul`: the entropy of a product of two independent laws is the sum of their
  entropies.
* `jointEntropy_indepProcess`: `H(X₁, …, Xₙ) = ∑ᵢ H(Xᵢ)` for independent random variables, (4.12).
* `iidProcess_hasEntropyRate`: an i.i.d. process has entropy rate `H(X₁)`, (4.11).
* `uniformProcess_hasEntropyRate`: the "typewriter", with `m` equally likely letters, has
  entropy rate `log m`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 4.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- If `f(x₁, …, xₙ, a) = g(x₁, …, xₙ) h(a)` with `g` and `h` summing to one, then
`H(f) = H(g) + H(h)`. -/
lemma entropy_snoc_mul {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {g : (Fin n → α) → ℝ} {h : α → ℝ}
    (hf : ∀ y a, f (Fin.snoc y a) = g y * h a) (hg : ∑ y, g y = 1) (hh : ∑ a, h a = 1) :
    entropy f = entropy g + entropy h := by
  rw [entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog, sum_snoc]
  simp only [hf, negMulLog_mul, sum_add_distrib, ← sum_mul, ← mul_sum, hh, hg, one_mul]

/-- The law `∏ᵢ psᵢ(xᵢ)` of independent random variables `Xᵢ ∼ psᵢ`. -/
def indepLaw (ps : ℕ → α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := ∏ i : Fin n, ps i (x i)

omit [Fintype α] in
lemma indepLaw_snoc (ps : ℕ → α → ℝ) (n : ℕ) (x : Fin n → α) (a : α) :
    indepLaw ps (n + 1) (Fin.snoc x a) = indepLaw ps n x * ps n a := by
  simp [indepLaw, Fin.prod_univ_castSucc]

lemma sum_indepLaw {ps : ℕ → α → ℝ} (hps : ∀ i, IsPMF (ps i)) (n : ℕ) :
    ∑ x, indepLaw ps n x = 1 := by
  induction n with
  | zero => simp [indepLaw]
  | succ n ih =>
    rw [sum_snoc]
    simp [indepLaw_snoc, ← mul_sum, (hps n).sum_eq_one, ih]

/-- The process of independent random variables `Xᵢ ∼ psᵢ`. -/
def indepProcess (ps : ℕ → α → ℝ) (hps : ∀ i, IsPMF (ps i)) : StochasticProcess α where
  law := indepLaw ps
  isPMF n := ⟨fun x => prod_nonneg fun i _ => (hps i).nonneg _, sum_indepLaw hps n⟩
  consistent n x := by simp [indepLaw_snoc, ← mul_sum, (hps n).sum_eq_one]

/-- **(4.12)** For independent random variables, `H(X₁, …, Xₙ) = ∑ᵢ H(Xᵢ)`. -/
theorem jointEntropy_indepProcess {ps : ℕ → α → ℝ} (hps : ∀ i, IsPMF (ps i)) (n : ℕ) :
    (indepProcess ps hps).jointEntropy n = ∑ i ∈ range n, entropy (ps i) := by
  induction n with
  | zero => exact (indepProcess ps hps).jointEntropy_zero
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    exact entropy_snoc_mul (indepLaw_snoc ps n) (sum_indepLaw hps n) (hps n).sum_eq_one

/-- The process of i.i.d. random variables `Xᵢ ∼ p`. -/
def iidProcess (p : α → ℝ) (hp : IsPMF p) : StochasticProcess α :=
  indepProcess (fun _ => p) fun _ => hp

lemma iidProcess_law {p : α → ℝ} (hp : IsPMF p) (n : ℕ) :
    (iidProcess p hp).law n = iidPMF p n := rfl

/-- An i.i.d. process is stationary. -/
theorem iidProcess_isStationary {p : α → ℝ} (hp : IsPMF p) : (iidProcess p hp).IsStationary := by
  intro n x
  change ∑ a, ∏ i : Fin (n + 1), p (Fin.cons a x i) = ∏ i : Fin n, p (x i)
  simp [Fin.prod_univ_succ, ← sum_mul, hp.sum_eq_one]

lemma jointEntropy_iidProcess {p : α → ℝ} (hp : IsPMF p) (n : ℕ) :
    (iidProcess p hp).jointEntropy n = n * entropy p := by
  rw [iidProcess, jointEntropy_indepProcess (fun _ => hp)]
  simp

/-- **(4.11)** An i.i.d. process has entropy rate `H(X₁)`. -/
theorem iidProcess_hasEntropyRate {p : α → ℝ} (hp : IsPMF p) :
    (iidProcess p hp).HasEntropyRate (entropy p) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [jointEntropy_iidProcess, mul_div_cancel_left₀ _ hn']

/-- The entropy rate of an i.i.d. process is `H(X₁)`. -/
theorem entropyRate_iidProcess {p : α → ℝ} (hp : IsPMF p) :
    (iidProcess p hp).entropyRate = entropy p :=
  ((iidProcess_isStationary hp).hasEntropyRate).unique _ (iidProcess_hasEntropyRate hp)

/-- **The typewriter.** A typewriter producing `m` equally likely letters independently has
entropy rate `log m`. -/
theorem uniformProcess_hasEntropyRate [Nonempty α] :
    (iidProcess (uniformPMF α) uniformPMF_isPMF).HasEntropyRate (log (Fintype.card α)) := by
  have h := iidProcess_hasEntropyRate (uniformPMF_isPMF (α := α))
  have he : entropy (uniformPMF α) = log (Fintype.card α) :=
    (entropy_eq_log_card_iff uniformPMF_isPMF).2 rfl
  rwa [he] at h

end InfoTheory
