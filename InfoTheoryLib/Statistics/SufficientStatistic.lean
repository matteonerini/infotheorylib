/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.Channel
public import InfoTheoryLib.MarkovChain.DataProcessing

/-!
# Sufficient statistics

A family of pmfs `{f_θ(x)}` indexed by a finite parameter set `Θ` is a channel
`f : Θ → α → ℝ`. For a distribution (prior) `w` on `Θ`, the pair `(θ, X)` has joint law
`jointOf w f`, with `θ = Prod.fst` and the sample `X = Prod.snd`.

## Main definitions

* `IsSufficient f T`: `T` is a sufficient statistic, i.e. `θ → T(X) → X` for every prior.
* `IsMinimalSufficient f T`: `T` is sufficient and a function of every sufficient statistic.

## Main statements

* `mutualInfo_statistic_le`: `I(θ; T(X)) ≤ I(θ; X)` for any statistic.
* `isSufficient_iff_mutualInfo`: `T` is sufficient iff `I(θ; X) = I(θ; T(X))` for every prior.
* `isSufficient_of_factorization`: the factorization criterion `f_θ(x) = g(θ, T(x)) h(x)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 2.9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable {Θ : Type*} [Fintype Θ]

/-- (2.123) For any statistic `T(X)` and any distribution on `θ`, `I(θ; T(X)) ≤ I(θ; X)`, by the
data processing inequality applied to `θ → X → T(X)`. -/
theorem mutualInfo_statistic_le {w : Θ → ℝ} (hw : IsPMF w) {f : Θ → α → ℝ} (hf : IsChannel f)
    (T : α → β) :
    I[Prod.fst : T ∘ Prod.snd ; jointOf w f] ≤ I[Prod.fst : Prod.snd ; jointOf w f] :=
  mutualInfo_comp_le (jointOf_isPMF hw hf) _ _ T

/-- **Definition.** A function `T(X)` is a sufficient statistic relative to the family
`{f_θ(x)}` if `X` is independent of `θ` given `T(X)` for any distribution on `θ`, i.e.
`θ → T(X) → X` forms a Markov chain. -/
def IsSufficient (f : Θ → α → ℝ) (T : α → β) : Prop :=
  ∀ w : Θ → ℝ, IsPMF w → MarkovChain (jointOf w f) Prod.fst (T ∘ Prod.snd) Prod.snd

/-- **(2.124).** `T` is sufficient iff `I(θ; X) = I(θ; T(X))` for all distributions on `θ`:
sufficient statistics preserve mutual information, and conversely. -/
theorem isSufficient_iff_mutualInfo {f : Θ → α → ℝ} (hf : IsChannel f) (T : α → β) :
    IsSufficient f T ↔ ∀ w : Θ → ℝ, IsPMF w →
      I[Prod.fst : Prod.snd ; jointOf w f] = I[Prod.fst : T ∘ Prod.snd ; jointOf w f] := by
  refine forall₂_congr fun w hw => ?_
  have hμ := jointOf_isPMF hw hf
  have h1 : I[Prod.fst : Prod.snd ; jointOf w f] =
      I[Prod.fst : pair Prod.snd (T ∘ Prod.snd) ; jointOf w f] :=
    (mutualInfo_congr_right hμ Prod.fst (fun x => (x, T x)) (fun a b h => (Prod.mk.inj h).1)
      (fun _ => rfl)).symm
  rw [h1, chain_rule_mutualInfo₂ hμ, markovChain_iff_condIndep hμ,
    ← condMutualInfo_eq_zero_iff hμ]
  constructor <;> intro h <;> linarith

open Classical in
omit [Fintype β] in
/-- The law of `(θ, T(X), X)`: `p(θ, t, x) = w(θ) f_θ(x) 1[T(x) = t]`. -/
lemma dist_param_stat_sample (μ : Θ × α → ℝ) (T : α → β) (θ : Θ) (t : β) (x : α) :
    dist μ (pair Prod.fst (pair (T ∘ Prod.snd) Prod.snd)) (θ, t, x) =
      if T x = t then μ (θ, x) else 0 := by
  split_ifs with h
  · subst h
    have := dist_eq_of_injective μ (U := id)
      (V := pair Prod.fst (pair (T ∘ Prod.snd) Prod.snd))
      (fun z : Θ × α => (z.1, T z.2, z.2))
      (fun a b h => Prod.ext (Prod.mk.inj h).1 (Prod.mk.inj (Prod.mk.inj h).2).2)
      (fun _ => rfl) (θ, x)
    rw [dist_id] at this
    exact this
  · refine dist_eq_zero_of_forall_ne μ fun ω hω => ?_
    simp only [pair_apply, Function.comp_apply, Prod.mk.injEq] at hω
    exact h (hω.2.2 ▸ hω.2.1)

open Classical in
omit [Fintype β] in
lemma dist_param_stat (μ : Θ × α → ℝ) (T : α → β) (θ : Θ) (t : β) :
    dist μ (pair Prod.fst (T ∘ Prod.snd)) (θ, t) = ∑ x, if T x = t then μ (θ, x) else 0 := by
  simp only [dist, pair_apply, Function.comp_apply, Prod.mk.injEq, Fintype.sum_prod_type,
    ite_and]
  rw [sum_eq_single θ]
  · simp
  · intro b _ hb; simp [hb]
  · simp

open Classical in
omit [Fintype β] in
lemma dist_stat_sample (μ : Θ × α → ℝ) (T : α → β) (t : β) (x : α) :
    dist μ (pair (T ∘ Prod.snd) Prod.snd) (t, x) = if T x = t then ∑ θ, μ (θ, x) else 0 := by
  simp only [dist, pair_apply, Function.comp_apply, Prod.mk.injEq, Fintype.sum_prod_type]
  split_ifs with h
  · refine sum_congr rfl fun θ _ => ?_
    rw [sum_eq_single x]
    · simp [h]
    · intro b _ hb; simp [hb]
    · simp
  · refine sum_eq_zero fun θ _ => sum_eq_zero fun y _ => ?_
    simp only [ite_eq_right_iff]
    rintro ⟨h1, rfl⟩
    exact absurd h1 h

open Classical in
omit [Fintype β] in
lemma dist_stat (μ : Θ × α → ℝ) (T : α → β) (t : β) :
    dist μ (T ∘ Prod.snd) t = ∑ θ, ∑ x, if T x = t then μ (θ, x) else 0 := by
  simp [dist, Fintype.sum_prod_type]

open Classical in
omit [Fintype β] in
/-- **Factorization criterion (sufficiency direction).** If `f_θ(x) = g(θ, T(x)) h(x)`, then
`T` is a sufficient statistic: the conditional law of `X` given `T(X)` does not depend on `θ`. -/
theorem isSufficient_of_factorization {f : Θ → α → ℝ} (hf : IsChannel f) {T : α → β}
    (g : Θ → β → ℝ) (h : α → ℝ) (hfac : ∀ θ x, f θ x = g θ (T x) * h x) : IsSufficient f T := by
  intro w hw
  have hμ := jointOf_isPMF hw hf
  rw [markovChain_iff_mul hμ]
  intro θ t x
  rw [dist_param_stat_sample, dist_stat, dist_param_stat, dist_stat_sample]
  split_ifs with hx
  · subst hx
    set H := ∑ y, if T y = T x then h y else 0
    have e1 : ∀ θ', (∑ y, if T y = T x then jointOf w f (θ', y) else 0) =
        w θ' * g θ' (T x) * H := by
      intro θ'
      simp only [H, mul_sum]
      refine sum_congr rfl fun y _ => ?_
      split_ifs with hy
      · simp [jointOf, hfac, hy]; ring
      · simp
    simp only [e1]
    simp only [jointOf, hfac, ← mul_assoc]
    rw [← sum_mul, ← sum_mul]
    ring
  · simp

/-- **Definition.** A statistic `T(X)` is a minimal sufficient statistic relative to `{f_θ(x)}`
if it is sufficient and it is a function of every other sufficient statistic `U`. -/
def IsMinimalSufficient (f : Θ → α → ℝ) (T : α → β) : Prop :=
  IsSufficient f T ∧
    ∀ (γ' : Type) [Fintype γ'] (U : α → γ'), IsSufficient f U → ∃ g : γ' → β, ∀ x, T x = g (U x)

/-- **(2.128).** If `T` is minimal sufficient and `U` is sufficient, then `T(X)` is a function of
`U(X)`, `θ → T(X) → U(X) → X`, and `I(θ; T(X)) = I(θ; U(X)) = I(θ; X)`: a minimal sufficient
statistic maximally compresses the information about `θ` in the sample. -/
theorem IsMinimalSufficient.chain {f : Θ → α → ℝ} (hf : IsChannel f) {T : α → β}
    (hT : IsMinimalSufficient f T) {γ' : Type} [Fintype γ'] {U : α → γ'} (hU : IsSufficient f U)
    {w : Θ → ℝ} (hw : IsPMF w) :
    (∃ g : γ' → β, ∀ x, T x = g (U x)) ∧
      MarkovChain (jointOf w f) Prod.fst (T ∘ Prod.snd) (U ∘ Prod.snd) ∧
      MarkovChain (jointOf w f) Prod.fst (U ∘ Prod.snd) Prod.snd ∧
      I[Prod.fst : T ∘ Prod.snd ; jointOf w f] = I[Prod.fst : U ∘ Prod.snd ; jointOf w f] ∧
      I[Prod.fst : U ∘ Prod.snd ; jointOf w f] = I[Prod.fst : Prod.snd ; jointOf w f] := by
  have hμ := jointOf_isPMF hw hf
  have h1 := (isSufficient_iff_mutualInfo hf T).1 hT.1 w hw
  have h2 := (isSufficient_iff_mutualInfo hf U).1 hU w hw
  exact ⟨hT.2 γ' U hU, (hT.1 w hw).comp_right hμ U, hU w hw, h1.symm.trans h2, h2.symm⟩

end InfoTheory
