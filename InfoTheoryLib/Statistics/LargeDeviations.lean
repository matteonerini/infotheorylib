/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Statistics.Types
public import InfoTheoryLib.RelativeEntropy.Gibbs
public import InfoTheoryLib.Probability.WeakLaw

/-!
# Large deviations: the law of large numbers for types and Sanov's theorem

For `X₁, …, Xₙ` i.i.d. `∼ Q` and a set `E` of distributions, the probability that the type of
`Xⁿ` lies in `E` is at most `(n + 1)^|𝒳| e^{-nD*}`, where `D* = inf_{P ∈ E} D(P‖Q)`, and if `E` is
the closure of its interior, `(1/n) log Qⁿ(E) → -D*` (Sanov's theorem). In particular the type of
`Xⁿ` converges to `Q`: `Pr{D(P_{Xⁿ}‖Q) > ε} ≤ (n + 1)^|𝒳| e^{-nε}`.

## Main definitions

* `typeEvent E n`: the event `{xⁿ : P_{xⁿ} ∈ E}`, so that `Qⁿ(E) = Pr{typeEvent E n}` (11.89).
* `sanovExponent Q E`: `D* = inf_{P ∈ E} D(P‖Q)` (11.95).
* `IsRelInteriorPt E P`: `P` is an interior point of `E` within the probability simplex.
* `tiltedPMF Q g λ`: the distribution `Q(x) e^{λ g(x)}/∑ₐ Q(a) e^{λ g(a)}` (11.110).

## Main statements

* `prob_typeEvent_le`: **Theorem 11.4.1 (Sanov), (11.94)**.
* `prob_relEntropy_typeOf_gt_le`, `tendstoInProb_relEntropy_typeOf`: **Theorem 11.2.1**.
* `tendsto_log_prob_typeEvent`: **Theorem 11.4.1 (Sanov), (11.96)**.
* `relEntropyReal_tiltedPMF_le`: (11.109)–(11.110), the tilted distribution is the closest to `Q`
  under a linear constraint.

## Implementation notes

The almost sure convergence `D(P_{Xⁿ}‖Q) → 0` of Theorem 11.2.1 needs a probability space for the
whole sequence; we state the bound (11.69) and the convergence in probability. Interiors are taken
relative to the probability simplex, and the limit (11.96) is proved for `Q > 0`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 11.2,
  11.4 and 11.5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### The probability of a set of types -/

open Classical in
/-- **(11.89)** The event `{xⁿ : P_{xⁿ} ∈ E}`; its probability is `Qⁿ(E)`. -/
def typeEvent (E : Set (α → ℝ)) (n : ℕ) : Finset (Fin n → α) := univ.filter fun x => typeOf x ∈ E

lemma mem_typeEvent {E : Set (α → ℝ)} {n : ℕ} {x : Fin n → α} :
    x ∈ typeEvent E n ↔ typeOf x ∈ E := by
  classical
  simp [typeEvent]

open Classical in
/-- **(11.97)** `Qⁿ(E) = ∑_{P ∈ E ∩ 𝒫ₙ} Qⁿ(T(P))`. -/
lemma prob_typeEvent_eq_sum (Q : α → ℝ) (E : Set (α → ℝ)) (n : ℕ) :
    prob (iidPMF Q n) (typeEvent E n) =
      ∑ P ∈ (types α n).filter (· ∈ E), prob (iidPMF Q n) (typeClass P n) := by
  rw [prob, ← sum_fiberwise_of_maps_to (g := typeOf) (t := (types α n).filter (· ∈ E))
    fun x hx => mem_filter.2 ⟨typeOf_mem_types x, mem_typeEvent.1 hx⟩]
  refine sum_congr rfl fun P hP => ?_
  rw [prob]
  congr 1
  ext x
  simp only [mem_filter, mem_typeEvent, mem_typeClass]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h ▸ (mem_filter.1 hP).2, h⟩

/-- A type class that is not absolutely continuous with respect to `Q` has probability `0`. -/
lemma prob_typeClass_eq_zero {Q : α → ℝ} {n : ℕ} (x : Fin n → α)
    (hxQ : ¬AbsCont (typeOf x) Q) : prob (iidPMF Q n) (typeClass (typeOf x) n) = 0 := by
  classical
  simp only [AbsCont, not_forall] at hxQ
  obtain ⟨a, hQa, hPa⟩ := hxQ
  refine sum_eq_zero fun y hy => ?_
  rw [mem_typeClass] at hy
  have hN : symbolCount y a ≠ 0 := fun h => hPa (by rw [← hy, typeOf, h]; simp)
  obtain ⟨i, hi⟩ : ∃ i, y i = a := by
    by_contra hne
    push Not at hne
    exact hN (card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ => hne i))
  exact prod_eq_zero (mem_univ i) (by rw [hi, hQa])

/-- **Theorem 11.4.1 (Sanov's theorem, upper bound), (11.97)–(11.103).** If `D(P‖Q) ≥ b` for every
distribution `P ≪ Q` in `E`, then `Qⁿ(E) ≤ (n + 1)^|𝒳| e^{-nb}`. -/
theorem prob_typeEvent_le {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) {E : Set (α → ℝ)} {b : ℝ}
    (hb : ∀ P ∈ E, IsPMF P → AbsCont P Q → b ≤ relEntropyReal P Q) {n : ℕ} (hn : 0 < n) :
    prob (iidPMF Q n) (typeEvent E n) ≤ (n + 1) ^ Fintype.card α * exp (-(n * b)) := by
  classical
  rw [prob_typeEvent_eq_sum]
  calc ∑ P ∈ (types α n).filter (· ∈ E), prob (iidPMF Q n) (typeClass P n)
      ≤ ∑ _P ∈ (types α n).filter (· ∈ E), exp (-(n * b)) := by
        refine sum_le_sum fun P hP => ?_
        obtain ⟨hPt, hPE⟩ := mem_filter.1 hP
        obtain ⟨x, rfl⟩ := mem_types.1 hPt
        by_cases hxQ : AbsCont (typeOf x) Q
        · refine (prob_typeClass_le hQ hn x hxQ).trans (exp_le_exp.2 ?_)
          have := hb _ hPE (typeOf_isPMF hn x) hxQ
          have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        · rw [prob_typeClass_eq_zero x hxQ]
          exact (exp_pos _).le
    _ = ((types α n).filter (· ∈ E)).card * exp (-(n * b)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n + 1) ^ Fintype.card α * exp (-(n * b)) := by
        refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
        exact (by exact_mod_cast card_filter_le _ _ : (((types α n).filter (· ∈ E)).card : ℝ) ≤
          (types α n).card).trans (card_types_le n)

/-! ### The law of large numbers for types -/

/-- `(n + 1)^k e^{-nε} → 0`. -/
lemma tendsto_pow_mul_exp_neg_nat (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k * exp (-(n * ε))) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_natCast_atTop_atTop.atTop_mul_const hε)).const_mul ((2 / ε) ^ k)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  rw [← mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ k) (exp_pos _).le
  have : 2 / ε * (n * ε) = 2 * n := by field_simp
  rw [this]
  linarith

/-- **Theorem 11.2.1, (11.63)–(11.69).** For `Xᵢ` i.i.d. `∼ Q`,
`Pr{D(P_{Xⁿ}‖Q) > ε} ≤ (n + 1)^|𝒳| e^{-nε}`. -/
theorem prob_relEntropy_typeOf_gt_le {Q : α → ℝ} (hQ : ∀ a, 0 ≤ Q a) (ε : ℝ) {n : ℕ}
    (hn : 0 < n) :
    prob (iidPMF Q n) (univ.filter fun x : Fin n → α => ε < relEntropyReal (typeOf x) Q) ≤
      (n + 1) ^ Fintype.card α * exp (-(n * ε)) := by
  classical
  have h := prob_typeEvent_le hQ (E := {P | ε < relEntropyReal P Q}) (b := ε)
    (fun P hP _ _ => le_of_lt hP) hn
  convert h using 2
  ext x
  simp [mem_typeEvent]

/-- **Theorem 11.2.1.** The type of an i.i.d. sequence converges to its distribution:
`D(P_{Xⁿ}‖Q) → 0` in probability. -/
theorem tendstoInProb_relEntropy_typeOf {Q : α → ℝ} (hQ : IsPMF Q) :
    TendstoInProb (fun n => iidPMF Q n) (fun _ x => relEntropyReal (typeOf x) Q) 0 := by
  classical
  intro ε hε
  have hbound : ∀ᶠ n : ℕ in atTop, prob (iidPMF Q n)
      (univ.filter fun x : Fin n → α => ε ≤ |relEntropyReal (typeOf x) Q - 0|) ≤
        (n + 1) ^ Fintype.card α * exp (-(n * (ε / 2))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    refine (prob_le_prob_of_ae (iidPMF_nonneg hQ.nonneg)
      (T := univ.filter fun x : Fin n → α => ε / 2 < relEntropyReal (typeOf x) Q)
      fun x hx hx0 => ?_).trans (prob_relEntropy_typeOf_gt_le hQ.nonneg (ε / 2) hn)
    -- A sequence of positive probability has `Pₓ ≪ Q`, so `D(Pₓ‖Q) ≥ 0`.
    have hxQ : AbsCont (typeOf x) Q := by
      by_contra h
      have := prob_typeClass_eq_zero x h
      have hle : iidPMF Q n x ≤ prob (iidPMF Q n) (typeClass (typeOf x) n) :=
        single_le_sum (fun y _ => iidPMF_nonneg hQ.nonneg y) (mem_typeClass.2 rfl)
      exact hx0 (le_antisymm (this ▸ hle) (iidPMF_nonneg hQ.nonneg x))
    have hD := relEntropyReal_nonneg (typeOf_isPMF hn x) hQ hxQ
    simp only [mem_filter, mem_univ, true_and, sub_zero, abs_of_nonneg hD] at hx ⊢
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_pow_mul_exp_neg_nat _ (half_pos hε))
    (Eventually.of_forall fun n => prob_nonneg (iidPMF_nonneg hQ.nonneg) _) hbound

/-! ### Sanov's theorem -/

/-- **(11.95)** The exponent `D* = inf_{P ∈ E} D(P‖Q)` of Sanov's theorem. -/
def sanovExponent (Q : α → ℝ) (E : Set (α → ℝ)) : ℝ :=
  sInf {d | ∃ P ∈ E, IsPMF P ∧ AbsCont P Q ∧ relEntropyReal P Q = d}

lemma sanovExponent_le {Q : α → ℝ} (hQ : IsPMF Q) {E : Set (α → ℝ)} {P : α → ℝ} (hPE : P ∈ E)
    (hP : IsPMF P) (hPQ : AbsCont P Q) : sanovExponent Q E ≤ relEntropyReal P Q :=
  csInf_le ⟨0, fun _ ⟨_, _, hP, hPQ, h⟩ => h ▸ relEntropyReal_nonneg hP hQ hPQ⟩
    ⟨P, hPE, hP, hPQ, rfl⟩

/-- **Theorem 11.4.1 (Sanov's theorem), (11.94).** `Qⁿ(E) ≤ (n + 1)^|𝒳| e^{-nD*}`. -/
theorem prob_typeEvent_le_sanov {Q : α → ℝ} (hQ : IsPMF Q) (E : Set (α → ℝ)) {n : ℕ}
    (hn : 0 < n) :
    prob (iidPMF Q n) (typeEvent E n) ≤
      (n + 1) ^ Fintype.card α * exp (-(n * sanovExponent Q E)) :=
  prob_typeEvent_le hQ.nonneg (fun _ hPE hP hPQ => sanovExponent_le hQ hPE hP hPQ) hn

/-- `P ↦ D(P‖Q)` is continuous when `Q > 0`. -/
lemma continuous_relEntropyReal_left {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) :
    Continuous fun P : α → ℝ => relEntropyReal P Q := by
  have h : (fun P : α → ℝ => relEntropyReal P Q) =
      fun P => ∑ a, (-negMulLog (P a) - P a * log (Q a)) := by
    funext P
    refine sum_congr rfl fun a _ => ?_
    rcases eq_or_ne (P a) 0 with h0 | h0
    · simp [h0]
    · rw [negMulLog, log_div h0 (hQ a).ne']
      ring
  rw [h]
  exact continuous_finsetSum _ fun a _ =>
    (continuous_negMulLog.comp (continuous_apply a)).neg.sub
      ((continuous_apply a).mul continuous_const)

/-- `P` is an interior point of `E` relative to the probability simplex: every distribution close
enough to `P` lies in `E`. -/
def IsRelInteriorPt (E : Set (α → ℝ)) (P : α → ℝ) : Prop :=
  ∃ δ > 0, ∀ P' : α → ℝ, IsPMF P' → (∀ a, |P' a - P a| < δ) → P' ∈ E

/-- `log (n + 1)/n → 0`. -/
lemma tendsto_log_add_one_div : Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  refine h.congr fun n => ?_
  simp

/-- Continuity of `D(·‖Q)` in the coordinatewise form. -/
lemma exists_relEntropyReal_lt {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) (P : α → ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ η > 0, ∀ P' : α → ℝ, (∀ a, |P' a - P a| < η) →
      relEntropyReal P' Q < relEntropyReal P Q + ε := by
  obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.1 (continuous_relEntropyReal_left hQ).continuousAt
    ε hε
  refine ⟨η, hη, fun P' hP' => ?_⟩
  have := h ((dist_pi_lt_iff hη).2 fun a => by rw [Real.dist_eq]; exact hP' a)
  rw [Real.dist_eq] at this
  linarith [(abs_lt.1 this).2]

/-- **(11.104)–(11.107)** The lower bound of Sanov's theorem: if `Q > 0` and `E` contains, for
every `ε > 0`, an interior point `P'` with `D(P'‖Q) < D* + ε`, then eventually `Qⁿ(E) > 0` and
`(1/n) log Qⁿ(E) ≥ -D* - ε`. -/
theorem eventually_neg_sub_le_log_prob {Q : α → ℝ} (hQ : IsPMF Q) (hQpos : ∀ a, 0 < Q a)
    {E : Set (α → ℝ)} {P : α → ℝ} (hP : IsPMF P) (hint : IsRelInteriorPt E P) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, 0 < prob (iidPMF Q n) (typeEvent E n) ∧
      -relEntropyReal P Q - ε ≤ log (prob (iidPMF Q n) (typeEvent E n)) / n := by
  obtain ⟨δ, hδ, hE⟩ := hint
  obtain ⟨η, hη, hD⟩ := exists_relEntropyReal_lt hQpos P (half_pos hε)
  set k := Fintype.card α
  have hk : Tendsto (fun n : ℕ => (k : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlog := tendsto_log_add_one_div.const_mul (k : ℝ)
  rw [mul_zero] at hlog
  filter_upwards [hk.eventually (gt_mem_nhds (lt_min hδ hη)), hlog.eventually
    (gt_mem_nhds (half_pos hε)), eventually_gt_atTop 0] with n hkn hlogn hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨x, hx, -⟩ := exists_typeOf_near hP hn
  have hxQ : AbsCont (typeOf x) Q := fun a h => absurd h (hQpos a).ne'
  have hclose : ∀ a, |typeOf x a - P a| < min δ η := fun a => (hx a).trans_lt hkn
  have hxE : typeOf x ∈ E :=
    hE _ (typeOf_isPMF hn x) fun a => (hclose a).trans_le (min_le_left _ _)
  have hDx := hD _ fun a => (hclose a).trans_le (min_le_right _ _)
  -- `Qⁿ(E) ≥ Qⁿ(T(Pₓ)) ≥ e^{-nD(Pₓ‖Q)}/(n + 1)^|𝒳|`.
  have hsub : prob (iidPMF Q n) (typeClass (typeOf x) n) ≤ prob (iidPMF Q n) (typeEvent E n) :=
    prob_mono (iidPMF_nonneg hQ.nonneg) fun y hy => mem_typeEvent.2 (mem_typeClass.1 hy ▸ hxE)
  have hlow := (exp_div_le_prob_typeClass hQ.nonneg hn x hxQ).trans hsub
  have hpos : 0 < exp (-(n * relEntropyReal (typeOf x) Q)) / (n + 1) ^ k := by positivity
  refine ⟨hpos.trans_le hlow, ?_⟩
  rw [le_div_iff₀ hn']
  have h1 := log_le_log hpos hlow
  rw [log_div (exp_pos _).ne' (by positivity), log_exp, log_pow] at h1
  have h2 : (k : ℝ) * log (n + 1) < ε / 2 * n := by
    have := hlogn
    rw [mul_div_assoc', div_lt_iff₀ hn'] at this
    linarith
  nlinarith

/-- **Theorem 11.4.1 (Sanov's theorem), (11.96).** Let `Q > 0` and let `E` be a set of
distributions contained in the closure of its interior (relative to the simplex). Then
`(1/n) log Qⁿ(E) → -D*`, with `D* = inf_{P ∈ E} D(P‖Q)`. -/
theorem tendsto_log_prob_typeEvent {Q : α → ℝ} (hQ : IsPMF Q) (hQpos : ∀ a, 0 < Q a)
    {E : Set (α → ℝ)} (hE : ∃ P ∈ E, IsPMF P)
    (hint : ∀ P ∈ E, IsPMF P → ∀ ε > 0, ∃ P', IsPMF P' ∧ IsRelInteriorPt E P' ∧
      ∀ a, |P' a - P a| < ε) :
    Tendsto (fun n : ℕ => log (prob (iidPMF Q n) (typeEvent E n)) / n) atTop
      (𝓝 (-sanovExponent Q E)) := by
  set D := sanovExponent Q E
  have habs : ∀ P : α → ℝ, AbsCont P Q := fun P a h => absurd h (hQpos a).ne'
  -- For every `ε > 0`, eventually `Qⁿ(E) > 0` and `(1/n) log Qⁿ(E) ≥ -D* - ε`.
  have hlow : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 0 < prob (iidPMF Q n) (typeEvent E n) ∧
      -D - ε ≤ log (prob (iidPMF Q n) (typeEvent E n)) / n := by
    intro ε hε
    obtain ⟨P₀, hP₀E, hP₀⟩ := hE
    have hne : {d | ∃ P ∈ E, IsPMF P ∧ AbsCont P Q ∧ relEntropyReal P Q = d}.Nonempty :=
      ⟨_, P₀, hP₀E, hP₀, habs P₀, rfl⟩
    obtain ⟨_, ⟨P₁, hP₁E, hP₁, -, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
      (show D < D + ε / 3 by linarith)
    obtain ⟨η, hη, hDη⟩ := exists_relEntropyReal_lt hQpos P₁ (show 0 < ε / 3 by positivity)
    obtain ⟨P₂, hP₂, hint₂, hP₂close⟩ := hint P₁ hP₁E hP₁ η hη
    have hD₂ := hDη P₂ hP₂close
    filter_upwards [eventually_neg_sub_le_log_prob hQ hQpos hP₂ hint₂
      (show 0 < ε / 3 by positivity)] with n hn
    exact ⟨hn.1, by linarith [hn.2]⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hlow ((-D - a) / 2) (by linarith)] with n hn
    linarith [hn.2]
  · -- The upper bound `(1/n) log Qⁿ(E) ≤ |𝒳| log (n + 1)/n - D*`.
    have hlog := tendsto_log_add_one_div.const_mul (Fintype.card α : ℝ)
    rw [mul_zero] at hlog
    filter_upwards [hlow 1 one_pos, hlog.eventually (gt_mem_nhds (show 0 < a + D by linarith)),
      eventually_gt_atTop 0] with n hn hlogn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hup := prob_typeEvent_le_sanov hQ E hn0
    have h1 := log_le_log hn.1 hup
    rw [log_mul (by positivity) (exp_pos _).ne', log_exp, log_pow] at h1
    rw [div_lt_iff₀ hn']
    rw [mul_div_assoc', div_lt_iff₀ hn'] at hlogn
    nlinarith

/-! ### The closest distribution under a linear constraint -/

/-- **(11.110)** The tilted distribution `P_λ(x) = Q(x) e^{λ g(x)}/∑ₐ Q(a) e^{λ g(a)}`. -/
def tiltedPMF (Q g : α → ℝ) (lam : ℝ) (x : α) : ℝ :=
  Q x * exp (lam * g x) / ∑ a, Q a * exp (lam * g a)

lemma sum_tiltedPMF_pos {Q : α → ℝ} (hQ : IsPMF Q) (g : α → ℝ) (lam : ℝ) :
    0 < ∑ a, Q a * exp (lam * g a) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < Q a := by
    by_contra h
    push Not at h
    have : ∑ a, Q a ≤ 0 := sum_nonpos fun a _ => h a
    linarith [hQ.sum_eq_one]
  exact lt_of_lt_of_le (mul_pos ha₀ (exp_pos _)) (single_le_sum
    (f := fun a => Q a * exp (lam * g a)) (fun a _ => mul_nonneg (hQ.nonneg a) (exp_pos _).le)
    (mem_univ a₀))

lemma tiltedPMF_isPMF {Q : α → ℝ} (hQ : IsPMF Q) (g : α → ℝ) (lam : ℝ) :
    IsPMF (tiltedPMF Q g lam) :=
  ⟨fun x => div_nonneg (mul_nonneg (hQ.nonneg x) (exp_pos _).le) (sum_tiltedPMF_pos hQ g lam).le,
    by simp only [tiltedPMF, ← sum_div]; exact div_self (sum_tiltedPMF_pos hQ g lam).ne'⟩

/-- **(11.108)–(11.110)** For `λ ≥ 0`, the tilted distribution `P_λ` is the distribution closest to
`Q` in relative entropy among those with `∑ₓ P(x) g(x) ≥ ∑ₓ P_λ(x) g(x)`. -/
theorem relEntropyReal_tiltedPMF_le {Q : α → ℝ} (hQ : IsPMF Q) (g : α → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) {P : α → ℝ} (hP : IsPMF P) (hPQ : AbsCont P Q)
    (hg : ∑ x, tiltedPMF Q g lam x * g x ≤ ∑ x, P x * g x) :
    relEntropyReal (tiltedPMF Q g lam) Q ≤ relEntropyReal P Q := by
  have h1 := neg_log_sum_le_relEntropyReal_add hP hQ.nonneg hPQ fun x => -(lam * g x)
  have h2 := relEntropyReal_gibbs_add (r := Q) fun x => -(lam * g x)
  simp only [neg_neg] at h1 h2
  have hZ := sum_tiltedPMF_pos hQ g lam
  have h2 := h2 hZ
  change relEntropyReal (tiltedPMF Q g lam) Q + ∑ x, tiltedPMF Q g lam x * -(lam * g x) =
    -log (∑ a, Q a * exp (lam * g a)) at h2
  have e1 : ∑ x, P x * -(lam * g x) = -(lam * ∑ x, P x * g x) := by
    rw [mul_sum, ← sum_neg_distrib]; exact sum_congr rfl fun x _ => by ring
  have e2 : ∑ x, tiltedPMF Q g lam x * -(lam * g x) = -(lam * ∑ x, tiltedPMF Q g lam x * g x) := by
    rw [mul_sum, ← sum_neg_distrib]; exact sum_congr rfl fun x _ => by ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 := mul_le_mul_of_nonneg_left hg hlam
  linarith

end InfoTheory
