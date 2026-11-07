/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Statistics.LargeDeviations
public import InfoTheoryLib.RelativeEntropy.Pinsker

/-!
# The Pythagorean theorem for relative entropy and the conditional limit theorem

If `P*` minimizes `D(P‖Q)` over a convex set `E`, then `D(P‖Q) ≥ D(P‖P*) + D(P*‖Q)` for every
`P ∈ E`: relative entropy behaves like a squared Euclidean distance. Consequently, given that the
type of an i.i.d. sequence lies in `E`, the type is close to `P*` with probability tending to
`1`, and the conditional law of `X₁` tends to `P*`.

## Main definitions

* `condProb μ S T`: the conditional probability `Pr(S | T)`.

## Main statements

* `relEntropy_pythagorean`: **Theorem 11.6.1**, (11.122)–(11.130).
* `tendsto_condProb_relEntropy_gt`: (11.155)–(11.170), `Pr(D(P_{Xⁿ}‖P*) > 2δ | P_{Xⁿ} ∈ E) → 0`.
* `tendsto_condProb_abs_typeOf_sub`: `Pr(|P_{Xⁿ}(a) - P*(a)| ≥ ε | P_{Xⁿ} ∈ E) → 0`.
* `tendsto_condProb_first_eq`: **Theorem 11.6.2 (conditional limit theorem)**,
  `Pr(X₁ = a | P_{Xⁿ} ∈ E) → P*(a)`.

## Implementation notes

We assume `Q > 0`, so that the relative entropies `D(P‖Q)` are finite and continuous. As for
Sanov's theorem, the probability of `E` is bounded below using interior points of `E` relative to
the simplex whose relative entropy is close to `D(P*‖Q)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 11.6
-/

open Real Finset Filter Topology
open Set (Ioo)

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### The Pythagorean theorem -/

section Pythagorean

variable {Q Ps P : α → ℝ}

/-- The mixture `P_λ = λP + (1 - λ)P*` (11.123). -/
private def mix (P Ps : α → ℝ) (lam : ℝ) (x : α) : ℝ := lam * P x + (1 - lam) * Ps x

/-- `∑ (P - P*)(log P_λ - log Q)`, the derivative of `D(P_λ‖Q)` at `λ` up to the factor `λ`. -/
private def slope (Q P Ps : α → ℝ) (lam : ℝ) : ℝ :=
  ∑ x, (P x - Ps x) * (log (mix P Ps lam x) - log (Q x))

lemma relEntropyReal_eq_sum_of_pos (hQ : ∀ a, 0 < Q a) (R : α → ℝ) :
    relEntropyReal R Q = ∑ x, (R x * log (R x) - R x * log (Q x)) := by
  refine sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (R x) 0 with h0 | h0
  · simp [h0]
  · rw [log_div h0 (hQ x).ne']
    ring

/-- **(11.124)–(11.126)** If `P*` minimizes `D(·‖Q)` along the segment from `P*` to `P`, then the
slope `∑ (P - P*)(log P_λ - log Q)` is nonnegative for `0 < λ < 1`. -/
private lemma slope_nonneg (hQ : ∀ a, 0 < Q a) (hP : IsPMF P) (hPs : IsPMF Ps)
    (hmin : ∀ lam ∈ Ioo (0 : ℝ) 1, relEntropyReal Ps Q ≤ relEntropyReal (mix P Ps lam) Q)
    {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1) : 0 ≤ slope Q P Ps lam := by
  have hmix_nonneg : ∀ x, 0 ≤ mix P Ps lam x := fun x =>
    add_nonneg (mul_nonneg hlam.1.le (hP.nonneg x)) (mul_nonneg (by linarith [hlam.2])
      (hPs.nonneg x))
  -- `φ(P_λ) - φ(P*) ≤ (P_λ - P*)(log P_λ + 1)` with `φ(t) = t log t`.
  have hterm : ∀ x, mix P Ps lam x * log (mix P Ps lam x) - Ps x * log (Ps x) ≤
      (mix P Ps lam x - Ps x) * (log (mix P Ps lam x) + 1) := by
    intro x
    have hb0 : mix P Ps lam x = 0 → Ps x = 0 := fun h => by
      have h1 := mul_nonneg hlam.1.le (hP.nonneg x)
      have h2 := mul_nonneg (by linarith [hlam.2] : (0 : ℝ) ≤ 1 - lam) (hPs.nonneg x)
      have h3 : (1 - lam) * Ps x = 0 := by simp only [mix] at h; linarith
      exact (mul_eq_zero.1 h3).resolve_left (by linarith [hlam.2])
    have := sub_le_mul_log_div (hPs.nonneg x) (hmix_nonneg x) hb0
    rcases eq_or_ne (mix P Ps lam x) 0 with h0 | h0
    · simp [h0, hb0 h0]
    · rw [mul_log_div_eq_sub h0] at this
      nlinarith
  have hdiff : relEntropyReal (mix P Ps lam) Q - relEntropyReal Ps Q ≤ lam * slope Q P Ps lam := by
    rw [relEntropyReal_eq_sum_of_pos hQ, relEntropyReal_eq_sum_of_pos hQ, ← sum_sub_distrib,
      slope, mul_sum]
    have hone : ∑ x, lam * (P x - Ps x) = 0 := by
      rw [← mul_sum, sum_sub_distrib, hP.sum_eq_one, hPs.sum_eq_one, sub_self, mul_zero]
    calc ∑ x, (mix P Ps lam x * log (mix P Ps lam x) - mix P Ps lam x * log (Q x) -
          (Ps x * log (Ps x) - Ps x * log (Q x)))
        ≤ ∑ x, (lam * ((P x - Ps x) * (log (mix P Ps lam x) - log (Q x))) +
          lam * (P x - Ps x)) := sum_le_sum fun x _ => by
          have h := hterm x
          have e : mix P Ps lam x - Ps x = lam * (P x - Ps x) := by simp only [mix]; ring
          rw [e] at h
          have e2 : mix P Ps lam x * log (Q x) - Ps x * log (Q x) =
              lam * (P x - Ps x) * log (Q x) := by rw [← sub_mul, e]
          linarith
      _ = ∑ x, lam * ((P x - Ps x) * (log (mix P Ps lam x) - log (Q x))) := by
          rw [sum_add_distrib, hone, add_zero]
  have := hmin lam hlam
  nlinarith [hlam.1]

omit [Fintype α] in
/-- The terms of the slope with `P*(x) > 0` are continuous at `λ = 0`. -/
private lemma continuousAt_term {x : α} (hx : 0 < Ps x) :
    ContinuousAt (fun lam => (P x - Ps x) * (log (mix P Ps lam x) - log (Q x))) 0 := by
  refine continuousAt_const.mul (ContinuousAt.sub ?_ continuousAt_const)
  refine ContinuousAt.log (by unfold mix; fun_prop) ?_
  simp [mix, hx.ne']

/-- **Theorem 11.6.1 (Pythagorean theorem for relative entropy).** Let `Q > 0`, let `E` be a
convex set of distributions and let `P* ∈ E` minimize `D(P‖Q)` over `E`. Then every `P ∈ E` has
`P ≪ P*` and `D(P‖Q) ≥ D(P‖P*) + D(P*‖Q)`. -/
theorem relEntropy_pythagorean (hQpos : ∀ a, 0 < Q a) {E : Set (α → ℝ)}
    (hEconv : Convex ℝ E) (hEpmf : ∀ P ∈ E, IsPMF P) (hPsE : Ps ∈ E)
    (hmin : ∀ P ∈ E, relEntropyReal Ps Q ≤ relEntropyReal P Q) (hPE : P ∈ E) :
    AbsCont P Ps ∧ relEntropyReal P Ps + relEntropyReal Ps Q ≤ relEntropyReal P Q := by
  classical
  have hP := hEpmf P hPE
  have hPs := hEpmf Ps hPsE
  have hmin' : ∀ lam ∈ Ioo (0 : ℝ) 1, relEntropyReal Ps Q ≤ relEntropyReal (mix P Ps lam) Q :=
    fun lam hlam => hmin _ (by
      have := hEconv hPE hPsE hlam.1.le (by linarith [hlam.2] : (0 : ℝ) ≤ 1 - lam)
        (by ring)
      convert this using 1
      funext x
      simp [mix])
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  have hslope : ∀ᶠ lam in 𝓝[>] (0 : ℝ), 0 ≤ slope Q P Ps lam :=
    hev.mono fun lam hlam => slope_nonneg hQpos hP hPs hmin' hlam
  -- `P ≪ P*`: otherwise the slope tends to `-∞`.
  have habs : AbsCont P Ps := by
    by_contra hnot
    simp only [AbsCont, not_forall] at hnot
    obtain ⟨x₀, hPs0, hP0⟩ := hnot
    have hP0' : 0 < P x₀ := lt_of_le_of_ne (hP.nonneg x₀) (Ne.symm hP0)
    set S := univ.filter fun x => Ps x = 0 ∧ 0 < P x
    have hx₀S : x₀ ∈ S := by simp [S, hPs0, hP0']
    set u : ℝ → ℝ := fun lam => ∑ x ∈ univ.filter (fun x => ¬(Ps x = 0 ∧ 0 < P x)),
      (P x - Ps x) * (log (mix P Ps lam x) - log (Q x))
    have hterm : ∀ x ∈ univ.filter (fun x => ¬(Ps x = 0 ∧ 0 < P x)),
        Tendsto (fun lam => (P x - Ps x) * (log (mix P Ps lam x) - log (Q x))) (𝓝 0)
          (𝓝 ((P x - Ps x) * (log (mix P Ps 0 x) - log (Q x)))) := by
      intro x hx
      rcases (hPs.nonneg x).eq_or_lt with h0 | h0
      · have hPx : P x = 0 := by
          simp only [mem_filter, mem_univ, true_and, not_and, not_lt] at hx
          exact le_antisymm (hx h0.symm) (hP.nonneg x)
        simp only [hPx, ← h0, sub_self, zero_mul]
        exact tendsto_const_nhds
      · exact (continuousAt_term h0).tendsto
    have hu : Tendsto u (𝓝 0) (𝓝 (u 0)) := tendsto_finsetSum _ hterm
    have hu1 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), u lam < u 0 + 1 :=
      (hu.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by linarith))
    set C₂ := ∑ x ∈ S.erase x₀, P x * (log (P x) - log (Q x))
    have hbound : ∀ lam ∈ Ioo (0 : ℝ) 1, slope Q P Ps lam ≤
        P x₀ * (log lam + (log (P x₀) - log (Q x₀))) + C₂ + u lam := by
      intro lam hlam
      rw [slope, ← sum_filter_add_sum_filter_not univ (fun x => Ps x = 0 ∧ 0 < P x)]
      have hS : ∀ x ∈ S, (P x - Ps x) * (log (mix P Ps lam x) - log (Q x)) =
          P x * (log lam + (log (P x) - log (Q x))) := by
        intro x hx
        simp only [S, mem_filter, mem_univ, true_and] at hx
        simp only [mix, hx.1, mul_zero, add_zero, sub_zero]
        rw [log_mul hlam.1.ne' hx.2.ne']
        ring
      rw [sum_congr rfl hS, ← add_sum_erase _ _ hx₀S]
      have hrest : ∑ x ∈ S.erase x₀, P x * (log lam + (log (P x) - log (Q x))) ≤ C₂ :=
        sum_le_sum fun x _ => by
          have hPx : 0 ≤ P x := hP.nonneg x
          have hlog : log lam ≤ 0 := log_nonpos hlam.1.le hlam.2.le
          nlinarith
      linarith
    have hlim : Tendsto (fun lam => P x₀ * (log lam + (log (P x₀) - log (Q x₀))) + C₂ +
        (u 0 + 1)) (𝓝[>] 0) atBot :=
      tendsto_atBot_add_const_right _ _ (tendsto_atBot_add_const_right _ _
        ((tendsto_atBot_add_const_right _ _ tendsto_log_nhdsGT_zero).const_mul_atBot hP0'))
    obtain ⟨lam, h1, h2, h3, h4⟩ :=
      ((hlim.eventually (eventually_lt_atBot 0)).and (hev.and (hslope.and hu1))).exists
    have := hbound lam h2
    linarith
  refine ⟨habs, ?_⟩
  -- The slope is continuous at `λ = 0`, hence nonnegative there.
  have hcont : Tendsto (slope Q P Ps) (𝓝 0) (𝓝 (slope Q P Ps 0)) := by
    refine tendsto_finsetSum _ fun x _ => ?_
    rcases (hPs.nonneg x).eq_or_lt with h0 | h0
    · have hPx : P x = 0 := habs x h0.symm
      simp only [hPx, ← h0, sub_self, zero_mul]
      exact tendsto_const_nhds
    · exact (continuousAt_term h0).tendsto
  have h0 : 0 ≤ slope Q P Ps 0 := ge_of_tendsto (hcont.mono_left nhdsWithin_le_nhds) hslope
  -- **(11.127)–(11.130)** The slope at `0` is `D(P‖Q) - D(P‖P*) - D(P*‖Q)`.
  have hid : relEntropyReal P Q - relEntropyReal P Ps - relEntropyReal Ps Q = slope Q P Ps 0 := by
    rw [relEntropyReal, relEntropyReal, relEntropyReal, slope, ← sum_sub_distrib,
      ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => ?_
    simp only [mix, zero_mul, sub_zero, one_mul, zero_add]
    have hQx := (hQpos x).ne'
    rcases eq_or_ne (P x) 0 with hP0 | hP0
    · simp only [hP0, zero_mul, zero_sub]
      rw [mul_log_div_eq_sub hQx]
      ring
    · have hPs0 : Ps x ≠ 0 := fun h => hP0 (habs x h)
      rw [mul_log_div_eq_sub hQx, mul_log_div_eq_sub hPs0, mul_log_div_eq_sub hQx]
      ring
  linarith

end Pythagorean

/-! ### The conditional limit theorem -/

/-- The conditional probability `Pr(S | T) = Pr(S ∩ T)/Pr(T)`. -/
def condProb {Ω : Type*} [DecidableEq Ω] (μ : Ω → ℝ) (S T : Finset Ω) : ℝ :=
  prob μ (S ∩ T) / prob μ T

section CondLimit

variable [DecidableEq α] {Q Ps : α → ℝ} {E : Set (α → ℝ)}

/-- **(11.155)–(11.170)** Given that the type of an i.i.d. sequence lies in `E`, it is within
`2δ` of `P*` in relative entropy with probability tending to `1`. -/
theorem tendsto_condProb_relEntropy_gt (hQ : IsPMF Q) (hQpos : ∀ a, 0 < Q a)
    (hEconv : Convex ℝ E) (hEpmf : ∀ P ∈ E, IsPMF P) (hPsE : Ps ∈ E)
    (hmin : ∀ P ∈ E, relEntropyReal Ps Q ≤ relEntropyReal P Q)
    (hint : ∀ ε > 0, ∃ P', IsPMF P' ∧ IsRelInteriorPt E P' ∧
      relEntropyReal P' Q < relEntropyReal Ps Q + ε) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => condProb (iidPMF Q n)
      (univ.filter fun x : Fin n → α => 2 * δ < relEntropyReal (typeOf x) Ps) (typeEvent E n))
      atTop (𝓝 0) := by
  classical
  set D := relEntropyReal Ps Q
  obtain ⟨P', hP', hint', hD'⟩ := hint (δ / 2) (half_pos hδ)
  set k := Fintype.card α
  -- `Qⁿ(E) ≥ e^{-n(D* + δ)}` eventually.
  have hlow : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ exp (-(n * (D + δ))) ≤ prob (iidPMF Q n) (typeEvent E n) := by
    filter_upwards [eventually_neg_sub_le_log_prob hQ hQpos hP' hint' (half_pos hδ),
      eventually_gt_atTop 0] with n hn hn0
    refine ⟨hn0, ?_⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [← exp_log hn.1]
    refine exp_le_exp.2 ?_
    have := hn.2
    rw [le_div_iff₀ hn'] at this
    nlinarith
  -- The atypical part has probability at most `(n + 1)^|𝒳| e^{-n(D* + 2δ)}`.
  have hup : ∀ n : ℕ, 0 < n → prob (iidPMF Q n)
      ((univ.filter fun x : Fin n → α => 2 * δ < relEntropyReal (typeOf x) Ps) ∩ typeEvent E n) ≤
        (n + 1) ^ k * exp (-(n * (D + 2 * δ))) := by
    intro n hn
    refine le_trans (prob_mono (iidPMF_nonneg hQ.nonneg)
      (T := typeEvent {P | P ∈ E ∧ D + 2 * δ < relEntropyReal P Q} n) fun x hx => ?_)
      (prob_typeEvent_le (E := {P | P ∈ E ∧ D + 2 * δ < relEntropyReal P Q}) hQ.nonneg
        (fun P hP _ _ => hP.2.le) hn)
    rw [mem_inter, mem_filter, mem_typeEvent] at hx
    rw [mem_typeEvent]
    refine ⟨hx.2, ?_⟩
    have := (relEntropy_pythagorean hQpos hEconv hEpmf hPsE hmin hx.2).2
    linarith [hx.1.2]
  have hlim := (tendsto_pow_mul_exp_neg_nat k hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => div_nonneg (prob_nonneg (iidPMF_nonneg hQ.nonneg) _)
      (prob_nonneg (iidPMF_nonneg hQ.nonneg) _)) ?_
  filter_upwards [hlow] with n hn
  have hpos : 0 < prob (iidPMF Q n) (typeEvent E n) := (exp_pos _).trans_le hn.2
  rw [condProb, div_le_iff₀ hpos]
  calc _ ≤ ((n : ℝ) + 1) ^ k * exp (-(n * (D + 2 * δ))) := hup n hn.1
    _ = ((n : ℝ) + 1) ^ k * exp (-(n * δ)) * exp (-(n * (D + δ))) := by
        rw [mul_assoc, ← exp_add]
        congr 2
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn.2 (by positivity)

/-- **(11.170)–(11.171)** Given that the type of an i.i.d. sequence lies in `E`, each frequency
`P_{Xⁿ}(a)` is within `ε` of `P*(a)` with probability tending to `1` (by Pinsker's inequality). -/
theorem tendsto_condProb_abs_typeOf_sub (hQ : IsPMF Q) (hQpos : ∀ a, 0 < Q a)
    (hEconv : Convex ℝ E) (hEpmf : ∀ P ∈ E, IsPMF P) (hPsE : Ps ∈ E)
    (hmin : ∀ P ∈ E, relEntropyReal Ps Q ≤ relEntropyReal P Q)
    (hint : ∀ ε > 0, ∃ P', IsPMF P' ∧ IsRelInteriorPt E P' ∧
      relEntropyReal P' Q < relEntropyReal Ps Q + ε) (a : α) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => condProb (iidPMF Q n)
      (univ.filter fun x : Fin n → α => ε ≤ |typeOf x a - Ps a|) (typeEvent E n))
      atTop (𝓝 0) := by
  classical
  have h := tendsto_condProb_relEntropy_gt hQ hQpos hEconv hEpmf hPsE hmin hint
    (show 0 < ε ^ 2 / 8 by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun n => div_nonneg (prob_nonneg (iidPMF_nonneg hQ.nonneg) _)
      (prob_nonneg (iidPMF_nonneg hQ.nonneg) _)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine div_le_div_of_nonneg_right (prob_mono (iidPMF_nonneg hQ.nonneg) fun x hx => ?_)
    (prob_nonneg (iidPMF_nonneg hQ.nonneg) _)
  rw [mem_inter, mem_filter] at hx ⊢
  refine ⟨⟨mem_univ _, ?_⟩, hx.2⟩
  have hxE := mem_typeEvent.1 hx.2
  have habs := (relEntropy_pythagorean hQpos hEconv hEpmf hPsE hmin hxE).1
  have hpin := pinsker (typeOf_isPMF hn x) (hEpmf _ hPsE) habs
  have hl1 : |typeOf x a - Ps a| ≤ l1Dist (typeOf x) Ps :=
    single_le_sum (f := fun b => |typeOf x b - Ps b|) (fun b _ => abs_nonneg _) (mem_univ a)
  have h1 := hx.1.2
  have : ε ^ 2 ≤ l1Dist (typeOf x) Ps ^ 2 := pow_le_pow_left₀ hε.le (h1.trans hl1) 2
  nlinarith

/-- **Exchangeability.** `Pr(X₁ = a, P_{Xⁿ} ∈ E) = E[P_{Xⁿ}(a) 1(P_{Xⁿ} ∈ E)]`. -/
lemma prob_first_eq_inter (Q : α → ℝ) (E : Set (α → ℝ)) (n : ℕ) (a : α) :
    prob (iidPMF Q (n + 1)) ((univ.filter fun x : Fin (n + 1) → α => x 0 = a) ∩
      typeEvent E (n + 1)) = ∑ x ∈ typeEvent E (n + 1), iidPMF Q (n + 1) x * typeOf x a := by
  classical
  -- Each coordinate `Xᵢ` gives the same probability, by the symmetry `x ↦ x ∘ (0 i)`.
  have hsym : ∀ i : Fin (n + 1), ∑ x ∈ typeEvent E (n + 1),
      iidPMF Q (n + 1) x * (if x i = a then 1 else 0) =
      ∑ x ∈ typeEvent E (n + 1), iidPMF Q (n + 1) x * (if x 0 = a then 1 else 0) := by
    intro i
    set σ := Equiv.swap (0 : Fin (n + 1)) i
    refine sum_nbij' (fun x => x ∘ σ) (fun x => x ∘ σ) (fun x hx => ?_) (fun x hx => ?_)
      (fun x _ => by funext j; simp [σ]) (fun x _ => by funext j; simp [σ]) fun x _ => ?_
    · rw [mem_typeEvent, typeOf_comp_perm]; exact mem_typeEvent.1 hx
    · rw [mem_typeEvent, typeOf_comp_perm]; exact mem_typeEvent.1 hx
    · have h1 : iidPMF Q (n + 1) (x ∘ σ) = iidPMF Q (n + 1) x := by
        simp only [iidPMF, Function.comp_apply]
        exact Equiv.prod_comp σ fun j => Q (x j)
      have h2 : (x ∘ σ) 0 = x i := by simp [σ]
      rw [h1, h2]
  have hsum : ∑ x ∈ typeEvent E (n + 1), iidPMF Q (n + 1) x * typeOf x a =
      (∑ i : Fin (n + 1), ∑ x ∈ typeEvent E (n + 1),
        iidPMF Q (n + 1) x * (if x i = a then 1 else 0)) / (n + 1) := by
    rw [sum_comm, sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [← mul_sum, typeOf, symbolCount_eq_sum]
    push_cast
    ring_nf
  rw [hsum, sum_congr rfl fun i _ => hsym i, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ (by positivity), prob]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext x
  simp [mem_typeEvent, and_comm]

/-- **Theorem 11.6.2 (Conditional limit theorem).** Let `Q > 0`, let `E` be a convex set of
distributions and let `P*` minimize `D(P‖Q)` over `E`, with `D(P*‖Q)` approached by interior
points of `E`. For `X₁, X₂, …` i.i.d. `∼ Q`, `Pr(X₁ = a | P_{Xⁿ} ∈ E) → P*(a)`. -/
theorem tendsto_condProb_first_eq (hQ : IsPMF Q) (hQpos : ∀ a, 0 < Q a)
    (hEconv : Convex ℝ E) (hEpmf : ∀ P ∈ E, IsPMF P) (hPsE : Ps ∈ E)
    (hmin : ∀ P ∈ E, relEntropyReal Ps Q ≤ relEntropyReal P Q)
    (hint : ∀ ε > 0, ∃ P', IsPMF P' ∧ IsRelInteriorPt E P' ∧
      relEntropyReal P' Q < relEntropyReal Ps Q + ε) (a : α) :
    Tendsto (fun n => condProb (iidPMF Q (n + 1))
      (univ.filter fun x : Fin (n + 1) → α => x 0 = a) (typeEvent E (n + 1))) atTop
      (𝓝 (Ps a)) := by
  classical
  have hPs := hEpmf _ hPsE
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hbad := (tendsto_condProb_abs_typeOf_sub hQ hQpos hEconv hEpmf hPsE hmin hint a
    (half_pos hε)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨P', hP', hint', -⟩ := hint 1 one_pos
  have hposE := ((eventually_neg_sub_le_log_prob hQ hQpos hP' hint' one_pos).filter_mono
    (tendsto_add_atTop_nat 1)).mono fun n hn => hn.1
  obtain ⟨N, hN⟩ := ((hbad.eventually (gt_mem_nhds (half_pos hε))).and hposE).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hb, hpos⟩ := hN n hn
  simp only [Function.comp_apply] at hb hpos
  set μ := iidPMF Q (n + 1)
  set T := typeEvent E (n + 1)
  set B := univ.filter fun x : Fin (n + 1) → α => ε / 2 ≤ |typeOf x a - Ps a|
  have hμ : ∀ x, 0 ≤ μ x := iidPMF_nonneg hQ.nonneg
  rw [Real.dist_eq, condProb, prob_first_eq_inter, abs_sub_lt_iff]
  -- `|E[P_{Xⁿ}(a) | E] - P*(a)| ≤ ε/2 + Pr(B | E)`.
  have hkey : |∑ x ∈ T, μ x * typeOf x a - prob μ T * Ps a| ≤
      ε / 2 * prob μ T + prob μ (B ∩ T) := by
    have e : ∑ x ∈ T, μ x * typeOf x a - prob μ T * Ps a = ∑ x ∈ T, μ x * (typeOf x a - Ps a) := by
      rw [prob, sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsplit : prob μ (B ∩ T) = ∑ x ∈ T, if x ∈ B then μ x else 0 := by
      rw [prob, ← sum_filter]
      congr 1
      ext x
      simp [and_comm]
    rw [hsplit, prob, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun x _ => ?_
    have hP1 : |typeOf x a - Ps a| ≤ 1 := by
      rcases Nat.eq_zero_or_pos (n + 1) with h | h
      · omega
      · have h1 := (typeOf_isPMF h x).le_one a
        have h2 := hPs.le_one a
        have h3 := typeOf_nonneg x a
        have h4 := hPs.nonneg a
        rw [abs_le]
        constructor <;> linarith
    rw [abs_mul, abs_of_nonneg (hμ x)]
    split_ifs with hxB
    · nlinarith [hμ x, abs_nonneg (typeOf x a - Ps a)]
    · simp only [B, mem_filter, mem_univ, true_and, not_le] at hxB
      nlinarith [hμ x]
  have hratio : prob μ (B ∩ T) / prob μ T < ε / 2 := by
    simpa [condProb] using hb
  rw [div_lt_iff₀ hpos] at hratio
  constructor
  · rw [div_sub' hpos.ne', div_lt_iff₀ hpos]
    nlinarith [(abs_le.1 hkey).2]
  · rw [sub_div' hpos.ne', div_lt_iff₀ hpos]
    nlinarith [(abs_le.1 hkey).1]

end CondLimit

end InfoTheory
