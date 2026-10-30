/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MarkovChain.DataProcessing
public import InfoTheoryLib.MarkovChain.Process
public import InfoTheoryLib.RelativeEntropy.Conditional
public import InfoTheoryLib.Entropy.Bounds

/-!
# The second law of thermodynamics for Markov chains

## Main statements

* `relEntropy_step_le`, `relEntropy_iterate_antitone`: the relative entropy between two
  distributions evolving under the same Markov chain decreases with time.
* `relEntropy_stationary_antitone`, `relEntropy_stationary_tendsto`: `D(μₙ ‖ π)` decreases to a
  limit for any stationary distribution `π`.
* `entropy_iterate_monotone`: if the uniform distribution is stationary, the entropy increases.
* `condEntropy_stationary_monotone`: for a stationary process, `H(Xₙ | X₀)` increases with `n`.
* `condEntropy_initial_monotone`: for any Markov chain, `H(X₀ | Xₙ)` increases with `n`.
* `entropy_shuffle`: shuffles increase entropy, `H(TX) ≥ H(X)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 4.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- **Second law, interpretation 1 (4.45).** Relative entropy `D(μₙ‖μ'ₙ)` decreases with `n`:
for two initial distributions evolving under the same Markov chain,
`D(μₙ₊₁‖μ'ₙ₊₁) ≤ D(μₙ‖μ'ₙ)`. -/
theorem relEntropy_step_le {r : α → α → ℝ} (hr : IsStochastic r) {p q : α → ℝ} (hp : IsPMF p)
    (hq : IsPMF q) (hpq : AbsCont p q) :
    relEntropyReal (step r p) (step r q) ≤ relEntropyReal p q := by
  set P := jointOf p r
  set Q := jointOf q r
  have hP := jointOf_isPMF hp hr
  have hQ := jointOf_isPMF hq hr
  have hPQ : AbsCont P Q := absCont_jointOf hpq
  -- First expansion: `D(P‖Q) = D(p‖q) + D(p(x'|x) ‖ q(x'|x)) = D(p‖q)`.
  have h1 := chain_rule_relEntropy hP.nonneg hQ.nonneg hPQ
  have hcond : condRelEntropy P Q = 0 := by
    rw [condRelEntropy_eq_zero_iff hP hQ hPQ]
    intro x hx y
    rw [marg_jointOf hr] at hx
    have hqx : q x ≠ 0 := fun h => hx.ne' (hpq x h)
    simp only [condPMF, marg_jointOf hr, jointOf]
    field_simp
  rw [hcond, add_zero, marg_jointOf hr, marg_jointOf hr] at h1
  -- Second expansion, conditioning on the future: `D(P‖Q) ≥ D(pₙ₊₁‖qₙ₊₁)`.
  have hP' : IsPMF (P ∘ Prod.swap) :=
    ⟨fun z => hP.nonneg _, by
      change ∑ x, P (Prod.swap x) = 1
      rw [← hP.sum_eq_one]; exact (Equiv.prodComm α α).sum_comp P⟩
  have hQ' : IsPMF (Q ∘ Prod.swap) :=
    ⟨fun z => hQ.nonneg _, by
      change ∑ x, Q (Prod.swap x) = 1
      rw [← hQ.sum_eq_one]; exact (Equiv.prodComm α α).sum_comp Q⟩
  have hPQ' : AbsCont (P ∘ Prod.swap) (Q ∘ Prod.swap) := fun z h => hPQ _ h
  have h2 := chain_rule_relEntropy hP'.nonneg hQ'.nonneg hPQ'
  have h3 := condRelEntropy_nonneg hP' hQ' hPQ'
  have h4 : relEntropyReal (P ∘ Prod.swap) (Q ∘ Prod.swap) = relEntropyReal P Q :=
    relEntropyReal_comp_equiv (Equiv.prodComm α α) P Q
  rw [h4, marg_jointOf_swap, marg_jointOf_swap] at h2
  unfold step
  linarith

/-- **Second law, interpretation 1.** `n ↦ D(μₙ‖μ'ₙ)` is non-increasing: "the distance between
the probability mass functions is decreasing with time `n` for any Markov chain". -/
theorem relEntropy_iterate_antitone {r : α → α → ℝ} (hr : IsStochastic r) {p q : α → ℝ}
    (hp : IsPMF p) (hq : IsPMF q) (hpq : AbsCont p q) :
    Antitone (fun n => relEntropyReal ((step r)^[n] p) ((step r)^[n] q)) := by
  refine antitone_nat_of_succ_le fun n => ?_
  simp only [Function.iterate_succ_apply']
  exact relEntropy_step_le hr (iterate_step_isPMF hr hp n) (iterate_step_isPMF hr hq n)
    (iterate_absCont hr hq hpq n)

/-- **Second law, interpretation 2 (4.46).** The relative entropy `D(μₙ‖ν)` between the
distribution at time `n` and a stationary distribution `ν` decreases with `n`. -/
theorem relEntropy_stationary_antitone {r : α → α → ℝ} (hr : IsStochastic r) {μ ν : α → ℝ}
    (hμ : IsPMF μ) (hν : IsPMF ν) (hstat : IsStationaryDist r ν) (hμν : AbsCont μ ν) :
    Antitone (fun n => relEntropyReal ((step r)^[n] μ) ν) := by
  have := relEntropy_iterate_antitone hr hμ hν hμν
  simpa only [hstat.iterate] using this

/-- **Second law, interpretation 2.** `D(μₙ‖ν)` is a monotonically non-increasing non-negative
sequence and therefore has a limit. -/
theorem relEntropy_stationary_tendsto {r : α → α → ℝ} (hr : IsStochastic r) {μ ν : α → ℝ}
    (hμ : IsPMF μ) (hν : IsPMF ν) (hstat : IsStationaryDist r ν) (hμν : AbsCont μ ν) :
    ∃ L, 0 ≤ L ∧ Tendsto (fun n => relEntropyReal ((step r)^[n] μ) ν) atTop (𝓝 L) := by
  have hanti := relEntropy_stationary_antitone hr hμ hν hstat hμν
  have hnn : ∀ n, 0 ≤ relEntropyReal ((step r)^[n] μ) ν := fun n => by
    have := relEntropyReal_nonneg (iterate_step_isPMF hr hμ n) hν
      (by simpa only [hstat.iterate] using iterate_absCont hr hν hμν n)
    exact this
  refine ⟨⨅ n, relEntropyReal ((step r)^[n] μ) ν, le_ciInf hnn,
    tendsto_atTop_ciInf hanti ⟨0, ?_⟩⟩
  rintro _ ⟨n, rfl⟩; exact hnn n

/-- **Second law, interpretation 3 (4.47).** If the stationary distribution is uniform, the
entropy `H(μₙ)` increases with `n`, since `D(μₙ‖u) = log |𝒳| - H(μₙ)` decreases. -/
theorem entropy_iterate_monotone {r : α → α → ℝ} (hr : IsStochastic r) {μ : α → ℝ}
    (hμ : IsPMF μ) (hu : IsStationaryDist r (uniformPMF α)) :
    Monotone (fun n => entropy ((step r)^[n] μ)) := by
  have : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)
  have habs : AbsCont μ (uniformPMF α) :=
    fun x hx => absurd hx (by simp [uniformPMF, Fintype.card_ne_zero])
  have hanti := relEntropy_stationary_antitone hr hμ uniformPMF_isPMF hu habs
  intro m n hmn
  have := hanti hmn
  simp only [relEntropyReal_uniform (iterate_step_isPMF hr hμ _)] at this
  linarith

/-- If the Markov process is stationary, the entropy `H(Xₙ)` is constant. -/
lemma entropy_stationary_const {r : α → α → ℝ} {ν : α → ℝ} (hstat : IsStationaryDist r ν) (n : ℕ) :
    entropy ((step r)^[n] ν) = entropy ν := by
  rw [hstat.iterate]

section ThreeStep

variable (ν : α → ℝ) (r : α → α → ℝ) (n : ℕ)

/-- The law of `(X₀, X₁, Xₙ₊₁)` of the Markov chain started from `ν`. -/
private def law3 : α × α × α → ℝ :=
  fun t => ν t.1 * r t.1 t.2.1 * transPow r n t.2.1 t.2.2

private lemma law3_isPMF {ν : α → ℝ} {r : α → α → ℝ} (hν : IsPMF ν) (hr : IsStochastic r) :
    IsPMF (law3 ν r n) := by
  refine ⟨fun t => mul_nonneg (mul_nonneg (hν.nonneg _) ((hr _).nonneg _))
    ((transPow_isStochastic hr n _).nonneg _), ?_⟩
  simp only [law3, Fintype.sum_prod_type, ← mul_sum, (transPow_isStochastic hr n _).sum_eq_one,
    mul_one, (hr _).sum_eq_one, hν.sum_eq_one]

private def X0 : α × α × α → α := fun t => t.1

private def X1 : α × α × α → α := fun t => t.2.1

private def X2 : α × α × α → α := fun t => t.2.2

/-- Marginalizing the middle coordinate. -/
private lemma dist_X0X2 (μ : α × α × α → ℝ) (x z : α) :
    dist μ (pair X0 X2) (x, z) = ∑ y, μ (x, y, z) := by
  rw [← sum_dist_pair_right μ (pair X0 X2) X1 (x, z)]
  refine sum_congr rfl fun y _ => ?_
  have := dist_eq_of_injective μ (U := id) (V := pair (pair X0 X2) X1)
    (fun t : α × α × α => ((t.1, t.2.2), t.2.1))
    (fun a b h => by
      obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
      simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl) (x, y, z)
  rw [dist_id] at this
  exact this

private lemma dist_X1X2 (μ : α × α × α → ℝ) (y z : α) :
    dist μ (pair X1 X2) (y, z) = ∑ x, μ (x, y, z) := by
  rw [← sum_dist_pair_left μ X0 (pair X1 X2) (y, z)]
  refine sum_congr rfl fun x _ => ?_
  have := dist_id μ
  exact congrFun this (x, y, z)

private lemma dist_X0X1 (μ : α × α × α → ℝ) (x y : α) :
    dist μ (pair X0 X1) (x, y) = ∑ z, μ (x, y, z) := by
  rw [← sum_dist_pair_right μ (pair X0 X1) X2 (x, y)]
  refine sum_congr rfl fun z _ => ?_
  have := dist_eq_of_injective μ (U := id) (V := pair (pair X0 X1) X2)
    (fun t : α × α × α => ((t.1, t.2.1), t.2.2))
    (fun a b h => by
      obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
      simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl) (x, y, z)
  rw [dist_id] at this
  exact this

private lemma dist_X1 (μ : α × α × α → ℝ) (y : α) :
    dist μ X1 y = ∑ x, ∑ z, μ (x, y, z) := by
  rw [← sum_dist_pair_left μ X0 X1 y]
  exact sum_congr rfl fun x _ => dist_X0X1 μ x y

end ThreeStep

/-- **Second law, interpretation 4 (4.50)–(4.52).** For a stationary Markov process, the
conditional entropy `H(Xₙ | X₀)` increases with `n`: the conditional uncertainty of the future
increases. Here `(X₀, Xₙ)` has joint law `ν(x) rⁿ(x'|x)`. -/
theorem condEntropy_stationary_monotone {r : α → α → ℝ} (hr : IsStochastic r) {ν : α → ℝ}
    (hν : IsPMF ν) (hstat : IsStationaryDist r ν) :
    Monotone (fun n => H[Prod.snd | Prod.fst ; jointOf ν (transPow r n)]) := by
  refine monotone_nat_of_le_succ fun n => ?_
  set μ := law3 ν r n
  have hμ : IsPMF μ := law3_isPMF n hν hr
  have hT := transPow_isStochastic hr n
  have hstat' : ∀ y, ∑ x, ν x * r x y = ν y := fun y => congrFun hstat y
  -- `(X₀, Xₙ₊₁)` has law `ν(x) rⁿ⁺¹(x'|x)` and `(X₁, Xₙ₊₁)` has law `ν(x) rⁿ(x'|x)`.
  have h02 : dist μ (pair X0 X2) =
      dist (jointOf ν (transPow r (n + 1))) (pair Prod.fst Prod.snd) := by
    rw [dist_pair_fst_snd]; funext ⟨x, z⟩
    rw [dist_X0X2]
    simp only [μ, law3, jointOf, transPow, mul_sum, mul_assoc]
  have h12 : dist μ (pair X1 X2) = dist (jointOf ν (transPow r n)) (pair Prod.fst Prod.snd) := by
    rw [dist_pair_fst_snd]; funext ⟨y, z⟩
    rw [dist_X1X2]
    simp only [μ, law3, jointOf, ← sum_mul, hstat']
  -- The Markov property `X₀ → X₁ → Xₙ₊₁`.
  have hmarkov : MarkovChain μ X0 X1 X2 := by
    rw [markovChain_iff_mul hμ]
    intro x y z
    have e3 : dist μ (pair X0 (pair X1 X2)) (x, y, z) = μ (x, y, z) := congrFun (dist_id μ) _
    rw [e3, dist_X1, dist_X0X1, dist_X1X2]
    simp only [μ, law3, ← mul_sum, (hT _).sum_eq_one, mul_one, ← sum_mul, hstat']
    ring
  have hci : I[X2 : X0 | X1 ; μ] = 0 := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq_zero_iff hμ]
    exact (markovChain_iff_condIndep hμ _ _ _).1 hmarkov
  have hswap : H[X2 | pair X0 X1 ; μ] = H[X2 | pair X1 X0 ; μ] :=
    condEntropy_congr_right hμ X2 Prod.swap Prod.swap_injective (fun _ => rfl)
  have hle := condEntropy_le_condEntropy hμ X2 X1 X0
  rw [condMutualInfo, hswap] at hci
  change H[Prod.snd | Prod.fst ; jointOf ν (transPow r n)] ≤
    H[Prod.snd | Prod.fst ; jointOf ν (transPow r (n + 1))]
  rw [← condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hν (transPow_isStochastic hr _)) h12,
    ← condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hν (transPow_isStochastic hr _)) h02]
  linarith

/-- The law `μ(x) rⁿ(y|x) r(z|y)` of `(X₀, Xₙ, Xₙ₊₁)` for the Markov chain started from `μ`. -/
private def lawLast (μ : α → ℝ) (r : α → α → ℝ) (n : ℕ) : α × α × α → ℝ :=
  fun t => μ t.1 * transPow r n t.1 t.2.1 * r t.2.1 t.2.2

private lemma lawLast_isPMF {μ : α → ℝ} {r : α → α → ℝ} (hμ : IsPMF μ) (hr : IsStochastic r)
    (n : ℕ) : IsPMF (lawLast μ r n) := by
  refine ⟨fun t => mul_nonneg (mul_nonneg (hμ.nonneg _) ((transPow_isStochastic hr n _).nonneg _))
    ((hr _).nonneg _), ?_⟩
  simp only [lawLast, Fintype.sum_prod_type, ← mul_sum, (hr _).sum_eq_one, mul_one,
    (transPow_isStochastic hr n _).sum_eq_one, hμ.sum_eq_one]

/-- **Second law, Section 4.4.** For any Markov chain, stationary or not, the conditional entropy
`H(X₀ | Xₙ)` of the initial state given the state at time `n` increases with `n`, by the
data-processing inequality for `X₀ → Xₙ → Xₙ₊₁`. Here `(X₀, Xₙ)` has joint law `μ(x) rⁿ(x'|x)`. -/
theorem condEntropy_initial_monotone {r : α → α → ℝ} (hr : IsStochastic r) {μ : α → ℝ}
    (hμ : IsPMF μ) : Monotone (fun n => H[Prod.fst | Prod.snd ; jointOf μ (transPow r n)]) := by
  refine monotone_nat_of_le_succ fun n => ?_
  set ν := lawLast μ r n
  have hν : IsPMF ν := lawLast_isPMF hμ hr n
  -- `(X₀, Xₙ)` has law `μ(x) rⁿ(y|x)` and `(X₀, Xₙ₊₁)` has law `μ(x) rⁿ⁺¹(z|x)`.
  have h01 : dist ν (pair X1 X0) = dist (jointOf μ (transPow r n)) (pair Prod.snd Prod.fst) := by
    funext ⟨y, x⟩
    rw [dist_pair_swap, dist_pair_snd_fst, dist_X0X1]
    simp only [ν, lawLast, jointOf, ← mul_sum, (hr _).sum_eq_one, mul_one]
  have h02 : dist ν (pair X2 X0) =
      dist (jointOf μ (transPow r (n + 1))) (pair Prod.snd Prod.fst) := by
    funext ⟨z, x⟩
    rw [dist_pair_swap, dist_pair_snd_fst, dist_X0X2]
    simp only [ν, lawLast, jointOf, transPow_succ', mul_sum, mul_assoc]
  -- The Markov property `X₀ → Xₙ → Xₙ₊₁`.
  have hmarkov : MarkovChain ν X0 X1 X2 := by
    rw [markovChain_iff_mul hν]
    intro x y z
    have e3 : dist ν (pair X0 (pair X1 X2)) (x, y, z) = ν (x, y, z) := congrFun (dist_id ν) _
    rw [e3, dist_X1, dist_X0X1, dist_X1X2]
    simp only [ν, lawLast, ← mul_sum, (hr _).sum_eq_one, mul_one, ← sum_mul]
    ring
  have hdp := data_processing hν hmarkov
  rw [mutualInfo_eq_entropy_sub_condEntropy hν, mutualInfo_eq_entropy_sub_condEntropy hν] at hdp
  change H[Prod.fst | Prod.snd ; jointOf μ (transPow r n)] ≤
    H[Prod.fst | Prod.snd ; jointOf μ (transPow r (n + 1))]
  rw [← condEntropy_eq_of_dist_pair_eq hν (jointOf_isPMF hμ (transPow_isStochastic hr _)) h01,
    ← condEntropy_eq_of_dist_pair_eq hν (jointOf_isPMF hμ (transPow_isStochastic hr _)) h02]
  linarith

/-- **Second law, interpretation 5 (4.56): shuffles increase entropy.** If `T` is a random
shuffle independent of the initial arrangement `X`, then `H(TX) ≥ H(X)`. We state it for any
finite group. A deck of `n` cards is the case `G = Equiv.Perm (Fin n)`. -/
theorem entropy_shuffle {G : Type*} [Group G] [Fintype G] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (T X : Ω → G) (hind : IndepRV μ X T) : H[X ; μ] ≤ H[fun ω => T ω * X ω ; μ] := by
  have h1 := condEntropy_le_entropy hμ (fun ω => T ω * X ω) T
  have h2 : H[(fun ω => T ω * X ω) | T ; μ] = H[X | T ; μ] := by
    rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
    congr 1
    exact entropyRV_eq_of_injective μ (fun z : G × G => (z.1, z.1 * z.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (by simpa [h.1] using h.2)) (fun _ => rfl)
  have h3 : H[X | T ; μ] = H[X ; μ] := (condEntropy_eq_entropy_iff hμ X T).2 hind
  linarith

/-- **Shuffles increase entropy** for a deck of `n` cards. -/
theorem entropy_shuffle_deck {n : ℕ} {μ : Ω → ℝ} (hμ : IsPMF μ) (T X : Ω → Equiv.Perm (Fin n))
    (hind : IndepRV μ X T) : H[X ; μ] ≤ H[fun ω => T ω * X ω ; μ] :=
  entropy_shuffle hμ T X hind

end InfoTheory
