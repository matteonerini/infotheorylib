/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MDCovering
public import InfoTheoryLib.Network.SourceHelperConverse
public import InfoTheoryLib.StateChannel.GPDerandomize

/-!
# The simple outer bound for multiple descriptions

If the rate pair `(R₁, R₂)` is in the rate–distortion region `R(D₀, D₁, D₂)` of Lecture 14 of
El Gamal and Kim, then, for some `p(x̂₀, x̂₁, x̂₂|x)` with `E dⱼ(X, X̂ⱼ) ≤ Dⱼ`, we have
`R₁ ≥ I(X; X̂₁)`, `R₂ ≥ I(X; X̂₂)` and `R₁ + R₂ ≥ I(X; X̂₀, X̂₁, X̂₂)`.

## Main definitions

* `mdOuterAt`: the outer bound holds at the rates and the distortions.

## Main statements

* `mutualInfo_mix_le`: the single-letter bound for one index.
* `MDCode.mdOuterAt_of_code`: the bound for one code.
* `isClosed_mdOuter`: the set of the rates and the distortions satisfying the bound is closed. This
  is why the distortions are exactly `Dⱼ`, and not `Dⱼ + ε`, in the limit.
* `mdRegion_subset_mdOuter`: **the simple outer bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 14
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₀ β₁ β₂ : Type*} [Fintype α] [Fintype β₀] [Fintype β₁] [Fintype β₂] {P : α → ℝ} {n : ℕ}

/-- **Lecture 14 of [elgamal2010], page 14-6.** The simple outer bound holds at `(R₁, R₂)` and
`(D₀, D₁, D₂)`: for some `p(x̂₀, x̂₁, x̂₂|x)` we have `E dⱼ(X, X̂ⱼ) ≤ Dⱼ` and, with the rates in
bits, `R₁ ≥ I(X; X̂₁)`, `R₂ ≥ I(X; X̂₂)` and `R₁ + R₂ ≥ I(X; X̂₀, X̂₁, X̂₂)`. -/
def mdOuterAt (P : α → ℝ) (d₀ : α → β₀ → ℝ) (d₁ : α → β₁ → ℝ) (d₂ : α → β₂ → ℝ)
    (R₁ R₂ D₀ D₁ D₂ : ℝ) : Prop :=
  ∃ κ : α → β₀ × β₁ × β₂ → ℝ, IsChannel κ ∧
    ∑ z, jointOf P κ z * d₀ z.1 z.2.1 ≤ D₀ ∧ ∑ z, jointOf P κ z * d₁ z.1 z.2.2.1 ≤ D₁ ∧
    ∑ z, jointOf P κ z * d₂ z.1 z.2.2.2 ≤ D₂ ∧
    I[Prod.fst : fun z : α × β₀ × β₁ × β₂ => z.2.2.1 ; jointOf P κ] ≤ R₁ * log 2 ∧
    I[Prod.fst : fun z : α × β₀ × β₁ × β₂ => z.2.2.2 ; jointOf P κ] ≤ R₂ * log 2 ∧
    I[Prod.fst : Prod.snd ; jointOf P κ] ≤ (R₁ + R₂) * log 2

/-! ### Uniform time sharing -/

section Mix

/-- Each coordinate of an i.i.d. sequence has the law `P`. -/
lemma dist_iidPMF_coord (hP : IsPMF P) (i : Fin n) (a : α) :
    dist (iidPMF P n) (fun ω => ω i) a = P a := by
  classical
  have h := sum_iidPMF_eval hP i fun x => if x = a then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  rw [← h, dist]

/-- The coordinate at a uniform time has the law `P`. -/
lemma dist_mix_coord (hP : IsPMF P) (hn : 0 < n) :
    dist (mixLaw (iidPMF P n) (Fin n)) (fun z => z.1 z.2) = P := by
  funext a
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [dist_mixLaw]
  simp only [dist_iidPMF_coord hP, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hn', one_mul]

/-- The average under the time sharing variable. -/
lemma sum_mix_mul (hn : 0 < n) (G : (Fin n → α) → Fin n → ℝ) :
    ∑ z, mixLaw (iidPMF P n) (Fin n) z * G z.1 z.2 =
      ∑ ω, iidPMF P n ω * ((∑ i, G ω i) / n) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  rw [sum_div, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [mixLaw, prodDist, uniformPMF, Fintype.card_fin]
  ring

/-- **Lecture 14, page 14-6.** The single-letter bound for an index `M` of `Xⁿ`: if `Yᵢ` is a
function of `M` at time `i`, then `I(X_Q; Y_Q) ≤ (1 / n) log |𝓜|`, for `Q` uniform and independent
of `Xⁿ`. -/
theorem mutualInfo_mix_le (hP : IsPMF P) (hn : 0 < n) {τ σ : Type*} [Fintype τ] [Fintype σ]
    (M : (Fin n → α) → τ) (Y : Fin n → τ → σ) :
    I[fun z : (Fin n → α) × Fin n => z.1 z.2 : fun z => Y z.2 (M z.1) ;
      mixLaw (iidPMF P n) (Fin n)] ≤ (n : ℝ)⁻¹ * log (Fintype.card τ) := by
  classical
  have hμ := iidPMF_isPMF hP n
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- The conditional entropy under time sharing.
  have h1 := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α) => ω i)
    (b := fun _ : Fin n => τ) fun _ => M
  simp only [Fintype.card_fin] at h1
  have h2 : H[fun z : (Fin n → α) × Fin n => z.1 z.2 |
      fun z => (⟨z.2, M z.1⟩ : Σ _ : Fin n, τ) ; mixLaw (iidPMF P n) (Fin n)] ≤
      H[fun z : (Fin n → α) × Fin n => z.1 z.2 | fun z => Y z.2 (M z.1) ;
        mixLaw (iidPMF P n) (Fin n)] :=
    condEntropy_le_condEntropy_comp hν _ _ fun s : Σ _ : Fin n, τ => Y s.1 s.2
  have h3 := condEntropy_pi_le_sum hμ (id : (Fin n → α) → Fin n → α) M
  -- The entropy of the source.
  have h4 : H[fun z : (Fin n → α) × Fin n => z.1 z.2 ; mixLaw (iidPMF P n) (Fin n)] =
    entropy P := by
    rw [entropyRV, dist_mix_coord hP hn]
  have h5 : H[id ; iidPMF P n] = n * entropy P := by
    rw [entropyRV, dist_id, entropy_iidPMF hP]
  have h6 : H[id ; iidPMF P n] - H[id | M ; iidPMF P n] ≤ log (Fintype.card τ) := by
    rw [← mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_comm hμ,
      mutualInfo_eq_entropy_sub_condEntropy hμ]
    have a1 := condEntropy_nonneg hμ M (id : (Fin n → α) → _)
    have a2 := entropyRV_le_log_card hμ M
    linarith
  rw [mutualInfo_eq_entropy_sub_condEntropy hν, h4]
  have hx : entropy P = (n : ℝ)⁻¹ * H[id ; iidPMF P n] := by
    rw [h5, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  have hy : (n : ℝ)⁻¹ * H[id | M ; iidPMF P n] ≤
      H[fun z : (Fin n → α) × Fin n => z.1 z.2 | fun z => Y z.2 (M z.1) ;
        mixLaw (iidPMF P n) (Fin n)] := by
    refine le_trans (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hn'.le)) (le_trans ?_ h2)
    rw [h1]
    exact le_of_eq rfl
  have hz := mul_le_mul_of_nonneg_left h6 (inv_nonneg.2 hn'.le)
  rw [mul_sub] at hz
  linarith

end Mix

/-! ### The bound for one code -/

section Code

variable {d₀ : α → β₀ → ℝ} {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ} {M₁ M₂ : ℕ}

/-- **Lecture 14, page 14-6.** The single-letter bound for one code. -/
theorem MDCode.mdOuterAt_of_code (hP : IsPMF P) (hn : 0 < n) (c : MDCode M₁ M₂ n α β₀ β₁ β₂)
    {R₁ R₂ : ℝ} (hM₁ : log M₁ ≤ n * (R₁ * log 2)) (hM₂ : log M₂ ≤ n * (R₂ * log 2))
    (hM₁0 : 0 < M₁) (hM₂0 : 0 < M₂) :
    mdOuterAt P d₀ d₁ d₂ R₁ R₂ (c.distortion₀ P d₀) (c.distortion₁ P d₁) (c.distortion₂ P d₂) := by
  classical
  obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  set ν := mixLaw (iidPMF P n) (Fin n) with hνd
  set W : (Fin n → α) × Fin n → α × β₀ × β₁ × β₂ := fun z =>
    (z.1 z.2, c.dec₀ (c.enc₁ z.1, c.enc₂ z.1) z.2, c.dec₁ (c.enc₁ z.1) z.2,
      c.dec₂ (c.enc₂ z.1) z.2) with hW
  have hr : IsPMF (dist ν W) := hν.dist W
  have hne : Nonempty (β₀ × β₁ × β₂) := by
    obtain ⟨z⟩ : Nonempty ((Fin n → α) × Fin n) := ⟨(fun _ => a₀, ⟨0, hn⟩)⟩
    exact ⟨(W z).2⟩
  obtain ⟨κ, hκ, hker⟩ := exists_kernel hr
  have hfst : dist (dist ν W) Prod.fst = P := by
    rw [← dist_comp_eq]
    exact dist_mix_coord hP hn
  have hL : jointOf P κ = dist ν W := by
    funext ⟨a, b⟩
    rw [hker a b, hfst]
    rfl
  have hinvm : ∀ {x y : ℝ}, x ≤ n * y → (n : ℝ)⁻¹ * x ≤ y := fun {x y} h => by
    rw [inv_mul_le_iff₀ hn']
    exact h
  have hcost : ∀ f : α × β₀ × β₁ × β₂ → ℝ, ∑ z, jointOf P κ z * f z =
      ∑ z, ν z * f (W z) := fun f => by
    rw [hL]
    exact sum_dist_mul ν W f
  refine ⟨κ, hκ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcost]
    exact le_of_eq (sum_mix_mul hn fun ω i => d₀ (ω i) (c.dec₀ (c.enc₁ ω, c.enc₂ ω) i))
  · rw [hcost]
    exact le_of_eq (sum_mix_mul hn fun ω i => d₁ (ω i) (c.dec₁ (c.enc₁ ω) i))
  · rw [hcost]
    exact le_of_eq (sum_mix_mul hn fun ω i => d₂ (ω i) (c.dec₂ (c.enc₂ ω) i))
  · rw [hL, ← mutualInfo_comp W]
    refine (mutualInfo_mix_le hP hn c.enc₁ fun i m => c.dec₁ m i).trans (hinvm ?_)
    rwa [Fintype.card_fin]
  · rw [hL, ← mutualInfo_comp W]
    refine (mutualInfo_mix_le hP hn c.enc₂ fun i m => c.dec₂ m i).trans (hinvm ?_)
    rwa [Fintype.card_fin]
  · rw [hL, ← mutualInfo_comp W]
    refine (mutualInfo_mix_le hP hn (fun ω => (c.enc₁ ω, c.enc₂ ω)) fun i m =>
      (c.dec₀ m i, c.dec₁ m.1 i, c.dec₂ m.2 i)).trans (hinvm ?_)
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul,
      log_mul (by exact_mod_cast hM₁0.ne') (by exact_mod_cast hM₂0.ne'), add_mul, mul_add]
    exact add_le_add hM₁ hM₂

end Code

/-! ### Closedness -/

section Closed

variable (P)

/-- The entropies are continuous in the channel. -/
lemma continuous_entropyRV_jointOf {β a : Type*} [Fintype β] [Fintype a] (A : α × β → a) :
    Continuous fun κ : α → β → ℝ => H[A ; jointOf P κ] := by
  classical
  simp only [entropyRV, entropy_eq_sum_negMulLog]
  refine continuous_finsetSum _ fun v _ => continuous_negMulLog.comp ?_
  simp only [dist]
  refine continuous_finsetSum _ fun z _ => ?_
  split_ifs
  · simp only [jointOf]
    fun_prop
  · exact continuous_const

/-- The expected costs are continuous in the channel. -/
lemma continuous_sum_jointOf {β : Type*} [Fintype β] (f : α × β → ℝ) :
    Continuous fun κ : α → β → ℝ => ∑ z, jointOf P κ z * f z := by
  refine continuous_finsetSum _ fun z _ => ?_
  simp only [jointOf]
  fun_prop

variable {P}

/-- A projection along a compact set maps a closed set to a closed set. -/
lemma isClosed_exists_mem_compact {A V : Type*} [TopologicalSpace A] [TopologicalSpace V]
    {K : Set A} (hK : IsCompact K) {T : Set (A × V)} (hT : IsClosed T) :
    IsClosed {t : V | ∃ κ ∈ K, (κ, t) ∈ T} := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hT' : IsClosed {p : K × V | ((p.1 : A), p.2) ∈ T} :=
    hT.preimage ((continuous_subtypeVal.comp continuous_fst).prodMk continuous_snd)
  have h := isClosedMap_snd_of_compactSpace _ hT'
  convert h using 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨κ, hκ, ht⟩
    exact ⟨(⟨κ, hκ⟩, t), ht, rfl⟩
  · rintro ⟨⟨κ, s⟩, ht, rfl⟩
    exact ⟨κ, κ.property, ht⟩

/-- The set of the rates and distortions satisfying the outer bound is closed. -/
theorem isClosed_mdOuter (hP : IsPMF P) (d₀ : α → β₀ → ℝ) (d₁ : α → β₁ → ℝ) (d₂ : α → β₂ → ℝ) :
    IsClosed {t : (ℝ × ℝ) × ℝ × ℝ × ℝ |
      mdOuterAt P d₀ d₁ d₂ t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2} := by
  set F₁ : (α → β₀ × β₁ × β₂ → ℝ) → ℝ := fun κ =>
    H[Prod.fst ; jointOf P κ] + H[fun z : α × β₀ × β₁ × β₂ => z.2.2.1 ; jointOf P κ] -
      H[pair Prod.fst (fun z : α × β₀ × β₁ × β₂ => z.2.2.1) ; jointOf P κ] with hF₁
  set F₂ : (α → β₀ × β₁ × β₂ → ℝ) → ℝ := fun κ =>
    H[Prod.fst ; jointOf P κ] + H[fun z : α × β₀ × β₁ × β₂ => z.2.2.2 ; jointOf P κ] -
      H[pair Prod.fst (fun z : α × β₀ × β₁ × β₂ => z.2.2.2) ; jointOf P κ] with hF₂
  set F₃ : (α → β₀ × β₁ × β₂ → ℝ) → ℝ := fun κ =>
    H[Prod.fst ; jointOf P κ] + H[Prod.snd ; jointOf P κ] -
      H[pair Prod.fst Prod.snd ; jointOf P κ] with hF₃
  have hc₁ : Continuous F₁ := ((continuous_entropyRV_jointOf P _).add
    (continuous_entropyRV_jointOf P _)).sub (continuous_entropyRV_jointOf P _)
  have hc₂ : Continuous F₂ := ((continuous_entropyRV_jointOf P _).add
    (continuous_entropyRV_jointOf P _)).sub (continuous_entropyRV_jointOf P _)
  have hc₃ : Continuous F₃ := ((continuous_entropyRV_jointOf P _).add
    (continuous_entropyRV_jointOf P _)).sub (continuous_entropyRV_jointOf P _)
  have hT : IsClosed {p : (α → β₀ × β₁ × β₂ → ℝ) × (ℝ × ℝ) × ℝ × ℝ × ℝ |
      ∑ z, jointOf P p.1 z * d₀ z.1 z.2.1 ≤ p.2.2.1 ∧
      ∑ z, jointOf P p.1 z * d₁ z.1 z.2.2.1 ≤ p.2.2.2.1 ∧
      ∑ z, jointOf P p.1 z * d₂ z.1 z.2.2.2 ≤ p.2.2.2.2 ∧
      F₁ p.1 ≤ p.2.1.1 * log 2 ∧ F₂ p.1 ≤ p.2.1.2 * log 2 ∧
      F₃ p.1 ≤ (p.2.1.1 + p.2.1.2) * log 2} := by
    have c0 := continuous_sum_jointOf (β := β₀ × β₁ × β₂) P fun z => d₀ z.1 z.2.1
    have c1 := continuous_sum_jointOf (β := β₀ × β₁ × β₂) P fun z => d₁ z.1 z.2.2.1
    have c2 := continuous_sum_jointOf (β := β₀ × β₁ × β₂) P fun z => d₂ z.1 z.2.2.2
    refine (isClosed_le (c0.comp continuous_fst) (by fun_prop)).inter
      ((isClosed_le (c1.comp continuous_fst) (by fun_prop)).inter
      ((isClosed_le (c2.comp continuous_fst) (by fun_prop)).inter
      ((isClosed_le (hc₁.comp continuous_fst) (by fun_prop)).inter
      ((isClosed_le (hc₂.comp continuous_fst) (by fun_prop)).inter
      (isClosed_le (hc₃.comp continuous_fst) (by fun_prop))))))
  have h := isClosed_exists_mem_compact (isCompact_setOf_isChannel (α := α)
    (β := β₀ × β₁ × β₂)) hT
  convert h using 1
  ext t
  simp only [Set.mem_ofPred_eq, mdOuterAt]
  refine exists_congr fun κ => ?_
  constructor
  · rintro ⟨hκ, a0, a1, a2, a3, a4, a5⟩
    have hμ := jointOf_isPMF hP hκ
    rw [mutualInfo_eq_add_sub hμ] at a3 a4 a5
    exact ⟨hκ, a0, a1, a2, a3, a4, a5⟩
  · rintro ⟨hκ, a0, a1, a2, a3, a4, a5⟩
    have hκ' : IsChannel κ := hκ
    have hμ := jointOf_isPMF hP hκ'
    refine ⟨hκ', a0, a1, a2, ?_, ?_, ?_⟩
    · rwa [mutualInfo_eq_add_sub hμ]
    · rwa [mutualInfo_eq_add_sub hμ]
    · rwa [mutualInfo_eq_add_sub hμ]

end Closed

/-! ### The outer bound -/

section Outer

variable {d₀ : α → β₀ → ℝ} {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ}

/-- An achievable rate pair satisfies the outer bound. -/
theorem IsAchievableMD.mdOuter (hP : IsPMF P) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : IsAchievableMD P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂) :
    mdOuterAt P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  obtain ⟨hR₁, hR₂, c, hc⟩ := h
  have hclosed := isClosed_mdOuter hP d₀ d₁ d₂
  -- The outer bound at `Dⱼ + ε`.
  have hε : ∀ ε > 0, mdOuterAt P d₀ d₁ d₂ R₁ R₂ (D₀ + ε) (D₁ + ε) (D₂ + ε) := fun ε hε => by
    obtain ⟨n, ⟨h0, h1, h2⟩, hn⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
    obtain ⟨κ, hκ, a0, a1, a2, a3⟩ := (c n).mdOuterAt_of_code (d₀ := d₀) (d₁ := d₁) (d₂ := d₂) hP hn
      (R₁ := R₁) (R₂ := R₂) (log_two_pow_floor_le n hR₁) (log_two_pow_floor_le n hR₂)
      (by positivity) (by positivity)
    exact ⟨κ, hκ, a0.trans h0, a1.trans h1, a2.trans h2, a3⟩
  -- The limit.
  have hlim : Tendsto (fun k : ℕ => (((R₁, R₂), D₀ + 1 / ((k : ℝ) + 1), D₁ + 1 / ((k : ℝ) + 1),
      D₂ + 1 / ((k : ℝ) + 1)) : (ℝ × ℝ) × ℝ × ℝ × ℝ)) atTop (𝓝 ((R₁, R₂), D₀, D₁, D₂)) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hj : ∀ D : ℝ, Tendsto (fun k : ℕ => D + 1 / ((k : ℝ) + 1)) atTop (𝓝 D) := fun D => by
      simpa using tendsto_const_nhds.add h0
    exact tendsto_const_nhds.prodMk_nhds ((hj D₀).prodMk_nhds ((hj D₁).prodMk_nhds (hj D₂)))
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun k => hε _ (by positivity))

/-- **Lecture 14 of [elgamal2010], page 14-6: the simple outer bound.** A rate pair of the
rate–distortion region `R(D₀, D₁, D₂)` satisfies the outer bound. -/
theorem mdRegion_subset_mdOuter (hP : IsPMF P) {D₀ D₁ D₂ : ℝ} {R : ℝ × ℝ}
    (h : R ∈ mdRegion P d₀ d₁ d₂ D₀ D₁ D₂) : mdOuterAt P d₀ d₁ d₂ R.1 R.2 D₀ D₁ D₂ := by
  have hclosed := isClosed_mdOuter hP d₀ d₁ d₂
  have hslice : IsClosed {R : ℝ × ℝ | mdOuterAt P d₀ d₁ d₂ R.1 R.2 D₀ D₁ D₂} :=
    hclosed.preimage (f := fun R : ℝ × ℝ => (R, D₀, D₁, D₂)) (by fun_prop)
  exact closure_minimal (fun R' hR' => IsAchievableMD.mdOuter hP hR') hslice h

end Outer

end InfoTheory
