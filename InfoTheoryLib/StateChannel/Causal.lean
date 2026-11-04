/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.StateChannel.Basic

/-!
# Causal state information at the encoder

This file proves Theorem 3 of Lecture 7, due to Shannon: with the state available causally at the
encoder only, the capacity is `max_{p(u), x(u, s)} I(U; Y)`, with `U` independent of `S`.

We code over the *strategies*, the functions `f : σ → α`: the memoryless channel from `F` to `Y` is
`strategyChannel W p id`, and every `p(u)` and `x(u, s)` are obtained from a law on the strategies
by processing the input.

## Main definitions

* `causalValue W p`: `max_{p(u), x(u, s)} I(U; Y)`, with `U` on `Fin k`.

## Main statements

* `isAchievableStateRate_causal_false_of_lt`: achievability.
* `StateCode.one_sub_errProb_mul_log_le_strategy`: the converse.
* `stateCapacity_causal_false`: **Theorem 3 of Lecture 7**.
* `causalValue_eq_capacity`: the maximum is the capacity of the channel from the strategies.

## Implementation notes

The notes take `Uᵢ = (M, Sⁱ⁻¹)` and bound `I(Uᵢ; Yᵢ)`. We use the strategy `Fᵢ = xᵢ(M, Sⁱ⁻¹, ·)`, a
function of `Uᵢ`, and the law `fbLaw` of the message and the outputs `(Sᵢ, Yᵢ)` of the channel with
input `Fᵢ`: the strategies are a kind of feedback encoder, which uses the past states.

The cardinality bound `|𝒰| ≤ min {(|𝒳| - 1)|𝒮| + 1, |𝒴|}` is not formalized: `U` takes values in
`Fin k` for some `k`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {σ α β : Type*} [Fintype σ] [Fintype α] [Fintype β] {W : α × σ → β → ℝ} {p : σ → ℝ}

/-- **Lecture 7 of [elgamal2010], Theorem 3.** `max_{p(u), x(u, s)} I(U; Y)`, with `U` independent
of `S`, on `Fin k` for some `k`. -/
def causalValue (W : α × σ → β → ℝ) (p : σ → ℝ) : ℝ :=
  sSup {v | ∃ (k : ℕ) (q : Fin k → ℝ) (e : Fin k → σ → α), IsPMF q ∧
    mutualInfoOf q (strategyChannel W p e) = v}

omit [Fintype α] [Fintype β] in
/-- `strategyChannel W p e` is the channel from the strategies, after processing the input by
`e`. -/
lemma strategyChannel_eq_comp {𝒰 : Type*} (W : α × σ → β → ℝ) (p : σ → ℝ) (e : 𝒰 → σ → α) :
    strategyChannel W p e = (strategyChannel W p fun f => f) ∘ e := rfl

variable [DecidableEq σ]

/-- **Lecture 7 of [elgamal2010], page 7-24.** The maximum over `p(u)` and `x(u, s)` is the capacity
of the channel from the strategies: we can view the encoding as done over `𝒳^𝒮`. -/
theorem causalValue_eq_capacity [Nonempty α] (hW : IsChannel W) (hp : IsPMF p) :
    causalValue W p = capacity (strategyChannel W p fun f : σ → α => f) := by
  have hV := strategyChannel_isChannel hW hp fun f : σ → α => f
  have hle : ∀ v ∈ {v | ∃ (k : ℕ) (q : Fin k → ℝ) (e : Fin k → σ → α), IsPMF q ∧
      mutualInfoOf q (strategyChannel W p e) = v},
      v ≤ capacity (strategyChannel W p fun f : σ → α => f) := by
    rintro _ ⟨k, q, e, hq, rfl⟩
    rw [strategyChannel_eq_comp]
    exact mutualInfoOf_comp_le_capacity hq hV e
  obtain ⟨q, hq, hqC⟩ := exists_capacity_eq hV
  set E := Fintype.equivFin (σ → α)
  have hq' : IsPMF (q ∘ E.symm) := ⟨fun i => hq.nonneg _, by
    rw [← hq.sum_eq_one]
    exact E.symm.sum_comp q⟩
  have hdist : dist (q ∘ E.symm) (fun i => E.symm i) = q := by
    classical
    funext f
    simp only [dist, Function.comp]
    rw [E.symm.sum_comp fun f' => if f' = f then q f' else 0]
    simp
  refine le_antisymm (csSup_le ?_ hle) ?_
  · exact ⟨_, Fintype.card (σ → α), q ∘ E.symm, fun i => E.symm i, hq', rfl⟩
  · refine le_csSup ⟨_, hle⟩ ⟨Fintype.card (σ → α), q ∘ E.symm, fun i => E.symm i, hq', ?_⟩
    rw [strategyChannel_eq_comp, mutualInfoOf_comp hq' hV, hdist, hqC]

/-- **Achievability of Theorem 3 (Lecture 7 of [elgamal2010]).** Attach the device `x = f(s)` in
front of the channel, and use a code for the channel from the strategies. -/
theorem isAchievableStateRate_causal_false_of_lt [Nonempty α] (hW : IsChannel W) (hp : IsPMF p)
    {R : ℝ} (hR : R < capacity (strategyChannel W p fun f : σ → α => f) / log 2) :
    IsAchievableStateRate W p .causal false R := by
  obtain ⟨c, hlim⟩ := isAchievableRateAvg_of_lt (strategyChannel_isChannel hW hp _) hR
  refine ⟨fun n => (c n).toStateCode fun f => f, fun n => ⟨?_, fun _ _ _ _ => rfl⟩,
    hlim.congr fun n => ?_⟩
  · intro m s s' i h
    change ((c n).enc m i) (s i) = ((c n).enc m i) (s' i)
    rw [h i le_rfl]
  · rw [ChannelCode.errProb_toStateCode]

/-! ### The converse -/

section Converse

omit [DecidableEq σ]

variable {𝒲 : Type*} [Fintype 𝒲] {ν : 𝒲 → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β × σ) → σ → α}

/-- The outputs `Yᵏ`, from the message and the outputs `(Yᵏ, Sᵏ)` of the channel from the
strategies. -/
abbrev causalY (𝒲 : Type*) {β σ : Type*} (k : ℕ) : 𝒲 × (Fin k → β × σ) → Fin k → β :=
  fun z i => (z.2 i).1

variable [DecidableEq σ] in
/-- **Lecture 7 of [elgamal2010], pages 7-24 and 7-25.** With `Fₖ = xₖ(M, Sᵏ⁻¹, ·)`,
`I(M; Yₖ | Yᵏ⁻¹) ≤ H(Yₖ) - H(Yₖ | M, Sᵏ⁻¹, Yᵏ⁻¹) ≤ C`: given the past, `Yₖ` is the output of the
channel from the strategies for the input `Fₖ`. -/
theorem mutualInfo_causalLaw_succ_le (hW : IsChannel W) (hp : IsPMF p) (hν : IsPMF ν)
    (k : ℕ) :
    I[Prod.fst : causalY 𝒲 (k + 1) ; fbLaw ν (strategyOutChannel W p fun f => f) enc (k + 1)] ≤
      I[Prod.fst : causalY 𝒲 k ; fbLaw ν (strategyOutChannel W p fun f => f) enc k] +
        capacity (strategyChannel W p fun f : σ → α => f) := by
  classical
  have hV := strategyOutChannel_isChannel hW hp fun f : σ → α => f
  have hVb := strategyChannel_isChannel hW hp fun f : σ → α => f
  set μ := fbLaw ν (strategyOutChannel W p fun f => f) enc (k + 1)
  have hμ : IsPMF μ := fbLaw_isPMF hν hV (k + 1)
  set Zp : 𝒲 × (Fin (k + 1) → β × σ) → (Fin k → β × σ) := fun z => Fin.init z.2
  set Yp : 𝒲 × (Fin (k + 1) → β × σ) → (Fin k → β) := fun z i => (Fin.init z.2 i).1
  set Yl : 𝒲 × (Fin (k + 1) → β × σ) → β := fun z => (z.2 (Fin.last k)).1
  set Sl : 𝒲 × (Fin (k + 1) → β × σ) → σ := fun z => (z.2 (Fin.last k)).2
  set Wv : 𝒲 × (Fin (k + 1) → β × σ) → 𝒲 := Prod.fst
  have h1 : I[Wv : causalY 𝒲 (k + 1) ; μ] = I[Wv : pair Yl Yp ; μ] :=
    mutualInfo_congr_right hμ Wv (fun v : β × (Fin k → β) => (Fin.snoc v.2 v.1 : Fin (k + 1) → β))
      (fun a b hab => by
        have := snoc_injective2 (α := β) k (a₁ := (a.2, a.1)) (a₂ := (b.2, b.1)) hab
        simp only [Prod.mk.injEq] at this
        exact Prod.ext this.2 this.1)
      fun z => by
        funext i
        induction i using Fin.lastCases with
        | last => simp [Yl, pair]
        | cast i => simp [Yp, pair, Fin.init]
  have h2 := chain_rule_mutualInfo₂ hμ Wv Yl Yp
  have h3 : I[Wv : Yp ; μ] =
      I[Prod.fst : causalY 𝒲 k ; fbLaw ν (strategyOutChannel W p fun f => f) enc k] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    have e : pair Wv Yp = (fun z : 𝒲 × (Fin k → β × σ) => (z.1, fun i => (z.2 i).1)) ∘
        fun z : 𝒲 × (Fin (k + 1) → β × σ) => (z.1, Fin.init z.2) := rfl
    rw [e, dist_comp_eq, dist_fbLaw_init hV k]
    rfl
  have h4 : I[Wv : Yl | Yp ; μ] ≤ H[Yl ; μ] - H[Yl | pair Yp Wv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    linarith [condEntropy_le_entropy hμ Yl Yp]
  have h4' : H[Yl | pair Zp Wv ; μ] ≤ H[Yl | pair Yp Wv ; μ] :=
    condEntropy_le_condEntropy_comp hμ Yl (pair Zp Wv)
      fun z : (Fin k → β × σ) × 𝒲 => ((fun i => (z.1 i).1 : Fin k → β), z.2)
  have hchan : ∀ (z : (Fin k → β × σ) × 𝒲) (b : β), dist μ (pair (pair Zp Wv) Yl) (z, b) =
      dist μ (pair Zp Wv) z * strategyChannel W p (fun f : σ → α => f) (enc k z.2 z.1) b := by
    rintro ⟨u, w⟩ b
    have hT : Function.Injective (pair (pair (pair Zp Wv) Yl) Sl) := fun a c hac => by
      simp only [pair, Prod.mk.injEq, Zp, Yl, Sl, Wv] at hac
      refine Prod.ext hac.1.1.2 ?_
      rw [← Fin.snoc_init_self a.2, ← Fin.snoc_init_self c.2, hac.1.1.1,
        Prod.ext hac.1.2 hac.2]
    have e1 : ∀ s, dist μ (pair (pair (pair Zp Wv) Yl) Sl) (((u, w), b), s) =
        μ (w, Fin.snoc u (b, s)) := fun s => by
      have := dist_comp_of_injective μ id hT (w, Fin.snoc u (b, s))
      rw [dist_id] at this
      simpa [pair, Zp, Yl, Sl, Wv, Fin.init_snoc] using this
    have e2 : dist μ (pair Zp Wv) (u, w) =
        fbLaw ν (strategyOutChannel W p fun f => f) enc k (w, u) := by
      have := dist_comp_of_injective μ (fun z => (z.1, Fin.init z.2)) Prod.swap_injective (w, u)
      rw [dist_fbLaw_init hV k] at this
      exact this
    rw [← sum_dist_pair_right μ _ Sl, e2]
    simp_rw [e1]
    simp only [μ, fbLaw_snoc, strategyOutChannel, strategyChannel]
    rw [mul_sum]
  have h5 := entropy_sub_condEntropy_le_capacity (fun z : (Fin k → β × σ) × 𝒲 => enc k z.2 z.1)
    hμ hVb hchan
  rw [h1, h2, h3]
  linarith

variable [DecidableEq σ] in
/-- `I(M; Yⁿ) ≤ n C`. -/
theorem mutualInfo_causalLaw_le (hW : IsChannel W) (hp : IsPMF p) (hν : IsPMF ν)
    (n : ℕ) :
    I[Prod.fst : causalY 𝒲 n ; fbLaw ν (strategyOutChannel W p fun f => f) enc n] ≤
      n * capacity (strategyChannel W p fun f : σ → α => f) := by
  induction n with
  | zero =>
    have hμ := fbLaw_isPMF (enc := enc) hν (strategyOutChannel_isChannel hW hp fun f : σ → α => f) 0
    rw [mutualInfo_eq_entropy_sub_condEntropy' hμ]
    have h1 := entropyRV_le_log_card hμ (causalY 𝒲 0 : 𝒲 × (Fin 0 → β × σ) → Fin 0 → β)
    have h2 := condEntropy_nonneg hμ (causalY 𝒲 0 : 𝒲 × (Fin 0 → β × σ) → Fin 0 → β) Prod.fst
    simp only [Fintype.card_unique, Nat.cast_one, log_one] at h1
    simp only [CharP.cast_eq_zero, zero_mul]
    linarith
  | succ n ih =>
    have := mutualInfo_causalLaw_succ_le (enc := enc) hW hp hν n
    push_cast
    linarith

variable {M n : ℕ}

/-- The strategy of a causal code at time `k`: `Fₖ = xₖ(m, sᵏ⁻¹, ·)`, given `sᵏ⁻¹`. -/
def StateCode.strategy [Nonempty α] (c : StateCode M n σ α β) (k : ℕ) (m : Fin M)
    (z : Fin k → β × σ) : σ → α :=
  fun s => if h : k < n then
    c.enc m (fun i => if h' : (i : ℕ) < k then (z ⟨i, h'⟩).2 else s) ⟨k, h⟩ else
    Classical.arbitrary α

omit [Fintype σ] [Fintype α] [Fintype β] in
/-- The law of the message and the outputs `(Yⁿ, Sⁿ)` of a causal code. -/
lemma fbLaw_strategy [Nonempty α] {c : StateCode M n σ α β} (hc : c.IsCausal) (w : Fin M)
    (s : Fin n → σ) (y : Fin n → β) (ν : Fin M → ℝ) :
    fbLaw ν (strategyOutChannel W p fun f => f) c.strategy n (w, zipSeq y s) =
      ν w * (iidPMF p n s * channelExt W n (zipSeq (c.enc w s) s) y) := by
  have key : ∀ k (hk : k ≤ n), fbLaw ν (strategyOutChannel W p fun f => f) c.strategy k
      (w, fun i : Fin k => (y (Fin.castLE hk i), s (Fin.castLE hk i))) =
      ν w * ∏ i : Fin k, (p (s (Fin.castLE hk i)) *
        W (c.enc w s (Fin.castLE hk i), s (Fin.castLE hk i)) (y (Fin.castLE hk i))) := by
    intro k
    induction k with
    | zero => intro _; simp [fbLaw]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      rw [fbLaw]
      have e := ih (by omega)
      have e' : Fin.init (fun i : Fin (k + 1) => (y (Fin.castLE hk i), s (Fin.castLE hk i))) =
          fun i : Fin k => (y (Fin.castLE (by omega) i), s (Fin.castLE (by omega) i)) := rfl
      simp only [e', e]
      rw [Fin.prod_univ_castSucc, mul_assoc]
      congr 2
      simp only [strategyOutChannel, StateCode.strategy, hkn, ↓reduceDIte]
      have hcaus : c.enc w (fun i => if h' : (i : ℕ) < k then s (Fin.castLE (by omega) ⟨i, h'⟩) else
          s ⟨k, hkn⟩) ⟨k, hkn⟩ = c.enc w s ⟨k, hkn⟩ := by
        refine hc w _ _ _ fun j hj => ?_
        by_cases hjk : (j : ℕ) < k
        · simp [hjk]
        · have : j = ⟨k, hkn⟩ := Fin.ext (le_antisymm (Fin.le_def.1 hj) (not_lt.1 hjk))
          subst this
          simp
      rw [show Fin.castLE hk (Fin.last k) = ⟨k, hkn⟩ from rfl, hcaus]
  have h := key n le_rfl
  have e : (fun i : Fin n => (y (Fin.castLE le_rfl i), s (Fin.castLE le_rfl i))) = zipSeq y s := rfl
  rw [e] at h
  rw [h]
  congr 1
  simp only [iidPMF, channelExt, zipSeq, prod_mul_distrib]
  rfl

variable [DecidableEq σ] in
/-- **Converse of Theorem 3 (Lecture 7 of [elgamal2010]).** By Fano's inequality, a code using the
state causally at the encoder only has `(1 - P_e^(n)) log M ≤ log 2 + n C`, where `C` is the
capacity of the channel from the strategies. -/
theorem StateCode.one_sub_errProb_mul_log_le_strategy [Nonempty α] (hW : IsChannel W)
    (hp : IsPMF p) (hM : 0 < M) (c : StateCode M n σ α β) (hc : c.IsCausal)
    (hd : c.DecIgnoresState) :
    (1 - c.errProb W p) * log M ≤
      log 2 + n * capacity (strategyChannel W p fun f : σ → α => f) := by
  classical
  obtain ⟨s₀⟩ := hp.nonempty_type
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hV := strategyOutChannel_isChannel hW hp fun f : σ → α => f
  have hν : IsPMF (uniformPMF (Fin M)) := uniformPMF_isPMF
  set μ := fbLaw (uniformPMF (Fin M)) (strategyOutChannel W p fun f => f) c.strategy n
  have hμ : IsPMF μ := fbLaw_isPMF hν hV n
  set s₀' : Fin n → σ := fun _ => s₀
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ (Prod.fst : Fin M × _ → Fin M) (causalY _ n)
  have h2 := fano_weak hμ (Prod.fst : Fin M × _ → Fin M) (causalY _ n) (c.dec s₀')
  have h3 := mutualInfo_causalLaw_le (enc := c.strategy) hW hp hν n
  have hH : H[Prod.fst ; μ] = log M := by
    rw [entropyRV, dist_fst_fbLaw hV, entropy_uniformPMF, Fintype.card_fin]
  have herr : InfoTheory.errProb μ Prod.fst (causalY _ n) (c.dec s₀') = c.errProb W p := by
    simp only [InfoTheory.errProb, Fintype.sum_prod_type, StateCode.errProb, StateCode.condErr]
    rw [sum_div]
    refine sum_congr rfl fun w _ => ?_
    have hequiv := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => β)
      (fun _ => σ)).symm.sum_comp fun z : Fin n → β × σ =>
        if c.dec s₀' (fun i => (z i).1) ≠ w then μ (w, z) else 0
    refine (Eq.trans (by congr!) hequiv.symm).trans ?_
    rw [Fintype.sum_prod_type_right, sum_div]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun y _ => ?_
    have hz : (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => β) (fun _ => σ)).symm (y, s) =
        zipSeq y s := rfl
    rw [hz]
    have hdy : c.dec s y = c.dec s₀' y := hd s s₀' y
    change (if c.dec s₀' y ≠ w then μ (w, zipSeq y s) else 0) = _
    rw [hdy]
    by_cases hw : c.dec s₀' y ≠ w
    · simp only [hw, ne_eq, not_false_eq_true, ite_true, μ, fbLaw_strategy hc]
      simp only [uniformPMF, Fintype.card_fin]
      field_simp
    · simp [hw]
  rw [herr, Fintype.card_fin] at h2
  have hn0 := mul_comm (c.errProb W p) (log M)
  linarith [sub_mul 1 (c.errProb W p) (log (M : ℝ))]

/-- The converse: a rate achievable with the state causally at the encoder is at most the capacity
of the channel from the strategies. -/
theorem IsAchievableStateRate.le_causal [DecidableEq σ] [Nonempty α] (hW : IsChannel W)
    (hp : IsPMF p) {R : ℝ} (h : IsAchievableStateRate W p .causal false R) :
    R ≤ capacity (strategyChannel W p fun f : σ → α => f) / log 2 := by
  obtain ⟨c, hc, hlim⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  exact le_div_log_two_of_converse hlim (fun n => (c n).errProb_le_one hW hp (hpos n))
    fun n => (c n).one_sub_errProb_mul_log_le_strategy hW hp (hpos n) (hc n).1 ((hc n).2 rfl)

omit [Fintype α] in
/-- **Theorem 3 (Lecture 7 of [elgamal2010]).** With the state available causally at the encoder
only, the capacity is `C_CSI-E = max_{p(u), x(u, s)} I(U; Y)`, in bits. -/
theorem stateCapacity_causal_false [Finite α] [Nonempty α] (hW : IsChannel W) (hp : IsPMF p) :
    stateCapacity W p .causal false = causalValue W p / log 2 := by
  classical
  have := Fintype.ofFinite α
  rw [causalValue_eq_capacity hW hp]
  exact sSup_eq_of_forall_mem (fun _ h => h.le_causal hW hp)
    fun _ hR => isAchievableStateRate_causal_false_of_lt hW hp hR

end Converse

end InfoTheory
